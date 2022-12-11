use std::{
    cell::UnsafeCell, fmt, hash::Hash, mem, mem::MaybeUninit, ptr, ptr::NonNull,
    sync::atomic::AtomicUsize, sync::atomic::Ordering::Acquire, sync::atomic::Ordering::Relaxed,
    sync::atomic::Ordering::Release, sync::atomic::Ordering::SeqCst,
};

use crossbeam::channel;
use once_cell::sync::Lazy;

/// An `Allocator` is requried to create new allocations using [`Strong::new`]. The allocator is used
/// to reuse heap allocations. Without allocators we would be leaking memory with every call to
/// `Strong::new`.
///
/// You usually define a static allocator for every type `T` that you intend to use.
///
/// ```
/// # use allusion::{Allocator, Strong};
/// static ALLOC_USIZE: Allocator<usize> = Allocator::new();
/// let _s = Strong::new(5, &ALLOC_USIZE);
/// ```
///
/// You can also define a trait to provide a reference to the relevant static, but again, you must
/// implement it for every type `T` you intend to use. There is no way to implement this genericly.
///
/// ```
/// # use allusion::{Allocator, Strong};
/// trait AllusionAllocator {
///     fn alloc() -> &'static Allocator<Self> where Self: Sized;
/// }
///
/// impl AllusionAllocator for usize {
///     fn alloc() -> &'static Allocator<Self> {
///         static ALLOC: Allocator<usize> = Allocator::new();
///         &ALLOC
///     }
/// }
///
/// impl AllusionAllocator for f32 {
///     fn alloc() -> &'static Allocator<Self> {
///         static ALLOC: Allocator<f32> = Allocator::new();
///         &ALLOC
///     }
/// }
///
/// fn alloc<T>() -> &'static Allocator<T> where T: AllusionAllocator {
///     T::alloc()
/// }
///
/// let _s = Strong::new(5usize, alloc());
/// let _s = Strong::new(5.1f32, alloc());
/// ```
///
/// You can also create a `&'static Allocator<T>` by [leaking][Box::leak] a [`Box`]. This will
/// cause a memory leak that [`miri`](https://github.com/rust-lang/miri) will detect though.
/// `static` variables get dropped when the application shuts down, leaked boxes do not. This
/// kind of memory leak is totally fine though, the operating system will reclaim all memory after
/// the application has shut down anyways.
#[derive()]
pub struct Allocator<T>
where
    T: 'static,
{
    channel: Lazy<(
        channel::Sender<AllowSend<NonNull<Node<T>>>>,
        channel::Receiver<AllowSend<NonNull<Node<T>>>>,
    )>,
}

impl<T> fmt::Debug for Allocator<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Allocator")
    }
}

impl<T> Allocator<T> {
    /// Creates a new allocator.
    pub const fn new() -> Self {
        Allocator {
            channel: Lazy::new(|| channel::unbounded()),
        }
    }
}

impl<T> Default for Allocator<T> {
    fn default() -> Self {
        Self::new()
    }
}

struct AllowSend<T>(T);

unsafe impl<T> Send for AllowSend<T> {}

struct Node<T>
where
    T: 'static,
{
    value: UnsafeCell<MaybeUninit<T>>,
    shared: Shared<T>,
}

struct Shared<T>
where
    T: 'static,
{
    strong: AtomicUsize,
    gen: AtomicUsize,
    alloc: &'static Allocator<T>,
}

/// A reference counted pointer, very similar to [`Arc`].
///
/// [`Arc`]: std::sync::Arc
#[derive()]
pub struct Strong<T>
where
    T: 'static,
{
    node: NonNull<Node<T>>,
    gen: usize,
}

impl<T> Drop for Strong<T> {
    fn drop(&mut self) {
        unsafe {
            let shared = self.shared();
            debug_assert!(shared.strong.load(Acquire) > 0);

            if shared.strong.fetch_sub(1, Release) == 1 {
                let alloc = shared.alloc;
                self.as_ptr_mut()
                    .as_mut()
                    .unwrap_unchecked()
                    .assume_init_drop();

                let _ = alloc.channel.0.send(AllowSend(self.node));
            }
        }
    }
}

unsafe impl<T> Send for Strong<T> where T: Send + Sync {}

unsafe impl<T> Sync for Strong<T> where T: Send + Sync {}

impl<T> fmt::Debug for Strong<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.get(), f)
    }
}

impl<T> Strong<T> {
    /// Creates a new allocation to store the provided value. The `allocator` is used to recycle old
    /// heap allocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    /// let s = Strong::new(5, &ALLOC);
    ///
    /// assert!(s.get() == &5);
    /// ```
    pub fn new(value: T, allocator: &'static Allocator<T>) -> Self {
        unsafe {
            if let Ok(node) = allocator.channel.1.try_recv() {
                let mut ret = Strong {
                    node: node.0,
                    gen: 0,
                };
                ret.as_ptr_mut().as_mut().unwrap_unchecked().write(value);
                ret.gen = ret.shared().gen.fetch_add(1, SeqCst).wrapping_add(1);
                ret.shared().strong.store(1, SeqCst);

                ret
            } else {
                let gen = 0;
                let node = NonNull::from(Box::leak(Box::new(Node {
                    value: UnsafeCell::new(MaybeUninit::new(value)),
                    shared: Shared {
                        strong: AtomicUsize::new(1),
                        gen: AtomicUsize::new(gen),
                        alloc: allocator,
                    },
                })));

                Strong { node, gen }
            }
        }
    }

    /// Gets a reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    /// let s = Strong::new(5, &ALLOC);
    ///
    /// assert!(s.get() == &5);
    /// ```
    pub fn get(&self) -> &T {
        unsafe {
            self.as_ptr_mut()
                .as_ref()
                .unwrap_unchecked()
                .assume_init_ref()
        }
    }

    /// Clones the `Strong`. This creates another pointer to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    /// let s1 = Strong::new(5, &ALLOC);
    ///
    /// let s2 = s1.clone();
    /// assert!(s1.as_ptr() == s2.as_ptr());
    /// ```
    pub fn clone(&self) -> Self {
        self.shared().strong.fetch_add(1, Relaxed);

        Strong {
            node: self.node,
            gen: self.gen,
        }
    }

    /// Gets the number of strong references to this allocation.
    ///
    /// Always returns a positive value because the count includes `&self`. The same method is also
    /// available on [`Weak::strong_count`], through that version can return `0` when there are no
    /// more strong references to the allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::drop;
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    /// let s1 = Strong::new(1, &ALLOC);
    ///
    /// assert!(s1.strong_count() == 1);
    ///
    /// let s2 = s1.clone();
    /// assert!(s1.strong_count() == 2);
    ///
    /// drop(s2);
    /// assert!(s1.strong_count() == 1);
    ///
    /// let w = s1.downgrade();
    /// assert!(w.strong_count() == 1);
    ///
    /// drop(s1);
    /// assert!(w.strong_count() == 0);
    /// ```
    pub fn strong_count(&self) -> usize {
        self.shared().strong.load(Acquire)
    }

    /// Creates a new weak reference to the allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::drop;
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    /// let s = Strong::new(1, &ALLOC);
    ///
    /// let w = s.downgrade();
    /// assert!(s.as_ptr() == w.as_ptr());
    /// assert!(s.strong_count() == 1);
    /// ```
    pub fn downgrade(&self) -> Weak<T> {
        Weak {
            node: self.node,
            gen: self.gen,
        }
    }

    /// Returns ownership of the contained value. Returns `Err` if there are multiple strong references
    /// to the allocation.
    pub fn into_inner(self) -> Result<T, Self> {
        let shared = self.shared();

        if let Err(strong) = shared.strong.compare_exchange(1, 0, Acquire, Relaxed) {
            debug_assert!(strong > 1);

            return Err(self);
        }

        let ret = unsafe {
            self.as_ptr_mut()
                .as_mut()
                .unwrap_unchecked()
                .assume_init_read()
        };
        let _ = shared.alloc.channel.0.send(AllowSend(self.node));
        mem::forget(self);

        Ok(ret)
    }

    /// Gets a raw pointer to the value.
    pub fn as_ptr(&self) -> *const T {
        self.as_ptr_mut() as *const T
    }

    fn as_ptr_mut(&self) -> *mut MaybeUninit<T> {
        unsafe { UnsafeCell::raw_get(ptr::addr_of!((*self.node.as_ptr()).value)) }
    }

    fn shared(&self) -> &Shared<T> {
        unsafe {
            ptr::addr_of!((*self.node.as_ptr()).shared)
                .as_ref()
                .unwrap_unchecked()
        }
    }
}

impl<T> Clone for Strong<T> {
    fn clone(&self) -> Self {
        Strong::clone(self)
    }
}

/// A weak reference to an allocation. Unlike strong references these are not reference counted. You can
/// duplicate weak references for free using the [`Copy`] trait.
///
/// Weak references cannot provide a reference to the stored value because the value may be freed at any
/// time if another thread drops the last remaining strong reference. Instead you must first attempt to
/// [`upgrade`][Weak::upgrade] the weak reference into a strong reference.
///
/// There is a tiny chance that a weak reference will successfully upgrade into a strong containing an
/// unexpected value. This can happen because the memory allocations are reused. Usually this will be
/// detected by comparing a `generation: usize` stored in the weak reference which can be compared to the
/// allocations `generation`. The generation will however wrap around once the allocation has been reused
/// `2^64` times.
#[derive()]
pub struct Weak<T>
where
    T: 'static,
{
    node: NonNull<Node<T>>,
    gen: usize,
}

unsafe impl<T> Send for Weak<T> where T: Send + Sync {}

unsafe impl<T> Sync for Weak<T> where T: Send + Sync {}

impl<T> fmt::Debug for Weak<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_tuple("Weak");
        if let Some(strong) = self.upgrade() {
            f.field(strong.get());
        }
        f.finish()
    }
}

impl<T> Weak<T> {
    /// See [`Strong::downgrade`].
    pub fn new(strong: &Strong<T>) -> Self {
        strong.downgrade()
    }

    /// Creates a strong reference to the allocation. Returns `None` if the allocation has already been
    /// freed because there are no more strong references to it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::drop;
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    /// let s = Strong::new(5, &ALLOC);
    ///
    /// let w = s.downgrade();
    /// assert!(w.upgrade().unwrap().get() == &5);
    ///
    /// drop(s);
    /// assert!(w.upgrade().is_none());
    /// ```
    pub fn upgrade(&self) -> Option<Strong<T>> {
        let shared = self.shared();

        let mut n = shared.strong.load(Relaxed);
        loop {
            if n == 0 {
                return None;
            }

            match shared
                .strong
                .compare_exchange_weak(n, n + 1, Acquire, Relaxed)
            {
                Ok(_) => break,
                Err(strong) => n = strong,
            }
        }

        let ret = Strong {
            node: self.node,
            gen: shared.gen.load(Acquire),
        };

        if ret.gen != self.gen {
            drop(ret);

            return None;
        }

        Some(ret)
    }

    /// See [`Strong::strong_count`].
    pub fn strong_count(&self) -> usize {
        let shared = self.shared();

        let n = shared.strong.load(Acquire);
        if self.gen == shared.gen.load(Acquire) {
            n
        } else {
            0
        }
    }

    /// Gets a raw pointer to the value.
    pub fn as_ptr(&self) -> *const T {
        self.as_ptr_mut() as *const T
    }

    fn as_ptr_mut(&self) -> *mut MaybeUninit<T> {
        unsafe { UnsafeCell::raw_get(ptr::addr_of!((*self.node.as_ptr()).value)) }
    }

    fn shared(&self) -> &Shared<T> {
        unsafe {
            ptr::addr_of!((*self.node.as_ptr()).shared)
                .as_ref()
                .unwrap_unchecked()
        }
    }
}

impl<T> From<&Strong<T>> for Weak<T> {
    fn from(value: &Strong<T>) -> Self {
        Self::new(value)
    }
}

impl<T> Clone for Weak<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Weak<T> {}

impl<T> PartialEq for Weak<T> {
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&(self.node, self.gen), &(other.node, other.gen))
    }

    fn ne(&self, other: &Self) -> bool {
        PartialEq::ne(&(self.node, self.gen), &(other.node, other.gen))
    }
}

impl<T> Eq for Weak<T> {}

impl<T> PartialOrd for Weak<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(&(self.node, self.gen), &(other.node, other.gen))
    }
}

impl<T> Ord for Weak<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&(self.node, self.gen), &(other.node, other.gen))
    }
}

impl<T> Hash for Weak<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Hash::hash(&(self.node, self.gen), state)
    }
}
