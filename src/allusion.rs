use std::{
    cell::UnsafeCell, fmt, hash::Hash, mem, mem::MaybeUninit, ptr, ptr::NonNull,
    sync::atomic::AtomicUsize, sync::atomic::Ordering::Acquire, sync::atomic::Ordering::Relaxed,
    sync::atomic::Ordering::Release, sync::OnceLock,
};

use crossbeam::channel;

/// An `Allocator` is requried to create new allocations using [`Strong::with_allocator`]. The
/// allocator is used to reuse heap allocations.
///
/// You usually define a static allocator for every type `T` that you intend to use.
///
/// ```
/// # use allusion::{Allocator, Strong};
/// static ALLOC_USIZE: Allocator<usize> = Allocator::new();
/// let _s = Strong::with_allocator(5, &ALLOC_USIZE);
/// ```
///
/// You can instead use [`Allocator::dynamic`]. This will perform worse than using a `static`
/// variable, but it can be called with a generic type parameter. Creating strong pointers with
/// this allocator can be done more easily using [`Strong::new`].
#[derive()]
pub struct Allocator<T>
where
    T: 'static,
{
    channel: OnceLock<(
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
            channel: OnceLock::new(),
        }
    }

    /// Provides a `'static` allocator. Uses a [`HashMap`][std::collections::HashMap] to lazily
    /// create allocators for different types `T`.
    ///
    /// It is recommended to use your own `static ALLOC: Allocator<T>` where possible, this dynamic
    /// solution performs worse because it must lock a [`RwLock`][std::sync::RwLock] and look up
    /// an entry in a hashmap. This is only provided for convenience and as a reference, you can
    /// implement the same thing using the public api of `allusion`.
    pub fn dynamic() -> &'static Self {
        use std::{any::Any, any::TypeId, collections::HashMap, sync::RwLock};

        static MAP: OnceLock<RwLock<HashMap<TypeId, &'static (dyn Any + Send + Sync)>>> =
            OnceLock::new();
        let map = MAP.get_or_init(|| RwLock::new(HashMap::new()));

        if let Some(alloc) = map.read().unwrap().get(&TypeId::of::<T>()) {
            return alloc.downcast_ref().unwrap();
        }

        map.write()
            .unwrap()
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Box::leak(Box::new(Self::new())))
            .downcast_ref()
            .unwrap()
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
    era: AtomicUsize,
    alloc: &'static Allocator<T>,
}

/// A reference counted pointer, similar to [`Arc`].
///
/// [`Arc`]: std::sync::Arc
#[derive()]
pub struct Strong<T>
where
    T: 'static,
{
    node: NonNull<Node<T>>,
    era: usize,
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

                let _ = alloc.channel.get().unwrap().0.send(AllowSend(self.node));
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
    /// Creates a new allocation using the default allocator [`Allocator::dynamic`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use allusion::{Allocator, Strong};
    /// let s = Strong::new(5);
    ///
    /// // the above is equivalent to
    /// let s = Strong::with_allocator(5, Allocator::dynamic());
    /// ```
    pub fn new(value: T) -> Self {
        Self::with_allocator(value, Allocator::dynamic())
    }

    /// Creates a new allocation using the provided allocator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use allusion::{Allocator, Strong};
    /// static ALLOC: Allocator<usize> = Allocator::new();
    ///
    /// let s = Strong::with_allocator(5, &ALLOC);
    /// ```
    pub fn with_allocator(value: T, allocator: &'static Allocator<T>) -> Self {
        unsafe {
            let recv = &allocator.channel.get_or_init(|| channel::unbounded()).1;
            while let Ok(node) = recv.try_recv() {
                let mut ret = Strong {
                    node: node.0,
                    era: 0,
                };

                let era: usize = if let Some(era) = ret.shared().era.load(Acquire).checked_add(1) {
                    era
                } else {
                    // we have exhausted the value space of `era`. there is no safe way to reuse this
                    // allocation, so we ignore it and try again.
                    //
                    // this heap allocation will never be freed and can be considered a memory leak.
                    // remember though that this only happens after an allocation has been used `2^64`
                    // times, which is unlikely to occur in practice (on some systems `usize` is
                    // smaller than 64 bits, so this may happen much more often there).
                    //
                    // if we reuse the allocation 1 million times per second it would take over 500
                    // thousand years to exhaust 64 bits. it is safe to assume this will never happen.
                    // it would only take a little over an hour to exhaust 32 bits though.

                    continue;
                };

                ret.as_ptr_mut().as_mut().unwrap_unchecked().write(value);
                ret.era = era;

                // we update `era` before `strong` so that old weak pointers never observe a positive
                // strong count paired with the old `era`.
                ret.shared().era.store(era, Release);
                ret.shared().strong.store(1, Release);

                return ret;
            }

            let era = 0;
            let node = NonNull::from(Box::leak(Box::new(Node {
                value: UnsafeCell::new(MaybeUninit::new(value)),
                shared: Shared {
                    strong: AtomicUsize::new(1),
                    era: AtomicUsize::new(era),
                    alloc: allocator,
                },
            })));

            Strong { node, era }
        }
    }

    /// Gets a reference to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use allusion::Strong;
    /// let s = Strong::new(5);
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
    /// # use allusion::Strong;
    /// let s1 = Strong::new(5);
    /// let s2 = s1.clone();
    ///
    /// assert!(s1.as_ptr() == s2.as_ptr());
    /// ```
    pub fn clone(&self) -> Self {
        self.shared().strong.fetch_add(1, Relaxed);

        Strong {
            node: self.node,
            era: self.era,
        }
    }

    /// Gets the number of strong pointers to this allocation.
    ///
    /// Always returns a positive value because the count includes `self`. The same method is also
    /// available on [`Weak::strong_count`], althrough that version can return `0` when there are no
    /// more strong pointers to the allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::drop;
    /// # use allusion::Strong;
    /// let s1 = Strong::new(5);
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

    /// Creates a new weak pointer to the allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::drop;
    /// # use allusion::Strong;
    /// let s = Strong::new(5);
    /// let w = s.downgrade();
    ///
    /// assert!(s.as_ptr() == w.as_ptr());
    /// assert!(s.strong_count() == 1);
    /// ```
    pub fn downgrade(&self) -> Weak<T> {
        Weak {
            node: self.node,
            era: self.era,
        }
    }

    /// Returns ownership of the contained value. Returns `Err` if there are multiple strong pointers
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
        let _ = shared
            .alloc
            .channel
            .get()
            .unwrap()
            .0
            .send(AllowSend(self.node));
        mem::forget(self);

        Ok(ret)
    }

    /// Gets a raw pointer to the value.
    pub fn as_ptr(&self) -> *const T {
        self.as_ptr_mut() as *const T
    }

    pub fn to_raw(&self) -> (usize, usize) {
        (self.node.as_ptr() as usize, self.era)
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

/// A weak pointer to an allocation. Unlike strong pointers these are not reference counted. You can
/// duplicate weak pointers for free using the [`Copy`] trait.
///
/// Weak pointers cannot provide a reference to the stored value because the value may be freed at any
/// time if another thread drops the last remaining strong pointer. Instead you must first attempt to
/// [`upgrade`][Weak::upgrade] the weak pointer into a strong pointer.
#[derive()]
pub struct Weak<T>
where
    T: 'static,
{
    node: NonNull<Node<T>>,
    era: usize,
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

    /// Creates a strong pointer to the allocation. Returns `None` if the allocation has already been
    /// freed because there are no more strong pointers to it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::mem::drop;
    /// # use allusion::Strong;
    /// let s = Strong::new(5);
    /// let w = s.downgrade();
    ///
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
            era: shared.era.load(Acquire),
        };

        if ret.era != self.era {
            drop(ret);

            return None;
        }

        Some(ret)
    }

    /// See [`Strong::strong_count`].
    pub fn strong_count(&self) -> usize {
        let shared = self.shared();

        let n = shared.strong.load(Acquire);
        if self.era == shared.era.load(Acquire) {
            n
        } else {
            0
        }
    }

    /// Gets a raw pointer to the value.
    pub fn as_ptr(&self) -> *const T {
        self.as_ptr_mut() as *const T
    }

    pub fn to_raw(&self) -> (usize, usize) {
        (self.node.as_ptr() as usize, self.era)
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
        PartialEq::eq(&self.to_raw(), &other.to_raw())
    }

    fn ne(&self, other: &Self) -> bool {
        PartialEq::ne(&self.to_raw(), &other.to_raw())
    }
}

impl<T> Eq for Weak<T> {}

impl<T> PartialOrd for Weak<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(&self.to_raw(), &other.to_raw())
    }
}

impl<T> Ord for Weak<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.to_raw(), &other.to_raw())
    }
}

impl<T> Hash for Weak<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Hash::hash(&self.to_raw(), state)
    }
}
