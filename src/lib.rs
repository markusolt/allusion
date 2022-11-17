//! A reference counted [`Strong`] and [`Weak`] pointer.
//!
//! The provided `Strong` and `Weak` pointer types are very similar to [`std::sync::Arc`] and
//! [`std::sync::Weak`]. The key difference is that our `Weak` implements [`Copy`], whereas the
//! `std::sync::Weak` is reference counted. For this reason weak references can be duplicate
//! with arguably no performance cost. To access the referenced value you must first upgrade the
//! weak references though, which similary to [`std::sync::Weak::upgrade`] performs multiple
//! atomic operations. It may be cheaper to simply clone [`std::sync::Arc`]s around to avoid
//! the cost of upgrading a weak reference.
//!
//! An additional downside is the need of an [`Allocator`]. Because weak references are `Copy`
//! and have no lifetime we can never free the memory allocation that the weak reference is
//! pointing at. We can however reuse the memory allocation once there are no more strong
//! pointers to it by incrementing a `generation: usize` field. The `Allocator` is used to
//! recycle such old allocations.

mod allusion;

pub use crate::allusion::{Allocator, Strong, Weak};

#[cfg(test)]
mod test;
