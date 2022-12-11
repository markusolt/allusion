//! A reference counted [`Strong`] and [`Weak`] pointer.
//!
//! The provided `Strong` and `Weak` pointer types are very similar to [`std::sync::Arc`] and
//! [`std::sync::Weak`]. The key difference is that our `Weak` implements [`Copy`], whereas the
//! `std::sync::Weak` is reference counted. For this reason weak pointers can be duplicated
//! with no performance cost. To access the referenced value you must first upgrade the weak
//! pointers though, which similary to [`std::sync::Weak::upgrade`] performs multiple atomic
//! operations. It may be cheaper to simply clone [`std::sync::Arc`]s around to avoid the cost
//! of upgrading a weak pointer.
//!
//! An additional downside is the need of an [`Allocator`]. Because weak pointers are `Copy`
//! and have no lifetime we can never free the memory allocation that the weak pointer is
//! pointing to. We can however reuse the memory allocation once there are no more strong
//! pointers to it by incrementing a `generation` field. The `Allocator` is used to recycle
//! such old allocations. The function [`Allocator::dynamic`] provides allocators for any
//! requested type `T` using a hashmap. This dynamic allocator provider is very convinient if
//! you can accept the perfomance cost of looking up the needed allocator in a hashmap.

mod allusion;

pub use crate::allusion::{Allocator, Strong, Weak};

#[cfg(test)]
mod test;
