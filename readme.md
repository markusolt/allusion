# Allusion

A small rust crate that provides a reference counted smart pointer.

The provided `Strong` and `Weak` pointer types are very similar to `std::sync::Arc` and `std::sync::Weak`.
The key difference is that our `Weak` implements `Copy`, whereas the `std::sync::Weak` is reference counted.
For this reason weak pointers can be duplicated with no performance cost.
To access the referenced value you must first upgrade the weak pointers though, which similary to `std::sync::Weak::upgrade` performs multiple atomic operations.
It may be cheaper to simply clone `std::sync::Arc`s around to avoid the cost of upgrading a weak pointer.

An additional downside is the need of an `Allocator`.
Because weak pointers are `Copy` and have no lifetime we can never free the memory allocation that the weak pointer is pointing to.
We can however reuse the memory allocation once there are no more strong pointers pointing to it by incrementing an `era` field.
The `Allocator` is used to recycle such old allocations.
The function `Allocator::dynamic` provides allocators for any requested type `T` using a hashmap over the `TypeId`.
This dynamic allocator provider is very convinient if you can accept the perfomance cost of looking up the needed allocator in a hashmap.

```rust
impl Strong<T> {
    pub fn new(value: T) -> Self;

    pub fn get(&self) -> &T;

    pub fn clone(&self) -> Self;

    pub fn downgrade(&self) -> Weak<T>;
}

impl Weak<T> {
    pub fn upgrade(&self) -> Option<Strong<T>>;
}

impl Copy for Weak<T> {}
```

## Safety

As is expected for this kind of utility crate, the implementation makes use of `unsafe`.
We have a number of tests to look for undefined behavior which can all be run natively or with [miri](https://github.com/rust-lang/miri).
`miri` is a fantastic tool to execute rust applications in a virtual runtime that is sensitive to various kinds of undefined behavior.

```
# run tests normally
cargo test

# install miri
rustup toolchain install nightly
rustup +nightly component add miri

# run tests in miri
cargo clean
cargo +nightly miri test
```
