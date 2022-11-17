use crate::{Allocator, Strong};
use std::{mem::drop, sync::Arc};

#[test]
fn t001() {
    static ALLOC: Allocator<usize> = Allocator::new();

    let s = Strong::new(1, &ALLOC);
    let w = s.downgrade();

    assert!(s.get() == &1);
    assert!(w.upgrade().unwrap().get() == &1);
    drop(s);
    assert!(w.upgrade().is_none());
}

#[test]
fn t002() {
    static ALLOC: Allocator<usize> = Allocator::new();

    let s = Strong::new(1, &ALLOC);
    let w = s.downgrade();
    drop(s);

    let s = Strong::new(2, &ALLOC);
    assert!(w.upgrade().is_none());
    assert!(s.get() == &2);
}

#[test]
fn t003() {
    static ALLOC: Allocator<Arc<usize>> = Allocator::new();

    let arc = Arc::new(1);
    let w = Strong::new(Arc::clone(&arc), &ALLOC);
    assert!(Arc::strong_count(&arc) == 2);
    drop(w);
    assert!(Arc::strong_count(&arc) == 1);
}
