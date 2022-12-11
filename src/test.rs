use crate::{Allocator, Strong};
use std::{mem::drop, sync::Arc, thread};

#[test]
fn t001() {
    let s = Strong::new(1);
    let w = s.downgrade();

    assert!(s.get() == &1);
    assert!(w.upgrade().unwrap().get() == &1);
    drop(s);
    assert!(w.upgrade().is_none());
}

#[test]
fn t002() {
    let s = Strong::new(1);
    let w = s.downgrade();
    drop(s);

    let s = Strong::new(2);
    assert!(w.upgrade().is_none());
    assert!(s.get() == &2);
}

#[test]
fn t003() {
    let arc = Arc::new(1);
    let w = Strong::new(Arc::clone(&arc));
    assert!(Arc::strong_count(&arc) == 2);
    drop(w);
    assert!(Arc::strong_count(&arc) == 1);
}

#[test]
fn t004() {
    {
        let s = Strong::new(String::from("a"));
        assert!(s.into_inner().unwrap() == "a");
    }

    {
        let s1 = Strong::new(String::from("b"));
        let s2 = s1.clone();
        let s1 = s1.into_inner().unwrap_err();
        drop(s2);
        assert!(s1.into_inner().unwrap() == "b");
    }

    {
        let s = Strong::new(String::from("c"));
        let w = s.downgrade();

        for _ in 0..50 {
            thread::spawn(move || {
                drop(w.upgrade());
            });
        }
        let _ = s.into_inner();
    }
}

#[test]
fn t005() {
    static ALLOC: Allocator<String> = Allocator::new();
    let s = Strong::with_allocator(String::from("1"), &ALLOC);

    assert!(s.get() == "1");
}
