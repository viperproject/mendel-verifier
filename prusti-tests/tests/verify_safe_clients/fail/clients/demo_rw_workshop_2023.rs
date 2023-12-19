#![feature(try_trait_v2)]
#![feature(allocator_api)]
#![allow(dead_code, unused_attributes, unused_variables, unused_imports)]
use std::{cell::*, ops::Deref, sync::*};
use prusti_contracts::*;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

// ========== example 0 ==========

fn client_1(x: Option<i32>) {
    let before = x.is_some();
    unknown(&x);
    let after = x.is_some();
    assert!(before == after);
}

fn client_2(x: Cell<i32>) {
    let before = x.get();
    unknown(&x);
    let after = x.get();
    assert!(before == after); //~ ERROR
}

fn unknown<T>(x: T) {
    /* ??? */
}

// ========== example 1 ==========
// With preconditions to prove that borrow() doesn't panic.

#[requires(!x.is_writing())]
fn example_1(x: &RefCell<i32>) {
    let a: Ref<i32> = x.borrow();
    let before = *a;
    unknown_1(x);
    let b: Ref<i32> = x.borrow();
    assert!(before == *b);
    drop(a); // This is necessary because of an imprecision in the analysis of the available places.
}

#[ensures(!old(x.is_writing()) ==> !x.is_writing())]
fn unknown_1(x: &RefCell<i32>) {
    /* ??? */
}

// ========== example 2 ==========
// Replace `write()` with `read()` to make the last line reachable.

fn example_2(a: Arc<RwLock<Vec<i32>>>) {
    let Ok(guard_1) = a.write() else { return; };
    let Ok(guard_2) = a.read() else { return; };
    prusti_assert!(guard_1.rwlock().data_ptr() == guard_2.rwlock().data_ptr());
    unreachable!();
}

// ========== example 3 ==========
// Other threads might interfere on the reference count.
// The specification of Arc assumes that there are no weak references.

fn example_3(x: Arc<i32>, y: Arc<i32>) {
    if Arc::strong_count(&x) != 1 {
        assert!(Arc::strong_count(&x) != 1); //~ ERROR
    } else {
        assert!(Arc::strong_count(&x) == 1);
        assert!(Arc::as_ptr(&x) != Arc::as_ptr(&y));
    }
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
