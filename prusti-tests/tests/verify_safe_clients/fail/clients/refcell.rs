#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::cell::*;
use std::ops::{Deref, DerefMut};

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

/// Test tuple of refcells
fn test_1() {
    let refcells = (RefCell::new(1), RefCell::new(2), RefCell::new(3));
    prusti_assert!(refcells.0.is_free());
    prusti_assert!(refcells.1.is_free());
    prusti_assert!(refcells.2.is_free());
    prusti_assert!(refcells.0.data() == 1);
    prusti_assert!(refcells.1.data() == 2);
    prusti_assert!(refcells.2.data() == 3);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/// Test deref_mut
#[requires(x.is_free())]
fn test_2(x: RefCell<i32>) {
    let mut refmut = x.borrow_mut();
    *refmut = 123;

    let data = refmut.deref_mut();
    assert!(*data == 123);

    *data = 42;
    assert!(*refmut == 42);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/// Taken from https://github.com/rust-lang/rust/issues/63787
#[requires(rc as *const _ == r.refcell_ptr())]
#[requires(rc.is_reading() && rc.num_reading() == 1)]
#[ensures(deref(rc.as_ptr()) == 2)]
#[ensures(rc.is_free())]
fn break_it<'a, 'b>(rc: &'a RefCell<i32>, r: Ref<'b, i32>) {
    // `r` has a shared reference, it is passed in as argument and hence
    // a barrier is added that marks this memory as read-only for the entire
    // duration of this function.
    drop_ref(r);
    // *oops* here we can mutate that memory.
    let mut rm = rc.borrow_mut();
    *rm = 2;
    prusti_assert!(deref(rc.as_ptr()) == 2);
    drop_refmut(rm);
    prusti_assert!(deref(rc.as_ptr()) == 2);
}

fn test_3() {
    let rc = RefCell::new(0);
    break_it(&rc, rc.borrow());

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_4(x: Ref<'_, i32>, mut y: RefMut<'_, i32>) {
	let a = *x.deref();
	*y.deref_mut() = 42;
	let b = *x.deref();
	assert!(a == b); // Always succeeds
	assert!(x.deref() as *const _ != y.deref() as *const _); // Always succeeds

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

#[requires(y.is_free())]
fn test_5(x: Ref<'_, i32>, y: &RefCell<i32>) {
	let a = *x.deref();
	let mut rm = y.borrow_mut();
    *rm = 42;
    drop_refmut(rm);
    let b = *x.deref();

    assert!(a == b); // Always succeeds
    assert!(x.deref() as *const _ != y.as_ptr() as *const _); // Always succeeds
    prusti_assert!(y.data() == 42);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_6(x: Ref<'_, i32>, y: &RefCell<i32>) {
	let a = *x.deref();
	if let Ok(mut rm) = y.try_borrow_mut() {
        *rm = 42;
        drop_refmut(rm);
        let b = *x.deref();

        assert!(a == b); // Always succeeds
        assert!(x.deref() as *const _ != y.as_ptr() as *const _); // Always succeeds
        prusti_assert!(y.data() == 42);

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    } else {
        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    }
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
