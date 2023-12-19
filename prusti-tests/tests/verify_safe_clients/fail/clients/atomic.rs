#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::sync::atomic::AtomicI32;
use std::ops::Deref;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

fn unknown<T>(x: T) {}

fn test_1() {
    let mut x = AtomicI32::new(123);
    prusti_assert!(deref(x.as_ptr()) == 123);
    assert!(*x.get_mut() == 123);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_2() {
    let mut x = AtomicI32::new(123);
    unknown(&x);
    assert!(*x.get_mut() == 123); //~ ERROR
}

fn test_3() {
    let mut x = AtomicI32::new(123);
    let y = &x;
    unknown(0);
    prusti_assert!(x.as_ptr() == y.as_ptr());

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn incompleteness_1() {
    let mut x = AtomicI32::new(123);
    let y = &x;
    unknown(0);
    let z = y;

    prusti_assert!(deref(x.as_ptr()) == 123); // Incompleteness
    //~^ ERROR the asserted expression might not hold

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

// This might be a bug in the encoding; not a limitation of the technique.
fn incompleteness_2() {
    let mut x = AtomicI32::new(123);
    assert!(*x.get_mut() == 123);
    let data = x.get_mut();
    *data = 456;
    assert!(*x.get_mut() == 456); // Incompleteness
    //~^ ERROR the asserted expression might not hold

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
