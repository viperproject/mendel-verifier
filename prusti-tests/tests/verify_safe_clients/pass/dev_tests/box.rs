#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::ops::Deref;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

fn test_1() {
    let mut x = Box::new(123);
    let y = x.as_mut();
    assert!(*y == 123);
    let z = y;
    assert!(*z == 123);
    *z = 42;
    assert!(*x.deref() == 42);


}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
