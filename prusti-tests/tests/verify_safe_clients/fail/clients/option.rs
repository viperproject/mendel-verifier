#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

#[trusted]
fn unknown<T>(_: T) {}

fn test_1() {
    let x = Some(123);
    assert!(x.is_some());
    assert!(!x.is_none());

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_2() {
    let x = Some(123);
    let y = x.unwrap();
    assert!(y == 123);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_3() {
    let mut x = Some(123);
    let y = x.as_mut();
    prusti_assert!(y === Some(&mut 123));
    prusti_assert!(y == Some(&mut 123));
    assert!(y == Some(&mut 123));
    assert!(y.is_some());
    let z = y.unwrap();
    assert!(*z == 123);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_4(x: &Option<i32>) {
    let a = x.is_some();
    unknown(x);
    let b = x.is_some();
    assert!(a == b); // Succeeds

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_5() {
    let x: Option<u32> = None;
    assert!(!x.is_some());
    assert!(x.is_none());
    let _ = x.unwrap(); //~ ERROR
}

fn test_6(mut x: Option<u32>) {
    let _ = x.unwrap(); //~ ERROR
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
