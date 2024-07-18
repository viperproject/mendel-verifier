#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::cell::UnsafeCell;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

#[trusted]
#[pure]
fn pure(x: &UnsafeCell<i32>) -> i32 {
    unimplemented!()
}

#[trusted]
#[pure_memory]
fn pure_memory(x: &UnsafeCell<i32>) -> i32 {
    unimplemented!()
}

#[trusted]
#[pure_unstable]
fn pure_unstable(x: &UnsafeCell<i32>) -> i32 {
    unimplemented!()
}

/// Test framing of pure functions
#[ensures(old(x) ==== x)]
#[ensures(old(pure(x)) == pure(x))]
#[ensures(old(pure_memory(x)) == pure_memory(x))]
#[ensures(old(pure_unstable(x)) == pure_unstable(x))] //~ ERROR
fn test_1(x: &UnsafeCell<i32>) {}

/// Test nonaliasing
fn test_2(x: &mut UnsafeCell<i32>, y: &i32) {
    assert!(x.get() as *const _ != y as *const _);


}

fn test_3(x: &mut UnsafeCell<i32>, y: &i32) {
    let mut x = UnsafeCell::new(123);
    assert!(*x.get_mut() == 123);
    let y = x.get_mut();
    *y = 456;
    prusti_assert!(deref(x.get()) == 456);
    assert!(*x.get_mut() == 456);
    let z = x.into_inner();
    assert!(z == 456);


}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
