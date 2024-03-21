#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::sync::atomic::AtomicI32;
use std::sync::Arc;
use std::cell::RefCell;
use std::ops::Deref;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;

// Sometimes, the postcondition does not verify. The cause seems to be that the verifier does not
// traverse the type parameter when generating axioms in the encoding.
#[requires(Arc::strong_count(a) == 1)]
#[ensures(Arc::strong_count(a) == 1)] // This sometimes fails
fn incompleteness(a: &mut Arc<RefCell<i32>>) {}

// As a workaround, we can add a dummy parameter. This should always work.
#[requires(Arc::strong_count(a) == 1)]
#[ensures(Arc::strong_count(a) == 1)]
fn workaround(a: &mut Arc<RefCell<i32>>, workaround: &RefCell<i32>) {}

fn smoke() {
    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn main(){}
