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

#[ensures(deref(a.as_ptr()) == 42)] //~ ERROR postcondition might not hold
fn atomic_set(a: &AtomicI32) {
    atomic_set(a);
}

#[requires(deref(a.as_ptr()) == 100)]
#[ensures(deref(a.as_ptr()) == 100)] //~ ERROR postcondition might not hold
fn atomic_require(a: &AtomicI32) {}

fn atomic_client(a: &AtomicI32) {
    atomic_set(a);
    atomic_require(a); //~ ERROR precondition might not hold
}

#[ensures(a.data() == 42)] //~ ERROR postcondition might not hold
fn arc_set(a: &Arc<RefCell<i32>>) {
    arc_set(a);
}

#[requires(a.data() == 100)]
#[ensures(a.data() == 100)] //~ ERROR postcondition might not hold
fn arc_require(a: &Arc<RefCell<i32>>) {}

fn arc_client(a: Arc<RefCell<i32>>) {
    arc_set(&a);
    arc_require(&a); //~ ERROR precondition might not hold
}

fn main() {}
