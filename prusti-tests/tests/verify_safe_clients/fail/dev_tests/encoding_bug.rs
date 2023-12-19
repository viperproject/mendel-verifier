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

#[requires(Arc::strong_count(a) == 1)]
#[ensures(Arc::strong_count(a) == 1)] //~ ERROR postcondition might not hold
fn bug(a: &mut Arc<RefCell<i32>>) {}

// For some reason, the Viper encoding does not traverse the type parameter when generating axioms.
// As a workaround, we can add a dummy parameter.
#[requires(Arc::strong_count(a) == 1)]
#[ensures(Arc::strong_count(a) == 1)]
fn workaround(a: &mut Arc<RefCell<i32>>, workaround: &RefCell<i32>) {}

fn main() {}

