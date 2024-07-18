#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::sync::Mutex;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;

#[requires(local_capability(mutex.data_ptr()))]
fn requires_data_local(mutex: &Mutex<i32>) {}

#[requires(local_capability(mutex as *const _))]
fn requires_mutex_local(mutex: &Mutex<i32>) {}

fn good_test_1() {
    let mutex = Mutex::new(123);
    requires_data_local(&mutex);
    requires_mutex_local(&mutex);
    
}

fn bad_test_1(mutex: &mut Mutex<i32>) {
    requires_data_local(mutex); //~ ERROR
    // The local sharing analysis is not precise enough to accept the following
    requires_mutex_local(mutex); //~ ERROR
    
}

fn bad_test_2(mutex: &Mutex<i32>) {
    requires_data_local(mutex); //~ ERROR
    requires_mutex_local(mutex); //~ ERROR
    
}

fn main() {
    
}
