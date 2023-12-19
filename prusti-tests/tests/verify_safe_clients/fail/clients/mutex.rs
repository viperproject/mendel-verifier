// compile-flags: -Pcheck_ghost=false
#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::sync::{Mutex, MutexGuard, LockResult};
use std::ops::{Deref, DerefMut};

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

fn unknown<T>(x: T) {}

/// Test pointers
fn test_1() {
    let mut mutex = Mutex::new(123);
    let a = mutex.data_ptr();
    let b = mutex.data_ptr();
    assert!(a == b); // Succeeds, because the data is not moved

    if let Ok(data_ref) = mutex.get_mut() {
        assert!(a == data_ref as *mut _); // The reference aliases the data in the mutex
    }

    let mut mutex2 = mutex;
    let c = mutex2.data_ptr();
    assert!(a == c); // Fails, because the data moves with the mutex
    //~^ ERROR the asserted expression might not hold

    if let Ok(guard) = mutex2.lock() {
        assert!(c == mutex2.data_ptr()); // Locking the mutex doesn't move the data
        prusti_assert!(c == guard.mutex().data_ptr()); // The guard aliases the data in the mutex
        let mut guard2 = guard;
        prusti_assert!(c == guard2.mutex().data_ptr()); // Moving the guard doesn't move the data
    }

    let Ok(data_ref) = mutex2.get_mut() else { return; };
    let data_ptr = data_ref as *mut _;
    prusti_assert!(c == data_ptr); // Borrowing the mutex gives a reference to the data
    prusti_assert!(data_ptr == mutex2.data_ptr()); // Borrowing the mutex doesn't move the data

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/// Test data
fn test_2() {
    let mutex0 = Mutex::new(42);
    prusti_assert!(deref(mutex0.data_ptr()) == 42); // Succeeds

    let mut mutex = mutex0;
    prusti_assert!(deref(mutex.data_ptr()) == 42); // The data doesn't change across moves

    // Get a mutable reference to the data in the mutex
    let Ok(guard) = mutex.get_mut() else { return; };
    assert!(*guard == 42); // The value is known
    *guard = 123;
    assert!(*guard == 123); // The value is known

    // Create a local reference to the mutex
    let locally_shared_mutex = &mutex;
    let locally_shared_mutex2 = &locally_shared_mutex;
    prusti_assert!(deref(mutex.data_ptr()) == 123); // The data doesn't change

    // The data_ptr method call briefly creates a local reference for the receiver
    let mutex_data_ptr = mutex.data_ptr();
    prusti_assert!(deref(mutex_data_ptr) == 123); // The data doesn't change

    let Ok(mut guard) = mutex.lock() else { return; };
    assert!(*guard == 123);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_3() {
    let m = Mutex::new(42);
    let data = m.lock().unwrap().deref(); // The unwrap succeeds

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
