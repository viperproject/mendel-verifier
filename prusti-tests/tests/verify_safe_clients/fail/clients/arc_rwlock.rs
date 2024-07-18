// compile-flags: -Pcheck_ghost=false
#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::ptr::addr_of;
use std::sync::{Arc, RwLock};
use std::ops::{Deref, DerefMut};

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

type Stack = Vec<i32>;
type OptError = Option<()>;

fn test_1(a: &mut Stack, b: &mut Stack) {
    let old_len = b.len();
    a.push(100);
    assert!(old_len == b.len());


}

fn push(a: &Arc<RwLock<Stack>>, v: i32) -> OptError {
    a.write().ok()?.push(v);
    None
}

fn test_2(a: Arc<RwLock<Stack>>, b: Arc<RwLock<Stack>>) -> OptError {
    let old_len = b.read().ok()?.len();
    push(&a, 100)?;
    let new_len = b.read().ok()?.len();

    // Fails, because `a` and `b` might refer to the same lock.
    // assert!(old_len == new_len); //~ ERROR

    // Fails, because `a` and `b` might refer to different locks.
    // assert!(a.data_ptr() != b.data_ptr()); //~ ERROR



    None
}

#[requires(Arc::strong_count(&a) == 1)]
#[requires(Arc::strong_count(&b) == 1)]
#[requires(!a.is_poisoned())]
#[requires(!b.is_poisoned())]
fn test_3(a: Arc<RwLock<Stack>>, b: Arc<RwLock<Stack>>) -> OptError {
    let old_len = b.read().ok()?.len();
    push(&a, 100)?;
    let new_len = b.read().ok()?.len();

    // The following assertion fails, because the counter value is not framed across impure methods
    // like `read()`, so across `push` the content of the lock is not framed.
    // assert!(old_len == new_len); //~ ERROR

    assert!(a.data_ptr() != b.data_ptr()); // Ok



    None
}

// fn test_4(a: Arc<RwLock<Stack>>, b: Arc<RwLock<Stack>>) -> OptError {
//     let mut guard_a = a.write().ok()?;
//     let guard_b = b.read().ok()?;

//     let old_len = guard_b.len();
//     guard_a.push(100);
//     let new_len = guard_b.len();

//     assert!(old_len == new_len); // Succeeds
//     assert!(a.data_ptr() != b.data_ptr()); // Succeeds

//     None
// }

/// Test framing
fn test_5(a: Arc<RwLock<Stack>>, b: Arc<RwLock<Stack>>) -> OptError {
    let aptr = a.data_ptr();
    let tmp1 = a.write();
    let tmp2 = tmp1.ok();
    let mut guard_a = tmp2?;
    prusti_assert!(a.data_ptr() == aptr);
    prusti_assert!(guard_a.rwlock().data_ptr() == aptr);
    None
}

/// Test nonaliasing
fn test_6(a: Arc<RwLock<Stack>>, b: Arc<RwLock<Stack>>) -> OptError {
    let mut guard_a = a.write().ok()?;
    let guard_b = b.read().ok()?;
    prusti_assert!(guard_a.rwlock().data_ptr() != guard_b.rwlock().data_ptr());
    prusti_assert!(a.data_ptr() != b.data_ptr());
    prusti_assert!(addr_of!(a) != addr_of!(b));
    prusti_assert!(&a as *const _ != &b as *const _);



    None
}

/// Test nonaliasing
fn test_7(a: &Arc<RwLock<Stack>>, b: &Arc<RwLock<Stack>>) -> OptError {
    let guard_a = a.write().ok()?;
    let guard_b = b.read().ok()?;

    prusti_assert!(guard_a.rwlock().data_ptr() != guard_b.rwlock().data_ptr());
    prusti_assert!(a.data_ptr() != b.data_ptr());
    prusti_assert!(Arc::as_ptr(a) != Arc::as_ptr(b));
    prusti_assert!(addr_of!(*a) != addr_of!(*b));
    prusti_assert!(a as *const _ != b as *const _);



    None
}

/// Test deref_mut
fn test_8(x: RwLock<i32>) -> OptError {
    let mut guard = x.write().ok()?;
    *guard = 123;

    let data = guard.deref_mut();
    assert!(*data == 123);

    *data = 42;
    assert!(*guard == 42);



    None
}

// #[requires(Arc::strong_count(&a) == 1)]
// fn incompleteness_1(a: Arc<RwLock<Stack>>, b: Arc<RwLock<Stack>>) {
//     // The following assertion fails, because even if `a` has full ownership of `a.data_ptr()`,
//     // nothing prevents `b.data_ptr()` from returning a pointer to the same memory location.
//     prusti_assert!(a.data_ptr() != b.data_ptr()); // Incompleteness


// }

// #[requires(Arc::strong_count(&a) == 1)]
// fn incompleteness_2(a: Arc<RwLock<Stack>>, v: i32) -> OptError {
//     a.write().ok()?.push(v);
//     // The following assertion fails, because the counter value is not framed across impure method
//     // calls like `write()`, `ok()`, `?`.
//     prusti_assert!(Arc::strong_count(&a) == 1); // Incompleteness



//     None
// }

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
