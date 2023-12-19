#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/lib_mutex_inv.rs"]
mod mutex_inv_lib;
use mutex_inv_lib::*;
/* EVALUATION:IGNOREBEFORE */

/// Test a modification that satisfies the invariant
fn test_1() {
    let mut m = Mutex::new(0, Even);
    let r = m.get_mut();
    *r = 4; // Ok

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/// Test a modification that breaks the invariant
fn test_2() {
    let mut m = Mutex::new(0, Even);
    let r = m.get_mut();
    *r = 1; //~ ERROR
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
