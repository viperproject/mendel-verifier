use prusti_contracts::*;

#[trusted]
#[pure]
fn trusted_pure() -> i32 {
    unsafe { unimplemented!() }
}

#[trusted]
#[pure_memory]
fn trusted_pure_memory() -> i32 {
    unsafe { unimplemented!() }
}

#[trusted]
#[pure_unstable]
fn trusted_pure_unstable() -> i32 {
    unsafe { unimplemented!() }
}

#[pure]
fn pure() -> i32 {
    if true {
        unsafe { unimplemented!() } //~ ERROR only trusted or ghost pure functions can use unsafe code
    } else {
        123
    }
}

#[pure_memory]
fn pure_memory() -> i32 {
    if true {
        unsafe { unimplemented!() } //~ ERROR only trusted or ghost pure functions can use unsafe code
    } else {
        123
    }
}

#[pure_unstable]
fn pure_unstable() -> i32 {
    if true {
        unsafe { unimplemented!() } //~ ERROR only trusted or ghost pure functions can use unsafe code
    } else {
        123
    }
}

#[ghost_fn]
#[pure]
fn ghost_pure() -> i32 {
    unsafe { unimplemented!() }
}

#[ghost_fn]
#[pure_memory]
fn ghost_pure_memory() -> i32 {
    unsafe { unimplemented!() }
}

#[ghost_fn]
#[pure_unstable]
fn ghost_pure_unstable() -> i32 {
    unsafe { unimplemented!() }
}

fn main() {}
