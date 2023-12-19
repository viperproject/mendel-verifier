use prusti_contracts::*;

#[trusted]
fn impure() -> i32 {
    unimplemented!()
}

#[trusted]
#[pure_unstable]
fn unstable() -> i32 {
    unimplemented!()
}

#[trusted]
#[pure_memory]
fn memory() -> i32 {
    unimplemented!()
}

#[trusted]
#[pure]
fn pure() -> i32 {
    unimplemented!()
}

#[ghost_fn]
#[trusted]
#[pure_unstable]
fn ghost_unstable() -> i32 {
    unimplemented!()
}

#[ghost_fn]
#[trusted]
#[pure_memory]
fn ghost_memory() -> i32 {
    unimplemented!()
}

#[ghost_fn]
#[pure_memory]
fn good1() -> i32 {
    ghost_memory()
}

#[ghost_fn]
#[pure_unstable]
fn good2() -> i32 {
    ghost_unstable()
}

#[ghost_fn]
#[pure_unstable]
fn good3() -> i32 {
    ghost_memory()
}

fn good4() {
    _ = impure();
    _ = unstable();
    _ = memory();
    _ = pure();
}

#[pure_memory]
fn bad1() -> i32 {
    ghost_memory() //~ ERROR using ghost functions from executable code is not allowed
}

#[pure_unstable]
fn bad2() -> i32 {
    ghost_unstable() //~ ERROR using ghost functions from executable code is not allowed
}

fn bad3() -> i32 {
    ghost_memory() //~ ERROR using ghost functions from executable code is not allowed
}

fn bad4() -> i32 {
    ghost_unstable() //~ ERROR using ghost functions from executable code is not allowed
}

fn main() {}
