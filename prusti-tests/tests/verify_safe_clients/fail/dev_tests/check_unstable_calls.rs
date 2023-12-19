use prusti_contracts::*;

#[trusted]
#[pure_unstable]
#[ensures(result > 10)]
fn unstable(x: u32) -> u32 {
    unimplemented!()
}

#[pure_unstable]
fn bad_executable_unstable(x: u32) -> u32 {
    let y = unstable(x); //~ ERROR unstable function called more than once per path
    unstable(y)
}

#[pure_unstable]
fn good_executable_unstable(x: u32, g: bool) -> u32 {
    unstable(x); // This has no effect, because it's pure
    if g {
        unstable(x)
    } else {
        unstable(x)
    }
}

#[ghost_fn]
#[pure_unstable]
fn good_ghost_unstable(x: u32) -> u32 {
    let y = unstable(x); // This is allowed, because it's ghost
    unstable(y)
}

#[ensures(good_ghost_unstable(0) > 10)]
fn client(){}

#[trusted]
#[pure]
#[requires(unstable(0) > 10)]
//~^ ERROR unstable functions can only be called from impure code or from pure unstable code
fn bad_pure_1() -> u32 { unimplemented!() }

#[trusted]
#[pure]
#[ensures(unstable(0) > 10)]
//~^ ERROR unstable functions can only be called from impure code or from pure unstable code
fn bad_pure_2() -> u32 { unimplemented!() }

#[trusted]
#[pure_memory]
#[requires(unstable(0) > 10)]
//~^ ERROR unstable functions can only be called from impure code or from pure unstable code
fn bad_pure_memory_1() -> u32 { unimplemented!() }

#[trusted]
#[pure_memory]
#[ensures(unstable(0) > 10)]
//~^ ERROR unstable functions can only be called from impure code or from pure unstable code
fn bad_pure_memory_2() -> u32 { unimplemented!() }

#[trusted]
#[requires(unstable(0) > 10)]
fn good_impure_1() { }

#[trusted]
#[ensures(unstable(0) > 10)]
fn good_impure_2() { }

fn client2() {
    bad_pure_1(); //~ ERROR
    bad_pure_2(); //~ ERROR
    bad_pure_memory_1(); //~ ERROR
    bad_pure_memory_2(); //~ ERROR
}

fn main() {}
