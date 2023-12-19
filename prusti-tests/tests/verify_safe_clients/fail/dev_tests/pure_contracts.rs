use prusti_contracts::*;

fn impure() {}

#[pure]
#[requires(x > 10)]
#[ensures(x > 10)]
fn good1(x: u32) -> u32 {
    123
}

#[pure]
#[requires(x > 100)]
fn good2(x: u32) -> u32 {
    good1(x)
}

#[pure]
#[requires(x > 10)]
fn good3(x: u32) -> u32 {
    if x > 10 {
        good1(x)
    } else {
        unreachable!() // Ok, because it's unreachable
    }
}

#[pure]
fn bad1() -> u32 {
    good1(0) //~ ERROR precondition of pure function call might not hold
}

fn bad2() -> u32 {
    good1(0) //~ ERROR precondition of pure function call might not hold
}

fn main() {}
