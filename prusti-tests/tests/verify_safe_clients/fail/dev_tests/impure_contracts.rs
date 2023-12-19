use prusti_contracts::*;

fn impure() {}

#[requires(x > 10)]
#[ensures(x > 10)]
fn good1(x: u32) -> u32 {
    123
}

#[requires(x > 100)]
fn good2(x: u32) -> u32 {
    good1(x)
}

fn bad1() -> u32 {
    good1(0) //~ ERROR precondition might not hold
}

#[ensures(true)] // Ok
#[ensures(false)] //~ ERROR postcondition might not hold
fn bad2() {}

fn main() {}
