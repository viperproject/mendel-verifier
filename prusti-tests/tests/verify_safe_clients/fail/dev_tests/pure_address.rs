use prusti_contracts::*;

struct T(i32);

#[pure_memory]
#[ensures(&x as *const T == result)] //~ ERROR postcondition might not hold
fn bad1(x: T) -> *const T {
    let tmp = x;
    &tmp as *const T
}

fn main() {}
