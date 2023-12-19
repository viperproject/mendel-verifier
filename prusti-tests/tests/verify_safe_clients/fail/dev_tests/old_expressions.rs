use prusti_contracts::*;

#[derive(Clone)]
pub struct T {
    pub x: u32,
}

#[pure]
fn get_x(t: &T) -> u32 {
    t.x
}

#[requires(0 < *x && *x < 1000)]
#[ensures(old(*x) == *x)]
#[ensures(false)] //~ ERROR postcondition might not hold
fn noop1(x: &mut u32) {
    *x -= 1;
    *x += 1;
}

#[requires(0 < t.x && t.x < 1000)]
#[ensures(old(get_x(t)) == get_x(t))]
#[ensures(false)] //~ ERROR postcondition might not hold
fn noop2(t: &mut T) {
    t.x -= 1;
    t.x += 1;
}

fn main() {}
