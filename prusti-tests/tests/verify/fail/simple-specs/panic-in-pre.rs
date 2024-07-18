use prusti_contracts::*;

#[requires({
    assert!(x != 0);
    true
})]
fn foo(x: u32) {
    assert!(x != 0); // OK
    
}

fn bad(x: u32) {
    foo(x); //~ ERROR precondition might not hold
}

fn main() {
    foo(1); // OK
}
