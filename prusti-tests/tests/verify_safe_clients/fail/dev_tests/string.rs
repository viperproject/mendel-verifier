use prusti_contracts::*;

fn test_string_aliasing(x: &mut String, y: &mut String) {
    assert!(x as *mut _ != y as *mut _); // Ok
    assert!(x as *mut _ == y as *mut _); //~ ERROR the asserted expression might not hold
}

fn unknown<T>(x: T) {}

#[trusted]
#[pure]
fn length(x: &String) -> usize {
    x.len()
}

fn test_string_framing(x: &String) {
    let before = length(x);
    unknown(x);
    let after = length(x);
    assert!(before == after); // Ok
    assert!(before != after); //~ ERROR the asserted expression might not hold
}

fn main() {}
