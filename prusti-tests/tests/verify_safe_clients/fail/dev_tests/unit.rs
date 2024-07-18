use prusti_contracts::*;

fn test_unit_aliasing_1(x: &mut (), y: &mut ()) {
    // Mutable references to zero-sized types can alias.
    assert!(x as *mut _ != y as *mut _); //~ ERROR the asserted expression might not hold
}

fn test_unit_aliasing_2(x: &mut (), y: &mut ()) {
    // This is not guaranteed to hold, not even for mutable references to zero-sized types.
    assert!(x as *mut _ == y as *mut _); //~ ERROR the asserted expression might not hold
}

fn unknown<T>(x: T) {}

fn test_unit_framing(x: &()) {
    let before = *x;
    unknown(x);
    let after = *x;

    // This should never hold.
    assert!(before != after); //~ ERROR the asserted expression might not hold


}

fn incompleteness(x: &()) {
    let before = *x;
    unknown(x);
    let after = *x;

    assert!(before == after); // Incompleteness of the current axiomatization of unit types
    //~^ ERROR the asserted expression might not hold


}

fn main() {}
