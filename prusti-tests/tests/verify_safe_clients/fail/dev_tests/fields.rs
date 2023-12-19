use std::ptr::addr_of;

pub struct T {
    f: i32,
    g: i32,
}

fn incompleteness() {
    let x = T { f: 123, g: 456 };

    assert!(addr_of!(x.f) != addr_of!(x.g)); // Incompleteness of the current axiomatization of non-aliasing.
    //~^ ERROR the asserted expression might not hold

    assert!(addr_of!(x.f) == addr_of!(x.g)); //~ ERROR the asserted expression might not hold
}

fn workaround() {
    let mut x = T { f: 123, g: 456 };

    // Workaround: temporarily borrow the fields.
    let _tmp = (&x.f, &x.g);

    assert!(addr_of!(x.f) != addr_of!(x.g)); // Ok
    assert!(addr_of!(x.f) == addr_of!(x.g)); //~ ERROR the asserted expression might not hold
}

fn main() {}
