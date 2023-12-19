use prusti_contracts::*;

fn good() {
    loop {}
    panic!(); // Ok, unreachable
}

fn bad() {
    panic!(); //~ ERROR
    loop {}
}

fn main() {}
