use std::cell::Cell;

#[analyzer::run]
fn test() {
    let mut a = Cell::new(123);
    let b = Cell::new(456);
    a = b;
}

fn main() {}
