use std::cell::UnsafeCell;

fn test(
    b: UnsafeCell<u32>,
    c: UnsafeCell<UnsafeCell<u32>>,
) {}

fn main() {
    let x: u32 = 123;
    let y = UnsafeCell::new(x);
    let z = UnsafeCell::new(y);
}
