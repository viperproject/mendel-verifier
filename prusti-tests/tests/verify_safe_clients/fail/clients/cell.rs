#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::cell::Cell;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

fn unknown<T>(_: T) {}

fn test_1() {
    let cell = Cell::new(123);
    let a = cell.as_ptr();
    let b = cell.as_ptr();
    assert!(a == b);
    assert!(cell.get() == 123);
    assert!(cell.get() == 123);

    unknown(()); // Frame a full permission for `cell`
    prusti_assert!(cell.get() == 123);

    let shared_cell = &cell;
    let _ = 123; // Frame a shared permission for `cell`
    prusti_assert!(cell.get() == 123);

    unknown(()); // Frame a shared permission for `cell`
    // Fails, because the cell might be modified
    prusti_assert!(cell.get() == 123); //~ ERROR

    drop(shared_cell); // Extend the lifetime of the shared reference until here


}

fn test_2(x: &Cell<i32>) {
    let a = x.get();
    unknown(x);
    let b = x.get();
    let c = x.get();
    assert!(b == c);
    assert!(a == b); //~ ERROR


}

fn test_3() {
    let mut a = Cell::new(123);
    let b = Cell::new(456);
    a = b;
    assert!(a.get() == 456);
    assert!(a.get() == 123); //~ ERROR
}

fn test_4(c: &mut Cell<i32>) {
    c.set(42);
    unknown(123);
    assert!(c.get() == 42);


}

fn test_5(x: &mut (Cell<i32>,)) {
    let y = (Cell::new(456),);
    x.0.set(123);
    let framed = &x.0;
    *x = y;
    let _ = framed;
    assert!(x.0.get() == 456);
    assert!(x.0.get() == 123); //~ ERROR
}

fn test_6() {
    let mut x = Cell::new(123);
    let mut y = Cell::new(456);
    let y = x;
    assert!(y.get() == 123);
    assert!(y.get() == 456); //~ ERROR
}

fn test_7() {
    let x = Cell::new(123);
    let x_ptr = x.as_ptr();
    let mut y = Cell::new(456);
    y = x;
    let y_ptr = y.as_ptr();
    prusti_assert!(deref(y_ptr) == 123);
    assert!(x_ptr == y_ptr); //~ ERROR
    assert!(x_ptr != y_ptr); //~ ERROR
}

fn test_8() {
    let mut x = Cell::new(123);
    assert!(x.get() == 123);
    let data = x.get_mut();
    assert!(*data == 123);
    *data = 456;
    assert!(x.get() == 456);


}

#[requires(-1000000 <= deref(c.as_ptr()) && deref(c.as_ptr()) <= 1000000)]
fn test_9(c: &Cell<i32>) {
    let before = c.get();
    c.set(before + 1);
    let after = c.get();
    assert!(before + 1 == after);


}

fn test_10() {
    let cell = Cell::new(123);
    let local = 123;
    let local_ref = &local;
    assert!(local_ref as *const _ != cell.as_ptr());


}

#[requires(deref(x.as_ptr()) >= 0 && deref(x.as_ptr()) <= 999)]
#[ensures(deref(x.as_ptr()) > old(deref(x.as_ptr())))]
fn increment_positive(x: &Cell<i32>) {
    let v = x.get();
    x.set(v + 1);
}

#[requires(deref(x.as_ptr()) >= 123 && deref(x.as_ptr()) <= 999)]
#[ensures(deref(x.as_ptr()) > 123)]
fn test_11(x: &Cell<i32>) {
    increment_positive(x);

}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
