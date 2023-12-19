#![feature(atomic_mut_ptr)]
use prusti_contracts::*;
use std::sync::atomic::AtomicI32;

#[extern_spec]
impl AtomicI32 {
    #[pure]
    pub fn as_mut_ptr(&self) -> *mut i32;
}

struct NonCell {
    value: i32,
}

impl NonCell {
    pub fn new(value: i32) -> Self {
        Self { value }
    }

    #[pure]
    #[trusted]
    pub fn get(&self) -> i32 {
        self.value
    }
}

#[pure_unstable]
#[trusted]
fn get_atomic(atomic: &AtomicI32) -> i32 {
    unimplemented!()
}

#[pure]
fn get_noncell(noncell: &NonCell) -> i32 {
    noncell.get()
}

fn test_cell() {
    let atomic = AtomicI32::new(1);
    let x = get_atomic(&atomic);
    let y = get_atomic(&atomic);
    assert!(x == y); //~ ERROR
    assert!(x == 1); //~ ERROR
}

fn test_noncell() {
    let noncell = NonCell::new(1);
    let x = get_noncell(&noncell);
    let y = get_noncell(&noncell);
    assert!(x == y); // Ok
    assert!(false); //~ ERROR
}

fn main() {}
