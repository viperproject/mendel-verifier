#![feature(allocator_api)]
use prusti_contracts::*;

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[ensures(result == 42)] // An intentionally unsound contract
    pub fn len(&self) -> usize;
}

fn unsound_1() {
    let x: Vec<i32> = vec![];
    assert!(x.len() == 42); // Succeeds, because the contract of the call is wrong
}

fn main() {
    assert!(false); //~ ERROR
}
