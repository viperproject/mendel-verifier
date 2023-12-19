// compile-flags: --crate-type=lib
#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;

// Source: https://dhghomon.github.io/easy_rust/Chapter_41.html
// Changes:
// - replaced string literals with trusted function calls
// - removed #[derive(Debug)], because of an unsupported dyn type
// - replaced println!(..) with assert!(..) to check values
// - replaced replace_with(..) with an equivalent implementation that doesn't use closures, using
//   drop_refmut(..) to explicitly drop RefMut
// - added assert!(false) epected to fail to check absence of trivial contradictions
// - added `pub` to all struct and fields

use std::cell::RefCell;

pub struct User {
    pub id: u32,
    pub year_registered: u32,
    pub username: String,
    pub active: RefCell<bool>,
    // Many other fields
}

#[trusted]
fn string_1() -> String {
    "User 1".to_string()
}

fn main_1() {
    let user_1 = User {
        id: 1,
        year_registered: 2020,
        username: string_1(),
        active: RefCell::new(true),
    };

    assert!(*user_1.active.borrow());

    assert!(false); //~ ERROR
}

fn main_2() {
    let user_1 = User {
        id: 1,
        year_registered: 2020,
        username: string_1(),
        active: RefCell::new(true),
    };

    user_1.active.replace(false);
    assert!(!*user_1.active.borrow());

    assert!(false); //~ ERROR
}

fn main_3() {
    let user_1 = User {
        id: 1,
        year_registered: 2020,
        username: string_1(),
        active: RefCell::new(true),
    };

    let date = 2020;

    let value = if date < 2000 { true } else { false };
    let mut refmut = user_1.active.borrow_mut();
    *refmut = value;
    drop_refmut(refmut);
    assert!(!*user_1.active.borrow());

    assert!(false); //~ ERROR
}

fn main_4() {
    let user_1 = User {
        id: 1,
        year_registered: 2020,
        username: string_1(),
        active: RefCell::new(true),
    };

    let borrow_one = user_1.active.borrow_mut(); // first mutable borrow - okay
    let borrow_two = user_1.active.borrow_mut(); // second mutable borrow - not okay //~ ERROR
}
