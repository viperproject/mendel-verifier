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
// - added assert!(..) to check the value of on_sale
// - added assert!(false) epected to fail to check absence of trivial contradictions

use std::cell::Cell;

struct PhoneModel {
    company_name: String,
    model_name: String,
    screen_size: f32,
    memory: usize,
    date_issued: u32,
    on_sale: Cell<bool>,
}

#[trusted]
fn string_1() -> String {
    "YY Electronics".to_string()
}

#[trusted]
fn string_2() -> String {
    "Super Phone 3000".to_string()
}

fn main() {
    let super_phone_3000 = PhoneModel {
        company_name: string_1(),
        model_name: string_2(),
        screen_size: 7.5,
        memory: 4_000_000,
        date_issued: 2020,
        on_sale: Cell::new(true),
    };

    // 10 years later, super_phone_3000 is not on sale anymore
    super_phone_3000.on_sale.set(false);

    assert!(super_phone_3000.on_sale.get() == false);
    assert!(false); //~ ERROR
}
