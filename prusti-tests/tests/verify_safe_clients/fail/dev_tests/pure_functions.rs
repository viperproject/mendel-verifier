use prusti_contracts::*;

fn impure() {}

#[pure]
fn good1() -> i32 {
    123
}

#[pure]
fn good2(x: u32) -> u32 {
    x - x // Ok, no overflows
}

#[pure]
fn good3(x: i32) -> i32 {
    if false {
        panic!() // Ok, unreachable
    } else {
        123
    }
}

#[pure]
fn good4() -> i32 {
    good1()
}

#[pure]
fn good5() -> i32 {
    let _ = good1();
    42
}

fn call_good5() {
    assert!(good5() == 42);
}

#[ghost_fn]
#[pure]
fn good6(x: String) -> String {
    x
}

#[pure]
fn bad1() -> i32 {
    impure(); //~ ERROR pure functions cannot call impure functions
    123
}

#[pure]
fn bad2() -> i32 { loop {} } //~ ERROR loops are not allowed in pure code

#[pure]
fn bad3(x: String) -> i32 { //~ ERROR non-ghost pure function argument type must be Copy
    123
}

#[pure]
fn bad4(x: i32) -> String { //~ ERROR non-ghost pure function return type must be Copy
    bad4(x)
}

#[pure]
fn bad5(x: i32) -> String {
    String::default() //~ ERROR pure functions cannot call impure functions
}

#[pure]
fn bad6(x: i32) { //~ ERROR pure code must have a non-panicking execution path
    panic!() //~ ERROR panic!(..) statement might be reachable
}

#[pure]
fn bad7(x: i32) -> i32 {
    x + x //~ ERROR assertion might fail with "attempt to add with overflow"
}

fn call_bad() {
    bad2(); //~ ERROR
}

fn main() {}
