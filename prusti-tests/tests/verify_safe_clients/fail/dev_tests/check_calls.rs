use prusti_contracts::*;

#[trusted]
fn impure() -> i32 {
    unimplemented!()
}

#[trusted]
#[pure_unstable]
fn unstable() -> i32 {
    unimplemented!()
}

#[trusted]
#[pure_memory]
fn memory() -> i32 {
    unimplemented!()
}

#[trusted]
#[pure]
fn pure() -> i32 {
    unimplemented!()
}

fn good1() -> i32 {
    _ = impure();
    _ = memory();
    _ = unstable();
    _ = pure();
    123
}

#[pure_unstable]
fn good2() -> i32 {
    _ = pure();
    _ = memory();
    _ = unstable();
    123
}

#[pure_memory]
fn good3() -> i32 {
    _ = pure();
    _ = memory();
    123
}

#[pure]
fn good4() -> i32 {
    _ = pure();
    123
}

#[pure_unstable]
fn bad1() -> i32 {
    impure() //~ ERROR pure functions cannot call impure functions
}

#[pure_memory]
fn bad2() -> i32 {
    impure() //~ ERROR pure functions cannot call impure functions
}

#[pure_memory]
fn bad3() -> i32 {
    unstable() //~ ERROR pure memory functions cannot call pure unstable functions
}

#[pure]
fn bad4() -> i32 {
    impure() //~ ERROR pure functions cannot call impure functions
}

#[pure]
fn bad5() -> i32 {
    unstable() //~ ERROR pure stable functions cannot call pure unstable functions
}

#[pure]
fn bad6() -> i32 {
    memory() //~ ERROR pure stable functions cannot call pure memory functions
}

fn main() {}
