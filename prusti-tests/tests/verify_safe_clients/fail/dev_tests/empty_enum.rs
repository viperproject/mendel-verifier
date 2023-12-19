use std::sync::{Arc, RwLock};

fn push(a: &Arc<RwLock<i32>>) -> Option<()> {
    assert!(false); // Smoke check
    //~^ ERROR
    None
}

fn main() {
    assert!(false); // Smoke check
    //~^ ERROR
}
