use std::sync::{Arc, RwLock};

fn push(a: &Arc<RwLock<i32>>) -> Option<()> {
    
    //~^ ERROR
    None
}

fn main() {
    
    //~^ ERROR
}
