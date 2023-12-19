use std::sync::Mutex;

#[analyzer::run]
fn lock() {
    let mutex = Mutex::new(123);
    let Ok(guard) = mutex.lock() else { return; };
    assert!(*guard == 123);
}

fn main() {}
