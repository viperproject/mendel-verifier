use std::sync::{Mutex, MutexGuard};

fn unknown<T>(x: T) {}

#[analyzer::run]
fn test(guard2: MutexGuard<i32>) {
    let mutex = Mutex::new(123);
    let mut guard = mutex.lock().unwrap();
    guard = guard2;
}

fn main() {}
