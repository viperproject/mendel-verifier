use std::sync::Mutex;

fn unknown<T>(x: T) {}

#[analyzer::run]
fn test(x: &mut u32) {
    let mut mutex = Mutex::new(123);

    let shared_mutex = &mutex;
    unknown(shared_mutex);

    let lock_result = mutex.lock();
}

fn main() {}
