
fn disallow_unsafe() {
    let mut x = 123;
    let ptr = &mut x as *mut i32;
    let data = unsafe { *ptr }; //~ ERROR only trusted or ghost pure functions can use unsafe code
    assert!(data == 123);
}

fn main() {}
