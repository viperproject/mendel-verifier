fn test(
    b: *mut u64,
    c: *const *mut u64,
) {}

fn main() {
    let mut a: u64 = 123;
    let b = &mut a as *mut u64;
    let c = &b as *const *mut u64;
}
