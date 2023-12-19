use prusti_contracts::*;

fn unknown() {}

#[capable(&self => readRef(&*self as *const _))]
impl<T> Box<T> {}

#[requires(*x == 123)]
fn test(x: Box<i32>) {
    let ptr_a = &*x as *const _;
    prusti_assert!(unsafe { *ptr_a == 123 });
    unknown();
    let ptr_b = &*x as *const _;
    assert!(ptr_a == ptr_b);
    prusti_assert!(unsafe { *ptr_a == 123 });
    assert!(*x == 123);

    assert!(false); //~ ERROR the asserted expression might not hold
}

fn main() {
    let mut x = Box::new(123);
    let ptr_a = &*x as *const _;
    let ptr_b = &*x as *const _;
    assert!(ptr_a == ptr_b);

    assert!(false); //~ ERROR the asserted expression might not hold
}
