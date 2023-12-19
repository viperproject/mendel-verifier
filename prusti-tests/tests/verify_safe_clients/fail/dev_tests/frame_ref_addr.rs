use prusti_contracts::*;

#[ensures(old(u.0) as *mut _ == result.0)]
#[ensures(old(u.1) as *mut _ == result.1)]
fn tuple2_to_ptr<T, U>(u: (&mut T, &mut U)) -> (*mut T, *mut U) {
    (u.0 as *mut T, u.1 as *mut U)
}

fn test() {
    let mut x = 42;
    let mut y = Ghost::<i32>::unknown();
    let x_ref = &mut x;
    let y_ref = &mut y;
    let x_ptr = x_ref as *mut _;
    let y_ptr = y_ref as *mut _;
    let t = (x_ref, y_ref);
    let u = tuple2_to_ptr(t);
    prusti_assert!(u === (x_ptr, y_ptr));
    assert!(u.0 == x_ptr);
    assert!(u.1 == y_ptr);

    assert!(false); //~ ERROR
}

fn main() {
    assert!(false); //~ ERROR
}
