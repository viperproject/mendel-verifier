use std::ptr::addr_of;

struct T(i32);

fn good() {
    let mut a = T(111);
    let mut b = T(222);

    assert!(addr_of!(a) == addr_of!(a));
    assert!(&a as *const T == &a as *const T);
    assert!(&mut a as *const T == &mut a as *const T);
    assert!(addr_of!(a) == &a as *const T);
    assert!(&a as *const T == &mut a as *const T);

    assert!(addr_of!(a) != addr_of!(b));
    assert!(&a as *const T != &b as *const T);
    assert!(&mut a as *const T != &mut b as *const T);
    assert!(addr_of!(a) != &b as *const T);
    assert!(&a as *const T != &mut b as *const T);

    
}

fn bad_1_1() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(addr_of!(a) != addr_of!(a)); //~ ERROR the asserted expression might not hold
}

fn bad_1_2() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(&a as *const T != &a as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_1_3() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(&mut a as *const T != &mut a as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_1_4() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(addr_of!(a) != &a as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_1_5() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(&a as *const T != &mut a as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_2_1() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(addr_of!(a) == addr_of!(b)); //~ ERROR the asserted expression might not hold
}

fn bad_2_2() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(&a as *const T == &b as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_2_3() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(&mut a as *const T == &mut b as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_2_4() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(addr_of!(a) == &b as *const T); //~ ERROR the asserted expression might not hold
}

fn bad_2_5() {
    let mut a = T(111);
    let mut b = T(222);
    assert!(&a as *const T == &mut b as *const T); //~ ERROR the asserted expression might not hold
}

fn main() {}
