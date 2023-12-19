#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::rc::Rc;
use std::sync::Mutex;
use std::ops::Deref;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

fn unknown<T>(x: T) {}

fn test_1() {
    let v = 123;
    let mut rc = Rc::new(v);
    assert!(Rc::strong_count(&rc) == 1);
    assert!(Rc::strong_count(&rc) == 1);
    prusti_assert!(Rc::weak_count(&rc) == 0);
    prusti_assert!(Rc::weak_count(&rc) == 0);
    assert!(*rc == 123);
    assert!(*rc == 123);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_2() {
    // The data and reference count of a new Rc are known and stable.
    let v = 123;
    let mut rc = Rc::new(v);
    prusti_assert!(Rc::strong_count(&rc) == 1);
    prusti_assert!(Rc::weak_count(&rc) == 0);
    prusti_assert!(deref(Rc::as_ptr(&rc)) == 123);
    let data_ref = Rc::get_mut(&mut rc);
    assert!(data_ref.is_some());
    assert!(data_ref == Some(&mut 123));

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_3() {
    let v = 42;
    let mut x = Rc::new(Mutex::new(v)); // Postcondition: rc's reference counter is 1
    prusti_assert!(deref(as_ref(Rc::as_ptr(&x)).data_ptr()) == 42);
}

fn test_4(rc: Rc<i32>) {
    let a = *rc;
    unknown(0);
    let b = *rc;
    assert!(a == b);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_5(mut rc: Rc<i32>) {
    if Rc::strong_count(&rc) == 1 && Rc::weak_count(&rc) == 0 {
        let a: i32 = *rc;
        unknown(0);
        assert!(Rc::strong_count(&rc) == 1);
        assert!(Rc::weak_count(&rc) == 0);
        let data = Rc::get_mut(&mut rc).unwrap();
        assert!(a == *data);
        *data = 123;
        assert!(*data == 123);
        assert!(*rc == 123);

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    } else {
        assert!(Rc::strong_count(&rc) != 1 || Rc::weak_count(&rc) != 0);

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    }
}

fn test_6(mut rc: Rc<i32>, other: Rc<i32>) {
    if Rc::strong_count(&rc) == 1 && Rc::weak_count(&rc) == 0 {
        assert!(Rc::strong_count(&rc) == 1);
        assert!(Rc::weak_count(&rc) == 0);
        let data = Rc::get_mut(&mut rc).unwrap();
        assert!(Rc::as_ptr(&rc) != Rc::as_ptr(&other));

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    } else {
        assert!(Rc::strong_count(&rc) != 1 || Rc::weak_count(&rc) != 0);

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    }
}

fn test_7() {
    let v = 123;
    let mut rc = Rc::new(v);
    unknown(&rc); // This call might clone the Rc
    assert!(Rc::strong_count(&rc) == 1); //~ ERROR the asserted expression might not hold

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/// Test clone and drop
fn test_8() {
    let v = 123;
    let mut x = Rc::new(v);
    unknown(0);
    assert!(Rc::strong_count(&x) == 1);
    let mut y = x.clone();
    assert!(*x == 123);
    assert!(*y == 123);
    assert!(Rc::strong_count(&x) == 2);
    assert!(Rc::strong_count(&y) == 2);
    let mut z = x.clone();
    assert!(Rc::strong_count(&x) == 3);
    assert!(Rc::strong_count(&y) == 3);
    assert!(Rc::strong_count(&z) == 3);
    assert!(*x == 123);
    assert!(*y == 123);
    assert!(*z == 123);
    drop_rc(y);
    assert!(Rc::strong_count(&x) == 2);
    assert!(Rc::strong_count(&z) == 2);
    assert!(*x == 123);
    assert!(*z == 123);
    assert!(Rc::get_mut(&mut x).is_none());
    drop_rc(x);
    assert!(Rc::strong_count(&z) == 1);
    assert!(*z == 123);
    let data = Rc::get_mut(&mut z).unwrap();
    assert!(*data == 123);
    assert!(Rc::strong_count(&z) == 1);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
