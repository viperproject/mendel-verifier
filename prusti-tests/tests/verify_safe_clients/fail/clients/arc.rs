#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::sync::{Arc, Mutex};
use std::ops::Deref;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

fn unknown<T>(x: T) {}

fn test_1() {
    let v = 123;
    let mut arc = Arc::new(v);
    assert!(Arc::strong_count(&arc) == 1);
    assert!(Arc::strong_count(&arc) == 1);
    assert!(*arc == 123);
    assert!(*arc == 123);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_2() {
    // The data and reference count of a new Arc are known and stable.
    let v = 123;
    let mut arc = Arc::new(v);
    prusti_assert!(Arc::strong_count(&arc) == 1);
    prusti_assert!(deref(Arc::as_ptr(&arc)) == 123);
    let data_ref = Arc::get_mut(&mut arc);
    assert!(data_ref.is_some());
    assert!(data_ref == Some(&mut 123));

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_3() {
    let v = 42;
    let mut x = Arc::new(Mutex::new(v)); // Postcondition: arc's reference counter is 1
    prusti_assert!(deref(as_ref(Arc::as_ptr(&x)).data_ptr()) == 42);
}

fn test_4(arc: Arc<i32>) {
    let a = *arc;
    unknown(());
    let b = *arc;
    assert!(a == b);

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

fn test_5(mut arc: Arc<i32>) {
    if Arc::strong_count(&arc) == 1 {
        let a: i32 = *arc;
        unknown(());
        assert!(Arc::strong_count(&arc) == 1);
        let data = Arc::get_mut(&mut arc).unwrap();
        assert!(a == *data);
        *data = 123;
        assert!(*data == 123);
        assert!(*arc == 123);

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    } else {
        assert!(Arc::strong_count(&arc) != 1); //~ ERROR

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    }
}

fn test_6(mut arc: Arc<i32>, other: Arc<i32>) {
    if Arc::strong_count(&arc) == 1 {
        assert!(Arc::strong_count(&arc) == 1);
        let data = Arc::get_mut(&mut arc).unwrap();
        assert!(Arc::as_ptr(&arc) != Arc::as_ptr(&other));

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    } else {
        assert!(Arc::strong_count(&arc) != 1); //~ ERROR

        assert!(false); // Smoke check
        //~^ ERROR the asserted expression might not hold
    }
}

fn test_7() {
    let v = 123;
    let mut arc = Arc::new(v);
    unknown(&arc); // This call could clone the Arc
    assert!(Arc::strong_count(&arc) == 1); //~ ERROR the asserted expression might not hold

    assert!(false); // Smoke check
    //~^ ERROR the asserted expression might not hold
}

/* EVALUATION:IGNOREAFTER */
pub fn main() {}
