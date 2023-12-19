#![feature(allocator_api)]
use prusti_contracts::*;

#[trusted]
// We don't support before_expiry
#[after_expiry(before_expiry(false))] //~ ERROR
fn assume_false_on_before_expiry(x: &mut i32) -> &mut i32 {
    unimplemented!()
}

fn test_before_expiry(x: &mut i32) {
    assume_false_on_before_expiry(x);
}

#[trusted]
#[after_expiry(false)] // An intentionally unsound contract
fn assume_false_on_expiry(x: &mut i32) -> &mut i32 {
    unimplemented!()
}

fn test_unsound_1(x: &mut i32) {
    assume_false_on_expiry(x);
    assert!(false); // Succeeds, because the contract of the call is unsound
}

#[extern_spec]
impl<T, A: std::alloc::Allocator> std::convert::AsMut<T> for std::boxed::Box<T, A> {
    #[after_expiry(false)] // An intentionally unsound contract
    fn as_mut(&mut self) -> &mut T;
}

fn test_unsound_2(mut x: Box<i32>) {
    let _ = x.as_mut();
    assert!(false); // Succeeds, because the contract of the call is unsound
}

#[trusted]
// Return a reference to the first element
#[ensures(result as *mut _ == &mut x.0 as *mut _)]
// The first element doesn't change
#[ensures(result ==== old(&mut x.0))]
// The second element must now be 42
// The second element doesn't change
#[assert_on_expiry(x.0 == 42, x.1 == old(x.1))]
fn get_mut_first(x: &mut (i32, i32)) -> &mut i32 {
    &mut x.0
}

#[ensures(snap(&x) ==== old(snap(&x)))]
fn expire(x: &mut i32) {}

fn good1() {
    let mut x = (42, 42);
    let y = get_mut_first(&mut x);
    prusti_assert!(*y == 42);
    expire(y); // The expiration succeeds
    assert!(x.0 == 42 && x.1 == 42); // Succeeds

    assert!(false); //~ ERROR
}

fn good2() {
    let mut x = (123, 42);
    let y = get_mut_first(&mut x);
    *y = 42;
    expire(y); // The expiration succeeds
    assert!(x.0 == 42 && x.1 == 42); // Succeeds

    assert!(false); //~ ERROR
}

fn bad1() {
    let mut x = (123, 42);
    let y = get_mut_first(&mut x);
    expire(y); //~ ERROR
}

fn bad2() {
    let mut x = (42, 42);
    let y = get_mut_first(&mut x);
    *y = 123;
    expire(y); //~ ERROR
}


#[trusted]
#[assert_on_expiry(false, false)]
fn unsound(x: &mut i32) -> &mut i32 { x }

#[trusted]
fn consume<T>(x: T) {}

fn wrap_unsound_1(x: &mut i32) -> &mut i32 {
    let y = unsound(x);
    y
} //~ ERROR obligation might not hold on borrow expiry

fn wrap_unsound_2(x: &mut i32) {
    let y = unsound(x);
    consume(y); //~ ERROR obligation might not hold on borrow expiry
}

#[trusted]
#[ensures(*x == old(*x) && old(x as *const _) == result as *const _)]
#[assert_on_expiry(*x == 42, true)]
fn will_be_42(x: &mut i32) -> &mut i32 { x }

#[trusted]
#[ensures(*x == old(*x) && old(x as *const _) == result as *const _)]
#[assert_on_expiry(*x == 0, true)]
fn will_be_0(x: &mut i32) -> &mut i32 { x }

#[ensures(x as *const _ == old(x as *const _) && *x == 42)]
fn set_42(x: &mut i32) {
    *x = 42;
}

fn test_1(x: &mut i32) {
    *x = 0;
    let y = will_be_42(x);
    set_42(y); // Ok, because the postcondition satisfies the assert-on-expiry.
}

fn test_2(x: &mut i32) {
    *x = 0;
    let y = will_be_42(x);
    consume(y); //~ ERROR obligation might not hold on borrow expiry
}

fn test_3(x: &mut i32) {
    *x = 0;
    let y = will_be_0(x);
    prusti_assert!(*y == 0);
    set_42(y); //~ ERROR obligation might not hold on borrow expiry
}

fn test_4(x: &mut i32) {
    *x = 0;
    let y = will_be_0(x);
    // The following doesn't ensure that `y` remains zero.
    consume(y); //~ ERROR obligation might not hold on borrow expiry
}

fn main() {}
