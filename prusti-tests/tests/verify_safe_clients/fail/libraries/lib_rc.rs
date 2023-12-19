// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::rc::Rc;
use std::ops::Deref;
use std::ptr::addr_of;
/* EVALUATION:IGNOREBEFORE */

pub trait RcSpec<T> {
    /// The address of the strong reference counter
    #[ghost_fn]
    #[trusted]
    #[pure]
    fn strong_count_ptr(this: &Self) -> *mut usize {
        unreachable!()
    }

    /// The address of the weak reference counter
    #[ghost_fn]
    #[trusted]
    #[pure]
    fn weak_count_ptr(this: &Self) -> *mut usize {
        unreachable!()
    }
}

impl<T> RcSpec<T> for Rc<T> {}

#[capable(&self => readRef(Rc::as_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&self => local(Rc::strong_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&self => local(Rc::weak_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&self => noReadRef(Rc::strong_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&self => noWriteRef(Rc::strong_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&self => noReadRef(Rc::weak_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&self => noWriteRef(Rc::weak_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&mut self if Rc::strong_count(&self) == 1 && Rc::weak_count(&self) == 0 => writeRef(Rc::as_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&mut self if Rc::strong_count(&self) == 1 && Rc::weak_count(&self) == 0 => unique(Rc::strong_count_ptr(&self)))]
impl<T> Rc<T> {}

#[capable(&mut self if Rc::strong_count(&self) == 1 && Rc::weak_count(&self) == 0 => unique(Rc::weak_count_ptr(&self)))]
impl<T> Rc<T> {}

#[extern_spec]
impl<T> Rc<T> {
    #[ensures(value ==== deref(Rc::as_ptr(&result)))]
    #[ensures(Rc::strong_count(&result) == 1)]
    #[ensures(Rc::weak_count(&result) == 0)]
    #[ensures(moved(addr_of!(value), Rc::as_ptr(&result)))]
    fn new(value: T) -> Self;

    #[pure]
    fn as_ptr(this: &Self) -> *const T;

    #[pure_unstable]
    #[ensures(result == deref(Rc::strong_count_ptr(this)))]
    fn strong_count(this: &Self) -> usize;

    #[pure_unstable]
    #[ensures(result == deref(Rc::weak_count_ptr(this)))]
    fn weak_count(this: &Self) -> usize;

    // The method doesn't change the rc
    #[ensures(snap(&this) ==== old(snap(&this)))]
    #[after_expiry(snap(&this) ==== old(snap(&this)))]
    // The method doesn't change the data or the counters
    #[ensures(deref(Rc::as_ptr(this)) ==== old(deref(Rc::as_ptr(this))))]
    #[ensures(Rc::strong_count(this) == old(Rc::strong_count(this)))]
    #[ensures(Rc::weak_count(this) == old(Rc::weak_count(this)))]
    #[after_expiry(Rc::strong_count(this) == old(Rc::strong_count(this)))]
    #[after_expiry(Rc::weak_count(this) == old(Rc::weak_count(this)))]
    // The result points to the rc's content
    #[ensures(Rc::strong_count(this) == 1 && Rc::weak_count(this) == 0 ==> result.is_some())]
    #[ensures(if let Some(ref r) = result {
        *r as *const _ == old(Rc::as_ptr(this))
    } else { true })]
    fn get_mut(this: &mut Self) -> Option<&mut T>;
}

#[extern_spec]
impl<T> Deref for Rc<T> {
    #[pure_memory]
    #[ensures(result as *const _ === old(Rc::as_ptr(self)))]
    fn deref<'a>(&'a self) -> &'a T;
}

#[extern_spec]
impl<T> Clone for Rc<T> {
    // The method doesn't change the rc
    #[ensures(snap(self) ==== old(snap(self)))]
    // The strong counter increases by 1, the weak counter does not change
    #[ensures(Rc::strong_count(self) == 1 + old(Rc::strong_count(self)))]
    #[ensures(Rc::weak_count(self) == old(Rc::weak_count(self)))]
    // The cloned rc shares the same content and counters of the original rc
    #[ensures(Rc::as_ptr(&result) ==== Rc::as_ptr(self))]
    #[ensures(Rc::strong_count_ptr(&result) ==== Rc::strong_count_ptr(self))]
    #[ensures(Rc::weak_count_ptr(&result) ==== Rc::weak_count_ptr(self))]
    fn clone(&self) -> Self;
}

#[trusted]
#[requires(Rc::strong_count(&rc) >= 1)]
// The strong counter decreases by 1, the weak counter and the data don't change
#[ensures(old(Rc::strong_count(&rc) >= 2) ==> (
    deref(old(Rc::strong_count_ptr(&rc))) == old(Rc::strong_count(&rc)) - 1
    && deref(old(Rc::weak_count_ptr(&rc))) == old(Rc::weak_count(&rc))
    && deref(old(Rc::as_ptr(&rc))) ==== old(deref(Rc::as_ptr(&rc)))
))]
pub fn drop_rc<T>(rc: Rc<T>) {
    drop(rc);
}
