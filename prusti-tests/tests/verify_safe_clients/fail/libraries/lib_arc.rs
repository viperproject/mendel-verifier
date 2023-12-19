// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::Arc;
use std::ops::Deref;
use std::ptr::addr_of;
/* EVALUATION:IGNOREBEFORE */

pub trait ArcSpec<T> {
    /// The address of the reference counter
    #[ghost_fn]
    #[trusted]
    #[pure]
    fn strong_count_ptr(this: &Self) -> *mut usize {
        unreachable!()
    }
}

impl<T> ArcSpec<T> for Arc<T> {}

#[capable(&self => readRef(Arc::as_ptr(&self)))]
impl<T> Arc<T> {}

#[capable(&self => noReadRef(Arc::strong_count_ptr(&self)))]
impl<T> Arc<T> {}

#[capable(&self => noWriteRef(Arc::strong_count_ptr(&self)))]
impl<T> Arc<T> {}

#[capable(&mut self if Arc::strong_count(&self) == 1 => writeRef(Arc::as_ptr(&self)))]
impl<T> Arc<T> {}

#[capable(&mut self if Arc::strong_count(&self) == 1 => unique(Arc::strong_count_ptr(&self)))]
impl<T> Arc<T> {}

#[capable(&self if Arc::strong_count(&self) == 1 => local(Arc::strong_count_ptr(&self)))]
impl<T> Arc<T> {}

#[extern_spec]
impl<T> Arc<T> {
    #[ensures(value ==== deref(Arc::as_ptr(&result)))]
    #[ensures(Arc::strong_count(&result) == 1)]
    #[ensures(moved(addr_of!(value), Arc::as_ptr(&result)))]
    fn new(value: T) -> Self;

    #[pure]
    fn as_ptr(this: &Self) -> *const T;

    #[pure_unstable]
    #[ensures((result == 1) == (deref(Arc::strong_count_ptr(this)) == 1))]
    fn strong_count(this: &Self) -> usize;

    // The method doesn't change the arc
    #[ensures(snap(&this) ==== old(snap(&this)))]
    #[after_expiry(snap(&this) ==== old(snap(&this)))]
    // The result points to the arc's content
    #[ensures(if let Some(ref r) = result {
        *r as *const _ == old(Arc::as_ptr(this))
    } else { true })]
    // The result cannot change the counter if it was 1
    #[after_expiry(old(Arc::strong_count(this) == 1) ==> Arc::strong_count(this) == 1)]
    // If the reference counter was 1, the result is not influenced by other threads
    #[ensures(if old(Arc::strong_count(this) == 1) {
        Arc::strong_count(this) == 1 &&
        result.is_some() &&
        deref(Arc::as_ptr(this)) ==== old(deref(Arc::as_ptr(this)))
    } else { true })]
    fn get_mut(this: &mut Self) -> Option<&mut T>;
}

#[extern_spec]
impl<T> Deref for Arc<T> {
    #[pure_memory]
    #[ensures(result as *const _ == Arc::as_ptr(self))]
    fn deref<'a>(&'a self) -> &'a T;
}
