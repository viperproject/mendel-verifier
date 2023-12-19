// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::cell::*;
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait RefMutSpec<T> {
    /// Returns the address of the associated refcell
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn refcell_ptr(&self) -> *const RefCell<T> {
        unimplemented!()
    }

    /// Returns the associated refcell, only usable in specifications
    #[trusted]
    #[ghost_fn]
    #[pure_memory]
    #[ensures(result as *const _ == self.refcell_ptr())]
    fn refcell(&self) -> &RefCell<T> {
        unimplemented!()
    }
}

impl<'b, T> RefMutSpec<T> for RefMut<'b, T> {}

#[capable(&self => immutable(self.refcell_ptr()))]
impl<'b, T> RefMut<'b, T> {}

#[capable(&self => readRef(self.refcell().as_ptr()))]
impl<'b, T> RefMut<'b, T> {}

#[capable(&mut self => writeRef(self.refcell().as_ptr()))]
impl<'b, T> RefMut<'b, T> {}

#[capable(&self => immutable(self.refcell().borrow_flag_ptr()))]
impl<'b, T> RefMut<'b, T> {}

#[capable(&self => noWriteRef(self.refcell().borrow_flag_ptr()))]
impl<'b, T> RefMut<'b, T> {}

#[extern_spec]
impl<'b, T> Deref for RefMut<'b, T> {
    #[pure_memory]
    #[ensures(result as *const _ == self.refcell().as_ptr())]
    fn deref<'a>(&'a self) -> &'a T;
}

#[extern_spec]
impl<'b, T> DerefMut for RefMut<'b, T> {
    #[ensures(result as *mut _ == self.refcell().as_ptr())]
    // The method doesn't change the RefMut
    #[ensures(snap(&self) ==== old(snap(&self)))]
    // The method doesn't change the content of the refcell
    #[ensures(self.refcell().data() ==== old(self.refcell().data()))]
    // The result doesn't change the RefMut
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    fn deref_mut<'a>(&'a mut self) -> &'a mut T;
}

#[trusted]
// Dropping a RefMut doesn't change the refcell
#[ensures(old(x.refcell()) ==== old(&x).refcell())]
// Dropping a RefMut doesn't change the content of the refcell
#[ensures(deref(old(x.refcell().as_ptr())) ==== old(deref(x.refcell().as_ptr())))]
// Dropping a RefMut frees the refcell
#[ensures(deref(old(x.refcell().borrow_flag_ptr())) == 0)]
pub fn drop_refmut<T>(x: RefMut<T>) {}
