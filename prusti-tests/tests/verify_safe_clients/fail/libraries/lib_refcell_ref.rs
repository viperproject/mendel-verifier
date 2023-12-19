// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::cell::*;
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait RefSpec<T> {
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

impl<'b, T> RefSpec<T> for Ref<'b, T> {}

#[capable(&self => immutable(self.refcell_ptr()))]
impl<'b, T> Ref<'b, T> {}

#[capable(&self => readRef(self.refcell().as_ptr()))]
impl<'b, T> Ref<'b, T> {}

#[capable(&self => noWriteRef(self.refcell().borrow_flag_ptr()))]
impl<'b, T> Ref<'b, T> {}

#[extern_spec]
impl<'b, T> Deref for Ref<'b, T> {
    #[pure_memory]
    #[ensures(result as *const _ == self.refcell().as_ptr())]
    fn deref<'a>(&'a self) -> &'a T;
}

#[trusted]
// Dropping a Ref doesn't change the refcell
#[ensures(old(x.refcell()) ==== old(&x).refcell())]
// Dropping a Ref doesn't change the content of the refcell
#[ensures(deref(old(x.refcell().as_ptr())) ==== old(deref(x.refcell().as_ptr())))]
// Dropping a Ref decreases the number of read borrows
#[ensures(deref(old(x.refcell().borrow_flag_ptr())) == old(deref(x.refcell().borrow_flag_ptr())) - 1)]
#[ensures(deref(old(x.refcell().borrow_flag_ptr())) >= 0)]
pub fn drop_ref<T>(x: Ref<T>) {}
