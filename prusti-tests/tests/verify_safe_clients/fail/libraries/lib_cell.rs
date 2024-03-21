// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::cell::Cell;
/* EVALUATION:IGNOREBEFORE */

#[capable(&self => local(self.as_ptr()))]
impl<T> Cell<T> {}

#[capable(&self => noReadRef(self.as_ptr()))]
impl<T> Cell<T> {}

#[capable(&self => noWriteRef(self.as_ptr()))]
impl<T> Cell<T> {}

#[capable(&mut self => writeRef(self.as_ptr()))]
impl<T> Cell<T> {}

#[extern_spec]
impl<T> Cell<T> {
    #[pure_memory]
    pub fn as_ptr(&self) -> *mut T;

    #[ensures(deref(result.as_ptr()) ==== old(value))]
    pub fn new(value: T) -> Cell<T>;

    #[ensures(deref(self.as_ptr()) ==== old(value))]
    pub fn set(&self, value: T);

    // The method doesn't change the cell or its content
    #[ensures(snap(self) ==== old(snap(self)))]
    #[ensures(deref(self.as_ptr()) ==== old(deref(self.as_ptr())))]
    // The result points to the cell's content
    #[ensures(result as *const _ == self.as_ptr())]
    // The result doesn't change the cell
    #[after_expiry(snap(self) ==== old(snap(self)))]
    pub fn get_mut(&mut self) -> &mut T;
}

#[extern_spec]
impl<T: Copy> Cell<T> {
    #[pure_unstable]
    #[ensures(result ==== deref(self.as_ptr()))]
    pub fn get(&self) -> T;
}
