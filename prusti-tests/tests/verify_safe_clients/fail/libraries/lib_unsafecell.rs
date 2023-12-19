// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::cell::UnsafeCell;
/* EVALUATION:IGNOREBEFORE */

#[capable(&mut self => writeRef(self.get()))]
impl<T> UnsafeCell<T> {}

#[extern_spec]
impl<T> UnsafeCell<T> {
    #[ensures(deref(result.get()) === old(value))]
    fn new(value: T) -> Self;

    #[pure_memory]
    fn get(&self) -> *mut T;

    // The method doesn't change the unsafecell
    #[ensures(snap(self) ==== old(snap(self)))]
    #[ensures(deref(self.get()) ==== old(deref(self.get())))]
    // The result points to the unsafecell's content
    #[ensures(result as *const _ == self.get())]
    // The result doesn't change the unsafecell
    #[after_expiry(snap(self) ==== old(snap(self)))]
    fn get_mut(&mut self) -> &mut T;

    #[ensures(result ==== old(deref(self.get())))]
    fn into_inner(self) -> T;
}
