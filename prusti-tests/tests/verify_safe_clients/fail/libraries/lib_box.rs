// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::boxed::Box;
use std::ops::{Deref, DerefMut};
use std::alloc::Allocator;
/* EVALUATION:IGNOREBEFORE */

pub trait BoxSpec<T, A> {
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn as_ptr(&self) -> *const T { unimplemented!() }
}

impl<T, A: Allocator> BoxSpec<T, A> for Box<T, A> {}

#[capable(&self => readRef(self.as_ptr()))]
impl<T, A: Allocator> Box<T, A> {}

#[capable(&loc self => localRef(self.as_ptr()))]
impl<T, A: Allocator> Box<T, A> {}

#[capable(&mut self => writeRef(self.as_ptr()))]
impl<T, A: Allocator> Box<T, A> {}

#[extern_spec]
impl<T> Box<T, std::alloc::Global> {
    #[ensures(deref(result.as_ptr()) ==== old(x))]
    fn new(x: T) -> Self;
}

#[extern_spec]
impl<T, A: Allocator> std::convert::AsMut<T> for Box<T, A> {
    // Returns a reference pointing to the data
    #[ensures(result as *const _ == old(self.as_ptr()))]
    // Doesn't modify the data
    #[ensures(*result ==== old(deref(self.as_ptr())))]
    // Doesn't modify self
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    fn as_mut(&mut self) -> &mut T;
}

#[extern_spec]
impl<T, A: Allocator> Deref for Box<T, A> {
    /// Returns a reference pointing to the data
    #[pure_memory]
    #[ensures(result as *const _ == old(self.as_ptr()))]
    fn deref<'a>(&'a self) -> &'a T;
}

#[extern_spec]
impl<T, A: Allocator> DerefMut for Box<T, A> {
    // Returns a reference pointing to the data
    #[ensures(result as *const _ == old(self.as_ptr()))]
    // Doesn't modify the data
    #[ensures(*result ==== old(deref(self.as_ptr())))]
    // Doesn't modify self
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    fn deref_mut<'a>(&'a mut self) -> &'a mut T;
}
