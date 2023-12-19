// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::atomic::AtomicI32;
/* EVALUATION:IGNOREBEFORE */

pub trait AtomicSpec<T> {
    #[ghost_fn]
    #[trusted]
    #[pure_memory]
    fn as_ptr(&self) -> *mut T { unimplemented!() }
}

impl AtomicSpec<i32> for AtomicI32 {}

#[capable(&self => write(self.as_ptr()))]
impl AtomicI32 {}

#[capable(&loc self => local(self.as_ptr()))]
impl AtomicI32 {}

#[capable(&mut self => writeRef(self.as_ptr()))]
impl AtomicI32 {}

#[extern_spec]
impl AtomicI32 {
    #[ensures(deref(result.as_ptr()) ==== old(value))]
    fn new(value: i32) -> Self;

    // The method doesn't change the atomic or its content
    #[ensures(snap(&self) === old(snap(&self)))]
    #[ensures(deref(self.as_ptr()) ==== old(deref(self.as_ptr())))]
    // The result points to the atomic's content
    #[ensures(result as *mut _ ==== self.as_ptr())]
    // The result doesn't change the atomic
    #[after_expiry(snap(&self) === old(snap(&self)))]
    fn get_mut(&mut self) -> &mut i32;
}
