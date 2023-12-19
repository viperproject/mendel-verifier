// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard, LockResult, TryLockResult};
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait RwLockWriteGuardSpec<T> {
    /// Returns the address of the associated rwlock.
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn rwlock_ptr(&self) -> *const RwLock<T> {
        unimplemented!()
    }

    /// Returns the associated rwloc, only usable in specifications.
    #[trusted]
    #[ghost_fn]
    #[pure_memory]
    #[ensures(result as *const _ == self.rwlock_ptr())]
    fn rwlock(&self) -> &RwLock<T> {
        unimplemented!()
    }
}

impl<'b, T> RwLockWriteGuardSpec<T> for RwLockWriteGuard<'b, T> {}

#[capable(&self => immutable(self.rwlock_ptr()))]
impl<'a, T> RwLockWriteGuard<'a, T> {}

#[capable(&self => readRef(self.rwlock().data_ptr()))]
impl<'a, T> RwLockWriteGuard<'a, T> {}

#[capable(&loc self => localRef(self.rwlock().data_ptr()))]
impl<'a, T> RwLockWriteGuard<'a, T> {}

#[capable(&mut self => writeRef(self.rwlock().data_ptr()))]
impl<'a, T> RwLockWriteGuard<'a, T> {}

#[extern_spec]
impl<'b, T> DerefMut for RwLockWriteGuard<'b, T> {
    // The method doesn't modify self nor the data protected by rwlock
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[ensures(self.rwlock().data() ==== old(self.rwlock().data()))]
    // The result doesn't modify the rwlock
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    // The returned reference points to the data of the rwlock.
    #[ensures(result as *mut _ == old(self.rwlock().data_ptr()))]
    fn deref_mut<'a>(&'a mut self) -> &'a mut T;
}

#[extern_spec]
impl<'b, T> Deref for RwLockWriteGuard<'b, T> {
    // The returned reference points to the data of the rwlock.
    #[ensures(result ==== self.rwlock().data())]
    fn deref<'a>(&'a self) -> &'a T;
}
