// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard, LockResult, TryLockResult};
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait RwLockReadGuardSpec<T> {
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

impl<'b, T> RwLockReadGuardSpec<T> for RwLockReadGuard<'b, T> {}

#[capable(&self => readRef(self.rwlock().data_ptr()))]
impl<'a, T> RwLockReadGuard<'a, T> {}

#[extern_spec]
impl<'b, T> Deref for RwLockReadGuard<'b, T> {
    /// The returned reference points to the data of the rwlock.
    #[ensures(result ==== self.rwlock().data())]
    fn deref<'a>(&'a self) -> &'a T;
}
