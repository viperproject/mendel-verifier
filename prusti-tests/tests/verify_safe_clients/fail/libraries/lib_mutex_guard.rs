// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::{Mutex, MutexGuard, LockResult, TryLockResult};
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait MutexGuardSpec<T> {
    /// Returns the address of the associated mutex
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn mutex_ptr(&self) -> *const Mutex<T> {
        unimplemented!()
    }

    /// Returns the associated mutex, only usable in specifications
    #[trusted]
    #[ghost_fn]
    #[pure_memory]
    #[ensures(result as *const _ == self.mutex_ptr())]
    fn mutex(&self) -> &Mutex<T> {
        unimplemented!()
    }
}

impl<'b, T> MutexGuardSpec<T> for MutexGuard<'b, T> {}

#[capable(&self => immutable(self.mutex_ptr()))]
impl<'a, T> MutexGuard<'a, T> {}

#[capable(&self => immutable(self.mutex().lock_ptr()))]
impl<'a, T> MutexGuard<'a, T> {}

#[capable(&self => immutable(self.mutex().poison_ptr()))]
impl<'a, T> MutexGuard<'a, T> {}

#[capable(&self => readRef(self.mutex().data_ptr()))]
impl<'a, T> MutexGuard<'a, T> {}

#[capable(&loc self => localRef(self.mutex().data_ptr()))]
impl<'a, T> MutexGuard<'a, T> {}

#[capable(&mut self => writeRef(self.mutex().data_ptr()))]
impl<'a, T> MutexGuard<'a, T> {}

#[extern_spec]
impl<'b, T> DerefMut for MutexGuard<'b, T> {
    // The method doesn't modify the guard or mutex
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[ensures(self.mutex().data() ==== old(self.mutex().data()))]
    // The result doesn't modify the mutex
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    // The returned reference points to the data of the mutex.
    #[ensures(result as *mut _ == old(self.mutex().data_ptr()))]
    fn deref_mut<'a>(&'a mut self) -> &'a mut T;
}

#[extern_spec]
impl<'b, T> Deref for MutexGuard<'b, T> {
    // The returned reference points to the data of the mutex.
    #[ensures(result ==== self.mutex().data())]
    fn deref<'a>(&'a self) -> &'a T;
}

#[trusted]
#[ensures(localRef_capability(old(x.mutex_ptr())) ==> (
    old(x.mutex()).data() ==== old(x.mutex().data())) &&
    !old(x.mutex()).is_locked() &&
    !old(x.mutex()).is_poisoned()
)]
pub fn drop_guard<T>(x: MutexGuard<T>) {}
