// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard, LockResult, TryLockResult};
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait RwLockSpec<T> {
    /// Returns the content of the rwlock, only usable in specifications
    #[ghost_fn]
    #[pure_unstable]
    fn data(&self) -> &T {
        as_ref(self.data_ptr())
    }

    /// The address of the data contained in a rwlock.
    #[ghost_fn]
    #[pure_memory]
    fn data_ptr(&self) -> *mut T {
        // To simulate a #[pure_offset] annotation
        Self::data_ptr_offset(self as *const _ as *mut _)
    }

    /// The address of the data contained in a rwlock, given the address of the rwlock.
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn data_ptr_offset(self_ptr: *mut Self) -> *mut T {
        unimplemented!()
    }

    /// The address of the byte storing the poison flag.
    #[ghost_fn]
    #[pure_memory]
    fn poison_ptr(&self) -> *mut bool {
        // To simulate a #[pure_offset] annotation
        Self::poison_ptr_offset(self as *const _ as *mut _)
    }

    /// The address of the poison flag of a mutex, given the address of the mutex.
    #[ghost_fn]
    #[trusted]
    #[pure]
    fn poison_ptr_offset(self_ptr: *mut Self) -> *mut bool {
        unimplemented!()
    }
}

impl<T> RwLockSpec<T> for RwLock<T> {}

#[capable(&mut self if !self.is_poisoned() => writeRef(self.data_ptr()))]
impl<T> RwLock<T> {}

#[capable(&self => noWriteRef(self.poison_ptr()))]
impl<T> RwLock<T> {}

#[capable(&loc self if !self.is_poisoned() => local(self.data_ptr()))]
impl<T> RwLock<T> {}

#[capable(&loc self => local(self.poison_ptr()))]
impl<T> RwLock<T> {}

#[extern_spec]
impl<T> RwLock<T> {
    #[ensures(old(value) ==== deref(result.data_ptr()))]
    fn new(value: T) -> Self;

    #[pure_unstable]
    #[ensures(result == deref(self.poison_ptr()))]
    fn is_poisoned(&self) -> bool;

    /// The result of a successful lock is a reference pointing to the data protected by the rwlock.
    /// This method doesn't modify the protected data, nor other fields of the rwlock.
    #[ensures(if let Ok(ref r) = result {
        // The returned reference points to the data in the rwlock
        *r as *const _ as *mut _ == old(self.data_ptr())
    } else { true })]
    // The method doesn't change the data protected by rwlock
    #[ensures(deref(self.data_ptr()) ==== old(deref(self.data_ptr())))]
    // The method doesn't modify self
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    #[ensures(!old(self.is_poisoned()) ==> result.is_ok())]
    #[after_expiry(!old(self.is_poisoned()) ==> !self.is_poisoned())]
    fn get_mut(&mut self) -> LockResult<&mut T>;

    /// The result of a successful lock operation is a read guard whose data aliases the data of
    /// the rwlock. The method doesn't always guarantee that the data doesn't change; it would be
    /// unsound.
    #[ensures(if let Ok(ref guard) = result {
        guard.rwlock() ==== self
    } else { true })]
    // If the rwlock is not shared nor poisoned, then it's ensured that when the method terminates
    // without panicking the data is still the same and no error is returned.
    #[ensures(old(localRef_capability(self as *const _)) && !old(self.is_poisoned()) ==> (
        result.is_ok() && self.data() ==== old(self.data())
    ))]
    fn read(&self) -> LockResult<RwLockReadGuard<'_, T>>;

    /// The result of a successful lock operation is a write guard whose data aliases the data of
    /// the rwlock. The method doesn't always guarantee that the data doesn't change; it would be
    /// unsound.
    #[ensures(if let Ok(ref guard) = result {
        guard.rwlock() ==== self
    } else { true })]
    // If the rwlock is not shared nor poisoned, then it's ensured that when the method terminates
    // without panicking the data is still the same and no error is returned.
    #[ensures(old(localRef_capability(self as *const _)) && !old(self.is_poisoned()) ==> (
        result.is_ok() && self.data() ==== old(self.data())
    ))]
    fn write(&self) -> LockResult<RwLockWriteGuard<'_, T>>;

    /// The result of a successful lock operation is a write guard whose data aliases the data of
    /// the rwlock. The method doesn't always guarantee that the data doesn't change; it would be
    /// unsound.
    #[ensures(if let Ok(ref guard) = result {
        guard.rwlock() ==== self
    } else { true })]
    // If the rwlock is not shared nor poisoned, then it's ensured that when the method terminates
    // without panicking the data is still the same and no error is returned.
    #[ensures(old(localRef_capability(self as *const _)) && !old(self.is_poisoned()) ==> (
        result.is_ok() && self.data() ==== old(self.data())
    ))]
    fn try_write(&self) -> TryLockResult<RwLockWriteGuard<'_, T>>;
}
