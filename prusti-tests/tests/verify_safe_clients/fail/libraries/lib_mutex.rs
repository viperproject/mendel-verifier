// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::sync::{Mutex, MutexGuard, LockResult, TryLockResult};
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

pub trait MutexSpec<T> {
    /// Returns the content of the mutex, only usable in specifications
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result ==== as_ref(self.data_ptr()))]
    fn data(&self) -> &T {
        as_ref(self.data_ptr())
    }

    /// The address of the data contained in a mutex.
    /// - `pure_memory`: The address is an offset from the address of self; moving the mutex also moves
    ///   the data.
    #[ghost_fn]
    #[pure_memory]
    #[ensures(result == Self::data_ptr_offset(self as *const _ as *mut _))]
    fn data_ptr(&self) -> *mut T {
        // To simulate a #[pure_offset] annotation
        Self::data_ptr_offset(self as *const _ as *mut _)
    }

    /// The address of the data contained in a mutex, given the address of the mutex.
    #[ghost_fn]
    #[trusted]
    #[pure]
    fn data_ptr_offset(self_ptr: *mut Self) -> *mut T {
        unimplemented!()
    }

    /// The address of the byte storing the poison flag.
    #[ghost_fn]
    #[pure_memory]
    #[ensures(result == Self::poison_ptr_offset(self as *const _ as *mut _))]
    fn poison_ptr(&self) -> *mut bool {
        // To simulate a #[pure_offset] annotation
        Self::poison_ptr_offset(self as *const _ as *mut _)
    }

    /// The address of the poison flag of a mutex, given the address of the mutex.
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn poison_ptr_offset(self_ptr: *mut Self) -> *mut bool {
        unimplemented!()
    }

    /// Returns true if the mutex is locked
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result ==== deref(self.lock_ptr()))]
    fn is_locked(&self) -> bool {
        deref(self.lock_ptr())
    }

    /// The address of the byte storing the lock flag.
    #[ghost_fn]
    #[pure_memory]
    #[ensures(result == Self::lock_ptr_offset(self as *const _ as *mut _))]
    fn lock_ptr(&self) -> *mut bool {
        // To simulate a #[pure_offset] annotation
        Self::lock_ptr_offset(self as *const _ as *mut _)
    }

    /// The address of the lock flag of a mutex, given the address of the mutex.
    #[ghost_fn]
    #[trusted]
    #[pure]
    fn lock_ptr_offset(self_ptr: *mut Self) -> *mut bool {
        unimplemented!()
    }
}

impl<T> MutexSpec<T> for Mutex<T> {}

#[capable(&mut self if !self.is_poisoned() => writeRef(self.data_ptr()))]
impl<T> Mutex<T> {}

#[capable(&mut self => unique(self.lock_ptr()))]
impl<T> Mutex<T> {}

#[capable(&loc self if !self.is_poisoned() => local(self.data_ptr()))]
impl<T> Mutex<T> {}

#[capable(&self => noWriteRef(self.lock_ptr()))]
impl<T> Mutex<T> {}

#[capable(&self if !self.is_locked() => noReadRef(self.data_ptr()))]
impl<T> Mutex<T> {}

#[capable(&self if !self.is_locked() => noWriteRef(self.data_ptr()))]
impl<T> Mutex<T> {}

#[capable(&self => noWriteRef(self.poison_ptr()))]
impl<T> Mutex<T> {}

#[capable(&loc self => local(self.lock_ptr()))]
impl<T> Mutex<T> {}

#[capable(&loc self => local(self.poison_ptr()))]
impl<T> Mutex<T> {}

#[extern_spec]
impl<T> Mutex<T> {
    #[ensures(old(value) ==== deref(result.data_ptr()))]
    #[ensures(!result.is_poisoned())]
    #[ensures(!result.is_locked())]
    fn new(value: T) -> Self;

    #[pure_unstable]
    #[ensures(result == deref(self.poison_ptr()))]
    fn is_poisoned(&self) -> bool;

    /// The result of a successful lock is a reference pointing to the data protected by the mutex.
    /// This method doesn't modify the protected data, nor other fields of the mutex.
    #[ensures(if let Ok(ref r) = result {
        // The returned reference points to the data in the mutex
        *r as *const _ as *mut _ == old(self.data_ptr())
    } else { true })]
    // The method doesn't change the data protected by mutex
    #[ensures(deref(self.data_ptr()) ==== old(deref(self.data_ptr())))]
    // The method doesn't modify self
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    #[ensures(!old(self.is_poisoned()) ==> result.is_ok())]
    #[after_expiry(!old(self.is_poisoned()) ==> !self.is_poisoned())]
    #[after_expiry(!self.is_locked())]
    fn get_mut(&mut self) -> LockResult<&mut T>;

    /// The result of a successful lock operation is a mutex guard whose data aliases the data of
    /// the mutex. The lock doesn't always guarantee that the data doesn't change; it would be unsound.
    #[ensures(if let Ok(ref guard) = result {
        guard.mutex() ==== self && self.is_locked() && !self.is_poisoned()
    } else { true })]
    // If the mutex is not shared nor poisoned, then it's ensured that when the method terminates
    // without panicking the data is still the same and no error is returned.
    #[ensures(old(localRef_capability(self as *const _)) && !old(self.is_poisoned()) ==> (
        result.is_ok() && self.data() ==== old(self.data())
    ))]
    fn lock(&self) -> LockResult<MutexGuard<'_, T>>;

    /// The result of a successful lock operation is a mutex guard whose data aliases the data of
    /// the mutex. The lock doesn't always guarantee that the data doesn't change; it would be unsound.
    #[ensures(if let Ok(ref guard) = result {
        guard.mutex() ==== self && self.is_locked() && !self.is_poisoned()
    } else { true })]
    // If the mutex is not shared nor poisoned, then it's ensured that when the method terminates
    // without panicking the data is still the same and no error is returned.
    #[ensures(old(localRef_capability(self as *const _)) && !old(self.is_poisoned()) ==> (
        result.is_ok() && self.data() ==== old(self.data())
    ))]
    fn try_lock(&self) -> TryLockResult<MutexGuard<'_, T>>;
}
