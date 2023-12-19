// ignore-test This is part of a module
#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

/// A Verus-style pointer, governed by a permission.
pub struct PPtr<T> {
    ptr: *mut T,
}

/// The (ghost) permission to access and modify a PPtr.
pub struct PointsTo<T> {
    pptr_id: Ghost<isize>,
    ptr: Ghost<*mut T>,
}

/// A shared reference to PointsTo guarantees immutability
#[capable(&self => immutable(self.as_ptr()))]
impl <T> PointsTo<T> {}

/// A mutable reference to PointsTo guarantees uniqueness
#[capable(&mut self => unique(self.as_ptr()))]
impl <T> PointsTo<T> {}

impl<T> PointsTo<T> {
    #[pure]
    #[trusted]
    #[ghost_fn]
    pub fn pptr_id(&self) -> isize {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    #[ghost_fn]
    pub fn as_ptr(&self) -> *const T {
        unimplemented!()
    }
}

impl<T> PPtr<T> {
    #[pure_unstable]
    #[trusted]
    #[ghost_fn]
    #[ensures(result == deref_id(self as *const _))]
    pub fn id(&self) -> isize {
        unimplemented!()
    }

    #[pure]
    pub fn as_ptr(&self) -> *const T {
        self.ptr as *const _
    }

    /// Allocate the value and return a pointer to it
    #[trusted]
    #[ensures(deref(result.0.as_ptr()) ==== old(v))]
    #[ensures(result.1.pptr_id() == result.0.id())]
    #[ensures(result.1.as_ptr() == result.0.as_ptr())]
    pub fn new(v: T) -> (PPtr<T>, PointsTo<T>) {
        (
            PPtr {
                ptr: todo!(),
            },
            PointsTo {
                pptr_id: Ghost::unknown(),
                ptr: Ghost::unknown(),
            },
        )
    }

    /// Borrow the target of the pointer
    #[trusted]
    // `perm` must have the right id
    #[requires(perm.pptr_id() == self.id())]
    // The target of the pointer doesn't change
    #[ensures(deref(self.as_ptr()) === old(deref(self.as_ptr())))]
    // The result points to the target of the pointer
    #[ensures(result as *const _ == self.as_ptr())]
    pub fn borrow<'a>(&self, perm: &'a PointsTo<T>) -> &'a T {
        todo!()
    }

    /// Mutably borrow the target of the pointer.
    /// Note: sound only when a verifier proves that the precondition holds.
    #[trusted]
    // `perm` must have the right id
    #[requires(perm.pptr_id() == self.id())]
    // The method doesn't change `perm`
    #[ensures(snap(&perm) === old(snap(&perm)))]
    // The returned reference doesn't change `perm`
    #[after_expiry(snap(&perm) === old(snap(&perm)))]
    // The target of the pointer doesn't change
    #[ensures(deref(self.as_ptr()) === old(deref(self.as_ptr())))]
    // The result points to the target of the pointer
    #[ensures(result as *const _ == self.as_ptr())]
    pub fn verified_borrow_mut<'a>(&self, perm: &'a mut PointsTo<T>) -> &'a mut T {
        todo!()
    }

    /// Deallocate the target of the pointer
    #[trusted]
    // `perm` must have the right id
    #[requires(perm.pptr_id() == deref_id(&self as *const _))]
    pub fn dispose(self, perm: PointsTo<T>) {
        todo!()
    }
}
