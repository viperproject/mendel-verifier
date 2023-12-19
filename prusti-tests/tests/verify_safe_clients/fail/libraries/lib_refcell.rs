// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::cell::*;
use std::ops::{Deref, DerefMut};
/* EVALUATION:IGNOREBEFORE */

#[capable(&self if !self.is_writing() => local(self.as_ptr()))]
impl<T> RefCell<T> {}

#[capable(&self => local(self.borrow_flag_ptr()))]
impl<T> RefCell<T> {}

#[capable(&self => noReadRef(self.borrow_flag_ptr()))]
impl<T> RefCell<T> {}

#[capable(&self => noWriteRef(self.borrow_flag_ptr()))]
impl<T> RefCell<T> {}

#[capable(&self if self.is_free() => noReadRef(self.as_ptr()))]
impl<T> RefCell<T> {}

#[capable(&self if !self.is_writing() => noWriteRef(self.as_ptr()))]
impl<T> RefCell<T> {}

#[capable(&mut self => writeRef(self.as_ptr()))]
impl<T> RefCell<T> {}

#[capable(&mut self => unique(self.borrow_flag_ptr()))]
impl<T> RefCell<T> {}

pub trait RefCellSpec<T> {
    /// Computes the address of the refcell's content as an offset from the refcell's address
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn data_ptr_offset(self_ptr: *const Self) -> *mut T {
        unimplemented!()
    }

    /// Returns the content of the refcell, only usable in specifications
    #[ghost_fn]
    #[pure_unstable]
    fn data(&self) -> T;

    /// Computes the address of the refcell's borrow flag as an offset from the refcell's address
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn borrow_flag_offset(self_ptr: *const Self) -> *mut isize {
        unimplemented!()
    }

    /// The address of the refcell's borrow flag
    #[ghost_fn]
    #[pure_memory]
    fn borrow_flag_ptr(&self) -> *mut isize {
        Self::borrow_flag_offset(self as *const _)
    }

    /// Returns the value of the refcell's borrow flag
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result == deref(self.borrow_flag_ptr()))]
    fn borrow_flag(&self) -> isize {
        deref(self.borrow_flag_ptr())
    }

    /// Returns true if the refcell is not borrowed
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result == (self.borrow_flag() == 0))]
    fn is_free(&self) -> bool {
        self.borrow_flag() == 0
    }

    /// Returns true if the refcell is read-borrowed
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result == (self.borrow_flag() > 0))]
    fn is_reading(&self) -> bool {
        self.borrow_flag() > 0
    }

    /// Returns the number of read borrows
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result == {
        let flag = self.borrow_flag();
        if flag > 0 { flag } else { 0 }
    })]
    fn num_reading(&self) -> isize {
        let flag = self.borrow_flag();
        if flag > 0 {
            flag
        } else {
            0
        }
    }

    /// Returns true if the refcell is write-borrowed
    #[ghost_fn]
    #[pure_unstable]
    #[ensures(result == (self.borrow_flag() < 0))]
    fn is_writing(&self) -> bool {
        self.borrow_flag() < 0
    }
}

impl<T> RefCellSpec<T> for RefCell<T> {
    #[ghost_fn]
    #[pure_unstable]
    fn data(&self) -> T {
        deref(self.as_ptr())
    }
}

#[extern_spec]
impl<T> RefCell<T> {
    #[pure_memory]
    #[ensures(result == RefCellSpec::data_ptr_offset(self as *const _))]
    pub fn as_ptr(&self) -> *mut T;

    #[ensures(deref(result.as_ptr()) ==== old(value))]
    #[ensures(result.is_free())]
    pub fn new(value: T) -> RefCell<T>;

    #[requires(self.is_free())]
    #[ensures(self.is_writing())]
    // The method doesn't change the content of the refcell
    #[ensures(self.data() ==== old(self.data()))]
    // The result shares the content of the refcell
    #[ensures(self ==== result.refcell())]
    pub fn borrow_mut<'b>(&'b self) -> RefMut<'b, T>;

    // The method doesn't change the content of the refcell
    #[ensures(self.data() ==== old(self.data()))]
    // If the refcell was not borrowed, the method write-borrowed it
    #[ensures(old(self.is_free()) ==> result.is_ok())]
    #[ensures(if let Ok(ref actual_result) = result {
        self.is_writing() &&
        self ==== actual_result.refcell()
    } else {
        self.borrow_flag() == old(self.borrow_flag())
    })]
    pub fn try_borrow_mut<'b>(&'b self) ->  Result<RefMut<'b, T>, BorrowMutError>;

    #[requires(!self.is_writing())]
    #[ensures(self.is_reading())]
    #[ensures(self.num_reading() == old(self.num_reading()) + 1)]
    // The method doesn't change the content of the refcell
    #[ensures(self.data() ==== old(self.data()))]
    // The result shares the content of the refcell
    #[ensures(self ==== result.refcell())]
    pub fn borrow<'b>(&'b self) -> Ref<'b, T>;

    // The method doesn't change the content of the refcell
    #[ensures(self.data() ==== old(self.data()))]
    // If the refcell was not borrowed, the method read-borrowed it
    #[ensures(old(!self.is_writing()) ==> result.is_ok())]
    #[ensures(if let Ok(ref actual_result) = result {
        self.is_reading() &&
        self.num_reading() == old(self.num_reading()) + 1 &&
        self ==== actual_result.refcell()
    } else {
        self.borrow_flag() == old(self.borrow_flag())
    })]
    pub fn try_borrow<'b>(&'b self) -> Result<Ref<'b, T>, BorrowError>;

    #[requires(self.is_free())]
    #[ensures(self.is_free())]
    // The method replaces the content of the refcell
    #[ensures(self.data() ==== old(value))]
    #[ensures(result ==== old(self.data()))]
    pub fn replace(&self, value: T) -> T;
}
