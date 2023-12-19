// ignore-test This is part of a module
#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;
/* EVALUATION:IGNOREBEFORE */

/// A Verus-style cell, governed by a permission.
pub struct PCell<T> {
    cell: std::cell::Cell<T>,
}

/// The (ghost) permission to access and modify a PCell.
pub struct CellPerm<T> {
    cell_id: Ghost<isize>,
    data: Ghost<T>,
}

impl<T> CellPerm<T> {
    #[pure]
    #[trusted]
    #[ghost_fn]
    pub fn cell_id(&self) -> isize {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    #[ghost_fn]
    pub fn data(&self) -> T {
        unimplemented!()
    }
}

impl<T> PCell<T> {
    #[pure_unstable]
    #[trusted]
    #[ghost_fn]
    #[ensures(result == deref_id(self as *const _))]
    pub fn id(&self) -> isize {
        unimplemented!()
    }

    #[trusted]
    #[ensures(deref_id(&result.0 as *const _) == result.1.cell_id())]
    #[ensures(deref(result.0.cell.as_ptr()) ==== result.1.data())]
    #[ensures(result.1.data() ==== old(v))]
    pub fn new(v: T) -> (PCell<T>, CellPerm<T>) {
        (
            PCell {
                cell: std::cell::Cell::new(v),
            },
            CellPerm {
                cell_id: Ghost::unknown(),
                data: Ghost::unknown(),
            },
        )
    }

    /// Mutably borrow the content of the cell.
    #[trusted]
    #[requires(perm.cell_id() == self.id())]
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[ensures(snap(&perm) ==== old(snap(&perm)))]
    #[ensures(deref(self.cell.as_ptr()) ==== old(deref(self.cell.as_ptr())))]
    #[ensures(*result ==== perm.data())]
    #[ensures(result as *const _ == self.cell.as_ptr())]
    #[after_expiry(self.id() ==== old(self.id()))]
    #[after_expiry(perm.cell_id() ==== old(perm.cell_id()))]
    #[after_expiry(snap(&self) ==== old(snap(&self)))]
    #[after_expiry(deref(self.cell.as_ptr()) ==== perm.data())]
    pub fn get_mut<'a>(&'a mut self, perm: &'a mut CellPerm<T>) -> &'a mut T {
        self.cell.get_mut()
    }
}

impl<T: Copy> PCell<T> {
    #[trusted]
    #[requires(perm.cell_id() == self.id())]
    #[ensures(perm.cell_id() == self.id())]
    #[ensures(perm.data() ==== old(v))]
    pub fn set(&self, perm: &mut CellPerm<T>, v: T) {
        self.cell.set(v)
    }

    #[trusted]
    #[requires(perm.cell_id() == self.id())]
    #[ensures(result ==== old(perm.data()))]
    pub fn get(&self, perm: &CellPerm<T>) -> T {
        self.cell.get()
    }

    #[trusted]
    #[requires(perm.cell_id() == self.id())]
    #[ensures(perm.cell_id() == self.id())]
    #[ensures(perm.data() ==== old(v))]
    #[ensures(result ==== old(perm.data()))]
    pub fn replace(&self, perm: &mut CellPerm<T>, v: T) -> T {
        self.cell.replace(v)
    }
}
