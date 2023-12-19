// ignore-test This is part of a module
#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;

#[path = "../libraries/mod.rs"]
mod libraries;
pub use libraries::*;
/* EVALUATION:IGNOREBEFORE */

/// Trait to define the invariant of a type T
pub trait Inv<T: ?Sized> {
    #[pure]
    fn inv(&self, x: &T) -> bool;
}

/// A Creusot-like mutex with an invariant.
pub struct Mutex<T, I: Inv<T>>(std::sync::Mutex<T>, I);

// The following specification assumes that the mutex is never poisoned.
impl<T, I: Inv<T> + Copy> Mutex<T, I> {
    #[trusted]
    #[requires(i.inv(&val))]
    pub fn new(val: T, i: I) -> Self {
        Mutex(std::sync::Mutex::new(val), i)
    }

    #[trusted]
    #[ensures(self.1.inv(&result))]
    pub fn into_inner(self) -> T {
        self.0.into_inner().unwrap()
    }

    #[trusted]
    #[ensures(result as *mut _ == self.0.data_ptr())]
    #[ensures(snap(&self) ==== old(snap(&self)))]
    #[assert_on_expiry(old(&self.1).inv(old(&self.0).data()), snap(&self) ==== old(snap(&self)))]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut().unwrap()
    }

    #[trusted]
    #[ensures(self.1 === result.1)]
    pub fn lock(&self) -> MutexGuard<'_, T, I> {
        MutexGuard(self.0.lock().unwrap(), self.1)
    }
}

/// A mutex guard with an invariant.
pub struct MutexGuard<'a, T: ?Sized + 'a, I: Inv<T>>(std::sync::MutexGuard<'a, T>, I);

impl<'a, T, I: Inv<T>> MutexGuard<'a, T, I> {
    #[trusted]
    #[ensures(self.1.inv(result))]
    #[ensures(result as *const _ == self.0.mutex().data_ptr())]
    pub fn deref(&self) -> &T {
        &*self.0
    }

    #[trusted]
    #[requires(self.1.inv(&v))]
    pub fn set(&mut self, v: T) {
        *self.0 = v;
    }
}

#[derive(Clone, Copy)]
pub struct Even;

impl Inv<u32> for Even {
    #[pure]
    fn inv(&self, x: &u32) -> bool {
        *x % 2u32 == 0u32
    }
}
