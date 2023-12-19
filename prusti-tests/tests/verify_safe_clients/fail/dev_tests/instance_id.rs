#![feature(try_trait_v2)]
#![feature(allocator_api)]
use prusti_contracts::*;
use std::cell::UnsafeCell;
use std::sync::MutexGuard;

#[path = "../libraries/mod.rs"]
mod libraries;
use libraries::*;

#[ensures(*dst ==== old(src))]
#[ensures(deref_id(dst as *const _) == old(deref_id(&src as *const _)))]
#[ensures(false)] //~ ERROR
fn move_t<T>(mut src: T, dst: &mut T) {
    *dst = src;
}

#[ensures(result ==== old(fst))]
#[ensures(deref_id(&result as *const _) == old(deref_id(&fst as *const _)))]
#[ensures(deref_id(&result as *const _) != old(deref_id(&snd as *const _)))] //~ ERROR
#[ensures(false)] //~ ERROR
fn return_first<T>(fst: T, snd: T) -> T {
    fst
}

#[ensures(result ==== old(x))]
//#[ensures(deref(result.data_ptr()) ==== old(deref(x.data_ptr())))]
#[ensures(deref_id(&result as *const _) == old(deref_id(&x as *const _)))]
//#[ensures(deref_id(result.data_ptr()) == old(deref_id(x.data_ptr())))]
#[ensures(false)] //~ ERROR
fn move_unsafe_cell<T>(x: MutexGuard<T>) -> MutexGuard<T> {
    x
}

fn main() {
    assert!(false); //~ ERROR
}
