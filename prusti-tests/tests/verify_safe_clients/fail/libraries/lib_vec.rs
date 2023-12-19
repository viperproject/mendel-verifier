// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
/* EVALUATION:IGNOREBEFORE */

#[extern_spec]
impl<T> Vec<T, std::alloc::Global> {
    #[ensures(result.len() == 0)]
    fn new() -> Self;
}

pub trait VecSpec<T> {
    #[trusted]
    #[ghost_fn]
    #[pure]
    fn len_ptr_offset(self_ptr: *const Self) -> *const usize {
        unimplemented!()
    }
}

impl<T> VecSpec<T> for Vec<T, std::alloc::Global> {}

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[pure]
    fn len(&self) -> usize;

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: T);
}

