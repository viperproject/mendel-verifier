// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::ptr::addr_of;
/* EVALUATION:IGNOREBEFORE */

#[extern_spec]
impl<T> Option<T> {
    #[pure]
    #[ensures(matches!(old(self), Some(_)) == result)]
    fn is_some(&self) -> bool;

    #[pure]
    #[ensures(old(self).is_some() == !result)]
    fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    #[ensures(if let Some(ref value) = old(self) {
        moved(value as *const _, addr_of!(result))
    } else { unreachable!() })]
    fn unwrap(self) -> T;

    #[ensures(if let Some(data_ref) = old(check_mem(snap(&self))) {
        result.is_some()
        && (if let Some(result_data_ref) = check_mem(snap(&result)) {
            data_ref ==== result_data_ref
        } else { unreachable!() })
    } else {
        result.is_none()
    })]
    #[ensures(snap(&self) ==== old(snap(&self)))]
    fn as_mut(&mut self) -> Option<&mut T>;
}

#[extern_spec]
impl<T> std::ops::Try for Option<T> {
    #[ensures(match (old(self), result) {
        (Some(v1), std::ops::ControlFlow::Continue(v2)) => v1 ==== v2,
        (None, std::ops::ControlFlow::Break(_)) => true,
        _ => false
    })]
    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output>;
}
