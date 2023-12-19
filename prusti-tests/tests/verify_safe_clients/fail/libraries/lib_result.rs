// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
use std::ptr::addr_of;
/* EVALUATION:IGNOREBEFORE */

#[extern_spec]
impl<T, E> Result<T, E> {
    #[pure]
    #[ensures(matches!(old(self), Ok(_)) == result)]
    fn is_ok(&self) -> bool;

    #[pure]
    #[ensures(old(self).is_err() == !result)]
    fn is_err(&self) -> bool;

    #[requires(self.is_ok())]
    #[ensures(if let Ok(ref value) = old(self) {
        moved(value as *const _, addr_of!(result))
    } else { unreachable!() })]
    fn unwrap(self) -> T where E: std::fmt::Debug;

    #[ensures(if let Ok(ref value) = old(self) {
        match result {
            Some(ref result_value) => moved(value as *const _, result_value as *const _),
            None => unreachable!(),
        }
    } else { result.is_none() })]
    fn ok(self) -> Option<T>;

    #[ensures(if let Err(ref err) = old(self) {
        match result {
            Some(ref result_err) => moved(err as *const _, result_err as *const _),
            None => unreachable!(),
        }
    } else { result.is_none() })]
    fn err(self) -> Option<E>;
}

#[extern_spec]
impl<T, E> std::ops::Try for Result<T, E> {
    #[ensures(match (old(self), result) {
        (Ok(v1), std::ops::ControlFlow::Continue(v2)) => v1 ==== v2,
        (Err(e1), std::ops::ControlFlow::Break(Err(e2))) => e1 ==== e2,
        _ => false
    })]
    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output>;
}
