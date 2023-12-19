// ignore-test This is part of a module
use prusti_contracts::*;
use super::*;
/* EVALUATION:IGNOREBEFORE */

#[extern_spec]
impl<B, C> std::ops::ControlFlow<B, C> {
    #[pure]
    #[ensures(result == matches!(self, std::ops::ControlFlow::Continue(_)))]
    fn is_continue(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, std::ops::ControlFlow::Break(_)))]
    fn is_break(&self) -> bool;
}
