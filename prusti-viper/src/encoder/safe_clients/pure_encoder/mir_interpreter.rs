// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::pure::interpreter::{BackwardMirInterpreter, run_backward_interpretation, run_backward_interpretation_point_to_point};
use super::MirInterpreterState;

/// Used to convert a MIR body to a `MirExpr`.
pub struct MirInterpreter<'p, 'tcx: 'p> {
    /// The MIR to convert to an expression.
    mir: &'p mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
}

/// This encoding works backward, so there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'tcx: 'p> MirInterpreter<'p, 'tcx> {
    pub fn new(
        mir: &'p mir::Body<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Self {
        MirInterpreter {
            mir,
            tcx,
        }
    }

    pub fn encode_body(&self) -> SpannedEncodingResult<MirExpr<'tcx>> {
        let Some(state) = run_backward_interpretation(self.mir, self)? else {
            error_incorrect!(self.mir.span => "loops are not allowed in pure code");
        };
        let Some(mir_expr) = state.into_expr() else {
            error_incorrect!(self.mir.span => "pure code must have a non-panicking execution path");
        };
        Ok(mir_expr)
    }

    pub fn encode_point_to_point(
        &self, final_expr: MirExpr<'tcx>, initial_bb: mir::BasicBlock, final_loc: mir::Location,
    ) -> SpannedEncodingResult<MirExpr<'tcx>> {
        let result = run_backward_interpretation_point_to_point(
            self.mir,
            self,
            initial_bb,
            final_loc.block,
            final_loc.statement_index,
            MirInterpreterState::new_defined(final_expr),
            MirInterpreterState::new_undefined(),
        )?;
        let Some(state) = result else {
            error_incorrect!(self.mir.span => "loops are not allowed in pure code");
        };
        let Some(mir_expr) = state.into_expr() else {
            error_incorrect!(self.mir.span => "pure code must have a non-panicking execution path");
        };
        Ok(mir_expr)
    }
}

impl<'p, 'tcx: 'p> BackwardMirInterpreter<'tcx>
    for MirInterpreter<'p, 'tcx>
{
    type State = MirInterpreterState<'tcx>;
    type Error = SpannedEncodingError;

    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error> {
        trace!("apply_statement {:?}, state: {:?}", stmt, state);
        let span = stmt.source_info.span;

        match stmt.kind {
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..)
            | mir::StatementKind::AscribeUserType(..)
             => {
                // Nothing to do
            }

            mir::StatementKind::Assign(box (lhs, ref rhs)) => {
                if !lhs.projection.is_empty() {
                    error_unsupported!(span =>
                        "unsupported assignment to a place that is not a local variable"
                    );
                }
                let rhs_expr = RvalueExpr::from_rvalue(rhs, Some(span)).with_span(span)?;
                state.replace_local(lhs.local, rhs_expr.into()).with_span(span)?;
            }
            _ => {
                error_unsupported!(span => "unsupported statement '{:?}'", stmt);
            }
        }
        state.normalize();
        Ok(())
    }

    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        term: &mir::Terminator<'tcx>,
        mut states: rustc_hash::FxHashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error> {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        let span = term.source_info.span;

        // Remove undefined targets
        states.retain(|_, state| state.expr().is_some());
        let states = states;
        let lookup_target = |bb: mir::BasicBlock| -> Option<&MirExpr<'tcx>> {
            states.get(&bb).and_then(|target_state| target_state.expr())
        };

        let mut state_expr = match &term.kind {
            mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Abort
            | mir::TerminatorKind::Resume { .. } => {
                assert!(states.is_empty());
                None
            }

            &mir::TerminatorKind::Drop { place, target, .. } => {
                assert!(states.len() <= 2);
                lookup_target(target).cloned()
            }

            &mir::TerminatorKind::DropAndReplace { place, ref value, target, .. } => {
                assert!(states.len() <= 2);
                let rhs_expr = RvalueExpr::from_operand(value).with_span(span)?;
                let mut state = MirInterpreterState::new(lookup_target(target).cloned());
                state.replace_local(place.local, rhs_expr.into()).with_span(span)?;
                state.into_expr()
            }

            &mir::TerminatorKind::Goto { target } => {
                assert!(states.len() <= 1);
                lookup_target(target).cloned()
            }

            &mir::TerminatorKind::FalseEdge {
                real_target, ..
            } => {
                // Can be 1 for match guards (both targets point at the same block after some
                // optimizations)
                assert!(states.len() <= 2);
                lookup_target(real_target).cloned()
            }

            &mir::TerminatorKind::FalseUnwind {
                real_target, ..
            } => {
                assert!(states.len() <= 1);
                lookup_target(real_target).cloned()
            }

            mir::TerminatorKind::Return => {
                assert!(states.is_empty());
                Some(RvalueExpr::from_place(mir::RETURN_PLACE.into()).into())
            }

            mir::TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } => {
                let mut guarded_exprs = Vec::with_capacity(targets.all_targets().len());
                for (value, target) in targets.iter() {
                    if let Some(target_expr) = lookup_target(target) {
                        guarded_exprs.push((value, target_expr.clone()));
                    }
                }
                let default_expr = match lookup_target(targets.otherwise()) {
                    Some(expr) => expr.clone(),
                    None => {
                        if let Some((_, expr)) = guarded_exprs.pop() {
                            expr
                        } else {
                            error_internal!(span =>
                                "no default expression found for switch terminator '{:?}'",
                                term,
                            );
                        }
                    }
                };

                // TODO: Reorder the targets such that Silicon explores branches in the order that we want

                Some(MirExpr::Switch {
                    discr: box RvalueExpr::from_operand(discr).with_span(span)?.into(),
                    guarded_exprs,
                    default_expr: box default_expr,
                    span: Some(span),
                })
            }

            &mir::TerminatorKind::Call {
                ref args,
                destination,
                target,
                ref func,
                ..
            } => {
                let &mir::Operand::Constant(box const_func) = func else {
                    error_unsupported!(span =>
                        "unsupported call to a non-constant function {:?}", func,
                    );
                };
                if !destination.projection.is_empty() {
                    error_unsupported!(span =>
                        "unsupported assignment to a place that is not a local variable"
                    );
                }
                if let Some(actual_target) = target {
                    let mut state = MirInterpreterState::new(lookup_target(actual_target).cloned());
                    let mut arg_exprs = Vec::with_capacity(args.len());
                    for arg in args {
                        arg_exprs.push(RvalueExpr::from_operand(arg).with_span(span)?.into());
                    }
                    let rhs_expr = MirExpr::Call {
                        func: const_func,
                        args: arg_exprs,
                        span: Some(span),
                        return_ty: destination.ty(self.mir, self.tcx).ty,
                    };
                    state.replace_local(destination.local, rhs_expr).with_span(span)?;
                    state.into_expr()
                } else {
                    // Diverging call
                    None
                }
            }

            &mir::TerminatorKind::Assert {
                ref cond,
                expected,
                target,
                ref msg,
                ..
            } => {
                assert_eq!(states.len(), 1);
                if let Some(expr) = lookup_target(target) {
                    Some(MirExpr::Assert {
                        cond: box RvalueExpr::from_operand(cond).with_span(span)?.into(),
                        expected,
                        msg: msg.clone(),
                        then: box expr.clone(),
                        span: Some(span),
                    })
                } else {
                    None
                }
            }

            mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::InlineAsm { .. } => {
                error_internal!(span => "unsupported terminator statement: {:?}", term.kind);
            }
        };
        let mut state = MirInterpreterState::new(state_expr);
        state.normalize();
        Ok(state)
    }
}
