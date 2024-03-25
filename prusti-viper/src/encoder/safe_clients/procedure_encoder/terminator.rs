// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    mir_successor::MirSuccessor,
    safe_clients::{prelude::*, procedure_encoder::*},
};

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    /// Note: it's better to call `encode_statement_at` instead of this method.
    pub(super) fn encode_terminator(
        &mut self,
        term: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> SpannedEncodingResult<(Vec<vir::Stmt>, MirSuccessor)> {
        trace!(
            "Encode terminator '{:?}', location: {:?}, span: {:?}",
            term.kind,
            location,
            term.source_info.span
        );
        let mut stmts: Vec<vir::Stmt> = vec![];
        let span = self.get_span_of_location(location);

        let result = match term.kind {
            mir::TerminatorKind::Return => {
                // Check that the method didn't "forget" about some assert-on-expiry pledges.
                stmts.extend(self.encode_expiring_active_borrows_at(location)?);

                (stmts, MirSuccessor::Return)
            }

            mir::TerminatorKind::Goto { target } => (stmts, MirSuccessor::Goto(target)),

            mir::TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } => {
                let switch_ty = self.get_operand_ty(discr);
                trace!(
                    "SwitchInt ty '{:?}', discr '{:?}', targets '{:?}'",
                    switch_ty,
                    discr,
                    targets
                );

                {
                    // Check whether we should not omit the spec block.
                    let all_targets = targets.all_targets();
                    if all_targets.len() == 2 {
                        if let Some(spec) = all_targets
                            .iter()
                            .position(|target| self.procedure.is_spec_block(*target))
                        {
                            let real_target = all_targets[(spec + 1) % 2];
                            let spec_target = all_targets[spec];
                            if let Some(statements) = self.specification_block_encoding.remove(&spec_target) && !statements.is_empty()
                            {
                                stmts.push(vir::Stmt::comment(format!(
                                    "Encoding of Prusti specification block {spec_target:?}"
                                )));
                                match self.tcx().sess.source_map().span_to_snippet(span) {
                                    Ok(source) => {
                                        stmts.push(vir::Stmt::comment(format!("Source: {source}")));
                                    }
                                    Err(err) => {
                                        stmts.push(vir::Stmt::comment(format!("Source: {err:?}")));
                                    }
                                }
                                stmts.extend(statements);
                                return Ok((stmts, MirSuccessor::Goto(
                                    real_target
                                )));
                            }
                        }
                    }
                }

                let mut cfg_targets: Vec<(vir::Expr, mir::BasicBlock)> = vec![];

                // Store the discriminant value in a local variable.
                let discr_var = self
                    .cfg_method
                    .add_fresh_local_var(types::encode_primitive_type(switch_ty).with_span(span)?);
                let switch_domain =
                    MemSnapshotDomain::encode(self.encoder, switch_ty).with_span(span)?;
                let encoded_discr = switch_domain
                    .primitive_field_function()
                    .with_span(span)?
                    .apply1(
                        self.encode_operand_snapshot(discr, Version::Old)
                            .with_span(span)?,
                    );
                stmts.push(vir::Stmt::Assign(vir::Assign {
                    target: discr_var.clone().into(),
                    source: encoded_discr,
                    kind: vir::AssignKind::Copy,
                }));

                let guard_is_bool = matches!(switch_ty.kind(), ty::TyKind::Bool);

                for (value, target) in targets.iter() {
                    // Convert int to bool, if required
                    let viper_guard = match switch_ty.kind() {
                        ty::TyKind::Bool => {
                            if value == 0 {
                                // If discr is 0 (false)
                                vir::Expr::not(discr_var.clone().into())
                            } else {
                                // If discr is not 0 (true)
                                discr_var.clone().into()
                            }
                        }

                        ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Char => {
                            vir::Expr::eq_cmp(
                                discr_var.clone().into(),
                                self.encoder.encode_int_cast(value, switch_ty),
                            )
                        }

                        ref x => unreachable!("{:?}", x),
                    };
                    cfg_targets.push((viper_guard, target))
                }
                let mut default_target = targets.otherwise();
                let mut kill_default_target = false;

                // Is the target an unreachable block?
                if let mir::TerminatorKind::Unreachable = self.mir[default_target].terminator().kind
                {
                    stmts.push(vir::Stmt::comment(format!(
                        "Ignore default target {default_target:?}, as the compiler marked it as unreachable."
                    )));
                    kill_default_target = true;
                };

                // Is the target a specification block?
                if self.procedure.is_spec_block(default_target) {
                    stmts.push(vir::Stmt::comment(format!(
                        "Ignore default target {default_target:?}, as it is only used by Prusti to type-check \
                        a loop invariant."
                    )));
                    kill_default_target = true;
                };

                if kill_default_target {
                    // Use the last conditional target as default. We could also assume or assert
                    // that the switch is exhaustive and never hits the default.
                    let last_target = cfg_targets.pop().unwrap();
                    (stmts, MirSuccessor::GotoSwitch(cfg_targets, last_target.1))
                } else {
                    // Reorder the targets such that Silicon explores branches in the order that we want
                    if guard_is_bool && cfg_targets.len() == 1 {
                        let (target_guard, target) = cfg_targets.pop().unwrap();
                        let target_span = self.get_span_of_basic_block(target);
                        let default_target_span = self.get_span_of_basic_block(default_target);
                        if target_span > default_target_span {
                            let guard_pos = target_guard.pos();
                            cfg_targets =
                                vec![(target_guard.negate().set_pos(guard_pos), default_target)];
                            default_target = target;
                        } else {
                            // Undo the pop
                            cfg_targets.push((target_guard, target));
                        }
                    }
                    (stmts, MirSuccessor::GotoSwitch(cfg_targets, default_target))
                }
            }

            mir::TerminatorKind::Unreachable => {
                // Asserting `false` here does not work. See issue #158
                (stmts, MirSuccessor::Kill)
            }

            mir::TerminatorKind::Abort => {
                let pos = self.register_error(term.source_info.span, ErrorCtxt::AbortTerminator);
                stmts.push(vir::Stmt::Assert(vir::Assert {
                    expr: false.into(),
                    position: pos,
                }));
                (stmts, MirSuccessor::Kill)
            }

            mir::TerminatorKind::Drop { place, target, .. } => {
                // Make sure that `stmts` is not empty, otherwise the terminator will be ignored
                stmts.push(vir::Stmt::comment(format!("Possible drop of {place:?}")));
                (stmts, MirSuccessor::Goto(target))
            }

            mir::TerminatorKind::FalseEdge { real_target, .. } => {
                (stmts, MirSuccessor::Goto(real_target))
            }

            mir::TerminatorKind::FalseUnwind { real_target, .. } => {
                (stmts, MirSuccessor::Goto(real_target))
            }

            mir::TerminatorKind::DropAndReplace {
                target,
                place,
                ref value,
                ..
            } => {
                // Make sure that `stmts` is not empty, otherwise the terminator will be ignored
                stmts.push(vir::Stmt::comment(format!("Possible drop of {place:?}")));
                let equivalent_stmt = mir::Statement {
                    source_info: term.source_info,
                    kind: mir::StatementKind::Assign(Box::new((
                        place,
                        mir::Rvalue::Use(value.clone()),
                    ))),
                };
                stmts.extend(self.encode_statement(&equivalent_stmt, location)?);
                (stmts, MirSuccessor::Goto(target))
            }

            mir::TerminatorKind::Call {
                ref args,
                destination,
                target,
                func: mir::Operand::Constant(ref func),
                ..
            } => {
                let &ty::TyKind::FnDef(called_def_id, call_substs) = func.literal.ty().kind() else {
                    unimplemented!();
                };
                trace!(
                    "Encode function call {} ({called_def_id:?}) with substs {call_substs:?}",
                    self.encoder
                        .env()
                        .name
                        .get_absolute_item_name(called_def_id)
                );

                // The called method might be a trait method.
                // We try to resolve it to the concrete implementation
                // and type substitutions.
                let (called_def_id, call_substs) = self.encoder.env().query.resolve_method_call(
                    self.def_id,
                    called_def_id,
                    call_substs,
                );

                let is_pure_call = self.is_pure(Some(self.def_id()), called_def_id, call_substs);
                // When encoding a direct recursive call, we need to encode it as a method.
                let is_recursive_call = self.def_id == called_def_id;
                if !is_recursive_call && is_pure_call {
                    assert!(target.is_some());
                    stmts.extend(self.encode_pure_function_call(
                        term.source_info.span,
                        args,
                        destination,
                        called_def_id,
                        call_substs,
                        location,
                    )?);
                } else {
                    stmts.extend(self.encode_impure_function_call(
                        term.source_info.span,
                        args,
                        Some(destination),
                        called_def_id,
                        call_substs,
                        location,
                    )?);
                }

                if let Some(target) = target {
                    (stmts, MirSuccessor::Goto(target))
                } else {
                    // Encode unreachability
                    //stmts.push(
                    //    vir::Stmt::Inhale(false.into())
                    //);
                    (stmts, MirSuccessor::Kill)
                }
            }

            mir::TerminatorKind::Call { .. } => {
                return Err(SpannedEncodingError::unsupported(
                    "non-literal function calls are not supported",
                    term.source_info.span,
                ))
            }

            mir::TerminatorKind::Assert {
                ref cond,
                expected,
                target,
                ref msg,
                ..
            } => {
                trace!("Assert cond '{:?}', expected '{:?}'", cond, expected);

                let cond_ty = self.tcx().mk_ty(ty::TyKind::Bool);
                let cond_snap = self
                    .encode_operand_snapshot(cond, Version::Old)
                    .with_span(span)?;
                let encoded_cond = self
                    .encode_snapshot_primitive_value(SnapshotExpr::new_memory(cond_snap), cond_ty)
                    .with_span(span)?;
                let viper_guard = if expected {
                    encoded_cond
                } else {
                    vir::Expr::not(encoded_cond)
                };

                // Check or assume the assertion
                let (assert_msg, error_ctxt) = if let mir::AssertKind::BoundsCheck { .. } = msg {
                    let mut s = String::new();
                    msg.fmt_assert_args(&mut s).unwrap();
                    (s, ErrorCtxt::BoundsCheckAssert)
                } else {
                    let assert_msg = msg.description().to_string();
                    (assert_msg.clone(), ErrorCtxt::AssertTerminator(assert_msg))
                };

                stmts.push(vir::Stmt::comment(format!("Rust assertion: {assert_msg}")));
                if config::check_panics() {
                    stmts.push(vir::Stmt::Assert(vir::Assert {
                        expr: viper_guard,
                        position: self.register_error(term.source_info.span, error_ctxt),
                    }));
                } else {
                    stmts.push(vir::Stmt::comment("This assertion will not be checked"));
                    stmts.push(vir::Stmt::Inhale(vir::Inhale { expr: viper_guard }));
                };

                (stmts, MirSuccessor::Goto(target))
            }

            mir::TerminatorKind::Resume
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::InlineAsm { .. } => {
                return Err(SpannedEncodingError::unsupported(
                    format!("unsupported terminator kind: {:?}", term.kind),
                    term.source_info.span,
                ))
            }
        };
        Ok(result)
    }
}
