// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    mir_encoder::operations::{encode_bin_op_check, encode_bin_op_expr, encode_unary_op_expr},
    safe_clients::prelude::*,
};
use prusti_rustc_interface::middle::ty::adjustment::PointerCast;

/// Trait used to encode the snapshot of an `RvalueExpr`.
pub trait MirExprEncoder<'v, 'tcx: 'v>: PlaceEncoder<'v, 'tcx> + WithMir<'v, 'tcx> + Sized {
    fn encode_failing_assertion(
        &self,
        msg: &mir::AssertMessage<'tcx>,
        domain_kind: BuiltinDomainKind<'tcx>,
        span: Span,
    ) -> SpannedEncodingResult<vir::Expr>;
    #[allow(clippy::too_many_arguments)]
    fn encode_pure_call_snapshot(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[MirExpr<'tcx>],
        version: Option<vir::LocalVar>,
        return_ty: ty::Ty<'tcx>,
        span: Span,
        context: GhostOrExec,
    ) -> SpannedEncodingResult<SnapshotExpr>;

    fn encode_pure_call_address(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[MirExpr<'tcx>],
        span: Span,
        context: GhostOrExec,
    ) -> SpannedEncodingResult<Option<vir::Expr>> {
        let _frame = open_trace!(
            self,
            "encode_pure_call_address",
            format!(
                "{called_def_id:?}, {} args, context {context:?}",
                args.len()
            )
        );
        let full_func_proc_name = self.env().name.get_absolute_item_name(called_def_id);
        let strip_ref = |index: usize| -> SpannedEncodingResult<&MirExpr<'tcx>> {
            let stripped_arg = if let Some(base_arg) = args[index].strip_ref() {
                base_arg
            } else {
                error_internal!(span =>
                    "expected a reference for argument {index}; got {:?}",
                    args[index].ty(self.mir(), self.tcx()).ty,
                );
            };
            Ok(stripped_arg)
        };
        // We can encode the address only if comes from a ghost call
        // like old(..), check_mem(..), snap(..)
        Ok(match full_func_proc_name.as_str() {
            "prusti_contracts::old" | "prusti_contracts::check_mem" => {
                assert_eq!(args.len(), 1);
                self.encode_mir_expr_address(&args[0], GhostOrExec::Ghost)
                    .with_default_span(span)?
            }
            "prusti_contracts::snap" => {
                assert_eq!(args.len(), 1);
                self.encode_mir_expr_address(strip_ref(0)?, GhostOrExec::Ghost)
                    .with_default_span(span)?
            }
            _ => {
                // It is only possible to use the address of the result of
                // old(..), snap(..) and check_mem(..) calls
                None
            }
        })
    }

    // TODO: convert the error case from None to (Span, message).
    fn encode_mir_expr_address(
        &self,
        expr: &MirExpr<'tcx>,
        context: GhostOrExec,
    ) -> EncodingResult<Option<vir::Expr>> {
        let frame = open_trace!(
            self,
            "encode_mir_expr_address",
            format!("{expr}, context {context}")
        );
        let ty = expr.ty(self.mir(), self.tcx()).ty;
        let result = match expr {
            MirExpr::Rvalue(rvalue) => self.encode_rvalue_expr_address(rvalue, context)?,
            &MirExpr::Call {
                ref func,
                ref args,
                return_ty,
                span,
            } => {
                let &ty::TyKind::FnDef(called_def_id, call_substs) = func.literal.ty().kind() else {
                    unimplemented!();
                };
                self.encode_pure_call_address(
                    called_def_id,
                    call_substs,
                    args,
                    span.unwrap(),
                    context,
                )?
            }
            &MirExpr::Switch {
                box ref discr,
                ref guarded_exprs,
                box ref default_expr,
                span,
            } => encode_switch(
                self,
                ty,
                discr,
                guarded_exprs.as_slice(),
                default_expr,
                span,
                |e| {
                    self.encode_mir_expr_address(e, context)
                        .map(|opt_e| opt_e.map(SnapshotExpr::new_memory))
                },
                context,
            )?
            .map(|e| e.into_expr()),
            &MirExpr::Assert {
                box ref cond,
                expected,
                box ref then,
                ref msg,
                span,
            } => {
                let Some(encoded_then) = self.encode_mir_expr_address(then, context)? else { return Ok(None); };
                Some(
                    encode_assert(
                        self,
                        BuiltinDomainKind::Address(ty),
                        cond,
                        expected,
                        SnapshotExpr::new_memory(encoded_then),
                        msg,
                        span.unwrap(),
                        context,
                    )?
                    .into_expr(),
                )
            }
        };
        close_trace!(
            self,
            frame,
            result
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or_else(|| "None".to_string())
        );
        Ok(result)
    }

    /// Returns `None` if the expression cannot be encoded.
    /// Mainly: the address of a `RvalueExpr::Projections` can only be encoded in ghost code.
    fn encode_mir_expr_snapshot(
        &self,
        expr: &MirExpr<'tcx>,
        context: GhostOrExec,
    ) -> EncodingResult<SnapshotExpr> {
        let frame = open_trace!(
            self,
            "impl_encode_mir_expr_snapshot",
            format!("{expr}, context {context}")
        );
        let ty = expr.ty(self.mir(), self.tcx()).ty;
        let snapshot_domain = MemSnapshotDomain::encode(self.encoder(), ty)?;
        let result = match expr {
            MirExpr::Rvalue(ref rvalue_expr) => {
                self.encode_rvalue_expr_snapshot(rvalue_expr, context)?
            }
            &MirExpr::Switch {
                ref discr,
                ref guarded_exprs,
                ref default_expr,
                span,
            } => encode_switch(
                self,
                ty,
                discr,
                guarded_exprs,
                default_expr,
                span,
                |e| self.encode_mir_expr_snapshot(e, context).map(Some),
                context,
            )?
            .unwrap(),
            &MirExpr::Assert {
                box ref cond,
                expected,
                ref then,
                ref msg,
                span,
            } => {
                let encoded_then = self.encode_mir_expr_snapshot(then, context)?;
                let domain_kind = if encoded_then.kind().is_memory() {
                    BuiltinDomainKind::MemorySnapshot(ty)
                } else {
                    BuiltinDomainKind::ValueSnapshot(ty)
                };
                encode_assert(
                    self,
                    domain_kind,
                    cond,
                    expected,
                    encoded_then,
                    msg,
                    span.unwrap(),
                    context,
                )?
            }
            &MirExpr::Call {
                ref func,
                ref args,
                span,
                return_ty,
                ..
            } => {
                let &ty::TyKind::FnDef(called_def_id, call_substs) = func.literal.ty().kind() else {
                    unimplemented!();
                };
                trace!(
                    "Encode function call {} ({called_def_id:?}) with substs {call_substs:?}",
                    self.env().name.get_absolute_item_name(called_def_id)
                );

                // The called method might be a trait method.
                // We try to resolve it to the concrete implementation
                // and type substitutions.
                let (called_def_id, call_substs) =
                    self.env()
                        .query
                        .resolve_method_call(self.def_id(), called_def_id, call_substs);

                self.encode_pure_call_snapshot(
                    called_def_id,
                    call_substs,
                    args,
                    PlaceEncoder::encode_version(self)?,
                    return_ty,
                    span.unwrap_or(self.span()),
                    context,
                )?
            }
        };
        close_trace!(self, frame, result.expr());
        Ok(result)
    }

    fn encode_rvalue_expr_address(
        &self,
        rvalue: &RvalueExpr<'tcx>,
        context: GhostOrExec,
    ) -> EncodingResult<Option<vir::Expr>> {
        let frame = open_trace!(
            self,
            "encode_rvalue_expr_address",
            format!("{rvalue}, context {context}")
        );
        let ty = rvalue.ty(self.mir(), self.tcx()).ty;
        let memory_domain = self.encode_snapshot_domain(SnapshotKind::Memory, ty)?;
        let result = match rvalue {
            &RvalueExpr::Place(place) => {
                if let Some(addr_expr) = self.encode_place_address(place)? {
                    Some(addr_expr)
                } else if let Some(last_proj) = place.projection.last() {
                    let last_ty = place
                        .iter_projections()
                        .last()
                        .unwrap()
                        .0
                        .ty(self.mir(), self.tcx())
                        .ty;
                    let (rem_place_ref, _) = place.iter_projections().last().unwrap();
                    let rem_place_ty = rem_place_ref.ty(self.mir(), self.tcx()).ty;
                    let rem_place = mir::Place {
                        local: rem_place_ref.local,
                        projection: self.tcx().intern_place_elems(rem_place_ref.projection),
                    };
                    match *last_proj {
                        // Special-case `*<expr>`
                        mir::ProjectionElem::Deref if last_ty.is_any_ptr() => {
                            let place_snap = self.encode_place_snapshot(rem_place)?;
                            if place_snap.kind().is_memory() {
                                Some(
                                    self.encode_snapshot_domain(
                                        SnapshotKind::Memory,
                                        rem_place_ty,
                                    )?
                                    .target_address_function()?
                                    .apply1(place_snap.expr().clone()),
                                )
                            } else {
                                None
                            }
                        }
                        // Special-case `<expr>.field`
                        mir::ProjectionElem::Field(field, _) => {
                            let rem_rvalue = RvalueExpr::Place(rem_place);
                            if let Some(rem_place_addr) =
                                self.encode_rvalue_expr_address(&rem_rvalue, context)?
                            {
                                Some(
                                    AddressDomain::encode(self.encoder(), last_ty)?
                                        .adt_field_address_function(None, field)?
                                        .apply1(rem_place_addr),
                                )
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            }
            // Special-case `*&<expr>` ==> `<expr>`.
            RvalueExpr::Projections {
                base: box MirExpr::Rvalue(RvalueExpr::Ref { box expr, .. }),
                projections,
            } if projections.first() == Some(&mir::ProjectionElem::Deref)
                && projections.len() == 1 =>
            {
                debug_assert_eq!(expr.ty(self.mir(), self.tcx()).ty, ty);
                if context.is_exec() {
                    // We cannot encode the address of a local variable declared in pure code.
                    return Ok(None);
                } else {
                    // We are encoding the argument of an old(..), snap(..) or check_mem(..) call,
                    // which uses a no-move semantics in which we can always encode the address of
                    // expressions.
                    self.encode_mir_expr_address(expr, context)?
                }
            }
            RvalueExpr::Projections { base, projections } => {
                if context.is_exec() {
                    // We cannot encode the address of a local variable declared in pure code.
                    return Ok(None);
                }
                // We are encoding the argument of an old(..), snap(..) or check_mem(..) call,
                // which uses a no-move semantics in which we can always encode the address of
                // expressions.
                if let Some(projection) = projections.last().copied() {
                    let rem_projections = projections
                        .iter()
                        .take(projections.len() - 1)
                        .copied()
                        .collect();
                    let mut rem_expr = MirExpr::from(RvalueExpr::Projections {
                        // TODO: this can be expensive
                        base: base.clone(),
                        projections: rem_projections,
                    });
                    rem_expr.normalize();
                    let rem_expr_ty = rem_expr.ty(self.mir(), self.tcx());
                    if let Some(base_addr) = self.encode_mir_expr_address(&rem_expr, context)? {
                        self.encode_place_projection_address(base_addr, rem_expr_ty, projection)?
                    } else {
                        // Special-case `*<reference>`.
                        if projection == mir::ProjectionElem::Deref && rem_expr_ty.ty.is_any_ptr() {
                            let rem_snapshot = self.encode_mir_expr_snapshot(&rem_expr, context)?;
                            if rem_snapshot.kind().is_memory() {
                                Some(
                                    self.encode_snapshot_domain(
                                        SnapshotKind::Memory,
                                        rem_expr_ty.ty,
                                    )?
                                    .target_address_function()?
                                    .apply1(rem_snapshot.expr().clone()),
                                )
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                } else {
                    self.encode_mir_expr_address(base, context)?
                }
            }
            RvalueExpr::Ref { .. }
            | RvalueExpr::Constant(_)
            | RvalueExpr::UnaryOp { .. }
            | RvalueExpr::BinaryOp { .. }
            | RvalueExpr::CheckedBinaryOp { .. }
            | RvalueExpr::AddressOf { .. }
            | RvalueExpr::Aggregate { .. }
            | RvalueExpr::Discriminant { .. }
            | RvalueExpr::Cast { .. } => {
                // It is not possible to use the address of other rvalues
                None
            }
        };
        close_trace!(
            self,
            frame,
            result
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or_else(|| "None".to_string())
        );
        Ok(result)
    }

    fn encode_rvalue_expr_snapshot(
        &self,
        rvalue: &RvalueExpr<'tcx>,
        context: GhostOrExec,
    ) -> EncodingResult<SnapshotExpr> {
        let frame = open_trace!(
            self,
            "encode_rvalue_expr_snapshot",
            format!("{rvalue}, context {context}")
        );
        let body = self.mir();
        let tcx = self.tcx();
        let encoder = self.encoder();
        let ty = rvalue.ty(body, tcx).ty;
        let memory_domain = self.encode_snapshot_domain(SnapshotKind::Memory, ty)?;
        let value_domain = self.encode_snapshot_domain(SnapshotKind::Value, ty)?;
        let result = match rvalue {
            &RvalueExpr::Constant(constant) => self.encode_constant_snapshot(constant)?,
            &RvalueExpr::Place(place) => self.encode_place_snapshot(place)?,
            // Special-case `*&<expr>`
            RvalueExpr::Projections {
                base: box MirExpr::Rvalue(RvalueExpr::Ref { box expr, .. }),
                projections,
            } if projections.first() == Some(&mir::ProjectionElem::Deref)
                && projections.len() == 1 =>
            {
                self.encode_mir_expr_snapshot(expr, context)?
            }
            RvalueExpr::Projections {
                box base,
                projections,
            } => {
                let mut place_ty = base.ty(body, tcx);
                let mut place_snapshot = self.encode_mir_expr_snapshot(base, context)?;
                for &projection in projections {
                    place_snapshot = self.encode_place_projection_snapshot(
                        place_snapshot,
                        place_ty,
                        projection,
                    )?;
                    place_ty = place_ty.projection_ty(self.tcx(), projection);
                }
                place_snapshot
            }
            &RvalueExpr::UnaryOp {
                box ref expr,
                op,
                span,
            } => {
                debug_assert_eq!(ty, expr.ty(body, tcx).ty);
                debug_assert!(ty.is_primitive_ty());
                let encoded_expr = self
                    .encode_mir_expr_snapshot(expr, context)
                    .with_opt_default_span(span)?;
                let encoded_result = encode_unary_op_expr(
                    op,
                    self.encode_snapshot_primitive_value(encoded_expr, ty)
                        .with_opt_span(span)?,
                );
                // Both memory and value would work here
                SnapshotExpr::new_memory(
                    memory_domain.constructor_function()?.apply1(encoded_result),
                )
            }
            &RvalueExpr::BinaryOp {
                box ref left,
                box ref right,
                op,
                span,
            } => {
                let op_ty = left.ty(body, tcx).ty;
                debug_assert_eq!(op_ty, right.ty(body, tcx).ty);
                debug_assert!(op_ty.is_primitive_ty() || op_ty.is_unsafe_ptr());
                let encoded_left = self
                    .encode_mir_expr_snapshot(left, context)
                    .with_opt_default_span(span)?;
                let encoded_right = self
                    .encode_mir_expr_snapshot(right, context)
                    .with_opt_default_span(span)?;
                let encoded_result = match op_ty.kind() {
                    _ if op_ty.is_unsafe_ptr() => {
                        let left_domain =
                            self.encode_snapshot_domain(encoded_left.kind(), op_ty)?;
                        let right_domain =
                            self.encode_snapshot_domain(encoded_right.kind(), op_ty)?;
                        encode_bin_op_expr(
                            op,
                            left_domain
                                .target_address_function()
                                .with_opt_span(span)?
                                .apply1(encoded_left),
                            right_domain
                                .target_address_function()
                                .with_opt_span(span)?
                                .apply1(encoded_right),
                            op_ty,
                        )
                        .with_opt_span(span)?
                    }
                    _ if op_ty.is_primitive_ty() => encode_bin_op_expr(
                        op,
                        self.encode_snapshot_primitive_value(encoded_left, op_ty)
                            .with_opt_span(span)?,
                        self.encode_snapshot_primitive_value(encoded_right, op_ty)
                            .with_opt_span(span)?,
                        op_ty,
                    )
                    .with_opt_span(span)?,
                    _ => {
                        error_unsupported!(opt span =>
                            "unsupported operation '{:?}' between expressions of type '{:?}'",
                            op,
                            op_ty
                        );
                    }
                };
                // Both memory and value would work here
                SnapshotExpr::new_memory(
                    memory_domain.constructor_function()?.apply1(encoded_result),
                )
            }
            &RvalueExpr::CheckedBinaryOp {
                box ref left,
                box ref right,
                op,
                span,
            } => {
                let op_ty = left.ty(body, tcx).ty;
                debug_assert_eq!(op_ty, right.ty(body, tcx).ty);
                debug_assert!(op_ty.is_primitive_ty());
                let encoded_left = self
                    .encode_mir_expr_snapshot(left, context)
                    .with_opt_default_span(span)?;
                let encoded_right = self
                    .encode_mir_expr_snapshot(right, context)
                    .with_opt_default_span(span)?;
                let encoded_result = encode_bin_op_expr(
                    op,
                    self.encode_snapshot_primitive_value(encoded_left.clone(), op_ty)
                        .with_opt_span(span)?,
                    self.encode_snapshot_primitive_value(encoded_right.clone(), op_ty)
                        .with_opt_span(span)?,
                    op_ty,
                )
                .with_opt_span(span)?;
                let check_ty = tcx.mk_ty(ty::TyKind::Bool);
                let encoded_check = encode_bin_op_check(
                    op,
                    self.encode_snapshot_primitive_value(encoded_left, op_ty)
                        .with_opt_span(span)?,
                    self.encode_snapshot_primitive_value(encoded_right, op_ty)
                        .with_opt_span(span)?,
                    op_ty,
                )
                .with_opt_span(span)?;
                // Both memory and value would work here
                SnapshotExpr::new_memory(
                    memory_domain.constructor_function()?.apply2(
                        self.encode_snapshot_domain(SnapshotKind::Memory, op_ty)?
                            .constructor_function()?
                            .apply1(encoded_result),
                        self.encode_snapshot_domain(SnapshotKind::Memory, check_ty)?
                            .constructor_function()?
                            .apply1(encoded_check),
                    ),
                )
            }
            &RvalueExpr::Ref {
                box ref expr,
                borrow_kind,
                region,
                span,
            } => {
                // Special-case `&*<expr>` in the `RvalueExpr::Place` case
                if let MirExpr::Rvalue(RvalueExpr::Place(place)) = expr {
                    if place.projection.last() == Some(&mir::ProjectionElem::Deref) {
                        let remaining_projections = &place.projection[..place.projection.len() - 1];
                        let remaining_rvalue = RvalueExpr::Place(mir::Place {
                            local: place.local,
                            projection: self.tcx().intern_place_elems(remaining_projections),
                        });
                        let remaining_ty = remaining_rvalue.ty(body, tcx).ty;
                        if ty == remaining_ty {
                            let rvalue_snapshot = self
                                .encode_rvalue_expr_snapshot(&remaining_rvalue, context)
                                .with_opt_default_span(span)?;
                            close_trace!(self, frame, rvalue_snapshot.expr());
                            return Ok(rvalue_snapshot);
                        }
                    }
                }
                // Special-case `&*<expr>` in the `RvalueExpr::Projections` case
                if let MirExpr::Rvalue(RvalueExpr::Projections { base, projections }) = expr {
                    if projections.last() == Some(&mir::ProjectionElem::Deref) {
                        let remaining_projections = &projections[..projections.len() - 1];
                        let remaining_rvalue = RvalueExpr::Projections {
                            base: base.clone(),
                            projections: remaining_projections.to_vec(),
                        };
                        let remaining_ty = remaining_rvalue.ty(body, tcx).ty;
                        if ty == remaining_ty {
                            let rvalue_snapshot = self
                                .encode_rvalue_expr_snapshot(&remaining_rvalue, context)
                                .with_opt_default_span(span)?;
                            close_trace!(self, frame, rvalue_snapshot.expr());
                            return Ok(rvalue_snapshot);
                        }
                    }
                }

                let encoded_expr = self
                    .encode_mir_expr_snapshot(expr, context)
                    .with_opt_default_span(span)?;
                let encoded_place_address = self
                    .encode_mir_expr_address(expr, context)
                    .with_opt_default_span(span)?;
                if let Some(actual_encoded_address) = encoded_place_address {
                    // The memory address has an encoding (e.g. impure context)
                    trace!("The memory address has an encoding, for {expr}");
                    if encoded_expr.kind().is_memory() {
                        SnapshotExpr::new_memory(
                            memory_domain
                                .constructor_function()?
                                .apply2(actual_encoded_address, encoded_expr),
                        )
                    } else {
                        SnapshotExpr::new_value(
                            value_domain.constructor_function()?.apply1(encoded_expr),
                        )
                    }
                } else {
                    // The memory address has no encoding (e.g. pure context)
                    let expr_ty = expr.ty(body, tcx).ty;
                    trace!("The memory address has no encoding, for {expr}: {expr_ty:?}");
                    let encoded_expr_value = self
                        .convert_to_value_snapshot(encoded_expr, expr_ty)
                        .with_opt_span(span)?;
                    SnapshotExpr::new_value(
                        value_domain
                            .constructor_function()?
                            .apply1(encoded_expr_value),
                    )
                }
            }
            &RvalueExpr::Aggregate {
                ref kind,
                ref fields,
                span,
            } => match kind {
                mir::AggregateKind::Tuple => {
                    let mut encoded_fields = vec![];
                    let field_types = fields
                        .iter()
                        .map(|field| field.ty(body, tcx).ty)
                        .collect::<Vec<_>>();
                    for field in fields.iter() {
                        let encoded_field = self
                            .encode_mir_expr_snapshot(field, context)
                            .with_opt_default_span(span)?;
                        encoded_fields.push(encoded_field);
                    }
                    let (converted_fields, mov) =
                        self.unify_typed_expressions(encoded_fields, &field_types)?;
                    SnapshotExpr::new(
                        self.encode_snapshot_domain(mov, ty)?
                            .constructor_function()?
                            .apply(converted_fields),
                        mov,
                    )
                }

                &mir::AggregateKind::Adt(adt_did, variant_index, _, _, _) => {
                    let adt_def = tcx.adt_def(adt_did);
                    let mut encoded_fields = vec![];
                    let field_types = fields
                        .iter()
                        .map(|field| field.ty(body, tcx).ty)
                        .collect::<Vec<_>>();
                    for (field_index, field) in fields.iter().enumerate() {
                        let encoded_op = self
                            .encode_mir_expr_snapshot(field, context)
                            .with_opt_default_span(span)?;
                        encoded_fields.push(encoded_op);
                    }
                    let (converted_fields, mov) =
                        self.unify_typed_expressions(encoded_fields, &field_types)?;
                    SnapshotExpr::new(
                        self.encode_snapshot_domain(mov, ty)?
                            .adt_constructor_function(Some(variant_index))
                            .with_opt_span(span)?
                            .apply(converted_fields),
                        mov,
                    )
                }

                _ => {
                    error_unsupported!(opt span =>
                        "unsupported assignment with RHS aggregate '{:?}'",
                        kind,
                    );
                }
            },
            &RvalueExpr::Discriminant { box ref expr, span } => {
                let expr_ty = expr.ty(body, tcx);
                debug_assert!(expr_ty.variant_index.is_none());
                let encoded_expr = self
                    .encode_mir_expr_snapshot(expr, context)
                    .with_opt_default_span(span)?;
                let discr_value = self
                    .encode_snapshot_domain(encoded_expr.kind(), expr_ty.ty)?
                    .discriminant_function()
                    .with_opt_span(span)?
                    .apply1(encoded_expr);
                SnapshotExpr::new_memory(memory_domain.constructor_function()?.apply1(discr_value))
            }
            &RvalueExpr::AddressOf {
                box ref expr,
                mutability,
                span,
            } => {
                let expr_ty = expr.ty(body, tcx);
                debug_assert!(expr_ty.variant_index.is_none());
                let ty::TyKind::RawPtr(..) = ty.kind() else {
                    error_unsupported!(opt span =>
                        "constructing a type {ty:?} from an address is not supported",
                    );
                };
                let opt_expr_address = self
                    .encode_mir_expr_address(expr, context)
                    .with_opt_default_span(span)?;
                let Some(expr_address) = opt_expr_address else {
                    error_incorrect!(opt span =>
                        "cannot compute the address of a ghost memory location (expr: {expr})",
                    );
                };
                SnapshotExpr::new_memory(memory_domain.constructor_function()?.apply1(expr_address))
            }
            &RvalueExpr::Cast {
                box ref expr,
                kind,
                ty,
                span,
            } => {
                let encoded_expr = self
                    .encode_mir_expr_snapshot(expr, context)
                    .with_opt_default_span(span)?;
                match kind {
                    mir::CastKind::PtrToPtr
                    | mir::CastKind::Pointer(PointerCast::MutToConstPointer) => {
                        // Keep the same encoding of the address, but change the domain type.
                        let expr_ty = expr.ty(body, tcx).ty;
                        let encoded_address = self
                            .encode_snapshot_domain(encoded_expr.kind(), expr_ty)?
                            .target_address_function()?
                            .apply1(encoded_expr);
                        SnapshotExpr::new_memory(
                            memory_domain
                                .constructor_function()?
                                .apply1(encoded_address),
                        )
                    }
                    _ => {
                        let expr_ty = expr.ty(body, tcx);
                        error_unsupported!(opt span =>
                            "unsupported cast {kind:?} from {expr_ty:?} to {ty:?}",
                        );
                    }
                }
            }
        };
        close_trace!(self, frame, result.expr());
        Ok(result)
    }
}

#[allow(clippy::too_many_arguments)]
fn encode_switch<'v, 'tcx: 'v>(
    this: &impl MirExprEncoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
    discr: &MirExpr<'tcx>,
    guarded_exprs: &[(u128, MirExpr<'tcx>)],
    default_expr: &MirExpr<'tcx>,
    span: Option<Span>,
    branch_encoder: impl Fn(&MirExpr<'tcx>) -> EncodingResult<Option<SnapshotExpr>>,
    context: GhostOrExec,
) -> EncodingResult<Option<SnapshotExpr>> {
    let discr_ty = discr.ty(this.mir(), this.tcx()).ty;
    if !discr_ty.is_primitive_ty() {
        error_internal!(opt span =>
            "unexpected switch on a non-primitive type; got {discr_ty:?}"
        );
    };

    let discr_expr = this.encode_mir_expr_snapshot(discr, context)?;
    let discr_value = this.encode_snapshot_primitive_value(discr_expr, discr_ty)?;

    let Some(mut expr) = branch_encoder(default_expr)? else { return Ok(None); };
    for &(guard_value, ref guarded_expr) in guarded_exprs.iter().rev() {
        let encoded_guard: vir::Expr = match discr_ty.kind() {
            ty::TyKind::Bool => {
                // 0 is false, 1 is true
                (guard_value > 0).into()
            }
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Char => {
                this.encoder().encode_int_cast(guard_value, discr_ty)
            }
            _ => {
                error_internal!(opt span => "unexpected switch on type {discr_ty:?}");
            }
        };
        let Some(encoded_expr) = branch_encoder(guarded_expr)? else { return Ok(None); };
        let (mut encoded_branches, kind) =
            this.unify_typed_expressions(vec![encoded_expr, expr], &[ty, ty])?;
        let encoded_else = encoded_branches.pop().unwrap();
        let encoded_then = encoded_branches.pop().unwrap();
        debug_assert!(encoded_branches.is_empty());
        expr = SnapshotExpr::new(
            vir::Expr::ite(
                vir_expr!([discr_value] == [encoded_guard]),
                encoded_then,
                encoded_else,
            ),
            kind,
        );
    }
    Ok(Some(expr))
}

#[allow(clippy::too_many_arguments)]
fn encode_assert<'v, 'tcx: 'v>(
    this: &impl MirExprEncoder<'v, 'tcx>,
    domain_kind: BuiltinDomainKind<'tcx>,
    cond: &MirExpr<'tcx>,
    expected: bool,
    encoded_then: SnapshotExpr,
    msg: &mir::AssertMessage<'tcx>,
    span: Span,
    context: GhostOrExec,
) -> EncodingResult<SnapshotExpr> {
    let failing_branch = this.encode_failing_assertion(msg, domain_kind, span)?;
    let cond_expr = this.encode_mir_expr_snapshot(cond, context)?;
    let cond_ty = cond.ty(this.mir(), this.tcx()).ty;
    let cond_expr = this.encode_mir_expr_snapshot(cond, context)?;
    let cond_value = this.encode_snapshot_primitive_value(cond_expr, cond_ty)?;
    let then_expr_kind = encoded_then.kind();
    Ok(SnapshotExpr::new(
        vir::Expr::ite(
            vir_expr!([cond_value] == [vir::Expr::from(expected)]),
            encoded_then.into_expr(),
            failing_branch,
        ),
        then_expr_kind,
    ))
}
