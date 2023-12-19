// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir::pure::PureFunctionEncoderInterface;
use crate::encoder::safe_clients::prelude::*;

/// Trait used to encode the snapshot of a call (pure stable/unstable, or impure).
pub trait CallEncoder<'v, 'tcx: 'v>: MirExprEncoder<'v, 'tcx> + SubstsEncoder<'v, 'tcx> + DefIdEncoder<'v, 'tcx> + WithOldMirExprEncoder<'v, 'tcx> + Sized {
    fn is_prusti_pure(
        &self, called_def_id: DefId, call_substs: ty::SubstsRef<'tcx>, arg_tys: &[ty::Ty<'tcx>],
    ) -> bool {
        let full_func_proc_name = self.env().name.get_absolute_item_name(called_def_id);
        match full_func_proc_name.as_str() {
            "std::cmp::PartialEq::eq" | "core::cmp::PartialEq::eq"
            | "std::cmp::PartialEq::ne" | "core::cmp::PartialEq::ne" => {
                // TODO(fpoli): This is wrong, because `has_structural_eq_impl` doesn't actually
                // check if the implementation is structural.
                self.encoder().has_structural_eq_impl(arg_tys[0])
            }
            _ if full_func_proc_name.ends_with(" as std::cmp::PartialEq>::eq") => {
                self.encoder().has_structural_eq_impl(arg_tys[0])
            }
            _ if full_func_proc_name.ends_with(" as core::cmp::PartialEq>::eq") => {
                self.encoder().has_structural_eq_impl(arg_tys[0])
            }
            _ if full_func_proc_name.ends_with(" as std::cmp::PartialEq>::ne") => {
                self.encoder().has_structural_eq_impl(arg_tys[0])
            }
            _ if full_func_proc_name.ends_with(" as core::cmp::PartialEq>::ne") => {
                self.encoder().has_structural_eq_impl(arg_tys[0])
            }

            "prusti_contracts::old"
            | "prusti_contracts::forall"
            | "prusti_contracts::exists"
            | "prusti_contracts::snap"
            | "prusti_contracts::check_mem"
            | "prusti_contracts::snapshot_equality"
            | "prusti_contracts::memory_snapshot_equality"
            | "prusti_contracts::deref_id"
            | "prusti_contracts::moved"
            | "prusti_contracts::local_capability"
            | "prusti_contracts::localRef_capability"
            | "prusti_contracts::unique_capability" => {
                true
            }

            _ => false,
        }
    }

    /// Returns the snapshot of a pure special function call.
    fn encode_prusti_function_call(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[MirExpr<'tcx>],
        return_ty: ty::Ty<'tcx>,
        span: Span,
        context: GhostOrExec,
    ) -> SpannedEncodingResult<Option<SnapshotExpr>> {
        let frame = open_trace!(
            self, "encode_prusti_function_call",
            format!("{called_def_id:?}, {call_substs:?}, {} args", args.len())
        );
        let full_func_proc_name = self.env().name.get_absolute_item_name(called_def_id);
        let arg_tys: Vec<_> = args.iter().map(|arg| arg.ty(self.mir(), self.tcx()).ty).collect();
        if !self.is_prusti_pure(called_def_id, call_substs, &arg_tys) {
            return Ok(None);
        }

        // Functions to encode the arguments in various ways
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
        let encode_value_arg = |expr: &MirExpr<'tcx>, context: GhostOrExec| -> SpannedEncodingResult<vir::Expr> {
            let encoded_expr = self.encode_mir_expr_snapshot(expr, context).with_default_span(span)?;
            let converted_expr = self.convert_to_value_snapshot(
                encoded_expr,
                expr.ty(self.mir(), self.tcx()).ty,
            ).with_default_span(span)?;
            Ok(converted_expr)
        };
        let encode_memory_arg = |expr: &MirExpr<'tcx>, context: GhostOrExec| -> SpannedEncodingResult<vir::Expr> {
            let encoded_expr = self.encode_mir_expr_snapshot(expr, context).with_default_span(span)?;
            let converted_expr = self.convert_to_memory_snapshot(
                encoded_expr,
                expr.ty(self.mir(), self.tcx()).ty,
            ).with_default_span(span)?;
            Ok(converted_expr)
        };

        let return_val = match full_func_proc_name.as_str() {
            "std::cmp::PartialEq::eq" | "core::cmp::PartialEq::eq"
                if self.encoder().has_structural_eq_impl(args[0].ty(self.mir(), self.tcx()).ty) =>
            {
                assert_eq!(args.len(), 2);
                vir::Expr::eq_cmp(encode_value_arg(&args[0], context)?, encode_value_arg(&args[1], context)?)
            }
            _ if full_func_proc_name.ends_with(" as std::cmp::PartialEq>::eq") => {
                assert_eq!(args.len(), 2);
                vir::Expr::eq_cmp(encode_value_arg(&args[0], context)?, encode_value_arg(&args[1], context)?)
            }
            _ if full_func_proc_name.ends_with(" as core::cmp::PartialEq>::eq") => {
                assert_eq!(args.len(), 2);
                vir::Expr::eq_cmp(encode_value_arg(&args[0], context)?, encode_value_arg(&args[1], context)?)
            }

            "std::cmp::PartialEq::ne" | "core::cmp::PartialEq::ne"
                if self.encoder().has_structural_eq_impl(args[0].ty(self.mir(), self.tcx()).ty) =>
            {
                assert_eq!(args.len(), 2);
                vir::Expr::ne_cmp(encode_value_arg(&args[0], context)?, encode_value_arg(&args[1], context)?)
            }
            _ if full_func_proc_name.ends_with(" as std::cmp::PartialEq>::ne") => {
                assert_eq!(args.len(), 2);
                vir::Expr::ne_cmp(encode_value_arg(&args[0], context)?, encode_value_arg(&args[1], context)?)
            }
            _ if full_func_proc_name.ends_with(" as core::cmp::PartialEq>::ne") => {
                assert_eq!(args.len(), 2);
                vir::Expr::ne_cmp(encode_value_arg(&args[0], context)?, encode_value_arg(&args[1], context)?)
            }

            "prusti_contracts::old" => {
                assert_eq!(args.len(), 1);

                // Detect unsupported overflow checks in binary operations
                let mut found_checked_op_span = None;
                args[0].visit_all_rvalues(&mut |expr| {
                    if let RvalueExpr::CheckedBinaryOp { span, .. } = expr {
                        found_checked_op_span = Some(*span);
                    }
                    Ok(())
                })?;
                if let Some(opt_span) = found_checked_op_span {
                    let err_span = opt_span.unwrap_or(span);
                    error_incorrect!(err_span =>
                        "old expression contains a checked operation; this is not supported",
                    );
                }

                // Early return, otherwise the code will try to build a bool snapshot.
                let old_encoder = self.old_mir_expr_encoder().with_default_span(span)?;
                return Ok(Some(old_encoder.encode_mir_expr_snapshot(&args[0], GhostOrExec::Ghost)
                    .with_default_span(span)?));
            }

            "prusti_contracts::forall" | "prusti_contracts::exists" => {
                // TODO(fpoli): Encode quantifiers
                todo!()
                // encode_quantifier(
                //     self,
                //     span,
                //     encoded_value_args,
                //     fn_name == "prusti_contracts::exists",
                //     parent_def_id,
                //     substs,
                // )
            }

            "prusti_contracts::snap" => {
                assert_eq!(args.len(), 1);
                let encoded_arg = self.encode_mir_expr_snapshot(strip_ref(0)?, GhostOrExec::Ghost)
                    .with_default_span(span)?;
                return Ok(Some(encoded_arg));
            }

            "prusti_contracts::check_mem" => {
                assert_eq!(args.len(), 1);
                let encoded_arg = self.encode_mir_expr_snapshot(&args[0], GhostOrExec::Ghost)
                    .with_default_span(span)?;
                if encoded_arg.kind().is_value() {
                    error_incorrect!(span =>
                        "failed check; the argument of check_mem cannot be encoded as a memory \
                        snaphsot"
                    )
                }
                return Ok(Some(encoded_arg));
            }

            "prusti_contracts::snapshot_equality" => {
                assert_eq!(args.len(), 2);
                vir::Expr::eq_cmp(
                    encode_value_arg(strip_ref(0)?, GhostOrExec::Ghost)?,
                    encode_value_arg(strip_ref(1)?, GhostOrExec::Ghost)?,
                )
            }

            "prusti_contracts::memory_snapshot_equality" => {
                assert_eq!(args.len(), 2);
                vir::Expr::eq_cmp(
                    encode_memory_arg(strip_ref(0)?, GhostOrExec::Ghost)?,
                    encode_memory_arg(strip_ref(1)?, GhostOrExec::Ghost)?,
                )
            }

            "prusti_contracts::deref_id" => {
                assert_eq!(args.len(), 1);
                let ptr_snap = encode_value_arg(&args[0], GhostOrExec::Ghost)?;
                let ptr_addr = ValueSnapshotDomain::encode(self.encoder(), arg_tys[0])
                    .with_default_span(span)?
                    .target_address_function().with_default_span(span)?
                    .apply1(ptr_snap);
                let Some(version) = self.encode_version().with_default_span(span)? else {
                    error_internal!(span =>
                        "deref_id has been called in a context that doesn't have a memory version"
                    );
                };
                let ty::TyKind::RawPtr(ty::TypeAndMut { ty: target_ty, .. }) = arg_tys[0].kind() else {
                    error_internal!(span => "expected raw pointer; got {:?}", arg_tys[0]);
                };
                AddressDomain::encode(self.encoder(), *target_ty)
                    .with_default_span(span)?
                    .id_function().with_default_span(span)?
                    .apply2(ptr_addr, version)
            }

            "prusti_contracts::moved" => {
                assert_eq!(args.len(), 2);
                let ty::TyKind::RawPtr(ty::TypeAndMut { ty: target_ty, .. }) = arg_tys[0].kind() else {
                    error_internal!(span => "expected raw pointer; got {:?}", arg_tys[0]);
                };
                let Some(version) = self.encode_version().with_default_span(span)? else {
                    error_internal!(span =>
                        "moved has been called in a context that doesn't have a memory version"
                    );
                };
                let old_encoder = self.old_mir_expr_encoder().with_default_span(span)?;
                let Some(old_version) = old_encoder.encode_version().with_default_span(span)? else {
                    error_internal!(span =>
                        "moved has been called in a context that doesn't have an old memory version"
                    );
                };
                let snap_domain = ValueSnapshotDomain::encode(self.encoder(), arg_tys[0])
                    .with_default_span(span)?;
                let old_ptr = encode_value_arg(&args[0], GhostOrExec::Ghost)?;
                let new_ptr = encode_value_arg(&args[1], GhostOrExec::Ghost)?;
                OwnershipDomain::encode(self.encoder(), *target_ty)
                    .with_default_span(span)?
                    .moved_fact_function()
                    .with_default_span(span)?
                    .apply4(
                        snap_domain.target_address_function().with_default_span(span)?.apply1(old_ptr),
                        old_version,
                        snap_domain.target_address_function().with_default_span(span)?.apply1(new_ptr),
                        version,
                    )
            }

            name @ "prusti_contracts::local_capability"
            | name @ "prusti_contracts::localRef_capability"
            | name @ "prusti_contracts::unique_capability" => {
                let Some(almost_ownership_kind_name) = name.strip_prefix("prusti_contracts::") else {
                    error_internal!(span => "unexpected function name: {}", name);
                };
                let Some(ownership_kind_name) = almost_ownership_kind_name.strip_suffix("_capability") else {
                    error_internal!(span => "unexpected function name: {}", name);
                };
                let Ok(ownership_kind) = OwnershipKind::try_from(ownership_kind_name) else {
                    error_internal!(span => "unexpected ownership kind name: {}", ownership_kind_name);
                };
                assert_eq!(args.len(), 1);
                let ty::TyKind::RawPtr(ty::TypeAndMut { ty: target_ty, .. }) = arg_tys[0].kind() else {
                    error_internal!(span => "expected raw pointer; got {:?}", arg_tys[0]);
                };
                let encoded_addr_type = self.encoder().encode_builtin_domain_type(BuiltinDomainKind::Address(*target_ty))
                    .with_default_span(span)?;
                let Some(version) = self.encode_version().with_default_span(span)? else {
                    error_internal!(span =>
                        "local has been called in a context that doesn't have a memory version"
                    );
                };
                let ptr = encode_value_arg(&args[0], GhostOrExec::Ghost)?;
                let addr = ValueSnapshotDomain::encode(self.encoder(), arg_tys[0])
                    .with_default_span(span)?
                    .target_address_function()
                    .with_default_span(span)?
                    .apply1(ptr);
                let free_root = vir::LocalVar::new("_root", vir::Type::Int);
                let free_addr = vir::LocalVar::new("_addr", encoded_addr_type);
                let free_fact = OwnershipDomain::encode(self.encoder(), *target_ty)
                    .with_default_span(span)?
                    .ownership_fact_function(ownership_kind)
                    .with_default_span(span)?
                    .apply3(
                        free_root.clone(),
                        free_addr.clone(),
                        version,
                    );
                // There exist a root for the given address and version s.t. local_capability(..) holds
                vir_expr!{
                    exists [free_root], [free_addr] ::
                    { [free_fact] } ::
                    ([free_fact] && ([vir::Expr::from(free_addr)] == [addr]))
                }
            }

            missing => {
                error_internal!(span => "the is_prusti_pure function missed the case {missing:?}");
            }
        };

        if !return_ty.is_primitive_ty() {
            error_internal!(span =>
                "prusti functions can only return primitive types; got {return_ty:?}"
            );
        }
        let return_snapshot_domain = MemSnapshotDomain::encode(self.encoder(), return_ty)
            .with_default_span(span)?;
        let return_snapshot = return_snapshot_domain.constructor_function()
            .with_default_span(span)?.apply1(return_val);
        close_trace!(self, frame, &return_snapshot);
        Ok(Some(SnapshotExpr::new_memory(return_snapshot)))
    }

    /// Encodes the snapshot of a pure (stable or unstable) function call.
    #[allow(clippy::too_many_arguments)]
    fn impl_encode_pure_function_call(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[MirExpr<'tcx>],
        version: Option<vir::LocalVar>,
        return_ty: ty::Ty<'tcx>,
        span: Span,
        context: GhostOrExec,
    ) -> SpannedEncodingResult<SnapshotExpr> {
        let frame = open_trace!(
            self, "impl_encode_pure_function_call",
            format!("{called_def_id:?}, {call_substs:?}, {} args", args.len())
        );
        if let Some(expr) = self.encode_prusti_function_call(
            called_def_id,
            call_substs,
            args,
            return_ty,
            span,
            context,
        )? {
            return Ok(expr);
        }

        self.check_call(called_def_id, call_substs, span)?;

        let arg_tys: Vec<_> = args.iter().map(|arg| arg.ty(self.mir(), self.tcx()).ty).collect();
        let is_prusti_pure = self.is_prusti_pure(called_def_id, call_substs, &arg_tys);
        debug_assert!(!is_prusti_pure);
        let is_pure_stable = self.is_pure_stable(Some(self.def_id()), called_def_id, call_substs);
        let is_pure_memory_or_unstable = self.is_pure_memory(Some(self.def_id()), called_def_id, call_substs)
            || self.is_pure_unstable(Some(self.def_id()), called_def_id, call_substs);
        debug_assert!(!is_pure_stable || !is_pure_memory_or_unstable);

        // Encode arguments (formal and actual)
        let mut encoded_args: Vec<vir::Expr> = Vec::with_capacity(args.len());
        let mut formal_args: Vec<vir::LocalVar> = Vec::with_capacity(args.len());
        let mut snapshot_kind: SnapshotKind;

        let mut encoded_snapshot_args = Vec::with_capacity(args.len());
        for arg in args {
            encoded_snapshot_args.push(self.encode_mir_expr_snapshot(arg, context).with_span(span)?);
        }

        if is_pure_stable {
            // Pure stable functions accept and return only value snapshots.
            // Prusti pure functions accept and return only value snapshots.
            for (encoded_snapshot_arg, &arg_ty) in encoded_snapshot_args.drain(..).zip(arg_tys.iter()) {
                let encoded_arg = self.convert_to_value_snapshot(encoded_snapshot_arg, arg_ty)
                    .with_span(span)?;
                encoded_args.push(encoded_arg);
            }
            snapshot_kind = SnapshotKind::Value;
        } else if is_pure_memory_or_unstable {
            // Pure memory and unstable functions accept and return only memory snapshots.
            for (encoded_snapshot_arg, &arg_ty) in encoded_snapshot_args.drain(..).zip(arg_tys.iter()) {
                let encoded_arg = self.convert_to_memory_snapshot(encoded_snapshot_arg, arg_ty)
                    .with_span(span)?;
                encoded_args.push(encoded_arg);
            }
            snapshot_kind = SnapshotKind::Memory;
        } else {
            error_incorrect!(span =>
                "pure code cannot call the non-pure function {}",
                self.env().name.get_absolute_item_name(called_def_id),
            );
        }

        for (arg_idx, &arg_ty) in arg_tys.iter().enumerate() {
            let arg_type = self.encoder().encode_builtin_domain_type(
                match snapshot_kind {
                    SnapshotKind::Memory => BuiltinDomainKind::MemorySnapshot(arg_ty),
                    SnapshotKind::Value => BuiltinDomainKind::ValueSnapshot(arg_ty),
                }
            ).with_span(span)?;
            formal_args.push(vir::LocalVar::new(format!("x{arg_idx}"), arg_type));
        }

        // TODO(fpoli): contracts are not marked as unstable, but they might be unstable.
        if self.is_pure_unstable(Some(self.def_id()), called_def_id, call_substs) {
            debug_assert!(!is_prusti_pure);
            if let Some(actual_version) = version {
                encoded_args.push(actual_version.clone().into());
                formal_args.push(actual_version);
            } else {
                error_incorrect!(span =>
                    "unstable functions can only be called from impure code or from \
                    pure unstable code",
                );
            }
        }

        let (function_name, return_type) = self.encoder().encode_pure_function_use(
            called_def_id,
            self.def_id(),
            call_substs,
        ).with_span(span)?;
        let pos = self.register_error(span, ErrorCtxt::PureFunctionCall);
        let type_arguments = self.encode_substs(call_substs).with_span(self.span())?;
        let func_expr = vir::Expr::func_app(
            function_name,
            type_arguments,
            encoded_args,
            formal_args,
            return_type,
            pos,
        );

        close_trace!(self, frame, &func_expr);
        Ok(SnapshotExpr::new(func_expr, snapshot_kind))
    }

    /// Returns the functional pre/postcondition of a call.
    /// Note: currently only used to encode impure calls.
    fn encode_call_contract_expr(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[mir::Operand<'tcx>],
        result: Option<mir::Place<'tcx>>,
        spec_expr_kind: SpecExprKind,
    ) -> EncodingResult<Vec<vir::Expr>> {
        let result = match result {
            Some(result) => result,
            None => {
                // Hack. The proper solution is to raise an error if the contract uses `result`.
                mir::Local::from_usize(0).into()
            }
        };

        // Prepare old bodyless encoder
        let old_encoder = self.old_mir_expr_encoder()?;
        let mut old_encoded_locals = vec![
            old_encoder.encode_place_snapshot(result)?
        ];
        let mut old_encoded_locals_address = vec![
            old_encoder.encode_place_address(result)?
        ];
        for arg in args {
            let encoded_arg = old_encoder.encode_operand_snapshot(arg)?;
            old_encoded_locals.push(encoded_arg);
            let encoded_arg_address = old_encoder.encode_operand_address(arg)?;
            old_encoded_locals_address.push(encoded_arg_address);
        }
        let old_bodyless_encoder = Some(box BodylessEncoder::new(
            self.encoder(),
            called_def_id,
            self.def_id(),
            call_substs,
            &old_encoded_locals,
            &old_encoded_locals_address,
            old_encoder.encode_version()?,
            None,
        )?);

        // Prepare bodyless encoder
        let mut encoded_locals: Vec<SnapshotExpr> = vec![
            self.encode_place_snapshot(result)?
        ];
        let mut encoded_locals_address = vec![
            self.encode_place_address(result)?
        ];
        for arg in args {
            let encoded_arg = self.encode_operand_snapshot(arg)?;
            encoded_locals.push(encoded_arg);
            let encoded_arg_address = self.encode_operand_address(arg)?;
            encoded_locals_address.push(encoded_arg_address);
        }
        let bodyless_encoder = BodylessEncoder::new(
            self.encoder(),
            called_def_id,
            self.def_id(),
            call_substs,
            &encoded_locals,
            &encoded_locals_address,
            self.encode_version()?,
            old_bodyless_encoder,
        )?;
        Ok(bodyless_encoder.encode_contract_expr(spec_expr_kind)?)
    }
}
