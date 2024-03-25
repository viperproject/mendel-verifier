// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::Version;
use crate::encoder::{
    mir::contracts::ContractsEncoderInterface,
    safe_clients::{prelude::*, procedure_encoder::VersionBasedProcedureEncoder},
};

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    pub fn encode_impure_function_call(
        &mut self,
        call_site_span: Span,
        mir_args: &[mir::Operand<'tcx>],
        destination: Option<mir::Place<'tcx>>,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        location: mir::Location,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        let full_fn_name = self
            .encoder
            .env()
            .name
            .get_absolute_item_name(called_def_id);

        // Detect calls to panic
        match full_fn_name.as_str() {
            "std::rt::begin_panic"
            | "core::panicking::panic"
            | "core::panicking::panic_fmt"
            | "std::rt::panic_fmt" => {
                // This is called when a Rust assertion fails
                // mir_args[0]: message
                // mir_args[1]: position of failing assertions

                if !config::check_panics() {
                    debug!("Absence of panic will not be checked");
                    return Ok(vec![]);
                }

                // Example of mir_args[0]: 'const "internal error: entered unreachable code"'
                let panic_message = format!("{:?}", mir_args[0]);

                let panic_cause = self.encode_panic_cause(call_site_span);
                let pos = self.register_error(call_site_span, ErrorCtxt::Panic(panic_cause));
                return Ok(vec![
                    vir::Stmt::comment(format!("Rust panic - {panic_message}")),
                    vir::Stmt::Assert(vir::Assert {
                        expr: false.into(),
                        position: pos,
                    }),
                ]);
            }
            _ => {}
        }

        let mut args_mir_expr = vec![];
        for arg in mir_args {
            let encoded_arg = RvalueExpr::from_operand(arg)
                .with_span(call_site_span)?
                .into();
            args_mir_expr.push(encoded_arg);
        }

        // Detect calls to special pure functions such as `PartialEq::eq` on Copy types, even if
        // these are not marked as pure.
        if let Some(actual_destination) = destination {
            let result_ty = self.get_place_ty(actual_destination).ty;
            if let Some(rhs_snapshot) = self
                .fixed_version_encoder(Version::Old)
                .encode_prusti_function_call(
                    called_def_id,
                    call_substs,
                    &args_mir_expr,
                    result_ty,
                    call_site_span,
                    GhostOrExec::Exec,
                )?
            {
                debug_assert!(rhs_snapshot.kind().is_memory());
                let lhs_snapshot = self
                    .encode_place_snapshot(actual_destination, Version::CurrPre) // CurrOld would work too
                    .with_span(call_site_span)?;
                return Ok(vec![vir::Stmt::inhale(vir_expr!(
                    [lhs_snapshot] == [rhs_snapshot.into_expr()]
                ))]);
            }
        }

        // Encode as a normal impure function call
        self.encode_standard_impure_function_call(
            call_site_span,
            mir_args,
            destination,
            called_def_id,
            call_substs,
            location,
        )
    }

    /// Encodes a normal impure function call
    fn encode_standard_impure_function_call(
        &mut self,
        call_site_span: Span,
        mir_args: &[mir::Operand<'tcx>],
        destination: Option<mir::Place<'tcx>>,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        location: mir::Location,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        let mut stmts = vec![];

        self.check_call(called_def_id, call_substs, call_site_span)?;

        // Assume relation between old and current memory version.
        // These assumptions (and the previously encode havoc) are only here to stabilize
        // the state before checking the method preconditions.
        stmts.extend(self.encode_framing_before_location(location)?);

        // Encode ownership before the call
        // These assumptions (and the previously encode havoc) are only here to stabilize
        // the state before checking the method preconditions.
        stmts.extend(self.encode_ownership_before_location(location)?);

        // Check the (stabilized) precondition of the called method
        let preconditions = self
            .fixed_version_encoder(Version::Old)
            .encode_call_contract_expr(
                called_def_id,
                call_substs,
                mir_args,
                destination,
                SpecExprKind::Pre,
            )
            .with_span(call_site_span)?;
        let precondition_pos =
            self.register_error(call_site_span, ErrorCtxt::ExhaleMethodPrecondition);
        stmts.push(vir::Stmt::comment(format!(
            "Check the preconditions (num: {}) of the call",
            preconditions.len(),
        )));
        for precondition in preconditions {
            stmts.push(vir::Stmt::Assert(vir::Assert {
                expr: precondition,
                position: precondition_pos,
            }));
        }

        // Havoc the memory version, to model interference and the method execution.
        stmts.push(vir::Stmt::comment(
            "Havoc the memory version during the call",
        ));
        stmts.extend(self.encode_version_bump().with_span(call_site_span)?);

        // If the call blocks &mut-typed arguments, store their target address and the version.
        let called_contract = self
            .encoder
            .get_mir_procedure_contract_for_call(self.def_id(), called_def_id, call_substs)
            .with_default_span(call_site_span)?;
        if called_contract.pledges().next().is_some() {
            if called_contract.borrow_infos.is_empty() {
                error_incorrect!(call_site_span =>
                    "the pledges annotation can only be used on functions that block some of their \
                    arguments, but this call blocks none",
                );
            }
            stmts.push(vir::Stmt::comment(
                "Store the target address of the &mut-typed arguments, for the encoding of the pledge"
            ));
            let block_idx = location.block.index();
            let version = self.fixed_version_encoder(Version::Old).version().clone();
            let version_name = format!("_call_{block_idx}_pre_version");
            let named_version = vir::LocalVar::new(version_name, version.typ.clone());
            self.cfg_method
                .add_local_var(&named_version.name, named_version.typ.clone());
            self.call_pre_version
                .insert(location, named_version.clone());
            stmts.push(vir::Stmt::Assign(vir::Assign {
                target: named_version.into(),
                source: version.into(),
                kind: vir::AssignKind::Copy,
            }));
            for (arg_idx, arg) in mir_args.iter().enumerate() {
                let arg_ty = self.get_operand_ty(arg);
                if let &ty::TyKind::Ref(_, target_ty, _) = arg_ty.kind() {
                    let arg_expr = RvalueExpr::from_operand(arg)
                        .with_span(call_site_span)?
                        .into();
                    let encoded_snapshot = self
                        .fixed_version_encoder(Version::Old)
                        .encode_mir_expr_snapshot(&arg_expr, GhostOrExec::Exec)
                        .with_span(call_site_span)?;
                    let encoded_address = self
                        .encode_snapshot_domain(SnapshotKind::Memory, arg_ty)
                        .with_span(call_site_span)?
                        .target_address_function()
                        .with_span(call_site_span)?
                        .apply1(encoded_snapshot.into_expr());
                    let address_type = self
                        .encoder
                        .encode_builtin_domain_type(BuiltinDomainKind::Address(target_ty))
                        .with_span(call_site_span)?;
                    let blocked_address_name =
                        format!("_call_{block_idx}_blocked_address_{arg_idx}",);
                    let blocked_address_var =
                        vir::LocalVar::new(blocked_address_name, address_type);
                    self.cfg_method
                        .add_local_var(&blocked_address_var.name, blocked_address_var.typ.clone());
                    self.call_blocked_address.insert(
                        (location, arg_idx),
                        (blocked_address_var.clone(), target_ty),
                    );
                    stmts.push(vir::Stmt::Assign(vir::Assign {
                        target: blocked_address_var.into(),
                        source: encoded_address,
                        kind: vir::AssignKind::Copy,
                    }));
                }
            }
        }

        // Assume the postcondition of the called method
        let postconditions = self
            .fixed_version_encoder(Version::CurrOld)
            .encode_call_contract_expr(
                called_def_id,
                call_substs,
                mir_args,
                destination,
                SpecExprKind::Post,
            )
            .with_span(call_site_span)?;
        stmts.push(vir::Stmt::comment(format!(
            "Assume the postconditions (num: {}) of the call",
            postconditions.len(),
        )));
        for postcondition in postconditions {
            stmts.push(vir::Stmt::inhale(postcondition));
        }

        // Assume that the snapshot of the arguments is still valid after the call,
        // because they might be used by the postcondition.
        // TODO: The "Allocated" name is misleading; it should be just "ValidSnap".
        let Some(allocation_facts) = self.allocation_facts().lookup_before(location) else {
            error_internal!(call_site_span =>
                "Allocation facts not available before {:?}", location,
            );
        };
        stmts.push(vir::Stmt::comment(
            "Validity and shallow ownership of the arguments",
        ));
        for (index, mir_arg) in mir_args.iter().enumerate() {
            let arg_ty = self.get_operand_ty(mir_arg);
            let ownership_domain =
                OwnershipDomain::encode(self.encoder, arg_ty).with_span(call_site_span)?;
            let validity_function = ownership_domain
                .ownership_fact_function(OwnershipKind::Allocated)
                .with_span(call_site_span)?;
            let shallow_ownership_function = ownership_domain
                .framed_call_fact_function(OwnershipKind::ShallowlyOwned)
                .with_span(call_site_span)?;
            let Some(place_addr) = self.fixed_version_encoder(Version::OldPre)
                .encode_operand_address(mir_arg).with_span(call_site_span)? else {
                // The argument is a constant
                continue;
            };
            let old_version = self.encode_version(Version::Old);
            let curr_version = self.encode_version(Version::CurrOld);
            let validity_fact = validity_function.apply3(
                -1 - (index as isize), // Dummy
                place_addr.clone(),
                curr_version.clone(),
            );
            let shallow_ownership_fact =
                shallow_ownership_function.apply3(place_addr, old_version, curr_version);
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume Allocated(arg#{index}: {arg_ty:?})")),
                vir::Stmt::inhale(validity_fact),
                vir::Stmt::comment(format!("frame ShallowlyOwned(arg#{index}: {arg_ty:?})")),
                vir::Stmt::inhale(shallow_ownership_fact),
            ]);
        }

        // Later, the usual encoding os MIR statements will assume the relation between
        // the intermediate memory version and the current one.

        Ok(stmts)
    }

    /// Encodes a pure (stable or unstable) function call
    pub fn encode_pure_function_call(
        &self,
        call_site_span: Span,
        mir_args: &[mir::Operand<'tcx>],
        destination: mir::Place<'tcx>,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        location: mir::Location,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        let mut args_mir_expr = vec![];
        for arg in mir_args {
            let encoded_arg = RvalueExpr::from_operand(arg)
                .with_span(call_site_span)?
                .into();
            args_mir_expr.push(encoded_arg);
        }
        let result_ty = self.get_place_ty(destination).ty;
        let old_encoder = self.fixed_version_encoder(Version::Old);
        let is_pure_stable = self.is_pure_stable(Some(self.def_id()), called_def_id, call_substs);
        let is_pure_memory = self.is_pure_memory(Some(self.def_id()), called_def_id, call_substs);
        let call_version = if is_pure_stable || is_pure_memory {
            None
        } else {
            PlaceEncoder::encode_version(old_encoder).with_span(call_site_span)?
        };
        let rhs_snapshot = old_encoder.encode_pure_call_snapshot(
            called_def_id,
            call_substs,
            &args_mir_expr,
            call_version,
            result_ty,
            call_site_span,
            GhostOrExec::Exec,
        )?;
        let rhs_memory_snapshot = old_encoder
            .convert_to_memory_snapshot(rhs_snapshot, result_ty)
            .with_span(call_site_span)?;
        let lhs_snapshot = self
            .encode_place_snapshot(destination, Version::CurrPre) // CurrOld would work too
            .with_span(call_site_span)?;
        let mut stmts = vec![vir::Stmt::inhale(vir_expr!(
            [lhs_snapshot] == [rhs_memory_snapshot]
        ))];

        // Since a pure function cannot have side effects, we can frame using all facts available
        // before the call.
        // TODO: Avoid the redundancy with what the framing of the call later assumes.
        stmts.extend(self.encode_framing_before_location(location)?);

        Ok(stmts)
    }
}
