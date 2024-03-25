// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    mir::{pure::PureEncodingContext, specifications::SpecificationsInterface},
    safe_clients::prelude::*,
};
use ownership_domain::{OwnershipDomain, OwnershipKind};

pub fn build_library_ownership_axioms<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<Vec<(String, vir::Expr)>> {
    trace!("build_library_ownership_axioms({:?})", ty);
    let ty_name = types::encode_type_name(encoder, ty)?;
    let version_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)?;
    let address_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(ty))?;
    let base_ownership_domain = OwnershipDomain::encode(encoder, ty)?;
    let snapshot_domain = MemSnapshotDomain::encode(encoder, ty)?;
    let address_domain = AddressDomain::encode(encoder, ty)?;
    let tcx = encoder.env().tcx();
    let mut axioms = vec![];

    let ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
        return Ok(axioms);
    };

    for (spec_idx, ownership_spec) in encoder
        .get_ownership_specs(adt_def.did())
        .drain(..)
        .enumerate()
    {
        // TODO(fpoli): Verify that the target/condition expressions do not panic nor overflow.

        let root = vir::LocalVar::new("r", vir::Type::Int);
        let address = vir::LocalVar::new("a", address_type.clone());
        let address_2 = vir::LocalVar::new("a2", address_type.clone());
        let version = vir::LocalVar::new("v", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let base_kind: OwnershipKind = ownership_spec.self_ownership.into();
        let target_kind: OwnershipKind = ownership_spec.target_ownership.into();

        // Encode condition of the ownership
        let condition: vir::Expr = if let Some(local_def_id) = ownership_spec.condition {
            let condition_def_id = local_def_id.to_def_id();
            let condition_span = tcx.def_span(condition_def_id);
            let condition_mir =
                encoder
                    .env()
                    .body
                    .get_spec_body(condition_def_id, substs, ownership_spec.source);
            let condition_args_snapshot = [SnapshotExpr::new_memory(
                address_domain
                    .deref_function()?
                    .apply2(address.clone(), version.clone()),
            )];
            let condition_args_address = [Some(address.clone().into())];
            let condition_encoder = AssertionEncoder::new(
                encoder,
                condition_def_id,
                ownership_spec.source,
                substs,
                condition_mir,
                &condition_args_snapshot,
                &condition_args_address,
                Some(version.clone()),
                None,
                // Ignore panic paths
                PureEncodingContext::Trigger,
            );
            let condition_ty = condition_encoder.get_local_ty(mir::RETURN_PLACE);
            debug_assert!(condition_ty.is_bool());
            let condition_snapshot = condition_encoder.encode_body(GhostOrExec::Ghost)?;
            let condition_snapshot_domain = MemSnapshotDomain::encode(encoder, condition_ty)?;
            condition_snapshot_domain
                .primitive_field_function()?
                .apply1(condition_snapshot)
        } else {
            true.into()
        };

        // Encode address of the target
        let target_parent_body = encoder.env().body.get_spec_body(
            ownership_spec.target_parent.into(),
            substs,
            ownership_spec.source,
        );
        let target_def_stmt = target_parent_body
            .stmt_at(mir::Location {
                block: mir::START_BLOCK,
                statement_index: 1,
            })
            .left()
            .unwrap();
        let mir::StatementKind::Assign(box (_, ref target_rhs)) = &target_def_stmt.kind else {
            unreachable!()
        };
        let &mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(_, target_substs), _) = target_rhs else {
            unreachable!()
        };
        // Weird fix for closure call substitutions
        let target_substs = tcx.mk_substs(substs.iter().chain(target_substs));
        let target_def_id = ownership_spec.target.to_def_id();
        let target_span = tcx.def_span(target_def_id);
        let target_mir = encoder.env().body.get_closure_body(
            ownership_spec.target,
            target_substs,
            ownership_spec.target_parent.into(),
        );
        let mut target_ptr_ty = target_mir.local_decls[mir::RETURN_PLACE].ty;
        let mut target_ptr_snapshot_domain = MemSnapshotDomain::encode(encoder, target_ptr_ty)?;
        // Address and version 1
        let target_args_snapshot = [
            SnapshotExpr::new_memory(false.into()), // dummy
            SnapshotExpr::new_memory(
                address_domain
                    .deref_function()?
                    .apply2(address.clone(), version.clone()),
            ),
        ];
        let target_args_address = [None, Some(address.clone().into())];
        let target_encoder = AssertionEncoder::new(
            encoder,
            target_def_id,
            ownership_spec.target_parent.into(),
            target_substs,
            target_mir.clone(),
            &target_args_snapshot,
            &target_args_address,
            Some(version.clone()),
            None,
            // Ignore panic paths
            PureEncodingContext::Trigger,
        );
        let target_address = target_ptr_snapshot_domain
            .target_address_function()?
            .apply1(target_encoder.encode_body(GhostOrExec::Ghost)?);
        // Address and version 2
        let target_args_snapshot_2 = [
            SnapshotExpr::new_memory(false.into()), // dummy
            SnapshotExpr::new_memory(
                address_domain
                    .deref_function()?
                    .apply2(address_2.clone(), version_2.clone()),
            ),
        ];
        let target_args_address_2 = [None, Some(address_2.clone().into())];
        let target_encoder_2 = AssertionEncoder::new(
            encoder,
            target_def_id,
            ownership_spec.target_parent.into(),
            target_substs,
            target_mir.clone(),
            &target_args_snapshot_2,
            &target_args_address_2,
            Some(version_2.clone()),
            None,
            // Ignore panic paths
            PureEncodingContext::Trigger,
        );
        let target_address_2 = target_ptr_snapshot_domain
            .target_address_function()?
            .apply1(target_encoder_2.encode_body(GhostOrExec::Ghost)?);

        let &ty::TyKind::RawPtr(ty::TypeAndMut { ty: target_ty, .. }) = target_ptr_ty.kind() else {
            error_internal!("Expected raw pointer type, got {:?}", target_ptr_ty);
        };
        let target_ownership_domain = OwnershipDomain::encode(encoder, target_ty)?;

        {
            // At program point
            let base_fact = base_ownership_domain
                .ownership_fact_function(base_kind)?
                .apply3(root.clone(), address.clone(), version.clone());
            let target_fact = target_ownership_domain
                .ownership_fact_function(target_kind)?
                .apply3(root.clone(), target_address.clone(), version.clone());
            let body = vir_expr!(
                forall [root], [address], [version] ::
                { [base_fact] } ::
                (([base_fact] && [condition]) ==> [target_fact])
            );
            axioms.push((
                format!("User-specified library ownership spec #{spec_idx} for {ty_name}"),
                body,
            ));
        }
        {
            // Across stmt
            let base_fact = base_ownership_domain
                .framed_stmt_fact_function(base_kind)?
                .apply3(address.clone(), version.clone(), version_2.clone());
            let target_fact = target_ownership_domain
                .framed_stmt_fact_function(target_kind)?
                .apply3(target_address.clone(), version.clone(), version_2.clone());
            let body = vir_expr!(
                forall [address], [version], [version_2] ::
                { [base_fact] } ::
                (([base_fact] && [condition]) ==> [target_fact])
            );
            axioms.push((
                format!("User-specified library ownership spec #{spec_idx} across statement for {ty_name}"),
                body,
            ));
        }
        {
            // Across call
            let base_fact = base_ownership_domain
                .framed_call_fact_function(base_kind)?
                .apply3(address.clone(), version.clone(), version_2.clone());
            let target_fact = target_ownership_domain
                .framed_call_fact_function(target_kind)?
                .apply3(target_address.clone(), version.clone(), version_2.clone());
            let body = vir_expr!(
                forall [address], [version], [version_2] ::
                { [base_fact] } ::
                (([base_fact] && [condition]) ==> [target_fact])
            );
            axioms.push((
                format!(
                    "User-specified library ownership spec #{spec_idx} across call for {ty_name}"
                ),
                body,
            ));
        }
        {
            // Across moves
            let base_fact = base_ownership_domain.moved_fact_function()?.apply4(
                address.clone(),
                version.clone(),
                address_2.clone(),
                version_2.clone(),
            );
            let target_fact = target_ownership_domain.moved_fact_function()?.apply4(
                target_address,
                version.clone(),
                target_address_2,
                version_2.clone(),
            );
            let body = vir_expr!(
                forall [address], [version], [address_2], [version_2] ::
                { [base_fact] } ::
                (([base_fact] && [condition]) ==> [target_fact])
            );
            axioms.push((
                format!(
                    "User-specified library ownership spec #{spec_idx} across move for {ty_name}"
                ),
                body,
            ));
        }
    }

    Ok(axioms)
}
