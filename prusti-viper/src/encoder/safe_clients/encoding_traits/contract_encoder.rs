// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir::pure::PureEncodingContext;
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::contracts::ProcedureContractMirDef;

/// Trait used to encode the pre/postcondition of the current function.
pub trait ContractEncoder<'v, 'tcx: 'v>: PlaceEncoder<'v, 'tcx> + WithDefId<'v, 'tcx> + WithOldPlaceEncoder<'v, 'tcx> {
    fn contract(&self) -> &ProcedureContractMirDef<'tcx>;

    /// Encode the pre/post-condition (functional specification).
    /// Value ranges are currently not supported.
    fn encode_contract_expr(&self, spec_expr_kind: SpecExprKind) -> SpannedEncodingResult<Vec<vir::Expr>> {
        let contract = self.contract();
        let old_place_encoder = self.old_place_encoder().with_span(self.span())?;

        // Encode old args
        let mut old_encoded_args_snapshot = Vec::with_capacity(contract.args.len());
        let mut old_encoded_args_address = Vec::with_capacity(contract.args.len());
        for &arg in &contract.args {
            old_encoded_args_snapshot.push(old_place_encoder.encode_local_snapshot(arg)?);
            old_encoded_args_address.push(old_place_encoder.encode_local_address(arg)?);
        }
        if spec_expr_kind.is_post_or_pledge() {
            let return_local = contract.returned_value;
            old_encoded_args_snapshot.push(old_place_encoder.encode_local_snapshot(return_local)?);
            old_encoded_args_address.push(old_place_encoder.encode_local_address(return_local)?);
        };

        // Encode args
        let mut encoded_args_snapshot = Vec::with_capacity(contract.args.len());
        let mut encoded_args_address = Vec::with_capacity(contract.args.len());
        for &arg in &contract.args {
            // TODO: Evaluate arguments in the old state
            encoded_args_snapshot.push(self.encode_local_snapshot(arg)?);
            encoded_args_address.push(self.encode_local_address(arg)?);
        }
        if spec_expr_kind.is_post_or_pledge() {
            let return_local = contract.returned_value;
            // TODO: Evaluate arguments in the old state
            encoded_args_snapshot.push(self.encode_local_snapshot(return_local)?);
            encoded_args_address.push(self.encode_local_address(return_local)?);
        };

        // Encode functional specification
        let mut func_spec = vec![];
        let bool_ty = self.tcx().mk_ty(ty::TyKind::Bool);
        let assertion_info = match spec_expr_kind {
            SpecExprKind::Pre => contract.functional_precondition(self.env(), self.substs()),
            SpecExprKind::Post => contract.functional_postcondition(self.env(), self.substs()),
            SpecExprKind::Pledge(spec_expr_def_id) => vec![(spec_expr_def_id, self.substs())],
        };
        let version = PlaceEncoder::encode_version(self).with_span(self.span())?;
        let old_version = old_place_encoder.encode_version().with_span(self.span())?;
        for (assertion_def_id, assertion_substs) in assertion_info {
            let assertion_span = self.env().query.get_def_span(assertion_def_id);
            let assertion_mir = self.env().body.get_expression_body(
                assertion_def_id,
                assertion_substs,
                self.def_id(),
            );
            let old_assertion_encoder = AssertionEncoder::new(
                self.encoder(),
                assertion_def_id,
                self.def_id(),
                assertion_substs,
                assertion_mir.clone(),
                &old_encoded_args_snapshot,
                &old_encoded_args_address,
                old_version.clone(),
                None,
                PureEncodingContext::Assertion,
            );
            let assertion_encoder = AssertionEncoder::new(
                self.encoder(),
                assertion_def_id,
                self.def_id(),
                assertion_substs,
                assertion_mir,
                &encoded_args_snapshot,
                &encoded_args_address,
                version.clone(),
                Some(box old_assertion_encoder),
                PureEncodingContext::Assertion,
            );
            let expr = assertion_encoder.encode_body(GhostOrExec::Ghost)?;
            let expr_value = self.encode_snapshot_primitive_value(
                SnapshotExpr::new_memory(expr), bool_ty,
            ).with_span(self.span())?;
            let expr_pos = self.register_span(assertion_span);
            func_spec.push(expr_value.set_default_pos(expr_pos));
        }
        Ok(func_spec)
    }
}
