// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::specifications::SpecificationsInterface;
use prusti_interface::specs::typed::ProcedureSpecificationKind;

pub trait WithEncoder<'v, 'tcx: 'v> {
    fn encoder(&self) -> &Encoder<'v, 'tcx>;

    fn env(&self) -> &'v Environment<'tcx> {
        self.encoder().env()
    }

    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.env().tcx()
    }

    fn is_pure(&self, caller_def_id: Option<DefId>, def_id: DefId, substs: ty::SubstsRef<'tcx>) -> bool {
        self.is_pure_stable(caller_def_id, def_id, substs)
        || self.is_pure_memory(caller_def_id, def_id, substs)
        || self.is_pure_unstable(caller_def_id, def_id, substs)
    }

    fn is_pure_stable(&self, caller_def_id: Option<DefId>, mut def_id: DefId, mut substs: ty::SubstsRef<'tcx>) -> bool {
        if let Some(actual_caller_def_id) = caller_def_id {
            (def_id, substs) = self.env().query.resolve_method_call(
                actual_caller_def_id, def_id, substs,
            );
        }
        let kind = self.encoder().get_proc_kind(def_id, Some(substs));
        matches!(kind,
            ProcedureSpecificationKind::Pure
            | ProcedureSpecificationKind::Predicate(_)
        )
    }

    fn is_pure_memory(&self, caller_def_id: Option<DefId>, mut def_id: DefId, mut substs: ty::SubstsRef<'tcx>) -> bool {
        if let Some(actual_caller_def_id) = caller_def_id {
            (def_id, substs) = self.env().query.resolve_method_call(
                actual_caller_def_id, def_id, substs,
            );
        }
        let kind = self.encoder().get_proc_kind(def_id, Some(substs));
        matches!(kind, ProcedureSpecificationKind::PureMemory)
    }

    fn is_pure_unstable(&self, caller_def_id: Option<DefId>, mut def_id: DefId, mut substs: ty::SubstsRef<'tcx>) -> bool {
        if let Some(actual_caller_def_id) = caller_def_id {
            (def_id, substs) = self.env().query.resolve_method_call(
                actual_caller_def_id, def_id, substs,
            );
        }
        let kind = self.encoder().get_proc_kind(def_id, Some(substs));
        matches!(kind, ProcedureSpecificationKind::PureUnstable)
    }

    fn is_ghost(&self, caller_def_id: Option<DefId>, mut def_id: DefId) -> bool {
        if let Some(actual_caller_def_id) = caller_def_id {
            (def_id, _) = self.env().query.resolve_method_call(
                actual_caller_def_id, def_id, self.env().query.identity_substs(def_id),
            );
        }
        self.env().query.has_prusti_attribute(def_id, "ghost_fn")
        || self.env().query.has_prusti_attribute(def_id, "predicate")
    }

    /// Encodes the primitive value of a snapshot.
    fn encode_snapshot_primitive_value(
        &self, expr: SnapshotExpr, ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Expr> {
        if !ty.is_primitive_ty() {
            error_internal!(
                "encode_snapshot_primitive_value called with non-primitive type {ty:?} \
                (expr: {expr:?}"
            )
        }
        let expr_domain = self.encode_snapshot_domain(expr.kind(), ty)?;
        Ok(expr_domain.primitive_field_function()?.apply1(expr.into_expr()))
    }

    fn encode_snapshot_domain(
        &self, kind: SnapshotKind, ty: ty::Ty<'tcx>,
    ) -> EncodingResult<Box<dyn SnapshotBuilder<'tcx> + 'tcx>> {
        Ok(match kind {
            SnapshotKind::Memory => box MemSnapshotDomain::encode(self.encoder(), ty)? as Box<dyn SnapshotBuilder>,
            SnapshotKind::Value => box ValueSnapshotDomain::encode(self.encoder(), ty)? as Box<dyn SnapshotBuilder>,
        })
    }
}
