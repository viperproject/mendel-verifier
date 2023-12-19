// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;
use crate::encoder::mir::pure::PureEncodingContext;
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::contracts::{ProcedureContractMirDef, ContractsEncoderInterface};
use super::local_address_encoder::LocalAddressEncoder;

/// Used to encode the snapshot of expressions at a fixed memory version.
pub struct FixedVersionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The MIR containing the expression to convert
    def_id: DefId,
    mir: &'p mir::Body<'tcx>,
    substs: ty::SubstsRef<'tcx>,
    contract: ProcedureContractMirDef<'tcx>,
    version: vir::LocalVar,
    /// The encoder of old expressions.
    old_encoder: Option<Rc<FixedVersionEncoder<'p, 'v, 'tcx>>>,
}

impl<'p, 'v: 'p, 'tcx: 'v> FixedVersionEncoder<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        def_id: DefId,
        mir: &'p mir::Body<'tcx>,
        substs: ty::SubstsRef<'tcx>,
        version: vir::LocalVar,
        old_encoder: Option<Rc<FixedVersionEncoder<'p, 'v, 'tcx>>>
    ) -> SpannedEncodingResult<Self> {
        let contract = encoder.get_mir_procedure_contract_for_def(def_id, substs)
            .with_span(mir.span)?;
        Ok(FixedVersionEncoder {
            encoder,
            def_id,
            mir,
            substs,
            contract,
            version,
            old_encoder,
        })
    }

    pub fn version(&self) -> &vir::LocalVar {
        &self.version
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn encoder(&self) -> &Encoder<'v, 'tcx> {
        self.encoder
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithDefId<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn substs(&self) -> ty::SubstsRef<'tcx> {
        self.substs
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> DefIdEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithLocalTy<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.mir.local_decls[local].ty
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithMir<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn mir(&self) -> &mir::Body<'tcx> {
        self.mir
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> LocalAddressEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> PlaceEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    /// Snapshot of a local at the given memory version.
    fn encode_local_snapshot(&self, local: mir::Local) -> SpannedEncodingResult<SnapshotExpr> {
        let local_addr = self.encode_local_address_var(local)?;
        let local_span = self.get_local_span(local);
        let local_domain = self.encode_local_address_domain(local)?;
        let version: vir::Expr = self.version().clone().into();
        let expr = local_domain.deref_function().with_span(local_span)?.apply2(local_addr, version);
        Ok(SnapshotExpr::new_memory(expr))
    }

    fn encode_local_address(&self, local: mir::Local) -> SpannedEncodingResult<Option<vir::Expr>> {
        Ok(Some(self.encode_local_address_var(local)?.into()))
    }

    fn encode_version(&self) -> EncodingResult<Option<vir::LocalVar>> {
        Ok(Some(self.version().clone()))
    }

    fn encode_promoted_mir_expr_snapshot(&self, mir_expr: &MirExpr<'tcx>) -> EncodingResult<SnapshotExpr> {
        self.encode_mir_expr_snapshot(mir_expr, GhostOrExec::Exec)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> MirExprEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn encode_failing_assertion(&self, msg: &mir::AssertMessage<'tcx>, domain_kind: BuiltinDomainKind<'tcx>, span: Span) -> SpannedEncodingResult<vir::Expr> {
        self.impl_encode_failing_assertion(msg, domain_kind, span)
    }

    fn encode_pure_call_snapshot(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[MirExpr<'tcx>],
        version: Option<vir::LocalVar>,
        result_ty: ty::Ty<'tcx>,
        span: Span,
        context: GhostOrExec,
    ) -> SpannedEncodingResult<SnapshotExpr> {
        self.impl_encode_pure_function_call(called_def_id, call_substs, args, version, result_ty, span, context)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> SubstsEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldPlaceEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn old_place_encoder(&self) -> EncodingResult<&Self> {
        // In preconditions old(..) has no effect
        Ok(self.old_encoder.as_ref().map(|e| e.as_ref()).unwrap_or(self))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldMirExprEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn old_mir_expr_encoder(&self) -> EncodingResult<&Self> {
        // In preconditions old(..) has no effect
        Ok(self.old_encoder.as_ref().map(|e| e.as_ref()).unwrap_or(self))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> CallEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> ContractEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn contract(&self) -> &ProcedureContractMirDef<'tcx> {
        &self.contract
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> PureEncoder<'v, 'tcx> for FixedVersionEncoder<'p, 'v, 'tcx> {
    fn pure_encoding_context(&self) -> PureEncodingContext {
        // Encode panics as pure functions with a `false` precondition.
        PureEncodingContext::Code
    }
}
