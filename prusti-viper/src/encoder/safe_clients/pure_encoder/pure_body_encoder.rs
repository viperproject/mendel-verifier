// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir::contracts::{ProcedureContractMirDef, ContractsEncoderInterface};
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::pure::PureEncodingContext;
use super::CommonPureEncoder;

/// Used to encode a pure item (i.e. pure function, method or predicate) to a `vir::Function`.
pub struct PureBodyEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The MIR containing the expression to convert
    def_id: DefId,
    caller_def_id: DefId,
    mir: MirBody<'tcx>,
    /// Type substitutions applied to the MIR (if any) and the signature.
    substs: ty::SubstsRef<'tcx>,
    /// Signature of the function to be encoded.
    sig: ty::PolyFnSig<'tcx>,
    /// The contract of the function to be encoded.
    pub(super) contract: ProcedureContractMirDef<'tcx>,
    /// The def_id of the function that calls the function to be encoded.
    pure_encoding_context: PureEncodingContext,
}

impl<'p, 'v: 'p, 'tcx: 'v> PureBodyEncoder<'p, 'v, 'tcx> {
    pub(crate) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        def_id: DefId,
        caller_def_id: DefId,
        substs: ty::SubstsRef<'tcx>,
        mir: MirBody<'tcx>,
        pure_encoding_context: PureEncodingContext,
    ) -> SpannedEncodingResult<Self> {
        let sig = encoder.env().query.get_fn_sig_resolved(def_id, substs, caller_def_id);
        debug_assert_eq!(sig.inputs().iter().count(), mir.args_iter().count());
        let contract = encoder.get_mir_procedure_contract_for_def(def_id, substs)
            .with_span(mir.span)?;

        Ok(PureBodyEncoder {
            encoder,
            def_id,
            caller_def_id,
            mir,
            substs,
            sig,
            contract,
            pure_encoding_context,
        })
    }

    /// Encode either a pure function or a predicate
    pub fn encode_function(&mut self) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_name();
        debug!("Encode pure function {function_name}");
        let body_expr = self.encode_body(GhostOrExec::Exec)?;
        let pos = self.register_error(self.span(), ErrorCtxt::PureFunctionDefinition);
        debug!("Pure function {function_name} has been encoded with expr: {body_expr}");
        self.encode_function_given_body(Some(body_expr.set_default_pos(pos)))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn encoder(&self) -> &Encoder<'v, 'tcx> {
        self.encoder
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithDefId<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn substs(&self) -> ty::SubstsRef<'tcx> {
        self.substs
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> DefIdEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithLocalTy<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        <Self as WithMir>::impl_get_local_ty(self, local)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithMir<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn mir(&self) -> &mir::Body<'tcx> {
        &self.mir
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> PlaceEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn encode_version(&self) -> EncodingResult<Option<vir::LocalVar>> {
        self.default_version()
    }

    fn encode_local_snapshot(&self, local: mir::Local) -> SpannedEncodingResult<SnapshotExpr> {
        self.impl_encode_local_snapshot(local)
    }

    fn encode_local_address(&self, local: mir::Local) -> SpannedEncodingResult<Option<vir::Expr>> {
        Ok(None)
    }

    fn encode_promoted_mir_expr_snapshot(&self, mir_expr: &MirExpr<'tcx>) -> EncodingResult<SnapshotExpr> {
        self.encode_mir_expr_snapshot(mir_expr, GhostOrExec::Exec)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithSig<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn sig(&self) -> ty::PolyFnSig<'tcx> {
        self.sig
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> SubstsEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> ContractEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn contract(&self) -> &ProcedureContractMirDef<'tcx> {
        &self.contract
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> CommonPureEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn caller_def_id(&self) -> DefId {
        self.caller_def_id
    }

    fn get_local_span(&self, local: mir::Local) -> Span {
        <Self as WithMir>::get_local_span(self, local)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> MirExprEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn encode_failing_assertion(&self, msg: &mir::AssertMessage<'tcx>, domain_kind: BuiltinDomainKind<'tcx>, span: Span) -> SpannedEncodingResult<vir::Expr> {
        self.impl_encode_failing_assertion(msg, domain_kind, span)
    }

    fn encode_pure_call_snapshot(
        &self,
        called_def_id: DefId,
        call_substs: ty::SubstsRef<'tcx>,
        args: &[MirExpr<'tcx>],
        version: Option<vir::LocalVar>,
        return_ty: ty::Ty<'tcx>,
        span: Span,
        context: GhostOrExec,
    ) -> SpannedEncodingResult<SnapshotExpr> {
        self.impl_encode_pure_function_call(called_def_id, call_substs, args, version, return_ty, span, context)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldPlaceEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn old_place_encoder(&self) -> EncodingResult<&Self> {
        // In pure functions old(..) has no effect
        Ok(self)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldMirExprEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn old_mir_expr_encoder(&self) -> EncodingResult<&Self> {
        // In pure functions old(..) has no effect
        Ok(self)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> CallEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> PureEncoder<'v, 'tcx> for PureBodyEncoder<'p, 'v, 'tcx> {
    fn pure_encoding_context(&self) -> PureEncodingContext {
        self.pure_encoding_context
    }
}
