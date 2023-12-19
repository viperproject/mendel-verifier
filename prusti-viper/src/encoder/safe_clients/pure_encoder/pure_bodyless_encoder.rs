// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir::contracts::{ProcedureContractMirDef, ContractsEncoderInterface};
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::pure::PureEncodingContext;
use super::CommonPureEncoder;

/// Used to encode a bodyless item (i.e. a trusted pure function) to a `vir::Function`.
pub struct PureBodylessEncoder<'p, 'v: 'p, 'tcx: 'v> {
    pub(super) encoder: &'p Encoder<'v, 'tcx>,
    /// The MIR containing the expression to convert
    pub(super) def_id: DefId,
    pub(super) caller_def_id: DefId,
    /// Type substitutions applied to the MIR (if any) and the signature.
    pub(super) substs: ty::SubstsRef<'tcx>,
    /// Signature of the function to be encoded.
    pub(super) sig: ty::PolyFnSig<'tcx>,
    /// The contract of the function to be encoded.
    pub(super) contract: ProcedureContractMirDef<'tcx>,
    /// The def_id of the function that calls the function to be encoded.
    pub(super) pure_encoding_context: PureEncodingContext,
}

impl<'p, 'v: 'p, 'tcx: 'v> PureBodylessEncoder<'p, 'v, 'tcx> {
    pub(crate) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        def_id: DefId,
        caller_def_id: DefId,
        substs: ty::SubstsRef<'tcx>,
        pure_encoding_context: PureEncodingContext,
    ) -> SpannedEncodingResult<Self> {
        let sig = encoder.env().query.get_fn_sig_resolved(def_id, substs, caller_def_id);
        let contract = encoder.get_mir_procedure_contract_for_def(def_id, substs)
            .with_span(encoder.env().tcx().def_span(def_id))?;
        Ok(PureBodylessEncoder {
            encoder,
            def_id,
            caller_def_id,
            substs,
            sig,
            contract,
            pure_encoding_context,
        })
    }

    pub fn encode_function(&self) -> SpannedEncodingResult<vir::Function> {
        debug!("Encode trusted (bodyless) pure function {}", self.encode_name());
        self.encode_function_given_body(None)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn encoder(&self) -> &Encoder<'v, 'tcx> {
        self.encoder
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithDefId<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn substs(&self) -> ty::SubstsRef<'tcx> {
        self.substs
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> DefIdEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithLocalTy<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.impl_get_local_ty(local)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithSig<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn sig(&self) -> ty::PolyFnSig<'tcx> {
        self.sig
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> PlaceEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
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
        error_internal!("promoted MIR expressions are not supported in bodyless items")
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldPlaceEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn old_place_encoder(&self) -> EncodingResult<&Self> {
        // In pure functions old(..) has no effect
        Ok(self)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ContractEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn contract(&self) -> &ProcedureContractMirDef<'tcx> {
        &self.contract
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> SubstsEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> CommonPureEncoder<'v, 'tcx> for PureBodylessEncoder<'p, 'v, 'tcx> {
    fn caller_def_id(&self) -> DefId {
        self.caller_def_id
    }

    fn get_local_span(&self, local: mir::Local) -> Span {
        // Can we do better than this without a MIR body?
        self.span()
    }
}
