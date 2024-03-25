// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    mir::{
        contracts::{ContractsEncoderInterface, ProcedureContractMirDef},
        pure::PureEncodingContext,
    },
    safe_clients::prelude::*,
};

/// Used to encode the contract (i.e. pre/postcondition) of a bodyless item (e.g. external items).
pub struct BodylessEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The item containing the expression to convert
    def_id: DefId,
    substs: ty::SubstsRef<'tcx>,
    /// The signature of the function to be encoded.
    sig: ty::PolyFnSig<'tcx>,
    /// The contract of the function to be encoded.
    contract: ProcedureContractMirDef<'tcx>,
    /// The encoding of the snapshot of the locals of the function.
    encoded_locals: &'p [SnapshotExpr],
    /// The encoding of the address of the locals of the function.
    encoded_locals_address: &'p [Option<vir::Expr>],
    /// The encoding of the memory version of the function.
    encoded_version: Option<vir::LocalVar>,
    /// The encoder of old expressions.
    old_encoder: Option<Box<BodylessEncoder<'p, 'v, 'tcx>>>,
    /// The def_id of the function that calls the function to be encoded.
    pure_encoding_context: PureEncodingContext,
}

impl<'p, 'v: 'p, 'tcx: 'v> BodylessEncoder<'p, 'v, 'tcx> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        def_id: DefId,
        caller_def_id: DefId,
        substs: ty::SubstsRef<'tcx>,
        encoded_locals: &'p [SnapshotExpr],
        encoded_locals_address: &'p [Option<vir::Expr>],
        encoded_version: Option<vir::LocalVar>,
        old_encoder: Option<Box<BodylessEncoder<'p, 'v, 'tcx>>>,
    ) -> EncodingResult<Self> {
        let sig = encoder
            .env()
            .query
            .get_fn_sig_resolved(def_id, substs, caller_def_id);
        let contract = encoder.get_mir_procedure_contract_for_def(def_id, substs)?;
        debug_assert_eq!(
            encoded_locals.len(),
            sig.inputs_and_output().skip_binder().len()
        );
        Ok(BodylessEncoder {
            encoder,
            def_id,
            substs,
            sig,
            contract,
            encoded_locals,
            encoded_locals_address,
            encoded_version,
            old_encoder,
            pure_encoding_context: PureEncodingContext::Assertion,
        })
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithEncoder<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn encoder(&self) -> &Encoder<'v, 'tcx> {
        self.encoder
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithDefId<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn substs(&self) -> ty::SubstsRef<'tcx> {
        self.substs
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> DefIdEncoder<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithLocalTy<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.impl_get_local_ty(local)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithSig<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn sig(&self) -> ty::PolyFnSig<'tcx> {
        self.sig
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> PlaceEncoder<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn encode_local_snapshot(&self, local: mir::Local) -> SpannedEncodingResult<SnapshotExpr> {
        // Return the client-provided expressions
        Ok(self.encoded_locals[local.index()].clone())
    }

    fn encode_local_address(&self, local: mir::Local) -> SpannedEncodingResult<Option<vir::Expr>> {
        // Return the client-provided addresses
        Ok(self.encoded_locals_address[local.index()].clone())
    }

    fn encode_version(&self) -> EncodingResult<Option<vir::LocalVar>> {
        Ok(self.encoded_version.clone())
    }

    fn encode_promoted_mir_expr_snapshot(
        &self,
        mir_expr: &MirExpr<'tcx>,
    ) -> EncodingResult<SnapshotExpr> {
        error_internal!("promoted MIR expressions are not supported in bodyless items")
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldPlaceEncoder<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn old_place_encoder(&self) -> EncodingResult<&Self> {
        // TODO: Return self instead of None, so that old(..) in a precondition has no effect.
        Ok(self
            .old_encoder
            .as_ref()
            .map(|e| e.as_ref())
            .unwrap_or(self))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ContractEncoder<'v, 'tcx> for BodylessEncoder<'p, 'v, 'tcx> {
    fn contract(&self) -> &ProcedureContractMirDef<'tcx> {
        &self.contract
    }
}
