// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::pure::PureEncodingContext;

/// Used to encode an assertion (i.e. pre/postcondition, loop invariant) to a `vir::Expr`.
pub struct AssertionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The MIR containing the expression to convert
    def_id: DefId,
    substs: ty::SubstsRef<'tcx>,
    mir: MirBody<'tcx>,
    /// The encoding of the snapshot of the arguments of the function.
    encoded_args: &'p [SnapshotExpr],
    /// The encoding of the address of the arguments of the function.
    encoded_args_address: &'p [Option<vir::Expr>],
    /// The encoding of the version argument of the function.
    encoded_version: Option<vir::LocalVar>,
    /// The encoder of old expressions.
    old_encoder: Option<Box<AssertionEncoder<'p, 'v, 'tcx>>>,
    pure_encoding_context: PureEncodingContext,
}

impl<'p, 'v: 'p, 'tcx: 'v> AssertionEncoder<'p, 'v, 'tcx> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        def_id: DefId,
        caller_def_id: DefId,
        substs: ty::SubstsRef<'tcx>,
        mir: MirBody<'tcx>,
        encoded_args: &'p [SnapshotExpr],
        encoded_args_address: &'p [Option<vir::Expr>],
        encoded_version: Option<vir::LocalVar>,
        old_encoder: Option<Box<AssertionEncoder<'p, 'v, 'tcx>>>,
        pure_encoding_context: PureEncodingContext,
    ) -> Self {
        debug_assert_eq!(encoded_args.len(), mir.args_iter().count());

        AssertionEncoder {
            encoder,
            def_id,
            substs,
            mir,
            encoded_args,
            encoded_args_address,
            encoded_version,
            old_encoder,
            pure_encoding_context,
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn encoder(&self) -> &Encoder<'v, 'tcx> {
        self.encoder
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithDefId<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn substs(&self) -> ty::SubstsRef<'tcx> {
        self.substs
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> DefIdEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithLocalTy<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.impl_get_local_ty(local)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithMir<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn mir(&self) -> &mir::Body<'tcx> {
        &self.mir
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> PlaceEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn encode_local_snapshot(&self, local: mir::Local) -> SpannedEncodingResult<SnapshotExpr> {
        if local == mir::RETURN_PLACE {
            error_internal!(self.span() =>
                "Cannot encode the return place as a snapshot when encoding an assertion"
            );
        }
        // Return the client-provided expressions
        Ok(self.encoded_args[local.index() - 1].clone())
    }

    fn encode_local_address(&self, local: mir::Local) -> SpannedEncodingResult<Option<vir::Expr>> {
        if local == mir::RETURN_PLACE {
            error_internal!(self.span() =>
                "Cannot encode the return place as a snapshot when encoding an assertion"
            );
        }
        Ok(self.encoded_args_address[local.index() - 1].clone())
    }

    fn encode_version(&self) -> EncodingResult<Option<vir::LocalVar>> {
        Ok(self.encoded_version.clone())
    }

    fn encode_promoted_mir_expr_snapshot(&self, mir_expr: &MirExpr<'tcx>) -> EncodingResult<SnapshotExpr> {
        self.encode_mir_expr_snapshot(mir_expr, GhostOrExec::Exec)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> MirExprEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
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

impl<'p, 'v: 'p, 'tcx: 'v> SubstsEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithOldMirExprEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn old_mir_expr_encoder(&self) -> EncodingResult<&Self> {
        // In preconditions old(..) has no effect
        Ok(self.old_encoder.as_ref().map(|e| e.as_ref()).unwrap_or(self))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> CallEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> PureEncoder<'v, 'tcx> for AssertionEncoder<'p, 'v, 'tcx> {
    fn pure_encoding_context(&self) -> PureEncodingContext {
        self.pure_encoding_context
    }
}
