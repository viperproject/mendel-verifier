// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prelude::pure_encoder::MirInterpreter;

use crate::encoder::{errors::PanicCause, safe_clients::prelude::*};

pub trait WithMir<'v, 'tcx: 'v>: WithDefId<'v, 'tcx> + WithLocalTy<'v, 'tcx> {
    fn mir(&self) -> &mir::Body<'tcx>;

    fn impl_get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.mir().local_decls[local].ty
    }

    fn get_local_span(&self, local: mir::Local) -> Span {
        self.mir().local_decls[local].source_info.span
    }

    fn get_rvalue_ty(&self, rvalue: &mir::Rvalue<'tcx>) -> ty::Ty<'tcx> {
        rvalue.ty(self.mir(), self.tcx())
    }

    fn get_span_of_location(&self, location: mir::Location) -> Span {
        self.mir().source_info(location).span
    }

    fn get_span_of_basic_block(&self, bbi: mir::BasicBlock) -> Span {
        let bb_data = &self.mir().basic_blocks[bbi];
        bb_data.terminator().source_info.span
    }

    /// Return the cause of a call to `begin_panic`
    fn encode_panic_cause(&self, span: Span) -> PanicCause {
        crate::encoder::mir_encoder::MirEncoder::new(self.encoder(), self.mir(), self.def_id())
            .encode_panic_cause(span)
    }

    // Translates a MIR body to a MirExpr.
    fn interpret_body(&self) -> SpannedEncodingResult<MirExpr<'tcx>> {
        let mir_interpreter = MirInterpreter::new(self.mir(), self.tcx());
        let mut mir_expr = mir_interpreter.encode_body()?;
        Ok(mir_expr)
    }

    /// Translated an expression `expr` at `final_loc` in the context at the beginning of `initial_bb`.
    fn backward_interpret_expr(
        &self,
        final_expr: MirExpr<'tcx>,
        initial_bb: mir::BasicBlock,
        final_loc: mir::Location,
    ) -> SpannedEncodingResult<MirExpr<'tcx>> {
        let mir_interpreter = MirInterpreter::new(self.mir(), self.tcx());
        let mut mir_expr =
            mir_interpreter.encode_point_to_point(final_expr, initial_bb, final_loc)?;
        mir_expr.normalize();
        Ok(mir_expr)
    }
}
