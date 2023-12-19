// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir::pure::PureEncodingContext;
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::safe_clients::procedure_encoder::*;

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    /// Encodes the assertion (i.e. loop invariant, prusti assert/assume) in a specification block.
    pub(super) fn encode_bool_assertion(&self, spec_block: mir::BasicBlock, version: Version) -> SpannedEncodingResult<vir::Expr> {
        // Identify closure aggregate assign (the invariant body)
        let closure_assigns: Vec<_> = self.mir.basic_blocks[spec_block]
            .statements
            .iter()
            .enumerate()
            .filter_map(|(loc, stmt)| {
                if let mir::StatementKind::Assign(box (
                    lhs,
                    mir::Rvalue::Aggregate(
                        box mir::AggregateKind::Closure(
                            cl_def_id,
                            cl_substs
                        ),
                        ref cl_args
                    ),
                )) = stmt.kind {
                    Some((loc, lhs, cl_def_id, cl_substs, cl_args))
                } else {
                    None
                }
            })
            .collect();

        // Extract relevant data
        // again there should only be one such assignment because the invariant
        // spec block should consist *only* of a closure aggregate assign with
        // its upvars initialised before
        assert_eq!(closure_assigns.len(), 1);
        let (cl_stmt_index, cl_lhs, cl_def_id, cl_substs, cl_args) = closure_assigns[0];
        let inv_loc = mir::Location {
            block: spec_block,
            statement_index: cl_stmt_index,
        };
        let inv_span = self.get_span_of_location(inv_loc);

        // Compute the MirExpr of the body of the closure
        let cl_mir = self.env().body.get_closure_body(
            cl_def_id,
            cl_substs,
            self.def_id(),
        );
        let dummy_args_snapshot = [SnapshotExpr::new_memory(false.into())];
        let dummy_args_address = [None];
        let closure_encoder = AssertionEncoder::new(
            self.encoder,
            cl_def_id.to_def_id(),
            self.def_id(),
            cl_substs,
            cl_mir.clone(),
            // TODO: Define a simpler MirEncoder that doesn't need all these dummy arguments.
            &dummy_args_snapshot,
            &dummy_args_address,
            None,
            None,
            // Encode panics as calls to functions with a `false` precondition.
            PureEncodingContext::Code,
        );
        let mut inv_mir_expr = closure_encoder.interpret_body()
            .with_default_span(inv_span)?;
        let inv_ty = inv_mir_expr.ty(&cl_mir.local_decls, self.tcx()).ty;
        debug_assert!(inv_ty.is_bool());

        // Prepare the captured variables of the closure
        let mut cl_args_mir_expr = Vec::with_capacity(cl_args.len());
        for cl_arg in cl_args {
            let mir_expr = RvalueExpr::from_operand(cl_arg).with_default_span(inv_span)?.into();
            let mir_expr = self.backward_interpret_expr(mir_expr, spec_block, inv_loc)
                .with_default_span(inv_span)?;
            cl_args_mir_expr.push(mir_expr);
        }

        // Replace the captured variables
        inv_mir_expr.replace_places(&|place| {
            debug_assert_eq!(place.local.index(), 1);
            let remaining_proj = place.projection.iter().skip(2).collect();
            let field_elem = place.projection.get(1);
            let Some(mir::PlaceElem::Field(field, _)) = field_elem else {
                error_internal!("unexpected projection {field_elem:?}");
            };
            Ok(Some(RvalueExpr::Projections {
                base: box cl_args_mir_expr[field.index()].clone(),
                projections: remaining_proj,
            }.into()))
        }).with_default_span(inv_span)?;
        inv_mir_expr.normalize();

        // Encode the expression, using the pre memory version for the encoding of old(..)
        // and encoding panics with calls functions with a `false` precondition.
        let snapshot_expr = self.fixed_version_encoder(version)
            .encode_mir_expr_snapshot(&inv_mir_expr, GhostOrExec::Ghost)
            .with_default_span(inv_span)?;

        let pos = self.register_span(inv_span);
        self.encode_snapshot_primitive_value(snapshot_expr, inv_ty)
            .with_default_span(inv_span)
            .map(|e| e.set_default_pos(pos))
    }
}
