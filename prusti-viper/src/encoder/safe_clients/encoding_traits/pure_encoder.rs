// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::high::builtin_functions::HighBuiltinFunctionEncoderInterface;
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::pure::PureEncodingContext;

/// Trait used to encode the body of a pure item (functions, triggers, predicates, assertions...).
pub(crate) trait PureEncoder<'v, 'tcx: 'v>: MirExprEncoder<'v, 'tcx> + CallEncoder<'v, 'tcx> {
    fn pure_encoding_context(&self) -> PureEncodingContext;

    fn impl_encode_failing_assertion(&self, msg: &mir::AssertMessage<'tcx>, domain_kind: BuiltinDomainKind<'tcx>, span: Span) -> SpannedEncodingResult<vir::Expr> {
        Ok(match self.pure_encoding_context() {
            PureEncodingContext::Code => {
                // We are encoding a pure function, so all failures should be unreachable.
                let error_ctxt = if let mir::AssertKind::BoundsCheck { .. } = msg {
                    ErrorCtxt::BoundsCheckAssert
                } else {
                    let assert_msg = msg.description().to_string();
                    ErrorCtxt::PureFunctionAssertTerminator(assert_msg)
                };
                let pos = self.encoder().error_manager().register_error(
                    span,
                    error_ctxt,
                    self.def_id(),
                );
                self.encode_requires_false_call(pos, domain_kind).with_span(span)?
            }
            PureEncodingContext::Assertion => {
                // We are encoding an assertion, all failures should be equivalent to false.
                let value_expr: vir::Expr = false.into();
                match domain_kind {
                    BuiltinDomainKind::Address(ty) => {
                        debug_assert!(ty.is_bool());
                        value_expr
                    }
                    BuiltinDomainKind::MemorySnapshot(ty) => {
                        debug_assert!(ty.is_bool());
                        MemSnapshotDomain::encode(self.encoder(), ty).with_default_span(span)?
                            .constructor_function().with_default_span(span)?
                            .apply1(value_expr)
                    }
                    BuiltinDomainKind::ValueSnapshot(ty) => {
                        debug_assert!(ty.is_bool());
                        ValueSnapshotDomain::encode(self.encoder(), ty).with_default_span(span)?
                            .constructor_function().with_default_span(span)?
                            .apply1(value_expr)
                    }
                    _ => error_internal!(span => "Unexpected domain kind {domain_kind:?}"),
                }
            }
            PureEncodingContext::Trigger => {
                // We are encoding a trigger, so all panic branches must be stripped.
                error_internal!(span =>
                    "assertions should be ignored when encoding triggers"
                )
            }
        })
    }

    fn encode_body(&self, context: GhostOrExec) -> SpannedEncodingResult<vir::Expr> {
        let mut mir_expr = self.interpret_body()?;
        if self.pure_encoding_context() == PureEncodingContext::Trigger {
            strip_assertions(&mut mir_expr);
            mir_expr.normalize();
        }
        debug!("Encoding pure MIR body of {:?}", self.def_id());
        let body_ty = mir_expr.ty(self.mir(), self.tcx()).ty;
        let encoded_body = self.encode_mir_expr_snapshot(&mir_expr, context).with_default_span(self.span())?;

        // TODO: Use a rich pure encoding context to know how to encode assertions.
        if self.is_pure_stable(None, self.def_id(), self.substs()) {
            self.convert_to_value_snapshot(encoded_body, body_ty)
        } else {
            self.convert_to_memory_snapshot(encoded_body, body_ty)
        }.with_default_span(self.span())
    }

    /// Encodes a call to a function with a false precondition.
    fn encode_requires_false_call(&self, pos: vir::Position, domain_kind: BuiltinDomainKind<'tcx>) -> EncodingResult<vir::Expr> {
        let domain_ty = self.encoder().encode_builtin_domain_type(domain_kind)?;
        let (function_name, type_arguments) = self.encoder().encode_builtin_function_use(
            BuiltinFunctionKind::Unreachable(domain_ty.clone())
        );
        Ok(vir::Expr::func_app(
            function_name,
            type_arguments,
            vec![],
            vec![],
            domain_ty,
            pos,
        ))
    }
}

/// Removes all assertions from the given expression.
fn strip_assertions(expr: &mut MirExpr<'_>) {
    if let MirExpr::Assert { box then, .. } = expr {
        *expr = then.clone();
    }
    expr.visit_subexpr_mut::<()>(&|e| { strip_assertions(e); Ok(()) }).unwrap();
}
