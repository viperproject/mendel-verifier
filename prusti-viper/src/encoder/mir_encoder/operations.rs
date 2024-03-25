// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use crate::{
    encoder::{
        errors::{
            EncodingError, EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult,
            WithSpan,
        },
        Encoder,
    },
    error_incorrect, error_internal, error_unsupported,
};
pub use log::{debug, info, trace};
pub use prusti_common::{config, vir_expr, vir_local, vir_stmt, vir_type};
pub use prusti_rustc_interface::{
    middle::{mir, ty},
    span::Span,
};
pub use vir_crate::polymorphic as vir;

/// Encode a binary operation given VIR expressions representing primitive Viper values.
pub fn encode_bin_op_expr(
    op: mir::BinOp,
    left: vir::Expr,
    right: vir::Expr,
    ty: ty::Ty<'_>,
) -> EncodingResult<vir::Expr> {
    let is_bool = ty.kind() == &ty::TyKind::Bool;
    let is_signed = matches!(ty.kind(), ty::TyKind::Int(_));
    Ok(match op {
        mir::BinOp::Eq => vir::Expr::eq_cmp(left, right),
        mir::BinOp::Ne => vir::Expr::ne_cmp(left, right),
        mir::BinOp::Gt => vir::Expr::gt_cmp(left, right),
        mir::BinOp::Ge => vir::Expr::ge_cmp(left, right),
        mir::BinOp::Lt => vir::Expr::lt_cmp(left, right),
        mir::BinOp::Le => vir::Expr::le_cmp(left, right),
        mir::BinOp::Add => vir::Expr::add(left, right),
        mir::BinOp::Sub => vir::Expr::sub(left, right),
        mir::BinOp::Rem => vir::Expr::rem(left, right),
        mir::BinOp::Div => vir::Expr::div(left, right),
        mir::BinOp::Mul => vir::Expr::mul(left, right),
        mir::BinOp::BitAnd if is_bool => vir::Expr::and(left, right),
        mir::BinOp::BitOr if is_bool => vir::Expr::or(left, right),
        mir::BinOp::BitXor if is_bool => vir::Expr::xor(left, right),
        mir::BinOp::BitAnd | mir::BinOp::BitOr | mir::BinOp::BitXor
            if !config::encode_bitvectors() =>
        {
            error_unsupported!(
                "bitwise operations on non-boolean types are experimental and disabled by \
                default; use `encode_bitvectors` to enable"
            );
        }
        unsupported_op if !config::encode_bitvectors() => {
            error_unsupported!(
                "support for operation '{:?}' is experimental and disabled by default; use \
                `encode_bitvectors` to enable it",
                unsupported_op
            );
        }
        mir::BinOp::BitAnd => vir::Expr::bin_op(vir::BinaryOpKind::BitAnd, left, right),
        mir::BinOp::BitOr => vir::Expr::bin_op(vir::BinaryOpKind::BitOr, left, right),
        mir::BinOp::BitXor => vir::Expr::bin_op(vir::BinaryOpKind::BitXor, left, right),
        mir::BinOp::Shl => vir::Expr::bin_op(vir::BinaryOpKind::Shl, left, right),
        // https://doc.rust-lang.org/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators
        // Arithmetic right shift on signed integer types, logical right shift on unsigned integer types.
        mir::BinOp::Shr if is_signed => vir::Expr::bin_op(vir::BinaryOpKind::AShr, left, right),
        mir::BinOp::Shr => vir::Expr::bin_op(vir::BinaryOpKind::LShr, left, right),
        mir::BinOp::Offset => {
            error_unsupported!("operation '{:?}' is not supported", op);
        }
    })
}

/// Encode a unary operation given a VIR expression representing a primitive Viper value.
pub fn encode_unary_op_expr(op: mir::UnOp, expr: vir::Expr) -> vir::Expr {
    match op {
        mir::UnOp::Not => vir::Expr::not(expr),
        mir::UnOp::Neg => vir::Expr::minus(expr),
    }
}

/// Encode the check of a binary operation given VIR expressions representing primitive Viper
/// values.
pub fn encode_bin_op_check(
    op: mir::BinOp,
    left: vir::Expr,
    right: vir::Expr,
    ty: ty::Ty<'_>,
) -> EncodingResult<vir::Expr> {
    if !op.is_checkable() || !config::check_overflows() {
        Ok(false.into())
    } else {
        let result = encode_bin_op_expr(op, left, right.clone(), ty)?;

        Ok(match op {
            mir::BinOp::Add | mir::BinOp::Mul | mir::BinOp::Sub => match ty.kind() {
                // Unsigned
                ty::TyKind::Uint(ty::UintTy::U8) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::u8::MIN.into()),
                    vir::Expr::gt_cmp(result, std::u8::MAX.into()),
                ),
                ty::TyKind::Uint(ty::UintTy::U16) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::u16::MIN.into()),
                    vir::Expr::gt_cmp(result, std::u16::MAX.into()),
                ),
                ty::TyKind::Uint(ty::UintTy::U32) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::u32::MIN.into()),
                    vir::Expr::gt_cmp(result, std::u32::MAX.into()),
                ),
                ty::TyKind::Uint(ty::UintTy::U64) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::u64::MIN.into()),
                    vir::Expr::gt_cmp(result, std::u64::MAX.into()),
                ),
                ty::TyKind::Uint(ty::UintTy::U128) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::u128::MIN.into()),
                    vir::Expr::gt_cmp(result, std::u128::MAX.into()),
                ),
                ty::TyKind::Uint(ty::UintTy::Usize) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::usize::MIN.into()),
                    vir::Expr::gt_cmp(result, std::usize::MAX.into()),
                ),
                // Signed
                ty::TyKind::Int(ty::IntTy::I8) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::i8::MIN.into()),
                    vir::Expr::gt_cmp(result, std::i8::MAX.into()),
                ),
                ty::TyKind::Int(ty::IntTy::I16) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::i16::MIN.into()),
                    vir::Expr::gt_cmp(result, std::i16::MAX.into()),
                ),
                ty::TyKind::Int(ty::IntTy::I32) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::i32::MIN.into()),
                    vir::Expr::gt_cmp(result, std::i32::MAX.into()),
                ),
                ty::TyKind::Int(ty::IntTy::I64) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::i64::MIN.into()),
                    vir::Expr::gt_cmp(result, std::i64::MAX.into()),
                ),
                ty::TyKind::Int(ty::IntTy::I128) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::i128::MIN.into()),
                    vir::Expr::gt_cmp(result, std::i128::MAX.into()),
                ),
                ty::TyKind::Int(ty::IntTy::Isize) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::isize::MIN.into()),
                    vir::Expr::gt_cmp(result, std::isize::MAX.into()),
                ),
                //Floats
                ty::TyKind::Float(ty::FloatTy::F32) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::f32::MIN.into()),
                    vir::Expr::gt_cmp(result, std::f32::MAX.into()),
                ),
                ty::TyKind::Float(ty::FloatTy::F64) => vir::Expr::or(
                    vir::Expr::lt_cmp(result.clone(), std::f64::MIN.into()),
                    vir::Expr::gt_cmp(result, std::f64::MAX.into()),
                ),
                _ => {
                    error_unsupported!(
                        "overflow checks are unsupported for operation '{:?}' on type '{:?}'",
                        op,
                        ty,
                    );
                }
            },

            mir::BinOp::Shl | mir::BinOp::Shr => {
                let size: u32 = match ty.kind() {
                    ty::TyKind::Uint(ty::UintTy::U8) => 8,
                    ty::TyKind::Uint(ty::UintTy::U16) => 16,
                    ty::TyKind::Uint(ty::UintTy::U32) => 32,
                    ty::TyKind::Uint(ty::UintTy::U64) => 64,
                    ty::TyKind::Uint(ty::UintTy::U128) => 128,
                    ty::TyKind::Uint(ty::UintTy::Usize) => {
                        error_unsupported!("unknown size of usize for the overflow check");
                    }
                    ty::TyKind::Int(ty::IntTy::I8) => 8,
                    ty::TyKind::Int(ty::IntTy::I16) => 16,
                    ty::TyKind::Int(ty::IntTy::I32) => 32,
                    ty::TyKind::Int(ty::IntTy::I64) => 64,
                    ty::TyKind::Int(ty::IntTy::I128) => 128,
                    ty::TyKind::Int(ty::IntTy::Isize) => {
                        error_unsupported!("unknown size of isize for the overflow check");
                    }
                    _ => {
                        error_unsupported!(
                            "overflow checks are unsupported for operation '{:?}' on type '{:?}'",
                            op,
                            ty,
                        );
                    }
                };
                vir::Expr::or(
                    vir::Expr::lt_cmp(right.clone(), 0.into()),
                    vir::Expr::ge_cmp(right, size.into()),
                )
            }

            _ => {
                error_unsupported!("overflow checks are unsupported for operation '{:?}'", op);
            }
        })
    }
}
