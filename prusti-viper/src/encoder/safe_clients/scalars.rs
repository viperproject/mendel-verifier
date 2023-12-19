// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

/// Build the VIR expression of a MIR scalar.
pub fn encode_scalar<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    scalar: mir::interpret::Scalar,
) -> EncodingResult<vir::Expr> {
    let expr = match ty.kind() {
        ty::TyKind::Bool => scalar.to_bool().unwrap().into(),
        ty::TyKind::Char => scalar.to_char().unwrap().into(),
        ty::TyKind::Int(ty::IntTy::I8) => scalar.to_i8().unwrap().into(),
        ty::TyKind::Int(ty::IntTy::I16) => scalar.to_i16().unwrap().into(),
        ty::TyKind::Int(ty::IntTy::I32) => scalar.to_i32().unwrap().into(),
        ty::TyKind::Int(ty::IntTy::I64) => scalar.to_i64().unwrap().into(),
        ty::TyKind::Int(ty::IntTy::I128) => scalar.to_i128().unwrap().into(),
        ty::TyKind::Int(ty::IntTy::Isize) => scalar.to_machine_isize(&tcx).unwrap().into(),
        ty::TyKind::Uint(ty::UintTy::U8) => scalar.to_u8().unwrap().into(),
        ty::TyKind::Uint(ty::UintTy::U16) => scalar.to_u16().unwrap().into(),
        ty::TyKind::Uint(ty::UintTy::U32) => scalar.to_u32().unwrap().into(),
        ty::TyKind::Uint(ty::UintTy::U64) => scalar.to_u64().unwrap().into(),
        ty::TyKind::Uint(ty::UintTy::U128) => scalar.to_u128().unwrap().into(),
        ty::TyKind::Uint(ty::UintTy::Usize) => scalar.to_machine_usize(&tcx).unwrap().into(),
        ty::TyKind::Float(ty::FloatTy::F32) => {
            let bits = scalar.to_u32().unwrap();
            vir::Expr::Const(vir::ConstExpr {
                value: vir::Const::Float(vir::FloatConst::F32(bits)),
                position: vir::Position::default(),
            })
        },
        ty::TyKind::Float(ty::FloatTy::F64) => {
            let bits = scalar.to_u64().unwrap();
            vir::Expr::Const(vir::ConstExpr {
                value: vir::Const::Float(vir::FloatConst::F64(bits)),
                position: vir::Position::default(),
            })
        }
        _ => {
            error_unsupported!("unsupported constant scalar type {:?}", ty.kind());
        }
    };
    Ok(expr)
}
