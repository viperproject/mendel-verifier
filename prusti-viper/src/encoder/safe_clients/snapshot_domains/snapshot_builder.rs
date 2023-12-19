// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prelude::encoding_structs::scalars::encode_scalar;

use crate::encoder::safe_clients::prelude::*;

pub trait SnapshotBuilder<'tcx> {
    /// Get the memory snapshot constructor function of MIR types with just one variant (non-enums).
    fn constructor_function(&self) -> EncodingResult<vir::DomainFunc>;

    /// Get the content of the memory snapshot of a primitive type
    fn primitive_field_function(&self) -> EncodingResult<vir::DomainFunc>;

    /// Get the content of the memory snapshot of a raw pointer or reference
    fn target_address_function(&self) -> EncodingResult<vir::DomainFunc>;

    /// Get the content of the memory snapshot of a reference
    fn target_snapshot_function(&self) -> EncodingResult<vir::DomainFunc>;

    /// Get the content of the memory snapshot of a unsafe cell
    fn content_address_function(&self) -> EncodingResult<vir::DomainFunc>;

    fn adt_constructor_function(&self, variant: Option<abi::VariantIdx>) -> EncodingResult<vir::DomainFunc>;
    fn adt_field_function(&self, variant: Option<abi::VariantIdx>, field: mir::Field) -> EncodingResult<vir::DomainFunc>;
    fn discriminant_function(&self) -> EncodingResult<vir::DomainFunc>;

    /// Build the snapshot of a MIR constant.
    fn constant_snapshot(&self, tcx: ty::TyCtxt<'tcx>, constant: mir::Constant<'tcx>) -> EncodingResult<vir::Expr> {
        let value = constant.literal.eval(tcx, ty::ParamEnv::empty());
        Ok(match constant.literal {
            mir::ConstantKind::Val(value, ty) => {
                match value {
                    mir::interpret::ConstValue::Scalar(scalar) => {
                        let encoded_scalar = encode_scalar(tcx, ty, scalar)?;
                        self.constructor_function()?.apply1(encoded_scalar)
                    }
                    mir::interpret::ConstValue::ZeroSized => {
                        self.constructor_function()?.apply0()
                    }
                    unsupported => {
                        error_unsupported!("unsupported constant value {unsupported:?}");
                    }
                }
            }
            mir::ConstantKind::Ty(constant) => {
                match constant.kind() {
                    ty::ConstKind::Value(constant_value) => {
                        if let Some(scalar) = constant_value.try_to_scalar() {
                            let encoded_scalar = encode_scalar(tcx, constant.ty(), scalar)?;
                            self.constructor_function()?.apply1(encoded_scalar)
                        } else {
                            error_unsupported!("unsupported constant value {constant_value:?}");
                        }
                    }
                    unsupported => {
                        error_unsupported!("unsupported constant {unsupported:?}");
                    }
                }
            }
            mir::ConstantKind::Unevaluated(_, _) => {
                error_unsupported!("unsupported unevaluated constant {value:?}");
            }
        })
    }
}
