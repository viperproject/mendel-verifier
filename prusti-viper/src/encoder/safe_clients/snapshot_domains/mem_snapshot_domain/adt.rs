// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use mem_snapshot_domain::*;

// ADT getters
impl<'tcx> MemSnapshotDomain<'tcx> {
    pub(super) fn impl_adt_constructor_function(
        &self,
        variant: Option<abi::VariantIdx>,
    ) -> EncodingResult<vir::DomainFunc> {
        let constructor_idx = match self.ty.kind() {
            _ if types::is_opaque_type(self.tcx, self.ty) => {
                error_internal!("expected non-opaque type; got {:?}", self.ty);
            }
            ty::TyKind::Tuple(..) => {
                debug_assert!(variant.is_none());
                0
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell() => {
                error_internal!("expected tuple or ADT type; got {:?}", self.ty);
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() || adt_def.is_enum() => {
                variant.map(|v| v.index()).unwrap_or(0)
            }
            _ => error_internal!("expected tuple or ADT type; got {:?}", self.ty),
        };

        let debug_name = format!("constructor of variant {variant:?}");
        self.get_domain_function(&debug_name, constructor_idx, CONSTRUCTOR_NAME_PREFIX)
    }

    pub(super) fn impl_adt_field_function(
        &self,
        variant: Option<abi::VariantIdx>,
        field: mir::Field,
    ) -> EncodingResult<vir::DomainFunc> {
        trace!("adt_field_function {:?} {:?} {:?}", self.ty, variant, field);
        let field_idx = field.index();
        let destructor_idx = match self.ty.kind() {
            _ if types::is_opaque_type(self.tcx, self.ty) => {
                error_internal!("expected non-opaque type; got {:?}", self.ty);
            }
            ty::TyKind::Tuple(..) => {
                debug_assert!(variant.is_none());
                // constructor, then field getters
                1 + field_idx
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell() => {
                error_internal!("expected tuple or ADT type; got {:?}", self.ty);
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
                debug_assert!(variant.iter().all(|v| v.index() == 0));
                debug_assert!(adt_def.variants().len() == 1);
                // constructor, then field getters
                1 + field_idx
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                let variant_idx = variant.map(|v| v.index()).unwrap_or(0);
                let fields_before: usize = adt_def
                    .variants()
                    .iter()
                    .take(variant_idx)
                    .map(|v| v.fields.len())
                    .sum();
                // constructors of the variants, then discriminant, then field getters
                adt_def.variants().len() + 1 + fields_before + field_idx
            }
            _ => error_internal!("expected tuple or ADT type; got {:?}", self.ty),
        };

        let debug_name = format!("field {field:?}, variant {variant:?}");
        self.get_domain_function(&debug_name, destructor_idx, FIELD_NAME_PREFIX)
    }

    pub(super) fn impl_discriminant_function(&self) -> EncodingResult<vir::DomainFunc> {
        trace!("discriminant_function {:?}", self.ty);
        let destructor_idx = match self.ty.kind() {
            _ if types::is_opaque_type(self.tcx, self.ty) => {
                error_internal!("expected non-opaque type; got {:?}", self.ty);
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_enum() => adt_def.variants().len(),
            _ => error_internal!("expected enum type; got {:?}", self.ty),
        };

        self.get_domain_function("discriminant", destructor_idx, FIELD_NAME_PREFIX)
    }
}
