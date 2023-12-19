// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod from_layout;
mod adt;
use std::rc::Rc;

use from_layout::*;
pub use adt::*;
use prelude::types::snapshot_might_contain_references;
use crate::encoder::safe_clients::prelude::*;
use super::snapshot_builder::SnapshotBuilder;

pub(super) const DOMAIN_NAME_PREFIX: &str = "ValueSnapshot";
pub(super) const CONSTRUCTOR_NAME_PREFIX: &str = "new_value_snap";
pub(super) const FIELD_NAME_PREFIX: &str = "get_value_field";
pub(super) const CONVERSION_NAME_PREFIX: &str = "convert";

/// Name of the constructor for non-enum types.
pub(super) fn constructor_function_name(ty_name: &str, variant_component: &str) -> String {
    format!("{CONSTRUCTOR_NAME_PREFIX}{variant_component}_of_{ty_name}")
}

/// Name of the destructor for non-enum types.
pub(super) fn field_function_name(ty_name: &str, field_name: &str) -> String {
    format!("{FIELD_NAME_PREFIX}_{field_name}_of_{ty_name}")
}

pub(super) fn conversion_from_memory_function_name(ty_name: &str) -> String {
    format!("{CONVERSION_NAME_PREFIX}_from_memory_of_{ty_name}")
}

pub(super) fn conversion_to_memory_function_name(ty_name: &str) -> String {
    format!("{CONVERSION_NAME_PREFIX}_to_memory_of_{ty_name}")
}

pub fn value_snapshot_domain_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> EncodingResult<String> {
    let ty_name = types::encode_type_name(encoder, ty)?;
    Ok(format!("{DOMAIN_NAME_PREFIX}${ty_name}"))
}

pub fn value_snapshot_domain_type<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Type> {
    Ok(vir::Type::domain(value_snapshot_domain_name(encoder, ty)?))
}

pub fn build_value_snapshot_domain<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Domain> {
    debug!("build_value_snapshot_domain({:?})", ty);
    let layout = type_layout::build_layout(encoder, ty)?;
    build_value_snapshot_domain_from_layout(encoder, ty, layout)
}

pub struct ValueSnapshotDomain<'tcx> {
    ty: ty::Ty<'tcx>,
    domain: Rc<vir::Domain>,
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> ValueSnapshotDomain<'tcx> {
    /// Returns the domain encoding a value snapshot of the given type.
    pub fn encode<'v>(encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> EncodingResult<ValueSnapshotDomain<'tcx>> {
        let domain = encoder.encode_builtin_domain(BuiltinDomainKind::ValueSnapshot(ty))?;
        Ok(Self::new(domain, ty, encoder.env().tcx()))
    }

    /// Wrap the generic domain encoding of a value snapshot. Acts like a downcast.
    pub fn new(domain: Rc<vir::Domain>, ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> ValueSnapshotDomain<'tcx> {
        debug_assert!(domain.name.starts_with(DOMAIN_NAME_PREFIX));
        ValueSnapshotDomain {
            ty,
            domain,
            tcx,
        }
    }

    /// Private helper method to get a function from the domain.
    pub(super) fn get_domain_function(&self, name: &str, index: usize, prefix: &str) -> EncodingResult<vir::DomainFunc> {
        let Some(func) = self.domain.functions.get(index) else {
            error_internal!(
                "cannot find function for {} in domain of type {:?}:\n{:#?}",
                name, self.ty, self.domain.functions,
            );
        };
        debug_assert!(func.name.starts_with(prefix));
        Ok(func.clone())
    }

    fn count_constructors_and_getters(&self) -> EncodingResult<usize> {
        Ok(match self.ty.kind() {
            _ if types::is_opaque_type(self.tcx, self.ty) => {
                // no constructors and no getters
                0
            }
            ty::TyKind::Tuple(elements) => {
                // constructor, then field getters
                1 + elements.len()
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
                debug_assert!(adt_def.variants().len() == 1);
                // constructor, then field getters
                1 + adt_def.variants().iter().map(|v| v.fields.len()).sum::<usize>()
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                // constructors of the variants, then discriminant, then field getters
                let num_getters: usize = adt_def.variants().iter().map(|v| v.fields.len()).sum();
                adt_def.variants().len() + 1 + num_getters
            }
            _ if self.ty.is_primitive_ty() || self.ty.is_unsafe_ptr() || self.ty.is_region_ptr() => {
                // constructor, then field getter
                2
            }
            _ => {
                // no constructor and no getters
                0
            }
        })
    }

    /// Returns the function to convert a memory snapshot to a value snapshot.
    pub fn conversion_from_memory_function(&self) -> EncodingResult<vir::DomainFunc> {
        let fn_index = self.count_constructors_and_getters()?;
        if snapshot_might_contain_references(self.tcx, self.ty) {
            debug_assert_eq!(
                self.domain.functions.len(), fn_index + 1,
                "Type {:?} has unexpected functions {:#?}", self.ty, self.domain.functions,
            );
        } else {
            debug_assert_eq!(
                self.domain.functions.len(), fn_index + 2,
                "Type {:?} has unexpected functions {:#?}", self.ty, self.domain.functions,
            );
        }
        self.get_domain_function("convert from memory", fn_index, CONVERSION_NAME_PREFIX)
    }

    /// Returns the function to convert a value snapshot to a memory snapshot.
    pub fn conversion_to_memory_function(&self) -> EncodingResult<vir::DomainFunc> {
        let fn_index = self.count_constructors_and_getters()?;
        if snapshot_might_contain_references(self.tcx, self.ty) {
            error_internal!(
                "value snapshot cannot be converted to memory snapshot for type {:?}, \
                because a type instance might contain references", self.ty,
            );
        }
        debug_assert!(self.domain.functions.len() == fn_index + 2);
        self.get_domain_function("convert to memory", fn_index + 1, CONVERSION_NAME_PREFIX)
    }
}

impl<'tcx> SnapshotBuilder<'tcx> for ValueSnapshotDomain<'tcx> {
    /// Get the value snapshot constructor function of MIR types with just one variant (non-enums).
    fn constructor_function(&self) -> EncodingResult<vir::DomainFunc> {
        if self.ty.is_enum() {
            error_internal!("expected non-enum type; got {:?}", self.ty);
        };

        self.get_domain_function("constructor", 0, CONSTRUCTOR_NAME_PREFIX)
    }

    /// Get the content of the value snapshot of a primitive type
    fn primitive_field_function(&self) -> EncodingResult<vir::DomainFunc> {
        if !self.ty.is_primitive_ty() {
            error_internal!("expected primitive type; got {:?}", self.ty);
        };

        self.get_domain_function("primitive field", 1, FIELD_NAME_PREFIX)
    }

    /// Get the content of the memory snapshot of a raw pointer
    fn target_address_function(&self) -> EncodingResult<vir::DomainFunc> {
        if !matches!(self.ty.kind(), ty::TyKind::RawPtr(..)) {
            error_internal!("expected raw pointer type; got {:?}", self.ty);
        };

        self.get_domain_function("target address", 1, FIELD_NAME_PREFIX)
    }

    /// Get the content of the value snapshot of a reference
    fn target_snapshot_function(&self) -> EncodingResult<vir::DomainFunc> {
        let ty::TyKind::Ref(..) = self.ty.kind() else {
            error_internal!("expected reference type; got {:?}", self.ty);
        };

        self.get_domain_function("dereference", 1, FIELD_NAME_PREFIX)
    }

    /// Get the content of the memory snapshot of a unsafe cell
    fn content_address_function(&self) -> EncodingResult<vir::DomainFunc> {
        let ty::TyKind::Adt(adt_def, ..) = self.ty.kind() else {
            error_internal!("expected unsafe cell type; got {:?}", self.ty);
        };
        if !adt_def.is_unsafe_cell() {
            error_internal!("expected unsafe cell type; got {:?}", self.ty);
        }

        self.get_domain_function("content address", 1, FIELD_NAME_PREFIX)
    }

    fn adt_constructor_function(&self, variant: Option<abi::VariantIdx>) -> EncodingResult<vir::DomainFunc> {
        self.impl_adt_constructor_function(variant)
    }

    fn adt_field_function(&self, variant: Option<abi::VariantIdx>, field: mir::Field) -> EncodingResult<vir::DomainFunc> {
        self.impl_adt_field_function(variant, field)
    }

    fn discriminant_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.impl_discriminant_function()
    }
}
