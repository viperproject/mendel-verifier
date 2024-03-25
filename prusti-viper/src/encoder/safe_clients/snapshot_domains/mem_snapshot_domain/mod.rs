// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod from_layout;
mod adt;
use std::rc::Rc;

use super::snapshot_builder::SnapshotBuilder;
use crate::encoder::safe_clients::prelude::*;
pub use adt::*;
use from_layout::*;

pub(super) const DOMAIN_NAME_PREFIX: &str = "MemorySnapshot";
pub(super) const CONSTRUCTOR_NAME_PREFIX: &str = "new_memory_snap";
pub(super) const FIELD_NAME_PREFIX: &str = "get_memory_field";

/// Name of the constructor for non-enum types.
pub(super) fn constructor_function_name(ty_name: &str, variant_component: &str) -> String {
    format!("{CONSTRUCTOR_NAME_PREFIX}{variant_component}_of_{ty_name}")
}

/// Name of the destructor for non-enum types.
pub(super) fn field_function_name(ty_name: &str, field_name: &str) -> String {
    format!("{FIELD_NAME_PREFIX}_{field_name}_of_{ty_name}")
}

pub fn mem_snapshot_domain_name<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<String> {
    let ty_name = types::encode_type_name(encoder, ty)?;
    Ok(format!("{DOMAIN_NAME_PREFIX}${ty_name}"))
}

pub fn mem_snapshot_domain_type<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Type> {
    Ok(vir::Type::domain(mem_snapshot_domain_name(encoder, ty)?))
}

pub fn build_mem_snapshot_domain<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Domain> {
    debug!("build_mem_snapshot_domain({:?})", ty);
    let layout = type_layout::build_layout(encoder, ty)?;
    build_mem_snapshot_domain_from_layout(encoder, ty, layout)
}

pub struct MemSnapshotDomain<'tcx> {
    ty: ty::Ty<'tcx>,
    pub(in super::super) domain: Rc<vir::Domain>,
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> MemSnapshotDomain<'tcx> {
    /// Returns the domain encoding a memory snapshot of the given type.
    pub fn encode<'v>(
        encoder: &Encoder<'v, 'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<MemSnapshotDomain<'tcx>> {
        let domain = encoder.encode_builtin_domain(BuiltinDomainKind::MemorySnapshot(ty))?;
        Ok(Self::new(domain, ty, encoder.env().tcx()))
    }

    /// Wrap the generic domain encoding of a memory snapshot. Acts like a downcast.
    pub fn new(
        domain: Rc<vir::Domain>,
        ty: ty::Ty<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> MemSnapshotDomain<'tcx> {
        debug_assert!(domain.name.starts_with(DOMAIN_NAME_PREFIX));
        MemSnapshotDomain { ty, domain, tcx }
    }

    /// Private helper method to get a function from the domain.
    pub(super) fn get_domain_function(
        &self,
        name: &str,
        index: usize,
        prefix: &str,
    ) -> EncodingResult<vir::DomainFunc> {
        let Some(func) = self.domain.functions.get(index) else {
            error_internal!(
                "cannot find function for {} in domain of type {:?}:\n{:#?}",
                name, self.ty, self.domain.functions,
            );
        };
        debug_assert!(func.name.starts_with(prefix));
        Ok(func.clone())
    }
}

impl<'tcx> SnapshotBuilder<'tcx> for MemSnapshotDomain<'tcx> {
    /// Get the memory snapshot constructor function of MIR types with just one variant (non-enums).
    fn constructor_function(&self) -> EncodingResult<vir::DomainFunc> {
        if self.ty.is_enum() {
            error_internal!("expected non-enum type; got {:?}", self.ty);
        };

        self.get_domain_function("constructor", 0, CONSTRUCTOR_NAME_PREFIX)
    }

    /// Get the content of the memory snapshot of a primitive type
    fn primitive_field_function(&self) -> EncodingResult<vir::DomainFunc> {
        if !self.ty.is_primitive_ty() {
            error_internal!("expected primitive type; got {:?}", self.ty);
        };

        self.get_domain_function("primitive field", 1, FIELD_NAME_PREFIX)
    }

    /// Get the content of the memory snapshot of a raw pointer or reference
    fn target_address_function(&self) -> EncodingResult<vir::DomainFunc> {
        if !matches!(self.ty.kind(), ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..)) {
            error_internal!("expected reference or raw pointer type; got {:?}", self.ty);
        };

        self.get_domain_function("target address", 1, FIELD_NAME_PREFIX)
    }

    /// Get the content of the memory snapshot of a reference
    fn target_snapshot_function(&self) -> EncodingResult<vir::DomainFunc> {
        let ty::TyKind::Ref(..) = self.ty.kind() else {
            error_internal!("expected reference type; got {:?}", self.ty);
        };

        self.get_domain_function("dereference", 2, FIELD_NAME_PREFIX)
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

    fn adt_constructor_function(
        &self,
        variant: Option<abi::VariantIdx>,
    ) -> EncodingResult<vir::DomainFunc> {
        self.impl_adt_constructor_function(variant)
    }

    fn adt_field_function(
        &self,
        variant: Option<abi::VariantIdx>,
        field: mir::Field,
    ) -> EncodingResult<vir::DomainFunc> {
        self.impl_adt_field_function(variant, field)
    }

    fn discriminant_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.impl_discriminant_function()
    }
}
