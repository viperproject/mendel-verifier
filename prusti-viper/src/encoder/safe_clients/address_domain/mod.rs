// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod from_layout;
use std::rc::Rc;

use crate::encoder::safe_clients::prelude::*;
use from_layout::*;

pub(super) const DOMAIN_NAME_PREFIX: &str = "Address";
pub(super) const FIELD_NAME_PREFIX: &str = "get_addr";
pub(super) const BASE_NAME_PREFIX: &str = "get_base";
pub(super) const DEREF_NAME_PREFIX: &str = "deref";
pub(super) const ID_NAME_PREFIX: &str = "id";

/// Name of the dereference function from addresses to snapshots.
pub(super) fn deref_function_name(ty_name: &str) -> String {
    format!("{DEREF_NAME_PREFIX}_{ty_name}")
}

/// Name of the id function from addresses to identifier.
pub(super) fn id_function_name(ty_name: &str) -> String {
    format!("{ID_NAME_PREFIX}_{ty_name}")
}

/// Name of the function that gives the offset from a base to a field.
pub(super) fn field_function_name(ty_name: &str, field_name: &str) -> String {
    format!("{FIELD_NAME_PREFIX}_{field_name}_of_{ty_name}")
}

/// Name of the function that gives the offset from a field to its base.
pub(super) fn base_function_name(ty_name: &str, field_name: &str) -> String {
    format!("{BASE_NAME_PREFIX}_{field_name}_of_{ty_name}")
}

pub fn address_domain_name<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<String> {
    let ty_name = types::encode_type_name(encoder, ty)?;
    Ok(format!("{DOMAIN_NAME_PREFIX}${ty_name}"))
}

pub fn address_domain_type<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Type> {
    Ok(vir::Type::domain(address_domain_name(encoder, ty)?))
}

pub fn build_address_domain<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Domain> {
    debug!("build_address_domain({ty:?})");
    let layout = type_layout::build_layout(encoder, ty)?;
    build_address_domain_from_layout(encoder, ty, layout)
}

pub struct AddressDomain<'tcx> {
    ty: ty::Ty<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    domain: Rc<vir::Domain>,
}

impl<'tcx> AddressDomain<'tcx> {
    /// Returns the domain encoding an address of the given type.
    pub fn encode(
        encoder: &Encoder<'_, 'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<AddressDomain<'tcx>> {
        let domain = encoder.encode_builtin_domain(BuiltinDomainKind::Address(ty))?;
        Ok(Self::new(domain, ty, encoder.env().tcx()))
    }

    /// Wrap the generic domain encoding of an address. Acts like a downcast.
    pub fn new(
        domain: Rc<vir::Domain>,
        ty: ty::Ty<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> AddressDomain<'tcx> {
        debug_assert!(domain.name.starts_with(DOMAIN_NAME_PREFIX));
        AddressDomain { ty, domain, tcx }
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
                "cannot find function for {name} in domain of type {:?}:\n{:#?}",
                self.ty, self.domain.functions,
            );
        };
        debug_assert!(func.name.starts_with(prefix));
        Ok(func.clone())
    }

    /// Get the function to dereference an address (given a memory version) to a snapshot.
    pub fn deref_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.get_domain_function("deref", 0, DEREF_NAME_PREFIX)
    }

    /// Get the function to convert an instance (given by address and memory version) to an identifier.
    pub fn id_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.get_domain_function("id", 1, ID_NAME_PREFIX)
    }

    /// Get the function modeling the address of the content of an unsafe cell.
    pub fn content_address_function(&self) -> EncodingResult<vir::DomainFunc> {
        let ty::TyKind::Adt(adt_def, ..) = self.ty.kind() else {
            error_internal!("expected unsafe cell type; got {:?}", self.ty);
        };
        if !adt_def.is_unsafe_cell() {
            error_internal!("expected unsafe cell type; got {:?}", self.ty);
        }

        self.get_domain_function("content address", 2, FIELD_NAME_PREFIX)
    }

    /// Get the function modeling the address of a field of an ADT.
    pub fn adt_field_address_function(
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
                // deref, then fields
                2 + field_idx
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
                debug_assert!(variant.iter().all(|v| v.index() == 0));
                debug_assert!(adt_def.variants().len() == 1);
                // deref, then fields
                2 + field_idx
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                let variant_idx = variant.map(|v| v.index()).unwrap_or(0);
                let fields_before: usize = adt_def
                    .variants()
                    .iter()
                    .take(variant_idx)
                    .map(|v| v.fields.len())
                    .sum();
                // deref, then fields
                2 + fields_before + field_idx
            }
            _ => error_internal!("expected tuple or ADT type; got {:?}", self.ty),
        };

        let debug_name = format!("field {field:?}, variant {variant:?}");
        self.get_domain_function(&debug_name, destructor_idx, FIELD_NAME_PREFIX)
    }
}
