// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use address_domain::*;
use type_layout::*;

/// Encodes a generic domain
/// The returned domain has the following functions, in order:
/// * A constructor for each variant.
/// * A discriminant, if the type is an enum.
/// * A destructor (aka getter) for each field, in the order of the variants.
pub(super) fn build_address_domain_from_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
    layout: TypeLayout<'tcx>,
) -> EncodingResult<vir::Domain> {
    trace!(
        "build_address_domain_from_layout {ty:?} with {} variants",
        layout.variants.len()
    );
    debug_assert!(ty.is_enum() || layout.variants.len() <= 1); // the never type has zero variants
    let ty_name = types::encode_type_name(encoder, ty)?;
    let domain_name = address_domain_name(encoder, ty)?;
    let address_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(ty))?;
    let snapshot_type =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(ty))?;
    let version_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)?;

    let deref_function = vir::DomainFunc::new(
        &domain_name,
        deref_function_name(&ty_name),
        vec![
            vir::LocalVar::new("base", address_type.clone()),
            vir::LocalVar::new("version", version_type.clone()),
        ],
        snapshot_type,
    );

    let id_function = vir::DomainFunc::new(
        &domain_name,
        id_function_name(&ty_name),
        vec![
            vir::LocalVar::new("base", address_type.clone()),
            vir::LocalVar::new("version", version_type),
        ],
        vir::Type::Int,
    );

    // Build offset functions from the base address to the field addresses
    let mut base_to_fields = vec![];
    for (variant_idx, variant) in layout.variants.iter().enumerate() {
        let mut variant_base_to_fields = vec![];
        for (field_idx, field) in variant.fields.iter().enumerate() {
            if let Some(field_ty) = field.ty.as_ref().copied() {
                let field_address_type =
                    encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(field_ty))?;
                variant_base_to_fields.push(vir::DomainFunc::new(
                    &domain_name,
                    field_function_name(&ty_name, &field.name),
                    vec![vir::LocalVar::new("base", address_type.clone())],
                    field_address_type,
                ));
            } else {
                // Ugly, but it keeps function lookups by index easy
                variant_base_to_fields.push(vir::DomainFunc::new(
                    &domain_name,
                    format!(
                        "_dummy_base_to_field_of_{ty_name}_variant${variant_idx}_field${field_idx}"
                    ),
                    vec![],
                    vir::Type::Int,
                ));
            }
        }
        base_to_fields.push(variant_base_to_fields);
    }

    // Build offset functions from field addresses the base address
    let mut fields_to_base = vec![];
    for (variant_idx, variant) in layout.variants.iter().enumerate() {
        let mut variant_fields_to_base = vec![];
        for (field_idx, field) in variant.fields.iter().enumerate() {
            if let Some(field_ty) = field.ty.as_ref().copied() {
                let field_address_type =
                    encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(field_ty))?;
                variant_fields_to_base.push(vir::DomainFunc::new(
                    &domain_name,
                    base_function_name(&ty_name, &field.name),
                    vec![vir::LocalVar::new("field_addr", field_address_type)],
                    address_type.clone(),
                ));
            } else {
                // Ugly, but it keeps function lookups by index easy
                variant_fields_to_base.push(vir::DomainFunc::new(
                    &domain_name,
                    format!(
                        "_dummy_field_to_base_of_{ty_name}_variant${variant_idx}_field${field_idx}"
                    ),
                    vec![],
                    vir::Type::Int,
                ));
            }
        }
        fields_to_base.push(variant_fields_to_base);
    }

    // Axiom: The address of a field determines the address of the type
    let mut base_axioms = vec![];
    for (variant_idx, variant) in layout.variants.iter().enumerate() {
        let mut field_idx = 0;
        for (field_idx, field) in variant.fields.iter().enumerate() {
            if field.ty.is_some() {
                let base_addr = vir::LocalVar::new("base_addr", address_type.clone());
                let field_addr = base_to_fields[variant_idx][field_idx].apply1(base_addr.clone());
                let base_field_addr =
                    fields_to_base[variant_idx][field_idx].apply1(field_addr.clone());
                let body = vir_expr!(
                    forall [base_addr] :: { [field_addr] } :: ((local [base_addr]) == [base_field_addr])
                );
                base_axioms.push(vir::DomainAxiom::new(
                    &domain_name,
                    format!(
                        "The base address is determined by the address of field {}",
                        field.name,
                    ),
                    format!("base_of_field_of_{ty_name}_variant${variant_idx}_field${field_idx}"),
                    body,
                ));
            }
        }
    }

    Ok(vir::Domain {
        name: domain_name,
        functions: vec![
            vec![deref_function, id_function],
            base_to_fields.concat(),
            fields_to_base.concat(),
        ]
        .concat(),
        axioms: vec![base_axioms].concat(),
        type_vars: vec![],
    })
}
