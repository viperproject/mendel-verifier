// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use type_layout::*;

/// Encodes a generic domain
/// The returned domain has the following functions, in order:
/// * A constructor for each variant.
/// * A discriminant, if the type is an enum.
/// * A destructor (aka getter) for each field, in the order of the variants.
pub(super) fn build_mem_snapshot_domain_from_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>, layout: TypeLayout<'tcx>
) -> EncodingResult<vir::Domain> {
    trace!("build_mem_snapshot_domain_from_layout {ty:?} with {} variants", layout.variants.len());
    let tcx = encoder.env().tcx();
    debug_assert!(types::is_opaque_type(tcx, ty) || ty.is_enum() || layout.variants.len() <= 1); // the never type has zero variants
    let ty_name = types::encode_type_name(encoder, ty)?;
    let domain_name = mem_snapshot_domain::mem_snapshot_domain_name(encoder, ty)?;
    let mem_snapshot_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(ty))?;
    let version_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)?;

    // Build constructors
    let mut constructors = vec![];
    for variant in layout.variants.iter() {
        let variant_component = if ty.is_enum() {
            format!("_v${}", variant.name)
        } else {
            "".to_string()
        };
        constructors.push(vir::DomainFunc::new(
            &domain_name,
            mem_snapshot_domain::constructor_function_name(&ty_name, &variant_component),
            variant.fields.iter().map(|f| vir::LocalVar::new(&f.name, f.mem_snapshot_ty.clone())).collect(),
            mem_snapshot_type.clone(),
        ));
    }

    // Build discriminant
    let mut discriminant = vec![];
    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        discriminant.push(vir::DomainFunc::new(
            &domain_name,
            mem_snapshot_domain::field_function_name(&ty_name, "discriminant"),
            vec![ vir_local!(snap: {mem_snapshot_type.clone()}) ],
            vir::Type::Int,
        ));
    }

    // Build destructors
    let mut destructors = vec![];
    for variant in layout.variants.iter() {
        let mut variant_destructors = vec![];
        for field in variant.fields.iter() {
            if field.is_visible {
                variant_destructors.push(vir::DomainFunc::new(
                    &domain_name,
                    mem_snapshot_domain::field_function_name(&ty_name, &field.name),
                    vec![ vir_local!(snap: {mem_snapshot_type.clone()}) ],
                    field.mem_snapshot_ty.clone(),
                ));
            } else {
                variant_destructors.push(vir::DomainFunc::new(
                    &domain_name,
                    // Ugly patch to disallow mentioning private fields in specifications
                    format!("{}_ERROR_field_is_not_visible", mem_snapshot_domain::field_function_name(&ty_name, &field.name)),
                    vec![ vir_local!(snap: {mem_snapshot_type.clone()}) ],
                    field.mem_snapshot_ty.clone(),
                ));
            }
        }
        destructors.push(variant_destructors);
    }

    // Build discriminant axioms
    let mut discriminant_axioms = vec![];
    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        // Define all the possible values of the discriminant
        let discriminant_destructor = &discriminant[0];
        let self_var = vir_local!(self: {mem_snapshot_type.clone()});
        let discriminant_value = discriminant_destructor.apply1(self_var.clone());
        if !layout.variants.is_empty() {
            discriminant_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                "Definition of all possible values of the discriminant",
                format!("memory_snapshot_valid_discriminants_of_{ty_name}"),
                vir::Expr::forall(
                    vec![self_var],
                    vec![ vir::Trigger::new(vec![discriminant_value.clone()]) ],
                    layout.variants.iter().map(|variant|
                        vir::Expr::eq_cmp(discriminant_value.clone(), variant.discriminant.clone())
                    ).disjoin(),
                ),
            ));
        }

        // Define the discriminant of each variant
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            let fields: Vec<_> = variant.fields.iter().map(|f|
                vir::LocalVar::new(format!("f${}", f.name), f.mem_snapshot_ty.clone())
            ).collect();
            let construction = constructors[variant_idx].clone()
                .apply(fields.iter().cloned().map(vir::Expr::from).collect());

            // Body of the axiom
            let mut body = vir::Expr::eq_cmp(
                discriminant_destructor.apply1(construction.clone()),
                variant.discriminant.clone(),
            );
            // Add quantified variables
            if !fields.is_empty() {
                body = vir::Expr::forall(
                    fields.clone(),
                    vec![ vir::Trigger::new(vec![construction.clone()]) ],
                    body,
                );
            }
            discriminant_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Definition of discriminant of variant {}", variant.name),
                format!("memory_snapshot_discriminant_of_{ty_name}_variant${variant_idx}"),
                body,
            ));
        }
    }

    // Define existence of the constructors
    let mut existence_axioms = vec![];
    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        let self_var = vir_local!(self: {mem_snapshot_type});
        let discriminant_value = discriminant[0].apply1(self_var.clone());
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            if variant.has_non_visible_fields() {
                // This is a rough approximation to model that snapshots stop at private
                // fields of types with an unsafe implementation.
                // This is slightly incomplete when considering types with both public
                // and private fields, but it's a rare case.
                continue;
            }

            let fields: Vec<_> = variant.fields.iter().enumerate().map(|(field_idx, _)|
                destructors[variant_idx][field_idx].apply1(self_var.clone())
            ).collect();
            let mut triggers = vec![
                vir::Trigger::new(vec![discriminant_value.clone()]),
            ];
            for field in &fields {
                triggers.push(vir::Trigger::new(vec![field.clone()]));
            }
            let construction = constructors[variant_idx].apply(fields);
            existence_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Definition of the existence of the constructor of variant {}", variant.name),
                format!("memory_snapshot_existence_of_{ty_name}_variant${variant_idx}"),
                vir::Expr::forall(
                    vec![self_var.clone()],
                    triggers,
                    vir::Expr::implies(
                        vir::Expr::eq_cmp(discriminant_value.clone(), variant.discriminant.clone()),
                        vir::Expr::eq_cmp(
                            self_var.clone().into(),
                            construction,
                        )
                    )
                ),
            ));
        }
    } else {
        let self_var = vir_local!(self: {mem_snapshot_type});
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            debug_assert_eq!(variant_idx, 0);
            if variant.has_non_visible_fields() {
                // This is a rough approximation to model that snapshots stop at private
                // fields of types with an unsafe implementation.
                // This is slightly incomplete when considering types with both public
                // and private fields, but it's a rare case.
                continue;
            }

            let fields: Vec<_> = variant.fields.iter().enumerate().map(|(field_idx, _)|
                destructors[variant_idx][field_idx].apply1(self_var.clone())
            ).collect();
            let mut triggers = vec![];
            for field in &fields {
                triggers.push(vir::Trigger::new(vec![field.clone()]));
            }
            let construction = constructors[variant_idx].apply(fields);
            existence_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Definition of the existence of the constructor of variant {}", variant.name),
                format!("memory_snapshot_existence_of_{ty_name}_variant${variant_idx}"),
                vir::Expr::forall(
                    vec![self_var.clone()],
                    triggers,
                    vir::Expr::eq_cmp(
                        self_var.clone().into(),
                        construction,
                    )
                ),
            ));
        }
    }

    // Build destructor axioms
    let mut destructor_axioms = vec![];
    for (variant_idx, variant) in layout.variants.iter().enumerate() {
        if variant.fields.is_empty() {
            continue;
        }
        if variant.has_non_visible_fields() {
            // This is a rough approximation to model that snapshots stop at private
            // fields of types with an unsafe implementation.
            // This is slightly incomplete when considering types with both public
            // and private fields, but it's a rare case.
            continue;
        }

        let fields: Vec<_> = variant.fields.iter().map(|f|
            vir::LocalVar::new(format!("f${}", f.name), f.mem_snapshot_ty.clone())
        ).collect();
        let constructor = &constructors[variant_idx];
        let construction = constructor.clone()
            .apply(fields.iter().cloned().map(vir::Expr::from).collect());
        for (field_idx, field) in variant.fields.iter().enumerate() {
            let field_destructor = &destructors[variant_idx][field_idx];
            let field_var = &fields[field_idx];
            destructor_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Definition of destructor, field {}", field.name),
                format!("definition_of_{ty_name}_variant${variant_idx}_field${field_idx}"),
                vir::Expr::forall(
                    fields.clone(),
                    vec![ vir::Trigger::new(vec![construction.clone()]) ],
                    vir::Expr::eq_cmp(
                        field_destructor.apply1(construction.clone()),
                        field_var.into(),
                    ),
                )
            ));
        }
    }

    Ok(vir::Domain {
        name: domain_name,
        functions: vec![constructors, discriminant, destructors.concat()].concat(),
        axioms: vec![discriminant_axioms, existence_axioms, destructor_axioms].concat(),
        type_vars: vec![],
    })
}
