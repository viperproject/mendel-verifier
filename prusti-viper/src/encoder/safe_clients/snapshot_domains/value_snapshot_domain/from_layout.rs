// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use prelude::types::{is_unsafe_cell, snapshot_might_contain_references};
use type_layout::*;

/// Encodes a generic domain
/// The returned domain has the following functions, in order:
/// * A constructor for each variant.
/// * A discriminant, if the type is an enum.
/// * A destructor (aka getter) for each field, in the order of the variants.
pub(super) fn build_value_snapshot_domain_from_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
    layout: TypeLayout<'tcx>,
) -> EncodingResult<vir::Domain> {
    trace!(
        "build_value_snapshot_domain_from_layout {ty:?} with {} variants",
        layout.variants.len()
    );
    let tcx = encoder.env().tcx();
    debug_assert!(types::is_opaque_type(tcx, ty) || ty.is_enum() || layout.variants.len() <= 1); // the never type has zero variants
    let ty_name = types::encode_type_name(encoder, ty)?;
    let domain_name = value_snapshot_domain::value_snapshot_domain_name(encoder, ty)?;
    let value_snapshot_type =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::ValueSnapshot(ty))?;
    let memory_snapshot_type =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(ty))?;
    let memory_snapshot_domain = MemSnapshotDomain::encode(encoder, ty)?;
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
            value_snapshot_domain::constructor_function_name(&ty_name, &variant_component),
            variant
                .value_fields()
                .map(|f| vir::LocalVar::new(&f.name, f.value_snapshot_ty().clone()))
                .collect(),
            value_snapshot_type.clone(),
        ));
    }

    // Build discriminant
    let mut discriminant = vec![];
    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        discriminant.push(vir::DomainFunc::new(
            &domain_name,
            value_snapshot_domain::field_function_name(&ty_name, "discriminant"),
            vec![vir_local!(snap: {value_snapshot_type.clone()})],
            vir::Type::Int,
        ));
    }

    // Build destructors
    let mut destructors = vec![];
    for variant in layout.variants.iter() {
        let mut variant_destructors = vec![];
        for field in variant.value_fields() {
            if field.is_visible {
                variant_destructors.push(vir::DomainFunc::new(
                    &domain_name,
                    value_snapshot_domain::field_function_name(&ty_name, &field.name),
                    vec![vir_local!(snap: {value_snapshot_type.clone()})],
                    field.value_snapshot_ty().clone(),
                ));
            } else {
                variant_destructors.push(vir::DomainFunc::new(
                    &domain_name,
                    // Ugly patch to disallow mentioning private fields in specifications
                    format!(
                        "{}_ERROR_field_is_not_visible",
                        value_snapshot_domain::field_function_name(&ty_name, &field.name)
                    ),
                    vec![vir_local!(snap: {value_snapshot_type.clone()})],
                    field.value_snapshot_ty().clone(),
                ));
            }
        }
        destructors.push(variant_destructors);
    }

    // Conversion functions
    let mut conversion_functions = vec![vir::DomainFunc::new(
        &domain_name,
        value_snapshot_domain::conversion_from_memory_function_name(&ty_name),
        vec![vir_local!(snap: {memory_snapshot_type.clone()})],
        value_snapshot_type.clone(),
    )];
    if !snapshot_might_contain_references(tcx, ty) {
        conversion_functions.push(vir::DomainFunc::new(
            &domain_name,
            value_snapshot_domain::conversion_to_memory_function_name(&ty_name),
            vec![vir_local!(snap: {value_snapshot_type.clone()})],
            memory_snapshot_type.clone(),
        ));
    }

    // Build discriminant axioms
    // (1) forall v ::
    //         { get_value_discr(v) }
    //         get_value_discr(v) == <value_1> || ... || get_value_discr(v) == <value_k>
    // (2) forall v_1...v_n ::
    //         { new_value_snap_of_T_variant<k>(v_1...v_n) }
    //         get_value_discr(new_value_snap_of_T_variant<k>(v_1...v_n)) == <k>
    let mut discriminant_axioms = vec![];
    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        // (1) Define all the possible values of the discriminant
        let discriminant_destructor = &discriminant[0];
        let self_var = vir_local!(self: {value_snapshot_type.clone()});
        let discriminant_value = discriminant_destructor.apply1(self_var.clone());
        if !layout.variants.is_empty() {
            discriminant_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                "Definition of all possible values of the discriminant",
                format!("value_snapshot_valid_discriminants_of_{ty_name}"),
                vir::Expr::forall(
                    // forall v ::
                    vec![self_var],
                    // { get_value_discr(v) }
                    vec![vir::Trigger::new(vec![discriminant_value.clone()])],
                    // get_value_discr(v) == <value_1> || ... || get_value_discr(v) == <value_k>
                    layout
                        .variants
                        .iter()
                        .map(|variant| {
                            vir::Expr::eq_cmp(
                                discriminant_value.clone(),
                                variant.discriminant.clone(),
                            )
                        })
                        .disjoin(),
                ),
            ));
        }

        // (2) Define the discriminant of each variant
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            if variant.has_non_visible_fields() {
                // This is a rough approximation to model that snapshots stop at private
                // fields of types with an unsafe implementation.
                // This is slightly incomplete when considering types with both public
                // and private fields, but it's a rare case.
                continue;
            }
            let fields: Vec<_> = variant
                .value_fields()
                .map(|f| vir::LocalVar::new(format!("f${}", f.name), f.value_snapshot_ty().clone()))
                .collect();
            let construction = constructors[variant_idx]
                .clone()
                .apply(fields.iter().cloned().map(vir::Expr::from).collect());

            // Boxy of the axiom
            let mut body = vir::Expr::eq_cmp(
                discriminant_destructor.apply1(construction.clone()),
                variant.discriminant.clone(),
            );
            // Add quantified variables
            if !fields.is_empty() {
                body = vir::Expr::forall(
                    // forall v_1...v_n ::
                    fields.clone(),
                    // { new_value_snap_of_T_variant<k>(v_1...v_n) }
                    vec![vir::Trigger::new(vec![construction.clone()])],
                    // get_value_discr(new_value_snap_of_T_variant<k>(v_1...v_n)) == <k>
                    body,
                );
            }
            discriminant_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Definition of discriminant of variant {}", variant.name),
                format!("value_snapshot_discriminant_of_{ty_name}_variant${variant_idx}"),
                body,
            ));
        }
    }

    // Define existence of the constructors
    // forall v ::
    //     { get_value_discr(v) } { get_value_field_1(v) } ...
    //     get_value_discr(v) == <value_1> ==>
    //         v == new_value_snap_of_T_variant<1>(get_value_field_1(v), ...)
    // or, if not enum:
    // forall v ::
    //     { get_value_field_1(v) } ...
    //     v == new_value_snap_of_T_variant<1>(get_value_field_1(v), ...)
    let mut existence_axioms = vec![];
    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        let self_var = vir_local!(self: {value_snapshot_type.clone()});
        let discriminant_value = discriminant[0].apply1(self_var.clone());
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            let fields: Vec<_> = variant
                .value_fields()
                .enumerate()
                .map(|(field_idx, _)| destructors[variant_idx][field_idx].apply1(self_var.clone()))
                .collect();
            let mut triggers = vec![
                // { get_value_discr(v) }
                vir::Trigger::new(vec![discriminant_value.clone()]),
            ];
            for field in &fields {
                // { get_value_field_1(v) }
                triggers.push(vir::Trigger::new(vec![field.clone()]));
            }
            let construction = constructors[variant_idx].apply(fields);
            existence_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!(
                    "Definition of the existence of the constructor of variant {}",
                    variant.name
                ),
                format!("value_snapshot_existence_of_{ty_name}_variant${variant_idx}"),
                vir::Expr::forall(
                    // forall v ::
                    vec![self_var.clone()],
                    // { get_value_discr(v) } { get_value_field_1(v) } ...
                    triggers,
                    // get_value_discr(v) == <value_1> ==>
                    //     v == new_value_snap_of_T_variant<1>(get_value_field_1(v), ...)
                    vir::Expr::implies(
                        vir::Expr::eq_cmp(discriminant_value.clone(), variant.discriminant.clone()),
                        vir::Expr::eq_cmp(self_var.clone().into(), construction),
                    ),
                ),
            ));
        }
    } else {
        let self_var = vir_local!(self: {value_snapshot_type.clone()});
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            debug_assert_eq!(variant_idx, 0);
            let fields: Vec<_> = variant
                .value_fields()
                .enumerate()
                .map(|(field_idx, _)| destructors[variant_idx][field_idx].apply1(self_var.clone()))
                .collect();
            let mut triggers = vec![];
            for field in &fields {
                // { get_value_field_1(v) }
                triggers.push(vir::Trigger::new(vec![field.clone()]));
            }
            let construction = constructors[variant_idx].apply(fields);
            existence_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!(
                    "Definition of the existence of the constructor of variant {}",
                    variant.name
                ),
                format!("value_snapshot_existence_of_{ty_name}_variant${variant_idx}"),
                vir::Expr::forall(
                    // forall v ::
                    vec![self_var.clone()],
                    // { get_value_field_1(v) } ...
                    triggers,
                    // v == new_value_snap_of_T_variant<1>(get_value_field_1(v), ...)
                    vir::Expr::eq_cmp(self_var.clone().into(), construction),
                ),
            ));
        }
    }

    // Build destructor axioms
    // forall v_1...v_n ::
    //     { new_value_snap_of_T(v_1...v_n) }
    //     get_value_field_<k>(new_value_snap_of_T(v_1...v_n)) == v_<k>
    let mut destructor_axioms = vec![];
    for (variant_idx, variant) in layout.variants.iter().enumerate() {
        if variant.value_fields().count() == 0 {
            continue;
        }
        if variant.has_non_visible_fields() {
            // This is a rough approximation to model that snapshots stop at private
            // fields of types with an unsafe implementation.
            // This is slightly incomplete when considering types with both public
            // and private fields, but it's a rare case.
            continue;
        }

        let fields: Vec<_> = variant
            .value_fields()
            .map(|f| vir::LocalVar::new(format!("f${}", f.name), f.value_snapshot_ty().clone()))
            .collect();
        let constructor = &constructors[variant_idx];
        let construction = constructor
            .clone()
            .apply(fields.iter().cloned().map(vir::Expr::from).collect());
        for (field_idx, field) in variant.value_fields().enumerate() {
            let field_destructor = &destructors[variant_idx][field_idx];
            let field_var = &fields[field_idx];
            destructor_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Definition of destructor, field {}", field.name),
                format!("value_snapshot_definition_of_{ty_name}_variant${variant_idx}_field${field_idx}"),
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

    // Build conversion axioms
    let mut conversion_axioms = vec![];
    let convert_field_to = |field_expr: vir::Expr,
                            value_field_ty: Option<ty::Ty<'tcx>>,
                            kind: SnapshotKind|
     -> EncodingResult<vir::Expr> {
        Ok(match (value_field_ty, ty.kind()) {
            _ if ty.is_primitive_ty() => field_expr,
            _ if is_unsafe_cell(ty) => field_expr,
            (Some(field_ty), _) | (_, &ty::TyKind::Ref(_, field_ty, _)) => {
                let field_value_domain = ValueSnapshotDomain::encode(encoder, field_ty)?;
                match kind {
                    SnapshotKind::Memory => field_value_domain.conversion_to_memory_function()?,
                    SnapshotKind::Value => field_value_domain.conversion_from_memory_function()?,
                }
                .apply1(field_expr)
            }
            (_, &ty::TyKind::RawPtr(_)) => field_expr,
            unexpected => unreachable!("{unexpected:?}"),
        })
    };
    {
        // Memory to value, constructor:
        // forall m_1...m_n ::
        //     { from_memory_T(new_memory_snap_of_T(m_1...m_n)) }
        //     if k < n:  { new_memory_snap_of_T(m_1...m_n), new_value_snap_of_T(from_memory_T1(m_1)...from_memory_Tk(m_k)) }
        //     if k == n: { new_value_snap_of_T(from_memory_T1(m_1)...from_memory_Tk(m_k)) }
        //     from_memory_T(new_memory_snap_of_T(m_1...m_n)) == new_value_snap_of_T(from_memory_T1(m_1)...from_memory_Tk(m_k))
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            if variant.has_non_visible_fields() {
                // This is a rough approximation to model that snapshots stop at private
                // fields of types with an unsafe implementation.
                // This is slightly incomplete when considering types with both public
                // and private fields, but it's a rare case.
                continue;
            }

            let lhs_memory_fields_vars: Vec<_> = variant
                .fields
                .iter()
                .map(|f| vir::LocalVar::new(format!("f${}", f.name), f.mem_snapshot_ty.clone()))
                .collect();
            let lhs_memory_fields: Vec<_> = lhs_memory_fields_vars
                .iter()
                .map(|f| vir::Expr::from(f.clone()))
                .collect();
            let rhs_memory_fields_vars: Vec<_> = variant
                .value_fields()
                .map(|f| vir::LocalVar::new(format!("f${}", f.name), f.mem_snapshot_ty.clone()))
                .collect();
            let rhs_value_fields: Vec<_> = variant
                .value_fields()
                .zip(rhs_memory_fields_vars.iter())
                .map(|(f, v)| convert_field_to(v.clone().into(), f.ty, SnapshotKind::Value))
                .collect::<Result<Vec<_>, _>>()?;
            let lhs_memory_snapshot = if ty.is_enum() {
                memory_snapshot_domain
                    .adt_constructor_function(Some(variant_idx.into()))?
                    .apply(lhs_memory_fields)
            } else {
                memory_snapshot_domain
                    .constructor_function()?
                    .apply(lhs_memory_fields)
            };
            let lhs_value_snapshot = conversion_functions[0].apply1(lhs_memory_snapshot.clone());
            let rhs_value_snapshot = if ty.is_enum() {
                constructors[variant_idx].apply(rhs_value_fields)
            } else {
                constructors[0].apply(rhs_value_fields)
            };

            // Body of the axiom
            let mut body = vir::Expr::eq_cmp(
                // from_memory_T(new_memory_snap_of_T(m_1...m_n))
                lhs_value_snapshot.clone(),
                // new_value_snap_of_T(from_memory_T1(m_1)...from_memory_Tk(m_k))
                rhs_value_snapshot.clone(),
            );
            // Add quantified variables
            if !lhs_memory_fields_vars.is_empty() {
                body = vir::Expr::forall(
                    // m_1...m_n
                    lhs_memory_fields_vars.clone(),
                    vec![
                        // { from_memory_T(new_memory_snap_of_T(m_1...m_n)) }
                        vir::Trigger::new(vec![lhs_value_snapshot]),
                        if rhs_memory_fields_vars.len() < lhs_memory_fields_vars.len() {
                            // { new_memory_snap_of_T(m_1...m_n), new_value_snap_of_T(from_memory_T1(m_1)...from_memory_Tk(m_k)) }
                            vir::Trigger::new(vec![lhs_memory_snapshot, rhs_value_snapshot.clone()])
                        } else {
                            // { new_value_snap_of_T(from_memory_T1(m_1)...from_memory_Tk(m_k)) }
                            vir::Trigger::new(vec![rhs_value_snapshot])
                        },
                    ],
                    body,
                );
            }
            conversion_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                "Definition of conversion between constructors",
                format!("conversion_memory_to_value_between_constructors_of_{ty_name}_variant${variant_idx}"),
                body,
            ));
        }
    }
    if !snapshot_might_contain_references(tcx, ty) {
        // Value to memory, constructor:
        // forall v_1...v_n ::
        //     { to_memory_T(new_value_snap_of_T(v_1...v_n)) }
        //     { new_memory_snap_of_T(to_memory_T1(v_1)...to_memory_Tn(v_n)) }
        //     to_memory_T(new_value_snap_of_T(v_1...v_n)) == new_memory_snap_of_T(to_memory_T1(v_1)...to_memory_Tn(v_n))
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            debug_assert_eq!(variant.fields.len(), variant.value_fields().count());
            if variant.has_non_visible_fields() {
                // This is a rough approximation to model that snapshots stop at private
                // fields of types with an unsafe implementation.
                // This is slightly incomplete when considering types with both public
                // and private fields, but it's a rare case.
                continue;
            }

            let value_fields_vars: Vec<_> = variant
                .fields
                .iter()
                .map(|f| vir::LocalVar::new(format!("v${}", f.name), f.value_snapshot_ty().clone()))
                .collect();
            let value_fields: Vec<_> = value_fields_vars
                .iter()
                .map(|f| vir::Expr::from(f.clone()))
                .collect();
            let memory_fields: Vec<_> = variant
                .fields
                .iter()
                .zip(value_fields.iter())
                .map(|(f, e)| convert_field_to(e.clone(), f.ty, SnapshotKind::Memory))
                .collect::<Result<Vec<_>, _>>()?;
            let rhs_memory_snapshot = if ty.is_enum() {
                memory_snapshot_domain
                    .adt_constructor_function(Some(variant_idx.into()))?
                    .apply(memory_fields)
            } else {
                memory_snapshot_domain
                    .constructor_function()?
                    .apply(memory_fields)
            };
            let lhs_value_snapshot = if ty.is_enum() {
                constructors[variant_idx].apply(value_fields)
            } else {
                constructors[0].apply(value_fields)
            };
            let lhs_memory_snapshot = conversion_functions[1].apply1(lhs_value_snapshot);

            // Body of the axiom
            let mut body = vir::Expr::eq_cmp(
                // to_memory_T(new_value_snap_of_T(v_1...v_n))
                lhs_memory_snapshot.clone(),
                // new_memory_snap_of_T(to_memory_T1(v_1)...to_memory_Tn(v_n))
                rhs_memory_snapshot.clone(),
            );
            // Add quantified variables
            if !value_fields_vars.is_empty() {
                body = vir::Expr::forall(
                    // v_1...v_n
                    value_fields_vars,
                    vec![
                        // { to_memory_T(new_value_snap_of_T(v_1...v_n)) }
                        vir::Trigger::new(vec![lhs_memory_snapshot]),
                        // { new_memory_snap_of_T(to_memory_T1(v_1)...to_memory_Tn(v_n)) }
                        vir::Trigger::new(vec![rhs_memory_snapshot]),
                    ],
                    body,
                );
            }
            conversion_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                "Definition of conversion between constructors",
                format!("conversion_value_to_memory_between_constructors_of_{ty_name}_variant${variant_idx}"),
                body
            ));
        }
    }
    if !snapshot_might_contain_references(tcx, ty) {
        // Value to memory to value:
        // forall v :: { from_memory(to_memory(v)) }  from_memory(to_memory(v)) == v
        let value_snapshot = vir::LocalVar::new("value_snapshot", value_snapshot_type);
        let memory_snapshot = conversion_functions[1].apply1(value_snapshot.clone());
        let lhs_value_snapshot = conversion_functions[0].apply1(memory_snapshot);
        let body = vir_expr!(
            // forall v ::
            forall [value_snapshot] ::
            // { from_memory(to_memory(v)) }
            { [lhs_value_snapshot] } ::
            // from_memory(to_memory(v)) == v
            ([lhs_value_snapshot] == [vir::Expr::from(value_snapshot)])
        );
        conversion_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            "Definition of conversion from value to memory to value",
            format!("conversion_value_to_value_of_{ty_name}"),
            body,
        ));
    }
    if !snapshot_might_contain_references(tcx, ty) {
        // Memory to value to memory:
        // forall m :: { to_memory(from_memory(m)) }  to_memory(from_memory(m)) == m
        let memory_snapshot = vir::LocalVar::new("memory_snapshot", memory_snapshot_type);
        let value_snapshot = conversion_functions[0].apply1(memory_snapshot.clone());
        let lhs_memory_snapshot = conversion_functions[1].apply1(value_snapshot);
        let body = vir_expr!(
            // forall m ::
            forall [memory_snapshot] ::
            // { to_memory(from_memory(m)) }
            { [lhs_memory_snapshot] } ::
            // to_memory(from_memory(m)) == m
            ([lhs_memory_snapshot] == [vir::Expr::from(memory_snapshot)])
        );
        conversion_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            "Definition of conversion from memory to value to memory",
            format!("conversion_memory_to_memory_of_{ty_name}"),
            body,
        ));
    }

    Ok(vir::Domain {
        name: domain_name,
        functions: vec![
            constructors,
            discriminant,
            destructors.concat(),
            conversion_functions,
        ]
        .concat(),
        axioms: vec![
            discriminant_axioms,
            existence_axioms,
            destructor_axioms,
            conversion_axioms,
        ]
        .concat(),
        type_vars: vec![],
    })
}
