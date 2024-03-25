// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

/// Representation of the layout of a type.
/// Blueprint used in the generation of snapshot and address domains.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeLayout<'tcx> {
    /// Layouts with no variants are considered opaque
    pub variants: Vec<VariantLayout<'tcx>>,
}

/// Representation of the layout of a type variant.
/// Blueprint used in the generation of snapshot and address domains.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantLayout<'tcx> {
    pub name: String,
    pub discriminant: vir::Expr,
    pub fields: Vec<FieldLayout<'tcx>>,
}

impl<'tcx> VariantLayout<'tcx> {
    pub fn has_non_visible_fields(&self) -> bool {
        self.fields.iter().any(|f| !f.is_visible)
    }

    /// Returns the visible fields that have a snapshot value
    pub fn value_fields(&self) -> impl Iterator<Item = &FieldLayout<'tcx>> {
        self.fields.iter().filter(|f| f.value_snapshot_ty.is_some())
    }
}

/// Representation of the layout of a field.
/// Blueprint used in the generation of snapshot and address domains.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldLayout<'tcx> {
    pub is_visible: bool,
    pub name: String,
    /// The field in the memory snapshot of the layout.
    /// * For primitive types it's a Viper primitive type.
    /// * For regular fields it's a snapshot.
    /// * For references it's an address or snapshot.
    /// * For raw pointers and unsafe cells it's an address.
    pub mem_snapshot_ty: vir::Type,
    /// The field in the value snapshot of the layout.
    /// * For primitive types it's a Viper primitive type.
    /// * For regular fields it's a value snapshot.
    /// * For references it's a value snapshot.
    /// * For raw pointers  it's an address.
    /// * For unsafe cells it's nothing.
    pub value_snapshot_ty: Option<vir::Type>,
    /// If defined, the type of the ADT field or UnsafeCell content.
    /// It's None for primitive types, references and raw pointers.
    /// This field represents the layout of a field *in the same type instance*, i.e. not following
    /// raw pointers or references.
    pub ty: Option<ty::Ty<'tcx>>,
}

impl<'tcx> FieldLayout<'tcx> {
    pub fn value_snapshot_ty(&self) -> &vir::Type {
        self.value_snapshot_ty.as_ref().unwrap()
    }
}

pub fn build_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<TypeLayout<'tcx>> {
    trace!("build_layout {:?}", ty);
    match ty.kind() {
        _ if types::is_opaque_type(encoder.env().tcx(), ty) => {
            debug_assert!(ty.is_adt());
            Ok(TypeLayout { variants: vec![] })
        }
        _ if ty.is_primitive_ty() => build_primitive_layout(encoder, ty),
        ty::TyKind::Tuple(_) => build_adt_layout(encoder, ty),
        ty::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell() => {
            build_unsafe_cell_layout(encoder, ty)
        }
        ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() || adt_def.is_enum() => {
            build_adt_layout(encoder, ty)
        }
        ty::TyKind::Ref(_, _, _) => build_reference_layout(encoder, ty),
        ty::TyKind::RawPtr(_) => build_pointer_layout(encoder, ty),
        _ => {
            // error_unsupported!("unsupported type {:?}", ty);
            Ok(TypeLayout { variants: vec![] })
        }
    }
}

fn build_primitive_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<TypeLayout<'tcx>> {
    if !ty.is_primitive_ty() {
        error_internal!("expected primitive type; got {:?}", ty);
    };

    let fields = vec![FieldLayout {
        is_visible: true,
        name: "value".to_string(),
        mem_snapshot_ty: types::encode_primitive_type(ty)?,
        value_snapshot_ty: Some(types::encode_primitive_type(ty)?),
        ty: None,
    }];

    let variants = vec![VariantLayout {
        name: "primitive".to_string(),
        discriminant: 0.into(),
        fields,
    }];
    Ok(TypeLayout { variants })
}

/// Encode *signed* discriminats
fn encode_discriminant_value<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    variant_index: abi::VariantIdx,
) -> vir::Expr {
    let tcx = encoder.env().tcx();
    let discr_ty = adt_def.repr().discr_type();
    if discr_ty.is_signed() {
        let bit_size = abi::Integer::from_attr(&tcx, discr_ty).size().bits();
        let shift = 128 - bit_size;
        let unsigned_discr = adt_def.discriminant_for_variant(tcx, variant_index).val;
        let casted_discr = unsigned_discr as i128;
        // sign extend the raw representation to be an i128
        ((casted_discr << shift) >> shift).into()
    } else {
        adt_def
            .discriminant_for_variant(tcx, variant_index)
            .val
            .into()
    }
}

fn build_adt_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<TypeLayout<'tcx>> {
    let mut variants = vec![];
    match ty.kind() {
        ty::TyKind::Tuple(substs) => {
            let mut fields = Vec::with_capacity(substs.len());
            for (field_idx, field_ty) in substs.iter().enumerate() {
                let field_snapshot_ty = encoder
                    .encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(field_ty))?;
                let field_value_snapshot_ty = encoder
                    .encode_builtin_domain_type(BuiltinDomainKind::ValueSnapshot(field_ty))?;
                fields.push(FieldLayout {
                    is_visible: true,
                    name: format!("f${field_idx}"),
                    mem_snapshot_ty: field_snapshot_ty,
                    value_snapshot_ty: Some(field_value_snapshot_ty),
                    ty: Some(field_ty),
                });
            }
            variants.push(VariantLayout {
                name: "tuple".to_string(),
                discriminant: 0.into(),
                fields,
            });
        }
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
            let tcx = encoder.env().tcx();
            for (variant_idx, variant) in adt_def.variants().iter_enumerated() {
                let variant_name = variant.ident(tcx).name.to_ident_string();
                let mut fields = Vec::with_capacity(variant.fields.len());
                for (field_idx, field) in variant.fields.iter().enumerate() {
                    let field_name = field.ident(tcx).name.to_ident_string();
                    let field_ty = field.ty(encoder.env().tcx(), substs);
                    let field_snapshot_ty = encoder
                        .encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(field_ty))?;
                    let field_value_snapshot_ty = encoder
                        .encode_builtin_domain_type(BuiltinDomainKind::ValueSnapshot(field_ty))?;
                    let field_address_ty =
                        encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(field_ty))?;
                    fields.push(FieldLayout {
                        is_visible: field.vis.is_public(),
                        name: format!("f${field_name}"),
                        mem_snapshot_ty: field_snapshot_ty,
                        value_snapshot_ty: Some(field_value_snapshot_ty),
                        ty: Some(field_ty),
                    });
                }
                variants.push(VariantLayout {
                    name: variant_name,
                    discriminant: 0.into(),
                    fields,
                });
            }
        }
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_enum() => {
            let tcx = encoder.env().tcx();
            for (variant_idx, variant) in adt_def.variants().iter_enumerated() {
                let discriminant = encode_discriminant_value(encoder, *adt_def, variant_idx);
                let variant_name = variant.ident(tcx).name.to_ident_string();
                let mut fields = vec![];
                for (field_idx, field) in variant.fields.iter().enumerate() {
                    let field_name = field.ident(tcx).name.to_ident_string();
                    let field_ty = field.ty(encoder.env().tcx(), substs);
                    let field_snapshot_ty = encoder
                        .encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(field_ty))?;
                    let field_value_snapshot_ty = encoder
                        .encode_builtin_domain_type(BuiltinDomainKind::ValueSnapshot(field_ty))?;
                    fields.push(FieldLayout {
                        is_visible: field.vis.is_public(),
                        name: format!("v${variant_name}_f${field_name}"),
                        mem_snapshot_ty: field_snapshot_ty,
                        value_snapshot_ty: Some(field_value_snapshot_ty),
                        ty: Some(field_ty),
                    });
                }
                variants.push(VariantLayout {
                    name: variant_name,
                    discriminant,
                    fields,
                });
            }
        }
        _ => error_internal!("expected tuple or ADT type; got {:?}", ty),
    }

    Ok(TypeLayout { variants })
}

fn build_reference_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<TypeLayout<'tcx>> {
    let ty::TyKind::Ref(_region, target_ty, _mutability) = ty.kind() else {
        error_internal!("expected reference type; got {:?}", ty);
    };

    let target_address_ty =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(*target_ty))?;
    let target_snapshot_ty =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(*target_ty))?;
    let target_value_snapshot_ty =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::ValueSnapshot(*target_ty))?;
    let fields = vec![
        FieldLayout {
            is_visible: true,
            name: "target_address".to_string(),
            mem_snapshot_ty: target_address_ty,
            value_snapshot_ty: None,
            ty: None,
        },
        FieldLayout {
            is_visible: true,
            name: "target_snapshot".to_string(),
            mem_snapshot_ty: target_snapshot_ty,
            value_snapshot_ty: Some(target_value_snapshot_ty),
            ty: None,
        },
    ];

    let variants = vec![VariantLayout {
        name: "reference".to_string(),
        discriminant: 0.into(),
        fields,
    }];
    Ok(TypeLayout { variants })
}

fn build_pointer_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<TypeLayout<'tcx>> {
    let &ty::TyKind::RawPtr(ty::TypeAndMut { ty: target_ty, .. }) = ty.kind() else {
        error_internal!("expected raw pointer type; got {:?}", ty);
    };

    let target_address_ty =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(target_ty))?;
    let fields = vec![FieldLayout {
        is_visible: true,
        name: "target".to_string(),
        mem_snapshot_ty: target_address_ty.clone(),
        value_snapshot_ty: Some(target_address_ty),
        ty: None,
    }];

    let variants = vec![VariantLayout {
        name: "raw_pointer".to_string(),
        discriminant: 0.into(),
        fields,
    }];
    Ok(TypeLayout { variants })
}

fn build_unsafe_cell_layout<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<TypeLayout<'tcx>> {
    let ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
        error_internal!("expected unsafe cell type; got {:?}", ty);
    };
    if !adt_def.is_unsafe_cell() {
        error_internal!("expected unsafe cell type; got {:?}", ty);
    }
    let content_field = &adt_def.variants().iter().next().unwrap().fields[0];
    let content_ty = content_field.ty(encoder.env().tcx(), substs);

    let content_address_ty =
        encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(content_ty))?;
    let fields = vec![
        // FieldLayout {
        //     is_visible: false,
        //     name: "content".to_string(),
        //     mem_snapshot_ty: content_address_ty.clone(),
        //     value_snapshot_ty: None, //Some(content_address_ty),
        //     ty: Some(content_ty),
        // }
    ];

    let variants = vec![VariantLayout {
        name: "unsafe_cell".to_string(),
        discriminant: 0.into(),
        fields,
    }];
    Ok(TypeLayout { variants })
}
