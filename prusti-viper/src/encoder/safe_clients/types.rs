// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::utils::identifiers::encode_identifier;
use prusti_rustc_interface::middle::ty::TypeVisitable;
use crate::encoder::safe_clients::prelude::*;

pub fn encode_primitive_type(ty: ty::Ty<'_>) -> EncodingResult<vir::Type> {
    Ok(match ty.kind() {
        ty::TyKind::Bool => vir::Type::Bool,
        ty::TyKind::Char | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir::Type::Int,
        ty::TyKind::Float(ty::FloatTy::F32) => vir::Type::Float(vir::Float::F32),
        ty::TyKind::Float(ty::FloatTy::F64) => vir::Type::Float(vir::Float::F64),
        _ => {
            error_internal!("expected primitive type; got {:?}", ty);
        }
    })
}

/// Capitalizes the first character in s.
fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
}

pub fn encode_type_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> EncodingResult<String> {
    Ok(match ty.kind() {
        ty::TyKind::Bool => "Bool".to_string(),
        ty::TyKind::Char => "Char".to_string(),
        ty::TyKind::Int(int_ty) => capitalize(int_ty.name_str()),
        ty::TyKind::Uint(uint_ty) => capitalize(uint_ty.name_str()),
        ty::TyKind::Float(float_ty) => capitalize(float_ty.name_str()),

        ty::TyKind::RawPtr(ty::TypeAndMut { ty, mutbl }) => {
            format!(
                "{}Ptr${}",
                match mutbl {
                    hir::Mutability::Mut => "Mut",
                    hir::Mutability::Not => "Const",
                },
                encode_type_name(encoder, *ty)?,
            )
        }

        ty::TyKind::Ref(_region, ty, mutability) => {
            format!(
                "{}Ref${}",
                match mutability {
                    hir::Mutability::Mut => "Mut",
                    hir::Mutability::Not => "Shared",
                },
                encode_type_name(encoder, *ty)?,
            )
        }

        ty::TyKind::Tuple(elems) => {
            let mut elems_name = Vec::with_capacity(elems.len());
            for elem in elems.iter() {
                elems_name.push(encode_type_name(encoder, elem)?);
            }

            format!(
                "Tuple{}{}{}",
                elems.len(),
                if elems.is_empty() { "" } else { "$" },
                elems_name.join("$"),
            )
        },

        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() || adt_def.is_enum() => {
            let name = encode_identifier(encoder.env().name.get_unique_item_name(adt_def.did()));
            if substs.is_empty() {
                format!("Adt${name}")
            } else {
                let mut ty_arg_names = Vec::with_capacity(substs.len());
                for ty_arg in substs.iter() {
                    ty_arg_names.push(encode_type_argument_name(encoder, ty_arg)?);
                }
                format!("Adt${name}${}${}", ty_arg_names.len(), ty_arg_names.join("$"))
            }
        }

        ty::TyKind::Never => {
            "Never".to_string()
        }

        ty::TyKind::Param(param) => {
            format!("TypeParam${}", param.name)
        }

        ty::TyKind::Str => {
            "Str".to_string()
        }

        &ty::TyKind::Closure(def_id, substs) => {
            let name = encode_identifier(encoder.env().name.get_unique_item_name(def_id));
            if substs.is_empty() {
                format!("Closure${name}")
            } else {
                let mut ty_arg_names = Vec::with_capacity(substs.len());
                for ty_arg in substs.iter() {
                    ty_arg_names.push(encode_type_argument_name(encoder, ty_arg)?);
                }
                format!("Closure${name}${}${}", ty_arg_names.len(), ty_arg_names.join("$"))
            }
        }

        &ty::TyKind::Foreign(def_id) => {
            let name = encode_identifier(encoder.env().name.get_unique_item_name(def_id));
            format!("Foreign${name}")
        }

        &ty::TyKind::FnPtr(sig) => {
            // TODO: How to encode the binder?
            let sig = sig.skip_binder();
            // TODO: Is it possible to have recursive function pointer types?
            format!(
                "FnPtr$args${}${}$return${}",
                sig.inputs().len(),
                sig.inputs().iter().map(
                    |&input_ty| encode_type_name(encoder, input_ty)
                ).collect::<Result<Vec<_>, _>>()?.join("$"),
                encode_type_name(encoder, sig.output())?,
            )
        }

        _ => {
            error_unsupported!("unsupported type: {:?}", ty);
        }
    })
}

fn encode_type_argument_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, arg: ty::subst::GenericArg<'tcx>) -> EncodingResult<String> {
    match arg.unpack() {
        ty::GenericArgKind::Lifetime(_) => Ok("".to_string()),
        ty::GenericArgKind::Type(ty) => encode_type_name(encoder, ty),
        ty::GenericArgKind::Const(c) => error_unsupported!("unsupported constant in type: {:?}", c),
    }
}

pub fn is_unsafe_cell(ty: ty::Ty) -> bool {
    matches!(ty.kind(), ty::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell())
}

pub fn maybe_zst<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    // Return `true` for types that have type parameters, because those might be ZST.
    if ty.still_further_specializable() {
        return true;
    }
    let Ok(layout) = tcx.layout_of(ty::ParamEnv::empty().and(ty)) else {
        return false;
    };
    layout.is_zst()
}

/// If the result is `true`, the value snapshot *cannot* be converted to a memory snapshot.
pub fn snapshot_might_contain_references<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    let inner_visitor = |ty| snapshot_might_contain_references(tcx, ty);
    match *ty.kind() {
        // Snapshots stop at unsafe cells
        ty::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell() => false,
        _ if ty.is_primitive_ty() => false,
        ty::TyKind::Str => false,
        // Snapshots stop at raw pointers
        ty::TyKind::RawPtr(_) => false,
        ty::TyKind::Foreign(_) => true,
        ty::TyKind::Ref(_, _, _) => true,
        ty::TyKind::Array(inner_ty, _)
        | ty::TyKind::Slice(inner_ty) => snapshot_might_contain_references(tcx, inner_ty),
        ty::TyKind::Tuple(elem_tys) => {
            elem_tys.iter().any(inner_visitor)
        }
        ty::TyKind::Adt(adt_def, substs) => {
            let def_id = adt_def.did();
            let type_name: &str = &tcx.def_path_str(def_id);
            if type_name == "prusti_contracts::Ghost" {
                match substs[0].unpack() {
                    ty::GenericArgKind::Lifetime(_) => unreachable!(),
                    ty::GenericArgKind::Type(inner_ty) => inner_visitor(inner_ty),
                    ty::GenericArgKind::Const(c) => inner_visitor(c.ty()),
                }
            } else {
                adt_def.all_fields().map(|f| f.ty(tcx, substs)).any(inner_visitor)
            }
        }
        _ => {
            // Return true if there is any lifetime or type parameter
            ty.has_free_regions() || ty.has_erased_regions() || ty.has_late_bound_regions() || ty.needs_subst()
        }
    }
}

pub fn is_opaque_type<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    // Only FFI, struct and enums can be opaque
    if matches!(ty.kind(), ty::TyKind::Foreign(_)) {
        return true;
    };
    let ty::TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    let def_id = adt_def.did();
    let type_name: &str = &tcx.def_path_str(def_id);

    // Needed to encode the dereferentiation of Box types
    if type_name == "std::boxed::Box" || type_name == "std::ptr::Unique" || type_name == "std::ptr::NonNull" {
        return false;
    }

    // Small optimization: types with no public fields cannot be described using #[extern_spec]
    let has_public_fields = adt_def.variants().iter().any(|v| v.fields.iter().any(|f| f.vis.is_public()));
    if def_id.krate != LOCAL_CRATE && !has_public_fields {
        return true;
    }

    // Detect the ghost type
    type_name == "prusti_contracts::Ghost"
}
