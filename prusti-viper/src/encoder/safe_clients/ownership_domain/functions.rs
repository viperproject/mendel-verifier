// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::*;
use crate::encoder::safe_clients::prelude::*;

pub(super) struct OwnershipDomainFunctions {
    pub(super) ownership_at_functions: Vec<vir::DomainFunc>,
    pub(super) framing_across_stmt_functions: Vec<vir::DomainFunc>,
    pub(super) framing_across_call_functions: Vec<vir::DomainFunc>,
    pub(super) same_snap_fact_function: vir::DomainFunc,
    pub(super) same_id_shallow_function: vir::DomainFunc,
    pub(super) moved_fact_function: vir::DomainFunc,
}

pub(super) fn build_ownership_domain_functions<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<OwnershipDomainFunctions> {
    debug!("build_ownership_domain_functions({:?})", ty);
    let ty_name = types::encode_type_name(encoder, ty)?;
    let domain_name = ownership_domain_name(encoder, ty)?;
    let version_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)?;
    let address_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(ty))?;
    let snapshot_domain = MemSnapshotDomain::encode(encoder, ty)?;
    let address_domain = AddressDomain::encode(encoder, ty)?;
    let layout = type_layout::build_layout(encoder, ty)?;

    let mut ownership_at_functions = vec![];
    for kind in OwnershipKind::iter() {
        let name = format!("{OWNERSHIP_AT_FACT_PREFIX}{kind}_{ty_name}");
        let ownership_function = vir::DomainFunc::new(
            &domain_name,
            name,
            vec![
                vir::LocalVar::new("r", vir::Type::Int),
                vir::LocalVar::new("a", address_type.clone()),
                vir::LocalVar::new("v", version_type.clone()),
            ],
            vir::Type::Bool,
        );
        ownership_at_functions.push(ownership_function);
    }

    let mut framing_across_stmt_functions = vec![];
    for kind in OwnershipKind::iter() {
        let name = format!("{FRAMING_ACROSS_STMT_FACT_PREFIX}{kind}_{ty_name}");
        let framing_across_stmt_function = vir::DomainFunc::new(
            &domain_name,
            name,
            vec![
                //vir::LocalVar::new("r", vir::Type::Int),
                vir::LocalVar::new("a", address_type.clone()),
                vir::LocalVar::new("v1", version_type.clone()),
                vir::LocalVar::new("v2", version_type.clone()),
            ],
            vir::Type::Bool,
        );
        framing_across_stmt_functions.push(framing_across_stmt_function);
    }

    let mut framing_across_call_functions = vec![];
    for kind in OwnershipKind::iter() {
        let name = format!("{FRAMING_ACROSS_CALL_OWNERSHIP_FACT_PREFIX}{kind}_{ty_name}");
        let framing_across_call_function = vir::DomainFunc::new(
            &domain_name,
            name,
            vec![
                //vir::LocalVar::new("r", vir::Type::Int),
                vir::LocalVar::new("a", address_type.clone()),
                vir::LocalVar::new("v1", version_type.clone()),
                vir::LocalVar::new("v2", version_type.clone()),
            ],
            vir::Type::Bool,
        );
        framing_across_call_functions.push(framing_across_call_function);
    }

    let same_snap_fact_function = vir::DomainFunc::new(
        &domain_name,
        format!("{SAME_SNAP_FACT_PREFIX}{ty_name}"),
        vec![
            vir::LocalVar::new("a", address_type.clone()),
            vir::LocalVar::new("v1", version_type.clone()),
            vir::LocalVar::new("v2", version_type.clone()),
        ],
        vir::Type::Bool,
    );

    let same_id_shallow_function = vir::DomainFunc::new(
        &domain_name,
        format!("{SAME_ID_SHALLOW_FACT_PREFIX}{ty_name}"),
        vec![
            vir::LocalVar::new("a", address_type.clone()),
            vir::LocalVar::new("v1", version_type.clone()),
            vir::LocalVar::new("v2", version_type.clone()),
        ],
        vir::Type::Bool,
    );

    let moved_fact_function = vir::DomainFunc::new(
        &domain_name,
        format!("{MOVED_FACT_PREFIX}_{ty_name}"),
        vec![
            vir::LocalVar::new("a1", address_type.clone()),
            vir::LocalVar::new("v1", version_type.clone()),
            vir::LocalVar::new("a2", address_type),
            vir::LocalVar::new("v2", version_type),
        ],
        vir::Type::Bool,
    );

    Ok(OwnershipDomainFunctions {
        ownership_at_functions,
        framing_across_stmt_functions,
        framing_across_call_functions,
        same_snap_fact_function,
        same_id_shallow_function,
        moved_fact_function,
    })
}
