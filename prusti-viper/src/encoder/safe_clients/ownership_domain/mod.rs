// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod functions;

use std::rc::Rc;
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::safe_clients::types::is_unsafe_cell;
use prusti_interface::specs::typed;
use strum::IntoEnumIterator;
use strum_macros::{EnumIter, Display};
use functions::*;

pub(super) const DOMAIN_NAME_PREFIX: &str = "Ownership";
pub(super) const OWNERSHIP_AT_FACT_PREFIX: &str = "owns_as_";
pub(super) const FRAMING_ACROSS_STMT_FACT_PREFIX: &str = "frame_across_stmt_";
pub(super) const FRAMING_ACROSS_CALL_OWNERSHIP_FACT_PREFIX: &str = "frame_across_call_";
pub(super) const SAME_SNAP_FACT_PREFIX: &str = "same_snap_";
pub(super) const SAME_ID_SHALLOW_FACT_PREFIX: &str = "same_id_shallow_";
pub(super) const MOVED_FACT_PREFIX: &str = "move_";

#[derive(Display, Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter)]
pub enum OwnershipKind {
    WriteRef = 0,
    /// A ReadRef ownership that is guaranteed to be local
    LocalRef,
    ReadRef,
    Unique,
    /// An instance that is guaranteed to be framed across interference (but not necessarily statements or calls).
    Local,
    /// A raw pointer with the properties of a shared reference
    Immutable,
    /// Can always read the target value
    Read,
    Write,
    /// An instance exists. Every ownership fact imples this. The root parameter of this fact is meaningless.
    Allocated,
    /// The ownership of part of a mutable reference that is unreachable due to some reborrowing.
    DeeplyUnreachable,
    /// Shallow ownership. For example:
    /// - the ownership of a mutable reference whose target is blocked due to some reborrowing;
    /// - the call-side framed ownership of a mutable reference passed as argument to a call.
    /// In both cases, the address of the target of the reference is guaranteed to not mutate.
    ShallowlyOwned,
    NoReadRef,
    NoWriteRef,
}

impl From<typed::OwnershipKind> for OwnershipKind {
    fn from(value: typed::OwnershipKind) -> Self {
        match value {
            typed::OwnershipKind::WriteRef => OwnershipKind::WriteRef,
            typed::OwnershipKind::LocalRef => OwnershipKind::LocalRef,
            typed::OwnershipKind::ReadRef => OwnershipKind::ReadRef,
            typed::OwnershipKind::Unique => OwnershipKind::Unique,
            typed::OwnershipKind::Local => OwnershipKind::Local,
            typed::OwnershipKind::Immutable => OwnershipKind::Immutable,
            typed::OwnershipKind::Read => OwnershipKind::Read,
            typed::OwnershipKind::Write => OwnershipKind::Write,
            typed::OwnershipKind::NoReadRef => OwnershipKind::NoReadRef,
            typed::OwnershipKind::NoWriteRef => OwnershipKind::NoWriteRef,
        }
    }
}

impl TryFrom<&str> for OwnershipKind {
    type Error = ();

    fn try_from(typ: &str) -> Result<OwnershipKind, ()> {
        match typ {
            "readRef" => Ok(OwnershipKind::ReadRef),
            "localRef" => Ok(OwnershipKind::LocalRef),
            "writeRef" => Ok(OwnershipKind::WriteRef),
            "unique" => Ok(OwnershipKind::Unique),
            "local" => Ok(OwnershipKind::Local),
            "immutable" => Ok(OwnershipKind::Immutable),
            "read" => Ok(OwnershipKind::Read),
            "write" => Ok(OwnershipKind::Write),
            "noReadRef" => Ok(OwnershipKind::NoReadRef),
            "noWriteRef" => Ok(OwnershipKind::NoWriteRef),
            _ => Err(()),
        }
    }
}

pub fn ownership_domain_name<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>,
) -> EncodingResult<String> {
    let ty_name = types::encode_type_name(encoder, ty)?;
    Ok(format!("{DOMAIN_NAME_PREFIX}${ty_name}"))
}

pub fn ownership_domain_type<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Type> {
    Ok(vir::Type::domain(ownership_domain_name(encoder, ty)?))
}

pub fn build_ownership_domain<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Domain> {
    debug!("build_ownership_domain({:?})", ty);
    let ty_name = types::encode_type_name(encoder, ty)?;
    let domain_name = ownership_domain_name(encoder, ty)?;
    let version_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)?;
    let address_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Address(ty))?;
    let snapshot_domain = MemSnapshotDomain::encode(encoder, ty)?;
    let address_domain = AddressDomain::encode(encoder, ty)?;
    let layout = type_layout::build_layout(encoder, ty)?;
    let tcx = encoder.env().tcx();

    let mut df = build_ownership_domain_functions(encoder, ty)?;

    // === Axioms: Agreement between field of snapshot and addresses ===
    let mut snap_address_axioms = vec![];
    if !types::is_unsafe_cell(ty) {
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            let abi_variant = if ty.is_enum() {
                Some(variant_idx.into())
            } else {
                None
            };
            for (field_idx, field) in variant.fields.iter().enumerate() {
                let mir_field = field_idx.into();
                if let Some(field_ty) = field.ty.as_ref().copied() {
                    let base_address_domain = AddressDomain::encode(encoder, ty)?;
                    let base_snapshot_domain = MemSnapshotDomain::encode(encoder, ty)?;
                    let field_address_domain = AddressDomain::encode(encoder, field_ty)?;
                    let field_snapshot_domain = MemSnapshotDomain::encode(encoder, field_ty)?;

                    let base_deref_fn = base_address_domain.deref_function()?;
                    let field_addr_fn = base_address_domain.adt_field_address_function(abi_variant, mir_field)?;
                    let field_deref_fn = field_address_domain.deref_function()?;
                    let field_snap_fn = base_snapshot_domain.adt_field_function(abi_variant, mir_field)?;

                    let version = vir::LocalVar::new("v", version_type.clone());
                    let base_addr = vir::LocalVar::new("base_addr", address_type.clone());
                    let base_snapshot = base_deref_fn.apply2(
                        base_addr.clone(), version.clone(),
                    );
                    let field_snap_1 = field_deref_fn.apply2(
                        field_addr_fn.apply1(base_addr.clone()), version.clone(),
                    );
                    let field_snap_2 = field_snap_fn.apply1(base_snapshot.clone());

                    // This is not a matching loop because it doesn't follow raw pointers or references.
                    let body = vir_expr!(
                        forall [version], [base_addr] :: { [base_snapshot] } :: ([field_snap_1] == [field_snap_2])
                    );
                    snap_address_axioms.push(vir::DomainAxiom::new(
                        &domain_name,
                        format!(
                            "The snapshot and address definitions agree on field {}",
                            field.name,
                        ),
                        format!(
                            "agree_snap_addr_of_{ty_name}_variant${variant_idx}_field${field_idx}"
                        ),
                        body,
                    ));
                }
            }
        }
    }

    // === Axioms: Language ownership implications ===
    let implications = [
        // left ==> right
        (OwnershipKind::WriteRef, OwnershipKind::Unique), // Only if it does not implement Unpin
        (OwnershipKind::WriteRef, OwnershipKind::Write),
        (OwnershipKind::WriteRef, OwnershipKind::LocalRef),
        (OwnershipKind::LocalRef, OwnershipKind::Local),
        (OwnershipKind::LocalRef, OwnershipKind::ReadRef),
        (OwnershipKind::Unique, OwnershipKind::Local),
        (OwnershipKind::Unique, OwnershipKind::Write),
        (OwnershipKind::ReadRef, OwnershipKind::Immutable),
        (OwnershipKind::Write, OwnershipKind::Read),
        (OwnershipKind::Local, OwnershipKind::Read),
        (OwnershipKind::Immutable, OwnershipKind::Read),
        (OwnershipKind::Read, OwnershipKind::Allocated),
        // We can use unique because we'll encode all unreachability facts as having the same root.
        (OwnershipKind::DeeplyUnreachable, OwnershipKind::Unique),
        (OwnershipKind::DeeplyUnreachable, OwnershipKind::NoReadRef),
        (OwnershipKind::DeeplyUnreachable, OwnershipKind::NoWriteRef),
        //(OwnershipKind::NoReadRef, OwnershipKind::Allocated),  // unnecessary
        //(OwnershipKind::NoReadRef, OwnershipKind::NoWriteRef), // Wrong!
        //(OwnershipKind::NoWriteRef, OwnershipKind::Allocated), // unnecessary
    ];

    let mut ownership_implication_axioms = vec![];
    for (left, right) in implications.iter().copied() {
        let root = vir::LocalVar::new("r", vir::Type::Int);
        let address = vir::LocalVar::new("a", address_type.clone());
        let version = vir::LocalVar::new("v", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());

        // .is_primitive_ty() is a conservative approximation of .is_unpin(..)
        if (left, right) == (OwnershipKind::WriteRef, OwnershipKind::Unique) && !ty.is_primitive_ty() {
            continue;
        }

        { // At program point
            let left_fact_fn = df.ownership_at_functions[left as usize].clone();
            let right_fact_fn = df.ownership_at_functions[right as usize].clone();
            let left_fact = left_fact_fn.apply3(root.clone(), address.clone(), version.clone());
            let right_fact = right_fact_fn.apply3(root.clone(), address.clone(), version.clone());

            let body = vir_expr!(
                forall [root], [address], [version] ::
                { [left_fact.clone()] } { [right_fact.clone()] } ::
                ([left_fact] ==> [right_fact])
            );
            ownership_implication_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Ownership implication: {left} ==> {right}"),
                format!("ownership_implication_at_from_{left}_to_{right}_of_{ty_name}"),
                body,
            ));
        }
        { // Across stmt
            let left_fact_fn = df.framing_across_stmt_functions[left as usize].clone();
            let right_fact_fn = df.framing_across_stmt_functions[right as usize].clone();
            let left_fact = left_fact_fn.apply3(
                address.clone(), version.clone(), version_2.clone(),
            );
            let right_fact = right_fact_fn.apply3(
                address.clone(), version.clone(), version_2.clone(),
            );

            let body = vir_expr!(
                forall [address], [version], [version_2] ::
                { [left_fact.clone()] } { [right_fact.clone()] } ::
                ([left_fact] ==> [right_fact])
            );
            ownership_implication_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Ownership implication across stmt: {left} ==> {right}"),
                format!("ownership_implication_across_stmt_from_{left}_to_{right}_of_{ty_name}"),
                body,
            ));
        }
        { // Across call
            let left_fact_fn = df.framing_across_call_functions[left as usize].clone();
            let right_fact_fn = df.framing_across_call_functions[right as usize].clone();
            let left_fact = left_fact_fn.apply3(
                address.clone(), version.clone(), version_2.clone(),
            );
            let right_fact = right_fact_fn.apply3(
                address.clone(), version.clone(), version_2.clone(),
            );

            let body = vir_expr!(
                forall [address], [version], [version_2] ::
                { [left_fact.clone()] } { [right_fact.clone()] } ::
                ([left_fact] ==> [right_fact])
            );
            ownership_implication_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Ownership implication across call: {left} ==> {right}"),
                format!("ownership_implication_across_call_from_{left}_to_{right}_of_{ty_name}"),
                body,
            ));
        }
    }

    // === Axioms: Language ownership incompatibilities ===
    let incompatibilities = [
        // !(left && right)
        (OwnershipKind::Immutable, OwnershipKind::Write),
        (OwnershipKind::Unique, OwnershipKind::Read),
        (OwnershipKind::NoReadRef, OwnershipKind::ReadRef),
        (OwnershipKind::NoWriteRef, OwnershipKind::WriteRef),
    ];

    let mut ownership_incompatibility_axioms = vec![];

    // Skip types that might be zero-size, because they can't have aliasing.
    if !types::maybe_zst(tcx, ty) {
        for (left, right) in incompatibilities.iter().copied() {
            let root = vir::LocalVar::new("r", vir::Type::Int);
            let other = vir::LocalVar::new("o", vir::Type::Int);
            let address = vir::LocalVar::new("a", address_type.clone());
            let version = vir::LocalVar::new("v", version_type.clone());
            let version_2 = vir::LocalVar::new("v2", version_type.clone());

            { // At program point
                let left_fact_fn = df.ownership_at_functions[left as usize].clone();
                let right_fact_fn = df.ownership_at_functions[right as usize].clone();
                let left_fact = left_fact_fn.apply3(root.clone(), address.clone(), version.clone());
                let right_fact = right_fact_fn.apply3(other.clone(), address.clone(), version.clone());
                let root_expr: vir::Expr = root.clone().into();
                let other_expr: vir::Expr = other.clone().into();

                let body = vir_expr!(
                    forall [root], [other], [address], [version] ::
                    { [left_fact.clone()], [right_fact.clone()] } ::
                    (([root_expr] != [other_expr]) ==> (!([left_fact] && [right_fact])))
                );
                ownership_incompatibility_axioms.push(vir::DomainAxiom::new(
                    &domain_name,
                    format!("Ownership incompatibility: {left} -- {right}"),
                    format!("ownership_incompatibility_at_between_{left}_{right}_of_{ty_name}"),
                    body,
                ));
            }
            // Nothing across statements
            // Nothing across calls
        }
    }

    // === Axioms: Field ownership ===
    let field_view_function = |(base_kind, visible_field)| {
        // visible_field is used to avoid entering e.g. UnsafeCells and Pin types
        // Exclude raw pointers
        assert!(!matches!(ty.kind(), ty::TyKind::RawPtr(_)));
        match base_kind {
            // Never transitive
            OwnershipKind::NoReadRef
            | OwnershipKind::NoWriteRef
            | OwnershipKind::Local
            | OwnershipKind::Unique
            | OwnershipKind::Immutable // might be declared transitive until unsafe cells
            | OwnershipKind::Read => None,

            // Only transitive for non-reference public fields
            OwnershipKind::ShallowlyOwned => {
                match ty.kind() {
                    // Ownership stops at references
                    ty::TyKind::Ref(_, _, _) => None,
                    // Ownership is (conservatively) only transitive for public fields
                    _ if visible_field => Some(base_kind),
                    _ => None,
                }
            }

            // Only transitive for non-shared-reference public fields
            OwnershipKind::WriteRef
            | OwnershipKind::LocalRef
            | OwnershipKind::Write
            => {
                match ty.kind() {
                    // Ownership stops at shared references
                    ty::TyKind::Ref(_, _, hir::Mutability::Not) => None,
                    // Ownership is (conservatively) only transitive for public fields
                    _ if visible_field => Some(base_kind),
                    _ => None,
                }
            }

            // Only transitive for public fields
            OwnershipKind::ReadRef | OwnershipKind::DeeplyUnreachable => {
                if visible_field { Some(base_kind) } else { None }
            }

            // Fully transitive
            OwnershipKind::Allocated => Some(base_kind),
        }
    };

    let mut field_ownership_axioms = vec![];
    for (variant_idx, variant) in layout.variants.iter().enumerate() {
        let root = vir::LocalVar::new("r", vir::Type::Int);
        let address = vir::LocalVar::new("a", address_type.clone());
        let version = vir::LocalVar::new("v", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let abi_variant = if ty.is_enum() {
            Some(variant_idx.into())
        } else {
            None
        };
        let discriminant_condition = if ty.is_enum() {
            let base_snapshot = address_domain.deref_function()?
                .apply2(address.clone(), version.clone());
            let discr_value = snapshot_domain.discriminant_function()?.apply1(base_snapshot);
            vir_expr!( [discr_value] == [variant.discriminant] )
        } else {
            true.into()
        };
        for (field_idx, field) in variant.fields.iter().enumerate() {
            let mir_field = field_idx.into();
            let (field_ty, field_address) = match field.ty.as_ref().copied() {
                Some(field_ty) => {
                    let field_address = address_domain
                        .adt_field_address_function(abi_variant, mir_field)?
                        .apply1(address.clone());
                    (field_ty, field_address)
                }
                None => {
                    if let &ty::TyKind::Ref(_, field_ty, _) = ty.kind() && field_idx == 0 {
                        let base_snapshot = address_domain.deref_function()?
                            .apply2(address.clone(), version.clone());
                        let field_address = snapshot_domain.target_address_function()?
                            .apply1(base_snapshot);
                        (field_ty, field_address)
                    } else {
                        continue;
                    }
                }
            };
            let field_ownership_domain = OwnershipDomain::encode(encoder, field_ty)?;
            for base_kind in OwnershipKind::iter() {
                let Some(field_kind) = field_view_function((base_kind, field.is_visible)) else {
                    continue;
                };
                { // At program point
                    let base_fact = df.ownership_at_functions[base_kind as usize]
                        .apply3(root.clone(), address.clone(), version.clone());
                    let field_fact = field_ownership_domain.ownership_fact_function(field_kind)?
                        .apply3(root.clone(), field_address.clone(), version.clone());
                    let body = vir_expr!(
                        forall [root], [address], [version] ::
                        { [base_fact.clone()] } ::
                        (([base_fact] && [discriminant_condition]) ==> [field_fact])
                    );
                    field_ownership_axioms.push(vir::DomainAxiom::new(
                        &domain_name,
                        format!("Ownership of field {}: {base_kind} ==> {field_kind}", field.name),
                        format!("ownership_of_field_{}_from_{base_kind}_of_{ty_name}", field.name,),
                        body,
                    ));
                }
                { // Across stmt
                    let base_fact = df.framing_across_stmt_functions[base_kind as usize]
                        .apply3(address.clone(), version.clone(), version_2.clone());
                    let field_fact = field_ownership_domain.framed_stmt_fact_function(field_kind)?
                        .apply3(field_address.clone(), version.clone(), version_2.clone());
                    let body = vir_expr!(
                        forall [address], [version], [version_2] ::
                        { [base_fact.clone()] } ::
                        (([base_fact] && [discriminant_condition]) ==> [field_fact])
                    );
                    field_ownership_axioms.push(vir::DomainAxiom::new(
                        &domain_name,
                        format!("Ownership across statement of field {}: {base_kind} ==> {field_kind}", field.name),
                        format!("ownership_across_stmt_of_field_{}_from_{base_kind}_of_{ty_name}", field.name),
                        body,
                    ));
                }
                { // Across call
                    let base_fact = df.framing_across_call_functions[base_kind as usize]
                        .apply3(address.clone(), version.clone(), version_2.clone());
                    let field_fact = field_ownership_domain.framed_call_fact_function(field_kind)?
                        .apply3(field_address.clone(), version.clone(), version_2.clone());
                    let body = vir_expr!(
                        forall [address], [version], [version_2] ::
                        { [base_fact.clone()] } ::
                        (([base_fact] && [discriminant_condition]) ==> [field_fact])
                    );
                    field_ownership_axioms.push(vir::DomainAxiom::new(
                        &domain_name,
                        format!("Ownership across call of field {}: {base_kind} ==> {field_kind}", field.name),
                        format!("ownership_across_call_of_field_{}_from_{base_kind}_of_{ty_name}", field.name),
                        body,
                    ));
                }
            }
        }
    }

    // === Axioms: Framing of primitive types implied by ownership ===
    let implied_framing = &[
        // Across a <1> we assume the same (memory) snapshot for framed <2>-owned locations
        (CallOrStmt::Call, OwnershipKind::Immutable),
        (CallOrStmt::Stmt, OwnershipKind::Immutable),
        (CallOrStmt::Call, OwnershipKind::Unique),
        (CallOrStmt::Stmt, OwnershipKind::Unique),
        //(CallOrStmt::Stmt, OwnershipKind::NoWriteRef && OwnershipKind::Local),
    ];

    let mut implied_framing_axioms = vec![];
    for &(stmt_or_call, base_kind) in implied_framing {
        let root = vir::LocalVar::new("r", vir::Type::Int);
        let address = vir::LocalVar::new("a", address_type.clone());
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let base_fact_fn = match stmt_or_call {
            CallOrStmt::Call => df.framing_across_call_functions[base_kind as usize].clone(),
            CallOrStmt::Stmt => df.framing_across_stmt_functions[base_kind as usize].clone(),
        };
        let base_fact = base_fact_fn
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let same_snap_fact = df.same_snap_fact_function
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let same_id_fact = df.same_id_shallow_function
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let body = vir_expr!(
            forall [address], [version_1], [version_2] ::
            { [base_fact.clone()] } ::
            ([base_fact] ==> ([same_snap_fact] && [same_id_fact]))
        );
        implied_framing_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            format!("Framing implied by ownership: {base_kind}"),
            format!("framing_across_{stmt_or_call}_implied_by_ownership_{base_kind}_of_{ty_name}"),
            body,
        ));
    }
    { //(CallOrStmt::Stmt, OwnershipKind::NoWriteRef && OwnershipKind::Local),
        let root = vir::LocalVar::new("r", vir::Type::Int);
        let address = vir::LocalVar::new("a", address_type.clone());
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let base_fact_fn_nwr = df.framing_across_stmt_functions[OwnershipKind::NoWriteRef as usize].clone();
        let base_fact_fn_loc = df.framing_across_stmt_functions[OwnershipKind::Local as usize].clone();
        let base_fact_nwr = base_fact_fn_nwr
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let base_fact_loc = base_fact_fn_loc
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let same_snap_fact = df.same_snap_fact_function
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let same_id_fact = df.same_id_shallow_function
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let body = vir_expr!(
            forall [address], [version_1], [version_2] ::
            { [base_fact_nwr], [base_fact_loc] } ::
            (([base_fact_nwr] && [base_fact_loc]) ==> ([same_snap_fact] && [same_id_fact]))
        );
        implied_framing_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            format!("Framing implied by ownership: NoWriteRef && Local"),
            format!("framing_across_stmt_implied_by_ownership_NoWriteRef_and_Local_of_{ty_name}"),
            body,
        ));
    }

    // === Axiom: Same snapshot fact ===
    let framing_snapshot_axiom = {
        let address = vir::LocalVar::new("a", address_type.clone());
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let same_snap_fact = df.same_snap_fact_function
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let snapshot_1 = address_domain.deref_function()?
            .apply2(address.clone(), version_1.clone());
        let snapshot_2 = address_domain.deref_function()?
            .apply2(address.clone(), version_2.clone());
        let body = vir_expr!(
            forall [address], [version_1], [version_2] ::
            { [same_snap_fact] } ::
            ([same_snap_fact] ==> ([snapshot_1] == [snapshot_2]))
        );
        vir::DomainAxiom::new(
            &domain_name,
            format!("Framing definition of {ty_name}"),
            format!("framing_definition_of_{ty_name}"),
            body,
        )
    };

    // === Axiom: Shallow framing of ids (until the first unsafe cell or raw pointer) ===
    let mut same_id_shallow_axioms = vec![];
    {
        let address = vir::LocalVar::new("a", address_type.clone());
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let same_id_fact = df.same_id_shallow_function
            .apply3(address.clone(), version_1.clone(), version_2.clone());
        let id_1 = address_domain.id_function()?
            .apply2(address.clone(), version_1.clone());
        let id_2 = address_domain.id_function()?
            .apply2(address.clone(), version_2.clone());
        same_id_shallow_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            format!("Shallow id framing definition of {ty_name}"),
            format!("same_id_shallow_definition_of_{ty_name}"),
            vir_expr!(
                forall [address], [version_1], [version_2] ::
                { [same_id_fact] } ::
                ([same_id_fact] ==> ([id_1] == [id_2]))
            ),
        ));

        if !is_unsafe_cell(ty) {
            for (variant_idx, variant) in layout.variants.iter().enumerate() {
                let abi_variant = if ty.is_enum() {
                    Some(variant_idx.into())
                } else {
                    None
                };
                let discriminant_condition = if ty.is_enum() {
                    let base_snapshot = address_domain.deref_function()?
                        .apply2(address.clone(), version_1.clone());
                    let discr_value = snapshot_domain.discriminant_function()?.apply1(base_snapshot);
                    vir_expr!( [discr_value] == [variant.discriminant] )
                } else {
                    true.into()
                };

                let mut same_id_fields = vec![];
                for (field_idx, field) in variant.fields.iter().enumerate() {
                    let mir_field = field_idx.into();
                    let Some(field_ty) = field.ty.as_ref().copied() else {
                        continue;
                    };
                    let field_address = address_domain
                        .adt_field_address_function(abi_variant, mir_field)?
                        .apply1(address.clone());
                    let field_ownership_domain = OwnershipDomain::encode(encoder, field_ty)?;
                    let same_id_field_fact = field_ownership_domain
                        .framed_id_shallow_fact_function()?
                        .apply3(field_address, version_1.clone(), version_2.clone());
                    same_id_fields.push(same_id_field_fact);
                }
                let same_id_fields_fact: vir::Expr = same_id_fields.into_iter().conjoin();

                let body = vir_expr!(
                    forall [address], [version_1], [version_2] ::
                    { [same_id_fact.clone()] } ::
                    (([same_id_fact] && [discriminant_condition]) ==> [same_id_fields_fact])
                );
                same_id_shallow_axioms.push(vir::DomainAxiom::new(
                    &domain_name,
                    format!("Shallow id framing definition of variant {variant_idx} of {ty_name}"),
                    format!("same_id_shallow_definition_of_variant_{variant_idx}_of_{ty_name}"),
                    body,
                ));
            }
        }
    };

    // === Axiom: Framing of moved instances ===
    let mut moved_instance_axioms = vec![];
    {
        let address_1 = vir::LocalVar::new("a1", address_type.clone());
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let address_2 = vir::LocalVar::new("a2", address_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let move_fact = df.moved_fact_function
            .apply4(address_1.clone(), version_1.clone(), address_2.clone(), version_2.clone());
        let snapshot_1 = address_domain.deref_function()?
            .apply2(address_1.clone(), version_1.clone());
        let snapshot_2 = address_domain.deref_function()?
            .apply2(address_2.clone(), version_2.clone());
        let id_1 = address_domain.id_function()?
            .apply2(address_1.clone(), version_1.clone());
        let id_2 = address_domain.id_function()?
            .apply2(address_2.clone(), version_2.clone());
        moved_instance_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            format!("Move definition of {ty_name}"),
            format!("moved_definition_of_{ty_name}"),
            vir_expr!(
                forall [address_1], [address_2], [version_1], [version_2] ::
                { [move_fact] } ::
                ([move_fact] ==> (([id_1] == [id_2]) && ([snapshot_1] == [snapshot_2])))
            ),
        ));

        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            let abi_variant = if ty.is_enum() {
                Some(variant_idx.into())
            } else {
                None
            };
            let discriminant_condition = if ty.is_enum() {
                let base_snapshot = address_domain.deref_function()?
                    .apply2(address_1.clone(), version_1.clone());
                let discr_value = snapshot_domain.discriminant_function()?.apply1(base_snapshot);
                vir_expr!( [discr_value] == [variant.discriminant] )
            } else {
                true.into()
            };

            let mut moved_fields = vec![];
            for (field_idx, field) in variant.fields.iter().enumerate() {
                let mir_field = field_idx.into();
                let Some(field_ty) = field.ty.as_ref().copied() else {
                    continue;
                };
                let field_address_1 = address_domain
                    .adt_field_address_function(abi_variant, mir_field)?
                    .apply1(address_1.clone());
                let field_address_2 = address_domain
                    .adt_field_address_function(abi_variant, mir_field)?
                    .apply1(address_2.clone());
                let field_ownership_domain = OwnershipDomain::encode(encoder, field_ty)?;
                let moved_field_fact = field_ownership_domain
                    .moved_fact_function()?
                    .apply4(field_address_1, version_1.clone(), field_address_2, version_2.clone());
                moved_fields.push(moved_field_fact);
            }
            let moved_fields_fact: vir::Expr = moved_fields.into_iter().conjoin();

            let body = vir_expr!(
                forall [address_1], [address_2], [version_1], [version_2] ::
                { [move_fact.clone()] } ::
                (([move_fact] && [discriminant_condition]) ==> [moved_fields_fact])
            );
            moved_instance_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Move definition of variant {variant_idx} of {ty_name}"),
                format!("moved_definition_of_variant_{variant_idx}_of_{ty_name}"),
                body,
            ));
        }
    }

    // === Axiom: Invariants of owning types ===
    // Owning types are those types whose snapshot contains both the address and the
    // dereferentiation of that address. For example: references, boxes, owning pointers,
    // MutexGuard etc.
    let mut owning_types_axioms = vec![];

    if let &ty::TyKind::Ref(_region, target_ty, _mutability) = ty.kind() {
        let root = vir::LocalVar::new("r", vir::Type::Int);
        let address = vir::LocalVar::new("a", address_type.clone());
        let version = vir::LocalVar::new("v", version_type.clone());
        let allocation_fact = df.ownership_at_functions[OwnershipKind::Allocated as usize]
            .apply3(root.clone(), address.clone(), version.clone());
        let target_address_domain = AddressDomain::encode(encoder, target_ty)?;
        let ref_snapshot = address_domain.deref_function()?.apply2(address.clone(), version.clone());
        let target_snapshot = snapshot_domain.target_snapshot_function()?.apply1(ref_snapshot.clone());
        let target_address = snapshot_domain.target_address_function()?.apply1(ref_snapshot);
        let target_deref = target_address_domain.deref_function()?
            .apply2(target_address, version.clone());
        let body = vir_expr!(
            forall [root], [address], [version] ::
            { [allocation_fact] } ::
            (([allocation_fact]) ==> ([target_deref] == [target_snapshot]))
        );
        owning_types_axioms.push(vir::DomainAxiom::new(
            &domain_name,
            format!("Invariant of the owning type {ty_name}"),
            format!("owning_type_invariant_of_{ty_name}"),
            body,
        ));
    }

    // === Axioms: Framing of shallowly owned places ===
    let mut shallow_ownership_axioms = vec![];

    if let &ty::TyKind::Ref(_region, target_ty, _mutability) = ty.kind() {
        let address = vir::LocalVar::new("a", address_type.clone());
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type.clone());
        let snap_1 = address_domain.deref_function()?
            .apply2(address.clone(), version_1.clone());
        let snap_2 = address_domain.deref_function()?
            .apply2(address.clone(), version_2.clone());
        let target_address_1 = snapshot_domain.target_address_function()?.apply1(snap_1);
        let target_address_2 = snapshot_domain.target_address_function()?.apply1(snap_2);
        // At program point: nothing
        { // Across stmt
            let shallow_ownership_fact = df.framing_across_stmt_functions[OwnershipKind::ShallowlyOwned as usize]
                .apply3(address.clone(), version_1.clone(), version_2.clone());
            let body = vir_expr!(
                forall [address], [version_1], [version_2] ::
                { [shallow_ownership_fact] } ::
                (([shallow_ownership_fact]) ==> ([target_address_1] == [target_address_2]))
            );
            shallow_ownership_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                "Framing across stmt of a shallowly unreachable place",
                format!("framing_across_stmt_of_shallowly_unreachable_{ty_name}"),
                body,
            ));
        }
        { // Across call
            let shallow_ownership_fact = df.framing_across_call_functions[OwnershipKind::ShallowlyOwned as usize]
                .apply3(address.clone(), version_1.clone(), version_2.clone());
            let body = vir_expr!(
                forall [address], [version_1], [version_2] ::
                { [shallow_ownership_fact] } ::
                (([shallow_ownership_fact]) ==> ([target_address_1] == [target_address_2]))
            );
            shallow_ownership_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                "Framing across call of a shallowly unreachable place",
                format!("framing_across_call_of_shallowly_unreachable_{ty_name}"),
                body,
            ));
        }
    }

    if !types::is_opaque_type(tcx, ty) && ty.is_enum() {
        let address = vir::LocalVar::new("a", address_type);
        let version_1 = vir::LocalVar::new("v1", version_type.clone());
        let version_2 = vir::LocalVar::new("v2", version_type);
        let snap_1 = address_domain.deref_function()?
            .apply2(address.clone(), version_1.clone());
        let snap_2 = address_domain.deref_function()?
            .apply2(address.clone(), version_2.clone());
        let discriminant_1 = snapshot_domain.discriminant_function()?.apply1(snap_1);
        let discriminant_2 = snapshot_domain.discriminant_function()?.apply1(snap_2);
        // At program point: nothing
        { // Across stmt
            let unreachability_fact = df.framing_across_stmt_functions[OwnershipKind::ShallowlyOwned as usize]
                .apply3(address.clone(), version_1.clone(), version_2.clone());
            let body = vir_expr!(
                forall [address], [version_1], [version_2] ::
                { [unreachability_fact] } ::
                (([unreachability_fact]) ==> ([discriminant_1] == [discriminant_2]))
            );
            shallow_ownership_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Framing across stmt of a shallowly unreachable place {ty_name}"),
                format!("framing_across_stmt_of_shallowly_unreachable_{ty_name}"),
                body,
            ));
        }
        { // Across call
            let unreachability_fact = df.framing_across_call_functions[OwnershipKind::ShallowlyOwned as usize]
                .apply3(address.clone(), version_1.clone(), version_2.clone());
            let body = vir_expr!(
                forall [address], [version_1], [version_2] ::
                { [unreachability_fact] } ::
                (([unreachability_fact]) ==> ([discriminant_1] == [discriminant_2]))
            );
            shallow_ownership_axioms.push(vir::DomainAxiom::new(
                &domain_name,
                format!("Framing across call of a shallowly unreachable place {ty_name}"),
                format!("framing_across_call_of_shallowly_unreachable_{ty_name}"),
                body,
            ));
        }
    }

    Ok(vir::Domain {
        name: domain_name,
        functions: vec![
            df.ownership_at_functions,
            df.framing_across_stmt_functions,
            df.framing_across_call_functions,
            vec![df.same_snap_fact_function, df.same_id_shallow_function, df.moved_fact_function],
        ].concat(),
        axioms: vec![
            snap_address_axioms,
            ownership_implication_axioms,
            ownership_incompatibility_axioms,
            field_ownership_axioms,
            implied_framing_axioms,
            vec![framing_snapshot_axiom],
            same_id_shallow_axioms,
            moved_instance_axioms,
            owning_types_axioms,
            shallow_ownership_axioms,
        ].concat(),
        type_vars: vec![],
    })
}

pub struct OwnershipDomain {
    domain: Option<Rc<vir::Domain>>,
    functions: Option<OwnershipDomainFunctions>,
}

impl OwnershipDomain {
    pub fn encode<'tcx>(
        encoder: &Encoder<'_, 'tcx>, ty: ty::Ty<'tcx>,
    ) -> EncodingResult<OwnershipDomain> {
        let domain_kind = BuiltinDomainKind::Ownership(ty);
        if encoder.is_encoding_builtin_domain(domain_kind)? {
            let functions = build_ownership_domain_functions(encoder, ty)?;
            Ok(OwnershipDomain {
                domain: None,
                functions: Some(functions),
            })
        } else {
            let domain = encoder.encode_builtin_domain(BuiltinDomainKind::Ownership(ty))?;
            debug_assert!(domain.name.starts_with(DOMAIN_NAME_PREFIX));
            Ok(OwnershipDomain {
                domain: Some(domain),
                functions: None,
            })
        }
    }

    /// Private helper method to get a function from the domain.
    fn get_domain_function(
        &self, name: &str, index: usize, prefix: &str,
    ) -> EncodingResult<vir::DomainFunc> {
        if let Some(domain) = self.domain.as_ref() {
            let Some(func) = domain.functions.get(index) else {
                error_internal!(
                    "cannot find function for {name} in domain {:?}:\n{:#?}",
                    domain.name, domain.functions,
                );
            };
            debug_assert!(func.name.starts_with(prefix));
            return Ok(func.clone());
        } else if let Some(df) = self.functions.as_ref() {
            let mut functions = df.ownership_at_functions.iter()
                .chain(df.framing_across_stmt_functions.iter())
                .chain(df.framing_across_call_functions.iter())
                .chain(std::iter::once(&df.same_snap_fact_function))
                .chain(std::iter::once(&df.same_id_shallow_function))
                .chain(std::iter::once(&df.moved_fact_function));
            let Some(func) = functions.nth(index) else {
                error_internal!(
                    "cannot find function for {name} in functions",
                );
            };
            debug_assert!(func.name.starts_with(prefix));
            return Ok(func.clone());
        }
        unreachable!()
    }

    /// Function that models the ownership of a memory location at a given memory version.
    pub fn ownership_fact_function(&self, kind: OwnershipKind) -> EncodingResult<vir::DomainFunc> {
        let kind_idx = kind as usize;
        let debug_name = format!("ownership kind {kind} ({kind_idx})");
        self.get_domain_function(&debug_name, kind_idx, OWNERSHIP_AT_FACT_PREFIX)
    }

    /// Function that models that at least a Immutable ownership is framed across a statement.
    pub fn framed_stmt_fact_function(&self, kind: OwnershipKind) -> EncodingResult<vir::DomainFunc> {
        let kind_idx = kind as usize;
        let debug_name = format!("framed stmt ownership kind {kind} ({kind_idx})");
        self.get_domain_function(
            &debug_name,
            OwnershipKind::iter().len() + kind_idx,
            FRAMING_ACROSS_STMT_FACT_PREFIX,
        )
    }

    /// Function that models that at least a Immutable ownership is framed across a call terminator.
    pub fn framed_call_fact_function(&self, kind: OwnershipKind) -> EncodingResult<vir::DomainFunc> {
        let kind_idx = kind as usize;
        let debug_name = format!("framed call ownership kind {kind} ({kind_idx})");
        self.get_domain_function(
            &debug_name,
            2 * OwnershipKind::iter().len() + kind_idx,
            FRAMING_ACROSS_CALL_OWNERSHIP_FACT_PREFIX,
        )
    }

    /// Function that models that a snapshot is immutable between two memory version.
    fn framed_snap_fact_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.get_domain_function(
            "framed snapshot",
            3 * OwnershipKind::iter().len(),
            SAME_SNAP_FACT_PREFIX,
        )
    }

    /// Function that models that an id is shallowly immutable between two memory version.
    fn framed_id_shallow_fact_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.get_domain_function(
            "framed id",
            3 * OwnershipKind::iter().len() + 1,
            SAME_ID_SHALLOW_FACT_PREFIX,
        )
    }

    /// Function that models that a fully-owned instance is moved between two memory locations.
    /// That is, its snapshot (including unsafe cells, but without following pointers or references)
    /// doesn't change.
    pub fn moved_fact_function(&self) -> EncodingResult<vir::DomainFunc> {
        self.get_domain_function(
            "moved instances",
            3 * OwnershipKind::iter().len() + 2,
            MOVED_FACT_PREFIX,
        )
    }
}
