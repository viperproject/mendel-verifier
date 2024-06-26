// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{
    errors::EncodingResult,
    high::builtin_functions::HighBuiltinFunctionEncoderInterface,
    safe_clients::{
        address_domain, bump_version, ownership_domain,
        snapshot_domains::{mem_snapshot_domain, value_snapshot_domain},
        version_domain,
    },
};
use log::debug;
use prusti_common::{vir_expr, vir_local};
use prusti_rustc_interface::middle::ty;
use vir_crate::{
    common::identifier::WithIdentifier,
    polymorphic::{self as vir},
};

const PRIMITIVE_VALID_DOMAIN_NAME: &str = "PrimitiveValidDomain";
const NAT_DOMAIN_NAME: &str = "NatDomain";

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinMethodKind {
    Havoc(vir::Type),
    BumpVersion,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinFunctionKind {
    /// type
    Unreachable(vir::Type),
    /// type
    Undefined(vir::Type),
    /// array lookup pure function
    ArrayLookupPure {
        array_pred_type: vir::Type,
        elem_pred_type: vir::Type,
        array_len: usize,
        return_ty: vir::Type,
    },
    /// lookup_pure function for slices
    SliceLookupPure {
        slice_pred_type: vir::Type,
        elem_pred_type: vir::Type,
        return_ty: vir::Type,
    },
    /// abstract length function for slices
    SliceLen {
        slice_pred_type: vir::Type,
        elem_pred_type: vir::Type,
    },
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinDomainKind<'tcx> {
    Nat,
    Primitive,
    Version,
    Address(ty::Ty<'tcx>),
    MemorySnapshot(ty::Ty<'tcx>),
    ValueSnapshot(ty::Ty<'tcx>),
    Ownership(ty::Ty<'tcx>),
}

pub struct BuiltinEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p super::Encoder<'v, 'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> BuiltinEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p super::Encoder<'v, 'tcx>) -> Self {
        Self { encoder }
    }

    pub fn encode_builtin_method_name(&self, method: &BuiltinMethodKind) -> String {
        match method {
            BuiltinMethodKind::Havoc(vir_ty) => {
                let ty_name = vir_ty.name();
                format!("builtin$havoc_{ty_name}")
            }
            BuiltinMethodKind::BumpVersion => bump_version::bump_version_method_name(),
        }
    }

    pub fn encode_builtin_method_def(
        &self,
        method: &BuiltinMethodKind,
    ) -> EncodingResult<vir::BodylessMethod> {
        debug!("encode_builtin_method_def {:?}", method);
        match method {
            BuiltinMethodKind::Havoc(vir_ty) => {
                let method_name = self.encode_builtin_method_name(method);
                Ok(vir::BodylessMethod {
                    name: method_name,
                    formal_args: vec![],
                    formal_returns: vec![vir_local! { ret: {vir_ty.clone()} }],
                    pres: vec![],
                    posts: vec![],
                })
            }
            BuiltinMethodKind::BumpVersion => bump_version::build_bump_version_method(self.encoder),
        }
    }

    pub fn encode_builtin_function_def(&self, function: BuiltinFunctionKind) -> vir::Function {
        debug!("encode_builtin_function_def {:?}", function);
        let (fn_name, type_arguments) = self
            .encoder
            .encode_builtin_function_name_with_type_args(&function);
        match function {
            BuiltinFunctionKind::Unreachable(typ) => vir::Function {
                name: fn_name,
                type_arguments,
                formal_args: vec![],
                return_type: typ,
                // Precondition is false, because we want to be sure that this function is never used
                pres: vec![false.into()],
                posts: vec![],
                body: None,
            },
            BuiltinFunctionKind::Undefined(typ) => vir::Function {
                name: fn_name,
                type_arguments,
                formal_args: vec![],
                return_type: typ,
                pres: vec![],
                posts: vec![],
                body: None,
            },
            BuiltinFunctionKind::ArrayLookupPure {
                array_pred_type,
                array_len,
                return_ty,
                ..
            } => {
                let self_var = vir::LocalVar::new("self", array_pred_type.clone());
                let idx_var = vir_local! { idx: Int };

                vir::Function {
                    name: fn_name,
                    type_arguments,
                    formal_args: vec![
                        // self,
                        self_var.clone(),
                        // idx,
                        idx_var.clone(),
                    ],
                    return_type: return_ty,
                    pres: vec![
                        // acc(self, read$())
                        vir::Expr::predicate_access_predicate(
                            array_pred_type,
                            vir::Expr::local(self_var),
                            vir::PermAmount::Read,
                        ),
                        // 0 <= idx < {len}
                        vir_expr! { [vir::Expr::from(0u32)] <= [vir::Expr::local(idx_var.clone())] },
                        vir_expr!([vir::Expr::local(idx_var)] < [vir::Expr::from(array_len)]),
                    ],
                    posts: vec![],
                    body: None,
                }
            }
            BuiltinFunctionKind::SliceLookupPure {
                slice_pred_type,
                elem_pred_type,
                return_ty,
            } => {
                let (slice_len, slice_len_type_arguments) = self
                    .encoder
                    .encode_builtin_function_name_with_type_args(&BuiltinFunctionKind::SliceLen {
                        slice_pred_type: slice_pred_type.clone(),
                        elem_pred_type,
                    });
                let self_var = vir::LocalVar::new("self", slice_pred_type.clone());
                let idx_var = vir_local! { idx: Int };

                let slice_len_call = vir::Expr::func_app(
                    slice_len,
                    slice_len_type_arguments,
                    vec![vir::Expr::local(self_var.clone())],
                    vec![self_var.clone()],
                    vir::Type::Int,
                    vir::Position::default(),
                );

                vir::Function {
                    name: fn_name,
                    type_arguments,
                    formal_args: vec![self_var.clone(), idx_var.clone()],
                    return_type: return_ty,
                    pres: vec![
                        // acc(self, read$())
                        vir::Expr::predicate_access_predicate(
                            slice_pred_type,
                            vir::Expr::local(self_var),
                            vir::PermAmount::Read,
                        ),
                        // 0 <= idx < Slice${ty}$len(self)
                        vir_expr! { [vir::Expr::from(0u32)] <= [vir::Expr::local(idx_var.clone())] },
                        vir_expr! { [vir::Expr::local(idx_var)] < [slice_len_call] },
                    ],
                    posts: vec![],
                    body: None,
                }
            }
            BuiltinFunctionKind::SliceLen {
                slice_pred_type, ..
            } => {
                let self_var = vir::LocalVar::new("self", slice_pred_type.clone());

                vir::Function {
                    name: fn_name,
                    type_arguments,
                    formal_args: vec![self_var.clone()],
                    return_type: vir::Type::Int,
                    pres: vec![vir::Expr::predicate_access_predicate(
                        slice_pred_type,
                        vir::Expr::local(self_var),
                        vir::PermAmount::Read,
                    )],
                    posts: vec![
                        vir_expr! { [vir::Expr::from(vir_local!{ __result: Int })] >= [vir::Expr::from(0)] },
                        // TODO: We should use a symbolic value for usize::MAX.
                        vir_expr! { [vir::Expr::from(vir_local!{ __result: Int })] <= [vir::Expr::from(usize::MAX)] },
                    ],
                    body: None,
                }
            }
        }
    }

    pub fn encode_builtin_domain_name(
        &self,
        kind: BuiltinDomainKind<'tcx>,
    ) -> EncodingResult<String> {
        debug!("encode_builtin_domain_name {:?}", kind);
        Ok(match kind {
            BuiltinDomainKind::Nat => NAT_DOMAIN_NAME.to_string(),
            BuiltinDomainKind::Primitive => PRIMITIVE_VALID_DOMAIN_NAME.to_string(),
            BuiltinDomainKind::Version => version_domain::version_domain_name(),
            BuiltinDomainKind::Address(ty) => {
                address_domain::address_domain_name(self.encoder, ty)?
            }
            BuiltinDomainKind::MemorySnapshot(ty) => {
                mem_snapshot_domain::mem_snapshot_domain_name(self.encoder, ty)?
            }
            BuiltinDomainKind::ValueSnapshot(ty) => {
                value_snapshot_domain::value_snapshot_domain_name(self.encoder, ty)?
            }
            BuiltinDomainKind::Ownership(ty) => {
                ownership_domain::ownership_domain_name(self.encoder, ty)?
            }
        })
    }

    pub fn encode_builtin_domain(
        &self,
        kind: BuiltinDomainKind<'tcx>,
    ) -> EncodingResult<vir::Domain> {
        debug!("encode_builtin_domain {:?}", kind);
        let domain = match kind {
            BuiltinDomainKind::Nat => self.encode_nat_builtin_domain(),
            BuiltinDomainKind::Primitive => self.encode_primitive_builtin_domain(),
            BuiltinDomainKind::Version => version_domain::build_version_domain(),
            BuiltinDomainKind::Address(ty) => {
                address_domain::build_address_domain(self.encoder, ty)?
            }
            BuiltinDomainKind::MemorySnapshot(ty) => {
                mem_snapshot_domain::build_mem_snapshot_domain(self.encoder, ty)?
            }
            BuiltinDomainKind::ValueSnapshot(ty) => {
                value_snapshot_domain::build_value_snapshot_domain(self.encoder, ty)?
            }
            BuiltinDomainKind::Ownership(ty) => {
                ownership_domain::build_ownership_domain(self.encoder, ty)?
            }
        };
        debug_assert_eq!(
            domain.get_identifier(),
            self.encode_builtin_domain_name(kind)?
        );
        Ok(domain)
    }

    pub fn encode_builtin_domain_type(
        &self,
        kind: BuiltinDomainKind<'tcx>,
    ) -> EncodingResult<vir::Type> {
        Ok(match kind {
            BuiltinDomainKind::Nat | BuiltinDomainKind::Primitive => {
                vir::Type::domain(self.encode_builtin_domain(kind)?.name)
            }
            BuiltinDomainKind::Version => version_domain::version_domain_type(),
            BuiltinDomainKind::Address(ty) => {
                address_domain::address_domain_type(self.encoder, ty)?
            }
            BuiltinDomainKind::MemorySnapshot(ty) => {
                mem_snapshot_domain::mem_snapshot_domain_type(self.encoder, ty)?
            }
            BuiltinDomainKind::ValueSnapshot(ty) => {
                value_snapshot_domain::value_snapshot_domain_type(self.encoder, ty)?
            }
            BuiltinDomainKind::Ownership(ty) => {
                ownership_domain::ownership_domain_type(self.encoder, ty)?
            }
        })
    }

    fn encode_nat_builtin_domain(&self) -> vir::Domain {
        let nat_domain_name = NAT_DOMAIN_NAME;
        let zero = vir::DomainFunc {
            name: "zero".to_owned(),
            type_arguments: vec![],
            formal_args: vec![],
            return_type: vir::Type::domain(nat_domain_name.to_owned()),
            unique: false,
            domain_name: nat_domain_name.to_owned(),
        };

        let functions = vec![zero]; // , snapshot::get_succ_func()];

        vir::Domain {
            name: nat_domain_name.to_owned(),
            functions,
            axioms: vec![],
            type_vars: vec![],
        }
    }

    fn encode_primitive_builtin_domain(&self) -> vir::Domain {
        //FIXME this does not check or handle the different sizes of primitve types
        let domain_name = PRIMITIVE_VALID_DOMAIN_NAME;

        let mut functions = vec![];
        let mut axioms = vec![];

        for t in &[vir::Type::Bool, vir::Type::Int] {
            //let f = snapshot::valid_func_for_type(t);
            let f = {
                let domain_name: String = match t {
                    // vir::Type::Domain(name) => name.clone(),
                    vir::Type::Bool | vir::Type::Int => domain_name.to_string(),
                    // vir::Type::TypedRef(_) => unreachable!(),
                    // vir::Type::TypeVar(_) => unreachable!(),
                    // vir::Type::Snapshot(_) => unreachable!(),
                    _ => unreachable!(),
                };

                let arg_typ: vir::Type = match t {
                    // vir::Type::Domain(vir::DomainType{label, ..}) => vir::Type::domain(label.clone()),
                    vir::Type::Bool => vir::Type::Bool,
                    vir::Type::Int => vir::Type::Int,
                    // vir::Type::TypedRef(_) => unreachable!(),
                    // vir::Type::TypeVar(_) => unreachable!(),
                    // vir::Type::Snapshot(_) => unreachable!(),
                    _ => unreachable!(),
                };

                let self_arg = vir::LocalVar::new("self", arg_typ);
                vir::DomainFunc {
                    name: format!("{domain_name}$valid"),
                    type_arguments: vec![], // FIXME: This is most likely wrong.
                    formal_args: vec![self_arg],
                    return_type: vir::Type::Bool,
                    unique: false,
                    domain_name,
                }
            };
            functions.push(f.clone());

            let forall_arg = vir_local! { self: {t.clone()} };
            let function_app =
                vir::Expr::domain_func_app(f.clone(), vec![vir::Expr::local(forall_arg.clone())]);
            let body = vir::Expr::forall(
                vec![forall_arg],
                vec![vir::Trigger::new(vec![function_app.clone()])],
                function_app,
            );
            let axiom = vir::DomainAxiom {
                comment: None,
                name: format!("{}$axiom", f.get_identifier()),
                expr: body,
                domain_name: domain_name.to_string(),
            };
            axioms.push(axiom);
        }

        vir::Domain {
            name: domain_name.to_owned(),
            functions,
            axioms,
            type_vars: vec![],
        }
    }
}
