// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::mir::pure::FunctionCallInfo;

/// Trait used to encode a pure function, trigger or predicate to a `vir::Function`.
pub(crate) trait CommonPureEncoder<'v, 'tcx: 'v>: WithSig<'v, 'tcx> + PlaceEncoder<'v, 'tcx> + ContractEncoder<'v, 'tcx> + SubstsEncoder<'v, 'tcx> + Sized {
    fn caller_def_id(&self) -> DefId;
    fn get_local_span(&self, local: mir::Local) -> Span;

    fn impl_encode_local_snapshot(&self, local: mir::Local) -> SpannedEncodingResult<SnapshotExpr> {
        let expr = self.encode_local_snapshot_var(local)?.into();
        Ok(if self.is_pure_stable(None, self.def_id(), self.substs()) {
            SnapshotExpr::new_value(expr)
        } else {
            SnapshotExpr::new_memory(expr)
        })
    }

    fn encode_local_name(&self, local: mir::Local) -> String {
        if local == mir::RETURN_PLACE {
            // The conversion from VIR to Viper will special-case this name.
            "__result".to_string()
        } else {
            format!("{local:?}")
        }
    }

    fn encode_local_snapshot_var(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let name = self.encode_local_name(local);
        let local_ty = self.get_local_ty(local);
        let local_span = self.get_local_span(local);
        let domain_kind = if self.is_pure_stable(None, self.def_id(), self.substs()) {
            BuiltinDomainKind::ValueSnapshot(local_ty)
        } else {
            BuiltinDomainKind::MemorySnapshot(local_ty)
        };
        let typ = self.encoder().encode_builtin_domain_type(domain_kind).with_span(local_span)?;
        Ok(vir::LocalVar { name, typ })
    }

    fn encode_formal_args(&self) -> SpannedEncodingResult<Vec<vir::LocalVar>> {
        let mut formal_args = vec![];
        for arg in iter_args(self) {
            formal_args.push(self.encode_local_snapshot_var(arg)?);
        }
        if self.is_pure_unstable(None, self.def_id(), self.substs()) {
            let version_type = self.encoder().encode_builtin_domain_type(BuiltinDomainKind::Version)
                .with_span(self.span())?;
            formal_args.push(vir::LocalVar::new("__version", version_type));
        }
        Ok(formal_args)
    }

    fn encode_stub_function(&self) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_name();
        debug!("Encode stub pure function {function_name}");

        let info = self.encode_function_call_info()?;

        Ok(vir::Function {
            name: info.name,
            type_arguments: info.type_arguments,
            formal_args: info.formal_args,
            return_type: info.return_type,
            pres: vec![false.into()],
            posts: vec![],
            body: None,
        })
    }

    fn encode_function_given_body(
        &self,
        body: Option<vir::Expr>,
    ) -> SpannedEncodingResult<vir::Function> {
        if let Some(actual_body) = &body {
            debug!("Encode pure function {} given body {actual_body}", self.encode_name());
        } else {
            debug!("Encode pure function {} given body None", self.encode_name());
        }

        // Check types
        if !self.is_ghost(None, self.def_id()) {
            check_args_and_result_are_copy(self)?;
        }

        let default_pos = self.register_error(self.span(), ErrorCtxt::PureFunctionDefinition);
        let preconditions = self.encode_contract_expr(SpecExprKind::Pre)?
            .into_iter().map(|e| e.set_default_pos(default_pos)).collect();
        let postconditions = self.encode_contract_expr(SpecExprKind::Post)?
            .into_iter().map(|e| e.set_default_pos(default_pos)).collect();
        let info = self.encode_function_call_info()?;

        Ok(vir::Function {
            name: info.name,
            type_arguments: info.type_arguments,
            formal_args: info.formal_args,
            return_type: info.return_type,
            pres: preconditions,
            posts: postconditions,
            body,
        })
    }

    /// Encodes the information to call the pure function (stable or unstable) being encoded.
    fn encode_function_call_info(&self) -> SpannedEncodingResult<FunctionCallInfo> {
        Ok(FunctionCallInfo {
            name: self.encode_name(),
            type_arguments: self.encode_substs(self.substs()).with_span(self.span())?,
            formal_args: self.encode_formal_args()?,
            return_type: self.encode_local_snapshot_var(mir::RETURN_PLACE)?.typ,
        })
    }

    /// Encodes the version to be used in pure (stable or unstable) function definitions.
    fn default_version(&self) -> EncodingResult<Option<vir::LocalVar>> {
        if self.is_pure_unstable(None, self.def_id(), self.substs()) {
            let version_type = self.encoder()
                .encode_builtin_domain_type(BuiltinDomainKind::Version)?;
            Ok(Some(vir::LocalVar::new("__version", version_type)))
        } else {
            Ok(None)
        }
    }
}

fn check_args_and_result_are_copy<'v, 'tcx: 'v>(
    this: &impl CommonPureEncoder<'v, 'tcx>,
) -> SpannedEncodingResult<()> {
    for local in iter_locals(this) {
        let local_ty = this.get_local_binder_ty(local);
        if !this.env().query.type_is_copy(local_ty, this.caller_def_id()) {
            if local == mir::RETURN_PLACE {
                error_incorrect!(this.get_local_span(local) =>
                    "non-ghost pure function return type must be Copy"
                );
            } else {
                error_incorrect!(this.get_local_span(local) =>
                    "non-ghost pure function argument type must be Copy"
                );
            }
        }
    }
    Ok(())
}

fn iter_locals<'v, 'tcx: 'v>(this: &impl CommonPureEncoder<'v, 'tcx>) -> impl Iterator<Item = mir::Local> {
    (0..this.sig().inputs_and_output().skip_binder().len()).map(mir::Local::from_usize)
}

fn iter_args<'v, 'tcx: 'v>(this: &impl CommonPureEncoder<'v, 'tcx>) -> impl Iterator<Item = mir::Local> {
    iter_locals(this).skip(1)
}
