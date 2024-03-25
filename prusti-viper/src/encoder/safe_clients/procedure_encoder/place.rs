// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::{prelude::*, procedure_encoder::*};

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    /// All derefs will use the old memory version.
    pub(super) fn encode_rvalue_snapshot(
        &self,
        rhs: &mir::Rvalue<'tcx>,
        version_kind: Version,
    ) -> EncodingResult<vir::Expr> {
        let expr = self
            .fixed_version_encoder(version_kind)
            .encode_rvalue_expr_snapshot(&RvalueExpr::from_rvalue(rhs, None)?, GhostOrExec::Exec)?;
        if !expr.kind().is_memory() {
            error_internal!("cannot determine the address of rvalue '{rhs:?}'")
        }
        Ok(expr.into_expr())
    }

    /// All derefs will use the old memory version.
    pub(super) fn encode_operand_snapshot(
        &self,
        operand: &mir::Operand<'tcx>,
        version_kind: Version,
    ) -> EncodingResult<vir::Expr> {
        debug_assert_eq!(version_kind, Version::Old); // I currently only use this.
        let expr = self
            .fixed_version_encoder(version_kind)
            .encode_rvalue_expr_snapshot(&RvalueExpr::from_operand(operand)?, GhostOrExec::Exec)?;
        if !expr.kind().is_memory() {
            error_internal!("cannot determine the address of operand '{operand:?}'")
        }
        Ok(expr.into_expr())
    }

    pub(super) fn encode_place_address(
        &self,
        place: mir::Place<'tcx>,
        version_kind: Version,
    ) -> EncodingResult<vir::Expr> {
        let opt_result = self
            .fixed_version_encoder(version_kind)
            .encode_place_address(place)?;
        if let Some(encoded_addr) = opt_result {
            Ok(encoded_addr)
        } else {
            error_internal!("cannot determine the address of place '{place:?}'");
        }
    }

    pub(super) fn encode_place_snapshot(
        &self,
        place: mir::Place<'tcx>,
        version_kind: Version,
    ) -> EncodingResult<vir::Expr> {
        trace!("encode_place_snapshot({:?})", place);
        // The returned expression should be equivalent to
        // `deref(self.encode_place_address(place))`.
        // Maybe we can generate a consistency check assertion.
        let expr = self
            .fixed_version_encoder(version_kind)
            .encode_place_snapshot(place)?;
        if !expr.kind().is_memory() {
            error_internal!("cannot determine the address of place '{place:?}'")
        }
        Ok(expr.into_expr())
    }
}
