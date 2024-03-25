// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

/// Used by the `MirInterpreter` to convert a MIR body to a `MirExpr`.
#[derive(Clone, Debug)]
pub struct MirInterpreterState<'tcx> {
    pub expr: Option<MirExpr<'tcx>>,
}

impl<'tcx> MirInterpreterState<'tcx> {
    pub fn new(expr: Option<MirExpr<'tcx>>) -> Self {
        MirInterpreterState { expr }
    }

    pub fn new_undefined() -> Self {
        MirInterpreterState { expr: None }
    }

    pub fn new_defined(expr: MirExpr<'tcx>) -> Self {
        MirInterpreterState { expr: Some(expr) }
    }

    pub fn expr(&self) -> Option<&MirExpr<'tcx>> {
        self.expr.as_ref()
    }

    pub fn expr_mut(&mut self) -> Option<&mut MirExpr<'tcx>> {
        self.expr.as_mut()
    }

    pub fn normalize(&mut self) {
        if let Some(expr) = self.expr.as_mut() {
            expr.normalize();
        }
    }

    pub fn into_expr(self) -> Option<MirExpr<'tcx>> {
        self.expr
    }

    pub fn replace_local(
        &mut self,
        target: mir::Local,
        replacement: MirExpr<'tcx>,
    ) -> EncodingResult<()> {
        trace!("replace {:?} --> {:?}", target, replacement);
        let visitor = |expr_local: mir::Local| -> EncodingResult<_> {
            if expr_local == target {
                Ok(Some(replacement.clone()))
            } else {
                Ok(None)
            }
        };
        if let Some(expr) = self.expr.as_mut() {
            expr.replace_locals(&visitor)?;
        }
        Ok(())
    }
}
