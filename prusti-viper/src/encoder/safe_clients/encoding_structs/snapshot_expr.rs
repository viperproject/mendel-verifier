// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SnapshotExpr {
    expr: vir::Expr,
    kind: SnapshotKind,
}

impl SnapshotExpr {
    pub fn new(expr: vir::Expr, mov: SnapshotKind) -> Self {
        Self { expr, kind: mov }
    }

    pub fn new_memory(expr: vir::Expr) -> Self {
        Self::new(expr, SnapshotKind::Memory)
    }

    pub fn new_value(expr: vir::Expr) -> Self {
        Self::new(expr, SnapshotKind::Value)
    }

    pub fn expr(&self) -> &vir::Expr {
        &self.expr
    }

    pub fn kind(&self) -> SnapshotKind {
        self.kind
    }

    pub fn into_expr(self) -> vir::Expr {
        self.expr
    }
}

impl From<SnapshotExpr> for vir::Expr {
    fn from(val: SnapshotExpr) -> vir::Expr {
        val.expr
    }
}
