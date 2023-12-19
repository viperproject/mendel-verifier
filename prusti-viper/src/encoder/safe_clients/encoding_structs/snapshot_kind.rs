// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use strum_macros::Display;
use crate::encoder::safe_clients::prelude::*;

#[derive(Copy, Clone, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SnapshotKind {
    Memory,
    Value,
}

impl SnapshotKind {
    pub fn is_memory(self) -> bool {
        self == SnapshotKind::Memory
    }

    pub fn is_value(self) -> bool {
        self == SnapshotKind::Value
    }

    pub fn with_expr(self, expr: vir::Expr) -> SnapshotExpr {
        SnapshotExpr::new(expr, self)
    }
}
