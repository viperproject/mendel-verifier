// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use strum_macros::Display;

#[derive(Copy, Clone, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CallOrStmt {
    Call,
    Stmt,
}

impl CallOrStmt {
    pub fn is_call(self) -> bool {
        self == CallOrStmt::Call
    }

    pub fn is_stmt(self) -> bool {
        self == CallOrStmt::Stmt
    }
}
