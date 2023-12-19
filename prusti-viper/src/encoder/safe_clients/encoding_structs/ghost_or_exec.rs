// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use strum_macros::Display;

#[derive(Copy, Clone, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GhostOrExec {
    Ghost,
    Exec,
}

impl GhostOrExec {
    pub fn is_ghost(self) -> bool {
        self == GhostOrExec::Ghost
    }

    pub fn is_exec(self) -> bool {
        self == GhostOrExec::Exec
    }
}
