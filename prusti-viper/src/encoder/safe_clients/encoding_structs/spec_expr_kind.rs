// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use crate::encoder::safe_clients::prelude::*;
use strum_macros::Display;

#[derive(Copy, Clone, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecExprKind {
    Pre,
    Post,
    Pledge(DefId),
}

impl SpecExprKind {
    pub fn is_pre(self) -> bool {
        self == SpecExprKind::Pre
    }

    pub fn is_post(self) -> bool {
        self == SpecExprKind::Post
    }

    pub fn is_pledge(self) -> bool {
        matches!(self, SpecExprKind::Pledge(_))
    }

    pub fn is_post_or_pledge(self) -> bool {
        matches!(self, SpecExprKind::Post | SpecExprKind::Pledge(_))
    }
}
