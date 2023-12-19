// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod fixed_version_encoder;
mod procedure_encoder;
mod version;
mod ownership;
mod place;
mod statement;
mod terminator;
mod call;
mod local_address_encoder;
mod assertion;

pub use procedure_encoder::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Version {
    Pre,
    Old,
    OldPre,
    CurrPre,
    CurrOld,
}

impl Version {
    pub fn is_curr(self) -> bool {
        self == Version::CurrPre || self == Version::CurrOld
    }
}
