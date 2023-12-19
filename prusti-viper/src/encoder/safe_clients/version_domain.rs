// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

pub fn version_domain_name() -> String {
    "Version".to_string()
}

pub fn version_domain_type() -> vir::Type {
    vir::Type::domain(version_domain_name())
}

pub fn build_version_domain() -> vir::Domain {
    debug!("build_version_domain");
    vir::Domain {
        name: version_domain_name(),
        functions: vec![],
        axioms: vec![],
        type_vars: vec![],
    }
}
