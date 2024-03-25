// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

pub fn bump_version_method_name() -> String {
    "bumpVersion".to_string()
}

pub fn build_bump_version_method<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
) -> EncodingResult<vir::BodylessMethod> {
    let version_domain_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)?;
    let arg = vir_local!(version: {version_domain_type.clone()});
    let target = vir_local!(new_version: {version_domain_type});
    Ok(vir::BodylessMethod {
        name: bump_version_method_name(),
        formal_args: vec![arg],
        formal_returns: vec![target],
        pres: vec![],
        posts: vec![],
    })
}
