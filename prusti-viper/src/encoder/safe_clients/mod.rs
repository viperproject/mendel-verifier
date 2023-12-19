// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unreachable_code)]
#![allow(unused_variables, dead_code, unused_assignments, unused_mut)]
#![allow(clippy::diverging_sub_expression, clippy::never_loop)]
#![allow(clippy::module_inception)]

pub mod procedure_encoder;
pub mod pure_encoder;
pub mod version_domain;
pub mod address_domain;
pub mod ownership_domain;
pub mod bump_version;
pub mod prelude;
pub mod scalars;
pub mod types;
pub mod type_layout;
pub mod encoding_traits;
pub mod encoding_structs;
pub mod snapshot_domains;
pub mod library_ownership;
