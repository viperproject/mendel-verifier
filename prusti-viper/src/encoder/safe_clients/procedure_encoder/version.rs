// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::safe_clients::procedure_encoder::*;

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    /// Encode a version bump
    pub(super) fn encode_version_bump(&self) -> EncodingResult<Vec<vir::Stmt>> {
        trace!("Encode version bump");
        let bump_version_method = self.encoder.encode_builtin_method_use(
            &BuiltinMethodKind::BumpVersion,
        )?;

        // Bump memory version
        Ok(vec![
            vir::Stmt::Assign(vir::Assign {
                target: self.encode_version(Version::Old).into(),
                source: self.encode_version(Version::CurrOld).into(),
                kind: vir::AssignKind::Ghost,
            }),
            vir::Stmt::MethodCall(vir::MethodCall {
                method_name: bump_version_method,
                arguments: vec![self.encode_version(Version::CurrOld).into()],
                targets: vec![self.encode_version(Version::CurrOld)],
            })
        ])
    }
}
