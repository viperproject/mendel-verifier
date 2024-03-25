// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

/// Trait used to encode type arguments.
pub trait SubstsEncoder<'v, 'tcx: 'v>: WithDefId<'v, 'tcx> {
    fn encode_substs(&self, args: ty::SubstsRef<'tcx>) -> EncodingResult<Vec<vir::Type>> {
        args.iter()
            // TODO(tymap): ignoring const params and lifetimes for now
            .filter_map(|generic| match generic.unpack() {
                ty::subst::GenericArgKind::Type(ty) => Some(ty),
                _ => None,
            })
            .map(|ty| {
                self.encoder()
                    .encode_builtin_domain_type(BuiltinDomainKind::MemorySnapshot(ty))
            })
            .collect::<Result<Vec<_>, _>>()
    }
}
