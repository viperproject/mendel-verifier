// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

/// Trait used to encode the address of a local variable in impure code.
pub trait LocalAddressEncoder<'v, 'tcx: 'v>: WithMir<'v, 'tcx> {
    fn encode_local_name(&self, local: mir::Local) -> String {
        format!("{local:?}")
    }

    fn encode_local_address_domain(
        &self,
        local: mir::Local,
    ) -> SpannedEncodingResult<AddressDomain<'tcx>> {
        let name = self.encode_local_name(local);
        let local_ty = self.get_local_ty(local);
        let local_span = self.get_local_span(local);
        let address_domain =
            AddressDomain::encode(self.encoder(), local_ty).with_span(local_span)?;
        Ok(address_domain)
    }

    fn encode_local_address_var(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let name = self.encode_local_name(local);
        let local_ty = self.get_local_ty(local);
        let local_span = self.get_local_span(local);
        let domain_kind = BuiltinDomainKind::Address(local_ty);
        let typ = self
            .encoder()
            .encode_builtin_domain_type(domain_kind)
            .with_default_span(local_span)?;
        Ok(vir::LocalVar { name, typ })
    }
}
