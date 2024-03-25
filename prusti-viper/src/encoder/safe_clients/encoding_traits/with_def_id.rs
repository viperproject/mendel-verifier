// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

pub trait WithDefId<'v, 'tcx: 'v>: WithEncoder<'v, 'tcx> {
    fn def_id(&self) -> DefId;
    fn substs(&self) -> ty::SubstsRef<'tcx>;

    fn span(&self) -> Span {
        self.tcx().def_span(self.def_id())
    }

    fn encode_name(&self) -> String {
        self.encoder().encode_item_name(self.def_id())
    }

    fn register_span<T: Into<MultiSpan>>(&self, span: T) -> vir::Position {
        self.encoder()
            .error_manager()
            .register_span(self.def_id(), span)
    }

    fn register_error<T: Into<MultiSpan>>(&self, span: T, error_ctxt: ErrorCtxt) -> vir::Position {
        self.encoder()
            .error_manager()
            .register_error(span, error_ctxt, self.def_id())
    }
}
