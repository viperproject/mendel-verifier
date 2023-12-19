// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

pub trait WithSig<'v, 'tcx: 'v>: WithDefId<'v, 'tcx> + WithLocalTy<'v, 'tcx> {
    fn sig(&self) -> ty::PolyFnSig<'tcx>;

    fn impl_get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.get_local_binder_ty(local).skip_binder()
    }

    fn get_local_binder_ty(&self, local: mir::Local) -> ty::Binder<'tcx, ty::Ty<'tcx>> {
        if local == mir::RETURN_PLACE {
            self.sig().output()
        } else {
            self.sig().input(local.index() - 1)
        }
    }
}
