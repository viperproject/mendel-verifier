// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

pub trait WithLocalTy<'v, 'tcx: 'v>: WithEncoder<'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx>;

    fn get_place_ty(&self, place: mir::Place<'tcx>) -> PlaceTy<'tcx> {
        place.projection.iter().fold(
            PlaceTy::from_ty(self.get_local_ty(place.local)),
            |place_ty, elem| place_ty.projection_ty(self.tcx(), elem),
        )
    }

    fn get_operand_ty(&self, operand: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        match operand {
            &mir::Operand::Copy(l) | &mir::Operand::Move(l) => self.get_place_ty(l).ty,
            mir::Operand::Constant(c) => c.literal.ty(),
        }
    }
}
