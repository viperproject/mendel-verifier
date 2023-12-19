// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

pub trait WithOldMirExprEncoder<'v, 'tcx: 'v>: MirExprEncoder<'v, 'tcx> {
    fn old_mir_expr_encoder(&self) -> EncodingResult<&Self>;
}

pub trait WithOldPlaceEncoder<'v, 'tcx: 'v>: PlaceEncoder<'v, 'tcx> {
    fn old_place_encoder(&self) -> EncodingResult<&Self>;
}
