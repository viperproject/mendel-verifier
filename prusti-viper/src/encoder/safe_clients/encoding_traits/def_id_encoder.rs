// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use prusti_interface::specs::typed::ProcedureSpecificationKind;
use crate::encoder::mir::specifications::SpecificationsInterface;

/// Trait used to encode items with a DefId.
pub trait DefIdEncoder<'v, 'tcx: 'v>: WithDefId<'v, 'tcx> {
    fn check_call(&self, called_def_id: DefId, call_substs: ty::SubstsRef<'tcx>, call_span: Span) -> SpannedEncodingResult<()> {
        let self_kind = self.encoder().get_proc_kind(self.def_id(), Some(self.substs()));
        let called_kind = self.encoder().get_proc_kind(called_def_id, Some(call_substs));
        use ProcedureSpecificationKind::*;
        match (self_kind, called_kind) {
            // Good
            (Impure, Impure | PureUnstable | PureMemory | Predicate(_) | Pure)
            | (PureUnstable, PureUnstable | PureMemory | Predicate(_) | Pure)
            | (PureMemory, PureMemory | Predicate(_) | Pure)
            | (Predicate(_) | Pure, Predicate(_) | Pure) => {} // Ok
            // Bad
            (PureUnstable | PureMemory | Predicate(_) | Pure, Impure) => {
                error_incorrect!(call_span => "pure functions cannot call impure functions");
            }
            (PureMemory, PureUnstable) => {
                error_incorrect!(call_span => "pure memory functions cannot call pure unstable functions");
            }
            (Predicate(_) | Pure, PureUnstable) => {
                error_incorrect!(call_span => "pure stable functions cannot call pure unstable functions");
            }
            (Predicate(_) | Pure, PureMemory) => {
                error_incorrect!(call_span => "pure stable functions cannot call pure memory functions");
            }
        }
        Ok(())
    }
}
