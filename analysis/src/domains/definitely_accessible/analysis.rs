// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::{
        DefinitelyAccessibleState, DefinitelyInitializedAnalysis, DefinitelyInitializedState,
        MaybeBorrowedAnalysis, MaybeBorrowedState,
    },
    mir_utils::{is_prefix, remove_place_from_set},
    PointwiseState,
};
use prusti_rustc_interface::{
    borrowck::consumers::{LocationTable, PoloniusInput, PoloniusOutput},
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

pub struct DefinitelyAccessibleAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> DefinitelyAccessibleAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, body: &'mir mir::Body<'tcx>) -> Self {
        DefinitelyAccessibleAnalysis { tcx, def_id, body }
    }

    pub fn run_analysis(
        &self,
        input_facts: &PoloniusInput,
        output_facts: &PoloniusOutput,
        location_table: &LocationTable,
    ) -> AnalysisResult<PointwiseState<'mir, 'tcx, DefinitelyAccessibleState<'tcx>>> {
        let def_init_analysis =
            DefinitelyInitializedAnalysis::new_relaxed(self.tcx, self.def_id, self.body);
        let borrowed_analysis = MaybeBorrowedAnalysis::new(self.tcx, self.body);
        let def_init = def_init_analysis.run_fwd_analysis()?;
        let borrowed = borrowed_analysis.run_analysis(input_facts, output_facts, location_table)?;
        let var_live_on_entry: FxHashMap<_, _> = output_facts
            .var_live_on_entry
            .iter()
            .map(|(&point, live_vars)| (point, FxHashSet::from_iter(live_vars.iter().cloned())))
            .collect();
        let empty_locals_set: FxHashSet<mir::Local> = FxHashSet::default();
        let mut analysis_state = PointwiseState::default(self.body);

        for (block, block_data) in self.body.basic_blocks.iter_enumerated() {
            // Initialize the state before each statement
            for statement_index in 0..=block_data.statements.len() {
                let location = mir::Location {
                    block,
                    statement_index,
                };
                let def_init_before = def_init
                    .lookup_before(location)
                    .unwrap_or_else(|| panic!("No 'def_init' state before location {location:?}"));
                let borrowed_before = borrowed
                    .lookup_before(location)
                    .unwrap_or_else(|| panic!("No 'borrowed' state before location {location:?}"));
                let liveness_before = var_live_on_entry
                    .get(&location_table.start_index(location))
                    .unwrap_or(&empty_locals_set);
                let state = self.compute_accessible_state(
                    def_init_before,
                    borrowed_before,
                    liveness_before,
                );
                state.check_invariant(location);
                analysis_state.set_before(location, state);
            }

            // Initialize the state of successors of terminators
            let def_init_after_block = def_init
                .lookup_after_block(block)
                .unwrap_or_else(|| panic!("No 'def_init' state after block {block:?}"));
            let borrowed_after_block = borrowed
                .lookup_after_block(block)
                .unwrap_or_else(|| panic!("No 'borrowed' state after block {block:?}"));
            let available_after_block = analysis_state.lookup_mut_after_block(block);
            for successor in block_data.terminator().successors() {
                let def_init_after = def_init_after_block.get(&successor).unwrap_or_else(|| {
                    panic!("No 'def_init' state from {block:?} to {successor:?}")
                });
                let borrowed_after = borrowed_after_block.get(&successor).unwrap_or_else(|| {
                    panic!("No 'borrowed' state from {block:?} to {successor:?}")
                });
                let liveness_after = var_live_on_entry
                    .get(&location_table.start_index(successor.start_location()))
                    .unwrap_or(&empty_locals_set);
                let state =
                    self.compute_accessible_state(def_init_after, borrowed_after, liveness_after);
                state.check_invariant(successor);
                available_after_block.insert(successor, state);
            }
        }

        Ok(analysis_state)
    }

    /// Compute the `definitely_available` state by subtracting the `maybe_borrowed` state from
    /// the `definitely_initialized` one.
    fn compute_accessible_state(
        &self,
        def_init: &DefinitelyInitializedState<'mir, 'tcx>,
        borrowed: &MaybeBorrowedState<'tcx>,
        live_vars: &FxHashSet<mir::Local>,
    ) -> DefinitelyAccessibleState<'tcx> {
        let mut definitely_accessible: FxHashSet<_> = def_init.get_def_init_places().clone();
        for (local, local_decl) in self.body.local_decls.iter_enumerated() {
            let has_lifetimes = self.tcx.any_free_region_meets(&local_decl.ty, |_| true);
            // The borrow checker expires loans as soon as the borrow is no longer used.
            let maybe_expired = !live_vars.contains(&local)
                && borrowed
                    .get_maybe_shared_borrowed()
                    .iter()
                    .all(|&p| !is_prefix(p, local.into()));
            // Reference-typed arguments cannot expire inside the function.
            let cannot_expire = matches!(
                self.body.local_kind(local),
                mir::LocalKind::Arg | mir::LocalKind::ReturnPointer
            );
            if has_lifetimes && maybe_expired && !cannot_expire {
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    local.into(),
                    &mut definitely_accessible,
                );
            }
        }
        for &place in borrowed.get_maybe_mut_borrowed().iter() {
            remove_place_from_set(self.body, self.tcx, place, &mut definitely_accessible);
        }
        let mut definitely_owned = definitely_accessible.clone();
        for &place in borrowed.get_maybe_shared_borrowed().iter() {
            remove_place_from_set(self.body, self.tcx, place, &mut definitely_owned);
        }
        DefinitelyAccessibleState {
            definitely_accessible,
            definitely_owned,
        }
    }
}
