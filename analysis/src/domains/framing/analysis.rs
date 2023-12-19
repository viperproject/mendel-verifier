// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine, LocallySharedAnalysis},
    domains::{
        locally_shared, DefinitelyAccessibleAnalysis, DefinitelyAccessibleState, FramingState,
    },
    mir_utils::{get_blocked_place, remove_place_from_set},
    PointwiseState,
};
use locally_shared::LocallySharedState;
use log::trace;
use prusti_rustc_interface::{
    borrowck::consumers::{LocationTable, PoloniusInput, PoloniusOutput},
    middle::{
        mir,
        mir::visit::{NonMutatingUseContext, PlaceContext, Visitor},
        ty::TyCtxt,
    },
    span::def_id::DefId,
};

pub struct FramingAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> FramingAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, body: &'mir mir::Body<'tcx>) -> Self {
        FramingAnalysis { tcx, def_id, body }
    }

    pub fn run_analysis(
        &self,
        input_facts: &PoloniusInput,
        output_facts: &PoloniusOutput,
        location_table: &LocationTable,
    ) -> AnalysisResult<PointwiseState<'mir, 'tcx, FramingState<'tcx>>> {
        let acc_analysis = DefinitelyAccessibleAnalysis::new(self.tcx, self.def_id, self.body);
        let accessibility =
            Rc::new(acc_analysis.run_analysis(input_facts, output_facts, location_table)?);
        let loc_shared_analysis =
            LocallySharedAnalysis::new(self.tcx, self.def_id, self.body, accessibility.clone());
        let locally_shared = loc_shared_analysis.run_fwd_analysis()?;
        let mut analysis_state = PointwiseState::default(self.body);

        // Set state_after_block
        for (block, block_data) in self.body.basic_blocks.iter_enumerated() {
            // Initialize the state before each statement and terminator
            for statement_index in 0..=block_data.statements.len() {
                let location = mir::Location {
                    block,
                    statement_index,
                };
                // Obtain the locally shared state and restrict it to what is framed
                let mut loc_shared_before = locally_shared
                    .lookup_before(location)
                    .unwrap_or_else(|| {
                        panic!("No 'locally_shared' state before location {location:?}")
                    })
                    .clone();
                if self.body.stmt_at(location).is_left() {
                    loc_shared_before.apply_statement_effect(location)?;
                }
                if self.body.stmt_at(location).is_right() {
                    let mut targets = loc_shared_before.apply_terminator_effect(location)?;
                    // All the targets should have the same state
                    if let Some((_, state)) = targets.pop() {
                        loc_shared_before = state;
                    }
                }
                // Obtain the accessibility state
                let acc_before = accessibility.lookup_before(location).unwrap_or_else(|| {
                    panic!("No 'accessibility' state before location {location:?}")
                });
                let mut compute_framing = ComputeFramingState::initial(
                    self.body,
                    self.tcx,
                    acc_before,
                    &loc_shared_before,
                );
                // Restrict the accessibility state to what is framed
                if let Some(stmt) = self.body.stmt_at(location).left() {
                    compute_framing.visit_statement(stmt, location);
                }
                if let Some(term) = self.body.stmt_at(location).right() {
                    compute_framing.visit_terminator(term, location);
                }
                let state = compute_framing.state;
                state.check_invariant(acc_before, location);
                analysis_state.set_before(location, state);
            }

            // Leave empty the state after terminators
        }

        Ok(analysis_state)
    }
}

struct ComputeFramingState<'mir, 'tcx: 'mir> {
    body: &'mir mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    state: FramingState<'tcx>,
}

impl<'mir, 'tcx: 'mir> ComputeFramingState<'mir, 'tcx> {
    pub fn initial(
        body: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        acc: &DefinitelyAccessibleState<'tcx>,
        locally_shared: &LocallySharedState<'mir, 'tcx>,
    ) -> Self {
        let state = FramingState {
            framed_accessible: acc.get_definitely_accessible().clone(),
            framed_owned: acc.get_definitely_owned().clone(),
            framed_locally_shared: locally_shared.get_locally_shared(),
        };
        ComputeFramingState { body, tcx, state }
    }
}

impl<'mir, 'tcx: 'mir> Visitor<'tcx> for ComputeFramingState<'mir, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: PlaceContext,
        location: mir::Location,
    ) {
        trace!("visit_place at {:?}: {:?} {:?}", location, place, context);
        let place = (*place).into();
        match context {
            PlaceContext::NonMutatingUse(NonMutatingUseContext::UniqueBorrow) => todo!(),
            PlaceContext::MutatingUse(_)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                // No permission can be framed
                let blocked_place = get_blocked_place(self.tcx, place);
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    blocked_place,
                    &mut self.state.framed_owned,
                );
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    blocked_place,
                    &mut self.state.framed_accessible,
                );
                self.state.framed_locally_shared.remove(&place.local);
            }
            PlaceContext::NonMutatingUse(_) => {
                // Read permission can be framed
                let frozen_place = get_blocked_place(self.tcx, place);
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    frozen_place,
                    &mut self.state.framed_owned,
                );
            }
            PlaceContext::NonUse(_) => {
                // Any permission can be framed
            }
        }
    }
}
