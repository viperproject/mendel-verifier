// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use crate::{
    abstract_interpretation::{AnalysisResult, DefinitelyAccessibleState, FixpointEngine},
    domains::LocallySharedState,
    PointwiseState,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

pub struct LocallySharedAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
    definitely_accessible_state: Rc<PointwiseState<'mir, 'tcx, DefinitelyAccessibleState<'tcx>>>,
}

impl<'mir, 'tcx: 'mir> LocallySharedAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        mir: &'mir mir::Body<'tcx>,
        definitely_accessible_state: Rc<
            PointwiseState<'mir, 'tcx, DefinitelyAccessibleState<'tcx>>,
        >,
    ) -> Self {
        LocallySharedAnalysis {
            tcx,
            def_id,
            mir,
            definitely_accessible_state,
        }
    }

    fn apply_definitely_accessible_state(
        &self,
        state: &mut LocallySharedState,
        definitely_accessible_state: &DefinitelyAccessibleState,
    ) {
        let mut owned_locals = FxHashSet::default();
        let mut accessible_locals = FxHashSet::default();
        for &place in definitely_accessible_state.get_definitely_owned() {
            if place.projection.is_empty() {
                owned_locals.insert(place.local);
            }
        }
        for &place in definitely_accessible_state.get_definitely_accessible() {
            if place.projection.is_empty() {
                accessible_locals.insert(place.local);
            }
        }
        state.set_accessible(&accessible_locals);
        state.set_owned(&owned_locals);
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for LocallySharedAnalysis<'mir, 'tcx> {
    type State = LocallySharedState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    fn new_bottom(&self) -> Self::State {
        LocallySharedState::new_bottom(self.def_id, self.mir, self.tcx)
    }

    fn new_initial(&self) -> Self::State {
        let mut locally_shared = FxHashMap::default();
        for local in self.mir.args_iter() {
            locally_shared.insert(local, FxHashSet::default());
        }
        LocallySharedState {
            locally_shared,
            def_id: self.def_id,
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn need_to_widen(_counter: u32) -> bool {
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        log::debug!("Statement {location:?}");

        // Update locally shared locals
        state.apply_statement_effect(location)?;

        // Add owed locals and remove non-accessible locals
        let definitely_accessible_state = self
            .definitely_accessible_state
            .lookup_after(location)
            .unwrap();
        self.apply_definitely_accessible_state(state, definitely_accessible_state);

        Ok(())
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        log::debug!("Terminator {location:?}");

        // Update locally shared locals
        let mut targets = state.apply_terminator_effect(location)?;

        // Add owed locals and remove non-accessible locals
        let definitely_accessible_state = self
            .definitely_accessible_state
            .lookup_after_block(location.block)
            .unwrap();
        for (target, state) in &mut targets {
            self.apply_definitely_accessible_state(state, &definitely_accessible_state[target]);
        }

        Ok(targets)
    }
}
