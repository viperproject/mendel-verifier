// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::{definitely_initialized, DefinitelyUnreachableState},
    mir_utils::{place_ref_to_place, remove_place_from_set, Place, PlaceImpl},
    PointwiseState,
};
use definitely_initialized::DefinitelyInitializedState;
use log::trace;
use prusti_rustc_interface::{
    borrowck::consumers::{LocationTable, PoloniusInput, PoloniusOutput, RichLocation},
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty, ty::TyCtxt},
    span::def_id::DefId,
};

pub struct DefinitelyUnreachableAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
    /// Which loans (value) are live at the beginning of a given location (key)
    loans_live_at_location: FxHashMap<mir::Location, FxHashSet<mir::Location>>,
    definitely_initialized_state:
        PointwiseState<'mir, 'tcx, DefinitelyInitializedState<'mir, 'tcx>>,
}

fn compute_loans_live_at_location(
    input_facts: &PoloniusInput,
    output_facts: &PoloniusOutput,
    location_table: &LocationTable,
) -> FxHashMap<mir::Location, FxHashSet<mir::Location>> {
    let loan_issued_at = &input_facts.loan_issued_at;
    let loan_live_at = &output_facts.loan_live_at;
    let loan_issued_at_location: FxHashMap<_, mir::Location> = loan_issued_at
        .iter()
        .map(|&(_, loan, point_index)| {
            let rich_location = location_table.to_location(point_index);
            let location = match rich_location {
                RichLocation::Start(loc) | RichLocation::Mid(loc) => loc,
            };
            (loan, location)
        })
        .collect();
    let mut loans_live_at_location: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    for (&point_index, loans) in loan_live_at.iter() {
        let rich_location = location_table.to_location(point_index);
        if let RichLocation::Start(at_location) = rich_location {
            trace!("  At location {:?}:", rich_location);
            for loan in loans {
                let loan_location = loan_issued_at_location[loan];
                trace!("    Loan {:?} is live", rich_location);
                loans_live_at_location
                    .entry(at_location)
                    .or_default()
                    .insert(loan_location);
            }
        }
    }
    loans_live_at_location
}

impl<'mir, 'tcx: 'mir> DefinitelyUnreachableAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        mir: &'mir mir::Body<'tcx>,
        input_facts: &PoloniusInput,
        output_facts: &PoloniusOutput,
        location_table: &LocationTable,
        definitely_initialized_state: PointwiseState<
            'mir,
            'tcx,
            DefinitelyInitializedState<'mir, 'tcx>,
        >,
    ) -> AnalysisResult<Self> {
        let loans_live_at_location =
            compute_loans_live_at_location(input_facts, output_facts, location_table);

        Ok(DefinitelyUnreachableAnalysis {
            tcx,
            def_id,
            mir,
            loans_live_at_location,
            definitely_initialized_state,
        })
    }

    fn kill_dead_loans(
        &self,
        location: mir::Location,
        state: &mut DefinitelyUnreachableState<'mir, 'tcx>,
    ) {
        let opt_live_loans = self.loans_live_at_location.get(&location);
        if let Some(live_loans) = opt_live_loans {
            trace!("Loan live at {:?}: {:?}", location, live_loans);
            state.retain_loans(live_loans);
        } else {
            state.clear();
        }
    }

    /// Returns sets of new deeply and shallowly unreachable places.
    fn get_new_unreachable_places(
        &self,
        location: mir::Location,
    ) -> (FxHashSet<Place<'tcx>>, FxHashSet<Place<'tcx>>) {
        // Terminators do not block new places
        let statement = self.mir.stmt_at(location).left().unwrap();
        let mut new_deeply_unreachable = FxHashSet::default();
        let mut new_shallowly_unreachable = FxHashSet::default();

        // New unreachable places can only come from reborrowing assignments
        if let mir::StatementKind::Assign(box (
            _target,
            mir::Rvalue::Ref(_region, _kind, ref place),
        )) = statement.kind
        {
            let mut after_deref = false;
            let mut last_deref_place = None;

            for (base, projection) in place.iter_projections() {
                match projection {
                    mir::ProjectionElem::Deref => {
                        // Detect dereferentiations of mutable references.
                        after_deref = true;
                        let base_ty = base.ty(self.mir, self.tcx).ty;
                        if !matches!(base_ty.kind(), ty::TyKind::Ref(_, _, mir::Mutability::Mut)) {
                            break;
                        }
                        last_deref_place =
                            Some(Place::from_mir_place(place_ref_to_place(base, self.tcx)));
                    }
                    mir::ProjectionElem::Field(field, field_ty) => {
                        if after_deref {
                            // Other fields of the unique base become unreachable.
                            let base_place = place_ref_to_place(base, self.tcx);
                            let mir_field_place =
                                self.tcx.mk_place_field(base_place, field, field_ty);
                            let field_place = Place::from_mir_place(mir_field_place);
                            new_deeply_unreachable.insert(Place::from_mir_place(base_place));
                            remove_place_from_set(
                                self.mir,
                                self.tcx,
                                field_place,
                                &mut new_deeply_unreachable,
                            );

                            // The dereferenced mutable reference becomes shallowly unreachable.
                            new_shallowly_unreachable.insert(last_deref_place.unwrap());

                            // The discriminant of the unique base becomes unreachable.
                            // Equivalently, the enum becomes shallowly unreachable.
                            let base_ty = base.ty(self.mir, self.tcx).ty;
                            if base_ty.is_enum() {
                                new_shallowly_unreachable.insert(Place::from_mir_place(base_place));
                            }
                        }
                    }
                    mir::ProjectionElem::Downcast(_, _) | mir::ProjectionElem::OpaqueCast(_) => {
                        // Nothing to do.
                    }
                    mir::ProjectionElem::Index(_)
                    | mir::ProjectionElem::ConstantIndex { .. }
                    | mir::ProjectionElem::Subslice { .. } => {
                        // Some of the unique available places might become unreachable.
                        // The analysis is imprecise for these projections.
                    }
                }
            }
        }

        trace!(
            "New deeply unreachable places at {:?}: {:?}",
            location,
            new_deeply_unreachable
        );
        trace!(
            "New shallowly unreachable references at {:?}: {:?}",
            location,
            new_shallowly_unreachable
        );
        (new_deeply_unreachable, new_shallowly_unreachable)
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for DefinitelyUnreachableAnalysis<'mir, 'tcx> {
    type State = DefinitelyUnreachableState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    /// The bottom element of the lattice contains no unreachable places.
    fn new_bottom(&self) -> Self::State {
        DefinitelyUnreachableState::new_bottom(self.def_id, self.mir, self.tcx)
    }

    /// The initial element of the lattice contains no unreachable places.
    fn new_initial(&self) -> Self::State {
        self.new_bottom()
    }

    fn need_to_widen(_counter: u32) -> bool {
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        // Remove dead loans
        self.kill_dead_loans(location, state);

        // Add new unreachable places
        let (new_deeply_unreachable, new_shallowly_unreachable) =
            self.get_new_unreachable_places(location);
        state.add_deeply_unreachable_places(location, new_deeply_unreachable.iter().copied());
        state.add_shallowly_unreachable_places(location, new_shallowly_unreachable.iter().copied());

        // Set the initialized places
        state.set_def_initialized_state(
            self.definitely_initialized_state
                .lookup_after(location)
                .unwrap()
                .clone(),
        );

        Ok(())
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        let mut new_state = state.clone();

        // Remove dead loans
        self.kill_dead_loans(location, &mut new_state);

        // Terminators do not block new places

        let terminator = self.mir.stmt_at(location).right().unwrap();
        let mut res_vec = Vec::new();
        for bb in terminator.successors() {
            let mut succ_state = new_state.clone();

            // Set the initialized places
            let succ_location = mir::Location {
                block: bb,
                statement_index: 0,
            };
            succ_state.set_def_initialized_state(
                self.definitely_initialized_state
                    .lookup_before(succ_location)
                    .unwrap()
                    .clone(),
            );

            res_vec.push((bb, succ_state));
        }
        Ok(res_vec)
    }
}
