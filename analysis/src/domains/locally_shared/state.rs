// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AbstractState, DefinitelyAccessibleState},
    mir_utils::{remove_place_from_set, Place},
    AnalysisError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, mir::visit::Visitor, ty::TyCtxt},
    span::def_id::DefId,
};
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::{collections::BTreeSet, fmt};

/// An (under-approximated) set of owned local variables that have been locally shared by a
/// (precise) set of local variables.
#[derive(Clone)]
#[allow(dead_code)]
pub struct LocallySharedState<'mir, 'tcx: 'mir> {
    /// A map from locally shared local variables to the set of locally shared borrows.
    /// If the set of shared borrows is empty then the local variable is owned, which corresponds
    /// to the bottom element of its lattice.
    pub(super) locally_shared: FxHashMap<mir::Local, FxHashSet<mir::Local>>,
    pub(super) def_id: DefId,
    pub(super) mir: &'mir mir::Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
}

impl<'mir, 'tcx: 'mir> fmt::Debug for LocallySharedState<'mir, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore tcx & mir
        f.debug_struct("LocallySharedState")
            .field("locally_shared", &self.locally_shared)
            .finish()
    }
}

impl<'mir, 'tcx: 'mir> PartialEq for LocallySharedState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.locally_shared == other.locally_shared
    }
}

impl<'mir, 'tcx: 'mir> Eq for LocallySharedState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> Serialize for LocallySharedState<'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(self.locally_shared.len()))?;
        let locally_shared_locals_set: BTreeSet<_> = self.locally_shared.keys().collect();
        for &local in locally_shared_locals_set {
            let mut loans_strings = vec![];
            let loans_set: BTreeSet<_> = self.locally_shared[&local].iter().copied().collect();
            for loan in loans_set {
                loans_strings.push(format!("{loan:?}"));
            }
            seq.serialize_entry(&format!("{local:?}"), &loans_strings)?;
        }
        seq.end()
    }
}

impl<'mir, 'tcx: 'mir> LocallySharedState<'mir, 'tcx> {
    pub fn get_locally_shared(&self) -> FxHashSet<mir::Local> {
        // TODO: Can be cached
        let locally_shared: FxHashSet<_> = self.locally_shared.keys().copied().collect();
        // TODO(fpoli): Add the loans, because they are local too
        // for loans in self.locally_shared.values() {
        //     locally_shared.extend(loans);
        // }
        locally_shared
    }

    pub fn get_locally_shared_only(
        &self,
        accessible: &DefinitelyAccessibleState<'tcx>,
    ) -> FxHashSet<mir::Local> {
        let mut locals: FxHashSet<_> = self.get_locally_shared();
        for &place in accessible.get_definitely_owned().iter() {
            locals.remove(&place.local);
        }
        locals
    }

    pub fn get_definitely_accessible_only(
        &self,
        accessible: &DefinitelyAccessibleState<'tcx>,
    ) -> FxHashSet<Place<'tcx>> {
        let mut places = accessible.get_definitely_accessible_only(self.mir, self.tcx);
        for &local in &self.get_locally_shared() {
            remove_place_from_set(self.mir, self.tcx, local.into(), &mut places);
        }
        places
    }

    pub fn set_accessible(&mut self, locals: &FxHashSet<mir::Local>) {
        log::debug!("Set accessible locals {locals:?}");
        self.locally_shared.retain(|k, _| locals.contains(k));
    }

    pub fn set_owned(&mut self, locals: &FxHashSet<mir::Local>) {
        log::debug!("Set owned locals {locals:?}");
        for &local in locals {
            self.locally_shared.entry(local).or_default().clear();
        }
    }

    /// The top element of the lattice represents the "known nothing" state
    pub fn new_top(def_id: DefId, mir: &'mir mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            locally_shared: FxHashMap::default(),
            def_id,
            mir,
            tcx,
        }
    }

    /// The bottom element of the lattice represents the "everything is possible" state
    pub fn new_bottom(def_id: DefId, mir: &'mir mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut locally_shared = FxHashMap::default();
        for local in mir.local_decls.indices() {
            locally_shared.insert(local, FxHashSet::default());
        }
        LocallySharedState {
            locally_shared,
            def_id,
            mir,
            tcx,
        }
    }

    pub(crate) fn apply_statement_effect(
        &mut self,
        location: mir::Location,
    ) -> Result<(), AnalysisError> {
        let statement = &self.mir[location.block].statements[location.statement_index];

        // Collect the used locals that might invalidate a locally_shared local
        let mut used_locals_collector = UsedLocalsCollector::default();

        match statement.kind {
            mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_)
            | mir::StatementKind::FakeRead(_) => {
                // Nothing
            }

            // Assignment `x = ..`
            mir::StatementKind::Assign(box (lhs, ref rhs)) if lhs.projection.is_empty() => {
                let lhs_local = lhs.local;
                match rhs {
                    // Assignment `x = &y`
                    mir::Rvalue::Ref(_, mir::BorrowKind::Shared, ref rhs_place)
                        if rhs_place.projection.is_empty() =>
                    {
                        // If `y` was owned, make it locally shared
                        if let Some(loans) = self.locally_shared.get_mut(&rhs_place.local) {
                            loans.insert(lhs_local);
                        }
                    }
                    // Assignment `x = &(*y)`
                    mir::Rvalue::Ref(_, mir::BorrowKind::Shared, ref rhs_place)
                        if rhs_place.projection.len() == 1
                            && rhs_place.projection.last() == Some(&mir::ProjectionElem::Deref) =>
                    {
                        let rhs_local = rhs_place.local;
                        debug_assert!(self
                            .locally_shared
                            .get(&rhs_local)
                            .iter()
                            .all(|l| l.is_empty()));
                        for loans in self.locally_shared.values_mut() {
                            if loans.contains(&rhs_local) {
                                loans.insert(lhs_local);
                            }
                        }
                        // The local is no longer owned
                        self.locally_shared.remove(&rhs_local);
                    }
                    // Assignment `x = copy/move y`
                    mir::Rvalue::Use(
                        mir::Operand::Copy(rhs_place) | mir::Operand::Move(rhs_place),
                    ) if rhs_place.projection.is_empty() => {
                        let rhs_local = rhs_place.local;
                        debug_assert!(self
                            .locally_shared
                            .get(&rhs_local)
                            .iter()
                            .all(|l| l.is_empty()));
                        for loans in self.locally_shared.values_mut() {
                            if loans.contains(&rhs_local) {
                                loans.insert(lhs_local);
                                if let mir::Rvalue::Use(mir::Operand::Move(_)) = rhs {
                                    // The loan is no longer used
                                    loans.remove(&rhs_local);
                                }
                            }
                        }
                        if let mir::Rvalue::Use(mir::Operand::Move(_)) = rhs {
                            // The local is no longer owned
                            self.locally_shared.remove(&rhs_local);
                        }
                    }
                    _ => {
                        used_locals_collector.visit_rvalue(rhs, location);
                    }
                }
            }

            _ => {
                used_locals_collector.visit_statement(statement, location);
            }
        }

        // Remove the locally_shared locals that are invalidated by the statement
        for used_local in used_locals_collector.used_locals.iter() {
            log::debug!("Remove used local {used_local:?}");
            // The local might be used to create references that are leaked to other threads
            self.locally_shared.remove(used_local);
            // The loan might be leaked to other threads
            self.locally_shared
                .retain(|_, loans| !loans.contains(used_local));
        }

        Ok(())
    }

    pub(crate) fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut new_state = self.clone();
        let terminator = self.mir[location.block].terminator();

        // Collect the used locals that might invalidate a locally_shared local
        let mut used_locals_collector = UsedLocalsCollector::default();

        match &terminator.kind {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } if destination.projection.is_empty() => {
                used_locals_collector.visit_operand(func, location);
                for arg in args {
                    used_locals_collector.visit_operand(arg, location);
                }
            }

            _ => {
                used_locals_collector.visit_terminator(terminator, location);
            }
        }

        // Remove the locally_shared locals that are invalidated by the terminator
        for used_local in used_locals_collector.used_locals.iter() {
            log::debug!("Remove used local {used_local:?}");
            // The local might be used to create references that are leaked to other threads
            new_state.locally_shared.remove(used_local);
            // The loan might be leaked to other threads
            new_state
                .locally_shared
                .retain(|_, loans| !loans.contains(used_local));
        }

        let res_vec = terminator
            .successors()
            .map(|bb| (bb, new_state.clone()))
            .collect();
        Ok(res_vec)
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for LocallySharedState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        if self.locally_shared.len() == self.mir.local_decls.len() {
            self.locally_shared.values().all(|loans| loans.is_empty())
        } else {
            false
        }
    }

    fn join(&mut self, other: &Self) {
        // Intersect the locals
        for local in &self.locally_shared.keys().cloned().collect::<Vec<_>>() {
            if !other.locally_shared.contains_key(local) {
                self.locally_shared.remove(local);
            }
        }
        // Merge the loans
        for (other_local, other_loans) in other.locally_shared.iter() {
            if let Some(loans) = self.locally_shared.get_mut(other_local) {
                loans.extend(other_loans.iter().copied());
            }
        }
    }

    fn widen(&mut self, _previous: &Self) {
        unimplemented!()
    }
}

#[derive(Debug, Clone, Default)]
struct UsedLocalsCollector {
    used_locals: FxHashSet<mir::Local>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for UsedLocalsCollector {
    fn visit_local(
        &mut self,
        local: mir::Local,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.used_locals.insert(local);
    }
}
