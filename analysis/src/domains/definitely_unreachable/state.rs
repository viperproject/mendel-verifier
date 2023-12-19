// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AbstractState, DefinitelyInitializedState},
    mir_utils::*,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::fmt;

/// A set of MIR places that are definitely unreachable.
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone)]
pub struct DefinitelyUnreachableState<'mir, 'tcx: 'mir> {
    /// Stores for each live loan (keys) which places are definitely deeply unreachable (values).
    /// Loans are identified by the location of their creation.
    pub(super) deeply_unreachable_places: FxHashMap<mir::Location, FxHashSet<Place<'tcx>>>,
    /// Stores for each live loan (keys) which places are definitely shallowly unreachable
    /// (values). Loans are identified by the location of their creation.
    /// A shallowly unreachable reference is a reference whose target address cannot be changed.
    /// A shallowly unreachable enumeration is an enumeration whose discrimiant cannot be changed.
    pub(super) shallowly_unreachable_places: FxHashMap<mir::Location, FxHashSet<Place<'tcx>>>,
    pub(super) def_initialized_state: DefinitelyInitializedState<'mir, 'tcx>,
}

impl<'mir, 'tcx: 'mir> fmt::Debug for DefinitelyUnreachableState<'mir, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore tcx & mir
        f.debug_struct("DefinitelyUnreachableState")
            .field("deeply_unreachable_places", &self.deeply_unreachable_places)
            .field(
                "deeply_unreachable_places",
                &self.shallowly_unreachable_places,
            )
            .field("def_initialized_state", &self.def_initialized_state)
            .finish()
    }
}

impl<'mir, 'tcx: 'mir> PartialEq for DefinitelyUnreachableState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.deeply_unreachable_places == other.deeply_unreachable_places
            && self.shallowly_unreachable_places == other.shallowly_unreachable_places
            && self.def_initialized_state == other.def_initialized_state
    }
}

impl<'mir, 'tcx: 'mir> Eq for DefinitelyUnreachableState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> Serialize for DefinitelyUnreachableState<'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(2))?;
        let mut deeply_unreachable_set: Vec<_> =
            self.get_deeply_unreachable_places().into_iter().collect();
        deeply_unreachable_set.sort();
        let mut deeply_unreachable_strings = vec![];
        for &place in &deeply_unreachable_set {
            deeply_unreachable_strings.push(format!("{place:?}"));
        }
        seq.serialize_entry("deeply_unreachable", &deeply_unreachable_strings)?;
        let mut shallowly_unreachable_set: Vec<_> = self
            .get_shallowly_unreachable_places()
            .into_iter()
            .collect();
        shallowly_unreachable_set.sort();
        let mut shallowly_unreachable_strings = vec![];
        for &place in &shallowly_unreachable_set {
            shallowly_unreachable_strings.push(format!("{place:?}"));
        }
        seq.serialize_entry("shallowly_unreachable", &shallowly_unreachable_strings)?;
        seq.end()
    }
}

impl<'mir, 'tcx: 'mir> DefinitelyUnreachableState<'mir, 'tcx> {
    /// Creates a new state with no unreachable or borrowed places and all places initialized.
    /// This corresponds to the bottom of the lattice.
    pub fn new_bottom(def_id: DefId, mir: &'mir mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            deeply_unreachable_places: FxHashMap::default(),
            shallowly_unreachable_places: FxHashMap::default(),
            def_initialized_state: DefinitelyInitializedState::new_bottom(def_id, mir, tcx),
        }
    }

    pub fn get_deeply_unreachable_places(&self) -> FxHashSet<Place<'tcx>> {
        // TODO: This can be cached
        let mut result = FxHashSet::default();
        for unreachable in self.deeply_unreachable_places.values() {
            result.extend(unreachable.iter().copied());
        }
        result
    }

    pub fn get_shallowly_unreachable_places(&self) -> FxHashSet<Place<'tcx>> {
        // TODO: This can be cached
        let mut result = FxHashSet::default();
        for unreachable in self.shallowly_unreachable_places.values() {
            result.extend(unreachable.iter().copied());
        }
        result
    }

    pub fn set_def_initialized_state(
        &mut self,
        def_initialized_state: DefinitelyInitializedState<'mir, 'tcx>,
    ) {
        self.def_initialized_state = def_initialized_state;
    }

    /// Adds to the state several `places` that are deeply unreachable due to `loan`.
    pub fn add_deeply_unreachable_places(
        &mut self,
        loan: mir::Location,
        places: impl Iterator<Item = Place<'tcx>>,
    ) {
        self.deeply_unreachable_places
            .entry(loan)
            .or_default()
            .extend(places);
    }

    /// Adds to the state several `places` that are shallowly unreachable due to `loan`.
    pub fn add_shallowly_unreachable_places(
        &mut self,
        loan: mir::Location,
        places: impl Iterator<Item = Place<'tcx>>,
    ) {
        self.shallowly_unreachable_places
            .entry(loan)
            .or_default()
            .extend(places);
    }

    /// Removes all unreachable places from the state.
    pub fn clear(&mut self) {
        self.deeply_unreachable_places.clear();
        self.shallowly_unreachable_places.clear();
    }

    /// Removes from the state all places that are not unreachable due to a loan in `loans_to_keep`.
    pub fn retain_loans(&mut self, loans_to_keep: &FxHashSet<mir::Location>) {
        self.deeply_unreachable_places
            .retain(|loan, _unreachable| loans_to_keep.contains(loan));
        self.shallowly_unreachable_places
            .retain(|loan, _unreachable| loans_to_keep.contains(loan));
    }

    pub fn check_invariant(&self) {
        // Nothing
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for DefinitelyUnreachableState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        self.deeply_unreachable_places.is_empty() && self.shallowly_unreachable_places.is_empty()
    }

    fn join(&mut self, other: &Self) {
        if cfg!(debug_assertions) {
            self.check_invariant();
            other.check_invariant();
        }

        // Intersect the unreachable places.
        // This is a very quick and imprecise approximation, which can be greatly improved:
        // 1. For deeply unreachable places { x.f, y } and { x.f.g, z } the result of the
        //    intersection can be { x.f.g } instead of the empty set.
        // 2. If the other branch doesn't borrow a place `x.f`, then if `x.f` is unreachable in a
        //    branch it can survive the join.
        for (loan, unreachable_places) in &other.deeply_unreachable_places {
            self.deeply_unreachable_places
                .entry(*loan)
                .or_default()
                .retain(|place| unreachable_places.contains(place));
        }
        for (loan, unreachable_places) in &other.shallowly_unreachable_places {
            self.shallowly_unreachable_places
                .entry(*loan)
                .or_default()
                .retain(|place| unreachable_places.contains(place));
        }

        // Join other domains in the state
        self.def_initialized_state
            .join(&other.def_initialized_state);

        // Remove all unreachable places that might be uninitialized
        for (_loan, unreachable_places) in self.deeply_unreachable_places.iter_mut() {
            unreachable_places.retain(|&unreachable_place| {
                self.def_initialized_state
                    .get_def_init_places()
                    .iter()
                    .any(|&init_place| is_prefix(init_place, unreachable_place))
            });
        }
        for (_loan, unreachable_places) in self.shallowly_unreachable_places.iter_mut() {
            unreachable_places.retain(|&unreachable_place| {
                self.def_initialized_state
                    .get_def_init_places()
                    .iter()
                    .any(|&init_place| is_prefix(init_place, unreachable_place))
            });
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    fn widen(&mut self, _previous: &Self) {
        unimplemented!()
    }
}
