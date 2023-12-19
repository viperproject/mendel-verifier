// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    domains::DefinitelyAccessibleState,
    mir_utils::{is_prefix, remove_place_from_set, Place},
};
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty::TyCtxt},
};
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::fmt;

#[derive(Clone, Default, Eq, PartialEq)]
pub struct FramingState<'tcx> {
    /// Places of `definitely_accessible` that can be framed across the *next* statement.
    pub(super) framed_accessible: FxHashSet<Place<'tcx>>,
    /// Locals that are locally shared and can be framed across the *next* statement.
    /// Note: This represents a subset of `framed_accessible`.
    pub(super) framed_locally_shared: FxHashSet<mir::Local>,
    /// Places of `definitely_owned` that can be framed across the *next* statement.
    /// Note: This is a subset of `framed_accessible` and might have elements in common with
    /// `framed_locally_shared`.
    pub(super) framed_owned: FxHashSet<Place<'tcx>>,
}

impl<'tcx> FramingState<'tcx> {
    pub fn get_framed_accessible(&self) -> &FxHashSet<Place<'tcx>> {
        &self.framed_accessible
    }

    pub fn get_framed_locally_shared(&self) -> &FxHashSet<mir::Local> {
        &self.framed_locally_shared
    }

    pub fn get_framed_owned(&self) -> &FxHashSet<Place<'tcx>> {
        &self.framed_owned
    }

    /// Get the elements of `framed_locally_shared` that are not owned.
    pub fn get_framed_locally_shared_only(&self) -> FxHashSet<mir::Local> {
        // TODO: This can be cached
        let mut result = self.framed_locally_shared.clone();
        for &place in &self.framed_owned {
            result.remove(&place.local);
        }
        result
    }

    /// Get the elements of `framed_accessible` that are not owned nor locally shared.
    pub fn get_framed_accessible_only(
        &self,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<Place<'tcx>> {
        // TODO: This can be cached
        let mut result = self.framed_accessible.clone();
        for &place in &self.framed_owned {
            remove_place_from_set(body, tcx, place, &mut result);
        }
        for &local in &self.framed_locally_shared {
            remove_place_from_set(body, tcx, local.into(), &mut result);
        }
        result
    }

    pub fn check_invariant(
        &self,
        accessibility: &DefinitelyAccessibleState<'tcx>,
        location: impl fmt::Debug,
    ) {
        for &owned_place in self.framed_owned.iter() {
            debug_assert!(
                self.framed_accessible
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {location:?} the framed place {owned_place:?} is owned but not accessible"
            );
        }
        for &local in self.framed_locally_shared.iter() {
            debug_assert!(
                self.framed_accessible
                    .iter()
                    .any(|&place| place == local.into()),
                "In the state before {location:?} the framed local {local:?} is locally shared but not accessible"
            );
        }
        for &owned_place in self.framed_accessible.iter() {
            debug_assert!(
                accessibility.get_definitely_accessible()
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {location:?} the place {owned_place:?} is not accessible, but it is framed as accessible"
            );
        }
        for &owned_place in self.framed_owned.iter() {
            debug_assert!(
                accessibility
                    .get_definitely_owned()
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {location:?} the place {owned_place:?} is not owned, but it is framed as owned"
            );
        }
    }
}

impl<'tcx> Serialize for FramingState<'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(3))?;
        let mut definitely_accessible_set: Vec<_> = self.framed_accessible.iter().collect();
        definitely_accessible_set.sort();
        let mut definitely_accessible_strings = vec![];
        for &place in definitely_accessible_set {
            definitely_accessible_strings.push(format!("{place:?}"));
        }
        seq.serialize_entry("frame_accessible", &definitely_accessible_strings)?;
        let mut locally_shared_set: Vec<_> = self.framed_locally_shared.iter().collect();
        locally_shared_set.sort();
        let mut locally_shared_strings = vec![];
        for &local in locally_shared_set {
            locally_shared_strings.push(format!("{local:?}"));
        }
        seq.serialize_entry("frame_locally_shared", &locally_shared_strings)?;
        let mut definitely_owned_set: Vec<_> = self.framed_owned.iter().collect();
        definitely_owned_set.sort();
        let mut definitely_owned_strings = vec![];
        for &place in definitely_owned_set {
            definitely_owned_strings.push(format!("{place:?}"));
        }
        seq.serialize_entry("frame_owned", &definitely_owned_strings)?;
        seq.end()
    }
}

impl fmt::Debug for FramingState<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}
