// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::safe_clients::procedure_encoder::*;
use analysis::domains::DefinitelyAllocatedAnalysis;
use analysis::domains::DefinitelyAllocatedState;
use analysis::domains::DefinitelyUnreachableAnalysis;
use analysis::domains::DefinitelyUnreachableState;
use analysis::domains::DefinitelyInitializedAnalysis;
use analysis::domains::LocallySharedAnalysis;
use analysis::domains::LocallySharedState;
use analysis::mir_utils::Place;
use prelude::ownership_domain::{OwnershipDomain, OwnershipKind};
use prusti_rustc_interface::{
    polonius_engine::{Algorithm, Output},
    data_structures::fx::FxHashSet,
};
use analysis::{
    abstract_interpretation::FixpointEngine,
    domains::{DefinitelyAccessibleAnalysis, FramingAnalysis, DefinitelyAccessibleState, FramingState}, PointwiseState,
};

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    /// Initialize ownership, framing and unreachable facts.
    #[allow(clippy::type_complexity)]
    pub(super) fn compute_facts(&self) -> SpannedEncodingResult<(
        Rc<PointwiseState<'p, 'tcx, DefinitelyAccessibleState<'tcx>>>,
        PointwiseState<'p, 'tcx, LocallySharedState<'p, 'tcx>>,
        PointwiseState<'p, 'tcx, FramingState<'tcx>>,
        PointwiseState<'p, 'tcx, DefinitelyUnreachableState<'p, 'tcx>>,
        PointwiseState<'p, 'tcx, DefinitelyAllocatedState<'p, 'tcx>>,
    )> {
        let tcx = self.tcx();
        let local_def_id = self.def_id.expect_local();

        // Load facts
        let borrowck_facts = self.encoder.env().body.local_mir_borrowck_facts(local_def_id);
        let location_table_borrow = borrowck_facts.location_table.borrow();
        let location_table = location_table_borrow.as_ref().unwrap();
        let input_facts_borrow = borrowck_facts.input_facts.borrow();
        let input_facts = input_facts_borrow.as_ref().unwrap();

        // Run Polonius
        let output_facts = Output::compute(input_facts, Algorithm::Naive, true);

        // Run analysis
        let ownership_analysis = DefinitelyAccessibleAnalysis::new(tcx, self.def_id, self.mir);
        let ownership_facts = match ownership_analysis.run_analysis(input_facts, &output_facts, location_table) {
            Ok(state) => Rc::new(state),
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while running the ownership analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };

        let locally_shared_analysis = LocallySharedAnalysis::new(tcx, self.def_id, self.mir, ownership_facts.clone());
        let locally_shared_facts = match locally_shared_analysis.run_fwd_analysis() {
            Ok(state) => state,
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while running the locally-shared analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };

        let framing_analysis = FramingAnalysis::new(tcx, self.def_id, self.mir);
        let framing_facts = match framing_analysis.run_analysis(input_facts, &output_facts, location_table) {
            Ok(state) => state,
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while running the framing analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };

        let def_initialized_analysis = DefinitelyInitializedAnalysis::new(tcx, self.def_id, self.mir);
        let def_initialized_state = match def_initialized_analysis.run_fwd_analysis() {
            Ok(state) => state,
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while running the initialization analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };

        let def_unreachable_analysis = match DefinitelyUnreachableAnalysis::new(
            tcx, self.def_id, self.mir,
            input_facts, &output_facts, location_table,
            def_initialized_state,
        ) {
            Ok(analysis) => analysis,
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while constructing the definitely-unreachable analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };
        let unreachable_facts = match def_unreachable_analysis.run_fwd_analysis() {
            Ok(state) => state,
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while running the definitely-unreachable analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };

        let def_allocated_analysis = DefinitelyAllocatedAnalysis::new(self.def_id, self.mir);
        let def_allocated_state = match def_allocated_analysis.run_fwd_analysis() {
            Ok(state) => state,
            Err(err) => {
                return Err(SpannedEncodingError::internal(
                    format!("error while running the allocation analysis: {err:?}"),
                    self.mir.span,
                ));
            }
        };

        Ok((ownership_facts, locally_shared_facts, framing_facts, unreachable_facts, def_allocated_state))
    }

    /// Encode framing across a ghost bump just after the precondition.
    /// The framing is between the old and the current memory version.
    pub(super) fn encode_framing_at_precondition(&self) -> EncodingResult<Vec<vir::Stmt>> {
        trace!("Encode framing at precondition");
        let location = mir::START_BLOCK.start_location();
        let Some(facts) = self.ownership_facts().lookup_before(location) else {
            error_internal!("Ownership facts not available at precondition");
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!("Locally shared facts not available at precondition");
        };
        let deeply_unreachable = self.get_deeply_unreachable_places_at(location)?;
        debug_assert!(deeply_unreachable.is_empty());
        let shallowly_unreachable = self.get_shallowly_unreachable_places_at(location)?;
        debug_assert!(shallowly_unreachable.is_empty());

        let mut stmts = vec![vir::Stmt::comment("Framing facts")];
        let mut fact_idx = 0;
        for &place in facts.get_definitely_owned() {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::WriteRef,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of WriteRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_locally_shared_only(facts) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::LocalRef,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_definitely_accessible_only(facts) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::ReadRef,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        Ok(stmts)
    }

    /// Encode framing across a ghost bump just before the postcondition.
    /// The framing is between the old and the current memory version.
    pub(super) fn encode_framing_at_postcondition(&self) -> EncodingResult<Vec<vir::Stmt>> {
        trace!("Encode framing at postcondition");
        let Some(location) = self.get_single_return_location()? else {
            return Ok(vec![]);
        };
        let Some(facts) = self.ownership_facts().lookup_before(location) else {
            error_internal!("Ownership facts not available at postcondition");
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!("Locally shared facts not available at postcondition");
        };
        let deeply_unreachable = self.get_deeply_unreachable_places_at(location)?;
        let shallowly_unreachable = self.get_shallowly_unreachable_places_at(location)?;

        let mut stmts = vec![vir::Stmt::comment("Framing facts")];
        let mut fact_idx = 0;
        for &place in facts.get_definitely_owned() {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::WriteRef,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of WriteRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_locally_shared_only(facts) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::LocalRef,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_definitely_accessible_only(facts) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::ReadRef,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }

        // Use THE SAME ROOT for ALL unreachable facts, because we don't have non-aliasing guarantees.
        fact_idx += 1;
        for &place in &deeply_unreachable {
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::DeeplyUnreachable,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of DeeplyUnreachable({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &shallowly_unreachable {
            let fact = self.encode_framed_ownership_fact(
                CallOrStmt::Stmt, fact_idx, place.into(), OwnershipKind::ShallowlyOwned,
            )?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ShallowlyUnreachable({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }

        Ok(stmts)
    }

    /// Encode framing across a location.
    /// The framing is between the old and the current memory version.
    pub(super) fn encode_framing_across_location(&self, location: mir::Location) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!("Encode framing across {:?}", location);
        let span = self.get_span_of_location(location);
        let pos = self.encoder.error_manager().register_span(self.def_id, span);
        let call_or_stmt = self.call_or_stmt(location);

        let Some(facts) = self.framing_facts().lookup_before(location) else {
            error_internal!(span => "Framing facts not available before location {:?}", location);
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!(span =>"Locally shared facts not available before location {:?}", location);
        };
        let deeply_unreachable = self.get_deeply_unreachable_places_at(location)?;
        let shallowly_unreachable = self.get_shallowly_unreachable_places_at(location)?;

        let mut stmts = vec![vir::Stmt::comment("Framing facts")];
        let mut fact_idx = 0;
        for &place in facts.get_framed_owned() {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::WriteRef,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of WriteRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &facts.get_framed_locally_shared_only() {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::LocalRef,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &facts.get_framed_accessible_only(self.mir, self.tcx()) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::ReadRef,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }

        // Use THE SAME ROOT for ALL unreachable facts, because we don't have non-aliasing guarantees.
        fact_idx += 1;
        for &place in &deeply_unreachable {
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::DeeplyUnreachable,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of DeeplyUnreachable({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &shallowly_unreachable {
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::ShallowlyOwned,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ShallowlyUnreachable({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }

        Ok(stmts)
    }

    /// Encode framing of before a location, e.g. to stabilize before a call.
    /// The framing is between the old and the current memory version.
    pub(super) fn encode_framing_before_location(&self, location: mir::Location) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!("Encode framing before {:?}", location);
        let span = self.get_span_of_location(location);
        let pos = self.encoder.error_manager().register_span(self.def_id, span);
        // We are encoding the framing of an interference. So, this doesn't need to be Call.
        let call_or_stmt = CallOrStmt::Stmt;

        let Some(facts) = self.ownership_facts().lookup_before(location) else {
            error_internal!(span => "Ownership facts not available before {:?}", location);
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!(span =>"Locally shared facts not available before {:?}", location);
        };
        let deeply_unreachable = self.get_deeply_unreachable_places_at(location)?;
        let shallowly_unreachable = self.get_shallowly_unreachable_places_at(location)?;

        let mut stmts = vec![vir::Stmt::comment("Framing facts")];
        let mut fact_idx = 0;
        for &place in facts.get_definitely_owned() {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::WriteRef,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of WriteRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_locally_shared_only(facts) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::LocalRef,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_definitely_accessible_only(facts) {
            fact_idx += 1;
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::ReadRef,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }

        // Use THE SAME ROOT for ALL unreachable facts, because we don't have non-aliasing guarantees.
        fact_idx += 1;
        for &place in &deeply_unreachable {
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::DeeplyUnreachable,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of DeeplyUnreachable({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &shallowly_unreachable {
            let fact = self.encode_framed_ownership_fact(
                call_or_stmt, fact_idx, place.into(), OwnershipKind::ShallowlyOwned,
            ).with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume framing of ShallowlyUnreachable({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }

        Ok(stmts)
    }

    /// Encode ownership at the beginning of the method, when the precondition holds.
    /// All derefs will use the current memory version.
    pub(super) fn encode_ownership_at_precondition(&self) -> EncodingResult<Vec<vir::Stmt>> {
        trace!("Encode ownership at the precondition");
        let location = mir::START_BLOCK.start_location();
        let Some(facts) = self.ownership_facts().lookup_before(location) else {
            error_internal!("Ownership facts not available at precondition");
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!("Locally shared facts not available at precondition");
        };
        let Some(allocation_facts) = self.allocation_facts().lookup_before(location) else {
            error_internal!("Allocation facts not available at precondition");
        };

        let mut stmts = vec![vir::Stmt::comment("Ownership facts")];
        let mut fact_idx = 0;
        for &place in facts.get_definitely_owned() {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::WriteRef)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume WriteRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_locally_shared_only(facts) {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::LocalRef)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_definitely_accessible_only(facts) {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::ReadRef)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in allocation_facts.get_def_allocated_locals() {
            fact_idx += 1; // Dummy
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::Allocated)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume Allocated({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        Ok(stmts)
    }

    /// Encode ownership at the beginning of the method, when the precondition holds.
    /// All derefs will use the current memory version.
    pub(super) fn encode_ownership_at_postcondition(&self) -> EncodingResult<Vec<vir::Stmt>> {
        trace!("Encode ownership at the postcondition");
        let Some(location) = self.get_single_return_location()? else {
            return Ok(vec![]);
        };
        let Some(facts) = self.ownership_facts().lookup_before(location) else {
            error_internal!("Ownership facts not available at postcondition");
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!("Locally shared facts not available at postcondition");
        };
        let Some(allocation_facts) = self.allocation_facts().lookup_before(location) else {
            error_internal!("Allocation facts not available at postcondition");
        };

        let mut stmts = vec![vir::Stmt::comment("Ownership facts")];
        let mut fact_idx = 0;
        for &place in facts.get_definitely_owned() {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::WriteRef)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume WriteRed({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_locally_shared_only(facts) {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::LocalRef)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_definitely_accessible_only(facts) {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::ReadRef)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in allocation_facts.get_def_allocated_locals() {
            fact_idx += 1; // Dummy
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::Allocated)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume Allocated({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        Ok(stmts)
    }

    /// Encode ownership before a location.
    /// All derefs will use the current memory version.
    pub(super) fn encode_ownership_before_location(&self, location: mir::Location) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!("Encode ownership before {:?}", location);
        let span = self.get_span_of_location(location);
        let pos = self.encoder.error_manager().register_span(self.def_id, span);

        let mut stmts = vec![vir::Stmt::comment("Ownership facts")];
        let Some(facts) = self.ownership_facts().lookup_before(location) else {
            error_internal!(span => "Ownership facts not available before {:?}", location);
        };
        let Some(locally_shared_facts) = self.locally_shared_facts().lookup_before(location) else {
            error_internal!(span => "Locally shared facts not available before {:?}", location);
        };
        let Some(allocation_facts) = self.allocation_facts().lookup_before(location) else {
            error_internal!(span => "Allocation facts not available before {:?}", location);
        };

        let mut stmts = vec![vir::Stmt::comment("Ownership facts")];
        let mut fact_idx = 0;
        for &place in facts.get_definitely_owned() {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::WriteRef)
                .with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume WriteRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_locally_shared_only(facts) {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::LocalRef)
                .with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume LocalRef({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in &locally_shared_facts.get_definitely_accessible_only(facts) {
            fact_idx += 1;
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::ReadRef)
                .with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume ReadRef({place:?}: {:?})", place.ty(self.mir, self.tcx()).ty)),
                vir::Stmt::inhale(fact),
            ]);
        }
        for &place in allocation_facts.get_def_allocated_locals() {
            fact_idx += 1; // Dummy
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::Allocated)
                .with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume Allocated({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        Ok(stmts)
    }

    /// Encode ownership before a location.
    /// All derefs will use the current memory version.
    pub(super) fn encode_allocation_at_location(&self, location: mir::Location) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!("Encode ownership before {:?}", location);
        let span = self.get_span_of_location(location);
        let pos = self.encoder.error_manager().register_span(self.def_id, span);

        let mut stmts = vec![vir::Stmt::comment("Allocation facts")];
        let Some(allocation_facts) = self.allocation_facts().lookup_before(location) else {
            error_internal!(span => "Allocation facts not available before {:?}", location);
        };

        let mut stmts = vec![vir::Stmt::comment("Allocation facts")];
        let mut fact_idx = 0;
        for &place in allocation_facts.get_def_allocated_locals() {
            fact_idx += 1; // Dummy
            let fact = self.encode_ownership_fact(fact_idx, place.into(), OwnershipKind::Allocated)
                .with_span(span)?;
            stmts.extend(vec![
                vir::Stmt::comment(format!("assume Allocated({place:?}: {:?})", self.get_local_ty(place))),
                vir::Stmt::inhale(fact),
            ]);
        }
        Ok(stmts)
    }

    /// Encode the ownership fact of a place.
    /// All derefs will use the current memory version.
    pub fn encode_ownership_fact(
        &self, root: usize, place: mir::Place<'tcx>, ownership_kind: OwnershipKind,
    ) -> EncodingResult<vir::Expr> {
        let place_ty = self.get_place_ty(place).ty;
        let ownership_domain = OwnershipDomain::encode(self.encoder, place_ty)?;
        let attr_function = ownership_domain.ownership_fact_function(ownership_kind)?;
        let place_addr = self.encode_place_address(place, Version::CurrPre)?; // Old should work too
        let curr_version = self.encode_version(Version::CurrPre);
        Ok(attr_function.apply3(root, place_addr, curr_version))
    }

    /// Encode the framing fact of a place.
    /// The framing is between the old and the current memory version.
    fn encode_framed_ownership_fact(
        &self, call_or_stmt: CallOrStmt, root: usize, place: mir::Place<'tcx>, ownership_kind: OwnershipKind,
    ) -> EncodingResult<vir::Expr> {
        let place_ty = self.get_place_ty(place).ty;
        let ownership_domain = OwnershipDomain::encode(self.encoder, place_ty)?;
        let attr_function = if call_or_stmt.is_call() {
            ownership_domain.framed_call_fact_function(ownership_kind)?
        } else {
            ownership_domain.framed_stmt_fact_function(ownership_kind)?
        };
        let place_addr = self.encode_place_address(place, Version::Old)?; // Curr should work too
        let old_version = self.encode_version(Version::Old);
        let curr_version = self.encode_version(Version::CurrPre);
        Ok(attr_function.apply3(place_addr, old_version, curr_version))
    }

    fn get_deeply_unreachable_places_at(&self, location: mir::Location) -> SpannedEncodingResult<FxHashSet<Place<'tcx>>> {
        let stmt_or_term = self.mir.stmt_at(location);
        let span = self.get_span_of_location(location);
        if stmt_or_term.is_left() {
            let Some(unreachable) = self.unreachable_facts().lookup_after(location) else {
                error_internal!(span => "Deeply unreachable paths not available after location {:?}", location);
            };
            Ok(unreachable.get_deeply_unreachable_places())
        } else {
            let Some(unreachable) = self.unreachable_facts().lookup_after_block(location.block) else {
                error_internal!(span => "Deeply unreachable paths not available after location {:?}", location);
            };
            // All the successors should have the same unreachable facts.
            Ok(unreachable.values().next().map(|s| s.get_deeply_unreachable_places()).unwrap_or_default())
        }
    }

    fn get_shallowly_unreachable_places_at(&self, location: mir::Location) -> SpannedEncodingResult<FxHashSet<Place<'tcx>>> {
        let stmt_or_term = self.mir.stmt_at(location);
        let span = self.get_span_of_location(location);
        if stmt_or_term.is_left() {
            let Some(unreachable) = self.unreachable_facts().lookup_after(location) else {
                error_internal!(span => "Shallowly unreachable paths not available after location {:?}", location);
            };
            Ok(unreachable.get_shallowly_unreachable_places())
        } else {
            let Some(unreachable) = self.unreachable_facts().lookup_after_block(location.block) else {
                error_internal!(span => "Shallowly unreachable paths not available after location {:?}", location);
            };
            // All the successors should have the same unreachable facts.
            Ok(unreachable.values().next().map(|s| s.get_shallowly_unreachable_places()).unwrap_or_default())
        }
    }
}
