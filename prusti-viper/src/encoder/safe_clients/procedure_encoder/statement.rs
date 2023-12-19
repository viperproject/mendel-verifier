// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use crate::encoder::safe_clients::procedure_encoder::*;
use analysis::mir_utils::Place;
use analysis::mir_utils::PlaceImpl;
use analysis::mir_utils::place_ref_to_place;
use analysis::mir_utils::remove_place_from_set;
use ownership_domain::{OwnershipDomain, OwnershipKind};
use prusti_rustc_interface::middle::mir::visit::{PlaceContext, Visitor};

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    /// Note: it's better to call `encode_statement_at` instead of this method.
    pub(super) fn encode_statement(
        &self,
        stmt: &mir::Statement<'tcx>,
        location: mir::Location,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!(
            "Encode statement '{:?}', location: {:?}, span: {:?}",
            stmt.kind, location, stmt.source_info.span
        );

        let mut stmts = vec![];
        let span = self.get_span_of_location(location);

        let encoding_stmts = match stmt.kind {
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(..)
            | mir::StatementKind::Nop => vec![],

            mir::StatementKind::Assign(box (lhs, ref rhs)) => {
                let lhs_ty = self.get_place_ty(lhs).ty;
                let rhs_snapshot = self.encode_rvalue_snapshot(rhs, Version::Old).with_span(span)?;
                let lhs_snapshot = self.encode_place_snapshot(lhs, Version::CurrOld).with_span(span)?;
                trace!("Encoding of {lhs:?} = {rhs:?} is: {lhs_snapshot} == {rhs_snapshot}");
                let mut assign_stmts = vec![
                    vir::Stmt::inhale(vir_expr!{ [lhs_snapshot] == [rhs_snapshot] })
                ];

                if lhs.projection.last() == Some(&mir::ProjectionElem::Deref) {
                    let lhs_ref = mir::Place {
                        local: lhs.local,
                        projection: self.tcx().intern_place_elems(&lhs.projection[..lhs.projection.len() - 1]),
                    };
                    let lhs_ref_ty = self.get_place_ty(lhs_ref).ty;
                    let old_lhs_ref_snap = self.encode_place_snapshot(lhs_ref, Version::Old).with_span(span)?;
                    let curr_lhs_ref_snap = self.encode_place_snapshot(lhs_ref, Version::CurrOld).with_span(span)?;
                    let old_lhs_target = self.encode_snapshot_domain(SnapshotKind::Memory, lhs_ref_ty).with_span(span)?
                        .target_address_function().with_span(span)?.apply1(old_lhs_ref_snap);
                    let curr_lhs_target = self.encode_snapshot_domain(SnapshotKind::Memory, lhs_ref_ty).with_span(span)?
                        .target_address_function().with_span(span)?.apply1(curr_lhs_ref_snap);
                    trace!("Encoding of {lhs:?} = {rhs:?} doesn't change the target address");
                    assign_stmts.extend(vec![
                        vir::Stmt::comment(format!("Target of {lhs_ref:?} doesn't change")),
                        vir::Stmt::inhale(vir::Expr::eq_cmp(old_lhs_target, curr_lhs_target)),
                    ]);
                }

                if let &mir::Rvalue::Use(mir::Operand::Move(rhs_place)) = rhs {
                    // The move assignment has stronger guarantees than the copy or use assignment
                    let old_rhs_address = self.encode_place_address(rhs_place, Version::Old).with_span(span)?;
                    let curr_lhs_address = self.encode_place_address(lhs, Version::CurrOld).with_span(span)?;
                    let old_version = self.encode_version(Version::Old);
                    let curr_version = self.encode_version(Version::CurrOld);
                    let ownership_domain = OwnershipDomain::encode(self.encoder, lhs_ty).with_span(span)?;
                    let move_fact = ownership_domain.moved_fact_function().with_span(span)?.apply4(
                        old_rhs_address,
                        old_version,
                        curr_lhs_address,
                        curr_version,
                    );
                    trace!("Encoding of {lhs:?} = move {rhs:?} is also: {move_fact:?}");
                    assign_stmts.extend(vec![
                        vir::Stmt::comment(format!("Place {rhs_place:?} has been moved")),
                        vir::Stmt::inhale(move_fact),
                    ]);
                } else {
                    // Frame owned places that are used, but not mutated.
                    let tcx = self.tcx();
                    let Some(facts) = self.ownership_facts().lookup_before(location) else {
                        error_internal!(span => "Ownership facts not available before {:?}", location);
                    };
                    let mut owned_places = facts.get_definitely_owned().clone();
                    if let Some(lhs_mut_ref) = get_dereferenced_mut_ref(self.mir, tcx, lhs) {
                        remove_place_from_set(self.mir, tcx, lhs_mut_ref, &mut owned_places);
                    } else {
                        remove_place_from_set(self.mir, tcx, lhs.into(), &mut owned_places);
                    }
                    for (index, &framed_place) in owned_places.iter().enumerate() {
                        trace!("Frame place {framed_place:?}");
                        let place_address = self.encode_place_address(*framed_place, Version::Old).with_span(span)?;
                        let old_version = self.encode_version(Version::Old);
                        let curr_version = self.encode_version(Version::CurrOld);
                        let place_ty = self.get_place_ty(*framed_place).ty;
                        let ownership_domain = OwnershipDomain::encode(self.encoder, place_ty).with_span(span)?;
                        let framing_fact = ownership_domain
                            .framed_stmt_fact_function(OwnershipKind::WriteRef)
                            .with_span(span)?
                            .apply3(
                                //-1 - (index as isize), // To avoid clashing with the framing facts assumed later
                                place_address,
                                old_version,
                                curr_version,
                            );
                        assign_stmts.extend(vec![
                            vir::Stmt::comment(format!("Fully-owned used place {framed_place:?} does not change")),
                            vir::Stmt::inhale(framing_fact),
                        ]);
                    }
                }

                // Encode stronger properties for move operands in aggregate assignments
                if let mir::Rvalue::Aggregate(box kind, operands) = rhs {
                    let variant_idx = if let &mir::AggregateKind::Adt(_, variant_idx, _, _, _) = kind {
                        Some(variant_idx)
                    } else {
                        None
                    };
                    for (field_idx, operand) in operands.iter().enumerate() {
                        if let &mir::Operand::Move(place) = operand {
                            let old_place_address = self.encode_place_address(place, Version::Old).with_span(span)?;
                            let curr_lhs_address = self.encode_place_address(lhs, Version::CurrOld).with_span(span)?;
                            let lhs_address_domain = AddressDomain::encode(self.encoder, lhs_ty).with_span(span)?;
                            let curr_place_address = lhs_address_domain.adt_field_address_function(
                                variant_idx, field_idx.into()
                            ).with_span(span)?.apply1(curr_lhs_address);
                            let old_version = self.encode_version(Version::Old);
                            let curr_version = self.encode_version(Version::CurrOld);
                            let place_ty = self.get_place_ty(place).ty;
                            let ownership_domain = OwnershipDomain::encode(self.encoder, place_ty).with_span(span)?;
                            let move_fact = ownership_domain.moved_fact_function().with_span(span)?.apply4(
                                old_place_address,
                                old_version,
                                curr_place_address,
                                curr_version,
                            );
                            assign_stmts.extend(vec![
                                vir::Stmt::comment(format!("Place {place:?} has been moved")),
                                vir::Stmt::inhale(move_fact),
                            ]);
                        }
                    }
                }

                assign_stmts
            }

            _ => return Err(SpannedEncodingError::unsupported(
                format!("unsupported statement kind: {:?}", stmt.kind),
                span,
            )),
        };
        stmts.extend(encoding_stmts);
        self.set_stmts_default_pos(&mut stmts, stmt.source_info.span);
        Ok(stmts)
    }

    fn collect_used_places(&self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) -> FxHashSet<Place<'tcx>> {
        struct CollectMutRef<'mir, 'tcx: 'mir> {
            body: &'mir mir::Body<'tcx>,
            tcx: ty::TyCtxt<'tcx>,
            store: FxHashSet<Place<'tcx>>,
        }

        impl<'mir, 'tcx: 'mir> Visitor<'tcx> for CollectMutRef<'mir, 'tcx> {
            fn visit_place(
                &mut self,
                place: &mir::Place<'tcx>,
                _context: PlaceContext,
                _location: mir::Location,
            ) {
                self.store.insert((*place).into());
            }
        }

        let mut collector = CollectMutRef {
            body: self.mir,
            tcx: self.tcx(),
            store: FxHashSet::default(),
        };
        collector.visit_rvalue(rvalue, location);
        collector.store
    }
}

/// Get the first dereferences mutable reference
fn get_dereferenced_mut_ref<'tcx>(body: &mir::Body<'tcx>, tcx: ty::TyCtxt<'tcx>, place: mir::Place<'tcx>) -> Option<Place<'tcx>> {
    for (base, proj) in place.iter_projections() {
        if let mir::ProjectionElem::Deref = proj {
            let base_ty = base.ty(body, tcx).ty;
            if let ty::TyKind::Ref(_, _, mir::Mutability::Mut) = base_ty.kind() {
                return Some(Place::from_mir_place(place_ref_to_place(base, tcx)));
            }
            // Stop at the first dereference
            break;
        }
    }
    None
}
