// © 2023, ETH Zurichencode_deref
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;
use encoding_structs::prelude::pure_encoder::MirInterpreter;

/// Trait used to encode the snapshot of a `mir::Place`.
pub trait PlaceEncoder<'v, 'tcx: 'v>: WithLocalTy<'v, 'tcx> {
    fn encode_local_snapshot(&self, local: mir::Local) -> SpannedEncodingResult<SnapshotExpr>;
    fn encode_local_address(&self, local: mir::Local) -> SpannedEncodingResult<Option<vir::Expr>>;
    fn encode_version(&self) -> EncodingResult<Option<vir::LocalVar>>;
    fn encode_promoted_mir_expr_snapshot(
        &self,
        mir_expr: &MirExpr<'tcx>,
    ) -> EncodingResult<SnapshotExpr>;

    fn encode_deref(
        &self,
        address: vir::Expr,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<Option<SnapshotExpr>> {
        if let Some(version) = self.encode_version()? {
            let address_domain = AddressDomain::encode(self.encoder(), ty)?;
            let expr = address_domain.deref_function()?.apply2(address, version);
            Ok(Some(SnapshotExpr::new_memory(expr)))
        } else {
            Ok(None)
        }
    }

    fn encode_place_snapshot(&self, place: mir::Place<'tcx>) -> EncodingResult<SnapshotExpr> {
        let mut place_ty = PlaceTy::from_ty(self.get_local_ty(place.local));
        let mut place_snapshot = self.encode_local_snapshot(place.local)?;
        for projection in place.projection {
            place_snapshot =
                self.encode_place_projection_snapshot(place_snapshot, place_ty, projection)?;
            place_ty = place_ty.projection_ty(self.tcx(), projection);
        }
        Ok(place_snapshot)
    }

    /// Encode the address of a place.
    fn encode_place_address(&self, place: mir::Place<'tcx>) -> EncodingResult<Option<vir::Expr>> {
        let frame = open_trace!("encode_place_address", format!("{place:?}"));

        let mut place_ty = PlaceTy::from_ty(self.get_local_ty(place.local));
        let Some(mut place_address) = self.encode_local_address(place.local)? else {
            return Ok(None);
        };

        for projection in place.projection {
            let Some(new_expr) = self.encode_place_projection_address(
                place_address,
                place_ty,
                projection,
            )? else {
                return Ok(None);
            };
            place_address = new_expr;
            place_ty = place_ty.projection_ty(self.tcx(), projection);
        }

        close_trace!(frame, &place_address);
        Ok(Some(place_address))
    }

    fn encode_place_projection_snapshot(
        &self,
        base_snapshot: SnapshotExpr,
        base_ty: PlaceTy<'tcx>,
        projection: mir::PlaceElem<'tcx>,
    ) -> EncodingResult<SnapshotExpr> {
        Ok(match projection {
            mir::ProjectionElem::Downcast(..) => {
                // The snapshot doesn't change.
                base_snapshot
            }
            mir::ProjectionElem::Field(ref field, field_ty) => {
                let kind = base_snapshot.kind();
                SnapshotExpr::new(
                    self.encode_snapshot_domain(kind, base_ty.ty)?
                        .adt_field_function(base_ty.variant_index, *field)?
                        .apply1(base_snapshot),
                    kind,
                )
            }
            mir::ProjectionElem::Deref => {
                match *base_ty.ty.kind() {
                    ty::TyKind::Ref(_, target_ty, _) => {
                        let kind = base_snapshot.kind();
                        SnapshotExpr::new(
                            self.encode_snapshot_domain(kind, base_ty.ty)?
                                .target_snapshot_function()?
                                .apply1(base_snapshot),
                            kind,
                        )
                    }
                    ty::TyKind::RawPtr(ty::TypeAndMut { ty: target_ty, .. }) => {
                        let kind = base_snapshot.kind();
                        let address = self
                            .encode_snapshot_domain(kind, base_ty.ty)?
                            .target_address_function()?
                            .apply1(base_snapshot);
                        let Some(version) = self.encode_version()? else {
                            error_incorrect!(
                                "dereferencing a raw pointer is only allowed in pure unstable \
                                ghost code"
                            );
                        };
                        // TODO(fpoli): Add check to only allow in ghost code
                        SnapshotExpr::new(
                            AddressDomain::encode(self.encoder(), target_ty)?
                                .deref_function()?
                                .apply2(address, version),
                            kind,
                        )
                    }
                    // Dereference the pointer in the NonNull field in the Unique field of the Box.
                    ty::Adt(adt_def, substs) if adt_def.is_box() => {
                        let (ptr_snap, ptr_ty) = self.encode_box_content(base_snapshot, base_ty)?;
                        self.encode_place_projection_snapshot(
                            ptr_snap,
                            ptr_ty,
                            mir::ProjectionElem::Deref,
                        )?
                    }
                    _ => {
                        error_unsupported!("unsupported dereferentiation of type {:?}", base_ty);
                    }
                }
            }
            _ => {
                error_unsupported!("unsupported place projection {:?}", projection);
            }
        })
    }

    fn encode_place_projection_address(
        &self,
        base_address: vir::Expr,
        base_ty: PlaceTy<'tcx>,
        projection: mir::PlaceElem<'tcx>,
    ) -> EncodingResult<Option<vir::Expr>> {
        Ok(Some(match projection {
            mir::ProjectionElem::Downcast(..) => {
                // The address doesn't change.
                base_address
            }
            mir::ProjectionElem::Field(ref field, field_ty) => {
                // Directly access the field.
                let address_domain = AddressDomain::encode(self.encoder(), base_ty.ty)?;
                address_domain
                    .adt_field_address_function(base_ty.variant_index, *field)?
                    .apply1(base_address)
            }
            mir::ProjectionElem::Deref => {
                match base_ty.ty.kind() {
                    &ty::TyKind::Ref(_, target_ty, _) => {
                        // Take the address from the dereferenced snapshot.
                        let Some(place_snapshot) = self.encode_deref(base_address, base_ty.ty)? else {
                            return Ok(None);
                        };
                        debug_assert!(place_snapshot.kind().is_memory());
                        let snapshot_domain =
                            self.encode_snapshot_domain(place_snapshot.kind(), base_ty.ty)?;
                        snapshot_domain
                            .target_address_function()?
                            .apply1(place_snapshot)
                    }
                    ty::Adt(adt_def, substs) if adt_def.is_box() => {
                        // Take the address from the dereferenced snapshot.
                        let Some(place_snapshot) = self.encode_deref(base_address, base_ty.ty)? else {
                            return Ok(None);
                        };
                        debug_assert!(place_snapshot.kind().is_memory());
                        let (ptr_snapshot, ptr_ty) =
                            self.encode_box_content(place_snapshot, base_ty)?;
                        debug_assert!(ptr_snapshot.kind().is_memory());
                        let snapshot_domain =
                            self.encode_snapshot_domain(ptr_snapshot.kind(), ptr_ty.ty)?;
                        snapshot_domain
                            .target_address_function()?
                            .apply1(ptr_snapshot)
                    }
                    _ => {
                        error_unsupported!("unsupported dereferentiation of type {:?}", base_ty);
                    }
                }
            }
            _ => {
                error_unsupported!("unsupported place projection {:?}", projection);
            }
        }))
    }

    fn encode_operand_address(
        &self,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<Option<vir::Expr>> {
        match operand {
            &mir::Operand::Copy(place) | &mir::Operand::Move(place) => {
                self.encode_place_address(place)
            }
            &mir::Operand::Constant(box constant) => Ok(None),
        }
    }

    fn encode_operand_snapshot(
        &self,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<SnapshotExpr> {
        // This has some repetition with encode_rvalue_expr_snapshot
        match operand {
            &mir::Operand::Copy(place) | &mir::Operand::Move(place) => {
                self.encode_place_snapshot(place)
            }
            &mir::Operand::Constant(box constant) => self.encode_constant_snapshot(constant),
        }
    }

    fn encode_constant_snapshot(
        &self,
        constant: mir::Constant<'tcx>,
    ) -> EncodingResult<SnapshotExpr> {
        if let mir::ConstantKind::Unevaluated(unevaluated_const, _) = constant.literal {
            let mir::UnevaluatedConst {
                def: def_id,
                substs,
                promoted,
            } = unevaluated_const;
            let promoted_id = promoted.expect("unevaluated const should have a promoted ID");
            let promoted_bodies = self.tcx().promoted_mir_opt_const_arg(def_id);
            let param_env = ty::ParamEnv::empty();
            let mir = self.tcx().subst_and_normalize_erasing_regions(
                substs,
                param_env,
                promoted_bodies[promoted_id].clone(),
            );
            let mir_interpreter = MirInterpreter::new(&mir, self.tcx());
            let mir_expr = mir_interpreter.encode_body()?;
            self.encode_promoted_mir_expr_snapshot(&mir_expr)
        } else {
            let ty = constant.literal.ty();
            // Both mem and value snapshots would work here.
            Ok(SnapshotExpr::new_memory(
                MemSnapshotDomain::encode(self.encoder(), ty)?
                    .constant_snapshot(self.tcx(), constant)?,
            ))
        }
    }

    /// Converts a list of expressions of different shapshot domains into a list of the same domain.
    fn unify_typed_expressions(
        &self,
        exprs: Vec<SnapshotExpr>,
        types: &[ty::Ty<'tcx>],
    ) -> EncodingResult<(Vec<vir::Expr>, SnapshotKind)> {
        let all_memory = exprs.iter().all(|expr| expr.kind().is_memory());
        if all_memory {
            return Ok((
                exprs.into_iter().map(|expr| expr.into_expr()).collect(),
                SnapshotKind::Memory,
            ));
        }
        let mut casted_exprs = Vec::with_capacity(exprs.len());
        for (expr, &ty) in exprs.into_iter().zip(types) {
            casted_exprs.push(self.convert_to_value_snapshot(expr, ty)?);
        }
        Ok((casted_exprs, SnapshotKind::Value))
    }

    /// Converts a snapshot encoding to a value snapshot encoding, if necessary.
    fn convert_to_value_snapshot(
        &self,
        expr: SnapshotExpr,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Expr> {
        let frame = open_trace!(
            "convert_to_value_snapshot",
            format!("{:?}: {ty:?}", expr.kind())
        );
        if expr.kind().is_value() {
            Ok(expr.into_expr())
        } else {
            Ok(ValueSnapshotDomain::encode(self.encoder(), ty)?
                .conversion_from_memory_function()?
                .apply1(expr))
        }
    }

    /// Converts a snapshot encoding to a memory snapshot encoding, if necessary.
    fn convert_to_memory_snapshot(
        &self,
        expr: SnapshotExpr,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Expr> {
        let frame = open_trace!(
            "convert_to_memory_snapshot",
            format!("{:?}: {ty:?}", expr.kind())
        );
        if expr.kind().is_memory() {
            Ok(expr.into_expr())
        } else if ty.is_unsafe_ptr() {
            // The conversion function doesn't always exist
            let expr_target_address = self
                .encode_snapshot_domain(expr.kind(), ty)?
                .target_address_function()?
                .apply1(expr);
            Ok(MemSnapshotDomain::encode(self.encoder(), ty)?
                .constructor_function()?
                .apply1(expr_target_address))
        } else {
            Ok(ValueSnapshotDomain::encode(self.encoder(), ty)?
                .conversion_to_memory_function()?
                .apply1(expr))
        }
    }

    /// Given the snapshot of a Box, returns the snapshot and type of its inner pointer.
    fn encode_box_content(
        &self,
        box_snapshot: SnapshotExpr,
        box_ty: PlaceTy<'tcx>,
    ) -> EncodingResult<(SnapshotExpr, PlaceTy<'tcx>)> {
        let ty::Adt(adt_def, substs) = box_ty.ty.kind() else {
            error_internal!("expected Box; got {:?}", box_ty.ty);
        };
        debug_assert!(adt_def.is_box());
        let unique_field = if let Some(variant) = adt_def.variants().get(0u32.into()) {
            mir::ProjectionElem::Field(
                mir::Field::from_u32(0),
                variant.fields[0].ty(self.tcx(), substs),
            )
        } else {
            error_internal!("Box has no variants");
        };
        let unique_ty = box_ty.projection_ty(self.tcx(), unique_field);
        let nonnull_field =
            if let ty::TyKind::Adt(unique_adt_def, unique_substs) = unique_ty.ty.kind() {
                if let Some(variant) = unique_adt_def.variants().get(0u32.into()) {
                    mir::ProjectionElem::Field(
                        mir::Field::from_u32(0),
                        variant.fields[0].ty(self.tcx(), unique_substs),
                    )
                } else {
                    error_internal!("Unique has no variants");
                }
            } else {
                error_internal!("Box field is not an Adt");
            };
        let nonnull_ty = unique_ty.projection_ty(self.tcx(), nonnull_field);
        let ptr_field =
            if let ty::TyKind::Adt(nonnull_adt_def, nonnull_substs) = nonnull_ty.ty.kind() {
                if let Some(variant) = nonnull_adt_def.variants().get(0u32.into()) {
                    mir::ProjectionElem::Field(
                        mir::Field::from_u32(0),
                        variant.fields[0].ty(self.tcx(), nonnull_substs),
                    )
                } else {
                    error_internal!("NonNull has no variants");
                }
            } else {
                error_internal!("Unique field is not an Adt");
            };
        let ptr_ty = nonnull_ty.projection_ty(self.tcx(), ptr_field);
        let unique_snap =
            self.encode_place_projection_snapshot(box_snapshot, box_ty, unique_field)?;
        let nonnull_snap =
            self.encode_place_projection_snapshot(unique_snap, unique_ty, nonnull_field)?;
        let ptr_snap =
            self.encode_place_projection_snapshot(nonnull_snap, nonnull_ty, ptr_field)?;
        Ok((ptr_snap, ptr_ty))
    }
}
