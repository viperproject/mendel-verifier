// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum RvalueExpr<'tcx> {
    Constant(mir::Constant<'tcx>),
    Place(mir::Place<'tcx>),
    Projections {
        base: Box<MirExpr<'tcx>>,
        projections: Vec<mir::PlaceElem<'tcx>>,
    },
    UnaryOp {
        expr: Box<MirExpr<'tcx>>,
        op: mir::UnOp,
        span: Option<Span>,
    },
    BinaryOp {
        left: Box<MirExpr<'tcx>>,
        right: Box<MirExpr<'tcx>>,
        op: mir::BinOp,
        span: Option<Span>,
    },
    CheckedBinaryOp {
        left: Box<MirExpr<'tcx>>,
        right: Box<MirExpr<'tcx>>,
        op: mir::BinOp,
        span: Option<Span>,
    },
    Ref {
        expr: Box<MirExpr<'tcx>>,
        borrow_kind: mir::BorrowKind,
        region: ty::Region<'tcx>,
        span: Option<Span>,
    },
    AddressOf {
        expr: Box<MirExpr<'tcx>>,
        mutability: mir::Mutability,
        span: Option<Span>,
    },
    Aggregate {
        kind: mir::AggregateKind<'tcx>,
        fields: Vec<MirExpr<'tcx>>,
        span: Option<Span>,
    },
    Discriminant {
        expr: Box<MirExpr<'tcx>>,
        span: Option<Span>,
    },
    Cast {
        expr: Box<MirExpr<'tcx>>,
        kind: mir::CastKind,
        ty: ty::Ty<'tcx>,
        span: Option<Span>,
    },
}

impl<'tcx> RvalueExpr<'tcx> {
    pub fn from_place(place: mir::Place<'tcx>) -> RvalueExpr<'tcx> {
        RvalueExpr::Place(place)
    }

    pub fn from_place_ref(place: mir::PlaceRef<'tcx>, tcx: ty::TyCtxt<'tcx>) -> RvalueExpr<'tcx> {
        RvalueExpr::Place(mir::Place {
            projection: tcx.mk_place_elems(place.projection.iter()),
            local: place.local,
        })
    }

    pub fn from_operand(operand: &mir::Operand<'tcx>) -> EncodingResult<RvalueExpr<'tcx>> {
        Ok(match operand {
            &mir::Operand::Copy(place) | &mir::Operand::Move(place) => {
                RvalueExpr::from_place(place)
            }
            &mir::Operand::Constant(box constant) => {
                RvalueExpr::Constant(constant)
            }
        })
    }

    pub fn from_rvalue(rvalue: &mir::Rvalue<'tcx>, span: Option<Span>) -> EncodingResult<RvalueExpr<'tcx>> {
        Ok(match rvalue {
            mir::Rvalue::Use(ref operand) => {
                RvalueExpr::from_operand(operand)?
            }
            mir::Rvalue::Aggregate(box kind, ref operands) => {
                let mut fields = Vec::with_capacity(operands.len());
                for operand in operands {
                    fields.push(RvalueExpr::from_operand(operand)?.into());
                }
                RvalueExpr::Aggregate { kind: kind.clone(), fields, span}
            }
            &mir::Rvalue::BinaryOp(op, box(ref left, ref right)) => {
                RvalueExpr::BinaryOp {
                    op,
                    left: box RvalueExpr::from_operand(left)?.into(),
                    right: box RvalueExpr::from_operand(right)?.into(),
                    span,
                }
            }
            &mir::Rvalue::CheckedBinaryOp(op, box (ref left, ref right)) => {
                RvalueExpr::CheckedBinaryOp {
                    op,
                    left: box RvalueExpr::from_operand(left)?.into(),
                    right: box RvalueExpr::from_operand(right)?.into(),
                    span,
                }
            }
            &mir::Rvalue::UnaryOp(op, ref operand) => {
                RvalueExpr::UnaryOp {
                    op,
                    expr: box RvalueExpr::from_operand(operand)?.into(),
                    span,
                }
            }
            &mir::Rvalue::Discriminant(place) => {
                RvalueExpr::Discriminant {
                    expr: box RvalueExpr::from_place(place).into(),
                    span,
                }
            }
            &mir::Rvalue::Ref(region, borrow_kind, place) => {
                RvalueExpr::Ref {
                    expr: box RvalueExpr::from_place(place).into(),
                    borrow_kind,
                    region,
                    span,
                }
            }
            &mir::Rvalue::AddressOf(mutability, place) => {
                RvalueExpr::AddressOf {
                    expr: box RvalueExpr::from_place(place).into(),
                    mutability,
                    span,
                }
            }
            &mir::Rvalue::Cast(kind, ref operand, ty) => {
                RvalueExpr::Cast {
                    expr: box RvalueExpr::from_operand(operand)?.into(),
                    kind,
                    ty,
                    span,
                }
            }
            _ => {
                error_unsupported!("unsupported right-hand-side of assignment: {:?}", rvalue);
            }
        })
    }

    /// Returns the span of the expression, if any.
    pub fn span(&self) -> Option<Span> {
        match self {
            RvalueExpr::Constant(c) => Some(c.span),
            RvalueExpr::Place(_) => None,
            RvalueExpr::Projections { base, .. } => base.span(),
            RvalueExpr::UnaryOp { span, .. }
            | RvalueExpr::BinaryOp { span, .. }
            | RvalueExpr::CheckedBinaryOp { span, .. }
            | RvalueExpr::Ref { span, .. }
            | RvalueExpr::AddressOf { span, .. }
            | RvalueExpr::Aggregate { span, .. }
            | RvalueExpr::Discriminant { span, .. }
            | RvalueExpr::Cast { span, .. } => *span,
        }
    }

    /// Returns the type of the expression.
    pub fn ty<D>(&self, local_decls: &D, tcx: ty::TyCtxt<'tcx>) -> PlaceTy<'tcx>
        where
            D: mir::HasLocalDecls<'tcx>
    {
        match self {
            RvalueExpr::Constant(c) => PlaceTy::from_ty(c.ty()),
            &RvalueExpr::Place(p) => p.ty(local_decls, tcx),
            RvalueExpr::Projections { base, projections } => {
                let base_ty = base.ty(local_decls, tcx);
                projections
                    .iter()
                    .fold(base_ty, |place_ty, &elem| {
                        place_ty.projection_ty(tcx, elem)
                    })
            }
            RvalueExpr::UnaryOp { expr, .. } => {
                expr.ty(local_decls, tcx)
            }
            RvalueExpr::BinaryOp { left, right, op, .. } => {
                let left_ty = left.ty(local_decls, tcx).ty;
                let right_ty = right.ty(local_decls, tcx).ty;
                let op_ty = op.ty(tcx, left_ty, right_ty);
                PlaceTy::from_ty(op_ty)
            }
            RvalueExpr::CheckedBinaryOp { left, right, op, .. } => {
                let left_ty = left.ty(local_decls, tcx).ty;
                let right_ty = right.ty(local_decls, tcx).ty;
                let op_ty = op.ty(tcx, left_ty, right_ty);
                let ty = tcx.intern_tup(&[op_ty, tcx.types.bool]);
                PlaceTy::from_ty(ty)
            }
            &RvalueExpr::Ref { ref expr, borrow_kind, region, .. } => {
                let expr_ty = expr.ty(local_decls, tcx).ty;
                let ty = tcx.mk_ref(region, ty::TypeAndMut { ty: expr_ty, mutbl: borrow_kind.to_mutbl_lossy() });
                PlaceTy::from_ty(ty)
            }
            &RvalueExpr::AddressOf { ref expr, mutability, .. } => {
                let expr_ty = expr.ty(local_decls, tcx).ty;
                let ty = tcx.mk_ptr(ty::TypeAndMut { ty: expr_ty, mutbl: mutability });
                PlaceTy::from_ty(ty)
            }
            RvalueExpr::Aggregate { kind, fields, .. } => {
                let ty = match *kind {
                    mir::AggregateKind::Array(ty) => tcx.mk_array(ty, fields.len() as u64),
                    mir::AggregateKind::Tuple => tcx.mk_tup(fields.iter().map(|f| f.ty(local_decls, tcx).ty)),
                    mir::AggregateKind::Adt(did, _, substs, _, _) => {
                        tcx.bound_type_of(did).subst(tcx, substs)
                    }
                    mir::AggregateKind::Closure(did, substs) => tcx.mk_closure(did.to_def_id(), substs),
                    mir::AggregateKind::Generator(did, substs, movability) => {
                        tcx.mk_generator(did.to_def_id(), substs, movability)
                    }
                };
                PlaceTy::from_ty(ty)
            }
            RvalueExpr::Discriminant { expr, .. } => {
                let ty = expr.ty(local_decls, tcx).ty.discriminant_ty(tcx);
                PlaceTy::from_ty(ty)
            }
            &RvalueExpr::Cast { ty, .. } => PlaceTy::from_ty(ty),
        }
    }

    /// Visits the direct `MirExpr` children of the expression.
    pub fn visit_subexpr<E>(&self, visitor: &dyn Fn(&MirExpr<'tcx>) -> Result<(), E>) -> Result<(), E> {
        match self {
            RvalueExpr::Constant(_) => {}
            RvalueExpr::Place(_) => {}
            RvalueExpr::Projections { base, projections } => {
                visitor(base)?;
            }
            RvalueExpr::UnaryOp { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::BinaryOp { left: lhs, right: rhs, .. } => {
                visitor(lhs)?;
                visitor(rhs)?;
            }
            RvalueExpr::CheckedBinaryOp { left: lhs, right: rhs, .. } => {
                visitor(lhs)?;
                visitor(rhs)?;
            }
            RvalueExpr::Ref { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::AddressOf { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::Aggregate { fields, .. } => {
                for field in fields {
                    visitor(field)?;
                }
            }
            RvalueExpr::Discriminant { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::Cast { expr, .. } => {
                visitor(expr)?;
            }
        }
        Ok(())
    }

    /// Visits the direct `MirExpr` children of the expression.
    pub fn visit_subexpr_mut<E>(&mut self, visitor: &dyn Fn(&mut MirExpr<'tcx>) -> Result<(), E>) -> Result<(), E> {
        match self {
            RvalueExpr::Constant(_) => {}
            RvalueExpr::Place(_) => {}
            RvalueExpr::Projections { base, projections } => {
                visitor(base)?;
            }
            RvalueExpr::UnaryOp { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::BinaryOp { left: lhs, right: rhs, .. } => {
                visitor(lhs)?;
                visitor(rhs)?;
            }
            RvalueExpr::CheckedBinaryOp { left: lhs, right: rhs, .. } => {
                visitor(lhs)?;
                visitor(rhs)?;
            }
            RvalueExpr::Ref { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::AddressOf { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::Aggregate { fields, .. } => {
                for field in fields {
                    visitor(field)?;
                }
            }
            RvalueExpr::Discriminant { expr, .. } => {
                visitor(expr)?;
            }
            RvalueExpr::Cast { expr, .. } => {
                visitor(expr)?;
            }
        }
        Ok(())
    }

    /// Visits the direct `RvalueExpr` children of the expression.
    pub fn visit_subrvalue_mut<E>(&mut self, visitor: &dyn Fn(&mut RvalueExpr<'tcx>) -> Result<(), E>) -> Result<(), E> {
        match self {
            RvalueExpr::Constant(_) => {}
            RvalueExpr::Place(_) => {}
            RvalueExpr::Projections { base, projections } => {
                base.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::UnaryOp { expr, .. } => {
                expr.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::BinaryOp { left: lhs, right: rhs, .. } => {
                lhs.visit_subrvalue_mut(visitor)?;
                rhs.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::CheckedBinaryOp { left: lhs, right: rhs, .. } => {
                lhs.visit_subrvalue_mut(visitor)?;
                rhs.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::Ref { expr, .. } => {
                expr.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::AddressOf { expr, .. } => {
                expr.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::Aggregate { fields, .. } => {
                for field in fields {
                    field.visit_subrvalue_mut(visitor)?;
                }
            }
            RvalueExpr::Discriminant { expr, .. } => {
                expr.visit_subrvalue_mut(visitor)?;
            }
            RvalueExpr::Cast { expr, .. } => {
                expr.visit_subrvalue_mut(visitor)?;
            }
        }
        Ok(())
    }

    /// Visits all the `RvalueExpr` in the expression.
    pub fn visit_all_rvalues<E>(&self, visitor: &mut dyn FnMut(&RvalueExpr<'tcx>) -> Result<(), E>) -> Result<(), E> {
        visitor(self)?;
        match self {
            RvalueExpr::Constant(_) => {}
            RvalueExpr::Place(_) => {}
            RvalueExpr::Projections { base, projections } => {
                base.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::UnaryOp { expr, .. } => {
                expr.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::BinaryOp { left: lhs, right: rhs, .. } => {
                lhs.visit_all_rvalues(visitor)?;
                rhs.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::CheckedBinaryOp { left: lhs, right: rhs, .. } => {
                lhs.visit_all_rvalues(visitor)?;
                rhs.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::Ref { expr, .. } => {
                expr.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::AddressOf { expr, .. } => {
                expr.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::Aggregate { fields, .. } => {
                for field in fields {
                    field.visit_all_rvalues(visitor)?;
                }
            }
            RvalueExpr::Discriminant { expr, .. } => {
                expr.visit_all_rvalues(visitor)?;
            }
            RvalueExpr::Cast { expr, .. } => {
                expr.visit_all_rvalues(visitor)?;
            }
        }
        Ok(())
    }

    /// Collapse consecutive projections and simplify dereferentiations.
    pub fn normalize(&mut self) {
        self.visit_subrvalue_mut::<()>(&|e| { e.normalize(); Ok(()) }).unwrap();
        loop {
            // Merge consecutive projections, but not `RvalueExpr::Place` because we want to know
            // which places directly come from an argument.
            if let RvalueExpr::Projections {
                base: box MirExpr::Rvalue(RvalueExpr::Projections { base, projections: inner }),
                projections: outer,
            } = self {
                let projections = inner.iter().copied().chain(outer.iter().copied()).collect();
                *self = RvalueExpr::Projections {
                    base: base.clone(),
                    projections,
                };
                continue;
            }
            // Simplify dereferentiation of references
            // Disabled because we want to know which places directly come from an argument.
            /*if let RvalueExpr::Projections {
                base: box MirExpr::Rvalue(RvalueExpr::Ref { expr, .. }),
                projections,
            } = self {
                if let [mir::ProjectionElem::Deref, tail_projections @ ..] = &projections[..] {
                    let projections = tail_projections.iter().skip(1).copied().collect();
                    *self = RvalueExpr::Projections { base: expr.clone(), projections };
                    continue;
                }
            }*/
            // TODO: Simplify reference of dereferentiation, if the types are the same
            break;
        }
    }

    /// Replaces all places in the expression with a new `MirExpr`.
    pub fn replace_places<E>(&mut self, visitor: &dyn Fn(mir::Place<'tcx>) -> Result<Option<MirExpr<'tcx>>, E>) -> Result<(), E> {
        match self {
            RvalueExpr::Constant(_) => {}
            &mut RvalueExpr::Place(place) => {
                if let Some(new_expr) = visitor(place)? {
                    *self = RvalueExpr::Projections {
                        base: box new_expr,
                        projections: vec![],
                    };
                }
            }
            RvalueExpr::Projections { base, projections } => {
                base.replace_places(visitor)?;
            }
            RvalueExpr::UnaryOp { expr, .. } => {
                expr.replace_places(visitor)?;
            }
            RvalueExpr::BinaryOp { left: lhs, right: rhs, .. } => {
                lhs.replace_places(visitor)?;
                rhs.replace_places(visitor)?;
            }
            RvalueExpr::CheckedBinaryOp { left: lhs, right: rhs, .. } => {
                lhs.replace_places(visitor)?;
                rhs.replace_places(visitor)?;
            }
            RvalueExpr::Ref { expr, .. } => {
                expr.replace_places(visitor)?;
            }
            RvalueExpr::AddressOf { expr, .. } => {
                expr.replace_places(visitor)?;
            }
            RvalueExpr::Aggregate { fields, .. } => {
                for field in fields {
                    field.replace_places(visitor)?;
                }
            }
            RvalueExpr::Discriminant { expr, .. } => {
                expr.replace_places(visitor)?;
            }
            RvalueExpr::Cast { expr, .. } => {
                expr.replace_places(visitor)?;
            }
        }
        Ok(())
    }

    /// Replaces all locals in the expression with a new `MirExpr`.
    pub fn replace_locals<E>(&mut self, visitor: &dyn Fn(mir::Local) -> Result<Option<MirExpr<'tcx>>, E>) -> Result<(), E> {
        self.replace_places(&|place| {
            if let Some(new_expr) = visitor(place.local)? {
                Ok(Some(RvalueExpr::Projections {
                    base: box new_expr,
                    projections: place.projection.iter().collect(),
                }.into()))
            } else {
                Ok(None)
            }
        })
    }

    /// If the expression is equivalent to a `mir::Place`, return it.
    pub fn as_place(&self, tcx: ty::TyCtxt<'tcx>) -> Option<mir::Place<'tcx>> {
        match self {
            &RvalueExpr::Place(place) => Some(place),
            RvalueExpr::Projections { base: box MirExpr::Rvalue(base), projections } => {
                let mut place = base.as_place(tcx)?;
                place = place.project_deeper(projections, tcx);
                Some(place)
            }
            _ => None,
        }
    }
}

impl std::fmt::Display for RvalueExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RvalueExpr::Constant(c) => write!(f, "{c}"),
            RvalueExpr::Place(place) => {
                write!(f, "{:?}", place.local)?;
                for projection in place.projection {
                    write!(f, ".{projection:?}")?;
                }
                Ok(())
            }
            RvalueExpr::Projections { base, projections } => {
                write!(f, "{base}")?;
                for projection in projections {
                    write!(f, ".{projection:?}")?;
                }
                Ok(())
            }
            RvalueExpr::UnaryOp { op, expr, .. } => write!(f, "{op:?}({expr})"),
            RvalueExpr::BinaryOp { op, left, right, .. } => write!(f, "{op:?}({left}, {right})"),
            RvalueExpr::CheckedBinaryOp { op, left, right, .. } => write!(f, "Checked{op:?}({left}, {right})"),
            RvalueExpr::Ref { expr, borrow_kind: mir::BorrowKind::Shared, .. } => write!(f, "{expr}.&"),
            RvalueExpr::Ref { expr, borrow_kind: mir::BorrowKind::Shallow, .. } => write!(f, "{expr}.&shallow"),
            RvalueExpr::Ref { expr, borrow_kind: mir::BorrowKind::Unique, .. } => write!(f, "{expr}.&unique"),
            RvalueExpr::Ref { expr, borrow_kind: mir::BorrowKind::Mut { .. }, .. } => write!(f, "{expr}.&mut"),
            RvalueExpr::AddressOf { expr, .. } => write!(f, "{expr}.address"),
            RvalueExpr::Aggregate { kind, fields, .. } => {
                write!(f, "{kind:?}(")?;
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{field}")?;
                }
                write!(f, ")")
            }
            RvalueExpr::Discriminant { expr, .. } => write!(f, "discriminant({expr})"),
            RvalueExpr::Cast { expr, kind, .. } => write!(f, "cast({expr}, {kind:?})"),
        }
    }
}
