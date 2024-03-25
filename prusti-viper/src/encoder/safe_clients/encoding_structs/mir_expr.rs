// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::safe_clients::prelude::*;

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum MirExpr<'tcx> {
    Rvalue(RvalueExpr<'tcx>),
    Switch {
        discr: Box<MirExpr<'tcx>>,
        guarded_exprs: Vec<(u128, MirExpr<'tcx>)>,
        default_expr: Box<MirExpr<'tcx>>,
        span: Option<Span>,
    },
    Call {
        func: mir::Constant<'tcx>,
        args: Vec<MirExpr<'tcx>>,
        return_ty: ty::Ty<'tcx>,
        span: Option<Span>,
    },
    Assert {
        cond: Box<MirExpr<'tcx>>,
        expected: bool,
        then: Box<MirExpr<'tcx>>,
        msg: mir::AssertMessage<'tcx>,
        span: Option<Span>,
    },
}

impl<'tcx> From<RvalueExpr<'tcx>> for MirExpr<'tcx> {
    fn from(rvalue: RvalueExpr<'tcx>) -> Self {
        MirExpr::Rvalue(rvalue)
    }
}

impl<'tcx> MirExpr<'tcx> {
    /// Returns the span of the expression, if any.
    pub fn span(&self) -> Option<Span> {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.span(),
            MirExpr::Switch { span, .. }
            | MirExpr::Call { span, .. }
            | MirExpr::Assert { span, .. } => *span,
        }
    }

    /// Returns the type of the expression.
    pub fn ty<D>(&self, local_decls: &D, tcx: ty::TyCtxt<'tcx>) -> PlaceTy<'tcx>
    where
        D: mir::HasLocalDecls<'tcx>,
    {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.ty(local_decls, tcx),
            MirExpr::Switch { default_expr, .. } => default_expr.ty(local_decls, tcx),
            &MirExpr::Call { return_ty, .. } => PlaceTy::from_ty(return_ty),
            MirExpr::Assert { then, .. } => then.ty(local_decls, tcx),
        }
    }

    /// Visits the direct `MirExpr` children of the expression.
    pub fn visit_subexpr<E>(
        &self,
        visitor: &dyn Fn(&MirExpr<'tcx>) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.visit_subexpr(visitor)?,
            MirExpr::Switch {
                box discr,
                guarded_exprs,
                default_expr,
                ..
            } => {
                visitor(discr)?;
                for (_, expr) in guarded_exprs {
                    visitor(expr)?;
                }
                visitor(default_expr)?;
            }
            MirExpr::Call { args, .. } => {
                for arg in args {
                    visitor(arg)?;
                }
            }
            MirExpr::Assert { cond, then, .. } => {
                visitor(cond)?;
                visitor(then)?;
            }
        }
        Ok(())
    }

    /// Visits the direct `MirExpr` children of the expression.
    pub fn visit_subexpr_mut<E>(
        &mut self,
        visitor: &dyn Fn(&mut MirExpr<'tcx>) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.visit_subexpr_mut(visitor)?,
            MirExpr::Switch {
                box discr,
                guarded_exprs,
                default_expr,
                ..
            } => {
                visitor(discr)?;
                for (_, expr) in guarded_exprs {
                    visitor(expr)?;
                }
                visitor(default_expr)?;
            }
            MirExpr::Call { args, .. } => {
                for arg in args {
                    visitor(arg)?;
                }
            }
            MirExpr::Assert { cond, then, .. } => {
                visitor(cond)?;
                visitor(then)?;
            }
        }
        Ok(())
    }

    /// Visits all `RvalueExpr` in the expression.
    pub fn visit_all_rvalues<E>(
        &self,
        visitor: &mut dyn FnMut(&RvalueExpr<'tcx>) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.visit_all_rvalues(visitor)?,
            MirExpr::Switch {
                discr,
                guarded_exprs,
                default_expr,
                ..
            } => {
                discr.visit_all_rvalues(visitor)?;
                for (_, expr) in guarded_exprs {
                    expr.visit_all_rvalues(visitor)?;
                }
                default_expr.visit_all_rvalues(visitor)?;
            }
            MirExpr::Call { args, .. } => {
                for arg in args {
                    arg.visit_all_rvalues(visitor)?;
                }
            }
            MirExpr::Assert { cond, then, .. } => {
                cond.visit_all_rvalues(visitor)?;
                then.visit_all_rvalues(visitor)?;
            }
        }
        Ok(())
    }

    /// Visits the direct `RvalueExpr` children of the expression.
    pub fn visit_subrvalue_mut<E>(
        &mut self,
        visitor: &dyn Fn(&mut RvalueExpr<'tcx>) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            MirExpr::Rvalue(rvalue) => visitor(rvalue)?,
            MirExpr::Switch {
                discr,
                guarded_exprs,
                default_expr,
                ..
            } => {
                discr.visit_subrvalue_mut(visitor)?;
                for (_, expr) in guarded_exprs {
                    expr.visit_subrvalue_mut(visitor)?;
                }
                default_expr.visit_subrvalue_mut(visitor)?;
            }
            MirExpr::Call { args, .. } => {
                for arg in args {
                    arg.visit_subrvalue_mut(visitor)?;
                }
            }
            MirExpr::Assert { cond, then, .. } => {
                cond.visit_subrvalue_mut(visitor)?;
                then.visit_subrvalue_mut(visitor)?;
            }
        }
        Ok(())
    }

    /// Normalize
    pub fn normalize(&mut self) {
        self.visit_subrvalue_mut::<()>(&|e| {
            e.normalize();
            Ok(())
        })
        .unwrap();
        // Note: we don't remove empty projections because they infor that an assignment happened.
        // TODO: Optimize away switch branches that are equal to the default branch
    }

    /// Replaces all places in the expression with a new `MirExpr`.
    pub fn replace_places<E>(
        &mut self,
        visitor: &dyn Fn(mir::Place<'tcx>) -> Result<Option<MirExpr<'tcx>>, E>,
    ) -> Result<(), E> {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.replace_places(visitor)?,
            MirExpr::Switch {
                discr,
                guarded_exprs,
                default_expr,
                ..
            } => {
                discr.replace_places(visitor)?;
                for (_, expr) in guarded_exprs {
                    expr.replace_places(visitor)?;
                }
                default_expr.replace_places(visitor)?;
            }
            MirExpr::Call { args, .. } => {
                for arg in args {
                    arg.replace_places(visitor)?;
                }
            }
            MirExpr::Assert { cond, then, .. } => {
                cond.replace_places(visitor)?;
                then.replace_places(visitor)?;
            }
        }
        Ok(())
    }

    /// Replaces all locals in the expression with a new expression.
    pub fn replace_locals<E>(
        &mut self,
        visitor: &dyn Fn(mir::Local) -> Result<Option<MirExpr<'tcx>>, E>,
    ) -> Result<(), E> {
        self.replace_places(&|place| {
            if let Some(new_expr) = visitor(place.local)? {
                Ok(Some(
                    RvalueExpr::Projections {
                        base: box new_expr,
                        projections: place.projection.iter().collect(),
                    }
                    .into(),
                ))
            } else {
                Ok(None)
            }
        })
    }

    /// If the expression is equivalent to a `mir::Place`, return it.
    pub fn as_place(&self, tcx: ty::TyCtxt<'tcx>) -> Option<mir::Place<'tcx>> {
        match self {
            MirExpr::Rvalue(rvalue) => rvalue.as_place(tcx),
            _ => None,
        }
    }

    pub fn strip_ref(&self) -> Option<&Self> {
        match self {
            MirExpr::Rvalue(rvalue) => match rvalue {
                RvalueExpr::Projections {
                    box base,
                    projections,
                } if projections.is_empty() => base.strip_ref(),
                &RvalueExpr::Ref { box ref expr, .. } => Some(expr),
                _ => None,
            },
            _ => None,
        }
    }
}

impl std::fmt::Display for MirExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirExpr::Rvalue(rvalue) => write!(f, "{rvalue}"),
            MirExpr::Switch {
                discr,
                guarded_exprs,
                default_expr,
                ..
            } => {
                write!(f, "switch {discr} {{")?;
                for (guard, expr) in guarded_exprs {
                    write!(f, " {guard} => {expr},")?;
                }
                write!(f, " _ => {default_expr} }}")
            }
            MirExpr::Call { func, args, .. } => {
                write!(f, "{func}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            MirExpr::Assert { cond, then, .. } => {
                write!(f, "assert({cond}, {then})")
            }
        }
    }
}
