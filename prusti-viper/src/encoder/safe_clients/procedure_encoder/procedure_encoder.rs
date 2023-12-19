// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir::contracts::BorrowInfo;
use crate::encoder::safe_clients::prelude::*;
use crate::encoder::builtin_encoder::{BuiltinMethodKind, BuiltinDomainKind};
use crate::encoder::errors::{
    SpannedEncodingError, ErrorCtxt, WithSpan,
    EncodingResult, SpannedEncodingResult
};
use crate::encoder::errors::error_manager::PanicCause;
use crate::encoder::loop_encoder::{LoopEncoder, LoopEncoderError};
use crate::encoder::mir_encoder::MirEncoder;
use crate::encoder::mir_successor::MirSuccessor;
use crate::encoder::Encoder;
use crate::encoder::mir::procedures::encoder::specification_blocks::SpecificationBlocks;
use analysis::PointwiseState;
use analysis::domains::{DefinitelyAllocatedState, LocallySharedState};
use analysis::domains::DefinitelyUnreachableState;
use analysis::domains::{DefinitelyAccessibleState, FramingState};
use itertools::Itertools;
use prelude::procedure_encoder::fixed_version_encoder::FixedVersionEncoder;
use prusti_common::{
    config,
    vir::{ToGraphViz, fixes::fix_ghost_vars},
};
use vir_crate::{
    polymorphic::{
        self as vir,
        collect_assigned_vars,
        CfgBlockIndex, Successor},
};
use prusti_interface::{
    environment::{
        borrowck::facts,
        polonius_info::{
            PoloniusInfo, PoloniusInfoError
        },
        BasicBlockIndex, Procedure,
    },
};
use std::collections::BTreeMap;
use std::rc::Rc;
use prusti_rustc_interface::middle::mir;
use prusti_rustc_interface::middle::ty::{self, subst::SubstsRef};
use rustc_hash::FxHashSet;
use prusti_rustc_interface::span::Span;
use prusti_rustc_interface::errors::MultiSpan;
use prusti_interface::environment::borrowck::regions::PlaceRegionsError;
use crate::encoder::errors::EncodingErrorKind;
use prusti_interface::specs::typed::{SpecificationItem, LoopSpecification, Pledge};
use crate::encoder::mir::{
    contracts::{
        ContractsEncoderInterface,
        ProcedureContractMirDef,
    },
    specifications::SpecificationsInterface,
};
use super::local_address_encoder::LocalAddressEncoder;
use super::Version;

pub struct VersionBasedProcedureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    pub(crate) encoder: &'p Encoder<'v, 'tcx>,
    pub(crate) def_id: DefId,
    pub(crate) mir: &'p mir::Body<'tcx>,
    pub(crate) procedure: &'p Procedure<'tcx>,
    pub(crate) mir_encoder: MirEncoder<'p, 'v, 'tcx>,
    pub(super) specification_blocks: SpecificationBlocks,
    pub(super) specification_block_encoding: BTreeMap<mir::BasicBlock, Vec<vir::Stmt>>,
    pub(super) cfg_method: vir::CfgMethod,
    pub(super) loop_encoder: LoopEncoder<'p, 'tcx>,
    ownership_facts: Option<Rc<PointwiseState<'p, 'tcx, DefinitelyAccessibleState<'tcx>>>>,
    locally_shared_facts: Option<PointwiseState<'p, 'tcx, LocallySharedState<'p, 'tcx>>>,
    framing_facts: Option<PointwiseState<'p, 'tcx, FramingState<'tcx>>>,
    unreachable_facts: Option<PointwiseState<'p, 'tcx, DefinitelyUnreachableState<'p, 'tcx>>>,
    allocation_facts: Option<PointwiseState<'p, 'tcx, DefinitelyAllocatedState<'p, 'tcx>>>,
    polonius_info: Option<PoloniusInfo<'p, 'tcx>>,
    contract: Option<ProcedureContractMirDef<'tcx>>,
    /// Store the CFG blocks that encode a MIR block each.
    pub(super) cfg_blocks_map: FxHashMap<mir::BasicBlock, FxHashSet<CfgBlockIndex>>,
    /// Mapping from old expressions to ghost variables with which they were replaced.
    pub(super) old_to_ghost_var: FxHashMap<vir::Expr, vir::Expr>,
    /// Ghost variables used inside package statements.
    pub(super) old_ghost_vars: FxHashMap<String, vir::Type>,
    /// For each loop head, the block at whose end the loop invariant holds
    pub(super) cached_loop_invariant_block: rustc_hash::FxHashMap<BasicBlockIndex, BasicBlockIndex>,
    /// Type substitutions inside this procedure. Most likely identity for the
    /// given proc_def_id.
    pub(super) substs: SubstsRef<'tcx>,
    /// Encoder of the pre memory version, used to evaluate the precondition.
    pre_version_encoder: Rc<FixedVersionEncoder<'p, 'v, 'tcx>>,
    /// Encoder of the old memory version, used to evaluate in the state before a statement.
    old_version_encoder: Rc<FixedVersionEncoder<'p, 'v, 'tcx>>,
    /// Encoder of the old memory version, using the pre memory version for old(..) expressions.
    /// This is the encoded for the prusti_assert!(..) and prusti_ensure!(..) special statements.
    old_pre_version_encoder: FixedVersionEncoder<'p, 'v, 'tcx>,
    /// Encoder of the curr memory version, using the pre memory version for old(..) expressions.
    /// This is the encoded for the contracts of the *current procedure* that is being encoded.
    curr_pre_version_encoder: FixedVersionEncoder<'p, 'v, 'tcx>,
    /// Encoder of the curr memory version, using the old memory version for old(..) expressions.
    /// This is the encoded for the contracts of the *calls* that are being encoded.
    curr_old_version_encoder: FixedVersionEncoder<'p, 'v, 'tcx>,
    /// Store the version of the pre-state of a call annotated with a pledge.
    pub(super) call_pre_version: FxHashMap<mir::Location, vir::LocalVar>,
    /// Store the target address of reference-typed arguments of a call annotated with a pledge.
    /// The key is (call_location, argument_index) and the value is (target_address, target_type).
    pub(super) call_blocked_address: FxHashMap<(mir::Location, usize), (vir::LocalVar, ty::Ty<'tcx>)>,
}

impl<'p, 'v: 'p, 'tcx: 'v> WithEncoder<'v, 'tcx> for VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    fn encoder(&self) -> &Encoder<'v, 'tcx> {
        self.encoder
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithDefId<'v, 'tcx> for VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn substs(&self) -> ty::SubstsRef<'tcx> {
        self.substs
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> DefIdEncoder<'v, 'tcx> for VersionBasedProcedureEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> WithLocalTy<'v, 'tcx> for VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.mir.local_decls[local].ty
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> WithMir<'v, 'tcx> for VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    fn mir(&self) -> &mir::Body<'tcx> {
        self.mir
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> LocalAddressEncoder<'v, 'tcx> for VersionBasedProcedureEncoder<'p, 'v, 'tcx> {}

impl<'p, 'v: 'p, 'tcx: 'v> VersionBasedProcedureEncoder<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        procedure: &'p Procedure<'tcx>
    ) -> SpannedEncodingResult<Self> {
        debug!("VersionBasedProcedureEncoder constructor");

        let mir = procedure.get_mir();
        let def_id = procedure.get_id();
        let substs = encoder.env().query.identity_substs(def_id);
        let tcx = encoder.env().tcx();
        let mir_encoder = MirEncoder::new(encoder, mir, def_id);

        let specification_blocks = SpecificationBlocks::build(encoder.env().query, mir, procedure, false);

        let mut cfg_method = vir::CfgMethod::new(
            // method name
            encoder.encode_item_name(def_id),
            // formal returns
            vec![],
            // local vars
            vec![],
            // reserved labels
            vec![],
        );

        let version_type = encoder.encode_builtin_domain_type(BuiltinDomainKind::Version)
            .with_span(mir.span)?;
        let curr_version = vir::LocalVar::new("version", version_type.clone());
        let old_version = vir::LocalVar::new("old_version", version_type.clone());
        let pre_version = vir::LocalVar::new("pre_version", version_type);
        cfg_method.add_local_var(&curr_version.name, curr_version.typ.clone());
        cfg_method.add_local_var(&old_version.name, old_version.typ.clone());
        cfg_method.add_local_var(&pre_version.name, pre_version.typ.clone());
        let pre_version_encoder = Rc::new(FixedVersionEncoder::new(
            encoder, def_id, mir, substs, pre_version, None,
        )?);
        let old_version_encoder = Rc::new(FixedVersionEncoder::new(
            encoder, def_id, mir, substs, old_version.clone(), None,
        )?);
        let old_pre_version_encoder = FixedVersionEncoder::new(
            encoder, def_id, mir, substs, old_version.clone(), Some(pre_version_encoder.clone()),
        )?;
        let curr_pre_version_encoder = FixedVersionEncoder::new(
            encoder, def_id, mir, substs, curr_version.clone(), Some(pre_version_encoder.clone()),
        )?;
        let curr_old_version_encoder = FixedVersionEncoder::new(
            encoder, def_id, mir, substs, curr_version, Some(old_version_encoder.clone()),
        )?;

        Ok(VersionBasedProcedureEncoder {
            encoder,
            def_id,
            procedure,
            mir,
            cfg_method,
            specification_blocks,
            specification_block_encoding: Default::default(),
            loop_encoder: LoopEncoder::new(procedure, tcx),
            mir_encoder,
            ownership_facts: None,
            locally_shared_facts: None,
            framing_facts: None,
            unreachable_facts: None,
            allocation_facts: None,
            polonius_info: None,
            contract: None,
            cfg_blocks_map: FxHashMap::default(),
            old_to_ghost_var: FxHashMap::default(),
            old_ghost_vars: FxHashMap::default(),
            cached_loop_invariant_block: rustc_hash::FxHashMap::default(),
            substs,
            pre_version_encoder,
            old_version_encoder,
            old_pre_version_encoder,
            curr_pre_version_encoder,
            curr_old_version_encoder,
            call_pre_version: FxHashMap::default(),
            call_blocked_address: FxHashMap::default(),
        })
    }

    pub(crate) fn polonius_info(&self) -> &PoloniusInfo<'p, 'tcx> {
        self.polonius_info.as_ref().unwrap()
    }

    pub(crate) fn ownership_facts(&self) -> &PointwiseState<'p, 'tcx, DefinitelyAccessibleState<'tcx>> {
        self.ownership_facts.as_ref().unwrap()
    }

    pub(crate) fn locally_shared_facts(&self) -> &PointwiseState<'p, 'tcx, LocallySharedState<'p, 'tcx>> {
        self.locally_shared_facts.as_ref().unwrap()
    }

    pub(crate) fn framing_facts(&self) -> &PointwiseState<'p, 'tcx, FramingState<'tcx>> {
        self.framing_facts.as_ref().unwrap()
    }

    pub(crate) fn unreachable_facts(&self) -> &PointwiseState<'p, 'tcx, DefinitelyUnreachableState<'p, 'tcx>> {
        self.unreachable_facts.as_ref().unwrap()
    }

    pub(crate) fn allocation_facts(&self) -> &PointwiseState<'p, 'tcx, DefinitelyAllocatedState<'p, 'tcx>> {
        self.allocation_facts.as_ref().unwrap()
    }

    pub(crate) fn contract(&self) -> &ProcedureContractMirDef<'tcx> {
        self.contract.as_ref().unwrap()
    }

    pub fn encode(mut self) -> SpannedEncodingResult<vir::CfgMethod> {
        debug!("Encode procedure {}", self.cfg_method.name());
        let mir_span = self.mir.span;

        self.check_body()?;

        // Retrieve the contract
        let contract = self.encoder
            .get_mir_procedure_contract_for_def(self.def_id, self.substs)
            .with_span(mir_span)?;
        self.contract = Some(contract);

        // Declare the address of local variables (including the arguments and the result)
        for local in self.mir.local_decls.indices() {
            let var = self.encode_local_address_var(local)?;
            self.cfg_method.add_local_var(&var.name, var.typ)
        }

        // Preprocess loops
        for bbi in self.procedure.get_reachable_nonspec_cfg_blocks() {
            if self.loop_encoder.loops().is_loop_head(bbi) {
                match self.loop_encoder.get_loop_invariant_block(bbi) {
                    Err(LoopEncoderError::LoopInvariantInBranch(loop_head)) => {
                        return Err(SpannedEncodingError::incorrect(
                            "the loop invariant cannot be in a conditional branch of the loop",
                            self.get_loop_span(loop_head),
                        ));
                    }
                    Ok(loop_inv_bbi) => {
                        self.cached_loop_invariant_block.insert(bbi, loop_inv_bbi);
                    }
                }
            }
        }

        // Run ownership and framing analysis.
        // Do this before `PoloniusInfo::new`, or it'll steal the borrow-checker facts!
        let (
            ownership_facts,
            locally_shared_facts,
            framing_facts,
            unreachable_facts,
            allocation_facts
        ) = self.compute_facts()?;
        self.ownership_facts = Some(ownership_facts);
        self.locally_shared_facts = Some(locally_shared_facts);
        self.framing_facts = Some(framing_facts);
        self.unreachable_facts = Some(unreachable_facts);
        self.allocation_facts = Some(allocation_facts);

        // Load Polonius info
        self.polonius_info = Some(
            PoloniusInfo::new(self.encoder.env(), self.procedure, &self.cached_loop_invariant_block)
                .map_err(|err| self.translate_polonius_error(err))?,
        );

        // Initialize CFG blocks
        let start_cfg_block = self.cfg_method.add_block(
            "start",
            vec![
                vir::Stmt::comment("========== start =========="),
                // vir::Stmt::comment(format!("Name: {:?}", self.procedure.get_name())),
                vir::Stmt::comment(format!("Def path: {:?}", self.procedure.get_def_path())),
            ],
        );

        let return_cfg_block = self.cfg_method.add_block(
            "return",
            vec![
                vir::Stmt::comment("========== return =========="),
                vir::Stmt::comment("Target of any 'return' statement."),
            ],
        );
        self.cfg_method
            .set_successor(return_cfg_block, Successor::Return);

        self.encode_specification_blocks()?;

        // Encode all blocks
        let nonspec_cfg_blocks = self.procedure.get_reachable_nonspec_cfg_blocks();
        let (opt_body_head, unresolved_edges) = self.encode_blocks_group(
            "",
            &nonspec_cfg_blocks,
            0,
            return_cfg_block,
        )?;
        if !unresolved_edges.is_empty() {
            return Err(SpannedEncodingError::internal(
                format!(
                    "there are unresolved CFG edges in the encoding: {unresolved_edges:?}"
                ),
                mir_span,
            ));
        }

        // Set the first CFG block
        self.cfg_method.set_successor(
            start_cfg_block,
            Successor::Goto(opt_body_head.unwrap_or(return_cfg_block)),
        );

        // Assume axioms that use top-level functions
        let axiom_stmts = self.encode_axioms().with_default_span(mir_span)?;
        self.cfg_method.add_stmts(start_cfg_block, axiom_stmts);

        // Prepare assertions to check specification refinement
        let (precondition_weakening, postcondition_strengthening)
            = self.encode_spec_refinement()?;

        // Encode preconditions
        self.encode_preconditions(start_cfg_block, precondition_weakening)?;

        // Encode postcondition
        self.encode_postconditions(return_cfg_block, postcondition_strengthening)?;

        let method_name = self.cfg_method.name();
        let source_filename = self.encoder.env().name.source_file_name();

        // Dump initial CFG
        if config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_before_fixes",
                format!("{source_filename}.{method_name}.dot"),
                |writer| self.cfg_method.to_graphviz(writer),
            );
        }

        // Fix variable declarations.
        self.cfg_method = fix_ghost_vars(self.cfg_method);

        // Dump final CFG
        if config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_before_viper",
                format!("{source_filename}.{method_name}.dot"),
                |writer| self.cfg_method.to_graphviz(writer),
            );
        }

        self.check_vir()?;
        Ok(self.cfg_method)
    }

    fn encode_specification_blocks(&mut self) -> SpannedEncodingResult<()> {
        // Collect the entry points into the specification blocks.
        let mut entry_points: BTreeMap<_, _> = self
            .specification_blocks
            .entry_points()
            .map(|bb| (bb, Vec::new()))
            .collect();

        // Encode the specification blocks.
        for (bb, statements) in &mut entry_points {
            self.encode_specification_block(*bb, statements)?;
        }
        assert!(self.specification_block_encoding.is_empty());
        self.specification_block_encoding = entry_points;
        Ok(())
    }

    #[allow(clippy::nonminimal_bool)]
    fn encode_specification_block(
        &self,
        bb: mir::BasicBlock,
        encoded_statements: &mut Vec<vir::Stmt>,
    ) -> SpannedEncodingResult<()> {
        let _ = self.try_encode_prusti_assert(bb, encoded_statements)?
        || self.try_encode_prusti_assume(bb, encoded_statements)?;
        Ok(())
    }

    fn try_encode_prusti_assume(
        &self,
        bb: mir::BasicBlock,
        encoded_statements: &mut Vec<vir::Stmt>,
    ) -> SpannedEncodingResult<bool> {
        for stmt in &self.mir[bb].statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(
                    box mir::AggregateKind::Closure(cl_def_id, _),
                    _
                ),
            )) = stmt.kind {
                let Some(assertion) = self.encoder.get_prusti_assertion(cl_def_id.to_def_id()) else {
                    return Ok(false);
                };
                let assume_expr = self.encode_bool_assertion(bb, Version::OldPre)?;
                encoded_statements.push(vir::Stmt::inhale(assume_expr));
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn try_encode_prusti_assert(
        &self,
        bb: mir::BasicBlock,
        encoded_statements: &mut Vec<vir::Stmt>,
    ) -> SpannedEncodingResult<bool> {
        for stmt in &self.mir[bb].statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(
                    box mir::AggregateKind::Closure(cl_def_id, _),
                    _
                ),
            )) = stmt.kind {
                let Some(assertion) = self.encoder.get_prusti_assertion(cl_def_id.to_def_id()) else {
                    return Ok(false);
                };
                let assert_expr = self.encode_bool_assertion(bb, Version::OldPre)?;
                let pos = assert_expr.pos();
                self.encoder.error_manager().set_error(pos, ErrorCtxt::Panic(PanicCause::Assert));
                let assert_stmt = vir::Stmt::Assert(vir::Assert {
                    expr: assert_expr,
                    position: pos,
                });
                encoded_statements.push(assert_stmt);
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn encode_loop_invariant_expr(
        &self, bb: mir::BasicBlock,
    ) -> SpannedEncodingResult<vir::Expr> {
        for stmt in &self.mir[bb].statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, cl_substs), _),
            )) = stmt.kind
            {
                let loop_spec = self.encoder.get_loop_specs(cl_def_id.to_def_id());
                let Some(LoopSpecification::Variant(invariant_def_id)) = loop_spec else {
                    continue;
                };
                return self.encode_bool_assertion(bb, Version::CurrPre);
            }
        }
        error_internal!(self.get_span_of_basic_block(bb) =>
            "no loop invariant encoding found in {bb:?} of {:?}",
            self.def_id(),
        );
    }

    fn translate_polonius_error(&self, error: PoloniusInfoError) -> SpannedEncodingError {
        match error {
            PoloniusInfoError::UnsupportedLoanInLoop {
                loop_head,
                variable,
            } => {
                let msg = if self.mir.local_decls[variable].is_user_variable() {
                    "creation of loan 'FIXME: extract variable name' in loop is unsupported".to_string()
                } else {
                    "creation of temporary loan in loop is unsupported".to_string()
                };
                SpannedEncodingError::unsupported(msg, self.get_span_of_basic_block(loop_head))
            }

            PoloniusInfoError::LoansInNestedLoops(location1, _loop1, _location2, _loop2) => {
                SpannedEncodingError::unsupported(
                    "creation of loans in nested loops is not supported".to_string(),
                    self.mir.source_info(location1).span,
                )
            }

            PoloniusInfoError::ReborrowingDagHasNoMagicWands(location) => {
                SpannedEncodingError::unsupported(
                    "the creation of loans in this loop is not supported \
                    (ReborrowingDagHasNoMagicWands)",
                    self.mir.source_info(location).span,
                )
            }

            PoloniusInfoError::MultipleMagicWandsPerLoop(location) => SpannedEncodingError::unsupported(
                "the creation of loans in this loop is not supported \
                    (MultipleMagicWandsPerLoop)",
                self.mir.source_info(location).span,
            ),

            PoloniusInfoError::MagicWandHasNoRepresentativeLoan(location) => {
                SpannedEncodingError::unsupported(
                    "the creation of loans in this loop is not supported \
                    (MagicWandHasNoRepresentativeLoan)",
                    self.mir.source_info(location).span,
                )
            }

            PoloniusInfoError::PlaceRegionsError(
                PlaceRegionsError::Unsupported(msg),
                span,
            ) => {
                SpannedEncodingError::unsupported(msg, span)
            }

            PoloniusInfoError::LoanInUnsupportedStatement(msg, location) => {
                SpannedEncodingError::unsupported(msg, self.mir.source_info(location).span)
            }
        }
    }

    /// Encodes a topologically ordered group of blocks.
    ///
    /// Returns:
    /// * The first CFG block of the encoding. None if there were no blocks to encode.
    /// * A vector of unresolved edges.
    #[allow(clippy::type_complexity)]
    fn encode_blocks_group(
        &mut self,
        label_prefix: &str,
        ordered_group_blocks: &[BasicBlockIndex],
        group_loop_depth: usize,
        return_block: CfgBlockIndex,
    ) -> SpannedEncodingResult<(Option<CfgBlockIndex>, Vec<(CfgBlockIndex, BasicBlockIndex)>)> {
        // Encode the CFG blocks
        let mut bb_map: FxHashMap<_, _> = FxHashMap::default();
        let mut unresolved_edges: Vec<_> = vec![];
        for &curr_bb in ordered_group_blocks.iter() {
            let loop_info = self.loop_encoder.loops();
            let curr_loop_depth = loop_info.get_loop_depth(curr_bb);
            let is_loop_head = loop_info.is_loop_head(curr_bb);
            let (curr_block, curr_edges) = if curr_loop_depth == group_loop_depth {
                // This block is not in a nested loop
                self.encode_block(label_prefix, curr_bb, return_block)?
            } else {
                debug_assert!(curr_loop_depth > group_loop_depth);
                if curr_loop_depth == group_loop_depth + 1 && is_loop_head {
                    // Encode a nested loop
                    self.encode_loop(label_prefix, curr_bb, return_block)?
                } else {
                    debug_assert!(curr_loop_depth > group_loop_depth + 1 || !is_loop_head);
                    // Skip the inner block of a nested loop
                    continue;
                }
            };
            bb_map.insert(curr_bb, curr_block);
            unresolved_edges.extend(curr_edges);
        }

        // Return unresolved CFG edges
        let group_head = ordered_group_blocks.get(0).map(|bb| {
            debug_assert!(
                bb_map.contains_key(bb),
                "Block {bb:?} (depth: {}, loop head: {}) has not been encoded \
                (group_loop_depth: {group_loop_depth}, \
                ordered_group_blocks: {ordered_group_blocks:?})",
                self.loop_encoder.loops().get_loop_depth(*bb),
                self.loop_encoder.loops().is_loop_head(*bb),
            );
            bb_map[bb]
        });
        // We pass `leave_unresolved=group_head` because we want to leave back edges to the current
        // loop head unresolved, so that the encoding of loops can map them to something else.
        let still_unresolved_edges = self.encode_unresolved_edges(
            unresolved_edges,
            |bb| bb_map.get(&bb).cloned(),
            group_head,
        )?;
        Ok((group_head, still_unresolved_edges))
    }

    fn encode_unresolved_edges<F: Fn(BasicBlockIndex) -> Option<CfgBlockIndex>>(
        &mut self,
        mut unresolved_edges: Vec<(CfgBlockIndex, BasicBlockIndex)>,
        resolver: F,
        leave_unresolved: Option<CfgBlockIndex>,
    ) -> SpannedEncodingResult<Vec<(CfgBlockIndex, BasicBlockIndex)>> {
        let mut still_unresolved_edges: Vec<_> = vec![];
        for (curr_block, target) in unresolved_edges.drain(..) {
            if let Some(target_block) = resolver(target) && Some(target_block) != leave_unresolved {
                self.cfg_method
                    .set_successor(curr_block, Successor::Goto(target_block));
            } else {
                still_unresolved_edges.push((curr_block, target));
            }
        }
        Ok(still_unresolved_edges)
    }

    /// Encodes a loop.
    ///
    /// Returns:
    /// * The first CFG block of the encoding
    /// * A vector of unresolved CFG edges
    ///
    /// The encoding transforms
    /// ```text
    /// loop_invariant!(I); loop { BODY }
    /// ```
    /// into
    /// ```text
    /// exhale I;             |
    /// havoc loop variables; |-> "start"
    /// inhale I;             |
    /// BODY;
    /// exhale I;  |
    /// kill path; |-> "end"
    /// ```
    /// where `BODY` contains edges to other CFG blocks.
    fn encode_loop(
        &mut self,
        label_prefix: &str,
        loop_head: BasicBlockIndex,
        return_block: CfgBlockIndex,
    ) -> SpannedEncodingResult<(CfgBlockIndex, Vec<(CfgBlockIndex, BasicBlockIndex)>)> {
        trace!("encode_loop: {:?}", loop_head);

        let loop_info = self.loop_encoder.loops();
        debug_assert!(loop_info.is_loop_head(loop_head));
        debug_assert!(loop_info.is_loop_head(loop_head));
        let loop_label_prefix = format!("{label_prefix}loop{}", loop_head.index());
        let loop_depth = loop_info.get_loop_head_depth(loop_head);

        let loop_body: Vec<BasicBlockIndex> = loop_info
            .get_loop_body(loop_head)
            .iter()
            .copied()
            .filter(
                |&bb| self.procedure.is_reachable_block(bb) && !self.procedure.is_spec_block(bb)
            )
            .collect();

        debug!("loop_head: {:?}", loop_head);
        debug!("loop_body: {:?}", loop_body);

        // Declare the "start" CFG block (*start* - body - end)
        let start_block = self.cfg_method.add_block(
            &format!("{loop_label_prefix}_start"),
            vec![vir::Stmt::comment(format!(
                "========== {loop_label_prefix}_loop_body_start ==========",
            ))],
        );

        // Encode the body (start - *body* - end)
        let (opt_body_head, unresolved_body_edges) = self.encode_blocks_group(
            &format!("{loop_label_prefix}_body_"),
            &loop_body,
            loop_depth,
            return_block,
        )?;

        // Declare the "end" CFG block (start - body - *end*)
        let end_block = self.cfg_method.add_block(
            &format!("{loop_label_prefix}_end"),
            vec![vir::Stmt::comment(format!(
                "========== {loop_label_prefix}_loop_body_end ==========",
            ))],
        );

        // Link edges of (*start* - body - end)
        if let Some(body_head) = opt_body_head {
            self.cfg_method.set_successor(start_block, vir::Successor::Goto(body_head));
        } else {
            debug_assert!(loop_body.is_empty());
            self.cfg_method.set_successor(start_block, vir::Successor::Goto(end_block));
        }

        // Link edges of (start - *body* - end)
        let mut unresolved_loop_edges = vec![];
        for &(body_block, target_block) in &unresolved_body_edges {
            if target_block == loop_head {
                self.cfg_method
                    .set_successor(body_block, Successor::Goto(end_block));
            } else {
                unresolved_loop_edges.push((body_block, target_block));
            }
        }

        // Link edges of (start - body - *end*)
        self.cfg_method.set_successor(end_block, vir::Successor::Return);

        // Assert the invariant at the beginning of the loop
        self.cfg_method.add_stmt(start_block, vir::Stmt::comment("Assert loop invariant on entry"));
        let start_assert_inv = self.encode_loop_invariant_stmts(loop_head, InvariantUsage::AssertOnEntry)?;
        self.cfg_method.add_stmts(start_block, start_assert_inv);

        // Havoc Viper local variables assigned in the encoding of the loop body
        self.cfg_method.add_stmt(start_block, vir::Stmt::comment("Havoc loop variables"));
        let assigned_vars = collect_assigned_vars(&self.cfg_method, end_block, start_block);
        for assigned_var in assigned_vars {
            let builtin_method = BuiltinMethodKind::Havoc(assigned_var.typ.clone());
            let method_name = self.encoder.encode_builtin_method_use(&builtin_method)
                .with_span(self.mir.span)?;
            let havoc_stmt = vir::Stmt::MethodCall( vir::MethodCall {
                method_name,
                arguments: vec![],
                targets: vec![assigned_var],
            });
            self.cfg_method.add_stmt(start_block, havoc_stmt);
        }

        // Assume the invariant at the beginning of the loop
        self.cfg_method.add_stmt(start_block, vir::Stmt::comment("Assume loop invariant before iteration"));
        let start_assert_inv = self.encode_loop_invariant_stmts(loop_head, InvariantUsage::AssumeBeforeIteration)?;
        self.cfg_method.add_stmts(start_block, start_assert_inv);

        // Assert the invariant at the end of the loop
        self.cfg_method.add_stmt(start_block, vir::Stmt::comment("Assert loop invariant after iteration"));
        let end_assert_inv = self.encode_loop_invariant_stmts(loop_head, InvariantUsage::AssertAfterIteration)?;
        self.cfg_method.add_stmts(end_block, end_assert_inv);

        // Done. Phew!
        Ok((start_block, unresolved_loop_edges))
    }

    /// Encodes the assert or assume statements of a loop invariant.
    fn encode_loop_invariant_stmts(
        &self,
        loop_head: BasicBlockIndex,
        invariant_usage: InvariantUsage,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!(
            "[enter] encode_loop_invariant_stmts loop_head={:?} \
            invariant_usage={:?}",
            loop_head,
            invariant_usage
        );
        let mut func_specs = vec![];
        for &invariant_bb in &self.get_loop_spec_blocks(loop_head) {
            func_specs.push(self.encode_loop_invariant_expr(invariant_bb)?);
        }

        match invariant_usage {
            InvariantUsage::AssumeBeforeIteration => {
                let mut stmts = vec![
                    vir::Stmt::comment(format!(
                        "Assume the loop invariants (num: {}, loop head: {loop_head:?})",
                        func_specs.len(),
                    )),
                ];
                for func_spec in func_specs {
                    stmts.push(vir::Stmt::inhale(func_spec));
                }
                Ok(stmts)
            }
            InvariantUsage::AssertOnEntry
            | InvariantUsage::AssertAfterIteration => {
                let error_ctx = match invariant_usage {
                    InvariantUsage::AssumeBeforeIteration => ErrorCtxt::AssertLoopInvariantOnEntry,
                    InvariantUsage::AssertAfterIteration => ErrorCtxt::AssertLoopInvariantAfterIteration,
                    InvariantUsage::AssertOnEntry => ErrorCtxt::AssertLoopInvariantOnEntry,
                };
                let mut stmts = vec![
                    vir::Stmt::comment(format!(
                        "Assert the loop invariants (num: {}, loop head: {loop_head:?})",
                        func_specs.len(),
                    )),
                ];
                for func_spec in func_specs {
                    debug_assert!(!func_spec.pos().is_default());
                    stmts.push(vir::Stmt::Assert(vir::Assert {
                        position: func_spec.pos(),
                        expr: func_spec,
                    }));
                }
                Ok(stmts)
            }
        }
    }

    /// Encode a block.
    ///
    /// Returns:
    /// * The head of the encoded block
    /// * A vector of unresolved edges
    fn encode_block(
        &mut self,
        label_prefix: &str,
        bbi: BasicBlockIndex,
        return_block: CfgBlockIndex,
    ) -> SpannedEncodingResult<(CfgBlockIndex, Vec<(CfgBlockIndex, BasicBlockIndex)>)> {
        debug_assert!(!self.procedure.is_spec_block(bbi));

        let curr_block = self.cfg_method.add_block(
            &format!("{label_prefix}{bbi:?}"),
            vec![vir::Stmt::comment(format!("========== {label_prefix}{bbi:?} =========="))],
        );
        self.cfg_blocks_map
            .entry(bbi)
            .or_insert_with(FxHashSet::default)
            .insert(curr_block);

        if self.loop_encoder.is_loop_head(bbi) {
            self.cfg_method.add_stmt(
                curr_block,
                vir::Stmt::comment("This is a loop head"),
            );
        }

        let opt_successor = self.encode_block_statements(bbi, curr_block)?;
        let mir_successor: MirSuccessor = if let Some(successor) = opt_successor {
            // In case of unsupported statements, we do not encode the terminator
            successor
        } else {
            self.encode_block_terminator(bbi, curr_block)?
        };

        // Encode MIR edges
        // Each (target, edge_block) in this map means that the successor of edge_block, which
        // should be the encoding of target, has not been encoded yet.
        let mut unresolved_targets = FxHashMap::default();
        let mir_targets = mir_successor.targets();
        let force_block_on_edge = mir_targets.len() > 1 || mir_targets.iter().any(
            |&target| self.loop_encoder.is_loop_head(target)
        );
        let mut complete_resolution = true;
        for &target in &mir_targets {
            let opt_edge_block = self.encode_edge_block(bbi, target, force_block_on_edge)?;
            if let Some(edge_block) = opt_edge_block {
                unresolved_targets.insert(target, edge_block);
            } else {
                complete_resolution = false;
            }
        }
        let unresolved_edges = if complete_resolution {
            // Resolve successor and return the edge blocks
            let curr_successor =
                mir_successor.encode(return_block, |target_bb| unresolved_targets[&target_bb]);
            self.cfg_method.set_successor(curr_block, curr_successor);
            // This can be empty, if there are no unresolved edges left
            unresolved_targets
                .iter()
                .map(|(&target, &edge_block)| (edge_block, target))
                .collect()
        } else {
            match mir_successor {
                MirSuccessor::Goto(target) => vec![(curr_block, target)],
                MirSuccessor::GotoSwitch(guarded_targets, default_target) => {
                    // This should hold because of the `force_block_on_edge` condition.
                    debug_assert!(guarded_targets.is_empty());
                    vec![(curr_block, default_target)]
                }
                x => unreachable!("{:?}", x),
            }
        };

        Ok((curr_block, unresolved_edges))
    }

    /// Encode the statements of the block.
    /// In case of unsupported statements, this function will return `MirSuccessor::Kill`.
    fn encode_block_statements(
        &mut self,
        bbi: BasicBlockIndex,
        cfg_block: CfgBlockIndex,
    ) -> SpannedEncodingResult<Option<MirSuccessor>> {
        debug_assert!(!self.procedure.is_spec_block(bbi));
        let bb_data = &self.mir.basic_blocks[bbi];
        let statements: &Vec<mir::Statement<'tcx>> = &bb_data.statements;
        for stmt_index in 0..statements.len() {
            trace!("Encode statement {:?}:{}", bbi, stmt_index);
            let location = mir::Location {
                block: bbi,
                statement_index: stmt_index,
            };

            let (stmts, opt_succ) = self.encode_statement_at(location)?;
            debug_assert!(matches!(opt_succ, None | Some(MirSuccessor::Kill)));
            self.cfg_method.add_stmts(cfg_block, stmts);
            if opt_succ.is_some() {
                // If the statement is unsupported, we stop encoding the block.
                return Ok(opt_succ);
            }

            // Needed to verify some assert_on_expiry assertions
            let expiring_borrows_stmts = self.encode_expiring_borrows_at(location)?;
            if !expiring_borrows_stmts.is_empty() {
                let allocation_facts = self.encode_allocation_at_location(location)?;
                self.cfg_method.add_stmts(cfg_block, allocation_facts);
            }
            self.cfg_method.add_stmts(cfg_block, expiring_borrows_stmts);
        }

        Ok(None)
    }

    /// Encode the terminator of the block
    fn encode_block_terminator(
        &mut self,
        bbi: BasicBlockIndex,
        curr_block: CfgBlockIndex,
    ) -> SpannedEncodingResult<MirSuccessor> {
        trace!("Encode terminator of {:?}", bbi);
        let bb_data = &self.mir.basic_blocks[bbi];
        let location = mir::Location {
            block: bbi,
            statement_index: bb_data.statements.len(),
        };
        let (stmts, opt_mir_successor) = self.encode_statement_at(location)?;
        self.cfg_method.add_stmts(curr_block, stmts);

        Ok(opt_mir_successor.unwrap())
    }

    /// Encode a MIR statement or terminator, encoding an `assert false` in case
    /// of usage of unsupported features.
    fn encode_statement_at(
        &mut self,
        location: mir::Location,
    ) -> SpannedEncodingResult<(Vec<vir::Stmt>, Option<MirSuccessor>)> {
        trace!("Encode location {:?}", location);
        let span = self.get_span_of_location(location);
        let intro_stmts: Vec<vir::Stmt>;

        // Encode ownership before the statement
        let ownership_stmts = self.encode_ownership_before_location(location)?;

        // Encode version bump before the encoding of the statement
        let bump_stmts = self.encode_version_bump().with_span(span)?;

        let bb_data = &self.mir[location.block];
        let index = location.statement_index;
        let stmts_succ_res = if index < bb_data.statements.len() {
            let mir_stmt = &bb_data.statements[index];
            intro_stmts = vec![
                vir::Stmt::comment(""),
                vir::Stmt::comment(format!("[mir] {mir_stmt:?}")),
            ];
            self.encode_statement(mir_stmt, location)
                .map(|stmts| (stmts, None))
        } else {
            let mir_term = bb_data.terminator();
            intro_stmts = vec![
                vir::Stmt::comment(""),
                vir::Stmt::comment(format!("[mir] {:?}", mir_term.kind)),
            ];
            self.encode_terminator(mir_term, location)
                .map(|(stmts, succ)| (stmts, Some(succ)))
        };

        // This is an optional optimization
        if let Ok(encoding) = &stmts_succ_res && encoding.0.is_empty() && encoding.1.is_none() {
            // The statement is a noop, so we can avoid encoding the ownership and framing
            return Ok((intro_stmts, None));
        }

        // Intercept encoding error caused by an unsupported feature
        let (encoding_stmts, successor) = match stmts_succ_res {
            Ok(stmts_succ) => stmts_succ,
            Err(err) => {
                let unsupported_msg = match err.kind() {
                    EncodingErrorKind::Unsupported(msg) => {
                        msg.to_string()
                    },
                    _ => {
                        // Propagate the error
                        return Err(err);
                    }
                };
                // TODO: How to combine this with the span of the encoding error?
                let err_ctxt = ErrorCtxt::Unsupported(unsupported_msg.clone());
                let pos = self.register_error(span, err_ctxt);
                let head_stmt = if index < bb_data.statements.len() {
                    format!("[mir] {:?}", &bb_data.statements[index])
                } else {
                    format!("[mir] {:?}", bb_data.terminator())
                };
                let stmts = vec![
                    vir::Stmt::comment(head_stmt),
                    vir::Stmt::comment(format!("Unsupported feature: {unsupported_msg}")),
                    vir::Stmt::Assert(vir::Assert {
                        expr: false.into(),
                        position: pos,
                    })
                ];
                (stmts, Some(MirSuccessor::Kill))
            }
        };

        // Encode framing
        let framing_stmts = self.encode_framing_across_location(location)?;

        // Concatenate ownership + bump + encoding + framing
        let mut stmts = vec![
            vec![vir::Stmt::comment("")],
            ownership_stmts,
            intro_stmts,
            bump_stmts,
            encoding_stmts,
            framing_stmts,
        ].concat();
        self.set_stmts_default_pos(&mut stmts, span);
        Ok((stmts, successor))
    }

    /// Set the default position for the given statements.
    pub(super) fn set_stmts_default_pos(&self, stmts: &mut Vec<vir::Stmt>, default_span: Span) {
        let pos = self.encoder.error_manager().register_span(self.def_id, default_span);
        for stmt in stmts {
            let tmp_stmt = std::mem::replace(stmt, vir::Stmt::inhale(true.into()));
            let _ = std::mem::replace(stmt, tmp_stmt.set_default_pos(pos));
        }
    }

    fn encode_expiration_of_loans(
        &mut self,
        loans: Vec<facts::Loan>,
        zombie_loans: &[facts::Loan],
        location: mir::Location,
        end_location: Option<mir::Location>,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        let _frame = open_trace!(
            self,
            "encode_expiration_of_loans",
            format!(
                "{} loans and {} zombie loans between {location:?} and {end_location:?}",
                loans.len(),
                zombie_loans.len(),
            )
        );
        let expiration_span = self.get_span_of_location(location);

        let mut stmts: Vec<vir::Stmt> = vec![];
        for loan in &loans {
            let loan_location = self.polonius_info().get_loan_location(loan);
            let loan_span = self.get_span_of_location(loan_location);
            let opt_terminator = self.mir.stmt_at(loan_location).right();
            if let Some(term_kind@mir::TerminatorKind::Call {
                func: mir::Operand::Constant(ref func),
                ..
            }) = opt_terminator.map(|term| &term.kind) {
                let &ty::TyKind::FnDef(called_def_id, call_substs) = func.literal.ty().kind() else {
                    unimplemented!();
                };
                // The called method might be a trait method.
                // We try to resolve it to the concrete implementation
                // and type substitutions.
                let (called_def_id, call_substs) = self.encoder.env().query
                    .resolve_method_call(self.def_id(), called_def_id, call_substs);
                let func_name = self.env().name.get_unique_item_name(called_def_id);
                let called_contract = self.encoder
                    .get_mir_procedure_contract_for_call(self.def_id(), called_def_id, call_substs)
                    .with_default_span(loan_span)?;
                if called_contract.pledges().next().is_some() {
                    stmts.push(vir::Stmt::comment(
                        format!("Applying pledges of function {func_name}")
                    ));
                }
                for pledge in called_contract.pledges() {
                    if called_contract.borrow_infos.len() > 1 {
                        error_unsupported!(loan_span =>
                            "pledges are currently supported only on functions with a single \
                            blocking lifetime"
                        );
                    }
                    let borrow_info = &called_contract.borrow_infos[0];
                    stmts.extend(
                        self.encode_expiring_pledge(
                            loan_location, term_kind, borrow_info, pledge, expiration_span,
                        ).with_default_span(loan_span)?,
                    );
                }
            }
        }
        Ok(stmts)
    }

    /// Assert the LHS and assume the RHS of the magic wand, using as old state the pre-state of
    /// the call that created the pledge, and as current state the current memory version.
    fn encode_expiring_pledge(
        &self, loan_location: mir::Location, terminator_kind: &mir::TerminatorKind<'tcx>,
        _borrow_info: &BorrowInfo<mir::Place<'tcx>>, pledge: &Pledge, expiration_span: Span,
    ) -> EncodingResult<Vec<vir::Stmt>> {
        let _frame = open_trace!(self, "encode_expiring_pledge", format!("{pledge:?}"));
        let &mir::TerminatorKind::Call {
            ref args,
            destination,
            target,
            func: mir::Operand::Constant(ref func),
            ..
        } = terminator_kind else {
            unreachable!()
        };
        let &ty::TyKind::FnDef(called_def_id, call_substs) = func.literal.ty().kind() else {
            unimplemented!();
        };
        // The called method might be a trait method.
        // We try to resolve it to the concrete implementation
        // and type substitutions.
        let (called_def_id, call_substs) = self.encoder.env().query
            .resolve_method_call(self.def_id(), called_def_id, call_substs);

        // Prepare the encoder
        let mut old_encoded_locals;
        let mut old_encoded_locals_address;
        let mut encoded_locals;
        let mut encoded_locals_address;
        let pledge_encoder = {
            // Old expressions
            let old_version = if let Some(old_version) = self.call_pre_version.get(&loan_location) {
                old_version.clone()
            } else {
                error_internal!("no old version for call at {loan_location:?}")
            };
            old_encoded_locals = vec![
                // We don't support using `result` in the pledge.
                // TODO: Replace this dummy placeholder with None.
                SnapshotExpr::new_memory(false.into()),
            ];
            old_encoded_locals_address = vec![None];
            for (arg_idx, arg) in args.iter().enumerate() {
                let arg_ty = self.get_operand_ty(arg);
                let opt_blocked_address = self.call_blocked_address.get(&(loan_location, arg_idx));
                let encoded_arg = SnapshotExpr::new_memory(
                    if let Some(&(ref encoded_arg_target, target_ty)) = opt_blocked_address {
                        MemSnapshotDomain::encode(self.encoder, arg_ty)?
                            .constructor_function()?
                            .apply2(
                                encoded_arg_target.clone(),
                                AddressDomain::encode(self.encoder, target_ty)?
                                    .deref_function()?
                                    .apply2(encoded_arg_target.clone(), old_version.clone())
                            )
                    } else {
                        // We don't support using non-reference-typed arguments in the pledge.
                        // TODO: Replace this dummy placeholder with None.
                        false.into()
                    }
                );
                old_encoded_locals.push(encoded_arg);
                old_encoded_locals_address.push(None);
            }
            let old_bodyless_encoder = BodylessEncoder::new(
                self.encoder(),
                called_def_id,
                self.def_id(),
                call_substs,
                &old_encoded_locals,
                &old_encoded_locals_address,
                Some(old_version),
                None,
            )?;

            // Curr expressions
            let curr_version = self.encode_version(Version::CurrOld); // Version::CurrPre would work too
            encoded_locals = vec![
                // We don't support using `result` in the pledge.
                // TODO: Replace this dummy placeholder with None.
                SnapshotExpr::new_memory(false.into()),
            ];
            encoded_locals_address = vec![None];
            for (arg_idx, arg) in args.iter().enumerate() {
                let arg_ty = self.get_operand_ty(arg);
                let opt_blocked_address = self.call_blocked_address.get(&(loan_location, arg_idx));
                let encoded_arg = SnapshotExpr::new_memory(
                    if let Some(&(ref encoded_arg_target, target_ty)) = opt_blocked_address {
                        MemSnapshotDomain::encode(self.encoder, arg_ty)?
                            .constructor_function()?
                            .apply2(
                                encoded_arg_target.clone(),
                                AddressDomain::encode(self.encoder, target_ty)?
                                    .deref_function()?
                                    .apply2(encoded_arg_target.clone(), curr_version.clone())
                            )
                    } else {
                        // We don't support using non-reference-typed arguments in the pledge.
                        // TODO: Replace this dummy placeholder with None.
                        false.into()
                    }
                );
                encoded_locals.push(encoded_arg);
                encoded_locals_address.push(None);
            }
            BodylessEncoder::new(
                self.encoder(),
                called_def_id,
                self.def_id(),
                call_substs,
                &encoded_locals,
                &encoded_locals_address,
                Some(curr_version),
                Some(box old_bodyless_encoder),
            )?
        };
        let mut stmts = vec![];

        // Assert the LHS
        if let Some(assert_def_id) = pledge.lhs {
            let assert_expr = pledge_encoder.encode_contract_expr(SpecExprKind::Pledge(assert_def_id))?;
            let position = self.register_error(expiration_span, ErrorCtxt::AssertPledgeOnExpiry);
            stmts.extend(assert_expr.into_iter().map(|expr| vir::Stmt::Assert(vir::Assert {
                expr,
                position,
            })));
        }

        // Assume the RHS
        let assume_expr = pledge_encoder.encode_contract_expr(SpecExprKind::Pledge(pledge.rhs))?;
        stmts.extend(assume_expr.into_iter().map(vir::Stmt::inhale));

        Ok(stmts)
    }

    fn encode_expiring_borrows_between(
        &mut self,
        begin_loc: mir::Location,
        end_loc: mir::Location,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        trace!(
            "encode_expiring_borrows_beteewn '{:?}' '{:?}'",
            begin_loc, end_loc
        );
        let (all_dying_loans, zombie_loans) = self
            .polonius_info()
            .get_all_loans_dying_between(begin_loc, end_loc);
        // FIXME: is 'end_loc' correct here? What about 'begin_loc'?
        self.encode_expiration_of_loans(all_dying_loans, &zombie_loans, begin_loc, Some(end_loc))
    }

    fn encode_expiring_borrows_at(&mut self, location: mir::Location)
        -> SpannedEncodingResult<Vec<vir::Stmt>>
    {
        trace!("encode_expiring_borrows_at '{:?}'", location);
        let (all_dying_loans, zombie_loans) = self.polonius_info().get_all_loans_dying_at(location);
        let mut stmts = self.encode_expiration_of_loans(all_dying_loans, &zombie_loans, location, None)?;
        self.set_stmts_default_pos(&mut stmts, self.get_span_of_location(location));
        Ok(stmts)
    }

    /// Expire all active borrows. For example, to check that a method does not "forget" about
    /// an assert-on-expiry pledge.
    pub(super) fn encode_expiring_active_borrows_at(&mut self, location: mir::Location)
        -> SpannedEncodingResult<Vec<vir::Stmt>>
    {
        trace!("encode_expiring_active_borrows_at '{:?}'", location);
        let (all_active_loans, zombie_loans) = self.polonius_info().get_all_active_loans(location);
        let mut stmts = self.encode_expiration_of_loans(all_active_loans, &zombie_loans, location, None)?;
        self.set_stmts_default_pos(&mut stmts, self.get_span_of_location(location));
        Ok(stmts)
    }

    /// Encode the loans expiring on an edge of the MIR graph.
    fn encode_edge_block(
        &mut self,
        source: BasicBlockIndex,
        destination: BasicBlockIndex,
        force_block: bool,
    ) -> SpannedEncodingResult<Option<CfgBlockIndex>> {
        let source_loc = mir::Location {
            block: source,
            statement_index: self.mir[source].statements.len(),
        };
        let destination_loc = mir::Location {
            block: destination,
            statement_index: 0,
        };
        let stmts = self.encode_expiring_borrows_between(source_loc, destination_loc)?;

        if force_block || !stmts.is_empty() {
            let edge_label = self.cfg_method.get_fresh_label_name();
            let edge_block = self.cfg_method.add_block(
                &edge_label,
                vec![
                    vir::Stmt::comment(format!("========== {edge_label} ==========")),
                    vir::Stmt::comment(format!("MIR edge {source:?} --> {destination:?}")),
                ],
            );
            if !stmts.is_empty() {
                self.cfg_method
                    .add_stmt(edge_block, vir::Stmt::comment("Expire borrows"));
                self.cfg_method.add_stmts(edge_block, stmts);
            }
            Ok(Some(edge_block))
        } else {
            Ok(None)
        }
    }

    fn encode_spec_refinement(&self) -> SpannedEncodingResult<(
        Option<PreconditionWeakening>,
        Option<PostconditionStrengthening>
    )> {
        debug!("contract: {:?}", self.contract());

        let procedure_spec = &self.contract().specification;

        if let SpecificationItem::Refined(from, to) = &procedure_spec.pres {
            return Err(SpannedEncodingError::unsupported(
                "refining preconditions of specifications is not supported",
                self.mir.span,
            ));
        }

        if let SpecificationItem::Refined(from, to) = &procedure_spec.posts {
            return Err(SpannedEncodingError::unsupported(
                "refining postconditions of specifications is not supported",
                self.mir.span,
            ));
        }

        if let SpecificationItem::Refined(from, to) = &procedure_spec.pledges {
            if !from.is_empty() || to.iter().any(|p| p.lhs.is_some()) {
                return Err(SpannedEncodingError::unsupported(
                    "refining pledges of specifications is not supported",
                    self.mir.span,
                ));
            }
            // If the trait has no pledges and the implementer only makes additional guarantees
            // then the refinement is safe
        }

        Ok((None, None))
    }

    /// Encode precondition inhale on the definition side.
    fn encode_preconditions(
        &mut self,
        start_cfg_block: CfgBlockIndex,
        weakening_spec: Option<PreconditionWeakening>,
    ) -> SpannedEncodingResult<()> {
        let func_specs = self.fixed_version_encoder(Version::CurrPre)
            .encode_contract_expr(SpecExprKind::Pre)?;

        // Weakening assertion must be put before inhaling the precondition, otherwise the weakening
        // soundness check becomes trivially satisfied.
        if let Some(weakening_spec) = weakening_spec {
            let pos = self.register_error(
                weakening_spec.spec_functions_span,
                ErrorCtxt::AssertMethodPreconditionWeakening
            );
            self.cfg_method.add_stmts(start_cfg_block, vec![
                vir::Stmt::comment("Assert specification refinement weakening"),
                vir::Stmt::Assert(vir::Assert {
                    expr: weakening_spec.refinement_check_expr,
                    position: pos
                }),
            ]);
        }

        self.cfg_method.add_stmt(
            start_cfg_block, vir::Stmt::comment("Assume precondition"),
        );
        for func_spec in func_specs {
            self.cfg_method.add_stmt(
                start_cfg_block,
                vir::Stmt::Inhale(vir::Inhale { expr: func_spec })
            );
        }
        self.cfg_method.add_stmts(start_cfg_block, vec![
                vir::Stmt::comment("Remember initial version"),
            vir::Stmt::Assign(vir::Assign {
                target: self.encode_version(Version::Pre).into(),
                source: self.encode_version(Version::CurrPre).into(), // CurrOld would work too
                kind: vir::AssignKind::Ghost,
            }),
        ]);

        // Encode a version bump to stabilize the precondition
        let ownership_stmts = self.encode_ownership_at_precondition().with_span(self.mir.span)?;
        let bump_stmts = self.encode_version_bump().with_span(self.mir.span)?;
        let framing_stmts = self.encode_framing_at_precondition().with_span(self.mir.span)?;
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::comment("Ownership"));
        self.cfg_method.add_stmts(start_cfg_block, ownership_stmts);
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::comment("Stabilize precondition"));
        self.cfg_method.add_stmts(start_cfg_block, bump_stmts);
        self.cfg_method.add_stmts(start_cfg_block, framing_stmts);

        Ok(())
    }

    /// Encode postcondition exhale in the `return_cfg_block` CFG block.
    fn encode_postconditions(
        &mut self,
        return_cfg_block: CfgBlockIndex,
        strengthening_spec: Option<PostconditionStrengthening>,
    ) -> SpannedEncodingResult<()> {
        // Encode a version bump to stabilize the postcondition
        let ownership_stmts = self.encode_ownership_at_postcondition().with_span(self.mir.span)?;
        let bump_stmts = self.encode_version_bump().with_span(self.mir.span)?;
        let framing_stmts = self.encode_framing_at_postcondition().with_span(self.mir.span)?;
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment("Ownership"));
        self.cfg_method.add_stmts(return_cfg_block, ownership_stmts.clone());
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment("Stabilize postcondition"));
        self.cfg_method.add_stmts(return_cfg_block, bump_stmts);
        self.cfg_method.add_stmts(return_cfg_block, framing_stmts);
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment("Ownership"));
        self.cfg_method.add_stmts(return_cfg_block, ownership_stmts);

        // Assert possible strengthening
        if let Some(strengthening_spec) = strengthening_spec {
            self.cfg_method.add_stmt(
                return_cfg_block,
                vir::Stmt::comment("Assert specification refinement strengthening"),
            );
            let pos = self.register_error(strengthening_spec.spec_functions_span, ErrorCtxt::AssertMethodPostconditionStrengthening);
            self.cfg_method.add_stmt(
                return_cfg_block,
                vir::Stmt::Assert( vir::Assert {
                    expr: strengthening_spec.refinement_check_expr,
                    position: pos,
                }),
            );
        }

        let func_specs = self.fixed_version_encoder(Version::CurrPre)
            .encode_contract_expr(SpecExprKind::Post)?;

        // Assert functional specification of postcondition
        self.cfg_method.add_stmt(
            return_cfg_block, vir::Stmt::comment("Assert postcondition"),
        );
        let default_pos = self.register_span(self.span());
        for func_spec in func_specs {
            debug_assert!(!func_spec.pos().is_default());
            let func_spec = func_spec.set_default_pos(default_pos);
            let pos = func_spec.pos();
            self.encoder().error_manager().set_error(
                pos, ErrorCtxt::AssertMethodPostcondition,
            );
            self.cfg_method.add_stmt(
                return_cfg_block,
                vir::Stmt::Assert( vir::Assert {
                    expr: func_spec,
                    position: pos,
                }),
            );
        }

        for pledge in self.contract().specification.pledges.extract_with_selective_replacement_iter() {
            let pledge_span = self.tcx().span_of_impl(pledge.rhs).unwrap();
            error_unsupported!(pledge_span => "checking pledges is currently not supported");
        }

        Ok(())
    }

    /// Get the basic blocks that encode the specification of a loop invariant
    fn get_loop_spec_blocks(&self, loop_head: BasicBlockIndex) -> Vec<BasicBlockIndex> {
        let mut res = vec![];
        for bbi in self.procedure.get_reachable_cfg_blocks() {
            if Some(loop_head) == self.loop_encoder.get_loop_head(bbi)
                && self.procedure.is_spec_block(bbi)
            {
                res.push(bbi)
            } else {
                trace!(
                    "bbi {bbi:?} has head {:?} and 'is spec' is {}",
                    self.loop_encoder.get_loop_head(bbi),
                    self.procedure.is_spec_block(bbi),
                );
            }
        }
        res
    }

    fn check_vir(&self) -> SpannedEncodingResult<()> {
        if self.cfg_method.has_loops() {
            return Err(SpannedEncodingError::internal(
                "The Viper encoding contains unexpected loops in the CFG",
                self.mir.span,
            ));
        }
        Ok(())
    }

    /// Computes the span of a loop.
    fn get_loop_span(&self, loop_head: mir::BasicBlock) -> Span {
        let loop_info = self.loop_encoder.loops();
        debug_assert!(loop_info.is_loop_head(loop_head));
        let loop_body = loop_info.get_loop_body(loop_head);
        let loop_head_span = self.get_span_of_basic_block(loop_head);
        loop_body
            .iter()
            .map(|&bb| self.get_span_of_basic_block(bb))
            .filter(|&span| span.contains(loop_head_span))
            .min()
            .unwrap()
    }

    pub fn get_return_locations(&self) -> Vec<mir::Location> {
        let mut locations = vec![];
        for (bb, bb_data) in self.mir.basic_blocks.iter_enumerated() {
            if let mir::TerminatorKind::Return = bb_data.terminator().kind {
                locations.push(self.mir.terminator_loc(bb))
            }
        }
        locations
    }

    pub fn get_single_return_location(&self) -> EncodingResult<Option<mir::Location>> {
        let locations = self.get_return_locations();
        match locations[..] {
            [] => Ok(None),
            [l] => Ok(Some(l)),
            _ => error_internal!("Expected at most one return location, but got: {:?}", locations),
        }
    }

    pub(super) fn encode_version(&self, version: Version) -> vir::LocalVar {
        self.fixed_version_encoder(version).version().clone()
    }

    pub(super) fn fixed_version_encoder(&self, version: Version) -> &FixedVersionEncoder<'p, 'v, 'tcx> {
        match version {
            Version::Old => &self.old_version_encoder,
            Version::OldPre => &self.old_pre_version_encoder,
            Version::CurrPre => &self.curr_pre_version_encoder,
            Version::CurrOld => &self.curr_old_version_encoder,
            Version::Pre => self.pre_version_encoder.as_ref(),
        }
    }

    pub fn call_or_stmt(&self, location: mir::Location) -> CallOrStmt {
        let is_call = if let Some(term) = self.mir.stmt_at(location).right() {
            matches!(term.kind, mir::TerminatorKind::Call { .. })
        } else {
            false
        };
        if is_call {
            CallOrStmt::Call
        } else {
            CallOrStmt::Stmt
        }
    }

    /// Collect all types (transitively) used in the method. Note that it's slow.
    fn get_used_types(&self) -> EncodingResult<Vec<ty::Ty<'tcx>>> {
        let mut used_types = FxHashSet::default();
        let mut work_list = Vec::with_capacity(self.mir.local_decls.len());
        for local in self.mir.local_decls.indices() {
            work_list.push(self.get_local_ty(local));
        }
        let param_env = self.tcx().param_env(self.def_id());
        while let Some(used_ty) = work_list.pop() {
            if !used_types.insert(self.tcx().normalize_erasing_regions(param_env, used_ty)) {
                continue;
            }
            let type_layout = type_layout::build_layout(self.encoder, used_ty)?;
            // Take the field types from the layout of the instance
            for variant in &type_layout.variants {
                for field in &variant.fields {
                    if let Some(field_ty) = field.ty {
                        work_list.push(field_ty);
                    }
                }
            }
            // Add the reachable types that are not in the layout of the instance
            match *used_ty.kind() {
                ty::TyKind::RawPtr(ty::TypeAndMut { ty: inner_ty, .. })
                | ty::TyKind::Ref(_, inner_ty, _) => {
                    work_list.push(inner_ty);
                }
                _ => {}
            }
        }
        Ok(used_types.into_iter().sorted_unstable().collect())
    }

    fn encode_axioms(&self) -> EncodingResult<Vec<vir::Stmt>> {
        let used_types = self.get_used_types()?;
        let mut stmts = Vec::with_capacity(4 * used_types.len());
        stmts.push(vir::Stmt::comment(""));
        stmts.push(vir::Stmt::comment(format!(
            "Library ownership axioms of {} types:", used_types.len()
        )));
        for &used_ty in &used_types {
            let axioms = library_ownership::build_library_ownership_axioms(self.encoder, used_ty)?;
            for (comment, axiom) in axioms.into_iter() {
                stmts.push(vir::Stmt::comment(comment));
                stmts.push(vir::Stmt::inhale(axiom));
            }
        }
        Ok(stmts)
    }

    fn check_body(&self) -> SpannedEncodingResult<()> {
        // Check that non-trusted functions can use unsafe code only if they are ghost
        if !self.is_ghost(None, self.def_id()) {
            for source_data in self.mir.source_scopes.iter() {
                let safety = source_data.local_data.as_ref().assert_crate_local().safety;
                if matches!(safety, mir::Safety::FnUnsafe | mir::Safety::ExplicitUnsafe(_)) {
                    error_incorrect!(source_data.span =>
                        "only trusted or ghost pure functions can use unsafe code"
                    )
                }
            }
        }

        // Check that unstable functions are called at most once per path
        if self.is_pure_unstable(None, self.def_id(), self.substs())
           && !self.is_ghost(None, self.def_id())
        {
            let mir_expr = self.interpret_body()?;
            self.check_max_unstable_call_per_path(&mir_expr, 1)?;
        }


        Ok(())
    }

    fn check_max_unstable_call_per_path(&self, expr: &MirExpr<'tcx>, max: usize) -> SpannedEncodingResult<()> {
        let mut subtree_max = max;
        if let MirExpr::Call { func, span, .. } = expr {
            let &ty::TyKind::FnDef(called_def_id, call_substs) = func.literal.ty().kind() else {
                unimplemented!();
            };
            if self.is_pure_unstable(Some(self.def_id()), called_def_id, call_substs) {
                if subtree_max == 0 {
                    error_incorrect!(span.unwrap() =>
                        "unstable function called more than once per path"
                    )
                }
                subtree_max -= 1;
            }
        }
        expr.visit_subexpr(&|e| { self.check_max_unstable_call_per_path(e, subtree_max) })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum InvariantUsage {
    AssertOnEntry,
    AssumeBeforeIteration,
    AssertAfterIteration,
}

type PreconditionWeakening = RefinementCheckExpr;
type PostconditionStrengthening = RefinementCheckExpr;
struct RefinementCheckExpr {
    spec_functions_span: MultiSpan,
    refinement_check_expr: vir::Expr,
}
