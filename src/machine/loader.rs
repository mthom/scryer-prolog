use prolog_parser::ast::*;
use prolog_parser::{clause_name, temp_v};

use crate::forms::*;
use crate::indexing::*;
use crate::machine::load_state::*;
use crate::machine::machine_indices::*;
use crate::machine::preprocessor::*;
use crate::machine::*;

use indexmap::IndexSet;
use slice_deque::{sdeq, SliceDeque};

use std::cell::Cell;
use std::convert::TryFrom;
use std::rc::Rc;

/*
 * The loader compiles Prolog terms read from a TermStream instance,
 * which may be incremental or monolithic. The monolithic term stream
 * reads from a file. It's used only to bootstrap Scryer at
 * start-up. Once Scryer is bootstrapped, all compilation and loading
 * work is divided between loader.pl and loader.rs.
 *
 * loader.pl does a few high-level things more easily handled from
 * Prolog that are not supported (or needed) during bootstrapping:
 * term and goal expansion, loading modules from different streams,
 * verifying certain kinds of declarations, perhaps (in the future?)
 * compiling inline disjunctions.
 *
 * Since the loader can operate incrementally, it uses an intermittent
 * structure to rebuild the loader between invocations. Preprocessor
 * needs access to a &'a mut Machine for as long as it lives, and we
 * can't have copies of &'a mut Machine distributed among multiple
 * owners.
 *
 * When loading a module, we modify the records of the WAM with the
 * location of new predicates, with new meta-predicate information,
 * new term and goal expansions, new dynamic clauses, etc. Should the
 * loader fail later, all changes must be rolled back, restoring the
 * WAM to its prior state. Retraction records describe individual changes
 * made by the loader, and they may be used later.
 */

#[derive(Debug)]
pub(crate) enum RetractionRecord {
    AddedMetaPredicate(ClauseName, PredicateKey),
    ReplacedMetaPredicate(ClauseName, ClauseName, Vec<MetaSpec>),
    AddedModule(ClauseName),
    ReplacedModule(ModuleDecl, ListingSource, LocalExtensiblePredicates),
    AddedModuleOp(ClauseName, OpDecl),
    ReplacedModuleOp(ClauseName, OpDecl, usize, Specifier),
    AddedModulePredicate(ClauseName, PredicateKey),
    ReplacedModulePredicate(ClauseName, PredicateKey, IndexPtr),
    AddedDiscontiguousPredicate(CompilationTarget, PredicateKey),
    AddedDynamicPredicate(CompilationTarget, PredicateKey),
    AddedMultifilePredicate(CompilationTarget, PredicateKey),
    AddedUserOp(OpDecl),
    ReplacedUserOp(OpDecl, usize, Specifier),
    AddedExtensiblePredicate(CompilationTarget, PredicateKey),
    AddedUserPredicate(PredicateKey),
    ReplacedUserPredicate(PredicateKey, IndexPtr),
    AddedIndex(OptArgIndexKey, usize), //, Vec<usize>),
    RemovedIndex(usize, OptArgIndexKey, usize),
    ReplacedChoiceOffset(usize, usize),
    AppendedTrustMe(usize, usize, bool),
    ReplacedSwitchOnTermVarIndex(usize, IndexingCodePtr),
    ModifiedTryMeElse(usize, usize),
    ModifiedRetryMeElse(usize, usize),
    ModifiedRevJmpBy(usize, usize),
    SkeletonClausePopBack(CompilationTarget, PredicateKey),
    SkeletonClausePopFront(CompilationTarget, PredicateKey),
    SkeletonLocalClauseClausePopBack(CompilationTarget, CompilationTarget, PredicateKey),
    SkeletonLocalClauseClausePopFront(CompilationTarget, CompilationTarget, PredicateKey),
    SkeletonLocalClauseTruncateBack(CompilationTarget, CompilationTarget, PredicateKey, usize),
    SkeletonClauseTruncateBack(CompilationTarget, PredicateKey, usize),
    SkeletonClauseStartReplaced(CompilationTarget, PredicateKey, usize, usize),
    RemovedSkeletonClause(
        CompilationTarget,
        PredicateKey,
        usize,
        ClauseIndexInfo,
        usize,
    ),
    ReplacedIndexingLine(usize, Vec<IndexingLine>),
    RemovedLocalSkeletonClauseLocations(
        CompilationTarget,
        CompilationTarget,
        PredicateKey,
        SliceDeque<usize>,
    ),
    RemovedSkeleton(CompilationTarget, PredicateKey, PredicateSkeleton),
    ReplacedDynamicElseOffset(usize, usize),
    AppendedNextOrFail(usize, NextOrFail),
}

/*
 * Retractions to be performed on rollback are represented by
 * individual records, and the original extent of the code vector of
 * the IndexStore, of which there are several (one per module).  The
 * "extent" of a code vector is its length prior to an attempted
 * module load. The only code vector of the WAM's IndexStore, "code",
 * is shared by all modules, including the default "user" module.
 */

pub(super) struct RetractionInfo {
    orig_code_extent: usize,
    records: Vec<RetractionRecord>,
}

impl RetractionInfo {
    #[inline]
    pub(super) fn new(orig_code_extent: usize) -> Self {
        Self {
            orig_code_extent,
            records: vec![], //BTreeMap::new(),
        }
    }

    #[inline]
    pub(crate) fn push_record(&mut self, record: RetractionRecord) {
        self.records.push(record);
    }

    #[inline]
    pub(crate) fn reset(&mut self, code_len: usize) -> Self {
        let orig_code_extent = self.orig_code_extent;
        self.orig_code_extent = code_len;

        Self {
            orig_code_extent,
            records: mem::replace(&mut self.records, vec![]),
        }
    }
}

impl<'a> Drop for LoadState<'a> {
    fn drop(&mut self) {
        while let Some(record) = self.retraction_info.records.pop() {
            match record {
                RetractionRecord::AddedMetaPredicate(target_module_name, key) => {
                    match target_module_name.as_str() {
                        "user" => {
                            self.wam.indices.meta_predicates.remove(&key);
                        }
                        _ => match self.wam.indices.modules.get_mut(&target_module_name) {
                            Some(ref mut module) => {
                                module.meta_predicates.remove(&key);
                            }
                            _ => {
                                unreachable!()
                            }
                        },
                    }
                }
                RetractionRecord::ReplacedMetaPredicate(target_module_name, name, meta_specs) => {
                    match target_module_name.as_str() {
                        "user" => {
                            self.wam
                                .indices
                                .meta_predicates
                                .insert((name, meta_specs.len()), meta_specs);
                        }
                        _ => match self.wam.indices.modules.get_mut(&target_module_name) {
                            Some(ref mut module) => {
                                module
                                    .meta_predicates
                                    .insert((name, meta_specs.len()), meta_specs);
                            }
                            _ => {
                                unreachable!()
                            }
                        },
                    }
                }
                RetractionRecord::AddedModule(module_name) => {
                    self.wam.indices.modules.remove(&module_name);
                }
                RetractionRecord::ReplacedModule(
                    module_decl,
                    listing_src,
                    local_extensible_predicates,
                ) => match self.wam.indices.modules.get_mut(&module_decl.name) {
                    Some(ref mut module) => {
                        module.module_decl = module_decl;
                        module.listing_src = listing_src;
                        module.local_extensible_predicates = local_extensible_predicates;
                    }
                    _ => {
                        unreachable!()
                    }
                },
                RetractionRecord::AddedDiscontiguousPredicate(compilation_target, key) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            self.wam
                                .indices
                                .extensible_predicates
                                .get_mut(&key)
                                .map(|skeleton| {
                                    skeleton.core.is_discontiguous = false;
                                });
                        }
                        CompilationTarget::Module(module_name) => {
                            match self.wam.indices.modules.get_mut(&module_name) {
                                Some(ref mut module) => {
                                    module.extensible_predicates.get_mut(&key).map(|skeleton| {
                                        skeleton.core.is_discontiguous = false;
                                    });
                                }
                                None => {}
                            }
                        }
                    }
                }
                RetractionRecord::AddedDynamicPredicate(compilation_target, key) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            self.wam
                                .indices
                                .extensible_predicates
                                .get_mut(&key)
                                .map(|skeleton| {
                                    skeleton.core.is_dynamic = false;
                                });
                        }
                        CompilationTarget::Module(module_name) => {
                            match self.wam.indices.modules.get_mut(&module_name) {
                                Some(ref mut module) => {
                                    module.extensible_predicates.get_mut(&key).map(|skeleton| {
                                        skeleton.core.is_dynamic = false;
                                    });
                                }
                                None => {}
                            }
                        }
                    }
                }
                RetractionRecord::AddedMultifilePredicate(compilation_target, key) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            self.wam
                                .indices
                                .extensible_predicates
                                .get_mut(&key)
                                .map(|skeleton| {
                                    skeleton.core.is_multifile = false;
                                });
                        }
                        CompilationTarget::Module(module_name) => {
                            match self.wam.indices.modules.get_mut(&module_name) {
                                Some(ref mut module) => {
                                    module.extensible_predicates.get_mut(&key).map(|skeleton| {
                                        skeleton.core.is_multifile = false;
                                    });
                                }
                                None => {}
                            }
                        }
                    }
                }
                RetractionRecord::AddedModuleOp(module_name, mut op_decl) => {
                    match self.wam.indices.modules.get_mut(&module_name) {
                        Some(ref mut module) => {
                            op_decl.remove(&mut module.op_dir);
                        }
                        None => {}
                    }
                }
                RetractionRecord::ReplacedModuleOp(module_name, mut op_decl, prec, spec) => {
                    match self.wam.indices.modules.get_mut(&module_name) {
                        Some(ref mut module) => {
                            op_decl.prec = prec;
                            op_decl.spec = spec;
                            op_decl.insert_into_op_dir(&mut module.op_dir);
                        }
                        None => {}
                    }
                }
                RetractionRecord::AddedModulePredicate(module_name, key) => {
                    match self.wam.indices.modules.get_mut(&module_name) {
                        Some(ref mut module) => {
                            module.code_dir.remove(&key);
                        }
                        None => {}
                    }
                }
                RetractionRecord::ReplacedModulePredicate(module_name, key, old_code_idx) => {
                    match self.wam.indices.modules.get_mut(&module_name) {
                        Some(ref mut module) => {
                            module
                                .code_dir
                                .get_mut(&key)
                                .map(|code_idx| code_idx.replace(old_code_idx));
                        }
                        None => {}
                    }
                }
                RetractionRecord::AddedExtensiblePredicate(compilation_target, key) => {
                    self.wam
                        .indices
                        .remove_predicate_skeleton(&compilation_target, &key);
                }
                RetractionRecord::AddedUserOp(mut op_decl) => {
                    op_decl.remove(&mut self.wam.indices.op_dir);
                }
                RetractionRecord::ReplacedUserOp(mut op_decl, prec, spec) => {
                    op_decl.prec = prec;
                    op_decl.spec = spec;
                    op_decl.insert_into_op_dir(&mut self.wam.indices.op_dir);
                }
                RetractionRecord::AddedUserPredicate(key) => {
                    self.wam.indices.code_dir.remove(&key);
                }
                RetractionRecord::ReplacedUserPredicate(key, old_code_idx) => {
                    self.wam
                        .indices
                        .code_dir
                        .get_mut(&key)
                        .map(|code_idx| code_idx.replace(old_code_idx));
                }
                RetractionRecord::AddedIndex(index_key, clause_loc) => {
                    // WAS: inner_index_locs) => {
                    if let Some(index_loc) = index_key.switch_on_term_loc() {
                        let indexing_code = match &mut self.wam.code_repo.code[index_loc] {
                            Line::IndexingCode(indexing_code) => indexing_code,
                            _ => {
                                unreachable!()
                            }
                        };

                        match index_key {
                            OptArgIndexKey::Constant(
                                _,
                                index_loc,
                                constant,
                                overlapping_constants,
                            ) => {
                                remove_constant_indices(
                                    &constant,
                                    &overlapping_constants,
                                    indexing_code,
                                    clause_loc - index_loc, // WAS: &inner_index_locs,
                                );
                            }
                            OptArgIndexKey::Structure(_, index_loc, name, arity) => {
                                remove_structure_index(
                                    &name,
                                    arity,
                                    indexing_code,
                                    clause_loc - index_loc, // WAS: &inner_index_locs,
                                );
                            }
                            OptArgIndexKey::List(_, index_loc) => {
                                remove_list_index(
                                    indexing_code,
                                    clause_loc - index_loc, // WAS: &inner_index_locs,
                                );
                            }
                            OptArgIndexKey::None => {
                                unreachable!();
                            }
                        }
                    }
                }
                RetractionRecord::RemovedIndex(_index_loc, _index_key, _clause_loc) => {
                    // TODO: this needs to be fixed! RemovedIndex doesn't provide
                    // enough information to restore the index. Correct that, then
                    // write the retraction logic of this arm.
                }
                RetractionRecord::ReplacedChoiceOffset(instr_loc, offset) => {
                    match &mut self.wam.code_repo.code[instr_loc] {
                        Line::Choice(ChoiceInstruction::TryMeElse(ref mut o))
                        | Line::Choice(ChoiceInstruction::RetryMeElse(ref mut o))
                        | Line::Choice(ChoiceInstruction::DefaultRetryMeElse(ref mut o)) => {
                            *o = offset;
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                RetractionRecord::AppendedTrustMe(instr_loc, offset, is_default) => {
                    match &mut self.wam.code_repo.code[instr_loc] {
                        Line::Choice(ref mut choice_instr) => {
                            *choice_instr = if is_default {
                                ChoiceInstruction::DefaultTrustMe(offset)
                            } else {
                                ChoiceInstruction::TrustMe(offset)
                            };
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                RetractionRecord::ReplacedSwitchOnTermVarIndex(index_loc, old_v) => {
                    match &mut self.wam.code_repo.code[index_loc] {
                        Line::IndexingCode(ref mut indexing_code) => match &mut indexing_code[0] {
                            IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                                _,
                                ref mut v,
                                ..,
                            )) => {
                                *v = old_v;
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                }
                RetractionRecord::ModifiedTryMeElse(instr_loc, o) => {
                    self.wam.code_repo.code[instr_loc] =
                        Line::Choice(ChoiceInstruction::TryMeElse(o));
                }
                RetractionRecord::ModifiedRetryMeElse(instr_loc, o) => {
                    self.wam.code_repo.code[instr_loc] =
                        Line::Choice(ChoiceInstruction::RetryMeElse(o));
                }
                RetractionRecord::ModifiedRevJmpBy(instr_loc, o) => {
                    self.wam.code_repo.code[instr_loc] =
                        Line::Control(ControlInstruction::RevJmpBy(o));
                }
                RetractionRecord::SkeletonClausePopBack(compilation_target, key) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clauses.pop_back();
                            skeleton.core.clause_clause_locs.pop_back();
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonClausePopFront(compilation_target, key) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clauses.pop_front();
                            skeleton.core.clause_clause_locs.pop_front();
                            skeleton.core.clause_assert_margin -= 1;
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonLocalClauseClausePopFront(
                    src_compilation_target,
                    local_compilation_target,
                    key,
                ) => {
                    match self.wam.indices.get_local_predicate_skeleton_mut(
                        src_compilation_target,
                        local_compilation_target,
                        self.listing_src_file_name(),
                        key,
                    ) {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.pop_front();
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonLocalClauseClausePopBack(
                    src_compilation_target,
                    local_compilation_target,
                    key,
                ) => {
                    match self.wam.indices.get_local_predicate_skeleton_mut(
                        src_compilation_target,
                        local_compilation_target,
                        self.listing_src_file_name(),
                        key,
                    ) {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.pop_back();
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonLocalClauseTruncateBack(
                    src_compilation_target,
                    local_compilation_target,
                    key,
                    len,
                ) => {
                    match self.wam.indices.get_local_predicate_skeleton_mut(
                        src_compilation_target,
                        local_compilation_target,
                        self.listing_src_file_name(),
                        key,
                    ) {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.truncate_back(len);
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonClauseTruncateBack(compilation_target, key, len) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clauses.truncate_back(len);
                            skeleton.core.clause_clause_locs.truncate_back(len);
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonClauseStartReplaced(
                    compilation_target,
                    key,
                    target_pos,
                    clause_start,
                ) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clauses[target_pos].clause_start = clause_start;
                        }
                        None => {}
                    }
                }
                RetractionRecord::RemovedSkeletonClause(
                    compilation_target,
                    key,
                    target_pos,
                    clause_index_info,
                    clause_clause_loc,
                ) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton
                                .core
                                .clause_clause_locs
                                .insert(target_pos, clause_clause_loc);
                            skeleton.clauses.insert(target_pos, clause_index_info);
                        }
                        None => {}
                    }
                }
                RetractionRecord::ReplacedIndexingLine(index_loc, indexing_code) => {
                    self.wam.code_repo.code[index_loc] = Line::IndexingCode(indexing_code);
                }
                RetractionRecord::RemovedLocalSkeletonClauseLocations(
                    compilation_target,
                    local_compilation_target,
                    key,
                    clause_locs,
                ) => {
                    match self.wam.indices.get_local_predicate_skeleton_mut(
                        compilation_target,
                        local_compilation_target,
                        self.listing_src_file_name(),
                        key,
                    ) {
                        Some(skeleton) => skeleton.clause_clause_locs = clause_locs,
                        None => {}
                    }
                }
                RetractionRecord::RemovedSkeleton(compilation_target, key, skeleton) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            self.wam.indices.extensible_predicates.insert(key, skeleton);
                        }
                        CompilationTarget::Module(module_name) => {
                            if let Some(module) = self.wam.indices.modules.get_mut(&module_name) {
                                module.extensible_predicates.insert(key, skeleton);
                            }
                        }
                    }
                }
                RetractionRecord::ReplacedDynamicElseOffset(instr_loc, next) => {
                    match &mut self.wam.code_repo.code[instr_loc] {
                        Line::Choice(ChoiceInstruction::DynamicElse(
                            _,
                            _,
                            NextOrFail::Next(ref mut o),
                        ))
                        | Line::Choice(ChoiceInstruction::DynamicInternalElse(
                            _,
                            _,
                            NextOrFail::Next(ref mut o),
                        )) => {
                            *o = next;
                        }
                        _ => {}
                    }
                }
                RetractionRecord::AppendedNextOrFail(instr_loc, fail) => {
                    match &mut self.wam.code_repo.code[instr_loc] {
                        Line::Choice(ChoiceInstruction::DynamicElse(
                            _,
                            _,
                            ref mut next_or_fail,
                        ))
                        | Line::Choice(ChoiceInstruction::DynamicInternalElse(
                            _,
                            _,
                            ref mut next_or_fail,
                        )) => {
                            *next_or_fail = fail;
                        }
                        _ => {}
                    }
                }
            }
        }

        // TODO: necessary? unnecessary?
        // self.wam.code_repo.code.truncate(self.retraction_info.orig_code_extent);
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(crate) enum CompilationTarget {
    Module(ClauseName),
    User,
}

impl Default for CompilationTarget {
    #[inline]
    fn default() -> Self {
        CompilationTarget::User
    }
}

impl CompilationTarget {
    #[inline]
    pub(super) fn take(&mut self) -> CompilationTarget {
        mem::replace(self, CompilationTarget::User)
    }

    #[inline]
    pub(crate) fn module_name(&self) -> ClauseName {
        match self {
            CompilationTarget::User => {
                clause_name!("user")
            }
            CompilationTarget::Module(ref module_name) => module_name.clone(),
        }
    }
}

pub(crate) struct PredicateQueue {
    pub(super) predicates: Vec<Term>,
    pub(super) compilation_target: CompilationTarget,
}

impl PredicateQueue {
    #[inline]
    pub(super) fn push(&mut self, clause: Term) {
        self.predicates.push(clause);
    }

    #[inline]
    pub(crate) fn first(&self) -> Option<&Term> {
        self.predicates.first()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }

    #[inline]
    pub(super) fn take(&mut self) -> Self {
        Self {
            predicates: mem::replace(&mut self.predicates, vec![]),
            compilation_target: self.compilation_target.take(),
        }
    }

    #[inline]
    pub(super) fn len(&self) -> usize {
        self.predicates.len()
    }
}

macro_rules! predicate_queue {
    [$($v:expr),*] => (
        PredicateQueue {
            predicates: vec![$($v,)*],
            compilation_target: CompilationTarget::default(),
        }
    )
}

pub(crate) struct Loader<'a, TermStream> {
    pub(super) load_state: LoadState<'a>,
    pub(super) predicates: PredicateQueue,
    pub(super) clause_clauses: Vec<(Term, Term)>,
    pub(super) term_stream: TermStream,
    pub(super) non_counted_bt_preds: IndexSet<PredicateKey>,
}

impl<'a, TS: TermStream> Loader<'a, TS> {
    #[inline]
    pub(super) fn new(term_stream: TS, wam: &'a mut Machine) -> Self {
        let load_state = LoadState {
            compilation_target: CompilationTarget::User,
            module_op_exports: vec![],
            retraction_info: RetractionInfo::new(wam.code_repo.code.len()),
            wam,
        };

        Self {
            load_state,
            term_stream,
            non_counted_bt_preds: IndexSet::new(),
            predicates: predicate_queue![],
            clause_clauses: vec![],
        }
    }

    pub(crate) fn load(mut self) -> Result<TS::Evacuable, SessionError> {
        while let Some(decl) = self.dequeue_terms()? {
            self.load_decl(decl)?;
        }

        TS::evacuate(self)
    }

    fn dequeue_terms(&mut self) -> Result<Option<Declaration>, SessionError> {
        while !self.term_stream.eof()? {
            let term = self.term_stream.next(&self.load_state.composite_op_dir())?;

            // if is_consistent is false, self.predicates is not empty.
            if !term.is_consistent(&self.predicates) {
                self.compile_and_submit()?;
            }

            let term = match term {
                Term::Clause(_, name, terms, _) if name.as_str() == ":-" && terms.len() == 1 => {
                    return Ok(Some(setup_declaration(&self.load_state, terms)?));
                }
                term => term,
            };

            self.predicates.push(term);
        }

        Ok(None)
    }

    pub(super) fn load_decl(&mut self, decl: Declaration) -> Result<(), SessionError> {
        match decl {
            Declaration::Dynamic(name, arity) => {
                let compilation_target = self.load_state.compilation_target.clone();
                self.add_dynamic_predicate(compilation_target, name, arity)?;
            }
            Declaration::MetaPredicate(module_name, name, meta_specs) => {
                self.load_state
                    .add_meta_predicate_record(module_name, name, meta_specs);
            }
            Declaration::Module(module_decl) => {
                self.load_state.compilation_target =
                    CompilationTarget::Module(module_decl.name.clone());

                self.predicates.compilation_target = self.load_state.compilation_target.clone();

                self.load_state
                    .add_module(module_decl, self.term_stream.listing_src().clone());
            }
            Declaration::NonCountedBacktracking(name, arity) => {
                self.non_counted_bt_preds.insert((name, arity));
            }
            Declaration::Op(op_decl) => {
                self.load_state.add_op_decl(&op_decl);
            }
            Declaration::UseModule(module_src) => {
                self.load_state.use_module(module_src)?;
            }
            Declaration::UseQualifiedModule(module_src, exports) => {
                self.load_state.use_qualified_module(module_src, exports)?;
            }
        }

        Ok(())
    }

    pub(super) fn read_term_from_heap(&self, heap_term_loc: RegType) -> Result<Term, SessionError> {
        let machine_st = &self.load_state.wam.machine_st;
        let term_addr = machine_st[heap_term_loc];

        if machine_st.is_cyclic_term(term_addr) {
            return Err(SessionError::from(CompilationError::CannotParseCyclicTerm));
        }

        let mut term_stack = vec![];

        for addr in machine_st.post_order_iter(term_addr) {
            match machine_st.heap.index_addr(&addr).as_ref() {
                HeapCellValue::Addr(Addr::Lis(_)) | HeapCellValue::Addr(Addr::PStrLocation(..)) => {
                    let tail = term_stack.pop().unwrap();
                    let head = term_stack.pop().unwrap();

                    term_stack.push(Term::Cons(Cell::default(), Box::new(head), Box::new(tail)));
                }
                HeapCellValue::Addr(addr) => {
                    if let Some(r) = addr.as_var() {
                        let offset_string = match r {
                            Ref::HeapCell(h) | Ref::AttrVar(h) => format!("_{}", h),
                            Ref::StackCell(fr, sc) => format!("_s_{}_{}", fr, sc),
                        };

                        term_stack.push(Term::Var(Cell::default(), Rc::new(offset_string)));
                    } else {
                        match addr.as_constant_index(machine_st) {
                            Some(constant) => {
                                term_stack.push(Term::Constant(Cell::default(), constant));
                            }
                            None => {
                                return Err(SessionError::from(CompilationError::UnreadableTerm));
                            }
                        }
                    }
                }
                HeapCellValue::Atom(ref name, ref shared_op_desc) => {
                    term_stack.push(Term::Constant(
                        Cell::default(),
                        Constant::Atom(name.clone(), shared_op_desc.clone()),
                    ));
                }
                HeapCellValue::Integer(ref integer) => {
                    term_stack.push(Term::Constant(
                        Cell::default(),
                        Constant::Integer(integer.clone()),
                    ));
                }
                HeapCellValue::NamedStr(arity, ref name, ref shared_op_desc) => {
                    let subterms = term_stack
                        .drain(term_stack.len() - arity..)
                        .map(Box::new)
                        .collect();

                    term_stack.push(Term::Clause(
                        Cell::default(),
                        name.clone(),
                        subterms,
                        shared_op_desc.clone(),
                    ));
                }
                HeapCellValue::PartialString(..) => {
                    let string = machine_st.heap_pstr_iter(addr).to_string();
                    term_stack.push(Term::Constant(
                        Cell::default(),
                        Constant::String(Rc::new(string)),
                    ));
                }
                HeapCellValue::Rational(ref rational) => {
                    term_stack.push(Term::Constant(
                        Cell::default(),
                        Constant::Rational(rational.clone()),
                    ));
                }
                _ => {
                    return Err(SessionError::from(CompilationError::UnreadableTerm));
                }
            }
        }

        debug_assert!(term_stack.len() == 1);
        Ok(term_stack.pop().unwrap())
    }

    fn extract_module_export_list_from_heap(
        &self,
        r: RegType,
    ) -> Result<IndexSet<ModuleExport>, SessionError> {
        let export_list = self.read_term_from_heap(r)?;
        let atom_tbl = self.load_state.wam.machine_st.atom_tbl.clone();
        let export_list = setup_module_export_list(export_list, atom_tbl)?;

        Ok(export_list.into_iter().collect())
    }

    fn add_clause_clause(&mut self, term: Term) -> Result<(), CompilationError> {
        match term {
            Term::Clause(_, turnstile, mut terms, _)
                if turnstile.as_str() == ":-" && terms.len() == 2 =>
            {
                let body = *terms.pop().unwrap();
                let head = *terms.pop().unwrap();

                self.clause_clauses.push((head, body));
            }
            head @ Term::Constant(_, Constant::Atom(..)) | head @ Term::Clause(..) => {
                let body =
                    Term::Constant(Cell::default(), Constant::Atom(clause_name!("true"), None));

                self.clause_clauses.push((head, body));
            }
            _ => {
                return Err(CompilationError::InadmissibleFact);
            }
        }

        Ok(())
    }

    fn add_extensible_predicate_declaration(
        &mut self,
        compilation_target: CompilationTarget,
        name: ClauseName,
        arity: usize,
        flag_accessor: impl Fn(&mut LocalPredicateSkeleton) -> &mut bool,
        retraction_fn: impl Fn(CompilationTarget, PredicateKey) -> RetractionRecord,
    ) -> Result<(), SessionError> {
        let key = (name, arity);
        let mut throw_permission_error = false;

        match &compilation_target {
            CompilationTarget::User => {
                match self
                    .load_state
                    .wam
                    .indices
                    .extensible_predicates
                    .get_mut(&key)
                {
                    Some(skeleton) => {
                        if !*flag_accessor(&mut skeleton.core) {
                            *flag_accessor(&mut skeleton.core) = true;

                            self.load_state.retraction_info.push_record(retraction_fn(
                                compilation_target.clone(),
                                key.clone(),
                            ));
                        }
                    }
                    None => {
                        if self.load_state.compilation_target == compilation_target {
                            let mut skeleton = PredicateSkeleton::new();
                            *flag_accessor(&mut skeleton.core) = true;

                            self.load_state.add_extensible_predicate(
                                key.clone(),
                                skeleton,
                                CompilationTarget::User,
                            );
                        } else {
                            throw_permission_error = true;
                        }
                    }
                }
            }
            CompilationTarget::Module(ref module_name) => {
                match self.load_state.wam.indices.modules.get_mut(module_name) {
                    Some(ref mut module) => match module.extensible_predicates.get_mut(&key) {
                        Some(ref mut skeleton) => {
                            if !*flag_accessor(&mut skeleton.core) {
                                *flag_accessor(&mut skeleton.core) = true;

                                self.load_state.retraction_info.push_record(retraction_fn(
                                    compilation_target.clone(),
                                    key.clone(),
                                ));
                            }
                        }
                        None => {
                            if self.load_state.compilation_target == compilation_target {
                                let mut skeleton = PredicateSkeleton::new();
                                *flag_accessor(&mut skeleton.core) = true;

                                self.load_state.add_extensible_predicate(
                                    key.clone(),
                                    skeleton,
                                    compilation_target.clone(),
                                );
                            } else {
                                throw_permission_error = true;
                            }
                        }
                    },
                    None => {
                        self.load_state
                            .add_dynamically_generated_module(module_name);

                        let mut skeleton = PredicateSkeleton::new();
                        *flag_accessor(&mut skeleton.core) = true;

                        self.load_state.add_extensible_predicate(
                            key.clone(),
                            skeleton,
                            compilation_target.clone(),
                        );
                    }
                }
            }
        }

        if !throw_permission_error {
            match self.load_state.compilation_target.clone() {
                CompilationTarget::User => {
                    match self
                        .load_state
                        .wam
                        .indices
                        .get_local_predicate_skeleton_mut(
                            self.load_state.compilation_target.clone(),
                            compilation_target.clone(),
                            self.load_state.listing_src_file_name(),
                            key.clone(),
                        ) {
                        Some(skeleton) => {
                            if !*flag_accessor(skeleton) {
                                *flag_accessor(skeleton) = true;
                            }
                        }
                        None => {
                            let mut skeleton = LocalPredicateSkeleton::new();
                            *flag_accessor(&mut skeleton) = true;

                            self.load_state.add_local_extensible_predicate(
                                compilation_target.clone(),
                                key.clone(),
                                skeleton,
                            );
                        }
                    }
                }
                CompilationTarget::Module(ref module_name) => {
                    match self.load_state.wam.indices.modules.get_mut(module_name) {
                        Some(module) => match module
                            .local_extensible_predicates
                            .get_mut(&(compilation_target.clone(), key.clone()))
                        {
                            Some(skeleton) => {
                                if !*flag_accessor(skeleton) {
                                    *flag_accessor(skeleton) = true;
                                }
                            }
                            None => {
                                let mut skeleton = LocalPredicateSkeleton::new();
                                *flag_accessor(&mut skeleton) = true;

                                self.load_state.add_local_extensible_predicate(
                                    compilation_target.clone(),
                                    key.clone(),
                                    skeleton,
                                );
                            }
                        },
                        None => {
                            self.load_state
                                .add_dynamically_generated_module(module_name);

                            let mut skeleton = LocalPredicateSkeleton::new();
                            *flag_accessor(&mut skeleton) = true;

                            self.load_state.add_local_extensible_predicate(
                                compilation_target.clone(),
                                key.clone(),
                                skeleton,
                            );
                        }
                    }
                }
            }

            self.fail_on_undefined(&compilation_target, key);

            Ok(())
        } else {
            Err(SessionError::PredicateNotMultifileOrDiscontiguous(
                compilation_target,
                key,
            ))
        }
    }

    fn fail_on_undefined(&mut self, compilation_target: &CompilationTarget, key: PredicateKey) {
        /*
         * DynamicUndefined isn't only applied to dynamic predicates
         * but to multifile and discontiguous predicates as well.
         */

        let code_index = self
            .load_state
            .get_or_insert_code_index(key.clone(), compilation_target.clone());

        if let IndexPtr::Undefined = code_index.get() {
            set_code_index(
                &mut self.load_state.retraction_info,
                compilation_target,
                key,
                &code_index,
                IndexPtr::DynamicUndefined,
            );
        }
    }

    fn add_discontiguous_predicate(
        &mut self,
        compilation_target: CompilationTarget,
        name: ClauseName,
        arity: usize,
    ) -> Result<(), SessionError> {
        self.add_extensible_predicate_declaration(
            compilation_target,
            name,
            arity,
            |skeleton| &mut skeleton.is_discontiguous,
            RetractionRecord::AddedDiscontiguousPredicate,
        )
    }

    fn add_dynamic_predicate(
        &mut self,
        compilation_target: CompilationTarget,
        name: ClauseName,
        arity: usize,
    ) -> Result<(), SessionError> {
        self.add_extensible_predicate_declaration(
            compilation_target.clone(),
            name.clone(),
            arity,
            |skeleton| &mut skeleton.is_dynamic,
            RetractionRecord::AddedDynamicPredicate,
        )
    }

    fn add_multifile_predicate(
        &mut self,
        compilation_target: CompilationTarget,
        name: ClauseName,
        arity: usize,
    ) -> Result<(), SessionError> {
        self.add_extensible_predicate_declaration(
            compilation_target,
            name,
            arity,
            |skeleton| &mut skeleton.is_multifile,
            RetractionRecord::AddedMultifilePredicate,
        )
    }

    fn add_clause_clause_if_dynamic(&mut self, term: &Term) -> Result<(), SessionError> {
        if let Some(predicate_name) = ClauseInfo::name(term) {
            let arity = ClauseInfo::arity(term);

            let is_dynamic = self
                .load_state
                .wam
                .indices
                .get_predicate_skeleton(
                    &self.predicates.compilation_target,
                    &(predicate_name, arity),
                )
                .map(|skeleton| skeleton.core.is_dynamic)
                .unwrap_or(false);

            if is_dynamic {
                self.add_clause_clause(term.clone())?;
            }
        }

        Ok(())
    }

    pub(super) fn retract_local_clauses(&mut self, key: &PredicateKey, is_dynamic: bool) {
        let clause_locs = match self
            .load_state
            .wam
            .indices
            .get_local_predicate_skeleton_mut(
                self.load_state.compilation_target.clone(),
                self.predicates.compilation_target.clone(),
                self.load_state.listing_src_file_name(),
                key.clone(),
            ) {
            Some(skeleton) if !skeleton.clause_clause_locs.is_empty() => {
                mem::replace(&mut skeleton.clause_clause_locs, sdeq![])
            }
            _ => return,
        };

        self.load_state.retraction_info.push_record(
            RetractionRecord::RemovedLocalSkeletonClauseLocations(
                self.load_state.compilation_target.clone(),
                self.predicates.compilation_target.clone(),
                key.clone(),
                clause_locs.clone(),
            ),
        );

        self.load_state.retract_local_clauses(
            self.predicates.compilation_target.clone(),
            key.clone(),
            &clause_locs,
        );

        if is_dynamic {
            let clause_clause_compilation_target = match &self.predicates.compilation_target {
                CompilationTarget::User => CompilationTarget::Module(clause_name!("builtins")),
                module_name => module_name.clone(),
            };

            self.load_state
                .retract_local_clause_clauses(clause_clause_compilation_target, &clause_locs);
        }
    }
}

impl Machine {
    pub(crate) fn use_module(&mut self) {
        let subevacuable_addr = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[temp_v!(2)]));

        let module_src = ModuleSource::Library(match subevacuable_addr {
            Addr::LoadStatePayload(payload) => match &self.machine_st.heap[payload] {
                HeapCellValue::LoadStatePayload(payload) => match &payload.compilation_target {
                    CompilationTarget::Module(ref module_name) => module_name.clone(),
                    CompilationTarget::User => {
                        return;
                    }
                },
                _ => {
                    unreachable!()
                }
            },
            _ => {
                unreachable!()
            }
        });

        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(1));

        let use_module = || {
            let export_list = loader.extract_module_export_list_from_heap(temp_v!(3))?;

            if export_list.is_empty() {
                loader.load_state.use_module(module_src)?;
            } else {
                loader
                    .load_state
                    .use_qualified_module(module_src, export_list)?;
            }

            LiveTermStream::evacuate(loader)
        };

        let result = use_module();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn load_compiled_library(&mut self) {
        let library = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        if let Some(module) = self.indices.modules.get(&library) {
            if let ListingSource::DynamicallyGenerated = module.listing_src {
                self.machine_st.fail = true;
                return;
            }

            let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(3));

            let import_module = || {
                let export_list = loader.extract_module_export_list_from_heap(temp_v!(2))?;

                if export_list.is_empty() {
                    loader.load_state.import_module(library)?;
                } else {
                    loader
                        .load_state
                        .import_qualified_module(library, export_list)?;
                }

                LiveTermStream::evacuate(loader)
            };

            let result = import_module();
            self.restore_load_state_payload(result, evacuable_h);
        } else {
            self.machine_st.fail = true;
        }
    }

    pub(crate) fn declare_module(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        // let export_list = self.machine_st.extract_module_export_list(temp_v!(2));
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(3));

        let declare_module = || {
            // let export_list = export_list?;
            let exports = loader.extract_module_export_list_from_heap(temp_v!(2))?;

            let module_decl = ModuleDecl {
                name: module_name,
                exports: exports.into_iter().collect(),
            };

            loader.load_decl(Declaration::Module(module_decl))?;
            LiveTermStream::evacuate(loader)
        };

        let result = declare_module();
        self.restore_load_state_payload(result, evacuable_h);
    }

    #[inline]
    pub(crate) fn add_discontiguous_predicate(&mut self) {
        self.add_extensible_predicate_declaration(
            |loader, compilation_target, clause_name, arity| {
                loader.add_discontiguous_predicate(compilation_target, clause_name, arity)
            },
        );
    }

    #[inline]
    pub(crate) fn add_dynamic_predicate(&mut self) {
        self.add_extensible_predicate_declaration(
            |loader, compilation_target, clause_name, arity| {
                loader.add_dynamic_predicate(compilation_target, clause_name, arity)
            },
        );
    }

    #[inline]
    pub(crate) fn add_multifile_predicate(&mut self) {
        self.add_extensible_predicate_declaration(
            |loader, compilation_target, clause_name, arity| {
                loader.add_multifile_predicate(compilation_target, clause_name, arity)
            },
        );
    }

    fn add_extensible_predicate_declaration(
        &mut self,
        decl_adder: impl Fn(
            &mut Loader<LiveTermStream>,
            CompilationTarget,
            ClauseName,
            usize,
        ) -> Result<(), SessionError>,
    ) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let predicate_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(2)]))
        );

        let arity = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[temp_v!(3)]));

        let arity = match Number::try_from((arity, &self.machine_st.heap)) {
            Ok(Number::Integer(n)) if &*n >= &0 && &*n <= &MAX_ARITY => Ok(n.to_usize().unwrap()),
            Ok(Number::Fixnum(n)) if n >= 0 && n <= MAX_ARITY as isize => {
                Ok(usize::try_from(n).unwrap())
            }
            _ => Err(SessionError::from(CompilationError::InvalidRuleHead)),
        };

        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(4));

        let add_predicate_decl = || {
            decl_adder(&mut loader, compilation_target, predicate_name, arity?)?;
            LiveTermStream::evacuate(loader)
        };

        let result = add_predicate_decl();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn add_term_expansion_clause(&mut self) {
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(2));

        let add_clause = || {
            let term = loader.read_term_from_heap(temp_v!(1))?;

            loader.load_state.incremental_compile_clause(
                (clause_name!("term_expansion"), 2),
                term,
                CompilationTarget::User,
                false,
                AppendOrPrepend::Append,
            )?;

            LiveTermStream::evacuate(loader)
        };

        let result = add_clause();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn add_goal_expansion_clause(&mut self) {
        let target_module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(3));

        let compilation_target = match target_module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(target_module_name),
        };

        let add_clause = || {
            let term = loader.read_term_from_heap(temp_v!(2))?;

            loader.load_state.incremental_compile_clause(
                (clause_name!("goal_expansion"), 2),
                term,
                compilation_target,
                false, // backtracking inferences are counted by call_with_inference_limit.
                AppendOrPrepend::Append,
            )?;

            LiveTermStream::evacuate(loader)
        };

        let result = add_clause();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn add_in_situ_filename_module(&mut self) {
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(1));

        let add_in_situ_filename_module = || {
            if let Some(filename) = loader.load_state.listing_src_file_name() {
                let module_decl = ModuleDecl {
                    name: filename,
                    exports: vec![],
                };

                let module_name = module_decl.name.clone();

                if !loader
                    .load_state
                    .wam
                    .indices
                    .modules
                    .contains_key(&module_decl.name)
                {
                    let module = Module::new_in_situ(module_decl);
                    loader
                        .load_state
                        .wam
                        .indices
                        .modules
                        .insert(module_name, module);
                } else {
                    loader.load_state.reset_in_situ_module(
                        module_decl.clone(),
                        &ListingSource::DynamicallyGenerated,
                    );

                    match loader.load_state.wam.indices.modules.get_mut(&module_name) {
                        Some(module) => {
                            for (key, value) in module.op_dir.drain(0..) {
                                let (prec, spec) = value.shared_op_desc().get();
                                let mut op_decl = OpDecl::new(prec, spec, key.0);

                                op_decl.remove(&mut loader.load_state.wam.indices.op_dir);
                            }
                        }
                        None => {}
                    }
                }
            }

            LiveTermStream::evacuate(loader)
        };

        let result = add_in_situ_filename_module();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn loader_from_heap_evacuable(
        &mut self,
        r: RegType,
    ) -> (Loader<LiveTermStream>, usize) {
        let (load_state_payload, evacuable_h) = match self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[r]))
        {
            Addr::LoadStatePayload(h) => (
                mem::replace(
                    &mut self.machine_st.heap[h],
                    HeapCellValue::Addr(Addr::EmptyList),
                ),
                h,
            ),
            _ => {
                unreachable!()
            }
        };

        match load_state_payload {
            HeapCellValue::LoadStatePayload(payload) => {
                (Loader::from_load_state_payload(self, payload), evacuable_h)
            }
            _ => {
                unreachable!()
            }
        }
    }

    #[inline]
    pub(crate) fn push_load_state_payload(&mut self) {
        let payload = Box::new(LoadStatePayload::new(self));
        let addr = Addr::LoadStatePayload(
            self.machine_st
                .heap
                .push(HeapCellValue::LoadStatePayload(payload)),
        );

        self.machine_st
            .bind(self.machine_st[temp_v!(1)].as_var().unwrap(), addr);
    }

    #[inline]
    pub(crate) fn pop_load_state_payload(&mut self) {
        let load_state_payload = match self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        {
            Addr::LoadStatePayload(h) => mem::replace(
                &mut self.machine_st.heap[h],
                HeapCellValue::Addr(Addr::EmptyList),
            ),
            _ => {
                unreachable!()
            }
        };

        match load_state_payload {
            HeapCellValue::LoadStatePayload(payload) => {
                Loader::from_load_state_payload(self, payload);
            }
            _ => {
                // unlike in loader_from_heap_evacuable,
                // pop_load_state_payload is allowed to fail to find a
                // LoadStatePayload in the heap, as a Rust-side
                // top-level command may have failed to write the
                // load state payload back to the heap.
            }
        }
    }

    #[inline]
    pub(crate) fn pop_load_context(&mut self) {
        self.load_contexts.pop();
    }

    pub(crate) fn push_load_context(&mut self) {
        let stream = try_or_fail!(
            self.machine_st,
            self.machine_st.get_stream_or_alias(
                self.machine_st[temp_v!(1)],
                &self.indices.stream_aliases,
                "$push_load_context",
                2,
            )
        );

        let path = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(2)]))
        );

        self.load_contexts
            .push(LoadContext::new(path.as_str(), stream));
    }

    pub(crate) fn restore_load_state_payload(
        &mut self,
        result: Result<LoadStatePayload, SessionError>,
        evacuable_h: usize,
    ) {
        match result {
            Ok(payload) => {
                self.machine_st.heap[evacuable_h] =
                    HeapCellValue::LoadStatePayload(Box::new(payload));
            }
            Err(e) => {
                self.throw_session_error(e, (clause_name!("load"), 1));
            }
        }
    }

    pub(crate) fn scoped_clause_to_evacuable(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let (loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(3));

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let result = loader.read_and_enqueue_term(temp_v!(2), compilation_target);
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn clause_to_evacuable(&mut self) {
        let (loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(2));
        let compilation_target = loader.load_state.compilation_target.clone();

        let result = loader.read_and_enqueue_term(temp_v!(1), compilation_target);
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn conclude_load(&mut self) {
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(1));

        let compile_final_terms = || {
            if !loader.predicates.is_empty() {
                loader.compile_and_submit()?;
            }

            loader.load_state.remove_module_op_exports();
            LiveTermStream::evacuate(loader)
        };

        let result = compile_final_terms();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn load_context_source(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            let path_str = load_context.path.to_str().unwrap();
            let path_atom = clause_name!(path_str.to_string(), self.machine_st.atom_tbl);

            let path_addr = Addr::Con(
                self.machine_st
                    .heap
                    .push(HeapCellValue::Atom(path_atom, None)),
            );

            self.machine_st
                .unify(path_addr, self.machine_st[temp_v!(1)]);
        } else {
            self.machine_st.fail = true;
        }
    }

    pub(crate) fn load_context_file(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            match load_context.path.file_name() {
                Some(file_name) if load_context.path.is_file() => {
                    let file_name_str = file_name.to_str().unwrap();
                    let file_name_atom =
                        clause_name!(file_name_str.to_string(), self.machine_st.atom_tbl);

                    let file_name_addr = Addr::Con(
                        self.machine_st
                            .heap
                            .push(HeapCellValue::Atom(file_name_atom, None)),
                    );

                    self.machine_st
                        .unify(file_name_addr, self.machine_st[temp_v!(1)]);
                    return;
                }
                _ => {
                    return self.load_context_module();
                }
            }
        }

        self.machine_st.fail = true;
    }

    pub(crate) fn load_context_directory(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            if let Some(directory) = load_context.path.parent() {
                let directory_str = directory.to_str().unwrap();

                let directory_atom =
                    clause_name!(directory_str.to_string(), self.machine_st.atom_tbl);

                let directory_addr = Addr::Con(
                    self.machine_st
                        .heap
                        .push(HeapCellValue::Atom(directory_atom, None)),
                );

                self.machine_st
                    .unify(directory_addr, self.machine_st[temp_v!(1)]);
                return;
            }
        }

        self.machine_st.fail = true;
    }

    pub(crate) fn load_context_module(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            let module_name_addr = Addr::Con(
                self.machine_st
                    .heap
                    .push(HeapCellValue::Atom(load_context.module.clone(), None)),
            );

            self.machine_st
                .unify(module_name_addr, self.machine_st[temp_v!(1)]);
        } else {
            self.machine_st.fail = true;
        }
    }

    pub(crate) fn load_context_stream(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            let stream_addr = Addr::Stream(
                self.machine_st
                    .heap
                    .push(HeapCellValue::Stream(load_context.stream.clone())),
            );

            self.machine_st
                .unify(stream_addr, self.machine_st[temp_v!(1)]);
        } else {
            self.machine_st.fail = true;
        }
    }

    pub(crate) fn compile_assert(&mut self, append_or_prepend: AppendOrPrepend) {
        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(3)], self.machine_st[temp_v!(4)]);

        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(5)]))
        );

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let compile_assert = || {
            let mut loader = Loader::new(LiveTermStream::new(ListingSource::User), self);

            loader.load_state.compilation_target = compilation_target.clone();

            let head = loader.read_term_from_heap(temp_v!(1))?;
            let body = loader.read_term_from_heap(temp_v!(2))?;

            let asserted_clause = Term::Clause(
                Cell::default(),
                clause_name!(":-"),
                vec![Box::new(head.clone()), Box::new(body.clone())],
                fetch_op_spec(clause_name!(":-"), 2, &loader.load_state.wam.indices.op_dir),
            );

            // if a new predicate was just created, make it dynamic.
            loader.add_dynamic_predicate(compilation_target.clone(), key.0.clone(), key.1)?;

            loader.load_state.incremental_compile_clause(
                key.clone(),
                asserted_clause,
                compilation_target.clone(),
                false,
                append_or_prepend,
            )?;

            // the global clock is incremented after each assertion.
            loader.load_state.wam.machine_st.global_clock += 1;

            loader.compile_clause_clauses(
                key,
                compilation_target,
                std::iter::once((head, body)),
                append_or_prepend,
            )?;

            LiveTermStream::evacuate(loader)
        };

        match compile_assert() {
            Ok(_) => {}
            Err(e) => {
                let error_pi = match append_or_prepend {
                    AppendOrPrepend::Append => (clause_name!("assertz"), 1),
                    AppendOrPrepend::Prepend => (clause_name!("asserta"), 1),
                };

                self.throw_session_error(e, error_pi);
            }
        }
    }

    pub(crate) fn abolish_clause(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let abolish_clause = || {
            let mut loader = Loader::new(LiveTermStream::new(ListingSource::User), self);
            loader.load_state.compilation_target = compilation_target;

            let clause_clause_compilation_target = match &loader.load_state.compilation_target {
                CompilationTarget::User => CompilationTarget::Module(clause_name!("builtins")),
                module => module.clone(),
            };

            let mut clause_clause_target_poses: Vec<_> = loader
                .load_state
                .wam
                .indices
                .get_predicate_skeleton(&loader.load_state.compilation_target, &key)
                .map(|skeleton| {
                    loader
                        .load_state
                        .wam
                        .indices
                        .get_predicate_skeleton(
                            &clause_clause_compilation_target,
                            &(clause_name!("$clause"), 2),
                        )
                        .map(|clause_clause_skeleton| {
                            skeleton
                                .core
                                .clause_clause_locs
                                .iter()
                                .map(|clause_clause_loc| {
                                    clause_clause_skeleton
                                        .target_pos_of_clause_clause_loc(*clause_clause_loc)
                                        .unwrap()
                                })
                                .collect()
                        })
                        .unwrap()
                })
                .unwrap();

            loader
                .load_state
                .wam
                .indices
                .get_predicate_skeleton_mut(&loader.load_state.compilation_target, &key)
                .map(|skeleton| skeleton.reset());

            let code_index = loader
                .load_state
                .get_or_insert_code_index(key, loader.load_state.compilation_target.clone());

            code_index.set(IndexPtr::DynamicUndefined);

            loader.load_state.compilation_target = clause_clause_compilation_target;

            while let Some(target_pos) = clause_clause_target_poses.pop() {
                loader
                    .load_state
                    .retract_clause((clause_name!("$clause"), 2), target_pos);
            }

            LiveTermStream::evacuate(loader)
        };

        match abolish_clause() {
            Ok(_) => {}
            Err(e) => {
                self.throw_session_error(e, (clause_name!("abolish"), 1));
            }
        }
    }

    pub(crate) fn retract_clause(&mut self) {
        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(1)], self.machine_st[temp_v!(2)]);

        let target_pos = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[temp_v!(3)]));

        let target_pos = match Number::try_from((target_pos, &self.machine_st.heap)) {
            Ok(Number::Integer(n)) => n.to_usize().unwrap(),
            Ok(Number::Fixnum(n)) => usize::try_from(n).unwrap(),
            _ => unreachable!(),
        };

        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(4)]))
        );

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let clause_clause_compilation_target = match &compilation_target {
            CompilationTarget::User => CompilationTarget::Module(clause_name!("builtins")),
            _ => compilation_target.clone(),
        };

        let retract_clause = || {
            let mut loader = Loader::new(LiveTermStream::new(ListingSource::User), self);
            loader.load_state.compilation_target = compilation_target;

            let clause_clause_loc = loader.load_state.retract_dynamic_clause(key, target_pos);

            // the global clock is incremented after each retraction.
            loader.load_state.wam.machine_st.global_clock += 1;

            let target_pos = match loader.load_state.wam.indices.get_predicate_skeleton(
                &clause_clause_compilation_target,
                &(clause_name!("$clause"), 2),
            ) {
                Some(skeleton) => skeleton
                    .target_pos_of_clause_clause_loc(clause_clause_loc)
                    .unwrap(),
                None => {
                    unreachable!();
                }
            };

            loader.load_state.compilation_target = clause_clause_compilation_target;
            loader
                .load_state
                .retract_clause((clause_name!("$clause"), 2), target_pos);

            LiveTermStream::evacuate(loader)
        };

        match retract_clause() {
            Ok(_) => {}
            Err(e) => {
                self.throw_session_error(e, (clause_name!("retract"), 1));
            }
        }
    }

    pub(crate) fn is_consistent_with_term_queue(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let (loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(4));

        loader.load_state.wam.machine_st.fail = (!loader.predicates.is_empty()
            && loader.predicates.compilation_target != compilation_target)
            || !key.is_consistent(&loader.predicates);

        let result = LiveTermStream::evacuate(loader);
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn flush_term_queue(&mut self) {
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(1));

        let flush_term_queue = || {
            if !loader.predicates.is_empty() {
                loader.compile_and_submit()?;
            }

            LiveTermStream::evacuate(loader)
        };

        let result = flush_term_queue();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn remove_module_exports(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(2));

        let remove_module_exports = || {
            loader.load_state.remove_module_exports(module_name);
            LiveTermStream::evacuate(loader)
        };

        let result = remove_module_exports();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn add_non_counted_backtracking(&mut self) {
        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(1)], self.machine_st[temp_v!(2)]);

        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(3));
        loader.non_counted_bt_preds.insert(key);

        let result = LiveTermStream::evacuate(loader);
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn meta_predicate_property(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let (predicate_name, arity) = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        match self
            .indices
            .get_meta_predicate_spec(predicate_name, arity, &compilation_target)
        {
            Some(meta_specs) => {
                let list_loc = self
                    .machine_st
                    .heap
                    .to_list(meta_specs.iter().map(|meta_spec| match meta_spec {
                        MetaSpec::Minus => HeapCellValue::Atom(clause_name!("+"), None),
                        MetaSpec::Plus => HeapCellValue::Atom(clause_name!("-"), None),
                        MetaSpec::Either => HeapCellValue::Atom(clause_name!("?"), None),
                        MetaSpec::RequiresExpansionWithArgument(ref arg_num) => {
                            HeapCellValue::Addr(Addr::Usize(*arg_num))
                        }
                    }));

                let heap_loc = self.machine_st.heap.push(HeapCellValue::NamedStr(
                    1,
                    clause_name!("meta_predicate"),
                    None,
                ));

                self.machine_st
                    .heap
                    .push(HeapCellValue::Addr(Addr::HeapCell(list_loc)));

                self.machine_st
                    .unify(Addr::HeapCell(heap_loc), self.machine_st[temp_v!(4)]);
            }
            None => {
                self.machine_st.fail = true;
            }
        }
    }

    pub(crate) fn dynamic_property(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        match self
            .indices
            .get_predicate_skeleton(&compilation_target, &key)
        {
            Some(skeleton) => {
                self.machine_st.fail = !skeleton.core.is_dynamic;
            }
            None => {
                self.machine_st.fail = true;
            }
        }
    }

    pub(crate) fn multifile_property(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        match self
            .indices
            .get_predicate_skeleton(&compilation_target, &key)
        {
            Some(skeleton) => {
                self.machine_st.fail = !skeleton.core.is_multifile;
            }
            None => {
                self.machine_st.fail = true;
            }
        }
    }

    pub(crate) fn discontiguous_property(&mut self) {
        let module_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name.as_str() {
            "user" => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        match self
            .indices
            .get_predicate_skeleton(&compilation_target, &key)
        {
            Some(skeleton) => {
                self.machine_st.fail = !skeleton.core.is_discontiguous;
            }
            None => {
                self.machine_st.fail = true;
            }
        }
    }

    pub(crate) fn builtin_property(&mut self) {
        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(1)], self.machine_st[temp_v!(2)]);

        match ClauseType::from(key.0, key.1, None) {
            ClauseType::BuiltIn(_) | ClauseType::Inlined(..) | ClauseType::CallN => {
                return;
            }
            ClauseType::Named(ref name, arity, _) => {
                if let Some(module) = self.indices.modules.get(&(clause_name!("builtins"))) {
                    self.machine_st.fail = !module.code_dir.contains_key(&(name.clone(), arity));

                    return;
                }
            }
            ClauseType::Op(ref name, ref op_desc, _) => {
                if let Some(module) = self.indices.modules.get(&(clause_name!("builtins"))) {
                    self.machine_st.fail = !module
                        .code_dir
                        .contains_key(&(name.clone(), op_desc.arity()));

                    return;
                }
            }
            _ => {}
        }

        self.machine_st.fail = true;
    }
}

impl<'a> Loader<'a, LiveTermStream> {
    pub(super) fn to_load_state_payload(mut self) -> LoadStatePayload {
        LoadStatePayload {
            term_stream: mem::replace(
                &mut self.term_stream,
                LiveTermStream::new(ListingSource::User),
            ),
            non_counted_bt_preds: mem::replace(&mut self.non_counted_bt_preds, IndexSet::new()),
            compilation_target: self.load_state.compilation_target.take(),
            retraction_info: mem::replace(
                &mut self.load_state.retraction_info,
                RetractionInfo::new(self.load_state.wam.code_repo.code.len()),
            ),
            predicates: self.predicates.take(),
            clause_clauses: mem::replace(&mut self.clause_clauses, vec![]),
            module_op_exports: mem::replace(&mut self.load_state.module_op_exports, vec![]),
        }
    }

    pub(super) fn from_load_state_payload(
        wam: &'a mut Machine,
        mut payload: Box<LoadStatePayload>,
    ) -> Self {
        Loader {
            term_stream: mem::replace(
                &mut payload.term_stream,
                LiveTermStream::new(ListingSource::User),
            ),
            non_counted_bt_preds: mem::replace(&mut payload.non_counted_bt_preds, IndexSet::new()),
            clause_clauses: mem::replace(&mut payload.clause_clauses, vec![]),
            predicates: payload.predicates.take(),
            load_state: LoadState {
                compilation_target: payload.compilation_target.take(),
                module_op_exports: mem::replace(&mut payload.module_op_exports, vec![]),
                retraction_info: mem::replace(&mut payload.retraction_info, RetractionInfo::new(0)),
                wam,
            },
        }
    }

    fn read_and_enqueue_term(
        mut self,
        term_reg: RegType,
        compilation_target: CompilationTarget,
    ) -> Result<LoadStatePayload, SessionError> {
        if self.predicates.compilation_target != compilation_target {
            if !self.predicates.is_empty() {
                self.compile_and_submit()?;
            }

            self.predicates.compilation_target = compilation_target;
        }

        let term = self.read_term_from_heap(term_reg)?;

        self.add_clause_clause_if_dynamic(&term)?;
        self.term_stream.term_queue.push_back(term);

        self.load()
    }
}

#[inline]
pub(super) fn load_module(
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicate_dir: &mut MetaPredicateDir,
    compilation_target: &CompilationTarget,
    module: &Module,
) {
    import_module_exports(
        &mut RetractionInfo::new(0),
        &compilation_target,
        module,
        code_dir,
        op_dir,
        meta_predicate_dir,
    )
    .unwrap();
}
