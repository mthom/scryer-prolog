use crate::arena::*;
use crate::atom_table::*;
use crate::forms::*;
use crate::heap_iter::*;
use crate::indexing::*;
use crate::instructions::*;
use crate::machine::load_state::*;
use crate::machine::machine_errors::*;
use crate::machine::machine_indices::*;
use crate::machine::preprocessor::*;
use crate::machine::term_stream::*;
use crate::machine::*;
use crate::parser::ast::*;
use crate::types::*;

use indexmap::IndexSet;

use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt;
use std::ops::{Deref, DerefMut};

impl TermWriteResult {
    pub(super) fn from(heap: &mut Heap, value: HeapCellValue) -> Result<Self, usize> {
        let focus = heap.index_of(value)?;
        let mut stack = Stack::uninitialized();

        heap[0] = value;

        let inverse_var_locs = inverse_var_locs_from_iter(
            stackful_preorder_iter::<NonListElider>(
                heap,
                &mut stack,
                0,
            ),
        );

        Ok(Self { focus, inverse_var_locs })
    }
}

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
 * and verifying certain kinds of declarations.
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
    AddedMetaPredicate(Atom, PredicateKey),
    ReplacedMetaPredicate(Atom, Atom, Vec<MetaSpec>),
    AddedModule(Atom),
    ReplacedModule(ModuleDecl, ListingSource, LocalExtensiblePredicates),
    AddedModuleOp(Atom, OpDecl),
    ReplacedModuleOp(Atom, OpDecl, OpDesc),
    AddedModulePredicate(Atom, PredicateKey),
    ReplacedModulePredicate(Atom, PredicateKey, IndexPtr),
    AddedDiscontiguousPredicate(CompilationTarget, PredicateKey),
    AddedDynamicPredicate(CompilationTarget, PredicateKey),
    AddedMultifilePredicate(CompilationTarget, PredicateKey),
    AddedUserOp(OpDecl),
    ReplacedUserOp(OpDecl, OpDesc),
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
    RemovedDynamicSkeletonClause(CompilationTarget, PredicateKey, usize, usize),
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
        VecDeque<usize>,
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
            records: vec![],
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
            records: std::mem::take(&mut self.records),
        }
    }
}

impl<'a, LS: LoadState<'a>> Drop for Loader<'a, LS> {
    fn drop(&mut self) {
        if LS::should_drop_load_state(self) {
            LS::reset_machine(self);
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
pub enum CompilationTarget {
    Module(Atom),
    #[default]
    User,
}

impl fmt::Display for CompilationTarget {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CompilationTarget::User => write!(f, "user"),
            CompilationTarget::Module(ref module_name) => write!(f, "{}", module_name.as_str()),
        }
    }
}

impl CompilationTarget {
    #[inline]
    pub(crate) fn module_name(&self) -> Atom {
        match self {
            CompilationTarget::User => {
                atom!("user")
            }
            CompilationTarget::Module(module_name) => *module_name,
        }
    }
}

pub struct PredicateQueue {
    pub predicates: Vec<TermWriteResult>,
    pub compilation_target: CompilationTarget,
}

impl PredicateQueue {
    #[inline]
    pub(super) fn push(&mut self, term_write_result: TermWriteResult) {
        self.predicates.push(term_write_result);
    }

    #[inline]
    pub(crate) fn first(&self) -> Option<&TermWriteResult> {
        self.predicates.first()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }

    #[inline]
    pub(super) fn take(&mut self) -> Self {
        Self {
            predicates: std::mem::take(&mut self.predicates),
            compilation_target: self.compilation_target,
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

pub type LiveLoadState = LoadStatePayload<LiveTermStream>;

pub struct BootstrappingLoadState<'a>(pub LoadStatePayload<BootstrappingTermStream<'a>>);

impl<'a> Deref for BootstrappingLoadState<'a> {
    type Target = LoadStatePayload<BootstrappingTermStream<'a>>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> DerefMut for BootstrappingLoadState<'a> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub trait LoadState<'a>: Sized {
    type Evacuable;
    type TS: TermStream;
    type LoaderFieldType: DerefMut<Target = LoadStatePayload<Self::TS>>;

    fn new(
        machine_st: &'a mut MachineState,
        payload: LoadStatePayload<Self::TS>,
    ) -> Self::LoaderFieldType;
    fn evacuate(loader: Loader<'a, Self>) -> Result<Self::Evacuable, SessionError>;
    fn should_drop_load_state(loader: &Loader<'a, Self>) -> bool;
    fn reset_machine(loader: &mut Loader<'a, Self>);
    fn machine_st(loader: &mut Self::LoaderFieldType) -> &mut MachineState;
    fn err_on_builtin_overwrite(
        loader: &Loader<'a, Self>,
        key: PredicateKey,
    ) -> Result<(), SessionError>;

    fn err_on_builtin_module_overwrite(_module_name: Atom) -> Result<(), SessionError> {
        Ok(())
    }
}

pub struct LiveLoadAndMachineState<'a> {
    load_state: TypedArenaPtr<LiveLoadState>,
    machine_st: &'a mut MachineState,
}

impl<'a> Deref for LiveLoadAndMachineState<'a> {
    type Target = LiveLoadState;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.load_state
    }
}

impl<'a> DerefMut for LiveLoadAndMachineState<'a> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.load_state
    }
}

impl<'a> LoadState<'a> for LiveLoadAndMachineState<'a> {
    type TS = LiveTermStream;
    type LoaderFieldType = LiveLoadAndMachineState<'a>;
    type Evacuable = TypedArenaPtr<LiveLoadState>;

    #[inline(always)]
    fn new(
        machine_st: &'a mut MachineState,
        payload: LoadStatePayload<Self::TS>,
    ) -> Self::LoaderFieldType {
        let load_state = arena_alloc!(payload, &mut machine_st.arena);
        LiveLoadAndMachineState {
            load_state,
            machine_st,
        }
    }

    #[inline(always)]
    fn evacuate(mut loader: Loader<'a, Self>) -> Result<Self::Evacuable, SessionError> {
        if loader.payload.load_state.get_tag() != ArenaHeaderTag::Dropped {
            loader
                .payload
                .load_state
                .set_tag(ArenaHeaderTag::InactiveLoadState);
            Ok(loader.payload.load_state)
        } else {
            unreachable!("we never evacuate after dropping")
        }
    }

    #[inline(always)]
    fn should_drop_load_state(loader: &Loader<'a, Self>) -> bool {
        loader.payload.load_state.get_tag() == ArenaHeaderTag::LiveLoadState
    }

    #[inline(always)]
    fn reset_machine(loader: &mut Loader<'a, Self>) {
        if loader.payload.load_state.get_tag() != ArenaHeaderTag::Dropped {
            loader.reset_machine();
            loader.payload.load_state.drop_payload();
        }
    }

    #[inline(always)]
    fn machine_st(loader: &mut Self::LoaderFieldType) -> &mut MachineState {
        loader.machine_st
    }

    #[inline(always)]
    fn err_on_builtin_overwrite(
        loader: &Loader<'a, Self>,
        key: PredicateKey,
    ) -> Result<(), SessionError> {
        if ClauseType::is_inbuilt(key.0, key.1) {
            return Err(SessionError::CannotOverwriteBuiltIn(key));
        }

        if let Some(builtins) = loader.wam_prelude.indices.modules.get(&atom!("builtins")) {
            if builtins
                .module_decl
                .exports
                .contains(&ModuleExport::PredicateKey(key))
            {
                return Err(SessionError::CannotOverwriteBuiltIn(key));
            }
        }

        Ok(())
    }

    #[inline]
    fn err_on_builtin_module_overwrite(module_name: Atom) -> Result<(), SessionError> {
        if libraries::contains(&module_name.as_str()) {
            Err(SessionError::CannotOverwriteBuiltInModule(module_name))
        } else {
            Ok(())
        }
    }
}

impl<'a> LoadState<'a> for BootstrappingLoadState<'a> {
    type TS = BootstrappingTermStream<'a>;
    type LoaderFieldType = BootstrappingLoadState<'a>;
    type Evacuable = CompilationTarget;

    #[inline(always)]
    fn new(_: &'a mut MachineState, payload: LoadStatePayload<Self::TS>) -> Self::LoaderFieldType {
        BootstrappingLoadState(payload)
    }

    fn evacuate(mut loader: Loader<'a, Self>) -> Result<Self::Evacuable, SessionError> {
        if !loader.payload.predicates.is_empty() {
            loader.compile_and_submit()?;
        }

        let repo_len = loader.wam_prelude.code.len();

        loader.payload.retraction_info.reset(repo_len);
        loader.remove_module_op_exports();

        Ok(loader.payload.compilation_target)
    }

    #[inline(always)]
    fn should_drop_load_state(_loader: &Loader<'a, Self>) -> bool {
        true
    }

    #[inline(always)]
    fn reset_machine(loader: &mut Loader<'a, Self>) {
        loader.reset_machine();
    }

    #[inline(always)]
    fn machine_st(loader: &mut Self::LoaderFieldType) -> &mut MachineState {
        loader.term_stream.lexer_parser.machine_st
    }

    #[inline(always)]
    fn err_on_builtin_overwrite(
        _loader: &Loader<'a, Self>,
        _key: PredicateKey,
    ) -> Result<(), SessionError> {
        Ok(())
    }
}

pub struct InlineLoadState<'a> {
    machine_st: &'a mut MachineState,
    pub payload: LoadStatePayload<InlineTermStream>,
}

impl<'a> Deref for InlineLoadState<'a> {
    type Target = LoadStatePayload<InlineTermStream>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.payload
    }
}

impl<'a> DerefMut for InlineLoadState<'a> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.payload
    }
}

impl<'a> LoadState<'a> for InlineLoadState<'a> {
    type TS = InlineTermStream;
    type LoaderFieldType = InlineLoadState<'a>;
    type Evacuable = ();

    #[inline(always)]
    fn new(
        machine_st: &'a mut MachineState,
        payload: LoadStatePayload<Self::TS>,
    ) -> Self::LoaderFieldType {
        InlineLoadState {
            machine_st,
            payload,
        }
    }

    fn evacuate(_loader: Loader<'a, Self>) -> Result<Self::Evacuable, SessionError> {
        Ok(())
    }

    #[inline(always)]
    fn should_drop_load_state(_loader: &Loader<'a, Self>) -> bool {
        false
    }

    #[inline(always)]
    fn reset_machine(_loader: &mut Loader<'a, Self>) {}

    #[inline(always)]
    fn machine_st(load_state: &mut Self::LoaderFieldType) -> &mut MachineState {
        load_state.machine_st
    }

    #[inline(always)]
    fn err_on_builtin_overwrite(
        _loader: &Loader<'a, Self>,
        _key: PredicateKey,
    ) -> Result<(), SessionError> {
        Ok(())
    }
}

pub struct Loader<'a, LS: LoadState<'a>> {
    pub(super) payload: LS::LoaderFieldType,
    pub(super) wam_prelude: MachinePreludeView<'a>,
}

impl<'a, LS: LoadState<'a>> Loader<'a, LS> {
    #[inline]
    pub(super) fn new(wam: &'a mut Machine, term_stream: <LS as LoadState<'a>>::TS) -> Self {
        let payload = LoadStatePayload::new(wam.code.len(), term_stream);
        let (wam_prelude, machine_st) = wam.prelude_view_and_machine_st();

        Self {
            payload: LS::new(machine_st, payload),
            wam_prelude,
        }
    }

    #[inline]
    pub(super) fn machine_heap(&mut self) -> &mut Heap {
        &mut LS::machine_st(&mut self.payload).heap
    }

    pub(crate) fn load(mut self) -> Result<LS::Evacuable, SessionError> {
        while let Some(decl) = self.dequeue_terms()? {
            self.load_decl(decl)?;
        }

        LS::evacuate(self)
    }

    fn dequeue_terms(&mut self) -> Result<Option<Declaration>, SessionError> {
        while !self.payload.term_stream.eof()? {
            let load_state = &mut self.payload;
            let compilation_target = &load_state.compilation_target;
            let composite_op_dir = self.wam_prelude.composite_op_dir(compilation_target);

            let mut term = load_state.term_stream.next(&composite_op_dir)?;
            let predicate_focus_opt = load_state.predicates.first().map(|term_write_result| {
                term_write_result.focus
            });

            let machine_st = LS::machine_st(&mut self.payload);
            let term_key_opt = clause_predicate_key(&machine_st.heap, term.focus);

            if let Some(predicate_focus) = predicate_focus_opt {
                let predicate_key_opt = clause_predicate_key(&machine_st.heap, predicate_focus);

                debug_assert!(predicate_key_opt.is_some());

                if term_key_opt != predicate_key_opt {
                    self.compile_and_submit()?;
                }
            }

            if Some((atom!(":-"), 1)) == term_key_opt {
                let machine_st = LS::machine_st(&mut self.payload);
                term.focus = term_nth_arg(&machine_st.heap, term.focus, 1).unwrap();
                return Ok(Some(setup_declaration(self, term)?));
            }

            self.payload.predicates.push(term);
        }

        Ok(None)
    }

    pub(super) fn load_decl(&mut self, decl: Declaration) -> Result<(), SessionError> {
        match decl {
            Declaration::Dynamic(name, arity) => {
                let compilation_target = self.payload.compilation_target;
                self.add_dynamic_predicate(compilation_target, name, arity)?;
            }
            Declaration::MetaPredicate(module_name, name, meta_specs) => {
                self.add_meta_predicate_record(module_name, name, meta_specs);
            }
            Declaration::Module(module_decl) => {
                let module_name = module_decl.name;

                self.payload.compilation_target = CompilationTarget::Module(module_name);
                self.payload.predicates.compilation_target = self.payload.compilation_target;

                let listing_src = self.payload.term_stream.listing_src().clone();
                self.add_module(module_decl, listing_src)?;
            }
            Declaration::NonCountedBacktracking(name, arity) => {
                self.payload.non_counted_bt_preds.insert((name, arity));
            }
            Declaration::Op(op_decl) => {
                self.add_op_decl(&op_decl);
            }
            Declaration::UseModule(module_src) => {
                self.use_module(module_src)?;
            }
            Declaration::UseQualifiedModule(module_src, exports) => {
                self.use_qualified_module(module_src, exports)?;
            }
        }

        Ok(())
    }

    fn reset_machine(&mut self) {
        while let Some(record) = self.payload.retraction_info.records.pop() {
            match record {
                RetractionRecord::AddedMetaPredicate(target_module_name, key) => {
                    match target_module_name {
                        atom!("user") => {
                            self.wam_prelude.indices.meta_predicates.swap_remove(&key);
                        }
                        _ => match self
                            .wam_prelude
                            .indices
                            .modules
                            .get_mut(&target_module_name)
                        {
                            Some(ref mut module) => {
                                module.meta_predicates.swap_remove(&key);
                            }
                            _ => {
                                unreachable!()
                            }
                        },
                    }
                }
                RetractionRecord::ReplacedMetaPredicate(target_module_name, name, meta_specs) => {
                    match target_module_name {
                        atom!("user") => {
                            self.wam_prelude
                                .indices
                                .meta_predicates
                                .insert((name, meta_specs.len()), meta_specs);
                        }
                        _ => match self
                            .wam_prelude
                            .indices
                            .modules
                            .get_mut(&target_module_name)
                        {
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
                    self.wam_prelude.indices.modules.swap_remove(&module_name);
                }
                RetractionRecord::ReplacedModule(
                    module_decl,
                    listing_src,
                    local_extensible_predicates,
                ) => match self.wam_prelude.indices.modules.get_mut(&module_decl.name) {
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
                            if let Some(skeleton) =
                                self.wam_prelude.indices.extensible_predicates.get_mut(&key)
                            {
                                skeleton.core.is_discontiguous = false;
                            }
                        }
                        CompilationTarget::Module(module_name) => {
                            if let Some(ref mut module) =
                                self.wam_prelude.indices.modules.get_mut(&module_name)
                            {
                                if let Some(skeleton) = module.extensible_predicates.get_mut(&key) {
                                    skeleton.core.is_discontiguous = false;
                                }
                            }
                        }
                    }
                }
                RetractionRecord::AddedDynamicPredicate(compilation_target, key) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            if let Some(skeleton) =
                                self.wam_prelude.indices.extensible_predicates.get_mut(&key)
                            {
                                skeleton.core.is_dynamic = false;
                            }
                        }
                        CompilationTarget::Module(module_name) => {
                            if let Some(ref mut module) =
                                self.wam_prelude.indices.modules.get_mut(&module_name)
                            {
                                if let Some(skeleton) = module.extensible_predicates.get_mut(&key) {
                                    skeleton.core.is_dynamic = false;
                                    skeleton.core.retracted_dynamic_clauses = None;
                                };
                            }
                        }
                    }
                }
                RetractionRecord::AddedMultifilePredicate(compilation_target, key) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            if let Some(skeleton) =
                                self.wam_prelude.indices.extensible_predicates.get_mut(&key)
                            {
                                skeleton.core.is_multifile = false;
                            }
                        }
                        CompilationTarget::Module(module_name) => {
                            if let Some(ref mut module) =
                                self.wam_prelude.indices.modules.get_mut(&module_name)
                            {
                                if let Some(skeleton) = module.extensible_predicates.get_mut(&key) {
                                    skeleton.core.is_multifile = false;
                                }
                            }
                        }
                    }
                }
                RetractionRecord::AddedModuleOp(module_name, mut op_decl) => {
                    if let Some(ref mut module) =
                        self.wam_prelude.indices.modules.get_mut(&module_name)
                    {
                        op_decl.remove(&mut module.op_dir);
                    }
                }
                RetractionRecord::ReplacedModuleOp(module_name, mut op_decl, op_desc) => {
                    if let Some(ref mut module) =
                        self.wam_prelude.indices.modules.get_mut(&module_name)
                    {
                        op_decl.op_desc = op_desc;
                        op_decl.insert_into_op_dir(&mut module.op_dir);
                    }
                }
                RetractionRecord::AddedModulePredicate(module_name, key) => {
                    if let Some(ref mut module) =
                        self.wam_prelude.indices.modules.get_mut(&module_name)
                    {
                        module.code_dir.swap_remove(&key);
                    }
                }
                RetractionRecord::ReplacedModulePredicate(module_name, key, old_code_idx) => {
                    if let Some(ref mut module) =
                        self.wam_prelude.indices.modules.get_mut(&module_name)
                    {
                        if let Some(code_idx) = module.code_dir.get_mut(&key) {
                            code_idx.set(old_code_idx)
                        }
                    }
                }
                RetractionRecord::AddedExtensiblePredicate(compilation_target, key) => {
                    self.wam_prelude
                        .indices
                        .remove_predicate_skeleton(&compilation_target, &key);
                }
                RetractionRecord::AddedUserOp(mut op_decl) => {
                    op_decl.remove(&mut self.wam_prelude.indices.op_dir);
                }
                RetractionRecord::ReplacedUserOp(mut op_decl, op_desc) => {
                    op_decl.op_desc = op_desc;
                    op_decl.insert_into_op_dir(&mut self.wam_prelude.indices.op_dir);
                }
                RetractionRecord::AddedUserPredicate(key) => {
                    self.wam_prelude.indices.code_dir.swap_remove(&key);
                }
                RetractionRecord::ReplacedUserPredicate(key, old_code_idx) => {
                    if let Some(code_idx) = self.wam_prelude.indices.code_dir.get_mut(&key) {
                        code_idx.set(old_code_idx)
                    }
                }
                RetractionRecord::AddedIndex(index_key, clause_loc) => {
                    if let Some(index_loc) = index_key.switch_on_term_loc() {
                        let indexing_code = match &mut self.wam_prelude.code[index_loc] {
                            Instruction::IndexingCode(indexing_code) => indexing_code,
                            _ => {
                                unreachable!()
                            }
                        };

                        match index_key {
                            OptArgIndexKey::Literal(
                                _,
                                index_loc,
                                constant,
                                overlapping_constants,
                            ) => {
                                remove_constant_indices(
                                    constant,
                                    &overlapping_constants,
                                    indexing_code,
                                    clause_loc - index_loc, // WAS: &inner_index_locs,
                                );
                            }
                            OptArgIndexKey::Structure(_, index_loc, name, arity) => {
                                remove_structure_index(
                                    name,
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
                    match self.wam_prelude.code[instr_loc] {
                        Instruction::TryMeElse(ref mut o)
                        | Instruction::RetryMeElse(ref mut o)
                        | Instruction::DefaultRetryMeElse(ref mut o) => {
                            *o = offset;
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                RetractionRecord::AppendedTrustMe(instr_loc, offset, is_default) => {
                    self.wam_prelude.code[instr_loc] = if is_default {
                        Instruction::DefaultTrustMe(offset)
                    } else {
                        Instruction::TrustMe(offset)
                    };
                }
                RetractionRecord::ReplacedSwitchOnTermVarIndex(index_loc, old_v) => {
                    if let Instruction::IndexingCode(ref mut indexing_code) =
                        self.wam_prelude.code[index_loc]
                    {
                        if let IndexingLine::Indexing(IndexingInstruction::SwitchOnTerm(
                            _,
                            ref mut v,
                            ..,
                        )) = &mut indexing_code[0]
                        {
                            *v = old_v;
                        }
                    }
                }
                RetractionRecord::ModifiedTryMeElse(instr_loc, o) => {
                    self.wam_prelude.code[instr_loc] = Instruction::TryMeElse(o);
                }
                RetractionRecord::ModifiedRetryMeElse(instr_loc, o) => {
                    self.wam_prelude.code[instr_loc] = Instruction::RetryMeElse(o);
                }
                RetractionRecord::ModifiedRevJmpBy(instr_loc, o) => {
                    self.wam_prelude.code[instr_loc] = Instruction::RevJmpBy(o);
                }
                RetractionRecord::SkeletonClausePopBack(compilation_target, key) => {
                    if let Some(skeleton) = self
                        .wam_prelude
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        skeleton.clauses.pop_back();
                        skeleton.core.clause_clause_locs.pop_back();
                    }
                }
                RetractionRecord::SkeletonClausePopFront(compilation_target, key) => {
                    if let Some(skeleton) = self
                        .wam_prelude
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        skeleton.clauses.pop_front();
                        skeleton.core.clause_clause_locs.pop_front();
                        skeleton.core.clause_assert_margin -= 1;
                    }
                }
                RetractionRecord::SkeletonLocalClauseClausePopFront(
                    src_compilation_target,
                    local_compilation_target,
                    key,
                ) => {
                    let listing_src_file_name = self.listing_src_file_name();

                    if let Some(skeleton) =
                        self.wam_prelude.indices.get_local_predicate_skeleton_mut(
                            src_compilation_target,
                            local_compilation_target,
                            listing_src_file_name,
                            key,
                        )
                    {
                        skeleton.clause_clause_locs.pop_front();
                    }
                }
                RetractionRecord::SkeletonLocalClauseClausePopBack(
                    src_compilation_target,
                    local_compilation_target,
                    key,
                ) => {
                    let listing_src_file_name = self.listing_src_file_name();

                    if let Some(skeleton) =
                        self.wam_prelude.indices.get_local_predicate_skeleton_mut(
                            src_compilation_target,
                            local_compilation_target,
                            listing_src_file_name,
                            key,
                        )
                    {
                        skeleton.clause_clause_locs.pop_back();
                    }
                }
                RetractionRecord::SkeletonLocalClauseTruncateBack(
                    src_compilation_target,
                    local_compilation_target,
                    key,
                    len,
                ) => {
                    let listing_src_file_name = self.listing_src_file_name();

                    if let Some(skeleton) =
                        self.wam_prelude.indices.get_local_predicate_skeleton_mut(
                            src_compilation_target,
                            local_compilation_target,
                            listing_src_file_name,
                            key,
                        )
                    {
                        skeleton.clause_clause_locs.truncate(len);
                    }
                }
                RetractionRecord::SkeletonClauseTruncateBack(compilation_target, key, len) => {
                    if let Some(skeleton) = self
                        .wam_prelude
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        skeleton.clauses.truncate(len);
                        skeleton.core.clause_clause_locs.truncate(len);
                    }
                }
                RetractionRecord::SkeletonClauseStartReplaced(
                    compilation_target,
                    key,
                    target_pos,
                    clause_start,
                ) => {
                    if let Some(skeleton) = self
                        .wam_prelude
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        skeleton.clauses[target_pos].clause_start = clause_start;
                    }
                }
                RetractionRecord::RemovedDynamicSkeletonClause(
                    compilation_target,
                    key,
                    target_pos,
                    clause_clause_loc,
                ) => {
                    if let Some(skeleton) = self
                        .wam_prelude
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        if let Some(removed_clauses) = &mut skeleton.core.retracted_dynamic_clauses
                        {
                            let clause_index_info = removed_clauses.pop().unwrap();

                            skeleton
                                .core
                                .clause_clause_locs
                                .insert(target_pos, clause_clause_loc);

                            skeleton.clauses.insert(target_pos, clause_index_info);
                        }
                    }
                }
                RetractionRecord::RemovedSkeletonClause(
                    compilation_target,
                    key,
                    target_pos,
                    clause_index_info,
                    clause_clause_loc,
                ) => {
                    if let Some(skeleton) = self
                        .wam_prelude
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        skeleton
                            .core
                            .clause_clause_locs
                            .insert(target_pos, clause_clause_loc);
                        skeleton.clauses.insert(target_pos, clause_index_info);
                    }
                }
                RetractionRecord::ReplacedIndexingLine(index_loc, indexing_code) => {
                    self.wam_prelude.code[index_loc] = Instruction::IndexingCode(indexing_code);
                }
                RetractionRecord::RemovedLocalSkeletonClauseLocations(
                    compilation_target,
                    local_compilation_target,
                    key,
                    clause_locs,
                ) => {
                    let listing_src_file_name = self.listing_src_file_name();

                    if let Some(skeleton) =
                        self.wam_prelude.indices.get_local_predicate_skeleton_mut(
                            compilation_target,
                            local_compilation_target,
                            listing_src_file_name,
                            key,
                        )
                    {
                        skeleton.clause_clause_locs = clause_locs
                    }
                }
                RetractionRecord::RemovedSkeleton(compilation_target, key, skeleton) => {
                    match compilation_target {
                        CompilationTarget::User => {
                            self.wam_prelude
                                .indices
                                .extensible_predicates
                                .insert(key, skeleton);
                        }
                        CompilationTarget::Module(module_name) => {
                            if let Some(module) =
                                self.wam_prelude.indices.modules.get_mut(&module_name)
                            {
                                module.extensible_predicates.insert(key, skeleton);
                            }
                        }
                    }
                }
                RetractionRecord::ReplacedDynamicElseOffset(instr_loc, next) => {
                    match self.wam_prelude.code[instr_loc] {
                        Instruction::DynamicElse(_, _, NextOrFail::Next(ref mut o))
                        | Instruction::DynamicInternalElse(_, _, NextOrFail::Next(ref mut o)) => {
                            *o = next;
                        }
                        _ => {}
                    }
                }
                RetractionRecord::AppendedNextOrFail(instr_loc, fail) => {
                    match self.wam_prelude.code[instr_loc] {
                        Instruction::DynamicElse(_, _, ref mut next_or_fail)
                        | Instruction::DynamicInternalElse(_, _, ref mut next_or_fail) => {
                            *next_or_fail = fail;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn extract_module_export_list_from_heap(
        &mut self,
        r: RegType,
    ) -> Result<IndexSet<ModuleExport>, SessionError> {
        let machine_st = LS::machine_st(&mut self.payload);
        let cell = machine_st[r];

        let focus = machine_st.heap.cell_len();
        machine_st.heap.push_cell(cell)
            .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;

        let export_list = FocusedHeapRefMut { heap: &mut machine_st.heap, focus };
        let export_list = setup_module_export_list(export_list)?;

        Ok(export_list.into_iter().collect())
    }

    fn clause_clause(&mut self, cell: HeapCellValue) -> Result<TermWriteResult, CompilationError> {
        let machine_st = LS::machine_st(&mut self.payload);
        let focus = machine_st.heap.cell_len();

        read_heap_cell!(cell,
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(machine_st.heap[s])
                    .get_name_and_arity();

                let mut writer = machine_st.heap.reserve(4)
                    .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;

                writer.write_with(|section| {
                    section.push_cell(str_loc_as_cell!(focus+1));
                    section.push_cell(atom_as_cell!(atom!("clause"), 2));

                    match (name, arity) {
                        (atom!(":-"), 2) => {
                            section.push_cell(heap_loc_as_cell!(s+1));
                            section.push_cell(heap_loc_as_cell!(s+2));
                        }
                        _ => {
                            section.push_cell(str_loc_as_cell!(s));
                            section.push_cell(atom_as_cell!(atom!("true")));
                        }
                    }
                });
            }
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    let mut writer = machine_st.heap.reserve(4)
                        .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;

                    writer.write_with(|section| {
                        section.push_cell(str_loc_as_cell!(focus+1));
                        section.push_cell(atom_as_cell!(atom!("clause"), 2));
                        section.push_cell(atom_as_cell!(name));
                        section.push_cell(atom_as_cell!(atom!("true")));
                    });
                } else {
                    return Err(CompilationError::InadmissibleFact);
                }
            }
            _ => {
                return Err(CompilationError::InadmissibleFact);
            }
        );

        Ok(TermWriteResult::from(&mut machine_st.heap, heap_loc_as_cell!(focus))
           .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?)
    }

    fn add_extensible_predicate_declaration(
        &mut self,
        compilation_target: CompilationTarget,
        name: Atom,
        arity: usize,
        flag_accessor: impl Fn(&mut LocalPredicateSkeleton) -> &mut bool,
        retraction_fn: impl Fn(CompilationTarget, PredicateKey) -> RetractionRecord,
    ) -> Result<(), SessionError> {
        let key = (name, arity);
        let mut throw_permission_error = false;

        match &compilation_target {
            CompilationTarget::User => {
                match self.wam_prelude.indices.extensible_predicates.get_mut(&key) {
                    Some(skeleton) => {
                        if !*flag_accessor(&mut skeleton.core) {
                            *flag_accessor(&mut skeleton.core) = true;

                            self.payload
                                .retraction_info
                                .push_record(retraction_fn(compilation_target, key));
                        }
                    }
                    None => {
                        if self.payload.compilation_target == compilation_target {
                            let mut skeleton = PredicateSkeleton::new();
                            *flag_accessor(&mut skeleton.core) = true;

                            self.add_extensible_predicate(key, skeleton, CompilationTarget::User);
                        } else {
                            throw_permission_error = true;
                        }
                    }
                }
            }
            CompilationTarget::Module(ref module_name) => {
                match self.wam_prelude.indices.modules.get_mut(module_name) {
                    Some(ref mut module) => match module.extensible_predicates.get_mut(&key) {
                        Some(ref mut skeleton) => {
                            if !*flag_accessor(&mut skeleton.core) {
                                *flag_accessor(&mut skeleton.core) = true;

                                self.payload
                                    .retraction_info
                                    .push_record(retraction_fn(compilation_target, key));
                            }
                        }
                        None => {
                            if self.payload.compilation_target == compilation_target {
                                let mut skeleton = PredicateSkeleton::new();
                                *flag_accessor(&mut skeleton.core) = true;

                                self.add_extensible_predicate(key, skeleton, compilation_target);
                            } else {
                                throw_permission_error = true;
                            }
                        }
                    },
                    None => {
                        self.add_dynamically_generated_module(*module_name);

                        let mut skeleton = PredicateSkeleton::new();
                        *flag_accessor(&mut skeleton.core) = true;

                        self.add_extensible_predicate(key, skeleton, compilation_target);
                    }
                }
            }
        }

        if !throw_permission_error {
            let listing_src_file_name = self.listing_src_file_name();
            let payload_compilation_target = self.payload.compilation_target;

            match payload_compilation_target {
                CompilationTarget::User => {
                    match self.wam_prelude.indices.get_local_predicate_skeleton_mut(
                        payload_compilation_target,
                        compilation_target,
                        listing_src_file_name,
                        key,
                    ) {
                        Some(skeleton) => {
                            if !*flag_accessor(skeleton) {
                                *flag_accessor(skeleton) = true;
                            }
                        }
                        None => {
                            let mut skeleton = LocalPredicateSkeleton::new();
                            *flag_accessor(&mut skeleton) = true;

                            self.add_local_extensible_predicate(compilation_target, key, skeleton);
                        }
                    }
                }
                CompilationTarget::Module(ref module_name) => {
                    match self.wam_prelude.indices.modules.get_mut(module_name) {
                        Some(module) => match module
                            .local_extensible_predicates
                            .get_mut(&(compilation_target, key))
                        {
                            Some(skeleton) => {
                                if !*flag_accessor(skeleton) {
                                    *flag_accessor(skeleton) = true;
                                }
                            }
                            None => {
                                let mut skeleton = LocalPredicateSkeleton::new();
                                *flag_accessor(&mut skeleton) = true;

                                self.add_local_extensible_predicate(
                                    compilation_target,
                                    key,
                                    skeleton,
                                );
                            }
                        },
                        None => {
                            self.add_dynamically_generated_module(*module_name);

                            let mut skeleton = LocalPredicateSkeleton::new();
                            *flag_accessor(&mut skeleton) = true;

                            self.add_local_extensible_predicate(compilation_target, key, skeleton);
                        }
                    }
                }
            }

            self.fail_on_undefined(compilation_target, key);

            Ok(())
        } else {
            Err(SessionError::PredicateNotMultifileOrDiscontiguous(
                compilation_target,
                key,
            ))
        }
    }

    fn fail_on_undefined(&mut self, compilation_target: CompilationTarget, key: PredicateKey) {
        /*
         * DynamicUndefined isn't only applied to dynamic predicates
         * but to multifile and discontiguous predicates as well.
         */

        let code_index = self.get_or_insert_code_index(key, compilation_target);

        if code_index.is_undefined() {
            set_code_index(
                &mut self.payload.retraction_info,
                &compilation_target,
                key,
                code_index,
                IndexPtr::dynamic_undefined(),
            );
        }
    }

    fn add_discontiguous_predicate(
        &mut self,
        compilation_target: CompilationTarget,
        name: Atom,
        arity: usize,
    ) -> Result<(), SessionError> {
        let key = (name, arity);

        let predicate_info = self
            .wam_prelude
            .indices
            .get_predicate_skeleton(&self.payload.predicates.compilation_target, &key)
            .map(|skeleton| skeleton.predicate_info())
            .unwrap_or_default();

        self.retract_local_clauses(&key, predicate_info.is_dynamic);

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
        name: Atom,
        arity: usize,
    ) -> Result<(), SessionError> {
        self.add_extensible_predicate_declaration(
            compilation_target,
            name,
            arity,
            |skeleton| &mut skeleton.is_dynamic,
            RetractionRecord::AddedDynamicPredicate,
        )
    }

    fn add_multifile_predicate(
        &mut self,
        compilation_target: CompilationTarget,
        name: Atom,
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

    fn add_clause_clause_if_dynamic(&mut self, value: HeapCellValue) -> Result<(), SessionError> {
        let machine_st = LS::machine_st(&mut self.payload);
        let key_opt = clause_predicate_key_from_heap(&machine_st.heap, value);

        if let Some((predicate_name, predicate_arity)) = key_opt {
            let predicates_compilation_target = self.payload.predicates.compilation_target;

            let is_dynamic = self
                .wam_prelude
                .indices
                .get_predicate_skeleton(
                    &predicates_compilation_target,
                    &(predicate_name, predicate_arity),
                )
                .map(|skeleton| skeleton.core.is_dynamic)
                .unwrap_or(false);

            if is_dynamic {
                let clause_clause_term = self.clause_clause(value)?;
                self.payload.clause_clauses.push(clause_clause_term);
            }
        }

        Ok(())
    }

    pub(super) fn retract_local_clauses(&mut self, key: &PredicateKey, is_dynamic: bool) {
        let payload_compilation_target = self.payload.compilation_target;
        let predicates_compilation_target = self.payload.predicates.compilation_target;
        let listing_src_file_name = self.listing_src_file_name();

        let clause_locs = match self.wam_prelude.indices.get_local_predicate_skeleton_mut(
            payload_compilation_target,
            predicates_compilation_target,
            listing_src_file_name,
            *key,
        ) {
            Some(skeleton) if !skeleton.clause_clause_locs.is_empty() => {
                std::mem::take(&mut skeleton.clause_clause_locs)
            }
            _ => return,
        };

        self.payload.retraction_info.push_record(
            RetractionRecord::RemovedLocalSkeletonClauseLocations(
                payload_compilation_target,
                predicates_compilation_target,
                *key,
                clause_locs.clone(),
            ),
        );

        self.retract_local_clauses_impl(predicates_compilation_target, *key, &clause_locs);

        if is_dynamic {
            let clause_clause_compilation_target = match predicates_compilation_target {
                CompilationTarget::User => CompilationTarget::Module(atom!("builtins")),
                module_name => module_name,
            };

            self.retract_local_clause_clauses(clause_clause_compilation_target, &clause_locs);
        }
    }
}

impl<'a> MachinePreludeView<'a> {
    #[inline]
    pub(super) fn composite_op_dir(
        &self,
        compilation_target: &CompilationTarget,
    ) -> CompositeOpDir {
        match compilation_target {
            CompilationTarget::User => CompositeOpDir::new(&self.indices.op_dir, None),
            CompilationTarget::Module(ref module_name) => {
                match self.indices.modules.get(module_name) {
                    Some(module) => CompositeOpDir::new(&self.indices.op_dir, Some(&module.op_dir)),
                    None => {
                        unreachable!()
                    }
                }
            }
        }
    }
}

impl Machine {
    pub(crate) fn use_module(&mut self) -> CallResult {
        let subevacuable_addr = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[2]));

        let module_src = ModuleSource::Library({
            let payload = cell_as_load_state_payload!(subevacuable_addr);

            match payload.compilation_target {
                CompilationTarget::Module(module_name) => module_name,
                CompilationTarget::User => {
                    return Ok(());
                }
            }
        });

        let mut loader = self.loader_from_heap_evacuable(temp_v!(1));

        let use_module = || {
            let export_list = loader.extract_module_export_list_from_heap(temp_v!(3))?;

            if export_list.is_empty() {
                loader.use_module(module_src)?;
            } else {
                loader.use_qualified_module(module_src, export_list)?;
            }

            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = use_module();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn load_compiled_library(&mut self) -> CallResult {
        let library = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        if let Some(module) = self.indices.modules.get(&library) {
            if let ListingSource::DynamicallyGenerated = module.listing_src {
                self.machine_st.fail = true;
                return Ok(());
            }

            let mut loader = self.loader_from_heap_evacuable(temp_v!(3));

            let import_module = || {
                let export_list = loader.extract_module_export_list_from_heap(temp_v!(2))?;

                if export_list.is_empty() {
                    loader.import_module(library)?;
                } else {
                    loader.import_qualified_module(library, export_list)?;
                }

                LiveLoadAndMachineState::evacuate(loader)
            };

            let result = import_module();
            self.restore_load_state_payload(result)
        } else {
            self.machine_st.fail = true;
            Ok(())
        }
    }

    pub(crate) fn declare_module(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let mut loader = self.loader_from_heap_evacuable(temp_v!(3));

        let declare_module = || {
            let exports = loader.extract_module_export_list_from_heap(temp_v!(2))?;

            let module_decl = ModuleDecl {
                name: module_name,
                exports: exports.into_iter().collect(),
            };

            loader.load_decl(Declaration::Module(module_decl))?;
            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = declare_module();
        self.restore_load_state_payload(result)
    }

    #[inline]
    pub(crate) fn add_discontiguous_predicate(&mut self) -> CallResult {
        self.add_extensible_predicate_declaration(
            |loader, compilation_target, clause_name, arity| {
                loader.add_discontiguous_predicate(compilation_target, clause_name, arity)
            },
        )
    }

    #[inline]
    pub(crate) fn add_dynamic_predicate(&mut self) -> CallResult {
        self.add_extensible_predicate_declaration(
            |loader, compilation_target, clause_name, arity| {
                loader.add_dynamic_predicate(compilation_target, clause_name, arity)
            },
        )
    }

    #[inline]
    pub(crate) fn add_multifile_predicate(&mut self) -> CallResult {
        self.add_extensible_predicate_declaration(
            |loader, compilation_target, clause_name, arity| {
                loader.add_multifile_predicate(compilation_target, clause_name, arity)
            },
        )
    }

    fn add_extensible_predicate_declaration(
        &mut self,
        decl_adder: impl for<'a> Fn(
            &mut Loader<'a, LiveLoadAndMachineState<'a>>,
            CompilationTarget,
            Atom,
            usize,
        ) -> Result<(), SessionError>,
    ) -> CallResult {
        let module_name = cell_as_atom!(self.deref_register(1));

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let predicate_name = cell_as_atom!(self.deref_register(2));

        let arity = self.deref_register(3);
        let arity = match Number::try_from(arity) {
            Ok(Number::Integer(n)) if *n >= Integer::ZERO && *n <= Integer::from(MAX_ARITY) => {
                let value: usize = (&*n).try_into().unwrap();
                Ok(value)
            }
            Ok(Number::Fixnum(n)) if n.get_num() >= 0 && n.get_num() <= MAX_ARITY as i64 => {
                Ok(usize::try_from(n.get_num()).unwrap())
            }
            _ => Err(SessionError::from(CompilationError::InvalidRuleHead)),
        };

        let mut loader = self.loader_from_heap_evacuable(temp_v!(4));

        let add_predicate_decl = move || {
            decl_adder(&mut loader, compilation_target, predicate_name, arity?)?;
            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = add_predicate_decl();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn add_term_expansion_clause(&mut self) -> CallResult {
        let value = self.machine_st.registers[1];
        let term = resource_error_call_result!(
            self.machine_st,
            TermWriteResult::from(&mut self.machine_st.heap, value)
        );

        let mut loader = self.loader_from_heap_evacuable(temp_v!(2));

        let add_clause = || {
            loader.incremental_compile_clause(
                (atom!("term_expansion"), 2),
                term,
                CompilationTarget::User,
                false,
                AppendOrPrepend::Append,
            )?;

            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = add_clause();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn add_goal_expansion_clause(&mut self) -> CallResult {
        let target_module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let compilation_target = match target_module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(target_module_name),
        };

        let value = self.machine_st.registers[2];
        let term  = resource_error_call_result!(
            self.machine_st,
            TermWriteResult::from(&mut self.machine_st.heap, value)
        );

        let add_clause = || {
            let indexing_arg_opt = match term_predicate_key(&self.machine_st.heap, term.focus) {
                Some((atom!(":-"), _)) => {
                    term_nth_arg(&self.machine_st.heap, term.focus, 1).and_then(|h| {
                        term_nth_arg(&self.machine_st.heap, h, 1)
                    })
                }
                Some(_) => term_nth_arg(&self.machine_st.heap, term.focus, 1),
                None => None,
            };

            let key_opt = indexing_arg_opt.and_then(|indexing_term_loc| {
                term_predicate_key(&self.machine_st.heap, indexing_term_loc)
            });

            let mut loader = self.loader_from_heap_evacuable(temp_v!(3));

            if let Some((name, arity)) = key_opt {
                loader
                    .wam_prelude
                    .indices
                    .goal_expansion_indices
                    .insert((name, arity));
            }

            loader.incremental_compile_clause(
                (atom!("goal_expansion"), 2),
                term,
                compilation_target,
                false, // backtracking inferences are counted by call_with_inference_limit.
                AppendOrPrepend::Append,
            )?;

            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = add_clause();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn add_in_situ_filename_module(&mut self) -> CallResult {
        let mut loader = self.loader_from_heap_evacuable(temp_v!(1));

        let add_in_situ_filename_module = || {
            if let Some(filename) = loader.listing_src_file_name() {
                let module_decl = ModuleDecl {
                    name: filename,
                    exports: vec![],
                };

                let module_name = module_decl.name;

                if !loader
                    .wam_prelude
                    .indices
                    .modules
                    .contains_key(&module_decl.name)
                {
                    let module = Module::new_in_situ(module_decl);
                    loader
                        .wam_prelude
                        .indices
                        .modules
                        .insert(module_name, module);
                } else {
                    loader.reset_in_situ_module(
                        module_decl.clone(),
                        &ListingSource::DynamicallyGenerated,
                    );

                    if let Some(module) = loader.wam_prelude.indices.modules.get_mut(&module_name) {
                        for (key, value) in module.op_dir.drain(0..) {
                            let mut op_decl = OpDecl::new(value, key.0);
                            op_decl.remove(&mut loader.wam_prelude.indices.op_dir);
                        }
                    }
                }
            }

            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = add_in_situ_filename_module();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn loader_from_heap_evacuable(
        &mut self,
        r: RegType,
    ) -> Loader<'_, LiveLoadAndMachineState<'_>> {
        let mut load_state = cell_as_load_state_payload!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[r])));

        load_state.set_tag(ArenaHeaderTag::LiveLoadState);

        let (wam_prelude, machine_st) = self.prelude_view_and_machine_st();

        Loader {
            payload: LiveLoadAndMachineState {
                load_state,
                machine_st,
            },
            wam_prelude,
        }
    }

    #[inline]
    pub(crate) fn push_load_state_payload(&mut self) {
        let payload: TypedArenaPtr<LiveLoadState> = arena_alloc!(
            LoadStatePayload::new(self.code.len(), LiveTermStream::new(ListingSource::User),),
            &mut self.machine_st.arena
        );

        let var = self.machine_st.deref(self.machine_st.registers[1]);

        self.machine_st
            .bind(var.as_var().unwrap(), typed_arena_ptr_as_cell!(payload));
    }

    #[inline]
    pub(crate) fn pop_load_state_payload(&mut self) {
        let load_state_payload = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1]));

        // unlike in loader_from_heap_evacuable,
        // pop_load_state_payload is allowed to fail to find a
        // LoadStatePayload in the heap, as a Rust-side
        // top-level command may have failed to write the
        // load state payload back to the heap.

        read_heap_cell!(load_state_payload,
            (HeapCellValueTag::Cons, cons_ptr) => {
                match_untyped_arena_ptr!(cons_ptr,
                    (ArenaHeaderTag::LiveLoadState, payload) => {
                        let mut payload = payload;
                        payload.drop_payload()
                    }
                    _ => {}
                );
            }
            _ => {}
        );
    }

    #[inline]
    pub(crate) fn pop_load_context(&mut self) {
        self.load_contexts.pop();
    }

    pub(crate) fn push_load_context(&mut self) -> CallResult {
        let stream = self.machine_st.get_stream_or_alias(
            self.machine_st.registers[1],
            &self.indices,
            atom!("$push_load_context"),
            2,
        )?;

        let path = cell_as_atom!(self.deref_register(2));

        self.load_contexts
            .push(LoadContext::new(&path.as_str(), stream));
        Ok(())
    }

    pub(crate) fn restore_load_state_payload(
        &mut self,
        result: Result<TypedArenaPtr<LiveLoadState>, SessionError>,
    ) -> CallResult {
        match result {
            Ok(_payload) => Ok(()),
            Err(e) => {
                let err = self.machine_st.session_error(e);
                let stub = functor_stub(atom!("load"), 1);

                Err(self.machine_st.error_form(err, stub))
            }
        }
    }

    pub(crate) fn scoped_clause_to_evacuable(&mut self) -> CallResult {
        let target = self.deref_register(1);

        let mut permission_error = || {
            let err = self.machine_st.permission_error(
                Permission::Modify,
                atom!("static_procedure"),
                functor_stub(atom!(":"), 2)
                    .into_iter()
                    .collect::<MachineStub>(),
            );

            self.machine_st
                .error_form(err, functor_stub(atom!("load"), 1))
        };

        let module_name = read_heap_cell!(target,
            (HeapCellValueTag::Atom, (name, arity)) => {
                if arity == 0 {
                    name
                } else {
                    return Err(permission_error());
                }
            }
            _ => {
                return Err(permission_error());
            }
        );

        let loader = self.loader_from_heap_evacuable(temp_v!(3));

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let result = loader.read_and_enqueue_term(temp_v!(2), compilation_target);
        self.restore_load_state_payload(result)
    }

    pub(crate) fn clause_to_evacuable(&mut self) -> CallResult {
        let loader = self.loader_from_heap_evacuable(temp_v!(2));
        let compilation_target = loader.payload.compilation_target;

        let result = loader.read_and_enqueue_term(temp_v!(1), compilation_target);
        self.restore_load_state_payload(result)
    }

    pub(crate) fn conclude_load(&mut self) -> CallResult {
        let mut loader = self.loader_from_heap_evacuable(temp_v!(1));

        let compile_final_terms = || {
            if !loader.payload.predicates.is_empty() {
                loader.compile_and_submit()?;
            }

            loader.remove_module_op_exports();
            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = compile_final_terms();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn load_context_source(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            let path_str = load_context.path.to_str().unwrap();
            let path_atom = AtomTable::build_with(&self.machine_st.atom_tbl, path_str);

            self.machine_st
                .unify_atom(path_atom, self.machine_st.registers[1]);
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
                        AtomTable::build_with(&self.machine_st.atom_tbl, file_name_str);

                    self.machine_st
                        .unify_atom(file_name_atom, self.machine_st.registers[1]);
                    return;
                }
                _ => {
                    return self.load_context_module(self.machine_st.registers[1]);
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
                    AtomTable::build_with(&self.machine_st.atom_tbl, directory_str);

                self.machine_st
                    .unify_atom(directory_atom, self.machine_st.registers[1]);
                return;
            }
        }

        self.machine_st.fail = true;
    }

    pub(crate) fn load_context_module(&mut self, target: HeapCellValue) {
        if let Some(load_context) = self.load_contexts.last() {
            self.machine_st.unify_atom(load_context.module, target);
        } else {
            self.machine_st.fail = true;
        }
    }

    pub(crate) fn load_context_stream(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            self.machine_st.unify_constant(
                UntypedArenaPtr::from(load_context.stream.as_ptr()),
                self.machine_st.registers[1],
            );
        } else {
            self.machine_st.fail = true;
        }
    }

    pub(crate) fn compile_assert(&mut self, append_or_prepend: AppendOrPrepend) -> CallResult {
        let module_name = cell_as_atom!(self.deref_register(1));

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let key = match append_or_prepend {
            AppendOrPrepend::Append => (atom!("assertz"), 1),
            AppendOrPrepend::Prepend => (atom!("asserta"), 1),
        };

        let stub_gen = || functor_stub(key.0, key.1);
        let assert_clause = self.machine_st.registers[2];
        let key_opt = clause_predicate_key_from_heap(&self.machine_st.heap, assert_clause);

        let mut compile_assert = |assert_clause, key_opt| {
            let mut loader: Loader<'_, LiveLoadAndMachineState<'_>> =
                Loader::new(self, LiveTermStream::new(ListingSource::User));

            loader.payload.compilation_target = compilation_target;

            let (name, arity) = if let Some(key) = key_opt {
                key
            } else {
                return Err(SessionError::from(CompilationError::InvalidRuleHead));
            };

            let is_builtin = loader.wam_prelude.indices.builtin_property((name, arity));

            let is_dynamic_predicate = loader
                .wam_prelude
                .indices
                .is_dynamic_predicate(module_name, (name, arity));

            let no_such_predicate = if !is_dynamic_predicate && !is_builtin {
                let idx_tag = loader
                    .wam_prelude
                    .indices
                    .get_predicate_code_index(name, arity, module_name)
                    .map(|code_idx| code_idx.get_tag())
                    .unwrap_or(IndexPtrTag::DynamicUndefined);

                if idx_tag == IndexPtrTag::Index {
                    return Err(SessionError::CannotOverwriteStaticProcedure((name, arity)));
                } else {
                    idx_tag == IndexPtrTag::Undefined || idx_tag == IndexPtrTag::DynamicUndefined
                }
            } else if is_builtin {
                return Err(SessionError::CannotOverwriteBuiltIn((name, arity)));
            } else {
                is_dynamic_predicate
            };

            if !no_such_predicate {
                LiveLoadAndMachineState::machine_st(&mut loader.payload).fail = true;
                return LiveLoadAndMachineState::evacuate(loader);
            }

            // if a new predicate was just created, make it dynamic.
            loader.add_dynamic_predicate(compilation_target, name, arity)?;

            let machine_st = LiveLoadAndMachineState::machine_st(&mut loader.payload);
            // let asserted_clause = loader.copy_term_from_heap(assert_clause);

            let term = TermWriteResult::from(&mut machine_st.heap, assert_clause)
                .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;

            loader.incremental_compile_clause(
                (name, arity),
                term,
                compilation_target,
                false,
                append_or_prepend,
            )?;

            let clause_clause_term = loader.clause_clause(assert_clause)?;

            // the global clock is incremented after each assertion.
            LiveLoadAndMachineState::machine_st(&mut loader.payload).global_clock += 1;

            loader.compile_clause_clauses(
                (name, arity),
                compilation_target,
                vec![clause_clause_term],
                append_or_prepend,
            )?;

            LiveLoadAndMachineState::evacuate(loader)
        };

        match compile_assert(assert_clause, key_opt) {
            Ok(_) => Ok(()),
            Err(SessionError::CompilationError(
                CompilationError::InvalidRuleHead | CompilationError::InadmissibleFact,
            )) => {
                let err = self
                    .machine_st
                    .type_error(ValidType::Callable, self.machine_st.registers[2]);

                Err(self.machine_st.error_form(err, stub_gen()))
            }
            Err(SessionError::CompilationError(CompilationError::InadmissibleQueryTerm)) => {
                let err = self
                    .machine_st
                    .type_error(ValidType::Callable, self.machine_st.registers[3]);

                Err(self.machine_st.error_form(err, stub_gen()))
            }
            Err(e) => {
                let err = self.machine_st.session_error(e);
                Err(self.machine_st.error_form(err, stub_gen()))
            }
        }
    }

    pub(crate) fn abolish_clause(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st.registers[2], self.machine_st.registers[3]);

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let mut abolish_clause = || {
            let mut loader: Loader<'_, LiveLoadAndMachineState<'_>> =
                Loader::new(self, LiveTermStream::new(ListingSource::User));

            loader.payload.compilation_target = compilation_target;

            let clause_clause_compilation_target = match compilation_target {
                CompilationTarget::User => CompilationTarget::Module(atom!("builtins")),
                module => module,
            };

            let mut clause_clause_target_poses: Vec<_> = loader
                .wam_prelude
                .indices
                .remove_predicate_skeleton(&compilation_target, &key)
                .map(|skeleton| {
                    let mut clause_clause_skeleton = loader
                        .wam_prelude
                        .indices
                        .remove_predicate_skeleton(
                            &clause_clause_compilation_target,
                            &(atom!("$clause"), 2),
                        )
                        .unwrap();

                    let result = skeleton
                        .core
                        .clause_clause_locs
                        .iter()
                        .map(|clause_clause_loc| {
                            clause_clause_skeleton
                                .target_pos_of_clause_clause_loc(*clause_clause_loc)
                                .unwrap()
                        })
                        .collect();

                    loader.add_extensible_predicate(key, skeleton, compilation_target);

                    loader.add_extensible_predicate(
                        (atom!("$clause"), 2),
                        clause_clause_skeleton,
                        clause_clause_compilation_target,
                    );

                    result
                })
                .unwrap();

            loader
                .wam_prelude
                .indices
                .remove_predicate_skeleton(&compilation_target, &key);

            let mut code_index = loader.get_or_insert_code_index(key, compilation_target);

            code_index.set(IndexPtr::undefined());

            loader.payload.compilation_target = clause_clause_compilation_target;

            while let Some(target_pos) = clause_clause_target_poses.pop() {
                loader.retract_clause((atom!("$clause"), 2), target_pos);
            }

            LiveLoadAndMachineState::evacuate(loader)
        };

        match abolish_clause() {
            Ok(_) => Ok(()),
            Err(e) => {
                let stub = functor_stub(atom!("abolish"), 1);
                let err = self.machine_st.session_error(e);
                Err(self.machine_st.error_form(err, stub))
            }
        }
    }

    pub(crate) fn retract_clause(&mut self) -> CallResult {
        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(1)], self.machine_st[temp_v!(2)]);

        let target_pos = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[temp_v!(3)]));

        let target_pos = match Number::try_from(target_pos) {
            Ok(Number::Integer(n)) => {
                let value: usize = (&*n).try_into().unwrap();
                value
            }
            Ok(Number::Fixnum(n)) => usize::try_from(n.get_num()).unwrap(),
            _ => unreachable!(),
        };

        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[4])));

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let clause_clause_compilation_target = match compilation_target {
            CompilationTarget::User => CompilationTarget::Module(atom!("builtins")),
            _ => compilation_target,
        };

        let mut retract_clause = || {
            let mut loader: Loader<'_, LiveLoadAndMachineState<'_>> =
                Loader::new(self, LiveTermStream::new(ListingSource::User));

            loader.payload.compilation_target = compilation_target;

            let clause_clause_loc = loader.retract_dynamic_clause(key, target_pos);

            // the global clock is incremented after each retraction.
            LiveLoadAndMachineState::machine_st(&mut loader.payload).global_clock += 1;

            let target_pos = match loader.wam_prelude.indices.get_predicate_skeleton_mut(
                &clause_clause_compilation_target,
                &(atom!("$clause"), 2),
            ) {
                Some(skeleton) => skeleton
                    .target_pos_of_clause_clause_loc(clause_clause_loc)
                    .unwrap(),
                None => {
                    unreachable!();
                }
            };

            loader.payload.compilation_target = clause_clause_compilation_target;
            loader.retract_clause((atom!("$clause"), 2), target_pos);

            LiveLoadAndMachineState::evacuate(loader)
        };

        match retract_clause() {
            Ok(_) => Ok(()),
            Err(e) => {
                let stub = functor_stub(atom!("retract"), 1);
                let err = self.machine_st.session_error(e);

                Err(self.machine_st.error_form(err, stub))
            }
        }
    }

    pub(crate) fn is_consistent_with_term_queue(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        let mut loader = self.loader_from_heap_evacuable(temp_v!(4));
        let predicate_focus_opt = loader.payload.predicates.first().map(|term_write_result| {
            term_write_result.focus
        });

        let is_consistent = if let Some(predicate_focus) = predicate_focus_opt {
            let machine_st = LiveLoadAndMachineState::machine_st(&mut loader.payload);
            clause_predicate_key(&machine_st.heap, predicate_focus) == Some(key)
        } else {
            true
        };

        LiveLoadAndMachineState::machine_st(&mut loader.payload).fail =
            (!loader.payload.predicates.is_empty()
             && loader.payload.predicates.compilation_target != compilation_target)
                || !is_consistent;

        let result = LiveLoadAndMachineState::evacuate(loader);
        self.restore_load_state_payload(result)
    }

    pub(crate) fn flush_term_queue(&mut self) -> CallResult {
        let mut loader = self.loader_from_heap_evacuable(temp_v!(1));

        let flush_term_queue = || {
            if !loader.payload.predicates.is_empty() {
                loader.compile_and_submit()?;
            }

            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = flush_term_queue();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn remove_module_exports(&mut self) -> CallResult {
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let mut loader = self.loader_from_heap_evacuable(temp_v!(2));

        let remove_module_exports = || {
            loader.remove_module_exports(module_name);
            LiveLoadAndMachineState::evacuate(loader)
        };

        let result = remove_module_exports();
        self.restore_load_state_payload(result)
    }

    pub(crate) fn add_non_counted_backtracking(&mut self) -> CallResult {
        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(1)], self.machine_st[temp_v!(2)]);

        let mut loader = self.loader_from_heap_evacuable(temp_v!(3));
        loader.payload.non_counted_bt_preds.insert(key);

        let result = LiveLoadAndMachineState::evacuate(loader);
        self.restore_load_state_payload(result)
    }

    pub(crate) fn meta_predicate_property(&mut self) {
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let (predicate_name, arity) = self
            .machine_st
            .read_predicate_key(self.machine_st.registers[2], self.machine_st.registers[3]);

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
            _ => CompilationTarget::Module(module_name),
        };

        match self
            .indices
            .get_meta_predicate_spec(predicate_name, arity, &compilation_target)
        {
            Some(meta_specs) => {
                let term_loc = self.machine_st.heap.cell_len();

                let mut writer = match self.machine_st.heap.reserve(3 + meta_specs.len()) {
                    Ok(writer) => writer,
                    Err(err_loc) => {
                        self.machine_st.throw_resource_error(err_loc);
                        return;
                    }
                };

                writer.write_with(|section| {
                    section.push_cell(atom_as_cell!(predicate_name, arity));

                    for meta_spec in meta_specs.iter() {
                        section.push_cell(match meta_spec {
                            MetaSpec::Minus => atom_as_cell!(atom!("+")),
                            MetaSpec::Plus => atom_as_cell!(atom!("-")),
                            MetaSpec::Either => atom_as_cell!(atom!("?")),
                            MetaSpec::Colon => atom_as_cell!(atom!(":")),
                            MetaSpec::RequiresExpansionWithArgument(ref arg_num) => {
                                fixnum_as_cell!(Fixnum::build_with(*arg_num as i64))
                            }
                        });
                    }

                    section.push_cell(atom_as_cell!(atom!("meta_predicate"), 1));
                    section.push_cell(str_loc_as_cell!(term_loc));
                });

                let heap_loc = self.machine_st.heap.cell_len() - 2;

                unify!(
                    self.machine_st,
                    str_loc_as_cell!(heap_loc),
                    self.machine_st.registers[4]
                );
            }
            None => {
                self.machine_st.fail = true;
            }
        }
    }

    pub(crate) fn dynamic_property(&mut self) {
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
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
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
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
        let module_name = cell_as_atom!(self
            .machine_st
            .store(self.machine_st.deref(self.machine_st.registers[1])));

        let key = self
            .machine_st
            .read_predicate_key(self.machine_st[temp_v!(2)], self.machine_st[temp_v!(3)]);

        let compilation_target = match module_name {
            atom!("user") => CompilationTarget::User,
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
}

impl<'a> Loader<'a, LiveLoadAndMachineState<'a>> {
    fn read_and_enqueue_term(
        mut self,
        term_reg: RegType,
        compilation_target: CompilationTarget,
    ) -> Result<TypedArenaPtr<LoadStatePayload<LiveTermStream>>, SessionError> {
        if self.payload.predicates.compilation_target != compilation_target {
            if !self.payload.predicates.is_empty() {
                self.compile_and_submit()?;
            }

            self.payload.predicates.compilation_target = compilation_target;
        }

        let machine_st = LiveLoadAndMachineState::machine_st(&mut self.payload);
        let value = machine_st.store(MachineState::deref(&machine_st, machine_st[term_reg]));

        self.add_clause_clause_if_dynamic(value)?;

        let machine_st = LiveLoadAndMachineState::machine_st(&mut self.payload);

        let term = TermWriteResult::from(&mut machine_st.heap, value)
            .map_err(|_err_loc| ParserError::ResourceError(ParserErrorSrc::default()))?;

        self.payload.term_stream.term_queue.push_back(term);
        self.load()
    }
}

#[inline]
pub(super) fn load_module(
    machine_st: &mut MachineState,
    code_dir: &mut CodeDir,
    op_dir: &mut OpDir,
    meta_predicate_dir: &mut MetaPredicateDir,
    compilation_target: &CompilationTarget,
    module: &Module,
) {
    let ts = LiveTermStream::new(ListingSource::User);
    let payload = LoadStatePayload::new(0, ts);
    let mut payload = LiveLoadAndMachineState::new(machine_st, payload);

    import_module_exports::<LiveLoadAndMachineState>(
        &mut payload,
        compilation_target,
        module,
        code_dir,
        op_dir,
        meta_predicate_dir,
    )
    .unwrap();
}
