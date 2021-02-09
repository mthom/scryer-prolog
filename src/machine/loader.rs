use prolog_parser::ast::*;
use prolog_parser::{clause_name, temp_v};

use crate::forms::*;
use crate::indexing::*;
use crate::machine::load_state::*;
use crate::machine::machine_indices::*;
use crate::machine::preprocessor::*;
use crate::machine::*;

use indexmap::IndexSet;

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
 * structure to rebuild the loader between
 * invocations. TopLevelBatchWorker needs access to a &'a mut Machine
 * for as long as it lives, and we can't have copies of &'a mut
 * Machine distributed among multiple owners.
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
    ReplacedModule(ModuleDecl, ListingSource),
    AddedModuleDynamicPredicate(ClauseName, PredicateKey),
    AddedModuleExtensiblePredicate(ClauseName, PredicateKey),
    AppendedModuleExtensiblePredicate(ClauseName, PredicateKey),
    PrependedModuleExtensiblePredicate(ClauseName, PredicateKey),
    AddedModuleOp(ClauseName, OpDecl),
    ReplacedModuleOp(ClauseName, OpDecl, usize, Specifier),
    AddedModulePredicate(ClauseName, PredicateKey),
    ReplacedModulePredicate(ClauseName, PredicateKey, IndexPtr),
    AddedUserDynamicPredicate(PredicateKey),
    AddedUserOp(OpDecl),
    ReplacedUserOp(OpDecl, usize, Specifier),
    AddedUserExtensiblePredicate(PredicateKey),
    AppendedUserExtensiblePredicate(PredicateKey),
    PrependedUserExtensiblePredicate(PredicateKey),
    AddedUserPredicate(PredicateKey),
    ReplacedUserPredicate(PredicateKey, IndexPtr),
    AddedIndex(OptArgIndexKey, usize), //, Vec<usize>),
    RemovedIndex(usize, OptArgIndexKey, usize),
    ReplacedChoiceOffset(usize, usize),
    AppendedTrustMe(usize, usize, bool),
    ReplacedSwitchOnTermVarIndex(usize, usize),
    ModifiedTryMeElse(usize, usize),
    ModifiedRetryMeElse(usize, usize),
    ModifiedRevJmpBy(usize, usize),
    IncreasedClauseAssertMargin(ClauseName, usize),
    SkeletonClauseClausesTruncateBack(CompilationTarget, PredicateKey, usize),
    SkeletonClauseClausesTruncateFront(CompilationTarget, PredicateKey, usize),
    SkeletonClausePopBack(CompilationTarget, PredicateKey),
    SkeletonClausePopFront(CompilationTarget, PredicateKey),
    SkeletonClauseTruncateBack(CompilationTarget, PredicateKey, usize),
    SkeletonClauseStartReplaced(CompilationTarget, PredicateKey, usize, usize),
    RemovedDynamicSkeletonClause(
        CompilationTarget,
        PredicateKey,
        usize,
        ClauseIndexInfo,
        usize,
    ),
    ReplacedIndexingLine(usize, Vec<IndexingLine>),
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
            records: mem::replace(&mut self.records, vec![]), //BTreeMap::new()),
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
                RetractionRecord::ReplacedModule(module_decl, listing_src) => {
                    match self.wam.indices.modules.get_mut(&module_decl.name) {
                        Some(ref mut module) => {
                            module.module_decl = module_decl;
                            module.listing_src = listing_src;
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }
                RetractionRecord::AddedModuleDynamicPredicate(module_name, key) => {
                    match self.wam.indices.modules.get_mut(&module_name) {
                        Some(ref mut module) => {
                            module.extensible_predicates.get_mut(&key).map(|skeleton| {
                                skeleton.is_dynamic = false;
                            });
                        }
                        None => {}
                    }
                }
                RetractionRecord::AddedModuleExtensiblePredicate(module_name, key) => {
                    self.wam
                        .indices
                        .remove_predicate_skeleton(&CompilationTarget::Module(module_name), &key);
                }
                RetractionRecord::AppendedModuleExtensiblePredicate(module_name, key) => {
                    self.wam
                        .indices
                        .get_predicate_skeleton_mut(&CompilationTarget::Module(module_name), &key)
                        .map(|skeleton| {
                            skeleton.clauses.pop_back();
                        });
                }
                RetractionRecord::PrependedModuleExtensiblePredicate(module_name, key) => {
                    self.wam
                        .indices
                        .get_predicate_skeleton_mut(&CompilationTarget::Module(module_name), &key)
                        .map(|skeleton| {
                            skeleton.clauses.pop_front();
                        });
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
                RetractionRecord::AddedUserDynamicPredicate(key) => {
                    self.wam
                        .indices
                        .extensible_predicates
                        .get_mut(&key)
                        .map(|skeleton| {
                            skeleton.is_dynamic = false;
                        });
                }
                RetractionRecord::AddedUserExtensiblePredicate(key) => {
                    self.wam
                        .indices
                        .remove_predicate_skeleton(&CompilationTarget::User, &key);
                }
                RetractionRecord::AppendedUserExtensiblePredicate(key) => {
                    self.wam
                        .indices
                        .get_predicate_skeleton_mut(&CompilationTarget::User, &key)
                        .map(|skeleton| {
                            skeleton.clauses.pop_back();
                        });
                }
                RetractionRecord::PrependedUserExtensiblePredicate(key) => {
                    self.wam
                        .indices
                        .get_predicate_skeleton_mut(&CompilationTarget::User, &key)
                        .map(|skeleton| {
                            skeleton.clauses.pop_front();
                        });
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
                RetractionRecord::IncreasedClauseAssertMargin(module_name, incr) => {
                    if let Some(module) = self.wam.indices.modules.get_mut(&module_name) {
                        module.clause_assert_margin -= incr;
                    }
                }
                RetractionRecord::SkeletonClauseClausesTruncateFront(
                    compilation_target,
                    key,
                    len,
                ) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.truncate_front(len);
                        }
                        None => {}
                    }

                    let compilation_target = match compilation_target {
                        CompilationTarget::User => {
                            CompilationTarget::Module(clause_name!("builtins"))
                        }
                        _ => compilation_target,
                    };

                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &(clause_name!("$clause"), 2))
                    {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.truncate_front(len);
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonClauseClausesTruncateBack(
                    compilation_target,
                    key,
                    len,
                ) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.truncate_back(len);
                        }
                        None => {}
                    }

                    let compilation_target = match compilation_target {
                        CompilationTarget::User => {
                            CompilationTarget::Module(clause_name!("builtins"))
                        }
                        _ => compilation_target,
                    };

                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &(clause_name!("$clause"), 2))
                    {
                        Some(skeleton) => {
                            skeleton.clause_clause_locs.truncate_back(len);
                        }
                        None => {}
                    }
                }
                RetractionRecord::SkeletonClausePopBack(compilation_target, key) => {
                    match self
                        .wam
                        .indices
                        .get_predicate_skeleton_mut(&compilation_target, &key)
                    {
                        Some(skeleton) => {
                            skeleton.clauses.pop_back();
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
                RetractionRecord::RemovedDynamicSkeletonClause(
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
            }
        }

        // TODO: necessary? unnecessary?
        // self.wam.code_repo.code.truncate(self.retraction_info.orig_code_extent);
    }
}

#[derive(Debug, Clone)]
pub enum CompilationTarget {
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
    pub(super) fn module_name(&self) -> ClauseName {
        match self {
            CompilationTarget::User => {
                clause_name!("user")
            }
            CompilationTarget::Module(ref module_name) => module_name.clone(),
        }
    }
}

pub(crate) struct Loader<'a, TermStream> {
    pub(super) load_state: LoadState<'a>,
    pub(super) predicates: Vec<PredicateClause>,
    pub(super) clause_clauses: Vec<(Term, Term)>,
    term_stream: TermStream,
    pub(super) non_counted_bt_preds: IndexSet<PredicateKey>,
    pub(super) preprocessor: Preprocessor,
}

impl<'a, TS: TermStream> Loader<'a, TS> {
    #[inline]
    pub(super) fn new(term_stream: TS, wam: &'a mut Machine) -> Self {
        let flags = wam.machine_st.flags;
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
            preprocessor: Preprocessor::new(flags),
            predicates: vec![],
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

            let tl = self.preprocessor.try_term_to_tl(
                &mut self.load_state,
                term,
                CutContext::BlocksCuts,
            )?;

            match tl {
                TopLevel::Fact(fact) => self.predicates.push(PredicateClause::Fact(fact)),
                TopLevel::Rule(rule) => self.predicates.push(PredicateClause::Rule(rule)),
                TopLevel::Predicate(pred) => self.predicates.extend(pred),
                TopLevel::Declaration(decl) => return Ok(Some(decl)),
                TopLevel::Query(_) => return Err(SessionError::QueryCannotBeDefinedAsFact),
            }
        }

        Ok(None)
    }

    pub(super) fn load_decl(&mut self, decl: Declaration) -> Result<(), SessionError> {
        match decl {
            Declaration::Dynamic(name, arity) => {
                self.add_dynamic_predicate(name, arity);
            }
            Declaration::MetaPredicate(module_name, name, meta_specs) => {
                self.load_state
                    .add_meta_predicate_record(module_name, name, meta_specs);
            }
            Declaration::Module(module_decl) => {
                self.load_state.compilation_target =
                    CompilationTarget::Module(module_decl.name.clone());

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

    fn add_dynamic_predicate(&mut self, name: ClauseName, arity: usize) {
        let key = (name, arity);

        match &self.load_state.compilation_target {
            CompilationTarget::User => {
                match self
                    .load_state
                    .wam
                    .indices
                    .extensible_predicates
                    .get_mut(&key)
                {
                    Some(ref mut skeleton) => {
                        if !skeleton.is_dynamic {
                            skeleton.is_dynamic = true;

                            self.load_state.retraction_info.push_record(
                                RetractionRecord::AddedUserDynamicPredicate(key.clone()),
                            );
                        }
                    }
                    None => {
                        self.load_state
                            .wam
                            .indices
                            .extensible_predicates
                            .insert(key.clone(), PredicateSkeleton::new().set_dynamic(true));

                        self.load_state.retraction_info.push_record(
                            RetractionRecord::AddedUserExtensiblePredicate(key.clone()),
                        );
                    }
                }
            }
            CompilationTarget::Module(ref module_name) => {
                match self.load_state.wam.indices.modules.get_mut(module_name) {
                    Some(ref mut module) => match module.extensible_predicates.get_mut(&key) {
                        Some(ref mut skeleton) => {
                            if !skeleton.is_dynamic {
                                skeleton.is_dynamic = true;

                                self.load_state.retraction_info.push_record(
                                    RetractionRecord::AddedModuleDynamicPredicate(
                                        module_name.clone(),
                                        key.clone(),
                                    ),
                                );
                            }
                        }
                        None => {
                            module
                                .extensible_predicates
                                .insert(key.clone(), PredicateSkeleton::new().set_dynamic(true));

                            self.load_state.retraction_info.push_record(
                                RetractionRecord::AddedModuleExtensiblePredicate(
                                    module_name.clone(),
                                    key.clone(),
                                ),
                            );
                        }
                    },
                    None => {
                        unreachable!();
                    }
                }
            }
        }

        let code_index = self.load_state.get_or_insert_code_index(key.clone());

        set_code_index(
            &mut self.load_state.retraction_info,
            &self.load_state.compilation_target,
            key,
            &code_index,
            IndexPtr::DynamicUndefined,
        );
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

            let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(2));

            let import_module = || {
                loader.load_state.import_module(library)?;
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

    pub(crate) fn add_dynamic_predicate(&mut self) {
        let predicate_name = atom_from!(
            self.machine_st,
            self.machine_st
                .store(self.machine_st.deref(self.machine_st[temp_v!(1)]))
        );

        let arity = self
            .machine_st
            .store(self.machine_st.deref(self.machine_st[temp_v!(2)]));

        let arity = match Number::try_from((arity, &self.machine_st.heap)) {
            Ok(Number::Integer(n)) if &*n >= &0 && &*n <= &MAX_ARITY => Ok(n.to_usize().unwrap()),
            Ok(Number::Fixnum(n)) if n >= 0 && n <= MAX_ARITY as isize => {
                Ok(usize::try_from(n).unwrap())
            }
            _ => Err(SessionError::from(CompilationError::InvalidRuleHead)),
        };

        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(3));

        let add_dynamic_predicate = || {
            loader.add_dynamic_predicate(predicate_name, arity?);
            LiveTermStream::evacuate(loader)
        };

        let result = add_dynamic_predicate();
        self.restore_load_state_payload(result, evacuable_h);
    }

    pub(crate) fn add_term_expansion_clause(&mut self) {
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(2));

        let add_clause = || {
            let term = loader.read_term_from_heap(temp_v!(1))?;

            loader.incremental_compile_clause(
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

            loader.incremental_compile_clause(
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
        let payload = LoadStatePayload::new(self);
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
                &self.indices,
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
                self.machine_st.heap[evacuable_h] = HeapCellValue::LoadStatePayload(payload);
            }
            Err(e) => {
                self.throw_session_error(e, (clause_name!("load"), 1));
            }
        }
    }

    pub(crate) fn clause_to_evacuable(&mut self) {
        let (mut loader, evacuable_h) = self.loader_from_heap_evacuable(temp_v!(2));

        let enqueue_term = || {
            let term = loader.read_term_from_heap(temp_v!(1))?;

            if let Some(predicate_name) = ClauseInfo::name(&term) {
                let arity = ClauseInfo::arity(&term);

                let is_dynamic = loader
                    .load_state
                    .wam
                    .indices
                    .get_predicate_skeleton(
                        &loader.load_state.compilation_target,
                        &(predicate_name, arity),
                    )
                    .map(|skeleton| skeleton.is_dynamic)
                    .unwrap_or(false);

                if is_dynamic {
                    loader.add_clause_clause(term.clone())?;
                }
            }

            loader.enqueue_term(term);
            loader.load()
        };

        let result = enqueue_term();
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
            if let Some(file_name) = load_context.path.file_name() {
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
        }

        self.machine_st.fail = true;
    }

    pub(crate) fn load_context_directory(&mut self) {
        if let Some(load_context) = self.load_contexts.last() {
            if let Some(directory) = load_context.path.parent() {
                // canonicalize returns the absolute path of the directory.
                let directory = directory.canonicalize().unwrap();
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

            let head = loader.read_term_from_heap(temp_v!(1))?;
            let body = loader.read_term_from_heap(temp_v!(2))?;

            let asserted_clause = Term::Clause(
                Cell::default(),
                clause_name!(":-"),
                vec![Box::new(head.clone()), Box::new(body.clone())],
                fetch_op_spec(clause_name!(":-"), 2, &loader.load_state.wam.indices.op_dir),
            );

            loader.incremental_compile_clause(
                key.clone(),
                asserted_clause,
                compilation_target.clone(),
                false,
                append_or_prepend,
            )?;

            // if a new predicate was just created, make it dynamic.
            loader
                .load_state
                .wam
                .indices
                .get_predicate_skeleton_mut(&compilation_target, &key)
                .map(|skeleton| skeleton.is_dynamic = true);

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

            let clause_clause_compilation_target =
                match &loader.load_state.compilation_target {
                    CompilationTarget::User => {
                        CompilationTarget::Module(clause_name!("builtins"))
                    }
                    module => {
                        module.clone()
                    }
                };

            let mut clause_assert_margin = loader
                .load_state
                .wam
                .indices
                .modules
                .get(&clause_clause_compilation_target.module_name())
                .map(|module| module.clause_assert_margin)
                .unwrap();

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
                            skeleton.clause_clause_locs
                                .iter()
                                .map(|clause_clause_loc| {
                                    clause_clause_skeleton.target_pos_of_clause_clause_loc(
                                        *clause_clause_loc,
                                        clause_assert_margin,
                                    )
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
                .map(|skeleton| {
                    skeleton.clauses.clear();
                    skeleton.clause_clause_locs.clear();
                });

            let code_index = loader.load_state.get_or_insert_code_index(key);
            code_index.set(IndexPtr::DynamicUndefined);

            loader.load_state.compilation_target = clause_clause_compilation_target;

            while let Some(target_pos) = clause_clause_target_poses.pop() {
                loader.load_state.retract_clause((clause_name!("$clause"), 2), target_pos);

                if target_pos < clause_assert_margin {
                    clause_assert_margin -= 1;
                }
            }

            loader
                .load_state
                .wam
                .indices
                .modules
                .get_mut(&loader.load_state.compilation_target.module_name())
                .map(|module| module.clause_assert_margin = clause_assert_margin);

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

            let clause_clause_loc = loader.load_state.retract_clause(key, target_pos);

            let clause_assert_margin = loader
                .load_state
                .wam
                .indices
                .modules
                .get(&clause_clause_compilation_target.module_name())
                .map(|module| module.clause_assert_margin)
                .unwrap();

            let target_pos = match loader.load_state.wam.indices.get_predicate_skeleton(
                &clause_clause_compilation_target,
                &(clause_name!("$clause"), 2),
            ) {
                Some(skeleton) => {
                    let target_pos = skeleton.target_pos_of_clause_clause_loc(
                        clause_clause_loc,
                        clause_assert_margin,
                    );

                    if target_pos < clause_assert_margin {
                        loader
                            .load_state
                            .wam
                            .indices
                            .modules
                            .get_mut(&clause_clause_compilation_target.module_name())
                            .map(|module| module.clause_assert_margin -= 1);
                    }

                    target_pos
                }
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
                self.machine_st.fail = !skeleton.is_dynamic;
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
                self.machine_st.fail = !skeleton.is_multifile;
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
                self.machine_st.fail = !skeleton.is_discontiguous;
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
            preprocessor: mem::replace(
                &mut self.preprocessor,
                Preprocessor::new(self.load_state.wam.machine_st.flags),
            ),
            non_counted_bt_preds: mem::replace(&mut self.non_counted_bt_preds, IndexSet::new()),
            compilation_target: self.load_state.compilation_target.take(),
            retraction_info: mem::replace(
                &mut self.load_state.retraction_info,
                RetractionInfo::new(self.load_state.wam.code_repo.code.len()),
            ),
            predicates: mem::replace(&mut self.predicates, vec![]),
            clause_clauses: mem::replace(&mut self.clause_clauses, vec![]),
            module_op_exports: mem::replace(&mut self.load_state.module_op_exports, vec![]),
        }
    }

    pub(super) fn from_load_state_payload(
        wam: &'a mut Machine,
        mut payload: LoadStatePayload,
    ) -> Self {
        Loader {
            term_stream: mem::replace(
                &mut payload.term_stream,
                LiveTermStream::new(ListingSource::User),
            ),
            preprocessor: mem::replace(
                &mut payload.preprocessor,
                Preprocessor::new(MachineFlags::default()),
            ),
            non_counted_bt_preds: mem::replace(&mut payload.non_counted_bt_preds, IndexSet::new()),
            clause_clauses: mem::replace(&mut payload.clause_clauses, vec![]),
            predicates: mem::replace(&mut payload.predicates, vec![]),
            load_state: LoadState {
                compilation_target: payload.compilation_target.take(),
                module_op_exports: mem::replace(&mut payload.module_op_exports, vec![]),
                retraction_info: mem::replace(&mut payload.retraction_info, RetractionInfo::new(0)),
                wam,
            },
        }
    }

    fn incremental_compile_clause(
        &mut self,
        key: PredicateKey,
        term: Term,
        compilation_target: CompilationTarget,
        non_counted_bt: bool,
        append_or_prepend: AppendOrPrepend,
    ) -> Result<(), SessionError> {
        let mut preprocessor = Preprocessor::new(self.load_state.wam.machine_st.flags);

        let tl = preprocessor.try_term_to_tl(&mut self.load_state, term, CutContext::BlocksCuts)?;

        let queue = preprocessor.parse_queue(&mut self.load_state)?;

        let clause = match tl {
            TopLevel::Fact(fact) => PredicateClause::Fact(fact),
            TopLevel::Rule(rule) => PredicateClause::Rule(rule),
            _ => {
                unreachable!()
            }
        };

        let compilation_target =
            mem::replace(&mut self.load_state.compilation_target, compilation_target);

        let result = self.load_state.incremental_compile_clause(
            key,
            clause,
            queue,
            non_counted_bt,
            append_or_prepend,
        );

        self.load_state.compilation_target = compilation_target;
        result?;

        Ok(())
    }

    #[inline]
    fn enqueue_term(&mut self, term: Term) {
        self.term_stream.term_queue.push_back(term);
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
    ).unwrap();
}
