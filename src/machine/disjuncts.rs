use crate::atom_table::*;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::CompilationError;
use crate::machine::preprocessor::*;
use crate::parser::ast::*;
use crate::parser::rug::Rational;
use crate::variable_records::*;

use indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)] //, PartialOrd, PartialEq, Eq, Hash)]
pub struct BranchNumber {
    branch_num: Rational,
    delta: Rational,
}

impl Default for BranchNumber {
    fn default() -> Self {
        Self {
            branch_num: Rational::from(1usize << 63),
            delta: Rational::from(1),
        }
    }
}

impl PartialEq<BranchNumber> for BranchNumber {
    #[inline]
    fn eq(&self, rhs: &BranchNumber) -> bool {
        self.branch_num == rhs.branch_num
    }
}

impl Eq for BranchNumber {}

impl Hash for BranchNumber {
    #[inline(always)]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.branch_num.hash(hasher)
    }
}

impl PartialOrd<BranchNumber> for BranchNumber {
    #[inline]
    fn partial_cmp(&self, rhs: &BranchNumber) -> Option<Ordering> {
        self.branch_num.partial_cmp(&rhs.branch_num)
    }
}

impl BranchNumber {
    fn split(&self) -> BranchNumber {
        BranchNumber {
            branch_num: self.branch_num.clone() + &self.delta / Rational::from(2),
            delta: &self.delta / Rational::from(4),
        }
    }

    fn incr_by_delta(&self) -> BranchNumber {
        BranchNumber {
            branch_num: self.branch_num.clone() + &self.delta,
            delta: self.delta.clone(),
        }
    }

    fn halve_delta(&self) -> BranchNumber {
        BranchNumber {
            branch_num: self.branch_num.clone(),
            delta : &self.delta / Rational::from(2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarInfo {
    var_ptr: VarPtr,
    chunk_type: ChunkType,
    classify_info: ClassifyInfo,
    lvl: Level,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ChunkInfo {
    chunk_num: usize,
    term_loc: GenContext,
    // pointer to incidence, term occurrence arity.
    vars: Vec<VarInfo>,
}

#[derive(Debug)]
pub struct BranchArm {
    pub arm_terms: Vec<QueryTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BranchInfo {
    branch_num: BranchNumber,
    chunks: Vec<ChunkInfo>,
}

impl BranchInfo {
    fn new(branch_num: BranchNumber) -> Self {
        Self { branch_num, chunks: vec![] }
    }
}

type BranchMapInt = IndexMap<VarPtr, Vec<BranchInfo>>;

#[derive(Debug, Clone)]
pub struct BranchMap(BranchMapInt);

impl Deref for BranchMap {
    type Target = BranchMapInt;

    #[inline(always)]
    fn deref(&self) -> &BranchMapInt {
        &self.0
    }
}

impl DerefMut for BranchMap {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut BranchMapInt {
        &mut self.0
    }
}

type RootSet = IndexSet<BranchNumber>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClassifyInfo {
    arg_c: usize,
    arity: usize,
}

enum TraversalState {
    // construct a QueryTerm::Branch with number of disjuncts, reset
    // the chunk type to that of the chunk preceding the disjunct and the chunk_num.
    BuildDisjunct(usize),
    // add the last disjunct to a QueryTerm::Branch, continuing from
    // where it leaves off.
    BuildFinalDisjunct(usize),
    Fail,
    GetCutPoint{ var_num: usize, prev_b: bool },
    Cut { var_num: usize, is_global: bool },
    ResetCallPolicy(CallPolicy),
    Term(Term),
    RemoveBranchNum, // pop the current_branch_num and from the root set.
    AddBranchNum(BranchNumber), // set current_branch_num, add it to the root set
    RepBranchNum(BranchNumber), // replace current_branch_num and the latest in the root set
}

#[derive(Debug)]
pub struct VariableClassifier {
    call_policy: CallPolicy,
    current_branch_num: BranchNumber,
    current_chunk_num: usize,
    current_chunk_type: ChunkType,
    branch_map: BranchMap,
    var_num: usize,
    root_set: RootSet,
    global_cut_var_num: Option<usize>,
}

#[derive(Debug, Default)]
pub struct VarData {
    pub records: VariableRecords,
    pub global_cut_var_num: Option<usize>,
    pub allocates: bool,
}

impl VarData {
    fn emit_initial_get_level(&mut self, build_stack: &mut ChunkedTermVec) {
        let global_cut_var_num =
            if let &Some(global_cut_var_num) = &self.global_cut_var_num {
                match &self.records[global_cut_var_num].allocation {
                    VarAlloc::Perm(..) => Some(global_cut_var_num),
                    VarAlloc::Temp { term_loc, .. } if term_loc.chunk_num() > 0 => {
                        Some(global_cut_var_num)
                    }
                    _ => None
                }
            } else {
                None
            };

        if let Some(global_cut_var_num) = global_cut_var_num {
            let term = QueryTerm::GetLevel(global_cut_var_num);
            self.records[global_cut_var_num].allocation = VarAlloc::Perm(0, PermVarAllocation::Pending);

            match build_stack.front_mut() {
                Some(ChunkedTerms::Branch(_)) => {
                    build_stack.push_front(ChunkedTerms::Chunk(VecDeque::from(vec![term])));
                }
                Some(ChunkedTerms::Chunk(chunk)) => {
                    chunk.push_front(term);
                }
                None => {
                    unreachable!()
                }
            }
        }
    }
}

pub type ClassifyFactResult = (Term, VarData);
pub type ClassifyRuleResult = (Term, ChunkedTermVec, VarData);

fn merge_branch_seq(branches: impl Iterator<Item = BranchInfo>) -> BranchInfo {
    let mut branch_info = BranchInfo::new(BranchNumber::default());

    for mut branch in branches {
        branch_info.branch_num = branch.branch_num;
        branch_info.chunks.extend(branch.chunks.drain(..));
    }

    branch_info.branch_num.delta *= 2;
    branch_info.branch_num.branch_num -= &branch_info.branch_num.delta;

    branch_info
}

fn flatten_into_disjunct(build_stack: &mut ChunkedTermVec, preceding_len: usize) {
    let branch_vec = build_stack.drain(preceding_len + 1 ..).collect();

    if let ChunkedTerms::Branch(ref mut disjuncts) = &mut build_stack[preceding_len] {
        disjuncts.push(branch_vec);
    } else {
        unreachable!();
    }
}

impl VariableClassifier {
    pub fn new(call_policy: CallPolicy) -> Self {
        Self {
            call_policy,
            current_branch_num: BranchNumber::default(),
            current_chunk_num: 0,
            current_chunk_type: ChunkType::Head,
            branch_map: BranchMap(BranchMapInt::new()),
            root_set: RootSet::new(),
            var_num: 0,
            global_cut_var_num: None,
        }
    }

    pub fn classify_fact(mut self, term: Term) -> Result<ClassifyFactResult, CompilationError> {
        self.classify_head_variables(&term)?;
        Ok((term, self.branch_map.separate_and_classify_variables(
            self.var_num,
            self.global_cut_var_num,
            self.current_chunk_num,
        )))
    }

    pub fn classify_rule<'a, LS: LoadState<'a>>(
        mut self,
        loader: &mut Loader<'a, LS>,
        head: Term,
        body: Term,
    ) -> Result<ClassifyRuleResult, CompilationError> {
        self.classify_head_variables(&head)?;
        self.root_set.insert(self.current_branch_num.clone());

        let mut query_terms = self.classify_body_variables(loader, body)?;

        self.merge_branches();

        let mut var_data = self.branch_map.separate_and_classify_variables(
            self.var_num,
            self.global_cut_var_num,
            self.current_chunk_num,
        );

        var_data.emit_initial_get_level(&mut query_terms);

        Ok((head, query_terms, var_data))
    }

    fn merge_branches(&mut self) {
        for branches in self.branch_map.values_mut() {
            let mut old_branches = std::mem::replace(branches, vec![]);

            while let Some(last_branch_num) = old_branches.last().map(|bi| &bi.branch_num) {
                let mut old_branches_len = old_branches.len();

                for (rev_idx, bi) in old_branches.iter().rev().enumerate() {
                    if &bi.branch_num > last_branch_num {
                        old_branches_len = old_branches.len() - rev_idx;
                    }
                }

                let iter = old_branches.drain(old_branches_len - 1 ..);
                branches.push(merge_branch_seq(iter));
            }

            branches.reverse();
        }
    }

    fn try_set_chunk_at_inlined_boundary(&mut self) -> bool {
        if self.current_chunk_type.is_last() {
            self.current_chunk_type = ChunkType::Mid;
            self.current_chunk_num += 1;
            true
        } else {
            false
        }
    }

    fn try_set_chunk_at_call_boundary(&mut self) -> bool {
        if self.current_chunk_type.is_last() {
            self.current_chunk_num += 1;
            true
        } else {
            self.current_chunk_type = ChunkType::Last;
            false
        }
    }

    fn probe_body_term(&mut self, arg_c: usize, arity: usize, term: &Term) {
        let classify_info = ClassifyInfo { arg_c, arity };

        // second arg is true to iterate the root, which may be a variable
        for term_ref in breadth_first_iter(term, RootIterationPolicy::Iterated) {
            if let TermRef::Var(lvl, _, var_ptr) = term_ref {
                // root terms are shallow here (since we're iterating a
                // body term) so take the child level.
                let lvl = lvl.child_level();
                self.probe_body_var(VarInfo {
                    var_ptr,
                    lvl,
                    classify_info,
                    chunk_type: self.current_chunk_type,
                });
            }
        }
    }

    fn probe_body_var(&mut self, var_info: VarInfo) {
        let term_loc = self.current_chunk_type.to_gen_context(self.current_chunk_num);

        let branch_info_v = self.branch_map.entry(var_info.var_ptr.clone())
            .or_insert_with(|| vec![]);

        let needs_new_branch = if let Some(last_bi) = branch_info_v.last() {
            !self.root_set.contains(&last_bi.branch_num)
        } else {
            true
        };

        if needs_new_branch {
            branch_info_v.push(BranchInfo::new(self.current_branch_num.clone()));
        }

        let branch_info = branch_info_v.last_mut().unwrap();

        let needs_new_chunk = if let Some(last_ci) = branch_info.chunks.last() {
            last_ci.chunk_num != self.current_chunk_num
        } else {
            true
        };

        if needs_new_chunk {
            branch_info.chunks.push(ChunkInfo {
                chunk_num: self.current_chunk_num,
                term_loc,
                vars: vec![],
            });
        }

        let chunk_info = branch_info.chunks.last_mut().unwrap();
        chunk_info.vars.push(var_info);
    }

    fn probe_in_situ_var(&mut self, var_num: usize) {
        let classify_info = ClassifyInfo { arg_c: 1, arity: 1 };

        let var_info = VarInfo {
            var_ptr: VarPtr::from(Var::InSitu(var_num)),
            classify_info,
            chunk_type: self.current_chunk_type,
            lvl: Level::Shallow,
        };

        self.probe_body_var(var_info);
    }

    fn classify_head_variables(&mut self, term: &Term) -> Result<(), CompilationError> {
        match term {
            Term::Clause(..) | Term::Literal(_, Literal::Atom(_)) => {
            }
            _ => return Err(CompilationError::InvalidRuleHead),
        }

        let mut classify_info = ClassifyInfo { arg_c: 1, arity: term.arity() };

        match term {
            Term::Clause(_, _, terms) => {
                for term in terms.into_iter() {
                    for term_ref in breadth_first_iter(term, RootIterationPolicy::Iterated) {
                        if let TermRef::Var(lvl, _, var_ptr) = term_ref {
                            // a body term, so we need the child level here.
                            let lvl = lvl.child_level();

                            // the body of the if let here is an inlined
                            // "probe_head_var". note the difference between it
                            // and "probe_body_var".
                            let branch_info_v = self.branch_map.entry(var_ptr.clone())
                                .or_insert_with(|| vec![]);

                            let needs_new_branch = branch_info_v.is_empty();

                            if needs_new_branch {
                                branch_info_v.push(BranchInfo::new(self.current_branch_num.clone()));
                            }

                            let branch_info = branch_info_v.last_mut().unwrap();
                            let needs_new_chunk = branch_info.chunks.is_empty();

                            if needs_new_chunk {
                                branch_info.chunks.push(ChunkInfo {
                                    chunk_num: self.current_chunk_num,
                                    term_loc: GenContext::Head,
                                    vars: vec![],
                                });
                            }

                            let chunk_info = branch_info.chunks.last_mut().unwrap();
                            let var_info = VarInfo {
                                var_ptr,
                                classify_info,
                                chunk_type: self.current_chunk_type,
                                lvl,
                            };

                            chunk_info.vars.push(var_info);
                        }
                    }

                    classify_info.arg_c += 1;
                }
            }
            _ => {}
        }

        Ok(())
    }

    fn classify_body_variables<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: Term,
    ) -> Result<ChunkedTermVec, CompilationError> {
        let mut state_stack = vec![TraversalState::Term(term)];
        let mut build_stack = ChunkedTermVec::new();

        self.current_chunk_type = ChunkType::Mid;

        while let Some(traversal_st) = state_stack.pop() {
            match traversal_st {
                TraversalState::AddBranchNum(branch_num) => {
                    self.root_set.insert(branch_num.clone());
                    self.current_branch_num = branch_num;
                }
                TraversalState::RemoveBranchNum => {
                    self.root_set.pop();
                }
                TraversalState::RepBranchNum(branch_num) => {
                    self.root_set.pop();
                    self.root_set.insert(branch_num.clone());
                    self.current_branch_num = branch_num;
                }
                TraversalState::ResetCallPolicy(call_policy) => {
                    self.call_policy = call_policy;
                }
                TraversalState::BuildDisjunct(preceding_len) => {
                    flatten_into_disjunct(&mut build_stack, preceding_len);

                    self.current_chunk_type = ChunkType::Mid;
                    self.current_chunk_num += 1;
                }
                TraversalState::BuildFinalDisjunct(preceding_len) => {
                    flatten_into_disjunct(&mut build_stack, preceding_len);

                    self.current_chunk_type = ChunkType::Mid;
                    self.current_chunk_num += 1;
                }
                TraversalState::GetCutPoint { var_num, prev_b } => {
                    if self.try_set_chunk_at_inlined_boundary() {
                        build_stack.add_chunk();
                    }

                    self.probe_in_situ_var(var_num);
                    build_stack.push_chunk_term(QueryTerm::GetCutPoint { var_num, prev_b });
                }
                TraversalState::Cut { var_num, is_global } => {
                    if self.try_set_chunk_at_inlined_boundary() {
                        build_stack.add_chunk();
                    }

                    self.probe_in_situ_var(var_num);

                    build_stack.push_chunk_term(
                        if is_global {
                            QueryTerm::GlobalCut(var_num)
                        } else {
                            QueryTerm::LocalCut(var_num)
                        }
                    );
                }
                TraversalState::Fail => {
                    build_stack.push_chunk_term(QueryTerm::Fail);
                }
                TraversalState::Term(term) => {
                    // return true iff new chunk should be added.
                    let update_chunk_data = |classifier: &mut Self, predicate_name, arity| {
                        if ClauseType::is_inlined(predicate_name, arity) {
                            classifier.try_set_chunk_at_inlined_boundary()
                        } else {
                            classifier.try_set_chunk_at_call_boundary()
                        }
                    };

                    match term {
                        Term::Clause(_, atom!(","), mut terms) if terms.len() == 2 => {
                            let tail = terms.pop().unwrap();
                            let head = terms.pop().unwrap();

                            let iter = unfold_by_str(tail, atom!(","))
                                .into_iter()
                                .rev()
                                .chain(std::iter::once(head))
                                .map(TraversalState::Term);

                            state_stack.extend(iter);
                        }
                        Term::Clause(_, atom!(";"), mut terms) if terms.len() == 2 => {
                            let tail = terms.pop().unwrap();
                            let head = terms.pop().unwrap();

                            let first_branch_num = self.current_branch_num.split();
                            let branches: Vec<_> = std::iter::once(head)
                                .chain(unfold_by_str(tail, atom!(";")).into_iter())
                                .collect();

                            let mut branch_numbers = vec![first_branch_num];

                            for idx in 1 .. branches.len() {
                                let succ_branch_number = branch_numbers[idx - 1].incr_by_delta();

                                branch_numbers.push(if idx + 1 < branches.len() {
                                    succ_branch_number.split()
                                } else {
                                    succ_branch_number
                                });
                            }

                            let build_stack_len = build_stack.len();
                            build_stack.reserve_branch(branches.len());

                            state_stack.push(TraversalState::RepBranchNum(
                                self.current_branch_num.halve_delta(),
                            ));

                            let iter = branches.into_iter().zip(branch_numbers.into_iter());
                            let final_disjunct_loc = state_stack.len();

                            for (term, branch_num) in iter.rev() {
                                state_stack.push(TraversalState::BuildDisjunct(build_stack_len));
                                state_stack.push(TraversalState::RemoveBranchNum);
                                state_stack.push(TraversalState::Term(term));
                                state_stack.push(TraversalState::AddBranchNum(branch_num));
                            }

                            if let TraversalState::BuildDisjunct(build_stack_len) = state_stack[final_disjunct_loc] {
                                state_stack[final_disjunct_loc] = TraversalState::BuildFinalDisjunct(build_stack_len);
                            }

                            self.current_chunk_type = ChunkType::Mid;
                            self.current_chunk_num += 1;
                        }
                        Term::Clause(_, atom!("->"), mut terms) if terms.len() == 2 => {
                            let then_term = terms.pop().unwrap();
                            let if_term = terms.pop().unwrap();

                            let prev_b = if matches!(state_stack.last(), Some(TraversalState::RemoveBranchNum)) {
                                // check if the second-to-last element is a regular BuildDisjunct, as we don't
                                // want to add GetPrevLevel in case of a TrustMe.
                                matches!(state_stack.iter().rev().nth(1), Some(TraversalState::BuildDisjunct(..)))
                            } else {
                                false
                            };

                            state_stack.push(TraversalState::Term(then_term));
                            state_stack.push(TraversalState::Cut { var_num: self.var_num, is_global: false });
                            state_stack.push(TraversalState::Term(if_term));
                            state_stack.push(TraversalState::GetCutPoint { var_num: self.var_num, prev_b });

                            self.var_num += 1;
                        }
                        Term::Clause(_, atom!("\\+"), mut terms) if terms.len() == 1 => {
                            let not_term = terms.pop().unwrap();
                            let build_stack_len = build_stack.len();

                            build_stack.reserve_branch(2);

                            state_stack.push(TraversalState::BuildFinalDisjunct(build_stack_len));
                            state_stack.push(TraversalState::Term(Term::Clause(Cell::default(), atom!("$succeed"), vec![])));
                            state_stack.push(TraversalState::BuildDisjunct(build_stack_len));
                            state_stack.push(TraversalState::Fail);
                            state_stack.push(TraversalState::Cut { var_num: self.var_num, is_global: false });
                            state_stack.push(TraversalState::Term(not_term));
                            state_stack.push(TraversalState::GetCutPoint { var_num: self.var_num, prev_b: true });

                            self.current_chunk_type = ChunkType::Mid;
                            self.current_chunk_num += 1;

                            self.var_num += 1;
                        }
                        Term::Clause(_, atom!(":"), mut terms) if terms.len() == 2 => {
                            let predicate_name = terms.pop().unwrap();
                            let module_name = terms.pop().unwrap();

                            match (module_name, predicate_name) {
                                (
                                    Term::Literal(_, Literal::Atom(module_name)),
                                    Term::Literal(_, Literal::Atom(predicate_name)),
                                ) => {
                                    if update_chunk_data(self, predicate_name, 0) {
                                        build_stack.add_chunk();
                                    }

                                    build_stack.push_chunk_term(
                                        qualified_clause_to_query_term(
                                            loader,
                                            module_name,
                                            predicate_name,
                                            vec![],
                                            self.call_policy,
                                        ),
                                    );
                                }
                                (
                                    Term::Literal(_, Literal::Atom(module_name)),
                                    Term::Clause(_, name, terms),
                                ) => {
                                    if update_chunk_data(self, name, terms.len()) {
                                        build_stack.add_chunk();
                                    }

                                    for (arg_c, term) in terms.iter().enumerate() {
                                        self.probe_body_term(arg_c + 1, terms.len(), term);
                                    }

                                    build_stack.push_chunk_term(
                                        qualified_clause_to_query_term(
                                            loader,
                                            module_name,
                                            name,
                                            terms,
                                            self.call_policy,
                                        ),
                                    );
                                }
                                (module_name, predicate_name) => {
                                    if update_chunk_data(self, atom!("call"), 2) {
                                        build_stack.add_chunk();
                                    }

                                    self.probe_body_term(1, 0, &module_name);
                                    self.probe_body_term(2, 0, &predicate_name);

                                    terms.push(module_name);
                                    terms.push(predicate_name);

                                    build_stack.push_chunk_term(
                                        clause_to_query_term(
                                            loader,
                                            atom!("call"),
                                            vec![Term::Clause(Cell::default(), atom!(":"), terms)],
                                            self.call_policy,
                                        ),
                                    );
                                }
                            }
                        }
                        Term::Clause(_, atom!("$call_with_inference_counting"), mut terms) if terms.len() == 1 => {
                            state_stack.push(TraversalState::ResetCallPolicy(self.call_policy));
                            state_stack.push(TraversalState::Term(terms.pop().unwrap()));

                            self.call_policy = CallPolicy::Counted;
                        }
                        Term::Clause(_, name, terms) => {
                            if update_chunk_data(self, name, terms.len()) {
                                build_stack.add_chunk();
                            }

                            for (arg_c, term) in terms.iter().enumerate() {
                                self.probe_body_term(arg_c + 1, terms.len(), term);
                            }

                            build_stack.push_chunk_term(
                                clause_to_query_term(
                                    loader,
                                    name,
                                    terms,
                                    self.call_policy,
                                ),
                            );
                        }
                        var @ Term::Var(..) => {
                            if update_chunk_data(self, atom!("call"), 1) {
                                build_stack.add_chunk();
                            }

                            self.probe_body_term(1, 1, &var);

                            build_stack.push_chunk_term(
                                clause_to_query_term(
                                    loader,
                                    atom!("call"),
                                    vec![var],
                                    self.call_policy,
                                ),
                            );
                        }
                        Term::Literal(_, Literal::Atom(atom!("!")) | Literal::Char('!')) => {
                            if self.global_cut_var_num.is_none() {
                                self.global_cut_var_num = Some(self.var_num);
                                self.var_num += 1;
                            }

                            self.probe_in_situ_var(self.global_cut_var_num.unwrap());

                            state_stack.push(TraversalState::Cut {
                                var_num: self.global_cut_var_num.unwrap(),
                                is_global: true,
                            });
                        }
                        Term::Literal(_, Literal::Atom(name)) => {
                            if update_chunk_data(self, name, 0) {
                                build_stack.add_chunk();
                            }

                            build_stack.push_chunk_term(
                                clause_to_query_term(
                                    loader,
                                    name,
                                    vec![],
                                    self.call_policy,
                                ),
                            );
                        }
                        _ => {
                            return Err(CompilationError::InadmissibleQueryTerm);
                        }
                    }
                }
            }
        }

        Ok(build_stack)
    }
}

impl BranchMap {
    pub fn separate_and_classify_variables(
        &mut self,
        var_num: usize,
        global_cut_var_num: Option<usize>,
        current_chunk_num: usize,
    ) -> VarData {
        let mut var_data = VarData {
            records: VariableRecords::new(var_num),
            global_cut_var_num,
            allocates: current_chunk_num > 0,
        };

        for (var, branches) in self.iter_mut() {
            let (mut var_num, var_num_incr) =
                if let Var::InSitu(var_num) = *var.borrow() {
                    (var_num, false)
                } else {
                    (var_data.records.len(), true)
                };

            for branch in branches.iter_mut() {
                if var_num_incr {
                    var_num = var_data.records.len();
                    var_data.records.push(VariableRecord::default());
                }

                if branch.chunks.len() <= 1 { // true iff var is a temporary variable.
                    debug_assert_eq!(branch.chunks.len(), 1);

                    let chunk = &mut branch.chunks[0];
                    let mut temp_var_data = TempVarData::new();

                    for var_info in chunk.vars.iter_mut() {
                        if var_info.lvl == Level::Shallow {
                            let term_loc = var_info.chunk_type.to_gen_context(chunk.chunk_num);
                            temp_var_data.use_set.insert((term_loc, var_info.classify_info.arg_c));
                        }
                    }

                    var_data.records[var_num].allocation = VarAlloc::Temp {
                        term_loc: chunk.term_loc,
                        temp_reg: 0,
                        temp_var_data,
                        safety: VarSafetyStatus::Needed,
                        to_perm_var_num: None,
                    };
                } // else VarAlloc is already a Perm variant, as it's the default.

                for chunk in branch.chunks.iter_mut() {
                    var_data.records[var_num].num_occurrences += chunk.vars.len();

                    for var_info in chunk.vars.iter_mut() {
                        var_info.var_ptr.set(Var::Generated(var_num));
                    }
                }
            }
        }

        var_data.records.populate_restricting_sets();
        var_data
    }
}
