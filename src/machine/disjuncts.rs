
/*
================================================================================

This is a disjunction compilation experiment attempting to adapt the
paper "Compiling Large Disjunctions" to Scryer Prolog.

================================================================================
 */

use crate::atom_table::*;
use crate::fixtures::VariableFixtures;
use crate::forms::*;
use crate::instructions::*;
use crate::iterators::*;
use crate::machine::loader::*;
use crate::machine::machine_errors::CompilationError;
use crate::machine::preprocessor::*;
use crate::parser::ast::*;
use crate::parser::rug::Rational;

use indexmap::{IndexMap, IndexSet};

use std::cell::Cell;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)]
struct BranchNumber {
    branch_num: Rational,
    delta: Rational,
}

impl Default for BranchNumber {
    fn default() -> Self {
        Self {
            branch_num: Rational::from(1 << 63),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarInfo {
    var_ptr: VarPtr,
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

type BranchMapInt = IndexMap<Var, Vec<BranchInfo>>;

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
    // the chunk type to that of the chunk preceding the disjunct.
    BuildDisjunct(ChunkType, usize),
    // add the last disjunct to a QueryTerm::Branch, continuing from
    // where it leaves off.
    BuildFinalDisjunct(usize),
    BuildIf(usize, Term), // build the P term of P -> Q
    BuildThen(usize, Vec<QueryTerm>), // build the Q term of P -> Q
    BuildNot(usize), // build the P term of \+ P
    ResetCallPolicy(CallPolicy),
    Term(Term),
    AddBranchNum(BranchNumber), // set current_branch_number, add it to the root set
    RemoveBranchNum, // remove latest branch number from the root set
    RepBranchNum(BranchNumber), // replace current_branch_number and the latest in the root set
    IncrChunkNum, // increment self.current_chunk_number
    SetLastChunkType, // consider remaining terms as belonging to a last chunk
}

impl Term {
    #[inline]
    fn is_var(&self) -> bool {
        if let Term::Var(..) = self {
            true
        } else {
            false
        }
    }

    #[inline]
    fn is_compound(&self) -> bool {
        match self {
            Term::Clause(..) | Term::Cons(..) => true,
            _ => false,
        }
    }
}

pub struct VariableClassifier {
    call_policy: CallPolicy,
    current_branch_num: BranchNumber,
    current_chunk_num: usize,
    branch_map: BranchMap,
    root_set: RootSet,
}

#[derive(Debug)]
pub enum VarClassification {
    Void,
    Temp,
    Perm,
}

pub struct VarRecord {
    pub classification: VarClassification,
    pub chunk_occurrences: Vec<usize>,
    pub num_occurrences: usize,
}

// TODO: already exists a VarData! although it may no longer exist??
// Also, the name is too similar to VarInfo. Think of better names!
pub struct VarData {
    pub records:  Vec<VarRecord>,
    pub fixtures: VariableFixtures,
}

pub type ClassifyFactResult = (Term, VarData);
pub type ClassifyRuleResult = (Term, Vec<QueryTerm>, VarData);

fn merge_branch_seq<Iter: Iterator<Item = BranchInfo>>(branches: Iter) -> BranchInfo {
    let mut branch_info = BranchInfo::new(BranchNumber::default());

    for mut branch in branches {
        branch_info.branch_num = branch.branch_num;

        if let Some(last_chunk) = branch_info.chunks.last_mut() {
            if let Some(first_moved_chunk) = branch.chunks.first_mut() {
                if last_chunk.chunk_num == first_moved_chunk.chunk_num {
                    last_chunk.vars.extend(first_moved_chunk.vars.drain(..));
                    branch_info.chunks.extend(branch.chunks.drain(1 ..));

                    continue;
                }
            }
        }

        branch_info.chunks.extend(branch.chunks.drain(..));
    }

    branch_info.branch_num.delta *= 2;
    branch_info.branch_num.branch_num -= &branch_info.branch_num.delta;

    branch_info
}

fn flatten_into_disjunct(build_stack: &mut Vec<QueryTerm>, preceding_len: usize) {
    let iter = build_stack.drain(preceding_len + 1 ..);

    if let QueryTerm::Branch(ref mut disjuncts) = &mut build_stack[preceding_len] {
        disjuncts.push(iter.collect());
    }
}

fn term_in_other_chunk(term: &Term) -> Option<bool> {
    match term {
        Term::Clause(_, name, terms) => Some(!ClauseType::is_inbuilt(*name, terms.len())),
        Term::Literal(_, Literal::Atom(atom!("!"))) |
        Term::Literal(_, Literal::Char('!')) => Some(false),
        Term::Literal(_, Literal::Atom(name)) => Some(!ClauseType::is_inbuilt(*name, 0)),
        Term::Var(..) => Some(true),
        _ => None,
    }
}

// returns true if the insertion of SetLastChunkType was the final push.
// expects that iter iterates over a conjunct of Terms in reverse order.
fn insert_set_last_chunk_type(
    state_stack: &mut Vec<TraversalState>,
    mut iter: impl Iterator<Item = TraversalState>,
) -> bool {
    let beg = state_stack.len();
    let mut idx = beg;

    while let Some(traversal_st) = iter.next() {
        match traversal_st {
            TraversalState::Term(term) | TraversalState::BuildIf(_, term) => {
                let mut will_break = false;

                match term_in_other_chunk(&term) {
                    Some(true) if idx > beg => will_break = true,
                    Some(_) => idx += 1,
                    None => will_break = true,
                }

                if will_break {
                    state_stack.push(TraversalState::SetLastChunkType);
                    state_stack.push(traversal_st);

                    break;
                } else {
                    state_stack.push(traversal_st);
                }
            }
            _ => {
                unreachable!();
            }
        }
    }

    state_stack.extend(iter);
    idx == state_stack.len()
}

impl VariableClassifier {
    pub fn new(call_policy: CallPolicy) -> Self {
        Self {
            call_policy,
            current_branch_num: BranchNumber::default(),
            current_chunk_num: 0,
            branch_map: BranchMap(BranchMapInt::new()),
            root_set: RootSet::new(),
        }
    }

    pub fn classify_fact(mut self, term: Term) -> Result<ClassifyFactResult, CompilationError> {
        self.classify_head_variables(&term)?;
        Ok((term, self.branch_map.separate_and_classify_variables()))
    }

    pub fn classify_rule<'a, LS: LoadState<'a>>(
        mut self,
        loader: &mut Loader<'a, LS>,
        head: Term,
        body: Term,
    ) -> Result<ClassifyRuleResult, CompilationError> {
        self.classify_head_variables(&head)?;
        let query_terms = self.classify_body_variables(loader, body)?;

        Ok((head, query_terms, self.branch_map.separate_and_classify_variables()))
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

    fn probe_body_term(&mut self, term: &Term, term_loc: GenContext) {
        let mut classify_info = ClassifyInfo { arg_c: 0, arity: term.arity() };

        // second arg is true to iterate the root, which may be a variable
        for term_ref in breadth_first_iter(term, true) {
            if let TermRef::Var(lvl, _, var_name) = term_ref {
                let var_info = VarInfo { var_ptr: VarPtr::from(&var_name), lvl, classify_info };
                self.probe_body_var(var_name, term_loc, var_info);
            }

            if let Level::Shallow = term_ref.level() {
                classify_info.arg_c += 1;
            }
        }
    }

    fn probe_body_var(&mut self, var_name: Var, term_loc: GenContext, var_info: VarInfo) {
        let branch_info_v = self.branch_map.entry(var_name)
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

    fn classify_head_variables(&mut self, term: &Term) -> Result<(), CompilationError> {
        match term {
            Term::Clause(..) | Term::Literal(_, Literal::Atom(_)) => {
            }
            _ => return Err(CompilationError::InvalidRuleHead),
        }

        let mut classify_info = ClassifyInfo {
            arg_c: 0,
            arity: term.arity(),
        };

        // false argument to breadth_first_iter because the root is not iterable.
        for term_ref in breadth_first_iter(term, false) {
            if let TermRef::Var(lvl, _, var_name) = term_ref {
                // the body of the if let here is an inlined
                // "probe_head_var". note the difference between it
                // and "probe_body_var".
                let branch_info_v = self.branch_map.entry(Var::from(var_name))
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
                        vars: vec![]
                    });
                }

                let chunk_info = branch_info.chunks.last_mut().unwrap();
                let var_info = VarInfo { var_ptr: VarPtr::from(&var_name), classify_info, lvl };

                chunk_info.vars.push(var_info);
            }

            if let Level::Shallow = term_ref.level() {
                classify_info.arg_c += 1;
            }
        }

        Ok(())
    }

    fn classify_body_variables<'a, LS: LoadState<'a>>(
        &mut self,
        loader: &mut Loader<'a, LS>,
        term: Term,
    ) -> Result<Vec<QueryTerm>, CompilationError> {
        let mut state_stack = vec![TraversalState::Term(term)];
        let mut build_stack = vec![];
        let mut chunk_type  = ChunkType::Head;

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
                TraversalState::IncrChunkNum => {
                    self.current_chunk_num += 1;
                    chunk_type = ChunkType::Mid;
                    build_stack.push(QueryTerm::ChunkTypeBoundary(chunk_type));
                }
                TraversalState::ResetCallPolicy(call_policy) => {
                    self.call_policy = call_policy;
                }
                TraversalState::SetLastChunkType => {
                    chunk_type = ChunkType::Last;
                    build_stack.push(QueryTerm::ChunkTypeBoundary(chunk_type));
                }
                TraversalState::BuildDisjunct(reset_chunk_type, preceding_len) => {
                    chunk_type = reset_chunk_type;
                    build_stack.push(QueryTerm::ChunkTypeBoundary(chunk_type));
                    flatten_into_disjunct(&mut build_stack, preceding_len);
                }
                TraversalState::BuildFinalDisjunct(preceding_len) => {
                    flatten_into_disjunct(&mut build_stack, preceding_len);
                }
                TraversalState::BuildIf(preceding_len, then_term) => {
                    let iter = build_stack.drain(preceding_len ..);

                    state_stack.push(TraversalState::BuildThen(preceding_len, iter.collect()));
                    state_stack.push(TraversalState::Term(then_term));
                }
                TraversalState::BuildThen(preceding_len, if_terms) => {
                    let iter = build_stack.drain(preceding_len ..);
                    build_stack.push(QueryTerm::IfThen(if_terms, iter.collect()));
                }
                TraversalState::BuildNot(preceding_len) => {
                    let iter = build_stack.drain(preceding_len ..);
                    build_stack.push(QueryTerm::Not(iter.collect()));
                }
                TraversalState::Term(term) => {
                    match term {
                        Term::Clause(_, atom!(","), terms) if terms.len() == 2 => {
                            let iter = unfold_by_str(terms[1], atom!(","))
                                .into_iter()
                                .rev()
                                .chain(std::iter::once(terms[0]))
                                .map(TraversalState::Term);

                            if let ChunkType::Last = chunk_type {
                                if !insert_set_last_chunk_type(&mut state_stack, iter) {
                                    chunk_type = ChunkType::Mid;
                                }
                            } else {
                                state_stack.extend(iter);
                            }
                        }
                        Term::Clause(_, atom!(";"), terms) if terms.len() == 2 => {
                            let first_branch_num = self.current_branch_num.split();
                            let branches: Vec<_> = std::iter::once(terms[0])
                                .chain(unfold_by_str(terms[1], atom!(";")).into_iter())
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
                            build_stack.push(QueryTerm::Branch(Vec::with_capacity(branches.len())));

                            state_stack.push(TraversalState::RepBranchNum(
                                self.current_branch_num.halve_delta(),
                            ));

                            let iter = branches.into_iter().zip(branch_numbers.into_iter());
                            let final_disjunct_loc = state_stack.len();

                            for (term, branch_num) in iter.rev() {
                                state_stack.push(TraversalState::BuildDisjunct(chunk_type, build_stack_len));

                                state_stack.push(TraversalState::RemoveBranchNum);
                                state_stack.push(TraversalState::Term(term));
                                state_stack.push(TraversalState::AddBranchNum(branch_num));
                            }

                            state_stack[final_disjunct_loc] =
                                TraversalState::BuildFinalDisjunct(build_stack_len);
                        }
                        Term::Clause(_, atom!("->"), mut terms) if terms.len() == 2 => {
                            let then_term = terms.pop().unwrap();
                            let if_term = terms.pop().unwrap();

                            let build_stack_len = build_stack.len();

                            // TODO: insert GetLevelAndUnify between
                            // the two traversal states and detect
                            // that as a chunk boundary in
                            // insert_set_last_chunk_type ??

                            let iter = vec![TraversalState::BuildIf(build_stack_len, then_term),
                                            TraversalState::Term(if_term)]
                                .into_iter();

                            if let ChunkType::Last = chunk_type {
                                if !insert_set_last_chunk_type(&mut state_stack, iter) {
                                    chunk_type = ChunkType::Mid;
                                }
                            }
                        }
                        Term::Clause(_, atom!("\\+"), terms) if terms.len() == 1 => {
                            let build_stack_len = build_stack.len();

                            state_stack.push(TraversalState::BuildNot(build_stack_len));
                            state_stack.push(TraversalState::Term(terms[0]));
                        }
                        Term::Clause(_, atom!("$get_level"), terms) if terms.len() == 1 => {
                            state_stack.push(TraversalState::IncrChunkNum);

                            // TODO: need to classify this variable?
                            // what is the difference between $get_cp and this exactly?
                            if let Term::Var(_, ref var) = &terms[0] {
                                build_stack.push(
                                    QueryTerm::GetLevelAndUnify(
                                        Cell::default(),
                                        var.clone(),
                                    ),
                                );
                            } else {
                                return Err(CompilationError::InadmissibleQueryTerm);
                            }
                        }
                        Term::Clause(_, atom!(":"), mut terms) if terms.len() == 2 => {
                            let term_loc = chunk_type.to_gen_context(self.current_chunk_num);

                            let predicate_name = terms.pop().unwrap();
                            let module_name = terms.pop().unwrap();

                            match (module_name, predicate_name) {
                                (
                                    Term::Literal(_, Literal::Atom(module_name)),
                                    Term::Literal(_, Literal::Atom(predicate_name)),
                                ) => {
                                    if !ClauseType::is_inbuilt(predicate_name, 0) {
                                        state_stack.push(TraversalState::IncrChunkNum);
                                    }

                                    build_stack.push(
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
                                    if !ClauseType::is_inbuilt(name, terms.len()) {
                                        state_stack.push(TraversalState::IncrChunkNum);
                                    }

                                    for term in terms.iter() {
                                        self.probe_body_term(term, term_loc);
                                    }

                                    build_stack.push(
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
                                    state_stack.push(TraversalState::IncrChunkNum);

                                    self.probe_body_term(&module_name, term_loc);
                                    self.probe_body_term(&predicate_name, term_loc);

                                    terms.push(module_name);
                                    terms.push(predicate_name);

                                    build_stack.push(
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
                        Term::Clause(cell, atom!("$call_with_inference_counting"), terms) if terms.len() == 1 => {
                            let term_loc = chunk_type.to_gen_context(self.current_chunk_num);

                            for term in terms.iter() {
                                self.probe_body_term(term, term_loc);
                            }

                            state_stack.push(TraversalState::ResetCallPolicy(self.call_policy));
                            state_stack.push(TraversalState::Term(terms[0]));

                            self.call_policy = CallPolicy::Counted;
                        }
                        Term::Clause(cell, name, terms) => {
                            if !ClauseType::is_inbuilt(name, terms.len()) {
                                state_stack.push(TraversalState::IncrChunkNum);
                            }

                            let term_loc = chunk_type.to_gen_context(self.current_chunk_num);

                            for term in terms.iter() {
                                self.probe_body_term(term, term_loc);
                            }

                            build_stack.push(
                                clause_to_query_term(
                                    loader,
                                    name,
                                    terms,
                                    self.call_policy,
                                ),
                            );
                        }
                        Term::Literal(_, Literal::Atom(atom!("!"))) |
                        Term::Literal(_, Literal::Char('!')) => {
                            build_stack.push(QueryTerm::Cut);
                        }
                        Term::Literal(cell, Literal::Atom(name)) => {
                            if !ClauseType::is_inbuilt(name, 0) {
                                state_stack.push(TraversalState::IncrChunkNum);
                            }

                            build_stack.push(
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
    pub fn separate_and_classify_variables(&mut self) -> VarData {
        let mut var_num  = 0usize;
        let mut var_data = VarData {
            records:  vec![],
            fixtures: VariableFixtures::new(),
        };

        for branches in self.values_mut() {
            for branch in branches.iter_mut() {
                let mut num_occurrences = 0;
                let mut chunk_occurrences = vec![];

                let classification = if branch.chunks.len() > 1 {
                    VarClassification::Perm
                } else {
                    branch.chunks
                        .first()
                        .map(|chunk| if chunk.vars.len() > 1 {
                            VarClassification::Temp
                        } else {
                            VarClassification::Void
                        })
                        .unwrap_or(VarClassification::Void)
                };

                for chunk in branch.chunks.iter_mut() {
                    num_occurrences += chunk.vars.len();

                    if let VarClassification::Temp = classification {
                        for var_info in chunk.vars.iter_mut() {
                            var_info.var_ptr.set(Var::Generated(var_num));
                            var_data.fixtures.mark_temp_var(
                                var_num,
                                var_info.lvl,
                                &var_info.classify_info,
                                chunk.term_loc,
                            );
                        }
                    } else {
                        for var_info in chunk.vars.iter_mut() {
                            var_info.var_ptr.set(Var::Generated(var_num));
                        }
                    }

                    chunk_occurrences.push(chunk.chunk_num);
                }

                let record = VarRecord { classification, chunk_occurrences, num_occurrences };
                var_data.records.push(record);

                var_num += 1;
            }
        }

        debug_assert_eq!(var_data.records.len(), var_num);

        var_data.fixtures.populate_restricting_sets();
        var_data
    }
}
