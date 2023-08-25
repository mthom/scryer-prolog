use crate::atom_table::*;
use crate::forms::*;
use crate::instructions::*;
use crate::parser::ast::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::iter::*;
use std::vec::Vec;

#[derive(Debug, Clone)]
pub(crate) enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Literal(Level, &'a Cell<RegType>, &'a Literal),
    Clause(Level, &'a Cell<RegType>, Atom, &'a Vec<Term>),
    PartialString(Level, &'a Cell<RegType>, &'a String, &'a Box<Term>),
    CompleteString(Level, &'a Cell<RegType>, Atom),
    Var(Level, &'a Cell<VarReg>, VarPtr),
}

/*
impl<'a> TermRef<'a> {
    pub(crate) fn level(&self) -> Level {
        match self {
            TermRef::AnonVar(lvl) |
            TermRef::Cons(lvl, ..) |
            TermRef::Literal(lvl, ..) |
            TermRef::Var(lvl, ..) |
            TermRef::Clause(lvl, ..) |
            TermRef::CompleteString(lvl, ..) |
            TermRef::PartialString(lvl, ..) => *lvl,
        }
    }
}
*/

#[derive(Debug)]
pub(crate) enum TermIterState<'a> {
    AnonVar(Level),
    Clause(Level, usize, &'a Cell<RegType>, Atom, &'a Vec<Term>),
    Literal(Level, &'a Cell<RegType>, &'a Literal),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    InitialPartialString(Level, &'a Cell<RegType>, &'a String, &'a Box<Term>),
    FinalPartialString(Level, &'a Cell<RegType>, &'a String, &'a Box<Term>),
    CompleteString(Level, &'a Cell<RegType>, Atom),
    Var(Level, &'a Cell<VarReg>, VarPtr),
}

impl<'a> TermIterState<'a> {
    pub(crate) fn subterm_to_state(lvl: Level, term: &'a Term) -> TermIterState<'a> {
        match term {
            Term::AnonVar => TermIterState::AnonVar(lvl),
            Term::Clause(cell, name, subterms) => {
                TermIterState::Clause(lvl, 0, cell, *name, subterms)
            }
            Term::Cons(cell, head, tail) => {
                TermIterState::InitialCons(lvl, cell, head.as_ref(), tail.as_ref())
            }
            Term::Literal(cell, constant) => TermIterState::Literal(lvl, cell, constant),
            Term::PartialString(cell, string_buf, tail) => {
                TermIterState::InitialPartialString(lvl, cell, string_buf, tail)
            }
            Term::CompleteString(cell, atom) => TermIterState::CompleteString(lvl, cell, *atom),
            Term::Var(cell, var_ptr) => TermIterState::Var(lvl, cell, var_ptr.clone()),
        }
    }
}

#[derive(Debug)]
pub(crate) struct QueryIterator<'a> {
    state_stack: Vec<TermIterState<'a>>,
}

impl<'a> QueryIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack
            .push(TermIterState::subterm_to_state(lvl, term));
    }

    /*
    fn from_rule_head_clause(terms: &'a Vec<Term>) -> Self {
        let state_stack = terms
            .iter()
            .rev()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt))
            .collect();

        QueryIterator { state_stack }
    }
    */

    fn from_term(term: &'a Term) -> Self {
        let state = match term {
            Term::AnonVar
            | Term::Cons(..)
            | Term::Literal(..)
            | Term::PartialString(..)
            | Term::CompleteString(..) => {
                return QueryIterator {
                    state_stack: vec![],
                }
            }
            Term::Clause(r, name, terms) => TermIterState::Clause(Level::Root, 0, r, *name, terms),
            Term::Var(cell, var_ptr) => TermIterState::Var(Level::Root, cell, var_ptr.clone()),
        };

        QueryIterator {
            state_stack: vec![state],
        }
    }

    fn extend_state(&mut self, lvl: Level, term: &'a QueryTerm) {
        match term {
            &QueryTerm::Clause(ref cell, ClauseType::CallN(_), ref terms, _) => {
                self.state_stack
                    .push(TermIterState::Clause(lvl, 1, cell, atom!("$call"), terms));
            }
            &QueryTerm::Clause(ref cell, ref ct, ref terms, _) => {
                self.state_stack
                    .push(TermIterState::Clause(lvl, 0, cell, ct.name(), terms));
            }
            _ => {}
        }
    }

    pub fn new(term: &'a QueryTerm) -> Self {
        let mut iter = QueryIterator {
            state_stack: vec![],
        };
        iter.extend_state(Level::Root, term);
        iter
    }
}

impl<'a> Iterator for QueryIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                TermIterState::AnonVar(lvl) => {
                    return Some(TermRef::AnonVar(lvl));
                }
                TermIterState::Clause(lvl, child_num, cell, name, child_terms) => {
                    if child_num == child_terms.len() {
                        match name {
                            atom!("$call") if lvl == Level::Root => {
                                self.push_subterm(Level::Shallow, &child_terms[0]);
                            }
                            _ => {
                                return match lvl {
                                    Level::Root => None,
                                    lvl => Some(TermRef::Clause(lvl, cell, name, child_terms)),
                                }
                            }
                        };
                    } else {
                        self.state_stack.push(TermIterState::Clause(
                            lvl,
                            child_num + 1,
                            cell,
                            name,
                            child_terms,
                        ));

                        self.push_subterm(lvl.child_level(), &child_terms[child_num]);
                    }
                }
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    self.state_stack
                        .push(TermIterState::FinalCons(lvl, cell, head, tail));

                    self.push_subterm(lvl.child_level(), tail);
                    self.push_subterm(lvl.child_level(), head);
                }
                TermIterState::InitialPartialString(lvl, cell, string, tail) => {
                    self.state_stack
                        .push(TermIterState::FinalPartialString(lvl, cell, string, tail));
                    self.push_subterm(lvl.child_level(), tail);
                }
                TermIterState::FinalPartialString(lvl, cell, atom, tail) => {
                    return Some(TermRef::PartialString(lvl, cell, atom, tail));
                }
                TermIterState::CompleteString(lvl, cell, atom) => {
                    return Some(TermRef::CompleteString(lvl, cell, atom));
                }
                TermIterState::FinalCons(lvl, cell, head, tail) => {
                    return Some(TermRef::Cons(lvl, cell, head, tail));
                }
                TermIterState::Literal(lvl, cell, constant) => {
                    return Some(TermRef::Literal(lvl, cell, constant));
                }
                TermIterState::Var(lvl, cell, var_ptr) => {
                    return Some(TermRef::Var(lvl, cell, var_ptr));
                }
            };
        }

        None
    }
}

#[derive(Debug)]
pub(crate) struct FactIterator<'a> {
    state_queue: VecDeque<TermIterState<'a>>,
    iterable_root: RootIterationPolicy,
}

impl<'a> FactIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_queue
            .push_back(TermIterState::subterm_to_state(lvl, term));
    }

    pub(crate) fn from_rule_head_clause(terms: &'a Vec<Term>) -> Self {
        let state_queue = terms
            .iter()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt))
            .collect();

        FactIterator {
            state_queue,
            iterable_root: RootIterationPolicy::NotIterated,
        }
    }

    fn new(term: &'a Term, iterable_root: RootIterationPolicy) -> Self {
        let states = match term {
            Term::AnonVar => {
                vec![TermIterState::AnonVar(Level::Root)]
            }
            Term::Clause(cell, name, terms) => {
                vec![TermIterState::Clause(Level::Root, 0, cell, *name, terms)]
            }
            Term::Cons(cell, head, tail) => vec![TermIterState::InitialCons(
                Level::Root,
                cell,
                head.as_ref(),
                tail.as_ref(),
            )],
            Term::PartialString(cell, string_buf, tail) => {
                vec![TermIterState::InitialPartialString(
                    Level::Root,
                    cell,
                    string_buf,
                    tail,
                )]
            }
            Term::CompleteString(cell, atom) => {
                vec![TermIterState::CompleteString(Level::Root, cell, *atom)]
            }
            Term::Literal(cell, constant) => {
                vec![TermIterState::Literal(Level::Root, cell, constant)]
            }
            Term::Var(cell, var_ptr) => {
                vec![TermIterState::Var(Level::Root, cell, var_ptr.clone())]
            }
        };

        FactIterator {
            state_queue: VecDeque::from(states),
            iterable_root,
        }
    }
}

impl<'a> Iterator for FactIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.state_queue.pop_front() {
            match state {
                TermIterState::AnonVar(lvl) => {
                    return Some(TermRef::AnonVar(lvl));
                }
                TermIterState::Clause(lvl, _, cell, name, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(lvl.child_level(), child_term);
                    }

                    match lvl {
                        Level::Root if !self.iterable_root.iterable() => continue,
                        _ => return Some(TermRef::Clause(lvl, cell, name, child_terms)),
                    };
                }
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    self.push_subterm(Level::Deep, head);
                    self.push_subterm(Level::Deep, tail);

                    return Some(TermRef::Cons(lvl, cell, head, tail));
                }
                TermIterState::InitialPartialString(lvl, cell, string_buf, tail) => {
                    self.push_subterm(Level::Deep, tail);
                    return Some(TermRef::PartialString(lvl, cell, string_buf, tail));
                }
                TermIterState::CompleteString(lvl, cell, atom) => {
                    return Some(TermRef::CompleteString(lvl, cell, atom));
                }
                TermIterState::Literal(lvl, cell, constant) => {
                    return Some(TermRef::Literal(lvl, cell, constant))
                }
                TermIterState::Var(lvl, cell, var_ptr) => {
                    return Some(TermRef::Var(lvl, cell, var_ptr));
                }
                _ => {}
            }
        }

        None
    }
}

pub(crate) fn post_order_iter<'a>(term: &'a Term) -> QueryIterator<'a> {
    QueryIterator::from_term(term)
}

pub(crate) fn breadth_first_iter<'a>(
    term: &'a Term,
    iterable_root: RootIterationPolicy,
) -> FactIterator<'a> {
    FactIterator::new(term, iterable_root)
}

#[derive(Debug, Copy, Clone)]
enum ClauseIteratorState<'a> {
    RemainingChunks(&'a VecDeque<ChunkedTerms>, usize),
    RemainingBranches(&'a Vec<VecDeque<ChunkedTerms>>, usize),
}

#[derive(Debug, Clone)]
pub(crate) enum ClauseItem<'a> {
    FirstBranch(usize),
    NextBranch,
    BranchEnd(usize),
    Chunk(&'a VecDeque<QueryTerm>),
}

#[derive(Debug)]
pub(crate) struct ClauseIterator<'a> {
    state_stack: Vec<ClauseIteratorState<'a>>,
    remaining_chunks_on_stack: usize,
}

fn state_from_chunked_terms<'a>(chunk_vec: &'a VecDeque<ChunkedTerms>) -> ClauseIteratorState<'a> {
    if chunk_vec.len() == 1 {
        if let Some(ChunkedTerms::Branch(ref branches)) = chunk_vec.front() {
            return ClauseIteratorState::RemainingBranches(branches, 0);
        }
    }

    ClauseIteratorState::RemainingChunks(chunk_vec, 0)
}

impl<'a> ClauseIterator<'a> {
    pub fn new(clauses: &'a ChunkedTermVec) -> Self {
        match state_from_chunked_terms(&clauses.chunk_vec) {
            state @ ClauseIteratorState::RemainingBranches(..) => Self {
                state_stack: vec![state],
                remaining_chunks_on_stack: 0,
            },
            state @ ClauseIteratorState::RemainingChunks(..) => Self {
                state_stack: vec![state],
                remaining_chunks_on_stack: 1,
            },
        }
    }

    #[inline(always)]
    pub fn in_tail_position(&self) -> bool {
        self.remaining_chunks_on_stack == 0
    }

    fn branch_end_depth(&mut self) -> usize {
        let mut depth = 1;

        while let Some(state) = self.state_stack.pop() {
            match state {
                ClauseIteratorState::RemainingBranches(terms, focus) if terms.len() == focus => {
                    depth += 1;
                }
                _ => {
                    self.state_stack.push(state);
                    break;
                }
            }
        }

        depth
    }
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = ClauseItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.state_stack.pop() {
            match state {
                ClauseIteratorState::RemainingChunks(chunks, focus) if focus < chunks.len() => {
                    if focus + 1 < chunks.len() {
                        self.state_stack
                            .push(ClauseIteratorState::RemainingChunks(chunks, focus + 1));
                    } else {
                        self.remaining_chunks_on_stack -= 1;
                    }

                    match &chunks[focus] {
                        ChunkedTerms::Branch(branches) => {
                            self.state_stack
                                .push(ClauseIteratorState::RemainingBranches(branches, 0));
                        }
                        ChunkedTerms::Chunk(chunk) => {
                            return Some(ClauseItem::Chunk(chunk));
                        }
                    }
                }
                ClauseIteratorState::RemainingChunks(chunks, focus) => {
                    debug_assert_eq!(chunks.len(), focus);
                }
                ClauseIteratorState::RemainingBranches(branches, focus)
                    if focus < branches.len() =>
                {
                    self.state_stack
                        .push(ClauseIteratorState::RemainingBranches(&branches, focus + 1));
                    let state = state_from_chunked_terms(&branches[focus]);

                    if let ClauseIteratorState::RemainingChunks(..) = &state {
                        self.remaining_chunks_on_stack += 1;
                    }

                    self.state_stack.push(state);

                    return if focus == 0 {
                        Some(ClauseItem::FirstBranch(branches.len()))
                    } else {
                        Some(ClauseItem::NextBranch)
                    };
                }
                ClauseIteratorState::RemainingBranches(branches, focus) => {
                    debug_assert_eq!(branches.len(), focus);
                    return Some(ClauseItem::BranchEnd(self.branch_end_depth()));
                }
            }
        }

        None
    }
}
