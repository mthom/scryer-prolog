use crate::atom_table::*;
use crate::forms::*;
use crate::instructions::*;
use crate::parser::ast::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Debug;
use std::hash::{Hash};
use std::iter::*;
use std::vec::Vec;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct VarPtr {
    ptr: std::ptr::NonNull<Var>,
}

impl From<&Var> for VarPtr {
    #[inline]
    fn from(value: &Var) -> VarPtr {
        unsafe {
            VarPtr { ptr: std::ptr::NonNull::new_unchecked(value as *const _ as *mut _) }
        }
    }
}

impl From<VarPtr> for Var {
    #[inline]
    fn from(value: VarPtr) -> Var {
        unsafe {
            (*value.ptr.as_ptr()).clone()
        }
    }
}

impl VarPtr {
    pub(crate) fn set(&mut self, value: Var) {
        unsafe { *self.ptr.as_mut() = value; }
    }
}


#[derive(Debug, Clone)]
pub(crate) enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Literal(Level, &'a Cell<RegType>, &'a Literal),
    Clause(Level, &'a Cell<RegType>, Atom, &'a Vec<Term>),
    PartialString(Level, &'a Cell<RegType>, &'a String, &'a Box<Term>),
    CompleteString(Level, &'a Cell<RegType>, Atom),
    Var(Level, &'a Cell<VarReg>, Var),
}

impl<'a> TermRef<'a> {
    pub(crate) fn level(self) -> Level {
        match self {
            TermRef::AnonVar(lvl)
            | TermRef::Cons(lvl, ..)
            | TermRef::Literal(lvl, ..)
            | TermRef::Var(lvl, ..)
            | TermRef::Clause(lvl, ..)
            | TermRef::CompleteString(lvl, ..)
            | TermRef::PartialString(lvl, ..) => lvl,
        }
    }
}

#[derive(Debug)]
pub(crate) enum TermIterState<'a> {
    AnonVar(Level),
    Literal(Level, &'a Cell<RegType>, &'a Literal),
    Clause(Level, usize, &'a Cell<RegType>, Atom, &'a Vec<Term>),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    InitialPartialString(Level, &'a Cell<RegType>, &'a String, &'a Box<Term>),
    FinalPartialString(Level, &'a Cell<RegType>, &'a String, &'a Box<Term>),
    CompleteString(Level, &'a Cell<RegType>, Atom),
    UnblockedCut(Level, &'a Cell<VarReg>),
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
            Term::CompleteString(cell, atom) => {
                TermIterState::CompleteString(lvl, cell, *atom)
            }
            Term::Var(cell, var) => TermIterState::Var(lvl, cell, VarPtr::from(var)),
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

    fn from_rule_head_clause(terms: &'a Vec<Term>) -> Self {
        let state_stack = terms
            .iter()
            .rev()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt))
            .collect();

        QueryIterator { state_stack }
    }

    fn from_term(term: &'a Term) -> Self {
        let state = match term {
            Term::AnonVar | Term::Cons(..) | Term::Literal(..) |
            Term::PartialString(..) | Term::CompleteString(..) => {
                return QueryIterator {
                    state_stack: vec![],
                }
            }
            Term::Clause(r, name, terms) => TermIterState::Clause(
                Level::Root,
                0,
                r,
                *name,
                terms,
            ),
            Term::Var(cell, var) => TermIterState::Var(Level::Root, cell, VarPtr::from(var)),
        };

        QueryIterator {
            state_stack: vec![state],
        }
    }

    fn new(term: &'a QueryTerm) -> Self {
        match term {
            &QueryTerm::Clause(ref cell, ClauseType::CallN(_), ref terms, _) => {
                let state = TermIterState::Clause(Level::Root, 1, cell, atom!("$call"), terms);
                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::Clause(ref cell, ref ct, ref terms, _) => {
                let state = TermIterState::Clause(Level::Root, 0, cell, ct.name(), terms);
                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::UnblockedCut(ref cell) => {
                let state = TermIterState::UnblockedCut(Level::Root, cell);

                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::GetLevelAndUnify(ref cell, ref var) => {
                let state = TermIterState::Var(Level::Root, cell, VarPtr::from(var));
                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::Jump(ref vars) => {
                let state_stack = vars
                    .iter()
                    .rev()
                    .map(|t| TermIterState::subterm_to_state(Level::Shallow, t))
                    .collect();

                QueryIterator { state_stack }
            }
            &QueryTerm::BlockedCut => QueryIterator {
                state_stack: vec![],
            },
        }
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
                    self.state_stack.push(TermIterState::FinalCons(lvl, cell, head, tail));

                    self.push_subterm(lvl.child_level(), tail);
                    self.push_subterm(lvl.child_level(), head);
                }
                TermIterState::InitialPartialString(lvl, cell, string, tail) => {
                    self.state_stack.push(TermIterState::FinalPartialString(lvl, cell, string, tail));
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
                TermIterState::Var(lvl, cell, var) => {
                    return Some(TermRef::Var(lvl, cell, Var::from(var)));
                }
                TermIterState::UnblockedCut(lvl, cell) => {
                    return Some(TermRef::Var(lvl, cell, Var::from("!")));
                }
            };
        }

        None
    }
}

#[derive(Debug)]
pub(crate) struct FactIterator<'a> {
    state_queue: VecDeque<TermIterState<'a>>,
    iterable_root: bool,
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
            iterable_root: false,
        }
    }

    fn new(term: &'a Term, iterable_root: bool) -> Self {
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
                vec![TermIterState::CompleteString(
                    Level::Root,
                    cell,
                    *atom,
                )]
            }
            Term::Literal(cell, constant) => {
                vec![TermIterState::Literal(Level::Root, cell, constant)]
            }
            Term::Var(cell, var) => {
                vec![TermIterState::Var(Level::Root, cell, VarPtr::from(var))]
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
                        Level::Root if !self.iterable_root => continue,
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
                TermIterState::Var(lvl, cell, var) => {
                    return Some(TermRef::Var(lvl, cell, Var::from(var)));
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

pub(crate) fn breadth_first_iter<'a>(term: &'a Term, iterable_root: bool) -> FactIterator<'a> {
    FactIterator::new(term, iterable_root)
}

#[derive(Debug)]
pub(crate) enum ChunkedTerm<'a> {
    HeadClause(Atom, &'a Vec<Term>),
    BodyTerm(&'a QueryTerm),
}

pub(crate) fn query_term_post_order_iter<'a>(query_term: &'a QueryTerm) -> QueryIterator<'a> {
    QueryIterator::new(query_term)
}

impl<'a> ChunkedTerm<'a> {
    pub(crate) fn post_order_iter(&self) -> QueryIterator<'a> {
        match self {
            &ChunkedTerm::BodyTerm(qt) => QueryIterator::new(qt),
            &ChunkedTerm::HeadClause(_, terms) => QueryIterator::from_rule_head_clause(terms),
        }
    }
}

fn contains_cut_var<'a, Iter: Iterator<Item = &'a Term>>(terms: Iter) -> bool {
    for term in terms {
        if let &Term::Var(_, ref var) = term {
            if var.as_str() == Some("!") {
                return true;
            }
        }
    }

    false
}

pub(crate) struct ChunkedIterator<'a> {
    pub(crate) chunk_num: usize,
    iter: Box<dyn Iterator<Item = ChunkedTerm<'a>> + 'a>,
    deep_cut_encountered: bool,
    cut_var_in_head: bool,
}

impl<'a> fmt::Debug for ChunkedIterator<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("ChunkedIterator")
            .field("chunk_num", &self.chunk_num)
            // Hacky solution.
            .field("iter", &"Box<dyn Iterator<Item = ChunkedTerm<'a>> + 'a>")
            .field("deep_cut_encountered", &self.deep_cut_encountered)
            .field("cut_var_in_head", &self.cut_var_in_head)
            .finish()
    }
}

type ChunkedIteratorItem<'a> = (usize, usize, Vec<ChunkedTerm<'a>>);
type RuleBodyIteratorItem<'a> = (usize, usize, Vec<&'a QueryTerm>);

impl<'a> ChunkedIterator<'a> {
    pub(crate) fn rule_body_iter(self) -> Box<dyn Iterator<Item = RuleBodyIteratorItem<'a>> + 'a> {
        Box::new(self.filter_map(|(cn, lt_arity, terms)| {
            let filtered_terms: Vec<_> = terms
                .into_iter()
                .filter_map(|ct| match ct {
                    ChunkedTerm::BodyTerm(qt) => Some(qt),
                    _ => None,
                })
                .collect();

            if filtered_terms.is_empty() {
                None
            } else {
                Some((cn, lt_arity, filtered_terms))
            }
        }))
    }

    pub(crate) fn from_rule_body(p1: &'a QueryTerm, clauses: &'a Vec<QueryTerm>) -> Self {
        let inner_iter = Box::new(once(ChunkedTerm::BodyTerm(p1)));
        let iter = inner_iter.chain(clauses.iter().map(|t| ChunkedTerm::BodyTerm(t)));

        ChunkedIterator {
            chunk_num: 0,
            iter: Box::new(iter),
            deep_cut_encountered: false,
            cut_var_in_head: false,
        }
    }

    pub(crate) fn from_rule(rule: &'a Rule) -> Self {
        let &Rule {
            head: (ref name, ref args, ref p1),
            ref clauses,
        } = rule;

        let iter = once(ChunkedTerm::HeadClause(name.clone(), args));
        let inner_iter = Box::new(once(ChunkedTerm::BodyTerm(p1)));
        let iter = iter.chain(inner_iter.chain(clauses.iter().map(|t| ChunkedTerm::BodyTerm(t))));

        ChunkedIterator {
            chunk_num: 0,
            iter: Box::new(iter),
            deep_cut_encountered: false,
            cut_var_in_head: false,
        }
    }

    pub(crate) fn encountered_deep_cut(&self) -> bool {
        self.deep_cut_encountered
    }

    fn take_chunk(&mut self, term: ChunkedTerm<'a>) -> (usize, usize, Vec<ChunkedTerm<'a>>) {
        let mut arity = 0;
        let mut item = Some(term);
        let mut result = Vec::new();

        while let Some(term) = item {
            match term {
                ChunkedTerm::HeadClause(_, terms) => {
                    if contains_cut_var(terms.iter()) {
                        self.cut_var_in_head = true;
                    }

                    result.push(term);
                }
                ChunkedTerm::BodyTerm(&QueryTerm::Jump(ref vars)) => {
                    result.push(term);
                    arity = vars.len();

                    if contains_cut_var(vars.iter()) && !self.cut_var_in_head {
                        self.deep_cut_encountered = true;
                    }

                    break;
                }
                ChunkedTerm::BodyTerm(&QueryTerm::BlockedCut) => {
                    result.push(term);

                    if self.chunk_num > 0 {
                        self.deep_cut_encountered = true;
                    }
                }
                ChunkedTerm::BodyTerm(&QueryTerm::GetLevelAndUnify(..)) => {
                    self.deep_cut_encountered = true;

                    result.push(term);
                    arity = 1;
                    break;
                }
                ChunkedTerm::BodyTerm(&QueryTerm::UnblockedCut(..)) => {
                    self.deep_cut_encountered = true;
                    result.push(term);
                }
                ChunkedTerm::BodyTerm(&QueryTerm::Clause(_, ClauseType::Inlined(_), ..)) => {
                    result.push(term)
                }
                ChunkedTerm::BodyTerm(&QueryTerm::Clause(
                    _,
                    ClauseType::CallN(_),
                    ref subterms,
                    _,
                )) => {
                    result.push(term);
                    arity = subterms.len() + 1;
                    break;
                }
                ChunkedTerm::BodyTerm(qt) => {
                    result.push(term);
                    arity = qt.arity();
                    break;
                }
            };

            item = self.iter.next();
        }

        let chunk_num = self.chunk_num;
        self.chunk_num += 1;

        (chunk_num, arity, result)
    }
}

impl<'a> Iterator for ChunkedIterator<'a> {
    // the chunk number, last term arity, and vector of references.
    type Item = ChunkedIteratorItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|term| self.take_chunk(term))
    }
}
