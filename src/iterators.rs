use prolog_parser::ast::*;
use prolog_parser::rc_atom;

use crate::clause_types::*;
use crate::forms::*;
use crate::machine::machine_indices::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::fmt;
use std::iter::*;
use std::rc::Rc;
use std::vec::Vec;

#[derive(Debug, Clone)]
pub enum TermRef<'a> {
    AnonVar(Level),
    Cons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(Level, &'a Cell<RegType>, ClauseType, &'a Vec<Box<Term>>),
    PartialString(Level, &'a Cell<RegType>, String, Option<&'a Term>),
    Var(Level, &'a Cell<VarReg>, Rc<Var>),
}

impl<'a> TermRef<'a> {
    pub fn level(self) -> Level {
        match self {
            TermRef::AnonVar(lvl)
            | TermRef::Cons(lvl, ..)
            | TermRef::Constant(lvl, ..)
            | TermRef::Var(lvl, ..)
            | TermRef::Clause(lvl, ..) => lvl,
            TermRef::PartialString(lvl, ..) => lvl,
        }
    }
}

#[derive(Debug)]
pub enum TermIterState<'a> {
    AnonVar(Level),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    Clause(
        Level,
        usize,
        &'a Cell<RegType>,
        ClauseType,
        &'a Vec<Box<Term>>,
    ),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    PartialString(Level, &'a Cell<RegType>, String, Option<&'a Term>),
    Var(Level, &'a Cell<VarReg>, Rc<Var>),
}

fn is_partial_string<'a>(head: &'a Term, mut tail: &'a Term) -> Option<(String, Option<&'a Term>)> {
    let mut string = match head {
        &Term::Constant(_, Constant::Atom(ref atom, _)) if atom.is_char() => {
            atom.as_str().chars().next().unwrap().to_string()
        }
        &Term::Constant(_, Constant::Char(c)) => c.to_string(),
        _ => {
            return None;
        }
    };

    while let Term::Cons(_, ref head, ref succ) = tail {
        match head.as_ref() {
            &Term::Constant(_, Constant::Atom(ref atom, _)) if atom.is_char() => {
                string.push(atom.as_str().chars().next().unwrap());
            }
            &Term::Constant(_, Constant::Char(c)) => {
                string.push(c);
            }
            _ => {
                return None;
            }
        };

        tail = succ.as_ref();
    }

    match tail {
        Term::AnonVar | Term::Var(..) => {
            return Some((string, Some(tail)));
        }
        Term::Constant(_, Constant::EmptyList) => {
            return Some((string, None));
        }
        Term::Constant(_, Constant::String(tail)) => {
            string += &tail;
            return Some((string, None));
        }
        _ => {
            return None;
        }
    }
}

impl<'a> TermIterState<'a> {
    pub fn subterm_to_state(lvl: Level, term: &'a Term) -> TermIterState<'a> {
        match term {
            &Term::AnonVar => TermIterState::AnonVar(lvl),
            &Term::Clause(ref cell, ref name, ref subterms, ref spec) => {
                let ct = if let Some(spec) = spec {
                    ClauseType::Op(name.clone(), spec.clone(), CodeIndex::default())
                } else {
                    ClauseType::Named(name.clone(), subterms.len(), CodeIndex::default())
                };

                TermIterState::Clause(lvl, 0, cell, ct, subterms)
            }
            &Term::Cons(ref cell, ref head, ref tail) => {
                TermIterState::InitialCons(lvl, cell, head.as_ref(), tail.as_ref())
            }
            &Term::Constant(ref cell, ref constant) => TermIterState::Constant(lvl, cell, constant),
            &Term::Var(ref cell, ref var) => TermIterState::Var(lvl, cell, var.clone()),
        }
    }
}

#[derive(Debug)]
pub struct QueryIterator<'a> {
    state_stack: Vec<TermIterState<'a>>,
}

impl<'a> QueryIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack
            .push(TermIterState::subterm_to_state(lvl, term));
    }

    fn from_rule_head_clause(terms: &'a Vec<Box<Term>>) -> Self {
        let state_stack = terms
            .iter()
            .rev()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt.as_ref()))
            .collect();

        QueryIterator { state_stack }
    }

    fn from_term(term: &'a Term) -> Self {
        let state = match term {
            &Term::AnonVar => {
                return QueryIterator {
                    state_stack: vec![],
                }
            }
            &Term::Clause(ref r, ref name, ref terms, ref fixity) => TermIterState::Clause(
                Level::Root,
                0,
                r,
                ClauseType::from(name.clone(), terms.len(), fixity.clone()),
                terms,
            ),
            &Term::Cons(..) => {
                return QueryIterator {
                    state_stack: vec![],
                }
            }
            &Term::Constant(_, _) => {
                return QueryIterator {
                    state_stack: vec![],
                }
            }
            &Term::Var(ref cell, ref var) => TermIterState::Var(Level::Root, cell, (*var).clone()),
        };

        QueryIterator {
            state_stack: vec![state],
        }
    }

    fn new(term: &'a QueryTerm) -> Self {
        match term {
            &QueryTerm::Clause(ref cell, ClauseType::CallN, ref terms, _) => {
                let state = TermIterState::Clause(Level::Root, 1, cell, ClauseType::CallN, terms);
                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::Clause(ref cell, ref ct, ref terms, _) => {
                let state = TermIterState::Clause(Level::Root, 0, cell, ct.clone(), terms);
                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::UnblockedCut(ref cell) => {
                let state = TermIterState::Var(Level::Root, cell, rc_atom!("!"));
                QueryIterator {
                    state_stack: vec![state],
                }
            }
            &QueryTerm::GetLevelAndUnify(ref cell, ref var) => {
                let state = TermIterState::Var(Level::Root, cell, var.clone());
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
                TermIterState::Clause(lvl, child_num, cell, ct, child_terms) => {
                    if child_num == child_terms.len() {
                        match ct {
                            ClauseType::CallN => {
                                self.push_subterm(Level::Shallow, child_terms[0].as_ref())
                            }
                            ClauseType::Named(..) | ClauseType::Op(..) => {
                                return match lvl {
                                    Level::Root => None,
                                    lvl => Some(TermRef::Clause(lvl, cell, ct, child_terms)),
                                }
                            }
                            _ => {
                                return None;
                            }
                        };
                    } else {
                        self.state_stack.push(TermIterState::Clause(
                            lvl,
                            child_num + 1,
                            cell,
                            ct,
                            child_terms,
                        ));

                        self.push_subterm(lvl.child_level(), child_terms[child_num].as_ref());
                    }
                }
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    if let Some((string, tail)) = is_partial_string(head, tail) {
                        self.state_stack
                            .push(TermIterState::PartialString(lvl, cell, string, tail));

                        if let Some(tail) = tail {
                            self.push_subterm(lvl.child_level(), tail);
                        }
                    } else {
                        self.state_stack
                            .push(TermIterState::FinalCons(lvl, cell, head, tail));

                        self.push_subterm(lvl.child_level(), tail);
                        self.push_subterm(lvl.child_level(), head);
                    }
                }
                TermIterState::PartialString(lvl, cell, string, tail) => {
                    return Some(TermRef::PartialString(lvl, cell, string, tail));
                }
                TermIterState::FinalCons(lvl, cell, head, tail) => {
                    return Some(TermRef::Cons(lvl, cell, head, tail));
                }
                TermIterState::Constant(lvl, cell, constant) => {
                    return Some(TermRef::Constant(lvl, cell, constant));
                }
                TermIterState::Var(lvl, cell, var) => {
                    return Some(TermRef::Var(lvl, cell, var));
                }
            };
        }

        None
    }
}

#[derive(Debug)]
pub struct FactIterator<'a> {
    state_queue: VecDeque<TermIterState<'a>>,
    iterable_root: bool,
}

impl<'a> FactIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_queue
            .push_back(TermIterState::subterm_to_state(lvl, term));
    }

    pub fn from_rule_head_clause(terms: &'a Vec<Box<Term>>) -> Self {
        let state_queue = terms
            .iter()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt.as_ref()))
            .collect();

        FactIterator {
            state_queue,
            iterable_root: false,
        }
    }

    fn new(term: &'a Term, iterable_root: bool) -> Self {
        let states = match term {
            &Term::AnonVar => {
                vec![TermIterState::AnonVar(Level::Root)]
            }
            &Term::Clause(ref cell, ref name, ref terms, ref fixity) => {
                let ct = ClauseType::from(name.clone(), terms.len(), fixity.clone());
                vec![TermIterState::Clause(Level::Root, 0, cell, ct, terms)]
            }
            &Term::Cons(ref cell, ref head, ref tail) => vec![TermIterState::InitialCons(
                Level::Root,
                cell,
                head.as_ref(),
                tail.as_ref(),
            )],
            &Term::Constant(ref cell, ref constant) => {
                vec![TermIterState::Constant(Level::Root, cell, constant)]
            }
            &Term::Var(ref cell, ref var) => {
                vec![TermIterState::Var(Level::Root, cell, var.clone())]
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
                TermIterState::Clause(lvl, _, cell, ct, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(lvl.child_level(), child_term);
                    }

                    match lvl {
                        Level::Root if !self.iterable_root => continue,
                        _ => return Some(TermRef::Clause(lvl, cell, ct, child_terms)),
                    };
                }
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    if let Some((string, tail)) = is_partial_string(head, tail) {
                        if let Some(tail) = tail {
                            self.push_subterm(Level::Deep, tail);
                        }

                        return Some(TermRef::PartialString(lvl, cell, string, tail));
                    } else {
                        self.push_subterm(Level::Deep, head);
                        self.push_subterm(Level::Deep, tail);

                        return Some(TermRef::Cons(lvl, cell, head, tail));
                    }
                }
                TermIterState::Constant(lvl, cell, constant) => {
                    return Some(TermRef::Constant(lvl, cell, constant))
                }
                TermIterState::Var(lvl, cell, var) => {
                    return Some(TermRef::Var(lvl, cell, var));
                }
                _ => {}
            }
        }

        None
    }
}

pub fn post_order_iter(term: &Term) -> QueryIterator {
    QueryIterator::from_term(term)
}

pub fn breadth_first_iter(term: &Term, iterable_root: bool) -> FactIterator {
    FactIterator::new(term, iterable_root)
}

#[derive(Debug)]
pub enum ChunkedTerm<'a> {
    HeadClause(ClauseName, &'a Vec<Box<Term>>),
    BodyTerm(&'a QueryTerm),
}

pub fn query_term_post_order_iter<'a>(query_term: &'a QueryTerm) -> QueryIterator<'a> {
    QueryIterator::new(query_term)
}

impl<'a> ChunkedTerm<'a> {
    pub fn post_order_iter(&self) -> QueryIterator<'a> {
        match self {
            &ChunkedTerm::BodyTerm(ref qt) => QueryIterator::new(qt),
            &ChunkedTerm::HeadClause(_, terms) => QueryIterator::from_rule_head_clause(terms),
        }
    }
}

fn contains_cut_var<'a, Iter: Iterator<Item = &'a Term>>(terms: Iter) -> bool {
    for term in terms {
        if let &Term::Var(_, ref var) = term {
            if var.as_str() == "!" {
                return true;
            }
        }
    }

    false
}

pub struct ChunkedIterator<'a> {
    pub chunk_num: usize,
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
    pub fn rule_body_iter(self) -> Box<dyn Iterator<Item = RuleBodyIteratorItem<'a>> + 'a> {
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
    /*
        pub fn from_term_sequence(terms: &'a [QueryTerm]) -> Self {
            ChunkedIterator {
                chunk_num: 0,
                iter: Box::new(terms.iter().map(|t| ChunkedTerm::BodyTerm(t))),
                deep_cut_encountered: false,
                cut_var_in_head: false,
            }
        }
    */
    pub fn from_rule_body(p1: &'a QueryTerm, clauses: &'a Vec<QueryTerm>) -> Self {
        let inner_iter = Box::new(once(ChunkedTerm::BodyTerm(p1)));
        let iter = inner_iter.chain(clauses.iter().map(|t| ChunkedTerm::BodyTerm(t)));

        ChunkedIterator {
            chunk_num: 0,
            iter: Box::new(iter),
            deep_cut_encountered: false,
            cut_var_in_head: false,
        }
    }

    pub fn from_rule(rule: &'a Rule) -> Self {
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

    pub fn encountered_deep_cut(&self) -> bool {
        self.deep_cut_encountered
    }

    fn take_chunk(&mut self, term: ChunkedTerm<'a>) -> (usize, usize, Vec<ChunkedTerm<'a>>) {
        let mut arity = 0;
        let mut item = Some(term);
        let mut result = Vec::new();

        while let Some(term) = item {
            match term {
                ChunkedTerm::HeadClause(_, terms) => {
                    if contains_cut_var(terms.iter().map(|t| t.as_ref())) {
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
                ChunkedTerm::BodyTerm(&QueryTerm::UnblockedCut(..)) => result.push(term),
                ChunkedTerm::BodyTerm(&QueryTerm::Clause(_, ClauseType::Inlined(_), ..)) => {
                    result.push(term)
                }
                ChunkedTerm::BodyTerm(&QueryTerm::Clause(
                    _,
                    ClauseType::CallN,
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
