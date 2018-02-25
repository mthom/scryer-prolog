use prolog::ast::*;

use std::collections::VecDeque;
use std::iter::*;
use std::vec::Vec;

pub struct QueryIterator<'a> {
    state_stack: Vec<TermIterState<'a>>
}

impl<'a> QueryIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack.push(TermIterState::subterm_to_state(lvl, term));
    }

    fn from_rule_head_clause(terms: &'a Vec<Box<Term>>) -> Self {
        let state_stack = terms.iter().rev()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt.as_ref()))
            .collect();

        QueryIterator { state_stack }
    }

    fn from_term(term: &'a Term) -> Self {
        let state = match term {
            &Term::AnonVar =>
                return QueryIterator { state_stack: vec![] },
            &Term::Clause(ref r, ref name, ref terms, fixity) =>
                TermIterState::Clause(Level::Root, 0, r,
                                      ClauseType::from(name.clone(), terms.len(), fixity),
                                      terms),
            &Term::Cons(..) =>
                return QueryIterator { state_stack: vec![] },
            &Term::Constant(_, _) =>
                return QueryIterator { state_stack: vec![] },
            &Term::Var(ref cell, ref var) =>
                TermIterState::Var(Level::Root, cell, var)
        };

        QueryIterator { state_stack: vec![state] }
    }

    fn new(term: &'a QueryTerm) -> Self {
        match term {
            &QueryTerm::Clause(ref cell, ClauseType::CallN, ref terms) => {
                let state = TermIterState::Clause(Level::Root, 1, cell, ClauseType::CallN, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Clause(ref cell, ref ct, ref terms) => {
                let state = TermIterState::Clause(Level::Root, 0, cell, ct.clone(), terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Cut => QueryIterator { state_stack: vec![] },
            &QueryTerm::Jump(ref vars) => {
                let state_stack = vars.iter().rev().map(|t| {
                    TermIterState::subterm_to_state(Level::Shallow, t)
                }).collect();

                QueryIterator { state_stack }
            }
        }
    }
}

impl<'a> Iterator for QueryIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                TermIterState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                TermIterState::Clause(lvl, child_num, cell, ct, child_terms) => {
                    if child_num == child_terms.len() {
                        match ct {
                            ClauseType::CallN =>
                                self.push_subterm(Level::Shallow, child_terms[0].as_ref()),
                            ClauseType::Named(..) | ClauseType::Op(..) =>
                                return match lvl {
                                    Level::Root => None,
                                    lvl => Some(TermRef::Clause(lvl, cell, ct, child_terms))
                                },
                            _ =>
                                return None
                        };
                    } else {
                        self.state_stack.push(TermIterState::Clause(lvl, child_num + 1,
                                                                    cell, ct, child_terms));
                        self.push_subterm(lvl.child_level(), child_terms[child_num].as_ref());
                    }
                },
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    self.state_stack.push(TermIterState::FinalCons(lvl, cell, head, tail));

                    self.push_subterm(lvl.child_level(), tail);
                    self.push_subterm(lvl.child_level(), head);
                },
                TermIterState::FinalCons(lvl, cell, head, tail) =>
                    return Some(TermRef::Cons(lvl, cell, head, tail)),
                TermIterState::Constant(lvl, cell, constant) =>
                    return Some(TermRef::Constant(lvl, cell, constant)),
                TermIterState::Var(lvl, cell, var) =>
                    return Some(TermRef::Var(lvl, cell, var))
            };
        }

        None
    }
}

pub struct FactIterator<'a> {
    state_queue: VecDeque<TermIterState<'a>>,
}

impl<'a> FactIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_queue.push_back(TermIterState::subterm_to_state(lvl, term));
    }

    pub fn from_rule_head_clause(terms: &'a Vec<Box<Term>>) -> Self {
        let state_queue = terms.iter()
            .map(|bt| TermIterState::subterm_to_state(Level::Shallow, bt.as_ref()))
            .collect();

        FactIterator { state_queue }
    }

    fn new(term: &'a Term) -> Self {
        let states = match term {
            &Term::AnonVar =>
                vec![TermIterState::AnonVar(Level::Root)],
            &Term::Clause(ref cell, ref name, ref terms, fixity) => {
                let ct = ClauseType::from(name.clone(), terms.len(), fixity);
                vec![TermIterState::Clause(Level::Root, 0, cell, ct, terms)]
            },
            &Term::Cons(ref cell, ref head, ref tail) =>
                vec![TermIterState::InitialCons(Level::Root, cell, head.as_ref(), tail.as_ref())],
            &Term::Constant(ref cell, ref constant) =>
                vec![TermIterState::Constant(Level::Root, cell, constant)],
            &Term::Var(ref cell, ref var) =>
                vec![TermIterState::Var(Level::Root, cell, var)]
        };

        FactIterator { state_queue: VecDeque::from(states) }
    }
}

impl<'a> Iterator for FactIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.state_queue.pop_front() {
            match state {
                TermIterState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                TermIterState::Clause(lvl, _, cell, ct, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(lvl.child_level(), child_term);
                    }

                    match lvl {
                        Level::Root => continue,
                        _ => return Some(TermRef::Clause(lvl, cell, ct, child_terms))
                    };
                },
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    self.push_subterm(Level::Deep, head);
                    self.push_subterm(Level::Deep, tail);

                    return Some(TermRef::Cons(lvl, cell, head, tail));
                },
                TermIterState::Constant(lvl, cell, constant) =>
                    return Some(TermRef::Constant(lvl, cell, constant)),
                TermIterState::Var(lvl, cell, var) =>
                    return Some(TermRef::Var(lvl, cell, var)),
                _ => {}
            }
        }

        None
    }
}

impl Term {
    pub fn post_order_iter(&self) -> QueryIterator {
        QueryIterator::from_term(self)
    }

    pub fn breadth_first_iter(&self) -> FactIterator {
        FactIterator::new(self)
    }
}

pub enum ChunkedTerm<'a> {
    HeadClause(ClauseName, &'a Vec<Box<Term>>),
    BodyTerm(&'a QueryTerm)
}

impl QueryTerm {
    pub fn post_order_iter<'a>(&'a self) -> QueryIterator<'a> {
        QueryIterator::new(self)
    }
}

impl<'a> ChunkedTerm<'a> {
    pub fn post_order_iter(&self) -> QueryIterator<'a> {
        match self {
            &ChunkedTerm::BodyTerm(ref qt) =>
                QueryIterator::new(qt),
            &ChunkedTerm::HeadClause(_, terms) =>
                QueryIterator::from_rule_head_clause(terms)
        }
    }
}

pub struct ChunkedIterator<'a>
{
    pub chunk_num: usize,
    iter: Box<Iterator<Item=ChunkedTerm<'a>> + 'a>,
    deep_cut_encountered: bool
}

impl<'a> ChunkedIterator<'a>
{
    pub fn from_term_sequence(terms: &'a [QueryTerm]) -> Self
    {
        ChunkedIterator {
            chunk_num: 0,
            iter: Box::new(terms.iter().map(|t| ChunkedTerm::BodyTerm(t))),
            deep_cut_encountered: false
        }
    }

    pub fn from_rule_body(p1: &'a QueryTerm, clauses: &'a Vec<QueryTerm>) -> Self
    {
        let inner_iter = Box::new(once(ChunkedTerm::BodyTerm(p1)));
        let iter = inner_iter.chain(clauses.iter().map(|t| ChunkedTerm::BodyTerm(t)));

        ChunkedIterator {
            chunk_num: 0,
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }

    pub fn from_rule(rule: &'a Rule) -> Self
    {
        let &Rule { head: (ref name, ref args, ref p1), ref clauses } = rule;

        let iter = once(ChunkedTerm::HeadClause(name.clone(), args));
        let inner_iter = Box::new(once(ChunkedTerm::BodyTerm(p1)));
        let iter = iter.chain(inner_iter.chain(clauses.iter().map(|t| ChunkedTerm::BodyTerm(t))));

        ChunkedIterator {
            chunk_num: 0,
            iter: Box::new(iter),
            deep_cut_encountered: false,
        }
    }

    pub fn encountered_deep_cut(&self) -> bool {
        self.deep_cut_encountered
    }

    fn take_chunk(&mut self, term: ChunkedTerm<'a>) -> (usize, usize, Vec<ChunkedTerm<'a>>)
    {
        let mut arity  = 0;
        let mut item   = Some(term);
        let mut result = Vec::new();

        while let Some(term) = item {
            match term {
                ChunkedTerm::HeadClause(..) =>
                    result.push(term),
                ChunkedTerm::BodyTerm(&QueryTerm::Jump(ref vars)) => {
                    result.push(term);
                    arity = vars.len();
                    break;
                },
                ChunkedTerm::BodyTerm(&QueryTerm::Cut) => {
                    result.push(term);

                    if self.chunk_num > 0 {
                        self.deep_cut_encountered = true;
                    }
                },
                ChunkedTerm::BodyTerm(&QueryTerm::Clause(_, ClauseType::Inlined(_), _)) =>
                    result.push(term),                
                ChunkedTerm::BodyTerm(&QueryTerm::Clause(_, ClauseType::CallN, ref subterms)) => {
                    result.push(term);
                    arity = subterms.len() + 1;
                    break;
                },
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

impl<'a> Iterator for ChunkedIterator<'a>
{
    // the chunk number, last term arity, and vector of references.
    type Item = (usize, usize, Vec<ChunkedTerm<'a>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|term| self.take_chunk(term))
    }
}
