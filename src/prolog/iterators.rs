use prolog::ast::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::iter::*;
use std::vec::Vec;

enum IteratorState<'a> {
    AnonVar(Level),
    Clause(usize, ClauseType<'a>, &'a Vec<Box<Term>>),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

impl<'a> IteratorState<'a> {
    fn to_state(lvl: Level, term: &'a Term) -> IteratorState<'a> {
        match term {
            &Term::AnonVar =>
                IteratorState::AnonVar(lvl),
            &Term::Clause(ref cell, ref atom, ref child_terms) =>
                IteratorState::Clause(0, ClauseType::Deep(lvl, cell, atom), child_terms),
            &Term::Cons(ref cell, ref head, ref tail) =>
                IteratorState::InitialCons(lvl, cell, head.as_ref(), tail.as_ref()),
            &Term::Constant(ref cell, ref constant) =>
                IteratorState::Constant(lvl, cell, constant),
            &Term::Var(ref cell, ref var) =>
                IteratorState::Var(lvl, cell, var)
        }
    }
}

pub struct QueryIterator<'a> {
    state_stack: Vec<IteratorState<'a>>
}

impl<'a> QueryIterator<'a> {
    fn push_clause(&mut self, child_num: usize, ct: ClauseType<'a>, child_terms: &'a Vec<Box<Term>>)
    {
        self.state_stack.push(IteratorState::Clause(child_num, ct, child_terms));
    }

    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack.push(IteratorState::to_state(lvl, term));
    }

    fn push_final_cons(&mut self, lvl: Level, cell: &'a Cell<RegType>, head: &'a Term, tail: &'a Term)
    {
        self.state_stack.push(IteratorState::FinalCons(lvl, cell, head, tail));
    }

    fn from_term(term: &'a Term) -> Self {
        let state = match term {
            &Term::AnonVar =>
                return QueryIterator { state_stack: vec![] },
            &Term::Clause(_, _, ref terms) =>
                IteratorState::Clause(0, ClauseType::Root, terms),
            &Term::Cons(_, _, _) =>
                return QueryIterator { state_stack: vec![] },
            &Term::Constant(_, _) =>
                return QueryIterator { state_stack: vec![] },
            &Term::Var(ref cell, ref var) =>
                IteratorState::Var(Level::Shallow, cell, var)
        };

        QueryIterator { state_stack: vec![state] }
    }

    fn new(term: QueryTermRef<'a>) -> Self {
        match term {
            QueryTermRef::CallN(terms) => {
                let state = IteratorState::Clause(1, ClauseType::CallN, terms);
                QueryIterator { state_stack: vec![state] }
            },
            QueryTermRef::Catch(terms) => {
                let state = IteratorState::Clause(0, ClauseType::Catch, terms);
                QueryIterator { state_stack: vec![state] }
            },
            QueryTermRef::IsAtomic(term) | QueryTermRef::IsVar(term) | QueryTermRef::Term(term) =>
                Self::from_term(term),
            QueryTermRef::Throw(term) => {
                let state = IteratorState::Clause(0, ClauseType::Throw, term);
                QueryIterator { state_stack: vec![state] }
            },
            _ => QueryIterator { state_stack: vec![] }
        }
    }
}

impl<'a> QueryTermRef<'a> {
    pub fn post_order_iter(self) -> QueryIterator<'a> {
        QueryIterator::new(self)
    }
}

impl<'a> Iterator for QueryIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                IteratorState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                IteratorState::Clause(child_num, ct, child_terms) => {
                    if child_num == child_terms.len() {
                        match ct {
                            ClauseType::CallN =>
                                self.push_subterm(Level::Shallow, child_terms[0].as_ref()),
                            ClauseType::Deep(_, _, _) =>
                                return Some(TermRef::Clause(ct, child_terms)),
                            _ =>
                                return None
                        };
                    } else {
                        self.push_clause(child_num + 1, ct, child_terms);
                        self.push_subterm(ct.level_of_subterms(), child_terms[child_num].as_ref());
                    }
                },
                IteratorState::InitialCons(lvl, cell, head, tail) => {
                    self.push_final_cons(lvl, cell, head, tail);
                    self.push_subterm(Level::Deep, tail);
                    self.push_subterm(Level::Deep, head);
                },
                IteratorState::FinalCons(lvl, cell, head, tail) =>
                    return Some(TermRef::Cons(lvl, cell, head, tail)),
                IteratorState::Constant(lvl, cell, constant) =>
                    return Some(TermRef::Constant(lvl, cell, constant)),
                IteratorState::Var(lvl, cell, var) =>
                    return Some(TermRef::Var(lvl, cell, var))
            };
        }

        None
    }
}

pub struct FactIterator<'a> {
    state_queue: VecDeque<IteratorState<'a>>,
}

impl<'a> FactIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_queue.push_back(IteratorState::to_state(lvl, term));
    }

    fn new(term: &'a Term) -> FactIterator<'a> {
        let states = match term {
            &Term::AnonVar =>
                vec![IteratorState::AnonVar(Level::Shallow)],
            &Term::Clause(_, _, ref terms) =>
                vec![IteratorState::Clause(0, ClauseType::Root, terms)],
            &Term::Cons(ref cell, ref head, ref tail) =>
                vec![IteratorState::InitialCons(Level::Shallow,
                                                cell,
                                                head.as_ref(),
                                                tail.as_ref())],
            &Term::Constant(ref cell, ref constant) =>
                vec![IteratorState::Constant(Level::Shallow, cell, constant)],
            &Term::Var(ref cell, ref var) =>
                vec![IteratorState::Var(Level::Shallow, cell, var)]
        };

        FactIterator { state_queue: VecDeque::from(states) }
    }
}

impl<'a> Iterator for FactIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.state_queue.pop_front() {
            match state {
                IteratorState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                IteratorState::Clause(_, ct, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(ct.level_of_subterms(), child_term);
                    }

                    match ct {
                        ClauseType::Deep(_, _, _) =>
                            return Some(TermRef::Clause(ct, child_terms)),
                        _ =>
                            continue
                    };
                },
                IteratorState::InitialCons(lvl, cell, head, tail) => {
                    self.push_subterm(Level::Deep, head);
                    self.push_subterm(Level::Deep, tail);

                    return Some(TermRef::Cons(lvl, cell, head, tail));
                },
                IteratorState::Constant(lvl, cell, constant) =>
                    return Some(TermRef::Constant(lvl, cell, constant)),
                IteratorState::Var(lvl, cell, var) =>
                    return Some(TermRef::Var(lvl, cell, var)),
                _ => {}
            }
        }

        None
    }
}

impl Term {
    pub fn post_order_iter(&self) -> QueryIterator {
        QueryIterator::new(QueryTermRef::Term(self))
    }

    pub fn breadth_first_iter(&self) -> FactIterator {
        FactIterator::new(self)
    }
}

pub struct ChunkedIterator<'a>
{
    term_loc: GenContext,
    iter: Box<Iterator<Item=QueryTermRef<'a>> + 'a>,
    deep_cut_encountered: bool
}

impl<'a> ChunkedIterator<'a>
{
    pub fn from_fact(term: &'a Term) -> Self
    {
        let inner_iter: Box<Iterator<Item=QueryTermRef<'a>>> =
            Box::new(once(QueryTermRef::Term(term)));

        ChunkedIterator {
            term_loc: GenContext::Head,
            iter: inner_iter,
            deep_cut_encountered: false,
        }
    }

    pub fn from_term_sequence(terms: &'a [QueryTerm]) -> Self
    {
        let iter = terms.iter().map(|c| c.to_ref());

        ChunkedIterator {
            term_loc: GenContext::Last(0),
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }

    pub fn from_rule_body(p1: &'a QueryTerm, clauses: &'a Vec<QueryTerm>) -> Self
    {
        let inner_iter = Box::new(once(p1.to_ref()));
        let iter = inner_iter.chain(clauses.iter().map(|c| c.to_ref()));

        ChunkedIterator {
            term_loc: GenContext::Last(0),
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }

    pub fn from_rule(rule: &'a Rule) -> Self
    {
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;

        let iter = once(QueryTermRef::Term(p0));
        let inner_iter = Box::new(once(p1.to_ref()));
        let iter = iter.chain(inner_iter.chain(clauses.iter().map(|c| c.to_ref())));

        ChunkedIterator {
            term_loc: GenContext::Head,
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }

    pub fn encountered_deep_cut(&self) -> bool {
        self.deep_cut_encountered
    }

    pub fn at_rule_head(&self) -> bool {
        self.term_loc == GenContext::Head
    }

    pub fn chunk_num(&self) -> usize {
        self.term_loc.chunk_num()
    }

    fn take_chunk(&mut self, term: QueryTermRef<'a>, mut result: Vec<QueryTermRef<'a>>)
                  -> (usize, usize, Vec<QueryTermRef<'a>>)
    {
        let mut arity  = 0;
        let mut item   = Some(term);

        while let Some(term) = item {
            match term {
                //TODO: This can refer to the term at the head of a
                // goal, not technically a QueryTerm (ie. a term in a
                // query).  Think of a better name.
                QueryTermRef::Term(inner_term) => {
                    if let GenContext::Head = self.term_loc {
                        result.push(term);
                        self.term_loc = GenContext::Last(0);
                    } else {
                        result.push(term);

                        if inner_term.is_callable() {
                            arity = inner_term.arity();
                            break;
                        }
                    }
                },
                QueryTermRef::CallN(child_terms) => {
                    result.push(term);
                    arity = child_terms.len() + 1;
                    break;
                },
                QueryTermRef::Catch(child_terms) | QueryTermRef::Throw(child_terms) => {
                    result.push(term);
                    arity = child_terms.len();
                    break;
                },
                QueryTermRef::IsAtomic(_) | QueryTermRef::IsVar(_) =>
                    result.push(term),
                QueryTermRef::Cut => {
                    result.push(term);

                    if self.term_loc.chunk_num() > 0 {
                        self.deep_cut_encountered = true;
                    }
                },
            };

            item = self.iter.next();
        }

        let chunk_num = self.term_loc.chunk_num();

        if let &mut GenContext::Last(ref mut chunk_num) = &mut self.term_loc {
            *chunk_num += 1;
        }

        (chunk_num, arity, result)
    }
}

impl<'a> Iterator for ChunkedIterator<'a>
{
    // the chunk number, last term arity, and vector of references.
    type Item = (usize, usize, Vec<QueryTermRef<'a>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|term| self.take_chunk(term, Vec::new()))
    }
}
