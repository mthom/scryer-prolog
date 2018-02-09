use prolog::ast::*;

use std::collections::VecDeque;
use std::iter::*;
use std::vec::Vec;

pub struct QueryIterator<'a> {
    state_stack: Vec<TermIterState<'a>>
}

impl<'a> QueryIterator<'a> {
    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack.push(TermIterState::to_state(lvl, term));
    }

    fn from_term(term: &'a Term) -> Self {
        let state = match term {
            &Term::AnonVar =>
                return QueryIterator { state_stack: vec![] },
            &Term::Clause(_, ref name, ref terms, _) =>
                TermIterState::Clause(0, ClauseType::Root(name), terms),
            &Term::Cons(..) =>
                return QueryIterator { state_stack: vec![] },
            &Term::Constant(_, _) =>
                return QueryIterator { state_stack: vec![] },
            &Term::Var(ref cell, ref var) =>
                TermIterState::Var(Level::Shallow, cell, var)
        };

        QueryIterator { state_stack: vec![state] }
    }

    fn new(term: &'a QueryTerm) -> Self {
        match term {
            &QueryTerm::CallN(ref terms) => {
                let state = TermIterState::Clause(1, ClauseType::CallN, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Catch(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::Catch, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::DuplicateTerm(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::DuplicateTerm, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Arg(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::Arg, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::SetupCallCleanup(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::SetupCallCleanup, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Functor(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::Functor, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Display(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::Display, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Ground(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::Ground, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Inlined(InlinedQueryTerm::CompareNumber(qt, ref terms)) => {                
                let state = TermIterState::Clause(0, ClauseType::CompareNumber(qt), terms);
                QueryIterator { state_stack: vec![state] }            
            },
            &QueryTerm::Is(ref terms) => {
                let state = TermIterState::Clause(0, ClauseType::Is, terms);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Inlined(InlinedQueryTerm::IsAtomic(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsInteger(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsVar(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsNonVar(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsFloat(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsRational(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsCompound(ref terms))
          | &QueryTerm::Inlined(InlinedQueryTerm::IsString(ref terms)) =>      
                Self::from_term(terms[0].as_ref()),
            &QueryTerm::Term(ref term) =>
                Self::from_term(term),
            &QueryTerm::Throw(ref term) => {
                let state = TermIterState::Clause(0, ClauseType::Throw, term);
                QueryIterator { state_stack: vec![state] }
            },
            &QueryTerm::Cut => QueryIterator { state_stack: vec![] },
            &QueryTerm::Jump(ref vars) => {
                let state_stack = vars.iter().rev().map(|t| {
                    TermIterState::to_state(Level::Shallow, t)
                }).collect();

                QueryIterator { state_stack }
            }
        }
    }
}

impl QueryTerm {
    pub fn post_order_iter<'a>(&'a self) -> QueryIterator<'a> {
        QueryIterator::new(self)
    }
}

impl<'a> Iterator for QueryIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                TermIterState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                TermIterState::Clause(child_num, ct, child_terms) => {
                    if child_num == child_terms.len() {
                        match ct {
                            ClauseType::CallN =>
                                self.push_subterm(Level::Shallow, child_terms[0].as_ref()),
                            ClauseType::Deep(..) =>
                                return Some(TermRef::Clause(ct, child_terms)),
                            _ =>
                                return None
                        };
                    } else {
                        self.state_stack.push(TermIterState::Clause(child_num + 1, ct, child_terms));
                        self.push_subterm(ct.level_of_subterms(), child_terms[child_num].as_ref());
                    }
                },
                TermIterState::InitialCons(lvl, cell, head, tail) => {
                    self.state_stack.push(TermIterState::FinalCons(lvl, cell, head, tail));
                    self.push_subterm(Level::Deep, tail);
                    self.push_subterm(Level::Deep, head);
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
        self.state_queue.push_back(TermIterState::to_state(lvl, term));
    }

    fn new(term: &'a Term) -> FactIterator<'a> {
        let states = match term {
            &Term::AnonVar =>
                vec![TermIterState::AnonVar(Level::Shallow)],
            &Term::Clause(.., ref name, ref terms, _) =>
                vec![TermIterState::Clause(0, ClauseType::Root(name), terms)],
            &Term::Cons(ref cell, ref head, ref tail) =>
                vec![TermIterState::InitialCons(Level::Shallow,
                                                cell,
                                                head.as_ref(),
                                                tail.as_ref())],
            &Term::Constant(ref cell, ref constant) =>
                vec![TermIterState::Constant(Level::Shallow, cell, constant)],
            &Term::Var(ref cell, ref var) =>
                vec![TermIterState::Var(Level::Shallow, cell, var)]
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
                TermIterState::Clause(_, ct, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(ct.level_of_subterms(), child_term);
                    }

                    match ct {
                        ClauseType::Deep(..) =>
                            return Some(TermRef::Clause(ct, child_terms)),
                        _ =>
                            continue
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

pub struct ChunkedIterator<'a>
{
    term_loc: GenContext,
    iter: Box<Iterator<Item=&'a QueryTerm> + 'a>,
    deep_cut_encountered: bool
}

impl<'a> ChunkedIterator<'a>
{
    pub fn from_term_sequence(terms: &'a [QueryTerm]) -> Self
    {
        ChunkedIterator {
            term_loc: GenContext::Last(0),
            iter: Box::new(terms.iter()),
            deep_cut_encountered: false
        }
    }

    pub fn from_rule_body(p1: &'a QueryTerm, clauses: &'a Vec<QueryTerm>) -> Self
    {
        let inner_iter = Box::new(once(p1));
        let iter = inner_iter.chain(clauses.iter());

        ChunkedIterator {
            term_loc: GenContext::Last(0),
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }

    pub fn from_rule(rule: &'a Rule) -> Self
    {
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;

        let iter = once(p0);
        let inner_iter = Box::new(once(p1));
        let iter = iter.chain(inner_iter.chain(clauses.iter()));

        ChunkedIterator {
            term_loc: GenContext::Head,
            iter: Box::new(iter),
            deep_cut_encountered: false,
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

    fn take_chunk(&mut self, term: &'a QueryTerm) -> (usize, usize, Vec<&'a QueryTerm>)
    {
        let mut arity  = 0;
        let mut item   = Some(term);
        let mut result = Vec::new();

        while let Some(term) = item {
            match term {
                &QueryTerm::Jump(ref vars) => {
                    result.push(term);
                    arity = vars.len();
                    break;
                },
                &QueryTerm::Term(ref inner_term) =>
                    if let GenContext::Head = self.term_loc {
                        result.push(term);
                        self.term_loc = GenContext::Last(0);
                    } else {
                        result.push(term);

                        if inner_term.is_callable() {
                            arity = inner_term.arity();
                            break;
                        }
                    },
                &QueryTerm::SetupCallCleanup(_) => {
                    result.push(term);
                    arity = 3;
                    break;
                },
                &QueryTerm::CallN(ref child_terms) => {
                    result.push(term);
                    arity = child_terms.len() + 1;
                    break;
                },
                &QueryTerm::Catch(ref child_terms) | &QueryTerm::Throw(ref child_terms) => {
                    result.push(term);
                    arity = child_terms.len();
                    break;
                },
                &QueryTerm::Ground(_) | &QueryTerm::Display(_) => {
                    result.push(term);
                    arity = 1;
                    break;
                },
                &QueryTerm::Arg(_)
              | &QueryTerm::Functor(_) => {
                    result.push(term);
                    arity = 3;
                    break;
                },
                &QueryTerm::Is(_) | &QueryTerm::DuplicateTerm(_) => {
                    result.push(term);
                    arity = 2;
                    break;
                },
                &QueryTerm::Inlined(_) =>
                    result.push(term),
                &QueryTerm::Cut => {
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
    type Item = (usize, usize, Vec<&'a QueryTerm>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|term| self.take_chunk(term))
    }
}
