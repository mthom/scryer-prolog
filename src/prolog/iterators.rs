use prolog::ast::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::iter::*;
use std::vec::Vec;

enum IteratorState<'a> {
    AnonVar(Level),
    Clause(Level, usize, &'a Cell<RegType>, &'a Atom, &'a Vec<Box<Term>>),
    Constant(Level, &'a Cell<RegType>, &'a Constant),
    InitialCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    FinalCons(Level, &'a Cell<RegType>, &'a Term, &'a Term),
    RootClause(usize, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<VarReg>, &'a Var)
}

impl<'a> IteratorState<'a> {
    fn to_state(lvl: Level, term: &'a Term) -> IteratorState<'a> {
        match term {
            &Term::AnonVar =>
                IteratorState::AnonVar(lvl),
            &Term::Clause(ref cell, ref atom, ref child_terms) =>
                IteratorState::Clause(lvl, 0, cell, atom, child_terms),
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
    fn push_clause(&mut self,
                   lvl: Level,
                   child_num: usize,
                   cell: &'a Cell<RegType>,
                   name: &'a Atom,
                   child_terms: &'a Vec<Box<Term>>)
    {
        self.state_stack.push(IteratorState::Clause(lvl,
                                                    child_num,
                                                    cell,
                                                    name,
                                                    child_terms));
    }

    fn push_root_clause(&mut self,
                        child_num: usize,
                        child_terms: &'a Vec<Box<Term>>)
    {
        self.state_stack.push(IteratorState::RootClause(child_num, child_terms));
    }

    fn push_subterm(&mut self, lvl: Level, term: &'a Term) {
        self.state_stack.push(IteratorState::to_state(lvl, term));
    }

    fn push_final_cons(&mut self,
                       lvl: Level,
                       cell: &'a Cell<RegType>,
                       head: &'a Term,
                       tail: &'a Term)
    {
        self.state_stack.push(IteratorState::FinalCons(lvl, cell, head, tail));
    }

    fn new(term: &'a Term) -> QueryIterator<'a> {
        let state = match term {
            &Term::AnonVar =>
                IteratorState::AnonVar(Level::Shallow),
            &Term::Clause(_, _, ref terms) =>
                IteratorState::RootClause(0, terms),
            &Term::Cons(ref cell, ref head, ref tail) =>
                IteratorState::InitialCons(Level::Shallow, cell, head.as_ref(), tail.as_ref()),
            &Term::Constant(ref cell, ref constant) =>
                IteratorState::Constant(Level::Shallow, cell, constant),
            &Term::Var(ref cell, ref var) =>
                IteratorState::Var(Level::Shallow, cell, var)
        };

        QueryIterator { state_stack: vec![state] }
    }
}

impl<'a> Iterator for QueryIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                IteratorState::AnonVar(lvl) =>
                    return Some(TermRef::AnonVar(lvl)),
                IteratorState::Clause(lvl, child_num, cell, atom, child_terms) => {
                    if child_num == child_terms.len() {
                        return Some(TermRef::Clause(lvl, cell, atom, child_terms));
                    } else {
                        self.push_clause(lvl, child_num + 1, cell, atom, child_terms);
                        self.push_subterm(Level::Deep, child_terms[child_num].as_ref());
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
                IteratorState::RootClause(child_num, child_terms) => {
                    if child_num == child_terms.len() {
                        return None;
                    } else {
                        self.push_root_clause(child_num + 1, child_terms);
                        self.push_subterm(Level::Shallow, child_terms[child_num].as_ref());
                    }
                },
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
                vec![IteratorState::RootClause(0, terms)],
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
                IteratorState::Clause(lvl, _, cell, atom, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(Level::Deep, child_term);
                    }

                    return Some(TermRef::Clause(lvl, cell, atom, child_terms));
                },
                IteratorState::InitialCons(lvl, cell, head, tail) => {
                    self.push_subterm(Level::Deep, head);
                    self.push_subterm(Level::Deep, tail);

                    return Some(TermRef::Cons(lvl, cell, head, tail));
                },
                IteratorState::Constant(lvl, cell, constant) =>
                    return Some(TermRef::Constant(lvl, cell, constant)),
                IteratorState::RootClause(_, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(Level::Shallow, child_term);
                    }
                },
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
        QueryIterator::new(self)
    }

    pub fn breadth_first_iter(&self) -> FactIterator {
        FactIterator::new(self)
    }
}

pub struct ChunkedIterator<'a>
{
    at_head: bool,
    iter: Box<Iterator<Item=TermOrCutRef<'a>> + 'a>,
    deep_cut_encountered: bool
}

impl<'a> ChunkedIterator<'a>
{
    pub fn from_term(term: &'a Term, at_head: bool) -> Self
    {
        let inner_iter: Box<Iterator<Item=TermOrCutRef<'a>>> =
            Box::new(once(TermOrCutRef::Term(term)));

        ChunkedIterator {
            at_head: at_head,
            iter: inner_iter,
            deep_cut_encountered: false
        }
    }

    pub fn from_term_sequence(terms: &'a Vec<TermOrCut>) -> Self
    {
        let iter = terms.iter().map(|c| {
            match c {
                &TermOrCut::Cut => TermOrCutRef::Cut,
                &TermOrCut::Term(ref term) => TermOrCutRef::Term(term)
            }
        });

        ChunkedIterator {
            at_head: false,
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }
    
    pub fn from_rule(rule: &'a Rule) -> Self
    {
        let &Rule { head: (ref p0, ref p1), ref clauses } = rule;
        let iter = once(TermOrCutRef::Term(p0));

        let inner_iter : Box<Iterator<Item=TermOrCutRef<'a>>> = match p1 {
            &TermOrCut::Term(ref p1) => Box::new(once(TermOrCutRef::Term(p1))),
            _ => Box::new(empty())
        };

        let iter = iter.chain(inner_iter.chain(clauses.iter().map(|c| {
            match c {
                &TermOrCut::Cut => TermOrCutRef::Cut,
                &TermOrCut::Term(ref term) => TermOrCutRef::Term(term)
            }
        })));
                              
        ChunkedIterator {
            at_head: true,
            iter: Box::new(iter),
            deep_cut_encountered: false
        }
    }

    pub fn contains_deep_cut(&self) -> bool {
        self.deep_cut_encountered
    }

    pub fn at_head(&self) -> bool {
        self.at_head
    }
    
    fn take_chunk(&mut self, term: TermOrCutRef<'a>) -> (usize, Vec<TermOrCutRef<'a>>)
    {
        let mut result = vec![term];
        let mut arity = 0;

        while let Some(term) = self.iter.next() {
            match term {
                TermOrCutRef::Term(inner_term) => {
                    result.push(term);

                    if inner_term.is_callable() {
                        arity = inner_term.arity();
                        break;
                    }
                },
                _ => {
                    result.push(term);
                    self.deep_cut_encountered = true;                    
                }
            };
        }

        (arity, result)
    }
}

impl<'a> Iterator for ChunkedIterator<'a>
{
    // the last term arity, and the reference.
    type Item = (usize, Vec<TermOrCutRef<'a>>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                None => return None,
                Some(TermOrCutRef::Term(term)) if self.at_head => {
                    self.at_head = false;
                    return Some(self.take_chunk(TermOrCutRef::Term(term)));
                },
                Some(TermOrCutRef::Term(term)) if term.is_callable() =>
                    return Some((term.arity(), vec![TermOrCutRef::Term(term)])),
                Some(term_or_cut_ref) =>
                    return Some(self.take_chunk(term_or_cut_ref))
            }
        }
    }
}
