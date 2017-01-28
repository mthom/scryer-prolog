use l1::ast::{Atom, Level, Reg, Term, TermRef, Var};

use std::cell::Cell;
use std::collections::VecDeque;
use std::vec::Vec;

enum IteratorState<'a> {
    Atom(Level, &'a Cell<usize>, &'a Atom),
    Clause(Level, usize, &'a Cell<usize>, &'a Atom, &'a Vec<Box<Term>>),
    IsolatedAtom(&'a Cell<usize>, &'a Atom),
    IsolatedVar(&'a Cell<Reg>, &'a Var),
    RootClause(usize, &'a Vec<Box<Term>>),
    Var(Level, &'a Cell<Reg>, &'a Var)
}

impl<'a> IteratorState<'a> {
    fn to_state(lvl: Level, term: &'a Term) -> IteratorState<'a>
    {
        match term {
            &Term::Atom(ref cell, ref atom) =>
                IteratorState::Atom(lvl, cell, atom),
            &Term::Clause(ref cell, ref atom, ref child_terms) =>
                IteratorState::Clause(lvl, 0, cell, atom, child_terms),
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
                   cell: &'a Cell<usize>,
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

    fn new(term: &'a Term) -> QueryIterator<'a> {
        let state = match term {
            &Term::Atom(ref cell, ref atom) =>
                IteratorState::IsolatedAtom(cell, atom),
            &Term::Clause(_, _, ref terms) =>
                IteratorState::RootClause(0, terms),
            &Term::Var(ref cell, ref var) =>
                IteratorState::IsolatedVar(cell, var)
        };
        
        QueryIterator { state_stack: vec![state] }
    }
}

impl<'a> Iterator for QueryIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                IteratorState::Atom(lvl, cell, atom) =>
                    return Some(TermRef::Atom(lvl, cell, atom)),
                IteratorState::Clause(lvl, child_num, cell, atom, child_terms) => {
                    if child_num == child_terms.len() {
                        return Some(TermRef::Clause(lvl, cell, atom, child_terms));
                    } else {
                        self.push_clause(lvl, child_num + 1, cell, atom, child_terms);
                        self.push_subterm(Level::Deep, child_terms[child_num].as_ref());
                    }
                },
                IteratorState::IsolatedAtom(cell, atom) =>
                    return Some(TermRef::Atom(Level::Shallow, cell, atom)),
                IteratorState::IsolatedVar(cell, var) =>
                    return Some(TermRef::Var(Level::Shallow, cell, var)),
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
            &Term::Atom(ref cell, ref atom) =>
                vec![IteratorState::IsolatedAtom(cell, atom)],
            &Term::Clause(_, _, ref terms) =>
                vec![IteratorState::RootClause(0, terms)],
            &Term::Var(ref cell, ref var) =>
                vec![IteratorState::IsolatedVar(cell, var)]
        };

        FactIterator { state_queue:  VecDeque::from(states) }
    }
}

impl<'a> Iterator for FactIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.state_queue.pop_front() {
            match state {
                IteratorState::Atom(lvl, cell, atom) =>
                    return Some(TermRef::Atom(lvl, cell, atom)),
                IteratorState::Clause(lvl, _, cell, atom, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(Level::Deep, child_term);
                    }

                    return Some(TermRef::Clause(lvl, cell, atom, child_terms));
                },
                IteratorState::IsolatedAtom(cell, atom) =>
                    return Some(TermRef::Atom(Level::Shallow, cell, atom)),
                IteratorState::IsolatedVar(cell, var) =>
                    return Some(TermRef::Var(Level::Shallow, cell, var)),
                IteratorState::RootClause(_, child_terms) => {
                    for child_term in child_terms {
                        self.push_subterm(Level::Shallow, child_term);
                    }
                },
                IteratorState::Var(lvl, cell, var) =>
                    return Some(TermRef::Var(lvl, cell, var))
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
