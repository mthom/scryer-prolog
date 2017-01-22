use l0::ast::{Term};

use std::collections::{VecDeque};
use std::vec::{Vec};

enum DepthFirstIteratorState<'a> {        
    // child no., the containing clause, its vector.
    Clause(usize, &'a Term, &'a Vec<Box<Term>>),
    NonClause(&'a Term)
}

pub struct PostOrderIterator<'a> {
    state_stack: Vec<DepthFirstIteratorState<'a>>        
}

impl<'a> PostOrderIterator<'a> {
    fn push_clause(&mut self,
                   child_num: usize,
                   term: &'a Term,
                   child_terms: &'a Vec<Box<Term>>)
    {
        self.state_stack.push(DepthFirstIteratorState::Clause(child_num,
                                                              term,
                                                              child_terms));
    }

    fn render_new_state(term: &'a Term) -> DepthFirstIteratorState<'a> {
        match term {
            &Term::Clause(_, _, ref child_terms) =>
                DepthFirstIteratorState::Clause(0, term, child_terms),
            _ => DepthFirstIteratorState::NonClause(term)
        }
    }

    fn push_term(&mut self, term: &'a Term) {
        self.state_stack.push(Self::render_new_state(term));
    }
}

impl<'a> Iterator for PostOrderIterator<'a> {
    type Item = &'a Term;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter_state) = self.state_stack.pop() {
            match iter_state {
                DepthFirstIteratorState::Clause(child_num, term, child_terms) => {                    
                    if child_num == child_terms.len() {
                        return Some(term);
                    } else {
                        self.push_clause(child_num + 1, term, child_terms);
                        self.push_term(child_terms[child_num].as_ref());
                    }
                },
                DepthFirstIteratorState::NonClause(term) => return Some(term),
            };
        }

        None
    }
}

pub struct BreadthFirstIterator<'a> {
    state_queue : VecDeque<&'a Term>
}

impl<'a> Iterator for BreadthFirstIterator<'a> {
    type Item = &'a Term;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(term) = self.state_queue.pop_front() {            
            if let &Term::Clause(_, _, ref child_terms) = term {
                for term in child_terms {
                    self.state_queue.push_back(term);
                }

                return Some(term);
            }

            return Some(term);
        }

        None
    }
}
    
impl<'a> Term {
    pub fn post_order_iter(&'a self) -> PostOrderIterator<'a> {
        let initial_state = PostOrderIterator::render_new_state(self);
        PostOrderIterator { state_stack: vec![initial_state] }
    }

    pub fn breadth_first_iter(&'a self) -> BreadthFirstIterator<'a> {
        let mut queue = VecDeque::new();
        queue.push_back(self);
        
        BreadthFirstIterator { state_queue: queue }
    }
}
