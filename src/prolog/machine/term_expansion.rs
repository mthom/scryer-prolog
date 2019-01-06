use prolog_parser::ast::*;
use prolog_parser::parser::*;

use prolog::instructions::HeapCellValue;
use prolog::machine::*;
use prolog::read::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::io::Read;
use std::iter::Rev;
use std::vec::IntoIter;

fn unfold_by_str_once(term: &mut Term, s: &str) -> Option<(Term, Term)>
{
    if let &mut Term::Clause(_, ref name, ref mut subterms, _) = term {
        if name.as_str() == s && subterms.len() == 2 {
            let snd = *subterms.pop().unwrap();
            let fst = *subterms.pop().unwrap();

            return Some((fst, snd));
        }
    }

    None
}

pub fn unfold_by_str(mut term: Term, s: &str) -> Vec<Term>
{
    let mut terms = vec![];

    while let Some((fst, snd)) = unfold_by_str_once(&mut term, s) {
        terms.push(fst);
        term = snd;
    }

    terms.push(term);
    terms
}

pub fn fold_by_str<I>(terms: I, mut term: Term, sym: ClauseName) -> Term
    where I: DoubleEndedIterator<Item=Term>
{
    for prec in terms.rev() {
        term = Term::Clause(Cell::default(), sym.clone(),
                            vec![Box::new(prec), Box::new(term)],
                            None);
    }

    term
}

fn extract_from_list(head: Box<Term>, tail: Box<Term>)
                     -> Result<Rev<IntoIter<Term>>, ParserError>
{
    let mut terms = vec![*head];
    let mut tail  = *tail;

    while let Term::Cons(_, head, next_tail) = tail {
        terms.push(*head);
        tail = *next_tail;
    }

    if let Term::Constant(_, Constant::EmptyList) = tail {
        Ok(terms.into_iter().rev())
    } else {
        Err(ParserError::ExpectedTopLevelTerm)
    }
}

pub struct TermStream<'a, R: Read> {
    stack: Vec<Term>,
    pub(crate) indices: &'a mut IndexStore,
    policies: &'a mut MachinePolicies,
    pub(crate) code_repo: &'a mut CodeRepo,
    parser: Parser<R>,
    in_module: bool,
    pub(crate) flags: MachineFlags,
    term_expansion_lens: (usize, usize),
    goal_expansion_lens: (usize, usize),
}

pub struct ExpansionAdditionResult {
    term_expansion_additions: (Predicate, VecDeque<TopLevel>),
    goal_expansion_additions: (Predicate, VecDeque<TopLevel>)
}

impl ExpansionAdditionResult {
    pub fn take_term_expansions(&mut self) -> (Predicate, VecDeque<TopLevel>) {
        let tes  = mem::replace(&mut self.term_expansion_additions.0, Predicate::new());
        let teqs = mem::replace(&mut self.term_expansion_additions.1, VecDeque::from(vec![]));

        (tes, teqs)
    }

    pub fn take_goal_expansions(&mut self) -> (Predicate, VecDeque<TopLevel>) {
        let ges  = mem::replace(&mut self.goal_expansion_additions.0, Predicate::new());
        let geqs = mem::replace(&mut self.goal_expansion_additions.1, VecDeque::from(vec![]));

        (ges, geqs)
    }
}

impl<'a, R: Read> Drop for TermStream<'a, R> {
    fn drop(&mut self) {
        self.indices.in_situ_code_dir.clear();
        self.code_repo.in_situ_code.clear();        
        discard_result!(self.rollback_expansion_code());
    }
}

impl<'a, R: Read> TermStream<'a, R> {
    pub fn new(src: R, atom_tbl: TabledData<Atom>, flags: MachineFlags,
               indices: &'a mut IndexStore, policies: &'a mut MachinePolicies,
               code_repo: &'a mut CodeRepo)
               -> Self
    {
        TermStream {
            stack: Vec::new(),
            term_expansion_lens: code_repo.term_dir_entry_len((clause_name!("term_expansion"), 2)),
            goal_expansion_lens: code_repo.term_dir_entry_len((clause_name!("goal_expansion"), 2)),
            code_repo,
            indices,
            policies,
            parser: Parser::new(src, atom_tbl, flags),
            in_module: false,
            flags
        }
    }

    #[inline]
    pub fn incr_expansion_lens(&mut self, hook: CompileTimeHook, len: usize, queue_len: usize) {
        match hook {
            CompileTimeHook::UserTermExpansion => {
                self.term_expansion_lens.0 += len;
                self.term_expansion_lens.1 += queue_len;
            },
            CompileTimeHook::UserGoalExpansion => {
                self.goal_expansion_lens.0 += len;
                self.goal_expansion_lens.1 += queue_len;
            },
            _ => {}
        }
    }

    #[inline]
    pub fn set_atom_tbl(&mut self, atom_tbl: TabledData<Atom>) {
        self.parser.set_atom_tbl(atom_tbl);
    }

    #[inline]
    pub fn add_to_top(&mut self, buf: &str) {
        self.parser.add_to_top(buf);
    }

    #[inline]
    pub fn eof(&mut self) -> Result<bool, ParserError> {
        Ok(self.stack.is_empty() && self.parser.eof()?)
    }

    pub fn rollback_expansion_code(&mut self) -> Result<ExpansionAdditionResult, ParserError> {
        let te_len = self.term_expansion_lens.0;
        let te_queue_len = self.term_expansion_lens.1;

        let ge_len = self.goal_expansion_lens.0;
        let ge_queue_len = self.goal_expansion_lens.1;

        let term_expansion_additions =
            self.code_repo.truncate_terms((clause_name!("term_expansion"), 2),
                                          te_len, te_queue_len);
        let goal_expansion_additions =
            self.code_repo.truncate_terms((clause_name!("goal_expansion"), 2),
                                          ge_len, ge_queue_len);

        self.code_repo.compile_hook(CompileTimeHook::TermExpansion, self.flags)?;
        self.code_repo.compile_hook(CompileTimeHook::GoalExpansion, self.flags)?;

        Ok(ExpansionAdditionResult {
            term_expansion_additions,
            goal_expansion_additions
        })
    }

    fn enqueue_term(&mut self, term: Term) -> Result<(), ParserError> {
        match term {
            Term::Cons(_, head, tail) => {
                let iter = extract_from_list(head, tail)?;
                Ok(self.stack.extend(iter))
            },
            Term::Clause(..) | Term::Constant(_, Constant::Atom(..)) =>
                Ok(self.stack.push(term)),
            _ => Err(ParserError::ExpectedTopLevelTerm)
        }
    }

    fn parse_expansion_output(&mut self, term_string: &str, op_dir: &OpDir)
                              -> Result<Term, ParserError>
    {
        let mut parser = Parser::new(term_string.trim().as_bytes(), self.indices.atom_tbl.clone(),
                                     self.flags);
        parser.read_term(composite_op!(self.in_module, &self.indices.op_dir, op_dir))
    }

    pub fn read_term(&mut self, machine_st: &mut MachineState, op_dir: &OpDir)
                     -> Result<Term, ParserError>
    {
        loop {
            while let Some(term) = self.stack.pop() {
                match machine_st.try_expand_term(self.indices, self.policies, self.code_repo,
                                                 &term, CompileTimeHook::TermExpansion)
                {
                    Some(term_string) => {
                        let term = self.parse_expansion_output(term_string.as_str(), op_dir)?;
                        self.enqueue_term(term)?
                    },
                    None => {
                        let term = self.run_goal_expanders(machine_st, op_dir, term)?;
                        return Ok(term);
                    }
                };
            }

            self.parser.reset();
            let term = self.parser.read_term(composite_op!(self.in_module, &self.indices.op_dir,
                                                           op_dir))?;
            self.stack.push(term);
        }
    }

    fn run_goal_expanders(&mut self, machine_st: &mut MachineState, op_dir: &OpDir, term: Term)
                          -> Result<Term, ParserError>
    {
        match term {
            Term::Clause(cell, name, mut terms, arity) => {
                let mut new_terms = {
                    let old_terms = if name.as_str() == ":-" && terms.len() == 2 {
                        let comma_term = *terms.pop().unwrap();
                        unfold_by_str(comma_term, ",")
                    } else if name.as_str() == "?-" && terms.len() == 1 {
                        let comma_term = *terms.pop().unwrap();
                        unfold_by_str(comma_term, ",")
                    } else {
                        return Ok(Term::Clause(cell, name, terms, arity));
                    };

                    self.expand_goals(machine_st, op_dir, VecDeque::from(old_terms))?
                };

                let initial_term = new_terms.pop().unwrap();

                terms.push(Box::new(fold_by_str(new_terms.into_iter(), initial_term,
                                                clause_name!(","))));
                Ok(Term::Clause(cell, name, terms, None))
            },
            _ =>
                Ok(term)
        }
    }

    fn expand_goals(&mut self, machine_st: &mut MachineState, op_dir: &OpDir,
                    mut terms: VecDeque<Term>)
                    -> Result<Vec<Term>, ParserError>
    {
        let mut results = vec![];

        while let Some(term) = terms.pop_front() {
            match machine_st.try_expand_term(self.indices, self.policies, self.code_repo,
                                             &term, CompileTimeHook::GoalExpansion)
            {
                Some(term_string) => {
                    let term = self.parse_expansion_output(term_string.as_str(), op_dir)?;

                    match term {
                        Term::Cons(_, head, tail) =>
                            for term in extract_from_list(head, tail)? {
                                terms.push_front(term);
                            },
                        term =>
                            terms.push_front(term)
                    };
                },
                None => results.push(term)
            }
        }

        Ok(results)
    }
}

impl MachineState {
    fn try_expand_term(&mut self, indices: &mut IndexStore, policies: &mut MachinePolicies,
                       code_repo: &mut CodeRepo, term: &Term, hook: CompileTimeHook)
                       -> Option<String>
    {
        let (term_h, var_dict) = write_term_to_heap(term, self);
        let h = self.heap.h;

        self[temp_v!(1)] = Addr::HeapCell(term_h);
        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
        self[temp_v!(2)] = Addr::HeapCell(h);

        let code = vec![call_clause!(ClauseType::Hook(hook), 2, 0, true)];

        code_repo.cached_query = code;
        self.run_query(indices, policies, code_repo, &AllocVarDict::new(), &mut HeapVarDict::new());

        if self.fail {
            self.reset();
            None
        } else {
            let mut output  = {
                let output = PrinterOutputter::new();
                let mut printer = HCPrinter::from_heap_locs(&self, output, &var_dict);

                printer.quoted = true;
                printer.numbervars = true;
                printer.ignore_ops = true;

                printer.see_all_locs();

                printer.print(Addr::HeapCell(h))
            };

            output.push_char('.');

            self.reset();
            Some(output.result())
        }
    }
}
