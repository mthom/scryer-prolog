use prolog_parser::ast::*;
use prolog_parser::parser::*;

use prolog::instructions::HeapCellValue;
use prolog::machine::*;
use prolog::read::*;

use std::io::Read;

pub struct TermStream<'a, R: Read> {
    stack: Vec<Term>,
    pub(crate) indices: &'a mut IndexStore,
    policies: &'a mut MachinePolicies,
    pub(crate) code_repo: &'a mut CodeRepo,
    parser: Parser<R>,
    in_module: bool,
    flags: MachineFlags        
}

impl<'a, R: Read> TermStream<'a, R> {
    pub fn new(src: R, atom_tbl: TabledData<Atom>, flags: MachineFlags,
               indices: &'a mut IndexStore, policies: &'a mut MachinePolicies,
               code_repo: &'a mut CodeRepo)
               -> Self
    {
        TermStream {
            stack: Vec::new(),
            indices,
            policies,
            code_repo,
            parser: Parser::new(src, atom_tbl, flags),
            in_module: false,
            flags
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

    fn enqueue_term(&mut self, term: Term) -> Result<(), ParserError> {
        match term {
            Term::Cons(_, head, tail) => {
                let mut terms = vec![*head];
                let mut tail = *tail;

                while let Term::Cons(_, head, next_tail) = tail {
                    terms.push(*head);
                    tail = *next_tail;
                }

                if let Term::Constant(_, Constant::EmptyList) = tail {
                    Ok(self.stack.extend(terms.into_iter().rev()))
                } else {
                    Err(ParserError::ExpectedTopLevelTerm)
                }
            },
            Term::Clause(..) | Term::Constant(_, Constant::Atom(..)) =>
                Ok(self.stack.push(term)),
            _ => Err(ParserError::ExpectedTopLevelTerm)
        }
    }

    fn parse_expansion_output(&mut self, term_string: &str, op_dir: &OpDir) -> Result<Term, ParserError> {
        let mut parser = Parser::new(term_string.trim().as_bytes(), self.indices.atom_tbl.clone(), self.flags);        
        parser.read_term(composite_op!(self.in_module,
                                       &self.indices.op_dir,
                                       op_dir))
    }
    
    pub fn read_term(&mut self, machine_st: &mut MachineState, op_dir: &OpDir)
                     -> Result<Term, ParserError>
    {
        loop {
            while let Some(term) = self.stack.pop() {
                match machine_st.try_expand_term(self.indices, self.policies, self.code_repo, &term)
                {
                    Some(term_string) => {
                        let term = self.parse_expansion_output(term_string.as_str(), op_dir)?;
                        self.enqueue_term(term)?
                    },
                    None => return Ok(term)
                };
            }

            self.parser.reset();
            let term = self.parser.read_term(composite_op!(self.in_module,
                                                           &self.indices.op_dir,
                                                           op_dir))?;
            self.stack.push(term);
        }
    }
}

impl MachineState {
    fn try_expand_term(&mut self, indices: &mut IndexStore, policies: &mut MachinePolicies,
                       code_repo: &mut CodeRepo, term: &Term)
                       -> Option<String>
    {
        let term_h = write_term_to_heap(term, self);
        let h = self.heap.h;

        self[temp_v!(1)] = Addr::HeapCell(term_h);
        self.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
        self[temp_v!(2)] = Addr::HeapCell(h);

        let code = vec![call_clause!(ClauseType::Hook(CompileTimeHook::TermExpansion), 2, 0, true)];

        code_repo.cached_query = Some(code);
        self.run_query(indices, policies, code_repo, &AllocVarDict::new(), &mut HeapVarDict::new());

        if self.fail {
            self.reset();
            None
        } else {
            let mut output  = {
                let mut printer = HCPrinter::new(&self, PrinterOutputter::new());
                
                printer.quoted = true;
                printer.numbervars = true;
                
                printer.print(Addr::HeapCell(h))
            };

            output.push_char('.');

            self.reset();
            Some(output.result())
        }
    }
}
