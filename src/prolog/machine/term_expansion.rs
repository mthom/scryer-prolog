use prolog_parser::ast::*;
use prolog_parser::parser::*;

use prolog::heap_iter::*;
use prolog::instructions::HeapCellValue;
use prolog::machine::*;
use prolog::read::*;

use std::cell::Cell;
use std::io::Read;

pub struct TermStream<R: Read> {
    stack: Vec<Term>,
    parser: Parser<R>,
    in_module: bool
}

impl<R: Read> TermStream<R> {
    pub fn new(src: R, atom_tbl: TabledData<Atom>, flags: MachineFlags) -> Self {
        TermStream {
            stack: Vec::new(),
            parser: Parser::new(src, atom_tbl, flags),
            in_module: false
        }
    }

    #[inline]
    pub fn add_to_top(&mut self, buf: &str) {
        self.parser.add_to_top(buf);
    }

    #[inline]
    pub fn eof(&mut self) -> Result<bool, ParserError> {
        Ok(self.stack.is_empty() && self.parser.eof()?)
    }

    #[inline]
    pub fn empty_tokens(&mut self) {
        self.parser.reset();
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

    pub fn read_term(&mut self, wam: &mut Machine, op_dir: &OpDir) -> Result<Term, ParserError>
    {
        loop {
            while let Some(term) = self.stack.pop() {
                match wam.try_expand_term(&term)? {
                    Some(term) => self.enqueue_term(term)?,
                    None => return Ok(term)
                };
            }

            let term = self.parser.read_term(composite_op!(self.in_module, &wam.op_dir, op_dir))?;
            self.stack.push(term);
        }
    }
}

impl Machine {
    fn try_expand_term(&mut self, term: &Term) -> Result<Option<Term>, ParserError> {
        let term_h = write_term_to_heap(term, &mut self.ms);
        let h = self.ms.heap.h;

        self.ms[temp_v!(1)] = Addr::HeapCell(term_h);
        self.ms.heap.push(HeapCellValue::Addr(Addr::HeapCell(h)));
        self.ms[temp_v!(2)] = Addr::HeapCell(h);

        let code = vec![call_clause!(ClauseType::Hook(CompileTimeHook::TermExpansion), 2, 0, true)];
        self.submit_query(code, AllocVarDict::new());

        if self.failed() {
            self.reset();
            Ok(None)
        } else {
            Ok(Some(read_term_from_heap(&self.ms, Addr::HeapCell(h))?))
        }
    }
}

pub fn read_term_from_heap(machine_st: &MachineState, addr: Addr) -> Result<Term, ParserError>
{
    let pre_order_iter  = HCPreOrderIterator::new(machine_st, addr);
    let post_order_iter = HCPostOrderIterator::new(pre_order_iter);

    let mut stack = vec![];

    for value in post_order_iter {
        match value {
            HeapCellValue::NamedStr(arity, ref name, fixity)
                if stack.len() >= arity => {
                    let stack_len = stack.len();
                    let subterms: Vec<_> = stack.drain(stack_len - arity ..).collect();

                    stack.push(Box::new(Term::Clause(Cell::default(), name.clone(), subterms,
                                                     fixity)));
                },
            HeapCellValue::Addr(Addr::Con(constant)) =>
                stack.push(Box::new(Term::Constant(Cell::default(), constant))),
            HeapCellValue::Addr(Addr::Lis(_))
                if stack.len() >= 2 => {
                    let stack_len = stack.len();
                    let (head, tail) = {
                        let mut iter  = stack.drain(stack_len - 2 ..);
                        (iter.next().unwrap(), iter.next().unwrap())
                    };

                    stack.push(Box::new(Term::Cons(Cell::default(), head, tail)));
                },
            HeapCellValue::Addr(Addr::HeapCell(h)) =>
                stack.push(Box::new(Term::Var(Cell::default(), Rc::new(format!("_{}", h))))),
            HeapCellValue::Addr(Addr::StackCell(fr, sc)) =>
                stack.push(Box::new(Term::Var(Cell::default(), Rc::new(format!("_{}_{}", sc, fr))))),
            _ => return Err(ParserError::IncompleteReduction)
        }
    }

    if let Some(term) = stack.pop() {
        if stack.is_empty() {
            return Ok(*term);
        }
    }

    Err(ParserError::IncompleteReduction)
}
