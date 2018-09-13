use prolog_parser::ast::*;

use prolog::heap_iter::*;
use prolog::instructions::*;
use prolog::machine::machine_state::MachineState;

use std::cell::Cell;
use std::rc::Rc;

pub fn term_write(machine_st: &MachineState, addr: Addr) -> Result<Term, ParserError>
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
                    let mut iter  = stack.drain(stack_len - 2 ..);
                    
                    let head = iter.next().unwrap();
                    let tail = iter.next().unwrap();

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
