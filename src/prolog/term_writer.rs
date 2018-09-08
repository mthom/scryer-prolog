use prolog_parser::ast::*;

use prolog::heap_iter::*;
use prolog::instructions::HeapCellValue;
use prolog::machine::machine_state::MachineState;

pub fn term_write(machine_st: &'a MachineState, addr: Addr) -> Result<Term, ParserError> {
    let pre_order_iter  = HCPreOrderIterator::new(machine_st, addr);
    let post_order_iter = HCPostOrderIterator::new(pre_order_iter);
    let acyclic_post_order_iter = HCAcyclicIterator::new(post_order_iter);

    let mut stack = vec![];
    
    for value in acyclic_post_order_iter {
        match value {
            HeapCellValue::NamedStr(arity, name, fixity)
                if stack.len() >= arity => {
                    let subterms: Vec<_> = stack[stack.len() - arity ..].drain().collect();
                    stack.push(Box::new(Term::Clause(Cell::default(), name, subterms, fixity)));
                },
            HeapCellValue::Addr(Addr::Con(constant)) =>
                stack.push(Box::new(Term::Constant(Cell::default(), constant))),
            HeapCellValue::Addr(Addr::Lis(_))
                if stack.len() >= 2 => {
                    let subterms: Vec<_> = stack[stack.len() - 2 ..].drain().collect();                    
                    stack.push(Box::new(Term::Cons(Cell::default(), subterms[0], subterms[1])));
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
            return Ok(term);
        } 
    }

    Err(ParserError::IncompleteReduction)
}
