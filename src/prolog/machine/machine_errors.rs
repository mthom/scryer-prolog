use prolog::ast::*;
use prolog::builtins::*;
use prolog::machine::machine_state::*;
use prolog::num::bigint::BigInt;

use std::rc::Rc;

pub(super) type MachineError = Vec<HeapCellValue>;

impl MachineState {
    pub(super) fn evaluation_error(&self, eval_error: EvalError) -> MachineError {
        functor!("evaluation_error", 1, [heap_atom!(eval_error.as_str())])
    }
    
    pub(super) fn type_error(&self, valid_type: ValidType, culprit: Addr) -> MachineError {
        functor!("type_error", 2, [heap_atom!(valid_type.as_str()), HeapCellValue::Addr(culprit)])
    }

    pub(super) fn existence_error(&self, name: ClauseName, arity: usize) -> MachineError {
        let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name)));
        let h = self.heap.h;
        
        let mut error = functor!("existence_error", 2, [heap_atom!("procedure"), heap_str!(3 + h)]);
        error.append(&mut functor!("/", 2, [name, heap_integer!(arity)], Fixity::In));
        
        error
    }

    pub(super) fn instantiation_error(&self) -> MachineError {
        functor!("instantiation_error")
    }

    pub(super) fn representation_error(&self, flag: RepFlag) -> MachineError {
        functor!("representation_error", 1, [heap_atom!(flag.as_str())])
    }

    pub(super) fn error_form(&self, mut err: MachineError) -> MachineError {
        let h = self.heap.h;
        let mut error_form = functor!("error", 2,
                                      [HeapCellValue::Addr(Addr::HeapCell(h + 3)),
                                       HeapCellValue::Addr(Addr::HeapCell(h + 2))]);
        
        error_form.append(&mut err);
        error_form
    }
    
    pub(super) fn throw_exception(&mut self, err: MachineError) {
        let h = self.heap.h;

        self.ball.0 = 0;
        self.ball.1.truncate(0);

        self.heap.append(err);

        self.registers[1] = Addr::HeapCell(h);        
        self.goto_throw();
    }    
} 
