use prolog::ast::*;
use prolog::builtins::*;
use prolog::machine::machine_state::*;
use prolog::num::bigint::BigInt;

use std::rc::Rc;

pub(super) type MachineError = Vec<HeapCellValue>;

// used by '$skip_max_list'.
pub(super) enum CycleSearchResult {
    EmptyList,
    NotList,
    PartialList(usize, usize), // the list length (up to max), and an offset into the heap.
    ProperList(usize), // the list length.
    UntouchedList(usize) // the address of an uniterated Addr::Lis(address).
}

impl MachineState {
    // see 8.4.3 of Draft Technical Corrigendum 2.
    pub(super) fn check_sort_errors(&self) -> Result<(), MachineError> {
        let list   = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(usize::max_value(), list.clone()) {
            CycleSearchResult::PartialList(..) =>
                Err(self.error_form(self.instantiation_error())),
            CycleSearchResult::NotList =>
                Err(self.error_form(self.type_error(ValidType::List, list))),
            _ => Ok(())
        }?;

        match self.detect_cycles(usize::max_value(), sorted.clone()) {
            CycleSearchResult::NotList if !sorted.is_ref() =>
                Err(self.error_form(self.type_error(ValidType::List, sorted))),
            _ => Ok(())
        }
    }

    // see 8.4.4 of Draft Technical Corrigendum 2.
    pub(super) fn check_keysort_errors(&self) -> Result<(), MachineError> {
        let pairs  = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(usize::max_value(), pairs.clone()) {
            CycleSearchResult::PartialList(..) =>
                Err(self.error_form(self.instantiation_error())),
            CycleSearchResult::NotList =>
                Err(self.error_form(self.type_error(ValidType::List, pairs))),
            _ => Ok(())
        }?;

        match self.detect_cycles(usize::max_value(), sorted.clone()) {
            CycleSearchResult::NotList if !sorted.is_ref() =>
                Err(self.error_form(self.type_error(ValidType::List, sorted))),
            _ => {
                let mut addr = sorted;

                while let Addr::Lis(mut l) = self.store(self.deref(addr)) {
                    loop {
                        match self.heap[l].clone() {
                            HeapCellValue::Addr(Addr::Str(new_l)) => l = new_l,
                            HeapCellValue::NamedStr(2, ref name, Some(Fixity::In))
                                if name.as_str() == "-" => break,
                            HeapCellValue::Addr(Addr::HeapCell(_)) => break,
                            HeapCellValue::Addr(Addr::StackCell(..)) => break,
                            _ => return Err(self.error_form(self.type_error(ValidType::Pair,
                                                                            Addr::HeapCell(l))))
                        };
                    }

                    addr = Addr::HeapCell(l + 2);
                }

                Ok(())
            }
        }
    }

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
