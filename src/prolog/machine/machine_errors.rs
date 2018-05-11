use prolog::ast::*;
use prolog::machine::machine_state::*;
use prolog::num::bigint::BigInt;

use std::rc::Rc;

pub(super) type MachineError = Vec<HeapCellValue>;
pub(super) type MachineStub = Vec<HeapCellValue>;

// from 7.12.2 b) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum ValidType {
    Atom,
    Atomic,
    Byte,
    Callable,
    Character,
    Compound,
    Evaluable,
    InByte,
    InCharacter,
    Integer,
    List,
    Number,
    Pair,
    PredicateIndicator,
    Variable
}

impl ValidType {
    pub fn as_str(self) -> &'static str {
        match self {
            ValidType::Atom => "atom",
            ValidType::Atomic => "atomic",
            ValidType::Byte => "byte",
            ValidType::Callable => "callable",
            ValidType::Character => "character",
            ValidType::Compound => "compound",
            ValidType::Evaluable => "evaluable",
            ValidType::InByte => "in_byte",
            ValidType::InCharacter => "in_character",
            ValidType::Integer => "integer",
            ValidType::List => "list",
            ValidType::Number => "number",
            ValidType::Pair => "pair",
            ValidType::PredicateIndicator => "predicate_indicator",
            ValidType::Variable => "variable"
        }
    }
}

// from 7.12.2 f) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum RepFlag {
    Character,
    CharacterCode,
    InCharacterCode,
    MaxArity,
    MaxInteger,
    MinInteger
}

impl RepFlag {
    pub fn as_str(self) -> &'static str {
        match self {
            RepFlag::Character => "character",
            RepFlag::CharacterCode => "character_code",
            RepFlag::InCharacterCode => "in_character_code",
            RepFlag::MaxArity => "max_arity",
            RepFlag::MaxInteger => "max_integer",
            RepFlag::MinInteger => "min_integer"
        }
    }
}

// from 7.12.2 g) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum EvalError {
    FloatOverflow,
    IntOverflow,
    Undefined,
    Underflow,
    ZeroDivisor
}

impl EvalError {
    pub fn as_str(self) -> &'static str {
        match self {
            EvalError::FloatOverflow => "float_overflow",
            EvalError::IntOverflow => "int_overflow",
            EvalError::Undefined => "undefined",
            EvalError::Underflow => "underflow",
            EvalError::ZeroDivisor => "zero_divisor"
        }
    }
}

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
        let stub   = self.functor_stub(clause_name!("sort"), 2);
        let list   = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::PartialList(..) =>
                Err(self.error_form(self.instantiation_error(), stub.clone())),
            CycleSearchResult::NotList =>
                Err(self.error_form(self.type_error(ValidType::List, list), stub.clone())),
            _ => Ok(())
        }?;

        match self.detect_cycles(sorted.clone()) {
            CycleSearchResult::NotList if !sorted.is_ref() =>
                Err(self.error_form(self.type_error(ValidType::List, sorted), stub)),
            _ => Ok(())
        }
    }

    fn check_for_list_pairs(&self, list: Addr) -> Result<(), MachineError> {
        let stub = self.functor_stub(clause_name!("keysort"), 2);

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::NotList if !list.is_ref() =>
                Err(self.error_form(self.type_error(ValidType::List, list), stub)),
            _ => {
                let mut addr = list;

                while let Addr::Lis(l) = self.store(self.deref(addr)) {
                    let mut new_l = l;

                    loop {
                        match self.heap[new_l].clone() {
                            HeapCellValue::Addr(Addr::Str(l)) => new_l = l,
                            HeapCellValue::NamedStr(2, ref name, Some(Fixity::In))
                                if name.as_str() == "-" => break,
                            HeapCellValue::Addr(Addr::HeapCell(_)) => break,
                            HeapCellValue::Addr(Addr::StackCell(..)) => break,
                            _ => return Err(self.error_form(self.type_error(ValidType::Pair,
                                                                            Addr::HeapCell(l)),
                                                            stub))
                        };
                    }

                    addr = Addr::HeapCell(l + 1);
                }

                Ok(())
            }
        }
    }

    // see 8.4.4 of Draft Technical Corrigendum 2.
    pub(super) fn check_keysort_errors(&self) -> Result<(), MachineError> {
        let stub   = self.functor_stub(clause_name!("keysort"), 2);
        let pairs  = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(pairs.clone()) {
            CycleSearchResult::PartialList(..) =>
                Err(self.error_form(self.instantiation_error(), stub)),
            CycleSearchResult::NotList =>
                Err(self.error_form(self.type_error(ValidType::List, pairs), stub)),
            _ => Ok(())
        }?;

        self.check_for_list_pairs(sorted)
    }

    pub(super) fn functor_stub(&self, name: ClauseName, arity: usize) -> MachineStub {
        let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name)));
        functor!("/", 2, [name, heap_integer!(arity)], Fixity::In)
    }

    pub(super) fn evaluation_error(&self, eval_error: EvalError) -> MachineError {
        functor!("evaluation_error", 1, [heap_atom!(eval_error.as_str())])
    }

    pub(super) fn type_error(&self, valid_type: ValidType, culprit: Addr) -> MachineError {
        functor!("type_error", 2, [heap_atom!(valid_type.as_str()), HeapCellValue::Addr(culprit)])
    }

    pub(super) fn existence_error(&self, name: ClauseName, arity: usize) -> MachineError {
        let h = self.heap.h;

        let mut error = functor!("existence_error", 2, [heap_atom!("procedure"), heap_str!(3 + h)]);
        error.append(&mut self.functor_stub(name, arity));

        error
    }

    pub(super) fn instantiation_error(&self) -> MachineError {
        functor!("instantiation_error")
    }

    pub(super) fn representation_error(&self, flag: RepFlag) -> MachineError {
        functor!("representation_error", 1, [heap_atom!(flag.as_str())])
    }

    pub(super) fn error_form(&self, err: MachineError, src: MachineStub) -> MachineError {
        let h = self.heap.h;

        let mut error_form = vec![HeapCellValue::NamedStr(2, clause_name!("error"), None),
                                  HeapCellValue::Addr(Addr::HeapCell(h + 3)),
                                  HeapCellValue::Addr(Addr::HeapCell(h + 3 + err.len()))];

        error_form.extend(err.into_iter());
        error_form.extend(src.into_iter());

        error_form
    }

    pub(super) fn throw_exception(&mut self, err: MachineError) {
        let h = self.heap.h;

        self.ball.boundary = 0;
        self.ball.stub.truncate(0);

        self.heap.append(err);

        self.registers[1] = Addr::HeapCell(h);

        self.set_ball();
        self.unwind_stack();
    }
}
