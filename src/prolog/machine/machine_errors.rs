use prolog_parser::ast::*;

use prolog::ast::*;
use prolog::machine::machine_state::*;
use prolog::num::bigint::BigInt;

use std::rc::Rc;

pub(super) type MachineStub = Vec<HeapCellValue>;

#[derive(Clone, Copy)]
enum ErrorProvenance {
    Constructed, // if constructed, offset the addresses.
    Received     // otherwise, preserve the addresses.
}

pub(super) struct MachineError {
    stub: MachineStub,
    from: ErrorProvenance
}

impl MachineError {
    pub(super) fn functor_stub(name: ClauseName, arity: usize) -> MachineStub {
        let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name)));
        functor!("/", 2, [name, heap_integer!(arity)], Fixity::In)
    }

    pub(super) fn evaluation_error(eval_error: EvalError) -> Self {
        let stub = functor!("evaluation_error", 1, [heap_atom!(eval_error.as_str())]);
        MachineError { stub, from: ErrorProvenance::Received }
    }

    pub(super) fn type_error(valid_type: ValidType, culprit: Addr) -> Self {
        let stub = functor!("type_error", 2, [heap_atom!(valid_type.as_str()),
                                              HeapCellValue::Addr(culprit)]);

        MachineError { stub, from: ErrorProvenance::Received }
    }

    pub(super)
    fn module_resolution_error(h: usize, mod_name: ClauseName, name: ClauseName, arity: usize) -> Self
    {
        let mod_name = HeapCellValue::Addr(Addr::Con(Constant::Atom(mod_name)));
        let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name)));

        let mut stub = functor!("evaluation_error", 1, [HeapCellValue::Addr(Addr::HeapCell(h + 2))]);

        stub.append(&mut functor!("/", 2, [HeapCellValue::Addr(Addr::HeapCell(h + 2 + 3)),
                                           heap_integer!(arity)],
                                  Fixity::In));
        stub.append(&mut functor!(":", 2, [mod_name, name], Fixity::In));

        MachineError { stub, from: ErrorProvenance::Constructed }
    }

    pub(super) fn existence_error(h: usize, name: ClauseName, arity: usize) -> Self {
        let mut stub = functor!("existence_error", 2, [heap_atom!("procedure"), heap_str!(3 + h)]);
        stub.append(&mut Self::functor_stub(name, arity));

        MachineError { stub, from: ErrorProvenance::Constructed }
    }

    pub(super) fn syntax_error(h: usize, err: ParserError) -> Self {
        let err = match err {
            ParserError::Arithmetic(_) =>
                vec![heap_atom!("arithmetic_error")],
            ParserError::BackQuotedString =>
                vec![heap_atom!("back_quoted_string")],
            ParserError::UnexpectedChar(c) =>
                functor!("unexpected_char", 1, [heap_char!(c)]),
            ParserError::UnexpectedEOF =>
                vec![heap_atom!("unexpected_end_of_file")],
            ParserError::ExpectedRel =>
                vec![heap_atom!("expected_relation")],
            ParserError::InadmissibleFact =>                
                vec![heap_atom!("inadmissible_fact")],
            ParserError::InadmissibleQueryTerm =>                
                vec![heap_atom!("inadmissible_query_term")],
            ParserError::IncompleteReduction =>
                vec![heap_atom!("incomplete_reduction")],
            ParserError::InconsistentEntry =>
                vec![heap_atom!("inconsistent_entry")],
            ParserError::InvalidModuleDecl =>
                vec![heap_atom!("invalid_module_declaration")],
            ParserError::InvalidModuleExport =>
                vec![heap_atom!("invalid_module_export")],
            ParserError::InvalidModuleResolution =>
                vec![heap_atom!("invalid_module_resolution")],
            ParserError::InvalidRuleHead =>
                vec![heap_atom!("invalid_head_of_rule")],
            ParserError::InvalidUseModuleDecl =>
                vec![heap_atom!("invalid_use_module_declaration")],
            ParserError::IO(_) =>
                vec![heap_atom!("input_output_error")],
            ParserError::MissingQuote =>
                vec![heap_atom!("missing_quote")],
            ParserError::NonPrologChar =>
                vec![heap_atom!("non_prolog_character")],
            ParserError::ParseBigInt =>
                vec![heap_atom!("cannot_parse_big_int")],
            ParserError::ParseFloat =>
                vec![heap_atom!("cannot_parse_float")],
            ParserError::Utf8Conversion(_) =>
                vec![heap_atom!("utf8_conversion_error")]
        };

        let mut stub = if err.len() == 1 {
            functor!("syntax_error", 1)            
        } else {
            functor!("syntax_error", 1, [heap_str!(h + 2)])
        };
        
        stub.extend(err.into_iter());
        MachineError { stub, from: ErrorProvenance::Constructed }
    }

    pub(super) fn domain_error(error: DomainError, culprit: Addr) -> Self {
        let stub = functor!("domain_error", 2, [heap_atom!(error.as_str()),
                                                HeapCellValue::Addr(culprit)]);
        MachineError { stub, from: ErrorProvenance::Received }
    }

    pub(super) fn instantiation_error() -> Self {
        let stub = functor!("instantiation_error");
        MachineError { stub, from: ErrorProvenance::Received }
    }

    pub(super) fn representation_error(flag: RepFlag) -> Self {
        let stub = functor!("representation_error", 1, [heap_atom!(flag.as_str())]);
        MachineError { stub, from: ErrorProvenance::Received }
    }

    fn into_iter(self, offset: usize) -> Box<Iterator<Item=HeapCellValue>> {
        match self.from {
            ErrorProvenance::Constructed =>
                Box::new(self.stub.into_iter().map(move |hcv| {
                    match hcv {
                        HeapCellValue::Addr(addr) => HeapCellValue::Addr(addr + offset),
                        hcv => hcv
                    }
                })),
            ErrorProvenance::Received =>
                Box::new(self.stub.into_iter())
        }
    }

    fn len(&self) -> usize {
        self.stub.len()
    }
}

// from 7.12.2 b) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum ValidType {
    Atom,
    Atomic,
//    Byte,
    Callable,
//    Character,
    Compound,
//    Evaluable,
//    InByte,
//    InCharacter,
    Integer,
    List,
//    Number,
    Pair,
//    PredicateIndicator,
//    Variable
}

impl ValidType {
    pub fn as_str(self) -> &'static str {
        match self {
            ValidType::Atom => "atom",
            ValidType::Atomic => "atomic",
//            ValidType::Byte => "byte",
            ValidType::Callable => "callable",
//            ValidType::Character => "character",
            ValidType::Compound => "compound",
//            ValidType::Evaluable => "evaluable",
//            ValidType::InByte => "in_byte",
//            ValidType::InCharacter => "in_character",
            ValidType::Integer => "integer",
            ValidType::List => "list",
//            ValidType::Number => "number",
            ValidType::Pair => "pair",
//            ValidType::PredicateIndicator => "predicate_indicator",
//            ValidType::Variable => "variable"
        }
    }
}

#[derive(Clone, Copy)]
pub enum DomainError {
    NotLessThanZero
}

impl DomainError {
    pub fn as_str(self) -> &'static str {
        match self {
            DomainError::NotLessThanZero => "not_less_than_zero"
        }
    }
}

// from 7.12.2 f) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum RepFlag {
//    Character,
//    CharacterCode,
//    InCharacterCode,
    MaxArity,
//    MaxInteger,
//    MinInteger
}

impl RepFlag {
    pub fn as_str(self) -> &'static str {
        match self {
//            RepFlag::Character => "character",
//            RepFlag::CharacterCode => "character_code",
//            RepFlag::InCharacterCode => "in_character_code",
            RepFlag::MaxArity => "max_arity",
//            RepFlag::MaxInteger => "max_integer",
//            RepFlag::MinInteger => "min_integer"
        }
    }
}

// from 7.12.2 g) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum EvalError {
//    FloatOverflow,
//    IntOverflow,
//    Undefined,
//    Underflow,
    ZeroDivisor,
    NoRoots
}

impl EvalError {
    pub fn as_str(self) -> &'static str {
        match self {
//            EvalError::FloatOverflow => "float_overflow",
//            EvalError::IntOverflow => "int_overflow",
//            EvalError::Undefined => "undefined",
//            EvalError::Underflow => "underflow",
            EvalError::ZeroDivisor => "zero_divisor",
            EvalError::NoRoots => "no_roots"
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
    pub(super) fn check_sort_errors(&self) -> CallResult {
        let stub   = MachineError::functor_stub(clause_name!("sort"), 2);
        let list   = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::PartialList(..) =>
                return Err(self.error_form(MachineError::instantiation_error(), stub)),
            CycleSearchResult::NotList =>
                return Err(self.error_form(MachineError::type_error(ValidType::List, list), stub)),
            _ => {}
        };

        match self.detect_cycles(sorted.clone()) {
            CycleSearchResult::NotList if !sorted.is_ref() =>
                Err(self.error_form(MachineError::type_error(ValidType::List, sorted), stub)),
            _ => Ok(())
        }
    }

    fn check_for_list_pairs(&self, list: Addr) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::NotList if !list.is_ref() =>
                Err(self.error_form(MachineError::type_error(ValidType::List, list), stub)),
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
                            _ => return Err(self.error_form(MachineError::type_error(ValidType::Pair,
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
    pub(super) fn check_keysort_errors(&self) -> CallResult {
        let stub   = MachineError::functor_stub(clause_name!("keysort"), 2);
        let pairs  = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(pairs.clone()) {
            CycleSearchResult::PartialList(..) =>
                Err(self.error_form(MachineError::instantiation_error(), stub)),
            CycleSearchResult::NotList =>
                Err(self.error_form(MachineError::type_error(ValidType::List, pairs), stub)),
            _ => Ok(())
        }?;

        self.check_for_list_pairs(sorted)
    }

    pub(super) fn error_form(&self, err: MachineError, src: MachineStub) -> MachineStub {
        let h = self.heap.h;
        let mut stub = vec![HeapCellValue::NamedStr(2, clause_name!("error"), None),
                            HeapCellValue::Addr(Addr::HeapCell(h + 3)),
                            HeapCellValue::Addr(Addr::HeapCell(h + 3 + err.len()))];

        stub.extend(err.into_iter(3));
        stub.extend(src.into_iter());

        stub
    }

    pub(super) fn throw_exception(&mut self, err: MachineStub) {
        let h = self.heap.h;

        self.ball.boundary = 0;
        self.ball.stub.truncate(0);

        self.heap.append(err);

        self.registers[1] = Addr::HeapCell(h);

        self.set_ball();
        self.unwind_stack();
    }
}
