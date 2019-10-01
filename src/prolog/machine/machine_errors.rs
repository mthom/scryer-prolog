use prolog_parser::ast::*;
use prolog_parser::string_list::*;

use prolog::machine::machine_indices::*;
use prolog::machine::machine_state::*;
use prolog::rug::Integer;

pub(crate) type MachineStub = Vec<HeapCellValue>;

#[derive(Clone, Copy)]
enum ErrorProvenance {
    Constructed, // if constructed, offset the addresses.
    Received,    // otherwise, preserve the addresses.
}

pub(super) struct MachineError {
    stub: MachineStub,
    location: Option<(usize, usize)>, // line_num, col_num
    from: ErrorProvenance,
}

impl MachineError {
    pub(super) fn functor_stub(name: ClauseName, arity: usize) -> MachineStub {
        let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name, None)));
        functor!(
            "/",
            2,
            [name, heap_integer!(Integer::from(arity))],
            SharedOpDesc::new(400, YFX)
        )
    }

    pub(super) fn evaluation_error(eval_error: EvalError) -> Self {
        let stub = functor!("evaluation_error", 1, [heap_atom!(eval_error.as_str())]);
        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn type_error(valid_type: ValidType, culprit: Addr) -> Self {
        let stub = functor!(
            "type_error",
            2,
            [
                heap_atom!(valid_type.as_str()),
                HeapCellValue::Addr(culprit)
            ]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn module_resolution_error(
        h: usize,
        mod_name: ClauseName,
        name: ClauseName,
        arity: usize,
    ) -> Self {
        let mod_name = HeapCellValue::Addr(Addr::Con(Constant::Atom(mod_name, None)));
        let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name, None)));

        let mut stub = functor!(
            "evaluation_error",
            1,
            [HeapCellValue::Addr(Addr::HeapCell(h + 2))]
        );

        stub.append(&mut functor!(
            "/",
            2,
            [
                HeapCellValue::Addr(Addr::HeapCell(h + 2 + 3)),
                heap_integer!(Integer::from(arity))
            ],
            SharedOpDesc::new(400, YFX)
        ));
        stub.append(&mut functor!(
            ":",
            2,
            [mod_name, name],
            SharedOpDesc::new(600, XFY)
        ));

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }

    pub(super) fn existence_error(h: usize, err: ExistenceError) -> Self {
        match err {
            ExistenceError::Procedure(name, arity) => {
                let mut stub = functor!(
                    "existence_error",
                    2,
                    [heap_atom!("procedure"), heap_str!(3 + h)]
                );
                stub.append(&mut Self::functor_stub(name, arity));

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Constructed,
                }
            }
            ExistenceError::Module(name) => {
                let name = HeapCellValue::Addr(Addr::Con(Constant::Atom(name, None)));
                let stub = functor!("existence_error", 2, [heap_atom!("module"), name]);

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Constructed,
                }
            }
        }
    }

    pub(super) fn session_error(h: usize, err: SessionError) -> Self {
        match err {
            SessionError::ParserError(err) => Self::syntax_error(h, err),
            SessionError::CannotOverwriteBuiltIn(pred_str)
          | SessionError::CannotOverwriteImport(pred_str) => {
                Self::permission_error(PermissionError::Modify, "private_procedure", pred_str)
            }
            SessionError::InvalidFileName(filename) => {
                Self::existence_error(h, ExistenceError::Module(filename))
            }
            SessionError::ModuleDoesNotContainExport => Self::permission_error(
                PermissionError::Access,
                "private_procedure",
                clause_name!("module_does_not_contain_claimed_export"),
            ),
            SessionError::ModuleNotFound => Self::permission_error(
                PermissionError::Access,
                "private_procedure",
                clause_name!("module_does_not_exist"),
            ),
            SessionError::NoModuleDeclaration(name) => {
                Self::existence_error(h, ExistenceError::Module(name))
            }
            SessionError::OpIsInfixAndPostFix(op) => {
                Self::permission_error(PermissionError::Create, "operator", op)
            }
            _ => unreachable!(),
        }
    }

    pub(super) fn permission_error(
        err: PermissionError,
        index_str: &'static str,
        pred_str: ClauseName,
    ) -> Self {
        let pred_str = HeapCellValue::Addr(Addr::Con(Constant::Atom(pred_str, None)));

        let err = vec![heap_atom!(err.as_str()), heap_atom!(index_str), pred_str];
        let mut stub = functor!("permission_error", 3);

        stub.extend(err.into_iter());

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }

    fn arithmetic_error(h: usize, err: ArithmeticError) -> Self {
        match err {
            ArithmeticError::UninstantiatedVar => Self::instantiation_error(),
            ArithmeticError::NonEvaluableFunctor(name, arity) => {
                let name = HeapCellValue::Addr(Addr::Con(name));
                let culprit = functor!(
                    "/",
                    2,
                    [name, heap_integer!(Integer::from(arity))],
                    SharedOpDesc::new(400, YFX)
                );

                let mut stub = Self::type_error(ValidType::Evaluable, Addr::HeapCell(3 + h)).stub;
                stub.extend(culprit.into_iter());

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Constructed,
                }
            }
        }
    }

    pub(super) fn syntax_error(h: usize, err: ParserError) -> Self {
        if let ParserError::Arithmetic(err) = err {
            return Self::arithmetic_error(h, err);
        }

        let location = err.line_and_col_num();
        let err = vec![heap_atom!(err.as_str())];

        let mut stub = if err.len() == 1 {
            functor!("syntax_error", 1)
        } else {
            functor!("syntax_error", 1, [heap_str!(h + 2)])
        };

        stub.extend(err.into_iter());

        MachineError {
            stub,
            location,
            from: ErrorProvenance::Constructed,
        }
    }

    pub(super) fn domain_error(error: DomainError, culprit: Addr) -> Self {
        let stub = functor!(
            "domain_error",
            2,
            [heap_atom!(error.as_str()), HeapCellValue::Addr(culprit)]
        );
        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn instantiation_error() -> Self {
        let stub = functor!("instantiation_error");
        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn representation_error(flag: RepFlag) -> Self {
        let stub = functor!("representation_error", 1, [heap_atom!(flag.as_str())]);
        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    fn into_iter(self, offset: usize) -> Box<Iterator<Item = HeapCellValue>> {
        match self.from {
            ErrorProvenance::Constructed => {
                Box::new(self.stub.into_iter().map(move |hcv| match hcv {
                    HeapCellValue::Addr(addr) => HeapCellValue::Addr(addr + offset),
                    hcv => hcv,
                }))
            }
            ErrorProvenance::Received => Box::new(self.stub.into_iter()),
        }
    }

    fn len(&self) -> usize {
        self.stub.len()
    }
}

#[derive(Clone, Copy)]
pub enum PermissionError {
    Access,
    Create,
    Modify,
}

impl PermissionError {
    pub fn as_str(self) -> &'static str {
        match self {
            PermissionError::Access => "access",
            PermissionError::Create => "create",
            PermissionError::Modify => "modify",
        }
    }
}

// from 7.12.2 b) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum ValidType {
    Atom,
    Atomic,
    //    Boolean,
    //    Byte,
    Callable,
    Character,
    Compound,
    Evaluable,
    Float,
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
            //            ValidType::Boolean => "boolean",
            //            ValidType::Byte => "byte",
            ValidType::Callable => "callable",
            ValidType::Character => "character",
            ValidType::Compound => "compound",
            ValidType::Evaluable => "evaluable",
            ValidType::Float => "float",
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
    NotLessThanZero,
}

impl DomainError {
    pub fn as_str(self) -> &'static str {
        match self {
            DomainError::NotLessThanZero => "not_less_than_zero",
        }
    }
}

// from 7.12.2 f) of 13211-1:1995
#[derive(Clone, Copy)]
pub enum RepFlag {
    Character,
    CharacterCode,
    //    InCharacterCode,
    MaxArity,
    //    MaxInteger,
    //    MinInteger
}

impl RepFlag {
    pub fn as_str(self) -> &'static str {
        match self {
            RepFlag::Character => "character",
            RepFlag::CharacterCode => "character_code",
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
    FloatOverflow,
    Undefined,
    //    Underflow,
    ZeroDivisor,
}

impl EvalError {
    pub fn as_str(self) -> &'static str {
        match self {
            EvalError::FloatOverflow => "float_overflow",
            EvalError::Undefined => "undefined",
            //            EvalError::FloatUnderflow => "underflow",
            EvalError::ZeroDivisor => "zero_divisor",
        }
    }
}

// used by '$skip_max_list'.
pub(super) enum CycleSearchResult {
    EmptyList,
    NotList,
    PartialList(usize, usize), // the list length (up to max), and an offset into the heap.
    ProperList(usize),         // the list length.
    String(usize, StringList), // the number of elements iterated, the string tail.
    UntouchedList(usize),      // the address of an uniterated Addr::Lis(address).
}

impl MachineState {
    // see 8.4.3 of Draft Technical Corrigendum 2.
    pub(super) fn check_sort_errors(&self) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("sort"), 2);
        let list = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::PartialList(..) => {
                return Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            CycleSearchResult::NotList => {
                return Err(self.error_form(MachineError::type_error(ValidType::List, list), stub))
            }
            _ => {}
        };

        match self.detect_cycles(sorted.clone()) {
            CycleSearchResult::NotList if !sorted.is_ref() => {
                Err(self.error_form(MachineError::type_error(ValidType::List, sorted), stub))
            }
            _ => Ok(()),
        }
    }

    fn check_for_list_pairs(&self, list: Addr) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::NotList if !list.is_ref() => {
                Err(self.error_form(MachineError::type_error(ValidType::List, list), stub))
            }
            _ => {
                let mut addr = list;

                while let Addr::Lis(l) = self.store(self.deref(addr)) {
                    let mut new_l = l;

                    loop {
                        match self.heap[new_l].clone() {
                            HeapCellValue::Addr(Addr::Str(l)) => new_l = l,
                            HeapCellValue::NamedStr(2, ref name, Some(_))
                                if name.as_str() == "-" =>
                            {
                                break
                            }
                            HeapCellValue::Addr(Addr::HeapCell(_)) => break,
                            HeapCellValue::Addr(Addr::StackCell(..)) => break,
                            _ => {
                                return Err(self.error_form(
                                    MachineError::type_error(ValidType::Pair, Addr::HeapCell(l)),
                                    stub,
                                ))
                            }
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
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);
        let pairs = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(pairs.clone()) {
            CycleSearchResult::PartialList(..) => {
                Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            CycleSearchResult::NotList => {
                Err(self.error_form(MachineError::type_error(ValidType::List, pairs), stub))
            }
            _ => Ok(()),
        }?;

        self.check_for_list_pairs(sorted)
    }

    pub(super) fn error_form(&self, err: MachineError, src: MachineStub) -> MachineStub {
        let location = err.location;
        let err_len = err.len();

        let h = self.heap.h;
        let mut stub = vec![
            HeapCellValue::NamedStr(2, clause_name!("error"), None),
            HeapCellValue::Addr(Addr::HeapCell(h + 3)),
            HeapCellValue::Addr(Addr::HeapCell(h + 3 + err_len)),
        ];

        stub.extend(err.into_iter(3));

        if let Some((line_num, _)) = location {
            let colon_op_desc = Some(SharedOpDesc::new(600, XFY));

            stub.extend(
                vec![
                    HeapCellValue::NamedStr(2, clause_name!(":"), colon_op_desc),
                    HeapCellValue::Addr(Addr::HeapCell(h + 6 + err_len)),
                    heap_integer!(Integer::from(line_num)),
                ]
                .into_iter(),
            );
        }

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

pub enum ExistenceError {
    Module(ClauseName),
    Procedure(ClauseName, usize),
}

pub enum SessionError {
    CannotOverwriteBuiltIn(ClauseName),
    CannotOverwriteImport(ClauseName),
    InvalidFileName(ClauseName),
    ModuleDoesNotContainExport,
    ModuleNotFound,
    NamelessEntry,
    NoModuleDeclaration(ClauseName),
    OpIsInfixAndPostFix(ClauseName),
    ParserError(ParserError),
    UserPrompt,
}

pub enum EvalSession {
    EntrySuccess,
    Error(SessionError),
    InitialQuerySuccess(AllocVarDict),
    QueryFailure,
    SubsequentQuerySuccess,
}

impl From<SessionError> for EvalSession {
    fn from(err: SessionError) -> Self {
        EvalSession::Error(err)
    }
}

impl From<ParserError> for SessionError {
    fn from(err: ParserError) -> Self {
        SessionError::ParserError(err)
    }
}

impl From<ParserError> for EvalSession {
    fn from(err: ParserError) -> Self {
        EvalSession::from(SessionError::ParserError(err))
    }
}
