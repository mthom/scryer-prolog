use prolog_parser::ast::*;

use crate::prolog::forms::{ModuleSource, Number, PredicateKey};
use crate::prolog::machine::heap::*;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::machine::machine_state::*;
use crate::prolog::rug::Integer;

use std::rc::Rc;

pub(crate) type MachineStub = Vec<HeapCellValue>;

#[derive(Debug, Clone, Copy)]
enum ErrorProvenance {
    Constructed, // if constructed, offset the addresses.
    Received,    // otherwise, preserve the addresses.
}

#[derive(Debug)]
pub(crate) struct MachineError {
    stub: MachineStub,
    location: Option<(usize, usize)>, // line_num, col_num
    from: ErrorProvenance,
}

pub(crate)
trait TypeError {
    fn type_error(self, h: usize, valid_type: ValidType) -> MachineError;
}

impl TypeError for Addr {
    fn type_error(self, _: usize, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            "type_error",
            [atom(valid_type.as_str()), addr(self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received
        }
    }
}

impl TypeError for MachineStub {
    fn type_error(self, h: usize, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            "type_error",
            [atom(valid_type.as_str()), aux(h, 0)],
            [self]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed
        }
    }
}

impl TypeError for Number {
    fn type_error(self, _h: usize, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            "type_error",
            [atom(valid_type.as_str()), number(self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received
        }
    }
}

pub(crate)
trait PermissionError {
    fn permission_error(self, h: usize, index_str: &'static str, perm: Permission) -> MachineError;
}

impl PermissionError for Addr {
    fn permission_error(self, _: usize, index_str: &'static str, perm: Permission) -> MachineError {
        let stub = functor!(
            "permission_error",
            [atom(perm.as_str()), atom(index_str), addr(self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received
        }
    }
}

impl PermissionError for MachineStub {
    fn permission_error(self, h: usize, index_str: &'static str, perm: Permission) -> MachineError {
        let stub = functor!(
            "permission_error",
            [atom(perm.as_str()), atom(index_str), aux(h, 0)],
            [self]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed
        }
    }
}

pub(super)
trait DomainError {
    fn domain_error(self, error: DomainErrorType) -> MachineError;
}

impl DomainError for Addr {
    fn domain_error(self, error: DomainErrorType) -> MachineError {
        let stub = functor!(
            "domain_error",
            [atom(error.as_str()), addr(self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }
}

impl DomainError for Number {
    fn domain_error(self, error: DomainErrorType) -> MachineError {
        let stub = functor!(
            "domain_error",
            [atom(error.as_str()), number(self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }
}

impl MachineError {
    pub(super)
    fn functor_stub(name: ClauseName, arity: usize) -> MachineStub {
        functor!(
            "/",
            SharedOpDesc::new(400, YFX),
            [clause_name(name), integer(arity)]
        )
    }

    #[inline]
    pub(super)
    fn interrupt_error() -> Self {
        let stub = functor!("$interrupt_thrown");

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super)
    fn evaluation_error(eval_error: EvalError) -> Self {
        let stub = functor!("evaluation_error", [atom(eval_error.as_str())]);

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super)
    fn type_error<T: TypeError>(h: usize, valid_type: ValidType, culprit: T) -> Self {
        culprit.type_error(h, valid_type)
    }

    pub(super)
    fn module_resolution_error(
        h: usize,
        mod_name: ClauseName,
        name: ClauseName,
        arity: usize,
    ) -> Self {
        let res_stub = functor!(
            ":",
            SharedOpDesc::new(600, XFY),
            [clause_name(mod_name), clause_name(name)]
        );

        let ind_stub = functor!(
            "/",
            SharedOpDesc::new(400, YFX),
            [aux(h + 2, 0), integer(arity)],
            [res_stub]
        );

        let stub = functor!(
            "evaluation_error",
            [aux(h, 0)],
            [ind_stub]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }

    pub(super)
    fn existence_error(h: usize, err: ExistenceError) -> Self {
        match err {
            ExistenceError::Module(name) => {
                let stub = functor!(
                    "existence_error",
                    [atom("source_sink"), clause_name(name)]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Received,
                }
            }
            ExistenceError::Procedure(name, arity) => {
                let culprit = functor!(
                    "/",
                    SharedOpDesc::new(400, YFX),
                    [clause_name(name), integer(arity)]
                );

                let stub = functor!(
                    "existence_error",
                    [atom("procedure"), aux(h, 0)],
                    [culprit]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Constructed,
                }
            }
            ExistenceError::ModuleSource(source) => {
                let source_stub = source.as_functor_stub();

                let stub = functor!(
                    "existence_error",
                    [atom("source_sink"), aux(h, 0)],
                    [source_stub]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Constructed,
                }
            }
            ExistenceError::SourceSink(culprit) => {
                let stub = functor!(
                    "existence_error",
                    [atom("source_sink"), addr(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Received,
                }
            }
            ExistenceError::Stream(culprit) => {
                let stub = functor!(
                    "existence_error",
                    [atom("stream"), addr(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Received,
                }
            }
        }
    }

    pub(super)
    fn permission_error<T: PermissionError>(
        h: usize,
        err: Permission,
        index_str: &'static str,
        culprit: T,
    ) -> Self {
        culprit.permission_error(
            h,
            index_str,
            err,
        )
    }

    fn arithmetic_error(h: usize, err: ArithmeticError) -> Self {
        match err {
            ArithmeticError::UninstantiatedVar => {
                Self::instantiation_error()
            }
            ArithmeticError::NonEvaluableFunctor(name, arity) => {
                let culprit = functor!(
                    "/",
                    SharedOpDesc::new(400, YFX),
                    [constant(h, &name), integer(arity)]
                );

                Self::type_error(h, ValidType::Evaluable, culprit)
            }
        }
    }

    #[inline]
    pub(super)
    fn domain_error<T: DomainError>(error: DomainErrorType, culprit: T) -> Self {
        culprit.domain_error(error)
    }

    pub(super)
    fn instantiation_error() -> Self {
        let stub = functor!("instantiation_error");

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super)
    fn uninstantiation_error(culprit: Addr) -> Self {
        let stub = functor!(
            "uninstantiation_error",
            [addr(culprit)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super)
    fn session_error(h: usize, err: SessionError) -> Self {
        match err {
            SessionError::CannotOverwriteBuiltIn(pred_str) |
            SessionError::CannotOverwriteImport(pred_str) => {
                Self::permission_error(
                    h,
                    Permission::Modify,
                    "private_procedure",
                    functor!(clause_name(pred_str)),
                )
            }
            SessionError::ExistenceError(err) => {
                Self::existence_error(h, err)
            }
            SessionError::InvalidFileName(filename) => {
                Self::existence_error(h, ExistenceError::Module(filename))
            }
            SessionError::ModuleDoesNotContainExport(..) => {
                Self::permission_error(
                    h,
                    Permission::Access,
                    "private_procedure",
                    functor!("module_does_not_contain_claimed_export"),
                )
            }
            SessionError::NamelessEntry => {
                Self::permission_error(
                    h,
                    Permission::Create,
                    "static_procedure",
                    functor!("nameless_procedure")
                )
            }
            SessionError::OpIsInfixAndPostFix(op) => {
                Self::permission_error(
                    h,
                    Permission::Create,
                    "operator",
                    functor!(clause_name(op)),
                )
            }
            SessionError::ParserError(err) => {
                Self::syntax_error(h, err)
            }
            SessionError::QueryCannotBeDefinedAsFact => {
                Self::permission_error(
                    h,
                    Permission::Create,
                    "static_procedure",
                    functor!("query_cannot_be_defined_as_fact")
                )
            }
        }
    }

    pub(super)
    fn syntax_error(h: usize, err: ParserError) -> Self {
        if let ParserError::Arithmetic(err) = err {
            return Self::arithmetic_error(h, err);
        }

        let location = err.line_and_col_num();
        let stub = functor!(err.as_str());

        let stub = functor!(
            "syntax_error",
            [aux(h, 0)],
            [stub]
        );

        MachineError {
            stub,
            location,
            from: ErrorProvenance::Constructed,
        }
    }

    pub(super)
    fn representation_error(flag: RepFlag) -> Self {
        let stub = functor!("representation_error", [atom(flag.as_str())]);

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    fn into_iter(self, offset: usize) -> Box<dyn Iterator<Item = HeapCellValue>> {
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

#[derive(Debug, Clone, Copy)]
pub enum Permission {
    Access,
    Create,
    InputStream,
    Modify,
    Open,
    OutputStream,
    Reposition,
}

impl Permission {
    #[inline]
    pub fn as_str(self) -> &'static str {
        match self {
            Permission::Access => "access",
            Permission::Create => "create",
            Permission::InputStream => "input",
            Permission::Modify => "modify",
            Permission::Open => "open",
            Permission::OutputStream => "output",
            Permission::Reposition => "reposition",
        }
    }
}

// from 7.12.2 b) of 13211-1:1995
#[derive(Debug, Clone, Copy)]
pub enum ValidType {
    Atom,
    Atomic,
    //    Boolean,
    Byte,
    Callable,
    Character,
    Compound,
    Evaluable,
    Float,
    InByte,
    InCharacter,
    Integer,
    List,
    //    Number,
    Pair,
    //    PredicateIndicator,
    //    Variable
    TcpListener,
}

impl ValidType {
    pub fn as_str(self) -> &'static str {
        match self {
            ValidType::Atom => "atom",
            ValidType::Atomic => "atomic",
            //            ValidType::Boolean => "boolean",
            ValidType::Byte => "byte",
            ValidType::Callable => "callable",
            ValidType::Character => "character",
            ValidType::Compound => "compound",
            ValidType::Evaluable => "evaluable",
            ValidType::Float => "float",
            ValidType::InByte => "in_byte",
            ValidType::InCharacter => "in_character",
            ValidType::Integer => "integer",
            ValidType::List => "list",
            //            ValidType::Number => "number",
            ValidType::Pair => "pair",
            //            ValidType::PredicateIndicator => "predicate_indicator",
            //            ValidType::Variable => "variable"
            ValidType::TcpListener => "tcp_listener",
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DomainErrorType {
    IOMode,
    NotLessThanZero,
    Order,
    SourceSink,
    Stream,
    StreamOrAlias,
}

impl DomainErrorType {
    pub fn as_str(self) -> &'static str {
        match self {
            DomainErrorType::IOMode => "io_mode",
            DomainErrorType::NotLessThanZero => "not_less_than_zero",
            DomainErrorType::Order => "order",
            DomainErrorType::SourceSink => "source_sink",
            DomainErrorType::Stream => "stream",
            DomainErrorType::StreamOrAlias => "stream_or_alias",
        }
    }
}

// from 7.12.2 f) of 13211-1:1995
#[derive(Debug, Clone, Copy)]
pub enum RepFlag {
    //    Character,
    CharacterCode,
    InCharacterCode,
    MaxArity,
    //    MaxInteger,
    //    MinInteger
}

impl RepFlag {
    pub fn as_str(self) -> &'static str {
        match self {
            //            RepFlag::Character => "character",
            RepFlag::CharacterCode => "character_code",
            RepFlag::InCharacterCode => "in_character_code",
            RepFlag::MaxArity => "max_arity",
            //            RepFlag::MaxInteger => "max_integer",
            //            RepFlag::MinInteger => "min_integer"
        }
    }
}

// from 7.12.2 g) of 13211-1:1995
#[derive(Debug, Clone, Copy)]
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
#[derive(Debug, Clone, Copy)]
pub(super) enum CycleSearchResult {
    EmptyList,
    NotList,
    PartialList(usize, Ref),           // the list length (up to max), and an offset into the heap.
    ProperList(usize),                 // the list length.
    PStrLocation(usize, usize, usize), // the list length (up to max), the heap offset, byte offset into the string.
    UntouchedList(usize),              // the address of an uniterated Addr::Lis(address).
}

impl MachineState {
    // see 8.4.3 of Draft Technical Corrigendum 2.
    pub(super)
    fn check_sort_errors(&self) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("sort"), 2);
        let list = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::PartialList(..) => {
                return Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            CycleSearchResult::NotList => {
                return Err(self.error_form(MachineError::type_error(0, ValidType::List, list), stub))
            }
            _ => {}
        };

        match self.detect_cycles(sorted.clone()) {
            CycleSearchResult::NotList if !sorted.is_ref() => {
                Err(self.error_form(MachineError::type_error(0, ValidType::List, sorted), stub))
            }
            _ => Ok(()),
        }
    }

    fn check_for_list_pairs(&self, list: Addr) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        match self.detect_cycles(list.clone()) {
            CycleSearchResult::NotList if !list.is_ref() => {
                Err(self.error_form(MachineError::type_error(0, ValidType::List, list), stub))
            }
            _ => {
                let mut addr = list;

                while let Addr::Lis(l) = self.store(self.deref(addr)) {
                    let mut new_l = l;

                    loop {
                        match self.heap.clone(new_l) {
                            HeapCellValue::Addr(Addr::Str(l)) => {
                                new_l = l;
                            }
                            HeapCellValue::NamedStr(2, ref name, Some(_))
                                if name.as_str() == "-" => {
                                break;
                            }
                            HeapCellValue::Addr(Addr::HeapCell(_)) => {
                                break;
                            }
                            HeapCellValue::Addr(Addr::StackCell(..)) => {
                                break;
                            }
                            _ => {
                                return Err(self.error_form(
                                    MachineError::type_error(0, ValidType::Pair, Addr::HeapCell(l)),
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
    pub(super)
    fn check_keysort_errors(&self) -> CallResult {
        let stub = MachineError::functor_stub(clause_name!("keysort"), 2);

        let pairs  = self.store(self.deref(self[temp_v!(1)].clone()));
        let sorted = self.store(self.deref(self[temp_v!(2)].clone()));

        match self.detect_cycles(pairs.clone()) {
            CycleSearchResult::PartialList(..) => {
                Err(self.error_form(MachineError::instantiation_error(), stub))
            }
            CycleSearchResult::NotList => {
                Err(self.error_form(MachineError::type_error(0, ValidType::List, pairs), stub))
            }
            _ => Ok(()),
        }?;

        self.check_for_list_pairs(sorted)
    }

    #[inline]
    pub(crate)
    fn type_error<T: TypeError>(
        &self,
        valid_type: ValidType,
        culprit: T,
        caller: ClauseName,
        arity: usize,
    ) -> MachineStub {
        let stub = MachineError::functor_stub(caller, arity);
        let err = MachineError::type_error(
            self.heap.h(),
            valid_type,
            culprit,
        );

        return self.error_form(err, stub);
    }

    #[inline]
    pub(crate)
    fn representation_error(
        &self,
        rep_flag: RepFlag,
        caller: ClauseName,
        arity: usize,
    ) -> MachineStub {
        let stub = MachineError::functor_stub(caller, arity);
        let err = MachineError::representation_error(
            rep_flag,
        );

        return self.error_form(err, stub);
    }

    pub(super)
    fn error_form(&self, err: MachineError, src: MachineStub) -> MachineStub {
        let location = err.location;
        let err_len = err.len();

        let h = self.heap.h();
        let mut stub = vec![
            HeapCellValue::NamedStr(2, clause_name!("error"), None),
            HeapCellValue::Addr(Addr::HeapCell(h + 3)),
            HeapCellValue::Addr(Addr::HeapCell(h + 3 + err_len)),
        ];

        stub.extend(err.into_iter(3));

        if let Some((line_num, _)) = location {
            let colon_op_desc = Some(SharedOpDesc::new(600, XFY));

            stub.push(HeapCellValue::NamedStr(2, clause_name!(":"), colon_op_desc));
            stub.push(HeapCellValue::Addr(Addr::HeapCell(h + 6 + err_len)));
            stub.push(HeapCellValue::Integer(Rc::new(Integer::from(line_num))));
        }

        stub.extend(src.into_iter());
        stub
    }

    pub(super)
    fn throw_exception(&mut self, err: MachineStub) {
        let h = self.heap.h();

        self.ball.boundary = 0;
        self.ball.stub.truncate(0);

        self.heap.append(err);

        self.registers[1] = Addr::HeapCell(h);

        self.set_ball();
        self.unwind_stack();
    }
}

#[derive(Debug)]
pub enum ExistenceError {
    Module(ClauseName),
    ModuleSource(ModuleSource),
    Procedure(ClauseName, usize),
    SourceSink(Addr),
    Stream(Addr),
}

#[derive(Debug)]
pub enum SessionError {
    CannotOverwriteBuiltIn(ClauseName),
    CannotOverwriteImport(ClauseName),
    ExistenceError(ExistenceError),
    InvalidFileName(ClauseName),
    ModuleDoesNotContainExport(ClauseName, PredicateKey),
    NamelessEntry,
    OpIsInfixAndPostFix(ClauseName),
    QueryCannotBeDefinedAsFact,
    ParserError(ParserError),
}

#[derive(Debug)]
pub enum EvalSession {
    EntrySuccess,
    Error(SessionError),
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
