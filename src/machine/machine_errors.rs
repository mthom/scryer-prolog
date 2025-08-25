use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;

#[cfg(feature = "ffi")]
use crate::ffi::{self, FfiError};
use crate::forms::*;
use crate::functor_macro::*;
use crate::machine::heap::*;
use crate::machine::loader::CompilationTarget;
use crate::machine::machine_state::*;
use crate::machine::streams::*;
use crate::machine::system_calls::BrentAlgState;
use crate::types::*;

pub type MachineStub = Vec<FunctorElement>;
pub type MachineStubGen = Box<dyn Fn(&mut MachineState) -> MachineStub>;

#[derive(Debug)]
pub(crate) struct MachineError {
    stub: MachineStub,
    location: Option<(usize, usize)>, // line_num, col_num
}

// from 7.12.2 b) of 13211-1:1995
#[derive(Debug, Clone, Copy)]
pub(crate) enum ValidType {
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
    #[allow(unused)]
    Number,
    Pair,
    //    PredicateIndicator,
    //    Variable
    TcpListener,
    Process,
}

impl ValidType {
    pub(crate) fn as_atom(self) -> Atom {
        match self {
            ValidType::Atom => atom!("atom"),
            ValidType::Atomic => atom!("atomic"),
            //            ValidType::Boolean => atom!("boolean"),
            ValidType::Byte => atom!("byte"),
            ValidType::Callable => atom!("callable"),
            ValidType::Character => atom!("character"),
            ValidType::Compound => atom!("compound"),
            ValidType::Evaluable => atom!("evaluable"),
            ValidType::Float => atom!("float"),
            ValidType::InByte => atom!("in_byte"),
            ValidType::InCharacter => atom!("in_character"),
            ValidType::Integer => atom!("integer"),
            ValidType::List => atom!("list"),
            ValidType::Number => atom!("number"),
            ValidType::Pair => atom!("pair"),
            //            ValidType::PredicateIndicator => atom!("predicate_indicator"),
            //            ValidType::Variable => atom!("variable")
            ValidType::TcpListener => atom!("tcp_listener"),
            ValidType::Process => atom!("process"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ResourceError {
    FiniteMemory(HeapCellValue),
    OutOfFiles,
}

pub(crate) trait TypeError {
    fn type_error(self, machine_st: &mut MachineState, valid_type: ValidType) -> MachineError;
}

impl TypeError for HeapCellValue {
    fn type_error(self, _machine_st: &mut MachineState, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            atom!("type_error"),
            [atom_as_cell((valid_type.as_atom())), cell(self)]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

impl TypeError for MachineStub {
    fn type_error(self, _machine_st: &mut MachineState, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            atom!("type_error"),
            [atom_as_cell((valid_type.as_atom())), functor(self)]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

impl TypeError for Number {
    fn type_error(self, machine_st: &mut MachineState, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            atom!("type_error"),
            [
                atom_as_cell((valid_type.as_atom())),
                number(self, (&mut machine_st.arena))
            ]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

pub(crate) trait PermissionError {
    fn permission_error(
        self,
        machine_st: &mut MachineState,
        index_atom: Atom,
        perm: Permission,
    ) -> MachineError;
}

impl PermissionError for Atom {
    fn permission_error(
        self,
        _machine_st: &mut MachineState,
        index_atom: Atom,
        perm: Permission,
    ) -> MachineError {
        let stub = functor!(
            atom!("permission_error"),
            [
                atom_as_cell((perm.as_atom())),
                atom_as_cell(index_atom),
                atom_as_cell(self)
            ]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

impl PermissionError for HeapCellValue {
    fn permission_error(
        self,
        _machine_st: &mut MachineState,
        index_atom: Atom,
        perm: Permission,
    ) -> MachineError {
        let cell = read_heap_cell!(self,
            (HeapCellValueTag::Cons, ptr) => {
                match_untyped_arena_ptr!(ptr,
                    (ArenaHeaderTag::Stream, stream) => {
                        if let Some(alias) = stream.options().get_alias() {
                            atom_as_cell!(alias)
                        } else {
                            self
                        }
                    }
                    _ => {
                        self
                    }
                )
            }
            _ => {
                self
            }
        );

        let stub = functor!(
            atom!("permission_error"),
            [
                atom_as_cell((perm.as_atom())),
                atom_as_cell(index_atom),
                cell(cell)
            ]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

impl PermissionError for MachineStub {
    fn permission_error(
        self,
        _machine_st: &mut MachineState,
        index_atom: Atom,
        perm: Permission,
    ) -> MachineError {
        let stub = functor!(
            atom!("permission_error"),
            [
                atom_as_cell((perm.as_atom())),
                atom_as_cell(index_atom),
                functor(self)
            ]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

pub(super) trait DomainError {
    fn domain_error(self, machine_st: &mut MachineState, error: DomainErrorType) -> MachineError;
}

impl DomainError for HeapCellValue {
    fn domain_error(self, _machine_st: &mut MachineState, error: DomainErrorType) -> MachineError {
        let stub = functor!(
            atom!("domain_error"),
            [atom_as_cell((error.as_atom())), cell(self)]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

impl DomainError for Number {
    fn domain_error(self, machine_st: &mut MachineState, error: DomainErrorType) -> MachineError {
        let stub = functor!(
            atom!("domain_error"),
            [
                atom_as_cell((error.as_atom())),
                number(self, (&mut machine_st.arena))
            ]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

impl DomainError for MachineStub {
    fn domain_error(self, _machine_st: &mut MachineState, error: DomainErrorType) -> MachineError {
        let stub = functor!(
            atom!("domain_error"),
            [atom_as_cell((error.as_atom())), functor(self)]
        );

        MachineError {
            stub,
            location: None,
        }
    }
}

#[cfg(feature = "ffi")]
impl DomainError for ffi::Value {
    fn domain_error(self, machine_st: &mut MachineState, error: DomainErrorType) -> MachineError {
        use ffi::Value;

        match self {
            Value::Number(number) => number.domain_error(machine_st, error),
            Value::CString(cstring) => {
                let str = cstring.to_string_lossy().into_owned();
                let stub = functor!(
                    atom!("domain_error"),
                    [atom_as_cell((error.as_atom())), string(str)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            Value::Struct(atom, _values) => atom_as_cell!(atom).domain_error(machine_st, error),
        }
    }
}

#[inline(always)]
pub(super) fn functor_stub(name: Atom, arity: usize) -> MachineStub {
    functor!(atom!("/"), [atom_as_cell(name), fixnum(arity)])
}

impl MachineState {
    #[inline]
    pub(super) fn interrupt_error(&mut self) -> MachineError {
        let stub = functor!(atom!("$interrupt_thrown"));

        MachineError {
            stub,
            location: None,
        }
    }

    pub(super) fn evaluation_error(&mut self, eval_error: EvalError) -> MachineError {
        let stub = functor!(
            atom!("evaluation_error"),
            [atom_as_cell((eval_error.as_atom()))]
        );

        MachineError {
            stub,
            location: None,
        }
    }

    pub(super) fn resource_error(err: ResourceError) -> MachineError {
        let stub = match err {
            ResourceError::FiniteMemory(size_requested) => {
                functor!(
                    atom!("resource_error"),
                    [atom_as_cell((atom!("finite_memory"))), cell(size_requested)]
                )
            }
            ResourceError::OutOfFiles => {
                functor!(
                    atom!("resource_error"),
                    [atom_as_cell((atom!("file_descriptors")))]
                )
            }
        };

        MachineError {
            stub,
            location: None,
        }
    }

    pub(super) fn type_error<T: TypeError>(
        &mut self,
        valid_type: ValidType,
        culprit: T,
    ) -> MachineError {
        culprit.type_error(self, valid_type)
    }

    pub(super) fn existence_error(&mut self, err: ExistenceError) -> MachineError {
        match err {
            ExistenceError::Module(name) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("source_sink"))), atom_as_cell(name)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::QualifiedProcedure {
                module_name,
                name,
                arity,
            } => {
                let ind_stub = functor!(atom!("/"), [atom_as_cell(name), fixnum(arity)]);
                let res_stub = functor!(atom!(":"), [atom_as_cell(module_name), functor(ind_stub)]);

                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("procedure"))), functor(res_stub)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::Procedure(name, arity) => {
                let culprit = functor!(atom!("/"), [atom_as_cell(name), fixnum(arity)]);

                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("procedure"))), functor(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::ModuleSource(source) => {
                let source_stub = source.as_functor_stub();

                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("source_sink"))), functor(source_stub)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::SourceSink(culprit) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("source_sink"))), cell(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::Stream(culprit) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("stream"))), cell(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::Process(culprit) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("process"))), cell(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::FfiFunction(atom) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("ffi_function"))), atom_as_cell(atom)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            ExistenceError::FfiStructType(atom) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom_as_cell((atom!("ffi_struct_type"))), atom_as_cell(atom)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
        }
    }

    pub(crate) fn directive_error(&mut self, err: DirectiveError) -> MachineError {
        match err {
            DirectiveError::ExpectedDirective(_term) => self.domain_error(
                DomainErrorType::Directive,
                atom_as_cell!(atom!("todo_insert_invalid_term_here")),
            ),
            DirectiveError::InvalidDirective(name, arity) => {
                self.domain_error(DomainErrorType::Directive, functor_stub(name, arity))
            }
            DirectiveError::InvalidOpDeclNameType(_term) => self.type_error(
                ValidType::List,
                atom_as_cell!(atom!("todo_insert_invalid_term_here")),
            ),
            DirectiveError::InvalidOpDeclSpecDomain(_term) => self.domain_error(
                DomainErrorType::OperatorSpecifier,
                atom_as_cell!(atom!("todo_insert_invalid_term_here")),
            ),
            DirectiveError::InvalidOpDeclSpecValue(atom) => {
                self.domain_error(DomainErrorType::OperatorSpecifier, atom_as_cell!(atom))
            }
            DirectiveError::InvalidOpDeclPrecType(_term) => self.type_error(
                ValidType::Integer,
                atom_as_cell!(atom!("todo_insert_invalid_term_here")),
            ),
            DirectiveError::InvalidOpDeclPrecDomain(num) => {
                self.domain_error(DomainErrorType::OperatorPriority, fixnum_as_cell!(num))
            }
            DirectiveError::ShallNotCreate(atom) => {
                self.permission_error(Permission::Create, atom!("operator"), atom)
            }
            DirectiveError::ShallNotModify(atom) => {
                self.permission_error(Permission::Modify, atom!("operator"), atom)
            }
        }
    }

    pub(super) fn permission_error<T: PermissionError>(
        &mut self,
        err: Permission,
        index_atom: Atom,
        culprit: T,
    ) -> MachineError {
        culprit.permission_error(self, index_atom, err)
    }

    pub(super) fn evaluable_error(&mut self, name: Atom, arity: usize) -> MachineError {
        let evaluable_stub = functor_stub(name, arity);
        evaluable_stub.type_error(self, ValidType::Evaluable)
    }

    fn arithmetic_error(&mut self, err: ArithmeticError) -> MachineError {
        match err {
            ArithmeticError::NonEvaluableFunctor(cell, arity) => {
                let culprit = functor!(atom!("/"), [literal(cell), fixnum(arity)]);
                self.type_error(ValidType::Evaluable, culprit)
            }
            ArithmeticError::UninstantiatedVar => self.instantiation_error(),
        }
    }

    #[inline]
    pub(super) fn domain_error<T: DomainError>(
        &mut self,
        error: DomainErrorType,
        culprit: T,
    ) -> MachineError {
        culprit.domain_error(self, error)
    }

    pub(super) fn instantiation_error(&mut self) -> MachineError {
        let stub = functor!(atom!("instantiation_error"));

        MachineError {
            stub,
            location: None,
        }
    }

    pub(super) fn session_error(&mut self, err: SessionError) -> MachineError {
        match err {
            SessionError::CannotOverwriteBuiltIn(key) => self.permission_error(
                Permission::Modify,
                atom!("static_procedure"),
                functor_stub(key.0, key.1),
            ),
            SessionError::CannotOverwriteStaticProcedure(key) => self.permission_error(
                Permission::Modify,
                atom!("static_procedure"),
                functor_stub(key.0, key.1),
            ),
            SessionError::CannotOverwriteBuiltInModule(module) => {
                self.permission_error(Permission::Modify, atom!("static_module"), module)
            }
            SessionError::ExistenceError(err) => self.existence_error(err),
            SessionError::ModuleDoesNotContainExport(module_name, key) => {
                let functor_stub = functor_stub(key.0, key.1);

                let stub = functor!(
                    atom!("module_does_not_contain_claimed_export"),
                    [atom_as_cell(module_name), functor(functor_stub)]
                );

                self.permission_error(Permission::Access, atom!("private_procedure"), stub)
            }
            SessionError::ModuleCannotImportSelf(module_name) => {
                let error_atom = atom!("module_cannot_import_self");

                self.permission_error(
                    Permission::Modify,
                    atom!("module"),
                    functor!(error_atom, [atom_as_cell(module_name)]),
                )
            }
            SessionError::NamelessEntry => {
                let error_atom = atom!("nameless_procedure");
                self.permission_error(
                    Permission::Create,
                    atom!("static_procedure"),
                    functor!(error_atom),
                )
            }
            SessionError::OpIsInfixAndPostFix(op) => {
                self.permission_error(Permission::Create, atom!("operator"), functor!(op))
            }
            SessionError::CompilationError(CompilationError::ExceededMaxArity) => {
                self.representation_error(RepFlag::MaxArity)
            }
            SessionError::CompilationError(err) => self.syntax_error(err),
            SessionError::PredicateNotMultifileOrDiscontiguous(compilation_target, key) => {
                let stub = functor!(
                    atom!(":"),
                    [
                        atom_as_cell((compilation_target.module_name())),
                        functor((key.0), [fixnum((key.1))])
                    ]
                );

                self.permission_error(
                    Permission::Modify,
                    atom!("not_declared_multifile_or_discontiguous"),
                    stub,
                )
            }
        }
    }

    pub(super) fn syntax_error<E: Into<CompilationError>>(&mut self, err: E) -> MachineError {
        let err = err.into();

        if let CompilationError::Arithmetic(err) = err {
            return self.arithmetic_error(err);
        }

        if let CompilationError::InvalidDirective(err) = err {
            return self.directive_error(err);
        }

        let location = err.line_and_col_num();
        let stub = err.as_functor();

        let stub = functor!(atom!("syntax_error"), [functor(stub)]);

        MachineError { stub, location }
    }

    pub(super) fn representation_error(&self, flag: RepFlag) -> MachineError {
        let stub = functor!(
            atom!("representation_error"),
            [atom_as_cell((flag.as_atom()))]
        );

        MachineError {
            stub,
            location: None,
        }
    }

    #[allow(dead_code)] // not used when all features are enabled
    pub(super) fn missing_feature_error(&self, feature: Atom) -> MachineError {
        let stub = functor!(
            atom!("representation_error"),
            [functor(
                (functor!(atom!("feature"), [atom_as_cell((feature))]))
            )]
        );

        MachineError {
            stub,
            location: None,
        }
    }

    pub(super) fn unreachable_error(&self) -> MachineError {
        let stub = functor!(atom!("system_error"));

        MachineError {
            stub,
            location: None,
        }
    }

    #[cfg(feature = "ffi")]
    pub(super) fn ffi_error(&mut self, err: FfiError) -> MachineError {
        match err {
            FfiError::ValueCast(expected, actual) => {
                let stub = functor!(
                    atom!("domain_error"),
                    [atom_as_cell(expected), atom_as_cell(actual)]
                );

                MachineError {
                    stub,
                    location: None,
                }
            }
            FfiError::ValueOutOfRange(domain, culprit) => self.domain_error(domain, culprit),
            FfiError::FunctionNotFound(name) => {
                self.existence_error(ExistenceError::FfiFunction(name))
            }
            FfiError::StructNotFound(name) => {
                self.existence_error(ExistenceError::FfiStructType(name))
            }
            FfiError::ArgCountMismatch => self.unreachable_error(),
            FfiError::AllocationFailed => MachineError {
                stub: functor!(atom!("resource_error"), [atom_as_cell((atom!("heap")))]),
                location: None,
            },
            FfiError::LayoutError => self.representation_error(RepFlag::FfiLayout),
            FfiError::UnsupportedTypedef => self.representation_error(RepFlag::FfiLayout),
            FfiError::UnsupportedAbi => self.representation_error(RepFlag::FfiAbi),
            FfiError::VoidArgumentType => self.domain_error(
                DomainErrorType::FfiArgumentType,
                atom_as_cell!(atom!("void")),
            ),
            FfiError::CStrFieldType => self.domain_error(
                DomainErrorType::NonCStrFfiArgumentType,
                atom_as_cell!(atom!("cstr")),
            ),
            FfiError::NullPtr => self.domain_error(
                DomainErrorType::NonNullPtr,
                fixnum_as_cell!(Fixnum::build_with(0)),
            ),
        }
    }

    pub(super) fn error_form(&mut self, err: MachineError, src: MachineStub) -> MachineStub {
        if let Some((line_num, _col_num)) = err.location {
            functor!(
                atom!("error"),
                [
                    functor((err.stub)),
                    functor(
                        (atom!(":")),
                        [functor(src), number(line_num, (&mut self.arena))]
                    )
                ]
            )
        } else {
            functor!(atom!("error"), [functor((err.stub)), functor(src)])
        }
    }

    // throw an error pre-allocated in the heap
    pub(super) fn throw_resource_error(&mut self, err_loc: usize) {
        self.registers[1] = str_loc_as_cell!(err_loc);
        self.set_ball();
        self.unwind_stack();
    }

    pub(super) fn throw_exception(&mut self, err: MachineStub) {
        self.ball.boundary = 0;
        self.ball.stub.truncate(0);

        let mut writer = Heap::functor_writer(err);

        self.registers[1] = match writer(&mut self.heap) {
            Ok(loc) => loc,
            Err(resource_err_loc) => {
                self.throw_resource_error(resource_err_loc);
                return;
            }
        };

        self.set_ball();
        self.unwind_stack();
    }
}

#[derive(Debug)]
pub enum CompilationError {
    Arithmetic(ArithmeticError),
    ParserError(ParserError),
    ExceededMaxArity,
    InadmissibleFact,
    InadmissibleQueryTerm,
    InvalidDirective(DirectiveError),
    InvalidMetaPredicateDecl,
    InvalidModuleDecl,
    InvalidModuleExport,
    InvalidRuleHead,
    InvalidUseModuleDecl,
    InvalidModuleResolution(Atom),
    FiniteMemoryInHeap(usize),
}

#[derive(Debug)]
pub enum DirectiveError {
    ExpectedDirective(Term),
    InvalidDirective(Atom, usize /* arity */),
    InvalidOpDeclNameType(Term),
    InvalidOpDeclSpecDomain(Term),
    InvalidOpDeclSpecValue(Atom),
    InvalidOpDeclPrecType(Term),
    InvalidOpDeclPrecDomain(Fixnum),
    ShallNotCreate(Atom),
    ShallNotModify(Atom),
}

impl From<ArithmeticError> for CompilationError {
    #[inline]
    fn from(err: ArithmeticError) -> CompilationError {
        CompilationError::Arithmetic(err)
    }
}

impl From<ParserError> for CompilationError {
    #[inline]
    fn from(err: ParserError) -> CompilationError {
        CompilationError::ParserError(err)
    }
}

impl CompilationError {
    pub(crate) fn line_and_col_num(&self) -> Option<(usize, usize)> {
        match self {
            CompilationError::ParserError(err) => err.line_and_col_num(),
            _ => None,
        }
    }

    pub(crate) fn as_functor(&self) -> MachineStub {
        match self {
            CompilationError::Arithmetic(..) => {
                functor!(atom!("arithmetic_error"))
            }
            CompilationError::ExceededMaxArity => {
                functor!(atom!("exceeded_max_arity"))
            }
            CompilationError::InadmissibleFact => {
                functor!(atom!("inadmissible_fact"))
            }
            CompilationError::InadmissibleQueryTerm => {
                functor!(atom!("inadmissible_query_term"))
            }
            CompilationError::InvalidDirective(_) => {
                functor!(atom!("directive_error"))
            }
            CompilationError::InvalidMetaPredicateDecl => {
                functor!(atom!("invalid_meta_predicate_decl"))
            }
            CompilationError::InvalidModuleDecl => {
                functor!(atom!("invalid_module_declaration"))
            }
            CompilationError::InvalidModuleExport => {
                functor!(atom!("invalid_module_export"))
            }
            &CompilationError::InvalidModuleResolution(module_name) => {
                functor!(atom!("no_such_module"), [atom_as_cell(module_name)])
            }
            CompilationError::InvalidRuleHead => {
                functor!(atom!("invalid_head_of_rule")) // TODO: type_error(callable, _).
            }
            CompilationError::InvalidUseModuleDecl => {
                functor!(atom!("invalid_use_module_declaration"))
            }
            CompilationError::ParserError(ref err) => {
                functor!(err.as_atom())
            }
            CompilationError::FiniteMemoryInHeap(h) => {
                vec![FunctorElement::AbsoluteCell(str_loc_as_cell!(*h))]
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Permission {
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
    pub(crate) fn as_atom(self) -> Atom {
        match self {
            Permission::Access => atom!("access"),
            Permission::Create => atom!("create"),
            Permission::InputStream => atom!("input"),
            Permission::Modify => atom!("modify"),
            Permission::Open => atom!("open"),
            Permission::OutputStream => atom!("output"),
            Permission::Reposition => atom!("reposition"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum DomainErrorType {
    IOMode,
    NotLessThanZero,
    Order,
    SourceSink,
    Stream,
    StreamOrAlias,
    OperatorSpecifier,
    OperatorPriority,
    Directive,
    Allocator,
    FfiStruct,
    ZeroOrOne,
    NonNullPtr,
    PtrLike,
    F64,
    FfiArgument,
    FfiArgumentType,
    FixedSizedInt,
    NonCStrFfiArgumentType,
}

impl DomainErrorType {
    pub(crate) fn as_atom(self) -> Atom {
        match self {
            DomainErrorType::IOMode => atom!("io_mode"),
            DomainErrorType::NotLessThanZero => atom!("not_less_than_zero"),
            DomainErrorType::Order => atom!("order"),
            DomainErrorType::SourceSink => atom!("source_sink"),
            DomainErrorType::Stream => atom!("stream"),
            DomainErrorType::StreamOrAlias => atom!("stream_or_alias"),
            DomainErrorType::OperatorSpecifier => atom!("operator_specifier"),
            DomainErrorType::OperatorPriority => atom!("operator_priority"),
            DomainErrorType::Directive => atom!("directive"),
            DomainErrorType::Allocator => atom!("allocator"),
            DomainErrorType::ZeroOrOne => atom!("zero_or_one"),
            DomainErrorType::FfiStruct => atom!("ffi_struct"),
            DomainErrorType::NonNullPtr => atom!("non_null_pointer"),
            DomainErrorType::PtrLike => atom!("pointer_like"),
            DomainErrorType::F64 => atom!("f64"),
            DomainErrorType::FfiArgument => atom!("ffi_argument"),
            DomainErrorType::FfiArgumentType => atom!("ffi_argument_type"),
            DomainErrorType::FixedSizedInt => atom!("fixed_sized_int"),
            DomainErrorType::NonCStrFfiArgumentType => atom!("non_cstr_ffi_argument_type"),
        }
    }
}

// from 7.12.2 f) of 13211-1:1995
#[derive(Debug, Clone, Copy)]
pub(crate) enum RepFlag {
    Character,
    CharacterCode,
    InCharacterCode,
    MaxArity,
    //    MaxInteger,
    //    MinInteger,
    Term,
    FfiLayout,
    FfiAbi,
}

impl RepFlag {
    pub(crate) fn as_atom(self) -> Atom {
        match self {
            RepFlag::Character => atom!("character"),
            RepFlag::CharacterCode => atom!("character_code"),
            RepFlag::InCharacterCode => atom!("in_character_code"),
            RepFlag::MaxArity => atom!("max_arity"),
            RepFlag::Term => atom!("term"),
            //            RepFlag::MaxInteger => atom!("max_integer"),
            //            RepFlag::MinInteger => atom!("min_integer"),
            RepFlag::FfiLayout => atom!("ffi_layout"),
            RepFlag::FfiAbi => atom!("ffi_abi"),
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
    pub(crate) fn as_atom(self) -> Atom {
        match self {
            EvalError::FloatOverflow => atom!("float_overflow"),
            EvalError::Undefined => atom!("undefined"),
            //            EvalError::FloatUnderflow => atom!("underflow"),
            EvalError::ZeroDivisor => atom!("zero_divisor"),
        }
    }
}

// used by '$skip_max_list'.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CycleSearchResult {
    Cyclic {
        lambda: usize,
    }, // number of steps
    EmptyList,
    NotList {
        num_steps: usize,
        heap_loc: HeapCellValue,
    },
    PartialList {
        num_steps: usize,
        heap_loc: HeapCellValue,
    },
    ProperList {
        num_steps: usize,
    },
    PStrLocation {
        num_steps: usize,
        pstr_loc: HeapCellValue,
    },
    UntouchedList {
        num_steps: usize,
        list_loc: usize,
    },
}

impl MachineState {
    // see 8.4.3 of Draft Technical Corrigendum 2.
    pub(super) fn check_sort_errors(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("sort"), 2);

        let list = self.store(self.deref(self.registers[1]));
        let sorted = self.store(self.deref(self.registers[2]));

        match BrentAlgState::detect_cycles(&self.heap, list) {
            CycleSearchResult::PartialList { .. } => {
                let err = self.instantiation_error();
                return Err(self.error_form(err, stub_gen()));
            }
            CycleSearchResult::NotList { .. } | CycleSearchResult::Cyclic { .. } => {
                let err = self.type_error(ValidType::List, list);
                return Err(self.error_form(err, stub_gen()));
            }
            _ => {}
        };

        match BrentAlgState::detect_cycles(&self.heap, sorted) {
            CycleSearchResult::NotList { .. } | CycleSearchResult::Cyclic { .. }
                if !sorted.is_var() =>
            {
                let err = self.type_error(ValidType::List, sorted);
                Err(self.error_form(err, stub_gen()))
            }
            _ => Ok(()),
        }
    }

    fn check_for_list_pairs(&mut self, mut list: HeapCellValue) -> CallResult {
        let stub_gen = || functor_stub(atom!("keysort"), 2);

        match BrentAlgState::detect_cycles(&self.heap, list) {
            CycleSearchResult::NotList { .. } | CycleSearchResult::Cyclic { .. }
                if !list.is_var() =>
            {
                let err = self.type_error(ValidType::List, list);
                Err(self.error_form(err, stub_gen()))
            }
            _ => {
                loop {
                    read_heap_cell!(self.store(self.deref(list)),
                        (HeapCellValueTag::Lis, l) => {
                            let mut new_l = l;

                            loop {
                                read_heap_cell!(self.heap[new_l],
                                    (HeapCellValueTag::Str, s) => {
                                        new_l = s;
                                    }
                                    (HeapCellValueTag::Atom, (name, arity)) => {
                                        if name == atom!("-") && arity == 2 {
                                            break;
                                        } else {
                                            let err = self.type_error(
                                                ValidType::Pair,
                                                list_loc_as_cell!(l),
                                            );

                                            return Err(self.error_form(err, stub_gen()));
                                        }
                                    }
                                    (HeapCellValueTag::Var | HeapCellValueTag::AttrVar) => {
                                        break;
                                    }
                                    _ => {
                                        let err = self.type_error(
                                            ValidType::Pair,
                                            list_loc_as_cell!(l),
                                        );

                                        return Err(self.error_form(err, stub_gen()));
                                    }
                                );
                            }

                            list = heap_loc_as_cell!(l+1);
                        }
                        _ => {
                            break;
                        }
                    );
                }

                Ok(())
            }
        }
    }

    // see 8.4.4 of Draft Technical Corrigendum 2.
    pub(super) fn check_keysort_errors(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("keysort"), 2);

        let pairs = self.store(self.deref(self[temp_v!(1)]));
        let sorted = self.store(self.deref(self[temp_v!(2)]));

        match BrentAlgState::detect_cycles(&self.heap, pairs) {
            CycleSearchResult::PartialList { .. } => {
                let err = self.instantiation_error();
                Err(self.error_form(err, stub_gen()))
            }
            CycleSearchResult::NotList { .. } | CycleSearchResult::Cyclic { .. } => {
                let err = self.type_error(ValidType::List, pairs);
                Err(self.error_form(err, stub_gen()))
            }
            _ => Ok(()),
        }?;

        self.check_for_list_pairs(sorted)
    }
}

#[derive(Debug)]
pub enum ExistenceError {
    Module(Atom),
    ModuleSource(ModuleSource),
    Procedure(Atom, usize),
    QualifiedProcedure {
        module_name: Atom,
        name: Atom,
        arity: usize,
    },
    SourceSink(HeapCellValue),
    Stream(HeapCellValue),
    Process(HeapCellValue),
    FfiFunction(Atom),
    FfiStructType(Atom),
}

#[derive(Debug)]
pub enum SessionError {
    CompilationError(CompilationError),
    CannotOverwriteBuiltIn(PredicateKey),
    CannotOverwriteBuiltInModule(Atom),
    CannotOverwriteStaticProcedure(PredicateKey),
    ExistenceError(ExistenceError),
    ModuleDoesNotContainExport(Atom, PredicateKey),
    ModuleCannotImportSelf(Atom),
    NamelessEntry,
    OpIsInfixAndPostFix(Atom),
    PredicateNotMultifileOrDiscontiguous(CompilationTarget, PredicateKey),
}

impl From<std::io::Error> for SessionError {
    #[inline]
    fn from(err: std::io::Error) -> SessionError {
        SessionError::from(ParserError::from(err))
    }
}

impl From<ParserError> for SessionError {
    #[inline]
    fn from(err: ParserError) -> Self {
        SessionError::CompilationError(CompilationError::from(err))
    }
}

impl From<CompilationError> for SessionError {
    #[inline]
    fn from(err: CompilationError) -> Self {
        SessionError::CompilationError(err)
    }
}
