use crate::arena::*;
use crate::atom_table::*;
use crate::parser::ast::*;

#[cfg(feature = "ffi")]
use crate::ffi::FFIError;
use crate::forms::*;
use crate::machine::heap::*;
use crate::machine::loader::CompilationTarget;
use crate::machine::machine_state::*;
use crate::machine::streams::*;
use crate::machine::system_calls::BrentAlgState;
use crate::types::*;

pub type MachineStub = Vec<HeapCellValue>;
pub type MachineStubGen = Box<dyn Fn(&mut MachineState) -> MachineStub>;

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
            [atom(valid_type.as_atom()), cell(self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }
}

impl TypeError for MachineStub {
    fn type_error(self, machine_st: &mut MachineState, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            atom!("type_error"),
            [atom(valid_type.as_atom()), str(machine_st.heap.len(), 0)],
            [self]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }
}

impl TypeError for FunctorStub {
    fn type_error(self, machine_st: &mut MachineState, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            atom!("type_error"),
            [atom(valid_type.as_atom()), str(machine_st.heap.len(), 0)],
            [self]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }
}

impl TypeError for Number {
    fn type_error(self, machine_st: &mut MachineState, valid_type: ValidType) -> MachineError {
        let stub = functor!(
            atom!("type_error"),
            [
                atom(valid_type.as_atom()),
                number(&mut machine_st.arena, self)
            ]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
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
                atom(perm.as_atom()),
                atom(index_atom),
                cell(atom_as_cell!(self))
            ]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
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
            [atom(perm.as_atom()), atom(index_atom), cell(cell)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }
}

impl PermissionError for MachineStub {
    fn permission_error(
        self,
        machine_st: &mut MachineState,
        index_atom: Atom,
        perm: Permission,
    ) -> MachineError {
        let stub = functor!(
            atom!("permission_error"),
            [
                atom(perm.as_atom()),
                atom(index_atom),
                str(machine_st.heap.len(), 0)
            ],
            [self]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }
}

pub(super) trait DomainError {
    fn domain_error(self, machine_st: &mut MachineState, error: DomainErrorType) -> MachineError;
}

impl DomainError for HeapCellValue {
    fn domain_error(self, _machine_st: &mut MachineState, error: DomainErrorType) -> MachineError {
        let stub = functor!(atom!("domain_error"), [atom(error.as_atom()), cell(self)]);

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }
}

impl DomainError for Number {
    fn domain_error(self, machine_st: &mut MachineState, error: DomainErrorType) -> MachineError {
        let stub = functor!(
            atom!("domain_error"),
            [atom(error.as_atom()), number(&mut machine_st.arena, self)]
        );

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }
}

pub(super) type FunctorStub = [HeapCellValue; 3];

#[inline(always)]
pub(super) fn functor_stub(name: Atom, arity: usize) -> FunctorStub {
    [
        atom_as_cell!(atom!("/"), 2),
        atom_as_cell!(name),
        fixnum_as_cell!(Fixnum::build_with(arity as i64)),
    ]
}

impl MachineState {
    #[inline]
    pub(super) fn interrupt_error(&mut self) -> MachineError {
        let stub = functor!(atom!("$interrupt_thrown"));

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn evaluation_error(&mut self, eval_error: EvalError) -> MachineError {
        let stub = functor!(atom!("evaluation_error"), [atom(eval_error.as_atom())]);

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn resource_error(&mut self, err: ResourceError) -> MachineError {
        let stub = match err {
            ResourceError::FiniteMemory(size_requested) => {
                functor!(
                    atom!("resource_error"),
                    [atom(atom!("finite_memory")), cell(size_requested)]
                )
            }
            ResourceError::OutOfFiles => {
                functor!(atom!("resource_error"), [atom(atom!("file_descriptors"))])
            }
        };

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
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
                    [atom(atom!("source_sink")), atom(name)]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Received,
                }
            }
            ExistenceError::QualifiedProcedure {
                module_name,
                name,
                arity,
            } => {
                let h = self.heap.len();

                let ind_stub = functor!(atom!("/"), [atom(name), fixnum(arity)]);
                let res_stub = functor!(atom!(":"), [atom(module_name), str(h + 3, 0)], [ind_stub]);

                let stub = functor!(
                    atom!("existence_error"),
                    [atom(atom!("procedure")), str(h, 0)],
                    [res_stub]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Constructed,
                }
            }
            ExistenceError::Procedure(name, arity) => {
                let culprit = functor!(atom!("/"), [atom(name), fixnum(arity)]);

                let stub = functor!(
                    atom!("existence_error"),
                    [atom(atom!("procedure")), str(self.heap.len(), 0)],
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
                    atom!("existence_error"),
                    [atom(atom!("source_sink")), str(self.heap.len(), 0)],
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
                    atom!("existence_error"),
                    [atom(atom!("source_sink")), cell(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Received,
                }
            }
            ExistenceError::Stream(culprit) => {
                let stub = functor!(
                    atom!("existence_error"),
                    [atom(atom!("stream")), cell(culprit)]
                );

                MachineError {
                    stub,
                    location: None,
                    from: ErrorProvenance::Received,
                }
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
            ArithmeticError::UninstantiatedVar => self.instantiation_error(),
            ArithmeticError::NonEvaluableFunctor(literal, arity) => {
                let culprit = functor!(atom!("/"), [literal(literal), fixnum(arity)]);

                self.type_error(ValidType::Evaluable, culprit)
            }
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
            from: ErrorProvenance::Received,
        }
    }

    pub(super) fn session_error(&mut self, err: SessionError) -> MachineError {
        match err {
            SessionError::CannotOverwriteBuiltIn(key) => self.permission_error(
                Permission::Modify,
                atom!("static_procedure"),
                functor_stub(key.0, key.1)
                    .into_iter()
                    .collect::<MachineStub>(),
            ),
            SessionError::CannotOverwriteBuiltInModule(module) => {
                self.permission_error(Permission::Modify, atom!("static_module"), module)
            }
            SessionError::ExistenceError(err) => self.existence_error(err),
            SessionError::ModuleDoesNotContainExport(module_name, key) => {
                let functor_stub = functor_stub(key.0, key.1);

                let stub = functor!(
                    atom!("module_does_not_contain_claimed_export"),
                    [atom(module_name), str(self.heap.len() + 4, 0)],
                    [functor_stub]
                );

                self.permission_error(Permission::Access, atom!("private_procedure"), stub)
            }
            SessionError::ModuleCannotImportSelf(module_name) => {
                let error_atom = atom!("module_cannot_import_self");

                self.permission_error(
                    Permission::Modify,
                    atom!("module"),
                    functor!(error_atom, [atom(module_name)]),
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
                let functor_stub = functor_stub(key.0, key.1);

                let stub = functor!(
                    atom!(":"),
                    [
                        atom(compilation_target.module_name()),
                        str(self.heap.len() + 4, 0)
                    ],
                    [functor_stub]
                );

                self.permission_error(
                    Permission::Modify,
                    atom!("not_declared_multifile_or_discontiguous"),
                    stub,
                )
            }
            SessionError::QueryCannotBeDefinedAsFact => {
                let error_atom = atom!("query_cannot_be_defined_as_fact");

                self.permission_error(
                    Permission::Create,
                    atom!("static_procedure"),
                    functor!(error_atom),
                )
            }
        }
    }

    pub(super) fn syntax_error<E: Into<CompilationError>>(&mut self, err: E) -> MachineError {
        let err = err.into();

        if let CompilationError::Arithmetic(err) = err {
            return self.arithmetic_error(err);
        }

        let location = err.line_and_col_num();
        let stub = err.as_functor();

        let stub = functor!(atom!("syntax_error"), [str(self.heap.len(), 0)], [stub]);

        MachineError {
            stub,
            location,
            from: ErrorProvenance::Constructed,
        }
    }

    pub(super) fn representation_error(&mut self, flag: RepFlag) -> MachineError {
        let stub = functor!(atom!("representation_error"), [atom(flag.as_atom())]);

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Received,
        }
    }

    #[cfg(feature = "ffi")]
    pub(super) fn ffi_error(&mut self, err: FFIError) -> MachineError {
        let error_atom = match err {
            FFIError::ValueCast => atom!("value_cast"),
            FFIError::ValueDontFit => atom!("value_dont_fit"),
            FFIError::InvalidFFIType => atom!("invalid_ffi_type"),
            FFIError::InvalidStructName => atom!("invalid_struct_name"),
            FFIError::FunctionNotFound => atom!("function_not_found"),
            FFIError::StructNotFound => atom!("struct_not_found"),
        };
        let stub = functor!(atom!("ffi_error"), [atom(error_atom)]);

        MachineError {
            stub,
            location: None,
            from: ErrorProvenance::Constructed,
        }
    }

    pub(super) fn error_form(&mut self, err: MachineError, src: FunctorStub) -> MachineStub {
        let h = self.heap.len();
        let location = err.location;
        let stub_addition_len = if err.len() == 1 {
            0 // if err contains 1 cell, it can be inlined at stub[1].
        } else {
            err.len()
        };

        let mut stub = vec![
            atom_as_cell!(atom!("error"), 2),
            str_loc_as_cell!(h + 3),
            str_loc_as_cell!(h + 3 + stub_addition_len),
        ];

        if stub_addition_len > 0 {
            stub.extend(err.into_iter(3));
        } else {
            stub[1] = err.stub[0];
        }

        if let Some((line_num, _)) = location {
            stub.push(atom_as_cell!(atom!(":"), 2));
            stub.push(str_loc_as_cell!(h + 6 + stub_addition_len));
            stub.push(integer_as_cell!(Number::arena_from(
                line_num,
                &mut self.arena
            )));
        }

        stub.extend(src.iter());
        stub
    }

    pub(super) fn throw_exception(&mut self, err: MachineStub) {
        let h = self.heap.len();
        let err_len = err.len();

        self.ball.boundary = 0;
        self.ball.stub.truncate(0);

        self.heap.extend(err);

        self.registers[1] = if err_len == 1 {
            heap_loc_as_cell!(h)
        } else {
            str_loc_as_cell!(h)
        };

        self.set_ball();
        self.unwind_stack();
    }
}

impl MachineError {
    fn into_iter(self, offset: usize) -> Box<dyn Iterator<Item = HeapCellValue>> {
        match self.from {
            ErrorProvenance::Constructed => {
                Box::new(self.stub.into_iter().map(move |hcv| hcv + offset))
            }
            ErrorProvenance::Received => Box::new(self.stub.into_iter()),
        }
    }

    fn len(&self) -> usize {
        self.stub.len()
    }
}

#[derive(Debug)]
pub enum CompilationError {
    Arithmetic(ArithmeticError),
    ParserError(ParserError),
    CannotParseCyclicTerm,
    ExceededMaxArity,
    ExpectedRel,
    InadmissibleFact,
    InadmissibleQueryTerm,
    InconsistentEntry,
    InvalidMetaPredicateDecl,
    InvalidModuleDecl,
    InvalidModuleExport,
    InvalidRuleHead,
    InvalidUseModuleDecl,
    InvalidModuleResolution(Atom),
    UnreadableTerm,
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
            CompilationError::CannotParseCyclicTerm => {
                functor!(atom!("cannot_parse_cyclic_term"))
            }
            CompilationError::ExceededMaxArity => {
                functor!(atom!("exceeded_max_arity"))
            }
            CompilationError::ExpectedRel => {
                functor!(atom!("expected_relation"))
            }
            CompilationError::InadmissibleFact => {
                // TODO: type_error(callable, _).
                functor!(atom!("inadmissible_fact"))
            }
            CompilationError::InadmissibleQueryTerm => {
                // TODO: type_error(callable, _).
                functor!(atom!("inadmissible_query_term"))
            }
            CompilationError::InconsistentEntry => {
                functor!(atom!("inconsistent_entry"))
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
            CompilationError::InvalidModuleResolution(ref module_name) => {
                functor!(atom!("no_such_module"), [atom(module_name)])
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
            CompilationError::UnreadableTerm => {
                functor!(atom!("unreadable_term"))
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
            //            RepFlag::MinInteger => atom!("min_integer")
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
    Cyclic(usize),
    EmptyList,
    NotList(usize, HeapCellValue), // the list length until the second argument in the heap
    PartialList(usize, Ref),       // the list length (up to max), and an offset into the heap.
    ProperList(usize),             // the list length.
    PStrLocation(usize, usize, usize), // list length (up to max), the heap address of the PStr, the offset
    UntouchedList(usize, usize), // list length (up to max), the address of an uniterated Addr::Lis(address).
    UntouchedCStr(Atom, usize),
}

impl MachineState {
    // see 8.4.3 of Draft Technical Corrigendum 2.
    pub(super) fn check_sort_errors(&mut self) -> CallResult {
        let stub_gen = || functor_stub(atom!("sort"), 2);

        let list = self.store(self.deref(self.registers[1]));
        let sorted = self.store(self.deref(self.registers[2]));

        match BrentAlgState::detect_cycles(&self.heap, list) {
            CycleSearchResult::PartialList(..) => {
                let err = self.instantiation_error();
                return Err(self.error_form(err, stub_gen()));
            }
            CycleSearchResult::NotList(..) | CycleSearchResult::Cyclic(_) => {
                let err = self.type_error(ValidType::List, list);
                return Err(self.error_form(err, stub_gen()));
            }
            _ => {}
        };

        match BrentAlgState::detect_cycles(&self.heap, sorted) {
            CycleSearchResult::NotList(..) | CycleSearchResult::Cyclic(_) if !sorted.is_var() => {
                let err = self.type_error(ValidType::List, sorted);
                Err(self.error_form(err, stub_gen()))
            }
            _ => Ok(()),
        }
    }

    fn check_for_list_pairs(&mut self, mut list: HeapCellValue) -> CallResult {
        let stub_gen = || functor_stub(atom!("keysort"), 2);

        match BrentAlgState::detect_cycles(&self.heap, list) {
            CycleSearchResult::NotList(..) | CycleSearchResult::Cyclic(_) if !list.is_var() => {
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
            CycleSearchResult::PartialList(..) => {
                let err = self.instantiation_error();
                Err(self.error_form(err, stub_gen()))
            }
            CycleSearchResult::NotList(..) | CycleSearchResult::Cyclic(_) => {
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
}

#[derive(Debug)]
pub enum SessionError {
    CompilationError(CompilationError),
    CannotOverwriteBuiltIn(PredicateKey),
    CannotOverwriteBuiltInModule(Atom),
    ExistenceError(ExistenceError),
    ModuleDoesNotContainExport(Atom, PredicateKey),
    ModuleCannotImportSelf(Atom),
    NamelessEntry,
    OpIsInfixAndPostFix(Atom),
    PredicateNotMultifileOrDiscontiguous(CompilationTarget, PredicateKey),
    QueryCannotBeDefinedAsFact,
}

#[derive(Debug)]
pub(crate) enum EvalSession {
    // EntrySuccess,
    Error(SessionError),
}

impl From<SessionError> for EvalSession {
    #[inline]
    fn from(err: SessionError) -> Self {
        EvalSession::Error(err)
    }
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

impl From<ParserError> for EvalSession {
    #[inline]
    fn from(err: ParserError) -> Self {
        EvalSession::from(SessionError::from(err))
    }
}
