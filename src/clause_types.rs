use prolog_parser::ast::*;
use prolog_parser::{clause_name, temp_v};

use crate::forms::Number;
use crate::machine::machine_indices::*;
use crate::rug::rand::RandState;

use ref_thread_local::{ref_thread_local, RefThreadLocal};

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum CompareNumberQT {
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    NotEqual,
    Equal,
}

impl CompareNumberQT {
    fn name(self) -> &'static str {
        match self {
            CompareNumberQT::GreaterThan => ">",
            CompareNumberQT::LessThan => "<",
            CompareNumberQT::GreaterThanOrEqual => ">=",
            CompareNumberQT::LessThanOrEqual => "=<",
            CompareNumberQT::NotEqual => "=\\=",
            CompareNumberQT::Equal => "=:=",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CompareTermQT {
    LessThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    GreaterThan,
}

impl CompareTermQT {
    fn name<'a>(self) -> &'a str {
        match self {
            CompareTermQT::GreaterThan => "@>",
            CompareTermQT::LessThan => "@<",
            CompareTermQT::GreaterThanOrEqual => "@>=",
            CompareTermQT::LessThanOrEqual => "@=<",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ArithmeticTerm {
    Reg(RegType),
    Interm(usize),
    Number(Number),
}

impl ArithmeticTerm {
    pub(crate) fn interm_or(&self, interm: usize) -> usize {
        if let &ArithmeticTerm::Interm(interm) = self {
            interm
        } else {
            interm
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum InlinedClauseType {
    CompareNumber(CompareNumberQT, ArithmeticTerm, ArithmeticTerm),
    IsAtom(RegType),
    IsAtomic(RegType),
    IsCompound(RegType),
    IsInteger(RegType),
    IsNumber(RegType),
    IsRational(RegType),
    IsFloat(RegType),
    IsNonVar(RegType),
    IsVar(RegType),
}

ref_thread_local! {
    pub(crate)static managed RANDOM_STATE: RandState<'static> = RandState::new();
}

ref_thread_local! {
    pub(crate)static managed CLAUSE_TYPE_FORMS: BTreeMap<(&'static str, usize), ClauseType> = {
        let mut m = BTreeMap::new();

        let r1 = temp_v!(1);
        let r2 = temp_v!(2);

        m.insert((">", 2),
                 ClauseType::Inlined(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThan, ar_reg!(r1), ar_reg!(r2))));
        m.insert(("<", 2),
                 ClauseType::Inlined(InlinedClauseType::CompareNumber(CompareNumberQT::LessThan, ar_reg!(r1), ar_reg!(r2))));
        m.insert((">=", 2), ClauseType::Inlined(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThanOrEqual, ar_reg!(r1), ar_reg!(r2))));
        m.insert(("=<", 2), ClauseType::Inlined(InlinedClauseType::CompareNumber(CompareNumberQT::LessThanOrEqual, ar_reg!(r1), ar_reg!(r2))));
        m.insert(("=:=", 2), ClauseType::Inlined(InlinedClauseType::CompareNumber(CompareNumberQT::Equal, ar_reg!(r1), ar_reg!(r2))));
        m.insert(("=\\=", 2), ClauseType::Inlined(InlinedClauseType::CompareNumber(CompareNumberQT::NotEqual, ar_reg!(r1), ar_reg!(r2))));
        m.insert(("atom", 1), ClauseType::Inlined(InlinedClauseType::IsAtom(r1)));
        m.insert(("atomic", 1), ClauseType::Inlined(InlinedClauseType::IsAtomic(r1)));
        m.insert(("compound", 1), ClauseType::Inlined(InlinedClauseType::IsCompound(r1)));
        m.insert(("integer", 1), ClauseType::Inlined(InlinedClauseType::IsInteger(r1)));
        m.insert(("number", 1), ClauseType::Inlined(InlinedClauseType::IsNumber(r1)));
        m.insert(("rational", 1), ClauseType::Inlined(InlinedClauseType::IsRational(r1)));
        m.insert(("float", 1), ClauseType::Inlined(InlinedClauseType::IsFloat(r1)));
        m.insert(("nonvar", 1), ClauseType::Inlined(InlinedClauseType::IsNonVar(r1)));
        m.insert(("var", 1), ClauseType::Inlined(InlinedClauseType::IsVar(r1)));
        m.insert(("acyclic_term", 1), ClauseType::BuiltIn(BuiltInClauseType::AcyclicTerm));
        m.insert(("arg", 3), ClauseType::BuiltIn(BuiltInClauseType::Arg));
        m.insert(("compare", 3), ClauseType::BuiltIn(BuiltInClauseType::Compare));
        m.insert(("@>", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThan)));
        m.insert(("@<", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::LessThan)));
        m.insert(("@>=", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThanOrEqual)));
        m.insert(("@=<", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::LessThanOrEqual)));
        m.insert(("copy_term", 2), ClauseType::BuiltIn(BuiltInClauseType::CopyTerm));
        m.insert(("==", 2), ClauseType::BuiltIn(BuiltInClauseType::Eq));
        m.insert(("functor", 3), ClauseType::BuiltIn(BuiltInClauseType::Functor));
        m.insert(("ground", 1), ClauseType::BuiltIn(BuiltInClauseType::Ground));
        m.insert(("is", 2), ClauseType::BuiltIn(BuiltInClauseType::Is(r1, ar_reg!(r2))));
        m.insert(("keysort", 2), ClauseType::BuiltIn(BuiltInClauseType::KeySort));
        m.insert(("\\==", 2), ClauseType::BuiltIn(BuiltInClauseType::NotEq));
        m.insert(("read", 2), ClauseType::BuiltIn(BuiltInClauseType::Read));
        m.insert(("sort", 2), ClauseType::BuiltIn(BuiltInClauseType::Sort));

        m
    };
}

impl InlinedClauseType {
    pub(crate) fn name(&self) -> &'static str {
        match self {
            &InlinedClauseType::CompareNumber(qt, ..) => qt.name(),
            &InlinedClauseType::IsAtom(..) => "atom",
            &InlinedClauseType::IsAtomic(..) => "atomic",
            &InlinedClauseType::IsCompound(..) => "compound",
            &InlinedClauseType::IsNumber(..) => "number",
            &InlinedClauseType::IsInteger(..) => "integer",
            &InlinedClauseType::IsRational(..) => "rational",
            &InlinedClauseType::IsFloat(..) => "float",
            &InlinedClauseType::IsNonVar(..) => "nonvar",
            &InlinedClauseType::IsVar(..) => "var",
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) enum SystemClauseType {
    AtomChars,
    AtomCodes,
    AtomLength,
    BindFromRegister,
    CallContinuation,
    CharCode,
    CharType,
    CharsToNumber,
    CodesToNumber,
    CopyTermWithoutAttrVars,
    CheckCutPoint,
    Close,
    CopyToLiftedHeap,
    CreatePartialString,
    CurrentHostname,
    CurrentInput,
    CurrentOutput,
    DirectoryFiles,
    FileSize,
    FileExists,
    DirectoryExists,
    DirectorySeparator,
    MakeDirectory,
    MakeDirectoryPath,
    DeleteFile,
	RenameFile,
    DeleteDirectory,
    WorkingDirectory,
    PathCanonical,
    FileTime,
    DeleteAttribute,
    DeleteHeadAttribute,
    DynamicModuleResolution(usize),
    EnqueueAttributedVar,
    FetchGlobalVar,
    FirstStream,
    FlushOutput,
    GetByte,
    GetChar,
    GetNChars,
    GetCode,
    GetSingleChar,
    ResetAttrVarState,
    TruncateIfNoLiftedHeapGrowthDiff,
    TruncateIfNoLiftedHeapGrowth,
    GetAttributedVariableList,
    GetAttrVarQueueDelimiter,
    GetAttrVarQueueBeyond,
    GetBValue,
    GetContinuationChunk,
    GetNextDBRef,
    GetNextOpDBRef,
    IsPartialString,
    LookupDBRef,
    LookupOpDBRef,
    Halt,
    GetLiftedHeapFromOffset,
    GetLiftedHeapFromOffsetDiff,
    GetSCCCleaner,
    HeadIsDynamic,
    InstallSCCCleaner,
    InstallInferenceCounter,
    LiftedHeapLength,
    LoadLibraryAsStream,
    ModuleExists,
    NextEP,
    NoSuchPredicate,
    NumberToChars,
    NumberToCodes,
    OpDeclaration,
    Open,
    NextStream,
    PartialStringTail,
    PeekByte,
    PeekChar,
    PeekCode,
    PointsToContinuationResetMarker,
    PutByte,
    PutChar,
    PutChars,
    PutCode,
    REPL(REPLCodePtr),
    ReadQueryTerm,
    ReadTerm,
    RedoAttrVarBinding,
    RemoveCallPolicyCheck,
    RemoveInferenceCounter,
    ResetContinuationMarker,
    RestoreCutPolicy,
    SetCutPoint(RegType),
    SetInput,
    SetOutput,
    StoreBacktrackableGlobalVar,
    StoreGlobalVar,
    StreamProperty,
    SetStreamPosition,
    InferenceLevel,
    CleanUpBlock,
    EraseBall,
    Fail,
    GetBall,
    GetCurrentBlock,
    GetCutPoint,
    GetDoubleQuotes,
    InstallNewBlock,
    Maybe,
    CpuNow,
    CurrentTime,
    QuotedToken,
    ReadTermFromChars,
    ResetBlock,
    ReturnFromVerifyAttr,
    SetBall,
    SetCutPointByDefault(RegType),
    SetDoubleQuotes,
    SetSeed,
    SkipMaxList,
    Sleep,
    SocketClientOpen,
    SocketServerOpen,
    SocketServerAccept,
    SocketServerClose,
    Succeed,
    TermAttributedVariables,
    TermVariables,
    TruncateLiftedHeapTo,
    UnifyWithOccursCheck,
    UnwindEnvironments,
    UnwindStack,
    Variant,
    WAMInstructions,
    WriteTerm,
    WriteTermToChars,
    ScryerPrologVersion,
    CryptoRandomByte,
    CryptoDataHash,
    CryptoDataHKDF,
    CryptoPasswordHash,
    CryptoDataEncrypt,
    CryptoDataDecrypt,
    CryptoCurveScalarMult,
    Ed25519Sign,
    Ed25519Verify,
    Ed25519NewKeyPair,
    Ed25519KeyPairPublicKey,
    Curve25519ScalarMult,
    LoadHTML,
    LoadXML,
    GetEnv,
    SetEnv,
    UnsetEnv,
    PID,
    CharsBase64,
    DevourWhitespace,
    IsSTOEnabled,
    SetSTOAsUnify,
    SetNSTOAsUnify,
    SetSTOWithErrorAsUnify,
    HomeDirectory,
    DebugHook,
    PopCount
}

impl SystemClauseType {
    pub(crate) fn name(&self) -> ClauseName {
        match self {
            &SystemClauseType::AtomChars => clause_name!("$atom_chars"),
            &SystemClauseType::AtomCodes => clause_name!("$atom_codes"),
            &SystemClauseType::AtomLength => clause_name!("$atom_length"),
            &SystemClauseType::BindFromRegister => clause_name!("$bind_from_register"),
            &SystemClauseType::CallContinuation => clause_name!("$call_continuation"),
            &SystemClauseType::CharCode => clause_name!("$char_code"),
            &SystemClauseType::CharType => clause_name!("$char_type"),
            &SystemClauseType::CharsToNumber => clause_name!("$chars_to_number"),
            &SystemClauseType::CheckCutPoint => clause_name!("$check_cp"),
            &SystemClauseType::CodesToNumber => clause_name!("$codes_to_number"),
            &SystemClauseType::CopyTermWithoutAttrVars => {
                clause_name!("$copy_term_without_attr_vars")
            }
            &SystemClauseType::CreatePartialString => clause_name!("$create_partial_string"),
            &SystemClauseType::CurrentInput => clause_name!("$current_input"),
            &SystemClauseType::CurrentHostname => clause_name!("$current_hostname"),
            &SystemClauseType::CurrentOutput => clause_name!("$current_output"),
            &SystemClauseType::DirectoryFiles => clause_name!("$directory_files"),
            &SystemClauseType::FileSize => clause_name!("$file_size"),
            &SystemClauseType::FileExists => clause_name!("$file_exists"),
            &SystemClauseType::DirectoryExists => clause_name!("$directory_exists"),
            &SystemClauseType::DirectorySeparator => clause_name!("$directory_separator"),
            &SystemClauseType::MakeDirectory => clause_name!("$make_directory"),
            &SystemClauseType::MakeDirectoryPath => clause_name!("$make_directory_path"),
            &SystemClauseType::DeleteFile => clause_name!("$delete_file"),
            &SystemClauseType::RenameFile => clause_name!("$rename_file"),
            &SystemClauseType::DeleteDirectory => clause_name!("$delete_directory"),
            &SystemClauseType::WorkingDirectory => clause_name!("$working_directory"),
            &SystemClauseType::PathCanonical => clause_name!("$path_canonical"),
            &SystemClauseType::FileTime => clause_name!("$file_time"),
            &SystemClauseType::REPL(REPLCodePtr::AddDiscontiguousPredicate) => {
                clause_name!("$add_discontiguous_predicate")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddDynamicPredicate) => {
                clause_name!("$add_dynamic_predicate")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddMultifilePredicate) => {
                clause_name!("$add_multifile_predicate")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddGoalExpansionClause) => {
                clause_name!("$add_goal_expansion_clause")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddTermExpansionClause) => {
                clause_name!("$add_term_expansion_clause")
            }
            &SystemClauseType::REPL(REPLCodePtr::ClauseToEvacuable) => {
                clause_name!("$clause_to_evacuable")
            }
            &SystemClauseType::REPL(REPLCodePtr::ScopedClauseToEvacuable) => {
                clause_name!("$scoped_clause_to_evacuable")
            }
            &SystemClauseType::REPL(REPLCodePtr::ConcludeLoad) => clause_name!("$conclude_load"),
            &SystemClauseType::REPL(REPLCodePtr::DeclareModule) => clause_name!("$declare_module"),
            &SystemClauseType::REPL(REPLCodePtr::LoadCompiledLibrary) => {
                clause_name!("$load_compiled_library")
            }
            &SystemClauseType::REPL(REPLCodePtr::PushLoadStatePayload) => {
                clause_name!("$push_load_state_payload")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddInSituFilenameModule) => {
                clause_name!("$add_in_situ_filename_module")
            }
            &SystemClauseType::REPL(REPLCodePtr::Asserta) => clause_name!("$asserta"),
            &SystemClauseType::REPL(REPLCodePtr::Assertz) => clause_name!("$assertz"),
            &SystemClauseType::REPL(REPLCodePtr::Retract) => clause_name!("$retract_clause"),
            &SystemClauseType::REPL(REPLCodePtr::UseModule) => clause_name!("$use_module"),
            &SystemClauseType::REPL(REPLCodePtr::PushLoadContext) => {
                clause_name!("$push_load_context")
            }
            &SystemClauseType::REPL(REPLCodePtr::PopLoadContext) => {
                clause_name!("$pop_load_context")
            }
            &SystemClauseType::REPL(REPLCodePtr::PopLoadStatePayload) => {
                clause_name!("$pop_load_state_payload")
            }
            &SystemClauseType::REPL(REPLCodePtr::LoadContextSource) => {
                clause_name!("$prolog_lc_source")
            }
            &SystemClauseType::REPL(REPLCodePtr::LoadContextFile) => {
                clause_name!("$prolog_lc_file")
            }
            &SystemClauseType::REPL(REPLCodePtr::LoadContextDirectory) => {
                clause_name!("$prolog_lc_dir")
            }
            &SystemClauseType::REPL(REPLCodePtr::LoadContextModule) => {
                clause_name!("$prolog_lc_module")
            }
            &SystemClauseType::REPL(REPLCodePtr::LoadContextStream) => {
                clause_name!("$prolog_lc_stream")
            }
            &SystemClauseType::REPL(REPLCodePtr::MetaPredicateProperty) => {
                clause_name!("$cpp_meta_predicate_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::BuiltInProperty) => {
                clause_name!("$cpp_built_in_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::DynamicProperty) => {
                clause_name!("$cpp_dynamic_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::MultifileProperty) => {
                clause_name!("$cpp_multifile_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::DiscontiguousProperty) => {
                clause_name!("$cpp_discontiguous_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::AbolishClause) => clause_name!("$abolish_clause"),
            &SystemClauseType::REPL(REPLCodePtr::IsConsistentWithTermQueue) => {
                clause_name!("$is_consistent_with_term_queue")
            }
            &SystemClauseType::REPL(REPLCodePtr::FlushTermQueue) => {
                clause_name!("$flush_term_queue")
            }
            &SystemClauseType::REPL(REPLCodePtr::RemoveModuleExports) => {
                clause_name!("$remove_module_exports")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddNonCountedBacktracking) => {
                clause_name!("$add_non_counted_backtracking")
            }
            &SystemClauseType::Close => clause_name!("$close"),
            &SystemClauseType::CopyToLiftedHeap => clause_name!("$copy_to_lh"),
            &SystemClauseType::DeleteAttribute => clause_name!("$del_attr_non_head"),
            &SystemClauseType::DeleteHeadAttribute => clause_name!("$del_attr_head"),
            &SystemClauseType::DynamicModuleResolution(_) => clause_name!("$module_call"),
            &SystemClauseType::EnqueueAttributedVar => clause_name!("$enqueue_attr_var"),
            &SystemClauseType::FetchGlobalVar => clause_name!("$fetch_global_var"),
            &SystemClauseType::FirstStream => clause_name!("$first_stream"),
            &SystemClauseType::FlushOutput => clause_name!("$flush_output"),
            &SystemClauseType::GetByte => clause_name!("$get_byte"),
            &SystemClauseType::GetChar => clause_name!("$get_char"),
            &SystemClauseType::GetNChars => clause_name!("$get_n_chars"),
            &SystemClauseType::GetCode => clause_name!("$get_code"),
            &SystemClauseType::GetSingleChar => clause_name!("$get_single_char"),
            &SystemClauseType::ResetAttrVarState => clause_name!("$reset_attr_var_state"),
            &SystemClauseType::TruncateIfNoLiftedHeapGrowth => {
                clause_name!("$truncate_if_no_lh_growth")
            }
            &SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff => {
                clause_name!("$truncate_if_no_lh_growth_diff")
            }
            &SystemClauseType::GetAttributedVariableList => clause_name!("$get_attr_list"),
            &SystemClauseType::GetAttrVarQueueDelimiter => {
                clause_name!("$get_attr_var_queue_delim")
            }
            &SystemClauseType::GetAttrVarQueueBeyond => clause_name!("$get_attr_var_queue_beyond"),
            &SystemClauseType::GetContinuationChunk => clause_name!("$get_cont_chunk"),
            &SystemClauseType::GetLiftedHeapFromOffset => clause_name!("$get_lh_from_offset"),
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => {
                clause_name!("$get_lh_from_offset_diff")
            }
            &SystemClauseType::GetBValue => clause_name!("$get_b_value"),
            //          &SystemClauseType::GetClause => clause_name!("$get_clause"),
            &SystemClauseType::GetNextDBRef => clause_name!("$get_next_db_ref"),
            &SystemClauseType::GetNextOpDBRef => clause_name!("$get_next_op_db_ref"),
            &SystemClauseType::LookupDBRef => clause_name!("$lookup_db_ref"),
            &SystemClauseType::LookupOpDBRef => clause_name!("$lookup_op_db_ref"),
            &SystemClauseType::GetDoubleQuotes => clause_name!("$get_double_quotes"),
            //          &SystemClauseType::GetModuleClause => clause_name!("$get_module_clause"),
            &SystemClauseType::GetSCCCleaner => clause_name!("$get_scc_cleaner"),
            &SystemClauseType::Halt => clause_name!("$halt"),
            &SystemClauseType::HeadIsDynamic => clause_name!("$head_is_dynamic"),
            &SystemClauseType::Open => clause_name!("$open"),
            &SystemClauseType::OpDeclaration => clause_name!("$op"),
            &SystemClauseType::InstallSCCCleaner => clause_name!("$install_scc_cleaner"),
            &SystemClauseType::InstallInferenceCounter => {
                clause_name!("$install_inference_counter")
            }
            &SystemClauseType::IsPartialString => clause_name!("$is_partial_string"),
            &SystemClauseType::PartialStringTail => clause_name!("$partial_string_tail"),
            &SystemClauseType::PeekByte => clause_name!("$peek_byte"),
            &SystemClauseType::PeekChar => clause_name!("$peek_char"),
            &SystemClauseType::PeekCode => clause_name!("$peek_code"),
            &SystemClauseType::LiftedHeapLength => clause_name!("$lh_length"),
            &SystemClauseType::Maybe => clause_name!("maybe"),
            &SystemClauseType::CpuNow => clause_name!("$cpu_now"),
            &SystemClauseType::CurrentTime => clause_name!("$current_time"),
            // &SystemClauseType::ModuleAssertDynamicPredicateToFront => {
            //     clause_name!("$module_asserta")
            // }
            // &SystemClauseType::ModuleAssertDynamicPredicateToBack => {
            //     clause_name!("$module_assertz")
            // }
            //          &SystemClauseType::ModuleHeadIsDynamic => clause_name!("$module_head_is_dynamic"),
            &SystemClauseType::ModuleExists => clause_name!("$module_exists"),
            &SystemClauseType::NextStream => clause_name!("$next_stream"),
            &SystemClauseType::NoSuchPredicate => clause_name!("$no_such_predicate"),
            &SystemClauseType::NumberToChars => clause_name!("$number_to_chars"),
            &SystemClauseType::NumberToCodes => clause_name!("$number_to_codes"),
            &SystemClauseType::PointsToContinuationResetMarker => {
                clause_name!("$points_to_cont_reset_marker")
            }
            &SystemClauseType::PutByte => {
                clause_name!("$put_byte")
            }
            &SystemClauseType::PutChar => {
                clause_name!("$put_char")
            }
            &SystemClauseType::PutChars => {
                clause_name!("$put_chars")
            }
            &SystemClauseType::PutCode => {
                clause_name!("$put_code")
            }
            &SystemClauseType::QuotedToken => {
                clause_name!("$quoted_token")
            }
            &SystemClauseType::RedoAttrVarBinding => clause_name!("$redo_attr_var_binding"),
            &SystemClauseType::RemoveCallPolicyCheck => clause_name!("$remove_call_policy_check"),
            &SystemClauseType::RemoveInferenceCounter => clause_name!("$remove_inference_counter"),
            &SystemClauseType::RestoreCutPolicy => clause_name!("$restore_cut_policy"),
            &SystemClauseType::SetCutPoint(_) => clause_name!("$set_cp"),
            &SystemClauseType::SetInput => clause_name!("$set_input"),
            &SystemClauseType::SetOutput => clause_name!("$set_output"),
            &SystemClauseType::SetSeed => clause_name!("$set_seed"),
            &SystemClauseType::StreamProperty => clause_name!("$stream_property"),
            &SystemClauseType::SetStreamPosition => clause_name!("$set_stream_position"),
            &SystemClauseType::StoreBacktrackableGlobalVar => {
                clause_name!("$store_back_trackable_global_var")
            }
            &SystemClauseType::StoreGlobalVar => clause_name!("$store_global_var"),
            &SystemClauseType::InferenceLevel => clause_name!("$inference_level"),
            &SystemClauseType::CleanUpBlock => clause_name!("$clean_up_block"),
            &SystemClauseType::EraseBall => clause_name!("$erase_ball"),
            &SystemClauseType::Fail => clause_name!("$fail"),
            &SystemClauseType::GetBall => clause_name!("$get_ball"),
            &SystemClauseType::GetCutPoint => clause_name!("$get_cp"),
            &SystemClauseType::GetCurrentBlock => clause_name!("$get_current_block"),
            &SystemClauseType::InstallNewBlock => clause_name!("$install_new_block"),
            &SystemClauseType::NextEP => clause_name!("$nextEP"),
            &SystemClauseType::ReadQueryTerm => clause_name!("$read_query_term"),
            &SystemClauseType::ReadTerm => clause_name!("$read_term"),
            &SystemClauseType::ReadTermFromChars => clause_name!("$read_term_from_chars"),
            &SystemClauseType::ResetBlock => clause_name!("$reset_block"),
            &SystemClauseType::ResetContinuationMarker => clause_name!("$reset_cont_marker"),
            &SystemClauseType::ReturnFromVerifyAttr => clause_name!("$return_from_verify_attr"),
            &SystemClauseType::SetBall => clause_name!("$set_ball"),
            &SystemClauseType::SetCutPointByDefault(_) => clause_name!("$set_cp_by_default"),
            &SystemClauseType::SetDoubleQuotes => clause_name!("$set_double_quotes"),
            &SystemClauseType::SkipMaxList => clause_name!("$skip_max_list"),
            &SystemClauseType::Sleep => clause_name!("$sleep"),
            &SystemClauseType::SocketClientOpen => clause_name!("$socket_client_open"),
            &SystemClauseType::SocketServerOpen => clause_name!("$socket_server_open"),
            &SystemClauseType::SocketServerAccept => clause_name!("$socket_server_accept"),
            &SystemClauseType::SocketServerClose => clause_name!("$socket_server_close"),
            &SystemClauseType::Succeed => clause_name!("$succeed"),
            &SystemClauseType::TermAttributedVariables => {
                clause_name!("$term_attributed_variables")
            }
            &SystemClauseType::TermVariables => clause_name!("$term_variables"),
            &SystemClauseType::TruncateLiftedHeapTo => clause_name!("$truncate_lh_to"),
            &SystemClauseType::UnifyWithOccursCheck => clause_name!("$unify_with_occurs_check"),
            &SystemClauseType::UnwindEnvironments => clause_name!("$unwind_environments"),
            &SystemClauseType::UnwindStack => clause_name!("$unwind_stack"),
            &SystemClauseType::Variant => clause_name!("$variant"),
            &SystemClauseType::WAMInstructions => clause_name!("$wam_instructions"),
            &SystemClauseType::WriteTerm => clause_name!("$write_term"),
            &SystemClauseType::WriteTermToChars => clause_name!("$write_term_to_chars"),
            &SystemClauseType::ScryerPrologVersion => clause_name!("$scryer_prolog_version"),
            &SystemClauseType::CryptoRandomByte => clause_name!("$crypto_random_byte"),
            &SystemClauseType::CryptoDataHash => clause_name!("$crypto_data_hash"),
            &SystemClauseType::CryptoDataHKDF => clause_name!("$crypto_data_hkdf"),
            &SystemClauseType::CryptoPasswordHash => clause_name!("$crypto_password_hash"),
            &SystemClauseType::CryptoDataEncrypt => clause_name!("$crypto_data_encrypt"),
            &SystemClauseType::CryptoDataDecrypt => clause_name!("$crypto_data_decrypt"),
            &SystemClauseType::CryptoCurveScalarMult => clause_name!("$crypto_curve_scalar_mult"),
            &SystemClauseType::Ed25519Sign => clause_name!("$ed25519_sign"),
            &SystemClauseType::Ed25519Verify => clause_name!("$ed25519_verify"),
            &SystemClauseType::Ed25519NewKeyPair => clause_name!("$ed25519_new_keypair"),
            &SystemClauseType::Ed25519KeyPairPublicKey => {
                clause_name!("$ed25519_keypair_public_key")
            }
            &SystemClauseType::Curve25519ScalarMult => clause_name!("$curve25519_scalar_mult"),
            &SystemClauseType::LoadHTML => clause_name!("$load_html"),
            &SystemClauseType::LoadXML => clause_name!("$load_xml"),
            &SystemClauseType::GetEnv => clause_name!("$getenv"),
            &SystemClauseType::SetEnv => clause_name!("$setenv"),
            &SystemClauseType::UnsetEnv => clause_name!("$unsetenv"),
            &SystemClauseType::PID => clause_name!("$pid"),
            &SystemClauseType::CharsBase64 => clause_name!("$chars_base64"),
            &SystemClauseType::LoadLibraryAsStream => clause_name!("$load_library_as_stream"),
            &SystemClauseType::DevourWhitespace => clause_name!("$devour_whitespace"),
            &SystemClauseType::IsSTOEnabled => clause_name!("$is_sto_enabled"),
            &SystemClauseType::SetSTOAsUnify => clause_name!("$set_sto_as_unify"),
            &SystemClauseType::SetNSTOAsUnify => clause_name!("$set_nsto_as_unify"),
            &SystemClauseType::HomeDirectory => clause_name!("$home_directory"),
            &SystemClauseType::SetSTOWithErrorAsUnify => {
                clause_name!("$set_sto_with_error_as_unify")
            }
            &SystemClauseType::DebugHook => clause_name!("$debug_hook"),
            &SystemClauseType::PopCount => clause_name!("$popcount"),
        }
    }

    pub(crate) fn from(name: &str, arity: usize) -> Option<SystemClauseType> {
        match (name, arity) {
            ("$abolish_clause", 3) => Some(SystemClauseType::REPL(REPLCodePtr::AbolishClause)),
            ("$add_dynamic_predicate", 4) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddDynamicPredicate))
            }
            ("$add_multifile_predicate", 4) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddMultifilePredicate))
            }
            ("$add_discontiguous_predicate", 4) => Some(SystemClauseType::REPL(
                REPLCodePtr::AddDiscontiguousPredicate,
            )),
            ("$add_goal_expansion_clause", 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddGoalExpansionClause))
            }
            ("$add_term_expansion_clause", 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddTermExpansionClause))
            }
            ("$atom_chars", 2) => Some(SystemClauseType::AtomChars),
            ("$atom_codes", 2) => Some(SystemClauseType::AtomCodes),
            ("$atom_length", 2) => Some(SystemClauseType::AtomLength),
            ("$bind_from_register", 2) => Some(SystemClauseType::BindFromRegister),
            ("$call_continuation", 1) => Some(SystemClauseType::CallContinuation),
            ("$char_code", 2) => Some(SystemClauseType::CharCode),
            ("$char_type", 2) => Some(SystemClauseType::CharType),
            ("$chars_to_number", 2) => Some(SystemClauseType::CharsToNumber),
            ("$codes_to_number", 2) => Some(SystemClauseType::CodesToNumber),
            ("$copy_term_without_attr_vars", 2) => Some(SystemClauseType::CopyTermWithoutAttrVars),
            ("$create_partial_string", 3) => Some(SystemClauseType::CreatePartialString),
            ("$check_cp", 1) => Some(SystemClauseType::CheckCutPoint),
            ("$copy_to_lh", 2) => Some(SystemClauseType::CopyToLiftedHeap),
            ("$close", 2) => Some(SystemClauseType::Close),
            ("$current_hostname", 1) => Some(SystemClauseType::CurrentHostname),
            ("$current_input", 1) => Some(SystemClauseType::CurrentInput),
            ("$current_output", 1) => Some(SystemClauseType::CurrentOutput),
            ("$first_stream", 1) => Some(SystemClauseType::FirstStream),
            ("$next_stream", 2) => Some(SystemClauseType::NextStream),
            ("$flush_output", 1) => Some(SystemClauseType::FlushOutput),
            ("$del_attr_non_head", 1) => Some(SystemClauseType::DeleteAttribute),
            ("$del_attr_head", 1) => Some(SystemClauseType::DeleteHeadAttribute),
            ("$get_next_db_ref", 2) => Some(SystemClauseType::GetNextDBRef),
            ("$get_next_op_db_ref", 2) => Some(SystemClauseType::GetNextOpDBRef),
            ("$lookup_db_ref", 3) => Some(SystemClauseType::LookupDBRef),
            ("$lookup_op_db_ref", 4) => Some(SystemClauseType::LookupOpDBRef),
            ("$module_call", _) => Some(SystemClauseType::DynamicModuleResolution(arity - 2)),
            ("$enqueue_attr_var", 1) => Some(SystemClauseType::EnqueueAttributedVar),
            ("$partial_string_tail", 2) => Some(SystemClauseType::PartialStringTail),
            ("$peek_byte", 2) => Some(SystemClauseType::PeekByte),
            ("$peek_char", 2) => Some(SystemClauseType::PeekChar),
            ("$peek_code", 2) => Some(SystemClauseType::PeekCode),
            ("$is_partial_string", 1) => Some(SystemClauseType::IsPartialString),
            ("$fetch_global_var", 2) => Some(SystemClauseType::FetchGlobalVar),
            ("$get_byte", 2) => Some(SystemClauseType::GetByte),
            ("$get_char", 2) => Some(SystemClauseType::GetChar),
            ("$get_n_chars", 3) => Some(SystemClauseType::GetNChars),
            ("$get_code", 2) => Some(SystemClauseType::GetCode),
            ("$get_single_char", 1) => Some(SystemClauseType::GetSingleChar),
            ("$points_to_cont_reset_marker", 1) => {
                Some(SystemClauseType::PointsToContinuationResetMarker)
            }
            ("$put_byte", 2) => Some(SystemClauseType::PutByte),
            ("$put_char", 2) => Some(SystemClauseType::PutChar),
            ("$put_chars", 2) => Some(SystemClauseType::PutChars),
            ("$put_code", 2) => Some(SystemClauseType::PutCode),
            ("$reset_attr_var_state", 0) => Some(SystemClauseType::ResetAttrVarState),
            ("$truncate_if_no_lh_growth", 1) => {
                Some(SystemClauseType::TruncateIfNoLiftedHeapGrowth)
            }
            ("$truncate_if_no_lh_growth_diff", 2) => {
                Some(SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff)
            }
            ("$get_attr_list", 2) => Some(SystemClauseType::GetAttributedVariableList),
            ("$get_b_value", 1) => Some(SystemClauseType::GetBValue),
            ("$get_lh_from_offset", 2) => Some(SystemClauseType::GetLiftedHeapFromOffset),
            ("$get_lh_from_offset_diff", 3) => Some(SystemClauseType::GetLiftedHeapFromOffsetDiff),
            ("$get_double_quotes", 1) => Some(SystemClauseType::GetDoubleQuotes),
            ("$get_scc_cleaner", 1) => Some(SystemClauseType::GetSCCCleaner),
            ("$halt", 1) => Some(SystemClauseType::Halt),
            ("$head_is_dynamic", 2) => Some(SystemClauseType::HeadIsDynamic),
            ("$install_scc_cleaner", 2) => Some(SystemClauseType::InstallSCCCleaner),
            ("$install_inference_counter", 3) => Some(SystemClauseType::InstallInferenceCounter),
            ("$lh_length", 1) => Some(SystemClauseType::LiftedHeapLength),
            ("$maybe", 0) => Some(SystemClauseType::Maybe),
            ("$cpu_now", 1) => Some(SystemClauseType::CpuNow),
            ("$current_time", 1) => Some(SystemClauseType::CurrentTime),
            ("$module_exists", 1) => Some(SystemClauseType::ModuleExists),
            ("$no_such_predicate", 2) => Some(SystemClauseType::NoSuchPredicate),
            ("$number_to_chars", 2) => Some(SystemClauseType::NumberToChars),
            ("$number_to_codes", 2) => Some(SystemClauseType::NumberToCodes),
            ("$op", 3) => Some(SystemClauseType::OpDeclaration),
            ("$open", 7) => Some(SystemClauseType::Open),
            ("$redo_attr_var_binding", 2) => Some(SystemClauseType::RedoAttrVarBinding),
            ("$remove_call_policy_check", 1) => Some(SystemClauseType::RemoveCallPolicyCheck),
            ("$remove_inference_counter", 2) => Some(SystemClauseType::RemoveInferenceCounter),
            ("$restore_cut_policy", 0) => Some(SystemClauseType::RestoreCutPolicy),
            ("$set_cp", 1) => Some(SystemClauseType::SetCutPoint(temp_v!(1))),
            ("$set_input", 1) => Some(SystemClauseType::SetInput),
            ("$set_output", 1) => Some(SystemClauseType::SetOutput),
            ("$stream_property", 3) => Some(SystemClauseType::StreamProperty),
            ("$set_stream_position", 2) => Some(SystemClauseType::SetStreamPosition),
            ("$inference_level", 2) => Some(SystemClauseType::InferenceLevel),
            ("$clean_up_block", 1) => Some(SystemClauseType::CleanUpBlock),
            ("$erase_ball", 0) => Some(SystemClauseType::EraseBall),
            ("$fail", 0) => Some(SystemClauseType::Fail),
            ("$get_attr_var_queue_beyond", 2) => Some(SystemClauseType::GetAttrVarQueueBeyond),
            ("$get_attr_var_queue_delim", 1) => Some(SystemClauseType::GetAttrVarQueueDelimiter),
            ("$get_ball", 1) => Some(SystemClauseType::GetBall),
            ("$get_cont_chunk", 3) => Some(SystemClauseType::GetContinuationChunk),
            ("$get_current_block", 1) => Some(SystemClauseType::GetCurrentBlock),
            ("$get_cp", 1) => Some(SystemClauseType::GetCutPoint),
            ("$install_new_block", 1) => Some(SystemClauseType::InstallNewBlock),
            ("$quoted_token", 1) => Some(SystemClauseType::QuotedToken),
            ("$nextEP", 3) => Some(SystemClauseType::NextEP),
            ("$read_query_term", 5) => Some(SystemClauseType::ReadQueryTerm),
            ("$read_term", 5) => Some(SystemClauseType::ReadTerm),
            ("$read_term_from_chars", 2) => Some(SystemClauseType::ReadTermFromChars),
            ("$reset_block", 1) => Some(SystemClauseType::ResetBlock),
            ("$reset_cont_marker", 0) => Some(SystemClauseType::ResetContinuationMarker),
            ("$return_from_verify_attr", 0) => Some(SystemClauseType::ReturnFromVerifyAttr),
            ("$set_ball", 1) => Some(SystemClauseType::SetBall),
            ("$set_cp_by_default", 1) => Some(SystemClauseType::SetCutPointByDefault(temp_v!(1))),
            ("$set_double_quotes", 1) => Some(SystemClauseType::SetDoubleQuotes),
            ("$set_seed", 1) => Some(SystemClauseType::SetSeed),
            ("$skip_max_list", 4) => Some(SystemClauseType::SkipMaxList),
            ("$sleep", 1) => Some(SystemClauseType::Sleep),
            ("$socket_client_open", 8) => Some(SystemClauseType::SocketClientOpen),
            ("$socket_server_open", 3) => Some(SystemClauseType::SocketServerOpen),
            ("$socket_server_accept", 7) => Some(SystemClauseType::SocketServerAccept),
            ("$socket_server_close", 1) => Some(SystemClauseType::SocketServerClose),
            ("$store_global_var", 2) => Some(SystemClauseType::StoreGlobalVar),
            ("$store_backtrackable_global_var", 2) => {
                Some(SystemClauseType::StoreBacktrackableGlobalVar)
            }
            ("$term_attributed_variables", 2) => Some(SystemClauseType::TermAttributedVariables),
            ("$term_variables", 2) => Some(SystemClauseType::TermVariables),
            ("$truncate_lh_to", 1) => Some(SystemClauseType::TruncateLiftedHeapTo),
            ("$unwind_environments", 0) => Some(SystemClauseType::UnwindEnvironments),
            ("$unwind_stack", 0) => Some(SystemClauseType::UnwindStack),
            ("$unify_with_occurs_check", 2) => Some(SystemClauseType::UnifyWithOccursCheck),
            ("$directory_files", 2) => Some(SystemClauseType::DirectoryFiles),
            ("$file_size", 2) => Some(SystemClauseType::FileSize),
            ("$file_exists", 1) => Some(SystemClauseType::FileExists),
            ("$directory_exists", 1) => Some(SystemClauseType::DirectoryExists),
            ("$directory_separator", 1) => Some(SystemClauseType::DirectorySeparator),
            ("$make_directory", 1) => Some(SystemClauseType::MakeDirectory),
            ("$make_directory_path", 1) => Some(SystemClauseType::MakeDirectoryPath),
            ("$delete_file", 1) => Some(SystemClauseType::DeleteFile),
            ("$rename_file", 2) => Some(SystemClauseType::RenameFile),
            ("$delete_directory", 1) => Some(SystemClauseType::DeleteDirectory),
            ("$working_directory", 2) => Some(SystemClauseType::WorkingDirectory),
            ("$path_canonical", 2) => Some(SystemClauseType::PathCanonical),
            ("$file_time", 3) => Some(SystemClauseType::FileTime),
            ("$clause_to_evacuable", 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::ClauseToEvacuable))
            }
            ("$scoped_clause_to_evacuable", 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::ScopedClauseToEvacuable))
            }
            ("$conclude_load", 1) => Some(SystemClauseType::REPL(REPLCodePtr::ConcludeLoad)),
            ("$use_module", 3) => Some(SystemClauseType::REPL(REPLCodePtr::UseModule)),
            ("$declare_module", 3) => Some(SystemClauseType::REPL(REPLCodePtr::DeclareModule)),
            ("$load_compiled_library", 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadCompiledLibrary))
            }
            ("$push_load_state_payload", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::PushLoadStatePayload))
            }
            ("$add_in_situ_filename_module", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddInSituFilenameModule))
            }
            ("$asserta", 5) => Some(SystemClauseType::REPL(REPLCodePtr::Asserta)),
            ("$assertz", 5) => Some(SystemClauseType::REPL(REPLCodePtr::Assertz)),
            ("$retract_clause", 4) => Some(SystemClauseType::REPL(REPLCodePtr::Retract)),
            ("$is_consistent_with_term_queue", 4) => Some(SystemClauseType::REPL(
                REPLCodePtr::IsConsistentWithTermQueue,
            )),
            ("$flush_term_queue", 1) => Some(SystemClauseType::REPL(REPLCodePtr::FlushTermQueue)),
            ("$remove_module_exports", 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::RemoveModuleExports))
            }
            ("$add_non_counted_backtracking", 3) => Some(SystemClauseType::REPL(
                REPLCodePtr::AddNonCountedBacktracking,
            )),
            ("$variant", 2) => Some(SystemClauseType::Variant),
            ("$wam_instructions", 4) => Some(SystemClauseType::WAMInstructions),
            ("$write_term", 7) => Some(SystemClauseType::WriteTerm),
            ("$write_term_to_chars", 7) => Some(SystemClauseType::WriteTermToChars),
            ("$scryer_prolog_version", 1) => Some(SystemClauseType::ScryerPrologVersion),
            ("$crypto_random_byte", 1) => Some(SystemClauseType::CryptoRandomByte),
            ("$crypto_data_hash", 4) => Some(SystemClauseType::CryptoDataHash),
            ("$crypto_data_hkdf", 7) => Some(SystemClauseType::CryptoDataHKDF),
            ("$crypto_password_hash", 4) => Some(SystemClauseType::CryptoPasswordHash),
            ("$crypto_data_encrypt", 7) => Some(SystemClauseType::CryptoDataEncrypt),
            ("$crypto_data_decrypt", 6) => Some(SystemClauseType::CryptoDataDecrypt),
            ("$crypto_curve_scalar_mult", 5) => Some(SystemClauseType::CryptoCurveScalarMult),
            ("$ed25519_sign", 4) => Some(SystemClauseType::Ed25519Sign),
            ("$ed25519_verify", 4) => Some(SystemClauseType::Ed25519Verify),
            ("$ed25519_new_keypair", 1) => Some(SystemClauseType::Ed25519NewKeyPair),
            ("$ed25519_keypair_public_key", 2) => Some(SystemClauseType::Ed25519KeyPairPublicKey),
            ("$curve25519_scalar_mult", 3) => Some(SystemClauseType::Curve25519ScalarMult),
            ("$load_html", 3) => Some(SystemClauseType::LoadHTML),
            ("$load_xml", 3) => Some(SystemClauseType::LoadXML),
            ("$getenv", 2) => Some(SystemClauseType::GetEnv),
            ("$setenv", 2) => Some(SystemClauseType::SetEnv),
            ("$unsetenv", 1) => Some(SystemClauseType::UnsetEnv),
            ("$pid", 1) => Some(SystemClauseType::PID),
            ("$chars_base64", 4) => Some(SystemClauseType::CharsBase64),
            ("$load_library_as_stream", 3) => Some(SystemClauseType::LoadLibraryAsStream),
            ("$push_load_context", 2) => Some(SystemClauseType::REPL(REPLCodePtr::PushLoadContext)),
            ("$pop_load_state_payload", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::PopLoadStatePayload))
            }
            ("$pop_load_context", 0) => Some(SystemClauseType::REPL(REPLCodePtr::PopLoadContext)),
            ("$prolog_lc_source", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextSource))
            }
            ("$prolog_lc_file", 1) => Some(SystemClauseType::REPL(REPLCodePtr::LoadContextFile)),
            ("$prolog_lc_dir", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextDirectory))
            }
            ("$prolog_lc_module", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextModule))
            }
            ("$prolog_lc_stream", 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextStream))
            }
            ("$cpp_meta_predicate_property", 4) => {
                Some(SystemClauseType::REPL(REPLCodePtr::MetaPredicateProperty))
            }
            ("$cpp_built_in_property", 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::BuiltInProperty))
            }
            ("$cpp_dynamic_property", 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::DynamicProperty))
            }
            ("$cpp_multifile_property", 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::MultifileProperty))
            }
            ("$cpp_discontiguous_property", 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::DiscontiguousProperty))
            }
            ("$devour_whitespace", 1) => Some(SystemClauseType::DevourWhitespace),
            ("$is_sto_enabled", 1) => Some(SystemClauseType::IsSTOEnabled),
            ("$set_sto_as_unify", 0) => Some(SystemClauseType::SetSTOAsUnify),
            ("$set_nsto_as_unify", 0) => Some(SystemClauseType::SetNSTOAsUnify),
            ("$set_sto_with_error_as_unify", 0) => Some(SystemClauseType::SetSTOWithErrorAsUnify),
            ("$home_directory", 1) => Some(SystemClauseType::HomeDirectory),
            ("$debug_hook", 0) => Some(SystemClauseType::DebugHook),
            ("$popcount", 2) => Some(SystemClauseType::PopCount),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum BuiltInClauseType {
    AcyclicTerm,
    Arg,
    Compare,
    CompareTerm(CompareTermQT),
    CopyTerm,
    Eq,
    Functor,
    Ground,
    Is(RegType, ArithmeticTerm),
    KeySort,
    NotEq,
    Read,
    Sort,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ClauseType {
    BuiltIn(BuiltInClauseType),
    CallN,
    Inlined(InlinedClauseType),
    Named(ClauseName, usize, CodeIndex), // name, arity, index.
    Op(ClauseName, SharedOpDesc, CodeIndex),
    System(SystemClauseType),
}

impl BuiltInClauseType {
    pub(crate) fn name(&self) -> ClauseName {
        match self {
            &BuiltInClauseType::AcyclicTerm => clause_name!("acyclic_term"),
            &BuiltInClauseType::Arg => clause_name!("arg"),
            &BuiltInClauseType::Compare => clause_name!("compare"),
            &BuiltInClauseType::CompareTerm(qt) => clause_name!(qt.name()),
            &BuiltInClauseType::CopyTerm => clause_name!("copy_term"),
            &BuiltInClauseType::Eq => clause_name!("=="),
            &BuiltInClauseType::Functor => clause_name!("functor"),
            &BuiltInClauseType::Ground => clause_name!("ground"),
            &BuiltInClauseType::Is(..) => clause_name!("is"),
            &BuiltInClauseType::KeySort => clause_name!("keysort"),
            &BuiltInClauseType::NotEq => clause_name!("\\=="),
            &BuiltInClauseType::Read => clause_name!("read"),
            &BuiltInClauseType::Sort => clause_name!("sort"),
        }
    }

    pub(crate) fn arity(&self) -> usize {
        match self {
            &BuiltInClauseType::AcyclicTerm => 1,
            &BuiltInClauseType::Arg => 3,
            &BuiltInClauseType::Compare => 2,
            &BuiltInClauseType::CompareTerm(_) => 2,
            &BuiltInClauseType::CopyTerm => 2,
            &BuiltInClauseType::Eq => 2,
            &BuiltInClauseType::Functor => 3,
            &BuiltInClauseType::Ground => 1,
            &BuiltInClauseType::Is(..) => 2,
            &BuiltInClauseType::KeySort => 2,
            &BuiltInClauseType::NotEq => 2,
            &BuiltInClauseType::Read => 2,
            &BuiltInClauseType::Sort => 2,
        }
    }
}

impl ClauseType {
    pub(crate) fn spec(&self) -> Option<SharedOpDesc> {
        match self {
            &ClauseType::Op(_, ref spec, _) => Some(spec.clone()),
            &ClauseType::Inlined(InlinedClauseType::CompareNumber(..))
            | &ClauseType::BuiltIn(BuiltInClauseType::Is(..))
            | &ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(_))
            | &ClauseType::BuiltIn(BuiltInClauseType::NotEq)
            | &ClauseType::BuiltIn(BuiltInClauseType::Eq) => Some(SharedOpDesc::new(700, XFX)),
            _ => None,
        }
    }

    pub(crate) fn name(&self) -> ClauseName {
        match self {
            &ClauseType::BuiltIn(ref built_in) => built_in.name(),
            &ClauseType::CallN => clause_name!("$call"),
            &ClauseType::Inlined(ref inlined) => clause_name!(inlined.name()),
            &ClauseType::Op(ref name, ..) => name.clone(),
            &ClauseType::Named(ref name, ..) => name.clone(),
            &ClauseType::System(ref system) => system.name(),
        }
    }

    pub(crate) fn from(name: ClauseName, arity: usize, spec: Option<SharedOpDesc>) -> Self {
        CLAUSE_TYPE_FORMS
            .borrow()
            .get(&(name.as_str(), arity))
            .cloned()
            .unwrap_or_else(|| {
                SystemClauseType::from(name.as_str(), arity)
                    .map(ClauseType::System)
                    .unwrap_or_else(|| {
                        if let Some(spec) = spec {
                            ClauseType::Op(name, spec, CodeIndex::default())
                        } else if name.as_str() == "$call" {
                            ClauseType::CallN
                        } else {
                            ClauseType::Named(name, arity, CodeIndex::default())
                        }
                    })
            })
    }
}

impl From<InlinedClauseType> for ClauseType {
    fn from(inlined_ct: InlinedClauseType) -> Self {
        ClauseType::Inlined(inlined_ct)
    }
}
