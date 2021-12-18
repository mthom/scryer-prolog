use crate::atom_table::*;
use crate::machine::machine_indices::*;
use crate::parser::ast::*;
use crate::parser::rug::rand::RandState;

use crate::forms::Number;
use crate::temp_v;

use ref_thread_local::{ref_thread_local};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum CompareNumberQT {
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    NotEqual,
    Equal,
}

impl CompareNumberQT {
    fn name(self) -> Atom {
        match self {
            CompareNumberQT::GreaterThan => atom!(">"),
            CompareNumberQT::LessThan => atom!("<"),
            CompareNumberQT::GreaterThanOrEqual => atom!(">="),
            CompareNumberQT::LessThanOrEqual => atom!("=<"),
            CompareNumberQT::NotEqual => atom!("=\\="),
            CompareNumberQT::Equal => atom!("=:="),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareTermQT {
    LessThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    GreaterThan,
}

impl CompareTermQT {
    fn name(self) -> Atom {
        match self {
            CompareTermQT::GreaterThan => atom!("@>"),
            CompareTermQT::LessThan => atom!("@<"),
            CompareTermQT::GreaterThanOrEqual => atom!("@>="),
            CompareTermQT::LessThanOrEqual => atom!("@=<"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ArithmeticTerm {
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum InlinedClauseType {
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
    pub(crate) static managed RANDOM_STATE: RandState<'static> = RandState::new();
}

pub fn clause_type_form(name: Atom, arity: usize) -> Option<ClauseType> {
    match (name, arity) {
        (atom!(">"), 2) => Some(ClauseType::Inlined(InlinedClauseType::CompareNumber(
            CompareNumberQT::GreaterThan,
            ar_reg!(temp_v!(1)),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!("<"), 2) => Some(ClauseType::Inlined(InlinedClauseType::CompareNumber(
            CompareNumberQT::LessThan,
            ar_reg!(temp_v!(1)),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!(">="), 2) => Some(ClauseType::Inlined(InlinedClauseType::CompareNumber(
            CompareNumberQT::GreaterThanOrEqual,
            ar_reg!(temp_v!(1)),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!("=<"), 2) => Some(ClauseType::Inlined(InlinedClauseType::CompareNumber(
            CompareNumberQT::LessThanOrEqual,
            ar_reg!(temp_v!(1)),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!("=:="), 2) => Some(ClauseType::Inlined(InlinedClauseType::CompareNumber(
            CompareNumberQT::Equal,
            ar_reg!(temp_v!(1)),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!("=\\="), 2) => Some(ClauseType::Inlined(InlinedClauseType::CompareNumber(
            CompareNumberQT::NotEqual,
            ar_reg!(temp_v!(1)),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!("atom"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsAtom(temp_v!(1)))),
        (atom!("atomic"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsAtomic(temp_v!(1)))),
        (atom!("compound"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsCompound(temp_v!(
            1
        )))),
        (atom!("integer"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsInteger(temp_v!(
            1
        )))),
        (atom!("number"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsNumber(temp_v!(1)))),
        (atom!("rational"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsRational(temp_v!(
            1
        )))),
        (atom!("float"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsFloat(temp_v!(1)))),
        (atom!("nonvar"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsNonVar(temp_v!(1)))),
        (atom!("var"), 1) => Some(ClauseType::Inlined(InlinedClauseType::IsVar(temp_v!(1)))),
        (atom!("acyclic_term"), 1) => Some(ClauseType::BuiltIn(BuiltInClauseType::AcyclicTerm)),
        (atom!("arg"), 3) => Some(ClauseType::BuiltIn(BuiltInClauseType::Arg)),
        (atom!("compare"), 3) => Some(ClauseType::BuiltIn(BuiltInClauseType::Compare)),
        (atom!("@>"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(
            CompareTermQT::GreaterThan,
        ))),
        (atom!("@<"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(
            CompareTermQT::LessThan,
        ))),
        (atom!("@>="), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(
            CompareTermQT::GreaterThanOrEqual,
        ))),
        (atom!("@=<"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(
            CompareTermQT::LessThanOrEqual,
        ))),
        (atom!("copy_term"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::CopyTerm)),
        (atom!("=="), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::Eq)),
        (atom!("functor"), 3) => Some(ClauseType::BuiltIn(BuiltInClauseType::Functor)),
        (atom!("ground"), 1) => Some(ClauseType::BuiltIn(BuiltInClauseType::Ground)),
        (atom!("is"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::Is(
            temp_v!(1),
            ar_reg!(temp_v!(2)),
        ))),
        (atom!("keysort"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::KeySort)),
        (atom!("\\=="), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::NotEq)),
        (atom!("read"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::Read)),
        (atom!("sort"), 2) => Some(ClauseType::BuiltIn(BuiltInClauseType::Sort)),
        _ => None,
    }
}

impl InlinedClauseType {
    pub(crate) fn name(&self) -> Atom {
        match self {
            &InlinedClauseType::CompareNumber(qt, ..) => qt.name(),
            &InlinedClauseType::IsAtom(..) => atom!("atom"),
            &InlinedClauseType::IsAtomic(..) => atom!("atomic"),
            &InlinedClauseType::IsCompound(..) => atom!("compound"),
            &InlinedClauseType::IsNumber(..) => atom!("number"),
            &InlinedClauseType::IsInteger(..) => atom!("integer"),
            &InlinedClauseType::IsRational(..) => atom!("rational"),
            &InlinedClauseType::IsFloat(..) => atom!("float"),
            &InlinedClauseType::IsNonVar(..) => atom!("nonvar"),
            &InlinedClauseType::IsVar(..) => atom!("var"),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum SystemClauseType {
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
    WorkingDirectory,
    DeleteDirectory,
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
    SetStreamOptions,
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
    GetStaggeredCutPoint,
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
    TLSAcceptClient,
    TLSClientConnect,
    Succeed,
    TermAttributedVariables,
    TermVariables,
    TermVariablesUnderMaxDepth,
    TruncateLiftedHeapTo,
    UnifyWithOccursCheck,
    UnwindEnvironments,
    UnwindStack,
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
    FirstNonOctet,
    LoadHTML,
    LoadXML,
    GetEnv,
    SetEnv,
    UnsetEnv,
    Shell,
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
    pub(crate) fn name(&self) -> Atom {
        match self {
            &SystemClauseType::AtomChars => atom!("$atom_chars"),
            &SystemClauseType::AtomCodes => atom!("$atom_codes"),
            &SystemClauseType::AtomLength => atom!("$atom_length"),
            &SystemClauseType::BindFromRegister => atom!("$bind_from_register"),
            &SystemClauseType::CallContinuation => atom!("$call_continuation"),
            &SystemClauseType::CharCode => atom!("$char_code"),
            &SystemClauseType::CharType => atom!("$char_type"),
            &SystemClauseType::CharsToNumber => atom!("$chars_to_number"),
            &SystemClauseType::CheckCutPoint => atom!("$check_cp"),
            &SystemClauseType::CodesToNumber => atom!("$codes_to_number"),
            &SystemClauseType::CopyTermWithoutAttrVars => {
                atom!("$copy_term_without_attr_vars")
            }
            &SystemClauseType::CreatePartialString => atom!("$create_partial_string"),
            &SystemClauseType::CurrentInput => atom!("$current_input"),
            &SystemClauseType::CurrentHostname => atom!("$current_hostname"),
            &SystemClauseType::CurrentOutput => atom!("$current_output"),
            &SystemClauseType::DirectoryFiles => atom!("$directory_files"),
            &SystemClauseType::FileSize => atom!("$file_size"),
            &SystemClauseType::FileExists => atom!("$file_exists"),
            &SystemClauseType::DirectoryExists => atom!("$directory_exists"),
            &SystemClauseType::DirectorySeparator => atom!("$directory_separator"),
            &SystemClauseType::MakeDirectory => atom!("$make_directory"),
            &SystemClauseType::MakeDirectoryPath => atom!("$make_directory_path"),
            &SystemClauseType::DeleteFile => atom!("$delete_file"),
            &SystemClauseType::RenameFile => atom!("$rename_file"),
            &SystemClauseType::DeleteDirectory => atom!("$delete_directory"),
            &SystemClauseType::WorkingDirectory => atom!("$working_directory"),
            &SystemClauseType::PathCanonical => atom!("$path_canonical"),
            &SystemClauseType::FileTime => atom!("$file_time"),
            &SystemClauseType::REPL(REPLCodePtr::AddDiscontiguousPredicate) => {
                atom!("$add_discontiguous_predicate")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddDynamicPredicate) => atom!("$add_dynamic_predicate"),
            &SystemClauseType::REPL(REPLCodePtr::AddMultifilePredicate) => {
                atom!("$add_multifile_predicate")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddGoalExpansionClause) => {
                atom!("$add_goal_expansion_clause")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddTermExpansionClause) => {
                atom!("$add_term_expansion_clause")
            }
            &SystemClauseType::REPL(REPLCodePtr::ClauseToEvacuable) => atom!("$clause_to_evacuable"),
            &SystemClauseType::REPL(REPLCodePtr::ScopedClauseToEvacuable) => {
                atom!("$scoped_clause_to_evacuable")
            }
            &SystemClauseType::REPL(REPLCodePtr::ConcludeLoad) => atom!("$conclude_load"),
            &SystemClauseType::REPL(REPLCodePtr::DeclareModule) => atom!("$declare_module"),
            &SystemClauseType::REPL(REPLCodePtr::LoadCompiledLibrary) => atom!("$load_compiled_library"),
            &SystemClauseType::REPL(REPLCodePtr::PushLoadStatePayload) => {
                atom!("$push_load_state_payload")
            }
            &SystemClauseType::REPL(REPLCodePtr::AddInSituFilenameModule) => {
                atom!("$add_in_situ_filename_module")
            }
            &SystemClauseType::REPL(REPLCodePtr::Asserta) => atom!("$asserta"),
            &SystemClauseType::REPL(REPLCodePtr::Assertz) => atom!("$assertz"),
            &SystemClauseType::REPL(REPLCodePtr::Retract) => atom!("$retract_clause"),
            &SystemClauseType::REPL(REPLCodePtr::UseModule) => atom!("$use_module"),
            &SystemClauseType::REPL(REPLCodePtr::PushLoadContext) => atom!("$push_load_context"),
            &SystemClauseType::REPL(REPLCodePtr::PopLoadContext) => atom!("$pop_load_context"),
            &SystemClauseType::REPL(REPLCodePtr::PopLoadStatePayload) => atom!("$pop_load_state_payload"),
            &SystemClauseType::REPL(REPLCodePtr::LoadContextSource) => atom!("$prolog_lc_source"),
            &SystemClauseType::REPL(REPLCodePtr::LoadContextFile) => atom!("$prolog_lc_file"),
            &SystemClauseType::REPL(REPLCodePtr::LoadContextDirectory) => atom!("$prolog_lc_dir"),
            &SystemClauseType::REPL(REPLCodePtr::LoadContextModule) => atom!("$prolog_lc_module"),
            &SystemClauseType::REPL(REPLCodePtr::LoadContextStream) => atom!("$prolog_lc_stream"),
            &SystemClauseType::REPL(REPLCodePtr::MetaPredicateProperty) => {
                atom!("$cpp_meta_predicate_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::BuiltInProperty) => atom!("$cpp_built_in_property"),
            &SystemClauseType::REPL(REPLCodePtr::DynamicProperty) => atom!("$cpp_dynamic_property"),
            &SystemClauseType::REPL(REPLCodePtr::MultifileProperty) => atom!("$cpp_multifile_property"),
            &SystemClauseType::REPL(REPLCodePtr::DiscontiguousProperty) => {
                atom!("$cpp_discontiguous_property")
            }
            &SystemClauseType::REPL(REPLCodePtr::AbolishClause) => atom!("$abolish_clause"),
            &SystemClauseType::REPL(REPLCodePtr::IsConsistentWithTermQueue) => {
                atom!("$is_consistent_with_term_queue")
            }
            &SystemClauseType::REPL(REPLCodePtr::FlushTermQueue) => atom!("$flush_term_queue"),
            &SystemClauseType::REPL(REPLCodePtr::RemoveModuleExports) => atom!("$remove_module_exports"),
            &SystemClauseType::REPL(REPLCodePtr::AddNonCountedBacktracking) => {
                atom!("$add_non_counted_backtracking")
            }
            &SystemClauseType::Close => atom!("$close"),
            &SystemClauseType::CopyToLiftedHeap => atom!("$copy_to_lh"),
            &SystemClauseType::DeleteAttribute => atom!("$del_attr_non_head"),
            &SystemClauseType::DeleteHeadAttribute => atom!("$del_attr_head"),
            &SystemClauseType::DynamicModuleResolution(_) => atom!("$module_call"),
            &SystemClauseType::EnqueueAttributedVar => atom!("$enqueue_attr_var"),
            &SystemClauseType::FetchGlobalVar => atom!("$fetch_global_var"),
            &SystemClauseType::FirstStream => atom!("$first_stream"),
            &SystemClauseType::FlushOutput => atom!("$flush_output"),
            &SystemClauseType::GetByte => atom!("$get_byte"),
            &SystemClauseType::GetChar => atom!("$get_char"),
            &SystemClauseType::GetNChars => atom!("$get_n_chars"),
            &SystemClauseType::GetCode => atom!("$get_code"),
            &SystemClauseType::GetSingleChar => atom!("$get_single_char"),
            &SystemClauseType::ResetAttrVarState => atom!("$reset_attr_var_state"),
            &SystemClauseType::TruncateIfNoLiftedHeapGrowth => atom!("$truncate_if_no_lh_growth"),
            &SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff => atom!("$truncate_if_no_lh_growth_diff"),
            &SystemClauseType::GetAttributedVariableList => atom!("$get_attr_list"),
            &SystemClauseType::GetAttrVarQueueDelimiter => atom!("$get_attr_var_queue_delim"),
            &SystemClauseType::GetAttrVarQueueBeyond => atom!("$get_attr_var_queue_beyond"),
            &SystemClauseType::GetContinuationChunk => atom!("$get_cont_chunk"),
            &SystemClauseType::GetLiftedHeapFromOffset => atom!("$get_lh_from_offset"),
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => atom!("$get_lh_from_offset_diff"),
            &SystemClauseType::GetBValue => atom!("$get_b_value"),
            &SystemClauseType::GetNextDBRef => atom!("$get_next_db_ref"),
            &SystemClauseType::GetNextOpDBRef => atom!("$get_next_op_db_ref"),
            &SystemClauseType::GetDoubleQuotes => atom!("$get_double_quotes"),
            &SystemClauseType::GetSCCCleaner => atom!("$get_scc_cleaner"),
            &SystemClauseType::Halt => atom!("$halt"),
            &SystemClauseType::HeadIsDynamic => atom!("$head_is_dynamic"),
            &SystemClauseType::Open => atom!("$open"),
            &SystemClauseType::OpDeclaration => atom!("$op"),
            &SystemClauseType::InstallSCCCleaner => atom!("$install_scc_cleaner"),
            &SystemClauseType::InstallInferenceCounter => atom!("$install_inference_counter"),
            &SystemClauseType::IsPartialString => atom!("$is_partial_string"),
            &SystemClauseType::PartialStringTail => atom!("$partial_string_tail"),
            &SystemClauseType::PeekByte => atom!("$peek_byte"),
            &SystemClauseType::PeekChar => atom!("$peek_char"),
            &SystemClauseType::PeekCode => atom!("$peek_code"),
            &SystemClauseType::LiftedHeapLength => atom!("$lh_length"),
            &SystemClauseType::Maybe => atom!("maybe"),
            &SystemClauseType::CpuNow => atom!("$cpu_now"),
            &SystemClauseType::CurrentTime => atom!("$current_time"),
            &SystemClauseType::ModuleExists => atom!("$module_exists"),
            &SystemClauseType::NextStream => atom!("$next_stream"),
            &SystemClauseType::NoSuchPredicate => atom!("$no_such_predicate"),
            &SystemClauseType::NumberToChars => atom!("$number_to_chars"),
            &SystemClauseType::NumberToCodes => atom!("$number_to_codes"),
            &SystemClauseType::PointsToContinuationResetMarker => {
                atom!("$points_to_cont_reset_marker")
            }
            &SystemClauseType::PutByte => {
                atom!("$put_byte")
            }
            &SystemClauseType::PutChar => {
                atom!("$put_char")
            }
            &SystemClauseType::PutChars => {
                atom!("$put_chars")
            }
            &SystemClauseType::PutCode => {
                atom!("$put_code")
            }
            &SystemClauseType::QuotedToken => {
                atom!("$quoted_token")
            }
            &SystemClauseType::RedoAttrVarBinding => atom!("$redo_attr_var_binding"),
            &SystemClauseType::RemoveCallPolicyCheck => atom!("$remove_call_policy_check"),
            &SystemClauseType::RemoveInferenceCounter => atom!("$remove_inference_counter"),
            &SystemClauseType::RestoreCutPolicy => atom!("$restore_cut_policy"),
            &SystemClauseType::SetCutPoint(_) => atom!("$set_cp"),
            &SystemClauseType::SetInput => atom!("$set_input"),
            &SystemClauseType::SetOutput => atom!("$set_output"),
            &SystemClauseType::SetSeed => atom!("$set_seed"),
            &SystemClauseType::StreamProperty => atom!("$stream_property"),
            &SystemClauseType::SetStreamPosition => atom!("$set_stream_position"),
            &SystemClauseType::SetStreamOptions => atom!("$set_stream_options"),
            &SystemClauseType::StoreBacktrackableGlobalVar => {
                atom!("$store_back_trackable_global_var")
            }
            &SystemClauseType::StoreGlobalVar => atom!("$store_global_var"),
            &SystemClauseType::InferenceLevel => atom!("$inference_level"),
            &SystemClauseType::CleanUpBlock => atom!("$clean_up_block"),
            &SystemClauseType::EraseBall => atom!("$erase_ball"),
            &SystemClauseType::Fail => atom!("$fail"),
            &SystemClauseType::GetBall => atom!("$get_ball"),
            &SystemClauseType::GetCutPoint => atom!("$get_cp"),
            &SystemClauseType::GetStaggeredCutPoint => atom!("$get_staggered_cp"),
            &SystemClauseType::GetCurrentBlock => atom!("$get_current_block"),
            &SystemClauseType::InstallNewBlock => atom!("$install_new_block"),
            &SystemClauseType::NextEP => atom!("$nextEP"),
            &SystemClauseType::ReadQueryTerm => atom!("$read_query_term"),
            &SystemClauseType::ReadTerm => atom!("$read_term"),
            &SystemClauseType::ReadTermFromChars => atom!("$read_term_from_chars"),
            &SystemClauseType::ResetBlock => atom!("$reset_block"),
            &SystemClauseType::ResetContinuationMarker => atom!("$reset_cont_marker"),
            &SystemClauseType::ReturnFromVerifyAttr => atom!("$return_from_verify_attr"),
            &SystemClauseType::SetBall => atom!("$set_ball"),
            &SystemClauseType::SetCutPointByDefault(_) => atom!("$set_cp_by_default"),
            &SystemClauseType::SetDoubleQuotes => atom!("$set_double_quotes"),
            &SystemClauseType::SkipMaxList => atom!("$skip_max_list"),
            &SystemClauseType::Sleep => atom!("$sleep"),
            &SystemClauseType::SocketClientOpen => atom!("$socket_client_open"),
            &SystemClauseType::SocketServerOpen => atom!("$socket_server_open"),
            &SystemClauseType::SocketServerAccept => atom!("$socket_server_accept"),
            &SystemClauseType::SocketServerClose => atom!("$socket_server_close"),
            &SystemClauseType::TLSAcceptClient => atom!("$tls_accept_client"),
            &SystemClauseType::TLSClientConnect => atom!("$tls_client_connect"),
            &SystemClauseType::Succeed => atom!("$succeed"),
            &SystemClauseType::TermAttributedVariables => {
                atom!("$term_attributed_variables")
            }
            &SystemClauseType::TermVariables => atom!("$term_variables"),
            &SystemClauseType::TermVariablesUnderMaxDepth => atom!("$term_variables_under_max_depth"),
            &SystemClauseType::TruncateLiftedHeapTo => atom!("$truncate_lh_to"),
            &SystemClauseType::UnifyWithOccursCheck => atom!("$unify_with_occurs_check"),
            &SystemClauseType::UnwindEnvironments => atom!("$unwind_environments"),
            &SystemClauseType::UnwindStack => atom!("$unwind_stack"),
            &SystemClauseType::WAMInstructions => atom!("$wam_instructions"),
            &SystemClauseType::WriteTerm => atom!("$write_term"),
            &SystemClauseType::WriteTermToChars => atom!("$write_term_to_chars"),
            &SystemClauseType::ScryerPrologVersion => atom!("$scryer_prolog_version"),
            &SystemClauseType::CryptoRandomByte => atom!("$crypto_random_byte"),
            &SystemClauseType::CryptoDataHash => atom!("$crypto_data_hash"),
            &SystemClauseType::CryptoDataHKDF => atom!("$crypto_data_hkdf"),
            &SystemClauseType::CryptoPasswordHash => atom!("$crypto_password_hash"),
            &SystemClauseType::CryptoDataEncrypt => atom!("$crypto_data_encrypt"),
            &SystemClauseType::CryptoDataDecrypt => atom!("$crypto_data_decrypt"),
            &SystemClauseType::CryptoCurveScalarMult => atom!("$crypto_curve_scalar_mult"),
            &SystemClauseType::Ed25519Sign => atom!("$ed25519_sign"),
            &SystemClauseType::Ed25519Verify => atom!("$ed25519_verify"),
            &SystemClauseType::Ed25519NewKeyPair => atom!("$ed25519_new_keypair"),
            &SystemClauseType::Ed25519KeyPairPublicKey => {
                atom!("$ed25519_keypair_public_key")
            }
            &SystemClauseType::Curve25519ScalarMult => atom!("$curve25519_scalar_mult"),
            &SystemClauseType::FirstNonOctet => atom!("$first_non_octet"),
            &SystemClauseType::LoadHTML => atom!("$load_html"),
            &SystemClauseType::LoadXML => atom!("$load_xml"),
            &SystemClauseType::GetEnv => atom!("$getenv"),
            &SystemClauseType::SetEnv => atom!("$setenv"),
            &SystemClauseType::UnsetEnv => atom!("$unsetenv"),
            &SystemClauseType::Shell => atom!("$shell"),
            &SystemClauseType::PID => atom!("$pid"),
            &SystemClauseType::CharsBase64 => atom!("$chars_base64"),
            &SystemClauseType::LoadLibraryAsStream => atom!("$load_library_as_stream"),
            &SystemClauseType::DevourWhitespace => atom!("$devour_whitespace"),
            &SystemClauseType::IsSTOEnabled => atom!("$is_sto_enabled"),
            &SystemClauseType::SetSTOAsUnify => atom!("$set_sto_as_unify"),
            &SystemClauseType::SetNSTOAsUnify => atom!("$set_nsto_as_unify"),
            &SystemClauseType::HomeDirectory => atom!("$home_directory"),
            &SystemClauseType::SetSTOWithErrorAsUnify => {
                atom!("$set_sto_with_error_as_unify")
            }
            &SystemClauseType::DebugHook => atom!("$debug_hook"),
            &SystemClauseType::PopCount => atom!("$popcount"),
        }
    }

    pub(crate) fn from(name: Atom, arity: usize) -> Option<SystemClauseType> {
        match (name, arity) {
            (atom!("$abolish_clause"), 3) => Some(SystemClauseType::REPL(REPLCodePtr::AbolishClause)),
            (atom!("$add_dynamic_predicate"), 4) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddDynamicPredicate))
            }
            (atom!("$add_multifile_predicate"), 4) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddMultifilePredicate))
            }
            (atom!("$add_discontiguous_predicate"), 4) => Some(SystemClauseType::REPL(
                REPLCodePtr::AddDiscontiguousPredicate,
            )),
            (atom!("$add_goal_expansion_clause"), 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddGoalExpansionClause))
            }
            (atom!("$add_term_expansion_clause"), 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddTermExpansionClause))
            }
            (atom!("$atom_chars"), 2) => Some(SystemClauseType::AtomChars),
            (atom!("$atom_codes"), 2) => Some(SystemClauseType::AtomCodes),
            (atom!("$atom_length"), 2) => Some(SystemClauseType::AtomLength),
            (atom!("$bind_from_register"), 2) => Some(SystemClauseType::BindFromRegister),
            (atom!("$call_continuation"), 1) => Some(SystemClauseType::CallContinuation),
            (atom!("$char_code"), 2) => Some(SystemClauseType::CharCode),
            (atom!("$char_type"), 2) => Some(SystemClauseType::CharType),
            (atom!("$chars_to_number"), 2) => Some(SystemClauseType::CharsToNumber),
            (atom!("$codes_to_number"), 2) => Some(SystemClauseType::CodesToNumber),
            (atom!("$copy_term_without_attr_vars"), 2) => Some(SystemClauseType::CopyTermWithoutAttrVars),
            (atom!("$create_partial_string"), 3) => Some(SystemClauseType::CreatePartialString),
            (atom!("$check_cp"), 1) => Some(SystemClauseType::CheckCutPoint),
            (atom!("$copy_to_lh"), 2) => Some(SystemClauseType::CopyToLiftedHeap),
            (atom!("$close"), 2) => Some(SystemClauseType::Close),
            (atom!("$current_hostname"), 1) => Some(SystemClauseType::CurrentHostname),
            (atom!("$current_input"), 1) => Some(SystemClauseType::CurrentInput),
            (atom!("$current_output"), 1) => Some(SystemClauseType::CurrentOutput),
            (atom!("$first_stream"), 1) => Some(SystemClauseType::FirstStream),
            (atom!("$next_stream"), 2) => Some(SystemClauseType::NextStream),
            (atom!("$flush_output"), 1) => Some(SystemClauseType::FlushOutput),
            (atom!("$del_attr_non_head"), 1) => Some(SystemClauseType::DeleteAttribute),
            (atom!("$del_attr_head"), 1) => Some(SystemClauseType::DeleteHeadAttribute),
            (atom!("$get_next_db_ref"), 4) => Some(SystemClauseType::GetNextDBRef),
            (atom!("$get_next_op_db_ref"), 7) => Some(SystemClauseType::GetNextOpDBRef),
            (atom!("$module_call"), _) => Some(SystemClauseType::DynamicModuleResolution(arity - 2)),
            (atom!("$enqueue_attr_var"), 1) => Some(SystemClauseType::EnqueueAttributedVar),
            (atom!("$partial_string_tail"), 2) => Some(SystemClauseType::PartialStringTail),
            (atom!("$peek_byte"), 2) => Some(SystemClauseType::PeekByte),
            (atom!("$peek_char"), 2) => Some(SystemClauseType::PeekChar),
            (atom!("$peek_code"), 2) => Some(SystemClauseType::PeekCode),
            (atom!("$is_partial_string"), 1) => Some(SystemClauseType::IsPartialString),
            (atom!("$fetch_global_var"), 2) => Some(SystemClauseType::FetchGlobalVar),
            (atom!("$get_byte"), 2) => Some(SystemClauseType::GetByte),
            (atom!("$get_char"), 2) => Some(SystemClauseType::GetChar),
            (atom!("$get_n_chars"), 3) => Some(SystemClauseType::GetNChars),
            (atom!("$get_code"), 2) => Some(SystemClauseType::GetCode),
            (atom!("$get_single_char"), 1) => Some(SystemClauseType::GetSingleChar),
            (atom!("$points_to_cont_reset_marker"), 1) => {
                Some(SystemClauseType::PointsToContinuationResetMarker)
            }
            (atom!("$put_byte"), 2) => Some(SystemClauseType::PutByte),
            (atom!("$put_char"), 2) => Some(SystemClauseType::PutChar),
            (atom!("$put_chars"), 2) => Some(SystemClauseType::PutChars),
            (atom!("$put_code"), 2) => Some(SystemClauseType::PutCode),
            (atom!("$reset_attr_var_state"), 0) => Some(SystemClauseType::ResetAttrVarState),
            (atom!("$truncate_if_no_lh_growth"), 1) => {
                Some(SystemClauseType::TruncateIfNoLiftedHeapGrowth)
            }
            (atom!("$truncate_if_no_lh_growth_diff"), 2) => {
                Some(SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff)
            }
            (atom!("$get_attr_list"), 2) => Some(SystemClauseType::GetAttributedVariableList),
            (atom!("$get_b_value"), 1) => Some(SystemClauseType::GetBValue),
            (atom!("$get_lh_from_offset"), 2) => Some(SystemClauseType::GetLiftedHeapFromOffset),
            (atom!("$get_lh_from_offset_diff"), 3) => Some(SystemClauseType::GetLiftedHeapFromOffsetDiff),
            (atom!("$get_double_quotes"), 1) => Some(SystemClauseType::GetDoubleQuotes),
            (atom!("$get_scc_cleaner"), 1) => Some(SystemClauseType::GetSCCCleaner),
            (atom!("$halt"), 1) => Some(SystemClauseType::Halt),
            (atom!("$head_is_dynamic"), 2) => Some(SystemClauseType::HeadIsDynamic),
            (atom!("$install_scc_cleaner"), 2) => Some(SystemClauseType::InstallSCCCleaner),
            (atom!("$install_inference_counter"), 3) => Some(SystemClauseType::InstallInferenceCounter),
            (atom!("$lh_length"), 1) => Some(SystemClauseType::LiftedHeapLength),
            (atom!("$maybe"), 0) => Some(SystemClauseType::Maybe),
            (atom!("$cpu_now"), 1) => Some(SystemClauseType::CpuNow),
            (atom!("$current_time"), 1) => Some(SystemClauseType::CurrentTime),
            (atom!("$module_exists"), 1) => Some(SystemClauseType::ModuleExists),
            (atom!("$no_such_predicate"), 2) => Some(SystemClauseType::NoSuchPredicate),
            (atom!("$number_to_chars"), 2) => Some(SystemClauseType::NumberToChars),
            (atom!("$number_to_codes"), 2) => Some(SystemClauseType::NumberToCodes),
            (atom!("$op"), 3) => Some(SystemClauseType::OpDeclaration),
            (atom!("$open"), 7) => Some(SystemClauseType::Open),
            (atom!("$set_stream_options"), 5) => Some(SystemClauseType::SetStreamOptions),
            (atom!("$redo_attr_var_binding"), 2) => Some(SystemClauseType::RedoAttrVarBinding),
            (atom!("$remove_call_policy_check"), 1) => Some(SystemClauseType::RemoveCallPolicyCheck),
            (atom!("$remove_inference_counter"), 2) => Some(SystemClauseType::RemoveInferenceCounter),
            (atom!("$restore_cut_policy"), 0) => Some(SystemClauseType::RestoreCutPolicy),
            (atom!("$set_cp"), 1) => Some(SystemClauseType::SetCutPoint(temp_v!(1))),
            (atom!("$set_input"), 1) => Some(SystemClauseType::SetInput),
            (atom!("$set_output"), 1) => Some(SystemClauseType::SetOutput),
            (atom!("$stream_property"), 3) => Some(SystemClauseType::StreamProperty),
            (atom!("$set_stream_position"), 2) => Some(SystemClauseType::SetStreamPosition),
            (atom!("$inference_level"), 2) => Some(SystemClauseType::InferenceLevel),
            (atom!("$clean_up_block"), 1) => Some(SystemClauseType::CleanUpBlock),
            (atom!("$erase_ball"), 0) => Some(SystemClauseType::EraseBall),
            (atom!("$fail"), 0) => Some(SystemClauseType::Fail),
            (atom!("$get_attr_var_queue_beyond"), 2) => Some(SystemClauseType::GetAttrVarQueueBeyond),
            (atom!("$get_attr_var_queue_delim"), 1) => Some(SystemClauseType::GetAttrVarQueueDelimiter),
            (atom!("$get_ball"), 1) => Some(SystemClauseType::GetBall),
            (atom!("$get_cont_chunk"), 3) => Some(SystemClauseType::GetContinuationChunk),
            (atom!("$get_current_block"), 1) => Some(SystemClauseType::GetCurrentBlock),
            (atom!("$get_cp"), 1) => Some(SystemClauseType::GetCutPoint),
            (atom!("$get_staggered_cp"), 1) => Some(SystemClauseType::GetStaggeredCutPoint),
            (atom!("$install_new_block"), 1) => Some(SystemClauseType::InstallNewBlock),
            (atom!("$quoted_token"), 1) => Some(SystemClauseType::QuotedToken),
            (atom!("$nextEP"), 3) => Some(SystemClauseType::NextEP),
            (atom!("$read_query_term"), 5) => Some(SystemClauseType::ReadQueryTerm),
            (atom!("$read_term"), 5) => Some(SystemClauseType::ReadTerm),
            (atom!("$read_term_from_chars"), 2) => Some(SystemClauseType::ReadTermFromChars),
            (atom!("$reset_block"), 1) => Some(SystemClauseType::ResetBlock),
            (atom!("$reset_cont_marker"), 0) => Some(SystemClauseType::ResetContinuationMarker),
            (atom!("$return_from_verify_attr"), 0) => Some(SystemClauseType::ReturnFromVerifyAttr),
            (atom!("$set_ball"), 1) => Some(SystemClauseType::SetBall),
            (atom!("$set_cp_by_default"), 1) => Some(SystemClauseType::SetCutPointByDefault(temp_v!(1))),
            (atom!("$set_double_quotes"), 1) => Some(SystemClauseType::SetDoubleQuotes),
            (atom!("$set_seed"), 1) => Some(SystemClauseType::SetSeed),
            (atom!("$skip_max_list"), 4) => Some(SystemClauseType::SkipMaxList),
            (atom!("$sleep"), 1) => Some(SystemClauseType::Sleep),
            (atom!("$tls_accept_client"), 4) => Some(SystemClauseType::TLSAcceptClient),
            (atom!("$tls_client_connect"), 3) => Some(SystemClauseType::TLSClientConnect),
            (atom!("$socket_client_open"), 8) => Some(SystemClauseType::SocketClientOpen),
            (atom!("$socket_server_open"), 3) => Some(SystemClauseType::SocketServerOpen),
            (atom!("$socket_server_accept"), 7) => Some(SystemClauseType::SocketServerAccept),
            (atom!("$socket_server_close"), 1) => Some(SystemClauseType::SocketServerClose),
            (atom!("$store_global_var"), 2) => Some(SystemClauseType::StoreGlobalVar),
            (atom!("$store_backtrackable_global_var"), 2) => {
                Some(SystemClauseType::StoreBacktrackableGlobalVar)
            }
            (atom!("$term_attributed_variables"), 2) => Some(SystemClauseType::TermAttributedVariables),
            (atom!("$term_variables"), 2) => Some(SystemClauseType::TermVariables),
            (atom!("$term_variables_under_max_depth"), 3) => Some(SystemClauseType::TermVariablesUnderMaxDepth),
            (atom!("$truncate_lh_to"), 1) => Some(SystemClauseType::TruncateLiftedHeapTo),
            (atom!("$unwind_environments"), 0) => Some(SystemClauseType::UnwindEnvironments),
            (atom!("$unwind_stack"), 0) => Some(SystemClauseType::UnwindStack),
            (atom!("$unify_with_occurs_check"), 2) => Some(SystemClauseType::UnifyWithOccursCheck),
            (atom!("$directory_files"), 2) => Some(SystemClauseType::DirectoryFiles),
            (atom!("$file_size"), 2) => Some(SystemClauseType::FileSize),
            (atom!("$file_exists"), 1) => Some(SystemClauseType::FileExists),
            (atom!("$directory_exists"), 1) => Some(SystemClauseType::DirectoryExists),
            (atom!("$directory_separator"), 1) => Some(SystemClauseType::DirectorySeparator),
            (atom!("$make_directory"), 1) => Some(SystemClauseType::MakeDirectory),
            (atom!("$make_directory_path"), 1) => Some(SystemClauseType::MakeDirectoryPath),
            (atom!("$delete_file"), 1) => Some(SystemClauseType::DeleteFile),
            (atom!("$rename_file"), 2) => Some(SystemClauseType::RenameFile),
            (atom!("$delete_directory"), 1) => Some(SystemClauseType::DeleteDirectory),
            (atom!("$working_directory"), 2) => Some(SystemClauseType::WorkingDirectory),
            (atom!("$path_canonical"), 2) => Some(SystemClauseType::PathCanonical),
            (atom!("$file_time"), 3) => Some(SystemClauseType::FileTime),
            (atom!("$clause_to_evacuable"), 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::ClauseToEvacuable))
            }
            (atom!("$scoped_clause_to_evacuable"), 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::ScopedClauseToEvacuable))
            }
            (atom!("$conclude_load"), 1) => Some(SystemClauseType::REPL(REPLCodePtr::ConcludeLoad)),
            (atom!("$use_module"), 3) => Some(SystemClauseType::REPL(REPLCodePtr::UseModule)),
            (atom!("$declare_module"), 3) => Some(SystemClauseType::REPL(REPLCodePtr::DeclareModule)),
            (atom!("$load_compiled_library"), 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadCompiledLibrary))
            }
            (atom!("$push_load_state_payload"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::PushLoadStatePayload))
            }
            (atom!("$add_in_situ_filename_module"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::AddInSituFilenameModule))
            }
            (atom!("$asserta"), 5) => Some(SystemClauseType::REPL(REPLCodePtr::Asserta)),
            (atom!("$assertz"), 5) => Some(SystemClauseType::REPL(REPLCodePtr::Assertz)),
            (atom!("$retract_clause"), 4) => Some(SystemClauseType::REPL(REPLCodePtr::Retract)),
            (atom!("$is_consistent_with_term_queue"), 4) => Some(SystemClauseType::REPL(
                REPLCodePtr::IsConsistentWithTermQueue,
            )),
            (atom!("$flush_term_queue"), 1) => Some(SystemClauseType::REPL(REPLCodePtr::FlushTermQueue)),
            (atom!("$remove_module_exports"), 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::RemoveModuleExports))
            }
            (atom!("$add_non_counted_backtracking"), 3) => Some(SystemClauseType::REPL(
                REPLCodePtr::AddNonCountedBacktracking,
            )),
            (atom!("$wam_instructions"), 4) => Some(SystemClauseType::WAMInstructions),
            (atom!("$write_term"), 7) => Some(SystemClauseType::WriteTerm),
            (atom!("$write_term_to_chars"), 7) => Some(SystemClauseType::WriteTermToChars),
            (atom!("$scryer_prolog_version"), 1) => Some(SystemClauseType::ScryerPrologVersion),
            (atom!("$crypto_random_byte"), 1) => Some(SystemClauseType::CryptoRandomByte),
            (atom!("$crypto_data_hash"), 4) => Some(SystemClauseType::CryptoDataHash),
            (atom!("$crypto_data_hkdf"), 7) => Some(SystemClauseType::CryptoDataHKDF),
            (atom!("$crypto_password_hash"), 4) => Some(SystemClauseType::CryptoPasswordHash),
            (atom!("$crypto_data_encrypt"), 7) => Some(SystemClauseType::CryptoDataEncrypt),
            (atom!("$crypto_data_decrypt"), 6) => Some(SystemClauseType::CryptoDataDecrypt),
            (atom!("$crypto_curve_scalar_mult"), 5) => Some(SystemClauseType::CryptoCurveScalarMult),
            (atom!("$ed25519_sign"), 4) => Some(SystemClauseType::Ed25519Sign),
            (atom!("$ed25519_verify"), 4) => Some(SystemClauseType::Ed25519Verify),
            (atom!("$ed25519_new_keypair"), 1) => Some(SystemClauseType::Ed25519NewKeyPair),
            (atom!("$ed25519_keypair_public_key"), 2) => Some(SystemClauseType::Ed25519KeyPairPublicKey),
            (atom!("$curve25519_scalar_mult"), 3) => Some(SystemClauseType::Curve25519ScalarMult),
            (atom!("$first_non_octet"), 2) => Some(SystemClauseType::FirstNonOctet),
            (atom!("$load_html"), 3) => Some(SystemClauseType::LoadHTML),
            (atom!("$load_xml"), 3) => Some(SystemClauseType::LoadXML),
            (atom!("$getenv"), 2) => Some(SystemClauseType::GetEnv),
            (atom!("$setenv"), 2) => Some(SystemClauseType::SetEnv),
            (atom!("$unsetenv"), 1) => Some(SystemClauseType::UnsetEnv),
            (atom!("$shell"), 2) => Some(SystemClauseType::Shell),
            (atom!("$pid"), 1) => Some(SystemClauseType::PID),
            (atom!("$chars_base64"), 4) => Some(SystemClauseType::CharsBase64),
            (atom!("$load_library_as_stream"), 3) => Some(SystemClauseType::LoadLibraryAsStream),
            (atom!("$push_load_context"), 2) => Some(SystemClauseType::REPL(REPLCodePtr::PushLoadContext)),
            (atom!("$pop_load_state_payload"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::PopLoadStatePayload))
            }
            (atom!("$pop_load_context"), 0) => Some(SystemClauseType::REPL(REPLCodePtr::PopLoadContext)),
            (atom!("$prolog_lc_source"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextSource))
            }
            (atom!("$prolog_lc_file"), 1) => Some(SystemClauseType::REPL(REPLCodePtr::LoadContextFile)),
            (atom!("$prolog_lc_dir"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextDirectory))
            }
            (atom!("$prolog_lc_module"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextModule))
            }
            (atom!("$prolog_lc_stream"), 1) => {
                Some(SystemClauseType::REPL(REPLCodePtr::LoadContextStream))
            }
            (atom!("$cpp_meta_predicate_property"), 4) => {
                Some(SystemClauseType::REPL(REPLCodePtr::MetaPredicateProperty))
            }
            (atom!("$cpp_built_in_property"), 2) => {
                Some(SystemClauseType::REPL(REPLCodePtr::BuiltInProperty))
            }
            (atom!("$cpp_dynamic_property"), 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::DynamicProperty))
            }
            (atom!("$cpp_multifile_property"), 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::MultifileProperty))
            }
            (atom!("$cpp_discontiguous_property"), 3) => {
                Some(SystemClauseType::REPL(REPLCodePtr::DiscontiguousProperty))
            }
            (atom!("$devour_whitespace"), 1) => Some(SystemClauseType::DevourWhitespace),
            (atom!("$is_sto_enabled"), 1) => Some(SystemClauseType::IsSTOEnabled),
            (atom!("$set_sto_as_unify"), 0) => Some(SystemClauseType::SetSTOAsUnify),
            (atom!("$set_nsto_as_unify"), 0) => Some(SystemClauseType::SetNSTOAsUnify),
            (atom!("$set_sto_with_error_as_unify"), 0) => Some(SystemClauseType::SetSTOWithErrorAsUnify),
            (atom!("$home_directory"), 1) => Some(SystemClauseType::HomeDirectory),
            (atom!("$debug_hook"), 0) => Some(SystemClauseType::DebugHook),
            (atom!("$popcount"), 2) => Some(SystemClauseType::PopCount),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BuiltInClauseType {
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
pub enum ClauseType {
    BuiltIn(BuiltInClauseType),
    CallN,
    Inlined(InlinedClauseType),
    Named(Atom, usize, CodeIndex), // name, arity, index.
    System(SystemClauseType),
}

impl BuiltInClauseType {
    pub(crate) fn name(&self) -> Atom {
        match self {
            &BuiltInClauseType::AcyclicTerm => atom!("acyclic_term"),
            &BuiltInClauseType::Arg => atom!("arg"),
            &BuiltInClauseType::Compare => atom!("compare"),
            &BuiltInClauseType::CompareTerm(qt) => qt.name(),
            &BuiltInClauseType::CopyTerm => atom!("copy_term"),
            &BuiltInClauseType::Eq => atom!("=="),
            &BuiltInClauseType::Functor => atom!("functor"),
            &BuiltInClauseType::Ground => atom!("ground"),
            &BuiltInClauseType::Is(..) => atom!("is"),
            &BuiltInClauseType::KeySort => atom!("keysort"),
            &BuiltInClauseType::NotEq => atom!("\\=="),
            &BuiltInClauseType::Read => atom!("read"),
            &BuiltInClauseType::Sort => atom!("sort"),
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
            &BuiltInClauseType::Read => 1,
            &BuiltInClauseType::Sort => 2,
        }
    }
}

impl ClauseType {
    pub(crate) fn name(&self) -> Atom {
        match self {
            &ClauseType::BuiltIn(ref built_in) => built_in.name(),
            &ClauseType::CallN => atom!("$call"),
            &ClauseType::Inlined(ref inlined) => inlined.name(),
            &ClauseType::Named(name, ..) => name,
            &ClauseType::System(ref system) => system.name(),
        }
    }

    pub(crate) fn from(name: Atom, arity: usize) -> Self {
        clause_type_form(name, arity).unwrap_or_else(|| {
            SystemClauseType::from(name, arity)
                .map(ClauseType::System)
                .unwrap_or_else(|| {
                    if name == atom!("$call") {
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
