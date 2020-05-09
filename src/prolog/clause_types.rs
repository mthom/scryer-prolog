use prolog_parser::ast::*;

use crate::prolog::forms::Number;
use crate::prolog::machine::machine_indices::*;
use crate::prolog::rug::rand::RandState;

use ref_thread_local::RefThreadLocal;

use std::collections::BTreeMap;

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
pub enum CompareTermQT {
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
pub enum ArithmeticTerm {
    Reg(RegType),
    Interm(usize),
    Number(Number),
}

impl ArithmeticTerm {
    pub fn interm_or(&self, interm: usize) -> usize {
        if let &ArithmeticTerm::Interm(interm) = self {
            interm
        } else {
            interm
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum InlinedClauseType {
    CompareNumber(CompareNumberQT, ArithmeticTerm, ArithmeticTerm),
    IsAtom(RegType),
    IsAtomic(RegType),
    IsCompound(RegType),
    IsInteger(RegType),
    IsRational(RegType),
    IsFloat(RegType),
    IsNonVar(RegType),
    IsVar(RegType),
}

ref_thread_local! {
    pub static managed RANDOM_STATE: RandState<'static> = RandState::new();
}

ref_thread_local! {
    pub static managed CLAUSE_TYPE_FORMS: BTreeMap<(&'static str, usize), ClauseType> = {
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
        m.insert(("nl", 0), ClauseType::BuiltIn(BuiltInClauseType::Nl));
        m.insert(("\\==", 2), ClauseType::BuiltIn(BuiltInClauseType::NotEq));
        m.insert(("read", 1), ClauseType::BuiltIn(BuiltInClauseType::Read));
        m.insert(("sort", 2), ClauseType::BuiltIn(BuiltInClauseType::Sort));

        m
    };
}

impl InlinedClauseType {
    pub fn name(&self) -> &'static str {
        match self {
            &InlinedClauseType::CompareNumber(qt, ..) => qt.name(),
            &InlinedClauseType::IsAtom(..) => "atom",
            &InlinedClauseType::IsAtomic(..) => "atomic",
            &InlinedClauseType::IsCompound(..) => "compound",
            &InlinedClauseType::IsInteger(..) => "integer",
            &InlinedClauseType::IsRational(..) => "rational",
            &InlinedClauseType::IsFloat(..) => "float",
            &InlinedClauseType::IsNonVar(..) => "nonvar",
            &InlinedClauseType::IsVar(..) => "var",
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum SystemClauseType {
    AbolishClause,
    AbolishModuleClause,
    AssertDynamicPredicateToBack,
    AssertDynamicPredicateToFront,
    AtEndOfExpansion,
    AtomChars,
    AtomCodes,
    AtomLength,
    BindFromRegister,
    CallContinuation,
    CharCode,
    CharType,
    CharsToNumber,
    ClearAttributeGoals,
    CloneAttributeGoals,
    CodesToNumber,
    CopyTermWithoutAttrVars,
    CheckCutPoint,
    Close,
    CopyToLiftedHeap,
    CreatePartialString,
    CurrentHostname,
    CurrentInput,
    CurrentOutput,
    DeleteAttribute,
    DeleteHeadAttribute,
    DynamicModuleResolution(usize),
    EnqueueAttributeGoal,
    EnqueueAttributedVar,
    ExpandGoal,
    ExpandTerm,
    FetchGlobalVar,
    FetchGlobalVarWithOffset,
    FileToChars,
    FirstStream,
    FlushOutput,
    GetByte,
    GetChar,
    GetCode,
    GetSingleChar,
    ResetAttrVarState,
    TruncateIfNoLiftedHeapGrowthDiff,
    TruncateIfNoLiftedHeapGrowth,
    GetAttributedVariableList,
    GetAttrVarQueueDelimiter,
    GetAttrVarQueueBeyond,
    GetBValue,
    GetClause,
    GetContinuationChunk,
    GetModuleClause,
    GetNextDBRef,
    GetNextOpDBRef,
    IsPartialString,
    LookupDBRef,
    LookupOpDBRef,
    Halt,
    ModuleHeadIsDynamic,
    GetLiftedHeapFromOffset,
    GetLiftedHeapFromOffsetDiff,
    GetSCCCleaner,
    HeadIsDynamic,
    InstallSCCCleaner,
    InstallInferenceCounter,
    LiftedHeapLength,
    ModuleAssertDynamicPredicateToFront,
    ModuleAssertDynamicPredicateToBack,
    ModuleExists,
    ModuleOf,
    ModuleRetractClause,
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
    PutCode,
    REPL(REPLCodePtr),
    ReadQueryTerm,
    ReadTerm,
    RedoAttrVarBinding,
    RemoveCallPolicyCheck,
    RemoveInferenceCounter,
    ResetContinuationMarker,
    ResetGlobalVarAtKey,
    ResetGlobalVarAtOffset,
    RetractClause,
    RestoreCutPolicy,
    SetCutPoint(RegType),
    SetInput,
    SetOutput,
    StoreGlobalVar,
    StoreGlobalVarWithOffset,
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
}

impl SystemClauseType {
    pub fn name(&self) -> ClauseName {
        match self {
            &SystemClauseType::AbolishClause => clause_name!("$abolish_clause"),
            &SystemClauseType::AbolishModuleClause => clause_name!("$abolish_module_clause"),
            &SystemClauseType::AssertDynamicPredicateToBack => clause_name!("$assertz"),
            &SystemClauseType::AssertDynamicPredicateToFront => clause_name!("$asserta"),
            &SystemClauseType::AtEndOfExpansion => clause_name!("$at_end_of_expansion"),
            &SystemClauseType::AtomChars => clause_name!("$atom_chars"),
            &SystemClauseType::AtomCodes => clause_name!("$atom_codes"),
            &SystemClauseType::AtomLength => clause_name!("$atom_length"),
            &SystemClauseType::BindFromRegister => clause_name!("$bind_from_register"),
            &SystemClauseType::CallContinuation => clause_name!("$call_continuation"),
            &SystemClauseType::CharCode => clause_name!("$char_code"),
            &SystemClauseType::CharType => clause_name!("$char_type"),
            &SystemClauseType::CharsToNumber => clause_name!("$chars_to_number"),
            &SystemClauseType::CheckCutPoint => clause_name!("$check_cp"),
            &SystemClauseType::ClearAttributeGoals => clause_name!("$clear_attribute_goals"),
            &SystemClauseType::CloneAttributeGoals => clause_name!("$clone_attribute_goals"),
            &SystemClauseType::CodesToNumber => clause_name!("$codes_to_number"),
            &SystemClauseType::CopyTermWithoutAttrVars => clause_name!("$copy_term_without_attr_vars"),
            &SystemClauseType::CreatePartialString => clause_name!("$create_partial_string"),
            &SystemClauseType::CurrentInput => clause_name!("$current_input"),
            &SystemClauseType::CurrentHostname => clause_name!("$current_hostname"),
            &SystemClauseType::CurrentOutput => clause_name!("$current_output"),
            &SystemClauseType::REPL(REPLCodePtr::CompileBatch) => clause_name!("$compile_batch"),
            &SystemClauseType::REPL(REPLCodePtr::UseModule) => clause_name!("$use_module"),
            &SystemClauseType::REPL(REPLCodePtr::UseQualifiedModule) => {
                    clause_name!("$use_qualified_module")
            }
            &SystemClauseType::REPL(REPLCodePtr::UseModuleFromFile) => {
                    clause_name!("$use_module_from_file")
            }
            &SystemClauseType::REPL(REPLCodePtr::UseQualifiedModuleFromFile) => {
                    clause_name!("$use_qualified_module_from_file")
            }
            &SystemClauseType::Close => clause_name!("$close"),
            &SystemClauseType::CopyToLiftedHeap => clause_name!("$copy_to_lh"),
            &SystemClauseType::DeleteAttribute => clause_name!("$del_attr_non_head"),
            &SystemClauseType::DeleteHeadAttribute => clause_name!("$del_attr_head"),
            &SystemClauseType::DynamicModuleResolution(_) => clause_name!("$module_call"),
            &SystemClauseType::EnqueueAttributeGoal => clause_name!("$enqueue_attribute_goal"),
            &SystemClauseType::EnqueueAttributedVar => clause_name!("$enqueue_attr_var"),
            &SystemClauseType::ExpandTerm => clause_name!("$expand_term"),
            &SystemClauseType::ExpandGoal => clause_name!("$expand_goal"),
            &SystemClauseType::FetchGlobalVar => clause_name!("$fetch_global_var"),
            &SystemClauseType::FetchGlobalVarWithOffset => {
                clause_name!("$fetch_global_var_with_offset")
            }
            &SystemClauseType::FileToChars => clause_name!("$file_to_chars"),
            &SystemClauseType::FirstStream => clause_name!("$first_stream"),
            &SystemClauseType::FlushOutput => clause_name!("$flush_output"),
            &SystemClauseType::GetByte => clause_name!("$get_byte"),
            &SystemClauseType::GetChar => clause_name!("$get_char"),
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
            &SystemClauseType::GetClause => clause_name!("$get_clause"),
            &SystemClauseType::GetNextDBRef => clause_name!("$get_next_db_ref"),
            &SystemClauseType::GetNextOpDBRef => clause_name!("$get_next_op_db_ref"),
            &SystemClauseType::LookupDBRef => clause_name!("$lookup_db_ref"),
            &SystemClauseType::LookupOpDBRef => clause_name!("$lookup_op_db_ref"),
            &SystemClauseType::GetDoubleQuotes => clause_name!("$get_double_quotes"),
            &SystemClauseType::GetModuleClause => clause_name!("$get_module_clause"),
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
            &SystemClauseType::ModuleAssertDynamicPredicateToFront => {
                clause_name!("$module_asserta")
            }
            &SystemClauseType::ModuleAssertDynamicPredicateToBack => {
                clause_name!("$module_assertz")
            }
            &SystemClauseType::ModuleHeadIsDynamic => clause_name!("$module_head_is_dynamic"),
            &SystemClauseType::ModuleExists => clause_name!("$module_exists"),
            &SystemClauseType::ModuleOf => clause_name!("$module_of"),
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
            &SystemClauseType::StoreGlobalVar => clause_name!("$store_global_var"),
            &SystemClauseType::StoreGlobalVarWithOffset => {
                clause_name!("$store_global_var_with_offset")
            }
            &SystemClauseType::InferenceLevel => clause_name!("$inference_level"),
            &SystemClauseType::CleanUpBlock => clause_name!("$clean_up_block"),
            &SystemClauseType::EraseBall => clause_name!("$erase_ball"),
            &SystemClauseType::Fail => clause_name!("$fail"),
            &SystemClauseType::GetBall => clause_name!("$get_ball"),
            &SystemClauseType::GetCutPoint => clause_name!("$get_cp"),
            &SystemClauseType::GetCurrentBlock => clause_name!("$get_current_block"),
            &SystemClauseType::InstallNewBlock => clause_name!("$install_new_block"),
            &SystemClauseType::ModuleRetractClause => clause_name!("$module_retract_clause"),
            &SystemClauseType::NextEP => clause_name!("$nextEP"),
            &SystemClauseType::ReadQueryTerm => clause_name!("$read_query_term"),
            &SystemClauseType::ReadTerm => clause_name!("$read_term"),
            &SystemClauseType::ReadTermFromChars => clause_name!("$read_term_from_chars"),
            &SystemClauseType::ResetGlobalVarAtKey => clause_name!("$reset_global_var_at_key"),
            &SystemClauseType::ResetGlobalVarAtOffset => clause_name!("$reset_global_var_at_offset"),
            &SystemClauseType::RetractClause => clause_name!("$retract_clause"),
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
            &SystemClauseType::TermAttributedVariables => clause_name!("$term_attributed_variables"),
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
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<SystemClauseType> {
        match (name, arity) {
            ("$abolish_clause", 2) => Some(SystemClauseType::AbolishClause),
            ("$at_end_of_expansion", 0) => Some(SystemClauseType::AtEndOfExpansion),
            ("$atom_chars", 2) => Some(SystemClauseType::AtomChars),
            ("$atom_codes", 2) => Some(SystemClauseType::AtomCodes),
            ("$atom_length", 2) => Some(SystemClauseType::AtomLength),
            ("$abolish_module_clause", 3) => Some(SystemClauseType::AbolishModuleClause),
            ("$bind_from_register", 2) => Some(SystemClauseType::BindFromRegister),
            ("$module_asserta", 5) => Some(SystemClauseType::ModuleAssertDynamicPredicateToFront),
            ("$module_assertz", 5) => Some(SystemClauseType::ModuleAssertDynamicPredicateToBack),
            ("$asserta", 4) => Some(SystemClauseType::AssertDynamicPredicateToFront),
            ("$assertz", 4) => Some(SystemClauseType::AssertDynamicPredicateToBack),
            ("$call_continuation", 1) => Some(SystemClauseType::CallContinuation),
            ("$char_code", 2) => Some(SystemClauseType::CharCode),
            ("$char_type", 2) => Some(SystemClauseType::CharType),
            ("$chars_to_number", 2) => Some(SystemClauseType::CharsToNumber),
            ("$clear_attribute_goals", 0) => Some(SystemClauseType::ClearAttributeGoals),
            ("$clone_attribute_goals", 1) => Some(SystemClauseType::CloneAttributeGoals),
            ("$codes_to_number", 2) => Some(SystemClauseType::CodesToNumber),
            ("$copy_term_without_attr_vars", 2) => Some(SystemClauseType::CopyTermWithoutAttrVars),
            ("$create_partial_string", 3) => Some(SystemClauseType::CreatePartialString),
            ("$check_cp", 1) => Some(SystemClauseType::CheckCutPoint),
            ("$compile_batch", 0) => Some(SystemClauseType::REPL(REPLCodePtr::CompileBatch)),
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
            ("$enqueue_attribute_goal", 1) => Some(SystemClauseType::EnqueueAttributeGoal),
            ("$enqueue_attr_var", 1) => Some(SystemClauseType::EnqueueAttributedVar),
            ("$partial_string_tail", 2) => Some(SystemClauseType::PartialStringTail),
            ("$peek_byte", 2) => Some(SystemClauseType::PeekByte),
            ("$peek_char", 2) => Some(SystemClauseType::PeekChar),
            ("$peek_code", 2) => Some(SystemClauseType::PeekCode),
            ("$is_partial_string", 1) => Some(SystemClauseType::IsPartialString),
            ("$expand_term", 2) => Some(SystemClauseType::ExpandTerm),
            ("$expand_goal", 2) => Some(SystemClauseType::ExpandGoal),
            ("$fetch_global_var", 2) => Some(SystemClauseType::FetchGlobalVar),
            ("$fetch_global_var_with_offset", 3) => Some(SystemClauseType::FetchGlobalVarWithOffset),
            ("$file_to_chars", 2) => Some(SystemClauseType::FileToChars),
            ("$get_byte", 2) => Some(SystemClauseType::GetByte),
            ("$get_char", 2) => Some(SystemClauseType::GetChar),
            ("$get_code", 2) => Some(SystemClauseType::GetCode),
            ("$get_single_char", 1) => Some(SystemClauseType::GetSingleChar),
            ("$points_to_cont_reset_marker", 1) => {
                Some(SystemClauseType::PointsToContinuationResetMarker)
            }
            ("$put_byte", 2) => {
                Some(SystemClauseType::PutByte)
            }
            ("$put_char", 2) => {
                Some(SystemClauseType::PutChar)
            }
            ("$put_code", 2) => {
                Some(SystemClauseType::PutCode)
            }
            ("$reset_attr_var_state", 0) => Some(SystemClauseType::ResetAttrVarState),
            ("$truncate_if_no_lh_growth", 1) => {
                Some(SystemClauseType::TruncateIfNoLiftedHeapGrowth)
            }
            ("$truncate_if_no_lh_growth_diff", 2) => {
                Some(SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff)
            }
            ("$get_attr_list", 2) => Some(SystemClauseType::GetAttributedVariableList),
            ("$get_b_value", 1) => Some(SystemClauseType::GetBValue),
            ("$get_clause", 2) => Some(SystemClauseType::GetClause),
            ("$get_module_clause", 3) => Some(SystemClauseType::GetModuleClause),
            ("$get_lh_from_offset", 2) => Some(SystemClauseType::GetLiftedHeapFromOffset),
            ("$get_lh_from_offset_diff", 3) => Some(SystemClauseType::GetLiftedHeapFromOffsetDiff),
            ("$get_double_quotes", 1) => Some(SystemClauseType::GetDoubleQuotes),
            ("$get_scc_cleaner", 1) => Some(SystemClauseType::GetSCCCleaner),
            ("$halt", 0) => Some(SystemClauseType::Halt),
            ("$head_is_dynamic", 1) => Some(SystemClauseType::HeadIsDynamic),
            ("$install_scc_cleaner", 2) => Some(SystemClauseType::InstallSCCCleaner),
            ("$install_inference_counter", 3) => Some(SystemClauseType::InstallInferenceCounter),
            ("$lh_length", 1) => Some(SystemClauseType::LiftedHeapLength),
            ("$maybe", 0) => Some(SystemClauseType::Maybe),
            ("$cpu_now", 1) => Some(SystemClauseType::CpuNow),
            ("$module_exists", 1) => Some(SystemClauseType::ModuleExists),
            ("$module_of", 2) => Some(SystemClauseType::ModuleOf),
            ("$module_retract_clause", 5) => Some(SystemClauseType::ModuleRetractClause),
            ("$module_head_is_dynamic", 2) => Some(SystemClauseType::ModuleHeadIsDynamic),
            ("$no_such_predicate", 1) => Some(SystemClauseType::NoSuchPredicate),
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
            ("$reset_global_var_at_key", 1) => Some(SystemClauseType::ResetGlobalVarAtKey),
            ("$reset_global_var_at_offset", 3) => Some(SystemClauseType::ResetGlobalVarAtOffset),
            ("$retract_clause", 4) => Some(SystemClauseType::RetractClause),
            ("$return_from_verify_attr", 0) => Some(SystemClauseType::ReturnFromVerifyAttr),
            ("$set_ball", 1) => Some(SystemClauseType::SetBall),
            ("$set_cp_by_default", 1) => Some(SystemClauseType::SetCutPointByDefault(temp_v!(1))),
            ("$set_double_quotes", 1) => Some(SystemClauseType::SetDoubleQuotes),
            ("$set_seed", 1) => Some(SystemClauseType::SetSeed),
            ("$skip_max_list", 4) => Some(SystemClauseType::SkipMaxList),
            ("$sleep", 1) => Some(SystemClauseType::Sleep),
            ("$socket_client_open", 7) => Some(SystemClauseType::SocketClientOpen),
            ("$socket_server_open", 3) => Some(SystemClauseType::SocketServerOpen),
            ("$socket_server_accept", 7) => Some(SystemClauseType::SocketServerAccept),
            ("$socket_server_close", 1) => Some(SystemClauseType::SocketServerClose),
            ("$store_global_var", 2) => Some(SystemClauseType::StoreGlobalVar),
            ("$store_global_var_with_offset", 2) => Some(SystemClauseType::StoreGlobalVarWithOffset),
            ("$term_attributed_variables", 2) => Some(SystemClauseType::TermAttributedVariables),
            ("$term_variables", 2) => Some(SystemClauseType::TermVariables),
            ("$truncate_lh_to", 1) => Some(SystemClauseType::TruncateLiftedHeapTo),
            ("$unwind_environments", 0) => Some(SystemClauseType::UnwindEnvironments),
            ("$unwind_stack", 0) => Some(SystemClauseType::UnwindStack),
            ("$unify_with_occurs_check", 2) => Some(SystemClauseType::UnifyWithOccursCheck),
            ("$use_module", 1) => Some(SystemClauseType::REPL(REPLCodePtr::UseModule)),
            ("$use_module_from_file", 1) =>
                    Some(SystemClauseType::REPL(REPLCodePtr::UseModuleFromFile)),
            ("$use_qualified_module", 2) =>
                    Some(SystemClauseType::REPL(REPLCodePtr::UseQualifiedModule)),
            ("$use_qualified_module_from_file", 2) =>
                    Some(SystemClauseType::REPL(REPLCodePtr::UseQualifiedModuleFromFile)),
            ("$variant", 2) => Some(SystemClauseType::Variant),
            ("$wam_instructions", 3) => Some(SystemClauseType::WAMInstructions),
            ("$write_term", 7) => Some(SystemClauseType::WriteTerm),
            ("$write_term_to_chars", 7) => Some(SystemClauseType::WriteTermToChars),
            ("$scryer_prolog_version", 1) => Some(SystemClauseType::ScryerPrologVersion),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
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
    Nl,
    NotEq,
    Read,
    Sort,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClauseType {
    BuiltIn(BuiltInClauseType),
    CallN,
    Hook(CompileTimeHook),
    Inlined(InlinedClauseType),
    Named(ClauseName, usize, CodeIndex), // name, arity, index.
    Op(ClauseName, SharedOpDesc, CodeIndex),
    System(SystemClauseType),
}

impl BuiltInClauseType {
    pub fn name(&self) -> ClauseName {
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
            &BuiltInClauseType::Nl => clause_name!("nl"),
            &BuiltInClauseType::NotEq => clause_name!("\\=="),
            &BuiltInClauseType::Read => clause_name!("read"),
            &BuiltInClauseType::Sort => clause_name!("sort"),
        }
    }

    pub fn arity(&self) -> usize {
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
            &BuiltInClauseType::Nl => 0,
            &BuiltInClauseType::Read => 1,
            &BuiltInClauseType::Sort => 2,
        }
    }
}

impl ClauseType {
    pub fn spec(&self) -> Option<SharedOpDesc> {
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

    pub fn name(&self) -> ClauseName {
        match self {
            &ClauseType::BuiltIn(ref built_in) => built_in.name(),
            &ClauseType::CallN => clause_name!("call"),
            &ClauseType::Hook(ref hook) => hook.name(),
            &ClauseType::Inlined(ref inlined) => clause_name!(inlined.name()),
            &ClauseType::Op(ref name, ..) => name.clone(),
            &ClauseType::Named(ref name, ..) => name.clone(),
            &ClauseType::System(ref system) => system.name(),
        }
    }

    pub fn from(name: ClauseName, arity: usize, spec: Option<SharedOpDesc>) -> Self {
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
                        } else if name.as_str() == "call" {
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
