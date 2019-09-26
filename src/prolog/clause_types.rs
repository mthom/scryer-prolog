use prolog_parser::ast::*;

use prolog::forms::Number;
use prolog::machine::machine_indices::*;

use ref_thread_local::RefThreadLocal;

use std::collections::BTreeMap;

#[derive(Clone, Copy, Eq, PartialEq)]
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

#[derive(Clone, Copy, PartialEq, Eq)]
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

#[derive(Clone, PartialEq, Eq)]
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

#[derive(Clone, Eq, PartialEq)]
pub enum InlinedClauseType {
    CompareNumber(CompareNumberQT, ArithmeticTerm, ArithmeticTerm),
    IsAtom(RegType),
    IsAtomic(RegType),
    IsCompound(RegType),
    IsInteger(RegType),
    IsRational(RegType),
    IsString(RegType),
    IsFloat(RegType),
    IsNonVar(RegType),
    IsPartialString(RegType),
    IsVar(RegType),
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
        m.insert(("string", 1), ClauseType::Inlined(InlinedClauseType::IsString(r1)));
        m.insert(("float", 1), ClauseType::Inlined(InlinedClauseType::IsFloat(r1)));
        m.insert(("nonvar", 1), ClauseType::Inlined(InlinedClauseType::IsNonVar(r1)));
        m.insert(("is_partial_string", 1), ClauseType::Inlined(InlinedClauseType::IsPartialString(r1)));
        m.insert(("var", 1), ClauseType::Inlined(InlinedClauseType::IsVar(r1)));
        m.insert(("acyclic_term", 1), ClauseType::BuiltIn(BuiltInClauseType::AcyclicTerm));
        m.insert(("arg", 3), ClauseType::BuiltIn(BuiltInClauseType::Arg));
        m.insert(("compare", 3), ClauseType::BuiltIn(BuiltInClauseType::Compare));
        m.insert(("@>", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThan)));
        m.insert(("@<", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::LessThan)));
        m.insert(("@>=", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThanOrEqual)));
        m.insert(("@=<", 2), ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(CompareTermQT::LessThanOrEqual)));
        m.insert(("copy_term", 2), ClauseType::BuiltIn(BuiltInClauseType::CopyTerm));
        m.insert(("cyclic_term", 1), ClauseType::BuiltIn(BuiltInClauseType::CyclicTerm));
        m.insert(("==", 2), ClauseType::BuiltIn(BuiltInClauseType::Eq));
        m.insert(("functor", 3), ClauseType::BuiltIn(BuiltInClauseType::Functor));
        m.insert(("ground", 1), ClauseType::BuiltIn(BuiltInClauseType::Ground));
        m.insert(("is", 2), ClauseType::BuiltIn(BuiltInClauseType::Is(r1, ar_reg!(r2))));
        m.insert(("keysort", 2), ClauseType::BuiltIn(BuiltInClauseType::KeySort));
        m.insert(("nl", 0), ClauseType::BuiltIn(BuiltInClauseType::Nl));
        m.insert(("\\==", 2), ClauseType::BuiltIn(BuiltInClauseType::NotEq));
        m.insert(("partial_string", 2), ClauseType::BuiltIn(BuiltInClauseType::PartialString));
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
            &InlinedClauseType::IsString(..) => "string",
            &InlinedClauseType::IsFloat(..) => "float",
            &InlinedClauseType::IsNonVar(..) => "nonvar",
            &InlinedClauseType::IsPartialString(..) => "is_partial_string",
            &InlinedClauseType::IsVar(..) => "var",
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum SystemClauseType {
    AbolishClause,
    AbolishModuleClause,
    AssertDynamicPredicateToBack,
    AssertDynamicPredicateToFront,
    AtomChars,
    AtomCodes,
    AtomLength,
    ModuleAssertDynamicPredicateToFront,
    ModuleAssertDynamicPredicateToBack,
    CharCode,
    CharsToNumber,
    CodesToNumber,
    CheckCutPoint,
    CopyToLiftedHeap,
    DeleteAttribute,
    DeleteHeadAttribute,
    DynamicModuleResolution,
    EnqueueAttributeGoal,
    EnqueueAttributedVar,
    ExpandGoal,
    ExpandTerm,
    FetchGlobalVar,
    GetChar,
    TruncateIfNoLiftedHeapGrowthDiff,
    TruncateIfNoLiftedHeapGrowth,
    GetAttributedVariableList,
    GetAttrVarQueueDelimiter,
    GetAttrVarQueueBeyond,
    GetBValue,
    GetClause,
    GetModuleClause,
    GetNextDBRef,
    GetNextOpDBRef,
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
    ModuleOf,
    ModuleRetractClause,
    NoSuchPredicate,
    NumberToChars,
    NumberToCodes,
    OpDeclaration,
    REPL(REPLCodePtr),
    ReadQueryTerm,
    ReadTerm,
    RedoAttrVarBindings,
    RemoveCallPolicyCheck,
    RemoveInferenceCounter,
    ResetGlobalVarAtKey,
    RetractClause,
    RestoreCutPolicy,
    SetCutPoint(RegType),
    StoreGlobalVar,
    InferenceLevel,
    CleanUpBlock,
    EraseBall,
    Fail,
    GetBall,
    GetCurrentBlock,
    GetCutPoint,
    GetDoubleQuotes,
    InstallNewBlock,
    ResetBlock,
    ReturnFromAttributeGoals,
    ReturnFromVerifyAttr,
    SetBall,
    SetCutPointByDefault(RegType),
    SetDoubleQuotes,
    SkipMaxList,
    Succeed,
    TermVariables,
    TruncateLiftedHeapTo,
    UnifyWithOccursCheck,
    UnwindStack,
    Variant,
    WAMInstructions,
    WriteTerm,
}

impl SystemClauseType {
    pub fn name(&self) -> ClauseName {
        match self {
            &SystemClauseType::AbolishClause => clause_name!("$abolish_clause"),
            &SystemClauseType::AbolishModuleClause => clause_name!("$abolish_module_clause"),
            &SystemClauseType::AssertDynamicPredicateToBack => clause_name!("$assertz"),
            &SystemClauseType::AssertDynamicPredicateToFront => clause_name!("$asserta"),
            &SystemClauseType::AtomChars => clause_name!("$atom_chars"),
            &SystemClauseType::AtomCodes => clause_name!("$atom_codes"),
            &SystemClauseType::AtomLength => clause_name!("$atom_length"),
            &SystemClauseType::ModuleAssertDynamicPredicateToFront => {
                clause_name!("$module_asserta")
            }
            &SystemClauseType::ModuleAssertDynamicPredicateToBack => {
                clause_name!("$module_assertz")
            }
            &SystemClauseType::CharCode => clause_name!("$char_code"),
            &SystemClauseType::CharsToNumber => clause_name!("$chars_to_number"),
            &SystemClauseType::CodesToNumber => clause_name!("$codes_to_number"),
            &SystemClauseType::CheckCutPoint => clause_name!("$check_cp"),
            &SystemClauseType::REPL(REPLCodePtr::CompileBatch) => clause_name!("$compile_batch"),
            &SystemClauseType::REPL(REPLCodePtr::SubmitQueryAndPrintResults) => {
                clause_name!("$submit_query_and_print_results")
            }
            &SystemClauseType::CopyToLiftedHeap => clause_name!("$copy_to_lh"),
            &SystemClauseType::DeleteAttribute => clause_name!("$del_attr_non_head"),
            &SystemClauseType::DeleteHeadAttribute => clause_name!("$del_attr_head"),
            &SystemClauseType::DynamicModuleResolution => clause_name!("$module_call"),
            &SystemClauseType::EnqueueAttributeGoal => clause_name!("$enqueue_attribute_goal"),
            &SystemClauseType::EnqueueAttributedVar => clause_name!("$enqueue_attr_var"),
            &SystemClauseType::ExpandTerm => clause_name!("$expand_term"),
            &SystemClauseType::ExpandGoal => clause_name!("$expand_goal"),
            &SystemClauseType::FetchGlobalVar => clause_name!("$fetch_global_var"),
            &SystemClauseType::GetChar => clause_name!("$get_char"),
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
            &SystemClauseType::OpDeclaration => clause_name!("$op$"),
            &SystemClauseType::InstallSCCCleaner => clause_name!("$install_scc_cleaner"),
            &SystemClauseType::InstallInferenceCounter => {
                clause_name!("$install_inference_counter")
            }
            &SystemClauseType::LiftedHeapLength => clause_name!("$lh_length"),
            &SystemClauseType::ModuleHeadIsDynamic => clause_name!("$module_head_is_dynamic"),
            &SystemClauseType::ModuleOf => clause_name!("$module_of"),
            &SystemClauseType::NoSuchPredicate => clause_name!("$no_such_predicate"),
            &SystemClauseType::NumberToChars => clause_name!("$number_to_chars"),
            &SystemClauseType::NumberToCodes => clause_name!("$number_to_codes"),
            &SystemClauseType::RedoAttrVarBindings => clause_name!("$redo_attr_var_bindings"),
            &SystemClauseType::RemoveCallPolicyCheck => clause_name!("$remove_call_policy_check"),
            &SystemClauseType::RemoveInferenceCounter => clause_name!("$remove_inference_counter"),
            &SystemClauseType::RestoreCutPolicy => clause_name!("$restore_cut_policy"),
            &SystemClauseType::SetCutPoint(_) => clause_name!("$set_cp"),
            &SystemClauseType::StoreGlobalVar => clause_name!("$store_global_var"),
            &SystemClauseType::InferenceLevel => clause_name!("$inference_level"),
            &SystemClauseType::CleanUpBlock => clause_name!("$clean_up_block"),
            &SystemClauseType::EraseBall => clause_name!("$erase_ball"),
            &SystemClauseType::Fail => clause_name!("$fail"),
            &SystemClauseType::GetBall => clause_name!("$get_ball"),
            &SystemClauseType::GetCutPoint => clause_name!("$get_cp"),
            &SystemClauseType::GetCurrentBlock => clause_name!("$get_current_block"),
            &SystemClauseType::InstallNewBlock => clause_name!("$install_new_block"),
            &SystemClauseType::ModuleRetractClause => clause_name!("$module_retract_clause"),
            &SystemClauseType::ReadQueryTerm => clause_name!("$read_query_term"),
            &SystemClauseType::ReadTerm => clause_name!("$read_term"),
            &SystemClauseType::ResetGlobalVarAtKey => clause_name!("$reset_global_var_at_key"),
            &SystemClauseType::RetractClause => clause_name!("$retract_clause"),
            &SystemClauseType::ResetBlock => clause_name!("$reset_block"),
            &SystemClauseType::ReturnFromAttributeGoals => {
                clause_name!("$return_from_attribute_goals")
            }
            &SystemClauseType::ReturnFromVerifyAttr => clause_name!("$return_from_verify_attr"),
            &SystemClauseType::SetBall => clause_name!("$set_ball"),
            &SystemClauseType::SetCutPointByDefault(_) => clause_name!("$set_cp_by_default"),
            &SystemClauseType::SetDoubleQuotes => clause_name!("$set_double_quotes"),
            &SystemClauseType::SkipMaxList => clause_name!("$skip_max_list"),
            &SystemClauseType::Succeed => clause_name!("$succeed"),
            &SystemClauseType::TermVariables => clause_name!("$term_variables"),
            &SystemClauseType::TruncateLiftedHeapTo => clause_name!("$truncate_lh_to"),
            &SystemClauseType::UnifyWithOccursCheck => clause_name!("$unify_with_occurs_check"),
            &SystemClauseType::UnwindStack => clause_name!("$unwind_stack"),
            &SystemClauseType::Variant => clause_name!("$variant"),
            &SystemClauseType::WAMInstructions => clause_name!("$wam_instructions"),
            &SystemClauseType::WriteTerm => clause_name!("$write_term"),
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<SystemClauseType> {
        match (name, arity) {
            ("$abolish_clause", 2) => Some(SystemClauseType::AbolishClause),
            ("$atom_chars", 2) => Some(SystemClauseType::AtomChars),
            ("$atom_codes", 2) => Some(SystemClauseType::AtomCodes),
            ("$atom_length", 2) => Some(SystemClauseType::AtomLength),
            ("$abolish_module_clause", 3) => Some(SystemClauseType::AbolishModuleClause),
            ("$module_asserta", 5) => Some(SystemClauseType::ModuleAssertDynamicPredicateToFront),
            ("$module_assertz", 5) => Some(SystemClauseType::ModuleAssertDynamicPredicateToBack),
            ("$asserta", 4) => Some(SystemClauseType::AssertDynamicPredicateToFront),
            ("$assertz", 4) => Some(SystemClauseType::AssertDynamicPredicateToBack),
            ("$char_code", 2) => Some(SystemClauseType::CharCode),
            ("$chars_to_number", 2) => Some(SystemClauseType::CharsToNumber),
            ("$codes_to_number", 2) => Some(SystemClauseType::CodesToNumber),
            ("$check_cp", 1) => Some(SystemClauseType::CheckCutPoint),
            ("$compile_batch", 0) => Some(SystemClauseType::REPL(REPLCodePtr::CompileBatch)),
            ("$copy_to_lh", 2) => Some(SystemClauseType::CopyToLiftedHeap),
            ("$del_attr_non_head", 1) => Some(SystemClauseType::DeleteAttribute),
            ("$del_attr_head", 1) => Some(SystemClauseType::DeleteHeadAttribute),
            ("$get_next_db_ref", 2) => Some(SystemClauseType::GetNextDBRef),
            ("$get_next_op_db_ref", 2) => Some(SystemClauseType::GetNextOpDBRef),
            ("$lookup_db_ref", 3) => Some(SystemClauseType::LookupDBRef),
            ("$lookup_op_db_ref", 4) => Some(SystemClauseType::LookupOpDBRef),
            ("$module_call", 2) => Some(SystemClauseType::DynamicModuleResolution),
            ("$enqueue_attribute_goal", 1) => Some(SystemClauseType::EnqueueAttributeGoal),
            ("$enqueue_attr_var", 1) => Some(SystemClauseType::EnqueueAttributedVar),
            ("$expand_term", 2) => Some(SystemClauseType::ExpandTerm),
            ("$expand_goal", 2) => Some(SystemClauseType::ExpandGoal),
            ("$fetch_global_var", 2) => Some(SystemClauseType::FetchGlobalVar),
            ("$get_char", 1) => Some(SystemClauseType::GetChar),
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
            ("$module_of", 2) => Some(SystemClauseType::ModuleOf),
            ("$module_retract_clause", 5) => Some(SystemClauseType::ModuleRetractClause),
            ("$module_head_is_dynamic", 2) => Some(SystemClauseType::ModuleHeadIsDynamic),
            ("$no_such_predicate", 1) => Some(SystemClauseType::NoSuchPredicate),
            ("$number_to_chars", 2) => Some(SystemClauseType::NumberToChars),
            ("$number_to_codes", 2) => Some(SystemClauseType::NumberToCodes),
            ("$op", 3) => Some(SystemClauseType::OpDeclaration),
            ("$redo_attr_var_bindings", 0) => Some(SystemClauseType::RedoAttrVarBindings),
            ("$remove_call_policy_check", 1) => Some(SystemClauseType::RemoveCallPolicyCheck),
            ("$remove_inference_counter", 2) => Some(SystemClauseType::RemoveInferenceCounter),
            ("$restore_cut_policy", 0) => Some(SystemClauseType::RestoreCutPolicy),
            ("$set_cp", 1) => Some(SystemClauseType::SetCutPoint(temp_v!(1))),
            ("$inference_level", 2) => Some(SystemClauseType::InferenceLevel),
            ("$clean_up_block", 1) => Some(SystemClauseType::CleanUpBlock),
            ("$erase_ball", 0) => Some(SystemClauseType::EraseBall),
            ("$fail", 0) => Some(SystemClauseType::Fail),
            ("$get_attr_var_queue_beyond", 2) => Some(SystemClauseType::GetAttrVarQueueBeyond),
            ("$get_attr_var_queue_delim", 1) => Some(SystemClauseType::GetAttrVarQueueDelimiter),
            ("$get_ball", 1) => Some(SystemClauseType::GetBall),
            ("$get_current_block", 1) => Some(SystemClauseType::GetCurrentBlock),
            ("$get_cp", 1) => Some(SystemClauseType::GetCutPoint),
            ("$install_new_block", 1) => Some(SystemClauseType::InstallNewBlock),
            ("$read_query_term", 2) => Some(SystemClauseType::ReadQueryTerm),
            ("$read_term", 2) => Some(SystemClauseType::ReadTerm),
            ("$reset_block", 1) => Some(SystemClauseType::ResetBlock),
            ("$reset_global_var_at_key", 1) => Some(SystemClauseType::ResetGlobalVarAtKey),
            ("$retract_clause", 4) => Some(SystemClauseType::RetractClause),
            ("$return_from_attribute_goals", 0) => Some(SystemClauseType::ReturnFromAttributeGoals),
            ("$return_from_verify_attr", 0) => Some(SystemClauseType::ReturnFromVerifyAttr),
            ("$set_ball", 1) => Some(SystemClauseType::SetBall),
            ("$set_cp_by_default", 1) => Some(SystemClauseType::SetCutPointByDefault(temp_v!(1))),
            ("$set_double_quotes", 1) => Some(SystemClauseType::SetDoubleQuotes),
            ("$skip_max_list", 4) => Some(SystemClauseType::SkipMaxList),
            ("$store_global_var", 2) => Some(SystemClauseType::StoreGlobalVar),
            ("$submit_query_and_print_results", 2) => Some(SystemClauseType::REPL(
                REPLCodePtr::SubmitQueryAndPrintResults,
            )),
            ("$term_variables", 2) => Some(SystemClauseType::TermVariables),
            ("$truncate_lh_to", 1) => Some(SystemClauseType::TruncateLiftedHeapTo),
            ("$unwind_stack", 0) => Some(SystemClauseType::UnwindStack),
            ("$unify_with_occurs_check", 2) => Some(SystemClauseType::UnifyWithOccursCheck),
            ("$variant", 2) => Some(SystemClauseType::Variant),
            ("$write_term", 5) => Some(SystemClauseType::WriteTerm),
            ("$wam_instructions", 3) => Some(SystemClauseType::WAMInstructions),
            _ => None,
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub enum BuiltInClauseType {
    AcyclicTerm,
    Arg,
    Compare,
    CompareTerm(CompareTermQT),
    CyclicTerm,
    CopyTerm,
    Eq,
    Functor,
    Ground,
    Is(RegType, ArithmeticTerm),
    KeySort,
    Nl,
    NotEq,
    PartialString,
    Read,
    Sort,
}

#[derive(Clone, PartialEq, Eq)]
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
            &BuiltInClauseType::CyclicTerm => clause_name!("cyclic_term"),
            &BuiltInClauseType::CopyTerm => clause_name!("copy_term"),
            &BuiltInClauseType::Eq => clause_name!("=="),
            &BuiltInClauseType::Functor => clause_name!("functor"),
            &BuiltInClauseType::Ground => clause_name!("ground"),
            &BuiltInClauseType::Is(..) => clause_name!("is"),
            &BuiltInClauseType::KeySort => clause_name!("keysort"),
            &BuiltInClauseType::Nl => clause_name!("nl"),
            &BuiltInClauseType::NotEq => clause_name!("\\=="),
            &BuiltInClauseType::PartialString => clause_name!("partial_string"),
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
            &BuiltInClauseType::CyclicTerm => 1,
            &BuiltInClauseType::CopyTerm => 2,
            &BuiltInClauseType::Eq => 2,
            &BuiltInClauseType::Functor => 3,
            &BuiltInClauseType::Ground => 1,
            &BuiltInClauseType::Is(..) => 2,
            &BuiltInClauseType::KeySort => 2,
            &BuiltInClauseType::NotEq => 2,
            &BuiltInClauseType::Nl => 0,
            &BuiltInClauseType::PartialString => 1,
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
            &ClauseType::CallN => clause_name!("call"),
            &ClauseType::BuiltIn(ref built_in) => built_in.name(),
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
