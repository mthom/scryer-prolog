use prolog_parser::ast::*;

use prolog::forms::OpDecl;
use prolog::machine::machine_indices::*;

#[derive(Clone, Copy, PartialEq)]
pub enum CompareNumberQT {
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    NotEqual,
    Equal
}

impl CompareNumberQT {
    fn name(self) -> &'static str {
        match self {
            CompareNumberQT::GreaterThan => ">",
            CompareNumberQT::LessThan => "<",
            CompareNumberQT::GreaterThanOrEqual => ">=",
            CompareNumberQT::LessThanOrEqual => "=<",
            CompareNumberQT::NotEqual => "=\\=",
            CompareNumberQT::Equal => "=:="
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum CompareTermQT {
    LessThan,
    LessThanOrEqual,
    Equal,
    GreaterThanOrEqual,
    GreaterThan,
    NotEqual,
}

impl CompareTermQT {
    fn name<'a>(self) -> &'a str {
        match self {
            CompareTermQT::GreaterThan => "@>",
            CompareTermQT::LessThan => "@<",
            CompareTermQT::GreaterThanOrEqual => "@>=",
            CompareTermQT::LessThanOrEqual => "@=<",
            CompareTermQT::NotEqual => "\\=@=",
            CompareTermQT::Equal => "=@="
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum ArithmeticTerm {
    Reg(RegType),
    Interm(usize),
    Number(Number)
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

#[derive(Clone, PartialEq)]
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
    IsVar(RegType)
}

impl InlinedClauseType {
    pub fn name(&self) -> &'static str {
        match self {
            &InlinedClauseType::CompareNumber(qt, ..) => qt.name(),
            &InlinedClauseType::IsAtom(..) => "atom",
            &InlinedClauseType::IsAtomic(..) => "atomic",
            &InlinedClauseType::IsCompound(..) => "compound",
            &InlinedClauseType::IsInteger (..) => "integer",
            &InlinedClauseType::IsRational(..) => "rational",
            &InlinedClauseType::IsString(..) => "string",
            &InlinedClauseType::IsFloat (..) => "float",
            &InlinedClauseType::IsNonVar(..) => "nonvar",
            &InlinedClauseType::IsPartialString(..) => "is_partial_string",
            &InlinedClauseType::IsVar(..) => "var",
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<Self> {
        let r1 = temp_v!(1);
        let r2 = temp_v!(2);

        let a1 = ArithmeticTerm::Reg(r1);
        let a2 = ArithmeticTerm::Reg(r2);

        match (name, arity) {
            (">", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThan, a1, a2)),
            ("<", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::LessThan, a1, a2)),
            (">=", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::GreaterThanOrEqual,a1, a2)),
            ("=<", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::LessThanOrEqual, a1, a2)),
            ("=\\=", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::NotEqual, a1, a2)),
            ("=:=", 2) =>
                Some(InlinedClauseType::CompareNumber(CompareNumberQT::Equal, a1, a2)),
            ("atom", 1) => Some(InlinedClauseType::IsAtom(r1)),
            ("atomic", 1) => Some(InlinedClauseType::IsAtomic(r1)),
            ("compound", 1) => Some(InlinedClauseType::IsCompound(r1)),
            ("integer", 1) => Some(InlinedClauseType::IsInteger(r1)),
            ("rational", 1) => Some(InlinedClauseType::IsRational(r1)),
            ("string", 1) => Some(InlinedClauseType::IsString(r1)),
            ("float", 1) => Some(InlinedClauseType::IsFloat(r1)),
            ("nonvar", 1) => Some(InlinedClauseType::IsNonVar(r1)),
            ("var", 1) => Some(InlinedClauseType::IsVar(r1)),
            ("is_partial_string", 1) => Some(InlinedClauseType::IsPartialString(r1)),
            _ => None
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum SystemClauseType {
    AbolishClause,
    AbolishModuleClause,
    AssertDynamicPredicateToBack,
    AssertDynamicPredicateToFront,
    ModuleAssertDynamicPredicateToFront,
    ModuleAssertDynamicPredicateToBack,
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
    TruncateIfNoLiftedHeapGrowthDiff,
    TruncateIfNoLiftedHeapGrowth,
    GetAttributedVariableList,
    GetAttrVarQueueDelimiter,
    GetAttrVarQueueBeyond,
    GetBValue,
    GetClause,
    GetCurrentPredicateList,
    GetModuleClause,
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
    UnwindStack,
    WriteTerm
}

impl SystemClauseType {
    pub fn name(&self) -> ClauseName {
        match self {
            &SystemClauseType::AbolishClause => clause_name!("$abolish_clause"),
            &SystemClauseType::AbolishModuleClause => clause_name!("$abolish_module_clause"),
            &SystemClauseType::AssertDynamicPredicateToBack => clause_name!("$assertz"),
            &SystemClauseType::AssertDynamicPredicateToFront => clause_name!("$asserta"),
            &SystemClauseType::ModuleAssertDynamicPredicateToFront => clause_name!("$module_asserta"),
            &SystemClauseType::ModuleAssertDynamicPredicateToBack => clause_name!("$module_assertz"),
            &SystemClauseType::CheckCutPoint => clause_name!("$check_cp"),
            &SystemClauseType::CopyToLiftedHeap => clause_name!("$copy_to_lh"),
            &SystemClauseType::DeleteAttribute => clause_name!("$del_attr_non_head"),
            &SystemClauseType::DeleteHeadAttribute => clause_name!("$del_attr_head"),
            &SystemClauseType::DynamicModuleResolution => clause_name!("$module_call"),
            &SystemClauseType::EnqueueAttributeGoal => clause_name!("$enqueue_attribute_goal"),
            &SystemClauseType::EnqueueAttributedVar => clause_name!("$enqueue_attr_var"),
            &SystemClauseType::ExpandTerm => clause_name!("$expand_term"),
            &SystemClauseType::ExpandGoal => clause_name!("$expand_goal"),
            &SystemClauseType::FetchGlobalVar => clause_name!("$fetch_global_var"),
            &SystemClauseType::TruncateIfNoLiftedHeapGrowth => clause_name!("$truncate_if_no_lh_growth"),
            &SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff => clause_name!("$truncate_if_no_lh_growth_diff"),
            &SystemClauseType::GetAttributedVariableList => clause_name!("$get_attr_list"),
            &SystemClauseType::GetAttrVarQueueDelimiter => clause_name!("$get_attr_var_queue_delim"),
            &SystemClauseType::GetAttrVarQueueBeyond => clause_name!("$get_attr_var_queue_beyond"),
            &SystemClauseType::GetLiftedHeapFromOffset => clause_name!("$get_lh_from_offset"),
            &SystemClauseType::GetLiftedHeapFromOffsetDiff => clause_name!("$get_lh_from_offset_diff"),
            &SystemClauseType::GetCurrentPredicateList => clause_name!("$get_current_predicate_list"),
            &SystemClauseType::GetBValue => clause_name!("$get_b_value"),
            &SystemClauseType::GetClause => clause_name!("$get_clause"),
            &SystemClauseType::GetDoubleQuotes => clause_name!("$get_double_quotes"),
            &SystemClauseType::GetModuleClause => clause_name!("$get_module_clause"),
            &SystemClauseType::GetSCCCleaner => clause_name!("$get_scc_cleaner"),
            &SystemClauseType::Halt => clause_name!("$halt"),
            &SystemClauseType::HeadIsDynamic => clause_name!("$head_is_dynamic"),
            &SystemClauseType::InstallSCCCleaner => clause_name!("$install_scc_cleaner"),
            &SystemClauseType::InstallInferenceCounter => clause_name!("$install_inference_counter"),
            &SystemClauseType::LiftedHeapLength => clause_name!("$lh_length"),
            &SystemClauseType::ModuleHeadIsDynamic => clause_name!("$module_head_is_dynamic"),
            &SystemClauseType::ModuleOf => clause_name!("$module_of"),
            &SystemClauseType::NoSuchPredicate => clause_name!("$no_such_predicate"),
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
            &SystemClauseType::ResetGlobalVarAtKey => clause_name!("$reset_global_var_at_key"),
            &SystemClauseType::RetractClause => clause_name!("$retract_clause"),
            &SystemClauseType::ResetBlock => clause_name!("$reset_block"),
            &SystemClauseType::ReturnFromAttributeGoals => clause_name!("$return_from_attribute_goals"),
            &SystemClauseType::ReturnFromVerifyAttr => clause_name!("$return_from_verify_attr"),
            &SystemClauseType::SetBall => clause_name!("$set_ball"),
            &SystemClauseType::SetCutPointByDefault(_) => clause_name!("$set_cp_by_default"),
            &SystemClauseType::SetDoubleQuotes => clause_name!("$set_double_quotes"),
            &SystemClauseType::SkipMaxList => clause_name!("$skip_max_list"),
            &SystemClauseType::Succeed => clause_name!("$succeed"),
            &SystemClauseType::TermVariables => clause_name!("$term_variables"),
            &SystemClauseType::TruncateLiftedHeapTo => clause_name!("$truncate_lh_to"),
            &SystemClauseType::UnwindStack => clause_name!("$unwind_stack"),
            &SystemClauseType::WriteTerm => clause_name!("$write_term"),
        }
    }
    
    pub fn from(name: &str, arity: usize) -> Option<SystemClauseType> {
        match (name, arity) {
            ("$abolish_clause", 2) => Some(SystemClauseType::AbolishClause),
            ("$abolish_module_clause", 3) => Some(SystemClauseType::AbolishModuleClause),
            ("$module_asserta", 5) => Some(SystemClauseType::ModuleAssertDynamicPredicateToFront),
            ("$module_assertz", 5) => Some(SystemClauseType::ModuleAssertDynamicPredicateToBack),
            ("$asserta", 4) => Some(SystemClauseType::AssertDynamicPredicateToFront),
            ("$assertz", 4) => Some(SystemClauseType::AssertDynamicPredicateToBack),
            ("$check_cp", 1) => Some(SystemClauseType::CheckCutPoint),
            ("$copy_to_lh", 2) => Some(SystemClauseType::CopyToLiftedHeap),
            ("$del_attr_non_head", 1) => Some(SystemClauseType::DeleteAttribute),
            ("$del_attr_head", 1) => Some(SystemClauseType::DeleteHeadAttribute),
            ("$module_call", 2) => Some(SystemClauseType::DynamicModuleResolution),
            ("$enqueue_attribute_goal", 1) => Some(SystemClauseType::EnqueueAttributeGoal),
            ("$enqueue_attr_var", 1) => Some(SystemClauseType::EnqueueAttributedVar),
            ("$expand_term", 2) => Some(SystemClauseType::ExpandTerm),
            ("$expand_goal", 2) => Some(SystemClauseType::ExpandGoal),
            ("$fetch_global_var", 2) => Some(SystemClauseType::FetchGlobalVar),
            ("$truncate_if_no_lh_growth", 1) => Some(SystemClauseType::TruncateIfNoLiftedHeapGrowth),
            ("$truncate_if_no_lh_growth_diff", 2) => Some(SystemClauseType::TruncateIfNoLiftedHeapGrowthDiff),
            ("$get_attr_list", 2) => Some(SystemClauseType::GetAttributedVariableList),
            ("$get_b_value", 1) => Some(SystemClauseType::GetBValue),
            ("$get_clause", 2) => Some(SystemClauseType::GetClause),
            ("$get_module_clause", 3) => Some(SystemClauseType::GetModuleClause),
            ("$get_current_predicate_list", 1) => Some(SystemClauseType::GetCurrentPredicateList),
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
            ("$term_variables", 2) => Some(SystemClauseType::TermVariables),
            ("$truncate_lh_to", 1) => Some(SystemClauseType::TruncateLiftedHeapTo),
            ("$unwind_stack", 0) => Some(SystemClauseType::UnwindStack),
            ("$write_term", 4) => Some(SystemClauseType::WriteTerm),
            _ => None
        }
    }
}

#[derive(Clone, PartialEq)]
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
    ReifySwitch,
    Sort,
}

#[derive(Clone)]
pub enum ClauseType {
    BuiltIn(BuiltInClauseType),
    CallN,
    Hook(CompileTimeHook),
    Inlined(InlinedClauseType),
    Named(ClauseName, usize, CodeIndex), // name, arity, index.
    Op(OpDecl, CodeIndex),
    System(SystemClauseType)
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
            &BuiltInClauseType::Ground  => clause_name!("ground"),
            &BuiltInClauseType::Is(..)  => clause_name!("is"),
            &BuiltInClauseType::KeySort => clause_name!("keysort"),
            &BuiltInClauseType::Nl => clause_name!("nl"),
            &BuiltInClauseType::NotEq => clause_name!("\\=="),
            &BuiltInClauseType::PartialString => clause_name!("partial_string"),
            &BuiltInClauseType::Read => clause_name!("read"),
            &BuiltInClauseType::ReifySwitch => clause_name!("$reify_switch"),
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
            &BuiltInClauseType::Ground  => 1,
            &BuiltInClauseType::Is(..) => 2,
            &BuiltInClauseType::KeySort => 2,
            &BuiltInClauseType::NotEq => 2,
            &BuiltInClauseType::Nl => 0,
            &BuiltInClauseType::PartialString => 1,
            &BuiltInClauseType::Read => 1,
            &BuiltInClauseType::ReifySwitch => 3,
            &BuiltInClauseType::Sort => 2,
        }
    }

    pub fn from(name: &str, arity: usize) -> Option<Self> {
        match (name, arity) {
            ("acyclic_term", 1) => Some(BuiltInClauseType::AcyclicTerm),
            ("arg", 3) => Some(BuiltInClauseType::Arg),
            ("compare", 3) => Some(BuiltInClauseType::Compare),
            ("cyclic_term", 1) => Some(BuiltInClauseType::CyclicTerm),
            ("@>", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThan)),
            ("@<", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::LessThan)),
            ("@>=", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::GreaterThanOrEqual)),
            ("@=<", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::LessThanOrEqual)),
            ("\\=@=", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::NotEqual)),
            ("=@=", 2) => Some(BuiltInClauseType::CompareTerm(CompareTermQT::Equal)),
            ("copy_term", 2) => Some(BuiltInClauseType::CopyTerm),
            ("==", 2) => Some(BuiltInClauseType::Eq),
            ("functor", 3) => Some(BuiltInClauseType::Functor),
            ("ground", 1) => Some(BuiltInClauseType::Ground),
            ("is", 2) => Some(BuiltInClauseType::Is(temp_v!(1), ArithmeticTerm::Reg(temp_v!(2)))),
            ("keysort", 2) => Some(BuiltInClauseType::KeySort),
            ("nl", 0) => Some(BuiltInClauseType::Nl),
            ("\\==", 2) => Some(BuiltInClauseType::NotEq),
            ("partial_string", 2) => Some(BuiltInClauseType::PartialString),
            ("read", 1) => Some(BuiltInClauseType::Read),
            ("$reify_switch", 3) => Some(BuiltInClauseType::ReifySwitch),
            ("sort", 2) => Some(BuiltInClauseType::Sort),
            _ => None
        }
    }
}

impl ClauseType {
    pub fn spec(&self) -> Option<(usize, Specifier)> {
        match self {
            &ClauseType::Op(ref op_decl, _) =>
                Some((op_decl.0, op_decl.1)),
            &ClauseType::Inlined(InlinedClauseType::CompareNumber(..))
          | &ClauseType::BuiltIn(BuiltInClauseType::Is(..))
          | &ClauseType::BuiltIn(BuiltInClauseType::CompareTerm(_))
          | &ClauseType::BuiltIn(BuiltInClauseType::NotEq)
          | &ClauseType::BuiltIn(BuiltInClauseType::Eq) =>
                Some((700, XFX)),
            _ => None
        }
    }

    pub fn name(&self) -> ClauseName {
        match self {
            &ClauseType::CallN => clause_name!("call"),
            &ClauseType::BuiltIn(ref built_in) => built_in.name(),
            &ClauseType::Hook(ref hook) => hook.name(),
            &ClauseType::Inlined(ref inlined) => clause_name!(inlined.name()),
            &ClauseType::Op(ref op_decl, ..) => op_decl.name(),
            &ClauseType::Named(ref name, ..) => name.clone(),
            &ClauseType::System(ref system) => system.name(),
        }
    }

    pub fn from(name: ClauseName, arity: usize, spec: Option<(usize, Specifier)>) -> Self {
        InlinedClauseType::from(name.as_str(), arity)
            .map(ClauseType::Inlined)
            .unwrap_or_else(|| {
                BuiltInClauseType::from(name.as_str(), arity)
                    .map(ClauseType::BuiltIn)
                    .unwrap_or_else(|| {
                        SystemClauseType::from(name.as_str(), arity)
                            .map(ClauseType::System)
                            .unwrap_or_else(|| {
                                if let Some(spec) = spec {
                                    let op_decl = OpDecl(spec.0, spec.1, name);
                                    ClauseType::Op(op_decl, CodeIndex::default())
                                } else if name.as_str() == "call" {
                                    ClauseType::CallN
                                } else {
                                    ClauseType::Named(name, arity, CodeIndex::default())
                                }
                            })
                    })
            })
    }
}

impl From<InlinedClauseType> for ClauseType {
    fn from(inlined_ct: InlinedClauseType) -> Self {
        ClauseType::Inlined(inlined_ct)
    }
}
