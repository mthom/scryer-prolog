macro_rules! clause_name {
    ($name: expr) => (
        ClauseName::BuiltIn($name)
    )
}

macro_rules! tabled_rc {
    ($e:expr, $tbl:expr) => (
        TabledRc::new(String::from($e), $tbl.clone())
    )
}

macro_rules! atom {
    ($e:expr, $tbl:expr) => (
        Constant::Atom(ClauseName::User(tabled_rc!($e, $tbl)))
    );
    ($e:expr) => (
        Constant::Atom(clause_name!($e))
    )
}

macro_rules! internal_call_n {
    () => (
        Line::BuiltIn(BuiltInInstruction::InternalCallN)
    )
}

macro_rules! allocate {
    ($cells:expr) => (
        Line::Control(ControlInstruction::Allocate($cells))
    )
}

macro_rules! deallocate {
    () => (
        Line::Control(ControlInstruction::Deallocate)
    )
}

macro_rules! compare_number_instr {
    ($cmp: expr, $at_1: expr, $at_2: expr) => (
        Line::BuiltIn(BuiltInInstruction::CompareNumber($cmp, $at_1, $at_2))
    )
}

macro_rules! interm {
    ($n: expr) => (
        ArithmeticTerm::Interm($n)
    )
}

macro_rules! query {
    [$($x:expr),+] => (
        Line::Query(vec![$($x),+])
    )
}

macro_rules! heap_atom {
    ($name:expr) => (
        HeapCellValue::Addr(Addr::Con(atom!($name)))
    );
    ($name:expr, $tbl:expr) => (
        HeapCellValue::Addr(Addr::Con(atom!($name, $tbl)))
    )
}

macro_rules! functor {
    ($name:expr) => (
        vec![ heap_atom!($name) ]
    );
    ($name:expr, $len:expr, [$($args:expr),*]) => (
        vec![ HeapCellValue::NamedStr($len, clause_name!($name), None), $($args),* ]
    )
}

macro_rules! fact {
    [$($x:expr),+] => (
        Line::Fact(vec![$($x),+])
    )
}

macro_rules! temp_v {
    ($x:expr) => (
        RegType::Temp($x)
    )
}

macro_rules! perm_v {
    ($x:expr) => (
        RegType::Perm($x)
    )
}

macro_rules! get_var_in_query {
    ($r:expr, $arg:expr) => (
        QueryInstruction::GetVariable($r, $arg)
    )
}


macro_rules! get_value {
    ($r:expr, $arg:expr) => (
        FactInstruction::GetValue($r, $arg)
    )
}

macro_rules! set_value {
    ($r:expr) => (
        QueryInstruction::SetValue($r)
    )
}

macro_rules! get_var_in_fact {
    ($r:expr, $arg:expr) => (
        FactInstruction::GetVariable($r, $arg)
    )
}

macro_rules! put_var {
    ($r:expr, $arg:expr) => (
        QueryInstruction::PutVariable($r, $arg)
    )
}

macro_rules! put_structure {
    ($atom:expr, $arity:expr, $r:expr, Some($fix:expr)) => (
        QueryInstruction::PutStructure(ClauseType::Op(clause_name!($atom), $fix), $arity, $r)
    );
    ($atom:expr, $arity:expr, $r:expr, None) => (
        QueryInstruction::PutStructure(ClauseType::Named(clause_name!($atom)), $arity, $r)
    )
}

macro_rules! put_constant {
    ($lvl:expr, $cons:expr, $r:expr) => (
        QueryInstruction::PutConstant($lvl, $cons, $r)
    )
}

macro_rules! set_constant {
    ($cons:expr) => (
        QueryInstruction::SetConstant($cons)
    )
}

macro_rules! put_value {
    ($r:expr, $arg:expr) => (
        QueryInstruction::PutValue($r, $arg)
    )
}

macro_rules! put_unsafe_value {
    ($r:expr, $arg:expr) => (
        QueryInstruction::PutUnsafeValue($r, $arg)
    )
}

macro_rules! try_me_else {
    ($o:expr) => (
        Line::Choice(ChoiceInstruction::TryMeElse($o))
    )
}

macro_rules! retry_me_else {
    ($o:expr) => (
        Line::Choice(ChoiceInstruction::RetryMeElse($o))
    )
}

macro_rules! is_atom {
    ($reg:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsAtom($reg))
    )
}

macro_rules! is_atomic {
    ($reg:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsAtomic($reg))
    )
}

macro_rules! is_integer {
    ($reg:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsInteger($reg))
    )
}

macro_rules! is_compound {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsCompound($r))
    )
}

macro_rules! is_float {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsFloat($r))
    )
}

macro_rules! is_rational {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsRational($r))
    )
}


macro_rules! is_nonvar {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsNonVar($r))
    )
}

macro_rules! is_string {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsString($r))
    )
}

macro_rules! is_var {
    ($reg:expr) => (
        Line::BuiltIn(BuiltInInstruction::IsVar($reg))
    )
}

macro_rules! trust_me {
    () => (
        Line::Choice(ChoiceInstruction::TrustMe)
    )
}

macro_rules! call_n {
    ($arity:expr) => (
        Line::Control(ControlInstruction::CallN($arity))
    )
}

macro_rules! execute_n {
    ($arity:expr) => (
        Line::Control(ControlInstruction::ExecuteN($arity))
    )
}

macro_rules! proceed {
    () => (
        Line::Control(ControlInstruction::Proceed)
    )
}

macro_rules! cut {
    ($r:expr) => (
        Line::Cut(CutInstruction::Cut($r))
    )
}

macro_rules! neck_cut {
    () => (
        Line::Cut(CutInstruction::NeckCut)
    )
}

macro_rules! get_current_block {
    () => (
        Line::BuiltIn(BuiltInInstruction::GetCurrentBlock)
    )
}

macro_rules! install_new_block {
    () => (
        Line::BuiltIn(BuiltInInstruction::InstallNewBlock)
    )
}

macro_rules! goto_call {
    ($line:expr, $arity:expr) => (
        Line::Control(ControlInstruction::GotoCall($line, $arity))
    )
}

macro_rules! goto_execute {
    ($line:expr, $arity:expr) => (
        Line::Control(ControlInstruction::GotoExecute($line, $arity))
    )
}

macro_rules! reset_block {
    () => (
        Line::BuiltIn(BuiltInInstruction::ResetBlock)
    )
}

macro_rules! get_ball {
    () => (
        Line::BuiltIn(BuiltInInstruction::GetBall)
    )
}

macro_rules! erase_ball {
    () => (
        Line::BuiltIn(BuiltInInstruction::EraseBall)
    )
}

macro_rules! unify {
    () => (
        Line::BuiltIn(BuiltInInstruction::Unify)
    )
}

macro_rules! is_call {
    ($r:expr, $at:expr) => (
        Line::Control(ControlInstruction::IsCall($r, $at))
    )
}

macro_rules! unwind_stack {
    () => (
        Line::BuiltIn(BuiltInInstruction::UnwindStack)
    )
}

macro_rules! clean_up_block {
    () => (
        Line::BuiltIn(BuiltInInstruction::CleanUpBlock)
    )
}

macro_rules! set_ball {
    () => (
        Line::BuiltIn(BuiltInInstruction::SetBall)
    )
}

macro_rules! fail {
    () => (
        Line::BuiltIn(BuiltInInstruction::Fail)
    )
}

macro_rules! succeed {
    () => (
        Line::BuiltIn(BuiltInInstruction::Succeed)
    )
}

macro_rules! duplicate_term {
    () => (
        Line::Control(ControlInstruction::DuplicateTermCall)
    )
}

macro_rules! get_level {
    ($r:expr) => (
        Line::Cut(CutInstruction::GetLevel($r))
    )
}

macro_rules! switch_on_term {
    ($v:expr, $c:expr, $l:expr, $s:expr) => (
        Line::Indexing(IndexingInstruction::SwitchOnTerm($v, $c, $l, $s))
    )
}

macro_rules! indexed_try {
    ($i:expr) => (
        Line::IndexedChoice(IndexedChoiceInstruction::Try($i))
    )
}

macro_rules! retry {
    ($i:expr) => (
        Line::IndexedChoice(IndexedChoiceInstruction::Retry($i))
    )
}

macro_rules! trust {
    ($i:expr) => (
        Line::IndexedChoice(IndexedChoiceInstruction::Trust($i))
    )
}

macro_rules! get_constant {
    ($c:expr, $r:expr) => (
        FactInstruction::GetConstant(Level::Shallow, $c, $r)
    )
}

macro_rules! get_structure {
    ($atom:expr, $arity:expr, $r:expr, Some($fix:expr)) => (
        FactInstruction::GetStructure(ClauseType::Op(clause_name!($atom), $fix), $arity, $r)
    );
    ($atom:expr, $arity:expr, $r:expr, None) => (
        FactInstruction::GetStructure(ClauseType::Named(clause_name!($atom)), $arity, $r)
    )
}

macro_rules! functor_call {
    () => (
        Line::Control(ControlInstruction::FunctorCall)
    )
}

macro_rules! functor_execute {
    () => (
        Line::Control(ControlInstruction::FunctorExecute)
    )
}

macro_rules! unify_value {
    ($r:expr) => (
        FactInstruction::UnifyValue($r)
    )
}

macro_rules! unify_variable {
    ($r:expr) => (
        FactInstruction::UnifyVariable($r)
    )
}

macro_rules! unify_void {
    ($n:expr) => (
        FactInstruction::UnifyVoid($n)
    )
}

macro_rules! set_cp {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::SetCutPoint($r))
    )
}

macro_rules! get_cp {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::GetCutPoint($r))
    )
}

macro_rules! integer {
    ($i:expr) => (
        Constant::Number(Number::Integer(Rc::new(BigInt::from($i))))
    )
}

macro_rules! add {
    ($at_1:expr, $at_2:expr, $o:expr) => (
        Line::Arithmetic(ArithmeticInstruction::Add($at_1, $at_2, $o))
    )
}

macro_rules! sub {
    ($at_1:expr, $at_2:expr, $o:expr) => (
        Line::Arithmetic(ArithmeticInstruction::Sub($at_1, $at_2, $o))
    )
}

macro_rules! get_arg_call {
    () => (
        Line::BuiltIn(BuiltInInstruction::GetArgCall)
    )
}

macro_rules! get_arg_execute {
    () => (
        Line::BuiltIn(BuiltInInstruction::GetArgExecute)
    )
}

macro_rules! rc_integer {
    ($e:expr) => (
        Number::Integer(Rc::new(BigInt::from($e)))
    )
}

macro_rules! rc_atom {
    ($e:expr) => (
        Rc::new(String::from($e))
    )
}

macro_rules! infix {
    () => (
        Fixity::In
    )
}

macro_rules! display {
    () => (
        Line::Control(ControlInstruction::DisplayCall)
    )
}

macro_rules! dynamic_is {
    () => (
        Line::Control(ControlInstruction::DynamicIs)
    )
}

macro_rules! dynamic_num_test {
    ($cmp:expr) => (
        Line::BuiltIn(BuiltInInstruction::DynamicCompareNumber($cmp))
    )
}

macro_rules! cmp_gt {
    () => (
        CompareNumberQT::GreaterThan
    )
}

macro_rules! cmp_lt {
    () => (
        CompareNumberQT::LessThan
    )
}

macro_rules! cmp_gte {
    () => (
        CompareNumberQT::GreaterThanOrEqual
    )
}

macro_rules! cmp_lte {
    () => (
        CompareNumberQT::LessThanOrEqual
    )
}

macro_rules! cmp_ne {
    () => (
        CompareNumberQT::NotEqual
    )
}

macro_rules! cmp_eq {
    () => (
        CompareNumberQT::Equal
    )
}

macro_rules! jmp_call {
    ($arity:expr, $offset:expr) => (
        Line::Control(ControlInstruction::JmpByCall($arity, $offset))
    )
}

macro_rules! jmp_execute {
    ($arity:expr, $offset:expr) => (
        Line::Control(ControlInstruction::JmpByExecute($arity, $offset))
    )
}

macro_rules! get_list {
    ($lvl:expr, $r:expr) => (
        FactInstruction::GetList($lvl, $r)
    )
}

macro_rules! unify_constant {
    ($c:expr) => (
        FactInstruction::UnifyConstant($c)
    )
}

macro_rules! install_cleaner {
    () => (
        Line::BuiltIn(BuiltInInstruction::InstallCleaner)
    )
}

macro_rules! check_cp_execute {
    () => (
        Line::Control(ControlInstruction::CheckCpExecute)
    )
}

macro_rules! get_cleaner_call {
    () => (
        Line::Control(ControlInstruction::GetCleanerCall)
    )
}

macro_rules! restore_cut_policy {
    () => (
        Line::BuiltIn(BuiltInInstruction::RestoreCutPolicy)
    )
}

macro_rules! ground_execute {
    () => (
        Line::Control(ControlInstruction::GroundExecute)
    )
}

macro_rules! eq_execute {
    () => (
        Line::Control(ControlInstruction::EqExecute)
    )
}

macro_rules! not_eq_execute {
    () => (
        Line::Control(ControlInstruction::NotEqExecute)
    )
}

macro_rules! compare_term_execute {
    ($qt:expr) => (
        Line::Control(ControlInstruction::CompareTermExecute($qt))
    )
}

macro_rules! term_cmp_gt {
    () => (
        CompareTermQT::GreaterThan
    )
}

macro_rules! term_cmp_lt {
    () => (
        CompareTermQT::LessThan
    )
}

macro_rules! term_cmp_gte {
    () => (
        CompareTermQT::GreaterThanOrEqual
    )
}

macro_rules! term_cmp_lte {
    () => (
        CompareTermQT::LessThanOrEqual
    )
}

macro_rules! term_cmp_ne {
    () => (
        CompareTermQT::NotEqual
    )
}

macro_rules! term_cmp_eq {
    () => (
        CompareTermQT::Equal
    )
}

macro_rules! install_inference_counter {
    ($r1:expr, $r2:expr, $r3:expr) => (
        Line::BuiltIn(BuiltInInstruction::InstallInferenceCounter($r1, $r2, $r3))
    )
}

macro_rules! remove_inference_counter {
    ($r1:expr, $r2:expr) => (
        Line::BuiltIn(BuiltInInstruction::RemoveInferenceCounter($r1, $r2))
    )
}

macro_rules! inference_level {
    ($r1:expr, $r2:expr) => (
        Line::BuiltIn(BuiltInInstruction::InferenceLevel($r1, $r2))
    )
}

macro_rules! default_set_cp {
    ($r:expr) => (
        Line::BuiltIn(BuiltInInstruction::DefaultSetCutPoint($r))
    )
}

macro_rules! default_retry_me_else {
    ($o:expr) => (
        Line::BuiltIn(BuiltInInstruction::DefaultRetryMeElse($o))
    )
}

macro_rules! default_trust_me {
    () => (
        Line::BuiltIn(BuiltInInstruction::DefaultTrustMe)
    )
}

macro_rules! remove_call_policy_check {
    () => (
        Line::BuiltIn(BuiltInInstruction::RemoveCallPolicyCheck)
    )
}

macro_rules! compare_execute {
    () => (
        Line::Control(ControlInstruction::CompareExecute)
    )
}

macro_rules! module_decl {
    ($name:expr, $decls:expr) => (
        ModuleDecl { name: $name, exports: $decls }
    )
}

macro_rules! try_eval_session {
    ($e:expr) => (
        match $e {
            Ok(result) => result,
            Err(e) => return EvalSession::from(e)
        }
    )
}
