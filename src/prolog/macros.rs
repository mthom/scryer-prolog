macro_rules! tabled_rc {
    ($e:expr, $tbl:expr) => (
        TabledRc::new(String::from($e), $tbl.clone())
    )
}

macro_rules! atom {
    ($e:expr, $tbl:expr) => (
        Constant::Atom(tabled_rc!($e, $tbl))
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

macro_rules! compare_number {
    ($cmp: expr, $terms: expr) => (
        QueryTerm::Inlined(InlinedQueryTerm::CompareNumber($cmp, $terms))
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
    ($name:expr, $tbl:expr) => (
        HeapCellValue::Addr(Addr::Con(atom!($name, $tbl)))
    )
}

macro_rules! functor {
    ($tbl:expr, $name:expr, $len:expr, [$($args:expr),*]) => {{
        if $len > 0 {
            vec![ HeapCellValue::NamedStr($len,
                                          tabled_rc!($name, $tbl),
                                          None),
                  $($args),* ]
        } else {
            vec![ heap_atom!($name, $tbl) ]
        }
    }}
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
    ($tbl:expr, $lvl:expr, $name:expr, $arity:expr, $r:expr, $fix:expr) => (
        QueryInstruction::PutStructure($lvl, tabled_rc!($name, $tbl), $arity, $r, $fix)
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
    () => (
        Line::Cut(CutInstruction::Cut)
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

macro_rules! goto {
    ($line:expr, $arity:expr) => (
        Line::Control(ControlInstruction::Goto($line, $arity))
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
    () => (
        Line::Cut(CutInstruction::GetLevel)
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
    ($tbl:expr, $atom:expr, $arity:expr, $r:expr, $fix:expr) => (
        FactInstruction::GetStructure(Level::Shallow,
                                      tabled_rc!($atom, $tbl),
                                      $arity,
                                      $r,
                                      $fix)
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

macro_rules! get_arg {
    () => (
        Line::BuiltIn(BuiltInInstruction::GetArg)
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
        Line::BuiltIn(BuiltInInstruction::DynamicIs)
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
