use prolog::ast::*;
use prolog::num::bigint::{BigInt};

use std::collections::HashMap;
use std::rc::Rc;

pub type PredicateKey = (Rc<Atom>, usize); // name, arity, type.

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateKeyType {
    BuiltIn,
    User
}

pub type OpDirKey = (Rc<Atom>, Fixity);
// name and fixity -> operator type and precedence.
pub type OpDir = HashMap<OpDirKey, (Specifier, usize)>;

pub type CodeDir = HashMap<PredicateKey, (PredicateKeyType, usize)>;

fn get_builtins() -> Code {
    vec![internal_call_n!(), // callN/N, 0.
         is_atomic!(temp_v!(1)), // atomic/1, 1.
         proceed!(),
         is_var!(temp_v!(1)),    // var/1, 3.
         proceed!(),
         allocate!(4), // catch/3, 5.
         fact![get_var_in_fact!(perm_v!(2), 1),
               get_var_in_fact!(perm_v!(3), 2),
               get_var_in_fact!(perm_v!(1), 3)],
         query![put_var!(perm_v!(4), 1)],
         get_current_block!(),
         query![put_value!(perm_v!(2), 1),
                put_value!(perm_v!(3), 2),
                put_value!(perm_v!(1), 3),
                put_unsafe_value!(4, 4)],
         deallocate!(),
         goto!(12, 4), // goto catch/4.
         try_me_else!(10), // catch/4, 12.
         allocate!(3),
         fact![get_var_in_fact!(perm_v!(3), 1),
               get_var_in_fact!(perm_v!(2), 4)],
         query![put_var!(perm_v!(1), 1)],
         install_new_block!(),
         query![put_value!(perm_v!(3), 1)],
         call_n!(1),
         query![put_value!(perm_v!(2), 1),
                put_unsafe_value!(1, 2)],
         deallocate!(),
         goto!(44, 2), //21: goto end_block/2.
         trust_me!(),
         allocate!(3),
         fact![get_var_in_fact!(perm_v!(2), 2),
               get_var_in_fact!(perm_v!(1), 3)],
         query![get_var_in_query!(temp_v!(2), 1),
                put_value!(temp_v!(4), 1)],
         reset_block!(),
         query![put_var!(perm_v!(3), 1)],
         get_ball!(),
         query![put_unsafe_value!(3, 1),
                put_value!(perm_v!(2), 2),
                put_value!(perm_v!(1), 3)],
         deallocate!(),
         goto!(32, 2), // goto handle_ball/2.
         try_me_else!(10), // handle_ball/2, 32.
         allocate!(2),
         get_level!(),
         fact![get_var_in_fact!(perm_v!(2), 3)],
         unify!(),
         cut!(),
         erase_ball!(),
         query![put_value!(perm_v!(2), 1)],
         deallocate!(),
         execute_n!(1),
         trust_me!(),
         unwind_stack!(),
         try_me_else!(9), // end_block/2, 44.
         allocate!(1),
         fact![get_var_in_fact!(perm_v!(1), 1)],
         query![put_value!(temp_v!(2), 1)],
         clean_up_block!(),
         query![put_value!(perm_v!(1), 1)],
         deallocate!(),
         reset_block!(),
         proceed!(),
         trust_me!(), // 53.
         allocate!(0),
         query![get_var_in_query!(temp_v!(3), 1),
                put_value!(temp_v!(2), 1)],
         reset_block!(),
         deallocate!(),
         goto!(61, 0),
         set_ball!(), // throw/1, 59.
         unwind_stack!(),
         fail!(), // false/0, 61.
         try_me_else!(7), // not/1, 62.
         allocate!(1),
         get_level!(),
         call_n!(1),
         cut!(),
         deallocate!(),
         goto!(61, 0),
         trust_me!(),
         proceed!(),
         duplicate_term!(), // duplicate_term/2, 71.
         proceed!(),
         fact![get_value!(temp_v!(1), 2)], // =/2, 73.
         proceed!(),
         proceed!(), // true/0, 75.
         get_cp!(temp_v!(3)), // ','/2, 76
         try_me_else!(18), // ','/3, 77.
         switch_on_term!(4, 1, 0, 0),
         indexed_try!(4),
         retry!(7),
         trust!(10),
         try_me_else!(4),
         fact![get_constant!(Constant::from("!"), temp_v!(1)),
               get_structure!(String::from(","), 2, temp_v!(2)),
               unify_variable!(temp_v!(1)),
               unify_variable!(temp_v!(2))],
         set_cp!(temp_v!(3)),
         goto!(83, 3),
         retry_me_else!(4),
         fact![get_constant!(Constant::from("!"), temp_v!(1)),
               get_constant!(Constant::from("!"), temp_v!(2))],
         set_cp!(temp_v!(3)),
         proceed!(),
         trust_me!(),
         fact![get_constant!(Constant::from("!"), temp_v!(1))],
         set_cp!(temp_v!(3)),
         query![put_value!(temp_v!(2), 1)],
         execute_n!(1),
         retry_me_else!(8),
         allocate!(3),
         fact![get_structure!(String::from(","), 2, temp_v!(2)),
               unify_variable!(perm_v!(2)),
               unify_variable!(perm_v!(1)),
               get_var_in_fact!(perm_v!(3), 3)],
         neck_cut!(),
         call_n!(1),
         query![put_unsafe_value!(2, 1),
                put_unsafe_value!(1, 2),
                put_value!(perm_v!(3), 3)],
         deallocate!(),
         goto!(83, 3),
         retry_me_else!(10),
         allocate!(1),
         get_level!(),
         fact![get_constant!(Constant::from("!"), temp_v!(2)),
               get_var_in_fact!(perm_v!(1), 3)],
         neck_cut!(),
         call_n!(1),
         query![put_value!(perm_v!(1), 1)],
         set_cp!(temp_v!(1)),
         deallocate!(),
         proceed!(),
         trust_me!(),
         allocate!(1),
         fact![get_var_in_fact!(perm_v!(1), 2)],
         call_n!(1),
         query![put_value!(perm_v!(1), 1)],
         deallocate!(),
         execute_n!(1),
         get_cp!(temp_v!(3)), // ';'/2, 120.
         try_me_else!(12),
         switch_on_term!(4, 0, 0, 1),
         indexed_try!(3),
         trust!(5),
         try_me_else!(3),
         fact![get_structure!(String::from("->"), 2, temp_v!(1)),
               unify_variable!(temp_v!(1)),
               unify_variable!(temp_v!(2))],
         goto!(139, 3),
         trust_me!(),
         fact![get_structure!(String::from("->"), 2, temp_v!(1)),
               unify_void!(2)],
         query![put_value!(temp_v!(2), 1)],
         neck_cut!(),
         execute_n!(1),
         retry_me_else!(2),
         execute_n!(1),
         trust_me!(),
         query![put_value!(temp_v!(2), 1)],
         execute_n!(1),
         get_cp!(temp_v!(3)), // '->'/2, 138.
         allocate!(2), // '->'/3, 139.
         fact![get_var_in_fact!(perm_v!(1), 2),
               get_var_in_fact!(perm_v!(2), 3)], // cut point.
         call_n!(1),
         set_cp!(perm_v!(2)),
         query![put_unsafe_value!(1, 1)],
         deallocate!(),
         execute_n!(1),
         functor_execute!(), // functor/3, 146.
         is_integer!(temp_v!(1)), // integer/1, 147.
         proceed!(),
         get_arg!(), // get_arg/3, 149.
         try_me_else!(10), // arg/3, 150.
         allocate!(4),
         fact![get_var_in_fact!(perm_v!(1), 1),
               get_var_in_fact!(perm_v!(2), 2),
               get_var_in_fact!(perm_v!(4), 3)],
         is_var!(perm_v!(1)),
         neck_cut!(),
         query![put_value!(perm_v!(2), 1),
                put_var!(temp_v!(4), 2),
                put_var!(perm_v!(3), 3)],
         functor_call!(),
         query![put_value!(perm_v!(1), 1),
                put_constant!(Level::Shallow, integer!(1), temp_v!(2)),
                put_unsafe_value!(3, 3),
                put_value!(perm_v!(2), 4),
                put_value!(perm_v!(4), 5)],
         deallocate!(),
         goto!(173, 5), // goto arg_/3.
         retry_me_else!(10),
         allocate!(3),
         fact![get_var_in_fact!(perm_v!(1), 1),
               get_var_in_fact!(perm_v!(2), 2),
               get_var_in_fact!(perm_v!(3), 3)],
         is_integer!(perm_v!(1)),
         neck_cut!(),
         query![put_value!(perm_v!(2), 1),
                put_var!(temp_v!(4), 2),
                put_var!(temp_v!(3), 3)],
         functor_call!(),
         query![put_value!(perm_v!(1), 1),
                put_value!(perm_v!(2), 2),
                put_value!(perm_v!(3), 3)],
         deallocate!(),
         goto!(149, 3), // goto get_arg/3.
         trust_me!(),
         query![get_var_in_query!(temp_v!(4), 1),
                put_structure!(Level::Shallow,
                               String::from("type_error"),
                               1,
                               temp_v!(1)),
                set_constant!(Constant::Atom(rc_atom!("integer_expected")))],
         goto!(59, 1), // goto throw/1.
         try_me_else!(5), // arg_/3, 173.
         fact![get_value!(temp_v!(1), 2),
               get_value!(temp_v!(1), 3)],
         neck_cut!(),
         query![put_value!(temp_v!(4), 2),
                put_value!(temp_v!(5), 3)],
         goto!(149, 3), // goto get_arg/3.
         retry_me_else!(4),
         fact![get_value!(temp_v!(1), 2)],
         query![put_value!(temp_v!(4), 2),
                get_var_in_query!(temp_v!(6), 3),
                put_value!(temp_v!(5), 3)],
         goto!(149, 3), // goto get_arg/3
         trust_me!(),
         allocate!(5),
         fact![get_var_in_fact!(perm_v!(2), 1),
               get_var_in_fact!(perm_v!(4), 3),
               get_var_in_fact!(perm_v!(3), 4),
               get_var_in_fact!(perm_v!(5), 5)],
         compare_number_instr!(CompareNumberQT::LessThan,
                               ArithmeticTerm::Reg(temp_v!(2)),
                               ArithmeticTerm::Reg(perm_v!(4))),
         add!(ArithmeticTerm::Reg(temp_v!(2)),
              ArithmeticTerm::Number(rc_integer!(1)),
              1),
         query![put_var!(perm_v!(1), 1)],
         is_call!(perm_v!(1), interm!(1)),
         query![put_value!(perm_v!(2), 1),
                put_unsafe_value!(1, 2),
                put_value!(perm_v!(4), 3),
                put_value!(perm_v!(3), 4),
                put_value!(perm_v!(5), 5)],
         deallocate!(),
         goto!(173, 3) // goto arg_/3.
    ]
}

pub fn build_code_dir() -> (Code, CodeDir, OpDir)
{
    let mut code_dir = HashMap::new();
    let mut op_dir   = HashMap::new();

    let builtin_code = get_builtins();

    op_dir.insert((rc_atom!(":-"), Fixity::In),   (XFX, 1200));
    op_dir.insert((rc_atom!(":-"), Fixity::Pre),  (FX, 1200));
    op_dir.insert((rc_atom!("?-"), Fixity::Pre),  (FX, 1200));

    // control operators.
    op_dir.insert((rc_atom!("\\+"), Fixity::Pre), (FY, 900));
    op_dir.insert((rc_atom!("="), Fixity::In), (XFX, 700));

    // arithmetic operators.
    op_dir.insert((rc_atom!("is"), Fixity::In), (XFX, 700));
    op_dir.insert((rc_atom!("+"), Fixity::In), (YFX, 500));
    op_dir.insert((rc_atom!("-"), Fixity::In), (YFX, 500));
    op_dir.insert((rc_atom!("/\\"), Fixity::In), (YFX, 500));
    op_dir.insert((rc_atom!("\\/"), Fixity::In), (YFX, 500));
    op_dir.insert((rc_atom!("xor"), Fixity::In), (YFX, 500));
    op_dir.insert((rc_atom!("//"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("/"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("div"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("*"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("-"), Fixity::Pre), (FY, 200));
    op_dir.insert((rc_atom!("rdiv"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("<<"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!(">>"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("mod"), Fixity::In), (YFX, 400));
    op_dir.insert((rc_atom!("rem"), Fixity::In), (YFX, 400));

    // arithmetic comparison operators.
    op_dir.insert((rc_atom!(">"), Fixity::In), (XFX, 700));
    op_dir.insert((rc_atom!("<"), Fixity::In), (XFX, 700));
    op_dir.insert((rc_atom!("=\\="), Fixity::In), (XFX, 700));
    op_dir.insert((rc_atom!("=:="), Fixity::In), (XFX, 700));
    op_dir.insert((rc_atom!(">="), Fixity::In), (XFX, 700));
    op_dir.insert((rc_atom!("=<"), Fixity::In), (XFX, 700));

    // control operators.
    op_dir.insert((rc_atom!(";"), Fixity::In), (XFY, 1100));
    op_dir.insert((rc_atom!("->"), Fixity::In), (XFY, 1050));

    // there are 63 registers in the VM, so call/N is defined for all 0 <= N <= 62
    // (an extra register is needed for the predicate name)
    for arity in 0 .. 63 {
        code_dir.insert((rc_atom!("call"), arity), (PredicateKeyType::BuiltIn, 0));
    }

    code_dir.insert((rc_atom!("atomic"), 1), (PredicateKeyType::BuiltIn, 1));
    code_dir.insert((rc_atom!("var"), 1), (PredicateKeyType::BuiltIn, 3));
    code_dir.insert((rc_atom!("false"), 0), (PredicateKeyType::BuiltIn, 61));
    code_dir.insert((rc_atom!("\\+"), 1), (PredicateKeyType::BuiltIn, 62));
    code_dir.insert((rc_atom!("duplicate_term"), 2), (PredicateKeyType::BuiltIn, 71));
    code_dir.insert((rc_atom!("catch"), 3), (PredicateKeyType::BuiltIn, 5));
    code_dir.insert((rc_atom!("throw"), 1), (PredicateKeyType::BuiltIn, 59));
    code_dir.insert((rc_atom!("="), 2), (PredicateKeyType::BuiltIn, 73));
    code_dir.insert((rc_atom!("true"), 0), (PredicateKeyType::BuiltIn, 75));

    code_dir.insert((rc_atom!(","), 2), (PredicateKeyType::BuiltIn, 76));
    code_dir.insert((rc_atom!(";"), 2), (PredicateKeyType::BuiltIn, 120));
    code_dir.insert((rc_atom!("->"), 2), (PredicateKeyType::BuiltIn, 138));

    code_dir.insert((rc_atom!("functor"), 3), (PredicateKeyType::BuiltIn, 146));
    code_dir.insert((rc_atom!("arg"), 3), (PredicateKeyType::BuiltIn, 150));
    code_dir.insert((rc_atom!("integer"), 1), (PredicateKeyType::BuiltIn, 147));

    (builtin_code, code_dir, op_dir)
}
