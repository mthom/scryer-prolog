use prolog::ast::*;

use std::collections::HashMap;

pub type PredicateKey = (Atom, usize); // name, arity, type.

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateKeyType {
    BuiltIn,
    User
}

pub type OpDirKey = (Atom, Fixity);
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
         cut!(non_terminal!()),
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
         cut!(non_terminal!()),
         deallocate!(),
         goto!(61, 0),
         trust_me!(),
         proceed!(),
         duplicate_term!(), // duplicate_term/2, 71.
         proceed!(),
         fact![get_value!(temp_v!(1), 2)], // =/2, 73.
         proceed!(),
         proceed!() // true/0, 75.
    ]
}

pub fn build_code_dir() -> (Code, CodeDir, OpDir)
{
    let mut code_dir = HashMap::new();
    let mut op_dir   = HashMap::new();

    let builtin_code = get_builtins();

    op_dir.insert((String::from(":-"), Fixity::In),   (XFX, 1200));
    op_dir.insert((String::from(":-"), Fixity::Pre),  (FX, 1200));
    op_dir.insert((String::from("?-"), Fixity::Pre),  (FX, 1200));

    // control operators.
    op_dir.insert((String::from("\\+"), Fixity::Pre), (FY, 900));
    op_dir.insert((String::from("="), Fixity::In), (XFX, 700));

    // arithmetic operators.
    op_dir.insert((String::from("is"), Fixity::In), (XFX, 700));
    op_dir.insert((String::from("+"), Fixity::In), (YFX, 500));
    op_dir.insert((String::from("-"), Fixity::In), (YFX, 500));
    op_dir.insert((String::from("/\\"), Fixity::In), (YFX, 500));
    op_dir.insert((String::from("\\/"), Fixity::In), (YFX, 500));
    op_dir.insert((String::from("xor"), Fixity::In), (YFX, 500));
    op_dir.insert((String::from("//"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("/"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("div"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("*"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("-"), Fixity::Pre), (FY, 200));
    op_dir.insert((String::from("rdiv"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("<<"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from(">>"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("mod"), Fixity::In), (YFX, 400));
    op_dir.insert((String::from("rem"), Fixity::In), (YFX, 400));
    
    // there are 63 registers in the VM, so call/N is defined for all 0 <= N <= 62
    // (an extra register is needed for the predicate name)
    for arity in 0 .. 63 {
        code_dir.insert((String::from("call"), arity), (PredicateKeyType::BuiltIn, 0));
    }

    code_dir.insert((String::from("atomic"), 1), (PredicateKeyType::BuiltIn, 1));
    code_dir.insert((String::from("var"), 1), (PredicateKeyType::BuiltIn, 3));
    code_dir.insert((String::from("false"), 0), (PredicateKeyType::BuiltIn, 61));
    code_dir.insert((String::from("\\+"), 1), (PredicateKeyType::BuiltIn, 62));
    code_dir.insert((String::from("duplicate_term"), 2), (PredicateKeyType::BuiltIn, 71));
    code_dir.insert((String::from("catch"), 3), (PredicateKeyType::BuiltIn, 5));
    code_dir.insert((String::from("throw"), 1), (PredicateKeyType::BuiltIn, 59));
    code_dir.insert((String::from("="), 2), (PredicateKeyType::BuiltIn, 73));
    code_dir.insert((String::from("true"), 0), (PredicateKeyType::BuiltIn, 75));

    (builtin_code, code_dir, op_dir)
}
