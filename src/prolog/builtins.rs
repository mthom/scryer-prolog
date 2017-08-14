use prolog::ast::*;

use std::collections::HashMap;

pub type PredicateKey = (Atom, usize); // name, arity, type.

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateKeyType {
    BuiltIn,
    User
}

pub type CodeDir = HashMap<PredicateKey, (PredicateKeyType, usize)>;
     
fn get_builtins() -> Code {    
    vec![internal_call_n!(), // callN/N, 0.
         is_atomic!(), // atomic/1, 1.
         proceed!(),
         is_var!(),    // var/1, 3.
         proceed!(),
         allocate!(4), // catch/3, 5.
         query![get_var_in_query!(perm_v!(2), 1),
                get_var_in_query!(perm_v!(3), 2),
                get_var_in_query!(perm_v!(1), 3),
                put_var!(perm_v!(4), 1)],
         get_current_block!(),
         query![put_value!(perm_v!(2), 1),
                put_value!(perm_v!(3), 2),
                put_value!(perm_v!(1), 3),
                put_unsafe_value!(4, 4)],
         deallocate!(),
         goto!(11, 4),
         try_me_else!(9), // catch/4, 11.
         allocate!(3),
         query![get_var_in_query!(perm_v!(3), 1),
                get_var_in_query!(perm_v!(2), 4),
                put_var!(perm_v!(1), 1)],
         install_new_block!(),
         query![put_value!(perm_v!(3), 1)],
         call_n!(1),
         query![put_value!(perm_v!(2), 1),
                put_unsafe_value!(1, 2)],
         deallocate!(),
         goto!(42, 2), // goto end_block/2 at 42.
         trust_me!(),
         allocate!(4),
         query![get_var_in_query!(perm_v!(2), 2),
                get_var_in_query!(perm_v!(1), 3),
                get_var_in_query!(temp_v!(2), 1),
                put_value!(temp_v!(4), 1)],
         reset_block!(),
         query![put_var!(perm_v!(4), 1)],
         get_ball!(),
         query![put_value!(perm_v!(4), 1),
                put_var!(perm_v!(3), 2)],
         copy_term!(),
         query![put_unsafe_value!(3, 1),
                put_value!(perm_v!(2), 2),
                put_value!(perm_v!(1), 3)],
         deallocate!(),
         goto!(31, 2), // goto handle_ball/2.
         try_me_else!(10), // handle_ball/2, 31.
         allocate!(2),
         get_level!(),
         query![get_var_in_query!(perm_v!(2), 3)],
         unify!(),
         cut!(non_terminal!()),
         query![put_value!(perm_v!(2), 1)],
         deallocate!(),
         execute_n!(1),
         trust_me!(),
         unwind_stack!(),
         try_me_else!(8), // end_block/2, 42.
         allocate!(1),
         query![get_var_in_query!(perm_v!(1), 1),
                put_value!(temp_v!(2), 1)],
         clean_up_block!(),
         query![put_value!(perm_v!(1), 1)],
         deallocate!(),
         reset_block!(),
         proceed!(),
         trust_me!(),
         allocate!(0),
         query![get_var_in_query!(temp_v!(3), 1),
                put_value!(temp_v!(2), 1)],
         reset_block!(),
         deallocate!(),
         goto!(58, 0), // goto false.
         set_ball!(), // throw/1, 56.
         unwind_stack!(),         
         fail!(), // false/0, 58.
         proceed!(),
         try_me_else!(7), // not/1, 60.
         allocate!(1),
         get_level!(),
         call_n!(1),
         cut!(non_terminal!()),
         deallocate!(),
         goto!(58, 0), // goto false.
         trust_me!(),
         proceed!(),
         copy_term!(), // copy_term/2, 69.
         proceed!()]
}

pub fn build_code_dir() -> (Code, CodeDir) {
    let mut code_dir = HashMap::new();
    let builtin_code = get_builtins();
    
    // there are 63 registers in the VM, so call/N is defined for all 0 <= N <= 62
    // (an extra register is needed for the predicate name)
    for arity in 0 .. 63 {
        code_dir.insert((String::from("call"), arity), (PredicateKeyType::BuiltIn, 0));
    }

    code_dir.insert((String::from("atomic"), 1), (PredicateKeyType::BuiltIn, 1));
    code_dir.insert((String::from("var"), 1), (PredicateKeyType::BuiltIn, 3));
    code_dir.insert((String::from("false"), 0), (PredicateKeyType::BuiltIn, 58));
    code_dir.insert((String::from("not"), 1), (PredicateKeyType::BuiltIn, 60));
    code_dir.insert((String::from("copy_term"), 2), (PredicateKeyType::BuiltIn, 69));
    code_dir.insert((String::from("catch"), 3), (PredicateKeyType::BuiltIn, 5));
    code_dir.insert((String::from("throw"), 1), (PredicateKeyType::BuiltIn, 56));

    (builtin_code, code_dir)
}
