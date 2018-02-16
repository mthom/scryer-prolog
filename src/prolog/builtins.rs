use prolog::ast::*;
use prolog::num::bigint::{BigInt};
use prolog::tabled_rc::*;

use std::collections::HashMap;
use std::rc::Rc;

pub type PredicateKey = (TabledRc<Atom>, usize); // name, arity, type.

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateKeyType {
    BuiltIn,
    User
}

pub type OpDirKey = (TabledRc<Atom>, Fixity);
// name and fixity -> operator type and precedence.
pub type OpDir = HashMap<OpDirKey, (Specifier, usize)>;

pub type CodeDir = HashMap<PredicateKey, (PredicateKeyType, usize)>;

fn get_builtins(atom_tbl: TabledData<Atom>) -> Code {
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
         goto_execute!(12, 4), // goto catch/4.
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
         goto_execute!(44, 2), //21: goto end_block/2.
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
         goto_execute!(32, 2), // goto handle_ball/2.
         try_me_else!(10), // handle_ball/2, 32.
         allocate!(2),
         get_level!(perm_v!(1)),
         fact![get_var_in_fact!(perm_v!(2), 3)],
         unify!(),
         cut!(perm_v!(1)),
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
         goto_execute!(61, 0),
         set_ball!(), // throw/1, 59.
         unwind_stack!(),
         fail!(), // false/0, 61.
         try_me_else!(7), // not/1, 62.
         allocate!(1),
         get_level!(perm_v!(1)),
         call_n!(1),
         cut!(perm_v!(1)),
         deallocate!(),
         goto_execute!(61, 0),
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
         fact![get_constant!(atom!("!", atom_tbl), temp_v!(1)),
               get_structure!(atom_tbl, ",", 2, temp_v!(2), Some(infix!())),
               unify_variable!(temp_v!(1)),
               unify_variable!(temp_v!(2))],
         set_cp!(temp_v!(3)),
         goto_execute!(83, 3),
         retry_me_else!(4),
         fact![get_constant!(atom!("!", atom_tbl), temp_v!(1)),
               get_constant!(atom!("!", atom_tbl), temp_v!(2))],
         set_cp!(temp_v!(3)),
         proceed!(),
         trust_me!(),
         fact![get_constant!(atom!("!", atom_tbl), temp_v!(1))],
         set_cp!(temp_v!(3)),
         query![put_value!(temp_v!(2), 1)],
         execute_n!(1),
         retry_me_else!(8),
         allocate!(3),
         fact![get_structure!(atom_tbl, ",", 2, temp_v!(2), Some(infix!())),
               unify_variable!(perm_v!(2)),
               unify_variable!(perm_v!(1)),
               get_var_in_fact!(perm_v!(3), 3)],
         neck_cut!(),
         call_n!(1),
         query![put_unsafe_value!(2, 1),
                put_unsafe_value!(1, 2),
                put_value!(perm_v!(3), 3)],
         deallocate!(),
         goto_execute!(83, 3),
         retry_me_else!(10),
         allocate!(2),
         get_level!(perm_v!(2)),
         fact![get_constant!(atom!("!", atom_tbl), temp_v!(2)),
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
         fact![get_structure!(atom_tbl, "->", 2, temp_v!(1), Some(infix!())),
               unify_variable!(temp_v!(1)),
               unify_variable!(temp_v!(2))],
         goto_execute!(139, 3),
         trust_me!(),
         fact![get_structure!(atom_tbl, "->", 2, temp_v!(1), Some(infix!())),
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
         get_arg_execute!(), // get_arg/3, 149.
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
         goto_execute!(173, 5), // goto arg_/3.
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
         goto_execute!(149, 3), // goto get_arg/3.
         trust_me!(),
         query![get_var_in_query!(temp_v!(4), 1),
                put_structure!(atom_tbl,
                               Level::Shallow,
                               String::from("type_error"),
                               1,
                               temp_v!(1),
                               None),
                set_constant!(atom!("integer_expected", atom_tbl))],
         goto_execute!(59, 1), // goto throw/1.
         try_me_else!(5), // arg_/5, 173.
         fact![get_value!(temp_v!(1), 2),
               get_value!(temp_v!(1), 3)],
         neck_cut!(),
         query![put_value!(temp_v!(4), 2),
                put_value!(temp_v!(5), 3)],
         goto_execute!(149, 3), // goto get_arg/3.
         retry_me_else!(4),
         fact![get_value!(temp_v!(1), 2)],
         query![put_value!(temp_v!(4), 2),
                get_var_in_query!(temp_v!(6), 3),
                put_value!(temp_v!(5), 3)],
         goto_execute!(149, 3), // goto get_arg/3
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
         goto_execute!(173, 5), // goto arg_/5.
         display!(), // display/1, 192.
         proceed!(),
         dynamic_is!(), // is/2, 194.
         proceed!(),
         dynamic_num_test!(cmp_gt!()), // >/2, 196.
         proceed!(),
         dynamic_num_test!(cmp_lt!()), // </2, 198.
         proceed!(),
         dynamic_num_test!(cmp_gte!()), // >=/2, 200.
         proceed!(),
         dynamic_num_test!(cmp_lte!()), // <=/2, 202.
         proceed!(),
         dynamic_num_test!(cmp_ne!()), // =\=, 204.
         proceed!(),
         dynamic_num_test!(cmp_eq!()), // =:=, 206.
         proceed!(),
         try_me_else!(5), // =.., 208.
         fact![get_var_in_fact!(temp_v!(3), 1),
               get_list!(Level::Shallow, temp_v!(2)),
               unify_value!(temp_v!(3)),
               unify_constant!(Constant::EmptyList)],
         is_atomic!(temp_v!(3)),
         neck_cut!(),
         proceed!(),
         retry_me_else!(11),
         allocate!(4),
         get_level!(perm_v!(1)),
         fact![get_var_in_fact!(perm_v!(3), 1),
               get_list!(Level::Shallow, temp_v!(2)),
               unify_variable!(temp_v!(2)),
               unify_variable!(perm_v!(4))],
         is_var!(perm_v!(4)),
         query![put_value!(perm_v!(3), 1),
                put_var!(perm_v!(2), 3)],
         functor_call!(),
         cut!(perm_v!(1)),
         query![put_unsafe_value!(4, 1),
                put_value!(perm_v!(3), 2),
                put_constant!(Level::Shallow, integer!(1), temp_v!(3)),
                put_unsafe_value!(2, 4)],
         deallocate!(),
         goto_execute!(236, 4), // goto get_args/4.
         trust_me!(),
         allocate!(5),
         get_level!(perm_v!(1)),
         fact![get_var_in_fact!(perm_v!(3), 1),
               get_list!(Level::Shallow, temp_v!(2)),
               unify_variable!(perm_v!(5)),
               unify_variable!(perm_v!(4))],
         query![put_value!(perm_v!(4), 1),
                put_var!(perm_v!(2), 2)],
         goto_call!(261, 2), // goto length/2.
         query![put_value!(perm_v!(3), 1),
                put_value!(perm_v!(5), 2),
                put_value!(perm_v!(2), 3)],
         functor_call!(),
         cut!(perm_v!(1)),
         query![put_unsafe_value!(4, 1),
                put_value!(perm_v!(3), 2),
                put_constant!(Level::Shallow, integer!(1), temp_v!(3)),
                put_unsafe_value!(2, 4)],
         deallocate!(),
         goto_execute!(236, 4), // goto get_args/4, 236.
         try_me_else!(5), // get_args/4, 236.
         fact![get_var_in_fact!(temp_v!(5), 1),
               get_constant!(integer!(0), temp_v!(4))],
         neck_cut!(),
         query![put_value!(temp_v!(5), 1),
                put_constant!(Level::Shallow, Constant::EmptyList, temp_v!(2))],
         goto_execute!(73, 2), // goto =/2.
         trust_me!(),
         switch_on_term!(3, 0, 1, 0),
         indexed_try!(3),
         trust!(7),
         try_me_else!(5),
         fact![get_list!(Level::Shallow, temp_v!(1)),
               unify_variable!(temp_v!(5)),
               unify_constant!(Constant::EmptyList),
               get_var_in_fact!(temp_v!(6), 2),
               get_var_in_fact!(temp_v!(1), 3),
               get_value!(temp_v!(1), 4)],
         neck_cut!(),
         query![put_value!(temp_v!(6), 2),
                put_value!(temp_v!(5), 3)],
         get_arg_execute!(),
         trust_me!(),
         allocate!(5),
         fact![get_list!(Level::Shallow, temp_v!(1)),
               unify_variable!(temp_v!(5)),
               unify_variable!(perm_v!(4)),
               get_var_in_fact!(perm_v!(3), 2),
               get_var_in_fact!(perm_v!(5), 3),
               get_var_in_fact!(perm_v!(1), 4)],
         query![put_value!(perm_v!(5), 1),
                put_value!(perm_v!(3), 2),
                put_value!(temp_v!(5), 3)],
         get_arg_call!(),
         add!(ArithmeticTerm::Reg(perm_v!(5)),
              ArithmeticTerm::Number(rc_integer!(1)),
              1),
         query![put_var!(perm_v!(2), 1)],
         is_call!(perm_v!(2), ArithmeticTerm::Interm(1)),
         query![put_unsafe_value!(4, 1),
                put_value!(perm_v!(3), 2),
                put_unsafe_value!(2, 3),
                put_value!(perm_v!(1), 4)],
         deallocate!(),
         goto_execute!(236, 4), // goto get_args/4, 236.
         try_me_else!(6), // length/2, 261.
         fact![get_var_in_fact!(temp_v!(4), 1),
               get_var_in_fact!(temp_v!(3), 2)],
         is_var!(temp_v!(3)),
         neck_cut!(),
         query![put_value!(temp_v!(4), 1),
                put_constant!(Level::Shallow, integer!(0), temp_v!(2))],
         goto_execute!(281, 3), // goto length/3, 281.
         retry_me_else!(10),
         allocate!(1),
         get_level!(perm_v!(1)),
         fact![get_var_in_fact!(temp_v!(4), 1),
               get_var_in_fact!(temp_v!(3), 2)],
         is_integer!(temp_v!(3)),
         query![put_value!(temp_v!(4), 1),
                put_constant!(Level::Shallow, integer!(0), temp_v!(2))],
         goto_call!(281, 3), // goto length/3, 281.
         cut!(perm_v!(1)),
         deallocate!(),
         proceed!(),
         trust_me!(),
         fact![get_var_in_fact!(temp_v!(3), 1),
               get_var_in_fact!(temp_v!(4), 2)],
         query![put_structure!(atom_tbl,
                               Level::Shallow,
                               String::from("type_error"),
                               2,
                               temp_v!(1),
                               None),
                set_constant!(atom!("integer_expected", atom_tbl)),
                set_value!(temp_v!(4))],
         goto_execute!(59, 1), // goto throw/1, 59.
         switch_on_term!(1,2,5,0), // length/3, 281.
         try_me_else!(3),
         fact![get_constant!(Constant::EmptyList, temp_v!(1)),
               get_var_in_fact!(temp_v!(4), 2),
               get_value!(temp_v!(4), 3)],
         proceed!(),
         trust_me!(),
         allocate!(3),
         fact![get_list!(Level::Shallow, temp_v!(1)),
               unify_void!(1),
               unify_variable!(perm_v!(1)),
               get_var_in_fact!(temp_v!(4), 2),
               get_var_in_fact!(perm_v!(3), 3)],
         add!(ArithmeticTerm::Reg(temp_v!(4)),
              ArithmeticTerm::Number(rc_integer!(1)),
              1),
         query![put_var!(perm_v!(2), 1)],
         is_call!(perm_v!(2), ArithmeticTerm::Interm(1)),
         query![put_unsafe_value!(1, 1),
                put_unsafe_value!(2, 2),
                put_value!(perm_v!(3), 3)],
         deallocate!(),
         goto_execute!(281, 3), // goto length/3, 281.
         allocate!(4), // setup_call_cleanup/3, 294.
         get_level!(perm_v!(1)),
         fact![get_var_in_fact!(perm_v!(2), 2),
               get_var_in_fact!(perm_v!(3), 3)],
         call_n!(1),
         cut!(perm_v!(1)),
         query![put_var!(perm_v!(4), 1)],
         get_current_block!(),
         query![put_value!(perm_v!(3), 1),
                put_unsafe_value!(4, 2),
                put_value!(perm_v!(2), 3)],
         deallocate!(),
         jmp_execute!(3, 1),
         try_me_else!(5), // 304.
         is_var!(temp_v!(1)),
         neck_cut!(),
         query![put_constant!(Level::Shallow, atom!("instantiation_error", atom_tbl),
                              temp_v!(1))],
         goto_execute!(59, 1),
         trust_me!(),
         query![get_var_in_query!(temp_v!(4), 2),
                put_value!(temp_v!(3), 2),
                get_var_in_query!(temp_v!(5), 3),
                put_value!(temp_v!(4), 3)],
         goto_execute!(312, 3),
         try_me_else!(13), // sgc_helper/3, 312.
         allocate!(4),
         fact![get_var_in_fact!(perm_v!(4), 1),
               get_var_in_fact!(perm_v!(3), 2),
               get_var_in_fact!(perm_v!(2), 3)],
         get_level!(perm_v!(1)),
         query![put_value!(perm_v!(4), 1)],
         install_cleaner!(),
         query![put_var!(temp_v!(2), 1)],
         install_new_block!(),
         query![put_value!(perm_v!(3), 1)],
         call_n!(1),
         query![put_value!(perm_v!(2), 1),
                put_value!(perm_v!(1), 2)],
         deallocate!(),
         check_cp_execute!(),
         retry_me_else!(12),
         allocate!(2),
         query![put_value!(temp_v!(3), 1)],
         reset_block!(),
         query![put_var!(perm_v!(1), 1)],
         get_ball!(),
         get_level!(perm_v!(2)),
         set_cp!(perm_v!(2)),
         goto_call!(342, 0), // goto run_cleaners_with_handling/0, 342.
         query![put_unsafe_value!(1, 1)],
         deallocate!(),
         goto_execute!(59, 1), // goto throw/1, 59.
         trust_me!(),
         allocate!(0),
         goto_call!(354, 0), // goto run_cleaners_without_handling/0, 354.
         deallocate!(),
         fail!(),
         try_me_else!(10), // run_cleaners_with_handling/0, 342.
         allocate!(2),
         get_level!(perm_v!(1)),
         query![put_var!(perm_v!(2), 1)],
         get_cleaner_call!(),
         query![put_value!(perm_v!(2), 1),
                put_var!(temp_v!(4), 2),
                put_constant!(Level::Shallow, atom!("true", atom_tbl), temp_v!(3))],
         goto_call!(5, 3), // goto catch/3, 5.
         set_cp!(perm_v!(1)),
         deallocate!(),
         goto_execute!(342, 0), // goto run_cleaners_with_handling/0, 342.
         trust_me!(),
         goto_execute!(382, 0), // goto restore_cut_points/0, 382.
         try_me_else!(10), // run_cleaners_without_handling/1, 354.
         allocate!(2),
         get_level!(perm_v!(1)),
         query![put_var!(perm_v!(2), 1)],
         get_cleaner_call!(),
         query![put_value!(perm_v!(2), 1)],
         call_n!(1),
         set_cp!(perm_v!(1)),
         deallocate!(),
         goto_execute!(354, 0), // goto run_cleaners_without_handling/0, 354.
         trust_me!(),
         goto_execute!(382, 0), // goto restore_cut_points/0, 382.
         allocate!(1), // sgc_on_success/2, 366.
         fact![get_var_in_fact!(perm_v!(1), 2)],
         reset_block!(),
         cut!(perm_v!(1)),
         deallocate!(),
         proceed!(),
         is_compound!(temp_v!(1)), // compound/1, 372.
         proceed!(),
         is_rational!(temp_v!(1)), // rational/1, 374.
         proceed!(),
         is_string!(temp_v!(1)), // string/1, 376.
         proceed!(),
         is_float!(temp_v!(1)), // float/1, 378.
         proceed!(),
         is_nonvar!(temp_v!(1)), // nonvar/1, 380.
         proceed!(),
         restore_cut_policy!(), // restore_cut_policy/0, 382.
         proceed!(),
         ground_execute!(), // ground/1, 384.
         eq_execute!(), // (==)/2, 385.
         not_eq_execute!(), // (\==)/2, 386.
         compare_term_execute!(term_cmp_gte!()), // (@>=)/2, 387.
         compare_term_execute!(term_cmp_lte!()), // (@=<)/2, 388.
         compare_term_execute!(term_cmp_gt!()), // (@>)/2, 389.
         compare_term_execute!(term_cmp_lt!()), // (@<)/2, 390.
         compare_term_execute!(term_cmp_eq!()), // (=@=)/2, 391.
         compare_term_execute!(term_cmp_ne!()), // (\=@=)/2, 392.
    ]
}

pub fn build_code_dir(atom_tbl: TabledData<Atom>) -> (Code, CodeDir, OpDir)
{
    let mut code_dir = HashMap::new();
    let mut op_dir   = HashMap::new();

    let builtin_code = get_builtins(atom_tbl.clone());

    op_dir.insert((tabled_rc!(":-", atom_tbl), Fixity::In),   (XFX, 1200));
    op_dir.insert((tabled_rc!(":-", atom_tbl), Fixity::Pre),  (FX, 1200));
    op_dir.insert((tabled_rc!("?-", atom_tbl), Fixity::Pre),  (FX, 1200));

    // control operators.
    op_dir.insert((tabled_rc!("\\+", atom_tbl), Fixity::Pre), (FY, 900));
    op_dir.insert((tabled_rc!("=", atom_tbl), Fixity::In), (XFX, 700));

    // arithmetic operators.
    op_dir.insert((tabled_rc!("is", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("+", atom_tbl), Fixity::In), (YFX, 500));
    op_dir.insert((tabled_rc!("-", atom_tbl), Fixity::In), (YFX, 500));
    op_dir.insert((tabled_rc!("/\\", atom_tbl), Fixity::In), (YFX, 500));
    op_dir.insert((tabled_rc!("\\/", atom_tbl), Fixity::In), (YFX, 500));
    op_dir.insert((tabled_rc!("xor", atom_tbl), Fixity::In), (YFX, 500));
    op_dir.insert((tabled_rc!("//", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("/", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("div", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("*", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("-", atom_tbl), Fixity::Pre), (FY, 200));
    op_dir.insert((tabled_rc!("rdiv", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("<<", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!(">>", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("mod", atom_tbl), Fixity::In), (YFX, 400));
    op_dir.insert((tabled_rc!("rem", atom_tbl), Fixity::In), (YFX, 400));

    // arithmetic comparison operators.
    op_dir.insert((tabled_rc!(">", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("<", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("=\\=", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("=:=", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!(">=", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("=<", atom_tbl), Fixity::In), (XFX, 700));

    // control operators.
    op_dir.insert((tabled_rc!(";", atom_tbl), Fixity::In), (XFY, 1100));
    op_dir.insert((tabled_rc!("->", atom_tbl), Fixity::In), (XFY, 1050));

    op_dir.insert((tabled_rc!("=..", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("==", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("\\==", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("@=<", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("@>=", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("@<", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("@>", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("=@=", atom_tbl), Fixity::In), (XFX, 700));
    op_dir.insert((tabled_rc!("\\=@=", atom_tbl), Fixity::In), (XFX, 700));

    // there are 63 registers in the VM, so call/N is defined for all 0 <= N <= 62
    // (an extra register is needed for the predicate name)
    for arity in 0 .. 63 {
        code_dir.insert((tabled_rc!("call", atom_tbl), arity), (PredicateKeyType::BuiltIn, 0));
    }

    code_dir.insert((tabled_rc!("atomic", atom_tbl), 1), (PredicateKeyType::BuiltIn, 1));
    code_dir.insert((tabled_rc!("var", atom_tbl), 1), (PredicateKeyType::BuiltIn, 3));
    code_dir.insert((tabled_rc!("false", atom_tbl), 0), (PredicateKeyType::BuiltIn, 61));
    code_dir.insert((tabled_rc!("\\+", atom_tbl), 1), (PredicateKeyType::BuiltIn, 62));
    code_dir.insert((tabled_rc!("duplicate_term", atom_tbl), 2), (PredicateKeyType::BuiltIn, 71));
    code_dir.insert((tabled_rc!("catch", atom_tbl), 3), (PredicateKeyType::BuiltIn, 5));
    code_dir.insert((tabled_rc!("throw", atom_tbl), 1), (PredicateKeyType::BuiltIn, 59));
    code_dir.insert((tabled_rc!("=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 73));
    code_dir.insert((tabled_rc!("true", atom_tbl), 0), (PredicateKeyType::BuiltIn, 75));

    code_dir.insert((tabled_rc!(",", atom_tbl), 2), (PredicateKeyType::BuiltIn, 76));
    code_dir.insert((tabled_rc!(";", atom_tbl), 2), (PredicateKeyType::BuiltIn, 120));
    code_dir.insert((tabled_rc!("->", atom_tbl), 2), (PredicateKeyType::BuiltIn, 138));

    code_dir.insert((tabled_rc!("functor", atom_tbl), 3), (PredicateKeyType::BuiltIn, 146));
    code_dir.insert((tabled_rc!("arg", atom_tbl), 3), (PredicateKeyType::BuiltIn, 150));
    code_dir.insert((tabled_rc!("integer", atom_tbl), 1), (PredicateKeyType::BuiltIn, 147));
    code_dir.insert((tabled_rc!("display", atom_tbl), 1), (PredicateKeyType::BuiltIn, 192));

    code_dir.insert((tabled_rc!("is", atom_tbl), 2), (PredicateKeyType::BuiltIn, 194));
    code_dir.insert((tabled_rc!(">", atom_tbl), 2), (PredicateKeyType::BuiltIn, 196));
    code_dir.insert((tabled_rc!("<", atom_tbl), 2), (PredicateKeyType::BuiltIn, 198));
    code_dir.insert((tabled_rc!(">=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 200));
    code_dir.insert((tabled_rc!("<=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 202));
    code_dir.insert((tabled_rc!("=\\=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 204));
    code_dir.insert((tabled_rc!("=:=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 206));
    code_dir.insert((tabled_rc!("=..", atom_tbl), 2), (PredicateKeyType::BuiltIn, 208));

    code_dir.insert((tabled_rc!("length", atom_tbl), 2), (PredicateKeyType::BuiltIn, 261));
    code_dir.insert((tabled_rc!("setup_call_cleanup", atom_tbl), 3), (PredicateKeyType::BuiltIn, 294));
    code_dir.insert((tabled_rc!("compound", atom_tbl), 1), (PredicateKeyType::BuiltIn, 372));
    code_dir.insert((tabled_rc!("rational", atom_tbl), 1), (PredicateKeyType::BuiltIn, 374));
    code_dir.insert((tabled_rc!("string", atom_tbl), 1), (PredicateKeyType::BuiltIn, 376));
    code_dir.insert((tabled_rc!("float", atom_tbl), 1), (PredicateKeyType::BuiltIn, 378));
    code_dir.insert((tabled_rc!("nonvar", atom_tbl), 1), (PredicateKeyType::BuiltIn, 380));

    code_dir.insert((tabled_rc!("ground", atom_tbl), 1), (PredicateKeyType::BuiltIn, 384));
    code_dir.insert((tabled_rc!("==", atom_tbl), 2), (PredicateKeyType::BuiltIn, 385));
    code_dir.insert((tabled_rc!("\\==", atom_tbl), 2), (PredicateKeyType::BuiltIn, 386));
    code_dir.insert((tabled_rc!("@>=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 387));
    code_dir.insert((tabled_rc!("@=<", atom_tbl), 2), (PredicateKeyType::BuiltIn, 388));
    code_dir.insert((tabled_rc!("@>", atom_tbl), 2), (PredicateKeyType::BuiltIn, 389));
    code_dir.insert((tabled_rc!("@<", atom_tbl), 2), (PredicateKeyType::BuiltIn, 390));
    code_dir.insert((tabled_rc!("=@=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 391));
    code_dir.insert((tabled_rc!("\\=@=", atom_tbl), 2), (PredicateKeyType::BuiltIn, 392));

    (builtin_code, code_dir, op_dir)
}
