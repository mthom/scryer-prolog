use crate::helper::{load_module_test, run_top_level_test_no_args, run_top_level_test_with_args};
use scryer_prolog::machine::Machine;
use serial_test::serial;

// issue #857
#[test]
fn display_constraints() {
    run_top_level_test_no_args(
        "\
        X = 1.\n\
        use_module(library(dif)).\n\
        X = 1.\n\
        dif(X,1).\n
        halt.\n",
        "   \
        X = 1.\n   \
        true.\n   \
        X = 1.\n   \
        dif:dif(X,1).\n\
        ",
    );
}

// issue #852
#[test]
fn do_not_duplicate_path_components() {
    run_top_level_test_no_args(
        "\
        ['tests-pl/issue852-throw_e.pl'].\n\
        ['tests-pl/issue852-throw_e.pl'].\n\
        halt.\n\
        ",
        "   throw(e).\n   false.\n   throw(e).\n   false.\n",
    );
}

// issue #844
#[test]
fn handle_residual_goal() {
    run_top_level_test_no_args(
        "\
        use_module(library(dif)).\n\
        use_module(library(atts)).\n\
        -X\\=X.\n\
        -X=X.\n\
        dif(-X,X).\n\
        dif(-X,X), -X=X.\n\
        call_residue_vars(dif(-X,X), Vars).\n\
        set_prolog_flag(occurs_check, true).\n\
        -X\\=X.\n\
        dif(-X,X).\n\
        halt.\n\
        ",
        "   \
        true.\n   \
        true.\n   \
        false.\n   \
        X = -X.\n   \
        dif:dif(-X,X).\n   \
        false.\n   \
        Vars = [X], dif:dif(-X,X).\n   \
        true.\n   \
        true.\n   \
        true.\n\
        ",
    )
}

// issue #841
#[test]
fn occurs_check_flag() {
    run_top_level_test_with_args(
        &["tests-pl/issue841-occurs-check.pl"],
        "\
         f(X, X).\n\
         halt.\n\
        ",
        "   false.\n",
    )
}

#[test]
fn occurs_check_flag2() {
    run_top_level_test_no_args(
        "\
            set_prolog_flag(occurs_check, true).\n\
            X = -X.\n\
            asserta(f(X,g(X))).\n\
            f(X,X).\n\
            X-X = X-g(X).\n\
            halt.\n\
            ",
        "   \
            true.\n   \
            false.\n   \
            true.\n   \
            false.\n   \
            false.\n\
            ",
    )
}

// issue #839
#[test]
fn op3() {
    run_top_level_test_with_args(&["tests-pl/issue839-op3.pl", "-g", "halt"], "", "")
}

// issue #820
#[test]
fn multiple_goals() {
    run_top_level_test_with_args(
        &["-g", "test", "-g", "halt", "tests-pl/issue820-goals.pl"],
        "",
        "helloworld\n",
    );
}

// issue #820
#[test]
fn compound_goal() {
    run_top_level_test_with_args(
        &["-g", "test,halt", "tests-pl/issue820-goals.pl"],
        "",
        "helloworld\n",
    )
}

// issue #815
#[test]
fn no_stutter() {
    run_top_level_test_no_args(
        "write(a), write(b), false.\n\
                                halt.\n\
                                ",
        "ab   false.\n",
    )
}

/*
// issue #812
#[test] // FIXME: the line number is of by one (should be 4), empty line not accounted for or starting to count at line 0?
fn singleton_warning() {
    run_top_level_test_no_args(
        "['tests-pl/issue812-singleton-warning.pl'].\n\
         halt.\n",
        "\
        Warning: singleton variables X at line 3 of issue812-singleton-warning.pl\n   \
        true.\n\
        ",
    );
}
*/

// issue #807
#[test]
fn ignored_constraint() {
    run_top_level_test_no_args(
        "use_module(library(freeze)), freeze(X,false), X \\=a.\n\
         halt.",
        "   freeze:freeze(X,false).\n",
    );
}

// issue #831
#[serial]
#[test]
fn call_0() {
    load_module_test(
        "tests-pl/issue831-call0.pl",
        "   error(existence_error(procedure,call/0),call/0).\n",
    );
}

// issue #1206
#[serial]
#[test]
#[should_panic(expected = "Overwriting atom table base pointer")]
fn atomtable_is_not_concurrency_safe() {
    // this is basically the same test as scryer_prolog::atom_table::atomtable_is_not_concurrency_safe
    // but for this integration test scryer_prolog is compiled with cfg!(not(test))  while for the unit test it is compiled with cfg!(test)
    // as the atom table implementation differ between cfg!(test) and cfg!(not(test)) both test serve a pourpose
    // Note: this integration test itself is compiled with cfg!(test) independent of scryer_prolog itself
    let _machine_a = Machine::with_test_streams();
    let _machine_b = Machine::with_test_streams();
}
