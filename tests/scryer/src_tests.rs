use crate::helper::{load_module_test, run_top_level_test_with_args};

#[test]
fn builtins() {
    load_module_test("src/tests/builtins.pl", "");
}

#[test]
fn call_with_inference_limit() {
    load_module_test("src/tests/call_with_inference_limit.pl", "");
}

#[test]
fn facts() {
    load_module_test("src/tests/facts.pl", "");
}

#[test]
fn hello_world() {
    load_module_test("src/tests/hello_world.pl", "Hello World!\n");
}

#[test]
fn syntax_error() {
    load_module_test(
        "tests-pl/syntax_error.pl",
        "caught: error(syntax_error(incomplete_reduction),read_term/3:6)\n",
    );
}

#[test]
#[ignore] // fails to halt
fn predicates() {
    load_module_test("src/tests/predicates.pl", "");
}

#[test]
fn rules() {
    load_module_test("src/tests/rules.pl", "");
}

#[test]
#[ignore]
fn setup_call_cleanup_load() {
    load_module_test(
        "src/tests/setup_call_cleanup.pl",
        "1+21+31+2>_13165+_131661+_121811+2>41+2>_131661+2>31+2>31+2>4ba",
    );
}

#[test]
#[ignore]
fn setup_call_cleanup_process() {
    run_top_level_test_with_args(
        &["src/tests/setup_call_cleanup.pl"],
        "",
        "1+21+31+2>_14108+_141091+_131241+2>41+2>_141091+2>31+2>31+2>4ba",
    );
}

#[test]
fn clpz_load() {
    load_module_test("src/tests/clpz/test_clpz.pl", "");
}
