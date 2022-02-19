use crate::helper::{load_module_test, run_top_level_test_with_args};
use serial_test::serial;

#[serial]
#[test]
fn builtins() {
    load_module_test("src/tests/builtins.pl", "");
}

#[serial]
#[test]
fn call_with_inference_limit() {
    load_module_test("src/tests/call_with_inference_limit.pl", "");
}

#[serial]
#[test]
fn facts() {
    load_module_test("src/tests/facts.pl", "");
}

#[serial]
#[test]
fn hello_world() {
    load_module_test("src/tests/hello_world.pl", "Hello World!\n");
}

#[serial]
#[test]
fn syntax_error() {
    load_module_test(
        "tests-pl/syntax_error.pl",
        "caught: error(syntax_error(incomplete_reduction),read_term/3:6)\n",
    );
}

#[serial]
#[test]
fn predicates() {
    load_module_test("src/tests/predicates.pl", "");
}

#[serial]
#[test]
fn rules() {
    load_module_test("src/tests/rules.pl", "");
}

#[serial]
#[test]
fn setup_call_cleanup_load() {
    load_module_test(
        "src/tests/setup_call_cleanup.pl",
        "1+21+31+2>_17737+_177381+_158071+2>41+2>_177381+2>31+2>31+2>4ba"
    );
}

#[test]
fn setup_call_cleanup_process() {
    run_top_level_test_with_args(
        &["src/tests/setup_call_cleanup.pl", "-f", "-g", "halt"],
        "",
        "1+21+31+2>_19590+_195911+_176601+2>41+2>_195911+2>31+2>31+2>4ba"
    );
}

#[serial]
#[test]
fn clpz_load() {
    load_module_test("src/tests/clpz/test_clpz.pl", "");
}
