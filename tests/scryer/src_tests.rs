use crate::helper::load_module_test;
use serial_test::serial;

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn builtins() {
    load_module_test("src/tests/builtins.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn call_with_inference_limit() {
    load_module_test("src/tests/call_with_inference_limit.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn facts() {
    load_module_test("src/tests/facts.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn hello_world() {
    load_module_test("src/tests/hello_world.pl", "Hello World!\n");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn syntax_error() {
    load_module_test(
        "tests-pl/syntax_error.pl",
        "   error(syntax_error(incomplete_reduction),read_term/3:6).\n",
    );
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn predicates() {
    load_module_test("src/tests/predicates.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn rules() {
    load_module_test("src/tests/rules.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn setup_call_cleanup_load() {
    load_module_test(
        "src/tests/setup_call_cleanup.pl",
        "1+21+31+2>A+B1+G1+2>41+2>B1+2>31+2>31+2>4ba",
    );
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn clpz_load() {
    load_module_test("src/tests/clpz/test_clpz.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn iso_conformity_tests() {
    load_module_test("tests-pl/iso-conformity-tests.pl", "All tests passed");
}
