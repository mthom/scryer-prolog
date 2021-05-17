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
fn predicates() {
    load_module_test("src/tests/predicates.pl", "");
}

#[test]
fn rules() {
    load_module_test("src/tests/rules.pl", "");
}

#[test]
fn setup_call_cleanup_load() {
    load_module_test(
        "src/tests/setup_call_cleanup.pl",
        "1+21+31+2>_12827+_128281+_119391+2>41+2>_128281+2>31+2>31+2>4ba",
    );
}

#[test]
#[ignore] // FIXME: it looks as though the output is being fed back into stdin. Fix this.
fn setup_call_cleanup_process() {
    run_top_level_test_with_args(
        &["src/tests/setup_call_cleanup.pl"],
        "1+21+31+2>_72164+_721651+_712761+2>41+2>_721651+2>31+2>31+2>4ba",
        "",
    );
}

#[test]
fn clpz_load() {
    load_module_test("src/tests/clpz/test_clpz.pl", "");
}
