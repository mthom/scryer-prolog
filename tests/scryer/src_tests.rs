use crate::helper::run_top_level_test_with_args;

#[test]
fn setup_call_cleanup_process() {
    run_top_level_test_with_args(
        ["src/tests/setup_call_cleanup.pl", "-f", "-g", "halt"],
        "",
        "1+21+31+2>A+B1+G1+2>41+2>B1+2>31+2>31+2>4ba",
    );
}

#[test]
fn dif_tests() {
    run_top_level_test_with_args(
        ["src/tests/dif.pl", "-f", "-g", "main_quiet"],
        "",
        "All tests passed",
    );
}

#[test]
fn ground_tests() {
    run_top_level_test_with_args(
        ["src/tests/ground.pl", "-f", "-g", "main_quiet"],
        "",
        "All tests passed",
    );
}

#[test]
fn term_variables_tests() {
    run_top_level_test_with_args(
        ["src/tests/term_variables.pl", "-f", "-g", "main_quiet"],
        "",
        "All tests passed",
    );
}

#[test]
fn acyclic_term_tests() {
    run_top_level_test_with_args(
        ["src/tests/acyclic_term.pl", "-f", "-g", "main_quiet"],
        "",
        "All tests passed",
    );
}
