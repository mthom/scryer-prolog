use crate::helper::load_module_test;
use serial_test::serial;

// issue #831
#[serial]
#[test]
#[cfg_attr(miri, ignore = "blocked on helper.rs UB")]
fn call_0() {
    load_module_test(
        "tests-pl/issue831-call0.pl",
        "   error(existence_error(procedure,call/0),call/0).\n",
    );
}

// issue #2361
#[serial]
#[test]
fn call_qualification() {
    load_module_test("tests-pl/issue2361-call-qualified.pl", "");
}
