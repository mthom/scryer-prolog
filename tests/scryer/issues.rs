use crate::helper::load_module_test;
use serial_test::serial;

// issue #831
#[serial]
#[test]
fn call_0() {
    load_module_test(
        "tests-pl/issue831-call0.pl",
        "   error(existence_error(procedure,call/0),call/0).\n",
    );
}
