use crate::helper::load_module_test;
#[cfg(not(target_arch = "wasm32"))]
use crate::helper::load_module_test_with_tokio_runtime;
use serial_test::serial;

// issue #831
#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn call_0() {
    load_module_test(
        "tests-pl/issue831-call0.pl",
        "   error(existence_error(procedure,call/0),call/0).\n",
    );
}

#[test]
#[cfg_attr(miri, ignore = "unsupported operation when isolation is enabled")]
fn issue2588_load_html() {
    load_module_test("tests-pl/issue2588.pl", "[element(html,[],[element(head,[],[element(title,[],[[H,e,l,l,o,!]])]),element(body,[],[])])]");
}

// issue #2361
#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn call_qualification() {
    load_module_test("tests-pl/issue2361-call-qualified.pl", "");
}

// PR #2756: ensures that calling load_context with a bound variable doesn't trigger unreachable!()
#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn load_context_unreachable() {
    load_module_test("tests-pl/load-context-unreachable.pl", "");
}

// Issue #2725: A dcg of the form `id(X) --> X.` would previously trigger an instantiation
// error, as it would call `strip_module(X, M, P)` and later `call(M:P)`,
// but `strip_module` left `M` uninstanciated if the `module:` prefix was unspecified.
#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue2725_dcg_without_module() {
    load_module_test("tests-pl/issue2725.pl", "");
}

#[test]
#[cfg(feature = "http")]
#[cfg(not(target_arch = "wasm32"))]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn http_open_hanging() {
    load_module_test_with_tokio_runtime(
        "tests-pl/issue-http_open-hanging.pl",
            "received response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\n"
    );
}
