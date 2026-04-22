use crate::helper::load_module_test;
use crate::helper::load_module_test_with_input;
#[cfg(not(target_arch = "wasm32"))]
use serial_test::serial;
use tokio::time::Duration;

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

// issue #2914
#[test]
#[cfg_attr(miri, ignore = "unsupported operation when isolation is enabled")]
fn issue2914_current_prolog_flag_shared_var() {
    load_module_test("tests-pl/issue2914.pl", "false");
}

#[test]
#[cfg_attr(miri, ignore = "unsupported operation when isolation is enabled")]
fn issue3256_load_xml_returns_list() {
    load_module_test(
        "tests-pl/issue3256.pl",
        "[element(foo,[],[element(bar,[],[[h,e,l,l,o]])])]",
    );
}

#[test]
#[cfg_attr(miri, ignore = "unsupported operation when isolation is enabled")]
fn issue2949_load_html() {
    load_module_test("tests-pl/issue2949.pl", "[doctype([h,t,m,l]),element(html,[],[element(head,[],[element(title,[],[[H,e,l,l,o,!]])]),element(body,[],[])])][doctype([h,t,m,l]),element(html,[],[element(head,[],[element(title,[],[[H,e,l,l,o,!]]),comment([ ,c,o,m,m,e,n,t, ])]),element(body,[],[])])][comment([]),element(html,[],[element(head,[],[]),element(body,[],[])])]");
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

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_delete_directory() {
    load_module_test("tests-pl/issue_delete_directory.pl", "directory_deleted");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_delete_file() {
    load_module_test("tests-pl/issue_delete_file.pl", "file_deleted");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_directory_exists() {
    load_module_test("tests-pl/issue_directory_exists.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_directory_files() {
    load_module_test("tests-pl/issue_directory_files.pl", "1");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_file_copy() {
    load_module_test("tests-pl/issue_file_copy.pl", "file_copied");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_file_exists() {
    load_module_test("tests-pl/issue_file_exists.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_file_size() {
    load_module_test("tests-pl/issue_file_size.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_file_time() {
    load_module_test("tests-pl/issue_file_time.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_make_directory() {
    load_module_test("tests-pl/issue_make_directory.pl", "directory_made");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_make_directory_path() {
    load_module_test(
        "tests-pl/issue_make_directory_path.pl",
        "directory_path_made",
    );
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_path_canonical() {
    load_module_test("tests-pl/issue_path_canonical.pl", "path_canonicalized");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_rename_file() {
    load_module_test("tests-pl/issue_rename_file.pl", "file_renamed");
}

// issue #3262: read/1 on non-TTY stdin should resolve without requiring a newline
#[test]
#[cfg_attr(miri, ignore = "unsupported operation when isolation is enabled")]
fn issue3262_read_from_stdin_no_newline() {
    load_module_test_with_input("tests-pl/issue3262.pl", "hello.", "hello");
}

#[tokio::test(flavor = "multi_thread")]
#[cfg(feature = "http")]
#[cfg(not(target_arch = "wasm32"))]
#[cfg_attr(miri, ignore = "it takes too long to run")]
async fn http_open_hanging() {
    tokio::time::timeout(Duration::from_mins(5), async {
        load_module_test_with_input(
            "tests-pl/issue-http_open-hanging.pl",
            format!("PROLOG={:?}.", env!("CARGO_BIN_EXE_scryer-prolog")),
            "received response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\n"
        );
    }).await.unwrap()
}

#[tokio::test(flavor = "multi_thread")]
#[cfg(feature = "repl")]
#[cfg(unix)]
async fn sigint_interrupts_nonterminating_goals() {
    load_module_test_with_input(
        "tests-pl/issue-interrupt-nontermination.pl",
        format!("PROLOG={:?}.", env!("CARGO_BIN_EXE_scryer-prolog")),
        "ok\n"
    );
}