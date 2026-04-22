use crate::helper::load_module_test;
use crate::helper::load_module_test_with_input;
#[cfg(not(target_arch = "wasm32"))]
use crate::helper::load_module_test_with_tokio_runtime_and_input;
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
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_delete_directory() {
    load_module_test(
        "tests-pl/issue-files-delete-directory.pl",
        "directory_deleted",
    );
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_delete_file() {
    load_module_test("tests-pl/issue-files-delete-file.pl", "file_deleted");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_directory_exists() {
    load_module_test("tests-pl/issue-files-directory-exists.pl", "");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_directory_files() {
    load_module_test("tests-pl/issue-files-directory-files.pl", "1");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_copy() {
    load_module_test("tests-pl/issue-files-file-copy.pl", "file_copied");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_exists() {
    load_module_test("tests-pl/issue-files-file-exists.pl", "");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_size() {
    load_module_test("tests-pl/issue-files-file-size.pl", "");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_time() {
    load_module_test("tests-pl/issue-files-file-time.pl", "");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_make_directory() {
    load_module_test("tests-pl/issue-files-make-directory.pl", "directory_made");
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_make_directory_path() {
    load_module_test(
        "tests-pl/issue-files-make-directory-path.pl",
        "directory_path_made",
    );
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_path_canonical() {
    load_module_test(
        "tests-pl/issue-files-path-canonical.pl",
        "path_canonicalized",
    );
}

#[serial]
#[test]
#[cfg(unix)]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_rename_file() {
    load_module_test("tests-pl/issue-files-rename-file.pl", "file_renamed");
}

// issue #3262: read/1 on non-TTY stdin should resolve without requiring a newline
#[test]
#[cfg_attr(miri, ignore = "unsupported operation when isolation is enabled")]
fn issue3262_read_from_stdin_no_newline() {
    load_module_test_with_input("tests-pl/issue3262.pl", "hello.", "hello");
}

#[test]
#[cfg(feature = "http")]
#[cfg(not(target_arch = "wasm32"))]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn http_open_hanging() {
    load_module_test_with_tokio_runtime_and_input(
        "tests-pl/issue-http_open-hanging.pl",
        format!("PROLOG={:?}.", env!("CARGO_BIN_EXE_scryer-prolog")),
            "received response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\n"
    );
}
