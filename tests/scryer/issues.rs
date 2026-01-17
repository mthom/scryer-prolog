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
fn issue_files_delete_directory() {
    load_module_test("tests-pl/issue-files-delete-directory.pl", "directory_deleted");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_delete_file() {
    load_module_test("tests-pl/issue-files-delete-file.pl", "file_deleted");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_directory_exists() {
    load_module_test("tests-pl/issue-files-directory-exists.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_directory_files() {
    load_module_test("tests-pl/issue-files-directory-files.pl", "1");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_copy() {
    load_module_test("tests-pl/issue-files-file-copy.pl", "file_copied");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_exists() {
    load_module_test("tests-pl/issue-files-file-exists.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_size() {
    load_module_test("tests-pl/issue-files-file-size.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_file_time() {
    load_module_test("tests-pl/issue-files-file-time.pl", "");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_make_directory() {
    load_module_test("tests-pl/issue-files-make-directory.pl", "directory_made");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_make_directory_path() {
    load_module_test(
        "tests-pl/issue-files-make-directory-path.pl",
        "directory_path_made",
    );
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_path_canonical() {
    load_module_test("tests-pl/issue-files-path-canonical.pl", "path_canonicalized");
}

#[serial]
#[test]
#[cfg_attr(miri, ignore = "it takes too long to run")]
fn issue_files_rename_file() {
    load_module_test("tests-pl/issue-files-rename-file.pl", "file_renamed");
}

#[test]
#[cfg(feature = "http")]
#[cfg(not(target_arch = "wasm32"))]
#[cfg_attr(miri, ignore = "it takes too long to run")]
#[cfg_attr(not(miri), ignore = "flaky due to network requests")]
fn http_open_hanging() {
    load_module_test_with_tokio_runtime(
        "tests-pl/issue-http_open-hanging.pl",
            "received response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\nreceived response with status code:200\n"
    );
}
