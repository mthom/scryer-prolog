use assert_cmd::Command;
use std::ffi::OsStr;

pub const SCRYER_PROLOG: &str = "scryer-prolog";

/// Test whether scryer-prolog
/// produces the expected output when called with the supplied
/// arguments and fed the supplied input
pub fn run_top_level_test_with_args<
    A: IntoIterator<Item = AS>,
    S: Into<Vec<u8>>,
    O: assert_cmd::assert::IntoOutputPredicate<P>,
    AS: AsRef<OsStr>,
    P: predicates_core::Predicate<[u8]>,
>(
    args: A,
    stdin: S,
    expected_stdout: O,
) {
    Command::cargo_bin(SCRYER_PROLOG)
        .unwrap()
        .arg("-f")
        .arg("--no-add-history")
        .args(args)
        .write_stdin(stdin)
        .assert()
        .stdout(expected_stdout.into_output())
        .success();
}
