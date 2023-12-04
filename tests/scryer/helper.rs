use assert_cmd::Command;
use std::ffi::OsStr;

pub(crate) trait Expectable {
    #[track_caller]
    fn assert_eq(self, other: &[u8]);
}

impl Expectable for &str {
    #[track_caller]
    fn assert_eq(self, other: &[u8]) {
        if let Ok(other_str) = std::str::from_utf8(other) {
            assert_eq!(other_str, self)
        } else {
            // should always fail as other is not valid utf-8 but self is
            // just for consistent assert error message
            assert_eq!(other, self.as_bytes())
        }
    }
}

impl Expectable for &[u8] {
    #[track_caller]
    fn assert_eq(self, other: &[u8]) {
        assert_eq!(other, self)
    }
}

/// Tests whether the file can be successfully loaded
/// and produces the expected output during it
pub(crate) fn load_module_test<T: Expectable>(file: &str, expected: T) {
    use scryer_prolog::machine::mock_wam::*;

    let mut wam = Machine::with_test_streams();
    expected.assert_eq(wam.test_load_file(file).as_slice());
}

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
