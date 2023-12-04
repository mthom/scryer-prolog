mod helper;
mod issues;
mod src_tests;

/// to generate new reference output files into dump/ run `TRYCMD=dump cargo test -- cli_test`
/// check that the output is as expected, then move them next to the .toml file
///
/// to re-generate reference output files run `TRYCMD=overwrite cargo test -- cli_test`
/// then check that the changes are as expected e.g. by looking at the `git diff`
#[test]
fn cli_tests() {
    trycmd::TestCases::new()
        .default_bin_name("scryer-prolog")
        .case("tests/scryer/cli/issues/*.toml")
        .skip("tests/scryer/cli/issues/singleton_warning.toml") // wrong line number
        .case("tests/scryer/cli/src_tests/*.toml");
}
