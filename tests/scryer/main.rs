mod helper;
mod issues;
mod src_tests;

/// To add new cli test copy an existing .toml file in `tests/scryer/cli/issues/` or `tests/scryer/cli/issues/src_tests/`,
/// adjust as necessary the `-f` and `--no-add-history` args should be kept but additional args may be added.
/// For input on stdin add a .stdin file with the same filename.
/// Then to generate new reference output files into dump/ run `TRYCMD=dump cargo test -- cli_test`
/// check that the output in the .stdout and .stderr file is as expected, then move them next to the .toml file.
///
/// If a test does not have a .stderr or .stdout the corresponding output is ignored i.e. any and no output is accepted
///
/// to re-generate all reference output files run `TRYCMD=overwrite cargo test -- cli_test`
/// then check that the changes are as expected e.g. by looking at the `git diff`
#[test]
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
#[cfg_attr(
    miri,
    ignore = "miri isolation, unsupported operation: can't call foreign function"
)]
fn cli_tests() {
    trycmd::TestCases::new()
        .default_bin_name("scryer-prolog")
        .case("tests/scryer/cli/issues/*.toml")
        .skip("tests/scryer/cli/issues/singleton_warning.toml") // wrong line number
        .case("tests/scryer/cli/src_tests/*.toml");
}
