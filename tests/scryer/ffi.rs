use std::{
    env::consts::{DLL_PREFIX, DLL_SUFFIX},
    io::Write,
    path::{Path, PathBuf},
    process::Stdio,
};

use crate::helper::load_module_test;

use current_platform::CURRENT_PLATFORM;

const TMP_DIR: &'static str = env!("CARGO_TARGET_TMPDIR");

// each test is building its own library so that they can easier run in parallel,
// i.e. don't need to wait for a large dynamic library to compile,
// also rusts test infra currently has no functionallity for a setup/befor step
fn build_dynamic_library(name: &str, src: &str) -> PathBuf {
    let tmp_dir: &Path = TMP_DIR.as_ref();

    let mut child = std::process::Command::new("rustc")
        .stdin(Stdio::piped())
        .arg(format!("--target={CURRENT_PLATFORM}"))
        .arg("--crate-type=dylib")
        .arg(format!("--crate-name={name}"))
        .arg("--out-dir")
        .arg(tmp_dir)
        .arg("-")
        .spawn()
        .unwrap();

    child
        .stdin
        .take()
        .unwrap()
        .write_all(src.as_bytes())
        .unwrap();

    assert!(child.wait().unwrap().success());

    tmp_dir.join(format!("{DLL_PREFIX}{name}{DLL_SUFFIX}"))
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_f64_nan() {
    let dynlib_path = build_dynamic_library(
        "ffi_f64_nan",
        r##"
                #[no_mangle]
                extern "C" fn ffi_f64_nan() -> f64 {
                    f64::NAN
                }
            "##,
    );

    // technically UB as tests are by default multi-threaded,
    // but there is currently no other easy way to get the dynamic library file path as an input into a load_module_test test
    std::env::set_var("ffi_f64_nan_LIB", dynlib_path);

    load_module_test(
        "tests-pl/ffi_f64_nan.pl",
        "   error(evaluation_error(undefined),round/1).\n",
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_f64_minus_zero() {
    let dynlib_path = build_dynamic_library(
        "ffi_f64_minus_zero",
        r##"
                #[no_mangle]
                extern "C" fn ffi_f64_minus_zero() -> f64 {
                    -0.0
                }

                #[no_mangle]
                extern "C" fn signum(f: f64) -> f64 {
                    f.signum()
                }
            "##,
    );

    // technically UB as tests are by default multi-threaded,
    // but there is currently no other easy way to get the dynamic library file path as an input into a load_module_test test
    std::env::set_var("ffi_f64_minus_zero_LIB", dynlib_path);

    // note: ouput is currently wrong correct would be 1.0,1.0
    load_module_test("tests-pl/ffi_f64_minus_zero.pl", "-1.0,1.0");
}
