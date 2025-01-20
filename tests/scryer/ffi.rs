use std::{
    env::consts::{DLL_PREFIX, DLL_SUFFIX},
    io::Write,
    path::Path,
    process::Stdio,
};

use crate::helper::load_module_test;

#[test]
fn ffi_f64_nan() {
    let tmp_dir: &Path = env!("CARGO_TARGET_TMPDIR").as_ref();
    println!("CARGO_TARGET_TMPDIR: {tmp_dir:?}");

    // technically UB as tests are by default multi-threaded,
    // but there is currently no other easy way to get the dynamic library file path as an input into a load_module_test test
    std::env::set_var(
        "ffi_f64_nan_LIB",
        tmp_dir.join(format!("{DLL_PREFIX}ffi_f64_nan{DLL_SUFFIX}")),
    );

    let mut child = std::process::Command::new("rustc")
        .stdin(Stdio::piped())
        .arg("--crate-type=dylib")
        .arg("--crate-name=ffi_f64_nan")
        .arg("--out-dir")
        .arg(tmp_dir)
        .arg("-")
        .spawn()
        .unwrap();

    child
        .stdin
        .take()
        .unwrap()
        .write_all(
            r##"
        #[no_mangle]
        extern "C" fn ffi_f64_nan() -> f64 {
            f64::NAN
        }
    "##
            .as_bytes(),
        )
        .unwrap();

    assert!(child.wait().unwrap().success());

    load_module_test(
        "tests-pl/ffi_f64_nan.pl",
        "   error(evaluation_error(undefined),round/1).\n",
    );
}

#[test]
fn ffi_f64_minus_zero() {
    let tmp_dir: &Path = env!("CARGO_TARGET_TMPDIR").as_ref();
    println!("CARGO_TARGET_TMPDIR: {tmp_dir:?}");

    // technically UB as tests are by default multi-threaded,
    // but there is currently no other easy way to get the dynamic library file path as an input into a load_module_test test
    std::env::set_var(
        "ffi_f64_minus_zero_LIB",
        tmp_dir.join(format!("{DLL_PREFIX}ffi_f64_minus_zero{DLL_SUFFIX}")),
    );

    let mut child = std::process::Command::new("rustc")
        .stdin(Stdio::piped())
        .arg("--crate-type=dylib")
        .arg("--crate-name=ffi_f64_minus_zero")
        .arg("--out-dir")
        .arg(tmp_dir)
        .arg("-")
        .spawn()
        .unwrap();

    child
        .stdin
        .take()
        .unwrap()
        .write_all(
            r##"
        #[no_mangle]
        extern "C" fn ffi_f64_minus_zero() -> f64 {
            -0.0
        }

        #[no_mangle]
        extern "C" fn signum(f: f64) -> f64 {
            f.signum()
        }
    "##
            .as_bytes(),
        )
        .unwrap();

    assert!(child.wait().unwrap().success());

    // note: ouput is currently wrong correct would be 1.0,1.0
    load_module_test("tests-pl/ffi_f64_minus_zero.pl", "-1.0,1.0");
}
