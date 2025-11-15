use std::{
    env::consts::{DLL_PREFIX, DLL_SUFFIX},
    io::Write,
    path::{Path, PathBuf},
    process::Stdio,
};

use crate::helper::load_module_test_with_input;

use current_platform::CURRENT_PLATFORM;

const TMP_DIR: &str = env!("CARGO_TARGET_TMPDIR");

// each test is building its own library so that they can easier run in parallel,
// i.e. don't need to wait for a large dynamic library to compile,
// also rusts test infra currently has no functionallity for a setup/befor step
fn build_dynamic_library(name: &str, src: &str) -> PathBuf {
    let tmp_dir: &Path = TMP_DIR.as_ref();

    let mut child = std::process::Command::new("rustc")
        .stdin(Stdio::piped())
        .args(["--edition", "2024"])
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
                #[unsafe(no_mangle)]
                extern "C" fn ffi_f64_nan() -> f64 {
                    f64::NAN
                }
            "##,
    );

    load_module_test_with_input(
        "tests-pl/ffi_f64_nan.pl",
        format!("LIB={dynlib_path:?}."),
        "   error(evaluation_error(undefined),round/1).\n",
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_f64_minus_zero() {
    let dynlib_path = build_dynamic_library(
        "ffi_f64_minus_zero",
        r##"
                #[unsafe(no_mangle)]
                extern "C" fn ffi_f64_minus_zero() -> f64 {
                    -0.0
                }

                #[unsafe(no_mangle)]
                extern "C" fn signum(f: f64) -> f64 {
                    f.signum()
                }
            "##,
    );

    // note: ouput is currently wrong correct would be 1.0,1.0
    load_module_test_with_input(
        "tests-pl/ffi_f64_minus_zero.pl",
        format!("LIB={dynlib_path:?}."),
        "1.0,1.0",
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_return_values() {
    let dynlib_path = build_dynamic_library(
        "ffi_return_values",
        r##"
                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_true() -> bool {
                    true
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_false() -> bool {
                    false
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_i8() -> i8 {
                    -42
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_u8() -> u8 {
                    73
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_i16() -> i16 {
                    -0xBEE
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_u16() -> u16 {
                    0xC0DE
                }


                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_i32() -> i32 {
                    -0xBEEFBEE
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_u32() -> u32 {
                    0xC0DEB000
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_i64() -> i64 {
                    -0xBEEFBEE5C0DEB00
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_u64() -> u64 {
                    0xFEDCBA9876543210
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_f32() -> f32 {
                    std::f32::consts::PI
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_return_values_f64() -> f64 {
                    std::f64::consts::TAU
                }
            "##,
    );

    let expected = format!(
        "i8- {},u8-{},i16- {},u16-{},i32- {},u32-{},i64- {},u64-{},f32-{},f64-{}",
        -42,
        73,
        -0xBEE,
        0xC0DE,
        -0xBEEFBEE,
        0xC0DEB000u32,
        -0xBEEFBEE5C0DEB00i64,
        0xFEDCBA9876543210u64,
        std::f32::consts::PI as f64,
        std::f64::consts::TAU
    );

    load_module_test_with_input(
        "tests-pl/ffi_return_values.pl",
        format!("LIB={dynlib_path:?}."),
        expected.as_str(),
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_invalid_type() {
    let dynlib_path = build_dynamic_library(
        "ffi_invalid_type",
        r##"
                #[unsafe(no_mangle)]
                extern "C" fn ffi_invalid_type() -> () {
                }
            "##,
    );

    load_module_test_with_input(
        "tests-pl/ffi_invalid_type.pl",
        format!("LIB={dynlib_path:?}."),
        "% Warning: initialization/1 failed for: user:test\n",
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_struct() {
    let dynlib_path = build_dynamic_library(
        "ffi_struct",
        r##"
                #[repr(C)]
                struct PaddingGalore {
                    a: u8,
                    b: u16,
                    c: u32,
                    d: u64,
                    a2: u8,
                    e: f32,
                    f: f64,
                }

                #[unsafe(no_mangle)]
                extern "C" fn construct(a: u8, b: u16, c: u32, d: u64, a2: u8, e: f32, f: f64) -> PaddingGalore {
                    PaddingGalore {
                        a,
                        a2,
                        b,
                        c,
                        d,
                        e,
                        f,
                    }
                }

                #[unsafe(no_mangle)]
                extern "C" fn modify(data: PaddingGalore) -> PaddingGalore {
                    PaddingGalore {
                        a: data.a2,
                        a2: data.a,
                        b: !data.b,
                        c: !data.c,
                        d: !data.d,
                        e: -data.e,
                        f: -data.f,
                    }
                }
            "##,
    );

    load_module_test_with_input(
        "tests-pl/ffi_struct.pl",
        format!("LIB={dynlib_path:?}."),
        "[P,G]-[pg,8,12,46,40,127,1.3680000305175781,-4.587]\n[P,G,2]-[pg,127,65523,4294967249,18446744073709551575,8,-1.3680000305175781,4.587]\n",
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_cstr() {
    let dynlib_path = build_dynamic_library(
        "ffi_cstr",
        r##"
                use std::ffi::CStr;

                #[unsafe(no_mangle)]
                extern "C" fn ffi_cstr_len(c_str: Option<std::ptr::NonNull<core::ffi::c_char>>) -> u64 {
                    if let Some(c_str) = c_str {
                        unsafe { CStr::from_ptr(c_str.as_ptr()) }.count_bytes() as u64
                    } else {
                        u64::MAX
                    }
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_example_cstr() -> *const core::ffi::c_char {
                    c"Rust Lang".as_ptr()
                }

                #[unsafe(no_mangle)]
                extern "C" fn ffi_null_cstr() -> *const core::ffi::c_char {
                    std::ptr::null()
                }
            "##,
    );

    load_module_test_with_input(
        "tests-pl/ffi_cstr.pl",
        format!("LIB={dynlib_path:?}."),
        format!(r#"13-[R,u,s,t, ,L,a,n,g]-0-{}"#, u64::MAX).as_str(),
    );
}

#[test]
#[cfg_attr(miri, ignore = "ffi")]
fn ffi_heap() {
    let dynlib_path = build_dynamic_library(
        "ffi_heap",
        r##"
                #[unsafe(no_mangle)]
                extern "C" fn ffi_set_u64(val: &mut u64) {
                    *val = 133742
                }
            "##,
    );

    load_module_test_with_input(
        "tests-pl/ffi_heap.pl",
        format!("LIB={dynlib_path:?}."),
        r#"133742"#,
    );
}
