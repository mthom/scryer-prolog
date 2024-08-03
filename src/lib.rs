#![recursion_limit = "4112"]

#[macro_use]
extern crate static_assertions;
#[cfg(test)]
#[macro_use]
extern crate maplit;

#[macro_use]
pub mod macros;
#[macro_use]
pub mod atom_table;
#[macro_use]
pub mod arena;
#[macro_use]
pub mod parser;
mod allocator;
mod arithmetic;
pub mod codegen;
mod debray_allocator;
#[cfg(feature = "ffi")]
mod ffi;
mod forms;
mod heap_iter;
pub mod heap_print;
#[cfg(feature = "http")]
mod http;
mod indexing;
mod variable_records;
#[macro_use]
pub mod instructions {
    include!(concat!(env!("OUT_DIR"), "/instructions.rs"));
}
mod iterators;
pub mod machine;
mod raw_block;
pub mod read;
#[cfg(feature = "repl")]
mod repl_helper;
mod targets;
pub mod types;

use instructions::instr;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn eval_code(s: &str) -> String {
    use machine::mock_wam::*;

    console_error_panic_hook::set_once();

    let mut wam = Machine::with_test_streams();
    let bytes = wam.test_load_string(s);
    String::from_utf8_lossy(&bytes).to_string()
}

#[cfg(not(target_arch = "wasm32"))]
use std::ffi::{c_char, CStr, CString};

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub extern "C" fn eval_code_c(input: *const c_char) -> *mut c_char {
    use machine::mock_wam::*;

    let c_str = unsafe {
        assert!(!input.is_null());
        CStr::from_ptr(input)
    };
    let r_str = c_str.to_str().expect("Not a valid UTF-8 string");

    let mut wam = Machine::with_test_streams();
    let bytes = wam.test_load_string(r_str);
    let result_str = String::from_utf8_lossy(&bytes).to_string();

    let c_string = CString::new(result_str).expect("Failed to convert to CString");
    c_string.into_raw() // convert to raw pointer and prevent Rust from cleaning it up
}
#[no_mangle]
pub extern "C" fn free_c_string(ptr: *mut c_char) {
    unsafe {
        if ptr.is_null() {
            return;
        }
        let _ = CString::from_raw(ptr);
    };
}
