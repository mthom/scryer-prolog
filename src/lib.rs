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

use std::cell::RefCell;
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

use machine::mock_wam::*;

#[cfg(not(target_arch = "wasm32"))]
thread_local! {
    pub static MACHINE: RefCell<Option<Machine>> = RefCell::new(None);
}


#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// In order to retain state, the invoking code must call machine_new().
/// NOTE: it is the responsibility of the invoking code to call machine_free() or expect
/// memory leaks.
pub extern "C" fn machine_new() {
    MACHINE.with(|m| *m.borrow_mut() = Some(Machine::new_lib()));
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// The invoking code must call machine_free() exactly once per machine_new() call to deallocate memory
/// and safely cleanup resources from the machine_new() invocation.
pub extern "C" fn machine_free() {
    MACHINE.with(|m| *m.borrow_mut() = None);
}


#[no_mangle]
/// Add source code to the database in the "facts" module.
/// NOTE: it is the responsibility of the invoking code to clean up the string
/// returned by this function with the free_c_string() function.
// is there any reason we would want to make other modules available as places to put facts...?
pub extern "C" fn load_module_string(input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| {
        let c_str = unsafe {
            assert!(!input.is_null());
            CStr::from_ptr(input)
        };
        let r_str = c_str.to_str().expect("Not a valid UTF-8 string");
        MACHINE.with(|m| {
            let mut machine = m.borrow_mut();
            let machine = machine.as_mut().expect("Machine not initialized.");
            machine.load_module_string("facts", r_str.to_owned());
        });
        true
    });

    let json_status = match result {
        Ok(_) => serde_json::to_string(&serde_json::json!({"status": "ok"})).unwrap(), // if the operation was successful
        Err(e) => serde_json::to_string(&serde_json::json!({"status": "error", "error": format!("{:?}", e)})).unwrap(), // if there was a panic
    };

    let c_string = CString::new(json_status).unwrap();
    c_string.into_raw()
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Consult facts.
/// NOTE: it is the responsibility of the invoking code to clean up the string returned
/// by this function with the free_c_string() function.
// I'm not sure if there is a technical difference between consulting and loading facts?
pub extern "C" fn consult_module_string(input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| {
        let c_str = unsafe {
            assert!(!input.is_null());
            CStr::from_ptr(input)
        };
        let r_str = c_str.to_str().expect("Not a valid UTF-8 string");
        MACHINE.with(|m| {
            let mut machine = m.borrow_mut();
            let machine = machine.as_mut().expect("Machine not initialized.");
            machine.consult_module_string("facts", r_str.to_owned());
        });
        true
    });

    let json_status = match result {
        Ok(_) => serde_json::to_string(&serde_json::json!({"status": "ok"})).unwrap(), // if the operation was successful
        Err(e) => serde_json::to_string(&serde_json::json!({"status": "error", "error": format!("{:?}", e)})).unwrap(), // if there was a panic
    };

    let c_string = CString::new(json_status).unwrap();
    c_string.into_raw()
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// run query, equivalent to preceding the facts with a "?-"
/// Returns JSON --
/// status: {"ok", "error","panic"}
/// <if status="error"> error: string
/// <if status="ok"> result: List[Map]
/// <if status="panic"> error: "panic"
pub extern "C" fn run_query(input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| {
        let c_str = unsafe {
            assert!(!input.is_null());
            CStr::from_ptr(input)
        };
        let r_str = c_str.to_str().expect("Not a valid UTF-8 string");

        MACHINE.with(|m| {
            let mut machine = m.borrow_mut();
            let machine = machine.as_mut().expect("Machine not initialized.");
            machine.run_query(r_str.to_owned())
        })
    });

    let output_string: String = match result {
        Ok(query_resolution) => {
            // Handling Result type
            match query_resolution {
                Ok(query_resolution) => {
                    serde_json::to_string(&serde_json::json!({"status": "ok", "result": format!("{}", query_resolution)})).unwrap()
                }
                Err(e_str) => {
                    serde_json::to_string(&serde_json::json!({"status": "error", "error": &e_str})).unwrap()
                }
            }
        }
        Err(_) => {
            serde_json::to_string(&serde_json::json!({"status": "panic", "error": "panic"})).unwrap()
        }
    };

    let c_string = CString::new(output_string).unwrap();
    c_string.into_raw()
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Make sure to call this after every invocation of `consult_module_string()`,
/// `load_module_string()`, and `run_query()` to cleanup resources, or
/// you will have a memory leak!
pub extern "C" fn free_c_string(ptr: *mut c_char) {
    unsafe {
        if ptr.is_null() {
            return;
        }
        let _ = CString::from_raw(ptr);
    };
}
