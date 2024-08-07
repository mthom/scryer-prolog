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

#[cfg(not(target_arch = "wasm32"))]
use std::ffi::{c_char, CStr, CString};

use machine::mock_wam::*;

#[cfg(not(target_arch = "wasm32"))]
use crate::machine::lib_machine::QueryState;


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
thread_local! {
    pub static QUERY_STATE: RefCell<Option<QueryState>> = RefCell::new(None);
    pub static MACHINE: RefCell<Option<Machine>> = RefCell::new(None);
}


#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// In order to retain state, the invoking code must call machine_new().
/// NOTE: it is the responsibility of the invoking code to call machine_free() or expect
/// memory leaks.
pub extern "C" fn machine_new() -> *mut Machine {
    let machine = Box::into_raw(Box::new(Machine::new_lib()));
    machine // This returns a raw pointer
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Free the machine. Don't do it twice!
pub extern "C" fn machine_free(ptr: *mut Machine) {
    unsafe { drop(Box::from_raw(ptr)); }
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub extern "C" fn start_new_query_generator(machine: *mut Machine, input: *const c_char) -> *mut QueryState {
    let result = std::panic::catch_unwind(|| unsafe {
        let c_str = {
            assert!(!input.is_null());
            CStr::from_ptr(input)
        };
        c_str.to_str().expect("Not a valid UTF-8 string").to_owned()
    });

    match result {
        Ok(r_str) => {
            let query_state = unsafe {
                (*machine).start_new_query_generator(r_str)
            };
            Box::into_raw(Box::new(query_state))
        }
        Err(e) => {
            println!("Panic: {:?}", e);
            std::ptr::null_mut()
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub extern "C" fn cleanup_query_generator(machine: *mut Machine, query_state: *mut QueryState) -> *mut c_char {
    unsafe {
        if !query_state.is_null() {
            drop(Box::from_raw(query_state));
        }
        (*machine).cleanup_query_generator();
        true
    };
    let c_string = CString::new(serde_json::to_string(&serde_json::json!({"status": "ok"})).unwrap()).unwrap();
    c_string.into_raw()
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Runs the query generator, equivalent to preceding facts with "?-" and returns results as JSON.
///
/// **Expected Usage:** This function is intended for use as part of a shared library binding. It assumes that
/// `machine_new()` and `start_new_query_generator()` have already been called to initialize the necessary structures.
pub extern "C" fn run_query_generator(machine: *mut Machine, query_state: *mut QueryState) -> *mut c_char {


    unsafe {
        let machine = &mut *machine;
        let query_state = &mut *(query_state);
        let query_resolution = machine.run_query_generator(query_state);
        let value: serde_json::Value = serde_json::from_str(&format!("{}", query_resolution.expect("Oh noes!"))).unwrap();
        let output_string = serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap();
        let c_string = CString::new(output_string).unwrap();
        c_string.into_raw()
    }
}


#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Add source code to the database in the "facts" module.
///
/// NOTE: It is the responsibility of the invoking code to free the string returned by this function using the free_c_string() function.
/// This function expects a null-terminated C string containing Prolog source code.
pub extern "C" fn load_module_string(machine: *mut Machine, input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| unsafe {
        assert!(!input.is_null());
        CStr::from_ptr(input).to_str().expect("Not a valid UTF-8 string")
    });

    let output_string = unsafe {
        match result {
            Ok(r_str) => {
                (*machine).load_module_string("facts", r_str.to_owned());
                serde_json::to_string(&serde_json::json!({"status": "ok"})).unwrap()
            }
            Err(e_str) => {
                serde_json::to_string(&serde_json::json!({"status": "error", "error": format!("{:?}", &e_str)})).unwrap()
            }
        }
    };

    let c_string = CString::new(output_string).unwrap();
    c_string.into_raw()
}


#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Consult facts.
/// NOTE: it is the responsibility of the invoking code to clean up the string returned
/// by this function with the free_c_string() function.
// I'm not sure if there is a technical difference between consulting and loading facts?
pub extern "C" fn consult_module_string(machine: *mut Machine, input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| unsafe {
        CStr::from_ptr(input).to_str().expect("Not a valid UTF-8 string")
    });

    let output_string = unsafe {
        match result {
            Ok(r_str) => {
                let query_resolution = (*machine).consult_module_string("facts", r_str.to_owned());
                let value: serde_json::Value = serde_json::from_str(&format!("{:?}", query_resolution)).unwrap();
                serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap()
            }
            Err(e_str) => {
                serde_json::to_string(&serde_json::json!({"status": "error", "error": format!("{:?}", &e_str)})).unwrap()
            }
        }
    };

    let c_string = CString::new(output_string).unwrap();
    c_string.into_raw()
}


#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Runs a single Prolog query and returns results as JSON.
/// **Expected Usage:**
/// This function is intended for use as part of a shared library binding. It assumes that
/// `machine_new()` has already been called to initialize the Prolog machine.
/// **Response Format (JSON):**
/// ```json
/// {
///   "status": "ok",  // or "error", or "panic"
///   "result": [ // present only if status is "ok"
///     { ... }, // Each element is a Map representing a query result.
///   ],
///   "error": "..." // present only if status is "error"
/// }
/// ```
/// **Warning:** Non-terminating queries will cause the thread to lock indefinitely.
pub extern "C" fn run_query(machine: *mut Machine, input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| unsafe {
        CStr::from_ptr(input).to_str().expect("Not a valid UTF-8 string")
    });

    let output_string = unsafe {
        match result {
            Ok(r_str) => {
                let query_resolution = (*machine).run_query(r_str.to_owned());
                let value: serde_json::Value = serde_json::from_str(&format!("{}", query_resolution.expect("Oh noes!"))).unwrap();
                let r = serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap();
                r
            }
            Err(e_str) => {
                serde_json::to_string(&serde_json::json!({"status": "error", "error": format!("{:?}", &e_str)})).unwrap()
            }
        }
    };
    let c_string = CString::new(output_string).unwrap();
    c_string.into_raw()
}


#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Frees the memory allocated for a C string previously returned by a Prolog binding function.
/// **IMPORTANT:** This function must be called after every invocation of `consult_module_string()`,
/// `load_module_string()`, `run_query()`, `run_query_generator()`, `start_new_query_generator()`,
/// and `cleanup_query_generator()` to prevent memory leaks!
pub extern "C" fn free_c_string(ptr: *mut c_char) {
    unsafe {
        if ptr.is_null() {
            return;
        }
        let _ = CString::from_raw(ptr);
    };
}
