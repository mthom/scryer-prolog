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

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
/// Initializes a new query generator with the provided Prolog source code string and returns a status JSON object.
/// The source code is expected to be a null-terminated C string.
///
/// Response Format (JSON):
/// json
/// {
///   "status": "ok" // if successful
/// } or
/// {
///    "status": "error",
///    "error": "..."
/// // Error message
/// }
pub fn start_new_query_generator(input: *const c_char) -> *mut c_char {
    let result = std::panic::catch_unwind(|| {
        let c_str = unsafe {
            assert!(!input.is_null());
            CStr::from_ptr(input)
        };
        let r_str = c_str.to_str().expect("Not a valid UTF-8 string").to_owned();
        QUERY_STATE.with(|qs| *qs.borrow_mut() =
            MACHINE.with(|m| {
                Some(m.borrow_mut().as_mut().expect("Machine not initialized!").start_new_query_generator(r_str))
            }));
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
/// Cleans up resources associated with the query generator and returns a status JSON object.
/// This function should be called after you are finished using `run_query_generator()` to release
/// any allocated memory.
/// **Response Format (JSON):**
/// ```json
/// {
///   "status": "ok" // if successful
/// } or
/// {
///    "status": "error",
///    "error": "..." // Error message
/// }
/// ```
pub fn cleanup_query_generator() -> *mut c_char {
    let result = std::panic::catch_unwind(|| {
        MACHINE.with(|m| {
            let mut machine = m.borrow_mut();
            let machine = machine.as_mut().expect("Machine not initialized!");
            machine.cleanup_query_generator();
            QUERY_STATE.with(|q| *q.borrow_mut() = None);
        })
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
/// Runs the query generator, equivalent to preceding facts with "?-" and returns results as JSON.
///
/// **Expected Usage:**
/// This function is intended for use as part of a shared library binding. It assumes that
/// `machine_new()` and `start_new_query_generator()` have already been called to initialize the
/// necessary structures.
/// **Response Format (JSON):** (per call)
/// ```json
/// [{
///   "status": "ok",  // or "error", or "panic"
///   "result": [ // present only if status is "ok" -- there will only be a single result per
///               // invocation
///     { ... }, // Each element is a Map representing a query result.
///   ],
///   "error": "..." // present only if status is "error"
/// }]
/// ```
/// When the answers are exhausted, the function returns a false `result` array and sets
/// the `status` to `"ok"`. The consuming code should handle this as a termination condition.
pub extern "C" fn run_query_generator() -> *mut c_char {
    let result = std::panic::catch_unwind(|| {
        QUERY_STATE.with(|q| {
            let mut qs = q.borrow_mut();
            let qs = qs.as_mut().expect("QueryState not initialized!");
            MACHINE.with(|m| {
                let mut machine = m.borrow_mut();
                let machine = machine.as_mut().expect("Machine not initialized.");
                machine.run_query_generator(qs)
            })
        })
    });

    let output_string: String = match result {
        Ok(query_resolution) => {
            // Handling Result type
            match query_resolution {
                Ok(query_resolution) => {
                    let value: serde_json::Value = serde_json::from_str(&format!("{}", query_resolution)).unwrap();
                    serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap()
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


#[no_mangle]
/// Add source code to the database in the "facts" module.
///
/// NOTE: It is the responsibility of the invoking code to free the string returned by this function using the free_c_string() function.
/// This function expects a null-terminated C string containing Prolog source code.
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
                    let value: serde_json::Value = serde_json::from_str(&format!("{}", query_resolution)).unwrap();
                    serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap()
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
