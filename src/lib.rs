#![recursion_limit = "4112"]

#[cfg(test)]
#[macro_use]
extern crate maplit;
#[macro_use]
extern crate static_assertions;

use instructions::instr;

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

pub mod lib {
    #[cfg(target_arch = "wasm32")]
    pub mod wasm {
        use wasm_bindgen::prelude::*;

        #[wasm_bindgen]
        pub fn eval_code(s: &str) -> String {
            use machine::mock_wam::*;

            console_error_panic_hook::set_once();

            let mut wam = Machine::with_test_streams();
            let bytes = wam.test_load_string(s);
            String::from_utf8_lossy(&bytes).to_string()
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub mod dll {
        use std::ffi::{c_char, CStr, CString};

        use crate::machine::lib_machine::QueryState;
        use crate::machine::Machine;

        /// Create a new instance of the Scryer Machine.
        ///
        /// # Safety
        ///
        /// The returned pointer must be properly deallocated using `scryer_machine_free()` once it is no longer needed.
        ///
        /// # Example
        ///
        /// ```
        /// let machine_ptr = scryer_machine_new();
        ///
        /// // Use machine_ptr...
        ///
        /// scryer_machine_free(machine_ptr);
        /// ```
        #[no_mangle]
        pub extern "C" fn scryer_machine_new() -> *mut Machine {
            let machine = Box::into_raw(Box::new(Machine::new_lib()));
            machine 
        }


        /// Frees the memory occupied by a `Machine` object.
        ///
        /// # Safety
        ///
        /// The function is marked as unsafe because it dereferences a raw pointer and assumes ownership of the object pointed to.
        /// It relies on the `Drop` implementation of `Box` to deallocate the memory.
        ///
        /// # Parameters
        ///
        /// - `ptr`: A mutable raw pointer to a `Machine` object.
        ///
        #[no_mangle]
        pub unsafe extern "C" fn scryer_machine_free(ptr: *mut Machine) {
            unsafe { drop(Box::from_raw(ptr)); }
        }

        /// This function initiates a new query on the provided machine instance with the given
        /// Prolog string query as input. It uses the Rust language and works with references.
        ///
        /// the provided C string is not a valid UTF-8 string, the function panics with an error
        /// message. After successfully converting the C string to a Rust UTF-8 string, a new query
        /// is started on the machine instance.
        ///
        /// In case of a panic during the execution, the function prints "Panic: " followed by the panic
        /// information, and returns a null pointer. Otherwise, it returns a raw pointer to the created
        /// `QueryState`.
        ///
        /// # Safety
        ///
        /// This function contains unsafe Rust code blocks. The behavior is undefined if:
        /// * `machine` is not a valid reference to a `Machine` instance.
        /// * `input` is not a null-terminated array.
        ///
        /// # Parameters
        ///
        /// * `machine`: Mutable reference to a `Machine` instance.
        /// * `input`:   Raw immutable pointer to a C string containing the Prolog string query.
        ///
        /// # Returns
        ///
        /// A raw pointer (`*mut QueryState`) to the created `QueryState` or a null pointer in case of a panic.
        #[no_mangle]
        pub unsafe  extern "C" fn scryer_start_new_query_generator(machine: &mut Machine, input: *const c_char) -> *mut QueryState {
            let result = std::panic::catch_unwind(|| {
                let c_str: &CStr;
                unsafe {
                    assert!(!input.is_null());
                    c_str = CStr::from_ptr(input);
                }

                let buf = c_str.to_str().expect("Not a valid UTF-8 string");
                buf.to_owned()
            });

            match result {
                Ok(r_str) => {
                    let query_state = machine.start_new_query_generator(r_str);
                    Box::into_raw(Box::new(query_state))
                },
                Err(e) => {
                    eprintln!("Panic: {:?}", e);
                    std::ptr::null_mut()
                },
            }
        }
        
        /// Cleans up the query generator in the Scryer machine.
        ///
        /// # Safety
        /// - `machine` must be a valid mutable pointer to a `Machine` instance.
        /// - `query_state` must be a valid mutable pointer to a `QueryState` instance.
        ///
        /// # Arguments
        ///
        /// - `machine`: A mutable pointer to the `Machine` instance.
        /// - `query_state`: A mutable pointer to the `QueryState` instance.
        ///
        /// # Returns
        ///
        /// Returns `0` to indicate successful cleanup.
        #[no_mangle]
        pub unsafe extern "C" fn scryer_cleanup_query_generator(machine: *mut Machine, query_state: *mut QueryState) -> i32 {
            unsafe {
                if !query_state.is_null() {
                    drop(Box::from_raw(query_state));
                }
                (*machine).cleanup_query_generator();
            }
            0

            
        }

        /// Runs a Prolog query generator, returning one result at a time as a C string pointer.
        ///
        /// This function takes a `&mut Machine` and a `*mut QueryState` as input, which respectively represent a mutable reference to a
        /// Prolog `Machine` and a `QueryState`. It then runs a Prolog query generator on the inputs, which yields one
        /// result at a time. The output is serialized into a JSON string and returned as a C string pointer (`*mut c_char`).
        ///
        /// The output format is a JSON object with the following keys:
        /// * `status` str: "ok" signifies successful completion, otherwise it would represent an error or a panic situation.
        /// * `result` List[Map]|bool: This would contain the actual result when the status is "ok". It can be a List of Maps, but the List will contain only a single map.
        ///                        ..: **Note:** if result is a boolean, this is the terminal result and the query generator should be cleaned up with 
        ///                        ..: `scryer_cleanup_query_generator()`.    
        /// * `error`  str: If the `status`=`error`, then this will contain the error message. If `status`=`panic`,
        ///            then the error message will be `panic`.
        ///
        /// If the status is "ok", and the result is `false`, it signifies that there are no more steps/results. Client applications must
        /// interpret this status and stop asking for more steps.
        ///
        /// This function can potentially panic during the resolution of the query or during the JSON serialization process.
        /// Therefore, exception handling should be implemented at the application level to mitigate potential issues.
        ///
        /// It's the caller's responsibility to deallocate the C string after usage by calling the function `scryer_free_c_string()`,
        /// to prevent memory leak.
        ///
        /// # Safety
        /// This function contains unsafe blocks due to the usage of raw pointers, as it needs to operate across
        /// language boundaries. The caller of this function has to ensure `query_state` are valid pointers.
        ///
        /// # Parameters
        /// * `machine`: a mutable reference to a `Machine` instance.
        /// * `query_state`: a raw pointer to a `QueryState` instance.
        ///
        /// # Returns
        /// - Returns a raw pointer to a C-string containing the serialized JSON result.
        ///
        /// # Expected Response Format
        /// ```json
        /// // if result is a binding
        /// // current limitation is that only concrete (equality) bindings are returned,
        /// // residual goals not yet supported.
        /// {
        ///   "status": "ok",  // Can also be "error" or "panic"
        ///   "result": [{ ... }], // single map entry, otherwise same signature as `scryer_run_query()`
        /// }
        /// 
        /// // if result is a boolean goal
        /// 
        /// {
        ///   "status": "ok",  // Can also be "error" or "panic"
        ///   "result": boolean // note -- `scryer_run_query_generator()` will continue returning results if
        ///                     //       .. successively invoked, but the result will always be the same
        ///                     //       .. at this point, `scryer_cleanup_query_generator()` should be called 
        /// }        
        /// 
        /// // if panic
        /// { 
        ///   "status": "error" | "panic",
        ///   "error": error message | "panic"
        /// }
        #[no_mangle]
        pub unsafe extern "C" fn scryer_run_query_generator(machine: &mut Machine, query_state: *mut QueryState) -> *mut c_char {
            let query_state = unsafe { &mut *(query_state) };
            let query_resolution = machine.run_query_generator(query_state);
            let value: serde_json::Value = serde_json::from_str(&format!("{}", query_resolution.expect("Error while marshaling JSON"))).unwrap();
            let output_string = serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap();
            let c_string = CString::new(output_string).unwrap();
            c_string.into_raw()
        }

        /// Loads a Scryer Prolog module from a string.
        ///
        /// # Safety
        ///
        /// - `machine` must be a valid mutable pointer to a `Machine`.
        /// - `input` must be a valid pointer to a null-terminated C string.
        ///
        /// # Arguments
        ///
        /// * `machine` - A mutable reference to the `Machine` to load the module into.
        /// * `input` - A pointer to a null-terminated C string containing the module source code.
        ///
        /// # Returns
        ///
        /// - `0` if the module was successfully loaded.
        /// - `1` if an error occurred while loading the module.
        #[no_mangle]
        pub unsafe extern "C" fn scryer_load_module_string(machine: &mut Machine, input: *const c_char) -> i32 {
            let result = std::panic::catch_unwind(|| {
                let c_str: &CStr;
                unsafe {
                    assert!(!input.is_null());
                    c_str = CStr::from_ptr(input);
                }
                c_str.to_str().expect("Not a valid UTF-8 string")
            });
            match result {
                Ok(r_str) => {
                    machine.load_module_string("facts", r_str.to_owned());
                    0
                }
                Err(e_str) => {
                    eprintln!("Error: {:?}", e_str);
                    1
                }
            }
        }

        #[no_mangle]
        pub unsafe extern "C" fn scryer_consult_module_string(machine: &mut Machine, input: *const c_char) -> i32 {
            let result = std::panic::catch_unwind(|| {
                let c_str: &CStr;
                unsafe {
                    c_str = CStr::from_ptr(input);
                }
                c_str.to_str().expect("Not a valid UTF-8 string")
            });

            match result {
                Ok(r_str) => {
                    machine.consult_module_string("facts", r_str.to_owned());
                    0
                },
                Err(e_str) => {
                    eprintln!("Error: {:?}", e_str);
                    1
                }
            }
        }

        /// `scryer_run_query` runs a prolog query using a Prolog machine instance.
        ///
        /// This function accepts a mutable reference (`machine`) to an instance of the Prolog `Machine`
        /// and an immutable C pointer (`input`) to a char which is to contain a valid Prolog query.
        /// It attempts to run the query on the machine and return a serialized JSON string as a raw
        /// C string pointer, with a "status" field and a "result" field.
        /// If anything goes wrong, the "status" will be set to "error" and an "error" field is included.
        /// However, if the operation is successful, the "status" is set to "ok" and the "result" field will contain the result of the query.
        ///
        /// # Safety
        ///
        /// This function contains unsafe blocks due to the use of raw pointers, but it is required
        /// to operate across FFI boundaries. It is the caller's responsibility to ensure the validity
        /// of `input`. The `input` should be a valid Null-Terminated `c_char` string.
        ///
        /// The returned C string is allocated on the heap and should be deallocated using the
        /// `scryer_free_c_string()` function to prevent memory leaks.
        ///
        /// # Parameters
        ///
        /// - `machine`: a mutable reference to a `Machine` instance.
        /// - `input`: an input in form of raw C `*const c_char` pointer.
        ///
        /// # Returns
        ///
        /// A raw pointer to a C string containing the serialized JSON result.
        ///
        /// # Expected Response Format
        /// ```json
        /// {
        ///   "status": "ok",  // Can also be "error" or "panic"
        ///   "result": [ // Only present if status is "ok"
        ///     { ... }, // Each is a Map representing a query result.
        ///   ],
        ///   "error": "..." // Only present if status is "error"
        /// }
        #[no_mangle]
        pub unsafe extern "C" fn scryer_run_query(machine: &mut Machine, input: *const c_char) -> *mut c_char {
            let c_string;
            let r_str;
            unsafe {
                c_string = CStr::from_ptr(input);
                r_str = c_string.to_str().expect("Not a valid UTF-8 string");
            };
            let result = std::panic::catch_unwind(|| r_str);

            let output_string = match result {
                Ok(r_str) => {
                    let query_resolution = machine.run_query(r_str.to_owned());
                    let value: serde_json::Value = serde_json::from_str(&format!("{}", query_resolution.expect("Something went wrong marshaling JSON"))).unwrap();
                    serde_json::to_string(&serde_json::json!({"status": "ok", "result": value})).unwrap()
                }
                Err(e_str) => serde_json::to_string(&serde_json::json!({"status": "error", "error": format!("{:?}", &e_str)})).unwrap()
            };

            let c_string = CString::new(output_string).unwrap();
            c_string.into_raw()
        }


        #[no_mangle]
        /// This function is responsible for freeing up the memory that was previously allocated for a C
        /// string that was returned by Scryer Prolog binding functions. It is of critical importance to
        /// prevent memory leaks that this function has to be invoked after every single invocation of
        /// the following functions: `scryer_consult_module_string()`, `scryer_load_module_string()`,
        /// `scryer_run_query()`, `scryer_run_query_generator()`, `scryer_start_new_query_generator()`,
        /// and `scryer_cleanup_query_generator()`.
        ///
        /// # Arguments
        ///
        /// * `ptr: *mut c_char` - A mutable pointer to c_char which indicates the memory address that should be freed.
        ///
        /// # Safety
        ///
        /// This function runs a unsafe block of code. The "unsafe" keyword is used because this function
        /// makes use of a raw pointer and the Rust memory safety guarantees cannot be upheld. Please
        /// ensure to follow the usage instructions to prevent any unintended side effects.
        pub unsafe extern "C" fn scryer_free_c_string(ptr: *mut c_char) {
            if ptr.is_null() {
                return;
            }

            unsafe {
                let _ = CString::from_raw(ptr);
            }
        }
    }
}
