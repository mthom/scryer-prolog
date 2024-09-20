#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),"/docs/shared_library/README.md"))]

use std::ffi::{c_char, CStr, CString};

use serde_json::json;

use crate::machine::lib_machine::QueryState;
use crate::machine::Machine;

/// Create a new instance of the Scryer Machine.
///
///
/// It is the caller's responsibility to maintain a reference to the machine pointer
/// created by this function, passing it to [`machine_free`] to deallocate
/// resources. Failure to do so may lead to memory leaks.
///
#[export_name = "scryer_machine_new"]
pub extern "C" fn machine_new() -> *mut Machine {
    let machine = Box::into_raw(Box::new(Machine::new_lib()));
    machine
}

/// Frees the memory occupied by a [`Machine`] object.
///
/// # Safety
///
/// * It is the caller's responsibility to ensure that the input is a valid [`Machine`] pointer
/// created by [`machine_new`] that has not yet been freed by this function.
/// * Any [`QueryState`] instances associated with this machine should be deallocated prior
/// to calling this function on the input, otherwise those [`QueryState`] instances may
/// not be deallocated until the program terminates.
///
#[export_name = "scryer_machine_free"]
pub unsafe extern "C" fn machine_free(ptr: *mut Machine) {
    unsafe {
        drop(Box::from_raw(ptr));
    }
}

/// Returns a new query generator for the given virtual machine.  Null pointer returned
/// if string is not valid UTF-8.
///
/// # Safety
///
/// Caller must satisfy the following preconditions for this function:
///
/// * Valid [`Machine`] pointer created with [`machine_new`] that has not yet been freed.
/// * the input fulfill the safety requirements of [`CStr::from_ptr`].
/// * There must be no other [`QueryState`] for this [`Machine`] started by
/// [`run_query_iter`] that has not yet been freed with
/// [`query_state_free`] or the [`Machine`] state will enter an undefined
/// configuration with unpredictable results.
///
/// Other concerns:
/// * after invoking this function, calling any other function besides [`run_query_next`]
/// before invoking [`query_state_free`] on the [`QueryState`] pointer
/// will leave the [`Machine`] in an undefined state
///
#[export_name = "scryer_run_query_iter"]
pub unsafe extern "C" fn run_query_iter(
    machine: &mut Machine,
    input: *const c_char,
) -> *mut QueryState {
    match unsafe { CStr::from_ptr(input) }.to_str() {
        Ok(input) => {
            let string = input.to_string();
            let query_state = machine.run_query_iter(string);
            Box::into_raw(Box::new(query_state))
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Cleans up the [`QueryState`] in the associated Scryer [`Machine`].
///
/// # Safety
///
/// * `query_state` must be a valid mutable pointer to a [`QueryState`] created by [`run_query_iter`]
/// that has not yet been freed by [`query_state_free`].
/// * There can be only one [`QueryState`] per [`Machine`] started by
/// [`run_query_iter`] that has not yet been freed with
/// [`query_state_free`] or the [`Machine`] state will enter an undefined
/// configuration with unpredictable results.
#[export_name = "scryer_query_state_free"]
pub unsafe extern "C" fn query_state_free(query_state: *mut QueryState) {
    unsafe {
        drop(Box::from_raw(query_state));
    }
}

/// Returns a NULL POINTER if no addition iterations, else returns a
/// UTF-8 encoded JSON string with one iteration of results from a Scryer Prolog query.
///
/// See documentation for known limitations (e.g., concrete goals only).
///
/// # Safety
///
/// * `query_state` must be a valid mutable pointer to a [`QueryState`] created by [`run_query_iter`]
/// that has not yet been freed by [`query_state_free`].
/// * There can be only one [`QueryState`] per [`Machine`] started by
/// [`run_query_iter`] that has not yet been freed with
/// [`query_state_free`] or the [`Machine`] state will enter an undefined
/// configuration with unpredictable results.
#[export_name = "scryer_run_query_next"]
pub extern "C" fn run_query_next(query_state: &mut QueryState) -> *mut c_char {
    match query_state.next() {
        None => std::ptr::null_mut(),
        Some(Ok(query_resolution_line)) => {
            // let v = QueryResolution::from(vec![query_resolution_line]).to_string();

            // let obj = serde_json::from_str::<serde_json::Value>(query_resolution_line).expect("Bad JSON");

            let output_string = json!({
                "status": "ok",
                "result": query_resolution_line
            })
            .to_string();

            CString::new(output_string.to_string()).unwrap().into_raw()
        }
        Some(Err(err)) => {
            let output_string = json!({
                "status": "error",
                "error": err.to_string(),
            })
            .to_string();

            CString::new(output_string.to_string()).unwrap().into_raw()
        }
    }
}

/// Consults a Scryer Prolog module from a string, optionally with a given module name.
/// Will panic if provided invalid Scryer Prolog code.
///
/// # Safety
///
/// * `machine` must be a valid mutable pointer to a [`Machine`] created by
/// [`machine_new`] that has not yet been freed.
/// * `input` must be a valid pointer to a null terminated UTF-8 string of valid
/// Scryer Prolog code that satisfies the safety requirements of [`CStr::from_ptr`].
/// * `module_name`, must be a valid pointer to a null terminated UTF-8 string
/// of a valid Prolog module name that satisfies the safety requirements of
/// [`CStr::from_ptr`].
/// * there must be no [`QueryState`] for this [`Machine`] that has been created by
/// [`run_query_iter`] that has not yet been freed by
/// [`query_state_free`], or the [`Machine`] will enter an undefined state
/// with unpredictable behavior.
///
/// # Arguments
///
/// * `machine` - A mutable reference to the [`Machine`] to load the module into.
/// * `module_name` - A pointer to a null-terminated UTF-8 string representing
/// Scryer Prolog module name.
/// * `input` - A pointer to a null-terminated UTF-8 string representing Scryer Prolog code.
///
#[export_name = "scryer_consult_module_string"]
pub unsafe extern "C" fn consult_module_string(
    machine: &mut Machine,
    module_name: *const c_char,
    input: *const c_char,
) {
    let c_str: &CStr;
    unsafe {
        c_str = CStr::from_ptr(input);
    }
    let r_str = c_str.to_str().expect("Not a valid UTF-8 string");

    let m_str: &CStr;
    unsafe {
        m_str = CStr::from_ptr(module_name);
    }
    let module_name = m_str.to_str().expect("Not a valid UTF-8 string");

    machine.consult_module_string(&module_name, r_str.to_owned())
}

/// Greedily evaluate a prolog query, returning all results in a JSON-formatted string.
/// Errors are printed to stderr and a null pointer is returned.
///
/// # Safety
///
/// * `machine` must be a valid [`Machine`] pointer created with [`machine_new`]
/// that has not yet been freed.
/// * There must be no existing [`QueryState`] for this [`Machine`] started by
/// [`run_query_iter`] that has not yet been freed with
/// [`query_state_free`] or the [`Machine`] state will enter an undefined
/// configuration with unpredictable results.
/// * it is the responsibility of the caller to deallocate the pointer returned by
/// this function with [`scyer_free_c_string`] in order to avoid memory leaks.
///
///
/// # Returns
/// - Returns a pointer to a JSON formatted, null terminated UTF-8 string
///
/// # Response Format
/// ```json
/// // if result is a binding
///
/// // current limitation is that only concrete (equality) bindings are returned,
/// // residual goals not yet supported.
/// {
///   "status": "ok",
///   "result": [{ ... }],
/// }
///
/// // if result is a boolean goal
///
/// {
///   "status": "ok",
///   "result": boolean
/// }
#[export_name = "scryer_run_query"]
pub unsafe extern "C" fn run_query(machine: &mut Machine, input: *const c_char) -> *mut c_char {
    let c_string;
    let r_str;
    unsafe {
        c_string = CStr::from_ptr(input);
    };
    r_str = c_string.to_str().expect("Not a valid UTF-8 string");
    let query_resolution = machine.run_query(r_str.to_owned());

    let output_string: String = match query_resolution {
        Ok(query_resolution_line) => {
            // let value: Value =
            //     serde_json::from_str(&format!("{:?}", query_resolution_line)).unwrap();
            json!( {
                "status": "ok",
                "result": query_resolution_line
            })
            .to_string()
        }
        Err(err) => {
            eprintln!("Error {err}");
            return std::ptr::null_mut();
        }
    };
    CString::new(output_string).unwrap().into_raw()
}

/// Deallocate a Scryer Prolog string.
///
/// # Safety
///
/// * it is the caller's responsibility to ensure the `ptr` is not deallocated more than
/// once.
#[export_name = "scryer_free_c_string"]
pub unsafe extern "C" fn free_c_string(ptr: *mut c_char) {
    unsafe {
        let _ = CString::from_raw(ptr);
    }
}
