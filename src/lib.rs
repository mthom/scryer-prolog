//! A free software ISO Prolog system.
#![recursion_limit = "4112"]
#![deny(missing_docs)]

#[macro_use]
extern crate static_assertions;
#[cfg(test)]
#[macro_use]
extern crate maplit;

#[macro_use]
pub(crate) mod macros;
#[macro_use]
pub(crate) mod atom_table;
#[macro_use]
pub(crate) mod arena;
#[macro_use]
pub(crate) mod parser;
mod allocator;
mod arithmetic;
pub(crate) mod codegen;
mod debray_allocator;
#[cfg(feature = "ffi")]
mod ffi;
mod forms;
mod heap_iter;
pub(crate) mod heap_print;
#[cfg(feature = "http")]
mod http;
mod indexing;
mod variable_records;
#[macro_use]
pub(crate) mod instructions {
    include!(concat!(env!("OUT_DIR"), "/instructions.rs"));
}
mod iterators;
pub(crate) mod machine;
mod raw_block;
pub(crate) mod read;
#[cfg(feature = "repl")]
mod repl_helper;
mod targets;
pub(crate) mod types;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

// Re-exports
pub use machine::config::*;
pub use machine::lib_machine::*;
pub use machine::parsed_results::*;
pub use machine::Machine;

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn eval_code(s: &str) -> String {
    use machine::mock_wam::*;

    console_error_panic_hook::set_once();

    let mut wam = Machine::with_test_streams();
    let bytes = wam.test_load_string(s);
    String::from_utf8_lossy(&bytes).to_string()
}

/// The entry point for the Scryer Prolog CLI.
pub fn run_binary() -> std::process::ExitCode {
    use crate::atom_table::Atom;
    use crate::machine::{Machine, INTERRUPT};

    #[cfg(feature = "repl")]
    ctrlc::set_handler(move || {
        INTERRUPT.store(true, std::sync::atomic::Ordering::Relaxed);
    })
    .unwrap();

    #[cfg(target_arch = "wasm32")]
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    #[cfg(not(target_arch = "wasm32"))]
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    runtime.block_on(async move {
        let mut wam = Machine::new(Default::default());
        wam.run_module_predicate(atom!("$toplevel"), (atom!("$repl"), 0))
    })
}
