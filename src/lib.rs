#[cfg(feature = "num-rug-adapter")]
use num_rug_adapter as rug;
#[cfg(feature = "rug")]
use rug;

#[macro_use]
mod macros;
mod allocator;
mod arithmetic;
mod clause_types;
mod codegen;
mod debray_allocator;
mod fixtures;
mod forms;
mod heap_iter;
mod heap_print;
mod indexing;
mod instructions;
mod iterators;
pub mod machine;
pub mod read;
mod targets;
mod write;

use machine::*;

use nix::sys::signal;
use std::sync::atomic::Ordering;

pub extern "C" fn handle_sigint(signal: libc::c_int) {
    let signal = signal::Signal::from_c_int(signal).unwrap();
    if signal == signal::Signal::SIGINT {
        INTERRUPT.store(true, Ordering::Relaxed);
    }
}
