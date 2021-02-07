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
mod machine;
mod read;
mod targets;
mod write;

use machine::streams::*;
use machine::*;
use read::*;

use nix::sys::signal;
use std::sync::atomic::Ordering;

extern "C" fn handle_sigint(signal: libc::c_int) {
    let signal = signal::Signal::from_c_int(signal).unwrap();
    if signal == signal::Signal::SIGINT {
        INTERRUPT.store(true, Ordering::Relaxed);
    }
}

fn main() {
    let handler = signal::SigHandler::Handler(handle_sigint);
    unsafe { signal::signal(signal::Signal::SIGINT, handler) }.unwrap();

    let mut wam = Machine::new(readline::input_stream(), Stream::stdout());
    wam.run_top_level();
}
