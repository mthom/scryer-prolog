extern crate blake2;
extern crate chrono;
extern crate cpu_time;
extern crate crossterm;
extern crate divrem;
#[macro_use]
extern crate downcast;
extern crate git_version;
extern crate hostname;
extern crate indexmap;
#[macro_use]
extern crate lazy_static;
extern crate libc;
extern crate native_tls;
extern crate nix;
extern crate openssl;
extern crate ordered_float;
#[macro_use]
extern crate prolog_parser;
#[macro_use]
extern crate ref_thread_local;
extern crate ring;
extern crate ripemd160;
#[cfg(feature = "rug")]
extern crate rug;
#[cfg(feature = "num-rug-adapter")]
extern crate num_rug_adapter as rug;
extern crate rustyline;
extern crate sha3;
extern crate unicode_reader;

use crate::nix::sys::signal;

#[macro_use]
mod macros;
mod allocator;
mod arithmetic;
mod codegen;
mod clause_types;
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

use machine::*;
use machine::streams::*;
use read::*;

use std::sync::atomic::Ordering;

extern fn handle_sigint(signal: libc::c_int) {
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
