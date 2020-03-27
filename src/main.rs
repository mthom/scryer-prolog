extern crate crossterm;
#[macro_use]
extern crate downcast;
extern crate git_version;
extern crate indexmap;
#[macro_use]
extern crate lazy_static;
extern crate libc;
extern crate nix;
#[macro_use]
extern crate prolog_parser;
#[macro_use]
extern crate ref_thread_local;

use git_version::git_version;
use nix::sys::signal;

mod prolog;

use crate::prolog::machine::*;
use crate::prolog::machine::streams::*;
use crate::prolog::read::*;

use std::env;
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

    if env::args().any(|a| a == "-v" || a == "--version") {
        println!("{:}", git_version!());
        return;
    }

    let mut wam = Machine::new(readline::input_stream(), Stream::stdout());
    wam.run_top_level();
}
