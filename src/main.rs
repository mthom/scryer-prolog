#[macro_use] extern crate cfg_if;
#[macro_use] extern crate downcast;
extern crate indexmap;
#[macro_use] extern crate prolog_parser;
#[macro_use] extern crate ref_thread_local;

cfg_if! {
    if #[cfg(feature = "readline_rs_compat")] {
        extern crate readline_rs_compat;
    }
}

extern crate termion;

mod prolog;

use prolog::machine::*;
use prolog::machine::machine_errors::*;
use prolog::read::*;

#[cfg(test)]
mod tests;

fn main() {
    #[cfg(feature = "readline_rs_compat")]
    readline::readline_initialize();

    let mut wam = Machine::new(readline::input_stream());
    wam.run_toplevel();
}
