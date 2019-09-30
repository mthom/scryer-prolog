#[macro_use]
extern crate downcast;
extern crate indexmap;
#[macro_use]
extern crate prolog_parser;
#[macro_use]
extern crate ref_thread_local;
extern crate termion;

mod prolog;

use prolog::machine::*;
use prolog::read::*;

#[cfg(test)]
mod tests;

fn main() {
    let mut wam = Machine::new(readline::input_stream());  
    wam.run_top_level();
}
