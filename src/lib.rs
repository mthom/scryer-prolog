#![recursion_limit = "4112"]

#[macro_use]
extern crate static_assertions;
#[cfg(test)]
#[macro_use] extern crate maplit;

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
mod ffi;
mod variable_records;
mod forms;
mod heap_iter;
pub mod heap_print;
mod http;
mod indexing;
#[macro_use]
pub mod instructions {
    include!(concat!(env!("OUT_DIR"), "/instructions.rs"));
}
mod iterators;
pub mod machine;
mod raw_block;
pub mod read;
mod repl_helper;
mod targets;
pub mod types;

use instructions::instr;
