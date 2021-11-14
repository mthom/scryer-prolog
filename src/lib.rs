#[macro_use]
extern crate static_assertions;

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
mod clause_types;
pub mod codegen;
mod debray_allocator;
mod fixtures;
mod forms;
mod heap_iter;
pub mod heap_print;
mod indexing;
mod instructions;
mod iterators;
pub mod machine;
mod raw_block;
pub mod read;
mod targets;
pub mod types;
pub mod write;
