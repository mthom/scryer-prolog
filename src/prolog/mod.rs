extern crate dirs;
extern crate ordered_float;
extern crate prolog_parser;
#[cfg(feature = "rug")]
extern crate rug;
#[cfg(feature = "num-rug-adapter")]
extern crate num_rug_adapter as rug;
extern crate rustyline;

#[macro_use]
mod macros;
mod clause_types;
pub mod instructions;
#[macro_use]
mod allocator;
mod arithmetic;
mod codegen;
mod debray_allocator;
mod fixtures;
mod forms;
mod heap_iter;
pub mod heap_print;
mod indexing;
mod iterators;
pub mod machine;
pub mod read;
mod targets;
pub mod write;
