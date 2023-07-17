#[cfg(feature = "num-rug-adapter")]
pub use num_rug_adapter as rug;

#[cfg(feature = "rug")]
pub use rug;
pub use dashu;

// #[macro_use]
// extern crate lazy_static;
// #[macro_use]
// extern crate static_assertions;

pub mod char_reader;
#[macro_use]
pub mod ast;
#[macro_use]
pub mod macros;
pub mod lexer;
pub mod parser;
