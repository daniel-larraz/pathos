//! Lexer for Eunoia, with source locations and the error type
//!
//! Ethos has no syntax tree: its parser builds terms as it reads, and what
//! it has already read (declarations, attributes) decides how the rest is
//! read. So this crate stops at tokens. The parser that turns them into
//! terms is in `pathos-elab`.

mod error;
pub mod latin1;
mod lexer;
mod token;

pub use error::{Error, Location, Result};
pub use lexer::Lexer;
pub use token::Token;
