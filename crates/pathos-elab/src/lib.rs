//! Elaboration: the parser, scopes, overloading and commands, from tokens to
//! checked terms
//!
//! [`State`] holds the symbol tables and scopes and owns the
//! [`pathos_check::Checker`]. A [`Parser`] reads one input and runs its
//! commands on the state; [`include_file`] does that for a file.

mod cmd_parser;
mod expr_parser;
mod parser;
mod path;
mod plugin;
mod snapshot;
mod state;

pub use parser::{Parser, include_file};
pub use plugin::{Plugin, StepResult};
pub use state::State;
