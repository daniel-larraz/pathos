//! Checking: term construction, typing, matching, program evaluation and
//! proof steps
//!
//! Everything here is a method of [`Checker`], which owns the term store.
//! The modules follow Ethos's `state.cpp` and `type_checker.cpp`:
//!
//! - `build`: `mk_expr`, which desugars applications by the attributes of
//!   their head, reduces macros and programs, and resolves overloads;
//! - `typing`: `get_type` and matching;
//! - `eval`: `evaluate`, programs and the `eo::` operators;
//! - `step`: what a proof step proves;
//! - `print`: terms as they appear in messages;
//! - `stats`: what `--stats` prints;
//! - `snapshot`: saving and restoring all of the above.
//!
//! These cannot be separate crates: building an application evaluates and
//! types terms, and evaluating reads attributes and builds terms.

mod attr;
mod build;
mod checker;
mod eval;
mod print;
pub mod snapshot;
mod stats;
mod step;
mod typing;

pub use attr::{AppInfo, Attr};
pub use checker::{Checker, Ctx, EvalPlugin, Options, PluginEvent};
pub use step::Step;
