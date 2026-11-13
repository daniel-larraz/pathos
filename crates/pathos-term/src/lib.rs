//! Terms: the hash-consed term store, literals and numbers

mod bitvec;
mod eostring;
mod kind;
mod lit;
mod num;
mod store;

pub use bitvec::BitVec;
pub use eostring::{EoString, NUM_CODES};
pub use kind::{EvalOp, Kind, LitKind, NodeKind, SymbolKind};
pub use lit::Lit;
pub use num::{Integer, Rational};
pub use store::{Args, Term, TermData, TermStore};
