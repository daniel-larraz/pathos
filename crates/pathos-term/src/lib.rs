//! Terms: the hash-consed term store, literals and numbers

mod bitvec;
pub mod codec;
mod eostring;
mod kind;
mod lit;
mod num;
mod store;

pub use bitvec::BitVec;
pub use eostring::{
    DEFAULT_MAX_CODE_POINT, EoString, MAX_MAX_CODE_POINT, MIN_MAX_CODE_POINT, max_code_point,
    num_codes, set_max_code_point,
};
pub use kind::{EvalOp, Kind, LitKind, NodeKind, SymbolKind};
pub use lit::Lit;
pub use num::{Integer, Rational};
pub use store::{Args, Limit, Term, TermData, TermStore};
