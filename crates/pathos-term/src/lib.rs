//! Terms: the hash-consed term store, literals and numbers
//!
//! Parts of this crate carry specifications that Verus checks
//! (`scripts/verify`, `docs/verus-spike.md`). They are compiled only under
//! `cfg(verus_keep_ghost)`, which Verus sets: a build with Cargo sees none of
//! them, and the crate does not depend on Verus's libraries.
#![cfg_attr(
    verus_keep_ghost,
    feature(proc_macro_hygiene),
    allow(unused_imports, unused_parens, unused_braces)
)]

/// A proof block, for Verus only: nothing in a build.
#[cfg(not(verus_keep_ghost))]
#[allow(unused_macros)]
macro_rules! proof {
    ($($t:tt)*) => {};
}
/// Declarations of ghost variables, for Verus only.
#[cfg(not(verus_keep_ghost))]
#[allow(unused_macros)]
macro_rules! proof_decl {
    ($($t:tt)*) => {};
}
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::prelude::*;

mod bitvec;
pub mod codec;
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
pub use store::{Args, Limit, Term, TermData, TermStore};
#[cfg(verus_keep_ghost)]
pub use store::{Tree, lemma_ground_node, tree_is_ground};
