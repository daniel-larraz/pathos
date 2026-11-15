//! The term store: an arena of hash-consed terms.
//!
//! A [`Term`] is a 32-bit handle into a [`TermStore`]. Compound terms and
//! literals are hash-consed, so two handles are equal exactly when the terms
//! are structurally equal. Symbols are not: every call to
//! [`TermStore::mk_symbol`] makes a new term, as in Ethos, where two symbols
//! with the same name and type are still different terms.
//!
//! The store never frees a term (design decision 2). It keeps, per term:
//!
//! - its [`TermData`] (12 bytes),
//! - its cached type (4 bytes),
//! - two flags, computed when the term is made (1 byte),
//!
//! plus one 4-byte slot in the hash-consing table for each compound term,
//! with the table kept at most 70% full. Literal values are stored once and
//! found through a second table of the same kind.
//!
//! Handles and positions are 32 bits. A store that runs out of them does
//! not panic; see [`TermStore::limit_exceeded`].

use std::hash::{BuildHasher, RandomState};
use std::num::NonZeroU32;

use crate::codec::{Reader, Writer};
use crate::kind::{EvalOp, Kind, LitKind, NodeKind, SymbolKind};
use crate::lit::Lit;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// A handle to a term in a [`TermStore`].
///
/// Handles are ordered by creation: a term's children always have smaller
/// handles than the term itself.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub struct Term(NonZeroU32);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Term {
    /// The handle for a position in the store; `None` for position 0 and
    /// past the 32-bit range.
    #[inline]
    fn from_index(i: usize) -> Option<Term> {
        let n = NonZeroU32::new(u32::try_from(i).ok()?)?;
        Some(Term(n))
    }

    /// The handle read back from an interning table, which holds only
    /// non-zero positions.
    #[inline]
    fn from_slot(slot: u32) -> Term {
        match NonZeroU32::new(slot) {
            Some(n) => Term(n),
            None => Term::first(),
        }
    }

    /// The first handle.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn first() -> Term {
        Term(NonZeroU32::MIN)
    }

    #[inline]
    fn index(self) -> usize {
        self.0.get() as usize
    }

    /// The position of the term in creation order, starting at 1.
    #[inline]
    pub fn id(self) -> u32 {
        self.0.get()
    }
}

/// A range of the store's child pool.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub struct Args {
    start: u32,
    len: u32,
}

/// What a term is.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub enum TermData {
    Type,
    BoolType,
    Any,
    /// Ethos's null expression; see [`Kind::Null`].
    Null,
    /// A named symbol; the name is [`TermStore::symbol_name`].
    Symbol(SymbolKind, u32),
    /// A literal; the value is [`TermStore::lit`].
    Lit(LitKind, u32),
    /// A binary application `(f a)`: by far the most common term.
    Apply([Term; 2]),
    /// Any other compound term, including applications that are not binary:
    /// those of programs and proof rules, which are not curried.
    Node(NodeKind, Args),
    /// An application of an `eo::` operator.
    Eval(EvalOp, Args),
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
const FLAG_EVAL: u8 = 1;
#[cfg_attr(verus_keep_ghost, verus_verify)]
const FLAG_NON_GROUND: u8 = 2;

/// An open-addressing table of term handles. The table does not hold keys:
/// the caller hashes a key, and compares it with the term behind each handle
/// the probe meets. Nothing is ever removed.
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct ConsTable {
    /// Term indices; 0 marks an empty slot.
    slots: Vec<u32>,
    len: usize,
    shift: u32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl ConsTable {
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires 6 <= bits <= 63,
        ensures
            r.wf(),
            r.shift == 64 - bits,
            r.len == 0,
            forall|i: int| 0 <= i < r.slots@.len() ==> r.slots@[i] == 0,
    ))]
    fn with_bits(bits: u32) -> ConsTable {
        proof! { lemma_count_nz_zeros(); }
        ConsTable {
            slots: vec![0; 1 << bits],
            len: 0,
            shift: 64 - bits,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires self.wf(),
        ensures r == path(self.shift, hash, 0), r < self.slots@.len(),
    ))]
    #[inline]
    fn start(&self, hash: u64) -> usize {
        proof! { lemma_path_in_range(self.shift, hash, 0); }
        (hash >> self.shift) as usize
    }

    #[inline]
    fn needs_growth(&self) -> bool {
        // keep the table at most 70% full (in 128 bits, where the products
        // cannot overflow)
        (self.len as u128) * 10 >= (self.slots.len() as u128) * 7
    }

    /// Looks for a handle whose term `is_match`. Returns it, or the empty
    /// slot where it belongs.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause, verus_spec(r =>
        requires
            self.wf(),
            forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0 ==>
                is_match.requires((#[trigger] self.slots@[p] as usize,)),
        ensures
            match r {
                Ok(c) => c != 0 && c <= u32::MAX && is_match.ensures((c,), true)
                    && exists|p: int| 0 <= p < self.slots@.len() && #[trigger] self.slots@[p] == c,
                Err(e) => e < self.slots@.len() && self.slots@[e as int] == 0
                    && exists|k: nat| #[trigger] no_match_before(self.slots@, self.shift, hash, k, is_match)
                        && e == path(self.shift, hash, k),
            },
    ))]
    #[inline]
    fn find(&self, hash: u64, is_match: impl Fn(usize) -> bool) -> Result<usize, usize> {
        proof! { lemma_path_in_range(self.shift, hash, 0); }
        let mask = self.slots.len() - 1;
        let mut i = self.start(hash);
        proof_decl! { let ghost mut k: nat = 0; }
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.wf(),
            mask == self.slots@.len() - 1,
            i < self.slots@.len(),
            i == path(self.shift, hash, k),
            no_match_before(self.slots@, self.shift, hash, k, is_match),
            forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0 ==>
                is_match.requires((#[trigger] self.slots@[p] as usize,)),
        ))]
        loop {
            let slot = self.slots[i];
            if slot == 0 {
                return Err(i);
            }
            if is_match(slot as usize) {
                return Ok(slot as usize);
            }
            proof! { lemma_path_in_range(self.shift, hash, k + 1); }
            i = (i + 1) & mask;
            proof! { k = k + 1; }
        }
    }

    /// Inserts a handle known not to be in the table.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause, verus_spec(
        requires old(self).wf(), index != 0,
        ensures
            final(self).wf(),
            final(self).shift == old(self).shift,
            exists|k: nat| #[trigger] probed(old(self).slots@, old(self).shift, hash, k)
                && old(self).slots@[path(old(self).shift, hash, k)] == 0
                && final(self).slots@ == old(self).slots@.update(path(old(self).shift, hash, k), index),
    ))]
    fn insert_new(&mut self, hash: u64, index: u32) {
        proof! { lemma_path_in_range(self.shift, hash, 0); }
        let mask = self.slots.len() - 1;
        let mut i = self.start(hash);
        proof_decl! { let ghost mut k: nat = 0; }
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self == old(self),
            self.wf(),
            mask == self.slots@.len() - 1,
            i < self.slots@.len(),
            i == path(self.shift, hash, k),
            probed(self.slots@, self.shift, hash, k),
        ))]
        while self.slots[i] != 0 {
            proof! { lemma_path_in_range(self.shift, hash, k + 1); }
            i = (i + 1) & mask;
            proof! { k = k + 1; }
        }
        proof! {
            lemma_count_nz_update(self.slots@, i as int, index);
            lemma_count_nz_bound(self.slots@);
            lemma_path_in_range(self.shift, hash, 0);
        }
        self.slots[i] = index;
        self.len += 1;
    }

    /// A table twice the size with the same handles, hashed by `hash_of`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0 ==>
                hash_of.requires((#[trigger] self.slots@[p] as usize,)),
        ensures
            r.wf(),
            forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0 ==>
                exists|h: u64| hash_of.ensures((#[trigger] self.slots@[p] as usize,), h)
                    && #[trigger] reach(r.slots@, r.shift, h, self.slots@[p]),
            forall|q: int| 0 <= q < r.slots@.len() && r.slots@[q] != 0 ==>
                exists|p: int| 0 <= p < self.slots@.len() && self.slots@[p] == #[trigger] r.slots@[q],
    ))]
    fn grown(&self, hash_of: impl Fn(usize) -> u64) -> ConsTable {
        proof! {
            axiom_vec_u32_len(&self.slots);
            lemma_path_in_range(self.shift, 0, 0);
            assert(cap_of(1) == 0x8000_0000_0000_0000) by (compute);
        }
        let bits = 64 - self.shift + 1;
        let mut table = ConsTable::with_bits(bits);
        #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
            iter.seq().unref() == self.slots@,
            table.wf(),
            table.shift == self.shift - 1,
            forall|p: int| 0 <= p < iter.index() && self.slots@[p] != 0 ==>
                exists|h: u64| hash_of.ensures((#[trigger] self.slots@[p] as usize,), h)
                    && #[trigger] reach(table.slots@, table.shift, h, self.slots@[p]),
            forall|q: int| 0 <= q < table.slots@.len() && table.slots@[q] != 0 ==>
                exists|p: int| 0 <= p < self.slots@.len() && self.slots@[p] == #[trigger] table.slots@[q],
            forall|p: int| 0 <= p < self.slots@.len() && self.slots@[p] != 0 ==>
                hash_of.requires((#[trigger] self.slots@[p] as usize,)),
        ))]
        for &slot in &self.slots {
            if slot != 0 {
                proof_decl! {
                    let ghost before = table.slots@;
                    let ghost at = iter.index() as int;
                    assert(slot == self.slots@[at]);
                }
                let h = hash_of(slot as usize);
                table.insert_new(h, slot);
                proof! {
                    let k = choose|k: nat| #[trigger] probed(before, table.shift, h, k)
                        && before[path(table.shift, h, k)] == 0
                        && table.slots@ == before.update(path(table.shift, h, k), slot);
                    let z = path(table.shift, h, k);
                    lemma_path_in_range(table.shift, h, k);
                    // the new handle is where its probe ends
                    assert(reach_at(table.slots@, table.shift, h, slot, k)) by {
                        assert forall|j: nat| j < k implies table.slots@[#[trigger] path(table.shift, h, j)] != 0 by {
                            lemma_path_in_range(table.shift, h, j);
                        }
                    }
                    assert(reach(table.slots@, table.shift, h, slot));
                    assert(hash_of.ensures((self.slots@[at] as usize,), h));
                    // and the handles put in before are still where theirs end
                    assert forall|p: int| 0 <= p < at && self.slots@[p] != 0 implies
                        exists|h2: u64| hash_of.ensures((#[trigger] self.slots@[p] as usize,), h2)
                            && #[trigger] reach(table.slots@, table.shift, h2, self.slots@[p]) by {
                        let h2 = choose|h2: u64| hash_of.ensures((self.slots@[p] as usize,), h2)
                            && #[trigger] reach(before, table.shift, h2, self.slots@[p]);
                        lemma_reach_update(before, table.shift, h2, self.slots@[p], z, slot);
                    }
                    assert forall|q: int| 0 <= q < table.slots@.len() && table.slots@[q] != 0 implies
                        exists|p: int| 0 <= p < self.slots@.len() && self.slots@[p] == #[trigger] table.slots@[q] by {
                        if q == z {
                            assert(self.slots@[at] == table.slots@[q]);
                        } else {
                            assert(before[q] == table.slots@[q]);
                        }
                    }
                }
            }
        }
        table
    }
}

/// The keys of the interning hash, chosen at random for each store. An
/// input cannot be built to make many terms collide without knowing them,
/// so lookups stay short on hostile proofs. Nothing but the layout of the
/// table depends on the keys.
#[derive(Copy, Clone)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
struct HashKeys {
    k0: u64,
    k1: u64,
    k2: u64,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl HashKeys {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn random(state: &RandomState) -> HashKeys {
        // Odd multipliers, so that multiplying by them loses nothing.
        HashKeys {
            k0: state.hash_one(0u8),
            k1: state.hash_one(1u8) | 1,
            k2: state.hash_one(2u8) | 1,
        }
    }
}

/// The two halves of the 128-bit product, folded together.
#[inline]
fn folded_mul(a: u64, b: u64) -> u64 {
    let full = u128::from(a) * u128::from(b);
    (full as u64) ^ ((full >> 64) as u64)
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[inline]
fn hash_node(keys: &HashKeys, tag: u32, children: &[Term]) -> u64 {
    let mut h = keys.k0 ^ (u64::from(tag) << 32) ^ children.len() as u64;
    // two children per multiplication
    let (pairs, rest) = children.as_chunks::<2>();
    for [a, b] in pairs {
        let x = (u64::from(a.0.get()) << 32) | u64::from(b.0.get());
        h = folded_mul(h ^ x, keys.k1);
    }
    if let [c] = rest {
        h = folded_mul(h ^ u64::from(c.0.get()), keys.k1);
    }
    // a last round, so that the top bits, which pick the slot, depend on
    // every bit of the state
    folded_mul(h, keys.k2)
}

/// The tag hashed and compared for a compound kind.
/// The hash of a literal's value.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
#[inline]
fn hash_lit(hasher: &RandomState, lit: &Lit) -> u64 {
    hasher.hash_one(lit)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[inline]
fn tag_of(kind: Kind) -> u32 {
    match kind {
        Kind::Node(n) => n as u32,
        Kind::Eval(op) => 64 + op as u32,
        Kind::Type | Kind::BoolType | Kind::Any | Kind::Null | Kind::Symbol(_) | Kind::Lit(_) => {
            u32::MAX
        }
    }
}

/// A size limit of the store's 32-bit handles and positions.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub enum Limit {
    /// More than 2^32 - 1 terms.
    Terms,
    /// More than 2^32 - 1 children of non-binary terms in total.
    Children,
}

impl std::fmt::Display for Limit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Limit::Terms => "more than 4294967295 terms",
            Limit::Children => "more than 4294967295 children of non-binary terms",
        })
    }
}

/// The arena of terms. See the module documentation.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct TermStore {
    nodes: Vec<TermData>,
    types: Vec<Option<Term>>,
    flags: Vec<u8>,
    /// The children of `Node` and `Eval` terms, back to back.
    child_pool: Vec<Term>,
    table: ConsTable,
    names: Vec<Box<str>>,
    lits: Vec<Lit>,
    /// The literal terms, keyed by their values in `lits`.
    lit_table: ConsTable,
    keys: HashKeys,
    lit_hasher: RandomState,
    /// Set when the store ran out of 32-bit ids or positions.
    limit: Option<Limit>,
    /// How many terms were asked for, new or not.
    mk_count: u64,
    ty_type: Term,
    ty_bool: Term,
    any: Term,
    null: Term,
}

impl Default for TermStore {
    fn default() -> Self {
        TermStore::new()
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl TermStore {
    pub fn new() -> TermStore {
        let mut s = TermStore {
            // index 0 is unused, so that handles are non-zero
            nodes: vec![TermData::Any],
            types: vec![None],
            flags: vec![0],
            child_pool: Vec::new(),
            table: ConsTable::with_bits(10),
            names: Vec::new(),
            lits: Vec::new(),
            lit_table: ConsTable::with_bits(6),
            keys: HashKeys::random(&RandomState::new()),
            lit_hasher: RandomState::new(),
            limit: None,
            mk_count: 0,
            ty_type: Term::first(),
            ty_bool: Term::first(),
            any: Term::first(),
            null: Term::first(),
        };
        s.ty_type = s.push(TermData::Type, 0).unwrap_or(s.ty_type);
        s.ty_bool = s.push(TermData::BoolType, 0).unwrap_or(s.ty_bool);
        s.any = s
            .push(TermData::Any, FLAG_EVAL | FLAG_NON_GROUND)
            .unwrap_or(s.any);
        s.null = s.push(TermData::Null, 0).unwrap_or(s.null);
        s
    }

    /// The number of terms made so far.
    pub fn len(&self) -> usize {
        self.nodes.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// How many times a symbol, literal or compound term was asked for,
    /// whether or not it existed already. For `--stats`.
    pub fn mk_count(&self) -> u64 {
        self.mk_count
    }

    /// The number of symbols made so far.
    pub fn symbol_count(&self) -> usize {
        self.names.len()
    }

    /// The number of distinct literals made so far.
    pub fn lit_count(&self) -> usize {
        self.lits.len()
    }

    /// Adds a term. Returns `None`, and records the limit, when the store
    /// is full.
    fn push(&mut self, data: TermData, flags: u8) -> Option<Term> {
        let Some(t) = Term::from_index(self.nodes.len()) else {
            self.limit = Some(Limit::Terms);
            return None;
        };
        self.nodes.push(data);
        self.types.push(None);
        self.flags.push(flags);
        Some(t)
    }

    /// The limit the store has run into, if any.
    ///
    /// The functions that make terms cannot fail: they are called from
    /// everywhere, deep inside typing and evaluation. When the store is
    /// full they record the limit here and return `eo::?` in place of the
    /// term. What is computed from then on is meaningless, so whoever
    /// drives the store must check this before trusting a result: the
    /// parser does after each command.
    pub fn limit_exceeded(&self) -> Option<Limit> {
        self.limit
    }

    /// The term `Type`.
    pub fn mk_type(&self) -> Term {
        self.ty_type
    }

    /// The term `Bool`.
    pub fn mk_bool_type(&self) -> Term {
        self.ty_bool
    }

    /// The term `eo::?`.
    pub fn mk_any(&self) -> Term {
        self.any
    }

    /// Ethos's null expression: ground, not evaluatable, never typed.
    pub fn mk_null(&self) -> Term {
        self.null
    }

    /// Makes a new symbol with the given type. Never returns an existing
    /// term.
    pub fn mk_symbol(&mut self, kind: SymbolKind, name: &str, ty: Term) -> Term {
        // there are no more names than terms, so this fits when the term does
        self.mk_count = self.mk_count.wrapping_add(1);
        let name_id = self.names.len() as u32;
        let flags = match kind {
            SymbolKind::ProgramConst => FLAG_EVAL,
            SymbolKind::Param => FLAG_NON_GROUND,
            _ => 0,
        };
        let Some(t) = self.push(TermData::Symbol(kind, name_id), flags) else {
            return self.any;
        };
        self.names.push(name.into());
        self.types[t.index()] = Some(ty);
        t
    }

    fn lit_at(&self, i: usize) -> Option<&Lit> {
        match self.nodes[i] {
            TermData::Lit(_, id) => Some(&self.lits[id as usize]),
            _ => None,
        }
    }

    /// The term for a literal value; equal values give the same term.
    pub fn mk_lit(&mut self, lit: Lit) -> Term {
        self.mk_count = self.mk_count.wrapping_add(1);
        let hash = hash_lit(&self.lit_hasher, &lit);
        let slot = match self.lit_table.find(hash, |i| self.lit_at(i) == Some(&lit)) {
            Ok(found) => return Term::from_slot(found as u32),
            Err(slot) => slot,
        };
        // there are no more literals than terms
        let lit_id = self.lits.len() as u32;
        let Some(t) = self.push(TermData::Lit(lit.kind(), lit_id), 0) else {
            return self.any;
        };
        self.lits.push(lit);
        self.lit_table.slots[slot] = t.0.get();
        self.lit_table.len += 1;
        if self.lit_table.needs_growth() {
            let grown = self.lit_table.grown(|i| match self.lit_at(i) {
                Some(l) => hash_lit(&self.lit_hasher, l),
                None => 0,
            });
            self.lit_table = grown;
        }
        t
    }

    /// The binary application `(f a)`.
    #[inline]
    pub fn mk_apply(&mut self, f: Term, a: Term) -> Term {
        self.mk(Kind::APPLY, &[f, a])
    }

    /// The term of a compound kind with the given children; equal arguments
    /// give the same term. This does no desugaring or evaluation.
    ///
    /// `Type`, `Bool` and `eo::?` are also accepted, without children.
    /// Symbols and literals are made with [`TermStore::mk_symbol`] and
    /// [`TermStore::mk_lit`]; asking for one here is a bug in the caller.
    pub fn mk(&mut self, kind: Kind, children: &[Term]) -> Term {
        match kind {
            Kind::Type => return self.ty_type,
            Kind::BoolType => return self.ty_bool,
            Kind::Any => return self.any,
            Kind::Null => return self.null,
            Kind::Symbol(_) | Kind::Lit(_) => {
                panic!("TermStore::mk called with the atomic kind {kind}")
            }
            Kind::Node(_) | Kind::Eval(_) => {}
        }
        self.mk_count = self.mk_count.wrapping_add(1);
        let tag = tag_of(kind);
        let hash = hash_node(&self.keys, tag, children);
        let found = self.table.find(hash, |cand| {
            tag_of(self.kind_at(cand)) == tag && self.children_at(cand) == children
        });
        let slot = match found {
            Ok(cand) => return Term::from_slot(cand as u32),
            Err(slot) => slot,
        };
        // not found: make it
        let mut flags = 0;
        for c in children {
            flags |= self.flags[c.index()];
        }
        // An operator applied to nothing counts as a leaf, as in Ethos.
        if matches!(kind, Kind::Eval(_)) && !children.is_empty() {
            flags |= FLAG_EVAL;
        }
        let data = match (kind, children) {
            (Kind::Node(NodeKind::Apply), &[f, a]) => TermData::Apply([f, a]),
            _ => {
                // the end of the range must fit too: `children_at` adds
                let (Ok(start), Ok(len)) = (
                    u32::try_from(self.child_pool.len()),
                    u32::try_from(children.len()),
                ) else {
                    self.limit = Some(Limit::Children);
                    return self.any;
                };
                if start.checked_add(len).is_none() {
                    self.limit = Some(Limit::Children);
                    return self.any;
                }
                let args = Args { start, len };
                match kind {
                    Kind::Node(n) => TermData::Node(n, args),
                    Kind::Eval(op) => TermData::Eval(op, args),
                    // atomic kinds returned above
                    _ => return self.any,
                }
            }
        };
        let Some(t) = self.push(data, flags) else {
            return self.any;
        };
        if !matches!(data, TermData::Apply(_)) {
            self.child_pool.extend_from_slice(children);
        }
        self.table.slots[slot] = t.0.get();
        self.table.len += 1;
        if self.table.needs_growth() {
            let grown = self
                .table
                .grown(|i| hash_node(&self.keys, tag_of(self.kind_at(i)), self.children_at(i)));
            self.table = grown;
        }
        t
    }

    #[inline]
    fn kind_at(&self, i: usize) -> Kind {
        match self.nodes[i] {
            TermData::Type => Kind::Type,
            TermData::BoolType => Kind::BoolType,
            TermData::Any => Kind::Any,
            TermData::Null => Kind::Null,
            TermData::Symbol(k, _) => Kind::Symbol(k),
            TermData::Lit(k, _) => Kind::Lit(k),
            TermData::Apply(_) => Kind::APPLY,
            TermData::Node(k, _) => Kind::Node(k),
            TermData::Eval(op, _) => Kind::Eval(op),
        }
    }

    #[inline]
    fn children_at(&self, i: usize) -> &[Term] {
        match &self.nodes[i] {
            TermData::Apply(c) => c,
            TermData::Node(_, a) | TermData::Eval(_, a) => {
                &self.child_pool[a.start as usize..(a.start + a.len) as usize]
            }
            _ => &[],
        }
    }

    /// What the term is.
    #[inline]
    pub fn data(&self, t: Term) -> TermData {
        self.nodes[t.index()]
    }

    #[inline]
    pub fn kind(&self, t: Term) -> Kind {
        self.kind_at(t.index())
    }

    /// The children of a compound term; empty for atoms.
    #[inline]
    pub fn children(&self, t: Term) -> &[Term] {
        self.children_at(t.index())
    }

    #[inline]
    pub fn num_children(&self, t: Term) -> usize {
        match &self.nodes[t.index()] {
            TermData::Apply(_) => 2,
            TermData::Node(_, a) | TermData::Eval(_, a) => a.len as usize,
            _ => 0,
        }
    }

    /// The `i`-th child. Panics if there is none: callers check the shape of
    /// a term before taking it apart.
    #[inline]
    pub fn child(&self, t: Term, i: usize) -> Term {
        self.children_at(t.index())[i]
    }

    /// The value of a literal term.
    pub fn lit(&self, t: Term) -> Option<&Lit> {
        match self.nodes[t.index()] {
            TermData::Lit(_, id) => Some(&self.lits[id as usize]),
            _ => None,
        }
    }

    /// The name of a symbol.
    pub fn symbol_name(&self, t: Term) -> Option<&str> {
        match self.nodes[t.index()] {
            TermData::Symbol(_, id) => Some(&self.names[id as usize]),
            _ => None,
        }
    }

    /// The cached type of the term, if one has been set.
    #[inline]
    pub fn ty(&self, t: Term) -> Option<Term> {
        self.types[t.index()]
    }

    /// Caches the type of the term.
    #[inline]
    pub fn set_ty(&mut self, t: Term, ty: Term) {
        self.types[t.index()] = Some(ty);
    }

    /// Whether the term contains an `eo::` operator application, a program
    /// symbol or `eo::?`.
    #[inline]
    pub fn is_evaluatable(&self, t: Term) -> bool {
        self.flags[t.index()] & FLAG_EVAL != 0
    }

    /// Whether the term contains no parameter and no `eo::?`.
    #[inline]
    pub fn is_ground(&self, t: Term) -> bool {
        self.flags[t.index()] & FLAG_NON_GROUND == 0
    }

    /// The bytes held by the store's tables, for the benchmark.
    #[cfg_attr(verus_keep_ghost, verus_verify(external))]
    pub fn heap_bytes(&self) -> usize {
        use std::mem::size_of;
        self.nodes.capacity() * size_of::<TermData>()
            + self.types.capacity() * size_of::<Option<Term>>()
            + self.flags.capacity()
            + self.child_pool.capacity() * size_of::<Term>()
            + self.table.slots.capacity() * size_of::<u32>()
    }
}

/// The codes of [`TermData`] in a snapshot.
mod tag {
    pub const TYPE: u8 = 0;
    pub const BOOL_TYPE: u8 = 1;
    pub const ANY: u8 = 2;
    pub const NULL: u8 = 3;
    pub const SYMBOL: u8 = 4;
    pub const LIT: u8 = 5;
    pub const APPLY: u8 = 6;
    pub const NODE: u8 = 7;
    pub const EVAL: u8 = 8;
}

impl TermStore {
    /// Writes the store, for a snapshot: the terms in order, their cached
    /// types, the names and the literal values. The flags and the interning
    /// tables are not written; reading computes them again.
    pub fn write_to(&self, w: &mut Writer) {
        w.len(self.len());
        for i in 1..self.nodes.len() {
            let (tag, sub, a, b) = match self.nodes[i] {
                TermData::Type => (tag::TYPE, 0, 0, 0),
                TermData::BoolType => (tag::BOOL_TYPE, 0, 0, 0),
                TermData::Any => (tag::ANY, 0, 0, 0),
                TermData::Null => (tag::NULL, 0, 0, 0),
                TermData::Symbol(k, name) => (tag::SYMBOL, k as u8, name, 0),
                TermData::Lit(k, lit) => (tag::LIT, k as u8, lit, 0),
                TermData::Apply([f, x]) => (tag::APPLY, 0, f.id(), x.id()),
                TermData::Node(k, args) => (tag::NODE, k as u8, args.start, args.len),
                TermData::Eval(op, args) => (tag::EVAL, op as u8, args.start, args.len),
            };
            w.u8(tag);
            w.u8(sub);
            w.u32(a);
            w.u32(b);
            w.u32(self.types[i].map_or(0, Term::id));
        }
        w.len(self.child_pool.len());
        for c in &self.child_pool {
            w.u32(c.id());
        }
        w.len(self.names.len());
        for name in &self.names {
            w.str(name);
        }
        w.len(self.lits.len());
        for lit in &self.lits {
            lit.write_to(w);
        }
        w.u64(self.mk_count);
    }

    /// Reads a store written by [`TermStore::write_to`]. Returns `None`
    /// unless the input describes a store that the functions of this module
    /// could have built:
    ///
    /// - the first terms are `Type`, `Bool`, `eo::?` and the null term, and
    ///   there is no other term of those kinds;
    /// - every child and every cached type is a term of the store, and a
    ///   child comes before its parent;
    /// - the symbols use the names in order, and the literals the values;
    /// - no compound term and no literal value is there twice.
    ///
    /// Whether the terms make sense to the checker (say, that a function
    /// type has an argument) is not checked here.
    pub fn read_from(r: &mut Reader) -> Option<TermStore> {
        // a term takes 14 bytes
        let n = r.len(14)?;
        let mut s = TermStore::new();
        if n < s.len() {
            return None;
        }
        let fixed = s.len();
        let mut raw = Vec::with_capacity(n);
        for _ in 0..n {
            raw.push((r.u8()?, r.u8()?, r.u32()?, r.u32()?, r.u32()?));
        }
        let pool_len = r.len(4)?;
        let mut pool = Vec::with_capacity(pool_len);
        for _ in 0..pool_len {
            pool.push(r.u32()?);
        }
        let names_len = r.len(4)?;
        let mut names: Vec<Box<str>> = Vec::with_capacity(names_len);
        for _ in 0..names_len {
            names.push(r.str()?.into());
        }
        let lits_len = r.len(2)?;
        let mut lits = Vec::with_capacity(lits_len);
        for _ in 0..lits_len {
            lits.push(Lit::read_from(r)?);
        }
        let mk_count = r.u64()?;

        // Size the tables for what is coming, so that they do not grow.
        let bits = |items: usize| (items * 2).next_power_of_two().trailing_zeros().max(6);
        s.table = ConsTable::with_bits(bits(n));
        s.lit_table = ConsTable::with_bits(bits(lits_len));
        s.nodes.reserve(n - fixed);
        s.types.reserve(n - fixed);
        s.flags.reserve(n - fixed);
        s.child_pool.reserve(pool_len);
        s.lits = lits;

        let (mut next_name, mut next_lit, mut next_child) = (0usize, 0usize, 0usize);
        for (i, &(tag, sub, a, b, _)) in raw.iter().enumerate() {
            // this term's handle, and the test for an earlier term
            let index = i + 1;
            let earlier = |id: u32| (id != 0 && (id as usize) < index).then(|| Term::from_slot(id));
            if index <= fixed {
                // the terms every store starts with, in their places
                let expected = match s.nodes[index] {
                    TermData::Type => tag::TYPE,
                    TermData::BoolType => tag::BOOL_TYPE,
                    TermData::Any => tag::ANY,
                    _ => tag::NULL,
                };
                if tag != expected {
                    return None;
                }
                continue;
            }
            let sub_index = usize::from(sub);
            let (data, flags) = match tag {
                tag::SYMBOL => {
                    let kind = *SymbolKind::ALL.get(sub_index)?;
                    if a as usize != next_name || next_name >= names.len() {
                        return None;
                    }
                    next_name += 1;
                    let flags = match kind {
                        SymbolKind::ProgramConst => FLAG_EVAL,
                        SymbolKind::Param => FLAG_NON_GROUND,
                        _ => 0,
                    };
                    (TermData::Symbol(kind, a), flags)
                }
                tag::LIT => {
                    let kind = *LitKind::ALL.get(sub_index)?;
                    if a as usize != next_lit || s.lits.get(next_lit)?.kind() != kind {
                        return None;
                    }
                    let lit = &s.lits[next_lit];
                    next_lit += 1;
                    let hash = s.lit_hasher.hash_one(lit);
                    let slot = (s.lit_table)
                        .find(hash, |c| s.lit_at(c) == Some(lit))
                        .err()?;
                    s.lit_table.slots[slot] = u32::try_from(index).ok()?;
                    s.lit_table.len += 1;
                    (TermData::Lit(kind, a), 0)
                }
                tag::APPLY | tag::NODE | tag::EVAL => {
                    let (kind, data) = match tag {
                        tag::APPLY => {
                            let pair = [earlier(a)?, earlier(b)?];
                            (Kind::APPLY, TermData::Apply(pair))
                        }
                        _ => {
                            // the children follow those of the term before
                            let end = (a as usize).checked_add(b as usize)?;
                            if a as usize != next_child || end > pool.len() {
                                return None;
                            }
                            for &c in &pool[next_child..end] {
                                s.child_pool.push(earlier(c)?);
                            }
                            next_child = end;
                            let args = Args { start: a, len: b };
                            if tag == tag::EVAL {
                                let op = EvalOp::ALL.get(sub_index)?.0;
                                (Kind::Eval(op), TermData::Eval(op, args))
                            } else {
                                let k = *NodeKind::ALL.get(sub_index)?;
                                // binary applications have their own form
                                if k == NodeKind::Apply && b == 2 {
                                    return None;
                                }
                                (Kind::Node(k), TermData::Node(k, args))
                            }
                        }
                    };
                    let children: &[Term] = match &data {
                        TermData::Apply(pair) => pair,
                        _ => &s.child_pool[a as usize..],
                    };
                    let mut flags = 0;
                    for c in children {
                        flags |= s.flags[c.index()];
                    }
                    if matches!(kind, Kind::Eval(_)) && !children.is_empty() {
                        flags |= FLAG_EVAL;
                    }
                    let ktag = tag_of(kind);
                    let hash = hash_node(&s.keys, ktag, children);
                    let slot = (s.table)
                        .find(hash, |c| {
                            tag_of(s.kind_at(c)) == ktag && s.children_at(c) == children
                        })
                        .err()?;
                    s.table.slots[slot] = u32::try_from(index).ok()?;
                    s.table.len += 1;
                    (data, flags)
                }
                _ => return None,
            };
            s.push(data, flags)?;
        }
        if next_name != names.len() || next_lit != s.lits.len() || next_child != pool.len() {
            return None;
        }
        s.names = names;
        // the cached types: any term of the store
        for (i, &(_, _, _, _, ty)) in raw.iter().enumerate() {
            if ty != 0 {
                if ty as usize > n {
                    return None;
                }
                s.types[i + 1] = Some(Term::from_slot(ty));
            }
        }
        s.mk_count = mk_count;
        Some(s)
    }

    /// The term with the given id, if the store has it. For reading
    /// snapshots.
    pub fn term_with_id(&self, id: u32) -> Option<Term> {
        (id != 0 && (id as usize) <= self.len()).then(|| Term::from_slot(id))
    }
}

/// The store's invariant and its view as trees, for Verus.
#[cfg(verus_keep_ghost)]
verus! {

// pathos is built for 64-bit targets only
global size_of usize == 8;

pub assume_specification[ RandomState::new ]() -> RandomState;

/// Assumed: a vector's contents take at most `isize::MAX` bytes, as the
/// standard library guarantees. (Verus does not model allocation: a vector
/// that cannot be allocated ends the program, by a panic or an abort, and
/// nothing is proved about that.)
#[verifier::external_body]
proof fn axiom_vec_u32_len(v: &Vec<u32>)
    ensures v@.len() <= 0x1fff_ffff_ffff_ffff,
{
}

// ---- the open-addressing table ----

/// The number of slots of a table that shifts hashes by `shift`.
spec fn cap_of(shift: u32) -> int {
    (1usize << ((64 - shift) as u32)) as int
}

/// The slot after `i`, cyclically.
spec fn next_of(cap: int, i: int) -> int {
    (((i + 1) as usize) & ((cap - 1) as usize)) as int
}

/// The `k`-th slot a lookup of `hash` visits.
spec fn path(shift: u32, hash: u64, k: nat) -> int
    decreases k,
{
    if k == 0 {
        ((hash >> shift) as usize) as int
    } else {
        next_of(cap_of(shift), path(shift, hash, (k - 1) as nat))
    }
}

proof fn lemma_path_in_range(shift: u32, hash: u64, k: nat)
    requires 1 <= shift <= 58,
    ensures
        0 <= path(shift, hash, k) < cap_of(shift),
        64 <= cap_of(shift) <= 0x8000_0000_0000_0000,
    decreases k,
{
    assert(64 <= (1usize << ((64 - shift) as u32)) <= 0x8000_0000_0000_0000) by (bit_vector)
        requires 1 <= shift <= 58;
    if k == 0 {
        assert((hash >> shift) < (1usize << ((64 - shift) as u32))) by (bit_vector)
            requires 1 <= shift <= 58;
    } else {
        lemma_path_in_range(shift, hash, (k - 1) as nat);
        let i = path(shift, hash, (k - 1) as nat) as usize;
        let mask = (cap_of(shift) - 1) as usize;
        assert(((i + 1) as usize & mask) <= mask) by (bit_vector);
    }
}

/// The first `k` slots a lookup of `hash` visits are taken.
spec fn probed(slots: Seq<u32>, shift: u32, hash: u64, k: nat) -> bool {
    forall|j: nat| j < k ==> slots[#[trigger] path(shift, hash, j)] != 0
}

/// A lookup of `hash` meets the handle `c` at its `k`-th slot, with no
/// empty slot before.
spec fn reach_at(slots: Seq<u32>, shift: u32, hash: u64, c: u32, k: nat) -> bool {
    probed(slots, shift, hash, k) && slots[path(shift, hash, k)] == c
}

/// A lookup of `hash` meets the handle `c` before it meets an empty slot.
spec fn reach(slots: Seq<u32>, shift: u32, hash: u64, c: u32) -> bool {
    exists|k: nat| reach_at(slots, shift, hash, c, k)
}

/// The first `k` slots a lookup of `hash` visits hold handles that
/// `is_match` rejects.
spec fn no_match_before<F: Fn(usize) -> bool>(slots: Seq<u32>, shift: u32, hash: u64, k: nat, is_match: F) -> bool {
    forall|j: nat| j < k ==> slots[#[trigger] path(shift, hash, j)] != 0
        && is_match.ensures((slots[path(shift, hash, j)] as usize,), false)
}

/// Filling an empty slot leaves every handle where lookups find it.
proof fn lemma_reach_update(slots: Seq<u32>, shift: u32, hash: u64, c: u32, z: int, v: u32)
    requires
        1 <= shift <= 58,
        slots.len() == cap_of(shift),
        reach(slots, shift, hash, c),
        c != 0,
        0 <= z < slots.len(),
        slots[z] == 0,
    ensures reach(slots.update(z, v), shift, hash, c),
{
    let k = choose|k: nat| reach_at(slots, shift, hash, c, k);
    let after = slots.update(z, v);
    lemma_path_in_range(shift, hash, k);
    assert forall|j: nat| j < k implies after[#[trigger] path(shift, hash, j)] != 0 by {
        lemma_path_in_range(shift, hash, j);
    }
    assert(reach_at(after, shift, hash, c, k));
}

/// The number of slots that are taken.
spec fn count_nz(s: Seq<u32>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_nz(s.drop_last()) + (if s.last() != 0 { 1nat } else { 0nat })
    }
}

proof fn lemma_count_nz_bound(s: Seq<u32>)
    ensures count_nz(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_nz_bound(s.drop_last());
    }
}

proof fn lemma_count_nz_zeros()
    ensures forall|s: Seq<u32>| (forall|i: int| 0 <= i < s.len() ==> s[i] == 0) ==> #[trigger] count_nz(s) == 0,
{
    assert forall|s: Seq<u32>| (forall|i: int| 0 <= i < s.len() ==> s[i] == 0) implies #[trigger] count_nz(s) == 0 by {
        lemma_count_nz_zeros_of(s);
    }
}

proof fn lemma_count_nz_zeros_of(s: Seq<u32>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == 0,
    ensures count_nz(s) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_nz_zeros_of(s.drop_last());
    }
}

proof fn lemma_count_nz_update(s: Seq<u32>, i: int, v: u32)
    requires 0 <= i < s.len(), s[i] == 0, v != 0,
    ensures count_nz(s.update(i, v)) == count_nz(s) + 1,
    decreases s.len(),
{
    let t = s.update(i, v);
    if i == s.len() - 1 {
        assert(t.drop_last() == s.drop_last());
    } else {
        assert(t.drop_last() == s.drop_last().update(i, v));
        lemma_count_nz_update(s.drop_last(), i, v);
    }
}

impl ConsTable {
    spec fn wf(&self) -> bool {
        &&& 1 <= self.shift <= 58
        &&& self.slots@.len() == cap_of(self.shift)
        &&& self.len == count_nz(self.slots@)
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use crate::num::Integer;

    #[test]
    fn layout() {
        assert_eq!(std::mem::size_of::<Term>(), 4);
        assert_eq!(std::mem::size_of::<Option<Term>>(), 4);
        assert_eq!(std::mem::size_of::<TermData>(), 12);
    }

    #[test]
    fn hash_consing() {
        let mut s = TermStore::new();
        let ty = s.mk_type();
        let f = s.mk_symbol(SymbolKind::Const, "f", ty);
        let a = s.mk_symbol(SymbolKind::Const, "a", ty);
        let fa = s.mk_apply(f, a);
        assert_eq!(fa, s.mk_apply(f, a));
        assert_eq!(fa, s.mk(Kind::APPLY, &[f, a]));
        assert_ne!(fa, s.mk(Kind::APPLY_OPAQUE, &[f, a]));
        assert_ne!(fa, s.mk(Kind::APPLY, &[f, a, a]));
        assert_ne!(fa, s.mk(Kind::APPLY, &[f]));
        assert_eq!(s.mk(Kind::APPLY, &[f]), s.mk(Kind::APPLY, &[f]));
        assert_eq!(s.children(fa), &[f, a]);
        assert_eq!(s.kind(fa), Kind::APPLY);
        let t3 = s.mk(Kind::APPLY, &[f, a, a]);
        assert_eq!(s.children(t3), &[f, a, a]);
        assert_eq!(s.num_children(t3), 3);
        // symbols are never shared
        assert_ne!(a, s.mk_symbol(SymbolKind::Const, "a", ty));
        assert_eq!(s.symbol_name(a), Some("a"));
        assert_eq!(s.ty(a), Some(ty));
        assert_eq!(s.ty(fa), None);
    }

    #[test]
    fn literals() {
        let mut s = TermStore::new();
        let one = s.mk_lit(Lit::Numeral(Integer::from(1u32)));
        assert_eq!(one, s.mk_lit(Lit::Numeral(Integer::from(1u32))));
        assert_ne!(one, s.mk_lit(Lit::Numeral(Integer::from(2u32))));
        assert_eq!(s.kind(one), Kind::NUMERAL);
        assert_eq!(s.lit(one).unwrap().to_string(), "1");
    }

    #[test]
    fn flags() {
        let mut s = TermStore::new();
        let ty = s.mk_type();
        let c = s.mk_symbol(SymbolKind::Const, "c", ty);
        let p = s.mk_symbol(SymbolKind::Param, "p", ty);
        let prog = s.mk_symbol(SymbolKind::ProgramConst, "prog", ty);
        assert!(s.is_ground(c) && !s.is_evaluatable(c));
        assert!(!s.is_ground(p) && !s.is_evaluatable(p));
        assert!(s.is_ground(prog) && s.is_evaluatable(prog));
        let any = s.mk_any();
        assert!(!s.is_ground(any) && s.is_evaluatable(any));
        let cp = s.mk_apply(c, p);
        assert!(!s.is_ground(cp) && !s.is_evaluatable(cp));
        let add = s.mk(Kind::Eval(EvalOp::Add), &[c, c]);
        assert!(s.is_ground(add) && s.is_evaluatable(add));
        let outer = s.mk_apply(c, add);
        assert!(s.is_evaluatable(outer));
        // an operator with no arguments is a leaf
        let empty = s.mk(Kind::Eval(EvalOp::Add), &[]);
        assert!(!s.is_evaluatable(empty));
    }

    #[test]
    fn table_growth_keeps_terms() {
        let mut s = TermStore::new();
        let ty = s.mk_type();
        let f = s.mk_symbol(SymbolKind::Const, "f", ty);
        let mut terms = vec![f];
        for i in 0..20_000 {
            let prev = terms[i];
            terms.push(s.mk_apply(f, prev));
        }
        let before = s.len();
        for i in 0..20_000 {
            assert_eq!(s.mk_apply(f, terms[i]), terms[i + 1]);
        }
        assert_eq!(s.len(), before);
    }

    /// A store with terms of every form.
    fn sample() -> TermStore {
        let mut s = TermStore::new();
        let ty = s.mk_type();
        let int = s.mk_symbol(SymbolKind::Const, "Int", ty);
        let x = s.mk_symbol(SymbolKind::Param, "x", int);
        let f = s.mk_symbol(SymbolKind::Const, "f", ty);
        let one = s.mk_lit(Lit::Numeral(Integer::from(1u32)));
        let half = s.mk_lit(Lit::Rational(crate::Rational::parse("-1/2").unwrap()));
        let bits = s.mk_lit(Lit::Binary(crate::BitVec::parse("0101", 2).unwrap()));
        let text = s.mk_lit(Lit::String(crate::EoString::parse("a\\u{e9}", true)));
        let fx = s.mk_apply(f, x);
        let add = s.mk(Kind::Eval(EvalOp::Add), &[one, fx, half]);
        let tuple = s.mk(Kind::TUPLE, &[]);
        let fun = s.mk(Kind::FUNCTION_TYPE, &[int, int, ty]);
        s.mk(Kind::APPLY, &[f, bits, text, add, tuple, fun]);
        s.set_ty(fx, int);
        s
    }

    fn written(s: &TermStore) -> Vec<u8> {
        let mut w = Writer::new();
        s.write_to(&mut w);
        w.bytes
    }

    #[test]
    fn a_store_read_back_is_the_same_store() {
        let s = sample();
        let bytes = written(&s);
        let mut r = Reader::new(&bytes);
        let mut back = TermStore::read_from(&mut r).unwrap();
        assert!(r.is_at_end());
        assert_eq!(written(&back), bytes);
        // flags are computed again, and terms are found again
        for i in 1..=s.len() {
            let t = Term::from_index(i).unwrap();
            assert_eq!(back.is_ground(t), s.is_ground(t));
            assert_eq!(back.is_evaluatable(t), s.is_evaluatable(t));
        }
        let len = back.len();
        let one = back.mk_lit(Lit::Numeral(Integer::from(1u32)));
        let f = back.term_with_id(7).unwrap();
        let x = back.term_with_id(6).unwrap();
        assert_eq!(back.symbol_name(f), Some("f"));
        let fx = back.mk_apply(f, x);
        assert_eq!(back.len(), len);
        assert_eq!(back.kind(one), Kind::NUMERAL);
        assert!(back.ty(fx).is_some());
        // and new terms can be made
        let ff = back.mk_apply(f, f);
        assert_eq!(ff.index(), len + 1);
    }

    #[test]
    fn a_damaged_store_is_rejected_or_well_formed() {
        let bytes = written(&sample());
        for len in 0..bytes.len() {
            assert!(TermStore::read_from(&mut Reader::new(&bytes[..len])).is_none());
        }
        for i in 0..bytes.len() {
            for flip in [1u8, 0x80, 0xff] {
                let mut damaged = bytes.clone();
                damaged[i] ^= flip;
                // Whatever is accepted obeys the store's invariants: it can
                // be walked and written without a panic.
                if let Some(s) = TermStore::read_from(&mut Reader::new(&damaged)) {
                    for t in 1..=s.len() {
                        let t = Term::from_index(t).unwrap();
                        for &c in s.children(t) {
                            assert!(c < t);
                        }
                        let _ = (s.kind(t), s.lit(t), s.symbol_name(t), s.ty(t));
                    }
                    written(&s);
                }
            }
        }
    }

    #[test]
    fn a_store_with_a_term_twice_is_rejected() {
        let mut s = TermStore::new();
        let ty = s.mk_type();
        let f = s.mk_symbol(SymbolKind::Const, "f", ty);
        s.mk_apply(f, f);
        s.mk_apply(f, ty);
        let mut bytes = written(&s);
        // make the second application the same as the first: its second
        // child is 4 bytes before its type, at the end of the terms
        let terms_end = 4 + 14 * s.len();
        let child = terms_end - 8;
        bytes[child..child + 4].copy_from_slice(&f.id().to_le_bytes());
        assert!(TermStore::read_from(&mut Reader::new(&bytes)).is_none());
    }
}
