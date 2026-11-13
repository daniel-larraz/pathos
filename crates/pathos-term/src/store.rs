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

use crate::kind::{EvalOp, Kind, LitKind, NodeKind, SymbolKind};
use crate::lit::Lit;

/// A handle to a term in a [`TermStore`].
///
/// Handles are ordered by creation: a term's children always have smaller
/// handles than the term itself.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Term(NonZeroU32);

impl Term {
    /// The handle for a position in the store; `None` for position 0 and
    /// past the 32-bit range.
    #[inline]
    fn from_index(i: usize) -> Option<Term> {
        u32::try_from(i).ok().and_then(NonZeroU32::new).map(Term)
    }

    /// The handle read back from an interning table, which holds only
    /// non-zero positions.
    #[inline]
    fn from_slot(slot: u32) -> Term {
        Term(NonZeroU32::new(slot).unwrap_or(NonZeroU32::MIN))
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
pub struct Args {
    start: u32,
    len: u32,
}

/// What a term is.
#[derive(Copy, Clone, Debug)]
pub enum TermData {
    Type,
    BoolType,
    Any,
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

const FLAG_EVAL: u8 = 1;
const FLAG_NON_GROUND: u8 = 2;

/// An open-addressing table of term handles. The table does not hold keys:
/// the caller hashes a key, and compares it with the term behind each handle
/// the probe meets. Nothing is ever removed.
struct ConsTable {
    /// Term indices; 0 marks an empty slot.
    slots: Vec<u32>,
    len: usize,
    shift: u32,
}

impl ConsTable {
    fn with_bits(bits: u32) -> ConsTable {
        ConsTable {
            slots: vec![0; 1 << bits],
            len: 0,
            shift: 64 - bits,
        }
    }

    #[inline]
    fn start(&self, hash: u64) -> usize {
        (hash >> self.shift) as usize
    }

    #[inline]
    fn needs_growth(&self) -> bool {
        // keep the table at most 70% full
        self.len * 10 >= self.slots.len() * 7
    }

    /// Looks for a handle whose term `is_match`. Returns it, or the empty
    /// slot where it belongs.
    #[inline]
    fn find(&self, hash: u64, mut is_match: impl FnMut(usize) -> bool) -> Result<usize, usize> {
        let mask = self.slots.len() - 1;
        let mut i = self.start(hash);
        loop {
            let slot = self.slots[i];
            if slot == 0 {
                return Err(i);
            }
            if is_match(slot as usize) {
                return Ok(slot as usize);
            }
            i = (i + 1) & mask;
        }
    }

    /// Inserts a handle known not to be in the table.
    fn insert_new(&mut self, hash: u64, index: u32) {
        let mask = self.slots.len() - 1;
        let mut i = self.start(hash);
        while self.slots[i] != 0 {
            i = (i + 1) & mask;
        }
        self.slots[i] = index;
        self.len += 1;
    }

    /// A table twice the size with the same handles, hashed by `hash_of`.
    fn grown(&self, mut hash_of: impl FnMut(usize) -> u64) -> ConsTable {
        let bits = self.slots.len().trailing_zeros() + 1;
        let mut table = ConsTable::with_bits(bits);
        for &slot in &self.slots {
            if slot != 0 {
                table.insert_new(hash_of(slot as usize), slot);
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
struct HashKeys {
    k0: u64,
    k1: u64,
    k2: u64,
}

impl HashKeys {
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
#[inline]
fn tag_of(kind: Kind) -> u32 {
    match kind {
        Kind::Node(n) => n as u32,
        Kind::Eval(op) => 64 + op as u32,
        Kind::Type | Kind::BoolType | Kind::Any | Kind::Symbol(_) | Kind::Lit(_) => u32::MAX,
    }
}

/// A size limit of the store's 32-bit handles and positions.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
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
    ty_type: Term,
    ty_bool: Term,
    any: Term,
}

impl Default for TermStore {
    fn default() -> Self {
        TermStore::new()
    }
}

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
            ty_type: Term(NonZeroU32::MIN),
            ty_bool: Term(NonZeroU32::MIN),
            any: Term(NonZeroU32::MIN),
        };
        s.ty_type = s.push(TermData::Type, 0).unwrap_or(s.ty_type);
        s.ty_bool = s.push(TermData::BoolType, 0).unwrap_or(s.ty_bool);
        s.any = s
            .push(TermData::Any, FLAG_EVAL | FLAG_NON_GROUND)
            .unwrap_or(s.any);
        s
    }

    /// The number of terms made so far.
    pub fn len(&self) -> usize {
        self.nodes.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
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

    /// Makes a new symbol with the given type. Never returns an existing
    /// term.
    pub fn mk_symbol(&mut self, kind: SymbolKind, name: &str, ty: Term) -> Term {
        // there are no more names than terms, so this fits when the term does
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
        let hash = self.lit_hasher.hash_one(&lit);
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
                Some(l) => self.lit_hasher.hash_one(l),
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
            Kind::Symbol(_) | Kind::Lit(_) => {
                panic!("TermStore::mk called with the atomic kind {kind}")
            }
            Kind::Node(_) | Kind::Eval(_) => {}
        }
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
                let range = u32::try_from(self.child_pool.len())
                    .ok()
                    .zip(u32::try_from(children.len()).ok())
                    .filter(|&(start, len)| start.checked_add(len).is_some());
                let Some((start, len)) = range else {
                    self.limit = Some(Limit::Children);
                    return self.any;
                };
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
    pub fn heap_bytes(&self) -> usize {
        use std::mem::size_of;
        self.nodes.capacity() * size_of::<TermData>()
            + self.types.capacity() * size_of::<Option<Term>>()
            + self.flags.capacity()
            + self.child_pool.capacity() * size_of::<Term>()
            + self.table.slots.capacity() * size_of::<u32>()
    }
}

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
}
