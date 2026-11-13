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
//! with the table kept at most 70% full.

use std::collections::HashMap;
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
    #[inline]
    fn from_index(i: usize) -> Term {
        match u32::try_from(i).ok().and_then(NonZeroU32::new) {
            Some(n) => Term(n),
            None => panic!("term store overflow: more than 2^32 - 1 terms"),
        }
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

/// An open-addressing table of term handles, keyed by the structure of the
/// terms they refer to. Nothing is ever removed.
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
}

#[inline]
fn mix(h: u64, x: u64) -> u64 {
    (h.rotate_left(23) ^ x).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

#[inline]
fn hash_node(tag: u32, children: &[Term]) -> u64 {
    let mut h = mix(0x51_7C_C1_B7_27_22_0A_95, u64::from(tag));
    for c in children {
        h = mix(h, u64::from(c.0.get()));
    }
    // a final round so that the top bits depend on the last child
    mix(h, children.len() as u64)
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
    lit_map: HashMap<Lit, Term>,
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
            lit_map: HashMap::new(),
            ty_type: Term(NonZeroU32::MIN),
            ty_bool: Term(NonZeroU32::MIN),
            any: Term(NonZeroU32::MIN),
        };
        s.ty_type = s.push(TermData::Type, 0);
        s.ty_bool = s.push(TermData::BoolType, 0);
        s.any = s.push(TermData::Any, FLAG_EVAL | FLAG_NON_GROUND);
        s
    }

    /// The number of terms made so far.
    pub fn len(&self) -> usize {
        self.nodes.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn push(&mut self, data: TermData, flags: u8) -> Term {
        let t = Term::from_index(self.nodes.len());
        self.nodes.push(data);
        self.types.push(None);
        self.flags.push(flags);
        t
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
        let name_id = u32::try_from(self.names.len()).expect("too many symbols");
        self.names.push(name.into());
        let flags = match kind {
            SymbolKind::ProgramConst => FLAG_EVAL,
            SymbolKind::Param => FLAG_NON_GROUND,
            _ => 0,
        };
        let t = self.push(TermData::Symbol(kind, name_id), flags);
        self.types[t.index()] = Some(ty);
        t
    }

    /// The term for a literal value; equal values give the same term.
    pub fn mk_lit(&mut self, lit: Lit) -> Term {
        if let Some(&t) = self.lit_map.get(&lit) {
            return t;
        }
        let lit_id = u32::try_from(self.lits.len()).expect("too many literals");
        let t = self.push(TermData::Lit(lit.kind(), lit_id), 0);
        self.lits.push(lit.clone());
        self.lit_map.insert(lit, t);
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
        let hash = hash_node(tag, children);
        let mask = self.table.slots.len() - 1;
        let mut i = self.table.start(hash);
        loop {
            let slot = self.table.slots[i];
            if slot == 0 {
                break;
            }
            let cand = slot as usize;
            if tag_of(self.kind_at(cand)) == tag && self.children_at(cand) == children {
                return Term::from_index(cand);
            }
            i = (i + 1) & mask;
        }
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
                let start = u32::try_from(self.child_pool.len()).expect("child pool overflow");
                let len = u32::try_from(children.len()).expect("too many children");
                self.child_pool.extend_from_slice(children);
                let args = Args { start, len };
                match kind {
                    Kind::Node(n) => TermData::Node(n, args),
                    Kind::Eval(op) => TermData::Eval(op, args),
                    _ => unreachable!("atomic kinds returned above"),
                }
            }
        };
        let t = self.push(data, flags);
        self.table.slots[i] = t.0.get();
        self.table.len += 1;
        if self.table.needs_growth() {
            self.grow_table();
        }
        t
    }

    fn grow_table(&mut self) {
        let bits = self.table.slots.len().trailing_zeros() + 1;
        let mut table = ConsTable::with_bits(bits);
        for &slot in &self.table.slots {
            if slot != 0 {
                let i = slot as usize;
                let hash = hash_node(tag_of(self.kind_at(i)), self.children_at(i));
                table.insert_new(hash, slot);
            }
        }
        self.table = table;
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
