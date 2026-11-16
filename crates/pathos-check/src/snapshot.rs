//! Saving and restoring what the checker knows, for signature snapshots.
//!
//! An image is read in full, and checked, before any of it replaces the
//! checker's state: [`Checker::read_image`] then [`Checker::install`].

use std::collections::{HashMap, HashSet};

use pathos_term::codec::{Reader, Writer};
use pathos_term::{Integer, Kind, Lit, LitKind, Term, TermStore};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::attr::{AppInfo, Attr};
use crate::checker::{Checker, Options};
use crate::matching;

impl Options {
    /// The options that decide what a signature loads as, one byte each. A
    /// snapshot is only used under the options it was written with. The
    /// statistics options and `require-proof-of-false` are not here: they
    /// only change what is printed at the end.
    pub fn snapshot_key(&self) -> Vec<u8> {
        [
            self.print_dag,
            self.parse_let,
            self.rule_sym_table,
            self.normalize_decimal,
            self.normalize_hexadecimal,
            self.normalize_numeral,
            self.reference_define_fun,
        ]
        .map(u8::from)
        .to_vec()
    }
}

/// Writes a term, or 0 for none.
pub fn write_opt_term(w: &mut Writer, t: Option<Term>) {
    w.u32(t.map_or(0, Term::id));
}

/// Reads a term of the store.
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(res =>
    requires store.wf(),
    ensures res matches Some(t) ==> store.has(t),
))]
pub fn read_term(r: &mut Reader, store: &TermStore) -> Option<Term> {
    store.term_with_id(r.u32()?)
}

/// Reads a term of the store, or none.
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(res =>
    requires store.wf(),
    ensures res matches Some(Some(t)) ==> store.has(t),
))]
pub fn read_opt_term(r: &mut Reader, store: &TermStore) -> Option<Option<Term>> {
    let id = r.u32()?;
    if id == 0 {
        return Some(None);
    }
    Some(Some(store.term_with_id(id)?))
}

/// Whether the terms numbered `1..=last` are the same in the two stores:
/// of the same kind, with the same name or value, and with the same
/// children. Their cached types are not compared.
fn same_first_terms(a: &TermStore, b: &TermStore, last: u32) -> bool {
    (1..=last).all(|id| {
        let (Some(ta), Some(tb)) = (a.term_with_id(id), b.term_with_id(id)) else {
            return false;
        };
        a.kind(ta) == b.kind(tb)
            && a.children(ta) == b.children(tb)
            && a.lit(ta) == b.lit(tb)
            && a.symbol_name(ta) == b.symbol_name(tb)
    })
}

/// The entries of a map in the order of their keys, so that the same state
/// is always written as the same bytes.
pub fn sorted<K: Ord + Copy, V>(map: &HashMap<K, V>) -> Vec<(K, &V)> {
    let mut entries: Vec<(K, &V)> = map.iter().map(|(&k, v)| (k, v)).collect();
    entries.sort_by_key(|&(k, _)| k);
    entries
}

/// The checker's state as read from a snapshot.
pub struct CheckerImage {
    store: TermStore,
    app: HashMap<Term, AppInfo>,
    overloads: HashMap<String, Vec<Term>>,
    literal_type_rules: HashMap<LitKind, Term>,
    hashes: HashMap<Term, u64>,
    hash_counter: u64,
    sorry_rules: HashSet<Term>,
    rule_counts: Vec<(Term, u64)>,
    program_counts: Vec<(Term, u64)>,
    neg_one: Option<Term>,
}

impl CheckerImage {
    pub fn store(&self) -> &TermStore {
        &self.store
    }
}

const ATTRS: &[Attr] = &[
    Attr::None,
    Attr::Implicit,
    Attr::Type,
    Attr::IsEq,
    Attr::Sorry,
    Attr::List,
    Attr::Program,
    Attr::Binder,
    Attr::LetBinder,
    Attr::Opaque,
    Attr::Syntax,
    Attr::Restrict,
    Attr::ProofRule,
    Attr::RightAssoc,
    Attr::LeftAssoc,
    Attr::RightAssocNil,
    Attr::LeftAssocNil,
    Attr::RightAssocNsNil,
    Attr::LeftAssocNsNil,
    Attr::Chainable,
    Attr::Pairwise,
    Attr::ArgList,
    Attr::Amb,
    Attr::Datatype,
    Attr::DatatypeConstructor,
    Attr::AmbDatatypeConstructor,
];

impl Checker {
    /// Writes the term store and everything known about its terms.
    pub fn write_snapshot(&self, w: &mut Writer) {
        self.store.write_to(w);
        let fixed = [
            self.t_true,
            self.t_false,
            self.t_self,
            self.list_type,
            self.list_nil,
            self.list_cons,
            self.proof_type,
        ];
        for t in fixed {
            w.u32(t.id());
        }
        write_opt_term(w, self.neg_one);

        w.len(self.app.len());
        for (t, ai) in sorted(&self.app) {
            w.u32(t.id());
            w.u8(ai.attr as u8);
            write_opt_term(w, ai.cons);
            match ai.kind {
                Some(k) => {
                    let (group, sub) = k.code();
                    w.u8(group + 1);
                    w.u8(sub);
                }
                None => {
                    w.u8(0);
                    w.u8(0);
                }
            }
            w.bool(ai.overloaded);
            w.str(&ai.overload_name);
        }

        let mut names: Vec<&String> = self.overloads.keys().collect();
        names.sort();
        w.len(names.len());
        for name in names {
            w.str(name);
            let terms = &self.overloads[name];
            w.len(terms.len());
            for t in terms {
                w.u32(t.id());
            }
        }

        let mut rules: Vec<(u8, Term)> = (self.literal_type_rules.iter())
            .map(|(&k, &t)| (k as u8, t))
            .collect();
        rules.sort();
        w.len(rules.len());
        for (k, t) in rules {
            w.u8(k);
            w.u32(t.id());
        }

        w.u64(self.hash_counter);
        w.len(self.hashes.len());
        for (t, h) in sorted(&self.hashes) {
            w.u32(t.id());
            w.u64(*h);
        }

        let mut sorry: Vec<Term> = self.sorry_rules.iter().copied().collect();
        sorry.sort();
        w.len(sorry.len());
        for t in sorry {
            w.u32(t.id());
        }

        for counts in [self.stats.rule_counts(), self.stats.program_counts()] {
            w.len(counts.len());
            for (t, n) in counts {
                w.u32(t.id());
                w.u64(n);
            }
        }
    }

    /// Reads what [`Checker::write_snapshot`] wrote. `None` if the input is
    /// not that, or was written by a checker whose builtin terms are not
    /// this one's.
    pub fn read_image(&self, r: &mut Reader) -> Option<CheckerImage> {
        let store = TermStore::read_from(r)?;
        let fixed = [
            self.t_true,
            self.t_false,
            self.t_self,
            self.list_type,
            self.list_nil,
            self.list_cons,
            self.proof_type,
        ];
        for t in fixed {
            if r.u32()? != t.id() {
                return None;
            }
        }
        // The checker keeps handles to these terms, so the store read must
        // have them: the same terms, not only terms with the same numbers.
        let last = fixed.iter().map(|t| t.id()).max().unwrap_or(0);
        if !same_first_terms(&self.store, &store, last) {
            return None;
        }
        let neg_one = read_opt_term(r, &store)?;
        // the numeral kept for the answer of `eo::list_find` when the
        // element is not there: -1, as the checker makes it
        if let Some(t) = neg_one {
            match store.lit(t) {
                Some(Lit::Numeral(i)) if *i == Integer::one().neg() => {}
                _ => return None,
            }
        }

        let n = r.len(15)?;
        let mut app = HashMap::with_capacity(n);
        for _ in 0..n {
            let t = read_term(r, &store)?;
            let attr = *ATTRS.get(usize::from(r.u8()?))?;
            let cons = read_opt_term(r, &store)?;
            let kind = match (r.u8()?, r.u8()?) {
                (0, 0) => None,
                (0, _) => return None,
                (group, sub) => Some(Kind::from_code(group - 1, sub)?),
            };
            // a builtin stands for a compound kind: one that `mk_expr` can
            // build a term of
            if kind.is_some_and(|k| !matches!(k, Kind::Node(_) | Kind::Eval(_))) {
                return None;
            }
            // a program is a list of cases, as the parser builds them
            if attr == Attr::Program && cons.is_some_and(|p| !matching::is_program_term(&store, p))
            {
                return None;
            }
            let overloaded = r.bool()?;
            let overload_name = r.str()?.to_string();
            let ai = AppInfo {
                attr,
                cons,
                kind,
                overloaded,
                overload_name,
            };
            if app.insert(t, ai).is_some() {
                return None;
            }
        }

        let n = r.len(8)?;
        let mut overloads = HashMap::with_capacity(n);
        for _ in 0..n {
            let name = r.str()?.to_string();
            let count = r.len(4)?;
            let mut terms = Vec::with_capacity(count);
            for _ in 0..count {
                terms.push(read_term(r, &store)?);
            }
            // a name is listed only while it is bound to two terms or more
            if terms.len() < 2 || overloads.insert(name, terms).is_some() {
                return None;
            }
        }

        let n = r.len(5)?;
        let mut literal_type_rules = HashMap::with_capacity(n);
        for _ in 0..n {
            let kind = *LitKind::ALL.get(usize::from(r.u8()?))?;
            if literal_type_rules
                .insert(kind, read_term(r, &store)?)
                .is_some()
            {
                return None;
            }
        }

        let hash_counter = r.u64()?;
        let n = r.len(12)?;
        let mut hashes = HashMap::with_capacity(n);
        for _ in 0..n {
            let t = read_term(r, &store)?;
            let h = r.u64()?;
            if h == 0 || h > hash_counter || hashes.insert(t, h).is_some() {
                return None;
            }
        }

        let n = r.len(4)?;
        let mut sorry_rules = HashSet::with_capacity(n);
        for _ in 0..n {
            sorry_rules.insert(read_term(r, &store)?);
        }

        let mut counts = [Vec::new(), Vec::new()];
        for list in &mut counts {
            let n = r.len(12)?;
            list.reserve(n);
            for _ in 0..n {
                list.push((read_term(r, &store)?, r.u64()?));
            }
        }
        let [rule_counts, program_counts] = counts;
        Some(CheckerImage {
            store,
            app,
            overloads,
            literal_type_rules,
            hashes,
            hash_counter,
            sorry_rules,
            rule_counts,
            program_counts,
            neg_one,
        })
    }

    /// Replaces the checker's state with the image.
    pub fn install(&mut self, image: CheckerImage) {
        self.store = image.store;
        self.app = image.app;
        self.overloads = image.overloads;
        self.literal_type_rules = image.literal_type_rules;
        self.hashes = image.hashes;
        self.hash_counter = image.hash_counter;
        self.sorry_rules = image.sorry_rules;
        self.neg_one = image.neg_one;
        (self.stats).set_counts(image.rule_counts, image.program_counts);
    }
}

#[cfg(test)]
mod tests {
    use pathos_term::SymbolKind;

    use super::*;

    fn checker() -> Checker {
        Checker::new(Options::default(), Box::new(|_| {}))
    }

    /// Whether a new checker reads the snapshot of `ck`.
    fn reads(ck: &Checker) -> bool {
        let mut w = Writer::new();
        ck.write_snapshot(&mut w);
        checker().read_image(&mut Reader::new(&w.bytes)).is_some()
    }

    #[test]
    fn a_snapshot_reads_back() {
        let mut ck = checker();
        let ty = ck.store.mk_type();
        let f = ck.store.mk_symbol(SymbolKind::Const, "f", ty);
        ck.app.entry(f).or_default().kind = Some(Kind::FUNCTION_TYPE);
        assert!(reads(&ck));
    }

    /// A builtin's kind is passed to `TermStore::mk`, which takes compound
    /// kinds only.
    #[test]
    fn a_builtin_of_an_atomic_kind_is_rejected() {
        for kind in [Kind::CONST, Kind::NUMERAL, Kind::Type] {
            let mut ck = checker();
            let ty = ck.store.mk_type();
            let f = ck.store.mk_symbol(SymbolKind::Const, "f", ty);
            ck.app.entry(f).or_default().kind = Some(kind);
            assert!(!reads(&ck), "{kind}");
        }
    }

    /// Matching takes a program's cases apart as pairs of an application
    /// and a body.
    #[test]
    fn a_program_that_is_not_a_list_of_cases_is_rejected() {
        let program = |shape: u8| {
            let mut ck = checker();
            let ty = ck.store.mk_type();
            let p = ck.store.mk_symbol(SymbolKind::ProgramConst, "p", ty);
            let x = ck.store.mk_symbol(SymbolKind::Param, "x", ty);
            let pattern = ck.store.mk(Kind::APPLY, &[p, x]);
            let case = match shape {
                // as the parser builds it
                0 => ck.store.mk(Kind::TUPLE, &[pattern, x]),
                // a case that is not a pair
                1 => ck.store.mk(Kind::TUPLE, &[pattern]),
                2 => x,
                // a pattern without a head
                _ => ck.store.mk(Kind::TUPLE, &[x, x]),
            };
            let prog = ck.store.mk(Kind::PROGRAM, &[case]);
            ck.define_program(p, Some(prog));
            reads(&ck)
        };
        assert!(program(0));
        assert!(!program(1));
        assert!(!program(2));
        assert!(!program(3));
    }

    /// The checker keeps handles to its builtin terms; a snapshot whose
    /// store does not have them would leave those handles pointing nowhere.
    #[test]
    fn a_store_without_the_builtin_terms_is_rejected() {
        let ck = checker();
        let mut w = Writer::new();
        // an empty store, and then what a checker without symbols writes
        TermStore::new().write_to(&mut w);
        let fixed = [
            ck.t_true,
            ck.t_false,
            ck.t_self,
            ck.list_type,
            ck.list_nil,
            ck.list_cons,
            ck.proof_type,
        ];
        for t in fixed {
            w.u32(t.id());
        }
        write_opt_term(&mut w, None);
        w.len(0); // symbols
        w.len(0); // overloads
        w.len(0); // literal type rules
        w.u64(0); // hash counter
        w.len(0); // hashes
        w.len(0); // sorry rules
        w.len(0); // rule counts
        w.len(0); // program counts
        let mut r = Reader::new(&w.bytes);
        assert!(ck.read_image(&mut r).is_none());
    }

    /// The same numbers are not enough: they must be the same terms.
    #[test]
    fn a_store_with_other_terms_in_place_of_the_builtin_ones_is_rejected() {
        let mut ck = checker();
        assert!(reads(&ck));
        // a store as large as the checker's, of other terms
        let mut other = TermStore::new();
        let ty = other.mk_type();
        while other.len() < ck.store.len() {
            other.mk_symbol(SymbolKind::Const, "c", ty);
        }
        ck.store = other;
        assert!(!reads(&ck));
    }

    /// `eo::list_find` answers with the numeral the checker keeps for "not
    /// found"; a snapshot with another term there is not read.
    #[test]
    fn a_kept_numeral_that_is_not_minus_one_is_rejected() {
        let numeral = |ck: &mut Checker, n: &str| {
            let i = Integer::parse(n, 10).unwrap();
            ck.store.mk_lit(Lit::Numeral(i))
        };
        // none kept, and the one the checker makes
        let mut ck = checker();
        assert!(reads(&ck));
        ck.neg_one = Some(numeral(&mut ck, "-1"));
        assert!(reads(&ck));
        // another numeral, a literal of another kind, a term that is none
        for forged in ["5", "1", "0"] {
            let mut ck = checker();
            ck.neg_one = Some(numeral(&mut ck, forged));
            assert!(!reads(&ck), "{forged}");
        }
        let mut ck = checker();
        ck.neg_one = Some(ck.store.mk_lit(Lit::Bool(true)));
        assert!(!reads(&ck));
        let mut ck = checker();
        ck.neg_one = Some(ck.store.mk_type());
        assert!(!reads(&ck));
    }

    /// The counters of a snapshot can be anything; none of them overflows.
    #[test]
    fn counters_at_their_maximum_wrap() {
        let mut ck = checker();
        let ty = ck.store.mk_type();
        let rule = ck.store.mk_symbol(SymbolKind::ProofRule, "r", ty);
        let prog = ck.store.mk_symbol(SymbolKind::ProgramConst, "p", ty);
        ck.hash_counter = u64::MAX;
        assert_eq!(ck.get_hash(rule), 0);
        ck.count_programs();
        (ck.stats).set_counts(vec![(rule, u64::MAX)], vec![(prog, u64::MAX)]);
        ck.step_begins(rule);
        ck.step_ends(rule);
        ck.stats.count_program(prog);
        assert_eq!(ck.stats.rule_counts(), vec![(rule, 0)]);
        assert_eq!(ck.stats.program_counts(), vec![(prog, 0)]);
    }
}
