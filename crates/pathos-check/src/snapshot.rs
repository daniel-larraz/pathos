//! Saving and restoring what the checker knows, for signature snapshots.
//!
//! An image is read in full, and checked, before any of it replaces the
//! checker's state: [`Checker::read_image`] then [`Checker::install`].

use std::collections::{HashMap, HashSet};

use pathos_term::codec::{Reader, Writer};
use pathos_term::{Kind, LitKind, Term, TermStore};

use crate::attr::{AppInfo, Attr};
use crate::checker::{Checker, Options};

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
pub fn read_term(r: &mut Reader, store: &TermStore) -> Option<Term> {
    store.term_with_id(r.u32()?)
}

/// Reads a term of the store, or none.
pub fn read_opt_term(r: &mut Reader, store: &TermStore) -> Option<Option<Term>> {
    match r.u32()? {
        0 => Some(None),
        id => store.term_with_id(id).map(Some),
    }
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
        let neg_one = read_opt_term(r, &store)?;

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
