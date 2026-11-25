//! The checker's state: the term store and what is known about symbols.

use std::collections::{BTreeMap, HashMap, HashSet};

use pathos_term::{Integer, Kind, Lit, LitKind, SymbolKind, Term, TermStore};

use crate::attr::{AppInfo, Attr};
use crate::stats::Stats;

/// The options of Ethos that the checker reads.
#[derive(Clone, Debug)]
pub struct Options {
    /// Print shared subterms once, with `eo::define`.
    pub print_dag: bool,
    /// Lex `let` as the SMT-LIB binder.
    pub parse_let: bool,
    pub stats: bool,
    pub stats_all: bool,
    pub stats_compact: bool,
    /// Keep proof rules in a symbol table of their own.
    pub rule_sym_table: bool,
    /// Require the last step at level zero to prove false.
    pub require_proof_of_false: bool,
    pub normalize_decimal: bool,
    pub normalize_hexadecimal: bool,
    pub normalize_numeral: bool,
    /// In reference files, read a `define-fun` with arguments as the
    /// higher-order equality `(= f (lambda (x) t))` instead of
    /// `(forall (x) (= (f x) t))`.
    pub reference_define_fun_ho: bool,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            print_dag: true,
            parse_let: true,
            stats: false,
            stats_all: false,
            stats_compact: false,
            rule_sym_table: true,
            require_proof_of_false: false,
            normalize_decimal: true,
            normalize_hexadecimal: true,
            normalize_numeral: false,
            reference_define_fun_ho: false,
        }
    }
}

impl Options {
    /// Sets the option named `key`. Returns false for an unknown option.
    pub fn set_option(&mut self, key: &str, val: bool) -> bool {
        match key {
            "parse-let" => self.parse_let = val,
            "print-dag" => self.print_dag = val,
            "stats" => self.stats = val,
            "stats-all" => {
                self.stats = val || self.stats;
                self.stats_all = val;
            }
            "stats-compact" => {
                self.stats = val || self.stats;
                self.stats_compact = val;
            }
            "rule-sym-table" => self.rule_sym_table = val,
            "require-proof-of-false" => self.require_proof_of_false = val,
            "normalize-dec" => self.normalize_decimal = val,
            "normalize-num" => self.normalize_numeral = val,
            "normalize-hex" => self.normalize_hexadecimal = val,
            "reference-define-fun-ho" => self.reference_define_fun_ho = val,
            _ => return false,
        }
        true
    }
}

/// A substitution from parameters to terms.
///
/// Ethos orders these by the address of the parameter. pathos orders them by
/// term handle, which is creation order (design decision 7); the order shows
/// when a context is printed in an error message.
pub type Ctx = BTreeMap<Term, Term>;

/// A plugin hook raised inside the checker, kept for whoever drives the
/// checker to deliver (see `pathos_elab::Plugin`).
#[derive(Copy, Clone, Debug)]
pub enum PluginEvent {
    MarkConstructorKind(Term, Attr, Option<Term>),
    DefineProgram(Term, Option<Term>),
}

/// A plugin's evaluation hooks (`hasEvaluation`, `evaluate` and
/// `evaluateProgram` in Ethos's `plugin.h`). While one of them runs, the
/// checker has no evaluation plugin: an evaluation the hook starts is the
/// checker's own.
pub trait EvalPlugin {
    /// Whether the plugin evaluates the term or program `e`.
    fn has_evaluation(&self, ck: &Checker, e: Term) -> bool;
    /// The value of `e` under the substitution `ctx`.
    fn evaluate(&mut self, ck: &mut Checker, e: Term, ctx: &Ctx) -> Option<Term>;
    /// The result of applying the program `args[0]` to the other arguments,
    /// with `new_ctx` filled as the checker's own matching would fill it;
    /// `None` if the plugin does not evaluate this application.
    fn evaluate_program(
        &mut self,
        ck: &mut Checker,
        args: &[Term],
        new_ctx: &mut Ctx,
    ) -> Option<Term>;
}

/// The term store together with everything the checker knows about the
/// terms in it: attributes, overloads, literal type rules. Its methods build
/// terms ([`Checker::mk_expr`]), type them ([`Checker::get_type`]) and
/// evaluate them ([`Checker::evaluate`]). The three depend on each other:
/// building an application may evaluate a program, and evaluating a list
/// operator reads attributes and types.
pub struct Checker {
    pub store: TermStore,
    pub opts: Options,
    pub(crate) app: HashMap<Term, AppInfo>,
    /// For each name bound to two or more terms, those terms in the order
    /// they were bound.
    pub(crate) overloads: HashMap<String, Vec<Term>>,
    /// The type rule of each literal kind, if declared.
    pub(crate) literal_type_rules: HashMap<LitKind, Term>,
    /// The numbers given out by `eo::hash`.
    pub(crate) hashes: HashMap<Term, u64>,
    pub(crate) hash_counter: u64,
    pub(crate) sorry_rules: HashSet<Term>,
    /// The rules and programs used, for the verdict and `--stats`.
    pub(crate) stats: Stats,
    /// Called with each warning; the binary writes them to stderr.
    warnings: Box<dyn FnMut(&str)>,
    /// The hooks raised since they were last delivered; `None` without a
    /// plugin.
    pub plugin_events: Option<Vec<PluginEvent>>,
    pub eval_plugin: Option<Box<dyn EvalPlugin>>,

    pub(crate) t_true: Term,
    pub(crate) t_false: Term,
    pub(crate) t_self: Term,
    pub(crate) list_type: Term,
    pub(crate) list_nil: Term,
    pub(crate) list_cons: Term,
    pub(crate) proof_type: Term,
    pub(crate) neg_one: Option<Term>,
}

impl Checker {
    pub fn new(opts: Options, warnings: Box<dyn FnMut(&str)>) -> Checker {
        let mut store = TermStore::new();
        let ty = store.mk_type();
        let any = store.mk_any();
        let t_true = store.mk_lit(Lit::Bool(true));
        let t_false = store.mk_lit(Lit::Bool(false));
        let list_type = store.mk_symbol(SymbolKind::Const, "eo::List", ty);
        let list_nil = store.mk_symbol(SymbolKind::Const, "eo::List::nil", list_type);
        let t = store.mk_symbol(SymbolKind::Param, "T", ty);
        let tail = store.mk(Kind::FUNCTION_TYPE, &[list_type, list_type]);
        let cons_type = store.mk(Kind::FUNCTION_TYPE, &[t, tail]);
        let list_cons = store.mk_symbol(SymbolKind::Const, "eo::List::cons", cons_type);
        let t_self = store.mk_symbol(SymbolKind::Param, "eo::self", any);
        let proof_type = store.mk_symbol(SymbolKind::Const, "eo::Proof", ty);
        let stats = Stats::new(opts.stats);
        let mut ck = Checker {
            store,
            opts,
            app: HashMap::new(),
            overloads: HashMap::new(),
            literal_type_rules: HashMap::new(),
            hashes: HashMap::new(),
            hash_counter: 0,
            sorry_rules: HashSet::new(),
            stats,
            warnings,
            plugin_events: None,
            eval_plugin: None,
            t_true,
            t_false,
            t_self,
            list_type,
            list_nil,
            list_cons,
            proof_type,
            neg_one: None,
        };
        ck.mark_constructor_kind(list_cons, Attr::RightAssocNil, Some(list_nil));
        ck
    }

    /// Reports a warning: a line Ethos writes to stderr without stopping.
    pub fn warn(&mut self, msg: &str) {
        (self.warnings)(msg);
    }

    // ---------------------------------------------------------- constants

    pub fn mk_type(&self) -> Term {
        self.store.mk_type()
    }

    pub fn mk_bool_type(&self) -> Term {
        self.store.mk_bool_type()
    }

    pub fn mk_any(&self) -> Term {
        self.store.mk_any()
    }

    pub fn mk_true(&self) -> Term {
        self.t_true
    }

    pub fn mk_false(&self) -> Term {
        self.t_false
    }

    pub fn mk_bool(&self, b: bool) -> Term {
        if b { self.t_true } else { self.t_false }
    }

    /// The parameter `eo::self` of literal type rules.
    pub fn mk_self(&self) -> Term {
        self.t_self
    }

    pub fn mk_list_type(&self) -> Term {
        self.list_type
    }

    pub fn mk_list_nil(&self) -> Term {
        self.list_nil
    }

    pub fn mk_list_cons(&self) -> Term {
        self.list_cons
    }

    /// The type of proof terms.
    pub fn mk_proof_type(&self) -> Term {
        self.proof_type
    }

    // ------------------------------------------------------------ symbols

    pub fn mk_symbol(&mut self, kind: SymbolKind, name: &str, ty: Term) -> Term {
        self.store.mk_symbol(kind, name, ty)
    }

    /// A builtin symbol such as `->` or `eo::add`, whose applications build
    /// terms of the given kind.
    pub fn mk_builtin(&mut self, name: &str, kind: Kind) -> Term {
        let any = self.mk_any();
        let c = self.store.mk_symbol(SymbolKind::BuiltinConst, name, any);
        self.app.entry(c).or_default().kind = Some(kind);
        c
    }

    pub fn mk_numeral(&mut self, i: Integer) -> Term {
        self.store.mk_lit(Lit::Numeral(i))
    }

    // --------------------------------------------------------- attributes

    pub(crate) fn app_info(&self, t: Term) -> Option<&AppInfo> {
        self.app.get(&t)
    }

    /// The constructor attribute of a symbol; `Attr::None` if it has none.
    pub fn attribute_kind(&self, t: Term) -> Attr {
        self.app.get(&t).map_or(Attr::None, |ai| ai.attr)
    }

    /// The term that goes with the symbol's constructor attribute.
    pub fn attribute_term(&self, t: Term) -> Option<Term> {
        self.app.get(&t).and_then(|ai| ai.cons)
    }

    /// Gives a symbol its constructor attribute. A symbol can have only one;
    /// a second call warns and returns false.
    pub fn mark_constructor_kind(&mut self, v: Term, a: Attr, cons: Option<Term>) -> bool {
        let ai = self.app.entry(v).or_default();
        if ai.attr != Attr::None {
            let msg = format!(
                "Cannot set the constructor kind for a term more than once ({} and {})",
                ai.attr, a
            );
            self.warn(&msg);
            return false;
        }
        ai.attr = a;
        ai.cons = cons;
        if let Some(events) = &mut self.plugin_events {
            events.push(PluginEvent::MarkConstructorKind(v, a, cons));
        }
        true
    }

    /// Records that `name` is now also bound to `e`, after `prev`.
    pub fn add_overload(&mut self, name: &str, prev: Term, e: Term) {
        let ai = self.app.entry(e).or_default();
        ai.overloaded = true;
        ai.overload_name = name.to_string();
        let ov = self.overloads.entry(name.to_string()).or_default();
        if ov.is_empty() {
            ov.push(prev);
        }
        ov.push(e);
    }

    /// The terms `name` is bound to, oldest first, if there are several.
    pub fn overloads_of(&self, name: &str) -> &[Term] {
        self.overloads.get(name).map_or(&[], Vec::as_slice)
    }

    /// Undoes the last [`Checker::add_overload`] for `name`. Returns the term
    /// the name is bound to again.
    pub fn pop_overload(&mut self, name: &str) -> Option<Term> {
        let ov = self.overloads.get_mut(name)?;
        ov.pop();
        let back = ov.last().copied();
        if ov.len() <= 1 {
            self.overloads.remove(name);
        }
        back
    }

    /// The cases of a program, as a `PROGRAM` term, if it has been defined.
    pub fn get_program(&self, t: Term) -> Option<Term> {
        match self.app.get(&t) {
            Some(ai) if ai.attr == Attr::Program => ai.cons,
            _ => None,
        }
    }

    /// Defines the cases of a program symbol.
    pub fn define_program(&mut self, v: Term, prog: Option<Term>) {
        if prog.is_some() {
            self.mark_constructor_kind(v, Attr::Program, prog);
        }
        // the plugin is told of forward declarations too
        if let Some(events) = &mut self.plugin_events {
            events.push(PluginEvent::DefineProgram(v, prog));
        }
    }

    pub fn mark_proof_rule_sorry(&mut self, rule: Term) {
        self.sorry_rules.insert(rule);
    }

    pub fn is_proof_rule_sorry(&self, rule: Term) -> bool {
        self.sorry_rules.contains(&rule)
    }

    /// The number `eo::hash` gives a term: terms are numbered from 1 in the
    /// order they are first asked about.
    pub(crate) fn get_hash(&mut self, t: Term) -> u64 {
        if let Some(&h) = self.hashes.get(&t) {
            return h;
        }
        // the counter of a snapshot can be anything: wrap, as a release
        // build always did
        self.hash_counter = self.hash_counter.wrapping_add(1);
        self.hashes.insert(t, self.hash_counter);
        self.hash_counter
    }
}
