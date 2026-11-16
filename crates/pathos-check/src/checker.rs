//! The checker's state: the term store and what is known about symbols.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use std::collections::{BTreeMap, HashMap, HashSet};

use pathos_term::{Integer, Kind, Lit, LitKind, SymbolKind, Term, TermStore};

use crate::attr::{AppInfo, Attr};
#[cfg(verus_keep_ghost)]
use crate::matching::{case_ok, ctx_ok, has_patterns, is_program};
use crate::stats::Stats;

/// The options of Ethos that the checker reads.
#[derive(Clone, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
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
    /// In reference files, read `define-fun` and `define-const` as
    /// definitions, not as reference assertions.
    pub reference_define_fun: bool,
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
            reference_define_fun: false,
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
            "reference-define-fun" => self.reference_define_fun = val,
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
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
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

/// Where warnings go. A type of its own because Verus does not accept a
/// boxed closure as a field of a type it looks into; to Verus this is
/// opaque.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub(crate) struct Warnings(Box<dyn FnMut(&str)>);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Warnings {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn emit(&mut self, msg: &str) {
        (self.0)(msg);
    }
}

/// The evaluation plugin, if there is one. Opaque to Verus, like
/// [`Warnings`].
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
pub(crate) struct EvalHooks(pub(crate) Option<Box<dyn EvalPlugin>>);

/// The term store together with everything the checker knows about the
/// terms in it: attributes, overloads, literal type rules. Its methods build
/// terms ([`Checker::mk_expr`]), type them ([`Checker::get_type`]) and
/// evaluate them ([`Checker::evaluate`]). The three depend on each other:
/// building an application may evaluate a program, and evaluating a list
/// operator reads attributes and types.
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
    pub(crate) warnings: Warnings,
    /// Set when the checker met something it cannot go on from: the message
    /// of the error that must end the run. Evaluation stops once it is set,
    /// and the parser reports it at the end of the command.
    pub(crate) fatal: Option<String>,
    /// The hooks raised since they were last delivered; `None` without a
    /// plugin.
    pub plugin_events: Option<Vec<PluginEvent>>,
    pub(crate) eval_plugin: EvalHooks,

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
            warnings: Warnings(warnings),
            fatal: None,
            plugin_events: None,
            eval_plugin: EvalHooks(None),
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

    /// The message of the error that must end the run, if the checker met
    /// one. Whatever the command computed after it cannot be trusted.
    pub fn take_fatal(&mut self) -> Option<String> {
        self.fatal.take()
    }

    /// Sets the plugin whose evaluation hooks the evaluator calls.
    pub fn set_eval_plugin(&mut self, plugin: Option<Box<dyn EvalPlugin>>) {
        self.eval_plugin = EvalHooks(plugin);
    }

    // ---------------------------------------------------------- constants

    pub fn mk_list_nil(&self) -> Term {
        self.list_nil
    }

    // ------------------------------------------------------------ symbols

    /// A builtin symbol such as `->` or `eo::add`, whose applications build
    /// terms of the given kind.
    pub fn mk_builtin(&mut self, name: &str, kind: Kind) -> Term {
        let any = self.mk_any();
        let c = self.store.mk_symbol(SymbolKind::BuiltinConst, name, any);
        self.app.entry(c).or_default().kind = Some(kind);
        c
    }

    // --------------------------------------------------------- attributes

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
}

/// What the evaluator uses, with what Verus proves of it: see
/// `docs/verus-spike.md`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Checker {
    /// Reports a warning: a line Ethos writes to stderr without stopping.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).unchanged(old(self)),
    ))]
    pub fn warn(&mut self, msg: &str) {
        self.warnings.emit(msg);
    }

    /// The term of a compound kind with the given children
    /// ([`TermStore::mk`]), keeping the checker's invariant.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(children@), !(k is Symbol) && !(k is Lit),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub(crate) fn mk_term(&mut self, k: Kind, children: &[Term]) -> Term {
        proof_decl! { let ghost before = *self; }
        let t = self.store.mk(k, children);
        proof! { self.lemma_stored(&before); }
        t
    }

    /// The application of `f` to `a` ([`TermStore::mk_apply`]), keeping the
    /// checker's invariant.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(f), old(self).has(a),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub(crate) fn mk_app(&mut self, f: Term, a: Term) -> Term {
        proof_decl! { let ghost before = *self; }
        let t = self.store.mk_apply(f, a);
        proof! { self.lemma_stored(&before); }
        t
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(ty),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_symbol(&mut self, kind: SymbolKind, name: &str, ty: Term) -> Term {
        proof_decl! { let ghost before = *self; }
        let t = self.store.mk_symbol(kind, name, ty);
        proof! { self.lemma_stored(&before); }
        t
    }

    /// The term that goes with the symbol's constructor attribute.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires self.wf(),
        ensures r matches Some(c) ==> self.has(c),
    ))]
    pub fn attribute_term(&self, t: Term) -> Option<Term> {
        match self.app_info(t) {
            Some(ai) => ai.cons,
            None => None,
        }
    }

    /// The terms the name is bound to, if it is overloaded; none otherwise.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires self.wf(),
        ensures self.has_all(r@),
    ))]
    pub(crate) fn overloads_of(&self, name: &String) -> Vec<Term> {
        proof! {
            axiom_names_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        match self.overloads.get(name) {
            Some(ov) => crate::eval::copy_of(ov.as_slice()),
            None => Vec::new(),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_bool_type(&self) -> Term {
        self.store.mk_bool_type()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_any(&self) -> Term {
        self.store.mk_any()
    }

    /// The parameter `eo::self` of literal type rules.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_self(&self) -> Term {
        self.t_self
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_list_type(&self) -> Term {
        self.list_type
    }

    /// The type of proof terms.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_proof_type(&self) -> Term {
        self.proof_type
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_type(&self) -> Term {
        self.store.mk_type()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_true(&self) -> Term {
        self.t_true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_false(&self) -> Term {
        self.t_false
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r), self.is_bool(r, b),))]
    pub fn mk_bool(&self, b: bool) -> Term {
        if b { self.t_true } else { self.t_false }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures self.has(r),))]
    pub fn mk_list_cons(&self) -> Term {
        self.list_cons
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(),
        ensures final(self).wf(), final(self).has(r), final(self).keeps(old(self)),
    ))]
    pub fn mk_numeral(&mut self, i: Integer) -> Term {
        proof_decl! { let ghost before = *self; }
        let t = self.store.mk_lit(Lit::Numeral(i));
        proof! { self.lemma_stored(&before); }
        t
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures r matches Some(ai) ==> self.knows(t, *ai),
    ))]
    pub(crate) fn app_info(&self, t: Term) -> Option<&AppInfo> {
        proof! {
            axiom_terms_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        self.app.get(&t)
    }

    /// The constructor attribute of a symbol; `Attr::None` if it has none.
    pub fn attribute_kind(&self, t: Term) -> Attr {
        match self.app_info(t) {
            Some(ai) => ai.attr,
            None => Attr::None,
        }
    }

    /// The cases of a program, as a `PROGRAM` term, if it has been defined.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires self.wf(),
        ensures r matches Some(p) ==> self.has_program(p),
    ))]
    pub fn get_program(&self, t: Term) -> Option<Term> {
        match self.app_info(t) {
            Some(ai) if ai.attr == Attr::Program => ai.cons,
            _ => None,
        }
    }

    /// The number `eo::hash` gives a term: terms are numbered from 1 in the
    /// order they are first asked about.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).unchanged(old(self)),
    ))]
    pub(crate) fn get_hash(&mut self, t: Term) -> u64 {
        proof! {
            axiom_terms_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
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

#[cfg(verus_keep_ghost)]
verus! {

/// Every term of the list is a term of the store.
pub open spec fn all_has(s: &TermStore, ts: Seq<Term>) -> bool {
    forall|i: int| 0 <= i < ts.len() ==> s.has(#[trigger] ts[i])
}

/// The store has the terms of the old one, with their kinds and children.
pub open spec fn keeps(new: &TermStore, old: &TermStore) -> bool {
    forall|t: Term| #[trigger] old.has(t) ==> new.has(t)
        && new.kind_of(t.idx()) == old.kind_of(t.idx())
        && new.kids(t.idx()) == old.kids(t.idx())
}

/// What is known of a symbol refers to the store: the term that goes with
/// its attribute is a term of the store, and that of a program is a list
/// of cases.
pub open spec fn app_ok(s: &TermStore, ai: AppInfo) -> bool {
    &&& ai.cons matches Some(c) ==> s.has(c)
        && (ai.attr == Attr::Program ==> is_program(s, c) && has_patterns(s, c))
    // a builtin stands for a compound kind
    &&& ai.kind matches Some(k) ==> k is Node || k is Eval
}

impl Checker {
    /// The invariant of the checker that the evaluator relies on and
    /// keeps. The rest of the checker, which Verus does not look at, is
    /// trusted to keep it.
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.store.wf()
        &&& self.store.has(self.t_true) && self.store.has(self.t_false) && self.store.has(self.t_self)
        // `true` and `false` are the Boolean literals
        &&& self.store.is_lit(self.t_true, Lit::Bool(true)) && self.store.is_lit(self.t_false, Lit::Bool(false))
        &&& self.store.has(self.list_type) && self.store.has(self.list_nil) && self.store.has(self.list_cons)
        &&& self.store.has(self.proof_type)
        &&& self.neg_one matches Some(t) ==> self.store.has(t)
        &&& forall|t: Term| #[trigger] self.app@.contains_key(t) ==> app_ok(&self.store, self.app@[t])
        // the terms a name is bound to are terms of the store
        &&& forall|name: String| #[trigger] self.overloads@.contains_key(name)
            ==> all_has(&self.store, self.overloads@[name]@)
        // the type of a kind of literal is a term of the store
        &&& forall|k: LitKind| #[trigger] self.literal_type_rules@.contains_key(k)
            ==> self.store.has(self.literal_type_rules@[k])
    }

    /// The attributes and the builtin terms are those of `old`.
    pub open(crate) spec fn same_tables(&self, old: &Checker) -> bool {
        &&& self.app == old.app
        &&& self.overloads == old.overloads
        &&& self.literal_type_rules == old.literal_type_rules
        &&& self.t_true == old.t_true && self.t_false == old.t_false && self.t_self == old.t_self
        &&& self.list_type == old.list_type && self.list_nil == old.list_nil && self.list_cons == old.list_cons
        &&& self.proof_type == old.proof_type
        &&& self.neg_one == old.neg_one
    }

    /// The term is a term of the checker's store.
    pub open(crate) spec fn has(&self, t: Term) -> bool {
        self.store.has(t)
    }

    /// Every term of the list is a term of the store.
    pub open(crate) spec fn has_all(&self, ts: Seq<Term>) -> bool {
        all_has(&self.store, ts)
    }

    /// The substitution is between terms of the store.
    pub open(crate) spec fn binds(&self, ctx: Map<Term, Term>) -> bool {
        ctx_ok(&self.store, ctx)
    }

    /// The rule, the conclusion, the premises, the arguments and the
    /// assumption of the step are terms of the store.
    pub open(crate) spec fn has_step(&self, step: crate::step::Step) -> bool {
        &&& self.store.has(step.rule)
        &&& step.proven matches Some(t) ==> self.store.has(t)
        &&& all_has(&self.store, step.premises@)
        &&& all_has(&self.store, step.args@)
        &&& step.assumption matches Some(t) ==> self.store.has(t)
    }

    /// The term is the Boolean literal `b`.
    pub open(crate) spec fn is_bool(&self, t: Term, b: bool) -> bool {
        self.store.is_lit(t, Lit::Bool(b))
    }

    /// Each of the terms has two children or more.
    pub open(crate) spec fn has_pairs(&self, ts: Seq<Term>) -> bool {
        forall|j: int| 0 <= j < ts.len() ==> self.store.kids((#[trigger] ts[j]).idx()).len() >= 2
    }

    /// The term is a term of the store with the shape of a program.
    pub open(crate) spec fn has_program(&self, p: Term) -> bool {
        self.store.has(p) && is_program(&self.store, p) && has_patterns(&self.store, p)
    }

    /// This is what the checker knows of the symbol.
    pub open(crate) spec fn knows(&self, t: Term, ai: AppInfo) -> bool {
        self.app@.contains_key(t) && ai == self.app@[t]
    }

    /// The store has the terms of `old`'s, as they were.
    pub open(crate) spec fn keeps(&self, old: &Checker) -> bool {
        keeps(&self.store, &old.store)
    }

    /// The store, the attributes and the builtin terms are those of `old`.
    pub open(crate) spec fn unchanged(&self, old: &Checker) -> bool {
        self.store == old.store && self.same_tables(old)
    }

    /// After terms were added to the store, the invariant holds again.
    pub(crate) proof fn lemma_stored(&self, old: &Checker)
        requires old.wf(), self.store.wf(), self.store.extends(&old.store), self.same_tables(old),
        ensures self.wf(), self.keeps(old),
    {
        self.store.lemma_extends(&old.store);
        self.store.lemma_lit_kept(&old.store, self.t_true, Lit::Bool(true));
        self.store.lemma_lit_kept(&old.store, self.t_false, Lit::Bool(false));
        assert forall|t: Term| #[trigger] self.app@.contains_key(t) implies app_ok(&self.store, self.app@[t]) by {
            let ai = self.app@[t];
            assert(app_ok(&old.store, ai));
            if ai.cons is Some && ai.attr == Attr::Program {
                let c = ai.cons->0;
                old.store.lemma_children(c);
                assert forall|i: int| 0 <= i < self.store.kids(c.idx()).len() implies
                    self.store.kids((#[trigger] self.store.kids(c.idx())[i]).idx()).len() >= 2 by {
                    assert(old.store.has(old.store.kids(c.idx())[i]));
                }
                assert forall|i: int| 0 <= i < self.store.kids(c.idx()).len() implies
                    case_ok(&self.store, #[trigger] self.store.kids(c.idx())[i]) by {
                    let case = old.store.kids(c.idx())[i];
                    assert(old.store.has(case));
                    assert(case_ok(&old.store, case));
                    old.store.lemma_children(case);
                    assert(old.store.has(old.store.kids(case.idx())[0]));
                }
            }
        }
    }
}

/// Assumed: the `Hash` and `Eq` of strings agree, which is what the table
/// of overloaded names needs to behave as a map.
#[verifier::external_body]
pub proof fn axiom_names_are_keys()
    ensures vstd::std_specs::hash::obeys_key_model::<String>(),
{
}

/// Assumed: the derived `Hash` and `Eq` of term handles agree, which is
/// what a `HashMap` keyed by them needs to behave as a map.
#[verifier::external_body]
pub proof fn axiom_terms_are_keys()
    ensures vstd::std_specs::hash::obeys_key_model::<Term>(),
{
}

} // verus!
