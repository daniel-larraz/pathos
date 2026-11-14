//! The parsing state: symbol tables, scopes, assumptions and included files
//! (the parsing half of Ethos's `State`).

use std::collections::{HashMap, HashSet};

use pathos_check::snapshot::{CheckerImage, read_opt_term, read_term, write_opt_term};
use pathos_check::{Checker, Options};
use pathos_syntax::{Error, Result};
use pathos_term::codec::{Reader, Writer};
use pathos_term::{EvalOp, Kind, Term};

use crate::path;
use crate::plugin::Plugin;
use crate::snapshot::{Recording, Snapshot};

/// What a run of the checker knows besides the terms themselves.
pub struct State {
    pub ck: Checker,
    /// The symbols in scope.
    sym_table: HashMap<String, Term>,
    /// The proof rules, when they have a table of their own.
    rule_sym_table: HashMap<String, Term>,
    /// The symbols bound inside a scope, in the order they were bound.
    decls: Vec<String>,
    /// Those of `decls` that were already bound when they were bound again.
    overloaded_decls: Vec<String>,
    /// The length of `decls` at each open scope.
    decls_size_ctx: Vec<usize>,
    /// The assumptions in force.
    assumptions: Vec<Term>,
    /// The length of `assumptions` at each open assumption scope.
    assumptions_size_ctx: Vec<usize>,
    /// The file being read.
    pub(crate) input_file: String,
    includes: HashSet<String>,
    pub(crate) has_reference: bool,
    /// The function that normalizes reference assertions, if given.
    pub(crate) reference_nf: Option<Term>,
    reference_asserts: HashSet<Term>,
    last_step_proves_false_at_level_zero: bool,
    /// Called with each line Ethos writes to stdout while reading.
    out: Box<dyn FnMut(&str)>,
    /// A snapshot to use when the signature it holds is included.
    pub(crate) snapshot: Option<Snapshot>,
    /// What a snapshot of this run needs besides the final state.
    pub(crate) recording: Option<Recording>,
    pub(crate) used_snapshot: bool,
    pub(crate) plugin: Option<Box<dyn Plugin>>,
    pub(crate) plugin_error: Option<Error>,
}

impl State {
    /// `warnings` receives the lines Ethos writes to stderr without
    /// stopping, `out` those it writes to stdout.
    pub fn new(opts: Options, warnings: Box<dyn FnMut(&str)>, out: Box<dyn FnMut(&str)>) -> State {
        let mut st = State {
            ck: Checker::new(opts, warnings),
            sym_table: HashMap::new(),
            rule_sym_table: HashMap::new(),
            decls: Vec::new(),
            overloaded_decls: Vec::new(),
            decls_size_ctx: Vec::new(),
            assumptions: Vec::new(),
            assumptions_size_ctx: Vec::new(),
            input_file: String::new(),
            includes: HashSet::new(),
            has_reference: false,
            reference_nf: None,
            reference_asserts: HashSet::new(),
            last_step_proves_false_at_level_zero: false,
            out,
            snapshot: None,
            recording: None,
            used_snapshot: false,
            plugin: None,
            plugin_error: None,
        };
        st.bind_builtin("->", Kind::FUNCTION_TYPE);
        st.bind_builtin("_", Kind::APPLY);
        for &(op, name) in EvalOp::ALL {
            st.bind_builtin(&format!("eo::{name}"), Kind::Eval(op));
        }
        st.bind_builtin("eo::var", Kind::VARIABLE);
        st.bind_builtin("as", Kind::AS_RETURN);
        st.bind_builtin("eo::as", Kind::AS);
        let consts = [
            ("true", st.ck.mk_true()),
            ("false", st.ck.mk_false()),
            ("eo::List", st.ck.mk_list_type()),
            ("eo::List::nil", st.ck.mk_list_nil()),
            ("eo::List::cons", st.ck.mk_list_cons()),
        ];
        for (name, t) in consts {
            st.bind(name, t);
        }
        st
    }

    fn bind_builtin(&mut self, name: &str, kind: Kind) {
        let c = self.ck.mk_builtin(name, kind);
        self.bind(name, c);
    }

    /// Writes a line to stdout.
    pub fn print_line(&mut self, line: &str) {
        (self.out)(line);
    }

    /// Forgets all symbols and assumptions, as the `reset` command does.
    /// The builtin symbols go too, as in Ethos.
    pub fn reset(&mut self) {
        self.sym_table.clear();
        self.assumptions.clear();
        self.assumptions_size_ctx.clear();
        self.decls.clear();
        self.decls_size_ctx.clear();
        self.last_step_proves_false_at_level_zero = false;
        self.with_plugin(|p, st| p.reset(st));
    }

    pub fn push_scope(&mut self) {
        self.decls_size_ctx.push(self.decls.len());
        self.with_plugin(|p, st| p.push_scope(st));
    }

    /// Unbinds the symbols bound since the matching `push_scope`.
    pub fn pop_scope(&mut self) -> Result<()> {
        self.with_plugin(|p, st| p.pop_scope(st));
        let Some(last_size) = self.decls_size_ctx.pop() else {
            return Err(Error::fatal("State::popScope: empty context"));
        };
        while self.decls.len() > last_size {
            let Some(name) = self.decls.pop() else { break };
            // The symbol was overloaded if the last overloaded declaration
            // has its name: then the previous binding comes back.
            if self.overloaded_decls.last() == Some(&name) {
                self.overloaded_decls.pop();
                if let Some(prev) = self.ck.pop_overload(&name) {
                    self.sym_table.insert(name, prev);
                }
                continue;
            }
            self.sym_table.remove(&name);
        }
        Ok(())
    }

    pub fn push_assumption_scope(&mut self) {
        self.push_scope();
        self.assumptions_size_ctx.push(self.assumptions.len());
    }

    pub fn pop_assumption_scope(&mut self) -> Result<()> {
        if let Some(last_size) = self.assumptions_size_ctx.pop() {
            self.assumptions.truncate(last_size);
        }
        self.pop_scope()
    }

    /// The number of open assumption scopes.
    pub fn assumption_level(&self) -> usize {
        self.assumptions_size_ctx.len()
    }

    /// The first assumption of the innermost assumption scope.
    pub fn first_current_assumption(&self) -> Option<Term> {
        let start = self.assumptions_size_ctx.last().copied().unwrap_or(0);
        self.assumptions.get(start).copied()
    }

    /// The name of the symbol that opened the innermost scope.
    pub(crate) fn innermost_scope_symbol(&self) -> Option<&str> {
        let start = *self.decls_size_ctx.last()?;
        self.decls.get(start).map(String::as_str)
    }

    /// Whether the file has been included.
    pub(crate) fn is_included(&self, canonical: &str) -> bool {
        self.includes.contains(canonical)
    }

    /// Records a file as included. Returns false if it already was.
    pub(crate) fn mark_included(&mut self, canonical: &str) -> bool {
        self.includes.insert(canonical.to_string())
    }

    /// Adds an assumption. Returns false if a reference file was given and
    /// the assumption, at level zero, is not one of its assertions.
    pub fn add_assumption(&mut self, a: Term) -> bool {
        self.assumptions.push(a);
        if self.has_reference && self.assumptions_size_ctx.is_empty() {
            let aa = self.normalize_reference(a);
            return self.reference_asserts.contains(&aa);
        }
        true
    }

    fn normalize_reference(&mut self, a: Term) -> Term {
        match self.reference_nf {
            Some(nf) => self.ck.mk_expr(Kind::APPLY, &[nf, a]),
            None => a,
        }
    }

    /// Adds an assertion of the reference file.
    pub fn add_reference_assert(&mut self, a: Term) {
        let aa = self.normalize_reference(a);
        self.reference_asserts.insert(aa);
    }

    pub fn clear_reference_asserts(&mut self) {
        self.reference_asserts.clear();
    }

    /// Binds a name to a term. A name already bound becomes overloaded: the
    /// new term shadows the old one, and applications pick the one that
    /// type checks. Returns false only for a proof rule whose name is taken.
    pub fn bind(&mut self, name: &str, e: Term) -> bool {
        // the plugin is told whichever table the name goes to
        self.with_plugin(|p, st| p.bind(st, name, e));
        if self.ck.opts.rule_sym_table && self.ck.store.kind(e) == Kind::PROOF_RULE {
            if self.rule_sym_table.contains_key(name) {
                return false;
            }
            self.rule_sym_table.insert(name.to_string(), e);
            return true;
        }
        if let Some(&prev) = self.sym_table.get(name) {
            self.ck.add_overload(name, prev, e);
            if !self.decls_size_ctx.is_empty() {
                self.overloaded_decls.push(name.to_string());
            }
        }
        self.sym_table.insert(name.to_string(), e);
        // symbols bound at the top level are never unbound
        if !self.decls_size_ctx.is_empty() {
            self.decls.push(name.to_string());
        }
        true
    }

    /// The term a name is bound to.
    pub fn get_var(&self, name: &str) -> Option<Term> {
        self.sym_table.get(name).copied()
    }

    /// The proof rule with the given name.
    pub fn get_proof_rule(&self, name: &str) -> Option<Term> {
        if self.ck.opts.rule_sym_table {
            self.rule_sym_table.get(name).copied()
        } else {
            self.sym_table.get(name).copied()
        }
    }

    /// Records what a checked step proved, for `require-proof-of-false`. A
    /// `step-pop` conclusion is bound after its scope is closed, so it is at
    /// level zero when the level is still one.
    pub(crate) fn notify_step_result(&mut self, is_pop: bool, result: Term) {
        self.last_step_proves_false_at_level_zero =
            self.assumption_level() == usize::from(is_pop) && result == self.ck.mk_false();
    }

    pub fn last_step_proves_false_at_level_zero(&self) -> bool {
        self.last_step_proves_false_at_level_zero
    }

    /// The path a file name in an `include` refers to: relative names are
    /// relative to the directory of the file being read.
    pub(crate) fn resolve_include(
        &self,
        file: &str,
    ) -> std::result::Result<String, path::Unresolved> {
        path::resolve(&self.input_file, file)
    }

    /// Writes the symbol tables, the assumptions and the reference state,
    /// after the checker's own state: everything a snapshot restores but
    /// the set of included files.
    pub(crate) fn write_image(&self, w: &mut Writer) {
        self.ck.write_snapshot(w);
        for table in [&self.sym_table, &self.rule_sym_table] {
            let mut entries: Vec<(&String, &Term)> = table.iter().collect();
            entries.sort();
            w.len(entries.len());
            for (name, t) in entries {
                w.str(name);
                w.u32(t.id());
            }
        }
        for names in [&self.decls, &self.overloaded_decls] {
            w.len(names.len());
            for name in names {
                w.str(name);
            }
        }
        for sizes in [&self.decls_size_ctx, &self.assumptions_size_ctx] {
            w.len(sizes.len());
            for &size in sizes {
                w.len(size);
            }
        }
        w.len(self.assumptions.len());
        for t in &self.assumptions {
            w.u32(t.id());
        }
        w.bool(self.has_reference);
        write_opt_term(w, self.reference_nf);
        let mut asserts: Vec<Term> = self.reference_asserts.iter().copied().collect();
        asserts.sort();
        w.len(asserts.len());
        for t in asserts {
            w.u32(t.id());
        }
        w.bool(self.last_step_proves_false_at_level_zero);
    }

    /// Reads what [`State::write_image`] wrote. `None` if the input is not
    /// that.
    pub(crate) fn read_image(&self, r: &mut Reader) -> Option<StateImage> {
        let ck = self.ck.read_image(r)?;
        let store = ck.store();
        let mut tables = [HashMap::new(), HashMap::new()];
        for table in &mut tables {
            let n = r.len(8)?;
            table.reserve(n);
            for _ in 0..n {
                let name = r.str()?.to_string();
                if table.insert(name, read_term(r, store)?).is_some() {
                    return None;
                }
            }
        }
        let [sym_table, rule_sym_table] = tables;
        let mut lists = [Vec::new(), Vec::new()];
        for names in &mut lists {
            let n = r.len(4)?;
            names.reserve(n);
            for _ in 0..n {
                names.push(r.str()?.to_string());
            }
        }
        let [decls, overloaded_decls] = lists;
        let mut contexts = [Vec::new(), Vec::new()];
        for sizes in &mut contexts {
            let n = r.len(4)?;
            sizes.reserve(n);
            for _ in 0..n {
                sizes.push(r.u32()? as usize);
            }
        }
        let [decls_size_ctx, assumptions_size_ctx] = contexts;
        let n = r.len(4)?;
        let mut assumptions = Vec::with_capacity(n);
        for _ in 0..n {
            assumptions.push(read_term(r, store)?);
        }
        // the open scopes are prefixes of the lists they index
        let within = |sizes: &[usize], len: usize| {
            sizes.is_sorted() && sizes.last().is_none_or(|&last| last <= len)
        };
        if !within(&decls_size_ctx, decls.len())
            || !within(&assumptions_size_ctx, assumptions.len())
        {
            return None;
        }
        let has_reference = r.bool()?;
        let reference_nf = read_opt_term(r, store)?;
        let n = r.len(4)?;
        let mut reference_asserts = HashSet::with_capacity(n);
        for _ in 0..n {
            reference_asserts.insert(read_term(r, store)?);
        }
        let last_step_proves_false_at_level_zero = r.bool()?;
        Some(StateImage {
            ck,
            sym_table,
            rule_sym_table,
            decls,
            overloaded_decls,
            decls_size_ctx,
            assumptions,
            assumptions_size_ctx,
            has_reference,
            reference_nf,
            reference_asserts,
            last_step_proves_false_at_level_zero,
        })
    }

    /// Replaces everything [`State::write_image`] writes with the image.
    pub(crate) fn install(&mut self, image: StateImage) {
        self.ck.install(image.ck);
        self.sym_table = image.sym_table;
        self.rule_sym_table = image.rule_sym_table;
        self.decls = image.decls;
        self.overloaded_decls = image.overloaded_decls;
        self.decls_size_ctx = image.decls_size_ctx;
        self.assumptions = image.assumptions;
        self.assumptions_size_ctx = image.assumptions_size_ctx;
        self.has_reference = image.has_reference;
        self.reference_nf = image.reference_nf;
        self.reference_asserts = image.reference_asserts;
        self.last_step_proves_false_at_level_zero = image.last_step_proves_false_at_level_zero;
    }
}

/// The path that `file`, named in an include in the file `includer`,
/// refers to, if it names a file.
pub(crate) fn resolve_include_from(includer: &str, file: &str) -> Option<String> {
    path::resolve(includer, file).ok()
}

/// The state as read from a snapshot.
pub(crate) struct StateImage {
    ck: CheckerImage,
    sym_table: HashMap<String, Term>,
    rule_sym_table: HashMap<String, Term>,
    decls: Vec<String>,
    overloaded_decls: Vec<String>,
    decls_size_ctx: Vec<usize>,
    assumptions: Vec<Term>,
    assumptions_size_ctx: Vec<usize>,
    has_reference: bool,
    reference_nf: Option<Term>,
    reference_asserts: HashSet<Term>,
    last_step_proves_false_at_level_zero: bool,
}
