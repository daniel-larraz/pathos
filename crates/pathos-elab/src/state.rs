//! The parsing state: symbol tables, scopes, assumptions and included files
//! (the parsing half of Ethos's `State`).

use std::collections::{HashMap, HashSet};

use pathos_check::{Checker, Options};
use pathos_syntax::{Error, Result};
use pathos_term::{EvalOp, Kind, Term};

use crate::path;

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
    }

    pub fn push_scope(&mut self) {
        self.decls_size_ctx.push(self.decls.len());
    }

    /// Unbinds the symbols bound since the matching `push_scope`.
    pub fn pop_scope(&mut self) -> Result<()> {
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
    pub(crate) fn resolve_include(&self, file: &str) -> String {
        let file = path::trim(file);
        let joined = if path::is_absolute(file) {
            file.to_string()
        } else {
            let mut p = path::parent(&self.input_file);
            p.push_str(file);
            p
        };
        path::canonical(&joined)
    }
}
