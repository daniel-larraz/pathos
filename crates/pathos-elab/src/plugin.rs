//! The plugin interface (`plugin.h` in Ethos).
//!
//! A plugin is told what the checker reads: bindings, definitions,
//! programs, attributes, echoes, files. Ethos's compiler stages (eoc) are
//! plugins. The hooks are Ethos's and are called at the same points; each
//! one gets the state, which a plugin in Ethos keeps a reference to.
//!
//! Two things differ from the C++, neither visible to the plugins ported so
//! far:
//!
//! - Hooks raised inside the checker (a constructor kind, a program's
//!   definition) are queued there and delivered, in order, before the next
//!   hook raised by the parser and at the end of each command. They return
//!   nothing, so the checker does not wait for them.
//! - While a hook runs, the plugin is not attached to the state: what the
//!   plugin itself does to the state raises no hooks.
//! - Where a C++ plugin aborts the process, a hook here returns an error.
//!   The state keeps it, calls no further hook, and the parser reports it
//!   when the command being read ends.
//!
//! The evaluation hooks are a separate trait, [`pathos_check::EvalPlugin`],
//! because they are called from inside the checker's evaluation; a plugin
//! that evaluates returns one from [`Plugin::evaluator`].

use pathos_check::{Attr, EvalPlugin, PluginEvent};
use pathos_syntax::{Error, Result};
use pathos_term::{LitKind, Term};

use crate::state::State;

/// What [`Plugin::notify_step`] says about a step.
pub struct StepResult {
    /// What the step proves; `None` if the plugin could not tell.
    pub result: Option<Term>,
}

#[allow(unused_variables)]
pub trait Plugin {
    /// Called when the plugin is attached to the state.
    fn initialize(&mut self, st: &mut State) -> Result<()> {
        Ok(())
    }
    /// The `reset` command.
    fn reset(&mut self, st: &mut State) -> Result<()> {
        Ok(())
    }
    /// `assume-push`, and the parser's own scopes.
    fn push_scope(&mut self, st: &mut State) -> Result<()> {
        Ok(())
    }
    /// `step-pop`, and the parser's own scopes.
    fn pop_scope(&mut self, st: &mut State) -> Result<()> {
        Ok(())
    }
    /// Called before a file is read for the first time. Returns true if the
    /// state should not read it.
    fn include_file(
        &mut self,
        st: &mut State,
        path: &str,
        is_signature: bool,
        is_reference: bool,
        reference_nf: Option<Term>,
    ) -> Result<bool> {
        Ok(false)
    }
    /// Called after a file has been read.
    fn finalize_include_file(
        &mut self,
        st: &mut State,
        path: &str,
        is_signature: bool,
        is_reference: bool,
        reference_nf: Option<Term>,
    ) -> Result<()> {
        Ok(())
    }
    /// `declare-consts` gave literals of kind `k` the type `t`.
    fn set_literal_type_rule(&mut self, st: &mut State, k: LitKind, t: Term) -> Result<()> {
        Ok(())
    }
    /// `name` is about to be bound to `e`.
    fn bind(&mut self, st: &mut State, name: &str, e: Term) -> Result<()> {
        Ok(())
    }
    /// The symbol `v` got the constructor attribute `a` with the term `cons`.
    fn mark_constructor_kind(
        &mut self,
        st: &mut State,
        v: Term,
        a: Attr,
        cons: Option<Term>,
    ) -> Result<()> {
        Ok(())
    }
    /// A `program` command declared `v`; `prog` is its `PROGRAM` term, or
    /// none for a forward declaration.
    fn define_program(&mut self, st: &mut State, v: Term, prog: Option<Term>) -> Result<()> {
        Ok(())
    }
    /// A `define` or `define-fun` command bound `name` to `e`.
    fn define(&mut self, st: &mut State, name: &str, e: Term) -> Result<()> {
        Ok(())
    }
    /// The evaluation hooks of this plugin, if it has any.
    fn evaluator(&mut self) -> Option<Box<dyn EvalPlugin>> {
        None
    }
    /// An `assume` or `assume-push` command. The plugin may replace what is
    /// assumed.
    fn notify_assume(
        &mut self,
        st: &mut State,
        name: &str,
        proven: &mut Term,
        is_push: bool,
    ) -> Result<()> {
        Ok(())
    }
    /// A `step` or `step-pop` command. Returns `None` to leave the step to
    /// the checker. `err`, if given, takes the details of a failure.
    #[allow(clippy::too_many_arguments)]
    fn notify_step(
        &mut self,
        st: &mut State,
        name: &str,
        rule: Term,
        proven: Option<Term>,
        premises: &[Term],
        args: &[Term],
        is_pop: bool,
        err: Option<&mut String>,
    ) -> Result<Option<StepResult>> {
        Ok(None)
    }
    /// An `echo` command. Returns false if the message was for the plugin
    /// and should not be printed.
    fn echo(&mut self, st: &mut State, msg: &str) -> Result<bool> {
        Ok(true)
    }
    /// Lines for `--show-config`.
    fn print_config(&self, out: &mut String) {}
    /// Called once, after all input has been read.
    fn finalize(&mut self, st: &mut State) -> Result<()> {
        Ok(())
    }
}

impl State {
    /// Attaches a plugin. It must be attached before any file is read.
    pub fn set_plugin(&mut self, mut plugin: Box<dyn Plugin>) -> Result<()> {
        self.ck.eval_plugin = plugin.evaluator();
        self.ck.plugin_events = Some(Vec::new());
        plugin.initialize(self)?;
        self.plugin = Some(plugin);
        Ok(())
    }

    pub fn has_plugin(&self) -> bool {
        self.plugin.is_some()
    }

    /// Runs `f` on the plugin, if there is one, after delivering the hooks
    /// queued in the checker. An error ends the plugin's part in the run:
    /// it is kept for [`State::take_plugin_error`], and no hook is called
    /// after it.
    pub(crate) fn with_plugin<R>(
        &mut self,
        f: impl FnOnce(&mut dyn Plugin, &mut State) -> Result<R>,
    ) -> Option<R> {
        if self.plugin_error.is_some() {
            return None;
        }
        let mut plugin = self.plugin.take()?;
        let r = self
            .deliver_events(plugin.as_mut())
            .and_then(|()| f(plugin.as_mut(), self));
        self.plugin = Some(plugin);
        match r {
            Ok(r) => Some(r),
            Err(e) => {
                self.plugin_error = Some(e);
                None
            }
        }
    }

    fn deliver_events(&mut self, plugin: &mut dyn Plugin) -> Result<()> {
        loop {
            let events = match &mut self.ck.plugin_events {
                Some(events) if !events.is_empty() => std::mem::take(events),
                _ => return Ok(()),
            };
            for event in events {
                match event {
                    PluginEvent::MarkConstructorKind(v, a, cons) => {
                        plugin.mark_constructor_kind(self, v, a, cons)?;
                    }
                    PluginEvent::DefineProgram(v, prog) => plugin.define_program(self, v, prog)?,
                }
            }
        }
    }

    /// Delivers the hooks queued in the checker.
    pub fn flush_plugin_events(&mut self) {
        self.with_plugin(|_, _| Ok(()));
    }

    /// The error that stopped the plugin, if one did. Ethos aborts inside
    /// the hook; here the command being read ends first.
    pub fn take_plugin_error(&mut self) -> Option<Error> {
        self.plugin_error.take()
    }

    /// Calls the plugin's `finalize`.
    pub fn finalize_plugin(&mut self) -> Result<()> {
        self.with_plugin(|p, st| p.finalize(st));
        self.take_plugin_error().map_or(Ok(()), Err)
    }

    /// An `echo` command: the plugin may take the message for itself. A
    /// plugin that fails on the message has stopped the run in Ethos, so
    /// nothing is printed then.
    pub fn echo(&mut self, msg: &str) {
        let print = self.with_plugin(|p, st| p.echo(st, msg)) != Some(false);
        if print && self.plugin_error.is_none() {
            self.print_line(msg);
        }
    }

    /// A `define` or `define-fun` command has bound `name` to `e`.
    pub fn define(&mut self, name: &str, e: Term) {
        self.with_plugin(|p, st| p.define(st, name, e));
    }

    /// Sets the type rule of a literal kind and tells the plugin.
    pub fn set_literal_type_rule(&mut self, k: LitKind, t: Term, out: Option<&mut String>) -> bool {
        if !self.ck.set_literal_type_rule(k, t, out) {
            return false;
        }
        self.with_plugin(|p, st| p.set_literal_type_rule(st, k, t));
        true
    }
}
