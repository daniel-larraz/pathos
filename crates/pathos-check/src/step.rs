//! Checking proof steps (`State::notifyStep` in Ethos's `state.cpp`).

use std::fmt::Write;

use pathos_term::{Kind, Term};

use crate::attr::Attr;
use crate::checker::Checker;

/// A `step` or `step-pop` command, as parsed.
pub struct Step<'a> {
    pub rule: Term,
    /// The conclusion given in the command, if any.
    pub proven: Option<Term>,
    pub premises: &'a [Term],
    pub args: &'a [Term],
    pub is_pop: bool,
    /// For `step-pop`: the first assumption of the scope being closed.
    pub assumption: Option<Term>,
}

impl Checker {
    /// Computes what a step proves: applies the rule's program to the
    /// arguments, the conclusion (for `:conclusion-explicit` rules), the
    /// assumption (for `:assumption` rules) and the premises.
    ///
    /// Returns `None` if the step does not check. With `err`, the reason is
    /// appended to it. The result is not necessarily of type Bool; the
    /// caller checks that.
    pub fn check_step(&mut self, step: &Step<'_>, mut err: Option<&mut String>) -> Option<Term> {
        macro_rules! fail {
            ($($arg:tt)*) => {{
                if let Some(e) = err.as_deref_mut() {
                    let _ = writeln!(e, $($arg)*);
                }
                return None;
            }};
        }
        let tuple = match self.app_info(step.rule) {
            Some(ai) if ai.attr == Attr::ProofRule => ai.cons,
            _ => None,
        };
        let Some(tuple) = tuple.filter(|&t| self.store.num_children(t) == 4) else {
            fail!("Provided :rule is not recognized as a proof rule");
        };
        let t = self.store.children(tuple).to_vec();
        // The program of the rule or, for a rule without arguments and
        // premises, its conclusion.
        let mut children = vec![t[3]];
        children.extend_from_slice(step.args);
        let pl_cons = (t[0] != self.mk_any()).then_some(t[0]);
        let is_assume = t[1] == self.mk_true();
        let is_conc_explicit = t[2] == self.mk_true();
        if is_conc_explicit {
            let Some(proven) = step.proven else {
                fail!("Rules with :conclusion-explicit require a provided conclusion.");
            };
            children.push(proven);
        }
        if step.is_pop == is_assume {
            if step.is_pop {
                // The scope may hold more assumptions, from assume commands
                // inside it; the first one is that of the assume-push.
                let Some(a) = step.assumption else {
                    fail!("step-pop can only be used on rules with :assumption");
                };
                children.push(a);
            }
        } else if step.is_pop {
            fail!("step-pop can only be used on rules with :assumption");
        } else {
            fail!("step cannot be used on rules with :assumption");
        }
        if let Some(pl_cons) = pl_cons {
            // The premises (eo::pf F1) ... (eo::pf Fn) are collected into
            // (eo::pf (and F1 ... Fn)), for the :premise-list operator `and`.
            let mut achildren = vec![pl_cons];
            for &e in step.premises {
                if self.store.kind(e) != Kind::PROOF {
                    fail!("Provided premise is not a proof");
                }
                achildren.push(self.store.child(e, 0));
            }
            let ap = if achildren.len() == 1 {
                // no premises: the nil terminator
                let nil = match self.app_info(pl_cons) {
                    Some(aic) if aic.attr.is_list_nil() => aic.cons,
                    _ => None,
                };
                let Some(nil) = nil else {
                    let s = self.show(pl_cons);
                    fail!("Premise list constructor {s} has no nil element");
                };
                nil
            } else {
                self.mk_expr(Kind::APPLY, &achildren)
            };
            let pf = self.mk_proof(ap);
            children.push(pf);
        } else {
            children.extend_from_slice(step.premises);
        }
        if children.len() == 1 {
            // a rule without arguments and premises
            return Some(children[0]);
        }
        let result = self.evaluate_program_app(&children);
        if self.store.is_evaluatable(result) {
            if err.is_some() {
                let stuck = self.store.kind(result) == Kind::APPLY
                    && self.store.child(result, 0) == children[0];
                let pattern = self
                    .get_program(children[0])
                    .filter(|&p| stuck && self.store.num_children(p) == 1)
                    .map(|p| self.store.child(self.store.child(p, 0), 0));
                if let Some(pattern) = pattern {
                    // the program did not apply: show what it expects
                    let eargs = self.store.children(pattern)[1..].to_vec();
                    let (se, sp) = (
                        self.show_list(&eargs, ", "),
                        self.show_list(&children[1..], ", "),
                    );
                    if let Some(e) = err.as_deref_mut() {
                        let _ = writeln!(e, "Expected args: {se}");
                        let _ = writeln!(e, "Provided args: {sp}");
                    }
                } else {
                    let s = self.show(result);
                    if let Some(e) = err {
                        let _ = writeln!(e, "Evaluation failed: {s}");
                    }
                }
            }
            return None;
        }
        Some(result)
    }
}
