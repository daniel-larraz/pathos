//! Checking proof steps (`State::notifyStep` in Ethos's `state.cpp`).

use pathos_term::{Kind, Term};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::attr::Attr;
use crate::build::rest_of;
#[cfg(verus_keep_ghost)]
use crate::build::{lemma_all_kept, lemma_part};
use crate::checker::Checker;
use crate::eval::{copy_of, push_all};
use crate::typing::say;

/// A `step` or `step-pop` command, as parsed.
#[cfg_attr(verus_keep_ghost, verus_verify)]
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

// Written for Verus, which follows a loop over indices without a
// specification of the iterator, and does not take a closure.
#[allow(clippy::needless_range_loop, clippy::manual_map, clippy::manual_filter)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Checker {
    // The texts of the messages that print terms. Trusted: printing is not
    // verified.

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_no_nil(&self, pl_cons: Term) -> String {
        format!(
            "Premise list constructor {} has no nil element\n",
            self.show(pl_cons)
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_args(&self, expected: &[Term], provided: &[Term]) -> String {
        format!(
            "Expected args: {}\nProvided args: {}\n",
            self.show_list(expected, ", "),
            self.show_list(provided, ", ")
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_stuck(&self, result: Term) -> String {
        format!("Evaluation failed: {}\n", self.show(result))
    }

    /// Computes what a step proves: applies the rule's program to the
    /// arguments, the conclusion (for `:conclusion-explicit` rules), the
    /// assumption (for `:assumption` rules) and the premises.
    ///
    /// Returns `None` if the step does not check. With `err`, the reason is
    /// appended to it. The result is not necessarily of type Bool; the
    /// caller checks that.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has_step(*step),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    pub fn check_step(&mut self, step: &Step<'_>, mut err: Option<&mut String>) -> Option<Term> {
        proof_decl! { let ghost start = *self; }
        let tuple = match self.app_info(step.rule) {
            Some(ai) => {
                if ai.attr == Attr::ProofRule {
                    ai.cons
                } else {
                    None
                }
            }
            None => None,
        };
        let tuple = match tuple {
            Some(t) => {
                if self.store.num_children(t) == 4 {
                    Some(t)
                } else {
                    None
                }
            }
            None => None,
        };
        let tuple = match tuple {
            Some(t) => t,
            None => {
                say(
                    &mut err,
                    "Provided :rule is not recognized as a proof rule\n",
                );
                return None;
            }
        };
        let t = copy_of(self.store.children(tuple));
        // The program of the rule or, for a rule without arguments and
        // premises, its conclusion.
        let mut children = Vec::new();
        children.push(t[3]);
        push_all(&mut children, step.args);
        let pl_cons = if t[0] != self.mk_any() {
            Some(t[0])
        } else {
            None
        };
        let is_assume = t[1] == self.mk_true();
        let is_conc_explicit = t[2] == self.mk_true();
        if is_conc_explicit {
            let proven = match step.proven {
                Some(proven) => proven,
                None => {
                    say(
                        &mut err,
                        "Rules with :conclusion-explicit require a provided conclusion.\n",
                    );
                    return None;
                }
            };
            children.push(proven);
        }
        if step.is_pop == is_assume {
            if step.is_pop {
                // The scope may hold more assumptions, from assume commands
                // inside it; the first one is that of the assume-push.
                let a = match step.assumption {
                    Some(a) => a,
                    None => {
                        say(
                            &mut err,
                            "step-pop can only be used on rules with :assumption\n",
                        );
                        return None;
                    }
                };
                children.push(a);
            }
        } else if step.is_pop {
            say(
                &mut err,
                "step-pop can only be used on rules with :assumption\n",
            );
            return None;
        } else {
            say(&mut err, "step cannot be used on rules with :assumption\n");
            return None;
        }
        if let Some(pl_cons) = pl_cons {
            // The premises (eo::pf F1) ... (eo::pf Fn) are collected into
            // (eo::pf (and F1 ... Fn)), for the :premise-list operator `and`.
            let mut achildren = Vec::new();
            achildren.push(pl_cons);
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                self.has_all(achildren@), achildren@.len() >= 1,
            ))]
            for i in 0..step.premises.len() {
                let e = step.premises[i];
                if self.store.kind(e) != Kind::PROOF {
                    say(&mut err, "Provided premise is not a proof\n");
                    return None;
                }
                proof! { self.store.lemma_shape(e); }
                achildren.push(self.store.child(e, 0));
            }
            let ap = if achildren.len() == 1 {
                // no premises: the nil terminator
                let nil = match self.app_info(pl_cons) {
                    Some(aic) => {
                        if aic.attr.is_list_nil() {
                            aic.cons
                        } else {
                            None
                        }
                    }
                    None => None,
                };
                match nil {
                    Some(nil) => nil,
                    None => {
                        if err.is_some() {
                            let msg = self.msg_no_nil(pl_cons);
                            say(&mut err, &msg);
                        }
                        return None;
                    }
                }
            } else {
                self.mk_expr(Kind::APPLY, &achildren)
            };
            let pf = self.mk_proof(ap);
            proof! { lemma_all_kept(&self.store, &start.store, children@); }
            children.push(pf);
        } else {
            push_all(&mut children, step.premises);
        }
        if children.len() == 1 {
            // a rule without arguments and premises
            return Some(children[0]);
        }
        proof_decl! { let ghost before = *self; }
        let result = self.evaluate_program_app(&children);
        if self.store.is_evaluatable(result) {
            if err.is_some() {
                proof! {
                    lemma_all_kept(&self.store, &before.store, children@);
                    self.store.lemma_shape(result);
                }
                let stuck = self.store.kind(result) == Kind::APPLY
                    && self.store.child(result, 0) == children[0];
                let pattern = match self.get_program(children[0]) {
                    Some(p) => {
                        if stuck && self.store.num_children(p) == 1 {
                            proof! {
                                self.store.lemma_children(p);
                                self.store.lemma_children(self.store.kids(p.idx())[0]);
                            }
                            Some(self.store.child(self.store.child(p, 0), 0))
                        } else {
                            None
                        }
                    }
                    None => None,
                };
                if let Some(pattern) = pattern {
                    // the program did not apply: show what it expects
                    let eargs = copy_of(rest_of(self.store.children(pattern), 1));
                    let msg = self.msg_args(&eargs, rest_of(&children, 1));
                    say(&mut err, &msg);
                } else {
                    let msg = self.msg_stuck(result);
                    say(&mut err, &msg);
                }
            }
            return None;
        }
        Some(result)
    }
}
