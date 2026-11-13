//! Typing and matching (`TypeChecker::getType` and `match` in Ethos).

use std::collections::HashSet;
use std::fmt::Write;

use pathos_term::{EvalOp, Kind, Lit, LitKind, NodeKind, Term};

use crate::checker::{Checker, Ctx};

/// Appends formatted text to an optional error message. Messages are only
/// built on the second pass, after a check has failed (see
/// [`Checker::get_type`]).
macro_rules! out {
    ($out:expr, $($arg:tt)*) => {
        if let Some(o) = $out.as_deref_mut() {
            // writing to a String cannot fail
            let _ = write!(o, $($arg)*);
        }
    };
}

impl Checker {
    /// Sets the type rule of a literal kind. Fails if the kind is Boolean,
    /// whose type is builtin, or if the rule is already set to another type.
    pub fn set_literal_type_rule(
        &mut self,
        k: LitKind,
        t: Term,
        mut out: Option<&mut String>,
    ) -> bool {
        if k == LitKind::Boolean {
            out!(
                out,
                "Cannot set a type rule for kind {}, since Boolean literals have the builtin \
                 type Bool",
                Kind::Lit(k)
            );
            return false;
        }
        if let Some(&prev) = self.literal_type_rules.get(&k) {
            if prev != t {
                if out.is_some() {
                    let (st, sprev) = (self.show(t), self.show(prev));
                    out!(
                        out,
                        "Cannot set type rule for kind {} to {}, since its type was already \
                         set to {}",
                        Kind::Lit(k),
                        st,
                        sprev
                    );
                }
                return false;
            }
        }
        self.literal_type_rules.insert(k, t);
        true
    }

    /// The type of literals of kind `k`. `self_term` instantiates `eo::self`
    /// in the rule; without it, `eo::?` does.
    pub fn get_literal_type_rule(
        &mut self,
        k: LitKind,
        self_term: Option<Term>,
        mut out: Option<&mut String>,
    ) -> Option<Term> {
        if k == LitKind::Boolean {
            return Some(self.mk_bool_type());
        }
        let Some(&tp) = self.literal_type_rules.get(&k) else {
            out!(
                out,
                "No type rule declared for literal kind {}; use declare-consts to declare its \
                 type before use",
                Kind::Lit(k)
            );
            return None;
        };
        if !self.store.is_ground(tp) {
            let mut ctx = Ctx::new();
            ctx.insert(self.mk_self(), self_term.unwrap_or(self.mk_any()));
            return Some(self.evaluate(tp, &ctx));
        }
        Some(tp)
    }

    /// The type of `e`, or `None` if it is not well typed. Types are cached
    /// in the store.
    ///
    /// With `out`, a description of the failure is appended to it. Callers
    /// first call without `out` and, on failure, call again to get the
    /// message, as Ethos does.
    pub fn get_type(&mut self, e: Term, mut out: Option<&mut String>) -> Option<Term> {
        if let Some(t) = self.store.ty(e) {
            return Some(t);
        }
        let mut visited: HashSet<Term> = HashSet::new();
        let mut to_visit = vec![e];
        let mut ret = None;
        while let Some(&cur) = to_visit.last() {
            if let Some(t) = self.store.ty(cur) {
                ret = Some(t);
                to_visit.pop();
                continue;
            }
            if visited.insert(cur) {
                to_visit.extend_from_slice(self.store.children(cur));
            } else {
                let t = self.get_type_internal(cur, out.as_deref_mut())?;
                if self.store.is_ground(t) && self.store.is_evaluatable(t) {
                    if out.is_some() {
                        let st = self.show(t);
                        out!(out, "Has type {st} whose evaluation cannot be reduced");
                    }
                    return None;
                }
                self.store.set_ty(cur, t);
                ret = Some(t);
                to_visit.pop();
            }
        }
        ret
    }

    /// Whether the `eo::` operator or `PROOF` kind `k` takes `nargs`
    /// arguments.
    pub fn check_arity(k: Kind, nargs: usize, mut out: Option<&mut String>) -> bool {
        let ret = match k {
            Kind::Node(NodeKind::Proof) => nargs == 1,
            Kind::Eval(op) => match op {
                EvalOp::IsEq
                | EvalOp::Eq
                | EvalOp::IntDiv
                | EvalOp::IntMod
                | EvalOp::RatDiv
                | EvalOp::Pow
                | EvalOp::ToBin
                | EvalOp::Find
                | EvalOp::Compare
                | EvalOp::Log
                | EvalOp::Gt
                | EvalOp::ListLength
                | EvalOp::ListRev
                | EvalOp::ListSetof
                | EvalOp::ListSingletonElim
                | EvalOp::ListSingletonIntro
                | EvalOp::Nil => nargs == 2,
                EvalOp::ListConcat => nargs == 3,
                EvalOp::IsOk
                | EvalOp::TypeOf
                | EvalOp::NameOf
                | EvalOp::Hash
                | EvalOp::Not
                | EvalOp::Neg
                | EvalOp::IsNeg
                | EvalOp::Length
                | EvalOp::ToInt
                | EvalOp::ToRat
                | EvalOp::ToString
                | EvalOp::IsZ
                | EvalOp::IsQ
                | EvalOp::IsBin
                | EvalOp::IsStr
                | EvalOp::IsBool
                | EvalOp::IsVar
                | EvalOp::DtConstructors
                | EvalOp::DtSelectors => nargs == 1,
                EvalOp::Requires
                | EvalOp::IfThenElse
                | EvalOp::Cons
                | EvalOp::ListFind
                | EvalOp::ListErase
                | EvalOp::ListEraseAll
                | EvalOp::ListNth
                | EvalOp::ListMinclude
                | EvalOp::ListMeq
                | EvalOp::ListDiff
                | EvalOp::ListInter
                | EvalOp::ListRepeat => nargs == 3,
                EvalOp::Extract => nargs == 3 || nargs == 2,
                // the n-ary operators
                EvalOp::Add
                | EvalOp::Mul
                | EvalOp::And
                | EvalOp::Or
                | EvalOp::Xor
                | EvalOp::Concat => nargs == 2,
            },
            _ => {
                out!(out, "Unknown arity for {k}");
                false
            }
        };
        if !ret {
            out!(out, "Incorrect arity for {k}");
        }
        ret
    }

    /// The type of `e`, whose children all have their types cached.
    fn get_type_internal(&mut self, e: Term, mut out: Option<&mut String>) -> Option<Term> {
        let k = self.store.kind(e);
        match k {
            Kind::Node(NodeKind::Apply | NodeKind::ApplyOpaque) => {
                let children = self.store.children(e).to_vec();
                let mut ctx = Ctx::new();
                self.get_type_app_internal(&children, &mut ctx, out)
            }
            Kind::Node(NodeKind::Lambda) => {
                let vars = self.store.children(self.store.child(e, 0)).to_vec();
                let mut args = Vec::with_capacity(vars.len());
                for v in vars {
                    args.push(self.store.ty(v)?);
                }
                let ret = self.store.ty(self.store.child(e, 1))?;
                Some(self.mk_function_type(&args, ret))
            }
            Kind::Type
            | Kind::BoolType
            | Kind::Any
            | Kind::Node(NodeKind::FunctionType | NodeKind::ProgramType) => Some(self.mk_type()),
            Kind::Node(NodeKind::Proof) => {
                let ctype = self.store.ty(self.store.child(e, 0))?;
                if self.store.kind(ctype) != Kind::BoolType {
                    out!(out, "Non-Bool for argument of Proof");
                    return None;
                }
                Some(self.mk_proof_type())
            }
            // These are not really typed. Their type is the unknown, not
            // Type, so that they cannot be used as the types of terms.
            Kind::Node(NodeKind::QuoteType | NodeKind::Tuple) => Some(self.mk_any()),
            Kind::Lit(lk) => self.get_literal_type_rule(lk, Some(e), out),
            Kind::Node(NodeKind::As | NodeKind::AsReturn) => {
                // an AS term is only built when the annotation was wrong
                out!(out, "Encountered bad type for {}", k.to_term_string());
                None
            }
            Kind::Node(NodeKind::Parameterized) => self.store.ty(self.store.child(e, 1)),
            Kind::Node(NodeKind::Variable) => {
                let (c0, c1) = (self.store.child(e, 0), self.store.child(e, 1));
                let ctype1 = self.store.ty(c0);
                let ctype2 = self.store.ty(c1)?;
                let string_type =
                    self.get_literal_type_rule(LitKind::String, Some(c0), out.as_deref_mut())?;
                if ctype1 != Some(string_type) {
                    out!(out, "Expected a string for first argument of eo::var");
                    return None;
                }
                if self.store.kind(ctype2) != Kind::Type {
                    out!(out, "Expected a type for second argument of eo::var");
                    return None;
                }
                Some(c1)
            }
            Kind::Eval(op) => {
                let children = self.store.children(e).to_vec();
                let ctypes: Vec<Option<Term>> =
                    children.iter().map(|&c| self.store.ty(c)).collect();
                self.get_literal_op_type(op, &children, &ctypes, out)
            }
            Kind::Symbol(_) | Kind::Node(NodeKind::Program) => {
                // symbols always have a type; programs are never typed
                out!(out, "Unknown kind {k}");
                None
            }
        }
    }

    /// The type of the application of `children[0]` to the rest, whose types
    /// are cached. `ctx` receives the instantiation of the head's type.
    pub(crate) fn get_type_app_internal(
        &mut self,
        children: &[Term],
        ctx: &mut Ctx,
        mut out: Option<&mut String>,
    ) -> Option<Term> {
        let hd = children[0];
        let hd_type = self.store.ty(hd)?;
        let hk = self.store.kind(hd_type);
        if hk != Kind::FUNCTION_TYPE && hk != Kind::PROGRAM_TYPE {
            if out.is_some() {
                let (shd, sty) = (self.show(hd), self.show(hd_type));
                out!(out, "Non-function {shd} as head of APPLY\nIts type is {sty}");
            }
            return None;
        }
        let hdtypes = self.store.children(hd_type).to_vec();
        if hdtypes.len() != children.len() {
            if out.is_some() {
                let shd = self.show(hd);
                out!(
                    out,
                    "Incorrect arity for {}, which expects {} arguments but {} were provided",
                    shd,
                    hdtypes.len().wrapping_sub(1),
                    children.len() - 1
                );
            }
            return None;
        }
        let mut visited = HashSet::new();
        for i in 1..hdtypes.len() {
            let mut hdt = hdtypes[i - 1];
            let mut child = children[i];
            let type_success;
            if self.store.kind(hdt) == Kind::QUOTE_TYPE {
                // For an argument type (eo::quote x), the argument must have
                // the type of x, which is ground. Then x is bound to the
                // argument itself: no matching is needed.
                let x = self.store.child(hdt, 0);
                let ct = self.store.ty(child)?;
                let cte = self.store.ty(x)?;
                if ct != cte {
                    type_success = false;
                    hdt = cte;
                    child = ct;
                } else {
                    type_success = true;
                    hdt = x;
                    ctx.insert(hdt, child);
                }
            } else {
                child = self.store.ty(child)?;
                type_success = self.match_terms(hdt, child, ctx, &mut visited);
            }
            if !type_success {
                if out.is_some() {
                    let msg = format!(
                        "Checking application of {}\nUnexpected type of child #{}\n  Term: {}\n  \
                         Has type: {}\n  Expected type: {}\n  Context {}\n",
                        self.show(hd),
                        i,
                        self.show(children[i]),
                        self.show(child),
                        self.show(hdt),
                        self.show_ctx(ctx)
                    );
                    out!(out, "{msg}");
                }
                return None;
            }
        }
        // the return type, in the matched context
        let ret = hdtypes[hdtypes.len() - 1];
        Some(self.evaluate(ret, ctx))
    }

    /// Matches the pattern `a` against `b`, extending `ctx` so that `a`
    /// instantiated by `ctx` is `b`. `visited` holds the pairs already
    /// matched by earlier calls that share `ctx`.
    pub(crate) fn match_terms(
        &self,
        a: Term,
        b: Term,
        ctx: &mut Ctx,
        visited: &mut HashSet<(Term, Term)>,
    ) -> bool {
        let s = &self.store;
        let mut stack = vec![(a, b)];
        while let Some((x, y)) = stack.pop() {
            if s.is_ground(x) {
                if x == y {
                    continue;
                }
                return false;
            }
            // Equal non-ground terms are still traversed, to bind each of
            // their parameters to itself.
            if !visited.insert((x, y)) {
                continue;
            }
            if s.num_children(x) == 0 {
                if s.kind(x) != Kind::PARAM {
                    return false;
                }
                // The types of x and y are not compared here.
                match ctx.get(&x) {
                    None => {
                        ctx.insert(x, y);
                    }
                    Some(&prev) => {
                        if prev != y {
                            return false;
                        }
                    }
                }
            } else {
                if s.num_children(x) != s.num_children(y) || s.kind(x) != s.kind(y) {
                    return false;
                }
                for (&cx, &cy) in s.children(x).iter().zip(s.children(y)) {
                    stack.push((cx, cy));
                }
            }
        }
        true
    }

    /// The type of an `eo::` operator application.
    fn get_literal_op_type(
        &mut self,
        op: EvalOp,
        children: &[Term],
        child_types: &[Option<Term>],
        mut out: Option<&mut String>,
    ) -> Option<Term> {
        if !Checker::check_arity(Kind::Eval(op), child_types.len(), out.as_deref_mut()) {
            return None;
        }
        // Most of these operators only occur in patterns, where typing is
        // not strict.
        match op {
            EvalOp::TypeOf => Some(self.mk_type()),
            // the type is the second argument
            EvalOp::Nil => Some(children[1]),
            EvalOp::Add
            | EvalOp::Mul
            | EvalOp::Pow
            | EvalOp::Neg
            | EvalOp::And
            | EvalOp::Or
            | EvalOp::Xor
            | EvalOp::Not
            | EvalOp::Concat
            | EvalOp::Extract => child_types[0],
            EvalOp::IfThenElse
            | EvalOp::Cons
            | EvalOp::ListConcat
            | EvalOp::ListNth
            | EvalOp::ListErase
            | EvalOp::ListEraseAll
            | EvalOp::ListRev
            | EvalOp::ListSetof
            | EvalOp::ListDiff
            | EvalOp::ListInter
            | EvalOp::ListSingletonElim
            | EvalOp::ListSingletonIntro => child_types[1],
            EvalOp::Requires => child_types[2],
            EvalOp::ListRepeat => {
                let op_type = child_types[0]?;
                if self.store.kind(op_type) == Kind::FUNCTION_TYPE {
                    Some(self.get_function_type(op_type).1)
                } else {
                    None
                }
            }
            EvalOp::IsOk
            | EvalOp::IsEq
            | EvalOp::Eq
            | EvalOp::IsNeg
            | EvalOp::Compare
            | EvalOp::IsZ
            | EvalOp::IsQ
            | EvalOp::IsBin
            | EvalOp::IsStr
            | EvalOp::IsBool
            | EvalOp::IsVar
            | EvalOp::Gt
            | EvalOp::ListMinclude
            | EvalOp::ListMeq => Some(self.mk_bool_type()),
            EvalOp::Hash
            | EvalOp::Log
            | EvalOp::IntDiv
            | EvalOp::IntMod
            | EvalOp::ToInt
            | EvalOp::Length
            | EvalOp::Find
            | EvalOp::ListLength
            | EvalOp::ListFind => self.get_literal_type_rule(LitKind::Numeral, None, out),
            EvalOp::RatDiv | EvalOp::ToRat => {
                self.get_literal_type_rule(LitKind::Rational, None, out)
            }
            EvalOp::NameOf | EvalOp::ToString => {
                self.get_literal_type_rule(LitKind::String, None, out)
            }
            EvalOp::ToBin => self.get_literal_type_rule(LitKind::Binary, None, out),
            EvalOp::DtConstructors | EvalOp::DtSelectors => Some(self.mk_list_type()),
        }
    }

    /// The term for a string literal given as Ethos's `mkLiteral` takes it:
    /// text in which `\u{...}` escapes denote code points.
    pub fn mk_string_literal(&mut self, s: &str) -> Term {
        self.store.mk_lit(Lit::String(pathos_term::EoString::parse(s, true)))
    }
}
