//! Evaluation (`TypeChecker::evaluate` and the program and `eo::` operator
//! evaluators in Ethos's `type_checker.cpp`).

use std::collections::{HashMap, HashSet};

use pathos_term::{EvalOp, Integer, Kind, Lit, NodeKind, Term};

use crate::attr::Attr;
use crate::checker::{Checker, Ctx};
use crate::matching::{self, CaseMatch};

/// One level of evaluation: a term being evaluated in a context. A new level
/// starts each time a program application reduces to a case's body.
struct EvFrame {
    init: Term,
    ctx: Ctx,
    /// The value of each subterm visited so far; `None` while its children
    /// are being evaluated.
    visited: HashMap<Term, Option<Term>>,
    visit: Vec<Term>,
    /// The program application this level computes, to be cached.
    result_key: Option<Vec<Term>>,
}

impl EvFrame {
    fn new(init: Term, ctx: Ctx, result_key: Option<Vec<Term>>) -> EvFrame {
        EvFrame {
            init,
            ctx,
            visited: HashMap::new(),
            visit: vec![init],
            result_key,
        }
    }
}

impl Checker {
    /// Evaluates `e` with the parameters in `ctx` replaced: applies programs
    /// and `eo::` operators until none applies. Stuck applications stay in
    /// the result.
    pub fn evaluate(&mut self, e: Term, ctx: &Ctx) -> Term {
        // Results of program applications in this call, so that programs
        // recursing over a term visit shared subterms once. `None` is an
        // application that failed: it is not tried again, as in Ethos, so
        // its warnings appear once.
        let mut eval_cache: HashMap<Vec<Term>, Option<Term>> = HashMap::new();
        let mut estack = vec![EvFrame::new(e, ctx.clone(), None)];
        let mut evaluated: Option<Term> = None;
        let mut new_context = false;
        let mut can_evaluate = true;
        while !estack.is_empty() {
            let top = estack.len() - 1;
            while let Some(&cur) = estack[top].visit.last() {
                let evf = &mut estack[top];
                // Not evaluatable, and ground or nothing to substitute: the
                // term stays as it is.
                if !self.store.is_evaluatable(cur)
                    && (self.store.is_ground(cur) || evf.ctx.is_empty())
                {
                    evf.visited.insert(cur, Some(cur));
                    evf.visit.pop();
                    continue;
                }
                let ck = self.store.kind(cur);
                if ck == Kind::PARAM {
                    // a parameter the context does not bind stays
                    let v = evf.ctx.get(&cur).copied().unwrap_or(cur);
                    evf.visited.insert(cur, Some(v));
                    evf.visit.pop();
                    continue;
                }
                match evf.visited.get(&cur).copied() {
                    None => {
                        // a plugin may evaluate the term itself
                        if self.eval_plugin.is_some() {
                            let ctx = estack[top].ctx.clone();
                            if let Some(r) = self.plugin_evaluate(cur, &ctx) {
                                let evf = &mut estack[top];
                                evf.visited.insert(cur, Some(r));
                                evf.visit.pop();
                                continue;
                            }
                        }
                        let evf = &mut estack[top];
                        // first visit: evaluate the children
                        evf.visited.insert(cur, None);
                        let children = self.store.children(cur);
                        if ck == Kind::Eval(EvalOp::IfThenElse) {
                            if children.len() != 3 {
                                // malformed: does not evaluate
                                evf.visited.insert(cur, Some(cur));
                                evf.visit.pop();
                                continue;
                            }
                            // only the condition, for now
                            evf.visit.push(children[0]);
                        } else {
                            evf.visit.extend_from_slice(children);
                        }
                        continue;
                    }
                    Some(Some(_)) => {
                        evf.visit.pop();
                        continue;
                    }
                    Some(None) => {}
                }
                // second visit: the children are evaluated (for
                // if-then-else, at least the condition is)
                let children = self.store.children(cur).to_vec();
                let mut cchildren: Vec<Option<Term>> = Vec::with_capacity(children.len());
                let mut cchanged = false;
                for &cp in &children {
                    let v = evf.visited.get(&cp).copied().flatten();
                    if let Some(v) = v {
                        cchanged = cchanged || v != cp;
                    }
                    cchildren.push(v);
                }
                evaluated = None;
                match ck {
                    Kind::Node(NodeKind::Apply | NodeKind::ApplyOpaque) => {
                        let Some(args) = cchildren.iter().copied().collect::<Option<Vec<Term>>>()
                        else {
                            unreachable!("children of an application are evaluated first")
                        };
                        if self.store.kind(args[0]) == Kind::PROGRAM_CONST {
                            if let Some(&r) = eval_cache.get(&args) {
                                evaluated = r;
                            } else {
                                let mut new_ctx = Ctx::new();
                                evaluated = self.evaluate_program_internal(&args, &mut new_ctx);
                                match evaluated {
                                    // a body that needs substitution is
                                    // evaluated at a new level
                                    Some(ev)
                                        if !self.store.is_ground(ev) && !new_ctx.is_empty() =>
                                    {
                                        new_context = true;
                                        estack.push(EvFrame::new(ev, new_ctx, Some(args)));
                                    }
                                    // otherwise the result, or the failure,
                                    // is final
                                    _ => {
                                        eval_cache.insert(args, evaluated);
                                    }
                                }
                            }
                        }
                    }
                    Kind::Eval(EvalOp::IfThenElse) => {
                        let evf = &mut estack[top];
                        let cond = cchildren[0].and_then(|c| match self.store.lit(c) {
                            Some(Lit::Bool(b)) => Some(*b),
                            _ => None,
                        });
                        if let Some(b) = cond {
                            // only the branch taken is evaluated
                            let index = if b { 1 } else { 2 };
                            match cchildren[index] {
                                None => {
                                    can_evaluate = false;
                                    evf.visit.push(children[index]);
                                }
                                Some(v) => evaluated = Some(v),
                            }
                        } else {
                            // Both branches are evaluated, so that
                            // substitution into them is complete.
                            for i in 1..3 {
                                if cchildren[i].is_none() {
                                    evf.visit.push(children[i]);
                                    can_evaluate = false;
                                }
                            }
                        }
                    }
                    Kind::Eval(op) => {
                        let Some(args) = cchildren.iter().copied().collect::<Option<Vec<Term>>>()
                        else {
                            unreachable!("children of an operator are evaluated first")
                        };
                        evaluated = self.evaluate_literal_op_internal(op, &args);
                        if self.fatal.is_some() {
                            // the run is over; see `Checker::take_fatal`
                            return e;
                        }
                    }
                    _ => {}
                }
                if new_context {
                    break;
                }
                if can_evaluate {
                    let ev = match evaluated {
                        Some(ev) => ev,
                        None if cchanged => {
                            let args: Vec<Term> = cchildren
                                .iter()
                                .zip(&children)
                                .map(|(c, &orig)| c.unwrap_or(orig))
                                .collect();
                            self.store.mk(ck, &args)
                        }
                        None => cur,
                    };
                    evaluated = Some(ev);
                    let evf = &mut estack[top];
                    evf.visited.insert(cur, Some(ev));
                    evf.visit.pop();
                } else {
                    can_evaluate = true;
                }
            }
            if new_context {
                // continue with the level just pushed
                new_context = false;
                continue;
            }
            // this level is done: hand its result to the level below
            let Some(evf) = estack.pop() else { break };
            let result = evf
                .visited
                .get(&evf.init)
                .copied()
                .flatten()
                .unwrap_or(evf.init);
            evaluated = Some(result);
            if let Some(key) = evf.result_key {
                eval_cache.insert(key, Some(result));
            }
            if let Some(parent) = estack.last_mut()
                && let Some(app) = parent.visit.pop()
            {
                parent.visited.insert(app, Some(result));
            }
        }
        evaluated.unwrap_or(e)
    }

    /// The plugin's value of `e`, if a plugin evaluates it.
    fn plugin_evaluate(&mut self, e: Term, ctx: &Ctx) -> Option<Term> {
        let mut plugin = self.eval_plugin.take()?;
        let ret = if plugin.has_evaluation(self, e) {
            plugin.evaluate(self, e, ctx)
        } else {
            None
        };
        self.eval_plugin = Some(plugin);
        ret
    }

    /// Applies the program `args[0]` to the other arguments and evaluates
    /// the result. Returns the unevaluated application if no case matches.
    pub fn evaluate_program_app(&mut self, args: &[Term]) -> Term {
        let mut new_ctx = Ctx::new();
        match self.evaluate_program_internal(args, &mut new_ctx) {
            Some(ret) => self.evaluate(ret, &new_ctx),
            None => self.store.mk(Kind::APPLY, args),
        }
    }

    /// Finds the first case of the program `children[0]` that matches the
    /// arguments. Returns the case's body and fills `new_ctx` with the
    /// match. Returns `None` if the arguments are not ground values or no
    /// case matches.
    pub(crate) fn evaluate_program_internal(
        &mut self,
        children: &[Term],
        new_ctx: &mut Ctx,
    ) -> Option<Term> {
        if children.iter().any(|&c| !self.store.is_ground(c)) {
            return None;
        }
        // Arguments that are themselves stuck, or are unapplied programs,
        // make the application stuck.
        if children[1..].iter().any(|&c| self.store.is_evaluatable(c)) {
            return None;
        }
        let hd = children[0];
        if let Some(mut plugin) = self.eval_plugin.take() {
            let handles = plugin.has_evaluation(self, hd);
            let ret = handles.then(|| plugin.evaluate_program(self, children, new_ctx));
            self.eval_plugin = Some(plugin);
            if let Some(ret) = ret {
                return ret;
            }
        }
        self.count_program(hd);
        let Some(prog) = self.get_program(hd) else {
            let msg = format!("No program defined for {}", self.show(hd));
            self.warn(&msg);
            return None;
        };
        match matching::match_cases(&self.store, prog, children, new_ctx) {
            CaseMatch::Body(body) => Some(body),
            CaseMatch::BadArity(pat) => {
                let msg1 = format!(
                    "*** Bad number of arguments provided in function call to {}",
                    self.show(pat)
                );
                let msg2 = format!("  Arguments: {}", self.show_list(children, " "));
                self.warn(&msg1);
                self.warn(&msg2);
                None
            }
            CaseMatch::NoCase => None,
        }
    }

    /// Applies the `eo::` operator to the arguments. Returns the application
    /// itself if it does not evaluate.
    pub fn evaluate_literal_op(&mut self, op: EvalOp, args: &[Term]) -> Term {
        match self.evaluate_literal_op_internal(op, args) {
            Some(ret) => ret,
            None => self.store.mk(Kind::Eval(op), args),
        }
    }

    /// The nil terminator of `op` for lists whose type (or, without
    /// `tinst_list_arg`, whose element type) is `tinst`.
    fn evaluate_nil(
        &mut self,
        op: Term,
        nil: Term,
        is_left: bool,
        tinst: Option<Term>,
        tinst_list_arg: bool,
    ) -> Option<Term> {
        if self.store.kind(nil) != Kind::PARAMETERIZED {
            // the terminator does not depend on the type
            return Some(nil);
        }
        let tinst = tinst.filter(|&t| self.store.is_ground(t))?;
        let top = self.get_type(op, None)?;
        // For a right associative operator of type (-> T L L), the element
        // type is the first argument type and the list type the second; for
        // a left associative one, of type (-> L T L), the other way round.
        // Ethos takes these children whatever the type looks like: for
        // (-> T L) the "second argument type" is the first child of L. Where
        // there is no such child Ethos reads past the end; here the
        // terminator is then not found.
        let src = if is_left == tinst_list_arg {
            *self.store.children(top).first()?
        } else {
            let rest = *self.store.children(top).get(1)?;
            *self.store.children(rest).first()?
        };
        let mut ctx = Ctx::new();
        let mut visited = HashSet::new();
        if !self.match_terms(src, tinst, &mut ctx, &mut visited) {
            return None;
        }
        let body = self.store.child(nil, 1);
        Some(self.evaluate(body, &ctx))
    }

    /// The elements of the `op`-list `e`, and its tail. With `check_nil`,
    /// the tail must be that term; otherwise this warns and returns `None`.
    fn get_nary_children(
        &mut self,
        e: Term,
        op: Term,
        check_nil: Option<Term>,
        children: &mut Vec<Term>,
        is_left: bool,
    ) -> Option<Term> {
        let orig = e;
        let mut e = e;
        while let Some((head, tail)) = self.nary_step(e, op, is_left) {
            children.push(head);
            e = tail;
        }
        if let Some(nil) = check_nil
            && e != nil
        {
            let msg = format!(
                "...expected associative application to end in {}, got {}",
                self.show(nil),
                self.show(orig)
            );
            self.warn(&msg);
            return None;
        }
        Some(e)
    }

    /// If `e` is `(op head tail)` (or `(op tail head)` when left
    /// associative), its head and tail.
    #[inline]
    fn nary_step(&self, e: Term, op: Term, is_left: bool) -> Option<(Term, Term)> {
        let s = &self.store;
        if s.kind(e) != Kind::APPLY || s.num_children(e) != 2 {
            return None;
        }
        let cop = s.child(e, 0);
        if s.kind(cop) != Kind::APPLY || s.num_children(cop) != 2 || s.child(cop, 0) != op {
            return None;
        }
        let (a, b) = (s.child(cop, 1), s.child(e, 1));
        Some(if is_left { (b, a) } else { (a, b) })
    }

    /// Whether `e` is an `op`-list ending in `nil`.
    fn is_nary_list(&self, e: Term, op: Term, nil: Term, is_left: bool) -> bool {
        let mut e = e;
        while let Some((_, tail)) = self.nary_step(e, op, is_left) {
            e = tail;
        }
        e == nil
    }

    /// The `n`-th tail of the `op`-list `e`, which has at least `n`
    /// elements.
    fn get_nary_nth_tail(&self, e: Term, op: Term, is_left: bool, n: usize) -> Term {
        let mut e = e;
        for _ in 0..n {
            match self.nary_step(e, op, is_left) {
                Some((_, tail)) => e = tail,
                None => break,
            }
        }
        e
    }

    /// Puts the elements `hargs` in front of the `op`-list `ret`.
    fn prepend_nary_children(
        &mut self,
        op: Term,
        ret: Term,
        hargs: &[Term],
        is_left: bool,
    ) -> Term {
        let mut ret = ret;
        for &h in hargs.iter().rev() {
            ret = if is_left {
                let c1 = self.store.mk_apply(op, ret);
                self.store.mk_apply(c1, h)
            } else {
                let c1 = self.store.mk_apply(op, h);
                self.store.mk_apply(c1, ret)
            };
        }
        ret
    }

    fn mk_usize(&mut self, n: usize) -> Term {
        self.mk_numeral(Integer::from(n))
    }

    /// Stops the run: evaluating `k` needs an argument that `args` lacks.
    /// Ethos reads past the end of its argument vector here, which is
    /// undefined behaviour and usually ends in a segmentation fault.
    fn missing_argument(&mut self, k: EvalOp, args: &[Term]) -> Option<Term> {
        if self.fatal.is_none() {
            self.fatal = Some(format!(
                "Too few arguments when evaluating literal op {}, {} arguments {}",
                Kind::Eval(k),
                args.len(),
                self.show_list(args, " ")
            ));
        }
        None
    }

    /// Applies the `eo::` operator to evaluated arguments. Returns `None`
    /// if it does not evaluate on them.
    pub(crate) fn evaluate_literal_op_internal(
        &mut self,
        k: EvalOp,
        args: &[Term],
    ) -> Option<Term> {
        let first = *args.first()?;
        let ground = |ck: &Checker, t: Term| ck.store.is_ground(t);
        let is_eval = |ck: &Checker, t: Term| ck.store.is_evaluatable(t);
        // These two may evaluate on non-ground arguments.
        match k {
            EvalOp::IfThenElse => {
                return match self.store.lit(first) {
                    // the branches may be non-ground
                    Some(Lit::Bool(b)) => Some(args[if *b { 1 } else { 2 }]),
                    // equal branches are not simplified
                    _ => None,
                };
            }
            EvalOp::Requires => {
                // (eo::requires t s r) is r when t and s are the same value,
                // whether or not r is ground.
                if ground(self, args[0]) && !is_eval(self, args[0]) {
                    let Some(&second) = args.get(1) else {
                        return self.missing_argument(k, args);
                    };
                    if ground(self, second) && !is_eval(self, second) && first == second {
                        return match args.get(2) {
                            Some(&r) => Some(r),
                            None => self.missing_argument(k, args),
                        };
                    }
                }
                return None;
            }
            _ => {}
        }
        if args.iter().any(|&a| !ground(self, a)) {
            return None;
        }
        // These three look at their second argument unless the first is
        // stuck.
        if matches!(k, EvalOp::IsEq | EvalOp::Eq | EvalOp::Compare)
            && args.len() < 2
            && !is_eval(self, first)
        {
            return self.missing_argument(k, args);
        }
        match k {
            // false exactly when the argument is stuck
            EvalOp::IsOk => return Some(self.mk_bool(!is_eval(self, first))),
            // true when both arguments are the same value; false also when
            // one of them is stuck
            EvalOp::IsEq => {
                return Some(self.mk_bool(
                    !is_eval(self, first) && !is_eval(self, args[1]) && first == args[1],
                ));
            }
            EvalOp::Eq => {
                // only compares values
                if !is_eval(self, first) && !is_eval(self, args[1]) {
                    return Some(self.mk_bool(first == args[1]));
                }
                return None;
            }
            EvalOp::Hash => {
                if is_eval(self, first) {
                    return None;
                }
                let h = self.get_hash(first);
                // Ethos keeps the low 32 bits
                return Some(self.mk_numeral(Integer::from(h as u32)));
            }
            EvalOp::Compare => {
                if is_eval(self, first) || is_eval(self, args[1]) {
                    return None;
                }
                let h1 = self.get_hash(args[0]);
                let h2 = self.get_hash(args[1]);
                return Some(self.mk_bool(h1 > h2));
            }
            EvalOp::IsZ
            | EvalOp::IsQ
            | EvalOp::IsBin
            | EvalOp::IsStr
            | EvalOp::IsBool
            | EvalOp::IsVar => {
                let kk = match k {
                    EvalOp::IsZ => Kind::NUMERAL,
                    EvalOp::IsQ => Kind::RATIONAL,
                    EvalOp::IsBin => Kind::BINARY,
                    EvalOp::IsStr => Kind::STRING,
                    EvalOp::IsBool => Kind::BOOLEAN,
                    _ => Kind::VARIABLE,
                };
                return Some(self.mk_bool(self.store.kind(first) == kk));
            }
            EvalOp::TypeOf => {
                if !is_eval(self, first)
                    && let Some(et) = self.get_type(first, None)
                    && ground(self, et)
                {
                    return Some(et);
                }
            }
            EvalOp::NameOf => {
                if self.store.kind(first) == Kind::VARIABLE {
                    // `(eo::var)` is a variable without children. Ethos
                    // reads its first child all the same, past the end.
                    return match self.store.children(first).first() {
                        Some(&name) => Some(name),
                        None => self.missing_argument(k, args),
                    };
                }
            }
            EvalOp::DtSelectors => {
                // an ambiguous constructor comes with its type annotation
                let sym = if self.store.kind(first) == Kind::APPLY_OPAQUE {
                    self.store.child(first, 0)
                } else {
                    first
                };
                return match self.app_info(sym) {
                    Some(ac)
                        if matches!(
                            ac.attr,
                            Attr::DatatypeConstructor | Attr::AmbDatatypeConstructor
                        ) =>
                    {
                        ac.cons
                    }
                    _ => None,
                };
            }
            EvalOp::DtConstructors => return self.evaluate_dt_constructors(first),
            _ => {}
        }
        // On literal values, run the literal evaluator. Symbols are not
        // values.
        if args.iter().all(|&a| self.store.kind(a).is_literal()) {
            if !Checker::check_arity(Kind::Eval(k), args.len(), None) {
                let msg = format!(
                    "Wrong number of arguments when applying literal op {}, {} arguments ({})",
                    Kind::Eval(k),
                    args.len(),
                    self.show_list(args, " ")
                );
                self.warn(&msg);
                return None;
            }
            let lits: Vec<&Lit> = args.iter().filter_map(|&a| self.store.lit(a)).collect();
            let eval = Lit::evaluate(k, &lits)?;
            return Some(self.store.mk_lit(eval));
        }
        if !k.is_list_op() {
            return None;
        }
        self.evaluate_list_op(k, args)
    }

    fn evaluate_dt_constructors(&mut self, arg: Term) -> Option<Term> {
        let mut sym = arg;
        // A parametric datatype is applied to its parameters; it is fully
        // applied when its type is Type.
        let mut is_param = false;
        if self.store.kind(sym) == Kind::APPLY && self.get_type(sym, None) == Some(self.mk_type()) {
            is_param = true;
            while self.store.kind(sym) == Kind::APPLY && self.store.num_children(sym) > 0 {
                sym = self.store.child(sym, 0);
            }
        }
        let cons = match self.app_info(sym) {
            Some(ac) if ac.attr == Attr::Datatype => ac.cons?,
            _ => return None,
        };
        if !is_param {
            return Some(cons);
        }
        // the ambiguous constructors get the datatype as annotation
        let mut cargs = Vec::new();
        let cop = self.mk_list_cons();
        self.get_nary_children(cons, cop, None, &mut cargs, false);
        let mut cargsp = Vec::with_capacity(cargs.len());
        for c in cargs {
            cargsp.push(if self.attribute_kind(c) == Attr::AmbDatatypeConstructor {
                self.store.mk(Kind::APPLY_OPAQUE, &[c, arg])
            } else {
                c
            });
        }
        Some(self.mk_list(&cargsp))
    }

    /// Evaluates a list operator: `args[0]` is the list constructor.
    fn evaluate_list_op(&mut self, k: EvalOp, args: &[Term]) -> Option<Term> {
        let mut op = args[0];
        // the attributes are on the operator inside (eo::_ params op)
        if self.store.kind(op) == Kind::PARAMETERIZED {
            op = self.store.child(op, 1);
        }
        let ac = self.app_info(op)?;
        let (ck, cons) = (ac.attr, ac.cons);
        if !ck.is_list_nil() {
            return None;
        }
        let cons = cons?;
        let is_left = ck.is_left_nil();
        if k == EvalOp::ListSingletonIntro {
            return self.evaluate_list_singleton_intro(op, cons, is_left, args);
        }
        // the nil terminator, which may depend on the type of args[1]
        let nil = if k == EvalOp::Nil {
            // eo::nil takes the type itself
            if args.len() < 2 && self.store.kind(cons) == Kind::PARAMETERIZED {
                return self.missing_argument(k, args);
            }
            return self.evaluate_nil(args[0], cons, is_left, args.get(1).copied(), false);
        } else if self.store.kind(cons) != Kind::PARAMETERIZED {
            cons
        } else if args.len() > 1 {
            // Operators whose second argument is an element, not a list,
            // infer the terminator from the element type.
            self.get_type(args[1], None);
            let t = self.store.ty(args[1]);
            let tinst_list_arg = k != EvalOp::Cons && k != EvalOp::ListRepeat;
            self.evaluate_nil(args[0], cons, is_left, t, tinst_list_arg)?
        } else {
            return None;
        };
        // The `i`-th argument, read where Ethos reads it. A missing one
        // stops the run.
        macro_rules! arg {
            ($i:expr) => {
                match args.get($i) {
                    Some(&a) => a,
                    None => return self.missing_argument(k, args),
                }
            };
        }
        let mut hargs = Vec::new();
        match k {
            EvalOp::Cons | EvalOp::ListConcat => {
                let is_concat = k == EvalOp::ListConcat;
                let tail_index = if is_left { 1 } else { 2 };
                let head_index = if is_left { 2 } else { 1 };
                let ret = arg!(if is_concat { tail_index } else { 2 });
                if !self.is_nary_list(ret, op, nil, is_left) {
                    return None;
                }
                if k == EvalOp::Cons {
                    hargs.push(arg!(1));
                } else {
                    self.get_nary_children(arg!(head_index), op, Some(nil), &mut hargs, is_left)?;
                    // nothing to rebuild when the tail is empty
                    if ret == nil {
                        return Some(arg!(head_index));
                    }
                }
                Some(self.prepend_nary_children(op, ret, &hargs, is_left))
            }
            EvalOp::ListRepeat => {
                let count = match self.store.lit(arg!(2)) {
                    Some(Lit::Numeral(i)) if i.fits_u32() => i.to_u32(),
                    _ => return None,
                };
                let mut ret = nil;
                for _ in 0..count {
                    ret = self.prepend_nary_children(op, ret, &[arg!(1)], is_left);
                }
                Some(ret)
            }
            EvalOp::ListLength => {
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                Some(self.mk_usize(hargs.len()))
            }
            EvalOp::ListNth => {
                let i = match self.store.lit(arg!(2)) {
                    Some(Lit::Numeral(i)) if i.fits_u32() => i.to_u32() as usize,
                    _ => return None,
                };
                // all the elements are read, to check that this is a list
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                hargs.get(i).copied()
            }
            EvalOp::ListFind => {
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                let elem = arg!(2);
                match hargs.iter().position(|&h| h == elem) {
                    Some(i) => Some(self.mk_usize(i)),
                    None => {
                        let neg_one = match self.neg_one {
                            Some(t) => t,
                            None => self.mk_numeral(Integer::one().neg()),
                        };
                        self.neg_one = Some(neg_one);
                        Some(neg_one)
                    }
                }
            }
            EvalOp::ListErase | EvalOp::ListEraseAll => {
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                let is_all = k == EvalOp::ListEraseAll;
                let mut result = Vec::new();
                let mut change_index = 0;
                let mut change_size = 0;
                for (i, &h) in hargs.iter().enumerate() {
                    if h == arg!(2) {
                        change_index = i + 1;
                        if !is_all {
                            break;
                        }
                        change_size = result.len();
                        continue;
                    }
                    result.push(h);
                }
                if change_index == 0 {
                    return Some(arg!(1));
                }
                // Keep the list after the last change as it is, and rebuild
                // only what comes before.
                if is_all {
                    result.truncate(change_size);
                }
                let ret = self.get_nary_nth_tail(arg!(1), op, is_left, change_index);
                Some(self.prepend_nary_children(op, ret, &result, is_left))
            }
            EvalOp::ListRev => {
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                hargs.reverse();
                Some(self.prepend_nary_children(op, nil, &hargs, is_left))
            }
            EvalOp::ListSetof => {
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                let mut seen = HashSet::new();
                let mut result = Vec::new();
                let mut change_index = 0;
                let mut change_size = 0;
                for (i, &elem) in hargs.iter().enumerate() {
                    if seen.insert(elem) {
                        result.push(elem);
                    } else {
                        change_index = i + 1;
                        change_size = result.len();
                    }
                }
                if change_index == 0 {
                    return Some(arg!(1));
                }
                result.truncate(change_size);
                let ret = self.get_nary_nth_tail(arg!(1), op, is_left, change_index);
                Some(self.prepend_nary_children(op, ret, &result, is_left))
            }
            EvalOp::ListMinclude | EvalOp::ListMeq => {
                let mut hargs2 = Vec::new();
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                self.get_nary_children(arg!(2), op, Some(nil), &mut hargs2, is_left)?;
                if arg!(1) == arg!(2) {
                    return Some(self.mk_true());
                }
                let mut count1: HashMap<Term, u32> = HashMap::new();
                let mut count2: HashMap<Term, u32> = HashMap::new();
                for &elem in &hargs {
                    *count1.entry(elem).or_default() += 1;
                }
                for &elem in &hargs2 {
                    *count2.entry(elem).or_default() += 1;
                }
                let is_eq = k == EvalOp::ListMeq;
                // With equally many distinct elements, comparing the counts
                // in one direction is enough.
                if is_eq && count1.len() != count2.len() {
                    return Some(self.mk_false());
                }
                for (elem, &n2) in &count2 {
                    let n1 = count1.get(elem).copied().unwrap_or(0);
                    if if is_eq { n1 != n2 } else { n1 < n2 } {
                        return Some(self.mk_false());
                    }
                }
                Some(self.mk_true())
            }
            EvalOp::ListDiff | EvalOp::ListInter => {
                let mut hargs2 = Vec::new();
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                self.get_nary_children(arg!(2), op, Some(nil), &mut hargs2, is_left)?;
                let is_diff = k == EvalOp::ListDiff;
                if arg!(1) == arg!(2) {
                    return Some(if is_diff { nil } else { arg!(1) });
                }
                let mut count2: HashMap<Term, u32> = HashMap::new();
                for &elem in &hargs2 {
                    *count2.entry(elem).or_default() += 1;
                }
                let mut change_index = 0;
                let mut change_size = 0;
                let mut result = Vec::new();
                for (i, &h) in hargs.iter().enumerate() {
                    let found = match count2.get_mut(&h) {
                        Some(n) => {
                            *n -= 1;
                            if *n == 0 {
                                count2.remove(&h);
                            }
                            true
                        }
                        None => false,
                    };
                    if found == is_diff {
                        change_index = i + 1;
                        change_size = result.len();
                        continue;
                    }
                    result.push(h);
                }
                if change_index == 0 {
                    return Some(arg!(1));
                }
                result.truncate(change_size);
                let ret = self.get_nary_nth_tail(arg!(1), op, is_left, change_index);
                Some(self.prepend_nary_children(op, ret, &result, is_left))
            }
            EvalOp::ListSingletonElim => {
                self.get_nary_children(arg!(1), op, Some(nil), &mut hargs, is_left)?;
                // a list of one element is that element
                Some(if hargs.len() == 1 { hargs[0] } else { arg!(1) })
            }
            _ => None,
        }
    }

    /// `(eo::list_singleton_intro op t)`: `t` if it is an `op`-list, the
    /// list of the one element `t` otherwise.
    fn evaluate_list_singleton_intro(
        &mut self,
        op: Term,
        nil: Term,
        is_left: bool,
        args: &[Term],
    ) -> Option<Term> {
        let Some(&arg) = args.get(1) else {
            return self.missing_argument(EvalOp::ListSingletonIntro, args);
        };
        self.get_type(arg, None);
        let arg_type = self.store.ty(arg);
        if let Some(n) = self.evaluate_nil(op, nil, is_left, arg_type, true)
            && self.is_nary_list(arg, op, n, is_left)
        {
            return Some(arg);
        }
        let n = self.evaluate_nil(op, nil, is_left, arg_type, false)?;
        if self.is_nary_list(arg, op, n, is_left) {
            return Some(arg);
        }
        Some(self.prepend_nary_children(op, n, &[arg], is_left))
    }

    /// The constructor term of a symbol for the application in `children`
    /// (the head and its arguments): the symbol's own, or, if that depends
    /// on type parameters, its instance for the type of the first argument.
    pub(crate) fn compute_constructor_term(
        &mut self,
        attr: Attr,
        cons: Option<Term>,
        children: &[Term],
    ) -> Option<Term> {
        let ct = cons?;
        if self.store.kind(ct) != Kind::PARAMETERIZED {
            return Some(ct);
        }
        if children.len() == 1 {
            let msg = format!(
                "Failed to determine parameters for {}",
                self.show(children[0])
            );
            self.warn(&msg);
            return None;
        }
        if !attr.is_list_nil() {
            let msg = format!(
                "Unknown category for parameterized operator {}",
                self.show(children[0])
            );
            self.warn(&msg);
            return None;
        }
        let is_left = attr.is_left_nil();
        let arg = children[1];
        let Some(t) = self.get_type(arg, None) else {
            if self.store.is_ground(arg) {
                let msg = format!(
                    "Type inference failed for {} applied to {}, failed to type check {}",
                    self.show(children[0]),
                    self.show(arg),
                    self.show(arg)
                );
                self.warn(&msg);
            }
            return None;
        };
        // This is still `None` if, say, the type is not ground.
        self.evaluate_nil(children[0], ct, is_left, Some(t), false)
    }
}
