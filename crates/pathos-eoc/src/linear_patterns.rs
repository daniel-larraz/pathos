//! Rewriting the cases of a program so that no parameter occurs twice in a
//! pattern (`plugins/linear_patterns/linear_patterns.cpp` in Ethos). Lean's
//! pattern matching, among others, needs that.
//!
//! A later occurrence of a parameter `x` becomes the new parameter
//! `$eo.lv.x.<n>`, and the equality the repetition stood for becomes the
//! guard `(eo::eq x $eo.lv.x.<n>)`. A guarded case that is not the last has
//! to fall through to the cases after it when the guard fails, so those
//! move to a continuation program `$eo.l.<n>.<prog>` that the guard's
//! `eo::ite` calls; a catch-all case over the parameters `$eo.dv.<i>` sends
//! what the linear pattern does not match there too. In the last case the
//! guard is an `eo::requires`.

use std::collections::HashMap;

use pathos_check::Checker;
use pathos_syntax::{Error, Result};
use pathos_term::{EvalOp, Kind, SymbolKind, Term};

/// A term the C++ takes for granted has another shape. The C++ would read
/// outside the term; here the stage stops.
fn malformed(what: &str) -> Error {
    Error::fatal(format!("LinearPattern: unexpected term: {what}"))
}

fn child(ck: &Checker, e: Term, i: usize) -> Result<Term> {
    (ck.store.children(e).get(i).copied())
        .ok_or_else(|| malformed(&format!("{} has no child {i}", ck.show(e))))
}

/// The type of `e`, or the null term if it has none, as `Expr::getType`.
fn type_or_null(ck: &mut Checker, e: Term) -> Term {
    ck.get_type(e, None).unwrap_or(ck.store.mk_null())
}

/// The programs that together do what `prog`, defined by `prog_def`, does,
/// with linear patterns only: each program and its cases. `prog` is always
/// among them, and each program comes after the continuations it calls.
pub fn linearize(ck: &mut Checker, prog: Term, prog_def: Term) -> Result<Vec<(Term, Term)>> {
    let mut ret = Vec::new();
    let mut curr_cases = Vec::new();
    let mut curr_prog = prog;
    let mut prog_count = 0usize;
    let ptype = type_or_null(ck, prog);
    let cases = ck.store.children(prog_def).to_vec();
    let ncases = cases.len();
    for (i, &case) in cases.iter().enumerate() {
        let pat = child(ck, case, 0)?;
        let body = child(ck, case, 1)?;
        let (lpat, cond) = linearize_pattern(ck, pat);
        let Some(cond) = cond else {
            let hd = mk_case_pattern(ck, curr_prog, pat)?;
            curr_cases.push(ck.mk_pair(hd, body));
            continue;
        };
        if i + 1 == ncases {
            // the last case: nothing to fall through to, so the guard is a
            // requirement
            let ctrue = ck.mk_true();
            let guarded_ret = ck.mk_expr(Kind::Eval(EvalOp::Requires), &[cond, ctrue, body]);
            let hd = mk_case_pattern(ck, curr_prog, lpat)?;
            curr_cases.push(ck.mk_pair(hd, guarded_ret));
            continue;
        }
        // the cases below go to a new copy of the program
        prog_count += 1;
        let name = format!("$eo.l.{prog_count}.{}", ck.show(prog));
        let new_prog = ck.mk_symbol(SymbolKind::ProgramConst, &name, ptype);
        let mut newappc = vec![new_prog];
        let mut defappc = vec![curr_prog];
        let mut was_default = true;
        let lpat_children = ck.store.children(lpat).to_vec();
        for (j, &arg) in lpat_children.iter().enumerate().skip(1) {
            was_default = was_default && ck.store.kind(arg) == Kind::PARAM;
            newappc.push(arg);
            let orig = child(ck, pat, j)?;
            let ty = type_or_null(ck, orig);
            defappc.push(ck.mk_symbol(SymbolKind::Param, &format!("$eo.dv.{j}"), ty));
        }
        let new_app = ck.mk_expr(Kind::APPLY, &newappc);
        let ret_lin = ck.mk_expr(Kind::Eval(EvalOp::IfThenElse), &[cond, body, new_app]);
        let hd = mk_case_pattern(ck, curr_prog, lpat)?;
        curr_cases.push(ck.mk_pair(hd, ret_lin));
        // a default is needed unless the linear case already matches all
        if !was_default {
            let def_app = ck.mk_expr(Kind::APPLY, &defappc);
            defappc[0] = new_prog;
            let def_ret = ck.mk_expr(Kind::APPLY, &defappc);
            curr_cases.push(ck.mk_pair(def_app, def_ret));
        }
        let curr_prog_def = ck.mk_expr(Kind::PROGRAM, &curr_cases);
        ret.push((curr_prog, curr_prog_def));
        curr_prog = new_prog;
        curr_cases.clear();
    }
    // what is left
    let curr_prog_def = ck.mk_expr(Kind::PROGRAM, &curr_cases);
    ret.push((curr_prog, curr_prog_def));
    ret.reverse();
    Ok(ret)
}

/// The case pattern `pat` with `prog` as its head.
fn mk_case_pattern(ck: &mut Checker, prog: Term, pat: Term) -> Result<Term> {
    if child(ck, pat, 0)? == prog {
        return Ok(pat);
    }
    let mut children = ck.store.children(pat).to_vec();
    children[0] = prog;
    // built as it is: the pattern was desugared when it was read
    Ok(ck.store.mk(Kind::APPLY, &children))
}

/// The linear form of one case pattern, and the equalities between
/// parameters that it stands for: each is `(eo::eq x y)`, where `y` is the
/// fresh parameter that replaced a further occurrence of `x`. For a
/// consumer that keeps the program's cases as they are and treats a failed
/// equality as "this case does not match".
pub fn linearize_case(ck: &mut Checker, pat: Term) -> (Term, Vec<Term>) {
    let mut params = HashMap::new();
    let mut conds = Vec::new();
    let lpat = linearize_rec(ck, pat, &mut params, &mut conds);
    (lpat, conds)
}

/// The linear pattern for `pat`, and the condition under which it stands
/// for `pat`; none if `pat` is linear already.
fn linearize_pattern(ck: &mut Checker, pat: Term) -> (Term, Option<Term>) {
    let mut params = HashMap::new();
    let mut conds = Vec::new();
    let lpat = linearize_rec(ck, pat, &mut params, &mut conds);
    let cond = match conds.as_slice() {
        [] => None,
        [cond] => Some(*cond),
        _ => Some(ck.mk_expr(Kind::Eval(EvalOp::And), &conds)),
    };
    (lpat, cond)
}

/// `pat` with every occurrence of a parameter after its first replaced by
/// a new parameter; `conds` gets the equalities between the two. The
/// occurrences are counted left to right.
fn linearize_rec(
    ck: &mut Checker,
    pat: Term,
    params: &mut HashMap<Term, usize>,
    conds: &mut Vec<Term>,
) -> Term {
    /// A term whose children are being rewritten.
    struct Frame {
        t: Term,
        children: Vec<Term>,
        changed: bool,
    }
    let mut stack: Vec<Frame> = Vec::new();
    // the term to rewrite next, and the term just rewritten
    let mut enter = Some(pat);
    let mut done: Option<Term> = None;
    loop {
        if let Some(t) = enter.take() {
            if ck.store.kind(t) == Kind::PARAM {
                done = Some(match params.get_mut(&t) {
                    None => {
                        params.insert(t, 1);
                        t
                    }
                    Some(n) => {
                        *n += 1;
                        let name = format!("$eo.lv.{}.{}", ck.show(t), *n);
                        let ty = type_or_null(ck, t);
                        let npat = ck.mk_symbol(SymbolKind::Param, &name, ty);
                        conds.push(ck.mk_expr(Kind::Eval(EvalOp::Eq), &[t, npat]));
                        npat
                    }
                });
            } else if ck.store.num_children(t) == 0 {
                done = Some(t);
            } else {
                stack.push(Frame {
                    t,
                    children: Vec::new(),
                    changed: false,
                });
            }
        }
        if let Some(r) = done.take() {
            let Some(f) = stack.last_mut() else {
                return r;
            };
            let orig = ck.store.children(f.t).get(f.children.len()).copied();
            f.changed = f.changed || orig != Some(r);
            f.children.push(r);
        }
        let Some(f) = stack.last() else {
            // not reached: the stack is empty only once the result is known
            return pat;
        };
        match ck.store.children(f.t).get(f.children.len()) {
            Some(&next) => enter = Some(next),
            None => {
                let Some(f) = stack.pop() else {
                    return pat;
                };
                // Built as it is: the pattern was desugared when it was
                // read, and building it again would, for one, add a second
                // nil to a right-assoc-nil application.
                done = Some(if f.changed {
                    ck.store.mk(ck.store.kind(f.t), &f.children)
                } else {
                    f.t
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pathos_check::Options;

    struct Sig {
        ck: Checker,
        and: Term,
        collapse: Term,
        x: Term,
        y: Term,
    }

    fn sig() -> Sig {
        // terms print in full
        let mut opts = Options::default();
        opts.set_option("print-dag", false);
        let mut ck = Checker::new(opts, Box::new(|_| {}));
        let b = ck.mk_bool_type();
        let and_ty = ck.mk_function_type(&[b, b], b);
        let and = ck.mk_symbol(SymbolKind::Const, "and", and_ty);
        let pt = ck.mk_program_type(&[b], b);
        let collapse = ck.mk_symbol(SymbolKind::ProgramConst, "$collapse", pt);
        let x = ck.mk_symbol(SymbolKind::Param, "x", b);
        let y = ck.mk_symbol(SymbolKind::Param, "y", b);
        Sig {
            ck,
            and,
            collapse,
            x,
            y,
        }
    }

    fn case(s: &mut Sig, a: Term, b: Term, body: Term) -> Term {
        let arg = s.ck.store.mk(Kind::APPLY, &[s.and, a, b]);
        let hd = s.ck.store.mk(Kind::APPLY, &[s.collapse, arg]);
        s.ck.mk_pair(hd, body)
    }

    fn shown(s: &Sig, progs: &[(Term, Term)]) -> Vec<String> {
        progs
            .iter()
            .map(|&(p, d)| format!("{} := {}", s.ck.show(p), s.ck.show(d)))
            .collect()
    }

    // The example of `linear_patterns.h`.
    #[test]
    fn a_guarded_case_before_others_splits_the_program() {
        let mut s = sig();
        let (x, y) = (s.x, s.y);
        let c1 = case(&mut s, x, x, x);
        let xy = s.ck.store.mk(Kind::APPLY, &[s.and, x, y]);
        let c2 = case(&mut s, x, y, xy);
        let def = s.ck.mk_expr(Kind::PROGRAM, &[c1, c2]);
        let progs = linearize(&mut s.ck, s.collapse, def).unwrap();
        assert_eq!(
            shown(&s, &progs),
            [
                "$eo.l.1.$collapse := (program (eo::tuple ($eo.l.1.$collapse (and x y)) \
                 (and x y)))",
                "$collapse := (program (eo::tuple ($collapse (and x $eo.lv.x.2)) \
                 (eo::ite (eo::eq x $eo.lv.x.2) x ($eo.l.1.$collapse (and x $eo.lv.x.2)))) \
                 (eo::tuple ($collapse $eo.dv.1) ($eo.l.1.$collapse $eo.dv.1)))",
            ]
        );
    }

    #[test]
    fn a_guarded_last_case_requires_its_guard() {
        let mut s = sig();
        let (x, y) = (s.x, s.y);
        let c1 = case(&mut s, x, y, y);
        let c2 = case(&mut s, x, x, x);
        let def = s.ck.mk_expr(Kind::PROGRAM, &[c1, c2]);
        let progs = linearize(&mut s.ck, s.collapse, def).unwrap();
        assert_eq!(
            shown(&s, &progs),
            ["$collapse := (program (eo::tuple ($collapse (and x y)) y) \
              (eo::tuple ($collapse (and x $eo.lv.x.2)) \
              (eo::requires (eo::eq x $eo.lv.x.2) true x)))"]
        );
    }

    #[test]
    fn linear_cases_stay_as_they_are() {
        let mut s = sig();
        let (x, y) = (s.x, s.y);
        let c1 = case(&mut s, x, y, y);
        let def = s.ck.mk_expr(Kind::PROGRAM, &[c1]);
        let progs = linearize(&mut s.ck, s.collapse, def).unwrap();
        assert_eq!(progs, [(s.collapse, def)]);
    }

    // A parameter that occurs three times gets two new parameters, and the
    // guards are joined; a fully general linear pattern needs no default.
    #[test]
    fn several_repetitions_and_a_general_pattern() {
        let mut s = sig();
        let b = s.ck.mk_bool_type();
        let pt = s.ck.mk_program_type(&[b, b, b], b);
        let p = s.ck.mk_symbol(SymbolKind::ProgramConst, "$p", pt);
        let (x, y) = (s.x, s.y);
        let hd1 = s.ck.store.mk(Kind::APPLY, &[p, x, x, x]);
        let c1 = s.ck.mk_pair(hd1, x);
        let hd2 = s.ck.store.mk(Kind::APPLY, &[p, x, y, y]);
        let c2 = s.ck.mk_pair(hd2, y);
        let def = s.ck.mk_expr(Kind::PROGRAM, &[c1, c2]);
        let progs = linearize(&mut s.ck, p, def).unwrap();
        assert_eq!(
            shown(&s, &progs),
            [
                "$eo.l.1.$p := (program (eo::tuple ($eo.l.1.$p x y $eo.lv.y.2) \
                 (eo::requires (eo::eq y $eo.lv.y.2) true y)))",
                "$p := (program (eo::tuple ($p x $eo.lv.x.2 $eo.lv.x.3) \
                 (eo::ite (eo::and (eo::eq x $eo.lv.x.2) (eo::eq x $eo.lv.x.3)) x \
                 ($eo.l.1.$p x $eo.lv.x.2 $eo.lv.x.3))))",
            ]
        );
    }
}
