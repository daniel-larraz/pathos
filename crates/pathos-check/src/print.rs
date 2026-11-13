//! Printing terms (`Expr::printDebug` in Ethos's `expr.cpp`).

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use pathos_term::{Kind, Lit, NodeKind, Term};

use crate::attr::Attr;
use crate::checker::{Checker, Ctx};

/// Quotes a symbol with `|` if it is not a simple SMT-LIB symbol.
fn quote_symbol(s: &str) -> String {
    if s.is_empty() {
        return "||".into();
    }
    // eo:: symbols are never quoted
    if s.starts_with("eo::") {
        return s.into();
    }
    let simple = |c: char| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c);
    if s.chars().all(simple) && !s.starts_with(|c: char| c.is_ascii_digit()) {
        return s.into();
    }
    // already quoted: look at what is between the bars
    let inner = if s.len() > 1 && s.starts_with('|') && s.ends_with('|') {
        &s[1..s.len() - 1]
    } else {
        s
    };
    // a quoted symbol cannot contain | or \
    let cleaned: String = inner.chars().map(|c| if c == '\\' || c == '|' { '_' } else { c }).collect();
    format!("|{cleaned}|")
}

/// Whether `(f t1 ... tn)` may be read as something other than the plain
/// application when `f` has this attribute.
fn is_desugaring_attr(a: Attr) -> bool {
    !matches!(
        a,
        Attr::None | Attr::Program | Attr::ProofRule | Attr::Datatype | Attr::DatatypeConstructor
    )
}

impl Checker {
    /// The subterms of `e` that occur more than once, each after its own
    /// subterms, numbered in that order.
    fn compute_let_binding(&self, e: Term) -> (Vec<Term>, HashMap<Term, usize>) {
        let mut count: HashMap<Term, usize> = HashMap::new();
        let mut visited: HashSet<Term> = HashSet::new();
        let mut order = Vec::new();
        let mut visit = vec![e];
        while let Some(&cur) = visit.last() {
            let children = self.store.children(cur);
            if children.is_empty() {
                visit.pop();
                continue;
            }
            if visited.insert(cur) {
                visit.extend_from_slice(children);
                continue;
            }
            visit.pop();
            let n = count.entry(cur).or_insert(0);
            if *n == 0 {
                order.push(cur);
            }
            *n += 1;
        }
        let mut ll = Vec::new();
        let mut lbind = HashMap::new();
        for t in order {
            if count[&t] > 1 {
                lbind.insert(t, ll.len());
                ll.push(t);
            }
        }
        (ll, lbind)
    }

    fn print_internal(&self, e: Term, os: &mut String, lbind: &HashMap<Term, usize>) {
        let s = &self.store;
        let mut visit: Vec<(Term, usize)> = vec![(e, 0)];
        while let Some(&(cur, idx)) = visit.last() {
            let top = visit.len() - 1;
            let nchildren = s.num_children(cur);
            if idx == 0 {
                if let Some(id) = lbind.get(&cur) {
                    let _ = write!(os, "_v{id}");
                    visit.pop();
                    continue;
                }
                let k = s.kind(cur);
                if nchildren == 0 {
                    match (s.lit(cur), s.symbol_name(cur)) {
                        (Some(l), _) => match l {
                            Lit::Hex(_) => {
                                let _ = write!(os, "#x{l}");
                            }
                            Lit::Binary(b) => {
                                if b.size() == 0 {
                                    os.push_str("(eo::to_bin 0 0)");
                                } else {
                                    let _ = write!(os, "#b{l}");
                                }
                            }
                            Lit::String(_) => {
                                let _ = write!(os, "\"{l}\"");
                            }
                            // there is no syntax for decimal literals
                            Lit::Decimal(_) => {
                                let _ = write!(os, "(! {l} :decimal)");
                            }
                            _ => {
                                let _ = write!(os, "{l}");
                            }
                        },
                        (None, Some(name)) => {
                            if k.is_symbol() {
                                os.push_str(&quote_symbol(name));
                            } else {
                                os.push_str(name);
                            }
                        }
                        (None, None) => os.push_str(&k.to_term_string()),
                    }
                    visit.pop();
                    continue;
                }
                os.push('(');
                let head = s.child(cur, 0);
                if k == Kind::APPLY_OPAQUE {
                    // ambiguous functions are written with `as`
                    let attr = self.attribute_kind(head);
                    if attr == Attr::Amb || attr == Attr::AmbDatatypeConstructor {
                        os.push_str("as ");
                    }
                } else if k != Kind::Node(NodeKind::Apply)
                    || s.num_children(head) > 0
                    || is_desugaring_attr(self.attribute_kind(head))
                {
                    // The `_` of an application is left out only when the
                    // result reads back as the same term.
                    os.push_str(&k.to_term_string());
                    os.push(' ');
                }
                visit[top].1 += 1;
                visit.push((head, 0));
            } else if idx >= nchildren {
                os.push(')');
                visit.pop();
            } else {
                os.push(' ');
                visit[top].1 += 1;
                visit.push((s.child(cur, idx), 0));
            }
        }
    }

    /// Appends the term as Ethos prints it in messages. With the
    /// `print_dag` option, subterms that occur more than once are printed
    /// once and named with `eo::define`.
    pub fn print(&self, e: Term, os: &mut String) {
        let mut cparen = String::new();
        let mut lbind = HashMap::new();
        if self.opts.print_dag {
            let (ll, lb) = self.compute_let_binding(e);
            lbind = lb;
            for l in ll {
                let Some(id) = lbind.remove(&l) else { continue };
                let _ = write!(os, "(eo::define ((_v{id} ");
                self.print_internal(l, os, &lbind);
                lbind.insert(l, id);
                os.push_str(")) ");
                cparen.push(')');
            }
        }
        self.print_internal(e, os, &lbind);
        os.push_str(&cparen);
    }

    /// The term as Ethos prints it in messages.
    pub fn show(&self, e: Term) -> String {
        let mut s = String::new();
        self.print(e, &mut s);
        s
    }

    /// The terms in brackets, separated by `sep`. Ethos uses `", "` for
    /// lists of expressions and `" "` for lists of expression values.
    pub fn show_list(&self, es: &[Term], sep: &str) -> String {
        let mut s = String::from("[");
        for (i, &e) in es.iter().enumerate() {
            if i > 0 {
                s.push_str(sep);
            }
            self.print(e, &mut s);
        }
        s.push(']');
        s
    }

    /// A context as `[x -> t, ...]`, in the order of the parameters'
    /// handles.
    pub fn show_ctx(&self, ctx: &Ctx) -> String {
        let mut s = String::from("[");
        for (i, (&k, &v)) in ctx.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            self.print(k, &mut s);
            s.push_str(" -> ");
            self.print(v, &mut s);
        }
        s.push(']');
        s
    }
}

#[cfg(test)]
mod tests {
    use super::quote_symbol;

    #[test]
    fn quoting() {
        assert_eq!(quote_symbol(""), "||");
        assert_eq!(quote_symbol("abc"), "abc");
        assert_eq!(quote_symbol("eo::List::cons"), "eo::List::cons");
        assert_eq!(quote_symbol("a b"), "|a b|");
        assert_eq!(quote_symbol("1a"), "|1a|");
        assert_eq!(quote_symbol("|a b|"), "|a b|");
        assert_eq!(quote_symbol("a\\b|c"), "|a_b_c|");
        assert_eq!(quote_symbol("$eo_prog_x"), "$eo_prog_x");
    }
}
