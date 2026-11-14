//! The `desugar` stage (`plugins/desugar/desugar.cpp` in Ethos): rewrites a
//! signature into the Eunoia core that the later stages read.
//!
//! The stage notes declarations, programs, rules, definitions, attributes
//! and literal type rules as the parser reports them. At the end it prints
//! them again, without the attributes that the parser has already applied,
//! together with generated cases (`$eo_typeof`, `$eo_nil`, datatype
//! reflection, the proof checker or the verification conditions) into the
//! template `plugins/desugar/eo_desugar.eo`.
//!
//! The functions follow the C++ one for one, since the output has to be the
//! same byte for byte.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write;

use pathos_check::{Attr, Checker};
use pathos_elab::{Plugin, State};
use pathos_syntax::{Error, Result};
use pathos_term::{BitVec, EoString, Integer, Kind, Lit, LitKind, Rational, SymbolKind, Term};

use crate::std_plugin::{
    StdPlugin, literal_kind_to_string, mk_parse_def_name, read_text, replace_all, rtrim_lines,
    subterms_of_kind, write_text,
};

/// What the parser reported, in the order it did.
enum Decl {
    /// A definition: a symbol carrying its name, and the term.
    Define(Term, Term),
    Const(Term),
    Rule(Term),
    /// A program and its cases, if it has them yet.
    Program(Term, Option<Term>),
}

/// The terms the stage makes when it starts.
struct Syms {
    bool_type: Term,
    t_true: Term,
    model_sat: Term,
    model_unsat: Term,
    /// `$eo_pf`, which stands for the proof kind in what is printed.
    pf: Term,
}

/// The cases of the generated proof checker
/// (`plugins/desugar/desugar_checker.cpp`).
#[derive(Default)]
struct DesugarChecker {
    rules: String,
    rule_invokes: String,
    rule_invokes_pop: String,
}

pub struct Desugar {
    std: StdPlugin,
    syms: Option<Syms>,
    decl_seen: Vec<Decl>,
    /// The last definition of each name, by the name as given.
    define_last: HashMap<String, Term>,
    attr_decl: HashMap<Term, (Attr, Option<Term>)>,
    decl_processed: HashSet<Term>,
    /// How many symbols print as each name so far.
    overload_count: HashMap<String, usize>,
    overload_id: HashMap<Term, usize>,
    /// What to print in place of a term: overloads get a suffix, and the
    /// builtin list and proof symbols a `$eo_` name.
    overload_san_visited: HashMap<Term, Term>,
    gen_vcs: bool,
    gen_checker: bool,
    excluded_rules: HashSet<String>,
    excluded_methods: HashSet<String>,
    excluded_symbols: HashSet<String>,
    lt_kind_processed: HashSet<LitKind>,
    lt_decl_processed: HashSet<Term>,
    lit_type_decl: String,
    lit_type_prog: String,
    defs: String,
    eo_is_list_nil: String,
    eo_nil_nground: String,
    eo_nil: String,
    lean_parser_metadata: String,
    eo_typeof: String,
    eo_is_closed: String,
    /// The numbers of opaque arguments the signature's operators have.
    index_arities: BTreeSet<usize>,
    eo_typeof_nground: String,
    eo_dt_cons_param: String,
    eo_dt_cons: String,
    eo_dt_sel: String,
    eo_vc: String,
    eo_dt_cons_param_count: usize,
    dchecker: DesugarChecker,
    /// For each type, the variables that stand for the first, second, ...
    /// variable of that type in a canonical type.
    vars: HashMap<Term, Vec<Term>>,
    canon_type_prog_name: HashMap<Term, String>,
}

fn lean_parser_attr_name(a: Attr) -> &'static str {
    match a {
        Attr::LeftAssoc => "left-assoc",
        Attr::RightAssoc => "right-assoc",
        Attr::LeftAssocNil => "left-assoc-nil",
        Attr::RightAssocNil => "right-assoc-nil",
        Attr::LeftAssocNsNil => "left-assoc-ns-nil",
        Attr::RightAssocNsNil => "right-assoc-ns-nil",
        Attr::Chainable => "chainable",
        Attr::Pairwise => "pairwise",
        Attr::ArgList => "arg-list",
        Attr::Binder => "binder",
        Attr::Opaque => "opaque",
        _ => "none",
    }
}

/// A term the C++ takes for granted is not there. The C++ would read past
/// the end of a child list or fail an assertion; here the stage stops.
fn malformed(what: &str) -> Error {
    Error::fatal(format!("Desugar: unexpected term: {what}"))
}

fn type_of(ck: &mut Checker, e: Term) -> Result<Term> {
    ck.get_type(e, None)
        .ok_or_else(|| malformed(&format!("{} has no type", ck.show(e))))
}

fn child(ck: &Checker, e: Term, i: usize) -> Result<Term> {
    (ck.store.children(e).get(i).copied())
        .ok_or_else(|| malformed(&format!("{} has no child {i}", ck.show(e))))
}

impl Desugar {
    pub fn new(gen_vcs: bool) -> Result<Desugar> {
        let mut eo_vc = String::new();
        if gen_vcs {
            eo_vc.push_str(";; verification conditions\n\n");
        }
        Ok(Desugar {
            std: StdPlugin::new()?,
            syms: None,
            decl_seen: Vec::new(),
            define_last: HashMap::new(),
            attr_decl: HashMap::new(),
            decl_processed: HashSet::new(),
            overload_count: HashMap::new(),
            overload_id: HashMap::new(),
            overload_san_visited: HashMap::new(),
            gen_vcs,
            gen_checker: !gen_vcs,
            excluded_rules: HashSet::new(),
            excluded_methods: HashSet::new(),
            excluded_symbols: HashSet::new(),
            lt_kind_processed: HashSet::new(),
            lt_decl_processed: HashSet::new(),
            lit_type_decl: String::new(),
            lit_type_prog: String::new(),
            defs: String::new(),
            eo_is_list_nil: String::new(),
            eo_nil_nground: String::new(),
            eo_nil: String::new(),
            lean_parser_metadata: String::new(),
            eo_typeof: String::new(),
            eo_is_closed: String::new(),
            index_arities: BTreeSet::new(),
            eo_typeof_nground: String::new(),
            eo_dt_cons_param: String::new(),
            eo_dt_cons: String::new(),
            eo_dt_sel: String::new(),
            eo_vc,
            eo_dt_cons_param_count: 0,
            dchecker: DesugarChecker::default(),
            vars: HashMap::new(),
            canon_type_prog_name: HashMap::new(),
        })
    }

    fn syms(&self) -> Result<&Syms> {
        self.syms
            .as_ref()
            .ok_or_else(|| Error::fatal("Desugar: used before it was initialized"))
    }

    /// The name `e` is printed under: its own, or `$eoo_<name>.<n>` for the
    /// n-th symbol of that name.
    fn print_name(&mut self, ck: &mut Checker, e: Term) -> Result<String> {
        let shown = ck.show(e);
        let oid = match self.overload_id.get(&e) {
            Some(&oid) => oid,
            None => {
                let count = self.overload_count.entry(shown.clone()).or_default();
                let oid = *count;
                *count += 1;
                self.overload_id.insert(e, oid);
                if oid > 0 {
                    let ct = type_of(ck, e)?;
                    let Kind::Symbol(kind) = ck.store.kind(e) else {
                        return Err(malformed(&format!("{shown} is not a symbol")));
                    };
                    let ctov = ck.mk_symbol(kind, &format!("$eoo_{shown}.{}", oid + 1), ct);
                    self.overload_san_visited.insert(e, ctov);
                }
                oid
            }
        };
        Ok(if oid > 0 {
            format!("$eoo_{shown}.{}", oid + 1)
        } else {
            shown
        })
    }

    /// `e` as it is printed: with the replacements for overloads.
    fn print_term(&mut self, ck: &mut Checker, e: Term) -> Result<String> {
        let es = self.mk_sanitize(ck, e)?;
        Ok(ck.show(es))
    }

    fn mk_sanitize(&mut self, ck: &mut Checker, t: Term) -> Result<Term> {
        let mut visited: HashMap<Term, Option<Term>> = (self.overload_san_visited.iter())
            .map(|(&k, &v)| (k, Some(v)))
            .collect();
        self.mk_sanitize_with(ck, t, &mut visited)
    }

    /// `t` with each term replaced as `visited` says, and each proof term
    /// `(eo::pf F)` by the application `($eo_pf F)`.
    fn mk_sanitize_with(
        &mut self,
        ck: &mut Checker,
        t: Term,
        visited: &mut HashMap<Term, Option<Term>>,
    ) -> Result<Term> {
        let pf = self.syms()?.pf;
        let mut visit = vec![t];
        while let Some(&cur) = visit.last() {
            match visited.get(&cur).copied() {
                None => {
                    visited.insert(cur, None);
                    visit.extend_from_slice(ck.store.children(cur));
                }
                Some(done) => {
                    visit.pop();
                    if done.is_some() {
                        continue;
                    }
                    let k = ck.store.kind(cur);
                    let mut child_changed = false;
                    let mut children = Vec::with_capacity(ck.store.num_children(cur));
                    for &cn in ck.store.children(cur) {
                        let Some(Some(r)) = visited.get(&cn).copied() else {
                            return Err(malformed("a term that contains itself"));
                        };
                        child_changed = child_changed || cn != r;
                        children.push(r);
                    }
                    let ret = if k == Kind::PROOF {
                        let Some(&proven) = children.first() else {
                            return Err(malformed("a proof term without a formula"));
                        };
                        ck.store.mk(Kind::APPLY, &[pf, proven])
                    } else if child_changed {
                        ck.store.mk(k, &children)
                    } else {
                        cur
                    };
                    visited.insert(cur, Some(ret));
                }
            }
        }
        visited
            .get(&t)
            .copied()
            .flatten()
            .ok_or_else(|| malformed("a term that was not rewritten"))
    }

    /// `t` with its variables replaced by the canonical ones of their
    /// types, so that types that differ only in variable names are equal.
    fn mk_canonize(&mut self, ck: &mut Checker, t: Term) -> Result<Term> {
        let mut visited: HashMap<Term, Option<Term>> = HashMap::new();
        let mut index: HashMap<Term, usize> = HashMap::new();
        for v in ck.get_variables(&[t]) {
            let tv = type_of(ck, v)?;
            let i = index.entry(tv).or_default();
            let tvars = self.vars.entry(tv).or_default();
            if tvars.len() == *i {
                tvars.push(v);
            } else {
                visited.insert(v, Some(tvars[*i]));
            }
            *i += 1;
        }
        self.mk_sanitize_with(ck, t, &mut visited)
    }

    /// Adds to `params` the variables `vars` and, before each, the
    /// variables of its type.
    fn get_param_list(
        &mut self,
        ck: &mut Checker,
        vars: &[Term],
        params: &mut Vec<Term>,
        visited: &mut HashMap<Term, bool>,
    ) -> Result<()> {
        let mut to_visit = vars.to_vec();
        while let Some(&cur) = to_visit.last() {
            match visited.get(&cur).copied() {
                Some(true) => {
                    to_visit.pop();
                }
                None => {
                    let tcur = type_of(ck, cur)?;
                    visited.insert(cur, false);
                    to_visit.extend(ck.get_variables(&[tcur]));
                }
                Some(false) => {
                    type_of(ck, cur)?;
                    visited.insert(cur, true);
                    params.push(cur);
                    to_visit.pop();
                }
            }
        }
        Ok(())
    }

    /// Prints `params` from `start_index` on. Those not in `nimplicit` are
    /// marked `:implicit` if `use_implicit`; those in it `:opaque` if
    /// `is_opaque`.
    #[allow(clippy::too_many_arguments)]
    fn finalize_param_list(
        &mut self,
        ck: &mut Checker,
        os: &mut String,
        params: &[Term],
        use_implicit: bool,
        nimplicit: &[Term],
        is_opaque: bool,
        start_index: usize,
    ) -> Result<()> {
        for (i, &cur) in params.iter().enumerate().skip(start_index) {
            if i > 0 {
                os.push(' ');
            }
            let tcur = type_of(ck, cur)?;
            let _ = write!(os, "({} {}", ck.show(cur), self.print_term(ck, tcur)?);
            if !nimplicit.contains(&cur) {
                if use_implicit {
                    os.push_str(" :implicit");
                }
            } else if is_opaque {
                os.push_str(" :opaque");
            }
            os.push(')');
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn print_param_list_shared(
        &mut self,
        ck: &mut Checker,
        vars: &[Term],
        os: &mut String,
        params: &mut Vec<Term>,
        visited: &mut HashMap<Term, bool>,
        use_implicit: bool,
        is_opaque: bool,
    ) -> Result<()> {
        let start_index = params.len();
        self.get_param_list(ck, vars, params, visited)?;
        self.finalize_param_list(ck, os, params, use_implicit, vars, is_opaque, start_index)
    }

    fn print_param_list(
        &mut self,
        ck: &mut Checker,
        vars: &[Term],
        os: &mut String,
        use_implicit: bool,
    ) -> Result<()> {
        let (mut params, mut visited) = (Vec::new(), HashMap::new());
        self.print_param_list_shared(ck, vars, os, &mut params, &mut visited, use_implicit, false)
    }

    fn is_excluded(&self, ck: &Checker, e: Term, k: Kind) -> bool {
        let name = ck.show(e);
        match k {
            Kind::PROOF_RULE => self.excluded_rules.contains(&name),
            Kind::PROGRAM_CONST => {
                self.excluded_methods.contains(&name)
                    || (name.strip_prefix("$eo_prog_"))
                        .is_some_and(|rule| self.excluded_rules.contains(rule))
            }
            Kind::CONST => self.excluded_symbols.contains(&name),
            _ => false,
        }
    }

    fn get_attribute(&self, e: Term) -> Attr {
        self.attr_decl.get(&e).map_or(Attr::None, |a| a.0)
    }

    /// The program `prog`, with its cases if it has them, as text.
    fn finalize_program(
        &mut self,
        ck: &mut Checker,
        prog: Term,
        prog_def: Option<Term>,
    ) -> Result<String> {
        let mut os = String::new();
        if self.is_excluded(ck, prog, Kind::PROGRAM_CONST) {
            return Ok(os);
        }
        let pt = type_of(ck, prog)?;
        let mut pandt = vec![pt];
        pandt.extend(prog_def);
        let vars = ck.get_variables(&pandt);
        let p = ck.show(prog);
        let what = if prog_def.is_none() {
            "fwd-decl: "
        } else {
            "program: "
        };
        let _ = write!(os, "; {what}{p}\n(program {p} (");
        self.print_param_list(ck, &vars, &mut os, false)?;
        os.push_str(")\n  :signature (");
        let types = ck.store.children(pt).to_vec();
        let Some((&ret, args)) = types.split_last() else {
            return Err(malformed("a program type without a return type"));
        };
        for (i, &arg) in args.iter().enumerate() {
            if i > 0 {
                os.push(' ');
            }
            os.push_str(&self.print_term(ck, arg)?);
        }
        let _ = writeln!(os, ") {}", self.print_term(ck, ret)?);
        if let Some(pdef) = prog_def {
            os.push_str("  (\n");
            for c in ck.store.children(pdef).to_vec() {
                let (pat, body) = (child(ck, c, 0)?, child(ck, c, 1)?);
                let _ = writeln!(
                    os,
                    "  ({} {})",
                    self.print_term(ck, pat)?,
                    self.print_term(ck, body)?
                );
            }
            os.push_str("  )\n");
        }
        os.push_str(")\n");
        Ok(os)
    }

    /// The declaration of the constant `e` as text, with its cases of
    /// `$eo_nil`, `$eo_typeof` and so on added to their own lists.
    fn finalize_declaration(&mut self, ck: &mut Checker, e: Term) -> Result<String> {
        let mut os = String::new();
        if self.is_excluded(ck, e, Kind::CONST) || !self.decl_processed.insert(e) {
            return Ok(os);
        }
        let (cattr, mut cattr_cons) = self
            .attr_decl
            .get(&e)
            .copied()
            .unwrap_or((Attr::None, None));
        // The name is settled before any case is written, so that all of
        // them use the same overload suffix.
        let cname = self.print_name(ck, e)?;
        if matches!(
            cattr,
            Attr::Datatype | Attr::DatatypeConstructor | Attr::AmbDatatypeConstructor
        ) {
            self.finalize_datatype(ck, e, cattr, cattr_cons)?;
        } else if cattr == Attr::Binder {
            self.finalize_binder(ck, e)?;
        }
        let is_amb = matches!(cattr, Attr::Amb | Attr::AmbDatatypeConstructor);
        let has_opaque_arg = cattr == Attr::Opaque || is_amb;
        // eo::List and its constructors
        if cname.starts_with("eo::") {
            return Ok(os);
        }
        let cto = type_of(ck, e)?;
        // An ambiguous constant is not ambiguous once desugared, so it is
        // printed without `as`.
        if is_amb {
            let cnamb = ck.mk_symbol(SymbolKind::Const, &cname, cto);
            self.overload_san_visited.insert(e, cnamb);
        }
        let mut ct = cto;
        let mut arg_types = Vec::new();
        let ret_type;
        let mut visited: HashMap<Term, bool> = HashMap::new();
        let mut params: Vec<Term> = Vec::new();
        let mut opaque_args = String::new();
        let mut parser_index_arity = 0usize;
        if ck.store.kind(ct) == Kind::FUNCTION_TYPE {
            if cattr == Attr::Opaque {
                let novars = (ck.attribute_term(e))
                    .and_then(|anum| match ck.store.lit(anum) {
                        Some(Lit::Numeral(n)) if n.fits_u32() => Some(n.to_u32() as usize),
                        _ => None,
                    })
                    .ok_or_else(|| malformed("an opaque symbol without its argument count"))?;
                parser_index_arity = novars;
                for i in 0..novars {
                    let cti = child(ck, ct, i)?;
                    let v = if ck.store.kind(cti) == Kind::QUOTE_TYPE {
                        child(ck, cti, 0)?
                    } else {
                        // an ordinary argument: its parameter comes back
                        ck.mk_symbol(SymbolKind::Param, &format!("$eo_ov_{i}"), cti)
                    };
                    self.print_param_list_shared(
                        ck,
                        &[v],
                        &mut opaque_args,
                        &mut params,
                        &mut visited,
                        true,
                        true,
                    )?;
                }
                ct = child(ck, ct, novars)?;
            }
            (arg_types, ret_type) = ck.get_function_type(ct);
        } else {
            ret_type = ct;
        }
        let _ = write!(os, "; declare: {}\n(declare-", ck.show(e));
        let vars = ck.get_variables(&[ct]);
        if !vars.is_empty() || cattr == Attr::Opaque {
            let _ = write!(os, "parameterized-const {cname} ({opaque_args}");
            let mut pcount = 0;
            for (i, &at) in arg_types.iter().enumerate() {
                if ck.store.kind(at) == Kind::QUOTE_TYPE {
                    let v = child(ck, at, 0)?;
                    if ck.store.kind(v) == Kind::PARAM {
                        let is_opaque = is_amb && i == 0;
                        self.print_param_list_shared(
                            ck,
                            &[v],
                            &mut os,
                            &mut params,
                            &mut visited,
                            true,
                            is_opaque,
                        )?;
                    }
                } else {
                    // an ordinary type
                    pcount += 1;
                    let v = ck.mk_symbol(SymbolKind::Param, &format!("$eo_x_{pcount}"), at);
                    self.print_param_list_shared(
                        ck,
                        &[v],
                        &mut os,
                        &mut params,
                        &mut visited,
                        true,
                        false,
                    )?;
                }
            }
            let _ = write!(os, ") {}", self.print_term(ck, ret_type)?);
        } else {
            let _ = write!(os, "const {cname} {}", self.print_term(ck, ct)?);
        }
        os.push_str(")\n");

        // The syntax the attributes gave the symbol, for the Lean backend:
        // the declarations printed here no longer carry them.
        let parser_surface = ck.show(e);
        let mut parser_term_arity = arg_types.len();
        if is_amb && parser_term_arity > 0 {
            // the first argument of an ambiguous constant becomes an index
            parser_index_arity += 1;
            parser_term_arity -= 1;
        }
        if parser_index_arity > 0 {
            self.index_arities.insert(parser_index_arity);
        }
        let mut parser_connector = String::from("-");
        if let Some(cons) = cattr_cons {
            if matches!(cattr, Attr::Chainable | Attr::Pairwise | Attr::ArgList) {
                parser_connector = ck.show(cons);
            } else if cattr == Attr::Binder {
                parser_connector = self.print_term(ck, cons)?;
            }
        } else if matches!(
            cattr,
            Attr::Chainable | Attr::Pairwise | Attr::ArgList | Attr::Binder
        ) {
            // the C++ prints its null expression
            parser_connector = ck.show(ck.store.mk_null());
        }
        let _ = writeln!(
            self.lean_parser_metadata,
            "(echo \"lean-parser-op {parser_surface} {cname} {parser_index_arity} \
             {parser_term_arity} {} {parser_connector}\")",
            lean_parser_attr_name(cattr)
        );
        // $eo_nil and $eo_is_list_nil
        if cattr.is_list_nil() {
            let Some(mut nil) = cattr_cons.take() else {
                return Err(malformed("a nil attribute without its nil"));
            };
            let _ = write!(self.eo_nil, "  (($eo_nil {cname} T) ");
            let _ = write!(self.eo_is_list_nil, "  (($eo_is_list_nil {cname} ");
            if !ck.get_variables(&[nil]).is_empty() {
                // The nil depends on the type: it is computed by a program
                // from the type of the first argument.
                nil = child(ck, nil, 1)?;
                let pname = format!("$eo_nil_{}", self.print_name(ck, e)?);
                let tp_tmp = self.std.allocate_type_variable(ck);
                let qtt = ck.mk_expr(Kind::QUOTE_TYPE, &[tp_tmp]);
                let prog_type = ck.mk_program_type(&[qtt], tp_tmp);
                let prog = ck.mk_symbol(SymbolKind::ProgramConst, &pname, prog_type);
                let ct0 = child(ck, ct, 0)?;
                let prog_pat = ck.mk_expr(Kind::APPLY, &[prog, ct0]);
                let prog_pair = ck.mk_pair(prog_pat, nil);
                let prog_def = ck.mk_expr(Kind::PROGRAM, &[prog_pair]);
                let text = self.finalize_program(ck, prog, Some(prog_def))?;
                self.eo_nil_nground.push_str(&text);
                let _ = write!(self.eo_nil, "({pname} T)");
                // Whether a term is this nil is said by a program the
                // signature's semantics give; this is the call to it.
                let _ = writeln!(self.eo_is_list_nil, "nil) ($eo_is_list_nil_{cname} nil))");
            } else {
                let printed = self.print_term(ck, nil)?;
                let _ = writeln!(self.eo_is_list_nil, "{printed}) true)");
                self.eo_nil.push_str(&printed);
            }
            self.eo_nil.push_str(")\n");
        }
        // $eo_typeof
        ct = cto;
        let _ = writeln!(self.eo_typeof, "  ; type-rule: {}", ck.show(e));
        if !ck.store.is_ground(ct) || ck.store.kind(ct) == Kind::FUNCTION_TYPE {
            // The pattern is the operator applied to a variable for each
            // argument, down to where its type is no longer a function.
            let mut pattern = e;
            let mut sslc = String::new();
            let mut sslc_end = String::new();
            let mut ng_args = 0usize;
            let mut ssngarg = String::new();
            let mut ngscope: Vec<Term> = Vec::new();
            let mut arg_count = 0usize;
            while ck.store.kind(ct) == Kind::FUNCTION_TYPE {
                let mut args = vec![pattern];
                let types = ck.store.children(ct).to_vec();
                let Some((&ret, arg_tys)) = types.split_last() else {
                    return Err(malformed("a function type without a return type"));
                };
                for &arg_ty in arg_tys {
                    let mut cta = arg_ty;
                    arg_count += 1;
                    let ssx = format!("$eo_x{arg_count}");
                    let arg;
                    if ck.store.kind(cta) == Kind::QUOTE_TYPE {
                        cta = child(ck, cta, 0)?;
                        // the type is checked as well
                        let tcta = type_of(ck, cta)?;
                        ngscope.push(tcta);
                        let _ = write!(ssngarg, " ($eo_typeof {ssx})");
                        arg = ck.mk_symbol(SymbolKind::Param, &ssx, tcta);
                        if ck.store.kind(cta) == Kind::PARAM {
                            let _ =
                                write!(sslc, "(eo::define (({} {})) ", ck.show(cta), ck.show(arg));
                            sslc_end.push(')');
                        }
                        let _ = write!(ssngarg, " {}", ck.show(arg));
                    } else {
                        arg = ck.mk_symbol(SymbolKind::Param, &ssx, cta);
                        if ck.store.is_ground(cta) {
                            let _ = write!(
                                sslc,
                                "($eo_requires_true ($eo_eq ($eo_typeof {}) {}) ",
                                ck.show(arg),
                                self.print_term(ck, cta)?
                            );
                            sslc_end.push(')');
                        } else if ck.store.kind(cta) == Kind::PARAM {
                            let _ = write!(
                                sslc,
                                "(eo::define (({} ($eo_typeof {}))) ",
                                ck.show(cta),
                                ck.show(arg)
                            );
                            sslc_end.push(')');
                        }
                        let _ = write!(ssngarg, " ($eo_typeof {})", ck.show(arg));
                    }
                    ngscope.push(cta);
                    ng_args += 1;
                    args.push(arg);
                }
                let ak = if has_opaque_arg && pattern == e {
                    Kind::APPLY_OPAQUE
                } else {
                    Kind::APPLY
                };
                pattern = ck.store.mk(ak, &args);
                ct = ret;
            }
            let printed = self.print_term(ck, pattern)?;
            let _ = write!(self.eo_typeof, "  (($eo_typeof {printed}) ");
            if ng_args > 0 {
                // Operators whose types differ only in variable names share
                // one program for the type of their applications.
                let canon_t = self.mk_canonize(ck, cto)?;
                let pname = match self.canon_type_prog_name.get(&canon_t) {
                    Some(pname) => pname.clone(),
                    None => {
                        let pname = format!("$eo_typeof_{}", self.print_name(ck, e)?);
                        let mut arg_types = Vec::with_capacity(ngscope.len());
                        for &t in &ngscope {
                            arg_types.push(type_of(ck, t)?);
                        }
                        let ret_type = ck.mk_type();
                        let prog_type = ck.mk_program_type(&arg_types, ret_type);
                        let prog = ck.mk_symbol(SymbolKind::ProgramConst, &pname, prog_type);
                        let mut pchildren = vec![prog];
                        pchildren.extend_from_slice(&ngscope);
                        let prog_pat = ck.mk_expr(Kind::APPLY, &pchildren);
                        let prog_pair = ck.mk_pair(prog_pat, ct);
                        let prog_def = ck.mk_expr(Kind::PROGRAM, &[prog_pair]);
                        let text = self.finalize_program(ck, prog, Some(prog_def))?;
                        self.eo_typeof_nground.push_str(&text);
                        self.canon_type_prog_name.insert(canon_t, pname.clone());
                        pname
                    }
                };
                let _ = write!(self.eo_typeof, "({pname}{ssngarg})");
            } else {
                let printed = self.print_term(ck, ct)?;
                let _ = write!(self.eo_typeof, "{sslc}{printed}{sslc_end}");
            }
            self.eo_typeof.push_str(")\n");
        } else {
            let printed = self.print_term(ck, ct)?;
            let _ = writeln!(self.eo_typeof, "  (($eo_typeof {cname}) {printed})");
        }
        Ok(os)
    }

    /// The definition `name` as a parse definition, if it is the last one
    /// of that name.
    fn finalize_definition(&mut self, ck: &mut Checker, name: &str, t: Term) -> Result<()> {
        if self.define_last.get(name) != Some(&t) {
            return Ok(());
        }
        let is_macro = ck.store.kind(t) == Kind::LAMBDA;
        let body = if is_macro { child(ck, t, 1)? } else { t };
        let vars = if is_macro {
            ck.store.children(child(ck, t, 0)?).to_vec()
        } else {
            Vec::new()
        };
        // A body that mentions an omitted declaration cannot be kept.
        for k in [Kind::CONST, Kind::PROGRAM_CONST] {
            for sub in subterms_of_kind(ck, k, body) {
                if self.is_excluded(ck, sub, k) {
                    return Ok(());
                }
            }
        }
        let mut os = format!("; define: {name}\n(define {} (", mk_parse_def_name(name));
        // The explicit parameters first, in the order the definition takes
        // them; then those of their types and the body's other variables.
        let (mut params, mut visited) = (Vec::new(), HashMap::new());
        for &v in &vars {
            self.get_param_list(ck, &[v], &mut params, &mut visited)?;
        }
        for v in ck.get_variables(&[body]) {
            self.get_param_list(ck, &[v], &mut params, &mut visited)?;
        }
        self.finalize_param_list(ck, &mut os, &params, true, &vars, false, 0)?;
        let _ = writeln!(os, ")\n  {})", self.print_term(ck, body)?);
        self.defs.push_str(&os);
        Ok(())
    }

    /// The checker's case for the rule, and its verification condition if
    /// those are wanted.
    fn finalize_rule(&mut self, ck: &mut Checker, e: Term) -> Result<()> {
        if self.is_excluded(ck, e, Kind::PROOF_RULE) || ck.is_proof_rule_sorry(e) {
            return Ok(());
        }
        self.dchecker.finalize_rule(ck, e)?;
        let tuple_val = ck
            .attribute_term(e)
            .ok_or_else(|| malformed("a proof rule without its definition"))?;
        let rprog = child(ck, tuple_val, 3)?;
        let ename = ck.show(e);
        if !self.gen_vcs {
            // a rule without arguments or premises: keep its definition
            if ck.store.kind(rprog) != Kind::PROGRAM_CONST {
                let printed = self.print_term(ck, rprog)?;
                let _ = writeln!(self.eo_vc, "(define $eo_prog_{ename} () {printed})");
            }
            let _ = writeln!(
                self.eo_vc,
                "(echo \"eo-desugar $eo_prog_{ename} :deps eo-desugar-deps \")"
            );
            return Ok(());
        }

        let prog_case = if ck.store.kind(rprog) == Kind::PROGRAM_CONST {
            let def = ck
                .get_program(rprog)
                .ok_or_else(|| malformed("a rule's program without cases"))?;
            let first = child(ck, def, 0)?;
            child(ck, first, 0)?
        } else {
            rprog
        };
        let (t_true, bool_type) = {
            let s = self.syms()?;
            (s.t_true, s.bool_type)
        };
        // A stand-in for the model, which `$smt_Model` in the template
        // gives its meaning when the output is read.
        let ty = ck.mk_type();
        let model_var_type = ck.mk_symbol(SymbolKind::Const, "$smt_Model", ty);
        let model_var = ck.mk_symbol(SymbolKind::Param, "$eoM", model_var_type);
        // the conclusion is not satisfied, and each premise is
        let mut unsound = self.mk_requires_model_sat(ck, model_var, false, prog_case, t_true)?;
        for &c in ck.store.children(prog_case).to_vec().iter().rev() {
            if ck.store.kind(c) == Kind::PROOF {
                let proven = child(ck, c, 0)?;
                unsound = self.mk_requires_model_sat(ck, model_var, true, proven, unsound)?;
            }
        }
        let uvars = ck.get_variables(&[unsound]);
        let mut uarg_types = Vec::with_capacity(uvars.len());
        for &v in &uvars {
            uarg_types.push(type_of(ck, v)?);
        }
        if uarg_types.is_empty() {
            return Err(malformed("a verification condition without variables"));
        }
        let prog_type = ck.mk_program_type(&uarg_types, bool_type);
        let prog = ck.mk_symbol(
            SymbolKind::ProgramConst,
            &format!("$eovc_{ename}"),
            prog_type,
        );
        let mut vcp_children = vec![prog];
        vcp_children.extend_from_slice(&uvars);
        let prog_pat = ck.mk_expr(Kind::APPLY, &vcp_children);
        let prog_pair = ck.mk_pair(prog_pat, unsound);
        let prog_def = ck.mk_expr(Kind::PROGRAM, &[prog_pair]);
        let text = self.finalize_program(ck, prog, Some(prog_def))?;
        self.eo_vc.push_str(&text);
        // the tags are replaced by whoever uses the condition
        let _ = writeln!(
            self.eo_vc,
            "(echo \"eo-desugar-vc $eovc_{ename} :deps eo-desugar-vc-deps \")"
        );
        Ok(())
    }

    /// `(eo::requires (<sat> m test) true ret)`, where `<sat>` says that
    /// the model satisfies the formula (`tgt`) or does not.
    fn mk_requires_model_sat(
        &mut self,
        ck: &mut Checker,
        m: Term,
        tgt: bool,
        test: Term,
        ret: Term,
    ) -> Result<Term> {
        let s = self.syms()?;
        let sat = if tgt { s.model_sat } else { s.model_unsat };
        let t1 = ck.mk_expr(Kind::APPLY, &[sat, m, test]);
        let t_true = ck.mk_bool(true);
        Ok(ck.mk_expr(
            Kind::Eval(pathos_term::EvalOp::Requires),
            &[t1, t_true, ret],
        ))
    }

    /// The reflection case of a datatype (its constructors) or of a
    /// constructor (its selectors).
    fn finalize_datatype(
        &mut self,
        ck: &mut Checker,
        e: Term,
        a: Attr,
        attr_cons: Option<Term>,
    ) -> Result<()> {
        let attr_cons = attr_cons.ok_or_else(|| malformed("a datatype without constructors"))?;
        let mut td = type_of(ck, e)?;
        let name = if a == Attr::Datatype {
            "constructors"
        } else {
            "selectors"
        };
        let mut os = format!("  (($eo_dt_{name}_main ");
        if a == Attr::Datatype && ck.store.kind(td) == Kind::FUNCTION_TYPE {
            // a parametric datatype
            let _ = write!(os, "({}", self.print_name(ck, e)?);
            let mut i = 1;
            let mut arg_list = String::new();
            while ck.store.kind(td) == Kind::FUNCTION_TYPE {
                if i > self.eo_dt_cons_param_count {
                    let _ = write!(self.eo_dt_cons_param, " (W{i} Type)");
                    self.eo_dt_cons_param_count += 1;
                }
                let _ = write!(arg_list, " W{i}");
                td = child(ck, td, 1)?;
                i += 1;
            }
            let _ = write!(os, "{arg_list}))");
            // The constructors that are ambiguous take the parameters.
            let mut ac = attr_cons;
            let mut os_end = String::new();
            while ck.store.kind(ac) == Kind::APPLY {
                os.push_str(" (_ ($eo_List_cons ");
                let head = child(ck, ac, 0)?;
                let cc = child(ck, head, 1)?;
                let cname = self.print_name(ck, cc)?;
                if self.get_attribute(cc) == Attr::AmbDatatypeConstructor {
                    let _ = write!(os, "({cname}{arg_list})");
                } else {
                    os.push_str(&cname);
                }
                os.push(')');
                os_end.push(')');
                ac = child(ck, ac, 1)?;
            }
            let _ = writeln!(os, " {}{os_end})", self.print_term(ck, ac)?);
        } else {
            let _ = writeln!(
                os,
                "{}) {})",
                self.print_name(ck, e)?,
                self.print_term(ck, attr_cons)?
            );
        }
        if a == Attr::Datatype {
            self.eo_dt_cons.push_str(&os);
        } else {
            self.eo_dt_sel.push_str(&os);
        }
        Ok(())
    }

    /// The case of `$eo_is_closed_rec` for the binder `e`.
    fn finalize_binder(&mut self, ck: &mut Checker, e: Term) -> Result<()> {
        let name = self.print_name(ck, e)?;
        let _ = writeln!(
            self.eo_is_closed,
            "  (($eo_is_closed_rec ({name} vs x) env) ($eo_is_closed_rec x (eo::list_concat \
             $eo_List_cons vs env)))"
        );
        Ok(())
    }

    /// The `$emb_UOp<n>` constructors for the index arities in use.
    fn print_uop_decls(&self) -> String {
        let mut decls = String::new();
        for (pos, &n) in self.index_arities.iter().enumerate() {
            if pos > 0 {
                decls.push('\n');
            }
            let _ = write!(
                decls,
                "(declare-parameterized-const $emb_UOp{n}\n  ((u ($native_type_0 \"UserOp{n}\") \
                 :opaque)"
            );
            for i in 1..=n {
                let _ = write!(decls, " (t{i} $eo_Term :opaque)");
            }
            let _ = write!(
                decls,
                ") $eo_Term)\n(define $eot_uop{n}\n  ((u ($native_type_0 \"UserOp{n}\"))"
            );
            for i in 1..=n {
                let _ = write!(decls, " (t{i} $eo_Term)");
            }
            let _ = write!(decls, ")\n  ($emb_UOp{n} u");
            for i in 1..=n {
                let _ = write!(decls, " t{i}");
            }
            decls.push_str("))");
        }
        decls
    }

    /// The `$eo_is_closed_rec` cases for the index arities in use.
    fn print_is_closed_uop_cases(&self) -> String {
        let mut cases = String::new();
        for (pos, &n) in self.index_arities.iter().enumerate() {
            if pos > 0 {
                cases.push('\n');
            }
            let _ = write!(cases, "  (($eo_is_closed_rec ($eot_uop{n} u");
            let mut body = String::new();
            for i in 1..=n {
                let arg = if i == 1 {
                    "x".to_string()
                } else {
                    format!("x{i}")
                };
                let _ = write!(cases, " {arg}");
                let ic = format!("($eo_is_closed_rec {arg} env)");
                body = if i == 1 {
                    ic
                } else {
                    format!("(eo::and {body} {ic})")
                };
            }
            cases.push_str(") env)");
            cases.push_str(if n == 1 { " " } else { "\n    " });
            let _ = write!(cases, "{body})");
        }
        cases
    }

    /// The ground term the type rule of a kind is instantiated with when it
    /// uses `eo::self`.
    fn ground_term_for_literal_kind(ck: &mut Checker, k: LitKind) -> Option<Term> {
        let lit = match k {
            LitKind::Numeral => Lit::Numeral(Integer::zero()),
            LitKind::Rational => Lit::Rational(Rational::parse("0/1")?),
            LitKind::Binary => Lit::Binary(BitVec::parse("0", 2)?),
            LitKind::String => Lit::String(EoString::default()),
            _ => return None,
        };
        Some(ck.store.mk_lit(lit))
    }

    fn literal_type_rule(&mut self, ck: &mut Checker, k: LitKind, t: Term) -> Result<()> {
        self.lt_kind_processed.insert(k);
        let eoss = match k {
            LitKind::Numeral => "Numeral",
            LitKind::Rational => "Rational",
            LitKind::Binary => "Binary",
            LitKind::String => "String",
            LitKind::Decimal | LitKind::Hexadecimal => return Ok(()),
            LitKind::Boolean => {
                return Err(Error::fatal(format!(
                    "Unknown literal type rule{}\n",
                    Kind::Lit(k)
                )));
            }
        };
        // the symbols of the type are declared ahead of it
        for s in subterms_of_kind(ck, Kind::CONST, t) {
            if !self.lt_decl_processed.insert(s) {
                continue;
            }
            let text = self.finalize_declaration(ck, s)?;
            self.lit_type_decl.push_str(&text);
        }
        let kind = Kind::Lit(k);
        let printed = self.print_term(ck, t)?;
        let _ = writeln!(
            self.lit_type_decl,
            "; type-rules: {kind}\n(declare-consts {} {printed})",
            literal_kind_to_string(k)?
        );
        // `$eo_lit_type_X` is always a program, and `$eo_X` always a ground
        // type: a rule that uses eo::self is instantiated with a ground
        // literal for it.
        let (mut ltinst, mut ltg) = (t, t);
        if ck.store.is_ground(t) {
            let _ = writeln!(self.lit_type_decl, "; type-rules: {kind}");
        } else {
            let any = ck.mk_any();
            let ty = ck.mk_symbol(SymbolKind::Const, "t", any);
            let gt = Self::ground_term_for_literal_kind(ck, k);
            let rule = |ck: &mut Checker, self_term| {
                ck.get_literal_type_rule(k, self_term, None)
                    .ok_or_else(|| malformed("a literal kind without its type rule"))
            };
            ltg = rule(ck, gt)?;
            ltinst = rule(ck, Some(ty))?;
            let _ = writeln!(self.lit_type_decl, "; (approx) type-rules: {kind}");
        }
        let printed = self.print_term(ck, ltg)?;
        let _ = writeln!(self.lit_type_decl, "(define $eo_{eoss} () {printed})");
        let printed = self.print_term(ck, ltinst)?;
        let _ = write!(
            self.lit_type_prog,
            "(program $eo_lit_type_{eoss} ((T Type) (t T))\n  :signature (T) Type\n  (\n  \
             (($eo_lit_type_{eoss} t) {printed})\n  )\n)\n"
        );
        Ok(())
    }
}

impl DesugarChecker {
    /// The declaration of the rule in the embedding and the checker's case
    /// that invokes its program.
    fn finalize_rule(&mut self, ck: &mut Checker, v: Term) -> Result<()> {
        let mut invoke_pat = String::new();
        let mut invoke_ret = String::new();
        let tuple_val = ck
            .attribute_term(v)
            .ok_or_else(|| malformed("a proof rule without its definition"))?;
        let pl_cons = Some(child(ck, tuple_val, 0)?).filter(|&c| ck.store.kind(c) != Kind::Any);
        let is_assume = child(ck, tuple_val, 1)? == ck.mk_true();
        let rprog = child(ck, tuple_val, 3)?;
        let rprog_type = type_of(ck, rprog)?;
        let (mut nargs, mut npremises) = (0usize, 0usize);
        if ck.store.kind(rprog_type) == Kind::PROGRAM_TYPE {
            let pf_type = ck.mk_proof_type();
            let types = ck.store.children(rprog_type);
            for &arg_type in &types[..types.len().saturating_sub(1)] {
                if arg_type == pf_type {
                    npremises += 1;
                } else {
                    nargs += 1;
                }
            }
        }
        // the assumption is an ordinary argument
        if is_assume {
            nargs = nargs.saturating_sub(1);
        }
        let vname = ck.show(v);
        if nargs > 10 {
            return Err(Error::fatal(format!(
                "DesugarChecker: proof rule {vname} has {nargs} arguments; at most 10 are \
                 supported"
            )));
        }
        let mut inv_pat_args = String::from("$eot_aln");
        for i in 1..=nargs {
            let _ = write!(invoke_ret, " a{i}");
            inv_pat_args = format!("($eot_alc a{} {inv_pat_args})", nargs - i + 1);
        }
        let _ = write!(invoke_pat, " {inv_pat_args}");
        if is_assume {
            invoke_pat.push_str(" A");
            invoke_ret.push_str(" A");
        }
        if let Some(pl_cons) = pl_cons {
            // The premises are gathered into a list that ends in the
            // operator's nil, so the operator must have one.
            let pl = ck.show(pl_cons);
            if !ck.attribute_kind(pl_cons).is_list_nil() {
                return Err(Error::fatal(format!(
                    "DesugarChecker: proof rule {vname} gathers its premises with {pl}, which \
                     declares no nil; mark {pl} :right-assoc-nil or :left-assoc-nil, or give \
                     the rule its premises individually"
                )));
            }
            invoke_pat.push_str(" premises");
            let _ = write!(
                invoke_ret,
                " ($eo_pf ($eo_mk_premise_list {pl} premises S))"
            );
        } else {
            if npremises > 8 {
                return Err(Error::fatal(format!(
                    "DesugarChecker: proof rule {vname} has {npremises} premises; at most 8 \
                     are supported"
                )));
            }
            let mut inv_pat_premises = String::from("$eot_iln");
            for i in 1..=npremises {
                let _ = write!(invoke_ret, " ($eo_pf ($eo_state_proven_nth S n{i}))");
                inv_pat_premises = format!("($eot_ilc n{} {inv_pat_premises})", npremises - i + 1);
            }
            let _ = write!(invoke_pat, " {inv_pat_premises}");
        }
        let emb_name = replace_all(&vname, "-", "_");
        let _ = writeln!(
            self.rules,
            "(echo \"lean-parser-rule {vname} {emb_name}\")\n(declare-const $emb_r.{emb_name} \
             $eo_Rule)"
        );
        let rout = if is_assume {
            &mut self.rule_invokes_pop
        } else {
            &mut self.rule_invokes
        };
        let _ = write!(
            rout,
            "  (($eo_cmd_step_{}proven S $emb_r.{emb_name}{invoke_pat}) ",
            if is_assume { "pop_" } else { "" }
        );
        let rprog_shown = ck.show(rprog);
        if invoke_ret.is_empty() {
            let _ = writeln!(rout, "{rprog_shown})");
        } else {
            let _ = writeln!(rout, "({rprog_shown}{invoke_ret}))");
        }
        Ok(())
    }

    /// The checker: its template with the rules' cases put in.
    fn output(&self, std: &StdPlugin) -> Result<String> {
        let template_path = "plugins/desugar/eo_desugar_checker.eo";
        let Some(template) = read_text(&std.resource_path(template_path)) else {
            return Err(Error::fatal(format!(
                "DesugarChecker: failed to open resource {template_path}"
            )));
        };
        let text = template
            .replacen("$EO_RULE_DEFS$", &self.rules, 1)
            .replacen("$EO_INVOKE$", &self.rule_invokes, 1)
            .replacen("$EO_INVOKE_POP$", &self.rule_invokes_pop, 1);
        Ok(format!(
            ";; ------------ checker\n{text};; ------------ checker end\n"
        ))
    }
}

impl Plugin for Desugar {
    fn initialize(&mut self, st: &mut State) -> Result<()> {
        let ck = &mut st.ck;
        // The builtin list and proof symbols are printed under `$eo_` names.
        let ty = ck.mk_type();
        let list_nil = ck.mk_list_nil();
        let lnt = type_of(ck, list_nil)?;
        let s = ck.mk_symbol(SymbolKind::Const, "$eo_List_nil", lnt);
        self.overload_san_visited.insert(list_nil, s);
        let list_cons = ck.mk_list_cons();
        let lct = type_of(ck, list_cons)?;
        let s = ck.mk_symbol(SymbolKind::Const, "$eo_List_cons", lct);
        self.overload_san_visited.insert(list_cons, s);
        let s = ck.mk_symbol(SymbolKind::Const, "$eo_List", ty);
        self.overload_san_visited.insert(ck.mk_list_type(), s);
        let s = ck.mk_symbol(SymbolKind::Const, "$eo_Proof", ty);
        self.overload_san_visited.insert(ck.mk_proof_type(), s);

        let bool_type = ck.mk_bool_type();
        let any_t = self.std.allocate_type_variable(ck);
        let any_t2 = self.std.allocate_type_variable(ck);
        let model_sat_type = ck.mk_program_type(&[any_t, bool_type], bool_type);
        let model_sat = ck.mk_symbol(SymbolKind::ProgramConst, "$eo_model_sat", model_sat_type);
        let model_unsat = ck.mk_symbol(SymbolKind::ProgramConst, "$eo_model_unsat", model_sat_type);
        let requires_eq_type = ck.mk_program_type(&[any_t, any_t, any_t2], any_t2);
        ck.mk_symbol(
            SymbolKind::ProgramConst,
            "$eo_requires_eq",
            requires_eq_type,
        );
        let proof_type = ck.mk_proof_type();
        let pf_type = ck.mk_function_type(&[bool_type], proof_type);
        let pf = ck.mk_symbol(SymbolKind::Const, "$eo_pf", pf_type);
        self.syms = Some(Syms {
            bool_type,
            t_true: ck.mk_true(),
            model_sat,
            model_unsat,
            pf,
        });
        Ok(())
    }

    fn define(&mut self, st: &mut State, name: &str, e: Term) -> Result<()> {
        // A name that begins with `$` is a helper of the signature; a proof
        // never mentions it, so it is not kept.
        if name.starts_with('$') {
            return Ok(());
        }
        let any = st.ck.mk_any();
        let tmp = st.ck.mk_symbol(SymbolKind::Const, name, any);
        self.decl_seen.push(Decl::Define(tmp, e));
        self.define_last.insert(name.to_string(), e);
        Ok(())
    }

    fn bind(&mut self, st: &mut State, _name: &str, e: Term) -> Result<()> {
        match st.ck.store.kind(e) {
            Kind::CONST => self.decl_seen.push(Decl::Const(e)),
            Kind::PROOF_RULE => self.decl_seen.push(Decl::Rule(e)),
            _ => {}
        }
        Ok(())
    }

    fn mark_constructor_kind(
        &mut self,
        _st: &mut State,
        v: Term,
        a: Attr,
        cons: Option<Term>,
    ) -> Result<()> {
        self.attr_decl.insert(v, (a, cons));
        Ok(())
    }

    fn define_program(&mut self, _st: &mut State, v: Term, prog: Option<Term>) -> Result<()> {
        self.decl_seen.push(Decl::Program(v, prog));
        Ok(())
    }

    fn set_literal_type_rule(&mut self, st: &mut State, k: LitKind, t: Term) -> Result<()> {
        self.literal_type_rule(&mut st.ck, k, t)
    }

    fn echo(&mut self, _st: &mut State, msg: &str) -> Result<bool> {
        let Some(rest) = msg.strip_prefix("eoc-exclude ") else {
            return Ok(true);
        };
        let is_space = |c: char| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r');
        let words: Vec<&str> = rest.split(is_space).filter(|w| !w.is_empty()).collect();
        let &[kind, name] = words.as_slice() else {
            return Err(Error::fatal(format!(
                "Malformed exclusion directive \"{msg}\"; expected \"eoc-exclude \
                 <rule|method|symbol> <name>\""
            )));
        };
        let set = match kind {
            "rule" => &mut self.excluded_rules,
            "method" => &mut self.excluded_methods,
            "symbol" => &mut self.excluded_symbols,
            _ => {
                return Err(Error::fatal(format!(
                    "Unknown exclusion kind \"{kind}\"; expected rule, method, or symbol"
                )));
            }
        };
        set.insert(name.to_string());
        Ok(false)
    }

    fn finalize(&mut self, st: &mut State) -> Result<()> {
        let ck = &mut st.ck;
        // every literal kind gets a type
        let mut builtin_type = None;
        for k in [
            LitKind::Numeral,
            LitKind::Rational,
            LitKind::Binary,
            LitKind::String,
        ] {
            if self.lt_kind_processed.contains(&k) {
                continue;
            }
            let t = match builtin_type {
                Some(t) => t,
                None => {
                    let ty = ck.mk_type();
                    let t = ck.mk_symbol(SymbolKind::Const, "$eo_Builtin_Type", ty);
                    builtin_type = Some(t);
                    t
                }
            };
            self.literal_type_rule(ck, k, t)?;
        }

        for decl in std::mem::take(&mut self.decl_seen) {
            match decl {
                Decl::Define(name, t) => {
                    let name = ck.show(name);
                    self.finalize_definition(ck, &name, t)?;
                }
                Decl::Const(e) => {
                    let text = self.finalize_declaration(ck, e)?;
                    self.defs.push_str(&text);
                }
                Decl::Rule(e) => self.finalize_rule(ck, e)?,
                Decl::Program(v, prog) => {
                    let text = self.finalize_program(ck, v, prog)?;
                    self.defs.push_str(&text);
                }
            }
        }

        let template_path = "plugins/desugar/eo_desugar.eo";
        let Some(mut final_eo) = read_text(&self.std.resource_path(template_path)) else {
            return Err(Error::fatal(format!(
                "Desugar: failed to open resource {template_path}"
            )));
        };
        let checker = if self.gen_checker {
            self.dchecker.output(&self.std)?
        } else {
            String::new()
        };
        let is_closed_uop_cases = self.print_is_closed_uop_cases();
        for (tag, text) in [
            ("$EO_LITERAL_TYPE_DECL$", &self.lit_type_decl),
            ("$EO_LIT_TYPEOF_DEFS$", &self.lit_type_prog),
            ("$EO_DEFS$", &self.defs),
            ("$EO_IS_LIST_NIL_CASES$", &self.eo_is_list_nil),
            ("$EO_NIL_CASES$", &self.eo_nil),
            ("$EO_NIL_NGROUND_DEFS$", &self.eo_nil_nground),
            ("$EO_LEAN_PARSER_METADATA$", &self.lean_parser_metadata),
            ("$EO_TYPEOF_CASES$", &self.eo_typeof),
            ("$EO_IS_CLOSED_CASES$", &self.eo_is_closed),
            ("$EO_IS_CLOSED_UOP_CASES$", &is_closed_uop_cases),
            ("$EO_TYPEOF_NGROUND_DEFS$", &self.eo_typeof_nground),
            ("$EO_DT_CONSTRUCTORS_PARAM$", &self.eo_dt_cons_param),
            ("$EO_DT_CONSTRUCTORS_CASES$", &self.eo_dt_cons),
            ("$EO_DT_SELECTORS_CASES$", &self.eo_dt_sel),
            ("$EO_CHECKER$", &checker),
            ("$EO_VC$", &self.eo_vc),
        ] {
            final_eo = final_eo.replacen(tag, text, 1);
        }
        // The files the output includes go next to it. The native embedding
        // is the one that depends on the signature: on the index arities.
        self.std.emit_resource_file(
            ck,
            "plugins/desugar/eo_desugar_native.eo",
            "plugins/desugar/eo_desugar_native.eo",
            &[("$EO_UOP_DECLS$".to_string(), self.print_uop_decls())],
            false,
        )?;
        self.std
            .copy_resource_to_output("plugins/desugar/native_embed.eo")?;
        let out_path = self.std.output_path("plugins/desugar/eo_desugar_gen.eo")?;
        st.print_line(&format!("Write core-defs    {out_path}"));
        if !write_text(&out_path, &format!("{}\n", rtrim_lines(&final_eo))) {
            return Err(Error::fatal(format!(
                "Desugar: failed to open output {out_path}"
            )));
        }
        Ok(())
    }
}
