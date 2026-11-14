//! The `smt-meta` stage (`plugins/smt_meta/smt_meta_reduce.cpp` in Ethos):
//! writes a desugared signature with its model semantics as an SMT-LIB
//! file that deeply embeds Eunoia terms, SMT-LIB terms, types and values.
//!
//! Each program becomes a function defined by nested `ite`s over testers
//! and selectors of the embedding's datatypes; each declared constant a
//! constructor of one of those datatypes. The verification condition of a
//! rule becomes a satisfiability query, or, with `smt-meta-sygus`, a
//! synthesis conjecture over the grammar of `SmtMetaSygus`.
//!
//! The functions follow the C++ one for one, since the output has to be the
//! same byte for byte.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write;

use pathos_check::{Attr, Checker};
use pathos_elab::{Plugin, State};
use pathos_syntax::{Error, Result};
use pathos_term::{Kind, Lit, LitKind, NodeKind, SymbolKind, Term};

use crate::meta_reduce::{
    ConjectureType, MetaKind, MetaReduce, get_embed_type_app, get_embed_type_name, get_name,
    is_embed_cons, is_program_app, is_smt_apply_app,
};
use crate::native_layer::NativeLayer;
use crate::std_plugin::{ground_term_for_literal_kind, has_subterm};

/// A term the C++ takes for granted has another shape. The C++ would read
/// outside the term; here the stage stops.
fn malformed(what: &str) -> Error {
    Error::fatal(format!("SmtMetaReduce: unexpected term: {what}"))
}

fn child(ck: &Checker, e: Term, i: usize) -> Result<Term> {
    (ck.store.children(e).get(i).copied())
        .ok_or_else(|| malformed(&format!("{} has no child {i}", ck.show(e))))
}

fn type_of(ck: &mut Checker, e: Term) -> Result<Term> {
    ck.get_type(e, None)
        .ok_or_else(|| malformed(&format!("{} has no type", ck.show(e))))
}

/// A conjunction (or disjunction) being collected.
#[derive(Default)]
struct ConjPrint {
    text: String,
    npush: usize,
}

impl ConjPrint {
    fn push(&mut self, s: &str) {
        if self.npush > 0 {
            self.text.push(' ');
        }
        self.text.push_str(s);
        self.npush += 1;
    }

    /// The conjuncts as `(and ...)`, or `(or ...)` if `is_disj`; one alone
    /// stands as it is, and none is `true` (or `false`).
    fn print(&self, is_disj: bool) -> String {
        match self.npush {
            0 => if is_disj { "false" } else { "true" }.to_string(),
            1 => self.text.clone(),
            _ => format!("({} {})", if is_disj { "or" } else { "and" }, self.text),
        }
    }
}

/// What the parameters of a pattern were matched to.
#[derive(Default)]
struct SelectorCtx {
    /// For each parameter, the chain of selectors that reaches it.
    ctx: HashMap<Term, String>,
}

/// A non-terminal of the SyGuS grammar.
struct SygusGrammar {
    type_name: String,
    rules: String,
}

/// The SyGuS grammar for embedded Eunoia terms
/// (`plugins/smt_meta/smt_meta_sygus.cpp`). It is told of every
/// declaration; a synthesis conjecture prints it.
#[derive(Default)]
struct SmtMetaSygus {
    /// The stand-ins for the grammars of function-typed arguments, of
    /// embedded SMT-LIB terms and of embedded SMT-LIB types.
    gfun: Option<Term>,
    gsmt_term: Option<Term>,
    gsmt_type: Option<Term>,
    /// For each grammar key (none is the general Eunoia term grammar), the
    /// keys of the grammars its rules refer to.
    grefs: BTreeMap<Option<Term>, Vec<Term>>,
    /// The names of the grammars, in the order they were made.
    glist: Vec<String>,
    grammar: BTreeMap<String, SygusGrammar>,
    /// The grammar made for each key.
    grammar_type_alloc: HashMap<Term, String>,
    /// The kind of literal each literal constructor of the embedding holds;
    /// `None` stands for `Type`, which is what `Bool` is.
    cname_to_kind: BTreeMap<&'static str, Option<LitKind>>,
}

impl SmtMetaSygus {
    fn initialize_grammars(&mut self, ck: &mut Checker) {
        let ty = ck.mk_type();
        self.gfun = Some(ck.mk_symbol(SymbolKind::Const, "Fun", ty));
        self.gsmt_term = Some(ck.mk_symbol(SymbolKind::Const, "SmtTerm", ty));
        self.gsmt_type = Some(ck.mk_symbol(SymbolKind::Const, "SmtType", ty));
        for (gn, tn, rules) in [
            ("G_eo.Term", "eo.Term", ""),
            ("G_Bool", "Bool", "true false"),
            ("G_Int", "Int", "0 (- G_Int_C) G_Int_C"),
            (
                "G_RegLan",
                "RegLan",
                "re.all re.none (str.to_re G_String) (re.union G_RegLan G_RegLan)",
            ),
            ("G_Int_C", "Int", "1 (+ G_Int_C 1)"),
            (
                "G_Rat",
                "Rat",
                "0.0 (/ G_Int_C G_Int_C) (- (/ G_Int_C G_Int_C))",
            ),
            (
                "G_String",
                "String",
                "\"\" (str.++ G_String \"A\") (str.++ G_String \"B\")",
            ),
            ("G_Nat", "Nat", "nat.zero (nat.succ G_Nat)"),
        ] {
            self.allocate_grammar(gn, tn).rules.push_str(rules);
        }
        self.cname_to_kind = BTreeMap::from([
            ("Bool", None),
            ("Boolean", Some(LitKind::Boolean)),
            ("Numeral", Some(LitKind::Numeral)),
            ("Rational", Some(LitKind::Rational)),
            ("Binary", Some(LitKind::Binary)),
            ("String", Some(LitKind::String)),
        ]);
    }

    fn allocate_grammar(&mut self, gn: &str, tn: &str) -> &mut SygusGrammar {
        self.glist.push(gn.to_string());
        let g = self.grammar.entry(gn.to_string()).or_insert(SygusGrammar {
            type_name: String::new(),
            rules: String::new(),
        });
        g.type_name = tn.to_string();
        g
    }

    /// The name of the grammar for the key `t`, made if need be; none is
    /// the general Eunoia term grammar.
    fn grammar_for(&mut self, ck: &Checker, t: Option<Term>) -> String {
        let Some(t) = t else {
            return "G_eo.Term".to_string();
        };
        if let Some(gname) = self.grammar_type_alloc.get(&t) {
            return gname.clone();
        }
        let gname = format!("T_{}", ck.show(t));
        self.allocate_grammar(&gname, "eo.Term");
        self.grammar_type_alloc.insert(t, gname.clone());
        // the general grammar refers to it
        self.grefs.entry(None).or_default().push(t);
        gname
    }

    fn add_rule(&mut self, gname: &str, rule: &str) {
        if let Some(g) = self.grammar.get_mut(gname) {
            g.rules.push_str(rule);
            g.rules.push(' ');
        }
    }

    /// Connects each grammar to those its rules refer to. Called once all
    /// declarations have been seen.
    fn finalize_grammars(&mut self, ck: &Checker) {
        let keys: Vec<Option<Term>> = self.grefs.keys().copied().collect();
        for key in keys {
            let sg = self.grammar_for(ck, key);
            let refs = self.grefs.get(&key).cloned().unwrap_or_default();
            let mut processed = HashSet::new();
            for aret in refs {
                if !processed.insert(aret) {
                    continue;
                }
                let sgr = self.grammar_for(ck, Some(aret));
                self.add_rule(&sg, &sgr);
            }
        }
    }

    /// The key of the grammar that approximates the type `e`; none if terms
    /// of that type come from the general Eunoia term grammar.
    fn grammar_type_approx(&self, ck: &mut Checker, e: Term) -> Option<Term> {
        let mut cur = e;
        if ck.store.kind(cur) == Kind::QUOTE_TYPE {
            let q = *ck.store.children(cur).first()?;
            cur = ck.get_type(q, None)?;
        }
        while ck.store.kind(cur) == Kind::APPLY {
            cur = *ck.store.children(cur).first()?;
        }
        if !ck.store.is_ground(cur) {
            return None;
        }
        match ck.store.kind(cur) {
            Kind::FUNCTION_TYPE => self.gfun,
            Kind::Type | Kind::BoolType => Some(cur),
            Kind::CONST => match ck.show(cur).as_str() {
                // those marked $eo_Term are general Eunoia terms
                "$eo_Term" => None,
                "$smt_Type" => self.gsmt_type,
                _ => Some(cur),
            },
            // opaque type applications and programs are general terms
            _ => None,
        }
    }

    /// The approximations of the argument types of `t` and of its range.
    fn grammar_sig_approx(&self, ck: &mut Checker, t: Term) -> Vec<Option<Term>> {
        let mut ret = Vec::new();
        let mut ct = t;
        while ck.store.kind(ct) == Kind::FUNCTION_TYPE {
            let &[arg, range, ..] = ck.store.children(ct) else {
                break;
            };
            ret.push(self.grammar_type_approx(ck, arg));
            ct = range;
        }
        ret.push(self.grammar_type_approx(ck, ct));
        ret
    }

    /// Whether `e` is an embedded SMT-LIB term, an embedded SMT-LIB type,
    /// or a Eunoia term, by its name and type.
    fn smt_lib_meta_kind(ck: &mut Checker, e: Term) -> MetaKind {
        let sname = ck.show(e);
        if sname.starts_with("@@") || sname.starts_with("$eo_") {
            return MetaKind::Eunoia;
        }
        if sname.starts_with("$emb_") {
            return match sname.as_str() {
                "$emb_Bool" => MetaKind::SmtType,
                "$emb_Boolean" | "$emb_Numeral" | "$emb_Rational" | "$emb_String"
                | "$emb_Binary" => MetaKind::Smt,
                _ => MetaKind::Eunoia,
            };
        }
        // otherwise by its type: a type, or a term
        let mut tc = ck.get_type(e, None);
        while let Some(t) = tc
            && ck.store.kind(t) == Kind::FUNCTION_TYPE
        {
            tc = ck.store.children(t).last().copied();
        }
        if tc.is_some_and(|t| ck.store.kind(t) == Kind::Type) {
            MetaKind::SmtType
        } else {
            MetaKind::Smt
        }
    }

    /// Adds the production `gbase` for the declared constant `e`, whose
    /// name in the embedding is `cname`, whose meta-kind is `tk` and whose
    /// type (past its opaque arguments) is `t`.
    fn add_grammar_rules(
        &mut self,
        ck: &mut Checker,
        e: Term,
        cname: &str,
        tk: MetaKind,
        gbase: &str,
        t: Term,
    ) {
        // only constants classified as Eunoia terms give rules
        if tk != MetaKind::Eunoia {
            return;
        }
        let default_g = match Self::smt_lib_meta_kind(ck, e) {
            MetaKind::Eunoia => {
                // not built by the grammar, or only through typed rules
                if matches!(
                    cname,
                    "Stuck"
                        | "DtCons"
                        | "DtSel"
                        | "DatatypeType"
                        | "DatatypeTypeRef"
                        | "Apply"
                        | "Const"
                ) {
                    return;
                }
                None
            }
            MetaKind::SmtType => self.gsmt_type,
            _ => self.gsmt_term,
        };
        let ct = match self.cname_to_kind.get(cname) {
            None => Some(t),
            Some(None) => Some(ck.mk_type()),
            Some(Some(LitKind::Boolean)) => Some(ck.mk_bool_type()),
            Some(&Some(k)) => {
                // a ground type, from an arbitrary value of the kind
                let gt = ground_term_for_literal_kind(ck, k);
                ck.get_literal_type_rule(k, gt, None)
            }
        };
        // A literal kind the signature gives no type: the default grammar
        // stands for it.
        let mut approx_sig = match ct {
            Some(ct) => self.grammar_sig_approx(ck, ct),
            None => vec![None],
        };
        for a in &mut approx_sig {
            if a.is_none() {
                *a = default_g;
            }
        }
        // the range is a sort the default grammar can produce
        let aret = approx_sig.last().copied().flatten();
        if let (Some(_), Some(aret)) = (default_g, aret)
            && Some(aret) != default_g
        {
            self.grammar_for(ck, default_g);
            self.grefs.entry(default_g).or_default().push(aret);
        }
        self.add_rules_for_sig(ck, gbase, &approx_sig);
    }

    fn add_rules_for_sig(&mut self, ck: &Checker, gbase: &str, approx_sig: &[Option<Term>]) {
        let mut curr = gbase.to_string();
        let Some((&aret, args)) = approx_sig.split_last() else {
            return;
        };
        if !args.is_empty() {
            // the function on its own
            let sg = self.grammar_for(ck, self.gfun);
            self.add_rule(&sg, &curr);
            // and applied to an argument from each argument's grammar
            for &arg in args {
                let sga = self.grammar_for(ck, arg);
                curr = format!("(eo.Apply {curr} {sga})");
            }
        }
        let sgret = self.grammar_for(ck, aret);
        self.add_rule(&sgret, &curr);
    }

    /// The grammar for a synthesis target of type `t`.
    fn print_grammar(&mut self, ck: &mut Checker, t: Term) -> String {
        let mut os = String::from("\n  ((G_Start eo.Term)");
        // An unknown type is likely a type parameter: an SMT-LIB term is
        // looked for.
        let gt = self.grammar_type_approx(ck, t).or(self.gsmt_term);
        let sggt = self.grammar_for(ck, gt);
        let mut body = format!("  (G_Start eo.Term ({sggt}))\n");
        for gn in &self.glist {
            let Some(g) = self.grammar.get(gn) else {
                continue;
            };
            let _ = write!(os, " ({gn} {})", g.type_name);
            let _ = write!(body, "  ({gn} {} (", g.type_name);
            if g.rules.is_empty() {
                let _ = write!(body, "(Constant {})", g.type_name);
            } else {
                body.push_str(&g.rules);
            }
            body.push_str("))\n");
        }
        let _ = write!(os, ") (\n{body})\n");
        os
    }
}

pub struct SmtMeta {
    base: MetaReduce,
    /// What `tools/eoc/compiler/sem_compile.py` compiled
    /// `plugins/smt_meta/smt-vc.eos` to. A block comes out in one of two
    /// places: `Vc`, where only SMT-LIB is in scope, and `Embed`, below the
    /// datatypes of the embedding.
    natives: NativeLayer,
    /// Where the text being printed comes out: `Embed` for definitions and
    /// the conjecture, `Vc` for the datatypes.
    scope: &'static str,
    /// The programs declared ahead of their definition.
    prog_decl_processed: HashSet<Term>,
    defs: String,
    smt_vc: String,
    embed_type_dt: String,
    embed_term_dt: String,
    embed_eo_term_dt: String,
    embed_value_dt: String,
    embed_map_dt: String,
    embed_seq_dt: String,
    sygus: SmtMetaSygus,
}

/// Whether the name is of a symbol the stage's templates supply.
fn is_builtin_meta_symbol(sname: &str) -> bool {
    sname.starts_with("$smt_") || sname.starts_with("$native_") || sname == "$eo_Term"
}

impl SmtMeta {
    pub fn new(sygus: bool) -> Result<SmtMeta> {
        let mut base = MetaReduce::new(if sygus {
            ConjectureType::Sygus
        } else {
            ConjectureType::Vc
        })?;
        // The layer is read now: names are noted as text is printed, which
        // starts before the end of the input.
        let path = base.std.resource_path("tools/eoc/out/smt_vc_native.smt2");
        let mut natives = NativeLayer::new(&path, ";", "Vc")?;
        (base.prefix_to_meta_kind).insert("eo".to_string(), MetaKind::Eunoia);
        // the grammars name the natural numbers by their constructors
        natives.use_top("Nat")?;
        Ok(SmtMeta {
            base,
            natives,
            scope: "Vc",
            prog_decl_processed: HashSet::new(),
            defs: String::new(),
            smt_vc: String::new(),
            embed_type_dt: String::new(),
            embed_term_dt: String::new(),
            embed_eo_term_dt: String::new(),
            embed_value_dt: String::new(),
            embed_map_dt: String::new(),
            embed_seq_dt: String::new(),
            sygus: SmtMetaSygus::default(),
        })
    }

    fn type_meta_kind(&self, ck: &Checker, typ: Term, else_kind: MetaKind) -> MetaKind {
        self.base.get_type_meta_kind_for(ck, typ, else_kind, true)
    }

    fn meta_kind(&self, ck: &mut Checker, e: Term) -> (MetaKind, String) {
        self.base.get_meta_kind_for(ck, e, is_builtin_meta_symbol)
    }

    /// The SMT-LIB name an application of `$native_apply_*` or
    /// `$native_type_*` carries; the native layer is told it is named.
    fn embed_name(&mut self, ck: &Checker, app: Term) -> Result<String> {
        if !is_smt_apply_app(ck, app) {
            return Err(malformed(&format!(
                "expected smt apply app when asking for embed name {}",
                ck.show(app)
            )));
        }
        let name = match ck.store.lit(child(ck, app, 1)?) {
            Some(Lit::String(s)) => s.to_string(),
            _ => String::new(),
        };
        self.natives.use_in(&name, self.scope)?;
        Ok(name)
    }

    /// The SMT-LIB sort of the type `t`; none if `t` is not a type of the
    /// embedding and `tctx` gives no default.
    fn print_meta_type(&mut self, ck: &Checker, t: Term, tctx: MetaKind) -> Result<Option<String>> {
        Ok(Some(match self.type_meta_kind(ck, t, tctx) {
            MetaKind::Eunoia | MetaKind::CheckerEmbed => "eo.Term".to_string(),
            MetaKind::Smt => "sm.Term".to_string(),
            MetaKind::SmtType => "tsm.Type".to_string(),
            MetaKind::SmtValue => "vsm.Value".to_string(),
            MetaKind::SmtBuiltin => self.embed_name(ck, t)?,
            MetaKind::SmtMap => "msm.Map".to_string(),
            MetaKind::SmtSeq => "ssm.Seq".to_string(),
            // the $native_embed_* application carries the name
            MetaKind::EoEmbed | MetaKind::SmtEmbed => {
                get_embed_type_name(ck, get_embed_type_app(ck, t))?
            }
            // the kinds of the proof checker are the Lean backend's
            MetaKind::None | MetaKind::Proof | MetaKind::CheckerRule | MetaKind::CheckerCmd => {
                return Ok(None);
            }
        }))
    }

    /// An atomic term as it is written in the embedding.
    fn print_emb_atomic_term(&self, ck: &mut Checker, c: Term) -> Result<String> {
        Ok(match ck.store.kind(c) {
            Kind::Type => "eo.Type".to_string(),
            // programs print as they are
            Kind::PROGRAM_CONST => ck.show(c),
            Kind::CONST => {
                let cname = get_name(ck, c);
                match cname.strip_prefix("$emb_") {
                    // a constructor of a datatype: its name without `$emb_`
                    Some(rest) if cname.contains('.') => rest.to_string(),
                    Some(rest) => format!("eo.{rest}"),
                    None => {
                        let (k, cname) = self.meta_kind(ck, c);
                        format!("{}{cname}", k.prefix()?)
                    }
                }
            }
            Kind::BoolType => "eo.Bool".to_string(),
            _ => match ck.store.lit(c) {
                Some(Lit::Bool(b)) => format!("(eo.Boolean {b})"),
                Some(Lit::Numeral(n)) if n.sgn() < 0 => format!("(eo.Numeral (- {}))", n.neg()),
                Some(Lit::Numeral(n)) => format!("(eo.Numeral {n})"),
                Some(Lit::Rational(_)) => format!("(eo.Rational {})", ck.show(c)),
                Some(Lit::Binary(bv)) => format!("(eo.Binary {} {})", bv.size(), bv.value()),
                Some(Lit::String(_)) => format!("(eo.String {})", ck.show(c)),
                // the C++ prints nothing for any other atom
                _ => String::new(),
            },
        })
    }

    /// Adds to `print` the conditions under which the term reached by
    /// `init_ctx` matches the pattern `c`, and to `ctx` what the pattern's
    /// parameters are bound to.
    fn print_emb_pattern_match(
        &mut self,
        ck: &mut Checker,
        c: Term,
        init_ctx: &str,
        ctx: &mut SelectorCtx,
        print: &mut ConjPrint,
    ) -> Result<()> {
        let mut visit = vec![(c, init_ctx.to_string())];
        while let Some((tcur, curr_term)) = visit.pop() {
            let ck_kind = ck.store.kind(tcur);
            let children = ck.store.children(tcur).to_vec();
            let is_fun_type = ck_kind == Kind::FUNCTION_TYPE;
            let mut print_arg_start = 0;
            let cname = match ck_kind {
                // (-> T U) is (_ (_ -> T) U); see below
                Kind::APPLY | Kind::FUNCTION_TYPE => Some("eo.Apply".to_string()),
                Kind::APPLY_OPAQUE => {
                    print_arg_start = 1;
                    if is_smt_apply_app(ck, tcur) {
                        if children.len() == 2 {
                            // e.g. ($native_apply_0 "nat.zero") in a pattern
                            let name = self.embed_name(ck, tcur)?;
                            print.push(&format!("(= {curr_term} {name})"));
                            continue;
                        }
                        // a builtin constructor with arguments, e.g. nat.succ
                        print_arg_start = 2;
                        Some(self.embed_name(ck, tcur)?)
                    } else {
                        Some(self.print_emb_atomic_term(ck, child(ck, tcur, 0)?)?)
                    }
                }
                _ => None,
            };
            if let Some(cname) = cname {
                print.push(&format!("((_ is {cname}) {curr_term})"));
                for (i, &arg) in children.iter().enumerate().skip(print_arg_start) {
                    let next = format!("({cname}.arg{} {curr_term})", i + 1 - print_arg_start);
                    if i == 0 && is_fun_type {
                        print.push(&format!("((_ is eo.Apply) {next})"));
                        print.push(&format!("((_ is eo.FunType) (eo.Apply.arg1 {next}))"));
                        visit.push((arg, format!("(eo.Apply.arg2 {next})")));
                    } else {
                        visit.push((arg, next));
                    }
                }
            } else if ck_kind == Kind::PARAM {
                match ctx.ctx.get(&tcur) {
                    // the first time: bound to the chain of selectors
                    None => {
                        ctx.ctx.insert(tcur, curr_term);
                    }
                    // seen before in the pattern: the two must be equal
                    Some(prev) => print.push(&format!("(= {curr_term} {prev})")),
                }
            } else {
                // an atom: equal to it
                let atom = self.print_emb_atomic_term(ck, tcur)?;
                print.push(&format!("(= {curr_term} {atom})"));
            }
        }
        Ok(())
    }

    /// The term `body` as it is written in the embedding, with each
    /// parameter replaced by what `ctx` binds it to.
    fn print_emb_term(
        &mut self,
        ck: &mut Checker,
        body: Term,
        ctx: &SelectorCtx,
    ) -> Result<String> {
        let mut os = String::new();
        // The parentheses to close after a term, and the terms whose
        // children are on the stack. Every term is printed in the Eunoia
        // context, so the term alone is the key.
        let mut cparen: HashMap<Term, usize> = HashMap::new();
        let mut pushed_children: HashSet<Term> = HashSet::new();
        // `None` stands for a space
        let mut visit: Vec<Option<Term>> = vec![Some(body)];
        while let Some(&cur) = visit.last() {
            let Some(rec_term) = cur else {
                os.push(' ');
                visit.pop();
                continue;
            };
            if pushed_children.remove(&rec_term) {
                // done with the arguments: close what is open
                if let Some(n) = cparen.remove(&rec_term) {
                    for _ in 0..n {
                        os.push(')');
                    }
                }
                visit.pop();
                continue;
            }
            pushed_children.insert(rec_term);
            let kind = ck.store.kind(rec_term);
            let children = ck.store.children(rec_term).to_vec();
            if kind == Kind::PARAM {
                match ctx.ctx.get(&rec_term) {
                    Some(bound) => os.push_str(bound),
                    None => os.push_str(&ck.show(rec_term)),
                }
                continue;
            }
            if children.is_empty() {
                os.push_str(&self.print_emb_atomic_term(ck, rec_term)?);
                continue;
            }
            let mut cstart = 0;
            match kind {
                Kind::APPLY => {
                    os.push('(');
                    *cparen.entry(rec_term).or_default() += 1;
                    // programs print as themselves
                    if !is_program_app(ck, rec_term) {
                        // An application that can evaluate must pass
                        // stuckness on, which $eo_mk_apply does.
                        os.push_str(if ck.store.is_evaluatable(rec_term) {
                            "$eo_mk_apply "
                        } else {
                            "eo.Apply "
                        });
                    }
                }
                Kind::APPLY_OPAQUE => {
                    let sname = ck.show(children[0]);
                    if sname.starts_with("$native_apply_") || sname.starts_with("$native_type_") {
                        // `($native_apply_3 "ite" ...)` prints as `(ite ...)`
                        let emb_name = self.embed_name(ck, rec_term)?;
                        if children.len() > 2 {
                            let _ = write!(os, "({emb_name} ");
                            *cparen.entry(rec_term).or_default() += 1;
                            cstart = 2;
                        } else {
                            // ($native_apply_0 "true") prints as `true`
                            os.push_str(&emb_name);
                            continue;
                        }
                    } else {
                        os.push('(');
                        *cparen.entry(rec_term).or_default() += 1;
                    }
                }
                Kind::FUNCTION_TYPE => {
                    os.push_str("(eo.Apply (eo.Apply eo.FunType ");
                    *cparen.entry(rec_term).or_default() += 1;
                    // the inner application closes after the first argument
                    *cparen.entry(children[0]).or_default() += 1;
                }
                Kind::Eval(_) => {
                    // the eo:: operators that are left become programs
                    let kstr = kind.to_term_string();
                    if let Some(op) = kstr.strip_prefix("eo::") {
                        let _ = write!(os, "($eo_{op} ");
                        *cparen.entry(rec_term).or_default() += 1;
                    }
                }
                Kind::Node(NodeKind::Variable) => {
                    os.push_str("(eo.Var ");
                    *cparen.entry(rec_term).or_default() += 1;
                }
                _ => {}
            }
            // the children, last first, with a space between two
            for (i, &rc) in children.iter().enumerate().skip(cstart).rev() {
                visit.push(Some(rc));
                if i != cstart {
                    visit.push(None);
                }
            }
        }
        Ok(os)
    }

    /// Writes the program `v`, or its declaration if `prog` is none, to the
    /// definitions. Also called for `define` commands.
    fn finalize_program(
        &mut self,
        ck: &mut Checker,
        v: Term,
        prog: Option<Term>,
        is_define: bool,
    ) -> Result<()> {
        self.scope = "Embed";
        // a second forward declaration
        if prog.is_none() && self.prog_decl_processed.contains(&v) {
            return Ok(());
        }
        let vshown = ck.show(v);
        let what = if prog.is_none() {
            "fwd-decl: "
        } else {
            "program: "
        };
        let _ = writeln!(self.defs, "; {what}{vshown}");
        let vt = type_of(ck, v)?;
        let types = ck.store.children(vt).to_vec();
        let nargs = types.len();
        let Some((&ret_ty, arg_tys)) = types.split_last() else {
            return Err(malformed("a program type without a return type"));
        };
        let vctx_args: Vec<MetaKind> = (types.iter())
            .map(|&t| self.type_meta_kind(ck, t, MetaKind::Eunoia))
            .collect();
        let mut decl = format!("(declare-fun {vshown} (");
        let mut var_list = String::new();
        let mut args = Vec::new();
        let mut app_term = format!("({vshown}");
        let mut print_stuck = ConjPrint::default();
        for (i, &arg_ty) in arg_tys.iter().enumerate() {
            if i > 0 {
                decl.push(' ');
                var_list.push(' ');
            }
            let arg_type =
                (self.print_meta_type(ck, arg_ty, MetaKind::Eunoia)?).unwrap_or_default();
            decl.push_str(&arg_type);
            let arg = format!("x{}", i + 1);
            let _ = write!(app_term, " {arg}");
            let _ = write!(var_list, "({arg} {arg_type})");
            // only a Eunoia term can be stuck
            if vctx_args[i] == MetaKind::Eunoia {
                print_stuck.push(&format!("(= {arg} eo.Stuck)"));
            }
            args.push(arg);
        }
        app_term.push(')');
        let ret_type = (self.print_meta_type(ck, ret_ty, MetaKind::Eunoia)?).unwrap_or_default();
        let _ = writeln!(decl, ") {ret_type})");
        let Some(prog) = prog else {
            self.prog_decl_processed.insert(v);
            let _ = writeln!(self.defs, "{decl}");
            return Ok(());
        };
        let mut req_axiom = self.prog_decl_processed.contains(&v);
        let mut cases = String::new();
        let mut cases_end = String::new();
        // A program whose range is not a Eunoia term cannot get stuck, and
        // neither can a definition.
        let is_eunoia_program =
            self.type_meta_kind(ck, ret_ty, MetaKind::Eunoia) == MetaKind::Eunoia && !is_define;
        if is_eunoia_program {
            let _ = write!(cases, "  (ite {}\n    eo.Stuck\n", print_stuck.print(true));
            cases_end.push(')');
        }
        let pcases = ck.store.children(prog).to_vec();
        let ncases = pcases.len();
        for (i, &c) in pcases.iter().enumerate() {
            let (hd, body) = (child(ck, c, 0)?, child(ck, c, 1)?);
            // a recursive program needs an axiom
            if !req_axiom && has_subterm(ck, body, v) {
                req_axiom = true;
            }
            let mut ctx = SelectorCtx::default();
            let mut print = ConjPrint::default();
            let hd_children = ck.store.children(hd).to_vec();
            if hd_children.len() > nargs {
                return Err(malformed(&format!(
                    "the case {} has more arguments than its program",
                    ck.show(hd)
                )));
            }
            for (j, &pat) in hd_children.iter().enumerate().skip(1) {
                self.print_emb_pattern_match(ck, pat, &args[j - 1], &mut ctx, &mut print)?;
            }
            let curr_ret = self.print_emb_term(ck, body, &ctx)?;
            // The last case of a program that is not over Eunoia terms is
            // taken to be total.
            if i + 1 < ncases || is_eunoia_program {
                let _ = writeln!(cases, "  (ite {}", print.print(false));
                cases_end.push(')');
            }
            let _ = writeln!(cases, "    {curr_ret}");
        }
        if req_axiom {
            // declared now, unless it was declared ahead
            if !self.prog_decl_processed.contains(&v) {
                self.defs.push_str(&decl);
            }
            let _ = write!(
                self.defs,
                "(assert (! (forall ({var_list})\n  (! (= {app_term}\n"
            );
            cases_end.push(')');
        } else {
            let _ = writeln!(self.defs, "(define-fun {vshown} ({var_list}) {ret_type}");
        }
        self.defs.push_str(&cases);
        if is_eunoia_program {
            self.defs.push_str("    eo.Stuck");
        }
        self.defs.push_str(&cases_end);
        if req_axiom {
            let _ = write!(
                self.defs,
                " :pattern ({app_term}))) :named sm.axiom.{vshown})"
            );
        }
        self.defs.push_str(")\n\n");
        Ok(())
    }

    /// The declared constant `e` as a constructor of the datatype of the
    /// embedding it belongs to.
    fn finalize_decl(&mut self, ck: &mut Checker, e: Term) -> Result<()> {
        // what a constructor names must stand above the datatypes
        self.scope = "Vc";
        if !self.base.begin_finalize_decl(e) {
            return Ok(());
        }
        let (tk, cnamek) = self.meta_kind(ck, e);
        let prefix = match tk {
            MetaKind::Eunoia => "eo.",
            MetaKind::SmtType => "tsm.",
            MetaKind::Smt => "sm.",
            MetaKind::SmtValue => "vsm.",
            MetaKind::SmtMap => "msm.",
            MetaKind::SmtSeq => "ssm.",
            _ => return Ok(()),
        };
        let cname = format!("{prefix}{cnamek}");
        let what = if is_embed_cons(ck, e) {
            "smt-cons: "
        } else {
            "user-decl: "
        };
        let mut out = format!("  ; {what}{cnamek}\n  ({cname}");
        let ct = type_of(ck, e)?;
        let attr = ck.attribute_kind(e);
        let mut nopq_args = 0;
        let mut ret_type = ct;
        if attr == Attr::Opaque {
            // opaque symbols are constructors with arguments
            nopq_args = ck.store.num_children(ct).saturating_sub(1);
            ret_type = child(ck, ct, nopq_args)?;
        }
        if matches!(attr, Attr::Amb | Attr::AmbDatatypeConstructor) {
            return Err(Error::fatal(format!(
                "SmtMetaReduce: ambiguous symbol {} in a desugared signature",
                ck.show(e)
            )));
        }
        let mut sygus_args = String::new();
        for i in 0..nopq_args {
            // the type the argument has in the embedding
            let mut typ = child(ck, ct, i)?;
            if ck.store.kind(typ) == Kind::QUOTE_TYPE {
                let targ = child(ck, typ, 0)?;
                typ = type_of(ck, targ)?;
            }
            let sst = (self.print_meta_type(ck, typ, MetaKind::None)?)
                .unwrap_or_else(|| "eo.Term".to_string());
            let _ = write!(out, " ({cname}.arg{} {sst})", i + 1);
            let _ = write!(sygus_args, " G_{sst}");
        }
        out.push_str(")\n");
        match tk {
            MetaKind::Eunoia => self.embed_eo_term_dt.push_str(&out),
            MetaKind::SmtType => self.embed_type_dt.push_str(&out),
            MetaKind::Smt => self.embed_term_dt.push_str(&out),
            MetaKind::SmtValue => self.embed_value_dt.push_str(&out),
            MetaKind::SmtMap => self.embed_map_dt.push_str(&out),
            _ => self.embed_seq_dt.push_str(&out),
        }
        let grule_base = if nopq_args > 0 {
            format!("({cname}{sygus_args})")
        } else {
            cname
        };
        (self.sygus).add_grammar_rules(ck, e, &cnamek, tk, &grule_base, ret_type);
        Ok(())
    }
}

impl Plugin for SmtMeta {
    fn initialize(&mut self, st: &mut State) -> Result<()> {
        self.sygus.initialize_grammars(&mut st.ck);
        Ok(())
    }

    fn bind(&mut self, st: &mut State, _name: &str, e: Term) -> Result<()> {
        if st.ck.store.kind(e) != Kind::CONST {
            return Ok(());
        }
        self.finalize_decl(&mut st.ck, e)
    }

    fn define_program(&mut self, st: &mut State, v: Term, prog: Option<Term>) -> Result<()> {
        self.finalize_program(&mut st.ck, v, prog, false)
    }

    fn define(&mut self, st: &mut State, name: &str, e: Term) -> Result<()> {
        let ck = &mut st.ck;
        // a definition stands with the programs
        self.scope = "Embed";
        // Definitions of `$eo_` names are kept: they say what the eo::
        // operators that are still in the text become.
        if !name.starts_with("$eo_") {
            return Ok(());
        }
        // a $native_embed_* type only names a datatype
        if get_embed_type_app(ck, e).is_some() {
            return Ok(());
        }
        match self.base.build_lambda_define_program(ck, name, e) {
            Some((symbol, prog)) => self.finalize_program(ck, symbol, Some(prog), true),
            None => {
                let printed = self.print_emb_term(ck, e, &SelectorCtx::default())?;
                let _ = writeln!(self.defs, "(define-fun {name} () eo.Term {printed})");
                Ok(())
            }
        }
    }

    fn echo(&mut self, st: &mut State, msg: &str) -> Result<bool> {
        if let Some(command) = msg.strip_prefix("smt-meta-cmd ") {
            let _ = writeln!(self.defs, "(echo \"Run {command}...\")\n{command}");
            return Ok(false);
        }
        let Some(rest) = msg.strip_prefix("smt-meta ") else {
            return Ok(true);
        };
        let eosc = rest.split(' ').next().unwrap_or_default();
        let Some(vv) = st.get_var(eosc) else {
            return Err(malformed(&format!(
                "when making verification condition, could not find program {eosc}"
            )));
        };
        let ck = &mut st.ck;
        let def = ck
            .get_program(vv)
            .ok_or_else(|| malformed(&format!("{eosc} is not a defined program")))?;
        let first_case = child(ck, def, 0)?;
        let pat_call = child(ck, first_case, 0)?;
        // the conjecture stands at the end of the file
        self.scope = "Embed";
        let _ = writeln!(self.smt_vc, ";;;; final verification condition for {eosc}");
        // The conjecture is over sm.Term: there is an SMT-LIB term that,
        // embedded into Eunoia, witnesses the unsoundness.
        let vt = type_of(ck, vv)?;
        let types = ck.store.children(vt).to_vec();
        let arg_tys = &types[..types.len().saturating_sub(1)];
        let eo_true = "(eo.Boolean true)";
        let mut call = String::new();
        match self.base.conjecture_type {
            ConjectureType::Vc => {
                self.smt_vc.push_str("(assert (! (exists (");
                for (i, &arg_ty) in arg_tys.iter().enumerate() {
                    let meta_type = (self.print_meta_type(ck, arg_ty, MetaKind::None)?)
                        .unwrap_or_else(|| "eo.Term".to_string());
                    if i > 0 {
                        self.smt_vc.push(' ');
                    }
                    let _ = write!(self.smt_vc, "(x{} {meta_type})", i + 1);
                    let _ = write!(call, " x{}", i + 1);
                }
                let _ = writeln!(
                    self.smt_vc,
                    ")\n  (= ({eosc}{call}) {eo_true})) :named sm.conjecture.{}))\n(check-sat)",
                    ck.show(vv)
                );
            }
            ConjectureType::Sygus => {
                self.sygus.finalize_grammars(ck);
                for (i, &arg_ty) in arg_tys.iter().enumerate() {
                    if self.type_meta_kind(ck, arg_ty, MetaKind::Eunoia) != MetaKind::Eunoia {
                        let meta_type =
                            (self.print_meta_type(ck, arg_ty, MetaKind::None)?).unwrap_or_default();
                        let _ = writeln!(self.smt_vc, "(declare-fun M{} () {meta_type})", i + 1);
                        let _ = write!(call, " M{}", i + 1);
                        continue;
                    }
                    let var_name = format!("arg_{}", ck.show(child(ck, pat_call, i + 1)?));
                    let grammar = self.sygus.print_grammar(ck, arg_ty);
                    let _ = writeln!(self.smt_vc, "(synth-fun {var_name} () eo.Term{grammar})");
                    let _ = write!(call, " {var_name}");
                }
                let _ = writeln!(
                    self.smt_vc,
                    "(constraint (= ({eosc}{call}) {eo_true}))\n(check-synth)"
                );
            }
        }
        Ok(false)
    }

    fn finalize(&mut self, st: &mut State) -> Result<()> {
        for (dt, none) in [
            (&mut self.embed_type_dt, "tsm"),
            (&mut self.embed_term_dt, "sm"),
            (&mut self.embed_map_dt, "msm"),
            (&mut self.embed_seq_dt, "ssm"),
        ] {
            if dt.is_empty() {
                let _ = writeln!(dt, "  ({none}.None)");
            }
        }
        let replacements = [
            ("$NATIVE_DEFS$", self.natives.defs("Vc")),
            ("$NATIVE_EMBED_DEFS$", self.natives.defs("Embed")),
            ("$SM_DEFS$", self.defs.clone()),
            ("$SMT_VC$", self.smt_vc.clone()),
            ("$SM_TYPE_DECL$", self.embed_type_dt.clone()),
            ("$SM_TERM_DECL$", self.embed_term_dt.clone()),
            ("$SM_VALUE_DECL$", self.embed_value_dt.clone()),
            ("$SM_MAP_DECL$", self.embed_map_dt.clone()),
            ("$SM_SEQ_DECL$", self.embed_seq_dt.clone()),
            ("$SM_EO_TERM_DECL$", self.embed_eo_term_dt.clone()),
        ]
        .map(|(tag, text)| (tag.to_string(), text));
        self.base.std.emit_resource_file(
            &mut st.ck,
            "plugins/smt_meta/smt_meta.smt2",
            "plugins/smt_meta/smt_meta_gen.smt2",
            &replacements,
            false,
        )?;
        Ok(())
    }
}
