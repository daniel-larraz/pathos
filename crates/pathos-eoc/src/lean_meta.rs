//! The `lean-meta` stage (`plugins/lean_meta/lean_meta_reduce.cpp` in
//! Ethos): writes a desugared signature with its model semantics as Lean
//! modules that deeply embed Eunoia terms and proofs, SMT-LIB terms, types
//! and values, and the commands and rules of the proof checker.
//!
//! Each program becomes a Lean definition by pattern matching; each
//! declared constant a constructor of one of the embedding's inductives.
//! The stage renders a dozen templates (the checker, the parser of proofs,
//! the SMT-LIB syntax, typing and model, the lemmas) and one file per proof
//! rule.
//!
//! The functions follow the C++ one for one, since the output has to be the
//! same byte for byte.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write;

use pathos_check::{Attr, Checker};
use pathos_elab::{Plugin, State};
use pathos_syntax::{Error, Result};
use pathos_term::{Kind, Lit, SymbolKind, Term};

use crate::linear_patterns;
use crate::meta_reduce::{
    ConjectureType, MetaKind, MetaReduce, get_embed_type_app, get_embed_type_name, get_name,
    is_program_app, is_smt_apply_app,
};
use crate::native_layer::NativeLayer;
use crate::std_plugin::{
    PARSE_DEF_PREFIX, Replacement, is_parse_def_name, mk_parse_def_name, os_path, read_text,
    replace_all, subterms_of_kind,
};

/// The greatest number of indices an operator may take: the embedding
/// declares `$emb_UOp<n>` for `n` up to this.
const MAX_INDEX_ARITY: usize = 5;

/// A term the C++ takes for granted has another shape. The C++ would read
/// outside the term; here the stage stops.
fn malformed(what: &str) -> Error {
    Error::fatal(format!("LeanMetaReduce: unexpected term: {what}"))
}

/// What a failed `AlwaysAssert(cond) << msg` prints.
fn check_failure(cond: &str, msg: &str) -> Error {
    Error::fatal(format!("Check failure\n\n {cond}\n{msg}"))
}

fn child(ck: &Checker, e: Term, i: usize) -> Result<Term> {
    (ck.store.children(e).get(i).copied())
        .ok_or_else(|| malformed(&format!("{} has no child {i}", ck.show(e))))
}

fn type_of(ck: &mut Checker, e: Term) -> Result<Term> {
    ck.get_type(e, None)
        .ok_or_else(|| malformed(&format!("{} has no type", ck.show(e))))
}

/// The characters `>>` skips.
const SPACES: [char; 6] = [' ', '\t', '\n', '\x0b', '\x0c', '\r'];

/// Reads a line as a C++ stream does with `>>`.
struct Words<'a> {
    rest: &'a str,
}

impl<'a> Words<'a> {
    fn word(&mut self) -> Option<&'a str> {
        self.rest = self.rest.trim_start_matches(SPACES);
        if self.rest.is_empty() {
            return None;
        }
        let end = self.rest.find(SPACES).unwrap_or(self.rest.len());
        let (word, rest) = self.rest.split_at(end);
        self.rest = rest;
        Some(word)
    }

    /// An unsigned number: a sign, then digits, up to the first character
    /// that is not one. A negative number wraps around, as in C++.
    fn number(&mut self) -> Option<u64> {
        self.rest = self.rest.trim_start_matches(SPACES);
        let (negative, digits) = match self.rest.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, self.rest.strip_prefix('+').unwrap_or(self.rest)),
        };
        let end = (digits.find(|c: char| !c.is_ascii_digit())).unwrap_or(digits.len());
        if end == 0 {
            return None;
        }
        let (digits, rest) = digits.split_at(end);
        self.rest = rest;
        let mut value = 0u64;
        for d in digits.chars() {
            value = (value.checked_mul(10))?.checked_add(u64::from(d.to_digit(10)?))?;
        }
        Some(if negative {
            value.wrapping_neg()
        } else {
            value
        })
    }
}

/// A Lean identifier for an SMT-LIB one.
fn clean_smt_id(id: &str) -> String {
    if id == "end" || id == "variable" {
        return format!("__eo_{id}");
    }
    let mut idc = id.to_string();
    for (from, to) in [
        ("++", "concat"),
        ("+", "plus"),
        ("-", "neg"),
        ("*", "mult"),
        ("=>", "imp"),
        ("<=", "leq"),
        ("<", "lt"),
        (">=", "geq"),
        (">", "gt"),
        ("=", "eq"),
        ("/", "qdiv"),
        ("^", "exp"),
        (".", "_"),
        ("@", "_at_"),
        ("$", "__"),
    ] {
        idc = replace_all(&idc, from, to);
    }
    idc
}

/// A Lean identifier for the name of a program.
fn clean_id(id: &str) -> String {
    clean_smt_id(&replace_all(id, "-", "_"))
}

/// The text as a Lean string literal.
fn quote_lean_string(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

fn is_integer(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_ascii_digit())
}

/// The Lean type of the terms of a meta-kind; none for the kinds that have
/// no inductive of their own.
fn print_meta_type_kind(k: MetaKind) -> Option<&'static str> {
    Some(match k {
        MetaKind::Eunoia => "Term",
        MetaKind::SmtType => "SmtType",
        MetaKind::Smt => "SmtTerm",
        MetaKind::SmtValue => "SmtValue",
        MetaKind::SmtMap => "SmtMap",
        MetaKind::SmtSeq => "SmtSeq",
        MetaKind::Proof => "Proof",
        MetaKind::CheckerRule => "CRule",
        MetaKind::CheckerCmd => "CCmd",
        _ => return None,
    })
}

/// Whether a constructor of this meta-kind is of a datatype the embedding
/// is built over (the map, the sequence, a declared SMT-LIB datatype)
/// rather than of a term, a type or a value.
fn is_embed_datatype_kind(k: MetaKind) -> bool {
    matches!(k, MetaKind::SmtMap | MetaKind::SmtSeq | MetaKind::SmtEmbed)
}

/// The name of the method that gives the ordering key of the Lean type
/// `t`: the type's name without `Smt` or `native_`, its first letter in
/// lower case, then `Key`, e.g. `datatypeDeclKey` for `SmtDatatypeDecl`.
/// The methods of the types that are not generated are in the
/// lean_meta_smt_value_order.lean template, e.g. `modelIdKey` for `ModelId`.
fn get_order_key_method(t: &str) -> String {
    let base = (t.strip_prefix("Smt"))
        .or_else(|| t.strip_prefix("native_"))
        .unwrap_or(t);
    let mut chars = base.chars();
    match chars.next() {
        None => "Key".to_string(),
        Some(first) => format!("{}{}Key", first.to_ascii_lowercase(), chars.as_str()),
    }
}

/// The streams of the C++ that a program can be written to.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Out {
    Defs,
    DefsTotal,
    EoChecker,
    SmtDefs,
    SmtTypingDefs,
    Smt,
    EoIsObjDefs,
    EoIsObjDefsSimple,
}

/// The scope of the module the text written to `out` comes out in: which
/// module a stream is spliced into says where a native it names is reached
/// from.
fn scope_of(out: Out) -> &'static str {
    match out {
        Out::Defs | Out::DefsTotal | Out::EoChecker => "Eo",
        // the translation stands below SmtTyping and beside SmtModel
        Out::SmtTypingDefs | Out::EoIsObjDefs | Out::EoIsObjDefsSimple => "SmtTyping",
        Out::Smt | Out::SmtDefs => "Smtm",
    }
}

/// The streams of the C++ that a declaration can be written to.
enum DeclOut {
    EmbedTerm,
    Smt,
    SmtType,
    SmtValue,
    Rule,
    Cmd,
    /// The datatype of the embedding with this name.
    Embed(String),
}

/// The surface syntax of an operator, as the desugar stage reports it.
#[derive(Clone)]
struct ParserOp {
    /// The name in the input.
    surface: String,
    /// The name in the generated signature.
    generated: String,
    /// The number of indices (opaque arguments).
    index_arity: u64,
    /// The number of ordinary arguments.
    term_arity: u64,
    /// The syntactic attribute, e.g. `right-assoc-nil`, or `none`.
    attr: String,
    /// The operand of the attribute, or `-`.
    connector: String,
}

pub struct LeanMeta {
    base: MetaReduce,
    /// Whether to write the parser of proofs for the signature.
    generate_parser: bool,
    /// What `tools/eoc/compiler/sem_compile.py` compiled
    /// `plugins/lean_meta/lean.eos` to. Its homes are the modules that
    /// carry a `$NATIVE_DEFS$`: SmtEval, which every module sees, Logos,
    /// SmtTyping and SmtModel.
    natives: NativeLayer,
    /// The scope of the module being written; see `scope_of`.
    scope: &'static str,
    /// The partial programs, and the total ones.
    defs: String,
    defs_total: String,
    has_defs: bool,
    /// The translation from Eunoia to SMT-LIB, and its simple programs.
    eo_is_obj_defs: String,
    eo_is_obj_defs_simple: String,
    /// The constructors of the Eunoia terms.
    embed_term_dt: String,
    /// The constructors of `Term` in `embed_term_dt`, in order, each with
    /// the Lean types of its arguments: what `print_term_cmp` writes its
    /// cases from.
    term_cons: Vec<(String, Vec<String>)>,
    /// The constructors of each datatype of the embedding the target
    /// declares, by the name of the type they return.
    embed_dt: BTreeMap<String, String>,
    /// The datatypes the configuration says are ordered, by the name of
    /// their Lean inductive, e.g. SmtValue (see read_termination_clauses):
    /// each of them, and nothing else, is given an ordering key. The
    /// ordering-key cases of each, and how many constructors each has so
    /// far, which is the tag of the next.
    ordered: BTreeSet<String>,
    key: BTreeMap<String, String>,
    key_ncons: BTreeMap<String, usize>,
    /// The user operators, by their number of indices.
    embed_top_dt: [String; MAX_INDEX_ARITY + 1],
    eo_is_ref: String,
    eo_checker: String,
    /// The SMT-LIB definitions of the model, and of the static interface.
    smt_defs: String,
    smt_typing_defs: String,
    smt: String,
    smt_dt: String,
    smt_type_dt: String,
    smt_value_dt: String,
    cmd_dt: String,
    rule_dt: String,
    rl_include: String,
    rl_include_step: String,
    rl_include_step_pop: String,
    /// The programs, in the order they were defined, and their cases.
    prog_defs: Vec<Term>,
    prog_to_def: HashMap<Term, Term>,
    /// The programs made from `define` commands.
    prog_is_define: HashSet<Term>,
    total_def_progs: HashSet<Term>,
    partial_def_progs: HashSet<Term>,
    /// The programs whose cases call only themselves and simple programs.
    simple_def_progs: HashSet<Term>,
    parser_has_binder: bool,
    parser_ops: Vec<ParserOp>,
    /// The names of the proof rules, in the input and as generated.
    parser_rules: Vec<(String, String)>,
    /// The definitions the desugar stage kept for the parser: the name in
    /// the input and the definition.
    parse_defs: Vec<(String, Term)>,
    /// The `UserOp` constructors written, with their number of indices.
    emitted_user_ops: BTreeSet<(String, u64)>,
    /// The `CRule` constructors written.
    emitted_rules: BTreeSet<String>,
    /// The programs that are forced to be partial, by name. None so far.
    partial_exc: HashSet<String>,
    /// For each program, the termination clause to put after its
    /// definition.
    terminating_by: BTreeMap<String, String>,
}

impl LeanMeta {
    pub fn new(generate_parser: bool, config_file: &str) -> Result<LeanMeta> {
        let mut base = MetaReduce::new(ConjectureType::Vc)?;
        // The layer is read now: a module names one of its blocks while
        // being written, and the first is written before the end of the
        // input.
        let path = base.std.resource_path("tools/eoc/out/lean_native.lean");
        let mut natives = NativeLayer::new(&path, "--", "SmtEval")?;
        for (name, kind) in [
            ("$eo_Term", MetaKind::Eunoia),
            ("$eo_Proof", MetaKind::Proof),
            ("$eo_Rule", MetaKind::CheckerRule),
            ("$eo_Cmd", MetaKind::CheckerCmd),
        ] {
            base.type_to_meta_kind.insert(name.to_string(), kind);
        }
        (base.prefix_to_meta_kind).insert("r".to_string(), MetaKind::CheckerRule);
        (base.prefix_to_meta_kind).insert("cmd".to_string(), MetaKind::CheckerCmd);
        // The model is written over the reals, so nothing generated
        // reaches the operations over the rationals; what a package proves
        // relates the two, so they are named from the model's scope all the
        // same.
        for n in [
            "native_qplus",
            "native_qmult",
            "native_qneg",
            "native_qabs",
            "native_qlt",
            "native_qleq",
            "native_qdiv_total",
            "native_to_real",
            "native_to_int",
            "native_natlt",
        ] {
            natives.use_in(n, "Smtm")?;
        }
        let mut lean = LeanMeta {
            base,
            generate_parser,
            natives,
            scope: "SmtEval",
            defs: String::new(),
            defs_total: "mutual\n\n".to_string(),
            has_defs: false,
            eo_is_obj_defs: String::new(),
            eo_is_obj_defs_simple: String::new(),
            embed_term_dt: String::new(),
            term_cons: Vec::new(),
            embed_dt: BTreeMap::new(),
            ordered: BTreeSet::new(),
            key: BTreeMap::new(),
            key_ncons: BTreeMap::new(),
            embed_top_dt: Default::default(),
            eo_is_ref: String::new(),
            eo_checker: String::new(),
            smt_defs: String::new(),
            smt_typing_defs: String::new(),
            smt: String::new(),
            smt_dt: String::new(),
            smt_type_dt: String::new(),
            smt_value_dt: String::new(),
            cmd_dt: String::new(),
            rule_dt: String::new(),
            rl_include: String::new(),
            rl_include_step: String::new(),
            rl_include_step_pop: String::new(),
            prog_defs: Vec::new(),
            prog_to_def: HashMap::new(),
            prog_is_define: HashSet::new(),
            total_def_progs: HashSet::new(),
            partial_def_progs: HashSet::new(),
            simple_def_progs: HashSet::new(),
            parser_has_binder: false,
            parser_ops: Vec::new(),
            parser_rules: Vec::new(),
            parse_defs: Vec::new(),
            emitted_user_ops: BTreeSet::new(),
            emitted_rules: BTreeSet::new(),
            partial_exc: HashSet::new(),
            terminating_by: BTreeMap::new(),
        };
        // Why a generated definition terminates is Lean text, compiled from
        // the semantics configuration into a file of its own: the one of
        // the deep embedding, and the one of the input named on the command
        // line.
        let path = (lean.base.std).resource_path("tools/eoc/out/smt_termination.lean");
        lean.read_termination_clauses(&path)?;
        if !config_file.is_empty() {
            lean.read_termination_clauses(config_file)?;
        }
        Ok(lean)
    }

    fn buf(&mut self, out: Out) -> &mut String {
        match out {
            Out::Defs => &mut self.defs,
            Out::DefsTotal => &mut self.defs_total,
            Out::EoChecker => &mut self.eo_checker,
            Out::SmtDefs => &mut self.smt_defs,
            Out::SmtTypingDefs => &mut self.smt_typing_defs,
            Out::Smt => &mut self.smt,
            Out::EoIsObjDefs => &mut self.eo_is_obj_defs,
            Out::EoIsObjDefsSimple => &mut self.eo_is_obj_defs_simple,
        }
    }

    /// Reads the termination clauses of a file. A block runs from a line
    /// `-- $name ...`, which names the programs it is of, to the next
    /// comment line; what lies between is the clause.
    fn read_termination_clauses(&mut self, path: &str) -> Result<()> {
        // A directory opens as a stream that gives no line.
        let is_dir = std::fs::metadata(os_path(path)).is_ok_and(|m| m.is_dir());
        let text = match read_text(path) {
            Some(text) => text,
            None if is_dir => String::new(),
            None => {
                return Err(Error::fatal(format!(
                    "LeanMetaReduce: could not read the termination clauses at {path}"
                )));
            }
        };
        // the programs the block being read is of, and the text of the clause
        let mut names: Vec<String> = Vec::new();
        let mut body = String::new();
        let mut lines: Vec<&str> = text.split('\n').collect();
        if lines.last() == Some(&"") {
            lines.pop();
        }
        // one more round, with no line, takes the last block
        for line in lines.into_iter().map(Some).chain([None]) {
            if line.is_none_or(|l| l.starts_with("--")) {
                let clause = body.trim_end_matches([' ', '\t', '\n']);
                if !clause.is_empty() {
                    // A clause is appended to a definition, not written
                    // into a resource: naming the native layer here would
                    // keep nothing of it alive.
                    if clause.contains("native_") {
                        return Err(Error::fatal(format!(
                            "LeanMetaReduce: the termination clause of {} in {path} names the \
                             native layer, which is trimmed to what the compilation reaches; \
                             write the Lean type it abbreviates",
                            names.first().map_or("a program", String::as_str)
                        )));
                    }
                    for n in &names {
                        self.terminating_by.insert(n.clone(), clause.to_string());
                    }
                }
                names.clear();
                body.clear();
                if let Some(name) = line.and_then(|l| l.strip_prefix("-- ordered ")) {
                    self.ordered.insert(name.to_string());
                } else if let Some(line) = line.filter(|l| l.starts_with("-- $")) {
                    // the names start at the `$`
                    let mut words = Words {
                        rest: line.get(3..).unwrap_or_default(),
                    };
                    while let Some(w) = words.word() {
                        names.push(w.to_string());
                    }
                }
                continue;
            }
            if let (Some(line), false) = (line, names.is_empty()) {
                body.push_str(line);
                body.push('\n');
            }
        }
        Ok(())
    }

    /// The meta-kind of the type `typ`: the datatype it stands for, or
    /// `Eunoia`.
    fn type_meta_kind(&self, ck: &Checker, typ: Term) -> MetaKind {
        (self.base).get_type_meta_kind_for(ck, typ, MetaKind::Eunoia, false)
    }

    /// The datatype of the embedding `e` is a constructor of, and its name
    /// there.
    fn meta_kind(&self, ck: &mut Checker, e: Term) -> (MetaKind, String) {
        self.base.get_meta_kind_for(ck, e, |sname| {
            sname.starts_with("$smt_")
                || sname.starts_with("$native_")
                || self.base.type_to_meta_kind.contains_key(sname)
        })
    }

    /// The Lean type for the type `t`; none if there is none.
    fn print_meta_type(&mut self, ck: &Checker, t: Term) -> Result<Option<String>> {
        let tk = self.type_meta_kind(ck, t);
        if tk == MetaKind::SmtBuiltin {
            return Ok(Some(self.get_embed_name(ck, t)?));
        }
        if tk.is_embed() {
            return Ok(Some(get_embed_type_name(ck, get_embed_type_app(ck, t))?));
        }
        Ok(print_meta_type_kind(tk).map(str::to_string))
    }

    /// Whether `c`, whose name in the embedding is `cname`, is written as a
    /// `UserOp`; if so, its number of indices.
    fn is_atomic_eo(&self, ck: &mut Checker, c: Term, cname: &str) -> Result<Option<usize>> {
        let attr = ck.attribute_kind(c);
        if get_name(ck, c).starts_with("$emb") {
            return Ok(None);
        }
        if attr != Attr::Opaque {
            if matches!(cname, "Stuck" | "Type" | "FunType" | "Bool") || cname.starts_with("$eo_") {
                return Ok(None);
            }
            return Ok(Some(0));
        }
        let ct = type_of(ck, c)?;
        // a type without arguments wraps around, as in the C++
        Ok(Some(ck.store.num_children(ct).wrapping_sub(1)))
    }

    /// An atomic term as it is written in the embedding.
    fn print_emb_atomic_term(&mut self, ck: &mut Checker, c: Term) -> Result<String> {
        Ok(match ck.store.kind(c) {
            Kind::Type => "Term.Type".to_string(),
            // programs print as they are
            Kind::PROGRAM_CONST => clean_id(&ck.show(c)),
            Kind::CONST => {
                let (k, cname) = self.meta_kind(ck, c);
                if cname == "$eo_pf" {
                    return Ok("Proof.pf".to_string());
                }
                let mut os = String::new();
                let mut needs_cparen = false;
                let uarity = if k == MetaKind::Eunoia {
                    self.is_atomic_eo(ck, c, &cname)?
                } else {
                    None
                };
                if let Some(uarity) = uarity {
                    if uarity == 0 {
                        needs_cparen = true;
                        os.push_str("(Term.UOp UserOp");
                    } else {
                        let _ = write!(os, "Term.UOp{uarity} UserOp{uarity}");
                    }
                } else if k.is_embed() {
                    // a constructor of a datatype declared by a
                    // $native_embed_* type: its return type carries the name
                    let ct = type_of(ck, c)?;
                    os.push_str(&get_embed_type_name(ck, get_embed_type_app(ck, ct))?);
                } else {
                    os.push_str(print_meta_type_kind(k).unwrap_or("Term"));
                }
                os.push('.');
                os.push_str(&clean_smt_id(&cname));
                if needs_cparen {
                    os.push(')');
                }
                os
            }
            Kind::BoolType => "Term.Bool".to_string(),
            _ => match ck.store.lit(c) {
                Some(Lit::Bool(b)) => format!("(Term.Boolean {b})"),
                Some(Lit::Numeral(n)) if n.sgn() < 0 => {
                    format!("(Term.Numeral (-{} : native_Int))", n.neg())
                }
                Some(Lit::Numeral(n)) => format!("(Term.Numeral {n})"),
                Some(Lit::Rational(r)) => {
                    let rstr = replace_all(&replace_all(&ck.show(c), "/", " "), "-", "");
                    if r.sgn() < 0 {
                        format!("(Term.Rational (- (native_mk_rational {rstr})))")
                    } else {
                        format!("(Term.Rational (native_mk_rational {rstr}))")
                    }
                }
                Some(Lit::Binary(bv)) => format!("(Term.Binary {} {})", bv.size(), bv.value()),
                Some(Lit::String(s)) => {
                    let css = s.to_string();
                    if css.contains(['"', '\\']) {
                        return Err(check_failure(
                            "css.find_first_of(\"\\\"\\\\\") == std::string::npos",
                            &format!(
                                "Lean meta only supports printable ASCII string literals without \
                                 quotes or backslashes, got \"{css}\""
                            ),
                        ));
                    }
                    if css.is_empty() {
                        "(Term.String [])".to_string()
                    } else {
                        format!("(Term.String (native_string_lit \"{css}\"))")
                    }
                }
                // the C++ prints nothing for any other atom
                _ => String::new(),
            },
        })
    }

    /// The Lean name an application of `$native_apply_*` or
    /// `$native_type_*` carries; the native layer is told that the module
    /// being written names it.
    fn get_embed_name(&mut self, ck: &Checker, app: Term) -> Result<String> {
        if ck.store.kind(app) != Kind::APPLY_OPAQUE {
            return Err(check_failure(
                "oApp.getKind() == Kind::APPLY_OPAQUE",
                &format!(
                    "Bad kind for opaque {} {}",
                    ck.store.kind(app),
                    ck.show(app)
                ),
            ));
        }
        if !is_smt_apply_app(ck, app) {
            return Err(check_failure(
                "isSmtApplyApp(oApp)",
                &format!(
                    "Expected smt apply app when asking for embed name {}",
                    ck.show(app)
                ),
            ));
        }
        let smt_str = match ck.store.lit(child(ck, app, 1)?) {
            Some(Lit::String(s)) => s.to_string(),
            _ => String::new(),
        };
        // literals are not natives
        if is_integer(&smt_str) || smt_str == "true" || smt_str == "false" {
            return Ok(smt_str);
        }
        if let Some(inner) = smt_str.strip_prefix('"') {
            // closed by its only other quote, and without a backslash
            if inner.find('"') != Some(inner.len().wrapping_sub(1)) || smt_str.contains('\\') {
                return Err(check_failure(
                    "smtStr.size() >= 2 && smtStr.back() == '\"' && smtStr.find('\\\\') == \
                     std::string::npos && smtStr.find('\"', 1) == smtStr.size() - 1",
                    &format!(
                        "Lean meta only supports quoted native strings with printable ASCII \
                         bodies that contain no quotes or backslashes, got \"{smt_str}\""
                    ),
                ));
            }
            if smt_str.len() == 2 {
                return Ok("[]".to_string());
            }
            self.natives.use_in("native_string_lit", self.scope)?;
            return Ok(format!("(native_string_lit {smt_str})"));
        }
        if smt_str.starts_with("UserOp") {
            return Ok(smt_str);
        }
        let name = format!("native_{}", clean_smt_id(&smt_str));
        self.natives.use_in(&name, self.scope)?;
        Ok(name)
    }

    /// The term `body` as it is written in the embedding. With
    /// `maybe_letify` and the `print-dag` option, the subterms that occur
    /// more than once are bound by `let`s on lines of their own first.
    fn print_emb_term(
        &mut self,
        ck: &mut Checker,
        body: Term,
        tinit: MetaKind,
        maybe_letify: bool,
    ) -> Result<String> {
        let mut os = String::new();
        let mut lbind = HashMap::new();
        if maybe_letify && ck.opts.print_dag {
            let (ll, lb) = ck.compute_let_binding(body);
            lbind = lb;
            let mut first_time = true;
            for l in ll {
                // a $native_apply_0 alone is not worth a name
                if is_smt_apply_app(ck, l) && ck.store.num_children(l) == 2 {
                    lbind.remove(&l);
                    continue;
                }
                if first_time {
                    os.push('\n');
                    first_time = false;
                }
                let id = lbind.remove(&l).unwrap_or(0);
                let _ = write!(os, "    let _v{id} := ");
                self.print_emb_term_internal(ck, l, &mut os, tinit, &lbind)?;
                lbind.insert(l, id);
                os.push('\n');
            }
            if !first_time {
                os.push_str("    ");
            }
        }
        self.print_emb_term_internal(ck, body, &mut os, tinit, &lbind)?;
        Ok(os)
    }

    fn print_emb_term_internal(
        &mut self,
        ck: &mut Checker,
        body: Term,
        os: &mut String,
        tinit: MetaKind,
        lbind: &HashMap<Term, usize>,
    ) -> Result<()> {
        // The parentheses to close after a term, and the terms whose
        // children are on the stack, each with the context it was reached
        // in.
        let mut cparen: HashMap<(Term, MetaKind), usize> = HashMap::new();
        let mut pushed_children: HashSet<(Term, MetaKind)> = HashSet::new();
        let tinit = if tinit == MetaKind::None {
            MetaKind::Eunoia
        } else {
            tinit
        };
        // `None` stands for a space
        let mut visit: Vec<(Option<Term>, MetaKind)> = vec![(Some(body), tinit)];
        while let Some(&(cur, parent)) = visit.last() {
            let Some(rec_term) = cur else {
                os.push(' ');
                visit.pop();
                continue;
            };
            let key = (rec_term, parent);
            if pushed_children.remove(&key) {
                // done with the arguments: close what is open
                if let Some(n) = cparen.remove(&key) {
                    for _ in 0..n {
                        os.push(')');
                    }
                }
                visit.pop();
                continue;
            }
            if let Some(id) = lbind.get(&rec_term) {
                let _ = write!(os, "_v{id}");
                if let Some(n) = cparen.remove(&key) {
                    for _ in 0..n {
                        os.push(')');
                    }
                }
                visit.pop();
                continue;
            }
            pushed_children.insert(key);
            let kind = ck.store.kind(rec_term);
            let children = ck.store.children(rec_term).to_vec();
            if kind == Kind::PARAM {
                os.push_str(&clean_smt_id(&ck.show(rec_term)));
                continue;
            }
            let Some(&first) = children.first() else {
                os.push_str(&self.print_emb_atomic_term(ck, rec_term)?);
                continue;
            };
            let mut cstart = 0;
            if kind == Kind::APPLY {
                os.push('(');
                *cparen.entry(key).or_default() += 1;
                // programs print as themselves
                if !is_program_app(ck, rec_term) {
                    // An application that can evaluate must pass stuckness
                    // on, which __eo_mk_apply does.
                    os.push_str(if ck.store.is_evaluatable(rec_term) {
                        "__eo_mk_apply "
                    } else {
                        "Term.Apply "
                    });
                }
            } else if kind == Kind::APPLY_OPAQUE {
                let sname = ck.show(first);
                if sname.starts_with("$native_apply_") || sname.starts_with("$native_type_") {
                    // `($native_apply_3 "ite" ...)` prints as `(ite ...)`
                    let emb_name = self.get_embed_name(ck, rec_term)?;
                    if children.len() > 2 {
                        let _ = write!(os, "({emb_name} ");
                        *cparen.entry(key).or_default() += 1;
                        cstart = 2;
                    } else {
                        // ($native_apply_0 "true") prints as `true`
                        os.push_str(&emb_name);
                        continue;
                    }
                } else {
                    os.push('(');
                    *cparen.entry(key).or_default() += 1;
                }
            } else if kind == Kind::FUNCTION_TYPE {
                // the final deep embedding, propagating stuckness as for
                // applications above if the function type is evaluatable,
                // e.g. if its return type is a program application
                os.push_str(if ck.store.is_evaluatable(rec_term) {
                    "(__eo_mk_apply (__eo_mk_apply Term.FunType "
                } else {
                    "(Term.Apply (Term.Apply Term.FunType "
                });
                *cparen.entry(key).or_default() += 1;
                // the inner application closes after the first argument
                *cparen.entry((first, MetaKind::Eunoia)).or_default() += 1;
            } else if kind.is_literal_op() {
                // the eo:: operators that are left become programs
                let kstr = kind.to_term_string();
                if let Some(op) = kstr.strip_prefix("eo::") {
                    let _ = write!(os, "(__eo_{op} ");
                    *cparen.entry(key).or_default() += 1;
                }
            } else if kind == Kind::VARIABLE {
                os.push_str("(Term.Var ");
                *cparen.entry(key).or_default() += 1;
            }
            // the children, last first, with a space between two
            for (i, &rc) in children.iter().enumerate().skip(cstart).rev() {
                visit.push((Some(rc), MetaKind::Eunoia));
                if i != cstart {
                    visit.push((None, MetaKind::None));
                }
            }
        }
        Ok(())
    }

    /// Writes all the programs.
    fn finalize_programs(&mut self, ck: &mut Checker) -> Result<()> {
        for prog in self.prog_defs.clone() {
            let is_define = self.prog_is_define.contains(&prog);
            let Some(&def) = self.prog_to_def.get(&prog) else {
                continue;
            };
            self.finalize_program(ck, prog, def, is_define)?;
        }
        Ok(())
    }

    /// Writes the program `v` with the cases `prog`, or the definition of
    /// `v` as `prog` if `prog` is no list of cases. Also called for
    /// `define` commands.
    fn finalize_program(
        &mut self,
        ck: &mut Checker,
        v: Term,
        prog: Term,
        is_define: bool,
    ) -> Result<()> {
        let vname = get_name(ck, v);
        // $eo_hash has no Lean: what eo::hash returns is left open, and the
        // native layer defines nothing for it to call.
        if vname == "$eo_ite" || vname == "$eo_hash" {
            return Ok(());
        }
        let vt = type_of(ck, v)?;
        if ck.store.kind(prog) != Kind::PROGRAM {
            let vctx = self.type_meta_kind(ck, vt);
            let mut out = if self.names_model_type(ck, vt)? {
                Out::SmtDefs
            } else {
                Out::SmtTypingDefs
            };
            if vctx == MetaKind::Eunoia {
                out = Out::DefsTotal;
            }
            self.scope = scope_of(out);
            let mut text = format!("def {} : ", clean_id(&vname));
            text.push_str(&self.print_meta_type(ck, vt)?.unwrap_or_default());
            text.push_str(" := ");
            text.push_str(&self.print_emb_term(ck, prog, MetaKind::None, true)?);
            text.push('\n');
            self.buf(out).push_str(&text);
            return Ok(());
        }
        let cases_of = ck.store.children(prog).to_vec();
        let types = ck.store.children(vt).to_vec();
        let nargs = types.len();
        let mut decl = String::new();
        // which stream the program goes to
        let vctx_args: Vec<MetaKind> = (types.iter())
            .map(|&t| self.type_meta_kind(ck, t))
            .collect();
        let is_checker_def = vctx_args.iter().any(|k| k.is_checker());
        let Some((&ret_ty, _)) = types.split_last() else {
            return Err(malformed(&format!(
                "the program {} has no return type",
                ck.show(v)
            )));
        };
        let retk = vctx_args[nargs - 1];
        let mut out;
        let mut tmk = MetaKind::Eunoia;
        if is_checker_def {
            out = Out::EoChecker;
        } else if retk.is_smt() {
            out = if self.names_model_type(ck, vt)? {
                Out::SmtDefs
            } else {
                Out::SmtTypingDefs
            };
            tmk = MetaKind::SmtType;
        } else {
            out = Out::DefsTotal;
        }
        let mut is_simple = true;
        let mut needs_partial = false;
        // the heads and the bodies of the cases
        let mut heads = Vec::with_capacity(cases_of.len());
        let mut prets = Vec::with_capacity(cases_of.len());
        for &c in &cases_of {
            heads.push(child(ck, c, 0)?);
            prets.push(child(ck, c, 1)?);
        }
        let all_rets = ck.mk_expr(Kind::TUPLE, &prets);
        for e in subterms_of_kind(ck, Kind::PROGRAM_CONST, all_rets) {
            // Any recursion through a partial program, or a call of one,
            // makes this one partial.
            if self.partial_def_progs.contains(&e) {
                needs_partial = true;
                is_simple = false;
                break;
            }
            if e != v && !self.simple_def_progs.contains(&e) {
                is_simple = false;
            }
        }
        let mut raw_name = vname.as_str();
        if let Some(rest) = vname.strip_prefix("$eo.l.") {
            match rest.split_once('.') {
                Some((_, name)) if !name.is_empty() => raw_name = name,
                _ => {
                    return Err(check_failure(
                        "namePos != std::string::npos && namePos + 1 < vname.size()",
                        &format!("Malformed linear-pattern program name {vname}"),
                    ));
                }
            }
        }
        if self.partial_exc.contains(raw_name) {
            needs_partial = true;
        }
        // the builtin eo:: operators are all total
        if vname.starts_with("$eo_") && !vname.starts_with("$eo_prog_") {
            needs_partial = false;
        }
        if is_simple {
            self.simple_def_progs.insert(v);
        }
        if needs_partial {
            if !self.has_defs {
                self.has_defs = true;
                self.defs.push_str("mutual\n\n");
            }
            out = Out::Defs;
            decl.push_str("partial ");
            self.partial_def_progs.insert(v);
        } else {
            self.total_def_progs.insert(v);
        }
        // $eo_model is for the verification conditions only
        if vname.starts_with("$eo_model") {
            return Ok(());
        }
        // the conversion from Eunoia to SMT-LIB has a module of its own
        if vname.starts_with("$eo_to_smt") {
            out = if is_simple {
                Out::EoIsObjDefsSimple
            } else {
                Out::EoIsObjDefs
            };
        }
        if vname == "$smtx_model_eval" {
            decl.push_str("noncomputable ");
            out = Out::Smt;
        }
        // The module is settled: a native the program names is named from
        // there.
        self.scope = scope_of(out);
        let _ = write!(decl, "def {}", clean_id(&vname));
        // The leading arguments that every case matches with the same
        // parameter become arguments of the definition.
        let mut macro_start_arg = 1;
        while macro_start_arg < nargs {
            if vctx_args[macro_start_arg - 1] == MetaKind::Eunoia {
                break;
            }
            let mut mv: Option<Term> = None;
            let mut macro_success = true;
            for &hd in &heads {
                let vn = child(ck, hd, macro_start_arg)?;
                if (mv.is_none() && ck.store.kind(vn) == Kind::PARAM) || mv == Some(vn) {
                    mv = Some(vn);
                    continue;
                }
                macro_success = false;
                break;
            }
            if !macro_success {
                break;
            }
            let shown = ck.show(mv.unwrap_or(ck.store.mk_null()));
            let ty = (self.print_meta_type(ck, types[macro_start_arg - 1])?).unwrap_or_default();
            let _ = write!(decl, " ({shown} : {ty})");
            macro_start_arg += 1;
        }
        decl.push_str(" : ");
        for &t in &types[macro_start_arg - 1..nargs - 1] {
            decl.push_str(&self.print_meta_type(ck, t)?.unwrap_or_default());
            decl.push_str(" -> ");
        }
        let ret_type = self.print_meta_type(ck, ret_ty)?.unwrap_or_default();
        decl.push_str(&ret_type);
        if macro_start_arg == nargs {
            // no cases: the definition is its body
            let Some(&ret) = prets.first() else {
                return Err(malformed(&format!(
                    "the program {} has no case",
                    ck.show(v)
                )));
            };
            let body = self.print_emb_term(ck, ret, tmk, true)?;
            decl.push_str(" :=");
            // with let bindings the body starts on a new line already
            if !body.starts_with('\n') {
                decl.push_str("\n  ");
            }
            decl.push_str(&body);
            decl.push_str("\n\n");
            self.buf(out).push_str(&decl);
            return Ok(());
        }
        decl.push('\n');
        let mut cases = String::new();
        // A program whose range is not a Eunoia term cannot get stuck;
        // neither can a definition, which is a macro in Eunoia; and the
        // checker's definitions are known not to need the check.
        if retk == MetaKind::Eunoia && !is_define && !is_checker_def {
            for i in macro_start_arg..nargs {
                if vctx_args[i - 1] != MetaKind::Eunoia {
                    continue;
                }
                // an argument no case matches with a parameter needs no
                // check for stuckness
                let mut matches_param = false;
                for &hd in &heads {
                    if ck.store.kind(child(ck, hd, i)?) == Kind::PARAM {
                        matches_param = true;
                        break;
                    }
                }
                if !matches_param {
                    continue;
                }
                cases.push_str("  | ");
                for j in macro_start_arg..nargs {
                    if j > macro_start_arg {
                        cases.push_str(", ");
                    }
                    cases.push_str(if i == j { "Term.Stuck " } else { "_ " });
                }
                cases.push_str(" => Term.Stuck\n");
            }
        }
        let mut was_default = false;
        for (&hd, &body) in heads.iter().zip(&prets) {
            was_default = true;
            let mut pat_match = String::new();
            let hd_children = ck.store.children(hd).to_vec();
            for (j, &pat) in hd_children.iter().enumerate().skip(macro_start_arg) {
                if j > macro_start_arg {
                    pat_match.push_str(", ");
                }
                pat_match.push_str(&self.print_emb_term(ck, pat, tmk, false)?);
                // the parameters of a pattern are distinct by now
                if ck.store.kind(pat) != Kind::PARAM {
                    was_default = false;
                }
            }
            let ssret = self.print_emb_term(ck, body, tmk, true)?;
            let _ = writeln!(cases, "  | {pat_match} => {ssret}");
        }
        // The datatypes with a stuck term get a last case, unless the
        // program is of the checker, whose definitions are total.
        if !was_default && !is_checker_def && matches!(retk, MetaKind::Eunoia | MetaKind::Proof) {
            cases.push_str("  | ");
            for j in macro_start_arg..nargs {
                if j > macro_start_arg {
                    cases.push_str(", ");
                }
                cases.push('_');
            }
            let _ = writeln!(cases, " => {ret_type}.Stuck");
        }
        let terminating_by = self.terminating_by.get(&vname).cloned();
        let os = self.buf(out);
        os.push_str(&decl);
        os.push_str(&cases);
        if let Some(clause) = terminating_by {
            os.push_str(&clause);
            os.push('\n');
        }
        os.push_str("\n\n");
        Ok(())
    }

    /// The declared constant `e` as a constructor of the inductive of the
    /// embedding it belongs to.
    fn finalize_decl(&mut self, ck: &mut Checker, e: Term) -> Result<()> {
        // A declaration is a case of the datatypes of the embedding, which
        // stand above every module that holds a block of the layer.
        self.scope = "SmtEval";
        if !self.base.begin_finalize_decl(e) {
            return Ok(());
        }
        if ck.show(e) == "$eo_pf" {
            return Ok(());
        }
        let (tk, cnamek) = self.meta_kind(ck, e);
        let cname = clean_smt_id(&cnamek);
        let mut out = match tk {
            MetaKind::Eunoia => Some(DeclOut::EmbedTerm),
            MetaKind::Smt => Some(DeclOut::Smt),
            MetaKind::SmtType => Some(DeclOut::SmtType),
            MetaKind::SmtValue => Some(DeclOut::SmtValue),
            MetaKind::CheckerRule => {
                self.emitted_rules.insert(cname.clone());
                Some(DeclOut::Rule)
            }
            MetaKind::CheckerCmd => Some(DeclOut::Cmd),
            _ => None,
        };
        // A constructor of a datatype the embedding is built over: it goes
        // to an inductive named as the type it returns.
        if out.is_none() && is_embed_datatype_kind(tk) {
            let mut dty = type_of(ck, e)?;
            if ck.store.kind(dty) == Kind::FUNCTION_TYPE {
                dty = child(ck, dty, ck.store.num_children(dty).wrapping_sub(1))?;
            }
            if let Some(name) = self.print_meta_type(ck, dty)? {
                self.embed_dt.entry(name.clone()).or_default();
                out = Some(DeclOut::Embed(name));
            }
        }
        let Some(out) = out else {
            return Ok(());
        };
        let ct = type_of(ck, e)?;
        let attr = ck.attribute_kind(e);
        // opaque symbols are constructors with arguments
        let nopq_args = if attr == Attr::Opaque {
            let n = ck.store.num_children(ct).wrapping_sub(1);
            child(ck, ct, n)?;
            n
        } else {
            0
        };
        if tk == MetaKind::Eunoia
            && let Some(uarity) = self.is_atomic_eo(ck, e, &cnamek)?
        {
            if uarity > MAX_INDEX_ARITY {
                return Err(check_failure(
                    "uarity <= s_maxIndexArity",
                    &format!(
                        "The embedding declares $emb_UOp up to {MAX_INDEX_ARITY} indices, and {} \
                         takes {uarity}; declare the wider constructor in eo_desugar_native.eo \
                         and raise s_maxIndexArity to match",
                        ck.show(e)
                    ),
                ));
            }
            (self.emitted_user_ops).insert((cname.clone(), uarity as u64));
            let etd = &mut self.embed_top_dt[uarity];
            let _ = write!(etd, "  | {cname} : UserOp");
            if uarity > 0 {
                let _ = write!(etd, "{uarity}");
            }
            etd.push('\n');
            return Ok(());
        }
        let mut text = format!("  | {cname} : ");
        if matches!(attr, Attr::Amb | Attr::AmbDatatypeConstructor) {
            return Err(check_failure(
                "attr != Attr::AMB && attr != Attr::AMB_DATATYPE_CONSTRUCTOR",
                "",
            ));
        }
        let mut arg_types = Vec::with_capacity(nopq_args);
        for i in 0..nopq_args {
            // the type the argument has in the embedding
            let mut typ = child(ck, ct, i)?;
            if ck.store.kind(typ) == Kind::QUOTE_TYPE {
                let targ = child(ck, typ, 0)?;
                typ = type_of(ck, targ)?;
            }
            let sst = (self.print_meta_type(ck, typ)?).unwrap_or_else(|| "Term".to_string());
            let _ = write!(text, "{sst} -> ");
            arg_types.push(sst);
        }
        let dt_name = match &out {
            DeclOut::Embed(name) => name.clone(),
            _ => print_meta_type_kind(tk).unwrap_or_default().to_string(),
        };
        text.push_str(&dt_name);
        text.push('\n');
        if tk == MetaKind::Eunoia {
            self.term_cons.push((cname.clone(), arg_types.clone()));
        }
        match out {
            DeclOut::EmbedTerm => self.embed_term_dt.push_str(&text),
            DeclOut::Smt => self.smt_dt.push_str(&text),
            DeclOut::Rule => self.rule_dt.push_str(&text),
            DeclOut::Cmd => self.cmd_dt.push_str(&text),
            DeclOut::SmtType => self.smt_type_dt.push_str(&text),
            DeclOut::SmtValue => self.smt_value_dt.push_str(&text),
            DeclOut::Embed(name) => (self.embed_dt.entry(name).or_default()).push_str(&text),
        }
        // The ordering keys are written in step with the datatypes they
        // order: the tag of a constructor is its index in the datatype.
        if self.ordered.contains(&dt_name) {
            let ncons = self.key_ncons.entry(dt_name.clone()).or_default();
            let key = print_order_key_case(&cname, &arg_types, *ncons);
            *ncons += 1;
            self.key.entry(dt_name).or_default().push_str(&key);
        }
        Ok(())
    }

    /// The `UserOp` inductives: one for each number of indices that got a
    /// constructor.
    fn print_theory_op_defs(&self) -> String {
        const TITLES: [&str; MAX_INDEX_ARITY + 1] = [
            "Ordinary user operators.",
            "User operators with one index.",
            "User operators with two indices.",
            "User operators with three indices.",
            "User operators with four indices.",
            "User operators with five indices.",
        ];
        let mut defs = String::new();
        let mut first = true;
        for (n, cons) in self.embed_top_dt.iter().enumerate() {
            if cons.is_empty() {
                continue;
            }
            // the blank line between two inductives
            if !first {
                defs.push_str("\n\n");
            }
            first = false;
            let name = if n > 0 {
                format!("UserOp{n}")
            } else {
                "UserOp".to_string()
            };
            let _ = write!(
                defs,
                "/-\n{}\n-/\ninductive {name} : Type where\n{cons}\nderiving Repr, DecidableEq, \
                 Inhabited",
                TITLES[n]
            );
        }
        defs
    }

    /// The comparison of each `UserOp` inductive that
    /// `print_theory_op_defs` writes: the text of `$LEAN_EO_USER_OP_CMPS$`.
    fn print_user_op_cmps(&self) -> String {
        let mut os = String::new();
        let mut first = true;
        for (n, cons) in self.embed_top_dt.iter().enumerate() {
            if cons.is_empty() {
                continue;
            }
            if !first {
                os.push_str("\n\n");
            }
            first = false;
            let name = if n > 0 {
                format!("UserOp{n}")
            } else {
                "UserOp".to_string()
            };
            let _ = write!(
                os,
                "@[expose] def {} (a b : {name}) : Ordering :=\n  natCmp a.ctorIdx b.ctorIdx",
                term_cmp_method(&name)
            );
        }
        os
    }

    /// The cases of `termCmp`, one for each constructor of `Term`: the text
    /// of `$LEAN_TERM_CMP$`. Lexicographic: the constructor index first,
    /// then the arguments from the left, each compared by the method its
    /// type names.
    fn print_term_cmp(&self) -> String {
        let mut os = String::new();
        let mut first = true;
        for (cname, args) in &self.term_cons {
            if !first {
                os.push('\n');
            }
            first = false;
            if args.is_empty() {
                let _ = write!(
                    os,
                    "  | .{cname}, b => natCmp (Term.ctorIdx .{cname}) b.ctorIdx"
                );
                continue;
            }
            let _ = write!(os, "  | a@(.{cname}");
            for i in 1..=args.len() {
                let _ = write!(os, " x{i}");
            }
            let _ = write!(os, "), b =>\n    match b with\n    | .{cname}");
            for i in 1..=args.len() {
                let _ = write!(os, " y{i}");
            }
            os.push_str(" =>\n");
            for (i, arg) in args.iter().enumerate() {
                let indent = " ".repeat(6 + 2 * i);
                let call = format!("{} x{} y{}", term_cmp_method(arg), i + 1, i + 1);
                if i + 1 == args.len() {
                    let _ = writeln!(os, "{indent}{call}");
                } else {
                    let _ = writeln!(os, "{indent}match {call} with\n{indent}| .eq =>");
                }
            }
            for i in (1..args.len()).rev() {
                let _ = writeln!(os, "{}| o => o", " ".repeat(6 + 2 * (i - 1)));
            }
            os.push_str("    | _ => natCmp a.ctorIdx b.ctorIdx");
        }
        os
    }

    fn emit(
        &self,
        ck: &mut Checker,
        resource: &str,
        output: &str,
        replacements: &[(&str, String)],
        repl_all: bool,
    ) -> Result<()> {
        let replacements: Vec<Replacement> = (replacements.iter())
            .map(|(tag, text)| (tag.to_string(), text.clone()))
            .collect();
        (self.base.std).emit_resource_file(ck, resource, output, &replacements, repl_all)?;
        Ok(())
    }

    fn finalize_checker(&self, ck: &mut Checker) -> Result<()> {
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_checker_term_order.lean",
            "plugins/lean_meta/lean_meta_checker_term_order_gen.lean",
            &[
                ("$LEAN_EO_USER_OP_CMPS$", self.print_user_op_cmps()),
                ("$LEAN_TERM_CMP$", self.print_term_cmp()),
            ],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_checker_term.lean",
            "plugins/lean_meta/lean_meta_checker_term_gen.lean",
            &[
                ("$LEAN_TERM_DEF$", self.embed_term_dt.clone()),
                ("$LEAN_EO_THEORY_OP_DEFS$", self.print_theory_op_defs()),
            ],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_checker.lean",
            "plugins/lean_meta/lean_meta_checker_gen.lean",
            &[
                ("$NATIVE_DEFS$", self.natives.defs("Eo")),
                ("$LEAN_DEFS$", self.defs.clone()),
                ("$LEAN_DEFS_TOTAL$", self.defs_total.clone()),
                ("$LEAN_CHECKER_RULE_DEF$", self.rule_dt.clone()),
                ("$LEAN_CHECKER_CMD_DEF$", self.cmd_dt.clone()),
                ("$LEAN_CHECKER_DEFS$", self.eo_checker.clone()),
                ("$LEAN_EO_IS_REFUTATION_DEF$", self.eo_is_ref.clone()),
            ],
            false,
        )
    }

    /// The Lean term for the operator without indices whose name in the
    /// input is `surface`; empty if it was not written.
    fn get_parser_op_term(&self, surface: &str) -> String {
        for op in &self.parser_ops {
            let generated = clean_smt_id(&op.generated);
            if op.surface == surface && self.emitted_user_ops.contains(&(generated.clone(), 0)) {
                return format!("(Term.UOp UserOp.{generated})");
            }
        }
        String::new()
    }

    /// A record of the operator whose generated name is `generated` and
    /// that was written.
    fn get_parser_op_for_generated(&self, generated: &str) -> Option<ParserOp> {
        (self.parser_ops.iter())
            .find(|op| op.generated == generated && self.is_emitted_parser_op(op))
            .cloned()
    }

    fn is_emitted_parser_op(&self, op: &ParserOp) -> bool {
        (self.emitted_user_ops).contains(&(clean_smt_id(&op.generated), op.index_arity))
    }

    /// Adds to `ops` the declaration of the operator `op` under `name`.
    fn print_parser_op(
        &mut self,
        st: &mut State,
        op: &ParserOp,
        name: &str,
        ops: &mut String,
    ) -> Result<()> {
        let generated = clean_smt_id(&op.generated);
        let mut term = String::new();
        if op.index_arity == 0 {
            let _ = write!(term, "(Term.UOp UserOp.{generated})");
        } else {
            let n = op.index_arity;
            let _ = write!(term, "(Term.UOp{n} UserOp{n}.{generated}");
            for i in 0..n {
                let _ = write!(term, " x{}", i + 1);
            }
            term.push(')');
        }
        let mut arity = String::new();
        match op.attr.as_str() {
            "left-assoc" => arity = ".leftAssoc".to_string(),
            "right-assoc" => arity = ".rightAssoc".to_string(),
            "left-assoc-nil" => arity = format!(".leftAssocNil (parserNil {term})"),
            "right-assoc-nil" => arity = format!(".rightAssocNil (parserNil {term})"),
            "left-assoc-ns-nil" => {
                arity = format!(".leftAssocNonSingletonNil (parserNil {term})");
            }
            "right-assoc-ns-nil" => {
                arity = format!(".rightAssocNonSingletonNil (parserNil {term})");
            }
            "arg-list" => {
                // the operator gathers its arguments into a list
                let cons_term = self.get_parser_op_term(&op.connector);
                if !cons_term.is_empty() {
                    arity = format!(
                        ".argList (fun ts => Logos.Parser.rightAssocNil Term.Apply {cons_term} \
                         (parserNil {cons_term}) ts)"
                    );
                }
            }
            "chainable" | "pairwise" => {
                let connector_term = self.get_parser_op_term(&op.connector);
                if !connector_term.is_empty() {
                    arity = format!(
                        ".{} (fun ts => Logos.Parser.rightAssocNil Term.Apply {connector_term} \
                         (parserNil {connector_term}) ts)",
                        op.attr
                    );
                }
            }
            _ => {}
        }
        // The first argument of a binder may be a sorted variable list,
        // which is read into the list its connector builds; the list ends
        // in the connector's nil at the type of the binder's first
        // argument.
        let mut binder = String::new();
        if op.attr == "binder" {
            let cons = st.get_var(&op.connector);
            let b = st.get_var(&op.generated);
            let ck = &mut st.ck;
            let bt = match b {
                Some(b) => ck.get_type(b, None),
                None => None,
            };
            let mut list_type = None;
            if let Some(bt) = bt
                && ck.store.kind(bt) == Kind::FUNCTION_TYPE
            {
                let mut lt = child(ck, bt, 0)?;
                // A binder whose type is not ground is a parameterized
                // constant: its first argument type quotes the parameter
                // that stands for the list.
                if ck.store.kind(lt) == Kind::QUOTE_TYPE {
                    let quoted = child(ck, lt, 0)?;
                    lt = type_of(ck, quoted)?;
                }
                list_type = Some(lt);
            }
            match (cons, list_type) {
                (Some(cons), Some(list_type)) if ck.store.is_ground(list_type) => {
                    let cons_term = self.print_emb_term(ck, cons, MetaKind::None, false)?;
                    let list_type_term =
                        self.print_emb_term(ck, list_type, MetaKind::None, false)?;
                    binder = format!(
                        "(fun vs => Logos.Parser.rightAssocNil Term.Apply {cons_term} (fun _ => \
                         __eo_nil {cons_term} {list_type_term}) vs)"
                    );
                    self.parser_has_binder = true;
                }
                _ => ck.warn(&format!(
                    "Lean parser: could not resolve the list constructor {} of binder {name}",
                    op.connector
                )),
            }
        }
        if arity.is_empty() {
            arity = format!(".exact {}", op.term_arity);
        }
        // `Logos.Parser.Arity` does not model every attribute.
        if arity.starts_with(".leftAssocNil")
            || arity.starts_with(".pairwise")
            || arity.contains("NonSingletonNil")
        {
            st.ck.warn(&format!(
                "Lean parser: operator {name} has argument-list attribute {}, which \
                 Logos.Parser.Arity does not model",
                op.attr
            ));
        }
        let _ = writeln!(ops, "  {{ name := {}", quote_lean_string(name));
        let _ = writeln!(ops, "    indexArity := {}", op.index_arity);
        let _ = writeln!(ops, "    arity := {arity}");
        ops.push_str("    build := fun\n      | [");
        for i in 0..op.index_arity {
            if i > 0 {
                ops.push_str(", ");
            }
            let _ = write!(ops, "x{}", i + 1);
        }
        let _ = writeln!(ops, "] => some {term}");
        if binder.is_empty() {
            ops.push_str("      | _ => none },\n");
            return Ok(());
        }
        ops.push_str("      | _ => none\n");
        let _ = writeln!(ops, "    binder := some {binder} }},");
        Ok(())
    }

    /// Writes the parser of proofs for the signature.
    fn finalize_parser(&mut self, st: &mut State) -> Result<()> {
        // The operators the template declares itself; a definition of the
        // same name does not override one.
        let mut op_names: BTreeSet<String> = ["Bool", "false", "true", "->", "@list"]
            .into_iter()
            .map(str::to_string)
            .collect();
        let mut ops = String::new();
        let mut seen_ops = HashSet::new();
        for op in self.parser_ops.clone() {
            if !self.is_emitted_parser_op(&op) {
                continue;
            }
            let op_key = format!(
                "{}\n{}\n{}\n{}\n{}",
                op.surface,
                clean_smt_id(&op.generated),
                op.index_arity,
                op.term_arity,
                op.attr
            );
            if !seen_ops.insert(op_key) {
                continue;
            }
            self.print_parser_op(st, &op, &op.surface, &mut ops)?;
            op_names.insert(op.surface);
        }
        let mut rules = String::new();
        let mut seen_rules = HashSet::new();
        let mut first_rule = true;
        for (surface, generated) in &self.parser_rules {
            let generated = clean_smt_id(generated);
            if !self.emitted_rules.contains(&generated) || !seen_rules.insert(surface) {
                continue;
            }
            if !first_rule {
                rules.push_str(",\n");
            }
            first_rule = false;
            let _ = write!(rules, "  ({}, .{generated})", quote_lean_string(surface));
        }
        if !first_rule {
            rules.push('\n');
        }
        let mut def_macros = String::new();
        self.finalize_parse_defs(st, &op_names, &mut ops, &mut def_macros)?;
        // The variables a binder binds are `(eo::var name type)`; a
        // calculus with no binder is left without them.
        let mk_var = if self.parser_has_binder {
            "  mkVar := some fun name ty => Term.Var (Term.String (native_string_lit name)) ty\n"
        } else {
            ""
        };
        // Testers and updaters carry a generic datatype operator as their
        // index, which the parser instantiates. A calculus with no
        // operator of one index has no Term.UOp1.
        let indexed_view = if self.embed_top_dt[1].is_empty() {
            ""
        } else {
            "  | .UOp1 op index => .indexed (Term.UOp1 op) index\n"
        };
        self.emit(
            &mut st.ck,
            "plugins/lean_meta/lean_meta_parser.lean",
            "plugins/lean_meta/lean_meta_parser_gen.lean",
            &[
                ("$LEAN_PARSER_OPS$", ops),
                ("$LEAN_PARSER_RULES$", rules),
                ("$LEAN_PARSER_MACROS$", def_macros),
                ("$LEAN_PARSER_INDEXED_VIEW$", indexed_view.to_string()),
                ("$LEAN_PARSER_MK_VAR$", mk_var.to_string()),
            ],
            false,
        )
    }

    /// Adds the parser's tables for the definitions of the input: to `ops`
    /// an operator for each, and to `macros` the identifiers of those that
    /// take arguments. `op_names` are the names declared as operators
    /// already.
    fn finalize_parse_defs(
        &mut self,
        st: &mut State,
        op_names: &BTreeSet<String>,
        ops: &mut String,
        macros: &mut String,
    ) -> Result<()> {
        // the parser is written over Logos
        self.scope = "Eo";
        let mut seen = HashSet::new();
        for (surface, def) in self.parse_defs.clone() {
            if !seen.insert(surface.clone()) {
                continue;
            }
            let mut body = def;
            let mut params = Vec::new();
            if st.ck.store.kind(body) == Kind::LAMBDA {
                let vars = child(&st.ck, body, 0)?;
                params = st.ck.store.children(vars).to_vec();
                body = child(&st.ck, body, 1)?;
            }
            // The other free variables of the body are implicit parameters,
            // which Eunoia finds by unification; the parser cannot.
            let fvs = st.ck.get_variables(&[body]);
            if fvs.iter().any(|v| !params.contains(v)) {
                continue;
            }
            // A nullary operator cannot shadow an operator of the same
            // name: the declaration of the signature is kept.
            if params.is_empty() && op_names.contains(&surface) {
                continue;
            }
            if params.is_empty() && st.ck.store.num_children(body) == 0 {
                // A definition without arguments whose body is an operator
                // is an alias: declared as the operator is, so that it has
                // its indices and its attribute.
                let shown = st.ck.show(body);
                if let Some(op) = self.get_parser_op_for_generated(&shown) {
                    self.print_parser_op(st, &op, &surface, ops)?;
                    continue;
                }
            }
            // not let-bound: it is the argument of a constructor below
            let body_term = self.print_emb_term(&mut st.ck, body, MetaKind::None, false)?;
            if params.is_empty() {
                // a definition without arguments denotes its body
                let _ = writeln!(ops, "  {{ name := {}", quote_lean_string(&surface));
                ops.push_str("    indexArity := 0\n    arity := .exact 0\n    build := fun\n");
                let _ = writeln!(ops, "      | [] => some {body_term}");
                ops.push_str("      | _ => none },\n");
                continue;
            }
            // A definition with arguments is a macro: its body is an
            // operator indexed by the arguments, and the macro applies that
            // operator to its parameters.
            let binders: Vec<String> = (params.iter())
                .map(|&v| clean_smt_id(&st.ck.show(v)))
                .collect();
            let distinct: HashSet<&String> = binders.iter().collect();
            if distinct.len() < binders.len() {
                st.ck.warn(&format!(
                    "Lean parser: omit definition {surface}, whose parameters do not have \
                     distinct generated names"
                ));
                continue;
            }
            let op_name = mk_parse_def_name(&surface);
            let _ = writeln!(ops, "  {{ name := {}", quote_lean_string(&op_name));
            let _ = writeln!(ops, "    indexArity := {}", params.len());
            ops.push_str("    arity := .exact 0\n    build := fun\n      | [");
            ops.push_str(&binders.join(", "));
            let _ = writeln!(ops, "] => some {body_term}");
            ops.push_str("      | _ => none },\n");
            let _ = writeln!(macros, "  ({},", quote_lean_string(&surface));
            let args: Vec<String> = (1..=params.len())
                .map(|i| format!("{}{i}", mk_parse_def_name("arg")))
                .collect();
            let quoted: Vec<String> = args.iter().map(|a| quote_lean_string(a)).collect();
            let _ = writeln!(macros, "    {{ params := [{}]", quoted.join(", "));
            let _ = write!(
                macros,
                "      body := .expr [.atom \"_\", .atom {}",
                quote_lean_string(&op_name)
            );
            for a in &quoted {
                let _ = write!(macros, ", .atom {a}");
            }
            macros.push_str("] }),\n");
        }
        Ok(())
    }

    /// The ordering keys of the datatypes the configuration says are
    /// ordered, in one mutual block: the text of the `$LEAN_SMT_KEYS$` hole.
    fn print_keys(&self) -> String {
        let mut keys = String::new();
        for (name, cases) in &self.key {
            let _ = writeln!(
                keys,
                "@[expose] def {} : {name} -> Key\n{cases}",
                get_order_key_method(name)
            );
        }
        keys
    }

    /// Whether `name` is SmtType, SmtTerm or a declared datatype that holds
    /// no value: one that stands in SmtSyntax, not in SmtModelDefs.
    fn is_syntax_datatype(&self, name: &str) -> bool {
        if name == "SmtType" || name == "SmtTerm" {
            return true;
        }
        (self.embed_dt.get(name)).is_some_and(|text| !text.contains("SmtValue"))
    }

    /// Whether the signature `t` names a value or a model, which puts an
    /// SMT-LIB definition in SmtModel rather than in SmtTyping.
    fn names_model_type(&self, ck: &Checker, t: Term) -> Result<bool> {
        let mut visit = vec![t];
        while let Some(t) = visit.pop() {
            let k = self.type_meta_kind(ck, t);
            if k == MetaKind::Eunoia {
                // not a type of the embedding, but what holds them, e.g. an
                // arrow
                visit.extend(ck.store.children(t).iter().rev());
                continue;
            }
            if k == MetaKind::SmtBuiltin {
                continue;
            }
            let name = if k.is_embed() {
                get_embed_type_name(ck, get_embed_type_app(ck, t))?
            } else {
                print_meta_type_kind(k).unwrap_or_default().to_string()
            };
            if !self.is_syntax_datatype(&name) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The inductives of the datatypes the target declared: those of
    /// SmtSyntax if `syntax`, else those of SmtModelDefs.
    fn print_embed_datatypes(&self, syntax: bool) -> String {
        let mut defs = String::new();
        for (name, cons) in &self.embed_dt {
            if self.is_syntax_datatype(name) != syntax {
                continue;
            }
            // What holds a value holds a real, whose equality is classical
            // and which has no Repr.
            let deriving = if syntax {
                "deriving Repr, DecidableEq, Inhabited"
            } else {
                "deriving DecidableEq, Inhabited"
            };
            let _ = write!(
                defs,
                "/-\nThe {name} of the embedding.\n-/\ninductive {name} : Type where\n\
                 {cons}{deriving}\n\n"
            );
        }
        defs
    }

    fn finalize_smt_model(&self, ck: &mut Checker) -> Result<()> {
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_syntax.lean",
            "plugins/lean_meta/lean_meta_smt_syntax_gen.lean",
            &[
                ("$LEAN_SMT_TYPE_DEF$", self.smt_type_dt.clone()),
                ("$LEAN_SMT_TERM_DEF$", self.smt_dt.clone()),
                ("$LEAN_SMT_EMBED_DEFS$", self.print_embed_datatypes(true)),
            ],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_typing.lean",
            "plugins/lean_meta/lean_meta_smt_typing_gen.lean",
            &[
                ("$LEAN_SMT_TYPING_DEFS$", self.smt_typing_defs.clone()),
                ("$NATIVE_DEFS$", self.natives.defs("SmtTyping")),
            ],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_model_defs.lean",
            "plugins/lean_meta/lean_meta_smt_model_defs_gen.lean",
            &[
                ("$LEAN_SMT_VALUE_DEF$", self.smt_value_dt.clone()),
                ("$LEAN_SMT_EMBED_DEFS$", self.print_embed_datatypes(false)),
            ],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_value_order.lean",
            "plugins/lean_meta/lean_meta_smt_value_order_gen.lean",
            &[("$LEAN_SMT_KEYS$", self.print_keys())],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_model.lean",
            "plugins/lean_meta/lean_meta_smt_model_gen.lean",
            &[
                ("$LEAN_SMT_EVAL_DEFS$", self.smt_defs.clone()),
                ("$LEAN_SMT_EVAL$", self.smt.clone()),
                ("$NATIVE_DEFS$", self.natives.defs("Smtm")),
            ],
            false,
        )
    }

    fn finalize_spec(&self, ck: &mut Checker) -> Result<()> {
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_translate.lean",
            "plugins/lean_meta/lean_meta_smt_translate_gen.lean",
            &[
                ("$LEAN_EO_IS_OBJ_DEFS$", self.eo_is_obj_defs.clone()),
                (
                    "$LEAN_EO_IS_OBJ_SIMPLE_DEFS$",
                    self.eo_is_obj_defs_simple.clone(),
                ),
            ],
            false,
        )?;
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_spec.lean",
            "plugins/lean_meta/lean_meta_spec_gen.lean",
            &[],
            false,
        )
    }

    fn finalize_lemmas(&self, ck: &mut Checker) -> Result<()> {
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_rule_lemmas.lean",
            "plugins/lean_meta/lean_meta_rule_lemmas_gen.lean",
            &[
                ("$EO_RULE_LEMMA_INCLUDE$", self.rl_include.clone()),
                ("$EO_RULE_LEMMA_STEP_CASES$", self.rl_include_step.clone()),
                (
                    "$EO_RULE_LEMMA_STEP_POP_CASES$",
                    self.rl_include_step_pop.clone(),
                ),
            ],
            false,
        )
    }

    /// Adds the case of the rule `prule` to the lemma about steps (or about
    /// popping steps), and writes the rule's own file.
    fn print_step_case(&mut self, ck: &mut Checker, prule: &str, is_pop: bool) -> Result<()> {
        let mut out = String::new();
        let pop = if is_pop { "pop_" } else { "" };
        let _ = writeln!(out, "  | {prule} =>");
        let _ = write!(out, "      exact cmd_step_{pop}facts_of_rule_properties");
        if is_pop {
            out.push_str(" M hM root tail A premises hsRoot hsRootStable hSuffix <|\n");
        } else {
            out.push_str(" M hM s premises hs hsStable <| by\n        intro N hN _hAgree\n");
        }
        if is_pop {
            let _ = writeln!(
                out,
                "        cmd_step_pop_{prule}_properties A root args premises\n          hATrans \
                 hATy hPremisesTrans hPremisesTy hResultTy"
            );
        } else {
            let _ = writeln!(
                out,
                "        exact cmd_step_{prule}_properties N hN s args premises\n          (by \
                 simpa using hCmdTrans) hPremisesBool hResultTy"
            );
        }
        if is_pop {
            self.rl_include_step_pop.push_str(&out);
        } else {
            self.rl_include_step.push_str(&out);
        }
        let resource = if is_pop {
            "plugins/lean_meta/lean_meta_rule_pop.lean"
        } else {
            "plugins/lean_meta/lean_meta_rule.lean"
        };
        self.emit(
            ck,
            resource,
            &format!("plugins/lean_meta/rules/lean_meta_rule_{prule}_gen.lean"),
            &[("$EO_RULE$", prule.to_string())],
            true,
        )
    }
}

/// The comparison a term-order case calls for an argument of Lean type
/// `t`: the type with any `native_` prefix dropped, its first letter
/// lowered and `Cmp` appended, e.g. `intCmp` for `native_Int`.
fn term_cmp_method(t: &str) -> String {
    let base = t.strip_prefix("native_").unwrap_or(t);
    let mut out = String::with_capacity(base.len() + 3);
    let mut chars = base.chars();
    if let Some(c) = chars.next() {
        out.push(c.to_ascii_lowercase());
    }
    out.push_str(chars.as_str());
    out.push_str("Cmp");
    out
}

/// The case of the ordering key for the constructor `cname`, whose index
/// in its datatype is `tag` and whose arguments have the Lean types
/// `arg_types`: `(node tag [k1 x1, ..., kn xn])`, where `ki` is the key
/// method of the type of argument `i`.
fn print_order_key_case(cname: &str, arg_types: &[String], tag: usize) -> String {
    let mut keys = String::new();
    for (i, t) in arg_types.iter().enumerate() {
        let method = get_order_key_method(t);
        if i > 0 {
            keys.push_str(", ");
        }
        let _ = write!(keys, "{method} x{}", i + 1);
    }
    let mut os = format!("  | .{cname}");
    for i in 0..arg_types.len() {
        let _ = write!(os, " x{}", i + 1);
    }
    let _ = writeln!(os, " => node {tag} [{keys}]");
    os
}

impl Plugin for LeanMeta {
    fn bind(&mut self, st: &mut State, _name: &str, e: Term) -> Result<()> {
        if st.ck.store.kind(e) != Kind::CONST {
            return Ok(());
        }
        self.finalize_decl(&mut st.ck, e)
    }

    fn define_program(&mut self, st: &mut State, v: Term, prog: Option<Term>) -> Result<()> {
        // a forward declaration
        let Some(prog) = prog else {
            return Ok(());
        };
        // Lean's patterns are linear
        for (p, def) in linear_patterns::linearize(&mut st.ck, v, prog)? {
            self.prog_defs.push(p);
            self.prog_to_def.insert(p, def);
        }
        Ok(())
    }

    fn define(&mut self, st: &mut State, name: &str, e: Term) -> Result<()> {
        let ck = &mut st.ck;
        if is_parse_def_name(name) {
            // kept by the desugar stage for the parser of proofs only
            let surface = name.strip_prefix(PARSE_DEF_PREFIX).unwrap_or(name);
            self.parse_defs.push((surface.to_string(), e));
            return Ok(());
        }
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
            Some((symbol, prog)) => {
                self.prog_defs.push(symbol);
                self.prog_to_def.insert(symbol, prog);
                self.prog_is_define.insert(symbol);
            }
            None => {
                let any = ck.mk_any();
                let symbol = ck.mk_symbol(SymbolKind::ProgramConst, name, any);
                self.prog_defs.push(symbol);
                self.prog_to_def.insert(symbol, e);
            }
        }
        Ok(())
    }

    fn echo(&mut self, st: &mut State, msg: &str) -> Result<bool> {
        if let Some(rest) = msg.strip_prefix("lean-parser-op ") {
            let mut words = Words { rest };
            let mut read = || {
                Some(ParserOp {
                    surface: words.word()?.to_string(),
                    generated: words.word()?.to_string(),
                    index_arity: words.number()?,
                    term_arity: words.number()?,
                    attr: words.word()?.to_string(),
                    connector: words.word()?.to_string(),
                })
            };
            match read() {
                Some(op) => self.parser_ops.push(op),
                None => (st.ck).warn(&format!("Malformed lean parser operator metadata: {msg}")),
            }
            return Ok(false);
        }
        if let Some(rest) = msg.strip_prefix("lean-parser-rule ") {
            let mut words = Words { rest };
            match (words.word(), words.word()) {
                (Some(surface), Some(generated)) => {
                    (self.parser_rules).push((surface.to_string(), generated.to_string()));
                }
                _ => (st.ck).warn(&format!("Malformed lean parser rule metadata: {msg}")),
            }
            return Ok(false);
        }
        let Some(rest) = msg.strip_prefix("lean-meta ") else {
            return Ok(true);
        };
        let eosc = rest.split(' ').next().unwrap_or_default();
        if st.get_var(eosc).is_none() {
            return Err(Error::fatal(format!(
                "When making Lean theorem, could not find program {eosc}"
            )));
        }
        let prog_name = clean_id(eosc);
        if self.base.conjecture_type == ConjectureType::Vc {
            let prule = match prog_name.strip_prefix(&clean_id("$eo_prog_")) {
                Some(prule) if !prule.is_empty() => prule,
                _ => {
                    return Err(Error::fatal(format!(
                        "Malformed lean-meta program name {eosc}; expected $eo_prog_<rule>"
                    )));
                }
            };
            let mut chars = prule.chars();
            let first = chars.next().map_or(' ', |c| c.to_ascii_uppercase());
            let _ = writeln!(
                self.rl_include,
                "import $EO_CALC$.Proofs.Rules.{first}{}",
                chars.as_str()
            );
            // TODO in the C++: do not hardcode this
            self.print_step_case(&mut st.ck, prule, prule == "scope")?;
        }
        Ok(false)
    }

    fn finalize(&mut self, st: &mut State) -> Result<()> {
        self.finalize_programs(&mut st.ck)?;
        // a refutation is when the method returns true
        self.eo_is_ref.push_str(
            "  | intro (F : CArgList) (c : CCmdList) : \n    (__eo_checker_is_refutation F c) = \
             true -> (eo_is_refutation F c)\n",
        );
        if self.rule_dt.is_empty() {
            self.rule_dt.push_str("  | none : CRule\n");
        }
        self.defs_total.push_str("end\n\n");
        if self.has_defs {
            self.defs.push_str("end\n\n");
        }
        // The checker names UserOp whether or not the signature has an
        // operator without indices, and an inductive with no constructor
        // cannot derive what Term asks of it.
        if self.embed_top_dt[0].is_empty() {
            self.embed_top_dt[0].push_str("  | None : UserOp\n");
        }
        if self.generate_parser {
            self.finalize_parser(st)?;
        }
        let ck = &mut st.ck;
        // Every module has now said what of the native layer it names, so
        // the modules that hold a block of it can be written.
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_eval.lean",
            "plugins/lean_meta/lean_meta_smt_eval_gen.lean",
            &[("$NATIVE_DEFS$", self.natives.defs("SmtEval"))],
            false,
        )?;
        // the reals of the model are fixed text
        self.emit(
            ck,
            "plugins/lean_meta/lean_meta_smt_real.lean",
            "plugins/lean_meta/lean_meta_smt_real_gen.lean",
            &[],
            false,
        )?;
        self.finalize_checker(ck)?;
        self.finalize_smt_model(ck)?;
        self.finalize_spec(ck)?;
        self.finalize_lemmas(ck)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifiers() {
        assert_eq!(clean_smt_id("end"), "__eo_end");
        assert_eq!(clean_smt_id("variable"), "__eo_variable");
        assert_eq!(clean_smt_id("str.++"), "str_concat");
        assert_eq!(clean_smt_id("a+b-c*d"), "aplusbnegcmultd");
        // `=>` goes before `<=`, which goes before `<`
        assert_eq!(clean_smt_id("=>"), "imp");
        assert_eq!(clean_smt_id("<="), "leq");
        assert_eq!(clean_smt_id(">="), "geq");
        assert_eq!(clean_smt_id("<=>"), "ltimp");
        assert_eq!(clean_smt_id("@@pair"), "_at__at_pair");
        assert_eq!(clean_smt_id("$eo_x/y^2"), "__eo_xqdivyexp2");
        assert_eq!(clean_id("$eo_prog_"), "__eo_prog_");
        assert_eq!(clean_id("$eo_prog_and-elim"), "__eo_prog_and_elim");
        assert_eq!(clean_id("end"), "__eo_end");
        assert_eq!(
            quote_lean_string("a\"b\\c\n\r\t"),
            "\"a\\\"b\\\\c\\n\\r\\t\""
        );
        assert!(is_integer("0123"));
        assert!(!is_integer(""));
        assert!(!is_integer("-1"));
    }

    #[test]
    fn order_key_methods() {
        assert_eq!(get_order_key_method("ModelId"), "modelIdKey");
        assert_eq!(get_order_key_method("SmtDatatypeDecl"), "datatypeDeclKey");
        assert_eq!(get_order_key_method("native_Int"), "intKey");
        assert_eq!(get_order_key_method("Smt"), "Key");
        assert_eq!(get_order_key_method("native_"), "Key");
        assert_eq!(get_order_key_method("Term"), "termKey");
    }

    #[test]
    fn words_as_a_stream_reads_them() {
        let mut w = Words {
            rest: "  and\t$eoo_and 0 12x -1 +7 99999999999999999999 z",
        };
        assert_eq!(w.word(), Some("and"));
        assert_eq!(w.word(), Some("$eoo_and"));
        assert_eq!(w.number(), Some(0));
        // a number ends where its digits do
        assert_eq!(w.number(), Some(12));
        assert_eq!(w.word(), Some("x"));
        assert_eq!(w.number(), Some(u64::MAX));
        assert_eq!(w.number(), Some(7));
        // too large for the type
        assert_eq!(w.number(), None);
        let mut w = Words { rest: " x" };
        assert_eq!(w.number(), None);
        let mut w = Words { rest: " \t" };
        assert_eq!(w.word(), None);
    }
}
