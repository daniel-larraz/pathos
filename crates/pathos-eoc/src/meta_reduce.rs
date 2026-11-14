//! What the meta-reduction backends share (`plugins/meta_reduce_plugin.cpp`
//! and the meta-kinds of `plugins/utils.cpp` in Ethos): which datatype of
//! the final deep embedding each symbol of a desugared signature belongs
//! to.

use std::collections::{BTreeMap, HashSet};

use pathos_check::Checker;
use pathos_syntax::{Error, Result};
use pathos_term::{Kind, SymbolKind, Term, TermData};

use crate::std_plugin::StdPlugin;

/// The datatype of the deep embedding a term belongs to.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum MetaKind {
    Eunoia,
    Smt,
    SmtType,
    SmtValue,
    SmtMap,
    SmtSeq,
    /// A builtin SMT-LIB term.
    SmtBuiltin,
    /// A datatype declared by a `$native_embed_eo` type.
    EoEmbed,
    /// A datatype declared by a `$native_embed_smt` type.
    SmtEmbed,
    /// A datatype declared by a `$native_embed_checker` type.
    CheckerEmbed,
    None,
}

impl MetaKind {
    pub fn name(self) -> &'static str {
        match self {
            MetaKind::Eunoia => "EUNOIA",
            MetaKind::Smt => "SMT",
            MetaKind::SmtBuiltin => "SMT_BUILTIN",
            MetaKind::SmtType => "SMT_TYPE",
            MetaKind::SmtValue => "SMT_VALUE",
            MetaKind::SmtMap => "SMT_MAP",
            MetaKind::SmtSeq => "SMT_SEQ",
            MetaKind::EoEmbed => "EO_EMBED",
            MetaKind::SmtEmbed => "SMT_EMBED",
            MetaKind::CheckerEmbed => "CHECKER_EMBED",
            MetaKind::None => "NONE",
        }
    }

    /// The prefix of the names of the kind in the embedding, e.g. `eo.`.
    pub fn prefix(self) -> Result<&'static str> {
        Ok(match self {
            MetaKind::Eunoia => "eo.",
            MetaKind::Smt => "sm.",
            MetaKind::SmtType => "tsm.",
            MetaKind::SmtValue => "vsm.",
            MetaKind::SmtMap => "msm.",
            MetaKind::SmtSeq => "ssm.",
            // builtin symbols have no prefix; this marks one that reaches
            // the output
            MetaKind::SmtBuiltin => "?",
            _ => {
                return Err(Error::fatal(format!(
                    "No prefix for meta-kind {}",
                    self.name()
                )));
            }
        })
    }
}

/// The kind of conjecture a backend writes.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ConjectureType {
    /// A verification condition for an SMT solver.
    Vc,
    /// A syntax-guided synthesis conjecture.
    Sygus,
}

/// `t` without the `eo::requires` guards around it.
fn strip_requires(ck: &Checker, t: Term) -> Term {
    let mut ret = t;
    while let TermData::Eval(pathos_term::EvalOp::Requires, _) = ck.store.data(ret) {
        match ck.store.children(ret).get(2) {
            Some(&inner) => ret = inner,
            None => break,
        }
    }
    ret
}

/// The name of `e`, or the empty string if `e` has children. This is the
/// name a symbol was bound to, not how it is printed: `|foo bar|` has the
/// name `foo bar`.
pub fn get_name(ck: &Checker, e: Term) -> String {
    if ck.store.num_children(e) != 0 {
        return String::new();
    }
    if let Some(name) = ck.store.symbol_name(e) {
        return name.to_string();
    }
    if let Some(lit) = ck.store.lit(e) {
        return lit.to_string();
    }
    // Type and the like print by their builtin names
    ck.show(e)
}

/// Whether `e` is a constructor of a datatype of the embedding: a symbol
/// whose name begins with `$emb_`.
pub fn is_embed_cons(ck: &Checker, e: Term) -> bool {
    get_name(ck, e).starts_with("$emb_")
}

/// Whether `app` is an opaque application of `$native_apply_*` or
/// `$native_type_*` to an SMT-LIB identifier.
pub fn is_smt_apply_app(ck: &Checker, app: Term) -> bool {
    let children = ck.store.children(app);
    if ck.store.kind(app) != Kind::APPLY_OPAQUE
        || children.len() <= 1
        || ck.store.kind(children[1]) != Kind::STRING
    {
        return false;
    }
    let sname = get_name(ck, children[0]);
    sname.starts_with("$native_apply_") || sname.starts_with("$native_type_")
}

/// If `typ`, or the range of `typ` if it is a function type, is a
/// `$native_embed_*` symbol applied to an SMT-LIB identifier, that
/// application.
pub fn get_embed_type_app(ck: &Checker, typ: Term) -> Option<Term> {
    let mut t = strip_requires(ck, typ);
    while ck.store.kind(t) == Kind::FUNCTION_TYPE {
        t = strip_requires(ck, *ck.store.children(t).last()?);
    }
    let children = ck.store.children(t);
    (ck.store.kind(t) == Kind::APPLY_OPAQUE
        && children.len() == 2
        && ck.store.kind(children[1]) == Kind::STRING
        && get_name(ck, children[0]).starts_with("$native_embed_"))
    .then_some(t)
}

/// The name of the datatype a `$native_embed_*` application carries.
pub fn get_embed_type_name(ck: &Checker, app: Option<Term>) -> Result<String> {
    let app = app.unwrap_or(ck.store.mk_null());
    let children = ck.store.children(app);
    if ck.store.kind(app) != Kind::APPLY_OPAQUE
        || children.len() != 2
        || ck.store.kind(children[1]) != Kind::STRING
    {
        return Err(Error::fatal(format!(
            "MetaReducePlugin: bad embed type application {}",
            ck.show(app)
        )));
    }
    Ok(get_name(ck, children[1]))
}

/// Whether `app` is an application of a program.
pub fn is_program_app(ck: &Checker, app: Term) -> bool {
    ck.store.kind(app) == Kind::APPLY
        && (ck.store.children(app).first())
            .is_some_and(|&hd| ck.store.kind(hd) == Kind::PROGRAM_CONST)
}

pub struct MetaReduce {
    pub std: StdPlugin,
    pub conjecture_type: ConjectureType,
    /// The meta-kind of each `$emb_` constructor prefix, e.g. `vsm`.
    pub prefix_to_meta_kind: BTreeMap<String, MetaKind>,
    /// The meta-kind of each type of the embedding, by name.
    type_to_meta_kind: BTreeMap<String, MetaKind>,
    /// The declarations seen so far.
    decl_seen: HashSet<Term>,
}

impl MetaReduce {
    pub fn new(conjecture_type: ConjectureType) -> Result<MetaReduce> {
        let entries =
            |pairs: &[(&str, MetaKind)]| pairs.iter().map(|&(n, k)| (n.to_string(), k)).collect();
        Ok(MetaReduce {
            std: StdPlugin::new()?,
            conjecture_type,
            prefix_to_meta_kind: entries(&[
                ("sm", MetaKind::Smt),
                ("tsm", MetaKind::SmtType),
                ("vsm", MetaKind::SmtValue),
                ("msm", MetaKind::SmtMap),
                ("ssm", MetaKind::SmtSeq),
            ]),
            // The datatypes whose constructors the templates give are not
            // here: `$native_embed_*` types carry their names.
            type_to_meta_kind: entries(&[
                ("$smt_Term", MetaKind::Smt),
                ("$smt_Type", MetaKind::SmtType),
                ("$smt_Value", MetaKind::SmtValue),
                ("$smt_Map", MetaKind::SmtMap),
                ("$smt_Seq", MetaKind::SmtSeq),
                ("$native_BuiltinType", MetaKind::SmtBuiltin),
            ]),
            decl_seen: HashSet::new(),
        })
    }

    /// The meta-kind of the type `typ`, or `else_kind` if it is not a type
    /// of the embedding. With `follow_function_range`, a function type is
    /// classified by its range. Guards are looked through.
    pub fn get_type_meta_kind_for(
        &self,
        ck: &Checker,
        typ: Term,
        else_kind: MetaKind,
        follow_function_range: bool,
    ) -> MetaKind {
        let mut t = strip_requires(ck, typ);
        loop {
            let k = ck.store.kind(t);
            if k == Kind::APPLY_OPAQUE
                && let Some(&hd) = ck.store.children(t).first()
            {
                let sname = get_name(ck, hd);
                if sname.starts_with("$native_type_") {
                    return MetaKind::SmtBuiltin;
                }
                match sname.as_str() {
                    "$native_embed_eo" => return MetaKind::EoEmbed,
                    "$native_embed_smt" => return MetaKind::SmtEmbed,
                    "$native_embed_checker" => return MetaKind::CheckerEmbed,
                    _ => {}
                }
            }
            if follow_function_range
                && k == Kind::FUNCTION_TYPE
                && let Some(&range) = ck.store.children(t).last()
            {
                t = strip_requires(ck, range);
                continue;
            }
            let sname = get_name(ck, t);
            return (self.type_to_meta_kind.get(&sname))
                .copied()
                .unwrap_or(else_kind);
        }
    }

    /// The datatype of the embedding the term `e` belongs to, and the name
    /// `e` has there. `is_builtin` says whether a name is one the backend's
    /// templates supply.
    pub fn get_meta_kind_for(
        &self,
        ck: &mut Checker,
        e: Term,
        is_builtin: impl Fn(&str) -> bool,
    ) -> (MetaKind, String) {
        let sname = get_name(ck, e);
        if is_builtin(&sname) {
            return (MetaKind::SmtBuiltin, sname);
        }
        if sname.starts_with("@@") || sname.starts_with("$eo_") {
            return (MetaKind::Eunoia, sname);
        }
        let Some(cname) = sname.strip_prefix("$emb_") else {
            return (MetaKind::Eunoia, sname);
        };
        let Some((prefix, rest)) = cname.split_once('.') else {
            return (MetaKind::Eunoia, cname.to_string());
        };
        let cname = rest.to_string();
        if let Some(&mk) = self.prefix_to_meta_kind.get(prefix) {
            return (mk, cname);
        }
        // a constructor of a datatype declared by a $native_embed_* type is
        // classified by its return type
        let app = (ck.get_type(e, None)).and_then(|ty| get_embed_type_app(ck, ty));
        let mk = match app {
            Some(app) => self.get_type_meta_kind_for(ck, app, MetaKind::Eunoia, false),
            None => MetaKind::Eunoia,
        };
        (mk, cname)
    }

    /// If `e` is a lambda that defines the `$eo_` symbol `name`, a program
    /// with one case that does the same: the program's symbol and its
    /// definition.
    pub fn build_lambda_define_program(
        &mut self,
        ck: &mut Checker,
        name: &str,
        e: Term,
    ) -> Option<(Term, Term)> {
        if !name.starts_with("$eo_") || ck.store.kind(e) != Kind::LAMBDA {
            return None;
        }
        let &[vars, body] = ck.store.children(e) else {
            return None;
        };
        let args = ck.store.children(vars).to_vec();
        let mut arg_types = Vec::with_capacity(args.len());
        for &arg in &args {
            arg_types.push(ck.get_type(arg, None)?);
        }
        let ret_type = self.std.allocate_type_variable(ck);
        let pt = ck.mk_program_type(&arg_types, ret_type);
        let symbol = ck.mk_symbol(SymbolKind::ProgramConst, name, pt);
        let mut app_children = vec![symbol];
        app_children.extend_from_slice(&args);
        let prog_app = ck.mk_expr(Kind::APPLY, &app_children);
        let pcase = ck.mk_pair(prog_app, body);
        let prog = ck.mk_expr(Kind::PROGRAM, &[pcase]);
        Some((symbol, prog))
    }

    /// Marks `e` as seen. False if it was already.
    pub fn begin_finalize_decl(&mut self, e: Term) -> bool {
        self.decl_seen.insert(e)
    }
}
