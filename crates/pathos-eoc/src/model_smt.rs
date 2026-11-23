//! The `model-smt` stage (`plugins/model_smt/model_smt.cpp` in Ethos):
//! writes `model_smt_gen.eo`, the EO layer for the SMT-LIB model semantics
//! of the symbols a desugared signature declares.
//!
//! What a symbol means to the model is said by two signatures written in
//! the deep embedding: the SMT-LIB one, which the source tree has, and the
//! one of the input, given with `--semantics`. The stage takes the blocks
//! of the symbols the input declares together with every block those name
//! (see `defs_reader`), puts what each says where it belongs in the
//! template `plugins/model_smt/model_smt.eo`, and checks that no declared
//! symbol was left without a meaning.

use std::collections::{BTreeMap, BTreeSet};

use pathos_elab::{Plugin, State};
use pathos_syntax::{Error, Result};
use pathos_term::{Kind, Term};

use crate::defs_reader::{DefsBlock, DefsFile, order_by_declarations, read_stream};
use crate::std_plugin::{StdPlugin, rtrim_lines, write_text};

pub struct ModelSmt {
    std: StdPlugin,
    /// The signature of the input written in the deep embedding.
    defs_file: String,
    /// The SMT-LIB one, where another than the bundled one was named.
    smt_defs_file: String,
    /// The symbols the signatures say something about.
    defs_covered: BTreeSet<String>,
    /// What is written at each marker of the template that the signatures
    /// name.
    at: BTreeMap<String, String>,
    /// The cases given an aggregate by a program of its own name, which are
    /// written at its marker after everything in `at`; see
    /// `DefsBlock::last`.
    last: BTreeMap<String, String>,
    /// The markers that take the cases of an aggregate, which are indented
    /// by two.
    spliced: BTreeSet<String>,
    /// Every auxiliary program the signatures write.
    helper_progs: String,
    /// Auxiliary definitions used by the conversion from EO to SMT.
    eo_to_smt_aux: String,
    /// Auxiliary definitions used by the canonicity of values.
    smt_canonical_aux: String,
    /// The names of the constants declared, in the order of the input.
    decl_seen: Vec<String>,
}

/// Writes what a block says about the model at the markers it names, and
/// the cases it gives an aggregate itself into `last`.
fn emit_at(
    at: &mut BTreeMap<String, String>,
    last: &mut BTreeMap<String, String>,
    spliced: &BTreeSet<String>,
    b: &DefsBlock,
) {
    for (marker, lines) in &b.at {
        for l in lines {
            let out = at.entry(marker.clone()).or_default();
            if spliced.contains(marker) {
                out.push_str("  ");
            }
            out.push_str(l);
            out.push('\n');
        }
    }
    for (marker, lines) in &b.last {
        for l in lines {
            let out = last.entry(marker.clone()).or_default();
            out.push_str("  ");
            out.push_str(l);
            out.push('\n');
        }
    }
}

/// Whether every constructor of what the block builds is the embedding's
/// own.
fn is_own(b: &DefsBlock) -> bool {
    b.builds.as_ref().is_some_and(|dt| dt.own())
}

/// Puts `replacement` in place of the first `;<tag>` of the template. The
/// placeholders are commented out there, and the comment sign goes too.
fn replace_placeholder(txt: &mut String, tag: &str, replacement: &str) -> Result<()> {
    let guarded = format!(";{tag}");
    let Some(pos) = txt.find(&guarded) else {
        return Err(Error::fatal(format!(
            "ModelSmt: template is missing placeholder {tag}"
        )));
    };
    txt.replace_range(pos..pos + guarded.len(), replacement);
    Ok(())
}

impl ModelSmt {
    /// `defs_file` is the path of the signature of the input written in the
    /// deep embedding, and `smt_defs_file` that of the SMT-LIB one. An empty
    /// `smt_defs_file` is the one of the source tree; an empty `defs_file`
    /// is an error once the stage runs.
    pub fn new(defs_file: &str, smt_defs_file: &str) -> Result<ModelSmt> {
        Ok(ModelSmt::new_in(
            StdPlugin::new()?,
            defs_file,
            smt_defs_file,
        ))
    }

    fn new_in(std: StdPlugin, defs_file: &str, smt_defs_file: &str) -> ModelSmt {
        ModelSmt {
            std,
            defs_file: defs_file.to_string(),
            smt_defs_file: smt_defs_file.to_string(),
            defs_covered: BTreeSet::new(),
            at: BTreeMap::new(),
            last: BTreeMap::new(),
            spliced: BTreeSet::new(),
            helper_progs: String::new(),
            eo_to_smt_aux: String::new(),
            smt_canonical_aux: String::new(),
            decl_seen: Vec::new(),
        }
    }

    /// Checks that the declared symbol `name` is one the signatures cover or
    /// one no model needs.
    fn finalize_decl(&self, name: &str) -> Result<()> {
        if self.defs_covered.contains(name) {
            return Ok(());
        }
        // a name of the desugar stage or of a signature helper, which no
        // proof writes
        if name.starts_with('$') || name.starts_with("@@") {
            return Ok(());
        }
        Err(Error::fatal(format!(
            "ERROR: no model semantics found for {name}"
        )))
    }

    /// Reads the two signatures, takes the blocks the input needs and puts
    /// what each says where it belongs. Returns the SMT-LIB one, whose head
    /// says which markers the template has.
    fn load_defs(&mut self) -> Result<DefsFile> {
        let smt_defs_path = if self.smt_defs_file.is_empty() {
            self.std.resource_path("tools/eoc/out/smt_defs.eo")
        } else {
            self.smt_defs_file.clone()
        };
        let mut smt_defs = DefsFile::default();
        if !smt_defs.read(&smt_defs_path)? {
            return Err(Error::fatal(format!(
                "ModelSmt: could not read the SMT-LIB signature written in the deep embedding at \
                 {smt_defs_path}"
            )));
        }
        if self.defs_file.is_empty() {
            return Err(Error::fatal(
                "ModelSmt: no semantics of the input was given; pass --semantics, see \
                 tools/eoc/driver.py",
            ));
        }
        let mut input_defs = DefsFile::default();
        if !input_defs.read(&self.defs_file)? {
            return Err(Error::fatal(format!(
                "ModelSmt: could not read the signature of the input at {}",
                self.defs_file
            )));
        }
        // The blocks the input needs are those of a symbol it declares and
        // the ones those name. The transformation of a symbol names the
        // constructor of what it denotes, which is a block of the other
        // file, so what the one needs of the other is taken as well.
        let syms: BTreeSet<String> = self.decl_seen.iter().cloned().collect();
        let input_blocks = input_defs.select(&syms, &BTreeSet::new());
        let mut blocks = smt_defs.select(&syms, &input_defs.external_uses(&input_blocks));
        blocks.extend(input_blocks);
        // A constructor and a case go in the order the input declares its
        // symbols; a block of a symbol it does not declare goes just before
        // the one that needs it.
        let by_decl = order_by_declarations(&blocks, &self.decl_seen);
        for a in smt_defs.aggregates() {
            self.spliced.insert(a.into.clone());
        }
        // The literals stand before the symbols written over them, in the
        // order the configuration gives.
        for b in blocks.iter().filter(|b| b.literal) {
            emit_at(&mut self.at, &mut self.last, &self.spliced, b);
        }
        for b in &by_decl {
            if b.literal || is_own(b) {
                // one of the embedding's own, written above or below
                continue;
            }
            // A block says something if it has a constructor or a case of
            // some aggregate; one that says nothing leaves its symbol to be
            // compiled as any other.
            if b.builds.is_some() || b.at.keys().any(|at| self.spliced.contains(at)) {
                self.defs_covered.insert(b.sym.clone());
            }
            emit_at(&mut self.at, &mut self.last, &self.spliced, b);
        }
        // The types and the values are the embedding's own, and stand in the
        // order the configuration gives them.
        for b in blocks.iter().filter(|b| is_own(b)) {
            emit_at(&mut self.at, &mut self.last, &self.spliced, b);
        }
        for b in &by_decl {
            for (out, progs) in [
                (&mut self.helper_progs, &b.helper_progs),
                (&mut self.smt_canonical_aux, &b.canonical_aux),
                (&mut self.eo_to_smt_aux, &b.eo_aux),
            ] {
                for f in progs {
                    out.push_str(f);
                    out.push('\n');
                }
            }
        }
        Ok(smt_defs)
    }

    /// What was written at a marker.
    fn written_at(&self, marker: &str) -> &str {
        self.at.get(marker).map_or("", String::as_str)
    }
}

impl Plugin for ModelSmt {
    fn bind(&mut self, st: &mut State, name: &str, e: Term) -> Result<()> {
        if st.ck.store.kind(e) == Kind::CONST {
            self.decl_seen.push(name.to_string());
        }
        Ok(())
    }

    fn finalize(&mut self, _st: &mut State) -> Result<()> {
        let smt_defs = self.load_defs()?;
        for name in &self.decl_seen {
            self.finalize_decl(name)?;
        }

        let template_path = self.std.resource_path("plugins/model_smt/model_smt.eo");
        let Some(mut final_smt) = read_stream(&template_path) else {
            return Err(Error::fatal(format!(
                "ModelSmt: failed to open resource {template_path}"
            )));
        };
        // What the signatures said about their symbols, each at the marker
        // the aggregate it belongs to names, and after those the cases a
        // signature gave the aggregate itself. A marker nothing was written
        // at is replaced all the same: the output must have no placeholder.
        for a in smt_defs.aggregates() {
            let last = self.last.get(&a.into).map_or("", String::as_str);
            let text = format!("{}{last}", self.written_at(&a.into));
            replace_placeholder(&mut final_smt, &a.into, &text)?;
        }
        for h in smt_defs.helpers() {
            replace_placeholder(&mut final_smt, &h.forward, self.written_at(&h.forward))?;
        }
        // What the stage says for itself: the programs the cases call, and
        // the constructors, which go where the datatype each builds says.
        for (marker, own) in [
            ("$SMT_HELPER_PROGS$", &self.helper_progs),
            ("$EO_TO_SMT_AUX$", &self.eo_to_smt_aux),
            ("$SMT_CANONICAL_AUX$", &self.smt_canonical_aux),
        ] {
            let text = format!("{own}{}", self.written_at(marker));
            replace_placeholder(&mut final_smt, marker, &text)?;
        }
        // Each marker once: two datatypes may be written at one.
        let mut written = BTreeSet::new();
        for dt in smt_defs.embed_datatypes() {
            for marker in [&dt.own_into, &dt.into] {
                if !marker.is_empty() && written.insert(marker) {
                    replace_placeholder(&mut final_smt, marker, self.written_at(marker))?;
                }
            }
        }
        if final_smt.contains("$eoc_") {
            return Err(Error::fatal(
                "ModelSmt: generated output contains an unexpanded $eoc_ name",
            ));
        }

        let out_path = self.std.output_path("plugins/model_smt/model_smt_gen.eo")?;
        if !write_text(&out_path, &rtrim_lines(&final_smt)) {
            return Err(Error::fatal(format!(
                "ModelSmt: failed to open output {out_path}"
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use pathos_check::Options;
    use pathos_elab::include_file;

    use super::*;

    const TEMPLATE: &str = "; a template
(declare-const $smt_Term Type)
;$SMT_OWN$
;$SMT_TERMS$
;$SMT_TYPES$
(program $smtx_typeof () :signature ($smt_Term) $smt_Type
  (
;$TYPEOF_CASES$
  )
)
;$EVAL_FWD$
;$SMT_HELPER_PROGS$
;$EO_TO_SMT_AUX$
;$SMT_CANONICAL_AUX$
(program $eo_to_smt () :signature (B) $smt_Term
  (
;$TRANSFORM_CASES$   \n  )
)
;$TYPE_CASES$ ; the types
";

    const SMT_DEFS: &str = "; the SMT-LIB signature
; $eoc-aggregate $smtx_typeof $eoc_typeof_ $TYPEOF_CASES$
; $eoc-aggregate $eo_to_smt $eoc_transform_ $TRANSFORM_CASES$
; $eoc-aggregate $eo_to_smt_type $eoc_transform_type_ $TYPE_CASES$
; $eoc-embed-datatype $emb_sm. $sm_ $SMT_OWN$ $SMT_TERMS$
; $eoc-embed-datatype $emb_tsm. $tsm_ $SMT_TYPES$
; $eoc-helper $smtx_eval_ $EVAL_FWD$

; -- $emb_sm.Boolean
(declare-const $emb_sm.Boolean $smt_Term)
(echo \"eoc-keep symbol Boolean\")

; -- Bool
(declare-const $emb_tsm.Bool $smt_Type)
(define $tsm_Bool () $emb_tsm.Bool)
(echo \"eoc-keep symbol Bool\")

; -- unused
(declare-const $emb_sm.unused $smt_Term)

; -- not
(declare-const $emb_sm.not $smt_Term)
(define $sm_not () $emb_sm.not)
(program $eoc_typeof_not () :signature ($smt_Term) $smt_Type
  ((($eoc_typeof_not $sm_not) $tsm_Bool)))
(program $smtx_eval_not ((x $smt_Term))
  :signature ($smt_Term) $smt_Term
  ((($smtx_eval_not x) ($smtx_flip x))))
(program $smtx_not_canonical () :signature ($smt_Term) Bool ())

; -- flip
(program $smtx_flip () :signature ($smt_Term) $smt_Term ())
";

    const DEFS: &str = "; the signature of the input
; $eoc-aggregate $eo_to_smt $eoc_transform_ $TRANSFORM_CASES$
; $eoc-aggregate $eo_to_smt_type $eoc_transform_type_ $TYPE_CASES$

; -- not
(program $eoc_transform_not () :signature (B) $smt_Term
  ((($eoc_transform_not not) $sm_not)))
(program $eo_to_smt_not_aux () :signature (B) B ())

; -- B
(program $eoc_transform_type_B () :signature (Type) $smt_Type
  ((($eoc_transform_type_B B) $tsm_Bool)))
";

    const SIG: &str = "(declare-const B Type)
(declare-const $helper B)
(declare-const not (-> B B))
";

    /// Runs the stage on the signature `sig` in a directory of its own.
    /// Returns the file written, or the error.
    fn run(name: &str, sig: &str, defs_file: Option<&str>) -> std::result::Result<String, String> {
        let dir = format!(
            "{}/../../target/tmp/model-smt-{name}",
            env!("CARGO_MANIFEST_DIR")
        );
        let _ = std::fs::remove_dir_all(&dir);
        for sub in ["plugins/model_smt", "tools/eoc/out"] {
            std::fs::create_dir_all(format!("{dir}/root/{sub}")).unwrap();
        }
        for (file, text) in [
            ("root/plugins/model_smt/model_smt.eo", TEMPLATE),
            ("root/tools/eoc/out/smt_defs.eo", SMT_DEFS),
            ("defs.eo", DEFS),
            ("sig.eo", sig),
        ] {
            std::fs::write(format!("{dir}/{file}"), text).unwrap();
        }
        let mut st = State::new(Options::default(), Box::new(|_| ()), Box::new(|_| ()));
        let defs_file = defs_file.map_or(String::new(), |f| format!("{dir}/{f}"));
        let std = StdPlugin::with_dirs(&format!("{dir}/root"), &format!("{dir}/out"));
        st.set_plugin(Box::new(ModelSmt::new_in(std, &defs_file, "")))
            .unwrap();
        include_file(&mut st, &format!("{dir}/sig.eo"), true, false, None).unwrap();
        st.finalize_plugin().map_err(|e| e.to_string())?;
        let out_path = format!("{dir}/out/plugins/model_smt/model_smt_gen.eo");
        Ok(crate::std_plugin::read_text(&out_path).unwrap())
    }

    /// The output is what `ethos-eoc --plugin.model-smt` writes for the same
    /// files.
    #[test]
    fn fills_the_template() {
        assert_eq!(
            run("fills", SIG, Some("defs.eo")).unwrap(),
            "; a template
(declare-const $smt_Term Type)
(declare-const $emb_sm.Boolean $smt_Term)

(declare-const $emb_sm.not $smt_Term)
(define $sm_not () $emb_sm.not)

(declare-const $emb_tsm.Bool $smt_Type)
(define $tsm_Bool () $emb_tsm.Bool)

(program $smtx_typeof () :signature ($smt_Term) $smt_Type
  (
  (($smtx_typeof $sm_not) $tsm_Bool)

  )
)
(program $smtx_eval_not () :signature ($smt_Term) $smt_Term)

(program $smtx_flip () :signature ($smt_Term) $smt_Term ())
(program $smtx_eval_not ((x $smt_Term))
  :signature ($smt_Term) $smt_Term
  ((($smtx_eval_not x) ($smtx_flip x))))

(program $eo_to_smt_not_aux () :signature (B) B ())

(program $smtx_not_canonical () :signature ($smt_Term) Bool ())

(program $eo_to_smt () :signature (B) $smt_Term
  (
  (($eo_to_smt not) $sm_not)

  )
)
  (($eo_to_smt_type B) $tsm_Bool)
 ; the types
"
        );
    }

    /// The messages are those of `ethos-eoc`.
    #[test]
    fn errors() {
        let sig = format!("{SIG}(declare-const other B)\n");
        assert_eq!(
            run("uncovered", &sig, Some("defs.eo")),
            Err("ERROR: no model semantics found for other".to_string())
        );
        assert_eq!(
            run("no-defs", SIG, None),
            Err(
                "ModelSmt: no semantics of the input was given; pass --semantics, see \
                 tools/eoc/driver.py"
                    .to_string()
            )
        );
        let e = run("missing-defs", SIG, Some("nothing.eo")).unwrap_err();
        assert!(
            e.starts_with("ModelSmt: could not read the signature of the input at ")
                && e.ends_with("/nothing.eo"),
            "{e}"
        );
    }
}
