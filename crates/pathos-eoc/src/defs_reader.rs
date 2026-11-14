//! Reads a signature written in the deep embedding
//! (`plugins/model_smt/defs_reader.cpp` in Ethos), for the `model-smt`
//! stage.
//!
//! Such a file has a head, whose comment lines say how the rest is to be
//! taken apart, and then one block per symbol, opened by a `; -- X` line. A
//! block is read as text, never as terms: what it says is copied into the
//! generated file as it stands.
//!
//! Text is held as described in `pathos_syntax::latin1`. Everything the
//! reader looks for is ASCII, so it scans the bytes of the `str` and cuts
//! only at ASCII characters.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;

use pathos_syntax::{Error, Result, latin1, textmode};

use crate::std_plugin::{os_path, replace_all};

/// The content of a file as the C++ gets it from a `std::ifstream`: nothing
/// if the file cannot be opened, and otherwise what could be read of it.
/// A failed read is not an error there, so a directory, which opens, reads
/// as an empty file.
pub fn read_stream(path: &str) -> Option<String> {
    let mut file = std::fs::File::open(os_path(path)).ok()?;
    let mut bytes = Vec::new();
    // what was read before a failure is kept
    let _ = file.read_to_end(&mut bytes);
    Some(latin1::decode(&textmode::input(bytes)))
}

/// One aggregate of the deep embedding, as the head declares it:
/// `; $eoc-aggregate <name> <case> <into>`.
pub struct DefsAggregate {
    /// The aggregate the cases are spliced into.
    pub name: String,
    /// What a symbol's case is named, up to the symbol.
    pub case: String,
    /// The marker of the template its cases are written at.
    pub into: String,
}

/// The programs over values that the cases hand their work to, as the head
/// declares them: `; $eoc-helper <case> <forward>`.
pub struct DefsHelper {
    /// What one is named, up to the symbol.
    pub case: String,
    /// The marker of the template the forward declarations are written at.
    pub forward: String,
}

/// One datatype of the embedding, as the head declares it:
/// `; $eoc-embed-datatype <cons> <macro> <own-into> [<into>]`.
#[derive(Clone)]
pub struct DefsEmbedDatatype {
    /// The constant a constructor of it is declared as, up to the name.
    pub cons: String,
    /// The macro that applies it, up to the name.
    pub macro_name: String,
    /// The marker the embedding's own constructors of it are written at.
    pub own_into: String,
    /// The marker a signature's constructors of it are written at; empty
    /// where the embedding builds every one.
    pub into: String,
}

impl DefsEmbedDatatype {
    /// Whether the embedding builds every constructor of it.
    pub fn own(&self) -> bool {
        self.into.is_empty()
    }
}

/// What one symbol contributes to the generated file: the block a `; -- X`
/// line opens.
#[derive(Default)]
pub struct DefsBlock {
    /// The symbol the block is of.
    pub sym: String,
    /// The names it defines.
    pub defs: BTreeSet<String>,
    /// The names it uses that it does not define.
    pub uses: BTreeSet<String>,
    /// Whether the block stands whatever the input declares, which
    /// `(echo "eoc-keep ...")` says.
    pub keep: bool,
    /// Whether the block is of a term the embedding builds itself, among a
    /// datatype a signature also builds.
    pub literal: bool,
    /// The datatype of the embedding the block declares a constructor of.
    pub builds: Option<DefsEmbedDatatype>,
    /// Whether what the block declares is the embedding's own.
    pub own: bool,
    /// The auxiliary programs of the block, in the order it writes them.
    pub helper_progs: Vec<String>,
    /// The same, for the programs written over the transformation.
    pub eo_aux: Vec<String>,
    /// The programs that say whether a value is canonical.
    pub canonical_aux: Vec<String>,
    /// What the block contributes, keyed by the marker of the template it
    /// is written at.
    pub at: BTreeMap<String, Vec<String>>,
}

/// A definitions file: its blocks, and what its head declares.
#[derive(Default)]
pub struct DefsFile {
    blocks: Vec<DefsBlock>,
    /// Longest case first; see `aggregate_of`.
    aggregates: Vec<DefsAggregate>,
    embed_datatypes: Vec<DefsEmbedDatatype>,
    helpers: Vec<DefsHelper>,
    /// The block that defines each name.
    owner: BTreeMap<String, usize>,
}

/// `isspace` in the C locale.
fn is_space(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

/// True if `c` may occur in a name of the signature.
fn is_name_char(c: u8) -> bool {
    !is_space(c) && !matches!(c, b'(' | b')' | b';' | b'"')
}

/// `text[from..to]`, with `to` clamped to the end as `substr` does.
fn sub(text: &str, from: usize, to: usize) -> &str {
    text.get(from..to.min(text.len())).unwrap_or("")
}

/// Where `pat` first occurs in `text` at or after `from`.
fn find_from(text: &str, pat: &str, from: usize) -> Option<usize> {
    text.get(from..)?.find(pat).map(|p| p + from)
}

/// Given the opening quote of a string at `i`, where its closing quote is,
/// or the end of the text. A quote is written twice in an SMT-LIB string.
fn string_end(b: &[u8], mut i: usize) -> usize {
    let n = b.len();
    i += 1;
    while i < n && !(b[i] == b'"' && (i + 1 >= n || b[i + 1] != b'"')) {
        i += if b[i] == b'"' { 2 } else { 1 };
    }
    i
}

/// Given the `;` of a comment at `i`, where its line ends.
fn comment_end(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && b[i] != b'\n' {
        i += 1;
    }
    i
}

/// One past the closing parenthesis of the form that begins at `i`. A
/// string and a comment are stepped over whole.
fn form_end(text: &str, mut i: usize) -> Option<usize> {
    let b = text.as_bytes();
    let mut depth = 0usize;
    while i < b.len() {
        match b[i] {
            b'"' => i = string_end(b, i),
            b';' => i = comment_end(b, i),
            b'(' => depth += 1,
            b')' => {
                // as the unsigned counter of the C++: a `)` too many never
                // closes anything
                depth = depth.wrapping_sub(1);
                if depth == 0 {
                    return Some(i + 1);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// The top-level forms of `text`, in order. An unclosed form ends them.
fn forms(text: &str) -> Vec<&str> {
    let b = text.as_bytes();
    let mut ret = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b';' {
            i = comment_end(b, i);
        } else if b[i] == b'(' {
            let Some(e) = form_end(text, i) else {
                return ret;
            };
            ret.push(sub(text, i, e));
            i = e - 1;
        }
        i += 1;
    }
    ret
}

/// The word of `form` that follows its keyword: the name it is of.
fn form_name(form: &str) -> &str {
    let b = form.as_bytes();
    let n = b.len();
    let Some(mut i) = (1..n).find(|&k| matches!(b[k], b' ' | b'\t' | b'\n')) else {
        return "";
    };
    while i < n && is_space(b[i]) {
        i += 1;
    }
    let mut j = i;
    while j < n && is_name_char(b[j]) {
        j += 1;
    }
    sub(form, i, j)
}

/// The keyword of `form`, e.g. `program` or `define`.
fn form_kind(form: &str) -> &str {
    let b = form.as_bytes();
    let mut j = 1;
    while j < b.len() && is_name_char(b[j]) {
        j += 1;
    }
    sub(form, 1, j)
}

/// Every word of `form` that begins with a dollar. Bound parameters such as
/// `$T` are among them; they have no owner, so they do no harm.
fn names_of(form: &str, out: &mut BTreeSet<String>) {
    let b = form.as_bytes();
    let n = b.len();
    let mut i = 0;
    while i < n {
        match b[i] {
            b'"' => i = string_end(b, i),
            b';' => i = comment_end(b, i),
            b'$' => {
                let mut j = i;
                while j < n && is_name_char(b[j]) {
                    j += 1;
                }
                out.insert(sub(form, i, j).to_string());
                i = j - 1;
            }
            _ => {}
        }
        i += 1;
    }
}

/// A form without its parentheses.
fn inner(form: &str) -> &str {
    sub(form, 1, form.len().saturating_sub(1))
}

/// The cases of a program: the forms of the last form of its body, with
/// `name` rewritten to `agg` in each.
fn cases_of(prog: &str, name: &str, agg: &str) -> Vec<String> {
    let body = forms(inner(prog));
    let Some(cl) = body.last() else {
        return Vec::new();
    };
    forms(inner(cl))
        .into_iter()
        .map(|c| replace_all(c, name, agg))
        .collect()
}

/// The forward declaration of the program `prog`, which is named `name`;
/// empty if the program gives no signature.
fn fwd_of(prog: &str, name: &str) -> String {
    let Some(s) = prog.find(":signature") else {
        return String::new();
    };
    let e = find_from(prog, "\n", s).unwrap_or(prog.len());
    format!("(program {name} () {})", sub(prog, s, e))
}

/// True if `name` is `prefix` and something more.
fn extends(name: &str, prefix: &str) -> bool {
    name.len() > prefix.len() && name.starts_with(prefix)
}

impl DefsFile {
    /// Reads the file at `path`. False if it could not be opened or held no
    /// blocks.
    pub fn read(&mut self, path: &str) -> Result<bool> {
        let Some(content) = read_stream(path) else {
            self.clear();
            return Ok(false);
        };
        self.read_content(path, &content)
    }

    fn clear(&mut self) {
        self.blocks.clear();
        self.owner.clear();
        self.aggregates.clear();
        self.helpers.clear();
    }

    /// Reads the content of the file at `path`.
    fn read_content(&mut self, path: &str, content: &str) -> Result<bool> {
        self.clear();
        // The newline in front lets the same marker find a block on line one.
        let text = format!("\n{content}");
        // A block runs from the line that names its symbol to the next one.
        let mark = "\n; -- ";
        let mut i = text.find(mark);
        // Everything above the first block is the head.
        self.read_head(sub(&text, 0, i.unwrap_or(text.len())))?;
        if self.aggregates.is_empty() {
            return Err(Error::fatal(format!(
                "DefsFile: {path} declares no aggregates; it was written by an older compiler, \
                 run tools/eoc/compiler/sem_compile.py"
            )));
        }
        while let Some(at) = i {
            let ns = at + mark.len();
            let Some(ne) = find_from(&text, "\n", ns) else {
                return Ok(false);
            };
            let next = find_from(&text, mark, ns);
            // Where the next block opens on the very next line, the length
            // the C++ computes wraps around, and this block takes the rest of
            // the file.
            let end = match next {
                Some(next) if next > ne => next,
                _ => text.len(),
            };
            self.add_block(sub(&text, ns, ne), sub(&text, ne + 1, end));
            i = next;
        }
        Ok(!self.blocks.is_empty())
    }

    /// The aggregates the head declares.
    pub fn aggregates(&self) -> &[DefsAggregate] {
        &self.aggregates
    }

    /// The datatypes the head declares.
    pub fn embed_datatypes(&self) -> &[DefsEmbedDatatype] {
        &self.embed_datatypes
    }

    /// The programs written over values that the head declares.
    pub fn helpers(&self) -> &[DefsHelper] {
        &self.helpers
    }

    /// Reads one block from its text, its symbol having been taken.
    fn add_block(&mut self, sym: &str, text: &str) {
        let mut b = DefsBlock {
            sym: sym.to_string(),
            ..DefsBlock::default()
        };
        // A block named after the constant it declares is one of the
        // embedding's own among a datatype a signature also builds.
        let named_after_constant = self.embed_datatype_of(sym).is_some();
        for f in forms(text) {
            let kind = form_kind(f);
            if kind == "echo" {
                // a directive to a stage; it names nothing
                if f.contains("\"eoc-keep ") {
                    b.keep = true;
                }
                continue;
            }
            let name = form_name(f);
            names_of(f, &mut b.uses);
            b.defs.insert(name.to_string());
            if matches!(
                kind,
                "declare-const" | "declare-parameterized-const" | "define"
            ) {
                if let Some(dt) = self.embed_datatype_of(name) {
                    // the constructor of the embedding for the symbol, or
                    // the macro that applies it
                    b.own = dt.own() || named_after_constant;
                    b.literal = named_after_constant && !dt.own();
                    let at = if b.own { &dt.own_into } else { &dt.into };
                    b.at.entry(at.clone()).or_default().push(f.to_string());
                    b.builds = Some(dt.clone());
                } else {
                    // a helper that happens to be written as a define
                    self.classify_program(&mut b, f, name);
                }
                continue;
            }
            if kind != "program" {
                continue;
            }
            self.classify_program(&mut b, f, name);
        }
        for d in &b.defs {
            b.uses.remove(d);
        }
        for d in &b.defs {
            self.owner.insert(d.clone(), self.blocks.len());
        }
        self.blocks.push(b);
    }

    /// The aggregate a per-symbol program belongs to: the one with the
    /// longest case the name begins with.
    fn aggregate_of(&self, name: &str) -> Option<&DefsAggregate> {
        self.aggregates.iter().find(|a| extends(name, &a.case))
    }

    /// The same, for a program written over values.
    fn helper_of(&self, name: &str) -> Option<&DefsHelper> {
        self.helpers.iter().find(|h| extends(name, &h.case))
    }

    /// The datatype a name is a constructor of.
    fn embed_datatype_of(&self, name: &str) -> Option<&DefsEmbedDatatype> {
        self.embed_datatypes
            .iter()
            .find(|dt| name.starts_with(&dt.cons) || name.starts_with(&dt.macro_name))
    }

    /// Puts one form of a block into the stream its name says.
    fn classify_program(&self, b: &mut DefsBlock, f: &str, name: &str) {
        // A per-symbol program gives its cases to the aggregate it feeds.
        // The entry is made even if it has no cases.
        if let Some(a) = self.aggregate_of(name) {
            b.at.entry(a.into.clone())
                .or_default()
                .extend(cases_of(f, name, &a.name));
            return;
        }
        if name != "_canonical" && name.ends_with("_canonical") {
            b.canonical_aux.push(f.to_string());
            return;
        }
        if let Some(h) = self.helper_of(name) {
            b.helper_progs.push(f.to_string());
            let fwd = fwd_of(f, name);
            if !fwd.is_empty() {
                b.at.entry(h.forward.clone()).or_default().push(fwd);
            }
            return;
        }
        if extends(name, "$eo_to_smt") {
            b.eo_aux.push(f.to_string());
            return;
        }
        // any other helper of the symbol
        b.helper_progs.push(f.to_string());
    }

    /// Reads what the head declares: everything above the first block.
    fn read_head(&mut self, head: &str) -> Result<()> {
        for line in head.split('\n') {
            let mut words = line
                .split(|c: char| u8::try_from(c).is_ok_and(is_space))
                .filter(|w| !w.is_empty());
            if words.next() != Some(";") {
                continue;
            }
            let mut word = || words.next().map(str::to_string);
            match word().as_deref() {
                Some("$eoc-aggregate") => {
                    let (Some(name), Some(case), Some(into)) = (word(), word(), word()) else {
                        return Err(Error::fatal(format!(
                            "DefsFile: an aggregate is written `; $eoc-aggregate <name> <case> \
                             <into>`, got: {line}"
                        )));
                    };
                    self.aggregates.push(DefsAggregate { name, case, into });
                }
                Some("$eoc-embed-datatype") => {
                    let (Some(cons), Some(macro_name), Some(own_into)) = (word(), word(), word())
                    else {
                        return Err(Error::fatal(format!(
                            "DefsFile: a datatype of the embedding is written `; \
                             $eoc-embed-datatype <cons> <macro> <own-into> [<into>]`, got: {line}"
                        )));
                    };
                    // One that says nothing more is the embedding's throughout.
                    let into = word().unwrap_or_default();
                    self.embed_datatypes.push(DefsEmbedDatatype {
                        cons,
                        macro_name,
                        own_into,
                        into,
                    });
                }
                Some("$eoc-helper") => {
                    let (Some(case), Some(forward)) = (word(), word()) else {
                        return Err(Error::fatal(format!(
                            "DefsFile: a helper is written `; $eoc-helper <case> <forward>`, \
                             got: {line}"
                        )));
                    };
                    self.helpers.push(DefsHelper { case, forward });
                }
                _ => {}
            }
        }
        // Longest case first, of which `aggregate_of` takes the first match.
        // The length is the one in bytes of the file: one per char.
        self.aggregates
            .sort_by_key(|a| std::cmp::Reverse(a.case.chars().count()));
        Ok(())
    }

    /// The names the blocks use that no block of this file defines.
    pub fn external_uses(&self, blocks: &[&DefsBlock]) -> BTreeSet<String> {
        let mut ret = BTreeSet::new();
        for b in blocks {
            for u in &b.uses {
                if !self.owner.contains_key(u) {
                    ret.insert(u.clone());
                }
            }
        }
        ret
    }

    /// The blocks whose symbol is in `syms`, that said `eoc-keep`, or that
    /// define one of `names`, together with every block those depend on, in
    /// the order of the file. A block depends on the one that defines a name
    /// it uses.
    pub fn select(&self, syms: &BTreeSet<String>, names: &BTreeSet<String>) -> Vec<&DefsBlock> {
        let mut keep = BTreeSet::new();
        let mut todo = Vec::new();
        for (i, b) in self.blocks.iter().enumerate() {
            if b.keep || syms.contains(&b.sym) || names.iter().any(|n| b.defs.contains(n)) {
                keep.insert(i);
                todo.push(i);
            }
        }
        // what a block kept above names, and what that names in turn
        while let Some(i) = todo.pop() {
            let Some(b) = self.blocks.get(i) else {
                continue;
            };
            for u in &b.uses {
                if let Some(&owner) = self.owner.get(u)
                    && keep.insert(owner)
                {
                    todo.push(owner);
                }
            }
        }
        keep.iter().filter_map(|&i| self.blocks.get(i)).collect()
    }
}

/// Orders blocks by the order the input declares their symbols in. Before
/// each declared block go, recursively, the blocks it depends on whose
/// symbol is not itself declared. The blocks of no declared symbol that are
/// left come last, in the order given.
pub fn order_by_declarations<'a>(
    blocks: &[&'a DefsBlock],
    declarations: &[String],
) -> Vec<&'a DefsBlock> {
    let mut owner: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, b) in blocks.iter().enumerate() {
        for d in &b.defs {
            owner.insert(d, i);
        }
    }
    let declared: BTreeSet<&str> = declarations.iter().map(String::as_str).collect();
    let mut ordered = Vec::new();
    let mut placed = vec![false; blocks.len()];
    for declaration in declarations {
        for (i, b) in blocks.iter().enumerate() {
            if b.sym != *declaration || placed[i] {
                continue;
            }
            // The dependencies of the block, each after its own. The walk is
            // the recursion of the C++ on an explicit stack: a block and
            // what is left of its uses.
            let mut stack = vec![(*b, b.uses.iter())];
            while let Some((_, uses)) = stack.last_mut() {
                let Some(u) = uses.next() else {
                    if let Some((done, _)) = stack.pop()
                        && !stack.is_empty()
                    {
                        ordered.push(done);
                    }
                    continue;
                };
                if let Some(&o) = owner.get(u.as_str())
                    && !declared.contains(blocks[o].sym.as_str())
                    && !placed[o]
                {
                    placed[o] = true;
                    stack.push((blocks[o], blocks[o].uses.iter()));
                }
            }
            placed[i] = true;
            ordered.push(*b);
        }
    }
    for (i, b) in blocks.iter().enumerate() {
        if !placed[i] {
            ordered.push(*b);
        }
    }
    ordered
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEAD: &str = "; a head
; $eoc-aggregate $smtx_typeof $eoc_typeof_ $SMT_TYPEOF_CASES$
; $eoc-aggregate $eo_to_smt_type $eoc_transform_type_ $TYPE_CASES$
; $eoc-aggregate $eo_to_smt $eoc_transform_ $TRANSFORM_CASES$
; $eoc-embed-datatype $emb_tsm. $tsm_ $SMT_TYPE_DECLS$
; $eoc-embed-datatype $emb_sm. $sm_ $SMT_OWN_DECLS$ $SMT_DECLS$
; $eoc-helper $smtx_eval_ $SMT_EVAL_FWD$
";

    fn read(content: &str) -> Result<(DefsFile, bool)> {
        let mut file = DefsFile::default();
        let ok = file.read_content("defs.eo", content)?;
        Ok((file, ok))
    }

    fn set(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|n| n.to_string()).collect()
    }

    fn strs<'a>(names: impl IntoIterator<Item = &'a String>) -> Vec<&'a str> {
        names.into_iter().map(String::as_str).collect()
    }

    #[test]
    fn form_helpers() {
        assert_eq!(
            forms("; (no)\n(a \"x)\"\"(\" b) junk (c ; )\n d)\n(open"),
            ["(a \"x)\"\"(\" b)", "(c ; )\n d)"]
        );
        // a `)` too many closes nothing, and neither does what follows
        assert_eq!(forms(") (a)"), ["(a)"]);
        assert_eq!(form_end("(a (b) c) d", 0), Some(9));
        assert_eq!(form_end("(a \"", 0), None);
        assert_eq!(form_kind("(program $f () x)"), "program");
        assert_eq!(form_kind("()"), "");
        assert_eq!(form_name("(program\n  $f () x)"), "$f");
        assert_eq!(form_name("(define $g() x)"), "$g");
        assert_eq!(form_name("(define)"), "");
        assert_eq!(form_name("(define (x) y)"), "");
        // a carriage return does not end the keyword
        assert_eq!(form_name("(a\rb c)"), "c");
        let mut names = BTreeSet::new();
        names_of("(f $a ($b$c \"$no \"\"$no\") ; $no\n x$d $e)", &mut names);
        assert_eq!(strs(&names), ["$a", "$b$c", "$d", "$e"]);
        assert_eq!(
            cases_of(
                "(program $p_x ((y T))\n  :signature (T) T\n  ((($p_x y) ($p_x_aux $p_x)) (($p_x \
                 z) z)))",
                "$p_x",
                "$agg"
            ),
            ["(($agg y) ($agg_aux $agg))", "(($agg z) z)"]
        );
        assert!(cases_of("()", "$p", "$agg").is_empty());
        assert_eq!(
            fwd_of("(program $f ((x T))\n  :signature (T) T\n  ())", "$f"),
            "(program $f () :signature (T) T)"
        );
        assert_eq!(
            fwd_of("(program $f () :signature (T) T ())", "$f"),
            "(program $f () :signature (T) T ()))"
        );
        assert_eq!(fwd_of("(program $f () ())", "$f"), "");
    }

    #[test]
    fn head() {
        let (file, ok) = read(HEAD).unwrap();
        // no blocks
        assert!(!ok);
        // longest case first, the others in the order written
        let cases: Vec<&str> = file.aggregates().iter().map(|a| a.case.as_str()).collect();
        assert_eq!(
            cases,
            ["$eoc_transform_type_", "$eoc_transform_", "$eoc_typeof_"]
        );
        assert_eq!(file.aggregates()[0].name, "$eo_to_smt_type");
        assert_eq!(file.aggregates()[0].into, "$TYPE_CASES$");
        let dts = file.embed_datatypes();
        assert!(dts[0].own() && !dts[1].own());
        assert_eq!(dts[1].into, "$SMT_DECLS$");
        assert_eq!(file.helpers()[0].forward, "$SMT_EVAL_FWD$");

        let err = |content: &str| read(content).err().map(|e| e.to_string());
        assert_eq!(
            err("; nothing\n"),
            Some(
                "DefsFile: defs.eo declares no aggregates; it was written by an older compiler, \
                 run tools/eoc/compiler/sem_compile.py"
                    .to_string()
            )
        );
        assert_eq!(
            err(";  $eoc-aggregate a b \n"),
            Some(
                "DefsFile: an aggregate is written `; $eoc-aggregate <name> <case> <into>`, got: \
                 ;  $eoc-aggregate a b "
                    .to_string()
            )
        );
        assert_eq!(
            err("; $eoc-embed-datatype a b\n"),
            Some(
                "DefsFile: a datatype of the embedding is written `; $eoc-embed-datatype <cons> \
                 <macro> <own-into> [<into>]`, got: ; $eoc-embed-datatype a b"
                    .to_string()
            )
        );
        assert_eq!(
            err("; $eoc-helper a\n"),
            Some(
                "DefsFile: a helper is written `; $eoc-helper <case> <forward>`, got: ; \
                 $eoc-helper a"
                    .to_string()
            )
        );
        // a line that does not begin with a lone `;` declares nothing
        assert!(err(";$eoc-aggregate a\n;; $eoc-helper a\n").is_some_and(|e| e.contains("older")));
    }

    #[test]
    fn blocks() {
        let content = format!(
            "{HEAD}; -- not
(declare-const $emb_sm.not (-> T T))
(define $sm_not ((x T)) ($emb_sm.not x))
(program $eoc_typeof_not ((x T))
  :signature (T) T
  ((($eoc_typeof_not ($sm_not x)) ($smtx_typeof_guard x $tsm_Bool))))
(program $eoc_transform_type_not () :signature (T) T ())
(program $smtx_eval_not ((x V))
  :signature (V) V
  ((($smtx_eval_not x) ($smtx_not_aux x))))
(program $smtx_not_aux () :signature (V) V ())
(program $smtx_not_canonical () :signature (V) V ())
(program $eo_to_smt_not () :signature (V) V ())
(program $eo_to_smt () :signature (V) V ())
(define $smtx_const () $emb_sm.Binary)
(declare-other $ignored $x)
(echo \"eoc-exclude symbol not $y\")
; -- Bool
(declare-const $emb_tsm.Bool Type)
(define $tsm_Bool () $emb_tsm.Bool)
(echo \"eoc-keep symbol Bool\")
; -- $emb_sm.Binary
(declare-const $emb_sm.Binary T)
"
        );
        let (file, ok) = read(&content).unwrap();
        assert!(ok);
        let [not, bool_, binary] = file.blocks.as_slice() else {
            panic!("three blocks");
        };

        assert_eq!(not.sym, "not");
        assert!(!not.keep && !not.literal && !not.own);
        assert!(not.builds.as_ref().is_some_and(|dt| dt.cons == "$emb_sm."));
        assert_eq!(
            strs(&not.defs),
            [
                "$emb_sm.not",
                "$eo_to_smt",
                "$eo_to_smt_not",
                "$eoc_transform_type_not",
                "$eoc_typeof_not",
                "$ignored",
                "$sm_not",
                "$smtx_const",
                "$smtx_eval_not",
                "$smtx_not_aux",
                "$smtx_not_canonical",
            ]
        );
        // what it defines is not a use; the echo names nothing
        assert_eq!(
            strs(&not.uses),
            ["$emb_sm.Binary", "$smtx_typeof_guard", "$tsm_Bool", "$x"]
        );
        let at: Vec<(&str, Vec<&str>)> =
            (not.at.iter().map(|(k, v)| (k.as_str(), strs(v)))).collect();
        assert_eq!(
            at,
            [
                (
                    "$SMT_DECLS$",
                    vec![
                        "(declare-const $emb_sm.not (-> T T))",
                        "(define $sm_not ((x T)) ($emb_sm.not x))"
                    ]
                ),
                (
                    "$SMT_EVAL_FWD$",
                    vec!["(program $smtx_eval_not () :signature (V) V)"]
                ),
                (
                    "$SMT_TYPEOF_CASES$",
                    vec!["(($smtx_typeof ($sm_not x)) ($smtx_typeof_guard x $tsm_Bool))"]
                ),
                // a program with no cases still has its marker
                ("$TYPE_CASES$", vec![]),
            ]
        );
        let names = |progs: &[String]| -> Vec<String> {
            progs.iter().map(|f| form_name(f).to_string()).collect()
        };
        assert_eq!(
            names(&not.helper_progs),
            [
                "$smtx_eval_not",
                "$smtx_not_aux",
                "$eo_to_smt",
                "$smtx_const"
            ]
        );
        assert_eq!(names(&not.canonical_aux), ["$smtx_not_canonical"]);
        assert_eq!(names(&not.eo_aux), ["$eo_to_smt_not"]);

        assert!(bool_.keep && bool_.own && !bool_.literal);
        assert_eq!(strs(bool_.at.keys()), ["$SMT_TYPE_DECLS$"]);
        assert!(binary.own && binary.literal && !binary.keep);
        assert_eq!(strs(binary.at.keys()), ["$SMT_OWN_DECLS$"]);

        // Bool is kept whatever is asked for
        let syms = |blocks: &[&DefsBlock]| -> Vec<String> {
            blocks.iter().map(|b| b.sym.clone()).collect()
        };
        let none = BTreeSet::new();
        assert_eq!(syms(&file.select(&none, &none)), ["Bool"]);
        // not names the two others
        let sel = file.select(&set(&["not"]), &none);
        assert_eq!(syms(&sel), ["not", "Bool", "$emb_sm.Binary"]);
        assert_eq!(
            syms(&file.select(&none, &set(&["$emb_sm.Binary"]))),
            ["Bool", "$emb_sm.Binary"]
        );
        assert_eq!(
            strs(&file.external_uses(&sel)),
            ["$smtx_typeof_guard", "$x"]
        );
    }

    #[test]
    fn block_boundaries() {
        // The head is what is above the first block, so a block on line one
        // leaves the file with no head.
        assert!(read("; -- a\n(define $x () $y)\n; $eoc-aggregate n c i\n").is_err());

        // a symbol is the rest of its line
        let head = "; $eoc-aggregate n c i\n";
        let (file, ok) = read(&format!("{head}; -- a b \n(define $x () $y)")).unwrap();
        assert!(ok);
        assert_eq!(file.blocks[0].sym, "a b ");
        assert_eq!(strs(&file.blocks[0].defs), ["$x"]);

        // A block whose line is followed at once by the next block takes the
        // rest of the file.
        let (file, ok) = read(&format!(
            "{head}; -- a\n; -- b\n(define $x () 1)\n; -- c\n(define $y () 1)\n"
        ))
        .unwrap();
        assert!(ok);
        let defs: Vec<(&str, Vec<&str>)> = (file.blocks.iter())
            .map(|b| (b.sym.as_str(), strs(&b.defs)))
            .collect();
        assert_eq!(
            defs,
            [
                ("a", vec!["$x", "$y"]),
                ("b", vec!["$x"]),
                ("c", vec!["$y"])
            ]
        );
        // the last block that defines a name owns it
        assert_eq!(file.owner.get("$x"), Some(&1));
        assert_eq!(file.owner.get("$y"), Some(&2));

        // a last block with no line end is not read
        let (file, ok) = read(&format!("{head}; -- a\n(define $x () 1)\n; -- b")).unwrap();
        assert!(!ok);
        assert_eq!(file.blocks.len(), 1);
    }

    #[test]
    fn declaration_order() {
        let block = |sym: &str, defs: &[&str], uses: &[&str]| DefsBlock {
            sym: sym.to_string(),
            defs: set(defs),
            uses: set(uses),
            ..DefsBlock::default()
        };
        let all = [
            block("helper", &["$h"], &["$deep"]),
            block("a", &["$a"], &["$b", "$h"]),
            block("deep", &["$deep"], &[]),
            block("b", &["$b"], &["$h"]),
            block("left", &["$l"], &["$a"]),
            block("c", &["$c"], &["$c2"]),
            block("c2", &["$c2"], &["$c"]),
        ];
        let blocks: Vec<&DefsBlock> = all.iter().collect();
        let order = |declarations: &[&str]| -> Vec<&str> {
            let declarations: Vec<String> = declarations.iter().map(|d| d.to_string()).collect();
            order_by_declarations(&blocks, &declarations)
                .iter()
                .map(|b| b.sym.as_str())
                .collect()
        };
        // b is declared, so it waits for its turn; helper is not, and goes
        // before the first that needs it, after what it needs itself
        assert_eq!(
            order(&["b", "a", "nothing"]),
            ["deep", "helper", "b", "a", "left", "c", "c2"]
        );
        // b is not declared now, and goes before a, which needs it
        assert_eq!(
            order(&["a", "a"]),
            ["deep", "helper", "b", "a", "left", "c", "c2"]
        );
        // c2 needs c back, which is declared and so not a dependency
        assert_eq!(
            order(&["c"]),
            ["c2", "c", "helper", "a", "deep", "b", "left"]
        );
        assert_eq!(order(&[]), ["helper", "a", "deep", "b", "left", "c", "c2"]);
    }
}
