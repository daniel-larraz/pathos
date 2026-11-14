//! What the compiler stages share (`plugins/std_plugin.cpp` and
//! `plugins/utils.cpp` in Ethos): where they read their templates and
//! write their output, and helpers on text and terms.

use std::collections::HashSet;
use std::ffi::OsString;

use pathos_syntax::{Error, Result, latin1};
use pathos_term::{Kind, LitKind, SymbolKind, Term};

use pathos_check::Checker;

/// The file-system path for a path held as text (see
/// `pathos_syntax::latin1`).
pub fn os_path(path: &str) -> OsString {
    latin1::to_os(path)
}

/// The content of a file as text, one character per byte.
pub fn read_text(path: &str) -> Option<String> {
    std::fs::read(os_path(path))
        .ok()
        .map(|b| latin1::decode(&b))
}

/// Writes text to a file, one byte per character. False if that fails.
pub fn write_text(path: &str, text: &str) -> bool {
    std::fs::write(os_path(path), latin1::encode(text)).is_ok()
}

fn normalize_directory(mut path: String) -> String {
    if !path.is_empty() && !path.ends_with('/') {
        path.push('/');
    }
    path
}

fn parent_directory(path: &str) -> &str {
    match path.rfind('/') {
        None => "",
        Some(0) => "/",
        Some(pos) => &path[..pos],
    }
}

/// Makes the directory and those above it, as `ensureDirectoryExists`.
fn ensure_directory_exists(path: &str) -> Result<()> {
    if path.is_empty() || path == "." {
        return Ok(());
    }
    let mut current = String::new();
    if path.starts_with('/') {
        current.push('/');
    }
    for part in path.split('/') {
        if part.is_empty() || part == "." {
            continue;
        }
        if !current.is_empty() && !current.ends_with('/') {
            current.push('/');
        }
        current.push_str(part);
        if part == ".." {
            continue;
        }
        match std::fs::metadata(os_path(&current)) {
            Ok(meta) if meta.is_dir() => continue,
            Ok(_) => {
                return Err(Error::fatal(format!(
                    "StdPlugin: path exists and is not a directory: {current}"
                )));
            }
            Err(_) => {}
        }
        if let Err(e) = std::fs::create_dir(os_path(&current))
            && e.kind() != std::io::ErrorKind::AlreadyExists
        {
            return Err(Error::fatal(format!(
                "StdPlugin: failed to create directory {current}, errno = {}",
                e.raw_os_error().unwrap_or(0)
            )));
        }
    }
    Ok(())
}

/// A tag of a template and what to put in its place.
pub type Replacement = (String, String);

/// The directories of the stages, and the counter for the type variables
/// they make.
pub struct StdPlugin {
    /// The root of the source tree the templates are read from, ending in
    /// `/`: `ETHOS_PLUGIN_ROOT`.
    plugin_path: String,
    /// Where generated files go, ending in `/`: `ETHOS_PLUGIN_OUTPUT_DIR`.
    output_path: String,
    type_var_counter: usize,
}

impl StdPlugin {
    /// Finds the two directories: from the environment variables
    /// `ETHOS_PLUGIN_ROOT` and `ETHOS_PLUGIN_OUTPUT_DIR` if they are set and
    /// not empty, else from the directories compiled in.
    ///
    /// `ethos-eoc` gets its compiled-in directories from CMake: the source
    /// tree and `<build directory>/out`. `pathos-eoc` gets them from the
    /// environment of its own build: `ETHOS_PLUGIN_SOURCE_DIR` and
    /// `ETHOS_PLUGIN_OUTPUT_DIR`, as in
    ///
    /// ```text
    /// ETHOS_PLUGIN_SOURCE_DIR=/path/to/ethos \
    /// ETHOS_PLUGIN_OUTPUT_DIR=/path/to/ethos/build-eoc/out \
    ///   cargo build --release --bin pathos-eoc
    /// ```
    ///
    /// eoc's driver sets neither variable when it runs a stage, so a
    /// `pathos-eoc` that the driver is to run on its own must be built
    /// this way. Built without them it has no fallback, and a stage fails
    /// with Ethos's message when a variable is missing.
    pub fn new() -> Result<StdPlugin> {
        let dir = |var: &str, compiled_in: Option<&str>| {
            let value = std::env::var_os(var).unwrap_or_default();
            let value = latin1::from_os(&value);
            normalize_directory(if value.is_empty() {
                compiled_in.unwrap_or_default().to_string()
            } else {
                value
            })
        };
        let plugin_path = dir("ETHOS_PLUGIN_ROOT", option_env!("ETHOS_PLUGIN_SOURCE_DIR"));
        let output_path = dir(
            "ETHOS_PLUGIN_OUTPUT_DIR",
            option_env!("ETHOS_PLUGIN_OUTPUT_DIR"),
        );
        if plugin_path.is_empty() {
            return Err(Error::fatal(
                "StdPlugin: unable to determine the plugin resource root",
            ));
        }
        if output_path.is_empty() {
            return Err(Error::fatal(
                "StdPlugin: unable to determine the plugin output root",
            ));
        }
        Ok(StdPlugin {
            plugin_path,
            output_path,
            type_var_counter: 0,
        })
    }

    /// With the directories given, for tests.
    #[cfg(test)]
    pub fn with_dirs(root: &str, out: &str) -> StdPlugin {
        StdPlugin {
            plugin_path: normalize_directory(root.to_string()),
            output_path: normalize_directory(out.to_string()),
            type_var_counter: 0,
        }
    }

    /// The path of a file of the source tree.
    pub fn resource_path(&self, relative: &str) -> String {
        format!("{}{relative}", self.plugin_path)
    }

    /// The path of a generated file; its directory is made if need be.
    pub fn output_path(&self, relative: &str) -> Result<String> {
        let path = format!("{}{relative}", self.output_path);
        ensure_directory_exists(parent_directory(&path))?;
        Ok(path)
    }

    /// Copies a file of the source tree to the same place under the output
    /// directory.
    pub fn copy_resource_to_output(&self, relative: &str) -> Result<()> {
        let Some(text) = read_text(&self.resource_path(relative)) else {
            return Err(Error::fatal(format!(
                "StdPlugin: failed to open resource {relative}"
            )));
        };
        let out_path = self.output_path(relative)?;
        if !write_text(&out_path, &text) {
            return Err(Error::fatal(format!(
                "StdPlugin: failed to open output {out_path}"
            )));
        }
        Ok(())
    }

    /// Writes the template `resource` to `output` with each tag replaced:
    /// its first occurrence, or all with `repl_all`. A tag the template
    /// does not have is warned about. The template's notes to its editors
    /// are dropped. Returns the path written.
    pub fn emit_resource_file(
        &self,
        ck: &mut Checker,
        resource: &str,
        output: &str,
        replacements: &[Replacement],
        repl_all: bool,
    ) -> Result<String> {
        let Some(mut rendered) = read_text(&self.resource_path(resource)) else {
            return Err(Error::fatal(format!(
                "MetaReducePlugin: failed to open resource {resource}"
            )));
        };
        for (tag, replacement) in replacements {
            if !rendered.contains(tag.as_str()) {
                ck.warn(&format!(
                    "MetaReducePlugin: tag {tag} does not occur in resource {resource}"
                ));
                continue;
            }
            if repl_all {
                rendered = replace_all(&rendered, tag, replacement);
            } else {
                rendered = rendered.replacen(tag.as_str(), replacement, 1);
            }
        }
        let out_path = self.output_path(output)?;
        if !write_text(&out_path, &rtrim_lines(&drop_resource_notes(&rendered))) {
            return Err(Error::fatal(format!(
                "MetaReducePlugin: failed to open output {out_path}"
            )));
        }
        Ok(out_path)
    }

    /// A new type variable `$eoT_<n>`.
    pub fn allocate_type_variable(&mut self, ck: &mut Checker) -> Term {
        self.type_var_counter += 1;
        let ty = ck.mk_type();
        ck.mk_symbol(
            SymbolKind::Param,
            &format!("$eoT_{}", self.type_var_counter),
            ty,
        )
    }
}

/// `text` with every occurrence of `from` replaced, left to right, never
/// looking again at what was put in.
pub fn replace_all(text: &str, from: &str, to: &str) -> String {
    if from.is_empty() {
        return text.to_string();
    }
    text.replace(from, to)
}

/// The subterms of `t` of kind `k`, each once, in the order a depth-first
/// walk that takes the last child first meets them.
pub fn subterms_of_kind(ck: &Checker, k: Kind, t: Term) -> Vec<Term> {
    let mut ret = Vec::new();
    let mut visited = HashSet::new();
    let mut to_visit = vec![t];
    while let Some(cur) = to_visit.pop() {
        if !visited.insert(cur) {
            continue;
        }
        if ck.store.kind(cur) == k {
            ret.push(cur);
        }
        to_visit.extend_from_slice(ck.store.children(cur));
    }
    ret
}

/// Whether `s` is `t` or occurs in it.
pub fn has_subterm(ck: &Checker, t: Term, s: Term) -> bool {
    let mut visited = HashSet::new();
    let mut to_visit = vec![t];
    while let Some(cur) = to_visit.pop() {
        if !visited.insert(cur) {
            continue;
        }
        if cur == s {
            return true;
        }
        to_visit.extend_from_slice(ck.store.children(cur));
    }
    false
}

/// The ground literal a type rule that uses `eo::self` is instantiated
/// with (`StdPlugin::getGroundTermForLiteralKind`).
pub fn ground_term_for_literal_kind(ck: &mut Checker, k: LitKind) -> Option<Term> {
    use pathos_term::{BitVec, EoString, Integer, Lit, Rational};
    let lit = match k {
        LitKind::Numeral => Lit::Numeral(Integer::zero()),
        LitKind::Rational => Lit::Rational(Rational::parse("0/1")?),
        LitKind::Binary => Lit::Binary(BitVec::parse("0", 2)?),
        LitKind::String => Lit::String(EoString::default()),
        _ => return None,
    };
    Some(ck.store.mk_lit(lit))
}

/// The name of a literal kind in `declare-consts`, e.g. `<numeral>`.
pub fn literal_kind_to_string(k: LitKind) -> Result<&'static str> {
    Ok(match k {
        LitKind::Numeral => "<numeral>",
        LitKind::Rational => "<rational>",
        LitKind::Binary => "<binary>",
        LitKind::String => "<string>",
        LitKind::Decimal => "<decimal>",
        LitKind::Hexadecimal => "<hexadecimal>",
        LitKind::Boolean => {
            return Err(Error::fatal(format!(
                "Unknown literal type rule{}\n",
                Kind::Lit(k)
            )));
        }
    })
}

/// The prefix of the name of a parse definition; see `plugins/utils.h`.
pub const PARSE_DEF_PREFIX: &str = "$parse_";

pub fn is_parse_def_name(name: &str) -> bool {
    name.starts_with(PARSE_DEF_PREFIX)
}

pub fn mk_parse_def_name(name: &str) -> String {
    format!("{PARSE_DEF_PREFIX}{name}")
}

/// `text` without the lines that are notes of a resource: those whose
/// first non-blank characters are `-- $` or `; $`.
pub fn drop_resource_notes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        let at = line.trim_start_matches([' ', '\t']);
        if !(at.starts_with("-- $") || at.starts_with("; $")) {
            out.push_str(line);
        }
    }
    out
}

/// `text` with no line ending in a space or a tab.
pub fn rtrim_lines(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut first = true;
    for line in text.split('\n') {
        if !first {
            out.push('\n');
        }
        first = false;
        out.push_str(line.trim_end_matches([' ', '\t']));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_helpers() {
        assert_eq!(rtrim_lines("a  \n\tb\t\n\n c "), "a\n\tb\n\n c");
        assert_eq!(rtrim_lines("a\n"), "a\n");
        assert_eq!(replace_all("aaa", "a", "aa"), "aaaaaa");
        assert_eq!(
            drop_resource_notes("a\n  ; $ note\nb\n-- $ note\n"),
            "a\nb\n"
        );
        assert_eq!(drop_resource_notes("a\n; $x"), "a\n");
        assert_eq!(drop_resource_notes("a\n;$ kept\n"), "a\n;$ kept\n");
        assert_eq!(parent_directory("/a/b/c.eo"), "/a/b");
        assert_eq!(parent_directory("/c.eo"), "/");
        assert_eq!(parent_directory("c.eo"), "");
    }
}
