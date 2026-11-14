//! The native layer of a backend (`plugins/native_layer.cpp` in Ethos): the
//! definitions its generated text may call and no stage writes, and the
//! part of them that a compilation reaches.
//!
//! A layer is a file of blocks. The line that opens a block is
//! `<comment> $native <name> <needs> <calls>...`: what the block defines,
//! the narrowest scope it can come out in, and the other blocks it calls.
//! A line `<comment> $native-keep <name>...` names the blocks that are kept
//! whatever the input reaches. A stage notes each name as it prints it,
//! with the scope the text comes out in.

use std::collections::BTreeMap;

use pathos_syntax::{Error, Result};

use crate::std_plugin::read_text;

struct Def {
    name: String,
    /// The narrowest scope the block can come out in.
    needs: String,
    /// The blocks it calls.
    deps: Vec<String>,
    text: String,
}

pub struct NativeLayer {
    /// The scope every module sees.
    top: String,
    /// The blocks, in the layer's order.
    defs: Vec<Def>,
    /// The block that defines each name.
    of: BTreeMap<String, usize>,
    /// The blocks reached, and the scope each comes out in.
    at: BTreeMap<String, String>,
}

/// The words of a line, as `>>` reads them.
fn words(s: &str) -> Vec<String> {
    s.split([' ', '\t', '\n', '\x0b', '\x0c', '\r'])
        .filter(|w| !w.is_empty())
        .map(str::to_string)
        .collect()
}

impl NativeLayer {
    /// Reads the layer at `path`. `comment` opens a comment in the layer's
    /// language; `top` is the scope every module sees.
    pub fn new(path: &str, comment: &str, top: &str) -> Result<NativeLayer> {
        let Some(text) = read_text(path) else {
            return Err(Error::fatal(format!("NativeLayer: could not read {path}")));
        };
        let opens = format!("{comment} $native");
        let keeps = format!("{opens}-keep ");
        let block = format!("{opens} ");
        let mut layer = NativeLayer {
            top: top.to_string(),
            defs: Vec::new(),
            of: BTreeMap::new(),
            at: BTreeMap::new(),
        };
        let mut keep = Vec::new();
        let mut lines: Vec<&str> = text.split('\n').collect();
        if lines.last() == Some(&"") {
            lines.pop();
        }
        for line in lines {
            if !line.starts_with(&opens) {
                // part of the block above, its own comments included
                if let Some(last) = layer.defs.last_mut() {
                    last.text.push_str(line);
                    last.text.push('\n');
                }
                continue;
            }
            let rest = match (line.strip_prefix(&keeps), line.strip_prefix(&block)) {
                (Some(rest), _) => {
                    keep = words(rest);
                    continue;
                }
                (None, Some(rest)) => rest,
                (None, None) => {
                    return Err(Error::fatal(format!(
                        "NativeLayer: `{line}` is not a line {path} writes"
                    )));
                }
            };
            let ws = words(rest);
            let [name, needs, deps @ ..] = ws.as_slice() else {
                return Err(Error::fatal(format!(
                    "NativeLayer: a block says its name and the narrowest scope it can come \
                     out in, got `{line}`"
                )));
            };
            layer.of.insert(name.clone(), layer.defs.len());
            layer.defs.push(Def {
                name: name.clone(),
                needs: needs.clone(),
                deps: deps.to_vec(),
                text: String::new(),
            });
        }
        if layer.defs.is_empty() {
            return Err(Error::fatal(format!("NativeLayer: {path} holds no block")));
        }
        // what the stage's own resources name
        for n in keep {
            layer.use_in(&n, top)?;
        }
        Ok(layer)
    }

    /// Notes that the top scope names `n`.
    pub fn use_top(&mut self, n: &str) -> Result<()> {
        let top = self.top.clone();
        self.use_in(n, &top)
    }

    /// Notes that the module of scope `scope` names `n`: the block defining
    /// `n` is wanted, and so is everything it calls. A block reached from
    /// two scopes comes out in the top one. A name the layer does not
    /// define is ignored.
    pub fn use_in(&mut self, n: &str, scope: &str) -> Result<()> {
        // the names still to note, last first, each with its scope
        let mut pending = vec![(n.to_string(), scope.to_string())];
        while let Some((n, scope)) = pending.pop() {
            let Some(&index) = self.of.get(&n) else {
                continue;
            };
            let d = &self.defs[index];
            let mut at = scope.clone();
            if d.needs != self.top {
                if scope != d.needs && scope != self.top {
                    return Err(Error::fatal(format!(
                        "NativeLayer: `{n}` comes out in {}, which the {scope} scope that \
                         names it cannot see",
                        d.needs
                    )));
                }
                at = d.needs.clone();
            }
            match self.at.get_mut(&n) {
                None => {
                    self.at.insert(n, at.clone());
                }
                Some(known) if *known == at => continue,
                Some(known) => {
                    // reached from two scopes
                    at = self.top.clone();
                    if *known == at {
                        continue;
                    }
                    *known = at.clone();
                }
            }
            for dep in d.deps.iter().rev() {
                pending.push((dep.clone(), at.clone()));
            }
        }
        Ok(())
    }

    /// The blocks that come out in `scope`, in the layer's order, without
    /// the blank lines after the last.
    pub fn defs(&self, scope: &str) -> String {
        let mut out = String::new();
        for d in &self.defs {
            if self.at.get(&d.name).is_some_and(|at| at == scope) {
                out.push_str(&d.text);
            }
        }
        out.truncate(out.trim_end_matches('\n').len());
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn layer(name: &str, text: &str) -> Result<NativeLayer> {
        let dir = format!(
            "{}/../../target/tmp/native-layer",
            env!("CARGO_MANIFEST_DIR")
        );
        std::fs::create_dir_all(&dir).unwrap();
        let path = format!("{dir}/{name}");
        std::fs::write(&path, text).unwrap();
        NativeLayer::new(&path, ";", "Vc")
    }

    const LAYER: &str = "; a header, part of no block
; $native-keep Kept
; $native Kept Vc
(define-sort Kept () Int)

; $native Nat Vc
; the naturals
(declare-datatype Nat ((nat.zero) (nat.succ (pred Nat))))

; $native len Embed Nat helper
(define-fun len () Nat nat.zero)

; $native helper Vc
(define-fun helper () Int 0)

; $native unused Vc
(define-fun unused () Int 1)
";

    #[test]
    fn blocks_come_out_where_they_are_needed() {
        let mut l = layer("ok.smt2", LAYER).unwrap();
        // only what is kept, without the blank line after the last block
        assert_eq!(l.defs("Vc"), "(define-sort Kept () Int)");
        assert_eq!(l.defs("Embed"), "");
        // `len` can only come out in Embed; what it calls follows it there
        l.use_in("len", "Embed").unwrap();
        assert_eq!(
            l.defs("Embed"),
            "; the naturals\n(declare-datatype Nat ((nat.zero) (nat.succ (pred Nat))))\n\n(define-fun len () Nat nat.zero)\n\n(define-fun helper () Int 0)"
        );
        // reached from the top scope too: it moves there, in the layer's order
        l.use_top("Nat").unwrap();
        assert_eq!(
            l.defs("Vc"),
            "(define-sort Kept () Int)\n\n; the naturals\n(declare-datatype Nat ((nat.zero) (nat.succ (pred Nat))))"
        );
        assert_eq!(
            l.defs("Embed"),
            "(define-fun len () Nat nat.zero)\n\n(define-fun helper () Int 0)"
        );
        // a name the layer does not define is nothing to place
        l.use_in("nothing", "Embed").unwrap();
    }

    #[test]
    fn errors() {
        let err = |r: Result<NativeLayer>| r.err().map(|e| e.to_string()).unwrap_or_default();
        assert!(err(layer("empty.smt2", "; nothing\n")).ends_with("holds no block"));
        assert!(err(layer("glued.smt2", "; $nativex y Vc\n")).contains("is not a line"));
        assert!(err(layer("short2.smt2", "; $native x \n")).contains("a block says its name"));
        assert!(err(NativeLayer::new("/nonexistent/layer", ";", "Vc")).contains("could not read"));
        // a block of one scope named from another that cannot see it
        let mut l = layer("scopes.smt2", "; $native a Embed\nA\n").unwrap();
        let e = l.use_in("a", "Other").unwrap_err().to_string();
        assert_eq!(
            e,
            "NativeLayer: `a` comes out in Embed, which the Other scope that names it cannot see"
        );
    }
}
