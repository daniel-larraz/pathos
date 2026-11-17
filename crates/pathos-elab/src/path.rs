//! File paths as Ethos handles them (`util/filesystem.cpp`).
//!
//! Ethos has two implementations. Everywhere but on Windows a path is a
//! string, made canonical without looking at the file system: [`trim`],
//! [`is_absolute`], [`parent`] and [`canonical`]. On Windows it is a
//! `std::filesystem::path`, and the canonical path is the one the file
//! system gives: absolute, with backslashes, and only for a file that
//! exists. On both, an include names a file only if the path is a regular
//! file's. [`resolve`] is the one that applies on the platform pathos is
//! built for.

/// An include names no file to read: nothing has the name, or it is not a
/// regular file's (a directory's, say). Ethos's `includeFile` returns
/// false, and its caller reports that the file cannot be included.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct NotAFile;

/// The path that `file`, named in an include in the file `includer` (or on
/// the command line, with `includer` empty), refers to: the name the file is
/// opened by, shown in error messages by, and remembered as included by.
#[cfg(not(windows))]
pub(crate) fn resolve(includer: &str, file: &str) -> Result<String, NotAFile> {
    let name = name_of(includer, file);
    // `stat`, which follows links: a regular file
    if std::path::Path::new(&pathos_syntax::latin1::to_os(&name)).is_file() {
        Ok(name)
    } else {
        Err(NotAFile)
    }
}

/// The name [`resolve`] looks for, from the text alone.
#[cfg(not(windows))]
fn name_of(includer: &str, file: &str) -> String {
    let file = trim(file);
    let joined = if is_absolute(file) {
        file.to_string()
    } else {
        let mut p = parent(includer);
        p.push_str(file);
        p
    };
    canonical(&joined)
}

/// See the other version. Here as `State::includeFile` does it with
/// `std::filesystem`: the includer's `parent_path()`, `/=` the name as it
/// is written (no trimming), then `canonical()`, which leaves the path as
/// it is if nothing has it, then `exists()`, which also asks for a regular
/// file.
#[cfg(windows)]
pub(crate) fn resolve(includer: &str, file: &str) -> Result<String, NotAFile> {
    use pathos_syntax::latin1;
    use std::path::PathBuf;
    let mut joined = PathBuf::from(latin1::to_os(includer));
    joined.pop();
    joined.push(latin1::to_os(file));
    let Ok(found) = std::fs::canonicalize(&joined) else {
        return Err(NotAFile);
    };
    if !found.is_file() {
        return Err(NotAFile);
    }
    Ok(without_verbatim_prefix(&latin1::from_os(found.as_os_str())))
}

/// Rust's canonical paths on Windows are in the `\\?\` form, which C++'s
/// are not: `\\?\C:\dir` is `C:\dir` and `\\?\UNC\server\share` is
/// `\\server\share`.
#[cfg_attr(not(windows), allow(dead_code))]
fn without_verbatim_prefix(path: &str) -> String {
    if let Some(rest) = path.strip_prefix(r"\\?\UNC\") {
        format!(r"\\{rest}")
    } else if let Some(rest) = path.strip_prefix(r"\\?\") {
        rest.to_string()
    } else {
        path.to_string()
    }
}

/// Removes leading and trailing spaces. A string of spaces only is kept.
#[cfg_attr(windows, allow(dead_code))]
pub(crate) fn trim(raw: &str) -> &str {
    let t = raw.trim_matches(' ');
    if t.is_empty() { raw } else { t }
}

#[cfg_attr(windows, allow(dead_code))]
pub(crate) fn is_absolute(p: &str) -> bool {
    p.starts_with('/')
}

/// The path up to and including the last `/`; empty if there is none.
#[cfg_attr(windows, allow(dead_code))]
pub(crate) fn parent(p: &str) -> String {
    match p.rfind('/') {
        Some(last) => trim(&p[..=last]).to_string(),
        None => String::new(),
    }
}

/// Removes empty and `.` segments and resolves `..` against the segments
/// before it. The last segment is kept as it is, even if it is empty, `.`
/// or `..`.
#[cfg_attr(windows, allow(dead_code))]
pub(crate) fn canonical(p: &str) -> String {
    if p.is_empty() {
        return String::new();
    }
    let is_abs = is_absolute(p);
    let mut parent_prefix = 0usize;
    let mut segments: Vec<&str> = Vec::new();
    let mut parts = p.split('/').peekable();
    while let Some(seg) = parts.next() {
        if parts.peek().is_none() {
            // the last segment
            segments.push(seg);
            break;
        }
        match seg {
            "" | "." => {}
            ".." => {
                if segments.pop().is_none() {
                    parent_prefix += 1;
                }
            }
            _ => segments.push(seg),
        }
    }
    let mut out = String::new();
    if is_abs {
        out.push('/');
    }
    for _ in 0..parent_prefix {
        out.push_str("../");
    }
    out.push_str(&segments.join("/"));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_paths() {
        assert_eq!(canonical("/a/b/../c.eo"), "/a/c.eo");
        assert_eq!(canonical("a/./b//c.eo"), "a/b/c.eo");
        assert_eq!(canonical("../x.eo"), "../x.eo");
        assert_eq!(canonical("a/../../x.eo"), "../x.eo");
        assert_eq!(canonical("./simple.eo"), "simple.eo");
        assert_eq!(canonical("x.eo"), "x.eo");
        assert_eq!(canonical("/x.eo"), "/x.eo");
        assert_eq!(canonical("a/"), "a/");
    }

    #[test]
    fn verbatim_prefixes() {
        assert_eq!(without_verbatim_prefix(r"\\?\C:\a\b.eo"), r"C:\a\b.eo");
        assert_eq!(without_verbatim_prefix(r"\\?\UNC\s\d\b.eo"), r"\\s\d\b.eo");
        assert_eq!(without_verbatim_prefix(r"C:\a"), r"C:\a");
    }

    #[cfg(not(windows))]
    #[test]
    fn resolving() {
        assert_eq!(name_of("", " a/../b.eo "), "b.eo");
        assert_eq!(name_of("d/main.eo", "sub/x.eo"), "d/sub/x.eo");
        assert_eq!(name_of("d/main.eo", "/x.eo"), "/x.eo");
        // only a regular file is one
        assert_eq!(resolve("", "no-such-file.eo"), Err(NotAFile));
        assert_eq!(resolve("", "/"), Err(NotAFile));
    }

    #[test]
    fn parents() {
        assert_eq!(parent("/a/b/c.eo"), "/a/b/");
        assert_eq!(parent("c.eo"), "");
        assert_eq!(trim("  a b  "), "a b");
        assert_eq!(trim("   "), "   ");
    }
}
