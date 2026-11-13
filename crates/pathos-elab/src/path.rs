//! File paths as Ethos handles them (`util/filesystem.cpp`): as strings,
//! without looking at the file system.

/// Removes leading and trailing spaces. A string of spaces only is kept.
pub(crate) fn trim(raw: &str) -> &str {
    let t = raw.trim_matches(' ');
    if t.is_empty() { raw } else { t }
}

pub(crate) fn is_absolute(p: &str) -> bool {
    p.starts_with('/')
}

/// The path up to and including the last `/`; empty if there is none.
pub(crate) fn parent(p: &str) -> String {
    match p.rfind('/') {
        Some(last) => trim(&p[..=last]).to_string(),
        None => String::new(),
    }
}

/// Removes empty and `.` segments and resolves `..` against the segments
/// before it. The last segment is kept as it is, even if it is empty, `.`
/// or `..`.
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
    fn parents() {
        assert_eq!(parent("/a/b/c.eo"), "/a/b/");
        assert_eq!(parent("c.eo"), "");
        assert_eq!(trim("  a b  "), "a b");
        assert_eq!(trim("   "), "   ");
    }
}
