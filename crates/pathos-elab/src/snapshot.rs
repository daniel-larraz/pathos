//! Signature snapshots: the state after loading a signature, saved to a
//! file, so that later runs need not parse the signature again.
//!
//! A run with a snapshot must print exactly what it would print without
//! one. So the snapshot is not loaded up front: it is used at the moment
//! the run includes the signature it holds, and only if at that moment
//!
//! - nothing has changed the state since the start of the run (the state
//!   hashes to what it hashed to when the snapshot's run began);
//! - the options that decide how a signature loads are those of the
//!   snapshot's run;
//! - every file the signature included has the content it had then, and
//!   the names by which this run would reach those files include the same
//!   files once and skip the same repeats.
//!
//! Then the state is replaced by the saved one, the files are marked as
//! included, and what the signature printed is printed again. In every
//! other case the snapshot is ignored without a word, and the signature is
//! parsed as usual.
//!
//! A snapshot is trusted as the signature itself is: its checksum finds
//! damage, not forgery. Reading one never panics and never allocates more
//! than a small multiple of the file's size, but a file made on purpose
//! with a valid checksum can hold a state no signature gives.

use std::collections::HashSet;

use pathos_check::Options;
use pathos_syntax::{Error, Result};
use pathos_term::codec::{Reader, Writer, content_hash};

use crate::parser::read_file;
use crate::state::{State, resolve_include_from};

const MAGIC: &[u8; 8] = b"PATHSNAP";
/// Changes whenever the layout of the file does.
const FORMAT: u32 = 1;
const VERSION: &str = env!("CARGO_PKG_VERSION");
const NO_PARENT: u32 = u32::MAX;

/// One `include` (or `reference`) met while loading the signature.
struct IncludeEntry {
    /// The entry of the file whose command this is; none for the signature
    /// itself.
    parent: Option<u32>,
    /// The file name as the command gives it.
    name: String,
    /// What the file held, if it was read: the length and the hash of its
    /// content. `None` for a file that had been included before.
    content: Option<(u64, u64)>,
}

/// What a run records for the snapshot it will write.
pub(crate) struct Recording {
    /// The hash and the number of terms of the state before anything was
    /// read.
    pristine: (u64, u32),
    entries: Vec<IncludeEntry>,
    /// The entries of the files being read, outermost first.
    open: Vec<u32>,
    root_is_signature: bool,
}

/// The hash of everything a snapshot restores, and the number of terms.
fn state_hash(st: &State) -> (u64, u32) {
    let mut w = Writer::new();
    st.write_image(&mut w);
    let terms = u32::try_from(st.ck.store.len()).unwrap_or(u32::MAX);
    (content_hash(&w.bytes), terms)
}

impl State {
    /// Starts recording what a snapshot of this run needs. Call this
    /// before anything is read.
    pub fn record_for_snapshot(&mut self) {
        self.ck.count_programs();
        self.recording = Some(Recording {
            pristine: state_hash(self),
            entries: Vec::new(),
            open: Vec::new(),
            root_is_signature: false,
        });
    }

    /// Notes an include. `content` is that of the file if it is read now.
    pub(crate) fn record_include(
        &mut self,
        name: &str,
        is_signature: bool,
        content: Option<&[u8]>,
    ) {
        let Some(rec) = &mut self.recording else {
            return;
        };
        if rec.entries.is_empty() {
            rec.root_is_signature = is_signature;
        }
        let index = u32::try_from(rec.entries.len()).unwrap_or(NO_PARENT);
        rec.entries.push(IncludeEntry {
            parent: rec.open.last().copied(),
            name: name.to_string(),
            content: content.map(|c| (c.len() as u64, content_hash(c))),
        });
        if content.is_some() {
            rec.open.push(index);
        }
    }

    /// Notes that the file being read has been read to its end.
    pub(crate) fn record_include_end(&mut self) {
        if let Some(rec) = &mut self.recording {
            rec.open.pop();
        }
    }

    /// The snapshot of this run: the state as it is now, with what
    /// [`State::record_for_snapshot`] has recorded since. `output` is what
    /// the run printed: each line, and whether it was a warning.
    pub fn write_snapshot(&self, output: &[(bool, String)]) -> Result<Vec<u8>> {
        let Some(rec) = &self.recording else {
            return Err(Error::plain("the run was not recorded for a snapshot"));
        };
        // A snapshot is used in place of one include, so it must be the
        // state after exactly one: the signature named on the command line.
        let roots = rec.entries.iter().filter(|e| e.parent.is_none()).count();
        if roots != 1 || !rec.open.is_empty() || self.assumption_level() != 0 {
            return Err(Error::plain(
                "a snapshot holds one signature, read to its end",
            ));
        }
        let mut w = Writer::new();
        w.str(VERSION);
        let key = self.ck.opts.snapshot_key();
        w.len(key.len());
        w.bytes.extend_from_slice(&key);
        w.u64(rec.pristine.0);
        w.u32(rec.pristine.1);
        w.bool(rec.root_is_signature);
        w.len(rec.entries.len());
        for e in &rec.entries {
            w.u32(e.parent.unwrap_or(NO_PARENT));
            w.str(&e.name);
            match e.content {
                Some((len, hash)) => {
                    w.bool(true);
                    w.u64(len);
                    w.u64(hash);
                }
                None => w.bool(false),
            }
        }
        w.len(output.len());
        for (is_warning, line) in output {
            w.bool(*is_warning);
            w.str(line);
        }
        self.write_image(&mut w);

        let mut file = Vec::with_capacity(w.bytes.len() + 20);
        file.extend_from_slice(MAGIC);
        file.extend_from_slice(&FORMAT.to_le_bytes());
        file.extend_from_slice(&content_hash(&w.bytes).to_le_bytes());
        file.extend_from_slice(&w.bytes);
        Ok(file)
    }

    /// Gives the run a snapshot to use when it includes the snapshot's
    /// signature. A file that is not a snapshot this run can use is
    /// ignored.
    pub fn offer_snapshot(&mut self, file: Vec<u8>) {
        self.snapshot = Snapshot::open(file, &self.ck.opts);
    }

    /// Whether a snapshot stood in for reading its signature.
    pub fn used_snapshot(&self) -> bool {
        self.used_snapshot
    }
}

/// A snapshot file that is whole and was written under this run's options.
pub(crate) struct Snapshot {
    file: Vec<u8>,
    /// Where the part after the options starts.
    start: usize,
    pristine: (u64, u32),
    root_is_signature: bool,
}

/// What became of an attempt to use the snapshot for an include.
enum Outcome {
    Used,
    /// This include is not the snapshot's signature; a later one may be.
    NotThisFile,
}

impl Snapshot {
    fn open(file: Vec<u8>, opts: &Options) -> Option<Snapshot> {
        let mut r = Reader::new(&file);
        if r.bytes(MAGIC.len())? != MAGIC || r.u32()? != FORMAT {
            return None;
        }
        let checksum = r.u64()?;
        let body = &file[MAGIC.len() + 12..];
        if content_hash(body) != checksum || r.str()? != VERSION {
            return None;
        }
        let key_len = r.len(1)?;
        if r.bytes(key_len)? != opts.snapshot_key() {
            return None;
        }
        let pristine = (r.u64()?, r.u32()?);
        let root_is_signature = r.bool()?;
        let start = file.len() - r.remaining();
        Some(Snapshot {
            file,
            start,
            pristine,
            root_is_signature,
        })
    }
}

/// Called when a file is about to be read for the first time. Returns true
/// if the snapshot the run was given stood in for it: the state is then as
/// if the file had been read.
pub(crate) fn use_for_include(
    st: &mut State,
    path: &str,
    is_signature: bool,
    is_reference: bool,
) -> bool {
    let Some(snap) = st.snapshot.take() else {
        return false;
    };
    match try_use(st, &snap, path, is_signature, is_reference) {
        Some(Outcome::Used) => true,
        Some(Outcome::NotThisFile) => {
            st.snapshot = Some(snap);
            false
        }
        // the snapshot can no longer be used in this run
        None => false,
    }
}

/// `None` if something in the snapshot cannot be read or does not fit this
/// run: it is then of no use for a later include either.
fn try_use(
    st: &mut State,
    snap: &Snapshot,
    path: &str,
    is_signature: bool,
    is_reference: bool,
) -> Option<Outcome> {
    // Terms are never removed, so a state that has gained one will never
    // be the snapshot's starting state again.
    if st.ck.store.len() != snap.pristine.1 as usize {
        return None;
    }
    if is_reference || is_signature != snap.root_is_signature {
        return Some(Outcome::NotThisFile);
    }
    let mut r = Reader::new(snap.file.get(snap.start..)?);
    // an include takes at least 9 bytes
    let n = r.len(9)?;
    let mut entries = Vec::with_capacity(n);
    for i in 0..n {
        let parent = match r.u32()? {
            NO_PARENT if i == 0 => None,
            p if (p as usize) < i => Some(p),
            _ => return None,
        };
        let name = r.str()?.to_string();
        let content = match r.bool()? {
            true => Some((r.u64()?, r.u64()?)),
            false => None,
        };
        entries.push(IncludeEntry {
            parent,
            name,
            content,
        });
    }
    // The signature itself: the same length, then the same content.
    let &(root_len, root_hash) = entries.first()?.content.as_ref()?;
    if file_len(path) != Some(root_len) {
        return Some(Outcome::NotThisFile);
    }
    let same_content = |path: &str, len: u64, hash: u64| {
        read_file(path).is_ok_and(|c| c.len() as u64 == len && content_hash(&c) == hash)
    };
    if !same_content(path, root_len, root_hash) {
        return Some(Outcome::NotThisFile);
    }
    if state_hash(st) != snap.pristine {
        return None;
    }
    // The files the signature included, under the names this run reaches
    // them by: each must be new where it was new and a repeat where it was
    // a repeat, and unchanged.
    let mut paths: Vec<String> = Vec::with_capacity(n);
    let mut added: HashSet<&str> = HashSet::new();
    paths.push(path.to_string());
    for e in &entries[1..] {
        let includer = paths.get(e.parent? as usize)?;
        paths.push(resolve_include_from(includer, &e.name));
    }
    for (e, p) in entries.iter().zip(&paths).skip(1) {
        // only a file that was read can include another
        entries.get(e.parent? as usize)?.content?;
        let seen = p == path || st.is_included(p) || added.contains(p.as_str());
        match e.content {
            Some((len, hash)) if !seen && same_content(p, len, hash) => {
                added.insert(p);
            }
            None if seen => {}
            _ => return None,
        }
    }
    let n = r.len(5)?;
    let mut output = Vec::with_capacity(n);
    for _ in 0..n {
        output.push((r.bool()?, r.str()?));
    }
    let image = st.read_image(&mut r)?;
    if !r.is_at_end() {
        return None;
    }

    st.install(image);
    st.used_snapshot = true;
    for p in added {
        st.mark_included(p);
    }
    for (is_warning, line) in output {
        if is_warning {
            st.ck.warn(line);
        } else {
            st.print_line(line);
        }
    }
    Some(Outcome::Used)
}

/// The length of the file, if it is a regular file.
fn file_len(path: &str) -> Option<u64> {
    use std::os::unix::ffi::OsStringExt;
    let os_path = std::ffi::OsString::from_vec(pathos_syntax::latin1::encode(path));
    let meta = std::fs::metadata(os_path).ok()?;
    meta.is_file().then_some(meta.len())
}
