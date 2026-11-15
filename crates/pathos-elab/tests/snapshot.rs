//! Signature snapshots: a run that uses one must behave as a run that
//! parses the signature, and a snapshot that does not fit must be ignored.

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use pathos_check::Options;
use pathos_elab::{State, include_file};
use pathos_term::codec::content_hash;

/// A directory of its own for a test, with the signature files in it.
fn setup(test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("snapshot-{test}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("sig/theories")).unwrap();
    std::fs::create_dir_all(dir.join("proofs")).unwrap();
    let write = |name: &str, text: &str| std::fs::write(dir.join(name), text).unwrap();
    write(
        "sig/Sig.eo",
        "(include \"theories/Core.eo\")
(include \"./theories/Core.eo\")
(echo \"signature loaded\")
(program $flip ((T Type) (x T) (y T)) :signature (Bool) Bool
  ((($flip (= x y)) (= y x))))
(declare-rule symm ((F Bool)) :premises (F) :conclusion ($flip F))
(declare-rule trust ((F Bool)) :args (F) :conclusion F :sorry)
(declare-const three Int)
(define tw () (eo::add 1 1))
(define h () (eo::hash three))
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
(declare-const and (-> Int Int Int))
",
    );
    write(
        "sig/theories/Core.eo",
        "(echo \"core\")
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const a Int)
(declare-const b Int)
",
    );
    write(
        "proofs/p.cpc",
        "(include \"../sig/Sig.eo\")
(include \"../sig/theories/Core.eo\")
(assume p (= a b))
(step q (= b a) :rule symm :premises (p))
(step r (= a b) :rule symm :premises (q))
(echo \"checked\")
(define k () (eo::hash b))
(step s (= k 2) :rule trust :args ((= k 2)))
(step t (= k 3) :rule symm :premises (s))
",
    );
    dir
}

fn path_str(p: &Path) -> String {
    p.to_str().unwrap().to_string()
}

struct Run {
    result: Result<bool, String>,
    /// Each line printed, and whether it was a warning.
    output: Vec<(bool, String)>,
    stats: String,
    used_snapshot: bool,
}

/// The lines a run printed, and whether each was a warning.
type Output = Rc<RefCell<Vec<(bool, String)>>>;

fn new_state(opts: Options) -> (State, Output) {
    let output = Rc::new(RefCell::new(Vec::new()));
    let (w, o) = (output.clone(), output.clone());
    let st = State::new(
        opts,
        Box::new(move |l| w.borrow_mut().push((true, l.to_string()))),
        Box::new(move |l| o.borrow_mut().push((false, l.to_string()))),
    );
    (st, output)
}

/// Checks the proof file, with the snapshot if one is given.
fn check(proof: &Path, opts: Options, snapshot: Option<&[u8]>) -> Run {
    let (mut st, output) = new_state(opts);
    if let Some(bytes) = snapshot {
        st.offer_snapshot(bytes.to_vec());
    }
    let parsed = include_file(&mut st, &path_str(proof), false, false, None);
    // the counts of the statistics; the other lines hold times
    let text = st.ck.stats_string();
    let stats: Vec<String> = (text.lines())
        .filter(|l| l.starts_with("ruleCount") || l.starts_with("progCount"))
        .map(sorted_entries)
        .collect();
    Run {
        result: match parsed {
            Ok(()) => Ok(st.ck.used_sorry_rule()),
            Err(e) => Err(e.to_string()),
        },
        output: output.take(),
        stats: stats.join("\n"),
        used_snapshot: st.used_snapshot(),
    }
}

/// A compact statistics line, `name = { a: 1, b: 2 }`, with its entries in
/// the order of their text. The statistics order them by time taken, which
/// differs from run to run; what the tests compare is the counts.
fn sorted_entries(line: &str) -> String {
    let (Some(open), Some(close)) = (line.find("{ "), line.rfind(" }")) else {
        return line.to_string();
    };
    if close < open + 2 {
        return line.to_string();
    }
    let mut entries: Vec<&str> = line[open + 2..close].split(", ").collect();
    entries.sort_unstable();
    format!("{}{} }}", &line[..open + 2], entries.join(", "))
}

#[test]
fn statistics_are_compared_without_their_order() {
    assert_eq!(
        sorted_entries("ruleCount = { symm: 2, trust: 1 }"),
        sorted_entries("ruleCount = { trust: 1, symm: 2 }")
    );
    assert_ne!(
        sorted_entries("ruleCount = { symm: 2, trust: 1 }"),
        sorted_entries("ruleCount = { symm: 1, trust: 2 }")
    );
    assert_eq!(sorted_entries("ruleCount = { }"), "ruleCount = { }");
}

/// The snapshot of the signature file.
fn snapshot_of(sig: &Path, opts: Options) -> Vec<u8> {
    let (mut st, output) = new_state(opts);
    st.record_for_snapshot();
    include_file(&mut st, &path_str(sig), true, false, None).unwrap();
    st.write_snapshot(&output.borrow()).unwrap()
}

fn stats_options() -> Options {
    let mut opts = Options::default();
    assert!(opts.set_option("stats-all", true));
    assert!(opts.set_option("stats-compact", true));
    opts
}

fn assert_same(with: &Run, without: &Run) {
    assert_eq!(with.result, without.result);
    assert_eq!(with.output, without.output);
    assert_eq!(with.stats, without.stats);
}

#[test]
fn a_run_with_a_snapshot_behaves_as_one_without() {
    let dir = setup("same");
    let proof = dir.join("proofs/p.cpc");
    let snap = snapshot_of(&dir.join("sig/Sig.eo"), Options::default());
    // The snapshot was written without --stats, and serves a run with it.
    let without = check(&proof, stats_options(), None);
    let with = check(&proof, stats_options(), Some(&snap));
    assert!(with.used_snapshot);
    assert!(!without.used_snapshot);
    assert_same(&with, &without);
    // The proof is rejected at its last step, after the echoes.
    assert_eq!(
        without.output,
        [
            (false, "core".to_string()),
            (false, "signature loaded".to_string()),
            (false, "checked".to_string()),
        ]
    );
    let err = without.result.unwrap_err();
    // `k` is the second term hashed: `three` was, in the signature
    assert!(err.contains("Proves: (_ (= 2) 2)"), "{err}");
    assert!(
        without.stats.contains("$flip: 3"),
        "{}",
        without.stats
    );
}

#[test]
fn writing_a_snapshot_twice_gives_the_same_bytes() {
    let dir = setup("deterministic");
    let sig = dir.join("sig/Sig.eo");
    assert_eq!(
        snapshot_of(&sig, Options::default()),
        snapshot_of(&sig, Options::default())
    );
}

#[test]
fn the_signature_may_be_reached_by_another_name() {
    let dir = setup("names");
    // written for an absolute path with a detour, used through `../sig`
    let snap = snapshot_of(&dir.join("proofs/../sig/./Sig.eo"), Options::default());
    let proof = dir.join("proofs/p.cpc");
    let with = check(&proof, Options::default(), Some(&snap));
    assert!(with.used_snapshot);
    // Core.eo is not read again by the proof's own include of it
    assert_same(&with, &check(&proof, Options::default(), None));
}

#[test]
fn a_snapshot_is_ignored_when_a_file_has_changed() {
    let dir = setup("changed");
    let proof = dir.join("proofs/p.cpc");
    let snap = snapshot_of(&dir.join("sig/Sig.eo"), Options::default());
    let core = dir.join("sig/theories/Core.eo");
    let mut text = std::fs::read_to_string(&core).unwrap();
    text.push_str("(echo \"changed\")\n");
    std::fs::write(&core, text).unwrap();
    let with = check(&proof, Options::default(), Some(&snap));
    assert!(!with.used_snapshot);
    assert!(with.output.contains(&(false, "changed".to_string())));
    assert_same(&with, &check(&proof, Options::default(), None));
}

#[test]
fn a_snapshot_is_ignored_under_other_options() {
    let dir = setup("options");
    let proof = dir.join("proofs/p.cpc");
    let snap = snapshot_of(&dir.join("sig/Sig.eo"), Options::default());
    for option in ["rule-sym-table", "parse-let", "print-dag", "normalize-dec"] {
        let mut opts = Options::default();
        assert!(opts.set_option(option, false));
        let with = check(&proof, opts.clone(), Some(&snap));
        assert!(!with.used_snapshot, "{option}");
        assert_same(&with, &check(&proof, opts, None));
    }
}

#[test]
fn a_snapshot_is_ignored_once_the_state_has_changed() {
    let dir = setup("late");
    let snap = snapshot_of(&dir.join("sig/Sig.eo"), Options::default());
    let proof = dir.join("proofs/late.cpc");
    std::fs::write(
        &proof,
        "(declare-const early Bool)\n(include \"../sig/Sig.eo\")\n(assume p (= a b))\n",
    )
    .unwrap();
    let with = check(&proof, Options::default(), Some(&snap));
    assert!(!with.used_snapshot);
    assert_same(&with, &check(&proof, Options::default(), None));
}

#[test]
fn a_snapshot_is_not_used_for_another_file() {
    let dir = setup("other");
    let snap = snapshot_of(&dir.join("sig/Sig.eo"), Options::default());
    let proof = dir.join("proofs/other.cpc");
    std::fs::write(
        &proof,
        "(include \"../sig/theories/Core.eo\")\n(assume p (= a b))\n",
    )
    .unwrap();
    let with = check(&proof, Options::default(), Some(&snap));
    assert!(!with.used_snapshot);
    assert_eq!(with.result, Ok(false));
}

#[test]
fn damaged_snapshots_are_ignored() {
    let dir = setup("damaged");
    let proof = dir.join("proofs/p.cpc");
    let snap = snapshot_of(&dir.join("sig/Sig.eo"), Options::default());
    let without = check(&proof, Options::default(), None);
    let mut damaged: Vec<Vec<u8>> = vec![Vec::new(), b"PATHSNAP".to_vec()];
    // cut short, at a spread of lengths
    for len in (0..snap.len()).step_by(snap.len() / 60 + 1) {
        damaged.push(snap[..len].to_vec());
    }
    // one byte changed, at a spread of places
    for i in (0..snap.len()).step_by(snap.len() / 200 + 1) {
        let mut bytes = snap.clone();
        bytes[i] ^= 0x5a;
        damaged.push(bytes);
    }
    // with something after the end
    let mut longer = snap.clone();
    longer.push(0);
    damaged.push(longer);
    for bytes in &damaged {
        let with = check(&proof, Options::default(), Some(bytes));
        assert!(!with.used_snapshot);
        assert_same(&with, &without);
    }
}

/// A snapshot whose content was changed and whose checksum was made to fit
/// is beyond what the checksum can find. Reading it must still not panic,
/// whatever it holds.
#[test]
fn reading_a_forged_snapshot_does_not_panic() {
    let dir = setup("forged");
    let sig = dir.join("sig/Sig.eo");
    let snap = snapshot_of(&sig, Options::default());
    let body_start = 8 + 4 + 8;
    let mut used = 0;
    for i in body_start..snap.len() {
        for flip in [0x01u8, 0x80, 0xff] {
            let mut bytes = snap.clone();
            bytes[i] ^= flip;
            let checksum = content_hash(&bytes[body_start..]);
            bytes[12..20].copy_from_slice(&checksum.to_le_bytes());
            let (mut st, _) = new_state(Options::default());
            st.offer_snapshot(bytes);
            // an error is fine: a forged list of files may name one that
            // cannot be read, and then the signature is parsed
            let _ = include_file(&mut st, &path_str(&sig), true, false, None);
            used += usize::from(st.used_snapshot());
        }
    }
    // Most changes are caught by the checks on the content; the rest give a
    // state that differs in a name, a number or a term.
    assert!(used < (snap.len() - body_start) * 3);
}
