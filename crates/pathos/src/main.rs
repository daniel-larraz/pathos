//! `pathos`: the checker for CPC proofs.
//!
//! The front end is pathos's own, shared with `pathos-eo`; the checker is
//! the one Ethos's `rust-meta` stage compiles from logos's CPC
//! (`generated/cpc-checker`). See `adapter.rs` for how the one feeds the
//! other. Like logos, it takes one proof and prints `correct` (exit status
//! 0), `incorrect` (1) or `incomplete` (2); a proof it cannot read is an
//! error on standard error, with status 1 and no verdict.

mod adapter;
mod explain;

use std::cell::RefCell;
use std::io::{IsTerminal, Write};
use std::process::ExitCode;
use std::rc::Rc;

use pathos_check::Options;
use pathos_compiled_checker::Verdict;
use pathos_elab::{Parser, State, include_file};
use pathos_syntax::{Result, latin1, textmode};

/// CPC as logos has it: the signature the checker was compiled from, and
/// the one the front end reads the proof against.
const CPC: &[u8] = include_bytes!("../../../generated/cpc-checker/Cpc.cached.eo");

/// The state after reading [`CPC`], made by `build.rs`.
const CPC_IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/cpc.image"));

const USAGE: &str = "usage: pathos [options] <proof.cpc>

Checks a CPC proof, as cvc5 writes it with --dump-proofs, and prints
correct, incorrect or incomplete (exit status 0, 1 or 2).

  --explain      for an incorrect proof, also say on standard error which
                 command the checker does not accept
  --no-cache     run the checker without its caches of types and of
                 program results
  --cache-stats  print the caches' hits, misses and sizes on standard error
  --depth=N      let the checker's functions nest N deep (default 4096).
                 The default is what the checker's 64 MiB stack is sized
                 for; far beyond it, the run ends with a stack overflow
                 instead of an error
  --profile      print on standard error the checker's time by rule (it
                 runs the checker once more for that)
";

fn write_line(mut w: impl Write + IsTerminal, line: &str) {
    let utf8_only = textmode::wants_utf8(&w);
    // Nothing useful can be done if stdout or stderr is closed.
    let _ = textmode::write(&mut w, &format!("{line}\n"), utf8_only);
}

/// Writes `text` as it is. Not `print!`, which panics when the write fails
/// (a full disk, a closed pipe).
fn write_text(mut w: impl Write + IsTerminal, text: &str) {
    let utf8_only = textmode::wants_utf8(&w);
    let _ = textmode::write(&mut w, text, utf8_only);
}

/// What the command line asks for.
#[derive(Default)]
struct Invocation {
    explain: bool,
    no_cache: bool,
    cache_stats: bool,
    profile: bool,
    depth: Option<u32>,
    file: String,
}

fn parse_args(args: &[String]) -> Option<Invocation> {
    let mut inv = Invocation::default();
    let mut file = None;
    for a in args {
        match a.as_str() {
            "--explain" => inv.explain = true,
            "--no-cache" => inv.no_cache = true,
            "--cache-stats" => inv.cache_stats = true,
            "--profile" => inv.profile = true,
            _ if a.starts_with("--depth=") => inv.depth = Some(a["--depth=".len()..].parse().ok()?),
            _ if a.starts_with("--") || file.is_some() => return None,
            _ => file = Some(a.clone()),
        }
    }
    inv.file = file?;
    Some(inv)
}

/// A state that holds CPC, with the adapter attached and what it builds.
fn prepare(caching: bool) -> Result<(State, Rc<RefCell<adapter::Built>>)> {
    let mut st = State::new(
        Options::default(),
        Box::new(|line| write_line(std::io::stderr().lock(), line)),
        Box::new(|line| write_line(std::io::stdout().lock(), line)),
    );
    // The state after reading CPC was made when pathos was built. Should
    // the image not fit this state, the signature is read here instead.
    if !st.load_image(CPC_IMAGE) {
        Parser::new(&mut st, CPC.to_vec(), "Cpc.eo", true, false).parse_all()?;
    }
    // The signature is built in: the proof's own includes are not read.
    st.skip_includes = true;
    let (plugin, built) = adapter::Adapter::new(&st, caching);
    st.set_plugin(Box::new(plugin))?;
    Ok((st, built))
}

fn run(inv: &Invocation) -> Result<Verdict> {
    let (mut st, built) = prepare(!inv.no_cache)?;
    if let Some(depth) = inv.depth {
        built.borrow_mut().set_depth(depth);
    }
    include_file(&mut st, &inv.file, false, false, None)?;
    if inv.profile {
        // a run of its own, before the one that gives the verdict
        let report = built.borrow_mut().profile()?;
        write_line(std::io::stderr().lock(), &report);
    }
    let verdict = built.borrow_mut().check()?;
    if inv.cache_stats {
        write_line(std::io::stderr().lock(), &built.borrow().cache_stats());
    }
    if inv.explain && verdict == Verdict::Incorrect {
        let why = built.borrow_mut().explain()?;
        write_line(std::io::stderr().lock(), &why);
    }
    Ok(verdict)
}

fn main() -> ExitCode {
    pathos_elab::on_checker_thread(check)
}

fn check() -> ExitCode {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|a| latin1::from_os(&a))
        .collect();
    if args.iter().any(|a| a == "--help") {
        write_text(std::io::stdout().lock(), USAGE);
        return ExitCode::SUCCESS;
    }
    let Some(inv) = parse_args(&args) else {
        write_text(std::io::stderr().lock(), USAGE);
        return ExitCode::FAILURE;
    };
    match run(&inv) {
        Ok(verdict) => {
            let (text, status) = match verdict {
                Verdict::Correct => ("correct", 0),
                Verdict::Incorrect => ("incorrect", 1),
                Verdict::Incomplete => ("incomplete", 2),
            };
            write_line(std::io::stdout().lock(), text);
            ExitCode::from(status)
        }
        Err(e) => {
            write_line(std::io::stderr().lock(), &e.to_string());
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_state() -> State {
        State::new(Options::default(), Box::new(|_| {}), Box::new(|_| {}))
    }

    #[test]
    fn the_built_in_image_loads_and_binds_what_the_signature_binds() {
        let mut from_image = new_state();
        assert!(from_image.load_image(CPC_IMAGE));
        let mut parsed = new_state();
        Parser::new(&mut parsed, CPC.to_vec(), "Cpc.eo", true, false)
            .parse_all()
            .unwrap();
        assert_eq!(from_image.ck.store.len(), parsed.ck.store.len());
        for name in ["or", "bvand", "extract", "forall", "$eo_test_nothing"] {
            assert_eq!(from_image.get_var(name), parsed.get_var(name), "{name}");
        }
        for rule in ["refl", "arith-elim-lt", "scope"] {
            assert_eq!(
                from_image.get_proof_rule(rule),
                parsed.get_proof_rule(rule),
                "{rule}"
            );
            assert!(parsed.get_proof_rule(rule).is_some(), "{rule}");
        }
    }

    #[test]
    fn an_image_is_refused_by_a_state_that_is_not_new() {
        let mut st = new_state();
        Parser::new(
            &mut st,
            b"(declare-const a Bool)".to_vec(),
            "t.eo",
            true,
            false,
        )
        .parse_all()
        .unwrap();
        assert!(!st.load_image(CPC_IMAGE));
        let mut damaged = CPC_IMAGE.to_vec();
        let last = damaged.len() - 1;
        damaged[last] ^= 1;
        assert!(!new_state().load_image(&damaged));
    }

    /// The verdict on a proof given as text, or the error.
    fn verdict(proof: &str) -> std::result::Result<Verdict, String> {
        let (mut st, built) = prepare(true).map_err(|e| e.to_string())?;
        Parser::new(&mut st, proof.as_bytes().to_vec(), "t.cpc", false, false)
            .parse_all()
            .map_err(|e| e.to_string())?;
        built.borrow_mut().check().map_err(|e| e.to_string())
    }

    const REFUTATION: &str = "(include \"not/there.eo\")
(declare-const p Bool)
(declare-const q Bool)
(assume @a1 (and p q))
(assume @a2 (not p))
(step @p1 p :rule and_elim :premises (@a1) :args (0))
(step @p2 false :rule contra :premises (@p1 @a2))
";

    #[test]
    fn a_refutation_is_correct() {
        assert_eq!(verdict(REFUTATION), Ok(Verdict::Correct));
    }

    /// `eo::is_q` of a term that does not evaluate is false, not stuck:
    /// the rule's program asks it of every atom of a polynomial.
    #[test]
    fn arith_poly_norm_takes_variables() {
        let proof = "(declare-const x Real)
(declare-const y Real)
(assume @a (not (= (+ x y) (+ y x))))
(step @p1 (= (+ x y) (+ y x)) :rule arith_poly_norm :args ((= (+ x y) (+ y x))))
(step @p2 false :rule contra :premises (@p1 @a))
";
        assert_eq!(verdict(proof), Ok(Verdict::Correct));
    }

    #[test]
    fn a_step_must_prove_what_it_states() {
        // and_elim with index 0 gives p, not q
        let wrong = REFUTATION.replace("(step @p1 p ", "(step @p1 q ");
        assert_eq!(verdict(&wrong), Ok(Verdict::Incorrect));
    }

    #[test]
    fn premises_are_found_by_what_they_prove() {
        let swapped = REFUTATION.replace(":premises (@p1 @a2)", ":premises (@a2 @p1)");
        assert_eq!(verdict(&swapped), Ok(Verdict::Incorrect));
        let unknown = REFUTATION.replace(":premises (@p1 @a2)", ":premises (@p1 @a3)");
        assert!(verdict(&unknown).unwrap_err().contains("@a3"));
    }

    #[test]
    fn a_proof_must_end_with_false() {
        let open = REFUTATION.replace("(step @p2 false :rule contra :premises (@p1 @a2))\n", "");
        assert_eq!(verdict(&open), Ok(Verdict::Incorrect));
        assert_eq!(
            verdict("(declare-const p Bool)\n(assume @a p)\n"),
            Ok(Verdict::Incorrect)
        );
    }

    #[test]
    fn a_step_without_a_stated_conclusion_is_checked_too() {
        let unstated = REFUTATION
            .replace("(step @p1 p ", "(step @p1 ")
            .replace("(step @p2 false ", "(step @p2 ");
        assert_eq!(verdict(&unstated), Ok(Verdict::Correct));
        // without the conclusion to compare with, a step of the wrong rule
        // still does not prove false
        let wrong = unstated.replace(
            ":rule contra :premises (@p1 @a2)",
            ":rule and_intro :premises (@p1 @a2)",
        );
        assert_ne!(verdict(&wrong), Ok(Verdict::Correct));
    }

    #[test]
    fn step_pop_discharges_its_assumption() {
        let proof = "(declare-const p Bool)
(assume @a (not (=> p p)))
(assume-push @h p)
(step-pop @p1 (=> p p) :rule scope :premises (@h))
(step @p2 false :rule contra :premises (@p1 @a))
";
        assert_eq!(verdict(proof), Ok(Verdict::Correct));
        // what was proved inside the scope is gone after it
        let leaked = proof.replace(":premises (@p1 @a)", ":premises (@h @a)");
        assert!(verdict(&leaked).is_err());
    }

    #[test]
    fn an_assumption_after_a_step_is_refused() {
        let proof = "(declare-const p Bool)
(assume @a p)
(step @p1 (= p p) :rule refl :args (p))
(assume @b (not p))
(step @p2 false :rule contra :premises (@a @b))
";
        assert!(
            verdict(proof)
                .unwrap_err()
                .contains("an assume after the first proof step")
        );
    }

    #[test]
    fn what_the_checker_has_no_form_for_is_an_error() {
        let lambda = "(declare-const f (-> Int Int))
(assume @a (not (= f (lambda ((x Int)) x))))
";
        assert!(verdict(lambda).unwrap_err().contains("lambda"));
        let rule = "(declare-const p Bool)\n(assume @a p)\n(step @p1 p :rule trust)\n";
        assert!(verdict(rule).is_err());
    }

    #[test]
    fn datatypes_are_declared_to_the_checker() {
        let proof = "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-datatypes ((P 2)) ((par (A B) ((pair (fst A) (snd B))))))
(declare-const l L)
(declare-const x (P Int L))
(assume @a (not (= (cons (fst x) l) (cons (fst x) l))))
(step @p1 (= (cons (fst x) l) (cons (fst x) l)) :rule refl :args ((cons (fst x) l)))
(step @p2 false :rule contra :premises (@p1 @a))
";
        assert_eq!(verdict(proof), Ok(Verdict::Correct));
    }

    /// A step's arguments are not typed, so a type annotation with too few
    /// parts reaches the adapter: an error, not an index out of range.
    #[test]
    fn a_malformed_annotation_in_a_step_is_an_error() {
        for args in ["(as)", "(as is)"] {
            let proof = format!(
                "(assume @p1 false)\n(step @p2 (= false false) :rule refl :args ({args}))\n"
            );
            let e = verdict(&proof).expect_err(args);
            assert!(e.contains("pathos does not read this proof"), "{args}: {e}");
        }
    }

    /// A constructor, selector, tester or updater of one parametric
    /// datatype used at an instance of another: the types do not rule it
    /// out for `is` and `update`, nor for a step's untyped arguments. Each
    /// is an error that names the symbol, whichever datatype has more
    /// constructors or selectors.
    #[test]
    fn a_member_at_an_instance_of_another_datatype_is_an_error() {
        let block = |list: &str| {
            format!(
                "(declare-datatypes ((List 1) (Box 1)) ((par (X) ({list})) \
                 (par (Y) ((box (unbox Y))))))\n(declare-const b (Box Int))\n"
            )
        };
        let nil_first = block("(nil) (cons (head X) (tail (List X)))");
        let cons_first = block("(cons (head X) (tail (List X))) (nil)");
        let step = |arg: &str| {
            format!("(assume @p1 false)\n(step @p2 (= false false) :rule refl :args ({arg}))\n")
        };
        let cases = [
            (&cons_first, step("(as nil (Box Int))"), "nil"),
            // the same where `nil` is the first constructor, as `box` is
            (&nil_first, step("(as nil (Box Int))"), "nil"),
            (&nil_first, step("(head b)"), "head"),
            (&cons_first, step("(tail b)"), "tail"),
            (&cons_first, step("(head b)"), "head"),
            (
                &nil_first,
                "(assume @p1 ((_ is cons) b))\n".to_string(),
                "cons",
            ),
            (
                &cons_first,
                "(assume @p1 ((_ is cons) b))\n".to_string(),
                "cons",
            ),
            (
                &nil_first,
                "(assume @p1 (= b ((_ update tail) b b)))\n".to_string(),
                "tail",
            ),
        ];
        for (block, rest, name) in cases {
            let proof = format!("{block}{rest}");
            let e = verdict(&proof).expect_err(&proof);
            assert!(
                e.contains(&format!(
                    "{name} is used at the type (Box Int), which is not an instance of its \
                     datatype"
                )),
                "{proof}: {e}"
            );
        }
        // the members of the datatype itself are still found
        let own = format!(
            "{nil_first}(declare-const l (List Int))\n\
             (assume @a (not (= (tail l) (tail l))))\n\
             (step @p1 (= (tail l) (tail l)) :rule refl :args ((tail l)))\n\
             (step @p2 false :rule contra :premises (@p1 @a))\n"
        );
        assert_eq!(verdict(&own), Ok(Verdict::Correct));
    }

    /// The compiler writes the hyphens of a rule's name as underscores. No
    /// two rules of CPC may then have the same constructor, or a step of
    /// one would be checked as a step of the other.
    #[test]
    fn every_rule_of_cpc_has_a_constructor_of_its_own() {
        let text = String::from_utf8_lossy(CPC);
        let mut seen = std::collections::HashMap::new();
        let mut rules = 0;
        for line in text.lines() {
            let Some(rest) = line
                .strip_prefix("(declare-rule ")
                .or_else(|| line.strip_prefix("(declare-ordered-rule "))
            else {
                continue;
            };
            let name = rest.split([' ', '(']).next().unwrap();
            let cname = format!("$emb_r.{}", name.replace('-', "_"));
            // logos leaves some rules out (those about lambda, for one)
            if pathos_compiled_checker::Constructor::from_name(&cname).is_none() {
                continue;
            }
            if let Some(other) = seen.insert(cname, name.to_string()) {
                panic!("the rules {other} and {name} share a constructor");
            }
            rules += 1;
        }
        assert!(rules > 500, "{rules} rules found");
    }
}
