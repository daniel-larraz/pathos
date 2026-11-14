//! End-to-end checks of small inputs. The expected messages and warnings are
//! what the reference Ethos binary prints for the same input in a file named
//! `t.eo` (see docs/brief.md, "The reference"), without the final newline
//! that the binary adds.

use std::cell::RefCell;
use std::rc::Rc;

use pathos_check::Options;
use pathos_elab::{Parser, State};

struct Run {
    /// `Ok(true)` if a rule marked `:sorry` was used, or the error text.
    result: Result<bool, String>,
    warnings: Vec<String>,
    stdout: Vec<String>,
}

fn run_as(input: &str, is_signature: bool, is_reference: bool) -> Run {
    let warnings = Rc::new(RefCell::new(Vec::new()));
    let stdout = Rc::new(RefCell::new(Vec::new()));
    let (w, o) = (warnings.clone(), stdout.clone());
    let mut st = State::new(
        Options::default(),
        Box::new(move |l| w.borrow_mut().push(l.to_string())),
        Box::new(move |l| o.borrow_mut().push(l.to_string())),
    );
    let parsed = Parser::new(
        &mut st,
        input.as_bytes().to_vec(),
        "t.eo",
        is_signature,
        is_reference,
    )
    .parse_all();
    let result = match parsed {
        Ok(()) => Ok(st.ck.used_sorry_rule()),
        Err(e) => Err(e.to_string()),
    };
    Run {
        result,
        warnings: warnings.take(),
        stdout: stdout.take(),
    }
}

/// Runs the input as a signature (a `.eo` file).
fn run(input: &str) -> Run {
    run_as(input, true, false)
}

const EQ: &str = "(declare-const Int Type)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const a Int)
(declare-const b Int)
";

#[test]
fn accepts_a_small_proof() {
    let r = run(&format!(
        "{EQ}(declare-rule symm ((T Type) (x T) (y T)) :premises ((= x y)) :conclusion (= y x))
(assume p1 (= a b))
(step s1 (= b a) :rule symm :premises (p1))"
    ));
    assert_eq!(r.result, Ok(false));
    assert!(r.warnings.is_empty() && r.stdout.is_empty());
}

#[test]
fn rejects_a_wrong_conclusion() {
    let r = run(&format!(
        "{EQ}(declare-rule symm ((T Type) (x T) (y T)) :premises ((= x y)) :conclusion (= y x))
(assume p1 (= a b))
(step s1 (= b b) :rule symm :premises (p1))"
    ));
    assert_eq!(
        r.result.unwrap_err(),
        "Error: t.eo:7.43: Unexpected conclusion for rule symm:\n    Proves: (_ (= b) a)\n  \
         Expected: (_ (= b) b)\n"
    );
}

#[test]
fn explains_a_step_that_does_not_apply() {
    let r = run(&format!(
        "{EQ}(declare-rule refl ((T Type) (x T)) :args (x x) :conclusion (= x x))
(step s1 :rule refl :args (a b))"
    ));
    assert_eq!(
        r.result.unwrap_err(),
        "Error: t.eo:6.31: A step of rule refl failed to check.\nExpected args: [x, x]\n\
         Provided args: [a, b]\n\n"
    );
}

#[test]
fn reports_type_errors() {
    let r = run("(declare-const Int Type)\n(declare-const a Int)\n(define x () (a a) :type Int)");
    assert_eq!(
        r.result.unwrap_err(),
        "Error: t.eo:3.26: Type checking failed:\nExpression: (a a)\nMessage: Non-function a \
         as head of APPLY\nIts type is Int\n\n"
    );
}

#[test]
fn sorry_rules_make_the_proof_incomplete() {
    let rule = "(declare-rule trust ((F Bool)) :args (F) :conclusion F :sorry)\n";
    assert_eq!(run(rule).result, Ok(false));
    let r = run(&format!("{rule}(step p0 false :rule trust :args (false))"));
    assert_eq!(r.result, Ok(true));
}

#[test]
fn evaluates_programs_and_operators() {
    let r = run("(declare-const Int Type)
(declare-consts <numeral> Int)
(program fact ((n Int))
  :signature (Int) Int
  (((fact 0) 1)
   ((fact n) (eo::mul n (fact (eo::add n -1))))))
(define f5 () (fact 5) :is_eq 120)
(define q () (eo::zdiv -7 2) :is_eq -4)
(define bad () (fact 1 2))");
    assert_eq!(r.result, Ok(false));
    assert_eq!(
        r.warnings,
        ["Wrong number of arguments when applying program fact, 2 arguments expected, got 3"]
    );
}

#[test]
fn desugars_by_attribute() {
    let r = run(
        "(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const a Bool)
(declare-const b Bool)
(define l () (or a b a))
(define t1 () (eo::list_len or l) :is_eq 3)
(define t2 () (eo::list_setof or l) :is_eq (or a b))
(define t3 () (eo::list_rev or l) :is_eq (or b a))",
    );
    assert_eq!(
        r.result.unwrap_err(),
        "Error: t.eo:7.49: Terms are not equal:\nExpression: (eo::define ((_v0 (_ or a))) (_ _v0 \
         (_ (_ or b) (_ _v0 false))))\nTarget expression: (_ (_ or b) (_ (_ or a) false))\n\n"
    );
}

#[test]
fn warns_and_goes_on() {
    let r = run("(declare-const Int Type)
(program foo ((x Int :list :list))
  :signature (Int) Int
  (((foo x) x)))
(echo \"hi\")");
    assert_eq!(r.result, Ok(false));
    assert_eq!(
        r.warnings,
        ["Cannot set the constructor kind for a term more than once (list and list)"]
    );
    assert_eq!(r.stdout, ["hi"]);
}

#[test]
fn reference_files_read_smt_lib() {
    // `Type` is not a token outside signatures
    let r = run_as("(declare-const Int Type)", false, true);
    assert_eq!(
        r.result.unwrap_err(),
        "Error: t.eo:1.20: Could not find symbol Type\n"
    );
    let r = run_as(
        "(set-logic ALL)\n(declare-fun p () Bool)\n(assert p)\n(get-model)",
        false,
        true,
    );
    assert_eq!(r.result, Ok(false));
}

#[test]
fn deep_terms_do_not_overflow_the_stack() {
    // 200,000 nested applications: parsed, typed and printed iteratively.
    let depth = 200_000;
    let mut input = String::from(
        "(declare-const Int Type)\n(declare-const f (-> Int Int))\n(declare-const a Int)\n\
         (define x () ",
    );
    for _ in 0..depth {
        input.push_str("(f ");
    }
    input.push('a');
    for _ in 0..depth {
        input.push(')');
    }
    input.push_str(" :type Bool)");
    let err = run(&input).result.unwrap_err();
    assert!(err.starts_with("Error: t.eo:4."), "{}", &err[..60]);
    assert!(err.contains("Expression of unexpected type:"));
    assert!(err.ends_with("      Type: Int\n  Expected: Bool\n\n"));
}

// The tests below come from the first fuzzing run (docs/reviews/fuzz-1.md).

#[test]
fn eo_var_with_one_argument_is_a_type_error() {
    let r = run("(declare-const Int Type)
(define y () (eo::var Int) :type Int)");
    assert_eq!(
        r.result,
        Err("Error: t.eo:2.34: Type checking failed:
Expression: (eo::var Int)
Message: No type rule declared for literal kind STRING; use declare-consts to declare its \
             type before use

"
        .to_string())
    );
}

/// Ethos reads the missing argument from past the end of a vector, and here
/// crashes. Without the error, the program below would recurse for ever,
/// since the condition of its `eo::ite` never becomes a value.
#[test]
fn evaluating_an_operator_without_an_argument_it_reads_ends_the_run() {
    let r = run("(declare-const Int Type)
(declare-consts <numeral> Int)
(program f ((x Int)) :signature (Int) Int (((f x) (eo::ite (eo::is_eq x) 1 (f x)))))
(define y () (f 4))");
    assert_eq!(
        r.result,
        Err(
            "Error: t.eo:4.19: Too few arguments when evaluating literal op EVAL_IS_EQ, 1 \
             arguments [4]\n"
                .to_string()
        )
    );
    assert_eq!(
        r.warnings,
        ["Wrong number of arguments when applying literal op EVAL_IS_EQ, 1 arguments"]
    );
}

/// The list is looked at before the missing third argument, so a term that
/// is not a list makes the operator stuck, with Ethos's warnings.
#[test]
fn a_missing_argument_matters_only_once_it_is_read() {
    let r = run(
        "(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const a Bool)
(declare-const and (-> Bool Bool Bool))
(program f ((x Bool)) :signature (Bool) Bool (((f x) (eo::list_find or x))))
(declare-rule r ((x Bool)) :args (x) :conclusion (f x))
(step p :rule r :args ((and a a)))",
    );
    assert_eq!(
        r.result,
        Err("Error: t.eo:6.33: A step of rule r failed to check.
Evaluation failed: (eo::list_find or (_ (and a) a))

"
        .to_string())
    );
    assert_eq!(
        r.warnings,
        [
            "Wrong number of arguments when applying literal op EVAL_LIST_FIND, 2 arguments",
            "...expected associative application to end in false, got (_ (and a) a)",
            "...expected associative application to end in false, got (_ (and a) a)",
        ]
    );
}

#[test]
fn a_token_is_shown_up_to_its_first_nul_character() {
    let r = run("(declare-const a Bool)\n(define b () \"ab\0cd)\n");
    assert_eq!(
        r.result,
        Err("Error: t.eo:2.14: Expected SMT-LIBv2 term, got `\"ab` \
             (UNTERMINATED_STRING_LITERAL).\n\n"
            .to_string())
    );
}

/// The operator's type has one argument where two are expected. Ethos finds
/// the element type in it all the same.
#[test]
fn the_nil_terminator_is_found_through_a_malformed_operator_type() {
    let r = run("(declare-parameterized-const L ((T Type)) Type)
(declare-parameterized-const L.nil ((T Type)) (L T))
(declare-parameterized-const L.cons ((T Type :implicit)) (-> T (L T)) :right-assoc-nil (L.nil T))
(declare-const b Bool)
(declare-const c Bool)
(define t () (eo::list_concat L.cons) :is_eq (L.cons b c))");
    assert_eq!(
        r.result,
        Err("Error: t.eo:6.57: Terms are not equal:
Expression: (eo::list_concat L.cons)
Target expression: (_ (_ L.cons b) (_ (_ L.cons c) (L.nil Bool)))

"
        .to_string())
    );
}

#[test]
fn a_chain_without_a_constructor_term_holds_the_null_expression() {
    let decl = "(declare-parameterized-const = ((T Type)) (-> Bool Bool Bool) :chainable T)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)
";
    let r = run(&format!("{decl}(assume a1 (= d))"));
    assert_eq!(
        r.result,
        Err("Error: t.eo:5.16: Type checking failed:
Expression: ([NONE])
Message: Unknown kind NONE

"
        .to_string())
    );
    assert_eq!(
        r.warnings,
        ["Unknown category for parameterized operator ="]
    );
    let r = run(&format!("{decl}(assume a1 (= d e f))"));
    assert_eq!(
        r.result,
        Err("Error: t.eo:5.20: Type checking failed:
Expression: (_ ([NONE] (_ (_ = d) e)) (_ (_ = e) f))
Message: Checking application of =
Unexpected type of child #1
  Term: e
  Has type: Bool
  Expected type: Type
  Context []


"
        .to_string())
    );
}

/// `(s c b)` has too few arguments and is met three times in one
/// evaluation. Ethos remembers that it failed, so it warns once.
#[test]
fn a_failed_program_application_is_tried_once_per_evaluation() {
    let r = run(
        "(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program s ((x Bool) (y Bool) (l Bool :list) (z Bool)) :signature (Bool Bool Bool) Bool
  (((s x y (or z l)) (_ or (s x y) (s x y l)))))
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const t (eo::requires (s c b (or a b c)) true Bool))",
    );
    assert_eq!(
        r.warnings,
        [
            "*** Bad number of arguments provided in function call to (s x y (_ (_ or z) l))",
            "  Arguments: [s c b]",
        ]
    );
    assert!(r.result.is_err());
}

/// The statistics for the input under the given `--stats` options, with
/// the numbers that are pathos's own (times, term-store counters) masked
/// and the rows in name order, as the harness compares them.
fn stats(input: &str, options: &[&str]) -> Vec<String> {
    let mut opts = Options::default();
    for o in options {
        assert!(opts.set_option(o, true));
    }
    let mut st = State::new(opts, Box::new(|_| ()), Box::new(|_| ()));
    Parser::new(&mut st, input.as_bytes().to_vec(), "t.eo", true, false)
        .parse_all()
        .unwrap();
    let text = st.ck.stats_string();
    let mut lines: Vec<String> = Vec::new();
    for line in text.lines() {
        let masked = match line.split_once(" = ") {
            Some((name, value)) if !value.starts_with('{') => {
                let unit = if value.ends_with("us") { "us" } else { "" };
                format!("{name} = N{unit}")
            }
            Some((name @ ("checkTime" | "mkExpr"), _)) => format!("{name} = {{}}"),
            _ => match line.split_once(": ") {
                // a rule's row: keep the name and the count
                Some((name, rest)) if rest.contains('%') => {
                    let count = rest.split(' ').next().unwrap();
                    format!("{name}: {count} ...")
                }
                _ => line.to_string(),
            },
        };
        lines.push(masked);
    }
    // The rules come in the order of the time they took: put them in name
    // order instead.
    if let Some(first) = lines
        .iter()
        .position(|l| l.ends_with(" ...") && l.contains(": "))
    {
        let n = lines[first..]
            .iter()
            .take_while(|l| l.ends_with(" ..."))
            .count();
        lines[first..first + n]
            .sort_by(|a, b| a.trim_start_matches(' ').cmp(b.trim_start_matches(' ')));
    }
    for line in &mut lines {
        if let Some(items) = line.strip_prefix("ruleCount = { ") {
            let mut items: Vec<&str> = items.trim_end_matches(" }").split(", ").collect();
            items.sort();
            *line = format!("ruleCount = {{ {} }}", items.join(", "));
        }
    }
    lines
}

const STATS_INPUT: &str = "(declare-const Int Type)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const a Int)
(declare-const b Int)
(program $flip ((T Type) (x T) (y T)) :signature (Bool) Bool
  ((($flip (= x y)) (= y x))))
(declare-rule symm ((F Bool)) :premises (F) :conclusion ($flip F))
(declare-rule |odd name| ((F Bool)) :args (F) :conclusion ($flip F))
(assume p (= a b))
(step q (= b a) :rule symm :premises (p))
(step r (= a b) :rule symm :premises (q))
(step t (= b a) :rule |odd name| :args ((= a b)))
";

#[test]
fn stats_list_the_rules_used() {
    let rule = "=".repeat(84);
    assert_eq!(
        stats(STATS_INPUT, &["stats"]),
        [
            rule.as_str(),
            "mkExprCount = N",
            "newExprCount = N",
            "deleteExprCount = N",
            "symCount = N",
            "litCount = N",
            "time = Nus",
            rule.as_str(),
            "                                  Rule  #      t(us)            t/#(us)   #mkExpr   ",
            rule.as_str(),
            "                                  symm: 2 ...",
            "                            |odd name|: 1 ...",
        ]
    );
}

#[test]
fn stats_all_lists_the_programs_with_the_generated_ones() {
    let rule = "=".repeat(84);
    let lines = stats(STATS_INPUT, &["stats-all"]);
    assert_eq!(
        lines[12..],
        [
            rule.as_str(),
            "                               Program  #      ",
            rule.as_str(),
            "                                 $flip: 3",
            "                         $eo_prog_symm: 2",
            "                   |$eo_prog_odd name|: 1",
        ]
    );
}

#[test]
fn stats_compact_prints_one_line_per_table() {
    let lines = stats(STATS_INPUT, &["stats-all", "stats-compact"]);
    assert_eq!(
        lines[6..],
        [
            "ruleCount = { symm: 2, |odd name|: 1 }",
            "checkTime = {}",
            "mkExpr = {}",
            "progCount = { $flip: 3, $eo_prog_symm: 2, |$eo_prog_odd name|: 1 }",
        ]
    );
    // without steps there is no rule table
    let lines = stats("(declare-const Int Type)\n", &["stats-compact"]);
    assert_eq!(lines.len(), 6);
}
