//! The statistics of `--stats`, `--stats-all` and `--stats-compact`
//! (`stats.cpp` in Ethos).
//!
//! The layout, the rules and programs listed and their counts are Ethos's.
//! The times and the term-store counters are pathos's own: its store never
//! deletes a term, so `deleteExprCount` is always 0.

use std::collections::HashMap;
use std::fmt::Write;
use std::time::Instant;

use pathos_term::Term;

use crate::Checker;

const RULE: &str =
    "====================================================================================";

/// What the steps of one proof rule cost.
#[derive(Default)]
struct RuleStat {
    count: u64,
    mk_expr_count: u64,
    time_us: u128,
}

pub(crate) struct Stats {
    start: Instant,
    /// Every rule a step has named. This is kept without `--stats` too: it
    /// decides whether the verdict is "incomplete".
    rules: HashMap<Term, RuleStat>,
    /// How often each program was applied; kept only with `--stats`.
    programs: HashMap<Term, u64>,
    /// When the step being checked began, and the store's count then.
    step_start: Option<(Instant, u64)>,
}

impl Stats {
    pub(crate) fn new() -> Stats {
        Stats {
            start: Instant::now(),
            rules: HashMap::new(),
            programs: HashMap::new(),
            step_start: None,
        }
    }
}

/// `s` in a field of `width`, as `std::left << std::setw(width)`.
fn left(out: &mut String, s: &str, width: usize) {
    let _ = write!(out, "{s:<width$}");
}

impl Checker {
    /// Records that a step names the rule. The rule counts as used from
    /// here on, whether or not the step checks.
    pub fn step_begins(&mut self, rule: Term) {
        self.stats.rules.entry(rule).or_default();
        if self.opts.stats {
            self.stats.step_start = Some((Instant::now(), self.store.mk_count()));
        }
    }

    /// Records that the step naming the rule checked.
    pub fn step_ends(&mut self, rule: Term) {
        let mk_count = self.store.mk_count();
        let stat = self.stats.rules.entry(rule).or_default();
        stat.count += 1;
        if let Some((start, start_mk)) = self.stats.step_start.take() {
            stat.mk_expr_count += mk_count - start_mk;
            stat.time_us += start.elapsed().as_micros();
        }
    }

    /// Records an application of the program `hd`.
    #[inline]
    pub(crate) fn count_program(&mut self, hd: Term) {
        if self.opts.stats {
            *self.stats.programs.entry(hd).or_default() += 1;
        }
    }

    /// Whether any rule named by a step is marked `:sorry`.
    pub fn used_sorry_rule(&self) -> bool {
        self.stats
            .rules
            .keys()
            .any(|&r| self.is_proof_rule_sorry(r))
    }

    /// The statistics, as Ethos prints them after the verdict.
    pub fn stats_string(&self) -> String {
        let compact = self.opts.stats_compact;
        let mut out = String::new();
        if !compact {
            let _ = writeln!(out, "{RULE}");
        }
        let total = self.stats.start.elapsed().as_micros();
        let _ = writeln!(out, "mkExprCount = {}", self.store.mk_count());
        let _ = writeln!(out, "newExprCount = {}", self.store.len());
        let _ = writeln!(out, "deleteExprCount = 0");
        let _ = writeln!(out, "symCount = {}", self.store.symbol_count());
        let _ = writeln!(out, "litCount = {}", self.store.lit_count());
        let _ = writeln!(out, "time = {total}us");

        let program_stats: HashMap<Term, RuleStat>;
        let mut tables = vec![(true, &self.stats.rules)];
        if self.opts.stats_all {
            program_stats = (self.stats.programs.iter())
                .map(|(&p, &count)| {
                    let stat = RuleStat {
                        count,
                        ..RuleStat::default()
                    };
                    (p, stat)
                })
                .collect();
            tables.push((false, &program_stats));
        }
        for (is_rules, table) in tables {
            if table.is_empty() {
                continue;
            }
            if !compact {
                let _ = writeln!(out, "{RULE}");
                let title = if is_rules { "Rule  " } else { "Program  " };
                let _ = write!(out, "{title:>40}");
                left(&mut out, "#", 7);
                if is_rules {
                    left(&mut out, "t(us)", 17);
                    left(&mut out, "t/#(us)", 10);
                    left(&mut out, "#mkExpr", 10);
                }
                let _ = writeln!(out, "\n{RULE}");
            }
            // Programs made for `eo::match` and the like are left out.
            let mut rows: Vec<(Term, &RuleStat)> = (table.iter())
                .filter(|&(&t, _)| {
                    !(self.store.symbol_name(t)).is_some_and(|n| n.starts_with("eo::"))
                })
                .map(|(&t, stat)| (t, stat))
                .collect();
            // By time, then by count, the largest first. Ethos leaves the
            // order of equal rows to the addresses of its terms; here they
            // are in the order the symbols were made.
            rows.sort_by(|(t1, s1), (t2, s2)| {
                (s2.time_us.cmp(&s1.time_us))
                    .then(s2.count.cmp(&s1.count))
                    .then(t1.id().cmp(&t2.id()))
            });
            let (mut counts, mut times, mut mk_exprs) = (Vec::new(), Vec::new(), Vec::new());
            for (t, stat) in rows {
                let name = self.show(t);
                if compact {
                    counts.push(format!("{name}: {}", stat.count));
                    times.push(format!("{name}: {}", stat.time_us));
                    mk_exprs.push(format!("{name}: {}", stat.mk_expr_count));
                    continue;
                }
                let _ = write!(out, "{:>40}", format!("{name}: "));
                if !is_rules {
                    let _ = writeln!(out, "{}", stat.count);
                    continue;
                }
                left(&mut out, &stat.count.to_string(), 7);
                let pct = (100 * stat.time_us) as f64 / total as f64;
                left(&mut out, &format!("{} ({pct:.1}%)", stat.time_us), 17);
                let per_step = stat.time_us as f64 / stat.count as f64;
                left(&mut out, &format!("{per_step:.0}"), 10);
                left(&mut out, &stat.mk_expr_count.to_string(), 10);
                out.push('\n');
            }
            if compact {
                let what = if is_rules { "rule" } else { "prog" };
                let _ = writeln!(out, "{what}Count = {{ {} }}", counts.join(", "));
                if is_rules {
                    let _ = writeln!(out, "checkTime = {{ {} }}", times.join(", "));
                    let _ = writeln!(out, "mkExpr = {{ {} }}", mk_exprs.join(", "));
                }
            }
        }
        out
    }
}
