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

use std::io::{IsTerminal, Write};
use std::process::ExitCode;

use pathos_check::Options;
use pathos_compiled_checker::Verdict;
use pathos_elab::{Parser, State, include_file};
use pathos_syntax::{Result, latin1, textmode};

/// CPC as logos has it: the signature the checker was compiled from, and
/// the one the front end reads the proof against.
const CPC: &[u8] = include_bytes!("../../../generated/cpc-checker/Cpc.cached.eo");

const USAGE: &str = "usage: pathos [options] <proof.cpc>

Checks a CPC proof, as cvc5 writes it with --dump-proofs, and prints
correct, incorrect or incomplete (exit status 0, 1 or 2).

  --explain      for an incorrect proof, also say on standard error which
                 command the checker does not accept
  --no-cache     run the checker without its caches of types and of
                 program results
  --cache-stats  print the caches' hits, misses and sizes on standard error
";

fn write_line(mut w: impl Write + IsTerminal, line: &str) {
    let utf8_only = textmode::wants_utf8(&w);
    // Nothing useful can be done if stdout or stderr is closed.
    let _ = textmode::write(&mut w, &format!("{line}\n"), utf8_only);
}

/// What the command line asks for.
#[derive(Default)]
struct Invocation {
    explain: bool,
    no_cache: bool,
    cache_stats: bool,
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
            _ if a.starts_with("--") || file.is_some() => return None,
            _ => file = Some(a.clone()),
        }
    }
    inv.file = file?;
    Some(inv)
}

fn run(inv: &Invocation) -> Result<Verdict> {
    let mut st = State::new(
        Options::default(),
        Box::new(|line| write_line(std::io::stderr().lock(), line)),
        Box::new(|line| write_line(std::io::stdout().lock(), line)),
    );
    Parser::new(&mut st, CPC.to_vec(), "Cpc.eo", true, false).parse_all()?;
    // The signature is built in: the proof's own includes are not read.
    st.skip_includes = true;
    let (plugin, built) = adapter::Adapter::new(&st, !inv.no_cache);
    st.set_plugin(Box::new(plugin))?;
    include_file(&mut st, &inv.file, false, false, None)?;
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
        print!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let Some(inv) = parse_args(&args) else {
        eprint!("{USAGE}");
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
