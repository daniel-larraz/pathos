//! The pathos command-line checker (`main.cpp` in Ethos).

use std::cell::RefCell;
use std::ffi::OsString;
use std::io::{IsTerminal, Read, Write};
use std::os::unix::ffi::OsStringExt;
use std::process::ExitCode;
use std::rc::Rc;

use pathos_check::Options;
use pathos_elab::{Parser, State, include_file};
use pathos_syntax::{Error, Result, latin1};

const HELP: &str = "        --include=X: includes the file specified by X.
             --help: displays this message.
    --normalize-num: treat numeral literals as syntax sugar for rational literals.
 --no-normalize-dec: do not treat decimal literals as syntax sugar for rational literals.
 --no-normalize-hex: do not treat hexadecimal literals as syntax sugar for binary literals.
     --no-parse-let: do not treat let as a builtin symbol for specifying terms having shared subterms.
     --no-print-dag: do not dagify the output of terms in error messages and trace messages.
--no-rule-sym-table: do not use a separate symbol table for proof rules and declared terms.
      --reference=X: includes the file specified by X as a reference file.
--reference-define-fun: in reference files, treat define-fun and define-const as definitions instead of reference assertions.
--require-proof-of-false: require the last proof step at level zero to prove false.
      --show-config: displays the build information for this binary.
            --stats: enables detailed statistics.
        --stats-all: enables all available statistics.
    --stats-compact: print statistics in a compact format.
           -t <tag>: enables the given trace tag (requires debug build).
                 -v: verbose mode, enable all standard trace messages (requires debug build).
";

/// The options for signature snapshots. Ethos has no such options, so
/// `--help`, which prints Ethos's text, does not list them. The names are a
/// proposal; they are only here.
const WRITE_SNAPSHOT: &str = "--write-snapshot=";
const SNAPSHOT: &str = "--snapshot=";

/// What the command line asks for.
struct Invocation {
    opts: Options,
    /// The files to include first, and whether each is a reference.
    includes: Vec<(String, bool)>,
    file: Option<String>,
    /// Where to write a snapshot of the signature `file`.
    write_snapshot: Option<String>,
    /// A snapshot to use in place of parsing its signature.
    snapshot: Option<String>,
}

enum Parsed {
    Run(Invocation),
    /// Print the text and stop.
    Print(String),
}

fn parse_args(args: &[String]) -> Result<Parsed> {
    let mut opts = Options::default();
    let mut includes = Vec::new();
    let mut file: Option<String> = None;
    let (mut write_snapshot, mut snapshot) = (None, None);
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        i += 1;
        if let Some(key) = arg.strip_prefix("--no-") {
            if opts.set_option(key, false) {
                continue;
            }
        } else if let Some(key) = arg.strip_prefix("--")
            && opts.set_option(key, true)
        {
            continue;
        }
        // included once the options are final
        if let Some(f) = arg.strip_prefix("--include=") {
            includes.push((f.to_string(), false));
            continue;
        }
        if let Some(f) = arg.strip_prefix("--reference=") {
            includes.push((f.to_string(), true));
            continue;
        }
        if let Some(f) = arg.strip_prefix(WRITE_SNAPSHOT) {
            write_snapshot = Some(f.to_string());
            continue;
        }
        if let Some(f) = arg.strip_prefix(SNAPSHOT) {
            snapshot = Some(f.to_string());
            continue;
        }
        if arg == "--help" {
            return Ok(Parsed::Print(HELP.to_string()));
        } else if arg == "--show-config" {
            let name = env!("CARGO_PKG_NAME");
            let version = env!("CARGO_PKG_VERSION");
            return Ok(Parsed::Print(format!(
                "This is {name} version {version}.\n\n     tracing : no\n"
            )));
        } else if arg == "-t" {
            if i >= args.len() {
                return Err(Error::plain("Missing trace tag."));
            }
            return Err(Error::plain("tracing not enabled in this build\n"));
        } else if arg == "-v" {
            return Err(Error::plain("tracing not enabled in this build"));
        } else if let Some(first) = &file {
            // maybe one of the two is a misspelt option
            for a in [first, arg] {
                if a.starts_with("--") {
                    return Err(Error::plain(format!("unrecognized option {a}")));
                }
            }
            return Err(Error::plain(format!(
                "mulitple files specified, \"{first}\" and \"{arg}\""
            )));
        } else {
            file = Some(arg.clone());
        }
    }
    Ok(Parsed::Run(Invocation {
        opts,
        includes,
        file,
        write_snapshot,
        snapshot,
    }))
}

/// Writes a line of text held as described in `pathos_syntax::latin1`.
fn write_line(mut w: impl Write, line: &str) {
    let mut bytes = latin1::encode(line);
    bytes.push(b'\n');
    // Nothing useful can be done if stdout or stderr is closed.
    let _ = w.write_all(&bytes);
}

/// Reads the inputs and returns what to print: the verdict and, if asked
/// for, the statistics.
fn run(inv: Invocation) -> Result<String> {
    if let Some(target) = &inv.write_snapshot {
        return write_snapshot(&inv, target);
    }
    let mut st = State::new(
        inv.opts,
        Box::new(|line| write_line(std::io::stderr().lock(), line)),
        Box::new(|line| write_line(std::io::stdout().lock(), line)),
    );
    // A snapshot that cannot be read, like one that cannot be used, is
    // ignored: the run goes on as if the option were not there.
    if let Some(bytes) = inv.snapshot.as_deref().and_then(read_bytes) {
        st.offer_snapshot(bytes);
    }
    for (file, is_reference) in &inv.includes {
        include_file(&mut st, file, !is_reference, *is_reference, None)?;
    }
    match &inv.file {
        Some(file) => {
            // files named *.eo are signatures
            let is_signature = file.ends_with(".eo");
            include_file(&mut st, file, is_signature, false, None)?;
        }
        None => {
            // a proof on stdin
            if std::io::stdin().is_terminal() {
                return Err(Error::plain("no input specified."));
            }
            let mut input = Vec::new();
            if std::io::stdin().lock().read_to_end(&mut input).is_err() {
                return Err(Error::fatal("Couldn't read the input"));
            }
            Parser::new(&mut st, input, "stream", false, false).parse_all()?;
        }
    }
    if st.ck.opts.require_proof_of_false && !st.last_step_proves_false_at_level_zero() {
        return Err(Error::plain(
            "the last proof step did not prove false at assumption level zero.",
        ));
    }
    let verdict = if st.ck.used_sorry_rule() {
        "incomplete"
    } else {
        "correct"
    };
    let mut text = format!("{verdict}\n");
    if st.ck.opts.stats {
        text.push_str(&st.ck.stats_string());
    }
    Ok(text)
}

/// The bytes of the file, if it can be read.
fn read_bytes(file: &str) -> Option<Vec<u8>> {
    std::fs::read(OsString::from_vec(latin1::encode(file))).ok()
}

/// Loads the signature and writes its snapshot to `target`. Prints nothing:
/// what the signature prints goes into the snapshot, to be printed by the
/// runs that use it.
fn write_snapshot(inv: &Invocation, target: &str) -> Result<String> {
    let Some(file) = &inv.file else {
        return Err(Error::plain("no signature to write a snapshot of."));
    };
    if !inv.includes.is_empty() {
        return Err(Error::plain(
            "a snapshot holds one signature: give no other file to include.",
        ));
    }
    let output = Rc::new(RefCell::new(Vec::new()));
    let (warnings, out) = (output.clone(), output.clone());
    let mut st = State::new(
        inv.opts.clone(),
        Box::new(move |line| warnings.borrow_mut().push((true, line.to_string()))),
        Box::new(move |line| out.borrow_mut().push((false, line.to_string()))),
    );
    st.record_for_snapshot();
    include_file(&mut st, file, file.ends_with(".eo"), false, None)?;
    let bytes = st.write_snapshot(&output.borrow())?;
    if std::fs::write(OsString::from_vec(latin1::encode(target)), bytes).is_err() {
        return Err(Error::plain(format!("cannot write the snapshot {target}")));
    }
    Ok(String::new())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|a| latin1::decode(&a.into_vec()))
        .collect();
    let result = parse_args(&args).and_then(|parsed| match parsed {
        Parsed::Print(text) => Ok(text),
        Parsed::Run(inv) => run(inv),
    });
    match result {
        Ok(text) => {
            let mut out = std::io::stdout().lock();
            let _ = out.write_all(&latin1::encode(&text));
            let _ = out.flush();
            ExitCode::SUCCESS
        }
        Err(e) => {
            write_line(std::io::stderr().lock(), &e.to_string());
            ExitCode::FAILURE
        }
    }
}
