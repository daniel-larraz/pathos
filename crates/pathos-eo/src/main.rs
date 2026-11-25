//! The pathos command-line checker (`main.cpp` in Ethos).

use std::cell::RefCell;
use std::io::{IsTerminal, Read, Write};
use std::process::ExitCode;
use std::rc::Rc;

use pathos_check::Options;
use pathos_elab::{Parser, State, include_file};
use pathos_syntax::{Error, Result, latin1, textmode};

const HELP: &str = "        --include=X: includes the file specified by X.
             --help: displays this message.
 --max-code-point=X: sets the maximum code point of string characters to X (default 196607, at most 1114111, i.e. 0x10FFFF).
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
        if let Some(val) = arg.strip_prefix("--max-code-point=") {
            // a decimal value, or a hexadecimal value prefixed by 0x
            if !parse_max_code_point(val).is_some_and(pathos_term::set_max_code_point) {
                return Err(Error::plain(format!(
                    "invalid value for --max-code-point: \"{val}\", must be between {} and {} (0x{:x})",
                    pathos_term::MIN_MAX_CODE_POINT,
                    pathos_term::MAX_MAX_CODE_POINT,
                    pathos_term::MAX_MAX_CODE_POINT
                )));
            }
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

/// The value of `--max-code-point`, as Ethos's `Options::setMaxCodePoint`
/// reads it: decimal, or hexadecimal after `0x`/`0X`; the first digit a
/// hexadecimal digit; the rest read as `std::stoul` does in that base (which
/// in base 16 also takes a second `0x`), all of it. Out of range is `None`
/// only if it does not fit; `set_max_code_point` checks the bounds.
fn parse_max_code_point(val: &str) -> Option<u32> {
    let (digits, radix) = match val.get(..2) {
        Some("0x") | Some("0X") => (&val[2..], 16),
        _ => (val, 10),
    };
    if !digits.chars().next().is_some_and(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    // stoul in base 16 skips a 0x before the digits
    let digits = match digits.get(..2) {
        Some("0x") | Some("0X")
            if radix == 16
                && digits[2..]
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_hexdigit()) =>
        {
            &digits[2..]
        }
        _ => digits,
    };
    let m = u64::from_str_radix(digits, radix).ok()?;
    u32::try_from(m).ok()
}

/// Writes a line of text held as described in `pathos_syntax::latin1`.
fn write_line(mut w: impl Write + IsTerminal, line: &str) {
    let utf8_only = textmode::wants_utf8(&w);
    // Nothing useful can be done if stdout or stderr is closed.
    let _ = textmode::write(&mut w, &format!("{line}\n"), utf8_only);
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
            if stdin_is_a_terminal() {
                return Err(Error::plain("no input specified."));
            }
            let mut input = Vec::new();
            if std::io::stdin().lock().read_to_end(&mut input).is_err() {
                return Err(Error::fatal("Couldn't read the input"));
            }
            let input = textmode::input(input);
            Parser::for_standard_input(&mut st, input).parse_all()?;
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

/// C's `isatty` on standard input, which decides whether Ethos waits for a
/// proof there. On Unix that is a terminal. On Windows it is any character
/// device: a console, and also the null device, which is what a process
/// started without input is given.
#[cfg(not(windows))]
fn stdin_is_a_terminal() -> bool {
    std::io::stdin().is_terminal()
}

/// See the other version. The standard library has no call for the kind of
/// a handle. What it has, measured on both Windows platforms (run
/// 43636416291): asking for a handle's metadata succeeds for a file and
/// for a pipe, fails with `ERROR_INVALID_HANDLE` when there is no standard
/// input, and fails with `ERROR_INVALID_FUNCTION` for the null device.
#[cfg(windows)]
fn stdin_is_a_terminal() -> bool {
    use std::os::windows::io::AsHandle;
    const ERROR_INVALID_FUNCTION: i32 = 1;
    let stdin = std::io::stdin();
    if stdin.is_terminal() {
        return true;
    }
    let Ok(handle) = stdin.as_handle().try_clone_to_owned() else {
        return false;
    };
    match std::fs::File::from(handle).metadata() {
        Ok(_) => false,
        Err(e) => e.raw_os_error() == Some(ERROR_INVALID_FUNCTION),
    }
}

/// The bytes of the file, if it can be read.
fn read_bytes(file: &str) -> Option<Vec<u8>> {
    std::fs::read(latin1::to_os(file)).ok()
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
    if std::fs::write(latin1::to_os(target), bytes).is_err() {
        return Err(Error::plain(format!("cannot write the snapshot {target}")));
    }
    Ok(String::new())
}

fn main() -> ExitCode {
    pathos_elab::on_checker_thread(check)
}

/// The whole run: reads the command line, checks, and prints the result.
fn check() -> ExitCode {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|a| latin1::from_os(&a))
        .collect();
    let result = parse_args(&args).and_then(|parsed| match parsed {
        Parsed::Print(text) => Ok(text),
        Parsed::Run(inv) => run(inv),
    });
    match result {
        Ok(text) => {
            let mut out = std::io::stdout().lock();
            let utf8_only = textmode::wants_utf8(&out);
            let _ = textmode::write(&mut out, &text, utf8_only);
            let _ = out.flush();
            ExitCode::SUCCESS
        }
        Err(e) => {
            write_line(std::io::stderr().lock(), &e.to_string());
            ExitCode::FAILURE
        }
    }
}
