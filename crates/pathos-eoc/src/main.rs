//! `pathos-eoc`: pathos with the Eunoia compiler stages, as `ethos-eoc` is
//! Ethos with them (`plugins/main_eoc.cpp`). eoc's driver
//! (`tools/eoc/driver.py`) runs it once per stage.
//!
//! It takes a file, never standard input, and prints no verdict: a run
//! succeeded if it exits with 0.

mod defs_reader;
mod desugar;
mod lean_meta;
mod linear_patterns;
mod meta_reduce;
mod model_smt;
mod native_layer;
mod smt_meta;
mod std_plugin;
mod trim_defs;

use std::io::Write;
use std::os::unix::ffi::OsStringExt;
use std::process::ExitCode;

use pathos_check::Options;
use pathos_elab::{Plugin, State, include_file};
use pathos_syntax::{Error, Result, latin1};

/// The stages `ethos-eoc` has, and whether pathos has them yet.
const PLUGINS: &[(&str, bool)] = &[
    ("desugar", true),
    ("desugar-vc", true),
    ("smt-meta", true),
    ("smt-meta-sygus", true),
    ("lean-meta", true),
    ("trim-defs", true),
    ("model-smt", true),
];

/// What the command line asks for.
struct Invocation {
    opts: Options,
    plugin: String,
    /// The files to include first, and whether each is a reference.
    includes: Vec<(String, bool)>,
    file: String,
    /// `--semantics=` and `--smt-semantics=`, for the `model-smt` stage;
    /// empty if not given.
    defs_file: String,
    smt_defs_file: String,
    /// `--no-parser` (negated) and `--lean-config=`, for the `lean-meta`
    /// stage.
    generate_parser: bool,
    lean_config_file: String,
}

fn parse_args(args: &[String]) -> Result<Invocation> {
    let mut opts = Options::default();
    let mut file: Option<String> = None;
    let mut plugin = String::new();
    let mut generate_parser = true;
    let (mut defs_file, mut smt_defs_file, mut lean_config_file) =
        (String::new(), String::new(), String::new());
    let mut includes = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        i += 1;
        if let Some(name) = arg.strip_prefix("--plugin.") {
            if !plugin.is_empty() {
                return Err(Error::plain(format!(
                    "multiple plugins specified, \"{plugin}\" and \"{name}\""
                )));
            }
            plugin = name.to_string();
            continue;
        }
        if arg == "--no-parser" {
            generate_parser = false;
            continue;
        }
        if let Some(f) = arg.strip_prefix("--smt-semantics=") {
            smt_defs_file = f.to_string();
            continue;
        }
        if let Some(f) = arg.strip_prefix("--semantics=") {
            defs_file = f.to_string();
            continue;
        }
        if let Some(f) = arg.strip_prefix("--lean-config=") {
            lean_config_file = f.to_string();
            continue;
        }
        if let Some(f) = arg.strip_prefix("--include=") {
            includes.push((f.to_string(), false));
            continue;
        }
        if let Some(f) = arg.strip_prefix("--reference=") {
            includes.push((f.to_string(), true));
            continue;
        }
        // What is left that begins with two dashes is an option of Ethos.
        if let Some(rest) = arg.strip_prefix("--") {
            let (key, val) = match rest.strip_prefix("no-") {
                Some(key) => (key, false),
                None => (rest, true),
            };
            if matches!(key, "require-proof-of-false" | "help" | "show-config") {
                return Err(Error::plain(format!("{arg} is not supported by ethos-eoc")));
            }
            if !opts.set_option(key, val) {
                return Err(Error::plain(format!("unrecognized option {arg}")));
            }
            continue;
        }
        if arg == "-t" {
            if i >= args.len() {
                return Err(Error::plain("Missing trace tag."));
            }
            return Err(Error::plain("tracing not enabled in this build"));
        } else if arg.starts_with('-') {
            return Err(Error::plain(format!("unrecognized option {arg}")));
        } else if let Some(first) = &file {
            return Err(Error::plain(format!(
                "multiple files specified, \"{first}\" and \"{arg}\""
            )));
        } else {
            file = Some(arg.clone());
        }
    }
    let Some(file) = file else {
        return Err(Error::plain("no input specified."));
    };
    if !generate_parser && plugin != "lean-meta" {
        return Err(Error::plain("--no-parser requires --plugin.lean-meta"));
    }
    if !defs_file.is_empty() && plugin != "model-smt" {
        return Err(Error::plain("--semantics requires --plugin.model-smt"));
    }
    if !smt_defs_file.is_empty() && plugin != "model-smt" {
        return Err(Error::plain("--smt-semantics requires --plugin.model-smt"));
    }
    if !lean_config_file.is_empty() && plugin != "lean-meta" {
        return Err(Error::plain("--lean-config requires --plugin.lean-meta"));
    }
    Ok(Invocation {
        opts,
        plugin,
        includes,
        file,
        defs_file,
        smt_defs_file,
        generate_parser,
        lean_config_file,
    })
}

fn create_plugin(inv: &Invocation) -> Result<Box<dyn Plugin>> {
    let name = inv.plugin.as_str();
    match name {
        "desugar" => Ok(Box::new(desugar::Desugar::new(false)?)),
        "desugar-vc" => Ok(Box::new(desugar::Desugar::new(true)?)),
        "smt-meta" => Ok(Box::new(smt_meta::SmtMeta::new(false)?)),
        "smt-meta-sygus" => Ok(Box::new(smt_meta::SmtMeta::new(true)?)),
        "lean-meta" => Ok(Box::new(lean_meta::LeanMeta::new(
            inv.generate_parser,
            &inv.lean_config_file,
        )?)),
        "trim-defs" => Ok(Box::new(trim_defs::TrimDefs::new()?)),
        // Naming neither file leaves the stage the SMT-LIB semantics of the
        // source tree and no semantics of an input, as an empty name does.
        "model-smt" => Ok(Box::new(model_smt::ModelSmt::new(
            &inv.defs_file,
            &inv.smt_defs_file,
        )?)),
        _ if PLUGINS.contains(&(name, false)) => Err(Error::fatal(format!(
            "pathos-eoc: the plugin \"{name}\" is not ported yet"
        ))),
        _ => Err(Error::plain(format!(
            "unknown plugin \"{name}\" (available: desugar, desugar-vc, smt-meta, \
             smt-meta-sygus, lean-meta, trim-defs, model-smt)"
        ))),
    }
}

/// Writes a line of text held as described in `pathos_syntax::latin1`.
fn write_line(mut w: impl Write, line: &str) {
    let mut bytes = latin1::encode(line);
    bytes.push(b'\n');
    // Nothing useful can be done if stdout or stderr is closed.
    let _ = w.write_all(&bytes);
}

/// Reads the inputs with the plugin attached. Returns what to print at the
/// end.
fn run(mut inv: Invocation) -> Result<String> {
    let mut st = State::new(
        std::mem::take(&mut inv.opts),
        Box::new(|line| write_line(std::io::stderr().lock(), line)),
        Box::new(|line| write_line(std::io::stdout().lock(), line)),
    );
    // the plugin must be there before any file is read
    if !inv.plugin.is_empty() {
        st.set_plugin(create_plugin(&inv)?)?;
    }
    for (file, is_reference) in &inv.includes {
        include_file(&mut st, file, !is_reference, *is_reference, None)?;
    }
    // files named *.eo are signatures
    include_file(&mut st, &inv.file, inv.file.ends_with(".eo"), false, None)?;
    st.finalize_plugin()?;
    Ok(if st.ck.opts.stats {
        st.ck.stats_string()
    } else {
        String::new()
    })
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|a| latin1::decode(&a.into_vec()))
        .collect();
    match parse_args(&args).and_then(run) {
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
