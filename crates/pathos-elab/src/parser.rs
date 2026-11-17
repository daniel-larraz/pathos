//! The parser of one input, and reading files.

use pathos_syntax::{Error, Lexer, Result, latin1, textmode};
use pathos_term::Term;

use crate::snapshot;
use crate::state::State;

/// A parser over one input. It builds terms and runs commands on the state
/// as it reads: there is no syntax tree in between.
pub struct Parser<'a> {
    pub(crate) lex: Lexer,
    pub(crate) st: &'a mut State,
    /// Reading a signature (`.eo`): `Type` is a token, `let` is not, and
    /// literals are not normalized.
    pub(crate) is_signature: bool,
    /// Reading an SMT-LIB reference file.
    pub(crate) is_reference: bool,
    /// An `exit` command was read.
    pub(crate) finished: bool,
}

impl<'a> Parser<'a> {
    pub fn new(
        st: &'a mut State,
        input: Vec<u8>,
        input_name: &str,
        is_signature: bool,
        is_reference: bool,
    ) -> Parser<'a> {
        // `let` is only lexed outside signatures, `Type` only inside
        let lex_let = !is_signature && st.ck.opts.parse_let;
        let lex = Lexer::new(input, input_name, lex_let, is_signature);
        Parser {
            lex,
            st,
            is_signature,
            is_reference,
            finished: false,
        }
    }

    /// A parser for a proof on standard input, which Ethos names `stream`.
    pub fn for_standard_input(st: &'a mut State, input: Vec<u8>) -> Parser<'a> {
        let mut p = Parser::new(st, input, "stream", false, false);
        p.lex.set_stream();
        p
    }

    /// Runs the commands of the input to its end.
    pub fn parse_all(&mut self) -> Result<()> {
        while self.parse_next_command()? {}
        Ok(())
    }
}

/// Reads a file as a signature, a proof or a reference, unless it has been
/// read before. `file` is relative to the file being read. This is the
/// include of a file named on the command line: a name that cannot be
/// included is the error `main.cpp` reports.
pub fn include_file(
    st: &mut State,
    file: &str,
    is_signature: bool,
    is_reference: bool,
    reference_nf: Option<Term>,
) -> Result<()> {
    if try_include_file(st, file, is_signature, is_reference, reference_nf)? {
        Ok(())
    } else {
        Err(Error::plain(format!("cannot include file {file}")))
    }
}

/// `State::includeFile`: as [`include_file`], but false, for the caller to
/// report, if the name is not a regular file's (see `path::resolve`).
pub(crate) fn try_include_file(
    st: &mut State,
    file: &str,
    is_signature: bool,
    is_reference: bool,
    reference_nf: Option<Term>,
) -> Result<bool> {
    let Ok(input_path) = st.resolve_include(file) else {
        return Ok(false);
    };
    if !st.mark_included(&input_path) {
        st.record_include(file, is_signature, None);
        return Ok(true);
    }
    // an ordinary include does not switch the reference's checks off
    if is_reference {
        st.has_reference = true;
        st.reference_nf = reference_nf;
    }
    // a snapshot of this file, if the run has one, stands in for reading it
    if reference_nf.is_none()
        && snapshot::use_for_include(st, &input_path, is_signature, is_reference)
    {
        return Ok(true);
    }
    let current_path = std::mem::replace(&mut st.input_file, input_path.clone());
    let handled = st.with_plugin(|p, st| {
        p.include_file(st, &input_path, is_signature, is_reference, reference_nf)
    });
    if handled == Some(true) {
        st.input_file = current_path;
        return Ok(true);
    }
    let input = read_file(&input_path)?;
    st.record_include(file, is_signature, Some(&input));
    let mut p = Parser::new(st, input, &input_path, is_signature, is_reference);
    p.parse_all()?;
    p.st.record_include_end();
    p.st.input_file = current_path;
    if p.st.assumption_level() != 0 {
        // reported through the lexer, like any other error in the file
        let open =
            p.st.innermost_scope_symbol()
                .unwrap_or_default()
                .to_string();
        return Err(p.lex.parse_error(format!(
            "This file did not preserve assumption scope. The most recent open assumption was \
             {open}."
        )));
    }
    st.with_plugin(|p, st| {
        p.finalize_include_file(st, &input_path, is_signature, is_reference, reference_nf)
    });
    st.take_plugin_error().map_or(Ok(true), Err)
}

/// The bytes of a file. Paths are byte strings held as described in
/// `pathos_syntax::latin1`.
pub(crate) fn read_file(path: &str) -> Result<Vec<u8>> {
    let os_path = latin1::to_os(path);
    match std::fs::read(&os_path) {
        Ok(bytes) => Ok(textmode::input(bytes)),
        // Ethos opens a directory without error and reads nothing from it.
        Err(_) if std::path::Path::new(&os_path).is_dir() => Ok(Vec::new()),
        Err(_) => Err(Error::fatal(format!("Couldn't open file: {path}"))),
    }
}
