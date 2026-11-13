//! The error type shared by the lexer, the parser and the checker.

use std::fmt;

/// A position in an input: where the token being read when the error was
/// found starts.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Location {
    /// The input's name as Ethos prints it: the canonical path of the file.
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// An error that ends the run. Its `Display` is the text Ethos writes to
/// stderr after its `Fatal failure within ...` line, without the final
/// newline.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Error {
    /// Where the error was found, for errors reported through the lexer.
    pub location: Option<Location>,
    /// Whether the text starts with `Error: `. Ethos's internal failures,
    /// such as a file that cannot be opened, do not.
    pub labelled: bool,
    pub message: String,
}

impl Error {
    /// An error at a position in the input. Ethos ends these messages with a
    /// newline of their own, so one is added here.
    pub fn at(location: Location, message: impl Into<String>) -> Error {
        let mut message = message.into();
        message.push('\n');
        Error { location: Some(location), labelled: true, message }
    }

    /// An error without a position, printed as `Error: <message>`.
    pub fn plain(message: impl Into<String>) -> Error {
        Error { location: None, labelled: true, message: message.into() }
    }

    /// A failure printed as the bare message.
    pub fn fatal(message: impl Into<String>) -> Error {
        Error { location: None, labelled: false, message: message.into() }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.labelled {
            f.write_str("Error: ")?;
        }
        if let Some(loc) = &self.location {
            write!(f, "{}:{}.{}: ", loc.file, loc.line, loc.column)?;
        }
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;
