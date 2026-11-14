//! Text-mode input and output, as the C runtime does it on Windows.
//!
//! Ethos opens every file as text and writes to the standard streams as
//! text. On Unix that changes nothing. On Windows the runtime removes the
//! carriage return of each CR LF pair it reads, takes a Ctrl-Z byte for the
//! end of the input, and writes each line feed as CR LF. [`input`] and
//! [`output`] do the same on Windows and nothing elsewhere, so that pathos
//! sees and prints what Ethos does on each platform; the two functions
//! they use are compiled, and tested, everywhere.

/// What a text-mode read gives for the bytes of a file: up to the first
/// Ctrl-Z (0x1A), without the CR of each CR LF. A CR before anything else
/// stays.
pub fn translate_input(bytes: &[u8]) -> Vec<u8> {
    let end = bytes.iter().position(|&b| b == 0x1a).unwrap_or(bytes.len());
    let bytes = &bytes[..end];
    let mut out = Vec::with_capacity(bytes.len());
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'\r' && bytes.get(i + 1) == Some(&b'\n') {
            continue;
        }
        out.push(b);
    }
    out
}

/// What a text-mode write puts out for the bytes: CR LF for each LF.
pub fn translate_output(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len() + bytes.len() / 16);
    for &b in bytes {
        if b == b'\n' {
            out.push(b'\r');
        }
        out.push(b);
    }
    out
}

/// The bytes of a file or of standard input as Ethos reads them on this
/// platform.
pub fn input(bytes: Vec<u8>) -> Vec<u8> {
    if cfg!(windows) {
        translate_input(&bytes)
    } else {
        bytes
    }
}

/// The bytes to write to a file or a standard stream for text, as Ethos
/// writes it on this platform.
pub fn output(bytes: Vec<u8>) -> Vec<u8> {
    if cfg!(windows) {
        translate_output(&bytes)
    } else {
        bytes
    }
}

/// Whether the stream takes only UTF-8: a Windows console, which Rust's
/// standard library writes to as Unicode and which refuses anything else.
/// A pipe or a file takes any bytes, on every platform.
pub fn wants_utf8(stream: &impl std::io::IsTerminal) -> bool {
    cfg!(windows) && stream.is_terminal()
}

/// Writes text held as described in [`crate::latin1`] to a standard stream,
/// as Ethos writes it on this platform: one byte per character.
///
/// `utf8_only` says that the stream is one for which [`wants_utf8`] holds.
/// Bytes that are not UTF-8 would be refused there, and the text lost, so
/// such text is written with each byte as the Unicode character of the same
/// number instead. Ethos writes the bytes, and the console shows them in
/// its code page: the same for ASCII, and for the rest whenever the code
/// page is Latin-1.
pub fn write(w: &mut impl std::io::Write, text: &str, utf8_only: bool) -> std::io::Result<()> {
    let bytes = output(crate::latin1::encode(text));
    if utf8_only && std::str::from_utf8(&bytes).is_err() {
        w.write_all(&output(text.as_bytes().to_vec()))
    } else {
        w.write_all(&bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stream like a Windows console: it fails on bytes that are not
    /// UTF-8 and keeps what it was given otherwise.
    struct Utf8Only(Vec<u8>);

    impl std::io::Write for Utf8Only {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if std::str::from_utf8(buf).is_err() {
                return Err(std::io::ErrorKind::InvalidData.into());
            }
            self.0.extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn bytes_above_127_reach_a_stream_that_takes_only_utf8() {
        // the bytes 63 61 66 E9 FF, held one char per byte
        let text = "caf\u{e9}\u{ff}\n";
        let mut console = Utf8Only(Vec::new());
        write(&mut console, text, true).unwrap();
        assert_eq!(console.0, output(text.as_bytes().to_vec()));
        assert!(String::from_utf8(console.0).is_ok());
        // without the fallback the line is refused, and so lost
        assert!(write(&mut Utf8Only(Vec::new()), text, false).is_err());
        // any other stream gets the bytes
        let mut pipe = Vec::new();
        write(&mut pipe, text, false).unwrap();
        assert_eq!(pipe, output(b"caf\xe9\xff\n".to_vec()));
        // ASCII, and bytes that happen to be UTF-8, go out unchanged
        let mut console = Utf8Only(Vec::new());
        write(&mut console, "ok\n", true).unwrap();
        write(&mut console, "\u{c3}\u{a9}\n", true).unwrap();
        assert_eq!(console.0, output(b"ok\n\xc3\xa9\n".to_vec()));
    }

    #[test]
    fn reading() {
        assert_eq!(translate_input(b"a\r\nb\n"), b"a\nb\n");
        assert_eq!(translate_input(b"a\rb\r\r\nc\r"), b"a\rb\r\nc\r");
        assert_eq!(translate_input(b"a\n\x1ab\n"), b"a\n");
        assert_eq!(translate_input(b"a\r\x1a\n"), b"a\r");
        assert_eq!(translate_input(b""), b"");
    }

    #[test]
    fn writing() {
        assert_eq!(translate_output(b"a\nb\r\n"), b"a\r\nb\r\r\n");
        assert_eq!(translate_output(b"ab"), b"ab");
    }
}
