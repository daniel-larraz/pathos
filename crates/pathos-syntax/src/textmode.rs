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

#[cfg(test)]
mod tests {
    use super::*;

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
