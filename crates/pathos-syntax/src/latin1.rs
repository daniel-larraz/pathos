//! Byte strings held as Rust strings.
//!
//! Ethos works on bytes: it never decodes its input, counts columns in
//! bytes, and writes symbol names back out byte for byte. pathos keeps text
//! in `String`s, so it maps each input byte to the `char` with the same
//! number (Latin-1) and maps back when writing. Input that is not valid
//! UTF-8 then round-trips unchanged, and one `char` is one column.
//!
//! Every string that comes from the input or goes to the output passes
//! through [`decode`] and [`encode`]: file contents, file names and messages.

/// Maps each byte to the `char` with the same number.
pub fn decode(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| char::from(b)).collect()
}

/// Maps each `char` back to its byte. Text made by [`decode`], and anything
/// built from it and ASCII, has no `char` above 255. One that does is a bug
/// in pathos: debug builds and tests stop on it, release builds write `?`.
pub fn encode(s: &str) -> Vec<u8> {
    s.chars()
        .map(|c| {
            let byte = u8::try_from(u32::from(c));
            debug_assert!(byte.is_ok(), "char {c:?} is not a byte: {s:?}");
            byte.unwrap_or(b'?')
        })
        .collect()
}

/// A file name, a command-line argument or an environment variable as text.
///
/// On Unix these are bytes, and Ethos takes them as they are, so this is
/// [`decode`]. On Windows they are UTF-16, which Ethos (built with MinGW)
/// receives converted to the process's code page: here each unit below 256
/// becomes the `char` with the same number, as code page 1252 does for
/// ASCII and for 0xA0 to 0xFF, and any other becomes `?`, the character
/// Windows substitutes when the code page lacks one.
#[cfg(unix)]
pub fn from_os(s: &std::ffi::OsStr) -> String {
    use std::os::unix::ffi::OsStrExt;
    decode(s.as_bytes())
}

/// See the Unix version.
#[cfg(windows)]
pub fn from_os(s: &std::ffi::OsStr) -> String {
    use std::os::windows::ffi::OsStrExt;
    s.encode_wide()
        .map(|unit| u8::try_from(unit).map_or('?', char::from))
        .collect()
}

/// The inverse of [`from_os`]: the name to give the operating system for
/// text made by it.
#[cfg(unix)]
pub fn to_os(s: &str) -> std::ffi::OsString {
    use std::os::unix::ffi::OsStringExt;
    std::ffi::OsString::from_vec(encode(s))
}

/// See the Unix version.
#[cfg(windows)]
pub fn to_os(s: &str) -> std::ffi::OsString {
    use std::os::windows::ffi::OsStringExt;
    let units: Vec<u16> = encode(s).into_iter().map(u16::from).collect();
    std::ffi::OsString::from_wide(&units)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        let bytes: Vec<u8> = (0..=255).collect();
        assert_eq!(encode(&decode(&bytes)), bytes);
        assert_eq!(decode(b"abc"), "abc");
    }

    #[test]
    fn operating_system_strings_round_trip() {
        let text = "dir/a b\u{e9}.eo";
        assert_eq!(from_os(&to_os(text)), text);
    }

    // The check is a debug_assert!, so it exists only with debug assertions;
    // in a release build encode() writes such a char as `?`.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "is not a byte")]
    fn chars_above_255_are_bugs() {
        encode("a\u{100}");
    }
}
