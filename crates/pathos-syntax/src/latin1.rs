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
    #[should_panic(expected = "is not a byte")]
    fn chars_above_255_are_bugs() {
        encode("a\u{100}");
    }
}
