//! Reading and writing binary data, for snapshots.
//!
//! Numbers are little-endian. A [`Reader`] never panics and never trusts a
//! length it reads: every read is checked against what is left of the
//! input, so nothing is allocated that the input could not fill.

/// Collects the bytes written.
#[derive(Default)]
pub struct Writer {
    pub bytes: Vec<u8>,
}

impl Writer {
    pub fn new() -> Writer {
        Writer::default()
    }

    pub fn u8(&mut self, v: u8) {
        self.bytes.push(v);
    }

    pub fn bool(&mut self, v: bool) {
        self.u8(u8::from(v));
    }

    pub fn u32(&mut self, v: u32) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    pub fn u64(&mut self, v: u64) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    /// A length or count. Lengths are 32 bits; the sizes that do not fit
    /// (4 GiB of anything) are beyond what the term store holds.
    pub fn len(&mut self, n: usize) {
        self.u32(u32::try_from(n).unwrap_or(u32::MAX));
    }

    pub fn str(&mut self, s: &str) {
        self.len(s.len());
        self.bytes.extend_from_slice(s.as_bytes());
    }
}

/// Reads from a byte slice. Every method returns `None` at the end of the
/// input or on a value that cannot be right.
pub struct Reader<'a> {
    rest: &'a [u8],
}

impl<'a> Reader<'a> {
    pub fn new(bytes: &'a [u8]) -> Reader<'a> {
        Reader { rest: bytes }
    }

    pub fn is_at_end(&self) -> bool {
        self.rest.is_empty()
    }

    /// The number of bytes not read yet.
    pub fn remaining(&self) -> usize {
        self.rest.len()
    }

    pub fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, tail) = self.rest.split_at_checked(n)?;
        self.rest = tail;
        Some(head)
    }

    pub fn u8(&mut self) -> Option<u8> {
        self.bytes(1).map(|b| b[0])
    }

    pub fn bool(&mut self) -> Option<bool> {
        match self.u8()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    pub fn u32(&mut self) -> Option<u32> {
        let b = self.bytes(4)?;
        Some(u32::from_le_bytes(b.try_into().ok()?))
    }

    pub fn u64(&mut self) -> Option<u64> {
        let b = self.bytes(8)?;
        Some(u64::from_le_bytes(b.try_into().ok()?))
    }

    /// The count of items that follow, each of which takes at least
    /// `min_item_bytes` (not zero) of input. A count that the rest of the
    /// input cannot hold is rejected, so a `Vec` of that capacity is never
    /// larger than a small multiple of the input.
    pub fn len(&mut self, min_item_bytes: usize) -> Option<usize> {
        let n = self.u32()? as usize;
        (n.checked_mul(min_item_bytes.max(1))? <= self.rest.len()).then_some(n)
    }

    pub fn str(&mut self) -> Option<&'a str> {
        let n = self.len(1)?;
        std::str::from_utf8(self.bytes(n)?).ok()
    }
}

/// A 64-bit hash of the bytes, for detecting damaged or changed files. It
/// is not cryptographic: it does not stop someone from making a file with
/// a chosen hash.
pub fn content_hash(bytes: &[u8]) -> u64 {
    const K: u64 = 0x9E37_79B9_7F4A_7C15;
    let fold = |h: u64, x: u64| {
        let full = u128::from(h ^ x) * u128::from(K);
        (full as u64) ^ ((full >> 64) as u64)
    };
    let mut h = fold(0x243F_6A88_85A3_08D3, bytes.len() as u64);
    let (words, tail) = bytes.as_chunks::<8>();
    for w in words {
        h = fold(h, u64::from_le_bytes(*w));
    }
    let mut last = [0u8; 8];
    last[..tail.len()].copy_from_slice(tail);
    // the rotation keeps a zero word from leaving the state as it was
    fold(h.rotate_left(29), u64::from_le_bytes(last))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        let mut w = Writer::new();
        w.u8(7);
        w.bool(true);
        w.u32(0xdead_beef);
        w.u64(u64::MAX - 1);
        w.str("a\u{e9}");
        let mut r = Reader::new(&w.bytes);
        assert_eq!(r.u8(), Some(7));
        assert_eq!(r.bool(), Some(true));
        assert_eq!(r.u32(), Some(0xdead_beef));
        assert_eq!(r.u64(), Some(u64::MAX - 1));
        assert_eq!(r.str(), Some("a\u{e9}"));
        assert!(r.is_at_end());
        assert_eq!(r.u8(), None);
    }

    #[test]
    fn lengths_are_bounded_by_the_input() {
        let mut w = Writer::new();
        w.u32(1000);
        w.u32(0);
        assert_eq!(Reader::new(&w.bytes).len(1), None);
        assert_eq!(Reader::new(&w.bytes).len(4), None);
        let mut w = Writer::new();
        w.u32(1);
        w.u32(0);
        assert_eq!(Reader::new(&w.bytes).len(4), Some(1));
        // invalid UTF-8 and a bad boolean
        assert_eq!(Reader::new(&[1, 0, 0, 0, 0xff]).str(), None);
        assert_eq!(Reader::new(&[2]).bool(), None);
    }

    #[test]
    fn hash_depends_on_every_byte_and_the_length() {
        let a = content_hash(b"0123456789abcdef");
        assert_ne!(a, content_hash(b"0123456789abcdeF"));
        assert_ne!(a, content_hash(b"1123456789abcdef"));
        assert_ne!(content_hash(&[0; 8]), content_hash(&[0; 16]));
        assert_ne!(content_hash(&[]), content_hash(&[0]));
    }
}
