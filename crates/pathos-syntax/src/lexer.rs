//! The lexer (`lexer.cpp` in Ethos).
//!
//! This follows the C++ character for character, because error messages
//! carry the position of the last token read, and because a few quirks of
//! the C++ decide which inputs are accepted (see `parse_non_empty_char_list`).

use crate::error::{Error, Location, Result};
use crate::token::Token;

const EOF: i32 = -1;

const WHITESPACE: u8 = 1 << 0;
const DECIMAL_DIGIT: u8 = 1 << 1;
const HEXADECIMAL_DIGIT: u8 = 1 << 2;
const BIT: u8 = 1 << 3;
const SYMBOL_START: u8 = 1 << 4;
const SYMBOL: u8 = 1 << 5;

/// The non-alphanumeric characters that may occur in symbols.
const EXTRA_SYMBOL_CHARS: &[u8] = b"+-/*=%?!.$_~&^<>@";

const fn char_classes() -> [u8; 256] {
    let mut t = [0u8; 256];
    let mut ch = b'a';
    while ch <= b'z' {
        t[ch as usize] |= SYMBOL_START | SYMBOL;
        ch += 1;
    }
    ch = b'A';
    while ch <= b'Z' {
        t[ch as usize] |= SYMBOL_START | SYMBOL;
        ch += 1;
    }
    ch = b'a';
    while ch <= b'f' {
        t[ch as usize] |= HEXADECIMAL_DIGIT;
        t[(ch - b'a' + b'A') as usize] |= HEXADECIMAL_DIGIT;
        ch += 1;
    }
    ch = b'0';
    while ch <= b'9' {
        t[ch as usize] |= HEXADECIMAL_DIGIT | DECIMAL_DIGIT | SYMBOL;
        ch += 1;
    }
    t[b'0' as usize] |= BIT;
    t[b'1' as usize] |= BIT;
    let mut i = 0;
    while i < EXTRA_SYMBOL_CHARS.len() {
        t[EXTRA_SYMBOL_CHARS[i] as usize] |= SYMBOL_START | SYMBOL;
        i += 1;
    }
    // allowed inside symbols, for eo::
    t[b':' as usize] |= SYMBOL;
    t[b' ' as usize] |= WHITESPACE;
    t[b'\t' as usize] |= WHITESPACE;
    t[b'\r' as usize] |= WHITESPACE;
    t[b'\n' as usize] |= WHITESPACE;
    t
}

static CHAR_CLASS: [u8; 256] = char_classes();

#[inline]
fn is_class(ch: i32, class: u8) -> bool {
    // End of input (-1) indexes entry 255 in Ethos, which has no class.
    CHAR_CLASS[(ch & 0xff) as usize] & class != 0
}

/// A lexer over one input.
pub struct Lexer {
    input: Vec<u8>,
    pos: usize,
    input_name: String,
    /// The start of the last token read: where errors are reported.
    start_line: u32,
    start_column: u32,
    /// The position after the last character read.
    end_line: u32,
    end_column: u32,
    /// Tokens put back; read again last in, first out.
    peeked: Vec<Token>,
    /// The text of the last token read from the input.
    token: String,
    /// A character read but not consumed.
    peeked_char: Option<i32>,
    lex_let: bool,
    lex_type: bool,
}

impl Lexer {
    /// `lex_let`: whether `let` is a token of its own. `lex_type`: whether
    /// `Type` is.
    pub fn new(input: Vec<u8>, input_name: &str, lex_let: bool, lex_type: bool) -> Lexer {
        Lexer {
            input,
            pos: 0,
            input_name: input_name.to_string(),
            start_line: 1,
            start_column: 0,
            end_line: 1,
            end_column: 0,
            peeked: Vec::new(),
            token: String::new(),
            peeked_char: None,
            lex_let,
            lex_type,
        }
    }

    /// The text of the last token read from the input. After a peek this is
    /// the peeked token's text.
    pub fn token_str(&self) -> &str {
        &self.token
    }

    pub fn next_token(&mut self) -> Result<Token> {
        match self.peeked.pop() {
            Some(t) => Ok(t),
            None => self.next_token_internal(),
        }
    }

    /// Reads the next token and puts it back. Peek at most one token at a
    /// time: put-back tokens are read last in, first out.
    pub fn peek_token(&mut self) -> Result<Token> {
        let t = self.next_token_internal()?;
        self.reinsert_token(t);
        Ok(t)
    }

    pub fn reinsert_token(&mut self, t: Token) {
        self.peeked.push(t);
    }

    /// Reads a token, which must be `t`.
    pub fn eat_token(&mut self, t: Token) -> Result<()> {
        let tt = self.next_token()?;
        if t != tt {
            return Err(self.unexpected_token_error(tt, &format!("Expected a {t}")));
        }
        Ok(())
    }

    /// Reads a token, which must be `t` or `f`. Returns whether it was `t`.
    pub fn eat_token_choice(&mut self, t: Token, f: Token) -> Result<bool> {
        let tt = self.next_token()?;
        if tt == t {
            Ok(true)
        } else if tt != f {
            Err(self.unexpected_token_error(tt, &format!("Expected {t} or {f}")))
        } else {
            Ok(false)
        }
    }

    /// The text of a warning at the current position, which Ethos prints on
    /// stdout.
    pub fn warning(&self, msg: &str) -> String {
        format!(
            "{}:{}.{}: {}",
            self.input_name, self.start_line, self.start_column, msg
        )
    }

    /// An error at the start of the last token read.
    pub fn parse_error(&self, msg: impl Into<String>) -> Error {
        Error::at(
            Location {
                file: self.input_name.clone(),
                line: self.start_line,
                column: self.start_column,
            },
            msg,
        )
    }

    /// The error for reading `t` where `info` was expected.
    pub fn unexpected_token_error(&self, t: Token, info: &str) -> Error {
        self.parse_error(format!("{}, got `{}` ({}).\n", info, self.token, t))
    }

    fn next_token_internal(&mut self) -> Result<Token> {
        self.token.clear();
        let ret = self.compute_next_token();
        // Ethos hands the token's text out as a C string, so everyone who
        // reads it sees it end at its first NUL character.
        if let Some(nul) = self.token.find('\0') {
            self.token.truncate(nul);
        }
        ret
    }

    fn read_next_char(&mut self) -> i32 {
        match self.input.get(self.pos) {
            Some(&b) => {
                self.pos += 1;
                // Ethos reads into a signed char, so the byte 0xFF is -1,
                // which is also its end-of-input marker. A token ends there,
                // but reading goes on after it.
                if b == 0xff { EOF } else { i32::from(b) }
            }
            None => EOF,
        }
    }

    fn next_char(&mut self) -> i32 {
        if let Some(ch) = self.peeked_char.take() {
            return ch;
        }
        let ch = self.read_next_char();
        if ch == i32::from(b'\n') {
            self.end_line = self.end_line.wrapping_add(1);
            self.end_column = 0;
        } else {
            // the end of the input counts as a column too
            self.end_column = self.end_column.wrapping_add(1);
        }
        ch
    }

    fn save_char(&mut self, ch: i32) {
        self.peeked_char = Some(ch);
    }

    fn bump_span(&mut self) {
        self.start_line = self.end_line;
        self.start_column = self.end_column;
    }

    fn push_to_token(&mut self, ch: i32) {
        self.token.push(char::from((ch & 0xff) as u8));
    }

    fn compute_next_token(&mut self) -> Result<Token> {
        self.bump_span();
        let mut ch;
        // skip whitespace and comments
        loop {
            loop {
                ch = self.next_char();
                if ch == EOF {
                    return Ok(Token::Eof);
                }
                if !is_class(ch, WHITESPACE) {
                    break;
                }
            }
            if ch != i32::from(b';') {
                break;
            }
            loop {
                ch = self.next_char();
                if ch == i32::from(b'\n') {
                    break;
                }
                if ch == EOF {
                    return Ok(Token::Eof);
                }
            }
        }
        self.bump_span();
        self.push_to_token(ch);
        match u8::try_from(ch).unwrap_or(0) {
            b'(' => return Ok(Token::Lparen),
            b')' => return Ok(Token::Rparen),
            b'|' => loop {
                ch = self.next_char();
                if ch == EOF {
                    return Ok(Token::UnterminatedQuotedSymbol);
                }
                self.push_to_token(ch);
                if ch == i32::from(b'|') {
                    return Ok(Token::QuotedSymbol);
                }
            },
            b'#' => {
                ch = self.next_char();
                if ch == i32::from(b'b') {
                    self.push_to_token(ch);
                    if !self.parse_non_empty_char_list(BIT) {
                        return Err(self.parse_error("Error expected bit string"));
                    }
                    return Ok(Token::BinaryLiteral);
                } else if ch == i32::from(b'x') {
                    self.push_to_token(ch);
                    if !self.parse_non_empty_char_list(HEXADECIMAL_DIGIT) {
                        return Err(self.parse_error("Error expected hexadecimal string"));
                    }
                    return Ok(Token::HexLiteral);
                }
                return Err(self.parse_error("Error finding token following #"));
            }
            b'"' => loop {
                ch = self.next_char();
                if ch == EOF {
                    return Ok(Token::UnterminatedStringLiteral);
                } else if ch == i32::from(b'"') {
                    self.push_to_token(ch);
                    ch = self.next_char();
                    // "" is the escape sequence for "
                    if ch != i32::from(b'"') {
                        self.save_char(ch);
                        return Ok(Token::StringLiteral);
                    }
                }
                self.push_to_token(ch);
            },
            b':' => {
                if !self.parse_char(SYMBOL_START) {
                    return Err(self.parse_error("Error expected symbol following :"));
                }
                self.parse_non_empty_char_list(SYMBOL);
                return Ok(Token::Keyword);
            }
            _ => {
                if is_class(ch, DECIMAL_DIGIT) {
                    let mut res = Token::IntegerLiteral;
                    self.parse_char_list(DECIMAL_DIGIT);
                    // maybe .[0-9]+ or /[0-9]+
                    ch = self.next_char();
                    if ch == i32::from(b'.') || ch == i32::from(b'/') {
                        self.push_to_token(ch);
                        res = if ch == i32::from(b'.') {
                            Token::DecimalLiteral
                        } else {
                            Token::RationalLiteral
                        };
                        if !self.parse_non_empty_char_list(DECIMAL_DIGIT) {
                            return Err(
                                self.parse_error("Error expected decimal string following .")
                            );
                        }
                    } else {
                        self.save_char(ch);
                    }
                    return Ok(res);
                } else if is_class(ch, SYMBOL_START) {
                    self.parse_char_list(SYMBOL);
                    return Ok(self.tokenize_current_symbol());
                }
            }
        }
        Err(self.parse_error("Error finding token"))
    }

    /// Reads one character, which must be of the class. A character of
    /// another class is consumed and lost; the caller reports an error.
    fn parse_char(&mut self, class: u8) -> bool {
        let ch = self.next_char();
        if !is_class(ch, class) {
            return false;
        }
        self.push_to_token(ch);
        true
    }

    /// Reads one or more characters of the class.
    ///
    /// When the first character is of another class it is consumed and lost,
    /// as in Ethos. Callers report an error then, except for keywords: after
    /// a one-letter keyword such as `:a`, the next character disappears.
    fn parse_non_empty_char_list(&mut self, class: u8) -> bool {
        let ch = self.next_char();
        if !is_class(ch, class) {
            return false;
        }
        self.push_to_token(ch);
        self.parse_char_list(class);
        true
    }

    /// Reads zero or more characters of the class.
    fn parse_char_list(&mut self, class: u8) {
        loop {
            let ch = self.next_char();
            if !is_class(ch, class) {
                self.save_char(ch);
                return;
            }
            self.push_to_token(ch);
        }
    }

    /// Finds the token for the symbol just read, which may be a special one.
    fn tokenize_current_symbol(&self) -> Token {
        let t = self.token.as_bytes();
        match t[0] {
            b'!' if t.len() == 1 => Token::Attribute,
            b'-' if t.len() >= 2 => {
                // maybe a negative numeral, rational or decimal
                let mut ret = Token::IntegerLiteral;
                for i in 1..t.len() {
                    if is_class(i32::from(t[i]), DECIMAL_DIGIT) {
                        continue;
                    } else if i + 1 < t.len() && ret == Token::IntegerLiteral {
                        if t[i] == b'.' {
                            ret = Token::DecimalLiteral;
                            continue;
                        } else if t[i] == b'/' {
                            ret = Token::RationalLiteral;
                            continue;
                        }
                    }
                    return Token::Symbol;
                }
                ret
            }
            _ => match t {
                b"eo::define" => Token::EvalDefine,
                b"par" => Token::Par,
                b"let" if self.lex_let => Token::Let,
                b"Bool" => Token::BoolType,
                b"Type" if self.lex_type => Token::Type,
                _ => Token::Symbol,
            },
        }
    }

    /// The name of the input, as it appears in error messages.
    pub fn input_name(&self) -> &str {
        &self.input_name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Reads all the tokens of `text`; for tests.
    fn tokens_of(text: &str, lex_let: bool, lex_type: bool) -> Result<Vec<(Token, String)>> {
        let mut lexer = Lexer::new(crate::latin1::encode(text), "test", lex_let, lex_type);
        let mut out = Vec::new();
        loop {
            let t = lexer.next_token()?;
            if t == Token::Eof {
                return Ok(out);
            }
            out.push((t, lexer.token_str().to_string()));
        }
    }

    fn toks(text: &str) -> Vec<(Token, String)> {
        tokens_of(text, true, true).unwrap()
    }

    fn kinds(text: &str) -> Vec<Token> {
        toks(text).into_iter().map(|(t, _)| t).collect()
    }

    #[test]
    fn basic_tokens() {
        assert_eq!(
            toks("(declare-const x Int) ; comment\n"),
            vec![
                (Token::Lparen, "(".into()),
                (Token::Symbol, "declare-const".into()),
                (Token::Symbol, "x".into()),
                (Token::Symbol, "Int".into()),
                (Token::Rparen, ")".into()),
            ]
        );
    }

    #[test]
    fn literals() {
        use Token::*;
        assert_eq!(
            kinds("12 1.5 3/4 -7 -7.5 -1/2 #b01 #xFf \"a\"\"b\" |q s| :key"),
            vec![
                IntegerLiteral,
                DecimalLiteral,
                RationalLiteral,
                IntegerLiteral,
                DecimalLiteral,
                RationalLiteral,
                BinaryLiteral,
                HexLiteral,
                StringLiteral,
                QuotedSymbol,
                Keyword
            ]
        );
        assert_eq!(toks("\"a\"\"b\"")[0].1, "\"a\"\"b\"");
        assert_eq!(kinds("- -a -5. !x ! eo::define par let Bool Type"), {
            vec![
                Symbol, Symbol, Symbol, Symbol, Attribute, EvalDefine, Par, Let, BoolType, Type,
            ]
        });
        assert_eq!(tokens_of("let Type", false, false).unwrap(), {
            vec![(Symbol, "let".into()), (Symbol, "Type".into())]
        });
        assert_eq!(kinds("\"abc"), vec![UnterminatedStringLiteral]);
        assert_eq!(kinds("|abc"), vec![UnterminatedQuotedSymbol]);
    }

    #[test]
    fn one_letter_keyword_swallows_next_char() {
        // as in Ethos
        assert_eq!(kinds(":a)"), vec![Token::Keyword]);
        assert_eq!(kinds(":ab)"), vec![Token::Keyword, Token::Rparen]);
    }

    #[test]
    fn byte_ff_reads_as_end_of_input() {
        // as in Ethos
        let mut lexer = Lexer::new(b"(a |x\xffy| b)".to_vec(), "f.eo", true, true);
        let mut seen = Vec::new();
        for _ in 0..6 {
            seen.push(lexer.next_token().unwrap());
        }
        use Token::*;
        // `|x` ends at the 0xFF byte; `y` is a symbol; `| b)` runs to the
        // real end of the input.
        assert_eq!(
            seen,
            vec![
                Lparen,
                Symbol,
                UnterminatedQuotedSymbol,
                Symbol,
                UnterminatedQuotedSymbol,
                Eof
            ]
        );
    }

    #[test]
    fn error_positions() {
        let mut lexer = Lexer::new(b"(a\n  #z".to_vec(), "f.eo", true, true);
        assert_eq!(lexer.next_token(), Ok(Token::Lparen));
        assert_eq!(lexer.next_token(), Ok(Token::Symbol));
        let err = lexer.next_token().unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error: f.eo:2.3: Error finding token following #\n"
        );
    }

    #[test]
    fn position_at_end_of_input() {
        // The position stays at the last token when the end is reached.
        let mut lexer = Lexer::new(b"(a b)\n".to_vec(), "f.eo", true, true);
        while lexer.next_token().unwrap() != Token::Eof {}
        assert_eq!(lexer.parse_error("x").to_string(), "Error: f.eo:1.5: x\n");
    }
}
