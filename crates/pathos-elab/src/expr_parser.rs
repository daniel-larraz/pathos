//! Parsing terms (`expr_parser.cpp` in Ethos).

use std::collections::BTreeMap;

use pathos_check::Attr;
use pathos_syntax::{Result, Token};
use pathos_term::{BitVec, EoString, Integer, Kind, Lit, LitKind, Rational, SymbolKind, Term};

use crate::parser::Parser;

/// The attributes read for one term, with their values, in the order of the
/// `Attr` enum.
pub(crate) type AttrMap = BTreeMap<Attr, Vec<Option<Term>>>;

/// Where an attribute list occurs; decides which attributes are allowed.
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum AttrCtx {
    /// On a term annotated with `!`.
    Term,
    /// On a `declare-rule`.
    ProofRule,
    /// On a parameter in a parameter list.
    Param,
    /// On a `declare-const` or `declare-parameterized-const`.
    Const,
    /// On a `define`.
    Define,
}

/// The kinds of parameter lists.
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum ParamList {
    /// The variables of a binder: these are `eo::var` terms, the same for
    /// the same name and type.
    Binder,
    /// The parameters of a `declare-parameterized-const`.
    Const,
    /// The parameters of a `define`.
    Define,
    Program,
    ProofRule,
}

/// What the term being parsed is part of.
#[derive(Copy, Clone, PartialEq, Eq)]
enum ParseCtx {
    /// `(<op> <term>* <term>`: the frame's `args` are the terms so far.
    NextArg,
    /// `(let (<binding>* (<symbol> <term>`
    LetNextBind,
    /// `(let (<binding>*) <term>`
    LetBody,
    /// `(! <term> <attribute>*`
    TermAnnotateBody,
}

struct StackFrame {
    ctx: ParseCtx,
    /// The scopes to close when the frame is done.
    nscopes: usize,
    args: Vec<Term>,
}

fn attr_of_keyword(key: &str) -> Option<Attr> {
    Some(match key {
        ":implicit" => Attr::Implicit,
        ":is_eq" => Attr::IsEq,
        ":type" => Attr::Type,
        ":list" => Attr::List,
        ":left-assoc" => Attr::LeftAssoc,
        ":right-assoc" => Attr::RightAssoc,
        ":left-assoc-nil" => Attr::LeftAssocNil,
        ":right-assoc-nil" => Attr::RightAssocNil,
        ":left-assoc-non-singleton-nil" => Attr::LeftAssocNsNil,
        ":right-assoc-non-singleton-nil" => Attr::RightAssocNsNil,
        ":chainable" => Attr::Chainable,
        ":pairwise" => Attr::Pairwise,
        ":binder" => Attr::Binder,
        ":let-binder" => Attr::LetBinder,
        ":arg-list" => Attr::ArgList,
        ":opaque" => Attr::Opaque,
        ":syntax" => Attr::Syntax,
        ":restrict" => Attr::Restrict,
        ":sorry" => Attr::Sorry,
        _ => return None,
    })
}

/// If `s` is `bv<numeral>`, the numeral: the head of the SMT-LIB bit-vector
/// constants `(_ bv<numeral> <width>)`.
fn bit_vector_constant_symbol(s: &str) -> Option<&str> {
    let digits = s.strip_prefix("bv")?;
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some(digits)
}

impl Parser<'_> {
    /// Parses a term.
    pub(crate) fn parse_expr(&mut self) -> Result<Term> {
        let mut ret: Option<Term> = None;
        // set when a frame was pushed that must be set up before a term is
        // parsed for it
        let mut needs_update_ctx = false;
        let mut pstack: Vec<StackFrame> = Vec::new();
        // the bindings of each let being parsed
        let mut let_binders: Vec<Vec<(String, Option<Term>)>> = Vec::new();
        loop {
            let mut tok = self.lex.next_token()?;
            match tok {
                Token::Lparen => {
                    tok = self.lex.next_token()?;
                    match tok {
                        Token::Let | Token::EvalDefine => {
                            pstack.push(StackFrame {
                                ctx: ParseCtx::LetNextBind,
                                nscopes: 0,
                                args: Vec::new(),
                            });
                            needs_update_ctx = true;
                            let_binders.push(Vec::new());
                        }
                        Token::Attribute => pstack.push(StackFrame {
                            ctx: ParseCtx::TermAnnotateBody,
                            nscopes: 0,
                            args: Vec::new(),
                        }),
                        Token::Lparen | Token::Symbol | Token::QuotedSymbol => {
                            if tok == Token::Lparen {
                                // ((_ ... and ((as ... may begin a term
                                pstack.push(StackFrame {
                                    ctx: ParseCtx::NextArg,
                                    nscopes: 0,
                                    args: Vec::new(),
                                });
                                tok = self.lex.next_token()?;
                                let head = self.token_str_to_symbol(tok)?;
                                if head != "_" && head != "as" {
                                    return Err(self.lex.parse_error(
                                        "Expected qualified identifier or indexed symbol as \
                                         head of apply",
                                    ));
                                }
                            }
                            if let Some(t) = self.parse_application_head(tok, &mut pstack)? {
                                ret = Some(t);
                            }
                        }
                        Token::UnterminatedQuotedSymbol => {
                            return Err(self.lex.parse_error("Expected SMT-LIBv2 operator"));
                        }
                        _ => {
                            return Err(self
                                .lex
                                .unexpected_token_error(tok, "Expected SMT-LIBv2 operator"));
                        }
                    }
                }
                Token::Rparen => {
                    // only expected after the arguments of an application
                    let Some(sf) = pstack.pop().filter(|sf| sf.ctx == ParseCtx::NextArg) else {
                        return Err(self.lex.unexpected_token_error(
                            tok,
                            "Mismatched parentheses in SMT-LIBv2 term",
                        ));
                    };
                    // (->) is not a type: a function type has a return type
                    if sf.args.len() == 1 && Some(sf.args[0]) == self.st.get_var("->") {
                        return Err(self.lex.parse_error("Expected a return type for ->"));
                    }
                    // (_) is not a term. In a reference file the `_` was
                    // dropped, so the frame has no arguments at all.
                    if sf.args.is_empty()
                        || (sf.args.len() == 1 && Some(sf.args[0]) == self.st.get_var("_"))
                    {
                        return Err(self.lex.parse_error("Expected an operator for _"));
                    }
                    let app = self.st.ck.mk_expr(Kind::APPLY, &sf.args);
                    // A variable has a name and a type. This is checked
                    // here because code that takes variables apart assumes
                    // the two; other builtin operators applied to the wrong
                    // number of arguments are caught by typing.
                    if self.st.ck.store.kind(app) == Kind::VARIABLE
                        && self.st.ck.store.num_children(app) != 2
                    {
                        return Err(self.lex.parse_error("Expected two arguments to eo::var"));
                    }
                    ret = Some(app);
                    for _ in 0..sf.nscopes {
                        self.st.pop_scope()?;
                    }
                }
                Token::Symbol | Token::QuotedSymbol => {
                    let name = self.token_str_to_symbol(tok)?;
                    let v = self.get_var(&name)?;
                    if self.st.ck.store.kind(v) == Kind::BUILTIN_CONST {
                        return Err(self
                            .lex
                            .parse_error(format!("Cannot use \"{name}\" as a first-class term.")));
                    }
                    ret = Some(v);
                }
                _ => ret = Some(self.parse_literal_token(tok)?),
            }
            // Now set up the frame on top of the stack for the next term:
            // after a term was parsed, or when the frame asked for it.
            while !pstack.is_empty() && (ret.is_some() || needs_update_ctx) {
                needs_update_ctx = false;
                let top = pstack.len() - 1;
                match pstack[top].ctx {
                    ParseCtx::NextArg => {
                        if let Some(t) = ret.take() {
                            pstack[top].args.push(t);
                        }
                    }
                    ParseCtx::LetNextBind => {
                        if let Some(t) = ret.take() {
                            // the term is the value of the last binding
                            if let Some(b) = let_binders.last_mut().and_then(|bs| bs.last_mut()) {
                                b.1 = Some(t);
                            }
                            self.lex.eat_token(Token::Rparen)?;
                        } else {
                            // the opening parenthesis of the bindings
                            self.lex.eat_token(Token::Lparen)?;
                        }
                        if self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
                            // another binding: its value is parsed next
                            let name = self.parse_symbol()?;
                            if let Some(bs) = let_binders.last_mut() {
                                bs.push((name, None));
                            }
                        } else {
                            // the body is parsed next, with the bindings in
                            // scope
                            pstack[top].ctx = ParseCtx::LetBody;
                            pstack[top].nscopes += 1;
                            self.st.push_scope();
                            for (name, value) in let_binders.pop().unwrap_or_default() {
                                if let Some(value) = value {
                                    self.bind(&name, value)?;
                                }
                            }
                        }
                    }
                    ParseCtx::LetBody => {
                        // the body is the value of the let
                        self.lex.eat_token(Token::Rparen)?;
                        let sf = pstack.remove(top);
                        for _ in 0..sf.nscopes {
                            self.st.pop_scope()?;
                        }
                    }
                    ParseCtx::TermAnnotateBody => {
                        let mut attrs = AttrMap::new();
                        self.parse_attribute_list(AttrCtx::Term, ret, &mut attrs, None)?;
                        // attributes on terms are ignored
                        for a in attrs.keys() {
                            let w = self.lex.warning(&format!("Unprocessed attribute {a}"));
                            self.st.print_line(&w);
                        }
                        self.lex.eat_token(Token::Rparen)?;
                        pstack.pop();
                    }
                }
            }
            if pstack.is_empty() {
                break;
            }
        }
        match ret {
            Some(t) => Ok(t),
            // unreachable: the loop ends with a term or an error
            None => Err(self.lex.parse_error("Expected SMT-LIBv2 term")),
        }
    }

    /// Handles the symbol after an opening parenthesis: pushes the frame of
    /// the application. Returns a term when the application was read in
    /// full here, which is the case for `(_ bv<n> <w>)` in reference files.
    fn parse_application_head(
        &mut self,
        tok: Token,
        pstack: &mut Vec<StackFrame>,
    ) -> Result<Option<Term>> {
        let name = self.token_str_to_symbol(tok)?;
        // In reference files (_ f i1 ... in) is an SMT-LIB indexed
        // identifier, the same term as (f i1 ... in). In Eunoia `_` is an
        // application that does not desugar. So the `_` is dropped here.
        if self.is_reference && name == "_" {
            // (_ bv<numeral> <width>) is a bit-vector constant, unless a
            // symbol of that name was declared.
            if self.lex.peek_token()? == Token::Symbol {
                let sym = self.lex.token_str().to_string();
                if let Some(digits) = bit_vector_constant_symbol(&sym)
                    && self.st.get_var(&sym).is_none()
                {
                    self.lex.next_token()?;
                    let w = self.parse_integer_numeral()?;
                    if w == 0 {
                        return Err(self
                            .lex
                            .parse_error("Bit-vector literals must have positive width"));
                    }
                    self.lex.eat_token(Token::Rparen)?;
                    let value = Integer::parse(digits, 10).unwrap_or_else(Integer::zero);
                    let bv = BitVec::new(w, &value);
                    return Ok(Some(self.st.ck.store.mk_lit(Lit::Binary(bv))));
                }
            }
            pstack.push(StackFrame {
                ctx: ParseCtx::NextArg,
                nscopes: 0,
                args: Vec::new(),
            });
            return Ok(None);
        }
        let v = self.get_var(&name)?;
        let mut args = vec![v];
        let mut nscopes = 0;
        // After a binder, a variable list in double parentheses is read and
        // bound here. Otherwise the argument is a term standing for a
        // variable list; no term begins with `((`.
        let ck = self.st.ck.attribute_kind(v);
        if ck == Attr::Binder || ck == Attr::LetBinder {
            let tok = self.lex.next_token()?;
            if tok == Token::Lparen {
                let tok2 = self.lex.peek_token()?;
                self.lex.reinsert_token(Token::Lparen);
                if tok2 == Token::Lparen {
                    nscopes = 1;
                    self.st.push_scope();
                    let vl = if ck == Attr::Binder {
                        let vs = self.parse_and_bind_sorted_var_list(ParamList::Binder)?;
                        if vs.is_empty() {
                            return Err(self
                                .lex
                                .parse_error("Expected non-empty sorted variable list"));
                        }
                        self.st.ck.mk_binder_list(v, &vs)
                    } else {
                        let lls = self.parse_and_bind_let_list()?;
                        if lls.is_empty() {
                            return Err(self.lex.parse_error("Expected non-empty let list"));
                        }
                        self.st.ck.mk_let_binder_list(v, &lls)
                    };
                    if let Some(vl) = vl {
                        args.push(vl);
                    }
                }
            } else {
                self.lex.reinsert_token(tok);
            }
        }
        pstack.push(StackFrame {
            ctx: ParseCtx::NextArg,
            nscopes,
            args,
        });
        Ok(None)
    }

    /// The term for a token that is a term by itself, other than a symbol.
    fn parse_literal_token(&mut self, tok: Token) -> Result<Term> {
        let opts = &self.st.ck.opts;
        let text = self.lex.token_str().to_string();
        let lit = match tok {
            Token::IntegerLiteral => {
                // outside signatures, numerals can be read as rationals
                if !self.is_signature && opts.normalize_numeral {
                    Rational::parse(&text).map(Lit::Rational)
                } else {
                    Integer::parse(&text, 10).map(Lit::Numeral)
                }
            }
            Token::DecimalLiteral => {
                // outside signatures, decimals are read as rationals
                if !self.is_signature && opts.normalize_decimal {
                    Rational::from_decimal(&text).map(Lit::Rational)
                } else {
                    Rational::from_decimal(&text).map(Lit::Decimal)
                }
            }
            Token::RationalLiteral => {
                if let Some(pos) = text.find('/')
                    && text[pos + 1..].bytes().all(|b| b == b'0')
                {
                    return Err(self.lex.parse_error("Expected non-zero denominator"));
                }
                Rational::parse(&text).map(Lit::Rational)
            }
            Token::HexLiteral => {
                // outside signatures, hexadecimals are read as binaries
                let bv = BitVec::parse(&text[2..], 16);
                if !self.is_signature && opts.normalize_hexadecimal {
                    bv.map(Lit::Binary)
                } else {
                    bv.map(Lit::Hex)
                }
            }
            Token::BinaryLiteral => BitVec::parse(&text[2..], 2).map(Lit::Binary),
            Token::StringLiteral => {
                let s = self.unescape_string(&text)?;
                Some(Lit::String(EoString::parse(&s, true)))
            }
            Token::Type => return Ok(self.st.ck.mk_type()),
            Token::BoolType => return Ok(self.st.ck.mk_bool_type()),
            Token::UnterminatedQuotedSymbol => {
                return Err(self.lex.parse_error("Expected SMT-LIBv2 term"));
            }
            _ => {
                return Err(self
                    .lex
                    .unexpected_token_error(tok, "Expected SMT-LIBv2 term"));
            }
        };
        match lit {
            Some(lit) => Ok(self.st.ck.store.mk_lit(lit)),
            // The lexer only makes literal tokens that parse, except for
            // forms like `-/5` that begin with a minus sign; Ethos crashes
            // on those.
            None => Err(self.lex.parse_error(format!("Malformed literal {text}"))),
        }
    }

    /// Parses a type. With `allow_quote_arg`, `(eo::quote x)` is one. A
    /// type must not contain a stuck term and, without `allow_eval`, no
    /// evaluation at all.
    pub(crate) fn parse_type(&mut self, allow_quote_arg: bool, allow_eval: bool) -> Result<Term> {
        if allow_quote_arg {
            let tok = self.lex.next_token()?;
            if tok == Token::Lparen {
                let tok = self.lex.next_token()?;
                if tok == Token::Symbol && self.lex.token_str() == "eo::quote" {
                    let t = self.parse_expr()?;
                    if self.st.ck.store.kind(t) != Kind::PARAM {
                        return Err(self
                            .lex
                            .parse_error("Expected a parameter as argument to eo::quote"));
                    }
                    self.lex.eat_token(Token::Rparen)?;
                    return Ok(self.st.ck.mk_quote_type(t));
                }
                self.lex.reinsert_token(tok);
                self.lex.reinsert_token(Token::Lparen);
            } else {
                self.lex.reinsert_token(tok);
            }
        }
        let e = self.parse_expr()?;
        let ty = self.st.ck.mk_type();
        self.type_check_expected(e, ty)?;
        if self.st.ck.store.is_evaluatable(e) {
            if self.st.ck.store.is_ground(e) {
                return Err(self.lex.parse_error(format!(
                    "Parsed type has an unevalated term:\nType: {}\n",
                    self.st.ck.show(e)
                )));
            } else if !allow_eval {
                return Err(self.lex.parse_error(format!(
                    "Parsed type cannot contain evaluation in this context:\nType: {}\n",
                    self.st.ck.show(e)
                )));
            }
        }
        Ok(e)
    }

    /// Parses a term of type Bool.
    pub(crate) fn parse_formula(&mut self) -> Result<Term> {
        let e = self.parse_expr()?;
        let b = self.st.ck.mk_bool_type();
        self.type_check_expected(e, b)?;
        Ok(e)
    }

    /// Parses `(<term>*)`.
    pub(crate) fn parse_expr_list(&mut self) -> Result<Vec<Term>> {
        self.lex.eat_token(Token::Lparen)?;
        let mut terms = Vec::new();
        loop {
            let tok = self.lex.next_token()?;
            if tok == Token::Rparen {
                return Ok(terms);
            }
            self.lex.reinsert_token(tok);
            terms.push(self.parse_expr()?);
        }
    }

    /// Parses `(<type>*)`. Evaluation is not allowed in the types.
    pub(crate) fn parse_type_list(&mut self, allow_quote_arg: bool) -> Result<Vec<Term>> {
        self.lex.eat_token(Token::Lparen)?;
        let mut terms = Vec::new();
        loop {
            let tok = self.lex.next_token()?;
            if tok == Token::Rparen {
                return Ok(terms);
            }
            self.lex.reinsert_token(tok);
            terms.push(self.parse_type(allow_quote_arg, false)?);
        }
    }

    /// Parses `(<term> <term>)` as a pair.
    pub(crate) fn parse_expr_pair(&mut self) -> Result<Term> {
        self.lex.eat_token(Token::Lparen)?;
        let t1 = self.parse_expr()?;
        let t2 = self.parse_expr()?;
        self.lex.eat_token(Token::Rparen)?;
        Ok(self.st.ck.mk_pair(t1, t2))
    }

    /// Parses `((<term> <term>)*)` as a list of pairs.
    pub(crate) fn parse_expr_pair_list(&mut self) -> Result<Vec<Term>> {
        self.lex.eat_token(Token::Lparen)?;
        let mut terms = Vec::new();
        while self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
            let t1 = self.parse_expr()?;
            let t2 = self.parse_expr()?;
            terms.push(self.st.ck.mk_pair(t1, t2));
            self.lex.eat_token(Token::Rparen)?;
        }
        Ok(terms)
    }

    /// Skips one s-expression.
    pub(crate) fn parse_symbolic_expr(&mut self) -> Result<()> {
        let mut nparen: usize = 0;
        loop {
            match self.lex.next_token()? {
                // Ethos counts in an unsigned integer. No caller starts
                // at a `)`, so the count does not go below zero.
                Token::Lparen => nparen = nparen.wrapping_add(1),
                Token::Rparen => nparen = nparen.wrapping_sub(1),
                Token::Eof => return Err(self.lex.parse_error("Expected s-expression")),
                _ => {}
            }
            if nparen == 0 {
                return Ok(());
            }
        }
    }

    /// Parses `((<symbol> <type> <attribute>*)*)` and binds the symbols.
    /// Returns the parameters that are not marked `:implicit`.
    pub(crate) fn parse_and_bind_sorted_var_list(&mut self, k: ParamList) -> Result<Vec<Term>> {
        let mut amap = Vec::new();
        let vars = self.parse_and_bind_sorted_var_list_attrs(k, &mut amap)?;
        self.process_attribute_maps(&amap)?;
        Ok(vars)
    }

    /// As [`Parser::parse_and_bind_sorted_var_list`], also giving the
    /// attributes read for each parameter, implicit ones included, to
    /// `amap`.
    pub(crate) fn parse_and_bind_sorted_var_list_attrs(
        &mut self,
        k: ParamList,
        amap: &mut Vec<(Term, AttrMap)>,
    ) -> Result<Vec<Term>> {
        let mut var_list = Vec::new();
        self.lex.eat_token(Token::Lparen)?;
        while self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
            let name = self.parse_symbol()?;
            // no eo::quote and no evaluation
            let t = self.parse_type(false, false)?;
            let v;
            let mut is_implicit = false;
            if k == ParamList::Binder {
                v = self.st.ck.get_bound_var(&name, t);
                self.bind(&name, v)?;
            } else {
                // all other parameter lists make fresh parameters
                v = self.st.ck.mk_symbol(SymbolKind::Param, &name, t);
                self.bind(&name, v)?;
                let mut attrs = AttrMap::new();
                self.parse_attribute_list(AttrCtx::Param, Some(v), &mut attrs, Some(k))?;
                if attrs.remove(&Attr::Implicit).is_some() {
                    is_implicit = true;
                }
                amap.push((v, attrs));
            }
            self.lex.eat_token(Token::Rparen)?;
            if !is_implicit {
                var_list.push(v);
            }
        }
        Ok(var_list)
    }

    /// Parses `((<symbol> <term>)*)` for a let-binder. Returns the variable
    /// and the term of each binding; the symbols are bound to the
    /// variables, not to the terms.
    fn parse_and_bind_let_list(&mut self) -> Result<Vec<(Term, Term)>> {
        let mut let_list = Vec::new();
        let mut names = Vec::new();
        self.lex.eat_token(Token::Lparen)?;
        while self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
            let name = self.parse_symbol()?;
            let t = self.parse_expr()?;
            self.lex.eat_token(Token::Rparen)?;
            let tt = self.type_check(t)?;
            let v = self.st.ck.get_bound_var(&name, tt);
            // The symbol is bound under the name of the variable, which is
            // the symbol's name read as a string literal.
            let bound_name = match self.st.ck.store.lit(self.st.ck.store.child(v, 0)) {
                Some(l) => l.to_string(),
                None => name,
            };
            names.push(bound_name);
            let_list.push((v, t));
        }
        for (name, &(v, _)) in names.iter().zip(&let_list) {
            self.bind(name, v)?;
        }
        Ok(let_list)
    }

    /// Parses a symbol, quoted or not, and returns its name.
    pub(crate) fn parse_symbol(&mut self) -> Result<String> {
        let tok = self.lex.next_token()?;
        self.token_str_to_symbol(tok)
    }

    /// Parses `(<symbol>*)`.
    pub(crate) fn parse_symbol_list(&mut self) -> Result<Vec<String>> {
        self.lex.eat_token(Token::Lparen)?;
        let mut symbols = Vec::new();
        loop {
            let tok = self.lex.next_token()?;
            if tok == Token::Rparen {
                return Ok(symbols);
            }
            self.lex.reinsert_token(tok);
            symbols.push(self.parse_symbol()?);
        }
    }

    /// Parses a keyword and returns it without the colon.
    pub(crate) fn parse_keyword(&mut self) -> Result<String> {
        self.lex.eat_token(Token::Keyword)?;
        Ok(self.lex.token_str()[1..].to_string())
    }

    /// Parses a numeral that fits in 32 bits.
    pub(crate) fn parse_integer_numeral(&mut self) -> Result<u32> {
        self.lex.eat_token(Token::IntegerLiteral)?;
        let token = self.lex.token_str();
        if token.len() > 1 && token.starts_with('0') {
            return Err(self
                .lex
                .parse_error("Numeral with leading zeroes are forbidden"));
        }
        let reason = if token.is_empty() || !token.bytes().all(|b| b.is_ascii_digit()) {
            // negative numerals are integer literals too
            "String is not a numeral."
        } else {
            match Integer::parse(token, 10) {
                Some(i) if i.fits_u32() => return Ok(i.to_u32()),
                _ => "Numerals must fit into 32-bit unsigned integers.",
            }
        };
        Err(self
            .lex
            .parse_error(format!("Failed to parse numeral. {reason}")))
    }

    /// The name of the symbol token just read.
    pub(crate) fn token_str_to_symbol(&mut self, tok: Token) -> Result<String> {
        match tok {
            Token::Symbol => Ok(self.lex.token_str().to_string()),
            Token::QuotedSymbol => {
                // without the bars
                match strip_ends(self.lex.token_str()) {
                    Some(name) => Ok(name.to_string()),
                    None => Err(self.lex.parse_error("Malformed quoted symbol")),
                }
            }
            Token::UnterminatedQuotedSymbol => {
                Err(self.lex.parse_error("Expected SMT-LIBv2 symbol"))
            }
            _ => Err(self
                .lex
                .unexpected_token_error(tok, "Expected SMT-LIBv2 symbol")),
        }
    }

    /// Parses a string literal and returns its text, with the quotes if not
    /// `unescape`.
    pub(crate) fn parse_str(&mut self, unescape: bool) -> Result<String> {
        self.lex.eat_token(Token::StringLiteral)?;
        let s = self.lex.token_str().to_string();
        if unescape {
            self.unescape_string(&s)
        } else {
            Ok(s)
        }
    }

    /// Removes the quotes around a string literal and replaces `""` by `"`.
    fn unescape_string(&self, s: &str) -> Result<String> {
        let Some(inner) = strip_ends(s) else {
            return Err(self.lex.parse_error("Malformed string literal"));
        };
        if inner.chars().any(|c| u32::from(c) > 127) {
            return Err(self.lex.parse_error(
                "Extended/unprintable characters are not part of SMT-LIB, and they must be \
                 encoded as escape sequences",
            ));
        }
        let mut out = String::with_capacity(inner.len());
        let mut chars = inner.chars();
        while let Some(c) = chars.next() {
            out.push(c);
            if c == '"' {
                // skip the second quote of the pair
                chars.next();
            }
        }
        Ok(out)
    }

    /// Parses attributes up to the closing parenthesis, which is left
    /// unread. `e` is the term they are on. `plk` is the kind of parameter
    /// list, for attributes on parameters.
    pub(crate) fn parse_attribute_list(
        &mut self,
        k: AttrCtx,
        e: Option<Term>,
        attrs: &mut AttrMap,
        plk: Option<ParamList>,
    ) -> Result<()> {
        while self.lex.eat_token_choice(Token::Keyword, Token::Rparen)? {
            let key = self.lex.token_str().to_string();
            let Some(a) = attr_of_keyword(&key) else {
                // skip the value, if there is one
                let tok = self.lex.peek_token()?;
                if tok != Token::Keyword && tok != Token::Rparen {
                    self.parse_symbolic_expr()?;
                }
                self.st.ck.warn(&format!("Unsupported attribute {key}"));
                // remember that an attribute was read
                attrs.entry(Attr::None).or_default().push(None);
                continue;
            };
            let mut val = None;
            let mut handled = false;
            match k {
                AttrCtx::ProofRule => {
                    if a == Attr::Sorry {
                        handled = true;
                        if let Some(rule) = e {
                            self.st.ck.mark_proof_rule_sorry(rule);
                        }
                    }
                }
                AttrCtx::Param => {
                    if a == Attr::List {
                        // :list is allowed on all parameters and takes
                        // effect at once, so that it holds for the types of
                        // the parameters that follow
                        if let Some(v) = e {
                            self.st.ck.mark_constructor_kind(v, a, None);
                        }
                        continue;
                    }
                    if matches!(plk, Some(ParamList::Const | ParamList::Define)) {
                        handled = true;
                        match a {
                            Attr::Implicit | Attr::Opaque => {}
                            Attr::Restrict => val = Some(self.parse_expr()?),
                            Attr::Syntax => {
                                self.parse_literal_kind()?;
                            }
                            _ => handled = false,
                        }
                    }
                }
                AttrCtx::Const => match a {
                    Attr::RightAssoc | Attr::LeftAssoc => handled = true,
                    Attr::RightAssocNil
                    | Attr::LeftAssocNil
                    | Attr::RightAssocNsNil
                    | Attr::LeftAssocNsNil
                    | Attr::Chainable
                    | Attr::Pairwise
                    | Attr::Binder
                    | Attr::ArgList => {
                        handled = true;
                        val = Some(self.parse_expr()?);
                    }
                    Attr::LetBinder => {
                        handled = true;
                        val = Some(self.parse_expr_pair()?);
                    }
                    _ => {}
                },
                AttrCtx::Define => {
                    if let Some(e) = e {
                        if a == Attr::Type {
                            handled = true;
                            let v = self.parse_expr()?;
                            val = Some(v);
                            self.type_check_expected(e, v)?;
                        } else if a == Attr::IsEq {
                            handled = true;
                            let v = self.parse_expr()?;
                            val = Some(v);
                            if e != v {
                                return Err(self.lex.parse_error(format!(
                                    "Terms are not equal:\nExpression: {}\nTarget expression: \
                                     {}\n",
                                    self.st.ck.show(e),
                                    self.st.ck.show(v)
                                )));
                            }
                        }
                    }
                }
                AttrCtx::Term => {}
            }
            if !handled {
                return Err(self.lex.parse_error(format!("Unhandled attribute {key}")));
            }
            attrs.entry(a).or_default().push(val);
        }
        self.lex.reinsert_token(Token::Rparen);
        Ok(())
    }

    /// Parses the name of a literal kind, e.g. `<numeral>`.
    pub(crate) fn parse_literal_kind(&mut self) -> Result<LitKind> {
        let name = self.parse_symbol()?;
        Ok(match name.as_str() {
            "<boolean>" => LitKind::Boolean,
            "<numeral>" => LitKind::Numeral,
            "<decimal>" => LitKind::Decimal,
            "<rational>" => LitKind::Rational,
            "<hexadecimal>" => LitKind::Hexadecimal,
            "<binary>" => LitKind::Binary,
            "<string>" => LitKind::String,
            _ => return Err(self.lex.parse_error(format!("Unknown literal kind {name}"))),
        })
    }

    /// The term a symbol is bound to; an error if it is not bound.
    pub(crate) fn get_var(&mut self, name: &str) -> Result<Term> {
        match self.st.get_var(name) {
            Some(t) => Ok(t),
            None => Err(self
                .lex
                .parse_error(format!("Could not find symbol {name}"))),
        }
    }

    pub(crate) fn get_proof_rule(&mut self, name: &str) -> Result<Term> {
        let Some(v) = self.st.get_proof_rule(name) else {
            return Err(self
                .lex
                .parse_error(format!("Could not find proof rule {name}")));
        };
        if self.st.ck.store.kind(v) != Kind::PROOF_RULE {
            return Err(self
                .lex
                .parse_error(format!("Expected proof rule for {name}")));
        }
        Ok(v)
    }

    pub(crate) fn bind(&mut self, name: &str, e: Term) -> Result<()> {
        if !self.st.bind(name, e) {
            return Err(self.lex.parse_error(format!(
                "Failed to bind symbol {name}, since the symbol has already been defined"
            )));
        }
        Ok(())
    }

    /// The type of `e`; an error at the current position if it has none.
    pub(crate) fn type_check(&mut self, e: Term) -> Result<Term> {
        if let Some(t) = self.st.ck.get_type(e, None) {
            return Ok(t);
        }
        // The message is only built now that the check has failed.
        let mut msg = String::new();
        self.st.ck.get_type(e, Some(&mut msg));
        Err(self.lex.parse_error(format!(
            "Type checking failed:\nExpression: {}\nMessage: {}\n",
            self.st.ck.show(e),
            msg
        )))
    }

    /// Checks that `e` has type `expected`.
    pub(crate) fn type_check_expected(&mut self, e: Term, expected: Term) -> Result<Term> {
        let et = self.type_check(e)?;
        if et != expected {
            return Err(self.lex.parse_error(format!(
                "Expression of unexpected type:\nExpression: {}\n      Type: {}\n  Expected: \
                 {}\n",
                self.st.ck.show(e),
                self.st.ck.show(et),
                self.st.ck.show(expected)
            )));
        }
        Ok(et)
    }

    /// Checks a case of a program: the parameters of the body occur in the
    /// pattern, and the pattern's arguments contain nothing to evaluate.
    pub(crate) fn type_check_program_pair(&mut self, pat: Term, ret: Term) -> Result<()> {
        let bvs = self.st.ck.get_variables(&[pat]);
        self.ensure_bound(ret, &bvs)?;
        for i in 1..self.st.ck.store.num_children(pat) {
            let arg = self.st.ck.store.child(pat, i);
            if self.st.ck.store.is_evaluatable(arg) {
                return Err(self.lex.parse_error(format!(
                    "Cannot match on evaluatable subterm {}",
                    self.st.ck.show(arg)
                )));
            }
        }
        Ok(())
    }

    /// Checks that a program's type is that of its forward declaration, up
    /// to the names of the parameters.
    pub(crate) fn type_check_program_fwd_decl(
        &mut self,
        prev_prog: Term,
        new_type: Term,
        prog_name: &str,
    ) -> Result<()> {
        let prev_type = self.st.ck.get_type(prev_prog, None);
        if prev_type == Some(new_type) {
            return Ok(());
        }
        if let Some(prev_type) = prev_type {
            let vso = self.st.ck.get_variables(&[prev_type]);
            let vsn = self.st.ck.get_variables(&[new_type]);
            if vso.len() == vsn.len() {
                let ctx = vso.into_iter().zip(vsn).collect();
                if self.st.ck.evaluate(prev_type, &ctx) == new_type {
                    return Ok(());
                }
            }
        }
        Err(self.lex.parse_error(format!(
            "Forward declaration of program {prog_name} had different type."
        )))
    }

    /// A parameter of `e` that is not in `bvs`, other than `eo::self`.
    pub(crate) fn find_free_var(&self, e: Term, bvs: &[Term]) -> Option<Term> {
        let self_param = self.st.ck.mk_self();
        self.st
            .ck
            .get_variables(&[e])
            .into_iter()
            .find(|v| !bvs.contains(v) && *v != self_param)
    }

    fn ensure_bound(&self, e: Term, bvs: &[Term]) -> Result<()> {
        if let Some(v) = self.find_free_var(e, bvs) {
            return Err(self.lex.parse_error(format!(
                "Unexpected free parameter in expression:\n      Expression: {}\n  Free \
                 parameter: {}\nBound parameters: {}\n",
                self.st.ck.show(e),
                self.st.ck.show(v),
                self.st.ck.show_list(bvs, ", ")
            )));
        }
        Ok(())
    }

    /// Gives each parameter the constructor attribute its attribute list
    /// asks for.
    pub(crate) fn process_attribute_maps(&mut self, amap: &[(Term, AttrMap)]) -> Result<()> {
        // Ethos visits the parameters in the order of their addresses;
        // pathos visits them in creation order (design decision 7).
        for (v, attrs) in amap {
            let (ck, cons) = self.process_attribute_map(attrs)?;
            if ck != Attr::None {
                self.st.ck.mark_constructor_kind(*v, ck, cons);
            }
        }
        Ok(())
    }

    /// The constructor attribute in an attribute list, and its term. Other
    /// attributes left in the list, and second constructor attributes, give
    /// warnings.
    pub(crate) fn process_attribute_map(
        &mut self,
        attrs: &AttrMap,
    ) -> Result<(Attr, Option<Term>)> {
        let mut ck = Attr::None;
        let mut cons = None;
        for (&a, vals) in attrs {
            for &av in vals {
                if a.is_constructor_kind() {
                    if ck != Attr::None {
                        let w = self.lex.warning(&format!(
                            "Cannot set multiple constructor types ({ck} and {a})\n"
                        ));
                        self.st.print_line(&w);
                        continue;
                    }
                    // a constructor term with parameters is kept with them
                    cons = match av {
                        Some(av) if !self.st.ck.store.is_ground(av) => {
                            // binder lists are built from the constructors
                            // as they are, so these cannot have parameters
                            if a == Attr::Binder || a == Attr::LetBinder {
                                let which = if a == Attr::Binder {
                                    ":binder"
                                } else {
                                    ":let-binder"
                                };
                                return Err(self.lex.parse_error(format!(
                                    "The constructors given by {which} cannot depend on parameters"
                                )));
                            }
                            let params = self.st.ck.get_variables(&[av]);
                            Some(self.st.ck.mk_parameterized(av, &params))
                        }
                        other => other,
                    };
                    ck = a;
                } else {
                    let w = self.lex.warning(&format!("Unhandled attribute {a}\n"));
                    self.st.print_line(&w);
                }
            }
        }
        Ok((ck, cons))
    }
}

/// The text of a quoted token without its first and last character, as
/// Ethos takes it (`erase(0, 1)`, then `erase(size() - 1, 1)`). The text
/// need not end in its closing quote: it stops at the token's first NUL
/// character (see `Lexer::token_str`). `None` if nothing is left to take
/// the last character from, where Ethos ends with an uncaught exception.
fn strip_ends(s: &str) -> Option<&str> {
    let mut chars = s.chars();
    chars.next();
    chars.next_back()?;
    Some(chars.as_str())
}
