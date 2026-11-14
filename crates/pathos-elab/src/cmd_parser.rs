//! Parsing and running commands (`cmd_parser.cpp` in Ethos).

use pathos_check::{Attr, Step};
use pathos_syntax::{Error, Result, Token};
use pathos_term::{Integer, Kind, SymbolKind, Term};

use crate::expr_parser::{AttrCtx, AttrMap, ParamList};
use crate::parser::{Parser, try_include_file};

/// The constructors and selectors read by a datatype declaration.
#[derive(Default)]
struct DatatypeDefs {
    /// Each datatype with its constructors.
    dts: Vec<(Term, Vec<Term>)>,
    /// Each constructor with its selectors.
    dtcons: Vec<(Term, Vec<Term>)>,
    /// The constructors that need a type annotation.
    amb_cons: Vec<Term>,
}

impl Parser<'_> {
    /// The command token for a command name, if it is one in this kind of
    /// input.
    fn command_token(&self, name: &str) -> Option<Token> {
        let common = match name {
            "declare-const" => Some(Token::DeclareConst),
            "declare-datatype" => Some(Token::DeclareDatatype),
            "declare-datatypes" => Some(Token::DeclareDatatypes),
            "declare-sort" => Some(Token::DeclareSort),
            "echo" => Some(Token::Echo),
            "exit" => Some(Token::Exit),
            "set-option" => Some(Token::SetOption),
            "reset" => Some(Token::Reset),
            _ => None,
        };
        if common.is_some() {
            return common;
        }
        if self.is_reference {
            match name {
                "assert" => Some(Token::Assert),
                "declare-fun" => Some(Token::DeclareFun),
                "define-const" => Some(Token::DefineConst),
                "define-fun" => Some(Token::DefineFun),
                "define-sort" => Some(Token::DefineSort),
                "check-sat" => Some(Token::CheckSat),
                "check-sat-assuming" => Some(Token::CheckSatAssuming),
                "reset-assertions" => Some(Token::ResetAssertions),
                "set-logic" => Some(Token::SetLogic),
                "set-info" => Some(Token::SetInfo),
                // Commands that ask the solver for output do not change the
                // assertions; all of them are read and ignored.
                _ if name.starts_with("get-") => Some(Token::Smt2QueryCommand),
                _ => None,
            }
        } else {
            match name {
                "assume" => Some(Token::Assume),
                "assume-push" => Some(Token::AssumePush),
                "declare-consts" => Some(Token::DeclareConsts),
                "declare-parameterized-const" => Some(Token::DeclareParameterizedConst),
                "declare-rule" => Some(Token::DeclareRule),
                "define" => Some(Token::Define),
                "include" => Some(Token::Include),
                "program" => Some(Token::Program),
                "reference" => Some(Token::Reference),
                "step" => Some(Token::Step),
                "step-pop" => Some(Token::StepPop),
                _ => None,
            }
        }
    }

    fn next_command_token(&mut self) -> Result<Token> {
        let tok = self.lex.next_token()?;
        if tok == Token::Symbol
            && let Some(cmd) = self.command_token(self.lex.token_str())
        {
            return Ok(cmd);
        }
        Ok(tok)
    }

    /// Reads and runs the next command. Returns false at the end of the
    /// input.
    pub fn parse_next_command(&mut self) -> Result<bool> {
        let ret = self.run_next_command();
        self.st.flush_plugin_events();
        if let Some(e) = self.st.take_plugin_error() {
            return Err(e);
        }
        // An error that stopped the checker inside the command comes before
        // whatever the command made of the unfinished result.
        if let Some(msg) = self.st.ck.take_fatal() {
            return Err(self.lex.parse_error(msg));
        }
        ret
    }

    fn run_next_command(&mut self) -> Result<bool> {
        if self.finished || self.lex.eat_token_choice(Token::Eof, Token::Lparen)? {
            return Ok(false);
        }
        let tok = self.next_command_token()?;
        match tok {
            Token::Assume | Token::AssumePush => self.cmd_assume(tok == Token::AssumePush)?,
            Token::DeclareConst | Token::DeclareFun | Token::DeclareParameterizedConst => {
                self.cmd_declare_const(tok)?;
            }
            Token::DeclareDatatype | Token::DeclareDatatypes => {
                self.cmd_declare_datatypes(tok == Token::DeclareDatatypes)?;
            }
            Token::DeclareConsts => {
                self.st.push_scope();
                let self_param = self.st.ck.mk_self();
                self.bind("eo::self", self_param)?;
                let k = self.parse_literal_kind()?;
                let t = self.parse_type(false, true)?;
                let mut msg = String::new();
                if !self.st.set_literal_type_rule(k, t, Some(&mut msg)) {
                    return Err(self.lex.parse_error(msg));
                }
                self.st.pop_scope()?;
            }
            Token::DeclareRule => self.cmd_declare_rule()?,
            Token::DeclareSort => {
                let name = self.parse_symbol()?;
                let arity = self.parse_integer_numeral()?;
                let dec_type = self.st.ck.mk_type_constant(&name, arity as usize);
                self.bind(&name, dec_type)?;
            }
            Token::DefineConst | Token::DefineFun | Token::Define => self.cmd_define(tok)?,
            Token::DefineSort => {
                let name = self.parse_symbol()?;
                let snames = self.parse_symbol_list()?;
                let mut vars = Vec::new();
                if !snames.is_empty() {
                    self.st.push_scope();
                    let ttype = self.st.ck.mk_type();
                    for sname in &snames {
                        let v = self.st.ck.mk_symbol(SymbolKind::Param, sname, ttype);
                        self.bind(sname, v)?;
                        vars.push(v);
                    }
                }
                let mut t = self.parse_type(false, true)?;
                if !snames.is_empty() {
                    self.st.pop_scope()?;
                    let vl = self.st.ck.mk_expr(Kind::TUPLE, &vars);
                    t = self.st.ck.mk_expr(Kind::LAMBDA, &[vl, t]);
                }
                self.bind(&name, t)?;
            }
            Token::Echo => {
                // the message is optional
                if self.lex.peek_token()? == Token::StringLiteral {
                    let msg = self.parse_str(true)?;
                    self.st.echo(&msg);
                } else {
                    self.st.echo("");
                }
            }
            Token::Exit => self.finished = true,
            Token::Include | Token::Reference => self.cmd_include(tok == Token::Reference)?,
            Token::Program => self.cmd_program()?,
            Token::Reset => {
                self.st.reset();
                // in reference files this also discards the assertions
                if self.is_reference {
                    self.st.clear_reference_asserts();
                }
            }
            Token::Step | Token::StepPop => self.cmd_step(tok == Token::StepPop)?,
            // ------------------------------------ SMT-LIB reference files
            Token::Assert => {
                let a = self.parse_formula()?;
                self.st.add_reference_assert(a);
            }
            Token::CheckSat => {}
            Token::CheckSatAssuming => {
                // The formulas are part of the query, so a proof may assume
                // them.
                let assumptions = self.parse_expr_list()?;
                let b = self.st.ck.mk_bool_type();
                for a in assumptions {
                    self.type_check_expected(a, b)?;
                    self.st.add_reference_assert(a);
                }
            }
            Token::ResetAssertions => self.st.clear_reference_asserts(),
            Token::Smt2QueryCommand => loop {
                // peek once per iteration, as the lexer requires
                match self.lex.peek_token()? {
                    Token::Rparen => break,
                    Token::Eof => return Err(self.lex.parse_error("Expected s-expression")),
                    _ => self.parse_symbolic_expr()?,
                }
            },
            Token::SetLogic => {
                self.parse_symbol()?;
            }
            Token::SetInfo => {
                self.parse_keyword()?;
                self.parse_symbolic_expr()?;
            }
            Token::SetOption => {
                let key = self.parse_keyword()?;
                // options in reference files are those of the solver
                if !self.is_reference {
                    let mut success = false;
                    if self.lex.peek_token()? == Token::Symbol {
                        let val = self.lex.token_str();
                        if val == "true" || val == "false" {
                            let val = val == "true";
                            success = self.st.ck.opts.set_option(&key, val);
                        }
                    }
                    if !success {
                        self.st
                            .ck
                            .warn(&format!("Unsupported option or value for option {key}"));
                    }
                }
                self.parse_symbolic_expr()?;
            }
            Token::Eof => return Err(self.lex.parse_error("Expected Eunoia command")),
            _ => {
                return Err(self
                    .lex
                    .unexpected_token_error(tok, "Expected Eunoia command"));
            }
        }
        // Terms made after the store filled up are placeholders, so
        // nothing the command computed can be trusted.
        if let Some(limit) = self.st.ck.store.limit_exceeded() {
            return Err(Error::fatal(format!("Term store limit exceeded: {limit}")));
        }
        self.lex.eat_token(Token::Rparen)?;
        Ok(true)
    }

    /// `(assume <symbol> <formula>)` and `(assume-push <symbol> <formula>)`.
    fn cmd_assume(&mut self, is_push: bool) -> Result<()> {
        let name = self.parse_symbol()?;
        let mut proven = self.parse_formula()?;
        self.st
            .with_plugin(|p, st| p.notify_assume(st, &name, &mut proven, is_push));
        if is_push {
            self.st.push_assumption_scope();
        }
        // the name stands for the proof of the formula
        let pt = self.st.ck.mk_proof(proven);
        self.bind(&name, pt)?;
        if !self.st.add_assumption(proven) {
            return Err(self.lex.parse_error(format!(
                "The assumption {name} was not part of the referenced assertions"
            )));
        }
        Ok(())
    }

    /// `(declare-const <symbol> <type> <attr>*)`,
    /// `(declare-fun <symbol> (<type>*) <type>)` and
    /// `(declare-parameterized-const <symbol> (<param>*) <type> <attr>*)`.
    fn cmd_declare_const(&mut self, tok: Token) -> Result<()> {
        let name = self.parse_symbol()?;
        let mut sorts = Vec::new();
        let mut params = Vec::new();
        let mut pattr_map: Vec<(Term, AttrMap)> = Vec::new();
        if tok == Token::DeclareFun {
            sorts = self.parse_type_list(false)?;
        } else if tok == Token::DeclareParameterizedConst {
            self.st.push_scope();
            params = self.parse_and_bind_sorted_var_list_attrs(ParamList::Const, &mut pattr_map)?;
        }
        let ret = self.parse_type(false, true)?;
        let mut ck = Attr::None;
        let mut cons = None;
        if tok != Token::DeclareFun {
            let mut attrs = AttrMap::new();
            self.parse_attribute_list(AttrCtx::Const, None, &mut attrs, None)?;
            (ck, cons) = self.process_attribute_map(&attrs);
        }
        let mut t = self.st.ck.mk_function_type(&sorts, ret);
        let mut opaque_args: Vec<Term> = Vec::new();
        // each explicit parameter becomes an argument, last one first
        for &p in params.iter().rev() {
            let pt = self.type_check(p)?;
            // A parameter that occurs in the type so far must be quoted: the
            // argument itself, not only its type, decides the result type.
            let qt = if self.st.ck.has_variable(t, p) {
                if !self.st.ck.store.is_ground(pt) {
                    return Err(self.lex.parse_error(format!(
                        "Cannot define a type involving a parameter that has non-ground type. \
                         The parameter in question was {}.",
                        self.st.ck.show(p)
                    )));
                }
                self.st.ck.mk_quote_type(p)
            } else {
                pt
            };
            if let Some((_, attrs)) = pattr_map.iter_mut().find(|(v, _)| *v == p)
                && attrs.remove(&Attr::Opaque).is_some()
            {
                opaque_args.insert(0, qt);
                continue;
            }
            if !opaque_args.is_empty() {
                return Err(self
                    .lex
                    .parse_error("Opaque arguments must be a prefix of arguments."));
            }
            t = self.st.ck.mk_function_type(&[qt], t);
        }
        if tok == Token::DeclareParameterizedConst {
            // The function is ambiguous if its return type has a parameter
            // that no argument type determines. It then takes the return
            // type as a first, quoted, argument.
            let (mut arg_types, ret_type) = self.st.ck.get_function_type(t);
            arg_types.extend_from_slice(&opaque_args);
            let pargs = self.st.ck.get_variables(&arg_types);
            if self.find_free_var(ret_type, &pargs).is_some() {
                if ck != Attr::None {
                    return Err(self
                        .lex
                        .parse_error("Ambiguous functions cannot have attributes"));
                } else if !opaque_args.is_empty() {
                    return Err(self
                        .lex
                        .parse_error("Ambiguous functions cannot have opaque arguments"));
                }
                t = self.st.ck.mk_disambiguated_type(ret_type, t, &name);
                ck = Attr::Amb;
            }
        }
        self.process_attribute_maps(&pattr_map)?;
        if !opaque_args.is_empty() {
            if ck != Attr::None {
                return Err(self
                    .lex
                    .parse_error("Can only use opaque argument on functions without attributes."));
            }
            ck = Attr::Opaque;
            // the number of opaque arguments is the constructor term
            cons = Some(self.st.ck.mk_numeral(Integer::from(opaque_args.len())));
            opaque_args.push(t);
            t = self.st.ck.mk_expr(Kind::FUNCTION_TYPE, &opaque_args);
        }
        let v = self.st.ck.mk_symbol(SymbolKind::Const, &name, t);
        if ck != Attr::None && !self.st.ck.mark_constructor_kind(v, ck, cons) {
            return Err(self.lex.parse_error(format!(
                "Failed to mark {} with attribute {}",
                self.st.ck.show(v),
                ck
            )));
        }
        if tok == Token::DeclareParameterizedConst {
            self.st.pop_scope()?;
        }
        self.bind(&name, v)
    }

    /// `(declare-datatype <symbol> <datatype_dec>)` and
    /// `(declare-datatypes (<sort_dec>+) (<datatype_dec>+))`.
    fn cmd_declare_datatypes(&mut self, is_multi: bool) -> Result<()> {
        let mut dnames = Vec::new();
        let mut arities = Vec::new();
        if is_multi {
            self.lex.eat_token(Token::Lparen)?;
            while self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
                let name = self.parse_symbol()?;
                let arity = self.parse_integer_numeral()? as usize;
                dnames.push(name);
                arities.push(arity);
                self.lex.eat_token(Token::Rparen)?;
            }
            if dnames.is_empty() {
                return Err(self.lex.parse_error("Empty list of datatypes"));
            }
            self.lex.eat_token(Token::Lparen)?;
        } else {
            dnames.push(self.parse_symbol()?);
        }
        let mut defs = DatatypeDefs::default();
        if !self.parse_datatypes_def(&dnames, &arities, &mut defs)? {
            return Err(self
                .lex
                .parse_error("Failed to bind symbols for datatype definition"));
        }
        // Ethos marks these in the order of the terms' addresses; the order
        // does not show.
        for (dt, conses) in &defs.dts {
            let ctuple = self.st.ck.mk_list(conses);
            self.st
                .ck
                .mark_constructor_kind(*dt, Attr::Datatype, Some(ctuple));
        }
        for (cons, sels) in &defs.dtcons {
            let ac = if defs.amb_cons.contains(cons) {
                Attr::AmbDatatypeConstructor
            } else {
                Attr::DatatypeConstructor
            };
            let stuple = self.st.ck.mk_list(sels);
            self.st.ck.mark_constructor_kind(*cons, ac, Some(stuple));
        }
        if is_multi {
            self.lex.eat_token(Token::Rparen)?;
        }
        Ok(())
    }

    /// Parses the bodies of the datatypes named `dnames`. `arities` is empty
    /// for `declare-datatype`, whose arity follows from the body. Returns
    /// false if a symbol could not be bound.
    fn parse_datatypes_def(
        &mut self,
        dnames: &[String],
        arities: &[usize],
        defs: &mut DatatypeDefs,
    ) -> Result<bool> {
        // The datatypes are declared first, so that their bodies can refer
        // to each other.
        let mut dtlist = Vec::new();
        for (name, &arity) in dnames.iter().zip(arities) {
            let t = self.st.ck.mk_type_constant(name, arity);
            if !self.st.bind(name, t) {
                return Ok(false);
            }
            dtlist.push(t);
        }
        let mut tok = self.lex.next_token()?;
        let mut i = 0;
        while tok == Token::Lparen {
            let mut params = Vec::new();
            if i >= dnames.len() {
                return Err(self
                    .lex
                    .parse_error("Too many datatypes defined in this block."));
            }
            tok = self.lex.next_token()?;
            let mut pushed_scope = false;
            if tok == Token::Par {
                pushed_scope = true;
                self.st.push_scope();
                let sym_list = self.parse_symbol_list()?;
                if sym_list.is_empty() {
                    return Err(self.lex.parse_error("Expected non-empty parameter list"));
                }
                // the parameters are type variables
                let ty = self.st.ck.mk_type();
                for sym in &sym_list {
                    let t = self.st.ck.mk_symbol(SymbolKind::Param, sym, ty);
                    if !self.st.bind(sym, t) {
                        return Ok(false);
                    }
                    params.push(t);
                }
            } else {
                // the constructor list, in parentheses, is parsed below
                self.lex.reinsert_token(tok);
                self.lex.reinsert_token(Token::Lparen);
            }
            // whether the datatype's name was bound inside the scope of its
            // parameters, and must be bound again after it
            let mut rebind_dt = false;
            if i >= arities.len() {
                let t = self.st.ck.mk_type_constant(&dnames[i], params.len());
                if !self.st.bind(&dnames[i], t) {
                    return Ok(false);
                }
                dtlist.push(t);
                rebind_dt = pushed_scope;
            } else if params.len() != arities[i] {
                return Err(self
                    .lex
                    .parse_error("Wrong number of parameters for datatype."));
            }
            let dt = dtlist[i];
            let mut dti = dt;
            if !params.is_empty() {
                let mut dapp = vec![dt];
                dapp.extend_from_slice(&params);
                dti = self.st.ck.mk_expr(Kind::APPLY, &dapp);
            }
            let mut to_bind = Vec::new();
            if rebind_dt {
                to_bind.push((dnames[i].clone(), dt));
            }
            let conslist =
                self.parse_constructor_definition_list(dti, defs, &mut to_bind, &params)?;
            match defs.dts.iter_mut().find(|(d, _)| *d == dt) {
                Some((_, cs)) => cs.extend(conslist),
                None => defs.dts.push((dt, conslist)),
            }
            if pushed_scope {
                self.lex.eat_token(Token::Rparen)?;
                self.st.pop_scope()?;
            }
            for (name, t) in to_bind {
                if !self.st.bind(&name, t) {
                    return Ok(false);
                }
            }
            tok = self.lex.next_token()?;
            i += 1;
        }
        if dtlist.len() != dnames.len() {
            return Err(self
                .lex
                .unexpected_token_error(tok, "Wrong number of datatypes provided."));
        }
        self.lex.reinsert_token(tok);
        Ok(true)
    }

    /// Parses `((<cons> (<sel> <type>)*)*)` for the datatype `dt`, which is
    /// applied to `params` if it has any. Returns the constructors.
    fn parse_constructor_definition_list(
        &mut self,
        dt: Term,
        defs: &mut DatatypeDefs,
        to_bind: &mut Vec<(String, Term)>,
        params: &[Term],
    ) -> Result<Vec<Term>> {
        let mut conslist = Vec::new();
        self.lex.eat_token(Token::Lparen)?;
        while self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
            let name = self.parse_symbol()?;
            let mut typelist = Vec::new();
            let mut sels = Vec::new();
            while self.lex.eat_token_choice(Token::Lparen, Token::Rparen)? {
                let id = self.parse_symbol()?;
                let t = self.parse_type(false, true)?;
                typelist.push(t);
                let stype = self.st.ck.mk_function_type(&[dt], t);
                let sel = self.st.ck.mk_symbol(SymbolKind::Const, &id, stype);
                to_bind.push((id, sel));
                sels.push(sel);
                self.lex.eat_token(Token::Rparen)?;
            }
            let mut is_amb = false;
            let mut ctype = self.st.ck.mk_function_type(&typelist, dt);
            if !params.is_empty() {
                // A constructor whose arguments do not determine all the
                // parameters is ambiguous: it takes the datatype as a
                // first, quoted, argument.
                let pargs = self.st.ck.get_variables(&typelist);
                if self.find_free_var(dt, &pargs).is_some() {
                    ctype = self.st.ck.mk_disambiguated_type(dt, ctype, &name);
                    is_amb = true;
                }
            }
            let cons = self.st.ck.mk_symbol(SymbolKind::Const, &name, ctype);
            to_bind.push((name, cons));
            conslist.push(cons);
            defs.dtcons.push((cons, sels));
            if is_amb {
                defs.amb_cons.push(cons);
            }
        }
        Ok(conslist)
    }

    /// `(declare-rule <symbol> (<param>*) <keyword-args> <attr>*)`.
    ///
    /// A rule becomes a program from its arguments and the proofs of its
    /// premises to its conclusion. For example
    /// ```text
    /// (declare-rule contra ((F Bool))
    ///   :premises (F (not F))
    ///   :conclusion false)
    /// ```
    /// becomes
    /// ```text
    /// (program $eo_prog_contra ((F Bool))
    ///   :signature (Proof Proof) Bool
    ///   ((($eo_prog_contra (eo::pf F) (eo::pf (not F))) false)))
    /// ```
    fn cmd_declare_rule(&mut self) -> Result<()> {
        if self.st.assumption_level() > 0 {
            return Err(self
                .lex
                .parse_error("Rules must be declared at assumption level zero"));
        }
        self.st.push_scope();
        let name = self.parse_symbol()?;
        self.parse_and_bind_sorted_var_list(ParamList::ProofRule)?;
        let mut assume = None;
        let mut pl_cons = None;
        let mut premises = Vec::new();
        let mut args = Vec::new();
        let mut reqs = Vec::new();
        let mut keyword = self.parse_keyword()?;
        if keyword == "assumption" {
            assume = Some(self.parse_expr()?);
            keyword = self.parse_keyword()?;
        }
        if keyword == "premises" {
            premises = self.parse_expr_list()?;
            keyword = self.parse_keyword()?;
        } else if keyword == "premise-list" {
            // :premise-list <pattern> <cons>: the pattern is the one premise
            let pat = self.parse_expr()?;
            pl_cons = Some(self.parse_expr()?);
            premises.push(pat);
            keyword = self.parse_keyword()?;
        }
        if keyword == "args" {
            args = self.parse_expr_list()?;
            keyword = self.parse_keyword()?;
        }
        if keyword == "requires" {
            reqs = self.parse_expr_pair_list()?;
            keyword = self.parse_keyword()?;
        }
        let conc_explicit = keyword == "conclusion-explicit";
        if keyword != "conclusion" && !conc_explicit {
            return Err(self.lex.parse_error("Expected conclusion in declare-rule"));
        }
        let conc = self.parse_expr()?;
        // What the program matches on: the arguments, the conclusion if
        // explicit, the assumption, then the premises.
        let mut prog_args = args;
        if conc_explicit {
            prog_args.push(conc);
        }
        if let Some(a) = assume {
            prog_args.push(a);
        }
        for e in premises {
            prog_args.push(self.st.ck.mk_proof(e));
        }
        // the requirements guard the conclusion
        let ret = self.st.ck.mk_requires_list(&reqs, conc);
        // The rule symbol itself has type Bool, which is not used.
        let mut pt = self.st.ck.mk_bool_type();
        self.st.pop_scope()?;
        let rule = self.st.ck.mk_symbol(SymbolKind::ProofRule, &name, pt);
        self.type_check(rule)?;
        let rule_prog;
        if prog_args.is_empty() {
            // without arguments and premises, the rule is its conclusion
            rule_prog = ret;
            if !self.st.ck.store.is_ground(ret) || self.st.ck.store.is_evaluatable(ret) {
                return Err(self
                    .lex
                    .parse_error("Nullary proof rule must have ground reduced conclusion"));
            }
        } else {
            let mut prog_types = Vec::with_capacity(prog_args.len());
            let ty = self.st.ck.mk_type();
            for (i, &a) in prog_args.iter().enumerate() {
                if self.st.ck.store.kind(a) == Kind::PROOF {
                    prog_types.push(self.st.ck.mk_proof_type());
                } else {
                    // Arguments may contain parameters and need not type
                    // check, so their types are left open.
                    let et = self
                        .st
                        .ck
                        .mk_symbol(SymbolKind::Param, &format!("$eo_arg_{i}"), ty);
                    prog_types.push(et);
                }
            }
            pt = self.st.ck.mk_program_type(&prog_types, pt);
            rule_prog =
                self.st
                    .ck
                    .mk_symbol(SymbolKind::ProgramConst, &format!("$eo_prog_{name}"), pt);
            prog_args.insert(0, rule_prog);
            let ppat = self.st.ck.mk_expr(Kind::APPLY, &prog_args);
            self.type_check_program_pair(ppat, ret)?;
            let prog_case = self.st.ck.mk_pair(ppat, ret);
            let prog = self.st.ck.mk_expr(Kind::PROGRAM, &[prog_case]);
            self.st.ck.define_program(rule_prog, Some(prog));
        }
        self.bind(&name, rule)?;
        // The premise-list operator is kept even when the rule also takes an
        // assumption or an explicit conclusion; check_step handles all three.
        let tuple = [
            pl_cons.unwrap_or(self.st.ck.mk_any()),
            self.st.ck.mk_bool(assume.is_some()),
            self.st.ck.mk_bool(conc_explicit),
            rule_prog,
        ];
        let attr_val = self.st.ck.mk_expr(Kind::TUPLE, &tuple);
        self.st
            .ck
            .mark_constructor_kind(rule, Attr::ProofRule, Some(attr_val));
        let mut attrs = AttrMap::new();
        self.parse_attribute_list(AttrCtx::ProofRule, Some(rule), &mut attrs, None)
    }

    /// `(define <symbol> (<param>*) <term> <attr>*)`,
    /// `(define-fun <symbol> (<sorted_var>*) <type> <term>)` and
    /// `(define-const <symbol> <type> <term>)`.
    fn cmd_define(&mut self, tok: Token) -> Result<()> {
        self.st.push_scope();
        let name = self.parse_symbol()?;
        let mut pattr_map: Vec<(Term, AttrMap)> = Vec::new();
        // In a reference file, a definition is an assertion that the symbol
        // equals its body, unless the option says to read it as a macro.
        let define_as_reference_assert =
            tok != Token::Define && self.is_reference && !self.st.ck.opts.reference_define_fun;
        let mut vars = Vec::new();
        if tok != Token::DefineConst {
            // Assertions range over variables of the object language;
            // macros need fresh parameters.
            let k = if define_as_reference_assert {
                ParamList::Binder
            } else {
                ParamList::Define
            };
            vars = self.parse_and_bind_sorted_var_list_attrs(k, &mut pattr_map)?;
        }
        if vars.len() < pattr_map.len() {
            // Implicit parameters are not in scope in the body:
            //   (define test ((T Type :implicit) (x T)) T)
            // is rejected, since T is not bound when test is applied.
            self.st.pop_scope()?;
            self.st.push_scope();
            for &e in &vars {
                let sym = self
                    .st
                    .ck
                    .store
                    .symbol_name(e)
                    .unwrap_or_default()
                    .to_string();
                self.st.bind(&sym, e);
            }
        }
        self.process_attribute_maps(&pattr_map)?;
        let ret = if tok != Token::Define {
            Some(self.parse_type(false, true)?)
        } else {
            None
        };
        let mut expr = self.parse_expr()?;
        if let Some(ret) = ret {
            self.type_check_expected(expr, ret)?;
        }
        if define_as_reference_assert {
            // `=` and `lambda` are not builtin: the signature defines them.
            let Some(eq) = self.st.get_var("=") else {
                let cmd = if tok == Token::DefineConst {
                    "define-const."
                } else {
                    "define-fun."
                };
                return Err(self.lex.parse_error(format!(
                    "Expected symbol '=' to be defined when parsing {cmd}"
                )));
            };
            let mut rhs = expr;
            let mut t = ret.unwrap_or(self.st.ck.mk_any());
            if !vars.is_empty() {
                let Some(lambda) = self.st.get_var("lambda") else {
                    return Err(self.lex.parse_error(
                        "Expected symbol 'lambda' to be defined when parsing define-fun.",
                    ));
                };
                let mut largs = vec![lambda];
                largs.extend(self.st.ck.mk_binder_list(lambda, &vars));
                largs.push(rhs);
                rhs = self.st.ck.mk_expr(Kind::APPLY, &largs);
                let mut types = Vec::with_capacity(vars.len());
                for &e in &vars {
                    types.push(self.type_check(e)?);
                }
                t = self.st.ck.mk_function_type(&types, t);
            }
            expr = self.st.ck.mk_symbol(SymbolKind::Const, &name, t);
            let a = self.st.ck.mk_expr(Kind::APPLY, &[eq, expr, rhs]);
            self.st.add_reference_assert(a);
        } else {
            // a macro: a lambda if it has parameters
            if !vars.is_empty() {
                let vl = self.st.ck.mk_expr(Kind::TUPLE, &vars);
                expr = self.st.ck.mk_expr(Kind::LAMBDA, &[vl, expr]);
            }
            if tok == Token::Define {
                let mut attrs = AttrMap::new();
                self.parse_attribute_list(AttrCtx::Define, Some(expr), &mut attrs, None)?;
            }
        }
        self.st.pop_scope()?;
        self.bind(&name, expr)?;
        self.st.define(&name, expr);
        Ok(())
    }

    /// `(include <string>)` and `(reference <string> <term>?)`.
    fn cmd_include(&mut self, is_reference: bool) -> Result<()> {
        if is_reference && self.st.has_reference {
            return Err(self.lex.parse_error("Cannot use more than one reference"));
        }
        if self.st.assumption_level() > 0 {
            return Err(self
                .lex
                .parse_error("Includes must be done at assumption level zero"));
        }
        if self.lex.peek_token()? != Token::StringLiteral {
            return Err(self.lex.parse_error("Expected string literal for include"));
        }
        let file = self.parse_str(true)?;
        // a reference may come with a function that normalizes assertions
        let mut reference_nf = None;
        if is_reference && self.lex.peek_token()? != Token::Rparen {
            reference_nf = Some(self.parse_expr()?);
        }
        // a file that is not a reference is a signature
        if try_include_file(self.st, &file, !is_reference, is_reference, reference_nf)? {
            Ok(())
        } else {
            Err(self.lex.parse_error(format!("Cannot include file {file}")))
        }
    }

    /// `(program <symbol> (<param>*) :signature (<type>+) <type>
    /// ((<pattern> <term>)*)?)`. Without cases this is a forward
    /// declaration.
    fn cmd_program(&mut self) -> Result<()> {
        let name = self.parse_symbol()?;
        self.st.push_scope();
        self.parse_and_bind_sorted_var_list(ParamList::Program)?;
        let mut parsed_sig = false;
        if self.lex.peek_token()? == Token::Keyword {
            parsed_sig = self.parse_keyword()? == "signature";
        }
        if !parsed_sig {
            return Err(self.lex.parse_error("Expected :signature attribute"));
        }
        let arg_types = self.parse_type_list(true)?;
        let ret_type = self.parse_type(false, true)?;
        if arg_types.is_empty() {
            return Err(self
                .lex
                .parse_error("Programs must have at least one argument"));
        }
        let prog_type = self.st.ck.mk_program_type(&arg_types, ret_type);
        // the program may have been declared before
        let pprev = self.st.get_var(&name);
        let pvar = match pprev {
            Some(prev) => {
                if self.st.ck.store.kind(prev) != Kind::PROGRAM_CONST {
                    return Err(self
                        .lex
                        .parse_error(format!("Already declared symbol {name} as a non-program")));
                }
                if self.st.ck.get_program(prev).is_some() {
                    return Err(self.lex.parse_error("Cannot define program more than once"));
                }
                self.type_check_program_fwd_decl(prev, prog_type, &name)?;
                prev
            }
            None => {
                let pvar = self
                    .st
                    .ck
                    .mk_symbol(SymbolKind::ProgramConst, &name, prog_type);
                // bound inside the scope, for the cases
                self.bind(&name, pvar)?;
                pvar
            }
        };
        let mut program = None;
        if self.lex.peek_token()? != Token::Rparen {
            let pchildren = self.parse_expr_pair_list()?;
            for &p in &pchildren {
                let pc = self.st.ck.store.child(p, 0);
                // each case is the program applied to patterns
                if self.st.ck.store.kind(pc) != Kind::APPLY || self.st.ck.store.child(pc, 0) != pvar
                {
                    return Err(self
                        .lex
                        .parse_error("Expected application of program as case"));
                }
                if self.st.ck.store.num_children(pc) != arg_types.len() + 1 {
                    return Err(self.lex.parse_error("Wrong arity for pattern"));
                }
                let rhs = self.st.ck.store.child(p, 1);
                self.type_check_program_pair(pc, rhs)?;
            }
            program = Some(self.st.ck.mk_expr(Kind::PROGRAM, &pchildren));
        }
        self.st.pop_scope()?;
        self.st.ck.define_program(pvar, program);
        if pprev.is_none() {
            // bound again, outside the scope
            self.bind(&name, pvar)?;
        }
        Ok(())
    }

    /// `(step <symbol> <formula>? :rule <symbol> :premises (<term>*)
    /// :args (<term>*))` and the same for `step-pop`.
    fn cmd_step(&mut self, is_pop: bool) -> Result<()> {
        if is_pop && self.st.assumption_level() == 0 {
            return Err(self.lex.parse_error("Cannot pop at level zero"));
        }
        let name = self.parse_symbol()?;
        // the conclusion is optional
        let mut proven = None;
        if self.lex.peek_token()? != Token::Keyword {
            proven = Some(self.parse_formula()?);
        }
        let mut keyword = self.parse_keyword()?;
        if keyword != "rule" {
            return Err(self.lex.parse_error("Expected rule in step"));
        }
        let rule_name = self.parse_symbol()?;
        let rule = self.get_proof_rule(&rule_name)?;
        // A rule counts as used from here on, which decides whether the
        // verdict is "incomplete".
        self.st.ck.step_begins(rule);
        if self.lex.peek_token()? == Token::Keyword {
            keyword = self.parse_keyword()?;
        }
        let mut premises = Vec::new();
        if keyword == "premises" {
            premises = self.parse_expr_list()?;
            if self.lex.peek_token()? == Token::Keyword {
                keyword = self.parse_keyword()?;
            }
        }
        let mut args = Vec::new();
        if keyword == "args" {
            args = self.parse_expr_list()?;
        }
        let step = Step {
            rule,
            proven,
            premises: &premises,
            args: &args,
            is_pop,
            assumption: self.st.first_current_assumption(),
        };
        // A plugin may check the step itself. What it gives must be fully
        // evaluated, or the step fails.
        let by_plugin = |st: &mut crate::State, err: Option<&mut String>| {
            st.with_plugin(|p, st| {
                p.notify_step(st, &name, rule, proven, &premises, &args, is_pop, err)
            })
            .flatten()
            .map(|r| r.result.filter(|&t| !st.ck.store.is_evaluatable(t)))
        };
        let checked = match by_plugin(self.st, None) {
            Some(result) => result,
            None => self.st.ck.check_step(&step, None),
        };
        let Some(conc_term) = checked else {
            // Check again, this time for the reason.
            let mut err = format!("A step of rule {rule_name} failed to check.\n");
            if by_plugin(self.st, Some(&mut err)).is_none() {
                self.st.ck.check_step(&step, Some(&mut err));
            }
            return Err(self.lex.parse_error(err));
        };
        self.st.notify_step_result(is_pop, conc_term);
        let conc_type = self.type_check(conc_term)?;
        if self.st.ck.store.kind(conc_type) != Kind::BoolType {
            return Err(self.lex.parse_error(format!(
                "Non-bool conclusion for step, got {}",
                self.st.ck.show(conc_type)
            )));
        }
        if let Some(proven) = proven
            && conc_term != proven
        {
            return Err(self.lex.parse_error(format!(
                "Unexpected conclusion for rule {}:\n    Proves: {}\n  Expected: {}",
                rule_name,
                self.st.ck.show(conc_term),
                self.st.ck.show(proven)
            )));
        }
        // the conclusion is bound outside the assumption scope
        if is_pop {
            self.st.pop_assumption_scope()?;
        }
        let pf_term = self.st.ck.mk_proof(conc_term);
        self.bind(&name, pf_term)?;
        self.st.ck.step_ends(rule);
        Ok(())
    }
}
