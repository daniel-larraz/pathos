//! The `trim-defs` stage (`plugins/trim_defs/trim_defs.cpp` in Ethos): cuts
//! a signature down to the commands that the targets named by
//! `(echo "trim-defs <symbol>")` need.
//!
//! The stage reads each signature file again as raw S-expressions, notes
//! which symbols each top-level command introduces and which it mentions,
//! and writes out, in source order and as they were written, the commands
//! reachable from the targets.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use pathos_elab::{Plugin, State};
use pathos_syntax::{Error, Result};
use pathos_term::Term;

use crate::std_plugin::{StdPlugin, is_parse_def_name, read_text, rtrim_lines, write_text};

/// A stream of characters, as far as the C++ uses `std::istream`.
struct Chars {
    chars: Vec<char>,
    pos: usize,
    /// Set when a read found nothing left, as the stream's fail bit.
    failed: bool,
}

impl Chars {
    fn new(text: &str) -> Chars {
        Chars {
            chars: text.chars().collect(),
            pos: 0,
            failed: false,
        }
    }

    fn get(&mut self) -> Option<char> {
        let c = self.chars.get(self.pos).copied();
        match c {
            Some(_) => self.pos += 1,
            None => self.failed = true,
        }
        c
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn putback(&mut self) {
        self.pos = self.pos.saturating_sub(1);
    }

    fn skip_line(&mut self) {
        while let Some(c) = self.get() {
            if c == '\n' {
                break;
            }
        }
    }
}

/// `isspace` in the C locale.
fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
}

fn malformed(message: &str, command: Option<&str>) -> Error {
    Error::fatal(match command {
        Some(text) => format!("TrimDefs: malformed command `{text}`: {message}"),
        None => format!("TrimDefs: malformed input: {message}"),
    })
}

/// Reads one token, skipping whitespace and comments. Empty at the end.
fn next_token(input: &mut Chars, command: Option<&str>) -> Result<String> {
    let mut tok = String::new();
    while let Some(c) = input.get() {
        if c == ';' {
            input.skip_line();
            if !tok.is_empty() {
                break;
            }
            continue;
        }
        if is_space(c) {
            if !tok.is_empty() {
                break;
            }
            continue;
        }
        if c == '(' || c == ')' {
            if tok.is_empty() {
                tok.push(c);
            } else {
                input.putback();
            }
            break;
        }
        if c == '"' && tok.is_empty() {
            tok.push(c);
            let mut closed = false;
            while let Some(c) = input.get() {
                tok.push(c);
                if c == '"' {
                    if input.peek() == Some('"') {
                        input.get();
                        tok.push('"');
                    } else {
                        closed = true;
                        break;
                    }
                }
            }
            if !closed {
                return Err(malformed("unterminated string literal", command));
            }
            break;
        }
        if c == '|' && tok.is_empty() {
            tok.push(c);
            let mut closed = false;
            while let Some(c) = input.get() {
                tok.push(c);
                if c == '|' {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return Err(malformed("unterminated quoted symbol", command));
            }
            break;
        }
        tok.push(c);
    }
    Ok(tok)
}

/// Reads one top-level S-expression, from `(` to the matching `)`, with
/// each comment replaced by a newline.
fn read_full_command(input: &mut Chars) -> Result<String> {
    let mut result = String::new();
    let mut depth = 0i64;
    let mut started = false;
    let mut in_string = false;
    let mut in_quoted_symbol = false;
    while let Some(c) = input.get() {
        if !in_string && !in_quoted_symbol && c == ';' {
            input.skip_line();
            result.push('\n');
            continue;
        }
        result.push(c);
        if in_string {
            if c == '"' {
                if input.peek() == Some('"') {
                    input.get();
                    result.push('"');
                } else {
                    in_string = false;
                }
            }
            continue;
        }
        if in_quoted_symbol {
            if c == '|' {
                in_quoted_symbol = false;
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '|' => in_quoted_symbol = true,
            '(' => {
                depth += 1;
                started = true;
            }
            ')' => {
                depth -= 1;
                if depth == 0 && started {
                    break;
                }
            }
            _ => {}
        }
    }
    if depth != 0 || !started || in_string || in_quoted_symbol {
        return Err(malformed("unterminated top-level command", None));
    }
    Ok(result)
}

struct SExpr {
    is_list: bool,
    is_string: bool,
    value: String,
    children: Vec<SExpr>,
}

impl SExpr {
    fn list() -> SExpr {
        SExpr {
            is_list: true,
            is_string: false,
            value: String::new(),
            children: Vec::new(),
        }
    }
}

/// Frees the tree without recursion: a command may nest lists as deep as
/// its text is long.
impl Drop for SExpr {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.children);
        while let Some(mut e) = pending.pop() {
            pending.append(&mut e.children);
        }
    }
}

fn parse_sexpr(text: &str) -> Result<SExpr> {
    let mut input = Chars::new(text);
    // The open lists, the root first. Each is added to its parent when it
    // closes.
    let mut open: Vec<SExpr> = Vec::new();
    loop {
        let tok = next_token(&mut input, Some(text))?;
        if tok.is_empty() {
            return Err(malformed("unexpected end of command", Some(text)));
        }
        if tok == "(" {
            open.push(SExpr::list());
            continue;
        }
        if tok == ")" {
            let Some(closed) = open.pop() else {
                return Err(malformed("unexpected `)`", Some(text)));
            };
            let Some(parent) = open.last_mut() else {
                // the root is closed
                let trailing = next_token(&mut input, Some(text))?;
                if !trailing.is_empty() {
                    return Err(malformed("trailing text after the command", Some(text)));
                }
                return Ok(closed);
            };
            parent.children.push(closed);
            continue;
        }
        let Some(parent) = open.last_mut() else {
            return Err(malformed("expected `(` at the start", Some(text)));
        };
        parent.children.push(SExpr {
            is_list: false,
            is_string: tok.starts_with('"'),
            value: tok,
            children: Vec::new(),
        });
    }
}

fn strip_quoted_symbol(symbol: &str) -> &str {
    if symbol.len() >= 2 && symbol.starts_with('|') && symbol.ends_with('|') {
        &symbol[1..symbol.len() - 1]
    } else {
        symbol
    }
}

fn get_symbol(expr: &SExpr) -> Option<&str> {
    if expr.is_list || expr.is_string || expr.value.is_empty() {
        return None;
    }
    Some(strip_quoted_symbol(&expr.value))
}

fn unescape_string(expr: &SExpr) -> Result<String> {
    let chars: Vec<char> = expr.value.chars().collect();
    if !expr.is_string || chars.len() < 2 {
        return Err(Error::fatal("TrimDefs: invalid internal string token"));
    }
    let n = chars.len() - 1;
    let mut value = String::new();
    let mut i = 1;
    while i < n {
        value.push(chars[i]);
        if chars[i] == '"' && i + 1 < n && chars[i + 1] == '"' {
            i += 1;
        }
        i += 1;
    }
    Ok(value)
}

fn collect_symbols(expr: &SExpr, symbols: &mut HashSet<String>) {
    // an explicit stack: commands can nest deeply
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        if let Some(symbol) = get_symbol(e) {
            symbols.insert(symbol.to_string());
        } else {
            stack.extend(e.children.iter());
        }
    }
}

/// The first symbol of each list in the list `expr`.
fn collect_list_head_symbols(expr: &SExpr, symbols: &mut HashSet<String>) {
    if !expr.is_list {
        return;
    }
    for child in &expr.children {
        if !child.is_list {
            continue;
        }
        if let Some(symbol) = child.children.first().and_then(get_symbol) {
            symbols.insert(symbol.to_string());
        }
    }
}

/// The constructors and selectors a datatype declaration defines, and the
/// parameters it binds.
fn collect_datatype_symbols(
    declaration: &SExpr,
    defined: &mut HashSet<String>,
    bound: &mut HashSet<String>,
) {
    if !declaration.is_list {
        return;
    }
    let mut constructors = declaration;
    if declaration.children.first().and_then(get_symbol) == Some("par") {
        if let Some(params) = declaration.children.get(1)
            && params.is_list
        {
            for param in &params.children {
                if let Some(symbol) = get_symbol(param) {
                    bound.insert(symbol.to_string());
                }
            }
        }
        match declaration.children.get(2) {
            Some(c) => constructors = c,
            None => return,
        }
    }
    if !constructors.is_list {
        return;
    }
    for constructor in &constructors.children {
        if !constructor.is_list || constructor.children.is_empty() {
            continue;
        }
        if let Some(symbol) = get_symbol(&constructor.children[0]) {
            defined.insert(symbol.to_string());
        }
        for selector in &constructor.children[1..] {
            if selector.is_list
                && let Some(symbol) = selector.children.first().and_then(get_symbol)
            {
                defined.insert(symbol.to_string());
            }
        }
    }
}

fn has_sorted_variables(command: &str) -> bool {
    matches!(
        command,
        "define" | "define-fun" | "program" | "declare-rule" | "declare-parameterized-const"
    )
}

/// A top-level command of a signature.
#[derive(Default)]
struct Command {
    name: String,
    /// The symbols it introduces, sorted.
    symbol_names: Vec<String>,
    /// The symbols its body mentions.
    body_syms: HashSet<String>,
    /// Its text, as it is written out.
    full_text: String,
    /// Kept whatever the targets are.
    always_keep: bool,
    /// An instruction to this stage, not part of the output.
    is_trim_directive: bool,
}

/// Parses a command and collects the names it introduces and mentions.
fn parse_command(text: &str) -> Result<Command> {
    let root = parse_sexpr(text)?;
    if !root.is_list || root.children.is_empty() {
        return Err(malformed("expected a non-empty S-expression", Some(text)));
    }
    let Some(name) = get_symbol(&root.children[0]) else {
        return Err(malformed("expected a command name", Some(text)));
    };
    let mut cmd = Command {
        name: name.to_string(),
        full_text: text.to_string(),
        ..Command::default()
    };
    let mut defined = HashSet::new();
    let mut bound = HashSet::new();
    let second = root.children.get(1);
    if cmd.name == "declare-datatype" {
        if let Some(symbol) = second.and_then(get_symbol) {
            defined.insert(symbol.to_string());
        }
        if let Some(declaration) = root.children.get(2) {
            collect_datatype_symbols(declaration, &mut defined, &mut bound);
        }
    } else if cmd.name == "declare-datatypes" {
        if let Some(sorts) = second {
            collect_list_head_symbols(sorts, &mut defined);
        }
        if let Some(declarations) = root.children.get(2)
            && declarations.is_list
        {
            for declaration in &declarations.children {
                collect_datatype_symbols(declaration, &mut defined, &mut bound);
            }
        }
    } else if cmd.name != "echo"
        && cmd.name != "include"
        && let Some(symbol) = second.and_then(get_symbol)
    {
        defined.insert(symbol.to_string());
    }
    if has_sorted_variables(&cmd.name)
        && let Some(vars) = root.children.get(2)
    {
        collect_list_head_symbols(vars, &mut bound);
    }

    collect_symbols(&root, &mut cmd.body_syms);
    cmd.body_syms.remove(&cmd.name);
    for symbol in defined {
        cmd.body_syms.remove(&symbol);
        cmd.symbol_names.push(symbol);
    }
    cmd.symbol_names.sort();
    for symbol in &bound {
        cmd.body_syms.remove(symbol);
    }

    cmd.always_keep = cmd.name == "declare-consts" || cmd.name == "echo";
    if cmd.name == "echo"
        && let Some(message) = second
        && message.is_string
    {
        let msg = unescape_string(message)?;
        cmd.is_trim_directive = msg.starts_with("trim-defs ") || msg.starts_with("trim-defs-cmd ");
        if !msg.starts_with("trim-defs-cmd ") {
            // The words of an echo name the symbols its reader will need;
            // those that name none are dropped when dependencies resolve.
            for word in msg.split(is_space).filter(|w| !w.is_empty()) {
                cmd.body_syms.insert(word.to_string());
            }
        }
    }
    Ok(cmd)
}

/// `eo::x` is `$eo_x` in a desugared signature.
fn normalize_symbol(symbol: &str) -> String {
    match symbol.strip_prefix("eo::") {
        Some(rest) => format!("$eo_{rest}"),
        None => symbol.to_string(),
    }
}

pub struct TrimDefs {
    std: StdPlugin,
    /// The targets named by `trim-defs` echoes.
    def_targets: Vec<String>,
    id_counter: usize,
    sym_to_id: BTreeMap<String, usize>,
    commands: Vec<Command>,
    /// The commands that introduce each symbol.
    sym_commands: BTreeMap<usize, BTreeSet<usize>>,
    /// The symbols each command introduces.
    cmd_defined_syms: Vec<HashSet<usize>>,
    /// The symbols each command mentions.
    cmd_syms: Vec<BTreeSet<usize>>,
    always_keep_cmds: Vec<usize>,
    /// The `define` commands of parse definitions; see `plugins/utils.h`.
    parse_def_cmds: Vec<usize>,
}

impl TrimDefs {
    pub fn new() -> Result<TrimDefs> {
        Ok(TrimDefs::new_in(StdPlugin::new()?))
    }

    fn new_in(std: StdPlugin) -> TrimDefs {
        TrimDefs {
            std,
            def_targets: Vec::new(),
            id_counter: 0,
            sym_to_id: BTreeMap::new(),
            commands: Vec::new(),
            sym_commands: BTreeMap::new(),
            cmd_defined_syms: Vec::new(),
            cmd_syms: Vec::new(),
            always_keep_cmds: Vec::new(),
            parse_def_cmds: Vec::new(),
        }
    }

    /// Reads every top-level command of the text.
    fn parse_commands(&mut self, text: &str) -> Result<()> {
        let mut input = Chars::new(text);
        while !input.failed {
            let tok = next_token(&mut input, None)?;
            if tok == "(" {
                input.putback();
                let full = read_full_command(&mut input)?;
                let cmd = parse_command(&full)?;
                self.process_command(cmd);
            }
        }
        Ok(())
    }

    fn process_command(&mut self, cmd: Command) {
        if cmd.name == "include" || cmd.is_trim_directive {
            return;
        }
        let cid = self.commands.len();
        let mut defined = HashSet::new();
        for symbol in &cmd.symbol_names {
            let id = match self.sym_to_id.get(symbol) {
                Some(&id) => id,
                None => {
                    self.id_counter += 1;
                    self.sym_to_id.insert(symbol.clone(), self.id_counter);
                    self.id_counter
                }
            };
            self.sym_commands.entry(id).or_default().insert(cid);
            defined.insert(id);
        }
        if cmd.always_keep {
            self.always_keep_cmds.push(cid);
        }
        if cmd.name == "define" && cmd.symbol_names.iter().any(|n| is_parse_def_name(n)) {
            self.parse_def_cmds.push(cid);
        }
        self.commands.push(cmd);
        self.cmd_defined_syms.push(defined);
        self.cmd_syms.push(BTreeSet::new());
    }

    /// Turns the symbols each command mentions into the ids of those that
    /// some command introduces.
    fn resolve_dependencies(&mut self) {
        for cid in 0..self.commands.len() {
            let mut dependencies = BTreeSet::new();
            for symbol in &self.commands[cid].body_syms {
                if let Some(&id) = self.sym_to_id.get(&normalize_symbol(symbol))
                    && !self.cmd_defined_syms[cid].contains(&id)
                {
                    dependencies.insert(id);
                }
            }
            self.cmd_syms[cid] = dependencies;
        }
    }
}

impl Plugin for TrimDefs {
    fn finalize_include_file(
        &mut self,
        _st: &mut State,
        path: &str,
        is_signature: bool,
        _is_reference: bool,
        _reference_nf: Option<Term>,
    ) -> Result<()> {
        if !is_signature {
            return Ok(());
        }
        let Some(text) = read_text(path) else {
            return Err(Error::fatal(format!("Couldn't open file: {path}")));
        };
        self.parse_commands(&text)
    }

    fn echo(&mut self, _st: &mut State, msg: &str) -> Result<bool> {
        if let Some(target) = msg.strip_prefix("trim-defs ") {
            self.def_targets.push(target.to_string());
            return Ok(false);
        }
        if let Some(command) = msg.strip_prefix("trim-defs-cmd ") {
            let cmd = parse_command(command)?;
            self.process_command(cmd);
            return Ok(false);
        }
        Ok(true)
    }

    fn finalize(&mut self, st: &mut State) -> Result<()> {
        if self.def_targets.is_empty() {
            return Err(Error::fatal(
                "Must set target with (echo \"trim-defs <symbol>\"), where <symbol> is the name \
                 of the symbol to trim with respect to.\n",
            ));
        }
        self.resolve_dependencies();

        let mut to_visit = Vec::new();
        for dt in &self.def_targets {
            let target = normalize_symbol(strip_quoted_symbol(dt));
            let Some(&id) = self.sym_to_id.get(&target) else {
                return Err(Error::fatal(format!(
                    "Could not find target definition \"{dt}\""
                )));
            };
            to_visit.push(id);
        }

        // The commands kept: those reachable from the targets and from the
        // commands that are always kept.
        let mut retained = BTreeSet::new();
        for &cid in &self.always_keep_cmds {
            if retained.insert(cid) {
                to_visit.extend(self.cmd_syms[cid].iter().copied());
            }
        }
        let mut visited = HashSet::new();
        while let Some(cur) = to_visit.pop() {
            if !visited.insert(cur) {
                continue;
            }
            let Some(commands) = self.sym_commands.get(&cur).filter(|c| !c.is_empty()) else {
                return Err(Error::fatal(
                    "TrimDefs: target symbol has no defining command",
                ));
            };
            for &cid in commands {
                if retained.insert(cid) {
                    to_visit.extend(self.cmd_syms[cid].iter().copied());
                }
            }
        }

        // A parse definition is kept when everything its body mentions is:
        // a symbol is there when one of the commands introducing it is kept.
        loop {
            let mut changed = false;
            for &cid in &self.parse_def_cmds {
                if retained.contains(&cid) {
                    continue;
                }
                let keep = self.cmd_syms[cid].iter().all(|symbol| {
                    (self.sym_commands.get(symbol))
                        .is_some_and(|cmds| cmds.iter().any(|c| retained.contains(c)))
                });
                if keep {
                    retained.insert(cid);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        // In source order: a command may need an earlier one without naming
        // any of its symbols.
        let mut text = String::from("; trim-defs:");
        for dt in &self.def_targets {
            text.push(' ');
            text.push_str(dt);
        }
        text.push_str(&format!("\n; #trim-defs: {}\n", retained.len()));
        for &cid in &retained {
            if self.commands[cid].name == "depends" {
                continue;
            }
            text.push_str(&self.commands[cid].full_text);
            text.push('\n');
        }

        let out_path = self.std.output_path("plugins/trim_defs/trim_gen.eo")?;
        if !write_text(&out_path, &rtrim_lines(&text)) {
            return Err(Error::fatal(format!(
                "TrimDefs: failed to open output {out_path}"
            )));
        }
        st.print_line(&format!("Write trim-defs {out_path}"));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use pathos_check::Options;
    use pathos_elab::include_file;

    use super::*;

    /// Lists nested deeper than the stack could follow are parsed, walked
    /// and freed without recursion, in time linear in the text.
    #[test]
    fn deeply_nested_lists() {
        let depth = 1_000_000;
        let text = format!("{}x{}", "(".repeat(depth), ")".repeat(depth));
        let root = parse_sexpr(&text).unwrap_or_else(|_| panic!("the command is well formed"));
        let mut symbols = HashSet::new();
        collect_symbols(&root, &mut symbols);
        assert!(symbols.contains("x"));
        assert!(parse_sexpr(&text[1..]).is_err());
    }

    #[test]
    fn tokens() {
        let mut input = Chars::new("(a ; note\n \"s \"\"q\"\" (\" |x y|)b");
        let mut toks = Vec::new();
        loop {
            let tok = next_token(&mut input, None).unwrap();
            if tok.is_empty() {
                break;
            }
            toks.push(tok);
        }
        assert_eq!(toks, ["(", "a", "\"s \"\"q\"\" (\"", "|x y|", ")", "b"]);
        assert!(next_token(&mut Chars::new("\"open"), None).is_err());
        assert!(next_token(&mut Chars::new("|open"), None).is_err());
    }

    #[test]
    fn commands() {
        let cmd =
            parse_command("(program $f ((T Type) (x T)) :signature (T) Bool\n ((($f x) (g x))))")
                .unwrap();
        assert_eq!(cmd.name, "program");
        assert_eq!(cmd.symbol_names, ["$f"]);
        let mut body: Vec<&str> = cmd.body_syms.iter().map(String::as_str).collect();
        body.sort();
        assert_eq!(body, [":signature", "Bool", "Type", "g"]);

        let cmd = parse_command(
            "(declare-datatypes ((L 1)) ((par (T) ((nil) (cons (head T) (tail (L T)))))))",
        )
        .unwrap();
        assert_eq!(cmd.symbol_names, ["L", "cons", "head", "nil", "tail"]);
        assert!(!cmd.body_syms.contains("T"));

        let cmd = parse_command("(echo \"trim-defs-cmd (depends a b)\")").unwrap();
        assert!(cmd.is_trim_directive && cmd.always_keep && cmd.body_syms.is_empty());
        let cmd = parse_command("(echo \"lean-meta r :deps a b\")").unwrap();
        assert!(!cmd.is_trim_directive && cmd.body_syms.contains("a"));

        for bad in ["(a", "()", "(\"s\")", "(a) b", "a"] {
            assert!(parse_command(bad).is_err(), "{bad}");
        }
        assert_eq!(normalize_symbol("eo::add"), "$eo_add");
    }

    /// The output is what `ethos-eoc --plugin.trim-defs` writes for the
    /// same files.
    #[test]
    fn trims_a_signature_to_a_rule() {
        let dir = format!("{}/../../target/tmp/trim-defs", env!("CARGO_MANIFEST_DIR"));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            format!("{dir}/sig.eo"),
            "; a small signature
(declare-const Int Type) ; the integers
(declare-consts <numeral> Int)
(declare-const |odd name| Int)
(declare-const unused Int)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(program $flip ((T Type) (x T) (y T)) :signature (Bool) Bool
  ((($flip (= x y)) (= y x))))
(define $parse_two () (eo::add 1 1))
(define $parse_bad () unused)
(declare-rule symm ((F Bool)) :premises (F) :conclusion ($flip F))
(declare-rule other ((F Bool)) :args (F) :conclusion F)
(echo \"kept: |odd name| says \"\"hi\"\"\")
",
        )
        .unwrap();
        std::fs::write(
            format!("{dir}/main.eo"),
            "(include \"sig.eo\")\n(echo \"trim-defs-cmd (depends symm $parse_two)\")\n(echo \
             \"trim-defs symm\")\n",
        )
        .unwrap();

        let printed = Rc::new(RefCell::new(Vec::new()));
        let out = printed.clone();
        let mut st = State::new(
            Options::default(),
            Box::new(|_| ()),
            Box::new(move |l| out.borrow_mut().push(l.to_string())),
        );
        let plugin = TrimDefs::new_in(StdPlugin::with_dirs(&dir, &format!("{dir}/out")));
        st.set_plugin(Box::new(plugin)).unwrap();
        include_file(&mut st, &format!("{dir}/main.eo"), true, false, None).unwrap();
        st.finalize_plugin().unwrap();

        let out_path = format!("{dir}/out/plugins/trim_defs/trim_gen.eo");
        assert_eq!(
            printed.take(),
            [
                "kept: |odd name| says \"hi\"".to_string(),
                format!("Write trim-defs {out_path}")
            ]
        );
        assert_eq!(
            std::fs::read_to_string(out_path).unwrap(),
            "; trim-defs: symm
; #trim-defs: 8
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(program $flip ((T Type) (x T) (y T)) :signature (Bool) Bool
  ((($flip (= x y)) (= y x))))
(define $parse_two () (eo::add 1 1))
(declare-rule symm ((F Bool)) :premises (F) :conclusion ($flip F))
(echo \"kept: |odd name| says \"\"hi\"\"\")
"
        );
    }
}
