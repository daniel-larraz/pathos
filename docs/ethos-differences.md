# Differences from Ethos

Two lists. The first is behaviour of Ethos that looks like a bug and that
pathos reproduces, because pathos must behave exactly like the reference
(see [brief.md](brief.md)). The second is where pathos does not behave like
Ethos.

The reference is Ethos `9217112f`. "Probed" means the behaviour was compared
with the reference binary on a small input; the others follow from reading
the C++.

## Ethos behaviour that pathos reproduces

| Behaviour | Where in Ethos | Checked |
| --- | --- | --- |
| After a one-letter keyword such as `:a`, the next character is lost. `(declare-const f T :a)` loses its closing parenthesis. | `Lexer::parseNonEmptyCharList` does not put back the character that ends the list; only keywords ignore its result. | Probed |
| The byte `0xFF` ends the current token as if the input ended there; reading then continues after it. | The lexer reads into a signed `char`, so `0xFF` is `-1`, which is `EOF`. | Probed |
| A file that does not exist gives `Couldn't open file: <path>`, without `Error:`, never `Cannot include file`. | `Filepath::exists` always returns true in the non-Windows build. | Probed |
| Hexadecimal literals print without leading zeros: `#x0f` prints as `#xf`. Only reachable with `--no-normalize-hex` or in signatures. | `BitVector::toString` pads only base 2. | Read |
| Characters below 32 or above 127 in a string literal are dropped silently, e.g. a newline or a tab. | `String::addCharToInternal` builds an error message and discards it. | Read |
| `(reset)` also unbinds the builtin symbols (`->`, `eo::add`, `true`, ...). | `State::reset` clears the whole symbol table. | Probed |
| A symbol stays marked as overloaded after the scope of its overloads ends. Applying it then warns `No overload found when constructing application`. | `State::popScope` removes the overload list but not the flag in `AppInfo`. | Read |
| In `step`, `:args` before `:premises` means the premises are not read, and the command then fails on the `:premises` keyword. | `CmdParser` reads the keywords in a fixed order. | Probed |
| `(f a)` for a `:right-assoc` or `:left-assoc` (without nil) `f` is just `a`. | `State::mkApplyAttr` with two children. | Read |
| Including a signature after a `reference` command turns reference checking of assumptions off again. | `State::includeFile` assigns `d_hasReference` on every include. | Read |
| An unmatched `)` while skipping an s-expression makes Ethos read to the end of the input. | `ExprParser::parseSymbolicExpr` counts parentheses in an unsigned integer. | Read |

## Where pathos differs

### Allowed by the harness

- pathos does not print the `Fatal failure within <function> at <file>`
  line, does not abort, and exits with status 1 on any error.
- pathos reads each input file into memory before lexing it.

### Inputs on which Ethos has undefined behaviour or crashes

pathos gives a defined result on these; the harness cannot compare them
meaningfully. None is in the corpus.

| Input | Ethos | pathos |
| --- | --- | --- |
| A literal such as `-/5`, which the lexer takes for a rational | Uncaught C++ exception from GMP | `Malformed literal` error |
| An `eo::` operator applied to too few arguments and then evaluated, e.g. `(eo::requires a)` inside a program body | Reads past the end of the argument vector | The application does not evaluate |
| `(_ bv<n> 0)` in a reference file | Uncaught exception (empty bit string) | The bit-vector of width 0 |
| A `:chainable`, `:pairwise` or `:arg-list` operator whose constructor term cannot be inferred | Builds a term with a null child | Builds the plain application |
| `step-pop` when the assumption scope holds no assumption | Reads past the end of a vector | The step fails to check |

### Size limits

pathos's terms are 32-bit handles. An input that needs more than 2^32 - 1
terms, or more than 2^32 - 1 children of non-binary terms in total, ends with
`Term store limit exceeded: <which>` after the command that hit the limit.
That takes tens of gigabytes of memory. Ethos has no such limit and no such
message; it runs until memory is exhausted.

### Not observed, but possible

- **`eo::hash` and `eo::cmp`.** Ethos numbers terms as `eo::hash` first sees
  them and forgets a term's number when it deletes the term. pathos never
  deletes terms (design decision 2), so a term that Ethos deleted and built
  again keeps its old number in pathos and gets a new, larger one in Ethos.
  A program whose result depends on `eo::cmp` of such a term could behave
  differently. All 630 harness cases agree.
- **Order by address.** Ethos orders some maps by the address of a term;
  pathos orders them by creation (design decision 7). The order shows in the
  `Context [...]` line of type errors and in the order of warnings about
  parameter attributes. On two probes with two and three entries in a
  context the two agreed; presumably Ethos allocated the parameters at
  increasing addresses, which it need not do. Nothing in the harness depends
  on it.

### Options (out of scope for now)

- `--stats`, `--stats-all` and `--stats-compact` are accepted and print
  nothing.
- `--show-config` prints pathos's own name and version.
- `-t` and `-v` fail with `tracing not enabled in this build`, as a release
  build of Ethos does.
