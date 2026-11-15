# Differences from Ethos

Two lists. The first is behaviour of Ethos that looks like a bug and that
pathos reproduces, because pathos must behave exactly like the reference
(see [brief.md](brief.md)). The second is where pathos does not behave like
Ethos.

The reference is Ethos `9217112f`. "Probed" means the behaviour was compared
with the reference binary on a small input; the others follow from reading
the C++.

## Reported to Ethos

What below looks like a bug in Ethos was reported upstream on 2026-11-14,
with a reproducer and the cause in the source: [#257](https://github.com/cvc5/ethos/issues/257), [#258](https://github.com/cvc5/ethos/issues/258), [#259](https://github.com/cvc5/ethos/issues/259), [#260](https://github.com/cvc5/ethos/issues/260), [#261](https://github.com/cvc5/ethos/issues/261), [#262](https://github.com/cvc5/ethos/issues/262), [#263](https://github.com/cvc5/ethos/issues/263), [#264](https://github.com/cvc5/ethos/issues/264), [#265](https://github.com/cvc5/ethos/issues/265), [#266](https://github.com/cvc5/ethos/issues/266), [#267](https://github.com/cvc5/ethos/issues/267), [#268](https://github.com/cvc5/ethos/issues/268). Each row says which. When Ethos fixes one, the drift job
(`docs/evidence.md`, "Keeping up with Ethos") goes red, and pathos follows
the fix in a milestone of its own.

## Ethos behaviour that pathos reproduces

| Behaviour | Where in Ethos | Checked |
| --- | --- | --- |
| After a one-letter keyword such as `:a`, the next character is lost. `(declare-const f T :a)` loses its closing parenthesis. | `Lexer::parseNonEmptyCharList` does not put back the character that ends the list; only keywords ignore its result. Reported: [cvc5/ethos#261](https://github.com/cvc5/ethos/issues/261). | Probed |
| In a file, the byte `0xFF` ends the current token as if the input ended there; reading then continues after it. Not on Linux on arm64, and not on standard input, where `0xFF` is a character like any other (see "By platform"). | The lexer reads a file into a `char` buffer; where `char` is signed, `0xFF` is `-1`, which is `EOF`. Standard input is read with `istream::get`, which gives 255. Reported: [cvc5/ethos#267](https://github.com/cvc5/ethos/issues/267). | Probed, on each platform |
| A file that does not exist gives `Couldn't open file: <path>`, without `Error:`, never `Cannot include file`. | `Filepath::exists` always returns true in the non-Windows build. Reported: [cvc5/ethos#264](https://github.com/cvc5/ethos/issues/264). | Probed |
| Hexadecimal literals print without leading zeros: `#x0f` prints as `#xf`. Only reachable with `--no-normalize-hex` or in signatures. | `BitVector::toString` pads only base 2. Reported: [cvc5/ethos#268](https://github.com/cvc5/ethos/issues/268). | Read |
| Characters below 32 in a string literal are dropped silently, e.g. a newline or a tab. (Bytes above 127 do not get this far: the parser rejects them with `Extended/unprintable characters are not part of SMT-LIB ...`.) | `String::addCharToInternal` builds an error message and discards it: its `throw` is commented out. Reported: [cvc5/ethos#262](https://github.com/cvc5/ethos/issues/262). | Read |
| `(reset)` also unbinds the builtin symbols (`->`, `eo::add`, `true`, ...). | `State::reset` clears the whole symbol table. Reported: [cvc5/ethos#260](https://github.com/cvc5/ethos/issues/260). | Probed |
| A symbol stays marked as overloaded after the scope of its overloads ends. Applying it then warns `No overload found when constructing application`. | `State::popScope` removes the overload list but not the flag in `AppInfo`. | Read; not reproduced (2026-11-14): the flag is set on the inner declaration only, and its name is unbound when the scope ends, so no input was found that applies it again |
| In `step`, `:args` before `:premises` means the premises are not read, and the command then fails on the `:premises` keyword. | `CmdParser` reads the keywords in a fixed order. | Probed |
| `(f a)` for a `:right-assoc` or `:left-assoc` (without nil) `f` is just `a`. | `State::mkApplyAttr` with two children. Reported: [cvc5/ethos#258](https://github.com/cvc5/ethos/issues/258). | Read |
| Including a signature after a `reference` command turns reference checking of assumptions off again. | `State::includeFile` assigns `d_hasReference` on every include. Reported: [cvc5/ethos#259](https://github.com/cvc5/ethos/issues/259). | Read |
| An unmatched `)` while skipping an s-expression makes Ethos read to the end of the input. | `ExprParser::parseSymbolicExpr` counts parentheses in an unsigned integer. | Read |
| A token's text ends at its first NUL character: an unterminated string `"ab\0cd` is shown as `` `"ab` `` in `Expected ..., got`. | `Lexer::tokenStr` returns a C string. | Probed |
| A `:chainable`, `:pairwise` or `:arg-list` operator whose constructor term cannot be computed is applied to Ethos's null expression, printed `[NONE]`: `(= d)` becomes `([NONE])`. Such a term fails to type check with `Unknown kind NONE`. | `State::mkApplyAttr` uses the null `Expr` without checking it. pathos has the same term (`Kind::Null`). | Probed |
| A failed program application is not tried again in the same evaluation, so `*** Bad number of arguments ...` and `No program defined for ...` appear once per evaluation, not once per occurrence. | `TypeChecker::evaluate` stores the null result in its cache of program applications. | Probed |
| The nil terminator of an operator with a parameterized terminator is found through the operator's type even if that type does not have two arguments: for `(-> T L)` the "second argument type" is the first child of `L`. | `TypeChecker::evaluateNil` asserts the shape only in debug builds. | Probed |
| The binding list of a parameterized `:let-binder` operator is built from the wrong terms: `(myLet ((y true)) y)` with `:let-binder (T @cons)` gives `(_ (eo::tuple T @cons) (_ (_ (eo::tuple T) y) true))`, the parameter tuple taken for the pair constructor and the whole tuple for the list constructor. | `State::mkLetBinderList` asserts only in debug builds that the constructor term is a tuple of two, and takes its first two children (reported, with `:let-binder` missing from the manual: [cvc5/ethos#266](https://github.com/cvc5/ethos/issues/266)); for a parameterized operator it is the term pairing the parameters with the tuple. With fewer than two children Ethos reads past their end; pathos then builds no list. | Probed |
| An argument whose type is `(eo::quote n)` rebinds `n`, also when an earlier argument's type already bound it. It shows only on an application that does not evaluate, since a term is typed after it is evaluated: with `:signature ((BitVec n) (eo::quote n)) (BitVec n)`, the single case `((p x 0) x)` and `a` of type `(BitVec 5)`, the application `(p a 7)` matches no case, stays as it is and type-checks with type `(BitVec 7)`; `(h (p a 7))` is then accepted for `h` of type `(-> (BitVec 7) Bool)`. With a case that matches, `(p a 7)` becomes `a`, of type `(BitVec 5)`, before any type is asked for. | `TypeChecker::getTypeAppInternal` assigns `ctx[hdt] = child` for a quoted argument without looking for an existing binding. Found in milestone 19, when the precondition of the verified matching was written down ([verus-spike.md](verus-spike.md)). Not reported. | Probed |

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
| A literal such as `-/5`, which the lexer takes for a rational | Uncaught C++ exception from GMP ([cvc5/ethos#263](https://github.com/cvc5/ethos/issues/263)) | `Malformed literal` error |
| An `eo::` operator evaluated without an argument that it reads, e.g. `(eo::is_eq a)` or `(eo::cons f a)` inside a program body. See below. | Reads past the end of the argument vector ([cvc5/ethos#257](https://github.com/cvc5/ethos/issues/257)) | Error `Too few arguments when evaluating literal op <kind>, <n> arguments [<arguments>]` |
| `(eo::var t)`, with one argument | The type rule reads the second child past the end | Type error: `Expected a type for second argument of eo::var`, unless the check of the first argument fails first |
| The nil terminator of an operator whose type is not a function type, or has too few children for the rule above | Reads past the end of the type's children | The terminator is not found |
| `(_ bv<n> 0)` in a reference file | Uncaught exception (empty bit string; [cvc5/ethos#263](https://github.com/cvc5/ethos/issues/263)) | The bit-vector of width 0 |
| `step-pop` when the assumption scope holds no assumption | Reads past the end of a vector | The step fails to check |
| `(eo::nameof (eo::var))`: `eo::var` without arguments makes a variable with no children | Reads the name past the end of the children; a segmentation fault when probed ([cvc5/ethos#257](https://github.com/cvc5/ethos/issues/257), second comment) | Error `Too few arguments when evaluating literal op EVAL_NAME_OF, 1 arguments [eo::var]` |
| A quoted symbol or string literal whose text, cut at its first NUL character, is the opening quote alone: `\|\0\|`, `"\0"` | Uncaught C++ exception (`basic_string::erase`; [cvc5/ethos#263](https://github.com/cvc5/ethos/issues/263)) | Error `Malformed quoted symbol` or `Malformed string literal` |
| Recursion deeper than the stack: a literal type rule that asks for the type of its own literal (`(declare-consts <numeral> (eo::typeof eo::self))`), a chain of several thousand declarations whose types or constructor terms each use the one before, or includes nested several thousand deep. See below. | Segmentation fault | `thread 'main' has overflowed its stack`, and the process aborts |

#### Operators without an argument they read

An application of an `eo::` operator to the wrong number of arguments is
built with a warning and is rejected if it is type checked. But it can be
evaluated without being type checked, for instance in the body of a program.
Ethos's evaluator reads the arguments an operator needs without looking at
how many there are. What it finds past the end is whatever the memory held
before. In the first fuzzing run, on three inputs of this kind, Ethos crashed
with a segmentation fault, took the missing third argument of `eo::requires`
to be the unrelated term `BitVec`, and took the missing tail of `eo::cons` to
be `@nil`; the same input gave a crash from one working directory and an
error message from another.

pathos ends the run with the error above at the point where Ethos would do
the read, and not before: `(eo::list_find f t)` first checks that `t` is a
list, with Ethos's warnings, and is stuck if it is not. The error is reported
at the end of the command, in place of whatever the command made of the
unfinished evaluation. The reads are those of
`TypeChecker::evaluateLiteralOpInternal`:

- `eo::requires`: the second argument if the first is a value, the third if
  the first two are the same value;
- `eo::is_eq`, `eo::eq`, `eo::cmp`: the second argument if the first is a
  value;
- `eo::nil`: the second argument if the terminator is parameterized;
- the list operators: each argument where the operator's code first uses it.

The alternative, to leave such an application unevaluated, was pathos's
behaviour before. It can run for ever where Ethos crashes: a recursive
program whose `eo::ite` condition is `(eo::is_eq x)` never stops. It can also
accept a proof on which Ethos crashes.

#### Recursion deeper than the stack

pathos walks terms, evaluates programs, matches and prints without
recursion (design decision 8), so the depth of a term or of a program's
calls is not limited by the stack (nor is it in Ethos: both read a term
1,000,000 applications deep). Three recursions remain in pathos, each
where Ethos has the same one:

- typing a term evaluates its type, and evaluating `eo::typeof` types a
  term (`typing.rs` and `eval.rs`);
- building an application of an operator with a constructor term builds the
  constructor term's own application first (`build.rs`);
- an `include` reads the included file inside the command that names it.

Their depth is the length of a chain of declarations or files, or the
number of steps of a program in a type that asks for the type of a term
whose type runs the program again; it is not the size of a term.

How deep they can go depends on the stack. Ethos runs on the main thread,
whose stack is 8 MiB on Linux and macOS (or what `ulimit -s` says) and is
fixed in the executable on Windows (2 MiB as MinGW links it). pathos runs
the checker on a thread of its own with a 64 MiB stack on every platform
(`pathos_elab::on_checker_thread`), so its depths are about the same
everywhere and do not follow `ulimit -s`. The longest chain each gets
through, in release builds, measured by `scripts/platform-probe` in CI
(run 43634777751), to within 2%:

| Platform | `f<i>` of type `(eo::typeof (f<i-1> x))` | `f<i>` declared `:pairwise f<i-1>` | `f<i>.eo` holding `(include "f<i+1>.eo")` |
| --- | --- | --- | --- |
| Linux x86-64 | Ethos 4,800; pathos 47,100 | 12,500; 159,700 | 232; over 20,000 |
| Linux arm64 | 10,240; 45,600 | 23,600; 159,700 | 464; over 20,000 |
| macOS x86-64 | 6,300; 48,600 | 15,600; 153,600 | 236; over 20,000 |
| macOS arm64 | 6,300; 44,000 | 15,600; 159,700 | 236; over 20,000 |
| Windows x86-64 | 1,100; 38,400 | 2,900; 112,600 | 56; over 20,000 |
| Windows arm64 | 780; 41,500 | 1,900; 143,400 | 56; over 20,000 |

(Linux x86-64 is the development machine; the include chain was tried up
to 20,000 files.) Past its depth Ethos dies of a segmentation fault (on
Windows, exception `0xC00000FD`) and prints nothing; pathos prints
`thread 'main' has overflowed its stack` and aborts. Two more shapes have
no depth to measure:

| Input | Ethos | pathos |
| --- | --- | --- |
| `(declare-consts <numeral> (eo::typeof eo::self))`, then a numeral | crashes always (the recursion has no end) | aborts always |
| A constant `g` of type `(P n)`, where `(P n)` is `(eo::typeof (g (eo::add n -1)))`, applied to 1000000 | crashes | aborts |

So on these shapes, on every platform, every input that stops pathos also
crashes Ethos, and pathos accepts many on which Ethos crashes. A Rust stack overflow is a
controlled abort (the stack has a guard page), not undefined behaviour, but
the run ends without an error message. Making these three iterative is
possible and has not been done; nothing in the corpus nests declarations
more than a few levels.

### By platform

Ethos is built for Linux, macOS and Windows, each on x86-64 and arm64, and
it does not behave the same on all six. Where its behaviour is defined,
pathos does on each platform what Ethos does there. CI compares the two on
every one of them (the `tests`, `cli`, `bignum` and `fuzz` gates and
`scripts/platform-probe`; see [evidence.md](evidence.md)).

Ethos behaviour that depends on the platform, and that pathos follows:

| Behaviour | Where | Why, in Ethos | In pathos |
| --- | --- | --- | --- |
| The byte `0xFF` in a file is a character, not the end of the token | Linux arm64 only | C's `char` is unsigned there, so the byte is 255 and not `-1` (`EOF`) | `Lexer::read_next_char` follows `std::ffi::c_char`, which is C's `char` on each target |
| A CR before a LF is not part of the input: positions, string literals and `echo` are as if the file had LF line ends. A CR before anything else stays | Windows | Every stream is opened in text mode, and the C runtime translates | `pathos_syntax::textmode` |
| A Ctrl-Z byte (`0x1A`) ends a file or standard input; what follows is not read | Windows | Text mode again | the same |
| Every line written ends in CR LF: standard output, standard error, and the files the eoc stages write | Windows | Text mode again | the same |
| The file named on the command line or in an `include` is looked up in the file system first and is known from then on by its full name: `Error: D:\dir\sub\f.eo:3.4: ...` where the other platforms print the name as given | Windows | `Filepath` is a `std::filesystem::path` there (`USE_CPP_FILESYSTEM`), and `makeCanonical` is `std::filesystem::canonical` | `path::resolve` |
| Spaces around an include's name are part of the name | Windows | Only the string implementation of `Filepath` trims | the same |
| Both `/` and `\` separate directories, and the same file under two spellings, or in another case, is included once | Windows | `canonical` gives one name per file | the same |
| A directory, or anything else that is not a regular file, gives `Error: cannot include file <name>` on the command line and `Cannot include file <name>` in an `include` command. Elsewhere a directory reads as an empty file | Windows | `Filepath::exists` asks `is_regular_file` there and always answers true elsewhere | the same |
| Without a file argument and with standard input from the null device (a process started without input), the run ends with `Error: no input specified.`; elsewhere it reads an empty proof and answers `correct` | Windows | `isatty` is true for every character device there, not only for a console | `stdin_is_a_terminal` in `crates/pathos/src/main.rs`. Without `unsafe` code pathos cannot ask for the kind of a handle; it takes a handle whose metadata call fails with `ERROR_INVALID_FUNCTION` for a character device, which is what the null device gives on both Windows platforms. A serial port or a printer as standard input was not tried |
| `--include=` with nothing after it gives `Error: cannot include file ` | Windows arm64 only | The C++ library of that build (libc++) makes the empty path canonical without complaint; the one of the x86-64 build (libstdc++) throws (next table) | `path::resolve`, by architecture |

Where Ethos crashes on one platform and pathos reports an error there:

| Input | Where | Ethos | pathos |
| --- | --- | --- | --- |
| A file that does not exist, on the command line, in `--include=`, `--reference=` or an `include` command; also an option Ethos does not know, such as `--nope`, which it takes for a file name | Windows | `std::filesystem::canonical` throws and nothing catches it: `terminate called after throwing an instance of 'std::filesystem::__cxx11::filesystem_error'` (x86-64), `libc++abi: terminating due to uncaught exception ...` (arm64). Reported: [cvc5/ethos#264](https://github.com/cvc5/ethos/issues/264) | `Couldn't open file: <name>`, the message of the other platforms, with the name as it was looked up, and exit status 1. The harness accepts these cases by name (`accepted-run.json`) |
| `--include=` with nothing after it | Windows x86-64 | The same exception (`Invalid argument []`) | `Couldn't open file: ` |

Where pathos does not follow, or cannot tell:

- **Bytes above 127 written to a Windows console.** Ethos writes the
  bytes, and the console shows them in its code page. Rust's standard
  library writes to a console as Unicode and refuses bytes that are not
  UTF-8, so pathos writes such text there with each byte as the Unicode
  character of the same number (`textmode::write`): the same picture as
  Ethos's under a Latin-1 code page, another one under, say, code page 437.
  Bytes that happen to be valid UTF-8 are shown as the characters they
  encode. Matching the code page needs the console API, which pathos
  cannot call without `unsafe` code. Only a console is concerned: to a pipe
  or a file pathos writes the bytes, as Ethos does, and that is what every
  gate compares. Tested with a stand-in for the console, not on one.
- **File names outside Latin-1 on Windows.** Ethos gets its arguments in
  the process's code page and passes them on as bytes. pathos gets them as
  UTF-16 and keeps each unit below 256 as one character
  (`latin1::from_os`), which is the same thing for ASCII and for 0xA0 to
  0xFF under code page 1252; any other character becomes `?`, as Windows
  itself substitutes one that the code page lacks. A file whose name has
  such a character cannot be opened by either. Not probed.
- **`C:name` in an include on Windows** (a drive with a relative path):
  C++'s `/=` keeps the includer's directory when the drive is the same,
  Rust's `PathBuf::push` does not. Not probed.
- **`ulimit -s`.** Ethos gets deeper with a larger stack limit; pathos's
  stack is fixed at 64 MiB (see "Recursion deeper than the stack").

### Size limits

An input can ask for more memory than there is, in both checkers:
`(declare-sort S 4294967295)` (a type constant of that arity), printing a
bit-vector literal of width 2^32 - 1, `(eo::pow 3 4294967295)`, or
`eo::list_repeat` with such a count. pathos then aborts with Rust's `memory
allocation of <n> bytes failed`, or the system kills it; Ethos throws
`std::bad_alloc` or is killed.


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

### Options

- `--stats`, `--stats-all` and `--stats-compact` print Ethos's statistics
  with these numbers pathos's own (the harness masks them):
  - the times;
  - `mkExprCount` and the `#mkExpr` of each rule: how many times the term
    store was asked for a symbol, literal or compound term. pathos builds
    terms in the same places as Ethos but not call for call, so the numbers
    are close to Ethos's and not equal;
  - `newExprCount`, `symCount`, `litCount`: the terms, symbols and distinct
    literals in the store, with the ones pathos makes at start-up (`true`
    and `false` among them, which Ethos does not count);
  - `deleteExprCount`: always 0, since the store never deletes a term.

  Rows are ordered by time and then count, as in Ethos, so their order
  differs from run to run in both. Rows equal in both come in the order
  their symbols were made; in Ethos, in the order of their addresses.
- Ethos keys the statistics by the address of the rule or program and holds
  no reference to it, and printing turns each address back into a term.
  That would read freed memory if a rule or program with an entry were
  freed, but none is: a program's definition, kept in its own `AppInfo`,
  contains the program (its cases apply it), and a rule's likewise, so
  their reference counts never reach zero, not even after `(reset)`.
  Checked on 2026-11-14 with Ethos built with AddressSanitizer, on a rule
  and a program used, then `(reset)`, then new ones used, under `--stats`
  and `--stats-all`: no error, and each entry printed under its own name.
  The regressions, the default corpus and the large proofs give the same
  rules, programs and counts in both.
- The columns of the rule table have fixed widths that a long number
  overflows, in Ethos and in pathos alike: a count of seven digits runs
  into the time after it, and a time of nine digits (100 s or more) into
  the next column. Since the times differ, the two outputs then differ in
  where the digits join. This happens on the two largest proofs
  (`regress3__hole10.cvc`, `regress4__bug143.smtv1`) under `--stats` and
  `--stats-all`; they are not part of gate 9. Since harness a2c80fd the
  harness drops the spaces between masked numbers and masks a count that
  ran into the time, so such rows compare equal; this was checked on rows
  of that shape, not rerun on those two proofs.
- `--write-snapshot=FILE` and `--snapshot=FILE` are pathos's own (signature
  snapshots, milestone 10); Ethos rejects them as unknown options. They are
  not in `--help`, which prints Ethos's text. A run with `--snapshot` prints
  what it would print without it, with these exceptions, all in the numbers
  that are pathos's own under `--stats`: the time of the steps a signature
  itself contains is not counted, and `mkExprCount` continues from the
  count of the run that wrote the snapshot. How a snapshot is used, and
  when it is ignored, is described at the top of
  `crates/pathos-elab/src/snapshot.rs`.
- A snapshot is trusted as the signature is. Its checksum finds damage, not
  forgery: a file made on purpose, with a checksum that fits, can hold
  rules or terms that no signature gives, and so make pathos accept a wrong
  proof, or fail on a term of a shape the parser never builds. Reading such
  a file does not panic and allocates no more than about 40 times its size.
  Checking with it can: the checker indexes the children its own terms
  always have, and a forged snapshot can hold an application without a
  head, or a builtin whose kind is not a compound one. Such a panic is
  memory safe (an index check that failed) and loses only the error
  message. [panics.md](panics.md) lists the places, and
  [evidence.md](evidence.md) puts the question to the developers.
- `--show-config` prints pathos's own name and version.
- `-t` and `-v` fail with `tracing not enabled in this build`, as a release
  build of Ethos does.

### pathos-eoc (the compiler stages)

`pathos-eoc` is `ethos-eoc` (`plugins/main_eoc.cpp`) with all its stages:
`desugar`, `desugar-vc`, `trim-defs`, `model-smt`, `smt-meta`,
`smt-meta-sygus` and `lean-meta`. What differs from the C++:

- `ethos-eoc` falls back on the source and build directories CMake
  compiled into it when `ETHOS_PLUGIN_ROOT` or `ETHOS_PLUGIN_OUTPUT_DIR` is
  not set. `pathos-eoc` has the same fallback, from the environment of its
  own build: build it with `ETHOS_PLUGIN_SOURCE_DIR` (the Ethos source
  tree) and `ETHOS_PLUGIN_OUTPUT_DIR` (`<build directory>/out`) set, as
  `crates/pathos-eoc/src/std_plugin.rs` shows. The environment variables at
  run time take precedence, as in Ethos. A `pathos-eoc` built without them
  has no fallback and fails with Ethos's message (`StdPlugin: unable to
  determine the plugin resource root`, or `... output root`). eoc's driver
  sets neither variable, so a binary the driver runs outside the harness
  must be built with the fallback.
- Where a C++ stage aborts inside a hook, the stage here returns an error,
  which is reported when the command being read ends. Anything the rest of
  that command prints comes before the error, where in Ethos it would not
  be printed at all. Not seen in the eoc gate.
- Hooks raised inside the checker (a constructor kind, a program) reach
  the stage when the parser raises its next hook or the command ends, not
  at once, and what a stage does to the state raises no hooks for the stage
  itself. No eoc stage of the reference changes the state from a hook
  (they make terms and read the symbol table), and `smt-meta`, which prints
  each program when it is told of it, gives the same output. See
  `crates/pathos-elab/src/plugin.rs`.
- Where the C++ indexes a term's children on the strength of an assertion
  (which a release build does not check), the stage stops with `Desugar:
  unexpected term: ...`. Ethos would read outside the term.
- The same for `smt-meta`: `SmtMetaReduce: unexpected term: ...`. Its one
  checked assertion in the C++ (`AlwaysAssert`, on a symbol that is still
  ambiguous after desugaring) is an error here with pathos's own wording.
  Not reached in the gate.
- `model-smt`: the C++'s `failed to read resource` and `failed to write
  output` errors could not be provoked in the reference, so pathos has no
  case for them; a write that fails says `failed to open output`.
- `smt-meta-sygus` orders one map by the addresses of terms
  (`d_grefs` in `smt_meta_sygus.cpp`). The order does not reach the output:
  each entry writes to a grammar of its own, and the grammars they name
  exist by then. pathos visits the entries in the order of their terms.
- `lean-meta`: where the C++ would read outside a term or through a null
  expression (a case head shorter than its program's type, a constant
  without a type, a case without a body), the stage stops with
  `LeanMetaReduce: unexpected term: ...` or `LinearPattern: unexpected
  term: ...`. Its checked assertions (`AlwaysAssert`) print Ethos's text.
  Several of its containers are ordered by address in the C++; none is
  iterated in a way that reaches the output.
- `trim-defs`: `ethos-eoc` overflows its stack on a command nested about
  120,000 parentheses deep; `pathos-eoc` reads it.
- `smt-meta`: on `(echo "smt-meta <name>")` with a name that is not bound,
  or not a program, Ethos crashes (a segmentation fault); pathos reports an
  error. Reported: [cvc5/ethos#265](https://github.com/cvc5/ethos/issues/265).
