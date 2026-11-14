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
| A token's text ends at its first NUL character: an unterminated string `"ab\0cd` is shown as `` `"ab` `` in `Expected ..., got`. | `Lexer::tokenStr` returns a C string. | Probed |
| A `:chainable`, `:pairwise` or `:arg-list` operator whose constructor term cannot be computed is applied to Ethos's null expression, printed `[NONE]`: `(= d)` becomes `([NONE])`. Such a term fails to type check with `Unknown kind NONE`. | `State::mkApplyAttr` uses the null `Expr` without checking it. pathos has the same term (`Kind::Null`). | Probed |
| A failed program application is not tried again in the same evaluation, so `*** Bad number of arguments ...` and `No program defined for ...` appear once per evaluation, not once per occurrence. | `TypeChecker::evaluate` stores the null result in its cache of program applications. | Probed |
| The nil terminator of an operator with a parameterized terminator is found through the operator's type even if that type does not have two arguments: for `(-> T L)` the "second argument type" is the first child of `L`. | `TypeChecker::evaluateNil` asserts the shape only in debug builds. | Probed |
| The binding list of a parameterized `:let-binder` operator is built from the wrong terms: `(myLet ((y true)) y)` with `:let-binder (T @cons)` gives `(_ (eo::tuple T @cons) (_ (_ (eo::tuple T) y) true))`, the parameter tuple taken for the pair constructor and the whole tuple for the list constructor. | `State::mkLetBinderList` asserts only in debug builds that the constructor term is a tuple of two, and takes its first two children; for a parameterized operator it is the term pairing the parameters with the tuple. With fewer than two children Ethos reads past their end; pathos then builds no list. | Probed |

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
| An `eo::` operator evaluated without an argument that it reads, e.g. `(eo::is_eq a)` or `(eo::cons f a)` inside a program body. See below. | Reads past the end of the argument vector | Error `Too few arguments when evaluating literal op <kind>, <n> arguments [<arguments>]` |
| `(eo::var t)`, with one argument | The type rule reads the second child past the end | Type error: `Expected a type for second argument of eo::var`, unless the check of the first argument fails first |
| The nil terminator of an operator whose type is not a function type, or has too few children for the rule above | Reads past the end of the type's children | The terminator is not found |
| `(_ bv<n> 0)` in a reference file | Uncaught exception (empty bit string) | The bit-vector of width 0 |
| `step-pop` when the assumption scope holds no assumption | Reads past the end of a vector | The step fails to check |
| `(eo::nameof (eo::var))`: `eo::var` without arguments makes a variable with no children | Reads the name past the end of the children; a segmentation fault when probed | Error `Too few arguments when evaluating literal op EVAL_NAME_OF, 1 arguments [eo::var]` |
| A quoted symbol or string literal whose text, cut at its first NUL character, is the opening quote alone: `\|\0\|`, `"\0"` | Uncaught C++ exception (`basic_string::erase`) | Error `Malformed quoted symbol` or `Malformed string literal` |
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
whose type runs the program again; it is not the size of a term. Measured with the default 8 MiB stack, in release builds:

| Input | Ethos crashes from | pathos aborts from |
| --- | --- | --- |
| `f<i>` declared with the type `(eo::typeof (f<i-1> x))` | about 4,900 declarations | about 5,900 |
| `f<i>` declared `:pairwise f<i-1>` | about 12,800 | about 20,000 |
| `f<i>.eo` holding `(include "f<i+1>.eo")` | about 236 files | about 9,700 |
| `(declare-consts <numeral> (eo::typeof eo::self))`, then a numeral | always (the recursion has no end) | always |
| A constant `g` of type `(P n)`, where `(P n)` is `(eo::typeof (g (eo::add n -1)))`, applied to 1000000 | crashes | aborts |

So on these shapes every input that stops pathos also crashes Ethos, and
pathos accepts some on which Ethos crashes. A Rust stack overflow is a
controlled abort (the stack has a guard page), not undefined behaviour, but
the run ends without an error message. Making these three iterative is
possible and has not been done; nothing in the corpus nests declarations
more than a few levels.

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
  no reference to it. If Ethos frees a program that has an entry, printing
  the entry reads freed memory, and a later program at the same address
  adds to its count. pathos never reuses a term, so it could not match
  that. Read from `stats.cpp`, not observed: the regressions, the default
  corpus and the large proofs give the same rules, programs and counts.
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
  Ethos crashes (a segmentation fault); pathos reports an error.
