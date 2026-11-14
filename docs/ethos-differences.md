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
- `--show-config` prints pathos's own name and version.
- `-t` and `-v` fail with `tracing not enabled in this build`, as a release
  build of Ethos does.
