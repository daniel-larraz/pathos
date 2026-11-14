# Review: milestone 14, the evidence for replacing Ethos

Reviewed branch `m14` at 48451c4 (commits 1f7fce7 to 48451c4).

## Results, rerun by the reviewer

On the m14 build, with the harness at 6a4fa74 and then at 663289e:

- `scripts/difftest tests --cli`: 268 cases, all the same. `proofs`: 400,
  all the same. `fuzz`: 0 still differ, 36 fixed, 4 accepted, 1 Ethos
  crash. `eoc --filter '/trim-defs(/|$)'`: 827, all the same (the stage
  whose parser changed).
- `cargo test --locked --release`: 0 failures.
- `scripts/difftest bignum` (new, below): 7 cases, all the same.
- `scripts/full-check --quick` with the new harness pin: see the commit
  that adds this review.

## The code changes

The milestone was not meant to change behaviour; the panic audit found
input that reaches panics, and the fixes are small:

- `eo::nameof` of a variable without children: an error where Ethos reads
  past the end. Checked by the reviewer: Ethos segfaults with no output;
  pathos prints "Too few arguments when evaluating literal op
  EVAL_NAME_OF".
- Quoted symbols and strings cut short by a NUL. `strip_ends` drops the
  first and last *character*, where Ethos erases the first and last
  *byte*. Checked by the reviewer that they agree: pathos reads its input
  one byte per character, so `|a\xc3\xa9\0|` names the same symbol, `a\xc3`,
  in both, and `|\xc3\xa9\0|` prints byte for byte the same. `|\0|` and
  `"\0"` end Ethos with an uncaught `std::out_of_range`; pathos reports
  "Malformed quoted symbol" / "Malformed string literal", its own wording,
  which is fine since Ethos has none.
- Wrapping instead of debug-mode overflow in `BitVec::extract`, the
  parenthesis count and the lexer's line number: release output unchanged.
- `trim-defs`: the command parser keeps a stack of open lists instead of a
  path from the root (it was quadratic in the nesting depth), and frees its
  tree without recursion. The error cases map one to one onto the old ones.

## The documents

- `docs/dependencies.md` follows Daniel's decision: option 0, `malachite`
  pinned at `=0.14.0`, `Cargo.lock` unchanged, `--locked` in CI, the
  scripts and `scripts/unsafe-reach`. The soundness table covers every
  reachable item, including the four that emit no instructions of their
  own (the second call site, the two marker impls, `wide`'s zeroed vector).
  The options are measured: option 1 costs nothing on the gates but makes
  large multiplications 45 times slower; option 2 is 32% slower on the
  gates. The status line leaves the signature to Daniel.
- `docs/evidence.md` is the page for the Ethos developers. The reviewer
  filled in the `bignum` row and the fuzzing paragraph and moved the
  harness reference to 663289e.
- `docs/panics.md`: 364 rows. Fable verified the reproducers and the rows
  it changed; the rest were written by its audit subagents and are not
  verified one by one, by Fable or by the reviewer. What is left open is
  listed: 23 rows reachable only from a forged snapshot (the first question
  for the developers), 8 stack rows (recursions Ethos shares, where pathos
  goes deeper), 12 resource rows.

## Added by the reviewer

- **`bignum` gate.** No case of any other gate has numbers large enough to
  reach `malachite`'s FFT multiplication, the only place where reachable
  `unsafe` code runs. The harness's `run --bignum` (`bignum.py`) generates
  7 files of `eo::add`, `mul`, `pow`, `zdiv`, `zmod`, `qdiv`, `to_z`,
  `to_q`, `to_bin`, `len` and the bit-vector operations on operands of 64
  bits to a million bits, each defined with `:is_eq` and a value computed
  by Python, and a last define wrong on purpose so that both checkers
  print a large value in full. Ethos fails each file only at that define;
  pathos's output is the same on all 7; a candidate that changes one digit
  of the printed value differs on all 7. `scripts/difftest bignum` runs
  it; it is in `scripts/full-check` and in CI. Not checked: that these
  cases enter the FFT, by the instrumented build of the method in
  `docs/dependencies.md`. The operands are several times over the
  threshold, and Fable showed inputs of that size do.
- **Harness pin** 663289e: also a memory limit per fuzzing run (`fuzz
  --memory`, default 4 GiB), after a 24-hour campaign died at 53 minutes
  on two mutants that make both checkers allocate without bound.

## Open

- **A difference found by the running fuzzing campaign** (seed 3, finding
  `bf776a04c4f0`): after "Unknown category for parameterized operator" for
  a `:let-binder` whose list constructor is not a list, the type error
  names a different term in pathos than in Ethos. **Fixed** in 8d1e51c:
  Ethos's `mkLetBinderList` takes the first two children of the
  constructor term whatever its kind (the shape is only asserted), which is
  defined behaviour for a parameterized binder; pathos now does the same,
  and builds no list where Ethos would read past the end. Checked by the
  reviewer against `state.cpp:1344`; on 8d1e51c, `scripts/full-check
  --quick` passes and `scripts/difftest eoc` agrees on all 3,507 cases.
- The campaign's other findings so far: six inputs where Ethos reads past
  the end of an `eo::` operator's arguments (a known class, to be accepted
  when the campaign ends), and one both-out-of-memory pair the harness did
  not recognise (fixed in the harness, 8ae0683, not yet pinned).
- Daniel's signature on `docs/dependencies.md`.
