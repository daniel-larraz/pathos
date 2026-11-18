# Panic sites

A Rust panic is a controlled stop: an index out of range, a failed
conversion or an explicit `panic!` ends the program with a message and exit
status 101, without touching memory it should not. It is memory safe, but
on bad input it is still a bug in pathos, because the run ends without the
error message Ethos would print (see "Memory safety" in
[brief.md](brief.md)).

This file lists every place in pathos's non-test code that can panic and
says, for each, why input cannot reach it, or what reaches it. It is the
appendix of [evidence.md](evidence.md).

It is two audits. The last section, "pathos (the CPC checker)", is the
audit of `crates/pathos` at the commit that section names, and a script
checks its rows against that commit. Everything before it is the audit of
the other six crates at commit `cd5face` on branch `m14`, whose line
numbers are that commit's; what later milestones changed is said in notes,
in the rows or beside the tables, and the generated checker that `pathos`
calls (`generated/cpc-checker`) is in neither.

For the audit of `cd5face`: Milestone 15 added `src/thread.rs` to
`pathos-elab` (two rows, with that milestone's line numbers) and moved
lines in the two `main.rs`, `parser.rs`, `path.rs` and `lexer.rs` by a few;
it added no other construct that can panic.
Since then the 23 "Crafted snapshot" rows were closed, and are marked
"Safe (was: crafted snapshot)": the check of a term's shape is in the store
itself (`TermStore::mk` and `TermStore::read_from`, by `NodeKind::takes`),
the checker's snapshot reader checks what it only assumed, and the counters
a snapshot sets wrap. These rows keep their old line numbers, like the
rest.

## What was looked for

In each of the six crates, outside `#[cfg(test)]` modules and `tests/`:
`panic!`, `unreachable!`, `unimplemented!`, `todo!`, `assert!`,
`assert_eq!`, `debug_assert!`, `.expect(`, `.unwrap()`; indexing and
slicing of slices, vectors, arrays, maps and strings; `TermStore::child`,
which indexes a term's children; division; arithmetic on values from the
input that a debug build checks for overflow; `RefCell` borrows; `remove`,
`split_at`, `drain` and the like; writes to a closed stdout; and allocation
sizes taken from the input. Recursion whose depth the input controls and
allocations the input can make arbitrarily large are listed too, although
they end in an abort, not a panic.

The explicit constructs are few: one `panic!` (`TermStore::mk`, for a kind
that has no children), two `unreachable!` (in the evaluator's main loop),
one `debug_assert!` (the Latin-1 encoder), and no `expect`, `unwrap`,
`assert!`, `todo!` or `unimplemented!` anywhere. Nearly every row below is
an index.

## How

Each site was read back to where input enters (the lexer, the parser, the
evaluator, the snapshot reader, the files the eoc stages read), and the
invariant that protects it is given with the line that establishes it.
Reading was backed by runs, on release and debug builds:

- 7,000,000 random calls of the literal operations and the number, bit-vector
  and string parsers; 300,000 mutated term-store images through the
  snapshot reader; 39,000 mutated snapshots with a recomputed checksum;
- 21,000 mutated regression files; every `eo::` operator with 0 to 4
  arguments from a pool of degenerate terms, directly, through a macro and
  through a program (about 83,000 runs); 281 hand-written malformed
  commands; nesting 1,000,000 deep of applications, `let`, annotations and
  program calls;
- for `pathos-eoc`: about 115 hand-written adversarial signatures on all
  seven stages, 4,000 fuzzed definition files for `model-smt`, every
  regression on every stage, and missing or unwritable files and
  directories, each compared with `ethos-eoc`.

## Result

366 rows.

| Verdict | Rows | Meaning |
| --- | --- | --- |
| Safe | 257 | No input reaches it; the row says why. |
| Safe (fixed in this milestone) | 9 | Input reached it; now an error or a defined result. See below. |
| Ethos's fatal error | 51 | `pathos-eoc` only: the place where the C++ stage calls `EO_FATAL` or fails an `AlwaysAssert`. It returns an error with Ethos's text, not a panic. |
| Error where Ethos reads out of bounds | 5 | `pathos-eoc` only: an error with pathos's own text where the C++ would index past a term's children. |
| Safe (was: crafted snapshot) | 16 | Was reached only through a snapshot file made on purpose, with a checksum that fits, holding a state no signature gives. The reader now rejects such a file, or the place cannot fail; each row says which. |
| Safe (was: crafted snapshot, debug build only) | 7 | The same, where only a debug build panicked (a counter read from the snapshot overflowed, or a character above 255 reached the output). |
| Stack | 8 | Recursion whose depth the input controls; the process aborts with `has overflowed its stack`. Ethos crashes on the same inputs. |
| Resource | 13 | Memory or time the input can make arbitrarily large; the process aborts when an allocation fails, or is killed. Ethos behaves alike. |

### Fixed in this milestone

(Since milestone 26, which follows Ethos `c7d3db90`, the first two inputs of this table and the last are errors in Ethos itself, with Ethos's messages in pathos: `Expected two arguments to eo::var`, `Illegal character in quoted symbol`, `Control characters other than whitespace are not permitted in string literals ...`, `Expected Eunoia command`. The `Too few arguments` error and `missing_argument` that this document mentions are gone; the line numbers below are those of the audited commit.)

Found by this audit and fixed in commits `1f7fce7` and `cd5face`, each with
a test except the line number (it needs 4 GiB of input). None is in a case
of any gate.

| Input | Before | Now |
| --- | --- | --- |
| `(eo::nameof (eo::var))` | Panic, index out of bounds, release and debug (Ethos: segmentation fault) | Error `Too few arguments when evaluating literal op EVAL_NAME_OF, 1 arguments [eo::var]` |
| A quoted symbol or string literal holding a NUL character, where the text before the NUL is the opening quote alone (`\|\0\|`, `"\0"`) | Panic, release and debug (Ethos: uncaught exception) | Error `Malformed quoted symbol` or `Malformed string literal` |
| The same with a byte above 127 before the NUL (`\|é\0\|`) | Panic, release and debug; Ethos accepts it | Accepted, as in Ethos |
| `(eo::extract b 0 4294967295)` on a bit-vector of width 2^32 - 1 | Panic in debug builds (overflow); release builds gave Ethos's result | Ethos's result in both |
| `)` and then `(` inside an s-expression being skipped, e.g. `(set-option :x )(` | Panic in debug builds (overflow); release builds gave Ethos's error | Ethos's error in both |
| An input with 2^32 newlines | Overflow of the line number in debug builds (not run) | Wraps, as in release builds |
| `trim-defs` on a command nested 60,000 deep | 11 s (Ethos: 0.02 s), and a stack overflow when the tree was freed with a 1 MiB stack | 0.03 s; 1,000,000 deep in 0.3 s (Ethos crashes from about 120,000) |

### Open

Nothing in the list panics on a signature or proof. Two things remain,
none of them a panic from text input, and one was closed:

1. **Crafted snapshots: closed.** The 23 rows that a forged snapshot (one
   with a checksum that fits) could reach are now safe. The store does not
   hold a term with a number of children that its kind cannot have, made or
   read. The checker's reader checks that a builtin's kind is compound,
   that a program is a list of cases, and that the store begins with the
   checker's own builtin terms; strings must be Latin-1; and the counters
   wrap. Each row says what holds it now, with its test. A forged snapshot
   can still hold a rule that proves anything, as an edited signature file
   can: that is a question of trust, not of panics.
2. **Stack** (8 rows). Three recursions remain, each of which Ethos has
   too: typing a term evaluates its type and `eo::typeof` types a term;
   building an application builds its constructor term's application; an
   include is read inside the command that names it. On every shape tried,
   pathos gets deeper than Ethos before the stack ends
   ([ethos-differences.md](ethos-differences.md), "Recursion deeper than
   the stack").
3. **Resource** (12 rows). `(declare-sort S 4294967295)`, printing a
   bit-vector of width 2^32 - 1, `(eo::pow 3 4294967295)`, `eo::list_repeat`
   with such a count. Ethos has no limit there either.

The `malachite` functions pathos calls panic on a zero divisor and on a
radix outside 2 to 36; the rows for `num.rs` show that every caller rules
those out. Whether `malachite` can panic inside an operation on a very
large number was not established by reading it; the runs above found no
such panic.

## pathos-term

### src/bitvec.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 17 | `value.mod_by_pow2(size)` | Safe | Cannot panic; the result has at most `size` bits. |
| 32-35 | `Integer::parse`, `u32::try_from(..).ok()?`, `checked_mul(4)?` | Safe | Every step is checked; callers pass base 2 or 16 only (`pathos-elab/src/expr_parser.rs:381`, `:388`). |
| 54-56 | `size as usize`, `size - s.len()` | Safe | The subtraction is guarded by `size > s.len()` at `bitvec.rs:55`. |
| 56 | `"0".repeat(size - s.len())` | Resource | Printing a binary literal of width 2^32-1 (from `eo::to_bin`) allocates about 4 GiB; the process runs out of memory without a panic. |
| 68 | `self.size.wrapping_add(other.size)` | Safe | Wraps by design. |
| 69 | `multiply_by_pow2(other.size)` | Resource | The shift amount is a width taken from the input; a non-zero value shifted by 2^32-1 bits takes 512 MiB. |
| 76 | `(high - low).wrapping_add(1)` | Safe (fixed in this milestone) | The count used to be `high - low + 1`, which overflowed in a debug build for width 2^32-1; it now wraps. The `-` is safe because `lit.rs:339` returns when `v1 > v2`. |
| 110, 119 | `floor_div_quotient(&y.value)` | Safe | A zero divisor returns at `bitvec.rs:110-118`. |
| 117 | `self.size - 1` | Safe | Width zero returns at `bitvec.rs:114`. |
| 117 | `one_extend(1, self.size - 1)` | Resource | Builds a value of `size` one bits; 512 MiB for width 2^32-1. |
| 124, 127 | `floor_div_remainder(&y.value)` | Safe | A zero divisor returns at `bitvec.rs:124`. |

### src/codec.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 37 | `u32::try_from(n).unwrap_or(u32::MAX)` | Safe | Saturates instead of unwrapping. |
| 67 | `split_at_checked(n)?` | Safe | Checked split. |
| 73 | `b[0]` | Safe | `bytes(1)` returned exactly one byte (`codec.rs:67`). |
| 86, 91 | `b.try_into().ok()?` | Safe | No unwrap; the slice has the requested length. |
| 99-100 | `as usize`, `checked_mul`, `max(1)` | Safe | Checked; a count is accepted only if the remaining input can hold it. |
| 105 | `std::str::from_utf8(..).ok()` | Safe | No unwrap. |
| 115 | `u128::from(h ^ x) * u128::from(K)` | Safe | Both operands are below 2^64, so the product fits. |
| 124 | `last[..tail.len()].copy_from_slice(tail)` | Safe | `tail` is the remainder of `as_chunks::<8>` (`codec.rs:119`), so it is shorter than 8 and the lengths are equal. |

### src/eostring.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 36 | `Vec::with_capacity(chars.len())` | Safe | The length of a string literal that is already in memory. |
| 39, 60 | `chars[i]` | Safe | Inside `while i < chars.len()` (`eostring.rs:38`, `:59`). |
| 51, 54 | `chars[i]` | Safe | Line 51 tests `i >= chars.len() \|\|` first; line 54 is in its else branch. |
| 97 | `u32::from_str_radix(&hex, 16)` | Safe | The `Result` is matched; `hex` is at most six ASCII hex digits. |
| 135 | `self.0.windows(y.len())` | Safe | `windows(0)` would panic; an empty `y` returns at `eostring.rs:132-134`. |
| 141 | `self.0[start..start + len]` | Safe | The only caller, `lit.rs:359-361`, passes `start = v1.min(vs)` and `len <= vs - start`. |
| 151 | `char::from_u32(c).unwrap_or('?')` | Safe | No unwrap. |

### src/kind.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 229 | `EvalOp::ALL[self as usize].1` | Safe | `ALL` lists every variant in declaration order (asserted by the test at `kind.rs:498-502`); the index is an enum discriminant, never input. |
| 469-472 | `k as u8`, `op as u8` | Safe | Casts of enum discriminants. |
| 476-490 | `ALL.get(i)?` | Safe | Checked lookups. |

### src/lit.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 96, 122, 131, 140, 166, 191-192, 213, 228, 241 | `args.first()?`, `args.get(n)?` | Safe | Checked access. |
| 122, 212 | `.filter(\|e\| e.fits_u32())?.to_u32()` | Safe | `to_u32` is `unwrap_or(0)` (`num.rs:131`) and is reached only when the value fits. |
| 124-125 | `i.pow(exp)`, `r.pow(exp)` | Resource | The exponent of `eo::pow` may be up to 2^32-1; large bases run out of memory or time without a panic. |
| 143-146 | `n.euclidean_qr(d)` | Safe | `d.sgn() == 0` returns `None` at `lit.rs:143`. |
| 157, 159 | `unsigned_div_total`, `unsigned_rem_total` | Safe | Total on a zero divisor (`bitvec.rs:110`, `:124`). |
| 169 | `Rational::from_integers(n, d)` | Safe | Returns `None` for a zero denominator (`num.rs:179`). |
| 173-176 | `n.div(d)` | Safe | `d.sgn() == 0` returns at `lit.rs:173`. |
| 201 | `s.code_points()[0]` | Safe | Match guard `s.len() == 1` at `lit.rs:200`. |
| 214-215 | `BitVec::new(size, ..)` | Safe | Cannot panic; `size` comes from the input but the value is reduced to at most `size` bits. |
| 252-253 | `args[1..]`, `args[0]` | Safe | Private function whose only call (`lit.rs:113`) follows `args.first()?` at `lit.rs:96`. |
| 336-338 | `i1.to_u32()`, `vs - 1`, `i2.to_u32()` | Safe | `lit.rs:333` returns when the width is zero or `i1` exceeds it; `i2.to_u32()` is used only when `i2 <= dsize`. (Since milestone 29, which follows Ethos `b8d65127`, the first returns when `i1` is not below the width, `i1 >= dsize`, and `i2.to_u32()` is used only when `i2 < dsize`.) |
| 344 | `b.extract(v2, v1)` | Safe (fixed in this milestone) | `v2` can equal the width, so for width 2^32-1 the bit count is 2^32; `bitvec.rs:76` now wraps it. (Since milestone 29 an upper index at the width is cut to the last bit, so `v2` is below the width.) |
| 351-360 | `vs - 1`, `v2 + 1 - v1`, `vs - v1.min(vs)`, `st.substr(..)` | Safe | `lit.rs:348` returns for an empty string; `v2 + 1 - v1` is guarded by `v2 >= v1`; the range passed to `substr` is clamped to the length. |
| 372-380 | loop with `remaining.floor_div_quotient(base)` | Safe | `base <= 1` returns at `lit.rs:372`, so the divisor is non-zero and the loop ends. |
| 423 | `LitKind::ALL.get(..)?` | Safe | Checked lookup. |
| 426-431 | `Integer::parse`, `Rational::parse` on snapshot strings | Safe | Both return `None` on anything that is not a number, including non-ASCII text. |
| 433-436 | width check, `BitVec::new(size, &value)` | Safe | A negative value or one wider than `size` is rejected at `lit.rs:433`. |
| 444-445 | `Vec::with_capacity(n)` | Safe | `n` comes from `Reader::len(4)`, so it is at most a quarter of the remaining input. |

### src/num.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 36 | `MInt::from_string_base(base, s)` | Safe | The base is always the constant 2, 10 or 16 (`bitvec.rs:32`, `num.rs:193-206`, `lit.rs:426`, `:431`, `pathos-elab/src/expr_parser.rs:292`, `:360`, `:647`); any string gives `None` or a number. |
| 61, 245 | `pow(u64::from(exp))` | Resource | The exponent is a `u32` from the input (`lit.rs:122`); the result can exceed memory, which aborts or is killed, not a panic. |
| 82, 99-100 | `<< u64::from(..)` | Resource | Shift amounts are bit-vector widths from the input; up to 512 MiB per value. |
| 87, 92-94 | `mod_power_of_2`, `u64 + u64`, `>>` | Safe | The sum of two widened `u32` cannot overflow. |
| 105, 110, 116 | `div_mod(&y.0)` | Safe | Panics on zero, and every caller excludes zero: `bitvec.rs:110`, `:124`, `lit.rs:143`, `lit.rs:372`. |
| 119-120 | `q += MInt::ONE`, `r -= &y.0` | Safe | Arbitrary-precision arithmetic. |
| 126, 131 | `u32::try_from(&self.0)`, `.unwrap_or(0)` | Safe | No unwrap. |
| 182 | `MRat::from_integers_ref(&n.0, &d.0)` | Safe | Panics on a zero denominator, which returns `None` at `num.rs:179`. |
| 204-205 | `dec[..i]`, `dec[i + 1..]` | Safe | `i` is the byte index of the ASCII `.`, so both ends are character boundaries and `i + 1 <= dec.len()`. |
| 207 | `dec.len() - (i + 1)`, `u32::try_from(..).ok()?` | Safe | `i < dec.len()`; the conversion is checked. |
| 208 | `Integer::from(10u32).pow(places)` | Safe | `places` is the number of digits written after the point, so the result is no larger than the input. |
| 241 | `&self.0 / &y.0` | Safe | Panics on zero; the only caller is `lit.rs:176`, guarded at `lit.rs:173`. |

### src/store.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 41, 48 | `u32::try_from(i).ok()`, `unwrap_or(NonZeroU32::MIN)` | Safe | No unwrap. |
| 107, 109 | `vec![0; 1 << bits]`, `64 - bits` | Safe | On 64-bit targets: `bits` is 10 or 6 (`store.rs:280`, `:283`), one more than the current size when growing (`store.rs:155`), or at least 6 and bounded by the snapshot's size (`store.rs:710`, `:682`). |
| 115 | `hash >> self.shift` | Safe | `shift` is at most 58 because `bits` is at least 6. |
| 121 | `self.len * 10`, `self.slots.len() * 7` | Safe | A table has at most 2^33 slots on a 64-bit target. |
| 128, 144 | `self.slots.len() - 1` | Safe | A table has at least 64 slots. |
| 131, 146, 149 | `self.slots[i]` | Safe | `i` starts below the table size (`store.rs:115`) and is masked after each step; the table is never more than 70% full (`store.rs:414`, `:495`), so the probe ends. |
| 304 | `self.nodes.len() - 1` | Safe | `nodes` starts with one entry (`store.rs:276`) and never shrinks. |
| 376, 400, 447 | `self.mk_count += 1` | Safe (was: crafted snapshot, debug build only) | `read_from` installs the snapshot's `mk_count` unchecked (`store.rs:836`); with `u64::MAX` the next term request overflows. From text the counter would need 2^64 requests. **Now the counter wraps (`wrapping_add`); test `the_counter_of_term_requests_wraps`.** |
| 377, 407 | `self.names.len() as u32`, `self.lits.len() as u32` | Safe | Casts; there are no more names or literals than terms, and terms are limited at `store.rs:330`. |
| 387 | `self.types[t.index()]` | Safe | `t` was pushed two lines above. |
| 392-393 | `self.nodes[i]`, `self.lits[id as usize]` | Safe | `i` is a table entry, written only at `store.rs:412` and `:763` with an index that is pushed right after; `id` is `lits.len()` at creation or checked at `store.rs:754`. |
| 412, 493 | `slots[slot] = t.0.get()` | Safe | `slot` is the empty slot returned by `find`. |
| 443 | `panic!("TermStore::mk called with the atomic kind ..")` | Safe (was: crafted snapshot) | `pathos-check/src/snapshot.rs:219-223` accepts a symbol or literal kind as a builtin's `AppInfo.kind`, which `build.rs:219` passes on to `build.rs:200`. From text, that kind is set only from the compound kinds at `pathos-elab/src/state.rs:79-85`. **Now `read_image` rejects a snapshot in which a builtin's kind is not a compound kind; test `a_builtin_of_an_atomic_kind_is_rejected`.** |
| 460 | `self.flags[c.index()]` | Safe (was: crafted snapshot) | `pathos-check/src/snapshot.rs:206-210` compares the builtin term ids as numbers without requiring them to be terms of the snapshot's store, and `install` keeps the old handles. From text every handle comes from the one store. **Now `read_image` rejects a snapshot whose store does not begin with the checker's own terms up to the last builtin one (`same_first_terms`), and every other term read (`read_term`, `read_opt_term`) is checked to be one of that store; tests `a_store_without_the_builtin_terms_is_rejected` and `a_store_with_other_terms_in_place_of_the_builtin_ones_is_rejected`.** |
| 470-473 | `u32::try_from(..).ok()`, `checked_add` | Safe | Checked; a full child pool sets `Limit::Children`. |
| 506, 521, 533, 549, 565, 573, 582, 588, 595, 601 | `nodes` / `types` / `flags[t.index()]` | Safe (was: crafted snapshot) | Same unchecked property as line 460: a snapshot store smaller than the checker's builtin ids leaves those handles out of range. Line 460 was the one observed. **Now `read_image` rejects a snapshot whose store does not begin with the checker's own terms up to the last builtin one (`same_first_terms`), and every other term read (`read_term`, `read_opt_term`) is checked to be one of that store; tests `a_store_without_the_builtin_terms_is_rejected` and `a_store_with_other_terms_in_place_of_the_builtin_ones_is_rejected`.** |
| 524 | `child_pool[a.start as usize..(a.start + a.len) as usize]` | Safe | `mk` stores only ranges whose end fits `u32` (`store.rs:473`); `read_from` requires `a + b <= pool.len()` (`store.rs:775-776`) with a 32-bit pool length (`store.rs:692`). |
| 560 | `self.children_at(t.index())[i]` | Safe (was: crafted snapshot) | `read_from` checks that a store is well formed, not that terms have the shape the checker builds, so a program whose case is not a pair reaches `pathos-check/src/eval.rs:298`. From text, callers check the arity or take terms built with a fixed one; the one that did not (`eo::nameof` on `(eo::var)`) was fixed in 1f7fce7. **Now `read_image` rejects a snapshot with a program that is not a list of cases, each a pair whose first element has a head (`is_program_term`); test `a_program_that_is_not_a_list_of_cases_is_rejected`.** |
| 566, 574 | `self.lits[id as usize]`, `self.names[id as usize]` | Safe | The ids are the vector lengths at creation (`store.rs:377`, `:407`) or checked in `read_from` (`store.rs:741`, `:754`, `:823`). |
| 634-650 | `self.nodes[i]`, `self.types[i]` | Safe | `i` ranges over `1..self.nodes.len()`, and the vectors grow together (`store.rs:334-336`). |
| 688, 693, 698 | `Vec::with_capacity(n)`, `(pool_len)`, `(names_len)` | Safe | Each count comes from `Reader::len` with the item's minimum size, so the allocation is a small multiple of the input. |
| 703 | `Vec::with_capacity(lits_len)` | Resource | `lits_len` may be half the remaining bytes and a `Lit` takes 64 bytes, so the allocation can be about 32 times the snapshot's size. |
| 710-712 | `(items * 2).next_power_of_two()`, `ConsTable::with_bits(..)` | Safe | `items` is bounded by the input's size (`store.rs:682`, `:702`). |
| 713-715 | `n - fixed` | Safe | `n < s.len()` returns at `store.rs:684`. |
| 722, 833 | `i + 1` | Safe | `i < n`, a count bounded by the input. |
| 726 | `s.nodes[index]` | Safe | Inside `if index <= fixed`. |
| 740, 753, 785, 788 | `ALL.get(sub_index)?` | Safe | Checked lookups. |
| 757 | `s.lits[next_lit]` | Safe | `s.lits.get(next_lit)?` on line 754. |
| 763, 815 | `slots[slot] = u32::try_from(index).ok()?` | Safe | `slot` comes from `find(..).err()?`; the conversion is checked. |
| 775 | `(a as usize).checked_add(b as usize)?` | Safe | Checked. |
| 779 | `pool[next_child..end]` | Safe | `a == next_child` and `end <= pool.len()` are required on line 776, and `end >= a`. |
| 799 | `s.child_pool[a as usize..]` | Safe | Before the pushes on line 780 the pool's length was `next_child`, which equals `a`. |
| 803 | `s.flags[c.index()]` | Safe | `earlier` (`store.rs:723`) only gives ids below `index`, which is the length of `flags` at that point. |
| 833 | `s.types[i + 1]` | Safe | All `n` terms have been pushed, and a type id above `n` returns on line 830. |

## pathos-syntax

### src/error.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 1-74 | no indexing, arithmetic, unwrap or assert | Safe | Plain data and a `Display` implementation. |

### src/latin1.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 24 | `debug_assert!(byte.is_ok(), ..)` | Safe (was: crafted snapshot, debug build only) | Snapshot strings are read as UTF-8 (`pathos-term/src/codec.rs:103-106`) and not checked to be Latin-1, so a name with a character above 255 reaches `encode` when it is printed. From text, every string is `decode` output joined with ASCII. **Now `Reader::str` rejects a string with a character above U+00FF, so no such name or line is read; test `a_store_with_a_name_that_is_not_latin_1_is_rejected`.** |
| 25 | `byte.unwrap_or(b'?')` | Safe | No unwrap. |

### src/lexer.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 22-58 | `t[..]` in `const fn char_classes` | Safe | Evaluated at compile time with `u8` indices into a 256-entry table. |
| 66 | `CHAR_CLASS[(ch & 0xff) as usize]` | Safe | The index is 0..=255; end of input (-1) maps to entry 255. |
| 187-188 | `self.token.find('\0')`, `truncate(nul)` | Safe | `nul` is the byte index of a one-byte character. |
| 194-196 | `self.input.get(self.pos)`, `self.pos += 1` | Safe | Checked access; `pos` never exceeds the input's length. |
| 212 | `self.end_line.wrapping_add(1)` | Safe (fixed in this milestone) | The line number is a `u32` counted per newline; it now wraps, as the column does at `lexer.rs:216`, instead of overflowing in a debug build on an input with 2^32 newlines. |
| 216 | `self.end_column.wrapping_add(1)` | Safe | Wraps by design. |
| 231 | `(ch & 0xff) as u8` | Safe | Cast. |
| 263 | `u8::try_from(ch).unwrap_or(0)` | Safe | No unwrap. |
| 387 | `t[0]` | Safe | The token holds at least the character pushed at `lexer.rs:262`; the function is called only from `lexer.rs:339`. |
| 392-399 | `t[i]`, `i + 1` | Safe | `i` ranges over `1..t.len()`; a symbol token holds only ASCII, so bytes and characters agree. |

### src/token.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 1-121 | no indexing, arithmetic, unwrap or assert | Safe | An enum and its `Display` implementation. |

## pathos-check

### src/eval.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 51-53, 75, 77, 83, 151, 207 | `estack[top]` | Safe | `top = len - 1` under `while !estack.is_empty()` (eval.rs:50); the stack only grows inside the inner loop (eval.rs:139). |
| 95 | `children[0]` | Safe | An if-then-else without exactly three children returns at eval.rs:88-92. |
| 124, 180 | `unreachable!` | Safe | A term is visited a second time only after every child pushed at eval.rs:97 was popped, and every pop stores a value (eval.rs:59, 67, 78, 90, 208, 234). Terms are acyclic: a child has a smaller handle, which store.rs:723 also enforces for snapshots. |
| 126 | `args[0]` | Safe | A term that reaches its second visit is evaluatable or non-ground (eval.rs:56); both flags come from children (store.rs:459-465), so it has one. This holds for snapshot terms too. |
| 152, 159, 162, 170, 171 | `cchildren[0..3]`, `children[1..3]` | Safe | An if-then-else without exactly three children is finished at its first visit (eval.rs:88-92). |
| 276, 279 | `children[1..]`, `children[0]` | Safe | Callers pass a head: eval.rs:131 (as line 126), build.rs:260 (non-empty by build.rs:155), step.rs:107 (two or more by step.rs:103). |
| 296, 298, 320 | `child(prog, i)`, `child(case, 0)`, `child(case, 1)` | Safe (was: crafted snapshot) | From text a program term is built only from pairs (cmd_parser.rs:883 with expr_parser.rs:508, cmd_parser.rs:675-676, build.rs:123-124). Needs a Program symbol whose `AppInfo.cons` is not a list of pairs, which snapshot.rs:218 does not check. Not demonstrated. **Now `read_image` rejects a snapshot with a program that is not a list of cases, each a pair whose first element has a head (`is_program_term`); test `a_program_that_is_not_a_list_of_cases_is_rejected`.** |
| 313 | `child(pat, j)` | Safe | `j < nargs == num_children(pat)` (eval.rs:299). |
| 359-362 | `.first()?`, `.get(1)?` | Safe | Checked accessors. |
| 350, 370, 581, 704, 925, 970 | calls from `evaluate` into `get_type` and `evaluate_nil`, which call `evaluate` again | Stack | Each call is a native frame, and typing.rs:83 and typing.rs:357 call back. The depth follows a numeral or a chain of declarations in the input, or has no bound at all (a literal type rule `(eo::typeof eo::self)`). |
| 369, 680 | `child(nil, 1)`, `child(op, 1)` on a `PARAMETERIZED` term | Safe (was: crafted snapshot) | From text only build.rs:70-72 makes this kind, with two children, and no builtin symbol builds it (state.rs:78-85). Needs a `PARAMETERIZED` term with fewer than two children; child counts per kind are not checked (store.rs:680-838). Not demonstrated. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 411, 412, 415 | `child` in `nary_step` | Safe | Kind and `num_children == 2` are checked at eval.rs:408 and 412. |
| 496 | `args[1]` or `args[2]` | Safe | If-then-else gets here only from build.rs:171 after `check_arity` (three arguments); `evaluate` handles it at eval.rs:150 and never passes it to eval.rs:182. |
| 504 | `args[0]` | Safe | `first` exists (eval.rs:488). |
| 537, 542, 543, 556, 559, 560 | `args[1]` | Safe | eval.rs:524-529 returns when there are fewer than two arguments and the first is not stuck; when it is stuck, `&&` and `\|\|` short-circuit before `args[1]`. |
| 591 | first child of a `VARIABLE` (was `child(first, 0)`) | Safe (fixed in this milestone) | `(eo::var)` has no children; the checked accessor now gives the "Too few arguments" error through `missing_argument`. |
| 600 | `child(first, 0)` on `APPLY_OPAQUE` | Safe (was: crafted snapshot) | From text this kind always has a head (build.rs:185, build.rs:435, eval.rs:667). Needs an `APPLY_OPAQUE` term with no children; child counts per kind are not checked. Not demonstrated. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 650 | `child(sym, 0)` | Safe | `num_children > 0` is in the loop condition (eval.rs:649). |
| 677, 698, 704-707 | `args[0]`, `args[1]` | Safe | `first` exists; `args[1]` is guarded by `args.len() > 1` (eval.rs:701). |
| 713-720, 764 | `args.get` in `arg!`, `hargs.get(i)` | Safe | Checked accessors; a missing argument sets the fatal error. |
| 742-751 | loop of up to 2^32 - 1 iterations for `eo::list_repeat` | Resource | The count comes from a numeral; each iteration makes terms. Memory and time only. |
| 789, 824, 891 | `i + 1` | Safe | `i` is a list index. |
| 845, 848, 874 | `+= 1` on `u32` counts | Safe | Bounded by the number of list elements. |
| 882 | `*n -= 1` | Safe | The entry is at least 1; it is removed when it reaches 0 (eval.rs:883-885). |
| 804, 831, 900 | `truncate` | Safe | `Vec::truncate` does not panic. |
| 907 | `hargs[0]` | Safe | `hargs.len() == 1` is checked in the same expression. |
| 955, 963, 969, 974, 983 | `children[0]`, `children[1]` | Safe | Callers build.rs:238 and build.rs:480 pass a head; a single child returns at eval.rs:952-959. |

### src/typing.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 83 | `evaluate` of a literal type rule | Stack | Recursion with `get_type` through eval.rs:581; a rule `(eo::typeof eo::self)` never ends. |
| 211, 216 | `child(e, 0)`, `child(e, 1)` on `LAMBDA` | Safe (was: crafted snapshot) | From text only cmd_parser.rs:150 and cmd_parser.rs:782 build `LAMBDA`, with two children. Needs a `LAMBDA` with fewer; child counts per kind are not checked. The same broken invariant is demonstrated at build.rs:459. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 224 | `child(e, 0)` on `PROOF` | Safe (was: crafted snapshot) | From text only build.rs:57 builds `PROOF`, with one child. Needs a `PROOF` term without children. Not demonstrated. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 240 | `child(e, 1)` on `PARAMETERIZED` | Safe (was: crafted snapshot) | As eval.rs:369. Not demonstrated. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 246 | `.first()`, `.get(1)` | Safe | Checked accessors. |
| 286 | `children[0]` | Safe (was: crafted snapshot) | From text an application always has a head: expr_parser.rs:174-178 rejects an empty frame and `(_)`, and every other `mk_expr(APPLY, ..)` call passes one. Needs an `APPLY` term without children, bound to a name. Demonstrated in release and debug builds. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 307, 308 | `wrapping_sub(1)`, `children.len() - 1` | Safe | `children` is non-empty (typing.rs:286). |
| 315, 316, 345, 356 | `hdtypes[i - 1]`, `children[i]`, `hdtypes[len - 1]` | Safe | `hdtypes.len() == children.len()`, at least 1 (typing.rs:300). |
| 322 | `child(hdt, 0)` on `QUOTE_TYPE` | Safe (was: crafted snapshot) | From text only build.rs:62 builds `QUOTE_TYPE`, with one child. Needs one without children. Not demonstrated. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 357 | `evaluate(ret, ctx)` | Stack | Recursion with `get_type` through eval.rs:581: a return type that applies `eo::typeof` to another application. Depth follows a numeral or a chain of declarations. |
| 427, 437, 449, 450, 452 | `children[1]`, `child_types[0..2]` | Safe | `check_arity` at typing.rs:419 fixes the number of arguments of each operator. |

### src/build.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 35 | `vec![ty; arity]` | Resource | `arity` is a numeral up to 2^32 - 1 from `declare-sort` or `declare-datatypes` (cmd_parser.rs:129, 373, 427): a 16 GiB request, which aborts the process where the allocation fails, then 2^32 terms at build.rs:17-19. |
| 49 | `child(p, 0)`, `child(p, 1)` | Safe | The pairs come from expr_parser.rs:508; the only caller is cmd_parser.rs:636. |
| 106 | `child(cons, 0)`, `child(cons, 1)` | Safe | Kind and `num_children == 2` are checked at build.rs:103. |
| 134, 135 | `children[0]`, `children[1..]` | Safe | Callers pass three children (build.rs:145 after `len > 2`, 278, 370, 390, 396). |
| 163, 164 | `children[..2]`, `children[2..]` | Safe | `children.len() > 2` (build.rs:162). |
| 183 | `children[0]` | Safe | `children.len() == 2` (build.rs:182). |
| 185, 219, 377, 405, 414 | `mk_expr` called from `mk_apply_expr` and `mk_apply_attr` | Stack | `mk_expr` calls `mk_apply_expr`, which calls `mk_apply_attr`, which calls `mk_expr` on the attribute's term. The depth is the length of a chain of symbols each naming the previous one as its `:pairwise` (or similar) term. |
| 200 | `store.mk(k, ..)`, which panics at store.rs:443 for an atomic kind | Safe (was: crafted snapshot) | From text `k` is a constant compound kind or an `AppInfo.kind` set only by checker.rs:267 from state.rs:78-85. Needs a symbol whose `AppInfo.kind` is a symbol or literal kind, which snapshot.rs:222 accepts. Demonstrated in release and debug builds. **Now `read_image` rejects a snapshot in which a builtin's kind is not a compound kind; test `a_builtin_of_an_atomic_kind_is_rejected`.** |
| 206, 213, 216, 219 | `children[0]`, `children[n - 1]`, `children[1..]` | Safe | `children` is non-empty (build.rs:155). |
| 285, 287, 291, 297 | `children[0]`, `children[1]` | Safe | `children.len() == 2` (build.rs:192). |
| 312, 476 | `vchildren[0]` | Safe | Callers build.rs:239, 299 and 481 pass a head. |
| 332, 334, 348, 357 | `vchildren[i]`, `vchildren[nchild - i]` | Safe | `nchild >= 2` (build.rs:321) and `1 <= i < nchild`. |
| 353 | `i -= 1` | Safe | `i` is 1 there. |
| 390, 396, 403 | `vchildren[i + 1]`, `vchildren[j]`, `cchildren[1]` | Safe | The loop bounds keep both indices below `nchild`; `cchildren.len() == 2` (build.rs:401). |
| 409, 410, 413 | `vchildren[1]`, `vchildren[1..]` | Safe | `nchild == 2` is checked first; the slice may be empty. |
| 435, 440 | `vchildren[..1 + nargs]`, `vchildren[1 + nargs..]` | Safe | `nargs < nchild` (build.rs:426). |
| 450, 452, 456 | `children[0]`, `children.len() - 1`, `children[1..]` | Safe | `children` is non-empty. |
| 451, 459 | `child(hd, 0)`, `child(hd, 1)` on `LAMBDA` | Safe (was: crafted snapshot) | As typing.rs:211. Needs a `LAMBDA` with one child, bound to a name and applied. Demonstrated in release and debug builds. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 511, 512, 516 | `ch[..n - 1]`, `ch[n - 1]`, `child(et, 2)` | Safe | `num_children > 0` (build.rs:508) and `== 3` (build.rs:514). |

### src/step.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 49, 51, 52, 53 | `t[0..3]` | Safe | `num_children == 4` is checked at step.rs:43, for snapshot terms too. |
| 82 | `child(e, 0)` on `PROOF` | Safe (was: crafted snapshot) | As typing.rs:224: needs a `PROOF` term without children bound to a name used as a premise. Not demonstrated. **Now `TermStore::mk` does not make, and `TermStore::read_from` rejects a snapshot with, a term whose number of children its kind cannot have (`NodeKind::takes`: two for `LAMBDA` and `PARAMETERIZED`, one for `PROOF` and `QUOTE_TYPE`, at least one for `APPLY` and `APPLY_OPAQUE`); test `a_term_of_the_wrong_shape_is_not_made_and_not_read`.** |
| 105, 121 | `children[0]`, `children[1..]` | Safe | `children` starts with the rule's program (step.rs:49). |
| 111 | `child(result, 0)` | Safe | `result` is an evaluatable `APPLY` (step.rs:108, 110), which has a child (store.rs:459-465). |
| 115, 118 | `child(child(p, 0), 0)`, `children(pattern)[1..]` | Safe (was: crafted snapshot) | From text the program has one case (step.rs:114), a pair whose first element is an application with a head (cmd_parser.rs:871-878, 673). Needs a rule program whose case is not such a pair. Not demonstrated. **Now `read_image` rejects a snapshot with a program that is not a list of cases, each a pair whose first element has a head (`is_program_term`); test `a_program_that_is_not_a_list_of_cases_is_rejected`.** |

### src/checker.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 327-331 | `pop`, `remove` on an overload list | Safe | Reached through `get_mut(name)?`; `pop` on an empty list returns `None`. |
| 368 | `hash_counter += 1` | Safe (was: crafted snapshot, debug build only) | From text it needs 2^64 calls. Needs `hash_counter = 2^64 - 1`, which snapshot.rs:265 reads without a bound. Demonstrated in a debug build; a release build wraps. **Now the counter wraps (`wrapping_add`), as a release build did; test `counters_at_their_maximum_wrap`.** |

### src/print.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 26 | `&s[1..s.len() - 1]` | Safe | `s.len() > 1` and both ends are the one-byte bar character (print.rs:25). |
| 75 | `count[&t]` | Safe | `t` comes from `order`, whose terms were inserted at print.rs:66. |
| 87, 149, 156 | `visit.len() - 1`, `visit[top]` | Safe | Inside `while let Some(..) = visit.last()` (print.rs:86). |
| 133, 157 | `child(cur, 0)`, `child(cur, idx)` | Safe | A term without children returns at print.rs:96-130; `idx < nchildren` (print.rs:151). Holds for any term shape. |
| 100-117 | printing a bit-vector literal | Resource | A bit-vector prints one digit per bit (bitvec.rs:55-56), and `(eo::to_bin 4294967295 0)` is cheap to make: printing it in a message asks for 4 GiB. |

### src/snapshot.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 152 | `self.overloads[name]` | Safe | `name` comes from `self.overloads.keys()` (snapshot.rs:147). |
| 214, 239, 243, 254, 267, 277, 285 | `with_capacity` and `reserve` with counts from the file | Safe | Each count is bounded by the bytes left in the file (codec.rs:98-101). |
| 222 | `group - 1` | Safe | `group` is at least 1 in that match arm. |
| 195-303 | all other reads | Safe | Every read goes through `codec::Reader`, which returns `None` at the end of the input (codec.rs:66-106). |

### src/stats.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 104 | `stat.count += 1` | Safe (was: crafted snapshot, debug build only) | Needs a rule count of 2^64 - 1, which snapshot.rs:287 reads without a bound, then a step of that rule. Demonstrated in a debug build; a release build wraps. **Now the counter wraps (`wrapping_add`), as a release build did; test `counters_at_their_maximum_wrap`.** |
| 106 | `mk_count - start_mk` | Safe | The store's count only grows during a step, and a snapshot is installed only by an include, never inside a step. |
| 115 | `+= 1` on a program count | Safe (was: crafted snapshot, debug build only) | As stats.rs:104, with a program count of 2^64 - 1 and `--stats`. Not demonstrated. **Now the counter wraps (`wrapping_add`), as a release build did; test `counters_at_their_maximum_wrap`.** |
| 208, 210 | divisions | Safe | Floating point: a zero count or total prints `inf` or `NaN`. |
| 87, 169, 202 | width formatting | Safe | Padding only; a wide value widens its column. |

## pathos-elab

### src/expr_parser.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 162, 254 | `pstack.pop()` | Safe | Line 162 is a `let ... else`; line 254 is under `!pstack.is_empty()` (expr_parser.rs:198). |
| 169, 175 | `sf.args[0]` | Safe | `sf.args.len() == 1` is checked in the same condition. |
| 200-204, 227, 228, 240 | `pstack[top]`, `pstack.remove(top)` | Safe | `top = len - 1` under `!pstack.is_empty()` (expr_parser.rs:198). |
| 293 | `BitVec::new(w, ..)` with `w` up to 2^32 - 1 | Resource | The value is reduced, not padded, so making it is cheap; the cost appears when it is printed (print.rs:100-117). |
| 373 | `text[pos + 1..]` | Safe | `pos` is the position of the one-byte `/`. |
| 381, 388 | `text[2..]` | Safe | These tokens are `#x` or `#b` plus at least one digit (lexer.rs:276-289), and the token text always belongs to the token being consumed. |
| 522, 523 | `nparen.wrapping_add(1)`, `nparen.wrapping_sub(1)` | Safe (fixed in this milestone) | Line 522 was `nparen += 1`, which overflowed in debug builds after a `)` had wrapped the count; both now wrap, as in Ethos. |
| 595 | `child(v, 0)` | Safe | `v` comes from build.rs:86-89, which gives it two children. |
| 631 | `token_str()[1..]` | Safe | A keyword token is `:` plus a symbol character (lexer.rs:308-313). |
| 663 | `strip_ends` on a quoted symbol (was `s[1..s.len() - 1]`) | Safe (fixed in this milestone) | The token text stops at its first NUL (lexer.rs:187-189), so it need not end in a bar; `strip_ends` (expr_parser.rs:1019-1024) works on characters and returns `None`, an error, when nothing is left. |
| 691 | `strip_ends` on a string literal (was `&s[1..s.len() - 1]`) | Safe (fixed in this milestone) | As line 663. |
| 904 | `child(pat, i)` | Safe | `i < num_children(pat)` (expr_parser.rs:903). |

### src/cmd_parser.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 129, 373 | arity `as usize`, passed to `mk_type_constant` | Resource | See build.rs:35. |
| 306, 672 | `insert(0, ..)` | Safe | Index 0 is valid for any vector. |
| 469, 470, 475, 480, 489 | `dnames[i]`, `arities[i]`, `dtlist[i]` | Safe | `i < dnames.len()` (cmd_parser.rs:437); `arities[i]` only when `i < arities.len()` (cmd_parser.rs:468); `dtlist` has an entry for each such `i` (cmd_parser.rs:426-431) or gets one at cmd_parser.rs:473. |
| 815 | `include_file`, which parses the file and runs its `include` commands | Stack | One set of native frames per nested include (parser.rs:52-101). Cycles are cut (parser.rs:60); a chain of several thousand distinct files is not. |
| 869, 880 | `child(p, 0)`, `child(p, 1)` | Safe | `p` is a pair from expr_parser.rs:508. |
| 871 | `child(pc, 0)` | Safe | Evaluated only when `pc` is an `APPLY`, which from text has a head (expr_parser.rs:174-178). |

### src/state.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 129-133 | `decls_size_ctx.pop()`, `decls.pop()` | Safe | `let ... else`: an empty stack is an error, not a panic. |
| 154-155 | `pop`, `truncate` | Safe | `if let`; `Vec::truncate` does not panic. |
| 167-168, 173-174 | `.get(start)` | Safe | Checked accessors. |
| 323, 335, 344, 351, 367 | `reserve` and `with_capacity` with counts from the file | Safe | Each count is bounded by the bytes left in the file (codec.rs:98-101). |
| 317-386 | all other reads | Safe | Through `codec::Reader`; the scope sizes are checked against their lists (state.rs:356-363). |

### src/snapshot.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 68, 98 | `try_from(..).unwrap_or(..)` | Safe | No panic on a value that does not fit. |
| 159, 266, 301, 321 | `with_capacity` | Safe | The state's own size, or a count bounded by the bytes left in the file (codec.rs:98-101). |
| 203 | `&file[MAGIC.len() + 12..]` | Safe | Twenty bytes were read just before (snapshot.rs:199-202). |
| 213 | `file.len() - r.remaining()` | Safe | The reader never has more left than the file holds. |
| 263, 305, 310 | `.get(..)?` | Safe | Checked accessors. |
| 304 | `&entries[1..]` | Safe | `entries.first()?` at snapshot.rs:285. |
| 337-340 | printing the lines stored in the snapshot | Safe (was: crafted snapshot, debug build only) | Needs an output line with a character above 255, which the reader accepts as UTF-8 (codec.rs:103-106); writing it trips the `debug_assert!` in latin1.rs:24 from main.rs:132. Demonstrated in a debug build; a release build writes `?`. **Now `Reader::str` rejects a string with a character above U+00FF, so no such name or line is read; test `a_store_with_a_name_that_is_not_latin_1_is_rejected`.** |

### src/parser.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 52-101 | `include_file` | Stack | See cmd_parser.rs:815. |
| 105-113 | reading a file | Safe | Bytes, not UTF-8; a directory reads as empty and a missing file is an error. |

### src/path.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 17 | `&p[..=last]` | Safe | `last` is the position of a one-byte `/`. |

### src/thread.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 26 | `thread.spawn(run)` failing | Resource | Not a panic: if the system cannot give the checker's thread its 64 MiB of address space, the run ends with `Error: cannot start the checker's thread` and status 1. No input decides it. |
| 30 | `std::panic::resume_unwind(panic)` | Safe | Runs only after the checker's thread has panicked, which the other rows of this file are about; it passes that panic on so that the process ends with status 101 as it did when the checker ran on the main thread. It does not print a second message. |

### src/plugin.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 167-203 | taking and restoring the plugin, the event queue | Safe | No indexing and no unwrap; in the `pathos-eo` binary nothing calls `State::set_plugin`, so there is no plugin and no queue. |

## pathos (the binary)

### src/main.rs

| Line | Construct | Verdict | Why |
| --- | --- | --- | --- |
| 64 | `args[i]` | Safe | `i < args.len()` (main.rs:63). |
| 131-136, 236-238, 242 | writing to stdout and stderr | Safe | `write_all` with its result dropped: a closed pipe, a full device and a closed descriptor are ignored. |
| 132, 237 | `latin1::encode`, whose `debug_assert!` is at latin1.rs:24 | Safe (was: crafted snapshot, debug build only) | From text every string is input bytes decoded one char per byte, plus ASCII. Needs a snapshot output line or name with a character above 255. Demonstrated in a debug build through snapshot.rs:339. **Now `Reader::str` rejects a string with a character above U+00FF, so no such name or line is read; test `a_store_with_a_name_that_is_not_latin_1_is_rejected`.** |
| 194, 219, 226-229 | paths and arguments that are not UTF-8 | Safe | Arguments are read with `args_os` and paths built with `OsString::from_vec`. |
| 209-218 | `RefCell`: `borrow_mut` in the two closures, `borrow` at line 218 | Safe | The closures run only inside `include_file` (main.rs:217); `write_snapshot(&self, ..)` cannot call them while the `borrow` is held. |

## pathos-eoc

### src/main.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 65 | `&args[i]` | Safe | The loop condition at main.rs:64 is `i < args.len()`. |
| 189, 225, 226 | `let _ = w.write_all(..)`, `out.flush()` | Safe | The results are discarded, so a closed stdout or stderr cannot panic; the crate has no `println!` or `eprintln!`. |
| 218-221 | `args_os()` with `latin1::decode` | Safe | Arguments are decoded byte by byte; nothing unwraps a UTF-8 conversion. |
| 229-232 | `Err(e)` arm of `main` | Ethos's fatal error | Every `Error` is printed and becomes exit status 1; Ethos prints the same text after its `Fatal failure within` line and aborts (base/check.h:90, docs/ethos-differences.md:36-37). |

### src/std_plugin.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 21-30 | `std::fs::read`, `std::fs::write` | Safe | `read_text` returns `Option` and `write_text` returns `bool`; no I/O result is unwrapped. |
| 43 | `&path[..pos]` | Safe | `pos` comes from `path.rfind('/')` at std_plugin.rs:40, so it is a char boundary inside the string. |
| 81, 124, 127 | `unwrap_or(0)`, `unwrap_or_default()` | Safe | These forms cannot panic. |
| 234 | `self.type_var_counter += 1` | Safe | A counter of generated type variables, one step per call. |
| 70 | `Error::fatal` (path is not a directory) | Ethos's fatal error | plugins/std_plugin.cpp:102, same text. |
| 79 | `Error::fatal` (cannot create directory) | Ethos's fatal error | plugins/std_plugin.cpp:109, same text including the errno. |
| 138, 143 | `Error::fatal` (no resource root, no output root) | Ethos's fatal error | plugins/std_plugin.cpp:232 and :236. |
| 180 | `Error::fatal` (resource to copy is missing) | Ethos's fatal error | plugins/std_plugin.cpp:212, same text. |
| 186 | `Error::fatal` (copy cannot be written) | Ethos's fatal error | plugins/std_plugin.cpp:218. |
| 206 | `Error::fatal` (template is missing) | Ethos's fatal error | plugins/std_plugin.cpp:166, same text. |
| 225 | `Error::fatal` (output cannot be written) | Ethos's fatal error | plugins/std_plugin.cpp:196, same text. |
| 311 | `Error::fatal` (Boolean literal kind) | Ethos's fatal error | plugins/std_plugin.cpp:331; the parser rejects `<boolean>` before a stage sees it. |

### src/defs_reader.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 26-30 | `File::open(..).ok()?`, `let _ = read_to_end(..)` | Safe | A file that cannot be opened is `None` and a failed read keeps what was read. |
| 130, 135 | `text.get(from..to)`, `text.get(from..)` | Safe | `sub` and `find_from` use `get`, which returns `None` for a bad range or a non-boundary; every cut of a `str` in the file goes through them. |
| 143, 144 | `b[i]`, `b[i + 1]` | Safe | The same condition at defs_reader.rs:143 tests `i < n` first and `i + 1 >= n` before the second index. |
| 151, 163, 188, 190 | `b[i]` | Safe | Guarded by the loop conditions at defs_reader.rs:151, :162 and :187. |
| 170 | `depth.wrapping_sub(1)` | Safe | Wraps on purpose, as the unsigned counter of the C++ does. |
| 195 | `i = e - 1` | Safe | `e` is the `i + 1` that `form_end` returns at defs_reader.rs:172, so it is at least 1. |
| 206, 209, 213, 223 | `b[k]`, `b[i]`, `b[j]` | Safe | `k` ranges over `1..n`, and the loops test `i < n`, `j < n` and `j < b.len()` first. |
| 236, 241 | `b[i]`, `b[j]` | Safe | Guarded by `i < n` at defs_reader.rs:235 and `j < n` at :241. |
| 245 | `i = j - 1` | Safe | `b[i]` is `$`, a name character, so the loop at defs_reader.rs:241 leaves `j >= i + 1`. |
| 255 | `form.len().saturating_sub(1)` | Safe | Saturating. |
| 573, 597, 602 | `placed[i]` | Safe | `placed` is `vec![false; blocks.len()]` (defs_reader.rs:570) and `i` comes from `blocks.iter().enumerate()`. |
| 590, 591, 593, 594 | `blocks[o]`, `placed[o]` | Safe | `o` comes from the `owner` map, filled at defs_reader.rs:563-566 with indices of the same slice. |
| 315 | `Error::fatal` (no aggregates) | Ethos's fatal error | plugins/model_smt/defs_reader.cpp:467. |
| 468, 478, 494 | `Error::fatal` (malformed head line) | Ethos's fatal error | plugins/model_smt/defs_reader.cpp:398, :409 and :424. |

### src/model_smt.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 75 | `txt.replace_range(pos..pos + guarded.len(), ..)` | Safe | `pos` is where `txt.find(&guarded)` matched (model_smt.rs:70), so both ends are char boundaries inside `txt`. |
| 71 | `Error::fatal` (placeholder missing) | Ethos's fatal error | plugins/model_smt/model_smt.cpp:248, same text. |
| 118 | `Error::fatal` (no model semantics) | Ethos's fatal error | plugins/model_smt/model_smt.cpp:72, same text. |
| 134, 140, 147 | `Error::fatal` (reading the two signatures) | Ethos's fatal error | plugins/model_smt/model_smt.cpp:88, :94 and :99, same text. |
| 227 | `Error::fatal` (template missing) | Ethos's fatal error | plugins/model_smt/model_smt.cpp:262. |
| 260 | `Error::fatal` (unexpanded `$eoc_` name) | Ethos's fatal error | plugins/model_smt/model_smt.cpp:308. |
| 267 | `Error::fatal` (output cannot be written) | Ethos's fatal error | plugins/model_smt/model_smt.cpp:316, same text. |

### src/native_layer.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 89 | slice pattern `[name, needs, deps @ ..]` | Safe | A `let .. else`; a line with fewer than two words takes the error branch. |
| 130 | `self.defs[index]` | Safe | `index` comes from `self.of`, set at native_layer.rs:95 to `defs.len()` just before the push at :96; `defs` never shrinks. |
| 172 | `out.truncate(out.trim_end_matches('\n').len())` | Safe | The length of a prefix of `out`, which is a char boundary. |
| 51 | `Error::fatal` (layer cannot be read) | Ethos's fatal error | plugins/native_layer.cpp:26, same text. |
| 83 | `Error::fatal` (not a line of the layer) | Ethos's fatal error | plugins/native_layer.cpp:48, same text. |
| 90 | `Error::fatal` (block without name and scope) | Ethos's fatal error | plugins/native_layer.cpp:65, same text. |
| 104 | `Error::fatal` (no block) | Ethos's fatal error | plugins/native_layer.cpp:78, same text. |
| 134 | `Error::fatal` (scope cannot see the block) | Ethos's fatal error | plugins/native_layer.cpp:106, same text. |

### src/meta_reduce.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 128, 179, 208, 265, 280, 340 | `.get(2)`, `.last()?`, `.first()`, `let &[vars, body] = .. else` | Safe | Checked accessors and a refutable slice pattern. |
| 165, 169 | `children[1]`, `children[0]` | Safe | `children.len() <= 1` short-circuits at meta_reduce.rs:164 and returns before either index. |
| 184, 185 | `children[1]`, `children[0]` | Safe | `children.len() == 2 &&` precedes them at meta_reduce.rs:183. |
| 195, 202 | `children[1]` | Safe | `children.len() != 2` at meta_reduce.rs:194 returns the error first. |
| 191, 288 | `unwrap_or(..)` | Safe | Cannot panic. |
| 75 | `Error::fatal` (no prefix for meta-kind) | Ethos's fatal error | plugins/utils.cpp:61. |
| 197 | `Error::fatal` (bad embed type application) | Ethos's fatal error | plugins/meta_reduce_plugin.cpp:244, same text. |

### src/linear_patterns.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 66, 156 | `prog_count += 1`, `*n += 1` | Safe | Counters, one step per case or occurrence. |
| 87 | `defappc[0] = new_prog` | Safe | `defappc` starts as `vec![curr_prog]` at linear_patterns.rs:70. |
| 109 | `children[0] = prog` | Safe | `child(ck, pat, 0)?` at linear_patterns.rs:105 has already shown the pattern has a first child. |
| 183-185, 189-191 | `let .. else { return pat }` | Safe | The branches that cannot be reached return a value; there is no `unreachable!`. |
| 23 (via 28, at 48, 49, 76, 105) | `malformed` | Error where Ethos reads out of bounds | A case or pattern without the child the C++ indexes unchecked stops the stage with `LinearPattern: unexpected term: ...`. |
| 97, 111, 196 | `ck.mk_expr(Kind::PROGRAM, &curr_cases)`, `ck.store.mk(..)` | Safe | `TermStore::mk` panics only for an atomic kind (`pathos-term/src/store.rs:443`). Lines 97 and 111 pass the constants `PROGRAM` and `APPLY`; line 196 passes the kind of a term that has children (`linear_patterns.rs:164` sets terms without children aside), which is a compound kind. `mk_expr` accepts an empty list of cases. |

### src/trim_defs.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 36, 45 | `self.chars.get(self.pos)` | Safe | Checked access. |
| 49 | `self.pos.saturating_sub(1)` | Safe | Saturating. |
| 174, 178 | `depth += 1`, `depth -= 1` | Safe | An `i64` that moves by one per parenthesis read. |
| 192-197, 212-219 | `struct SExpr` and its `Drop` | Safe (fixed in this milestone) | `drop` moves the children to a worklist (trim_defs.rs:214-216), so each node is dropped with no children left and the stack does not grow with the nesting; the derived drop it replaces recursed once per level. |
| 221-258 | `parse_sexpr`: `open.push`, `open.pop()`, `open.last_mut()` | Safe (fixed in this milestone) | The open lists are a `Vec<SExpr>` used only through `push`, `pop` and `last_mut` (trim_defs.rs:232, :236, :239, :250), with no index; the `list_at` walk from the root on every token, which made the parse quadratic in the depth, is gone. |
| 264 | `&symbol[1..symbol.len() - 1]` | Safe | trim_defs.rs:263 requires `len() >= 2` and a `\|` at each end, each one byte, so both cuts are boundaries. |
| 282 | `chars.len() - 1` | Safe | `chars.len() < 2` returns at trim_defs.rs:279. |
| 286, 287 | `chars[i]`, `chars[i + 1]` | Safe | The loop keeps `i < n` and tests `i + 1 < n` first; `chars` is a `Vec<char>`, so there is no boundary to miss. |
| 355, 358 | `constructor.children[0]`, `constructor.children[1..]` | Safe | An empty `children` is skipped at trim_defs.rs:352. |
| 397 | `root.children[0]` | Safe | An empty `root.children` returns the error at trim_defs.rs:394. |
| 538 | `self.id_counter += 1` | Safe | A counter of symbols. |
| 562, 564, 569 | `self.commands[cid]`, `self.cmd_defined_syms[cid]`, `self.cmd_syms[cid]` | Safe | `cid` ranges over `0..self.commands.len()` and the three vectors are pushed together at trim_defs.rs:552-554. |
| 630, 645, 658 | `self.cmd_syms[cid]` | Safe | Every stored id is `self.commands.len()` taken at trim_defs.rs:532 before the push at :552 (stored at :543, :547, :550). |
| 681, 684 | `self.commands[cid]` | Safe | `retained` holds only those ids. |
| 67 (via 114, 129, 187, 229, 237, 243, 251, 395, 398) | `malformed` | Ethos's fatal error | plugins/trim_defs/trim_defs.cpp:43 (in a command) and :46 (in the input), same text. |
| 280 | `Error::fatal` (invalid internal string token) | Ethos's fatal error | plugins/trim_defs/trim_defs.cpp:291; a string token always carries both quotes (trim_defs.rs:98-116), so it is not reached. |
| 587 | `Error::fatal` (file cannot be reopened) | Ethos's fatal error | The text Ethos prints for a file it cannot open (src/input.cpp:27). |
| 607 | `Error::fatal` (no target) | Ethos's fatal error | plugins/trim_defs/trim_defs.cpp:666, same text. |
| 618 | `Error::fatal` (target not found) | Ethos's fatal error | plugins/trim_defs/trim_defs.cpp:680, same text. |
| 639 | `Error::fatal` (symbol without defining command) | Ethos's fatal error | plugins/trim_defs/trim_defs.cpp:711; an id exists only with a command that defines it (trim_defs.rs:543), so it is not reached. |
| 690 | `Error::fatal` (output cannot be written) | Ethos's fatal error | plugins/trim_defs/trim_defs.cpp:779, same text. |

### src/desugar.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 194, 201, 208 | `*count += 1`, `oid + 1` | Safe | Counters of symbols that share a name. |
| 259, 431, 656 | `.first()`, `.split_last()` with `else` | Safe | An empty child list takes the error branch. |
| 291 | `tvars[*i]` | Safe | `tvars.len() >= *i` holds throughout: `*i` starts at 0 in each call and grows by one at desugar.rs:293, and when the two are equal the branch at :288-289 pushes instead of indexing. |
| 505 | `n.to_u32() as usize` | Safe | Taken only when `n.fits_u32()`; each step of the loop at desugar.rs:510 is `child(ck, ct, i)?`, which stops at the first missing child. |
| 556, 661, 699, 913, 917 | `+= 1` | Safe | Counters of arguments and parameters. |
| 582 | `parser_term_arity -= 1` | Safe | Guarded by `parser_term_arity > 0` at desugar.rs:579. |
| 1103 | `&types[..types.len().saturating_sub(1)]` | Safe | The end saturates at 0. |
| 1113 | `nargs.saturating_sub(1)` | Safe | Saturating. |
| 1125, 1158 | `nargs - i + 1`, `npremises - i + 1` | Safe | `i` ranges over `1..=nargs` and `1..=npremises`. |
| 1070, 1071 | `ck.get_literal_type_rule(k, self_term, None)` | Stack | A literal type rule that asks for the type of `eo::self`, e.g. `(declare-consts <numeral> (eo::typeof eo::self))`, recurses without end in pathos-check (crates/pathos-check/src/typing.rs:62-86) and overflows the stack; Ethos overflows on the same input. |
| 121 (via 126, 131 and their callers) | `malformed` | Error where Ethos reads out of bounds | A term without the type or child the C++ takes for granted stops the stage with `Desugar: unexpected term: ...` (docs/ethos-differences.md:237-239). |
| 182 | `Error::fatal` (used before it was initialized) | Error where Ethos reads out of bounds | `syms` is set by `initialize` (desugar.rs:1238) before any hook runs; the C++ has no such check. |
| 1035 | `Error::fatal` (Boolean literal kind) | Ethos's fatal error | plugins/desugar/desugar.cpp:1362; the parser rejects `<boolean>` first. |
| 1117 | `Error::fatal` (more than 10 arguments) | Ethos's fatal error | plugins/desugar/desugar_checker.cpp:70, same text. |
| 1137 | `Error::fatal` (premise list without nil) | Ethos's fatal error | plugins/desugar/desugar_checker.cpp:103, same text. |
| 1150 | `Error::fatal` (more than 8 premises) | Ethos's fatal error | plugins/desugar/desugar_checker.cpp:116, same text. |
| 1191 | `Error::fatal` (checker template missing) | Ethos's fatal error | plugins/desugar/desugar_checker.cpp:160, same text. |
| 1297 | `Error::fatal` (malformed exclusion directive) | Ethos's fatal error | plugins/desugar/desugar.cpp:1152, same text. |
| 1307 | `Error::fatal` (unknown exclusion kind) | Ethos's fatal error | plugins/desugar/desugar.cpp:1169, same text. |
| 1361 | `Error::fatal` (template missing) | Ethos's fatal error | plugins/desugar/desugar.cpp:1082, same text. |
| 1405 | `Error::fatal` (output cannot be written) | Ethos's fatal error | plugins/desugar/desugar.cpp:1127. |

(Milestone 29, which follows Ethos `b8d65127`, added two fatal errors to this file, at the places where the C++ now calls `EO_FATAL`: for an operator declared `:left-assoc-nil` or `:left-assoc-non-singleton-nil`, in `finalize_declaration`, and for a type rule for `<decimal>` or `<hexadecimal>` literals, in `literal_type_rule`. Each returns an error with Ethos's text. They have no line at the audited commit and are not counted in the table of results.)
| 262, 264, 707 | `ck.store.mk(kind, &children)` | Safe | `TermStore::mk` panics only for an atomic kind (`pathos-term/src/store.rs:443`). Line 262 passes `APPLY`, line 707 `APPLY` or `APPLY_OPAQUE`, and line 264 the kind of a term one of whose children changed, so a term with children, of a compound kind. |

### src/smt_meta.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 58 | `self.npush += 1` | Safe | A counter. |
| 188, 205, 209, 233, 263 | `unwrap_or_default()`, `.first()?`, slice pattern, `.last()` | Safe | Checked accessors. |
| 564 | `i + 1 - print_arg_start` | Safe | `.skip(print_arg_start)` at smt_meta.rs:563 gives `i >= print_arg_start`. |
| 654, 676 | `children[0]` | Safe | An empty `children` is handled at smt_meta.rs:633. |
| 693 | `.enumerate().skip(cstart).rev()` | Safe | No index; a `cstart` past the end gives an empty iterator. |
| 750 | `vctx_args[i]` | Safe | `vctx_args` has one entry per element of `types` (smt_meta.rs:730-732) and `i` ranges over all but the last. |
| 792 | `&args[j - 1]` | Safe | `j >= 1` by `.skip(1)`, and smt_meta.rs:785-790 rejects a case head with more children than `nargs`, while `args.len() == nargs - 1`. |
| 862 | `num_children(ct).saturating_sub(1)` | Safe | Saturating, and `child(ck, ct, nopq_args)?` follows at smt_meta.rs:863. |
| 970 | `&types[..types.len().saturating_sub(1)]` | Safe | The end saturates at 0. |
| 315 | `ck.get_literal_type_rule(k, gt, None)` | Stack | The same recursion in pathos-check as at desugar.rs:1070, reached when a constant named `$emb_Numeral`, `$emb_Rational`, `$emb_Binary` or `$emb_String` is declared under such a rule; Ethos overflows too. |
| 32 (via 37, 42, 456, 728, 786, 953, 960) | `malformed` | Error where Ethos reads out of bounds | The C++ guards these with `Assert`, a no-op in release (e.g. plugins/smt_meta/smt_meta_reduce.cpp:329, :927), and then reads outside the term; pathos stops with `SmtMetaReduce: unexpected term: ...` (docs/ethos-differences.md:240). |
| 866 | `Error::fatal` (ambiguous symbol) | Ethos's fatal error | The `AlwaysAssert` at plugins/smt_meta/smt_meta_reduce.cpp:837, with pathos's own wording (docs/ethos-differences.md:240-243). |

### src/lean_meta.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 74 | `self.rest.split_at(end)` | Safe | `end` is where `find(SPACES)` matched, or the length. |
| 91 | `digits.split_at(end)` | Safe | `end` is where `find(..)` matched, or the length. |
| 95, 98 | `checked_mul(10)?`, `checked_add(..)?`, `wrapping_neg()` | Safe | A number too large for `u64` is `None`; the negation wraps on purpose, as the C++ does. |
| 483 | `line.get(3..)` | Safe | Checked. |
| 542, 1148, 1162 | `num_children(..).wrapping_sub(1)` | Safe | The result is printed, passed to `child(..)?` (lean_meta.rs:1148, :1163) or compared with `MAX_INDEX_ARITY` (:1171); it never indexes unchecked. |
| 657 | `inner.len().wrapping_sub(1)` | Safe | Only compared with the result of `find`. |
| 707, 751, 761 | `unwrap_or(0)`, `for _ in 0..n` | Safe | Cannot panic. |
| 901 | `vctx_args[nargs - 1]` | Safe | `types.split_last()` at lean_meta.rs:895-900 returns the error for an empty `types`, and `vctx_args` has the same length. |
| 995, 1013 | `vctx_args[macro_start_arg - 1]`, `types[macro_start_arg - 1]` | Safe | `macro_start_arg` starts at 1 (lean_meta.rs:993) and the loop runs while it is below `nargs` (:994). |
| 1018 | `&types[macro_start_arg - 1..nargs - 1]` | Safe | `1 <= macro_start_arg <= nargs` after the loop and `nargs >= 1`. |
| 1050 | `vctx_args[i - 1]` | Safe | `i` ranges over `macro_start_arg..nargs`, so it is at least 1 and below the length. |
| 1183 | `self.embed_top_dt[uarity]` | Safe | `uarity > MAX_INDEX_ARITY` returns the error at lean_meta.rs:1171, which also covers the wrapped value from :542. |
| 1198 | `Vec::with_capacity(nopq_args)` | Safe | `nopq_args` is a child index that `child(ck, ct, n)?` accepted at lean_meta.rs:1163. |
| 1276 | `TITLES[n]` | Safe | `n` enumerates `embed_top_dt`, which has the same `MAX_INDEX_ARITY + 1` elements (lean_meta.rs:282, :1248). |
| 1364, 1465 | `for i in 0..op.index_arity` | Safe | The count comes from an echo, but only operators that pass `is_emitted_parser_op` get here (lean_meta.rs:1492, :1341), and those have at most 5 indices (:1171, :1182). |
| 1538, 2029, 2030 | `self.embed_top_dt[1]`, `self.embed_top_dt[0]` | Safe | Constant indices into an array of 6. |
| 1182, 1226, 1232, 1238 | `uarity as u64`, `+= 1` | Safe | A widening cast and counters of constructors. |
| 41 (via 51, 56, 896, 1027) | `malformed` | Error where Ethos reads out of bounds | A term without the type or child the C++ indexes unchecked stops the stage with `LeanMetaReduce: unexpected term: ...`. |
| 446 | `Error::fatal` (termination clauses cannot be read) | Ethos's fatal error | plugins/lean_meta/lean_meta_reduce.cpp:129, same text. |
| 467 | `Error::fatal` (clause names the native layer) | Ethos's fatal error | plugins/lean_meta/lean_meta_reduce.cpp:150, same text. |
| 604 | `check_failure` (string literal with quote or backslash) | Ethos's fatal error | `AlwaysAssert` at plugins/lean_meta/lean_meta_reduce.cpp:400, same text. |
| 629, 639 | `check_failure` (not an opaque application, not a native application) | Ethos's fatal error | `AlwaysAssert` at plugins/lean_meta/lean_meta_reduce.cpp:435 and :437, same text. |
| 658 | `check_failure` (quoted native string) | Ethos's fatal error | `AlwaysAssert` at plugins/lean_meta/lean_meta_reduce.cpp:450, same text. |
| 943 | `check_failure` (linear-pattern program name) | Ethos's fatal error | `AlwaysAssert` at plugins/lean_meta/lean_meta_reduce.cpp:843, same text. |
| 1172 | `check_failure` (more than 5 indices) | Ethos's fatal error | `AlwaysAssert` at plugins/lean_meta/lean_meta_reduce.cpp:1275, same text. |
| 1193 | `check_failure` (ambiguous symbol) | Ethos's fatal error | `AlwaysAssert` at plugins/lean_meta/lean_meta_reduce.cpp:1291. |
| 1985 | `Error::fatal` (program not found) | Ethos's fatal error | plugins/lean_meta/lean_meta_reduce.cpp:2195, same text. |
| 1994 | `Error::fatal` (malformed program name) | Ethos's fatal error | plugins/lean_meta/lean_meta_reduce.cpp:2205, same text. |

## pathos (the CPC checker)

`crates/pathos`, the binary that checks CPC proofs on the compiled checker
([pathos-cpc.md](pathos-cpc.md)), audited as the crates above were, for
everything "What was looked for" lists, outside `#[cfg(test)]`. Line numbers
are those of commit `cee75db0b4b188116e140897a7790b716c569db8` (`cee75db`, the commit milestone 30 branched
from), and `scripts/check-panics` checks every row against that commit: the
lines exist and hold the code the row names. CI runs it.

The input is the proof, any text at all, and the command line. The proof is
read by pathos's front end, which the sections above cover; the rows below
are the adapter's own code, from the hooks the front end calls
(`adapter.rs:1280-1340`) to the calls into the compiled checker. Two things
about that path matter in many rows: the arguments of a step reach the
adapter without having been typed (`pathos-elab/src/cmd_parser.rs:943-959`),
so it sees terms the front end would refuse elsewhere; and the compiled
checker's store (`generated/cpc-checker/src/lib.rs`) returns an error for a
wrong constructor, arity or handle instead of panicking, which the rows cite
by line. The generated crate itself is not audited here: its runtime is to
be rewritten (milestone 28), and audited then.

Reading was backed by runs, each under a memory cap, on release and debug
builds:

- **Mutated proofs** (`scripts/fuzz-cpc`): the 340 proofs of the safe
  corpus of at most 100 kB, mutated with the mutations of the harness's
  `fuzz.py`. 200,000 mutants on the release build of the audited commit
  (`--seed 1`): 13 panicked, all at `adapter.rs:303`, the `(as f)` row
  below, and one, holding `(declare-sort Index 4294967295)`, asked for
  16 GiB and stopped at the limit (the front end's `Resource` rows above).
  The same 200,000 on the fixed code: no panic, the one mutant at the
  memory limit. 60,000 more on the debug build of the fixed code
  (`--seed 2`): every run ends in a verdict or an error.
- **Deep terms**: proofs whose step holds an `or` nested 3,000, 30,000 and
  300,000 deep to the right and to the left, one `or` with that many
  arguments, and that many nested `not`. Each ends in `correct` or in the
  error `the compiled checker stopped without a verdict: Limit`, on both
  builds, the deepest in under a second (release). The two large proofs
  that need more than the default depth
  (`regress3__friedman_n4_i5.smtv1`,
  `regress4__C880mul.miter.shuffled-as.sat03-348.smtv1`): `Limit` at the
  default, `correct` with `--depth=16384` and with `--depth=1000000`, on
  the debug build too.
- **Includes, snapshots, options**: `pathos` skips `include` commands and
  reads no snapshot file (the signature is built in, `main.rs:25-28`), so
  there is no file of either kind to malform. An `include` without a
  string, with a number, or with a control character in its string is the
  front end's error; an unknown option, a `--depth` that is not a number, no
  file or two files give the usage text; a file that does not exist, or a
  directory, the error `cannot include file`.
- **By hand**: an input for every `Fixed`, `Stack` and `Resource` row
  below, given in the row.

### Result

67 rows.

| Verdict | Rows | Meaning |
| --- | --- | --- |
| Safe | 52 | No input reaches it; the row says why. |
| Fixed | 7 | Input reached it at the audited commit: a panic. The commit after it gives an error or ignores the failed write; the row says what reached it and what holds now. See below. |
| Stack | 3 | Recursion whose depth the input or an option controls; the process aborts with `has overflowed its stack`. |
| Resource | 5 | Memory or time the input can make arbitrarily large; the process is killed or does not end. |

#### Fixed

Found by this audit, and one of them (`(as f)`) also by the mutated proofs.
Each panicked in release and debug builds with exit status 101, and each
has a test in `crates/pathos/src/main.rs`
(`a_malformed_annotation_in_a_step_is_an_error`,
`a_member_at_an_instance_of_another_datatype_is_an_error`), except the two
about a failed write, which were tried by hand.

| Input | At the audited commit | Now |
| --- | --- | --- |
| A step with the argument `(as)` or `(as is)`: `(step @p2 (= false false) :rule refl :args ((as)))` | Panic, index out of bounds (`adapter.rs:299`, `:303`) | Error `pathos does not read this proof: a type annotation the checker for CPC has no operator for: ...` |
| With `(declare-datatypes ((List 1) (Box 1)) ((par (X) ((cons (head X) (tail (List X))) (nil))) (par (Y) ((box (unbox Y))))))` and `(declare-const b (Box Int))`: a step with the argument `(as nil (Box Int))`, `(head b)` or `(tail b)` | Panic, index out of bounds (`adapter.rs:1040`, `:1063`) | Error `pathos does not read this proof: nil is used at the type (Box Int), which is not an instance of its datatype` |
| The same datatypes: `(assume @p1 ((_ is cons) b))`, `(assume @p1 (= b ((_ update tail) b b)))`. These terms are well typed: CPC's `is` and `update` do not relate the constructor or selector to the type of the term | Panic, index out of bounds (`adapter.rs:1101`, `:1102`) | The same error, naming `cons` or `tail` |
| `pathos --help > /dev/full`, `pathos --help \| true`, `pathos 2> /dev/full` | Panic, `failed printing to stdout` or `to stderr` (`main.rs:134`, `:138`) | Exit status 0 for `--help`, 1 for the usage error; the failed write is ignored, as for the verdict |

Where the index was in range, the adapter took the member of the other
datatype at that position: with `nil` declared first, `(as nil (Box Int))`
and `((_ is nil) b)` were read as `box` and `(_ is box)`, and a proof with
`((_ is nil) b)` was checked without an error. That was not a panic but
another term than the proof's given to the checker; the same check now
makes it the error above. Whether a proof could get `correct` that way
where Ethos refuses it was not tried. With the fix, `pathos` gives the same
verdict as before on each of the 400 proofs of the safe corpus and the 41
large ones.

#### Open

Nothing in the list panics on a proof or a command line after the fixes.
What remains is not a panic:

1. **Stack** (3 rows). The adapter declares the instances of parametric
   datatypes by a recursion that nests once per block in a chain of blocks
   (`adapter.rs:946`, `:1024`): 5,000 chained `declare-datatypes` commands
   overflow the stack of a debug build, 100,000 that of a release build.
   The other two rows are the compiled checker's recursion when `--depth`
   is set beyond what its 64 MiB stack holds; at the default depth it stops
   with the error `Limit`.
2. **Resource** (5 rows). `pathos` sets no limit of its own on the
   checker's terms and calls; an application with n arguments is converted
   in time quadratic in n; a datatype with a field that is a larger
   instance of itself (`(N (N T))`) does cubic work before the limit of
   10,000 instances stops it; and `--explain` prints a bit-vector digit by
   digit, whatever its width.


### crates/pathos/build.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 9-16 | `println!(`, `.expect("generated/cpc-checker/Cpc.cached.eo is read")`, `.expect("pathos reads CPC")`, `.expect("cargo sets OUT_DIR")`, `.expect("the image is written")` | Safe | The build script runs when pathos is built, on the repository's own `generated/cpc-checker/Cpc.cached.eo` and on Cargo's `OUT_DIR`; no proof and no command line of a run reaches it. A failure here stops the build, not a run of `pathos`. |

### crates/pathos/src/adapter.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 140-142 | `terms: u32::MAX`, `calls: u64::MAX` | Resource | The store is made without the generated checker's limits on terms and calls (also at 1127-1131), so the memory and the time of a check grow with the proof without a bound of pathos's own; only the nesting depth is limited. The run ends by the system's memory limit or not at all, not by a panic. |
| 175 | `self.store.named(name, args)` | Safe | `Store::named` returns `InvalidConstructor` for an unknown name (generated/cpc-checker/src/lib.rs:306) and `Store::construct` for a wrong number of fields (generated/cpc-checker/src/lib.rs:310) or `InvalidHandle` for a term not of the store (generated/cpc-checker/src/lib.rs:182, 313-315); all become the error of `refused` (37-39). |
| 179-181, 196-198 | `.raw(cc::Lit::Numeral(cc::Integer::from(n)))`, `.raw(cc::Lit::String(cc::EoString::from_code_points(points)))` | Safe | `Store::raw` only interns (generated/cpc-checker/src/lib.rs:267, 187-199): a full store is `CheckError::Limit`, returned. `from_code_points` wraps the vector (generated/cpc-checker/src/eostring.rs:27). |
| 207-208 | `self.next_sort += 1`, `self.next_sort as usize` | Safe | Counts the distinct sort terms of the proof converted so far (one per miss of `declared`, 204); the front end's terms have 32-bit identifiers, so there are fewer than 2^32 of them. |
| 223 | `i + 1` | Safe | `i` is a position in the overloads of one name, a vector held in memory. |
| 234 | `while st.ck.store.kind(t) == Kind::APPLY` | Resource | `head` walks the whole spine of a curried application, and `shape` calls it (267) for every application node; `spine` (1211) does the same from `parametric` (1027) and `instance_key` (796) once a parametric datatype is declared. An application of one head to n arguments has n nested application nodes, so its conversion takes n^2/2 steps: `:args ((a a ... a))` with 20,000, 40,000 and 80,000 arguments takes 0.7 s, 2.7 s and 10.6 s (release). Time only, no panic. |
| 235 | `st.ck.store.child(t, 0)` | Safe | `t` has kind `APPLY` (234), and an application has at least its head: `TermStore::mk` refuses other counts (pathos-term/src/store.rs:452-455 with pathos-term/src/kind.rs:105). |
| 266, 275 | `children[0]`, `children.len() - 1` | Safe | `t` is an `Apply` or `ApplyOpaque` node (265), which has at least one child (pathos-term/src/kind.rs:105, enforced by `TermStore::mk`, pathos-term/src/store.rs:452-455). |
| 284-285 | `children[1..=n]`, `children[n + 1..]` | Safe | Line 275 returns an error unless `children.len() - 1 >= n`, so `n + 1 <= children.len()`. |
| 299 | `children[0]` | Fixed | Reached at the audited commit; now a pattern on the two children, and any other number is the error at 306. What reached it: an `AsReturn` node may have any number of children (pathos-term/src/kind.rs:106), and `(as)` builds one with none (pathos-check/src/build.rs:184-193). Such a term has no type, but the arguments of a step are given to the plugin without being typed (pathos-elab/src/cmd_parser.rs:943-959). `(assume @p1 false) (step @p2 (= false false) :rule refl :args ((as)))` panics: index out of bounds, the len is 0 but the index is 0 (release and debug, status 101). |
| 303 | `children[1]` | Fixed | Reached at the audited commit; now the same pattern as 299. What reached it: same path as 299 with one child: `(step @p2 (= false false) :rule refl :args ((as is)))`. `is` is a symbol of CPC whose constructor has arity 1 (302), and the node has only the child 0. Panics: the len is 1 but the index is 1 (release and debug, status 101). |
| 313 | `children[0]`, `children[1]` | Safe | The guard of the arm at 312 is `children.len() == 2`. |
| 353, 369 | `self.store.boolean(*b)`, `self.store.literal(lit)` | Safe | Both only intern (generated/cpc-checker/src/lib.rs:258-272, 187-199) and return `Limit` as an error. |
| 354-362 | `integer(n)?`, `cc::Rational::parse(&q.to_string())`, `cc::BitVec::new(b.size(), &integer(b.value())?)` | Safe | `Integer::parse` and `Rational::parse` return `None` for text they do not read, a zero denominator included (generated/cpc-checker/src/num.rs:32-37, 178-181, 190-197), and the `None` is an error here (358, 1196). `BitVec::new` reduces the value modulo 2^size and allocates nothing of that size (generated/cpc-checker/src/bitvec.rs:14-19); the value comes from a front-end literal and is already below 2^size. |
| 379, 449, 474, 589 | `self.store.construct(c, &[])`, `self.store.construct(c, &[index])`, `self.store.construct(c, &fields)`, `self.store.construct(rule, &[])` | Safe | `Store::construct` returns `InvalidConstructor` when the number of fields is not the constructor's arity (generated/cpc-checker/src/lib.rs:310-312) and `InvalidHandle` for a foreign term (313-315). `Self::constructor` (227-229) only gives user constructors and the `$eo_List` ones, so the `$emb_UOp`, `$emb_Binary` and literal branches (316-351), which also return errors, are not taken. A rule constructor with fields gives the error at 589. |
| 444, 451, 458, 467-468, 476 | `self.store.apply(acc, get(a)?)`, `self.store.apply(fun, get(a)?)`, `self.store.apply(partial, acc)` | Safe | `Store::apply` checks both handles with `view` and interns (generated/cpc-checker/src/lib.rs:287-292); every failure is a returned `CheckError`. A part missing from `memo` is the error of `get` (433-437), not an index. |
| 456-457 | `ts[0]`, `ts[1..]` | Safe | `Shape::Apply` is only made at 296 from the children of an `Apply` node, which has at least one (pathos-term/src/kind.rs:105). |
| 487-488 | `self.next_const += 1`, `self.next_const as usize` | Safe | Counts the distinct constants of the proof converted so far (one per miss of `declared`, 484); fewer than 2^32, as the front end's terms. |
| 590, 595 | `Vec::with_capacity(args.len())`, `Vec::with_capacity(premises.len())` | Safe | The lengths of slices the parser already holds in memory. |
| 605 | `st.ck.store.child(p, 0)` | Safe | `p` has kind `Proof` (599), and a proof node has exactly one child (pathos-term/src/kind.rs:104, enforced at pathos-term/src/store.rs:452-455). |
| 616 | `self.stack.len() - pos - 1` | Safe | `positions` holds, for each formula, exactly the indices at which it stands in `stack`, ascending: `push` (518-524) records `stack.len()` before pushing, and `truncate` (526-534) removes the last index of the formula it pops, which is the top of the stack. These two are the only writers, so `pos < stack.len()`. |
| 667 | `self.next_block += 1` | Safe | A `usize` counting `declare-datatypes` commands read. |
| 717, 728 | `Vec::with_capacity(datatypes.len())` | Safe | The length of a slice the parser holds. |
| 750 | `names[i]`, `bodies[i]` | Safe | `i` comes from `productive_order(&refs)` (747), a permutation of `0..refs.len()` (1244-1262). `refs`, `shapes`, `names` and `bodies` each get one entry per element of `datatypes` (699-710, 718-723, 729-744); an error in between returns before this line. |
| 753-759 | `shapes[i]`, `names[i]`, `inst.constructors[k]`, `shapes[i][k]`, `inst.selectors[k][j]` | Safe | `i` enumerates `datatypes`, and `shapes[i]` has one entry per constructor in `conses` (702-708), which `k` enumerates. `declared_terms` (769-787) returns one constructor and one selector vector per entry of `arities`, taken from `shapes[i]` at 753, with `arities[k]` selectors, the length of `shapes[i][k]` that `j` enumerates. |
| 806 | `self.templates[&key.0]` | Safe | Every `InstanceKey` comes from `instance_key`, which returns one only after `self.templates.get(&head)?` found the head (797). The callers pass `nodes[i]` (872), made of the root (from 1020 or 993) and of keys from `mentioned_instances` (843). Templates are never removed. |
| 846 | `self.templates[&key.0]` | Safe | `key` is what `instance_key` returned at 843; see 806. |
| 864 | `self.templates[&root.0]` | Safe | `root` comes from `instance_key` at 993 (via 1000) or 1020 (via 1024); see 806. |
| 871, 894 | `while i < nodes.len()`, `vec![vec![false; n]; n]` | Resource | A datatype whose field is a larger instance of itself needs instances without end: `(declare-datatypes ((N 1)) ((par (T) ((z) (s (p (N (N T))))))))`, `(declare-const x (N Int))`, `(assume @p1 (= x x))`. The loop stops with an error at 10,000 instances (879-883), but before that each round walks a type one level deeper and compares keys linearly (878, and `found.contains` at 846), which is cubic: the run above is still going after 60 s at about 1 GiB (release). The table at 894 and the search at 911-913 are quadratic and cubic in the same n, at most 10,000. No panic. |
| 872 | `&nodes[i]` | Safe | The loop condition at 871 is `i < nodes.len()`. |
| 898-900 | `uses[x]`, `row[b]` | Safe | `uses` gets one entry per node (888), so it has `n` entries; `x` is `a` (from `0..n`, 895) or a `b` given by `index`, a position in `nodes` (892). `row` has `n` entries (894). |
| 912, 919 | `done[a]`, `reach[a][b]`, `reach[b][a]`, `reach[first][b]`, `reach[b][first]` | Safe | `a`, `b` and `first` range over `0..n`, and `done` and `reach` have `n` entries and rows (894, 907). |
| 922 | `self.next_instance += 1` | Safe | A `usize` counting instances declared, each of which costs far more than one unit of memory. |
| 925-930 | `self.templates[&nodes[m].0]`, `names[m]`, `nodes[m]` | Safe | `m` is an element of `group`, a subset of `0..n` (918-920); `nodes` and `names` have `n` entries (891, 906). The key of a node is in `templates`; see 806. |
| 941 | `fields[m]` | Safe | `fields` gets one entry per node in the loop at 871-890 (887), so `n` entries; `m < n`. |
| 946, 1024 | `self.convert_with(st, ty, &mut memo)`, `self.ensure_instance(st, &key)?` | Stack | `ensure_instance` converts the field types of an instance (946), `convert_with` asks `parametric` for each term (411), and `parametric` calls `ensure_instance` for an instance of another block that is not declared yet (1024). The nesting is as deep as the chain of blocks: 5,000 commands `(declare-datatypes ((Di 1)) ((par (X) ((ci (si (D(i-1) X)))))))` and then `(declare-const x (D4999 Int))`, `(assume @p1 (= x x))` overflow the 64 MiB stack in the debug build; 100,000 of them overflow it in the release build too (status 134, `has overflowed its stack`). |
| 968 | `nodes[m]` | Safe | `m` is an element of `group`; see 925-930. |
| 977-978 | `names[group[g]]`, `bodies[g]` | Safe | `g` comes from `productive_order(&refs)` (973), a permutation of `0..refs.len()`. `refs` and `bodies` get one entry per member of `group` (964-965); a failed conversion leaves the loop early, and then 970-972 returns before this line. So `g < group.len()`. |
| 981-985 | `fields[m]`, `names[m]`, `nodes[m]`, `done[m]` | Safe | `m` is an element of `group`, below `n`; all four have `n` entries. |
| 1025 | `self.instances[&key]` | Safe | `ensure_instance` returned `Ok` at 1024: either the key was there (861), or the loop at 908-987 ended, which it does only when every node, the root first among them (867), is `done`, and a node is `done` only after its instance is inserted (984-985). Instances are never removed. |
| 1032-1038 | `c[0]`, `c[1]` | Safe | `annotated` is `Some` only if the filter at 1031-1033 holds, which tests `c.len() == 2` before `c[0]`. |
| 1040 | `self.instances[&key].constructors[k]` | Fixed | Reached at the audited commit; now `member` looks the constructor up in the instance only if the instance's template is the constructor's own, and gives the error `... is used at the type ..., which is not an instance of its datatype` otherwise. What reached it: `k` is the constructor's position in its own datatype, but the instance is the one of the annotation's type, which nothing here ties to that datatype; the front end would refuse the term when typing it, and a step's arguments are not typed (pathos-elab/src/cmd_parser.rs:943-959). With `(declare-datatypes ((List 1) (Box 1)) ((par (X) ((cons (head X) (tail (List X))) (nil))) (par (Y) ((box (unbox Y))))))`, `(assume @p1 false)`, `(step @p2 (= false false) :rule refl :args ((as nil (Box Int))))`: panics, the len is 1 but the index is 1 (release and debug, status 101). `self.instances[&key]` itself is safe as at 1025 (`instance_of_type` returns after `ensure_instance`, 1000). |
| 1049 | `self.instances[&key].constructors[k]` | Safe | The instance is the one of the type that `type_of` computes for `t` (1046), an application whose head is the constructor. A constructor's type is a function to its own datatype applied to its parameters (pathos-elab/src/cmd_parser.rs:551), so a type with a template at its head has the constructor's own template there, and `k` is below that template's number of constructors: an instance has one constructor per constructor of its template (814, 981-983, 773-775). A partial application has a function type, for which `instance_key` gives nothing and 993-998 an error; an ambiguous constructor has a type that does not reduce without its annotation, and with it takes the path of 1034. |
| 1063 | `self.instances[&key].selectors[k][j]` | Fixed | Reached at the audited commit; now through `member`, as 1040. What reached it: the instance is the one of the operand's type, and the operand of a selector in a step's argument is not checked against the selector's type (arguments are not typed, pathos-elab/src/cmd_parser.rs:943-959). With `(declare-datatypes ((List 1) (Box 1)) ((par (X) ((nil) (cons (head X) (tail (List X))))) (par (Y) ((box (unbox Y))))))`, `(declare-const b (Box Int))`, `(assume @p1 false)`, `(step @p2 (= false false) :rule refl :args ((head b)))`: panics, the len is 1 but the index is 1 (release and debug, status 101). With `cons` declared first, `(tail b)` panics on the second index. |
| 1075 | `c[0]`, `c[1]` | Safe | Line 1072 returns unless `c.len() == 2`. |
| 1077 | `args[0]`, `args[1..]` | Safe | The branch is taken only if `args.len() >= 2` (1076). |
| 1099 | `self.instances[&key]` | Safe | `instance_of_type` returned `Ok` at 1098, after `ensure_instance` (1000); see 1025. |
| 1101-1102 | `inst.constructors[k]`, `inst.selectors[k][j]` | Fixed | Reached at the audited commit; now through `member`, as 1040. What reached it: a tester or an updater names a constructor or selector of one datatype and is applied to a term of any type: in CPC `is` and `update` do not relate the two (`(declare-parameterized-const is ((C Type :implicit) (D Type :implicit) (c C :opaque)) (-> D Bool))`), so the term is well typed, in an assumption too. With the datatypes and `b` of 1063: `(assume @p1 ((_ is cons) b))` panics at 1101, and `(assume @p1 (= b ((_ update tail) b b)))` at 1102, both with the len is 1 but the index is 1 (release and debug, status 101). |
| 1119, 1155, 1186 | `cc::with_checker_stack(`, `self.store.check_proof(assumptions, commands)` | Stack | The generated functions recurse over the terms, on a thread of 64 MiB (generated/cpc-checker/src/lib.rs:121, 1150-1158), and stop with `CheckError::Limit` at `Limits::depth`. The default depth (144) is sized for that stack and gives the error; `--depth=N` (main.rs:74, 105, and 1125-1131 here) raises the limit without the stack. An assumption of 300,000 nested `not` gives `Limit` by default and, with `--depth=4000000000`, a stack overflow (status 134; release and debug; also with `--profile`). A panic on that thread would come back as `CheckError::Worker` (generated/cpc-checker/src/lib.rs:1156-1157), an error and not status 101. |
| 1162 | `label[i + 1..]` | Safe | `i` is where `find` saw `"(rule "`, so the byte at `i` is the ASCII `(` and `i + 1` is inside the string and on a character boundary. |
| 1168-1169 | `e.0 += t`, `e.1 += 1` | Safe | A sum of `f64` and a count of labels, which are in memory. |
| 1211 | `while st.ck.store.kind(t) == Kind::APPLY` | Resource | `spine` walks and copies the whole spine for each node `parametric` (1027) and `instance_key` (796) are asked about; quadratic in the number of arguments of one application, as `head` at 234. |
| 1213-1214 | `children[1..]`, `children[0]` | Safe | `t` has kind `APPLY` (1211), so it has at least one child (pathos-term/src/kind.rs:105). |
| 1250 | `refs[d]` | Safe | `d` is an element of `remaining`, which starts as `0..refs.len()` (1246) and only loses elements. |
| 1258 | `order.splice(0..0, ready)` | Safe | The empty range at the start is in bounds for any vector. |
| 1288, 1307, 1318, 1338 | `self.built.borrow_mut()`, `.borrow_mut()` | Safe | Each hook borrows `built` for its own duration only, and hooks do not nest: `State::with_plugin` takes the plugin out of the state while a hook runs (pathos-elab/src/plugin.rs:186-190), so nothing the hook does to the state calls a hook, and the `Adapter` has no evaluation hooks. `Built`'s methods get the state but not the `Rc`. The only other borrows are `main.rs:105-118`, made before and after `include_file`, not during it. |
| 1294 | `st.ck.store.child(e, 0)` | Safe | `e` has kind `Proof` (1291), which has exactly one child (pathos-term/src/kind.rs:104). |

### crates/pathos/src/explain.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 28 | `b.to_string_base(2)` | Resource | The text of a bit-vector has as many digits as its width (generated/cpc-checker/src/bitvec.rs:53-60), and the front end computes literals of any width: `(assume @p1 false)`, `(step @p2 (= (eo::to_bin 3000000000 1) (eo::to_bin 3000000000 1)) :rule refl :args (false))` is `incorrect` in 0.02 s and 8 MB without `--explain`, and with it is killed at the 4 GiB cap (status 143). No panic. |
| 33, 40 | `depth - 1` | Safe | Line 21 returns when `depth == 0`. The recursion is at most 12 deep: both callers pass 12 (68, 77). |
| 58, 63, 84, 104, 111 | `g::eo__24eo_5finvoke_5fassume_5flist(s, nil, assumptions)`, `g::eo__24eo_5finvoke_5fcmd(s, state, cmd)`, `g::eo__24eo_5fstate_5fis_5frefutation(s, state)` | Stack | The generated functions, run on the checker's 64 MiB thread (adapter.rs:1119, 1155): their recursion is bounded by `Limits::depth`, which `--depth=N` can set beyond what the stack holds. See adapter.rs:1186. |
| 77 | `fields[0]` | Safe | `destruct` gives the fields of a `$emb_s.cons` node (generated/cpc-checker/src/lib.rs:386), and a node is only made by `construct` with as many fields as its arity (generated/cpc-checker/src/lib.rs:310), which is 2 for `$emb_s.cons` (generated/cpc-checker/src/schema.rs:4031). |
| 105 | `Vec::with_capacity(commands.len())` | Safe | The length of the command list the adapter holds. |

### crates/pathos/src/main.rs

| Line | Construct | Verdict | Why |
|---|---|---|---|
| 74 | `a["--depth=".len()..]` | Safe | The guard on the same line is `a.starts_with("--depth=")`, so the prefix is in the string and ends on a character boundary; an unreadable number is `None` (`.ok()?`), the usage text. |
| 105, 110, 113, 115, 118 | `built.borrow_mut()`, `built.borrow()` | Safe | Each borrow is a temporary of its statement, and none is alive during `include_file` (107), the only time the adapter's hooks borrow (adapter.rs:1288-1338). |
| 134 | `print!("{USAGE}")` | Fixed | Reached at the audited commit; now written as the verdict is, ignoring a failed write. What reached it: `print!` panics when the write fails: `pathos --help > /dev/full` (failed printing to stdout: No space left on device) and `pathos --help \| true` (Broken pipe) end with status 101, release and debug. A closed standard output (`>&-`) is ignored by the standard library, status 0. The verdict and the errors go through `write_line` (48-52), which ignores a failed write. |
| 138 | `eprint!("{USAGE}")` | Fixed | Reached at the audited commit; now written as the errors are, ignoring a failed write. What reached it: `eprint!` panics when the write fails: `pathos 2> /dev/full` (no file given, so the usage text is printed) ends with status 101, release and debug. |
