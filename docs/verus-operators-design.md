# Design: a specification of the `eo::` operators (milestone 25)

Milestone 25 of [brief.md](brief.md) asks for the form of the specification
to be written down, and for a stop for review, before anything is proved.
This is that document, as it was reviewed. All five decisions at its end
were approved as recommended (Daniel, 15 November 2026). What came of it,
and where the result departs from it, is in
[verus-spike.md](verus-spike.md#milestone-25-the-operators-are-correct-pilot-in-part).

It answers the brief's three questions (how the signature's tables are
taken, how Stuck is represented, what is left out), says what the theorems
would be, and lists what probing the reference binary has already shown to
differ from the plugin's definitions. The decisions I need are at the end.

## The sources

- `plugins/desugar/eo_desugar_native.eo`: the literal operators, as
  programs over an embedding of terms (`$eot_numeral`, `$eot_binary w n`,
  ...) and "native" functions (`$native_zplus`, `str.substr`, ...).
- `plugins/desugar/eo_desugar.eo`: the list operators, as recursive
  programs over applications `(f x y)`, with two tables that eoc generates
  for each signature: `$eo_nil f T` (the terminator of `f` at type `T`) and
  `$eo_is_list_nil f nil`.
- The reference binary, which decides where the two disagree.
- What pathos has: `Val` and `eval_spec` in `lit.rs` (12 operators),
  `tree`, `inst` and matching in `store.rs` and `matching.rs`.

## The form: two layers

### Layer 1: values

```
spec fn lit_spec(op: EvalOp, args: Seq<Val>) -> Option<Val>
```

`Val` is what a literal stands for; it exists since milestone 17 and has a
constructor for each of pathos's seven kinds of literal. Two things change:

- A string becomes its sequence of code points, `Val::String(Seq<int>)`.
  Today it holds the `EoString` itself, which says nothing.
- `lit_spec` is total: `None` means the application does not evaluate.
  Today's `eval_spec` has three answers, the third being "not specified
  here"; that answer goes away for the operators in scope, and `eval_spec`
  is replaced, not kept beside the new function.

`lit_spec` is transcribed from `eo_desugar_native.eo`, one `match` arm for
each case of each program, with the `$native_` functions written as
arithmetic on `int` and `real` and the string functions as the SMT-LIB
definitions on sequences (`str.len`, `str.++`, `str.substr`, `str.indexof`
from 0, `str.to_code`, `str.from_code`). The arms carry the name of the
program they come from, so the two can be read side by side.

The theorem is exact:

> `Lit::evaluate(op, args)` returns `Some(v)` exactly when
> `lit_spec(op, args@)` is `Some(v@)`, and `None` exactly when it is
> `None`.

### Layer 2: terms

```
spec fn op_spec(op: EvalOp, args: Seq<Tree>) -> Option<Tree>
spec fn list_op_spec(op: EvalOp, f: Tree, nil: Tree, left: bool, args: Seq<Tree>) -> Option<Tree>
```

`Tree` is the store's view of a term (milestone 19). `op_spec` covers the
operators that look at more than values:

- a literal operator on arguments that are all literals is `lit_spec` on
  their values, and its result the literal with that value;
- `eo::eq` on two values is whether their trees are equal (which, by the
  store's theorem, is whether they are the same term);
- `eo::is_z`, `is_q`, `is_bin`, `is_str`, `is_bool`, `is_var` test the kind
  of the argument's tree;
- the list operators are `list_op_spec`, below.

The theorem for the entry point in `eval.rs`, for an operator in scope and
a run that did not end in a fatal error:

> `evaluate_literal_op_internal(op, args)` returns `Some(t)` exactly when
> the specification gives `Some(tree(t))` on the trees of `args`, and
> `None` exactly when it gives `None`.

## Stuck

**`None` is "the application stays as it is".** That is what Ethos and
pathos do: an operator that does not apply leaves `(eo::add x 1)` in the
term, where it can still be matched, substituted into and printed. The
specification does not build that term; the caller does (`evaluate`,
`mk_expr`), and saying what it builds belongs to S2 and S4.

Three kinds of argument make an operator not apply, and the specification
has a clause for each, taken from the binary:

1. **An argument that is not ground** (it contains a parameter): `None`,
   for every operator in scope. logos has no counterpart; its functions
   run on closed terms.
2. **An argument that is itself unevaluated** (it contains an `eo::`
   application or a program symbol; the store's "evaluatable" flag, which
   needs a specification on trees as "ground" got one in milestone 19):
   `None`, except for the `eo::is_*` tests, which give `false`. This is
   logos's `Stuck` passing through: there an unevaluated argument *is*
   `Stuck`, a program applied to `Stuck` is `Stuck`, and
   `$eo_is_z t` is `is_ok t` and the test.
3. **Values the operator has no case for**, or a case that gives
   `$eot_stuck` (division by zero, a width that is negative): `None`.

So the relation to logos, as it would be stated in the report: on closed
arguments, the specification gives `None` exactly where the plugin's
program is stuck, and otherwise the same value, **except for the listed
differences**. It is a statement about two texts read side by side, not a
theorem: there is no Lean on this side and no Verus on that one.

## The signature's tables

A list operator `(eo::list_concat f a b)` needs to know that `f` builds
lists, whether they nest to the right or to the left, and what ends them.
In the plugin that is the two generated tables. In pathos it is the
attribute of `f` (`RightAssocNil` and the like) and the term that goes with
it, in the checker's table `app`.

**The specification takes them as arguments, already resolved**:
`list_op_spec(op, f, nil, left, args)`. It is then a function of trees
alone, transcribed from `eo_desugar.eo` with `nil` and `left` where the
plugin calls its tables:

```
spec fn elements(f, nil, left, t: Tree) -> Option<Seq<Tree>>   // $eo_is_list and $eo_get_elements_rec
spec fn build(f, nil, left, es: Seq<Tree>) -> Tree
... one function for each $eo_list_*_rec
```

The theorem for `evaluate_list_op_with(k, args, op, nil, is_left)`, the
function that runs once the terminator is known, is exact as above.

What connects the tables to it is a second, smaller statement about
`evaluate_list_op`, which finds the terminator:

- **When the term that goes with the attribute is not parameterized**, it
  is the terminator: `nil` is that term. This is complete in this
  milestone. `or`, `and` and `eo::List::cons` are of this kind.
- **When it is parameterized**, the terminator depends on a type: for
  `bvor` on `(BitVec 4)` it is `#b0000`. pathos computes it by typing an
  argument, matching the operator's type against it, and evaluating the
  term's body (`evaluate_nil`). Saying what the *right* terminator is needs
  the specifications of typing and of evaluation, which are S3 and S2.
  **For these operators this milestone proves the result relative to the
  terminator found**: "if `evaluate_nil` gave `nil`, the result is
  `list_op_spec(..., nil, ...)`". That `nil` is the right one is left
  open, and said so.

`eo::nil` itself is the table lookup: complete for the first kind,
left out for the second.

## What is specified, and what is left out

In scope, 46 operators:

| Group | Operators |
| --- | --- |
| Boolean and bit-wise | `not`, `and`, `or`, `xor` |
| Arithmetic | `add`, `mul`, `neg`, `pow`, `log`, `zdiv`, `zmod`, `qdiv`, `is_neg`, `gt` |
| Strings and bit-vectors | `len`, `concat`, `extract`, `find` |
| Conversions | `to_z`, `to_q`, `to_bin`, `to_str` |
| Tests | `is_z`, `is_q`, `is_bin`, `is_str`, `is_bool`, `is_var` |
| Equality | `eq` |
| Lists | `nil` (not parameterized), `cons`, `list_len`, `list_concat`, `list_nth`, `list_find`, `list_erase`, `list_erase_all`, `list_rev`, `list_setof`, `list_minclude`, `list_meq`, `list_diff`, `list_inter`, `list_singleton_elim`, `list_singleton_intro`, `list_repeat` |

Left out:

| What | Why |
| --- | --- |
| `eo::ite`, `eo::requires`, `eo::is_ok`, `eo::is_eq` | They are about evaluation: what was evaluated, and what "stuck" means for a term in the middle of it. S2. |
| `eo::typeof`, `eo::nameof`, `eo::dt_constructors`, `eo::dt_selectors`, `eo::var` | Typing and the datatype tables. S3. |
| `eo::hash`, `eo::cmp` | As the scope document says: functions with only the term-order properties. |
| The terminator of a parameterized list operator, and `eo::nil` for one | Above. S2 and S3. |
| `list_singleton_intro` and `list_repeat` when they need the type of an element to find the terminator | The same: they are specified given the terminator. |
| An operator applied to a number of arguments `check_arity` refuses | Ethos reads past the end of its arguments there and pathos stops with an error ([ethos-differences.md](ethos-differences.md)). The specification is for the numbers `Checker::takes` allows. |
| What the caller builds when the answer is `None` | S2 and S4. |

`eo::is_var` is in: the plugin defines it through `eo::nameof` and
`eo::typeof`, the binary tests the kind, and the two agree. The
specification takes the binary's form.

## Where the binary differs from the plugin, so far

Found by running the reference binary on one-line inputs; pathos agrees
with the binary on all of them. The report will have the full list, each
with its input. These are the kinds of difference, so that the form of the
specification can be judged against them:

| Difference | Input | Binary | Plugin |
| --- | --- | --- | --- |
| Decimals are a kind of their own | `(eo::add 1.5 2.5)` | the decimal 4 | has no decimals; `1.5` is a rational |
| A decimal and a rational do not mix | `(eo::add 1.5 1/2)` | stays | 2 |
| Hexadecimals are a kind of their own | `(eo::add #x1 #x1)` | `#x2` | has one kind of bit-vector |
| A hexadecimal and a binary do not mix | `(eo::add #x1 #b0001)` | stays | `#b0010` |
| `eo::to_z` has no case for a hexadecimal | `(eo::to_z #xf)` | stays | 15 |
| `eo::gt` does not compare widths | `(eo::gt #b10 #b001)` | `true` | stuck (widths differ) |
| `eo::extract` cuts the upper index | `(eo::extract #b1010 1 9)` | `#b101` | a 9-bit value |
| A negative exponent | `(eo::pow 2 -1)` | stays | the "total" power, a value (to be confirmed) |

The first five say that pathos's `Val` needs its seven kinds where the
plugin has five; `lit_spec` is written on seven, and the report says which
arms have no counterpart. None of them is a reason to change the form.

Not yet checked, and likely to add rows: the list operators on lists that
nest to the left (the plugin's programs only take `(f x y)` apart with the
element first), on elements that are themselves unevaluated (the plugin
compares with `eo::eq`, which is stuck on them; pathos compares handles),
and `eo::log` at its edges.

## The proofs, and what they need

**`Lit::evaluate`.** The 12 operators of milestone 17 are re-stated against
`lit_spec`, which should be mechanical. The others need:

- **Strings.** `EoString` is a wrapper around `Vec<u32>` that Verus does
  not look into. It gets a view, the sequence of its code points, and its
  functions are **proved**, since they are loops over a vector: `len`,
  `is_empty`, `concat`, `substr`, `find`, `code_points`,
  `from_code_points`. `parse`, which reads escapes from text, stays
  trusted without a contract; it is the parser's side.
- **Numbers.** `Integer::pow` and the logarithm (`integer_floor_log`) get
  contracts stating the mathematical function, as the other `malachite`
  wrappers have. They stay trusted.
- **Bit-vectors on `int`.** `add`, `mul`, `neg`, `zdiv`, `zmod`, `gt` and
  `to_bin` on bit-vectors reduce to arithmetic modulo `2^w`, of which
  `bitvec.rs` has the lemmas.

**The list operators.** Each `list_*` function in `eval.rs` reads its
arguments into vectors (`get_nary_children`), works on the vectors, and
builds a term (`prepend_nary_children`). So the proof is in three parts,
shared by all of them:

1. `get_nary_children` returns `elements(...)`: the vector's view is the
   specification's sequence.
2. `prepend_nary_children` returns `build(...)`.
3. For each operator, that its work on vectors is the plugin's recursion on
   lists. For most this is a short induction. Two are not short:
   `list_minclude` and `list_meq` count occurrences in hash maps where the
   plugin erases one element at a time, so the proof is that the two
   notions of "contained as a multiset" agree; and `list_setof`, where the
   plugin erases later duplicates recursively.

The store's `tree` and the theorem "same tree, same term" carry the step
from handles to trees. A new one is needed: a specification of the
"evaluatable" flag on trees, proved in the store as `is_ground` was.

## What it would cost

The scope document has 800 to 1,500 lines of proof for S1. From the above:

| Part | Specification | Proof |
| --- | --- | --- |
| `lit_spec`, 22 operators on 7 kinds | 250 to 350 | |
| `Lit::evaluate` against it | | 300 to 500 |
| `EoString` | 60 to 100 | 150 to 250 |
| "Evaluatable" on trees | 30 | 100 to 150 |
| `list_op_spec`, 17 operators | 200 to 300 | |
| The three shared parts and the short operators | | 300 to 500 |
| `list_minclude`, `list_meq`, `list_setof` | | 200 to 400 |

That is 540 to 780 lines of specification and 1,050 to 1,800 of proof: the
upper half of the scope document's range, or over it. The report will give
the cost per operator, separately for the two groups, as the brief asks.

## What I need decided

1. **Parameterized terminators.** Prove the list operators relative to the
   terminator found, and leave "it is the right one" to S2 and S3
   (recommended)? The alternative is to leave every list operator whose
   head has a parameterized terminator out of this milestone, which says
   less for the same proof.
2. **Decimals and hexadecimals.** Specify them as the binary treats them,
   seven kinds, and list each arm that the plugin does not have
   (recommended)? The alternative, a specification on the plugin's five
   kinds with decimals and hexadecimals excluded, would leave out literals
   that a proof may contain.
3. **The list operators' transcription.** Recursive functions on trees,
   one for each `$eo_list_*_rec`, as close to the plugin's text as Verus
   allows (recommended), with the sequence form as lemmas where the proofs
   want it? Or the sequence form as the specification, which is shorter
   and easier to prove but further from the source a reviewer compares it
   with?
4. **Exactness.** The theorems as stated: the code returns `None` exactly
   when the specification does (recommended). The weaker form, "what the
   code returns is what the specification gives", would let pathos leave
   unevaluated something the specification evaluates, without the proof
   noticing.
5. **`eval_spec` is replaced**, not extended beside a second function, so
   milestone 17's statements about the 12 operators are restated in the new
   form. Nothing proved is dropped.
