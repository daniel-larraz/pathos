# Design: verifying the evaluator (milestone 21)

Milestone 21 of [brief.md](brief.md) asks for the design to be written
down before anything is proved, and to stop for review if it needs more
than moving code. **It does need more than moving code**, in three places.
This file says what the split would be, what it costs, and what needed
deciding.

**Decided** (Daniel, 15 November 2026), and what came of it:

1. **Option A**: the evaluator stays methods of `Checker`. Done.
2. **Shapes: measure a check in `TermStore::mk` first**, and keep it if it
   costs under about 1%. It costs 0.2% at most, so the check is in, and
   `shapes_ok` is part of the store's proved invariant, not an assumption
   about every builder of terms.
3. **`get_type` and the plugin are trusted**, with the contracts below.
4. **Two milestones.** Milestone 21 is everything but `evaluate`;
   milestone 22 is `evaluate`, the frame stack and its two `unreachable!`.

The result of milestone 21, with the measurements and what differs from
this design, is in
[verus-spike.md](verus-spike.md#milestone-21-the-evaluators-operators-cannot-panic).
Milestone 22 proved `evaluate`; its result is in
[verus-spike.md](verus-spike.md#milestone-22-evaluate-cannot-panic). The
invariant there is stated on the order of handles, not as "The invariant,
as I would state it" below has it, and it says why.
The rest of this file is the design as it was reviewed.

## What stands in the way

`eval.rs` is 970 lines of methods of `Checker`. Matching (milestone 18)
could be moved out because it reads only the store. The evaluator cannot:

- it builds terms, so it needs the store mutably;
- it calls typing (`get_type`, 6 places), the plugin's hooks, warnings (8
  places, each formatting terms with `show`), the program table, the
  attribute table (`app_info`), the `eo::hash` table and the statistics;
- it calls itself through `evaluate_nil`, and typing calls it back.

And Verus does not accept the `Checker` type as it is. I tried: it stops at
`Box<dyn FnMut(&str)>` and `Option<Box<dyn EvalPlugin>>` ("does not
support dyn with more than one trait"), before it gets to the hash maps of
`AppInfo` and `String`.

## The three things that are more than moving code

### 1. `Checker` has to become a type Verus can see

Two ways:

**A. Keep the evaluator as methods of `Checker`, and make `Checker`
visible.** (Recommended.)

- Wrap the two boxed trait objects in small types of their own
  (`Warnings`, `Plugin`) that Verus treats as opaque. `AppInfo`, `Stats`,
  `Options` and `PluginEvent` are marked opaque too.
- `Checker` keeps its fields and their names. The evaluator stays where it
  is and still writes `self.store.mk(..)`.
- Everything the evaluator calls that is not verified gets a contract and
  is trusted: see the table below.
- Change to shipped code: two wrapper types and the places that touch
  those two fields (12 outside `eval.rs`). No behaviour.

**B. Move the evaluator out, generic over a trait** (`EvalHost`) that
`Checker` implements, as the brief suggests.

- The verified code would see only the trait: the store through accessor
  methods, and one method per side effect.
- Cost: every `self.store.x(..)` in the evaluator (49 places) goes through
  an accessor; Verus has to relate the store before and after each trait
  call through specification functions of the trait; and I have not yet
  checked how well the attribute syntax this branch uses supports traits
  with specifications.
- Gain: the trusted surface is one trait, in one place.

Both give the same guarantees. A changes less code and keeps the evaluator
readable; B draws a sharper line. I would start with A and fall back to B
only if Verus rejects more of `Checker` than the two fields.

### 2. Shapes become part of what is assumed of the whole store

The evaluator indexes terms without looking: `args[0]` of an application,
`child(nil, 1)` of a parameterized terminator, `cchildren[0]` to `[2]` of
an `eo::ite`. These are safe because of how terms are built (an
application has a head), not because of anything the store enforces:
`TermStore::mk` builds a term with any number of children.

Milestone 20 made the snapshot reader check these shapes
(`NodeKind::takes`). To prove the evaluator they have to hold for **every
term in the store, at all times**:

- a new invariant of the checker, `shapes_ok`: every term has a number of
  children its kind can have;
- the verified evaluator proves it keeps it (it rebuilds a term with the
  same kind and number of children, or builds binary applications);
- every unverified caller of `mk` (the parser, `build.rs`, typing, the
  `eoc` stages) is **trusted** to keep it. That is a real assumption, and
  a new one. It is what `docs/panics.md` argues row by row today.

The alternative is to make `mk` check the number of children. It cannot
return an error (its callers are everywhere), so a wrong shape would have
to become a recorded failure like the size limits are. That changes
shipped code on the hottest path, and I do not recommend it for this
milestone.

### 3. Two `unreachable!` need a real invariant

`evaluate` contains

```rust
let Some(args) = cchildren.iter().copied().collect::<Option<Vec<Term>>>() else {
    unreachable!("children of an application are evaluated first")
};
```

twice. Proving that this is not reached is proving that the traversal
works: when a term is looked at the second time, each of its children has
a value. This is the invariant the brief asks for, and it is of the same
kind as the one for `match_terms` in milestone 19, but for a stack of
frames, each with its own work list and cache, and with `eo::ite`
evaluating its branches late.

## The invariant, as I would state it

For the checker: `store.wf()`, `shapes_ok`, and the builtin handles
(`t_true`, `list_nil`, ...) are terms of the store.

For the frame stack, one predicate `frames_ok(store, estack)`: for every
frame,

- `init`, every key and value of `ctx`, every term on `visit`, every key
  and every value of `visited`, and every term of `result_key` is a term
  of the store;
- `visit` is not empty while the frame is being worked on, and `init` is
  at its bottom;
- for every term `x` with `visited[x] == None` (expanded, not yet
  evaluated): every child of `x` either has a value in `visited` or is on
  `visit` above some occurrence of `x`; for `eo::ite`, this is required of
  the condition only, and of a branch once it has been pushed;
- for every frame but the top one, the term on top of its `visit` is the
  program application the frame above is computing.

And for the cache of program applications: every key is a list of terms of
the store and every value, if any, a term of the store.

## What would be trusted, with its contract

Each is a method of `Checker` marked `external_body`. "Keeps the checker"
means: `store.wf()` and `shapes_ok` still hold, the store only grew
(`extends`), and the builtin handles are unchanged.

| Method | Contract |
| --- | --- |
| `warn`, `show`, `show_list`, `count_program`, `missing_argument` | The store is unchanged. (`missing_argument` sets `fatal`.) |
| `plugin_evaluate`, and the plugin's `evaluate_program` | Keeps the checker; a term returned is a term of the store; a context filled holds terms of the store. The plugin may call back into the checker: this is the largest assumption. |
| `get_type` | Keeps the checker; a type returned is a term of the store. Typing calls `evaluate`, so until typing is verified this assumes what is being proved, one level down. |
| `get_program` | A program returned is a term of the store with the shape of a program (`is_program`). True from text by the parser, and from a snapshot by milestone 20's check. |
| `app_info`, `attribute_kind` | A `cons` term returned is a term of the store. |
| `get_hash` | The store is unchanged. |
| `mk_bool`, `mk_numeral`, `mk_true`, `mk_false`, `mk_type`, `mk_list`, `mk_list_cons` | Could be verified instead of trusted: they are one or two calls into the store. |
| `match_terms`, `Lit::evaluate`, the store | Verified already. |

Also assumed: Verus's model of `HashMap` for keys `Term` and `Vec<Term>`
(that their derived `Hash` agrees with `==`).

## What would not be proved

- **Termination.** Programs need not terminate. A later proof of partial
  correctness would add a fuel parameter in the specification only: the
  evaluator "returns `r` within `n` program applications", with `n` the
  number of frames pushed. Within one frame the work list does end, by the
  measure milestone 19 used for matching (the sum of the sizes of the
  terms on `visit`), adjusted for terms being pushed back.
- **That the stack does not overflow** through `evaluate_nil` calling
  `evaluate`: this is one of the three recursions `docs/panics.md` lists
  under "Stack".
- Correctness of any result.

## Behaviour

Nothing in the plan changes what runs, apart from the two wrapper types.
The order of warnings and statistics is the order of the calls, which are
not moved. Rewrites that Verus will ask for (iterator chains to loops, as
in every milestone so far) keep the order of evaluation; I would check the
`options` gate, which covers `--stats`, as well as the quick gates.

## Cost

From milestones 18 to 20: reading code costs little once the store's
contracts are there; an explicit stack with a "what is still owed"
invariant cost about nine lines of specification and proof per line of
loop for `match_terms`.

| Part | Code | My estimate, specification and proof |
| --- | --- | --- |
| Making `Checker` visible, the trusted contracts, `shapes_ok` | about 60 lines touched | 200 to 300 lines |
| `evaluate` (the frame stack) | 200 lines | 1,200 to 1,800 lines |
| `evaluate_literal_op_internal` and the small helpers | 250 lines | 300 to 500 lines |
| The list operators (`evaluate_list_op`, the n-ary helpers, datatypes) | 400 lines | 500 to 900 lines |

About 2,200 to 3,500 lines, which is in the range milestone 17 gave for
the evaluator (2,500 to 3,500). It is several times the work of any
milestone on this branch so far. A natural cut, if one is wanted: the
checker's visibility, the contracts and the operators first (everything
but `evaluate` itself, which is then trusted for one milestone), and the
frame stack as a milestone of its own.

## What I need decided

1. **A or B** for making the checker visible. I recommend A.
2. **`shapes_ok` as a trusted invariant** of every unverified builder of
   terms, or a check in `mk`. I recommend the trusted invariant.
3. **`get_type` and the plugin as trusted**, with the contracts above,
   knowing that typing calls the evaluator back.
4. **One milestone or two.** I recommend two, cut as above.
