# Gates 6 and 7: large proofs and options

Run 2026-11-13 on `main`, with harness `daniel-larraz/ethos` `5c93fa35`, by a
separate Claude session (Opus 5.5). pathos was not changed for these gates.

## Gate 6: large proofs

`scripts/difftest large`: the 43 proofs of 1 MB or more that cvc5 `2107a003`
produces for the unsat benchmarks of `regress1` to `regress4` (331 tried).
Sizes range from 1.1 to 453 MB, median 2.2 MB.

- **Agreement:** 43 of 43. Ethos accepts 37, reports 4 as incomplete and
  rejects 2 (`regress4__miplib-pp08a-3000`, both variants, with a type
  error); pathos does the same, with the same messages.
- **Performance** (three jobs at a time, so approximate): over the 41
  accepted proofs pathos takes 270 s against Ethos's 667 s (40%).

| Proof | Ethos | pathos |
| --- | --- | --- |
| `regress3__hole10.cvc` (453 MB) | 403 s, 24.3 GiB | 162 s, 3.7 GiB |
| `regress4__bug143.smtv1` (29 MB) | 172 s, 2.6 GiB | 63 s, 0.4 GiB |
| `regress3__hole9.cvc` (52 MB) | 37 s, 2.8 GiB | 18 s, 0.5 GiB |

`scripts/difftest perf` now includes this corpus. Its 30-minute timeout
(`LARGE_TIMEOUT` in `difftest.env`) leaves room for the largest proof.

## Gate 7: options

`scripts/difftest options`: the 230 regressions and 400 default-corpus proofs,
each under each of Ethos's eight non-default options and under all eight
together, plus the default run: 6,300 runs.

- **Agreement:** 6,300 of 6,300.
- One run needs a long timeout: `corpus/regress1__auflia__bug330.cpc` under
  all eight options prints 1.77 GB of error output (`--no-print-dag` prints
  terms without sharing). Ethos takes 179 s, pathos 8.5 s; the outputs were
  checked byte for byte outside the harness too. `OPTIONS_TIMEOUT` is 600 s.

Not covered: the `--stats` options (their output contains timings), `--help`,
`--show-config`, and `--include=` and `--reference=` on the command line.
