# Review: milestone 15, every platform Ethos supports

Reviewed branch `m15` at 77e289a (commits d23c2b1 to 77e289a, with the
reviewer's harness pins d97cdda and 3ed5aaa).

## Results

- CI run 43637950215 (69f7ece; 77e289a adds `docs/evidence.md` only):
  every step of every job green on the six platforms of Ethos's CI. On
  each, `tests` 230, `cli` 1,192 (on Windows 4 and 3 of them accepted Ethos
  crashes), `bignum` 7 agree, the fuzz replay has none still differing
  (39 of 41 replayed; two need the corpus), the probe finds no
  differences. On Windows also `tests` 230 on a CR LF checkout. Read by
  the reviewer in the job logs.
- Fable's local `scripts/full-check` (no `--quick`) and `scripts/difftest
  eoc`: all agree (numbers in `docs/evidence.md`); the reviewer did not
  rerun them, since the code that changed is platform code that the Linux
  gates already exercised in CI.

## How the platforms were reached

Four CI runs. The harness, which ran on Linux only, was ported by the
reviewer (87665c6: process groups, `wait4`, `resource`, `prlimit`, GNU
time, `.exe`, MSYS2's CMake generator) and given, from the runs:
`accepted-run.json`, per-platform accepted differences with the exact
output of both sides (Ethos's uncaught `filesystem_error` on a missing
file on Windows); the UCRT abort status `0xC0000409` taken out of the
fuzzer's crash table; and command-line cases for `0xFF` and other bytes
above 127 (harness 500f12f).

What Ethos does differently by platform, and pathos now follows
(`docs/ethos-differences.md`, "By platform"): unsigned `char` on arm64
(`0xFF` is no EOF), Windows text mode (CR LF, Ctrl-Z), `std::filesystem`
path resolution and printing on Windows, `isatty` true for the null
device on Windows, and the empty include name, which the two Windows
builds of Ethos (libstdc++ and libc++) treat differently. Found on the
way, on every platform: `0xFF` on standard input is never EOF in Ethos;
pathos answered `correct`; fixed.

## Code read

- `thread.rs`: the checker runs on a thread named `main` with a 64 MiB
  stack on every platform; a panic resumes on the main thread with the
  usual status. pathos now goes 4 to 50 times deeper than Ethos on each
  platform, and no longer follows `ulimit -s` (recorded).
- `textmode.rs`: text-mode reading and writing as the Windows C runtime
  does it, compiled and tested everywhere, applied on Windows only.
- `path.rs` (Windows `resolve`): join, `canonicalize`, `\\?\` and
  `\\?\UNC\` stripped, a directory "not a file", the empty name by target
  architecture. Matches `std::filesystem::canonical` on what the probe
  covers.
- `stdin_is_a_terminal` (Windows): a console, or a handle whose metadata
  call fails with `ERROR_INVALID_FUNCTION`, which CI showed to be the null
  device and not a file or pipe. Standard library only; a heuristic for
  "character device", documented as such (serial ports and printers not
  tried).
- `latin1::from_os`/`to_os`: bytes round-trip on Unix; on Windows UTF-16
  units above 255 become `?` (names outside Latin-1, listed as not
  matched).

## Finding

1. **Output to a Windows console is lost for lines with bytes above 127.**
   `main.rs:133` and `:272` write with `let _ = ...write_all(...)`. When
   standard output or error is a Windows console (not a pipe or file),
   Rust's standard library refuses bytes that are not UTF-8, and the error
   is ignored, so such a line (a symbol with a Latin-1 byte, say) is not
   printed at all; Ethos writes the bytes and the console shows them in its
   code page. CI cannot see it: its streams are pipes. Matching Ethos
   exactly needs the console API; at least the line should not vanish
   (for instance, on that error, write it again decoded as Latin-1), and
   the difference belongs in `docs/ethos-differences.md`. Sent to Fable.

## Noted

- `docs/dependencies.md` covers the six platforms; its arm64 soundness
  table (NEON intrinsics on values, NEON being in every arm64 target's
  baseline) and the macOS x86-64 extras (`safe_arch` `sse4_1.rs:72`,
  `wide` `simd.rs:393`, Apple's target assuming SSE4.1) are right. The
  status line awaits Daniel's signature again.
- Not run: `scripts/package` on macOS and Windows (the upload steps run on
  pushes to `main` only, so the first merge is its first run there); the
  eoc gate off Linux x86-64, as the brief says.
- For Daniel: the release binaries link `malachite` (LGPL-3.0-only)
  statically, and the crates ship no licence text. Ethos, which links GMP
  statically, ships `licenses/lgpl-3.0.txt` and says so in `COPYING`.

## The console fix

Fixed in dc26d99: on a Windows console (`textmode::wants_utf8`), text that
is not valid UTF-8 is written with each byte as the character of the same
number, decided before writing (a retry after the error would print the
valid start of the buffer twice). Pipes and files are unchanged. Tested
with a stand-in writer, not on a real console; CI run 43644441697 green on
all six platforms.
