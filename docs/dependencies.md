# Dependencies and their unsafe code

pathos forbids `unsafe` code in its own crates. This file accounts for the
`unsafe` code in every dependency, direct and indirect, as listed in
`Cargo.lock`. See "Memory safety" in [brief.md](brief.md).

For each dependency: its version, whether it contains `unsafe` code, where,
and why that is acceptable. Adding a dependency that contains `unsafe` code
or binds C code needs the user's agreement.

**Status (2026-11-13, milestone 1): awaiting the user's agreement.** The
brief agreed to `malachite` knowing of one `unsafe` use, the AVX2 FFT in
`malachite-nz`. `malachite` also brings nine crates of its own, none of them
optional, and all nine contain `unsafe` code. They are listed below. None
binds C or C++ code, and none has a build script that compiles any.

## Direct dependencies

Only `pathos-term` has external dependencies.

| Crate | Version | `unsafe` code | Where, and why acceptable |
| --- | --- | --- | --- |
| `malachite-base` | 0.14.0 | none | `#![forbid(unsafe_code)]`. Used for the arithmetic traits. |
| `malachite-nz` | 0.14.0 | 9 lines in 2 files | `#![deny(unsafe_code)]`, allowed only in `natural/arithmetic/mul/fft/avx2.rs` and at its call site in `fft/mod.rs`: AVX2 intrinsics, called after a run-time check that the CPU has AVX2, and only for very large multiplications. The `unsafe` in `conversion/pyo3.rs` is behind the `enable_pyo3` feature, which pathos does not enable. This is the case the brief accepted. |
| `malachite-q` | 0.14.0 | none | `#![forbid(unsafe_code)]`. |

## Indirect dependencies

All of these come from `malachite` and cannot be turned off with features.

| Crate | Version | Needed by | `unsafe` code | Where, and why acceptable |
| --- | --- | --- | --- | --- |
| `hashbrown` | 0.16.1 | `malachite-base` | yes, throughout (about 325 lines in 18 files) | The hash table behind `std::collections::HashMap`; the standard library ships the same code. |
| `foldhash` | 0.2.0 | `hashbrown` | 10 lines in 3 files | The default hasher of `hashbrown`: unaligned reads of byte slices and a seed kept in a static. |
| `itertools` | 0.14.0 | all three `malachite` crates | 10 lines in 2 files | `next_array.rs` (filling a `MaybeUninit` array) and `either_or_both.rs` (`unreachable_unchecked` after a check). |
| `either` | 1.19.0 | `itertools` | 2 lines in 1 file | Pin projection for `Either`, in `lib.rs`. pathos does not pin anything. |
| `libm` | 0.2.16 | all three `malachite` crates | about 56 lines in 9 files | Pure-Rust floating-point functions. The `unsafe` is CPU feature detection and x86/aarch64 intrinsics for `sqrt`, `fma` and rounding. Its build script only sets `cfg` flags. |
| `ryu` | 1.0.23 | `malachite-base` | about 27 lines in 11 files | Float-to-string conversion, writing digits through raw pointers into a fixed buffer. |
| `wide` | 1.7.1 | `malachite-nz` | yes (about 443 lines in 34 files) | SIMD vector types, used by the FFT multiplication. Mostly transmutes between vectors and arrays of the same size, and calls into `safe_arch`. |
| `safe_arch` | 1.2.0 | `wide` | yes, throughout (about 1,157 lines in 30 files) | Wrappers that expose CPU intrinsics as safe functions, each compiled only when the target has the CPU feature. |
| `bytemuck` | 1.25.2 | `wide`, `safe_arch` | yes (about 323 lines in 14 files) | Checked casts between plain-data types; the `unsafe` is the implementation of those checks and the marker traits. |

The line counts are of lines that contain the word `unsafe` outside
comments and lint attributes, in each crate's `src/`.

## What pathos reaches

pathos calls `malachite` for parsing and printing integers, addition,
multiplication, powers, floor division, bit operations and shifts, and the
same on rationals.

Which of the `unsafe` code above those calls can reach has **not** been
traced, by hand or with a tool such as `cargo geiger`. What is known:

- `malachite-nz` says its AVX2 FFT is used only for very large
  multiplications. `eo::mul` and `eo::pow` can produce such numbers from a
  proof. That path goes through `wide`, `safe_arch` and `bytemuck`.
- pathos does no floating-point arithmetic and converts no floats, which is
  what `libm` and `ryu` are for. Whether `malachite` calls them inside
  integer or rational operations is not known.

## Options

1. Accept the nine crates as part of the decision to use `malachite`.
2. Replace `malachite` with a big-number crate that has fewer dependencies.
   The wrapper types in `crates/pathos-term/src/num.rs` are the only code
   that names `malachite`, so the swap is local. No candidate has been
   evaluated yet.
