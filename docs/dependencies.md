# Dependencies and their unsafe code

pathos forbids `unsafe` code in its own crates. This file accounts for the
`unsafe` code in every dependency, direct and indirect, as listed in
`Cargo.lock`. See "Memory safety" in [brief.md](brief.md).

For each dependency: its version, whether it contains `unsafe` code, where,
and why that is acceptable. Adding a dependency that contains `unsafe` code
or binds C code needs the user's agreement.

| Crate | Version | `unsafe` code | Where, and why acceptable |
| --- | --- | --- | --- |

No external dependencies yet (2026-11-13).
