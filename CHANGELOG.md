# Changelog

All notable changes to this crate will be documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

The crate has not yet been published to crates.io. The first
crates.io release will be `0.0.1`. While `Cargo.toml` reads
`version = "0.0.0"`, this file's pre-publish entries describe the
cumulative in-development state.

## [Unreleased]

### Changed (Plan 32 — `floor_le_ceil` cleanup, breaking)

- **Demoted ~140 connections from `triple!` to `Conn::new_l`** because
  their `inner` is non-injective (and therefore not order-reflecting),
  so they aren't true adjoint triples in the categorical sense:
  `floor(a) ≤ ceil(a)` is a necessary-and-sufficient consequence of
  `inner` being an order-embedding (proof in `prop::conn::floor_le_ceil`
  docstring), and these connections violate it at the saturation
  boundary. Affected:
  - **`STDRU128`** (`time::Duration` ↔ unsigned u128 nanoseconds)
  - **`ext_int!` family** (20 widening Conns: `I008I016`, `U008I016`,
    `I008I032`, `U008I032`, `I016I032`, `U016I032`, `I008I064`,
    `U008I064`, `I016I064`, `U016I064`, `I032I064`, `U032I064`,
    `I008I128`, `U008I128`, `I016I128`, `U016I128`, `I032I128`,
    `U032I128`, `I064I128`, `U064I128`)
  - **`fix_fix_*!` family** (~119 Q-format Conns across i8/i16/i32/
    i64/i128 and u8/u16/u32/u64/u128 host types)
  - **`F064DURN`, `F032DURN`, `F064STDR`, `F032STDR`** (float ↔
    duration: f64/f32 plateaus collapse multiple Durations onto the
    same float)

  **Migration**: callers of `.floor()` on any of the above will see
  compile errors (the method literally doesn't exist on `ConnL`).
  Either use `.ceil()` (which round-trips through `inner` as
  documented), or hand-compute the round-down direction via
  arithmetic, or open an issue for a paired `*CEIL`/`*FLOOR`
  alternative.
- **Strengthened `prop::conn::law_battery!`'s `full` subset to require
  `floor_le_ceil`.** Previously `full` covered the eight per-side
  Galois laws plus `idempotent`; now it also enforces the rounding
  sandwich. This makes the test suite refuse to ship triple markers
  that aren't true adjoint triples — closing the door on the latent-
  bug shape that motivated this entire sprint.

### Changed

- **Folded `connections::int::*` into `connections::fixed::*`.** Every
  std-int Conn (`I064I128`, `U008I016`, `U128I008`, etc.) is
  structurally a Q*N*.0 fixed-point conversion, so it now lives
  alongside the Q-format ladder for the same destination primitive.
  Std-int constant names (e.g. `I064I128`, `U008I016`) are unchanged;
  only the module path moves (`int::i64::I064I128` →
  `fixed::i64::I064I128`). `src/int/` files remain as thin
  re-export shims pointing at `crate::fixed::*` until the references
  in tests/doctests are rewritten in T9 and the tree is removed in
  T10.
- **Renamed every intra-`fixed` Conn prefix from `I`/`U` to `Q`.**
  After the merge, the prefix letter alone disambiguates: `Q` =
  Q-format wrapper from the [`fixed`] crate, `I` = signed std
  primitive, `U` = unsigned std primitive, `N` = `NonZero<*>`. Sign
  and host bit-width come from the module path. Examples:
  `fixed::i8::I008I004` → `fixed::i8::Q008Q004`;
  `fixed::u8::U008U007` → `fixed::u8::Q008Q007`;
  `fixed::i64::I064I004` → `fixed::i64::Q064Q004`. ~150 constants
  renamed; their semantics, doctests, and Galois-law guarantees are
  unchanged.
- **Reset `Cargo.toml` `version` from `0.1.0` to `0.0.0`** to reflect
  the pre-publish state. The first crates.io release will be `0.0.1`.

### Added

- **`Conn::new_iso(forward, back)`** — degenerate-Galois constructor
  for total order-isomorphisms (where `floor = ceil = forward` and
  both Galois laws hold trivially). Used by the new cross-crate iso
  family below; available for any future iso Conn (e.g. `Ipv4Addr ↔
  u32`).
- **NonZero family** — 10 new Conns, one per primitive width:
  `fixed::iN::I{NN}N{NN}` and `fixed::uN::U{NN}N{NN}`, with type
  `Conn<{i,u}N, NonZero<{i,u}N>>`. Signed variants are the
  **asymmetric-adjoint-at-zero showcase**: `floor(0) = NonZero(-1)`
  (largest NonZero ≤ 0), `ceil(0) = NonZero(+1)` (smallest NonZero
  ≥ 0); both Galois laws hold because the asymmetric forward map
  sandwiches the punctured zero. Unsigned variants have `floor =
  ceil` and saturate `0` to `NonZero(1)`; single-sided left-Galois
  (right-Galois fails at the unsigned bottom plateau, where there is
  no NonZero strictly below `NonZero(1)`).
- **Cross-crate iso family** — 10 new Conns
  `fixed::iN::Q000I{NN}` (and unsigned analogues) bridging
  `Fixed{I,U}{NN}<U0>` and the corresponding std-int primitive.
  Lossless `to_bits` / `from_bits` via `Conn::new_iso`.

### Why

`int/` and `fixed/` had parallel file layouts, and every std-int
primitive is structurally a Q*N*.0 fixed-point. The crate's only
real top-level distinction is float vs fixed; merging `int/` into
`fixed/` makes that visible. Switching the intra-fixed prefix to
`Q` lets the prefix letter encode "Fixed wrapper vs std primitive"
directly, so the 8-char Conn names stay self-decodable after the
merge — no context-dependent digit interpretation needed.

[`fixed`]: https://docs.rs/fixed

## Initial inventory (pre-publish)

The following content was assembled as the initial release inventory
before the Plan 25 reorg above; it remains accurate for everything
not touched by [Unreleased].

Initial release. A Rust port of the Haskell
[`connections`](https://github.com/cmk/connections) library, encoding
Galois connections as first-class `Conn<A, B>` values and exposing a
hierarchy of lattice-based numerical conversions on top.

### Added

- **`Conn<A, B>`** — adjoint triple `ceil ⊣ inner ⊣ floor` stored as
  three bare `fn` pointers. `Copy`, `const`-constructible, heap-free.
  `Conn::new` (full triple), `Conn::new_left` (one-sided),
  `Conn::identity()`.
- **`compose!` macro** — variadic compile-time composition of two or
  more parent Conns into a fresh `Conn<Src, Dst>`. Source/dest types
  come from the binding's annotation; intermediates are inferred.
- **`Extended<T>`** and **`ExtendedFloat<T>`** — three-element extensions
  (`Bot`/`Extend(_)`/`Top`) recovering the lattice top/bottom that std
  primitives lack. `ExtendedFloat<T>` patches NaN reflexivity so the
  Galois-law machinery can reason about IEEE floats under N5.
- **Lattice trait hierarchy** in `connections::lattice` (Eq + PartialOrd
  base, Heyting / Bi-Heyting operators).
- **`property::laws`** — pure `bool`-returning Galois-law predicates
  (`conn_galois_l/r`, `conn_closure_l/r`, `conn_kernel_l/r`,
  `conn_monotone_l/r`, `conn_idempotent`, `conn_floor_le_ceil`,
  `conn_roundtrip_ceil/floor`, `conn_ulp_bound`). Always public; no
  `proptest` dependency.
- **`property::arb`** (gated on the `testing` feature) — proptest
  strategies (`arb_f32`/`arb_f64`/`arb_f64_bounded`/`arb_f16`/
  `arb_bf16`, `fixed_*`, `extended_fd00..extended_fd12`, time-crate
  generators).
- **Cast operations** in `connections::conn::cast` — `ceiling`,
  `floor`, `upper`, `lower`, their `*1` / `*2` lifters, plus
  `maximize` / `minimize`. All re-exported at the crate root and
  marked `#[inline]` + `#[must_use]`.

#### Conn families

- **`conn::fixed::{i8,i16,i32,i64,i128}` and `{u8,u16,u32,u64,u128}`**
  — `fixed`-crate-backed binary Q-format ladders. `i128` uses
  `checked_mul`+saturate.
- **`conn::std::{i8,i16,i32,i64,i128,u8,u16,u32,u64,u128}`** —
  std-int widening + narrowing + cross-sign Conns. Each per-type
  submodule hosts the Conns whose destination is that primitive.
- **`conn::float::f64`** — `F064F032`, `F064F016`, `F064B016`.
- **`conn::float::f32`** — `F032F016`, `F032B016`. (IEEE binary16
  and Google bfloat16 via the [`half`](https://docs.rs/half) crate.)
- **`conn::time`** — time-crate types: `DATEJDAY`, `TIMENANO`,
  `TIMESECS`, `DURNSECS`, `PDTMDATE`, `OFDTNANO`, `OFDTSECS`.

#### Conventions

- 8-character Conn names with a fixed two-side shape (smaller-
  resolution / coarser tier on the right; see CLAUDE.md §Conn-name
  format).
- Module organization: one `conn::` submodule per dependency crate
  (`fixed`, `time`, `half` — pending) plus `conn::std`; type-named
  filenames; placement by specificity (specific > general; right >
  left as tie-breaker).

### Deferred (planned for future releases)

- Half-bridge Conn relocation into `conn::half::{f16,bf16}` per the
  placement rules (currently still in `conn::float`).
- `f128` Conns (blocked on stable `f128`).
- Runtime composition (`Conn::then` / `DynConn`).
- Domain-specific ladders (decimal time rungs, audio sample rates,
  float-Duration bridges) live in downstream crates
  ([`agogo`](https://gitlab.com/cmk/agogo) for audio); this crate
  ships the algebra plus the per-host-crate cast families.

### Requirements

- **MSRV**: Rust 1.85.
