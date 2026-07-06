# Changelog

All notable changes to this crate will be documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

The crate has not yet been published to crates.io. The first
crates.io release will be `0.0.1`. While `Cargo.toml` reads
`version = "0.0.0"`, this file's pre-publish entries describe the
cumulative in-development state.

## [Unreleased]

### Added

- **`core::size` — `usize` cast family.** `SIZEU032` (`usize → u32`,
  saturating narrow) and `SIZEU064` (`usize → u64`, saturating embed),
  both one-sided left-Galois. Implemented with `TryFrom` clamping rather
  than the fixed-width `as`-based macros, so the Galois laws hold on
  16/32/64-bit targets (an `as`-narrowing would truncate, not saturate,
  a `u32 > usize::MAX` on a 16-bit target).

### Changed (swap-only capability traits)

- **`ConnL` / `ConnR` redefined**: each trait now carries exactly one
  method — the polarity swap (`swap_l(&self) -> Conn<B, A, R>`,
  `swap_r(&self) -> Conn<B, A, L>`). The `conn_l()` / `conn_r()`
  projections and the duplicate default accessors (`ceil` / `upper` /
  `floor` / `lower`) are gone; accessors live solely as kind-gated
  inherent methods on `Conn`. The blanket impls on `Conn` values are
  removed — a value is its own view and swaps inherently, so one name
  covers disjoint receivers with no duplication.
- **Marker macros emit `const` projections**: `conn_k!` / `iso!` /
  `compose_k!` / `lift_k!` / `nz_int_ext!` markers now expose public
  inherent `const fn swap_l()` / `swap_r()` — usable in `const`
  composition, e.g. `compose!(U032BE04.swap_r(), U032U064)` — plus
  crate-local `const fn view_l()` / `view_r()` direct views that never
  cross a crate boundary. The public spelling of a direct view is the
  double swap `M.swap_l().swap_r()`.
- **`Conn::identity()` is kind-generic**: `Conn::<X, X, R>::identity()`
  exists directly; the `.swap_l()` workaround is gone.
- **`lift_l!` / `lift_r!` accept `:expr` parents** and dispatch through
  inherent accessors; marker parents are passed as views
  (`lift_k!` handles this internally).

### Added (swap-only capability traits)

- **`prop::conn::swap_involutive_l` / `swap_involutive_r`** — the swap
  round trips are exact fn-pointer identities.
- **`prop::conn::shared_middle`** — a lawful triple's L- and R-views
  agree on the middle adjoint, checked behaviorally.
- Both wired into `law_battery!`'s shared arm, so every marker battery
  exercises them.

### Added (Plan 33 — `order_reflecting` predicate + audit cleanup)

- **`prop::conn::order_reflecting`** — new triple-bound predicate
  asserting `inner(b1) ≤ inner(b2) ⟹ b1 ≤ b2`. This is the load-
  bearing property `floor_le_ceil` is a corollary of (per the
  necessity / sufficiency proofs in the README's *Why one-sided?*
  section). Quantifying over `(b1, b2) ∈ B²` doubles proptest's
  surface area vs `floor_le_ceil`, catching boundary violations the
  rounding-sandwich check misses when source-side strategies under-
  sample extremes — the failure mode that hid the Haskell `f09sys`
  bug for years. Wired into `law_battery!`'s `full` arm so every
  current and future triple marker exercises it without per-site
  opt-in.
- **README *Why one-sided?* section expanded** with explicit
  step-by-step proof chains for both directions of the equivalence,
  a sharpened counterexample that derives `ceil(a) = b₁` /
  `floor(a) = b₃` from L/R-Galois, and the categorical statement
  (`g` fully faithful ⟺ `h ≤ f` in an adjoint triple).
- **`F032F016` / `F064F016`** — added `order_reflecting` proptest
  invocations to their hand-rolled batteries (these float Conns
  carry custom proptest config and don't go through `law_battery!`).
- Symmetric `f032_floor_nan` / `f064_floor_nan` spot tests in
  `src/float/f016.rs` (companions to existing `*_ceil_nan`).
- Definition-site `# Examples` doctest for `F064F032` in
  `src/float/f064.rs` (mirrors the existing `F032F016` / `F064F016`
  doctests).
- `sovxsov6_idempotent_r` proptest in `src/addr/socket.rs`
  (companion to `sovxsov4_idempotent`).

### Changed (Plan 33 docs/cleanup)

- **Boundary-biased every Q-format proptest strategy.** All
  `props_for_pair!` macros (5 inline in `src/fixed/i{8,16,32,64,
  128}.rs`, 5 in `tests/fixed_u{8,16,32,64,128}_galois.rs`) used
  `any::<TN>().prop_map(...)` — uniform sampling over the full bit-
  space, which never hits MIN/MAX for TN ≥ 16 bits in any reasonable
  case-count. Replaced with `prop_oneof![1=>MIN, 1=>MAX, 1=>0|1,
  8=>any]` per CLAUDE.md's strategy guidance. The Plan 32 saturation-
  plateau bugs were caught by manual trace, not by these proptests;
  with the fix, any future regression surfaces at CI. This also makes
  the `order_reflecting` predicate (above) properly exercise the
  boundary that was its raison d'être.
- `prop::conn::floor_le_ceil` doccomment now points at
  `order_reflecting` as the *cause*; rounding sandwich is the
  user-facing fast signal.
- README cross-references from Examples 3 (`triple!` introduction)
  and 6 (`Conn` API tour with the demoted `U008I016`) back into
  *Why one-sided?* so readers hit the math when they meet the API.
- `SOVXSOV6.inner(NegInf)` doc reasoning rewritten — value is
  unchanged, the prior wording inverted the R-Galois derivation.
- Five stale `tests/conn_fixed_u*_galois.rs` filename references
  in `src/fixed/u{8,16,32,64,128}.rs` corrected to the actual
  `tests/fixed_u*_galois.rs` paths (filenames lost their `conn_`
  prefix in an earlier sprint; the source comments rotted).
- `U008N008` test cleanup — dropped duplicated `.ceil()` lines in
  `u008n008_zero_saturates_to_one`, `u008n008_nonzero_round_trip`,
  and `u008n008_inner_then_ceil_recovers_nonzero` (artifacts of
  Plan 32's NonZero ConnL demotion that left dead assertions).
  Also dropped the misleading "floor = ceil" comment.

### Changed (Plan 32 — `floor_le_ceil` cleanup, breaking)

- **Demoted ~140 connections from `triple!` to `Conn::new_l`** because
  their `inner` is non-injective (and therefore not order-reflecting),
  so they aren't true adjoint triples in the categorical sense:
  `floor(a) ≤ ceil(a)` is a necessary-and-sufficient consequence of
  `inner` being an order-embedding (proof in `prop::conn::floor_le_ceil`
  docstring), and these connections violate it at the saturation
  boundary. Affected:
  - **`SDURU128`** (`time::Duration` ↔ unsigned u128 nanoseconds)
  - **`ext_int!` family** (20 widening Conns: `I008I016`, `U008I016`,
    `I008I032`, `U008I032`, `I016I032`, `U016I032`, `I008I064`,
    `U008I064`, `I016I064`, `U016I064`, `I032I064`, `U032I064`,
    `I008I128`, `U008I128`, `I016I128`, `U016I128`, `I032I128`,
    `U032I128`, `I064I128`, `U064I128`)
  - **`fix_fix_*!` family** (~119 Q-format Conns across i8/i16/i32/
    i64/i128 and u8/u16/u32/u64/u128 host types)
  - **`F064TDUR`, `F032TDUR`, `F064SDUR`, `F032SDUR`** (float ↔
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
  alongside the Q-format ladder for the source side primitive.
  Std-int constant names (e.g. `I064I128`, `U008I016`) are unchanged;
  only the module path moves (`int::i64::I064I128` →
  `fixed::i064::I064I128`).
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
  `fixed::iN::I{NN}Q000` (and unsigned analogues) bridging
  the corresponding std-int primitive and `Fixed{I,U}{NN}<U0>`.
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

- **`conn::fixed::{i008,i016,i032,i064,i128}` and `{u008,u016,u032,u064,u128}`**
  — `fixed`-crate-backed binary Q-format ladders. `i128` uses
  `checked_mul`+saturate.
- **`conn::fixed::{i008,…,u128}` std-int surface** — widening,
  narrowing, and cross-sign Conns. Peer numeric Conns live with the
  source side named by the const prefix.
- **`conn::float::f064`** — `F064F032`, `F064F016`.
- **`conn::float::f032`** — `F032F016`. (IEEE binary16
  and Google bfloat16 via the [`half`](https://docs.rs/half) crate.)
- **`conn::time`** — time-crate types: `DATEJDAY`, `TIMENANO`,
  `TIMESECS`, `TDURSECS`, `PDTMDATE`, `ODTMNANO`, `ODTMSECS`.

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
