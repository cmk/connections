# PR #8 — uhlc Conns: NDURU064 + HLIDLX16

## Summary

Adds a feature-gated `src/uhlc/` module bridging the
[`uhlc-rs`](https://crates.io/crates/uhlc) HLC types to existing
endpoints via two Galois connections. Two consumers covered: the
64-bit hybrid logical clock value `NTP64`, and the 16-byte node
identifier `ID`.

1. **`NDURU064` — `NTP64 ↔ u64`, iso (full triple).** `NTP64` is
   `pub struct NTP64(pub u64)`, a transparent newtype with no
   internal invariant. The forward / back pair is direct field
   access; the iso laws hold trivially. Built via `iso!`.
2. **`HLIDLX16` — `ID ↔ LX<16>`, right-Galois only.** `ID`'s derived
   `Ord` is byte-lex from byte 0 of `to_le_bytes()` (LSB-first under
   LE storage), which agrees with `LX<16>`'s lex-from-byte-0 `Ord`
   but **disagrees** with the integer order on the underlying `u128`.
   Bridging to `NonZero<u128>` or `LE<16>` would break Galois at any
   pair where the LE byte order disagrees with the integer order
   (`ID(1)` byte-lex-greater than `ID(256)` is the canonical
   counter-example).
   `LX<16>` is the right target type, *but* the iso is one value
   short of total — `LX([0; 16])` is a byte string that no `ID`
   represents (ID's construction enforces a non-zero `u128`). The
   fix mirrors `nz_uint_ext!`'s shape: route the puncture to a
   sentinel (here, `[0,…,0,1]` — the lex-min valid ID) and ship as a
   single-sided Conn. R-Galois holds; L-Galois fails at the corner.
   Built via `conn_r!`.

### Galois-law derivation at the puncture

At `b = LX([0; 16])` with `inner(b) = ID([0,…,0,1])`:

- **R-law** (`inner(b) ≤ a ⟺ b ≤ floor(a)`): the LHS is
  `ID([0,…,0,1]) ≤ a`, which holds for every valid `a` because
  `ID([0,…,0,1])` is the lex-min `ID`. The RHS is `LX([0; 16]) ≤
  LX(a.0)`, which holds for every valid `a` because `LX([0; 16])` is
  the lex-min `LX<16>`. Both sides always true. ✓
- **L-law** (`ceil(a) ≤ b ⟺ a ≤ inner(b)`): at the corner
  `(a = ID([0,…,0,1]), b = LX([0; 16]))`, the LHS is
  `LX(a.0) ≤ LX([0; 16])`, which is *false* (every valid `ID`'s
  bytes are strictly above `[0; 16]` under lex). The RHS is
  `a ≤ ID([0,…,0,1]) = a`, which is *true*. Mismatch. ✗

So the structural choice is `conn_r!`, not `iso!`. Exact mirror of
the `nz_uint_ext!` situation — the puncture sits on the *target*
side rather than the source.

### Totality and panics

`HLIDLX16`'s endpoints are total — no `panic!`, no `.expect()`. The
only fallible call (`ID::try_from(&[u8; 16])`) is fed bytes that are
provably non-zero at every reachable call site: the puncture branch
routes through a compile-time non-zero `LEX_MIN_ID_BYTES`, and the
fallthrough branch only fires when `lx.0` has at least one non-zero
byte. The `unreachable!()` arm documents the dead code statically.
The Kani harness `lower_never_panics` exercises the full `[u8; 16]`
domain with *no* `kani::assume` precondition, proving totality in
the SMT sense.

A documented L-law regression test (`l_law_fails_at_puncture`)
builds an ad-hoc `Conn<ID, LX<16>>` from the same `(ceil, inner)`
pair and asserts the L-law's documented `false`. If a future `ID`-Ord
change ever silently makes the L-law hold, this test fails and forces
a revisit of the `conn_r!` vs `iso!` choice.

### Naming

- **`NDUR`** (4L+0D) for `NTP64` — "NTP Duration", parallel to
  `TDUR` (`time::Duration`) and `HDUR` (`hifitime::Duration`). The
  `E***` family in `src/hifi/epoch.rs` is reserved for typed-epoch-
  anchored types and would mislead here: `NTP64` is clock-agnostic
  (`uhlc-rs/src/ntp64.rs:68-71`). Trailing digits on `NTP` collide
  with NTP protocol version numbers (NTPv4, RFC 5905; v5 in draft),
  so `NTP4`/`NTP5` are off-limits.
- **`HLID`** (4L+0D) for `ID` — "HLC node ID". The name says what the
  type *is*, parallel to the `NDUR` choice. `UHID` would have read as
  a crate-prefix rather than a structural mnemonic.
- **`U064`** (1L+3D) for `u64` — existing.
- **`LX16`** (2L+2D) for `LX<16>` — wrapper family parallel to
  `LE16`, `B216`, `L216`.

Both Conn names (`NDURU064`, `HLIDLX16`) are exactly 8 chars, 4+4.
No collisions in the codebase.

### Files

New:

- `src/uhlc.rs` — module rustdoc + submodule declarations + `pub use`
  re-exports.
- `src/uhlc/ntp64.rs` — `NDURU064` + proptest battery + boundary spot
  check.
- `src/uhlc/id.rs` — `HLIDLX16` + proptest battery + negative
  L-law assertion + totality spot check + floor/lower spot check.
- `src/kani/uhlc.rs` — Kani harnesses for both Conns plus the
  totality proof.

Modified:

- `Cargo.toml` — new optional `uhlc` dep (`default-features = false`
  to skip uhlc's default `["std", "serde"]`, which would drag in
  `humantime`, `lazy_static`, `log`, `rand/std`); new `uhlc` feature.
- `src/lib.rs` — `#[cfg(feature = "uhlc")] pub mod uhlc;` alongside
  `hifi`/`time`.
- `src/kani.rs` — `#[cfg(feature = "uhlc")] mod uhlc;` alongside the
  other feature-gated kani submodules.
- `AGENTS.md` (= `CLAUDE.md`) — per-domain table gains `uhlc` and
  `hifi` rows.
- CI matrix (`ci.yml`, `pages.yml`, `kani.yml`), pre-push hook, and
  `docs.rs` metadata — all add `uhlc` to their feature sets.

### Why a single right-Galois target, not two

The plan considered shipping both `Conn<ID, LX<16>, R>` and a
literal-`nz_uint_ext!`-mirror `Conn<LX<16>, ID, L>`. They are
algebraically equivalent (same `(ceil, inner) = (floor, lower)`
swap), but `HLIDLX16` reads naturally as "domain-type encoded as
bytes" — same order as `U128LE16`, `U064BE08`, etc. Shipping both
would just double the public surface for one underlying construction.

### Composition story

Cross-width chains aren't pre-baked here. Users who need `NTP64 ↔
u32` compose `NDURU064` with the existing `core::u064::U064U032`
ladder; users who need `ID ↔ NonZeroU8`-style short keys compose
`HLIDLX16` with manual byte projections (no canonical Conn fits, by
design — `ID` is a 128-bit identifier; truncating it isn't a Galois
connection, it's a hash). The `hifi` module pre-bakes a couple of
common-precision rungs (`HDURNANO`, `HDURSECS`) for ergonomics, but
there's no analogous "common precision" for HLC values — just the
raw 64-bit timestamp.

### Notable deferrals

- `NTP64 ↔ core::time::Duration` — `From<Duration>` panics for
  `secs > u32::MAX` (`uhlc-rs/src/ntp64.rs:287-293`); the proper
  treatment is a saturating-ceil L-only Conn at the 32-bit-seconds
  boundary. Not in v1 because no consumer has asked.
- `Timestamp = (NTP64, ID)` — lex-ordered composite; no single
  integer endpoint preserves the order without inventing a
  `u192`. Users decompose: Conn over the `time` projection + Conn
  over the `id` projection.
- Loosening the `lib.rs:251` Kani gate so `cargo kani` doesn't
  require `--features fixed` — a refactor across the existing Kani
  module tree, outside this sprint. Today, `cargo kani --features
  fixed,hifi,uhlc` exercises everything.

### Verification

- 14 in-module unit / proptest cases on top of the existing 689,
  plus 44 doctests — all pass with
  `cargo test --features fixed,time,hifi,uhlc,proptest,macros`.
- `cargo build --no-default-features` and `cargo build --features
  uhlc` both clean.
- `cargo clippy --features fixed,time,hifi,uhlc,proptest,macros
  --all-targets -- -D warnings` clean.
- `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
  fixed,proptest,macros,time,uhlc --document-private-items` clean.
- Kani harnesses (10 total: 4 NDURU064 + 5 HLIDLX16 R-laws +
  `lower_never_panics`) compile under `cargo kani --features
  fixed,hifi,uhlc`; CI runs them weekly per the existing `kani.yml`
  schedule, now with `--features fixed,hifi,uhlc`. (`fixed` is
  required by the outer Kani gate at `lib.rs:251`; this PR's local
  review caught a draft `kani.yml` that only enabled `hifi,uhlc`.)

## Local review (2026-05-19)

**Branch:** plan/2026-05-19-03
**Commits:** 3 (origin/main..plan/2026-05-19-03)
**Reviewer:** Codex (`codex review --base origin/main`)
**Prompt fingerprint:** AGENTS.md=4563f590caa7dbba5ea9eae973fa59182f1a6470 calibration=missing

---

The runtime Conns and tests build, but the new Kani verification added by the patch is not exercised by the updated workflow because the required parent feature gate is not enabled.

Review comment:

- [P2] Enable the Kani parent gate for uhlc proofs — .github/workflows/kani.yml:22-22
  With this workflow invocation, the new `src/kani/uhlc.rs` proofs are never compiled: the Kani module is only included under `#[cfg(all(kani, feature = "fixed"))]` in `src/lib.rs`, but CI now runs `cargo kani` with only `hifi,uhlc`. Add `fixed` here or relax the parent cfg; otherwise the advertised uhlc Kani coverage remains disabled.


<!-- gh-id: 3271453893 -->
### Copilot on [`src/uhlc.rs:9`](https://github.com/cmk/connections/pull/8#discussion_r3271453893) (2026-05-20 05:39 UTC)

In this markdown table, `LX<16>` (and other generics with `<…>`) aren’t wrapped in code spans, so rustdoc/Markdown may treat `<16>` as an HTML tag and render it incorrectly or drop it. Wrap the endpoint types in backticks (e.g., `LX<16>`) or escape `<`/`>` to keep the table readable.


<!-- gh-id: 4325471849 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-05-20 05:39 UTC](https://github.com/cmk/connections/pull/8#pullrequestreview-4325471849))

## Pull request overview

Adds a new `uhlc`-feature-gated module that bridges types from the external `uhlc` crate into this crate’s Conn ecosystem, providing lawful conversions for `NTP64` and `ID` via two Galois connections and wiring those into tests, Kani proofs, and CI/docs feature matrices.

**Changes:**
- Introduce `connections::uhlc` with `NDURU064` (`NTP64 ↔ u64` iso) and `HLIDLX16` (`ID ↔ LX<16>` right-Galois) plus property/unit tests.
- Add Kani harnesses for both Conns and wire them into the feature-gated Kani module tree.
- Add optional `uhlc` dependency + `uhlc` feature, and propagate `uhlc` through docs.rs metadata, CI workflows, and local hooks.

### Reviewed changes

Copilot reviewed 14 out of 14 changed files in this pull request and generated 2 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| `Cargo.toml` | Adds optional `uhlc` dependency, `uhlc` feature, and docs.rs feature set updates. |
| `src/lib.rs` | Exposes `pub mod uhlc` behind `#[cfg(feature = "uhlc")]`. |
| `src/uhlc.rs` | New module docs + submodule declarations and re-exports for the `uhlc` Conns. |
| `src/uhlc/ntp64.rs` | Implements `NDURU064` iso (`NTP64 ↔ u64`) with proptests and boundary checks. |
| `src/uhlc/id.rs` | Implements `HLIDLX16` right-Galois Conn (`ID ↔ LX<16>`) with puncture saturation + tests. |
| `src/kani.rs` | Wires in the new `kani::uhlc` module behind `feature = "uhlc"`. |
| `src/kani/uhlc.rs` | Adds Kani proofs for `NDURU064` and `HLIDLX16`, including totality proof for `lower`. |
| `.github/workflows/ci.yml` | Runs tests/doctests with `uhlc` enabled in the feature set. |
| `.github/workflows/pages.yml` | Builds docs with `uhlc` enabled for GitHub Pages artifacts. |
| `.github/workflows/kani.yml` | Enables `fixed,hifi,uhlc` features so the new Kani proofs are compiled/exercised. |
| `.githooks/pre-push` | Mirrors CI feature set by adding `uhlc` to local test/doc checks. |
| `AGENTS.md` | Updates the per-domain Conn families table to include `uhlc` (and `hifi`). |
| `doc/plans/plan-2026-05-19-03.md` | Adds a detailed implementation/verification plan for the `uhlc` module. |
| `doc/reviews/review-00008.md` | Adds the PR’s review record/audit-trail entry. |
</details>







<!-- gh-id: 3271453928 -->
### Copilot on [`doc/plans/plan-2026-05-19-03.md:68`](https://github.com/cmk/connections/pull/8#discussion_r3271453928) (2026-05-20 05:39 UTC)

This task description no longer matches the implemented Kani harnesses: the committed `src/kani/uhlc.rs` doesn’t include `closure_l`/`closure_r` proofs for `NDURU064`, and it also omits the described `roundtrip_floor` / `lx16_to_id_never_panics` proof structure for `HLIDLX16`. Please update this section to reflect the actual proofs shipped (or add the missing proofs if the doc is the intended contract).


<!-- gh-id: 3271559519 -->
#### ↳ cmk ([2026-05-20 06:04 UTC](https://github.com/cmk/connections/pull/8#discussion_r3271559519))

Fixed — wrapped `NTP64`, `u64`, `ID`, and `LX<16>` in code spans in the rustdoc table so `<16>` isn't parsed as an HTML tag.

<!-- gh-id: 3271560262 -->
#### ↳ cmk ([2026-05-20 06:04 UTC](https://github.com/cmk/connections/pull/8#discussion_r3271560262))

Fixed — aligned the T4 narrative and the Kani sketch with the harnesses that actually shipped. `closure_l`/`closure_r` are dropped from NDURU064 (an iso's `iso_roundtrip_l` is the stronger form and subsumes both closures); `roundtrip_floor` is called out as proptest-only (`uhlc::id::tests::roundtrip_floor_nonpuncture`) and not duplicated as a Kani harness; and the totality proof reads as `lower_never_panics` (the shipped name) rather than the draft `lx16_to_id_never_panics`. Also dropped the stale `kani::assume(bytes != [0u8; 16])` from the `kernel_r` sketch — the R-kernel law holds at the puncture too, which the shipped harness exercises without an assume.
