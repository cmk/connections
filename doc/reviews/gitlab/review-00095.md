# MR !95 — T10: f16-source Q-format Conns

## Summary

- Ship 68 `Float→Q-format` Conns sourced from `f16` across the 10
  `fixed/{i,u}{008,016,032,064,128}.rs` host files, gated on
  `feature = "f16"` (nightly). Mirrors the `F032Q<X>` / `F064Q<X>`
  rung cadence already in each file: full triple for hosts ≤ f16
  mantissa (8-bit hosts), L-only otherwise.
- Direct `float_fixed!` / `float_fixed_l!` invocations — `f16 as f64`
  is exact so the existing macro bodies work unchanged with
  `$float = f16`. No new infrastructure (no compose-based
  alternative, no walk machinery).
- Add 10 integration-test files (`tests/fixed_<host>_float_q_galois_f16.rs`)
  with `cases: 1024` law batteries, plus an `extended_float_f16()`
  proptest strategy in `tests/common/f16.rs` (separate file so the
  existing 10 non-f16 integration tests don't have to opt in to
  `#![feature(f16)]`).

## Test plan

- [x] `cargo build` (stable, no f16) — clean.
- [x] `cargo test --workspace` (stable) — all green; 0 regressions.
- [x] `cargo +nightly build --features f16` — clean.
- [x] `cargo +nightly test --features f16 --workspace` — 1479 lib
  tests pass; each new `fixed_*_float_q_galois_f16.rs` battery
  passes (98 props per i8 host, similar for the rest).
- [x] `cargo +nightly clippy --all-targets --features f16 -- -D warnings`
  — clean.
- [x] `cargo clippy --all-targets -- -D warnings` (stable) — clean.
- [x] `cargo fmt --all -- --check` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo +nightly doc --no-deps
  --features testing,macros,time,f16 --document-private-items`
  — clean, no broken intra-doc links.

## Notes

- **Conn count: 68, not 62.** The plan's stated count assumed
  symmetric 6/7 rungs across signed/unsigned hosts, but the existing
  `F032Q<X>` / `F064Q<X>` rungs already differ (e.g. u008 has 8
  rungs F0..F8 with F7, i008 has 7 rungs U0..U8 without U7). I
  matched the per-file rung cadence so f16 sources line up with f32
  / f64 in each file rather than introducing an asymmetric f16
  ladder. Ladder summary: i008=7, u008=8, i016=6, u016=8, i032=6,
  u032=7, i064=6, u064=7, i128=6, u128=7 → 68 Conns.
- **L-only threshold for f16: host > 11 bits.** f16 mantissa is 11
  bits (10 explicit + 1 implicit). Only the 8-bit host files
  (i008/u008) get the full adjoint triple; everything 16-bit and
  wider is L-only because `inner` aliases distinct Q-format values
  onto the same f16 at large magnitudes.
- **Helper module placement.** `extended_float_f16()` lives in
  `tests/common/f16.rs` rather than inline in
  `tests/common/mod.rs`. Cargo discovers every `tests/*.rs` as a
  test target, but `tests/common/*` (subdirectory form) is excluded.
  The non-f16 integration tests don't transitively load the f16
  helper, so they don't need `#![feature(f16)]` at their crate
  root.

## Out of scope (deferred to a future MR)

- Bumping the inline `cases: 256 → 1024` in `src/float/f016.rs`'s
  Phase-1 `F016I<N>` / `F016U<N>` law batteries. Gated on the
  separate nightly f16 CI runner; the f16 → Q-format batteries here
  use 1024 cases out of the gate.
- f16-source Conns for `time`, `addr`, or other downstream domains.
  Same direct-macro path applies whenever the target type's
  `T as f64` is exact.

## Local review (2026-05-10)

**Branch:** sprint/f16-q
**Commits:** 2 (origin/main..sprint/f16-q)
**Reviewer:** Claude (sonnet, independent)

---

### P1.A — Trait-claim audit

Macro contract verified:
- `float_fixed!` claims full triple (`ConnL` + `ConnR`) — requires host
  bits ≤ source mantissa.
- `float_fixed_l!` claims L-only — requires host bits > source mantissa.

Spot-checked invocations across host widths/signs:
- `F016Q008` in `i008.rs`: full triple, host=8 ≤ f16-mantissa=11 ✓
- `F016Q007` in `u008.rs`: full triple, host=8 ≤ 11 ✓
- `F016Q016` in `i016.rs`: L-only, host=16 > 11 ✓
- `F016Q128` in `u128.rs`: L-only, host=128 > 11; routes through
  pre-existing `BitsToF64Rd::to_f64_rd` for the `u128::MAX` saturation
  case ✓

All 68 new Conns follow the correct macro at the correct threshold. No
trait-claim mismatch.

### P1.B — Standard review

- **Commit hygiene**: Two atomic, conventional commits. `feat:` for
  the source change, `doc:` for plan/review. Clean.
- **Code quality**: No unsafe; section numbering consistent (`§7` per
  file); 8-char Conn names per CLAUDE.md; module placement matches the
  specificity rules. `float_fixed_l` import added to i016/u016 with
  `#[allow(unused_imports)]` preserved.
- **Test coverage**: 10 integration-test files mirror existing pattern.
  `cases: 1024` throughout. `extended_float_f16()` boundary set
  includes `2.0_f16.powi(11)` (mantissa boundary), `f16::MAX/MIN/EPSILON`,
  and i8/u8 saturation boundaries. Wider-host plateaus (2^32, 2^63,
  2^127) overflow f16 to `INFINITY`, covered indirectly via
  `Just(f16::INFINITY)`.
- **Risks**: No TODOs, no new deps, all `#[cfg(feature = "f16")]`-gated.

### P2 — Plan-aware

No relaxation notes in the plan. T5 was folded into T6 (smoke-tested
during implementation rather than as a separate scratch artifact).
T6's 62 → 68 Conn-count delta is explained in the plan Review section
with per-file rung-cadence reasoning. T7's `tests/common/f16.rs`
placement (rather than inline in `tests/common/mod.rs`) is documented
in the same section.

### Findings

**Must fix before push**: none.

**Follow-up**:
1. Stale doc path in `tests/common/f16.rs:7` — comment says
   `#[path = "common_f16.rs"]` but actual attribute in test files is
   `#[path = "common/f16.rs"]`. Doc-only; no runtime impact. **Fixed
   inline before push** (see fix-up commit).
2. Plan's named spot checks (`f016q008_one_half`, `f016q000_int_round`,
   `f016q008_nan`) are not present as named unit tests. The proptest
   law battery covers the underlying laws, so the spot checks are
   redundant point-documentation. Deferred — no value-add over the
   battery.
3. `cases: 256 → 1024` bump in inline `src/float/f016.rs` batteries —
   already in the deferred list above.
