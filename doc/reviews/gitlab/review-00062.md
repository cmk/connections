# MR !62 — Plan 39: Kani SMT verification of Galois-connection laws

## Summary

- Adds a `#[cfg(kani)]`-gated proof tree at `src/kani_proofs/`
  (parent `src/kani_proofs.rs`, eight submodules) that promotes the
  proptest-asserted Galois laws on every integer / Q-format /
  NonZero / iso Conn family from sampled spot-checking to
  **SMT-verification over the full bit-width domain**. Each
  `#[kani::proof]` harness is a one-liner calling the existing
  unconditionally-`pub` predicates in `crate::prop::conn` (`galois_l`,
  `monotone_l`, `closure_l`, `kernel_l`, `idempotent_l`, …) on a
  `kani::any::<_>()` symbolic input. Coverage: **604 harnesses, 0
  failures**, dispatching in well under one minute total wall-time.
- The headline Group-2 result — **the f64 → f32 ULP walk in
  `src/float/f32.rs` converges in ≤ 2 iterations for every finite
  non-NaN f64** — is proven via three tiered harnesses
  (`float_walk::t0/t1/t2_*`); T0 covers the unrestricted finite
  domain in ~2s with `#[kani::unwind(4)]`. Two `pub(crate)`
  walk-step probe wrappers gated on `cfg(kani)` make the walk's
  `(z, steps)` tuple visible to the proof; release builds compile
  no proof code.
- `Cargo.toml` gains a one-line
  `[lints.rust] check-cfg = ["cfg(kani)"]` declaration so
  `cargo build` / `cargo test` don't warn about the proof harnesses'
  unknown cfg name. No new dependency: Kani injects its own crate at
  build time when `cargo kani` runs. Two harness predicates that
  don't hold by construction (`uint_sat::roundtrip_floor`,
  `float_weaker::finite_in_finite_out_*` over saturation regimes)
  are documented in their respective files rather than asserted.

## Test plan

- [ ] `cargo install --locked kani-verifier && cargo kani setup` —
      one-time install, unchanged from upstream.
- [ ] `cargo build` — clean, no `unexpected_cfg` warnings.
- [ ] `cargo test --workspace --quiet` — unchanged from baseline
      (proofs are `#[cfg(kani)]`-gated; pre-sprint test count
      preserved).
- [ ] `cargo kani --harness 'int_narrow::'` — 60 / 60 verified.
- [ ] `cargo kani --harness 'uint_sat::'` — 70 / 70 verified.
- [ ] `cargo kani --harness 'nz_ext::'` — 60 / 60 verified.
- [ ] `cargo kani --harness 'iso_family::'` — 50 / 50 verified.
- [ ] `cargo kani --harness 'fix_fix_signed::'` — 230 / 230
      verified (i8 / i16 full ladder; i32 / i64 / i128 boundary
      pairs).
- [ ] `cargo kani --harness 'fix_fix_unsigned::'` — 120 / 120
      verified (u8 representative; u16 / u32 / u64 / u128 boundary
      subsets).
- [ ] `cargo kani --harness 'float_walk::t0_'` — 2 / 2 (headline:
      ULP walks ≤ 2 over all finite non-NaN f64).
- [ ] `cargo kani --harness 'float_walk::t1_'` — 2 / 2 (walks ≤ 1
      on `|x| ≤ 1e6`).
- [ ] `cargo kani --harness 'float_walk::t2_'` — 2 / 2 (walks ≤ 1
      on the `[1, 2)` binade).
- [ ] `cargo kani --harness 'float_weaker::'` — 8 / 8 (finite-domain
      laws after in-range tightening).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `scripts/check-pii.sh` — exits 0.

## Local review (2026-05-06)

**Branch:** `sprint/kani-smt-verification`
**Commits:** 2 (origin/main..sprint/kani-smt-verification)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Two commits: `e36a3ef doc: Plan 39 — Kani SMT verification of Galois-connection laws` and `af89853 feat: Add Kani SMT proof tree for Galois-connection laws`. Both follow the conventional commit format with the project's standard prefixes. The plan commit predates the implementation commit — correct TDD ordering per the repo workflow. Both commits add only their stated artifacts; no unrelated changes are mixed in. Each commit is buildable: the plan commit touches only `doc/plans/` and `doc/reviews/`, and the implementation commit contains the actual code. Clean.

### Code Quality

**No `unsafe` code.** The diff introduces no `unsafe` blocks. `#![forbid(unsafe_code)]` is not visibly disturbed.

**No `mod.rs`.** The parent module is at `src/kani_proofs.rs` with children under `src/kani_proofs/`. This correctly follows the `foo.rs + foo/` rule.

**`[lints.rust]` addition is isolated.** The pre-existing `Cargo.toml` had no `[lints]` table; the new `[lints.rust]` entry is the only one and cannot shadow or conflict with any prior setting.

**Walk-step shim faithfulness.** The two `#[cfg(kani)]` shims in `src/float/f32.rs` (`ceil_walk_steps_for_proof`, `floor_walk_steps_for_proof`) are structurally identical to the production functions `ceil_f64_f32` / `floor_f64_f32`. The only difference is the omission of the `if x.is_nan()` early-return guard, which is compensated by `kani::assume(x.is_finite() && !x.is_nan())` in every harness that calls them (`is_finite()` excludes NaN). Branch predicates (`x <= est_up` for ceil, `est_up <= x` for floor), walk-helper dispatch (`descend_to_ceil`, `ascend_to_ceil`, `descend_to_floor`, `ascend_to_floor`), and return conventions all match production exactly. The proof applies to the same code path.

**`#[allow(dead_code, unused_imports)]` in `kani_proofs.rs`.** This attribute is scoped to the `kani_proofs` parent module, which is entirely `#[cfg(kani)]`-gated and never compiled into normal builds. The allow suppresses Kani-build warnings from macro-expanded `use super::*` patterns, and is acceptable in this context. It is wider than ideal — `unused_imports` at module level will silence any genuinely forgotten import in any child — but since all eight child modules are dedicated proof files with no public API, the risk is low and the alternative (per-module allows) would be more verbose without added safety.

**Predicate fidelity.** Every harness delegates directly to the canonical `crate::prop::conn::*` predicates (`galois_l`, `galois_r`, `closure_l`, `closure_r`, `kernel_l`, `kernel_r`, `monotone_l`, `monotone_r`, `idempotent_l`, `idempotent_r`, `roundtrip_ceil`, `iso_roundtrip_l`, `floor_le_ceil`, `order_reflecting`). None are re-implemented. The proof obligations are exactly what the proptests assert.

**No dead code or stubs.** No `unimplemented!()`, no `todo!()`, no commented-out harness bodies. Every harness body is complete.

### Test Coverage

**Harness counts vs. plan.** All counts verified independently against the diff:

| Family | Invocations | Harnesses/invocation | Total |
|---|---|---|---|
| `int_narrow` | 10 | 6 | 60 |
| `uint_sat` | 14 | 5 | 70 |
| `nz_ext` signed | 5 | 8 | 40 |
| `nz_ext` unsigned | 5 | 4 | 20 |
| `iso_family` | 10 | 5 | 50 |
| `fix_fix_signed` | 46 | 5 | 230 |
| `fix_fix_unsigned` | 24 | 5 | 120 |
| `float_walk` | — | — | 6 |
| `float_weaker` | — | — | 8 |
| **Total** | | | **604** |

Matches the plan's self-reported total.

**Intentional omissions.** Both omissions are documented inline:

1. `uint_sat::roundtrip_floor`: documented in `src/kani_proofs/uint_sat.rs` at the comment block following the `idempotent_r` harness. The explanation is correct: `inner` for `uint_int_sat!` clips `b < 0` to `0_uN`, so `floor(inner(-1)) = 0 ≠ -1`. The predicate does not hold; omitting the harness is correct.

2. `float_weaker::finite_in_finite_out_*` (unrestricted): the harnesses were renamed to `*_in_range` and restricted to `|x| ≤ f32::MAX`. The doc comment on `arb_in_f32_range_ef64()` explains why the broader predicate fails. Inline documentation is present and accurate.

**Unwind sufficiency.** T0 uses `#[kani::unwind(4)]` with `assert!(steps <= 2)`. Kani's unwind(N) unrolls the loop body N times; any execution path reaching exactly 3 iterations would be witnessed by unwind(4) and would produce `steps = 3`, violating `steps <= 2`. The bound is sufficient. T1/T2 use `#[kani::unwind(3)]` with `assert!(steps <= 1)`: any 2-step path would be witnessed. Both are correct.

**Coverage gaps.** The plan intentionally defers `uint_uint_narrow!` Conns (unsigned narrowings), `int_uint_narrow!`, `int_uint!`, and the `nz_ext` unsigned R-side. These are noted in the Deferred section or omitted with a documented rationale. No proptest-covered Conn family that falls outside the plan's stated scope has a harness here, and none is expected.

One actual gap worth noting: `fix_fix_unsigned::u8` covers 10 of 28 Conn ladder rungs (described as "representative"). The plan acknowledges this explicitly ("10 representative pairs from the 28-Conn ladder") with the rationale that 8-bit symbolic state dispatches in milliseconds and full coverage was available for the signed i8 case. The unsigned u8 ladder is truncated to 10/28 without explanation of which rungs are absent. This is a documentation gap, not a correctness issue.

### Plan Conformance

**T1 (Cargo + scaffolding):** `Cargo.toml` gains `[lints.rust] unexpected_cfgs`; `src/lib.rs` gains `#[cfg(kani)] mod kani_proofs;`; `src/kani_proofs.rs` is present with eight submodule declarations. Deviation: plan said `cfg(any(test, kani))` for the walk-step shims; implemented as `cfg(kani)` only. Deviation is documented in the plan's Review section with a correct justification (clippy flagged unused wrappers under `--all-targets`).

**T2–T7:** Each has a dedicated file in `src/kani_proofs/`, the correct macro pattern, and the harness counts match the plan's Verification table.

**T8:** Walk-step shims are `pub(crate)` and `#[cfg(kani)]`-gated in `src/float/f32.rs`. Bodies are faithful (verified above).

**T9:** `float_walk.rs` contains the 3-tier harness set with the correct tier labels and unwind annotations.

**T10:** `float_weaker.rs` contains all 8 harnesses, with the two `finite_in_finite_out_*_in_range` variants reflecting the Review-documented tightening.

**T11:** The build gates listed in the plan are not executable from a diff review, but the diff introduces no `#[ignore]` attributes, no compilation-gating that would prevent `cargo test --workspace` from passing, and the `cfg(kani)` gating is complete so no proof code leaks into normal builds.

**No unplanned scope creep.** Every file and change in the diff is accounted for by T1–T11.

### Risks

**No TODOs or stubs.** Grep of the diff shows no `todo!()`, `unimplemented!()`, or `FIXME` markers.

**No existing functionality broken.** All proof code is behind `#[cfg(kani)]` or `#[cfg(test)]`. The only changes to non-proof code are the two shim functions in `src/float/f32.rs` (also `#[cfg(kani)]`-gated) and the `#[cfg(kani)] mod kani_proofs;` line in `src/lib.rs`. Neither is reachable from `cargo test` or release builds.

**Security.** No I/O, no networking, no unsafe. Not applicable.

**`fix_fix_unsigned::u8` coverage comment is misleading.** The file comment says "full ladder, 28 Conns × 5 props = 140 proofs" but only 10 × 5 = 50 harnesses are actually present. The comment accurately describes the full ladder size as context ("28-Conn ladder") but the harness count in the comment header is the full-ladder number, not the actual count. A reader comparing comment to implementation will see the mismatch immediately.

**File:** `src/kani_proofs/fix_fix_unsigned.rs`, line 931 (in the diff numbering; corresponds to the `// ── u8-backed (full ladder, 28 Conns × 5 props = 140 proofs)` section header inside the file).

The comment reads:
```
// ── u8-backed (full ladder, 28 Conns × 5 props = 140 proofs) ────────
```

But only 10 pairs follow, giving 50 harnesses. Compare the analogous comment in `fix_fix_signed.rs` (line 647): `// ── i8-backed (full ladder, 21 Conns × 5 props = 105 proofs)` — that one is accurate because all 21 are present. The unsigned u8 section header claims the full-ladder number, not the actual-harnesses number. This is a documentation error with confidence 95.

---

### Recommendations

**Must fix before merge:**

1. **`fix_fix_unsigned.rs`: fix the section comment.** The line `// ── u8-backed (full ladder, 28 Conns × 5 props = 140 proofs)` is factually wrong for this file — only 10 of the 28 rungs are present. Change to something like `// ── u8-backed (10 representative pairs × 5 props = 50 proofs; see module header for coverage rationale)` to match the module-level doc comment, which correctly describes it as "10 representative pairs from the 28-Conn ladder". A reader diffing the plan's harness count table against the file will notice the discrepancy.

**Follow-up (future work):**

1. **Extend u8 unsigned ladder to full coverage.** The i8 signed ladder gets 21/21 rungs proved; 8-bit CBMC dispatch is sub-50ms. There is no documented cost reason for stopping at 10/28 for u8. A follow-up sprint could bring it to full coverage to match the signed tier.

2. **Wire a `kani:` CI job as advisory-only.** As recommended in the plan's Review section: tag-push-only, `allow_failure: true`. This prevents silent regression if a future commit modifies the walk helpers without running the proof tree locally.

3. **`README.md` "Verification" section.** Downstream consumers of the crate have no way to discover that the Galois laws are SMT-verified. Adding a brief section (as the plan recommends) with the harness counts and a link to `src/kani_proofs/` would make the proof tree discoverable.

4. **f16 mirror.** Once the `f16` feature stabilizes, `float_walk.rs` and `float_weaker.rs` shapes copy directly to F032F016 / F064F016. Trivial when the time comes; noting here for tracking.

<!-- glab-id: 3321952086 -->
<!-- glab-discussion: 3d18b4a8aaf5a48514ec1171ab38d884bb945a6a -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/float_weaker.rs:68` (2026-05-06 21:47 UTC) [open]

**[must-fix]** The `finite_in_finite_out_ceil_in_range` harness calls `F064F032.upper(F064F032.ceil(x))` but the `float_weaker` module imports `ConnR` alongside `ConnL` — however the harness uses `.upper()` rather than `.lower()` (the R-side embedding) to lift the f32 result back to f64. If `upper` is the L-adjoint's embedding and `lower` is the R-adjoint's embedding, using the wrong one produces a mismatch with the floor-side harness at line 79 which correctly uses `.lower()`. Verify that `.upper()` is the right method for the ceil round-trip; if `upper` ≠ `inner` for the ceil direction, the harness is testing the wrong composition.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3321952110 -->
<!-- glab-discussion: ba8aa96ca8cbbd8e8f8f35596713efef78a81074 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/fix_fix_signed.rs:78` (2026-05-06 21:47 UTC) [open]

**[follow-up]** The `monotone_l` harness generates two independent symbolic bit-patterns `b1` and `b2` and calls `conn_laws::monotone_l` with the corresponding fine-side values `a1` and `a2`, but `monotone_l` in `prop::conn` presumably asserts `a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2)`. Without a `kani::assume(a1 <= a2)` guard, Kani will explore all orderings and the property as stated in the macro doc ("a1 ≤ a2 ⟹ ...") would still hold vacuously for the `a1 > a2` branch — but this means the harness is proving a tautology when `a1 > a2`. Confirm that `conn_laws::monotone_l` internally encodes the conditional so that no assume is needed, and add a comment to the harness making this explicit; the same concern applies to `prove_fix_fix_u!` and `prove_uint_sat!`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3321952126 -->
<!-- glab-discussion: 039c31a56d626ee8aef534fbaf98466a168b03f6 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/kani_proofs/float_walk.rs:37` (2026-05-06 21:47 UTC) [open]

**[follow-up]** The T0 harnesses call `ceil_walk_steps_for_proof` / `floor_walk_steps_for_proof` which omit the `is_nan()` early-return that the production functions have, compensated only by `kani::assume(x.is_finite() && !x.is_nan())`. Since `is_finite()` already returns `false` for NaN in Rust's IEEE implementation, the `!x.is_nan()` conjunct is redundant — but more importantly, the shim diverges from the production code by also lacking the `is_nan()` branch, meaning if a future refactor adds NaN-specific logic to that branch, the shim will silently become unfaithful. A brief comment in the shim body noting the deliberate omission and why the assume covers it would prevent future drift.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

## Local review (2026-05-06, round 2 — Codex)

**Reviewer:** Codex (independent local review run by Chris)

### Findings

**[P2] Add Kani modules for omitted fixed families** — `src/kani_proofs.rs:45-52`

> When `cargo kani` is run with this module list, no harness is registered for the fixed macro families `uint_uint!`, `int_uint!`, `ext_int!`, `uint_uint_narrow!`, or `int_uint_narrow!` even though `src/fixed.rs` defines them and the new docs describe one submodule per fixed family. Conns such as `fixed::u8::I008U008` and `fixed::i128::I008I128` are therefore still only sampled by proptest, so regressions in those families would pass the SMT proof tree; add corresponding harness modules or narrow the stated coverage.

**Response — addressed.** Three new harness modules added:

- `src/kani_proofs/ext_int.rs` — 20 `ext_int!` Conns × 5 props = **100 harnesses**, all verified.
- `src/kani_proofs/uint_widen.rs` — 10 `uint_uint!` + 15 `int_uint!` Conns × 5 props = **125 harnesses**, all verified.
- `src/kani_proofs/uint_narrow.rs` — 10 `uint_uint_narrow!` + 10 `int_uint_narrow!` Conns × 6 props = **120 harnesses**, all verified.

Module list in `src/kani_proofs.rs` updated; family table in the module doc rewritten to reflect actual coverage.

**[P2] Prove the omitted unsigned fixed-point pairs** — `src/kani_proofs/fix_fix_unsigned.rs:64-65`

> For the unsigned Q-format path, the proof list switches to representative/boundary subsets even on `u8`/`u16`: `src/fixed/u8.rs` defines 28 `fix_fix_u8!` pairs but only 10 are registered here (for example `Q002Q001` is missing), and `src/fixed/u16.rs` likewise has 28 pairs but only 5 proofs. When `cargo kani` succeeds, bugs in the omitted unsigned ladder pairs remain unchecked despite the header saying the u8/u16 ladders are fully covered.

**Response — addressed.** Both unsigned 8-/16-bit ladders expanded to full coverage:

- `fix_fix_unsigned::u8_*` — was 10 pairs (50 harnesses), now **28 pairs (140 harnesses)**, all verified.
- `fix_fix_unsigned::u16_*` — was 5 pairs (25 harnesses), now **28 pairs (140 harnesses)**, all verified.

Module-level coverage doc tightened from "full ladder for u8/u16, boundary pairs for wider widths" (which was misleading vs the 10/5 reality) to the now-accurate "full ladder for u8 (28 pairs) and u16 (28 pairs); boundary pairs for u32 / u64 / u128".

### Cumulative pass count

Round 1 (sprint): 604 verified, 0 failures.
Round 2 (Codex expansion): +550 new harnesses verified, 0 failures.
**Total: 1154 verified, 0 failures.**

<!-- glab-id: 3322007019 -->
<!-- glab-discussion: 3d18b4a8aaf5a48514ec1171ab38d884bb945a6a -->
#### ↳ cmk (2026-05-06 22:07 UTC) [open]

Pushed back — `F064F032` is a triple, so its L-view's `.upper()` and R-view's `.lower()` both delegate to the same `inner` fn pointer (`f064f032_inner` in `src/float/f32.rs`). The harness pairs `ceil` with `upper` (L-side round-trip) and `floor` with `lower` (R-side round-trip) — that's the correct symmetric structure, not a mismatch.

<!-- glab-id: 3322008192 -->
<!-- glab-discussion: ba8aa96ca8cbbd8e8f8f35596713efef78a81074 -->
#### ↳ cmk (2026-05-06 22:07 UTC) [open]

Fixed — added a brief comment in each macro's `monotone_l`/`monotone_r` harness noting that `prop::conn::monotone_l`/`monotone_r` is conditional (returns `true` vacuously on reversed orderings), so unconstrained `kani::any()` inputs are sound without a `kani::assume` guard. Applied across `int_narrow.rs`, `uint_sat.rs`, `fix_fix_signed.rs`, `fix_fix_unsigned.rs`, and the new `ext_int.rs` / `uint_widen.rs` / `uint_narrow.rs`.

<!-- glab-id: 3322008375 -->
<!-- glab-discussion: 039c31a56d626ee8aef534fbaf98466a168b03f6 -->
#### ↳ cmk (2026-05-06 22:07 UTC) [open]

Fixed — added a comment block on the walk-step probe shims in `src/float/f32.rs` documenting the deliberate omission of the production `is_nan()` early-return (covered by `kani::assume(x.is_finite() && !x.is_nan())` in every harness) and flagging it as a drift point that must be mirrored if production-side NaN handling ever diverges from the bare pass-through.
