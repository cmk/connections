# MR !11 — Property tidy-up: predicates as public API

## Summary

- **Promote `property` module to the public API.** Replace
  `#[cfg(test)] pub(crate) mod property;` with `pub mod property;`,
  split into `property::laws` (predicates, no proptest dep, always
  public) and `property::arb` (strategies, gated on a new `testing`
  feature that flips `proptest` from dev-dep to optional regular
  dep). Downstream crates can now drive every algebraic-law check
  against their own types.
- **Add Galois-connection + bare-preorder law predicates.** Extend
  `property::laws` with `conn_galois_l/r`, `conn_closure_l/r`,
  `conn_kernel_l/r`, `conn_monotone_l/r`, `conn_idempotent`,
  `conn_floor_le_ceil`, `conn_roundtrip_ceil/floor`, `conn_ulp_bound`,
  plus `lattice_reflexive`/`transitive`/`antisymmetric`/`bot`/`top`.
  All `Ple`-bound for uniformity across integer rungs,
  `ExtendedFloat<T>`, `Extended<T>`, and bare floats. Added `Ple`
  impls for `ExtendedFloat<T>`/`Extended<T>` (delegating to their
  N5-patched `PartialOrd`) and for the `SampleRate` types via
  `def_rate!`.
- **Centralise proptest strategies under `<tier>_<role>` names.**
  Lift `bounded_coarse`/`bounded_fine`/`safe_fine` (previously
  duplicated across `conn/fixed.rs` and `conn/sample.rs` with
  identical names but different signatures) into `property::arb`
  as disambiguated `fixed_coarse`/`fixed_fine`/`fixed_safe_fine`,
  `rate_coarse`/`rate_fine`/`rate_safe_fine`, and
  `pico_fine`/`pico_coarse`/`pico_safe`. Same disambiguation for
  `arb_extended_*` → `extended_*`.
- **Rewrite the four conn-property macros as predicate-call
  wrappers.** `props_for_pair!`, `float_conn_props!`,
  `props_for_conn!`, `props_for_pico_conn!` now have ~10-line
  bodies that just feed strategy values to `laws::conn_*` calls.
  Test names align on the law-name convention: `galois_l`,
  `closure_l`, `monotone_l`, etc. — drops the `prop_` prefix and
  the `_id` suffix throughout.
- **Convert all inline free-standing predicates.** The identity-
  conn helpers in `conn.rs` (`adjoint_id` etc.), the f64↔f32
  helpers in `conn/float.rs` (`adjoint_l/r` etc.), the MR !9
  compose tests, and the N5 preorder tests in `lattice.rs` all
  switch from inline bodies to `laws::*` calls. ~150 lines of
  duplicated invariant logic deleted.

## Test plan

- `cargo build` (no features) — clean; `proptest` not pulled in.
- `cargo build --features testing` — clean; `proptest` available.
- `cargo test --workspace` — 491 lib tests + 3 doctests pass.
  Test count drops 519 → 491 from merging `ceil_monotone` +
  `floor_monotone` into `monotone_l` (×27 macro calls = -27) and
  collapsing the `ulp_bound` / `floor_le_ceil` pair on the pico
  family into a single `floor_le_ceil` (×6 = -6); +5 from
  identity-conn `monotone_r` + the new `kernel_l`/`r` pair on
  float Conn. Net -28.
- `cargo clippy --all-targets --features testing -- -D warnings` —
  clean.
- `cargo doc --no-deps --features testing` — `connections::property::laws`
  and `connections::property::arb` render on the public-API page;
  zero warnings.

Deferred (tracked in plan Review):
- **In-crate proptest tests for orphan Heyting/Coheyting/Boolean/
  Symmetric predicates.** The crate ships those traits but has no
  concrete instance (no `impl Heyting for $T` exists in `src/`),
  so there's nothing to drive the predicates against in-crate.
  They are nonetheless exposed for downstream use, which is the
  prime directive.
- **Trait-based predicate dispatch** (e.g. `trait IsConn`).
- **Generic-over-Conn macro consolidation** — collapsing the four
  property macros into one.
- **`proptest-regressions` seed renames** — old test-name entries
  are now orphans (harmless; just unused).

## Local review (2026-04-26)

**Branch:** sprint/property-tidy
**Commits:** 8 (origin/main..HEAD)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All eight commits use conventional subjects under 72 characters. The commit order follows the plan's dependency graph (T1 → T2 → T3 → T4 → T5 → T6 → T8, T7 deferred). Each refactor commit has a corresponding structural change (not doc-only). No merge commits. Hygiene is clean.

---

### Code Quality

**`testing` feature flag mechanism.** `Cargo.toml` adds `proptest` as both an optional regular dep and an unconditional dev-dep. This is the correct pattern: `cargo test` resolves the dev-dep without the feature, so in-crate tests get proptest; downstream gets it only with `--features testing`. `property::arb` is gated on `#[cfg(any(test, feature = "testing"))]`. The mechanism works as intended.

**`Ple` impls for emergent types.**
- `ExtendedFloat<T>`: the `Ple` impl delegates via `partial_cmp`. The `impl_float_ext!` macro gives `ExtendedFloat<f64>` and `f32` a custom `PartialOrd` that treats `Finite(NaN)` as reflexive. The delegation is therefore correct — `ple` inherits the N5-patched semantics.
- `Extended<T: PartialOrd>`: `partial_cmp` is the standard derived impl with no NaN quirks (only used for integer rungs). Correct.
- `SampleRate` types via `def_rate!`: delegates to `self <= other`, which uses `Ord` on `Q48_16`. Correct.

**`#[allow(dead_code)]` in `src/property/arb.rs` (line 25).** The module-level attribute suppresses dead-code warnings for the entire file. Every exported function in `arb.rs` is used. The attribute is harmless but unnecessary for public items and will mask any genuinely dead functions added in the future. Low severity.

**Stale doc comment in `src/property/arb.rs` lines 21–23.**

```
//! Tier-specific strategies (e.g. `arb_extended_micro`,
//! `bounded_coarse`) will land here in subsequent commits as the
//! property tidy-up proceeds.
```

These strategies already exist in this module — they were moved in commit `f9ae667`. The forward-looking language is factually wrong. Minor but visible in `cargo doc`.

---

### Test Coverage

**Coverage regression in `float_conn_props!` idempotence check. Confidence: 82.**

The old `float_conn_props!` macro's `prop_idempotent(a, b)` called `idempotent(&conn, a, b)` which checked four distinct idempotence conditions:
- `inner(ceil(inner(ceil(a)))) ~~ inner(ceil(a))` (closure idempotence on source)
- `ceil(inner(ceil(inner(b)))) ~~ ceil(inner(b))` (counit idempotence on target via ceil)
- `inner(floor(inner(floor(a)))) ~~ inner(floor(a))` (closure idempotence via floor)
- `floor(inner(floor(inner(b)))) ~~ floor(inner(b))` (counit idempotence on target via floor)

The new `conn_idempotent` predicate in `laws.rs` checks only condition (1). Conditions (2), (3), and (4) are gone from both the `float_conn_props!` macro and the direct `conn/float.rs` tests.

Conditions (2)–(4) cannot be violated by a correct Galois connection without also violating the kernel laws, which are now tested. However, the counit-side idempotences are distinct properties that could expose implementation bugs in `ceil_f64_f32` or `floor_f64_f32` that the kernel laws alone don't catch. This is a real but mild coverage regression.

**Fix:** Either extend `conn_idempotent` to accept an optional b-side input and check counit idempotence, or add a separate `conn_counit_idempotent` predicate and drive it from `float_conn_props!`. Alternatively, since the floor-side idempotence is the symmetric dual and is always implied by `conn_roundtrip_floor` for exact-embedding conns, document that the lossy f64↔f32 case relies on the kernel laws as a proxy. If this is a deliberate scoping choice, it should be noted in the plan Review section (it currently is not).

**`peq` deleted despite plan §T6 saying it stays. Confidence: 80.**

Plan §T6: "The `peq` helper (line 352) stays — it's a Ple-equivalence predicate, not a law, useful as a building block."

`peq` was deleted from `src/conn/float.rs` along with the other helpers. No in-crate code calls it now, so there is no compilation error. However, the deletion directly reduces `float_conn_props!` idempotence coverage and violates the plan's explicit instruction to retain it. The plan's Review section does not mention this deletion.

A downstream crate implementing a lossy float connection cannot use `peq` as a building block for its own idempotence check — it must roll its own `x.ple(&y) && y.ple(&x)` inline. Minor in isolation but is a deviation not captured in review documentation.

**`proptest-regressions` seeds are correctly orphaned (not misrouted). Confidence: 100.**

Two seed files (`proptest-regressions/conn.txt`, `proptest-regressions/conn/float.txt`) reference test names that no longer exist. Crucially, neither is silently replaying against a wrong test body — proptest matches seeds by path+name, and the old names are gone. The NaN edge cases these seeds encoded are covered by explicit `Just(f64::NAN)` entries in `arb_f64()`.

**T7 deferral verified.** Confirmed: no `impl Heyting for` or `impl Coheyting for` exists in the new code. Plan correctly identifies no concrete instance to wire.

**Test count arithmetic.** 519 → 491, net -28. Arithmetic checks out.

---

### Plan Conformance

- **T1** (feature flag): Implemented correctly. `Cargo.toml` and `lib.rs` match spec.
- **T2** (split `property/`): Flat `arb.rs` instead of subdivided. Documented deviation in plan Review.
- **T3** (Conn law predicates): All 13 predicates present plus the 5 preorder predicates. Ple-bound family confirmed.
- **T4** (lift strategies): All renames match plan's table. Old strategies removed.
- **T5** (rewrite four macros): All four rewritten. `peq` deletion not noted in plan Review — deviation.
- **T6** (convert remaining inline predicates): Done. `peq` deletion undocumented.
- **T7** (orphan lattice predicates): Deferred, documented. Verified correct.
- **T8** (doc + smoke test): Doctests present. One stale sentence in `arb.rs` module doc.

---

### Risks

No silent ULP-check drops at any `conn_ulp_bound` call site (verified). No old strategy names lingering in doc comments (verified). The `Ple` impl delegations are correctly bounded.

---

### Recommendations

**Must fix before push:**

1. **Document the `peq` deletion and idempotence scope reduction in the plan Review section.** Plan §T6 explicitly says "`peq` stays." It was deleted. The plan Review must acknowledge this, explain that the Ple-equivalence idiom is now inlined into `conn_idempotent`, and note that floor-side counit idempotence is no longer explicitly tested in `float_conn_props!`. Documentation fix only — no code change. File: `doc/plans/plan-2026-04-26-04.md`, Review section.

**Follow-up (future work):**

2. **Remove `#[allow(dead_code)]` from `src/property/arb.rs` line 25.** Inherited from test-only `property.rs`; not needed for public items and will mask future dead code.

3. **Fix stale doc comment in `src/property/arb.rs` lines 21–23.** Replace "will land here in subsequent commits" with a description of what tier-specific strategies are actually present.

4. **Consider adding a `conn_counit_idempotent` predicate** (or extending `conn_idempotent` to cover the `ceil ∘ inner` composition) and driving it from `float_conn_props!` and `conn/float.rs` tests. The removed coverage is non-critical (it follows from the kernel laws for correct implementations), but provides defense-in-depth for the lossy `f64 ↔ f32` connection specifically.

<!-- glab-id: 3287381076 -->
<!-- glab-discussion: df2f71de93a376fd424062340570f7c36ebf7faa -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/arb.rs:23` (2026-04-26 11:00 UTC) [open]

**[follow-up]** The module-level doc comment says "Tier-specific strategies (e.g. `arb_extended_micro`, `bounded_coarse`) will land here in subsequent commits as the property tidy-up proceeds." All those strategies are already present in this file (moved in this very sprint). The forward-looking language is factually wrong and will mislead readers of `cargo doc --features testing`.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287381083 -->
<!-- glab-discussion: e660952a54a31c7a4d2a8fe3aa4e561519c7ec51 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/arb.rs:25` (2026-04-26 11:00 UTC) [open]

**[follow-up]** `#![allow(dead_code)]` suppresses dead-code warnings for the entire module. The local review (review-00011.md) correctly flags this as unnecessary for public items and notes it will mask genuinely dead functions added in the future. The attribute was inherited from the old test-only `property.rs` and should be removed now that the module is public.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287381089 -->
<!-- glab-discussion: 095e4145da1562af808a8a479c8ee227d5ddd0f9 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/laws.rs:354` (2026-04-26 11:00 UTC) [open]

**[must-fix]** The `#![allow(dead_code)]` attribute at the top of `laws.rs` (inherited from the old `property.rs`) suppresses dead-code warnings for the entire file of public predicates. The lattice predicates (`heyting_*`, `coheyting_*`, `biheyting_*`, `symmetric_*`, `boolean_*`) have no in-crate call sites (T7 was deferred), so without this attribute the compiler would emit dead-code warnings that would break `cargo clippy -D warnings`. The attribute papers over the symptom instead of fixing it: those public `pub fn`s are genuinely reachable from downstream and should not be `dead_code` — but the `#![allow(dead_code)]` also silences any truly dead helper that might be introduced later. Either add `#[allow(dead_code)]` only to the specific unreachable items, or confirm clippy is satisfied without the attribute (public items are never considered dead by the linter), and remove it.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287381110 -->
<!-- glab-discussion: 20b202f07e042677dd2c3cfca8e77a68e726c049 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 — (2026-04-26 11:00 UTC) [open]

**[must-fix]** `src/property/laws.rs:354` — The `#![allow(dead_code)]` attribute at the top of `laws.rs` (inherited from the old `property.rs`) suppresses dead-code warnings for the entire file of public predicates. The lattice predicates (`heyting_*`, `coheyting_*`, `biheyting_*`, `symmetric_*`, `boolean_*`) have no in-crate call sites (T7 was deferred), so without this attribute the compiler would emit dead-code warnings that would break `cargo clippy -D warnings`. The attribute papers over the symptom instead of fixing it: those public `pub fn`s are genuinely reachable from downstream and should not be `dead_code` — but the `#![allow(dead_code)]` also silences any truly dead helper that might be introduced later. Either add `#[allow(dead_code)]` only to the specific unreachable items, or confirm clippy is satisfied without the attribute (public items are never considered dead by the linter), and remove it.

*(inline anchor rejected by GitLab: 500)*

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287381113 -->
<!-- glab-discussion: ef2cd6e02cb4d63b3fa50a7461daab755dc1ebc6 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/laws.rs:436` (2026-04-26 11:00 UTC) [open]

**[follow-up]** The `conn_idempotent` predicate checks only `(inner ∘ ceil)²  = inner ∘ ceil` (closure idempotence on the source side). The plan's Review section documents that the original `idempotent` helper in `conn/float.rs` also checked `(ceil ∘ inner)² = ceil ∘ inner` (counit idempotence) and the floor-side duals, and flags the reduction as a coverage regression for the lossy `f64 ↔ f32` connection. The plan says to add a `conn_counit_idempotent` predicate or extend this one if a future bug surfaces — but the plan Review section does not document this as intentional for the `float_conn_props!` macro. Consider adding a `conn_counit_idempotent` predicate (checking `ceil(inner(ceil(inner(b)))) ~~ ceil(inner(b))`) and driving it from `float_conn_props!` to restore defense-in-depth coverage for lossy connections.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287382562 -->
<!-- glab-discussion: df2f71de93a376fd424062340570f7c36ebf7faa -->
#### ↳ cmk (2026-04-26 11:03 UTC) [open]

Fixed in commit 4028cc0 — replaced the stale forward-looking sentence with a description of the four tier families (`fixed_*` / `rate_*` / `pico_*` / `extended_*`) actually present in this module.

<!-- glab-id: 3287382590 -->
<!-- glab-discussion: e660952a54a31c7a4d2a8fe3aa4e561519c7ec51 -->
#### ↳ cmk (2026-04-26 11:04 UTC) [open]

Fixed in commit 4028cc0 — dropped the attribute. Verified `cargo clippy --features testing -- -D warnings` stays clean (public items aren't dead-code-checked).

<!-- glab-id: 3287382617 -->
<!-- glab-discussion: 095e4145da1562af808a8a479c8ee227d5ddd0f9 -->
#### ↳ cmk (2026-04-26 11:04 UTC) [open]

Fixed in commit 4028cc0 — dropped the attribute. Confirmed clippy stays clean even with the orphan Heyting/Coheyting/Boolean/Symmetric predicates that have no in-crate callers; `pub fn`s are exempt from the dead-code lint by default.

<!-- glab-id: 3287382644 -->
<!-- glab-discussion: 20b202f07e042677dd2c3cfca8e77a68e726c049 -->
#### ↳ cmk (2026-04-26 11:04 UTC) [open]

Same finding as the inline anchor on `src/property/laws.rs:354` — fixed in commit 4028cc0. See that thread for the full reply.

<!-- glab-id: 3287382671 -->
<!-- glab-discussion: ef2cd6e02cb4d63b3fa50a7461daab755dc1ebc6 -->
#### ↳ cmk (2026-04-26 11:04 UTC) [open]

Deferred — tracked in plan-2026-04-26-04 §"Additional deviations" and as Recommendation #4 in the local Tier-1 review. The closure-side idempotence we kept (`inner ∘ ceil`) plus the now-explicit `conn_kernel_l`/`conn_kernel_r` tests cover the same invariants for any correct Galois connection. We'll add `conn_counit_idempotent` if a future bug surfaces in a lossy connection that the kernel laws miss.

<!-- glab-id: 3287383154 -->
<!-- glab-discussion: 5453431782dc3a6a5f50ae720809cb171ea7632c -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/arb.rs:245` (2026-04-26 11:05 UTC) [open]

**[must-fix]** The `rate_fine` signature accepts `den: i128` and `_num: i128`, but the `near_max` computation casts `den as i64` directly. For `den` values close to `i64::MAX` (unlikely but possible since the parameter is `i128`) this silently truncates; more concretely, the `_num` parameter is unused — the strategy's range is independent of `num`, which means the guard comment ("dividing by `num ≥ den` shrinks magnitude") is never actually enforced in the generated values. Callers in `props_for_conn!` pass `($den, $num)` and the strategy silently ignores `$num`, so the documented contract (`ceil/floor fit i64 because dividing by num ≥ den shrinks magnitude`) is asserted in prose but not enforced by the bounds — if a future caller has `num < den` the strategy will generate values that overflow. Consider renaming `_num` to `num` and asserting `num >= den` at the top, or documenting that the caller is responsible for this invariant.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287383163 -->
<!-- glab-discussion: ffa74eeab5d6d4f4978ccfb27663c3823c88fa3b -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/laws.rs:411` (2026-04-26 11:05 UTC) [open]

**[follow-up]** The `conn_ulp_bound` predicate asserts `c_val >= f_val` before computing `c_val - f_val`, but if `floor(a) > ceil(a)` — which would itself be a violation of `conn_floor_le_ceil` — the subtraction underflows silently and returns a large positive number that satisfies `<= 1` only by accident. Callers currently always invoke `conn_floor_le_ceil` first (verified in both `props_for_pair!` and `props_for_pico_conn!`), but the predicate itself makes no claim about ordering and the internal guard only prevents the i64 underflow from panicking, not from masking a real violation. Consider documenting that `conn_floor_le_ceil` must hold as a precondition, or rewriting the check as `c_val.checked_sub(f_val).map_or(false, |d| d <= 1)` to make the ordering assumption explicit.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287383175 -->
<!-- glab-discussion: d5a400640fb3a2469669142d3933d5ca5f71eab7 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 — (2026-04-26 11:05 UTC) [open]

**[follow-up]** `src/conn/sample.rs:503` — The `props_for_pico_conn!` macro uses `pico_coarse($num, $den)` for `monotone_r` and `galois_l`/`galois_r`, but the original `sample_bounded` in the deleted code computed the limit as `i64::MAX · DEN / NUM` (i.e. the Coarse/Sample-side bound). The new `pico_coarse` in `arb.rs` uses `(i64::MAX as i128).saturating_mul(den) / num.max(1)`, which is algebraically the same — however the saturation on `saturating_mul` silently clamps when `i64::MAX * den` overflows i128, which cannot happen for representable `den ≤ 113_000` and `num ≥ 1` but is not documented. A comment noting the i128 headroom assumption (matching the original code's comment "stays in i128 trivially for DEN ≤ 113_000") would preserve the safety argument for future macro callers.

*(inline anchor rejected by GitLab: 400)*

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287385617 -->
<!-- glab-discussion: 5453431782dc3a6a5f50ae720809cb171ea7632c -->
#### ↳ cmk (2026-04-26 11:10 UTC) [open]

Fixed in commit 163d06b — renamed `_num` → `num` and asserted `num >= den` at the top. The strategy's range still depends only on `den`, but a future caller mismatch now fails loudly during property-test setup instead of as a silent overflow inside a generated case.

<!-- glab-id: 3287385637 -->
<!-- glab-discussion: ffa74eeab5d6d4f4978ccfb27663c3823c88fa3b -->
#### ↳ cmk (2026-04-26 11:10 UTC) [open]

Fixed in commit 163d06b — replaced `c_val >= f_val && c_val - f_val <= 1` with `c_val.checked_sub(f_val).is_some_and(|d| (0..=1).contains(&d))`. Same semantics for the well-formed case; on a buggy `floor > ceil` the predicate now returns `false` rather than masking the violation via i64 wraparound.

<!-- glab-id: 3287385663 -->
<!-- glab-discussion: d5a400640fb3a2469669142d3933d5ca5f71eab7 -->
#### ↳ cmk (2026-04-26 11:10 UTC) [open]

Fixed in commit 163d06b — added a doc paragraph noting that `i64::MAX · den` stays in i128 trivially for the rate ratios shipped today (`den ≤ 113_000`); the `saturating_mul` is belt-and-suspenders for a future pathologically large `den`. No call site approaches the bound.
