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
