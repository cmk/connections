# Review — MR !94 (Plan 2026-05-10-02)

## Summary

- Move the `(A, B)` Galois pair from trait type parameters to associated
  types on `ConnL` / `ConnR`. The library has always honored the
  functional dependency `T → (A, B)`; associated types model that at
  the type level. `ConnK` becomes `ConnL + ConnR<A = ConnL::A,
  B = ConnL::B>`.
- Helper-fn bounds use the explicit pair `T: ConnL<A = A, B = B> +
  ConnR<A = A, B = B>` because `T: ConnK<A = A, B = B>` is ambiguous
  (E0222) — `ConnK` inherits A/B through two paths. `ConnK` survives
  as a marker trait.
- Rustdoc: typenum link expansions under `target/doc/connections/`
  drop from 3888 to 1964 (49%). Impl headers, Implementors lists, and
  method signatures all render cleanly with the `U12`-style alias
  preserved; the residual expansion is confined to the per-impl
  `type A = … / type B = …` assignment lines, which rustdoc 1.85
  still normalizes through every alias level.

## Test plan

- [x] `cargo build --features testing,macros,time` clean
- [x] `cargo test --workspace` — 1356 lib + 168×9 host-file integration
      batteries, all green
- [x] `cargo clippy --all-targets --features testing,macros,time -- -D warnings`
      clean
- [x] `cargo doc --no-deps --features testing,macros,time` clean
- [x] Spot-checked rendered `struct.F032Q012.html`: header reads
      `impl ConnL for F032Q012`, method sig reads
      `fn conn_l(&self) -> Conn<…, Extended<FixedI16<U12>>, L>`
- [x] `compile_fail/round_on_l_conn` regenerated via
      `TRYBUILD=overwrite` for the new bound text

## Local review (2026-05-10)

**Branch:** sprint/conn-assoc-types
**Commits:** 2 (origin/main..sprint/conn-assoc-types)
**Reviewer:** Claude (sonnet, independent)

---

# Review — MR !94 (Plan 2026-05-10-02) — `ConnL`/`ConnR` to associated types

## Pass 1 — Cold review

### P1.A — Trait-claim audit

This sprint reshapes existing traits; it does not add new `pub const` Conn instances, new `iso!` invocations, or new law-bearing `impl` blocks beyond the blanket impls. Items in scope:

**1. `impl<A: Copy, B: Copy> ConnL for Conn<A, B, L>`**
- Contract: `ConnL` claims `conn_l(&self) -> Conn<Self::A, Self::B, L>`, with `ceil` / `upper` dispatch through it.
- Implementation: `fn conn_l(&self) -> Conn<A, B, L> { *self }`. `ceil` and `upper` are inherited defaults dispatching through `conn_l()`. Behavior is identical to before.
- Consistent.

**2. `impl<A: Copy, B: Copy> ConnR for Conn<A, B, R>`** — same analysis. Consistent.

**3. `pub trait ConnK: ConnL + ConnR<A = <Self as ConnL>::A, B = <Self as ConnL>::B>`**
- Contract: shorthand for "both sides, same `(A, B)`." Equality bound is the formal type-level statement of the functional dependency `T → (A, B)`.
- Implementation: blanket `impl<T> ConnK for T where T: ConnL + ConnR<A = <T as ConnL>::A, B = <T as ConnL>::B>` matches the supertrait bound exactly.
- Consistent.

**4. Codegen macros (`conn_k!`, `compose_k!`, `nz_int_ext!`, `lift_k!`)**
- Each emits `impl ConnL for $name { type A = $A; type B = $B; … }` and `impl ConnR for $name { type A = $A; type B = $B; … }`. The `A` / `B` assignments agree on both sides. The `conn_l` / `conn_r` return types match the associated types. Consistent across all four macro sites.

**5.** No new `iso!` invocations, no new `Conn` constants, no new law-bearing trait impls beyond the above.

Trait-claim audit: no soundness issues. All changed impls are behavior-preserving reshapes.

### P1.B — Standard review

#### Commit hygiene

Two commits, both conventionally prefixed. The feat commit bundles T1–T8 (trait reshape, blanket impls, ConnK, macros, helper-fn bounds, prop preds, extended lifters, doc cleanup, test cleanup). Large but coherent — every change is mechanically required by the trait reshape. No unrelated changes mixed in. Acceptable.

#### Code quality

**Stale doc comments referencing the old parametric trait shape — five sites:**

`src/conn.rs:57`:
```
// `T: ConnL<A, B>` accepts both triple markers and raw `Conn<A,B,L>`
```
Post-reshape, the correct spelling is `T: ConnL<A = A, B = B>`. `ConnL<A, B>` is the old type-parameter form, no longer valid syntax.

`src/conn.rs:469` (in `ConnL` trait's own doc):
```
/// generic bounds `T: ConnL<A, B>` accept both shapes uniformly.
```
Same problem.

`src/lib.rs:214`:
```
// Resolution is by argument type — these take `&T: ConnK<A, B>` as
```
`ConnK<A, B>` never existed and doesn't now (ConnK is parameter-free). Should say `&T: ConnK` or `&T: ConnL<A=A,B=B> + ConnR<A=A,B=B>`.

`src/prop/conn.rs:4`:
```
//! `&Conn<A, B, R>` (R-laws), or `&T: ConnK<A, B>` (laws spanning
```
Same: `ConnK<A, B>` is not the post-sprint spelling.

`src/extended.rs:342`:
```
/// `$parent` must impl `ConnK<A, B>` (i.e. be either a triple marker
```
Post-sprint, `ConnK` takes no type parameters.

These are doc comments, not intra-doc links with backticks rustdoc compiles, so they don't cause a build failure. But this sprint's stated purpose is the trait shape change — shipping it with five doc sites spelling the old API directly contradicts T7's intent.

**`compose_k!` type inference:** The old form `<$t1 as ConnL<$A, $B>>::conn_l(&$t1)` pinned the intermediate type `$B` via turbofish. The new form `<$t1 as ConnL>::conn_l(&$t1)` relies on inference through `compose_l!`. Works today because the associated types on the outer impl are fixed by the macro args at expansion time, not inferred — but the inference chain has one fewer explicit anchor.

No unsafe code. No new dependencies. No dead code introduced.

#### Test coverage

All existing Galois law batteries are behavior-preserving (no new `#[ignore]`). The diff updates `tests/macros_feature_smoke.rs` with renamed identifiers (`SMOKE_EXT08`, `SMOKE_NZ_U8`) and fixes the `SmokeNzI8::R.floor(0_i8)` dead-code issue. The `compile_fail/round_on_l_conn` test is updated with regenerated stderr. No new property tests are needed — this sprint adds no new Conn instances or algorithms.

The plan's verification spot-check states: `fn use_round<T: ConnK>(t: &T, x: T::A) -> T::A where T::A: Copy { round(t, x) }`. As written this would not compile: `round`'s bound is `T: ConnL<A=A, B=B> + ConnR<A=A, B=B>`, and `T: ConnK` alone doesn't satisfy it (the E0222 deviation the §Review documents). The spot-check is plan documentation, not a test, so the discrepancy is latent.

#### Risks

None significant. The migration is mechanical and behavior-preserving.

## Pass 2 — Plan-aware review

### P2.A — Test-exception escalation

No relaxation-renamed properties, no `#[ignore]`d tests, no "weaker predicate" language in the plan's Verification table. Plan is explicit that the migration is behavior-preserving and all existing law batteries pass unchanged. No escalation required.

### P2.B — Plan conformance

T1–T6 and T8 are fully implemented in the diff. T7 (doctests + README) was scoped to a "recompile pass, no content change expected" — but that scope was too narrow. Five doc-comment sites in changed files still describe the old API. The plan should have included a scan-and-update step.

The `midpoint` function listed in T5's audit list does not appear in either the old or new diff — checking source confirms `midpoint` does not exist. Stale entry in the plan's T5 audit list, not a missing implementation.

The plan's §Review/Deviation section correctly documents why helper signatures use `T: ConnL<A=A,B=B> + ConnR<A=A,B=B>` instead of `T: ConnK<A=A,B=B>`, and why `ConnK` survives as a marker trait. Consistent with the diff.

The `tests/macros_feature_smoke.rs` cleanup is mentioned in the plan's §Review section but was not in the original task list — it surfaced when clippy ran with `--features testing,macros,time`. Documented after the fact. Genuine cleanup, not hidden scope creep.

## Recommendations

**Must fix before push:**

1. **Five stale doc comments referencing `ConnL<A, B>` / `ConnR<A, B>` / `ConnK<A, B>` — the old parametric spelling.** This sprint is specifically about the trait shape change, and shipping with five doc sites spelling the old API is a direct contradiction of T7.

   - `src/conn.rs:57`: `T: ConnL<A, B>` → `T: ConnL<A = A, B = B>`
   - `src/conn.rs:469`: `T: ConnL<A, B>` → `T: ConnL<A = A, B = B>`
   - `src/lib.rs:214`: `&T: ConnK<A, B>` → `&T: ConnL<A=A,B=B> + ConnR<A=A,B=B>` (or remove parameters)
   - `src/prop/conn.rs:4`: `&T: ConnK<A, B>` → `&T: ConnK` (or explicit pair)
   - `src/extended.rs:342`: `ConnK<A, B>` → `ConnK`

   Confidence: 90. Not compile-checked (bare comments, not intra-doc links), so build passes — but `cargo doc` won't catch them and they'll mislead users.

**Follow-up (future work):**

2. **Plan's spot-check `fn use_round<T: ConnK>` is not compilable given the E0222 deviation.** Plan's §Review documents E0222 correctly but the §Verification spot-check wasn't updated to match. No runtime/CI impact (it's plan documentation, not a test), but anyone copying it as a usage example will hit the bound mismatch.

3. **`compose_k!` no longer anchors intermediate type `$B` via turbofish.** Works today through inference; a `let _: Conn<$A, $B, L> = <$t1 as ConnL>::conn_l(&$t1);` intermediate would restore the explicit anchor. Low priority — defensive against future changes to `compose_l!`'s return-type handling.
