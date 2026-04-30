# MR !45 — Plan 29: Phantom kind tag + 2-fn Conn with marker-type triples

## Summary

- Reshape `Conn` to a strict 2-fn-pointer struct kind-tagged by `L` /
  `R`, with adjoint triples encoded as zero-sized marker types
  implementing `ViewL` / `ViewR` projection traits. Mirrors Haskell's
  `Cast (k :: Side) a b` discipline at the type level: kind-mismatched
  predicate / accessor calls (`floor` on an `L`-Conn, `galois_l` on an
  `R`-Conn, etc.) become compile errors instead of runtime test
  failures. 4 trybuild compile-fail fixtures pin the discipline.
- Adjoint triples ship as unit-struct markers via the `triple! { pub
  NAME : A => B { ceil, inner, floor } }` declaration-form macro; their
  L-view and R-view `Conn`s are accessed via `NAME::L` / `NAME::R` (or
  via default `.ceil()` / `.inner()` / `.floor()` methods on `ViewL` /
  `ViewR` directly). Two-sided ops (`round`, `truncate`, `interval`,
  `midpoint`, `median` + lifters) bind on the `Triple<A, B>`
  super-trait. `compose!` (declaration form) and `compose_l!` /
  `compose_r!` (variadic same-kind) cover the composition surface.
- Migration scope: 28 macro-generated triples (`ext_int!`,
  `nz_int_ext!`, `fix_fix_*!`) + 10 cross-crate iso consts + 13
  standalone triples (float / time / addr) → markers; one-sided
  `new_l` / `new_r` consts stay as `Conn` values. All 1172 lib tests +
  16 integration suites + 36 doctests + 4 compile-fail fixtures green;
  clippy + fmt clean.

## Test plan

- [ ] `cargo test --workspace` passes (1172 lib + 1080+ integration
      proptests + 36 doctests + 4 compile-fail fixtures, all green
      locally).
- [ ] `cargo clippy --all-targets -- -D warnings` clean.
- [ ] `cargo fmt --all -- --check` clean.
- [ ] `compile_fail::kind_discipline` rejects all 4 wrong-kind fixtures
      (`floor` on `L`, `ceiling` on `R`, `galois_l` on `R`-kind,
      `galois_r` on `L`-kind).
- [ ] Spot-check `triple!` macro: a fresh `pub TRIPLE : A => B { ... }`
      declaration produces a unit-struct marker satisfying `Triple<A, B>`
      (covered by the migrated callsites — every `ext_int!` /
      `fix_fix_*!` invocation exercises the macro path).
- [ ] Spot-check `compose!`: composing two triple markers produces a
      fresh marker satisfying `Triple<A, C>` (verified by the
      `compose_*_step_matches_handcoded_at_samples` proptest battery
      in `src/conn.rs::tests`).
- [ ] Spot-check default-method dispatch: `MARKER.ceil(x)` /
      `MARKER.inner(x)` / `MARKER.floor(x)` resolve via `ViewL` /
      `ViewR` defaults when those traits are in scope (covered by
      restored doctests and per-Conn test blocks).

## Local review (2026-04-30)

**Branch:** sprint/phantom
**Commits:** 2 (origin/main..sprint/phantom)
**Reviewer:** Claude (sonnet, **author self-review**) — Tier 1 independent agent hit the org usage cap before producing output. Self-reviews are weaker than the independent read /sprint-review normally produces; treat the must-fix below as authoritative but the "all clear" sections as provisional. Tier 2 (CI + GitLab Duo) will provide the truly independent pass.

---

### Commit Hygiene

Two commits, both conventional and atomic.

- `5a4a033 feat: Phantom kind tag + 2-fn Conn with marker-type triples (Plan 29)` — 70-char subject, comprehensive body. Squashed work from Sprint A staging + Sprint B target per the user's explicit instruction; squash leaves the tree green.
- `2ebb2a6 doc: Restore migrated doctests under new kind-tagged API` — 56 chars, scoped strictly to doctest restoration + the review-00045.md skeleton (folded via `--amend`).

Both leave the repo buildable with `cargo test --workspace` green.

---

### Code Quality

**No `unsafe`.** `#![forbid(unsafe_code)]` preserved in `src/lib.rs:151`. No new `TODO` / `FIXME` / `unimplemented!()` / `todo!()` introduced.

**Conn struct shape is correct** — `src/conn.rs:88` has exactly `{ f: fn(A) -> B, g: fn(B) -> A, _k: PhantomData<fn() -> K> }`, matching Plan 29B T1.

**Kind machinery is clean.** Sealed `Kind` trait with `L` / `R` markers in a private `mod kind`; only the public re-exports leak (`pub use kind::{Kind, L, R};`). No back-door for downstream impls.

**One-sided const kind annotations are consistent.** All 10 single-sided shipped consts (`TIMENANO`, `TIMESECS`, `DATEJDAY`, `OFDTNANO`, `OFDTSECS`, `PDTMDATE`, `IPVXIPV4`, `SOVXSOV4` ascribed `ConnL`; `IPVXIPV6`, `SOVXSOV6` ascribed `ConnR`) match the kind their constructors imply.

**Naming of marker private fns (`_ceil` / `_inner` / `_floor`).** The leading underscore is necessary — without it the inherent associated fn would shadow the trait's default method (caught during Sprint B; see commit body). Worth a one-line comment in the `fix_fix_*!` and `triple!` macro definitions explaining why; right now a future reader could mistake them for "private detail" rather than "deliberate name to avoid collision."

**The 5 remaining `ignore` doctest blocks all check out:**
- `src/conn.rs:567,592` — `compose!` and `triple!` declaration-form macros (need module scope).
- `src/lib.rs:49` — qualified-import demo (`fi8` and `fi64` aliases).
- `src/prop.rs:38, src/prop/lattice.rs:8` — `testing`-feature gated proptest examples.
- `README.md:384` — f16-feature example (gated on nightly).

---

### Test Coverage

**Property tests survive the migration.** 35 callsites of `galois_l` / `galois_r`, 12 of `floor_le_ceil`, 6 of `ulp_bound`. Per-primitive coverage is split:

- Signed widths (`fixed/i8`–`i128`): inline `props_for_pair!` macros — i8 has 22 invocations (full ladder), i16/i32/i64/i128 have 15-16 each. Total: 85 `props_for_pair!` × ~9 properties = ~760 generated proptests.
- Unsigned widths (`fixed/u8`–`u128`): integration tests in `tests/fixed_u{8,16,32,64,128}_galois.rs`. 5 files × ~9 properties × per-rung pairs.

**Compile-fail fixtures: 2 of 4 are broken in a way that defeats their purpose.** This is the must-fix finding.

`tests/compile_fail/floor_on_l_conn.rs` and `tests/compile_fail/ceiling_on_r_conn.rs` import `floor` / `ceiling` as **free functions from `connections::conn`**:

```rust
use connections::conn::{Conn, ConnL, floor};   // floor_on_l_conn.rs:4
```

But the 2-fn migration removed the free-fn `floor` / `ceiling` — they're inherent methods on `Conn<_, _, L>` / `Conn<_, _, R>` now. The `.stderr` snapshots confirm:

```
error[E0432]: unresolved import `connections::conn::floor`
  --> tests/compile_fail/floor_on_l_conn.rs:4:38
```

The fixture passes, but the test no longer exercises kind discipline — it exercises "this name moved." A future regression that *re-introduces* kind-violating dispatch wouldn't trip the fixture, since the import line fails first. This silently negates 2 of the 4 advertised guard rails.

**Fix:** rewrite the fixtures to call the kind-violating method directly:

```rust
// floor_on_l_conn.rs (proposed):
use connections::conn::{Conn, ConnL};
const L_CONN: ConnL<i32, i32> = Conn::new_l(|x| x, |x| x);
fn main() {
    let _ = L_CONN.floor(0_i32);  // L-Conn has no method named `floor`
}
```

The `.stderr` snapshot will pin "no method named `floor` found for struct `Conn<i32, i32, L>`", which is the actual structural discipline. Same shape for `ceiling_on_r_conn.rs`.

The `galois_l_on_r_conn.rs` / `galois_r_on_l_conn.rs` fixtures are **correct** — `galois_l` is still a free fn in `prop::conn`, and the `.stderr` pins the genuine kind-mismatch error.

**Doctests:** 36 passing, 5 ignored. Restoration coverage looks complete; the 5 ignores are categorically legitimate (see Code Quality).

---

### Plan Conformance

Plan 29B's tasks all landed:

| Task | Status | Evidence |
|------|--------|----------|
| T1: 2-fn Conn struct | ✓ | `src/conn.rs:88` matches spec |
| T2: ViewL / ViewR / Triple | ✓ | `src/conn.rs:316,352,373`. Default-method `.ceil/.inner/.floor` on the base traits is a Sprint B late-add (folded from the prior `ViewLExt`/`ViewRExt` Ext-traits) — clean simplification |
| T3: Two-sided ops on Triple | ✓ | All 9 free fns at `src/conn.rs:382–504` bound on `T: Triple<A, B>` |
| T4: compose macros | ✓ | `compose_l!`, `compose_r!`, `compose!` declaration-form, `triple!` declaration-form |
| T5: macro generators emit markers | ✓ | `pub struct $NAME` in `ext_int!`, `nz_int_ext!`, `nz_uint_ext!` (ViewL only), `fix_fix_*!` |
| T6: iso consts → markers | ✓ | 10 `Q000IXX` / `Q000UXX` + `U032IPV4` / `U128IPV6` |
| T7: standalone triples → markers | ✓ | 13 markers including F064F032, F064F016, F032F016, IPV6IPV4, DURNSECS, F064DURN, F032DURN, F064STDR, F032STDR, STDRU064, STDRU128 |
| T8: trybuild compile-fail | partial | 2 of 4 fixtures broken (see Test Coverage) |

**Justified out-of-plan changes:**
- `.ceil` / `.inner` / `.floor` back-compat aliases on `Conn<_, _, L>` / `Conn<_, _, R>` and on `ViewL` / `ViewR` traits (default methods). Reduces test churn substantially. Reasonable.
- `_ceil` / `_inner` / `_floor` private associated fns on triple markers (vs free fns) to avoid shadowing the trait default methods. Pragmatic.
- Prefix strip (`conn_` and `triple_` from predicate names) — applied uniformly across `src/`, `tests/`, and `tests/compile_fail/*.stderr`. Test imports halved.

**Test deletions (3 total) are all coherent with the new contract:**
- `src/fixed/i8.rs::tests::u_to_i_ceil_eq_floor` — was checking `U008I008.ceil(a) == U008I008.floor(a)` for an R-Conn that structurally satisfies it. Under kind discipline, R-Conns don't have a `.ceil()` method; the property is unrepresentable, not just untestable.
- `src/lattice.rs::tests::lattbool_ordering_galois_r` and `lattbool_ordering_floor_le_ceil` — `LATTBOOL` returns `ConnL` only after the redesign (no R-view), so R-side and Triple-bound predicates can't accept it. The L-side battery (`galois_l`, `closure_l`, `kernel_l`, `monotone_l`, `idempotent`) is preserved.

---

### Risks

**The compile-fail fixture issue (above) is the only correctness risk.** Because the fixtures still report "ok" in CI, the kind-discipline regression they're supposed to catch wouldn't surface until property tests fail at runtime — exactly the failure mode this MR is trying to prevent.

**Migration completeness:** spot-checked all 10 per-primitive `fixed/{i,u}{8..128}.rs` modules — every Q-format ladder, ext_int!, nz_int_ext!/nz_uint_ext!, and iso const migrated. The `props_for_pair!` macro in each signed `fixed/iN.rs` test mod uses `&$conn::L` / `&$conn::R` for kind-bound predicates and bare `&$conn` for triple-bound predicates, which is correct under the new shape.

**New dependency:** `trybuild = "1"` added as dev-dep. Justified — the only realistic way to test compile-fail discipline. Stable, widely used (>500M downloads). Worth keeping.

**No security surface changed.** This crate has no I/O boundary; no shell-outs, no path handling, no input parsing.

---

### Recommendations

**Must fix before push:**

1. **Rewrite `tests/compile_fail/floor_on_l_conn.rs` and `tests/compile_fail/ceiling_on_r_conn.rs`** to call the kind-violating *method* directly, then re-bless the `.stderr` snapshots. Current state is a silent regression: the fixtures pass, but they pin import errors instead of the kind-discipline error they advertise.

**Follow-up (future work):**

1. **Add a one-line comment in the `fix_fix_*!` and `triple!` macro definitions** explaining the underscore prefix on `_ceil`/`_inner`/`_floor` (avoids shadowing the trait default methods on the marker). Cuts surprise for the next reader.
2. **Restore the f16 README doctest** when the `f16` feature stabilizes (currently the only legitimately-ignored README block tied to upstream Rust).
3. **Sprint A's intermediate state was discarded by the squash** — if there's value in showing the staged design (3-fn struct + T-kind via ImpliesL/ImpliesR/Meet) for future cross-references, an archived plan note in `doc/plans/plan-2026-04-29-02.md` already covers it. Acceptable as-is.
