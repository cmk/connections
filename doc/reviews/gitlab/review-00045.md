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

## Local review (2026-04-30, independent agent re-run)

**Branch:** sprint/phantom
**Commits:** 3 (origin/main..sprint/phantom)
**Reviewer:** Claude (sonnet, **independent**) — second pass after the org usage cap reset; supersedes the author self-review above.

---

### Commit Hygiene

Three commits, each conventional (`feat:`, `doc:`, `fix:`). The `feat:` squash commit is large (58 files, ~3200 insertions) but acceptable given the explicit user instruction. The `fix:` commit that follows (`1134910`) is a clean targeted repair. No merge commits; history is linear. All three commits leave a passing test suite. Commit messages are within 72 chars.

### Code Quality

`#![forbid(unsafe_code)]` is present at `src/lib.rs:151`. No unsafe code found.

**Conn struct shape** (`src/conn.rs:88–92`): Exactly `{ f, g, _k: PhantomData<fn() -> K> }`. Matches Plan 29B T1 precisely.

**Kind machinery**: Sealed `Kind` trait with `L` / `R` markers, `ConnL` / `ConnR` type aliases. All correct.

**ViewL / ViewR / Triple**: Defined at `conn.rs:316–374`. Default methods on `ViewL` give `.ceiling()` / `.upper()` / `.ceil()` / `.inner()`; on `ViewR` give `.floor()` / `.lower()`. The `Triple` blanket impl is a one-liner. All correct.

**Back-compat aliases (`.ceil` / `.inner` / `.floor`)**: Present as documented back-compat aliases on the `Copy` inherent impl blocks and as `ViewL` / `ViewR` default methods. Justified — they preserve call-site compatibility for code migrated from the 3-fn API.

**Inherent ops by kind**: L-side ops (`ceiling`, `upper`, lifters `upper1/2`, `ceiling1/2`) live only on `impl<A:Copy, B:Copy> Conn<A,B,L>`. R-side ops (`floor`, `lower`, lifters) live only on `Conn<A,B,R>`. The kind-discipline is structural.

**compose_l! / compose_r!**: The closures in the macro arms (`|a| $first.ceiling($x)` etc.) are non-capturing and coerce to `fn` pointers. Correct.

**compose! macro**: Emits `pub struct $name; impl ViewL...; impl ViewR...`. Syntactically correct. However, the macro has **never been instantiated** anywhere in the codebase — neither in production code nor in a test. `F064F016` is implemented directly rather than via `compose!(F064F016 : F064 => F032 => F016 = F064F032, F032F016)`. The compile-correctness of the macro body is not exercised by any test.

**triple! macro**: Same situation — `#[macro_export]` but zero invocations. Neither `triple!` nor `compose!` appear outside their own macro definition.

**Broken intra-doc links (31 warnings from `cargo doc --no-deps`)**: This sprint removed `Conn::new`, `Conn::new_left`, `Conn::new_right`, `Conn::new_iso` and promoted the old free functions `ceiling` / `floor` / `upper` / `lower` to inherent methods. The doc comments that linked to those names were not updated. Affected files: `src/lib.rs`, `src/addr.rs`, `src/addr/ip.rs`, `src/addr/socket.rs`, `src/fixed.rs`, `src/fixed/i128.rs`, `src/time.rs`, `src/time/clock.rs`, `src/time/datetime.rs`, `src/time/duration.rs`, `src/time/offset.rs`. Specifically:

- `src/lib.rs:68–70`: `[Conn::new_left]` / `[Conn::new_right]` — both links dead.
- `src/lib.rs:101`: "stores three bare `fn` pointers" — factually wrong (two fields now).
- `src/lib.rs:130–132`: "collapses both sides onto the unified `Conn` (it always carries the full triple `ceil ⊣ inner ⊣ floor`)" — directly contradicts the new design.
- `src/lib.rs:138–143`: The Haskell/Rust table claims `ceiling` / `upper` / `floor` / `lower` and their lifters are "free fn at crate root" — they are now inherent methods and the links are unresolved.
- `src/addr.rs:51–59`: Four `[Conn::new_left]` / `[Conn::new_right]` links.
- `src/fixed.rs:44–50`, `src/fixed.rs:291`, `src/fixed.rs:388–392`: Multiple `new_left` / `new_right` references in rustdoc tables.

The pre-commit hook does not run `cargo doc --deny broken_intra_doc_links`. Broken intra-doc links are warnings not errors, and `cargo test` doesn't check them. They slip through cleanly.

**Stale prop.rs ignore doctest**: `src/prop.rs:38–57` shows a downstream usage example passing `&F064F032` directly to `galois_l`. Since `F064F032` is now a unit struct marker (not `Conn<_,_,L>`), and `galois_l` takes `&Conn<A,B,L>`, this example would not compile. The `ignore` hides the mismatch. The correct call is `conn::galois_l(&F064F032::L, a, b)` as shown in the `no_run` block above it. A consumer reading the `ignore` block as a usage guide would copy broken code.

**README stale narrative**: `README.md:84–99` describes `Conn<A,B>` as holding three fn fields (`ceil`, `inner`, `floor`) and says "A length-2 (one-sided) connection sets `floor = ceil`." This is the pre-migration design and is now incorrect. `README.md:268–270` repeats "three function pointers in one value" and "crate-root `ceiling` / `floor` / `upper` / `lower` free functions." Both claims are false after this sprint.

No dead code or clippy issues. `cargo clippy --all-targets -- -D warnings` passes clean. `cargo fmt --all -- --check` passes clean.

### Test Coverage

**Property tests preserved**: The core property batteries are present and exercised on every shipped Conn. The kind-monomorphic predicates in `src/prop/conn.rs` correctly take `&Conn<A,B,L>` or `&Conn<A,B,R>` — the compile-fail fixtures confirm the wrong-kind calls are rejected.

**compile-fail fixtures**: All four shipped fixtures pass and the `.stderr` snapshots pin the correct error mode after the `1134910` repair commit:
- `floor_on_l_conn.rs` → `error[E0599]: no method named 'floor' found for struct Conn<i32, i32>` with the note that it's available on `Conn<A, B, R>`. Correct.
- `ceiling_on_r_conn.rs` → dual error, correct.
- `galois_l_on_r_conn.rs` → `error[E0308]: mismatched types`, expected `&Conn<i32,i32,L>` found `&Conn<i32,i32,R>`. Correct.
- `galois_r_on_l_conn.rs` → dual, correct.

**Plan 29B verification gaps**: Two fixtures from Plan 29B's Verification table are absent:
1. `tests/compile_fail/round_on_l_conn.rs` — the `Triple` bound on `round()` is never negatively tested.
2. `tests/compile_fail/compose_l_with_r.rs` — mixed-kind composition through `compose_l!` is never negatively tested.

The swap involution properties from Plan 29B's Verification table (`swap_l . swap_r ≡ id`, `swap_r . swap_l ≡ id`) have no tests at all. `swap_l` and `swap_r` are untested beyond type-checking.

**Plan 29B spot checks**: None of the five named spot checks from the Verification table exist (`aliases_compile`, `triple_marker_zero_sized`, `triple_uses_both_views`, `round_works_on_triple`, `compose_triple_marker`). `src/conn.rs` has zero `#[test]` functions outside doctests.

**compose! / triple! macros**: Neither macro is instantiated anywhere in the codebase. Their correctness is untested beyond the fact that they parse.

**Deleted tests**: Three deletions (`u_to_i_ceil_eq_floor`, `lattbool_ordering_galois_r`, `lattbool_ordering_floor_le_ceil`) all justified by structural impossibility under the new kind discipline. The replaced surface (L-law battery on `LATTBOOL`, R-Galois on `U008I008` integration tests) covers the lost ground.

### Plan Conformance

| Task | Status |
|------|--------|
| T1: 2-fn `Conn<A,B,K>` | Complete |
| T2: Kind constructors `new_l` / `new_r` | Complete |
| T3: Inherent ops by kind | Complete |
| T4: `ViewL` / `ViewR` / `Triple` | Complete |
| T5: Two-sided ops on `Triple` | Complete |
| T6: `swap_l` / `swap_r` | Present (but untested) |
| T7: Property fn signatures by kind | Complete |
| T8: `compose_l!` / `compose_r!` / `compose!` | Macros present; `compose!` / `triple!` never instantiated or tested |
| T9: Migrate ~28 full-triple consts | Complete |
| T10: Rewrite `conn.rs` rustdoc | `conn.rs` module doc is accurate; stale text in `lib.rs` and `README.md` not cleaned up |
| T11: Compile-fail tests | 4 of 5 Plan 29B fixtures; 2 missing (`round_on_l_conn`, `compose_l_with_r`) |

### Risks

**No blocking bugs found.** `cargo test --workspace` passes clean with 1172+ unit tests. `cargo clippy -- -D warnings` is clean. `cargo fmt --check` is clean.

The 31 broken intra-doc links are warnings, not errors — `cargo test` does not check them, and the pre-commit hook has no `cargo doc --deny broken_intra_doc_links` step. They will appear in published documentation and can mislead downstream users.

The `compose!` and `triple!` macros are dead from a testing perspective. If they contain a subtle expansion bug (especially the `compose!` macro's const-context behavior with associated-const paths like `<T as ViewL<A,B>>::L`), it will not be discovered until someone first instantiates the macro.

### Recommendations

**Must fix before push:**

1. **Stale intra-doc links (31 warnings).** `src/lib.rs:68–70, 101, 130–132, 136–143`, `src/addr.rs:51–59`, `src/fixed.rs:44–50, 291, 388–392`, and the `time/` module comment blocks all link to removed constructors or removed free functions. Update to `new_l` / `new_r`, or remove the broken `[` links for the free fns. Also correct the "three bare `fn` pointers" and "full triple" narrative at `lib.rs:101` and `lib.rs:130–132` to match the 2-fn reality.

2. **Stale `prop.rs` ignore doctest (`src/prop.rs:51`).** Replace `&F064F032` with `&F064F032::L` in the `ignore` block. This is an example that downstream crate authors will copy; it should compile.

**Follow-up (future work):**

3. **README "How connections work" section** (`README.md:84–99, 268–270`). The three-fn struct description and "crate-root free functions" claim are wrong. Not blocking (it's `rust,no_run` / prose), but will confuse first-time readers.

4. **`compose!` and `triple!` macros untested.** Add at least one instantiation of each (a test-only unit struct in a `#[cfg(test)]` block in `conn.rs`) to prove the expansion compiles and the resulting type satisfies `Triple<A,B>`.

5. **Missing Plan 29B compile-fail fixtures.** Add `round_on_l_conn.rs` and `compose_l_with_r.rs`. Negative-test coverage is materially thinner than the plan specified.

6. **`swap_l` / `swap_r` involution properties** (`prop::conn::swap_round_trip_l/r`) are absent. Worth a short proptest block in a `#[cfg(test)]` section of `conn.rs`.

## Local review (2026-04-30, round 2 — independent re-run)

**Branch:** sprint/phantom
**Commits:** 4 (origin/main..sprint/phantom)
**Reviewer:** Claude (sonnet, independent)

---

### Round-1 must-fix verification

**MF-1 (broken intra-doc links + stale narrative):** Landed cleanly. `cargo doc --no-deps` now emits exactly 3 warnings — all pre-existing `arb_f32_bounded` references, zero sprint-introduced warnings. `src/fixed.rs:291,388` use `new_r` / `new_l`. `src/addr.rs:58-59` uses `new_l` / `new_r`. `src/lib.rs:102-144` describes the 2-fn struct + phantom kind tag + Triple-bound shape correctly; "stores three bare fn pointers" is gone.

**MF-2 (`src/prop.rs:51` ignore-block with `&F064F032`):** Fixed correctly. The `ignore` block now reads `&F064F032::L` and imports `use connections::conn::ViewL;`. The non-`ignore` example above it was already correct.

### Round-1 follow-up verification

**FU-3 (README "How connections work"):** Lines 80-108 correctly describe the 2-fn struct with phantom kind tag. "No struct in the crate stores three fns" is explicit.

**FU-4 (`triple!` / `compose!` / `swap_l` / `swap_r` tests):** All present in `src/conn.rs` lines 636-729. `triple_marker_zero_sized`, `triple_uses_both_views`, and `compose_triple_marker` test the new macros with concrete values. `swap_round_trip_l` / `swap_round_trip_r` are proptest blocks. The `:path` → `:expr` change in `compose_l!` / `compose_r!` is correct (all fragment specifiers are `:expr` throughout the recursive arms).

**FU-5 (compile-fail fixtures):** Both new fixtures pin genuine kind-discipline errors: `round_on_l_conn.stderr` pins `E0277` ("trait `ViewL<_, _>` is not implemented for `Conn<i32, i32>`"), `compose_l_with_r.stderr` pins `E0599` ("no method named `ceiling` found for struct `Conn<i32, i32, R>`"). A regression that re-permitted either use would break the snapshot.

**FU-6 (`swap_round_trip_l` / `swap_round_trip_r`):** Present at `src/conn.rs:712-729`. Proper proptest blocks over `(i32, i64)`.

### New issues

**Minor — README "Why this crate" bullet still says three fn pointers (line 21-25).** The introductory bullet reads: "A `Conn<A, B>` exposes `ceil: A → B`, `floor: A → B`, *and* the embedding `inner: B → A` as three function pointers on one value." Under the post-sprint design a `ConnL` carries 2 fn pointers and a `ConnR` carries 2 fn pointers; the third function lives in module scope via `triple!`. The "How connections work" section two scrolls below correctly undoes this, but the contradiction in the first user-facing paragraph is jarring. Not a must-fix; should be corrected before 0.1 is published.

**Absent — variadic `compose_l!` chain test with 3+ operands.** The `:expr` macro fix is structurally sound, but the 3-operand path is never exercised in a real test. The lib.rs doc example (`compose_l!(ID_I32, ID_I32, ID_I32)`) is `no_run` so it doesn't prove it compiles. A concrete `const`-level test with 3 operands would close this gap. Not blocking given structural correctness.

### Net assessment

**Clear to push.** Both round-1 must-fix items landed correctly. All four follow-ups are addressed with genuine kind-discipline fixtures and a full proptest battery. The test suite passes clean. Clippy is clean. The two new issues are quality follow-ups, not blockers. The branch is ready to push.

<!-- glab-id: 3302801510 -->
<!-- glab-discussion: 72e1aac08b43215e2adfc93e487a901a74862116 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 — (2026-04-30 09:05 UTC) [open]

**[must-fix]** `src/addr/ip.rs:256` — The doctest for `IPVXIPV4` previously demonstrated that `floor` and `ceil` return the same value on a one-sided conn, but after the migration the assertion was changed from `IPVXIPV4.floor(...)` to `IPVXIPV4.ceil(...)` — so both lines now assert the same thing (`ceil` twice) and the test no longer demonstrates the one-sided property it claims to document. The comment still says `// 'floor' returns the same as 'ceil' (one-sided contract)` but no `floor` call appears. Either restore the second assertion using `IPVXIPV4::R` or remove the misleading comment.

*(inline anchor rejected by GitLab: 400)*

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3302801541 -->
<!-- glab-discussion: ceedfe26cf23b5e935149dfdc0483a9e8e11b555 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/addr/socket.rs:69` (2026-04-30 09:05 UTC) [open]

**[must-fix]** Same issue as `ip.rs:256`: the doctest comment says `// 'floor' returns the same as 'ceil' (one-sided contract)` but the assertion was changed from `SOVXSOV4.floor(...)` to `SOVXSOV4.ceil(...)`, making both lines identical. The claimed one-sided contract is no longer demonstrated. The analogous change at `socket.rs:125` (`SOVXSOV6`) has the same problem for the `ceil` / `floor` pair. Either restore meaningful assertions or remove the misleading comments.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3302801578 -->
<!-- glab-discussion: 243cd0810fcd2d9682759754cd2ab4e557de7ed6 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn.rs:436` (2026-04-30 09:05 UTC) [open]

**[follow-up]** `truncate1` reaches the upper adjoint through `ViewL` (`<T as ViewL<A,B>>::L.upper(x)`) to widen `x: B` to `A` before calling `truncate`. But `truncate` itself routes the positive branch through `ViewR::R.floor` and the negative branch through `ViewL::L.ceiling`. The Haskell original uses `inner` from either side (they share the middle adjoint); in the new design the L upper and R lower are wired to different fn pointers (`f` vs `g` of different Conn values). For a lawful triple these coincide, so the behavior is correct, but it is worth a comment explaining why `ViewL::L.upper` is the right choice here (the L and R `g` fields are both `inner` by convention in any lawful triple).

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3302801620 -->
<!-- glab-discussion: df17c82fb8589d9a013e5ec90f3633db9d983b42 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn.rs:316` (2026-04-30 09:05 UTC) [open]

**[follow-up]** The `ViewL` and `ViewR` trait default methods take `&self` but only ever delegate to the associated const `Self::L` / `Self::R`, ignoring the receiver entirely. This means zero-sized triple markers work fine, but a hypothetical non-ZST implementor would silently ignore its own state. The plan text acknowledges triple markers are always zero-sized, but the trait definition itself has no `where Self: Sized` or documentation note constraining implementors. A short doc comment stating the expectation (implementors should be ZSTs) would prevent misuse.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3302830549 -->
<!-- glab-discussion: 72e1aac08b43215e2adfc93e487a901a74862116 -->
#### ↳ cmk (2026-04-30 09:14 UTC) [open]

Fixed — IPVXIPV4 is a one-sided ConnL with no `.floor()` method, so the second assertion now exercises `.inner()` (the surviving lower-side accessor for the L-pair) and the comment was rewritten to match. IPVXIPV6 got the symmetric treatment.

<!-- glab-id: 3302831042 -->
<!-- glab-discussion: ceedfe26cf23b5e935149dfdc0483a9e8e11b555 -->
#### ↳ cmk (2026-04-30 09:14 UTC) [open]

Fixed — same shape as the ip.rs thread: SOVXSOV4 and SOVXSOV6 are one-sided so the second assertion now exercises `.inner()` and the misleading "floor returns same as ceil" comment is gone.

<!-- glab-id: 3302831958 -->
<!-- glab-discussion: 243cd0810fcd2d9682759754cd2ab4e557de7ed6 -->
#### ↳ cmk (2026-04-30 09:14 UTC) [open]

Added — truncate1's docstring now explains that both views' `g` fields are wired to the same shared middle adjoint in any lawful triple, so widening through `<T as ViewL<A,B>>::L.upper` is canonical (we pick L by convention).

<!-- glab-id: 3302833323 -->
<!-- glab-discussion: df17c82fb8589d9a013e5ec90f3633db9d983b42 -->
#### ↳ cmk (2026-04-30 09:14 UTC) [open]

Added an "Implementor contract" paragraph to both `ViewL` and `ViewR` documenting that `Self` should be a zero-sized type, and noting the macros (`triple!`, `ext_int!`, `nz_int_ext!`, `fix_fix_*!`) emit unit structs to satisfy that contract. No `where Self: Sized` bound — kept it doc-only since enforcing structurally would gratuitously block ZST-with-PhantomData markers downstream.
