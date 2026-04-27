# MR !16 — Port `Cast.hs` accessors and lifters (Sprint A)

## Summary

- Add `conn::cast` — 14 free functions porting the L-side
  (`upper`/`upper1`/`upper2`/`ceiling`/`ceiling1`/`ceiling2`/`maximize`)
  and R-side (`lower`/`lower1`/`lower2`/`floor`/`floor1`/`floor2`/
  `minimize`) accessor + lifter API from Haskell `Data.Connection.Cast`.
  Both naming conventions live as free functions on the unified
  `Conn<A, B>` (which always carries the full triple `ceil ⊣ inner ⊣
  floor`); the Haskell `Side` data kind is deliberately not ported.
- Re-export the Cast API at the crate root so callers write
  `connections::ceiling(&c, x)` rather than reaching into
  `connections::conn::cast::ceiling`.
- Add 8 new `cast_*` law predicates to `property::laws`
  (`cast_upper1_id_unit`, `cast_lower1_id_counit`,
  `cast_ceiling1_id_kernel`, `cast_floor1_id_kernel`, plus
  `cast_*2_id_diag` for the binary lifters), each routed through the
  lifter under test. 38 new proptest blocks (8 predicates × 3 conn
  bases — `Conn::<i32, i32>::identity()`, `Conn::<f64, f64>::identity()`,
  and the non-trivial triple `FD12FD09`) plus deterministic spot checks.
  Total: 1298 lib tests (up from 1260) + 11 doctests.
- Rewrite `README.md` as a Rust-native landing page (Rust-native
  motivations: gaps in `as`/`From`, round-trip law guarantees, ladder
  ergonomics; quick tour with five examples; status table; relationship
  to the upstream Haskell library). The README is wired into `lib.rs`
  via `#![doc = include_str!]` so `cargo test --doc` compile-checks
  every example.
- Append a `doc/design.md` section "Cast: L/R as a naming axis, not a
  type axis" documenting why no `CastR` constructor was added (the
  Haskell library has 122 L-only concrete connections vs **0** R-only,
  so the unified `Conn` already covers every use case without a
  type-level split).

## Test plan

- [ ] `cargo test --workspace` — 1298 tests pass (up from 1260; 38
      new proptest blocks).
- [ ] `cargo test --doc` — 11 doctests pass (up from 5; README rust
      blocks are now compile-checked).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — clean (one pre-existing warning on
      `src/property/mod.rs:8` about `[arb]` link gating; not
      introduced by this MR).
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke:
      `connections::ceiling(&FD12FD09, FD12(1_500))` returns
      `FD12FD09.ceil(FD12(1_500))`; `connections::maximize(&ord_pair,
      3, 5)` returns `5` for the obvious `Conn<(i32, i32), i32>`
      built from `(max, diag, min)`.

## Local review (2026-04-26)

**Branch:** sprint/cast-accessors
**Commits:** 3 (origin/main..sprint/cast-accessors)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Three commits: `doc:` (design.md section), `feat:` (all new code), `doc:`
(plan + review docs). Conventional prefixes, subjects 58–66 chars, each
buildable in isolation. The ordering — design justification before code —
follows the established sprint pattern. No merge commits.

### Code Quality

`#![forbid(unsafe_code)]` preserved at `src/lib.rs:126`.

All 14 free functions take `&Conn<A, B>` first, matching the
`property::laws::conn_*` precedent. Bodies are correct one-liners:
`upper`/`lower` both return `c.inner(b)` as specified; `upper1` calls
`c.inner(f(c.ceil(a)))` and `lower1` calls `c.inner(f(c.floor(a)))` — the
L/R distinction is preserved in which field is used for the round-trip.

`FnOnce` bounds on the lifter closures are correct. Each closure is
consumed exactly once per call; `FnOnce` is the minimal sufficient bound
and strictly more general than `Fn`. The plan said `impl Fn(...)` but
`FnOnce` is correct. No issue.

The `#![doc = include_str!("../README.md")]` + subsequent `//!` blocks in
`lib.rs` concatenate as intended: README content renders first, then
`---`, then the existing internal module docs. Correct ordering, no
shadowing.

Inline doctests in `cast.rs` for `upper` and `ceiling` use the module
path directly, not the crate-root re-export — correct for module-local
doctests. The README blocks are all `rust,no_run`; they are compile-
checked by `cargo test --doc` (which is what the review doc's "11
doctests" count reflects) but not run. Compile-checking is sufficient
to catch import resolution bugs.

### Test Coverage

**Critical: `maximize`/`minimize` laws are inline assertions, not
`laws::` predicates.**

`src/conn/cast.rs`, the `maximize_is_max` / `minimize_is_min` proptest
blocks:

```rust
fn maximize_is_max(a: i32, b: i32) {
    let c = ordered_pair();
    prop_assert_eq!(maximize(&c, a, b), a.max(b));
}

fn minimize_is_min(a: i32, b: i32) {
    let c = ordered_pair();
    prop_assert_eq!(minimize(&c, a, b), a.min(b));
}
```

CLAUDE.md states: "Predicates that test laws should be defined as
`bool`-returning fns in `property::laws::*`, not inline in
`prop_assert!` blocks." Plan T3 explicitly listed
`cast_maximize_eq_ceiling(c, a, b)` and `cast_minimize_eq_floor(c, a, b)`
as named law predicates to be added to `src/property/laws.rs`. Neither
appears in the laws.rs diff. The two proptest blocks substitute a
different assertion (`a.max(b)` rather than `ceiling(c, (a, b))`) and
place it inline.

Consequence: the specified predicates are absent from `property::laws`,
making them unavailable to downstream crates that import `property::laws`
to test their own connections. The inline form also diverges from every
other proptest block in the file, which all call `laws::cast_*`.

Fix: add `cast_maximize_eq_ceiling` and `cast_minimize_eq_floor` to
`src/property/laws.rs` returning `bool`, and route the proptest blocks
through them.

---

The eight `laws::cast_*` predicates that were added all return `bool` and
take `&Conn<A,B>` first. The `*_diag` predicates use `ple`-based
equivalence (`l.ple(&r) && r.ple(&l)`) rather than `==`, which is correct
for N5-ordered types.

Generator choice for FD12FD09 blocks is correct: `fixed_safe_fine`
(source-side, prevents inner-round-trip overflow) for properties that
pass through `inner(ceil(a))` or `inner(floor(a))`; `fixed_coarse`
(target-side) for `ceiling1`/`floor1` properties that start at `B`.
NaN/±∞ coverage present via `arb_f64` in the ID_F64 blocks.

### Plan Conformance

- **T1** (rename `conn.rs` → `conn/mod.rs`): Done — 99% similarity
  rename, `pub mod cast;` added.
- **T2** (14 free functions in `cast.rs`): All 14 present, signatures
  and bodies match the table.
- **T3** (8 `cast_*` predicates in `laws.rs`): 8 of the 10 specified
  predicates are present. `cast_maximize_eq_ceiling` and
  `cast_minimize_eq_floor` are absent — see Critical finding above.
- **T4** (proptest suite): 26 proptest blocks total (8 predicates × 3
  bases + 2 inline maximize/minimize). The 2 inline blocks should be
  laws-routed per T3/CLAUDE.md.
- **T5** (re-export from `lib.rs`): All 14 names re-exported at crate
  root.
- **T6** (plan + review docs): Both present with required sections.
- **T7** (README rewrite): Comprehensive, Rust-native, all 9 plan
  sections present, ~256 lines (slightly over the 150–250 target but
  acceptable). CI badge retained.

### Risks

The README `rust,no_run` blocks reference `connections::ceiling`,
`connections::upper1`, `connections::maximize`, `connections::conn::Conn`
— all resolve via the `pub use conn::cast::{...}` block in `lib.rs`. No
broken references.

No new runtime or dev dependencies introduced. `.gitignore`,
`.claude/settings.json`, and pre-commit hook config are untouched.

The `_ple_referenced` helper at the end of the test module
(`#[allow(dead_code)] fn _ple_referenced<T: Ple>(_t: &T) {}`) is a
workaround to anchor the `use crate::lattice::Ple` import. The trait is
not referenced directly in the test module (all `Ple` usage routes
through `laws::*`). Removing the import + the dummy function together
is the clean fix; the current approach compiles but is unusual.

### Recommendations

**Must fix before push:**

1. **`src/conn/cast.rs` — `maximize_is_max` / `minimize_is_min` inline
   assertions.** Add `cast_maximize_eq_ceiling` and
   `cast_minimize_eq_floor` as `bool`-returning predicates to
   `src/property/laws.rs`, and route the two proptest blocks through
   them. CLAUDE.md's law-predicate convention and plan T3's Verification
   table both require this.

**Follow-up (future work):**

2. **`src/conn/cast.rs` tests — `Ple` import anchor**: Remove
   `use crate::lattice::Ple;` and the `_ple_referenced` dead-code
   workaround. The trait is not referenced directly in the test module.

3. **README code blocks**: T7 plan specified `cargo test --doc`-runnable
   blocks (bare ` ```rust `). All five Quick Tour blocks are
   `rust,no_run`. They are compile-checked but not executed. Future
   sprint could make the self-contained examples runnable.

## Round-1 fixes (2026-04-26)

All three review recommendations addressed in one `fix:` commit:

1. **Must-fix (rec #1) — laws-routing for `maximize`/`minimize`.** Added
   `laws::cast_maximize_eq_ceiling` and `laws::cast_minimize_eq_floor`
   to `src/property/laws.rs`, both `bool`-returning predicates that
   compare the curried form to the pair form via N5 ple-equivalence.
   Renamed the two inline proptest blocks to
   `maximize_eq_ceiling_random` and `minimize_eq_floor_random` (to
   avoid collision with the deterministic `maximize_eq_ceiling_pair` /
   `minimize_eq_floor_pair` spot checks that were already present),
   and routed both through the new predicates. CLAUDE.md's
   "predicates over inline `prop_assert!`" rule is now uniformly
   followed in `cast.rs::tests`.

2. **Follow-up (rec #2) — `Ple` import anchor.** Removed
   `use crate::lattice::Ple;` and the
   `#[allow(dead_code)] fn _ple_referenced<T: Ple>(_t: &T)` workaround
   from the test module. The trait was not used directly; all `Ple`
   usage routes through `laws::*`.

3. **Follow-up (rec #3) — README code blocks runnable.** Changed all
   five Quick Tour blocks from `rust,no_run` to plain `rust` so
   `cargo test --doc` now executes the assertions (not just compile-
   checks them). Doctest count unchanged at 11 passing (the same
   blocks now both compile *and* run). Fixed the `U008I016` example
   along the way: the original asserted `ceil(PosInf) == i16::MAX`,
   which is wrong — `ceil(PosInf)` returns the synthetic "one past
   source max" point (`u8::MAX + 1 = 256`), and `i16::MAX` is what
   `floor(PosInf)` returns. The example now demonstrates both
   behaviors explicitly.

Test counts after fix: **1298 lib tests + 11 doctests, all passing.**
Clippy clean. Cargo doc clean modulo the pre-existing `[arb]` link
warning on `src/property/mod.rs:8`.

<!-- glab-id: 3288059588 -->
<!-- glab-discussion: c3a41e70b74c8cb0d559d79f55f5d07b78eddbac -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/property/laws.rs:497` (2026-04-27 03:39 UTC) [open]

**[must-fix]** The doc comment on `cast_upper2_id_diag` states the diagonal law holds with projection `|p, _| p`, but the predicate uses `upper2(c, |p, _q| p, a, a)` and compares it to `upper1(c, |x| x, a)`. `upper2(c, |p, _| p, a, a)` expands to `inner(f(ceil(a), ceil(a)))` where `f` discards the second argument and returns the first, which equals `inner(ceil(a))` — the same as `upper1(c, id, a)`. The law holds here, but the claimed diagonal collapse is specific to idempotent-style projections; the predicate name and doc should clarify it tests the `|p, _| p` projection specifically, not the general diagonal `|p, q| p` (where `p ≠ q` could produce a different result). As stated in the plan (`cast_upper2_diag: upper2(c, |p, q| p, a, a) == upper1(c, id, a)`), the intent matches, but the comment says "with the projection `|p, _| p`" which is ambiguous — future readers may misread this as a general diag law. A minor doc clarification is sufficient, but the current wording risks confusion about the scope of the guarantee.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3288059603 -->
<!-- glab-discussion: b83ec72ce53a7c44ab9ae227bc395b48ef685552 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/cast.rs:198` (2026-04-27 03:39 UTC) [open]

**[follow-up]** The `ordered_pair` helper is defined as a function returning a fresh `Conn<(i32, i32), i32>` rather than a module-level `const`, and is called once per proptest iteration in `maximize_eq_ceiling_random` / `minimize_eq_floor_random`. This is harmless for correctness but allocates a new closure/function-pointer triple on every proptest case; a `const` would match the pattern of `ID_I32` / `ID_F64` and avoid the (small) per-iteration cost.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3288059612 -->
<!-- glab-discussion: e7b64e774c9e09a1e8ece0f103beacb64081d4ca -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/lib.rs:133` (2026-04-27 03:39 UTC) [open]

**[follow-up]** The `pub use conn::cast::{ceiling, ..., floor, ...}` re-export shadows `std::f32::consts`-style names but more critically shadows Rust's own `floor` and `ceiling` if a user glob-imports `connections::*` alongside `std::primitive` or `libm`. The re-exported names `floor` and `ceiling` are free functions whose first argument is `&Conn<A,B>`, so accidental shadowing would produce a type error rather than silent misbehavior — but adding a module-level doc note warning against glob-importing would help downstream users avoid confusing error messages.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3288063739 -->
<!-- glab-discussion: c3a41e70b74c8cb0d559d79f55f5d07b78eddbac -->
#### ↳ cmk (2026-04-27 03:44 UTC) [open]

Fixed — clarified the docstring on the four `cast_*2_id_diag` predicates: header is now "collapse-on-projection" rather than "diagonal", with an explicit note that the broader f-parametric diagonal law would require the projection to be a parameter.

<!-- glab-id: 3288063911 -->
<!-- glab-discussion: b83ec72ce53a7c44ab9ae227bc395b48ef685552 -->
#### ↳ cmk (2026-04-27 03:44 UTC) [open]

Fixed — converted `ordered_pair()` to `const ORDERED_PAIR: Conn<(i32, i32), i32>` matching the `ID_I32` / `ID_F64` pattern in the same module, and updated the spot-check and proptest call sites accordingly.

<!-- glab-id: 3288064044 -->
<!-- glab-discussion: e7b64e774c9e09a1e8ece0f103beacb64081d4ca -->
#### ↳ cmk (2026-04-27 03:44 UTC) [open]

Fixed — added a doc comment above the `pub use conn::cast::{...}` block in `lib.rs` explaining the shadowing scenario (`floor` / `ceiling` vs other crates' globs), noting that the `&Conn<A, B>` first arg makes a wrong import a type error rather than silent misbehavior, and recommending named imports over globs.
