# MR !50 — Plan 32: `floor_le_ceil` cleanup — demote ~140 non-triple Conns to ConnL

## Summary

- A connection labeled as a **triple marker** (impl `ViewL` + `ViewR`) is
  a true adjoint triple iff its middle adjoint `inner` is order-reflecting,
  iff `floor(a) ≤ ceil(a)` for every `a` (proof in
  `prop::conn::floor_le_ceil` docstring; both directions are elementary
  applications of the per-side adjunction laws + monotonicity). Connections
  failing the rounding sandwich aren't triples — and the two-sided helpers
  (`round`, `truncate`, `interval`, `midpoint`) inherit the inverted
  bracket and produce wildly wrong answers (e.g. previously
  `Q004Q000.round(7.9375) = 127`).
- This MR demotes **~140 connections** whose `inner` is non-injective from
  `triple!` to `Conn::new_l`, splits across 5 commits (T1 STDRU128 = 1 Conn;
  T2 `ext_int!` macro = 20 widening Conns; T3 `fix_fix_*!` macros across 9
  host-type modules = ~119 Q-format Conns; T4–T5 the four float↔duration
  Conns the strengthened battery surfaced as latent failures; T6 docs).
- Strengthens `prop::conn::law_battery!`'s `full` subset to require
  `floor_le_ceil` so future triple markers can't silently re-introduce the
  flaw. Every remaining triple (`DURNSECS`, `STDRU064`, `U032CHAR`,
  `U032IPV4`, `U128IPV6`, `IPV6IPV4`, `F064F032`, plus f16-gated
  `F064F016`/`F032F016`) passes the strengthened battery — they're true
  triples.
- Breaking change: callers of `.floor()` on any demoted Conn will see a
  compile error (the method literally doesn't exist on `ConnL`). This is
  the desired outcome — explicit at compile time vs. wrong answer at
  runtime. Migration guidance documented in the CHANGELOG entry.

## Test plan

- [x] `cargo test --workspace` — 2300+ tests pass (lib, integration,
      doctests, compile_fail). Test count drop from ~3000 → ~2300 reflects
      the 4 R-side proptests dropped per demoted Conn (~560), minus added
      boundary spot tests (~5) and the new `floor_le_ceil` checks in `full`
      (~7).
- [x] `cargo clippy --all-targets -- -D warnings` — clean
- [x] `cargo fmt --all -- --check` — clean
- [x] `bash scripts/check_readme_mirror.sh` — clean
- [x] STDRU128 boundary spot test (`stdru128_kernel_l_at_above_max_boundary`)
      explicitly probes `Finite(max_nanos + 1)` and `Finite(u128::MAX)`,
      pinning the previously-broken case
- [x] `compile_fail/round_on_l_conn.stderr` re-blessed (the trait-impl-list
      portion of the error message changed when the demoted markers'
      `ViewR` impls disappeared)

## Local review (2026-05-01)

**Branch:** sprint/floor-le-ceil
**Commits:** 6 (origin/main..sprint/floor-le-ceil)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Six commits, each scoped to a single task (T1 through T6). The commit
messages are conventional (`fix:`/`doc:`) with imperative present-tense
subjects and all appear within the 72-character limit. The linear
history is clean — no merge commits. Each commit demotes a well-defined
family, so no unrelated changes are mixed.

The T4–T5 commit combines strengthening `law_battery!` `full` with the
four latent demotions the battery then caught. The combination is
justified because the battery change is what surfaced the failures, and
each demotion is trivially small; separating them would add noise
without improving bisectability.

### Code Quality

No unsafe code. The structural change is consistent across all 10
per-host-type files: `_floor` const fn removed, `ViewR` impl removed,
`ViewL` impl updated with `ConnL`, in-module tests switched to
`subset: l_only`. The pattern is mechanical and uniform.

The `#[allow(dead_code)]` on `ascend_to_floor` / `descend_to_floor` in
`src/float.rs` (lines 724, 743): the comment says "kept in the macro
for downstream users." These functions are `pub(super)`, meaning they
are not actually visible outside their module boundary. Downstream
users cannot call them. The rationale is therefore incorrect, though
retaining them is harmless since they encode non-trivial walk logic.
This is low-severity — the `#[allow(dead_code)]` prevents the lint
failure, so it won't break anything, but the comment misleads about
why they're being kept.

The `stdr_tests` module still imports `ViewR` with
`#[allow(unused_imports)]` (line 960, `src/time/duration.rs`).
`STDRU064` remains a triple in this module, so `ViewR` is genuinely
used — this is fine.

### Test Coverage

**The `floor_le_ceil` inline in `law_battery!` `full` versus calling
`prop::conn::floor_le_ceil`.**

The inline (added at line 503 of `src/prop/conn.rs`) directly accesses
`.floor()` and `.ceiling()` through the `ViewR`/`ViewL` type
projections rather than through the `Triple`-bound function. The two
compute the same comparison; the inline operates on `ConnR`/`ConnL`
values, while the function works on a triple marker instance.
Equivalent.

**`closure_l` gap in `ext_int_props!` integration tests.** Confidence: 85.

The plan's Verification table requires five L-side laws for the
`ext_int!` Conns: `galois_l`, `closure_l`, `kernel_l`, `monotone_l`,
`idempotent`. The hand-rolled `ext_int_props!` macro in all four
`tests/int_i*_galois.rs` files tests `galois_upper` (= galois_l),
`ceil_monotone` (= monotone_l), `inner_monotone`, `kernel_upper` (=
kernel_l), and `idempotent`. `closure_l` (`a ≤ inner(ceil(a))`) is
not tested as a named property.

This affects all 20 `ext_int!` Conns across `tests/int_i16_galois.rs`,
`tests/int_i32_galois.rs`, `tests/int_i64_galois.rs`, and
`tests/int_i128_galois.rs`. The property is derivable from `galois_l`
(substitute `b = ceil(a)`) but the plan's Verification table lists it
explicitly. The `fix_fix_*!` families use `law_battery!` with
`subset: l_only`, which does include `closure_l`; the `ext_int!`
families use a bespoke `ext_int_props!` that does not. Asymmetry
between how the two families are tested.

**STDRU128 boundary spot test.** The test
`stdru128_kernel_l_at_above_max_boundary` at `src/time/duration.rs`
line 1394 pins all four plan-specified values (`0`, `max_nanos`,
`max_nanos + 1`, `u128::MAX`). Coverage complete.

**F064DURN / F032DURN / F064STDR / F032STDR hand-rolled batteries.**
These test `galois_l`, `closure_l`, `kernel_l` but not `monotone_l`
or `idempotent`. The plan required all five L-side laws for the
demoted Conns. The float↔duration families are missing two of the
five planned properties. STDRU128 by contrast is fully covered.

**`ascend_to_floor` / `descend_to_floor` callers outside the diff.**
These are `pub(super)` within the `def_walk_helpers!` macro's
expansion, so visibility is scoped to the module they expand in. No
callers outside the diff's scope are reachable. The only callers were
`f*durn_floor` and `f*stdr_floor`, all of which are deleted.

### Plan Conformance

**T1 (STDRU128 → ConnL):** Fully implemented. `stdru128_floor`
deleted, `triple!` replaced with `ConnL` const, doctest updated,
`law_battery!` migrated to `l_only` (hand-rolled proptest, which is
appropriate for a bare const). Boundary spot test present.

**T2 (`ext_int!` → ConnL):** Macro rewritten, `_floor` deleted,
`ViewR` impl deleted. Integration tests migrated. `closure_l` is
absent from the hand-rolled `ext_int_props!` — gap versus
Verification table, as noted above.

**T3 (`fix_fix_*!` → ConnL):** All 10 per-host-type files updated.
`_floor` deleted. `ViewR` deleted. Module tests and integration tests
switch to `subset: l_only`. `closure_l` is included via
`law_battery!`. Fully covered.

**T4 (strengthen `law_battery!` `full`):** `floor_le_ceil` added
inline to the `full` arm. The design deviation (strengthening `full`
in place rather than adding a `triple` arm) is documented in the
plan's Review section and is the right call.

**T5 (audit remaining triples):** Four latent failures (`F064DURN`,
`F032DURN`, `F064STDR`, `F032STDR`) caught and demoted. The plan
states `DURNSECS` and `STDRU064` remain as triples — they are not
touched in this diff, which is correct.

**T6 (docs):** CHANGELOG and README updated. `src/fixed/i16.rs`
module docstring rewritten. The plan called for updating
`src/fixed/i*.rs` and `src/fixed/u*.rs` module docstrings — only
`i16.rs` has the rewrite visible in the diff. Other `fixed/` module
docstrings may need the same update; the diff doesn't show them being
touched. May be intentional (only `i16.rs` had the explicit "five
Galois axioms hold for every input" language to remove) or an
oversight.

**CHANGELOG count discrepancy:** The CHANGELOG at `CHANGELOG.md`
line 25 reads "14 widening Conns" then lists 20 names (I008I016
through U064I128). Actual `ext_int!` invocations: 2 in `i16.rs` +
4 in `i32.rs` + 6 in `i64.rs` + 8 in `i128.rs` = 20. The plan also
says "14 invocations" which is inconsistent with the code. One of
these counts is wrong; the enumerated list of 20 names in the
CHANGELOG matches the code, so "14" is the error.

**Deferred items respected:** No code in the diff touches
`fix_fix_*!` redesign with wider source backing, Plan 27 reversal,
or lattice trait impls.

### Risks

**`ascend_to_floor`/`descend_to_floor` rationale.** The comment at
`src/float.rs` line 722 says "Kept in the macro for downstream users."
These functions are `pub(super)` so downstream users cannot see them.
The correct rationale is that they may be needed if the floor
functions are ever re-enabled or if a downstream module in the same
crate adds a new `def_walk_helpers!` expansion that calls them. As a
practical matter, `cargo clippy` would catch this if the
`#[allow(dead_code)]` weren't present, so the suppression is
load-bearing. Consider either removing the functions (safest) or
correcting the comment.

**No security concerns.** This is a pure math library with no I/O,
no file operations, no subprocess calls, and no new dependencies.

**API break is intentional and compile-time.** Downstream callers
using `.floor()` on demoted Conns will get a compile error, not a
silent wrong answer. The `agogo` crate (mentioned in CLAUDE.md as
downstream) is not in this repo; if it calls `.floor()` on any of
the 140 demoted Conns, it will fail to compile after this lands.
The CHANGELOG migration guidance is present.

**No TODOs or stubs in implementation code.** Plan-level follow-ups
are tracked in the plan document's Follow-ups section, not as inline
TODOs.

### Recommendations

**Must fix before push:**

1. **CHANGELOG count: "14 widening Conns" should be "20 widening
   Conns."** File: `CHANGELOG.md`, line 25. The list immediately
   following names 20 Conns; the plan's own "14 invocations" count
   was already wrong. The code has 20 `ext_int!` call sites. Shipping
   a CHANGELOG with a wrong count undermines its value as migration
   documentation.

**Follow-up (future work):**

2. **`closure_l` not tested for `ext_int!` families in
   `tests/int_i*_galois.rs`.** The plan's Verification table lists
   `closure_l` as required for every `ext_int!` Conn. The property
   is theoretically implied by `galois_l` + `kernel_l`, but it is not
   named in the test suite. Adding it to `ext_int_props!` (one line
   per file, same shape as `kernel_upper`) would make the coverage
   match the Verification table exactly. Low urgency — the law holds
   by adjunction, but the gap between plan and implementation is
   traceable.

3. **`monotone_l` and `idempotent` absent from
   F064DURN/F032DURN/F064STDR/F032STDR hand-rolled batteries.** The
   plan required all five L-side laws for every demoted Conn. The
   float↔duration families test three of five. Adding
   `f064durn_monotone_l`, `f064durn_idempotent`, and their `f032*` /
   `stdr` counterparts would close the gap.

4. **`ascend_to_floor`/`descend_to_floor` comment.** The comment in
   `src/float.rs` at line 722 says "Kept in the macro for downstream
   users" but the visibility is `pub(super)`. Correct the rationale
   or remove the functions if no in-crate user is planned.
