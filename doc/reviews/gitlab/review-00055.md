# MR !55 — Plan 35: `conn_l!` / `conn_r!` macros for one-sided Conns

## Summary

- Adds `conn_l!` and `conn_r!` declaration-form macros next to
  `triple!` / `iso!` in `src/conn.rs`. They emit a bare
  `pub const ConnL<A, B> = Conn::new_l(...)` (or `ConnR<A, B>`) from
  a named-field block, completing the macro family for the five Conn
  shapes (`compose!`, `triple!`, `iso!`, `conn_l!`, `conn_r!`).
- Primary motivation is footgun avoidance: `Conn::new_l` takes
  `(ceil, inner)` while `Conn::new_r` takes `(inner, floor)` — the
  positional mismatch means a `new_l → new_r` flip silently swaps the
  slots. Named fields close that hole. The boilerplate savings vs.
  raw `Conn::new_l(...)` is intentionally small (~1 line per site).
- Converts the 9 hand-written one-sided Conn consts in `time/clock`,
  `time/date`, `time/datetime`, `time/offset`, and `time/duration` to
  the new macros; `lattice::LATTBOOL` stays as-is (per-instantiation
  generic `ConnL` inside a fn — the macro emits `pub const`, which
  cannot carry type parameters), as do per-family generator macros.
  Public type signatures unchanged at every converted site.

## Test plan

- [ ] `cargo test --workspace` — all green; new
      `conn_l_macro_expands_to_new_l` and
      `conn_r_macro_expands_to_new_r` unit tests visible; existing
      `time/*` round-trip props pass unchanged.
- [ ] `cargo test --doc` — definition-site doctests on `conn_l!` /
      `conn_r!` pass (or are `ignore`-blocked alongside `triple!` /
      `iso!`'s).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] Local pre-push hook (`RUSTDOCFLAGS="-D warnings" cargo doc
      --no-deps --features testing --document-private-items`) —
      clean.

## Local review (2026-05-04)

**Branch:** `sprint/conn-l-r-macros`
**Commits:** 2 (origin/main..sprint/conn-l-r-macros)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Both commits are clean. The `feat:` commit (`d9bee36`) ships
`src/conn.rs` (macros + tests) and all five `src/time/*.rs`
call-site conversions together — a single green-at-that-sha
delta. The `doc:` commit (`f1313ba`) adds only the plan and
review files. Conventional subjects, ≤72 chars, atomic split.

### Code Quality

`conn_l!` / `conn_r!` sit immediately after `iso!` in
`src/conn.rs`, both `#[macro_export]`ed, both accepting
`$(#[$meta:meta])*` and `$vis:vis` matching `triple!`/`iso!`,
and using `$crate::conn::ConnL` / `$crate::conn::Conn::new_l`
consistently in expansion. Doc comments at the macro definition
sites explain the distinction from `triple!` and cite the
`new_l` / `new_r` argument-order footgun.

Lifted helpers in `time/{clock, date, datetime, offset}.rs` are
all module-private (no inadvertent `pub`) and Conn-name-prefixed
where one file hosts more than one Conn (`timenano_*` vs
`timesecs_*`, `ofdtnano_*` vs `ofdtsecs_*`); single-Conn files
use the Conn-name prefix uniformly (`datejday_*`, `pdtmdate_*`).
The `use crate::conn::Conn` imports removed from those files
were only needed inside the old const-init blocks; their
removal is correct. `duration.rs`'s `f064durn_*` /
`stdru128_*` / `f064stdr_*` family helpers were already at
module scope before this sprint — only the const declarations
that reference them moved to macro form.

`doc/design.md` was not touched, consistent with the plan's
"if such a section exists; otherwise skip" escape clause.

### Test Coverage

Both Verification-table unit tests are present and assert what
the table says:

- `conn_l_macro_expands_to_new_l` (`src/conn.rs:923`):
  constructs a hand-written `Conn::new_l(...)` reference and
  asserts `.ceiling()` / `.upper()` agreement with the macro-
  built const over representative `i64` / `i32` boundary
  inputs. Both adjoint slots covered.
- `conn_r_macro_expands_to_new_r` (`src/conn.rs:936`): same
  shape over `Conn::new_r`. The reference's argument order
  (`_i32_to_i64, _i64_to_i32`) was sanity-checked against
  `Conn::new_r`'s `(inner: fn(B)->A, floor: fn(A)->B)`
  signature — the slots line up.

All converted Conn doctests preserved verbatim inside the
macro brace; `rustdoc` extracts them from the expanded
`pub const`. Macro definition-site doctests use `ignore`,
matching `triple!`/`iso!` style. No existing law-property
test was removed or weakened — converted sites are pure
refactors with unchanged helper bodies.

### Plan Conformance

T1, T2, T3, T4 all delivered. Verification-table properties
both present. `lattice.rs:402` correctly excluded (generic-fn
body, not a `pub const` — the macro emits `pub const`, which
cannot carry type parameters). 9 sites converted, matching
the Review-section count.

The plan's own goal sentence and T3 site list mention "~10"
and include `lattice.rs`; the Review section corrects this to
9. The discrepancy is entirely in-document. Fix recommended
as a follow-up so the MR description (drawn from the review-
file Summary, which currently echoes the same "10 + lattice"
phrasing) doesn't repeat the inconsistency on GitLab.

### Risks

No TODOs or `unimplemented!` stubs. No public API surface
change — every converted `pub const` retains its name, type,
and visibility (the macro emits `$vis const $name:
$crate::conn::ConnL<$A, $B>`). Macro hygiene is correct: the
`$ceil` / `$inner` / `$floor` arguments resolve in the
caller's scope (intentional, so callers can pass bare fn
paths), and all crate-relative references go through
`$crate::`.

**One minor doc inconsistency (confidence 82, follow-up only):**

`src/conn.rs` lines 707-712 and the `conn_r!` doc include an
"Expands to:" `ignore` block showing
`pub const TIMENANO: ConnL<Extended<Time>, i64> = Conn::new_l(...)`
without the `$crate::` qualification the macro actually
emits. This block does not exist in the `triple!` / `iso!`
docs, so the new docs depart from the stated "mirror the
`triple!` / `iso!` doctest style verbatim" plan instruction.
The block can't fail any test (it's `ignore`d), but a
downstream reader inspecting the docstring to understand
cross-crate usage will see the un-qualified path and wonder
whether this is what's emitted. Either delete the "Expands
to:" block (cheapest) or qualify the paths shown.

### Recommendations

**Must fix before push:**

None. No bugs, no broken tests, no Conn-name violations, no
API surface changes, no unsafe code, no removed law tests.
The branch is clear to push.

**Follow-up (future work, can ride this MR or a later one):**

1. **Fix the review-file `## Summary` to match what shipped.**
   Lines 15-18 list "`time/clock`, `time/date`, `time/datetime`,
   `time/offset`, `time/duration`, and `lattice.rs`" as
   converted sites — but `lattice.rs` was correctly excluded
   (generic fn, not `pub const`). Drop "and `lattice.rs`" from
   the bullet so the GitLab MR description (extracted verbatim
   from this `## Summary`) doesn't repeat the inaccuracy.

2. **`conn_l!` / `conn_r!` doc "Expands to:" block.** Either
   remove the block (aligning with `triple!`/`iso!` style
   exactly per the plan's "mirror verbatim" instruction) or
   correct the shown expansion to use the `$crate::conn::*`
   paths the macro actually emits.

3. **Plan-document internal consistency.** The plan's goal
   sentence says "~10 sites including `lattice.rs`" but the
   Review section corrects to 9. A one-line edit aligning the
   goal would close the loop.
