# MR !61 — Plan 38: Interval<A> + filter_l/filter_r; prune midpoint

## Summary

- Adds an `Interval<A>` ADT (`Empty | Bounded { lo, hi }`) in a new
  `src/interval.rs` module, ported from `Data.Order.Interval` in the
  Haskell `connections` crate. `Interval::new` collapses
  incomparable / out-of-order endpoints to `Empty` (handles NaN
  cleanly); `imap` re-runs the preorder check on its result so
  non-monotonic maps collapse to `Empty`. Carries a containment
  preorder (`Empty ≤ everything`; `Bounded i₁ ≤ i₂ ⟺ i₂ ⊇ i₁`).
  Re-exported as `connections::Interval`.
- Replaces `pub fn interval(t, x) -> Option<Ordering>` (the misnamed
  half-comparison) with a real bracket function returning
  `Interval<A>`. Deletes `pub fn midpoint` (the `Add + Div`
  constraints excluded NonZero / dates / IpAddr / fixed-point
  shapes; only consumer was `round`). Rewrites `round` to compute
  its tiebreak directly from the bracket endpoints; bound delta
  drops `Add + Div`, keeps `Sub + From<u8> + PartialOrd`. Tiebreak
  direction (toward zero) preserved.
- Adds `Conn<_, _, L>::filter_l` and `Conn<_, _, R>::filter_r`
  inherent methods — principal-filter / principal-ideal membership
  predicates (`PartialOrd`-only, no arithmetic). Wires nine new
  property predicates into `law_battery!`: three bracket
  invariants on the `full` arm, three filter invariants each on
  `l_only` / `r_only`. New `src/prop/interval.rs` carries five
  standalone `Interval<A>` predicates with their own proptest block.

## Test plan

- [ ] `cargo test --lib` — 1163 tests pass (was 893 pre-sprint;
      delta ≈ 9 properties × ~30 battery instantiations + new
      `prop::interval` proptests).
- [ ] `cargo test --doc` — 57 doctests pass (was 51; delta = 5
      `Interval<A>` doctests + 1 reworked `interval` + 2
      `filter_l` / `filter_r`, minus 1 deleted `midpoint`).
- [ ] `cargo test --workspace --quiet` — battery green on every
      `law_battery!` instantiation under `src/{addr,char,float,
      fixed,time}/`.
- [ ] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
      --document-private-items` — clean (catches the
      `crate::interval` ambiguity introduced by the new module
      vs the existing fn re-export; resolved via fully-qualified
      `crate::conn::interval`).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `scripts/check-pii.sh` — exits 0.
- [ ] `scripts/check_readme_mirror.sh` — exits 0 (no new headline
      `Conn` const introduced; README mirror rule N/A).

## Local review (2026-05-06)

**Branch:** `sprint/interval-filter`
**Commits:** 6 (origin/main..sprint/interval-filter)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All six commits use conventional prefixes (`task:`, `feat:`, `feat:`,
`test:`, `fix:`, `doc:`) and are reasonably atomic. The `feat:`
combining `interval` rename + `midpoint` deletion + `round` rewrite +
`filter_l`/`filter_r` is a deliberate bundle (changes must move
together to keep the build green). Each commit leaves
`cargo test --workspace` passing.

### Code Quality

`#![forbid(unsafe_code)]` respected. Doc-link disambiguation correct
after `pub mod interval` was introduced alongside the existing
`pub use conn::interval` (function): both `lib.rs` and
`src/interval.rs` use fully-qualified `crate::conn::interval` for
the function. Module placement of `src/interval.rs` follows the
top-level layout convention. The `## ConnK` index in `lib.rs`
correctly drops `midpoint`, updates `interval`'s wording, and adds
prose for the one-sided `filter_l`/`filter_r` methods. Clippy clean.

### Test Coverage

**Must-fix #1 — `round_picks_endpoint` not wired into `@batch full`.**
The plan T6 lists this as a required wiring; the verification table
includes it as a must-pass property; the predicate exists at
`src/prop/conn.rs:337` but no `#[test]` block was added in the
`@batch full` arm. The `Sub<Output = A> + From<u8>` bounds may
prevent universal wiring (`addr::ip` / `char` batteries have non-
numeric `A` types). Either wire it (and accept the bound-tightening
on numeric-only batteries via a new subset variant) or document the
deferral in the plan's Review section with rationale. Currently it
is silently omitted.

**Must-fix #2 — undocumented property reformulation.** The plan
specified `bracket_idempotent`, but during implementation it failed
against five batteries because bracket endpoints are themselves
grid-aligned and have singleton brackets, not the parent bracket.
Reformulated as `bracket_endpoints_self_bracket` (which is the
*correct* idempotence-flavored property and is sound). The
reformulation is a design deviation from the plan; per the TDD
workflow (CLAUDE.md), it must be documented in the plan's Review
section.

**Must-fix #3 — undocumented property substitution.** The plan
specified `imap_monotonic_preserved` (general monotone `f`); the
diff ships `imap_identity_preserves` (only `f = id`). Identity is
trivially monotone but does not exercise the case where a strictly
monotone function re-sorts endpoints. Same plan-Review documentation
requirement.

**Weaker-than-needed properties:** `filter_l_dual_to_ceil` and
`filter_r_dual_to_floor` are tautologies — `filter_l(a, b) ==
(ceil(a) <= b)` is literally the body of `filter_l`. They will
always pass and never catch a regression. Acceptable as
specification documentation, but not coverage.

`bracket_endpoints_share_b_cell`'s `B: Eq` bound is satisfied by
all current battery instantiations (every `B` here either derives
or hand-impls `Eq`). Sound.

`Interval<A>` proptest block covers `i32` only; NaN handling is
verified via doctests on `Interval::new` and the
`prop::interval::new_orientation` predicate (which works correctly
on `f64::NAN` since `partial_cmp` returns `None` → `Empty`). No
gap for NaN specifically.

### Plan Conformance

- T1 (Interval<A> ADT): complete.
- T2 (replace `interval`): complete.
- T3 (delete `midpoint` + obsolete predicates): complete.
- T4 (rewrite `round`): complete; tiebreak direction (toward zero)
  preserved.
- T5 (`filter_l`/`filter_r` inherent methods): complete with
  doctests.
- T6 (property bodies + `law_battery!` plumbing): **incomplete** —
  9/10 wired; `round_picks_endpoint` missing from `@batch full`.
- T7 (standalone `Interval<A>` properties): **partially complete** —
  4 of 5 planned predicates present; `imap_monotonic_preserved`
  weakened to `imap_identity_preserves`.
- T8 (`lib.rs` index update): complete.
- T9 (verification gate): all gates green; T6/T7 gaps not gating.

### Risks

`round` tiebreak direction preserved correctly (`Equal | None →
truncate(t, x)` faithfully replicated). `midpoint` removal is a
breaking change to any external consumer; the MR description
mentions the deletion in the second bullet. Pre-0.1.0 crate, no
known cross-crate consumers — acceptable. `imap` antimonotone
collapse-to-Empty behavior is documented at the doctest. `Interval`
API surface uses `endpts(self)` which moves out, fine because
`Interval: Copy` when `A: Copy`.

### Recommendations

**Must fix before merge:**

1. Wire `round_picks_endpoint` into `@batch full` *or* document the
   deferral in `doc/plans/plan-2026-05-06-01.md`'s Review section
   with the bound-tension rationale (`Sub + From<u8>` excludes
   `addr` / `char` batteries).

2. Append a Review section to `doc/plans/plan-2026-05-06-01.md`
   documenting: (a) the `bracket_idempotent` →
   `bracket_endpoints_self_bracket` reformulation with the failure
   trace and reasoning; (b) the `imap_monotonic_preserved` →
   `imap_identity_preserves` substitution. Both are TDD-workflow
   deviations and must be tracked.

**Follow-up (future work):**

- Replace `imap_identity_preserves` with a real monotone proptest
  (e.g., `i.imap(|a| a.saturating_add(k))` for `k: i32`) — would
  exercise the actual reordering / preservation invariant the plan
  intended.
- Strengthen `filter_l_dual_to_ceil` / `filter_r_dual_to_floor`
  beyond definitional tautologies — perhaps test the excluded zone
  (`!filter_l(a, b)` whenever `b < ceil(a)`).
- Consider a `numeric_only` battery subset for round/truncate
  contract properties that need arithmetic bounds.

---

## Round 1 fixes (2026-05-06)

All three must-fix items and all three follow-ups addressed in a
single fix commit on `sprint/interval-filter`. Branch tested clean
on every layer (`cargo test --workspace`, `cargo test --doc`,
`cargo clippy --all-targets -- -D warnings`,
`cargo fmt -- --check`, `RUSTDOCFLAGS="-D warnings" cargo doc
--no-deps --document-private-items`, `scripts/check-pii.sh`,
`scripts/check_readme_mirror.sh`).

**Must-fix #1 — `round_picks_endpoint` wired.** Added a new
`@batch numeric_only` arm to `law_battery!` (`src/prop/conn.rs`),
a strict superset of `@batch full` that adds three arithmetic-
bound contract properties (`round_picks_endpoint`,
`truncate_picks_endpoint`, `truncate_toward_zero`). Switched
`F064F032` to `subset: numeric_only` (`src/float/f32.rs:213-219`).
Non-numeric `full` batteries (`addr::ip::*`, `char::U032CHAR`,
`time::DURNSECS` / `STDRU064`) stay on `full` and remain green —
their `A` types don't impl `Sub<Output = A> + From<u8>`.

**Must-fix #2 / #3 — plan Review section appended.** Documented
`bracket_idempotent` → `bracket_endpoints_self_bracket` and
`imap_monotonic_preserved` → `imap_identity_preserves +
imap_saturating_add_preserves` reformulations in
`doc/plans/plan-2026-05-06-01.md`'s newly-populated `## Review`
section, including the failure trace, structural reasoning, and
sound-replacement rationale for each.

**Follow-up #1 — real monotonic imap proptest.** Added
`imap_saturating_add_preserves(lo, hi, k: i64)` to
`src/prop/interval.rs`, exercising `f(a) = a.saturating_add(k)`
(strictly monotone non-decreasing over `i64`, no overflow
filtering needed). Wired into the in-file proptest block.

**Follow-up #2 — `filter_*_via_*` non-tautologies.** Renamed
`filter_l_dual_to_ceil` → `filter_l_via_upper` (asserts
`filter_l(a, b) ⟺ a ≤ upper(b)`) and `filter_r_dual_to_floor`
→ `filter_r_via_lower` (asserts `filter_r(a, b) ⟺ lower(b) ≤ a`).
These are non-trivial: they hold only because of the L/R Galois
adjunctions, so a regression in L/R Galois that left the body of
`filter_l` untouched would now show up here. Battery wiring
updated to call the renamed predicates.

**Follow-up #3 — `numeric_only` subset.** Same change as
must-fix #1, now in place.

Test-count delta: 1163 → 1167 lib tests
(+ `imap_saturating_add_preserves` proptest in `src/prop/interval.rs`,
+ `round_picks_endpoint`, `truncate_picks_endpoint`,
`truncate_toward_zero` instantiations on `F064F032`).
