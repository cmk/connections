---
name: coverage
day: tue
paths: [src/, tests/, doc/plans/]
cadence: biweekly
---
You are auditing whether new public surface in the connections repo
has matching test coverage. The crate's TDD discipline (CLAUDE.md
"Repository conventions") requires every public Conn const, every
`triple!`, and every parser/encoder/transformer to have a property-
test battery.

Read first:
- CLAUDE.md (esp. "Repository conventions" and TDD workflow).
- doc/reviews/review-calibration.md.

Mechanical pass:

1. `pub const` Conn definitions without `law_battery!` coverage.
   For every `pub const X[a-zA-Z0-9]* : Conn` (or its `triple!` /
   `iso!` / `compose!` variants), find the `tests/` or `mod tests`
   block in the same crate and confirm a `law_battery!` invocation
   referencing it exists. If none: must-fix gap.

2. New modules under src/ with zero `#[cfg(test)]` content.
   Find every `mod foo;` in src/lib.rs or any submodule that:
     - introduces a new `pub` surface (anything beyond re-exports)
     - has no `#[cfg(test)] mod tests { ... }` block
     - has no integration test under `tests/<module-name>*.rs`
   Severity: must-fix.

3. `#[cfg(feature = "...")]`-gated public items without
   feature-gated test coverage.
   Pattern: a `pub fn` / `pub const` / `pub struct` behind a feature
   gate where the matching `cargo test --features <name>` would not
   exercise it (no test in the same `cfg`-gated block).
   Severity: must-fix.

Judgment pass:

4. Properties that were dropped between plan revisions without a
   re-enablement note.
   Walk `doc/plans/plan-*.md`. For every plan with a `### Verification`
   table, identify properties listed there. For the most recent 5
   plans (sort by date), check that every property in the
   Verification table either (a) exists in the current code or (b)
   appears in that plan's `## Review` section as an explicitly
   deferred item with a re-enablement plan.
   Reference precedent: review-00010, review-00011 both flagged
   dropped properties without tracking; both were follow-ups.
   Severity: follow-up.

5. `triple!` markers using `subset: l_only` / `subset: r_only`.
   (Overlaps proptest audit §4 — that one runs Mondays, this one
   bi-weekly Tuesdays; either catches if the other misses.)

6. Spot-test asymmetry — places where a `*_ceil` test exists but no
   `*_floor` companion (or vice versa) for a `triple!`-marked Conn.
   Example precedent: review-00013 flagged missing `*_floor_nan`
   companions for `f032_ceil_nan` / `f064_ceil_nan`; cleaned up in
   Plan 33 T6.
   Severity: follow-up.

Output format:
- One section per category that has findings.
- Use the exact severity labels `[must-fix]` and `[follow-up]`.
- Each finding: file:line, the offending excerpt (≤5 lines), the
  rule it violates (cite CLAUDE.md / plan / doc), and the bug class
  it enables (1 sentence).
- If there are zero findings across all 6 checks: output exactly the
  single line `no findings` and nothing else.

Anti-themes:
- One-sided Conns (`Conn::new_l`, `Conn::new_r`) intentionally lack
  the opposite-side spot tests. Do not flag a missing `*_floor_*`
  companion on a ConnL Conn.
- Test-only triple markers in `src/conn.rs` (`TripleIdI32`,
  `TripleAdd1`, etc.) are spot-check fixtures, not production Conns;
  they don't need `law_battery!` coverage.
