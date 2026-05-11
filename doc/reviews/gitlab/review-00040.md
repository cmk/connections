# Review 00040 — Plan 26: make cargo fmt pre-commit step blocking

## Summary

- Flips `.claude/settings.json`'s `cargo fmt --all -- --check` step
  from a non-blocking warning (`{ … || echo '[warn] …'; }`) to a
  hard block, matching the other quality gates. Plan 25 / MR !39 hit
  a real CI fmt failure that local tooling let through; this lands
  the safety net so it can't recur.
- Folds in two adjacent fixes: drops a stale `F064B016` entry from
  `scripts/readme_mirrors.txt` (manifest pointed at a long-removed
  path `src/conn/float/f64.rs` and a Conn const that no longer
  exists), and updates `CLAUDE.md` §Pre-commit hook to describe all
  five steps with their blocking semantics — the prior list named
  only four.

## Test plan

- [x] `cargo fmt --all -- --check` clean.
- [x] `cargo build` clean.
- [x] `cargo test --workspace` clean (no Conn-shape changes; this
      sprint touches workflow infra only).
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `scripts/check_readme_mirror.sh` exits 0 (manifest reduces to
      header-comments-only post-T2).
- [x] `.claude/settings.json` parses as valid JSON.
- [x] Regression probe: a manually-injected fmt drift in
      `src/conn.rs` (extra whitespace after `pub struct`) makes
      `cargo fmt --all -- --check` exit 1. File restored before
      commit; never staged.
- [x] Full pre-commit chain (`cargo fmt && check-pii &&
      check_readme_mirror && cargo test && cargo clippy`) returns 0
      on a clean tree.

## Local review (2026-04-28)

**Branch:** sprint/fmt-blocking
**Commits:** 4 (origin/main..sprint/fmt-blocking)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All four subjects use the correct conventional prefix (`plan:`,
`task:`, `doc:`) and stay under 72 characters. Each commit is
atomic for its role: the plan lands first (before any source
change), T2 precedes T1 in commit order, matching the dependency
graph in the plan. The doc/review skeleton is last. No merge
commits, no fixup squashing needed.

The T2-before-T1 ordering is intentional and the rationale is
documented in the plan's Dependency Graph section: without T2,
the new blocking hook would reject its own landing commit because
`check_readme_mirror.sh` exits 1 on the stale manifest entry.
That logic checks out — the plan commit (`2dfab8a`) even explains
it in the body.

### Code Quality

**`.claude/settings.json` hook command — clean.** The new command
preserves the `&&`-chain short-circuit semantics; each step runs
only if the prior one exits 0. The old `{ … || echo '…'; }`
construct made the fmt step always succeed; the new form correctly
fails fast on fmt drift. JSON parses successfully (verified). No
quoting issues — the command contains no single quotes or
backslashes that need escaping.

**`CLAUDE.md` §Pre-commit hook — accurate, with one minor count
concern.** The rewritten list now enumerates all five steps in
order, matching the actual hook command exactly. The prior list
omitted step 3 (`check_readme_mirror.sh`) entirely and called
step 1 non-blocking; both are now corrected. Bullet 1 includes a
rationale sentence referencing Plan 25 / MR !39 — slightly
changelog-flavoured for a reference doc but answers "why is this
blocking?" inline. Acceptable.

**`scripts/readme_mirrors.txt` after deletion — valid.** Reduces
to 18 lines of header comments. `check_readme_mirror.sh`'s
`[[ -z "$conn" || "$conn" =~ ^[[:space:]]*# ]]` guard skips every
remaining line; the loop body never executes, `drift` stays 0,
script exits 0. Verified by running the script directly against
the post-edit manifest.

### Test Coverage

The plan's Verification section calls for four spot checks, all
reported as completed in the Review section: JSON parse, hook
command shape, clean-tree chain, fmt-drift probe. The drift probe
was manual and one-shot, not a committed test — appropriate for
infra tooling of this kind. Property tests are correctly noted as
not applicable. Evidence is credible and proportionate to scope.

### Plan Conformance

Both tasks implemented. T1 (`.claude/settings.json` + `CLAUDE.md`)
and T2 (`scripts/readme_mirrors.txt` deletion) match the plan
descriptions verbatim.

T2 was not in the original plan commit but is documented in both
the plan file and the plan commit's body. The dependency graph
and Review section together give sufficient context for a reader
walking the audit trail.

### Risks

**Blocking fmt on mid-refactor commits.** Intentional behavioural
change: any `git commit` now fails on `cargo fmt` drift. The plan
frames this as desired ("fail-fast"). Minor UX regression: the
old warning message (`run: cargo fmt --all`) was helpful friction
at exactly the failure moment; now a user sees only rustfmt's
diff output. Not a correctness issue.

No platform-specific surprise. No security or dependency concerns.
The plan's Recommendations section ("None") correctly scopes out
follow-ups (editor fmt-on-save, `rustfmt.toml` changes).

### Recommendations

**Must fix before push:** None.

**Follow-up (future work):** Consider adding the original "Run:
`cargo fmt --all`" remediation hint at failure time — either as
a brief comment in `CLAUDE.md` §Pre-commit hook (where someone
debugging an aborted commit would land), or as a `|| (… ; echo
'Run: cargo fmt --all'; false)` wrapper that preserves the
blocking exit code while still surfacing the suggestion. Pure DX
nicety; not a correctness issue.
