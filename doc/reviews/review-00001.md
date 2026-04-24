# MR !1 — GitLab workflow port from template-rust

## Summary

- Port the two-tier review workflow from `template-rust` to GitLab:
  four `.claude/commands/` (sprint-review, pull-reviews, reply-reviews,
  watch-mr), eight `scripts/` helpers (autosquash, PII scan,
  review-path/number, and `glab`-backed review fetch/reply CLIs).
- Extend `.gitlab-ci.yml` with a `check / test / audit` pipeline
  (fmt warn-only, clippy `-D warnings`, test, `cargo-deny`, gitleaks);
  add the MR description template and a root CODEOWNERS.
- Pin the toolchain and formatting policy (`rust-toolchain.toml`
  1.85, `rustfmt.toml` edition 2024, `deny.toml` permissive
  allow-list); extend the pre-commit hook with `cargo fmt --check`
  (warn) and `scripts/check-pii.sh` (block); document the whole
  two-tier loop in `CLAUDE.md` and the mermaid state diagrams in
  `doc/workflow.md`.

## Test plan

- `cargo build` — clean.
- `cargo test --workspace` — 349 tests pass (no `src/` changes).
- `cargo clippy --all-targets -- -D warnings` — clean.
- `bash -n scripts/*.sh` — syntax valid.
- `python3 -m py_compile scripts/*.py` — syntax valid.
- `scripts/check-pii.sh` on the full staged diff — exits 0.
- `ls .claude/commands/` — four commands present; skills dir gone.
- `ls doc/reviews/` — review-00000.md sentinel + review-calibration.md
  + this file.
- Pending for first real MR: live `glab api` calls (iid lookup,
  discussion fetch, reply post); `gitleaks` CI job against the
  repo.

## Local review (2026-04-23)

**Branch:** sprint/gitlab-workflow
**Commits:** 9 (main..HEAD)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

All nine commits use conventional-commit prefixes (`plan:`, `task:`,
`doc:`). Subjects are ≤72 characters. Ordering — plan first, then
task commits, then doc finalization — matches the TDD step sequence.
Each commit is a coherent unit; no unrelated changes mixed.

Commit ordering note: `4e69b53` (extends pre-commit hook to call
`scripts/check-pii.sh`) lands after `f15132a` (adds `scripts/`), so
`check-pii.sh` exists before the hook tries to invoke it. Correct.

### Code Quality

Shell scripts all set `-euo pipefail`, quote paths, use NUL-delimited
loops where needed, defuse octal interpretation via `$((10#$n))`.
Error messages go to stderr with specific context.

Python files have type hints on public functions and catch both
`FileNotFoundError` and `CalledProcessError` at every subprocess
boundary. `glab_api` pagination terminates correctly on both
empty-next-page and short-page conditions.

No leftover GitHub references found. The `deny.toml` `[sources]`
block retains `https://github.com/rust-lang/crates.io-index` — that
is the canonical `cargo-deny` registry identifier, not a GitHub
reference.

### GitLab-specific correctness

- `glab mr view -F json | jq .iid` — matches GitLab REST v4 (`.iid`
  is the internal MR id; `.id` is a different global integer).
  Consistent across `sprint-review.md`, `pull-reviews.md`,
  `reply-reviews.md`, `watch-mr.md`.
- `_glab.py` `encode_project()` with `safe=""` correctly encodes `/`
  to `%2F` for GitLab's URL-encoded project path id.
- `_glab.py` `glab_project()` probes `("fullName",
  "path_with_namespace", "full_name")`. Error message is clear if
  all three miss on a future `glab` version.
- Shell injection in `reply_review.py` — not a risk; `subprocess`
  list form bypasses the shell.

### Test Coverage

No `src/` changes this sprint. Plan's Verification lists
`existing_tests_pass` + `existing_clippy_clean` only; both green.
Scripts have no unit tests; per plan, `bash -n` and `py_compile`
syntax checks are the accepted contract. Acceptable scope.

### Plan Conformance

| Task | Status |
|------|--------|
| T1 scripts/ | ✓ (5 shell + 3 Python = 8 files; plan text says "seven" and Verification says "9 scripts (7 shell + 2 Python + _glab.py)" — see follow-up #1) |
| T2 CI + MR template + CODEOWNERS | ✓ |
| T3 doc/reviews/ + doc/workflow.md | ✓ |
| T4 four commands + delete old skill | ✓ |
| T5 pre-commit hook extended | ✓ |
| T6 CLAUDE.md Tier-2 workflow | ✓ |
| T7 rust-toolchain, rustfmt, deny | ✓ |

The MR template landed with `## Verification` + `## Review trail`
headings rather than the plan's `## Summary` + `## Test plan`. This
does not break `extract_mr_body.sh` (it stops at `## Local review`
or `<!-- glab-id:` markers, not `## Verification`). Arguably more
accurate for this project's conventions. Acceptable deviation.

### Risks

- PII scan does not block this sprint's own commits — plan and
  review files use `~/Music/...` tilde form, not `/Users/<name>/`.
- `gitleaks` CI false positives on `doc/plans/` — tracked in plan
  Recommendations; no `.gitleaks.toml` yet. Handle before first push.
- API field names on live GitLab calls — already documented as a
  known unknown in plan Review.

### Recommendations

**Must fix before push:**

None.

**Follow-up:**

1. Plan 03 Verification spot check says "9 scripts (7 shell + 2
   Python + _glab.py)" and the prose says "seven"; actual tally is
   5 shell + 3 Python = 8. Correct the count in a later doc pass.
2. `_glab.py` `glab_project()`: add `"fullPath"` as a fourth field
   probe for forward compatibility with newer `glab` versions.
3. Add `.gitleaks.toml` with path-based skips for `doc/plans/`
   before the first MR push, per the plan's existing recommendation.
4. `doc/reviews/review-00001.md` Test plan hard-codes "349 tests";
   that will go stale after Sprint B/C. Either omit the count or
   note it is a point-in-time snapshot.
