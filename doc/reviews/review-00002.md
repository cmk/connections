# MR !2 — GitLab workflow port from template-rust

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
4. `doc/reviews/review-00002.md` Test plan hard-codes "349 tests";
   that will go stale after Sprint B/C. Either omit the count or
   note it is a point-in-time snapshot.

<!-- glab-id: 3281848279 -->
<!-- glab-discussion: e975b87346d3d0e9fe4250cf8d9e00c1d1d0c529 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/claude_review.py:290` (2026-04-24 02:31 UTC) [open]

**[follow-up]** The `git_diff` call uses `f"{base}...{head}"` (three-dot notation), which resolves to the diff between the merge-base and `head` — correct for MR review. However, the error message on line 296 says `` `git diff {base_sha}...{head_sha}` `` with three dots, matching the actual call, so the diagnostic is accurate. The real risk is that `CI_MERGE_REQUEST_DIFF_BASE_SHA` is not always the true merge-base on GitLab (it can be the target branch tip); if this produces an oversized or wrong diff, there's no fallback. Consider documenting this assumption or falling back to `git merge-base` when the env var looks stale.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281848289 -->
<!-- glab-discussion: faa91bcb48d98ba7f8805e96aa1c23117debc001 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/pull_reviews.py:152` (2026-04-24 02:31 UTC) [open]

**[must-fix]** The `existing_ids` function parses `<!-- glab-id: (\d+) -->` and casts matches to `int`, but note ids from GitLab's REST API are integers while `it['id']` is stored directly from the API response without explicit int-casting in `collect_items`. If GitLab ever returns note ids as strings (which it does in some API versions), `it['id'] not in seen` will always be `False` (str ≠ int), causing every note to be appended on every run, breaking idempotency. Both the `existing_ids` return set and the `it['id']` value should be cast to the same type consistently.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281848304 -->
<!-- glab-discussion: 44f0ac9daa8fe07c9e8b2a8b4e712d94cd3448b3 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/reply_review.py:96` (2026-04-24 02:31 UTC) [open]

**[follow-up]** The `find_discussion_for_note` function compares `n.get('id') == note_id` where `note_id` is an `int` (from `argparse type=int`) and the API may return note ids as integers or strings depending on GitLab version. This is the same type-mismatch risk as in `pull_reviews.py` — a string id from the API will never equal the int argument, causing the search to exhaust all pages and raise `SystemExit(1)` with a misleading 'note id not found' error. Cast both sides to `int` or `str` for the comparison.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281848317 -->
<!-- glab-discussion: ad56ec3a8ec143601bcb24332c669de693ecaf6c -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `.claude/commands/watch-mr.md:186` (2026-04-24 02:31 UTC) [open]

**[follow-up]** The backoff table comment says `BACKOFF_MINUTES=(5 5 5 10 10)` has 5 slots and quits on the "6th quiet tick (after the 5 slots are exhausted)", but the decision logic reads `if [ "$new" -gt "$N_SLOTS" ]` where `N_SLOTS=5`. After the 5th unproductive tick `new` becomes 5 — which is not `> 5` — so the quit fires on the *6th* quiet tick (when `new` becomes 6), meaning the actual silence budget is 5+5+5+10+10 minutes plus one more 10-minute tick before quitting, not 35 minutes as stated in the table. The table's `Tick 5 → quit` annotation is misleading and should reflect the actual `> N_SLOTS` condition.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281848331 -->
<!-- glab-discussion: 726d1d79d19fe3f914d02095fe6c20cd3ad5223a -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/claude_review.py:242` (2026-04-24 02:31 UTC) [open]

**[follow-up]** The `post_finding` function sets `old_path` equal to `new_path` for every finding, which is correct for files that were not renamed but will produce wrong inline anchors for renamed files. GitLab requires `old_path` to be the pre-rename path to anchor correctly on a renamed file's diff; using `new_path` for both will cause GitLab to reject the inline position and fall back to a general comment, silently degrading anchor quality. Consider accepting an optional `old_path` field in the finding schema or documenting this limitation.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281852689 -->
<!-- glab-discussion: faa91bcb48d98ba7f8805e96aa1c23117debc001 -->
#### ↳ cmk (2026-04-24 02:35 UTC) [open]

Fixed — added `int()` coercion at the API boundary in `collect_items()` (f4380ea). Same commit also fixes the parallel case in `reply_review.py:96`.

<!-- glab-id: 3281852817 -->
<!-- glab-discussion: 44f0ac9daa8fe07c9e8b2a8b4e712d94cd3448b3 -->
#### ↳ cmk (2026-04-24 02:35 UTC) [open]

Fixed — same commit (f4380ea). `find_discussion_for_note` now casts via `int(n.get("id", 0))` with a TypeError/ValueError guard so a non-numeric id is skipped rather than crashing the pager.

<!-- glab-id: 3281852935 -->
<!-- glab-discussion: e975b87346d3d0e9fe4250cf8d9e00c1d1d0c529 -->
#### ↳ cmk (2026-04-24 02:35 UTC) [open]

Deferred — tracked as a follow-up. `CI_MERGE_REQUEST_DIFF_BASE_SHA` being stale is an uncommon GitLab rarity, and the `MAX_DIFF_CHARS` truncation bounds the worst-case blast radius. Will revisit with a `git merge-base` fallback if we see a wrong-diff incident.

<!-- glab-id: 3281853092 -->
<!-- glab-discussion: 726d1d79d19fe3f914d02095fe6c20cd3ad5223a -->
#### ↳ cmk (2026-04-24 02:36 UTC) [open]

Deferred — tracked as a follow-up. The general-comment fallback already handles rename-anchor rejections cleanly; adding a rename-aware `old_path` in the finding schema would require Claude to know about renames, which adds prompt complexity for an edge case. Will revisit if we see frequent anchor rejections on renamed files.

<!-- glab-id: 3281853219 -->
<!-- glab-discussion: ad56ec3a8ec143601bcb24332c669de693ecaf6c -->
#### ↳ cmk (2026-04-24 02:36 UTC) [open]

Push-back — the table matches the code. Tracing: tick 0 at t=0 increments count 0→1 (not `>5`, sleep 5m); tick 4 at t=25 increments 4→5 (not `>5`, sleep 10m); tick 5 at t=35 increments 5→6 (`>5`, **quit — no additional sleep**). Total silence 5+5+5+10+10 = 35m, matching the `Tick 5 | 35m | quiet | **quit**` row. The "6th quiet tick" phrasing uses 1-based ordinal counting of fires, consistent with `Tick 5` being the 6th index-0 tick.
