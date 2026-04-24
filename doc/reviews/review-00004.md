# MR !4 — Manual re-review trigger + claude-review hardening

## Summary

- Add a manual-trigger path to `claude-review`: setting
  `CLAUDE_REVIEW_MR` on a manual pipeline (via `glab ci run` or the
  web UI) re-runs the reviewer against the named MR without needing
  a new commit. The script reads the MR's base/head SHAs from the
  GitLab API when the merge-event env vars aren't present.
- Harden against transient Anthropic 5xx / 529 windows: bump the
  SDK client's `max_retries` from 2 to 5 for in-process backoff, and
  add `retry: 2` to the CI job so GitLab reruns the whole thing on
  `script_failure` / `api_failure`. `allow_failure: true` stays on,
  so even total exhaustion doesn't block a merge.
- Drive-by fix to `scripts/next_mr_number.sh`: the GitLab MR-list
  endpoint doesn't accept `order_by=iid`, and `glab api` has no
  `--jq` flag. Both were latent bugs from Sprint A's initial port.

## Test plan

- `cargo test --workspace` — clean (no `src/` changes).
- `cargo clippy --all-targets -- -D warnings` — clean.
- `python3 -m py_compile scripts/claude_review.py` — syntax valid.
- `bash -n scripts/next_mr_number.sh` — syntax valid.
- `scripts/next_mr_number.sh` against `cmk/connections` — returns
  the predicted next iid (verified: 4 before this MR opens).
- Pending for live first-exercise: `glab ci run --variables
  CLAUDE_REVIEW_MR=<iid> --branch <source>` → manual pipeline fires
  only the `claude-review` job → script reads `CLAUDE_REVIEW_MR`,
  fetches SHAs via API, posts findings to the MR.

## Local review (2026-04-23)

**Branch:** sprint/rereview
**Commits:** 7 (origin/main..HEAD, post-must-fix commit)
**Reviewer:** Claude (sonnet, independent)

---

### Findings

Tier-1 surfaced three must-fix items — all addressed before push in
the `fix: Address Tier-1 review must-fix items` commit:

1. **`scripts/claude_review.py:374` — `head_sha` preference inverted.**
   `mr.get("sha") or diff_refs.get("head_sha")` could select a newer
   top-level `sha` while `base_sha` still pointed at the old
   `diff_refs` snapshot, producing a cross-version diff. Flipped to
   `diff_refs.get("head_sha") or mr.get("sha")` so both SHAs come
   from the same diff version.
2. **`scripts/claude_review.py:113` — `git fetch --unshallow origin`
   fails on complete clones.** The MR-event job already uses
   `GIT_DEPTH: 0`, which makes the clone complete; `--unshallow`
   then errors with "fatal: --unshallow on a complete repository
   does not make sense." Replaced with plain `git fetch origin`,
   which works on both shallow and complete clones.
3. **`CLAUDE.md` — typo "rerunts" → "reruns".** Trivial but CLAUDE.md
   is injected verbatim into every reviewer's context, so stale
   copy here compounds.

One follow-up also picked up: added a YAML comment to the
`$CLAUDE_REVIEW_MR` rule in `.gitlab-ci.yml` noting that the branch
passed to a manual trigger is irrelevant (the script ignores
`CI_COMMIT_SHA` on that path).

### Plan Conformance

| Task | Status |
|------|--------|
| T1 manual-trigger path in claude_review.py | ✓ |
| T2 CI rules + retries | ✓ |
| T3 CLAUDE.md docs | ✓ |
| T4 plan wrap + MR | ✓ |

Drive-by fix to `next_mr_number.sh` (unsupported `--jq`,
`order_by=iid`) is documented in the plan Review.

### Risks (addressed)

- `CI_COMMIT_SHA` vs MR-head mismatch on manual pipelines: plan
  acknowledges it, code handles it (API-fetched SHAs override).
- `git fetch origin <sha>` on gitlab.com: `uploadpack.allowReachableSHA1InWant`
  is enabled, so this works.
- Shell-injection on SHA arg: `subprocess.check_output` with list
  form, no shell interpretation.

### Recommendations

**Must fix before push:** None (all three landed in fix commit).

**Follow-up:** The `retry: 2` + SDK `max_retries=5` combo is
conservative. Tune after accumulating 5–10 real runs; if Anthropic
529s remain rare, drop `retry: 2` to save runner minutes.
