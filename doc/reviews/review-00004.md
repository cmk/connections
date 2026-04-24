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

<!-- glab-id: 3281912847 -->
<!-- glab-discussion: 1366f8b3b55d2e960580d8794fbf47bfdccd50c8 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/claude_review.py:362` (2026-04-24 03:23 UTC) [open]

**[follow-up]** The guard `if base_sha and head_sha and os.environ.get('CI_MERGE_REQUEST_IID')` means that if a manual trigger sets `CLAUDE_REVIEW_MR` but the runner *also* happens to have partial MR env vars (e.g. `CI_COMMIT_SHA` set from a branch push but `CI_MERGE_REQUEST_DIFF_BASE_SHA` absent), the code falls through to the API path — which is correct. However the condition is slightly misleading: it requires all three to be set, yet `CI_COMMIT_SHA` is always set in any pipeline. Consider expressing the intent as `os.environ.get('CI_MERGE_REQUEST_IID') and base_sha and head_sha` and adding a brief comment that `CI_COMMIT_SHA` alone is not sufficient to confirm the MR-event envelope, to prevent future confusion.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281912857 -->
<!-- glab-discussion: d18dd45a857a1a376e34e33015e3160bd4e91d5c -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/claude_review.py:382` (2026-04-24 03:23 UTC) [open]

**[follow-up]** The error message says `"Is the MR closed/unavailable?"` but the actual condition also fires when `diff_refs` is present but `base_sha` is `null` (e.g. for a freshly opened MR that GitLab hasn't computed a diff for yet). The plan says the script should handle the manual-trigger path cleanly; a slightly more accurate message like `"diff_refs not yet computed or MR unavailable"` would reduce confusion during first-exercise debugging.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281912864 -->
<!-- glab-discussion: dd2dee4c4c698a4c59771c73f4c282b4d0ecf044 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `scripts/next_mr_number.sh:49` (2026-04-24 03:23 UTC) [open]

**[follow-up]** `glab api` without `--paginate` returns at most the default page size (typically 20, not 1), but `per_page=1` is passed in the query string so this should still work. The concern is that `sort=desc` without `order_by` defaults to `created_at` order per the GitLab docs, which equals iid order only if no MRs were ever manually re-ordered or imported — an assumption the code comment already acknowledges. No change needed, but the comment could note this assumption explicitly so a future reader doesn't silently break it by, e.g., importing MRs from another project.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281912873 -->
<!-- glab-discussion: fa2ef008d51595f08c0ffc6dee5ce1d61abcd94b -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 — (2026-04-24 03:23 UTC) [open]

**[follow-up]** `scripts/next_mr_number.sh:49` — `glab api` without `--paginate` returns at most the default page size (typically 20, not 1), but `per_page=1` is passed in the query string so this should still work. The concern is that `sort=desc` without `order_by` defaults to `created_at` order per the GitLab docs, which equals iid order only if no MRs were ever manually re-ordered or imported — an assumption the code comment already acknowledges. No change needed, but the comment could note this assumption explicitly so a future reader doesn't silently break it by, e.g., importing MRs from another project.

*(inline anchor rejected by GitLab: 500)*

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3281934388 -->
<!-- glab-discussion: 1366f8b3b55d2e960580d8794fbf47bfdccd50c8 -->
#### ↳ cmk (2026-04-24 03:34 UTC) [open]

Fixed (9474bab) — reordered the guard to lead with `CI_MERGE_REQUEST_IID` and added a comment explaining that `CI_COMMIT_SHA` is set in every pipeline and isn't a discriminator.

<!-- glab-id: 3281934603 -->
<!-- glab-discussion: d18dd45a857a1a376e34e33015e3160bd4e91d5c -->
#### ↳ cmk (2026-04-24 03:35 UTC) [open]

Fixed (9474bab) — the message now covers the "diff_refs not yet computed" case alongside closed/unavailable, with a note to retry if it's a fresh MR.

<!-- glab-id: 3281934854 -->
<!-- glab-discussion: dd2dee4c4c698a4c59771c73f4c282b4d0ecf044 -->
#### ↳ cmk (2026-04-24 03:35 UTC) [open]

Fixed (9474bab) — comment expanded to document the iid-monotonicity assumption explicitly and call out the "imported MRs may break it" scenario as a revisit trigger.

<!-- glab-id: 3281935216 -->
<!-- glab-discussion: fa2ef008d51595f08c0ffc6dee5ce1d61abcd94b -->
#### ↳ cmk (2026-04-24 03:35 UTC) [open]

Duplicate of the inline thread on `scripts/next_mr_number.sh:49` above (this comment was the general-comment fallback when GitLab rejected the inline anchor with 500). Same fix applies — see 9474bab.
