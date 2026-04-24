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
