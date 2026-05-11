# MR !77 — Guard MR review reply workflow

## Summary

- Require MR review replies to flow through `/pull-reviews` and
  `/reply-reviews`, with raw `glab` posting treated as justified
  fallback-only behavior.
- Harden `scripts/reply_review.py` so Markdown-sensitive inline bodies
  are refused by default, while preserving stdin and adding
  `--body-file` for prepared replies.
- Document the corrected review-round transition: post through the
  script, mirror, verify the mirrored body, amend into the unpushed fix
  commit, then push once.
- Add a mandatory pre-edit worktree check so the primary checkout stays
  clean for humans and other agents.

## Test plan

- [x] `scripts/reply_review.py --help`.
- [x] Non-network parser smoke tests for stdin, `--body-file`, and
  inline-body refusal.
- [x] `python3 -m py_compile scripts/reply_review.py scripts/pull_reviews.py scripts/_glab.py`.
- [x] `cargo fmt --all -- --check`.
- [x] `cargo test --workspace --quiet`.
- [x] Manual documentation inspection for the required ordering and no
  unsafe inline Markdown examples.
- [x] Manual documentation inspection for the shared-checkout worktree
  preflight.
