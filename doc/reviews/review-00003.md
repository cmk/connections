# PR #3 — Archive GitLab-era reviews under `doc/reviews/gitlab/`

## Summary

- Move the 75 frozen `review-00002.md..review-00098.md` files into
  `doc/reviews/gitlab/` so GitHub-issued PR numbers can reclaim
  `doc/reviews/review-NNNNN.md` without colliding with the GitLab
  audit trail. `review-00000.md` (sentinel) and the new GitHub
  `review-00001.md` stay at the top level.
- Update `AGENTS.md`'s historical note to point at the new path.
- Add a narrow `.pii-allow` regex for one historical line that quotes
  an absolute home-directory path; content is unchanged on the rename
  but `scripts/check_pii.sh` diff-walks the new path as a pure add.

## Test plan

- `cargo fmt --all -- --check`
- `scripts/check_pii.sh`
- `scripts/check_readme_mirror.sh`
- `cargo test --features fixed,time,hifi,testing,macros`
- `cargo clippy --all-targets -- -D warnings`
- `RUSTDOCFLAGS=-D warnings cargo doc --no-deps --features fixed,testing,macros,time --document-private-items`
- Confirm `scripts/pr_report.py path` predicts `doc/reviews/review-00003.md` (next-PR-number prediction does not regress after the move; the `doc/reviews/review-*.md` pathspec in `scripts/pr_review.sh` and `scripts/workflow_state.sh` only matches the top level).
