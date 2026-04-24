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
