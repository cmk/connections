# MR !76 — Reduce GitLab CI usage and align rustdoc gates

## Summary

- Trim GitLab CI usage by folding `fmt` into `clippy`, adding
  interruptible / auto-cancel behavior, and skipping Rust jobs for
  docs-only and review-only MRs while keeping `README.md` changes in
  the Rust/doc/test gate.
- Keep post-merge `main` coverage conservative: `deny`, `gitleaks`,
  and strict Pages still run for landed changes, and direct
  source-impacting `main` pushes still run folded format+clippy and
  tests.
- Align CI, Pages, and pre-push rustdoc validation with the stable
  docs.rs feature surface: `byte,testing,macros` plus
  `--document-private-items`.

## Test plan

- [x] `glab ci lint` — CI/CD YAML is valid.
- [x] `cargo fmt --all -- --check` — clean.
- [x] `scripts/check-pii.sh` — clean.
- [x] `scripts/check_readme_mirror.sh` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features byte,testing,macros --document-private-items` — clean.
- [x] `cargo test --workspace --quiet` — 1166 lib + compile-fail + integration/doc suites passed.
- [x] `cargo clippy --all-targets --quiet -- -D warnings` — clean.
- [x] `git diff --check` — clean.
