# PR #4 — fix(ci): Force nightly toolchain in doc-nightly workflow

<!-- gh-id: 4285611139 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-05-13 21:48 UTC](https://github.com/cmk/connections/pull/4#pullrequestreview-4285611139))

## Pull request overview

Fixes the `doc-all-features-nightly` workflow which was failing because `rust-toolchain.toml` (channel "1.88") overrode the nightly toolchain installed by `dtolnay/rust-toolchain@nightly`. Using the `+nightly` shortcut takes precedence over `rust-toolchain.toml`, ensuring the doc build runs on nightly as intended.

**Changes:**
- Add `+nightly` shortcut to the `cargo doc` invocation in the doc-nightly workflow.




