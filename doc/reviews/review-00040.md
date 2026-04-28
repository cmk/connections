# Review 00040 — Plan 26: make cargo fmt pre-commit step blocking

## Summary

- Flips `.claude/settings.json`'s `cargo fmt --all -- --check` step
  from a non-blocking warning (`{ … || echo '[warn] …'; }`) to a
  hard block, matching the other quality gates. Plan 25 / MR !39 hit
  a real CI fmt failure that local tooling let through; this lands
  the safety net so it can't recur.
- Folds in two adjacent fixes: drops a stale `F064B016` entry from
  `scripts/readme_mirrors.txt` (manifest pointed at a long-removed
  path `src/conn/float/f64.rs` and a Conn const that no longer
  exists), and updates `CLAUDE.md` §Pre-commit hook to describe all
  five steps with their blocking semantics — the prior list named
  only four.

## Test plan

- [x] `cargo fmt --all -- --check` clean.
- [x] `cargo build` clean.
- [x] `cargo test --workspace` clean (no Conn-shape changes; this
      sprint touches workflow infra only).
- [x] `cargo clippy --all-targets -- -D warnings` clean.
- [x] `scripts/check_readme_mirror.sh` exits 0 (manifest reduces to
      header-comments-only post-T2).
- [x] `.claude/settings.json` parses as valid JSON.
- [x] Regression probe: a manually-injected fmt drift in
      `src/conn.rs` (extra whitespace after `pub struct`) makes
      `cargo fmt --all -- --check` exit 1. File restored before
      commit; never staged.
- [x] Full pre-commit chain (`cargo fmt && check-pii &&
      check_readme_mirror && cargo test && cargo clippy`) returns 0
      on a clean tree.
