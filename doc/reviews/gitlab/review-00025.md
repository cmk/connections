# MR !25 — crates.io publish prep

## Summary

Lands every blocker from the publish-readiness audit — 3 audits
(src structural, test coverage, repo metadata) plus an API-gap pass
plus the parallel-time-v2 reconcile. Establishes two project-wide
conventions on the way: per-crate module organization under
`conn::*` (`std`, `fixed`, `half`, `time`) and type-named filenames
(`i8.rs` not `i08.rs`), with placement precedence codified in
CLAUDE.md as **specific > general → right > left**.

The crate is publish-ready after this lands. `cargo publish
--dry-run --allow-dirty` packages 48 files / 142.8 KiB compressed;
`connections` is confirmed available on crates.io. Actual publish
is gated on flipping the GitLab project public so the `repository`
URL is reachable.

Highlights:

- **Metadata + LICENSE-MIT + docs.rs config** — Cargo.toml gets
  `repository`/`homepage`/`keywords`/`categories`/`readme` plus
  `[package.metadata.docs.rs]` (`all-features`, `--cfg docsrs`).
  `LICENSE-MIT` lands at the repo root.
- **Module reorganization (partial)** — `conn::fixed::decimal` →
  `conn::std::i64::decimal`; `conn::fixed::{i08,u08}` →
  `conn::fixed::{i8,u8}`; `src/property/mod.rs` →
  `src/property.rs`. Half-bridge extraction and the int/uint split
  into per-type modules are deferred (the latter handed off to the
  parallel missing-Conns sprint).
- **Test coverage backfill** — every `F064FD<N>` rung now drives
  the full 9-law battery (was only FD06 + FD12). +40 lib tests
  (1781 → 1821). The audit's float-Galois blocker turned out to be
  a false positive — the existing `conn::float::{f32,f64}` test
  modules already had the complete battery.
- **API hygiene** — `Conn::ceil`/`inner`/`floor` and the 14 cast
  free-fns get `#[must_use]`; `Conn` methods also get `#[inline]`
  to let LLVM optimize through the fn-pointer dispatch.
- **CI** — `deny` and `gitleaks` move to `main`-only / scheduled
  pipelines (no per-MR runs); a new `doc` job at the `check` stage
  runs `cargo doc --no-deps --all-features --document-private-items`
  with `RUSTDOCFLAGS="-D warnings"`. The 12 redundant rustdoc-link
  warnings the audit flagged are all fixed.
- **`conn::sample` removed** — audio-domain types moved to the
  downstream [`agogo`](https://gitlab.com/cmk/agogo) crate. Audit
  confirmed zero reverse-deps so the lift-out is clean.
- **`scripts/check_readme_mirror.sh`** — generalized from a
  hardcoded F064B016 check to a manifest-driven walk
  (`scripts/readme_mirrors.txt`), so future headline-Conn additions
  just append a row.
- **CHANGELOG.md** — 0.1.0 entry with the full surface, conventions,
  deferred items, and MSRV.

## Test plan

- [ ] CI green (fmt, clippy, test, doc).
- [ ] `cargo publish --dry-run --allow-dirty` clean locally
      (verified pre-push: 48 files / 142.8 KiB compressed).
- [ ] `cargo doc --no-deps --all-features --document-private-items`
      under `RUSTDOCFLAGS="-D warnings"` clean (verified pre-push).
- [ ] All 1821 lib tests + 252 integration + 29 doctests pass at
      every commit (verified by pre-commit hook on each landing).
- [ ] Confirm `repository` URL is reachable from a logged-out
      browser before `cargo publish` (Chris-driven post-merge).
- [ ] `cargo search connections` shows the name available
      (verified pre-push via crates.io API: HTTP 404, available).
- [ ] After merge: tag `v0.1.0`; run `cargo publish` for real.
