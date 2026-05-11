# PR #1 — Port connections from GitLab to GitHub

## Summary

- Port the `connections` repo from `gitlab.com/cmk/connections` to
  `github.com/cmk/connections`, replacing GitLab tooling with the
  GitHub-shaped equivalents synced from
  [`template-rust`](https://github.com/cmk/template-rust). The crate
  stays single-crate; full 469-commit history is preserved.
- Bump MSRV 1.85 → 1.88 (aligns with the ADAT ecosystem). At 1.88
  `cargo-deny` floats with `EmbarkStudios/cargo-deny-action@v2` without
  the CVSS-4.0-on-1.85 workaround. `time` is pinned `<0.3.46` because
  0.3.46 added a `year >= -9999` panic that the `arb_extended_offset_dt`
  proptest strategy trips on — clamping the generator is a deferred
  follow-up.
- New CI surface in `.github/workflows/`: `ci.yml` (split clippy / test
  / doc), `doc-nightly.yml` (scheduled all-features), `kani.yml`
  (allow-failure SMT proofs), `pages.yml` (GitHub Pages). `deny` and
  `secrets` gated to push-to-main only, matching the historical GitLab
  cadence. `claude-review` CI job is dropped — local `/pr-review` via
  `codex review` replaces it.
- `CLAUDE.md` → `AGENTS.md` (with `CLAUDE.md` as compatibility symlink),
  content-merged from template-rust's outline plus the connections-
  specific Conn-naming / module-organization / Conn-placement tables.

## Test plan

- `cargo +1.88 test --features fixed,time,hifi,testing,macros` green
  locally (1791 passing).
- `cargo +1.88 clippy --all-targets -- -D warnings` clean.
- `RUSTDOCFLAGS=-D warnings cargo +1.88 doc --no-deps --features
  fixed,testing,macros,time --document-private-items` clean.
- Local pre-commit + pre-push hook chains exercised on each commit
  (fmt, `check_pii.sh`, `check_readme_mirror.sh` for pre-commit; test
  + clippy + doc for pre-push).
- CI verification once this PR opens: confirm `clippy` / `test` / `doc`
  fire and pass; confirm `deny` / `secrets` / `pages` / `kani` /
  `doc-nightly` do **not** fire on the PR.
- Manual one-time: Settings → Pages → Source = "GitHub Actions".
- Post-merge: verify `cmk.github.io/connections/` resolves; verify
  `scripts/template_sync.sh` from `template-rust` reports only the
  expected surgical drift (AGENTS.md, Cargo.toml, rust-toolchain.toml,
  rustfmt.toml, deny.toml, .github/workflows/ci.yml).

## Deferred

- `time = ">=0.3, <0.3.46"` — float back to `0.3` after clamping
  `arb_extended_offset_dt` so generated dates with non-zero offsets
  don't normalize past `year >= -9999`.
- `doc/reviews/review-calibration.md` → `calibration.md` rename to
  match template's canonical filename (touches grep-able prose in
  `doc/audits/*.md`).
- Live `scripts/template_sync.sh` drift check against the post-cutover
  tree.
- Optional GitHub branch protection on `main` requiring `clippy` /
  `test` / `doc`.
