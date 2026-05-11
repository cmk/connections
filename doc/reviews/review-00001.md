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

<!-- gh-id: 3217542423 -->
### Copilot on [`scripts/git_autosquash_finalize.sh:49`](https://github.com/cmk/connections/pull/1#discussion_r3217542423) (2026-05-11 09:00 UTC)

`git_autosquash_finalize.sh` invokes `scripts/check_layers.sh`, but that script is not present in this repo, so finalization will fail every time. Either add `scripts/check_layers.sh` (and keep it in sync with the intended checks) or remove this step and align the remaining gates with `.githooks/pre-push` / CI (notably the feature set and rustdoc gate).

<!-- gh-id: 3217542489 -->
### Copilot on [`.claude/commands/pr-reply.md:195`](https://github.com/cmk/connections/pull/1#discussion_r3217542489) (2026-05-11 09:00 UTC)

This section describes pre-commit/pre-push hooks that don’t match the repo’s actual hooks: `.githooks/pre-commit` runs `cargo fmt`, `scripts/check_pii.sh`, and `scripts/check_readme_mirror.sh`, and `.githooks/pre-push` runs feature-gated `cargo test`, `cargo clippy`, and `cargo doc`. Also, `scripts/check_layers.sh` is referenced here but does not exist. Please update this text to reflect the real hook chain (or add the missing script if it’s intended).


<!-- gh-id: 4262069783 -->
### copilot-pull-request-reviewer[bot] — COMMENTED ([2026-05-11 09:00 UTC](https://github.com/cmk/connections/pull/1#pullrequestreview-4262069783))

## Pull request overview

Ports the repository’s developer workflow and automation surface from GitLab to GitHub, aligning CI, local tooling, and documentation with the `template-rust` GitHub-based process while bumping the MSRV to Rust 1.88.

**Changes:**
- Replace GitLab CI/review tooling (`glab`, `.gitlab-ci.yml`, MR scripts) with GitHub equivalents (`gh`, `.github/workflows/*`, PR scripts).
- Add/refresh local workflow scripts and git hooks for PR review, replies, state detection, autosquash finalization, and guarded merging.
- Update crate metadata/docs for the GitHub move and bump MSRV (including a temporary `time` version pin).

### Reviewed changes

Copilot reviewed 52 out of 54 changed files in this pull request and generated 4 comments.

<details>
<summary>Show a summary per file</summary>

| File | Description |
| ---- | ----------- |
| src/core/char.rs | Minor test formatting update (Rust format string capture). |
| scripts/workflow_state.sh | New helper to infer local workflow FSM state (best-effort, non-mutating). |
| scripts/template_sync.sh | New template-rust drift check/sync script (verbatim/surgical manifests). |
| scripts/review_path.sh | Removed GitLab MR review-path helper (superseded by PR tooling). |
| scripts/reply_review.py | Removed GitLab MR reply poster. |
| scripts/pull_reviews.py | Removed GitLab MR discussion mirroring script. |
| scripts/pr_review.sh | New local Tier-1 review runner integrating `codex review` into review docs. |
| scripts/pr_request.sh | New “predict next PR/issue number” helper via `gh api`. |
| scripts/pr_report.py | New PR report tool (review path/body extraction + GitHub review/comment mirroring). |
| scripts/pr_reply.py | New GitHub PR review-comment reply poster via `gh api`. |
| scripts/next_mr_number.sh | Removed GitLab “next MR iid” helper. |
| scripts/github_client.py | New shared helper for GH repo auto-detection and PR existence verification. |
| scripts/git_squash.sh | Fix usage comment to match actual script name. |
| scripts/git_merge.sh | New guard wrapper around `gh pr merge` to prevent merging with unpushed/fixup state. |
| scripts/git_autosquash_finalize.sh | New pre-merge autosquash + gate runner + force-with-lease push. |
| scripts/extract_mr_body.sh | Removed GitLab MR body extractor (replaced by `pr_report.py body`). |
| scripts/claude_review.py | Removed GitLab CI Claude reviewer integration. |
| scripts/ci-select-tests.sh | Removed GitLab-specific selective nextest runner. |
| scripts/check-pii.sh | Removed legacy PII hook script name (replaced by underscore version). |
| scripts/check_pii.sh | New/expanded PII+secret scanning script (staged diff + optional tree scan). |
| scripts/_glab.py | Removed GitLab CLI helper module. |
| rust-toolchain.toml | Bump pinned toolchain channel to 1.88. |
| README.md | Update CI badge + links from GitLab Pages/URLs to GitHub equivalents; MSRV update. |
| doc/workflow.md | Update workflow FSM diagrams/prose from GitLab MR flow to GitHub PR flow. |
| doc/reviews/review-00001.md | Add PR review record seeded with PR summary/test plan/deferred items. |
| deny.toml | Update comment referencing CI location to GitHub workflow. |
| CODEOWNERS | Remove GitLab CODEOWNERS file. |
| .github/CODEOWNERS | Add GitHub CODEOWNERS file in the correct location. |
| Cargo.toml | Update MSRV, repository/homepage URLs, packaging excludes, and pin `time` `<0.3.46`. |
| AGENTS.md | Add consolidated agent/workflow conventions (renamed from CLAUDE.md per PR description). |
| .pii-allow | Add allowlist patterns for CI runner home paths. |
| .gitleaks.toml | Update allowlist path references to new `check_pii.sh` filename. |
| .gitlab-ci.yml | Remove GitLab CI configuration. |
| .gitignore | Rename ignored watch-state directory from `.watch-mr/` to `.pr-watch/`. |
| .github/workflows/ci.yml | New GitHub Actions CI (fmt/clippy, tests, docs; deny/secrets only on main pushes). |
| .github/workflows/doc-nightly.yml | New scheduled/manual nightly all-features rustdoc job. |
| .github/workflows/kani.yml | New scheduled/tag/manual Kani job (allow-failure). |
| .github/workflows/pages.yml | New GitHub Pages rustdoc build + deploy workflow. |
| .github/pull_request_template.md | Update PR template checklist for GitHub workflow. |
| .github/instructions/docs-review.instructions.md | Add Copilot documentation-review instructions (doc/**/*.md). |
| .githooks/pre-commit | Update pre-commit gate (fmt + PII + README mirror). |
| .githooks/pre-push | Update pre-push gate (tests + clippy + doc; skip on delete-only/no-op push). |
| .config/nextest.toml | Remove nextest CI profile (GitHub CI now uses cargo test directly). |
| .claude/settings.json | Update Claude Code hook command chain to match renamed/updated scripts. |
| .claude/commands/watch-mr.md | Remove GitLab MR polling command. |
| .claude/commands/sprint-review.md | Remove GitLab-era local review orchestration command. |
| .claude/commands/reply-reviews.md | Remove GitLab-era reply/mirror/amend command. |
| .claude/commands/pull-reviews.md | Remove GitLab-era “pull reviews” command wrapper. |
| .claude/commands/pr-watch.md | Add GitHub PR polling + auto-fix/reply + push workflow command. |
| .claude/commands/pr-review.md | Add GitHub-era local review orchestration command (delegates to `scripts/pr_review.sh`). |
| .claude/commands/pr-report.md | Add GitHub-era “mirror PR reviews/comments into review doc” command wrapper. |
| .claude/commands/pr-reply.md | Add GitHub-era reply/mirror/fixup workflow command. |
</details>



<details>
<summary>Comments suppressed due to low confidence (1)</summary>

**.github/pull_request_template.md:15**
* This checklist item is factually incorrect: CI runs `cargo fmt --all -- --check` in the `clippy` job (see `.github/workflows/ci.yml`), so formatting failures are blocking. Please adjust the wording so contributors aren’t misled into thinking fmt is non-blocking.
</details>



---

💡 <a href="https://github.com/cmk/connections/new/main?filename=.github/instructions/*.instructions.md" class="Link--inTextBlock" target="_blank" rel="noopener noreferrer">Add Copilot custom instructions</a> for smarter, more guided reviews. <a href="https://docs.github.com/en/copilot/customizing-copilot/adding-repository-custom-instructions-for-github-copilot" class="Link--inTextBlock" target="_blank" rel="noopener noreferrer">Learn how to get started</a>.

<!-- gh-id: 3217542528 -->
### Copilot on [`.claude/commands/pr-review.md:154`](https://github.com/cmk/connections/pull/1#discussion_r3217542528) (2026-05-11 09:00 UTC)

This section claims the hooks run `scripts/check_layers.sh` and `cargo test --workspace`, but the actual hooks differ (`scripts/check_readme_mirror.sh` in pre-commit; feature-gated tests + rustdoc in pre-push), and `scripts/check_layers.sh` is not present. Please sync this text with `.githooks/pre-commit`/`.githooks/pre-push` (or add the missing script if intended).


<!-- gh-id: 3217542571 -->
### Copilot on [`.claude/commands/pr-watch.md:189`](https://github.com/cmk/connections/pull/1#discussion_r3217542571) (2026-05-11 09:00 UTC)

This section claims the hooks run `scripts/check_layers.sh` and `cargo test --workspace`, but the actual hooks differ (`scripts/check_readme_mirror.sh` in pre-commit; feature-gated tests + rustdoc in pre-push), and `scripts/check_layers.sh` is not present. Please sync this text with `.githooks/pre-commit`/`.githooks/pre-push` (or add the missing script if intended).


<!-- gh-id: 3217677988 -->
#### ↳ cmk ([2026-05-11 09:22 UTC](https://github.com/cmk/connections/pull/1#discussion_r3217677988))

Fixed in upcoming fixup commit. `scripts/git_autosquash_finalize.sh` now drops the `check_layers.sh` step, swaps `--workspace` for the connections feature set, adds `scripts/check_readme_mirror.sh`, and adds the `RUSTDOCFLAGS=-D warnings cargo doc` gate so the chain matches `.githooks/pre-push` and CI's `clippy` / `test` / `doc` jobs.

<!-- gh-id: 3217679480 -->
#### ↳ cmk ([2026-05-11 09:22 UTC](https://github.com/cmk/connections/pull/1#discussion_r3217679480))

Fixed: the description now reads `cargo fmt --check`, `scripts/check_pii.sh`, `scripts/check_readme_mirror.sh` for pre-commit and `cargo test --features fixed,time,hifi,testing,macros` + clippy + `cargo doc` with `RUSTDOCFLAGS=-D warnings` for pre-push, matching `.githooks/`. The `scripts/check_layers.sh` reference was acceptable cosmetic drift in the port plan (to keep template-rust byte-identity for future sync) but it misled the reader, so fixing here.

<!-- gh-id: 3217679793 -->
#### ↳ cmk ([2026-05-11 09:22 UTC](https://github.com/cmk/connections/pull/1#discussion_r3217679793))

Fixed in the same fixup commit as the pr-reply.md / pr-watch.md sibling threads — same drift, same correction.

<!-- gh-id: 3217680081 -->
#### ↳ cmk ([2026-05-11 09:22 UTC](https://github.com/cmk/connections/pull/1#discussion_r3217680081))

Fixed in the same fixup commit as the pr-reply.md / pr-review.md sibling threads — same drift, same correction.
