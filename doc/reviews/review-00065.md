# MR !65 — Plan 40: README + CI follow-ups for Plan 39 Kani proof tree

## Summary

- Adds a one-sentence mention of Kani SMT verification at the top of
  `README.md` (right after the existing project description) plus a
  full `## SMT verification (Kani)` subsection under `# Testing`.
  The subsection explains the proof tree's location and `#[cfg(kani)]`
  gating, the headline f64 → f32 ULP-walk bound (`≤ 2 iterations for
  every finite non-NaN f64`), the family-level coverage breakdown
  (1154 harnesses across integer narrowing / widening / saturating /
  NonZero / Q-format / iso / float walking), out-of-scope items
  (time / addr / full float Galois / composed Conns), and the
  three-line run sequence.
- Adds a new `kani:` job to `.gitlab-ci.yml` in the `audit` stage
  alongside `deny` / `gitleaks` / `claude-review`. **Advisory-only**
  (`allow_failure: true`), **tag-push + scheduled + manual-trigger
  only** (the full sweep is fast but the cold-cache `cargo kani
  setup` downloads ~1 GB; per-MR is too costly for the marginal
  value over local `cargo kani`). Uses `image: rust:1.92` because
  the project's pinned 1.85 cannot install kani-verifier 0.67+
  (transitive `home 0.5.12+` requires 1.88+); Kani's own pinned
  nightly toolchain runs the harnesses.
- No production code changes. Plan 40 documenting the
  recommendations-from-plan-39 scope is in
  `doc/plans/plan-2026-05-06-03.md`.

## Test plan

- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `cargo test --workspace --quiet` — 57 passed / 0 failed / 9
      ignored, unchanged from baseline.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `scripts/check-pii.sh` — exits 0.
- [ ] `scripts/check_readme_mirror.sh` — exits 0 (no headline-Conn
      doctest mirror was touched; the new subsection is informational
      prose, not a mirrored doctest).
- [ ] `glab ci lint` — `✓ CI/CD YAML is valid!`.
- [ ] Manual `glab ci run --variables KANI_RUN=1 --branch
      sprint/kani-followups` after merge → confirms the new
      `kani:` job actually installs Kani, sets up the toolchain, and
      runs the full proof tree green on a CI runner.
