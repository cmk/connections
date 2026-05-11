# MR !71 — Tighten review prompts so reviewers stop ratifying author framing

## Summary

- Restructure the `/sprint-review` reviewer prompt into two passes —
  cold trait-claim audit first, plan-aware review second — so the
  author's plan can no longer pre-frame the diff.
- Update the GitLab `claude-review` bot's `SYSTEM` prompt with the same
  trait-claim audit and test-exception escalation rule; remove the
  "don't speculate about alternate `ceil` / `floor`" guard that
  dampened soundness scrutiny on MR !70.
- Add **Pattern 9** to `doc/reviews/review-calibration.md` (the
  `iso!`-claims-`<=`-but-test-uses-`total_cmp` shape that MR !70 hit)
  and a documented-blind-spot disclaimer in `CLAUDE.md` so the
  reviewers are positioned as advisory, not a soundness gate.

## Test plan

- [x] `cargo test --workspace` — should pass (no Rust changes).
- [x] `cargo clippy --all-targets -- -D warnings` — should pass.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features testing --document-private-items` — pre-push hook covers this.
- [x] Manual read-through of `.claude/commands/sprint-review.md` Step 4 — confirm Pass 1 / Pass 2 ordering and that the plan section sits between the two passes, not before Pass 1.
- [x] `grep -n "Trait-claim audit" scripts/claude_review.py` — confirm the new section is in the `SYSTEM` constant.
- [x] `grep -n "Pattern 9" doc/reviews/review-calibration.md` — confirm the new pattern landed.
- [x] `grep -n "Documented blind spot" CLAUDE.md` — confirm the disclaimer landed.
- [ ] **Follow-up (deferred):** Manual smoke test — rerun
  `claude_review.py` against MR !70's pre-merge diff and confirm a
  `must-fix` finding citing the `iso!`/`*_total` mismatch shape.
