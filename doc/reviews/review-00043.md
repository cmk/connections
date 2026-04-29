# Review 00043 — Plan 28: port template-rust's Layer 2 git pre-commit hook

## Summary

- Adds `.githooks/pre-commit` — a git-side hook that runs the same
  fmt / pii / readme-mirror / test / clippy chain at git's standard
  pre-commit hook point (after staging, in the actual worktree),
  ported from `template-rust`. Connections previously had only the
  Claude Code `PreToolUse` hook (Layer 1), which by construction runs
  in Claude Code's session cwd — so an agent's `cd <worktree> && git
  commit -m "..."` had Layer 1's `cargo fmt` / `cargo clippy`
  checking the launch directory, not the worktree. Layer 2 closes
  that gap.
- Updates `CLAUDE.md` §Pre-commit hooks to describe the two-layer
  design and the per-clone activation step (`git config core.hooksPath
  .githooks`). Discovered while diagnosing MR !42's clippy CI failure
  — every Plan 23 / Plan 24 commit silently bypassed the local
  fmt / clippy / test gates because of this cwd issue.
- Initial diagnosis on this branch blamed Layer 1's matcher pattern
  (`Bash(git commit*)`) for missing compound commands; that fix was
  unnecessary (matchers DO fire on subcommands of compound Bash
  calls). The branch was reset and redone with the correct
  diagnosis. The plan's "Why MR !43 was rewritten" section captures
  the false-start.

## Test plan

- [x] `.claude/settings.json` unchanged — Layer 1 was correct as-is.
- [x] `.githooks/pre-commit` is executable (`-rwxr-xr-x`) and runs
      the same five-step chain as Layer 1.
- [x] `git config core.hooksPath .githooks` activates Layer 2; this
      sprint's own commits go through it (verifies the hook works
      end-to-end before merge).
- [x] CLAUDE.md describes both layers + activation.
- [ ] Empirical verification on a fresh clone deferred to next
      sprint — this sprint validates locally where `core.hooksPath`
      is set.
