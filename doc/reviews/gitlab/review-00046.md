# MR !46 — Add pre-push hook for cargo doc link check

## Summary

- Adds `.githooks/pre-push` that runs `RUSTDOCFLAGS=-D warnings cargo
  doc --no-deps --features testing --document-private-items` once per
  push, mirroring the CI `doc:` job. Catches broken intra-doc links
  before they leave the laptop.
- Pre-push (not pre-commit) so the cargo-doc cost is paid once per
  sprint instead of once per commit.
- Updates `.githooks/pre-commit` header and the CLAUDE.md "hooks"
  section to document the new Layer 3 alongside the existing Layer 1
  (Claude Code `PreToolUse`) and Layer 2 (`pre-commit`).

## Test plan

- [x] `.githooks/pre-push` runs cleanly on `origin/main` tree
- [x] Hook is executable (`chmod +x`)
- [ ] CI green
