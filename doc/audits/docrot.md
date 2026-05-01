---
name: docrot
day: thu
paths: [src/, doc/, README.md, CHANGELOG.md]
---
You are auditing the connections repo for documentation rot:
forward-looking prose that describes a future state that's now the
present, references to renamed/deleted items, and cross-references
that no longer resolve.

Read first:
- CLAUDE.md.
- doc/reviews/review-calibration.md.

Mechanical pass:

1. Forward-looking prose that's now stale.
   Pattern in any committed `///` doc-comment, `//!` module doc, or
   `.md` file under doc/ (excluding plan/review/chat archives — see
   anti-themes):
     - "will land in [a-z]"
     - "to be added"
     - "TODO" / "FIXME" without an issue / MR / plan reference
     - "will be" followed by future-tense verb
     - "deferred to" without a follow-up reference
   For each, run `git log -p --follow <file>` and check whether the
   referenced future event has already happened. If yes: the prose
   is stale (must-fix). If unclear: flag as follow-up for human
   triage.

2. Stale path references in source comments.
   Patterns:
     - References in `// ...` comments to `tests/<name>.rs` or
       `src/<path>` — verify the path exists at the cited location.
       Example precedent: 5 references to
       `tests/conn_fixed_u*_galois.rs` were stale because the actual
       files lived at `tests/fixed_u*_galois.rs` (cleaned up in
       Plan 33).
     - References to functions / types / constants by name — verify
       the symbol still exists with that name (`grep -rn 'fn <name>'
       src/` or similar). Renames in this codebase are common
       (Plan 25/29/32 all renamed surfaces); doc comments often lag.
   Severity: follow-up.

3. Broken intra-doc links (rustdoc `[`Item`]` syntax).
   This is partially covered by the pre-push hook
   (`.githooks/pre-push` runs `RUSTDOCFLAGS=-D warnings cargo doc
   --no-deps`). Check that hook is still active by reading
   `.githooks/pre-push` and confirming the rustdoc step. If absent
   or weakened, that itself is a must-fix.

4. CHANGELOG entries with broken back-references.
   Read `CHANGELOG.md`. For every reference to an MR (`MR !N`), file
   path, function name, or feature gate, verify the reference still
   resolves. Flag anything that doesn't.
   Severity: follow-up.

Judgment pass (only if mechanical found nothing):

5. Comments that describe behavior the code no longer has.
   Walk every doc comment on `pub` items in src/. For each, briefly
   evaluate whether the documented behavior matches the body. Flag
   only clear divergences (not stylistic differences).

6. README mirror drift not caught by `scripts/check_readme_mirror.sh`.
   The script catches byte-identical mirrors of doctest blocks; it
   doesn't catch *prose* in README that no longer matches src docs.
   Sample 3-5 sections of README.md against the corresponding
   src/<...>.rs module docs and flag mismatches.

Output format:
- One section per category that has findings.
- Use the exact severity labels `[must-fix]` and `[follow-up]`.
- Each finding: file:line, the offending excerpt (≤5 lines), the
  rule it violates (cite CLAUDE.md / plan / doc), and the bug class
  it enables (1 sentence).
- If there are zero findings across all 6 checks: output exactly the
  single line `no findings` and nothing else.

Anti-themes:
- Plan files (`doc/plans/plan-*.md`) and review files
  (`doc/reviews/review-*.md`) are historical records — stale prose
  in these is intentional (audit trail). Skip them entirely.
- Chat logs (`doc/chats/*.md`) — same, skip.
- The `Deferred` section of any plan is supposed to describe future
  state by definition. Don't flag.
