---
name: hygiene
day: wed
paths: [src/]
cadence: monthly
---
You are doing a quick mechanical hygiene sweep of the connections
repo. None of these findings block merges — they're cleanup items
that accumulate slowly and are worth batching.

Read first: CLAUDE.md (esp. the "Don't add error handling, fallbacks,
or validation for scenarios that can't happen" and "Avoid backwards-
compatibility hacks like renaming unused _vars" guidance).

Mechanical pass only — no judgment calls:

1. `#[allow(dead_code)]` on `pub` items.
   Pattern: `#[allow(dead_code)]` immediately preceding `pub fn`,
   `pub const`, `pub struct`, `pub enum`. Public dead code is
   contradictory — either the item is used (allow is wrong) or it
   isn't (item should be removed). Reference precedent:
   review-00011.

2. `#[allow(unused_imports)]` that have outlived their reason.
   For every `#[allow(unused_imports)]`, check if removing it would
   produce a warning. If not, the suppression is dead.
   Note: `#[cfg(test)] use ...` patterns commonly need this — check
   for the cfg attr nearby and skip those.

3. `_var` parameters that should be removed entirely.
   Pattern: function parameters named `_var` (leading underscore)
   that don't have a documented "kept for trait signature" or "kept
   for ABI" reason in a nearby comment. Per CLAUDE.md "Avoid
   backwards-compatibility hacks like renaming unused _vars", these
   should be deleted, not silenced.

4. `// removed: ...` / `// was: ...` comments left behind.
   Pattern: comments referencing deleted code. Per CLAUDE.md "no
   removed comments for removed code", these should be deleted.

5. Trailing TODOs without owner / issue / MR reference.
   Pattern: `TODO` or `FIXME` not followed by `(MR !N)`, `(issue
   N)`, `(@username)`, or a date string. Bare TODOs rot — assign
   them or delete them.

Output format: bulleted list, grouped by category, file:line each.
All findings are `[follow-up]` severity by default; do NOT use
`[must-fix]` in this audit.

If there are zero findings across all 5 categories: output exactly
the single line `no findings` and nothing else.
