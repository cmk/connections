---
description: Fetch GitLab MR discussion notes for a merge request and append new ones chronologically to doc/reviews/review-NNNNN.md. Lower-level primitive — normally invoked by /reply-reviews, but usable standalone to refresh the doc before final push.
argument-hint: <mr-number>
---

# Pull Reviews — Fetch GitLab Comments to Local File

Fetch discussion notes from a GitLab MR and append new ones chronologically
to `doc/reviews/review-NNNNN.md`. The heavy lifting lives in
`scripts/pull_reviews.py`; this command is a thin wrapper around it.

**In the normal review-round workflow, `/reply-reviews` invokes this
internally** after posting replies, so you rarely run it by hand.
Standalone use is for: (a) refreshing `review-NNNNN.md` right before the
final pre-merge push to capture any trailing reviewer comments; or
(b) catching up after a round where someone else pushed review activity
to the MR.

---

## Step 1: Parse the MR number

The user provides an MR number (iid) as an argument (e.g., `/pull-reviews 17`).
Argument: `$ARGUMENTS`

If omitted, check if the current branch has an open MR:

```
glab mr view -F json | jq .iid
```

If no MR is found, ask the user for the number.

## Step 2: Run the script

```
scripts/pull_reviews.py <N>
```

The script handles everything: fetches discussions and their notes by
iterating `?per_page=100&page=N` explicitly against the GitLab API,
flattens discussions into a chronological note stream, de-dupes via set
membership on `<!-- glab-id: -->` markers, records the parent discussion
for each note as `<!-- glab-discussion: -->` (used by `reply_review.py`
to target replies), and creates `review-NNNNN.md` with a
`# MR !N — <title>` header if it doesn't exist.

The script is idempotent: any note whose `glab-id` is already present in
the file is skipped. Note ids are globally unique within a project, so
one marker pool is sufficient (this differs from GitHub, where reviews
and inline comments draw IDs from separate sequences).

## Step 3: Let the file ride with the next fix commit

The review file is not committed on its own. It rides with the **next
review round's fix commit** — the commit that addresses the comments
you just pulled.

The `/reply-reviews` command enforces this: it posts replies, runs
`pull_reviews.py`, and `git commit --amend`s the mutated doc into the
pre-push fix commit, so one push delivers everything in order.

If you invoked `/pull-reviews` standalone (no paired reply round), the
file stays modified-but-uncommitted on disk. A later `/reply-reviews`
will pick it up and fold it in. Do **not** open a standalone
`doc: update review-NNNNN.md` commit just to land it — that forces a CI
round-trip for no code change and was the ordering bug the unified
`/reply-reviews` was designed to eliminate.

If there were no new items (script reported `no new items`), there is
nothing staged and nothing to do.

## Step 4: Report

Print a one-paragraph summary: how many new items were appended and
the path to the review file. The script's own stdout line —
`MR !N: appended K items -> <path>` — already gives you both, so you
can pipe it through verbatim if that's easier.

---

## Format contract (for reference / debugging)

The script writes three block shapes. If you're editing the file by hand
or extending the script, preserve these:

Top-level note with no code location (review body / general comment):

```markdown
<!-- glab-id: {id} -->
<!-- glab-discussion: {discussion_id} -->
### {user} — ({YYYY-MM-DD HH:MM UTC}){status}

{body}
```

Top-level inline note. The `:line` suffix is omitted when the GitLab
API returns `line: null` (outdated diff comments or file-level comments):

```markdown
<!-- glab-id: {id} -->
<!-- glab-discussion: {discussion_id} -->
### {user} on `{path}` ({YYYY-MM-DD HH:MM UTC}){status}
### {user} on `{path}:{line}` ({YYYY-MM-DD HH:MM UTC}){status}

{body}
```

Reply (second or later note in a discussion):

```markdown
<!-- glab-id: {id} -->
<!-- glab-discussion: {discussion_id} -->
#### ↳ {user} ({YYYY-MM-DD HH:MM UTC}){status}

{body}
```

`{status}` is ` [open]` or ` [resolved]` when the discussion is
resolvable (inline threads); empty otherwise.

## Notes

- **The script does not auto-commit.** The file rides with the next
  round's fix commit (see Step 3); don't land a standalone `doc:`
  commit just to attach the audit trail.
- **Idempotent** via set membership on `<!-- glab-id: -->` markers.
  Safe to re-run.
- **Chronological, not grouped.** Items are appended in posted order
  (by `created_at`). Replies are only indicated by `↳` formatting based
  on their position inside a discussion; they are not guaranteed to be
  adjacent to their parent in the file — other notes posted in between
  will interleave.
