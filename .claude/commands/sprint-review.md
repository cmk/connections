---
description: Tier-1 local pre-push code review. Spawns an independent reviewer agent to examine the branch diff against origin/main and writes the review to doc/reviews/review-NNNNN.md.
argument-hint: (no args)
---

# Sprint Review — Tier 1 (Local)

You are orchestrating a **local, pre-push** code review. This is Tier 1 of
a two-tier system:

- **Tier 1 (this command):** Independent agent reviews `origin/main...HEAD` locally.
  Gate before pushing.
- **Tier 2 (GitLab):** After push, CI runs the pipeline in
  `.gitlab-ci.yml` (fmt, clippy, test, deny, gitleaks). GitLab Duo
  and/or a human reviewer post review comments on the MR.

Your job: gather inputs, launch the reviewer, place the output, then help
the user push if the review passes.

---

## Step 0: Autosquash any pending fixups

Per CLAUDE.md, CI-repair commits are made as `--fixup`s and must be
collapsed before review/push. Refresh the remote-tracking ref first so
the check isn't against a stale base, then scan for fixups:

```
git fetch --quiet origin main
git -c color.ui=never log --oneline origin/main..HEAD | grep -E '^[0-9a-f]+ fixup!' || true
```

If any fixups exist, run `scripts/autosquash.sh` to collapse them.
Abort if the working tree is dirty (the script checks this). After
autosquash, re-run the fixup check to confirm the branch is clean.

## Step 1: Identify the plan (optional)

Check for a plan doc associated with this branch:

```
ls -t doc/plans/plan-*.md | head -3
```

If a plan exists and is clearly related to the branch work (check dates,
topic), read it. You'll pass its text to the reviewer.

If no plan exists or none is relevant, that's fine — the review proceeds
in **code-only mode** (no plan-conformance section).

## Step 2: Collect the diff and verify prerequisites

The review always targets the current branch against `origin/main`.
Refresh the ref first so the base isn't stale:

```
git fetch --quiet origin main
git diff origin/main...HEAD
git log origin/main..HEAD --oneline
```

If the branch has not diverged from `origin/main`, abort with a
message — there's nothing to review.

**Verify the review file exists.** `/sprint-review` appends to a
file created by TDD step 7; it never creates the file itself. Get
its path:

- If an MR already exists for this branch:
  ```
  scripts/review_path.sh "$(glab mr view -F json | jq .iid)"
  ```
- Otherwise (the normal pre-push case):
  ```
  scripts/review_path.sh
  ```

`review_path.sh` predicts (or accepts) the MR iid and emits the
zero-padded filename — no need to compose the path by hand. Then
confirm the returned path exists **and contains a `## Summary`
section**. If either is missing, abort and tell the user to run TDD
step 7 (finalize plan + draft MR description). Do not create the
file and do not proceed to the reviewer — the MR description belongs
in that commit, not as a post-hoc fabrication by this command.

## Step 3: Gather context

Read these files and include them in the reviewer prompt:

- `CLAUDE.md` — repo conventions, workspace layout, TDD workflow, commit
  style, feature-gate conventions
- `doc/reviews/review-calibration.md` — if it exists, include as few-shot
  examples. If absent, skip (the reviewer prompt has built-in guidance).

## Step 4: Launch the reviewer

Spawn a **new agent** with `subagent_type: "feature-dev:code-reviewer"` and
`model: "sonnet"`.

The prompt must be self-contained and ordered so the reviewer reads
the diff cold before the plan can frame their analysis. Include, in
this order:

1. The full diff
2. The commit log
3. The repo conventions from CLAUDE.md
4. Calibration examples from `doc/reviews/review-calibration.md` (if found)
5. **Pass 1** review instructions (cold, no plan)
6. The plan text (if found), labeled as Pass 2 input
7. **Pass 2** review instructions (plan-aware)

The plan ordering is deliberate: feeding the plan in alongside the
diff primes the reviewer to ratify the author's framing. The two-pass
structure was added after MR !70 — where both Claude reviewers
accepted a §Review note that "we use a weaker test predicate" as a
test deviation, missing that the type still claimed the unrelaxed
law. Pass 1 forces a cold trait-claim audit; Pass 2 surfaces
plan-vs-claim mismatches.

### Reviewer voice and calibration

The reviewer should write like a thorough human MR reviewer, not a checklist
robot. Good review comments share these qualities:

- **Cite the contract, then the violation.** When the plan says X and the code
  does Y, quote both. "The plan specifies `device = ["dep:tokio", ...]` as an
  optional feature gate (T1), but `Cargo.toml` lists tokio as unconditional."

- **Name the consequence.** Don't just say "this differs from the plan." Say
  what breaks: "This means `driver-motu` links tokio/russh/mdns despite only
  using HTTP+OSC, adding ~3s to clean builds."

- **Distinguish severity.** Some findings block the merge, others are
  improvement opportunities. Be explicit: "Must fix before merge" vs
  "Consider for a follow-up."

- **Don't pad.** If a section has no findings, one sentence: "All N planned
  tests are present and correctly gated." Don't invent concerns to fill space.

### Reviewer prompt template

~~~
You are reviewing code on a local feature branch before it is pushed to
GitLab. This is a pre-push quality gate — there is no MR yet. You are
reviewing the diff between `origin/main` and the branch HEAD.

You are an independent reviewer. You did not write this code and have no
context beyond what is provided here. Review what you see, not what you
assume. The author's framing — in the plan, in commit messages, in
comments — is one input, not a verdict. Your job is to challenge it
where the diff disagrees.

## Diff (origin/main...HEAD)

{diff}

## Commit log (origin/main..HEAD)

{commit log}

## Repo conventions

{CLAUDE.md contents}

{IF calibration examples exist:}
## Examples of high-quality review comments

{doc/reviews/review-calibration.md contents}

Match this style: cite the contract (doc, plan, or naming), show how the
code violates it, and name the consequence. When something is fine, one
sentence is enough. Don't invent concerns to fill space.
{END IF}

# Pass 1 — Cold review (no plan)

The sprint plan is **not** in your context yet. Do this pass on the
diff alone. The whole point is to reach an independent verdict before
the author's framing arrives.

## P1.A — Trait-claim audit (do this first, before anything else)

For every new or changed item in the diff that fits any of:

- a `pub const` of `Conn<_, _>` / `Conn<_, _, K>` type
- an `iso!`, `conn_l!`, `conn_r!`, `compose!`, or `triple!` macro invocation
- a new `impl` of any law-bearing trait (`Lattice`, `Heyting`,
  `Boolean`, `Ord`, `PartialOrd`, `Eq`, `PartialEq` where the impl is
  not derived)

write down, in this order:

1. **The contract.** Quote the type definition or trait doc — what
   law does this declaration claim? (e.g. `iso!` produces
   `ConnK<A, B>`, claiming `(ceil(a) ≤ b) == (a ≤ upper(b))` over `<=`
   on both sides.)
2. **The implementation.** Quote the closures, arms, or impl body.
3. **Consistency.** State whether (1) and (2) are consistent. If
   the impl satisfies the contract only on a subset of the input
   domain (NaN-free floats, finite ints, non-empty strings, …), say
   so explicitly and flag it `must-fix` unless the type itself was
   weakened to match.

A test renamed with a relaxation suffix (`*_total`, `*_relaxed`,
`*_partial`, `*_weak`) is a load-bearing signal: the author found the
strong predicate fails, and unless the type declaration was also
weakened, the type is now claiming a law its tests don't check.
That mismatch is `must-fix`, not a test-style nit.

## P1.B — Standard review (after the audit)

For each section, state what you found concretely. When something is wrong,
cite the specific file, line, and consequence. When something is fine, one
sentence is enough — don't pad.

### Commit Hygiene

- Does each commit leave the repo in a buildable, testable state?
- Are commit messages conventional (feat/fix/doc/test/task/debt prefix, optional scope)?
- Are commits reasonably atomic, or are unrelated changes mixed?

### Code Quality

- Does the code follow repo conventions (no unsafe, `#![forbid(unsafe_code)]`,
  lint config in Cargo.toml)?
- Are error messages specific enough to diagnose from a log line?
- Any dead code, redundant logic, or clippy-level issues?

### Test Coverage

**Property tests are the highest-priority check.**

- For any module that parses, encodes, or transforms data: are there
  property tests? If not, flag this as a gap.
- Do fixture-gated tests use `fixture_or_skip!` (return early when
  fixture is absent, don't panic, don't `#[ignore]`)?
- What edge cases do the tests miss? Be specific — "NaN vs ±∞ vs
  subnormal coverage in the f64↔f32 generator" is useful; "more tests
  would be good" is not.

### Risks

- TODOs, stubs, or placeholder implementations?
- Could any change break existing functionality in other modules?
- Security: path traversal in file operations? Command injection in
  shell-outs? Unsanitized input passed to subprocesses?
- New dependencies justified and maintained?

{IF plan exists:}
# Pass 2 — Plan-aware review (read the plan now)

## Sprint plan

{plan text}

## P2.A — Test-exception escalation

Scan the plan's Implementation, Verification, and §Review sections
for any of: "weaker predicate", "exclude", "saturate instead", "this
case is excluded", "deferred from", "exception", "use … instead of",
"relaxed", "total order analog", "skip on …".

For each occurrence, ask: **does the type declaration in the diff
still claim the unrelaxed law?** If yes, that is a P1 soundness bug,
not a test deviation. Promote your Pass 1 trait-claim audit findings
to `must-fix` if the plan's relaxation note matches. If the audit
already flagged it, cross-reference both findings in the report so
the reader sees the two-pass agreement.

## P2.B — Plan conformance

- Walk each task (T1, T2, ...) and each row in the Verification table:
  was it implemented?
- For each planned test, does a corresponding test exist in the diff?
- Is there code in the diff that wasn't in the plan? Justified emergent
  requirement, or undocumented scope creep?
- Were any features, config options, or feature gates described in the
  plan but absent from the implementation? Plans often specify build
  configuration that gets lost.

The plan is one input. If your Pass 1 findings disagree with what the
plan says is OK, report the disagreement — don't downgrade Pass 1.
{END IF}

# Recommendations

Separate into two lists:

**Must fix before push:**
- Issues that violate conventions, break tests, or introduce bugs.
- Trait-claim mismatches from P1.A (or P2.A escalations).

**Follow-up (future work):**
- Improvements that are acceptable now but should be tracked.

# Output format

Structure your review as markdown with the section headers above.
Include the trait-claim audit verbatim — even if every item is
consistent, the audit log is the artifact that proves you did it.
Be direct and specific. Cite file paths and line numbers. Keep the
total review under 500 lines. Prioritize by impact.
~~~

## Step 5: Place the output

Append (never overwrite) a dated section to the already-existing
`doc/reviews/review-NNNNN.md`, below the `## Summary` and any prior
review rounds:

```markdown
## Local review (YYYY-MM-DD)

**Branch:** <branch>
**Commits:** <count> (origin/main..<branch>)
**Reviewer:** Claude (sonnet, independent)

---

{reviewer output}
```

Then:

1. **Print a summary** to the conversation: how many must-fix items,
   how many follow-ups, and the path to the review file. One paragraph
   max.

2. **If zero must-fix items:**
   Tell the user the branch is clear to push. Offer to push and open
   the MR (but don't do it without confirmation). The MR-create
   command is:

   ```
   glab mr create --title "<title>" \
     --description "$(scripts/extract_mr_body.sh NNNNN)"
   ```

   This makes the GitLab description a direct copy of the `## Summary`
   section — the two can't drift. Remind the user that Tier 2 (CI +
   GitLab review) will run automatically on the MR.

3. **If must-fix items exist:**
   Stop. Do not push. Do not offer to fix the issues. The user reads
   the review and decides what to do next.
