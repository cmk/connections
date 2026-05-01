# Recurring audits

Self-hosted audit harness for the connections repo. Five audits, one
master script, one early-exit gate. Cron-driven (no Anthropic
routine-budget consumption); per-audit prompts are markdown files
with YAML front-matter.

## Layout

```
doc/audits/
  README.md           — this file
  log.md              — append-only findings log (created on first run)
  proptest.md         — Mondays, weekly: generator/property relaxation
  docrot.md           — Thursdays, weekly: stale prose, dead refs
  coverage.md         — Tuesdays, biweekly: test coverage drift
  hygiene.md          — Wednesdays, monthly: cleanup sweep
  pii.md              — Fridays, monthly: secret/PII scan

scripts/
  audit.py            — orchestrator (calendar + dispatch + log)
  audit_state.sh      — early-exit gate (since-last/mark/last)
```

## How a run works

1. Cron fires `scripts/audit.py cron-tick` daily.
2. The script reads each `*.md` under `doc/audits/`, parses
   front-matter (name, day, paths, cadence), and decides which audits
   are due today.
3. For each due audit: it asks `audit_state.sh since-last <name>
   <paths>` whether anything has changed under the audit's path
   filter since the last successful run. If empty, skip.
4. If non-empty: invoke `claude -p <prompt>` with the audit body plus
   a "Files changed since last audit" preamble.
5. Capture stdout. If it's `no findings`, do nothing. Otherwise
   append a dated section to `log.md`.
6. Mark the audit's HEAD pin so the next run early-exits unless
   something else changes.

## Prompt format

Each audit lives in its own markdown file with YAML front-matter:

```markdown
---
name: proptest        # required; matches the filename stem
day: mon              # required; mon|tue|wed|thu|fri|sat|sun
paths: [src/, tests/] # required; pathspec for early-exit gate
cadence: weekly       # optional; weekly (default) | biweekly | monthly
---
<prompt body — handed to claude -p verbatim, with a file-list preamble>
```

Prompts must instruct the agent to output `no findings` on a clean
run (the harness greps for that exact string to decide whether to
append to the log).

## Cron entry

```
0 9 * * *  cd /path/to/connections && scripts/audit.py cron-tick
```

Fires daily at 9am. On no-due days, exits silently. On due days
where nothing changed under the audit's paths, exits silently. Only
days with both (a) an audit due *and* (b) actual changes incur a
`claude -p` invocation.

## Manual / dev usage

```sh
# List configured audits and which are due today.
scripts/audit.py list

# Run one audit unconditionally (skips early-exit gate).
scripts/audit.py run proptest --force

# Same, but print the prompt instead of invoking claude (free).
scripts/audit.py run proptest --force --dry-run
```

## Adding a new audit

1. Drop a new markdown file under `doc/audits/<name>.md` with the
   front-matter schema above.
2. Body should include: a "Read first" section pointing at relevant
   docs, a mechanical pass (regex-checkable rules), an optional
   judgment pass, an output format, and an anti-themes section
   listing known false positives.
3. Test with `scripts/audit.py run <name> --force --dry-run` to
   confirm prompt assembly.

## Cadence accounting

| Audit | Day | Cadence | Avg fires/year |
|-------|-----|---------|----------------|
| proptest | mon | weekly | 52 |
| docrot | thu | weekly | 52 |
| coverage | tue | biweekly | 26 |
| hygiene | wed | monthly | 12 |
| pii | fri | monthly | 12 |

154 fires/year against the calendar; far fewer against `claude -p`
since the early-exit gate skips no-change weeks. For a low-velocity
project this is comfortably ~30–60 actual Claude invocations/year.

## Why not Anthropic routines?

Routines (claude.ai/code/routines) are budget-counted and
GitHub-biased; the GitLab MCP integration requires GitLab Premium
(out of scope for this project). System cron + `claude -p` gives
the same recurrence semantics with: no routine budget, no MCP
setup, no OAuth handshake, no GitHub assumption.
