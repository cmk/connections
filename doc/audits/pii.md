---
name: pii
day: fri
paths: [.]
cadence: monthly
---
You are scanning the connections repo for PII or secrets that have
slipped past the pre-commit `check-pii.sh` hook. The hook runs on
staged diffs only — files committed before the hook existed, files
authored via tools that bypass the hook, or files whose patterns
the hook doesn't catch can still leak.

Read first:
- scripts/check-pii.sh — to understand what the hook *does* catch
  (so you don't duplicate its work; just extend it).

Mechanical pass:

1. Absolute home-directory paths in committed files.
   Pattern: `/Users/[a-z]+/` or `/home/[a-z]+/` anywhere outside
   `.gitignore`'d directories. The hook catches these in staged
   diffs but not historical content.
   Reference precedent: review-00014 flagged `/Users/cmk/` in a plan
   doc that bypassed staging.
   Severity: must-fix (any user-identifying path is a must-fix).

2. Common API token / key shapes.
   Patterns:
     - `sk-[A-Za-z0-9_-]{20,}` (Anthropic / OpenAI style)
     - `glpat-[A-Za-z0-9_-]{20,}` (GitLab personal access token)
     - `ghp_[A-Za-z0-9]{36}` (GitHub personal access token)
     - `xox[baprs]-[A-Za-z0-9-]{10,}` (Slack)
     - 40-character hex strings adjacent to the words "token",
       "key", "secret", "password" (case-insensitive)
   Severity: must-fix. If found, also recommend rotating the token.

3. Email addresses other than the maintainer's.
   Maintainer: chris.mckinlay@gmail.com,
   6869885+cmk@users.noreply.github.com (from git config).
   Any other email address in committed files is a flag.
   Severity: follow-up unless it's clearly a third party's contact
   info (then must-fix and recommend redaction).

4. Hostnames / IPs that look internal.
   Pattern: hostnames matching `*.internal`, `*.corp`, `*.local`,
   or IPv4 addresses in the RFC1918 ranges (10.x, 172.16-31.x,
   192.168.x) anywhere outside test data or example code.
   Severity: follow-up.

Output format:
- One section per category that has findings.
- Use the exact severity labels `[must-fix]` and `[follow-up]`.
- For must-fix findings: include a recommended remediation (rotate
  token, rewrite history with git-filter-repo, etc.).
- If there are zero findings across all 4 categories: output
  exactly the single line `no findings` and nothing else.

Anti-themes:
- Git config values in committed files (`.gitlab-ci.yml`,
  `.githooks/`, etc.) — these are intentional.
- Doc examples that show *example* tokens (clearly fake, e.g.,
  "sk-XXXXXXXXX") — skip if the surrounding text frames them as
  examples.
- Maintainer email in git config-derived files (CHANGELOG
  attribution, commit metadata mirrors).
