#!/usr/bin/env bash
# Extracts the MR description body from doc/reviews/review-NNNNN.md.
#
# The review file's `## Summary` section is the single source of truth
# for the MR description (see CLAUDE.md "Tier 1 — Local review"). This
# script extracts that section so `glab mr create --description-file`
# (or a process substitution) can feed it straight to GitLab:
#
#     glab mr create --title "..." \
#       --description "$(scripts/extract_mr_body.sh 17)"
#
# Content is taken between the `## Summary` heading (exclusive) and the
# first review-round marker (exclusive), printed verbatim to stdout.
#
# Fails loudly with a nonzero exit and a message on stderr if:
#   - the argument is missing or not numeric
#   - the review file doesn't exist
#   - the `## Summary` section is missing
#   - the `## Summary` section is empty (whitespace only)
#
# These checks prevent silently opening an MR with a blank description.
# Run from the repo root.
set -euo pipefail

if [ $# -ne 1 ] || [ -z "${1:-}" ]; then
  echo "usage: $0 <mr-number>" >&2
  exit 1
fi

if ! [[ "$1" =~ ^[0-9]+$ ]]; then
  echo "error: mr number must be numeric: '$1'" >&2
  exit 1
fi

# Force base-10 so zero-padded inputs like `00017` don't trigger bash's
# octal interpretation (which would silently misroute `00017` → `00015`
# and error on digits 8-9).
n=$(printf '%05d' "$((10#$1))")
file="doc/reviews/review-${n}.md"

if [ ! -f "$file" ]; then
  echo "error: review file not found: $file" >&2
  echo "  run TDD step 7 to create it (finalize plan + draft MR description)." >&2
  exit 1
fi

# Extract between `## Summary` (exclusive) and the first review-round
# marker (exclusive). Review markers are `## Local review (YYYY-MM-DD)`
# from /sprint-review and `<!-- glab-id: N -->` from pull_reviews.py.
# Stopping at review markers (rather than any `## ` heading) lets the
# MR body contain sibling sections like `## Test plan` without being
# truncated.
if ! body=$(awk '
  !found && /^## Summary[[:space:]]*$/                    { in_s = 1; found = 1; next }
  in_s && (/^## Local review \(/ || /^<!-- glab-id: /)    { in_s = 0 }
  in_s                                                    { print }
  END                                                     { if (!found) exit 2 }
' "$file"); then
  echo "error: '## Summary' section not found in $file" >&2
  echo "  write the MR description under '## Summary' before opening the MR." >&2
  exit 1
fi

if ! printf '%s' "$body" | grep -q '[^[:space:]]'; then
  echo "error: '## Summary' section in $file is empty" >&2
  echo "  write the MR description under '## Summary' before opening the MR." >&2
  exit 1
fi

printf '%s\n' "$body"
