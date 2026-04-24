#!/usr/bin/env bash
# Prints the review file path for an MR: `doc/reviews/review-NNNNN.md`
# with `NNNNN` zero-padded to 5 digits.
#
# Source of truth for the review-file naming convention. Callers that
# don't want to know about padding should use this instead of composing
# `doc/reviews/review-$(printf '%05d' ...).md` themselves.
#
# Usage:
#     scripts/review_path.sh              — path for the next-to-be-opened MR
#                                           (calls scripts/next_mr_number.sh)
#     scripts/review_path.sh <mr-number>  — path for a given MR number (iid)
#
# Accepts both unpadded (`17`) and zero-padded (`00017`) input; bash's
# octal interpretation is defused via `$((10#$n))`.
#
# Run from the repo root (output path is relative to CWD).
set -euo pipefail

if [ $# -gt 1 ]; then
  echo "usage: $0 [<mr-number>]" >&2
  exit 1
fi

if [ $# -eq 1 ]; then
  if ! [[ "$1" =~ ^[0-9]+$ ]]; then
    echo "error: mr number must be numeric: '$1'" >&2
    exit 1
  fi
  n="$1"
else
  script_dir=$(cd "$(dirname "$0")" && pwd)
  if ! n=$("$script_dir/next_mr_number.sh"); then
    echo "error: scripts/next_mr_number.sh failed; pass an mr number explicitly" >&2
    exit 1
  fi
fi

printf 'doc/reviews/review-%05d.md\n' "$((10#$n))"
