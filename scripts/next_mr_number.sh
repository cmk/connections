#!/usr/bin/env bash
# Prints the iid (internal id) that will be assigned to the *next* MR
# opened in the current project.
#
# GitLab uses per-resource iids (merge_requests and issues have their
# own sequences — unlike GitHub's single-sequence model). So the next
# MR iid is simply:
#
#     max(current_mr_iid) + 1
#
# GitLab's MR list endpoint supports `order_by=iid&sort=desc&per_page=1`
# to return the current max directly.
#
# Used by `/sprint-review` to name `doc/reviews/review-NNNNN.md` before
# the MR is opened. The prediction is usually final, but if another MR
# is opened between the prediction and the MR being created, the number
# drifts and the review file has to be renamed to match the iid GitLab
# actually assigned.
#
# Usage:
#     scripts/next_mr_number.sh [group/project]
#
# If `group/project` is omitted, `glab api projects/:id/...` uses the
# current git repo's GitLab project automatically.
#
# Requires: `glab` authenticated for the target project. Prints only
# the number on stdout (so callers can capture it with `$(…)`);
# diagnostics go to stderr.
set -euo pipefail

if [ $# -ge 1 ] && [ -n "$1" ]; then
  # URL-encode the group/project path so it can be used as an API id.
  enc=$(python3 -c 'import sys,urllib.parse;print(urllib.parse.quote(sys.argv[1], safe=""))' "$1")
  api_base="projects/${enc}/merge_requests"
else
  api_base="projects/:id/merge_requests"
fi

if ! last=$(glab api "${api_base}?state=all&order_by=iid&sort=desc&per_page=1" \
    --jq '.[0].iid // 0' 2>/dev/null); then
  echo "error: glab api failed for ${api_base} (check auth, network, and that the repo is on GitLab)" >&2
  exit 1
fi

printf '%d\n' "$((last + 1))"
