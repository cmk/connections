#!/usr/bin/env python3
"""Run Claude against a GitLab MR diff and post review findings as
discussion notes anchored to file:line (with a general-comment fallback
when the anchor doesn't land on a line GitLab recognizes).

Invoked by the `claude-review` job in `.gitlab-ci.yml` on
`merge_request_event` pipelines.

Required CI environment variables (GitLab predefined):
    CI_PROJECT_ID
    CI_MERGE_REQUEST_IID
    CI_MERGE_REQUEST_DIFF_BASE_SHA   (merge-base)
    CI_COMMIT_SHA                    (source HEAD)

Required secrets (set in Project → Settings → CI/CD → Variables,
masked, protected if on a protected branch):
    ANTHROPIC_API_KEY
    GITLAB_TOKEN                     (PAT with `api` scope; or a
                                       Project Access Token)

Optional:
    CLAUDE_MODEL                     default: claude-sonnet-4-6
                                     (set to claude-opus-4-7 for
                                     deeper-but-slower review)
    GITLAB_HOST                      default: gitlab.com

The job is advisory: the script's exit code is non-zero only if posting
itself failed. Review content that flags bugs does not fail the job —
that would make the AI a merge blocker, which is not the intent here.
`allow_failure: true` in the CI job provides the matching belt.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import textwrap
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

try:
    import anthropic
except ImportError:
    print(
        "error: `anthropic` package not installed. In CI, add "
        "`pip install anthropic` to before_script.",
        file=sys.stderr,
    )
    raise SystemExit(2)


DEFAULT_MODEL = "claude-sonnet-4-6"
MAX_DIFF_CHARS = 160_000  # ~40k tokens, well under the 200k context.


SYSTEM = textwrap.dedent("""\
    You are reviewing code on a GitLab merge request. You are an
    independent reviewer — you did not write this code and have no
    context beyond what is provided below. Review what you see, not
    what you assume.

    Emit a JSON array of findings. Each finding is an object:

        {
          "path": "src/foo.rs",          // new-path, repo-root-relative
          "line": 42,                      // new-line number, 1-indexed
          "severity": "must-fix" | "follow-up",
          "body": "..."                   // <= 3 sentences, markdown
        }

    Review style (match the calibration examples if provided):
    - Cite the contract (doc, plan, naming), show the violation, name
      the consequence.
    - `must-fix` only for correctness violations or convention breaches
      that should block merge. Everything else is `follow-up`.
    - Skip nits (naming preferences, whitespace). CI handles those.
    - One finding per issue; no duplicates across files.
    - If nothing warrants review, return `[]`.

    HARD OUTPUT CONSTRAINT: your entire response must be a single JSON
    array. No prose preamble, no code fences, no trailing commentary.
    This response is parsed by a script; anything non-JSON causes the
    review to be silently dropped.
    """)


def sh(cmd: list[str]) -> str:
    return subprocess.check_output(cmd, text=True, stderr=subprocess.PIPE)


def git_diff(base: str, head: str) -> str:
    return sh(["git", "diff", f"{base}...{head}"])


def git_fetch_sha(sha: str) -> None:
    """Ensure `sha` is present locally. No-op if already fetched."""
    try:
        sh(["git", "cat-file", "-e", sha])
        return
    except subprocess.CalledProcessError:
        pass
    # Either a direct fetch-by-sha (server must have
    # `uploadpack.allowReachableSHA1InWant`, which gitlab.com does), or
    # a deep-ish fetch of the ref that contains it.
    try:
        sh(["git", "fetch", "--depth=200", "origin", sha])
    except subprocess.CalledProcessError:
        # Fall back to a full fetch.
        sh(["git", "fetch", "--unshallow", "origin"])


def glab_fetch_mr(project_id: str, mr_iid: int, token: str, host: str) -> dict:
    """Fetch MR details from GitLab. Used by the manual-trigger path
    when CI_MERGE_REQUEST_DIFF_BASE_SHA isn't provided by the runner.
    """
    url = (
        f"https://{host}/api/v4/projects/"
        f"{urllib.parse.quote(project_id, safe='')}"
        f"/merge_requests/{mr_iid}"
    )
    req = urllib.request.Request(url, headers={"PRIVATE-TOKEN": token})
    with urllib.request.urlopen(req) as resp:
        return json.loads(resp.read().decode("utf-8"))


def read_optional(path: str) -> str:
    try:
        return Path(path).read_text(encoding="utf-8")
    except FileNotFoundError:
        return ""


def build_user_content(diff: str, conventions: str, calibration: str) -> list[dict]:
    """Build the user message content array. Stable parts (conventions,
    calibration) are cached; the diff is not.
    """
    parts: list[dict] = []
    if conventions:
        parts.append(
            {
                "type": "text",
                "text": f"## Repo conventions (CLAUDE.md)\n\n{conventions}",
                "cache_control": {"type": "ephemeral"},
            }
        )
    if calibration:
        parts.append(
            {
                "type": "text",
                "text": f"## Calibration examples\n\n{calibration}",
                "cache_control": {"type": "ephemeral"},
            }
        )
    parts.append(
        {
            "type": "text",
            "text": (
                "## MR diff\n\n"
                f"```diff\n{diff}\n```\n\n"
                "Review this diff and emit findings as JSON per the "
                "system instructions."
            ),
        }
    )
    return parts


def call_claude(model: str, user_content: list[dict]) -> str:
    # max_retries=5 (up from the SDK default of 2) to ride through
    # transient 5xx / 529 Overloaded blips that last a few seconds.
    # The SDK applies exponential backoff between retries. If it still
    # fails after 5 attempts the CI job's own `retry: 2` takes another
    # swing minutes later when Anthropic's load window has shifted.
    client = anthropic.Anthropic(max_retries=5)
    msg = client.messages.create(
        model=model,
        max_tokens=4096,
        system=[
            {
                "type": "text",
                "text": SYSTEM,
                "cache_control": {"type": "ephemeral"},
            }
        ],
        messages=[{"role": "user", "content": user_content}],
    )
    # Concatenate all text blocks in the response.
    return "".join(
        b.text for b in msg.content if getattr(b, "type", None) == "text"
    )


def parse_findings(raw: str) -> list[dict]:
    raw = raw.strip()
    # Tolerate accidental code fences.
    if raw.startswith("```"):
        raw = raw.strip("`")
        if raw.startswith("json"):
            raw = raw[4:]
        raw = raw.strip()
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError as e:
        print(
            "warning: Claude did not return parseable JSON; "
            "no findings will be posted.",
            file=sys.stderr,
        )
        print(f"  parse error: {e}", file=sys.stderr)
        print(f"  raw (first 500 chars): {raw[:500]!r}", file=sys.stderr)
        return []
    if not isinstance(parsed, list):
        print(
            f"warning: JSON was not an array (got {type(parsed).__name__}); "
            "no findings will be posted.",
            file=sys.stderr,
        )
        return []
    valid: list[dict] = []
    for i, f in enumerate(parsed):
        if not isinstance(f, dict):
            continue
        if not all(k in f for k in ("path", "line", "severity", "body")):
            print(
                f"warning: finding #{i} missing required fields; skipping",
                file=sys.stderr,
            )
            continue
        if f["severity"] not in ("must-fix", "follow-up"):
            f["severity"] = "follow-up"
        valid.append(f)
    return valid


def gitlab_post(
    host: str,
    project_id: str,
    mr_iid: int,
    token: str,
    body: str,
    position: dict | None,
) -> tuple[int, str]:
    """POST to /merge_requests/:iid/discussions. Returns (status, body).

    If `position` is None, posts a general comment. Otherwise posts an
    inline-anchored discussion.
    """
    url = (
        f"https://{host}/api/v4/projects/"
        f"{urllib.parse.quote(project_id, safe='')}"
        f"/merge_requests/{mr_iid}/discussions"
    )
    form: dict[str, str] = {"body": body}
    if position is not None:
        for k, v in position.items():
            form[f"position[{k}]"] = str(v)
    data = urllib.parse.urlencode(form).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=data,
        method="POST",
        headers={
            "PRIVATE-TOKEN": token,
            "Content-Type": "application/x-www-form-urlencoded",
        },
    )
    try:
        with urllib.request.urlopen(req) as resp:
            return resp.status, resp.read().decode("utf-8", errors="replace")[:500]
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", errors="replace")[:500]


FOOTER = "\n\n---\n_Posted by `claude-review` CI — advisory, not merge-blocking._"


def post_finding(
    host: str,
    project_id: str,
    mr_iid: int,
    token: str,
    finding: dict,
    base_sha: str,
    head_sha: str,
) -> tuple[bool, str]:
    inline_body = f"**[{finding['severity']}]** {finding['body']}{FOOTER}"
    position = {
        "position_type": "text",
        "base_sha": base_sha,
        "start_sha": base_sha,
        "head_sha": head_sha,
        "new_path": finding["path"],
        "old_path": finding["path"],
        "new_line": finding["line"],
    }
    status, body = gitlab_post(host, project_id, mr_iid, token, inline_body, position)
    if status < 300:
        return True, f"inline: {finding['path']}:{finding['line']}"
    # Inline failed — fall back to a general-comment reference.
    general_body = (
        f"**[{finding['severity']}]** `{finding['path']}:{finding['line']}` — "
        f"{finding['body']}\n\n"
        f"*(inline anchor rejected by GitLab: {status})*{FOOTER}"
    )
    status2, body2 = gitlab_post(host, project_id, mr_iid, token, general_body, None)
    if status2 < 300:
        return True, f"general: {finding['path']}:{finding['line']} (inline {status})"
    return (
        False,
        f"failed {finding['path']}:{finding['line']}: inline={status} general={status2}"
        f" // body: {body2[:120]}",
    )


def require_env(name: str) -> str | None:
    v = os.environ.get(name)
    return v if v else None


def resolve_mr_inputs(host: str, project_id: str, token: str) -> tuple[int, str, str] | None:
    """Return (mr_iid, base_sha, head_sha) or None on missing/invalid input.

    Two envelopes:

    - **merge_request_event pipeline** — `CI_MERGE_REQUEST_IID`,
      `CI_MERGE_REQUEST_DIFF_BASE_SHA`, `CI_COMMIT_SHA` are all
      provided by GitLab. Use them directly.
    - **manual trigger** — user sets `CLAUDE_REVIEW_MR` via
      `glab ci run --variables` or the web UI. We look up the MR's
      base and head SHAs via the GitLab API, then ensure both are
      fetched locally so `git diff base...head` works regardless of
      which branch the manual pipeline happened to check out.
    """
    mr_iid_s = os.environ.get("CI_MERGE_REQUEST_IID") or os.environ.get(
        "CLAUDE_REVIEW_MR"
    )
    if not mr_iid_s:
        print(
            "claude-review: no MR iid in environment "
            "(CI_MERGE_REQUEST_IID or CLAUDE_REVIEW_MR). Nothing to review.",
            file=sys.stderr,
        )
        return None
    try:
        mr_iid = int(mr_iid_s)
    except ValueError:
        print(f"error: MR iid is not an integer: {mr_iid_s!r}", file=sys.stderr)
        return None

    base_sha = os.environ.get("CI_MERGE_REQUEST_DIFF_BASE_SHA")
    head_sha = os.environ.get("CI_COMMIT_SHA")
    if base_sha and head_sha and os.environ.get("CI_MERGE_REQUEST_IID"):
        # MR-event envelope: CI gave us everything.
        return mr_iid, base_sha, head_sha

    # Manual envelope: ask GitLab for the SHAs.
    try:
        mr = glab_fetch_mr(project_id, mr_iid, token, host)
    except urllib.error.HTTPError as e:
        print(
            f"error: GET /merge_requests/{mr_iid} failed: {e.code} {e.reason}",
            file=sys.stderr,
        )
        return None
    diff_refs = mr.get("diff_refs") or {}
    base_sha = diff_refs.get("base_sha")
    head_sha = mr.get("sha") or diff_refs.get("head_sha")
    if not base_sha or not head_sha:
        print(
            f"error: MR !{mr_iid} API response missing diff_refs.base_sha or sha. "
            "Is the MR closed/unavailable?",
            file=sys.stderr,
        )
        return None

    # Ensure both SHAs are in the local clone before git diff.
    try:
        git_fetch_sha(base_sha)
        git_fetch_sha(head_sha)
    except subprocess.CalledProcessError as e:
        print(
            f"error: could not fetch MR SHAs ({base_sha[:8]}, {head_sha[:8]}) "
            f"into the local clone: {(e.stderr or '').strip()}",
            file=sys.stderr,
        )
        return None
    return mr_iid, base_sha, head_sha


def main() -> int:
    required_secrets = ["ANTHROPIC_API_KEY", "GITLAB_TOKEN", "CI_PROJECT_ID"]
    missing = [n for n in required_secrets if not os.environ.get(n)]
    if missing:
        print(
            f"claude-review: missing env var(s): {', '.join(missing)} — "
            "skipping (harmless on first setup; wire the CI variables to enable).",
            file=sys.stderr,
        )
        return 0

    host = os.environ.get("GITLAB_HOST", "gitlab.com")
    project_id = os.environ["CI_PROJECT_ID"]
    gitlab_token = os.environ["GITLAB_TOKEN"]
    model = os.environ.get("CLAUDE_MODEL", DEFAULT_MODEL)

    resolved = resolve_mr_inputs(host, project_id, gitlab_token)
    if resolved is None:
        return 0  # already logged a diagnostic
    mr_iid, base_sha, head_sha = resolved

    try:
        diff = git_diff(base_sha, head_sha)
    except subprocess.CalledProcessError as e:
        print(
            f"error: `git diff {base_sha}...{head_sha}` failed. "
            "For MR-event pipelines ensure GIT_DEPTH: 0; for manual "
            "triggers the script attempts to fetch both SHAs itself, "
            "so this failure means the fetch step also failed.",
            file=sys.stderr,
        )
        print(f"  stderr: {(e.stderr or '').strip()}", file=sys.stderr)
        return 2

    if not diff.strip():
        print("claude-review: empty diff; nothing to review.")
        return 0

    if len(diff) > MAX_DIFF_CHARS:
        print(
            f"claude-review: diff is {len(diff)} chars (> {MAX_DIFF_CHARS}); "
            "truncating. Consider reviewing large MRs in smaller pieces.",
            file=sys.stderr,
        )
        diff = diff[:MAX_DIFF_CHARS] + "\n\n... [truncated]\n"

    conventions = read_optional("CLAUDE.md")
    calibration = read_optional("doc/reviews/review-calibration.md")
    user = build_user_content(diff, conventions, calibration)

    print(f"claude-review: model={model}, diff={len(diff)} chars, mr=!{mr_iid}")
    try:
        raw = call_claude(model, user)
    except anthropic.APIError as e:
        print(f"error: Anthropic API call failed: {e}", file=sys.stderr)
        return 2

    findings = parse_findings(raw)
    if not findings:
        print("claude-review: no findings.")
        return 0

    print(f"claude-review: {len(findings)} finding(s); posting to MR !{mr_iid}.")
    posted = failed = 0
    for f in findings:
        ok, msg = post_finding(
            host, project_id, mr_iid, gitlab_token, f, base_sha, head_sha
        )
        print(f"  {msg}")
        if ok:
            posted += 1
        else:
            failed += 1

    print(f"claude-review: posted {posted}, failed {failed}.")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
