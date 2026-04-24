"""Shared helpers for scripts/pull_reviews.py and scripts/reply_review.py
GitLab-review CLIs.

Private sibling module so updates land in one place. Scripts invoked as
`scripts/foo.py` get `scripts/` on `sys.path[0]` automatically, which is
enough for `from _glab import ...` to resolve without any package setup.
"""

from __future__ import annotations

import os
import subprocess
import sys
import urllib.parse


def _run_glab(args: list[str]) -> str:
    """Run `glab` with the given args, returning stdout.

    Raises SystemExit on FileNotFoundError (missing `glab`) or
    CalledProcessError, with a user-facing message on stderr.
    """
    try:
        return subprocess.check_output(
            ["glab", *args], text=True, stderr=subprocess.PIPE,
        )
    except FileNotFoundError:
        print(
            "error: `glab` CLI not found; install GitLab CLI and ensure it is on PATH",
            file=sys.stderr,
        )
        raise SystemExit(1)
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or "").strip()
        msg = f": {detail}" if detail else ""
        print(
            f"error: `glab {' '.join(args)}` failed{msg}",
            file=sys.stderr,
        )
        raise SystemExit(1)


def glab_project() -> str:
    """Return the full path of the repo for the current working dir
    (e.g. "group/subgroup/project"), suitable for URL-encoding into a
    project id.
    """
    # `glab repo view -F json` outputs a blob that includes
    # `fullName` / `path_with_namespace` depending on version; try the
    # newer field first.
    import json

    raw = _run_glab(["repo", "view", "-F", "json"])
    try:
        obj = json.loads(raw)
    except json.JSONDecodeError as exc:
        print(
            f"error: could not parse `glab repo view -F json` output: {exc}",
            file=sys.stderr,
        )
        raise SystemExit(1)
    for key in ("fullName", "path_with_namespace", "full_name"):
        val = obj.get(key)
        if isinstance(val, str) and val:
            return val
    print(
        "error: `glab repo view` did not return a full project path; "
        "pass --repo group/project explicitly",
        file=sys.stderr,
    )
    raise SystemExit(1)


def encode_project(path: str) -> str:
    """URL-encode a group/project path for use as a REST API id."""
    return urllib.parse.quote(path, safe="")


def resolve_mr(mr: int, repo_override: str | None) -> str:
    """Pick the target project, verifying the MR exists in it.

    If `--repo` was passed, trust it (explicit beats inferred).
    Otherwise auto-detect via `glab repo view` from cwd, then pre-flight
    `glab api projects/{id}/merge_requests/{iid}`. On 404, error with
    both the detected project and cwd so a user whose shell drifted
    into the wrong directory sees the mismatch immediately instead of
    getting an opaque 404 from later endpoint calls.

    Returns the URL-encoded project id suitable for interpolating into
    subsequent `projects/{id}/...` calls.
    """
    if repo_override:
        project = repo_override
    else:
        project = glab_project()

    project_id = encode_project(project)
    try:
        subprocess.run(
            ["glab", "api", f"projects/{project_id}/merge_requests/{mr}"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            text=True,
            check=True,
        )
    except FileNotFoundError:
        print(
            "error: `glab` CLI not found; install GitLab CLI and ensure it is on PATH",
            file=sys.stderr,
        )
        raise SystemExit(1)
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or "").strip()
        if "404" in detail or "Not Found" in detail or "not found" in detail.lower():
            cwd = os.getcwd()
            lines = [
                f"error: couldn't verify MR !{mr} in {project} "
                f"(project detected from cwd: {cwd}).",
                "  The MR may be in a different project — pass "
                "--repo group/project to override.",
                "  A 404 here can also mean your glab token lacks access "
                "to this project/MR.",
            ]
            if detail:
                lines.append(f"  glab api detail: {detail}")
            print("\n".join(lines), file=sys.stderr)
            raise SystemExit(1)
        msg = f": {detail}" if detail else ""
        print(
            f"error: couldn't verify MR !{mr} in {project} via `glab api`{msg}",
            file=sys.stderr,
        )
        raise SystemExit(1)
    return project_id
