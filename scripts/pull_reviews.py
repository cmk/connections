#!/usr/bin/env python3
"""Fetch GitLab MR discussions and append them chronologically to
`doc/reviews/review-NNNNN.md`.

GitLab's review model is "discussions" (threads) each containing one
or more "notes" (messages). This script fetches every note across
every discussion and appends new ones to the review file.

Idempotent via set-membership on `<!-- glab-id: N -->` markers: any
note whose id is already present in the target file is skipped. Note
ids are globally unique within a project, so one marker pool is
sufficient.

Paginated via explicit `?per_page=100&page=N` iteration.

Requires: `glab` CLI authenticated for the current project.

Usage:
    scripts/pull_reviews.py <MR_NUMBER> [--repo group/project] [--out doc/reviews]
"""

from __future__ import annotations

import argparse
import datetime
import json
import pathlib
import re
import subprocess
import sys

from _glab import resolve_mr


def glab_api(path: str) -> list | dict:
    """Fetch a list endpoint, iterating pages explicitly.

    Explicit `?page=N&per_page=100` iteration is version-agnostic and
    trivially inspectable.

    If the endpoint returns a dict (non-list), we return it as-is from
    page 1 without continuing to page.
    """
    all_items: list = []
    page = 1
    while True:
        sep = "&" if "?" in path else "?"
        paged = f"{path}{sep}per_page=100&page={page}"
        try:
            raw = json.loads(
                subprocess.check_output(
                    ["glab", "api", paged], text=True, stderr=subprocess.PIPE
                )
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
                f"error: `glab api` failed for endpoint `{paged}`{msg}", file=sys.stderr
            )
            raise SystemExit(1)
        if not isinstance(raw, list):
            return raw
        if not raw:
            break
        all_items.extend(raw)
        if len(raw) < 100:
            break
        page += 1
    return all_items


def mr_title(project_id: str, iid: int) -> str:
    try:
        raw = subprocess.check_output(
            ["glab", "api", f"projects/{project_id}/merge_requests/{iid}"],
            text=True,
            stderr=subprocess.PIPE,
        )
        return json.loads(raw).get("title", f"MR !{iid}")
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
            f"error: failed to determine title for MR !{iid} via `glab api`{msg}",
            file=sys.stderr,
        )
        raise SystemExit(1)


def fmt_ts(t: str) -> str:
    d = datetime.datetime.fromisoformat(t.replace("Z", "+00:00"))
    return d.strftime("%Y-%m-%d %H:%M UTC")


def existing_ids(path: pathlib.Path) -> set[int]:
    if not path.exists():
        return set()
    return {
        int(h)
        for h in re.findall(
            r"<!-- glab-id: (\d+) -->", path.read_text(encoding="utf-8")
        )
    }


def collect_items(project_id: str, iid: int) -> list[dict]:
    """Fetch all notes from all discussions on the MR and flatten.

    Each discussion carries its own id (string) and a list of notes.
    The first note in a discussion is the thread starter; subsequent
    notes are replies. System notes (label changes, assignments) are
    dropped.
    """
    items: list[dict] = []
    for d in glab_api(f"projects/{project_id}/merge_requests/{iid}/discussions"):
        discussion_id = d.get("id", "")
        notes = d.get("notes", []) or []
        for idx, n in enumerate(notes):
            if n.get("system"):
                continue
            if not n.get("body"):
                continue
            created_at = n.get("created_at")
            if not created_at:
                continue
            pos = n.get("position") or {}
            path_hit = pos.get("new_path") or pos.get("old_path")
            line_hit = pos.get("new_line") or pos.get("old_line")
            items.append(
                {
                    "ts": created_at,
                    # Coerce to int at the API boundary: `existing_ids()`
                    # parses ids from the review file as ints, and some
                    # GitLab API versions return note ids as strings.
                    # Mismatched types would silently break idempotency
                    # (int ≠ str, so seen-check never hits).
                    "id": int(n["id"]),
                    "user": (n.get("author") or {}).get("username", "unknown"),
                    "body": n["body"],
                    "path": path_hit,
                    "line": line_hit,
                    "discussion_id": discussion_id,
                    "is_reply": idx > 0,
                    "resolvable": n.get("resolvable", False),
                    "resolved": n.get("resolved", False),
                }
            )
    items.sort(key=lambda x: x["ts"])
    return items


def render(it: dict, web_base: str | None) -> str:
    ts = fmt_ts(it["ts"])
    body = it["body"]
    out = [
        f"\n<!-- glab-id: {it['id']} -->",
        f"<!-- glab-discussion: {it['discussion_id']} -->",
    ]
    status = ""
    if it["resolvable"]:
        status = " [resolved]" if it["resolved"] else " [open]"
    if it["is_reply"]:
        out.append(f"#### ↳ {it['user']} ({ts}){status}")
    elif it["path"]:
        loc = it["path"] + (f":{it['line']}" if it["line"] else "")
        out.append(f"### {it['user']} on `{loc}` ({ts}){status}")
    else:
        out.append(f"### {it['user']} — ({ts}){status}")
    out.append("")
    out.append(body)
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("mr", type=int, help="MR number (iid)")
    ap.add_argument("--repo", default=None, help="group/project (default: auto)")
    ap.add_argument(
        "--out",
        default="doc/reviews",
        help="directory for review-NNNNN.md (default: doc/reviews)",
    )
    args = ap.parse_args()

    project_id = resolve_mr(args.mr, args.repo)
    out_dir = pathlib.Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / f"review-{args.mr:05d}.md"

    if not path.exists():
        title = mr_title(project_id, args.mr)
        path.write_text(f"# MR !{args.mr} — {title}\n", encoding="utf-8")

    seen = existing_ids(path)
    new_items = [it for it in collect_items(project_id, args.mr) if it["id"] not in seen]

    if not new_items:
        print(f"MR !{args.mr}: no new items ({len(seen)} already recorded)")
        return 0

    with path.open("a", encoding="utf-8") as f:
        for it in new_items:
            f.write(render(it, None))

    print(f"MR !{args.mr}: appended {len(new_items)} items -> {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
