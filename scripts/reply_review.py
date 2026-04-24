#!/usr/bin/env python3
"""Post a reply into an existing MR discussion thread on GitLab.

GitLab's review model is discussions-of-notes: to reply to a specific
comment, you add a note to the discussion that comment lives in. This
script takes a note id and looks up its discussion, then appends a new
note to that discussion via
`POST /projects/:id/merge_requests/:iid/discussions/:discussion_id/notes`.

Prints the new note's id and web URL on success.

Requires: `glab` CLI authenticated for the current project.

Usage:
    scripts/reply_review.py <MR> <IN_REPLY_TO_ID> <BODY>
    scripts/reply_review.py <MR> <IN_REPLY_TO_ID> -    # read body from stdin
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys

from _glab import resolve_mr


def find_discussion_for_note(project_id: str, mr: int, note_id: int) -> str:
    """Return the discussion_id that contains the given note_id."""
    page = 1
    while True:
        path = (
            f"projects/{project_id}/merge_requests/{mr}/discussions"
            f"?per_page=100&page={page}"
        )
        try:
            raw = json.loads(
                subprocess.check_output(
                    ["glab", "api", path], text=True, stderr=subprocess.PIPE
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
                f"error: `glab api` failed for `{path}`{msg}", file=sys.stderr,
            )
            raise SystemExit(1)
        if not isinstance(raw, list) or not raw:
            break
        for d in raw:
            for n in d.get("notes", []) or []:
                if n.get("id") == note_id:
                    return d["id"]
        if len(raw) < 100:
            break
        page += 1
    print(
        f"error: note id {note_id} not found in any discussion on MR !{mr}",
        file=sys.stderr,
    )
    raise SystemExit(1)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("mr", type=int, help="MR number (iid)")
    ap.add_argument(
        "in_reply_to_id",
        type=int,
        help="glab-id of the note you are replying to",
    )
    ap.add_argument(
        "body",
        help="Reply body (markdown). Pass '-' to read from stdin.",
    )
    ap.add_argument("--repo", default=None, help="group/project (default: auto)")
    args = ap.parse_args()

    body = sys.stdin.read() if args.body == "-" else args.body
    body = body.strip()
    if not body:
        print("error: empty body", file=sys.stderr)
        return 1

    project_id = resolve_mr(args.mr, args.repo)
    discussion_id = find_discussion_for_note(project_id, args.mr, args.in_reply_to_id)
    path = (
        f"projects/{project_id}/merge_requests/{args.mr}"
        f"/discussions/{discussion_id}/notes"
    )

    try:
        result = subprocess.run(
            ["glab", "api", "--method", "POST", path, "-f", f"body={body}"],
            capture_output=True,
            text=True,
            check=True,
        )
    except FileNotFoundError:
        print(
            "error: `glab` CLI not found; install GitLab CLI and ensure it is on PATH",
            file=sys.stderr,
        )
        return 1
    except subprocess.CalledProcessError as exc:
        if exc.stderr:
            sys.stderr.write(exc.stderr)
        return exc.returncode or 1

    data = json.loads(result.stdout)
    print(f"posted reply id={data['id']} discussion={discussion_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
