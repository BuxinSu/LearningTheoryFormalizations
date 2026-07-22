#!/usr/bin/env python3
"""Normalize a closed V4 shard transcript after duplicate-run recovery.

Only transcript framing is rewritten: the final process footer is treated as
authoritative, its start time is reconstructed from the recorded elapsed
duration, heartbeat/status metadata are removed, and any Lean diagnostic
body is preserved verbatim.  The result has exactly one header and one
successful footer for the shard merger's fail-closed parser.
"""

from __future__ import annotations

import argparse
import datetime as dt
import os
import re
import tempfile
from pathlib import Path


FIELD_LINE = re.compile(
    r"^(?:started|cwd|command|source_manifest_digest|harness_sha256|heartbeat|finished|elapsed_seconds|exit_code):"
)


class NormalizeError(RuntimeError):
    pass


def unique_last(text: str, key: str) -> str:
    values = re.findall(rf"(?m)^{re.escape(key)}:\s*(.+?)\s*$", text)
    if not values:
        raise NormalizeError(f"missing {key} field")
    return values[-1]


def normalize(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="strict")
    finished_text = unique_last(text, "finished")
    elapsed_text = unique_last(text, "elapsed_seconds")
    exit_text = unique_last(text, "exit_code")
    if exit_text != "0":
        raise NormalizeError(f"refusing nonzero shard transcript: {exit_text}")
    finished = dt.datetime.fromisoformat(finished_text)
    if finished.tzinfo is None:
        raise NormalizeError("finished timestamp is not timezone-aware")
    elapsed = float(elapsed_text)
    if elapsed <= 0:
        raise NormalizeError("elapsed duration is not positive")
    started = finished - dt.timedelta(seconds=elapsed)
    cwd = unique_last(text, "cwd")
    command = unique_last(text, "command")
    source_manifest_digest = unique_last(text, "source_manifest_digest")
    harness_sha256 = unique_last(text, "harness_sha256")

    body: list[str] = []
    for line in text.splitlines():
        if FIELD_LINE.match(line):
            continue
        body.append(line)
    while body and not body[0]:
        body.pop(0)
    while body and not body[-1]:
        body.pop()
    rendered_lines = [
        f"started: {started.isoformat()}",
        f"cwd: {cwd}",
        f"command: {command}",
        f"source_manifest_digest: {source_manifest_digest}",
        f"harness_sha256: {harness_sha256}",
        "",
        *body,
        "",
        f"finished: {finished.isoformat()}",
        f"elapsed_seconds: {elapsed:.3f}",
        "exit_code: 0",
        "",
    ]
    rendered = "\n".join(rendered_lines)
    temporary_fd, temporary_name = tempfile.mkstemp(
        dir=path.parent, prefix=f".{path.name}.normalize-"
    )
    try:
        with os.fdopen(temporary_fd, "w", encoding="utf-8") as handle:
            handle.write(rendered)
        os.replace(temporary_name, path)
    except BaseException:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise
    print(f"PASS: normalized closed V4 shard transcript: {path}")
    print(f"started: {started.isoformat()}")
    print(f"finished: {finished.isoformat()}")
    print(f"elapsed_seconds: {elapsed:.3f}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", type=Path)
    args = parser.parse_args()
    return normalize(args.path)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (NormalizeError, OSError, ValueError) as error:
        print(f"V4 LOG NORMALIZATION FAIL: {error}")
        raise SystemExit(1)
