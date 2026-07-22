#!/usr/bin/env python3
"""Run a command while streaming and permanently recording merged output."""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import os
import selectors
import shlex
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
V4_LOCK = Path("/private/tmp/hdp_axiom_audit_final_recertification.lock")


def acquire_v4_lock_if_needed(command: list[str]):
    """Prevent this generic runner from bypassing the V4 writer lock."""
    if not any("AxiomAuditShard" in argument for argument in command):
        return None
    lock = V4_LOCK.open("a+", encoding="utf-8")
    try:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        lock.close()
        raise RuntimeError(
            "refusing concurrent V4 shard: the global audit lock is held"
        )
    return lock


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--cwd", type=Path, default=ROOT)
    parser.add_argument(
        "--heartbeat-seconds",
        type=float,
        default=0,
        help=(
            "emit a timestamped progress line after this many silent seconds; "
            "zero disables heartbeats"
        ),
    )
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("a command is required after --")
    v4_lock = acquire_v4_lock_if_needed(command)

    log_path = args.log if args.log.is_absolute() else ROOT / args.log
    cwd = args.cwd if args.cwd.is_absolute() else ROOT / args.cwd
    log_path.parent.mkdir(parents=True, exist_ok=True)
    started = dt.datetime.now(dt.timezone.utc).astimezone()
    header = [
        f"started: {started.isoformat()}",
        f"cwd: {cwd}",
        f"command: {shlex.join(command)}",
        "",
    ]
    with log_path.open("w", encoding="utf-8") as log:
        for line in header:
            print(line)
            log.write(line + "\n")
        log.flush()
        process = subprocess.Popen(
            command,
            cwd=cwd,
            env=os.environ.copy(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=1,
        )
        assert process.stdout is not None
        if args.heartbeat_seconds < 0:
            parser.error("--heartbeat-seconds must be nonnegative")
        if args.heartbeat_seconds == 0:
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                log.write(line)
                log.flush()
        else:
            selector = selectors.DefaultSelector()
            selector.register(process.stdout, selectors.EVENT_READ)
            while True:
                ready = selector.select(timeout=args.heartbeat_seconds)
                if ready:
                    line = process.stdout.readline()
                    if line:
                        sys.stdout.write(line)
                        sys.stdout.flush()
                        log.write(line)
                        log.flush()
                        continue
                if process.poll() is not None:
                    for line in process.stdout:
                        sys.stdout.write(line)
                        sys.stdout.flush()
                        log.write(line)
                    log.flush()
                    break
                heartbeat = (
                    "heartbeat: "
                    f"{dt.datetime.now(dt.timezone.utc).astimezone().isoformat()}"
                )
                print(heartbeat, flush=True)
                log.write(heartbeat + "\n")
                log.flush()
        returncode = process.wait()
        finished = dt.datetime.now(dt.timezone.utc).astimezone()
        footer = [
            "",
            f"finished: {finished.isoformat()}",
            f"elapsed_seconds: {(finished - started).total_seconds():.3f}",
            f"exit_code: {returncode}",
        ]
        for line in footer:
            print(line)
            log.write(line + "\n")
    if v4_lock is not None:
        v4_lock.close()
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())
