#!/usr/bin/env python3
"""Run one final-recertification V4 shard with a closed transcript.

The shard harness writes its large raw tables to local temporary storage.
This runner prevents concurrent V4 writers, verifies the frozen source
manifest before and after Lean runs, and appends the timestamped footer that
the exhaustive merger validates.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import os
import shlex
import subprocess
from pathlib import Path

from source_manifest import build_manifest


SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
LOCK = Path("/private/tmp/hdp_axiom_audit_final_recertification.lock")
HARNESSES = (
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard0.lean",
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard1.lean",
)
OUTPUTS = (
    Path("/private/tmp/hdp_v4_78da87_shard0"),
    Path("/private/tmp/hdp_v4_78da87_shard1"),
)
EXPECTED_OUTPUTS = (
    "axiom_calibration.tsv",
    "axiom_modules.txt",
    "axiom_audit.tsv",
    "axiom_declaration_types.tsv",
    "axiom_declaration_binders.tsv",
    "axiom_direct_dependencies.tsv",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_current_manifest() -> str:
    rendered, digest = build_manifest()
    if SOURCE_MANIFEST.read_text(encoding="utf-8") != rendered:
        raise RuntimeError(
            "source manifest drift; refusing to run a V4 shard"
        )
    return digest


def validate_harness(index: int, harness: Path, output: Path) -> None:
    if not harness.is_file():
        raise FileNotFoundError(harness)
    text = harness.read_text(encoding="utf-8")
    required = (
        "import HighDimensionalProbability\n",
        "import HighDimensionalProbability.Appendix\n",
        "import MatrixConcentration.Appendix_MatrixRosenthal\n",
        f'"/private/tmp/hdp_v4_78da87_shard{index}/axiom_audit.tsv"',
        f"if currentIndex % 2 == {index} then",
    )
    missing = [fragment for fragment in required if fragment not in text]
    if missing:
        raise RuntimeError(
            f"{harness}: invalid shard-{index} harness; missing {missing}"
        )
    if output != OUTPUTS[index]:
        raise RuntimeError(
            f"shard {index} output must be the audited path {OUTPUTS[index]}"
        )


def run(index: int) -> int:
    harness = HARNESSES[index]
    output = OUTPUTS[index]
    validate_harness(index, harness, output)
    digest_before = require_current_manifest()
    if output.exists():
        raise RuntimeError(f"refusing to overwrite shard output: {output}")
    output.mkdir(parents=True)
    build_log = output / "axiom_audit_build.log"
    lake = Path.home() / ".elan" / "bin" / "lake"
    command = [
        str(lake),
        "env",
        "lean",
        "-DmaxSynthPendingDepth=3",
        "-DrelaxedAutoImplicit=false",
        str(harness),
    ]
    started = dt.datetime.now(dt.timezone.utc).astimezone()
    with LOCK.open("a+", encoding="utf-8") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            lock.seek(0)
            owner = lock.read().strip() or "unknown owner"
            raise RuntimeError(
                f"another V4 writer holds the global lock: {owner}"
            ) from error
        lock.seek(0)
        lock.truncate()
        lock.write(
            f"pid={os.getpid()} shard={index} "
            f"started={started.isoformat()}\n"
        )
        lock.flush()
        with build_log.open("w", encoding="utf-8") as log:
            log.write(f"started: {started.isoformat()}\n")
            log.write(f"cwd: {ROOT}\n")
            log.write(f"command: {shlex.join(command)}\n\n")
            log.write(f"source_manifest_digest: {digest_before}\n\n")
            log.write(f"harness_sha256: {sha256(harness)}\n\n")
            log.flush()
            completed = subprocess.run(
                command,
                cwd=ROOT,
                text=True,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
            finished = dt.datetime.now(dt.timezone.utc).astimezone()
            log.write(f"\nfinished: {finished.isoformat()}\n")
            log.write(
                "elapsed_seconds: "
                f"{(finished - started).total_seconds():.3f}\n"
            )
            log.write(f"exit_code: {completed.returncode}\n")
    if completed.returncode != 0:
        return completed.returncode
    missing_outputs = [
        name
        for name in EXPECTED_OUTPUTS
        if not (output / name).is_file() or (output / name).stat().st_size == 0
    ]
    if missing_outputs:
        raise RuntimeError(
            f"shard {index} did not close outputs: {missing_outputs}"
        )
    digest_after = require_current_manifest()
    if digest_after != digest_before:
        raise RuntimeError(
            "source manifest changed while the V4 shard was running"
        )
    print(
        f"PASS: V4 shard {index} closed; "
        f"source_manifest_digest={digest_after}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("index", type=int, choices=(0, 1))
    args = parser.parse_args()
    return run(args.index)


if __name__ == "__main__":
    raise SystemExit(main())
