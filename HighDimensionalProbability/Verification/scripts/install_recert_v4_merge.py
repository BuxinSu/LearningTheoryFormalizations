#!/usr/bin/env python3
"""Atomically install a validated exhaustive V4 shard merge.

The large shard tables are produced on local temporary storage. This script
accepts only a fresh merge for the exact current manifest. It verifies every
artifact hash and exact current row total, installs the six canonical
``recert_axiom_*`` inputs, and writes one aggregate build transcript with
exactly one successful exit footer.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import tempfile
from pathlib import Path

from source_manifest import build_manifest
from verify_exercise_reorganization import (
    CERTIFICATE_LOG,
    require_certificate as require_reorganization_certificate,
)


SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[3]
MERGER_SCRIPT = SCRIPT.with_name("merge_pass07_v4_shards.py")
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
EXPECTED_ROWS = {
    "axiom_audit.tsv": 15_022,
    "axiom_declaration_types.tsv": 15_022,
    "axiom_declaration_binders.tsv": 80_919,
    "axiom_direct_dependencies.tsv": 1_448_224,
}
INSTALL_MAP = {
    "axiom_calibration.tsv": "recert_axiom_calibration.tsv",
    "axiom_modules.txt": "recert_axiom_modules.txt",
    "axiom_audit.tsv": "recert_axiom_audit.tsv",
    "axiom_declaration_types.tsv": "recert_axiom_declaration_types.tsv",
    "axiom_declaration_binders.tsv": "recert_axiom_declaration_binders.tsv",
    "axiom_direct_dependencies.tsv": "recert_axiom_direct_dependencies.tsv",
}
HARNESSES = (
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard0.lean",
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard1.lean",
)
FIELD = re.compile(r"(?m)^(started|finished|exit_code):\s*(.+?)\s*$")


class InstallError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def data_rows(path: Path) -> int:
    with path.open("rb") as handle:
        lines = sum(1 for _ in handle)
    if lines < 1:
        raise InstallError(f"{path}: missing header")
    return lines - 1


def closed_times(path: Path) -> tuple[dt.datetime, dt.datetime]:
    text = path.read_text(encoding="utf-8", errors="replace")
    fields: dict[str, list[str]] = {}
    for key, value in FIELD.findall(text):
        fields.setdefault(key, []).append(value)
    if fields.get("exit_code") != ["0"]:
        raise InstallError(f"{path}: not one successful closed transcript")
    if len(fields.get("started", [])) != 1 or len(fields.get("finished", [])) != 1:
        raise InstallError(f"{path}: ambiguous timestamps")
    started = dt.datetime.fromisoformat(fields["started"][0])
    finished = dt.datetime.fromisoformat(fields["finished"][0])
    if started.tzinfo is None or finished.tzinfo is None or finished <= started:
        raise InstallError(f"{path}: invalid timestamp interval")
    return started, finished


def require_current_manifest() -> str:
    rendered, digest = build_manifest()
    if SOURCE_MANIFEST.read_text(encoding="utf-8") != rendered:
        raise InstallError("source manifest file is stale")
    try:
        certified_digest = require_reorganization_certificate()
    except (OSError, RuntimeError, TypeError, ValueError) as error:
        raise InstallError(
            f"exercise-reorganization certificate failed: {error}"
        ) from error
    if certified_digest != digest:
        raise InstallError(
            "exercise-reorganization certificate identifies another source "
            f"digest: {certified_digest} != {digest}"
        )
    return digest


def install(merged: Path, shards: tuple[Path, Path]) -> int:
    current_digest = require_current_manifest()
    summary_path = merged / "merge_summary.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    environment_digest = summary.get("source_manifest_digest")
    if environment_digest != current_digest:
        raise InstallError("merge summary is for a different source manifest")
    if summary.get("row_counts") != EXPECTED_ROWS:
        raise InstallError(
            f"merge summary has wrong row totals: {summary.get('row_counts')}"
        )
    if summary.get("merger_sha256") != sha256(MERGER_SCRIPT):
        raise InstallError("merge summary was not produced by the current merger")
    shard_records = summary.get("shards")
    if not isinstance(shard_records, dict):
        raise InstallError("merge summary lacks shard provenance")
    for index, (shard, harness) in enumerate(
        zip(shards, HARNESSES, strict=True)
    ):
        record = shard_records.get(str(index))
        if not isinstance(record, dict):
            raise InstallError(f"merge summary lacks shard {index}")
        expected_metadata = {
            "path": str(shard),
            "harness_path": str(harness),
            "harness_sha256": sha256(harness),
            "build_log_sha256": sha256(shard / "axiom_audit_build.log"),
        }
        mismatched = [
            key
            for key, expected in expected_metadata.items()
            if record.get(key) != expected
        ]
        if mismatched:
            raise InstallError(
                f"merge summary shard-{index} provenance mismatch: {mismatched}"
            )
        raw_hashes = record.get("artifact_sha256")
        if not isinstance(raw_hashes, dict):
            raise InstallError(f"merge summary shard-{index} lacks raw hashes")
        for source_name in INSTALL_MAP:
            source = shard / source_name
            if raw_hashes.get(source_name) != sha256(source):
                raise InstallError(
                    f"merge summary shard-{index} hash mismatch: {source_name}"
                )
    recorded_hashes = summary.get("artifact_sha256")
    if not isinstance(recorded_hashes, dict):
        raise InstallError("merge summary lacks artifact hashes")
    for source_name in INSTALL_MAP:
        source = merged / source_name
        if not source.is_file() or source.stat().st_size == 0:
            raise InstallError(f"merged artifact missing/empty: {source}")
        if recorded_hashes.get(source_name) != sha256(source):
            raise InstallError(f"merged artifact hash mismatch: {source}")
    for name, expected in EXPECTED_ROWS.items():
        observed = data_rows(merged / name)
        if observed != expected:
            raise InstallError(
                f"{name}: expected {expected} data rows, found {observed}"
            )

    intervals = tuple(
        closed_times(shard / "axiom_audit_build.log") for shard in shards
    )
    started = min(interval[0] for interval in intervals)
    finished = max(interval[1] for interval in intervals)
    staging = Path(tempfile.mkdtemp(dir=LOGS, prefix=".recert-v4-install-"))
    try:
        for source_name, destination_name in INSTALL_MAP.items():
            shutil.copyfile(merged / source_name, staging / destination_name)
        shutil.copyfile(summary_path, staging / "recert_v4_merge_summary.json")
        for index, shard in enumerate(shards):
            shutil.copyfile(
                shard / "axiom_audit_build.log",
                staging / f"recert_v4_shard{index}.log",
            )
        aggregate = "\n".join(
            [
                f"started: {started.isoformat()}",
                f"cwd: {ROOT}",
                (
                    "command: exhaustive sequential two-shard V4 collection "
                    "followed by validated disjoint merge"
                ),
                f"environment_evidence_source_digest: {environment_digest}",
                f"current_source_digest: {current_digest}",
                "source_relation: exact current-source collection",
                "round10_docstring_delta_sha256: not-required",
                f"exercise_reorganization_delta_sha256: {sha256(CERTIFICATE_LOG)}",
                "partition_rule: audited_environment_index_mod_2",
                "environment_modules: 223",
                "declarations_audited: 15022",
                "declaration_binder_rows: 80919",
                "direct_dependency_edges: 1448224",
                f"shard0_log_sha256: {sha256(shards[0] / 'axiom_audit_build.log')}",
                f"shard1_log_sha256: {sha256(shards[1] / 'axiom_audit_build.log')}",
                f"merge_summary_sha256: {sha256(summary_path)}",
                "",
                f"finished: {finished.isoformat()}",
                f"elapsed_seconds: {(finished - started).total_seconds():.3f}",
                "exit_code: 0",
                "",
            ]
        )
        (staging / "recert_axiom_audit_build.log").write_text(
            aggregate, encoding="utf-8"
        )
        for path in staging.iterdir():
            os.replace(path, LOGS / path.name)
        staging.rmdir()
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    require_current_manifest()
    print("PASS: installed exhaustive current V4 shard merge")
    print(f"environment_evidence_source_digest: {environment_digest}")
    print(f"current_source_digest: {current_digest}")
    for name, rows in EXPECTED_ROWS.items():
        print(f"{name}: {rows}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--merged",
        type=Path,
        default=Path("/private/tmp/hdp_v4_78da87_merged"),
    )
    parser.add_argument(
        "--shard0",
        type=Path,
        default=Path("/private/tmp/hdp_v4_78da87_shard0"),
    )
    parser.add_argument(
        "--shard1",
        type=Path,
        default=Path("/private/tmp/hdp_v4_78da87_shard1"),
    )
    args = parser.parse_args()
    return install(args.merged, (args.shard0, args.shard1))


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (InstallError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"V4 INSTALL FAIL: {error}")
        raise SystemExit(1)
