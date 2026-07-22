#!/usr/bin/env python3
"""Merge and validate the two exhaustive final-recertification V4 shards.

The two Lean harnesses enumerate the same deterministic environment and route
alternating audited declarations to disjoint local-output directories.  This
script verifies successful shard runs, identical module evidence, each
shard-specific private calibration, disjoint and complete declaration
identities, exact binder totals, and the current exhaustive row counts
before producing the canonical raw V4 files.
The ordinary ``axiom_audit.py analyze`` pass then performs the full semantic
schema, axiom, telescope, dependency, module, and V3 reconciliation checks.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import json
import os
import re
import shlex
import sys
import tempfile
from pathlib import Path

from source_manifest import build_manifest as build_source_manifest


EXPECTED_DECLARATIONS = 15_022
EXPECTED_BINDERS = 80_919
EXPECTED_EDGES = 1_448_224
SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
DEFAULT_HARNESSES = (
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard0.lean",
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard1.lean",
)

TSV_FILES = (
    "axiom_audit.tsv",
    "axiom_declaration_types.tsv",
    "axiom_declaration_binders.tsv",
    "axiom_direct_dependencies.tsv",
)
IDENTICAL_FILES = ("axiom_modules.txt",)
CALIBRATION = "axiom_calibration.tsv"
CALIBRATION_COLUMNS = ("label", "name", "has_sorryAx", "axioms")
TSV_HEADERS = {
    "axiom_audit.tsv": (
        "module",
        "name",
        "kind",
        "is_private",
        "private_user_name",
        "is_internal",
        "axioms",
    ),
    "axiom_declaration_types.tsv": (
        "module",
        "name",
        "kind",
        "is_private",
        "private_user_name",
        "is_internal",
        "level_params",
        "binder_count",
        "type_raw",
        "conclusion_raw",
    ),
    "axiom_declaration_binders.tsv": (
        "module",
        "name",
        "private_user_name",
        "kind",
        "binder_index",
        "binder_name",
        "binder_info",
        "binder_type_raw",
    ),
    "axiom_direct_dependencies.tsv": (
        "source_module",
        "source",
        "source_kind",
        "origin",
        "target_module",
        "target",
    ),
}
REFERENCE_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "is_unsafe",
    "is_partial",
)


class MergeError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def completed_shard_log(
    path: Path, harness: Path, expected_source_digest: str
) -> None:
    text = path.read_text(encoding="utf-8", errors="replace")
    exits = re.findall(r"(?m)^exit_code:\s*(-?\d+)\s*$", text)
    if exits != ["0"]:
        raise MergeError(f"{path}: expected one exit_code 0 footer, found {exits}")
    if not text.rstrip().endswith("exit_code: 0"):
        raise MergeError(f"{path}: exit footer is not at EOF")
    fields = {
        key: re.findall(rf"(?m)^{key}:\s*(.+?)\s*$", text)
        for key in (
            "started",
            "cwd",
            "command",
            "source_manifest_digest",
            "harness_sha256",
            "finished",
            "elapsed_seconds",
        )
    }
    if any(len(values) != 1 for values in fields.values()):
        raise MergeError(f"{path}: incomplete or duplicated transcript metadata")
    if fields["cwd"][0] != str(ROOT):
        raise MergeError(f"{path}: wrong working directory")
    if fields["source_manifest_digest"][0] != expected_source_digest:
        raise MergeError(f"{path}: wrong source manifest digest")
    if fields["harness_sha256"][0] != sha256(harness):
        raise MergeError(f"{path}: harness digest does not match executed harness")
    expected_command = [
        str(Path.home() / ".elan" / "bin" / "lake"),
        "env",
        "lean",
        "-DmaxSynthPendingDepth=3",
        "-DrelaxedAutoImplicit=false",
        str(harness),
    ]
    if shlex.split(fields["command"][0]) != expected_command:
        raise MergeError(f"{path}: wrong shard command")
    started = dt.datetime.fromisoformat(fields["started"][0])
    finished = dt.datetime.fromisoformat(fields["finished"][0])
    if started.tzinfo is None or finished.tzinfo is None or finished <= started:
        raise MergeError(f"{path}: invalid transcript timestamps")
    elapsed = float(fields["elapsed_seconds"][0])
    if abs((finished - started).total_seconds() - elapsed) > 0.01:
        raise MergeError(f"{path}: inconsistent elapsed time")


def validate_calibration(path: Path, shard_index: int) -> bytes:
    raw = path.read_bytes()
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != CALIBRATION_COLUMNS:
            raise MergeError(f"{path}: invalid calibration header")
        rows = list(reader)
    if len(rows) != 2 or {row["label"] for row in rows} != {
        "known_exercise_sorry",
        "planted_private_sorry",
    }:
        raise MergeError(f"{path}: invalid calibration label set")
    by_label = {row["label"]: row for row in rows}
    exercise = by_label["known_exercise_sorry"]
    if (
        exercise["name"] != "HDP.Chapter1.exercise_1_2"
        or exercise["has_sorryAx"] != "true"
        or set(filter(None, exercise["axioms"].split(";")))
        != {"propext", "sorryAx", "Classical.choice", "Quot.sound"}
    ):
        raise MergeError(f"{path}: invalid known-exercise calibration row")
    private = by_label["planted_private_sorry"]
    if (
        private["has_sorryAx"] != "true"
        or set(filter(None, private["axioms"].split(";"))) != {"sorryAx"}
        or "_private" not in private["name"]
        or f"AxiomAuditShard{shard_index}" not in private["name"]
        or not private["name"].endswith(".v4_private_bad_calibration")
    ):
        raise MergeError(f"{path}: invalid private calibration row")
    return raw


def merge_tsv(
    name: str, shards: tuple[Path, Path], output: Path
) -> tuple[int, tuple[int, int]]:
    headers: list[bytes] = []
    count = 0
    shard_counts = [0, 0]
    expected_header = ("\t".join(TSV_HEADERS[name]) + "\n").encode()
    expected_tabs = len(TSV_HEADERS[name]) - 1
    with output.open("wb") as destination:
        for index, shard in enumerate(shards):
            path = shard / name
            with path.open("rb") as source:
                header = source.readline()
                if header != expected_header:
                    raise MergeError(f"{path}: invalid TSV header")
                headers.append(header)
                if index == 0:
                    destination.write(header)
                for line in source:
                    if not line.strip():
                        raise MergeError(f"{path}: blank data row")
                    if line.count(b"\t") != expected_tabs:
                        raise MergeError(f"{path}: malformed TSV data row")
                    destination.write(line)
                    count += 1
                    shard_counts[index] += 1
    if headers[0] != headers[1]:
        raise MergeError(f"{name}: shard headers differ")
    return count, (shard_counts[0], shard_counts[1])


def declaration_names(path: Path) -> tuple[set[str], dict[str, int]]:
    csv.field_size_limit(sys.maxsize)
    names: set[str] = set()
    binder_counts: dict[str, int] = {}
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            name = row["name"]
            if name in names:
                raise MergeError(f"{path}: duplicate declaration {name}")
            names.add(name)
            if "binder_count" in row:
                binder_counts[name] = int(row["binder_count"])
    return names, binder_counts


def declaration_shapes(
    path: Path, expected_columns: tuple[str, ...]
) -> dict[str, tuple[str, str, str, str]]:
    shapes: dict[str, tuple[str, str, str, str]] = {}
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != expected_columns:
            raise MergeError(f"{path}: invalid declaration-universe header")
        for row in reader:
            name = row["name"]
            if not name or name in shapes:
                raise MergeError(f"{path}: blank/duplicate declaration {name!r}")
            shapes[name] = (
                row["module"],
                row["is_private"],
                row["private_user_name"],
                row["is_internal"],
            )
    return shapes


def binder_keys(path: Path) -> set[tuple[str, int]]:
    keys: set[tuple[str, int]] = set()
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            key = (row["name"], int(row["binder_index"]))
            if key in keys:
                raise MergeError(f"{path}: duplicate binder key {key}")
            keys.add(key)
    return keys


def main() -> int:
    parser = argparse.ArgumentParser()
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
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("/private/tmp/hdp_v4_78da87_merged"),
    )
    parser.add_argument(
        "--reference",
        type=Path,
        help=(
            "optional independent V7 declaration universe; when omitted, "
            "the later V7 environment-name-set reconciliation supplies this "
            "cross-check"
        ),
    )
    parser.add_argument(
        "--harness0", type=Path, default=DEFAULT_HARNESSES[0]
    )
    parser.add_argument(
        "--harness1", type=Path, default=DEFAULT_HARNESSES[1]
    )
    args = parser.parse_args()
    shards = (args.shard0, args.shard1)
    harnesses = (args.harness0, args.harness1)
    if args.output.exists():
        raise MergeError(f"refusing to overwrite merge output: {args.output}")
    args.output.parent.mkdir(parents=True, exist_ok=True)

    rendered_manifest, source_digest = build_source_manifest()
    if SOURCE_MANIFEST.read_text(encoding="utf-8") != rendered_manifest:
        raise MergeError("source manifest is not current")

    for shard, harness in zip(shards, harnesses, strict=True):
        completed_shard_log(
            shard / "axiom_audit_build.log", harness, source_digest
        )
    for index, harness in enumerate(harnesses):
        text = harness.read_text(encoding="utf-8")
        required = (
            f"/private/tmp/hdp_v4_78da87_shard{index}/axiom_audit.tsv",
            f"if currentIndex % 2 == {index} then",
        )
        if any(fragment not in text for fragment in required):
            raise MergeError(f"{harness}: wrong shard-{index} partition harness")

    temporary = tempfile.mkdtemp(
        dir=args.output.parent, prefix=f".{args.output.name}.staging-"
    )
    work_output = Path(temporary)
    for name in IDENTICAL_FILES:
        left = (shards[0] / name).read_bytes()
        right = (shards[1] / name).read_bytes()
        if left != right:
            raise MergeError(f"{name}: shard evidence differs")
        (work_output / name).write_bytes(left)
    calibrations = tuple(
        validate_calibration(shard / CALIBRATION, index)
        for index, shard in enumerate(shards)
    )
    # The private calibration declaration is necessarily mangled with the
    # shard module name, so the two valid rows cannot be byte-identical.
    # Select shard 0 deterministically for the canonical V4 artifact.
    (work_output / CALIBRATION).write_bytes(calibrations[0])

    merged = {
        name: merge_tsv(name, shards, work_output / name)
        for name in TSV_FILES
    }
    row_counts = {name: values[0] for name, values in merged.items()}
    shard_row_counts = {
        str(index): {
            name: values[1][index] for name, values in merged.items()
        }
        for index in range(2)
    }
    if row_counts["axiom_audit.tsv"] != EXPECTED_DECLARATIONS:
        raise MergeError(f"unexpected audit rows: {row_counts}")
    if row_counts["axiom_declaration_types.tsv"] != EXPECTED_DECLARATIONS:
        raise MergeError(f"unexpected type rows: {row_counts}")
    if row_counts["axiom_declaration_binders.tsv"] != EXPECTED_BINDERS:
        raise MergeError(f"unexpected binder rows: {row_counts}")
    if row_counts["axiom_direct_dependencies.tsv"] != EXPECTED_EDGES:
        raise MergeError(f"unexpected dependency rows: {row_counts}")

    audit_names, _ = declaration_names(work_output / "axiom_audit.tsv")
    type_names, expected_binders = declaration_names(
        work_output / "axiom_declaration_types.tsv"
    )
    if audit_names != type_names:
        raise MergeError(
            "audit/type declaration sets differ: "
            f"audit_only={len(audit_names - type_names)} "
            f"type_only={len(type_names - audit_names)}"
        )
    keys = binder_keys(work_output / "axiom_declaration_binders.tsv")
    if len(keys) != EXPECTED_BINDERS:
        raise MergeError(f"unexpected unique binder keys: {len(keys)}")
    if sum(expected_binders.values()) != EXPECTED_BINDERS:
        raise MergeError(
            f"type telescope total is {sum(expected_binders.values())}, "
            f"expected {EXPECTED_BINDERS}"
        )
    for name, count in expected_binders.items():
        if any((name, index) not in keys for index in range(count)):
            raise MergeError(f"incomplete binder index set for {name}")

    audit_shapes = declaration_shapes(
        work_output / "axiom_audit.tsv", TSV_HEADERS["axiom_audit.tsv"]
    )
    reference_record: dict[str, object] = {
        "status": "DEFERRED_TO_V7_ENVIRONMENT_NAME_SET_RECONCILIATION"
    }
    if args.reference is not None:
        reference_shapes = declaration_shapes(args.reference, REFERENCE_COLUMNS)
        if len(reference_shapes) != EXPECTED_DECLARATIONS:
            raise MergeError(
                f"{args.reference}: expected {EXPECTED_DECLARATIONS} declarations"
            )
        if audit_shapes != reference_shapes:
            raise MergeError(
                "merged declaration identities/shapes differ from the independent "
                "exhaustive definition-constant universe"
            )
        reference_record = {
            "status": "PASS",
            "path": str(args.reference),
            "rows": len(reference_shapes),
            "sha256": sha256(args.reference),
        }

    summary = {
        "schema": "pass07-v4-two-shard-merge-v2",
        "partition_rule": "audited_environment_index_mod_2",
        "merger_sha256": sha256(SCRIPT),
        "source_manifest_digest": source_digest,
        "partition_completeness_basis": (
            "both shards enumerate an identical 223-module environment; "
            "audited_environment_index_mod_2 is exhaustive and disjoint; "
            "merged audit/type identities and all binder keys are unique; "
            "current exact row totals are enforced"
        ),
        "reference_universe": reference_record,
        "row_counts": row_counts,
        "shard_row_counts": shard_row_counts,
        "shards": {
            str(index): {
                "path": str(shard),
                "harness_path": str(harnesses[index]),
                "harness_sha256": sha256(harnesses[index]),
                "build_log_sha256": sha256(shard / "axiom_audit_build.log"),
                "artifact_sha256": {
                    name: sha256(shard / name)
                    for name in (*IDENTICAL_FILES, CALIBRATION, *TSV_FILES)
                },
            }
            for index, shard in enumerate(shards)
        },
        "artifact_sha256": {
            name: sha256(work_output / name)
            for name in (*IDENTICAL_FILES, CALIBRATION, *TSV_FILES)
        },
    }
    summary_path = work_output / "merge_summary.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    os.replace(work_output, args.output)
    print("PASS: exhaustive V4 two-shard merge")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MergeError, OSError, ValueError, csv.Error) as exc:
        print(f"V4 SHARD MERGE FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
