#!/usr/bin/env python3
"""Create/check the atomic completion manifest for the fresh Pass 07 V4 audit.

The exhaustive Lean dump is produced in two deterministic parity shards to
avoid serial cloud-drive writes.  The shard merger proves disjoint/comprehensive
declaration identities and exact row totals; ``axiom_audit.py analyze`` and the
existing V4 static checker then validate the merged schemas, telescopes,
dependencies, module coverage, calibration, axioms, and V3 reconciliation.
Only after all of those checks pass does this script bind every raw artifact,
shard transcript, and harness to the current source manifest.
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
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from source_manifest import build_manifest as build_source_manifest


SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[3]
VERIFICATION = ROOT / "HighDimensionalProbability" / "Verification"
LOGS = VERIFICATION / "logs"
WITNESSES = VERIFICATION / "scripts" / "witnesses"
OUTPUT = LOGS / "pass07_v4_completion.json"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
WHOLE_BUILD_LOG = LOGS / "pass07_final_whole_build.log"
MERGE_OUTPUT = Path("/tmp/pass07_v4_merged_fresh")
SHARD_DIRS = (
    Path("/tmp/pass07_v4_shard0"),
    Path("/tmp/pass07_v4_shard1"),
)
SCRATCH_HARNESSES = (
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard0.lean",
    ROOT / ".audit_work" / "verification" / "AxiomAuditShard1.lean",
)

EXPECTED_MISSING = {
    "MatrixConcentration.Appendix_RosenthalPinelis",
    "MatrixConcentration.Chapter1_Introduction",
    "MatrixConcentration.Chapter6_SumOfBoundedRandomMatrices",
    "MatrixConcentration.Chapter7_IntrinsicDimension",
}
EXPECTED_SUMMARY = {
    "verdict": "INCOMPLETE",
    "declarations_audited": "15022",
    "declaration_type_rows": "15022",
    "declaration_binder_rows": "80919",
    "direct_dependency_edges": "1448224",
    "expected_modules": "227",
    "environment_modules": "223",
    "sorryAx_declarations": "228",
    "nonstandard_non_sorry_axiom_declarations": "0",
    "project_axiom_declarations": "0",
    "unexpected_user_facing_opaque_declarations": "0",
    "v3_reconciliation": "PASS",
    "type_telescope_dump": "PASS",
    "direct_dependency_dump": "PASS",
    "calibration": "PASS",
}
ARTIFACTS = {
    "source_manifest.txt": SOURCE_MANIFEST,
    "pass07_final_whole_build.log": WHOLE_BUILD_LOG,
    "axiom_audit.tsv": LOGS / "axiom_audit.tsv",
    "axiom_declaration_types.tsv": LOGS / "axiom_declaration_types.tsv",
    "axiom_declaration_binders.tsv": LOGS / "axiom_declaration_binders.tsv",
    "axiom_direct_dependencies.tsv": LOGS / "axiom_direct_dependencies.tsv",
    "axiom_modules.txt": LOGS / "axiom_modules.txt",
    "axiom_calibration.tsv": LOGS / "axiom_calibration.tsv",
    "axiom_audit_build.log": LOGS / "axiom_audit_build.log",
    "pass07_v4_analyze.log": LOGS / "pass07_v4_analyze.log",
    "axiom_audit_summary.txt": LOGS / "axiom_audit_summary.txt",
    "axiom_module_coverage.txt": LOGS / "axiom_module_coverage.txt",
    "axiom_audit_exceedances.tsv": LOGS / "axiom_audit_exceedances.tsv",
    "axiom_and_opaque_declarations.tsv": (
        LOGS / "axiom_and_opaque_declarations.tsv"
    ),
    "axiom_audit_full_surface_attempt.log": (
        LOGS / "axiom_audit_full_surface_attempt.log"
    ),
    "v3_direct_sorry_declarations.tsv": (
        LOGS / "v3_direct_sorry_declarations.tsv"
    ),
    "definition_constants.tsv": LOGS / "definition_constants.tsv",
    "definition_sanity_build.log": LOGS / "definition_sanity_build.log",
    "pass07_v4_shard0.log": LOGS / "pass07_v4_shard0.log",
    "pass07_v4_shard1.log": LOGS / "pass07_v4_shard1.log",
    "pass07_v4_merge.log": LOGS / "pass07_v4_merge.log",
    "pass07_v4_merge_summary.json": LOGS / "pass07_v4_merge_summary.json",
    "Pass07FreshV4AxiomAuditShard0.lean": (
        WITNESSES / "Pass07FreshV4AxiomAuditShard0.lean"
    ),
    "Pass07FreshV4AxiomAuditShard1.lean": (
        WITNESSES / "Pass07FreshV4AxiomAuditShard1.lean"
    ),
    "scratch_AxiomAuditShard0.lean": SCRATCH_HARNESSES[0],
    "scratch_AxiomAuditShard1.lean": SCRATCH_HARNESSES[1],
    "merge_pass07_v4_shards.py": (
        VERIFICATION / "scripts" / "merge_pass07_v4_shards.py"
    ),
    "pass07_v4_completion.py": SCRIPT,
    "axiom_audit.py": VERIFICATION / "scripts" / "axiom_audit.py",
    "run_all_static_checks.py": (
        VERIFICATION / "scripts" / "run_all_static_checks.py"
    ),
}


class CompletionError(RuntimeError):
    pass


@dataclass(frozen=True)
class LogRecord:
    path: Path
    started: dt.datetime
    finished: dt.datetime
    elapsed_seconds: float
    command: tuple[str, ...]
    text: str


def sha256(path: Path) -> str:
    before = path.stat()
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    after = path.stat()
    if (
        before.st_size,
        before.st_mtime_ns,
        before.st_ino,
    ) != (
        after.st_size,
        after.st_mtime_ns,
        after.st_ino,
    ):
        raise CompletionError(f"artifact changed while hashing: {path}")
    return digest.hexdigest()


def completed_log(
    path: Path,
    *,
    expected_exit: int,
    expected_command: tuple[str, ...] | None = None,
) -> LogRecord:
    if not path.is_file() or path.is_symlink() or path.stat().st_size == 0:
        raise CompletionError(f"required transcript is missing/unsafe: {path}")
    text = path.read_text(encoding="utf-8", errors="replace")
    exits = re.findall(r"(?m)^exit_code:\s*(-?\d+)\s*$", text)
    if exits != [str(expected_exit)]:
        raise CompletionError(
            f"{path}: expected exactly one exit {expected_exit} footer, found {exits}"
        )
    if not text.rstrip().endswith(f"exit_code: {expected_exit}"):
        raise CompletionError(f"{path}: exit footer is not at EOF")
    fields = {
        key: re.findall(rf"(?m)^{key}:\s*(.+?)\s*$", text)
        for key in ("started", "cwd", "command", "finished", "elapsed_seconds")
    }
    if any(len(values) != 1 for values in fields.values()):
        raise CompletionError(f"{path}: incomplete or duplicated transcript metadata")
    if fields["cwd"][0] != str(ROOT):
        raise CompletionError(f"{path}: wrong working directory")
    try:
        started = dt.datetime.fromisoformat(fields["started"][0])
        finished = dt.datetime.fromisoformat(fields["finished"][0])
        elapsed = float(fields["elapsed_seconds"][0])
        command = tuple(shlex.split(fields["command"][0]))
    except (ValueError, TypeError) as exc:
        raise CompletionError(f"{path}: malformed transcript metadata") from exc
    if (
        started.tzinfo is None
        or finished.tzinfo is None
        or finished <= started
        or abs((finished - started).total_seconds() - elapsed) > 0.01
    ):
        raise CompletionError(f"{path}: inconsistent transcript timing")
    if expected_command is not None and command != expected_command:
        raise CompletionError(
            f"{path}: command={command!r}, expected={expected_command!r}"
        )
    return LogRecord(path, started, finished, elapsed, command, text)


def source_digest() -> str:
    path = SOURCE_MANIFEST
    rendered, digest = build_source_manifest()
    if path.read_text(encoding="utf-8") != rendered:
        raise CompletionError("source manifest is not current")
    return digest


def parse_summary() -> dict[str, str]:
    path = LOGS / "axiom_audit_summary.txt"
    values: dict[str, str] = {}
    lines = path.read_text(encoding="utf-8").splitlines()
    for line in lines:
        if ": " in line:
            key, value = line.split(": ", 1)
            if key in values:
                raise CompletionError(f"{path}: duplicate summary key {key}")
            values[key] = value
    for key, expected in EXPECTED_SUMMARY.items():
        if values.get(key) != expected:
            raise CompletionError(
                f"{path}: {key}={values.get(key)!r}, expected {expected!r}"
            )
    try:
        hard_start = lines.index("[hard_failures]") + 1
        incomplete_start = lines.index("[incomplete_reasons]") + 1
        v3_start = lines.index("[v3_only_declarations]")
    except ValueError as exc:
        raise CompletionError(f"{path}: required status sections are missing") from exc
    hard_failures = [
        line for line in lines[hard_start:incomplete_start - 1] if line
    ]
    incomplete_reasons = [
        line for line in lines[incomplete_start:v3_start] if line
    ]
    if hard_failures != ["(none)"]:
        raise CompletionError(f"{path}: hard failures are present: {hard_failures}")
    if incomplete_reasons != [
        "4 expected modules missing from environment",
        "one or more required orphan candidates were not imported",
    ]:
        raise CompletionError(
            f"{path}: unexpected incompleteness reasons: {incomplete_reasons}"
        )
    return values


def missing_modules() -> list[str]:
    lines = (LOGS / "axiom_module_coverage.txt").read_text(
        encoding="utf-8"
    ).splitlines()
    try:
        start = lines.index("[missing_modules]") + 1
        end = lines.index("[extra_modules]")
    except ValueError as exc:
        raise CompletionError("module coverage sections are missing") from exc
    observed = {line for line in lines[start:end] if line}
    raw_observed = [line for line in lines[start:end] if line]
    if len(raw_observed) != len(observed):
        raise CompletionError("module coverage contains duplicate missing modules")
    if observed != EXPECTED_MISSING:
        raise CompletionError(f"wrong V4 missing-module set: {sorted(observed)}")
    return sorted(observed)


def appendix_sorry_count() -> int:
    path = LOGS / "axiom_audit.tsv"
    csv.field_size_limit(sys.maxsize)
    count = 0
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            axioms = set(filter(None, row["axioms"].split(";")))
            if (
                row["module"].startswith("HighDimensionalProbability.Appendix")
                and "sorryAx" in axioms
            ):
                count += 1
    if count:
        raise CompletionError(f"Appendix has {count} sorryAx declarations")
    return count


def validate_merge_summary(source_digest_value: str) -> dict[str, object]:
    path = LOGS / "pass07_v4_merge_summary.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    expected_counts = {
        "axiom_audit.tsv": 15022,
        "axiom_declaration_types.tsv": 15022,
        "axiom_declaration_binders.tsv": 80919,
        "axiom_direct_dependencies.tsv": 1448224,
    }
    if data.get("row_counts") != expected_counts:
        raise CompletionError(f"{path}: wrong merge row counts")
    if (
        data.get("schema") != "pass07-v4-two-shard-merge-v2"
        or data.get("partition_rule") != "audited_environment_index_mod_2"
        or data.get("source_manifest_digest") != source_digest_value
        or data.get("merger_sha256")
        != sha256(VERIFICATION / "scripts" / "merge_pass07_v4_shards.py")
    ):
        raise CompletionError(f"{path}: wrong merge identity/provenance fields")
    reference = data.get("reference_universe")
    reference_path = LOGS / "definition_constants.tsv"
    if reference != {
        "path": str(reference_path),
        "rows": 15022,
        "sha256": sha256(reference_path),
    }:
        raise CompletionError(f"{path}: wrong independent declaration universe")
    shard_counts = data.get("shard_row_counts")
    if not isinstance(shard_counts, dict) or set(shard_counts) != {"0", "1"}:
        raise CompletionError(f"{path}: invalid shard row-count table")
    for index in ("0", "1"):
        rows = shard_counts[index]
        if not isinstance(rows, dict) or set(rows) != set(expected_counts):
            raise CompletionError(f"{path}: malformed shard {index} row counts")
        if (
            rows["axiom_audit.tsv"] != 7511
            or rows["axiom_declaration_types.tsv"] != 7511
            or any(not isinstance(value, int) or value <= 0 for value in rows.values())
        ):
            raise CompletionError(f"{path}: invalid shard {index} partition counts")
    for name, total in expected_counts.items():
        if sum(shard_counts[index][name] for index in ("0", "1")) != total:
            raise CompletionError(f"{path}: shard counts do not sum for {name}")

    shards = data.get("shards")
    if not isinstance(shards, dict) or set(shards) != {"0", "1"}:
        raise CompletionError(f"{path}: invalid shard provenance table")
    expected_artifact_names = {
        "axiom_modules.txt",
        "axiom_calibration.tsv",
        "axiom_audit.tsv",
        "axiom_declaration_types.tsv",
        "axiom_declaration_binders.tsv",
        "axiom_direct_dependencies.tsv",
    }
    hex_digest = re.compile(r"[0-9a-f]{64}")
    for index in (0, 1):
        entry = shards[str(index)]
        if not isinstance(entry, dict):
            raise CompletionError(f"{path}: shard {index} entry is not an object")
        witness = WITNESSES / f"Pass07FreshV4AxiomAuditShard{index}.lean"
        if (
            entry.get("path") != str(SHARD_DIRS[index])
            or entry.get("harness_path") != str(SCRATCH_HARNESSES[index])
            or entry.get("harness_sha256") != sha256(SCRATCH_HARNESSES[index])
            or sha256(witness) != entry.get("harness_sha256")
            or entry.get("build_log_sha256")
            != sha256(LOGS / f"pass07_v4_shard{index}.log")
        ):
            raise CompletionError(f"{path}: shard {index} provenance mismatch")
        raw_hashes = entry.get("artifact_sha256")
        if (
            not isinstance(raw_hashes, dict)
            or set(raw_hashes) != expected_artifact_names
            or any(
                not isinstance(value, str) or hex_digest.fullmatch(value) is None
                for value in raw_hashes.values()
            )
        ):
            raise CompletionError(f"{path}: invalid shard {index} raw hashes")
    hashes = data.get("artifact_sha256")
    if not isinstance(hashes, dict) or set(hashes) != expected_artifact_names:
        raise CompletionError(f"{path}: missing artifact hashes")
    for name in expected_artifact_names:
        if hashes.get(name) != sha256(LOGS / name):
            raise CompletionError(f"{path}: merged hash mismatch for {name}")
    return data


def require_python_command(
    record: LogRecord,
    script: Path,
    arguments: tuple[str, ...],
) -> None:
    command = record.command
    if (
        len(command) < 3
        or not Path(command[0]).name.startswith("python")
        or command[1:] != ("-B", str(script), *arguments)
    ):
        raise CompletionError(f"{record.path}: wrong Python command {command!r}")


def validate_transcripts(merge_summary: dict[str, object]) -> dict[str, LogRecord]:
    lake = str(Path.home() / ".elan" / "bin" / "lake")
    whole = completed_log(
        WHOLE_BUILD_LOG,
        expected_exit=0,
        expected_command=(lake, "build"),
    )
    if "Build completed successfully (8670 jobs)." not in whole.text:
        raise CompletionError(f"{WHOLE_BUILD_LOG}: missing exact whole-build success")

    shard_records: list[LogRecord] = []
    for index in (0, 1):
        record = completed_log(
            LOGS / f"pass07_v4_shard{index}.log",
            expected_exit=0,
            expected_command=(
                lake,
                "env",
                "lean",
                "-DmaxSynthPendingDepth=3",
                "-DrelaxedAutoImplicit=false",
                str(SCRATCH_HARNESSES[index]),
            ),
        )
        shard_records.append(record)

    merge = completed_log(LOGS / "pass07_v4_merge.log", expected_exit=0)
    require_python_command(
        merge,
        VERIFICATION / "scripts" / "merge_pass07_v4_shards.py",
        (
            "--shard0",
            str(SHARD_DIRS[0]),
            "--shard1",
            str(SHARD_DIRS[1]),
            "--output",
            str(MERGE_OUTPUT),
        ),
    )
    marker = "PASS: exhaustive V4 two-shard merge\n"
    if marker not in merge.text or "\n\nfinished:" not in merge.text:
        raise CompletionError(f"{merge.path}: merge result payload is missing")
    payload = merge.text.split(marker, 1)[1].split("\n\nfinished:", 1)[0]
    try:
        logged_summary = json.loads(payload)
    except json.JSONDecodeError as exc:
        raise CompletionError(f"{merge.path}: invalid logged merge JSON") from exc
    if logged_summary != merge_summary:
        raise CompletionError(f"{merge.path}: logged/file merge summaries differ")

    analyze = completed_log(LOGS / "pass07_v4_analyze.log", expected_exit=2)
    require_python_command(
        analyze,
        VERIFICATION / "scripts" / "axiom_audit.py",
        (
            "analyze",
            "--v3-sorry-declarations",
            str(LOGS / "v3_direct_sorry_declarations.tsv"),
        ),
    )
    for required in (
        "verdict: INCOMPLETE",
        "declarations_audited: 15022",
        "type_telescope_dump: PASS",
        "direct_dependency_dump: PASS",
        "v3_reconciliation: PASS",
    ):
        if required not in analyze.text:
            raise CompletionError(f"{analyze.path}: missing analyzer result {required}")

    aggregate = completed_log(LOGS / "axiom_audit_build.log", expected_exit=0)
    require_python_command(
        aggregate,
        VERIFICATION / "scripts" / "run_all_static_checks.py",
        ("v4",),
    )
    if "V4_STATIC_OK" not in aggregate.text:
        raise CompletionError(f"{aggregate.path}: aggregate V4 validator did not pass")

    full_surface = completed_log(
        LOGS / "axiom_audit_full_surface_attempt.log", expected_exit=1
    )
    if (
        "AxiomAuditFullSurface.lean" not in " ".join(full_surface.command)
        or "MatrixConcentration.Appendix_RosenthalPinelis" not in full_surface.text
    ):
        raise CompletionError(f"{full_surface.path}: wrong full-surface boundary run")
    definition = completed_log(LOGS / "definition_sanity_build.log", expected_exit=0)
    if "DefinitionSanity.lean" not in " ".join(definition.command):
        raise CompletionError(f"{definition.path}: wrong reference-universe run")

    if SOURCE_MANIFEST.stat().st_mtime > whole.started.timestamp() + 0.01:
        raise CompletionError("source manifest was written after the whole build began")
    for line in SOURCE_MANIFEST.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        try:
            relative = line.split("  ", 1)[1]
        except IndexError as exc:
            raise CompletionError("malformed source-manifest data row") from exc
        source = ROOT / relative
        if source.stat().st_mtime > whole.started.timestamp() + 0.01:
            raise CompletionError(
                f"source input is newer than the bound whole build: {relative}"
            )
    if any(
        harness.stat().st_mtime > shard_records[index].started.timestamp() + 0.01
        for index, harness in enumerate(SCRATCH_HARNESSES)
    ):
        raise CompletionError("a shard harness changed after its run began")
    if whole.finished > min(record.started for record in shard_records):
        raise CompletionError("V4 shards began before the bound whole build finished")
    if max(record.finished for record in shard_records) > merge.started:
        raise CompletionError("V4 merge began before both shards finished")
    if merge.finished > analyze.started:
        raise CompletionError("V4 analysis began before the merge finished")
    if analyze.finished > aggregate.started:
        raise CompletionError("aggregate V4 validation began before analysis finished")
    script_runs = (
        (
            VERIFICATION / "scripts" / "merge_pass07_v4_shards.py",
            merge.started,
        ),
        (VERIFICATION / "scripts" / "axiom_audit.py", analyze.started),
        (
            VERIFICATION / "scripts" / "run_all_static_checks.py",
            aggregate.started,
        ),
    )
    for script, started in script_runs:
        if script.stat().st_mtime > started.timestamp() + 0.01:
            raise CompletionError(f"{script}: changed after its bound run began")

    for name in (
        "axiom_audit_summary.txt",
        "axiom_module_coverage.txt",
        "axiom_audit_exceedances.tsv",
        "axiom_and_opaque_declarations.tsv",
    ):
        modified = (LOGS / name).stat().st_mtime
        if not (
            analyze.started.timestamp() - 0.01
            <= modified
            <= analyze.finished.timestamp() + 0.01
        ):
            raise CompletionError(f"{name}: not freshly produced by analyzer")
    return {
        "whole_build": whole,
        "shard0": shard_records[0],
        "shard1": shard_records[1],
        "merge": merge,
        "analyze": analyze,
        "aggregate": aggregate,
    }


def validate_static_v4() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-B",
            str(VERIFICATION / "scripts" / "run_all_static_checks.py"),
            "v4",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        raise CompletionError(
            "existing V4 static checker rejected the fresh merged evidence:\n"
            + result.stdout
        )


def build_completion_manifest() -> dict[str, object]:
    digest = source_digest()
    summary = parse_summary()
    missing = missing_modules()
    merge_summary = validate_merge_summary(digest)
    transcripts = validate_transcripts(merge_summary)
    validate_static_v4()
    appendix_sorries = appendix_sorry_count()
    for path in ARTIFACTS.values():
        if not path.is_file() or path.is_symlink() or path.stat().st_size == 0:
            raise CompletionError(f"required V4 artifact is missing/unsafe: {path}")
    artifact_records = {
        name: {"sha256": sha256(path), "bytes": path.stat().st_size}
        for name, path in ARTIFACTS.items()
    }
    if source_digest() != digest:
        raise CompletionError("source manifest changed during completion validation")
    return {
        "schema": "pass07-v4-current-v1",
        "completion_status": "COMPLETE_MAXIMAL_BUILDABLE",
        "run_mode": "TWO_SHARD_EXHAUSTIVE_PARTITION",
        "partition_rule": "audited_environment_index_mod_2",
        "partition_completeness_basis": (
            "disjoint merged identities equal independent exhaustive "
            "definition_constants.tsv universe"
        ),
        "source_manifest_digest": digest,
        "whole_build_exit_code": 0,
        "build_exit_code": 0,
        "analyzer_exit_code": 2,
        "analyzer_exit_meaning": "EXPECTED_FROZEN_MODULE_BOUNDARY",
        "declarations_audited": int(summary["declarations_audited"]),
        "declaration_type_rows": int(summary["declaration_type_rows"]),
        "declaration_binder_rows": int(summary["declaration_binder_rows"]),
        "direct_dependency_edges": int(summary["direct_dependency_edges"]),
        "environment_modules": int(summary["environment_modules"]),
        "expected_modules": int(summary["expected_modules"]),
        "sorryAx_declarations": int(summary["sorryAx_declarations"]),
        "nonstandard_non_sorry_axiom_declarations": int(
            summary["nonstandard_non_sorry_axiom_declarations"]
        ),
        "appendix_sorryAx_declarations": appendix_sorries,
        "missing_modules": missing,
        "timeline": {
            label: {
                "started": record.started.isoformat(),
                "finished": record.finished.isoformat(),
                "elapsed_seconds": record.elapsed_seconds,
            }
            for label, record in transcripts.items()
        },
        "merge_summary_sha256": sha256(
            LOGS / "pass07_v4_merge_summary.json"
        ),
        "artifacts": artifact_records,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--generate", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        expected = render(build_completion_manifest())
        if args.generate:
            descriptor, temporary_name = tempfile.mkstemp(
                dir=OUTPUT.parent, prefix=f".{OUTPUT.name}.", suffix=".tmp"
            )
            os.close(descriptor)
            temporary = Path(temporary_name)
            temporary.write_text(expected, encoding="utf-8")
            os.replace(temporary, OUTPUT)
            label = "GENERATED"
        else:
            if not OUTPUT.is_file() or OUTPUT.read_text(encoding="utf-8") != expected:
                raise CompletionError("V4 completion manifest is missing or stale")
            label = "CHECKED"
        print(f"PASS: fresh exhaustive V4 completion manifest {label}")
        print(f"sha256: {hashlib.sha256(expected.encode()).hexdigest()}")
        return 0
    except (CompletionError, OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"V4 COMPLETION FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
