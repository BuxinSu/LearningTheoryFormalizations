#!/usr/bin/env python3
"""Audit clean-build coverage and warnings, calibrated on a planted sorry."""

from __future__ import annotations

from collections import Counter
import csv
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import subprocess
import sys


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
LOGS = VERIFY / "logs"
BUILD_LOG = LOGS / "build_full.log"
RECOVERY_BUILD_LOG = LOGS / "build_full.recertification-empty-recovery.log"
RECOVERY_STATUS_LOG = (
    LOGS / "build_full.recertification-empty-recovery.status.log"
)
RECOVERY_REUSE_STATUS_LOG = LOGS / "v1_recovery_reuse_status.log"
RECOVERY_DONE_MARKER = ROOT / ".audit_work" / "v1_recovery_build.done"
RECOVERY_BUILD_DIR = (
    ROOT / ".audit_work" / "v1_recertification_recovery_build_v7"
)
RECOVERY_CONFIG = SCRIPT.parent / "v1_recovery_lakefile.toml"
RECOVERY_CONFIG_CHECKER = SCRIPT.parent / "check_v1_recovery_config.py"
HASH_TREE = SCRIPT.parent / "hash_tree.py"
RECOVERY_CONFIG_CHECK = LOGS / "v1_recovery_config_check.log"
CANONICAL_BEFORE = LOGS / "v1_canonical_build_before.tsv"
CANONICAL_AFTER = LOGS / "v1_canonical_build_after.tsv"
RECOVERY_TREE = LOGS / "v1_recovery_build_tree.tsv"
CANONICAL_DONE_MARKER = ROOT / ".audit_work" / "v1_clean_build.done"
INPUT_MANIFEST_SCRIPT = SCRIPT.parent / "verification_input_manifest.py"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
PLANT_LOG = LOGS / "calibration_sorry_compile.log"

LAKE_WARNING_HEADER = re.compile(
    r"^warning: (?P<file>[^:]+):(?P<line>\d+):(?P<col>\d+): (?P<message>.*)$"
)
LEAN_WARNING_HEADER = re.compile(
    r"^(?P<file>[^:]+):(?P<line>\d+):(?P<col>\d+): warning: (?P<message>.*)$"
)
MODULE_ACTION = re.compile(
    r"^[✔⚠✖] \[\d+/\d+\] (?P<action>Built|Replayed) "
    r"(?P<module>MatrixConcentration(?:\.[A-Za-z0-9_]+)?)(?:\s|$)",
    re.MULTILINE,
)
LINTER = re.compile(r"set_option (linter\.[A-Za-z0-9_.]+) false")


@dataclass(frozen=True)
class WarningRecord:
    file: str
    line: int
    col: int
    warning_class: str
    message: str


@dataclass(frozen=True)
class BuildAnalysis:
    exit_ok: bool
    exit_statuses: list[str]
    success_terminals: int
    error_lines: list[str]
    warning_records: list[WarningRecord]
    action_count: int
    duplicate_action_pairs: list[tuple[str, str]]
    observed_modules: set[str]
    built_action_modules: set[str]
    replayed_action_modules: set[str]
    covered_modules: set[str]
    root_target_inferred: bool
    missing_modules: list[str]
    unexpected_modules: list[str]


def blocks(text: str) -> list[list[str]]:
    result: list[list[str]] = []
    current: list[str] | None = None
    for line in text.splitlines():
        if warning_match(line):
            if current is not None:
                result.append(current)
            current = [line]
        elif current is not None:
            if re.match(r"^[✔⚠✖] \[\d+/\d+\] (?:Built|Replayed) ", line):
                result.append(current)
                current = None
            else:
                current.append(line)
    if current is not None:
        result.append(current)
    return result


def fallback_class(message: str) -> str:
    lower = message.lower()
    if "declaration uses" in lower and "sorry" in lower:
        return "sorry"
    if "deprecated" in lower:
        return "deprecation"
    if "unused" in lower:
        return "unused"
    return "other"


def parse_warnings(text: str) -> list[WarningRecord]:
    records: list[WarningRecord] = []
    for block in blocks(text):
        match = warning_match(block[0])
        if match is None:
            continue
        linter_names = LINTER.findall("\n".join(block))
        warning_class = linter_names[-1] if linter_names else fallback_class(match["message"])
        records.append(
            WarningRecord(
                file=match["file"],
                line=int(match["line"]),
                col=int(match["col"]),
                warning_class=warning_class,
                message=match["message"].strip(),
            )
        )
    return records


def warning_match(line: str) -> re.Match[str] | None:
    return LAKE_WARNING_HEADER.match(line) or LEAN_WARNING_HEADER.match(line)


def write_inventory(records: list[WarningRecord]) -> None:
    inventory = LOGS / "build_warning_inventory.tsv"
    with inventory.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t")
        writer.writerow(("file", "line", "column", "class", "message"))
        for record in records:
            writer.writerow(
                (record.file, record.line, record.col, record.warning_class, record.message)
            )

    summary = LOGS / "build_warning_summary.tsv"
    counts = Counter((record.file, record.warning_class) for record in records)
    with summary.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t")
        writer.writerow(("file", "class", "count"))
        for (file, warning_class), count in sorted(counts.items()):
            writer.writerow((file, warning_class, count))


EXPECTED_MODULES = {
    "MatrixConcentration",
    "MatrixConcentration.Prelude",
    "MatrixConcentration.Chapter1_Introduction",
    "MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices",
    "MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod",
    "MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries",
    "MatrixConcentration.Chapter5_SumOfPSDMatrices",
    "MatrixConcentration.Chapter6_SumOfBoundedRandomMatrices",
    "MatrixConcentration.Chapter7_IntrinsicDimension",
    "MatrixConcentration.Chapter8_ProofOfLiebsTheorem",
    "MatrixConcentration.Appendix_GoldenThompson",
    "MatrixConcentration.Appendix_GaussianConcentration",
    "MatrixConcentration.Appendix_SymmetricLowerBound",
    "MatrixConcentration.Appendix_MatrixRosenthal",
    "MatrixConcentration.Appendix_RosenthalPinelis",
}


def analyze_build(text: str) -> BuildAnalysis:
    warning_records = parse_warnings(text)
    module_actions = list(MODULE_ACTION.finditer(text))
    action_pairs = [
        (match["action"], match["module"]) for match in module_actions
    ]
    action_counts = Counter(action_pairs)
    duplicate_action_pairs = sorted(
        pair for pair, count in action_counts.items() if count != 1
    )
    observed_modules = {match["module"] for match in module_actions}
    built_action_modules = {
        match["module"] for match in module_actions if match["action"] == "Built"
    }
    replayed_action_modules = {
        match["module"] for match in module_actions if match["action"] == "Replayed"
    }
    error_lines = [
        line for line in text.splitlines() if re.search(r"(^|:)error:", line)
    ]
    exit_statuses = re.findall(r"^EXIT_STATUS ([0-9]+)$", text, re.MULTILINE)
    success_terminals = len(
        re.findall(
            r"^Build completed successfully \([1-9][0-9]* jobs\)\.$",
            text,
            re.MULTILINE,
        )
    )
    exit_ok = exit_statuses == ["0"] and success_terminals == 1
    expected_inner_modules = EXPECTED_MODULES - {"MatrixConcentration"}
    root_target_inferred = (
        "MatrixConcentration" not in observed_modules
        and expected_inner_modules <= observed_modules
        and exit_ok
        and "COMMAND " in text
        and "build MatrixConcentration" in text
        and "Build completed successfully" in text
    )
    covered_modules = set(observed_modules)
    if root_target_inferred:
        covered_modules.add("MatrixConcentration")
    return BuildAnalysis(
        exit_ok=exit_ok,
        exit_statuses=exit_statuses,
        success_terminals=success_terminals,
        error_lines=error_lines,
        warning_records=warning_records,
        action_count=len(module_actions),
        duplicate_action_pairs=duplicate_action_pairs,
        observed_modules=observed_modules,
        built_action_modules=built_action_modules,
        replayed_action_modules=replayed_action_modules,
        covered_modules=covered_modules,
        root_target_inferred=root_target_inferred,
        missing_modules=sorted(EXPECTED_MODULES - covered_modules),
        unexpected_modules=sorted(covered_modules - EXPECTED_MODULES),
    )


def equals_values(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in text.splitlines():
        key, separator, value = line.partition("=")
        if separator:
            values[key.strip()] = value.strip()
    return values


def colon_values(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in text.splitlines():
        key, separator, value = line.partition(":")
        if separator:
            values[key.strip()] = value.strip()
    return values


def exact_colon_shape(text: str, keys: set[str]) -> bool:
    lines = text.splitlines()
    parsed_keys = [
        line.partition(":")[0].strip()
        for line in lines
        if line.partition(":")[1]
    ]
    return (
        len(lines) == len(keys)
        and len(parsed_keys) == len(keys)
        and set(parsed_keys) == keys
    )


def main() -> int:
    build_text = BUILD_LOG.read_text(encoding="utf-8", errors="replace")
    recovery_text = RECOVERY_BUILD_LOG.read_text(
        encoding="utf-8", errors="replace"
    )
    plant_text = PLANT_LOG.read_text(encoding="utf-8", errors="replace")
    recovery = analyze_build(recovery_text)
    canonical = analyze_build(build_text)
    build_records = recovery.warning_records
    plant_records = parse_warnings(plant_text)
    write_inventory(build_records)

    sorry_build = [record for record in build_records if record.warning_class == "sorry"]
    sorry_canonical = [
        record
        for record in canonical.warning_records
        if record.warning_class == "sorry"
    ]
    sorry_plant = [record for record in plant_records if record.warning_class == "sorry"]
    expected_plant_sorry_warnings = 2
    calibration_exact = len(sorry_plant) == expected_plant_sorry_warnings
    recovery_status = colon_values(
        RECOVERY_STATUS_LOG.read_text(encoding="utf-8")
    )
    recovery_status_text = RECOVERY_STATUS_LOG.read_text(encoding="utf-8")
    reuse_status_text = RECOVERY_REUSE_STATUS_LOG.read_text(encoding="utf-8")
    reuse_status = colon_values(reuse_status_text)
    marker = equals_values(RECOVERY_DONE_MARKER.read_text(encoding="utf-8"))
    manifest_text = SOURCE_MANIFEST.read_text(encoding="utf-8")
    manifest_match = re.search(
        r"^TOP_LEVEL_SHA256\s+([0-9a-f]{64})$", manifest_text, re.MULTILINE
    )
    manifest_digest = manifest_match.group(1) if manifest_match else ""
    config_sha256 = hashlib.sha256(RECOVERY_CONFIG.read_bytes()).hexdigest()
    runner_sha256 = hashlib.sha256(
        (SCRIPT.parent / "v1_recovery_clean_build.sh").read_bytes()
    ).hexdigest()
    config_checker_sha256 = hashlib.sha256(
        RECOVERY_CONFIG_CHECKER.read_bytes()
    ).hexdigest()
    hash_tree_sha256 = hashlib.sha256(HASH_TREE.read_bytes()).hexdigest()
    recovery_log_sha256 = hashlib.sha256(
        RECOVERY_BUILD_LOG.read_bytes()
    ).hexdigest()
    canonical_log_sha256 = hashlib.sha256(BUILD_LOG.read_bytes()).hexdigest()
    canonical_before_sha256 = hashlib.sha256(
        CANONICAL_BEFORE.read_bytes()
    ).hexdigest()
    canonical_after_sha256 = hashlib.sha256(
        CANONICAL_AFTER.read_bytes()
    ).hexdigest()
    recovery_tree_sha256 = hashlib.sha256(
        RECOVERY_TREE.read_bytes()
    ).hexdigest()
    marker_lines = RECOVERY_DONE_MARKER.read_text(
        encoding="utf-8"
    ).splitlines()
    expected_marker_keys = {
        "marker_version",
        "run_id",
        "verification_input_digest",
        "source_digest",
        "runner_sha256",
        "config_sha256",
        "config_checker_sha256",
        "hash_tree_sha256",
        "build_log_sha256",
        "canonical_before_sha256",
        "canonical_after_sha256",
        "recovery_tree_sha256",
        "recovery_build_dir",
        "canonical_build_unchanged",
        "completed_at_utc",
    }
    marker_shape_ok = (
        len(marker_lines) == 15
        and set(marker) == expected_marker_keys
        and re.fullmatch(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z",
            marker.get("completed_at_utc", ""),
        )
        is not None
    )
    canonical_marker = equals_values(
        CANONICAL_DONE_MARKER.read_text(encoding="utf-8")
    )
    canonical_marker_lines = CANONICAL_DONE_MARKER.read_text(
        encoding="utf-8"
    ).splitlines()
    recovery_tree_current = subprocess.run(
        [sys.executable, str(HASH_TREE), str(RECOVERY_BUILD_DIR)],
        check=False,
        capture_output=True,
    )
    input_check = subprocess.run(
        [sys.executable, str(INPUT_MANIFEST_SCRIPT), "check"],
        check=False,
        capture_output=True,
        text=True,
    )
    input_match = re.search(
        r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$",
        input_check.stdout,
        re.MULTILINE,
    )
    input_digest = input_match.group(1) if input_match else ""
    status_keys = {
        "command",
        "run_id",
        "run_state",
        "evidence_mode",
        "verification_input_digest",
        "source_digest",
        "started_at_utc",
        "finished_at_utc",
        "elapsed_seconds",
        "build_log_sha256",
        "completion_marker_sha256",
        "exit_code",
    }
    provenance_ok = (
        exact_colon_shape(recovery_status_text, status_keys)
        and recovery_status.get("run_state") == "PASS"
        and recovery_status.get("evidence_mode")
        == "executed_fresh_reserved_empty_build_dir"
        and recovery_status.get("exit_code") == "0"
        and recovery_status.get("verification_input_digest") == input_digest
        and recovery_status.get("source_digest") == manifest_digest
        and recovery_status.get("build_log_sha256") == recovery_log_sha256
        and recovery_status.get("completion_marker_sha256")
        == hashlib.sha256(RECOVERY_DONE_MARKER.read_bytes()).hexdigest()
        and marker.get("run_id") == recovery_status.get("run_id")
        and input_check.returncode == 0
        and marker_shape_ok
        and marker.get("marker_version") == "7"
        and marker.get("verification_input_digest") == input_digest
        and marker.get("source_digest") == manifest_digest
        and marker.get("runner_sha256") == runner_sha256
        and marker.get("config_sha256") == config_sha256
        and marker.get("config_checker_sha256") == config_checker_sha256
        and marker.get("hash_tree_sha256") == hash_tree_sha256
        and marker.get("build_log_sha256") == recovery_log_sha256
        and marker.get("canonical_before_sha256")
        == canonical_before_sha256
        and marker.get("canonical_after_sha256") == canonical_after_sha256
        and marker.get("recovery_tree_sha256") == recovery_tree_sha256
        and marker.get("recovery_build_dir")
        == ".audit_work/v1_recertification_recovery_build_v7"
        and marker.get("canonical_build_unchanged") == "true"
        and "RECOVERY_BUILD_DIR_EXISTED_AT_START false" in recovery_text
        and "RECOVERY_BUILD_DIR_RESERVED_EMPTY true" in recovery_text
        and "v1_recovery_lakefile.toml --rehash --no-cache --no-ansi build MatrixConcentration"
        in recovery_text
        and RECOVERY_BUILD_DIR.is_dir()
        and not RECOVERY_BUILD_DIR.is_symlink()
        and CANONICAL_BEFORE.read_bytes() == CANONICAL_AFTER.read_bytes()
        and recovery_tree_current.returncode == 0
        and recovery_tree_current.stdout == RECOVERY_TREE.read_bytes()
        and "result=PASS" in RECOVERY_CONFIG_CHECK.read_text(encoding="utf-8")
        and exact_colon_shape(reuse_status_text, status_keys)
        and reuse_status.get("run_state") == "PASS"
        and reuse_status.get("evidence_mode") == "validated_existing_evidence"
        and reuse_status.get("verification_input_digest") == input_digest
        and reuse_status.get("source_digest") == manifest_digest
        and reuse_status.get("build_log_sha256") == recovery_log_sha256
        and reuse_status.get("completion_marker_sha256")
        == hashlib.sha256(RECOVERY_DONE_MARKER.read_bytes()).hexdigest()
        and len(canonical_marker_lines) == 7
        and set(canonical_marker)
        == {
            "marker_version",
            "run_id",
            "verification_input_digest",
            "runner_sha256",
            "source_digest",
            "build_log_sha256",
            "completed_at_utc",
        }
        and canonical_marker.get("marker_version") == "2"
        and canonical_marker.get("verification_input_digest") == input_digest
        and canonical_marker.get("runner_sha256")
        == hashlib.sha256((SCRIPT.parent / "v1_clean_build.sh").read_bytes()).hexdigest()
        and canonical_marker.get("source_digest") == manifest_digest
        and canonical_marker.get("build_log_sha256") == canonical_log_sha256
        and f"RUN_ID {canonical_marker.get('run_id')}" in build_text
        and f"VERIFICATION_INPUT_DIGEST {input_digest}" in build_text
    )

    output = [
        "V1 BUILD LOG AUDIT",
        "clean_evidence=isolated_reserved_empty_build_directory",
        f"clean_provenance_valid={str(provenance_ok).lower()}",
        f"build_exit_zero={str(recovery.exit_ok).lower()}",
        f"build_exit_status_markers={len(recovery.exit_statuses)}",
        f"build_success_terminals={recovery.success_terminals}",
        f"build_errors={len(recovery.error_lines)}",
        f"built_modules={len(recovery.covered_modules)}",
        f"observed_module_actions={recovery.action_count}",
        f"duplicate_module_actions={len(recovery.duplicate_action_pairs)}",
        f"built_action_modules={len(recovery.built_action_modules)}",
        f"replayed_action_modules={len(recovery.replayed_action_modules)}",
        "root_target_inferred_from_success="
        f"{str(recovery.root_target_inferred).lower()}",
        f"expected_modules={len(EXPECTED_MODULES)}",
        f"missing_modules={len(recovery.missing_modules)}",
        f"unexpected_modules={len(recovery.unexpected_modules)}",
        f"build_warnings={len(build_records)}",
        f"build_sorry_warnings={len(sorry_build)}",
        f"canonical_replay_exit_zero={str(canonical.exit_ok).lower()}",
        "canonical_replay_exit_status_markers="
        f"{len(canonical.exit_statuses)}",
        f"canonical_replay_success_terminals={canonical.success_terminals}",
        f"canonical_replay_errors={len(canonical.error_lines)}",
        f"canonical_replay_covered_modules={len(canonical.covered_modules)}",
        "canonical_replay_observed_module_actions="
        f"{canonical.action_count}",
        "canonical_replay_duplicate_module_actions="
        f"{len(canonical.duplicate_action_pairs)}",
        "canonical_replay_built_action_modules="
        f"{len(canonical.built_action_modules)}",
        "canonical_replay_replayed_action_modules="
        f"{len(canonical.replayed_action_modules)}",
        "canonical_replay_root_target_inferred="
        f"{str(canonical.root_target_inferred).lower()}",
        f"canonical_replay_warnings={len(canonical.warning_records)}",
        f"canonical_replay_sorry_warnings={len(sorry_canonical)}",
        f"calibration_sorry_warnings={len(sorry_plant)}",
        f"calibration_expected_sorry_warnings={expected_plant_sorry_warnings}",
        f"calibration_detected={str(calibration_exact).lower()}",
        f"clean_build_log_sha256={recovery_log_sha256}",
        f"canonical_replay_log_sha256={canonical_log_sha256}",
        "MODULES",
        *sorted(recovery.covered_modules),
        "MISSING",
        *recovery.missing_modules,
        "UNEXPECTED",
        *recovery.unexpected_modules,
        "ERROR_LINES",
        *recovery.error_lines,
    ]
    result_path = LOGS / "build_audit_summary.txt"
    result_path.write_text("\n".join(output) + "\n", encoding="utf-8")
    print("\n".join(output))

    passed = (
        provenance_ok
        and recovery.exit_ok
        and not recovery.error_lines
        and not recovery.missing_modules
        and not recovery.unexpected_modules
        and recovery.action_count == 15
        and not recovery.duplicate_action_pairs
        and recovery.observed_modules == EXPECTED_MODULES
        and len(recovery.built_action_modules) == 15
        and not recovery.replayed_action_modules
        and not recovery.root_target_inferred
        and not sorry_build
        and canonical.exit_ok
        and not canonical.error_lines
        and not canonical.missing_modules
        and not canonical.unexpected_modules
        and canonical.action_count == 14
        and not canonical.duplicate_action_pairs
        and canonical.observed_modules
        == EXPECTED_MODULES - {"MatrixConcentration"}
        and not canonical.built_action_modules
        and canonical.replayed_action_modules
        == EXPECTED_MODULES - {"MatrixConcentration"}
        and canonical.root_target_inferred
        and len(build_records) == len(canonical.warning_records)
        and not sorry_canonical
        and calibration_exact
    )
    print(f"VERDICT {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
