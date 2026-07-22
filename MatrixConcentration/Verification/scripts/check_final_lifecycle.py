#!/usr/bin/env python3
"""Fail closed unless the delivered V1–V10 verification lifecycle is complete."""

from __future__ import annotations

import atexit
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import secrets
import shlex
import signal
import subprocess
import sys
import uuid
from collections import Counter
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
LOGS = VERIFY / "logs"
AUDIT_WORK = ROOT / ".audit_work"
STAGE_DIR = ROOT / ".audit_work" / "run_all_stages"
LOCK = ROOT / ".audit_work" / "verification.run.lock"
GUARD = ROOT / ".audit_work" / "verification.finalization.guard"
FINAL_OUTPUT = LOGS / "final_lifecycle_check.txt"
FINAL_CLAIMS_MANIFEST = LOGS / "final_claims_manifest.tsv"
INPUT_MANIFEST_SCRIPT = SCRIPT.parent / "verification_input_manifest.py"

V1_DELETE_MARKER = ROOT / ".audit_work" / "v1_build_deleted.marker"
V1_DONE_MARKER = ROOT / ".audit_work" / "v1_clean_build.done"
V1_DELETE_LOG = LOGS / "build_delete_once.log"
V1_RUNNER = SCRIPT.parent / "v1_clean_build.sh"
V1_RECOVERY_RUNNER = SCRIPT.parent / "v1_recovery_clean_build.sh"
V1_RECOVERY_CONFIG = SCRIPT.parent / "v1_recovery_lakefile.toml"
V1_RECOVERY_MARKER = ROOT / ".audit_work" / "v1_recovery_build.done"
V1_RECOVERY_BUILD_DIR = (
    ROOT / ".audit_work" / "v1_recertification_recovery_build_v7"
)
V1_INTERRUPTED_RECOVERY_BUILD_DIRS = (
    ROOT / ".audit_work" / "v1_recertification_recovery_build_v3",
    ROOT / ".audit_work" / "v1_recertification_recovery_build_v4",
    ROOT / ".audit_work" / "v1_recertification_recovery_build_v5",
)
V1_RECOVERY_LOG = LOGS / "build_full.recertification-empty-recovery.log"
V1_RECOVERY_STATUS = (
    LOGS / "build_full.recertification-empty-recovery.status.log"
)
V1_RECOVERY_REUSE_STATUS = LOGS / "v1_recovery_reuse_status.log"
V1_RECOVERY_CONFIG_CHECK = LOGS / "v1_recovery_config_check.log"
V1_CANONICAL_BEFORE = LOGS / "v1_canonical_build_before.tsv"
V1_CANONICAL_AFTER = LOGS / "v1_canonical_build_after.tsv"
V1_RECOVERY_TREE = LOGS / "v1_recovery_build_tree.tsv"
V1_CANONICAL_LOG = LOGS / "build_full.log"
RUN_ALL = SCRIPT.parent / "run_all.sh"
V10_AGGREGATE_LOG = LOGS / "v10_run.aggregate.log"
V10_AGGREGATE_STATUS = LOGS / "v10_run_status.aggregate.log"

INCIDENT_START_MARKER = (
    ROOT / ".audit_work" / "v1_recert_build_delete_started.marker"
)
INCIDENT_DELETE_MARKER = (
    ROOT / ".audit_work" / "v1_recert_build_deleted.marker"
)
INCIDENT_DELETE_LOG = LOGS / "build_delete_once.recertification.log"
REMOVED_INCIDENT_RUNNER = SCRIPT.parent / "v1_recert_clean_build.sh"
INVALID_INCIDENT_DONE_MARKER = (
    ROOT / ".audit_work" / "v1_recert_clean_build.done"
)

EXPECTED_V10_QUALITY_SHA256 = (
    "86ab9eb095e251e767eb776928e127bc1898e81347e7fb20b51b9a8c2f5897b6"
)
ALLOWED_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
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
LAKE_PROJECT_ACTION = re.compile(
    r"^[✔⚠✖] \[\d+/\d+\] (Built|Replayed) "
    r"(MatrixConcentration(?:\.[A-Za-z0-9_]+)?)(?:\s|$)",
    re.MULTILINE,
)

INCIDENT_ARCHIVES = (
    "run_all.recertification-attempt1.log",
    "run_all_status.recertification-attempt1.log",
    "v10_run.interrupted-20260720.log",
    "v10_run_status.interrupted-20260720.log",
    "run_all.invalid-concurrent-v1.log",
    "run_all_status.invalid-concurrent-v1.log",
    "build_full.invalid-concurrent-v1.log",
    "run_all.invalid-concurrent-v1-and-resume.log",
    "run_all_status.invalid-resume.log",
    "build_full.invalid-resume.log",
    "run_all.invalid-postfinal-overwrite.log",
    "run_all_status.invalid-postfinal-overwrite.log",
    "build_full.invalid-postfinal-overwrite.log",
    "build_audit_summary.invalid-postfinal-overwrite.txt",
    "run_all.invalid-finalization-interrupt.log",
    "run_all_status.invalid-finalization-interrupt.log",
    "build_full.invalid-finalization-interrupt.log",
    "build_audit_summary.invalid-finalization-interrupt.txt",
    "run_all.invalid-stale-finalizer-partial.log",
    "run_all_status.invalid-stale-finalizer-partial.log",
    "build_full.invalid-stale-finalizer-partial.log",
    "build_audit_summary.invalid-stale-finalizer-partial.txt",
    "run_all.invalid-finalization-interrupt-20260720T074713Z.log",
    "run_all_status.invalid-finalization-interrupt-20260720T074713Z.log",
    "build_full.invalid-finalization-interrupt-20260720T074713Z.log",
    "build_audit_summary.invalid-finalization-interrupt-20260720T074713Z.txt",
    "run_all.invalid-concurrent-edit-20260720T075034Z.log",
    "run_all_status.invalid-concurrent-edit-20260720T075034Z.log",
    "build_full.invalid-concurrent-edit-20260720T075034Z.log",
    "build_audit_summary.invalid-concurrent-edit-20260720T075034Z.txt",
    "run_all.invalid-orphan-bypass-20260720T081232Z.log",
    "run_all_status.invalid-orphan-bypass-20260720T081232Z.log",
    "build_full.invalid-orphan-bypass-20260720T081232Z.log",
    "build_audit_summary.invalid-orphan-bypass-20260720T081232Z.txt",
    "run_all.invalid-nested-guard-20260720T081751Z.log",
    "run_all_status.invalid-nested-guard-20260720T081751Z.log",
    "build_full.invalid-nested-guard-20260720T081751Z.log",
    "build_audit_summary.invalid-nested-guard-20260720T081751Z.txt",
    "v10_run.invalid-nested-guard-20260720T081751Z.log",
    "final_lifecycle_check.invalid-pre-recovery.log",
    "run_all.invalid-concurrent-correction-20260720T090805Z.log",
    "run_all_status.invalid-concurrent-correction-20260720T090805Z.log",
    (
        "build_full.recertification-empty-recovery."
        "invalid-v3-interrupted-20260720T090811Z.log"
    ),
    "v1_recovery_config_check.invalid-v3-interrupted-20260720T090811Z.log",
    "v1_recovery_manifest_check.invalid-v3-interrupted-20260720T090811Z.log",
    (
        "build_full.recertification-empty-recovery."
        "invalid-v4-interrupted-20260720T092351Z.status.log"
    ),
    (
        "build_full.recertification-empty-recovery."
        "invalid-v5-interrupted-20260720T093501Z.log"
    ),
    (
        "build_full.recertification-empty-recovery."
        "invalid-v5-interrupted-20260720T093501Z.status.log"
    ),
    (
        "cache_get.recertification-empty-recovery."
        "invalid-v5-interrupted-20260720T093501Z.log"
    ),
    "v1_recovery_config_check.invalid-v5-interrupted-20260720T093501Z.log",
    "v1_recovery_manifest_check.invalid-v5-interrupted-20260720T093501Z.log",
    "v1_canonical_build_before.invalid-v5-interrupted-20260720T093501Z.tsv",
)
INCIDENT_STATUSES = {
    "run_all_status.recertification-attempt1.log": ("FAIL", "2"),
    "v10_run_status.interrupted-20260720.log": ("FAIL", "130"),
    "run_all_status.invalid-concurrent-v1.log": ("FAIL", "143"),
    "run_all_status.invalid-resume.log": ("FAIL", "143"),
    "run_all_status.invalid-postfinal-overwrite.log": ("FAIL", "143"),
    "run_all_status.invalid-finalization-interrupt.log": ("FAIL", "143"),
    # This abandoned finalizer wrote a nominal PASS status after only nine
    # stages. Its paired transcript is checked below to prove it is archived
    # as invalid partial evidence rather than mistaken for certification.
    "run_all_status.invalid-stale-finalizer-partial.log": ("PASS", "0"),
    "run_all_status.invalid-concurrent-edit-20260720T075034Z.log": (
        "PASS",
        "0",
    ),
    "run_all_status.invalid-orphan-bypass-20260720T081232Z.log": (
        "FAIL",
        "143",
    ),
    "run_all_status.invalid-nested-guard-20260720T081751Z.log": (
        "FAIL",
        "76",
    ),
    "run_all_status.invalid-concurrent-correction-20260720T090805Z.log": (
        "FAIL",
        "130",
    ),
    (
        "build_full.recertification-empty-recovery."
        "invalid-v4-interrupted-20260720T092351Z.status.log"
    ): ("FAIL", "130"),
    (
        "build_full.recertification-empty-recovery."
        "invalid-v5-interrupted-20260720T093501Z.status.log"
    ): ("FAIL", "143"),
}
INCOMPLETE_INCIDENT_STATUSES = {
    "run_all_status.invalid-finalization-interrupt-20260720T074713Z.log": {
        "command": "./MatrixConcentration/Verification/scripts/run_all.sh --fresh",
        "run_state": "RUNNING",
        "started_at_utc": "2026-07-20T07:50:34Z",
    },
}

V10_QUALITY_INPUT_SHA256 = {
    VERIFY / "curation" / "v10_inline_adjudication.tsv":
        "8f8d75096d31086991886a32a8ee2960c33c24a83e33b5821abe8c1658f31f1b",
    LOGS / "v10_inline_review_obligations.tsv":
        "b6156f630d452e51c754efab842868941697870ac6d856803ae0198cded35511",
    LOGS / "v10_inline_review_queue.tsv":
        "2399491456d28b3f694f8aa505dba10707337a3eace7a8bd5bf943854b976779",
    LOGS / "v10_inline_assumptions.tsv":
        "43b357efb5d2f05b72043e45cbce9860f0b43e8db7ba9e6d98395b8c319fab56",
    LOGS / "v10_inline_type_groups.tsv":
        "ead336e69c026609ef9cdc37fa86161a5ea2a719e9646eca8c820caf680fe3d2",
    LOGS / "v10_summary.json":
        "b1fd4659788b2e1bf86d7c264a3e992bdb2c4fbd72bbfa7eb1a5c3c3b3592f91",
    LOGS / "v10_status.tsv":
        "b44837175e3475879bd65d1e1bac88ef624053b1b3cdaa92c563d257eb5b1628",
    LOGS / "v10_disclosure_reconciliation.tsv":
        "f532e15925aa7d59584a342ea8c9a34b0d14ac6032727cde6368aa4016ad42f5",
}
INVALID_NOMINAL_PASS_TRANSCRIPTS = {
    "run_all.invalid-stale-finalizer-partial.log": (9, 9, 0, 0),
    "run_all.invalid-concurrent-edit-20260720T075034Z.log": (9, 9, 0, 0),
    "run_all.invalid-concurrent-correction-20260720T090805Z.log": (2, 1, 0, 0),
}

EXPECTED_STAGE_IDS = (
    "01_environment",
    "02_v1_build",
    "03_plants_generate",
    "04_plants_compile",
    "05_v1_log_audit",
    "06_v2_import_graph",
    "07_v3_calibration",
    "08_v3_production",
    "09_v4_collection",
    "10_v4_analysis",
    "11_v3_v4_reconcile",
    "12_v5_calibration",
    "13_v5_production",
    "14_v8_lint",
    "15_v9_extract",
    "16_v9_endpoints",
    "17_v9_claims",
    "18_v9_calibration",
    "19_v9_commands",
    "20_v9_records",
    "21_v10",
)
EXPECTED_STAGE_LABELS = {
    "01_environment": "environment capture",
    "02_v1_build": "V1 clean-state recovery and canonical replay",
    "03_plants_generate": "calibration plant generation",
    "04_plants_compile": "calibration plant compilation",
    "05_v1_log_audit": "V1 build-log audit",
    "06_v2_import_graph": "V2 import graph",
    "07_v3_calibration": "V3 textual calibration",
    "08_v3_production": "V3 production scan",
    "09_v4_collection": "V4 environment collection",
    "10_v4_analysis": "V4 axiom analysis",
    "11_v3_v4_reconcile": "V3/V4 reconciliation",
    "12_v5_calibration": "V5 calibration",
    "13_v5_production": "V5 production scan",
    "14_v8_lint": "V8 package lint and analysis",
    "15_v9_extract": "V9 correspondence extraction",
    "16_v9_endpoints": "V9 endpoint collection",
    "17_v9_claims": "V9 claims check",
    "18_v9_calibration": "V9 fake-name calibration",
    "19_v9_commands": "V9 printed-command check",
    "20_v9_records": "V9 record chronology",
    "21_v10": "V10 conditional-interface census",
}

EXPECTED_V6_STAGE_LABELS = (
    "source manifest gate",
    "calibration generation",
    "correspondence extraction",
    "compiled endpoint telescopes",
    "Tier-A calibrated statement scan",
    "Tier-A hit adjudication",
    "auto-bound positive-control compilation",
    "auto-bound source/environment audit",
    "curated Tier-B merge",
    "curated Tier-B independent validation",
    "uniform all-OK Tier-C sample",
    "library endpoint dependency collection",
    "witness and bad-witness compilation",
    "witness acceptance",
    "dynamic Tier-C environment evidence",
    "dynamic Tier-C fail-closed validation",
    "maxSummandSq containment",
    "V6 report assembly",
)

EXPECTED_V10_STAGE_LABELS = (
    "initial source manifest gate",
    "calibration plant generation",
    "conditional calibration compilation",
    "environment census collection",
    "concrete witness compilation",
    "census reconciliation and adjudication",
    "final source manifest stability",
)

EXPECTED_V7_WITNESS_NAMES = {
    "MatrixConcentration.V7Witnesses.mIntegrable_nonzero_constant",
    "MatrixConcentration.V7Witnesses.isRademacher_identity",
    "MatrixConcentration.V7Witnesses.isStdGaussian_identity",
    "MatrixConcentration.V7Witnesses.isBernoulli_identity",
    "MatrixConcentration.V7Witnesses.sampleCovSummand_nonzero_model",
    "MatrixConcentration.V7Witnesses.gChernoff_positive_model",
    "MatrixConcentration.V7Witnesses.gBernstein_value_model",
    "MatrixConcentration.V7Witnesses.maxSummandSq_finite_nonzero_model",
    "MatrixConcentration.V7Witnesses.featureOuter_nonzero_model",
    "MatrixConcentration.V7Witnesses.secondMoment_nonzero_model",
    "MatrixConcentration.V7Witnesses.variance_statistics_nonzero_models",
    "MatrixConcentration.V7Witnesses.entropy_nonzero_models",
    "MatrixConcentration.V7Witnesses.laplCoeff_nonzero_model",
    "MatrixConcentration.V7Witnesses.psiOne_positive_model",
    "MatrixConcentration.V7Witnesses.psiTwo_positive_model",
}
EXPECTED_V10_WITNESS_NAME = (
    "MatrixConcentration.V10Witnesses.hasReproducingProperty_zero"
)

EXPECTED_LEAN_VERSION = "4.31.0"
EXPECTED_LEAN_COMMIT = "68218e876d2a38b1985b8590fff244a83c321783"
EXPECTED_MATHLIB_REV = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
EXPECTED_FROZEN_SHA256 = {
    "README.pre-recertification.md":
        "61decdc9a7d6ca489fb331159657ed63d493e4bef26bb994626bf82e262d9fe1",
    "README.pre-correction.md":
        "99d208585309890b57bc2ce542f59d8f43a33edd9ac600ebde70f8555d83fb1a",
}

_ACTIVE_LIFECYCLE_LOCK: tuple[str, int] | None = None
_ACTIVE_LIFECYCLE_GUARD: tuple[str, int] | None = None
_LIFECYCLE_FINALIZED = False


def read_text(path: Path, problems: list[str]) -> str | None:
    if not path.is_file() or path.is_symlink():
        problems.append(
            f"missing, nonregular, or symlinked file: {path.relative_to(ROOT)}"
        )
        return None
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        problems.append(f"cannot read {path.relative_to(ROOT)}: {error}")
        return None


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_write_bytes(path: Path, payload: bytes) -> None:
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    try:
        with temporary.open("wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            temporary.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def replace_with_nonpass(payload: bytes) -> bool:
    """Replace the certificate, or remove any stale PASS if replacement fails."""
    try:
        atomic_write_bytes(FINAL_OUTPUT, payload)
        return True
    except BaseException:
        try:
            FINAL_OUTPUT.unlink(missing_ok=True)
        except OSError:
            pass
        return False


def write_final_claims_manifest(problems: list[str]) -> tuple[int, str | None]:
    reports = sorted(VERIFY.glob("[0-9][0-9]_*.md"))
    expected_reports = [
        next(iter(sorted(VERIFY.glob(f"{number:02d}_*.md"))), None)
        for number in range(1, 11)
    ]
    paths: list[Path] = [
        VERIFY / "README.md",
        VERIFY / "SOUNDNESS_CORRECTION.md",
        VERIFY / "README.pre-correction.md",
        VERIFY / "README.pre-recertification.md",
        *(path for path in expected_reports if path is not None),
    ]
    if (
        len(reports) != 10
        or any(path is None for path in expected_reports)
        or len(paths) != 14
    ):
        problems.append(
            "final claims manifest: expected README, correction report, "
            "two frozen snapshots, and exactly ten numbered reports"
        )
        return 0, None
    rows: list[tuple[str, int, str]] = []
    for path in paths:
        if not path.is_file() or path.is_symlink():
            problems.append(
                "final claims manifest: missing, nonregular, or symlinked "
                f"{path.relative_to(ROOT)}"
            )
            continue
        rows.append(
            (
                path.relative_to(ROOT).as_posix(),
                path.stat().st_size,
                sha256(path),
            )
        )
        expected_frozen = EXPECTED_FROZEN_SHA256.get(path.name)
        if expected_frozen is not None and rows[-1][2] != expected_frozen:
            problems.append(
                f"final claims manifest: frozen snapshot drifted: {path.name}"
            )
    if len(rows) != 14:
        return len(rows), None
    lines = ["path\tbytes\tsha256"]
    lines.extend(
        f"{path}\t{size}\t{digest}" for path, size, digest in sorted(rows)
    )
    payload = ("\n".join(lines) + "\n").encode("utf-8")
    digest = hashlib.sha256(payload).hexdigest()
    try:
        atomic_write_bytes(FINAL_CLAIMS_MANIFEST, payload)
    except OSError as error:
        problems.append(f"cannot commit final claims manifest: {error}")
        return len(rows), None
    return len(rows), digest


def colon_values(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in text.splitlines():
        key, separator, value = line.partition(":")
        if separator:
            values[key.strip()] = value.strip()
    return values


def equals_values(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in text.splitlines():
        key, separator, value = line.partition("=")
        if separator:
            values[key.strip()] = value.strip()
    return values


def space_values(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in text.splitlines():
        fields = line.split(maxsplit=1)
        if len(fields) == 2:
            values[fields[0]] = fields[1]
    return values


def exact_colon_record(
    text: str,
    expected_keys: set[str],
    source: str,
    problems: list[str],
) -> dict[str, str]:
    lines = text.splitlines()
    keys = [
        line.partition(":")[0].strip()
        for line in lines
        if line.partition(":")[1]
    ]
    if (
        len(lines) != len(expected_keys)
        or len(keys) != len(expected_keys)
        or set(keys) != expected_keys
    ):
        problems.append(
            f"{source}: expected exact keys {sorted(expected_keys)}, "
            f"measured {keys}"
        )
    return colon_values(text)


def valid_run_id(value: str | None) -> bool:
    return bool(
        value
        and re.fullmatch(
            r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-"
            r"[0-9a-f]{4}-[0-9a-f]{12}",
            value,
        )
    )


def validate_status_chronology(
    values: dict[str, str], source: str, problems: list[str]
) -> None:
    try:
        started = datetime.fromisoformat(
            values["started_at_utc"].replace("Z", "+00:00")
        )
        finished = datetime.fromisoformat(
            values["finished_at_utc"].replace("Z", "+00:00")
        )
        elapsed = int(values["elapsed_seconds"])
    except (KeyError, ValueError):
        problems.append(f"{source}: invalid timestamp or elapsed field")
        return
    if started.tzinfo != timezone.utc or finished.tzinfo != timezone.utc:
        problems.append(f"{source}: timestamps are not UTC")
    measured = int((finished - started).total_seconds())
    if measured < 0 or elapsed < 0 or abs(measured - elapsed) > 2:
        problems.append(
            f"{source}: inconsistent chronology measured={measured} "
            f"elapsed={elapsed}"
        )


def parse_utc_timestamp(
    value: str | None, source: str, problems: list[str]
) -> datetime | None:
    if value is None:
        problems.append(f"{source}: missing UTC timestamp")
        return None
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        problems.append(f"{source}: invalid UTC timestamp {value!r}")
        return None
    if parsed.tzinfo != timezone.utc or not value.endswith("Z"):
        problems.append(f"{source}: timestamp is not canonical UTC: {value!r}")
        return None
    return parsed


def require_timestamp_within(
    value: str | None,
    lower: str | None,
    upper: str | None,
    source: str,
    problems: list[str],
) -> None:
    parsed = parse_utc_timestamp(value, source, problems)
    lower_parsed = parse_utc_timestamp(
        lower, f"{source} lower bound", problems
    )
    upper_parsed = parse_utc_timestamp(
        upper, f"{source} upper bound", problems
    )
    if (
        parsed is not None
        and lower_parsed is not None
        and upper_parsed is not None
        and not lower_parsed <= parsed <= upper_parsed
    ):
        problems.append(
            f"{source}: timestamp {value} falls outside [{lower}, {upper}]"
        )


def require_ordered_stage_labels(
    text: str,
    expected: tuple[str, ...],
    source: str,
    problems: list[str],
    *,
    timestamped: bool,
) -> None:
    if timestamped:
        start_pattern = (
            r"^===== START (.+?) "
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z =====$"
        )
        pass_pattern = (
            r"^===== PASS  (.+?) "
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z =====$"
        )
    else:
        start_pattern = r"^===== START (.+?) =====$"
        pass_pattern = r"^===== PASS  (.+?) =====$"
    starts = tuple(re.findall(start_pattern, text, re.MULTILINE))
    passes = tuple(re.findall(pass_pattern, text, re.MULTILINE))
    if starts != expected:
        problems.append(f"{source}: unexpected ordered START labels {starts}")
    if passes != expected:
        problems.append(f"{source}: unexpected ordered PASS labels {passes}")


def require_input_digest_in_log(
    text: str, digest: str | None, source: str, problems: list[str]
) -> None:
    matches = re.findall(
        r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$", text, re.MULTILINE
    )
    if digest is None or not matches or any(value != digest for value in matches):
        problems.append(
            f"{source}: verification-input digest evidence is absent or drifting"
        )


def acquire_lifecycle_lock(problems: list[str]) -> tuple[str, int] | None:
    if os.path.lexists(GUARD):
        problems.append("finalization guard remains before lifecycle check")
        return None
    if os.path.lexists(LOCK):
        problems.append("verification writer lock exists before lifecycle check")
        return None
    run_id = str(uuid.uuid4())
    capability_hash = hashlib.sha256(secrets.token_bytes(32)).hexdigest()
    payload = (
        f"pid={os.getpid()} runner=final_lifecycle "
        f"capability_sha256={capability_hash} run_id={run_id}\n"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(LOCK, flags, 0o600)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        inode = LOCK.lstat().st_ino
    except OSError as error:
        problems.append(f"cannot acquire lifecycle writer lock: {error}")
        return None
    return payload, inode


def validate_lifecycle_lock(
    ownership: tuple[str, int] | None, problems: list[str]
) -> bool:
    if ownership is None:
        return False
    payload, inode = ownership
    try:
        stat = LOCK.lstat()
        observed = LOCK.read_text(encoding="utf-8")
        if LOCK.is_symlink() or stat.st_ino != inode or observed != payload:
            problems.append("lifecycle writer lock ownership changed")
            return False
    except OSError as error:
        problems.append(f"cannot validate lifecycle writer lock: {error}")
        return False
    return True


def release_lifecycle_lock(
    ownership: tuple[str, int] | None, problems: list[str]
) -> bool:
    if not validate_lifecycle_lock(ownership, problems):
        return False
    try:
        LOCK.unlink()
        if os.path.lexists(LOCK):
            problems.append("lifecycle writer lock remains after release")
            return False
    except OSError as error:
        problems.append(f"cannot release lifecycle writer lock: {error}")
        return False
    return True


def acquire_lifecycle_guard(
    problems: list[str],
) -> tuple[str, int] | None:
    if os.path.lexists(GUARD):
        problems.append("finalization guard appeared during lifecycle setup")
        return None
    payload = (
        f"pid={os.getpid()} owner=final_lifecycle "
        f"nonce={secrets.token_hex(32)}\n"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(GUARD, flags, 0o600)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        inode = GUARD.lstat().st_ino
    except OSError as error:
        problems.append(f"cannot acquire lifecycle finalization guard: {error}")
        return None
    return payload, inode


def validate_lifecycle_guard(
    ownership: tuple[str, int] | None, problems: list[str]
) -> bool:
    if ownership is None:
        return False
    payload, inode = ownership
    try:
        stat = GUARD.lstat()
        observed = GUARD.read_text(encoding="utf-8")
    except OSError as error:
        problems.append(f"cannot validate lifecycle finalization guard: {error}")
        return False
    if GUARD.is_symlink() or stat.st_ino != inode or observed != payload:
        problems.append("lifecycle finalization guard ownership changed")
        return False
    return True


def release_lifecycle_guard(
    ownership: tuple[str, int] | None, problems: list[str]
) -> bool:
    if not validate_lifecycle_guard(ownership, problems):
        return False
    try:
        GUARD.unlink()
        if os.path.lexists(GUARD):
            problems.append("lifecycle finalization guard remains after release")
            return False
    except OSError as error:
        problems.append(f"cannot release lifecycle finalization guard: {error}")
        return False
    return True


def handoff_lifecycle_lock_to_guard(
    lock_ownership: tuple[str, int] | None,
    guard_ownership: tuple[str, int] | None,
    problems: list[str],
) -> tuple[str, int] | None:
    """Atomically preserve a validity gate while releasing the writer path."""
    if not validate_lifecycle_lock(lock_ownership, problems):
        return None
    if not release_lifecycle_guard(guard_ownership, problems):
        return None
    if not validate_lifecycle_lock(lock_ownership, problems):
        return None
    assert lock_ownership is not None
    payload, inode = lock_ownership
    try:
        # A hard link fails rather than replacing a guard that appeared
        # concurrently. Until LOCK is unlinked both names protect the state;
        # afterwards GUARD remains the publication gate.
        os.link(LOCK, GUARD, follow_symlinks=False)
        guard_stat = GUARD.lstat()
        if GUARD.is_symlink() or guard_stat.st_ino != inode:
            problems.append("publication guard does not preserve lock inode")
            return None
        LOCK.unlink()
        if os.path.lexists(LOCK):
            problems.append("writer lock remains after publication handoff")
            return None
    except OSError as error:
        problems.append(f"cannot hand off writer lock to publication guard: {error}")
        return None
    return payload, inode


def fail_closed_at_exit() -> None:
    """Best-effort cleanup and certificate invalidation after an exception."""
    global _ACTIVE_LIFECYCLE_LOCK
    global _ACTIVE_LIFECYCLE_GUARD
    if _LIFECYCLE_FINALIZED:
        return
    sentinel = (
        "FINAL VERIFICATION LIFECYCLE CHECK\n"
        "state=ABORTED\n"
        f"checker_pid={os.getpid()}\n"
        f"aborted_at_utc={datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}\n"
        "result=FAIL\n"
    ).encode("utf-8")
    output_invalidated = False
    try:
        atomic_write_bytes(FINAL_OUTPUT, sentinel)
        output_invalidated = True
    except OSError:
        try:
            FINAL_OUTPUT.unlink(missing_ok=True)
            output_invalidated = not os.path.lexists(FINAL_OUTPUT)
        except OSError:
            pass
    if not output_invalidated:
        # Deliberately retain every coordination gate rather than allowing an
        # older PASS transcript to coexist with an apparently idle verifier.
        return
    cleanup_problems: list[str] = []
    if _ACTIVE_LIFECYCLE_GUARD is not None:
        release_lifecycle_guard(_ACTIVE_LIFECYCLE_GUARD, cleanup_problems)
        _ACTIVE_LIFECYCLE_GUARD = None
    if _ACTIVE_LIFECYCLE_LOCK is not None:
        release_lifecycle_lock(_ACTIVE_LIFECYCLE_LOCK, cleanup_problems)
        _ACTIVE_LIFECYCLE_LOCK = None


atexit.register(fail_closed_at_exit)


def terminate_with_cleanup(signum: int, _frame: object) -> None:
    raise SystemExit(128 + signum)


signal.signal(signal.SIGTERM, terminate_with_cleanup)


def contains_recursive_rm(text: str) -> bool:
    """Recognize recursive rm flags regardless of flag grouping/order."""
    logical_text = text.replace("\\\n", " ")
    for line in logical_text.splitlines():
        if not re.search(r"(?:^|[\s;&|])(?:[A-Za-z0-9_./-]*/)?rm(?:\s|$)", line):
            continue
        try:
            tokens = shlex.split(line, comments=True, posix=True)
        except ValueError:
            return True
        for index, token in enumerate(tokens):
            if Path(token).name != "rm":
                continue
            for argument in tokens[index + 1 :]:
                if argument == "--":
                    break
                if argument == "--recursive":
                    return True
                if argument.startswith("-") and (
                    "r" in argument[1:] or "R" in argument[1:]
                ):
                    return True
    return False


def project_actions(text: str) -> list[tuple[str, str]]:
    return [
        (match.group(1), match.group(2))
        for match in LAKE_PROJECT_ACTION.finditer(text)
    ]


def require_equal(
    values: dict[str, str],
    key: str,
    expected: str,
    source: str,
    problems: list[str],
) -> None:
    measured = values.get(key)
    if measured != expected:
        problems.append(
            f"{source}: expected {key}={expected!r}, measured {measured!r}"
        )


def marker_counts(text: str) -> tuple[int, int, int, int]:
    lines = text.splitlines()
    return tuple(
        sum(bool(re.match(rf"^===== {kind}(?:\s|=)", line)) for line in lines)
        for kind in ("START", "PASS", "SKIP", "FAIL")
    )  # type: ignore[return-value]


def require_terminal(
    text: str,
    terminal: str,
    source: str,
    problems: list[str],
    *,
    final_nonempty: bool = False,
) -> bool:
    before = len(problems)
    lines = text.splitlines()
    positions = [index for index, line in enumerate(lines) if line == terminal]
    if len(positions) != 1:
        problems.append(
            f"{source}: expected one terminal {terminal!r}, measured {len(positions)}"
        )
        return False
    later_markers = [
        line
        for line in lines[positions[0] + 1 :]
        if re.match(r"^===== (?:START|PASS|SKIP|FAIL)(?:\s|=)", line)
    ]
    if later_markers:
        problems.append(f"{source}: stage marker occurs after terminal success")
    if final_nonempty:
        nonempty = [line for line in lines if line.strip()]
        if not nonempty or nonempty[-1] != terminal:
            problems.append(f"{source}: terminal is not the final nonempty line")
    return len(problems) == before


def current_manifest(problems: list[str]) -> str | None:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT.parent / "source_manifest.py"), "check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    match = re.search(
        r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$",
        completed.stdout,
        re.MULTILINE,
    )
    if completed.returncode != 0:
        problems.append(
            f"source_manifest.py check: exit code {completed.returncode}"
        )
    if "SOURCE MANIFEST: PASS" not in completed.stdout.splitlines():
        problems.append("source_manifest.py check: missing PASS")
    if match is None:
        problems.append("source_manifest.py check: missing digest")
    return match.group(1) if match else None


def current_input_manifest(problems: list[str]) -> str | None:
    completed = subprocess.run(
        [sys.executable, str(INPUT_MANIFEST_SCRIPT), "check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    match = re.search(
        r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$",
        completed.stdout,
        re.MULTILINE,
    )
    if completed.returncode != 0:
        problems.append(
            "verification_input_manifest.py check: "
            f"exit code {completed.returncode}"
        )
    if "VERIFICATION INPUT MANIFEST: PASS" not in completed.stdout.splitlines():
        problems.append("verification input manifest: missing PASS")
    if match is None:
        problems.append("verification input manifest: missing digest")
    return match.group(1) if match else None


def require_manifest_log(
    path: Path,
    digest: str | None,
    problems: list[str],
) -> bool:
    text = read_text(path, problems)
    if text is None:
        return False
    before = len(problems)
    if "SOURCE MANIFEST: PASS" not in text.splitlines():
        problems.append(f"{path.name}: missing SOURCE MANIFEST: PASS")
    match = re.search(
        r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$", text, re.MULTILINE
    )
    if match is None:
        problems.append(f"{path.name}: missing digest")
    elif digest is not None and match.group(1) != digest:
        problems.append(
            f"{path.name}: digest {match.group(1)} differs from {digest}"
        )
    return len(problems) == before


def require_clean_lean_log(path: Path, problems: list[str]) -> bool:
    text = read_text(path, problems)
    if text is None:
        return False
    before = len(problems)
    statuses = re.findall(r"^LEAN_EXIT_STATUS ([0-9]+)$", text, re.MULTILINE)
    if statuses != ["0"]:
        problems.append(
            f"{path.name}: expected exactly one LEAN_EXIT_STATUS 0, "
            f"measured {statuses!r}"
        )
    if re.search(r"\berror:", text, re.IGNORECASE):
        problems.append(f"{path.name}: contains a Lean error")
    if re.search(r"declaration uses ['\"`]?sorry", text, re.IGNORECASE):
        problems.append(f"{path.name}: contains a sorry warning")
    return len(problems) == before


def read_tsv(path: Path, problems: list[str]) -> list[dict[str, str]]:
    text = read_text(path, problems)
    if text is None:
        return []
    try:
        return list(csv.DictReader(text.splitlines(), delimiter="\t"))
    except csv.Error as error:
        problems.append(f"{path.name}: invalid TSV: {error}")
        return []


def main() -> int:
    global _ACTIVE_LIFECYCLE_LOCK
    global _ACTIVE_LIFECYCLE_GUARD
    global _LIFECYCLE_FINALIZED
    problems: list[str] = []
    audit_directories_pass = (
        LOGS.is_dir()
        and not LOGS.is_symlink()
        and AUDIT_WORK.is_dir()
        and not AUDIT_WORK.is_symlink()
    )
    if not audit_directories_pass:
        payload = (
            "FINAL VERIFICATION LIFECYCLE CHECK\n"
            "audit_directories=FAIL\n"
            "PROBLEM logs or .audit_work is missing, non-directory, or symlinked\n"
            "result=FAIL\n"
        )
        if LOGS.is_dir() and not LOGS.is_symlink():
            replace_with_nonpass(payload.encode("utf-8"))
        _LIFECYCLE_FINALIZED = True
        print(payload, end="")
        return 1
    prelock_sentinel = (
        "FINAL VERIFICATION LIFECYCLE CHECK\n"
        "state=ACQUIRING_LOCK\n"
        f"checker_pid={os.getpid()}\n"
        f"started_at_utc={datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}\n"
        "result=FAIL\n"
    ).encode("utf-8")
    if not replace_with_nonpass(prelock_sentinel):
        problems.append("cannot invalidate prior lifecycle output before lock")
    lifecycle_lock = acquire_lifecycle_lock(problems)
    lock_pass = lifecycle_lock is not None
    if lifecycle_lock is None:
        payload = (
            "FINAL VERIFICATION LIFECYCLE CHECK\n"
            "lifecycle_lock_exclusive=FAIL\n"
            + "".join(f"PROBLEM {problem}\n" for problem in problems)
            + "result=FAIL\n"
        )
        replace_with_nonpass(payload.encode("utf-8"))
        _LIFECYCLE_FINALIZED = True
        print(payload, end="")
        return 1
    _ACTIVE_LIFECYCLE_LOCK = lifecycle_lock
    running_sentinel = (
        "FINAL VERIFICATION LIFECYCLE CHECK\n"
        "state=RUNNING\n"
        f"checker_pid={os.getpid()}\n"
        f"started_at_utc={datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}\n"
        "result=FAIL\n"
    ).encode("utf-8")
    try:
        atomic_write_bytes(FINAL_OUTPUT, running_sentinel)
    except OSError as error:
        problems.append(f"cannot invalidate prior lifecycle output: {error}")
        try:
            FINAL_OUTPUT.unlink(missing_ok=True)
        except OSError as unlink_error:
            problems.append(
                f"cannot remove prior lifecycle output: {unlink_error}"
            )
        print("FINAL VERIFICATION LIFECYCLE CHECK")
        for problem in problems:
            print(f"PROBLEM {problem}")
        print("result=FAIL")
        return 1
    lifecycle_guard = acquire_lifecycle_guard(problems)
    if lifecycle_guard is None:
        released = release_lifecycle_lock(lifecycle_lock, problems)
        if released:
            _ACTIVE_LIFECYCLE_LOCK = None
            _LIFECYCLE_FINALIZED = True
        print(running_sentinel.decode("utf-8"), end="")
        for problem in problems:
            print(f"PROBLEM {problem}")
        return 1
    _ACTIVE_LIFECYCLE_GUARD = lifecycle_guard
    guard_pass = True

    digest = current_manifest(problems)
    manifest_pass = digest is not None
    input_digest = current_input_manifest(problems)
    input_manifest_pass = input_digest is not None

    run_status_pass = False
    run_status_values: dict[str, str] = {}
    run_status_text = read_text(LOGS / "run_all_status.log", problems)
    if run_status_text is not None:
        run_status_values = exact_colon_record(
            run_status_text,
            {
                "command",
                "run_id",
                "run_state",
                "verification_input_digest",
                "source_digest",
                "started_at_utc",
                "finished_at_utc",
                "elapsed_seconds",
                "run_log_sha256",
                "exit_code",
            },
            "run_all_status.log",
            problems,
        )
        before = len(problems)
        require_equal(
            run_status_values,
            "command",
            "./MatrixConcentration/Verification/scripts/run_all.sh --fresh",
            "run_all_status.log",
            problems,
        )
        require_equal(
            run_status_values, "run_state", "PASS", "run_all_status.log", problems
        )
        require_equal(
            run_status_values,
            "verification_input_digest",
            input_digest or "UNAVAILABLE",
            "run_all_status.log",
            problems,
        )
        require_equal(
            run_status_values,
            "source_digest",
            digest or "UNAVAILABLE",
            "run_all_status.log",
            problems,
        )
        require_equal(
            run_status_values, "exit_code", "0", "run_all_status.log", problems
        )
        if not valid_run_id(run_status_values.get("run_id")):
            problems.append("run_all_status.log: invalid run_id")
        validate_status_chronology(
            run_status_values, "run_all_status.log", problems
        )
        run_status_pass = len(problems) == before

    run_counts = (0, 0, 0, 0)
    run_log_pass = False
    run_text = read_text(LOGS / "run_all.log", problems)
    if run_text is not None:
        before = len(problems)
        run_counts = marker_counts(run_text)
        if run_counts != (23, 23, 0, 0):
            problems.append(
                "run_all.log: expected START/PASS/SKIP/FAIL "
                f"(23, 23, 0, 0), measured {run_counts}"
            )
        require_terminal(
            run_text, "ALL MACHINE STAGES PASSED", "run_all.log", problems
        )
        seen_digests = re.findall(
            r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$", run_text, re.MULTILINE
        )
        allowed_digests = {
            value for value in (digest, input_digest) if value is not None
        }
        if (
            digest is None
            or input_digest is None
            or seen_digests.count(digest) < 2
            or seen_digests.count(input_digest) < 2
            or any(value not in allowed_digests for value in seen_digests)
        ):
            problems.append(
                "run_all.log: source/input manifest digest evidence is "
                f"absent or drifting: {seen_digests}"
            )
        final_index = run_text.rfind("===== FINAL SOURCE MANIFEST STABILITY ")
        terminal_index = run_text.rfind("ALL MACHINE STAGES PASSED")
        final_block = (
            run_text[final_index:terminal_index]
            if final_index >= 0 and terminal_index > final_index
            else ""
        )
        if "SOURCE MANIFEST: PASS" not in final_block.splitlines():
            problems.append("run_all.log: final manifest block does not pass")
        if run_status_values:
            require_equal(
                run_status_values,
                "run_log_sha256",
                sha256(LOGS / "run_all.log"),
                "run_all_status.log",
                problems,
            )
            if (
                f"run_id={run_status_values.get('run_id')}"
                not in run_text.splitlines()
            ):
                problems.append("run_all.log: run_id differs from status")
        if (
            f"run_id={run_status_values.get('run_id')}"
            not in run_text.splitlines()
        ):
            problems.append("run_all.log: missing bound aggregate run_id")
        expected_run_labels = [
            EXPECTED_STAGE_LABELS[stage] for stage in EXPECTED_STAGE_IDS
        ] + ["final V2 scratch refresh", "README/report consistency"]
        start_labels = re.findall(
            r"^===== START (.+?) \d{4}-\d{2}-\d{2} "
            r"\d{2}:\d{2}:\d{2} [A-Z]+ =====$",
            run_text,
            re.MULTILINE,
        )
        pass_labels = re.findall(
            r"^===== PASS  (.+?) \d{4}-\d{2}-\d{2} "
            r"\d{2}:\d{2}:\d{2} [A-Z]+ =====$",
            run_text,
            re.MULTILINE,
        )
        if start_labels != expected_run_labels:
            problems.append(
                f"run_all.log: unexpected ordered START labels {start_labels}"
            )
        if pass_labels != expected_run_labels:
            problems.append(
                f"run_all.log: unexpected ordered PASS labels {pass_labels}"
            )
        terminal_position = run_text.splitlines().index(
            "ALL MACHINE STAGES PASSED"
        ) if "ALL MACHINE STAGES PASSED" in run_text.splitlines() else -1
        if terminal_position >= 0:
            tail = run_text.splitlines()[terminal_position + 1 :]
            if (
                len(tail) != 2
                or not tail[0].startswith("finished=")
                or not tail[1].startswith("Review-tier V6 Tier B")
            ):
                problems.append(f"run_all.log: unexpected terminal tail {tail}")
        run_log_pass = len(problems) == before

    expected_markers = {f"{stage}.done" for stage in EXPECTED_STAGE_IDS}
    stage_dir_valid = STAGE_DIR.is_dir() and not STAGE_DIR.is_symlink()
    actual_markers = (
        {path.name for path in STAGE_DIR.glob("*.done")}
        if stage_dir_valid
        else set()
    )
    markers_pass = actual_markers == expected_markers
    if not stage_dir_valid:
        problems.append(
            "run_all stage directory is missing, non-directory, or symlinked"
        )
        markers_pass = False
    if not markers_pass:
        problems.append(
            "run_all stage markers: "
            f"missing={sorted(expected_markers - actual_markers)}, "
            f"extra={sorted(actual_markers - expected_markers)}"
        )
    for stage in EXPECTED_STAGE_IDS:
        marker = STAGE_DIR / f"{stage}.done"
        if not marker.is_file() or marker.is_symlink():
            problems.append(
                f"{marker.relative_to(ROOT)}: missing, nonregular, or symlinked"
            )
            markers_pass = False
            continue
        text = read_text(marker, problems)
        if text is None:
            markers_pass = False
            continue
        lines = text.splitlines()
        valid = (
            len(lines) == 3
            and lines[0] == f"stage={stage}"
            and lines[1] == f"label={EXPECTED_STAGE_LABELS[stage]}"
            and re.fullmatch(
                r"completed=\d{4}-\d{2}-\d{2}T"
                r"\d{2}:\d{2}:\d{2}Z",
                lines[2],
            )
            is not None
        )
        if not valid:
            problems.append(f"{marker.relative_to(ROOT)}: invalid contents")
            markers_pass = False
        elif run_status_values:
            before = len(problems)
            require_timestamp_within(
                lines[2].removeprefix("completed="),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                f"{marker.relative_to(ROOT)} completion",
                problems,
            )
            if len(problems) != before:
                markers_pass = False

    v1_pass = True
    v1_recovery_pass = True
    incident_pass = True
    for path, description in (
        (V1_DELETE_MARKER, "historical V1 deletion marker"),
        (V1_DONE_MARKER, "canonical replay completion marker"),
        (V1_RUNNER, "canonical replay runner"),
        (V1_RECOVERY_RUNNER, "isolated clean-build runner"),
        (V1_RECOVERY_CONFIG, "isolated clean-build Lake configuration"),
        (V1_RECOVERY_MARKER, "isolated clean-build completion marker"),
        (V1_RECOVERY_BUILD_DIR, "isolated clean-build output directory"),
    ):
        expected = (
            path.is_dir() and not path.is_symlink()
            if path == V1_RECOVERY_BUILD_DIR
            else path.is_file() and not path.is_symlink()
        )
        if not expected:
            problems.append(f"missing {description}")
            v1_pass = False
            if path in (
                V1_RECOVERY_RUNNER,
                V1_RECOVERY_CONFIG,
                V1_RECOVERY_MARKER,
                V1_RECOVERY_BUILD_DIR,
            ):
                v1_recovery_pass = False
    for path, description in (
        (INCIDENT_START_MARKER, "incident start marker"),
        (INCIDENT_DELETE_MARKER, "incident deletion marker"),
    ):
        if not path.is_file() or path.is_symlink():
            problems.append(f"missing {description}")
            incident_pass = False
    for interrupted_version, interrupted_dir in zip(
        ("v3", "v4", "v5"),
        V1_INTERRUPTED_RECOVERY_BUILD_DIRS,
        strict=True,
    ):
        if not interrupted_dir.is_dir() or interrupted_dir.is_symlink():
            problems.append(
                "missing or symlinked interrupted V1 "
                f"{interrupted_version} recovery directory"
            )
            incident_pass = False
    if os.path.lexists(REMOVED_INCIDENT_RUNNER):
        problems.append("discarded v1_recert_clean_build.sh is present")
        incident_pass = False
    if os.path.lexists(INVALID_INCIDENT_DONE_MARKER):
        problems.append("post-run v1_recert_clean_build.done artifact is present")
        incident_pass = False

    if not input_manifest_pass:
        v1_pass = False
        v1_recovery_pass = False
    run_script = read_text(RUN_ALL, problems)
    if run_script is None:
        v1_pass = False
    else:
        if 'bash "$SCRIPT_DIR/v1_clean_build.sh"' not in run_script:
            problems.append("run_all.sh does not invoke v1_clean_build.sh")
            v1_pass = False
        if 'bash "$SCRIPT_DIR/v1_recovery_clean_build.sh"' not in run_script:
            problems.append(
                "run_all.sh does not invoke v1_recovery_clean_build.sh"
            )
            v1_pass = False
            v1_recovery_pass = False
        if "v1_recert_clean_build.sh" in run_script:
            problems.append("run_all.sh references the discarded helper")
            incident_pass = False
    for runner in sorted(SCRIPT.parent.rglob("*.sh")):
        name = runner.relative_to(SCRIPT.parent).as_posix()
        runner_text = read_text(runner, problems)
        if runner_text is None:
            v1_pass = False
            if runner == V1_RECOVERY_RUNNER:
                v1_recovery_pass = False
        elif contains_recursive_rm(runner_text):
            problems.append(f"{name}: contains a recursive removal command")
            v1_pass = False
            if runner == V1_RECOVERY_RUNNER:
                v1_recovery_pass = False
    for script_path in sorted(SCRIPT.parent.rglob("*.py")):
        if script_path.resolve() == SCRIPT:
            continue
        script_text = read_text(script_path, problems)
        if script_text is None:
            v1_pass = False
            continue
        if re.search(
            r"\b(?:shutil\.)?rmtree\s*\(|"
            r"\bfind\b[^\n]*\s-delete(?:\s|$)",
            script_text,
        ):
            problems.append(
                f"{script_path.relative_to(SCRIPT.parent)}: "
                "contains a recursive deletion primitive"
            )
            v1_pass = False

    main_delete_text = read_text(V1_DELETE_LOG, problems)
    if main_delete_text is None:
        v1_pass = False
    else:
        lines = [line for line in main_delete_text.splitlines() if line]
        deletes = [line for line in lines if line.startswith("DELETE_ONCE ")]
        resumes = [
            line
            for line in lines
            if line.startswith("RESUME_WITHOUT_DELETE ")
        ]
        legacy_recert_resumes = [
            line
            for line in lines
            if line.startswith("RECERTIFICATION_RESUME_WITHOUT_DELETE ")
        ]
        unknown = [
            line
            for line in lines
            if line not in deletes
            and line not in resumes
            and line not in legacy_recert_resumes
        ]
        if len(deletes) != 1:
            problems.append(
                f"build_delete_once.log: baseline deletes={len(deletes)}, expected 1"
            )
            v1_pass = False
        if not resumes:
            problems.append("build_delete_once.log: missing resume evidence")
            v1_pass = False
        if len(legacy_recert_resumes) != 1:
            problems.append(
                "build_delete_once.log: expected exactly one disclosed legacy "
                "misfiled re-certification resume row"
            )
            v1_pass = False
        if unknown:
            problems.append(f"build_delete_once.log: unexpected rows {unknown}")
            v1_pass = False

    incident_text = read_text(INCIDENT_DELETE_LOG, problems)
    if incident_text is None:
        incident_pass = False
    else:
        lines = [line for line in incident_text.splitlines() if line]
        deletes = [
            line
            for line in lines
            if line.startswith("RECERTIFICATION_DELETE_ONCE ")
        ]
        resumes = [
            line
            for line in lines
            if line.startswith("RECERTIFICATION_RESUME_WITHOUT_DELETE ")
        ]
        if len(deletes) != 1 or not resumes or len(deletes) + len(resumes) != len(lines):
            problems.append(
                "build_delete_once.recertification.log: expected one disclosed "
                "delete and one or more no-delete resumes"
            )
            incident_pass = False

    recovery_status_values: dict[str, str] = {}
    recovery_status_keys = {
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
    recovery_status_text = read_text(V1_RECOVERY_STATUS, problems)
    if recovery_status_text is None:
        v1_pass = False
        v1_recovery_pass = False
    else:
        recovery_status_values = exact_colon_record(
            recovery_status_text,
            recovery_status_keys,
            "build_full.recertification-empty-recovery.status.log",
            problems,
        )
        before = len(problems)
        for key, expected in (
            (
                "command",
                "./MatrixConcentration/Verification/scripts/"
                "v1_recovery_clean_build.sh",
            ),
            ("run_state", "PASS"),
            (
                "evidence_mode",
                "executed_fresh_reserved_empty_build_dir",
            ),
            ("exit_code", "0"),
        ):
            require_equal(
                recovery_status_values,
                key,
                expected,
                "build_full.recertification-empty-recovery.status.log",
                problems,
            )
        require_equal(
            recovery_status_values,
            "verification_input_digest",
            input_digest or "UNAVAILABLE",
            "build_full.recertification-empty-recovery.status.log",
            problems,
        )
        require_equal(
            recovery_status_values,
            "source_digest",
            digest or "UNAVAILABLE",
            "build_full.recertification-empty-recovery.status.log",
            problems,
        )
        if V1_RECOVERY_LOG.is_file():
            require_equal(
                recovery_status_values,
                "build_log_sha256",
                sha256(V1_RECOVERY_LOG),
                "build_full.recertification-empty-recovery.status.log",
                problems,
            )
        if V1_RECOVERY_MARKER.is_file():
            require_equal(
                recovery_status_values,
                "completion_marker_sha256",
                sha256(V1_RECOVERY_MARKER),
                "build_full.recertification-empty-recovery.status.log",
                problems,
            )
        if not valid_run_id(recovery_status_values.get("run_id")):
            problems.append(
                "build_full.recertification-empty-recovery.status.log: "
                "invalid run_id"
            )
        validate_status_chronology(
            recovery_status_values,
            "build_full.recertification-empty-recovery.status.log",
            problems,
        )
        if len(problems) != before:
            v1_pass = False
            v1_recovery_pass = False
        elapsed = recovery_status_values.get("elapsed_seconds", "")
        if not elapsed.isdigit() or int(elapsed) <= 0:
            problems.append(
                "build_full.recertification-empty-recovery.status.log: "
                f"invalid elapsed_seconds={elapsed!r}"
            )
            v1_pass = False
            v1_recovery_pass = False

    recovery_reuse_values: dict[str, str] = {}
    recovery_reuse_status_text = read_text(
        V1_RECOVERY_REUSE_STATUS, problems
    )
    if recovery_reuse_status_text is None:
        v1_pass = False
        v1_recovery_pass = False
    else:
        recovery_reuse_values = exact_colon_record(
            recovery_reuse_status_text,
            recovery_status_keys,
            "v1_recovery_reuse_status.log",
            problems,
        )
        before = len(problems)
        for key, expected in (
            (
                "command",
                "./MatrixConcentration/Verification/scripts/"
                "v1_recovery_clean_build.sh",
            ),
            ("run_state", "PASS"),
            ("evidence_mode", "validated_existing_evidence"),
            ("exit_code", "0"),
        ):
            require_equal(
                recovery_reuse_values,
                key,
                expected,
                "v1_recovery_reuse_status.log",
                problems,
            )
        for key, expected in (
            ("verification_input_digest", input_digest or "UNAVAILABLE"),
            ("source_digest", digest or "UNAVAILABLE"),
        ):
            require_equal(
                recovery_reuse_values,
                key,
                expected,
                "v1_recovery_reuse_status.log",
                problems,
            )
        if V1_RECOVERY_LOG.is_file():
            require_equal(
                recovery_reuse_values,
                "build_log_sha256",
                sha256(V1_RECOVERY_LOG),
                "v1_recovery_reuse_status.log",
                problems,
            )
        if V1_RECOVERY_MARKER.is_file():
            require_equal(
                recovery_reuse_values,
                "completion_marker_sha256",
                sha256(V1_RECOVERY_MARKER),
                "v1_recovery_reuse_status.log",
                problems,
            )
        if not valid_run_id(recovery_reuse_values.get("run_id")):
            problems.append("v1_recovery_reuse_status.log: invalid run_id")
        validate_status_chronology(
            recovery_reuse_values,
            "v1_recovery_reuse_status.log",
            problems,
        )
        if run_status_values:
            require_timestamp_within(
                recovery_reuse_values.get("started_at_utc"),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                "v1_recovery_reuse_status.log start",
                problems,
            )
            require_timestamp_within(
                recovery_reuse_values.get("finished_at_utc"),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                "v1_recovery_reuse_status.log finish",
                problems,
            )
        primary_finished = parse_utc_timestamp(
            recovery_status_values.get("finished_at_utc"),
            "V1 primary recovery finish",
            problems,
        )
        reuse_started = parse_utc_timestamp(
            recovery_reuse_values.get("started_at_utc"),
            "V1 recovery reuse start",
            problems,
        )
        if (
            primary_finished is not None
            and reuse_started is not None
            and reuse_started < primary_finished
        ):
            problems.append("V1 reuse status predates the primary fresh recovery")
        if len(problems) != before:
            v1_pass = False
            v1_recovery_pass = False

    recovery_log_text = read_text(V1_RECOVERY_LOG, problems)
    if recovery_log_text is None:
        v1_pass = False
        v1_recovery_pass = False
    else:
        before = len(problems)
        statuses = re.findall(
            r"^EXIT_STATUS ([0-9]+)$", recovery_log_text, re.MULTILINE
        )
        if statuses != ["0"]:
            problems.append(
                "isolated V1 log: expected exactly one EXIT_STATUS 0, "
                f"measured {statuses!r}"
            )
        if "RECOVERY_BUILD_DIR_EXISTED_AT_START false" not in recovery_log_text:
            problems.append(
                "isolated V1 log: missing empty-build-directory provenance"
            )
        if "RECOVERY_BUILD_DIR_RESERVED_EMPTY true" not in recovery_log_text:
            problems.append(
                "isolated V1 log: missing atomic empty-directory reservation"
            )
        if (
            "v1_recovery_lakefile.toml --rehash --no-cache --no-ansi "
            "build MatrixConcentration"
        ) not in recovery_log_text:
            problems.append("isolated V1 log: unexpected build command")
        if digest is not None and f"SOURCE_DIGEST {digest}" not in recovery_log_text:
            problems.append("isolated V1 log: source digest mismatch")
        if input_digest is not None and (
            f"VERIFICATION_INPUT_DIGEST {input_digest}"
            not in recovery_log_text.splitlines()
        ):
            problems.append("isolated V1 log: verification-input digest mismatch")
        if recovery_status_values and (
            f"RUN_ID {recovery_status_values.get('run_id')}"
            not in recovery_log_text.splitlines()
        ):
            problems.append("isolated V1 log: run_id differs from status")
        terminals = re.findall(
            r"^Build completed successfully \(([1-9][0-9]*) jobs\)\.$",
            recovery_log_text,
            re.MULTILINE,
        )
        if len(terminals) != 1:
            problems.append(
                "isolated V1 log: expected one positive-job success terminal, "
                f"measured {terminals!r}"
            )
        if re.search(r"(^|:)error:", recovery_log_text, re.MULTILINE):
            problems.append("isolated V1 log: contains an error")
        if re.search(
            r"declaration uses ['\"`]?sorry",
            recovery_log_text,
            re.IGNORECASE,
        ):
            problems.append("isolated V1 log: contains a sorry warning")
        actions = project_actions(recovery_log_text)
        action_counts = Counter(actions)
        built = {module for action, module in actions if action == "Built"}
        replayed = {
            module for action, module in actions if action == "Replayed"
        }
        if (
            len(actions) != 15
            or any(count != 1 for count in action_counts.values())
            or built != EXPECTED_MODULES
            or replayed
        ):
            problems.append(
                "isolated V1 log: expected 15 Built / 0 Replayed project "
                f"actions, measured actions={len(actions)} "
                f"built={len(built)} replayed={len(replayed)}"
            )
        if "MatrixConcentration" not in built:
            problems.append("isolated V1 log: root module was not explicitly Built")
        if len(problems) != before:
            v1_pass = False
            v1_recovery_pass = False

    recovery_marker_text = read_text(V1_RECOVERY_MARKER, problems)
    if recovery_marker_text is None:
        v1_pass = False
        v1_recovery_pass = False
    else:
        marker_values = equals_values(recovery_marker_text)
        before = len(problems)
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
        if (
            len(recovery_marker_text.splitlines()) != 15
            or set(marker_values) != expected_marker_keys
        ):
            problems.append("v1_recovery_build.done: invalid exact marker shape")
        require_equal(
            marker_values,
            "marker_version",
            "7",
            "v1_recovery_build.done",
            problems,
        )
        require_equal(
            marker_values,
            "verification_input_digest",
            input_digest or "UNAVAILABLE",
            "v1_recovery_build.done",
            problems,
        )
        if not valid_run_id(marker_values.get("run_id")):
            problems.append("v1_recovery_build.done: invalid run_id")
        if recovery_status_values and (
            marker_values.get("run_id") != recovery_status_values.get("run_id")
        ):
            problems.append(
                "v1_recovery_build.done: run_id differs from primary status"
            )
        if digest is not None:
            require_equal(
                marker_values,
                "source_digest",
                digest,
                "v1_recovery_build.done",
                problems,
            )
        if V1_RECOVERY_RUNNER.is_file():
            require_equal(
                marker_values,
                "runner_sha256",
                sha256(V1_RECOVERY_RUNNER),
                "v1_recovery_build.done",
                problems,
            )
        if V1_RECOVERY_CONFIG.is_file():
            require_equal(
                marker_values,
                "config_sha256",
                sha256(V1_RECOVERY_CONFIG),
                "v1_recovery_build.done",
                problems,
            )
        config_checker = SCRIPT.parent / "check_v1_recovery_config.py"
        if config_checker.is_file():
            require_equal(
                marker_values,
                "config_checker_sha256",
                sha256(config_checker),
                "v1_recovery_build.done",
                problems,
            )
        hash_tree = SCRIPT.parent / "hash_tree.py"
        if hash_tree.is_file():
            require_equal(
                marker_values,
                "hash_tree_sha256",
                sha256(hash_tree),
                "v1_recovery_build.done",
                problems,
            )
        if V1_RECOVERY_LOG.is_file():
            require_equal(
                marker_values,
                "build_log_sha256",
                sha256(V1_RECOVERY_LOG),
                "v1_recovery_build.done",
                problems,
            )
        if (
            V1_CANONICAL_BEFORE.is_file()
            and not V1_CANONICAL_BEFORE.is_symlink()
        ):
            require_equal(
                marker_values,
                "canonical_before_sha256",
                sha256(V1_CANONICAL_BEFORE),
                "v1_recovery_build.done",
                problems,
            )
        if (
            V1_CANONICAL_AFTER.is_file()
            and not V1_CANONICAL_AFTER.is_symlink()
        ):
            require_equal(
                marker_values,
                "canonical_after_sha256",
                sha256(V1_CANONICAL_AFTER),
                "v1_recovery_build.done",
                problems,
            )
        if V1_RECOVERY_TREE.is_file() and not V1_RECOVERY_TREE.is_symlink():
            require_equal(
                marker_values,
                "recovery_tree_sha256",
                sha256(V1_RECOVERY_TREE),
                "v1_recovery_build.done",
                problems,
            )
        require_equal(
            marker_values,
            "recovery_build_dir",
            ".audit_work/v1_recertification_recovery_build_v7",
            "v1_recovery_build.done",
            problems,
        )
        if not re.fullmatch(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z",
            marker_values.get("completed_at_utc", ""),
        ):
            problems.append(
                "v1_recovery_build.done: invalid completion timestamp"
            )
        if recovery_status_values:
            require_timestamp_within(
                marker_values.get("completed_at_utc"),
                recovery_status_values.get("started_at_utc"),
                recovery_status_values.get("finished_at_utc"),
                "v1_recovery_build.done completion",
                problems,
            )
        require_equal(
            marker_values,
            "canonical_build_unchanged",
            "true",
            "v1_recovery_build.done",
            problems,
        )
        if len(problems) != before:
            v1_pass = False
            v1_recovery_pass = False

    config_check_text = read_text(V1_RECOVERY_CONFIG_CHECK, problems)
    if config_check_text is None or "result=PASS" not in config_check_text.splitlines():
        problems.append("V1 recovery Lake configuration check did not pass")
        v1_pass = False
        v1_recovery_pass = False
    if (
        not V1_CANONICAL_BEFORE.is_file()
        or V1_CANONICAL_BEFORE.is_symlink()
        or not V1_CANONICAL_AFTER.is_file()
        or V1_CANONICAL_AFTER.is_symlink()
        or V1_CANONICAL_BEFORE.read_bytes() != V1_CANONICAL_AFTER.read_bytes()
    ):
        problems.append(
            "canonical .lake/build content manifest changed during isolated V1 build"
        )
        v1_pass = False
        v1_recovery_pass = False
    if V1_RECOVERY_BUILD_DIR.is_symlink():
        problems.append("isolated V1 build directory is a symlink")
        v1_pass = False
        v1_recovery_pass = False
    elif (
        V1_RECOVERY_TREE.is_file()
        and not V1_RECOVERY_TREE.is_symlink()
        and V1_RECOVERY_BUILD_DIR.is_dir()
    ):
        completed = subprocess.run(
            [
                sys.executable,
                str(SCRIPT.parent / "hash_tree.py"),
                str(V1_RECOVERY_BUILD_DIR),
            ],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if (
            completed.returncode != 0
            or completed.stdout != V1_RECOVERY_TREE.read_bytes()
        ):
            problems.append(
                "isolated V1 build tree differs from its bound content manifest"
            )
            v1_pass = False
            v1_recovery_pass = False
    else:
        problems.append("missing isolated V1 build-tree content manifest")
        v1_pass = False
        v1_recovery_pass = False

    canonical_log_sha256 = ""
    canonical_text = read_text(V1_CANONICAL_LOG, problems)
    if canonical_text is None:
        v1_pass = False
    else:
        canonical_log_sha256 = sha256(V1_CANONICAL_LOG)
        before = len(problems)
        statuses = re.findall(
            r"^EXIT_STATUS ([0-9]+)$", canonical_text, re.MULTILINE
        )
        if statuses != ["0"]:
            problems.append(
                "canonical V1 log: expected exactly one EXIT_STATUS 0, "
                f"measured {statuses!r}"
            )
        terminals = re.findall(
            r"^Build completed successfully \(([1-9][0-9]*) jobs\)\.$",
            canonical_text,
            re.MULTILINE,
        )
        if len(terminals) != 1:
            problems.append(
                "canonical V1 log: expected one positive-job success terminal, "
                f"measured {terminals!r}"
            )
        if (
            "COMMAND " not in canonical_text
            or "--no-ansi build MatrixConcentration" not in canonical_text
        ):
            problems.append("canonical V1 log: unexpected build command")
        if digest is not None and f"SOURCE_DIGEST {digest}" not in canonical_text:
            problems.append("canonical V1 log: source digest mismatch")
        if input_digest is not None and (
            f"VERIFICATION_INPUT_DIGEST {input_digest}"
            not in canonical_text.splitlines()
        ):
            problems.append("canonical V1 log: verification-input digest mismatch")
        if run_status_values and (
            f"RUN_ID {run_status_values.get('run_id')}"
            not in canonical_text.splitlines()
        ):
            problems.append("canonical V1 log: run_id differs from aggregate")
        if re.search(r"(^|:)error:", canonical_text, re.MULTILINE):
            problems.append("canonical V1 log: contains an error")
        if re.search(
            r"declaration uses ['\"`]?sorry",
            canonical_text,
            re.IGNORECASE,
        ):
            problems.append("canonical V1 log: contains a sorry warning")
        actions = project_actions(canonical_text)
        counts = Counter(actions)
        built = {module for action, module in actions if action == "Built"}
        replayed = {
            module for action, module in actions if action == "Replayed"
        }
        expected_inner = EXPECTED_MODULES - {"MatrixConcentration"}
        if (
            len(actions) != 14
            or any(count != 1 for count in counts.values())
            or built
            or replayed != expected_inner
        ):
            problems.append(
                "canonical V1 log: expected exact 0 Built / 14 Replayed "
                f"profile, measured actions={len(actions)} "
                f"built={sorted(built)} replayed={sorted(replayed)}"
            )
        if len(problems) != before:
            v1_pass = False

    canonical_marker_text = read_text(V1_DONE_MARKER, problems)
    if canonical_marker_text is None:
        v1_pass = False
    else:
        values = equals_values(canonical_marker_text)
        before = len(problems)
        expected_canonical_marker_keys = {
            "marker_version",
            "run_id",
            "verification_input_digest",
            "runner_sha256",
            "source_digest",
            "build_log_sha256",
            "completed_at_utc",
        }
        if (
            len(canonical_marker_text.splitlines()) != 7
            or set(values) != expected_canonical_marker_keys
        ):
            problems.append("v1_clean_build.done: invalid exact marker shape")
        require_equal(
            values,
            "marker_version",
            "2",
            "v1_clean_build.done",
            problems,
        )
        if run_status_values:
            require_equal(
                values,
                "run_id",
                run_status_values.get("run_id", ""),
                "v1_clean_build.done",
                problems,
            )
        if input_digest is not None:
            require_equal(
                values,
                "verification_input_digest",
                input_digest,
                "v1_clean_build.done",
                problems,
            )
        if V1_RUNNER.is_file():
            require_equal(
                values,
                "runner_sha256",
                sha256(V1_RUNNER),
                "v1_clean_build.done",
                problems,
            )
        if digest is not None:
            require_equal(
                values,
                "source_digest",
                digest,
                "v1_clean_build.done",
                problems,
            )
        if canonical_log_sha256:
            require_equal(
                values,
                "build_log_sha256",
                canonical_log_sha256,
                "v1_clean_build.done",
                problems,
            )
        if not re.fullmatch(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z",
            values.get("completed_at_utc", ""),
        ):
            problems.append("v1_clean_build.done: invalid completion timestamp")
        if run_status_values:
            require_timestamp_within(
                values.get("completed_at_utc"),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                "v1_clean_build.done completion",
                problems,
            )
        if len(problems) != before:
            v1_pass = False

    for archive in INCIDENT_ARCHIVES:
        archive_path = LOGS / archive
        if (
            not archive_path.is_file()
            or archive_path.is_symlink()
            or archive_path.stat().st_size == 0
        ):
            problems.append(
                f"missing, empty, nonregular, or symlinked incident archive: "
                f"logs/{archive}"
            )
            incident_pass = False
    for name, (state, code) in INCIDENT_STATUSES.items():
        text = read_text(LOGS / name, problems)
        if text is None:
            incident_pass = False
            continue
        values = colon_values(text)
        before = len(problems)
        require_equal(values, "run_state", state, name, problems)
        require_equal(values, "exit_code", code, name, problems)
        if len(problems) != before:
            incident_pass = False
    for name, expected_values in INCOMPLETE_INCIDENT_STATUSES.items():
        text = read_text(LOGS / name, problems)
        if text is None:
            incident_pass = False
            continue
        before = len(problems)
        values = exact_colon_record(
            text,
            set(expected_values),
            name,
            problems,
        )
        for key, expected in expected_values.items():
            require_equal(values, key, expected, name, problems)
        if len(problems) != before:
            incident_pass = False
    for name, expected_counts in INVALID_NOMINAL_PASS_TRANSCRIPTS.items():
        partial_text = read_text(LOGS / name, problems)
        if partial_text is None:
            incident_pass = False
            continue
        partial_counts = marker_counts(partial_text)
        if partial_counts != expected_counts:
            problems.append(
                f"{name}: expected {expected_counts} markers, "
                f"measured {partial_counts}"
            )
            incident_pass = False
        if "ALL MACHINE STAGES PASSED" in partial_text.splitlines():
            problems.append(f"{name}: unexpected aggregate terminal")
            incident_pass = False
    interrupted_v3_text = read_text(
        LOGS
        / (
            "build_full.recertification-empty-recovery."
            "invalid-v3-interrupted-20260720T090811Z.log"
        ),
        problems,
    )
    if interrupted_v3_text is None:
        incident_pass = False
    elif (
        re.search(r"^EXIT_STATUS ", interrupted_v3_text, re.MULTILINE)
        or re.search(
            r"^Build completed successfully ",
            interrupted_v3_text,
            re.MULTILINE,
        )
    ):
        problems.append(
            "interrupted V1 v3 archive unexpectedly contains a completion marker"
        )
        incident_pass = False
    interrupted_v5_log = (
        "build_full.recertification-empty-recovery."
        "invalid-v5-interrupted-20260720T093501Z.log"
    )
    interrupted_v5_status = (
        "build_full.recertification-empty-recovery."
        "invalid-v5-interrupted-20260720T093501Z.status.log"
    )
    interrupted_v5_text = read_text(LOGS / interrupted_v5_log, problems)
    interrupted_v5_status_text = read_text(
        LOGS / interrupted_v5_status,
        problems,
    )
    if interrupted_v5_text is None or interrupted_v5_status_text is None:
        incident_pass = False
    else:
        interrupted_v5_values = colon_values(interrupted_v5_status_text)
        if (
            re.search(r"^EXIT_STATUS ", interrupted_v5_text, re.MULTILINE)
            or re.search(
                r"^Build completed successfully ",
                interrupted_v5_text,
                re.MULTILINE,
            )
        ):
            problems.append(
                "interrupted V1 v5 archive unexpectedly contains a "
                "completion marker"
            )
            incident_pass = False
        if interrupted_v5_values.get("build_log_sha256") != sha256(
            LOGS / interrupted_v5_log
        ):
            problems.append(
                "interrupted V1 v5 status does not bind its archived log"
            )
            incident_pass = False
        if (
            interrupted_v5_values.get("completion_marker_sha256")
            != "UNAVAILABLE"
        ):
            problems.append(
                "interrupted V1 v5 status unexpectedly claims a "
                "completion marker"
            )
            incident_pass = False

    build_summary_text = read_text(LOGS / "build_audit_summary.txt", problems)
    if build_summary_text is None:
        v1_pass = False
    else:
        values = equals_values(build_summary_text)
        before = len(problems)
        for key, expected in (
            ("clean_evidence", "isolated_reserved_empty_build_directory"),
            ("clean_provenance_valid", "true"),
            ("build_exit_zero", "true"),
            ("build_exit_status_markers", "1"),
            ("build_success_terminals", "1"),
            ("build_errors", "0"),
            ("built_modules", "15"),
            ("observed_module_actions", "15"),
            ("duplicate_module_actions", "0"),
            ("built_action_modules", "15"),
            ("replayed_action_modules", "0"),
            ("root_target_inferred_from_success", "false"),
            ("expected_modules", "15"),
            ("missing_modules", "0"),
            ("unexpected_modules", "0"),
            ("build_sorry_warnings", "0"),
            ("canonical_replay_exit_zero", "true"),
            ("canonical_replay_exit_status_markers", "1"),
            ("canonical_replay_success_terminals", "1"),
            ("canonical_replay_errors", "0"),
            ("canonical_replay_covered_modules", "15"),
            ("canonical_replay_observed_module_actions", "14"),
            ("canonical_replay_duplicate_module_actions", "0"),
            ("canonical_replay_built_action_modules", "0"),
            ("canonical_replay_replayed_action_modules", "14"),
            ("canonical_replay_root_target_inferred", "true"),
            ("canonical_replay_sorry_warnings", "0"),
            ("calibration_sorry_warnings", "2"),
            ("calibration_expected_sorry_warnings", "2"),
            ("calibration_detected", "true"),
        ):
            require_equal(values, key, expected, "build_audit_summary.txt", problems)
        build_warnings = values.get("build_warnings", "")
        replay_warnings = values.get("canonical_replay_warnings", "")
        if (
            not build_warnings.isdigit()
            or not replay_warnings.isdigit()
            or build_warnings != replay_warnings
        ):
            problems.append(
                "build_audit_summary.txt: recovery/canonical warning totals "
                f"must be equal nonnegative integers, measured "
                f"{build_warnings!r}/{replay_warnings!r}"
            )
        if V1_RECOVERY_LOG.is_file():
            require_equal(
                values,
                "clean_build_log_sha256",
                sha256(V1_RECOVERY_LOG),
                "build_audit_summary.txt",
                problems,
            )
        if canonical_log_sha256:
            require_equal(
                values,
                "canonical_replay_log_sha256",
                canonical_log_sha256,
                "build_audit_summary.txt",
                problems,
            )
        if len(problems) != before:
            v1_pass = False

    v6_status_pass = False
    v6_status_values: dict[str, str] = {}
    text = read_text(LOGS / "v6_run_status.log", problems)
    if text is not None:
        v6_status_values = exact_colon_record(
            text,
            {
                "command",
                "run_id",
                "run_state",
                "verification_input_digest",
                "source_digest",
                "started_at_utc",
                "finished_at_utc",
                "elapsed_seconds",
                "run_log_sha256",
                "exit_code",
            },
            "v6_run_status.log",
            problems,
        )
        before = len(problems)
        for key, expected in (
            (
                "command",
                "./MatrixConcentration/Verification/scripts/v6_run.sh",
            ),
            ("run_state", "PASS"),
            ("verification_input_digest", input_digest or "UNAVAILABLE"),
            ("source_digest", digest or "UNAVAILABLE"),
            ("exit_code", "0"),
        ):
            require_equal(
                v6_status_values, key, expected, "v6_run_status.log", problems
            )
        if not valid_run_id(v6_status_values.get("run_id")):
            problems.append("v6_run_status.log: invalid run_id")
        validate_status_chronology(
            v6_status_values, "v6_run_status.log", problems
        )
        aggregate_finished = parse_utc_timestamp(
            run_status_values.get("finished_at_utc"),
            "aggregate finish before standalone V6",
            problems,
        )
        v6_started = parse_utc_timestamp(
            v6_status_values.get("started_at_utc"),
            "standalone V6 start",
            problems,
        )
        if (
            aggregate_finished is not None
            and v6_started is not None
            and v6_started < aggregate_finished
        ):
            problems.append("standalone V6 status predates aggregate completion")
        v6_status_pass = len(problems) == before
    v6_counts = (0, 0, 0, 0)
    v6_log_pass = False
    text = read_text(LOGS / "v6_run.log", problems)
    if text is not None:
        before = len(problems)
        v6_counts = marker_counts(text)
        if v6_counts != (18, 18, 0, 0):
            problems.append(f"v6_run.log: measured markers {v6_counts}")
        require_ordered_stage_labels(
            text,
            EXPECTED_V6_STAGE_LABELS,
            "v6_run.log",
            problems,
            timestamped=False,
        )
        require_terminal(
            text,
            "V6 ALL STAGES PASSED",
            "v6_run.log",
            problems,
            final_nonempty=True,
        )
        v6_digests = re.findall(
            r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$", text, re.MULTILINE
        )
        allowed_v6_digests = {
            value for value in (digest, input_digest) if value is not None
        }
        if (
            digest is None
            or input_digest is None
            or v6_digests.count(digest) < 2
            or v6_digests.count(input_digest) < 2
            or any(value not in allowed_v6_digests for value in v6_digests)
        ):
            problems.append(
                "v6_run.log: source/input manifest digest evidence is "
                f"absent or drifting: {v6_digests}"
            )
        if v6_status_values:
            require_equal(
                v6_status_values,
                "run_log_sha256",
                sha256(LOGS / "v6_run.log"),
                "v6_run_status.log",
                problems,
            )
            if (
                f"run_id={v6_status_values.get('run_id')}"
                not in text.splitlines()
            ):
                problems.append("v6_run.log: run_id differs from status")
        v6_log_pass = len(problems) == before
    v6_initial_manifest_pass = require_manifest_log(
        LOGS / "v6_manifest_check.log", digest, problems
    )
    # V6 writes its final source-manifest gate into v6_run.log rather than a
    # separate v6_final_manifest_check.log. Validate the block after the
    # explicit final marker so this follows the actual V6 lifecycle.
    v6_final_manifest_pass = False
    v6_run_text = read_text(LOGS / "v6_run.log", problems)
    if v6_run_text is not None:
        before = len(problems)
        final_index = v6_run_text.rfind(
            "===== FINAL SOURCE MANIFEST STABILITY ====="
        )
        terminal_index = v6_run_text.rfind("V6 ALL STAGES PASSED")
        final_block = (
            v6_run_text[final_index:terminal_index]
            if final_index >= 0 and terminal_index > final_index
            else ""
        )
        if "SOURCE MANIFEST: PASS" not in final_block.splitlines():
            problems.append("v6_run.log: final manifest block does not pass")
        final_match = re.search(
            r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$",
            final_block,
            re.MULTILINE,
        )
        if final_match is None:
            problems.append("v6_run.log: final manifest block missing digest")
        elif digest is not None and final_match.group(1) != digest:
            problems.append(
                "v6_run.log: final manifest digest "
                f"{final_match.group(1)} differs from {digest}"
            )
        v6_final_manifest_pass = len(problems) == before
    v6_metrics_pass = True
    for name, expected in (
        (
            "v6_tier_b_run.log",
            {
                "STATUS": "PASS",
                "ROWS": "467",
                "OK": "433",
                "SUSPECT": "34",
                "VACUOUS": "0",
                "ERRORS": "0",
            },
        ),
        (
            "v6_tier_c_coverage_run.log",
            {
                "STATUS": "PASS",
                "SAMPLED_OK": "40",
                "SUSPECT": "34",
                "TOTAL": "74",
                "COVERED": "74",
                "UNCOVERED": "0",
                "ERRORS": "0",
            },
        ),
    ):
        text = read_text(LOGS / name, problems)
        if text is None:
            v6_metrics_pass = False
            continue
        values = space_values(text)
        before = len(problems)
        for key, value in expected.items():
            require_equal(values, key, value, name, problems)
        if len(problems) != before:
            v6_metrics_pass = False
    v6_axioms_pass = True
    v6_witness_rows = read_tsv(LOGS / "v6_witness_axioms.tsv", problems)
    v6_witness_names = [row.get("name", "") for row in v6_witness_rows]
    if (
        len(v6_witness_rows) != 74
        or len(v6_witness_names) != len(set(v6_witness_names))
        or any(not name for name in v6_witness_names)
    ):
        problems.append(
            "v6_witness_axioms.tsv: expected 74 uniquely named witnesses"
        )
        v6_axioms_pass = False
    for row in v6_witness_rows:
        axioms = {value for value in row.get("axioms", "").split(",") if value}
        if axioms != ALLOWED_AXIOMS:
            problems.append(
                f"v6_witness_axioms.tsv: {row.get('name')} "
                f"axioms={sorted(axioms)}"
            )
            v6_axioms_pass = False

    v7_status_pass = False
    v7_status_values: dict[str, str] = {}
    text = read_text(LOGS / "v7_run_status.log", problems)
    if text is not None:
        v7_status_values = exact_colon_record(
            text,
            {
                "command",
                "run_id",
                "run_state",
                "verification_input_digest",
                "source_digest",
                "started_at_utc",
                "finished_at_utc",
                "elapsed_seconds",
                "run_log_sha256",
                "load_bearing_definitions",
                "sanity_covered",
                "dead_code_candidates",
                "exit_code",
            },
            "v7_run_status.log",
            problems,
        )
        before = len(problems)
        for key, expected in (
            (
                "command",
                "./MatrixConcentration/Verification/scripts/v7_run.sh",
            ),
            ("run_state", "PASS"),
            ("verification_input_digest", input_digest or "UNAVAILABLE"),
            ("source_digest", digest or "UNAVAILABLE"),
            ("load_bearing_definitions", "51"),
            ("sanity_covered", "51"),
            ("dead_code_candidates", "78"),
            ("exit_code", "0"),
        ):
            require_equal(
                v7_status_values, key, expected, "v7_run_status.log", problems
            )
        if not valid_run_id(v7_status_values.get("run_id")):
            problems.append("v7_run_status.log: invalid run_id")
        validate_status_chronology(
            v7_status_values, "v7_run_status.log", problems
        )
        v6_finished = parse_utc_timestamp(
            v6_status_values.get("finished_at_utc"),
            "standalone V6 finish before V7",
            problems,
        )
        v7_started = parse_utc_timestamp(
            v7_status_values.get("started_at_utc"),
            "standalone V7 start",
            problems,
        )
        if (
            v6_finished is not None
            and v7_started is not None
            and v7_started < v6_finished
        ):
            problems.append("standalone V7 status predates V6 completion")
        v7_status_pass = len(problems) == before
    v7_log_pass = False
    v7_run_text = read_text(LOGS / "v7_run.log", problems)
    if v7_run_text is not None:
        before = len(problems)
        require_terminal(
            v7_run_text,
            "V7 ALL STAGES PASSED",
            "v7_run.log",
            problems,
            final_nonempty=True,
        )
        v7_input_digests = re.findall(
            r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$",
            v7_run_text,
            re.MULTILINE,
        )
        if (
            input_digest is None
            or len(v7_input_digests) < 2
            or any(value != input_digest for value in v7_input_digests)
        ):
            problems.append(
                "v7_run.log: verification-input digest evidence is "
                f"absent or drifting: {v7_input_digests}"
            )
        if v7_status_values:
            require_equal(
                v7_status_values,
                "run_log_sha256",
                sha256(LOGS / "v7_run.log"),
                "v7_run_status.log",
                problems,
            )
            if (
                f"run_id={v7_status_values.get('run_id')}"
                not in v7_run_text.splitlines()
            ):
                problems.append("v7_run.log: run_id differs from status")
        v7_log_pass = len(problems) == before
    v7_summary_pass = False
    text = read_text(LOGS / "v7_sanity_summary.log", problems)
    if text is not None:
        values = space_values(text)
        before = len(problems)
        for key, expected in (
            ("LOAD_BEARING_DEFINITIONS", "51"),
            ("COVERED", "51"),
            ("CITATIONS", "32"),
            ("COMPILED_NAMED_WITNESSES", "19"),
            ("ERRORS", "0"),
            ("VERDICT", "PASS"),
        ):
            require_equal(values, key, expected, "v7_sanity_summary.log", problems)
        v7_summary_pass = len(problems) == before
    v7_initial_manifest_pass = require_manifest_log(
        LOGS / "v7_manifest_check.log", digest, problems
    )
    v7_final_manifest_pass = require_manifest_log(
        LOGS / "v7_final_manifest_check.log", digest, problems
    )
    v7_axioms_pass = True
    rows = read_tsv(LOGS / "v7_witness_axioms.tsv", problems)
    if len(rows) != 15:
        problems.append(f"v7_witness_axioms.tsv: rows={len(rows)}, expected 15")
        v7_axioms_pass = False
    witness_names = [row.get("name", "") for row in rows]
    if (
        len(witness_names) != len(set(witness_names))
        or set(witness_names) != EXPECTED_V7_WITNESS_NAMES
    ):
        problems.append(
            "v7_witness_axioms.tsv: witness names are duplicated or differ "
            f"from the expected set: {witness_names}"
        )
        v7_axioms_pass = False
    for row in rows:
        axioms = {value for value in row.get("axioms", "").split(",") if value}
        if axioms != ALLOWED_AXIOMS:
            problems.append(
                f"v7_witness_axioms.tsv: {row.get('name')} axioms={sorted(axioms)}"
            )
            v7_axioms_pass = False

    v10_status_pass = False
    v10_status_values: dict[str, str] = {}
    text = read_text(LOGS / "v10_run_status.log", problems)
    if text is not None:
        v10_status_values = exact_colon_record(
            text,
            {
                "command",
                "run_id",
                "parent_run_id",
                "run_state",
                "verification_input_digest",
                "source_digest",
                "started_at_utc",
                "finished_at_utc",
                "elapsed_seconds",
                "run_log_sha256",
                "exit_code",
                "last_stage",
            },
            "v10_run_status.log",
            problems,
        )
        before = len(problems)
        for key, expected in (
            (
                "command",
                "./MatrixConcentration/Verification/scripts/v10_run.sh",
            ),
            ("parent_run_id", "standalone"),
            ("run_state", "PASS"),
            ("verification_input_digest", input_digest or "UNAVAILABLE"),
            ("source_digest", digest or "UNAVAILABLE"),
            ("exit_code", "0"),
            ("last_stage", "complete"),
        ):
            require_equal(
                v10_status_values,
                key,
                expected,
                "v10_run_status.log",
                problems,
            )
        if not valid_run_id(v10_status_values.get("run_id")):
            problems.append("v10_run_status.log: invalid run_id")
        validate_status_chronology(
            v10_status_values, "v10_run_status.log", problems
        )
        aggregate_finished = parse_utc_timestamp(
            run_status_values.get("finished_at_utc"),
            "aggregate finish before standalone V10",
            problems,
        )
        standalone_started = parse_utc_timestamp(
            v10_status_values.get("started_at_utc"),
            "standalone V10 start",
            problems,
        )
        v7_finished = parse_utc_timestamp(
            v7_status_values.get("finished_at_utc"),
            "standalone V7 finish before V10",
            problems,
        )
        if (
            aggregate_finished is not None
            and standalone_started is not None
            and standalone_started < aggregate_finished
        ):
            problems.append("standalone V10 status predates aggregate completion")
        if (
            v7_finished is not None
            and standalone_started is not None
            and standalone_started < v7_finished
        ):
            problems.append("standalone V10 status predates V7 completion")
        v10_status_pass = len(problems) == before
    v10_counts = (0, 0, 0, 0)
    v10_log_pass = False
    text = read_text(LOGS / "v10_run.log", problems)
    if text is not None:
        before = len(problems)
        v10_counts = marker_counts(text)
        if v10_counts != (7, 7, 0, 0):
            problems.append(f"v10_run.log: measured markers {v10_counts}")
        require_ordered_stage_labels(
            text,
            EXPECTED_V10_STAGE_LABELS,
            "v10_run.log",
            problems,
            timestamped=True,
        )
        require_terminal(
            text,
            "V10 ALL MACHINE STAGES PASSED",
            "v10_run.log",
            problems,
            final_nonempty=True,
        )
        v10_digests = re.findall(
            r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$", text, re.MULTILINE
        )
        allowed_v10_digests = {
            value for value in (digest, input_digest) if value is not None
        }
        if (
            digest is None
            or input_digest is None
            or v10_digests.count(digest) < 2
            or v10_digests.count(input_digest) < 2
            or any(value not in allowed_v10_digests for value in v10_digests)
        ):
            problems.append(
                "v10_run.log: source/input manifest digest evidence is "
                f"absent or drifting: {v10_digests}"
            )
        if v10_status_values:
            require_equal(
                v10_status_values,
                "run_log_sha256",
                sha256(LOGS / "v10_run.log"),
                "v10_run_status.log",
                problems,
            )
            if (
                f"run_id={v10_status_values.get('run_id')}"
                not in text.splitlines()
            ):
                problems.append("v10_run.log: run_id differs from status")
            if "parent_run_id=standalone" not in text.splitlines():
                problems.append("v10_run.log: parent_run_id is not standalone")
        v10_log_pass = len(problems) == before

    v10_aggregate_pass = False
    v10_aggregate_values: dict[str, str] = {}
    aggregate_status_text = read_text(V10_AGGREGATE_STATUS, problems)
    aggregate_log_text = read_text(V10_AGGREGATE_LOG, problems)
    if aggregate_status_text is not None and aggregate_log_text is not None:
        before = len(problems)
        v10_aggregate_values = exact_colon_record(
            aggregate_status_text,
            {
                "command",
                "run_id",
                "parent_run_id",
                "run_state",
                "verification_input_digest",
                "source_digest",
                "started_at_utc",
                "finished_at_utc",
                "elapsed_seconds",
                "run_log_sha256",
                "exit_code",
                "last_stage",
            },
            "v10_run_status.aggregate.log",
            problems,
        )
        for key, expected in (
            (
                "command",
                "./MatrixConcentration/Verification/scripts/v10_run.sh",
            ),
            ("parent_run_id", run_status_values.get("run_id", "")),
            ("run_state", "PASS"),
            ("verification_input_digest", input_digest or "UNAVAILABLE"),
            ("source_digest", digest or "UNAVAILABLE"),
            ("exit_code", "0"),
            ("last_stage", "complete"),
        ):
            require_equal(
                v10_aggregate_values,
                key,
                expected,
                "v10_run_status.aggregate.log",
                problems,
            )
        if not valid_run_id(v10_aggregate_values.get("run_id")):
            problems.append("v10_run_status.aggregate.log: invalid run_id")
        validate_status_chronology(
            v10_aggregate_values,
            "v10_run_status.aggregate.log",
            problems,
        )
        if run_status_values:
            require_timestamp_within(
                v10_aggregate_values.get("started_at_utc"),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                "aggregate V10 child start",
                problems,
            )
            require_timestamp_within(
                v10_aggregate_values.get("finished_at_utc"),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                "aggregate V10 child finish",
                problems,
            )
        require_equal(
            v10_aggregate_values,
            "run_log_sha256",
            sha256(V10_AGGREGATE_LOG),
            "v10_run_status.aggregate.log",
            problems,
        )
        aggregate_counts = marker_counts(aggregate_log_text)
        if aggregate_counts != (7, 7, 0, 0):
            problems.append(
                "v10_run.aggregate.log: expected marker counts "
                f"(7, 7, 0, 0), measured {aggregate_counts}"
            )
        require_ordered_stage_labels(
            aggregate_log_text,
            EXPECTED_V10_STAGE_LABELS,
            "v10_run.aggregate.log",
            problems,
            timestamped=True,
        )
        require_terminal(
            aggregate_log_text,
            "V10 ALL MACHINE STAGES PASSED",
            "v10_run.aggregate.log",
            problems,
            final_nonempty=True,
        )
        aggregate_digests = re.findall(
            r"^TOP_LEVEL_SHA256 ([0-9a-f]{64})$",
            aggregate_log_text,
            re.MULTILINE,
        )
        allowed_aggregate_digests = {
            value for value in (digest, input_digest) if value is not None
        }
        if (
            digest is None
            or input_digest is None
            or aggregate_digests.count(digest) < 2
            or aggregate_digests.count(input_digest) < 2
            or any(
                value not in allowed_aggregate_digests
                for value in aggregate_digests
            )
        ):
            problems.append(
                "v10_run.aggregate.log: source/input manifest digest "
                f"evidence is absent or drifting: {aggregate_digests}"
            )
        if (
            f"run_id={v10_aggregate_values.get('run_id')}"
            not in aggregate_log_text.splitlines()
        ):
            problems.append("v10_run.aggregate.log: child run_id mismatch")
        if (
            f"parent_run_id={run_status_values.get('run_id')}"
            not in aggregate_log_text.splitlines()
        ):
            problems.append("v10_run.aggregate.log: parent run_id mismatch")
        v10_aggregate_pass = len(problems) == before
    v10_initial_manifest_pass = require_manifest_log(
        LOGS / "v10_manifest_check.log", digest, problems
    )
    v10_final_manifest_pass = require_manifest_log(
        LOGS / "v10_final_manifest_check.log", digest, problems
    )

    v10_summary_pass = False
    text = read_text(LOGS / "v10_summary.txt", problems)
    if text is not None:
        values = space_values(text)
        before = len(problems)
        for key, expected in (
            ("FILE_WALK_LEAN_FILES", "15"),
            ("ENVIRONMENT_MODULES", "15"),
            ("ENVIRONMENT_PROJECT_CONSTANTS", "2213"),
            ("V4_AXIOM_AUDIT_CONSTANTS", "2213"),
            ("ENVIRONMENT_COVERAGE_GUARD", "PASS"),
            ("ENVIRONMENT_PREDICATES", "14"),
            ("TEXT_PREDICATES", "14"),
            ("ENVIRONMENT_TEXT_DIFF", "0"),
            ("SOURCE_PROVED", "7"),
            ("SOURCE_CONSUMED_ONLY", "6"),
            ("SOURCE_DEAD", "1"),
            ("PROP_BINDER_ROWS", "3827"),
            ("UNIQUE_PROP_BINDER_TYPE_HASHES", "542"),
            ("MANUAL_REVIEW_OBLIGATION_TYPE_HASHES", "368"),
            ("INLINE_REVIEW_QUEUE_TYPE_HASHES", "0"),
            ("INSTANCE_BINDER_ROWS", "4762"),
            ("INSTANCE_UNIQUE_HEADS", "22"),
            ("CALIBRATION_ROWS", "5"),
            ("CALIBRATION_FAILURES", "0"),
            ("ERRORS", "0"),
            ("VERDICT", "PASS"),
        ):
            require_equal(values, key, expected, "v10_summary.txt", problems)
        v10_summary_pass = len(problems) == before

    v10_compile_pass = all(
        require_clean_lean_log(LOGS / name, problems)
        for name in (
            "v10_environment_compile.log",
            "v10_conditional_calibration_compile.log",
            "v10_witnesses_compile.log",
        )
    )
    v10_witness_rows = read_tsv(LOGS / "v10_witness_axioms.tsv", problems)
    if len(v10_witness_rows) != 1:
        problems.append(
            f"v10_witness_axioms.tsv: rows={len(v10_witness_rows)}, expected 1"
        )
        v10_compile_pass = False
    else:
        if v10_witness_rows[0].get("name") != EXPECTED_V10_WITNESS_NAME:
            problems.append("v10_witness_axioms.tsv: unexpected witness name")
            v10_compile_pass = False
        if {
            value
            for value in v10_witness_rows[0].get("axioms", "").split(",")
            if value
        } != ALLOWED_AXIOMS:
            problems.append("v10_witness_axioms.tsv: unexpected axiom set")
            v10_compile_pass = False

    curated = read_tsv(
        VERIFY / "curation" / "v10_inline_adjudication.tsv", problems
    )
    obligations = read_tsv(LOGS / "v10_inline_review_obligations.tsv", problems)
    queue = read_tsv(LOGS / "v10_inline_review_queue.tsv", problems)
    curated_hashes = {row.get("type_hash", "") for row in curated}
    obligation_hashes = {row.get("type_hash", "") for row in obligations}
    dispositions = Counter(row.get("adjudication", "") for row in curated)
    v10_curation_pass = (
        len(curated) == 368
        and len(curated_hashes) == 368
        and len(obligations) == 368
        and curated_hashes == obligation_hashes
        and len(queue) == 0
        and dispositions["ROUTINE_EXPLICIT_HYPOTHESIS"] == 359
        and dispositions["DISCHARGED_BY_SOURCE_CALLER"] == 9
    )
    if not v10_curation_pass:
        problems.append(
            "V10 curation sets/counts do not equal 368 obligations, "
            "359 routine, 9 discharged, queue 0"
        )

    quality_path = LOGS / "v10_curation_quality_review.md"
    quality_pass = (
        quality_path.is_file()
        and not quality_path.is_symlink()
        and sha256(quality_path) == EXPECTED_V10_QUALITY_SHA256
    )
    if not quality_pass:
        problems.append("v10_curation_quality_review.md: digest mismatch")
    v10_quality_inputs_pass = True
    for path, expected_sha256 in V10_QUALITY_INPUT_SHA256.items():
        if not path.is_file() or path.is_symlink():
            problems.append(
                "V10 quality-review input missing or symlinked: "
                f"{path.relative_to(ROOT)}"
            )
            v10_quality_inputs_pass = False
        elif sha256(path) != expected_sha256:
            problems.append(
                f"V10 quality-review input digest mismatch: "
                f"{path.relative_to(ROOT)}"
            )
            v10_quality_inputs_pass = False

    environment_pass = False
    environment_text = read_text(LOGS / "environment.txt", problems)
    if environment_text is not None:
        before = len(problems)
        required_environment_lines = {
            f"Canonical project root: {ROOT}",
            f"Physical project root: {ROOT.resolve()}",
            f"lean-toolchain: leanprover/lean4:v{EXPECTED_LEAN_VERSION}",
            "Flat source .lean count: 14",
            "Root module: MatrixConcentration.lean",
            "Universe file count:",
            "15",
        }
        missing_environment_lines = (
            required_environment_lines - set(environment_text.splitlines())
        )
        if missing_environment_lines:
            problems.append(
                "environment.txt: missing exact environment lines "
                f"{sorted(missing_environment_lines)}"
            )
        if (
            f"Lake version 5.0.0-src+{EXPECTED_LEAN_COMMIT[:7]} "
            f"(Lean version {EXPECTED_LEAN_VERSION})"
            not in environment_text.splitlines()
        ):
            problems.append("environment.txt: unexpected Lake/Lean version")
        expected_lean_banner = (
            f"Lean (version {EXPECTED_LEAN_VERSION}, "
            f"arm64-apple-darwin24.6.0, commit {EXPECTED_LEAN_COMMIT}, Release)"
        )
        if environment_text.splitlines().count(expected_lean_banner) != 2:
            problems.append(
                "environment.txt: expected two exact Lean version banners"
            )
        if (
            f"leanprover/lean4:v{EXPECTED_LEAN_VERSION} "
            f"(overridden by '{ROOT}/lean-toolchain')"
            not in environment_text
        ):
            problems.append("environment.txt: active toolchain is not pinned")
        try:
            manifest_data = json.loads(
                (ROOT / "lake-manifest.json").read_text(encoding="utf-8")
            )
            mathlib_rows = [
                package
                for package in manifest_data.get("packages", [])
                if package.get("name") == "mathlib"
            ]
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            problems.append(f"lake-manifest.json: cannot parse: {error}")
            mathlib_rows = []
        if (
            len(mathlib_rows) != 1
            or mathlib_rows[0].get("rev") != EXPECTED_MATHLIB_REV
            or mathlib_rows[0].get("inputRev")
            != f"v{EXPECTED_LEAN_VERSION}"
        ):
            problems.append("lake-manifest.json: unexpected mathlib pin")
        if (
            f'"rev": "{EXPECTED_MATHLIB_REV}"' not in environment_text
            or f'"inputRev": "v{EXPECTED_LEAN_VERSION}"'
            not in environment_text
        ):
            problems.append("environment.txt: mathlib pin is absent")
        symlink_section = environment_text.partition(
            "In-universe symlinks:\n"
        )[2].partition("\n[Lake library declaration]")[0]
        if symlink_section.strip():
            problems.append(
                "environment.txt: in-universe symlink list is not empty"
            )
        captured_match = re.search(
            r"^Captured UTC: (.+)$", environment_text, re.MULTILINE
        )
        if captured_match is None:
            problems.append("environment.txt: missing captured UTC timestamp")
        elif run_status_values:
            require_timestamp_within(
                captured_match.group(1),
                run_status_values.get("started_at_utc"),
                run_status_values.get("finished_at_utc"),
                "environment.txt capture",
                problems,
            )
        environment_pass = len(problems) == before

    claims_count, claims_digest = write_final_claims_manifest(problems)
    claims_stable = claims_count == 14 and claims_digest is not None

    consistency_completed = subprocess.run(
        [sys.executable, str(SCRIPT.parent / "check_consistency.py")],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if (
        consistency_completed.returncode != 0
        or "result=PASS" not in consistency_completed.stdout.splitlines()
    ):
        problems.append(
            "fresh report consistency check failed: "
            f"exit={consistency_completed.returncode}"
        )
    consistency_pass = False
    text = read_text(LOGS / "consistency_check.txt", problems)
    if text is not None:
        values = equals_values(text)
        before = len(problems)
        for key, expected in (
            ("reports", "10"),
            ("index_rows", "10"),
            ("report_findings", "16"),
            ("summary_findings", "16"),
            ("problems", "0"),
            ("result", "PASS"),
        ):
            require_equal(values, key, expected, "consistency_check.txt", problems)
        consistency_pass = len(problems) == before

    post_consistency_count, post_consistency_digest = (
        write_final_claims_manifest(problems)
    )
    if (
        post_consistency_count != claims_count
        or post_consistency_digest != claims_digest
    ):
        problems.append(
            "final claims changed while running the consistency check: "
            f"{claims_digest} -> {post_consistency_digest}"
        )
        claims_stable = False

    final_digest = current_manifest(problems)
    final_input_digest = current_input_manifest(problems)
    source_stable = digest is not None and final_digest == digest
    input_stable = (
        input_digest is not None and final_input_digest == input_digest
    )
    if not source_stable:
        problems.append(
            f"source digest changed during lifecycle check: "
            f"{digest} -> {final_digest}"
        )
    if not input_stable:
        problems.append(
            f"verification-input digest changed during lifecycle check: "
            f"{input_digest} -> {final_input_digest}"
        )
    final_claims_count, final_claims_digest = write_final_claims_manifest(
        problems
    )
    if (
        final_claims_count != claims_count
        or final_claims_digest != claims_digest
    ):
        problems.append(
            "final claims changed during lifecycle check: "
            f"{claims_digest} -> {final_claims_digest}"
        )
        claims_stable = False
    claims_count = final_claims_count
    claims_digest = final_claims_digest
    guard_pass = validate_lifecycle_guard(lifecycle_guard, problems)

    def output_text() -> str:
        lines = [
            "FINAL VERIFICATION LIFECYCLE CHECK",
            f"audit_directories={'PASS' if audit_directories_pass else 'FAIL'}",
            f"lifecycle_lock_exclusive={'PASS' if lock_pass else 'FAIL'}",
            (
                "lifecycle_finalization_guard="
                f"{'PASS' if guard_pass else 'FAIL'}"
            ),
            f"source_manifest={'PASS' if manifest_pass else 'FAIL'}",
            f"source_manifest_stable={'PASS' if source_stable else 'FAIL'}",
            f"source_digest={digest or 'UNAVAILABLE'}",
            (
                "verification_input_manifest="
                f"{'PASS' if input_manifest_pass else 'FAIL'}"
            ),
            (
                "verification_input_manifest_stable="
                f"{'PASS' if input_stable else 'FAIL'}"
            ),
            f"verification_input_digest={input_digest or 'UNAVAILABLE'}",
            (
                f"final_claims_manifest={claims_count}/14 "
                f"{'PASS' if claims_digest is not None else 'FAIL'}"
            ),
            f"final_claims_stable={'PASS' if claims_stable else 'FAIL'}",
            f"final_claims_digest={claims_digest or 'UNAVAILABLE'}",
            f"environment={'PASS' if environment_pass else 'FAIL'}",
            f"run_all_status={'PASS' if run_status_pass else 'FAIL'}",
            (
                "run_all_markers="
                f"START:{run_counts[0]} PASS:{run_counts[1]} "
                f"SKIP:{run_counts[2]} FAIL:{run_counts[3]} "
                f"log_checks:{'PASS' if run_log_pass else 'FAIL'}"
            ),
            (
                f"run_all_done_markers={len(actual_markers)}/"
                f"{len(expected_markers)} "
                f"{'PASS' if markers_pass else 'FAIL'}"
            ),
            (
                "v1_isolated_empty_build="
                f"{'PASS' if v1_recovery_pass else 'FAIL'}"
            ),
            (
                "v1_combined_clean_and_replay_evidence="
                f"{'PASS' if v1_pass else 'FAIL'}"
            ),
            (
                "v1_second_delete_incident="
                f"{'DOCUMENTED' if incident_pass else 'FAIL'}"
            ),
            f"v6_status={'PASS' if v6_status_pass else 'FAIL'}",
            (
                "v6_markers="
                f"START:{v6_counts[0]} PASS:{v6_counts[1]} "
                f"SKIP:{v6_counts[2]} FAIL:{v6_counts[3]} "
                f"log_checks:{'PASS' if v6_log_pass else 'FAIL'}"
            ),
            (
                "v6_manifests="
                f"initial:{'PASS' if v6_initial_manifest_pass else 'FAIL'} "
                f"final:{'PASS' if v6_final_manifest_pass else 'FAIL'}"
            ),
            f"v6_metrics={'PASS' if v6_metrics_pass else 'FAIL'}",
            f"v6_witness_axioms={'PASS' if v6_axioms_pass else 'FAIL'}",
            f"v7_status={'PASS' if v7_status_pass else 'FAIL'}",
            f"v7_log={'PASS' if v7_log_pass else 'FAIL'}",
            f"v7_summary_51_of_51={'PASS' if v7_summary_pass else 'FAIL'}",
            f"v7_witness_axioms={'PASS' if v7_axioms_pass else 'FAIL'}",
            (
                "v7_manifests="
                f"initial:{'PASS' if v7_initial_manifest_pass else 'FAIL'} "
                f"final:{'PASS' if v7_final_manifest_pass else 'FAIL'}"
            ),
            f"v10_status={'PASS' if v10_status_pass else 'FAIL'}",
            (
                "v10_markers="
                f"START:{v10_counts[0]} PASS:{v10_counts[1]} "
                f"SKIP:{v10_counts[2]} FAIL:{v10_counts[3]} "
                f"log_checks:{'PASS' if v10_log_pass else 'FAIL'}"
            ),
            (
                "v10_manifests="
                f"initial:{'PASS' if v10_initial_manifest_pass else 'FAIL'} "
                f"final:{'PASS' if v10_final_manifest_pass else 'FAIL'}"
            ),
            f"aggregate_v10_child={'PASS' if v10_aggregate_pass else 'FAIL'}",
            f"v10_exact_summary={'PASS' if v10_summary_pass else 'FAIL'}",
            f"v10_clean_compile_logs={'PASS' if v10_compile_pass else 'FAIL'}",
            f"v10_curation_sets={'PASS' if v10_curation_pass else 'FAIL'}",
            f"v10_quality_review={'PASS' if quality_pass else 'FAIL'}",
            (
                "v10_quality_input_hashes="
                f"{'PASS' if v10_quality_inputs_pass else 'FAIL'}"
            ),
            f"consistency={'PASS' if consistency_pass else 'FAIL'}",
            (
                "certificate_validity=requires_absent_writer_lock_and_"
                "finalization_guard"
            ),
            f"problems={len(problems)}",
            *(f"PROBLEM {problem}" for problem in problems),
            f"result={'PASS' if not problems else 'FAIL'}",
        ]
        return "\n".join(lines) + "\n"

    def commit_output(payload: str) -> bool:
        try:
            atomic_write_bytes(FINAL_OUTPUT, payload.encode("utf-8"))
        except OSError as error:
            problems.append(f"cannot commit final lifecycle output: {error}")
            return False
        return True

    if not validate_lifecycle_guard(lifecycle_guard, problems):
        guard_pass = False
    ready_sentinel = (
        "FINAL VERIFICATION LIFECYCLE CHECK\n"
        "state=READY_TO_PUBLISH\n"
        f"checker_pid={os.getpid()}\n"
        "result=FAIL\n"
    )
    ready_committed = commit_output(ready_sentinel)
    if not ready_committed:
        commit_output(output_text())
    publication_guard = handoff_lifecycle_lock_to_guard(
        lifecycle_lock, lifecycle_guard, problems
    )
    if publication_guard is not None:
        _ACTIVE_LIFECYCLE_LOCK = None
        _ACTIVE_LIFECYCLE_GUARD = publication_guard
        payload = output_text()
        if not commit_output(payload):
            payload = output_text()
            commit_output(payload)
        publication_release_ok = release_lifecycle_guard(
            publication_guard, problems
        )
        if publication_release_ok:
            _ACTIVE_LIFECYCLE_GUARD = None
        else:
            guard_pass = False
            payload = output_text()
            replace_with_nonpass(payload.encode("utf-8"))
    else:
        guard_pass = False
        payload = output_text()
        commit_output(payload)
        # The canonical transcript is now non-PASS, so it is safe to make a
        # best-effort cleanup. Any cleanup failure deliberately leaves a gate.
        if validate_lifecycle_lock(lifecycle_lock, []):
            if release_lifecycle_lock(lifecycle_lock, []):
                _ACTIVE_LIFECYCLE_LOCK = None
        if validate_lifecycle_guard(lifecycle_guard, []):
            if release_lifecycle_guard(lifecycle_guard, []):
                _ACTIVE_LIFECYCLE_GUARD = None
    _LIFECYCLE_FINALIZED = (
        _ACTIVE_LIFECYCLE_LOCK is None
        and _ACTIVE_LIFECYCLE_GUARD is None
    )
    print(payload, end="")
    return 0 if not problems else 1


if __name__ == "__main__":
    raise SystemExit(main())
