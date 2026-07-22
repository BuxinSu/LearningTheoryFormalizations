#!/usr/bin/env python3
"""Read-only validators used by the staged ``run_all.sh`` orchestrator.

The expensive Lean/Lake commands are intentionally absent here.  Each
subcommand validates already-preserved evidence or fresh scanner output
written into a unique run-all attempt directory.  It never writes a project
file.  The superseded pre-removal V4 and V8 validators are retained below
only as historical implementation provenance and are deliberately
fail-closed and absent from the command-line interface; current evidence is
validated by the corresponding stages in ``run_all.sh``.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Sequence

from file_universe import ROOT, enumerate_universe
from run_v8_package_lint import (
    FAILED_ORPHAN_IMPORTS,
    validate_all_harnesses,
    validate_v2_orphan_evidence,
)
from v3_v4_reconcile import (
    DEFAULT_EDGES,
    DEFAULT_EXERCISES,
    DEFAULT_V3,
    DEFAULT_V4,
    _direct_textual_sorries,
    _read_edges,
    _reverse_closure,
)
from v8_lint_parser import parse_lint_log
from verify_readme_axioms import (
    ALLOWED,
    EXPECTED_ROWS,
    EXPECTED_UNIQUE_NAMES,
    PROJECT_PREFIXES,
    parse_axioms,
    proved_names,
    read_v4,
    table_rows,
    validate_preserved_artifacts,
)


VERIFY = ROOT / "HighDimensionalProbability" / "Verification"
LOGS = VERIFY / "logs"
V4_RAW_FILES = (
    LOGS / "axiom_audit.tsv",
    LOGS / "axiom_modules.txt",
    LOGS / "axiom_calibration.tsv",
    LOGS / "axiom_declaration_types.tsv",
    LOGS / "axiom_declaration_binders.tsv",
    LOGS / "axiom_direct_dependencies.tsv",
)
V4_DERIVED_FILES = (
    LOGS / "axiom_audit_summary.txt",
    LOGS / "axiom_module_coverage.txt",
    LOGS / "axiom_audit_exceedances.tsv",
    LOGS / "axiom_and_opaque_declarations.tsv",
)
FAILED_V4_MODULES = frozenset(FAILED_ORPHAN_IMPORTS)
EXPECTED_V4_DECLARATIONS = 15052
EXPECTED_V4_MODULES = 230
EXPECTED_V4_ENVIRONMENT_MODULES = 226
EXPECTED_V4_BINDERS = 81067
EXPECTED_V4_EDGES = 1450620
EXPECTED_V4_CALIBRATIONS = 2
EXPECTED_V4_EXCEEDANCES = 228
EXPECTED_V4_OPAQUE_ROWS = 1

V4_SCHEMAS = {
    "axiom_audit.tsv": (
        "module",
        "name",
        "kind",
        "is_private",
        "private_user_name",
        "is_internal",
        "axioms",
    ),
    "axiom_calibration.tsv": ("label", "name", "has_sorryAx", "axioms"),
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
    "axiom_audit_exceedances.tsv": (
        "module",
        "name",
        "kind",
        "classification",
        "unexpected_axioms",
        "all_axioms",
    ),
    "axiom_and_opaque_declarations.tsv": (
        "module",
        "name",
        "kind",
        "is_private",
        "is_internal",
    ),
}

MC_SELF_RECORD_FIELDS = (
    "claim_id",
    "document",
    "line",
    "category",
    "severity",
    "verdict",
    "claim",
    "claimed",
    "observed",
    "evidence",
    "recommended_action",
)
MC_SELF_RECORD_VERDICTS = frozenset(
    {
        "MATCH",
        "PENDING",
        "STALE",
        "OVERSTATED",
        "CONTRADICTED",
        "UNVERIFIABLE",
    }
)
MC_SELF_RECORD_SEVERITIES = frozenset(
    {"INFO", "MINOR", "MAJOR", "CRITICAL"}
)
EXPECTED_MC_SELF_RECORD_CLAIMS = 632

V5_LIBRARY_FORBIDDEN = frozenset(
    {
        "v5.axiom",
        "v5.opaque",
        "v5.native_decide",
        "v5.unsafe",
        "v5.implemented_by",
        "v5.extern",
        "v5.csimp",
        "v5.skip_kernel_tc",
        "v5.bootstrap_option",
        "v5.run_cmd",
        "v5.run_elab",
        "v5.eval",
        "v5.initialize",
        "v5.modifyEnv",
        "v5.addDecl",
        "v5.environment_add",
        "v5.partial_def",
        "v5.macro_rules",
        "v5.macro",
        "v5.elab_rules",
        "v5.elab",
        "v5.syntax",
        "v5.run_tac",
    }
)
SCAN_TSV_FIELDS = (
    "record",
    "profile",
    "pattern_id",
    "category",
    "in_code",
    "path",
    "line",
    "column",
    "match",
    "context",
)


def _physical_file(path: Path, *, nonempty: bool = True) -> Path:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"not a physical regular file: {path}")
    if nonempty and path.stat().st_size == 0:
        raise ValueError(f"evidence file is empty: {path}")
    return path


def _read(path: Path) -> str:
    return _physical_file(path).read_text(encoding="utf-8", errors="replace")


def _completed_log(path: Path, *, allowed_exits: set[int]) -> str:
    text = _read(path)
    exits = re.findall(r"(?m)^exit_code:\s*(-?\d+)\s*$", text)
    if len(exits) != 1:
        raise ValueError(f"{path}: expected one exit_code footer, found {exits}")
    observed = int(exits[0])
    if observed not in allowed_exits:
        raise ValueError(
            f"{path}: exit {observed} not in allowed set {sorted(allowed_exits)}"
        )
    if not re.search(r"(?m)^finished:\s*\S+", text):
        raise ValueError(f"{path}: missing finished timestamp")
    return text


def _tsv_rows(path: Path) -> list[dict[str, str]]:
    csv.field_size_limit(sys.maxsize)
    with _physical_file(path).open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if not reader.fieldnames:
            raise ValueError(f"{path}: missing TSV header")
        return list(reader)


def _project_tsv(
    path: Path,
    *,
    expected_fields: tuple[str, ...],
    keep_fields: tuple[str, ...],
) -> list[dict[str, str]]:
    """Validate a TSV exactly while retaining only structurally useful cells."""

    csv.field_size_limit(sys.maxsize)
    rows: list[dict[str, str]] = []
    with _physical_file(path).open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != expected_fields:
            raise ValueError(
                f"{path}: header {reader.fieldnames!r} != {list(expected_fields)!r}"
            )
        for line, row in enumerate(reader, start=2):
            if None in row or any(row[field] is None for field in expected_fields):
                raise ValueError(f"{path}:{line}: malformed TSV row")
            rows.append({field: row[field] for field in keep_fields})
    return rows


def _count_tsv(
    path: Path,
    *,
    expected_fields: tuple[str, ...],
) -> int:
    csv.field_size_limit(sys.maxsize)
    count = 0
    with _physical_file(path).open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != expected_fields:
            raise ValueError(
                f"{path}: header {reader.fieldnames!r} != {list(expected_fields)!r}"
            )
        for line, row in enumerate(reader, start=2):
            if None in row or any(row[field] is None for field in expected_fields):
                raise ValueError(f"{path}:{line}: malformed TSV row")
            count += 1
    return count


def _require_unique(
    rows: Sequence[dict[str, str]],
    *,
    key_fields: tuple[str, ...],
    label: str,
) -> None:
    keys = [tuple(row[field] for field in key_fields) for row in rows]
    if any(not all(key) for key in keys) or len(set(keys)) != len(keys):
        raise ValueError(f"{label} keys are empty or duplicated")


def check_v4_structure_self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="v4-structure-selftest-") as temporary:
        sample = Path(temporary) / "sample.tsv"
        sample.write_text("name\tvalue\nA\t1\n", encoding="utf-8")
        rows = _project_tsv(
            sample,
            expected_fields=("name", "value"),
            keep_fields=("name",),
        )
        _require_unique(rows, key_fields=("name",), label="planted")
        sample.write_text("name\tvalue\nA\t1\nA\t2\n", encoding="utf-8")
        duplicate_rows = _project_tsv(
            sample,
            expected_fields=("name", "value"),
            keep_fields=("name",),
        )
        try:
            _require_unique(
                duplicate_rows,
                key_fields=("name",),
                label="planted",
            )
        except ValueError:
            pass
        else:
            raise ValueError("V4 planted duplicate-key calibration was accepted")
        sample.write_text("wrong\tvalue\nA\t1\n", encoding="utf-8")
        try:
            _count_tsv(sample, expected_fields=("name", "value"))
        except ValueError:
            pass
        else:
            raise ValueError("V4 planted wrong-header calibration was accepted")
    print("V4_STRUCTURE_SELFTEST_OK duplicate_key_and_header_rejected")


def scratch_fingerprint() -> tuple[str, int, int, int]:
    """Hash the exact scratch path set and contents used by V5."""

    universe = enumerate_universe()
    tmp = list(universe["tmp_scratch"])
    audit = list(universe["audit_work_scratch"])
    relative_paths = sorted(str(item) for item in (*tmp, *audit))
    digest = hashlib.sha256()
    for relative in relative_paths:
        source = _physical_file(ROOT / relative)
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(hashlib.sha256(source.read_bytes()).digest())
        digest.update(b"\0")
    return digest.hexdigest(), len(relative_paths), len(tmp), len(audit)


def inventory_fingerprint() -> tuple[str, int]:
    """Hash the exact top-level V9 inventory path set and contents."""

    inventory = VERIFY / "inventory"
    if not inventory.is_dir():
        raise ValueError(f"inventory directory is missing: {inventory}")
    entries = sorted(inventory.iterdir(), key=lambda path: path.name)
    symlinks = [path for path in entries if path.is_symlink()]
    if symlinks:
        raise ValueError(f"inventory contains symlinks: {symlinks!r}")
    files = [path for path in entries if path.is_file()]
    digest = hashlib.sha256()
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
        digest.update(b"\0")
    return digest.hexdigest(), len(files)


def _scan_tsv_rows(path: Path) -> list[dict[str, str]]:
    with _physical_file(path).open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != SCAN_TSV_FIELDS:
            raise ValueError(
                f"{path}: scanner TSV header is {reader.fieldnames!r}, "
                f"expected {list(SCAN_TSV_FIELDS)!r}"
            )
        return list(reader)


def _scan_payload(
    json_path: Path,
    tsv_path: Path,
    *,
    profile: str,
    scope: str,
) -> dict:
    payload = json.loads(_read(json_path))
    summary = payload.get("summary")
    if not isinstance(summary, dict):
        raise ValueError(f"{json_path}: missing scanner summary")
    if summary.get("profile") != profile:
        raise ValueError(
            f"{json_path}: profile {summary.get('profile')!r} != {profile!r}"
        )
    if summary.get("scope") != scope:
        raise ValueError(
            f"{json_path}: scope {summary.get('scope')!r} != {scope!r}"
        )
    hits = payload.get("hits")
    diagnostics = payload.get("lex_diagnostics")
    if not isinstance(hits, list):
        raise ValueError(f"{json_path}: missing scanner hits")
    if not isinstance(diagnostics, list):
        raise ValueError(f"{json_path}: missing scanner lexical diagnostics")
    if diagnostics:
        raise ValueError(f"{json_path}: lexical diagnostics are nonempty")
    if summary.get("lex_diagnostic_count") != 0:
        raise ValueError(f"{profile}/{scope}: stale lexical diagnostic count")
    rows = _scan_tsv_rows(tsv_path)
    if len(rows) != len(hits):
        raise ValueError(
            f"{profile}/{scope}: JSON/TSV hit counts differ: "
            f"{len(hits)} != {len(rows)}"
        )
    if summary.get("raw_hit_count") != len(hits):
        raise ValueError(f"{profile}/{scope}: summary raw_hit_count is stale")
    for index, (hit, row) in enumerate(zip(hits, rows, strict=True), start=1):
        if not isinstance(hit, dict):
            raise ValueError(f"{json_path}: hit {index} is not an object")
        expected = {
            "record": "hit",
            "profile": str(hit.get("profile", "")),
            "pattern_id": str(hit.get("pattern_id", "")),
            "category": str(hit.get("category", "")),
            "in_code": str(bool(hit.get("in_code"))).lower(),
            "path": str(hit.get("path", "")),
            "line": str(hit.get("line", "")),
            "column": str(hit.get("column", "")),
            "match": str(hit.get("matched_text", "")),
            "context": str(hit.get("context", "")),
        }
        if row != expected:
            differing = [
                field
                for field in SCAN_TSV_FIELDS
                if row.get(field) != expected[field]
            ]
            raise ValueError(
                f"{profile}/{scope}: JSON/TSV row {index} differs in "
                f"{differing!r}"
            )
    return payload


def check_v3(json_path: Path, tsv_path: Path) -> None:
    payload = _scan_payload(
        json_path,
        tsv_path,
        profile="V3",
        scope="library",
    )
    by_pattern = payload["summary"].get("by_pattern", {})
    sorry = by_pattern.get("v3.sorry", {})
    if sorry.get("code") != 228:
        raise ValueError(f"V3 executable sorry count changed: {sorry!r}")
    appendix_sorries = [
        hit
        for hit in payload["hits"]
        if hit.get("pattern_id") == "v3.sorry"
        and hit.get("in_code") is True
        and str(hit.get("path", "")).startswith(
            "HighDimensionalProbability/Appendix"
        )
    ]
    if appendix_sorries:
        raise ValueError("V3 found executable Appendix sorry tokens")
    direct_summary = _read(LOGS / "v3_direct_sorry_summary.txt")
    required = (
        "status: PASS",
        "mapped_direct_sorry_declarations: 228",
        "unique_direct_sorry_declarations: 228",
        "exercise_leaf_files_with_sorry: 46",
        "appendix_code_sorries: 0",
        "mapping_errors: 0",
    )
    missing = [line for line in required if line not in direct_summary]
    if missing:
        raise ValueError(f"V3 direct-map summary lacks {missing!r}")
    direct_rows = _tsv_rows(LOGS / "v3_direct_sorry_declarations.tsv")
    if len(direct_rows) != 228:
        raise ValueError("V3 direct declaration table does not have 228 rows")
    if {row["classification"] for row in direct_rows} != {"EXERCISE-SORRY"}:
        raise ValueError("V3 direct table has unexpected classifications")
    print(
        "V3_STATIC_OK "
        f"hits={len(payload['hits'])} direct_sorries={len(direct_rows)}"
    )


def _section_values(text: str, heading: str) -> list[str]:
    marker = f"[{heading}]"
    if marker not in text:
        raise ValueError(f"missing section {marker}")
    tail = text.split(marker, 1)[1]
    body = tail.split("\n[", 1)[0]
    return [
        line.strip()
        for line in body.splitlines()
        if line.strip() and line.strip() != "(none)"
    ]


def check_v4() -> None:
    raise RuntimeError(
        "retired pre-removal V4 validator: use axiom_audit.py analyze and "
        "run_all.sh stage 04_v4_axiom_audit"
    )
    for path in (*V4_RAW_FILES, *V4_DERIVED_FILES):
        _physical_file(path)
    _completed_log(LOGS / "axiom_audit_build.log", allowed_exits={0})
    _completed_log(
        LOGS / "axiom_audit_full_surface_attempt.log",
        allowed_exits={1},
    )
    summary = _read(LOGS / "axiom_audit_summary.txt")
    summary_lines = frozenset(summary.splitlines())
    required = (
        "verdict: INCOMPLETE",
        f"declarations_audited: {EXPECTED_V4_DECLARATIONS}",
        f"declaration_type_rows: {EXPECTED_V4_DECLARATIONS}",
        f"declaration_binder_rows: {EXPECTED_V4_BINDERS}",
        "type_telescope_dump: PASS",
        f"direct_dependency_edges: {EXPECTED_V4_EDGES}",
        "direct_dependency_dump: PASS",
        f"expected_modules: {EXPECTED_V4_MODULES}",
        f"environment_modules: {EXPECTED_V4_ENVIRONMENT_MODULES}",
        "module_coverage: FAIL",
        "calibration: PASS",
        "v3_reconciliation: PASS",
        "nonstandard_non_sorry_axiom_declarations: 0",
        "project_axiom_or_opaque_declarations: 1",
        "project_axiom_declarations: 0",
        "project_opaque_declarations: 1",
        "internal_generated_opaque_declarations: 1",
        "unexpected_user_facing_opaque_declarations: 0",
        "4 expected modules missing from environment",
    )
    missing = [line for line in required if line not in summary_lines]
    if missing:
        raise ValueError(f"V4 summary lacks {missing!r}")

    audit_rows = _project_tsv(
        LOGS / "axiom_audit.tsv",
        expected_fields=V4_SCHEMAS["axiom_audit.tsv"],
        keep_fields=V4_SCHEMAS["axiom_audit.tsv"],
    )
    if len(audit_rows) != EXPECTED_V4_DECLARATIONS:
        raise ValueError(
            "V4 axiom ledger row count changed: "
            f"{len(audit_rows)} != {EXPECTED_V4_DECLARATIONS}"
        )
    _require_unique(
        audit_rows,
        key_fields=("name",),
        label="V4 axiom ledger",
    )
    audit_by_name = {row["name"]: row for row in audit_rows}
    for row in audit_rows:
        if row["is_private"] not in {"true", "false"} or row[
            "is_internal"
        ] not in {"true", "false"}:
            raise ValueError(f"V4 axiom row has invalid booleans: {row['name']}")

    type_rows = _project_tsv(
        LOGS / "axiom_declaration_types.tsv",
        expected_fields=V4_SCHEMAS["axiom_declaration_types.tsv"],
        keep_fields=(
            "module",
            "name",
            "kind",
            "is_private",
            "private_user_name",
            "is_internal",
            "binder_count",
        ),
    )
    if len(type_rows) != EXPECTED_V4_DECLARATIONS:
        raise ValueError(
            "V4 declaration-type row count changed: "
            f"{len(type_rows)} != {EXPECTED_V4_DECLARATIONS}"
        )
    _require_unique(
        type_rows,
        key_fields=("name",),
        label="V4 declaration-type ledger",
    )
    binder_counts: dict[str, int] = {}
    audit_shape_fields = (
        "module",
        "name",
        "kind",
        "is_private",
        "private_user_name",
        "is_internal",
    )
    for row in type_rows:
        audit = audit_by_name.get(row["name"])
        if audit is None or any(
            row[field] != audit[field] for field in audit_shape_fields
        ):
            raise ValueError(
                f"V4 declaration-type row disagrees with axiom ledger: {row['name']}"
            )
        try:
            binder_count = int(row["binder_count"])
        except ValueError as error:
            raise ValueError(
                f"V4 declaration has nonnumeric binder count: {row['name']}"
            ) from error
        if binder_count < 0:
            raise ValueError(f"V4 declaration has negative binders: {row['name']}")
        binder_counts[row["name"]] = binder_count
    if sum(binder_counts.values()) != EXPECTED_V4_BINDERS:
        raise ValueError(
            "V4 type-table binder total changed: "
            f"{sum(binder_counts.values())} != {EXPECTED_V4_BINDERS}"
        )

    binder_rows = _project_tsv(
        LOGS / "axiom_declaration_binders.tsv",
        expected_fields=V4_SCHEMAS["axiom_declaration_binders.tsv"],
        keep_fields=(
            "module",
            "name",
            "private_user_name",
            "kind",
            "binder_index",
            "binder_name",
            "binder_info",
        ),
    )
    if len(binder_rows) != EXPECTED_V4_BINDERS:
        raise ValueError(
            f"V4 binder row count changed: {len(binder_rows)} != "
            f"{EXPECTED_V4_BINDERS}"
        )
    indices_by_name: dict[str, set[int]] = {}
    binder_keys: set[tuple[str, int]] = set()
    for row in binder_rows:
        audit = audit_by_name.get(row["name"])
        if audit is None or any(
            row[field] != audit[field]
            for field in ("module", "name", "private_user_name", "kind")
        ):
            raise ValueError(
                f"V4 binder row disagrees with axiom ledger: {row['name']}"
            )
        try:
            index = int(row["binder_index"])
        except ValueError as error:
            raise ValueError(
                f"V4 binder index is nonnumeric: {row['name']}"
            ) from error
        key = (row["name"], index)
        if key in binder_keys:
            raise ValueError(f"V4 duplicate binder key: {key!r}")
        binder_keys.add(key)
        indices_by_name.setdefault(row["name"], set()).add(index)
        if not row["binder_name"] or not row["binder_info"]:
            raise ValueError(f"V4 binder metadata is empty: {key!r}")
    for name, expected_count in binder_counts.items():
        observed = indices_by_name.get(name, set())
        if observed != set(range(expected_count)):
            raise ValueError(
                f"V4 binder indices are not 0..{expected_count - 1}: {name}"
            )

    calibration_rows = _project_tsv(
        LOGS / "axiom_calibration.tsv",
        expected_fields=V4_SCHEMAS["axiom_calibration.tsv"],
        keep_fields=V4_SCHEMAS["axiom_calibration.tsv"],
    )
    expected_calibrations = {
        "known_exercise_sorry",
        "planted_private_sorry",
    }
    if (
        len(calibration_rows) != EXPECTED_V4_CALIBRATIONS
        or {row["label"] for row in calibration_rows} != expected_calibrations
        or any(
            row["has_sorryAx"] != "true"
            or "sorryAx" not in set(filter(None, row["axioms"].split(";")))
            for row in calibration_rows
        )
    ):
        raise ValueError("V4 public/private sorryAx calibration rows are invalid")

    coverage = _read(LOGS / "axiom_module_coverage.txt")
    coverage_lines = frozenset(coverage.splitlines())
    coverage_required = (
        f"expected_modules: {EXPECTED_V4_MODULES}",
        f"environment_modules: {EXPECTED_V4_ENVIRONMENT_MODULES}",
        f"missing_modules: {len(FAILED_V4_MODULES)}",
        "extra_modules: 0",
    )
    coverage_missing = [
        line for line in coverage_required if line not in coverage_lines
    ]
    if coverage_missing:
        raise ValueError(
            f"V4 module-coverage summary lacks {coverage_missing!r}"
        )
    missing_modules = frozenset(_section_values(coverage, "missing_modules"))
    if missing_modules != FAILED_V4_MODULES:
        raise ValueError(
            "V4 missing-module set differs from the four failed V2 orphans: "
            f"{sorted(missing_modules)!r}"
        )
    if _section_values(coverage, "extra_modules"):
        raise ValueError("V4 environment contains unexpected project modules")
    environment_modules = [
        line.strip()
        for line in _read(LOGS / "axiom_modules.txt").splitlines()
        if line.strip()
    ]
    if (
        len(environment_modules) != EXPECTED_V4_ENVIRONMENT_MODULES
        or len(set(environment_modules)) != EXPECTED_V4_ENVIRONMENT_MODULES
    ):
        raise ValueError(
            "V4 environment-module ledger is not exactly "
            f"{EXPECTED_V4_ENVIRONMENT_MODULES} unique rows"
        )
    opaque_rows = _project_tsv(
        LOGS / "axiom_and_opaque_declarations.tsv",
        expected_fields=V4_SCHEMAS["axiom_and_opaque_declarations.tsv"],
        keep_fields=V4_SCHEMAS["axiom_and_opaque_declarations.tsv"],
    )
    if len(opaque_rows) != EXPECTED_V4_OPAQUE_ROWS:
        raise ValueError(
            "V4 expected exactly one inventoried irreducible_def wrapper, got "
            f"{len(opaque_rows)}"
        )
    opaque = opaque_rows[0]
    opaque_audit = audit_by_name.get(opaque["name"])
    if (
        opaque_audit is None
        or any(
            opaque[field] != opaque_audit[field]
            for field in ("module", "name", "kind", "is_private", "is_internal")
        )
        or opaque["kind"] != "opaque"
        or opaque["is_internal"] != "true"
        or "MajorizingMeasureRanked" not in opaque["module"]
        or "wrapped._@" not in opaque["name"]
    ):
        raise ValueError(
            "V4 opaque inventory differs from the internal "
            "greedyOwnerIndex irreducible_def wrapper"
        )

    mapped, mapping_errors = _direct_textual_sorries(
        DEFAULT_V3, DEFAULT_EXERCISES
    )
    if mapping_errors:
        raise ValueError(f"V3 textual mapping errors: {mapping_errors[:5]!r}")
    direct = {declaration.endpoint for declaration, _ in mapped}
    v4_sorry = {
        row["name"]
        for row in audit_rows
        if "sorryAx" in set(filter(None, row["axioms"].split(";")))
    }
    exceedance_rows = _project_tsv(
        LOGS / "axiom_audit_exceedances.tsv",
        expected_fields=V4_SCHEMAS["axiom_audit_exceedances.tsv"],
        keep_fields=V4_SCHEMAS["axiom_audit_exceedances.tsv"],
    )
    if (
        len(exceedance_rows) != EXPECTED_V4_EXCEEDANCES
        or len({row["name"] for row in exceedance_rows})
        != EXPECTED_V4_EXCEEDANCES
        or {row["name"] for row in exceedance_rows} != v4_sorry
        or any(
            row["classification"] != "V3_RECONCILED_SORRY"
            or row["unexpected_axioms"] != "sorryAx"
            or "sorryAx"
            not in set(filter(None, row["all_axioms"].split(";")))
            for row in exceedance_rows
        )
    ):
        raise ValueError("V4 exceedance ledger does not exactly equal sorryAx rows")
    for row in exceedance_rows:
        audit = audit_by_name[row["name"]]
        if any(row[field] != audit[field] for field in ("module", "name", "kind")):
            raise ValueError(
                f"V4 exceedance row disagrees with axiom ledger: {row['name']}"
            )

    edge_rows = _count_tsv(
        LOGS / "axiom_direct_dependencies.tsv",
        expected_fields=V4_SCHEMAS["axiom_direct_dependencies.tsv"],
    )
    if edge_rows != EXPECTED_V4_EDGES:
        raise ValueError(
            f"V4 dependency-edge count changed: {edge_rows} != {EXPECTED_V4_EDGES}"
        )
    forward, _origins = _read_edges(DEFAULT_EDGES)
    unique_edges = sum(len(origins) for origins in _origins.values())
    if unique_edges != EXPECTED_V4_EDGES:
        raise ValueError(
            "V4 dependency ledger contains duplicate source/origin/target rows: "
            f"unique={unique_edges}, rows={EXPECTED_V4_EDGES}"
        )
    unknown_sources = set(forward) - set(audit_by_name)
    if unknown_sources:
        raise ValueError(
            f"V4 dependency ledger has unknown project sources: "
            f"{sorted(unknown_sources)[:5]!r}"
        )
    closure, _next_edge, _distance = _reverse_closure(direct, forward)
    project_closure = closure & set(audit_by_name)
    if len(direct) != 228:
        raise ValueError(f"V3 direct sorry set has size {len(direct)}, not 228")
    if v4_sorry != project_closure:
        raise ValueError(
            "V3/V4 sorry closure mismatch: "
            f"V4-only={len(v4_sorry - project_closure)}, "
            f"closure-only={len(project_closure - v4_sorry)}"
        )
    print(
        "V4_STATIC_OK "
        f"audited_rows={len(audit_rows)} sorryAx={len(v4_sorry)} "
        f"excluded_failed_modules={len(missing_modules)}"
    )


def check_v5(
    library_json: Path,
    library_tsv: Path,
    scratch_json: Path,
    scratch_tsv: Path,
    auto_probe_log: Path,
) -> None:
    library = _scan_payload(
        library_json,
        library_tsv,
        profile="V5",
        scope="library",
    )
    scratch = _scan_payload(
        scratch_json,
        scratch_tsv,
        profile="V5",
        scope="scratch",
    )
    code_by_pattern = {
        pattern_id: int(counts["code"])
        for pattern_id, counts in library["summary"]["by_pattern"].items()
    }
    forbidden = {
        pattern_id: code_by_pattern.get(pattern_id, 0)
        for pattern_id in V5_LIBRARY_FORBIDDEN
        if code_by_pattern.get(pattern_id, 0)
    }
    if forbidden:
        raise ValueError(f"V5 executable library bypass hits: {forbidden!r}")
    probe = _completed_log(auto_probe_log, allowed_exits={0})
    if "v5AutoImplicitDefaultProbe" not in probe or "{α : Sort" not in probe:
        raise ValueError(
            "V5 autoImplicit probe log lacks the elaborated implicit Sort binder"
        )
    print(
        "V5_STATIC_OK "
        f"library_hits={len(library['hits'])} "
        f"scratch_hits={len(scratch['hits'])} forbidden_code_hits=0"
    )


def check_v8(
    maximal_log: Path,
    full_surface_log: Path,
    v7_report: Path,
) -> None:
    raise RuntimeError(
        "retired maximal-buildable/orphan-failure V8 validator: use "
        "run_v8_package_lint.py and run_all.sh stage 08_v8_lint"
    )
    harness_errors = validate_all_harnesses()
    harness_errors.extend(validate_v2_orphan_evidence())
    if harness_errors:
        raise ValueError(f"V8 harness/V2 contract errors: {harness_errors!r}")
    v7 = _read(v7_report)
    if "PENDING" in v7 or "TBD" in v7:
        raise ValueError("V8 sequencing gate: V7 report is not final")
    if not re.search(r"(?m)^\*\*Verdict:\s*[A-Z-]+\*\*\s*$", v7):
        raise ValueError("V8 sequencing gate: V7 has no final verdict")

    maximal_text = _completed_log(maximal_log, allowed_exits={0, 1})
    maximal = parse_lint_log(
        maximal_text,
        log_path=maximal_log.relative_to(ROOT).as_posix(),
    )
    if (
        not maximal.gate_passed
        or maximal.surface_profile != "maximal-buildable"
        or maximal.overall_status != "INCOMPLETE"
    ):
        raise ValueError(
            "V8 maximal-buildable lint evidence is not structurally valid "
            f"INCOMPLETE evidence: {maximal.diagnostics!r}"
        )
    full_text = _completed_log(full_surface_log, allowed_exits={1})
    if (
        "MatrixConcentration.Appendix_RosenthalPinelis" not in full_text
        or "error:" not in full_text
    ):
        raise ValueError(
            "V8 full-surface gate does not expose the V2 orphan failure"
        )
    print(
        "V8_STATIC_OK "
        f"maximal_declarations="
        f"{sum(package.declarations_examined for package in maximal.packages)} "
        f"lint_hits={maximal.total_hits} full_surface_gate=EXPECTED_FAIL"
    )


def check_v9_mc_self_record(
    result_tsv: Path,
    summary_path: Path,
    run_log_path: Path,
) -> int:
    with _physical_file(result_tsv).open(
        encoding="utf-8", newline=""
    ) as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != MC_SELF_RECORD_FIELDS:
            raise ValueError(
                "V9 MatrixConcentration self-record TSV header changed: "
                f"{reader.fieldnames!r}"
            )
        rows = list(reader)
    if len(rows) != EXPECTED_MC_SELF_RECORD_CLAIMS:
        raise ValueError(
            "V9 MatrixConcentration self-record claim count changed: "
            f"{len(rows)} != {EXPECTED_MC_SELF_RECORD_CLAIMS}"
        )
    claim_ids = [row["claim_id"] for row in rows]
    if len(set(claim_ids)) != len(claim_ids) or any(not item for item in claim_ids):
        raise ValueError(
            "V9 MatrixConcentration self-record claim IDs are empty or duplicated"
        )
    invalid_verdicts = sorted(
        {
            row["verdict"]
            for row in rows
            if row["verdict"] not in MC_SELF_RECORD_VERDICTS
        }
    )
    invalid_severities = sorted(
        {
            row["severity"]
            for row in rows
            if row["severity"] not in MC_SELF_RECORD_SEVERITIES
        }
    )
    if invalid_verdicts or invalid_severities:
        raise ValueError(
            "V9 MatrixConcentration self-record has invalid enums: "
            f"verdicts={invalid_verdicts!r}, severities={invalid_severities!r}"
        )

    tsv_sha = hashlib.sha256(_physical_file(result_tsv).read_bytes()).hexdigest()
    verdicts = Counter(row["verdict"] for row in rows)
    verdict_summary = ", ".join(
        f"`{verdict}={verdicts[verdict]}`" for verdict in sorted(verdicts)
    )
    material_count = sum(
        row["severity"] in {"MAJOR", "CRITICAL"}
        and row["verdict"] in {"STALE", "OVERSTATED", "CONTRADICTED"}
        for row in rows
    )

    summary = _read(summary_path)
    summary_required = (
        "# V9 MatrixConcentration self-record audit",
        f"- TSV SHA-256: `{tsv_sha}`",
        "- V4 raw state: `COMPLETE` (15052 readable rows; 1508 MC-origin rows)",
        f"- Claims audited: **{len(rows)}**",
        f"- Verdicts: {verdict_summary}",
        "- Major/critical stale, overstated, or contradicted claims: "
        f"**{material_count}**",
    )
    summary_lines = frozenset(summary.splitlines())
    missing_summary = [
        line for line in summary_required if line not in summary_lines
    ]
    if missing_summary:
        raise ValueError(
            "V9 MatrixConcentration self-record summary lacks "
            f"{missing_summary!r}"
        )

    run_log = _read(run_log_path)
    log_required = (
        "V9 MATRIXCONCENTRATION SELF-RECORD AUDIT",
        "method: deterministic static scan; no Lean/Lake/Git/network",
        "negative_calibration: PASS",
        f"claims: {len(rows)}",
        "v4_complete: true",
        "v4_readable_rows: 15052",
        "v4_mc_origin_rows: 1508",
        f"tsv_sha256: {tsv_sha}",
        "ledger: HighDimensionalProbability/Verification/review/"
        "v9_matrix_concentration_self_record.tsv",
        "summary: HighDimensionalProbability/Verification/review/"
        "v9_matrix_concentration_self_record_summary.md",
    )
    log_lines = frozenset(run_log.splitlines())
    missing_log = [line for line in log_required if line not in log_lines]
    if missing_log:
        raise ValueError(
            "V9 MatrixConcentration self-record log lacks "
            f"{missing_log!r}"
        )
    return len(rows)


def check_v9(
    raw_log: Path,
    result_tsv: Path,
    summary_path: Path,
    mc_result_tsv: Path,
    mc_summary_path: Path,
    mc_run_log_path: Path,
) -> None:
    validated_rows, validated_names = validate_preserved_artifacts(
        raw_log=raw_log,
        results_path=result_tsv,
        summary_path=summary_path,
        v4_path=DEFAULT_V4,
    )
    if (
        validated_rows != EXPECTED_ROWS
        or validated_names != EXPECTED_UNIQUE_NAMES
    ):
        raise ValueError(
            "V9 exact artifact validator returned unexpected dimensions: "
            f"rows={validated_rows}, names={validated_names}"
        )
    raw = _completed_log(raw_log, allowed_exits={0})
    rows = table_rows()
    names = proved_names(rows)
    found, missing, duplicates = parse_axioms(raw, names)
    if len(rows) != EXPECTED_ROWS or len(names) != EXPECTED_UNIQUE_NAMES:
        raise ValueError(
            f"V9 README census changed: rows={len(rows)}, names={len(names)}"
        )
    if missing or duplicates:
        raise ValueError(
            f"V9 axiom log parse mismatch: missing={len(missing)}, "
            f"duplicates={len(duplicates)}"
        )
    unexpected = {
        name: axioms - ALLOWED
        for name, axioms in found.items()
        if axioms - ALLOWED
    }
    if unexpected:
        raise ValueError(
            f"V9 README endpoints use nonstandard axioms: {len(unexpected)}"
        )
    v4 = read_v4(DEFAULT_V4)
    project = {name for name in names if name.startswith(PROJECT_PREFIXES)}
    if project - set(v4):
        raise ValueError(
            f"V9 project endpoints absent from V4: {len(project - set(v4))}"
        )
    mismatches = {
        name
        for name in project
        if name in found and found[name] != v4[name]
    }
    if mismatches:
        raise ValueError(
            f"V9 README/V4 axiom mismatches: {len(mismatches)}"
        )
    mc_claims = check_v9_mc_self_record(
        mc_result_tsv,
        mc_summary_path,
        mc_run_log_path,
    )
    print(
        "V9_STATIC_OK "
        f"correspondence_rows={len(rows)} endpoints={len(names)} "
        f"project_endpoints={len(project)} "
        f"matrix_concentration_self_record_claims={mc_claims}"
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="stage", required=True)

    subparsers.add_parser(
        "scratch-fingerprint",
        help="print the path-and-content SHA-256 of the exact V5 scratch universe",
    )
    subparsers.add_parser(
        "inventory-fingerprint",
        help="print the path-and-content SHA-256 of the exact V9 inventory universe",
    )

    v3 = subparsers.add_parser("v3")
    v3.add_argument("--json", type=Path, required=True)
    v3.add_argument("--tsv", type=Path, required=True)

    v5 = subparsers.add_parser("v5")
    v5.add_argument("--library-json", type=Path, required=True)
    v5.add_argument("--library-tsv", type=Path, required=True)
    v5.add_argument("--scratch-json", type=Path, required=True)
    v5.add_argument("--scratch-tsv", type=Path, required=True)
    v5.add_argument("--auto-probe-log", type=Path, required=True)

    v9 = subparsers.add_parser("v9")
    v9.add_argument("--raw-log", type=Path, required=True)
    v9.add_argument("--result-tsv", type=Path, required=True)
    v9.add_argument("--summary", type=Path, required=True)
    v9.add_argument("--mc-self-record-tsv", type=Path, required=True)
    v9.add_argument("--mc-self-record-summary", type=Path, required=True)
    v9.add_argument("--mc-self-record-log", type=Path, required=True)

    v9_mc = subparsers.add_parser(
        "v9-mc-self-record",
        help="validate the preserved MatrixConcentration self-record trio",
    )
    v9_mc.add_argument("--result-tsv", type=Path, required=True)
    v9_mc.add_argument("--summary", type=Path, required=True)
    v9_mc.add_argument("--run-log", type=Path, required=True)

    args = parser.parse_args(argv)
    try:
        if args.stage == "scratch-fingerprint":
            digest, _total, _tmp, _audit = scratch_fingerprint()
            print(digest)
        elif args.stage == "inventory-fingerprint":
            digest, _total = inventory_fingerprint()
            print(digest)
        elif args.stage == "v3":
            check_v3(args.json.resolve(), args.tsv.resolve())
        elif args.stage == "v5":
            check_v5(
                args.library_json.resolve(),
                args.library_tsv.resolve(),
                args.scratch_json.resolve(),
                args.scratch_tsv.resolve(),
                args.auto_probe_log.resolve(),
            )
        elif args.stage == "v9":
            check_v9(
                args.raw_log.resolve(),
                args.result_tsv.resolve(),
                args.summary.resolve(),
                args.mc_self_record_tsv.resolve(),
                args.mc_self_record_summary.resolve(),
                args.mc_self_record_log.resolve(),
            )
        elif args.stage == "v9-mc-self-record":
            claims = check_v9_mc_self_record(
                args.result_tsv.resolve(),
                args.summary.resolve(),
                args.run_log.resolve(),
            )
            print(f"V9_MC_SELF_RECORD_STATIC_OK claims={claims}")
        else:
            raise AssertionError(args.stage)
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"{args.stage.upper()}_STATIC_FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
