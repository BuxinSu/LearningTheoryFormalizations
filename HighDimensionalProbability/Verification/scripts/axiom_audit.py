#!/usr/bin/env python3
"""Run and validate the exhaustive V4 ``Lean.collectAxioms`` audit.

The Lean harness lives outside both libraries, in
``.audit_work/verification/AxiomAuditFinalRecertification.lean``. It imports the
full current surface classified by V2 and writes fresh TSV evidence. This
script proves the module coverage invariant against the physical file-walk
universe, classifies every constant and axiom set, and optionally reconciles
every ``sorryAx`` result with V3's declaration-level allowlist.

The final ``run`` action deliberately requires completed V2 evidence.  Merely
invoking ``self-test`` or ``analyze`` never compiles the full harness.
"""

from __future__ import annotations

import argparse
import collections
import csv
import datetime as dt
import fcntl
import io
import os
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from file_universe import enumerate_universe


ROOT = Path(__file__).resolve().parents[3]
# Raw Lean expression renderings can be much larger than Python's 128 KiB
# CSV default.  The V4 files are trusted local evidence and the validators
# stream them, so accepting the platform maximum is both necessary and
# bounded by the on-disk input.
csv.field_size_limit(sys.maxsize)
DEFAULT_LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
# Long-running V4 writers can be redirected to a local, non-synchronised
# filesystem and copied back only after every handle is closed.  This avoids
# cloud-sync rollback of partially written TSVs while preserving the default
# checked-in evidence paths for normal runs and analysis.
LOGS = Path(os.environ.get("HDP_V4_OUTPUT_DIR", DEFAULT_LOGS)).resolve()
HARNESS = (
    ROOT
    / ".audit_work"
    / "verification"
    / "AxiomAuditFinalRecertification.lean"
)
RAW_AUDIT = LOGS / "recert_axiom_audit.tsv"
RAW_MODULES = LOGS / "recert_axiom_modules.txt"
RAW_CALIBRATION = LOGS / "recert_axiom_calibration.tsv"
RAW_TYPES = LOGS / "recert_axiom_declaration_types.tsv"
RAW_BINDERS = LOGS / "recert_axiom_declaration_binders.tsv"
RAW_DIRECT_DEPENDENCIES = LOGS / "recert_axiom_direct_dependencies.tsv"
BUILD_LOG = LOGS / "recert_axiom_audit_build.log"
SUMMARY = LOGS / "recert_axiom_summary.txt"
COVERAGE = LOGS / "recert_axiom_module_coverage.txt"
EXCEEDANCES = LOGS / "recert_axiom_exceedances.tsv"
OPAQUE_AXIOM_INVENTORY = LOGS / "recert_axiom_and_opaque_declarations.tsv"
# One exhaustive collector at a time, even when its streaming outputs are
# redirected away from a synchronised workspace.
RUN_LOCK = Path(
    os.environ.get(
        "HDP_V4_LOCK_FILE",
        "/private/tmp/hdp_axiom_audit_final_recertification.lock",
    )
)


def display_path(path: Path) -> Path:
    """Prefer project-relative diagnostics, while supporting isolated outputs."""
    return path.relative_to(ROOT) if path.is_relative_to(ROOT) else path


def write_text_if_changed(path: Path, text: str) -> None:
    """Preserve evidence mtimes when deterministic analysis is byte-identical."""
    encoded = text.encode("utf-8")
    if path.is_file() and path.read_bytes() == encoded:
        return
    path.write_bytes(encoded)


def write_tsv_if_changed(path: Path, rows: list[list[str]]) -> None:
    """Render a small derived TSV in memory and replace it only on real drift."""
    buffer = io.StringIO(newline="")
    writer = csv.writer(buffer, delimiter="\t", lineterminator="\n")
    writer.writerows(rows)
    write_text_if_changed(path, buffer.getvalue())


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SORRY_AXIOM = "sorryAx"
REQUIRED_MC_MODULES = frozenset(
    {
        "MatrixConcentration.Prelude",
        "MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices",
        "MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod",
        "MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries",
        "MatrixConcentration.Chapter5_SumOfPSDMatrices",
        "MatrixConcentration.Chapter8_ProofOfLiebsTheorem",
        "MatrixConcentration.Appendix_GoldenThompson",
        "MatrixConcentration.Appendix_GaussianConcentration",
        "MatrixConcentration.Appendix_SymmetricLowerBound",
        "MatrixConcentration.Appendix_MatrixRosenthal",
    }
)
REQUIRED_AUDIT_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "axioms",
)
REQUIRED_TYPE_COLUMNS = (
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
)
REQUIRED_BINDER_COLUMNS = (
    "module",
    "name",
    "private_user_name",
    "kind",
    "binder_index",
    "binder_name",
    "binder_info",
    "binder_type_raw",
)
REQUIRED_DIRECT_DEPENDENCY_COLUMNS = (
    "source_module",
    "source",
    "source_kind",
    "origin",
    "target_module",
    "target",
)


@dataclass(frozen=True)
class AuditRow:
    module: str
    name: str
    kind: str
    is_private: bool
    private_user_name: str
    is_internal: bool
    axioms: frozenset[str]


def _parse_bool(text: str, *, field: str) -> bool:
    if text == "true":
        return True
    if text == "false":
        return False
    raise ValueError(f"{field} must be true or false, got {text!r}")


def source_path_to_module(relative_path: str) -> str:
    """Map one physical library path to its Lean module name."""
    path = Path(relative_path)
    if path.suffix != ".lean":
        raise ValueError(f"not a Lean source path: {relative_path}")
    without_suffix = path.with_suffix("")
    parts = without_suffix.parts
    if parts[0] == "HighDimensionalProbability":
        return ".".join(parts)
    if parts[0] == "MatrixConcentration":
        return ".".join(parts)
    if len(parts) == 1 and parts[0] == "HighDimensionalProbability":
        return parts[0]
    raise ValueError(f"path is outside the two library surfaces: {relative_path}")


def expected_modules() -> set[str]:
    universe = enumerate_universe()
    library_paths = universe["file_walk_universe"]
    root_paths = universe["root_modules_separate"]
    assert isinstance(library_paths, list)
    assert isinstance(root_paths, list)
    return {
        source_path_to_module(str(path))
        for path in [*library_paths, *root_paths]
    }


def read_audit_rows(path: Path = RAW_AUDIT) -> list[AuditRow]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != REQUIRED_AUDIT_COLUMNS:
            raise ValueError(
                f"{path}: unexpected columns {reader.fieldnames!r}; "
                f"expected {REQUIRED_AUDIT_COLUMNS!r}"
            )
        rows: list[AuditRow] = []
        for raw in reader:
            axioms = frozenset(filter(None, raw["axioms"].split(";")))
            rows.append(
                AuditRow(
                    module=raw["module"],
                    name=raw["name"],
                    kind=raw["kind"],
                    is_private=_parse_bool(raw["is_private"], field="is_private"),
                    private_user_name=raw["private_user_name"],
                    is_internal=_parse_bool(raw["is_internal"], field="is_internal"),
                    axioms=axioms,
                )
            )
    if not rows:
        raise ValueError(f"{path}: audit contains no declarations")
    names = [row.name for row in rows]
    duplicates = sorted(name for name, count in collections.Counter(names).items() if count > 1)
    if duplicates:
        raise ValueError(f"{path}: duplicate declarations: {duplicates[:20]}")
    return rows


def read_modules(path: Path = RAW_MODULES) -> set[str]:
    modules = {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    if not modules:
        raise ValueError(f"{path}: module list is empty")
    return modules


def validate_calibration(path: Path = RAW_CALIBRATION) -> list[str]:
    with path.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    by_label = {row.get("label", ""): row for row in rows}
    errors: list[str] = []
    for label in ("known_exercise_sorry", "planted_private_sorry"):
        row = by_label.get(label)
        if row is None:
            errors.append(f"missing calibration row {label}")
            continue
        axioms = set(filter(None, row.get("axioms", "").split(";")))
        if row.get("has_sorryAx") != "true" or SORRY_AXIOM not in axioms:
            errors.append(f"{label} did not report sorryAx")
    private_row = by_label.get("planted_private_sorry")
    if private_row is not None and "_private" not in private_row.get("name", ""):
        errors.append(
            "planted_private_sorry did not expose a mangled _private declaration name"
        )
    return errors


def validate_type_and_telescope_dumps(
    audit_rows: list[AuditRow],
    type_path: Path = RAW_TYPES,
    binder_path: Path = RAW_BINDERS,
) -> tuple[int, int, list[str]]:
    errors: list[str] = []
    audit_by_name = {row.name: row for row in audit_rows}
    # The raw expression columns can exceed a gigabyte in aggregate.  Retain
    # only the compact metadata needed by this validator so analysis remains
    # streaming and does not duplicate the evidence file in Python memory.
    type_by_name: dict[str, tuple[str, str, int]] = {}
    type_row_count = 0
    with type_path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != REQUIRED_TYPE_COLUMNS:
            raise ValueError(
                f"{type_path}: unexpected columns {reader.fieldnames!r}; "
                f"expected {REQUIRED_TYPE_COLUMNS!r}"
            )
        for row in reader:
            type_row_count += 1
            name = row["name"]
            if name in type_by_name:
                errors.append(f"duplicate type row for {name}")
            if not row["type_raw"] or not row["conclusion_raw"]:
                errors.append(f"empty raw type or conclusion for {name}")
            try:
                binder_count = int(row["binder_count"])
            except ValueError:
                errors.append(
                    f"invalid binder_count for {name}: {row['binder_count']!r}"
                )
                binder_count = -1
            if binder_count < 0:
                errors.append(f"negative binder_count for {name}")
            type_by_name[name] = (
                row["module"],
                row["kind"],
                binder_count,
            )

    audit_names = set(audit_by_name)
    type_names = set(type_by_name)
    if audit_names != type_names:
        errors.append(
            "type dump name set differs from axiom audit: "
            f"{len(audit_names - type_names)} missing, "
            f"{len(type_names - audit_names)} extra"
        )

    binder_indices: dict[str, list[int]] = collections.defaultdict(list)
    valid_binder_infos = {
        "explicit",
        "implicit",
        "strictImplicit",
        "instImplicit",
    }
    binder_row_count = 0
    with binder_path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != REQUIRED_BINDER_COLUMNS:
            raise ValueError(
                f"{binder_path}: unexpected columns {reader.fieldnames!r}; "
                f"expected {REQUIRED_BINDER_COLUMNS!r}"
            )
        for row in reader:
            binder_row_count += 1
            name = row["name"]
            if name not in type_by_name:
                errors.append(f"binder row names unknown declaration {name}")
                continue
            try:
                index = int(row["binder_index"])
            except ValueError:
                errors.append(
                    f"invalid binder_index for {name}: {row['binder_index']!r}"
                )
                continue
            binder_indices[name].append(index)
            if row["binder_info"] not in valid_binder_infos:
                errors.append(
                    f"invalid BinderInfo for {name}[{index}]: "
                    f"{row['binder_info']!r}"
                )
            if not row["binder_type_raw"]:
                errors.append(f"empty binder_type_raw for {name}[{index}]")

    for name, (module, kind, expected_count) in type_by_name.items():
        if expected_count < 0:
            continue
        actual_indices = sorted(binder_indices.get(name, []))
        if actual_indices != list(range(expected_count)):
            errors.append(
                f"telescope index/count mismatch for {name}: "
                f"expected 0..{expected_count - 1}, got {actual_indices[:20]}"
            )
        audit_row = audit_by_name.get(name)
        if audit_row is not None:
            if module != audit_row.module or kind != audit_row.kind:
                errors.append(f"type metadata differs from audit metadata for {name}")

    return type_row_count, binder_row_count, errors


def validate_direct_dependency_dump(
    audit_rows: list[AuditRow],
    path: Path = RAW_DIRECT_DEPENDENCIES,
) -> tuple[int, list[str]]:
    errors: list[str] = []
    audit_by_name = {row.name: row for row in audit_rows}
    seen: set[tuple[str, str, str]] = set()
    row_count = 0
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != REQUIRED_DIRECT_DEPENDENCY_COLUMNS:
            raise ValueError(
                f"{path}: unexpected columns {reader.fieldnames!r}; "
                f"expected {REQUIRED_DIRECT_DEPENDENCY_COLUMNS!r}"
            )
        for row in reader:
            row_count += 1
            source = row["source"]
            target = row["target"]
            origin = row["origin"]
            if source not in audit_by_name:
                errors.append(
                    f"dependency edge has unknown audited source {source}"
                )
                continue
            audit_row = audit_by_name[source]
            if (
                row["source_module"] != audit_row.module
                or row["source_kind"] != audit_row.kind
            ):
                errors.append(
                    f"dependency metadata differs from audit row for {source}"
                )
            if origin not in {"type", "value"}:
                errors.append(
                    f"invalid dependency origin for {source}: {origin!r}"
                )
            if not target:
                errors.append(f"dependency edge from {source} has empty target")
            key = (source, origin, target)
            if key in seen:
                errors.append(
                    f"duplicate direct dependency edge: {source} {origin} {target}"
                )
            seen.add(key)
    if row_count == 0:
        errors.append("direct dependency dump is empty")
    return row_count, errors


def read_v3_allowlist(path: Path) -> set[str]:
    """Read one declaration name per line, or the first column of a TSV."""
    names: set[str] = set()
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        first = stripped.split("\t", 1)[0].strip()
        if index == 0 and first.lower() in {"name", "declaration", "declaration_name"}:
            continue
        names.add(first)
    if not names:
        raise ValueError(f"{path}: V3 sorry declaration allowlist is empty")
    return names


def _write_coverage(expected: set[str], actual: set[str], row_modules: set[str]) -> tuple[set[str], set[str], set[str]]:
    missing = expected - actual
    extra = actual - expected
    modules_without_rows = actual - row_modules
    lines = [
        "V4 MODULE COVERAGE INVARIANT",
        "============================",
        f"expected_modules: {len(expected)}",
        f"environment_modules: {len(actual)}",
        f"audited_row_modules: {len(row_modules)}",
        f"missing_modules: {len(missing)}",
        f"extra_modules: {len(extra)}",
        (
            "Modules without constant rows are permitted only because import-only "
            "aggregators may export no constants; their presence is proved by "
            "env.header.moduleNames."
        ),
        "",
        "[required_explicit_matrix_concentration_modules]",
        *sorted(REQUIRED_MC_MODULES),
        "",
        "[missing_modules]",
        *(sorted(missing) or ["(none)"]),
        "",
        "[extra_modules]",
        *(sorted(extra) or ["(none)"]),
        "",
        "[modules_without_constant_rows]",
        *(sorted(modules_without_rows) or ["(none)"]),
        "",
        "[expected_modules]",
        *sorted(expected),
        "",
        "[environment_modules]",
        *sorted(actual),
    ]
    write_text_if_changed(COVERAGE, "\n".join(lines) + "\n")
    return missing, extra, modules_without_rows


def analyze(v3_allowlist_path: Path | None) -> int:
    for required in (
        RAW_AUDIT,
        RAW_MODULES,
        RAW_CALIBRATION,
        RAW_TYPES,
        RAW_BINDERS,
        RAW_DIRECT_DEPENDENCIES,
    ):
        if not required.is_file():
            raise FileNotFoundError(f"missing raw V4 evidence: {required}")
    LOGS.mkdir(parents=True, exist_ok=True)
    rows = read_audit_rows()
    actual_modules = read_modules()
    expected = expected_modules()
    row_modules = {row.module for row in rows}
    missing, extra, _ = _write_coverage(expected, actual_modules, row_modules)
    calibration_errors = validate_calibration()
    type_row_count, binder_row_count, type_dump_errors = (
        validate_type_and_telescope_dumps(rows)
    )
    direct_dependency_count, direct_dependency_errors = (
        validate_direct_dependency_dump(rows)
    )

    kind_counts = collections.Counter(row.kind for row in rows)
    axiom_distribution = collections.Counter(
        tuple(sorted(row.axioms)) for row in rows
    )
    private_count = sum(row.is_private for row in rows)
    internal_count = sum(row.is_internal for row in rows)
    sorry_rows = {row.name for row in rows if SORRY_AXIOM in row.axioms}
    nonstandard_rows = [
        (row, sorted(row.axioms - ALLOWED_AXIOMS - {SORRY_AXIOM}))
        for row in rows
        if row.axioms - ALLOWED_AXIOMS - {SORRY_AXIOM}
    ]
    project_axioms = [row for row in rows if row.kind == "axiom"]
    project_opaques = [row for row in rows if row.kind == "opaque"]
    # `irreducible_def` elaborates a user-facing checked definition plus an
    # internal hygienic opaque wrapper.  Keep every such wrapper in the raw
    # inventory, but distinguish it from a user-facing `opaque` command or a
    # custom axiom.  V5 independently inventories the source command.
    internal_generated_opaques = [
        row for row in project_opaques if row.is_internal
    ]
    unexpected_user_opaques = [
        row for row in project_opaques if not row.is_internal
    ]
    project_axioms_or_opaques = [*project_axioms, *project_opaques]

    v3_status = "INCOMPLETE"
    v3_missing_from_v4: set[str] = set()
    v4_unledgered_sorry: set[str] = set()
    if v3_allowlist_path is not None:
        v3_names = read_v3_allowlist(v3_allowlist_path)
        v3_missing_from_v4 = v3_names - sorry_rows
        v4_unledgered_sorry = sorry_rows - v3_names
        v3_status = (
            "PASS"
            if not v3_missing_from_v4 and not v4_unledgered_sorry
            else "FAIL"
        )

    exceedance_rows = [
        [
            "module",
            "name",
            "kind",
            "classification",
            "unexpected_axioms",
            "all_axioms",
        ]
    ]
    for row in rows:
        unexpected = row.axioms - ALLOWED_AXIOMS
        if not unexpected:
            continue
        if unexpected == {SORRY_AXIOM}:
            classification = (
                "V3_RECONCILED_SORRY"
                if v3_allowlist_path is not None and row.name not in v4_unledgered_sorry
                else "SORRY_REQUIRES_V3_RECONCILIATION"
            )
        else:
            classification = "CRITICAL_NONSTANDARD_AXIOM"
        exceedance_rows.append(
            [
                row.module,
                row.name,
                row.kind,
                classification,
                ";".join(sorted(unexpected)),
                ";".join(sorted(row.axioms)),
            ]
        )
    write_tsv_if_changed(EXCEEDANCES, exceedance_rows)

    opaque_rows = [["module", "name", "kind", "is_private", "is_internal"]]
    opaque_rows.extend(
        [
            row.module,
            row.name,
            row.kind,
            str(row.is_private).lower(),
            str(row.is_internal).lower(),
        ]
        for row in project_axioms_or_opaques
    )
    write_tsv_if_changed(OPAQUE_AXIOM_INVENTORY, opaque_rows)

    hard_failures: list[str] = []
    incomplete_reasons: list[str] = []
    if missing:
        incomplete_reasons.append(
            f"{len(missing)} expected modules missing from environment"
        )
    if extra:
        hard_failures.append(f"{len(extra)} unexpected project-root modules in environment")
    if not REQUIRED_MC_MODULES <= actual_modules:
        incomplete_reasons.append(
            "one or more required MatrixConcentration modules were not imported"
        )
    if calibration_errors:
        hard_failures.extend(calibration_errors)
    if type_dump_errors:
        hard_failures.extend(type_dump_errors)
    if direct_dependency_errors:
        hard_failures.extend(direct_dependency_errors)
    if nonstandard_rows:
        hard_failures.append(
            f"{len(nonstandard_rows)} declarations use a nonstandard non-sorry axiom"
        )
    if project_axioms:
        hard_failures.append(
            f"{len(project_axioms)} project axiom declarations found"
        )
    if unexpected_user_opaques:
        hard_failures.append(
            f"{len(unexpected_user_opaques)} unexpected user-facing opaque "
            "declarations found"
        )
    if v3_status == "FAIL":
        hard_failures.append(
            "V3/V4 sorry declaration sets differ: "
            f"{len(v3_missing_from_v4)} V3-only, {len(v4_unledgered_sorry)} V4-only"
        )
    elif v3_status == "INCOMPLETE":
        incomplete_reasons.append("no V3 declaration-level sorry allowlist supplied")

    if incomplete_reasons:
        verdict = "INCOMPLETE"
    elif hard_failures:
        verdict = "ISSUES-FOUND"
    else:
        verdict = "PASS"

    lines = [
        "V4 EXHAUSTIVE AXIOM AUDIT SUMMARY",
        "=================================",
        f"verdict: {verdict}",
        f"declarations_audited: {len(rows)}",
        f"private_declarations_audited: {private_count}",
        f"internal_declarations_audited: {internal_count}",
        f"declaration_type_rows: {type_row_count}",
        f"declaration_binder_rows: {binder_row_count}",
        f"type_telescope_dump: {'PASS' if not type_dump_errors else 'FAIL'}",
        f"direct_dependency_edges: {direct_dependency_count}",
        (
            "direct_dependency_dump: "
            f"{'PASS' if not direct_dependency_errors else 'FAIL'}"
        ),
        f"expected_modules: {len(expected)}",
        f"environment_modules: {len(actual_modules)}",
        f"module_coverage: {'PASS' if not missing and not extra else 'FAIL'}",
        f"calibration: {'PASS' if not calibration_errors else 'FAIL'}",
        f"sorryAx_declarations: {len(sorry_rows)}",
        f"v3_reconciliation: {v3_status}",
        f"nonstandard_non_sorry_axiom_declarations: {len(nonstandard_rows)}",
        f"project_axiom_or_opaque_declarations: {len(project_axioms_or_opaques)}",
        f"project_axiom_declarations: {len(project_axioms)}",
        f"project_opaque_declarations: {len(project_opaques)}",
        (
            "internal_generated_opaque_declarations: "
            f"{len(internal_generated_opaques)}"
        ),
        (
            "unexpected_user_facing_opaque_declarations: "
            f"{len(unexpected_user_opaques)}"
        ),
        "",
        "[constant_kind_counts]",
    ]
    lines.extend(f"{kind}: {count}" for kind, count in sorted(kind_counts.items()))
    lines.extend(("", "[axiom_set_distribution]"))
    for axioms, count in sorted(
        axiom_distribution.items(), key=lambda item: (len(item[0]), item[0])
    ):
        label = ";".join(axioms) if axioms else "(none)"
        lines.append(f"{count}\t{label}")
    lines.extend(("", "[hard_failures]"))
    lines.extend(hard_failures or ["(none)"])
    lines.extend(("", "[incomplete_reasons]"))
    lines.extend(incomplete_reasons or ["(none)"])
    lines.extend(("", "[v3_only_declarations]"))
    lines.extend(sorted(v3_missing_from_v4) or ["(none)"])
    lines.extend(("", "[v4_unledgered_sorryAx_declarations]"))
    lines.extend(sorted(v4_unledgered_sorry) or ["(none)"])
    write_text_if_changed(SUMMARY, "\n".join(lines) + "\n")
    print("\n".join(lines[:19]))
    print(f"summary: {display_path(SUMMARY)}")
    print(f"coverage: {display_path(COVERAGE)}")
    print(f"exceedances: {display_path(EXCEEDANCES)}")
    return 2 if incomplete_reasons else (1 if hard_failures else 0)


def run_harness(v2_evidence: Path, v3_allowlist_path: Path | None) -> int:
    if not v2_evidence.is_file() or not v2_evidence.read_text(
        encoding="utf-8", errors="replace"
    ).strip():
        raise RuntimeError(
            "refusing to run V4 before nonempty V2 evidence exists: "
            f"{v2_evidence}"
        )
    if not HARNESS.is_file():
        raise FileNotFoundError(HARNESS)
    LOGS.mkdir(parents=True, exist_ok=True)
    with RUN_LOCK.open("a+", encoding="utf-8") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            lock.seek(0)
            owner = lock.read().strip() or "unknown owner"
            raise RuntimeError(
                "refusing concurrent V4 run; the evidence writer lock is "
                f"held by {owner}"
            ) from error
        lock.seek(0)
        lock.truncate()
        lock.write(
            f"pid={os.getpid()} "
            f"started={dt.datetime.now(dt.timezone.utc).astimezone().isoformat()}\n"
        )
        lock.flush()
        return _run_harness_locked(v3_allowlist_path)


def _run_harness_locked(v3_allowlist_path: Path | None) -> int:
    lake = Path.home() / ".elan" / "bin" / "lake"
    command = [
        str(lake),
        "env",
        "lean",
        "-DmaxSynthPendingDepth=3",
        "-DrelaxedAutoImplicit=false",
        str(HARNESS),
    ]
    started = dt.datetime.now(dt.timezone.utc).astimezone()
    with BUILD_LOG.open("w", encoding="utf-8") as log:
        log.write(f"started: {started.isoformat()}\n")
        log.write(f"cwd: {ROOT}\n")
        log.write(f"command: {shlex.join(command)}\n\n")
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
        log.write(f"elapsed_seconds: {(finished - started).total_seconds():.3f}\n")
        log.write(f"exit_code: {completed.returncode}\n")
    if completed.returncode != 0:
        print(f"Lean harness failed; see {display_path(BUILD_LOG)}", file=sys.stderr)
        return completed.returncode
    return analyze(v3_allowlist_path)


def self_test() -> int:
    assert source_path_to_module(
        "HighDimensionalProbability/Appendix/Infra/BerryEsseenSmoothing.lean"
    ) == "HighDimensionalProbability.Appendix.Infra.BerryEsseenSmoothing"
    assert source_path_to_module(
        "MatrixConcentration/Appendix_MatrixRosenthal.lean"
    ) == "MatrixConcentration.Appendix_MatrixRosenthal"
    assert source_path_to_module(
        "HighDimensionalProbability.lean"
    ) == "HighDimensionalProbability"
    expected = expected_modules()
    assert REQUIRED_MC_MODULES <= expected
    assert "HighDimensionalProbability" in expected
    assert "MatrixConcentration" not in expected
    print(
        "PASS: axiom-audit Python self-test; "
        f"{len(expected)} physical/root modules expected"
    )
    return 0


def _resolve_from_root(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="action", required=True)
    subparsers.add_parser("self-test")

    analyze_parser = subparsers.add_parser("analyze")
    analyze_parser.add_argument(
        "--v3-sorry-declarations",
        type=Path,
        help="declaration-level V3 allowlist; omission makes the verdict INCOMPLETE",
    )

    run_parser = subparsers.add_parser("run")
    run_parser.add_argument(
        "--v2-evidence",
        type=Path,
        default=Path(
            "HighDimensionalProbability/Verification/logs/recert_import_graph.txt"
        ),
        help="nonempty completed V2 evidence; V4 refuses to run before it exists",
    )
    run_parser.add_argument(
        "--v3-sorry-declarations",
        type=Path,
        help="declaration-level V3 allowlist; omission makes the verdict INCOMPLETE",
    )

    args = parser.parse_args()
    if args.action == "self-test":
        return self_test()
    v3_path = (
        _resolve_from_root(args.v3_sorry_declarations)
        if args.v3_sorry_declarations is not None
        else None
    )
    if args.action == "analyze":
        return analyze(v3_path)
    if args.action == "run":
        return run_harness(_resolve_from_root(args.v2_evidence), v3_path)
    raise AssertionError(args.action)


if __name__ == "__main__":
    raise SystemExit(main())
