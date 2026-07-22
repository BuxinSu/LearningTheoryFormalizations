#!/usr/bin/env python3
"""V10 conditional-interface and undischarged-assumption census.

This script joins two independent inventories:

* a comment/string-aware textual scan over the shared FILE-WALK UNIVERSE; and
* environment data emitted by ``v10_environment.lean``.

It deliberately distinguishes a predicate's *source* instantiation status
from its semantic adjudication.  In particular, an explicit data-model
hypothesis can be CONSUMED-ONLY in the source without being an unproved
mathematical principle.  The latter judgment is supplied by the checked
``curation/v10_adjudication.tsv`` register.

The machine outputs are complete inventories, not samples.  Every input row is
either represented in an output or causes a hard failure.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from lean_source_scan import (
    LOGS,
    ROOT,
    VERIFY,
    lexical_contexts,
    lean_universe,
    relative,
    tsv_safe,
)


CURATION = VERIFY / "curation"
WORK = ROOT / ".audit_work"
SOURCE_README = ROOT / "MatrixConcentration" / "README.md"
APPENDIX_SUMMARY = ROOT / "MatrixConcentration" / "APPENDIX_SUMMARY.md"
TRANSLATION = ROOT.parent / "TranslationReport"

ENV_PREDICATES = LOGS / "v10_environment_predicates.tsv"
ENV_FIELDS = LOGS / "v10_environment_prop_fields.tsv"
ENV_CONSTANTS = LOGS / "v10_environment_constants.tsv"
ENV_STRUCTURES = LOGS / "v10_environment_structures.tsv"
ENV_ROLES = LOGS / "v10_declaration_roles.tsv"
ENV_PROP_BINDERS = LOGS / "v10_prop_binders.tsv"
ENV_INSTANCE_BINDERS = LOGS / "v10_instance_binders.tsv"
ENV_MODULES = LOGS / "v10_modules.txt"
ENV_SUMMARY = LOGS / "v10_environment_summary.txt"
ENV_COMPILE_LOG = LOGS / "v10_environment_compile.log"
AXIOM_AUDIT = LOGS / "axiom_audit.tsv"
AXIOM_SUMMARY = LOGS / "axiom_summary.json"
AXIOM_MODULES = LOGS / "axiom_modules.txt"
AXIOM_CALIBRATION = LOGS / "axiom_calibration.tsv"
CORRESPONDENCE = LOGS / "v6_correspondence_rows.tsv"
ADJUDICATION = CURATION / "v10_adjudication.tsv"
INLINE_ADJUDICATION = CURATION / "v10_inline_adjudication.tsv"
PLANT = WORK / "ConditionalPlant.lean"
PLANT_COMPILE_LOG = LOGS / "v10_conditional_calibration_compile.log"
INLINE_PLANT_BINDERS = LOGS / "v10_inline_calibration_binders.tsv"
WITNESS_COMPILE_LOG = LOGS / "v10_witnesses_compile.log"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SOURCE_STATUSES = {"PROVED", "CONSUMED-ONLY", "DEAD"}
SEMANTIC_CLASSES = {
    "SOURCE_DISCHARGED",
    "ORDINARY_MODEL_CONDITION",
    "DISCLOSED_CONDITIONAL_INFRASTRUCTURE",
    "DEAD_CODE",
}
PUBLICATION_CLASSES = {
    "SOURCE_PROVED",
    "PUBLISHED_EXPLICIT_HYPOTHESIS",
    "UNPUBLISHED_INFRASTRUCTURE",
    "UNPUBLISHED_DEAD",
}
ADJUDICATION_HEADER = [
    "predicate",
    "source_status",
    "expected_producer_or_witness",
    "semantic_class",
    "publication",
    "disclosure",
    "ledger",
    "adjudication",
]
INLINE_ADJUDICATION_HEADER = [
    "type_hash",
    "adjudication",
    "evidence",
    "reviewer_note",
]
INLINE_CLEAN_ADJUDICATIONS = {
    "ROUTINE_EXPLICIT_HYPOTHESIS",
    "DISCHARGED_BY_SOURCE_CALLER",
}
INLINE_FINDING_ADJUDICATIONS = {
    "DISCLOSED_CONDITIONAL_INFRASTRUCTURE",
    "UNDISCLOSED_CONDITIONAL_PRINCIPLE",
    "UNRESOLVED_REVIEW_RISK",
}

KNOWN_CONDITIONALS = {
    "MatrixConcentration.HermitianNCKhintchineAt",
    "MatrixConcentration.RectangularNCKhintchineAt",
    "MatrixConcentration.ProvidesCenteredRosenthalBootstrap",
}
EXPECTED_KNOWN_CONSUMERS = {
    "MatrixConcentration.HermitianNCKhintchineAt": {
        (
            "MatrixConcentration.hermitian_nckhintchine_implies_rectangular",
            "PROP_BINDER",
        ),
    },
    "MatrixConcentration.RectangularNCKhintchineAt": {
        (
            "MatrixConcentration.ProvidesCenteredRosenthalBootstrap",
            "DEFINITION_BODY",
        ),
        (
            "MatrixConcentration.matrix_rosenthal_pinelis_of_nck_and_bootstrap",
            "PROP_BINDER",
        ),
        (
            "MatrixConcentration.matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap",
            "PROP_BINDER",
        ),
    },
    "MatrixConcentration.ProvidesCenteredRosenthalBootstrap": {
        (
            "MatrixConcentration.matrix_rosenthal_pinelis_of_nck_and_bootstrap",
            "PROP_BINDER",
        ),
        (
            "MatrixConcentration.matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap",
            "PROP_BINDER",
        ),
    },
}


@dataclass(frozen=True)
class SourceDeclaration:
    path: Path
    module: str
    keyword: str
    name: str
    line: int
    end_line: int
    header: str
    codomain: str
    prop_codomain: bool


def require_file(path: Path, errors: list[str]) -> bool:
    if not path.is_file() or path.stat().st_size == 0:
        errors.append(f"missing or empty required input: {relative(path)}")
        return False
    return True


def read_tsv(
    path: Path,
    expected_header: Sequence[str] | None = None,
) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        header = reader.fieldnames or []
        if expected_header is not None and list(header) != list(expected_header):
            raise RuntimeError(
                f"{relative(path)} header mismatch: expected "
                f"{list(expected_header)!r}, measured {header!r}"
            )
        rows = list(reader)
    for index, row in enumerate(rows, start=2):
        if None in row:
            raise RuntimeError(f"{relative(path)}:{index}: extra TSV fields")
    return rows


def read_environment_summary(
    path: Path,
    errors: list[str],
) -> dict[str, str]:
    """Read the environment emitter's single-valued coverage metrics."""

    expected = {
        "MODULES",
        "PROJECT_CONSTANTS",
        "SOURCE_BACKED_CONSTANTS",
        "PROJECT_DEFINITIONS",
        "PROP_CODOMAIN_DEF_OR_ABBREV",
        "PROJECT_STRUCTURES",
        "PROJECT_CLASSES",
        "PROP_VALUED_STRUCTURE_OR_CLASS_FIELDS",
        "PROP_BINDERS",
        "INSTANCE_BINDERS",
        "CODOMAIN_RULE",
        "ROLE_RULE",
        "VERDICT",
    }
    metrics: dict[str, str] = {}
    for line_number, raw_line in enumerate(
        path.read_text(encoding="utf-8").splitlines(),
        start=1,
    ):
        line = raw_line.strip()
        if not line:
            continue
        key, _, value = line.partition(" ")
        if key not in expected:
            continue
        if not value:
            errors.append(
                f"{relative(path)}:{line_number}: empty value for {key}"
            )
            continue
        if key in metrics:
            errors.append(
                f"{relative(path)}:{line_number}: duplicate metric {key}"
            )
            continue
        metrics[key] = value.strip()
    missing = expected - set(metrics)
    if missing:
        errors.append(
            f"{relative(path)} missing metrics: " + ",".join(sorted(missing))
        )
    return metrics


def checked_metric_int(
    metrics: dict[str, str],
    key: str,
    errors: list[str],
) -> int | None:
    value = metrics.get(key)
    if value is None:
        return None
    try:
        result = int(value)
    except ValueError:
        errors.append(f"{relative(ENV_SUMMARY)}: {key} is not an integer: {value!r}")
        return None
    if result < 0:
        errors.append(f"{relative(ENV_SUMMARY)}: {key} is negative: {result}")
        return None
    return result


def validate_lean_compile_log(
    path: Path,
    label: str,
    errors: list[str],
) -> bool:
    """Require a fresh runner-written success marker and a clean Lean log."""

    text = path.read_text(encoding="utf-8", errors="replace")
    statuses = re.findall(r"^LEAN_EXIT_STATUS ([0-9]+)$", text, re.MULTILINE)
    clean = (
        statuses == ["0"]
        and not re.search(
            r"\berror:|declaration uses ['\"]?sorry",
            text,
            re.IGNORECASE,
        )
    )
    if statuses != ["0"]:
        errors.append(
            f"{label} compile log has success markers {statuses!r}, expected ['0']"
        )
    if re.search(r"\berror:", text, re.IGNORECASE):
        errors.append(f"{label} compile log contains a Lean error")
    if re.search(
        r"declaration uses ['\"]?sorry",
        text,
        re.IGNORECASE,
    ):
        errors.append(f"{label} compile log contains a sorry warning")
    return clean


def validate_environment_coverage(
    universe: list[Path],
    modules: list[str],
    metrics: dict[str, str],
    constants: list[dict[str, str]],
    structures: list[dict[str, str]],
    axiom_rows: list[dict[str, str]],
    axiom_summary: dict[str, object],
    axiom_modules_list: list[str],
    axiom_calibration: list[dict[str, str]],
    predicates: list[dict[str, str]],
    prop_fields: list[dict[str, str]],
    roles: list[dict[str, str]],
    prop_binders: list[dict[str, str]],
    instance_binders: list[dict[str, str]],
    errors: list[str],
) -> dict[str, object]:
    """Cross-check that the optimized environment walk retained full scope."""

    expected_modules = sorted(source_module(path) for path in universe)
    if len(modules) != len(set(modules)):
        errors.append(
            f"{relative(ENV_MODULES)} contains duplicate module names"
        )
    if modules != sorted(modules):
        errors.append(f"{relative(ENV_MODULES)} is not lexicographically sorted")
    if modules != expected_modules:
        errors.append(
            "environment/file-walk module-set mismatch: missing="
            + ",".join(sorted(set(expected_modules) - set(modules)))
            + " extra="
            + ",".join(sorted(set(modules) - set(expected_modules)))
        )
    if len(axiom_modules_list) != len(set(axiom_modules_list)):
        errors.append(f"{relative(AXIOM_MODULES)} contains duplicate module names")
    if axiom_modules_list != sorted(axiom_modules_list):
        errors.append(f"{relative(AXIOM_MODULES)} is not lexicographically sorted")
    if axiom_modules_list != expected_modules:
        errors.append(
            "V4/file-walk module-set mismatch: missing="
            + ",".join(sorted(set(expected_modules) - set(axiom_modules_list)))
            + " extra="
            + ",".join(sorted(set(axiom_modules_list) - set(expected_modules)))
        )

    if not axiom_rows:
        errors.append(f"{relative(AXIOM_AUDIT)} has no declaration rows")
    axiom_keys = [(row["module"], row["name"]) for row in axiom_rows]
    axiom_names = [row["name"] for row in axiom_rows]
    if any(
        not row["module"]
        or not row["name"]
        or not row["user_name"]
        or not row["kind"]
        for row in axiom_rows
    ):
        errors.append(f"{relative(AXIOM_AUDIT)} has blank identity/kind fields")
    if len(axiom_keys) != len(set(axiom_keys)):
        errors.append(f"{relative(AXIOM_AUDIT)} has duplicate module/name rows")
    if len(axiom_names) != len(set(axiom_names)):
        errors.append(f"{relative(AXIOM_AUDIT)} has duplicate global names")
    axiom_modules = {row["module"] for row in axiom_rows}
    if not axiom_modules <= set(expected_modules):
        errors.append(
            f"{relative(AXIOM_AUDIT)} contains non-universe modules: "
            + ",".join(sorted(axiom_modules - set(expected_modules)))
        )

    constant_triples = [
        (row["module"], row["name"], row["kind"]) for row in constants
    ]
    axiom_triples = [
        (row["module"], row["name"], row["kind"]) for row in axiom_rows
    ]
    if any(not all(triple) for triple in constant_triples):
        errors.append(f"{relative(ENV_CONSTANTS)} has blank identity/kind fields")
    if len(constant_triples) != len(set(constant_triples)):
        errors.append(f"{relative(ENV_CONSTANTS)} has duplicate rows")
    if [row["name"] for row in constants] != sorted(
        row["name"] for row in constants
    ):
        errors.append(f"{relative(ENV_CONSTANTS)} is not sorted by constant name")
    if set(constant_triples) != set(axiom_triples):
        errors.append(
            "V10/V4 project-constant identity mismatch: v10_only="
            + ",".join(
                f"{module}:{name}:{kind}"
                for module, name, kind in sorted(
                    set(constant_triples) - set(axiom_triples)
                )
            )
            + " v4_only="
            + ",".join(
                f"{module}:{name}:{kind}"
                for module, name, kind in sorted(
                    set(axiom_triples) - set(constant_triples)
                )
            )
        )

    constants_by_name = {
        row["name"]: (row["module"], row["kind"]) for row in constants
    }

    owner_ranges: dict[str, tuple[int, int]] = {}

    def validate_named_rows(
        rows: list[dict[str, str]],
        label: str,
        *,
        theorem_only: bool = False,
        unique_names: bool = True,
    ) -> None:
        seen: set[str] = set()
        for index, row in enumerate(rows, start=2):
            name = row.get("name", "")
            module = row.get("module", "")
            if not name or not module:
                errors.append(f"{label}:{index}: blank module/name")
                continue
            if unique_names and name in seen:
                errors.append(f"{label}:{index}: duplicate name {name}")
            seen.add(name)
            constant = constants_by_name.get(name)
            if constant is None:
                errors.append(f"{label}:{index}: unknown project constant {name}")
                continue
            if constant[0] != module:
                errors.append(
                    f"{label}:{index}: module mismatch for {name}: "
                    f"{module} != {constant[0]}"
                )
            row_kind = row.get("kind")
            if row_kind is not None and row_kind != constant[1]:
                errors.append(
                    f"{label}:{index}: kind mismatch for {name}: "
                    f"{row_kind} != {constant[1]}"
                )
            if theorem_only and constant[1] != "theorem":
                errors.append(
                    f"{label}:{index}: non-theorem binder owner {name}: "
                    f"{constant[1]}"
                )

            range_start = row.get("range_start_line")
            range_end = row.get("range_end_line")
            if range_start is not None or range_end is not None:
                try:
                    start = int(range_start or "")
                    end = int(range_end or "")
                    if (
                        start <= 0
                        or end < start
                        or range_start != str(start)
                        or range_end != str(end)
                    ):
                        raise ValueError
                except ValueError:
                    errors.append(
                        f"{label}:{index}: invalid source range "
                        f"{range_start!r}..{range_end!r}"
                    )
                else:
                    measured_range = (start, end)
                    previous_range = owner_ranges.setdefault(name, measured_range)
                    if previous_range != measured_range:
                        errors.append(
                            f"{label}:{index}: inconsistent source range for {name}: "
                            f"{measured_range} != {previous_range}"
                        )

    validate_named_rows(predicates, relative(ENV_PREDICATES))
    validate_named_rows(roles, relative(ENV_ROLES))
    for index, row in enumerate(predicates, start=2):
        constant = constants_by_name.get(row.get("name", ""))
        if constant is not None and constant[1] != "definition":
            errors.append(
                f"{relative(ENV_PREDICATES)}:{index}: predicate owner "
                f"{row['name']} has non-definition kind {constant[1]}"
            )

    for rows, path in (
        (prop_binders, ENV_PROP_BINDERS),
        (instance_binders, ENV_INSTANCE_BINDERS),
    ):
        seen_binders: set[tuple[str, str]] = set()
        validate_named_rows(
            rows,
            relative(path),
            theorem_only=True,
            unique_names=False,
        )
        for index, row in enumerate(rows, start=2):
            name = row.get("name", "")
            raw_index = row.get("binder_index", "")
            if not raw_index:
                errors.append(f"{relative(path)}:{index}: blank binder index")
            try:
                binder_index = int(raw_index)
                if binder_index <= 0 or raw_index != str(binder_index):
                    raise ValueError
            except ValueError:
                errors.append(
                    f"{relative(path)}:{index}: invalid binder index {raw_index!r}"
                )
                continue
            key = (name, str(binder_index))
            if key in seen_binders:
                errors.append(
                    f"{relative(path)}:{index}: duplicate name/binder_index {key}"
                )
            seen_binders.add(key)

    seen_structures: set[str] = set()
    for index, row in enumerate(structures, start=2):
        name = row.get("structure", "")
        module = row.get("module", "")
        is_class = row.get("structure_is_class", "")
        if not name or not module or is_class not in {"true", "false"}:
            errors.append(
                f"{relative(ENV_STRUCTURES)}:{index}: invalid structure identity/class flag"
            )
            continue
        if name in seen_structures:
            errors.append(
                f"{relative(ENV_STRUCTURES)}:{index}: duplicate structure {name}"
            )
        seen_structures.add(name)
        constant = constants_by_name.get(name)
        if constant is None:
            errors.append(
                f"{relative(ENV_STRUCTURES)}:{index}: unknown structure {name}"
            )
        elif constant != (module, "inductive"):
            errors.append(
                f"{relative(ENV_STRUCTURES)}:{index}: structure ownership/kind "
                f"mismatch for {name}: {(module, 'inductive')} != {constant}"
            )

    seen_fields: set[str] = set()
    for index, row in enumerate(prop_fields, start=2):
        field = row.get("field", "")
        structure = row.get("structure", "")
        module = row.get("module", "")
        if not field or not structure or not module:
            errors.append(f"{relative(ENV_FIELDS)}:{index}: blank field identity")
            continue
        if field in seen_fields:
            errors.append(f"{relative(ENV_FIELDS)}:{index}: duplicate field {field}")
        seen_fields.add(field)
        for name, role in ((field, "field"), (structure, "structure")):
            constant = constants_by_name.get(name)
            if constant is None:
                errors.append(
                    f"{relative(ENV_FIELDS)}:{index}: unknown {role} constant {name}"
                )
            elif constant[0] != module:
                errors.append(
                    f"{relative(ENV_FIELDS)}:{index}: {role} module mismatch "
                    f"for {name}: {module} != {constant[0]}"
                )
        try:
            start = int(row["range_start_line"])
            end = int(row["range_end_line"])
            if (
                start <= 0
                or end < start
                or row["range_start_line"] != str(start)
                or row["range_end_line"] != str(end)
            ):
                raise ValueError
        except (KeyError, ValueError):
            errors.append(
                f"{relative(ENV_FIELDS)}:{index}: invalid source range "
                f"{row.get('range_start_line', '')!r}.."
                f"{row.get('range_end_line', '')!r}"
            )

    axiom_kind_counts = Counter(row["kind"] for row in axiom_rows)
    axiom_module_counts = Counter(row["module"] for row in axiom_rows)
    axiom_distribution = Counter(
        tuple(sorted(split_names(row["axioms"]))) for row in axiom_rows
    )
    malformed_axiom_rows = [
        row["name"]
        for row in axiom_rows
        if row["axioms"] and (
            any(not token for token in row["axioms"].split(","))
            or len(row["axioms"].split(","))
            != len(set(row["axioms"].split(",")))
        )
    ]
    unexpected_axiom_rows = [
        row["name"]
        for row in axiom_rows
        if not split_names(row["axioms"]) <= ALLOWED_AXIOMS
    ]
    sorry_axiom_rows = [
        row["name"]
        for row in axiom_rows
        if "sorryAx" in split_names(row["axioms"])
    ]
    reduce_or_trust_rows = [
        row["name"]
        for row in axiom_rows
        if split_names(row["axioms"])
        & {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
    ]
    declared_axiom_rows = [
        row["name"] for row in axiom_rows if row["kind"] == "axiom"
    ]
    declared_opaque_rows = [
        row["name"] for row in axiom_rows if row["kind"] == "opaque"
    ]
    calibration_public = [
        row
        for row in axiom_calibration
        if row["user_name"] == "VerificationPublicAxiomCalibration"
        and "sorryAx" in split_names(row["axioms"])
    ]
    calibration_private = [
        row
        for row in axiom_calibration
        if row["user_name"] == "verificationPrivateAxiomCalibration"
        and row["name"].startswith("_private.")
        and "sorryAx" in split_names(row["axioms"])
    ]
    if any(
        not row["name"] or not row["user_name"] or not row["axioms"]
        for row in axiom_calibration
    ):
        errors.append(f"{relative(AXIOM_CALIBRATION)} has blank calibration fields")
    if len(calibration_public) != 1 or len(calibration_private) != 1:
        errors.append(
            f"{relative(AXIOM_CALIBRATION)} calibration coverage mismatch: "
            f"public={len(calibration_public)} private={len(calibration_private)}"
        )
    if malformed_axiom_rows:
        errors.append(
            f"{relative(AXIOM_AUDIT)} has malformed axiom lists for "
            + ",".join(malformed_axiom_rows)
        )
    if unexpected_axiom_rows:
        errors.append(
            f"{relative(AXIOM_AUDIT)} has unexpected axiom dependencies for "
            + ",".join(unexpected_axiom_rows)
        )
    if sorry_axiom_rows:
        errors.append(
            f"{relative(AXIOM_AUDIT)} has sorryAx dependencies for "
            + ",".join(sorry_axiom_rows)
        )
    if reduce_or_trust_rows:
        errors.append(
            f"{relative(AXIOM_AUDIT)} has reduce/trust dependencies for "
            + ",".join(reduce_or_trust_rows)
        )
    if declared_axiom_rows:
        errors.append(
            f"{relative(AXIOM_AUDIT)} has declared project axioms "
            + ",".join(declared_axiom_rows)
        )
    if declared_opaque_rows:
        errors.append(
            f"{relative(AXIOM_AUDIT)} has declared project opaques "
            + ",".join(declared_opaque_rows)
        )
    summary_clean_checks = {
        "total_declarations": len(axiom_rows),
        "expected_module_count": len(expected_modules),
        "module_count": len(expected_modules),
        "exceedances": 0,
        "sorryAx_dependencies": 0,
        "reduce_or_trust_dependencies": 0,
        "declared_axioms": 0,
        "declared_opaques": 0,
        "calibration_public_sorryAx": len(calibration_public),
        "calibration_private_sorryAx": len(calibration_private),
    }
    for key, expected in summary_clean_checks.items():
        if axiom_summary.get(key) != expected:
            errors.append(
                f"{relative(AXIOM_SUMMARY)}: {key}="
                f"{axiom_summary.get(key)!r}, expected {expected!r}"
            )
    for key in ("missing_modules", "unexpected_modules", "duplicate_names"):
        if axiom_summary.get(key) != []:
            errors.append(
                f"{relative(AXIOM_SUMMARY)}: {key} must be an empty list"
            )
    expected_without_constants = sorted(
        set(axiom_modules_list) - axiom_modules
    )
    if axiom_summary.get("modules_without_constants") != expected_without_constants:
        errors.append(
            f"{relative(AXIOM_SUMMARY)}: modules_without_constants mismatch"
        )
    if axiom_summary.get("allowed_axioms") != sorted(ALLOWED_AXIOMS):
        errors.append(f"{relative(AXIOM_SUMMARY)}: allowed_axioms mismatch")
    if axiom_summary.get("kind_counts") != dict(sorted(axiom_kind_counts.items())):
        errors.append(f"{relative(AXIOM_SUMMARY)}: kind_counts mismatch")
    if axiom_summary.get("module_declaration_counts") != dict(
        sorted(axiom_module_counts.items())
    ):
        errors.append(
            f"{relative(AXIOM_SUMMARY)}: module_declaration_counts mismatch"
        )
    expected_distribution = {
        ",".join(axioms) or "(none)": count
        for axioms, count in sorted(
            axiom_distribution.items(),
            key=lambda item: (len(item[0]), item[0]),
        )
    }
    if axiom_summary.get("axiom_distribution") != expected_distribution:
        errors.append(f"{relative(AXIOM_SUMMARY)}: axiom_distribution mismatch")
    private_count = sum(
        row["name"].startswith("_private.") for row in axiom_rows
    )
    internal_count = sum(
        row["name"].startswith("_")
        or "._@" in row["name"]
        or ".match_" in row["name"]
        or ".proof_" in row["name"]
        for row in axiom_rows
    )
    if axiom_summary.get("private_declarations") != private_count:
        errors.append(f"{relative(AXIOM_SUMMARY)}: private_declarations mismatch")
    if axiom_summary.get("internal_or_generated_declarations") != internal_count:
        errors.append(
            f"{relative(AXIOM_SUMMARY)}: "
            "internal_or_generated_declarations mismatch"
        )

    measured = {
        "MODULES": len(modules),
        "PROJECT_CONSTANTS": len(constants),
        "SOURCE_BACKED_CONSTANTS": len(roles),
        "PROJECT_DEFINITIONS": axiom_kind_counts["definition"],
        "PROP_CODOMAIN_DEF_OR_ABBREV": len(predicates),
        "PROP_VALUED_STRUCTURE_OR_CLASS_FIELDS": len(prop_fields),
        "PROP_BINDERS": len(prop_binders),
        "INSTANCE_BINDERS": len(instance_binders),
    }
    emitted: dict[str, int | None] = {}
    for key, actual in measured.items():
        claimed = checked_metric_int(metrics, key, errors)
        emitted[key] = claimed
        if claimed is not None and claimed != actual:
            errors.append(
                f"environment coverage mismatch for {key}: "
                f"summary={claimed} independent_input={actual}"
            )
    structure_count = checked_metric_int(metrics, "PROJECT_STRUCTURES", errors)
    class_count = checked_metric_int(metrics, "PROJECT_CLASSES", errors)
    inductive_count = axiom_kind_counts["inductive"]
    if structure_count is not None and structure_count > inductive_count:
        errors.append(
            "environment coverage mismatch for PROJECT_STRUCTURES: "
            f"summary={structure_count} exceeds V4 inductives={inductive_count}"
        )
    if structure_count is not None and structure_count != len(structures):
        errors.append(
            "environment coverage mismatch for PROJECT_STRUCTURES: "
            f"summary={structure_count} inventory={len(structures)}"
        )
    measured_class_count = sum(
        row["structure_is_class"] == "true" for row in structures
    )
    if class_count is not None and class_count != measured_class_count:
        errors.append(
            "environment coverage mismatch for PROJECT_CLASSES: "
            f"summary={class_count} inventory={measured_class_count}"
        )
    if (
        structure_count is not None
        and class_count is not None
        and class_count > structure_count
    ):
        errors.append(
            "environment coverage mismatch for PROJECT_CLASSES: "
            f"summary={class_count} exceeds structures={structure_count}"
        )
    if metrics.get("VERDICT") != "PASS":
        errors.append(
            f"{relative(ENV_SUMMARY)} verdict is "
            f"{metrics.get('VERDICT', 'MISSING')!r}, expected 'PASS'"
        )

    passed = (
        not errors
        and
        modules == expected_modules
        and len(modules) == len(set(modules))
        and modules == sorted(modules)
        and axiom_modules_list == expected_modules
        and len(axiom_modules_list) == len(set(axiom_modules_list))
        and len(axiom_keys) == len(set(axiom_keys))
        and len(axiom_names) == len(set(axiom_names))
        and axiom_modules <= set(expected_modules)
        and len(constant_triples) == len(set(constant_triples))
        and set(constant_triples) == set(axiom_triples)
        and all(
            axiom_summary.get(key) == expected
            for key, expected in summary_clean_checks.items()
        )
        and all(
            axiom_summary.get(key) == []
            for key in ("missing_modules", "unexpected_modules", "duplicate_names")
        )
        and axiom_summary.get("modules_without_constants")
        == expected_without_constants
        and axiom_summary.get("allowed_axioms") == sorted(ALLOWED_AXIOMS)
        and axiom_summary.get("kind_counts")
        == dict(sorted(axiom_kind_counts.items()))
        and axiom_summary.get("module_declaration_counts")
        == dict(sorted(axiom_module_counts.items()))
        and axiom_summary.get("axiom_distribution") == expected_distribution
        and axiom_summary.get("private_declarations") == private_count
        and axiom_summary.get("internal_or_generated_declarations")
        == internal_count
        and not malformed_axiom_rows
        and not unexpected_axiom_rows
        and not sorry_axiom_rows
        and not reduce_or_trust_rows
        and not declared_axiom_rows
        and not declared_opaque_rows
        and len(calibration_public) == 1
        and len(calibration_private) == 1
        and metrics.get("VERDICT") == "PASS"
        and all(emitted[key] == value for key, value in measured.items())
        and structure_count is not None
        and class_count is not None
        and structure_count == len(structures)
        and class_count == measured_class_count
        and structure_count <= inductive_count
        and class_count <= structure_count
    )
    return {
        "module_rows": len(modules),
        "file_walk_module_rows": len(expected_modules),
        "v10_project_constant_rows": len(constants),
        "v10_structure_rows": len(structures),
        "v4_axiom_rows": len(axiom_rows),
        "environment_summary_metrics": emitted,
        "independent_input_metrics": measured,
        "verdict": "PASS" if passed else "FAIL",
        "method": (
            "exact environment/file-walk module equality; PROJECT_CONSTANTS "
            "reconciled by exact (module,name,kind) identity to the independently "
            "validated V4 all-constant axiom audit; source-backed roles, "
            "predicate rows, Prop-field rows, Prop binders, and instance binders "
            "checked for identity, module ownership, uniqueness, and reconciliation "
            "to their emitted complete inventories"
        ),
    }


def write_tsv(
    path: Path,
    fields: Sequence[str],
    rows: Iterable[dict[str, object]],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(fields),
            delimiter="\t",
            extrasaction="ignore",
            lineterminator="\n",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({field: tsv_safe(row.get(field, "")) for field in fields})


def split_names(value: str) -> set[str]:
    return {item for item in value.split(",") if item}


def suffix_match(full_name: str, expected: str) -> bool:
    return full_name == expected or full_name.endswith("." + expected)


def mask_noncode(text: str) -> str:
    """Replace comments and strings by spaces while preserving line breaks."""

    contexts = lexical_contexts(text)
    return "".join(
        char if context == 0 or char == "\n" else " "
        for char, context in zip(text, contexts, strict=True)
    )


DECL_START = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|opaque)\s+)*"
    r"(?P<keyword>def|abbrev|theorem|lemma)\s+"
    r"(?P<name>[^\s({:\[]+)"
)


def find_header_end(masked: str, start: int) -> int | None:
    """Find a declaration's top-level ``:=`` delimiter."""

    paren = brace = bracket = 0
    index = start
    while index + 1 < len(masked):
        char = masked[index]
        if char == "(":
            paren += 1
        elif char == ")":
            paren -= 1
        elif char == "{":
            brace += 1
        elif char == "}":
            brace -= 1
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket -= 1
        if min(paren, brace, bracket) < 0:
            return None
        if (
            char == ":"
            and masked[index + 1] == "="
            and paren == brace == bracket == 0
        ):
            return index
        index += 1
    return None


def top_level_colons(header: str) -> list[int]:
    paren = brace = bracket = 0
    result: list[int] = []
    for index, char in enumerate(header):
        if char == "(":
            paren += 1
        elif char == ")":
            paren -= 1
        elif char == "{":
            brace += 1
        elif char == "}":
            brace -= 1
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket -= 1
        elif char == ":" and paren == brace == bracket == 0:
            result.append(index)
    return result


def source_module(path: Path) -> str:
    rel = path.relative_to(ROOT)
    if rel == Path("MatrixConcentration.lean"):
        return "MatrixConcentration"
    if len(rel.parts) == 2 and rel.parts[0] == "MatrixConcentration":
        return f"MatrixConcentration.{path.stem}"
    return rel.with_suffix("").as_posix().replace("/", ".")


def parse_source_declarations(paths: Iterable[Path]) -> list[SourceDeclaration]:
    declarations: list[SourceDeclaration] = []
    for path in sorted(paths, key=relative):
        text = path.read_text(encoding="utf-8")
        masked = mask_noncode(text)
        for match in DECL_START.finditer(masked):
            end = find_header_end(masked, match.end())
            if end is None:
                raise RuntimeError(
                    f"{relative(path)}:{text.count(chr(10), 0, match.start()) + 1}: "
                    f"could not find top-level ':=' for {match.group('keyword')} "
                    f"{match.group('name')}"
                )
            header = masked[match.start() : end]
            colons = top_level_colons(header)
            codomain = header[colons[-1] + 1 :] if colons else ""
            normalized_codomain = re.sub(r"\s+", "", codomain)
            declarations.append(
                SourceDeclaration(
                    path=path,
                    module=source_module(path),
                    keyword=match.group("keyword"),
                    name=match.group("name"),
                    line=text.count("\n", 0, match.start("keyword")) + 1,
                    end_line=text.count("\n", 0, end) + 1,
                    header=re.sub(r"\s+", " ", header).strip(),
                    codomain=re.sub(r"\s+", " ", codomain).strip(),
                    prop_codomain=normalized_codomain == "Prop",
                )
            )
    return declarations


def normalized_type(value: str) -> str:
    """Return a stable, alpha-normalized structural rendering.

    ``reprStr`` on an ``Expr`` includes process-local fvar names such as
    ``(Lean.Name.mkNum `_uniq 27774)``.  The numbers are allocation ids, not
    part of the proposition.  Renumber them by first occurrence within each
    type so repeated references remain equal while clean reruns hash to the
    same value.  Internal hygienic binder counters are likewise erased.
    Fully-qualified generated declaration hashes (for example
    ``x.«_@».Mathlib...``) are retained because they identify constants rather
    than local variables.
    """

    value = re.sub(r"\s+", " ", value).strip()
    # Pretty-printer collision suffixes are presentation artifacts, not types.
    value = re.sub(r"(?<=\w)✝+\d*", "✝", value)
    fvar_ids: dict[str, int] = {}

    def canonical_fvar(match: re.Match[str]) -> str:
        old_id = match.group(1)
        new_id = fvar_ids.setdefault(old_id, len(fvar_ids))
        return f"(Lean.Name.mkNum `_uniq {new_id})"

    value = re.sub(
        r"\(Lean\.Name\.mkNum `_uniq ([0-9]+)\)",
        canonical_fvar,
        value,
    )
    value = re.sub(
        r"\(Lean\.Name\.mkNum `a\._@\._internal\._hyg [0-9]+\)",
        "(Lean.Name.mkNum `a._@._internal._hyg 0)",
        value,
    )
    return value


def type_hash(value: str) -> str:
    return hashlib.sha256(normalized_type(value).encode("utf-8")).hexdigest()


def resolve_text_predicates(
    declarations: list[SourceDeclaration],
    environment: list[dict[str, str]],
    errors: list[str],
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    textual = [
        declaration
        for declaration in declarations
        if declaration.keyword in {"def", "abbrev"} and declaration.prop_codomain
    ]
    environment_names = {row["name"] for row in environment}
    resolved_rows: list[dict[str, object]] = []
    resolved_names: set[str] = set()
    for declaration in textual:
        candidates = [
            row
            for row in environment
            if row["module"] == declaration.module
            and row["declaration_kind"] == declaration.keyword
            and suffix_match(row["user_name"], declaration.name)
        ]
        if len(candidates) != 1:
            errors.append(
                f"text predicate {relative(declaration.path)}:{declaration.line} "
                f"{declaration.name}: expected one environment match, "
                f"measured {len(candidates)}"
            )
            resolved = ""
            env_line = ""
        else:
            resolved = candidates[0]["name"]
            env_line = candidates[0]["range_start_line"]
            resolved_names.add(resolved)
        resolved_rows.append(
            {
                "module": declaration.module,
                "path": relative(declaration.path),
                "line": declaration.line,
                "end_line": declaration.end_line,
                "keyword": declaration.keyword,
                "raw_name": declaration.name,
                "resolved_name": resolved,
                "environment_range_start_line": env_line,
                "declared_codomain": declaration.codomain,
                "header": declaration.header,
            }
        )

    diff_rows: list[dict[str, object]] = []
    for name in sorted(environment_names - resolved_names):
        diff_rows.append(
            {"side": "ENVIRONMENT_ONLY", "name": name, "detail": "absent text match"}
        )
    for name in sorted(resolved_names - environment_names):
        diff_rows.append(
            {"side": "TEXT_ONLY", "name": name, "detail": "absent environment row"}
        )
    if diff_rows:
        errors.append(
            "environment/text predicate-set mismatch: "
            + ", ".join(f"{row['side']}:{row['name']}" for row in diff_rows)
        )
    return resolved_rows, diff_rows


def source_backed(row: dict[str, str]) -> bool:
    try:
        return int(row["range_start_line"]) > 0
    except (KeyError, ValueError):
        return False


def enumerate_roles(
    predicates: list[dict[str, str]],
    roles: list[dict[str, str]],
    prop_binders: list[dict[str, str]],
) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, str]]:
    predicate_names = {row["name"] for row in predicates}
    predicate_short = {row["name"]: row["user_name"].split(".")[-1] for row in predicates}
    binders_by_declaration: dict[str, list[dict[str, str]]] = defaultdict(list)
    for binder in prop_binders:
        if source_backed(binder):
            binders_by_declaration[binder["name"]].append(binder)

    producer_rows: list[dict[str, object]] = []
    for role in roles:
        target = role["final_head"]
        if target not in predicate_names or not source_backed(role):
            continue
        prerequisites = sorted(
            {
                dependency
                for binder in binders_by_declaration.get(role["name"], [])
                for dependency in split_names(binder["domain_dependencies"])
                if dependency in predicate_names
            }
        )
        producer_rows.append(
            {
                "predicate": target,
                "predicate_user_name": predicate_short[target],
                "producer": role["name"],
                "producer_user_name": role["user_name"],
                "producer_kind": role["kind"],
                "module": role["module"],
                "range_start_line": role["range_start_line"],
                "range_end_line": role["range_end_line"],
                "candidate_prerequisites": ",".join(prerequisites),
                "fixed_point_usable": "",
            }
        )

    consumer_rows: list[dict[str, object]] = []
    seen_consumers: set[tuple[str, str, str, str]] = set()
    for binder in prop_binders:
        if not source_backed(binder):
            continue
        dependencies = split_names(binder["domain_dependencies"])
        for predicate in sorted(predicate_names & dependencies):
            key = (predicate, binder["name"], "PROP_BINDER", binder["binder_index"])
            if key in seen_consumers:
                continue
            seen_consumers.add(key)
            consumer_rows.append(
                {
                    "predicate": predicate,
                    "predicate_user_name": predicate_short[predicate],
                    "consumer": binder["name"],
                    "consumer_user_name": binder["user_name"],
                    "consumer_kind": binder["kind"],
                    "module": binder["module"],
                    "range_start_line": binder["range_start_line"],
                    "range_end_line": binder["range_end_line"],
                    "consumer_mode": "PROP_BINDER",
                    "binder_index": binder["binder_index"],
                    "binder_name": binder["binder_name"],
                    "binder_type": binder["domain_type"],
                }
            )

    # A Prop definition can itself package another candidate as a premise.
    # This dependency is semantically a consumer even though it is invisible
    # in the definition's own telescope.
    for role in roles:
        if role["kind"] != "definition" or not source_backed(role):
            continue
        dependencies = split_names(role["value_dependencies"])
        for predicate in sorted(predicate_names & dependencies):
            if role["name"] == predicate:
                continue
            if any(
                row["predicate"] == predicate and row["consumer"] == role["name"]
                for row in consumer_rows
            ):
                continue
            key = (predicate, role["name"], "DEFINITION_BODY", "")
            if key in seen_consumers:
                continue
            seen_consumers.add(key)
            consumer_rows.append(
                {
                    "predicate": predicate,
                    "predicate_user_name": predicate_short[predicate],
                    "consumer": role["name"],
                    "consumer_user_name": role["user_name"],
                    "consumer_kind": role["kind"],
                    "module": role["module"],
                    "range_start_line": role["range_start_line"],
                    "range_end_line": role["range_end_line"],
                    "consumer_mode": "DEFINITION_BODY",
                    "binder_index": "",
                    "binder_name": "",
                    "binder_type": "",
                }
            )

    proved: set[str] = set()
    changed = True
    while changed:
        changed = False
        for producer in producer_rows:
            prerequisites = split_names(str(producer["candidate_prerequisites"]))
            predicate = str(producer["predicate"])
            if prerequisites <= proved and predicate not in proved:
                proved.add(predicate)
                changed = True
    for producer in producer_rows:
        prerequisites = split_names(str(producer["candidate_prerequisites"]))
        producer["fixed_point_usable"] = str(prerequisites <= proved).lower()

    consumed = {str(row["predicate"]) for row in consumer_rows}
    statuses = {
        name: (
            "PROVED"
            if name in proved
            else "CONSUMED-ONLY"
            if name in consumed
            else "DEAD"
        )
        for name in predicate_names
    }
    return (
        sorted(
            producer_rows,
            key=lambda row: (str(row["predicate"]), str(row["producer"])),
        ),
        sorted(
            consumer_rows,
            key=lambda row: (
                str(row["predicate"]),
                str(row["consumer"]),
                str(row["consumer_mode"]),
                str(row["binder_index"]),
            ),
        ),
        statuses,
    )


def correspondence_names(errors: list[str]) -> set[str]:
    if not CORRESPONDENCE.is_file():
        errors.append(f"missing required input: {relative(CORRESPONDENCE)}")
        return set()
    rows = read_tsv(CORRESPONDENCE)
    if len(rows) != 467:
        errors.append(
            f"correspondence coverage mismatch: expected 467 rows, measured {len(rows)}"
        )
    names = {row.get("declaration", "") for row in rows if row.get("declaration")}
    if len(names) != 467:
        errors.append(
            f"correspondence declaration cells not unique: rows=467 names={len(names)}"
        )
    return names


def name_in_set(full_name: str, names: set[str]) -> bool:
    return any(suffix_match(full_name, name) for name in names)


def exact_identifier_mention(text: str, full_name: str, user_name: str) -> bool:
    candidates = {full_name, user_name, user_name.split(".")[-1]}
    return any(
        re.search(rf"(?<![\w.]){re.escape(candidate)}(?![\w.])", text)
        for candidate in candidates
    )


def load_axiom_clean_witnesses(errors: list[str]) -> dict[str, dict[str, str]]:
    witnesses: dict[str, dict[str, str]] = {}
    found_any = False
    for path in (LOGS / "v7_witness_axioms.tsv", LOGS / "v10_witness_axioms.tsv"):
        if not path.is_file():
            continue
        found_any = True
        for row in read_tsv(path):
            name = row.get("name", "")
            if not name:
                errors.append(f"{relative(path)} has witness row without name")
                continue
            axioms = split_names(row.get("axioms", ""))
            if not axioms <= ALLOWED_AXIOMS:
                errors.append(
                    f"witness {name} has forbidden axioms "
                    f"{sorted(axioms - ALLOWED_AXIOMS)}"
                )
            witnesses[name] = row
    if not found_any:
        errors.append("no V7/V10 witness axiom evidence found")
    return witnesses


def validate_curation(
    predicates: list[dict[str, str]],
    statuses: dict[str, str],
    producers: list[dict[str, object]],
    consumers: list[dict[str, object]],
    correspondence: set[str],
    errors: list[str],
) -> tuple[list[dict[str, object]], dict[str, dict[str, str]]]:
    if not ADJUDICATION.is_file():
        errors.append(
            f"missing review curation: {relative(ADJUDICATION)}; expected exact header "
            + "\\t".join(ADJUDICATION_HEADER)
        )
        return [], {}
    rows = read_tsv(ADJUDICATION, ADJUDICATION_HEADER)
    short_counts = Counter(row["user_name"].split(".")[-1] for row in predicates)
    duplicate_shorts = sorted(name for name, count in short_counts.items() if count > 1)
    if duplicate_shorts:
        errors.append(
            "predicate short names are not unique: " + ",".join(duplicate_shorts)
        )
    by_short = {
        row["user_name"].split(".")[-1]: row["name"]
        for row in predicates
        if short_counts[row["user_name"].split(".")[-1]] == 1
    }
    by_full = {row["name"]: row["name"] for row in predicates}
    resolved: dict[str, dict[str, str]] = {}
    for line, row in enumerate(rows, start=2):
        if any(not row[field].strip() for field in ADJUDICATION_HEADER):
            errors.append(f"{relative(ADJUDICATION)}:{line}: blank curation field")
            continue
        raw = row["predicate"]
        name = by_full.get(raw) or by_short.get(raw)
        if name is None:
            errors.append(
                f"{relative(ADJUDICATION)}:{line}: unknown predicate {raw!r}"
            )
            continue
        if name in resolved:
            errors.append(
                f"{relative(ADJUDICATION)}:{line}: duplicate predicate {raw!r}"
            )
            continue
        resolved[name] = row
    expected_names = set(statuses)
    if set(resolved) != expected_names:
        errors.append(
            "curation candidate coverage mismatch: missing="
            + ",".join(sorted(expected_names - set(resolved)))
            + " extra="
            + ",".join(sorted(set(resolved) - expected_names))
        )

    producers_by_predicate: dict[str, list[str]] = defaultdict(list)
    usable_producers_by_predicate: dict[str, list[str]] = defaultdict(list)
    for row in producers:
        producers_by_predicate[str(row["predicate"])].append(str(row["producer"]))
        if row["fixed_point_usable"] == "true":
            usable_producers_by_predicate[str(row["predicate"])].append(
                str(row["producer"])
            )
    consumers_by_predicate: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in consumers:
        consumers_by_predicate[str(row["predicate"])].append(row)
    witnesses = load_axiom_clean_witnesses(errors)
    readme_text = SOURCE_README.read_text(encoding="utf-8")
    appendix_text = APPENDIX_SUMMARY.read_text(encoding="utf-8")

    output: list[dict[str, object]] = []
    for predicate in sorted(expected_names):
        env = next(row for row in predicates if row["name"] == predicate)
        row = resolved.get(predicate)
        if row is None:
            continue
        status = statuses[predicate]
        if row["source_status"] not in SOURCE_STATUSES:
            errors.append(
                f"{predicate}: invalid curated source_status {row['source_status']!r}"
            )
        if row["source_status"] != status:
            errors.append(
                f"{predicate}: curated status {row['source_status']} != measured {status}"
            )
        semantic = row["semantic_class"]
        publication = row["publication"]
        if semantic not in SEMANTIC_CLASSES:
            errors.append(f"{predicate}: invalid semantic_class {semantic!r}")
        if publication not in PUBLICATION_CLASSES:
            errors.append(f"{predicate}: invalid publication {publication!r}")
        expected_semantics = {
            "PROVED": {"SOURCE_DISCHARGED"},
            "CONSUMED-ONLY": {
                "ORDINARY_MODEL_CONDITION",
                "DISCLOSED_CONDITIONAL_INFRASTRUCTURE",
            },
            "DEAD": {"DEAD_CODE"},
        }[status]
        if semantic not in expected_semantics:
            errors.append(
                f"{predicate}: semantic_class {semantic} incompatible with {status}"
            )

        predicate_consumers = consumers_by_predicate[predicate]
        published_consumers = sorted(
            {
                str(consumer["consumer"])
                for consumer in predicate_consumers
                if name_in_set(str(consumer["consumer_user_name"]), correspondence)
            }
        )
        claimed_consumers = sorted(
            {
                str(consumer["consumer"])
                for consumer in predicate_consumers
                if exact_identifier_mention(
                    readme_text,
                    str(consumer["consumer"]),
                    str(consumer["consumer_user_name"]),
                )
                or exact_identifier_mention(
                    appendix_text,
                    str(consumer["consumer"]),
                    str(consumer["consumer_user_name"]),
                )
            }
        )
        if publication == "PUBLISHED_EXPLICIT_HYPOTHESIS" and not (
            published_consumers or claimed_consumers
        ):
            errors.append(
                f"{predicate}: curated as published explicit hypothesis but no "
                "consumer is in the correspondence table or claims ledgers"
            )
        if publication in {"UNPUBLISHED_INFRASTRUCTURE", "UNPUBLISHED_DEAD"} and (
            published_consumers or claimed_consumers
        ):
            errors.append(
                f"{predicate}: curated unpublished but machine publication scan found "
                + ",".join(sorted(set(published_consumers + claimed_consumers)))
            )

        expected_evidence = [
            item.strip()
            for item in row["expected_producer_or_witness"].split(",")
            if item.strip() and item.strip() != "-"
        ]
        evidence_hits: list[str] = []
        if semantic == "SOURCE_DISCHARGED":
            for expected in expected_evidence:
                matching = [
                    name
                    for name in usable_producers_by_predicate[predicate]
                    if suffix_match(name, expected)
                ]
                if not matching:
                    errors.append(
                        f"{predicate}: expected fixed-point-usable producer "
                        f"{expected!r} not measured"
                    )
                evidence_hits.extend(matching)
            if not expected_evidence:
                errors.append(f"{predicate}: no expected producer curated")
        elif semantic == "ORDINARY_MODEL_CONDITION":
            for expected in expected_evidence:
                matching = [
                    name for name in witnesses if suffix_match(name, expected)
                ]
                if not matching:
                    errors.append(
                        f"{predicate}: expected compiled witness {expected!r} not found"
                    )
                    continue
                for name in matching:
                    dependencies = split_names(
                        witnesses[name].get("type_dependencies", "")
                    )
                    if predicate not in dependencies:
                        errors.append(
                            f"{predicate}: witness {name} type does not depend on predicate"
                        )
                    evidence_hits.append(name)
            if not expected_evidence:
                errors.append(f"{predicate}: no model witness curated")
        elif expected_evidence:
            errors.append(
                f"{predicate}: {semantic} must use '-' for "
                "expected_producer_or_witness"
            )

        if semantic == "DISCLOSED_CONDITIONAL_INFRASTRUCTURE":
            if row["disclosure"] == "NOT_APPLICABLE":
                errors.append(f"{predicate}: conditional infrastructure lacks disclosure")
            if row["ledger"] == "NOT_APPLICABLE":
                errors.append(f"{predicate}: conditional infrastructure lacks ledger")
            required_markers = (
                "Appendix_RosenthalPinelis.lean",
                "SOURCE_STATEMENT_ISSUES",
                "APPENDIX_SUMMARY",
                "UP-007",
            )
            joined = row["disclosure"] + " " + row["ledger"]
            missing_markers = [
                marker for marker in required_markers if marker not in joined
            ]
            if missing_markers:
                errors.append(
                    f"{predicate}: disclosure/ledger curation misses "
                    + ",".join(missing_markers)
                )
            if not row["adjudication"].startswith("INFO:"):
                errors.append(
                    f"{predicate}: expected INFO adjudication for honest "
                    f"conditional infrastructure, got {row['adjudication']!r}"
                )

        output.append(
            {
                "predicate": predicate,
                "predicate_user_name": env["user_name"],
                "source_status": status,
                "semantic_class": semantic,
                "publication_class": publication,
                "producer_count": len(producers_by_predicate[predicate]),
                "consumer_count": len(predicate_consumers),
                "correspondence_consumer_count": len(published_consumers),
                "claim_mentioned_consumer_count": len(claimed_consumers),
                "correspondence_consumers": ",".join(published_consumers),
                "claim_mentioned_consumers": ",".join(claimed_consumers),
                "expected_producer_or_witness": row[
                    "expected_producer_or_witness"
                ],
                "validated_evidence": ",".join(sorted(set(evidence_hits))),
                "disclosure": row["disclosure"],
                "ledger": row["ledger"],
                "adjudication": row["adjudication"],
                "curation_status": "REVIEWED",
            }
        )
    return output, resolved


def route_inline_binder(
    binder: dict[str, str],
    candidate_dependencies: list[str],
    statuses: dict[str, str],
    in_correspondence: bool,
    has_manual_curation: bool,
) -> tuple[str, str, str]:
    """Apply the production fail-closed routing rule to one Prop binder."""

    direct_candidate_application = (
        bool(binder["domain_head"])
        and binder["domain_head"] in candidate_dependencies
    )
    if direct_candidate_application:
        return (
            "NAMED_PROJECT_PREDICATE",
            "RECONCILED_BY_CANDIDATE_CURATION",
            ",".join(
                f"{name}:{statuses[name]}" for name in candidate_dependencies
            ),
        )
    if in_correspondence:
        return (
            "PUBLISHED_ENDPOINT_INLINE_PREMISE",
            "COVERED_BY_V6_CORRESPONDENCE_REVIEW",
            "v6_endpoint_telescopes.tsv + V6 Tier-B review",
        )
    if binder["binder_info"] == "instanceImplicit":
        return (
            "INSTANCE_MEDIATED_PREMISE",
            "ENUMERATED_TYPECLASS_LIMITATION",
            "v10_instance_binders.tsv",
        )

    category = (
        "COMPOUND_PROJECT_PREDICATE_PREMISE"
        if candidate_dependencies
        else (
            "EXTERNAL_OR_LOCAL_NAMED_PREDICATE"
            if binder["domain_head"]
            else "ANONYMOUS_INLINE_PREMISE"
        )
    )
    if has_manual_curation:
        return category, "MANUALLY_ADJUDICATED", ""
    # Externally headed formulae such as equalities, inequalities,
    # measurability, or integrability assumptions are deliberately included:
    # a difficult principle can have any of those shapes.
    return (
        category,
        "REVIEW_TIER_REQUIRED",
        "complete machine inventory; semantic review required",
    )


def inline_inventory(
    prop_binders: list[dict[str, str]],
    predicate_names: set[str],
    statuses: dict[str, str],
    correspondence: set[str],
    errors: list[str],
) -> tuple[list[dict[str, object]], list[dict[str, object]], list[dict[str, object]]]:
    manual: dict[str, dict[str, str]] = {}
    if INLINE_ADJUDICATION.is_file():
        rows = read_tsv(INLINE_ADJUDICATION, INLINE_ADJUDICATION_HEADER)
        for line, row in enumerate(rows, start=2):
            if any(not row[field].strip() for field in INLINE_ADJUDICATION_HEADER):
                errors.append(
                    f"{relative(INLINE_ADJUDICATION)}:{line}: blank field"
                )
                continue
            adjudication = row["adjudication"]
            if adjudication not in (
                INLINE_CLEAN_ADJUDICATIONS | INLINE_FINDING_ADJUDICATIONS
            ):
                errors.append(
                    f"{relative(INLINE_ADJUDICATION)}:{line}: invalid "
                    f"adjudication {adjudication!r}"
                )
            if adjudication in INLINE_FINDING_ADJUDICATIONS:
                errors.append(
                    f"{relative(INLINE_ADJUDICATION)}:{line}: review found "
                    f"{adjudication}; report and disposition required"
                )
            for field in ("evidence", "reviewer_note"):
                value = row[field].strip()
                if len(value) < 20 or value.upper() in {
                    "-",
                    "N/A",
                    "NA",
                    "TBD",
                    "TODO",
                    "UNKNOWN",
                    "PLACEHOLDER",
                }:
                    errors.append(
                        f"{relative(INLINE_ADJUDICATION)}:{line}: "
                        f"non-substantive {field}"
                    )
            digest = row["type_hash"]
            if digest in manual:
                errors.append(
                    f"{relative(INLINE_ADJUDICATION)}:{line}: duplicate hash {digest}"
                )
            manual[digest] = row

    output: list[dict[str, object]] = []
    groups: dict[str, dict[str, object]] = {}
    used_manual: set[str] = set()
    for binder in prop_binders:
        if not source_backed(binder):
            continue
        normalized = normalized_type(binder["domain_type"])
        digest = type_hash(normalized)
        dependencies = split_names(binder["domain_dependencies"])
        candidate_dependencies = sorted(predicate_names & dependencies)
        in_correspondence = name_in_set(binder["user_name"], correspondence)
        category, review_state, evidence = route_inline_binder(
            binder,
            candidate_dependencies,
            statuses,
            in_correspondence,
            digest in manual,
        )
        if review_state == "MANUALLY_ADJUDICATED":
            used_manual.add(digest)
            evidence = (
                manual[digest]["adjudication"]
                + ": "
                + manual[digest]["evidence"]
            )

        row = {
            **binder,
            "normalized_type": normalized,
            "type_hash": digest,
            "candidate_dependencies": ",".join(candidate_dependencies),
            "candidate_dependency_statuses": ",".join(
                f"{name}:{statuses[name]}" for name in candidate_dependencies
            ),
            "in_correspondence_table": str(in_correspondence).lower(),
            "inline_category": category,
            "review_state": review_state,
            "review_evidence": evidence,
        }
        output.append(row)
        group = groups.setdefault(
            digest,
            {
                "type_hash": digest,
                "normalized_type": normalized,
                "occurrence_count": 0,
                "declaration_count": 0,
                "declarations": set(),
                "categories": set(),
                "review_states": set(),
            },
        )
        if group["normalized_type"] != normalized:
            errors.append(
                f"SHA-256 collision in inline type inventory for digest {digest}"
            )
        group["occurrence_count"] = int(group["occurrence_count"]) + 1
        cast_declarations = group["declarations"]
        cast_categories = group["categories"]
        cast_review_states = group["review_states"]
        assert isinstance(cast_declarations, set)
        assert isinstance(cast_categories, set)
        assert isinstance(cast_review_states, set)
        cast_declarations.add(binder["name"])
        cast_categories.add(category)
        cast_review_states.add(review_state)

    group_rows: list[dict[str, object]] = []
    for digest, group in sorted(groups.items()):
        declarations = group["declarations"]
        categories = group["categories"]
        review_states = group["review_states"]
        assert isinstance(declarations, set)
        assert isinstance(categories, set)
        assert isinstance(review_states, set)
        group_rows.append(
            {
                "type_hash": digest,
                "occurrence_count": group["occurrence_count"],
                "declaration_count": len(declarations),
                "categories": ",".join(sorted(categories)),
                "review_states": ",".join(sorted(review_states)),
                "declarations": ",".join(sorted(declarations)),
                "normalized_type": group["normalized_type"],
            }
        )

    queue = [
        row
        for row in group_rows
        if "REVIEW_TIER_REQUIRED" in str(row["review_states"]).split(",")
    ]
    unused_manual = set(manual) - used_manual
    if unused_manual:
        errors.append(
            "stale inline curation hashes: " + ",".join(sorted(unused_manual))
        )
    if any(not row["review_state"] for row in output):
        errors.append("inline inventory contains silently unclassified rows")
    return output, group_rows, queue


def typeclass_inventory(
    instance_binders: list[dict[str, str]],
    prop_fields: list[dict[str, str]],
    errors: list[str],
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    rows: list[dict[str, object]] = []
    for binder in instance_binders:
        normalized = normalized_type(binder["domain_type"])
        rows.append(
            {
                **binder,
                "normalized_type": normalized,
                "type_hash": type_hash(normalized),
                "project_defined_head": str(
                    binder["domain_head"].startswith("MatrixConcentration")
                ).lower(),
                "coverage": "ENUMERATED_NOT_SEMANTICALLY_INSTANTIATED",
            }
        )
    field_rows: list[dict[str, object]] = []
    for field in prop_fields:
        field_rows.append(
            {
                **field,
                "coverage": "REQUIRES_CANDIDATE_STYLE_ADJUDICATION",
            }
        )
    if field_rows:
        errors.append(
            f"measured {len(field_rows)} project structure/class Prop fields; "
            "no field-level adjudication rows exist"
        )
    return rows, field_rows


def calibration_checks(
    declarations: list[SourceDeclaration],
    statuses: dict[str, str],
    consumers: list[dict[str, object]],
    errors: list[str],
) -> list[dict[str, object]]:
    checks: list[dict[str, object]] = []
    plant_compile_clean = False

    measured_consumers: dict[str, set[tuple[str, str]]] = defaultdict(set)
    for row in consumers:
        measured_consumers[str(row["predicate"])].add(
            (str(row["consumer"]), str(row["consumer_mode"]))
        )
    for predicate in sorted(KNOWN_CONDITIONALS):
        observed = measured_consumers.get(predicate, set())
        expected = EXPECTED_KNOWN_CONSUMERS[predicate]
        passed = statuses.get(predicate) == "CONSUMED-ONLY" and observed == expected
        checks.append(
            {
                "calibration": "KNOWN_CONDITIONAL",
                "subject": predicate,
                "expected": "CONSUMED-ONLY;"
                + ",".join(f"{name}[{mode}]" for name, mode in sorted(expected)),
                "observed": str(statuses.get(predicate, "MISSING"))
                + ";"
                + ",".join(f"{name}[{mode}]" for name, mode in sorted(observed)),
                "pass": str(passed).lower(),
            }
        )
        if not passed:
            errors.append(f"known-positive calibration failed for {predicate}")

    if not PLANT.is_file():
        errors.append(f"missing conditional calibration plant: {relative(PLANT)}")
        checks.append(
            {
                "calibration": "PLANTED_PAIR",
                "subject": "FakePrinciple/fake_result",
                "expected": "def FakePrinciple : Prop consumed by fake_result",
                "observed": "plant missing",
                "pass": "false",
            }
        )
    else:
        plant_declarations = parse_source_declarations([PLANT])
        fake_predicates = [
            declaration
            for declaration in plant_declarations
            if declaration.keyword in {"def", "abbrev"}
            and declaration.prop_codomain
            and declaration.name == "FakePrinciple"
        ]
        fake_consumers = [
            declaration
            for declaration in plant_declarations
            if declaration.keyword in {"theorem", "lemma"}
            and declaration.name == "fake_result"
            and re.search(
                r"(?<![\w.])FakePrinciple(?![\w.])", declaration.header
            )
        ]
        compile_log_present = (
            PLANT_COMPILE_LOG.is_file()
            and PLANT_COMPILE_LOG.stat().st_size > 0
        )
        compile_log = (
            PLANT_COMPILE_LOG.read_text(encoding="utf-8", errors="replace")
            if compile_log_present
            else ""
        )
        plant_compile_clean = bool(compile_log_present) and (
            re.findall(
                r"^LEAN_EXIT_STATUS ([0-9]+)$",
                compile_log,
                re.MULTILINE,
            )
            == ["0"]
        ) and not re.search(
            r"\berror:|declaration uses ['\"]?sorry",
            compile_log,
            re.IGNORECASE,
        )
        passed = (
            len(fake_predicates) == 1
            and len(fake_consumers) == 1
            and plant_compile_clean
        )
        checks.append(
            {
                "calibration": "PLANTED_PAIR",
                "subject": "FakePrinciple/fake_result",
                "expected": "one Prop def; one theorem consumer; compiled without error/sorry",
                "observed": (
                    f"predicates={len(fake_predicates)};"
                    f"consumers={len(fake_consumers)};"
                    f"compile_log_present={str(compile_log_present).lower()};"
                    f"compile_clean={str(plant_compile_clean).lower()}"
                ),
                "pass": str(passed).lower(),
            }
        )
        if not passed:
            errors.append("planted FakePrinciple/fake_result calibration failed")

    routing_expected = {
        "fake_result": (
            "NAMED_PROJECT_PREDICATE",
            "RECONCILED_BY_CANDIDATE_CURATION",
        ),
        "fake_external_head_result": (
            "EXTERNAL_OR_LOCAL_NAMED_PREDICATE",
            "REVIEW_TIER_REQUIRED",
        ),
        "fake_compound_result": (
            "COMPOUND_PROJECT_PREDICATE_PREMISE",
            "REVIEW_TIER_REQUIRED",
        ),
    }
    routing_observed: dict[str, tuple[str, str]] = {}
    if INLINE_PLANT_BINDERS.is_file():
        for row in read_tsv(
            INLINE_PLANT_BINDERS,
            [
                "name",
                "binder_index",
                "binder_name",
                "binder_info",
                "domain_head",
                "domain_dependencies",
                "domain_type",
            ],
        ):
            dependencies = split_names(row["domain_dependencies"])
            candidate_dependencies = sorted({"FakePrinciple"} & dependencies)
            category, review_state, _ = route_inline_binder(
                row,
                candidate_dependencies,
                {"FakePrinciple": "CONSUMED-ONLY"},
                False,
                False,
            )
            routing_observed[row["name"]] = (category, review_state)
    routing_passed = (
        plant_compile_clean
        and routing_observed == routing_expected
    )
    checks.append(
        {
            "calibration": "INLINE_ROUTING",
            "subject": "direct candidate / external head / compound candidate",
            "expected": ";".join(
                f"{name}={category}/{state}"
                for name, (category, state) in routing_expected.items()
            ),
            "observed": ";".join(
                f"{name}={category}/{state}"
                for name, (category, state) in sorted(routing_observed.items())
            )
            or "binder calibration output missing",
            "pass": str(routing_passed).lower(),
        }
    )
    if not routing_passed:
        errors.append(
            "inline routing calibration failed for direct, external-headed, "
            "or compound premise"
        )

    # ``declarations`` is intentionally referenced here: a zero-sized shared
    # universe would otherwise let the plant alone make calibration look live.
    if not declarations:
        errors.append("shared FILE-WALK source declaration inventory is empty")
    return checks


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    errors: list[str] = []
    for path in (
        ENV_PREDICATES,
        ENV_FIELDS,
        ENV_CONSTANTS,
        ENV_STRUCTURES,
        ENV_ROLES,
        ENV_PROP_BINDERS,
        ENV_INSTANCE_BINDERS,
        ENV_MODULES,
        ENV_SUMMARY,
        ENV_COMPILE_LOG,
        AXIOM_AUDIT,
        AXIOM_SUMMARY,
        AXIOM_MODULES,
        AXIOM_CALIBRATION,
        SOURCE_README,
        APPENDIX_SUMMARY,
        PLANT_COMPILE_LOG,
        WITNESS_COMPILE_LOG,
    ):
        require_file(path, errors)
    if errors:
        (LOGS / "v10_summary.txt").write_text(
            "V10 CONDITIONAL-INTERFACE CENSUS\n"
            + "\n".join(f"ERROR {error}" for error in errors)
            + "\nVERDICT FAIL\n",
            encoding="utf-8",
        )
        print("\n".join(errors), file=sys.stderr)
        return 1

    validate_lean_compile_log(
        ENV_COMPILE_LOG,
        "V10 environment census",
        errors,
    )
    validate_lean_compile_log(
        WITNESS_COMPILE_LOG,
        "V10 concrete witness",
        errors,
    )

    predicates = read_tsv(
        ENV_PREDICATES,
        [
            "module",
            "name",
            "user_name",
            "declaration_kind",
            "reducibility_hint",
            "range_start_line",
            "range_end_line",
            "type",
        ],
    )
    prop_fields = read_tsv(
        ENV_FIELDS,
        [
            "module",
            "structure",
            "structure_is_class",
            "field",
            "field_user_name",
            "prop_mode",
            "range_start_line",
            "range_end_line",
            "type",
        ],
    )
    environment_constants = read_tsv(
        ENV_CONSTANTS,
        ["module", "name", "kind"],
    )
    environment_structures = read_tsv(
        ENV_STRUCTURES,
        ["module", "structure", "structure_is_class"],
    )
    roles = read_tsv(
        ENV_ROLES,
        [
            "module",
            "name",
            "user_name",
            "kind",
            "range_start_line",
            "range_end_line",
            "final_head",
            "final_dependencies",
            "value_dependencies",
        ],
    )
    prop_binders = read_tsv(
        ENV_PROP_BINDERS,
        [
            "module",
            "name",
            "user_name",
            "kind",
            "range_start_line",
            "range_end_line",
            "binder_index",
            "binder_name",
            "binder_info",
            "domain_head",
            "domain_dependencies",
            "domain_type",
        ],
    )
    instance_binders = read_tsv(
        ENV_INSTANCE_BINDERS,
        [
            "module",
            "name",
            "user_name",
            "kind",
            "range_start_line",
            "range_end_line",
            "binder_index",
            "binder_name",
            "domain_head",
            "domain_dependencies",
            "domain_type",
        ],
    )
    environment_modules = [
        line.strip()
        for line in ENV_MODULES.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    environment_metrics = read_environment_summary(ENV_SUMMARY, errors)
    axiom_rows = read_tsv(
        AXIOM_AUDIT,
        ["module", "name", "user_name", "kind", "axioms"],
    )
    axiom_summary = json.loads(AXIOM_SUMMARY.read_text(encoding="utf-8"))
    if not isinstance(axiom_summary, dict):
        raise RuntimeError(f"{relative(AXIOM_SUMMARY)} must contain a JSON object")
    axiom_modules_list = [
        line.strip()
        for line in AXIOM_MODULES.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    axiom_calibration = read_tsv(
        AXIOM_CALIBRATION,
        ["name", "user_name", "axioms"],
    )

    universe = lean_universe()
    if len(universe) != 15:
        errors.append(
            f"FILE-WALK UNIVERSE expected 15 Lean files, measured {len(universe)}"
        )
    environment_coverage = validate_environment_coverage(
        universe,
        environment_modules,
        environment_metrics,
        environment_constants,
        environment_structures,
        axiom_rows,
        axiom_summary,
        axiom_modules_list,
        axiom_calibration,
        predicates,
        prop_fields,
        roles,
        prop_binders,
        instance_binders,
        errors,
    )
    declarations = parse_source_declarations(universe)
    text_predicates, text_diff = resolve_text_predicates(
        declarations, predicates, errors
    )
    producers, consumers, statuses = enumerate_roles(
        predicates, roles, prop_binders
    )
    correspondence = correspondence_names(errors)

    readme_text = SOURCE_README.read_text(encoding="utf-8")
    appendix_text = APPENDIX_SUMMARY.read_text(encoding="utf-8")
    consumers_enriched: list[dict[str, object]] = []
    for consumer in consumers:
        consumers_enriched.append(
            {
                **consumer,
                "in_correspondence_table": str(
                    name_in_set(str(consumer["consumer_user_name"]), correspondence)
                ).lower(),
                "mentioned_in_source_readme": str(
                    exact_identifier_mention(
                        readme_text,
                        str(consumer["consumer"]),
                        str(consumer["consumer_user_name"]),
                    )
                ).lower(),
                "mentioned_in_appendix_summary": str(
                    exact_identifier_mention(
                        appendix_text,
                        str(consumer["consumer"]),
                        str(consumer["consumer_user_name"]),
                    )
                ).lower(),
            }
        )

    reconciliation, curation = validate_curation(
        predicates,
        statuses,
        producers,
        consumers_enriched,
        correspondence,
        errors,
    )
    inline, inline_groups, inline_queue = inline_inventory(
        prop_binders,
        set(statuses),
        statuses,
        correspondence,
        errors,
    )
    inline_review_obligations = [
        row
        for row in inline_groups
        if {
            "MANUALLY_ADJUDICATED",
            "REVIEW_TIER_REQUIRED",
        }
        & set(str(row["review_states"]).split(","))
    ]
    if inline_queue:
        errors.append(
            f"inline review queue is nonempty ({len(inline_queue)} unique "
            f"normalized type hashes); curate every row in "
            f"{relative(INLINE_ADJUDICATION)}"
        )
    typeclasses, prop_field_coverage = typeclass_inventory(
        instance_binders, prop_fields, errors
    )
    calibrations = calibration_checks(
        declarations, statuses, consumers, errors
    )

    producer_fields = [
        "predicate",
        "predicate_user_name",
        "producer",
        "producer_user_name",
        "producer_kind",
        "module",
        "range_start_line",
        "range_end_line",
        "candidate_prerequisites",
        "fixed_point_usable",
    ]
    consumer_fields = [
        "predicate",
        "predicate_user_name",
        "consumer",
        "consumer_user_name",
        "consumer_kind",
        "module",
        "range_start_line",
        "range_end_line",
        "consumer_mode",
        "binder_index",
        "binder_name",
        "binder_type",
        "in_correspondence_table",
        "mentioned_in_source_readme",
        "mentioned_in_appendix_summary",
    ]
    write_tsv(
        LOGS / "v10_text_predicates.tsv",
        [
            "module",
            "path",
            "line",
            "end_line",
            "keyword",
            "raw_name",
            "resolved_name",
            "environment_range_start_line",
            "declared_codomain",
            "header",
        ],
        text_predicates,
    )
    write_tsv(
        LOGS / "v10_environment_text_diff.tsv",
        ["side", "name", "detail"],
        text_diff,
    )
    write_tsv(LOGS / "v10_producers.tsv", producer_fields, producers)
    write_tsv(LOGS / "v10_consumers.tsv", consumer_fields, consumers_enriched)
    write_tsv(
        LOGS / "v10_disclosure_reconciliation.tsv",
        [
            "predicate",
            "predicate_user_name",
            "source_status",
            "semantic_class",
            "publication_class",
            "producer_count",
            "consumer_count",
            "correspondence_consumer_count",
            "claim_mentioned_consumer_count",
            "correspondence_consumers",
            "claim_mentioned_consumers",
            "expected_producer_or_witness",
            "validated_evidence",
            "disclosure",
            "ledger",
            "adjudication",
            "curation_status",
        ],
        reconciliation,
    )
    write_tsv(
        LOGS / "v10_calibration.tsv",
        ["calibration", "subject", "expected", "observed", "pass"],
        calibrations,
    )
    inline_fields = list(prop_binders[0].keys()) if prop_binders else [
        "module",
        "name",
        "user_name",
        "kind",
        "range_start_line",
        "range_end_line",
        "binder_index",
        "binder_name",
        "binder_info",
        "domain_head",
        "domain_dependencies",
        "domain_type",
    ]
    inline_fields += [
        "normalized_type",
        "type_hash",
        "candidate_dependencies",
        "candidate_dependency_statuses",
        "in_correspondence_table",
        "inline_category",
        "review_state",
        "review_evidence",
    ]
    write_tsv(LOGS / "v10_inline_assumptions.tsv", inline_fields, inline)
    write_tsv(
        LOGS / "v10_inline_type_groups.tsv",
        [
            "type_hash",
            "occurrence_count",
            "declaration_count",
            "categories",
            "review_states",
            "declarations",
            "normalized_type",
        ],
        inline_groups,
    )
    write_tsv(
        LOGS / "v10_inline_review_obligations.tsv",
        [
            "type_hash",
            "occurrence_count",
            "declaration_count",
            "categories",
            "review_states",
            "declarations",
            "normalized_type",
        ],
        inline_review_obligations,
    )
    write_tsv(
        LOGS / "v10_inline_review_queue.tsv",
        [
            "type_hash",
            "occurrence_count",
            "declaration_count",
            "categories",
            "review_states",
            "declarations",
            "normalized_type",
        ],
        inline_queue,
    )
    typeclass_fields = list(instance_binders[0].keys()) if instance_binders else [
        "module",
        "name",
        "user_name",
        "kind",
        "range_start_line",
        "range_end_line",
        "binder_index",
        "binder_name",
        "domain_head",
        "domain_dependencies",
        "domain_type",
    ]
    typeclass_fields += [
        "normalized_type",
        "type_hash",
        "project_defined_head",
        "coverage",
    ]
    write_tsv(LOGS / "v10_typeclasses.tsv", typeclass_fields, typeclasses)
    write_tsv(
        LOGS / "v10_prop_field_coverage.tsv",
        [
            "module",
            "structure",
            "structure_is_class",
            "field",
            "field_user_name",
            "prop_mode",
            "range_start_line",
            "range_end_line",
            "type",
            "coverage",
        ],
        prop_field_coverage,
    )

    producers_by_predicate = Counter(str(row["predicate"]) for row in producers)
    consumers_by_predicate = Counter(str(row["predicate"]) for row in consumers)
    status_rows: list[dict[str, object]] = []
    predicate_by_name = {row["name"]: row for row in predicates}
    reconciliation_by_name = {
        str(row["predicate"]): row for row in reconciliation
    }
    for name in sorted(statuses):
        env = predicate_by_name[name]
        review = reconciliation_by_name.get(name, {})
        status_rows.append(
            {
                "predicate": name,
                "predicate_user_name": env["user_name"],
                "module": env["module"],
                "range_start_line": env["range_start_line"],
                "source_status": statuses[name],
                "producer_count": producers_by_predicate[name],
                "consumer_count": consumers_by_predicate[name],
                "semantic_class": review.get("semantic_class", "UNREVIEWED"),
                "publication_class": review.get("publication_class", "UNREVIEWED"),
                "adjudication": review.get("adjudication", "UNREVIEWED"),
                "curation_status": review.get("curation_status", "UNREVIEWED"),
            }
        )
    status_fields = [
        "predicate",
        "predicate_user_name",
        "module",
        "range_start_line",
        "source_status",
        "producer_count",
        "consumer_count",
        "semantic_class",
        "publication_class",
        "adjudication",
        "curation_status",
    ]
    write_tsv(LOGS / "v10_status.tsv", status_fields, status_rows)

    source_status_counts = Counter(statuses.values())
    inline_category_counts = Counter(str(row["inline_category"]) for row in inline)
    inline_review_counts = Counter(str(row["review_state"]) for row in inline)
    typeclass_heads = {str(row["domain_head"]) for row in typeclasses}
    summary = {
        "file_walk_universe": {
            "count": len(universe),
            "files": [relative(path) for path in universe],
            "exclusions": [
                ".lake/**",
                "MatrixConcentration/Verification/**",
                ".audit_work/**",
            ],
        },
        "environment": {
            "project_constant_count": len(environment_constants),
            "structure_count": len(environment_structures),
            "predicate_count": len(predicates),
            "prop_field_count": len(prop_fields),
            "role_count": len(roles),
            "prop_binder_input_count": len(prop_binders),
            "source_backed_prop_binder_count": len(inline),
            "instance_binder_count": len(instance_binders),
        },
        "environment_coverage_guard": environment_coverage,
        "text": {
            "declaration_count": len(declarations),
            "predicate_count": len(text_predicates),
            "environment_text_diff_count": len(text_diff),
        },
        "classification": {
            "status_counts": dict(sorted(source_status_counts.items())),
            "producer_rows": len(producers),
            "consumer_rows": len(consumers),
            "candidate_curation_rows": len(curation),
        },
        "inline_dual": {
            "binder_rows": len(inline),
            "unique_type_hashes": len(inline_groups),
            "category_counts": dict(sorted(inline_category_counts.items())),
            "review_state_counts": dict(sorted(inline_review_counts.items())),
            "manual_review_obligation_unique_type_hashes": len(
                inline_review_obligations
            ),
            "review_queue_unique_type_hashes": len(inline_queue),
            "hash_canonicalization": (
                "collapse whitespace; alpha-renumber every reprStr "
                "(Lean.Name.mkNum `_uniq N) local fvar id by first occurrence; "
                "erase internal hygienic binder counters; retain fully-qualified "
                "generated declaration hashes"
            ),
            "limitation": (
                "machine enumeration and shape triage cannot decide whether an "
                "explicit discharged premise is mathematically meaningful; published "
                "endpoints are linked to V6, direct project-predicate applications "
                "are linked to named curation, and every other non-instance shape "
                "remains visible in "
                "v10_inline_review_queue.tsv unless manually curated"
            ),
        },
        "typeclass": {
            "instance_binder_rows": len(typeclasses),
            "unique_instance_heads": len(typeclass_heads),
            "project_prop_field_rows": len(prop_fields),
            "instance_level_semantic_instantiation_audited": False,
            "limitation": (
                "all instance binders and project Prop fields are enumerated, but "
                "external typeclass instance existence is not semantically proved"
            ),
        },
        "calibration": {
            "rows": len(calibrations),
            "passes": sum(row["pass"] == "true" for row in calibrations),
            "failures": sum(row["pass"] != "true" for row in calibrations),
        },
        "errors": errors,
        "verdict": "PASS" if not errors else "FAIL",
    }
    (LOGS / "v10_status.json").write_text(
        json.dumps(status_rows, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (LOGS / "v10_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    summary_lines = [
        "V10 CONDITIONAL-INTERFACE CENSUS",
        "UNIVERSE_RULE every .lean under project root excluding .lake/**, "
        "MatrixConcentration/Verification/**, .audit_work/**",
        f"FILE_WALK_LEAN_FILES {len(universe)}",
        f"ENVIRONMENT_MODULES {len(environment_modules)}",
        f"ENVIRONMENT_PROJECT_CONSTANTS {len(environment_constants)}",
        f"V4_AXIOM_AUDIT_CONSTANTS {len(axiom_rows)}",
        f"ENVIRONMENT_COVERAGE_GUARD {environment_coverage['verdict']}",
        f"TEXT_DECLARATIONS_PARSED {len(declarations)}",
        f"ENVIRONMENT_PREDICATES {len(predicates)}",
        f"TEXT_PREDICATES {len(text_predicates)}",
        f"ENVIRONMENT_TEXT_DIFF {len(text_diff)}",
        f"PROJECT_PROP_FIELDS {len(prop_fields)}",
        f"SOURCE_PROVED {source_status_counts['PROVED']}",
        f"SOURCE_CONSUMED_ONLY {source_status_counts['CONSUMED-ONLY']}",
        f"SOURCE_DEAD {source_status_counts['DEAD']}",
        f"PRODUCER_ROWS {len(producers)}",
        f"CONSUMER_ROWS {len(consumers)}",
        f"CURATED_CANDIDATES {len(curation)}",
        f"PROP_BINDER_ROWS {len(inline)}",
        f"UNIQUE_PROP_BINDER_TYPE_HASHES {len(inline_groups)}",
        "TYPE_HASH_CANONICALIZATION whitespace collapsed; `_uniq N` local fvar "
        "ids alpha-renumbered by first occurrence; internal hygienic binder "
        "counters erased; fully-qualified generated declaration hashes retained",
        f"MANUAL_REVIEW_OBLIGATION_TYPE_HASHES {len(inline_review_obligations)}",
        f"INLINE_REVIEW_QUEUE_TYPE_HASHES {len(inline_queue)}",
        f"INSTANCE_BINDER_ROWS {len(typeclasses)}",
        f"INSTANCE_UNIQUE_HEADS {len(typeclass_heads)}",
        "INSTANCE_LEVEL_SEMANTIC_INSTANTIATION_AUDITED false",
        f"CALIBRATION_ROWS {len(calibrations)}",
        f"CALIBRATION_FAILURES {summary['calibration']['failures']}",
        f"ERRORS {len(errors)}",
        *(f"ERROR {error}" for error in errors),
        f"VERDICT {'PASS' if not errors else 'FAIL'}",
    ]
    (LOGS / "v10_summary.txt").write_text(
        "\n".join(summary_lines) + "\n", encoding="utf-8"
    )
    (LOGS / "v10_inline_summary.txt").write_text(
        "\n".join(
            [
                "V10 EXHAUSTIVE INLINE PROP-BINDER INVENTORY",
                f"SOURCE_BACKED_BINDERS {len(inline)}",
                f"UNIQUE_NORMALIZED_TYPES {len(inline_groups)}",
                "TYPE_HASH_CANONICALIZATION whitespace collapsed; `_uniq N` "
                "local fvar ids alpha-renumbered by first occurrence; internal "
                "hygienic binder counters erased; fully-qualified generated "
                "declaration hashes retained",
                *(
                    f"CATEGORY_{key} {value}"
                    for key, value in sorted(inline_category_counts.items())
                ),
                *(
                    f"REVIEW_STATE_{key} {value}"
                    for key, value in sorted(inline_review_counts.items())
                ),
                f"MANUAL_REVIEW_OBLIGATION_TYPES {len(inline_review_obligations)}",
                f"REVIEW_QUEUE_UNIQUE_TYPES {len(inline_queue)}",
                "LIMITATION machine shape triage does not establish semantic "
                "satisfiability; V6 supplies review for published endpoints",
                "VERDICT ENUMERATION-PASS",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (LOGS / "v10_typeclass_summary.txt").write_text(
        "\n".join(
            [
                "V10 TYPECLASS-MEDIATED CONDITIONALITY COVERAGE",
                f"INSTANCE_BINDER_ROWS {len(typeclasses)}",
                f"UNIQUE_INSTANCE_HEADS {len(typeclass_heads)}",
                f"PROJECT_DEFINED_INSTANCE_HEAD_ROWS "
                f"{sum(row['project_defined_head'] == 'true' for row in typeclasses)}",
                f"PROJECT_PROP_FIELD_ROWS {len(prop_fields)}",
                "INSTANCE_LEVEL_SEMANTIC_INSTANTIATION_AUDITED false",
                "LIMITATION environment enumeration is exhaustive, but the existence "
                "of external class instances at every use site was not semantically audited",
                f"VERDICT {'PASS-WITH-LIMITATION' if not prop_fields else 'FAIL'}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    print("\n".join(summary_lines))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
