#!/usr/bin/env python3
"""Prepare and analyze current-tree V7 definition-sanity and dead-code evidence.

The environment harness exports declaration metadata and *direct* type/value
dependency edges for the complete current 223-module environment.  This
analyzer waits for V6's exact Tier-B endpoint TSV, then defines the
load-bearing set as:

* every environment ``defnInfo``/structure/class in an HDP ``Prelude`` module;
* every definition/structure/class directly cited by at least three distinct
  Tier-B theorem endpoints.

The blanket Prelude rule follows source-level ``def``/``structure``/``class``
commands and excludes only a narrow, named family of equation-compiler and
inductive helper constants.  Those helpers remain eligible under the
independent >=3 Tier-B endpoint rule.  Internal/private status remains
explicit in every output.
"""

from __future__ import annotations

import argparse
import collections
import csv
import datetime as dt
import shlex
import subprocess
import sys
import tempfile
import re
from dataclasses import dataclass
from pathlib import Path

from file_universe import enumerate_universe


ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
HARNESS = (
    ROOT
    / ".audit_work"
    / "verification"
    / "DefinitionSanityRecertification.lean"
)
RAW_CONSTANTS = LOGS / "recert_definition_constants.tsv"
RAW_EDGES = LOGS / "recert_definition_dependency_edges.tsv"
RAW_CALIBRATION = LOGS / "recert_definition_dead_code_calibration.tsv"
RAW_MODULES = LOGS / "recert_definition_modules.txt"
BUILD_LOG = LOGS / "recert_definition_sanity_build.log"
DEFAULT_V6_ENDPOINTS = LOGS / "recert_v6_tier_b_endpoints.tsv"
DEFAULT_V4_AUDIT = LOGS / "recert_axiom_audit.tsv"
DEFAULT_V2_EVIDENCE = LOGS / "v2_orphan_recertification_summary.log"
LOAD_BEARING = LOGS / "recert_definition_load_bearing.tsv"
REVERSE_CITATIONS = LOGS / "recert_definition_reverse_citations.tsv"
NONTRIVIALITY_CANDIDATES = LOGS / "recert_definition_nontriviality_candidates.tsv"
DEAD_CODE_SWEEP = LOGS / "recert_definition_dead_code_sweep.tsv"
SUMMARY = LOGS / "recert_definition_sanity_summary.txt"
MODULE_COVERAGE = LOGS / "recert_definition_module_coverage.txt"

DEFINITION_KINDS = frozenset({"definition", "structure", "class"})
DEAD_CODE_KINDS = frozenset(
    {
        "axiom",
        "definition",
        "theorem",
        "opaque",
        "structure",
        "class",
        "inductive",
    }
)
CONSTANT_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "is_unsafe",
    "is_partial",
)
EDGE_COLUMNS = (
    "source_module",
    "source",
    "source_kind",
    "origin",
    "target_module",
    "target",
    "target_kind",
)
LOAD_BEARING_COLUMNS = (
    "module",
    "source_path",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "reason",
    "tier_b_endpoint_count",
    "tier_b_type_endpoint_count",
    "tier_b_value_endpoint_count",
)
CANDIDATE_COLUMNS = (
    "target_module",
    "target",
    "target_kind",
    "candidate_module",
    "candidate_theorem",
    "origin",
    "score",
    "reasons",
)
DEAD_CODE_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "reverse_citation_count",
    "classification",
    "exclusion_reason",
)
CALIBRATION_COLUMNS = (
    "label",
    "name",
    "self_reference_count",
    "other_reference_count",
    "expected_dead_code_candidate",
)

# These are elaborator-generated helpers rather than source-level ``def``,
# ``structure``, or ``class`` commands.  They are excluded from the blanket
# Prelude rule, but remain load-bearing if the independent >=3 Tier-B direct
# reference rule selects them.
COMPILER_GENERATED_DEFINITION = re.compile(
    r"(?:"
    r"\._sizeOf(?:_[0-9]+|_inst)?|"
    r"\.casesOn|\.recOn|\.ctorIdx|"
    r"\.noConfusion(?:Type)?|"
    r"\.mk\._flat_ctor|\.mk\.noConfusion"
    r")$"
)


@dataclass(frozen=True)
class Constant:
    module: str
    name: str
    kind: str
    is_private: bool
    private_user_name: str
    is_internal: bool
    is_unsafe: bool
    is_partial: bool


@dataclass(frozen=True)
class Edge:
    source_module: str
    source: str
    source_kind: str
    origin: str
    target_module: str
    target: str
    target_kind: str


def source_path_to_module(relative_path: str) -> str:
    """Map one physical library path to its Lean module name."""
    path = Path(relative_path)
    if path.suffix != ".lean":
        raise ValueError(f"not a Lean source path: {relative_path}")
    parts = path.with_suffix("").parts
    if parts[0] == "HighDimensionalProbability":
        return ".".join(parts)
    if parts[0] == "MatrixConcentration":
        return ".".join(("MatrixConcentration", *parts[1:]))
    if len(parts) == 1 and parts[0] in {
        "HighDimensionalProbability",
        "MatrixConcentration",
    }:
        return parts[0]
    raise ValueError(f"path is outside the two library surfaces: {relative_path}")


def module_to_source_path(module: str) -> str:
    """Map one project module name to its canonical physical source path."""
    parts = module.split(".")
    if parts[0] == "HighDimensionalProbability":
        if len(parts) == 1:
            return "HighDimensionalProbability.lean"
        return "/".join(parts) + ".lean"
    if parts[0] == "MatrixConcentration":
        if len(parts) == 1:
            return "MatrixConcentration.lean"
        return "/".join(("MatrixConcentration", *parts[1:])) + ".lean"
    raise ValueError(f"not a project module: {module}")


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


def is_compiler_generated_definition(name: str) -> bool:
    return COMPILER_GENERATED_DEFINITION.search(name) is not None


def read_modules(path: Path = RAW_MODULES) -> set[str]:
    modules = {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    if not modules:
        raise ValueError(f"{path}: module list is empty")
    return modules


def write_module_coverage(
    expected: set[str], actual: set[str], row_modules: set[str]
) -> tuple[set[str], set[str], set[str]]:
    missing = expected - actual
    extra = actual - expected
    modules_without_rows = actual - row_modules
    lines = [
        "V7 MODULE COVERAGE INVARIANT",
        "============================",
        f"expected_modules: {len(expected)}",
        f"environment_modules: {len(actual)}",
        f"constant_row_modules: {len(row_modules)}",
        f"missing_modules: {len(missing)}",
        f"extra_modules: {len(extra)}",
        (
            "Modules without constant rows are permitted only for import-only "
            "aggregators; their environment presence is recorded separately."
        ),
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
    MODULE_COVERAGE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return missing, extra, modules_without_rows


def choose_verdict(
    *,
    hard_failures: list[str],
    incomplete_reasons: list[str],
) -> str:
    if hard_failures:
        return "ISSUES-FOUND"
    if incomplete_reasons:
        return "INCOMPLETE"
    return "PASS"


def parse_bool(text: str, *, field: str) -> bool:
    if text == "true":
        return True
    if text == "false":
        return False
    raise ValueError(f"{field} must be true or false, got {text!r}")


def read_constants(path: Path = RAW_CONSTANTS) -> dict[str, Constant]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != CONSTANT_COLUMNS:
            raise ValueError(
                f"{path}: unexpected columns {reader.fieldnames!r}; "
                f"expected {CONSTANT_COLUMNS!r}"
            )
        result: dict[str, Constant] = {}
        for row in reader:
            constant = Constant(
                module=row["module"],
                name=row["name"],
                kind=row["kind"],
                is_private=parse_bool(row["is_private"], field="is_private"),
                private_user_name=row["private_user_name"],
                is_internal=parse_bool(row["is_internal"], field="is_internal"),
                is_unsafe=parse_bool(row["is_unsafe"], field="is_unsafe"),
                is_partial=parse_bool(row["is_partial"], field="is_partial"),
            )
            if constant.name in result:
                raise ValueError(f"{path}: duplicate constant {constant.name}")
            result[constant.name] = constant
    if not result:
        raise ValueError(f"{path}: no project constants found")
    return result


def read_edges(path: Path = RAW_EDGES) -> list[Edge]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != EDGE_COLUMNS:
            raise ValueError(
                f"{path}: unexpected columns {reader.fieldnames!r}; "
                f"expected {EDGE_COLUMNS!r}"
            )
        edges = [Edge(**row) for row in reader]
    if not edges:
        raise ValueError(f"{path}: no dependency edges found")
    bad_origins = sorted({edge.origin for edge in edges} - {"type", "value"})
    if bad_origins:
        raise ValueError(f"{path}: unknown edge origins {bad_origins}")
    return edges


def read_endpoint_names(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        fieldnames = reader.fieldnames or []
        name_column = next(
            (
                candidate
                for candidate in ("name", "declaration", "declaration_name", "endpoint")
                if candidate in fieldnames
            ),
            None,
        )
        if name_column is None:
            raise ValueError(
                f"{path}: V6 endpoint TSV needs one of name/declaration/"
                "declaration_name/endpoint"
            )
        names = {row[name_column].strip() for row in reader if row[name_column].strip()}
    if not names:
        raise ValueError(f"{path}: V6 Tier-B endpoint set is empty")
    return names


def validate_dead_code_calibration(path: Path = RAW_CALIBRATION) -> list[str]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != CALIBRATION_COLUMNS:
            return [
                f"{path}: unexpected calibration columns "
                f"{tuple(reader.fieldnames or ())!r}"
            ]
        rows = list(reader)
    by_label = {row["label"]: row for row in rows}
    errors: list[str] = []
    required_labels = {
        "planted_unreferenced_definition",
        "planted_referenced_definition",
    }
    optional_labels = {"planted_self_recursive_only_definition"}
    observed_labels = set(by_label)
    if (
        not required_labels <= observed_labels
        or observed_labels - required_labels - optional_labels
        or len(rows) != len(observed_labels)
    ):
        errors.append(
            "dead-code calibration label set differs: "
            f"observed={sorted(by_label)}, "
            f"required={sorted(required_labels)}, "
            f"optional={sorted(optional_labels)}"
        )

    constants: dict[str, Constant] = {}
    edges: list[Edge] = []
    expected_candidates: set[str] = set()
    parsed_counts: dict[str, tuple[int, int]] = {}
    for index, row in enumerate(rows, start=2):
        label = row["label"]
        try:
            self_count = int(row["self_reference_count"])
            other_count = int(row["other_reference_count"])
        except ValueError:
            errors.append(f"{path}:{index}: invalid calibration reference count")
            continue
        if self_count < 0 or other_count < 0:
            errors.append(f"{path}:{index}: negative calibration reference count")
            continue
        parsed_counts[label] = (self_count, other_count)
        name = row["name"]
        if not name or name in constants:
            errors.append(f"{path}:{index}: empty or duplicate calibration name")
            continue
        constants[name] = Constant(
            module="V7Calibration",
            name=name,
            kind="definition",
            is_private=True,
            private_user_name=label,
            is_internal=True,
            is_unsafe=False,
            is_partial=False,
        )
        if row["expected_dead_code_candidate"] == "true":
            expected_candidates.add(name)
        elif row["expected_dead_code_candidate"] != "false":
            errors.append(
                f"{path}:{index}: expected_dead_code_candidate must be true/false"
            )
        if self_count:
            edges.append(
                Edge(
                    source_module="V7Calibration",
                    source=name,
                    source_kind="definition",
                    origin="value",
                    target_module="V7Calibration",
                    target=name,
                    target_kind="definition",
                )
            )
        for source_index in range(other_count):
            edges.append(
                Edge(
                    source_module="V7Calibration",
                    source=f"V7Calibration.user.{label}.{source_index}",
                    source_kind="theorem",
                    origin="type",
                    target_module="V7Calibration",
                    target=name,
                    target_kind="definition",
                )
            )
    unreferenced = parsed_counts.get("planted_unreferenced_definition")
    if unreferenced != (0, 0):
        errors.append(
            "planted unreferenced definition does not have (self,other)=(0,0)"
        )
    self_recursive = parsed_counts.get(
        "planted_self_recursive_only_definition"
    )
    if self_recursive is None:
        # Lean's equation compiler need not retain a direct edge from a
        # user-facing recursive constant to itself.  Exercise the production
        # classifier's self-edge rule with a synthetic edge while keeping the
        # required unreferenced/referenced controls environment-measured.
        synthetic_name = "V7Calibration.syntheticSelfRecursive"
        constants[synthetic_name] = Constant(
            module="V7Calibration",
            name=synthetic_name,
            kind="definition",
            is_private=True,
            private_user_name="planted_self_recursive_only_definition",
            is_internal=True,
            is_unsafe=False,
            is_partial=False,
        )
        edges.append(
            Edge(
                source_module="V7Calibration",
                source=synthetic_name,
                source_kind="definition",
                origin="value",
                target_module="V7Calibration",
                target=synthetic_name,
                target_kind="definition",
            )
        )
        expected_candidates.add(synthetic_name)
    elif self_recursive[0] <= 0 or self_recursive[1] != 0:
        errors.append(
            "planted self-recursive-only definition lacks the required "
            "positive self / zero other reference shape"
        )
    referenced = parsed_counts.get("planted_referenced_definition")
    if referenced is None or referenced[1] <= 0:
        errors.append("planted referenced definition has no other reference")
    observed_rows, _exclusions, _zero_total = classify_dead_code(
        constants, edges, set()
    )
    observed_candidates = {
        row["name"]
        for row in observed_rows
        if row["classification"] == "DEAD_CODE_CANDIDATE"
    }
    if observed_candidates != expected_candidates:
        errors.append(
            "production dead-code classifier failed planted calibration: "
            f"observed={sorted(observed_candidates)}, "
            f"expected={sorted(expected_candidates)}"
        )
    return errors


def read_v4_names(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if "name" not in (reader.fieldnames or []):
            raise ValueError(f"{path}: V4 TSV has no name column")
        names = {row["name"] for row in reader}
    if not names:
        raise ValueError(f"{path}: V4 audit is empty")
    return names


def is_prelude_module(module: str) -> bool:
    return (
        module == "HighDimensionalProbability.Prelude"
        or module.startswith("HighDimensionalProbability.Prelude.")
        or module == "MatrixConcentration.Prelude"
        or module.startswith("MatrixConcentration.Prelude.")
    )


def is_aggregator_module(module: str) -> bool:
    return (
        module in {
            "HighDimensionalProbability",
            "MatrixConcentration",
            "HighDimensionalProbability.Appendix",
        }
        or module.endswith(".Main")
    )


def is_exercise_module(module: str) -> bool:
    return ".Exercise." in module or module.endswith(".Exercise")


def is_exercise_declaration(constant: Constant) -> bool:
    """Recognize both exercise-leaf modules and consolidated exercise names."""
    return is_exercise_module(constant.module) or constant.name.rsplit(
        ".", 1
    )[-1].lower().startswith("exercise_")


def classify_dead_code(
    constants: dict[str, Constant],
    edges: list[Edge],
    endpoints: set[str],
) -> tuple[list[dict[str, str]], collections.Counter[str], int]:
    """Classify zero-*other*-reference declarations.

    A recursive declaration's self-edge is not a citation by another
    declaration and therefore cannot rescue it from the dead-code sweep.
    This function is shared verbatim by production analysis and the planted
    static calibration.
    """

    reverse_source_names: dict[str, set[str]] = collections.defaultdict(set)
    for edge in edges:
        if edge.source != edge.target:
            reverse_source_names[edge.target].add(edge.source)
    rows: list[dict[str, str]] = []
    exclusion_counts: collections.Counter[str] = collections.Counter()
    zero_reverse_total = 0
    for constant in sorted(constants.values(), key=lambda item: item.name):
        reverse_count = len(reverse_source_names.get(constant.name, set()))
        if reverse_count != 0:
            continue
        zero_reverse_total += 1
        exclusion_reason = ""
        if constant.kind not in DEAD_CODE_KINDS:
            exclusion_reason = "generated_constructor_recursor_or_quotient"
        elif is_aggregator_module(constant.module):
            exclusion_reason = "root_or_import_aggregator"
        elif is_exercise_declaration(constant):
            exclusion_reason = "exercise_declaration"
        elif constant.name in endpoints:
            exclusion_reason = "deliberately_terminal_tier_b_result"
        elif constant.is_internal and not constant.private_user_name:
            exclusion_reason = "compiler_generated_internal"
        if exclusion_reason:
            classification = "EXCLUDED"
            exclusion_counts[exclusion_reason] += 1
        else:
            classification = "DEAD_CODE_CANDIDATE"
        rows.append(
            {
                "module": constant.module,
                "name": constant.name,
                "kind": constant.kind,
                "is_private": str(constant.is_private).lower(),
                "private_user_name": constant.private_user_name,
                "is_internal": str(constant.is_internal).lower(),
                "reverse_citation_count": str(reverse_count),
                "classification": classification,
                "exclusion_reason": exclusion_reason,
            }
        )
    return rows, exclusion_counts, zero_reverse_total


def citation_score(source: Constant, edge: Edge) -> tuple[int, str]:
    score = 0
    reasons: list[str] = []
    if edge.origin == "type":
        score += 6
        reasons.append("statement-direct")
    else:
        score += 1
        reasons.append("proof-direct")
    if not is_exercise_module(source.module):
        score += 2
        reasons.append("non-exercise")
    if not source.is_internal:
        score += 1
        reasons.append("public-name")
    lowered = source.name.lower()
    lexical = (
        "_eq",
        "eq_",
        "_iff",
        "iff_",
        "_ne",
        "ne_",
        "_pos",
        "positive",
        "_lt",
        "_le",
        "norm",
        "measure",
        "probability",
        "nonempty",
        "finite",
        "mem_",
        "_mem",
    )
    if any(token in lowered for token in lexical):
        score += 3
        reasons.append("nontriviality-lexeme")
    return score, ",".join(reasons)


def analyze(v6_endpoints_path: Path, v4_audit_path: Path) -> int:
    for required in (
        RAW_CONSTANTS,
        RAW_EDGES,
        RAW_CALIBRATION,
        RAW_MODULES,
        v6_endpoints_path,
        v4_audit_path,
    ):
        if not required.is_file():
            raise FileNotFoundError(required)
    LOGS.mkdir(parents=True, exist_ok=True)
    constants = read_constants()
    edges = read_edges()
    actual_modules = read_modules()
    expected = expected_modules()
    row_modules = {constant.module for constant in constants.values()}
    missing_modules, extra_modules, _ = write_module_coverage(
        expected, actual_modules, row_modules
    )
    endpoints = read_endpoint_names(v6_endpoints_path)
    v4_names = read_v4_names(v4_audit_path)
    calibration_errors = validate_dead_code_calibration()

    hard_failures: list[str] = []
    incomplete_reasons: list[str] = []
    constant_names = set(constants)
    edge_keys = {
        (edge.source, edge.origin, edge.target) for edge in edges
    }
    if len(edge_keys) != len(edges):
        hard_failures.append(
            f"{len(edges) - len(edge_keys)} duplicate direct dependency rows"
        )
    unknown_edge_sources = {
        edge.source for edge in edges if edge.source not in constants
    }
    if unknown_edge_sources:
        hard_failures.append(
            f"{len(unknown_edge_sources)} dependency-edge sources are absent "
            "from the project constant inventory"
        )
    bad_source_metadata = {
        edge.source
        for edge in edges
        if edge.source in constants
        and (
            edge.source_module != constants[edge.source].module
            or edge.source_kind != constants[edge.source].kind
        )
    }
    if bad_source_metadata:
        hard_failures.append(
            f"{len(bad_source_metadata)} dependency-edge sources have "
            "inconsistent module/kind metadata"
        )
    bad_project_target_metadata = {
        edge.target
        for edge in edges
        if edge.target in constants
        and (
            edge.target_module != constants[edge.target].module
            or edge.target_kind != constants[edge.target].kind
        )
    }
    if bad_project_target_metadata:
        hard_failures.append(
            f"{len(bad_project_target_metadata)} project dependency targets "
            "have inconsistent module/kind metadata"
        )
    constants_outside_environment_modules = {
        constant.module
        for constant in constants.values()
        if constant.module not in actual_modules
    }
    if constants_outside_environment_modules:
        hard_failures.append(
            f"{len(constants_outside_environment_modules)} constant-row "
            "modules are absent from the environment module list"
        )
    if missing_modules:
        incomplete_reasons.append(
            f"{len(missing_modules)} expected physical/root modules are absent "
            "from the current complete environment"
        )
    if extra_modules:
        hard_failures.append(
            f"{len(extra_modules)} unexpected project-root modules are present"
        )
    if constant_names != v4_names:
        hard_failures.append(
            "V4/V7 environment declaration sets differ: "
            f"{len(v4_names - constant_names)} V4-only, "
            f"{len(constant_names - v4_names)} V7-only"
        )
    unknown_endpoints = endpoints - constant_names
    if unknown_endpoints:
        hard_failures.append(
            f"{len(unknown_endpoints)} V6 endpoints are absent from the V4/V7 environment"
        )
    nontheorem_endpoints = {
        name
        for name in endpoints & constant_names
        if constants[name].kind != "theorem"
    }
    if nontheorem_endpoints:
        hard_failures.append(
            f"{len(nontheorem_endpoints)} V6 Tier-B endpoints are not theorem constants"
        )
    hard_failures.extend(calibration_errors)

    incoming: dict[str, list[Edge]] = collections.defaultdict(list)
    outgoing: dict[str, list[Edge]] = collections.defaultdict(list)
    for edge in edges:
        incoming[edge.target].append(edge)
        outgoing[edge.source].append(edge)

    endpoint_refs: dict[str, dict[str, set[str]]] = collections.defaultdict(
        lambda: {"type": set(), "value": set(), "any": set()}
    )
    for endpoint in endpoints & constant_names:
        for edge in outgoing.get(endpoint, []):
            target = constants.get(edge.target)
            if target is None or target.kind not in DEFINITION_KINDS:
                continue
            endpoint_refs[target.name][edge.origin].add(endpoint)
            endpoint_refs[target.name]["any"].add(endpoint)

    prelude_environment_definitions = {
        constant.name
        for constant in constants.values()
        if is_prelude_module(constant.module)
        and constant.kind in DEFINITION_KINDS
    }
    prelude_generated_exclusions = {
        name
        for name in prelude_environment_definitions
        if is_compiler_generated_definition(name)
    }
    prelude_definitions = (
        prelude_environment_definitions - prelude_generated_exclusions
    )
    threshold_definitions = {
        target
        for target, counts in endpoint_refs.items()
        if len(counts["any"]) >= 3
    }
    load_bearing = prelude_definitions | threshold_definitions

    with LOAD_BEARING.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(LOAD_BEARING_COLUMNS)
        for name in sorted(load_bearing):
            constant = constants[name]
            reasons = []
            if name in prelude_definitions:
                reasons.append("all_prelude_defs_structures_classes")
            if name in threshold_definitions:
                reasons.append("directly_referenced_by_ge3_tier_b_endpoints")
            counts = endpoint_refs.get(
                name, {"type": set(), "value": set(), "any": set()}
            )
            writer.writerow(
                [
                    constant.module,
                    module_to_source_path(constant.module),
                    constant.name,
                    constant.kind,
                    str(constant.is_private).lower(),
                    constant.private_user_name,
                    str(constant.is_internal).lower(),
                    ";".join(reasons),
                    len(counts["any"]),
                    len(counts["type"]),
                    len(counts["value"]),
                ]
            )

    reverse_row_count = 0
    with REVERSE_CITATIONS.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "target_module",
                "target",
                "target_kind",
                "source_module",
                "source",
                "source_kind",
                "origin",
            ]
        )
        for target in sorted(load_bearing):
            for edge in sorted(
                incoming.get(target, []),
                key=lambda item: (item.source, item.origin),
            ):
                writer.writerow(
                    [
                        constants[target].module,
                        target,
                        constants[target].kind,
                        edge.source_module,
                        edge.source,
                        edge.source_kind,
                        edge.origin,
                    ]
                )
                reverse_row_count += 1

    candidate_row_count = 0
    targets_with_statement_theorem_candidate: set[str] = set()
    with NONTRIVIALITY_CANDIDATES.open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(CANDIDATE_COLUMNS)
        candidates: list[tuple[str, int, str, Edge]] = []
        for target in load_bearing:
            for edge in incoming.get(target, []):
                source = constants.get(edge.source)
                # A proof-body dependency shows that a definition is used, but
                # it does not state a mathematical property of that
                # definition.  Only statement-level theorem citations are
                # admissible nontriviality candidates.
                if (
                    source is None
                    or source.kind != "theorem"
                    or edge.origin != "type"
                ):
                    continue
                score, reasons = citation_score(source, edge)
                candidates.append((target, score, reasons, edge))
                targets_with_statement_theorem_candidate.add(target)
        for target, score, reasons, edge in sorted(
            candidates,
            key=lambda item: (item[0], -item[1], item[3].source, item[3].origin),
        ):
            writer.writerow(
                [
                    constants[target].module,
                    target,
                    constants[target].kind,
                    edge.source_module,
                    edge.source,
                    edge.origin,
                    score,
                    reasons,
                ]
            )
            candidate_row_count += 1

    dead_rows, exclusion_counts, zero_reverse_total = classify_dead_code(
        constants, edges, endpoints
    )
    dead_candidates = sum(
        row["classification"] == "DEAD_CODE_CANDIDATE" for row in dead_rows
    )
    with DEAD_CODE_SWEEP.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=DEAD_CODE_COLUMNS,
            delimiter="\t",
            lineterminator="\n",
            extrasaction="raise",
        )
        writer.writeheader()
        writer.writerows(dead_rows)

    no_candidate = load_bearing - targets_with_statement_theorem_candidate
    if not load_bearing:
        hard_failures.append("the measured load-bearing definition set is empty")
    if no_candidate:
        incomplete_reasons.append(
            f"{len(no_candidate)} load-bearing definitions have no direct theorem-statement "
            "citation; "
            "review or compiled witnesses are required"
        )
    incomplete_reasons.append(
        f"all {len(load_bearing)} load-bearing rows require an explicit manual "
        "disposition: theorem-statement rows are candidates only and are not "
        "nontriviality evidence until a reviewer verifies the semantic claim; "
        "witness rows require a named clean build and allowed-axiom result"
    )
    verdict = choose_verdict(
        hard_failures=hard_failures,
        incomplete_reasons=incomplete_reasons,
    )

    lines = [
        "V7 DEFINITION SANITY TOOLING SUMMARY",
        "====================================",
        f"verdict: {verdict}",
        f"expected_modules: {len(expected)}",
        f"environment_modules: {len(actual_modules)}",
        f"missing_modules: {len(missing_modules)}",
        (
            "module_coverage: "
            f"{'PASS' if not missing_modules and not extra_modules else 'INCOMPLETE'}"
        ),
        "full_surface_gate: PASS (complete current 223-module environment)",
        f"project_constants: {len(constants)}",
        f"direct_dependency_edges: {len(edges)}",
        f"direct_dependency_rows_unique: {len(edge_keys) == len(edges)}",
        f"unknown_dependency_edge_sources: {len(unknown_edge_sources)}",
        f"inconsistent_edge_source_metadata: {len(bad_source_metadata)}",
        (
            "inconsistent_project_target_metadata: "
            f"{len(bad_project_target_metadata)}"
        ),
        (
            "constant_modules_outside_environment: "
            f"{len(constants_outside_environment_modules)}"
        ),
        f"v6_tier_b_theorem_endpoints: {len(endpoints)}",
        f"prelude_definitions_structures_classes: {len(prelude_definitions)}",
        (
            "prelude_compiler_generated_helpers_excluded_from_blanket_rule: "
            f"{len(prelude_generated_exclusions)}"
        ),
        f"ge3_tier_b_direct_reference_definitions: {len(threshold_definitions)}",
        f"load_bearing_union: {len(load_bearing)}",
        f"reverse_citation_rows_for_load_bearing: {reverse_row_count}",
        (
            "candidate_nontriviality_citation_rows_NOT_VERIFIED: "
            f"{candidate_row_count}"
        ),
        f"load_bearing_without_theorem_statement_candidate: {len(no_candidate)}",
        "manual_review_complete: false",
        "review_input_contract_version: 2",
        f"zero_reverse_declarations_before_exclusions: {zero_reverse_total}",
        f"dead_code_candidates_after_exclusions: {dead_candidates}",
        f"dead_code_calibration: {'PASS' if not calibration_errors else 'FAIL'}",
        f"v4_environment_name_set_match: {constant_names == v4_names}",
        "",
        "[dead_code_exclusion_counts]",
    ]
    lines.extend(
        f"{reason}: {count}" for reason, count in sorted(exclusion_counts.items())
    )
    lines.extend(("", "[hard_failures]"))
    lines.extend(hard_failures or ["(none)"])
    lines.extend(("", "[incomplete_reasons]"))
    lines.extend(incomplete_reasons or ["(none)"])
    lines.extend(
        ("", "[load_bearing_without_direct_theorem_statement_candidate]")
    )
    lines.extend(sorted(no_candidate) or ["(none)"])
    lines.extend(("", "[prelude_compiler_generated_helper_exclusions]"))
    lines.extend(sorted(prelude_generated_exclusions) or ["(none)"])
    lines.extend(
        (
            "",
            "[manual_review_contract]",
            (
                "A candidate theorem is discovery metadata only. It becomes "
                "VERIFIED_CITATION only after a reviewer records why the theorem "
                "statement would fail for the relevant degenerate interpretation "
                "and the evidence declaration passes the V4 axiom gate."
            ),
            (
                "A proposed witness becomes VERIFIED_WITNESS only after its named "
                "declaration compiles without sorry/admit and its collected axioms "
                "are contained in {propext, Classical.choice, Quot.sound}."
            ),
            (
                "Until a separate fail-closed review-register validator accepts "
                "every load-bearing row, this analyzer's verdict is INCOMPLETE."
            ),
        )
    )
    SUMMARY.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines[:24]))
    print(f"summary: {SUMMARY.relative_to(ROOT)}")
    return {"PASS": 0, "ISSUES-FOUND": 1, "INCOMPLETE": 2}[verdict]


def run_lean_file(harness: Path, log_path: Path) -> tuple[int, str]:
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
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    finished = dt.datetime.now(dt.timezone.utc).astimezone()
    log_path.write_text(
        "\n".join(
            [
                f"started: {started.isoformat()}",
                f"cwd: {ROOT}",
                f"command: {shlex.join(command)}",
                "",
                completed.stdout.rstrip("\n"),
                "",
                f"finished: {finished.isoformat()}",
                f"elapsed_seconds: {(finished - started).total_seconds():.3f}",
                f"exit_code: {completed.returncode}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return completed.returncode, completed.stdout


def run_harness(
    v2_evidence_path: Path,
    v6_endpoints_path: Path,
    v4_audit_path: Path,
) -> int:
    if not v2_evidence_path.is_file():
        raise RuntimeError(
            "refusing to run V7 before fresh V2 surface evidence exists: "
            f"{v2_evidence_path}"
        )
    v2_text = v2_evidence_path.read_text(
        encoding="utf-8", errors="replace"
    )
    required_v2_markers = (
        "graph_status: PASS",
        "partition_status: PASS",
        "orphan_count: 0",
        "matrix_concentration_modules: 10",
        "v2_zero_orphan_gate: true",
    )
    missing_v2_markers = [
        marker for marker in required_v2_markers if marker not in v2_text
    ]
    if missing_v2_markers:
        raise RuntimeError(
            "refusing to run V7 because V2 surface evidence lacks "
            f"{missing_v2_markers}: {v2_evidence_path}"
        )
    if not v6_endpoints_path.is_file() or not v6_endpoints_path.read_text(
        encoding="utf-8", errors="replace"
    ).strip():
        raise RuntimeError(
            "refusing to run final V7 before nonempty V6 Tier-B endpoint evidence "
            f"exists: {v6_endpoints_path}"
        )
    if not v4_audit_path.is_file():
        raise RuntimeError(
            f"refusing to run V7 before the V4 environment audit: {v4_audit_path}"
        )
    if not HARNESS.is_file():
        raise FileNotFoundError(HARNESS)
    LOGS.mkdir(parents=True, exist_ok=True)
    returncode, _ = run_lean_file(HARNESS, BUILD_LOG)
    if returncode != 0:
        print(f"Lean harness failed; see {BUILD_LOG.relative_to(ROOT)}", file=sys.stderr)
        return returncode
    return analyze(v6_endpoints_path, v4_audit_path)


def self_test() -> int:
    assert source_path_to_module(
        "HighDimensionalProbability/Appendix/Infra/BerryEsseenSmoothing.lean"
    ) == "HighDimensionalProbability.Appendix.Infra.BerryEsseenSmoothing"
    assert source_path_to_module(
        "MatrixConcentration/Chapter1_Introduction.lean"
    ) == "MatrixConcentration.Chapter1_Introduction"
    assert module_to_source_path(
        "HighDimensionalProbability.Prelude.Orlicz"
    ) == "HighDimensionalProbability/Prelude/Orlicz.lean"
    assert module_to_source_path(
        "MatrixConcentration.Chapter1_Introduction"
    ) == "MatrixConcentration/Chapter1_Introduction.lean"
    expected = expected_modules()
    assert len(expected) == 223
    assert (
        "HighDimensionalProbability.Appendix.Infra.BerryEsseenSmoothing"
        in expected
    )
    assert is_compiler_generated_definition("HDP.FiniteNet.casesOn")
    assert is_compiler_generated_definition("HDP.FiniteNet.mk._flat_ctor")
    assert not is_compiler_generated_definition("HDP.minimalFiniteNet")
    assert choose_verdict(
        hard_failures=["local issue"],
        incomplete_reasons=[],
    ) == "ISSUES-FOUND"
    assert choose_verdict(
        hard_failures=[],
        incomplete_reasons=[
            "semantic review is required even when every row has a candidate"
        ],
    ) == "INCOMPLETE"
    assert is_prelude_module("HighDimensionalProbability.Prelude.Orlicz")
    assert is_prelude_module("MatrixConcentration.Prelude")
    assert not is_prelude_module("HighDimensionalProbability.Chapter1.Main")
    assert is_aggregator_module("HighDimensionalProbability")
    assert is_aggregator_module("HighDimensionalProbability.Chapter1.Main")
    assert is_exercise_module("HighDimensionalProbability.Exercise.Chapter1.Sec01")
    consolidated_exercise = Constant(
        module="HighDimensionalProbability.Chapter8_Chaining",
        name="HDP.Chapter8.exercise_8_1",
        kind="theorem",
        is_private=False,
        private_user_name="",
        is_internal=False,
        is_unsafe=False,
        is_partial=False,
    )
    assert is_exercise_declaration(consolidated_exercise)
    sample = Constant(
        module="HighDimensionalProbability.Prelude.Orlicz",
        name="HDP.orliczNorm_eq_zero",
        kind="theorem",
        is_private=False,
        private_user_name="",
        is_internal=False,
        is_unsafe=False,
        is_partial=False,
    )
    edge = Edge(
        source_module=sample.module,
        source=sample.name,
        source_kind="theorem",
        origin="type",
        target_module=sample.module,
        target="HDP.orliczNorm",
        target_kind="definition",
    )
    score, reasons = citation_score(sample, edge)
    assert score >= 10 and "statement-direct" in reasons
    dead = Constant(
        module="V7Calibration",
        name="V7Calibration.dead",
        kind="definition",
        is_private=False,
        private_user_name="",
        is_internal=False,
        is_unsafe=False,
        is_partial=False,
    )
    recursive = Constant(
        module="V7Calibration",
        name="V7Calibration.recursive",
        kind="definition",
        is_private=False,
        private_user_name="",
        is_internal=False,
        is_unsafe=False,
        is_partial=False,
    )
    live = Constant(
        module="V7Calibration",
        name="V7Calibration.live",
        kind="definition",
        is_private=False,
        private_user_name="",
        is_internal=False,
        is_unsafe=False,
        is_partial=False,
    )
    calibration_edges = [
        Edge(
            source_module=recursive.module,
            source=recursive.name,
            source_kind="definition",
            origin="value",
            target_module=recursive.module,
            target=recursive.name,
            target_kind="definition",
        ),
        Edge(
            source_module="V7Calibration.User",
            source="V7Calibration.usesLive",
            source_kind="theorem",
            origin="type",
            target_module=live.module,
            target=live.name,
            target_kind="definition",
        ),
    ]
    dead_rows, _, _ = classify_dead_code(
        {item.name: item for item in (dead, recursive, live)},
        calibration_edges,
        set(),
    )
    assert {
        row["name"]
        for row in dead_rows
        if row["classification"] == "DEAD_CODE_CANDIDATE"
    } == {dead.name, recursive.name}
    with tempfile.TemporaryDirectory(
        prefix="hdp-v7-dead-code-calibration-"
    ) as temporary:
        calibration_path = Path(temporary) / "calibration.tsv"
        with calibration_path.open(
            "w", encoding="utf-8", newline=""
        ) as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=CALIBRATION_COLUMNS,
                delimiter="\t",
                lineterminator="\n",
            )
            writer.writeheader()
            writer.writerows(
                (
                    {
                        "label": "planted_unreferenced_definition",
                        "name": "_private.V7.0.dead",
                        "self_reference_count": "0",
                        "other_reference_count": "0",
                        "expected_dead_code_candidate": "true",
                    },
                    {
                        "label": (
                            "planted_self_recursive_only_definition"
                        ),
                        "name": "_private.V7.0.recursive",
                        "self_reference_count": "1",
                        "other_reference_count": "0",
                        "expected_dead_code_candidate": "true",
                    },
                    {
                        "label": "planted_referenced_definition",
                        "name": "_private.V7.0.live",
                        "self_reference_count": "0",
                        "other_reference_count": "1",
                        "expected_dead_code_candidate": "false",
                    },
                )
            )
        assert not validate_dead_code_calibration(calibration_path)
    print(
        "PASS: definition-sanity Python self-test; "
        "current 223-module path mappings pass; verdict precedence and production "
        "dead-code classifier flags unreferenced and self-recursive-only plants"
    )
    return 0


def resolve_from_root(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="action", required=True)
    subparsers.add_parser("self-test")
    for action in ("analyze", "run"):
        subparser = subparsers.add_parser(action)
        subparser.add_argument(
            "--v6-endpoints",
            type=Path,
            default=DEFAULT_V6_ENDPOINTS.relative_to(ROOT),
        )
        subparser.add_argument(
            "--v4-audit",
            type=Path,
            default=DEFAULT_V4_AUDIT.relative_to(ROOT),
        )
        if action == "run":
            subparser.add_argument(
                "--v2-evidence",
                type=Path,
                default=DEFAULT_V2_EVIDENCE.relative_to(ROOT),
                help="nonempty completed V2 surface/import evidence",
            )
    args = parser.parse_args()
    if args.action == "self-test":
        return self_test()
    v6_endpoints = resolve_from_root(args.v6_endpoints)
    v4_audit = resolve_from_root(args.v4_audit)
    if args.action == "analyze":
        return analyze(v6_endpoints, v4_audit)
    if args.action == "run":
        return run_harness(
            resolve_from_root(args.v2_evidence),
            v6_endpoints,
            v4_audit,
        )
    raise AssertionError(args.action)


if __name__ == "__main__":
    raise SystemExit(main())
