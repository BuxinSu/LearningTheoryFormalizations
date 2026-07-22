#!/usr/bin/env python3
"""Reconcile textual V3 placeholders with V4 ``sorryAx`` dependencies.

The direct placeholder set is recovered independently from the lexer-aware V3
JSON and the mechanically parsed exercise declaration inventory.  The V4
direct dependency dump then supplies a checkable path from every transitive
``sorryAx`` declaration back to one of those textual sites.  The computed
reverse closure must equal the kernel-level ``sorryAx`` set exactly.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
DEFAULT_V3 = LOGS / "v3_library.json"
DEFAULT_V4 = LOGS / "axiom_audit.tsv"
DEFAULT_EDGES = LOGS / "axiom_direct_dependencies.tsv"
DEFAULT_EXERCISES = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "inventory"
    / "exercise_leaf_declarations.tsv"
)
DIRECT_OUT = LOGS / "v3_direct_sorry_declarations.tsv"
ALLOWLIST_OUT = LOGS / "v3_sorry_declarations.tsv"
RECONCILIATION_OUT = LOGS / "v3_v4_sorry_reconciliation.tsv"
SUMMARY_OUT = LOGS / "v3_v4_sorry_reconciliation.txt"
EXERCISE_LEAF_MODULE = re.compile(
    r"^HighDimensionalProbability\.Exercise\.Chapter[0-9]+\.Sec[0-9]+$"
)


@dataclass(frozen=True)
class ExerciseDeclaration:
    path: str
    endpoint: str
    start_line: int


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def _read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def _direct_textual_sorries(
    v3_path: Path, exercise_path: Path
) -> tuple[list[tuple[ExerciseDeclaration, int]], list[str]]:
    payload = json.loads(v3_path.read_text(encoding="utf-8"))
    hits = [
        hit
        for hit in payload.get("hits", [])
        if hit.get("in_code") is True
        and hit.get("pattern_id") in {"v3.sorry", "v3.admit", "v3.sorryAx"}
    ]
    declarations_by_path: dict[str, list[ExerciseDeclaration]] = defaultdict(list)
    for row in _read_tsv(exercise_path):
        declarations_by_path[row["path"]].append(
            ExerciseDeclaration(
                path=row["path"],
                endpoint=row["endpoint"],
                start_line=int(row["start_line"]),
            )
        )
    for declarations in declarations_by_path.values():
        declarations.sort(key=lambda declaration: declaration.start_line)

    mapped: list[tuple[ExerciseDeclaration, int]] = []
    errors: list[str] = []
    for hit in hits:
        path = str(hit["path"])
        line = int(hit["line"])
        candidates = [
            declaration
            for declaration in declarations_by_path.get(path, [])
            if declaration.start_line <= line
        ]
        if not candidates:
            errors.append(f"no exercise declaration precedes {path}:{line}")
            continue
        declaration = candidates[-1]
        source = ROOT / path
        lines = source.read_text(encoding="utf-8").splitlines()
        prefix_start = max(0, declaration.start_line - 30)
        prefix = "\n".join(lines[prefix_start : line])
        if "EXERCISE-SORRY" not in prefix:
            errors.append(
                f"{declaration.endpoint} at {path}:{line} lacks nearby "
                "EXERCISE-SORRY marker"
            )
        mapped.append((declaration, line))

    duplicate_endpoints = sorted(
        endpoint
        for endpoint in {declaration.endpoint for declaration, _ in mapped}
        if sum(
            1
            for declaration, _ in mapped
            if declaration.endpoint == endpoint
        )
        != 1
    )
    if duplicate_endpoints:
        errors.append(
            "multiple textual placeholder sites mapped to one declaration: "
            + ", ".join(duplicate_endpoints[:20])
        )
    return mapped, errors


def _read_v4_sorry(path: Path) -> tuple[set[str], dict[str, dict[str, str]]]:
    rows = _read_tsv(path)
    by_name = {row["name"]: row for row in rows}
    sorry = {
        row["name"]
        for row in rows
        if "sorryAx" in set(filter(None, row["axioms"].split(";")))
    }
    return sorry, by_name


def _read_edges(
    path: Path,
    project_names: set[str],
) -> tuple[
    dict[str, set[str]],
    dict[tuple[str, str], set[str]],
]:
    forward: dict[str, set[str]] = defaultdict(set)
    origins: dict[tuple[str, str], set[str]] = defaultdict(set)
    # The V4 dump also records every direct edge from a project declaration
    # into Mathlib.  Those rows dominate the file size but cannot participate
    # in a reverse path between two project declarations.  Stream the dump
    # and retain only the project-to-project subgraph needed for this join.
    with path.open(encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            source = row["source"]
            target = row["target"]
            if source not in project_names or target not in project_names:
                continue
            forward[source].add(target)
            origins[(source, target)].add(row["origin"])
    return forward, origins


def _reverse_closure(
    direct: set[str],
    forward: dict[str, set[str]],
) -> tuple[set[str], dict[str, str], dict[str, int]]:
    reverse: dict[str, set[str]] = defaultdict(set)
    for source, targets in forward.items():
        for target in targets:
            reverse[target].add(source)
    closure = set(direct)
    next_toward_direct: dict[str, str] = {}
    distance = {name: 0 for name in direct}
    queue: deque[str] = deque(sorted(direct))
    while queue:
        target = queue.popleft()
        for source in sorted(reverse.get(target, ())):
            if source in closure:
                continue
            closure.add(source)
            next_toward_direct[source] = target
            distance[source] = distance[target] + 1
            queue.append(source)
    return closure, next_toward_direct, distance


def _path_to_direct(
    name: str,
    direct: set[str],
    next_toward_direct: dict[str, str],
) -> list[str]:
    result = [name]
    seen = {name}
    while result[-1] not in direct:
        next_name = next_toward_direct.get(result[-1])
        if next_name is None or next_name in seen:
            break
        result.append(next_name)
        seen.add(next_name)
    return result


def analyze(
    v3_path: Path,
    v4_path: Path,
    edge_path: Path,
    exercise_path: Path,
    direct_output: Path,
    allowlist_output: Path,
    reconciliation_output: Path,
    summary_output: Path,
) -> int:
    for output in (
        direct_output,
        allowlist_output,
        reconciliation_output,
        summary_output,
    ):
        output.parent.mkdir(parents=True, exist_ok=True)
    mapped, errors = _direct_textual_sorries(v3_path, exercise_path)
    direct = {declaration.endpoint for declaration, _ in mapped}
    v4_sorry, v4_rows = _read_v4_sorry(v4_path)
    forward, origins = _read_edges(edge_path, set(v4_rows))
    closure, next_toward_direct, distance = _reverse_closure(direct, forward)
    project_closure = closure & set(v4_rows)
    v4_only = v4_sorry - project_closure
    closure_only = project_closure - v4_sorry
    if v4_only:
        errors.append(
            f"{len(v4_only)} V4 sorryAx declarations lack a dependency path "
            "to a textual placeholder"
        )
    if closure_only:
        errors.append(
            f"{len(closure_only)} declarations are in the textual reverse "
            "dependency closure but V4 does not report sorryAx"
        )
    if not direct:
        errors.append("direct textual sorry declaration set is empty")
    non_exercise_kernel = sorted(
        name
        for name in v4_sorry
        if not EXERCISE_LEAF_MODULE.fullmatch(v4_rows[name]["module"])
    )
    if non_exercise_kernel:
        errors.append(
            f"{len(non_exercise_kernel)} kernel sorryAx declarations are "
            "outside Exercise leaf modules"
        )
    direct_kernel = v4_sorry & direct
    transitive_kernel = v4_sorry - direct

    with direct_output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(["name", "classification", "path", "sorry_line"])
        for declaration, line in sorted(
            mapped, key=lambda item: (item[0].path, item[1], item[0].endpoint)
        ):
            writer.writerow(
                [
                    declaration.endpoint,
                    "EXERCISE-SORRY",
                    declaration.path,
                    line,
                ]
            )

    with allowlist_output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(["name", "classification"])
        for name in sorted(v4_sorry):
            writer.writerow(
                [
                    name,
                    "DIRECT_TEXTUAL_SORRY"
                    if name in direct
                    else "TRANSITIVE_SORRY_DEPENDENCY",
                ]
            )

    with reconciliation_output.open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "name",
                "module",
                "classification",
                "distance_to_textual_sorry",
                "immediate_dependency_edge",
                "edge_origin",
                "dependency_path",
            ]
        )
        for name in sorted(v4_sorry):
            row = v4_rows[name]
            target = next_toward_direct.get(name, "")
            writer.writerow(
                [
                    name,
                    row["module"],
                    (
                        "DIRECT_TEXTUAL_SORRY"
                        if name in direct
                        else "TRANSITIVE_SORRY_DEPENDENCY"
                    ),
                    distance.get(name, ""),
                    f"{name} -> {target}" if target else "",
                    ";".join(sorted(origins.get((name, target), ()))),
                    " -> ".join(
                        _path_to_direct(name, direct, next_toward_direct)
                    ),
                ]
            )

    lines = [
        "V3/V4 SORRY RECONCILIATION",
        "===========================",
        f"direct_textual_sorry_declarations: {len(direct)}",
        f"kernel_sorryAx_declarations: {len(v4_sorry)}",
        f"reverse_dependency_closure_project_declarations: {len(project_closure)}",
        f"kernel_sorryAx_direct_textual_declarations: {len(direct_kernel)}",
        f"kernel_sorryAx_transitive_declarations: {len(transitive_kernel)}",
        f"kernel_sorryAx_outside_exercise_leaf_modules: {len(non_exercise_kernel)}",
        f"v4_without_textual_dependency_path: {len(v4_only)}",
        f"closure_without_v4_sorryAx: {len(closure_only)}",
        f"marker_or_mapping_errors: {len(errors)}",
        f"verdict: {'PASS' if not errors else 'FAIL'}",
        "",
        "[errors]",
        *(errors or ["(none)"]),
        "",
        "[V4-only]",
        *(sorted(v4_only) or ["(none)"]),
        "",
        "[closure-only]",
        *(sorted(closure_only) or ["(none)"]),
        "",
        "[kernel sorryAx outside Exercise leaf modules]",
        *(non_exercise_kernel or ["(none)"]),
    ]
    summary_output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines[:9]))
    return 1 if errors else 0


def self_test() -> int:
    direct = {"A"}
    forward = {
        "B": {"A"},
        "C": {"B"},
        "D": {"Unrelated"},
    }
    closure, next_edge, distance = _reverse_closure(direct, forward)
    assert closure == {"A", "B", "C"}
    assert next_edge == {"B": "A", "C": "B"}
    assert distance == {"A": 0, "B": 1, "C": 2}
    assert _path_to_direct("C", direct, next_edge) == ["C", "B", "A"]
    print("PASS: V3/V4 reconciliation graph self-test")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--v3-json", type=Path, default=DEFAULT_V3)
    parser.add_argument("--v4-audit", type=Path, default=DEFAULT_V4)
    parser.add_argument("--v4-dependencies", type=Path, default=DEFAULT_EDGES)
    parser.add_argument(
        "--exercise-inventory", type=Path, default=DEFAULT_EXERCISES
    )
    parser.add_argument("--direct-output", type=Path, default=DIRECT_OUT)
    parser.add_argument("--allowlist-output", type=Path, default=ALLOWLIST_OUT)
    parser.add_argument(
        "--reconciliation-output",
        type=Path,
        default=RECONCILIATION_OUT,
    )
    parser.add_argument("--summary-output", type=Path, default=SUMMARY_OUT)
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    return analyze(
        _resolve(args.v3_json),
        _resolve(args.v4_audit),
        _resolve(args.v4_dependencies),
        _resolve(args.exercise_inventory),
        _resolve(args.direct_output),
        _resolve(args.allowlist_output),
        _resolve(args.reconciliation_output),
        _resolve(args.summary_output),
    )


if __name__ == "__main__":
    raise SystemExit(main())
