#!/usr/bin/env python3
"""Resolve source declarations and analyze V7 direct dependency graphs."""

from __future__ import annotations

import csv
import json
from collections import defaultdict
from pathlib import Path

from lean_source_scan import LOGS


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def names(text: str) -> set[str]:
    return {name for name in text.split(",") if name}


def write_tsv(path: Path, fields: list[str], rows: list[dict[str, object]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)


def suffix_matches(environment_name: str, raw_name: str) -> bool:
    return environment_name == raw_name or environment_name.endswith("." + raw_name)


def main() -> int:
    source = read_tsv(LOGS / "v7_public_source_declarations.tsv")
    all_source = read_tsv(LOGS / "v7_all_source_declarations.tsv")
    environment = read_tsv(LOGS / "v7_environment_dependencies.tsv")
    environment_by_module: dict[str, list[dict[str, str]]] = defaultdict(list)
    environment_by_name: dict[str, dict[str, str]] = {}
    for row in environment:
        environment_by_module[row["module"]].append(row)
        environment_by_name[row["name"]] = row

    def resolve_inventory(
        inventory: list[dict[str, str]], *, id_field: str
    ) -> tuple[list[dict[str, str]], list[str]]:
        inventory_resolved: list[dict[str, str]] = []
        failures: list[str] = []
        for row in inventory:
            line = int(row["line"])
            expected_kind = (
                "theorem"
                if row["keyword"] in {"theorem", "lemma"}
                else "definition"
            )
            candidates = [
                candidate
                for candidate in environment_by_module[row["module"]]
                if candidate["kind"] == expected_kind
                and suffix_matches(candidate["user_name"], row["raw_name"])
                and int(candidate["range_start_line"]) <= line
                and line <= int(candidate["range_end_line"])
            ]
            if len(candidates) != 1:
                failures.append(
                    f"{row['path']}:{line} {row['keyword']} {row['raw_name']}: "
                    f"{len(candidates)} candidates "
                    + ",".join(candidate["name"] for candidate in candidates)
                )
                continue
            candidate = candidates[0]
            merged = dict(row)
            merged.update(
                {
                    id_field: row[id_field],
                    "resolved_name": candidate["name"],
                    "user_name": candidate["user_name"],
                    "environment_kind": candidate["kind"],
                    "range_start_line": candidate["range_start_line"],
                    "range_end_line": candidate["range_end_line"],
                    "axioms": candidate["axioms"],
                }
            )
            inventory_resolved.append(merged)
        return inventory_resolved, failures

    resolved, resolution_failures = resolve_inventory(
        source, id_field="source_id"
    )
    all_resolved, all_resolution_failures = resolve_inventory(
        all_source, id_field="all_source_id"
    )

    resolution_fields = [
        "source_id",
        "module",
        "path",
        "line",
        "keyword",
        "raw_name",
        "visibility",
        "resolved_name",
        "user_name",
        "environment_kind",
        "range_start_line",
        "range_end_line",
        "axioms",
    ]
    write_tsv(
        LOGS / "v7_source_resolution.tsv", resolution_fields, resolved
    )
    (LOGS / "v7_source_resolution_failures.log").write_text(
        "\n".join(resolution_failures + all_resolution_failures)
        + ("\n" if resolution_failures or all_resolution_failures else ""),
        encoding="utf-8",
    )
    all_resolution_fields = [
        "all_source_id",
        "module",
        "path",
        "line",
        "keyword",
        "raw_name",
        "visibility",
        "resolved_name",
        "user_name",
        "environment_kind",
        "range_start_line",
        "range_end_line",
        "axioms",
    ]
    write_tsv(
        LOGS / "v7_all_source_resolution.tsv",
        all_resolution_fields,
        all_resolved,
    )
    if (
        resolution_failures
        or all_resolution_failures
        or len(resolved) != 1443
        or len(all_resolved) != 1525
    ):
        raise RuntimeError(
            f"source resolution failed: public={len(resolved)}, "
            f"all={len(all_resolved)}, "
            f"failures={len(resolution_failures) + len(all_resolution_failures)}"
        )

    source_by_name = {row["resolved_name"]: row for row in resolved}
    source_names = set(source_by_name)
    all_source_by_name = {row["resolved_name"]: row for row in all_resolved}
    all_source_names = set(all_source_by_name)
    definition_keywords = {"def", "structure", "class"}
    public_definition_candidates = [
        row for row in resolved if row["keyword"] in definition_keywords
    ]
    private_definition_candidates = [
        row
        for row in all_resolved
        if row["visibility"] == "private"
        and row["keyword"] in definition_keywords
    ]
    all_definition_candidates = (
        public_definition_candidates + private_definition_candidates
    )
    endpoints = read_tsv(LOGS / "v6_endpoint_telescopes.tsv")
    theorem_endpoints = [
        row for row in endpoints if row["kind"] == "theorem"
    ]
    endpoint_names = {row["resolved_name"] for row in endpoints}
    terminal_result_names = {
        row["resolved_name"] for row in theorem_endpoints
    }
    if len(endpoints) != 467 or len(theorem_endpoints) != 401:
        raise RuntimeError(
            f"endpoint coverage mismatch: all={len(endpoints)}, "
            f"theorems={len(theorem_endpoints)}"
        )

    endpoint_type_uses: dict[str, set[str]] = {}
    for endpoint in theorem_endpoints:
        env_row = environment_by_name.get(endpoint["resolved_name"])
        if env_row is None:
            raise RuntimeError(
                f"theorem endpoint missing from environment: {endpoint['resolved_name']}"
            )
        endpoint_type_uses[endpoint["resolved_name"]] = names(
            env_row["type_dependencies"]
        )

    definition_rows: list[dict[str, object]] = []
    private_definition_rows: list[dict[str, object]] = []
    load_bearing_names: set[str] = set()
    for definition in all_definition_candidates:
        name = definition["resolved_name"]
        citing_endpoints = sorted(
            endpoint_name
            for endpoint_name, dependencies in endpoint_type_uses.items()
            if name in dependencies
        )
        is_prelude = definition["path"] == "MatrixConcentration/Prelude.lean"
        is_load_bearing = is_prelude or len(citing_endpoints) >= 3
        if is_load_bearing:
            load_bearing_names.add(name)
        candidate_row = {
            "source_id": (
                definition["source_id"]
                if definition["visibility"] == "public"
                else definition["all_source_id"]
            ),
            "all_source_id": definition.get("all_source_id", ""),
            "visibility": definition["visibility"],
            "keyword": definition["keyword"],
            "module": definition["module"],
            "path": definition["path"],
            "line": definition["line"],
            "raw_name": definition["raw_name"],
            "resolved_name": name,
            "prelude_definition": str(is_prelude).lower(),
            "theorem_endpoint_direct_type_reference_count": len(
                citing_endpoints
            ),
            "theorem_endpoint_direct_type_referrers": ",".join(
                citing_endpoints
            ),
            "load_bearing": str(is_load_bearing).lower(),
            "load_bearing_reason": (
                "Prelude"
                if is_prelude
                else (
                    "directly referenced in elaborated types of >=3 "
                    "correspondence theorem endpoints"
                    if is_load_bearing
                    else "below threshold"
                )
            ),
        }
        if definition["visibility"] == "public":
            definition_rows.append(candidate_row)
        else:
            private_definition_rows.append(candidate_row)
    definition_fields = [
        "source_id",
        "all_source_id",
        "visibility",
        "keyword",
        "module",
        "path",
        "line",
        "raw_name",
        "resolved_name",
        "prelude_definition",
        "theorem_endpoint_direct_type_reference_count",
        "theorem_endpoint_direct_type_referrers",
        "load_bearing",
        "load_bearing_reason",
    ]
    write_tsv(
        LOGS / "v7_definition_type_references.tsv",
        definition_fields,
        definition_rows,
    )
    write_tsv(
        LOGS / "v7_private_definition_type_references.tsv",
        definition_fields,
        private_definition_rows,
    )
    write_tsv(
        LOGS / "v7_load_bearing_definitions.tsv",
        definition_fields,
        [
            row
            for row in definition_rows + private_definition_rows
            if row["load_bearing"] == "true"
        ],
    )

    direct_dependencies: dict[str, set[str]] = {}
    for declaration in all_resolved:
        env_row = environment_by_name[declaration["resolved_name"]]
        direct_dependencies[declaration["resolved_name"]] = (
            names(env_row["type_dependencies"])
            | names(env_row["value_dependencies"])
        ) & all_source_names

    source_reference_counts: dict[str, int] = {}
    source_referrers: dict[str, list[str]] = {}
    for target in sorted(all_source_names):
        referrers = sorted(
            source_name
            for source_name, dependencies in direct_dependencies.items()
            if source_name != target and target in dependencies
        )
        source_reference_counts[target] = len(referrers)
        source_referrers[target] = referrers

    dead_rows: list[dict[str, object]] = []
    for declaration in all_resolved:
        target = declaration["resolved_name"]
        # Correspondence theorems are deliberately terminal named book
        # results. Definition endpoints are API objects, not terminal
        # results, and therefore remain eligible for the dead-code census.
        if target in terminal_result_names:
            continue
        if source_reference_counts[target] != 0:
            continue
        dead_rows.append(
            {
                "module": declaration["module"],
                "path": declaration["path"],
                "line": declaration["line"],
                "keyword": declaration["keyword"],
                "visibility": declaration["visibility"],
                "raw_name": declaration["raw_name"],
                "resolved_name": target,
                "source_direct_reference_count": 0,
                "classification": "INFO",
                "exclusion_rule": (
                    "not a 401-row theorem-kind correspondence endpoint; "
                    "definition endpoints remain eligible"
                ),
            }
        )
    dead_fields = [
        "module",
        "path",
        "line",
        "keyword",
        "visibility",
        "raw_name",
        "resolved_name",
        "source_direct_reference_count",
        "classification",
        "exclusion_rule",
    ]
    write_tsv(LOGS / "v7_dead_code.tsv", dead_fields, dead_rows)
    write_tsv(
        LOGS / "v7_dead_code_private.tsv",
        dead_fields,
        [row for row in dead_rows if row["visibility"] == "private"],
    )

    reference_rows = [
        {
            "module": declaration["module"],
            "path": declaration["path"],
            "line": declaration["line"],
            "keyword": declaration["keyword"],
            "visibility": declaration["visibility"],
            "resolved_name": declaration["resolved_name"],
            "source_direct_reference_count": source_reference_counts[
                declaration["resolved_name"]
            ],
            "source_direct_referrers": ",".join(
                source_referrers[declaration["resolved_name"]]
            ),
            "correspondence_endpoint": str(
                declaration["resolved_name"] in endpoint_names
            ).lower(),
        }
        for declaration in all_resolved
    ]
    reference_fields = [
        "module",
        "path",
        "line",
        "keyword",
        "visibility",
        "resolved_name",
        "source_direct_reference_count",
        "source_direct_referrers",
        "correspondence_endpoint",
    ]
    write_tsv(
        LOGS / "v7_source_reference_counts.tsv",
        reference_fields,
        reference_rows,
    )
    # Retain the original evidence filename as a compatibility alias; its
    # contents also cover all public and private source declarations.
    write_tsv(
        LOGS / "v7_public_reference_counts.tsv",
        reference_fields,
        reference_rows,
    )

    all_definition_rows = definition_rows + private_definition_rows
    prelude_count = sum(
        row["prelude_definition"] == "true" for row in all_definition_rows
    )
    public_threshold_count = sum(
        int(row["theorem_endpoint_direct_type_reference_count"]) >= 3
        for row in definition_rows
    )
    private_threshold_count = sum(
        int(row["theorem_endpoint_direct_type_reference_count"]) >= 3
        for row in private_definition_rows
    )
    threshold_count = public_threshold_count + private_threshold_count
    summary = {
        "public_source_declarations": len(resolved),
        "all_source_declarations": len(all_resolved),
        "private_source_declarations": sum(
            row["visibility"] == "private" for row in all_resolved
        ),
        "public_definition_candidates_enumerated": len(definition_rows),
        "private_definition_candidates_enumerated": len(
            private_definition_rows
        ),
        "all_definition_candidates_enumerated": len(all_definition_rows),
        "public_definitions_enumerated": sum(
            row["keyword"] == "def" for row in definition_rows
        ),
        "private_definitions_enumerated": sum(
            row["keyword"] == "def" for row in private_definition_rows
        ),
        "public_structures_enumerated": sum(
            row["keyword"] == "structure" for row in definition_rows
        ),
        "private_structures_enumerated": sum(
            row["keyword"] == "structure" for row in private_definition_rows
        ),
        "public_classes_enumerated": sum(
            row["keyword"] == "class" for row in definition_rows
        ),
        "private_classes_enumerated": sum(
            row["keyword"] == "class" for row in private_definition_rows
        ),
        "correspondence_endpoints": len(endpoints),
        "correspondence_theorem_endpoints": len(theorem_endpoints),
        "prelude_definitions": prelude_count,
        "definitions_meeting_reference_threshold": threshold_count,
        "public_definitions_meeting_reference_threshold": (
            public_threshold_count
        ),
        "private_definitions_meeting_reference_threshold": (
            private_threshold_count
        ),
        "load_bearing_definitions_union": len(load_bearing_names),
        "dead_code_candidates_after_terminal_exclusion": len(dead_rows),
        "dead_code_public_candidates": sum(
            row["visibility"] == "public" for row in dead_rows
        ),
        "dead_code_private_candidates": sum(
            row["visibility"] == "private" for row in dead_rows
        ),
        "dependency_rule": (
            "direct constant occurrences in the elaborated type of each of "
            "the 401 theorem-kind correspondence endpoints"
        ),
        "dead_code_rule": (
            "zero direct type-or-value references from any other one of the "
            "1,525 source declarations (1,443 public plus 82 private); "
            "compiler-generated environment constants are excluded from graph "
            "nodes and the 401 theorem-kind correspondence endpoints are "
            "excluded as deliberately terminal named book results; "
            "definition endpoints remain eligible"
        ),
        "coverage_match": (
            len(resolved) == 1443
            and len(all_resolved) == 1525
            and len(definition_rows) == 135
            and len(private_definition_rows) == 14
            and len(endpoints) == 467
            and len(theorem_endpoints) == 401
        ),
    }
    (LOGS / "v7_dependency_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (LOGS / "v7_dependency_summary.log").write_text(
        "\n".join(
            [
                "V7 DEFINITION AND DEAD-CODE DEPENDENCY ANALYSIS",
                f"PUBLIC_SOURCE_DECLARATIONS {len(resolved)}",
                f"ALL_SOURCE_DECLARATIONS {len(all_resolved)}",
                "PRIVATE_SOURCE_DECLARATIONS "
                f"{sum(row['visibility'] == 'private' for row in all_resolved)}",
                "PUBLIC_DEFINITION_CANDIDATES_ENUMERATED "
                f"{len(definition_rows)}",
                "PRIVATE_DEFINITION_CANDIDATES_ENUMERATED "
                f"{len(private_definition_rows)}",
                "ALL_DEFINITION_CANDIDATES_ENUMERATED "
                f"{len(all_definition_rows)}",
                "PUBLIC_DEFINITIONS_ENUMERATED "
                f"{sum(row['keyword'] == 'def' for row in definition_rows)}",
                "PRIVATE_DEFINITIONS_ENUMERATED "
                f"{sum(row['keyword'] == 'def' for row in private_definition_rows)}",
                "PUBLIC_STRUCTURES_ENUMERATED "
                f"{sum(row['keyword'] == 'structure' for row in definition_rows)}",
                "PRIVATE_STRUCTURES_ENUMERATED "
                f"{sum(row['keyword'] == 'structure' for row in private_definition_rows)}",
                "PUBLIC_CLASSES_ENUMERATED "
                f"{sum(row['keyword'] == 'class' for row in definition_rows)}",
                "PRIVATE_CLASSES_ENUMERATED "
                f"{sum(row['keyword'] == 'class' for row in private_definition_rows)}",
                f"CORRESPONDENCE_ENDPOINTS {len(endpoints)}",
                f"CORRESPONDENCE_THEOREM_ENDPOINTS {len(theorem_endpoints)}",
                f"PRELUDE_DEFINITIONS {prelude_count}",
                f"DEFINITIONS_MEETING_REFERENCE_THRESHOLD {threshold_count}",
                "PUBLIC_DEFINITIONS_MEETING_REFERENCE_THRESHOLD "
                f"{public_threshold_count}",
                "PRIVATE_DEFINITIONS_MEETING_REFERENCE_THRESHOLD "
                f"{private_threshold_count}",
                f"LOAD_BEARING_DEFINITIONS_UNION {len(load_bearing_names)}",
                f"DEAD_CODE_AFTER_TERMINAL_EXCLUSION {len(dead_rows)}",
                "DEAD_CODE_PUBLIC "
                f"{sum(row['visibility'] == 'public' for row in dead_rows)}",
                "DEAD_CODE_PRIVATE "
                f"{sum(row['visibility'] == 'private' for row in dead_rows)}",
                f"COVERAGE_MATCH {str(summary['coverage_match']).lower()}",
                f"VERDICT {'PASS' if summary['coverage_match'] else 'FAIL'}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    if not summary["coverage_match"]:
        raise RuntimeError(f"dependency coverage mismatch: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
