#!/usr/bin/env python3
"""Validate and summarize the current-tree V5 trust-surface scan.

This analyzer is deliberately source-level.  It checks JSON/TSV agreement,
rejects every executable high-risk escape pattern, inventories all options,
and enumerates the exported instances whose carrier type is owned by
Mathlib.  Definitional-equality claims in the instance table are compiled by
``.audit_work/verification/RecertV5InstanceAudit.lean``.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from file_universe import ROOT, enumerate_universe
from lean_source_scanner import mask_lean_noncode


LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
DEFAULT_JSON = LOGS / "recert_v5_library.json"
DEFAULT_TSV = LOGS / "recert_v5_library.tsv"
DEFAULT_SUMMARY = LOGS / "recert_v5_trust_surface_summary.txt"
DEFAULT_OPTIONS = LOGS / "recert_v5_options.tsv"
DEFAULT_INSTANCES = LOGS / "recert_v5_global_instances.tsv"
DEFAULT_ALL_INSTANCES = LOGS / "recert_v5_all_instances.tsv"
DEFAULT_REVIEWABLE = LOGS / "recert_v5_reviewable_hits.tsv"
INSTANCE_HARNESS = (
    ROOT / ".audit_work" / "verification" / "RecertV5InstanceAudit.lean"
)

HIGH_RISK_PATTERNS = frozenset(
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

ALLOWED_OPTIONS = frozenset(
    {
        "maxHeartbeats",
        "linter.unusedSectionVars",
        "linter.unusedDecidableInType",
        "linter.unusedFintypeInType",
        "linter.style.setOption",
    }
)


@dataclass(frozen=True)
class InstanceSpec:
    target: str
    overlap_status: str
    evidence: str


MATHLIB_OWNED_INSTANCE_SPECS: dict[tuple[str, str], InstanceSpec] = {
    (
        "HighDimensionalProbability/Prelude/Matrix.lean",
        "instMeasurableSpaceRealMatrix",
    ): InstanceSpec(
        "MeasurableSpace (Matrix m n ℝ)",
        "DEF_EQ_CANONICAL_PRODUCT",
        "recert_real_matrix_measurable_defeq_pi",
    ),
    (
        "HighDimensionalProbability/Prelude/Matrix.lean",
        "instBorelSpaceRealMatrix",
    ): InstanceSpec(
        "BorelSpace (Matrix m n ℝ)",
        "CANONICAL_PRODUCT_BOREL",
        "recert_real_matrix_borel_proof_irrelevant",
    ),
    (
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean",
        "instMeasurableSpaceMatrix",
    ): InstanceSpec(
        "MeasurableSpace (Matrix m n ℂ)",
        "DEF_EQ_CANONICAL_PRODUCT",
        "recert_complex_matrix_measurable_defeq_pi",
    ),
    (
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean",
        "instBorelSpaceMatrix",
    ): InstanceSpec(
        "BorelSpace (Matrix m n ℂ)",
        "CANONICAL_PRODUCT_BOREL",
        "recert_complex_matrix_borel_proof_irrelevant",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instMeasurableSpacePermutation",
    ): InstanceSpec(
        "MeasurableSpace (Equiv.Perm (Fin n))",
        "DEF_EQ_TOP_LOCAL_DUPLICATE",
        (
            "recert_permutation_measurable_defeq_top; "
            "recert_permutation_no_exported_fallback; the second declaration "
            "in Appendix/Infra/SymmetricGroupCode.lean is local and also := ⊤"
        ),
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instMeasurableSpaceRealSquareMatrix",
    ): InstanceSpec(
        "MeasurableSpace (Matrix (Fin n) (Fin n) ℝ)",
        "DEF_EQ_SHARED_HDP_INSTANCE",
        "recert_real_square_measurable_defeq_shared",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instBorelSpaceRealSquareMatrix",
    ): InstanceSpec(
        "BorelSpace (Matrix (Fin n) (Fin n) ℝ)",
        "SHARED_HDP_BOREL",
        "recert_real_square_borel_proof_irrelevant",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instCompactSpaceOrthogonalGroup",
    ): InstanceSpec(
        "CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ)",
        "UNIQUE_EXPORTED_CONSTRUCTION",
        "recert_orthogonal_compact_no_fallback",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instMeasurableSpaceOrthogonalGroup",
    ): InstanceSpec(
        "MeasurableSpace (Matrix.orthogonalGroup (Fin n) ℝ)",
        "DEF_EQ_SUBTYPE_INSTANCE",
        "recert_orthogonal_measurable_defeq_subtype",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instBorelSpaceOrthogonalGroup",
    ): InstanceSpec(
        "BorelSpace (Matrix.orthogonalGroup (Fin n) ℝ)",
        "SUBTYPE_BOREL",
        "recert_orthogonal_borel_proof_irrelevant",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instCompactSpaceSpecialOrthogonalGroup",
    ): InstanceSpec(
        "CompactSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ)",
        "UNIQUE_EXPORTED_CONSTRUCTION",
        "recert_special_orthogonal_compact_no_fallback",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instMeasurableSpaceSpecialOrthogonalGroup",
    ): InstanceSpec(
        "MeasurableSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ)",
        "DEF_EQ_SUBTYPE_INSTANCE",
        "recert_special_orthogonal_measurable_defeq_subtype",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instBorelSpaceSpecialOrthogonalGroup",
    ): InstanceSpec(
        "BorelSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ)",
        "SUBTYPE_BOREL",
        "recert_special_orthogonal_borel_proof_irrelevant",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instContinuousInvSpecialOrthogonalGroup",
    ): InstanceSpec(
        "ContinuousInv (Matrix.specialOrthogonalGroup (Fin n) ℝ)",
        "UNIQUE_EXPORTED_CONSTRUCTION",
        "recert_special_orthogonal_continuous_inv_no_fallback",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instIsTopologicalGroupSpecialOrthogonalGroup",
    ): InstanceSpec(
        "IsTopologicalGroup (Matrix.specialOrthogonalGroup (Fin n) ℝ)",
        "UNIQUE_EXPORTED_CONSTRUCTION",
        "recert_special_orthogonal_topological_group_no_fallback",
    ),
    (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        "instContinuousInvOrthogonalGroup",
    ): InstanceSpec(
        "ContinuousInv (Matrix.orthogonalGroup (Fin n) ℝ)",
        "PROOF_IRRELEVANT_MATHLIB_UNITARY_FALLBACK",
        (
            "recert_orthogonal_continuous_inv_fallback_proof_irrelevant; "
            "orthogonalGroup is definitionally unitaryGroup, and Mathlib's "
            "generic ContinuousInv (unitary R) instance remains available"
        ),
    ),
}

INSTANCE_START = re.compile(
    r"(?m)^[ \t]*(?:(?P<noncomputable>noncomputable)[ \t]+)?"
    r"(?:(?P<scope>local|scoped)[ \t]+)?instance\b"
)
NAMED_INSTANCE = re.compile(
    r"(?m)^[ \t]*(?:noncomputable[ \t]+)?"
    r"(?:(?:local|scoped)[ \t]+)?instance[ \t]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
OWNED_TARGET_MARKERS = (
    "MeasurableSpace (Matrix",
    "BorelSpace (Matrix",
    "MeasurableSpace (Equiv.Perm",
    "CompactSpace (Matrix.orthogonalGroup",
    "MeasurableSpace (Matrix.orthogonalGroup",
    "BorelSpace (Matrix.orthogonalGroup",
    "ContinuousInv (Matrix.orthogonalGroup",
    "CompactSpace (Matrix.specialOrthogonalGroup",
    "MeasurableSpace (Matrix.specialOrthogonalGroup",
    "BorelSpace (Matrix.specialOrthogonalGroup",
    "ContinuousInv (Matrix.specialOrthogonalGroup",
    "IsTopologicalGroup (Matrix.specialOrthogonalGroup",
)


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def _read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def _header(code: str, offset: int) -> str:
    tail = code[offset : offset + 2000]
    ends = [
        match.start()
        for marker in (r":=", r"\bwhere\b")
        if (match := re.search(marker, tail)) is not None
    ]
    end = min(ends) if ends else min(len(tail), 1000)
    return " ".join(tail[:end].split())


def _line(code: str, offset: int) -> int:
    return code.count("\n", 0, offset) + 1


def _instance_rows() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    universe = enumerate_universe()
    paths = universe["file_walk_universe"]
    assert isinstance(paths, list)
    all_rows: list[dict[str, str]] = []
    owned_rows: list[dict[str, str]] = []
    observed_owned_keys: set[tuple[str, str]] = set()

    for relative in paths:
        path = ROOT / str(relative)
        source = path.read_text(encoding="utf-8")
        code, diagnostics = mask_lean_noncode(source)
        if diagnostics:
            raise ValueError(f"lexer diagnostics while scanning instances: {relative}")
        for match in INSTANCE_START.finditer(code):
            header = _header(code, match.start())
            name_match = NAMED_INSTANCE.match(code, match.start())
            name = name_match.group("name") if name_match else "<anonymous>"
            scope = match.group("scope") or "global"
            row = {
                "path": str(relative),
                "line": str(_line(code, match.start())),
                "scope": scope,
                "name": name,
                "header": header,
            }
            all_rows.append(row)
            if scope != "global" or not any(
                marker in header for marker in OWNED_TARGET_MARKERS
            ):
                continue
            key = (str(relative), name)
            spec = MATHLIB_OWNED_INSTANCE_SPECS.get(key)
            if spec is None:
                raise ValueError(
                    f"unclassified Mathlib-owned global instance {key}: {header}"
                )
            observed_owned_keys.add(key)
            owned_rows.append(
                {
                    **row,
                    "target": spec.target,
                    "overlap_status": spec.overlap_status,
                    "evidence": spec.evidence,
                }
            )

    missing = sorted(set(MATHLIB_OWNED_INSTANCE_SPECS) - observed_owned_keys)
    if missing:
        raise ValueError(f"expected Mathlib-owned instances not found: {missing}")
    if len(owned_rows) != len(MATHLIB_OWNED_INSTANCE_SPECS):
        raise ValueError("duplicate Mathlib-owned instance classification")
    harness_source = INSTANCE_HARNESS.read_text(encoding="utf-8")
    evidence_names = {
        name
        for spec in MATHLIB_OWNED_INSTANCE_SPECS.values()
        for name in re.findall(r"\brecert_[A-Za-z0-9_]+\b", spec.evidence)
    }
    missing_evidence = sorted(
        name for name in evidence_names if name not in harness_source
    )
    if missing_evidence:
        raise ValueError(
            f"instance evidence names absent from harness: {missing_evidence}"
        )
    return all_rows, owned_rows


def _write_rows(path: Path, fields: list[str], rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def analyze(
    json_path: Path,
    tsv_path: Path,
    summary_path: Path,
    options_path: Path,
    instances_path: Path,
    all_instances_path: Path,
    reviewable_path: Path,
) -> int:
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    summary = payload["summary"]
    hits = payload["hits"]
    tsv_rows = _read_tsv(tsv_path)
    errors: list[str] = []

    if summary.get("scanned_file_count") != 222:
        errors.append(
            f"library scan count is {summary.get('scanned_file_count')}, expected 222"
        )
    if summary.get("lex_diagnostic_count") != 0:
        errors.append("library scan has lexical diagnostics")
    json_identities = Counter(
        (
            str(hit["pattern_id"]),
            bool(hit["in_code"]),
            str(hit["path"]),
            int(hit["line"]),
            int(hit["column"]),
            str(hit["matched_text"]),
            str(hit["context"]),
        )
        for hit in hits
    )
    tsv_identities = Counter(
        (
            row["pattern_id"],
            row["in_code"].lower() == "true",
            row["path"],
            int(row["line"]),
            int(row["column"]),
            row["match"],
            row["context"],
        )
        for row in tsv_rows
    )
    if json_identities != tsv_identities:
        errors.append("JSON/TSV hit multisets differ")

    by_pattern = summary["by_pattern"]
    high_risk = {
        pattern_id: int(by_pattern[pattern_id]["code"])
        for pattern_id in sorted(HIGH_RISK_PATTERNS)
    }
    nonzero_high_risk = {
        pattern_id: count for pattern_id, count in high_risk.items() if count
    }
    if nonzero_high_risk:
        errors.append(f"executable high-risk V5 hits: {nonzero_high_risk}")

    option_rows: list[dict[str, str]] = []
    option_counts: Counter[str] = Counter()
    heartbeat_values: list[int] = []
    for hit in hits:
        if hit["pattern_id"] != "v5.set_option" or hit["in_code"] is not True:
            continue
        name = str(hit["matched_text"]).removeprefix("set_option ")
        option_counts[name] += 1
        if name not in ALLOWED_OPTIONS:
            errors.append(f"unclassified source option {name} at {hit['path']}:{hit['line']}")
        if name == "maxHeartbeats":
            value_match = re.search(r"\bset_option\s+maxHeartbeats\s+(\d+)", hit["context"])
            if value_match is None:
                errors.append(
                    f"could not parse heartbeat value at {hit['path']}:{hit['line']}"
                )
            else:
                value = int(value_match.group(1))
                heartbeat_values.append(value)
                if value <= 0:
                    errors.append(
                        f"nonpositive library heartbeat value at {hit['path']}:{hit['line']}"
                    )
        option_rows.append(
            {
                "path": str(hit["path"]),
                "line": str(hit["line"]),
                "name": name,
                "context": str(hit["context"]),
            }
        )

    all_instances, owned_instances = _instance_rows()
    _write_rows(
        options_path,
        ["path", "line", "name", "context"],
        option_rows,
    )
    _write_rows(
        all_instances_path,
        ["path", "line", "scope", "name", "header"],
        all_instances,
    )
    _write_rows(
        instances_path,
        [
            "path",
            "line",
            "scope",
            "name",
            "target",
            "overlap_status",
            "evidence",
            "header",
        ],
        owned_instances,
    )
    reviewable_patterns = {
        "v5.fact",
        "v5.irreducible_def",
        "v5.local_instance",
        "v5.notation",
        "v5.reducible",
    }
    reviewable_rows = [
        {
            "pattern_id": str(hit["pattern_id"]),
            "path": str(hit["path"]),
            "line": str(hit["line"]),
            "column": str(hit["column"]),
            "matched_text": str(hit["matched_text"]),
            "context": str(hit["context"]),
        }
        for hit in hits
        if hit["in_code"] is True
        and str(hit["pattern_id"]) in reviewable_patterns
    ]
    _write_rows(
        reviewable_path,
        [
            "pattern_id",
            "path",
            "line",
            "column",
            "matched_text",
            "context",
        ],
        reviewable_rows,
    )

    code_counts = {
        pattern_id: int(values["code"])
        for pattern_id, values in sorted(by_pattern.items())
    }
    raw_counts = {
        pattern_id: int(values["raw"])
        for pattern_id, values in sorted(by_pattern.items())
    }
    raw_hit_files = {str(hit["path"]) for hit in hits}
    code_hit_files = {
        str(hit["path"]) for hit in hits if hit["in_code"] is True
    }
    lines = [
        "V5 CURRENT-TREE TRUST-SURFACE ANALYSIS",
        "======================================",
        f"verdict: {'PASS' if not errors else 'FAIL'}",
        f"scanned_library_files: {summary.get('scanned_file_count')}",
        f"raw_hits: {summary.get('raw_hit_count')}",
        f"code_hits: {summary.get('code_hit_count')}",
        (
            "noncode_hits: "
            f"{int(summary.get('raw_hit_count', 0)) - int(summary.get('code_hit_count', 0))}"
        ),
        f"files_with_raw_hits: {len(raw_hit_files)}",
        f"files_with_code_hits: {len(code_hit_files)}",
        f"lex_diagnostics: {summary.get('lex_diagnostic_count')}",
        f"json_tsv_rows: {len(hits)}/{len(tsv_rows)}",
        f"executable_high_risk_hits: {sum(high_risk.values())}",
        f"all_instance_declarations: {len(all_instances)}",
        f"mathlib_owned_global_instances: {len(owned_instances)}",
        "",
        "[code counts by pattern]",
        *(f"{key}\t{value}" for key, value in code_counts.items()),
        "",
        "[raw counts by pattern]",
        *(f"{key}\t{value}" for key, value in raw_counts.items()),
        "",
        "[set_option counts]",
        *(f"{key}\t{value}" for key, value in sorted(option_counts.items())),
        (
            "maxHeartbeats_range\t"
            + (
                f"{min(heartbeat_values)}..{max(heartbeat_values)}"
                if heartbeat_values
                else "NONE"
            )
        ),
        "",
        "[errors]",
        *(errors or ["(none)"]),
    ]
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 1 if errors else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--library-json", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--library-tsv", type=Path, default=DEFAULT_TSV)
    parser.add_argument("--summary-output", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--options-output", type=Path, default=DEFAULT_OPTIONS)
    parser.add_argument("--instances-output", type=Path, default=DEFAULT_INSTANCES)
    parser.add_argument(
        "--all-instances-output", type=Path, default=DEFAULT_ALL_INSTANCES
    )
    parser.add_argument(
        "--reviewable-output", type=Path, default=DEFAULT_REVIEWABLE
    )
    args = parser.parse_args()
    return analyze(
        _resolve(args.library_json),
        _resolve(args.library_tsv),
        _resolve(args.summary_output),
        _resolve(args.options_output),
        _resolve(args.instances_output),
        _resolve(args.all_instances_output),
        _resolve(args.reviewable_output),
    )


if __name__ == "__main__":
    raise SystemExit(main())
