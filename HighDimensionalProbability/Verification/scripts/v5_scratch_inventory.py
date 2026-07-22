#!/usr/bin/env python3
"""Validate and summarize the final V5 scratch-surface census.

Scratch is intentionally outside the library verdict, but it is not silently
ignored.  This analyzer checks the JSON/TSV serializations against the live
``tmp/*.lean`` plus ``.audit_work/**/*.lean`` universe, separates the planted
scanner control from ordinary current audit harnesses and enumerated
historical files, and rejects unexpected executable escape-surface classes
outside that control.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from pathlib import Path

from file_universe import ROOT, enumerate_universe


LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
DEFAULT_JSON = LOGS / "recert_v5_scratch.json"
DEFAULT_TSV = LOGS / "recert_v5_scratch.tsv"
DEFAULT_SUMMARY = LOGS / "recert_v5_scratch_summary.txt"
DEFAULT_INVENTORY = LOGS / "recert_v5_scratch_inventory.tsv"

POSITIVE_CONTROL = (
    ".audit_work/verification/RecertV3V5ScannerPositive.lean"
)
NEGATIVE_CONTROL = (
    ".audit_work/verification/RecertV3V5ScannerNoncode.lean"
)
PRIOR_POSITIVE_CONTROL = ".audit_work/verification/scanner_positive.lean"
PRIOR_NEGATIVE_CONTROL = ".audit_work/verification/scanner_noncode.lean"
# Files born before the recertification start, plus the byte-restored
# AxiomAuditRecertification prototype, remain in the mandatory scratch census
# but are never accepted as evidence for this run.
HISTORICAL_NOT_CURRENT = frozenset(
    {
        ".audit_work/READMEProvedAxioms.lean",
        ".audit_work/verification/AxiomAudit.lean",
        ".audit_work/verification/AxiomAuditApiProbe.lean",
        ".audit_work/verification/AxiomAuditFullSurface.lean",
        ".audit_work/verification/AxiomAuditShard0.lean",
        ".audit_work/verification/AxiomAuditShard1.lean",
        ".audit_work/verification/AutoImplicitProbe.lean",
        ".audit_work/verification/AxiomAuditRecertification.lean",
        ".audit_work/verification/DefinitionSanity.lean",
        ".audit_work/verification/DefinitionSanityApiProbe.lean",
        ".audit_work/verification/DefinitionSanityFullSurface.lean",
        ".audit_work/verification/V6TierCCh5_7AxiomAudit.lean",
        ".audit_work/verification/V6TierCCh8_9AxiomAudit.lean",
        ".audit_work/verification/V6TierCPlantedBad.lean",
        ".audit_work/verification/V8PackageLint.lean",
        ".audit_work/verification/V8PackageLintFullSurface.lean",
        ".audit_work/verification/V9READMEProvedAxioms.lean",
        ".audit_work/verification/import_graph_positive.lean",
        ".audit_work/verification/v6_tier_a_positive.lean",
    }
)

# These constructs are expected in executable audit collectors and resource
# controls.  All other executable detector classes must remain confined to the
# planted positive control.
AUDIT_HARNESS_ALLOWED = frozenset(
    {
        "v5.set_option",
        "v5.run_cmd",
        "v5.partial_def",
    }
)


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def _read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def analyze(
    json_path: Path,
    tsv_path: Path,
    summary_path: Path,
    inventory_path: Path,
) -> int:
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    rows = _read_tsv(tsv_path)
    hits = payload.get("hits", [])
    summary = payload.get("summary", {})
    errors: list[str] = []

    def json_identity(
        row: dict[str, object],
    ) -> tuple[str, str, int, int, str, bool]:
        return (
            str(row["path"]),
            str(row["pattern_id"]),
            int(row["line"]),
            int(row["column"]),
            str(row["matched_text"]),
            bool(row["in_code"]),
        )

    json_identities = Counter(json_identity(hit) for hit in hits)
    tsv_identities = Counter(
        (
            row["path"],
            row["pattern_id"],
            int(row["line"]),
            int(row["column"]),
            row["match"],
            row["in_code"].lower() == "true",
        )
        for row in rows
    )
    if json_identities != tsv_identities:
        errors.append("JSON/TSV hit multisets differ")

    universe = enumerate_universe()
    tmp_scratch = universe["tmp_scratch"]
    audit_scratch = universe["audit_work_scratch"]
    assert isinstance(tmp_scratch, list)
    assert isinstance(audit_scratch, list)
    expected_paths = set(map(str, [*tmp_scratch, *audit_scratch]))
    if int(summary.get("scanned_file_count", -1)) != len(expected_paths):
        errors.append("summary scratch-file count differs from live enumeration")
    if int(summary.get("lex_diagnostic_count", -1)) != 0:
        errors.append("scratch scan has lexical diagnostics")

    by_path_pattern_code: Counter[tuple[str, str]] = Counter()
    by_path_pattern_raw: Counter[tuple[str, str]] = Counter()
    for hit in hits:
        key = (str(hit["path"]), str(hit["pattern_id"]))
        by_path_pattern_raw[key] += 1
        if hit["in_code"] is True:
            by_path_pattern_code[key] += 1

    inventory_path.parent.mkdir(parents=True, exist_ok=True)
    with inventory_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "path",
                "classification",
                "pattern_id",
                "raw_hits",
                "code_hits",
                "disposition",
            ]
        )
        for path, pattern in sorted(by_path_pattern_raw):
            raw_count = by_path_pattern_raw[(path, pattern)]
            code_count = by_path_pattern_code[(path, pattern)]
            if path == POSITIVE_CONTROL:
                classification = "CALIBRATION_POSITIVE"
                disposition = "EXPECTED_PLANT"
            elif path == NEGATIVE_CONTROL:
                classification = "CALIBRATION_NEGATIVE"
                disposition = (
                    "EXPECTED_NONCODE"
                    if code_count == 0
                    else "UNEXPECTED_EXECUTABLE_HIT"
                )
                if code_count:
                    errors.append(
                        f"negative control has executable {pattern} hit"
                    )
            elif path == PRIOR_POSITIVE_CONTROL:
                classification = "PRIOR_CALIBRATION_POSITIVE"
                disposition = "HISTORICAL_PLANT_NOT_CURRENT_EVIDENCE"
            elif path == PRIOR_NEGATIVE_CONTROL:
                classification = "PRIOR_CALIBRATION_NEGATIVE"
                disposition = (
                    "HISTORICAL_NONCODE_NOT_CURRENT_EVIDENCE"
                    if code_count == 0
                    else "UNEXPECTED_EXECUTABLE_HIT"
                )
                if code_count:
                    errors.append(
                        f"prior negative control has executable {pattern} hit"
                    )
            elif path in HISTORICAL_NOT_CURRENT:
                classification = "HISTORICAL_NOT_CURRENT"
                disposition = "ENUMERATED_NOT_CURRENT_EVIDENCE"
            elif path.startswith(".audit_work/verification/"):
                classification = "AUDIT_HARNESS"
                disposition = (
                    "EXPECTED_AUDIT_CONSTRUCT"
                    if code_count == 0 or pattern in AUDIT_HARNESS_ALLOWED
                    else "UNEXPECTED_AUDIT_CONSTRUCT"
                )
                if code_count and pattern not in AUDIT_HARNESS_ALLOWED:
                    errors.append(
                        f"unexpected executable scratch construct "
                        f"{pattern} in {path}"
                    )
            elif path.startswith(".audit_work/"):
                classification = "PRIOR_AUDIT_SCRATCH"
                disposition = (
                    "EXPECTED_AUDIT_CONSTRUCT"
                    if code_count == 0 or pattern in AUDIT_HARNESS_ALLOWED
                    else "UNEXPECTED_AUDIT_CONSTRUCT"
                )
                if code_count and pattern not in AUDIT_HARNESS_ALLOWED:
                    errors.append(
                        f"unexpected executable prior-audit construct "
                        f"{pattern} in {path}"
                    )
            elif path.startswith("tmp/"):
                classification = "KNOWN_TMP_SCRATCH"
                disposition = (
                    "NONCODE_ONLY"
                    if code_count == 0
                    else "UNEXPECTED_EXECUTABLE_HIT"
                )
                if code_count:
                    errors.append(
                        f"tmp scratch has executable {pattern} hit in {path}"
                    )
            else:
                classification = "UNCLASSIFIED_SCRATCH"
                disposition = "UNEXPECTED_PATH"
                errors.append(f"unclassified scratch path {path}")
            writer.writerow(
                [
                    path,
                    classification,
                    pattern,
                    raw_count,
                    code_count,
                    disposition,
                ]
            )
        for path in sorted(expected_paths - {key[0] for key in by_path_pattern_raw}):
            if path in HISTORICAL_NOT_CURRENT:
                classification = "HISTORICAL_NOT_CURRENT"
                disposition = "ENUMERATED_NOT_CURRENT_EVIDENCE"
            elif path.startswith("tmp/"):
                classification = "KNOWN_TMP_SCRATCH"
                disposition = "NO_MATCH"
            elif path.startswith(".audit_work/verification/"):
                classification = "AUDIT_HARNESS"
                disposition = "NO_MATCH"
            else:
                classification = "PRIOR_AUDIT_SCRATCH"
                disposition = "NO_MATCH"
            writer.writerow(
                [path, classification, "", 0, 0, disposition]
            )

    code_hits = [hit for hit in hits if hit["in_code"] is True]
    positive_code = [
        hit for hit in code_hits if hit["path"] == POSITIVE_CONTROL
    ]
    negative_code = [
        hit for hit in code_hits if hit["path"] == NEGATIVE_CONTROL
    ]
    profile_patterns = set(summary.get("by_pattern", {}))
    positive_patterns = {
        str(hit["pattern_id"]) for hit in positive_code
    }
    missing_positive_patterns = sorted(profile_patterns - positive_patterns)
    if missing_positive_patterns:
        errors.append(
            "positive control misses executable detector classes: "
            + ", ".join(missing_positive_patterns)
        )
    audit_code = [
        hit
        for hit in code_hits
        if str(hit["path"]).startswith(".audit_work/verification/")
        and hit["path"]
        not in {
            POSITIVE_CONTROL,
            NEGATIVE_CONTROL,
            PRIOR_POSITIVE_CONTROL,
            PRIOR_NEGATIVE_CONTROL,
        }
        and hit["path"] not in HISTORICAL_NOT_CURRENT
    ]
    prior_positive_code = [
        hit for hit in code_hits if hit["path"] == PRIOR_POSITIVE_CONTROL
    ]
    historical_paths = set(HISTORICAL_NOT_CURRENT) | {
        PRIOR_POSITIVE_CONTROL,
        PRIOR_NEGATIVE_CONTROL,
    }
    historical_code = [
        hit for hit in code_hits if hit["path"] in historical_paths
    ]
    current_audit_paths = {
        path
        for path in expected_paths
        if path.startswith(".audit_work/verification/")
        and path
        not in {
            POSITIVE_CONTROL,
            NEGATIVE_CONTROL,
            PRIOR_POSITIVE_CONTROL,
            PRIOR_NEGATIVE_CONTROL,
        }
        and path not in HISTORICAL_NOT_CURRENT
    }
    prior_audit_code = [
        hit
        for hit in code_hits
        if str(hit["path"]).startswith(".audit_work/")
        and not str(hit["path"]).startswith(".audit_work/verification/")
        and hit["path"] not in HISTORICAL_NOT_CURRENT
    ]
    tmp_code = [
        hit for hit in code_hits if str(hit["path"]).startswith("tmp/")
    ]
    hit_files = {str(hit["path"]) for hit in hits}
    code_files = {str(hit["path"]) for hit in code_hits}
    audit_code_files = {str(hit["path"]) for hit in audit_code}
    prior_audit_code_files = {
        str(hit["path"]) for hit in prior_audit_code
    }
    code_pattern_counts = Counter(str(hit["pattern_id"]) for hit in code_hits)

    lines = [
        "V5 FINAL SCRATCH-SURFACE ANALYSIS",
        "=================================",
        f"verdict: {'PASS' if not errors else 'FAIL'}",
        f"scratch_files: {len(expected_paths)}",
        f"raw_hits: {len(hits)}",
        f"code_hits: {len(code_hits)}",
        f"noncode_hits: {len(hits) - len(code_hits)}",
        f"files_with_raw_hits: {len(hit_files)}",
        f"files_with_code_hits: {len(code_files)}",
        f"positive_control_code_hits: {len(positive_code)}",
        f"positive_control_pattern_classes: {len(positive_patterns)}",
        f"negative_control_code_hits: {len(negative_code)}",
        f"prior_positive_control_code_hits: {len(prior_positive_code)}",
        (
            "historical_not_current_files: "
            f"{len(expected_paths & historical_paths)}"
        ),
        f"historical_not_current_code_hits: {len(historical_code)}",
        f"current_audit_harness_files: {len(current_audit_paths)}",
        f"audit_harness_code_hits: {len(audit_code)}",
        f"audit_harness_files_with_code_hits: {len(audit_code_files)}",
        f"prior_audit_scratch_code_hits: {len(prior_audit_code)}",
        (
            "prior_audit_scratch_files_with_code_hits: "
            f"{len(prior_audit_code_files)}"
        ),
        f"tmp_code_hits: {len(tmp_code)}",
        f"lex_diagnostics: {summary.get('lex_diagnostic_count', -1)}",
        f"json_tsv_rows: {len(hits)}/{len(rows)}",
        "",
        "[code counts by pattern]",
        *(
            f"{pattern}\t{count}"
            for pattern, count in sorted(code_pattern_counts.items())
        ),
        "",
        "[audit harness files with executable hits]",
        *(sorted(audit_code_files) or ["(none)"]),
        "",
        "[prior audit scratch files with executable hits]",
        *(sorted(prior_audit_code_files) or ["(none)"]),
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
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--tsv", type=Path, default=DEFAULT_TSV)
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    args = parser.parse_args()
    return analyze(
        _resolve(args.json),
        _resolve(args.tsv),
        _resolve(args.summary),
        _resolve(args.inventory),
    )


if __name__ == "__main__":
    raise SystemExit(main())
