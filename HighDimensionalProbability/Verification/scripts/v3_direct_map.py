#!/usr/bin/env python3
"""Map every executable V3 placeholder token to its Exercise declaration."""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from pathlib import Path

from v3_v4_reconcile import (
    DEFAULT_EXERCISES,
    DEFAULT_V3,
    DIRECT_OUT,
    _direct_textual_sorries,
)


ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
SUMMARY_OUT = LOGS / "v3_direct_sorry_summary.txt"
DEFAULT_V3_TSV = LOGS / "v3_library.tsv"


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def analyze(
    v3_path: Path,
    v3_tsv_path: Path,
    exercise_path: Path,
    direct_output: Path,
    summary_output: Path,
) -> int:
    mapped, errors = _direct_textual_sorries(v3_path, exercise_path)
    payload = json.loads(v3_path.read_text(encoding="utf-8"))
    hits = payload["hits"]
    by_pattern = payload["summary"]["by_pattern"]
    with v3_tsv_path.open(encoding="utf-8", newline="") as handle:
        tsv_rows = list(csv.DictReader(handle, delimiter="\t"))
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
    identity_mismatches = json_identities != tsv_identities
    if identity_mismatches:
        errors.append("V3 JSON/TSV hit multisets differ")

    direct_output.parent.mkdir(parents=True, exist_ok=True)
    with direct_output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(["name", "classification", "path", "sorry_line"])
        for declaration, line in sorted(
            mapped, key=lambda item: (item[0].path, item[1], item[0].endpoint)
        ):
            writer.writerow(
                [declaration.endpoint, "EXERCISE-SORRY", declaration.path, line]
            )

    endpoints = [declaration.endpoint for declaration, _line in mapped]
    paths = {declaration.path for declaration, _line in mapped}
    non_exercise_paths = sorted(
        path
        for path in paths
        if "/Exercise/" not in path or not path.endswith(".lean")
    )
    appendix_code_sorries = [
        hit
        for hit in hits
        if hit["pattern_id"] == "v3.sorry"
        and hit["in_code"] is True
        and str(hit["path"]).startswith("HighDimensionalProbability/Appendix")
    ]
    legacy_code_hits = [
        hit
        for hit in hits
        if hit["in_code"] is True
        and hit["pattern_id"]
        in {
            "v3.external_sorry_marker",
            "v3.forward_sorry_marker",
            "v3.unresolved_proof_marker",
        }
    ]
    other_placeholder_code_hits = [
        hit
        for hit in hits
        if hit["in_code"] is True
        and hit["pattern_id"]
        in {
            "v3.admit",
            "v3.sorryAx",
            "v3.proof_wanted",
            "v3.exit",
            "v3.stop",
            "v3.todo",
            "v3.wip",
        }
    ]
    appendix_unresolved_hits = [
        hit
        for hit in hits
        if hit["pattern_id"] == "v3.appendix_unresolved_marker"
    ]
    checks = {
        "mapped_direct_sorry_declarations": len(mapped),
        "unique_direct_sorry_declarations": len(set(endpoints)),
        "exercise_leaf_files_with_sorry": len(paths),
        "raw_sorry_tokens": by_pattern["v3.sorry"]["raw"],
        "code_sorry_tokens": by_pattern["v3.sorry"]["code"],
        "raw_exercise_sorry_markers": by_pattern["v3.exercise_sorry_marker"][
            "raw"
        ],
        "raw_appendix_unresolved_markers": len(appendix_unresolved_hits),
        "code_appendix_unresolved_markers": sum(
            hit["in_code"] is True for hit in appendix_unresolved_hits
        ),
        "appendix_code_sorries": len(appendix_code_sorries),
        "legacy_marker_code_hits": len(legacy_code_hits),
        "other_placeholder_code_hits": len(other_placeholder_code_hits),
        "non_exercise_sorry_paths": len(non_exercise_paths),
        "mapping_errors": len(errors),
        "scanned_library_files": payload["summary"]["scanned_file_count"],
        "lex_diagnostics": payload["summary"]["lex_diagnostic_count"],
        "json_tsv_raw_rows": f"{len(hits)}/{len(tsv_rows)}",
        "json_tsv_code_rows": (
            f"{sum(hit['in_code'] is True for hit in hits)}/"
            f"{sum(row['in_code'].lower() == 'true' for row in tsv_rows)}"
        ),
        "json_tsv_identity_mismatches": int(identity_mismatches),
    }
    status = (
        "PASS"
        if checks["mapped_direct_sorry_declarations"] == 228
        and checks["unique_direct_sorry_declarations"] == 228
        and checks["exercise_leaf_files_with_sorry"] == 46
        and checks["code_sorry_tokens"] == 228
        and checks["raw_appendix_unresolved_markers"] == 0
        and checks["code_appendix_unresolved_markers"] == 0
        and checks["appendix_code_sorries"] == 0
        and checks["legacy_marker_code_hits"] == 0
        and checks["other_placeholder_code_hits"] == 0
        and checks["non_exercise_sorry_paths"] == 0
        and checks["mapping_errors"] == 0
        and checks["scanned_library_files"] == 222
        and checks["lex_diagnostics"] == 0
        and checks["json_tsv_raw_rows"] == "462/462"
        and checks["json_tsv_code_rows"] == "228/228"
        and checks["json_tsv_identity_mismatches"] == 0
        else "FAIL"
    )
    lines = ["V3 DIRECT PLACEHOLDER MAPPING", "=============================", f"status: {status}"]
    lines.extend(f"{key}: {value}" for key, value in checks.items())
    lines.extend(["", "[errors]"])
    lines.extend(errors or ["(none)"])
    lines.extend(["", "[non_exercise_sorry_paths]"])
    lines.extend(non_exercise_paths or ["(none)"])
    summary_output.parent.mkdir(parents=True, exist_ok=True)
    summary_output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    print(f"direct_table: {direct_output.relative_to(ROOT)}")
    print(f"summary: {summary_output.relative_to(ROOT)}")
    return 0 if status == "PASS" else 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--v3-json",
        type=Path,
        default=DEFAULT_V3.relative_to(ROOT),
    )
    parser.add_argument(
        "--v3-tsv",
        type=Path,
        default=DEFAULT_V3_TSV.relative_to(ROOT),
    )
    parser.add_argument(
        "--exercise-inventory",
        type=Path,
        default=DEFAULT_EXERCISES.relative_to(ROOT),
    )
    parser.add_argument(
        "--direct-output",
        type=Path,
        default=DIRECT_OUT.relative_to(ROOT),
    )
    parser.add_argument(
        "--summary-output",
        type=Path,
        default=SUMMARY_OUT.relative_to(ROOT),
    )
    args = parser.parse_args()
    return analyze(
        _resolve(args.v3_json),
        _resolve(args.v3_tsv),
        _resolve(args.exercise_inventory),
        _resolve(args.direct_output),
        _resolve(args.summary_output),
    )


if __name__ == "__main__":
    raise SystemExit(main())
