#!/usr/bin/env python3
"""Build the complete manual V6 Tier-A semantic-review ledger.

The builder deliberately separates machine triage from semantic judgment:

* one or more scanner JSON files supply exact source statements and reasons;
* a hand-reviewed TSV supplies H/C/T/Q and the semantic verdict; and
* every observed hit must have exactly one review, with exactly the observed
  reason-ID set.

Additional scanner JSON files may be repeated on the command line.  This is
the merge point for the final auto-bound-binder scan: a new declaration or a
new reason fails closed until its manual-review row is added or updated.
"""

from __future__ import annotations

import argparse
import copy
import csv
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

from verify_exercise_reorganization import new_to_old_exercise_path


ROOT = Path(__file__).resolve().parents[3]
VERIFY = Path("HighDimensionalProbability/Verification")
DEFAULT_SCAN = (
    VERIFY / "logs/recert_v6_tier_a_final.json"
)
DEFAULT_REVIEWS = (
    VERIFY / "review/v6_tier_a_full_review_decisions.tsv"
)
DEFAULT_LEDGER = VERIFY / "review/recert_v6_tier_a_full_review.tsv"
DEFAULT_SUMMARY = VERIFY / "review/recert_v6_tier_a_full_review_summary.md"
DEFAULT_LOG = VERIFY / "logs/recert_v6_tier_a_full_review_builder_final.log"

DECISION_COLUMNS = (
    "path",
    "name",
    "qualified_name",
    "reviewed_reason_ids",
    "semantic_verdict",
    "h_hypotheses",
    "c_conclusion",
    "t_nontriviality",
    "q_quantifiers",
    "tier_c_required",
    "tier_c_witness_or_action",
    "citations",
    "notes",
)

LEDGER_COLUMNS = (
    "row_id",
    "path",
    "module",
    "start_line",
    "end_line",
    "kind",
    "name",
    "qualified_name",
    "source_statement",
    "source_conclusion",
    "reason_ids",
    "reason_details",
    "semantic_verdict",
    "h_hypotheses",
    "c_conclusion",
    "t_nontriviality",
    "q_quantifiers",
    "hctq",
    "tier_c_required",
    "tier_c_witness_or_action",
    "citations",
    "notes",
)

ALLOWED_VERDICTS = {
    "OK_FALSE_POSITIVE",
    "SUSPECT",
    "VACUOUS",
}
ALLOWED_TIER_C = {"YES", "NO"}


class ReviewFailure(RuntimeError):
    pass


def root_path(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def normalized_space(text: object) -> str:
    return " ".join(str(text or "").split())


def row_key(row: dict[str, object]) -> tuple[str, str]:
    path = str(row.get("path", "")).strip()
    name = str(row.get("name", "")).strip()
    if not path or not name:
        raise ReviewFailure(f"scanner/review row has no path/name: {row!r}")
    return path, name


def reason_rows(row: dict[str, object]) -> list[dict[str, str]]:
    raw = (
        row.get("triage_reasons")
        or row.get("auto_bound_reasons")
        or row.get("reasons")
        or []
    )
    if isinstance(raw, str):
        raw = [
            {"reason_id": item.strip(), "detail": ""}
            for item in raw.split(";")
            if item.strip()
        ]
    if not isinstance(raw, list):
        raise ReviewFailure(f"reason list has unsupported shape: {raw!r}")
    result: list[dict[str, str]] = []
    for item in raw:
        if isinstance(item, str):
            reason_id, detail = item, ""
        elif isinstance(item, dict):
            reason_id = str(
                item.get("reason_id") or item.get("id") or ""
            ).strip()
            detail = normalized_space(item.get("detail", ""))
        else:
            raise ReviewFailure(f"unsupported reason row: {item!r}")
        if not reason_id:
            raise ReviewFailure(f"reason row has no ID: {item!r}")
        result.append({"reason_id": reason_id, "detail": detail})
    return result


def declaration_list(data: object, source: Path) -> list[dict[str, object]]:
    if isinstance(data, list):
        rows = data
    elif isinstance(data, dict):
        rows = data.get("declarations")
        if rows is None:
            rows = data.get("hits")
    else:
        rows = None
    if not isinstance(rows, list):
        raise ReviewFailure(
            f"{source}: expected a declaration list or declarations/hits key"
        )
    if any(not isinstance(row, dict) for row in rows):
        raise ReviewFailure(f"{source}: a declaration entry is not an object")
    return rows  # type: ignore[return-value]


def merge_scan_rows(paths: Iterable[Path]) -> dict[tuple[str, str], dict[str, object]]:
    merged: dict[tuple[str, str], dict[str, object]] = {}
    for source in paths:
        absolute = root_path(source)
        data = json.loads(absolute.read_text(encoding="utf-8"))
        for raw in declaration_list(data, absolute):
            reasons = reason_rows(raw)
            if not reasons:
                continue
            key = row_key(raw)
            statement = normalized_space(
                raw.get("statement") or raw.get("source_statement")
            )
            conclusion = normalized_space(
                raw.get("conclusion") or raw.get("source_conclusion")
            )
            if not statement:
                raise ReviewFailure(
                    f"{absolute}: flagged {key!r} has no source statement"
                )
            if key not in merged:
                merged[key] = {
                    "path": key[0],
                    "name": key[1],
                    "module": str(raw.get("module", "")),
                    "start_line": raw.get("start_line", raw.get("line", "")),
                    "end_line": raw.get("end_line", ""),
                    "kind": str(raw.get("kind", "")),
                    "statement": statement,
                    "conclusion": conclusion,
                    "reasons": {},
                    "scan_sources": [],
                }
            current = merged[key]
            if normalized_space(current["statement"]) != statement:
                raise ReviewFailure(
                    f"{key!r}: scanner inputs disagree on source statement"
                )
            if conclusion and current["conclusion"] and (
                normalized_space(current["conclusion"]) != conclusion
            ):
                raise ReviewFailure(
                    f"{key!r}: scanner inputs disagree on conclusion"
                )
            if conclusion:
                current["conclusion"] = conclusion
            for field in ("module", "start_line", "end_line", "kind"):
                value = raw.get(field)
                if value not in (None, ""):
                    current[field] = value
            reason_map = current["reasons"]
            assert isinstance(reason_map, dict)
            for reason in reasons:
                reason_key = (reason["reason_id"], reason["detail"])
                reason_map[reason_key] = reason
            scan_sources = current["scan_sources"]
            assert isinstance(scan_sources, list)
            source_text = str(source)
            if source_text not in scan_sources:
                scan_sources.append(source_text)
    return merged


def read_decisions(path: Path) -> dict[tuple[str, str], dict[str, str]]:
    absolute = root_path(path)
    with absolute.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != DECISION_COLUMNS:
            raise ReviewFailure(
                f"{absolute}: expected columns {DECISION_COLUMNS!r}, "
                f"found {tuple(reader.fieldnames or ())!r}"
            )
        rows = [dict(row) for row in reader]
    decisions: dict[tuple[str, str], dict[str, str]] = {}
    for row in rows:
        key = row_key(row)
        if key in decisions:
            raise ReviewFailure(f"{absolute}: duplicate review for {key!r}")
        for field in DECISION_COLUMNS:
            row[field] = row[field].strip()
        if row["semantic_verdict"] not in ALLOWED_VERDICTS:
            raise ReviewFailure(
                f"{key!r}: invalid verdict {row['semantic_verdict']!r}"
            )
        if row["tier_c_required"] not in ALLOWED_TIER_C:
            raise ReviewFailure(
                f"{key!r}: invalid Tier-C value {row['tier_c_required']!r}"
            )
        for field in (
            "qualified_name",
            "reviewed_reason_ids",
            "h_hypotheses",
            "c_conclusion",
            "t_nontriviality",
            "q_quantifiers",
            "tier_c_witness_or_action",
            "citations",
            "notes",
        ):
            if not row[field]:
                raise ReviewFailure(f"{key!r}: empty review field {field}")
        if (
            row["semantic_verdict"] == "VACUOUS"
            and row["tier_c_required"] != "YES"
        ):
            raise ReviewFailure(
                f"{key!r}: a VACUOUS row must demand Tier-C/source repair"
            )
        decisions[key] = row
    return decisions


def stable_row_id(path: str, name: str) -> str:
    # A physical Exercise-tree move must not mint new semantic review IDs.
    # Normalize the current path to its certified pre-reorganization identity
    # while retaining the current path in every source-location field.
    identity_path = new_to_old_exercise_path(path)
    digest = hashlib.sha256(f"{identity_path}\0{name}".encode()).hexdigest()[:16]
    return f"tier-a-{digest}"


def build_ledger(
    scans: dict[tuple[str, str], dict[str, object]],
    decisions: dict[tuple[str, str], dict[str, str]],
) -> list[dict[str, str]]:
    missing = sorted(set(scans) - set(decisions))
    extra = sorted(set(decisions) - set(scans))
    if missing or extra:
        raise ReviewFailure(
            "manual-review coverage is not exact; "
            f"missing={missing!r}; extra={extra!r}"
        )
    ledger: list[dict[str, str]] = []
    for key, scan in scans.items():
        decision = decisions[key]
        reason_map = scan["reasons"]
        assert isinstance(reason_map, dict)
        reasons = sorted(
            reason_map.values(),
            key=lambda row: (row["reason_id"], row["detail"]),
        )
        observed_reason_ids = sorted({row["reason_id"] for row in reasons})
        reviewed_reason_ids = sorted(
            item
            for item in decision["reviewed_reason_ids"].split(";")
            if item
        )
        if reviewed_reason_ids != observed_reason_ids:
            raise ReviewFailure(
                f"{key!r}: reviewed reasons {reviewed_reason_ids!r} do not "
                f"match observed reasons {observed_reason_ids!r}"
            )
        hctq = " ".join(
            (
                f"H({decision['h_hypotheses']})",
                f"C({decision['c_conclusion']})",
                f"T({decision['t_nontriviality']})",
                f"Q({decision['q_quantifiers']})",
            )
        )
        ledger.append(
            {
                "row_id": stable_row_id(*key),
                "path": key[0],
                "module": str(scan["module"]),
                "start_line": str(scan["start_line"]),
                "end_line": str(scan["end_line"]),
                "kind": str(scan["kind"]),
                "name": key[1],
                "qualified_name": decision["qualified_name"],
                "source_statement": str(scan["statement"]),
                "source_conclusion": str(scan["conclusion"]),
                "reason_ids": ";".join(observed_reason_ids),
                "reason_details": " | ".join(
                    f"{row['reason_id']}: {row['detail']}" for row in reasons
                ),
                "semantic_verdict": decision["semantic_verdict"],
                "h_hypotheses": decision["h_hypotheses"],
                "c_conclusion": decision["c_conclusion"],
                "t_nontriviality": decision["t_nontriviality"],
                "q_quantifiers": decision["q_quantifiers"],
                "hctq": hctq,
                "tier_c_required": decision["tier_c_required"],
                "tier_c_witness_or_action": decision[
                    "tier_c_witness_or_action"
                ],
                "citations": decision["citations"],
                "notes": decision["notes"],
            }
        )
    ledger.sort(
        key=lambda row: (
            row["path"],
            int(row["start_line"] or 0),
            row["name"],
        )
    )
    return ledger


def calibrate_auto_bound_merge_contract(
    scans: Sequence[Path],
    merged: dict[tuple[str, str], dict[str, object]],
    decisions: dict[tuple[str, str], dict[str, str]],
) -> None:
    """Prove duplicate merging and fail-closed handling of a new reason."""

    if not scans or not merged:
        raise ReviewFailure("merge calibration requires a nonempty scan")
    once = merge_scan_rows([scans[0]])
    twice = merge_scan_rows([scans[0], scans[0]])
    if once != twice:
        raise ReviewFailure("duplicate scanner input is not idempotent")
    planted = copy.deepcopy(merged)
    key = sorted(planted)[0]
    reasons = planted[key]["reasons"]
    assert isinstance(reasons, dict)
    reasons[("auto_bound_binder", "planted merge calibration")] = {
        "reason_id": "auto_bound_binder",
        "detail": "planted merge calibration",
    }
    try:
        build_ledger(planted, decisions)
    except ReviewFailure as error:
        if "reviewed reasons" not in str(error):
            raise ReviewFailure(
                "planted auto-bound reason failed for the wrong cause: "
                f"{error}"
            ) from error
    else:
        raise ReviewFailure(
            "planted auto-bound reason escaped manual-review coverage"
        )


def render_tsv(rows: Sequence[dict[str, str]]) -> str:
    from io import StringIO

    buffer = StringIO()
    writer = csv.DictWriter(
        buffer,
        fieldnames=LEDGER_COLUMNS,
        delimiter="\t",
        lineterminator="\n",
    )
    writer.writeheader()
    writer.writerows(rows)
    return buffer.getvalue()


def render_summary(
    rows: Sequence[dict[str, str]], scans: Sequence[Path]
) -> str:
    verdicts = Counter(row["semantic_verdict"] for row in rows)
    reasons = Counter(
        reason
        for row in rows
        for reason in row["reason_ids"].split(";")
        if reason
    )
    tier_c = [row for row in rows if row["tier_c_required"] == "YES"]
    gradient = next(
        (
            row
            for row in rows
            if row["qualified_name"]
            == "BernoulliLSI.gradient_term_symmetric"
        ),
        None,
    )
    lines = [
        "# V6 Tier-A full semantic review",
        "",
        f"Reviewed machine-red-flag declarations: **{len(rows)}**.",
        "",
        f"- `OK_FALSE_POSITIVE`: **{verdicts['OK_FALSE_POSITIVE']}**",
        f"- `SUSPECT`: **{verdicts['SUSPECT']}**",
        f"- `VACUOUS`: **{verdicts['VACUOUS']}**",
        f"- Tier-C/source-repair required: **{len(tier_c)}**",
        "",
        "The source statement column is the scanner's exact token content with",
        "whitespace normalized. Each row separately records H (joint",
        "satisfiability), C (conclusion substance), T (nontrivial model/domain),",
        "and Q (quantifier/binder integrity). A semantic verdict does not",
        "override V1 buildability, V3 placeholder, or V4 axiom findings.",
        "",
        "## Reason inventory",
        "",
        "| Reason | Rows |",
        "|---|---:|",
    ]
    lines.extend(f"| `{name}` | {count} |" for name, count in sorted(reasons.items()))
    lines.extend(
        [
            "",
            "## Tier-C and repair queue",
            "",
            "| Declaration | Verdict | Required action/witness |",
            "|---|---|---|",
        ]
    )
    lines.extend(
        f"| `{row['qualified_name']}` | `{row['semantic_verdict']}` | "
        f"{row['tier_c_witness_or_action']} |"
        for row in tier_c
    )
    if gradient is not None:
        lines.extend(
            [
                "",
                "## `gradient_term_symmetric`",
                "",
                "This declaration is not dismissed as a scanner false positive.",
                "Its two displayed integrals are literally identical and its proof",
                "is `rfl`; a source-wide exact-name search finds no consumer beyond",
                "the declaration. It is therefore classified `VACUOUS`. A",
                "nonzero `Fin 1` Boolean-indicator integral is proposed as the",
                "named calibration witness, but that witness cannot rehabilitate",
                "the current reflexive endpoint: the source statement itself must",
                "first be repaired to express the intended coordinate symmetry.",
            ]
        )
    lines.extend(
        [
            "",
            "## Merge contract for the final scanner",
            "",
            "The builder accepts repeated `--scan-json` arguments. It unions",
            "reason rows for an identical `(path, name, statement)` and fails",
            "closed if a later auto-bound-binder hit has no manual decision or",
            "adds an unreviewed reason ID. After appending/updating the decision",
            "TSV, rerunning the builder deterministically regenerates this ledger",
            "and summary.",
            "",
            "Scanner inputs for this snapshot:",
            "",
        ]
    )
    lines.extend(f"- `{path}`" for path in scans)
    return "\n".join(lines) + "\n"


def write(path: Path, text: str) -> None:
    absolute = root_path(path)
    absolute.parent.mkdir(parents=True, exist_ok=True)
    absolute.write_text(text, encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--scan-json",
        action="append",
        type=Path,
        help=(
            "scanner JSON to merge; repeat for final auto-bound-binder hits "
            f"(default: {DEFAULT_SCAN})"
        ),
    )
    parser.add_argument("--reviews", type=Path, default=DEFAULT_REVIEWS)
    parser.add_argument("--output", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--log", type=Path, default=DEFAULT_LOG)
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="validate and compare existing generated files without rewriting",
    )
    args = parser.parse_args(argv)
    scans = args.scan_json or [DEFAULT_SCAN]
    try:
        merged = merge_scan_rows(scans)
        decisions = read_decisions(args.reviews)
        rows = build_ledger(merged, decisions)
        calibrate_auto_bound_merge_contract(scans, merged, decisions)
        ledger_text = render_tsv(rows)
        summary_text = render_summary(rows, scans)
        verdicts = Counter(row["semantic_verdict"] for row in rows)
        log_text = "\n".join(
            [
                "V6 Tier-A full semantic review builder",
                "overall: PASS",
                f"scanner_inputs: {len(scans)}",
                f"reviewed_hits: {len(rows)}",
                f"verdict_counts: {dict(sorted(verdicts.items()))}",
                "tier_c_required: "
                f"{sum(row['tier_c_required'] == 'YES' for row in rows)}",
                "coverage: EXACT",
                "reason_sets: EXACT",
                "auto_bound_merge_contract: READY_FAIL_CLOSED",
                "duplicate_merge_calibration: PASS",
                "planted_auto_bound_reason_calibration: REJECT",
                "",
            ]
        )
        if args.check_only:
            comparisons = (
                (args.output, ledger_text),
                (args.summary, summary_text),
                (args.log, log_text),
            )
            for path, expected in comparisons:
                absolute = root_path(path)
                if not absolute.exists():
                    raise ReviewFailure(f"{absolute}: generated artifact missing")
                if absolute.read_text(encoding="utf-8") != expected:
                    raise ReviewFailure(f"{absolute}: generated artifact is stale")
        else:
            write(args.output, ledger_text)
            write(args.summary, summary_text)
            write(args.log, log_text)
        sys.stdout.write(log_text)
        return 0
    except (OSError, ValueError, json.JSONDecodeError, ReviewFailure) as error:
        failure = (
            "V6 Tier-A full semantic review builder\n"
            "overall: FAIL\n"
            f"error: {error}\n"
        )
        if not args.check_only:
            write(args.log, failure)
        print(failure, file=sys.stderr, end="")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
