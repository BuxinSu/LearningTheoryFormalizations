#!/usr/bin/env python3
"""Create a fresh fail-closed V7 review register from current evidence.

Previously accepted citation packets are used only as candidate semantic
review text.  Every promoted citation requires byte-identical old/current
kernel types for both the target and citation, is re-resolved in the current
candidate inventory, is re-anchored in current source, and is rechecked
against the fresh V4 axiom ledger.  Rows without all of that current evidence
are emitted as explicit ``UNVERIFIED_SANITY`` findings.
"""

from __future__ import annotations

import argparse
import collections
import csv
import datetime as dt
import sys
from pathlib import Path

import v7_definition_review as review
from definition_sanity import (
    CANDIDATE_COLUMNS,
    LOAD_BEARING_COLUMNS,
    module_to_source_path,
)


ROOT = Path(__file__).resolve().parents[3]
VERIFY = ROOT / "HighDimensionalProbability" / "Verification"
LOGS = VERIFY / "logs"
REVIEW = VERIFY / "review"
OLD_REVIEW = REVIEW
OUTPUT_DIR = REVIEW / "recert_v7_definition_review"
DECISIONS = REVIEW / "recert_v7_semantic_decisions.tsv"

LOAD_BEARING = LOGS / "recert_definition_load_bearing.tsv"
CANDIDATES = LOGS / "recert_definition_nontriviality_candidates.tsv"
V4 = LOGS / "recert_axiom_audit.tsv"
OLD_TYPES = LOGS / "axiom_declaration_types.tsv"
CURRENT_TYPES = LOGS / "recert_axiom_declaration_types.tsv"
VALIDATION = LOGS / "recert_v7_definition_review_validation.txt"
SUMMARY = OUTPUT_DIR / "recert_v7_definition_review_summary.txt"
FRAMEWORK_SUMMARY = OUTPUT_DIR / "v7_definition_review_framework_summary.txt"
WITNESS_EVIDENCE = LOGS / "recert_definition_witness_evidence.tsv"
WITNESS_SOURCE = (
    VERIFY / "scripts" / "witnesses" / "RecertV7Nontriviality.lean"
)
WITNESS_MODULE = (
    "HighDimensionalProbability.Verification.scripts.witnesses."
    "RecertV7Nontriviality"
)
WITNESS_BUILD_LOG = LOGS / "recert_v7_nontriviality_witness_build.log"
WITNESS_COLLECTOR_SOURCE = (
    ROOT
    / ".audit_work"
    / "verification"
    / "RecertV7NontrivialityCollector.lean"
)
WITNESS_COLLECTOR_LOG = (
    LOGS / "recert_v7_nontriviality_witness_collector.log"
)

DECISION_COLUMNS = (
    "name",
    "review_status",
    "evidence_name",
    "semantic_nontriviality_claim",
    "nondegenerate_model",
    "constant_or_zero_collapse_check",
    "junk_or_empty_boundary_check",
    "measure_or_typeclass_check",
    "review_rationale",
)
SEMANTIC_COLUMNS = DECISION_COLUMNS[3:]


class MigrationFailure(RuntimeError):
    pass


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def old_rows() -> dict[str, dict[str, str]]:
    rows: dict[str, dict[str, str]] = {}
    for path in sorted(OLD_REVIEW.glob("v7_definition_review_shard_*.tsv")):
        for row in read_tsv(path):
            if row["name"] in rows:
                raise MigrationFailure(f"duplicate old review name {row['name']}")
            rows[row["name"]] = row
    return rows


def v4_rows() -> dict[str, dict[str, str]]:
    rows = read_tsv(V4)
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        if row["name"] in result:
            raise MigrationFailure(f"duplicate fresh V4 name {row['name']}")
        result[row["name"]] = row
    return result


def type_fingerprints(
    path: Path, required_names: set[str]
) -> dict[str, tuple[str, ...]]:
    """Stream exact kernel-type fields needed to reject statement drift.

    The raw declaration-type dump is roughly gigabyte-scale.  Retaining every
    row would make recertification depend on excessive memory even though the
    semantic register needs only its current targets and proposed citations.
    """
    required = (
        "name",
        "kind",
        "level_params",
        "binder_count",
        "type_raw",
        "conclusion_raw",
    )
    result: dict[str, tuple[str, ...]] = {}
    csv.field_size_limit(sys.maxsize)
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if reader.fieldnames is None or any(
            field not in reader.fieldnames for field in required
        ):
            raise MigrationFailure(
                f"{path}: incomplete declaration-type schema"
            )
        for row in reader:
            name = row["name"]
            if name not in required_names:
                continue
            if name in result:
                raise MigrationFailure(
                    f"{path}: duplicate declaration type {name}"
                )
            result[name] = tuple(row[field] for field in required[1:])
    return result


def candidate_rows() -> dict[tuple[str, str], dict[str, str]]:
    rows = review._read_tsv(CANDIDATES, CANDIDATE_COLUMNS)
    return {(row["target"], row["candidate_theorem"]): row for row in rows}


def decision_rows() -> dict[str, dict[str, str]]:
    rows = review._read_tsv(DECISIONS, DECISION_COLUMNS)
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        name = row["name"]
        if not name or name in result:
            raise MigrationFailure(
                f"{DECISIONS}: empty or duplicate decision name {name!r}"
            )
        if row["review_status"] not in {
            "VERIFIED_CITATION",
            "VERIFIED_WITNESS",
            "UNVERIFIED_SANITY",
        }:
            raise MigrationFailure(
                f"{DECISIONS}: unsupported status for {name}: "
                f"{row['review_status']!r}"
            )
        if not row["review_rationale"]:
            raise MigrationFailure(
                f"{DECISIONS}: {name} lacks a current review rationale"
            )
        if row["review_status"] != "UNVERIFIED_SANITY":
            missing = [
                field for field in SEMANTIC_COLUMNS if not row[field]
            ]
            if missing or not row["evidence_name"]:
                raise MigrationFailure(
                    f"{DECISIONS}: incomplete positive evidence decision for "
                    f"{name}: missing={missing!r}"
                )
        result[name] = row
    return result


def collector_rows() -> dict[str, dict[str, str]]:
    if not WITNESS_COLLECTOR_LOG.is_file():
        raise MigrationFailure(
            f"missing witness collector log {WITNESS_COLLECTOR_LOG}"
        )
    result: dict[str, dict[str, str]] = {}
    for line in WITNESS_COLLECTOR_LOG.read_text(
        encoding="utf-8", errors="replace"
    ).splitlines():
        if not line.startswith(review.COLLECTOR_PREFIX + "\t"):
            continue
        cells = line.split("\t")
        if len(cells) != 7:
            raise MigrationFailure(
                f"malformed witness collector row: {line[:200]!r}"
            )
        (
            _prefix,
            module,
            name,
            kind,
            private_user_name,
            axioms,
            type_dependencies,
        ) = cells
        if name in result:
            raise MigrationFailure(
                f"duplicate witness collector row for {name}"
            )
        result[name] = {
            "module": module,
            "name": name,
            "kind": kind,
            "private_user_name": private_user_name,
            "axioms": axioms,
            "type_dependencies": type_dependencies,
        }
    if not result:
        raise MigrationFailure("witness collector emitted no marker rows")
    return result


def write_witness_evidence(
    decisions: dict[str, dict[str, str]],
    collected: dict[str, dict[str, str]],
) -> None:
    rows: list[dict[str, str]] = []
    source = WITNESS_SOURCE.relative_to(ROOT).as_posix()
    collector_source = WITNESS_COLLECTOR_SOURCE.relative_to(ROOT).as_posix()
    build_log = WITNESS_BUILD_LOG.relative_to(ROOT).as_posix()
    collector_log = WITNESS_COLLECTOR_LOG.relative_to(ROOT).as_posix()
    for name, decision in sorted(decisions.items()):
        if decision["review_status"] != "VERIFIED_WITNESS":
            continue
        witness = decision["evidence_name"]
        measured = collected.get(witness)
        if measured is None:
            raise MigrationFailure(
                f"{name}: missing collector row for witness {witness}"
            )
        dependencies = {
            item
            for item in measured["type_dependencies"].split(";")
            if item
        }
        if name not in dependencies:
            raise MigrationFailure(
                f"{name}: witness {witness} lacks the direct type dependency"
            )
        if (
            measured["module"] != WITNESS_MODULE
            or measured["kind"] != "theorem"
        ):
            raise MigrationFailure(
                f"{name}: invalid measured witness module/kind {measured}"
            )
        if review._axiom_set(measured["axioms"]) - review.ALLOWED_AXIOMS:
            raise MigrationFailure(
                f"{name}: witness {witness} has disallowed axioms"
            )
        rows.append(
            {
                "definition": name,
                "witness": witness,
                "witness_module": WITNESS_MODULE,
                "source_path": source,
                "build_log": build_log,
                "collector_source": collector_source,
                "collector_log": collector_log,
            }
        )
    review._write_tsv(
        WITNESS_EVIDENCE, review.WITNESS_EVIDENCE_COLUMNS, rows
    )


def exact_anchor(
    *,
    target: str,
    evidence: str,
    candidate: dict[str, str],
    v4: dict[str, str],
) -> str:
    source = module_to_source_path(candidate["candidate_module"])
    problems: list[str] = []
    line = review._resolve_theorem_anchor(
        module=candidate["candidate_module"],
        name=evidence,
        private_user_name=v4.get("private_user_name", ""),
        source_relative=source,
        context=f"recert citation {target}",
        problems=problems,
    )
    if problems or line is None:
        raise MigrationFailure(
            f"cannot re-anchor {target} via {evidence}: {problems}"
        )
    return f"{source}:{line}"


def residual(row: dict[str, str], *, rationale: str) -> None:
    for field in review.REVIEW_JUDGMENT_COLUMNS:
        row[field] = ""
    row.update(
        {
            "review_status": "UNVERIFIED_SANITY",
            "evidence_method": "",
            "review_rationale": rationale,
            "finding_id": "V7-F2",
            "finding_severity": "MAJOR",
            "blocker": (
                "No accepted current theorem-statement citation or clean compiled "
                "witness establishes nontriviality for this load-bearing definition."
            ),
            "reviewer": "Codex V7 current-tree recertification",
            "review_date": dt.date.today().isoformat(),
        }
    )


def apply_decision(
    row: dict[str, str],
    *,
    decision: dict[str, str],
    candidates: dict[tuple[str, str], dict[str, str]],
    v4: dict[str, dict[str, str]],
    collected: dict[str, dict[str, str]],
) -> None:
    status = decision["review_status"]
    if status == "UNVERIFIED_SANITY":
        residual(row, rationale=decision["review_rationale"])
        return

    for field in review.REVIEW_JUDGMENT_COLUMNS:
        row[field] = ""
    row.update(
        {
            "review_status": status,
            "evidence_name": decision["evidence_name"],
            **{field: decision[field] for field in SEMANTIC_COLUMNS},
            "reviewer": "Codex V7 current-tree fresh evidence review",
            "review_date": dt.date.today().isoformat(),
        }
    )
    evidence = decision["evidence_name"]
    if status == "VERIFIED_CITATION":
        candidate = candidates.get((row["name"], evidence))
        evidence_v4 = v4.get(evidence)
        if candidate is None or evidence_v4 is None:
            raise MigrationFailure(
                f"{row['name']}: fresh citation {evidence} is absent from "
                "the current candidate/V4 intersection"
            )
        if evidence_v4["kind"] != "theorem":
            raise MigrationFailure(
                f"{row['name']}: fresh citation is not a theorem"
            )
        extras = (
            review._axiom_set(evidence_v4["axioms"])
            - review.ALLOWED_AXIOMS
        )
        if extras:
            raise MigrationFailure(
                f"{row['name']}: fresh citation has disallowed axioms "
                f"{sorted(extras)}"
            )
        row.update(
            {
                "evidence_method": "citation",
                "evidence_location": exact_anchor(
                    target=row["name"],
                    evidence=evidence,
                    candidate=candidate,
                    v4=evidence_v4,
                ),
                "evidence_axioms": evidence_v4["axioms"] or "(none)",
            }
        )
        return

    measured = collected.get(evidence)
    if measured is None:
        raise MigrationFailure(
            f"{row['name']}: missing measured witness {evidence}"
        )
    dependencies = {
        item for item in measured["type_dependencies"].split(";") if item
    }
    if row["name"] not in dependencies:
        raise MigrationFailure(
            f"{row['name']}: witness {evidence} lacks direct type dependency"
        )
    anchor_problems: list[str] = []
    source = WITNESS_SOURCE.relative_to(ROOT).as_posix()
    anchor = review._resolve_theorem_anchor(
        module=WITNESS_MODULE,
        name=evidence,
        private_user_name=measured["private_user_name"],
        source_relative=source,
        context=f"recert witness {row['name']}",
        problems=anchor_problems,
    )
    if anchor_problems or anchor is None:
        raise MigrationFailure(
            f"{row['name']}: cannot anchor witness {evidence}: "
            f"{anchor_problems}"
        )
    row.update(
        {
            "evidence_method": "compiled_named_witness",
            "evidence_location": f"{source}:{anchor}",
            "evidence_axioms": measured["axioms"],
            "witness_evidence_key": f"{row['name']}|{evidence}",
        }
    )


def migrate_row(
    row: dict[str, str],
    *,
    old: dict[str, dict[str, str]],
    candidates: dict[tuple[str, str], dict[str, str]],
    v4: dict[str, dict[str, str]],
    old_types: dict[str, tuple[str, ...]],
    current_types: dict[str, tuple[str, ...]],
) -> None:
    prior = old.get(row["name"])
    if prior is None:
        residual(
            row,
            rationale=(
                "This definition is newly load-bearing in the current environment; "
                "the live candidate search supplied no manually accepted citation "
                "or compiled witness during this pass."
            ),
        )
        return
    if prior["review_status"] != "VERIFIED_CITATION":
        residual(
            row,
            rationale=(
                f"Fresh review of {row['candidate_count']} current statement-level "
                "candidate(s) found no citation that both demonstrates a "
                "nondegenerate model and rules out constant/zero/junk collapse. "
                "No clean compiled witness was available."
            ),
        )
        return
    evidence = prior["evidence_name"]
    candidate = candidates.get((row["name"], evidence))
    evidence_v4 = v4.get(evidence)
    if candidate is None or evidence_v4 is None:
        residual(
            row,
            rationale=(
                "The previously reviewed citation is absent from the current exact "
                "candidate/V4 intersection, so it was not inherited."
            ),
        )
        return
    if evidence_v4["kind"] != "theorem":
        residual(
            row,
            rationale=(
                "The previously reviewed evidence no longer has theorem kind in "
                "the fresh V4 environment."
            ),
        )
        return
    target = row["name"]
    if (
        old_types.get(target) is None
        or current_types.get(target) != old_types[target]
    ):
        residual(
            row,
            rationale=(
                "The load-bearing definition's exact kernel type differs from, "
                "or is absent in, the previously reviewed type snapshot. The "
                "prior semantic packet was therefore not reused."
            ),
        )
        return
    if (
        old_types.get(evidence) is None
        or current_types.get(evidence) != old_types[evidence]
    ):
        residual(
            row,
            rationale=(
                "The proposed citation theorem's exact kernel type differs "
                "from, or is absent in, the previously reviewed type snapshot. "
                "The prior semantic packet was therefore not reused."
            ),
        )
        return
    extras = review._axiom_set(evidence_v4["axioms"]) - review.ALLOWED_AXIOMS
    if extras:
        residual(
            row,
            rationale=(
                "The previously reviewed citation has nonstandard axioms in the "
                f"fresh V4 ledger: {sorted(extras)}."
            ),
        )
        return

    for field in review.REVIEW_JUDGMENT_COLUMNS:
        row[field] = prior[field]
    row.update(
        {
            "review_status": "VERIFIED_CITATION",
            "evidence_method": "citation",
            "evidence_location": exact_anchor(
                target=row["name"],
                evidence=evidence,
                candidate=candidate,
                v4=evidence_v4,
            ),
            "evidence_axioms": evidence_v4["axioms"] or "(none)",
            "reviewer": (
                "Codex V7 current-tree exact-statement citation recertification"
            ),
            "review_date": dt.date.today().isoformat(),
        }
    )


def write_summary(rows: list[dict[str, str]]) -> str:
    counts = collections.Counter(row["review_status"] for row in rows)
    report_verdict = (
        "ISSUES-FOUND"
        if counts["UNVERIFIED_SANITY"]
        else "PASS-WITH-NOTES"
    )
    residual_finding_id = (
        "V7-F2" if counts["UNVERIFIED_SANITY"] else "(none)"
    )
    residual_finding_severity = (
        "MAJOR" if counts["UNVERIFIED_SANITY"] else "(none)"
    )
    lines = [
        "V7 CURRENT-TREE DEFINITION REVIEW REGISTER",
        "==========================================",
        f"report_verdict_under_R6: {report_verdict}",
        f"rows: {len(rows)}",
        f"verified_citation: {counts['VERIFIED_CITATION']}",
        f"verified_witness: {counts['VERIFIED_WITNESS']}",
        f"unverified_sanity: {counts['UNVERIFIED_SANITY']}",
        "unreviewed: 0",
        "fresh_v4_revalidation: true",
        "fresh_source_reanchoring: true",
        "exact_target_type_identity_gate: true",
        "exact_citation_type_identity_gate: true",
        "old_machine_metadata_inherited: false",
        (
            "prior_semantic_packet_use: candidate-only; accepted only after "
            "exact current target/citation type identity"
        ),
        f"residual_finding_id: {residual_finding_id}",
        f"residual_finding_severity: {residual_finding_severity}",
        "",
    ]
    text = "\n".join(lines)
    SUMMARY.write_text(text, encoding="utf-8")
    FRAMEWORK_SUMMARY.write_text(text, encoding="utf-8")
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="validate an existing current register"
    )
    args = parser.parse_args()
    if not args.check:
        review.prepare(
            load_path=LOAD_BEARING,
            candidates_path=CANDIDATES,
            output_dir=OUTPUT_DIR,
            shard_count=4,
            force=True,
        )
        prior = old_rows()
        candidates = candidate_rows()
        v4 = v4_rows()
        decisions = decision_rows()
        collected = collector_rows()
        shard_paths = sorted(
            OUTPUT_DIR.glob("v7_definition_review_shard_*.tsv")
        )
        shard_rows = [
            (path, review._read_tsv(path, review.REVIEW_COLUMNS))
            for path in shard_paths
        ]
        required_type_names = {
            row["name"] for _, rows in shard_rows for row in rows
        }
        required_type_names.update(
            row["evidence_name"]
            for name, row in prior.items()
            if name in required_type_names
            and row["review_status"] == "VERIFIED_CITATION"
            and row["evidence_name"]
        )
        old_types = type_fingerprints(OLD_TYPES, required_type_names)
        current_types = type_fingerprints(CURRENT_TYPES, required_type_names)
        current_names = {
            row["name"] for _, rows in shard_rows for row in rows
        }
        stale_decisions = set(decisions) - current_names
        if stale_decisions:
            raise MigrationFailure(
                "fresh semantic decisions are stale/not load-bearing: "
                f"{sorted(stale_decisions)}"
            )
        all_rows: list[dict[str, str]] = []
        for path, rows in shard_rows:
            for row in rows:
                migrate_row(
                    row,
                    old=prior,
                    candidates=candidates,
                    v4=v4,
                    old_types=old_types,
                    current_types=current_types,
                )
                if row["name"] in decisions:
                    apply_decision(
                        row,
                        decision=decisions[row["name"]],
                        candidates=candidates,
                        v4=v4,
                        collected=collected,
                    )
            review._write_tsv(path, review.REVIEW_COLUMNS, rows)
            all_rows.extend(rows)
        undecided_residuals = sorted(
            row["name"]
            for row in all_rows
            if row["review_status"] == "UNVERIFIED_SANITY"
            and row["name"] not in decisions
        )
        if undecided_residuals:
            raise MigrationFailure(
                "every non-revalidated row requires an explicit fresh "
                f"semantic decision; missing={undecided_residuals}"
            )
        write_witness_evidence(decisions, collected)
        write_summary(all_rows)

    validation = review.validate(
        load_path=LOAD_BEARING,
        candidates_path=CANDIDATES,
        review_dir=OUTPUT_DIR,
        v4_path=V4,
        witness_evidence_path=WITNESS_EVIDENCE,
        require_final=True,
    )
    text = review.render_validation(validation)
    VALIDATION.write_text(text, encoding="utf-8")
    print(text, end="")
    if not validation.passed or not validation.final_ready:
        raise MigrationFailure(
            "current V7 review register is not final-ready and problem-free"
        )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MigrationFailure, OSError, ValueError, KeyError) as error:
        print(f"FAIL recert_v7_review: {error}")
        raise SystemExit(1)
