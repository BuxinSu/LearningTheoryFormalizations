#!/usr/bin/env python3
"""Fail-closed dynamic validation of every V6 Tier-C evidence obligation."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

from v6_init_tier_c_evidence import FIELDS as MANIFEST_FIELDS


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
REPO_ROOT = PACKAGE_ROOT.parent
LOGS = VERIFICATION / "logs"
MANIFEST = VERIFICATION / "curation" / "v6_tier_c_evidence.tsv"
SAMPLE = LOGS / "v6_tier_c_sample.tsv"
TIER_B = LOGS / "v6_tier_b_review.tsv"
ENV_EVIDENCE = LOGS / "v6_tier_c_environment_evidence.tsv"
ENV_MODELS = LOGS / "v6_tier_c_environment_models.tsv"
NEGATIVE = LOGS / "v6_tier_c_negative_evidence.tsv"

OUTPUT = LOGS / "v6_tier_c_coverage.tsv"
SUMMARY = LOGS / "v6_tier_c_coverage_summary.json"
RUN_LOG = LOGS / "v6_tier_c_coverage_run.log"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
METHODS = {"NAMED_APPLICATION", "LIBRARY_CITATION"}
PREMISE_CLASSES = {
    "NONE",
    "CLOSED_BY_EVIDENCE",
    "MODEL_DISCHARGED",
    "BOUNDARY_AND_NONBOUNDARY",
}
FORBIDDEN_COMPILE = (
    r": error(?::|\b)",
    r"declaration uses ['`]?sorry",
    r"\bsorryAx\b",
)


def read(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        return list(reader.fieldnames or []), list(reader)


def names(text: str) -> list[str]:
    return [item.strip() for item in text.split(";") if item.strip()]


def axioms(text: str) -> set[str]:
    return {item for item in text.split(",") if item}


def sha256(path: Path) -> str:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return digest


def compile_clean(log: Path, status: Path, label: str, errors: list[str]) -> bool:
    clean = True
    if not log.is_file() or not status.is_file():
        errors.append(f"{label}: missing compile log/status")
        return False
    text = log.read_text(encoding="utf-8")
    for pattern in FORBIDDEN_COMPILE:
        if re.search(pattern, text, flags=re.IGNORECASE):
            errors.append(f"{label}: compile log matches forbidden {pattern!r}")
            clean = False
    if not re.search(
        r"(?m)^exit_code:\s*0\s*$",
        status.read_text(encoding="utf-8"),
    ):
        errors.append(f"{label}: status does not record exit_code: 0")
        clean = False
    return clean


def dependency_ok(endpoint_kind: str, row: dict[str, str]) -> bool:
    in_type = row["target_in_type"] == "true"
    in_value = row["target_in_value"] == "true"
    if endpoint_kind == "theorem":
        return in_type or in_value
    if endpoint_kind == "definition":
        return in_type or in_value
    return False


SITE_RE = re.compile(
    r"^(?P<path>(?:MatrixConcentration/)?"
    r"(?:Verification/)?[A-Za-z0-9_./-]+\.lean):(?P<line>[0-9]+)$"
)


def validate_site(
    manifest: dict[str, str],
    evidence_names: list[str],
) -> list[str]:
    errors: list[str] = []
    sites = names(manifest["application_site"])
    if not sites:
        return [
            f"{manifest['declaration']}: application_site is not "
            "File.lean:line"
        ]
    if len(sites) != len(evidence_names):
        return [
            f"{manifest['declaration']}: application-site/evidence cardinality "
            f"mismatch ({len(sites)} != {len(evidence_names)})"
        ]
    for site, evidence_name in zip(sites, evidence_names, strict=True):
        match = SITE_RE.fullmatch(site)
        if match is None:
            errors.append(
                f"{manifest['declaration']}: invalid application site {site!r}"
            )
            continue
        rel = Path(match.group("path"))
        if rel.parts and rel.parts[0] == "MatrixConcentration":
            rel = Path(*rel.parts[1:])
        path = PACKAGE_ROOT / rel
        line = int(match.group("line"))
        if not path.is_file():
            errors.append(
                f"{manifest['declaration']}: application file missing: {rel}"
            )
            continue
        source = path.read_text(encoding="utf-8").splitlines()
        if not (1 <= line <= len(source)):
            errors.append(
                f"{manifest['declaration']}: application line {line} "
                "outside file"
            )
            continue
        line_text = source[line - 1]
        expected = (
            manifest["declaration"]
            if manifest["evidence_method"] == "LIBRARY_CITATION"
            else evidence_name.rsplit(".", 1)[-1]
        )
        if expected not in line_text:
            errors.append(
                f"{manifest['declaration']}: application site {rel}:{line} "
                f"does not contain {expected!r}"
            )
    return errors


def write_output(rows: list[dict[str, str]]) -> None:
    fields = [
        "obligation_id",
        "obligation_kind",
        "chapter",
        "global_row",
        "chapter_row",
        "declaration",
        "endpoint_kind",
        "tier_b_verdict",
        "coverage_method",
        "evidence_names",
        "endpoint_dependencies",
        "evidence_axioms",
        "application_site",
        "substantive_prop_premises",
        "premise_discharge",
        "model_witnesses",
        "model_types",
        "evidence_detail",
        "status",
    ]
    with OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    errors: list[str] = []
    required = [
        MANIFEST,
        SAMPLE,
        TIER_B,
        ENV_EVIDENCE,
        ENV_MODELS,
        NEGATIVE,
        LOGS / "v6_witnesses_compile.log",
        LOGS / "v6_witnesses_compile_status.log",
        LOGS / "v6_tier_c_environment_compile.log",
        LOGS / "v6_tier_c_environment_compile_status.log",
        LOGS / "v6_witness_module_build.log",
        LOGS / "v6_witness_module_build_status.log",
    ]
    missing = [path for path in required if not path.is_file()]
    if missing:
        errors.extend(f"missing required input: {path}" for path in missing)
        write_output([])
        SUMMARY.write_text(
            json.dumps(
                {
                    "status": "FAIL",
                    "errors": errors,
                    "total_obligations": 0,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        print("\n".join(errors))
        return 1

    witness_clean = compile_clean(
        LOGS / "v6_witnesses_compile.log",
        LOGS / "v6_witnesses_compile_status.log",
        "witness suite",
        errors,
    )
    module_clean = compile_clean(
        LOGS / "v6_witness_module_build.log",
        LOGS / "v6_witness_module_build_status.log",
        "witness importable module",
        errors,
    )
    environment_clean = compile_clean(
        LOGS / "v6_tier_c_environment_compile.log",
        LOGS / "v6_tier_c_environment_compile_status.log",
        "Tier-C environment harness",
        errors,
    )

    manifest_fields, manifest = read(MANIFEST)
    if manifest_fields != MANIFEST_FIELDS:
        errors.append(f"Tier-C manifest schema drift: {manifest_fields!r}")
    _, sample = read(SAMPLE)
    _, tier_b = read(TIER_B)
    _, environment = read(ENV_EVIDENCE)
    _, model_environment = read(ENV_MODELS)
    _, negative = read(NEGATIVE)
    tier_b_by_global = {row["global_row"]: row for row in tier_b}

    expected: dict[str, tuple[dict[str, str], str]] = {}
    for sample_row in sample:
        tier_row = tier_b_by_global.get(sample_row["global_row"])
        if tier_row is None or tier_row["verdict"] != "OK":
            errors.append(
                f"sample row {sample_row['global_row']} is absent/non-OK"
            )
            continue
        expected[sample_row["global_row"]] = (tier_row, "sampled_OK")
    if len(sample) != 40 or Counter(row["chapter"] for row in sample) != Counter(
        {str(chapter): 5 for chapter in range(1, 9)}
    ):
        errors.append("sample is not exactly five OK rows per chapter")
    for chapter in map(str, range(1, 9)):
        chapter_has_ok_definition = any(
            row["chapter"] == chapter
            and row["verdict"] == "OK"
            and row["endpoint_kind"] == "definition"
            for row in tier_b
        )
        chapter_samples_definition = any(
            row["chapter"] == chapter
            and row["endpoint_kind"] == "definition"
            for row in sample
        )
        if chapter_has_ok_definition and not chapter_samples_definition:
            errors.append(
                f"sample chapter {chapter} omits its OK-definition stratum"
            )
    for tier_row in tier_b:
        if tier_row["verdict"] in {"SUSPECT", "VACUOUS"}:
            if tier_row["global_row"] in expected:
                errors.append(
                    f"Tier-C obligation overlap at {tier_row['global_row']}"
                )
            expected[tier_row["global_row"]] = (
                tier_row,
                f"TierB_{tier_row['verdict']}",
            )

    manifest_by_global: dict[str, dict[str, str]] = {}
    for row in manifest:
        if row["global_row"] in manifest_by_global:
            errors.append(f"duplicate manifest row {row['global_row']}")
        manifest_by_global[row["global_row"]] = row
    if set(manifest_by_global) != set(expected):
        errors.append(
            "manifest obligation-set mismatch: "
            f"missing={sorted(set(expected)-set(manifest_by_global))}, "
            f"extra={sorted(set(manifest_by_global)-set(expected))}"
        )

    env_map: dict[tuple[str, str], dict[str, str]] = {}
    for row in environment:
        key = (row["global_row"], row["evidence_name"])
        if key in env_map:
            errors.append(f"duplicate environment evidence row {key}")
        env_map[key] = row
    model_map: dict[tuple[str, str], dict[str, str]] = {}
    for row in model_environment:
        key = (row["global_row"], row["model_name"])
        if key in model_map:
            errors.append(f"duplicate environment model row {key}")
        model_map[key] = row

    coverage: list[dict[str, str]] = []
    for global_row in sorted(expected, key=int):
        tier_row, obligation_kind = expected[global_row]
        row = manifest_by_global.get(global_row)
        row_errors_before = len(errors)
        if row is None:
            continue
        immutable = {
            "global_row": tier_row["global_row"],
            "chapter": tier_row["chapter"],
            "chapter_row": tier_row["chapter_row"],
            "declaration": tier_row["declaration"],
            "endpoint_kind": tier_row["endpoint_kind"],
            "tier_b_verdict": tier_row["verdict"],
            "obligation_kind": obligation_kind,
        }
        for field, expected_value in immutable.items():
            if row[field] != expected_value:
                errors.append(
                    f"{tier_row['declaration']}: manifest {field} drift "
                    f"{row[field]!r} != {expected_value!r}"
                )
        if row["evidence_method"] not in METHODS:
            errors.append(
                f"{tier_row['declaration']}: invalid evidence method "
                f"{row['evidence_method']!r}"
            )
        evidence_names = names(row["evidence_names"])
        if not evidence_names:
            errors.append(f"{tier_row['declaration']}: no evidence names")
        if len(evidence_names) != len(set(evidence_names)):
            errors.append(
                f"{tier_row['declaration']}: duplicate evidence names"
            )
        if any(not name.startswith("MatrixConcentration.") for name in evidence_names):
            errors.append(
                f"{tier_row['declaration']}: evidence names must be fully qualified"
            )
        if row["evidence_method"] == "NAMED_APPLICATION" and any(
            not name.startswith("MatrixConcentration.V6Witnesses.")
            for name in evidence_names
        ):
            errors.append(
                f"{tier_row['declaration']}: named application outside V6Witnesses"
            )
        if row["evidence_method"] == "LIBRARY_CITATION" and any(
            name.startswith("MatrixConcentration.V6Witnesses.")
            for name in evidence_names
        ):
            errors.append(
                f"{tier_row['declaration']}: witness mislabeled library citation"
            )

        dependency_descriptions: list[str] = []
        axiom_descriptions: list[str] = []
        evidence_prop_binders: list[int] = []
        for evidence_name in evidence_names:
            env_row = env_map.get((global_row, evidence_name))
            if env_row is None:
                errors.append(
                    f"{tier_row['declaration']}: missing environment row for "
                    f"{evidence_name}"
                )
                continue
            if env_row["endpoint"] != (
                "MatrixConcentration." + tier_row["declaration"]
            ):
                errors.append(
                    f"{tier_row['declaration']}: environment target drift"
                )
            if env_row["evidence_kind"] != "theorem":
                errors.append(
                    f"{tier_row['declaration']}: evidence {evidence_name} "
                    "is not a theorem"
                )
            if not dependency_ok(tier_row["endpoint_kind"], env_row):
                errors.append(
                    f"{tier_row['declaration']}: evidence {evidence_name} "
                    "has no accepted endpoint dependency/application"
                )
            extras = axioms(env_row["axioms"]) - ALLOWED_AXIOMS
            if extras:
                errors.append(
                    f"{tier_row['declaration']}: evidence {evidence_name} "
                    f"has disallowed axioms {sorted(extras)}"
                )
            dependency_descriptions.append(
                f"{evidence_name}:type={env_row['target_in_type']},"
                f"value={env_row['target_in_value']}"
            )
            axiom_descriptions.append(
                f"{evidence_name}="
                + (env_row["axioms"] or "none")
            )
            try:
                evidence_prop_binders.append(int(env_row["prop_binders"]))
            except (KeyError, ValueError):
                errors.append(
                    f"{tier_row['declaration']}: evidence {evidence_name} "
                    "has invalid Prop-binder count"
                )

        premise_class = row["premise_class"]
        if premise_class not in PREMISE_CLASSES:
            errors.append(
                f"{tier_row['declaration']}: invalid premise class "
                f"{premise_class!r}"
            )
        model_names = names(row["model_names"])
        premises = row["substantive_premises"].strip()
        if premise_class == "NONE":
            if premises.casefold() != "none" or model_names:
                errors.append(
                    f"{tier_row['declaration']}: malformed NONE premise evidence"
                )
        elif len(premises) < 15:
            errors.append(
                f"{tier_row['declaration']}: substantive premise text too short"
            )
        if premise_class == "CLOSED_BY_EVIDENCE":
            if model_names:
                errors.append(
                    f"{tier_row['declaration']}: CLOSED_BY_EVIDENCE must not "
                    "list separate models"
                )
            if (
                row["evidence_method"] == "NAMED_APPLICATION"
                and any(count != 0 for count in evidence_prop_binders)
            ):
                errors.append(
                    f"{tier_row['declaration']}: CLOSED_BY_EVIDENCE republishes "
                    "undischarged Prop premises"
                )
        if premise_class == "MODEL_DISCHARGED":
            if not model_names:
                errors.append(
                    f"{tier_row['declaration']}: MODEL_DISCHARGED lacks models"
                )
            if (
                row["evidence_method"] == "NAMED_APPLICATION"
                and not any(count > 0 for count in evidence_prop_binders)
            ):
                errors.append(
                    f"{tier_row['declaration']}: MODEL_DISCHARGED is used "
                    "without an evidence Prop premise"
                )
        if premise_class == "BOUNDARY_AND_NONBOUNDARY":
            if len(evidence_names) < 2:
                errors.append(
                    f"{tier_row['declaration']}: boundary class needs ≥2 "
                    "endpoint-dependent evidence declarations"
                )
            detail_lower = row["discharge_detail"].casefold()
            if "boundary" not in detail_lower or "nonboundary" not in detail_lower:
                errors.append(
                    f"{tier_row['declaration']}: boundary discharge must map "
                    "both boundary and nonboundary evidence"
                )
        model_types: list[str] = []
        for model_name in model_names:
            model = model_map.get((global_row, model_name))
            if model is None:
                errors.append(
                    f"{tier_row['declaration']}: missing environment model "
                    f"{model_name}"
                )
                continue
            if model["model_kind"] != "theorem":
                errors.append(
                    f"{tier_row['declaration']}: model {model_name} not theorem"
                )
            extras = axioms(model["axioms"]) - ALLOWED_AXIOMS
            if extras:
                errors.append(
                    f"{tier_row['declaration']}: model {model_name} has "
                    f"disallowed axioms {sorted(extras)}"
                )
            if not model["model_type"].strip():
                errors.append(
                    f"{tier_row['declaration']}: model {model_name} has empty type"
                )
            try:
                model_prop_binders = int(model["prop_binders"])
            except (KeyError, ValueError):
                model_prop_binders = -1
            if model_prop_binders != 0:
                errors.append(
                    f"{tier_row['declaration']}: model {model_name} is not a "
                    "closed theorem (has undischarged Prop binders)"
                )
            model_types.append(f"{model_name}: {model['model_type']}")
        if set(model_names) != {
            name for (row_id, name) in model_map if row_id == global_row
        }:
            errors.append(
                f"{tier_row['declaration']}: model environment set differs "
                "from manifest"
            )
        if len(row["discharge_detail"].strip()) < 50:
            errors.append(
                f"{tier_row['declaration']}: discharge detail too short"
            )
        errors.extend(validate_site(row, evidence_names))

        accepted = (
            len(errors) == row_errors_before
            and witness_clean
            and module_clean
            and environment_clean
        )
        if obligation_kind == "sampled_OK":
            sample_index = next(
                item["sample_index"]
                for item in sample
                if item["global_row"] == global_row
            )
            obligation_id = (
                f"OK-C{int(tier_row['chapter']):02d}-"
                f"S{int(sample_index):02d}"
            )
        else:
            obligation_id = (
                f"{tier_row['verdict']}-R{int(global_row):03d}"
            )
        coverage.append(
            {
                "obligation_id": obligation_id,
                "obligation_kind": obligation_kind,
                "chapter": tier_row["chapter"],
                "global_row": global_row,
                "chapter_row": tier_row["chapter_row"],
                "declaration": tier_row["declaration"],
                "endpoint_kind": tier_row["endpoint_kind"],
                "tier_b_verdict": tier_row["verdict"],
                "coverage_method": row["evidence_method"],
                "evidence_names": ";".join(evidence_names),
                "endpoint_dependencies": ";".join(dependency_descriptions),
                "evidence_axioms": ";".join(axiom_descriptions),
                "application_site": row["application_site"],
                "substantive_prop_premises": premises,
                "premise_discharge": premise_class,
                "model_witnesses": ";".join(model_names) or "none",
                "model_types": " | ".join(model_types) or "none",
                "evidence_detail": row["discharge_detail"],
                "status": "COVERED" if accepted else "UNCOVERED",
            }
        )

    expected_env_keys = {
        (row["global_row"], name)
        for row in manifest
        for name in names(row["evidence_names"])
    }
    if set(env_map) != expected_env_keys:
        errors.append(
            "environment evidence set differs from manifest: "
            f"missing={sorted(expected_env_keys-set(env_map))}, "
            f"extra={sorted(set(env_map)-expected_env_keys)}"
        )

    negative_pass = False
    if len(negative) != 1:
        errors.append(
            f"negative Tier-C calibration has {len(negative)} rows, expected 1"
        )
    else:
        bad = negative[0]
        allowed = not (axioms(bad["axioms"]) - ALLOWED_AXIOMS)
        unrelated = not dependency_ok(bad["endpoint_kind"], bad)
        resolved_theorem = bad["evidence_kind"] == "theorem"
        exact_control = (
            bad["endpoint"] == "MatrixConcentration.covarianceMatrix"
            and bad["evidence_name"]
            == "MatrixConcentration.V6Witnesses."
            "calibration_unrelated_allowed_axiom"
        )
        negative_pass = (
            allowed and unrelated and resolved_theorem and exact_control
        )
        if not negative_pass:
            errors.append(
                "negative Tier-C calibration did not isolate/reject an "
                "unrelated allowed-axiom theorem"
            )

    # Recompute row status after global checks so no row can remain COVERED in
    # a globally failed ledger.
    status = (
        "PASS"
        if not errors
        and len(coverage) == len(expected)
        and all(row["status"] == "COVERED" for row in coverage)
        and negative_pass
        else "FAIL"
    )
    if status != "PASS":
        for row in coverage:
            row["status"] = "UNCOVERED"
    write_output(coverage)
    summary = {
        "status": status,
        "total_obligations": len(expected),
        "covered_obligations": sum(
            row["status"] == "COVERED" for row in coverage
        ),
        "uncovered_obligations": sum(
            row["status"] != "COVERED" for row in coverage
        ),
        "sampled_ok_obligations": sum(
            kind == "sampled_OK" for _, kind in expected.values()
        ),
        "suspect_obligations": sum(
            kind == "TierB_SUSPECT" for _, kind in expected.values()
        ),
        "vacuous_obligations": sum(
            kind == "TierB_VACUOUS" for _, kind in expected.values()
        ),
        "method_counts": dict(
            sorted(Counter(row["coverage_method"] for row in coverage).items())
        ),
        "negative_unrelated_allowed_axiom_rejected": negative_pass,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "compile_clean": {
            "witness": witness_clean,
            "witness_module": module_clean,
            "environment_harness": environment_clean,
        },
        "input_sha256": {
            str(path.relative_to(PACKAGE_ROOT)): sha256(path)
            for path in required
        },
        "errors": errors,
    }
    SUMMARY.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    lines = [
        "V6 DYNAMIC TIER-C EVIDENCE VALIDATION",
        f"STATUS {status}",
        f"SAMPLED_OK {summary['sampled_ok_obligations']}",
        f"SUSPECT {summary['suspect_obligations']}",
        f"VACUOUS {summary['vacuous_obligations']}",
        f"TOTAL {summary['total_obligations']}",
        f"COVERED {summary['covered_obligations']}",
        f"UNCOVERED {summary['uncovered_obligations']}",
        "NEGATIVE_UNRELATED_ALLOWED_AXIOM_REJECTED "
        + str(negative_pass).lower(),
        f"ERRORS {len(errors)}",
        *(f"ERROR {error}" for error in errors),
    ]
    RUN_LOG.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
