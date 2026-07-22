#!/usr/bin/env python3
"""Fail-closed validation of the complete V7 load-bearing sanity register."""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path

from lean_source_scan import LOGS, ROOT


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
VERIFY = ROOT / "MatrixConcentration" / "Verification"
WITNESS_SOURCE = VERIFY / "scripts" / "witnesses" / "V7Witnesses.lean"


def citation(short: str, reason: str) -> tuple[str, str, str]:
    return ("citation", f"MatrixConcentration.{short}", reason)


def witness(short: str, reason: str) -> tuple[str, str, str]:
    return (
        "compiled_named_witness",
        f"MatrixConcentration.V7Witnesses.{short}",
        reason,
    )


REGISTER: dict[str, tuple[str, str, str]] = {
    "MatrixConcentration.covarianceMatrix": citation(
        "covarianceMatrix_apply",
        "The entry formula is the covariance integral and is not a constant matrix formula.",
    ),
    "MatrixConcentration.sampleCovSummand": witness(
        "sampleCovSummand_nonzero_model",
        "With one all-one sample and zero population vector in dimension one, the summand is exactly the identity matrix.",
    ),
    "MatrixConcentration.frobeniusNorm": citation(
        "frobeniusNorm_pos",
        "Every nonzero finite matrix has strictly positive Frobenius norm.",
    ),
    "MatrixConcentration.entrywiseL1Norm": citation(
        "entrywiseL1Norm_eq_zero_iff",
        "The quantity vanishes exactly on the zero matrix.",
    ),
    "MatrixConcentration.singularValues": citation(
        "l2_opNorm_eq_sup_singularValues",
        "Their supremum is the spectral norm, hence is positive for a nonzero matrix.",
    ),
    "MatrixConcentration.stableRank": citation(
        "one_le_stableRank",
        "The stable rank is at least one on every nonzero matrix; the zero 0/0 boundary is explicit.",
    ),
    "MatrixConcentration.schattenOneNorm": citation(
        "schattenOneNorm_eq_zero_iff",
        "The Schatten one-norm vanishes exactly on the zero matrix.",
    ),
    "MatrixConcentration.hermDilation": citation(
        "l2_opNorm_hermDilation",
        "Hermitian dilation preserves the spectral norm of every rectangular matrix.",
    ),
    "MatrixConcentration.expectation": citation(
        "expectation_const",
        "Under a probability measure, expectation fixes every constant matrix.",
    ),
    "MatrixConcentration.MIntegrable": witness(
        "mIntegrable_nonzero_constant",
        "A nonzero constant 1x1 matrix is integrable on a one-point space but not under counting measure on Nat, ruling out both constant truth values.",
    ),
    "MatrixConcentration.IsRademacher": witness(
        "isRademacher_identity",
        "The identity law satisfies the predicate, while the constant-zero one-point law is excluded by the unit-second-moment consequence.",
    ),
    "MatrixConcentration.IsStdGaussian": witness(
        "isStdGaussian_identity",
        "The standard-Gaussian identity law satisfies the predicate, while the constant-zero one-point law is excluded by the unit-second-moment consequence.",
    ),
    "MatrixConcentration.IsBernoulli": witness(
        "isBernoulli_identity",
        "The nondegenerate Bernoulli(1/2) identity law satisfies the predicate, while the constant-zero one-point law is excluded by its forced expectation 1/2.",
    ),
    "MatrixConcentration.matrixVar": witness(
        "variance_statistics_nonzero_models",
        "For the 1x1 scalar Rademacher matrix, matrixVar is exactly one.",
    ),
    "MatrixConcentration.varStatHerm": witness(
        "variance_statistics_nonzero_models",
        "For the same 1x1 scalar Rademacher matrix, the Hermitian variance statistic is exactly one.",
    ),
    "MatrixConcentration.matrixVar1": witness(
        "variance_statistics_nonzero_models",
        "For the same 1x1 scalar Rademacher matrix, the first rectangular variance is exactly one.",
    ),
    "MatrixConcentration.matrixVar2": witness(
        "variance_statistics_nonzero_models",
        "For the same 1x1 scalar Rademacher matrix, the second rectangular variance is exactly one.",
    ),
    "MatrixConcentration.varStat": witness(
        "variance_statistics_nonzero_models",
        "For the same 1x1 scalar Rademacher matrix, the rectangular variance statistic is exactly one.",
    ),
    "MatrixConcentration.matrixMgf": citation(
        "matrixMgf_hasSum_moments",
        "The full convergent moment series sums to the matrix mgf.",
    ),
    "MatrixConcentration.matrixCgf": citation(
        "gaussian_matrix_cgf",
        "A Gaussian Hermitian series has the stated nonconstant quadratic cgf.",
    ),
    "MatrixConcentration.weakVariance": citation(
        "variance_le_max_dim_mul_weakVariance",
        "It controls the ordinary coefficient variance up to the measured dimension factor.",
    ),
    "MatrixConcentration.wignerCoeff": citation(
        "wignerCoeff_sq",
        "Its square is the nonzero sum of two diagonal matrix units.",
    ),
    "MatrixConcentration.shiftPow": citation(
        "shiftPow_apply",
        "Every entry is characterized as the intended 0/1 shifted diagonal.",
    ),
    "MatrixConcentration.toeplitzCoeff": citation(
        "toeplitz_coeff_sum_right",
        "For positive d its Gram sum is exactly d times the identity.",
    ),
    "MatrixConcentration.gChernoff": witness(
        "gChernoff_positive_model",
        "At theta=L=1 the coefficient is strictly positive.",
    ),
    "MatrixConcentration.columnSubmatrix": citation(
        "columnSubmatrix_gram",
        "Its Gram matrix is exactly the selected sum of column Gram matrices.",
    ),
    "MatrixConcentration.colGram": citation(
        "colGram_apply",
        "Every entry is exactly B_ik times conjugate B_jk.",
    ),
    "MatrixConcentration.colNormSq": citation(
        "sum_colNormSq",
        "The sum over columns is exactly the squared Frobenius norm.",
    ),
    "MatrixConcentration.rowSubmatrix": citation(
        "rowSubmatrix_apply",
        "Every entry is exactly the selector times the corresponding entry of B.",
    ),
    "MatrixConcentration.rowColumnSubmatrix": citation(
        "rowColumnSubmatrix_eq",
        "It is exactly the book product PBR.",
    ),
    "MatrixConcentration.entryDiag": citation(
        "sup_colNormSq_eq_lambdaMax",
        "The maximum selected column norm is represented as the largest eigenvalue of its sum.",
    ),
    "MatrixConcentration.secondSmallestEigenvalue": citation(
        "connected_iff_secondSmallest_pos",
        "For graph Laplacians it is positive exactly when the graph is connected.",
    ),
    "MatrixConcentration.lapMatrixC": citation(
        "connected_iff_secondSmallest_pos",
        "The complex Laplacian feeds the substantive connectivity characterization.",
    ),
    "MatrixConcentration.laplCoeff": witness(
        "laplCoeff_nonzero_model",
        "For the concrete edge (0,1) in dimension two, the (0,0) entry is exactly one.",
    ),
    "MatrixConcentration.erLaplacian": citation(
        "compressed_sum_eq",
        "Its compressed random sum is identified exactly with the compressed Laplacian coefficient sum.",
    ),
    "MatrixConcentration.gBernstein": witness(
        "gBernstein_value_model",
        "At theta=L=1 the coefficient computes exactly to 3/4.",
    ),
    "MatrixConcentration.secondMoment": witness(
        "secondMoment_nonzero_model",
        "A constant 1x1 identity sample on a one-point space has second moment exactly one.",
    ),
    "MatrixConcentration.sparsifyProb": citation(
        "sparsifyProb_sum_eq_one",
        "For every nonzero matrix the probabilities sum exactly to one.",
    ),
    "MatrixConcentration.sparsifyValue": citation(
        "sum_sparsifyProb_smul_value",
        "The probability-weighted values reconstruct every nonzero target matrix.",
    ),
    "MatrixConcentration.matmulProb": citation(
        "matmulProb_sum_eq_one_of_pair_ne_zero",
        "The probabilities normalize whenever the matrix pair is not simultaneously zero.",
    ),
    "MatrixConcentration.matmulValue": citation(
        "expectation_matmulEstimator_book",
        "The estimator expectation is exactly the matrix product B*C.",
    ),
    "MatrixConcentration.featureOuter": witness(
        "featureOuter_nonzero_model",
        "The all-one Fin 1 feature vector produces the 1x1 identity matrix.",
    ),
    "MatrixConcentration.intdim": citation(
        "intdim_one",
        "The identity matrix has intrinsic dimension exactly the index cardinality.",
    ),
    "MatrixConcentration.psiOne": witness(
        "psiOne_positive_model",
        "psiOne 1 1 is strictly positive, while the library separately proves psiOne 1 0 = 0.",
    ),
    "MatrixConcentration.psiTwo": witness(
        "psiTwo_positive_model",
        "psiTwo 1 1 is strictly positive, while the library separately proves psiTwo 1 0 = 0.",
    ),
    "MatrixConcentration.mre": witness(
        "entropy_nonzero_models",
        "On the 1x1 diagonal pair (exp(1),1), matrix relative entropy is exactly one.",
    ),
    "MatrixConcentration.vre": witness(
        "entropy_nonzero_models",
        "On the one-coordinate pair (exp(1),1), vector relative entropy is exactly one.",
    ),
    "MatrixConcentration.l2norm": citation(
        "l2norm_sq",
        "Its square is exactly the sum of squared coordinate norms.",
    ),
    "MatrixConcentration.lambdaMax": citation(
        "lambdaMax_one",
        "On every nonempty identity matrix the largest eigenvalue is exactly one.",
    ),
    "MatrixConcentration.lambdaMin": citation(
        "lambdaMin_one",
        "On every nonempty identity matrix the smallest eigenvalue is exactly one.",
    ),
    "MatrixConcentration.rayleigh": citation(
        "rayleigh_smul_one",
        "On c times the identity it is exactly c times the squared l2 norm.",
    ),
}


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def locate(short_name: str, path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        rf"(?m)^[ \t]*(?:theorem|lemma)\s+{re.escape(short_name)}\b", text
    )
    if not match:
        return "MISSING"
    return f"{path.relative_to(ROOT).as_posix()}:{text.count(chr(10), 0, match.start()) + 1}"


def parse_status(path: Path, key: str) -> int | None:
    text = path.read_text(encoding="utf-8") if path.is_file() else ""
    match = re.search(rf"(?m)^{re.escape(key)}\s+(-?\d+)\s*$", text)
    return int(match.group(1)) if match else None


def main() -> int:
    errors: list[str] = []
    load_bearing = read_tsv(LOGS / "v7_load_bearing_definitions.tsv")
    load_names = {row["resolved_name"] for row in load_bearing}
    if load_names != set(REGISTER):
        errors.append(
            "register/load-bearing mismatch: "
            f"missing={sorted(load_names - set(REGISTER))}, "
            f"extra={sorted(set(REGISTER) - load_names)}"
        )

    source_rows = read_tsv(LOGS / "v7_source_resolution.tsv")
    source_by_name = {row["resolved_name"]: row for row in source_rows}
    env_rows = read_tsv(LOGS / "v7_environment_dependencies.tsv")
    env_by_name = {row["name"]: row for row in env_rows}
    witness_axiom_rows = read_tsv(LOGS / "v7_witness_axioms.tsv")
    witness_axioms = {
        row["name"]: {item for item in row["axioms"].split(",") if item}
        for row in witness_axiom_rows
    }
    witness_type_dependencies = {
        row["name"]: {
            item for item in row["type_dependencies"].split(",") if item
        }
        for row in witness_axiom_rows
    }

    witness_status = parse_status(
        LOGS / "v7_witness_exit_status.log", "WITNESS_EXIT_STATUS"
    )
    if witness_status != 0:
        errors.append(f"witness Lean exit status is not recorded zero: {witness_status}")
    witness_log = (LOGS / "v7_witnesses_compile.log").read_text(encoding="utf-8")
    for pattern in (r": error(?::|\b)", r"declaration uses ['`]?sorry", r"\bsorryAx\b"):
        if re.search(pattern, witness_log, flags=re.IGNORECASE):
            errors.append(f"official witness compile log matched forbidden {pattern!r}")
    witness_source_text = WITNESS_SOURCE.read_text(encoding="utf-8")
    if "set_option autoImplicit false" not in witness_source_text:
        errors.append("V7 witness source does not set autoImplicit false")

    bad_status = parse_status(
        LOGS / "v7_witness_exit_status.log", "BAD_WITNESS_LEAN_EXIT_STATUS"
    )
    bad_text = (LOGS / "v7_bad_witness_compile.log").read_text(encoding="utf-8")
    bad_has_sorry = bool(
        re.search(r"declaration uses ['`]?sorry", bad_text, flags=re.IGNORECASE)
    )
    bad_has_error = bool(
        re.search(r": error(?::|\b)", bad_text, flags=re.IGNORECASE)
    )
    bad_rejected = (
        bad_status == 0 and bad_has_sorry and not bad_has_error
    )
    if not bad_rejected:
        errors.append(
            "BadWitness calibration was not rejected from an explicitly recorded run"
        )

    output_rows: list[dict[str, object]] = []
    load_by_name = {row["resolved_name"]: row for row in load_bearing}
    for definition in sorted(load_names):
        method, evidence, reason = REGISTER[definition]
        evidence_location = ""
        evidence_axioms: set[str] = set()
        accepted = True
        if method == "citation":
            citation_row = source_by_name.get(evidence)
            env_row = env_by_name.get(evidence)
            if citation_row is None or env_row is None:
                errors.append(f"{definition}: citation does not resolve: {evidence}")
                accepted = False
            else:
                evidence_location = (
                    f"{citation_row['path']}:{citation_row['line']}"
                )
                direct_uses = {
                    item
                    for field in ("type_dependencies", "value_dependencies")
                    for item in env_row[field].split(",")
                    if item
                }
                if definition not in direct_uses:
                    errors.append(
                        f"{definition}: citation {evidence} has no direct type/value dependency"
                    )
                    accepted = False
                evidence_axioms = {
                    item for item in env_row["axioms"].split(",") if item
                }
        else:
            short_name = evidence.rsplit(".", 1)[-1]
            evidence_location = locate(short_name, WITNESS_SOURCE)
            if evidence_location == "MISSING":
                errors.append(f"{definition}: witness declaration missing: {evidence}")
                accepted = False
            if evidence not in witness_axioms:
                errors.append(f"{definition}: witness axiom row missing: {evidence}")
                accepted = False
            else:
                evidence_axioms = witness_axioms[evidence]
                if definition not in witness_type_dependencies[evidence]:
                    errors.append(
                        f"{definition}: witness type has no direct dependency: {evidence}"
                    )
                    accepted = False
            if witness_status != 0:
                accepted = False

        extras = evidence_axioms - ALLOWED_AXIOMS
        if extras:
            errors.append(
                f"{definition}: evidence has disallowed axioms {sorted(extras)}"
            )
            accepted = False
        if not reason.strip():
            errors.append(f"{definition}: empty nondegeneracy reason")
            accepted = False
        load_row = load_by_name[definition]
        output_rows.append(
            {
                "definition": definition,
                "module": load_row["module"],
                "path": load_row["path"],
                "line": load_row["line"],
                "prelude_definition": load_row["prelude_definition"],
                "theorem_endpoint_direct_type_reference_count": load_row[
                    "theorem_endpoint_direct_type_reference_count"
                ],
                "load_bearing_reason": load_row["load_bearing_reason"],
                "method": method,
                "evidence": evidence,
                "evidence_location": evidence_location,
                "evidence_axioms": ",".join(sorted(evidence_axioms)),
                "nondegeneracy_reason": reason,
                "status": "COVERED" if accepted else "REJECTED",
            }
        )

    fields = [
        "definition",
        "module",
        "path",
        "line",
        "prelude_definition",
        "theorem_endpoint_direct_type_reference_count",
        "load_bearing_reason",
        "method",
        "evidence",
        "evidence_location",
        "evidence_axioms",
        "nondegeneracy_reason",
        "status",
    ]
    with (LOGS / "v7_sanity_register.tsv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        writer.writerows(output_rows)

    covered = sum(row["status"] == "COVERED" for row in output_rows)
    method_counts = {
        method: sum(row["method"] == method for row in output_rows)
        for method in ("citation", "compiled_named_witness")
    }
    summary = {
        "load_bearing_definitions": len(load_names),
        "register_rows": len(output_rows),
        "covered": covered,
        "method_counts": method_counts,
        "witness_lean_exit_status": witness_status,
        "witness_compile_clean": not any(
            re.search(pattern, witness_log, flags=re.IGNORECASE)
            for pattern in (
                r": error(?::|\b)",
                r"declaration uses ['`]?sorry",
                r"\bsorryAx\b",
            )
        ),
        "witness_axiom_rows": len(witness_axiom_rows),
        "bad_witness_lean_exit_status": bad_status,
        "bad_witness_sorry_warning_detected": bad_has_sorry,
        "bad_witness_error_detected": bad_has_error,
        "bad_witness_calibration": "REJECTED" if bad_rejected else "NOT_REJECTED",
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "errors": errors,
        "verdict": "PASS" if not errors and covered == len(load_names) else "FAIL",
    }
    (LOGS / "v7_sanity_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (LOGS / "v7_sanity_summary.log").write_text(
        "\n".join(
            [
                "V7 LOAD-BEARING DEFINITION SANITY CHECK",
                f"LOAD_BEARING_DEFINITIONS {len(load_names)}",
                f"REGISTER_ROWS {len(output_rows)}",
                f"COVERED {covered}",
                f"CITATIONS {method_counts['citation']}",
                f"COMPILED_NAMED_WITNESSES {method_counts['compiled_named_witness']}",
                f"WITNESS_LEAN_EXIT_STATUS {witness_status}",
                f"WITNESS_AXIOM_ROWS {len(witness_axiom_rows)}",
                f"BAD_WITNESS_LEAN_EXIT_STATUS {bad_status}",
                f"BAD_WITNESS_SORRY_WARNING_DETECTED {str(bad_has_sorry).lower()}",
                f"BAD_WITNESS_ERROR_DETECTED {str(bad_has_error).lower()}",
                f"BAD_WITNESS_CALIBRATION {'REJECTED' if bad_rejected else 'NOT_REJECTED'}",
                f"ERRORS {len(errors)}",
                *(f"ERROR {error}" for error in errors),
                f"VERDICT {summary['verdict']}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    if summary["verdict"] != "PASS":
        raise RuntimeError("V7 sanity checker failed; see v7_sanity_summary.log")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
