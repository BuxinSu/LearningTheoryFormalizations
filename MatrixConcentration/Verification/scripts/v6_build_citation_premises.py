#!/usr/bin/env python3
"""Build the fail-closed premise-discharge ledger for Tier-C citations.

A dependency edge alone is not a satisfiability witness.  Each accepted
citation records the exact application line, the target's substantive Prop
premises, how the caller discharges them, and (for any premise-bearing target)
one or more compiled named model witnesses that close the passed-through model
requirements.
"""

from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
LOGS = VERIFICATION / "logs"
AXIOMS = LOGS / "v6_witness_axioms.tsv"
OUTPUT = LOGS / "v6_citation_premise_discharge.tsv"
SUMMARY = LOGS / "v6_citation_premise_discharge_summary.json"
RUN_LOG = LOGS / "v6_citation_premise_discharge.log"
PREFIX = "MatrixConcentration.V6Witnesses."

ANY_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque)\s+"
    r"(?P<name>[^\s({:\[]+)(?=$|[\s({:\[])"
)


def declaration_re(name: str) -> re.Pattern[str]:
    return re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque)\s+"
        + re.escape(name)
        + r"(?=$|[\s({:\[])"
    )


def identifier_re(name: str) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])"
    )


def current_application_site(
    endpoint: str,
    caller: str,
    site_hint: str,
) -> tuple[str, str]:
    """Resolve an endpoint use inside the recorded caller, fail-closed."""

    rel, line_hint = site_hint.rsplit(":", 1)
    old_line = int(line_hint)
    path = PACKAGE_ROOT / rel
    if not path.is_file():
        raise ValueError(f"application file missing: {rel}")
    lines = path.read_text(encoding="utf-8").splitlines()
    caller_starts = [
        line_number
        for line_number, line in enumerate(lines, 1)
        if declaration_re(caller).match(line)
    ]
    if len(caller_starts) != 1:
        raise ValueError(
            f"expected one declaration of caller {caller}, "
            f"found {caller_starts}"
        )
    start = caller_starts[0]
    end = len(lines)
    for line_number in range(start + 1, len(lines) + 1):
        if ANY_DECL_RE.match(lines[line_number - 1]):
            end = line_number - 1
            break
    target = identifier_re(endpoint)
    hits = [
        line_number
        for line_number in range(start, end + 1)
        if target.search(lines[line_number - 1])
    ]
    if not hits:
        raise ValueError(
            f"expected at least one endpoint use in "
            f"{rel}:{start}-{end}, found {hits}"
        )
    distances = {line: abs(line - old_line) for line in hits}
    nearest_distance = min(distances.values())
    nearest = [
        line for line in hits if distances[line] == nearest_distance
    ]
    if len(nearest) != 1:
        raise ValueError(
            f"site hint {old_line} is equidistant from multiple "
            f"endpoint uses in {rel}:{start}-{end}: {nearest}"
        )
    line_number = nearest[0]
    return f"{rel}:{line_number}", lines[line_number - 1]


def row(
    caller: str,
    site: str,
    premises: str,
    classification: str,
    models: tuple[str, ...],
    detail: str,
) -> dict[str, object]:
    return {
        "caller": caller,
        "application_site": site,
        "substantive_prop_premises": premises,
        "discharge_class": classification,
        "model_witnesses": models,
        "discharge_detail": detail,
    }


EVIDENCE: dict[str, dict[str, object]] = {
    "sampleCov_indep_summands": row(
        "sampleCov_varStat_eq", "Chapter1_Introduction.lean:1252",
        "iIndepFun xs μ", "PASSTHROUGH+MODEL",
        ("sampled_bernstein_variance_identity", "suspect_sampleCovariance_nonzero_model"),
        "maps: caller passes `hxs_ind`; the compiled product-sign witness supplies a nonconstant independent finite family, and the nonzero sample-covariance witness fixes `nn=P=1` with nonzero vector data. The measurable coordinate-to-vector transform preserves independence.",
    ),
    "covarianceMatrix_apply": row(
        "covarianceMatrix_eq_sum_single", "Chapter1_Introduction.lean:769",
        "none", "PREMISES-NONE", (),
        "maps: the endpoint has no substantive Prop premise; this is an actual compiled rewrite for arbitrary `x,j,k`.",
    ),
    "norm_covarianceMatrix_le": row(
        "sampleCov_summand_norm_le", "Chapter1_Introduction.lean:919",
        "Measurable x; ∀ᵐ ω, l2norm (x ω)^2 ≤ B", "PASSTHROUGH+MODEL",
        ("sampled_bernstein_variance_identity", "suspect_sampleCovariance_nonzero_model"),
        "maps: caller passes `hx,hB`; the finite product-sign model is measurable and pointwise norm-one, while the nonzero sample witness fixes a genuine one-dimensional complex vector model (`B=1`).",
    ),
    "sampleCov_summand_centered": row(
        "sampleCov_varStat_eq", "Chapter1_Introduction.lean:1249",
        "∀k, IdentDistrib (xs k) x μ μ; ∀k, MIntegrable (vecMulVec (xs k) (star (xs k))) μ",
        "PASSTHROUGH+MODEL",
        ("sampled_bernstein_variance_identity", "suspect_sampleCovariance_nonzero_model"),
        "maps: caller passes `hid` and derives outer-product integrability from `hxs_meas,hBs`; on the compiled singleton product-sign model `xs 0=x`, identical distribution is reflexive and finite-space boundedness gives integrability.",
    ),
    "l2_opNorm_replicateCol": row(
        "l2_opNorm_replicateRow", "Prelude.lean:289", "none",
        "PREMISES-NONE", (),
        "maps: no substantive Prop premise; the caller rewrites the identity for arbitrary finite vector `x`.",
    ),
    "matrixExp_eq_cfc": row(
        "exp_cfc", "Chapter4_MatrixGaussianAndRademacherSeries.lean:91",
        "A.IsHermitian", "CLOSED-DERIVED+MODEL",
        ("sampled_matrix_exp_add_of_commute",),
        "maps: caller constructs `isHermitian_cfc f A`; the compiled identity-matrix exponential witness supplies a nonzero Hermitian finite matrix model.",
    ),
    "cfc_pow_eq": row(
        "commute_cfc", "Chapter8_ProofOfLiebsTheorem.lean:3079",
        "A.IsHermitian", "PASSTHROUGH+MODEL",
        ("sampled_matrix_exp_add_of_commute",),
        "maps: caller passes `hM`; the compiled nonzero identity-matrix model is Hermitian, and any natural `k` (e.g. 2) instantiates the power premise.",
    ),
    "concaveOn_posDef_expectation_le": row(
        "expectation_trace_exp_add_le", "Chapter3_MatrixLaplaceTransformMethod.lean:1635",
        "ConcaveOn PosDef f; Measurable A; 0<a; ∀ω,aI≤Aω; ∀ω,Aω≤bI",
        "CLOSED-DERIVED+MODEL",
        ("sampled_master_expectation_upper_inf_hypotheses",),
        "maps: caller derives concavity from Lieb, measurability of matrix exponential, `a=exp(-R)>0`, and both Loewner bounds from `hHerm,hR`; the compiled bounded nonconstant product-sign Hermitian model supplies `hHerm,hR` with `R=1`.",
    ),
    "lambdaMax_exp": row(
        "exp_lambdaMax_le_trace_exp", "Chapter3_MatrixLaplaceTransformMethod.lean:697",
        "A.IsHermitian", "PASSTHROUGH+MODEL",
        ("suspect_lambdaMax_nonzero_model",),
        "maps: caller passes `hA`; the compiled nonzero identity matrix on `Fin 2` is Hermitian and has genuine maximum eigenvalue one.",
    ),
    "series_second_moment_left": row(
        "gaussian_series_second_moment", "Chapter4_MatrixGaussianAndRademacherSeries.lean:2725",
        "measurable coordinates; independence; centered; square-integrable; unit second moments",
        "PASSTHROUGH+MODEL",
        ("sampled_rademacher_second_moment",),
        "maps: the compiled named Rademacher second-moment theorem uses the product-sign model and discharges exactly measurability, independence, zero mean, square integrability, and unit second moment for a nonzero coefficient.",
    ),
    "erLaplacian_mulVec_one": row(
        "er_second_smallest_tail", "Chapter5_SumOfPSDMatrices.lean:4482",
        "none", "PREMISES-NONE", (),
        "maps: no substantive Prop premise; the caller rewrites the random Laplacian identity for arbitrary edge data.",
    ),
    "posSemidef_lapMatrixC": row(
        "connected_iff_secondSmallest_pos", "Chapter5_SumOfPSDMatrices.lean:3751",
        "none", "PREMISES-NONE", (),
        "maps: no substantive Prop premise; the theorem constructs PSD for every finite simple graph.",
    ),
    "expectation_matsum_eq": row(
        "chernoff_mu_max_eq", "Chapter5_SumOfPSDMatrices.lean:809",
        "∀k, MIntegrable (X k) μ", "PASSTHROUGH+MODEL",
        ("sampled_intdim_chernoff_expectation_ae_hypotheses",),
        "maps: caller passes `hint`; the compiled finite Bernoulli Hermitian model is bounded/measurable on a probability space, hence each singleton summand is MIntegrable, and its nonzero expectation sum is explicitly bounded by `I`.",
    ),
    "exists_compression_isometry": row(
        "connected_iff_secondSmallest_pos", "Chapter5_SumOfPSDMatrices.lean:3738",
        "l2norm v = 1", "CLOSED-DERIVED+MODEL",
        ("suspect_secondSmallest_nonzero_model",),
        "maps: caller obtains `v` as the normalized all-ones vector and proves `hv`; the compiled connected complete graph on `Fin 2` supplies the nonzero graph/dimension model used by the compression chain.",
    ),
    "sparsify_norm_le": row(
        "sparsification_error_bound", "Chapter6_SumOfBoundedRandomMatrices.lean:4014",
        "B ≠ 0", "PASSTHROUGH+MODEL",
        ("suspect_stableRank_nonzero_model",),
        "maps: caller passes `hB`; the compiled identity matrix on `Fin 2` is a concrete nonzero rectangular matrix and therefore gives positive entrywise mass/support.",
    ),
    "bernstein_matrix_cgf_le_one_sided": row(
        "bernstein_cgf_trace_bound_one_sided", "Chapter6_SumOfBoundedRandomMatrices.lean:5790",
        "Measurable X; Hermitian; MIntegrable X,X²; E X=0; pointwise λmax≤L; 0<θ; θL<3",
        "PASSTHROUGH+MODEL",
        ("sampled_bernstein_cgf_ae_hypotheses",),
        "maps: caller passes the seven named hypotheses per summand; the compiled product-sign Hermitian bundle discharges measurability, Hermiticity, both integrabilities, centering, the stronger pointwise norm/λmax bound with `L=1`, and `θ=1` gives `θL<3`.",
    ),
    "exp_le_one_add_bernstein_quadratic": row(
        "bernstein_matrix_mgf_le", "Chapter6_SumOfBoundedRandomMatrices.lean:659",
        "0<θ; a≤L; 0≤L; θL<3", "CLOSED-DERIVED+MODEL",
        ("sampled_bernstein_cgf_ae_hypotheses",),
        "maps: caller derives `a≤L` from the eigenvalue bound and passes `hθ,hL,hθL`; the compiled Bernstein bundle has the consistent concrete choice `θ=L=1` and eigenvalues `a∈{-1,1}`.",
    ),
    "psi_lambdaMax_le_sum": row(
        "generalized_matrix_laplace_tail", "Chapter7_IntrinsicDimension.lean:808",
        "∀s,0≤ψ s; A.IsHermitian", "PASSTHROUGH+MODEL",
        ("suspect_lambdaMax_nonzero_model",),
        "maps: caller passes `hψ0,hY`; choose the compiled nonzero identity Hermitian matrix and the concrete nonnegative function `ψ(s)=s²` to discharge both premises on `Fin 2`.",
    ),
    "intdim_bernstein_herm_tail_core_one_sided": row(
        "intdim_bernstein_herm_tail_one_sided", "Chapter7_IntrinsicDimension.lean:5167",
        "measurable/Hermitian/integrable/centered/independent summands; ae λmax≤L; 0≤L; V PSD,V≠0; variance sum≤V; 0<t; ‖V‖+Lt/3≤t²",
        "CLOSED-DERIVED+MODEL",
        ("sampled_bernstein_cgf_ae_hypotheses", "sampled_intdim_chernoff_expectation_ae_hypotheses"),
        "maps: caller passes the stochastic/variance data, derives `t>0` and the final quadratic inequality from `sqrt ‖V‖+L/3≤t`; the compiled product-sign bundle gives centered bounded independent Hermitian summands, and the compiled nonzero-PSD control bundle supplies `V=I`; choosing `L=1,t=2` satisfies the scalar inequalities.",
    ),
    "intdim_laplace_psd": row(
        "intdim_chernoff_tail", "Chapter7_IntrinsicDimension.lean:1414",
        "Measurable Y; ∀ω,Yω PSD; ∀ω,‖Yω‖≤R; 0<t; 0<θ",
        "CLOSED-DERIVED+MODEL",
        ("sampled_intdim_chernoff_expectation_ae_hypotheses",),
        "maps: caller constructs measurability, PSD, and a finite norm bound for the matrix sum and proves positive `t,θ`; the compiled nonconstant Bernoulli identity-scaled model gives pointwise PSD matrices bounded by one, with concrete `t=θ=1`.",
    ),
    "exp_one_kronecker": row(
        "log_kronecker", "Chapter8_ProofOfLiebsTheorem.lean:3529",
        "none", "PREMISES-NONE", (),
        "maps: no substantive Prop premise; the caller rewrites the identity for arbitrary finite square matrix `M`.",
    ),
    "klein_inequality": row(
        "mre_nonneg", "Chapter8_ProofOfLiebsTheorem.lean:615",
        "scalar tangent inequality on I; A,H Hermitian; spectra of A,H lie in I",
        "CLOSED-DERIVED+MODEL",
        ("sampled_matrixPerspective_arg_posDef",),
        "maps: caller proves the tangent inequality from `entropy_tangent_nonneg`, obtains Hermiticity and positive spectra from PosDef `hA,hH`, and applies Klein on `I=(0,∞)`; the compiled identity PosDef model closes the PosDef premises (distinct positive diagonals are also available).",
    ),
    "one_le_inv_of_le_one": row(
        "inv_shift_loewner_anti", "Chapter8_ProofOfLiebsTheorem.lean:1355",
        "M.PosDef; M≤I", "CLOSED-DERIVED+MODEL",
        ("sampled_matrixPerspective_arg_posDef",),
        "maps: caller derives PosDef `h3` by positive-definite conjugation and `h1` by the conjugation rule; the compiled identity PosDef model gives `M=I`, satisfying both premises without an empty dimension.",
    ),
    "perspectiveFun_convexOn": row(
        "vre_convexOn", "Chapter8_ProofOfLiebsTheorem.lean:228",
        "ConvexOn (0,∞) f; a₁,a₂,h₁,h₂>0; τ∈[0,1]",
        "CLOSED-DERIVED+MODEL",
        ("sampled_matrixPerspective_arg_posDef",),
        "maps: caller supplies `entropyKernel_convexOn`, derives all four positive eigenvalue/coordinate premises from PosDef data, and passes `hτ`; the compiled positive-definite identity model supplies positive coordinates, with concrete `τ=1/2`.",
    ),
}


def main() -> int:
    errors: list[str] = []
    with AXIOMS.open(newline="", encoding="utf-8") as handle:
        axiom_names = {row["name"] for row in csv.DictReader(handle, delimiter="\t")}
    output_rows: list[dict[str, str]] = []
    for endpoint, evidence in EVIDENCE.items():
        site_hint = str(evidence["application_site"])
        caller = str(evidence["caller"])
        try:
            site, source_line = current_application_site(
                endpoint, caller, site_hint
            )
        except (OSError, ValueError) as error:
            errors.append(f"{endpoint}: {error}")
            site = site_hint
            source_line = ""
        models = tuple(evidence["model_witnesses"])
        full_models = tuple(PREFIX + name for name in models)
        if evidence["discharge_class"] == "PREMISES-NONE":
            if evidence["substantive_prop_premises"] != "none" or models:
                errors.append(f"{endpoint}: malformed PREMISES-NONE evidence")
        else:
            if evidence["substantive_prop_premises"] == "none" or not models:
                errors.append(f"{endpoint}: premise-bearing evidence lacks models")
            if "maps:" not in str(evidence["discharge_detail"]):
                errors.append(f"{endpoint}: discharge detail lacks explicit mapping")
        for model in full_models:
            if model not in axiom_names:
                errors.append(f"{endpoint}: model witness lacks axiom evidence: {model}")
        output_rows.append(
            {
                "endpoint": endpoint,
                "caller": str(evidence["caller"]),
                "application_site": site,
                "application_source_line": source_line.strip(),
                "substantive_prop_premises": str(evidence["substantive_prop_premises"]),
                "discharge_class": str(evidence["discharge_class"]),
                "model_witnesses": ";".join(full_models) if full_models else "none",
                "discharge_detail": str(evidence["discharge_detail"]),
                "status": "ACCEPTED",
            }
        )
    if len(EVIDENCE) != 24:
        errors.append(f"citation evidence has {len(EVIDENCE)} rows, expected 24")
    if len(output_rows) != len({row["endpoint"] for row in output_rows}):
        errors.append("duplicate citation endpoint evidence")
    if errors:
        for row_out in output_rows:
            row_out["status"] = "REJECTED"
    fields = list(output_rows[0])
    with OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(output_rows)
    status = "PASS" if not errors else "FAIL"
    classes: dict[str, int] = {}
    for item in output_rows:
        classes[item["discharge_class"]] = classes.get(item["discharge_class"], 0) + 1
    result = {
        "status": status,
        "rows": len(output_rows),
        "discharge_class_counts": dict(sorted(classes.items())),
        "errors": errors,
    }
    SUMMARY.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    lines = [
        "command: python3 MatrixConcentration/Verification/scripts/"
        "v6_build_citation_premises.py",
        f"status: {status}",
        f"citation_rows: {len(output_rows)}",
        "classes: " + ", ".join(f"{k}={v}" for k, v in sorted(classes.items())),
    ]
    lines.extend(f"ERROR: {error}" for error in errors)
    RUN_LOG.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
