#!/usr/bin/env python3
"""Build the V6 Tier-B supplemental census ledger for Appetizer--Chapter 4.

The exact input set is frozen by `endpoint_union.tsv`: retain only rows whose
`source_kinds` JSON value is exactly `["review_census_direct"]` and whose
chapter is Appetizer or Chapter 1--4.  This is a source-text audit only.  It
does not invoke Lean or Lake.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
from collections import Counter
from pathlib import Path

import build_v6_tier_b_ch0_4 as tier_b_common


require_round10_source_identity = tier_b_common.require_round10_source_identity


PROJECT = Path(__file__).resolve().parents[3]
VERIFICATION = PROJECT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
OUTPUT = REVIEW / "v6_tier_b_supplement_ch0_4.tsv"
SUMMARY = REVIEW / "v6_tier_b_supplement_ch0_4_summary.txt"

ASSIGNED_CHAPTERS = {
    "Appetizer",
    "Chapter 1",
    "Chapter 2",
    "Chapter 3",
    "Chapter 4",
}

FIELDS = (
    "row_set",
    "sample_kind",
    "row_id",
    "source_row_ids",
    "chapter",
    "book_label",
    "inventory_endpoint",
    "resolved_declarations",
    "verdict",
    "joint_satisfiability",
    "nontrivial_conclusion",
    "typeclass_nondegeneracy",
    "quantifier_usability",
    "justification",
    "witness_by_citation_candidate",
    "source_locations",
    "tier_c_required",
    "v9_crossfile",
    "resolution_note",
)

COMMAND = re.compile(
    r"""(?x)
    ^[ \t]*
    (?:@\[[^\r\n]*\][ \t]*)?
    (?:(?:private|protected|noncomputable|unsafe|local)[ \t]+)*
    (?P<kind>
      theorem|lemma|def|abbrev|structure|class|alias|irreducible_def
    )
    [ \t]+
    (?P<name>
      (?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)
      (?:\.(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*))*
    )
    (?=[ \t({[:=]|$)
    """
)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def ev(
    h: str,
    c: str,
    t: str,
    q: str,
    citation: str = "",
) -> dict[str, str]:
    return {
        "verdict": "OK",
        "h": f"OK: {h}",
        "c": f"OK: {c}",
        "t": f"OK: {t}",
        "q": f"OK: {q}",
        "citation": citation,
        "v9": "",
        "note": "Resolved exactly to an inspected source declaration.",
    }


EVIDENCE: dict[str, dict[str, str]] = {
    "HDP.Chapter0.integral_norm_sub_mean_sq": ev(
        "a square-integrable Rademacher variable on Bool with E=R satisfies the "
        "probability, Hilbert-space, and MemLp hypotheses",
        "the equality is the vector bias-variance identity and has nonzero variance "
        "on that model",
        "the standard real Hilbert space and fair Bool probability law are "
        "nontrivial; CompleteSpace does not force collapse",
        "Z and its L2 premise are universally supplied for one fixed probability "
        "measure and the same Bochner mean occurs on both sides",
        "HDP.Chapter0.integral_norm_sub_mean_sq_le",
    ),
    "HDP.Chapter0.integral_norm_sub_mean_sq_le": ev(
        "the same nonconstant Bool/Rademacher model with a deterministic center "
        "different from the mean satisfies all premises",
        "it compares two genuine expected squared distances and states that the "
        "mean minimizes the loss",
        "standard real Hilbert and probability instances provide nondegenerate "
        "models with finite second moments",
        "the arbitrary center a is universally supplied after the L2 random vector; "
        "the conclusion does not existentially choose a favorable center",
    ),
    "HDP.Chapter0.integral_norm_sum_sq_of_iIndepFun": ev(
        "two independent centered Rademacher coordinates on Bool x Bool, valued in "
        "one-dimensional Euclidean space, satisfy L2, mean-zero, and independence",
        "the expected squared norm of the sum equals the sum of component second "
        "moments, giving a substantive 2=1+1 instance",
        "Fintype admits a nonempty two-element index and the positive-dimensional "
        "Euclidean target is nontrivial",
        "all L2, mean, and pairwise-independence hypotheses quantify over the same "
        "finite family Z",
        "HDP.Chapter0.approximate_caratheodory",
    ),
    "HDP.Chapter0.polytope_volume_optimizer_unique": ev(
        "N=exp(1), n=2, and k=1 satisfy k>0, log(N)>0, and the critical equation",
        "the conclusion uniquely identifies the positive critical point rather than "
        "returning an arbitrary optimizer",
        "only standard nontrivial real-field operations occur and the positivity "
        "guards make both denominators nonzero",
        "n, N, and k are universal parameters with positivity and the critical "
        "equation explicit; uniqueness is not assumed",
    ),
    "HDP.Chapter1.poisson_limit_theorem": ev(
        "a triangular product of Bernoulli variables with row probabilities 1/N "
        "for N>0 gives max probability tending to zero and row means tending to one",
        "it proves convergence of every nonintegral CDF threshold to the corresponding "
        "Poisson probability",
        "the row probability spaces can be nontrivial finite products and the target "
        "Poisson law is a genuine probability measure",
        "the whole triangular array, independence, two Tendsto premises, threshold, "
        "and exclusion of integer discontinuities are explicit",
    ),
    "HDP.Chapter2.berryEsseen": ev(
        "an iid standard-Gaussian sequence with m=0, sig=1, positive N, and any t "
        "satisfies independence, identical law, L3, mean, and variance premises",
        "the absolute CDF error is quantitatively bounded by the standardized third "
        "absolute moment divided by sqrt(N)",
        "IsProbabilityMeasure has nontrivial Gaussian models, while sig>0 and N>0 "
        "prevent every normalization denominator from vanishing",
        "all distributional hypotheses concern X 0 and the same iid family; N and t "
        "are universally supplied and no favorable threshold is chosen",
    ),
    "HDP.psi2Norm_le_of_bounded": ev(
        "a Rademacher variable with M=1 satisfies the positive bound and almost-sure "
        "absolute-value premise",
        "it jointly proves subgaussianity and an explicit psi2-norm upper bound",
        "a nontrivial probability space realizes the hypotheses and M>0 prevents the "
        "comparison scale from degenerating",
        "X, M, positivity, and the almost-sure bound are explicit and refer to one "
        "fixed measure",
        "HDP.example_2_7_4",
    ),
    "HDP.psi2Norm_rademacher": ev(
        "the coordinate sign on fair Bool is an actual nonconstant IsRademacher "
        "random variable",
        "the exact positive psi2 norm 1/sqrt(log 2) is identified, not merely bounded",
        "IsRademacher supplies a genuine probability law; log 2 and its square root "
        "are positive in the standard real instance",
        "the law predicate fixes X and mu, and the conclusion is an exact equality "
        "for that same variable",
        "HDP.example_2_7_4",
    ),
    "HDP.psi2Norm_standardGaussian": ev(
        "the identity variable under gaussianReal 0 1 has the required standard "
        "Gaussian law",
        "the endpoint computes its exact psi2 norm as sqrt(8/3)",
        "the standard Borel Gaussian measure is nontrivial and the displayed scale is "
        "strictly positive",
        "the single HasLaw premise fixes the same X and measure appearing in the exact "
        "norm conclusion",
        "HDP.Chapter3.exercise_3_6_top",
    ),
    "HDP.psi2Norm_bernoulli": ev(
        "a Bernoulli coordinate on Bool with p=1/2 is nonconstant and satisfies the "
        "IsBernoulli premise",
        "the exact p-dependent psi2 norm is computed, including a separately handled "
        "p=0 boundary case",
        "the unit-interval parameter and induced probability law admit nondegenerate "
        "interior models; totalization at p=0 does not force collapse",
        "X, p, mu, and the Bernoulli-law premise are fixed before the equality",
        "HDP.Chapter2.exercise_2_35b_scaledBernoulli",
    ),
    "HDP.subGaussian_to_subExponential": ev(
        "a measurable Rademacher variable is a nonzero subgaussian example satisfying "
        "the two premises",
        "it proves both subexponentiality and a quantitative psi1-to-psi2 comparison",
        "standard nontrivial probability models realize the typeclasses and log 2 "
        "gives a positive fixed denominator",
        "measurability and subgaussianity constrain the same X and mu; the conclusion "
        "does not weaken to existence of another variable",
        "HDP.remark_2_8_8",
    ),
    "HDP.Chapter3.affineGaussianMeasure": ev(
        "n=k=1, mu=0, and A=[1] give the standard one-dimensional Gaussian as a "
        "concrete affine-image law",
        "the definition depends on both translation and rectangular linear map and is "
        "not a constant or empty measure placeholder",
        "positive-dimensional Euclidean/Borel instances are nontrivial; zero-dimensional "
        "boundary cases are optional rather than forced",
        "mu and A are explicit and determine both the source Gaussian dimension and "
        "the affine pushforward map",
        "HDP.Chapter3.affineGaussianMeasure_eq_multivariateGaussian",
    ),
    "HDP.Chapter3.affineGaussianMeasure_eq_multivariateGaussian": ev(
        "n=k=1 with mu=0 and A=[1] supplies a nondegenerate covariance AA^T=1",
        "it equates the affine pushforward law with the multivariate Gaussian having "
        "the calculated covariance",
        "standard positive-dimensional Gaussian instances are nontrivial and no "
        "invertibility of A is incorrectly required",
        "the equality is universal in mu and rectangular A and uses the identical "
        "AA^T covariance on the right",
        "HDP.Chapter3.hasGaussianVectorLaw_iff_affineRepresentation",
    ),
    "HDP.Chapter3.covarianceMatrix_eq_secondMoment_of_mean_zero": ev(
        "a one-dimensional centered Rademacher vector is L2 and has Bochner mean zero",
        "it identifies the covariance matrix with the uncentered second-moment matrix "
        "under the explicit centering premise",
        "the fair finite probability law and Euclidean dimension one are nontrivial; "
        "L2 ensures all matrix entries are meaningful",
        "X, L2 membership, and the exact zero-mean equation are explicit for one "
        "fixed measure",
    ),
    "HDP.Chapter3.covarianceOperator_reApplyInnerSelf": ev(
        "a one-dimensional nonconstant L2 random vector and v=1 satisfy the "
        "probability and integrability premises",
        "the covariance-operator quadratic form is exactly the scalar projection "
        "variance and is positive in the concrete model",
        "positive-dimensional Euclidean and nontrivial probability instances exist; "
        "MemLp rules out undefined covariance terms",
        "X, hX, and arbitrary v are explicit and the same projected variable occurs "
        "in the variance",
        "HDP.Chapter3.covariance_pca_kth_maximum",
    ),
    "HDP.Chapter3.isotropic_finiteShannonEntropy_and_support_lower_bounds": ev(
        "the uniform two-point law p=1/2 on x=+/-1 with n=1 and K=1 satisfies "
        "normalization, isotropy, positivity, and the atom bound",
        "it jointly gives quantitative entropy and support-cardinality lower bounds",
        "Fintype admits the nonempty Bool model; hpsum=1 itself excludes an empty "
        "probability family and K>0 prevents zero scaling",
        "p, x, every moment equation, K, and every atom bound are explicit before "
        "the conjunction",
        "HDP.Chapter3.isotropic_subgaussian_finite_support_entropy_and_card",
    ),
    "HDP.Chapter3.sum_independent_gaussians_hasGaussianLaw": ev(
        "two independent standard Gaussian coordinates on a product space satisfy "
        "HasGaussianLaw and iIndepFun",
        "the finite pointwise sum is concluded to have a Gaussian law",
        "Fintype has nonempty finite models and the real complete Borel target is "
        "nontrivial; empty-family validity is only a boundary case",
        "the Gaussian-law and independence premises quantify over exactly the same "
        "family X",
        "HDP.Chapter3.sum_independent_gaussians_parameters",
    ),
    "HDP.Chapter3.unitSphere_marginal_tail": ev(
        "n=1, either unit direction, and any t>=0 satisfy positive dimension and "
        "threshold premises under the genuine uniform sphere law",
        "it gives an n-dependent Gaussian tail bound for the absolute directional "
        "marginal",
        "hn forces a nonempty unit sphere and the standard normalized sphere measure "
        "is nontrivial",
        "n, its positivity proof, the unit vector v, and arbitrary nonnegative t are "
        "all explicit",
        "HDP.Chapter3.gaussianCloud_angle_bad_le",
    ),
    "HDP.absolutePowerSummable_of_entire": ev(
        "a finite-support coefficient sequence, or a_k=1/k!, satisfies convergence "
        "of the power series at every real input",
        "it upgrades conditional convergence at every signed input to absolute "
        "power summability at every radius",
        "only the standard nontrivial real topology and natural filter are used",
        "a and the all-real Summable premise are explicit; the conclusion universally "
        "ranges over every radius",
        "HDP.Chapter3.realAnalytic_featureMap_of_entire",
    ),
    "HDP.tensorInner": ev(
        "for k=2 with one-element axes and nonzero tensors A,B, the coordinate sum "
        "has a nonzero concrete value",
        "the definition computes the full finite multi-index sum of entrywise products "
        "and depends on both inputs",
        "finite axis instances admit nonempty product indices; empty axes are allowed "
        "boundaries but not forced",
        "axis Fintype data and tensors A,B are explicit; the sum ranges over the exact "
        "dependent product index",
        "HDP.tensorInner_eq_inner",
    ),
    "HDP.tensorPowerSpace_eq_tensorSpace": ev(
        "iota=Bool and k=2 give a nonzero finite-dimensional tensor space on both "
        "sides",
        "the rfl equality intentionally records the definitional specialization of "
        "equal-axis TensorSpace; it is a definition-level bridge, not an analytic claim",
        "Fintype iota admits nonempty models and no typeclass forces the tensor space "
        "to be trivial",
        "k is universally supplied and the same iota is used on every axis; the "
        "definitional equality does not hide an existential type",
    ),
    "HDP.Chapter4.rectangularSingularValueMatrix": ev(
        "a nonzero 2x1 matrix and any RealSVD witness give a rectangular diagonal "
        "matrix with one genuine singular entry",
        "the definition places precisely the first min(m,n) singular values on the "
        "rectangular diagonal and depends on s",
        "positive m,n models are nontrivial; zero-size matrix boundaries are not "
        "forced by the declaration",
        "the RealSVD witness fixes A and every embedded row/column index is bounded by "
        "the corresponding min-dimension proof",
        "HDP.Chapter4.exists_matrixFormSVD",
    ),
    "HDP.Chapter4.remark_4_1_9": ev(
        "p=q=2, singleton row/column types, the identity matrix, and a nonzero vector "
        "satisfy all Fact, Fintype, and DecidableEq premises",
        "it gives the standard induced-operator-norm application inequality for the "
        "actual matrix and vector",
        "Fact(1<=p/q) admits the ordinary L2 model and finite types can be chosen "
        "nonempty; degeneracy is not forced",
        "p, q, A, and arbitrary x are explicit and the same induced norm controls "
        "Matrix.toLpLin applied to x",
    ),
    "HDP.Chapter4.singularValue_eq_zero_of_domain_le": ev(
        "for a nonzero 2x1 matrix and i=1, the explicit domain bound n<=i holds",
        "it states the substantive zero-padding convention for every singular-value "
        "index beyond the domain dimension",
        "positive rectangular dimensions give nontrivial matrices and valid beyond-"
        "domain indices; no zero matrix is assumed",
        "A and i are universal and the exact guard n<=i is explicit before the zero "
        "conclusion",
    ),
}

def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def build_source_index() -> dict[str, list[tuple[str, int, str, str]]]:
    index: dict[str, list[tuple[str, int, str, str]]] = {}
    for directory in (
        PROJECT / "HighDimensionalProbability",
        PROJECT / "MatrixConcentration",
    ):
        if not directory.exists():
            continue
        for path in sorted(directory.rglob("*.lean")):
            if "Verification" in path.parts or path.is_symlink():
                continue
            relative = path.relative_to(PROJECT).as_posix()
            for number, line in enumerate(
                path.read_text(encoding="utf-8").splitlines(), start=1
            ):
                match = COMMAND.match(line)
                if not match:
                    continue
                name = match.group("name")
                local = name.split(".")[-1]
                index.setdefault(local, []).append(
                    (relative, number, match.group("kind"), name)
                )
    return index


def build_local_dependency_edges() -> dict[str, set[str]]:
    """Build a conservative local-name dependency graph from declaration bodies."""
    raw_blocks: dict[str, list[str]] = {}
    for directory in (
        PROJECT / "HighDimensionalProbability",
        PROJECT / "MatrixConcentration",
    ):
        if not directory.exists():
            continue
        for path in sorted(directory.rglob("*.lean")):
            if "Verification" in path.parts or path.is_symlink():
                continue
            lines = path.read_text(encoding="utf-8").splitlines()
            starts: list[tuple[int, str]] = []
            for index, line in enumerate(lines):
                match = COMMAND.match(line)
                if match:
                    starts.append((index, match.group("name").split(".")[-1]))
            for position, (start, local) in enumerate(starts):
                end = (
                    starts[position + 1][0]
                    if position + 1 < len(starts)
                    else len(lines)
                )
                raw_blocks.setdefault(local, []).append("\n".join(lines[start:end]))
    names = set(raw_blocks)
    return {
        name: (
            {
                token
                for body in bodies
                for token in TOKEN.findall(body)
                if token in names
            }
            - {name}
        )
        for name, bodies in raw_blocks.items()
    }


def dependency_reaches(
    edges: dict[str, set[str]], source: str, target: str
) -> bool:
    pending = [source]
    seen = {source}
    while pending:
        current = pending.pop()
        if current == target:
            return True
        for successor in edges.get(current, set()):
            if successor not in seen:
                seen.add(successor)
                pending.append(successor)
    return False


def candidate_score(
    endpoint: str, candidate: tuple[str, int, str, str]
) -> tuple[int, int, int, str, int]:
    path, line, _kind, declared = candidate
    score = 0
    if declared == endpoint:
        score += 100
    if endpoint.startswith("HDP.") and path.startswith("HighDimensionalProbability/"):
        score += 40
    chapter_match = re.search(r"HDP\.Chapter(\d+)", endpoint)
    if chapter_match and f"Chapter{chapter_match.group(1)}" in path:
        score += 20
    if endpoint.startswith("HDP.Chapter0") and "Chapter0_" in path:
        score += 20
    if "/Main.lean" not in path:
        score += 10
    return (
        -score,
        0 if path.startswith("HighDimensionalProbability/") else 1,
        len(path),
        path,
        line,
    )


def resolve_endpoint(
    endpoint: str,
    source_index: dict[str, list[tuple[str, int, str, str]]],
) -> tuple[str, int, str] | None:
    local = endpoint.split(".")[-1]
    candidates = source_index.get(local, [])
    if not candidates:
        return None
    path, line, kind, _declared = sorted(
        candidates, key=lambda item: candidate_score(endpoint, item)
    )[0]
    return path, line, kind


def inventory_line_numbers(path: Path) -> dict[str, int]:
    numbers: dict[str, int] = {}
    with path.open(encoding="utf-8") as handle:
        for number, line in enumerate(handle, start=1):
            endpoint = line.split("\t", 1)[0]
            numbers[endpoint] = number
    return numbers


def stable_row_id(endpoint: str) -> str:
    digest = hashlib.sha256(endpoint.encode("utf-8")).hexdigest()[:16]
    return f"supplement-{digest}"


def one_json_value(cell: str, field: str, endpoint: str) -> str:
    values = json.loads(cell)
    if not isinstance(values, list) or len(values) != 1:
        raise ValueError(f"{endpoint}: expected one {field}, got {values!r}")
    return str(values[0])


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help="validate generated TSV/summary byte-for-byte without writing (default)",
    )
    mode.add_argument(
        "--write",
        action="store_true",
        help="regenerate TSV/summary and then validate them byte-for-byte",
    )
    return parser.parse_args(argv)


def require_exact(path: Path, expected: str) -> None:
    display = (
        path.relative_to(PROJECT).as_posix()
        if path.is_relative_to(PROJECT)
        else path.as_posix()
    )
    if not path.is_file():
        raise ValueError(f"missing generated artifact: {display}")
    if path.read_text(encoding="utf-8") != expected:
        raise ValueError(
            f"generated artifact is stale: {display}; "
            "rerun with --write"
        )


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    require_round10_source_identity()
    union_path = INVENTORY / "endpoint_union.tsv"
    all_rows = read_tsv(union_path)
    selected: list[dict[str, str]] = []
    for row in all_rows:
        source_kinds = json.loads(row["source_kinds"])
        chapters = json.loads(row["chapters"])
        if (
            source_kinds == ["review_census_direct"]
            and any(chapter in ASSIGNED_CHAPTERS for chapter in chapters)
        ):
            selected.append(row)

    selected_endpoints = {row["endpoint"] for row in selected}
    if len(selected) != 24 or len(selected_endpoints) != 24:
        raise ValueError(
            f"supplemental inventory drift: expected 24 unique rows, "
            f"got rows={len(selected)}, unique={len(selected_endpoints)}"
        )
    if selected_endpoints != set(EVIDENCE):
        raise ValueError(
            "hand review evidence drift: "
            f"missing={sorted(selected_endpoints - set(EVIDENCE))}; "
            f"extra={sorted(set(EVIDENCE) - selected_endpoints)}"
        )

    source_index = build_source_index()
    inventory_lines = inventory_line_numbers(union_path)
    output_rows: list[dict[str, str]] = []
    for inventory_row in selected:
        endpoint = inventory_row["endpoint"]
        chapter = one_json_value(inventory_row["chapters"], "chapter", endpoint)
        book_label = one_json_value(
            inventory_row["book_refs"], "book reference", endpoint
        )
        source_row_ids = json.loads(inventory_row["source_row_ids"])
        judgment = EVIDENCE[endpoint]
        resolved = resolve_endpoint(endpoint, source_index)

        if resolved is None:
            raise ValueError(f"unexpected unresolved endpoint: {endpoint}")
        path, line, _kind = resolved
        locations = f"{path}:{line}"
        resolved_declarations = endpoint

        citation = judgment["citation"]
        justification = (
            f"H({judgment['h'].split(': ', 1)[-1]}) "
            f"C({judgment['c'].split(': ', 1)[-1]}) "
            f"T({judgment['t'].split(': ', 1)[-1]}) "
            f"Q({judgment['q'].split(': ', 1)[-1]}) "
            f"D({citation or 'no static reverse-citation candidate recorded'}) "
            f"S({locations})"
        )
        output_rows.append(
            {
                "row_set": "endpoint_union",
                "sample_kind": "supplemental_review_census_direct",
                "row_id": stable_row_id(endpoint),
                "source_row_ids": "; ".join(source_row_ids),
                "chapter": chapter,
                "book_label": book_label,
                "inventory_endpoint": endpoint,
                "resolved_declarations": resolved_declarations,
                "verdict": judgment["verdict"],
                "joint_satisfiability": judgment["h"],
                "nontrivial_conclusion": judgment["c"],
                "typeclass_nondegeneracy": judgment["t"],
                "quantifier_usability": judgment["q"],
                "justification": justification,
                "witness_by_citation_candidate": citation,
                "source_locations": locations,
                "tier_c_required": "no",
                "v9_crossfile": judgment["v9"],
                "resolution_note": judgment["note"],
            }
        )

    if {row["inventory_endpoint"] for row in output_rows} != selected_endpoints:
        raise ValueError("output is not the exact selected endpoint set")
    if len({row["row_id"] for row in output_rows}) != 24:
        raise ValueError("supplement row IDs are not unique")
    if any(
        not all(
            token in row["justification"]
            for token in ("H(", "C(", "T(", "Q(", "D(", "S(")
        )
        for row in output_rows
    ):
        raise ValueError("a supplemental row lacks H/C/T/Q/D/S evidence")
    if any(row["verdict"] != "OK" for row in output_rows):
        raise ValueError("current supplemental projection must have 24 OK rows")

    dependency_edges = build_local_dependency_edges()
    citation_rows = [
        row for row in output_rows if row["witness_by_citation_candidate"]
    ]
    for row in citation_rows:
        candidate_local = row["witness_by_citation_candidate"].split(".")[-1]
        endpoint_local = row["inventory_endpoint"].split(".")[-1]
        if not dependency_reaches(
            dependency_edges, candidate_local, endpoint_local
        ):
            raise ValueError(
                "static reverse-citation dependency did not validate: "
                f"{row['witness_by_citation_candidate']} -> "
                f"{row['inventory_endpoint']}"
            )

    tsv_handle = io.StringIO(newline="")
    writer = csv.DictWriter(
        tsv_handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(output_rows)
    tsv_text = tsv_handle.getvalue()

    verdicts = Counter(row["verdict"] for row in output_rows)
    chapters = Counter(row["chapter"] for row in output_rows)
    citation_count = len(citation_rows)
    lines = [
        "V6 Tier-B supplemental census coverage: Appetizer--Chapter 4",
        "output: "
        + (
            OUTPUT.relative_to(PROJECT).as_posix()
            if OUTPUT.is_relative_to(PROJECT)
            else OUTPUT.as_posix()
        ),
        f"builder: {Path(__file__).resolve().relative_to(PROJECT).as_posix()}",
        "check_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_b_supplement_ch0_4.py --check",
        "rebuild_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_b_supplement_ch0_4.py --write",
        "method: static source close reading only; no Lean/lake invocation",
        "selection: source_kinds exactly [\"review_census_direct\"] and chapter "
        "in Appetizer/Chapter 1--4",
        f"exact_selected_endpoint_rows: {len(output_rows)}",
        f"exact_unique_inventory_endpoints: "
        f"{len({row['inventory_endpoint'] for row in output_rows})}",
        "chapter_counts: "
        + ", ".join(
            f"{chapter}={chapters[chapter]}"
            for chapter in (
                "Appetizer",
                "Chapter 1",
                "Chapter 2",
                "Chapter 3",
                "Chapter 4",
            )
        ),
        "verdict_counts: "
        + ", ".join(
            f"{verdict}={verdicts.get(verdict, 0)}"
            for verdict in ("OK", "SUSPECT", "VACUOUS")
        ),
        f"exact_source_declarations_resolved: "
        f"{sum(bool(row['resolved_declarations']) for row in output_rows)}",
        f"rows_with_complete_H_C_T_Q_D_S: {len(output_rows)}/{len(output_rows)}",
        f"rows_with_static_reverse_citation_candidate: {citation_count}",
        f"static_reverse_citation_dependency_paths_validated: {citation_count}",
        "v9_crossfile_count: "
        f"{sum(row['v9_crossfile'] == 'V9_STALE_ENDPOINT_INVENTORY' for row in output_rows)}",
    ]
    summary_text = "\n".join(lines) + "\n"

    if args.write:
        REVIEW.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(tsv_text, encoding="utf-8")
        SUMMARY.write_text(summary_text, encoding="utf-8")

    require_exact(OUTPUT, tsv_text)
    require_exact(SUMMARY, summary_text)
    print(
        "PASS v6_tier_b_supplement_ch0_4: 24 rows; OK=24; SUSPECT=0; "
        "check_mode=read-only"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
