#!/usr/bin/env python3
"""Build/check the V6 Tier-B supplemental ledger for Chapters 5--7.

The project endpoint inventory is `endpoint_union.tsv`.  The raw set consists
of rows whose `source_kinds` JSON value is exactly
`["review_census_direct"]` and whose chapter is 5, 6, or 7.  Every endpoint
already named in the main Chapters 5--7 V6 ledger is then excluded.

This is a deterministic source-text audit.  It reads inventories, review
artifacts, current Lean source, and publication-status Markdown, but never
invokes Lean or Lake.  `--check` is read-only; `--write` regenerates the TSV
and summary and then checks them byte-for-byte.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
from collections import Counter
from pathlib import Path

import build_v6_tier_b_supplement_ch0_4 as common


PROJECT = Path(__file__).resolve().parents[3]
VERIFICATION = PROJECT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
MAIN_LEDGER = REVIEW / "v6_tier_b_ch5_7.tsv"
OUTPUT = REVIEW / "v6_tier_b_supplement_ch5_7.tsv"
SUMMARY = REVIEW / "v6_tier_b_supplement_ch5_7_summary.txt"

ASSIGNED_CHAPTERS = {"Chapter 5", "Chapter 6", "Chapter 7"}
CHAPTER_ORDER = ("Chapter 5", "Chapter 6", "Chapter 7")

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

STALE_LIPSCHITZ = "HDP.Chapter5.LipschitzWith"

EXPECTED_MAIN_OVERLAP = {
    "HDP.Chapter5.grassmannDistance",
    "HDP.Chapter5.grassmannHaarMeasure",
    "HDP.Chapter5.grassmannian_concentration",
}

EXPECTED_SOURCE_LOCATIONS: dict[str, tuple[str, int, str]] = {
    "HDP.Chapter5.bounded_differences": (
        "HighDimensionalProbability/Appendix/BoundedDifferences.lean",
        17,
        "theorem",
    ),
    "HDP.Chapter5.euclidean_isoperimetric": (
        "HighDimensionalProbability/Appendix/EuclideanIsoperimetric.lean",
        25,
        "theorem",
    ),
    "HDP.Chapter5.exercise_5_17a_commutingMatrixFunction_monotone": (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        6347,
        "theorem",
    ),
    "HDP.Chapter5.exists_measureMedian": (
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        1440,
        "theorem",
    ),
    "HDP.Chapter5.gaussian_isoperimetric": (
        "HighDimensionalProbability/Appendix/GaussianIsoperimetric.lean",
        24,
        "theorem",
    ),
    "HDP.Chapter5.hamming_cube_concentration": (
        "HighDimensionalProbability/Appendix/HammingCubeConcentration.lean",
        36,
        "theorem",
    ),
    "HDP.Chapter5.special_orthogonal_concentration": (
        "HighDimensionalProbability/Appendix/SpecialOrthogonalConcentration.lean",
        133,
        "theorem",
    ),
    "HDP.Chapter5.spherical_isoperimetric": (
        "HighDimensionalProbability/Appendix/SphericalIsoperimetric.lean",
        23,
        "theorem",
    ),
    "HDP.Chapter5.strongly_convex_density_concentration": (
        "HighDimensionalProbability/Appendix/StronglyConvexDensity.lean",
        21,
        "theorem",
    ),
    "HDP.Chapter5.symmetric_group_concentration": (
        "HighDimensionalProbability/Appendix/SymmetricGroupConcentration.lean",
        48,
        "theorem",
    ),
    "HDP.Chapter5.talagrand_convex_concentration": (
        "HighDimensionalProbability/Appendix/TalagrandConvexConcentration.lean",
        29,
        "theorem",
    ),
    "HDP.Chapter7.crossPolytopeGaussianWidth_asymptotic_actual": (
        "HighDimensionalProbability/Chapter7_RandomProcesses.lean",
        12971,
        "theorem",
    ),
    "HDP.Chapter7.brownianReflectionPrinciple_external": (
        "HighDimensionalProbability/Appendix/BrownianReflection.lean",
        159,
        "theorem",
    ),
}

# Reverse-citation candidates and the exact current declaration locations of
# those downstream dependents.  The builder also validates a source-token
# dependency path from each candidate back to the reviewed endpoint.
CITATIONS: dict[str, tuple[str, str, int]] = {
    "HDP.Chapter5.bounded_differences": (
        "HDP.Chapter5.hamming_cube_concentration",
        "HighDimensionalProbability/Appendix/HammingCubeConcentration.lean",
        36,
    ),
    "HDP.Chapter5.exists_measureMedian": (
        "HDP.Chapter5.exists_isMedian",
        "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean",
        1500,
    ),
    "HDP.Chapter5.special_orthogonal_concentration": (
        "HDP.Chapter5.grassmannian_concentration",
        "HighDimensionalProbability/Appendix/GrassmannianConcentration.lean",
        181,
    ),
    "HDP.Chapter5.spherical_isoperimetric": (
        "HDP.Appendix.gaussian_isoperimetric_poincare",
        "HighDimensionalProbability/Appendix/Infra/"
        "PoincareIsoperimetricLimit.lean",
        345,
    ),
    "HDP.Chapter7.crossPolytopeGaussianWidth_asymptotic_actual": (
        "HDP.Chapter7.crossPolytopeGaussianWidth_twoSided",
        "HighDimensionalProbability/Chapter7_RandomProcesses.lean",
        12993,
    ),
}


def ev(
    h: str,
    c: str,
    t: str,
    q: str,
    *,
    verdict: str = "OK",
    v9: str = "",
    note: str = "RESOLVED_EXACT: inspected the current Lean declaration.",
) -> dict[str, str]:
    return {
        "verdict": verdict,
        "h": f"{verdict}: {h}",
        "c": f"{verdict}: {c}",
        "t": f"{verdict}: {t}",
        "q": f"{verdict}: {q}",
        "v9": v9,
        "note": note,
    }


EVIDENCE: dict[str, dict[str, str]] = {
    STALE_LIPSCHITZ: ev(
        "the Pass-07 replacement overlay maps the historical qualified key to the "
        "global Mathlib LipschitzWith definition, which has nonconstant identity-map models",
        "the resolved global definition is a substantive pairwise distance bound",
        "standard nontrivial metric spaces instantiate global LipschitzWith",
        "the overlay records that the old namespace_inherited qualification was "
        "inventory metadata, not a new project declaration",
        note=(
            "PASS07_REPLACED_HISTORICAL_KEY: the authoritative symbol is global "
            "Mathlib LipschitzWith; no project declaration under the stale "
            "HDP.Chapter5-qualified name is asserted."
        ),
    ),
    "HDP.Chapter5.bounded_differences": ev(
        "N=1, X 0=Bool with the fair law, f the indicator coordinate, and c 0=1 "
        "satisfy measurability, integrability, nonnegative sensitivity, and the "
        "one-coordinate bounded-difference premise",
        "the upper-tail probability is bounded by exp(-2 t^2/sum c_i^2), which is "
        "strictly informative for the nonconstant Bool model and positive t",
        "the dependent finite product has a nontrivial probability instance; the "
        "permitted zero-sensitivity boundary does not force the concrete c=1 model",
        "the coordinate laws, f, c, sensitivity, integrability, and every t>=0 "
        "refer to the same product measure and no independence assumption is hidden",
    ),
    "HDP.Chapter5.euclidean_isoperimetric": ev(
        "n=1, A equal to the radius-one closed ball, r=1, and epsilon=1 satisfy "
        "NeZero, measurability, positivity, and the equal-volume premise",
        "the conclusion compares closed-expansion volumes for every measurable "
        "equal-volume competitor; that expansion inequality is not assumed",
        "NeZero n forces positive ambient dimension and the explicit r,epsilon>0 "
        "guards remove the old empty/zero-radius degeneration",
        "A is universally supplied before the mass equality and the ball is fixed "
        "by the same r; no favorable competitor is existentially selected",
    ),
    "HDP.Chapter5.exercise_5_17a_commutingMatrixFunction_monotone": ev(
        "on Fin 2, diagonal Hermitian A=diag(0,1), B=diag(1,2), and f(x)=x "
        "satisfy commutation, Loewner order, and scalar monotonicity",
        "the continuous-functional-calculus Loewner inequality can be strict and "
        "is not one of the hypotheses",
        "Fintype and DecidableEq admit the nonempty Fin 2 model; allowing an empty "
        "index boundary elsewhere does not force matrix collapse",
        "A, B, their Hermitian/commuting/order evidence, and arbitrary monotone f "
        "are explicit and constrain the same two matrices",
    ),
    "HDP.Chapter5.exists_measureMedian": ev(
        "the fair two-atom probability measure on the real points -1 and 1 is a "
        "nonconstant concrete instance",
        "it constructs one real M satisfying both closed half-mass inequalities, "
        "including the substantive atomic case",
        "the standard real Borel space and a nontrivial probability measure supply "
        "all instances; no empty measurable space is required",
        "the probability measure is universal and the median is chosen afterward; "
        "neither half-mass inequality is assumed",
    ),
    "HDP.Chapter5.gaussian_isoperimetric": ev(
        "n=1, u=1, A equal to gaussianHalfspace u 0, and epsilon=1 satisfy "
        "NeZero, unit norm, measurability, positivity, and equal Gaussian mass",
        "the theorem compares closed-expansion Gaussian masses for every measurable "
        "equal-mass competitor; the desired expansion comparison is not a premise",
        "NeZero n and the unit-vector equation give a positive-dimensional "
        "nondegenerate standard Gaussian model",
        "A,u,a,epsilon and the mass equality are explicit and the reference "
        "halfspace uses the same u and a",
    ),
    "HDP.Chapter5.hamming_cube_concentration": ev(
        "n=2 gives a four-point normalized Hamming cube with nonconstant "
        "one-Lipschitz observables under the uniform law",
        "one absolute positive constant controls all positive dimensions at the "
        "nonzero scale C/sqrt(n), yielding genuine two-sided mean concentration",
        "the n>0 guard makes the finite cube nonempty and the normalized distance "
        "well-defined; its uniform law is a genuine probability measure",
        "C is chosen before n and HasMeanConcentration then universally binds the "
        "observable and threshold, rather than choosing a favorable function",
    ),
    "HDP.Chapter5.special_orthogonal_concentration": ev(
        "n=2 gives the nontrivial rotation circle with canonical Borel Haar and n=3 "
        "gives a positive-dimensional compact group; both satisfy the stated range",
        "one positive absolute constant supplies mean concentration at scale "
        "C/sqrt(n) for every n>=2",
        "the dimension guard excludes empty matrix indices and the canonical Haar "
        "law is a genuine probability measure, not an arbitrary supplied measure",
        "C is chosen before n and the theorem directly exports HasMeanConcentration "
        "without a hidden diffusion certificate",
    ),
    "HDP.Chapter5.spherical_isoperimetric": ev(
        "n=2, a unit u, a positive-mass hemisphere cap, A equal to that cap, and "
        "epsilon=1 satisfy every measurable, positivity, and equal-mass premise",
        "closed-expansion sphere measure of the cap is minimal among arbitrary "
        "equal-mass measurable competitors; this inequality is not assumed",
        "n>=2, unit norm, and positive cap mass explicitly rule out the old "
        "zero-area cap and empty-sphere degeneracies",
        "the competitor A is universal and the reference cap is fixed by the same "
        "u,a; only its initial mass is equated",
    ),
    "HDP.Chapter5.strongly_convex_density_concentration": ev(
        "in dimension one, U(x)=x^2/2 plus the Gaussian normalizing constant with "
        "kappa=1 is measurable, strongly convex, and gives total density mass one",
        "one positive absolute constant yields dimension-free mean concentration "
        "for the normalized strongly log-concave law",
        "NeZero n and kappa>0 give a positive-dimensional, positive-curvature "
        "model; the mass-one premise supplies a genuine probability measure",
        "C is chosen before n,U,kappa and the normalization is an explicit premise, "
        "not a hidden instance or the desired concentration statement",
    ),
    "HDP.Chapter5.symmetric_group_concentration": ev(
        "n=2 gives the two-element permutation group with nonconstant normalized "
        "Hamming observables under its uniform law",
        "one positive constant controls all positive n at scale C/sqrt(n), a "
        "substantive concentration assertion for nonconstant permutations",
        "n>0 makes Fin n nonempty and the finite uniform permutation law a genuine "
        "probability measure",
        "C precedes n and HasMeanConcentration universally quantifies the observable "
        "and threshold on the same permutation metric space",
    ),
    "HDP.Chapter5.talagrand_convex_concentration": ev(
        "n=1, the fair law on {-1,1}, and the coordinate function satisfy cube "
        "support, convexity, measurability, local Euclidean Lipschitzness, and "
        "integrability",
        "the centered product-law tail receives a positive Gaussian exponential "
        "bound for every t>=0 and varies with the chosen convex observable",
        "finite product probability spaces have nontrivial one-coordinate models; "
        "the valid n=0 boundary is optional rather than forced",
        "the absolute C is selected before n, the coordinate laws, f, and t, and all "
        "support/locality guards constrain those same data",
    ),
    "HDP.Chapter7.crossPolytopeGaussianWidth_asymptotic_actual": ev(
        "this is a closed theorem for the canonical independent standard-Gaussian "
        "sequence; Fin(k+2) is always nonempty and gaussianMaxScale is positive",
        "the ratio of actual cross-polytope width to the sharp Gaussian-maximum "
        "scale tends to one, a nonconstant asymptotic statement",
        "canonical Gaussian product laws and positive finite index sets are "
        "nondegenerate for every k",
        "the atTop limit fixes the full canonical sequence and normalization; no "
        "subsequence or existential comparison constants weaken the claim",
    ),
    "HDP.Chapter7.brownianReflectionPrinciple_external": ev(
        "the standard Wiener process satisfies the supplied Brownian-law "
        "hypotheses, and every finite queried time family has a genuine "
        "nonconstant Gaussian increment model",
        "the theorem proves the finite-subfamily expected-supremum reflection "
        "interface, whose specialization gives the exact Brownian maximum "
        "expectation rather than assuming it",
        "the universal probability space and Brownian process admit the standard "
        "nondegenerate Wiener model; positive times produce nonzero variance",
        "the probability measure and process are fixed before the Brownian-law "
        "argument and queried time, so the reflection conclusion cannot choose "
        "favorable sample data",
        note=(
            "RESOLVED_EXACT: the current active census records the completed "
            "source-faithful Brownian appendix theorem."
        ),
    ),
}


def line_number_containing(path: Path, needle: str) -> int:
    matches = [
        number
        for number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        )
        if needle in line
    ]
    if len(matches) != 1:
        raise ValueError(
            f"expected one occurrence of {needle!r} in {path}, got {matches}"
        )
    return matches[0]


def row_line_numbers(path: Path, key_field: str) -> dict[str, int]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        return {
            row[key_field]: number
            for number, row in enumerate(reader, start=2)
        }


def main_endpoint_set() -> set[str]:
    endpoints: set[str] = set()
    for row in common.read_tsv(MAIN_LEDGER):
        endpoints.update(
            endpoint
            for endpoint in row["resolved_declarations"].split("; ")
            if endpoint
        )
    return endpoints


def load_exact_selection() -> tuple[
    list[dict[str, str]], list[dict[str, str]], set[str]
]:
    all_rows = common.read_tsv(INVENTORY / "endpoint_union.tsv")
    main_endpoints = main_endpoint_set()
    raw = [
        row
        for row in all_rows
        if json.loads(row["source_kinds"]) == ["review_census_direct"]
        and any(
            chapter in ASSIGNED_CHAPTERS
            for chapter in json.loads(row["chapters"])
        )
    ]
    overlap = {row["endpoint"] for row in raw if row["endpoint"] in main_endpoints}
    selected = [row for row in raw if row["endpoint"] not in main_endpoints]
    selected_endpoints = {row["endpoint"] for row in selected}

    if (len(raw), len({row["endpoint"] for row in raw})) != (17, 17):
        raise ValueError(
            "raw supplemental inventory drift: expected 17 unique rows; "
            f"got rows={len(raw)}, unique={len({row['endpoint'] for row in raw})}"
        )
    if overlap != EXPECTED_MAIN_OVERLAP:
        raise ValueError(
            "main-ledger overlap drift: "
            f"missing={sorted(EXPECTED_MAIN_OVERLAP - overlap)}; "
            f"extra={sorted(overlap - EXPECTED_MAIN_OVERLAP)}"
        )
    if (len(selected), len(selected_endpoints)) != (14, 14):
        raise ValueError(
            "supplemental exact-set drift: expected 14 unique rows; "
            f"got rows={len(selected)}, unique={len(selected_endpoints)}"
        )
    if selected_endpoints != set(EVIDENCE):
        raise ValueError(
            "hand-review evidence drift: "
            f"missing={sorted(selected_endpoints - set(EVIDENCE))}; "
            f"extra={sorted(set(EVIDENCE) - selected_endpoints)}"
        )
    return raw, selected, main_endpoints


def validate_declaration_line(
    endpoint: str, location: tuple[str, int, str]
) -> None:
    path_text, line, kind = location
    path = PROJECT / path_text
    if not path.is_file():
        raise ValueError(f"{endpoint}: missing source file {path_text}")
    lines = path.read_text(encoding="utf-8").splitlines()
    if not 1 <= line <= len(lines):
        raise ValueError(f"{endpoint}: line out of range: {path_text}:{line}")
    match = common.COMMAND.match(lines[line - 1])
    if (
        match is None
        or match.group("kind") != kind
        or match.group("name").split(".")[-1] != endpoint.split(".")[-1]
    ):
        raise ValueError(
            f"{endpoint}: declaration mismatch at {path_text}:{line}: "
            f"{lines[line - 1]!r}"
        )


def v9_extra_locations(
    endpoint: str,
    union_lines: dict[str, int],
    census_lines: dict[str, int],
) -> list[str]:
    if endpoint == STALE_LIPSCHITZ:
        return [
            "HighDimensionalProbability/Verification/inventory/"
            f"endpoint_union.tsv:{union_lines[endpoint]}",
            "HighDimensionalProbability/Verification/inventory/"
            f"review_census_835.tsv:{census_lines['census-e77ea5243e1dd79c']}",
            ".lake/packages/mathlib/Mathlib/Topology/EMetricSpace/"
            "Lipschitz.lean:58",
            "HighDimensionalProbability/"
            "Chapter5_ConcentrationWithoutIndependence.lean:104",
        ]
    return []


def build_rows() -> tuple[
    list[dict[str, str]], list[dict[str, str]], set[str]
]:
    raw, selected, main_endpoints = load_exact_selection()
    source_index = common.build_source_index()
    dependency_edges = common.build_local_dependency_edges()
    union_lines = common.inventory_line_numbers(INVENTORY / "endpoint_union.tsv")
    census_lines = row_line_numbers(
        INVENTORY / "review_census_835.tsv", "row_id"
    )
    census_by_id = {
        row["row_id"]: row
        for row in common.read_tsv(INVENTORY / "review_census_835.tsv")
    }

    if common.resolve_endpoint(STALE_LIPSCHITZ, source_index) is not None:
        raise ValueError(
            "the known stale HDP.Chapter5.LipschitzWith name unexpectedly resolved"
        )
    global_lipschitz = (
        ".lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean",
        58,
        "def",
    )
    validate_declaration_line("LipschitzWith", global_lipschitz)
    lipschitz_census = census_by_id["census-e77ea5243e1dd79c"]
    if (
        "HDP.Chapter5.LipschitzWith"
        not in json.loads(lipschitz_census["direct_endpoint_names"])
        or "namespace_inherited"
        not in json.loads(lipschitz_census["direct_endpoint_resolution_modes"])
        or "HDP.Chapter5.LipschitzWith"
        in json.loads(lipschitz_census["readme_exact_endpoint_names"])
    ):
        raise ValueError("the documented Lipschitz namespace mismatch changed")

    for endpoint, expected in EXPECTED_SOURCE_LOCATIONS.items():
        actual = common.resolve_endpoint(endpoint, source_index)
        if actual != expected:
            raise ValueError(
                f"{endpoint}: resolution drift; expected {expected}, got {actual}"
            )
        validate_declaration_line(endpoint, expected)

    for endpoint, (candidate, path, line) in CITATIONS.items():
        candidate_resolution = common.resolve_endpoint(candidate, source_index)
        expected = (path, line)
        if (
            candidate_resolution is None
            or candidate_resolution[:2] != expected
        ):
            raise ValueError(
                f"{endpoint}: citation resolution drift for {candidate}; "
                f"expected {expected}, got {candidate_resolution}"
            )
        validate_declaration_line(candidate, candidate_resolution)
        if not common.dependency_reaches(
            dependency_edges,
            candidate.split(".")[-1],
            endpoint.split(".")[-1],
        ):
            raise ValueError(
                f"{endpoint}: no static dependency path from {candidate}"
            )

    output_rows: list[dict[str, str]] = []
    for inventory_row in selected:
        endpoint = inventory_row["endpoint"]
        chapters = json.loads(inventory_row["chapters"])
        if len(chapters) != 1:
            raise ValueError(f"{endpoint}: expected one chapter, got {chapters}")
        chapter = str(chapters[0])
        book_labels = [str(value) for value in json.loads(inventory_row["book_refs"])]
        source_row_ids = [
            str(value) for value in json.loads(inventory_row["source_row_ids"])
        ]
        judgment = EVIDENCE[endpoint]

        if endpoint == STALE_LIPSCHITZ:
            resolved_declarations = "LipschitzWith"
            locations = v9_extra_locations(
                endpoint, union_lines, census_lines
            )
        else:
            source_path, source_line, _kind = EXPECTED_SOURCE_LOCATIONS[endpoint]
            resolved_declarations = endpoint
            locations = [f"{source_path}:{source_line}"]
            locations.extend(
                v9_extra_locations(endpoint, union_lines, census_lines)
            )

        citation = CITATIONS.get(endpoint)
        if citation is None:
            citation_name = ""
            d_text = (
                "Pass-07 replacement: global LipschitzWith is used by "
                "HDP.Chapter5.lipschitzSeminorm_le_iff at "
                "HighDimensionalProbability/"
                "Chapter5_ConcentrationWithoutIndependence.lean:104"
                if endpoint == STALE_LIPSCHITZ
                else "no static reverse-citation candidate recorded"
            )
        else:
            citation_name, citation_path, citation_line = citation
            d_text = f"{citation_name} @ {citation_path}:{citation_line}"

        justification = (
            f"H({judgment['h'].split(': ', 1)[-1]}) "
            f"C({judgment['c'].split(': ', 1)[-1]}) "
            f"T({judgment['t'].split(': ', 1)[-1]}) "
            f"Q({judgment['q'].split(': ', 1)[-1]}) "
            f"D({d_text}) "
            f"S({'; '.join(locations)})"
        )
        output_rows.append(
            {
                "row_set": "endpoint_union",
                "sample_kind": "supplemental_review_census_direct",
                "row_id": common.stable_row_id(endpoint),
                "source_row_ids": "; ".join(source_row_ids),
                "chapter": chapter,
                "book_label": "; ".join(book_labels),
                "inventory_endpoint": endpoint,
                "resolved_declarations": resolved_declarations,
                "verdict": judgment["verdict"],
                "joint_satisfiability": judgment["h"],
                "nontrivial_conclusion": judgment["c"],
                "typeclass_nondegeneracy": judgment["t"],
                "quantifier_usability": judgment["q"],
                "justification": justification,
                "witness_by_citation_candidate": citation_name,
                "source_locations": "; ".join(locations),
                "tier_c_required": "no",
                "v9_crossfile": judgment["v9"],
                "resolution_note": judgment["note"],
            }
        )
    return output_rows, raw, main_endpoints


def validate_line_locations(row: dict[str, str]) -> None:
    for location in row["source_locations"].split("; "):
        path_text, line_text = location.rsplit(":", 1)
        path = PROJECT / path_text
        if not path.is_file():
            raise ValueError(f"{row['row_id']}: missing evidence path {path_text}")
        line = int(line_text)
        line_count = len(path.read_text(encoding="utf-8").splitlines())
        if not 1 <= line <= line_count:
            raise ValueError(
                f"{row['row_id']}: evidence line out of range: {location}"
            )


def validate_rows(
    rows: list[dict[str, str]],
    raw: list[dict[str, str]],
    main_endpoints: set[str],
) -> None:
    if len(rows) != 14 or len({row["row_id"] for row in rows}) != 14:
        raise ValueError("supplement must contain exactly 14 unique row IDs")
    if any(tuple(row) != FIELDS for row in rows):
        raise ValueError("a row does not use the coordinated supplemental schema")
    if {row["inventory_endpoint"] for row in rows} != set(EVIDENCE):
        raise ValueError("output is not the exact hand-reviewed endpoint set")
    if {row["inventory_endpoint"] for row in rows} & main_endpoints:
        raise ValueError("supplement overlaps an endpoint in the main Ch5--7 ledger")
    raw_endpoints = {row["endpoint"] for row in raw}
    if (
        {row["inventory_endpoint"] for row in rows}
        | EXPECTED_MAIN_OVERLAP
    ) != raw_endpoints:
        raise ValueError("selected plus excluded endpoints do not reconstruct raw set")

    expected_chapters = Counter(
        {"Chapter 5": 12, "Chapter 6": 0, "Chapter 7": 2}
    )
    actual_chapters = Counter(row["chapter"] for row in rows)
    for chapter in CHAPTER_ORDER:
        if actual_chapters[chapter] != expected_chapters[chapter]:
            raise ValueError(
                f"chapter count drift for {chapter}: {actual_chapters[chapter]}"
            )
    if Counter(row["verdict"] for row in rows) != Counter({"OK": 14}):
        raise ValueError("expected current verdicts OK=14")

    v9 = {
        row["inventory_endpoint"]: row["v9_crossfile"]
        for row in rows
        if row["v9_crossfile"]
    }
    expected_v9 = {}
    if v9 != expected_v9:
        raise ValueError(f"V9 cross-file flags drifted: {v9}")

    citation_count = 0
    for row in rows:
        if row["row_set"] != "endpoint_union":
            raise ValueError(f"{row['row_id']}: wrong row_set")
        if row["sample_kind"] != "supplemental_review_census_direct":
            raise ValueError(f"{row['row_id']}: wrong sample_kind")
        if row["tier_c_required"] != "no":
            raise ValueError(f"{row['row_id']}: supplemental row selected for Tier C")
        if not row["source_row_ids"] or not row["book_label"]:
            raise ValueError(f"{row['row_id']}: incomplete inventory provenance")
        if not row["source_locations"]:
            raise ValueError(f"{row['row_id']}: missing source/evidence location")
        if not all(
            token in row["justification"]
            for token in ("H(", "C(", "T(", "Q(", "D(", "S(")
        ):
            raise ValueError(f"{row['row_id']}: incomplete H/C/T/Q/D/S")
        expected_prefix = (
            "SUSPECT: "
            if row["verdict"] == "SUSPECT"
            else "OK: "
        )
        for field in (
            "joint_satisfiability",
            "nontrivial_conclusion",
            "typeclass_nondegeneracy",
            "quantifier_usability",
        ):
            if not row[field].startswith(expected_prefix):
                raise ValueError(
                    f"{row['row_id']}: {field} lacks {expected_prefix!r}"
                )
        if row["witness_by_citation_candidate"]:
            citation_count += 1
            candidate, path, line = CITATIONS[row["inventory_endpoint"]]
            if row["witness_by_citation_candidate"] != candidate:
                raise ValueError(f"{row['row_id']}: citation name drift")
            if f"D({candidate} @ {path}:{line})" not in row["justification"]:
                raise ValueError(f"{row['row_id']}: citation path missing from D")
        validate_line_locations(row)

    if citation_count != 5:
        raise ValueError(f"expected 5 dependency citations, got {citation_count}")
    if sum(bool(row["resolved_declarations"]) for row in rows) != 14:
        raise ValueError("expected exactly 14 current declaration resolutions")


def render_tsv(rows: list[dict[str, str]]) -> str:
    handle = io.StringIO(newline="")
    writer = csv.DictWriter(
        handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(rows)
    return handle.getvalue()


def render_summary(rows: list[dict[str, str]]) -> str:
    chapters = Counter(row["chapter"] for row in rows)
    verdicts = Counter(row["verdict"] for row in rows)
    citations = [
        row for row in rows if row["witness_by_citation_candidate"]
    ]
    v9_rows = [row for row in rows if row["v9_crossfile"]]
    lines = [
        "V6 Tier-B supplemental census coverage: Chapters 5--7",
        f"output: {OUTPUT.relative_to(PROJECT).as_posix()}",
        f"builder: {Path(__file__).resolve().relative_to(PROJECT).as_posix()}",
        "check_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_b_supplement_ch5_7.py --check",
        "rebuild_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_b_supplement_ch5_7.py --write",
        "method: static current-source close reading only; no Lean/lake invocation",
        "inventory_source: HighDimensionalProbability/Verification/inventory/"
        "endpoint_union.tsv (the project endpoint inventory)",
        "selection: source_kinds exactly [\"review_census_direct\"], chapter in "
        "Chapter 5--7, minus every resolved_declarations endpoint in the main "
        "Ch5--7 ledger",
        "raw_exact_review_census_direct_rows: 17",
        "excluded_main_ledger_overlap_rows: 3",
        f"exact_selected_endpoint_rows: {len(rows)}",
        f"exact_unique_inventory_endpoints: "
        f"{len({row['inventory_endpoint'] for row in rows})}",
        "chapter_counts: "
        + ", ".join(
            f"{chapter}={chapters[chapter]}" for chapter in CHAPTER_ORDER
        ),
        "verdict_counts: "
        + ", ".join(
            f"{verdict}={verdicts.get(verdict, 0)}"
            for verdict in ("OK", "SUSPECT", "VACUOUS")
        ),
        "exact_source_declarations_resolved: "
        f"{sum(bool(row['resolved_declarations']) for row in rows)}",
        f"rows_with_complete_H_C_T_Q_D_S: {len(rows)}/{len(rows)}",
        f"rows_with_static_reverse_citation_candidate: {len(citations)}",
        f"static_reverse_citation_dependency_paths_validated: {len(citations)}",
        f"v9_crossfile_rows: {len(v9_rows)}",
        "",
        "[excluded_as_already_in_main_ledger]",
    ]
    lines.extend(sorted(EXPECTED_MAIN_OVERLAP))
    lines.extend(
        [
            "",
            "[pass07_historical_endpoint_replacement]",
            f"{STALE_LIPSCHITZ}\tOK\tPASS07_REPLACED_HISTORICAL_KEY",
            "actual_symbol: global LipschitzWith at "
            ".lake/packages/mathlib/Mathlib/Topology/EMetricSpace/"
            "Lipschitz.lean:58",
            "disposition: explicit historical-to-current replacement overlay; "
            "no project declaration under the old qualified name",
            "",
            "[v9_crossfile]",
        ]
    )
    lines.extend(
        f"{row['inventory_endpoint']}\t{row['v9_crossfile']}\t"
        f"{row['resolution_note']}"
        for row in v9_rows
    )
    lines.extend(["", "[validated_dependency_paths]"])
    for row in citations:
        candidate, path, line = CITATIONS[row["inventory_endpoint"]]
        lines.append(
            f"{candidate} -> {row['inventory_endpoint']}\t{path}:{line}"
        )
    return "\n".join(lines) + "\n"


def require_exact(path: Path, expected: str) -> None:
    if not path.is_file():
        raise ValueError(f"missing artifact: {path.relative_to(PROJECT)}")
    if path.read_text(encoding="utf-8") != expected:
        raise ValueError(
            f"artifact drift: {path.relative_to(PROJECT)}; "
            "run this builder with --write"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="read-only exact check")
    mode.add_argument("--write", action="store_true", help="regenerate and check")
    mode.add_argument("--print-tsv", action="store_true", help="print generated TSV")
    mode.add_argument(
        "--print-summary", action="store_true", help="print generated summary"
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    common.require_round10_source_identity()
    rows, raw, main_endpoints = build_rows()
    validate_rows(rows, raw, main_endpoints)
    tsv_text = render_tsv(rows)
    summary_text = render_summary(rows)

    if args.print_tsv:
        print(tsv_text, end="")
        return 0
    if args.print_summary:
        print(summary_text, end="")
        return 0
    if args.write:
        REVIEW.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(tsv_text, encoding="utf-8")
        SUMMARY.write_text(summary_text, encoding="utf-8")

    require_exact(OUTPUT, tsv_text)
    require_exact(SUMMARY, summary_text)
    print(
        "OK: static V6 Tier-B supplement Chapters 5--7; "
        "14 rows; resolved=14; suspect=0; V9=0; citations=5"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
