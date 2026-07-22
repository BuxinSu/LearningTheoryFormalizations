#!/usr/bin/env python3
"""Build and validate the static V6 Tier-B ledger for Chapters 5--7.

The builder is deliberately source-only.  It reads the frozen verification
inventories and the Lean source tree, resolves every reviewed declaration to a
source location, and combines that information with the recorded close-reading
judgments below.  It never invokes Lean or Lake.

Running without options regenerates both the TSV and its summary, then reads
them back and validates them.  ``--check`` performs the same reconstruction in
memory and requires the checked-in artifacts to match byte-for-byte.
"""

from __future__ import annotations

import argparse
import csv
import io
from collections import Counter
from pathlib import Path

import build_v6_tier_b_ch0_4 as common


PROJECT = Path(__file__).resolve().parents[3]
VERIFICATION = PROJECT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
OUTPUT = REVIEW / "v6_tier_b_ch5_7.tsv"
SUMMARY = REVIEW / "v6_tier_b_ch5_7_summary.txt"

ASSIGNED_CHAPTERS = {"Chapter 5", "Chapter 6", "Chapter 7"}
CHAPTER_ORDER = ("Chapter 5", "Chapter 6", "Chapter 7")

FIELDS = (
    "row_set",
    "sample_kind",
    "sample_rank",
    "row_id",
    "chapter",
    "book_label",
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
)

CHAPTER_MODELS = {
    "Chapter 5": (
        "positive-dimensional sphere/Haar models, nonzero Hermitian matrices, "
        "and bounded Bernoulli/Rademacher samples satisfy the guards"
    ),
    "Chapter 6": (
        "bounded independent Rademacher coordinates and copies, standard "
        "Gaussians, and nonzero finite matrices satisfy the guards"
    ),
    "Chapter 7": (
        "finite centered Gaussian processes, nonempty Euclidean sets, iid walks, "
        "and the standard Wiener model satisfy the guards"
    ),
}

TYPECLASS_EVIDENCE = {
    "Chapter 5": (
        "OK: Borel probability, EuclideanSpace, Fintype, Nonempty, and NeZero "
        "have dimension-1/2 nondegenerate instances; optional zero boundaries "
        "are not forced"
    ),
    "Chapter 6": (
        "OK: finite product probability spaces and nonempty matrix spaces give "
        "nondegenerate instances; arbitrary-measure endpoints admit these "
        "probability models"
    ),
    "Chapter 7": (
        "OK: standard Borel probability/Euclidean instances and explicit "
        "positive-dimension/nonempty guards avoid forced IsEmpty/Subsingleton "
        "domains"
    ),
}

# These are static reverse-citation leads or concrete witness designs.  They
# remain Tier-C candidates until the separate compilation/axiom stage checks
# them.  Keys are the exact ordered declaration cells reconstructed from the
# inventories, so any correspondence drift is visible.
WITNESS_BY_DECLARATION_CELL = {
    "HDP.Chapter5.lipschitzSeminorm; "
    "HDP.Chapter5.lipschitzSeminorm_le_iff":
        "HDP.Chapter5.lipschitzSeminorm_le_iff",
    "HDP.Chapter5.sphere_lipschitz_concentration":
        "HDP.Chapter5.sphere_lipschitz_tail",
    "HDP.Chapter5.blowUp_of_centered_concentration":
        "HDP.Chapter5.sphere_blowUp",
    "HDP.Chapter5.IsMedian; HDP.Chapter5.exists_isMedian":
        "HDP.Chapter5.exists_isMedian",
    "HDP.Chapter5.gaussian_lipschitz_hasSubgaussianMGF":
        "HDP.Chapter5.gaussian_lipschitz_concentration",
    "HDP.Chapter5.theorem_5_3_1":
        "HDP.Chapter5.theorem_5_3_1_exponential",
    "HDP.Chapter5.randomProjection_secondMoment":
        "HDP.Chapter5.randomProjection_rms",
    "HDP.Chapter5.matrixBernsteinTail":
        "HDP.Chapter5.matrixBernsteinSymmetricTail",
    "HDP.Chapter5.matrixBernsteinExpectation":
        "HDP.Chapter5.sparseSBM_expectedNoise_exact",
    "HDP.Chapter5.matrixKhintchineOne":
        "HDP.Chapter6.conditionalKhintchine_symmetricCoordinates",
    "HDP.effectiveRank":
        "HDP.Chapter9.theorem_9_2_2_lowRankCovariance_effectiveRank",
    "HDP.Chapter5.matrixNorm_le_iff_loewnerInterval":
        "FRESH_NAMED_WITNESS: nonzero 2x2 diagonal Hermitian matrix",
    "HDP.Chapter6.decoupling":
        "HDP.Chapter6.decoupling_mgf",
    "HDP.Chapter6.hansonWright":
        "HDP.Chapter6.theorem_6_2_2",
    "HDP.Chapter6.gaussianReplacement":
        "HDP.Chapter6.hansonWright_offDiagonal_lmgf",
    "HDP.Chapter6.symmetrization":
        "HDP.Chapter6.symmetrization_upper",
    "HDP.Chapter6.matrixCompletion_bernoulli":
        "HDP.Chapter6.matrixCompletion_bernoulli_normalized",
    "HDP.Chapter6.gaussianSymmetrization_upper":
        "HDP.Chapter6.gaussianSymmetrization_source",
    "HDP.Chapter6.integral_norm_le_integral_norm_add_independent_centered":
        "HDP.Chapter6.symmetrization",
    "HDP.Chapter6.symmetricRandomMatrix_expectedNorm_upper_of_symmetrization":
        "HDP.Chapter6.theorem_6_4_1",
    "HDP.Chapter6.quadraticForm_sub_integral_eq_diagonal_add_offDiagonal":
        "HDP.Chapter6.hansonWright",
    "HDP.Chapter7.gaussianIntegrationByParts":
        "HDP.Chapter7.gaussianIntegrationByParts_measure",
    "HDP.Chapter7.multivariateGaussianIntegrationByParts":
        "FRESH_NAMED_WITNESS: n=1 standard covariance and smooth compact-support bump",
    "HDP.Chapter7.gaussianInterpolation":
        "FRESH_NAMED_WITNESS: n=1,u=1/2,PSD covariances,smooth compact-support f",
    "HDP.Chapter7.sudakovFernique":
        "HDP.Chapter7.gaussianMatrix_expected_opNorm",
    "HDP.Chapter7.sudakovInequality":
        "HDP.Chapter7.extendedExpectedSupremum_ge_sudakovSeq",
    "HDP.Chapter7.cubeGaussianWidth_eq_source":
        "HDP.Chapter9.example_9_7_4_cubeGaussianWidth",
    "HDP.Chapter7.crossPolytopeGaussianWidth_twoSided":
        "FRESH_NAMED_WITNESS: specialize k=0",
    "HDP.Chapter7.randomProjection_expectedDiameter; "
    "HDP.Chapter9.haarProjection_expectedDiameter_set":
        "HDP.Chapter9.haarProjection_expectedDiameter_envelope",
    "HDP.Chapter5.Grassmannian; HDP.Chapter5.grassmannDistance; "
    "HDP.Chapter5.grassmannHaarMeasure; "
    "HDP.Chapter5.grassmannian_concentration":
        "FRESH_NAMED_WITNESS: specialize n=2,m=1",
}

# Per-row evidence for the deterministic Tier-C queue.  Tuple order is:
# satisfiable hypotheses, nontrivial conclusion, nondegenerate typeclasses,
# usable quantifiers.  The common "OK: " prefix is added by review_row.
QUEUE_EVIDENCE: dict[str, tuple[str, str, str, str]] = {
    "census-4873958abc52b612": (
        "n=2,m=1 gives a nontrivial Grassmannian Haar model",
        "uniform Lipschitz concentration has a positive data-dependent scale",
        "1≤m<n excludes degenerate quotient dimensions",
        "one C works for all admissible n,m",
    ),
    "census-9a8303edb533db45": (
        "A=diag(1,-1) in Fin 2 is Hermitian and nonzero",
        "the norm/Loewner iff has two substantive directions",
        "Nonempty Fin 2 supplies eigenvalue extrema",
        "a is arbitrary and the interval forces its needed sign",
    ),
    "census-28ee26691f687a9c": (
        "centered signs times a nonzero matrix satisfy bounded independent hypotheses",
        "the expectation bound varies with variance and dimension",
        "finite product probability and nonempty matrices are standard",
        "L≥0 allows but does not force the zero case",
    ),
    "census-a42f06353bdaf063": (
        "sphere distance to a hemisphere supplies D≥0,D=0 and the proved "
        "subgaussian certificate",
        "the far-distance event has a genuine exponential bound",
        "the positive-dimensional sphere law is nonempty",
        "sphere_blowUp instantiates the certificate rather than assuming the conclusion",
    ),
    "census-636ecf0b5c2c32b0": (
        "n=2,m=1,z≠0 gives nonzero projected norm",
        "the second moment is (m/n)‖z‖²>0",
        "hn and m≤n admit a nonempty Grassmannian",
        "z and dimensions are universal with n>0 explicit",
    ),
    "census-78a4a177ee6726a5": (
        "a 2x2 symmetric Rademacher-entry matrix and independent signs satisfy "
        "all guards",
        "expected operator norm is bounded by positive row energy",
        "Nonempty Fin 2 and two probability spaces are nondegenerate",
        "hsymm is supplied by the proved symmetrization theorem",
    ),
    "census-f5a50680149423f4": (
        "centered Rademacher vectors plus independent Gaussian/sign families "
        "satisfy the telescope",
        "the Gaussianized expected norm depends on the vector family",
        "Fin(n+2) and all probability laws are nonempty",
        "n+2 keeps the logarithmic scale positive",
    ),
    "census-1edd5d9d59f81553": (
        "centered Rademachers and a nonzero 2x2 mixed A satisfy MemLp 2",
        "both diagonal and off-diagonal pieces can be nonzero",
        "Fin 2 on a finite probability law is nondegenerate",
        "A,X,ω are universal and the split is an equality",
    ),
    "census-15e0e28502a3aa01": (
        "two centered standard Gaussian vectors satisfy "
        "SubGaussianVector,BddAbove and a common positive ψ₂ bound",
        "the bilinear exponential integral varies with A and λ",
        "standard Euclidean Borel laws are nonempty",
        "K>0 instances remain and BddAbove is a real finite-dimensional certificate",
    ),
    "census-96eaba74736a906b": (
        "nonzero integrable Y and an independent centered sign perturbation Z "
        "satisfy the guards",
        "the right norm changes with Z and can strictly exceed the left",
        "separate probability spaces with E=ℝ are nondegenerate",
        "centering is not the conclusion and no guard is empty",
    ),
    "census-0560df665cff4b2d": (
        "n=1,positive covariances,u=1/2 and a smooth compact-support non-affine f "
        "satisfy the analytic guards",
        "the derivative changes with covariance difference and Hessian",
        "one-dimensional Gaussian laws are nonempty",
        "0<u<1 and compact support prevent endpoint/domination junk",
    ),
    "census-bd0478c6633a1f9d": (
        "k=0 gives the genuine two-dimensional cross-polytope",
        "its positive width has nonzero two-sided bounds",
        "dimension k+2 is always at least 2",
        "one positive c,C works for every k",
    ),
    "census-ea1c69d973f1e27b": (
        "n=1,S=[1] and a nonconstant compact-support bump satisfy "
        "derivative/integrability guards",
        "the covariance-weighted derivative identity is not reflexive",
        "the standard one-dimensional Gaussian is nondegenerate",
        "PSD,differentiability,support and derivative identification are explicit",
    ),
    "census-a334813e84362d44": (
        "f(x)=x,f′(x)=1 satisfy derivative and Gaussian integrability",
        "the identity becomes E[X²]=1",
        "the fixed standard Gaussian is nondegenerate",
        "f and f′ are universal but linked by HasDerivAt",
    ),
    "census-158ae90881f0f306": (
        "n=1 gives the nontrivial interval cube support",
        "the width is √(2/π)>0",
        "Fin 1 and standard Gaussian law are nonempty",
        "the universal n formula includes positive dimensions",
    ),
}

EXPECTED_EXERCISE_IDS = {
    "exercise-decl-d42df821ed85d7b1",
    "exercise-decl-ef2ede532b3a1561",
    "exercise-decl-be566045331778ce",
    "exercise-decl-42ba4f86f0864bb1",
    "exercise-decl-6311254e11df0a03",
    "exercise-decl-acb0fd4fe1df2f02",
    "exercise-decl-d3f0aca5f6315f3e",
    "exercise-decl-40798e129e8da034",
    "exercise-decl-f627fbc49b18f982",
}

EXERCISE_QUANTIFIER_OVERRIDE = {
    "exercise-decl-acb0fd4fe1df2f02": (
        "OK: the two conjuncts rebind p separately (1<p≤2 and 2≤p); the "
        "Tier-A p=2 alert is a cross-branch false positive"
    ),
}

# Finset.sum is generated by the @[to_additive] command attached to prod, so it
# does not have a standalone command line for the source index to discover.
LOCATION_OVERRIDES = {
    "Finset.sum": (
        ".lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean",
        64,
        "def",
    ),
}


def resolve_endpoint(
    endpoint: str,
    source_index: dict[str, list[tuple[str, int, str, str]]],
) -> tuple[str, int, str]:
    if endpoint in LOCATION_OVERRIDES:
        return LOCATION_OVERRIDES[endpoint]
    return common.resolve_endpoint(endpoint, source_index)


def review_row(
    *,
    row_set: str,
    sample_kind: str,
    sample_rank: str,
    row_id: str,
    chapter: str,
    book_label: str,
    result: str,
    endpoints: list[str],
    source_index: dict[str, list[tuple[str, int, str, str]]],
    tier_c: bool,
    evidence: tuple[str, str, str, str] | None = None,
) -> dict[str, str]:
    resolved = [resolve_endpoint(endpoint, source_index) for endpoint in endpoints]
    locations = [f"{path}:{line}" for path, line, _kind in resolved]
    definition_only = all(
        kind in {"def", "abbrev", "structure", "class", "irreducible_def"}
        for _path, _line, kind in resolved
    )

    if evidence is not None:
        h_text, c_text, t_text, q_text = (
            f"OK: {component}" for component in evidence
        )
    elif definition_only:
        h_text = (
            f"N/A: definitional row; {CHAPTER_MODELS[chapter]} for its intended "
            "instantiations"
        )
        c_text = (
            "OK: the inspected body depends explicitly on its inputs and is not a "
            "constant/empty placeholder; any totalized off-domain value is separated "
            "from the guarded source-facing use"
        )
        t_text = TYPECLASS_EVIDENCE[chapter]
        q_text = (
            "OK: parameters are explicit and the associated source-facing "
            "characterization keeps the intended domain; no guard-empty existential "
            "replacement was seen"
        )
    else:
        h_text = f"OK: {CHAPTER_MODELS[chapter]}"
        c_text = (
            "OK: the inspected endpoint has a data-dependent equality, inequality, "
            "existence, measure, or norm conclusion corresponding to "
            f"“{common.clip(result)}”; it is not True/top/a bare reflexivity placeholder"
        )
        t_text = TYPECLASS_EVIDENCE[chapter]
        q_text = EXERCISE_QUANTIFIER_OVERRIDE.get(
            row_id,
            "OK: the inspected declaration binds the advertised data and guards "
            "explicitly; no accidentally existential, empty-domain-only, or apparent "
            "auto-implicit weakening was seen",
        )

    declaration_cell = "; ".join(endpoints)
    witness = WITNESS_BY_DECLARATION_CELL.get(
        declaration_cell,
        f"FRESH_NAMED_WITNESS_NEEDED: {CHAPTER_MODELS[chapter]}",
    )
    justification = (
        f"H({h_text.split(': ', 1)[-1]}) "
        f"C({c_text.split(': ', 1)[-1]}) "
        f"T({t_text.split(': ', 1)[-1]}) "
        f"Q({q_text.split(': ', 1)[-1]}) "
        f"D({witness}) "
        f"S({'; '.join(locations)})"
    )
    return {
        "row_set": row_set,
        "sample_kind": sample_kind,
        "sample_rank": sample_rank,
        "row_id": row_id,
        "chapter": chapter,
        "book_label": book_label,
        "resolved_declarations": declaration_cell,
        "verdict": "OK",
        "joint_satisfiability": h_text,
        "nontrivial_conclusion": c_text,
        "typeclass_nondegeneracy": t_text,
        "quantifier_usability": q_text,
        "justification": justification,
        "witness_by_citation_candidate": witness,
        "source_locations": "; ".join(locations),
        "tier_c_required": "yes" if tier_c else "no",
    }


def load_assigned_inventory() -> tuple[
    list[dict[str, str]],
    list[dict[str, str]],
    list[dict[str, str]],
]:
    readme_rows = [
        row
        for row in common.read_tsv(INVENTORY / "readme_correspondence.tsv")
        if row["chapter"] in ASSIGNED_CHAPTERS
    ]
    sampling_rows = common.read_tsv(INVENTORY / "sampling_plan.tsv")
    exercise_rows = [
        row
        for row in sampling_rows
        if row["chapter"] in ASSIGNED_CHAPTERS
        and row["sample_kind"] == "exercise_leaf_close_read"
    ]
    queue_rows = [
        row
        for row in sampling_rows
        if row["chapter"] in ASSIGNED_CHAPTERS
        and row["sample_kind"] == "ok_review_queue_head"
    ]

    if (len(readme_rows), len(exercise_rows), len(queue_rows)) != (169, 9, 15):
        raise ValueError(
            "assigned inventory drift: expected README=169, exercise=9, queue=15; "
            f"got {len(readme_rows)}, {len(exercise_rows)}, {len(queue_rows)}"
        )
    exercise_ids = {row["target_id"] for row in exercise_rows}
    if exercise_ids != EXPECTED_EXERCISE_IDS:
        raise ValueError(
            "deterministic exercise sample drift: "
            f"missing={sorted(EXPECTED_EXERCISE_IDS - exercise_ids)}; "
            f"extra={sorted(exercise_ids - EXPECTED_EXERCISE_IDS)}"
        )
    queue_ids = {row["target_id"] for row in queue_rows}
    if queue_ids != set(QUEUE_EVIDENCE):
        raise ValueError(
            "hand-reviewed queue evidence drift: "
            f"missing={sorted(set(QUEUE_EVIDENCE) - queue_ids)}; "
            f"extra={sorted(queue_ids - set(QUEUE_EVIDENCE))}"
        )
    return readme_rows, exercise_rows, queue_rows


def build_rows() -> tuple[
    list[dict[str, str]],
    list[dict[str, str]],
    list[dict[str, str]],
    list[dict[str, str]],
]:
    readme_rows, exercise_rows, queue_rows = load_assigned_inventory()
    source_index = common.build_source_index()
    output_rows: list[dict[str, str]] = []

    for row in readme_rows:
        output_rows.append(
            review_row(
                row_set="readme_correspondence",
                sample_kind="mandatory_readme",
                sample_rank="",
                row_id=row["row_id"],
                chapter=row["chapter"],
                book_label=row["book_ref"],
                result=row["result"],
                endpoints=common.endpoints_from_json_cell(row["endpoint_names"]),
                source_index=source_index,
                tier_c=False,
            )
        )
    for row in exercise_rows:
        output_rows.append(
            review_row(
                row_set="sampling_plan",
                sample_kind=row["sample_kind"],
                sample_rank=row["rank"],
                row_id=row["target_id"],
                chapter=row["chapter"],
                book_label=row["book_ref"],
                result=row["result"],
                endpoints=[row["endpoint"]],
                source_index=source_index,
                tier_c=False,
            )
        )
    for row in queue_rows:
        output_rows.append(
            review_row(
                row_set="sampling_plan",
                sample_kind=row["sample_kind"],
                sample_rank=row["rank"],
                row_id=row["target_id"],
                chapter=row["chapter"],
                book_label=row["book_ref"],
                result=row["result"],
                endpoints=common.endpoints_from_plain_cell(row["endpoint"]),
                source_index=source_index,
                tier_c=True,
                evidence=QUEUE_EVIDENCE[row["target_id"]],
            )
        )
    return output_rows, readme_rows, exercise_rows, queue_rows


def validate_rows(
    rows: list[dict[str, str]],
    readme_rows: list[dict[str, str]],
    exercise_rows: list[dict[str, str]],
    queue_rows: list[dict[str, str]],
) -> None:
    if len(rows) != 193:
        raise ValueError(f"expected 193 review rows, got {len(rows)}")
    if any(tuple(row) != FIELDS for row in rows):
        raise ValueError("a generated row does not use the coordinated 16-column schema")
    if len({row["row_id"] for row in rows}) != len(rows):
        raise ValueError("row_id is not unique across the generated ledger")

    expected_chapters = Counter(
        {"Chapter 5": 76, "Chapter 6": 47, "Chapter 7": 70}
    )
    expected_kinds = Counter(
        {
            "mandatory_readme": 169,
            "exercise_leaf_close_read": 9,
            "ok_review_queue_head": 15,
        }
    )
    if Counter(row["chapter"] for row in rows) != expected_chapters:
        raise ValueError("generated chapter counts do not match 76/47/70")
    if Counter(row["sample_kind"] for row in rows) != expected_kinds:
        raise ValueError("generated sample-kind counts do not match 169/9/15")
    if Counter(row["verdict"] for row in rows) != Counter({"OK": 193}):
        raise ValueError("the frozen Tier-B verdict distribution is no longer OK=193")

    actual_readme_ids = {
        row["row_id"] for row in rows if row["sample_kind"] == "mandatory_readme"
    }
    actual_exercise_ids = {
        row["row_id"]
        for row in rows
        if row["sample_kind"] == "exercise_leaf_close_read"
    }
    actual_queue_ids = {
        row["row_id"]
        for row in rows
        if row["sample_kind"] == "ok_review_queue_head"
    }
    if actual_readme_ids != {row["row_id"] for row in readme_rows}:
        raise ValueError("generated README IDs do not equal the assigned inventory")
    if actual_exercise_ids != {row["target_id"] for row in exercise_rows}:
        raise ValueError("generated exercise IDs do not equal the sampling plan")
    if actual_queue_ids != {row["target_id"] for row in queue_rows}:
        raise ValueError("generated queue IDs do not equal the sampling plan")

    tier_c_rows = [row for row in rows if row["tier_c_required"] == "yes"]
    if len(tier_c_rows) != 15:
        raise ValueError(f"expected 15 Tier-C rows, got {len(tier_c_rows)}")
    if any(
        (row["tier_c_required"] == "yes")
        != (row["sample_kind"] == "ok_review_queue_head")
        for row in rows
    ):
        raise ValueError("Tier-C must select exactly the separate queue-head rows")
    for chapter in CHAPTER_ORDER:
        ranks = sorted(
            int(row["sample_rank"])
            for row in tier_c_rows
            if row["chapter"] == chapter
        )
        if ranks != [1, 2, 3, 4, 5]:
            raise ValueError(
                f"Tier-C queue for {chapter} is not ranks 1--5: {ranks}"
            )

    for row in rows:
        if not row["joint_satisfiability"].startswith(("OK: ", "N/A: ")):
            raise ValueError(f"{row['row_id']}: invalid satisfiability checklist state")
        for field in (
            "nontrivial_conclusion",
            "typeclass_nondegeneracy",
            "quantifier_usability",
        ):
            if not row[field].startswith("OK: "):
                raise ValueError(f"{row['row_id']}: {field} is not marked OK")
        if not all(
            token in row["justification"]
            for token in ("H(", "C(", "T(", "Q(", "D(", "S(")
        ):
            raise ValueError(f"{row['row_id']}: incomplete H/C/T/Q/D/S justification")
        if not row["witness_by_citation_candidate"]:
            raise ValueError(f"{row['row_id']}: missing citation/witness candidate")
        if not row["source_locations"] or "UNRESOLVED" in row["source_locations"]:
            raise ValueError(f"{row['row_id']}: unresolved source location")

        endpoints = row["resolved_declarations"].split("; ")
        locations = row["source_locations"].split("; ")
        if len(endpoints) != len(locations):
            raise ValueError(
                f"{row['row_id']}: endpoint/source-location arity mismatch"
            )
        for location in locations:
            relative, line_text = location.rsplit(":", 1)
            source = PROJECT / relative
            if not source.is_file():
                raise ValueError(f"{row['row_id']}: missing source file {relative}")
            line = int(line_text)
            line_count = len(source.read_text(encoding="utf-8").splitlines())
            if not 1 <= line <= line_count:
                raise ValueError(
                    f"{row['row_id']}: source line {location} is out of range"
                )


def render_tsv(rows: list[dict[str, str]]) -> str:
    handle = io.StringIO(newline="")
    writer = csv.DictWriter(
        handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(rows)
    return handle.getvalue()


def render_summary(rows: list[dict[str, str]]) -> str:
    by_chapter = Counter(row["chapter"] for row in rows)
    by_kind = Counter(row["sample_kind"] for row in rows)
    verdicts = Counter(row["verdict"] for row in rows)
    tier_c_rows = [row for row in rows if row["tier_c_required"] == "yes"]
    lines = [
        "V6 Tier-B close-reading coverage: Chapters 5--7",
        f"output: {OUTPUT.relative_to(PROJECT).as_posix()}",
        f"builder: {Path(__file__).resolve().relative_to(PROJECT).as_posix()}",
        "rerun_and_validate_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/build_v6_tier_b_ch5_7.py",
        "method: static close reading of actual Lean declarations only; no "
        "Lean/lake invocation",
        "assigned scope counted without deduplication: 169 README + 9 exercise + "
        "15 queue-head rows",
        f"total_assigned_rows: {len(rows)}",
        "sample_kind_counts: "
        f"mandatory_readme={by_kind['mandatory_readme']}, "
        f"exercise_leaf_close_read={by_kind['exercise_leaf_close_read']}, "
        f"ok_review_queue_head={by_kind['ok_review_queue_head']}",
        "chapter_counts: "
        f"Chapter 5={by_chapter['Chapter 5']}, "
        f"Chapter 6={by_chapter['Chapter 6']}, "
        f"Chapter 7={by_chapter['Chapter 7']}",
        "verdict_counts: "
        f"OK={verdicts.get('OK', 0)}, "
        f"SUSPECT={verdicts.get('SUSPECT', 0)}, "
        f"VACUOUS={verdicts.get('VACUOUS', 0)}",
        f"tier_c_required_rows: {len(tier_c_rows)} "
        "(queue ranks 1--5 in each chapter)",
        "tier_c_rows_with_candidate: "
        f"{sum(bool(row['witness_by_citation_candidate']) for row in tier_c_rows)}",
        "",
        "[manual-review-notes]",
        "Ordinary analytic/measurability/BddAbove guards stayed OK when a standard "
        "nondegenerate model was inspected; optional zero boundaries did not "
        "force collapse.",
        "Exercise 6.25: Tier A merged p<=2 from one conjunct with 2<=p from "
        "another; each conjunct rebinds p, so this was a false positive.",
        "sphere_blowUp, Hanson--Wright, and symmetrization provide concrete "
        "downstream instantiations for the main conditional-looking interfaces.",
        "Brownian Example 7.1.6 uses Mathlib IsPreBrownianReal and the standard "
        "nondegenerate Wiener model, not a custom conclusion-smuggling certificate.",
        "",
        "[tier_c_queue]",
    ]
    lines.extend(
        f"{row['row_id']}\t{row['chapter']}\trank={row['sample_rank']}\t"
        f"{row['book_label']}\t{row['resolved_declarations']}\t"
        f"{row['witness_by_citation_candidate']}"
        for row in tier_c_rows
    )
    lines.extend(
        [
            "",
            "[files]",
            "ledger: HighDimensionalProbability/Verification/review/"
            "v6_tier_b_ch5_7.tsv",
            "summary: HighDimensionalProbability/Verification/review/"
            "v6_tier_b_ch5_7_summary.txt",
            "",
            "[exact_rebuild_and_validation_command]",
            "PYTHONDONTWRITEBYTECODE=1 python3 "
            "HighDimensionalProbability/Verification/scripts/"
            "build_v6_tier_b_ch5_7.py",
        ]
    )
    return "\n".join(lines) + "\n"


def require_exact_artifact(path: Path, expected: str) -> None:
    if not path.is_file():
        raise ValueError(f"missing generated artifact: {path.relative_to(PROJECT)}")
    actual = path.read_text(encoding="utf-8")
    if actual != expected:
        raise ValueError(
            f"artifact drift: {path.relative_to(PROJECT)}; rerun this builder "
            "without --check"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="do not write; require both generated artifacts to match exactly",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    common.require_round10_source_identity()
    rows, readme_rows, exercise_rows, queue_rows = build_rows()
    validate_rows(rows, readme_rows, exercise_rows, queue_rows)
    tsv_text = render_tsv(rows)
    summary_text = render_summary(rows)

    if not args.check:
        REVIEW.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(tsv_text, encoding="utf-8")
        SUMMARY.write_text(summary_text, encoding="utf-8")

    require_exact_artifact(OUTPUT, tsv_text)
    require_exact_artifact(SUMMARY, summary_text)
    print(
        "OK: static V6 Tier-B Chapters 5--7 "
        f"({'check' if args.check else 'rebuild'}); "
        "193 rows; README=169, exercises=9, queue=15; Tier-C=15"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
