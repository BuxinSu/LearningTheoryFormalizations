#!/usr/bin/env python3
"""Assemble V6 from the current validated Tier-A/B/C evidence ledgers."""

from __future__ import annotations

import csv
import json
import re
import sys
from collections import Counter
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
LOGS = VERIFICATION / "logs"
REPORT = VERIFICATION / "06_vacuity_triviality.md"
WITNESS_SOURCE = VERIFICATION / "scripts" / "witnesses" / "V6Witnesses.lean"

EXPECTED_CHAPTERS = {
    "1": 21,
    "2": 136,
    "3": 35,
    "4": 55,
    "5": 71,
    "6": 62,
    "7": 63,
    "8": 24,
}


def read_tsv(name: str) -> list[dict[str, str]]:
    with (LOGS / name).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def read_json(name: str) -> dict[str, object]:
    return json.loads((LOGS / name).read_text(encoding="utf-8"))


def md(text: str) -> str:
    return (
        text.replace("\\", "\\\\")
        .replace("|", "\\|")
        .replace("\r", " ")
        .replace("\n", " ")
    )


def short_names(text: str) -> str:
    if not text or text == "none":
        return text or "none"
    return "; ".join(
        item.rsplit(".", 1)[-1] for item in text.split(";") if item
    )


def metric(text: str, label: str) -> int:
    match = re.search(rf"(?m)^{re.escape(label)}\s+([0-9]+)\s*$", text)
    if match is None:
        raise ValueError(f"missing integer metric {label}")
    return int(match.group(1))


def text_metric(text: str, label: str) -> str:
    match = re.search(rf"(?m)^{re.escape(label)}\s+(\S+)\s*$", text)
    if match is None:
        raise ValueError(f"missing text metric {label}")
    return match.group(1)


def declaration_line(name: str) -> int:
    """Return the current source line for a named V6 witness declaration."""
    pattern = re.compile(
        rf"^\s*(?:private\s+)?(?:theorem|lemma|def)\s+{re.escape(name)}\b"
    )
    for line_no, line in enumerate(
        WITNESS_SOURCE.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if pattern.match(line):
            return line_no
    raise ValueError(f"missing V6 witness declaration {name}")


def chapter_summary(
    tier_b: list[dict[str, str]], verdicts: Counter[str]
) -> str:
    lines = [
        "| Chapter | Rows | OK | SUSPECT | VACUOUS |",
        "|---:|---:|---:|---:|---:|",
    ]
    for chapter in map(str, range(1, 9)):
        rows = [row for row in tier_b if row["chapter"] == chapter]
        counts = Counter(row["verdict"] for row in rows)
        lines.append(
            f"| {chapter} | {len(rows)} | {counts['OK']} | "
            f"{counts['SUSPECT']} | {counts['VACUOUS']} |"
        )
    lines.append(
        f"| **Total** | **{len(tier_b)}** | **{verdicts['OK']}** | "
        f"**{verdicts['SUSPECT']}** | **{verdicts['VACUOUS']}** |"
    )
    return "\n".join(lines)


def suspect_table(
    tier_b: list[dict[str, str]],
    coverage_by_global: dict[str, dict[str, str]],
) -> str:
    lines = [
        "| Row | Declaration | Boundary / totalization concern | "
        "Nondegenerate model | Compiled evidence | Disposition |",
        "|---|---|---|---|---|---|",
    ]
    suspects = [
        row for row in tier_b if row["verdict"] in {"SUSPECT", "VACUOUS"}
    ]
    for row in suspects:
        evidence = coverage_by_global[row["global_row"]]
        if row["declaration"] == "maxSummandSq":
            disposition = "**V6-F1 (INFO; REJECTED after containment review)**"
        elif row["declaration"] == "gChernoff":
            disposition = "**V6-F2 (INFO; REJECTED after boundary review)**"
        else:
            disposition = "V6-F3 review observation; not vacuous"
        lines.append(
            f"| C{int(row['chapter']):02d}-{int(row['chapter_row']):03d} "
            f"| `{md(row['declaration'])}` "
            f"| {md(row['check2_nontrivial'])} "
            f"| {md(row['check1_model'])} "
            f"| `{md(short_names(evidence['evidence_names']))}`; "
            f"{md(evidence['application_site'])} "
            f"| {disposition} |"
        )
    return "\n".join(lines)


def coverage_tables(coverage: list[dict[str, str]]) -> str:
    output: list[str] = []
    for chapter in map(str, range(1, 9)):
        rows = [row for row in coverage if row["chapter"] == chapter]
        rows.sort(
            key=lambda row: (
                row["obligation_kind"] != "sampled_OK",
                int(row["global_row"]),
            )
        )
        output.extend(
            [
                f"### Chapter {chapter}",
                "",
                "| Obligation / row | Declaration | Kind | Method and exact "
                "evidence | Endpoint dependency and axioms | Premise mapping | "
                "Status |",
                "|---|---|---|---|---|---|---|",
            ]
        )
        for row in rows:
            evidence = short_names(row["evidence_names"])
            mapping = (
                f"`{row['premise_discharge']}`; "
                f"{row['substantive_prop_premises']}; "
                f"{row['evidence_detail']}"
            )
            output.append(
                f"| {row['obligation_id']} / "
                f"C{int(chapter):02d}-{int(row['chapter_row']):03d} "
                f"| `{md(row['declaration'])}` "
                f"| {md(row['endpoint_kind'])} "
                f"| `{md(row['coverage_method'])}`; `{md(evidence)}` at "
                f"{md(row['application_site'])} "
                f"| {md(row['endpoint_dependencies'])}; "
                f"axioms: {md(row['evidence_axioms'])} "
                f"| {md(mapping)} "
                f"| **{row['status']}** |"
            )
        output.append("")
    return "\n".join(output)


def main() -> int:
    errors: list[str] = []
    required = [
        "v6_tier_b_review.tsv",
        "v6_tier_b_tables.md",
        "v6_tier_b_summary.json",
        "v6_tier_b_note_validation.json",
        "v6_tier_c_sample.tsv",
        "v6_tier_c_sampling.log",
        "v6_tier_c_coverage.tsv",
        "v6_tier_c_coverage_summary.json",
        "v6_tier_a_summary.json",
        "v6_tier_a_hits.tsv",
        "v6_autoimplicit_run.log",
        "v6_witness_acceptance.json",
        "v6_maxsummand_users.log",
    ]
    missing = [name for name in required if not (LOGS / name).is_file()]
    if missing:
        print(
            "\n".join(f"ERROR: missing logs/{name}" for name in missing),
            file=sys.stderr,
        )
        return 1

    tier_b = read_tsv("v6_tier_b_review.tsv")
    coverage = read_tsv("v6_tier_c_coverage.tsv")
    sample = read_tsv("v6_tier_c_sample.tsv")
    tier_a_hits = read_tsv("v6_tier_a_hits.tsv")
    tier_b_summary = read_json("v6_tier_b_summary.json")
    tier_b_validation = read_json("v6_tier_b_note_validation.json")
    tier_c_summary = read_json("v6_tier_c_coverage_summary.json")
    tier_a_summary = read_json("v6_tier_a_summary.json")
    witness_acceptance = read_json("v6_witness_acceptance.json")
    auto_text = (LOGS / "v6_autoimplicit_run.log").read_text(encoding="utf-8")
    maxsummand_text = (LOGS / "v6_maxsummand_users.log").read_text(
        encoding="utf-8"
    )
    sampling_text = (LOGS / "v6_tier_c_sampling.log").read_text(
        encoding="utf-8"
    )
    tier_b_tables = (LOGS / "v6_tier_b_tables.md").read_text(
        encoding="utf-8"
    ).rstrip()

    chapters = Counter(row["chapter"] for row in tier_b)
    verdicts = Counter(row["verdict"] for row in tier_b)
    kinds = Counter(row["endpoint_kind"] for row in tier_b)
    sample_kinds = Counter(row["endpoint_kind"] for row in sample)
    methods = Counter(row["coverage_method"] for row in coverage)
    try:
        sampling_seed = text_metric(sampling_text, "SEED")
        if not re.fullmatch(r"[0-9a-f]{64}", sampling_seed):
            errors.append("Tier-C sampling seed is not a SHA-256 digest")
    except ValueError as exc:
        errors.append(str(exc))
        sampling_seed = "MISSING"

    if len(tier_b) != sum(EXPECTED_CHAPTERS.values()):
        errors.append(f"Tier-B row drift: {len(tier_b)}")
    if chapters != Counter(EXPECTED_CHAPTERS):
        errors.append(f"Tier-B chapter drift: {dict(chapters)}")
    if verdicts != Counter({"OK": 433, "SUSPECT": 34, "VACUOUS": 0}):
        errors.append(f"Tier-B verdict-count drift: {dict(verdicts)}")
    if tier_b_summary.get("status") != "PASS":
        errors.append("Tier-B merge summary is not PASS")
    if tier_b_summary.get("checklist_complete") is not True:
        errors.append("Tier-B checklist is incomplete")
    if tier_b_validation.get("status") != "PASS":
        errors.append("independent Tier-B validation is not PASS")
    if sum(line.startswith("| C") for line in tier_b_tables.splitlines()) != len(
        tier_b
    ):
        errors.append("rendered Tier-B table row count differs from ledger")

    expected_obligations = (
        len(sample) + verdicts["SUSPECT"] + verdicts["VACUOUS"]
    )
    if len(sample) != 40 or Counter(row["chapter"] for row in sample) != Counter(
        {str(chapter): 5 for chapter in range(1, 9)}
    ):
        errors.append("Tier-C sample is not exactly five rows per chapter")
    for chapter in map(str, range(1, 9)):
        has_ok_def = any(
            row["chapter"] == chapter
            and row["verdict"] == "OK"
            and row["endpoint_kind"] == "definition"
            for row in tier_b
        )
        sampled_def = any(
            row["chapter"] == chapter
            and row["endpoint_kind"] == "definition"
            for row in sample
        )
        if has_ok_def and not sampled_def:
            errors.append(f"sample chapter {chapter} omits OK definitions")
    if len(coverage) != expected_obligations:
        errors.append(
            f"Tier-C obligation drift: {len(coverage)} != {expected_obligations}"
        )
    if any(row["status"] != "COVERED" for row in coverage):
        errors.append("Tier-C has uncovered obligations")
    if tier_c_summary.get("status") != "PASS":
        errors.append("Tier-C summary is not PASS")
    if tier_c_summary.get("total_obligations") != expected_obligations:
        errors.append("Tier-C summary total differs from dynamic obligation set")
    if tier_c_summary.get(
        "negative_unrelated_allowed_axiom_rejected"
    ) is not True:
        errors.append("unrelated allowed-axiom negative control was not rejected")
    if set(methods) - {"LIBRARY_CITATION", "NAMED_APPLICATION"}:
        errors.append(f"unexpected Tier-C methods: {dict(methods)}")

    if tier_a_summary.get("calibration_statements") != 3 or tier_a_summary.get(
        "calibration_statements_with_flags"
    ) != 3:
        errors.append("Tier-A positive calibration is not 3/3")
    if tier_a_summary.get("statements") != 1376:
        errors.append("Tier-A statement count drift")
    try:
        auto_metrics = {
            label: metric(auto_text, label)
            for label in (
                "CALIBRATION_EXPECTED_HITS",
                "CALIBRATION_ACTUAL_HITS",
                "CALIBRATION_ERRORS",
                "THEOREM_ENDPOINTS",
                "ALL_ENDPOINT_BINDER_ROWS",
                "CANDIDATE_BINDERS",
                "EXPLICITLY_ACCOUNTED",
                "SUSPECT_AUTO_BOUND",
            )
        }
        if (
            auto_metrics["CALIBRATION_EXPECTED_HITS"] != 2
            or auto_metrics["CALIBRATION_ACTUAL_HITS"] != 2
            or auto_metrics["CALIBRATION_ERRORS"] != 0
            or auto_metrics["CANDIDATE_BINDERS"]
            != auto_metrics["EXPLICITLY_ACCOUNTED"]
            or auto_metrics["SUSPECT_AUTO_BOUND"] != 0
            or "VERDICT PASS" not in auto_text
        ):
            errors.append("auto-bound audit/calibration is not PASS")
    except ValueError as exc:
        errors.append(str(exc))
        auto_metrics = Counter()

    if witness_acceptance.get("status") != "PASS":
        errors.append("witness acceptance is not PASS")
    if witness_acceptance.get("bad_witness_calibration") != "REJECTED":
        errors.append("sorry-based BadWitness calibration was not rejected")
    if "VERDICT PASS" not in maxsummand_text:
        errors.append("maxSummandSq containment audit is not PASS")

    if errors:
        print("\n".join(f"ERROR: {error}" for error in errors), file=sys.stderr)
        return 1

    coverage_by_global = {row["global_row"]: row for row in coverage}
    hit_names = ", ".join(
        f"`{row['name']}`" for row in tier_a_hits
    )
    other_suspects = [
        row["declaration"]
        for row in tier_b
        if row["verdict"] == "SUSPECT"
        and row["declaration"] not in {"maxSummandSq", "gChernoff"}
    ]
    sampled_definition_chapters = sorted(
        {
            int(row["chapter"])
            for row in sample
            if row["endpoint_kind"] == "definition"
        }
    )

    report = f"""# V6 — Vacuity and triviality audit

**Verdict: PASS-WITH-NOTES**

**Tier: mixed (machine Tier A/C and review Tier B)**

**Finding count: C=0 M=0 m=0 I=3**

## Guarantee

No correspondence-table endpoint was adjudicated VACUOUS, and no vacuous main theorem was
found in this post-correction re-certification of the snapshot pinned by
`logs/source_manifest.txt`. The correction pass rejected the two formerly MINOR boundary
findings as soundness defects, and the current rerun revalidated those dispositions:
`maxSummandSq` has only finite or finite-guarded handwritten users, and every audited
Chernoff caller either assumes `L > 0` or neutralizes `L = 0`. Their totalized out-of-domain
behavior remains visible as documented INFO observations.

This verdict follows the fixed severity mapping: INFO findings, with no CRITICAL, MAJOR, or
MINOR finding, mean PASS-WITH-NOTES.

V6 guarantees complete calibrated syntactic coverage of the fixed source universe,
complete declaration-specific four-point review of all {len(tier_b)} correspondence rows,
and accepted compiled evidence for every Tier-B SUSPECT/VACUOUS row plus the recorded
stratified OK-row sample. The review-tier and sampling limitations are stated below.

## Method

Tier A scans every theorem/lemma statement in the 15-file universe: the 14 flat source
modules plus `MatrixConcentration.lean`, excluding `.lake/**`,
`MatrixConcentration/Verification/**`, and `.audit_work/**`. It also audits the environment
telescope of every correspondence theorem for accidental auto-bound single-letter Type/Prop
variables. The syntax detector was calibrated on three planted positives; the auto-bound
detector was calibrated on a self-contained plant with one auto-bound Type and one
auto-bound Prop.

Tier B reads exactly the fixed correspondence rows and records four independent cells per
row: a jointly satisfiable model, triviality/junk-value analysis, typeclass
nondegeneracy, and quantifier/auto-implicit analysis. The merger verifies every primary
`source: File.lean:line[-line]` citation against a declaration location derived directly
from the 14 source modules. An independent validator rejects blank, duplicated, generic, or
schema-drifted review records. This fixed row set is deliberately not claimed to cover
unpublished conditional helpers or every proposition-valued hypothesis outside the 467
published rows.

Tier C covers every SUSPECT/VACUOUS row plus a deterministic, stratified sample of five OK
rows per chapter. Chapters containing OK definitions must contribute at least one definition.
Evidence is either a direct downstream library citation or a named compiled application.
The environment collector requires the audited endpoint in the evidence theorem's type or
value, records the exact theorem type and axiom set, and rejects an unrelated clean theorem
as a negative control. Named evidence classified `CLOSED_BY_EVIDENCE` must expose zero
undischarged Prop binders, preventing a generic restatement from counting as a concrete
model.

## Results

| Tier | Standing | Measured coverage | Result |
|---|---|---|---|
| A — calibrated syntax and auto-bound triage | machine | {tier_a_summary['statements']} statements; {auto_metrics['THEOREM_ENDPOINTS']} correspondence theorem endpoints; {auto_metrics['ALL_ENDPOINT_BINDER_ROWS']} binders | 3 syntax hits, all adjudicated boundary helpers; {auto_metrics['CANDIDATE_BINDERS']}/{auto_metrics['CANDIDATE_BINDERS']} single-letter candidates explicit; 0 suspect auto-binds |
| B — four-point close reading | review | {len(tier_b)} rows ({kinds['theorem']} theorem, {kinds['definition']} definition endpoints) | {verdicts['OK']} OK, {verdicts['SUSPECT']} SUSPECT, {verdicts['VACUOUS']} VACUOUS |
| C — compiled evidence | machine compilation plus review mapping | {len(sample)} sampled OK + {verdicts['SUSPECT']} SUSPECT + {verdicts['VACUOUS']} VACUOUS | {len(coverage)}/{len(coverage)} COVERED; methods {dict(sorted(methods.items()))} |

Every numerical claim traces to a file under `logs/`; the certified source snapshot is
[`source_manifest.txt`](logs/source_manifest.txt).

## Findings

### V6-F1 — INFO — REJECTED: `maxSummandSq` boundary is outside every in-scope use

- **Location:** [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2931`](../Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean#L2931)
- **Measured evidence:** [`suspect_maxSummandSq_unbounded_family_collapse`](scripts/witnesses/V6Witnesses.lean#L115)
  proves that an unbounded rational-indexed scalar-matrix family has `maxSummandSq = 0`;
  [`suspect_maxSummandSq_finite_nonzero_model`](scripts/witnesses/V6Witnesses.lean#L167)
  proves a singleton nonzero family has value 1.
- **Containment:** the compiled-use audit found {metric(maxsummand_text, 'DIRECT_COMPILED_USERS')}
  compiled direct users: {metric(maxsummand_text, 'HANDWRITTEN_DOWNSTREAM_USERS')}
  handwritten theorem users, {metric(maxsummand_text, 'HANDWRITTEN_FINTYPE_GUARDED_PREDICATES')}
  handwritten finite-guarded predicate, and
  {metric(maxsummand_text, 'GENERATED_DEFINITION_HELPERS')} generated definition helpers.
  All {metric(maxsummand_text, 'HANDWRITTEN_WITH_FINTYPE_IN_TELESCOPE')}
  handwritten theorem users carry `Fintype`.
- **Correction-pass disposition:** **REJECTED as a soundness defect.** Tropp's TeX and every
  library theorem use a finite sequence. The unrestricted index is only a totalized API
  extension, and no in-scope result reaches its infinite unbounded branch. The definition and
  signature remain unchanged; its docstring now discloses the fallback explicitly.

Raw containment: [`v6_maxsummand_users.log`](logs/v6_maxsummand_users.log) and
[`v6_maxsummand_users.tsv`](logs/v6_maxsummand_users.tsv).

### V6-F2 — INFO — REJECTED: `gChernoff` zero boundary is avoided or neutralized

- **Location:** [`Chapter5_SumOfPSDMatrices.lean:220`](../Chapter5_SumOfPSDMatrices.lean#L220)
- **Measured evidence:** [`suspect_gChernoff_zero_bound`](scripts/witnesses/V6Witnesses.lean#L{declaration_line('suspect_gChernoff_zero_bound')})
  proves `gChernoff 1 0 = 0`, while
  [`suspect_gChernoff_positive_bound`](scripts/witnesses/V6Witnesses.lean#L{declaration_line('suspect_gChernoff_positive_bound')}) proves the
  intended positive-scale formula at `L = 1`.
- **Correction-pass disposition:** **REJECTED as a soundness defect.** The TeX formula is used
  on `L > 0`; every current theorem either carries that strict guard or proves a separate
  zero-scale branch in which the coefficient is eliminated. The dependency cone has 43
  downstream source declarations (44 declarations including `gChernoff` itself); changing
  the totalization would alter that cone without improving a result. The definition remains
  unchanged and its docstring now discloses both Lean's value and the analytic limit.

### V6-F3 — INFO — other totalized semantic boundaries are explicit review observations

The remaining {len(other_suspects)} SUSPECT endpoints are not globally vacuous: each has a
recorded nondegenerate model and accepted endpoint-dependent Tier-C evidence. They expose
public totalizations such as empty dimensions, nonintegrable Bochner integrals, zero
denominators, clipped Bernoulli weights, or unguarded log/perspective domains. Their exact
names are:

{", ".join(f"`{name}`" for name in other_suspects)}.

These are kept visible rather than promoted en masse to defects: several are documented
sentinels or standard total-function APIs, and substantive theorem callers add the missing
guards. The table below preserves the exact row-by-row adjudication.

## Tier A — calibrated red-flag scan

The three planted statements (contradictory numeric premises/reflexive conclusion,
`IsEmpty` quantification, and syntactic reflexivity) were all detected: 3/3. Production
contained {len(tier_a_hits)} hits: {hit_names}. They are explicit empty-dimension or
empty-index branches, not vacuous main theorems.

The separate auto-bound plant produced
{auto_metrics['CALIBRATION_ACTUAL_HITS']}/{auto_metrics['CALIBRATION_EXPECTED_HITS']} expected
hits. Production measured {auto_metrics['ALL_ENDPOINT_BINDER_ROWS']} binders across
{auto_metrics['THEOREM_ENDPOINTS']} theorem endpoints and checked
{auto_metrics['CANDIDATE_BINDERS']} single-letter Type/Prop candidates;
{auto_metrics['EXPLICITLY_ACCOUNTED']} were explicitly accounted for and
{auto_metrics['SUSPECT_AUTO_BOUND']} were suspect.

Raw evidence:
[`v6_tier_a_summary.json`](logs/v6_tier_a_summary.json),
[`v6_tier_a_statements.tsv`](logs/v6_tier_a_statements.tsv),
[`v6_tier_a_hits.tsv`](logs/v6_tier_a_hits.tsv),
[`v6_vacuity_calibration.tsv`](logs/v6_vacuity_calibration.tsv),
[`v6_autoimplicit_calibration_binders.tsv`](logs/v6_autoimplicit_calibration_binders.tsv),
and [`v6_autoimplicit_run.log`](logs/v6_autoimplicit_run.log).

## Tier B — all correspondence rows

### Chapter totals

{chapter_summary(tier_b, verdicts)}

### Complete four-point review ledger

The following tables are a rendered view of the authoritative curated TSV shards and merged
ledger. Each row includes all four checklist judgments, its adjudication, and direct source
and telescope references.

{tier_b_tables}

### SUSPECT/VACUOUS adjudication

{suspect_table(tier_b, coverage_by_global)}

## Tier C — compiled evidence

### Reproducible stratified sample

The seed is
`{sampling_seed}`.
The sampler selects one random OK definition first whenever a chapter has any, then fills
the remaining positions from the other OK rows; chapters without OK definitions sample five
OK theorems. It produced {sample_kinds['theorem']} theorem and
{sample_kinds['definition']} definition rows. Definition evidence was exercised in chapters
{", ".join(map(str, sampled_definition_chapters))}.

Exact command:

```sh
python3 MatrixConcentration/Verification/scripts/v6_sample_ok.py
```

The dynamic obligation set contains {len(coverage)} rows:
{len(sample)} sampled OK, {verdicts['SUSPECT']} SUSPECT, and
{verdicts['VACUOUS']} VACUOUS. All are COVERED. The unrelated allowed-axiom theorem was
rejected because it had no endpoint dependency; the separate `sorry` witness was also
rejected by the witness acceptance checker.

### Complete Tier-C obligation ledger

{coverage_tables(coverage)}

## Exact re-run commands

Run from the project root:

```sh
cd "$(git rev-parse --show-toplevel)"
./MatrixConcentration/Verification/scripts/v6_run.sh
```

The runner records every stage in
[`v6_run.log`](logs/v6_run.log), repeats
`-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false` for every single-file Lean command,
checks the source manifest before executing, regenerates both positive controls, merges only
the immutable curated Tier-B shards, recompiles positive/negative witnesses, collects
environment dependencies/axioms, validates the dynamic obligation set, and assembles this
report only after every gate passes.

Useful standalone validation commands:

```sh
python3 MatrixConcentration/Verification/scripts/v6_merge_curated_tier_b.py
python3 MatrixConcentration/Verification/scripts/v6_validate_curated_tier_b.py
python3 MatrixConcentration/Verification/scripts/v6_validate_tier_c.py
python3 MatrixConcentration/Verification/scripts/v6_assemble_report.py
```

## Raw evidence

- Tier A and auto-bound:
  [`v6_tier_a_summary.json`](logs/v6_tier_a_summary.json),
  [`v6_tier_a_adjudication.tsv`](logs/v6_tier_a_adjudication.tsv),
  [`v6_endpoint_telescopes.tsv`](logs/v6_endpoint_telescopes.tsv),
  [`v6_endpoint_binders.tsv`](logs/v6_endpoint_binders.tsv),
  [`v6_autoimplicit_audit.tsv`](logs/v6_autoimplicit_audit.tsv).
- Tier B:
  [`v6_correspondence_rows.tsv`](logs/v6_correspondence_rows.tsv),
  [`v6_tier_b_review.tsv`](logs/v6_tier_b_review.tsv),
  [`v6_tier_b_summary.json`](logs/v6_tier_b_summary.json),
  [`v6_tier_b_note_validation.json`](logs/v6_tier_b_note_validation.json),
  and [`curation/README.md`](curation/README.md).
- Tier C:
  [`v6_tier_c_sample.tsv`](logs/v6_tier_c_sample.tsv),
  [`curation/v6_tier_c_evidence.tsv`](curation/v6_tier_c_evidence.tsv),
  [`v6_tier_c_environment_evidence.tsv`](logs/v6_tier_c_environment_evidence.tsv),
  [`v6_tier_c_coverage.tsv`](logs/v6_tier_c_coverage.tsv),
  [`v6_tier_c_coverage_summary.json`](logs/v6_tier_c_coverage_summary.json).
- Witness acceptance:
  [`V6Witnesses.lean`](scripts/witnesses/V6Witnesses.lean),
  [`v6_witnesses_compile_status.log`](logs/v6_witnesses_compile_status.log),
  [`v6_witness_axioms.tsv`](logs/v6_witness_axioms.tsv),
  [`v6_witness_acceptance.json`](logs/v6_witness_acceptance.json),
  [`calibration_bad_witness_compile.log`](logs/calibration_bad_witness_compile.log),
  and [`v6_tier_c_negative_evidence.tsv`](logs/v6_tier_c_negative_evidence.tsv).

## Limitations

- Tier A is syntactic. Calibration proves that the implemented patterns fire; silence outside
  those patterns is not a semantic decision procedure.
- Tier B is review-tier. Its validators prove fixed-row coverage, source/telescope joins, and
  declaration-specific record structure; the satisfiability/triviality judgments remain
  mathematical review.
- Tier C samples {len(sample)} of the {verdicts['OK']} OK rows rather than all OK rows. It
  does cover every SUSPECT and VACUOUS row.
- A direct library citation proves that the endpoint is actually used; its premise mapping is
  still review evidence. A concrete named witness proves existence of that model, not
  non-vacuity for every parameter value.
- The auto-bound audit is scoped to single-codepoint Type/Prop variables on correspondence
  theorem endpoints; arbitrary multi-character implicit identifiers are outside that check.
- Tier B is intentionally the 467-row published correspondence set. It cannot by itself
  exclude a clean conditional helper of shape `P → Q` outside those rows when the library
  never constructs `P`; V10 supplies that broader conditional-interface census, which is
  outside V6's own guarantee.
- Book-faithfulness is out of scope; the TranslationReport and correspondence table cover it.
"""

    REPORT.write_text(report.rstrip() + "\n", encoding="utf-8")
    print("V6 REPORT ASSEMBLY")
    print(f"REPORT {REPORT.relative_to(VERIFICATION.parent)}")
    print(f"TIER_B_ROWS {len(tier_b)}")
    print(f"TIER_B_OK {verdicts['OK']}")
    print(f"TIER_B_SUSPECT {verdicts['SUSPECT']}")
    print(f"TIER_B_VACUOUS {verdicts['VACUOUS']}")
    print(f"TIER_C_OBLIGATIONS {len(coverage)}")
    print(f"TIER_C_SAMPLE_THEOREMS {sample_kinds['theorem']}")
    print(f"TIER_C_SAMPLE_DEFINITIONS {sample_kinds['definition']}")
    print("FINDINGS CRITICAL=0 MAJOR=0 MINOR=0 INFO=3")
    print("VERDICT PASS-WITH-NOTES")
    return 0


if __name__ == "__main__":
    sys.exit(main())
