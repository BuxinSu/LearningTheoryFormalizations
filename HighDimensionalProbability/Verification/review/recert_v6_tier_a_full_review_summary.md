# V6 Tier-A full semantic review

Reviewed machine-red-flag declarations: **13**.

- `OK_FALSE_POSITIVE`: **13**
- `SUSPECT`: **0**
- `VACUOUS`: **0**
- Tier-C/source-repair required: **3**

The source statement column is the scanner's exact token content with
whitespace normalized. Each row separately records H (joint
satisfiability), C (conclusion substance), T (nontrivial model/domain),
and Q (quantifier/binder integrity). A semantic verdict does not
override V1 buildability, V3 placeholder, or V4 axiom findings.

## Reason inventory

| Reason | Rows |
|---|---:|
| `contradictory_numeric_bounds` | 2 |
| `fin_zero_domain` | 2 |
| `is_empty_domain` | 2 |
| `near_degenerate_numeric_bounds` | 4 |
| `zero_fintype_card` | 3 |

## Tier-C and repair queue

| Declaration | Verdict | Required action/witness |
|---|---|---|
| `HDP.Chapter6.Exercise.exercise_6_25` | `OK_FALSE_POSITIVE` | HDP.Verification.V6TierC.tierA_ch6_exercise625_two_branches_nonvacuous |
| `HDP.Chapter7.exercise_7_7_logPartitionDerivativeExpression_nonpos` | `OK_FALSE_POSITIVE` | HDP.Verification.V6TierC.tierA_ch7_logPartition_positiveBeta_fin2 |
| `HDP.matrixSingularValue_of_finrank_le` | `OK_FALSE_POSITIVE` | HDP.Verification.V6TierC.tierA_prelude_matrixSingularValue_fin1_index_one |

## Merge contract for the final scanner

The builder accepts repeated `--scan-json` arguments. It unions
reason rows for an identical `(path, name, statement)` and fails
closed if a later auto-bound-binder hit has no manual decision or
adds an unreviewed reason ID. After appending/updating the decision
TSV, rerunning the builder deterministically regenerates this ledger
and summary.

Scanner inputs for this snapshot:

- `HighDimensionalProbability/Verification/logs/recert_v6_tier_a_final.json`
