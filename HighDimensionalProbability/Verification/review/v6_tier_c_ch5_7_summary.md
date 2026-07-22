# V6 Tier-C witness summary: Chapters 5--7

Status: **FINAL PASS**.  The final official full runner exited 0 with
`overall=PASS` and `lean_execution_complete=true`.  Its positive witness build
completed all 8,646 jobs and exited 0; the declaration-exact harness audited
all seven named witnesses; and both planted-bad acceptance gates rejected the
calibration witness.

The development record is intentionally not presented as a first-try pass.
The first two official witness builds failed while the concrete Chapter 7 and
Tier-A instances were being completed (first six proof/elaboration goals,
then four).  A target-only build exposed and reduced the final coordinate
continuity mismatch to one goal.  After those defects were corrected, the
authoritative final official run produced the preserved PASS artifacts listed
below.

## Final executed result

| Gate or measurement | Final result |
|---|---|
| fixed queue | 15/15 rows: five each from Chapters 5, 6, and 7 |
| evidence split | 10 direct-use citations; 5 compiled concrete witnesses |
| exact V4 direct value edges | 10/10 |
| compiled declarations | 7 total: 5 queue witnesses plus 2 Tier-A witnesses |
| witness build | PASS; 8,646/8,646 jobs; exit 0 |
| exact axiom audit | PASS; 7/7; every set is exactly `Classical.choice`, `Quot.sound`, `propext` |
| planted lexical gate | PASS by rejecting source token `sorry` |
| planted axiom gate | PASS by rejecting emitted `sorryAx` |
| final runner | PASS; full mode; Lean execution complete |

The final full run also freshly parsed 7,740 library declarations, confirmed
7,402 complete uniquely joined V4 binder telescopes, recovered exactly the two
expected Chapter 5--7 Tier-A hits, and found zero auto-bound flags.

## Fixed queue coverage

The input is exactly the fifteen `sampling_plan / ok_review_queue_head` rows
of `v6_tier_b_ch5_7.tsv`: ranks 1--5 in each of Chapters 5, 6, and 7.  No
non-queue row was substituted.

The queue is not narrowed to README rows: `row_inventory.py` ranks every
eligible non-exercise row in the fixed 838-row census
(`core_formalized`/`appendix_proved`, excluding `STRONGER`) with seed
`hdp-v6-ok-row-candidate-order-v1`.  The runner cross-checks the first five
candidate ranks in `sampling_plan.json`, the queue head, and the Tier-B ledger
against the same fixed IDs.

| Chapter | Tier-B row | Tier-C evidence |
|---|---|---|
| 5 | `census-4873958abc52b612` | compiled `queue_ch5_grassmannian_fin2_line` |
| 5 | `census-9a8303edb533db45` | compiled `queue_ch5_matrixNorm_loewner_diagonal_fin2` |
| 5 | `census-28ee26691f687a9c` | citation `HDP.Chapter5.sparseSBM_expectedNoise_exact` → `matrixBernsteinExpectation` |
| 5 | `census-a42f06353bdaf063` | citation `HDP.Chapter5.sphere_blowUp` → `blowUp_of_centered_concentration` |
| 5 | `census-636ecf0b5c2c32b0` | citation `HDP.Chapter5.randomProjection_rms` → `randomProjection_secondMoment` |
| 6 | `census-78a4a177ee6726a5` | citation `HDP.Chapter6.theorem_6_4_1` → `symmetricRandomMatrix_expectedNorm_upper_of_symmetrization` |
| 6 | `census-f5a50680149423f4` | citation `HDP.Chapter6.gaussianSymmetrization_source` → `gaussianSymmetrization_upper` |
| 6 | `census-1edd5d9d59f81553` | citation `HDP.Chapter6.hansonWright` → `quadraticForm_sub_integral_eq_diagonal_add_offDiagonal` |
| 6 | `census-15e0e28502a3aa01` | citation `HDP.Chapter6.hansonWright_offDiagonal_lmgf` → `gaussianReplacement` |
| 6 | `census-96eaba74736a906b` | citation `HDP.Chapter6.symmetrization` → `integral_norm_le_integral_norm_add_independent_centered` |
| 7 | `census-0560df665cff4b2d` | compiled `queue_ch7_gaussianInterpolation_fin1_half` |
| 7 | `census-bd0478c6633a1f9d` | compiled `queue_ch7_crossPolytope_dimension_two` |
| 7 | `census-ea1c69d973f1e27b` | compiled `queue_ch7_multivariateGaussianIBP_fin1` |
| 7 | `census-a334813e84362d44` | citation private `HDP.Chapter7.gaussianIntegrationByParts_measure` → `gaussianIntegrationByParts` |
| 7 | `census-158ae90881f0f306` | citation `HDP.Chapter9.example_9_7_4_cubeGaussianWidth` → `cubeGaussianWidth_eq_source` |

The ten citation rows are not accepted from names or prose alone: the runner
requires an exact V4 proof-body (`origin=value`) direct-dependency edge from
the named citing theorem to the queue endpoint, and allowed axiom sets on
both declarations.  The recorded rationale explains which endpoint
hypotheses the citing proof actually discharges.

The five compiled queue witnesses fix nonempty dimensions (`Fin 1`, `Fin 2`),
an interior parameter (`u=1/2`), distinct positive-definite interpolation
covariances, concrete nonzero matrices, and a named nonzero smooth compactly
supported cutoff.  Each theorem states an instantiated endpoint conclusion;
none is a `#check` or a restatement under arbitrary unconstructed hypotheses.

## Fresh Tier-A additions

A fresh full-library scan found exactly two Chapter 5--7 source hits:

1. `HDP.Chapter6.Exercise.exercise_6_25`
2. `HDP.Chapter7.exercise_7_7_logPartitionDerivativeExpression_nonpos`

The first is a scanner false positive caused by merging two separately bound
`p` variables.  Because its global exercise declaration still uses
`sorryAx`, the clean witness independently proves a complete concrete instance
of both branches (`p=3/2` and `p=2`) instead of importing that axiom into the
witness.  The second witness fixes `beta=1`, `I=Fin 2`, negative increment
gaps, and positive weights.

## Checker contract

`run_v6_tier_c_ch5_7.py` deterministically requires:

- the exact fifteen queue row IDs and ranks;
- the exact seven named compiled declarations (five queue plus two Tier-A);
- ten exact V4 direct citation edges, with clean source and target axioms;
- `set_option autoImplicit false`;
- no executable `sorry` or `admit`;
- no import of
  `MatrixConcentration.Appendix_RosenthalPinelis`;
- successful project-option compilation;
- one `Lean.collectAxioms` result per theorem, each contained in
  `{propext, Classical.choice, Quot.sound}`;
- rejection of the suite-neutral planted theorem in
  `.audit_work/verification/V6TierCPlantedBad.lean` both lexically and through
  a reported `sorryAx`.

## Evidence paths

- Witnesses:
  `HighDimensionalProbability/Verification/scripts/witnesses/V6TierCCh5_7.lean`
- Runner:
  `HighDimensionalProbability/Verification/scripts/run_v6_tier_c_ch5_7.py`
- Axiom harness:
  `.audit_work/verification/V6TierCCh5_7AxiomAudit.lean`
- Planted bad witness:
  `.audit_work/verification/V6TierCPlantedBad.lean`
- Final machine report:
  `HighDimensionalProbability/Verification/logs/v6_tier_c_ch5_7_results.json`
- Positive build:
  `HighDimensionalProbability/Verification/logs/v6_tier_c_ch5_7_build.log`
- Exact axiom rows:
  `HighDimensionalProbability/Verification/logs/v6_tier_c_ch5_7_axioms.log`
- Planted-negative calibration:
  `HighDimensionalProbability/Verification/logs/v6_tier_c_ch5_7_planted_bad.log`
- Final runner log:
  `HighDimensionalProbability/Verification/logs/v6_tier_c_ch5_7_runner.log`
- Fresh Tier-A scan:
  `HighDimensionalProbability/Verification/logs/v6_tier_c_ch5_7_tier_a_scan.json`

The read-only replay is:

```text
python3 -B HighDimensionalProbability/Verification/scripts/run_v6_tier_c_ch5_7.py --check
```

It validates the current static contracts, the preserved full PASS JSON,
successful raw logs, exact seven-row axiom set, planted rejection, source-to-
olean freshness, and prints SHA-256 hashes without invoking Lean or Lake.
