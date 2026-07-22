# V7 — Definition sanity (no hollow definitions)

**Verdict: PASS-WITH-NOTES**

**Tier: mixed (machine inventory/compilation and review sanity judgments)**

**Finding count: C=0 M=0 m=0 I=1**

## Guarantee

For the corrected source snapshot, all 149 source-level
`def`/`structure`/`class` candidates are enumerated: 135 public definitions,
14 private definitions, and no structures or classes. The measured
load-bearing set contains 51 definitions. Every one has either a
source citation whose statement forces substantive behavior or a named,
kernel-checked concrete witness. No load-bearing definition was found to be
constant, hollow, or vacuous on its intended nondegenerate inputs.

The corrected source-level dead-code graph has 78 zero-referrer declarations
after excluding the 401 theorem-kind correspondence endpoints as deliberately
terminal book results. The set contains 75 theorem/lemma leaves and three
definitions; definition endpoints remain eligible for the census. These
declarations are reported as the informational finding V7-F1, so the fixed
verdict remains `PASS-WITH-NOTES`. The final standalone runner reproduced the
corrected inventory and terminated with status `PASS` and exit code 0.

## Method

Run the complete check from the project root with:

```sh
bash MatrixConcentration/Verification/scripts/v7_run.sh
```

The runner first checks the pinned source manifest and then executes these
steps, failing on the first unsuccessful command:

```sh
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/make_calibration_plants.py
python3 MatrixConcentration/Verification/scripts/v6_extract_correspondence.py
~/.elan/bin/lake env lean -DmaxSynthPendingDepth=3 \
  -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/v6_endpoint_telescopes.lean
python3 MatrixConcentration/Verification/scripts/v7_extract_source_declarations.py
~/.elan/bin/lake env lean -DmaxSynthPendingDepth=3 \
  -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/v7_environment_dependencies.lean
python3 MatrixConcentration/Verification/scripts/v7_analyze_dependencies.py
bash MatrixConcentration/Verification/scripts/v7_run_witnesses.sh
bash MatrixConcentration/Verification/scripts/v7_run_dead_code_calibration.sh
python3 MatrixConcentration/Verification/scripts/v7_check_sanity.py
```

The single-file Lean commands use the lakefile caveat flags explicitly.
[`logs/v7_run_status.log`](logs/v7_run_status.log) is the fresh
post-correction status record: it reports 51 load-bearing definitions, 51
sanity rows covered, 78 dead-code candidates (76 public and two private), run
state `PASS`, and exit code 0. The accepted standalone run is
`ea099f89-3c20-466b-bbfb-a4e7abd839f5`; it ran from
`2026-07-20T18:26:10Z` through `2026-07-20T18:30:10Z` (240 seconds).
Its run-log SHA-256 is
`1d8ab2977e077100389e2283fd79fd1abfb5f1203e8c67c3cd2814b31518b497`,
and it is bound to source digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`
and verification-input digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.

### Candidate and load-bearing selection

The source inventory is a comment/string-aware lexical scan of exactly the 14
flat source modules. Every extracted declaration is then resolved uniquely
against the imported Lean environment by module, user-facing name, source
range, and declaration kind. The corrected inventory contains 1,443 public and 82
private source declarations; the failure log is empty.

The candidate universe is every source `def`, `structure`, or `class`,
regardless of visibility. It contains 149 definitions (135 public and 14
private), with zero structures/classes. For each of the 401 theorem-kind
endpoints among the 467 Book→Lean correspondence rows, the environment harness
collects constants occurring directly anywhere in its elaborated type. A
definition is load-bearing when either:

1. it is one of the four definitions in `Prelude.lean`; or
2. it occurs directly in the elaborated types of at least three distinct
   theorem-kind correspondence endpoints.

Fifty public definitions meet the threshold. No private definition does.
The Prelude union adds `rayleigh`, whose direct-type count is one, producing
the final set of 51. The 66 correspondence rows whose endpoints elaborate as
definitions are not counted as “theorems” for this threshold.

### Sanity evidence

For citation-backed rows, the checker requires the cited source declaration to
resolve, to contain the target definition as a direct type or value/proof
dependency, and to use no axiom outside
`{propext, Classical.choice, Quot.sound}`. The review column in the complete
register explains why the cited statement would fail under the relevant
constant or degenerate interpretation.

For witness-backed rows, the named witness must:

- occur in
  [`scripts/witnesses/V7Witnesses.lean`](scripts/witnesses/V7Witnesses.lean),
  which sets `autoImplicit false`;
- mention the audited definition directly in its elaborated type;
- compile with explicit Lean exit status 0 and no error, `sorry` warning, or
  `sorryAx`;
- have `Lean.collectAxioms` contained in the allowed three-axiom set.

All 15 compiled witness theorems satisfy those conditions. Fourteen are used
by the corrected load-bearing register. Several conjunction witnesses cover
compatible definition families, so those 14 witnesses support 19 of the 51
register rows; the remaining 32 use citations. The compiled
`maxSummandSq_finite_nonzero_model` witness remains valid boundary evidence,
but `maxSummandSq` no longer meets the corrected ≥3 correspondence-reference
threshold and therefore is not a register row.

### Calibration

The witness acceptance filter was calibrated on `.audit_work/BadWitness.lean`.
Lean itself exits 0 but emits `declaration uses 'sorry'`; the checker records
the successful compilation status, confirms there was no unrelated Lean
error, detects the warning, and rejects the witness. This distinguishes a
working rejection filter from a compiler failure.

The same type-plus-value direct-reference machinery used by the dead-code
sweep was run against `.audit_work/DeadCodePlant.lean`. It reported
`verificationUnreferencedPlant` with exactly zero referrers. Both plant and
calibration harness exited 0.

## Results

### Coverage counts

| Measurement | Result |
|---|---:|
| Public source declarations resolved | 1,443 / 1,443 |
| Private source declarations resolved | 82 / 82 |
| Public definition candidates | 135 |
| Private definition candidates | 14 |
| Structures / classes, public or private | 0 / 0 |
| Correspondence endpoints | 467 |
| Theorem-kind correspondence endpoints | 401 |
| Prelude definitions | 4 |
| Definitions meeting the ≥3 threshold | 50 public, 0 private |
| Load-bearing union | 51 |
| Sanity rows covered | 51 / 51 |
| Citation-backed rows | 32 |
| Witness-backed rows | 19 |
| Compiled named witness theorems | 15 |
| Named witness theorems used by the register | 14 |
| Witnesses with disallowed axioms | 0 |
| Official witness compile errors / `sorry` warnings | 0 / 0 |

### Complete load-bearing register

“Type refs” is the number of distinct theorem-kind correspondence endpoints
whose elaborated type directly contains the definition. The full machine
register also records module, source line, axiom set, and the complete
nondegeneracy rationale in
[`logs/v7_sanity_register.tsv`](logs/v7_sanity_register.tsv).

| Definition | Type refs | Basis | Method | Evidence | Substantive fact |
|---|---:|---|---|---|---|
| `IsBernoulli` | 16 | ≥3 types | witness | `isBernoulli_identity` | The nondegenerate Bernoulli(1/2) identity law satisfies the predicate; the constant-zero one-point law does not, since its expectation is not 1/2. |
| `IsRademacher` | 13 | ≥3 types | witness | `isRademacher_identity` | The identity Rademacher law satisfies it; a constant-zero one-point law is excluded by the forced unit second moment. |
| `IsStdGaussian` | 18 | ≥3 types | witness | `isStdGaussian_identity` | The standard-Gaussian identity law satisfies it; a constant-zero one-point law is excluded by the forced unit second moment. |
| `MIntegrable` | 47 | ≥3 types | witness | `mIntegrable_nonzero_constant` | A nonzero 1×1 constant is integrable on a one-point space but not under counting measure on `Nat`, ruling out both constant truth values. |
| `colGram` | 3 | ≥3 types | citation | `colGram_apply` | Every entry is exactly `Bᵢₖ * conj(Bⱼₖ)`. |
| `colNormSq` | 12 | ≥3 types | citation | `sum_colNormSq` | The column quantities sum exactly to the squared Frobenius norm. |
| `columnSubmatrix` | 5 | ≥3 types | citation | `columnSubmatrix_gram` | Its Gram matrix is the selected sum of column Gram matrices. |
| `covarianceMatrix` | 6 | ≥3 types | citation | `covarianceMatrix_apply` | Each entry is the corresponding covariance integral. |
| `entryDiag` | 3 | ≥3 types | citation | `sup_colNormSq_eq_lambdaMax` | Selected column norms are represented by the largest eigenvalue of its sum. |
| `entrywiseL1Norm` | 8 | ≥3 types | citation | `entrywiseL1Norm_eq_zero_iff` | It vanishes exactly on the zero matrix. |
| `erLaplacian` | 3 | ≥3 types | citation | `compressed_sum_eq` | Its compression is exactly the Laplacian coefficient sum, whose coefficient model is independently nonzero below. |
| `expectation` | 100 | ≥3 types | citation | `expectation_const` | Expectation fixes every constant matrix under a probability measure. |
| `featureOuter` | 4 | ≥3 types | witness | `featureOuter_nonzero_model` | The all-one `Fin 1` feature vector produces the 1×1 identity. |
| `frobeniusNorm` | 12 | ≥3 types | citation | `frobeniusNorm_pos` | It is strictly positive on every nonzero finite matrix. |
| `gBernstein` | 7 | ≥3 types | witness | `gBernstein_value_model` | `gBernstein 1 1 = 3/4`. |
| `gChernoff` | 6 | ≥3 types | witness | `gChernoff_positive_model` | `gChernoff 1 1` is strictly positive. |
| `hermDilation` | 13 | ≥3 types | citation | `l2_opNorm_hermDilation` | Hermitian dilation preserves the spectral norm. |
| `intdim` | 29 | ≥3 types | citation | `intdim_one` | The identity has intrinsic dimension equal to the index cardinality. |
| `l2norm` | 14 | Prelude | citation | `l2norm_sq` | Its square is the sum of squared coordinate norms. |
| `lambdaMax` | 75 | Prelude | citation | `lambdaMax_one` | The largest eigenvalue of every nonempty identity matrix is one. |
| `lambdaMin` | 52 | Prelude | citation | `lambdaMin_one` | The smallest eigenvalue of every nonempty identity matrix is one. |
| `lapMatrixC` | 3 | ≥3 types | citation | `connected_iff_secondSmallest_pos` | On graph Laplacians, the composite quantity is positive exactly for connected graphs, forcing substantive behavior across connected/disconnected inputs. |
| `laplCoeff` | 7 | ≥3 types | witness | `laplCoeff_nonzero_model` | For edge `(0,1)` in dimension two, entry `(0,0)` is exactly one. |
| `matmulProb` | 9 | ≥3 types | citation | `matmulProb_sum_eq_one_of_pair_ne_zero` | The probabilities normalize whenever the matrix pair is not jointly zero. |
| `matmulValue` | 9 | ≥3 types | citation | `expectation_matmulEstimator_book` | The estimator expectation is exactly `B * C`. |
| `matrixCgf` | 18 | ≥3 types | citation | `gaussian_matrix_cgf` | A Gaussian Hermitian series has the stated nonconstant quadratic cgf. |
| `matrixMgf` | 9 | ≥3 types | citation | `matrixMgf_hasSum_moments` | Its full convergent moment series sums to the matrix mgf. |
| `matrixVar` | 10 | ≥3 types | witness | `variance_statistics_nonzero_models` | For the 1×1 scalar Rademacher matrix, it is exactly the identity. |
| `matrixVar1` | 5 | ≥3 types | witness | `variance_statistics_nonzero_models` | On the same model, the first rectangular variance is exactly the identity. |
| `matrixVar2` | 5 | ≥3 types | witness | `variance_statistics_nonzero_models` | On the same model, the second rectangular variance is exactly the identity. |
| `mre` | 3 | ≥3 types | witness | `entropy_nonzero_models` | For the 1×1 diagonal pair `(exp(1),1)`, matrix relative entropy is exactly one. |
| `psiOne` | 4 | ≥3 types | witness | `psiOne_positive_model` | `psiOne 1 1 > 0`; the source separately gives the zero boundary at its second argument zero. |
| `psiTwo` | 4 | ≥3 types | witness | `psiTwo_positive_model` | `psiTwo 1 1 > 0`; the source separately gives the zero boundary at its second argument zero. |
| `rayleigh` | 1 | Prelude | citation | `rayleigh_smul_one` | On `c • I`, it is `c` times the squared `l2norm`. |
| `rowColumnSubmatrix` | 4 | ≥3 types | citation | `rowColumnSubmatrix_eq` | It is exactly the selector product `PBR`. |
| `rowSubmatrix` | 6 | ≥3 types | citation | `rowSubmatrix_apply` | Each entry is the selector times the corresponding entry of `B`. |
| `sampleCovSummand` | 4 | ≥3 types | witness | `sampleCovSummand_nonzero_model` | One all-one sample against a zero population vector in dimension one gives the identity. |
| `schattenOneNorm` | 7 | ≥3 types | citation | `schattenOneNorm_eq_zero_iff` | It vanishes exactly on the zero matrix. |
| `secondMoment` | 5 | ≥3 types | witness | `secondMoment_nonzero_model` | A constant 1×1 identity sample on a one-point space has second moment one. |
| `secondSmallestEigenvalue` | 3 | ≥3 types | citation | `connected_iff_secondSmallest_pos` | For graph Laplacians, it is positive exactly when the graph is connected. |
| `shiftPow` | 3 | ≥3 types | citation | `shiftPow_apply` | Every entry is the intended varying 0/1 shifted diagonal. |
| `singularValues` | 7 | ≥3 types | citation | `l2_opNorm_eq_sup_singularValues` | Their supremum is the spectral norm, hence positive on a nonzero matrix. |
| `sparsifyProb` | 7 | ≥3 types | citation | `sparsifyProb_sum_eq_one` | For every nonzero matrix, the probabilities sum to one. |
| `sparsifyValue` | 6 | ≥3 types | citation | `sum_sparsifyProb_smul_value` | Probability-weighted values reconstruct every nonzero target matrix. |
| `stableRank` | 11 | ≥3 types | citation | `one_le_stableRank` | It is at least one on every nonzero matrix; the zero 0/0 boundary is explicit. |
| `toeplitzCoeff` | 4 | ≥3 types | citation | `toeplitz_coeff_sum_right` | For positive dimension, its Gram sum is `d • I`. |
| `varStat` | 3 | ≥3 types | witness | `variance_statistics_nonzero_models` | On the scalar Rademacher model, it is exactly one. |
| `varStatHerm` | 9 | ≥3 types | witness | `variance_statistics_nonzero_models` | On the same Hermitian model, it is exactly one. |
| `vre` | 3 | ≥3 types | witness | `entropy_nonzero_models` | For the one-coordinate pair `(exp(1),1)`, vector relative entropy is exactly one. |
| `weakVariance` | 3 | ≥3 types | citation | `variance_le_max_dim_mul_weakVariance` | It universally controls the ordinary nonnegative coefficient variance, which is positive for nonzero coefficient families. |
| `wignerCoeff` | 4 | ≥3 types | citation | `wignerCoeff_sq` | Its square is the nonzero sum of two diagonal matrix units. |

### Targeted boundary review

The register explicitly covers the requested risk classes:

| Risk class | Evidence and conclusion |
|---|---|
| Norm/statistic collapses | Exact zero characterizations cover the entrywise and Schatten norms; positivity covers the Frobenius norm; the scalar Rademacher witness makes all five variance quantities exactly one. |
| Ratio junk values | `stableRank` is guarded by a nonzero hypothesis in `one_le_stableRank`; `intdim_one` gives the correct positive value on identities. Totalized zero-input behavior does not make either quantity identically degenerate. |
| `sInf`/`sSup` and empty dimensions | `lambdaMax_one` and `lambdaMin_one` use nonempty identity matrices; singular-value and weak-variance citations force substantive nonzero behavior. Empty-index conventions therefore do not explain the audited facts. |
| Expectation/distribution semantics | `expectation_const`, the exact second-moment witness, and two-sided Rademacher/Gaussian/Bernoulli predicate witnesses use standard probability measures. |
| Matrix-function/order semantics | Hermitian dilation preserves norm; Gaussian cgf has the expected quadratic form; graph connectivity is equivalent to positivity of the Laplacian spectral statistic. |

The compiled finite singleton witness still establishes
`maxSummandSq = 1` on an intended finite family. After removal of the two
incorrect (6.1.6) correspondence endpoints, however, `maxSummandSq` has fewer
than three theorem-kind correspondence type references and is no longer
load-bearing under V7's declared selection rule. Its separate unbounded-index
boundary remains recorded in V6-F1.

The corrected V6 endpoint ledger independently records 433 `OK`, 34
`SUSPECT`, and zero `VACUOUS` rows among the 467 correspondence endpoints,
with zero suspect automatically bound variables. Tier C covers all 74
obligations: 40 sampled `OK` rows plus all 34 `SUSPECT` rows, discharged by 20
named applications and 54 library citations.

### Post-correction re-certification provenance

The corrected deterministic inventory is 1,443 public plus 82 private source
declarations, 149 definition candidates, 51 load-bearing definitions, 51/51
sanity-register coverage, and 78 post-terminal zero-referrer leaves. The final
manifest-bound standalone V7 runner
`ea099f89-3c20-466b-bbfb-a4e7abd839f5` reproduced these counts and completed
all stages successfully in 240 seconds. Its status record is bound to the same
final source and verification-input manifests as recovery-v7, the fresh
aggregate, V6, and V10; it is the post-correction certification evidence for
this pass.

For historical context, the earlier correction pass changed no source
definition body or signature. It added boundary disclosures to `maxSummandSq` and `gChernoff`,
documentation/deliberate-unused-argument annotations to `sampleCovariance`,
`loewnerIcc`, `projDiag`, and `blockU`, and a missing docstring to
`bernoulliRepresentative`. The current environment/dependency extraction
confirmed that those annotations did not change substantive witness results.
The final (6.1.6) correction did change the declaration universe and
correspondence-reference graph: two incorrect public coverage endpoints were
removed, `maxSummandSq` left the load-bearing set, and
`matrix_rosenthal_pinelis_centered_with_loss_integrable_aux` became a new
zero-referrer support leaf. The `maxSummandSq` infinite-unbounded extension and
`gChernoff` zero-scale totalization remain separately contained and
dispositioned in V6 rather than being reclassified as hollow definitions here.

## Findings

### V7-F1 — INFO — Source declarations with no source-level referrer

**Severity: INFO**

After excluding the 401 theorem-kind correspondence endpoints as deliberately
terminal named book results, 78 source declarations have zero direct
type-or-value references from every other one of the 1,525 source
declarations. The set comprises 43 theorems, 32 lemmas, and three definitions,
with 76 public and two private declarations. Correspondence definition
endpoints are not excluded merely for appearing in the table.

The complete list is reproduced here; the authoritative row-by-row list with
source locations and visibility is
[`logs/v7_dead_code.tsv`](logs/v7_dead_code.tsv).

| Module | Zero-referrer declarations |
|---|---|
| `Appendix_GaussianConcentration` | `essSup_ne_zero_of_lintegral_ne_zero` |
| `Appendix_GoldenThompson` | `ltr_false`, `ltr_true`, `lprod_nil`, `dtrans_le_ctrans`, `trotterC_nonneg` |
| `Appendix_MatrixRosenthal` | `boolSign_false`, `boolSign_true`, `measurable_pairSwap` |
| `Appendix_RosenthalPinelis` | `schattenR_nonneg`, `schattenR_one_eq_schattenOneNorm`, `schattenR_two_eq_frobeniusNorm`, `natCast_rpow_two_div_two_log_eq_exp`, `l2_opNorm_le_schattenR_general`, `schattenR_le_card_mul_l2_opNorm_general`, `schattenR_le_rank_mul_l2_opNorm_general`, `schattenR_eq_zero_iff_general`, `hermitian_nckhintchine_implies_rectangular`, `matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap`, `matrix_rosenthal_pinelis_centered_with_loss_integrable_aux` |
| `Chapter1_Introduction` | `sampleCovariance_relative_error` |
| `Chapter2_MatrixFunctionsAndProbabilityWithMatrices` | `lambdaMin_cfc_of_monotone`, `singularValues_posSemidef_multiset_eq`, `smul_complex`, `expectation_smul_complex`, `rademacherMeasure_integral_id`, `isProbabilityMeasure_bernoulliMeasureReal` |
| `Chapter3_MatrixLaplaceTransformMethod` | `entryCLM_apply`, `isOpen_posDef_herm` |
| `Chapter4_MatrixGaussianAndRademacherSeries` | `posDef_rademacher_mgf`, `rademacher_herm_min_expectation`, `rademacher_herm_min_tail` |
| `Chapter5_SumOfPSDMatrices` | `normalizedLapMatrix`, `erAdjacency`, `rowVec_zero` |
| `Chapter6_SumOfBoundedRandomMatrices` | `IsPosDefKernel`, `matrix_bernstein_herm_min_expectation`, `matrix_bernstein_herm_min_tail`, `expectation_discrete_no_hV`, `matmulProb_sum_eq_one`, `random_feature_error_bound_of_abs_le`, `matrix_rosenthal_pinelis_symmetric`, `matrix_rosenthal_pinelis_centered_with_loss`, `symmetric_sum_lower_bound`, `matrix_bernstein_herm_min_expectation_one_sided`, `matrix_bernstein_herm_min_tail_one_sided` |
| `Chapter7_IntrinsicDimension` | `intdim_bernstein_herm_tail`, `intdim_bernstein_uncentered_tail` |
| `Chapter8_ProofOfLiebsTheorem` | `spectrum_subset_Ioi`, `posSemidef_cfc_of_nonneg`, `posDef_posSqrt_inv`, private `quadFormCLM_apply`, private `conjTransposeCLM_apply`, `operatorMonotoneOn_affine`, `operatorMonotoneOn_smul`, `operatorMonotoneOn_add`, `operatorMonotoneOn_neg_inv_shift`, `operatorMonotoneOn_log`, `not_operatorMonotoneOn_sq`, `not_operatorMonotoneOn_exp`, `operatorConvexOn_smul`, `operatorConvexOn_inv_shift`, `matrix_convex_combo_scalar`, `matrix_convex_combo_one`, `matrix_convex_combo_posSemidef`, `matrix_convex_combo_eigenvalues_mem`, `kronecker_zero_left`, `kronecker_zero_right`, `kronecker_real_smul_left`, `kronecker_real_smul_right`, `kronecker_add_left`, `kronecker_add_right`, `phiMap_sum_nonneg`, `si_c8_1_refutation`, `spectral_sum_outer`, `trace_exp_monotone_of_loewner` |
| `Prelude` | `le_l2_opNorm_of_witness`, `trace_re_le_of_loewner_le` |

These are public/private API leaves, not evidence of unsoundness or hollow
definitions. The three zero-referrer definitions are outside the declared
51-definition load-bearing set; `normalizedLapMatrix` also has concrete
boundary and nonboundary evidence in V6. External downstream users are
outside this repository-local graph, so no removal is implied.

## Raw evidence

| Evidence | Purpose |
|---|---|
| [`logs/v7_run_status.log`](logs/v7_run_status.log) | Final standalone end-to-end PASS status, run identity, bound digests, and 240-second elapsed time |
| [`logs/v7_manifest_check.log`](logs/v7_manifest_check.log) | Source snapshot check |
| [`logs/v7_calibration_plant_generation.log`](logs/v7_calibration_plant_generation.log) | Recreated V7 calibration plants in excluded scratch |
| [`logs/v7_source_inventory_summary.log`](logs/v7_source_inventory_summary.log) and [`logs/v7_public_source_declarations.tsv`](logs/v7_public_source_declarations.tsv) | Complete public inventory |
| [`logs/v7_all_source_declarations.tsv`](logs/v7_all_source_declarations.tsv) | Public plus private source inventory |
| [`logs/v7_environment_dependencies.tsv`](logs/v7_environment_dependencies.tsv) | Elaborated type/value dependencies and axioms |
| [`logs/v7_environment_dependencies_compile.log`](logs/v7_environment_dependencies_compile.log) | Dependency-harness compilation |
| [`logs/v7_source_resolution.tsv`](logs/v7_source_resolution.tsv), [`logs/v7_all_source_resolution.tsv`](logs/v7_all_source_resolution.tsv), and [`logs/v7_source_resolution_failures.log`](logs/v7_source_resolution_failures.log) | Source-to-environment resolution |
| [`logs/v7_definition_type_references.tsv`](logs/v7_definition_type_references.tsv) | All 135 public definition candidates and endpoint referrers |
| [`logs/v7_private_definition_type_references.tsv`](logs/v7_private_definition_type_references.tsv) | All 14 private definition candidates and zero threshold hits |
| [`logs/v7_load_bearing_definitions.tsv`](logs/v7_load_bearing_definitions.tsv) | Exact 51-definition selected set after the fresh runner |
| [`logs/v7_dependency_summary.log`](logs/v7_dependency_summary.log) | Selection and dead-code counts |
| [`logs/v7_sanity_register.tsv`](logs/v7_sanity_register.tsv) and [`logs/v7_sanity_summary.log`](logs/v7_sanity_summary.log) | Per-definition evidence and fail-closed result |
| [`scripts/witnesses/V7Witnesses.lean`](scripts/witnesses/V7Witnesses.lean), [`logs/v7_witnesses_compile.log`](logs/v7_witnesses_compile.log), [`logs/v7_witness_exit_status.log`](logs/v7_witness_exit_status.log), and [`logs/v7_witness_axioms.tsv`](logs/v7_witness_axioms.tsv) | Named witnesses, compile status, direct type dependencies, and axiom sets |
| [`logs/v7_bad_witness_compile.log`](logs/v7_bad_witness_compile.log) | Rejected `sorry` witness calibration |
| [`logs/v7_source_reference_counts.tsv`](logs/v7_source_reference_counts.tsv) and [`logs/v7_dead_code.tsv`](logs/v7_dead_code.tsv) | Complete source graph and zero-referrer list |
| [`logs/v7_dead_code_private.tsv`](logs/v7_dead_code_private.tsv) | Separate private zero-referrer rows |
| [`logs/v7_dead_code_calibration.log`](logs/v7_dead_code_calibration.log) and [`logs/v7_dead_code_calibration_status.log`](logs/v7_dead_code_calibration_status.log) | Planted unreferenced-definition hit and explicit statuses |

## Limitations

- The ≥3 rule uses direct constant occurrences in elaborated endpoint types,
  not transitive dependencies through other definitions. This is the declared
  selection rule, not a whole-program semantic slice.

- Citation selection and the judgment that a cited fact forces meaningful
  behavior are review-tier. The checker machine-verifies name resolution,
  direct dependency, source location, and axioms; it cannot decide
  mathematical meaningfulness.

- The 98 non-load-bearing candidates (84 public and 14 private) were
  enumerated and measured but were not individually subjected to the
  nondegeneracy review. This report guarantees the rule-defined 51-definition
  load-bearing set.

- The dead-code graph includes all 1,525 source declarations as nodes and
  referrers, but deliberately excludes compiler-generated/internal environment
  constants. Including generated equation and recursor artifacts would make
  the source-level “referenced by another declaration” question unstable and
  misleading.

- Zero direct repository referrers do not establish that a public declaration
  is useless: it may be a deliberate API leaf or be consumed by external code.
  V7-F1 therefore carries no remediation implication.

- Concrete witnesses establish nondegenerate behavior on audited models; they
  do not re-audit book faithfulness, which remains the responsibility of the
  TranslationReport and correspondence records.

- V7 does not establish that every proposition-valued interface is discharged
  by a source proof. A meaningful or verification-side-realizable predicate
  `P` can still appear only as the premise of a kernel-valid theorem `P → Q`;
  neither V7's load-bearing nondegeneracy test nor its direct dead-code graph
  classifies the publication and disclosure status of that conditionality;
  that broader coverage expansion is outside V7's guarantee.
