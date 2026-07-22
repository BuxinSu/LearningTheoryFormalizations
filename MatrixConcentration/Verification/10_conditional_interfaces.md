# V10 — Conditional-interface / undischarged-assumption census

**Verdict: PASS-WITH-NOTES**

**Tier: mixed (machine enumeration/classification and review adjudication)**

**Finding count: C=0 M=0 m=0 I=1**

> **Run-state note.** The deterministic fixed point below reflects the
> corrected source and a fresh V4/V10 identity reconciliation. The final fresh
> aggregate child and the subsequent standalone V10 runner both passed with
> identical source and verification-input digests. These are the current V10
> machine-census records. The independent final lifecycle checker also passed
> with zero problems, 14/14 final claims present, and every
> writer-lock/finalization-guard gate PASS.

## Guarantee

For the source snapshot pinned by `logs/source_manifest.txt`, the imported Lean
environment covers the same 15-module universe as the file walk. The corrected
environment contains 2,213 `(module, name, kind)` project constants, 1,531 of
which have source-backed declaration roles, while the independent textual
inventory contains 1,526 source declarations. The refreshed V4 identity set
equals those same 2,213 constants, not merely the same count.
Within that universe, an independent comment/string-aware scan agrees on
exactly 14 project `def`/`abbrev` declarations whose telescoped codomain is
`Prop`; their symmetric difference is empty. There are no project `structure`
or `class` declarations and therefore no project-defined proposition-valued
structure/class fields.

Every named predicate was classified by a least-fixed-point producer analysis
and every source consumer was enumerated. The unnamed dual emitted all 3,827
source-backed theorem proposition binders. Its 1,590 review-tier occurrences,
grouped into 368 persistent manual-obligation hashes, all have substantive
human adjudication: 359 routine explicit hypotheses and nine hypotheses
discharged by source callers. The persistent obligation register retains
those hashes while the uncurated queue is empty. Every source-level
`CONSUMED-ONLY` predicate was separately
checked for a concrete compiled instantiation, publication status, and
disclosure; absence of an instantiation is recorded rather than inferred
away.

The only principle-like never-discharged interfaces are the three
NC-Khintchine/bootstrap predicates in
`Appendix_RosenthalPinelis.lean`. Their consumers are unpublished internal
reductions; the source banner and the project records explicitly say that no
witness is supplied and that the literal centered exact form of Book display
(6.1.6), tracked as UP-007, is documented but not asserted. It is the sole
declared formal-coverage exception. The retained symmetric,
centered-with-loss, and integrable `_aux` results are support-only,
non-correspondence infrastructure and do not count as formal coverage of that
display. This honest conditional infrastructure is retained as the
known-ledgered informational observation V10-F1 and rejected as a new
soundness defect. No result presented as established was found to depend on an
undisclosed, never-discharged principle.

## Why V10 is separate

This failure mode leaves no kernel-level defect. A theorem of the form
`P → Q`, where `P` is a `def ... : Prop` for which the project never constructs
a proof, can be completely sorry-free, kernel-checked, and axiom-clean. V3's
placeholder/sorry scan and V4's axiom-dependency census are therefore
**structurally blind** to it: unlike `sorry`, the assumption leaves no
`sorryAx` in the declaration. V6 Tier B sees the pattern only when its consumer
happens to be among the 467 Book→Lean correspondence rows. V10 instead
enumerates proposition-valued interfaces and theorem proposition binders
directly, then reconciles them with publication and disclosure records.

## Scope

The textual side uses the common file-walk universe: every `.lean` file
physically under the project root, excluding exactly `.lake/**`,
`MatrixConcentration/Verification/**`, and `.audit_work/**`. On this tree that
is the 14 flat source modules plus root `MatrixConcentration.lean` (15 files),
with no in-universe symlinks. The environment and V4 module registers each
contain those same 15 module identities: the root plus all 14 leaf source
modules.

The named-predicate census includes:

1. every project `def` or `abbrev` whose type, after telescoping all binders
   and weak-head-normalizing the result, ends in `Prop`;
2. every project `structure`/`class` field whose corresponding field type is
   proposition-valued; and
3. independently, every textual `def ... : Prop` or `abbrev ... : Prop`
   declaration in the full file-walk universe, including multiline headers.

The unnamed dual covers every proposition-valued binder in every source-backed
project theorem in the imported environment. Definition-body dependencies are
also emitted separately so that a conditional premise embedded in a
proposition definition, notably
`ProvidesCenteredRosenthalBootstrap`, is not lost.

## Method

### Dual enumeration and cross-check

`scripts/v10_environment.lean` imports `MatrixConcentration` and records
declaration kind, source range, final target, theorem proposition binders,
definition-body dependencies, instance binders, structures/classes, and
proposition-valued fields. `scripts/v10_census.py` independently performs a
comment/string-aware multiline source scan over the full file-walk universe.
It normalizes both name sets and fails if either side has an unmatched
predicate. This specifically prevents an imported-environment census from
silently missing an orphan source file and prevents a line-oriented textual
regular expression from missing a multiline declaration.

### Exact environment coverage guard

The optimized environment emitter is accepted only after an identity-level
coverage reconciliation:

1. its 15-module list must exactly equal the file-walk module set;
2. the independently generated V4 module list must equal that same set;
3. all 2,213 environment constants must match all 2,213 V4 axiom-audit rows
   as an exact set of `(module, name, kind)` triples, with no blank or
   duplicate identity; and
4. the 1,531 source-backed declaration roles, 14 predicate rows,
   proposition-field rows, 3,827 proposition binders, and 4,762 instance
   binders must reconcile to their complete emitted inventories by identity,
   ownership, uniqueness, and the environment summary totals.

The resulting `ENVIRONMENT_COVERAGE_GUARD PASS` therefore rules out a faster
V10 walk silently dropping declarations that V4 audited. It does not merely
compare aggregate totals.

### Source instantiation status

For a predicate `P`, a source declaration is a producer candidate only when
its elaborated final conclusion has head `P`. A theorem is a consumer when a
proposition-valued domain binder depends on `P`; definition-body dependencies
are recorded as a separate consumer mode.

Producer status is computed as a least fixed point:

1. begin with no proved predicates;
2. add `P` only when some source-backed producer concludes `P` and every
   candidate-predicate premise of that producer is already in the proved set;
3. iterate until no status changes.

Consequently, a theorem that merely maps `P` to `P`, or a cycle
`P → Q` / `Q → P`, does not manufacture an instantiation. Final statuses are
`PROVED`, `CONSUMED-ONLY`, and `DEAD`. This is a source-library status. A
second, deliberately separate column records concrete verification-side
instantiations, so ordinary model predicates are not silently relabeled as
source-proved.

### Publication and disclosure adjudication

Every `CONSUMED-ONLY` source predicate was checked against:

- all 467 names in the Book→Lean correspondence table;
- claims in `MatrixConcentration/README.md` and
  `MatrixConcentration/APPENDIX_SUMMARY.md`;
- the in-source declaration/banners; and
- `TranslationReport/SOURCE_STATEMENT_ISSUES.md`.

The checker records both directions: every detected conditional item must map
to a disclosure, and every disclosed conditional item must be detected.
Ordinary explicit data/model hypotheses are distinguished from missing
mathematical principles by their declared semantics and by compiled,
axiom-audited concrete models. The existing V7 witnesses instantiate
`IsStdGaussian` and `IsBernoulli`; V10 adds the source-external zero-kernel
model `hasReproducingProperty_zero`. These witnesses establish consistency and
realizability, not source-level producer status.

### Unnamed inline assumptions

The environment harness emits every proposition-valued theorem binder after
elaboration, not merely binders whose surface text names one of the 14
predicates. The census groups those rows by normalized domain head and
dependency signature. Stable type hashes collapse whitespace, alpha-renumber
Lean's `_uniq N` local free-variable identifiers by first occurrence, erase
internal hygiene counters, and retain fully qualified generated-declaration
hashes.

Routing is fail-closed. A direct application of one of the 14 project
predicates goes to named-candidate curation; a Book-correspondence theorem
premise goes to the V6 467-row review; and an instance-implicit premise goes to
the explicitly limited typeclass inventory. Every other proposition binder
requires manual review, including formulas with an external/local head and
compound formulas that merely depend on a project predicate. Equality,
inequality, measurability, or integrability heads are not accepted as semantic
evidence by name alone.

The persistent obligation file records every type hash that ever takes the
manual route, whether already curated or not. The queue is only the
uncurated subset. Thus a zero-row queue cannot erase the 368-hash,
1,590-occurrence review scope, and stale curation hashes fail the census. The
machine inventory is exhaustive for source-backed imported theorem binders;
the judgment that a hypothesis is an ordinary local condition rather than a
missing theorem remains review-tier.

### Typeclass survey

The environment census independently asks Lean for every project structure
and class and inspects every field type, while also recording all
instance-implicit binders on source-backed theorems. The source has zero
project structures, zero project classes, and zero project-defined
proposition-valued fields. Thus there is no project-defined class whose
propositional obligation can hide the same pattern as the three named
interfaces. Imported Mathlib typeclasses and their use as instance binders are
present, but an instance-level search over all possible types and all possible
external downstream instantiations was not performed; that limitation is
stated explicitly below.

### Calibration

Calibration ran before accepting the production result:

- the production census found all three required built-in positives:
  `HermitianNCKhintchineAt`, `RectangularNCKhintchineAt`, and
  `ProvidesCenteredRosenthalBootstrap`;
- the same textual/binder machinery found `FakePrinciple` and its consumer
  `fake_result` in `.audit_work/ConditionalPlant.lean`; and
- the compiled plant also supplied a direct `FakePrinciple` binder, an
  external-headed equality binder, and a compound
  `FakePrinciple ∧ equality` binder; the shared router had to send these,
  respectively, to candidate reconciliation, mandatory manual review, and
  mandatory manual review; and
- that plant compiled with Lean, demonstrating the reason V3/V4 alone cannot
  reject a clean theorem whose premise is merely assumed.

The plant is excluded from the library file-walk universe and source manifest.
Failure to find any one of the three production positives, either planted
named role, or any of the three expected routing dispositions is a hard
failure in `v10_census.py`. The final calibration table has five rows and five
passes: three known conditionals, one planted predicate/consumer pair, and one
three-way inline-routing check.

### Compile and status gates

The runner appends a machine-readable `LEAN_EXIT_STATUS` marker to each Lean
compile log. The environment census, calibration plant, and V10 witness logs
each contain exactly one `LEAN_EXIT_STATUS 0`; the census also rejects a Lean
error or a “declaration uses sorry” warning in those logs. Ordinary linter
warnings in the planted or witness harness do not constitute compile failure.

The three human review chunks remain merged at 368 obligations, with 359
routine and nine caller-discharged rows and an empty queue. A corrected
environment/census extraction and refreshed V4 inventory measured the
deterministic totals in this report and reconciled all 2,213 identities
exactly.

The final standalone run
`4501a473-f8a5-49cc-93f7-6b57fe1e3fb3` ran from
`2026-07-20T18:30:27Z` to `2026-07-20T18:32:50Z` (143 seconds), recorded seven
`START` and seven `PASS` stages, reported zero census errors, and exited 0. Its
run-log SHA-256 is
`afcfaa944f9336545621fbeb99d9008a16182495f37a9a62aefc8c28b6199adb`.
Its initial and final gates agreed on source digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`
and verification-input digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
The separate terminal lifecycle checker reports `result=PASS`, zero problems,
14/14 final claims present, and all lock/guard gates PASS.

## Results

### Coverage summary

| Measurement | Result |
|---|---:|
| Files in textual file-walk universe | 15 |
| Environment / file-walk / V4 modules | 15 / 15 / 15 |
| Environment / V4 exact `(module, name, kind)` constants | 2,213 / 2,213 |
| Source-backed declaration roles | 1,531 |
| Textual source declarations parsed | 1,526 |
| Environment coverage guard | PASS |
| Environment `def`/`abbrev` predicates ending in `Prop` | 14 |
| Textual `def ... : Prop` / `abbrev ... : Prop` predicates | 14 |
| Environment-only / text-only predicates | 0 / 0 |
| Project `structure` / `class` declarations | 0 / 0 |
| Project proposition-valued structure/class fields | 0 |
| Source-status `PROVED` / `CONSUMED-ONLY` / `DEAD` | 7 / 6 / 1 |
| Producer rows / consumer binder-or-body occurrences | 46 / 287 |
| Distinct consumer declarations / predicate–consumer pairs | 225 / 227 |
| Source-backed theorem proposition binders | 3,827 |
| Stable normalized proposition-binder type hashes | 542 |
| Manual-review obligation hashes / occurrences | 368 / 1,590 |
| Manual curation `ROUTINE` / `DISCHARGED` | 359 / 9 |
| Remaining manual-review queue hashes | 0 |
| Theorem instance binders / distinct recorded heads | 4,762 / 22 |
| Instance binders with a project-defined head | 0 |
| Calibration rows passed | 5 / 5 |
| Production census errors / verdict | 0 / PASS |
| New undisclosed principle-like interfaces | 0 |
| Stale disclosures not found by the detector | 0 |

### Complete named-predicate classification

“Compiled instantiation” is intentionally separate from “source status.”
`SOURCE` means that the read-only library itself supplies a least-fixed-point
producer; `VERIFICATION` is a compiled, axiom-audited model outside the source
library.

| Predicate | Source location | Source status | Producer / instantiation evidence | Adjudication |
|---|---|---|---|---|
| `GaussPL` | `Appendix_GaussianConcentration.lean:761` | PROVED | SOURCE: `gaussPL_real`, then `gaussPL_pi_fin` and `gaussPL_pi` | Ordinary proved analytic predicate |
| `HermitianNCKhintchineAt` | `Appendix_RosenthalPinelis.lean:348` | CONSUMED-ONLY | none | Disclosed conditional principle; V10-F1 |
| `RectangularNCKhintchineAt` | `Appendix_RosenthalPinelis.lean:362` | CONSUMED-ONLY | `hermitian_nckhintchine_implies_rectangular` is conditional on the still-unproved Hermitian predicate and therefore does not enter the fixed point | Disclosed conditional principle; V10-F1 |
| `ProvidesCenteredRosenthalBootstrap` | `Appendix_RosenthalPinelis.lean:474` | CONSUMED-ONLY | none | Disclosed conditional principle; V10-F1 |
| `MIntegrable` | `Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2611` | PROVED | SOURCE: `MIntegrable.const`, `MIntegrable.of_bound`, and closure theorems | Ordinary integrability condition |
| `IsRademacher` | `Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2865` | PROVED | SOURCE: `boolSign_law` | Ordinary probability-law predicate |
| `IsStdGaussian` | `Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2881` | CONSUMED-ONLY | VERIFICATION: `MatrixConcentration.V7Witnesses.isStdGaussian_identity` | Explicit realizable probability-law input |
| `IsBernoulli` | `Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2902` | CONSUMED-ONLY | VERIFICATION: `MatrixConcentration.V7Witnesses.isBernoulli_identity`; the source representative theorem is self-dependent and does not enter the fixed point | Explicit realizable probability-law input |
| `IsSymmetricRV` | `Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2920` | PROVED | SOURCE: `ghostDiff_symmetric` | Ordinary proved probability-law predicate |
| `IsPosDefKernel` | `Chapter6_SumOfBoundedRandomMatrices.lean:4950` | DEAD | none; zero consumers | Already included in V7-F1's zero-referrer list |
| `HasReproducingProperty` | `Chapter6_SumOfBoundedRandomMatrices.lean:4956` | CONSUMED-ONLY | VERIFICATION: `MatrixConcentration.V10Witnesses.hasReproducingProperty_zero` | Explicit realizable random-feature model input |
| `OperatorMonotoneOn` | `Chapter8_ProofOfLiebsTheorem.lean:1273` | PROVED | SOURCE: `operatorMonotoneOn_affine`, `operatorMonotoneOn_neg_inv_shift`, `operatorMonotoneOn_log` | Ordinary proved operator predicate |
| `OperatorConvexOn` | `Chapter8_ProofOfLiebsTheorem.lean:1628` | PROVED | SOURCE: `operatorConvexOn_quadratic`, `operatorConvexOn_inv_shift`, `operatorConvexOn_entropyKernel` | Ordinary proved operator predicate |
| `OperatorConcaveOn` | `Chapter8_ProofOfLiebsTheorem.lean:1637` | PROVED | SOURCE: `operatorConcaveOn_log` | Ordinary proved operator predicate |

No proposition-valued `abbrev` was found. The single source `abbrev`,
`WignerIndex`, is not proposition-valued.

### Complete human-readable consumer register

The authoritative row-level register, including module, source range, binder
index/name, consumer mode, publication flags, and disclosure disposition, is
[`logs/v10_consumers.tsv`](logs/v10_consumers.tsv). It contains 287
predicate-consuming binder/body occurrences across 225 distinct source
declarations and 227 distinct predicate–consumer pairs. Repeated binders are
retained there—for example,
`GaussPL.prod` has two `GaussPL` premises—while the complete human-readable
lists below name each consuming declaration once:

- `GaussPL` (3 occurrences, 2 declarations): `GaussPL.prod` and
  `GaussPL.transfer`.

- `HermitianNCKhintchineAt` (1 occurrence/declaration):
  `hermitian_nckhintchine_implies_rectangular`.

- `RectangularNCKhintchineAt` (3 occurrences/declarations):
  `ProvidesCenteredRosenthalBootstrap` (definition-body premise),
  `matrix_rosenthal_pinelis_of_nck_and_bootstrap`, and
  `matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap`.

- `ProvidesCenteredRosenthalBootstrap` (2 occurrences/declarations):
  `matrix_rosenthal_pinelis_of_nck_and_bootstrap` and
  `matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap`.

- `MIntegrable` (153 occurrences, 99 declarations):
  `MIntegrable.add`, `MIntegrable.centered_mul_conjTranspose`,
  `MIntegrable.centered_sq`, `MIntegrable.congr_ae`,
  `MIntegrable.conjTranspose`,
  `MIntegrable.conjTranspose_mul_centered`, `MIntegrable.const_mul`,
  `MIntegrable.finsetSum`, `MIntegrable.mul_const`,
  `MIntegrable.mul_of_indepFun`, `MIntegrable.neg`,
  `MIntegrable.smul_complex`, `MIntegrable.smul_real`, `MIntegrable.sub`,
  `bernstein_L_nonneg_one_sided`,
  `bernstein_cgf_trace_bound_one_sided`,
  `bernstein_expected_trace_bound_one_sided`,
  `bernstein_matrix_cgf_le_one_sided`,
  `bernstein_matrix_cgf_le_one_sided_ae`,
  `bernstein_matrix_mgf_le_one_sided`,
  `bernstein_matrix_mgf_le_one_sided_ae`,
  `bernstein_trace_mgf_bound_one_sided`,
  `bernstein_trace_mgf_bound_one_sided_pointwise`,
  `centered_second_moment_le`, `centered_second_moment_le₂`,
  `chernoff_mu_max_eq`, `chernoff_mu_min_eq`, `expectation_add`,
  `expectation_centered`, `expectation_comp_fst`,
  `expectation_comp_snd`, `expectation_const_mul`,
  `expectation_finsetSum`, `expectation_lambdaMin_le`,
  `expectation_loewner_mono`, `expectation_matsum_eq`,
  `expectation_mul_const`, `expectation_mul_of_indepFun`,
  `expectation_one_add_smul`, `expectation_one_add_smul_add_smul_sq`,
  `expectation_sampleCovariance`, `expectation_sub`,
  `expectation_sum_mul_conjTranspose_of_centered`,
  `expectation_sum_mul_sum`, `expectation_trace`,
  `ghostDiff_colVariance`, `ghostDiff_rowVariance`,
  `intdim_bernstein_herm_tail_core_one_sided`,
  `intdim_bernstein_herm_tail_one_sided`,
  `intdim_laplace_psiTwo_one_sided`,
  `integrable_l2_opNorm_of_mintegrable`,
  `integrable_matrix_of_mintegrable`, `integrable_star_dotProduct`,
  `integrable_trace_re_of_mintegrable`,
  `integral_lambdaMax_eq_zero_of_card_one_one_sided`,
  `integral_trace_re_eq_zero_of_mintegrable`,
  `isHermitian_sampleCovSummand`, `lambdaMax_expectation_le`,
  `lambdaMax_symmetrization_ghost`,
  `master_expectation_upper_one_sided`, `master_tail_upper_one_sided`,
  `matrixVar1_eq_sub`, `matrixVar1_sum`, `matrixVar2_eq_sub`,
  `matrixVar2_sum`, `matrixVar_eq_sub`, `matrixVar_sum`,
  `matrix_bernstein_herm_expectation_one_sided`,
  `matrix_bernstein_herm_expectation_one_sided_ae`,
  `matrix_bernstein_herm_min_expectation_one_sided`,
  `matrix_bernstein_herm_min_expectation_one_sided_ae`,
  `matrix_bernstein_herm_min_tail_one_sided`,
  `matrix_bernstein_herm_min_tail_one_sided_ae`,
  `matrix_bernstein_herm_tail_one_sided`,
  `matrix_bernstein_herm_tail_one_sided_ae`,
  `matrix_bernstein_variance_eq`, `matrix_rosenthal`,
  `matrix_rosenthal_aux`, `norm_expectation_le`,
  `posSemidef_covarianceMatrix`, `posSemidef_expectation`,
  `posSemidef_matrixVar`, `posSemidef_matrixVar1`,
  `posSemidef_matrixVar2`, `rayleigh_matrixVar`,
  `sampleCov_norm_sum_sq_le`, `sampleCov_sum_sq_le`,
  `sampleCov_summand_centered`, `sampleCov_varStat_eq`,
  `sampleCovariance_expected_error`, `sampleCovariance_relative_error`,
  `star_dotProduct_expectation`, `sum_varStatHerm_le_card_mul`,
  `varStatHerm_eq_lambdaMax`, `varStatHerm_eq_sup_variance`,
  `varStatHerm_sum`, `varStatHerm_sum_le`,
  `varStatHerm_sum_of_identDistrib`, and `varStat_sum`.

- `IsRademacher` (33 occurrences/declarations):
  `ae_range_isRademacher`, `iIndepFun_rademacherRepresentative`,
  `integrable_isRademacher`, `integral_id_isRademacher`,
  `integral_isRademacher`, `integral_sq_isRademacher`,
  `isRademacher_rademacherRepresentative`, `maxqp_rounding_bound`,
  `maxqp_rounding_bound_of_isRademacher`, `maxqp_rounding_bound_one`,
  `maxqp_rounding_bound_one_of_isRademacher`,
  `posDef_rademacher_mgf`, `rademacherRepresentative_ae_eq`,
  `rademacherRepresentative_matsum_ae`, `rademacher_cgf_trace_bound`,
  `rademacher_herm_expectation`,
  `rademacher_herm_expectation_of_isRademacher`,
  `rademacher_herm_min_expectation`,
  `rademacher_herm_min_expectation_of_isRademacher`,
  `rademacher_herm_min_tail`,
  `rademacher_herm_min_tail_of_isRademacher`,
  `rademacher_herm_tail`, `rademacher_herm_tail_of_isRademacher`,
  `rademacher_matrix_cgf_le`, `rademacher_matrix_mgf`,
  `rademacher_matrix_mgf_le`, `rademacher_series_rect_expectation`,
  `rademacher_series_rect_expectation_of_isRademacher`,
  `rademacher_series_rect_tail`,
  `rademacher_series_rect_tail_of_isRademacher`,
  `rademacher_series_second_moment`, `signed_expected_norm`, and
  `signed_expected_norm_of_isRademacher`.

- `IsStdGaussian` (29 occurrences/declarations): `gauss_concentration`,
  `gauss_expect_sq_lower`,
  `gauss_expect_sq_upper`, `gauss_quadform_second_moment`,
  `gaussianRect_expected_norm`, `gaussian_cgf_trace_bound`,
  `gaussian_family_expc`, `gaussian_herm_expectation`,
  `gaussian_herm_min_expectation`, `gaussian_herm_min_tail`,
  `gaussian_herm_tail`, `gaussian_matrix_cgf`, `gaussian_matrix_mgf`,
  `gaussian_series_rect_expectation`, `gaussian_series_rect_tail`,
  `gaussian_series_second_moment`, `integrable_exp_abs_isStdGaussian`,
  `integrable_exp_mul_isStdGaussian`, `integrable_norm_sq_gauss_series`,
  `integrable_sq_isStdGaussian`, `integral_exp_mul_isStdGaussian`,
  `integral_isStdGaussian`, `integral_sq_isStdGaussian`,
  `mgf_isStdGaussian_mul`, `scalar_gauss_series_tail`,
  `scalar_gauss_series_tail_upper`, `scalar_gauss_series_variance`,
  `toeplitz_expected_norm`, and `wigner_expected_norm`.

- `IsBernoulli` (36 occurrences, 33 declarations): `ae_range_isBernoulli`,
  `bernoulliRepresentative_ae_eq`, `bernoulliRepresentative_all_ae`,
  `bernoulli_diagonal_example`, `column_submatrix_lower`,
  `column_submatrix_lower_of_isBernoulli`, `column_submatrix_upper`,
  `column_submatrix_upper_of_isBernoulli`, `conditional_column_bound`,
  `conditional_column_bound_of_isBernoulli`,
  `conditional_column_bound_pointwise`,
  `conditional_column_bound_pointwise_of_isBernoulli`,
  `entryDiag_sum_expectation`, `er_compression_tail`,
  `er_compression_tail_of_isBernoulli`, `er_second_smallest_tail`,
  `er_second_smallest_tail_of_isBernoulli`, `expectation_column_gram`,
  `expectation_erY_eq`, `iIndepFun_bernoulliRepresentative`,
  `intdim_column_submatrix_upper`,
  `intdim_column_submatrix_upper_of_isBernoulli`,
  `intdim_column_submatrix_upper_totalized`, `integrable_isBernoulli`,
  `integral_id_isBernoulli`, `integral_isBernoulli`,
  `isBernoulli_bernoulliRepresentative`, `max_column_norm_bound`,
  `max_column_norm_bound_of_isBernoulli`, `row_column_submatrix_norm`,
  `row_column_submatrix_norm_of_isBernoulli`,
  `row_sampling_gram_bound`, and
  `row_sampling_gram_bound_of_isBernoulli`.

- `HasReproducingProperty` (1 occurrence/declaration):
  `kernelMatrix_eq_expectation_outer`.

- `IsSymmetricRV` (16 occurrences/declarations):
  `expectation_eq_zero_of_isSymmetricRV`,
  `integral_signFlip_eq_of_symmetric`,
  `matrix_rosenthal_pinelis_symmetric`,
  `matrix_rosenthal_pinelis_symmetric_aux`,
  `matrix_rosenthal_pinelis_symmetric_integrable_aux`,
  `matrix_rosenthal_pinelis_symmetric_of_large_squared_bound`,
  `symmetric_expect_sq_le_square_function`,
  `symmetric_expect_sq_le_square_function_integrable`,
  `symmetric_large_squared_bound`,
  `symmetric_large_squared_bound_integrable`, `symmetric_sum_lower_bound`,
  `symmetric_sum_lower_bound_aux`, `symmetric_sum_lower_bound_integrable`,
  `symmetric_sum_lower_bound_strong`,
  `symmetric_sum_lower_bound_strong_integrable`, and
  `symmetric_sum_lower_bound_strong_of_nonempty`.

- `IsPosDefKernel`: no consumers.

- `OperatorMonotoneOn` (3 occurrences, 2 declarations):
  `operatorMonotoneOn_add` and `operatorMonotoneOn_smul`.

- `OperatorConvexOn` (7 occurrences, 6 declarations):
  `OperatorConcaveOn` (definition-body dependency),
  `OperatorConvexOn.mono`, `matrixPerspective_operator_convex`,
  `operatorConvexOn_add`, `operatorConvexOn_smul`, and `operator_jensen`.

- `OperatorConcaveOn`: no consumers.

The three predicates grouped in V10-F1 are the only never-instantiated
principle-like interfaces. The other source-level `CONSUMED-ONLY` predicates
(`IsStdGaussian`, `IsBernoulli`, and `HasReproducingProperty`) state ordinary
data/model conditions explicitly in their consumers. Their concrete
verification models compile without `sorryAx` or nonstandard axioms, so they
are not assumptions in disguise.

### Published-consumer and ledger reconciliation

The three V10-F1 predicates and all four conditional reduction roles
(`hermitian_nckhintchine_implies_rectangular`, the definition-body premise in
`ProvidesCenteredRosenthalBootstrap`, and the two
`matrix_rosenthal_pinelis_of_*_and_bootstrap` theorems) are absent from the
467-row correspondence table. They are internal conditional reductions, not
formal coverage of UP-007.

The conditionality is disclosed in all required places:

| Detector item | In-source disclosure | Record disclosure | Publication result |
|---|---|---|---|
| Three NC-Khintchine/bootstrap predicates | `Appendix_RosenthalPinelis.lean` “Conditional-only infrastructure” banner: no witness is asserted; retained results are support-only | `TranslationReport/SOURCE_STATEMENT_ISSUES.md` says the predicates are not instantiated; `APPENDIX_SUMMARY.md` calls the reductions internal infrastructure | Consumers absent from 467-row table; INFO |
| Literal centered exact (6.1.6) display / UP-007 | Conditional reductions retain the premises explicitly; the incorrect public coverage aliases were deleted | Project records identify (6.1.6) as documented but not asserted and as the sole declared coverage exception | No theorem is claimed as formal coverage of the literal display; no stale ledger item |
| Retained symmetric, centered-with-loss, and integrable `_aux` results | Independently proved bounded/support statements with their own hypotheses and conclusions | Source and appendix records label them support-only | Deliberately absent from the 467-row correspondence table; they are not substitute coverage endpoints |

The reconciliation is bidirectional: every detector-positive conditional
principle maps to the same ledger item, and the one disclosed conditional
source item maps back to those three predicates. There are zero new
undisclosed items and zero stale disclosures.

`IsStdGaussian`, `IsBernoulli`, and `HasReproducingProperty` do occur in
published declarations, but their consumers state the corresponding
distribution/model conditions explicitly; the correspondence table also
registers the predicate definitions themselves. Their compiled models
demonstrate that these are satisfiable input conditions, not unavailable
theorems that the library presents as proved.

### Unnamed and typeclass-mediated assumptions

The complete proposition-binder inventory is
[`logs/v10_prop_binders.tsv`](logs/v10_prop_binders.tsv); its normalized
review/adjudication is
[`logs/v10_inline_assumptions.tsv`](logs/v10_inline_assumptions.tsv).

The six routing categories are mutually exclusive at the occurrence level and
sum to all 3,827 proposition binders:

| Category | Occurrences | Manual-obligation hashes | Disposition |
|---|---:|---:|---|
| Anonymous inline premise | 496 | 101 | Manual semantic adjudication |
| Compound project-predicate premise | 69 | 18 | Manual semantic adjudication |
| External/local named predicate | 1,025 | 249 | Manual semantic adjudication |
| Instance-mediated premise | 584 | — | Enumerated under the typeclass limitation |
| Direct named project predicate | 129 | — | Reconciled with the 14-row candidate curation |
| Published-endpoint inline premise | 1,524 | — | Cross-linked to V6 Tier B |

The external/local category contains 34 distinct domain heads and 249 stable
type hashes. All were manually reviewed; a familiar name such as `Eq`,
`LE.le`, `Measurable`, `Integrable`, `IsHermitian`, or `iIndepFun` did not
short-circuit review. The 18 compound hashes depend only on ordinary
`MIntegrable`, `IsSymmetricRV`, `IsBernoulli`, `IsRademacher`, or
`IsStdGaussian` model/regularity conditions. None packages an NC-Khintchine or
Rosenthal-bootstrap principle; direct occurrences of those predicates are
handled by the named census and V10-F1.

The initial anonymous-inline baseline comprised 101 hashes and 496
occurrences. Tightening the router to require review for external-headed and
compound formulas added 267 hashes and 1,094 occurrences. Those 267 hashes
were divided into three disjoint human-review chunks of 89 hashes. For every
hash the reviewers inspected all matching occurrence rows and the relevant
source declarations or call sites. The merge checker accepted the original
101 rows plus all 267 chunk rows as exactly the 368 persistent obligations,
recorded zero finding-labelled rows and a merged content digest, and then
applied that content to
[`curation/v10_inline_adjudication.tsv`](curation/v10_inline_adjudication.tsv).

Final curation contains 359 `ROUTINE_EXPLICIT_HYPOTHESIS` rows and nine
`DISCHARGED_BY_SOURCE_CALLER` rows. Every row has a substantive evidence field
and reviewer note. The persistent register
[`logs/v10_inline_review_obligations.tsv`](logs/v10_inline_review_obligations.tsv)
still contains all 368 hashes; the header-only
[`logs/v10_inline_review_queue.tsv`](logs/v10_inline_review_queue.tsv)
contains zero uncurated hashes. No principle-like assumption was found among
the 1,590 manually adjudicated occurrences.

Representative high-risk shapes were resolved as follows; the curation TSV is
the row-level evidence for all 368 hashes:

| Inline shape | Adjudication |
|---|---|
| `hlarge` in the large-dimension Rosenthal helper | Discharged by `symmetric_large_squared_bound` in the caller at `Appendix_RosenthalPinelis.lean:2305` |
| Low- and large-dimension final scalar inequalities | Callers derive them from the proved centered-sum, squared-bound, and coefficient lemmas; these account for several of the nine `DISCHARGED_BY_SOURCE_CALLER` rows |
| `sharp_khintchine_constant_is_sufficient` scalar premises | The specialization equation is supplied by `rfl`, and the numeric bound is derived from the explicit caller premise; the named conditional NC/bootstrap predicates remain separately disclosed in V10-F1 |
| `rosenthal_scalar_algebra` master inequality | Supplied as the locally proved `hmaster` at `Appendix_MatrixRosenthal.lean:1163` |
| `hmgfpd` in matrix-log/MGF helpers | Explicit positive-definiteness regularity; concrete Gaussian callers supply it, not an assumed concentration conclusion |
| Prékopa–Leindler `hcond` | Standard pointwise domination premise; the Gaussian caller supplies the proof |
| `GaussPL.transfer` compatibility premises `hcomb` / `hcost` | Structural equations for transporting an already supplied `GaussPL` proof |
| Rosenthal/Chernoff `hmin` families | Explicit positive-semidefinite or eigenvalue-bound inputs; relevant callers use proved square-PSD facts |
| Quantified Bernoulli/Rademacher/Gaussian and symmetry conditions | Explicit stochastic model hypotheses, with realizability or producers checked in the named-predicate census |

The project structure/class field inventory
[`logs/v10_environment_prop_fields.tsv`](logs/v10_environment_prop_fields.tsv)
contains only its header. The complete imported-class use at theorem
interfaces is recorded in
[`logs/v10_instance_binders.tsv`](logs/v10_instance_binders.tsv): 4,762
instance-binder rows, 22 recorded domain heads, and zero rows with a
project-defined head. This proves there is no project-defined class/field
analogue of the named conditional pattern; it does not claim a global semantic
audit of every possible Mathlib instance.

### Cross-check with V7

`IsPosDefKernel` has no producer and no consumer, so V10 classifies it
`DEAD`. It is already one of the three definition-kind zero-referrer rows in
V7-F1. V10 does not create a second finding for the same observation: the
classification here confirms the cross-report fixed point and points to
V7-F1 as the finding of record.

## Findings

### V10-F1 — INFO — KNOWN-LEDGERED; rejected as a new soundness defect

**Severity: INFO**

`HermitianNCKhintchineAt`, `RectangularNCKhintchineAt`, and
`ProvidesCenteredRosenthalBootstrap` have no unconditional source producer.
They are consumed only by internal conditional reductions absent from the
467-row correspondence table. The source banner, the source-statement-issues
ledger, and `APPENDIX_SUMMARY.md` explicitly disclose that no witness is
provided and that the literal centered exact (6.1.6) display is documented but
not asserted. UP-007/(6.1.6) is the sole declared formal-coverage exception.
The retained symmetric, centered-with-loss, and integrable `_aux` theorems are
support-only, non-correspondence results and are not substitutes for the
literal display. This is honest conditional infrastructure and requires no
additional remediation. In accordance with the re-certification scope, this
observation is **REJECTED as a new/open soundness defect** because it
re-reports the now-explicit, KNOWN-LEDGERED UP-007/NC-Khintchine limitation.
It is an additional V10 INFO observation and is not folded into the original
five-item Round-1 disposition totals.

## Exact re-run commands

From the Lake project root:

```sh
bash MatrixConcentration/Verification/scripts/v10_run.sh
```

A standalone invocation acquires the shared verification-writer lock
automatically. When stage 21 is nested under `run_all.sh`,
`VERIFICATION_OUTER_LOCK_HELD=1` reuses the orchestrator's lock rather than
acquiring a second one.

The runner executes the following fail-closed sequence:

```sh
python3 MatrixConcentration/Verification/scripts/verification_input_manifest.py check
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/make_calibration_plants.py
~/.elan/bin/lake env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
  .audit_work/ConditionalPlant.lean
~/.elan/bin/lake env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/v10_environment.lean
~/.elan/bin/lake env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/witnesses/V10Witnesses.lean
python3 MatrixConcentration/Verification/scripts/v10_census.py
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/verification_input_manifest.py check
```

The actual shell runner performs the initial and final verification-input
checks through `verification_load_input_digest`, retaining the initial digest
and rejecting any final mismatch.

`lake env lean` does not inherit the lakefile's `leanOptions`; the two
library-adjacent caveat flags are therefore explicit. The lakefile linter set
is not active in these single-file harness compilations. V8 separately runs
the package linter.

The same runner is numbered verification stage 21 in the full
re-certification command; the orchestrator then performs the final V2 scratch
refresh, ten-report consistency check, and source- and
verification-input-manifest stability gates:

```sh
bash MatrixConcentration/Verification/scripts/run_all.sh --fresh
```

The required final order is recovery-v7 establishment/validation, fresh
aggregate (including nested V10), standalone V6, standalone V7, standalone
V10, consistency refresh, and lifecycle gate:

```sh
bash MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh
bash MatrixConcentration/Verification/scripts/run_all.sh --fresh
bash MatrixConcentration/Verification/scripts/v6_run.sh
bash MatrixConcentration/Verification/scripts/v7_run.sh
bash MatrixConcentration/Verification/scripts/v10_run.sh
python3 MatrixConcentration/Verification/scripts/check_consistency.py
python3 MatrixConcentration/Verification/scripts/check_final_lifecycle.py
```

## Raw evidence

| Evidence | Purpose |
|---|---|
| [`logs/v10_summary.txt`](logs/v10_summary.txt) and [`logs/v10_summary.json`](logs/v10_summary.json) | Corrected development fixed-point census: coverage guard PASS, errors 0, verdict PASS, and the machine-readable totals in this report |
| [`logs/v10_postreview_census.log`](logs/v10_postreview_census.log) | Retained pre-correction post-review chronology; not used for the corrected counts |
| [`logs/v10_run.aggregate.log`](logs/v10_run.aggregate.log) and [`logs/v10_run_status.aggregate.log`](logs/v10_run_status.aggregate.log) | Final fresh-aggregate child: run `526b6a99-c0de-4319-96e8-24e798bb1b9f`, parent `8212cc84-aad8-4abc-b0df-b68fd3241112`, PASS in 278 seconds, log SHA-256 `4fc285259fbae52eedebc4b741e0bbed18d6cc9cbbee0c2560ec5f07bc5e0fdc` |
| [`logs/v10_run.log`](logs/v10_run.log) and [`logs/v10_run_status.log`](logs/v10_run_status.log) | Final standalone: run `4501a473-f8a5-49cc-93f7-6b57fe1e3fb3`, parent `standalone`, seven of seven stages PASS in 143 seconds, log SHA-256 `afcfaa944f9336545621fbeb99d9008a16182495f37a9a62aefc8c28b6199adb` |
| [`logs/v10_manifest_check.log`](logs/v10_manifest_check.log) and [`logs/v10_final_manifest_check.log`](logs/v10_final_manifest_check.log) | Stable initial/final source and verification-input manifest measurements for the standalone PASS |
| [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) | Independent terminal lifecycle/report gate: zero problems, `result=PASS`, 14/14 final claims present, and every writer-lock/finalization-guard gate PASS |
| [`logs/v10_environment_compile.log`](logs/v10_environment_compile.log), [`logs/v10_conditional_calibration_compile.log`](logs/v10_conditional_calibration_compile.log), and [`logs/v10_witnesses_compile.log`](logs/v10_witnesses_compile.log) | Lean compile logs with exactly one `LEAN_EXIT_STATUS 0` marker each |
| [`logs/v10_modules.txt`](logs/v10_modules.txt), [`logs/v10_environment_constants.tsv`](logs/v10_environment_constants.tsv), and [`logs/v10_environment_summary.txt`](logs/v10_environment_summary.txt) | Fifteen-module corrected environment inventory, 2,213 constant identities, 1,531 source-backed roles, and emitted totals |
| [`logs/axiom_modules.txt`](logs/axiom_modules.txt), [`logs/axiom_audit.tsv`](logs/axiom_audit.tsv), and [`logs/axiom_summary.json`](logs/axiom_summary.json) | Refreshed independent V4 identity side: exactly the same 2,213 `(module, name, kind)` constants as V10 |
| [`logs/v10_environment_predicates.tsv`](logs/v10_environment_predicates.tsv) and [`logs/v10_text_predicates.tsv`](logs/v10_text_predicates.tsv) | Independent predicate enumerations |
| [`logs/v10_environment_text_diff.tsv`](logs/v10_environment_text_diff.tsv) | Empty environment/text symmetric difference |
| [`logs/v10_declaration_roles.tsv`](logs/v10_declaration_roles.tsv), [`logs/v10_prop_binders.tsv`](logs/v10_prop_binders.tsv), and [`logs/v10_instance_binders.tsv`](logs/v10_instance_binders.tsv) | Complete elaborated role and binder inventories |
| [`logs/v10_producers.tsv`](logs/v10_producers.tsv), [`logs/v10_consumers.tsv`](logs/v10_consumers.tsv), and [`logs/v10_status.tsv`](logs/v10_status.tsv) | Producer graph, every consumer, fixed-point status, and adjudication |
| [`curation/v10_adjudication.tsv`](curation/v10_adjudication.tsv) and [`logs/v10_disclosure_reconciliation.tsv`](logs/v10_disclosure_reconciliation.tsv) | Checked per-predicate semantic/publication adjudication and its machine reconciliation |
| [`logs/v10_inline_assumptions.tsv`](logs/v10_inline_assumptions.tsv), [`logs/v10_inline_type_groups.tsv`](logs/v10_inline_type_groups.tsv), and [`logs/v10_inline_summary.txt`](logs/v10_inline_summary.txt) | Exhaustive proposition-binder inventory, stable type grouping, and totals |
| [`logs/v10_inline_review_obligations.tsv`](logs/v10_inline_review_obligations.tsv), [`curation/v10_inline_adjudication.tsv`](curation/v10_inline_adjudication.tsv), and [`logs/v10_inline_review_queue.tsv`](logs/v10_inline_review_queue.tsv) | Persistent 368-hash obligation register, complete 359/9 curation, and empty uncurated queue |
| [`logs/v10_curation_quality_review.md`](logs/v10_curation_quality_review.md) | Independent 49-row stratified quality audit covering all nine caller-discharged hashes and all 18 compound-project-predicate hashes, with no escalation; SHA-256 `86ab9eb095e251e767eb776928e127bc1898e81347e7fb20b51b9a8c2f5897b6` |
| [`logs/v10_inline_merge_check.log`](logs/v10_inline_merge_check.log) and [`logs/v10_inline_merge_apply.log`](logs/v10_inline_merge_apply.log) | Three-chunk review merge validation and application: 101 base plus 267 new rows, 368 total, zero finding rows |
| [`logs/v10_environment_prop_fields.tsv`](logs/v10_environment_prop_fields.tsv), [`logs/v10_prop_field_coverage.tsv`](logs/v10_prop_field_coverage.tsv), [`logs/v10_typeclasses.tsv`](logs/v10_typeclasses.tsv), and [`logs/v10_typeclass_summary.txt`](logs/v10_typeclass_summary.txt) | Project structure/class proposition fields and instance-binder coverage |
| [`logs/v10_calibration.tsv`](logs/v10_calibration.tsv) and [`logs/v10_inline_calibration_binders.tsv`](logs/v10_inline_calibration_binders.tsv) | Five-of-five known-conditional, planted-pair, and direct/external/compound routing calibration |
| [`scripts/witnesses/V10Witnesses.lean`](scripts/witnesses/V10Witnesses.lean), [`logs/v10_witnesses_compile.log`](logs/v10_witnesses_compile.log), and [`logs/v10_witness_axioms.tsv`](logs/v10_witness_axioms.tsv) | Concrete `HasReproducingProperty` model and axiom audit |
| [`logs/v7_witness_axioms.tsv`](logs/v7_witness_axioms.tsv) | Existing compiled Gaussian/Bernoulli model evidence |

## Limitations

- The named census detects `def`/`abbrev` predicates and
  proposition-valued project structure/class fields. The inline dual covers
  proposition-valued binders of source-backed imported theorems. Thus it
  directly exposes the relevant explicit `P → Q` interfaces, but it does not
  attempt unrestricted semantic theorem discovery from arbitrary expressions
  in proof bodies, non-propositional data encodings, or future downstream
  declarations outside the source universe.

- Least-fixed-point status answers whether the source library constructs the
  predicate. It does not judge whether a discharged predicate's proof is
  mathematically meaningful or nonvacuous; V6 is the check for that question.

- Publication/disclosure and the distinction between an ordinary explicit
  model hypothesis and an unavailable mathematical principle are
  review-tier judgments. The machine side makes the inventory, producer graph,
  consumer lists, and publication-name intersections reproducible, but Lean
  cannot infer the intended expository role.

- The inline inventory is syntactically exhaustive for source-backed project
  theorem binders after elaboration. It cannot prove, for every possible
  proposition, that a premise is philosophically “routine”; that final
  classification is the declared review portion of this mixed-tier report.
  The 368 manual rows cover every residual type hash requiring semantic
  adjudication. Project-named predicates use the 14-row adjudication,
  published endpoint premises cross-link to V6, and instance binders use the
  typeclass limitation. External/local named and anonymous formulas receive
  the same manual review; their domain heads alone are never treated as proof
  of instantiation.

- The typeclass survey proves that this project declares no
  structures/classes or proposition-valued fields and records every
  instance-implicit binder on its source-backed theorems: 4,762 rows with 22
  recorded heads, including 584 proposition binders routed as
  instance-mediated. It does not semantically prove instance availability for
  every possible type in imported Mathlib or for future external downstream
  code.

- Concrete verification witnesses show that `IsStdGaussian`, `IsBernoulli`,
  and `HasReproducingProperty` are realizable without `sorryAx` or
  nonstandard axioms. They do not change the accurate source status
  `CONSUMED-ONLY` and do not re-audit the book-faithfulness of statements.

- The correspondence table and TranslationReport records are used here only
  to classify publication and disclosure. Their statement-faithfulness audit
  remains outside this mechanical-soundness pass.
