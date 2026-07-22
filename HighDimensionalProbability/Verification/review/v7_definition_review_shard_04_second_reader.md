# V7 Definition Review — Shard 04 Independent Second-Reader Audit

- Reviewer: Codex, independent V7 shard-4 second reader
- Review date: 2026-07-18
- Result: **PASS — no objection to any of the 26 promoted citations**

> **Historical evidence boundary.** This Pass 06 second-reader record covers
> the original 75-row shard-4 split of 26 `VERIFIED_CITATION` and 49
> `UNVERIFIED_SANITY` rows. It does not second-read the 36 additional
> promotions made during the later Pass 07 reconstruction. The current
> 62/13 shard-4 split and its aggregate provenance are recorded in
> `../07_definition_sanity.md`; this document supports only the 26 promotions
> listed below.

## Scope

This is a read-only semantic audit of the 26 rows then marked
`VERIFIED_CITATION` in
`v7_definition_review_shard_04.tsv`.  The review covered the complete
historical 75-row shard-4 packet, with particular attention to rows 38–75, and checked
the final promoted rows against `V7_DEFINITION_REVIEW_PROTOCOL.md`, the
packet candidate records, and the cited Lean source declarations.

This audit did not modify the shard TSV or the aggregate report. It also did
not promote any of the 49 rows that remained `UNVERIFIED_SANITY` at that
historical stage.

## Method and acceptance checks

For each promoted row, the second reader checked all of the following:

1. The evidence name occurs in that definition's own packet candidate list.
2. Candidate resolution is `exact`; no fuzzy, generated-owner,
   named-instance, or private-owner resolution is used.
3. The resolved physical declaration is a theorem at the recorded source
   location and is admissible as a V4 theorem candidate.
4. The packet's resolved axiom set and the TSV agree exactly.  Every promoted
   theorem records
   `propext;Classical.choice;Quot.sound`, with no disallowed axiom.
5. The theorem statement, instantiated on a concrete finite/scalar/Gaussian
   model as appropriate, excludes the relevant zero, constant, or
   data-forgetting implementation.
6. Empty-index, zero-sample, division, supremum/maximum, measure, and
   typeclass boundaries were checked wherever they occur.  A boundary case
   was not used as the sole evidence for a nondegenerate claim.

## Accepted definition/evidence pairs

All locations below were resolved physically and exactly.  The V4 axiom set
for every row is `propext;Classical.choice;Quot.sound`.

| # | Definition | Accepted theorem evidence | Physical location | Concrete collapse exclusion and boundary check |
|---:|---|---|---|---|
| 1 | `HDP.Chapter4.gramExpectationConstant` | `HDP.Chapter4.gramExpectationConstant_pos` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:12858` | Strict positivity directly excludes the zero or a negative placeholder.  This is a closed scalar, so there is no empty, division, measure, or typeclass boundary. |
| 2 | `HDP.Chapter4.leadingEigenSubspace` | `HDP.Chapter4.finrank_leadingEigenSubspace` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:794` | The exact formula `finrank = k + 1` gives rank one for the one-dimensional `k = 0` model and varying ranks as `k` varies, excluding both the zero subspace and a `k`-independent constant subspace.  `k : Fin n` makes the `n = 0` case uninhabited. |
| 3 | `HDP.Chapter4.matrixLpToLpNorm` | `HDP.Chapter4.exercise_4_18b_matrixLpToLpNorm` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:1531` | Triangle inequality, exact homogeneity, and `norm A = 0 ↔ A = 0` exclude zero and nonzero constant functionals; singleton matrices `[0]` and `[1]` are concrete witnesses.  The hypotheses `1 ≤ p,q` are explicit, and empty matrix shapes are extensionally zero rather than false positive models. |
| 4 | `HDP.Chapter4.maxAbsEntry` | `HDP.Chapter4.exists_entry_eq_maxAbsEntry` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:1582` | Attainment forces values zero and one on singleton matrices `[0]` and `[1]`, excluding zero and globally constant functionals.  Nonempty row and column hypotheses remove empty-maximum ambiguity. |
| 5 | `HDP.Chapter4.maxRowL2Norm` | `HDP.Chapter4.exists_row_eq_maxRowL2Norm` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:1832` | Attainment gives values zero and one on singleton matrices `[0]` and `[1]`, excluding zero and constant row-norm functionals.  The row type is explicitly nonempty; an empty column type legitimately gives zero row norms. |
| 6 | `HDP.Chapter4.outerMatrix` | `HDP.Chapter4.exercise_4_3a_outer_norms` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:1428` | The exact operator- and Frobenius-norm identities yield norm one for one-dimensional `u = v = 1` and zero when `u = 0`, excluding zero and constant constructors.  Zero-dimensional inputs legitimately have zero vector and output norms. |
| 7 | `HDP.Chapter4.sampleCovarianceMatrix` | `HDP.Chapter4.sampleCovarianceMatrix_apply` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:13814` | The exact entry formula gives one for the singleton sample `X 0 = 1` and zero for `X 0 = 0`, excluding zero and constant matrices.  At sample size zero the inverse and empty sum give the intended zero boundary; the positive model uses sample size one. |
| 8 | `HDP.Chapter4.sbmNoise` | `HDP.Chapter4.sbmNoise_apply` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:10793` | With `k = 1` and `p = q = 1/2`, absent and present edges force entries `-1/2` and `1/2`, excluding zero and sample-independent constants.  The model has actual vertices and avoids the empty `k = 0` boundary. |
| 9 | `HDP.Chapter4.twoSidedGramConstant` | `HDP.Chapter4.twoSidedGramConstant_pos` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:12643` | Strict positivity excludes zero and negative placeholders.  The definition is a closed scalar with no empty, division, measure, or typeclass boundary. |
| 10 | `HDP.Chapter4.twoSidedSingularConstant` | `HDP.Chapter4.twoSidedSingularConstant_pos` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:13081` | Strict positivity excludes zero and negative placeholders.  The definition is a closed scalar with no empty, division, measure, or typeclass boundary. |
| 11 | `HDP.Chapter7.canonicalGaussianProcess` | `HDP.Chapter7.canonicalGaussianProcess_variance` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:929` | In `E = ℝ`, coefficients one and zero force variances one and zero, excluding a zero or coefficient-independent constant process.  The one-point index and fixed standard Gaussian measure make the measure/typeclass assumptions explicit. |
| 12 | `HDP.Chapter7.crossPolytopeGaussianWidth` | `HDP.Chapter7.crossPolytopeGaussianWidth_twoSided` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:12993` | The positive lower bound at `k = 0` excludes zero, while comparison with the dimension-varying Gaussian maximum scale excludes a dimension-independent constant.  Dimensions are `k + 2`, avoiding exceptional dimensions zero and one. |
| 13 | `HDP.Chapter7.finiteEuclideanDiameter` | `HDP.Chapter7.finiteEuclideanDiameter_eq_sup'` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:11819` | The finite sets `{0}` and `{0,1}` in one dimension force diameters zero and one, excluding zero and constant functionals.  The theorem requires a nonempty set, so no empty-supremum convention supplies the evidence. |
| 14 | `HDP.Chapter7.finiteRadius` | `HDP.Chapter7.finiteRadius_eq_sup'` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:12339` | The singleton sets `{0}` and `{1}` force radii zero and one, excluding zero and constant functionals.  Nonemptiness removes empty-supremum ambiguity. |
| 15 | `HDP.Chapter7.gaussianComplexity` | `HDP.Chapter8.finiteRadius_le_two_gaussianComplexity` | `HighDimensionalProbability/Chapter8_Chaining.lean:21853` | For the one-dimensional singleton `{1}`, radius one forces Gaussian complexity at least `1/2`; scaling the singleton excludes a fixed bounded constant.  The set is explicitly nonempty, so no empty supremum is involved. |
| 16 | `HDP.Chapter7.gaussianMeasureCovarianceMatrix` | `HDP.Chapter7.gaussianMeasureCovarianceMatrix_processVector_apply` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:3351` | A one-coordinate standard real Gaussian process gives diagonal entry one, while the zero Gaussian process gives zero, excluding zero and constant covariance matrices.  The mapped measure, integral, centering, measurability, and finite-index requirements are explicit. |
| 17 | `HDP.Chapter7.gaussianWidth` | `HDP.Chapter7.gaussianWidth_diameterSymmetricPair_eq` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:11931` | The exact symmetric-pair formula gives positive width for `v = 1` and zero for `v = 0`; scaling excludes zero and constant widths.  It directly covers the collapsed `v = 0` boundary and has no empty-set or cardinality division. |
| 18 | `HDP.gramMatrix` | `HDP.matrixOpNorm_sq_eq_gram` | `HighDimensionalProbability/Prelude/Matrix.lean:326` | Singleton matrices `[1]` and `[0]` force Gram operator norms one and zero, excluding zero and constant Gram constructors.  An empty column type legitimately makes both sides zero. |
| 19 | `HDP.matrixFrobeniusInner` | `HDP.Chapter4.frobeniusInner_eq_trace` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:1335` | Singleton pairs `A = B = [1]` and `A = [0], B = [1]` force values one and zero, excluding zero and constant functionals.  Empty shapes legitimately reduce the trace and sum to zero. |
| 20 | `HDP.matrixFrobeniusNorm` | `HDP.matrixFrobeniusNorm_sq` | `HighDimensionalProbability/Prelude/Matrix.lean:217` | The exact sum-of-squares formula forces squared norms one and zero on `[1]` and `[0]`, excluding zero and constant norms.  Empty row or column types legitimately produce an empty sum and norm zero. |
| 21 | `HDP.matrixOpNorm` | `HDP.Chapter4.exercise_4_2a_operator_norm` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean:1309` | Triangle inequality, homogeneity, and `matrixOpNorm A = 0 ↔ A = 0` exclude zero and nonzero constant functionals on `[1]` and `[0]`.  Empty matrix shapes are extensionally zero, consistently with the separation law. |
| 22 | `HDP.matrixOperator` | `HDP.Chapter6.matrixOperatorEquiv_apply` | `HighDimensionalProbability/Chapter6_QuadraticFormsSymmetrizationContraction.lean:7229` | Equality to the injective matrix/operator linear equivalence distinguishes one-dimensional matrices `[0]` and `[1]`, excluding zero and data-forgetting constant constructors.  Dimension zero legitimately has the unique zero matrix/operator. |
| 23 | `HDP.processCovariance` | `HDP.Chapter7.canonicalGaussianProcess_covariance` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:910` | In `E = ℝ`, coefficient maps one and zero force covariance values one and zero through the exact inner-product formula, excluding zero and constant covariance functionals.  The Gaussian measure and finite-dimensional measurable/Borel hypotheses are explicit. |
| 24 | `HDP.processIncrement` | `HDP.processIncrement_eq_lpNorm` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean:127` | On a one-point probability space, coordinates one and zero give increment one, while equal coordinates give zero, excluding zero and constant increments.  `MemLp` hypotheses are explicit and prevent an infinite-norm boundary from being hidden. |
| 25 | `HDP.randomMatrixRow` | `HDP.randomMatrixRow_apply` | `HighDimensionalProbability/Prelude/RandomMatrix.lean:141` | The exact component formula gives singleton row components one and zero for matrices with entries one and zero, excluding zero, constant, omitted, or permuted data.  The singleton model avoids empty-vector vacuity; the empty-column case is the unique legitimate empty row. |
| 26 | `HDP.sampleSecondMoment` | `HDP.sampleSecondMoment_apply` | `HighDimensionalProbability/Prelude/RandomMatrix.lean:353` | The exact entry formula gives one and zero for singleton samples with coordinate one and zero, excluding zero and constant constructors.  Sample size zero is exposed explicitly: inverse zero and the empty sum yield the legitimate zero-normalization boundary. |

## Independent conclusion

The 26 promotions are internally consistent with the packet and protocol,
resolve to exact physical theorem declarations, use only the recorded allowed
V4 axiom set, and each has a concrete interpretation that excludes the
relevant zero/constant/junk collapse while respecting its boundary
conditions.  I found no semantic or provenance objection to freezing these
26 rows as `VERIFIED_CITATION`.

## Limitations

This is an independent manual source-and-statement review, assisted by
mechanical cross-checking of the TSV against the packet.  It is not a
machine-checked proof of the English model explanations, does not create or
compile new Lean witness declarations, and does not upgrade any row lacking
an accepted citation.  The audit therefore confirms the stated 26
promotions; it does not claim completeness of the candidate search for the
remaining 49 rows.
