import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# Book Chapter 3 exercises 3.32--3.46

Only non-load-bearing category-A declarations remain here. Exercise 3.32 is
implemented directly in `13_SubGaussianVectors.lean`, Exercise 3.34 in
`26_SubGaussianMatrices.lean`, and the reusable Exercise 3.37 counterexample in
`27_SubGaussianCounterexample.lean`; no wrappers or aliases are repeated in this leaf.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- EXERCISE-SORRY (category A): Exercise 3.33 is not load-bearing. -/
/-- Applying a linear isometry preserves both the subgaussian-vector property
and the vector `ψ₂` norm.

**Book Exercise 3.33.** -/
theorem exercise_3_33 [IsProbabilityMeasure μ]
    {n : ℕ} (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n))
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    HDP.SubGaussianVector (fun ω => U (X ω)) μ ↔
      HDP.SubGaussianVector X μ ∧
        HDP.psi2NormVector (fun ω => U (X ω)) μ =
          HDP.psi2NormVector X μ := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.35 is not load-bearing. -/
/-- A sum of independent centered subgaussian vectors is subgaussian, with
squared vector `ψ₂` norm at most `30` times the sum of the squared individual
norms.

**Book Exercise 3.35.** -/
theorem exercise_3_35 [IsProbabilityMeasure μ]
    {N n : ℕ} {X : Fin N → Ω → EuclideanSpace ℝ (Fin n)}
    (hsub : ∀ i, HDP.SubGaussianVector (X i) μ)
    (hmean : ∀ i u, ∫ ω, inner ℝ (X i ω) u ∂μ = 0)
    (hindep : iIndepFun X μ) :
    HDP.SubGaussianVector (fun ω => ∑ i, X i ω) μ ∧
      HDP.psi2NormVector (fun ω => ∑ i, X i ω) μ ^ 2 ≤
        30 * ∑ i, HDP.psi2NormVector (X i) μ ^ 2 := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.36(a) is not load-bearing;
part (b) is a constructive sharpness request and is recorded as skipped. -/
/-- Every coordinate `ψ₂` norm is bounded by the vector `ψ₂` norm, while a
uniform coordinate bound `K` gives the upper estimate `√n · K`.

**Book Exercise 3.36(a).** -/
theorem exercise_3_36a [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n] {X : Fin n → Ω → ℝ}
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm
          (fun ω => inner ℝ (vectorOfCoordinates X ω) u) μ})
    {K : ℝ} (hK : 0 ≤ K) (hcoord : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    (∀ i, HDP.psi2Norm (X i) μ ≤
      HDP.psi2NormVector (vectorOfCoordinates X) μ) ∧
      HDP.psi2NormVector (vectorOfCoordinates X) μ ≤ Real.sqrt n * K := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.38 is not load-bearing. -/
/-- The vector `ψ₂` norm of a centered Gaussian vector equals
`√(8/3)` times the square root of the largest covariance quadratic form over
unit directions.

**Book Exercise 3.38.** -/
theorem exercise_3_38 [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    {m : EuclideanSpace ℝ (Fin n)} {S : Matrix (Fin n) (Fin n) ℝ}
    (hX : HDP.HasGaussianVectorLaw X μ m S)
    (hcenter : m = 0) (hS : S.PosSemidef) :
    HDP.psi2NormVector X μ = Real.sqrt (8 / 3) *
      Real.sqrt (sSup {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n),
        ‖u‖ = 1 ∧ r = ∑ i, u i * ∑ j, S i j * u j}) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.39 is not load-bearing. -/
/-- The `ψ₂` norm of the Euclidean length of a random vector is at most the
root-sum-square of its coordinate `ψ₂` norms.

**Book Exercise 3.39.** -/
theorem exercise_3_39 [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HDP.SubGaussian (X i) μ) :
    HDP.psi2Norm (fun ω => Real.sqrt (∑ i, X i ω ^ 2)) μ ≤
      Real.sqrt (∑ i, HDP.psi2Norm (X i) μ ^ 2) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.40 is not load-bearing. -/
/-- Two independent isotropic subgaussian vectors have normalized directions
whose inner product is `O(1/√n)` with probability at least `99/100`.

**Book Exercise 3.40(a).** -/
theorem exercise_3_40a [IsProbabilityMeasure μ]
    {n : ℕ} {X Y : Ω → EuclideanSpace ℝ (Fin n)}
    (hXY : IndepFun X Y μ) (hXiso : HDP.IsIsotropic X μ)
    (hYiso : HDP.IsIsotropic Y μ) {K : ℝ} (hK : 0 ≤ K)
    (hXK : HDP.psi2NormVector X μ ≤ K)
    (hYK : HDP.psi2NormVector Y μ ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      99 / 100 ≤ μ.real {ω |
        |inner ℝ ((‖X ω‖)⁻¹ • X ω) ((‖Y ω‖)⁻¹ • Y ω)| ≤
          C / Real.sqrt n} := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.41 is not load-bearing. -/
/-- Whenever `N ≤ exp(n/100000)`, there exist `N` unit vectors in `ℝⁿ` whose
pairwise inner products are at most `1/100`.

**Book Exercise 3.41.** -/
theorem exercise_3_41 {n N : ℕ} (hn : 0 < n)
    (hN : (N : ℝ) ≤ Real.exp (n / 100000 : ℝ)) :
    ∃ X : Fin N → EuclideanSpace ℝ (Fin n),
      (∀ i, ‖X i‖ = 1) ∧
      ∀ i j, i ≠ j → inner ℝ (X i) (X j) ≤ 1 / 100 := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.42 is not load-bearing. -/
/-- Every unit direction of a random vector supported in the Euclidean unit
ball has tail at most `2 exp(-n t²/8)` at threshold `t ≥ 0`.

**Book Exercise 3.42.** -/
theorem exercise_3_42 [IsProbabilityMeasure μ]
    {n : ℕ} {Y : Ω → EuclideanSpace ℝ (Fin n)}
    (hball : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ 1) :
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 → ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | |inner ℝ (Y ω) u| ≥ t} ≤
        2 * Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.43 is not load-bearing. -/
/-- A vector chosen uniformly from the standard basis of `ℝⁿ` has vector
`ψ₂` norm comparable to `1/√(log n)`.

**Book Exercise 3.43.** -/
theorem exercise_3_43 {n : ℕ} (hn : 2 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      c / Real.sqrt (Real.log n) ≤
        HDP.psi2NormVector (fun i : Fin n =>
          EuclideanSpace.single i 1) (uniformOn Set.univ) ∧
      HDP.psi2NormVector (fun i : Fin n =>
          EuclideanSpace.single i 1) (uniformOn Set.univ) ≤
        C / Real.sqrt (Real.log n) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.44 is not load-bearing. -/
/-- For some radius between `n` and `4n`, the uniform measure on the
corresponding `ℓ¹` ball supports an isotropic random vector whose vector `ψ₂`
norm is at least `√n/100`.

**Book Exercise 3.44.** -/
theorem exercise_3_44 {n : ℕ} (hn : 0 < n) :
    ∃ r : ℝ, 0 < r ∧ n ≤ r ∧ r ≤ 4 * n ∧
      ∃ X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HDP.IsIsotropic X
          (uniformOn {x | ∑ i, |x i| ≤ r}) ∧
        Real.sqrt n / 100 ≤ HDP.psi2NormVector X
          (uniformOn {x | ∑ i, |x i| ≤ r}) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.45 is not load-bearing.  The
printed division by `K²` is split at `K = 0`. -/
/-- The atom masses of a subgaussian vector obey a Gaussian-type bound:
nonzero atoms vanish when the vector `ψ₂` norm is zero, and otherwise every
atom has mass at most `2 exp(-‖x‖²/K²)`.

**Book Exercise 3.45.** -/
theorem exercise_3_45 [IsProbabilityMeasure μ]
    {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hsub : HDP.SubGaussianVector X μ)
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (X ω) u) μ}) :
    let K := HDP.psi2NormVector X μ
    (K = 0 → ∀ x, x ≠ 0 → μ.real {ω | X ω = x} = 0) ∧
      (0 < K → ∀ x, μ.real {ω | X ω = x} ≤
        2 * Real.exp (-‖x‖ ^ 2 / K ^ 2)) := by
  sorry

/-- Entropy of a finite probability vector.

**Lean implementation helper.** -/
noncomputable def finiteEntropy {ι : Type*} [Fintype ι]
    (p : ι → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/- EXERCISE-SORRY (category A): Exercise 3.46 is not load-bearing. -/
/-- A finite isotropic distribution with Gaussian-type atom bounds has entropy
at least `n/K² - log 2` and consequently has at least
`(1/2) exp(n/K²)` support indices.

**Book Exercise 3.46.** -/
theorem exercise_3_46
    {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (x : ι → EuclideanSpace ℝ (Fin n))
    (hiso : ∀ j k, ∑ i, p i * (x i j * x i k) =
      if j = k then 1 else 0)
    {K : ℝ} (hK : 0 < K)
    (hatom : ∀ i, p i ≤ 2 * Real.exp (-‖x i‖ ^ 2 / K ^ 2)) :
    n / K ^ 2 - Real.log 2 ≤ finiteEntropy p ∧
      (1 / 2 : ℝ) * Real.exp (n / K ^ 2) ≤ Fintype.card ι := by
  sorry

end HDP.Chapter3
