import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums

/-!
# Book Chapter 2 exercises for Section 2.7

Load-bearing Exercises 2.35, 2.37 and 2.38 are proved in the core
`GaussianMaxima` and `GaussianMaximaAsymptotic` modules and re-exported by this
leaf's namespace.  The remaining
proof questions are exact category-A declarations.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal unitInterval Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- EXERCISE-SORRY (category A): Exercise 2.36(a) is not load-bearing. -/
/-- The `L²` norm is at most the product of the `L¹` norm to the power `1/4`
and the `L³` norm to the power `3/4`.

**Book Exercise 2.36(a).** -/
theorem exercise_2_36a [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : MemLp Z 3 μ) :
    HDP.Chapter1.lpNormRV Z 2 μ ≤
      HDP.Chapter1.lpNormRV Z 1 μ ^ (1 / 4 : ℝ) *
        HDP.Chapter1.lpNormRV Z 3 μ ^ (3 / 4 : ℝ) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.36(b) is not load-bearing. -/
/-- The expected absolute value of a weighted independent subgaussian sum is
bounded above by the coefficient `ℓ²` norm and below by
`(1/1000) K⁻³` times that norm.

**Book Exercise 2.36(b).** -/
theorem exercise_2_36b [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKmax : ∀ i, HDP.psi2Norm (X i) μ ≤ K) (a : Fin N → ℝ) :
    (1 / 1000 : ℝ) * K⁻¹ ^ 3 * Real.sqrt (∑ i, a i ^ 2) ≤
        ∫ ω, |∑ i, a i * X i ω| ∂μ ∧
      (∫ ω, |∑ i, a i * X i ω| ∂μ) ≤
        Real.sqrt (∑ i, a i ^ 2) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.36(c) is not load-bearing. -/
/-- For every `p ∈ [1,2]`, the `Lᵖ` norm of a weighted independent
subgaussian sum satisfies the same two-sided coefficient `ℓ²` comparison.

**Book Exercise 2.36(c).** -/
theorem exercise_2_36c [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKmax : ∀ i, HDP.psi2Norm (X i) μ ≤ K) (a : Fin N → ℝ)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    (1 / 1000 : ℝ) * K⁻¹ ^ 3 * Real.sqrt (∑ i, a i ^ 2) ≤
        HDP.Chapter1.lpNormRV (fun ω => ∑ i, a i * X i ω) p μ ∧
      HDP.Chapter1.lpNormRV (fun ω => ∑ i, a i * X i ω) p μ ≤
        Real.sqrt (∑ i, a i ^ 2) := by
  sorry

/-- `MaximalCopyBound X μ K` bounds the expected maximum absolute value of
every finite independent family distributed like `X` by `K √(log N)`.

**Book Exercise 2.39.** -/
def MaximalCopyBound (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N) (Y : Fin N → Ω → ℝ),
    letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    (∀ i, IdentDistrib (Y i) X μ μ) → iIndepFun Y μ →
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty
          (fun i => |Y i ω|) ∂μ ≤ K * Real.sqrt (Real.log N)

/- EXERCISE-SORRY (category A): Exercise 2.39 is not load-bearing. -/
/-- A measurable random variable is subgaussian if and only if the expected
maximum of every finite independent family of copies grows at most like
`√(log N)`, with quantitative comparison to its `ψ₂` norm.

**Book Exercise 2.39.** -/
theorem exercise_2_39 :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ},
        AEMeasurable X μ → HDP.SubGaussian X μ →
          MaximalCopyBound X μ (C * HDP.psi2Norm X μ)) ∧
      (∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ},
        AEMeasurable X μ → 0 < K → MaximalCopyBound X μ K →
          HDP.SubGaussian X μ ∧ HDP.psi2Norm X μ ≤ C * K) := by
  sorry

/-! ## Exercise 2.40: exact subgaussian norm -/

/-- The infimum of variance proxies in the centered subgaussian MGF bound.

**Book Exercise 2.40.** -/
noncomputable def subGaussianVariance (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ∀ lam : ℝ,
    ∫⁻ ω, ENNReal.ofReal
        (Real.exp (lam * (X ω - ∫ ω', X ω' ∂μ))) ∂μ ≤
      ENNReal.ofReal (Real.exp (s * lam ^ 2 / 2))}

/-- The exact subgaussian norm obtained by combining the optimal centered MGF
variance proxy with the square of the mean.

**Book Exercise 2.40.** -/
noncomputable def exactSubGaussianNorm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  Real.sqrt (subGaussianVariance X μ + (∫ ω, X ω ∂μ) ^ 2)

/- EXERCISE-SORRY (category A): Exercise 2.40(a) is not load-bearing. -/
/-- The exact subgaussian norm is nonnegative, vanishes exactly for variables
equal to zero almost everywhere, is absolutely homogeneous, and satisfies the
triangle inequality.

**Book Exercise 2.40(a).** -/
theorem exercise_2_40a [IsProbabilityMeasure μ] :
    (∀ X : Ω → ℝ, Integrable X μ → HDP.SubGaussian X μ →
      0 ≤ exactSubGaussianNorm X μ) ∧
    (∀ X : Ω → ℝ, Integrable X μ → HDP.SubGaussian X μ →
      (exactSubGaussianNorm X μ = 0 ↔ X =ᵐ[μ] 0)) ∧
    (∀ (X : Ω → ℝ) (c : ℝ), Integrable X μ → HDP.SubGaussian X μ →
      exactSubGaussianNorm (fun ω => c * X ω) μ =
        |c| * exactSubGaussianNorm X μ) ∧
    (∀ X Y : Ω → ℝ, Integrable X μ → Integrable Y μ →
      HDP.SubGaussian X μ → HDP.SubGaussian Y μ →
      exactSubGaussianNorm (fun ω => X ω + Y ω) μ ≤
        exactSubGaussianNorm X μ + exactSubGaussianNorm Y μ) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.40(b) is not load-bearing. -/
/-- The exact subgaussian norm and the standard `ψ₂` norm are equivalent up to
universal positive constants.

**Book Exercise 2.40(b).** -/
theorem exercise_2_40b :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {X : Ω → ℝ},
        Integrable X μ → HDP.SubGaussian X μ →
          c₁ * HDP.psi2Norm X μ ≤ exactSubGaussianNorm X μ ∧
          exactSubGaussianNorm X μ ≤ c₂ * HDP.psi2Norm X μ := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.40(c) is not load-bearing. -/
/-- The optimal centered MGF variance proxy dominates the variance, and the
exact subgaussian norm dominates the `L²` norm.

**Book Exercise 2.40(c).** -/
theorem exercise_2_40c [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hsub : HDP.SubGaussian X μ) :
    Var[X; μ] ≤ subGaussianVariance X μ ∧
      HDP.Chapter1.lpNormRV X 2 μ ≤ exactSubGaussianNorm X μ := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.40(c) is not load-bearing. -/
/-- For a Gaussian variable with mean `m` and variance `v`, the optimal MGF
variance proxy is `v` and the exact subgaussian norm is `√(v + m²)`.

**Book Exercise 2.40(c).** -/
theorem exercise_2_40c_gaussian [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) μ) :
    subGaussianVariance X μ = v ∧
      exactSubGaussianNorm X μ = Real.sqrt ((v : ℝ) + m ^ 2) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.40(d) is not load-bearing. -/
/-- The optimal centered MGF variance proxy of an independent centered sum is
at most the sum of the individual proxies.

**Book Exercise 2.40(d).** -/
theorem exercise_2_40d [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXint : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hindep : iIndepFun X μ) :
    subGaussianVariance (fun ω => ∑ i, X i ω) μ ≤
      ∑ i, subGaussianVariance (X i) μ := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.40(e) is not load-bearing. -/
/-- Centering a subgaussian variable does not increase its exact subgaussian
norm.

**Book Exercise 2.40(e).** -/
theorem exercise_2_40e [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) (hsub : HDP.SubGaussian X μ) :
    exactSubGaussianNorm (fun ω => X ω - ∫ ω', X ω' ∂μ) μ ≤
      exactSubGaussianNorm X μ := by
  sorry

end HDP.Chapter2
