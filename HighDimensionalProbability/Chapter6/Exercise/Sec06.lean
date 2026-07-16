import HighDimensionalProbability.Chapter6_QuadraticFormsSymmetrizationContraction

/-!
# Chapter 6 exercises attached to Section 6.6

Exercise 6.37 is a witness task whose resulting optimality fact proves Remark
6.6.3, so that fact belongs to core.  The two non-load-bearing proof exercises
6.36 and 6.38 live here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HDP.Chapter6.Exercise

/-- A random vector sum with deterministic scalar coefficients.

**Lean implementation helper.** -/
def coefficientVectorSum {Ω E : Type*} {N : ℕ} [AddCommMonoid E]
    [Module ℝ E] (a : Fin N → ℝ) (X : Fin N → Ω → E) (ω : Ω) : E :=
  ∑ i, a i • X i ω

/-- A signed deterministic vector series.

**Lean implementation helper.** -/
def signedDeterministicSum {Ω E : Type*} {N : ℕ} [AddCommMonoid E]
    [Module ℝ E] (eps : Fin N → Ω → ℝ) (a : Fin N → ℝ)
    (x : Fin N → E) (ω : Ω) : E :=
  ∑ i, (a i * eps i ω) • x i

/-- A Gaussian-randomized vector sum.

**Lean implementation helper.** -/
def gaussianRandomizedSum {Ω E : Type*} {N : ℕ} [AddCommMonoid E]
    [Module ℝ E] (g : Fin N → Ω → ℝ) (X : Fin N → Ω → E) (ω : Ω) : E :=
  ∑ i, g i ω • X i ω

/-- The source says `a ∈ ℝⁿ` while indexing both coefficients and vectors by `1,...,N`; the
coefficient type is therefore `Fin N → ℝ`.

**Book Exercise 6.36.** -/
theorem exercise_6_36 {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (a : Fin N → ℝ) (X : Fin N → Ω → E)
    (_hXint : ∀ i, Integrable (X i) μ) (_hind : iIndepFun X μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, ‖coefficientVectorSum a X ω‖ ∂μ) ≤
      4 * HDP.Chapter1.linftyNorm a *
        ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.36.
  sorry

/-- Contraction and Gaussian symmetrization after applying an increasing convex function to the
norm. Scale factors remain *inside* `F`, as required by the phrase “replace the norm
throughout.” The Gaussian part uses `N ≥ 2`, avoiding the source's undefined `sqrt(log 1)`
denominator.

**Book Exercise 6.38.** -/
theorem exercise_6_38 :
    (∀ {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {N : ℕ}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E]
        (x : Fin N → E) (a : Fin N → ℝ) (eps : Fin N → Ω → ℝ),
        (∀ i, HDP.IsRademacher (eps i) μ) → iIndepFun eps μ →
        ∀ (F : ℝ → ℝ), MonotoneOn F (Set.Ici 0) →
        ConvexOn ℝ (Set.Ici 0) F →
        Integrable (fun ω => F ‖signedDeterministicSum eps a x ω‖) μ →
        Integrable (fun ω => F
          (HDP.Chapter1.linftyNorm a *
            ‖signedDeterministicSum eps (fun _ => 1) x ω‖)) μ →
        (∫ ω, F ‖signedDeterministicSum eps a x ω‖ ∂μ) ≤
          ∫ ω, F (HDP.Chapter1.linftyNorm a *
            ‖signedDeterministicSum eps (fun _ => 1) x ω‖) ∂μ) ∧
      (∃ c : ℝ, 0 < c ∧
        ∀ {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {N : ℕ} (hN : 2 ≤ N)
          [NormedAddCommGroup E] [NormedSpace ℝ E]
          [MeasurableSpace E] [BorelSpace E]
          (X : Fin N → Ω → E) (g : Fin N → Ω → ℝ),
          (∀ i, Integrable (X i) μ) → iIndepFun X μ →
          (∀ i, ∫ ω, X i ω ∂μ = 0) →
          (∀ i, HasLaw (g i) (gaussianReal 0 1) μ) → iIndepFun g μ →
          IndepFun (fun ω i => X i ω) (fun ω i => g i ω) μ →
          ∀ (F : ℝ → ℝ), MonotoneOn F (Set.Ici 0) →
          ConvexOn ℝ (Set.Ici 0) F →
          Integrable (fun ω => F
            (c / Real.sqrt (Real.log N) * ‖gaussianRandomizedSum g X ω‖)) μ →
          Integrable (fun ω => F ‖∑ i, X i ω‖) μ →
          Integrable (fun ω => F (3 * ‖gaussianRandomizedSum g X ω‖)) μ →
          (∫ ω, F
              (c / Real.sqrt (Real.log N) * ‖gaussianRandomizedSum g X ω‖) ∂μ) ≤
              ∫ ω, F ‖∑ i, X i ω‖ ∂μ ∧
            (∫ ω, F ‖∑ i, X i ω‖ ∂μ) ≤
              ∫ ω, F (3 * ‖gaussianRandomizedSum g X ω‖) ∂μ) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.38.
  sorry

end HDP.Chapter6.Exercise
