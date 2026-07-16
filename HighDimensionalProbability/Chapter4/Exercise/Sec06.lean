import HighDimensionalProbability.Prelude.RandomMatrix

/-!
# Chapter 4 exercises attached to Section 4.6
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HDP.Chapter4.Exercise

/-- Alternative net proof of the two-sided singular-value bound. The declaration states the same
quantitative endpoint while the exercise asks for the alternative proof route.

**Book Exercise 4.46.** -/
theorem exercise_4_46 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ} [NeZero m] [NeZero n]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ),
        HDP.RandomMatrix.IndependentRows A P →
        (∀ i, AEMeasurable (HDP.randomMatrixRow A i) P) →
        (∀ i j, ∫ ω, A ω i j ∂P = 0) →
        (∀ i, HDP.IsIsotropic (HDP.randomMatrixRow A i) P) →
        (∀ i, HDP.SubGaussianVector (HDP.randomMatrixRow A i) P) →
        (∀ i, BddAbove
          {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
            r = HDP.psi2Norm
              (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) u) P}) →
        ∀ {K t : ℝ}, 0 < K →
        (∀ i, HDP.psi2NormVector (HDP.randomMatrixRow A i) P ≤ K) →
        0 ≤ t →
        P {ω |
          Real.sqrt m - C * K ^ 2 * (Real.sqrt n + t) ≤
              HDP.matrixSingularValue (A ω) (n - 1) ∧
            HDP.matrixSingularValue (A ω) 0 ≤
              Real.sqrt m + C * K ^ 2 * (Real.sqrt n + t)} ≥
          ENNReal.ofReal (1 - 2 * Real.exp (-t ^ 2)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.46.
  sorry

end HDP.Chapter4.Exercise
