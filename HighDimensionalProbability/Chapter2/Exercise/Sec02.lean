import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.Probability.Density

/-!
# Book Chapter 2 exercises for Section 2.2

Exercises 2.5, 2.6, and 2.8--2.10 are authoritative core results: they are used
by Chapter 2 or later chapters and are therefore not redeclared here. This leaf
contains only the non-load-bearing Exercise 2.7.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- EXERCISE-SORRY (category A): Exercise 2.7 is not used by the main line. -/
/-- If independent nonnegative variables have densities bounded by `K`, then
their sum is at most `εN` with probability at most `(e K ε)ᴺ`.

**Book Exercise 2.7.** -/
theorem exercise_2_7 [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hindep : iIndepFun X μ)
    (hX0 : ∀ i, 0 ≤ᵐ[μ] X i) (hpdf : ∀ i, HasPDF (X i) μ volume)
    {K ε : ℝ} (hK : 0 ≤ K)
    (hpdfK : ∀ i, ∀ᵐ x ∂volume, (pdf (X i) μ volume x).toReal ≤ K)
    (hε : 0 < ε) :
    μ.real {ω | ∑ i, X i ω ≤ ε * N} ≤
      (Real.exp 1 * K * ε) ^ N := by
  sorry

end HDP.Chapter2
