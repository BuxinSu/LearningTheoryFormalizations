import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.Probability.Distributions.Uniform

/-!
# Book Chapter 2 exercises for Section 2.1
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- EXERCISE-SORRY (category A): Exercise 2.1 is not used by the main line. -/
/-- For a product of `N` independent `Unif[0,1]` variables, the probability
that the product is at least its mean lies between `(1/2)ᴺ` and `(19/20)ᴺ`.

**Book Exercise 2.1.** -/
theorem exercise_2_1 [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hindep : iIndepFun X μ) :
    (1 / 2 : ℝ) ^ N ≤
        μ.real {ω | (∫ ω', ∏ i, X i ω' ∂μ) ≤ ∏ i, X i ω} ∧
      μ.real {ω | (∫ ω', ∏ i, X i ω' ∂μ) ≤ ∏ i, X i ω} ≤
        (19 / 20 : ℝ) ^ N := by
  sorry

/- Exercise 2.2 is Proposition 2.1.2 itself. Its authoritative declaration is
`gaussian_tail_lower` in the Section 2.1 core module; it is intentionally not
redeclared in this exercise leaf. -/

/- EXERCISE-SORRY (category A): Exercise 2.3 is not used by the main line. -/
/-- For a positive threshold `t`, the upper standard-Gaussian tail divided by
its density lies between `1/t - 1/t³` and `1/t - 1/t³ + 3/t⁵`.

**Book Exercise 2.3.** -/
theorem exercise_2_3 {t : ℝ} (ht : 0 < t) :
    1 / t - 1 / t ^ 3 ≤
        (gaussianReal 0 1).real (Set.Ioi t) / stdGaussianDensity t ∧
      (gaussianReal 0 1).real (Set.Ioi t) / stdGaussianDensity t ≤
        1 / t - 1 / t ^ 3 + 3 / t ^ 5 := by
  sorry

/-- For a standard Gaussian variable `g` and `t > 0`, the truncated first
moment of `g` above `t` equals the standard-Gaussian density at `t`.

**Book Exercise 2.4(a).** -/
theorem exercise_2_4a {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ)
    (hgm : Measurable g) {t : ℝ} (_ht : 0 < t) :
    (∫ ω in {ω | t < g ω}, g ω ∂μ) = stdGaussianDensity t :=
  gaussian_truncated_first_moment hg hgm t

/- Corrected Exercise 2.4(b) is used in the Chapter 3 Grothendieck truncation
argument. Its authoritative declaration is
`gaussian_truncated_second_moment_upper` in the Section 2.1 core module. -/

end HDP.Chapter2
