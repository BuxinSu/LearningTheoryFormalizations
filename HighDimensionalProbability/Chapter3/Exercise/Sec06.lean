import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import Mathlib.Probability.ProductMeasure

/-!
# Book Chapter 3 exercises 3.53--3.54

Exercise 3.53 is promoted to the core file `21_Grothendieck.lean` because Chapter 3
uses it. Exercise 3.54 remains isolated here as a category-A algorithmic
exercise.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter3

/-- Half the total matrix weight, which upper-bounds every cut objective when
the weights are nonnegative.

**Lean implementation helper.** -/
noncomputable def totalCutWeight {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, A i j

/-- A precise certificate for the Las Vegas repetition requested in Exercise
3.54.  It records both the first successful Gaussian round and the source's
deterministic output guarantee. -/
structure LasVegasCutCertificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (X : ι → EuclideanSpace ℝ κ) (ε : ℝ) where
  runtime : (ℕ → EuclideanSpace ℝ κ) → ℕ
  output : (ℕ → EuclideanSpace ℝ κ) → ι → ℝ
  output_eq_rounding : ∀ samples i,
    output samples i = HDP.hyperplaneLabel
      (samples (runtime samples)) (X i)
  guarantee : ∀ samples,
    (439 / 500 - ε) * HDP.sdpCutObjective A X ≤
      HDP.cutMatrixObjective A (output samples)

/- EXERCISE-SORRY (category A): Exercise 3.54 is an algorithmic,
non-load-bearing exercise. -/
/-- Repeated independent Gaussian hyperplane rounds
give a deterministic `(0.878-ε)` outcome. The final inequality is the
standard geometric-trial bound obtained from the one-round expectation and
the cut upper bound `totalCutWeight A`.

**Book Exercise 3.54.** -/
theorem exercise_3_54
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (X : ι → EuclideanSpace ℝ κ) (hX : ∀ i, ‖X i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 439 / 500)
    (hS : 0 < HDP.sdpCutObjective A X) :
    ∃ C : LasVegasCutCertificate A X ε,
      (∫ samples : ℕ → EuclideanSpace ℝ κ,
          (C.runtime samples : ℝ)
          ∂Measure.infinitePi (fun _ : ℕ =>
            stdGaussian (EuclideanSpace ℝ κ))) ≤
        (totalCutWeight A -
            (439 / 500 - ε) * HDP.sdpCutObjective A X) /
          (ε * HDP.sdpCutObjective A X) := by
  sorry

end HDP.Chapter3
