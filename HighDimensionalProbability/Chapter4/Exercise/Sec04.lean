import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import HighDimensionalProbability.Prelude.RandomMatrix

/-!
# Chapter 4 exercises attached to Section 4.4

Only the two non-load-bearing exercises occur here.  Exercises 4.41, 4.43 and
4.44 are promoted to the thematic core because later text uses their bounds.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace HDP.Chapter4.Exercise

/-- A finite family is in convex position when no point belongs to the convex hull of all the
others.

**Lean implementation helper.** -/
def InConvexPosition {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (x : ι → E) : Prop :=
  ∀ i, x i ∉ convexHull ℝ (x '' {j | j ≠ i})

/-- Exponentially many independent standard Gaussian points fail to be in convex position with
exponentially high probability. The constants are quantified before the dimension and cloud
size, so they are genuinely absolute.

**Book Exercise 4.40.** -/
theorem exercise_4_40 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (n N : ℕ), 0 < n → Real.exp (C * n) ≤ N →
        HDP.Chapter3.gaussianCloudMeasure N n {g | InConvexPosition g} ≤
          ENNReal.ofReal (Real.exp (-c * n)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.40.
  sorry

/-- Matching lower tail for the operator norm of an independent variance-one subgaussian matrix.
Positive dimensions make the first-row/first-column argument nonvacuous, and `c` is absolute.

**Book Exercise 4.42.** -/
theorem exercise_4_42 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ} [NeZero m] [NeZero n]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ),
        (∀ i j, AEMeasurable (fun ω => A ω i j) P) →
        HDP.RandomMatrix.IndependentEntries A P →
        (∀ i j, HDP.SubGaussian (fun ω => A ω i j) P) →
        (∀ i j, ∫ ω, (A ω i j) ^ 2 ∂P = 1) →
        ∀ {K t : ℝ}, 0 < K →
        (∀ i j, HDP.psi2Norm (fun ω => A ω i j) P ≤ K) → 0 < t →
        P {ω | HDP.matrixOpNorm (A ω) <
          (Real.sqrt m + Real.sqrt n - t) / 2} ≤
          ENNReal.ofReal (2 * Real.exp (-c * t ^ 2 / K ^ 4)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.42.
  sorry

end HDP.Chapter4.Exercise
