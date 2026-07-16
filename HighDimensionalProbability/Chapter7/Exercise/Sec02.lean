import HighDimensionalProbability.Chapter6.Main

/-!
# Book Chapter 7 exercises attached to Section 7.2

Exercises 7.6, 7.7, and 7.9 discharge proofs used by the Gaussian-comparison
main line and therefore live only in core.  This leaf contains only Exercise
7.8.
-/

open MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HDP.Chapter7.Exercise

/-- A finite supremum used in the Gaussian contraction statement.

**Lean implementation helper.** -/
def gaussianFiniteSup {A E : Type*} (S : Finset A) (hS : S.Nonempty)
    (F : A → E → ℝ) (g : E) : ℝ :=
  S.sup' hS fun x => F x g

/-- **Exercise 7.8.** Gaussian contraction on a finite restriction of the
index set, which is the chapter's convention for general suprema.

**Book Exercise 7.8.** -/
theorem exercise_7_8 {n : ℕ} (S : Finset (Fin n → ℝ))
    (hS : S.Nonempty) (phi : Fin n → ℝ → ℝ)
    (_hLip : ∀ i, LipschitzWith 1 (phi i)) :
    (∫ g : EuclideanSpace ℝ (Fin n), gaussianFiniteSup S hS
      (fun t g => ∑ i, g i * phi i (t i)) g
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ∫ g : EuclideanSpace ℝ (Fin n), gaussianFiniteSup S hS
        (fun t g => ∑ i, g i * t i) g
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.8.
  sorry

end HDP.Chapter7.Exercise
