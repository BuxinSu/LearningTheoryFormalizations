import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher

/-!
# Book Chapter 1 Exercise folder: Section 1.6

Only the non-load-bearing Exercise 1.18 remains in this leaf.  Exercises
1.14–1.17 and the duality statement proved by Exercise 1.19 are declared only
in core modules because the body or later chapters consume them.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal BigOperators Topology unitInterval

namespace HDP.Chapter1

/- EXERCISE-SORRY (category A): Exercise 1.18 is not used by the main line. -/
/-- In finite dimension, the `ℓᵖ` norm tends to the `ℓ∞` norm as `p → ∞`;
for positive `p ≥ log n`, it lies between `ℓ∞` and `e · ℓ∞`.

`EXERCISE-SORRY`: exact corrected statement, deliberately deferred as non-load-bearing.

**Book Exercise 1.18.** -/
theorem exercise_1_18 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    Tendsto (fun p : ℝ => lpNorm p x) atTop (𝓝 (linftyNorm x)) ∧
      ∀ p : ℝ, 0 < p → Real.log n ≤ p →
        linftyNorm x ≤ lpNorm p x ∧
          lpNorm p x ≤ Real.exp 1 * linftyNorm x := by
  sorry

end HDP.Chapter1
