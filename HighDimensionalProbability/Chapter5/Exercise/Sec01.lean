import HighDimensionalProbability.Chapter4_RandomMatrices

/-!
# Chapter 5 exercises attached to Section 5.1

Only non-load-bearing Exercise 5.2 lives here.  Exercises 5.1 and 5.3--5.7
are part of the Chapter 5 proof chain and therefore have their authoritative
proved declarations in core.
-/

open InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace HDP.Chapter5.Exercise

/-- A linear functional has its vector norm as a valid Lipschitz constant. The reverse
inequality, and hence sharpness, follows by testing on the normalized vector when it is nonzero.

**Book Example 5.1.2.** -/
theorem exercise_5_2a {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) :
    LipschitzWith ⟨‖a‖, norm_nonneg a⟩
      (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ a x) ∧
    (∀ K : ℝ≥0, LipschitzWith K
        (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ a x) → ‖a‖ ≤ (K : ℝ)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 5.2(a).
  sorry

/-- An `m × n` matrix acts from `ℝⁿ` to `ℝᵐ`, and its operator norm is its sharp Lipschitz
constant.

**Book Example 5.1.2.** -/
theorem exercise_5_2b {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    LipschitzWith ⟨HDP.matrixOpNorm A, HDP.matrixOpNorm_nonneg A⟩
      A.toEuclideanLin ∧
    (∀ K : ℝ≥0, LipschitzWith K A.toEuclideanLin →
      HDP.matrixOpNorm A ≤ (K : ℝ)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 5.2(b).
  sorry

/-- The norm map is one-Lipschitz on every real normed space; the constant is sharp on every
nontrivial space.

**Book Example 5.1.2.** -/
theorem exercise_5_2c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] :
    LipschitzWith 1 (fun x : E => ‖x‖) ∧
      ∀ K : ℝ≥0, LipschitzWith K (fun x : E => ‖x‖) → (1 : ℝ) ≤ K := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 5.2(c).
  sorry

end HDP.Chapter5.Exercise
