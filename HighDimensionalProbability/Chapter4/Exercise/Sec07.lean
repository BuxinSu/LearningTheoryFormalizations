import HighDimensionalProbability.Prelude.RandomMatrix

/-!
# Chapter 4 exercises attached to Section 4.7
-/

open Matrix MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators

namespace HDP.Chapter4.Exercise

/-- This is the relative covariance estimate for independent copies of one centered
distribution. Positive definiteness replaces the printed bare invertibility assumption and
justifies every denominator. The directional ψ₂ hypothesis is the coordinate-free form of the
standardized subgaussian bound in (4.29).

**Book Exercise 4.48.** -/
theorem exercise_4_48 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ} [NeZero m] [NeZero n]
        (X : Fin m → Ω → EuclideanSpace ℝ (Fin n))
        (S : Matrix (Fin n) (Fin n) ℝ),
        (∀ r, AEMeasurable (X r) P) → iIndepFun X P →
        (∀ r s, Measure.map (X r) P = Measure.map (X s) P) →
        (∀ r i, ∫ ω, X r ω i ∂P = 0) →
        (∀ r, HDP.secondMomentMatrix (X r) P = S) →
        (∀ r, HDP.SubGaussianVector (X r) P) → S.PosDef →
        ∀ {K : ℝ}, 0 < K →
        (∀ r v, HDP.psi2Norm (fun ω => inner ℝ (X r ω) v) P ≤
          K * Real.sqrt (∑ i, ∑ j, v i * S i j * v j)) →
        ∫ ω, ⨆ v : {v : EuclideanSpace ℝ (Fin n) // v ≠ 0},
          |((∑ i, ∑ j, v.1 i *
                (HDP.sampleSecondMoment m (fun r => X r ω)) i j * v.1 j) /
              (∑ i, ∑ j, v.1 i * S i j * v.1 j)) - 1| ∂P ≤
          C * K ^ 2 *
            (Real.sqrt ((n : ℝ) / (m : ℝ)) + (n : ℝ) / (m : ℝ)) := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 4.48.
  sorry

/-- Low-rank Frobenius unit ball, with the corrected `rank ≤ r` convention.

**Lean implementation helper.** -/
def lowRankFrobeniusBall (m n r : ℕ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | A.rank ≤ r ∧ HDP.matrixFrobeniusNorm A ≤ 1}

/-- Covering orthonormal-column matrices. The net is internal, `1 ≤ r ≤ m`, and the absolute
constant is independent of all dimensions and of `ε`. The printed pure-power bound is stated on
its necessary small-scale range `0 < ε ≤ 1`.

**Book Exercise 4.50(a).** -/
theorem exercise_4_50a :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∃ N : Finset (Matrix (Fin m) (Fin r) ℝ),
          (N.card : ℝ) ≤ (C / ε) ^ (m * r) ∧
          (N : Set (Matrix (Fin m) (Fin r) ℝ)) ⊆ {A | Aᵀ * A = 1} ∧
          ∀ A : Matrix (Fin m) (Fin r) ℝ, Aᵀ * A = 1 →
            ∃ B ∈ N, ∀ j, ‖WithLp.toLp 2 (fun i => (A - B) i j)‖ ≤ ε := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.50(a).
  sorry

/-- Constructs a small internal net for the Frobenius unit ball of matrices of rank at most `r`.

**Book Exercise 4.50(b).** -/
theorem exercise_4_50b :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n r : ℕ), 1 ≤ r → r ≤ min m n → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∃ N : Finset (Matrix (Fin m) (Fin n) ℝ),
          (N.card : ℝ) ≤ (C / ε) ^ ((m + n + 1) * r) ∧
          (N : Set (Matrix (Fin m) (Fin n) ℝ)) ⊆
            lowRankFrobeniusBall m n r ∧
          ∀ A ∈ lowRankFrobeniusBall m n r,
            ∃ B ∈ N, HDP.matrixFrobeniusNorm (A - B) ≤ ε := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 4.50(b).
  sorry

/-- A `2ε`-separated internal packing is the standard witness for the covering-number lower
bound. The exponent is a real half-dimension, rather than truncated natural division.

**Book Exercise 4.50(c).** -/
theorem exercise_4_50c :
    ∃ c : ℝ, 0 < c ∧
      ∀ (m n r : ℕ), 1 ≤ r → r ≤ min m n → ∀ {ε : ℝ}, 0 < ε →
        ∃ N : Finset (Matrix (Fin m) (Fin n) ℝ),
          Real.rpow (c / ε) (((m + n : ℕ) : ℝ) * r / 2) ≤ (N.card : ℝ) ∧
          (N : Set (Matrix (Fin m) (Fin n) ℝ)) ⊆
            lowRankFrobeniusBall m n r ∧
          Set.Pairwise (N : Set (Matrix (Fin m) (Fin n) ℝ))
            (fun A B => 2 * ε < HDP.matrixFrobeniusNorm (A - B)) := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 4.50(c).
  sorry

end HDP.Chapter4.Exercise
