import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import HighDimensionalProbability.Chapter4_RandomMatrices

/-!
# Chapter 5 exercises attached to Section 5.6

Only Exercises 5.30--5.32 are non-load-bearing.  Their open-ended wording is
replaced by precise sampling statements, and the false `N/n` factor in 5.32
is corrected to the unbiased `N/m` factor.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace

namespace HDP.Chapter5.Exercise

/-- Empirical frame operator, normalized for sampling with replacement.

**Lean implementation helper.** -/
noncomputable def sampledFrameOperator {n M N : ℕ}
    (u : Fin M → EuclideanSpace ℝ (Fin n)) (I : Fin N → Fin M) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((M : ℝ) / (N : ℝ)) •
    ∑ j, HDP.Chapter4.outerProductMatrix (u (I j))

/-- Gives a high-probability near-isometry bound for sampling an equal-norm Parseval frame.

**Book Exercise 5.30.** -/
theorem exercise_5_30 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n M N : ℕ} [NeZero M] [NeZero N]
        (u : Fin M → EuclideanSpace ℝ (Fin n)),
        HDP.IsParsevalFrame u →
        (∀ i, ‖u i‖ ^ 2 = (n : ℝ) / M) →
        ∀ {ε δ : ℝ}, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        C * (n : ℝ) * (Real.log n + Real.log (δ⁻¹)) ≤ N * ε ^ 2 →
        (Measure.pi (fun _ : Fin N =>
          uniformOn (Set.univ : Set (Fin M))))
          {I | HDP.matrixOpNorm (sampledFrameOperator u I - 1) ≤ ε} ≥
            ENNReal.ofReal (1 - δ) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 5.30.
  sorry

/-- Controls every singular value of a matrix with independent isotropic bounded rows.

**Book Exercise 5.31.** -/
theorem exercise_5_31 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ} (hn : 2 ≤ n) (hmn : n ≤ m)
        (X : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun X P → (∀ i, AEMeasurable (X i) P) →
        (∀ i j, Measure.map (X i) P = Measure.map (X j) P) →
        (∀ i, HDP.IsIsotropic (X i) P) →
        ∀ {K t : ℝ}, 1 ≤ K → 1 ≤ t →
        (∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ K * Real.sqrt n) →
        P {ω | ∀ j : Fin n,
          |HDP.matrixSingularValue
              (fun i a => X i ω a : Matrix (Fin m) (Fin n) ℝ) j -
              Real.sqrt m| ≤ C * K * t * Real.sqrt (n * Real.log n)} ≥
          ENNReal.ofReal (1 - Real.exp (-t ^ 2 * n * Real.log n)) := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 5.31.
  sorry

/-- Matrix formed by sampling `m` rows of `A` with replacement.

**Lean implementation helper.** -/
def sampledRows {N n m : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (I : Fin m → Fin N) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => A (I i) j

/-- Shows that uniformly sampled and unbiasedly rescaled rows preserve all squared singular
values.

**Book Exercise 5.32.** -/
theorem exercise_5_32 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N n m : ℕ} (hn : 2 ≤ n) [NeZero N] [NeZero m]
        (A : Matrix (Fin N) (Fin n) ℝ),
        C * (n : ℝ) * Real.log n ≤ m →
        (Measure.pi (fun _ : Fin m =>
          uniformOn (Set.univ : Set (Fin N))))
          {I | ∀ j : Fin n,
            |HDP.matrixSingularValue A j ^ 2 -
              (N : ℝ) / m *
                HDP.matrixSingularValue (sampledRows A I) j ^ 2| ≤
              (1 / 10 : ℝ) * HDP.matrixSingularValue A 0 ^ 2} ≥
            (9 / 10 : ℝ≥0∞) := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 5.32.
  sorry

end HDP.Chapter5.Exercise
