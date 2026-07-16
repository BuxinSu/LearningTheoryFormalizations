/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter9.Main
import HighDimensionalProbability.Chapter9.Exercise.Sec01

/-!
# Book Chapter 9 exercises attached to Section 9.2

Exercise 9.9 is promoted to the covariance-estimation core.  Exercise 9.11
is a nonproof counterexample task; its explicit useful witness is extracted
and proved in the thematic core, with no Exercise-leaf wrapper.  This leaf
contains the three remaining non-load-bearing proof exercises.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology
  Matrix.Norms.L2Operator

namespace HDP.Chapter9.Exercise

noncomputable section

/-- Scalar multiplication of a rectangular real matrix.

**Lean implementation helper.** -/
def scaledMatrix {m n : ℕ} (c : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  c • A

/-- Image of a set under a genuine Grassmannian orthogonal projection.

**Lean implementation helper.** -/
def projectionImage {m n : ℕ} (P : HDP.Chapter5.Grassmannian n m)
    (T : Set (Euc n)) : Set (Euc n) :=
  HDP.Chapter5.randomProjection P '' T

/-- Relative Euclidean isometry on a finite point cloud.

**Lean implementation helper.** -/
def IsEpsilonIsometryOn {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Finset (Euc n))
    (ε : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * ‖x - y‖ ≤ ‖matrixApply Q x - matrixApply Q y‖ ∧
      ‖matrixApply Q x - matrixApply Q y‖ ≤ (1 + ε) * ‖x - y‖

/-- **Exercise 9.7 (projected diameter, high probability).** The matrix is
normalized by `1 / sqrt n`, exactly as in the source's subgaussian-projection
model. The event is required to be measurable because the printed
probability is real-valued.

**Book Exercise 9.7.** -/
theorem exercise_9_7 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (T : Set (Euc n)) (K ε : ℝ),
        0 < m → 0 < n → T.Nonempty → Bornology.IsBounded T →
        1 ≤ K → 0 < ε →
        A.AEMeasurableEntries μ → A.IsotropicRows μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        A.RowPsi2Bound μ K →
        MeasurableSet {ω |
          setDiameter
              (matrixImage
                (scaledMatrix (Real.sqrt n)⁻¹ (A ω)) T) ≤
            (1 + ε) * Real.sqrt ((m : ℝ) / n) * setDiameter T +
              C * K ^ 2 * setSphericalWidth T} →
        μ.real {ω |
          setDiameter
              (matrixImage
                (scaledMatrix (Real.sqrt n)⁻¹ (A ω)) T) ≤
            (1 + ε) * Real.sqrt ((m : ℝ) / n) * setDiameter T +
              C * K ^ 2 * setSphericalWidth T} ≥
          1 - Real.exp (-c * ε ^ 2 * m / K ^ 4) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.7.
  sorry

/-- **Exercise 9.8 (sizes of true random projections).** This is the Haar
Grassmannian counterpart of Proposition 9.2.1, with the source's exact
`sqrt (m/n)` diameter scale and spherical-width error.

**Book Exercise 9.8.** -/
theorem exercise_9_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Set (Euc n)), T.Nonempty → Bornology.IsBounded T →
        (∀ P : HDP.Chapter5.Grassmannian n m,
          BddAbove {r : ℝ | ∃ x ∈ T, ∃ y ∈ T,
          r = ‖HDP.Chapter5.randomProjection P x -
            HDP.Chapter5.randomProjection P y‖}) →
        Measurable (fun P : HDP.Chapter5.Grassmannian n m =>
          setDiameter (projectionImage P T)) →
        Integrable (fun P : HDP.Chapter5.Grassmannian n m =>
          setDiameter (projectionImage P T))
            (HDP.Chapter5.grassmannHaarMeasure n m) →
        (∫ P, setDiameter (projectionImage P T)
          ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
            Real.sqrt ((m : ℝ) / n) * setDiameter T +
              C * setSphericalWidth T := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.8.
  sorry

/-- **Exercise 9.10 (subgaussian Johnson--Lindenstrauss).** The success
probability and the `K⁴` dependence suppressed by the exercise prompt are
made explicit.

**Book Exercise 9.10.** -/
theorem exercise_9_10 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (X : Finset (Euc n)) (K ε : ℝ),
        0 < m → 0 < n → 2 ≤ X.card → 1 ≤ K →
        0 < ε → ε < 1 →
        A.AEMeasurableEntries μ → A.IsotropicRows μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        A.RowPsi2Bound μ K →
        C * K ^ 4 * ε⁻¹ ^ 2 * Real.log X.card ≤ m →
        MeasurableSet {ω |
          IsEpsilonIsometryOn
            (scaledMatrix (Real.sqrt m)⁻¹ (A ω)) X ε} →
        μ.real {ω |
          IsEpsilonIsometryOn
            (scaledMatrix (Real.sqrt m)⁻¹ (A ω)) X ε} ≥
          1 - 2 * Real.exp (-c * ε ^ 2 * m / K ^ 4) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.10.
  sorry

end

end HDP.Chapter9.Exercise
