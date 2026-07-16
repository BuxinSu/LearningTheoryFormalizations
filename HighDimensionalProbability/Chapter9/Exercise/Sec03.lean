/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter9.Main
import HighDimensionalProbability.Chapter9.Exercise.Sec01

/-!
# Book Chapter 9 exercises attached to Section 9.3

Exercise 9.12 is promoted to core.  Exercise 9.15 is a tightness-witness task
and is recorded as a deliberate non-proof skip.  Exercise 9.14(b)'s final
intuition prompt is likewise prose; its mathematical radius identity is
formalized below.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology
  Matrix.Norms.L2Operator

namespace HDP.Chapter9.Exercise

noncomputable section

/-- Section of a Euclidean set by the kernel of a rectangular matrix.

**Lean implementation helper.** -/
def matrixKernelSection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (T : Set (Euc n)) : Set (Euc n) :=
  {x ∈ T | matrixApply A x = 0}

/-- Unit `ℓᵖ` ball in Euclidean coordinate space.

**Lean implementation helper.** -/
def lpUnitBall (n : ℕ) (p : ℝ) : Set (Euc n) :=
  {x | HDP.Chapter1.lpNorm p x ≤ 1}

/-- Section of a set by the range of a Grassmannian projection.

**Lean implementation helper.** -/
def grassmannSection {n k : ℕ} (P : HDP.Chapter5.Grassmannian n k)
    (T : Set (Euc n)) : Set (Euc n) :=
  {x ∈ T | HDP.Chapter5.randomProjection P x = x}

/-- Radius of the largest origin-centered Euclidean ball contained in `T`.

**Lean implementation helper.** -/
def euclideanInradius {n : ℕ} (T : Set (Euc n)) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ Metric.closedBall (0 : Euc n) r ⊆ T}

/-- Radius of the smallest origin-centered Euclidean ball containing `T`.

**Lean implementation helper.** -/
def euclideanCircumradius {n : ℕ} (T : Set (Euc n)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ T ⊆ Metric.closedBall (0 : Euc n) r}

/-- Rotation of a subset of the Euclidean unit sphere.

**Lean implementation helper.** -/
def rotatedSphereSet {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Set (Metric.sphere (0 : Euc n) 1)) :
    Set (Metric.sphere (0 : Euc n) 1) :=
  HDP.unitSphereHomeomorph
      (HDP.Chapter5.orthogonalLinearIsometryEquiv U) '' T

/-- **Exercise 9.13 (high-probability `M*` bound).** The exercise prompt
does not print its tail. This declaration supplies the standard confidence
parameter form inherited from the matrix-deviation tail estimate.

**Book Exercise 9.13.** -/
theorem exercise_9_13 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (T : Set (Euc n)) (K u : ℝ),
        0 < m → 0 < n → T.Nonempty → Bornology.IsBounded T →
        1 ≤ K → 0 ≤ u →
        A.AEMeasurableEntries μ → A.IsotropicRows μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        A.RowPsi2Bound μ K →
        MeasurableSet {ω |
          setDiameter (matrixKernelSection (A ω) T) ≤
            C * K ^ 2 *
              (setGaussianWidth T + u * setRadius T) / Real.sqrt m} →
        μ.real {ω |
          setDiameter (matrixKernelSection (A ω) T) ≤
            C * K ^ 2 *
              (setGaussianWidth T + u * setRadius T) / Real.sqrt m} ≥
          1 - 2 * Real.exp (-u ^ 2) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.13.
  sorry

/-- **Exercise 9.14(a) (random sections of `ℓᵖ` balls).** Constants are
quantified after `p`, so the comparison is precisely `asymp_p`. The integer
condition `100 k ≤ 99 n` is the safe exact rendering of `k ≤ 0.99 n`.

**Book Exercise 9.14(a).** -/
theorem exercise_9_14_part_a :
    ∀ p : ℝ, 1 < p →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ {n k : ℕ}, 0 < n → 0 < k → 100 * k ≤ 99 * n →
          Measurable (fun P : HDP.Chapter5.Grassmannian n k =>
            setDiameter (grassmannSection P (lpUnitBall n p))) →
          Integrable (fun P : HDP.Chapter5.Grassmannian n k =>
            setDiameter (grassmannSection P (lpUnitBall n p)))
              (HDP.Chapter5.grassmannHaarMeasure n k) →
          c * Real.rpow n ((1 : ℝ) / 2 - 1 / p) ≤
            (∫ P, setDiameter (grassmannSection P (lpUnitBall n p))
              ∂HDP.Chapter5.grassmannHaarMeasure n k) ∧
          (∫ P, setDiameter (grassmannSection P (lpUnitBall n p))
              ∂HDP.Chapter5.grassmannHaarMeasure n k) ≤
            C * Real.rpow n ((1 : ℝ) / 2 - 1 / p) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.14(a).
  sorry

/-- **Exercise 9.14(b) (Euclidean inradius/circumradius).** This is the
mathematical equivalence requested by the source. The subsequent request for
an intuitive explanation is not a proof proposition and is not encoded.

**Book Exercise 9.14(b).** -/
theorem exercise_9_14_part_b :
    ∀ {n : ℕ}, 0 < n → ∀ {p : ℝ}, 1 < p →
      (p ≤ 2 →
        euclideanInradius (lpUnitBall n p) =
          Real.rpow n ((1 : ℝ) / 2 - 1 / p)) ∧
      (2 ≤ p →
        euclideanCircumradius (lpUnitBall n p) =
          Real.rpow n ((1 : ℝ) / 2 - 1 / p)) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.14(b).
  sorry

/-- **Exercise 9.16 (putting a sticker on the soccer ball).** The mark set
is explicitly finite and nonempty, and the sticker is measurable for the
normalized surface probability.

**Book Exercise 9.16.** -/
theorem exercise_9_16 :
    ∀ {n : ℕ}, 0 < n →
      ∀ (T : Set (Metric.sphere (0 : Euc n) 1))
        (X : Finset (Metric.sphere (0 : Euc n) 1)),
        MeasurableSet T → X.Nonempty →
        (HDP.unitSphereMeasure (Euc n)).real T <
          1 / (X.card : ℝ) →
        ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
          rotatedSphereSet U T ∩ (X : Set _) = ∅ := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.16.
  sorry

end

end HDP.Chapter9.Exercise
