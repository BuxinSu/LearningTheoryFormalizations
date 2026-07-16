/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter9.Main
import HighDimensionalProbability.Chapter9.Exercise.Sec01
import HighDimensionalProbability.Chapter9.Exercise.Sec04

/-!
# Book Chapter 9 exercises attached to Section 9.5

This leaf makes each of the source's qualitative “extend” and “with high
probability” requests quantitative.  Exercise 9.32(a) is proved in the
restricted-isometry core and has no duplicate leaf declaration.  The Haar
projection is normalized by `sqrt (n/m)` before stating RIP.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology
  Matrix.Norms.L2Operator

namespace HDP.Chapter9.Exercise

noncomputable section

/-- Restriction of a vector to a finite coordinate set, padded by zero.

**Lean implementation helper.** -/
def restrictedVector {n : ℕ} (x : Euc n) (S : Finset (Fin n)) : Euc n :=
  WithLp.toLp 2 (fun i => if i ∈ S then x i else 0)

/-- Nullspace property of order `s`. Using `card ≤ s` is equivalent to the
source's `s`-element formulation and behaves correctly when `s=n`.

**Lean implementation helper.** -/
def NullspaceProperty {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Prop :=
  ∀ h : Euc n, h ≠ 0 → matrixApply A h = 0 →
    ∀ S : Finset (Fin n), S.card ≤ s →
      ellOneNorm (restrictedVector h S) <
        ellOneNorm (restrictedVector h Sᶜ)

/-- Uniform uniqueness of basis pursuit for all `s`-sparse signals.

**Lean implementation helper.** -/
def UniformUniqueL1Recovery {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Prop :=
  ∀ x : Euc n, IsSparse s x → ∀ z : Euc n,
    matrixApply A z = matrixApply A x →
      ellOneNorm z ≤ ellOneNorm x → z = x

/-- Restricted isometry of a linear-looking map on `s`-sparse vectors.

**Lean implementation helper.** -/
def SparseRestrictedIsometry {n : ℕ}
    (Q : Euc n → Euc n) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x : Euc n, IsSparse s x →
    (1 - δ) * ‖x‖ ≤ ‖Q x‖ ∧ ‖Q x‖ ≤ (1 + δ) * ‖x‖

/-- **Exercise 9.31 (noisy measurements).** The recovery program is basis
pursuit denoising. The source does not print a rate; the standard normalized
error `C η / sqrt m` and the exact-recovery tail are made explicit.

**Book Exercise 9.31.** -/
theorem exercise_9_31 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n s : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (x : Euc n) (w : Ω → Euc m) (xhat : Ω → Euc n)
        (K η : ℝ),
        0 < m → 2 ≤ n → 1 ≤ s → s ≤ n → IsSparse s x →
        1 ≤ K → 0 ≤ η →
        C * K ^ 4 * s * Real.log (Real.exp 1 * n / s) ≤ m →
        A.AEMeasurableEntries μ → A.IsotropicRows μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        A.RowPsi2Bound μ K → (∀ ω, ‖w ω‖ ≤ η) →
        (∀ ω, ‖matrixApply (A ω) (xhat ω) -
          (matrixApply (A ω) x + w ω)‖ ≤ η) →
        (∀ ω z, ‖matrixApply (A ω) z -
            (matrixApply (A ω) x + w ω)‖ ≤ η →
          ellOneNorm (xhat ω) ≤ ellOneNorm z) →
        MeasurableSet {ω | ‖xhat ω - x‖ ≤ C * η / Real.sqrt m} →
        μ.real {ω | ‖xhat ω - x‖ ≤ C * η / Real.sqrt m} ≥
          1 - 2 * Real.exp (-c * m / K ^ 4) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.31.
  sorry

/-- **Exercise 9.32(b) (random matrices have the nullspace property).**.

**Book Exercise 9.32(b).** -/
theorem exercise_9_32_part_b :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n s : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) (K : ℝ),
        0 < m → 2 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ K →
        C * K ^ 4 * s * Real.log (Real.exp 1 * n / s) ≤ m →
        A.AEMeasurableEntries μ → A.IsotropicRows μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        A.RowPsi2Bound μ K →
        MeasurableSet {ω | NullspaceProperty (A ω) s} →
        μ.real {ω | NullspaceProperty (A ω) s} ≥
          1 - 2 * Real.exp (-c * m / K ^ 4) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.32(b).
  sorry

/-- **Exercise 9.33(a) (Haar projections satisfy RIP).** The range remains
in the ambient Euclidean space, but the projection is normalized by
`sqrt (n/m)` as required for unit-scale isometry.

**Book Exercise 9.33(a).** -/
theorem exercise_9_33_part_a :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n s : ℕ}, 0 < m → m ≤ n → 2 ≤ n →
        1 ≤ s → s ≤ m → ∀ {δ : ℝ}, 0 < δ → δ < 1 →
        C * δ⁻¹ ^ 2 * s * Real.log (Real.exp 1 * n / s) ≤ m →
        MeasurableSet {P : HDP.Chapter5.Grassmannian n m |
          SparseRestrictedIsometry
            (fun x => Real.sqrt ((n : ℝ) / m) •
              HDP.Chapter5.randomProjection P x) s δ} →
        (HDP.Chapter5.grassmannHaarMeasure n m).real
            {P | SparseRestrictedIsometry
              (fun x => Real.sqrt ((n : ℝ) / m) •
                HDP.Chapter5.randomProjection P x) s δ} ≥
          1 - 2 * Real.exp (-c * δ ^ 2 * m) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.33(a).
  sorry

/-- **Exercise 9.33(b) (exact recovery from random projections).**.

**Book Exercise 9.33(b).** -/
theorem exercise_9_33_part_b :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n s : ℕ}, 0 < m → m ≤ n → 2 ≤ n →
        1 ≤ s → s ≤ m →
        C * s * Real.log (Real.exp 1 * n / s) ≤ m →
        MeasurableSet {P : HDP.Chapter5.Grassmannian n m |
          ∀ x : Euc n, IsSparse s x → ∀ z : Euc n,
            HDP.Chapter5.randomProjection P z =
                HDP.Chapter5.randomProjection P x →
              ellOneNorm z ≤ ellOneNorm x → z = x} →
        (HDP.Chapter5.grassmannHaarMeasure n m).real
            {P | ∀ x : Euc n, IsSparse s x → ∀ z : Euc n,
              HDP.Chapter5.randomProjection P z =
                  HDP.Chapter5.randomProjection P x →
                ellOneNorm z ≤ ellOneNorm x → z = x} ≥
          1 - 2 * Real.exp (-c * m) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.33(b).
  sorry

end

end HDP.Chapter9.Exercise
