import HighDimensionalProbability.Chapter4_RandomMatrices
import HighDimensionalProbability.Prelude.Sphere

/-!
# Chapter 4 exercises attached to Section 4.1

These are isolated category-A declarations.  None is imported by Chapter 4
core.  Printed rectangular powers in Exercise 4.6 are corrected to square
matrices, and every finite maximum carries nonempty-index hypotheses.
-/

open Matrix WithLp Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace Topology

namespace HDP.Chapter4.Exercise

/-- A square matrix is invertible exactly when all of its singular values are nonzero.

**Book Exercise 4.1(a).** -/
theorem exercise_4_1a {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUnit A ↔ ∀ i : Fin n, HDP.matrixSingularValue A i ≠ 0 := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.1(a).
  sorry

/-- Inversion swaps the left and right singular vectors.

**Book Exercise 4.1(b).** -/
theorem exercise_4_1b {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (svd : HDP.Chapter4.RealSVD A) (hs : ∀ i, svd.singularValue i ≠ 0) :
    A⁻¹ = ∑ i, (svd.singularValue i)⁻¹ •
      HDP.Chapter4.outerMatrix (svd.right i) (svd.left i) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.1(b).
  sorry

/-- Zero-based singular-value bound.

**Book Exercise 4.5.** -/
theorem exercise_4_5 {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ min m n) :
    HDP.matrixSingularValue A (k - 1) ≤
      HDP.matrixFrobeniusNorm A / Real.sqrt k := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.5.
  sorry

/-- The printed rectangular power is ill-typed, and for a general nonnormal square matrix the
limit detects the spectral radius rather than the operator norm.

**Book Exercise 4.6.** -/
theorem exercise_4_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂stdGaussian (EuclideanSpace ℝ (Fin n)),
      Tendsto (fun p : ℕ =>
        (‖(A ^ p).toEuclideanLin x‖ : ℝ) ^ (1 / (p : ℝ))) atTop
        (𝓝 (HDP.matrixOpNorm A)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.6.
  sorry

/-- Bounds the operator norm by the geometric mean of the largest absolute row and column sums.

**Book Exercise 4.8.** -/
theorem exercise_4_8 {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm A ≤ Real.sqrt
      ((⨆ i : Fin m, ∑ j : Fin n, |A i j|) *
        (⨆ j : Fin n, ∑ i : Fin m, |A i j|)) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.8.
  sorry

/-- Every square sign matrix has norm between `√n` and `n`.

**Book Exercise 4.10(a).** -/
theorem exercise_4_10a {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, |A i j| = 1) :
    Real.sqrt n ≤ HDP.matrixOpNorm A ∧ HDP.matrixOpNorm A ≤ n := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.10(a).
  sorry

/- The endpoint-achievability clause of Exercise 4.10 is a pure infinite
construction request.  It is recorded and skipped under the
constructive-witness policy rather than represented by a deferred theorem. -/

/-- A matrix is an orthogonal projection in the Euclidean realization.

**Lean implementation helper.** -/
def IsOrthogonalProjectionMatrix {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.IsSymm ∧ P * P = P

/-- Shows that two Euclidean orthogonal projections differ by operator norm at most one.

**Book Exercise 4.11.** -/
theorem exercise_4_11 {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsOrthogonalProjectionMatrix P) (hQ : IsOrthogonalProjectionMatrix Q) :
    HDP.matrixOpNorm (P - Q) ≤ 1 := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.11.
  sorry

/-- Controls the difference of leading left singular projections by the perturbation norm
divided by the singular-value gap.

**Book Exercise 4.15.** -/
theorem exercise_4_15_left {m n k : ℕ} (hk : 1 ≤ k) (hkn : k < min m n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (a : HDP.Chapter4.RealSVD A)
    (b : HDP.Chapter4.RealSVD B)
    (hgap : 0 < a.singularValue ⟨k - 1, by omega⟩ -
      a.singularValue ⟨k, hkn⟩) :
    HDP.matrixOpNorm
      ((∑ i : Fin k, HDP.Chapter4.outerMatrix
          (a.left (Fin.castLE hkn.le i)) (a.left (Fin.castLE hkn.le i))) -
       (∑ i : Fin k, HDP.Chapter4.outerMatrix
          (b.left (Fin.castLE hkn.le i)) (b.left (Fin.castLE hkn.le i)))) ≤
      2 * HDP.matrixOpNorm (A - B) /
        (a.singularValue ⟨k - 1, by omega⟩ - a.singularValue ⟨k, hkn⟩) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.15, left part.
  sorry

/-- Controls the difference of leading right singular projections by the perturbation norm
divided by the singular-value gap.

**Book Exercise 4.15.** -/
theorem exercise_4_15_right {m n k : ℕ} (hk : 1 ≤ k) (hkn : k < min m n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (a : HDP.Chapter4.RealSVD A)
    (b : HDP.Chapter4.RealSVD B)
    (hgap : 0 < a.singularValue ⟨k - 1, by omega⟩ -
      a.singularValue ⟨k, hkn⟩) :
    HDP.matrixOpNorm
      ((∑ i : Fin k, HDP.Chapter4.outerMatrix
          (a.right (Fin.castLE hkn.le i)) (a.right (Fin.castLE hkn.le i))) -
       (∑ i : Fin k, HDP.Chapter4.outerMatrix
          (b.right (Fin.castLE hkn.le i)) (b.right (Fin.castLE hkn.le i)))) ≤
      2 * HDP.matrixOpNorm (A - B) /
        (a.singularValue ⟨k - 1, by omega⟩ - a.singularValue ⟨k, hkn⟩) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.15, right part.
  sorry

/-- This is the corrected Wedin/Davis--Kahan form for the `k`th left and right singular vectors.
The chosen singular value is isolated from every other singular value and from zero; these
hypotheses also cover rectangular null-space directions.

**Book Exercise 4.15.** -/
theorem exercise_4_15_singularVectors {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (a : HDP.Chapter4.RealSVD A)
    (b : HDP.Chapter4.RealSVD B) (k : Fin (min m n)) {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : ∀ i : Fin (min m n), i ≠ k →
      δ ≤ |a.singularValue k - a.singularValue i|)
    (hzero : δ ≤ a.singularValue k) :
    Real.sqrt (1 - |inner ℝ (a.left k) (b.left k)| ^ 2) ≤
        2 * HDP.matrixOpNorm (A - B) / δ ∧
      Real.sqrt (1 - |inner ℝ (a.right k) (b.right k)| ^ 2) ≤
        2 * HDP.matrixOpNorm (A - B) / δ := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.15, vector part.
  sorry

/-- Exact isometries are precisely matrices whose codomain Gram matrix is a rank-`n` orthogonal
projection.

**Book Exercise 4.17(a).** -/
theorem exercise_4_17a {m n : ℕ} (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Aᵀ * A = 1 ↔ ∃ P : Matrix (Fin m) (Fin m) ℝ,
      IsOrthogonalProjectionMatrix P ∧
      Module.finrank ℝ P.toEuclideanLin.range = n ∧ A * Aᵀ = P := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.17(a).
  sorry

/-- Characterizes approximate isometries through closeness of the codomain Gram matrix to an
orthogonal projection.

**Book Exercise 4.17(b).** -/
theorem exercise_4_17b {m n : ℕ} (hnm : n ≤ m) (ε : ℝ) (hε : 0 ≤ ε)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm (Aᵀ * A - 1) ≤ ε ↔
      ∃ P : Matrix (Fin m) (Fin m) ℝ,
        IsOrthogonalProjectionMatrix P ∧
        Module.finrank ℝ P.toEuclideanLin.range = n ∧
        HDP.matrixOpNorm (A * Aᵀ - P) ≤ ε := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.17(b).
  sorry

/-- The rectangular Grothendieck vector SDP has the explicit universal approximation factor
proved in Chapter 3.

**Book Exercise 4.22.** -/
theorem exercise_4_22_inftyToOne
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    [Nonempty κ] (A : Matrix m n ℝ)
    (C : ℝ) (hC : ∀ x : m → ℝ, (∀ i, x i = -1 ∨ x i = 1) →
      ∀ y : n → ℝ, (∀ j, y j = -1 ∨ y j = 1) →
        |∑ i, ∑ j, A i j * x i * y j| ≤ C)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |∑ i, ∑ j, A i j * inner ℝ (X i) (Y j)| ≤
      (1783 / 1000 : ℝ) * C := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.22.
  sorry

/-- Squaring the norm turns the sign optimum into the positive-semidefinite quadratic form
associated with `AᵀA`; its vector SDP relaxation loses at most an absolute factor.

**Book Exercise 4.22.** -/
theorem exercise_4_22_inftyToTwo
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    [Nonempty κ] (A : Matrix m n ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hSign : ∀ x : n → ℝ, (∀ i, x i = -1 ∨ x i = 1) →
      ∑ i, ∑ j, (Aᵀ * A) i j * x i * x j ≤ C)
    (X : n → EuclideanSpace ℝ κ) (hX : ∀ i, ‖X i‖ = 1) :
    ∑ i, ∑ j, (Aᵀ * A) i j * inner ℝ (X i) (X j) ≤ 2 * C := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.22 (`∞→2`).
  sorry

/-- Combining the four-factor comparison in the corresponding exercise with rectangular
Grothendieck gives an SDP approximation of the cut norm. The source accidentally lists the cut
norm twice; this is the corrected third distinct comparison.

**Book Exercise 4.22.** -/
theorem exercise_4_22_cut
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    [Nonempty κ] (A : Matrix m n ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hCut : ∀ I : Finset m, ∀ J : Finset n,
      |∑ i ∈ I, ∑ j ∈ J, A i j| ≤ C)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |∑ i, ∑ j, A i j * inner ℝ (X i) (Y j)| ≤
      (1783 / 250 : ℝ) * C := by
  -- EXERCISE-SORRY: category A; corrected cut-norm part of Exercise 4.22.
  sorry

end HDP.Chapter4.Exercise
