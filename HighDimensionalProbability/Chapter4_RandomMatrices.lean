/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Prelude.Matrix
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import HighDimensionalProbability.Prelude.RandomVector
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.UnitaryGroup
import HighDimensionalProbability.Prelude.MetricEntropy
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Bases
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Fin.Embedding
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.LocallyConvex.Separation
import HighDimensionalProbability.Prelude.RandomMatrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Layercake
import HighDimensionalProbability.Prelude.StochasticBlockModel
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Chapter 4 — Random Matrices

## Contents

- §4.1 A quick refresher on linear algebra — compact and matrix-form SVD
  (Theorem 4.1.1, Remark 4.1.3, and Equation (4.4)),
  orthogonal projections from orthonormal columns (Example 4.1.5),
  attained general induced norms and their bilinear dual maxima (Remark 4.1.9),
  Courant--Fischer (Theorem 4.1.6), Eckart--Young--Mirsky (Theorem 4.1.13),
  and spectral perturbation (Lemma 4.1.14 and Theorem 4.1.15)
- §4.2 Nets, covering, and packing — Definitions 4.2.1--4.2.4,
  volumetric bounds (Proposition 4.2.10), and Euclidean ball covers
  (Corollary 4.2.11)
- §4.3 Error-correcting codes — metric entropy (Proposition 4.3.1) and
  efficient binary codes (Theorem 4.3.5)
- §4.4 Upper bounds on subgaussian random matrices — net reductions
  (Lemmas 4.4.1--4.4.2), the main norm bound (Theorem 4.4.3), and the
  symmetric-matrix corollary (Corollary 4.4.7)
- §4.5 Community detection in networks — the stochastic block model
  (Definition 4.5.1) and spectral recovery (Theorem 4.5.2)
- §4.6 Two-sided bounds on subgaussian matrices — extreme singular values
  (Theorem 4.6.1)
- §4.7 Covariance estimation and clustering — covariance estimation
  (Theorem 4.7.1) and Gaussian-mixture recovery (Definition 4.7.4 and
  Theorem 4.7.5)

The detailed entries below identify the chapter's key source-facing definitions and
results by the numbering printed in the second-edition book PDF.
-/

/-! ## Material formerly in `01_SingularValueDecomposition.lean` -/

section Source_01_SingularValueDecomposition

/-!
# Chapter 4, §4.1.1: singular-value decomposition

The source's final displayed sum has `vⱼ` where `vᵢ` is required.  The theorem below uses
the corrected factor.  Mathlib's singular values are zero-indexed and padded by zero.

For zero singular values the corresponding left vector is mathematically irrelevant to the
decomposition.  We therefore expose the canonical normalized image on the positive support;
an arbitrary orthonormal completion can be chosen when a square orthogonal-matrix presentation is
needed.
-/

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter4

set_option linter.unusedSectionVars false

/-- The canonical right singular-vector basis: the ordered eigenbasis of `AᵀA`.

**Lean implementation helper.** -/
noncomputable def rightSingularBasis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ))

/-- The canonical positive-support left singular vector.

**Lean implementation helper.** -/
noncomputable def leftSingularVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) : EuclideanSpace ℝ (Fin m) :=
  if _h : HDP.matrixSingularValue A i = 0 then 0
  else (HDP.matrixSingularValue A i)⁻¹ •
    A.toEuclideanLin (rightSingularBasis A i)

/-- Shows that the canonical right singular-vector basis is orthonormal.

**Lean implementation helper.** -/
lemma rightSingularBasis_orthonormal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Orthonormal ℝ (rightSingularBasis A) :=
  (rightSingularBasis A).orthonormal

/-- Shows that every singular value is nonnegative.

**Lean implementation helper.** -/
lemma singularValues_nonnegative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : ℕ) : 0 ≤ HDP.matrixSingularValue A i :=
  HDP.matrixSingularValue_nonneg A i

/-- Shows that the singular-value sequence is decreasing.

**Lean implementation helper.** -/
lemma singularValues_decreasing {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (HDP.matrixSingularValue A) :=
  HDP.matrixSingularValue_antitone A

/-- Right-hand Gram version: a right singular vector is an eigenvector of `AᵀA` with eigenvalue
`sᵢ²`.

**Book Remark 4.1.4.** -/
theorem gram_apply_rightSingularVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (rightSingularBasis A i) =
      HDP.matrixSingularValue A i ^ 2 • rightSingularBasis A i := by
  let hS := A.toEuclideanLin.isSymmetric_adjoint_comp_self
  have h := hS.apply_eigenvectorBasis (finrank_euclideanSpace_fin (𝕜 := ℝ)) i
  have hs := A.toEuclideanLin.sq_singularValues_fin
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) i
  change (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (rightSingularBasis A i) = _
  rw [show HDP.matrixSingularValue A i ^ 2 = hS.eigenvalues
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) i from hs]
  convert h using 1 <;> rfl

/-- `A` stretches the `i`th right singular vector by `sᵢ` in the canonical positive-support left
direction.

**Book Equation (4.3).** -/
theorem apply_rightSingularVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) (hi : HDP.matrixSingularValue A i ≠ 0) :
    A.toEuclideanLin (rightSingularBasis A i) =
      HDP.matrixSingularValue A i • leftSingularVector A i := by
  rw [leftSingularVector, dif_neg hi, smul_smul]
  simp [hi]

/-- Computes the norm of the image of a right singular vector.

**Lean implementation helper.** -/
lemma norm_apply_rightSingularVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ‖A.toEuclideanLin (rightSingularBasis A i)‖ = HDP.matrixSingularValue A i := by
  have hgram := gram_apply_rightSingularVector A i
  have hsq : ‖A.toEuclideanLin (rightSingularBasis A i)‖ ^ 2 =
      HDP.matrixSingularValue A i ^ 2 := by
    calc
      ‖A.toEuclideanLin (rightSingularBasis A i)‖ ^ 2 =
          inner ℝ (A.toEuclideanLin (rightSingularBasis A i))
            (A.toEuclideanLin (rightSingularBasis A i)) := by
              rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ
          ((A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (rightSingularBasis A i))
          (rightSingularBasis A i) := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
      _ = HDP.matrixSingularValue A i ^ 2 := by
            rw [hgram, inner_smul_left, real_inner_self_eq_norm_sq,
              (rightSingularBasis A).norm_eq_one]
            simp
  nlinarith [norm_nonneg (A.toEuclideanLin (rightSingularBasis A i)),
    HDP.matrixSingularValue_nonneg A i]

/-- Shows that each positive-support left singular vector has unit norm.

**Lean implementation helper.** -/
lemma norm_leftSingularVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) (hi : HDP.matrixSingularValue A i ≠ 0) :
    ‖leftSingularVector A i‖ = 1 := by
  rw [leftSingularVector, dif_neg hi, norm_smul, norm_apply_rightSingularVector]
  rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (HDP.matrixSingularValue_nonneg A i)]
  exact inv_mul_cancel₀ hi

/-- Images of distinct right singular vectors are orthogonal.

**Book (4.2).** -/
lemma inner_apply_rightSingularVector_ne {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (A.toEuclideanLin (rightSingularBasis A i))
      (A.toEuclideanLin (rightSingularBasis A j)) = 0 := by
  rw [← LinearMap.adjoint_inner_left, ← LinearMap.comp_apply,
    gram_apply_rightSingularVector, inner_smul_left]
  simp [hij]

/-- Shows that distinct positive-support left singular vectors are orthogonal.

**Lean implementation helper.** -/
lemma leftSingularVector_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {i j : Fin n} (hij : i ≠ j)
    (hi : HDP.matrixSingularValue A i ≠ 0)
    (hj : HDP.matrixSingularValue A j ≠ 0) :
    inner ℝ (leftSingularVector A i) (leftSingularVector A j) = 0 := by
  rw [leftSingularVector, dif_neg hi, leftSingularVector, dif_neg hj,
    inner_smul_left, inner_smul_right, inner_apply_rightSingularVector_ne A hij]
  simp

/-- The corrected SVD expansion uses the canonical right basis and the actual images;
`apply_rightSingularVector` rewrites every positive term as `sᵢ uᵢ`. This form also handles zero
singular values without making an arbitrary completion choice.

**Book (4.1).** -/
theorem singularValueDecomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    A.toEuclideanLin x =
      ∑ i, inner ℝ (rightSingularBasis A i) x •
        A.toEuclideanLin (rightSingularBasis A i) := by
  calc
    A.toEuclideanLin x = A.toEuclideanLin
        (∑ i, inner ℝ (rightSingularBasis A i) x • rightSingularBasis A i) := by
      rw [(rightSingularBasis A).sum_repr' x]
    _ = ∑ i, inner ℝ (rightSingularBasis A i) x •
        A.toEuclideanLin (rightSingularBasis A i) := by simp

/-- Matrix-form content of (4.1), avoiding the source's `vⱼ` typo: equality of linear maps is
certified by the corrected singular-vector expansion.

**Book Remark 4.1.3.** -/
theorem singularValueDecomposition_linearMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    A.toEuclideanLin =
      ∑ i, LinearMap.smulRight
        (innerSL ℝ (rightSingularBasis A i)).toLinearMap
        (A.toEuclideanLin (rightSingularBasis A i)) := by
  apply LinearMap.ext
  intro x
  simpa using singularValueDecomposition A x

/-- The singular values beyond the domain dimension vanish, as stipulated in the corresponding
remark.

**Book Remark 4.1.3.** -/
theorem singularValue_eq_zero_of_domain_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {i : ℕ} (hi : n ≤ i) :
    HDP.matrixSingularValue A i = 0 := by
  exact HDP.matrixSingularValue_of_finrank_le A (by simpa using hi)

/-- A matrix with orthonormal columns determines the rank-`k` orthogonal
projection `P = UUᵀ`. The conjunction records symmetry, idempotence, exact
rank, eigenvalue one on the column space, and eigenvalue zero on its orthogonal
complement.

**Book Example 4.1.5.** -/
theorem orthogonalProjection_eq_mul_transpose {n k : ℕ}
    (U : Matrix (Fin n) (Fin k) ℝ) (hU : U.transpose * U = 1) :
    let P := U * U.transpose
    P.transpose = P ∧ P * P = P ∧ P.rank = k ∧
      (∀ x, P.mulVec (U.mulVec x) = U.mulVec x) ∧
      (∀ x, U.transpose.mulVec x = 0 → P.mulVec x = 0) := by
  classical
  dsimp
  constructor
  · simp
  constructor
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U.transpose U U.transpose, hU]
    simp
  constructor
  · rw [Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self U, hU,
      Matrix.rank_one, Fintype.card_fin]
  constructor
  · intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one]
  · intro x hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-! ## Source-strength rectangular SVD -/

/-- The real outer-product matrix associated with Euclidean vectors.

**Lean implementation helper.** -/
noncomputable def outerMatrix {m n : ℕ} (u : EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp v)

/-- Under `toEuclideanLin`, the outer-product matrix `u vᵀ` induces the rank-one operator `x ↦ ⟨v,x⟩u`.

**Lean implementation helper.** -/
lemma toEuclideanLin_outerMatrix {m n : ℕ} (u : EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n)) :
    (outerMatrix u v).toEuclideanLin =
      (InnerProductSpace.rankOne ℝ u v).toLinearMap := by
  have h := congrArg
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n))
    (InnerProductSpace.symm_toEuclideanLin_rankOne u v)
  simpa [outerMatrix] using h.symm

/-- Source-facing SVD data.  The index has exactly `min m n` elements. -/
structure RealSVD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) where
  left : Fin (min m n) → EuclideanSpace ℝ (Fin m)
  right : Fin (min m n) → EuclideanSpace ℝ (Fin n)
  singularValue : Fin (min m n) → ℝ
  left_orthonormal : Orthonormal ℝ left
  right_orthonormal : Orthonormal ℝ right
  singularValue_nonneg : ∀ i, 0 ≤ singularValue i
  singularValue_antitone : Antitone singularValue
  eq_sum_outer : A = ∑ i : Fin (min m n),
    singularValue i • outerMatrix (left i) (right i)

/-- A tall real matrix (`n ≤ m`) has an SVD with `n` orthonormal left and right singular
vectors. Positive normalized images are extended to an orthonormal basis of the codomain; zero
singular terms then vanish.

**Lean implementation helper.** -/
theorem exists_tall_svd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hnm : n ≤ m) :
    ∃ (u : Fin n → EuclideanSpace ℝ (Fin m)),
      Orthonormal ℝ u ∧
      A = ∑ i : Fin n, HDP.matrixSingularValue A i •
        outerMatrix (u i) (rightSingularBasis A i) := by
  classical
  let e : Fin n → Fin m := Fin.castLE hnm
  let w : Fin m → EuclideanSpace ℝ (Fin m) := fun j =>
    if h : (j : ℕ) < n then leftSingularVector A ⟨j, h⟩ else 0
  let s : Set (Fin m) :=
    {j | ∃ i : Fin n, e i = j ∧ HDP.matrixSingularValue A i ≠ 0}
  have hw_cast (i : Fin n) : w (e i) = leftSingularVector A i := by
    simp [w, e, Fin.castLE, i.isLt]
  have hON : Orthonormal ℝ (s.restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨ja, hja⟩ ⟨jb, hjb⟩
    have hja' := hja
    have hjb' := hjb
    rcases hja' with ⟨ia, hia, hsi⟩
    rcases hjb' with ⟨ib, hib, hsj⟩
    have hwa : s.restrict w ⟨ja, hja⟩ = leftSingularVector A ia := by
      change w ja = _
      rw [← hia, hw_cast]
    have hwb : s.restrict w ⟨jb, hjb⟩ = leftSingularVector A ib := by
      change w jb = _
      rw [← hib, hw_cast]
    rw [hwa, hwb]
    by_cases hab : (⟨ja, hja⟩ : s) = ⟨jb, hjb⟩
    · have hjab : ja = jb := congrArg Subtype.val hab
      have hiab : ia = ib := Fin.castLE_injective hnm (hia.trans (hjab.trans hib.symm))
      subst ib
      rw [inner_self_eq_norm_sq_to_K, norm_leftSingularVector A ia hsi, if_pos hab]
      norm_num
    · have hiab : ia ≠ ib := by
        intro h
        subst ib
        apply hab
        apply Subtype.ext
        exact hia.symm.trans hib
      rw [leftSingularVector_orthogonal A hiab hsi hsj, if_neg hab]
  obtain ⟨b, hb⟩ := hON.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  let u : Fin n → EuclideanSpace ℝ (Fin m) := fun i => b (e i)
  have hu : Orthonormal ℝ u := by
    simpa [u, Function.comp_def] using
      b.orthonormal.comp e (Fin.castLE_injective hnm)
  have happly (i : Fin n) :
      A.toEuclideanLin (rightSingularBasis A i) =
        HDP.matrixSingularValue A i • u i := by
    by_cases hi : HDP.matrixSingularValue A i = 0
    · have hz : A.toEuclideanLin (rightSingularBasis A i) = 0 := by
        apply norm_eq_zero.mp
        rw [norm_apply_rightSingularVector A i, hi]
      simp [hz, hi]
    · have hei : e i ∈ s := ⟨i, rfl, hi⟩
      have hbi : b (e i) = leftSingularVector A i := by
        calc
          b (e i) = w (e i) := hb (e i) hei
          _ = leftSingularVector A i := hw_cast i
      simpa [u, hbi] using apply_rightSingularVector A i hi
  refine ⟨u, hu, ?_⟩
  apply (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n)).injective
  apply LinearMap.ext
  intro x
  rw [map_sum]
  simp only [map_smul]
  calc
    A.toEuclideanLin x = ∑ i, inner ℝ (rightSingularBasis A i) x •
        A.toEuclideanLin (rightSingularBasis A i) := singularValueDecomposition A x
    _ = ∑ i : Fin n, inner ℝ (rightSingularBasis A i) x •
        (HDP.matrixSingularValue A i • u i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [happly]
    _ = (∑ i : Fin n, HDP.matrixSingularValue A i •
        (outerMatrix (u i) (rightSingularBasis A i)).toEuclideanLin) x := by
          simp only [toEuclideanLin_outerMatrix, LinearMap.sum_apply,
            LinearMap.smul_apply]
          apply Finset.sum_congr rfl
          intro i _
          change inner ℝ (rightSingularBasis A i) x •
              (HDP.matrixSingularValue A i • u i) =
            HDP.matrixSingularValue A i •
              (inner ℝ (rightSingularBasis A i) x • u i)
          rw [smul_smul, smul_smul]
          congr 1
          ring

/-- Transposing an outer-product matrix swaps its two vectors.

**Lean implementation helper.** -/
@[simp] lemma outerMatrix_transpose {m n : ℕ} (u : EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n)) :
    (outerMatrix u v)ᵀ = outerMatrix v u := by
  ext i j
  simp [outerMatrix, Matrix.vecMulVec_apply, mul_comm]

/-- Every real `m × n` matrix admits a corrected rank-one expansion with exactly `min m n`
nonnegative decreasing coefficients and orthonormal left/right families.

**Book Theorem 4.1.1.** -/
theorem exists_singularValueDecomposition {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Nonempty (RealSVD A) := by
  classical
  by_cases hnm : n ≤ m
  · obtain ⟨u, hu, hA⟩ := exists_tall_svd A hnm
    have hmin : min m n = n := Nat.min_eq_right hnm
    let e : Fin (min m n) ≃ Fin n := finCongr hmin
    have he_mono : Monotone e := by
      intro i j hij
      exact Fin.mk_le_mk.mpr (by simpa [e] using Fin.mk_le_mk.mp hij)
    have hsum :
        (∑ i : Fin (min m n), HDP.matrixSingularValue A (e i) •
          outerMatrix (u (e i)) (rightSingularBasis A (e i))) =
        ∑ i : Fin n, HDP.matrixSingularValue A i •
          outerMatrix (u i) (rightSingularBasis A i) :=
      Equiv.sum_comp e (fun i : Fin n => HDP.matrixSingularValue A i •
        outerMatrix (u i) (rightSingularBasis A i))
    exact ⟨{
      left := fun i => u (e i)
      right := fun i => rightSingularBasis A (e i)
      singularValue := fun i => HDP.matrixSingularValue A (e i)
      left_orthonormal := hu.comp e e.injective
      right_orthonormal := (rightSingularBasis A).orthonormal.comp e e.injective
      singularValue_nonneg := fun i => HDP.matrixSingularValue_nonneg A (e i)
      singularValue_antitone := fun _ _ hij =>
        HDP.matrixSingularValue_antitone A (he_mono hij)
      eq_sum_outer := hA.trans hsum.symm }⟩
  · have hmn : m ≤ n := le_of_not_ge hnm
    obtain ⟨u, hu, hAT⟩ := exists_tall_svd Aᵀ hmn
    have hmin : min m n = m := Nat.min_eq_left hmn
    have htranspose := congrArg Matrix.transpose hAT
    have hA : A = ∑ i : Fin m, HDP.matrixSingularValue Aᵀ i •
        outerMatrix (rightSingularBasis Aᵀ i) (u i) := by
      calc
        A = Aᵀᵀ := by simp
        _ = (∑ i : Fin m, HDP.matrixSingularValue Aᵀ i •
            outerMatrix (u i) (rightSingularBasis Aᵀ i))ᵀ := htranspose
        _ = ∑ i : Fin m,
            (HDP.matrixSingularValue Aᵀ i •
              outerMatrix (u i) (rightSingularBasis Aᵀ i))ᵀ := by
              simpa using Matrix.transpose_sum (Finset.univ : Finset (Fin m))
                (fun i => HDP.matrixSingularValue Aᵀ i •
                  outerMatrix (u i) (rightSingularBasis Aᵀ i))
        _ = ∑ i : Fin m, HDP.matrixSingularValue Aᵀ i •
            outerMatrix (rightSingularBasis Aᵀ i) (u i) := by simp
    let e : Fin (min m n) ≃ Fin m := finCongr hmin
    have he_mono : Monotone e := by
      intro i j hij
      exact Fin.mk_le_mk.mpr (by simpa [e] using Fin.mk_le_mk.mp hij)
    have hsum :
        (∑ i : Fin (min m n), HDP.matrixSingularValue Aᵀ (e i) •
          outerMatrix (rightSingularBasis Aᵀ (e i)) (u (e i))) =
        ∑ i : Fin m, HDP.matrixSingularValue Aᵀ i •
          outerMatrix (rightSingularBasis Aᵀ i) (u i) :=
      Equiv.sum_comp e (fun i : Fin m => HDP.matrixSingularValue Aᵀ i •
        outerMatrix (rightSingularBasis Aᵀ i) (u i))
    exact ⟨{
      left := fun i => rightSingularBasis Aᵀ (e i)
      right := fun i => u (e i)
      singularValue := fun i => HDP.matrixSingularValue Aᵀ (e i)
      left_orthonormal := (rightSingularBasis Aᵀ).orthonormal.comp e e.injective
      right_orthonormal := hu.comp e e.injective
      singularValue_nonneg := fun i => HDP.matrixSingularValue_nonneg Aᵀ (e i)
      singularValue_antitone := fun _ _ hij =>
        HDP.matrixSingularValue_antitone Aᵀ (he_mono hij)
      eq_sum_outer := hA.trans hsum.symm }⟩

/-- Applying an SVD expansion to a right singular vector yields `A vᵢ = sᵢ uᵢ`. This includes
the zero-singular-value case.

**Lean implementation helper.** -/
theorem RealSVD.apply_right {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (d : RealSVD A) (j : Fin (min m n)) :
    A.toEuclideanLin (d.right j) = d.singularValue j • d.left j := by
  calc
    A.toEuclideanLin (d.right j) =
        (∑ i : Fin (min m n), d.singularValue i •
          outerMatrix (d.left i) (d.right i)).toEuclideanLin (d.right j) :=
      congrArg (fun M : Matrix (Fin m) (Fin n) ℝ =>
        M.toEuclideanLin (d.right j)) d.eq_sum_outer
    _ = d.singularValue j • d.left j := by
      simp only [map_sum, map_smul, toEuclideanLin_outerMatrix,
        LinearMap.sum_apply, LinearMap.smul_apply]
      rw [Finset.sum_eq_single j]
      · change d.singularValue j •
          (inner ℝ (d.right j) (d.right j) • d.left j) = _
        rw [inner_self_eq_norm_sq_to_K, d.right_orthonormal.1]
        simp
      · intro i _ hij
        change d.singularValue i •
          (inner ℝ (d.right i) (d.right j) • d.left i) = 0
        rw [d.right_orthonormal.2 hij]
        simp
      · simp

/-- The matrix whose columns are the vectors of an orthonormal basis.

**Lean implementation helper.** -/
noncomputable def orthonormalBasisMatrix {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => WithLp.ofLp (b j) i

/-- The column matrix of an orthonormal basis is orthogonal.

**Lean implementation helper.** -/
theorem orthonormalBasisMatrix_mem_orthogonal {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    orthonormalBasisMatrix b ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ k, orthonormalBasisMatrix b k i *
    orthonormalBasisMatrix b k j) = if i = j then 1 else 0
  simpa [orthonormalBasisMatrix, PiLp.inner_apply, RCLike.inner_apply,
    eq_comm]
    using orthonormal_iff_ite.mp b.orthonormal j i

/-- Extend a finite orthonormal family to a coordinate-indexed orthonormal
basis of its ambient Euclidean space.

**Lean implementation helper.** -/
private theorem exists_singularOrthonormalBasis
    {r d : ℕ} (hrd : r ≤ d)
    (v : Fin r → EuclideanSpace ℝ (Fin d)) (hv : Orthonormal ℝ v) :
    ∃ b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      ∀ k : Fin r, b (Fin.castLE hrd k) = v k := by
  classical
  let e : Fin r → Fin d := Fin.castLE hrd
  let w : Fin d → EuclideanSpace ℝ (Fin d) := fun j =>
    if h : (j : ℕ) < r then v ⟨j, h⟩ else 0
  let S : Set (Fin d) := {j | (j : ℕ) < r}
  have hwe (k : Fin r) : w (e k) = v k := by
    simp only [w, e]
    split_ifs with h
    · exact congrArg v (Fin.ext rfl)
    · exact (h k.isLt).elim
  have hON : Orthonormal ℝ (S.restrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    change (i : ℕ) < r at hi
    change (j : ℕ) < r at hj
    have hwi : S.restrict w ⟨i, hi⟩ = v ⟨i, hi⟩ := by
      simp only [Set.restrict_apply, w]
      simp [hi]
    have hwj : S.restrict w ⟨j, hj⟩ = v ⟨j, hj⟩ := by
      simp only [Set.restrict_apply, w]
      simp [hj]
    rw [hwi, hwj, orthonormal_iff_ite.mp hv]
    by_cases hij : i = j
    · subst j
      simp
    · have hval : (i : ℕ) ≠ (j : ℕ) := by
        intro h
        exact hij (Fin.ext h)
      simp [hij, hval]
  obtain ⟨b, hb⟩ := hON.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  refine ⟨b, fun k => ?_⟩
  rw [hb (e k) (by
    change ((e k : Fin d) : ℕ) < r
    exact k.isLt), hwe]

/-- The rectangular diagonal matrix whose first `min m n` diagonal entries
are the singular values of `s`.

**Book Remark 4.1.3; Equation (4.4).** -/
noncomputable def rectangularSingularValueMatrix
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (s : RealSVD A) :
    Matrix (Fin m) (Fin n) ℝ :=
  ∑ k : Fin (min m n), Matrix.single
    (Fin.castLE (Nat.min_le_left m n) k)
    (Fin.castLE (Nat.min_le_right m n) k) (s.singularValue k)

/-- Multiplying a coordinate matrix unit between two orthonormal-basis
matrices produces the corresponding outer product.

**Lean implementation helper.** -/
private lemma orthonormalBasisMatrix_single_mul
    {m n : ℕ}
    (bU : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (a : Fin m) (b : Fin n) (c : ℝ) :
    orthonormalBasisMatrix bU * Matrix.single a b c *
        (orthonormalBasisMatrix bV)ᵀ =
      c • outerMatrix (bU a) (bV b) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_single_apply_same]
    simp [orthonormalBasisMatrix, outerMatrix, Matrix.vecMulVec_apply]
    ring
  · intro x _ hxb
    rw [Matrix.mul_single_apply_of_ne (M := orthonormalBasisMatrix bU)
      (c := c) (i := a) (j := b) (a := i) (b := x) hxb]
    simp
  · simp

/-- Every real rectangular matrix has the literal matrix-form SVD
`A = U Σ Vᵀ`: the compact singular families extend to orthonormal bases,
`U,V` are square orthogonal matrices, and `Σ` is the rectangular diagonal
matrix of singular values.

**Book Remark 4.1.3; Equation (4.4).** -/
theorem exists_matrixFormSVD {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ s : RealSVD A,
      ∃ bU : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ bV : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
        (∀ k : Fin (min m n),
          bU (Fin.castLE (Nat.min_le_left m n) k) = s.left k) ∧
        (∀ k : Fin (min m n),
          bV (Fin.castLE (Nat.min_le_right m n) k) = s.right k) ∧
        orthonormalBasisMatrix bU ∈
          Matrix.orthogonalGroup (Fin m) ℝ ∧
        orthonormalBasisMatrix bV ∈
          Matrix.orthogonalGroup (Fin n) ℝ ∧
        A = orthonormalBasisMatrix bU *
          rectangularSingularValueMatrix s *
          (orthonormalBasisMatrix bV)ᵀ := by
  classical
  let s := Classical.choice (exists_singularValueDecomposition A)
  obtain ⟨bU, hbU⟩ := exists_singularOrthonormalBasis
    (Nat.min_le_left m n) s.left s.left_orthonormal
  obtain ⟨bV, hbV⟩ := exists_singularOrthonormalBasis
    (Nat.min_le_right m n) s.right s.right_orthonormal
  refine ⟨s, bU, bV, hbU, hbV,
    orthonormalBasisMatrix_mem_orthogonal bU,
    orthonormalBasisMatrix_mem_orthogonal bV, ?_⟩
  conv_lhs => rw [s.eq_sum_outer]
  simp only [rectangularSingularValueMatrix, Matrix.mul_sum,
    Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [orthonormalBasisMatrix_single_mul, hbU, hbV]

/-- Canonical source-numbered public name for Theorem 4.1.1. -/
alias theorem_4_1_1 := exists_singularValueDecomposition

end HDP.Chapter4

end Source_01_SingularValueDecomposition

/-! ## Material formerly in `02_MinMaxPrinciple.lean` -/

section Source_02_MinMaxPrinciple

/-!
# Chapter 4, §4.1.2: min–max principles

We use the ordered orthogonal-constraint form of Courant–Fischer.  The two extremal
sets below are the unit spheres in the leading eigenspace and in the orthogonal
complement of the preceding eigenvectors, respectively.
-/

open Real Metric
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter4

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Unit vectors in the span of the first `k+1` ordered eigenvectors, expressed without choosing
a separate subspace basis.

**Lean implementation helper.** -/
def leadingEigenSphere {n : ℕ} (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) : Set E :=
  {x | ‖x‖ = 1 ∧ ∀ i : Fin n, k < i →
    inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0}

/-- Unit vectors orthogonal to the first `k` ordered eigenvectors.

**Lean implementation helper.** -/
def trailingEigenSphere {n : ℕ} (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) : Set E :=
  {x | ‖x‖ = 1 ∧ ∀ i : Fin n, i < k →
    inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0}

/-! The finite-dimensional subspaces used in the source-strength min--max statement. -/

/-- Span of the eigenvectors strictly preceding `k`.

**Lean implementation helper.** -/
noncomputable def precedingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Fin k.val =>
    hT.isSymmetric.eigenvectorBasis hn
      ⟨i.val, lt_trans i.isLt k.isLt⟩)

/-- Span of the eigenvectors strictly following `k`.

**Lean implementation helper.** -/
noncomputable def followingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Fin (n - (k.val + 1)) =>
    hT.isSymmetric.eigenvectorBasis hn
      ⟨k.val + 1 + i.val, by omega⟩)

/-- The canonical `(k+1)`-dimensional leading eigenspace.

**Lean implementation helper.** -/
noncomputable def leadingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Submodule ℝ E :=
  (followingEigenSubspace T hT hn k)ᗮ

/-- The canonical `(n-k)`-dimensional trailing eigenspace.

**Lean implementation helper.** -/
noncomputable def trailingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Submodule ℝ E :=
  (precedingEigenSubspace T hT hn k)ᗮ

/-- Computes the dimension of preceding eigen subspace.

**Lean implementation helper.** -/
lemma finrank_precedingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ (precedingEigenSubspace T hT hn k) = k.val := by
  classical
  unfold precedingEigenSubspace
  rw [finrank_span_eq_card]
  · simp
  · let b := hT.isSymmetric.eigenvectorBasis hn
    exact b.orthonormal.linearIndependent.comp
      (fun i : Fin k.val => (⟨i.val, lt_trans i.isLt k.isLt⟩ : Fin n))
      (by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun z : Fin n => z.val) hij)

/-- Computes the dimension of following eigen subspace.

**Lean implementation helper.** -/
lemma finrank_followingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ (followingEigenSubspace T hT hn k) = n - (k.val + 1) := by
  classical
  unfold followingEigenSubspace
  rw [finrank_span_eq_card]
  · simp
  · let b := hT.isSymmetric.eigenvectorBasis hn
    exact b.orthonormal.linearIndependent.comp
      (fun i : Fin (n - (k.val + 1)) =>
        (⟨k.val + 1 + i.val, by omega⟩ : Fin n))
      (by
        intro i j hij
        apply Fin.ext
        have hval : k.val + 1 + i.val = k.val + 1 + j.val :=
          congrArg Fin.val hij
        omega)

/-- Computes the dimension of leading eigen subspace.

**Lean implementation helper.** -/
lemma finrank_leadingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ (leadingEigenSubspace T hT hn k) = k.val + 1 := by
  have hdim := (followingEigenSubspace T hT hn k).finrank_add_finrank_orthogonal
  rw [finrank_followingEigenSubspace T hT hn k, hn] at hdim
  unfold leadingEigenSubspace
  omega

/-- Computes the dimension of trailing eigen subspace.

**Lean implementation helper.** -/
lemma finrank_trailingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    Module.finrank ℝ (trailingEigenSubspace T hT hn k) = n - k.val := by
  have hdim := (precedingEigenSubspace T hT hn k).finrank_add_finrank_orthogonal
  rw [finrank_precedingEigenSubspace T hT hn k, hn] at hdim
  unfold trailingEigenSubspace
  omega

/-- Dimension intersection lemma used in both halves of Courant--Fischer.

**Lean implementation helper.** -/
lemma exists_unit_mem_inf_of_finrank_lt_add (U V : Submodule ℝ E)
    (h : Module.finrank ℝ E < Module.finrank ℝ U + Module.finrank ℝ V) :
    ∃ x : E, x ∈ U ∧ x ∈ V ∧ ‖x‖ = 1 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hsup : Module.finrank ℝ (U ⊔ V : Submodule ℝ E) ≤ Module.finrank ℝ E :=
    Submodule.finrank_le _
  have hinf : 0 < Module.finrank ℝ (U ⊓ V : Submodule ℝ E) := by omega
  letI : Nontrivial (U ⊓ V : Submodule ℝ E) :=
    Module.nontrivial_of_finrank_pos hinf
  obtain ⟨z, hz⟩ := exists_ne (0 : {x : E // x ∈ U ⊓ V})
  have hzn : ‖(z : E)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact fun hzero => hz (Subtype.ext hzero)
  let x : E := ‖(z : E)‖⁻¹ • (z : E)
  refine ⟨x, U.smul_mem _ z.2.1, V.smul_mem _ z.2.2, ?_⟩
  simp [x, norm_smul, hzn, inv_mul_cancel₀]

/-- Every vector in the trailing eigenspace from index `k` is orthogonal to all eigenvectors with index below `k`.

**Lean implementation helper.** -/
lemma mem_trailingEigenSubspace_orthogonal_preceding {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {x : E}
    (hx : x ∈ trailingEigenSubspace T hT hn k) :
    ∀ i : Fin n, i < k →
      inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0 := by
  intro i hik
  apply Submodule.inner_right_of_mem_orthogonal _ hx
  apply Submodule.subset_span
  refine ⟨(⟨i.val, hik⟩ : Fin k.val), ?_⟩
  apply congrArg (hT.isSymmetric.eigenvectorBasis hn)
  apply Fin.ext
  rfl

/-- Every vector in the leading eigenspace through index `k` is orthogonal to all eigenvectors with index above `k`.

**Lean implementation helper.** -/
lemma mem_leadingEigenSubspace_orthogonal_following {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {x : E}
    (hx : x ∈ leadingEigenSubspace T hT hn k) :
    ∀ i : Fin n, k < i →
      inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0 := by
  intro i hik
  apply Submodule.inner_right_of_mem_orthogonal _ hx
  apply Submodule.subset_span
  let j : Fin (n - (k.val + 1)) := ⟨i.val - (k.val + 1), by omega⟩
  refine ⟨j, ?_⟩
  apply congrArg (hT.isSymmetric.eigenvectorBasis hn)
  apply Fin.ext
  simp [j]
  omega

/-- The `k`th eigenvector belongs to the leading eigenspace through index `k`.

**Lean implementation helper.** -/
lemma kth_eigenvector_mem_leadingEigenSubspace {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    hT.isSymmetric.eigenvectorBasis hn k ∈
      leadingEigenSubspace T hT hn k := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis hn
  unfold leadingEigenSubspace
  rw [Submodule.mem_orthogonal']
  intro y hy
  refine Submodule.span_induction (p := fun y _ => inner ℝ (b k) y = 0)
    ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    have hne : k ≠ (⟨k.val + 1 + i.val, by omega⟩ : Fin n) := by
      intro heq
      have hval := congrArg (fun z : Fin n => z.val) heq
      change k.val = k.val + 1 + i.val at hval
      omega
    simp [b, hne]
  · simp
  · intro x y _ _ hx hy
    simp [inner_add_right, hx, hy]
  · intro a x _ hx
    simp [inner_smul_right, hx]

/-- The `k`th eigenvector belongs to the trailing eigenspace beginning at index `k`.

**Lean implementation helper.** -/
lemma kth_eigenvector_mem_trailingEigenSubspace {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    hT.isSymmetric.eigenvectorBasis hn k ∈
      trailingEigenSubspace T hT hn k := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis hn
  unfold trailingEigenSubspace
  rw [Submodule.mem_orthogonal']
  intro y hy
  refine Submodule.span_induction (p := fun y _ => inner ℝ (b k) y = 0)
    ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    have hne : k ≠ (⟨i.val, lt_trans i.isLt k.isLt⟩ : Fin n) := by
      intro heq
      have hval := congrArg (fun z : Fin n => z.val) heq
      change k.val = i.val at hval
      omega
    simp [b, hne]
  · simp
  · intro x y _ _ hx hy
    simp [inner_add_right, hx, hy]
  · intro a x _ hx
    simp [inner_smul_right, hx]

/-- Scalar core of the leading-eigenspace half of Courant–Fischer.

**Lean implementation helper.** -/
lemma kth_le_antitone_weighted_sq_sum {n : ℕ} (lam : Fin n → ℝ)
    (hlam : Antitone lam) (k : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hzero : ∀ i, k < i → x i = 0) :
    lam k ≤ ∑ i, lam i * x i ^ 2 := by
  calc
    lam k = lam k * ∑ i, x i ^ 2 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hx]
      ring
    _ ≤ ∑ i, lam i * x i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hik : k < i
      · rw [hzero i hik]
        simp
      · exact mul_le_mul_of_nonneg_right (hlam (le_of_not_gt hik)) (sq_nonneg _)

/-- Courant–Fischer, leading-space lower bound: every unit vector in the span of the first `k+1`
eigenvectors has Rayleigh quotient at least `λₖ`.

**Lean implementation helper.** -/
theorem eigenvalue_le_on_leadingEigenSphere {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n)
    {x : E} (hx : x ∈ leadingEigenSphere T hT hn k) :
    hT.isSymmetric.eigenvalues hn k ≤ T.reApplyInnerSelf x := by
  classical
  let hS := hT.isSymmetric
  let b := hS.eigenvectorBasis hn
  let y : EuclideanSpace ℝ (Fin n) := b.repr x
  have hy : ‖y‖ = 1 := by
    simpa [y, b] using (b.repr.norm_map x).trans hx.1
  have hyzero : ∀ i : Fin n, k < i → y i = 0 := by
    intro i hik
    simpa [y, b, OrthonormalBasis.repr_apply_apply] using hx.2 i hik
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
  rw [← b.repr.inner_map_map]
  simp only [PiLp.inner_apply, Real.inner_apply]
  have hcoord (i : Fin n) :
      b.repr (T x) i = hS.eigenvalues hn i * b.repr x i := by
    change (hS.eigenvectorBasis hn).repr ((T : E →ₗ[ℝ] E) x) i = _
    exact hS.eigenvectorBasis_apply_self_apply hn x i
  simp_rw [hcoord, mul_assoc, ← pow_two]
  simpa [y] using kth_le_antitone_weighted_sq_sum (hS.eigenvalues hn)
    (hS.eigenvalues_antitone hn) k y hy hyzero

/-- The `k`th eigenvector belongs to the leading extremal sphere and attains `λₖ`.

**Lean implementation helper.** -/
theorem kth_eigenvector_attains_leading_min {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    hT.isSymmetric.eigenvectorBasis hn k ∈ leadingEigenSphere T hT hn k ∧
      T.reApplyInnerSelf (hT.isSymmetric.eigenvectorBasis hn k) =
        hT.isSymmetric.eigenvalues hn k := by
  let b := hT.isSymmetric.eigenvectorBasis hn
  refine ⟨⟨b.norm_eq_one k, ?_⟩, (HDP.Chapter3.pca_kth_eigenvector_attains T hT hn k).2⟩
  intro i hik
  rw [b.inner_eq_ite]
  simp [ne_of_gt hik]

/-- The `k`th eigenvalue is the minimum Rayleigh quotient on the unit sphere of the leading eigenspace through `k`.

**Book Theorem 4.1.6.** -/
theorem minmax_eigenvalue_leading {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    IsLeast (T.reApplyInnerSelf '' leadingEigenSphere T hT hn k)
      (hT.isSymmetric.eigenvalues hn k) := by
  constructor
  · exact ⟨hT.isSymmetric.eigenvectorBasis hn k,
      (kth_eigenvector_attains_leading_min T hT hn k).1,
      (kth_eigenvector_attains_leading_min T hT hn k).2⟩
  · rintro y ⟨x, hx, rfl⟩
    exact eigenvalue_le_on_leadingEigenSphere T hT hn k hx

/-- This is the ordered PCA theorem from Chapter 3, now exposed as the Courant–Fischer
interface.

**Book Theorem 4.1.6.** -/
theorem minmax_eigenvalue_trailing {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    IsGreatest (T.reApplyInnerSelf '' trailingEigenSphere T hT hn k)
      (hT.isSymmetric.eigenvalues hn k) := by
  simpa [trailingEigenSphere] using
    HDP.Chapter3.pca_kth_maximum_principle T hT hn k

/-- Every unit vector in the leading eigenspace through `k` has Rayleigh quotient at least the `k`th eigenvalue.

**Lean implementation helper.** -/
lemma rayleigh_lower_on_leadingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n)
    {x : E} (hx : x ∈ leadingEigenSubspace T hT hn k) (hxnorm : ‖x‖ = 1) :
    hT.isSymmetric.eigenvalues hn k ≤ T.reApplyInnerSelf x :=
  eigenvalue_le_on_leadingEigenSphere T hT hn k
    ⟨hxnorm, mem_leadingEigenSubspace_orthogonal_following T hT hn k hx⟩

/-- Every unit vector in the trailing eigenspace from `k` has Rayleigh quotient at most the `k`th eigenvalue.

**Lean implementation helper.** -/
lemma rayleigh_upper_on_trailingEigenSubspace {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n)
    {x : E} (hx : x ∈ trailingEigenSubspace T hT hn k) (hxnorm : ‖x‖ = 1) :
    T.reApplyInnerSelf x ≤ hT.isSymmetric.eigenvalues hn k := by
  exact (minmax_eigenvalue_trailing T hT hn k).2
    ⟨x, ⟨hxnorm,
      mem_trailingEigenSubspace_orthogonal_preceding T hT hn k hx⟩, rfl⟩

/-- Every `(k+1)`-dimensional subspace contains a unit vector whose Rayleigh quotient is at most
the `k`th eigenvalue. This is the universal-subspace half of the first Courant--Fischer formula.

**Lean implementation helper.** -/
theorem every_finrank_succ_subspace_has_rayleigh_le {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) (V : Submodule ℝ E)
    (hV : Module.finrank ℝ V = k.val + 1) :
    ∃ x : E, x ∈ V ∧ ‖x‖ = 1 ∧
      T.reApplyInnerSelf x ≤ hT.isSymmetric.eigenvalues hn k := by
  have hinter : Module.finrank ℝ E <
      Module.finrank ℝ V + Module.finrank ℝ (trailingEigenSubspace T hT hn k) := by
    rw [hn, hV, finrank_trailingEigenSubspace T hT hn k]
    omega
  obtain ⟨x, hxV, hxtrail, hxnorm⟩ :=
    exists_unit_mem_inf_of_finrank_lt_add V
      (trailingEigenSubspace T hT hn k) hinter
  exact ⟨x, hxV, hxnorm,
    rayleigh_upper_on_trailingEigenSubspace T hT hn k hxtrail hxnorm⟩

/-- Every `(n-k)`-dimensional subspace contains a unit vector whose Rayleigh quotient is at
least the `k`th eigenvalue. This is the universal-subspace half of the second Courant--Fischer
formula.

**Lean implementation helper.** -/
theorem every_finrank_tail_subspace_has_rayleigh_ge {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) (V : Submodule ℝ E)
    (hV : Module.finrank ℝ V = n - k.val) :
    ∃ x : E, x ∈ V ∧ ‖x‖ = 1 ∧
      hT.isSymmetric.eigenvalues hn k ≤ T.reApplyInnerSelf x := by
  have hinter : Module.finrank ℝ E <
      Module.finrank ℝ V + Module.finrank ℝ (leadingEigenSubspace T hT hn k) := by
    rw [hn, hV, finrank_leadingEigenSubspace T hT hn k]
    omega
  obtain ⟨x, hxV, hxlead, hxnorm⟩ :=
    exists_unit_mem_inf_of_finrank_lt_add V
      (leadingEigenSubspace T hT hn k) hinter
  exact ⟨x, hxV, hxnorm,
    rayleigh_lower_on_leadingEigenSubspace T hT hn k hxlead hxnorm⟩

/-- The first conjunct states the max--min formula: every `(k+1)`-dimensional subspace has
minimum Rayleigh quotient at most `λₖ`, while the canonical leading subspace has dimension
`k+1`, all its unit Rayleigh quotients are at least `λₖ`, and `λₖ` is attained there. The second
conjunct is the dual min--max formula for subspaces of dimension `n-k`.

**Book Theorem 4.1.6.** -/
theorem courantFischer {n : ℕ} (T : E →L[ℝ] E)
    (hT : IsSelfAdjoint T) (hn : Module.finrank ℝ E = n) (k : Fin n) :
    ((∀ V : Submodule ℝ E, Module.finrank ℝ V = k.val + 1 →
        ∃ x : E, x ∈ V ∧ ‖x‖ = 1 ∧
          T.reApplyInnerSelf x ≤ hT.isSymmetric.eigenvalues hn k) ∧
      Module.finrank ℝ (leadingEigenSubspace T hT hn k) = k.val + 1 ∧
      (∀ x : E, x ∈ leadingEigenSubspace T hT hn k → ‖x‖ = 1 →
        hT.isSymmetric.eigenvalues hn k ≤ T.reApplyInnerSelf x) ∧
      ∃ x : E, x ∈ leadingEigenSubspace T hT hn k ∧ ‖x‖ = 1 ∧
        T.reApplyInnerSelf x = hT.isSymmetric.eigenvalues hn k) ∧
    ((∀ V : Submodule ℝ E, Module.finrank ℝ V = n - k.val →
        ∃ x : E, x ∈ V ∧ ‖x‖ = 1 ∧
          hT.isSymmetric.eigenvalues hn k ≤ T.reApplyInnerSelf x) ∧
      Module.finrank ℝ (trailingEigenSubspace T hT hn k) = n - k.val ∧
      (∀ x : E, x ∈ trailingEigenSubspace T hT hn k → ‖x‖ = 1 →
        T.reApplyInnerSelf x ≤ hT.isSymmetric.eigenvalues hn k) ∧
      ∃ x : E, x ∈ trailingEigenSubspace T hT hn k ∧ ‖x‖ = 1 ∧
        T.reApplyInnerSelf x = hT.isSymmetric.eigenvalues hn k) := by
  let b := hT.isSymmetric.eigenvectorBasis hn
  have hattain := kth_eigenvector_attains_leading_min T hT hn k
  refine ⟨⟨?_, finrank_leadingEigenSubspace T hT hn k, ?_, ?_⟩,
    ⟨?_, finrank_trailingEigenSubspace T hT hn k, ?_, ?_⟩⟩
  · intro V hV
    exact every_finrank_succ_subspace_has_rayleigh_le T hT hn k V hV
  · intro x hx hxnorm
    exact rayleigh_lower_on_leadingEigenSubspace T hT hn k hx hxnorm
  · exact ⟨b k, kth_eigenvector_mem_leadingEigenSubspace T hT hn k,
      b.norm_eq_one k, hattain.2⟩
  · intro V hV
    exact every_finrank_tail_subspace_has_rayleigh_ge T hT hn k V hV
  · intro x hx hxnorm
    exact rayleigh_upper_on_trailingEigenSubspace T hT hn k hx hxnorm
  · exact ⟨b k, kth_eigenvector_mem_trailingEigenSubspace T hT hn k,
      b.norm_eq_one k, hattain.2⟩

/-! ## Singular-value min--max -/

/-- The continuous Gram operator associated with a real matrix.

**Lean implementation helper.** -/
noncomputable def matrixGramOperator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  A.toEuclideanLin.toContinuousLinearMap.adjoint ∘L
    A.toEuclideanLin.toContinuousLinearMap

/-- Shows that matrix gram operator is self-adjoint.

**Lean implementation helper.** -/
lemma matrixGramOperator_isSelfAdjoint {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsSelfAdjoint (matrixGramOperator A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [matrixGramOperator]

/-- The Rayleigh quotient of the Gram operator `AᵀA` at `x` is `‖Ax‖²`.

**Lean implementation helper.** -/
lemma matrixGramOperator_rayleigh {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (matrixGramOperator A).reApplyInnerSelf x = ‖A.toEuclideanLin x‖ ^ 2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
  exact (A.toEuclideanLin.toContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left x).symm

/-- Identifies matrix gram operator eigenvalue with squared singular value.

**Lean implementation helper.** -/
lemma matrixGramOperator_eigenvalue_eq_sq_singularValue {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    (matrixGramOperator_isSelfAdjoint A).isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) i =
      HDP.matrixSingularValue A i ^ 2 := by
  have hs := A.toEuclideanLin.sq_singularValues_fin
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) i
  change A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) i =
    A.toEuclideanLin.singularValues i ^ 2
  exact hs.symm

/-- Both quantifiers range over arbitrary subspaces. The existential subspaces are the canonical
leading/trailing eigenspaces of `AᵀA`.

**Book Corollary 4.1.7.** -/
theorem singularValueMinMax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) :
    ((∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        Module.finrank ℝ V = i.val + 1 →
        ∃ x : EuclideanSpace ℝ (Fin n), x ∈ V ∧ ‖x‖ = 1 ∧
          ‖A.toEuclideanLin x‖ ≤ HDP.matrixSingularValue A i) ∧
      ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        Module.finrank ℝ V = i.val + 1 ∧
        (∀ x : EuclideanSpace ℝ (Fin n), x ∈ V → ‖x‖ = 1 →
          HDP.matrixSingularValue A i ≤ ‖A.toEuclideanLin x‖) ∧
        ∃ x : EuclideanSpace ℝ (Fin n), x ∈ V ∧ ‖x‖ = 1 ∧
          ‖A.toEuclideanLin x‖ = HDP.matrixSingularValue A i) ∧
    ((∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        Module.finrank ℝ V = n - i.val →
        ∃ x : EuclideanSpace ℝ (Fin n), x ∈ V ∧ ‖x‖ = 1 ∧
          HDP.matrixSingularValue A i ≤ ‖A.toEuclideanLin x‖) ∧
      ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        Module.finrank ℝ V = n - i.val ∧
        (∀ x : EuclideanSpace ℝ (Fin n), x ∈ V → ‖x‖ = 1 →
          ‖A.toEuclideanLin x‖ ≤ HDP.matrixSingularValue A i) ∧
        ∃ x : EuclideanSpace ℝ (Fin n), x ∈ V ∧ ‖x‖ = 1 ∧
          ‖A.toEuclideanLin x‖ = HDP.matrixSingularValue A i) := by
  let G := matrixGramOperator A
  have hG : IsSelfAdjoint G := matrixGramOperator_isSelfAdjoint A
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let b := hG.isSymmetric.eigenvectorBasis hn
  have hsnonneg := HDP.matrixSingularValue_nonneg A i
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro V hV
    obtain ⟨x, hxV, hxnorm, hxq⟩ :=
      every_finrank_succ_subspace_has_rayleigh_le G hG hn i V hV
    have hxq' : ‖A.toEuclideanLin x‖ ^ 2 ≤
        HDP.matrixSingularValue A i ^ 2 := by
      simpa [G, hn, matrixGramOperator_rayleigh,
        matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
    refine ⟨x, hxV, hxnorm, ?_⟩
    nlinarith [norm_nonneg (A.toEuclideanLin x)]
  · refine ⟨leadingEigenSubspace G hG hn i,
      finrank_leadingEigenSubspace G hG hn i, ?_, ?_⟩
    · intro x hx hxnorm
      have hxq := rayleigh_lower_on_leadingEigenSubspace G hG hn i hx hxnorm
      have hxq' : HDP.matrixSingularValue A i ^ 2 ≤
          ‖A.toEuclideanLin x‖ ^ 2 := by
        simpa [G, hn, matrixGramOperator_rayleigh,
          matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
      nlinarith [norm_nonneg (A.toEuclideanLin x)]
    · have hxmem := kth_eigenvector_mem_leadingEigenSubspace G hG hn i
      have hxq := (kth_eigenvector_attains_leading_min G hG hn i).2
      have hxq' : ‖A.toEuclideanLin (b i)‖ ^ 2 =
          HDP.matrixSingularValue A i ^ 2 := by
        simpa [G, hn, b, matrixGramOperator_rayleigh,
          matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
      refine ⟨b i, ?_, b.norm_eq_one i, ?_⟩
      · simpa [b] using hxmem
      · nlinarith [norm_nonneg (A.toEuclideanLin (b i))]
  · intro V hV
    obtain ⟨x, hxV, hxnorm, hxq⟩ :=
      every_finrank_tail_subspace_has_rayleigh_ge G hG hn i V hV
    have hxq' : HDP.matrixSingularValue A i ^ 2 ≤
        ‖A.toEuclideanLin x‖ ^ 2 := by
      simpa [G, hn, matrixGramOperator_rayleigh,
        matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
    refine ⟨x, hxV, hxnorm, ?_⟩
    nlinarith [norm_nonneg (A.toEuclideanLin x)]
  · refine ⟨trailingEigenSubspace G hG hn i,
      finrank_trailingEigenSubspace G hG hn i, ?_, ?_⟩
    · intro x hx hxnorm
      have hxq := rayleigh_upper_on_trailingEigenSubspace G hG hn i hx hxnorm
      have hxq' : ‖A.toEuclideanLin x‖ ^ 2 ≤
          HDP.matrixSingularValue A i ^ 2 := by
        simpa [G, hn, matrixGramOperator_rayleigh,
          matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
      nlinarith [norm_nonneg (A.toEuclideanLin x)]
    · have hxmem := kth_eigenvector_mem_trailingEigenSubspace G hG hn i
      have hxq := (kth_eigenvector_attains_leading_min G hG hn i).2
      have hxq' : ‖A.toEuclideanLin (b i)‖ ^ 2 =
          HDP.matrixSingularValue A i ^ 2 := by
        simpa [G, hn, b, matrixGramOperator_rayleigh,
          matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
      refine ⟨b i, ?_, b.norm_eq_one i, ?_⟩
      · simpa [b] using hxmem
      · nlinarith [norm_nonneg (A.toEuclideanLin (b i))]

/-- Courant--Fischer formulas for singular values.

**Book Corollary 4.1.7.** -/
theorem singularValue_attained {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) :
    ‖rightSingularBasis A i‖ = 1 ∧
      ‖A.toEuclideanLin (rightSingularBasis A i)‖ = HDP.matrixSingularValue A i :=
  ⟨(rightSingularBasis A).norm_eq_one i, norm_apply_rightSingularVector A i⟩

/-- Canonical source-numbered public name for Theorem 4.1.6. -/
alias theorem_4_1_6 := courantFischer

/-- Canonical source-numbered public name for Corollary 4.1.7. -/
alias corollary_4_1_7 := singularValueMinMax

end HDP.Chapter4

end Source_02_MinMaxPrinciple

/-! ## Material formerly in `03_MatrixNorms.lean` -/

section Source_03_MatrixNorms

/-!
# Chapter 4, §§4.1.3--4.1.4: matrix norms

The Euclidean operator norm is Mathlib's L2 operator norm.  The Frobenius norm
is exposed as an explicit real-valued wrapper, so its finiteness is automatic.
Promoted exercises from this part of the source live here rather than in an
exercise leaf.
-/

open Matrix WithLp
open Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter4

set_option linter.unusedSectionVars false

/-- The Euclidean operator norm is the least uniform stretch factor, equivalently a
unit-sphere/nonzero-vector maximum.

**Book Definition 4.1.8.** -/
theorem matrixOpNorm_apply_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖A.toEuclideanLin x‖ ≤ HDP.matrixOpNorm A * ‖x‖ := by
  simpa [HDP.matrixOpNorm, Matrix.l2_opNorm_def] using
    A.toEuclideanLin.toContinuousLinearMap.le_opNorm x

/-- Definiteness of the Euclidean operator norm.

**Lean implementation helper.** -/
theorem matrixOpNorm_eq_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm A = 0 ↔ A = 0 := by
  change ‖A‖ = 0 ↔ A = 0
  exact norm_eq_zero

/-- Operator-norm axioms, transpose invariance, submultiplicativity, and submatrix monotonicity.

**Book Exercise 4.2.** -/
theorem exercise_4_2a_operator_norm {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) :
    HDP.matrixOpNorm (A + B) ≤ HDP.matrixOpNorm A + HDP.matrixOpNorm B ∧
      HDP.matrixOpNorm (c • A) = |c| * HDP.matrixOpNorm A ∧
      (HDP.matrixOpNorm A = 0 ↔ A = 0) :=
  ⟨HDP.matrixOpNorm_add_le A B, HDP.matrixOpNorm_smul c A,
    matrixOpNorm_eq_zero_iff A⟩

/-- Operator-norm axioms, transpose invariance, submultiplicativity, and submatrix monotonicity.

**Book Exercise 4.2.** -/
theorem exercise_4_2b_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm Aᵀ = HDP.matrixOpNorm A :=
  HDP.matrixOpNorm_transpose A

/-- Shows that the Euclidean operator norm is submultiplicative under matrix multiplication.

**Book Exercise 4.2.** -/
theorem exercise_4_2c_submultiplicative {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm (A * B) ≤ HDP.matrixOpNorm A * HDP.matrixOpNorm B :=
  HDP.matrixOpNorm_mul A B

/-- Frobenius pairing equals the trace pairing.

**Book (4.7).** -/
theorem frobeniusInner_eq_trace {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner A B = (Aᵀ * B).trace :=
  HDP.matrixInner_eq_trace A B

/-- The squared Frobenius norm is the self-pairing.

**Book (4.8).** -/
theorem frobeniusNorm_sq_eq_inner {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm A ^ 2 = HDP.matrixFrobeniusInner A A := by
  exact (HDP.matrixInner_self A).symm

/-- The Frobenius norm squared is the sum of the squared Euclidean column norms. This is the
finite-dimensional Hilbert--Schmidt identity used in the corresponding exercise.

**Lean implementation helper.** -/
theorem frobeniusNorm_sq_eq_sum_column_norm_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm A ^ 2 =
      ∑ j : Fin n,
        ‖(WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
  rw [HDP.matrixFrobeniusNorm_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))).symm

/-- The row version of the Hilbert--Schmidt identity.

**Lean implementation helper.** -/
theorem frobeniusNorm_sq_eq_sum_row_norm_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm A ^ 2 =
      ∑ i : Fin m,
        ‖(WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [HDP.matrixFrobeniusNorm_sq]
  apply Finset.sum_congr rfl
  intro i _
  exact (EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))).symm

/-- Applying `B.toEuclideanLin` to the `j`th column of `A` yields the `j`th column of `B * A`.

**Lean implementation helper.** -/
lemma toEuclideanLin_apply_column {l m n : ℕ}
    (B : Matrix (Fin l) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    B.toEuclideanLin
        (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m)) =
      (WithLp.toLp 2 ((B * A).col j) : EuclideanSpace ℝ (Fin l)) := by
  ext i
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]

/-- Rank/Frobenius/operator inequalities and sharpness witnesses.

**Book Exercise 4.4.** -/
theorem exercise_4_4c_frobenius_mul_le {l m n : ℕ}
    (B : Matrix (Fin l) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm (B * A) ≤
      HDP.matrixOpNorm B * HDP.matrixFrobeniusNorm A := by
  have hsq : HDP.matrixFrobeniusNorm (B * A) ^ 2 ≤
      (HDP.matrixOpNorm B * HDP.matrixFrobeniusNorm A) ^ 2 := by
    rw [frobeniusNorm_sq_eq_sum_column_norm_sq]
    calc
      (∑ j : Fin n,
          ‖(WithLp.toLp 2 ((B * A).col j) : EuclideanSpace ℝ (Fin l))‖ ^ 2) =
          ∑ j : Fin n,
            ‖B.toEuclideanLin
              (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [toEuclideanLin_apply_column]
      _ ≤ ∑ j : Fin n,
          (HDP.matrixOpNorm B *
            ‖(WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            exact sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg (HDP.matrixOpNorm_nonneg B) (norm_nonneg _)) |>.2
                (matrixOpNorm_apply_le B _)
      _ = (HDP.matrixOpNorm B * HDP.matrixFrobeniusNorm A) ^ 2 := by
            simp_rw [mul_pow]
            rw [← Finset.mul_sum]
            rw [← frobeniusNorm_sq_eq_sum_column_norm_sq]
  have hrhs : 0 ≤ HDP.matrixOpNorm B * HDP.matrixFrobeniusNorm A :=
    mul_nonneg (HDP.matrixOpNorm_nonneg B) (HDP.matrixFrobeniusNorm_nonneg A)
  nlinarith [HDP.matrixFrobeniusNorm_nonneg (B * A)]

/-- Operator/Frobenius norms of rank-one and diagonal matrices.

**Book Exercise 4.3.** -/
theorem exercise_4_3a_outer_norms {m n : ℕ}
    (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)) :
    HDP.matrixOpNorm (outerMatrix u v) = ‖u‖ * ‖v‖ ∧
      HDP.matrixFrobeniusNorm (outerMatrix u v) = ‖u‖ * ‖v‖ := by
  constructor
  · rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
    change ‖(outerMatrix u v).toEuclideanLin.toContinuousLinearMap‖ = _
    rw [toEuclideanLin_outerMatrix]
    exact InnerProductSpace.norm_rankOne u v
  · have hsq : HDP.matrixFrobeniusNorm (outerMatrix u v) ^ 2 =
        (‖u‖ * ‖v‖) ^ 2 := by
      rw [HDP.matrixFrobeniusNorm_sq]
      simp only [outerMatrix, Matrix.vecMulVec_apply]
      rw [show (∑ i : Fin m, ∑ j : Fin n,
          ((WithLp.ofLp u) i * (WithLp.ofLp v) j) ^ 2) =
          (∑ i : Fin m, ((WithLp.ofLp u) i) ^ 2) *
            (∑ j : Fin n, ((WithLp.ofLp v) j) ^ 2) by
        simp_rw [mul_pow]
        rw [Finset.sum_comm]
        calc
          (∑ j : Fin n, ∑ i : Fin m,
              (WithLp.ofLp u i) ^ 2 * (WithLp.ofLp v j) ^ 2) =
              ∑ j : Fin n, (∑ i : Fin m, (WithLp.ofLp u i) ^ 2) *
                (WithLp.ofLp v j) ^ 2 := by
                apply Finset.sum_congr rfl
                intro j _
                rw [Finset.sum_mul]
          _ = (∑ i : Fin m, (WithLp.ofLp u i) ^ 2) *
              ∑ j : Fin n, (WithLp.ofLp v j) ^ 2 := by
                rw [Finset.mul_sum]]
      rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
      ring
    nlinarith [HDP.matrixFrobeniusNorm_nonneg (outerMatrix u v),
      norm_nonneg u, norm_nonneg v, mul_nonneg (norm_nonneg u) (norm_nonneg v)]

/-- Operator/Frobenius norms of rank-one and diagonal matrices.

**Book Exercise 4.3.** -/
theorem exercise_4_3b_diagonal {n : ℕ} (a : Fin n → ℝ) :
    HDP.matrixOpNorm (Matrix.diagonal a) = ‖a‖ := by
  exact Matrix.l2_opNorm_diagonal a

/-! ### General `p → q` norms (Exercises 4.18--4.19) -/

/-- The authoritative finite-dimensional `p → q` matrix norm. The endpoint `p = ∞` is Mathlib's
genuine supremum norm, not a finite-exponent surrogate.

**Book Remark 4.1.9.** -/
noncomputable def matrixLpToLpNorm (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ :=
  ‖(Matrix.toLpLin p q A).toContinuousLinearMap‖

/-- General `p -> q` induced matrix norms and the bilinear dual formula.

**Book Remark 4.1.9.** -/
theorem matrixLpToLpNorm_apply_le (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (x : WithLp p (n → ℝ)) :
    ‖Matrix.toLpLin p q A x‖ ≤ matrixLpToLpNorm p q A * ‖x‖ := by
  exact (Matrix.toLpLin p q A).toContinuousLinearMap.le_opNorm x

/-- General `p -> q` induced matrix norms and the bilinear dual formula.

**Book Remark 4.1.9.** -/
theorem matrixLpToLpNorm_ratio_le (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (x : WithLp p (n → ℝ)) (hx : x ≠ 0) :
    ‖Matrix.toLpLin p q A x‖ / ‖x‖ ≤ matrixLpToLpNorm p q A := by
  apply (div_le_iff₀ (norm_pos_iff.mpr hx)).2
  simpa [mul_comm] using matrixLpToLpNorm_apply_le p q A x

/-- Every induced `ℓᵖ`-to-`ℓᑫ` norm of the zero matrix is zero.

**Lean implementation helper.** -/
@[simp] theorem matrixLpToLpNorm_zero (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    matrixLpToLpNorm p q (0 : Matrix m n ℝ) = 0 := by
  simp [matrixLpToLpNorm]

/-- Identifies matrix lp to `Lᵖ` norm with zero iff.

**Lean implementation helper.** -/
theorem matrixLpToLpNorm_eq_zero_iff (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : matrixLpToLpNorm p q A = 0 ↔ A = 0 := by
  rw [matrixLpToLpNorm, norm_eq_zero]
  constructor
  · intro h
    apply (Matrix.toLpLin p q).injective
    apply LinearMap.ext
    intro x
    have hx := congrArg
      (fun f : WithLp p (n → ℝ) →L[ℝ] WithLp q (m → ℝ) => f x) h
    simpa using hx
  · rintro rfl
    simp

/-- General `p -> q` induced matrix norm, its norm axioms, and transpose duality.

**Book Exercise 4.18.** -/
theorem exercise_4_18b_matrixLpToLpNorm (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℝ) (c : ℝ) :
    matrixLpToLpNorm p q (A + B) ≤
        matrixLpToLpNorm p q A + matrixLpToLpNorm p q B ∧
      matrixLpToLpNorm p q (c • A) = |c| * matrixLpToLpNorm p q A ∧
      (matrixLpToLpNorm p q A = 0 ↔ A = 0) := by
  constructor
  · simpa [matrixLpToLpNorm] using
      norm_add_le
        (Matrix.toLpLin p q A).toContinuousLinearMap
        (Matrix.toLpLin p q B).toContinuousLinearMap
  constructor
  · simpa [matrixLpToLpNorm, Real.norm_eq_abs] using
      norm_smul c (Matrix.toLpLin p q A).toContinuousLinearMap
  · exact matrixLpToLpNorm_eq_zero_iff p q A

/-! Exact endpoint formulas from Exercise 4.19. -/

/-- The actual finite maximum of the absolute matrix entries.

**Lean implementation helper.** -/
noncomputable def maxAbsEntry {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) : ℝ :=
  ((Finset.univ.product Finset.univ).image
    (fun ij : m × n => |A ij.1 ij.2|)).max' (by simp)

/-- Bounds abs entry by max abs entry.

**Lean implementation helper.** -/
lemma abs_entry_le_maxAbsEntry {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) (i : m) (j : n) :
    |A i j| ≤ maxAbsEntry A := by
  exact Finset.le_max'
    ((Finset.univ.product Finset.univ).image
      (fun ij : m × n => |A ij.1 ij.2|)) _ (Finset.mem_image.mpr
    ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩)

/-- Shows that max abs entry is nonnegative.

**Lean implementation helper.** -/
lemma maxAbsEntry_nonneg {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) : 0 ≤ maxAbsEntry A := by
  let i : m := Classical.choice inferInstance
  let j : n := Classical.choice inferInstance
  exact (abs_nonneg (A i j)).trans (abs_entry_le_maxAbsEntry A i j)

/-- Identifies exists entry with max abs entry.

**Lean implementation helper.** -/
lemma exists_entry_eq_maxAbsEntry {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ∃ i j, |A i j| = maxAbsEntry A := by
  have hm := Finset.max'_mem ((Finset.univ.product Finset.univ).image
    (fun ij : m × n => |A ij.1 ij.2|))
    (by simp)
  rcases Finset.mem_image.mp hm with ⟨ij, _, hij⟩
  exact ⟨ij.1, ij.2, hij⟩

/-- Exact formulas for `1->infinity`, `1->2`, and `2->infinity` norms.

**Book Exercise 4.19.** -/
theorem exercise_4_19a_one_to_infty {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    matrixLpToLpNorm 1 ∞ A = maxAbsEntry A := by
  let T := (Matrix.toLpLin 1 ∞ A).toContinuousLinearMap
  apply le_antisymm
  · change ‖T‖ ≤ maxAbsEntry A
    refine ContinuousLinearMap.opNorm_le_bound _ (maxAbsEntry_nonneg A) ?_
    intro x
    change ‖Matrix.toLpLin 1 ∞ A x‖ ≤ maxAbsEntry A * ‖x‖
    rw [Matrix.toLpLin_apply, PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (maxAbsEntry_nonneg A) (norm_nonneg x))).2
    intro i
    change |∑ j, A i j * WithLp.ofLp x j| ≤ maxAbsEntry A * ‖x‖
    calc
      |∑ j, A i j * WithLp.ofLp x j| ≤
          ∑ j, |A i j * WithLp.ofLp x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |WithLp.ofLp x j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
      _ ≤ ∑ j, maxAbsEntry A * |WithLp.ofLp x j| := by
        gcongr with j
        exact abs_entry_le_maxAbsEntry A i j
      _ = maxAbsEntry A * ∑ j, |WithLp.ofLp x j| := by rw [Finset.mul_sum]
      _ = maxAbsEntry A * ‖x‖ := by
        rw [PiLp.norm_eq_of_L1]
        simp only [Real.norm_eq_abs]
  · obtain ⟨i, j, hij⟩ := exists_entry_eq_maxAbsEntry A
    let x : WithLp (1 : ℝ≥0∞) (n → ℝ) := PiLp.single 1 j 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hop := matrixLpToLpNorm_apply_le 1 ∞ A x
    have hcoord := PiLp.norm_apply_le (Matrix.toLpLin 1 ∞ A x) i
    change maxAbsEntry A ≤ matrixLpToLpNorm 1 ∞ A
    rw [← hij]
    calc
      |A i j| = ‖(Matrix.toLpLin 1 ∞ A x) i‖ := by
        simp [x, Matrix.toLpLin_apply]
      _ ≤ ‖Matrix.toLpLin 1 ∞ A x‖ := hcoord
      _ ≤ matrixLpToLpNorm 1 ∞ A * ‖x‖ := hop
      _ = matrixLpToLpNorm 1 ∞ A := by rw [hx, mul_one]

/-- The actual finite maximum of the Euclidean column norms.

**Lean implementation helper.** -/
noncomputable def maxColumnL2Norm {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty n] (A : Matrix m n ℝ) : ℝ :=
  (Finset.univ.image (fun j : n =>
    ‖(WithLp.toLp 2 (A.col j) : WithLp 2 (m → ℝ))‖)).max' (by simp)

/-- Bounds column norm by max column l2 norm.

**Lean implementation helper.** -/
lemma column_norm_le_maxColumnL2Norm {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty n] (A : Matrix m n ℝ) (j : n) :
    ‖(WithLp.toLp 2 (A.col j) : WithLp 2 (m → ℝ))‖ ≤ maxColumnL2Norm A := by
  exact Finset.le_max'
    (Finset.univ.image (fun j : n =>
      ‖(WithLp.toLp 2 (A.col j) : WithLp 2 (m → ℝ))‖)) _
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Shows that max column l2 norm is nonnegative.

**Lean implementation helper.** -/
lemma maxColumnL2Norm_nonneg {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty n] (A : Matrix m n ℝ) : 0 ≤ maxColumnL2Norm A := by
  let j : n := Classical.choice inferInstance
  exact (norm_nonneg _).trans (column_norm_le_maxColumnL2Norm A j)

/-- Identifies exists column with max column l2 norm.

**Lean implementation helper.** -/
lemma exists_column_eq_maxColumnL2Norm {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty n] (A : Matrix m n ℝ) :
    ∃ j, ‖(WithLp.toLp 2 (A.col j) : WithLp 2 (m → ℝ))‖ = maxColumnL2Norm A := by
  have hm := Finset.max'_mem (Finset.univ.image (fun j : n =>
    ‖(WithLp.toLp 2 (A.col j) : WithLp 2 (m → ℝ))‖)) (by simp)
  rcases Finset.mem_image.mp hm with ⟨j, _, hj⟩
  exact ⟨j, hj⟩

/-- Exact formulas for `1->infinity`, `1->2`, and `2->infinity` norms.

**Book Exercise 4.19.** -/
theorem exercise_4_19b_one_to_two {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [Nonempty n] (A : Matrix m n ℝ) :
    matrixLpToLpNorm 1 2 A = maxColumnL2Norm A := by
  let T := (Matrix.toLpLin 1 2 A).toContinuousLinearMap
  apply le_antisymm
  · change ‖T‖ ≤ maxColumnL2Norm A
    refine ContinuousLinearMap.opNorm_le_bound _ (maxColumnL2Norm_nonneg A) ?_
    intro x
    change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ maxColumnL2Norm A * ‖x‖
    have hsum : WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) =
        ∑ j, (WithLp.ofLp x j) • WithLp.toLp 2 (A.col j) := by
      ext i
      rw [WithLp.ofLp_sum]
      simp only [WithLp.ofLp_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      change A i j * WithLp.ofLp x j = WithLp.ofLp x j * A i j
      ring
    rw [hsum]
    calc
      ‖∑ j, (WithLp.ofLp x j) • WithLp.toLp 2 (A.col j)‖ ≤
          ∑ j, ‖(WithLp.ofLp x j) • WithLp.toLp 2 (A.col j)‖ :=
        norm_sum_le _ _
      _ = ∑ j, |WithLp.ofLp x j| * ‖(WithLp.toLp 2 (A.col j) :
          WithLp 2 (m → ℝ))‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ j, |WithLp.ofLp x j| * maxColumnL2Norm A := by
        gcongr with j
        exact column_norm_le_maxColumnL2Norm A j
      _ = maxColumnL2Norm A * ∑ j, |WithLp.ofLp x j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = maxColumnL2Norm A * ‖x‖ := by
        rw [PiLp.norm_eq_of_L1]
        simp only [Real.norm_eq_abs]
  · obtain ⟨j, hj⟩ := exists_column_eq_maxColumnL2Norm A
    let x : WithLp (1 : ℝ≥0∞) (n → ℝ) := PiLp.single 1 j 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hop := matrixLpToLpNorm_apply_le 1 2 A x
    change maxColumnL2Norm A ≤ matrixLpToLpNorm 1 2 A
    rw [← hj]
    calc
      ‖(WithLp.toLp 2 (A.col j) : WithLp 2 (m → ℝ))‖ =
          ‖Matrix.toLpLin 1 2 A x‖ := by
            congr 1
            ext i
            simp [x, Matrix.toLpLin_apply]
      _ ≤ matrixLpToLpNorm 1 2 A * ‖x‖ := hop
      _ = matrixLpToLpNorm 1 2 A := by rw [hx, mul_one]

/-- A diagonal right factor scales the `j`th column by its `j`th diagonal entry.

**Lean implementation helper.** -/
lemma column_mul_diagonal {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    (WithLp.toLp 2 ((B * Matrix.diagonal a).col j) :
        EuclideanSpace ℝ (Fin m)) =
      a j • (WithLp.toLp 2 (B.col j) : EuclideanSpace ℝ (Fin m)) := by
  ext i
  simp [mul_comm]

/-- Rank/Frobenius/operator inequalities and sharpness witnesses.

**Book Exercise 4.4.** -/
theorem exercise_4_4d_diagonal_frobenius_mul_le {m n : ℕ}
    [Nonempty (Fin n)] (B : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ) :
    HDP.matrixFrobeniusNorm (B * Matrix.diagonal a) ≤
      matrixLpToLpNorm 1 2 B *
        HDP.matrixFrobeniusNorm (Matrix.diagonal a) := by
  rw [exercise_4_19b_one_to_two]
  have hdiag : HDP.matrixFrobeniusNorm (Matrix.diagonal a) ^ 2 =
      ∑ j : Fin n, a j ^ 2 := by
    rw [frobeniusNorm_sq_eq_sum_column_norm_sq]
    apply Finset.sum_congr rfl
    intro j _
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hsq : HDP.matrixFrobeniusNorm (B * Matrix.diagonal a) ^ 2 ≤
      (maxColumnL2Norm B *
        HDP.matrixFrobeniusNorm (Matrix.diagonal a)) ^ 2 := by
    rw [frobeniusNorm_sq_eq_sum_column_norm_sq]
    calc
      (∑ j : Fin n,
          ‖(WithLp.toLp 2 ((B * Matrix.diagonal a).col j) :
            EuclideanSpace ℝ (Fin m))‖ ^ 2) =
          ∑ j : Fin n,
            (|a j| *
              ‖(WithLp.toLp 2 (B.col j) : EuclideanSpace ℝ (Fin m))‖) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [column_mul_diagonal, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ j : Fin n, (|a j| * maxColumnL2Norm B) ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            apply sq_le_sq₀
              (mul_nonneg (abs_nonneg _) (norm_nonneg _))
              (mul_nonneg (abs_nonneg _) (maxColumnL2Norm_nonneg B)) |>.2
            exact mul_le_mul_of_nonneg_left
              (column_norm_le_maxColumnL2Norm B j) (abs_nonneg _)
      _ = (maxColumnL2Norm B *
          HDP.matrixFrobeniusNorm (Matrix.diagonal a)) ^ 2 := by
            simp_rw [mul_pow]
            rw [show (∑ j : Fin n, |a j| ^ 2 * maxColumnL2Norm B ^ 2) =
                maxColumnL2Norm B ^ 2 * ∑ j : Fin n, a j ^ 2 by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [sq_abs]
              ring]
            rw [hdiag]
  have hrhs : 0 ≤ maxColumnL2Norm B *
      HDP.matrixFrobeniusNorm (Matrix.diagonal a) :=
    mul_nonneg (maxColumnL2Norm_nonneg B)
      (HDP.matrixFrobeniusNorm_nonneg _)
  nlinarith [HDP.matrixFrobeniusNorm_nonneg (B * Matrix.diagonal a)]

/-- The actual finite maximum of the Euclidean row norms.

**Lean implementation helper.** -/
noncomputable def maxRowL2Norm {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] (A : Matrix m n ℝ) : ℝ :=
  (Finset.univ.image (fun i : m =>
    ‖(WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ))‖)).max' (by simp)

/-- Bounds row norm by max row l2 norm.

**Lean implementation helper.** -/
lemma row_norm_le_maxRowL2Norm {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] (A : Matrix m n ℝ) (i : m) :
    ‖(WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ))‖ ≤ maxRowL2Norm A := by
  exact Finset.le_max'
    (Finset.univ.image (fun i : m =>
      ‖(WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ))‖)) _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- Shows that max row l2 norm is nonnegative.

**Lean implementation helper.** -/
lemma maxRowL2Norm_nonneg {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] (A : Matrix m n ℝ) : 0 ≤ maxRowL2Norm A := by
  let i : m := Classical.choice inferInstance
  exact (norm_nonneg _).trans (row_norm_le_maxRowL2Norm A i)

/-- Identifies exists row with max row l2 norm.

**Lean implementation helper.** -/
lemma exists_row_eq_maxRowL2Norm {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] (A : Matrix m n ℝ) :
    ∃ i, ‖(WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ))‖ = maxRowL2Norm A := by
  have hm := Finset.max'_mem (Finset.univ.image (fun i : m =>
    ‖(WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ))‖)) (by simp)
  rcases Finset.mem_image.mp hm with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- The `i`th coordinate of `A *ᵥ x` is the Euclidean inner product of row `i` of `A` with `x`.

**Lean implementation helper.** -/
lemma mulVec_apply_eq_inner_row {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (x : WithLp 2 (n → ℝ)) (i : m) :
    (A *ᵥ WithLp.ofLp x) i =
      inner ℝ (WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ)) x := by
  simp [Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]

/-- Exact formulas for `1->infinity`, `1->2`, and `2->infinity` norms.

**Book Exercise 4.19.** -/
theorem exercise_4_19b_two_to_infty {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [Nonempty m] (A : Matrix m n ℝ) :
    matrixLpToLpNorm 2 ∞ A = maxRowL2Norm A := by
  let T := (Matrix.toLpLin 2 ∞ A).toContinuousLinearMap
  apply le_antisymm
  · change ‖T‖ ≤ maxRowL2Norm A
    refine ContinuousLinearMap.opNorm_le_bound _ (maxRowL2Norm_nonneg A) ?_
    intro x
    change ‖Matrix.toLpLin 2 ∞ A x‖ ≤ maxRowL2Norm A * ‖x‖
    rw [Matrix.toLpLin_apply, PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (maxRowL2Norm_nonneg A) (norm_nonneg x))).2
    intro i
    change |(A *ᵥ WithLp.ofLp x) i| ≤ maxRowL2Norm A * ‖x‖
    rw [mulVec_apply_eq_inner_row]
    calc
      |inner ℝ (WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ)) x| ≤
          ‖(WithLp.toLp 2 (A.row i) : WithLp 2 (n → ℝ))‖ * ‖x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ maxRowL2Norm A * ‖x‖ :=
        mul_le_mul_of_nonneg_right (row_norm_le_maxRowL2Norm A i) (norm_nonneg x)
  · obtain ⟨i, hi⟩ := exists_row_eq_maxRowL2Norm A
    let r : WithLp 2 (n → ℝ) := WithLp.toLp 2 (A.row i)
    by_cases hr : r = 0
    · have hmax : maxRowL2Norm A = 0 := by simpa [r, hr] using hi.symm
      rw [hmax]
      exact norm_nonneg _
    · let x : WithLp 2 (n → ℝ) := ‖r‖⁻¹ • r
      have hx : ‖x‖ = 1 := by simp [x, norm_smul, hr]
      have hop := matrixLpToLpNorm_apply_le 2 ∞ A x
      have hcoord := PiLp.norm_apply_le (Matrix.toLpLin 2 ∞ A x) i
      change maxRowL2Norm A ≤ matrixLpToLpNorm 2 ∞ A
      rw [← hi]
      calc
        ‖r‖ = ‖(Matrix.toLpLin 2 ∞ A x) i‖ := by
          rw [Matrix.toLpLin_apply]
          change ‖r‖ = |(A *ᵥ WithLp.ofLp x) i|
          rw [mulVec_apply_eq_inner_row]
          change ‖r‖ = |inner ℝ r x|
          rw [show x = ‖r‖⁻¹ • r by rfl, inner_smul_right]
          rw [real_inner_self_eq_norm_sq]
          have hrnorm : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
          field_simp
          exact (abs_of_nonneg (norm_nonneg r)).symm
        _ ≤ ‖Matrix.toLpLin 2 ∞ A x‖ := hcoord
        _ ≤ matrixLpToLpNorm 2 ∞ A * ‖x‖ := hop
        _ = matrixLpToLpNorm 2 ∞ A := by rw [hx, mul_one]

/-! ### Exercise 4.20: the `∞ → 1` sign formula -/

/-- A canonical `{−1,1}`-valued vector.

**Lean implementation helper.** -/
def pmOneVector {ι : Type*} (s : ι → Bool) : ι → ℝ :=
  fun i => if s i then 1 else -1

/-- Every coordinate of `pmOneVector s` has absolute value one.

**Lean implementation helper.** -/
@[simp] lemma abs_pmOneVector {ι : Type*} (s : ι → Bool) (i : ι) :
    |pmOneVector s i| = 1 := by
  cases h : s i <;> simp [pmOneVector, h]

/-- The rectangular bilinear form `xᵀAy`.

**Lean implementation helper.** -/
def matrixBilinear {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * y j

/-- The matrix bilinear form is additive in its left vector argument.

**Lean implementation helper.** -/
lemma matrixBilinear_add_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x z : m → ℝ) (y : n → ℝ) :
    matrixBilinear A (x + z) y = matrixBilinear A x y + matrixBilinear A z y := by
  simp only [matrixBilinear, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix bilinear form is additive in its right vector argument.

**Lean implementation helper.** -/
lemma matrixBilinear_add_right {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y z : n → ℝ) :
    matrixBilinear A x (y + z) = matrixBilinear A x y + matrixBilinear A x z := by
  simp only [matrixBilinear, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix bilinear form is homogeneous in its left vector argument.

**Lean implementation helper.** -/
lemma matrixBilinear_smul_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a : ℝ) (x : m → ℝ) (y : n → ℝ) :
    matrixBilinear A (a • x) y = a * matrixBilinear A x y := by
  simp only [matrixBilinear, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix bilinear form is homogeneous in its right vector argument.

**Lean implementation helper.** -/
lemma matrixBilinear_smul_right {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a : ℝ) (x : m → ℝ) (y : n → ℝ) :
    matrixBilinear A x (a • y) = a * matrixBilinear A x y := by
  simp only [matrixBilinear, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For fixed `y`, the absolute matrix bilinear form is convex as a function of `x`.

**Lean implementation helper.** -/
lemma convexOn_abs_matrixBilinear_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (y : n → ℝ) :
    ConvexOn ℝ univ (fun x : m → ℝ => |matrixBilinear A x y|) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  change |matrixBilinear A (a • x + b • z) y| ≤
    a * |matrixBilinear A x y| + b * |matrixBilinear A z y|
  rw [matrixBilinear_add_left, matrixBilinear_smul_left,
    matrixBilinear_smul_left]
  calc
        |a * matrixBilinear A x y + b * matrixBilinear A z y| ≤
        |a * matrixBilinear A x y| + |b * matrixBilinear A z y| := abs_add_le _ _
    _ = a * |matrixBilinear A x y| + b * |matrixBilinear A z y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- For fixed `x`, the absolute matrix bilinear form is convex as a function of `y`.

**Lean implementation helper.** -/
lemma convexOn_abs_matrixBilinear_right {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) :
    ConvexOn ℝ univ (fun y : n → ℝ => |matrixBilinear A x y|) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ z _ a b ha hb hab
  change |matrixBilinear A x (a • y + b • z)| ≤
    a * |matrixBilinear A x y| + b * |matrixBilinear A x z|
  rw [matrixBilinear_add_right, matrixBilinear_smul_right,
    matrixBilinear_smul_right]
  calc
        |a * matrixBilinear A x y + b * matrixBilinear A x z| ≤
        |a * matrixBilinear A x y| + |b * matrixBilinear A x z| := abs_add_le _ _
    _ = a * |matrixBilinear A x y| + b * |matrixBilinear A x z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- The actual maximum of `|xᵀAy|` over the two sign cubes.

**Lean implementation helper.** -/
noncomputable def signBilinearMax {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ := by
  classical
  exact ((Finset.univ.product Finset.univ).image
      (fun st : (m → Bool) × (n → Bool) =>
        |matrixBilinear A (pmOneVector st.1) (pmOneVector st.2)|)).max' (by simp)

/-- Bounds sign bilinear by sign bilinear max.

**Lean implementation helper.** -/
lemma sign_bilinear_le_signBilinearMax {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (s : m → Bool) (t : n → Bool) :
    |matrixBilinear A (pmOneVector s) (pmOneVector t)| ≤ signBilinearMax A := by
  classical
  exact Finset.le_max'
    ((Finset.univ.product Finset.univ).image
      (fun st : (m → Bool) × (n → Bool) =>
        |matrixBilinear A (pmOneVector st.1) (pmOneVector st.2)|)) _
    (Finset.mem_image.mpr ⟨(s, t), by simp, rfl⟩)

/-- Shows that sign bilinear max is nonnegative.

**Lean implementation helper.** -/
lemma signBilinearMax_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : 0 ≤ signBilinearMax A := by
  let s : m → Bool := fun _ => false
  let t : n → Bool := fun _ => false
  exact (abs_nonneg _).trans (sign_bilinear_le_signBilinearMax A s t)

/-- Identifies exists sign with sign bilinear max.

**Lean implementation helper.** -/
lemma exists_sign_eq_signBilinearMax {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    ∃ s t, |matrixBilinear A (pmOneVector s) (pmOneVector t)| =
      signBilinearMax A := by
  classical
  have hm := Finset.max'_mem ((Finset.univ.product Finset.univ).image
    (fun st : (m → Bool) × (n → Bool) =>
      |matrixBilinear A (pmOneVector st.1) (pmOneVector st.2)|)) (by simp)
  rcases Finset.mem_image.mp hm with ⟨st, _, hst⟩
  exact ⟨st.1, st.2, hst⟩

/-- Bounds abs matrix bilinear by sign bilinear max of cube.

**Lean implementation helper.** -/
lemma abs_matrixBilinear_le_signBilinearMax_of_cube
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    |matrixBilinear A x y| ≤ signBilinearMax A := by
  classical
  have hxcube : x ∈ HDP.Chapter1.linftyUnitBall (ι := m) := by
    rw [HDP.Chapter1.linftyUnitBall_eq_cube]
    exact fun i _ => (abs_le.mp (hx i))
  have hxch : x ∈ convexHull ℝ (HDP.Chapter1.cubeVertices (ι := m)) := by
    rw [← HDP.Chapter1.linftyUnitBall_eq_convexHull_cubeVertices]
    exact hxcube
  rcases (convexOn_abs_matrixBilinear_left A y).exists_ge_of_mem_convexHull
      (fun _ _ => Set.mem_univ _) hxch with ⟨sx, hsx, hxsx⟩
  have hycube : y ∈ HDP.Chapter1.linftyUnitBall (ι := n) := by
    rw [HDP.Chapter1.linftyUnitBall_eq_cube]
    exact fun j _ => (abs_le.mp (hy j))
  have hych : y ∈ convexHull ℝ (HDP.Chapter1.cubeVertices (ι := n)) := by
    rw [← HDP.Chapter1.linftyUnitBall_eq_convexHull_cubeVertices]
    exact hycube
  rcases (convexOn_abs_matrixBilinear_right A sx).exists_ge_of_mem_convexHull
      (fun _ _ => Set.mem_univ _) hych with ⟨sy, hsy, hysy⟩
  have hsx' : ∀ i, sx i = -1 ∨ sx i = 1 := by
    simpa [HDP.Chapter1.cubeVertices] using hsx
  have hsy' : ∀ j, sy j = -1 ∨ sy j = 1 := by
    simpa [HDP.Chapter1.cubeVertices] using hsy
  let bx : m → Bool := fun i => decide (sx i = 1)
  let bt : n → Bool := fun j => decide (sy j = 1)
  have hbx : pmOneVector bx = sx := by
    funext i
    rcases hsx' i with hi | hi
    · norm_num [pmOneVector, bx, hi]
    · simp [pmOneVector, bx, hi]
  have hbt : pmOneVector bt = sy := by
    funext j
    rcases hsy' j with hj | hj
    · norm_num [pmOneVector, bt, hj]
    · simp [pmOneVector, bt, hj]
  exact hxsx.trans (hysy.trans (by
    rw [← hbx, ← hbt]
    exact sign_bilinear_le_signBilinearMax A bx bt))

/-- Identifies matrix bilinear with sum mul vec.

**Lean implementation helper.** -/
lemma matrixBilinear_eq_sum_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    matrixBilinear A x y = ∑ i, x i * (A *ᵥ y) i := by
  simp only [matrixBilinear, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Bounds abs matrix bilinear by l1 mul vec.

**Lean implementation helper.** -/
lemma abs_matrixBilinear_le_l1_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ)
    (hx : ∀ i, |x i| = 1) :
    |matrixBilinear A x y| ≤ ∑ i, |(A *ᵥ y) i| := by
  rw [matrixBilinear_eq_sum_mulVec]
  calc
    |∑ i, x i * (A *ᵥ y) i| ≤ ∑ i, |x i * (A *ᵥ y) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(A *ᵥ y) i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, hx i, one_mul]

/-- `infinity -> 1` norm is attained on sign vectors.

**Book (4.32).** -/
theorem exercise_4_20a_infty_to_one_sign_formula
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix m n ℝ) :
    matrixLpToLpNorm ∞ 1 A = signBilinearMax A := by
  let T := (Matrix.toLpLin ∞ 1 A).toContinuousLinearMap
  apply le_antisymm
  · change ‖T‖ ≤ signBilinearMax A
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (signBilinearMax_nonneg A)
    intro y hy
    let s : m → Bool := fun i => decide (0 ≤ (A *ᵥ WithLp.ofLp y) i)
    have hs (i : m) :
        pmOneVector s i * (A *ᵥ WithLp.ofLp y) i =
          |(A *ᵥ WithLp.ofLp y) i| := by
      by_cases hi : 0 ≤ (A *ᵥ WithLp.ofLp y) i
      · simp [pmOneVector, s, hi, abs_of_nonneg hi]
      · have hle : (A *ᵥ WithLp.ofLp y) i ≤ 0 := le_of_not_ge hi
        simp [pmOneVector, s, hi, abs_of_nonpos hle]
    have hycube : ∀ j, |WithLp.ofLp y j| ≤ 1 := by
      intro j
      have hj := PiLp.norm_apply_le y j
      rw [hy] at hj
      simpa [Real.norm_eq_abs] using hj
    have hcube := abs_matrixBilinear_le_signBilinearMax_of_cube A
      (pmOneVector s) (WithLp.ofLp y) (fun i => by simp) hycube
    change ‖Matrix.toLpLin ∞ 1 A y‖ ≤ signBilinearMax A
    rw [Matrix.toLpLin_apply, PiLp.norm_eq_of_L1]
    simp only [Real.norm_eq_abs]
    have hobj : matrixBilinear A (pmOneVector s) (WithLp.ofLp y) =
        ∑ i, |(A *ᵥ WithLp.ofLp y) i| := by
      rw [matrixBilinear_eq_sum_mulVec]
      apply Finset.sum_congr rfl
      intro i _
      exact hs i
    rw [← hobj]
    exact (le_abs_self _).trans hcube
  · obtain ⟨s, t, hst⟩ := exists_sign_eq_signBilinearMax A
    let y : WithLp (∞ : ℝ≥0∞) (n → ℝ) := WithLp.toLp ∞ (pmOneVector t)
    have hy : ‖y‖ = 1 := by
      apply le_antisymm
      · rw [PiLp.norm_toLp]
        apply (pi_norm_le_iff_of_nonneg zero_le_one).2
        intro j
        simp
      · let j : n := Classical.choice inferInstance
        calc
          (1 : ℝ) = ‖WithLp.ofLp y j‖ := by simp [y]
          _ ≤ ‖y‖ := PiLp.norm_apply_le y j
    have hop := matrixLpToLpNorm_apply_le ∞ 1 A y
    change signBilinearMax A ≤ matrixLpToLpNorm ∞ 1 A
    rw [← hst]
    calc
      |matrixBilinear A (pmOneVector s) (pmOneVector t)| ≤
          ∑ i, |(A *ᵥ pmOneVector t) i| :=
        abs_matrixBilinear_le_l1_mulVec A _ _ (fun i => by simp)
      _ = ‖Matrix.toLpLin ∞ 1 A y‖ := by
        rw [Matrix.toLpLin_apply, PiLp.norm_eq_of_L1]
        simp [y, Real.norm_eq_abs]
      _ ≤ matrixLpToLpNorm ∞ 1 A * ‖y‖ := hop
      _ = matrixLpToLpNorm ∞ 1 A := by rw [hy, mul_one]

/-! ### Rank-one duality (Exercise 4.20(b)) -/

/-- The maximum absolute coordinate of a vector on a nonempty finite index set. This helper is
used to normalize an arbitrary nonzero rank-one factorization without changing its outer
product.

**Lean implementation helper.** -/
noncomputable def maxAbsVector {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) : ℝ :=
  (Finset.univ.image (fun i : ι => |x i|)).max' (by simp)

/-- Bounds abs by max abs vector.

**Lean implementation helper.** -/
lemma abs_le_maxAbsVector {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (i : ι) : |x i| ≤ maxAbsVector x := by
  exact Finset.le_max' (Finset.univ.image (fun i : ι => |x i|)) _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- Identifies exists abs with max abs vector.

**Lean implementation helper.** -/
lemma exists_abs_eq_maxAbsVector {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) : ∃ i, |x i| = maxAbsVector x := by
  have hm := Finset.max'_mem (Finset.univ.image (fun i : ι => |x i|)) (by simp)
  rcases Finset.mem_image.mp hm with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- Shows that max abs vector is positive.

**Lean implementation helper.** -/
lemma maxAbsVector_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < maxAbsVector x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact (abs_pos.mpr hi).trans_le (abs_le_maxAbsVector x i)

/-- Frobenius pairing with an outer product is the associated bilinear form.

**Lean implementation helper.** -/
lemma matrixInner_vecMulVec_eq_bilinear
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    HDP.matrixFrobeniusInner A (Matrix.vecMulVec x y) = matrixBilinear A x y := by
  simp only [HDP.matrixFrobeniusInner, matrixBilinear, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A nonzero outer product has matrix rank exactly one.

**Lean implementation helper.** -/
lemma matrixRank_vecMulVec_eq_one {m n : ℕ}
    (x : Fin m → ℝ) (y : Fin n → ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    HDP.matrixRank (Matrix.vecMulVec x y) = 1 := by
  let u : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 x
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hu : u ≠ 0 := by simpa [u] using hx
  have hv : v ≠ 0 := by simpa [v] using hy
  change HDP.matrixRank (outerMatrix u v) = 1
  rw [HDP.matrixRank, toEuclideanLin_outerMatrix]
  exact Module.rank_eq_one_iff_finrank_eq_one.mp
    (InnerProductSpace.rank_rankOne hu hv)

/-- Normalization of a bounded nonzero outer product: its two factors can be rescaled into their
respective unit cubes without changing the matrix.

**Lean implementation helper.** -/
lemma exists_cube_factorization_of_entrywise_bounded
    {m n : Type*} [Finite m] [Finite n] [Nonempty m]
    (x : m → ℝ) (y : n → ℝ) (hx : x ≠ 0)
    (hxy : ∀ i j, |x i * y j| ≤ 1) :
    ∃ x' y', (∀ i, |x' i| ≤ 1) ∧ (∀ j, |y' j| ≤ 1) ∧
      Matrix.vecMulVec x' y' = Matrix.vecMulVec x y := by
  letI : Fintype m := Fintype.ofFinite m
  letI : Fintype n := Fintype.ofFinite n
  let a := maxAbsVector x
  have ha : 0 < a := maxAbsVector_pos hx
  obtain ⟨i₀, hi₀⟩ := exists_abs_eq_maxAbsVector x
  let x' : m → ℝ := fun i => x i / a
  let y' : n → ℝ := fun j => a * y j
  refine ⟨x', y', ?_, ?_, ?_⟩
  · intro i
    change |x i / a| ≤ 1
    rw [abs_div, abs_of_pos ha]
    exact (div_le_one ha).2 (abs_le_maxAbsVector x i)
  · intro j
    change |a * y j| ≤ 1
    rw [abs_mul, abs_of_pos ha]
    have h := hxy i₀ j
    rw [abs_mul, hi₀] at h
    exact h
  · ext i j
    simp only [Matrix.vecMulVec_apply, x', y']
    field_simp [ne_of_gt ha]

/-- `infinity->1` sign formula, rank-one duality, and failure of a quadratic analogue.

**Book Exercise 4.20.** -/
theorem exercise_4_20b_outer_product_duality {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ (x : Fin m → ℝ) (y : Fin n → ℝ), x ≠ 0 → y ≠ 0 →
      (∀ i j, |x i * y j| ≤ 1) →
      |HDP.matrixFrobeniusInner A (Matrix.vecMulVec x y)| ≤
        matrixLpToLpNorm ∞ 1 A) ∧
    ∃ Z : Matrix (Fin m) (Fin n) ℝ,
      HDP.matrixRank Z = 1 ∧ (∀ i j, |Z i j| ≤ 1) ∧
        |HDP.matrixFrobeniusInner A Z| = matrixLpToLpNorm ∞ 1 A := by
  constructor
  · intro x y hx _ hxy
    obtain ⟨x', y', hx', hy', houter⟩ :=
      exists_cube_factorization_of_entrywise_bounded x y hx hxy
    rw [← houter, matrixInner_vecMulVec_eq_bilinear,
      exercise_4_20a_infty_to_one_sign_formula A]
    exact abs_matrixBilinear_le_signBilinearMax_of_cube A x' y' hx' hy'
  · obtain ⟨s, t, hst⟩ := exists_sign_eq_signBilinearMax A
    let x : Fin m → ℝ := pmOneVector s
    let y : Fin n → ℝ := pmOneVector t
    let Z : Matrix (Fin m) (Fin n) ℝ := Matrix.vecMulVec x y
    have hx : x ≠ 0 := by
      intro h
      let i : Fin m := Classical.choice inferInstance
      have := congrFun h i
      have habs := congrArg abs this
      simp [x] at habs
    have hy : y ≠ 0 := by
      intro h
      let j : Fin n := Classical.choice inferInstance
      have := congrFun h j
      have habs := congrArg abs this
      simp [y] at habs
    refine ⟨Z, matrixRank_vecMulVec_eq_one x y hx hy, ?_, ?_⟩
    · intro i j
      change |x i * y j| ≤ 1
      simp [x, y]
    · change |HDP.matrixFrobeniusInner A (Matrix.vecMulVec x y)| = _
      rw [matrixInner_vecMulVec_eq_bilinear,
        exercise_4_20a_infty_to_one_sign_formula A]
      exact hst

/-- A coordinate column is the image of the corresponding Euclidean basis vector.

**Lean implementation helper.** -/
lemma toEuclideanLin_basisFun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ j) =
      WithLp.toLp 2 (A.col j) := by
  ext i
  simp [EuclideanSpace.basisFun_apply, Matrix.toLpLin_apply]

/-- Every matrix of authoritative rank one admits a nonzero outer-product factorization. This
closes the semantic gap between `rank Z = 1` in the source and the outer-product
parameterization used in the proof.

**Lean implementation helper.** -/
lemma exists_vecMulVec_of_matrixRank_eq_one {m n : ℕ}
    (Z : Matrix (Fin m) (Fin n) ℝ) (hZrank : HDP.matrixRank Z = 1) :
    ∃ x : Fin m → ℝ, ∃ y : Fin n → ℝ,
      x ≠ 0 ∧ y ≠ 0 ∧ Z = Matrix.vecMulVec x y := by
  classical
  let S := Z.toEuclideanLin.range
  have hfin : Module.finrank ℝ S = 1 := hZrank
  have hpos : 0 < Module.finrank ℝ S := by omega
  letI : Nontrivial S := Module.finrank_pos_iff.mp hpos
  obtain ⟨w : S, hw⟩ := exists_ne (0 : S)
  have hall : ∀ z : S, ∃ c : ℝ, c • w = z :=
    (finrank_eq_one_iff_of_nonzero' w hw).mp hfin
  let colInRange (j : Fin n) : S :=
    ⟨Z.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ j),
      ⟨EuclideanSpace.basisFun (Fin n) ℝ j, rfl⟩⟩
  choose y hy using fun j : Fin n => hall (colInRange j)
  let x : Fin m → ℝ := WithLp.ofLp (w : EuclideanSpace ℝ (Fin m))
  have hfactor : Z = Matrix.vecMulVec x y := by
    ext i j
    have hj := congrArg Subtype.val (hy j)
    change y j • (w : EuclideanSpace ℝ (Fin m)) =
      Z.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ j) at hj
    rw [toEuclideanLin_basisFun] at hj
    have hij := congrArg
      (fun z : EuclideanSpace ℝ (Fin m) => WithLp.ofLp z i) hj
    simpa [x, Matrix.vecMulVec_apply, mul_comm] using hij.symm
  have hx : x ≠ 0 := by
    intro hx
    apply hw
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    simpa [x] using hx
  have hy0 : y ≠ 0 := by
    intro hy0
    have hzero : Z = 0 := by
      rw [hfactor]
      ext i j
      simp [hy0, Matrix.vecMulVec_apply]
    have hrankzero : HDP.matrixRank Z = 0 := by
      rw [hzero]
      simp [HDP.matrixRank]
    omega
  exact ⟨x, y, hx, hy0, hfactor⟩

/-- `infinity->1` sign formula, rank-one duality, and failure of a quadratic analogue.

**Book Exercise 4.20.** -/
theorem exercise_4_20b_rank_one_duality {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ Z : Matrix (Fin m) (Fin n) ℝ, HDP.matrixRank Z = 1 →
      (∀ i j, |Z i j| ≤ 1) →
      |HDP.matrixFrobeniusInner A Z| ≤ matrixLpToLpNorm ∞ 1 A) ∧
    ∃ Z : Matrix (Fin m) (Fin n) ℝ,
      HDP.matrixRank Z = 1 ∧ (∀ i j, |Z i j| ≤ 1) ∧
        |HDP.matrixFrobeniusInner A Z| = matrixLpToLpNorm ∞ 1 A := by
  have houter := exercise_4_20b_outer_product_duality A
  constructor
  · intro Z hZrank hZbound
    obtain ⟨x, y, hx, hy, hfactor⟩ :=
      exists_vecMulVec_of_matrixRank_eq_one Z hZrank
    rw [hfactor]
    exact houter.1 x y hx hy (fun i j => by
      simpa [hfactor, Matrix.vecMulVec_apply] using hZbound i j)
  · exact houter.2

/-- `infinity->1` sign formula, rank-one duality, and failure of a quadratic analogue.

**Book Exercise 4.20.** -/
theorem exercise_4_20c_quadratic_sign_counterexample :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      Aᵀ = A ∧
      (∃ x : Fin 2 → ℝ, (∀ i, |x i| ≤ 1) ∧
        |matrixBilinear A x x| = 1) ∧
      ∀ s : Fin 2 → Bool,
        matrixBilinear A (pmOneVector s) (pmOneVector s) = 0 := by
  let a : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal a
  let x : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  refine ⟨A, ?_, ⟨x, ?_, ?_⟩, ?_⟩
  · simp [A]
  · intro i
    fin_cases i <;> norm_num [x]
  · norm_num [matrixBilinear, A, a, x, Fin.sum_univ_two,
      Matrix.diagonal_apply]
  · intro s
    cases h₀ : s 0 <;> cases h₁ : s 1 <;>
      norm_num [matrixBilinear, A, a, pmOneVector, Fin.sum_univ_two,
        Matrix.diagonal_apply, h₀, h₁]

/-! ### Exercise 4.21: cut norm -/

/-- Sum of the entries of the submatrix selected by row set `I` and column set `J`.

**Lean implementation helper.** -/
def matrixCutSum {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (I : Finset m) (J : Finset n) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ J, A i j

/-- The source's cut norm, expressed as an actual finite maximum over all row and column
subsets.

**Lean implementation helper.** -/
noncomputable def matrixCutNorm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ := by
  classical
  exact ((Finset.univ.powerset.product Finset.univ.powerset).image
    (fun IJ : Finset m × Finset n => |matrixCutSum A IJ.1 IJ.2|)).max' (by simp)

/-- Bounds abs matrix cut sum by matrix cut norm.

**Lean implementation helper.** -/
lemma abs_matrixCutSum_le_matrixCutNorm
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (I : Finset m) (J : Finset n) :
    |matrixCutSum A I J| ≤ matrixCutNorm A := by
  classical
  exact Finset.le_max'
    ((Finset.univ.powerset.product Finset.univ.powerset).image
      (fun IJ : Finset m × Finset n => |matrixCutSum A IJ.1 IJ.2|)) _
    (Finset.mem_image.mpr ⟨(I, J), by simp, rfl⟩)

/-- Shows that matrix cut norm is nonnegative.

**Lean implementation helper.** -/
lemma matrixCutNorm_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : 0 ≤ matrixCutNorm A := by
  exact (abs_nonneg (matrixCutSum A ∅ ∅)).trans
    (abs_matrixCutSum_le_matrixCutNorm A ∅ ∅)

/-- Identifies exists cut with matrix cut norm.

**Lean implementation helper.** -/
lemma exists_cut_eq_matrixCutNorm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    ∃ I : Finset m, ∃ J : Finset n,
      |matrixCutSum A I J| = matrixCutNorm A := by
  classical
  have hm := Finset.max'_mem
    ((Finset.univ.powerset.product Finset.univ.powerset).image
      (fun IJ : Finset m × Finset n => |matrixCutSum A IJ.1 IJ.2|)) (by simp)
  rcases Finset.mem_image.mp hm with ⟨IJ, _, hIJ⟩
  exact ⟨IJ.1, IJ.2, hIJ⟩

/-- The `{0,1}` indicator of a finite subset.

**Lean implementation helper.** -/
def cutIndicator {ι : Type*} [DecidableEq ι] (I : Finset ι) : ι → ℝ :=
  fun i => if i ∈ I then 1 else 0

/-- Bounds abs cut indicator by one.

**Lean implementation helper.** -/
@[simp] lemma abs_cutIndicator_le_one {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (i : ι) : |cutIndicator I i| ≤ 1 := by
  by_cases hi : i ∈ I <;> simp [cutIndicator, hi]

/-- Evaluating the matrix bilinear form on two cut indicators gives the corresponding rectangular cut sum.

**Lean implementation helper.** -/
lemma matrixBilinear_cutIndicator
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (I : Finset m) (J : Finset n) :
    matrixBilinear A (cutIndicator I) (cutIndicator J) =
      matrixCutSum A I J := by
  classical
  simp [matrixBilinear, matrixCutSum, cutIndicator, Finset.sum_ite_irrel]

/-- The matrix bilinear form turns subtraction in its left argument into subtraction of values.

**Lean implementation helper.** -/
lemma matrixBilinear_sub_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x z : m → ℝ) (y : n → ℝ) :
    matrixBilinear A (x - z) y =
      matrixBilinear A x y - matrixBilinear A z y := by
  simp only [matrixBilinear, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix bilinear form turns subtraction in its right argument into subtraction of values.

**Lean implementation helper.** -/
lemma matrixBilinear_sub_right {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y z : n → ℝ) :
    matrixBilinear A x (y - z) =
      matrixBilinear A x y - matrixBilinear A x z := by
  simp only [matrixBilinear, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Identifies pm one vector with cut indicator sub.

**Lean implementation helper.** -/
lemma pmOneVector_eq_cutIndicator_sub {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → Bool) :
    pmOneVector s =
      cutIndicator (Finset.univ.filter fun i => s i = true) -
        cutIndicator (Finset.univ.filter fun i => s i = false) := by
  funext i
  cases hi : s i <;> simp [pmOneVector, cutIndicator, hi]

/-- Cut norm is equivalent to the corresponding sign/operator formulation.

**Book Exercise 4.21.** -/
theorem exercise_4_21_cut_norm_equivalence
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : Matrix m n ℝ) :
    matrixCutNorm A ≤ matrixLpToLpNorm ∞ 1 A ∧
      matrixLpToLpNorm ∞ 1 A ≤ 4 * matrixCutNorm A := by
  classical
  constructor
  · obtain ⟨I, J, hIJ⟩ := exists_cut_eq_matrixCutNorm A
    rw [← hIJ, ← matrixBilinear_cutIndicator]
    calc
      |matrixBilinear A (cutIndicator I) (cutIndicator J)| ≤
          signBilinearMax A :=
        abs_matrixBilinear_le_signBilinearMax_of_cube A _ _
          (abs_cutIndicator_le_one I) (abs_cutIndicator_le_one J)
      _ = matrixLpToLpNorm ∞ 1 A :=
        (exercise_4_20a_infty_to_one_sign_formula A).symm
  · rw [exercise_4_20a_infty_to_one_sign_formula A]
    obtain ⟨s, t, hst⟩ := exists_sign_eq_signBilinearMax A
    rw [← hst]
    let Ipos : Finset m := Finset.univ.filter fun i => s i = true
    let Ineg : Finset m := Finset.univ.filter fun i => s i = false
    let Jpos : Finset n := Finset.univ.filter fun j => t j = true
    let Jneg : Finset n := Finset.univ.filter fun j => t j = false
    have hs : pmOneVector s = cutIndicator Ipos - cutIndicator Ineg := by
      simpa [Ipos, Ineg] using pmOneVector_eq_cutIndicator_sub s
    have ht : pmOneVector t = cutIndicator Jpos - cutIndicator Jneg := by
      simpa [Jpos, Jneg] using pmOneVector_eq_cutIndicator_sub t
    rw [hs, ht, matrixBilinear_sub_left, matrixBilinear_sub_right,
      matrixBilinear_sub_right]
    rw [matrixBilinear_cutIndicator, matrixBilinear_cutIndicator,
      matrixBilinear_cutIndicator, matrixBilinear_cutIndicator]
    let a := matrixCutSum A Ipos Jpos
    let b := matrixCutSum A Ipos Jneg
    let c := matrixCutSum A Ineg Jpos
    let d := matrixCutSum A Ineg Jneg
    have hab : |a - b - (c - d)| ≤ (|a| + |b|) + (|c| + |d|) := by
      calc
        |a - b - (c - d)| ≤ |a - b| + |c - d| := by
          have h := abs_add_le (a - b) (-(c - d))
          rw [abs_neg] at h
          simpa [sub_eq_add_neg] using h
        _ ≤ (|a| + |b|) + (|c| + |d|) := by
          gcongr
          · simpa [sub_eq_add_neg] using abs_add_le a (-b)
          · simpa [sub_eq_add_neg] using abs_add_le c (-d)
    calc
      |matrixCutSum A Ipos Jpos - matrixCutSum A Ipos Jneg -
          (matrixCutSum A Ineg Jpos - matrixCutSum A Ineg Jneg)| ≤
          (|a| + |b|) + (|c| + |d|) := by simpa [a, b, c, d] using hab
      _ ≤ (matrixCutNorm A + matrixCutNorm A) +
          (matrixCutNorm A + matrixCutNorm A) := by
        gcongr <;> apply abs_matrixCutSum_le_matrixCutNorm
      _ = 4 * matrixCutNorm A := by ring

/-- Operator norm versus row/column Euclidean norms, with equality for orthogonal families.

**Book Exercise 4.7.** -/
theorem exercise_4_7a_column_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    ‖(WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))‖ ≤
      HDP.matrixOpNorm A := by
  rw [← toEuclideanLin_basisFun A j]
  have h := matrixOpNorm_apply_le A (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa using h

/-- Pythagoras for a finite pairwise-orthogonal family, in the weighted form needed for the
corresponding exercise.

**Lean implementation helper.** -/
lemma norm_sq_sum_smul_of_pairwise_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (v : Fin n → E)
    (horth : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0)
    (a : Fin n → ℝ) :
    ‖∑ i, a i • v i‖ ^ 2 = ∑ i, a i ^ 2 * ‖v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]
    simp
    ring
  · intro j _ hji
    rw [horth i j hji.symm]
    simp
  · simp

/-- Identifies to euclidean lin with sum smul columns.

**Lean implementation helper.** -/
lemma toEuclideanLin_eq_sum_smul_columns {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    A.toEuclideanLin x = ∑ j : Fin n,
      (WithLp.ofLp x j) •
        (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Orthogonal columns give the matching operator-norm upper bound.

**Lean implementation helper.** -/
theorem matrixOpNorm_le_maxColumnL2Norm_of_pairwise_orthogonal
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ)
    (horth : ∀ i j : Fin n, i ≠ j →
      inner ℝ
        (WithLp.toLp 2 (A.col i) : EuclideanSpace ℝ (Fin m))
        (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m)) = 0) :
    HDP.matrixOpNorm A ≤ maxColumnL2Norm A := by
  rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (maxColumnL2Norm_nonneg A) ?_
  intro x
  change ‖A.toEuclideanLin x‖ ≤ maxColumnL2Norm A * ‖x‖
  rw [toEuclideanLin_eq_sum_smul_columns]
  have hnorm := norm_sq_sum_smul_of_pairwise_orthogonal
    (fun j : Fin n =>
      (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))) horth
    (WithLp.ofLp x)
  have hsq : ‖∑ j : Fin n, (WithLp.ofLp x j) •
        (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))‖ ^ 2 ≤
      (maxColumnL2Norm A * ‖x‖) ^ 2 := by
    rw [hnorm]
    calc
      (∑ j : Fin n, WithLp.ofLp x j ^ 2 *
          ‖(WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))‖ ^ 2) ≤
          ∑ j : Fin n, WithLp.ofLp x j ^ 2 * maxColumnL2Norm A ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            gcongr
            exact column_norm_le_maxColumnL2Norm A j
      _ = (maxColumnL2Norm A * ‖x‖) ^ 2 := by
        rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  nlinarith [norm_nonneg
    (∑ j : Fin n, (WithLp.ofLp x j) •
      (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m))),
    mul_nonneg (maxColumnL2Norm_nonneg A) (norm_nonneg x)]

/-- Pairwise-orthogonal columns make the operator norm exactly the largest column norm.

**Book Exercise 4.7(a).** -/
theorem exercise_4_7a_column_eq_of_pairwise_orthogonal
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ)
    (horth : ∀ i j : Fin n, i ≠ j →
      inner ℝ
        (WithLp.toLp 2 (A.col i) : EuclideanSpace ℝ (Fin m))
        (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m)) = 0) :
    HDP.matrixOpNorm A = maxColumnL2Norm A := by
  apply le_antisymm
  · exact matrixOpNorm_le_maxColumnL2Norm_of_pairwise_orthogonal A horth
  · obtain ⟨j, hj⟩ := exists_column_eq_maxColumnL2Norm A
    rw [← hj]
    exact exercise_4_7a_column_le A j

/-- Operator norm versus row/column Euclidean norms, with equality for orthogonal families.

**Book Exercise 4.7.** -/
theorem exercise_4_7c_row_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) :
    ‖(WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))‖ ≤
      HDP.matrixOpNorm A := by
  have h := exercise_4_7a_column_le Aᵀ i
  simpa [HDP.matrixOpNorm_transpose] using h

/-- Shows that exercise 4 7c row eq of pairwise is orthogonal.

**Book Exercise 4.7(c).** -/
theorem exercise_4_7c_row_eq_of_pairwise_orthogonal
    {m n : ℕ} [Nonempty (Fin m)]
    (A : Matrix (Fin m) (Fin n) ℝ)
    (horth : ∀ i j : Fin m, i ≠ j →
      inner ℝ
        (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (A.row j) : EuclideanSpace ℝ (Fin n)) = 0) :
    HDP.matrixOpNorm A = maxRowL2Norm A := by
  have h := exercise_4_7a_column_eq_of_pairwise_orthogonal Aᵀ horth
  simpa [HDP.matrixOpNorm_transpose, maxColumnL2Norm, maxRowL2Norm] using h

/-! ### Exercise 4.9: Walsh matrices -/

/-- The recursively doubled index set used by the block definition of Walsh matrices. Its
cardinality is exactly `2^k`.

**Lean implementation helper.** -/
def WalshIndex : ℕ → Type
  | 0 => Unit
  | k + 1 => WalshIndex k ⊕ WalshIndex k

instance walshIndexFintype : ∀ k, Fintype (WalshIndex k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 =>
      letI := walshIndexFintype k
      inferInstanceAs (Fintype (WalshIndex k ⊕ WalshIndex k))

instance walshIndexDecidableEq : ∀ k, DecidableEq (WalshIndex k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 =>
      letI := walshIndexDecidableEq k
      inferInstanceAs (DecidableEq (WalshIndex k ⊕ WalshIndex k))

/-- Computes the cardinality of walsh index.

**Lean implementation helper.** -/
@[simp] theorem card_walshIndex (k : ℕ) : Fintype.card (WalshIndex k) = 2 ^ k := by
  induction k with
  | zero => simp [WalshIndex]
  | succ k ih =>
      change Fintype.card (WalshIndex k ⊕ WalshIndex k) = _
      rw [Fintype.card_sum, ih]
      omega

/-- Walsh's block recursion, with `W₀ = [1]`. Thus the source's `W₁` is `walshMatrix 1`.

**Lean implementation helper.** -/
def walshMatrix : (k : ℕ) → Matrix (WalshIndex k) (WalshIndex k) ℝ
  | 0 => 1
  | k + 1 => Matrix.fromBlocks (walshMatrix k) (walshMatrix k)
      (walshMatrix k) (-walshMatrix k)

/-- Every Walsh matrix is symmetric.

**Lean implementation helper.** -/
@[simp] theorem walshMatrix_transpose (k : ℕ) : (walshMatrix k)ᵀ = walshMatrix k := by
  induction k with
  | zero => simp [walshMatrix]
  | succ k ih =>
      change (Matrix.fromBlocks (walshMatrix k) (walshMatrix k)
        (walshMatrix k) (-walshMatrix k))ᵀ = _
      rw [Matrix.fromBlocks_transpose]
      simp [ih, walshMatrix]

/-- The unnormalised Walsh identity `WₖᵀWₖ = 2ᵏ I`.

**Lean implementation helper.** -/
theorem walshMatrix_gram (k : ℕ) :
    (walshMatrix k)ᵀ * walshMatrix k = (2 ^ k : ℝ) • 1 := by
  induction k with
  | zero => simp [walshMatrix]
  | succ k ih =>
      have ih' : walshMatrix k * walshMatrix k = (2 ^ k : ℝ) • 1 := by
        nth_rw 1 [← walshMatrix_transpose k]
        exact ih
      change (Matrix.fromBlocks (walshMatrix k) (walshMatrix k)
        (walshMatrix k) (-walshMatrix k))ᵀ *
          Matrix.fromBlocks (walshMatrix k) (walshMatrix k)
            (walshMatrix k) (-walshMatrix k) =
          (2 ^ (k + 1) : ℝ) •
            (1 : Matrix (WalshIndex k ⊕ WalshIndex k)
              (WalshIndex k ⊕ WalshIndex k) ℝ)
      rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
      simp only [walshMatrix_transpose, Matrix.transpose_neg, Matrix.mul_neg,
        Matrix.neg_mul, neg_neg]
      ext i j
      cases i <;> cases j <;>
        simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply, ih', pow_succ]
      all_goals split <;> ring

/-- Walsh/Hadamard matrices are orthogonal after normalization.

**Book Exercise 4.9.** -/
theorem exercise_4_9_walsh_orthogonal (k : ℕ) :
    (((Real.sqrt (2 ^ k : ℝ))⁻¹ • walshMatrix k)ᵀ *
      ((Real.sqrt (2 ^ k : ℝ))⁻¹ • walshMatrix k)) = 1 := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, walshMatrix_gram]
  have hpos : 0 < (2 ^ k : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 ^ k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply, if_pos, Matrix.smul_apply, smul_eq_mul]
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt hpos.le]
  · simp [Matrix.smul_apply, hij]

/-- For a unit vector, a symmetric quadratic form is bounded by the spectral norm.

**Lean implementation helper.** -/
theorem symmetric_rayleigh_le_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    |inner ℝ x (A.toEuclideanLin x)| ≤ HDP.matrixOpNorm A := by
  calc
    |inner ℝ x (A.toEuclideanLin x)|
        ≤ ‖x‖ * ‖A.toEuclideanLin x‖ := abs_real_inner_le_norm x _
    _ ≤ ‖x‖ * (HDP.matrixOpNorm A * ‖x‖) := by
      gcongr
      exact matrixOpNorm_apply_le A x
    _ = HDP.matrixOpNorm A := by rw [hx]; ring

/-- Identifies op norm with largest singular value.

**Lean implementation helper.** -/
theorem opNorm_eq_largestSingularValue {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm A = HDP.matrixSingularValue A 0 := by
  have hnpos : 0 < n := by
    simpa using Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n))
  let i : Fin n := ⟨0, hnpos⟩
  have hcf := singularValueMinMax A i
  rcases hcf.2.2 with ⟨V, hVdim, hupper, x, hxV, hxnorm, hxattain⟩
  have hVtop : V = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [i, finrank_euclideanSpace_fin] using hVdim
  apply le_antisymm
  · rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _
      (HDP.matrixSingularValue_nonneg A 0) ?_
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · let z := ‖y‖⁻¹ • y
      have hz : ‖z‖ = 1 := by simp [z, norm_smul, hy]
      have hzV : z ∈ V := by rw [hVtop]; exact Submodule.mem_top
      have hzbound := hupper z hzV hz
      have hydecomp : y = ‖y‖ • z := by
        simp [z, smul_smul, hy]
      calc
        ‖A.toEuclideanLin y‖ = ‖A.toEuclideanLin (‖y‖ • z)‖ :=
          congrArg (fun w => ‖A.toEuclideanLin w‖) hydecomp
        _ = ‖y‖ * ‖A.toEuclideanLin z‖ := by
          rw [map_smul, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg y)]
        _
            ≤ ‖y‖ * HDP.matrixSingularValue A i :=
          mul_le_mul_of_nonneg_left hzbound (norm_nonneg y)
        _ = HDP.matrixSingularValue A 0 * ‖y‖ := by
          change ‖y‖ * HDP.matrixSingularValue A 0 = _
          ring
  · have hattain := singularValue_attained A i
    change HDP.matrixSingularValue A 0 ≤ HDP.matrixOpNorm A
    calc
      HDP.matrixSingularValue A 0 =
          ‖A.toEuclideanLin (rightSingularBasis A i)‖ := by
        change HDP.matrixSingularValue A i = _
        exact (norm_apply_rightSingularVector A i).symm
      _ ≤ HDP.matrixOpNorm A * ‖rightSingularBasis A i‖ :=
        matrixOpNorm_apply_le A _
      _ = HDP.matrixOpNorm A := by rw [hattain.1, mul_one]

/-! ### Exact source formulations from Definitions 4.1.8--4.1.12 -/

/-- The squared Frobenius norm is the sum of the squared singular values (with Mathlib's
zero-padded rectangular indexing).

**Lean implementation helper.** -/
theorem frobeniusNorm_sq_eq_sum_singularValues {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm A ^ 2 =
      ∑ i : Fin n, HDP.matrixSingularValue A i ^ 2 := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    A.toEuclideanLin.adjoint.comp A.toEuclideanLin
  have htraceBasis := LinearMap.trace_eq_sum_inner T
    (EuclideanSpace.basisFun (Fin n) ℝ)
  have htraceFrob : (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))) T =
      HDP.matrixFrobeniusNorm A ^ 2 := by
    rw [htraceBasis, frobeniusNorm_sq_eq_sum_column_norm_sq]
    apply Finset.sum_congr rfl
    intro j _
    change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)
        (A.toEuclideanLin.adjoint (A.toEuclideanLin
          (EuclideanSpace.basisFun (Fin n) ℝ j))) = _
    rw [LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      toEuclideanLin_basisFun]
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  have htraceEig :=
    A.toEuclideanLin.isSymmetric_adjoint_comp_self.trace_eq_sum_eigenvalues hn
  rw [← htraceFrob, htraceEig]
  push_cast
  change (∑ i : Fin n,
      A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues hn i) = _
  apply Finset.sum_congr rfl
  intro i _
  exact (A.toEuclideanLin.sq_singularValues_fin hn i).symm

/-- Identifies frobenius norm with sqrt sum singular values.

**Lean implementation helper.** -/
theorem frobeniusNorm_eq_sqrt_sum_singularValues {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm A =
      Real.sqrt (∑ i : Fin n, HDP.matrixSingularValue A i ^ 2) := by
  rw [← frobeniusNorm_sq_eq_sum_singularValues A,
    Real.sqrt_sq (HDP.matrixFrobeniusNorm_nonneg A)]

/-- Canonical source-facing bundle for the corresponding lemma.

**Book Lemma 4.1.11.** -/
theorem lemma_4_1_11 {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm A =
        Real.sqrt (∑ i : Fin n, HDP.matrixSingularValue A i ^ 2) ∧
      HDP.matrixOpNorm A = HDP.matrixSingularValue A 0 :=
  ⟨frobeniusNorm_eq_sqrt_sum_singularValues A,
    opNorm_eq_largestSingularValue A⟩

/-- The operator norm of the identity matrix is at most `1`.

**Lean implementation helper.** -/
lemma matrixOpNorm_one_le (n : ℕ) :
    HDP.matrixOpNorm (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 := by
  rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simp

/-- Bounds matrix operator norm orthogonal by one.

**Lean implementation helper.** -/
lemma matrixOpNorm_orthogonal_le_one {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    HDP.matrixOpNorm Q ≤ 1 := by
  have hgram : HDP.gramMatrix Q = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hQ
  have hs := HDP.matrixOpNorm_sq_eq_gram Q
  rw [hgram] at hs
  nlinarith [HDP.matrixOpNorm_nonneg Q, matrixOpNorm_one_le n]

/-- Left and right multiplication by orthogonal matrices preserves both the Frobenius and
Euclidean operator norms.

**Lean implementation helper.** -/
theorem orthogonalInvariance {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm (Q * A * R) = HDP.matrixFrobeniusNorm A ∧
      HDP.matrixOpNorm (Q * A * R) = HDP.matrixOpNorm A := by
  have hQtQ : Qᵀ * Q = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp hQ
  have hRRt : R * Rᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hR
  constructor
  · have hsq : HDP.matrixFrobeniusNorm (Q * A * R) ^ 2 =
        HDP.matrixFrobeniusNorm A ^ 2 := by
      rw [frobeniusNorm_sq_eq_inner, frobeniusInner_eq_trace,
        frobeniusNorm_sq_eq_inner, frobeniusInner_eq_trace]
      simp only [Matrix.transpose_mul]
      calc
        ((Rᵀ * (Aᵀ * Qᵀ)) * (Q * A * R)).trace =
            (Rᵀ * (Aᵀ * (Qᵀ * Q) * A) * R).trace := by
              congr 1
              simp only [Matrix.mul_assoc]
        _ = (Rᵀ * (Aᵀ * A) * R).trace := by rw [hQtQ]; simp
        _ = (Rᵀ * ((Aᵀ * A) * R)).trace := by rw [Matrix.mul_assoc]
        _ = (((Aᵀ * A) * R) * Rᵀ).trace :=
          Matrix.trace_mul_comm Rᵀ ((Aᵀ * A) * R)
        _ = ((Aᵀ * A) * (R * Rᵀ)).trace := by rw [Matrix.mul_assoc]
        _ = (Aᵀ * A).trace := by rw [hRRt]; simp
    nlinarith [HDP.matrixFrobeniusNorm_nonneg (Q * A * R),
      HDP.matrixFrobeniusNorm_nonneg A]
  · apply le_antisymm
    · calc
        HDP.matrixOpNorm (Q * A * R) ≤
            HDP.matrixOpNorm (Q * A) * HDP.matrixOpNorm R :=
          HDP.matrixOpNorm_mul (Q * A) R
        _ ≤ (HDP.matrixOpNorm Q * HDP.matrixOpNorm A) *
            HDP.matrixOpNorm R := by
          exact mul_le_mul_of_nonneg_right (HDP.matrixOpNorm_mul Q A)
            (HDP.matrixOpNorm_nonneg R)
        _ ≤ HDP.matrixOpNorm A := by
          have hQ1 := matrixOpNorm_orthogonal_le_one Q hQ
          have hR1 := matrixOpNorm_orthogonal_le_one R hR
          calc
            (HDP.matrixOpNorm Q * HDP.matrixOpNorm A) *
                HDP.matrixOpNorm R ≤
                (1 * HDP.matrixOpNorm A) * HDP.matrixOpNorm R := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hQ1
                  (HDP.matrixOpNorm_nonneg A))
                (HDP.matrixOpNorm_nonneg R)
            _ ≤ (1 * HDP.matrixOpNorm A) * 1 := by
              exact mul_le_mul_of_nonneg_left hR1
                (mul_nonneg zero_le_one (HDP.matrixOpNorm_nonneg A))
            _ = HDP.matrixOpNorm A := by ring
    · have hrecover : Qᵀ * (Q * A * R) * Rᵀ = A := by
        calc
          Qᵀ * (Q * A * R) * Rᵀ = (Qᵀ * Q) * A * (R * Rᵀ) := by
            simp only [Matrix.mul_assoc]
          _ = A := by rw [hQtQ, hRRt]; simp
      calc
        HDP.matrixOpNorm A =
            HDP.matrixOpNorm (Qᵀ * (Q * A * R) * Rᵀ) := by rw [hrecover]
        _ ≤ HDP.matrixOpNorm (Qᵀ * (Q * A * R)) *
            HDP.matrixOpNorm Rᵀ := HDP.matrixOpNorm_mul _ _
        _ ≤ (HDP.matrixOpNorm Qᵀ * HDP.matrixOpNorm (Q * A * R)) *
            HDP.matrixOpNorm Rᵀ := by
          exact mul_le_mul_of_nonneg_right (HDP.matrixOpNorm_mul _ _)
            (HDP.matrixOpNorm_nonneg Rᵀ)
        _ ≤ HDP.matrixOpNorm (Q * A * R) := by
          rw [HDP.matrixOpNorm_transpose Q, HDP.matrixOpNorm_transpose R]
          have hQ1 := matrixOpNorm_orthogonal_le_one Q hQ
          have hR1 := matrixOpNorm_orthogonal_le_one R hR
          calc
            (HDP.matrixOpNorm Q * HDP.matrixOpNorm (Q * A * R)) *
                HDP.matrixOpNorm R ≤
                (1 * HDP.matrixOpNorm (Q * A * R)) *
                  HDP.matrixOpNorm R := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hQ1
                  (HDP.matrixOpNorm_nonneg (Q * A * R)))
                (HDP.matrixOpNorm_nonneg R)
            _ ≤ (1 * HDP.matrixOpNorm (Q * A * R)) * 1 := by
              exact mul_le_mul_of_nonneg_left hR1
                (mul_nonneg zero_le_one
                  (HDP.matrixOpNorm_nonneg (Q * A * R)))
            _ = HDP.matrixOpNorm (Q * A * R) := by ring

/-- Compatibility alias with the source number.

**Book Lemma 4.1.10.** -/
theorem lemma_4_1_10 {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm (Q * A * R) = HDP.matrixFrobeniusNorm A ∧
      HDP.matrixOpNorm (Q * A * R) = HDP.matrixOpNorm A :=
  orthogonalInvariance A Q R hQ hR

/-- The nonzero-vector ratio values in the corresponding definition.

**Lean implementation helper.** -/
def operatorRatioValues {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {z | ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧
    z = ‖A.toEuclideanLin x‖ / ‖x‖}

/-- The unit-ball values in the corresponding definition.

**Lean implementation helper.** -/
def operatorUnitBallValues {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {z | ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 ∧
    z = ‖A.toEuclideanLin x‖}

/-- The unit-sphere values in the corresponding definition.

**Lean implementation helper.** -/
def operatorUnitSphereValues {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {z | ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
    z = ‖A.toEuclideanLin x‖}

/-- The unit bilinear values in the corresponding definition.

**Lean implementation helper.** -/
def operatorBilinearUnitValues {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {z | ∃ x : EuclideanSpace ℝ (Fin n),
    ∃ y : EuclideanSpace ℝ (Fin m), ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      z = |inner ℝ y (A.toEuclideanLin x)|}

/-- All four finite-dimensional maximum formulations of the Euclidean operator norm agree.

**Lean implementation helper.** -/
theorem operatorNorm_fourMaxima {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsGreatest (operatorRatioValues A) (HDP.matrixOpNorm A) ∧
      IsGreatest (operatorUnitBallValues A) (HDP.matrixOpNorm A) ∧
      IsGreatest (operatorUnitSphereValues A) (HDP.matrixOpNorm A) ∧
      IsGreatest (operatorBilinearUnitValues A) (HDP.matrixOpNorm A) := by
  have hn : 0 < n := by
    simpa using Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n))
  let i : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℝ (Fin n) := rightSingularBasis A i
  have hx : ‖x‖ = 1 := (rightSingularBasis A).norm_eq_one i
  have hAx : ‖A.toEuclideanLin x‖ = HDP.matrixOpNorm A := by
    rw [opNorm_eq_largestSingularValue A]
    exact norm_apply_rightSingularVector A i
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  have hratio : IsGreatest (operatorRatioValues A) (HDP.matrixOpNorm A) := by
    constructor
    · exact ⟨x, hx0, by simp [hAx, hx]⟩
    · rintro z ⟨w, hw, rfl⟩
      simpa [HDP.matrixOpNorm, Matrix.l2_opNorm_def] using
        A.toEuclideanLin.toContinuousLinearMap.ratio_le_opNorm w
  have hball : IsGreatest (operatorUnitBallValues A) (HDP.matrixOpNorm A) := by
    constructor
    · exact ⟨x, hx.le, hAx.symm⟩
    · rintro z ⟨w, hw, rfl⟩
      exact (matrixOpNorm_apply_le A w).trans
        (mul_le_of_le_one_right (HDP.matrixOpNorm_nonneg A) hw)
  have hsphere :
      IsGreatest (operatorUnitSphereValues A) (HDP.matrixOpNorm A) := by
    constructor
    · exact ⟨x, hx, hAx.symm⟩
    · rintro z ⟨w, hw, rfl⟩
      simpa [hw] using matrixOpNorm_apply_le A w
  refine ⟨hratio, hball, hsphere, ?_⟩
  constructor
  · by_cases hzero : HDP.matrixOpNorm A = 0
    · let j : Fin m := Classical.choice (inferInstance : Nonempty (Fin m))
      let y : EuclideanSpace ℝ (Fin m) := EuclideanSpace.basisFun (Fin m) ℝ j
      have hy : ‖y‖ = 1 := by simp [y]
      have hAxx : A.toEuclideanLin x = 0 := norm_eq_zero.mp (hAx.trans hzero)
      exact ⟨x, y, hx, hy, by simp [hzero, hAxx]⟩
    · let y : EuclideanSpace ℝ (Fin m) :=
        (HDP.matrixOpNorm A)⁻¹ • A.toEuclideanLin x
      have hoppos : 0 < HDP.matrixOpNorm A :=
        lt_of_le_of_ne (HDP.matrixOpNorm_nonneg A) (Ne.symm hzero)
      have hy : ‖y‖ = 1 := by
        simp [y, norm_smul, hAx, abs_of_pos hoppos, hzero]
      refine ⟨x, y, hx, hy, ?_⟩
      rw [show inner ℝ y (A.toEuclideanLin x) =
          (HDP.matrixOpNorm A)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 by
        simp [y, inner_smul_left]]
      rw [hAx, inv_mul_eq_div, sq, mul_div_cancel_left₀ _ hzero,
        abs_of_pos hoppos]
  · rintro z ⟨w, y, hw, hy, rfl⟩
    calc
      |inner ℝ y (A.toEuclideanLin w)| ≤ ‖y‖ * ‖A.toEuclideanLin w‖ :=
        abs_real_inner_le_norm y _
      _ ≤ ‖y‖ * (HDP.matrixOpNorm A * ‖w‖) := by
        gcongr
        exact matrixOpNorm_apply_le A w
      _ = HDP.matrixOpNorm A := by rw [hw, hy]; ring

/-- Canonical source-facing name for the corresponding definition.

**Book Definition 4.1.8.** -/
theorem definition_4_1_8 {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsGreatest (operatorRatioValues A) (HDP.matrixOpNorm A) ∧
      IsGreatest (operatorUnitBallValues A) (HDP.matrixOpNorm A) ∧
      IsGreatest (operatorUnitSphereValues A) (HDP.matrixOpNorm A) ∧
      IsGreatest (operatorBilinearUnitValues A) (HDP.matrixOpNorm A) :=
  operatorNorm_fourMaxima A

/-- Every induced finite-dimensional `ℓᵖ → ℓᑫ` norm is attained on its
closed unit ball, including the endpoint exponents `1` and `∞`.

**Book Remark 4.1.9.** -/
theorem matrixLpToLpNorm_attained (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    ∃ x : WithLp p (n → ℝ), ‖x‖ ≤ 1 ∧
      ‖Matrix.toLpLin p q A x‖ = matrixLpToLpNorm p q A := by
  let L := (Matrix.toLpLin p q A).toContinuousLinearMap
  let K : Set (WithLp p (n → ℝ)) := Metric.closedBall 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  obtain ⟨x, hxK, hxmax⟩ :=
    hK.exists_isMaxOn hKne L.continuous.norm.continuousOn
  have hx : ‖x‖ ≤ 1 := by
    simpa [K, Metric.mem_closedBall] using hxK
  have hmax0 : 0 ≤ ‖L x‖ := norm_nonneg _
  have hnorm_le : ‖L‖ ≤ ‖L x‖ := by
    apply L.opNorm_le_bound hmax0
    intro y
    by_cases hy : y = 0
    · subst y
      simp
    · have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      let z : WithLp p (n → ℝ) := ‖y‖⁻¹ • y
      have hzK : z ∈ K := by
        simp [K, z, Metric.mem_closedBall, norm_smul,
          inv_mul_cancel₀ hypos.ne']
      have hzmax := hxmax hzK
      change ‖L z‖ ≤ ‖L x‖ at hzmax
      have hscale : ‖L z‖ = ‖y‖⁻¹ * ‖L y‖ := by
        simp [z, norm_smul]
      rw [hscale] at hzmax
      calc
        ‖L y‖ = ‖y‖ * (‖y‖⁻¹ * ‖L y‖) := by field_simp
        _ ≤ ‖y‖ * ‖L x‖ :=
          mul_le_mul_of_nonneg_left hzmax (norm_nonneg y)
        _ = ‖L x‖ * ‖y‖ := mul_comm _ _
  have hmax_le : ‖L x‖ ≤ ‖L‖ := by
    calc
      ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg L)
      _ = ‖L‖ := mul_one _
  refine ⟨x, hx, ?_⟩
  change ‖L x‖ = ‖L‖
  exact le_antisymm hmax_le hnorm_le

/-
/-- Values of the `ℓᵖ` matrix bilinear form on the primal and dual closed
unit balls.

**Lean implementation helper.** -/
def matrixLpBilinearUnitBallValues (p q q' : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : Set ℝ :=
  {z | ∃ x : WithLp p (n → ℝ), ∃ y : WithLp q' (m → ℝ),
    ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      z = |finiteLpPairing y (Matrix.toLpLin p q A x)|}

/-- The general induced `ℓᵖ → ℓᑫ` norm equals the maximum of the associated
bilinear form over the primal `ℓᵖ` and conjugate `ℓ^{q'}` unit balls.

**Book Remark 4.1.9.** -/
theorem matrixLpToLpNorm_bilinear_isGreatest
    (p q q' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [Fact (1 ≤ q')] [q'.HolderConjugate q]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    IsGreatest (matrixLpBilinearUnitBallValues p q q' A)
      (matrixLpToLpNorm p q A) := by
  obtain ⟨x, hx, hAx⟩ := matrixLpToLpNorm_attained p q A
  obtain ⟨y, hy, hpair⟩ := finiteLpPairing_exists_norming q' q
    (Matrix.toLpLin p q A x)
  constructor
  · refine ⟨x, y, hx, hy, ?_⟩
    rw [hpair, abs_of_nonneg (norm_nonneg _), hAx]
  · rintro z ⟨u, v, hu, hv, rfl⟩
    calc
      |finiteLpPairing v (Matrix.toLpLin p q A u)| ≤
          ‖v‖ * ‖Matrix.toLpLin p q A u‖ :=
        finiteLpPairing_abs_le q' q v _
      _ ≤ 1 * (matrixLpToLpNorm p q A * ‖u‖) := by
        exact mul_le_mul hv (matrixLpToLpNorm_apply_le p q A u)
          (norm_nonneg _) zero_le_one
      _ ≤ 1 * (matrixLpToLpNorm p q A * 1) := by
        gcongr
        exact norm_nonneg _
      _ = matrixLpToLpNorm p q A := by ring
-/

/-- The same induced-norm construction works for arbitrary finite-dimensional `p → q` norms,
including the endpoint `∞`.

**Book Remark 4.1.9.** -/
theorem remark_4_1_9 (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (x : WithLp p (n → ℝ)) :
    ‖Matrix.toLpLin p q A x‖ ≤ matrixLpToLpNorm p q A * ‖x‖ :=
  matrixLpToLpNorm_apply_le p q A x

/-- For a real symmetric matrix the spectral norm is the maximum absolute Rayleigh quotient on
the unit sphere.

**Lean implementation helper.** -/
theorem symmetricRayleighFormula {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    IsGreatest
      {z : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ = 1 ∧ z = |inner ℝ x (A.toEuclideanLin x)|}
      (HDP.matrixOpNorm A) := by
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    A.toEuclideanLin.toContinuousLinearMap
  have hsymm : T.IsSymmetric := by
    change A.toEuclideanLin.IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let i : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty := by
    refine ⟨EuclideanSpace.basisFun (Fin n) ℝ i, ?_⟩
    simp
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      |inner ℝ x (T x)|) := by fun_prop
  obtain ⟨x, hx, hxmax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
      hsphere hcont.continuousOn
  have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
  have hTx : |inner ℝ x (T x)| = ‖T‖ := by
    apply le_antisymm
    · simpa [T, HDP.matrixOpNorm, Matrix.l2_opNorm_def] using
        symmetric_rayleigh_le_opNorm A x hxnorm
    · rw [T.norm_eq_iSup_rayleighQuotient hsymm]
      refine ciSup_le fun z => ?_
      by_cases hz : z = 0
      · simp [hz]
      · let y : EuclideanSpace ℝ (Fin n) := ‖z‖⁻¹ • z
        have hynorm : ‖y‖ = 1 := by simp [y, norm_smul, hz]
        have hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          simpa [Metric.mem_sphere] using hynorm
        have hmax := hxmax hy
        have hray : T.rayleighQuotient y = T.rayleighQuotient z := by
          exact T.rayleigh_smul z (inv_ne_zero (norm_ne_zero_iff.mpr hz))
        calc
          |T.rayleighQuotient z| = |T.rayleighQuotient y| := by rw [hray]
          _ = |inner ℝ y (T y)| := by
            simp [ContinuousLinearMap.rayleighQuotient,
              ContinuousLinearMap.reApplyInnerSelf_apply, hynorm,
              real_inner_comm]
          _ ≤ |inner ℝ x (T x)| := hmax
  constructor
  · refine ⟨x, hxnorm, ?_⟩
    simpa [T, HDP.matrixOpNorm, Matrix.l2_opNorm_def,
      real_inner_comm] using hTx.symm
  · rintro z ⟨y, hy, rfl⟩
    exact symmetric_rayleigh_le_opNorm A y hy

/-- Canonical source-facing name for the corresponding remark.

**Book Remark 4.1.12.** -/
theorem remark_4_1_12 {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    IsGreatest
      {z : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ = 1 ∧ z = |inner ℝ x (A.toEuclideanLin x)|}
      (HDP.matrixOpNorm A) :=
  symmetricRayleighFormula A hA

/-! ### Promoted exercises completing the matrix-norm section -/

/-- Isometric coordinate embedding used to compare a submatrix with its ambient matrix in the
corresponding exercise.

**Lean implementation helper.** -/
noncomputable def euclideanCoordinateEmbedding {k n : ℕ}
    (e : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ j : Fin k, (WithLp.ofLp x j) •
    EuclideanSpace.basisFun (Fin n) ℝ (e j)

/-- Embedding selected coordinates into the ambient Euclidean space preserves norm.

**Lean implementation helper.** -/
lemma euclideanCoordinateEmbedding_norm {k n : ℕ} (e : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin k)) :
    ‖euclideanCoordinateEmbedding e x‖ = ‖x‖ := by
  have horth : ∀ i j : Fin k, i ≠ j →
      inner ℝ
        (EuclideanSpace.basisFun (Fin n) ℝ (e i))
        (EuclideanSpace.basisFun (Fin n) ℝ (e j)) = 0 := by
    intro i j hij
    rw [EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply, e.injective.ne hij]
  have hsq := norm_sq_sum_smul_of_pairwise_orthogonal
    (fun j : Fin k => EuclideanSpace.basisFun (Fin n) ℝ (e j)) horth
    (WithLp.ofLp x)
  change ‖euclideanCoordinateEmbedding e x‖ ^ 2 = _ at hsq
  have hright : (∑ i : Fin k, WithLp.ofLp x i ^ 2 *
      ‖EuclideanSpace.basisFun (Fin n) ℝ (e i)‖ ^ 2) = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [hright] at hsq
  nlinarith [norm_nonneg (euclideanCoordinateEmbedding e x), norm_nonneg x]

/-- The bilinear form of an ambient matrix on coordinate embeddings equals the bilinear form of the corresponding submatrix.

**Lean implementation helper.** -/
lemma euclideanCoordinateEmbedding_bilinear {k l m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin k ↪ Fin m) (c : Fin l ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (euclideanCoordinateEmbedding r y)
      (A.toEuclideanLin (euclideanCoordinateEmbedding c x)) =
    inner ℝ y ((A.submatrix r c).toEuclideanLin x) := by
  have hentry (i : Fin k) (j : Fin l) :
      inner ℝ
        (EuclideanSpace.basisFun (Fin m) ℝ (r i))
        (A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ (c j))) =
        A (r i) (c j) := by
    rw [toEuclideanLin_basisFun, EuclideanSpace.basisFun_inner]
    rfl
  simp only [euclideanCoordinateEmbedding, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  simp_rw [hentry]
  simp only [PiLp.inner_apply, Real.inner_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.submatrix]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

/-- Operator-norm axioms, transpose invariance, submultiplicativity, and submatrix monotonicity.

**Book Exercise 4.2.** -/
theorem exercise_4_2d_submatrix {m n k l : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin k ↪ Fin m) (c : Fin l ↪ Fin n) :
    HDP.matrixOpNorm (A.submatrix r c) ≤ HDP.matrixOpNorm A := by
  by_cases hk : k = 0
  · subst k
    have hz : A.submatrix r c = 0 := by ext i; exact Fin.elim0 i
    rw [hz, HDP.matrixOpNorm_zero]
    exact HDP.matrixOpNorm_nonneg A
  by_cases hl : l = 0
  · subst l
    have hz : A.submatrix r c = 0 := by ext i j; exact Fin.elim0 j
    rw [hz, HDP.matrixOpNorm_zero]
    exact HDP.matrixOpNorm_nonneg A
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
  letI : Nonempty (Fin l) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hl)
  letI : Nonempty (Fin m) :=
    ⟨r (Classical.choice (inferInstance : Nonempty (Fin k)))⟩
  letI : Nonempty (Fin n) :=
    ⟨c (Classical.choice (inferInstance : Nonempty (Fin l)))⟩
  rcases (operatorNorm_fourMaxima (A.submatrix r c)).2.2.2.1 with
    ⟨x, y, hx, hy, hmax⟩
  have hfull := (operatorNorm_fourMaxima A).2.2.2.2
  have hmem : |inner ℝ (euclideanCoordinateEmbedding r y)
      (A.toEuclideanLin (euclideanCoordinateEmbedding c x))| ≤
      HDP.matrixOpNorm A := by
    apply hfull
    exact ⟨euclideanCoordinateEmbedding c x,
      euclideanCoordinateEmbedding r y,
      by simpa [euclideanCoordinateEmbedding_norm] using hx,
      by simpa [euclideanCoordinateEmbedding_norm] using hy, rfl⟩
  rw [euclideanCoordinateEmbedding_bilinear] at hmem
  exact hmax ▸ hmem

/-- Derives linear coefficient zero from quadratic bound.

**Lean implementation helper.** -/
lemma linear_coefficient_zero_of_quadratic_bound (c D : ℝ) (hD : 0 ≤ D)
    (h : ∀ t : ℝ, 2 * t * c ≤ t ^ 2 * D) : c = 0 := by
  by_cases hDz : D = 0
  · have h1 := h 1
    have hm := h (-1)
    rw [hDz] at h1 hm
    norm_num at h1 hm
    linarith
  · have hc := h (c / D)
    field_simp [hDz] at hc
    nlinarith [sq_nonneg c]

/-- Operator norm versus row/column Euclidean norms, with equality for orthogonal families.

**Book Exercise 4.7.** -/
theorem exercise_4_7b_column_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) (hij : j ≠ i)
    (hi : HDP.matrixOpNorm A =
      ‖(WithLp.toLp 2 (A.col i) : EuclideanSpace ℝ (Fin m))‖) :
    inner ℝ
      (WithLp.toLp 2 (A.col i) : EuclideanSpace ℝ (Fin m))
      (WithLp.toLp 2 (A.col j) : EuclideanSpace ℝ (Fin m)) = 0 := by
  let u : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (A.col i)
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (A.col j)
  let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i
  let ej : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ j
  have hvi : ‖v‖ ≤ HDP.matrixOpNorm A := exercise_4_7a_column_le A j
  have hD : 0 ≤ HDP.matrixOpNorm A ^ 2 - ‖v‖ ^ 2 := by
    nlinarith [HDP.matrixOpNorm_nonneg A, norm_nonneg v]
  apply linear_coefficient_zero_of_quadratic_bound
    (inner ℝ u v) (HDP.matrixOpNorm A ^ 2 - ‖v‖ ^ 2) hD
  intro t
  have hbound := matrixOpNorm_apply_le A (ei + t • ej)
  have hboundSq : ‖A.toEuclideanLin (ei + t • ej)‖ ^ 2 ≤
      (HDP.matrixOpNorm A * ‖ei + t • ej‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (HDP.matrixOpNorm_nonneg A) (norm_nonneg _))).2 hbound
  have hAapply : A.toEuclideanLin (ei + t • ej) = u + t • v := by
    simp only [map_add, map_smul]
    rw [show A.toEuclideanLin ei = u by
      simpa only [ei, u] using toEuclideanLin_basisFun A i]
    rw [show A.toEuclideanLin ej = v by
      simpa only [ej, v] using toEuclideanLin_basisFun A j]
  have heinner : inner ℝ ei (t • ej) = 0 := by
    rw [inner_smul_right]
    have hbase : inner ℝ ei ej = 0 := by
      change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) = 0
      rw [EuclideanSpace.basisFun_inner]
      simp [EuclideanSpace.basisFun_apply, Ne.symm hij]
    rw [hbase, mul_zero]
  have hei : ‖ei‖ = 1 := by simp [ei]
  have hej : ‖ej‖ = 1 := by simp [ej]
  have hinput : ‖ei + t • ej‖ ^ 2 = 1 + t ^ 2 := by
    rw [norm_add_sq_real, heinner, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, hei, hej]
    ring
  have houtput : ‖u + t • v‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * t * inner ℝ u v + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  rw [hAapply, houtput, mul_pow, hinput] at hboundSq
  change HDP.matrixOpNorm A = ‖u‖ at hi
  rw [← hi] at hboundSq
  nlinarith

/-- Operator norm versus row/column Euclidean norms, with equality for orthogonal families.

**Book Exercise 4.7.** -/
theorem exercise_4_7b_row_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin m) (hij : j ≠ i)
    (hi : HDP.matrixOpNorm A =
      ‖(WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))‖) :
    inner ℝ
      (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))
      (WithLp.toLp 2 (A.row j) : EuclideanSpace ℝ (Fin n)) = 0 := by
  have hi' : HDP.matrixOpNorm Aᵀ =
      ‖(WithLp.toLp 2 ((Aᵀ).col i) : EuclideanSpace ℝ (Fin n))‖ := by
    simpa using hi
  exact exercise_4_7b_column_orthogonal Aᵀ i j hij hi'

/-- First half of the corresponding exercise: the spectral norm is at most the Frobenius norm.

**Lean implementation helper.** -/
theorem operatorNorm_le_frobeniusNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm A ≤ HDP.matrixFrobeniusNorm A := by
  by_cases hn : n = 0
  · subst n
    have hA : A = 0 := by ext i j; exact Fin.elim0 j
    simp [hA]
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hsq : HDP.matrixOpNorm A ^ 2 ≤ HDP.matrixFrobeniusNorm A ^ 2 := by
      rw [frobeniusNorm_sq_eq_sum_singularValues,
        opNorm_eq_largestSingularValue]
      simpa using Finset.single_le_sum (s := Finset.univ)
        (fun (j : Fin n) _ => sq_nonneg (HDP.matrixSingularValue A j))
        (Finset.mem_univ i)
    nlinarith [HDP.matrixOpNorm_nonneg A, HDP.matrixFrobeniusNorm_nonneg A]

/-- Second half of the corresponding exercise, safely stated with `rank A ≤ r`.

**Lean implementation helper.** -/
theorem frobeniusNorm_le_sqrt_rank_mul_operatorNorm {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hrank : HDP.matrixRank A ≤ r) :
    HDP.matrixFrobeniusNorm A ≤ Real.sqrt r * HDP.matrixOpNorm A := by
  by_cases hr : r = 0
  · have hrank0 : HDP.matrixRank A = 0 := Nat.eq_zero_of_le_zero (hr ▸ hrank)
    have hA : A = 0 := by
      apply (Matrix.toLpLin 2 2).injective
      have hrange : A.toEuclideanLin.range = ⊥ :=
        Submodule.finrank_eq_zero.mp hrank0
      have hlin : A.toEuclideanLin = 0 := LinearMap.range_eq_bot.mp hrange
      simpa using hlin
    simp [hA, hr]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  let S := {i : Fin n // i.val < r}
  let emb : S → Fin r := fun i => ⟨i.val, i.property⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    have hv' : (emb i).val = (emb j).val := congrArg Fin.val hij
    change i.val.val = j.val.val at hv'
    have hfin : i.val = j.val := Fin.ext hv'
    exact Subtype.ext hfin
  have hcard : Fintype.card S ≤ r := by
    simpa [S] using Fintype.card_le_of_injective emb hemb
  have hvanish : ∀ i : {i : Fin n // ¬i.val < r},
      HDP.matrixSingularValue A i.val ^ 2 = 0 := by
    intro i
    have hir : r ≤ i.val.val := Nat.le_of_not_gt i.property
    have hz : HDP.matrixSingularValue A i.val = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr
        (hrank.trans hir)
    rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
  have hsumRestrict :
      (∑ i : Fin n, HDP.matrixSingularValue A i ^ 2) =
      ∑ i : S, HDP.matrixSingularValue A i.val ^ 2 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun i : Fin n => i.val < r)
      (fun i : Fin n => HDP.matrixSingularValue A i ^ 2)
    have hzero : (∑ i : {i : Fin n // ¬i.val < r},
        HDP.matrixSingularValue A i.val ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hvanish i
    rw [hzero, add_zero] at hsplit
    exact hsplit.symm
  have hpoint (i : S) : HDP.matrixSingularValue A i.val ^ 2 ≤
      HDP.matrixOpNorm A ^ 2 := by
    by_cases hn : n = 0
    · subst n
      exact Fin.elim0 i.val
    · letI : Nonempty (Fin n) :=
        Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
      rw [opNorm_eq_largestSingularValue]
      exact (sq_le_sq₀ (HDP.matrixSingularValue_nonneg A i.val)
        (HDP.matrixSingularValue_nonneg A 0)).2
          (HDP.matrixSingularValue_antitone A (Nat.zero_le _))
  have hsumsq : HDP.matrixFrobeniusNorm A ^ 2 ≤
      (r : ℝ) * HDP.matrixOpNorm A ^ 2 := by
    rw [frobeniusNorm_sq_eq_sum_singularValues, hsumRestrict]
    calc
      (∑ i : S, HDP.matrixSingularValue A i.val ^ 2) ≤
          ∑ _i : S, HDP.matrixOpNorm A ^ 2 :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = (Fintype.card S : ℝ) * HDP.matrixOpNorm A ^ 2 := by simp
      _ ≤ (r : ℝ) * HDP.matrixOpNorm A ^ 2 := by gcongr
  have hsqrt : (Real.sqrt r) ^ 2 = (r : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hrhs : 0 ≤ Real.sqrt r * HDP.matrixOpNorm A :=
    mul_nonneg (Real.sqrt_nonneg _) (HDP.matrixOpNorm_nonneg A)
  nlinarith [HDP.matrixFrobeniusNorm_nonneg A]

/-- Rank/Frobenius/operator inequalities and sharpness witnesses.

**Book Exercise 4.4.** -/
theorem exercise_4_4a {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hrank : HDP.matrixRank A ≤ r) :
    HDP.matrixOpNorm A ≤ HDP.matrixFrobeniusNorm A ∧
      HDP.matrixFrobeniusNorm A ≤ Real.sqrt r * HDP.matrixOpNorm A :=
  ⟨operatorNorm_le_frobeniusNorm A,
    frobeniusNorm_le_sqrt_rank_mul_operatorNorm A hrank⟩

/-- Lower-bound sharpness in the corresponding exercise, witnessed by every nonzero rank-one
outer product.

**Book Exercise 4.4.** -/
theorem exercise_4_4a_lower_sharp {m n : ℕ}
    (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    HDP.matrixRank (outerMatrix u v) = 1 ∧
      HDP.matrixOpNorm (outerMatrix u v) =
        HDP.matrixFrobeniusNorm (outerMatrix u v) := by
  constructor
  · exact matrixRank_vecMulVec_eq_one (WithLp.ofLp u) (WithLp.ofLp v)
      (by simpa using hu) (by simpa using hv)
  · exact (exercise_4_3a_outer_norms u v).1.trans
      (exercise_4_3a_outer_norms u v).2.symm

/-- The `r × r` identity matrix has rank `r`.

**Lean implementation helper.** -/
theorem identityMatrix_rank (r : ℕ) :
    HDP.matrixRank (1 : Matrix (Fin r) (Fin r) ℝ) = r := by
  rw [HDP.matrixRank]
  have hone : (1 : Matrix (Fin r) (Fin r) ℝ).toEuclideanLin = LinearMap.id :=
    Matrix.toLpLin_one 2
  rw [hone, LinearMap.range_id, finrank_top, finrank_euclideanSpace_fin]

/-- The Frobenius norm of the `r × r` identity matrix is `√r`.

**Lean implementation helper.** -/
theorem identityMatrix_frobeniusNorm (r : ℕ) :
    HDP.matrixFrobeniusNorm (1 : Matrix (Fin r) (Fin r) ℝ) =
      Real.sqrt r := by
  apply (sq_eq_sq₀ (HDP.matrixFrobeniusNorm_nonneg _)
    (Real.sqrt_nonneg _)).mp
  rw [HDP.matrixFrobeniusNorm_sq, Real.sq_sqrt (by positivity)]
  simp [Matrix.one_apply]

/-- Upper-bound sharpness in the corresponding exercise, witnessed in every positive rank by the
square identity matrix. Together with the rank-one witness this states the valid sharpness
claim; the printed exact-rank lower-equality claim would be false for `r > 1`.

**Book Exercise 4.4.** -/
theorem exercise_4_4a_upper_sharp (r : ℕ) (hr : 0 < r) :
    HDP.matrixRank (1 : Matrix (Fin r) (Fin r) ℝ) = r ∧
      HDP.matrixFrobeniusNorm (1 : Matrix (Fin r) (Fin r) ℝ) =
        Real.sqrt r * HDP.matrixOpNorm (1 : Matrix (Fin r) (Fin r) ℝ) := by
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  constructor
  · exact identityMatrix_rank r
  · rw [identityMatrix_frobeniusNorm]
    have hone : HDP.matrixOpNorm (1 : Matrix (Fin r) (Fin r) ℝ) = 1 := by
      change ‖(1 : Matrix (Fin r) (Fin r) ℝ).toEuclideanLin.toContinuousLinearMap‖ = 1
      rw [Matrix.toLpLin_one 2]
      have hclm : LinearMap.toContinuousLinearMap
          (LinearMap.id : EuclideanSpace ℝ (Fin r) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin r)) = ContinuousLinearMap.id ℝ _ := by
        ext x
        rfl
      rw [hclm, ContinuousLinearMap.norm_id]
    rw [hone, mul_one]

/-- Rank/Frobenius/operator inequalities and sharpness witnesses.

**Book Exercise 4.4.** -/
theorem exercise_4_4b_isotropic
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX : HDP.IsIsotropic X μ)
    (hprod : ∀ j k, MeasureTheory.Integrable
      (fun ω => X ω j * X ω k) μ) :
    (∫ ω, ‖A.toEuclideanLin (X ω)‖ ^ 2 ∂μ) =
      HDP.matrixFrobeniusNorm A ^ 2 := by
  have hexpand (ω : Ω) : ‖A.toEuclideanLin (X ω)‖ ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
        (A i j * A i k) * (X ω j * X ω k) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (∫ ω, ‖A.toEuclideanLin (X ω)‖ ^ 2 ∂μ) =
        ∫ ω, ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
          (A i j * A i k) * (X ω j * X ω k) ∂μ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
        (A i j * A i k) * (∫ ω, X ω j * X ω k ∂μ) := by
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [MeasureTheory.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro k _
            rw [MeasureTheory.integral_const_mul]
          · intro k _
            exact (hprod j k).const_mul (A i j * A i k)
        · intro j _
          exact MeasureTheory.integrable_finsetSum _ fun k _ =>
            (hprod j k).const_mul (A i j * A i k)
      · intro i _
        exact MeasureTheory.integrable_finsetSum _ fun j _ =>
          MeasureTheory.integrable_finsetSum _ fun k _ =>
            (hprod j k).const_mul (A i j * A i k)
    _ = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
        (A i j * A i k) * (if j = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [(HDP.isIsotropic_iff.mp hX) j k]
    _ = HDP.matrixFrobeniusNorm A ^ 2 := by
      rw [HDP.matrixFrobeniusNorm_sq]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-! ### Exercise 4.18(c): exact finite-dimensional `Lp` duality -/

/-- The ordinary finite pairing between two `WithLp` vectors.

**Lean implementation helper.** -/
def finiteLpPairing {ι : Type*} [Fintype ι] {p p' : ℝ≥0∞}
    (x : WithLp p (ι → ℝ)) (z : WithLp p' (ι → ℝ)) : ℝ :=
  ∑ i, WithLp.ofLp x i * WithLp.ofLp z i

/-- Finite Hölder inequality, including the two `1/∞` endpoints.

**Lean implementation helper.** -/
theorem finiteLpPairing_abs_le {ι : Type*} [Fintype ι]
    (p p' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ p')]
    [p.HolderConjugate p']
    (x : WithLp p (ι → ℝ)) (z : WithLp p' (ι → ℝ)) :
    |finiteLpPairing x z| ≤ ‖x‖ * ‖z‖ := by
  by_cases hp : p = ∞
  · have hp' : p' = 1 :=
      (ENNReal.HolderConjugate.eq_top_iff_eq_one p p').mp hp
    subst p
    subst p'
    calc
      |finiteLpPairing x z| ≤ ∑ i, |WithLp.ofLp x i * WithLp.ofLp z i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ‖x‖ * |WithLp.ofLp z i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (abs_nonneg _)
      _ = ‖x‖ * ∑ i, |WithLp.ofLp z i| := by rw [Finset.mul_sum]
      _ = ‖x‖ * ‖z‖ := by
        rw [PiLp.norm_eq_of_L1]
        simp only [Real.norm_eq_abs]
  · by_cases hp' : p' = ∞
    · have hp1 : p = 1 :=
        (ENNReal.HolderConjugate.eq_top_iff_eq_one p' p).mp hp'
      subst p
      subst p'
      calc
        |finiteLpPairing x z| ≤ ∑ i, |WithLp.ofLp x i * WithLp.ofLp z i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |WithLp.ofLp x i| * ‖z‖ := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z i) (abs_nonneg _)
        _ = (∑ i, |WithLp.ofLp x i|) * ‖z‖ := by rw [Finset.sum_mul]
        _ = ‖x‖ * ‖z‖ := by
          rw [PiLp.norm_eq_of_L1]
          simp only [Real.norm_eq_abs]
    · have hpR : 1 < p.toReal := by
        have h := (ENNReal.toReal_lt_toReal (by simp) hp).2
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mp
            (lt_top_iff_ne_top.mpr hp'))
        simpa using h
      have hp'R : 1 < p'.toReal := by
        have h := (ENNReal.toReal_lt_toReal (by simp) hp').2
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp
            (lt_top_iff_ne_top.mpr hp))
        simpa using h
      have hpqR : p.toReal.HolderConjugate p'.toReal :=
        ENNReal.HolderConjugate.toReal hpR
      calc
        |finiteLpPairing x z| ≤ ∑ i, |WithLp.ofLp x i * WithLp.ofLp z i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |WithLp.ofLp x i| * |WithLp.ofLp z i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul]
        _ ≤ (∑ i, |WithLp.ofLp x i| ^ p.toReal) ^ (1 / p.toReal) *
            (∑ i, |WithLp.ofLp z i| ^ p'.toReal) ^ (1 / p'.toReal) := by
          simpa using Real.inner_le_Lp_mul_Lq Finset.univ
            (fun i => |WithLp.ofLp x i|) (fun i => |WithLp.ofLp z i|) hpqR
        _ = ‖x‖ * ‖z‖ := by
          rw [PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp),
            PiLp.norm_eq_sum (p'.toReal_pos_iff_ne_top.mpr hp')]
          simp only [Real.norm_eq_abs]

/-- Identifies real sign mul self with abs.

**Lean implementation helper.** -/
lemma real_sign_mul_self_eq_abs (a : ℝ) : Real.sign a * a = |a| := by
  obtain ha | rfl | ha := lt_trichotomy a 0
  · rw [Real.sign_of_neg ha, abs_of_neg ha]
    ring
  · simp
  · rw [Real.sign_of_pos ha, abs_of_pos ha]
    ring

/-- Bounds abs real sign by one.

**Lean implementation helper.** -/
lemma abs_real_sign_le_one (a : ℝ) : |Real.sign a| ≤ 1 := by
  obtain h | h | h := Real.sign_apply_eq a <;> rw [h] <;> norm_num

/-- Every finite `Lp` vector has a norming vector in the conjugate unit ball. This is proved
uniformly, with separate exact constructions at the two endpoints and `NNReal.isGreatest_Lp` in
the interior.

**Lean implementation helper.** -/
theorem finiteLpPairing_exists_norming {ι : Type*} [Fintype ι]
    (p p' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ p')]
    [p.HolderConjugate p'] (z : WithLp p' (ι → ℝ)) :
    ∃ x : WithLp p (ι → ℝ), ‖x‖ ≤ 1 ∧
      finiteLpPairing x z = ‖z‖ := by
  classical
  by_cases hp : p = ∞
  · have hp' : p' = 1 :=
      (ENNReal.HolderConjugate.eq_top_iff_eq_one p p').mp hp
    subst p
    subst p'
    let x : WithLp ∞ (ι → ℝ) :=
      WithLp.toLp ∞ (fun i => Real.sign (WithLp.ofLp z i))
    refine ⟨x, ?_, ?_⟩
    · rw [show ‖x‖ = ‖fun i => Real.sign (WithLp.ofLp z i)‖ by
        exact PiLp.norm_toLp _]
      exact (pi_norm_le_iff_of_nonneg
        (G := fun _ : ι => ℝ)
        (x := fun i => Real.sign (WithLp.ofLp z i)) zero_le_one).2 fun i => by
          simpa [Real.norm_eq_abs] using
            abs_real_sign_le_one (WithLp.ofLp z i)
    · rw [PiLp.norm_eq_of_L1]
      simp only [Real.norm_eq_abs]
      simp [finiteLpPairing, x, real_sign_mul_self_eq_abs]
  · by_cases hp' : p' = ∞
    · have hp1 : p = 1 :=
        (ENNReal.HolderConjugate.eq_top_iff_eq_one p' p).mp hp'
      subst p
      subst p'
      cases isEmpty_or_nonempty ι with
      | inl hempty =>
          refine ⟨0, by simp, ?_⟩
          have hz : z = 0 := by
            apply WithLp.ofLp_injective
            funext i
            exact isEmptyElim i
          simp [hz, finiteLpPairing]
      | inr hnonempty =>
          letI : Nonempty ι := hnonempty
          obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
            (f := fun i : ι => ‖WithLp.ofLp z i‖₊)
          have hcoordNN : ‖WithLp.ofLp z i‖₊ = ‖z‖₊ :=
            hi.trans (PiLp.nnnorm_eq_ciSup z).symm
          have hcoord : |WithLp.ofLp z i| = ‖z‖ := by
            have hcast := congrArg (fun t : NNReal => (t : ℝ)) hcoordNN
            simpa [Real.norm_eq_abs] using hcast
          let sx : ι → ℝ := Pi.single i (Real.sign (WithLp.ofLp z i))
          let x : WithLp 1 (ι → ℝ) := WithLp.toLp 1 sx
          refine ⟨x, ?_, ?_⟩
          · rw [PiLp.norm_eq_of_L1]
            change (∑ j, |sx j|) ≤ 1
            calc
              (∑ j, |sx j|) = |Real.sign (WithLp.ofLp z i)| := by
                rw [Finset.sum_eq_single i]
                · simp [sx]
                · intro j _ hji
                  simp [sx, hji]
                · simp
              _ ≤ 1 := abs_real_sign_le_one (WithLp.ofLp z i)
          · change (∑ j, sx j * WithLp.ofLp z j) = ‖z‖
            calc
              (∑ j, sx j * WithLp.ofLp z j) =
                  Real.sign (WithLp.ofLp z i) * WithLp.ofLp z i := by
                    simp [sx, Pi.single_apply]
              _ = |WithLp.ofLp z i| := real_sign_mul_self_eq_abs _
              _ = ‖z‖ := hcoord
    · have hpR : 1 < p.toReal := by
        have h := (ENNReal.toReal_lt_toReal (by simp) hp).2
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mp
            (lt_top_iff_ne_top.mpr hp'))
        simpa using h
      have hp'R : 1 < p'.toReal := by
        have h := (ENNReal.toReal_lt_toReal (by simp) hp').2
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp
            (lt_top_iff_ne_top.mpr hp))
        simpa using h
      have hpqR : p.toReal.HolderConjugate p'.toReal :=
        ENNReal.HolderConjugate.toReal hpR
      let f : ι → NNReal := fun i => ⟨|WithLp.ofLp z i|, abs_nonneg _⟩
      obtain ⟨g, hg, hpair⟩ :=
        (NNReal.isGreatest_Lp Finset.univ f hpqR.symm).1
      have hgnorm : (∑ i, (g i : ℝ) ^ p.toReal) ≤ 1 := by
        have hg' : (∑ i ∈ Finset.univ, g i ^ p.toReal) ≤ (1 : NNReal) := hg
        exact_mod_cast hg'
      let x : WithLp p (ι → ℝ) := WithLp.toLp p
        (fun i => Real.sign (WithLp.ofLp z i) * (g i : ℝ))
      refine ⟨x, ?_, ?_⟩
      · rw [PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]
        simp only [x, Real.norm_eq_abs, abs_mul]
        have hsignpow (i : ι) :
            (|Real.sign (WithLp.ofLp z i)| * (g i : ℝ)) ^ p.toReal ≤
              (g i : ℝ) ^ p.toReal := by
          have hg0 : 0 ≤ (g i : ℝ) := (g i).property
          exact Real.rpow_le_rpow
            (mul_nonneg (abs_nonneg _) hg0)
            (mul_le_of_le_one_left hg0 (abs_real_sign_le_one _))
            (zero_le_one.trans hpR.le)
        have hsum :
            (∑ i, (|Real.sign (WithLp.ofLp z i)| * (g i : ℝ)) ^
              p.toReal) ≤ 1 :=
          (Finset.sum_le_sum fun i _ => hsignpow i).trans hgnorm
        simpa only [NNReal.coe_nonneg, abs_of_nonneg] using
          Real.rpow_le_one
            (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
              (mul_nonneg (abs_nonneg _) (g i).coe_nonneg) _)
            hsum (by positivity)
      · have hpairR :
          (∑ i, |WithLp.ofLp z i| * (g i : ℝ)) =
            (∑ i, |WithLp.ofLp z i| ^ p'.toReal) ^
              (1 / p'.toReal) := by
          have hcast := congrArg (fun t : NNReal => (t : ℝ)) hpair
          simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow] at hcast
          have hfcoe (i : ι) : (f i : ℝ) = |WithLp.ofLp z i| := by rfl
          simpa only [hfcoe] using hcast
        rw [PiLp.norm_eq_sum (p'.toReal_pos_iff_ne_top.mpr hp')]
        simp only [finiteLpPairing, x]
        calc
          (∑ i, (Real.sign (WithLp.ofLp z i) * (g i : ℝ)) *
              WithLp.ofLp z i) =
              ∑ i, |WithLp.ofLp z i| * (g i : ℝ) := by
                apply Finset.sum_congr rfl
                intro i _
                calc
                  (Real.sign (WithLp.ofLp z i) * (g i : ℝ)) *
                      WithLp.ofLp z i =
                      (g i : ℝ) *
                        (Real.sign (WithLp.ofLp z i) * WithLp.ofLp z i) := by
                          ring
                  _ = (g i : ℝ) * |WithLp.ofLp z i| := by
                    rw [real_sign_mul_self_eq_abs]
                  _ = |WithLp.ofLp z i| * (g i : ℝ) := mul_comm _ _
          _ = _ := hpairR

/-- Values of the `ℓᵖ` matrix bilinear form on the primal and dual closed
unit balls.

**Lean implementation helper.** -/
def matrixLpBilinearUnitBallValues (p q q' : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : Set ℝ :=
  {z | ∃ x : WithLp p (n → ℝ), ∃ y : WithLp q' (m → ℝ),
    ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      z = |finiteLpPairing y (Matrix.toLpLin p q A x)|}

/-- The general induced `ℓᵖ → ℓᑫ` norm equals the maximum of the associated
bilinear form over the primal `ℓᵖ` and conjugate `ℓ^{q'}` unit balls.

**Book Remark 4.1.9.** -/
theorem matrixLpToLpNorm_bilinear_isGreatest
    (p q q' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [Fact (1 ≤ q')] [q'.HolderConjugate q]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    IsGreatest (matrixLpBilinearUnitBallValues p q q' A)
      (matrixLpToLpNorm p q A) := by
  obtain ⟨x, hx, hAx⟩ := matrixLpToLpNorm_attained p q A
  obtain ⟨y, hy, hpair⟩ := finiteLpPairing_exists_norming q' q
    (Matrix.toLpLin p q A x)
  constructor
  · refine ⟨x, y, hx, hy, ?_⟩
    rw [hpair, abs_of_nonneg (norm_nonneg _), hAx]
  · rintro z ⟨u, v, hu, hv, rfl⟩
    calc
      |finiteLpPairing v (Matrix.toLpLin p q A u)| ≤
          ‖v‖ * ‖Matrix.toLpLin p q A u‖ :=
        finiteLpPairing_abs_le q' q v _
      _ ≤ 1 * (matrixLpToLpNorm p q A * ‖u‖) := by
        exact mul_le_mul hv (matrixLpToLpNorm_apply_le p q A u)
          (norm_nonneg _) zero_le_one
      _ ≤ 1 * (matrixLpToLpNorm p q A * 1) := by
        gcongr
        exact norm_nonneg _
      _ = matrixLpToLpNorm p q A := by ring

/-- Transposing a matrix transfers it across the finite pairing.

**Lean implementation helper.** -/
theorem finiteLpPairing_transpose {m n : ℕ}
    {p q p' q' : ℝ≥0∞}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : WithLp p (Fin m → ℝ)) (y : WithLp q' (Fin n → ℝ)) :
    finiteLpPairing y (Matrix.toLpLin p q Aᵀ x) =
      finiteLpPairing x (Matrix.toLpLin q' p' A y) := by
  simp only [finiteLpPairing, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Bounds matrix lp to `Lᵖ` norm transpose by dual.

**Lean implementation helper.** -/
theorem matrixLpToLpNorm_transpose_le_dual {m n : ℕ}
    (p q p' q' : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    [p.HolderConjugate p'] [q.HolderConjugate q']
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixLpToLpNorm p q Aᵀ ≤ matrixLpToLpNorm q' p' A := by
  letI : p'.HolderConjugate p := ENNReal.HolderConjugate.symm
  letI : q'.HolderConjugate q := ENNReal.HolderConjugate.symm
  rw [matrixLpToLpNorm]
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    exact norm_nonneg (Matrix.toLpLin q' p' A).toContinuousLinearMap)
  intro x
  let z : WithLp q (Fin n → ℝ) := Matrix.toLpLin p q Aᵀ x
  obtain ⟨y, hy, hnorming⟩ := finiteLpPairing_exists_norming q' q z
  have hAy : ‖Matrix.toLpLin q' p' A y‖ ≤ matrixLpToLpNorm q' p' A := by
    exact (matrixLpToLpNorm_apply_le q' p' A y).trans
      (mul_le_of_le_one_right
        (by exact norm_nonneg (Matrix.toLpLin q' p' A).toContinuousLinearMap)
        hy)
  change ‖Matrix.toLpLin p q Aᵀ x‖ ≤ matrixLpToLpNorm q' p' A * ‖x‖
  rw [show Matrix.toLpLin p q Aᵀ x = z by rfl, ← hnorming]
  calc
    finiteLpPairing y z ≤ |finiteLpPairing y z| := le_abs_self _
    _ = |finiteLpPairing x (Matrix.toLpLin q' p' A y)| := by
      rw [show finiteLpPairing y z =
          finiteLpPairing x (Matrix.toLpLin q' p' A y) by
        exact finiteLpPairing_transpose A x y]
    _ ≤ ‖x‖ * ‖Matrix.toLpLin q' p' A y‖ :=
      finiteLpPairing_abs_le p p' x (Matrix.toLpLin q' p' A y)
    _ ≤ ‖x‖ * matrixLpToLpNorm q' p' A :=
      mul_le_mul_of_nonneg_left hAy (norm_nonneg x)
    _ = matrixLpToLpNorm q' p' A * ‖x‖ := mul_comm _ _

/-- General `p -> q` norm equals both a maximum ratio and a bilinear maximum.

**Book (4.31).** -/
theorem exercise_4_18c_duality {m n : ℕ}
    (p q p' q' : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    [p.HolderConjugate p'] [q.HolderConjugate q']
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixLpToLpNorm p q Aᵀ = matrixLpToLpNorm q' p' A := by
  letI : p'.HolderConjugate p := ENNReal.HolderConjugate.symm
  letI : q'.HolderConjugate q := ENNReal.HolderConjugate.symm
  apply le_antisymm
  · exact matrixLpToLpNorm_transpose_le_dual p q p' q' A
  · simpa only [Matrix.transpose_transpose] using
      matrixLpToLpNorm_transpose_le_dual q' p' q p Aᵀ

end HDP.Chapter4

end Source_03_MatrixNorms

/-! ## Material formerly in `04_LowRankApproximation.lean` -/

section Source_04_LowRankApproximation

/-!
# Chapter 4, §4.1.5: low-rank approximation

The rank hypothesis is the rank of the associated Euclidean linear map.  This
is definitionally the usual matrix rank after choosing the standard bases, and
avoids invalid casts between Mathlib's several matrix-rank wrappers.
-/

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter4

set_option linter.unusedSectionVars false

/-- The rank used by the real Chapter 4 matrix API.

**Lean implementation helper.** -/
noncomputable def euclideanMatrixRank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℕ :=
  Module.finrank ℝ A.toEuclideanLin.range

/-- Computes the dimension of ker associated Euclidean linear map.

**Lean implementation helper.** -/
lemma finrank_ker_toEuclideanLin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    euclideanMatrixRank A + Module.finrank ℝ A.toEuclideanLin.ker = n := by
  simpa [euclideanMatrixRank, finrank_euclideanSpace_fin] using
    A.toEuclideanLin.finrank_range_add_finrank_ker

/-- The lower-bound half of the corresponding theorem, with the corrected hypothesis `rank B ≤
k`.

**Lean implementation helper.** -/
theorem eckartYoungMirsky_lower {m n k : ℕ} (hk : k < n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (hBrank : euclideanMatrixRank B ≤ k) :
    HDP.matrixSingularValue A k ≤ HDP.matrixOpNorm (A - B) := by
  let i : Fin n := ⟨k, hk⟩
  let G := matrixGramOperator A
  have hG : IsSelfAdjoint G := matrixGramOperator_isSelfAdjoint A
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  have hker := finrank_ker_toEuclideanLin B
  have hinter : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) <
      Module.finrank ℝ B.toEuclideanLin.ker +
        Module.finrank ℝ (leadingEigenSubspace G hG hn i) := by
    rw [hn, finrank_leadingEigenSubspace G hG hn i]
    change euclideanMatrixRank B + Module.finrank ℝ B.toEuclideanLin.ker = n at hker
    change n < Module.finrank ℝ B.toEuclideanLin.ker + (k + 1)
    omega
  obtain ⟨x, hxker, hxlead, hxnorm⟩ :=
    exists_unit_mem_inf_of_finrank_lt_add B.toEuclideanLin.ker
      (leadingEigenSubspace G hG hn i) hinter
  have hxq := rayleigh_lower_on_leadingEigenSubspace G hG hn i hxlead hxnorm
  have hsing : HDP.matrixSingularValue A k ≤ ‖A.toEuclideanLin x‖ := by
    have hxq' : HDP.matrixSingularValue A k ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 := by
      simpa [G, hn, i, matrixGramOperator_rayleigh,
        matrixGramOperator_eigenvalue_eq_sq_singularValue] using hxq
    nlinarith [HDP.matrixSingularValue_nonneg A k,
      norm_nonneg (A.toEuclideanLin x)]
  have hxB : B.toEuclideanLin x = 0 := hxker
  have hdiff : (A - B).toEuclideanLin x = A.toEuclideanLin x := by
    simp [hxB]
  calc
    HDP.matrixSingularValue A k ≤ ‖A.toEuclideanLin x‖ := hsing
    _ = ‖(A - B).toEuclideanLin x‖ := by rw [hdiff]
    _ ≤ HDP.matrixOpNorm (A - B) * ‖x‖ := matrixOpNorm_apply_le (A - B) x
    _ = HDP.matrixOpNorm (A - B) := by rw [hxnorm, mul_one]

/-- The spectral truncation used for the attainment half of EYM. It is `A` composed with
orthogonal projection onto the first `k` right singular directions.

**Lean implementation helper.** -/
noncomputable def truncatedSVDApproximation {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k < n) :
    Matrix (Fin m) (Fin n) ℝ := by
  let i : Fin n := ⟨k, hk⟩
  let G := matrixGramOperator A
  let hG : IsSelfAdjoint G := matrixGramOperator_isSelfAdjoint A
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let P := (precedingEigenSubspace G hG hn i).starProjection
  exact (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n)).symm
    (A.toEuclideanLin.comp P.toLinearMap)

/-- The truncated SVD operator is `A` composed with orthogonal projection onto the span of its first `k` right singular vectors.

**Lean implementation helper.** -/
lemma toEuclideanLin_truncatedSVDApproximation {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k < n) :
    (truncatedSVDApproximation A hk).toEuclideanLin =
      A.toEuclideanLin.comp
        (precedingEigenSubspace (matrixGramOperator A)
          (matrixGramOperator_isSelfAdjoint A)
          (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨k, hk⟩ : Fin n)).starProjection.toLinearMap := by
  simp [truncatedSVDApproximation]

/-- The rank of the `k`-term truncated SVD approximation is at most `k`.

**Lean implementation helper.** -/
lemma rank_truncatedSVDApproximation_le {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k < n) :
    euclideanMatrixRank (truncatedSVDApproximation A hk) ≤ k := by
  let i : Fin n := ⟨k, hk⟩
  let G := matrixGramOperator A
  let hG : IsSelfAdjoint G := matrixGramOperator_isSelfAdjoint A
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let K := precedingEigenSubspace G hG hn i
  let P := K.starProjection
  change Module.finrank ℝ (truncatedSVDApproximation A hk).toEuclideanLin.range ≤ k
  rw [toEuclideanLin_truncatedSVDApproximation]
  change Module.finrank ℝ (A.toEuclideanLin.comp P.toLinearMap).range ≤ k
  rw [LinearMap.range_comp]
  calc
    Module.finrank ℝ (Submodule.map A.toEuclideanLin P.toLinearMap.range)
        ≤ Module.finrank ℝ P.toLinearMap.range :=
      Submodule.finrank_map_le _ _
    _ = Module.finrank ℝ K := by
      rw [show P.toLinearMap.range = K by simp [P]]
    _ = k := finrank_precedingEigenSubspace G hG hn i

/-- On the trailing right-singular subspace, `A` is Lipschitz with constant the next singular
value.

**Lean implementation helper.** -/
lemma norm_apply_le_singularValue_of_mem_trailing {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k < n)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ trailingEigenSubspace (matrixGramOperator A)
      (matrixGramOperator_isSelfAdjoint A)
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨k, hk⟩ : Fin n)) :
    ‖A.toEuclideanLin x‖ ≤ HDP.matrixSingularValue A k * ‖x‖ := by
  let i : Fin n := ⟨k, hk⟩
  let G := matrixGramOperator A
  have hG : IsSelfAdjoint G := matrixGramOperator_isSelfAdjoint A
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  by_cases hx0 : x = 0
  · simp [hx0]
  · let y := ‖x‖⁻¹ • x
    have hynorm : ‖y‖ = 1 := by simp [y, norm_smul, hx0]
    have hytrail : y ∈ trailingEigenSubspace G hG hn i := by
      exact (trailingEigenSubspace G hG hn i).smul_mem _ hx
    have hyq := rayleigh_upper_on_trailingEigenSubspace G hG hn i hytrail hynorm
    have hySq : ‖A.toEuclideanLin y‖ ^ 2 ≤
        HDP.matrixSingularValue A k ^ 2 := by
      simpa [G, hn, i, matrixGramOperator_rayleigh,
        matrixGramOperator_eigenvalue_eq_sq_singularValue] using hyq
    have hybound : ‖A.toEuclideanLin y‖ ≤ HDP.matrixSingularValue A k := by
      nlinarith [norm_nonneg (A.toEuclideanLin y),
        HDP.matrixSingularValue_nonneg A k]
    have hxdecomp : x = ‖x‖ • y := by simp [y, smul_smul, hx0]
    calc
      ‖A.toEuclideanLin x‖ = ‖A.toEuclideanLin (‖x‖ • y)‖ :=
        congrArg (fun z => ‖A.toEuclideanLin z‖) hxdecomp
      _ = ‖x‖ * ‖A.toEuclideanLin y‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x)]
      _ ≤ ‖x‖ * HDP.matrixSingularValue A k :=
        mul_le_mul_of_nonneg_left hybound (norm_nonneg x)
      _ = HDP.matrixSingularValue A k * ‖x‖ := mul_comm _ _

/-- The operator-norm error of the `k`-term truncated SVD approximation is at most the `k`th singular value.

**Lean implementation helper.** -/
lemma opNorm_sub_truncatedSVDApproximation_le {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k < n) :
    HDP.matrixOpNorm (A - truncatedSVDApproximation A hk) ≤
      HDP.matrixSingularValue A k := by
  let K := precedingEigenSubspace (matrixGramOperator A)
    (matrixGramOperator_isSelfAdjoint A)
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨k, hk⟩ : Fin n)
  let P := K.starProjection
  rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (HDP.matrixSingularValue_nonneg A k) ?_
  intro x
  let z := x - P x
  have hz : z ∈ trailingEigenSubspace (matrixGramOperator A)
      (matrixGramOperator_isSelfAdjoint A)
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨k, hk⟩ : Fin n) := by
    exact K.sub_starProjection_mem_orthogonal x
  have hzbound : ‖A.toEuclideanLin z‖ ≤
      HDP.matrixSingularValue A k * ‖z‖ :=
    norm_apply_le_singularValue_of_mem_trailing A hk hz
  have hznorm : ‖z‖ ≤ ‖x‖ := by
    rw [show z = Kᗮ.starProjection x by simp [z, P]]
    exact Kᗮ.norm_starProjection_apply_le x
  have happ : (A - truncatedSVDApproximation A hk).toEuclideanLin x =
      A.toEuclideanLin z := by
    rw [map_sub]
    change A.toEuclideanLin x -
      (truncatedSVDApproximation A hk).toEuclideanLin x = A.toEuclideanLin z
    rw [toEuclideanLin_truncatedSVDApproximation]
    simp [z, P, K]
  change ‖(A - truncatedSVDApproximation A hk).toEuclideanLin x‖ ≤ _
  rw [happ]
  exact hzbound.trans (mul_le_mul_of_nonneg_left hznorm
    (HDP.matrixSingularValue_nonneg A k))

/-- The corrected optimization class is `rank B ≤ k`; the displayed spectral truncation attains
the minimum.

**Book Theorem 4.1.13.** -/
theorem eckartYoungMirsky {m n k : ℕ} (hk : k < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    euclideanMatrixRank (truncatedSVDApproximation A hk) ≤ k ∧
      HDP.matrixOpNorm (A - truncatedSVDApproximation A hk) =
        HDP.matrixSingularValue A k ∧
      ∀ B : Matrix (Fin m) (Fin n) ℝ, euclideanMatrixRank B ≤ k →
        HDP.matrixSingularValue A k ≤ HDP.matrixOpNorm (A - B) := by
  refine ⟨rank_truncatedSVDApproximation_le A hk, ?_, ?_⟩
  · exact le_antisymm (opNorm_sub_truncatedSVDApproximation_le A hk)
      (eckartYoungMirsky_lower hk A _ (rank_truncatedSVDApproximation_le A hk))
  · intro B hB
    exact eckartYoungMirsky_lower hk A B hB

/-- Canonical source-numbered public name for Theorem 4.1.13. -/
alias theorem_4_1_13 := eckartYoungMirsky

end HDP.Chapter4

end Source_04_LowRankApproximation

/-! ## Material formerly in `05_SpectralPerturbation.lean` -/

section Source_05_SpectralPerturbation

/-!
# Chapter 4, §4.1.6: spectral perturbation

This file proves Weyl's inequalities directly from the arbitrary-subspace
Courant--Fischer interfaces.  It also records the real Hermitian dilation and
the exact projection identities and angle/sign conversion used downstream by
community detection.
-/

open Matrix WithLp Real
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter4

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Bounds abs rayleigh sub by op norm.

**Lean implementation helper.** -/
lemma abs_rayleigh_sub_le_opNorm (A B : E →L[ℝ] E) (x : E)
    (hx : ‖x‖ = 1) :
    |A.reApplyInnerSelf x - B.reApplyInnerSelf x| ≤ ‖A - B‖ := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply,
    ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
    RCLike.re_to_real]
  have hrewrite : inner ℝ (A x) x - inner ℝ (B x) x =
      inner ℝ ((A - B) x) x := by
    simp [inner_sub_left]
  rw [hrewrite]
  calc
    |inner ℝ ((A - B) x) x| ≤ ‖(A - B) x‖ * ‖x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖A - B‖ * ‖x‖) * ‖x‖ := by
      gcongr
      exact (A - B).le_opNorm x
    _ = ‖A - B‖ := by rw [hx]; ring

/-- Weyl perturbation bounds for ordered eigenvalues and singular values.

**Book Lemma 4.1.14.** -/
theorem weylEigenvalue {n : ℕ} (A B : E →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hn : Module.finrank ℝ E = n) (i : Fin n) :
    |hA.isSymmetric.eigenvalues hn i - hB.isSymmetric.eigenvalues hn i| ≤
      ‖A - B‖ := by
  have hone : hA.isSymmetric.eigenvalues hn i -
      hB.isSymmetric.eigenvalues hn i ≤ ‖A - B‖ := by
    let V := leadingEigenSubspace A hA hn i
    obtain ⟨x, hxV, hxnorm, hxB⟩ :=
      every_finrank_succ_subspace_has_rayleigh_le B hB hn i V
        (finrank_leadingEigenSubspace A hA hn i)
    have hxA := rayleigh_lower_on_leadingEigenSubspace A hA hn i hxV hxnorm
    have hdiff := abs_rayleigh_sub_le_opNorm A B x hxnorm
    exact le_trans (sub_le_sub hxA hxB) (le_trans (le_abs_self _) hdiff)
  have htwo : hB.isSymmetric.eigenvalues hn i -
      hA.isSymmetric.eigenvalues hn i ≤ ‖A - B‖ := by
    let V := leadingEigenSubspace B hB hn i
    obtain ⟨x, hxV, hxnorm, hxA⟩ :=
      every_finrank_succ_subspace_has_rayleigh_le A hA hn i V
        (finrank_leadingEigenSubspace B hB hn i)
    have hxB := rayleigh_lower_on_leadingEigenSubspace B hB hn i hxV hxnorm
    have hdiff := abs_rayleigh_sub_le_opNorm B A x hxnorm
    have hnorm : ‖B - A‖ = ‖A - B‖ := by rw [← norm_neg, neg_sub]
    rw [hnorm] at hdiff
    exact le_trans (sub_le_sub hxB hxA) (le_trans (le_abs_self _) hdiff)
  rw [abs_le]
  exact ⟨by linarith, hone⟩

/-- Weyl perturbation bounds for ordered eigenvalues and singular values.

**Book Lemma 4.1.14.** -/
theorem weylSingularValue {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    |HDP.matrixSingularValue A i - HDP.matrixSingularValue B i| ≤
      HDP.matrixOpNorm (A - B) := by
  have oneSide (X Y : Matrix (Fin m) (Fin n) ℝ) :
      HDP.matrixSingularValue X i - HDP.matrixSingularValue Y i ≤
        HDP.matrixOpNorm (X - Y) := by
    rcases (singularValueMinMax X i).1.2 with
      ⟨V, hVdim, hXlower, _xX, _hxXV, _hxXnorm, _hxXattain⟩
    obtain ⟨x, hxV, hxnorm, hxY⟩ :=
      (singularValueMinMax Y i).1.1 V hVdim
    have hxX := hXlower x hxV hxnorm
    have hdiff := matrixOpNorm_apply_le (X - Y) x
    have hsub : ‖X.toEuclideanLin x‖ ≤
        ‖Y.toEuclideanLin x‖ + ‖(X - Y).toEuclideanLin x‖ := by
      have heq : X.toEuclideanLin x =
          Y.toEuclideanLin x + (X - Y).toEuclideanLin x := by
        simp
      rw [heq]
      exact norm_add_le _ _
    calc
      HDP.matrixSingularValue X i - HDP.matrixSingularValue Y i
          ≤ ‖X.toEuclideanLin x‖ - ‖Y.toEuclideanLin x‖ :=
        sub_le_sub hxX hxY
      _ ≤ ‖(X - Y).toEuclideanLin x‖ := by linarith
      _ ≤ HDP.matrixOpNorm (X - Y) := by simpa [hxnorm] using hdiff
  have hone := oneSide A B
  have htwo : HDP.matrixSingularValue B i - HDP.matrixSingularValue A i ≤
      HDP.matrixOpNorm (A - B) := by
    have h := oneSide B A
    have hnorm : HDP.matrixOpNorm (B - A) = HDP.matrixOpNorm (A - B) := by
      rw [show B - A = -(A - B) by abel, HDP.matrixOpNorm_neg]
    rw [hnorm] at h
    exact h
  rw [abs_le]
  exact ⟨by linarith, hone⟩

/-! ### Spectral projections and Davis--Kahan -/

/-- `U` is an `A`-spectral subspace on which `A` has norm at most `r`; `V` is a `B`-spectral
subspace on which `B` expands by at least `r + δ`. The commutation hypothesis is automatic for a
spectral subspace. This is the operator statement proved by displays (4.11)--(4.13), with no
choice of eigenbasis in the public API.

**Book Lemma 4.1.16.** -/
theorem davisKahanSpectralProjections
    (A B : E →L[ℝ] E) (U V : Submodule ℝ E)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hAinvariant : ∀ x : E, x ∈ U → A x ∈ U)
    (hAcontract : ∀ x : E, x ∈ U → ‖A x‖ ≤ r * ‖x‖)
    (hBcomm : ∀ x : E, B (V.starProjection x) = V.starProjection (B x))
    (hBexpand : ∀ x : E, x ∈ V → (r + δ) * ‖x‖ ≤ ‖B x‖) :
    ‖V.starProjection ∘L U.starProjection‖ ≤ ‖B - A‖ / δ := by
  let P := U.starProjection
  let Q := V.starProjection
  let C := Q ∘L P
  let D := B - A
  have hrδ : 0 < r + δ := by linarith
  have hPmem (x : E) : P x ∈ U := by
    change U.starProjection x ∈ U
    exact U.starProjection_apply_mem x
  have hQmem (x : E) : Q x ∈ V := by
    change V.starProjection x ∈ V
    exact V.starProjection_apply_mem x
  have hlower : (r + δ) * ‖C‖ ≤ ‖B ∘L C‖ := by
    have hC : ‖C‖ ≤ ‖B ∘L C‖ / (r + δ) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hrδ.le) ?_
      intro x
      have hxbound : (r + δ) * ‖C x‖ ≤ ‖B ∘L C‖ * ‖x‖ := calc
        (r + δ) * ‖C x‖ ≤ ‖B (C x)‖ :=
          hBexpand (C x) (by simpa [C] using hQmem (P x))
        _ = ‖(B ∘L C) x‖ := rfl
        _ ≤ ‖B ∘L C‖ * ‖x‖ := (B ∘L C).le_opNorm x
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hrδ).2
      simpa [mul_comm] using hxbound
    simpa [mul_comm] using (le_div_iff₀ hrδ).1 hC
  have hupper : ‖B ∘L C‖ ≤ ‖D‖ + r * ‖C‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (add_nonneg (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))) ?_
    intro x
    have hAPmem : A (P x) ∈ U := hAinvariant (P x) (hPmem x)
    have hPAP : P (A (P x)) = A (P x) :=
      U.starProjection_eq_self_iff.mpr hAPmem
    have heq : (B ∘L C) x = Q (D (P x)) + C (A (P x)) := by
      change B (Q (P x)) = Q (D (P x)) + Q (P (A (P x)))
      calc
        B (Q (P x)) = Q (B (P x)) := by
          simpa [Q] using hBcomm (P x)
        _ = Q (D (P x) + A (P x)) := by simp [D]
        _ = Q (D (P x)) + Q (A (P x)) := map_add Q _ _
        _ = Q (D (P x)) + Q (P (A (P x))) := by rw [hPAP]
    rw [heq]
    calc
      ‖Q (D (P x)) + C (A (P x))‖
          ≤ ‖Q (D (P x))‖ + ‖C (A (P x))‖ := norm_add_le _ _
      _ ≤ ‖D‖ * ‖x‖ + r * ‖C‖ * ‖x‖ := by
        have hP := U.norm_starProjection_apply_le x
        have hQ := V.norm_starProjection_apply_le (D (P x))
        have hD := D.le_opNorm (P x)
        have hC := C.le_opNorm (A (P x))
        have hA := hAcontract (P x) (hPmem x)
        calc
          ‖Q (D (P x))‖ + ‖C (A (P x))‖
              ≤ (‖D‖ * ‖P x‖) + ‖C‖ * (r * ‖P x‖) := by
                gcongr
                · exact hQ.trans hD
                · exact hC.trans (mul_le_mul_of_nonneg_left hA (norm_nonneg C))
          _ ≤ ‖D‖ * ‖x‖ + ‖C‖ * (r * ‖x‖) := by
                gcongr
          _ = ‖D‖ * ‖x‖ + r * ‖C‖ * ‖x‖ := by ring
      _ = (‖D‖ + r * ‖C‖) * ‖x‖ := by ring
  have hmain : δ * ‖C‖ ≤ ‖D‖ := by linarith
  change ‖C‖ ≤ ‖D‖ / δ
  apply (le_div_iff₀ hδ).2
  simpa [mul_comm] using hmain

/-- The source's interval/separation formulation is obtained by supplying the two elementary
spectral estimates to the invariant-subspace theorem. This wrapper keeps their quantifier order
explicit for later spectral constructions.

**Book Lemma 4.1.16.** -/
theorem davisKahanSpectralProjections_of_spectral_bounds
    (A B : E →L[ℝ] E) (U V : Submodule ℝ E)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hAU : ∀ x : E, x ∈ U → A x ∈ U ∧ ‖A x‖ ≤ r * ‖x‖)
    (hBV : ∀ x : E, x ∈ V → (r + δ) * ‖x‖ ≤ ‖B x‖)
    (hBVcomm : ∀ x : E, B (V.starProjection x) = V.starProjection (B x)) :
    ‖V.starProjection ∘L U.starProjection‖ ≤ ‖B - A‖ / δ :=
  davisKahanSpectralProjections A B U V hr hδ
    (fun x hx => (hAU x hx).1) (fun x hx => (hAU x hx).2)
    hBVcomm hBV

/-- A self-adjoint operator is uniformly invertible on the span of those eigenvectors whose
eigenvalues stay a fixed distance from a target scalar.

**Lean implementation helper.** -/
lemma norm_sub_smul_ge_on_eigenvector_orthogonal {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {a c : ℝ}
    (hc : 0 ≤ c)
    (hsep : ∀ i : Fin n, i ≠ k →
      c ≤ |hT.isSymmetric.eigenvalues hn i - a|)
    {x : E}
    (hx : inner ℝ (hT.isSymmetric.eigenvectorBasis hn k) x = 0) :
    c * ‖x‖ ≤ ‖T x - a • x‖ := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis hn
  let y : EuclideanSpace ℝ (Fin n) := b.repr x
  have hyk : y k = 0 := by
    simpa [y, b, OrthonormalBasis.repr_apply_apply] using hx
  have hcoord (i : Fin n) :
      b.repr (T x - a • x) i =
        (hT.isSymmetric.eigenvalues hn i - a) * y i := by
    have hi := hT.isSymmetric.eigenvectorBasis_apply_self_apply hn x i
    simp only [map_sub, map_smul]
    change b.repr (T x) i - a * b.repr x i = _
    rw [show b.repr (T x) i =
      hT.isSymmetric.eigenvalues hn i * b.repr x i by simpa [b] using hi]
    simp [y]
    ring
  have hsum : c ^ 2 * (∑ i, y i ^ 2) ≤
      ∑ i, ((hT.isSymmetric.eigenvalues hn i - a) * y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hik : i = k
    · subst i
      simp [hyk]
    · have hi := hsep i hik
      have hsquare : c ^ 2 ≤
          (hT.isSymmetric.eigenvalues hn i - a) ^ 2 := by
        nlinarith [sq_abs (hT.isSymmetric.eigenvalues hn i - a)]
      nlinarith [sq_nonneg (y i),
        sq_nonneg ((hT.isSymmetric.eigenvalues hn i - a) * y i)]
  have hxnorm : ‖x‖ ^ 2 = ∑ i, y i ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖y‖ ^ 2 := by rw [b.repr.norm_map]
      _ = ∑ i, y i ^ 2 := EuclideanSpace.real_norm_sq_eq y
  have houtnorm : ‖T x - a • x‖ ^ 2 =
      ∑ i, ((hT.isSymmetric.eigenvalues hn i - a) * y i) ^ 2 := by
    calc
      ‖T x - a • x‖ ^ 2 = ‖b.repr (T x - a • x)‖ ^ 2 := by
        rw [b.repr.norm_map]
      _ = ∑ i, (b.repr (T x - a • x) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      _ = _ := by simp_rw [hcoord]
  rw [← hxnorm, ← houtnorm] at hsum
  nlinarith [norm_nonneg x, norm_nonneg (T x - a • x)]

/-- A self-adjoint operator commutes with orthogonal projection onto any of its eigenlines.

**Lean implementation helper.** -/
lemma eigenline_orthogonalProjection_commutes {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) (x : E) :
    T ((ℝ ∙ hT.isSymmetric.eigenvectorBasis hn k)ᗮ.starProjection x) =
      (ℝ ∙ hT.isSymmetric.eigenvectorBasis hn k)ᗮ.starProjection (T x) := by
  let v := hT.isSymmetric.eigenvectorBasis hn k
  have hv : ‖v‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one k
  have hTv : T v = hT.isSymmetric.eigenvalues hn k • v :=
    hT.isSymmetric.apply_eigenvectorBasis hn k
  have hinner : inner ℝ v (T x) =
      hT.isSymmetric.eigenvalues hn k * inner ℝ v x := by
    have hs := hT.isSymmetric v x
    change inner ℝ (T v) x = inner ℝ v (T x) at hs
    rw [hTv, inner_smul_left] at hs
    simpa [mul_comm] using hs.symm
  rw [Submodule.starProjection_orthogonal]
  simp only [_root_.sub_apply]
  rw [Submodule.starProjection_unit_singleton ℝ hv,
    Submodule.starProjection_unit_singleton ℝ hv]
  rw [map_sub, map_smul, hTv]
  simp only [smul_smul]
  rw [hinner]
  congr 1
  ring_nf

/-- For unit vectors `u` and `v`, the squared norm of the component of `u` orthogonal to `span(v)` is `1 - |⟨v,u⟩|²`.

**Lean implementation helper.** -/
lemma norm_orthogonalProjection_line_sq {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(ℝ ∙ v)ᗮ.starProjection u‖ ^ 2 = 1 - |inner ℝ v u| ^ 2 := by
  have hp := (ℝ ∙ v).norm_sq_eq_add_norm_sq_starProjection u
  rw [hu, Submodule.starProjection_unit_singleton ℝ hv,
    norm_smul, Real.norm_eq_abs, hv, mul_one] at hp
  nlinarith

/-- The eigenvalues are Mathlib's weakly decreasing eigenvalues, and the sine of the acute angle
is represented safely as `sqrt (1 - |⟪uₖ,vₖ⟫|²)`.

**Book Theorem 4.1.15.** -/
theorem davisKahan {n : ℕ} (A B : E →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin n, i ≠ k →
      δ ≤ |hA.isSymmetric.eigenvalues hn k -
        hA.isSymmetric.eigenvalues hn i|) :
    Real.sqrt (1 - |inner ℝ
      (hA.isSymmetric.eigenvectorBasis hn k)
      (hB.isSymmetric.eigenvectorBasis hn k)| ^ 2) ≤
      2 * ‖A - B‖ / δ := by
  let u := hA.isSymmetric.eigenvectorBasis hn k
  let v := hB.isSymmetric.eigenvectorBasis hn k
  let lam := hA.isSymmetric.eigenvalues hn k
  let ε := ‖A - B‖
  have hu : ‖u‖ = 1 := (hA.isSymmetric.eigenvectorBasis hn).norm_eq_one k
  have hv : ‖v‖ = 1 := (hB.isSymmetric.eigenvectorBasis hn).norm_eq_one k
  have hinner : |inner ℝ u v| ≤ 1 := by
    calc
      |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hu, hv]; ring
  by_cases hlarge : δ / 2 ≤ ε
  · have hsqrt : Real.sqrt (1 - |inner ℝ u v| ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg |inner ℝ u v|]
    change Real.sqrt (1 - |inner ℝ u v| ^ 2) ≤ 2 * ε / δ
    have hone : 1 ≤ 2 * ε / δ := by
      apply (le_div_iff₀ hδ).2
      nlinarith
    exact hsqrt.trans hone
  · have hsmall : ε < δ / 2 := lt_of_not_ge hlarge
    let Ashift : E →L[ℝ] E := A - lam • 1
    let Bshift : E →L[ℝ] E := B - lam • 1
    let U : Submodule ℝ E := ℝ ∙ u
    let V : Submodule ℝ E := (ℝ ∙ v)ᗮ
    have hAu : A u = lam • u := hA.isSymmetric.apply_eigenvectorBasis hn k
    have hsepB : ∀ i : Fin n, i ≠ k →
        δ / 2 ≤ |hB.isSymmetric.eigenvalues hn i - lam| := by
      intro i hik
      have hweyl := weylEigenvalue A B hA hB hn i
      have htri : |lam - hA.isSymmetric.eigenvalues hn i| ≤
          |lam - hB.isSymmetric.eigenvalues hn i| +
            |hB.isSymmetric.eigenvalues hn i -
              hA.isSymmetric.eigenvalues hn i| := by
        calc
          |lam - hA.isSymmetric.eigenvalues hn i| =
              |(lam - hB.isSymmetric.eigenvalues hn i) +
                (hB.isSymmetric.eigenvalues hn i -
                  hA.isSymmetric.eigenvalues hn i)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have hgap_i := hgap i hik
      have hrev : |hB.isSymmetric.eigenvalues hn i -
          hA.isSymmetric.eigenvalues hn i| ≤ ε := by
        calc
          |hB.isSymmetric.eigenvalues hn i -
              hA.isSymmetric.eigenvalues hn i| =
              |hA.isSymmetric.eigenvalues hn i -
                hB.isSymmetric.eigenvalues hn i| := abs_sub_comm _ _
          _ ≤ ‖A - B‖ := hweyl
          _ = ε := rfl
      have habs : |lam - hB.isSymmetric.eigenvalues hn i| =
          |hB.isSymmetric.eigenvalues hn i - lam| := abs_sub_comm _ _
      rw [habs] at htri
      linarith
    have hAinv : ∀ x : E, x ∈ U → Ashift x ∈ U := by
      intro x hx
      change x ∈ ℝ ∙ u at hx
      rw [Submodule.mem_span_singleton] at hx
      rcases hx with ⟨c, rfl⟩
      change Ashift (c • u) ∈ ℝ ∙ u
      simp [Ashift, hAu]
    have hAcontract : ∀ x : E, x ∈ U → ‖Ashift x‖ ≤ 0 * ‖x‖ := by
      intro x hx
      change x ∈ ℝ ∙ u at hx
      rw [Submodule.mem_span_singleton] at hx
      rcases hx with ⟨c, rfl⟩
      simp [Ashift, hAu]
    have hBcomm : ∀ x : E,
        Bshift (V.starProjection x) = V.starProjection (Bshift x) := by
      intro x
      have hcomm := eigenline_orthogonalProjection_commutes B hB hn k x
      change (B - lam • 1) ((ℝ ∙ v)ᗮ.starProjection x) =
        (ℝ ∙ v)ᗮ.starProjection ((B - lam • 1) x)
      simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self]
      rw [map_sub, map_smul, hcomm]
    have hBexpand : ∀ x : E, x ∈ V →
        (0 + δ / 2) * ‖x‖ ≤ ‖Bshift x‖ := by
      intro x hx
      have hxorth : inner ℝ v x = 0 := by
        change x ∈ (ℝ ∙ v)ᗮ at hx
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hx
        exact (real_inner_comm x v).trans hx
      have h := norm_sub_smul_ge_on_eigenvector_orthogonal B hB hn k
        (c := δ / 2) (a := lam) (by linarith) hsepB hxorth
      simpa [Bshift] using h
    have hproj := davisKahanSpectralProjections Ashift Bshift U V
      (r := 0) (δ := δ / 2) (by norm_num) (by linarith)
      hAinv hAcontract hBcomm hBexpand
    have hdiff : Bshift - Ashift = B - A := by
      ext x
      simp [Ashift, Bshift]
    rw [hdiff] at hproj
    have hproj' : ‖V.starProjection ∘L U.starProjection‖ ≤ 2 * ε / δ := by
      change ‖V.starProjection ∘L U.starProjection‖ ≤ 2 * ‖A - B‖ / δ
      rw [show ‖B - A‖ = ‖A - B‖ by rw [← norm_neg, neg_sub]] at hproj
      calc
        ‖V.starProjection ∘L U.starProjection‖ ≤ ‖A - B‖ / (δ / 2) := hproj
        _ = 2 * ‖A - B‖ / δ := by field_simp
    have hPu : U.starProjection u = u := by
      apply U.starProjection_eq_self_iff.mpr
      simp [U]
    have heval := (V.starProjection ∘L U.starProjection).le_opNorm u
    rw [ContinuousLinearMap.comp_apply, hPu, hu, mul_one] at heval
    have hQsq : ‖V.starProjection u‖ ^ 2 =
        1 - |inner ℝ u v| ^ 2 := by
      have hq := norm_orthogonalProjection_line_sq hu hv
      change ‖(ℝ ∙ v)ᗮ.starProjection u‖ ^ 2 = 1 - |inner ℝ u v| ^ 2
      rw [show |inner ℝ u v| = |inner ℝ v u| by
        rw [real_inner_comm u v]]
      exact hq
    change Real.sqrt (1 - |inner ℝ u v| ^ 2) ≤ 2 * ε / δ
    rw [← hQsq, Real.sqrt_sq (norm_nonneg _)]
    exact heval.trans hproj'

/-! ### Exercise 4.12: differences of orthogonal projections -/

/-- Norm of a difference of orthogonal projections.

**Book Exercise 4.12.** -/
theorem exercise_4_12a_projection_difference (U V : Submodule ℝ E) :
    ‖U.starProjection - V.starProjection‖ =
      max ‖Uᗮ.starProjection ∘L V.starProjection‖
        ‖U.starProjection ∘L Vᗮ.starProjection‖ := by
  let P := U.starProjection
  let Q := V.starProjection
  let Pperp := Uᗮ.starProjection
  let Qperp := Vᗮ.starProjection
  let C1 := Pperp ∘L Q
  let C2 := P ∘L Qperp
  let M := max ‖C1‖ ‖C2‖
  have hPid (x : E) : P (P x) = P x :=
    U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hQid (x : E) : Q (Q x) = Q x :=
    V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  have hPpid (x : E) : Pperp (Pperp x) = Pperp x :=
    Uᗮ.starProjection_eq_self_iff.mpr (Uᗮ.starProjection_apply_mem x)
  have hQpid (x : E) : Qperp (Qperp x) = Qperp x :=
    Vᗮ.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem x)
  have hdecomp (x : E) : (P - Q) x = C2 x - C1 x := by
    change P x - Q x = P (Qperp x) - Pperp (Q x)
    have hp : Pperp = ContinuousLinearMap.id ℝ E - P := by simpa [Pperp, P] using
      (Submodule.starProjection_orthogonal (U := U))
    have hq : Qperp = ContinuousLinearMap.id ℝ E - Q := by simpa [Qperp, Q] using
      (Submodule.starProjection_orthogonal (U := V))
    rw [hp, hq]
    simp only [_root_.sub_apply, map_sub]
    abel
  have horth (x : E) : inner ℝ (C2 x) (C1 x) = 0 := by
    exact Submodule.inner_right_of_mem_orthogonal (K := U)
      (by
        change U.starProjection (Qperp x) ∈ U
        exact U.starProjection_apply_mem (Qperp x))
      (by
        change Uᗮ.starProjection (Q x) ∈ Uᗮ
        exact Uᗮ.starProjection_apply_mem (Q x))
  have hupper : ‖P - Q‖ ≤ M := by
    have hM : 0 ≤ M := (norm_nonneg C1).trans (le_max_left _ _)
    refine ContinuousLinearMap.opNorm_le_bound _
      hM ?_
    intro x
    have hC1same : C1 (Q x) = C1 x := by
      change Pperp (Q (Q x)) = Pperp (Q x)
      rw [hQid]
    have hC2same : C2 (Qperp x) = C2 x := by
      change P (Qperp (Qperp x)) = P (Qperp x)
      rw [hQpid]
    have hC1bound : ‖C1 x‖ ≤ M * ‖Q x‖ := by
      rw [← hC1same]
      exact (C1.le_opNorm (Q x)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hC2bound : ‖C2 x‖ ≤ M * ‖Qperp x‖ := by
      rw [← hC2same]
      exact (C2.le_opNorm (Qperp x)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hpyth := V.norm_sq_eq_add_norm_sq_starProjection x
    change ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖Qperp x‖ ^ 2 at hpyth
    have hC1sq : ‖C1 x‖ ^ 2 ≤ (M * ‖Q x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).2 hC1bound
    have hC2sq : ‖C2 x‖ ^ 2 ≤ (M * ‖Qperp x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).2 hC2bound
    rw [hdecomp]
    have hsq : ‖C2 x - C1 x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
      calc
        ‖C2 x - C1 x‖ ^ 2 = ‖C2 x‖ ^ 2 + ‖C1 x‖ ^ 2 := by
          rw [norm_sub_sq_real, horth]
          ring
        _ ≤ (M * ‖Qperp x‖) ^ 2 + (M * ‖Q x‖) ^ 2 :=
          add_le_add hC2sq hC1sq
        _ = M ^ 2 * (‖Qperp x‖ ^ 2 + ‖Q x‖ ^ 2) := by ring
        _ = M ^ 2 * ‖x‖ ^ 2 := by
          congr 1
          linarith
        _ = (M * ‖x‖) ^ 2 := by ring
    nlinarith [norm_nonneg (C2 x - C1 x),
      mul_nonneg hM (norm_nonneg x)]
  have hC1op : ‖C1‖ ≤ ‖P - Q‖ := by
    have heq : C1 = Pperp ∘L (Q - P) := by
      ext x
      change Pperp (Q x) = Pperp (Q x - P x)
      rw [map_sub]
      have hz : Pperp (P x) = 0 := by
        have hp : Pperp = ContinuousLinearMap.id ℝ E - P := by simpa [Pperp, P] using
          (Submodule.starProjection_orthogonal (U := U))
        rw [hp]
        simp [P, hPid]
      rw [hz, sub_zero]
    rw [heq]
    calc
      ‖Pperp ∘L (Q - P)‖ ≤ ‖Pperp‖ * ‖Q - P‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖Q - P‖ := by
        gcongr
        exact Uᗮ.starProjection_norm_le
      _ = ‖P - Q‖ := by rw [one_mul, ← norm_neg, neg_sub]
  have hC2op : ‖C2‖ ≤ ‖P - Q‖ := by
    have heq : C2 = P ∘L (P - Q) := by
      ext x
      change P (Qperp x) = P (P x - Q x)
      have hq : Qperp = ContinuousLinearMap.id ℝ E - Q := by simpa [Qperp, Q] using
        (Submodule.starProjection_orthogonal (U := V))
      rw [hq]
      simp [hPid, map_sub]
    rw [heq]
    calc
      ‖P ∘L (P - Q)‖ ≤ ‖P‖ * ‖P - Q‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖P - Q‖ := by
        gcongr
        exact U.starProjection_norm_le
      _ = ‖P - Q‖ := one_mul _
  apply le_antisymm hupper
  exact max_le hC1op hC2op

/-- Bounds norm sub star projections by one.

**Lean implementation helper.** -/
lemma norm_sub_starProjections_le_one (U V : Submodule ℝ E) :
    ‖U.starProjection - V.starProjection‖ ≤ 1 := by
  rw [exercise_4_12a_projection_difference]
  apply max_le
  · calc
      ‖Uᗮ.starProjection ∘L V.starProjection‖ ≤
          ‖Uᗮ.starProjection‖ * ‖V.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul Uᗮ.starProjection_norm_le
        V.starProjection_norm_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · calc
      ‖U.starProjection ∘L Vᗮ.starProjection‖ ≤
          ‖U.starProjection‖ * ‖Vᗮ.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul U.starProjection_norm_le
        Vᗮ.starProjection_norm_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Norm of a difference of orthogonal projections.

**Book Exercise 4.12.** -/
theorem exercise_4_12b_projection_difference_of_finrank_ne
    (U V : Submodule ℝ E)
    (hUV : Module.finrank ℝ U ≠ Module.finrank ℝ V) :
    ‖U.starProjection - V.starProjection‖ = 1 := by
  apply le_antisymm (norm_sub_starProjections_le_one U V)
  rcases lt_or_gt_of_ne hUV with hlt | hgt
  · have hdim := U.finrank_add_finrank_orthogonal
    have hinter : Module.finrank ℝ E <
        Module.finrank ℝ V + Module.finrank ℝ Uᗮ := by omega
    obtain ⟨x, hxV, hxUorth, hxnorm⟩ :=
      exists_unit_mem_inf_of_finrank_lt_add V Uᗮ hinter
    have hPx : U.starProjection x = 0 := by
      have : x ∈ U.starProjection.ker := by
        rw [U.ker_starProjection]
        exact hxUorth
      exact this
    have hQx : V.starProjection x = x :=
      V.starProjection_eq_self_iff.mpr hxV
    have hop := (U.starProjection - V.starProjection).le_opNorm x
    rw [_root_.sub_apply, hPx, hQx, zero_sub, norm_neg, hxnorm, mul_one] at hop
    exact hop
  · have hdim := V.finrank_add_finrank_orthogonal
    have hinter : Module.finrank ℝ E <
        Module.finrank ℝ U + Module.finrank ℝ Vᗮ := by omega
    obtain ⟨x, hxU, hxVorth, hxnorm⟩ :=
      exists_unit_mem_inf_of_finrank_lt_add U Vᗮ hinter
    have hPx : U.starProjection x = x :=
      U.starProjection_eq_self_iff.mpr hxU
    have hQx : V.starProjection x = 0 := by
      have : x ∈ V.starProjection.ker := by
        rw [V.ker_starProjection]
        exact hxVorth
      exact this
    have hop := (U.starProjection - V.starProjection).le_opNorm x
    rw [_root_.sub_apply, hPx, hQx, sub_zero, hxnorm, mul_one] at hop
    exact hop

/-- The geometric core of the corresponding exercise. If the largest distance from `V` to `U` is
strictly less than one, projection from `V` onto `U` is invertible; orthogonality then bounds
the distance in the reverse direction.

**Lean implementation helper.** -/
lemma projection_cross_norm_le_of_lt_one
    (U V : Submodule ℝ E)
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V)
    (hlt : ‖Uᗮ.starProjection ∘L V.starProjection‖ < 1) :
    ‖U.starProjection ∘L Vᗮ.starProjection‖ ≤
      ‖Uᗮ.starProjection ∘L V.starProjection‖ := by
  let P := U.starProjection
  let Pperp := Uᗮ.starProjection
  let Q := V.starProjection
  let Qperp := Vᗮ.starProjection
  let C := Pperp ∘L Q
  let c := ‖C‖
  let T : V →L[ℝ] U :=
    (P.domRestrict V).codRestrict U (fun x => U.starProjection_apply_mem x)
  have hc0 : 0 ≤ c := norm_nonneg _
  have hc1 : c < 1 := by simpa [c, C] using hlt
  have hTinj : Function.Injective T := by
    change Function.Injective T.toLinearMap
    rw [← LinearMap.ker_eq_bot]
    ext z
    constructor
    · intro hz
      have hPz : P (z : E) = 0 := congrArg Subtype.val hz
      have hQz : Q (z : E) = z :=
        V.starProjection_eq_self_iff.mpr z.property
      have hPperpz : Pperp (z : E) = z := by
        have hp : Pperp = ContinuousLinearMap.id ℝ E - P := by
          simpa [Pperp, P] using (Submodule.starProjection_orthogonal (U := U))
        rw [hp]
        simp [hPz]
      have hCz : C (z : E) = z := by
        change Pperp (Q (z : E)) = z
        rw [hQz, hPperpz]
      have hop := C.le_opNorm (z : E)
      rw [hCz] at hop
      by_contra hz0
      have hzval : (z : E) ≠ 0 := by
        intro hzval
        apply hz0
        simpa only [Submodule.mem_bot] using (Subtype.ext hzval)
      have hznorm : 0 < ‖(z : E)‖ := norm_pos_iff.mpr hzval
      have : 1 ≤ c := by
        apply (le_of_mul_le_mul_right ?_ hznorm)
        simpa [c] using hop
      linarith
    · intro hz
      have hz' : z = 0 := by simpa only [Submodule.mem_bot] using hz
      subst z
      simp
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank.symm).mp hTinj
  have hbound : ∀ z : E, z ∈ Vᗮ → ‖P z‖ ≤ c * ‖z‖ := by
    intro z hzV
    obtain ⟨v, hv⟩ := hTsurj ⟨P z, U.starProjection_apply_mem z⟩
    have hPv : P (v : E) = P z := congrArg Subtype.val hv
    have hQv : Q (v : E) = v := V.starProjection_eq_self_iff.mpr v.property
    have hQz : Q z = 0 := by
      have hzker : z ∈ V.starProjection.ker := by
        rw [V.ker_starProjection]
        exact hzV
      exact hzker
    have horth : inner ℝ z (v : E) = 0 := by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal v.property hzV
    have hp : Pperp = ContinuousLinearMap.id ℝ E - P := by
      simpa [Pperp, P] using (Submodule.starProjection_orthogonal (U := U))
    have hzdec : z = P z + Pperp z := by rw [hp]; simp
    have hvdec : (v : E) = P (v : E) + Pperp (v : E) := by rw [hp]; simp
    have hzCross : inner ℝ (P z) (Pperp (v : E)) = 0 := by
      exact Submodule.inner_right_of_mem_orthogonal
        (U.starProjection_apply_mem z) (Uᗮ.starProjection_apply_mem (v : E))
    have hvCross : inner ℝ (Pperp z) (P (v : E)) = 0 := by
      exact Submodule.inner_left_of_mem_orthogonal
        (U.starProjection_apply_mem (v : E)) (Uᗮ.starProjection_apply_mem z)
    have hdecomp_inner :
        inner ℝ (P z) (P z) + inner ℝ (Pperp z) (Pperp (v : E)) = 0 := by
      rw [hzdec, hvdec, inner_add_left, inner_add_right,
        inner_add_right, hzCross, hvCross, add_zero, zero_add] at horth
      simpa [hPv] using horth
    have hCbound : ‖Pperp (v : E)‖ ≤ c * ‖(v : E)‖ := by
      have hop := C.le_opNorm (v : E)
      change ‖Pperp (Q (v : E))‖ ≤ ‖C‖ * ‖(v : E)‖ at hop
      simpa [hQv, c] using hop
    have hzpyth := U.norm_sq_eq_add_norm_sq_starProjection z
    have hvpyth := U.norm_sq_eq_add_norm_sq_starProjection (v : E)
    change ‖z‖ ^ 2 = ‖P z‖ ^ 2 + ‖Pperp z‖ ^ 2 at hzpyth
    change ‖(v : E)‖ ^ 2 =
      ‖P (v : E)‖ ^ 2 + ‖Pperp (v : E)‖ ^ 2 at hvpyth
    rw [hPv] at hvpyth
    have hinner_abs : ‖P z‖ ^ 2 ≤ ‖Pperp z‖ * ‖Pperp (v : E)‖ := by
      have habs := abs_real_inner_le_norm (Pperp z) (Pperp (v : E))
      have hneg : inner ℝ (Pperp z) (Pperp (v : E)) =
          -inner ℝ (P z) (P z) := by linarith
      calc
        ‖P z‖ ^ 2 = |inner ℝ (P z) (P z)| := by
          rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖P z‖)]
        _ = |inner ℝ (Pperp z) (Pperp (v : E))| := by rw [hneg, abs_neg]
        _ ≤ ‖Pperp z‖ * ‖Pperp (v : E)‖ := habs
    have hinner_sq : ‖P z‖ ^ 4 ≤
        ‖Pperp z‖ ^ 2 * ‖Pperp (v : E)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Pperp z‖ * ‖Pperp (v : E)‖ - ‖P z‖ ^ 2)]
    have hCsq : ‖Pperp (v : E)‖ ^ 2 ≤ c ^ 2 * ‖(v : E)‖ ^ 2 := by
      nlinarith [norm_nonneg (Pperp (v : E)),
        mul_nonneg hc0 (norm_nonneg (v : E))]
    have hcoef : 0 < 1 - c ^ 2 := by nlinarith
    have hvrel : (1 - c ^ 2) * ‖(v : E)‖ ^ 2 ≤ ‖P z‖ ^ 2 := by
      nlinarith
    have hvperprel :
        (1 - c ^ 2) * ‖Pperp (v : E)‖ ^ 2 ≤ c ^ 2 * ‖P z‖ ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg ‖P z‖)]
    have hmult1 := mul_le_mul_of_nonneg_left hinner_sq hcoef.le
    have hmult2 := mul_le_mul_of_nonneg_left hvperprel (sq_nonneg ‖Pperp z‖)
    have hmain : ‖P z‖ ^ 2 ≤ c ^ 2 * ‖z‖ ^ 2 := by
      by_cases hPzero : ‖P z‖ = 0
      · simp [hPzero, mul_nonneg (sq_nonneg c) (sq_nonneg ‖z‖)]
      · have hPnormpos : 0 < ‖P z‖ :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm hPzero)
        have hPpos : 0 < ‖P z‖ ^ 2 := sq_pos_of_pos hPnormpos
        nlinarith
    nlinarith [norm_nonneg (P z), mul_nonneg hc0 (norm_nonneg z)]
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 ?_
  intro x
  have hxmem : Qperp x ∈ Vᗮ := Vᗮ.starProjection_apply_mem x
  have hx := hbound (Qperp x) hxmem
  change ‖P (Qperp x)‖ ≤ c * ‖x‖
  exact hx.trans (mul_le_mul_of_nonneg_left (Vᗮ.norm_starProjection_apply_le x) hc0)

/-- The norm of a product of two orthogonal projections is invariant under reversing the order,
since the two products are adjoints.

**Lean implementation helper.** -/
lemma norm_starProjection_comp_comm (U V : Submodule ℝ E) :
    ‖U.starProjection ∘L V.starProjection‖ =
      ‖V.starProjection ∘L U.starProjection‖ := by
  calc
    ‖U.starProjection ∘L V.starProjection‖ =
        ‖ContinuousLinearMap.adjoint
          (V.starProjection ∘L U.starProjection)‖ := by
      have hU : IsSelfAdjoint U.starProjection := by simp
      have hV : IsSelfAdjoint V.starProjection := by simp
      rw [ContinuousLinearMap.adjoint_comp, hU.adjoint_eq, hV.adjoint_eq]
    _ = ‖V.starProjection ∘L U.starProjection‖ :=
      ContinuousLinearMap.adjoint.norm_map _

/-- Norm of a difference of orthogonal projections.

**Book Exercise 4.12.** -/
theorem exercise_4_12c_projection_difference_of_finrank_eq
    (U V : Submodule ℝ E)
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V) :
    ‖U.starProjection - V.starProjection‖ =
        ‖Uᗮ.starProjection ∘L V.starProjection‖ ∧
      ‖Uᗮ.starProjection ∘L V.starProjection‖ =
        ‖U.starProjection ∘L Vᗮ.starProjection‖ := by
  let a := ‖Uᗮ.starProjection ∘L V.starProjection‖
  let b := ‖U.starProjection ∘L Vᗮ.starProjection‖
  have ha1 : a ≤ 1 := by
    calc
      a ≤ ‖Uᗮ.starProjection‖ * ‖V.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul Uᗮ.starProjection_norm_le
        V.starProjection_norm_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hb1 : b ≤ 1 := by
    calc
      b ≤ ‖U.starProjection‖ * ‖Vᗮ.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul U.starProjection_norm_le
        Vᗮ.starProjection_norm_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hab : b ≤ a := by
    by_cases ha : a < 1
    · exact projection_cross_norm_le_of_lt_one U V hrank (by simpa [a] using ha)
    · have : a = 1 := le_antisymm ha1 (le_of_not_gt ha)
      simpa [this] using hb1
  have hba : a ≤ b := by
    by_cases hb : b < 1
    · have hswap := projection_cross_norm_le_of_lt_one V U hrank.symm
        (by
          have : ‖Vᗮ.starProjection ∘L U.starProjection‖ = b := by
            calc
              ‖Vᗮ.starProjection ∘L U.starProjection‖ =
                  ‖U.starProjection ∘L Vᗮ.starProjection‖ :=
                norm_starProjection_comp_comm Vᗮ U
              _ = b := rfl
          simpa [this] using hb)
      have hleft : ‖V.starProjection ∘L Uᗮ.starProjection‖ = a := by
        calc
          ‖V.starProjection ∘L Uᗮ.starProjection‖ =
              ‖Uᗮ.starProjection ∘L V.starProjection‖ :=
            norm_starProjection_comp_comm V Uᗮ
          _ = a := rfl
      have hright : ‖Vᗮ.starProjection ∘L U.starProjection‖ = b := by
        calc
          ‖Vᗮ.starProjection ∘L U.starProjection‖ =
              ‖U.starProjection ∘L Vᗮ.starProjection‖ :=
            norm_starProjection_comp_comm Vᗮ U
          _ = b := rfl
      simpa [hleft, hright] using hswap
    · have : b = 1 := le_antisymm hb1 (le_of_not_gt hb)
      simpa [this] using ha1
  have habEq : a = b := le_antisymm hba hab
  constructor
  · rw [exercise_4_12a_projection_difference]
    simp [a, b, habEq]
  · exact habEq

/-! ### Exercise 4.13: Davis--Kahan for leading spectral projections -/

/-- Shows that following eigen subspace is invariant under the indicated operator.

**Lean implementation helper.** -/
lemma followingEigenSubspace_invariant {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {x : E}
    (hx : x ∈ followingEigenSubspace T hT hn k) :
    T x ∈ followingEigenSubspace T hT hn k := by
  classical
  unfold followingEigenSubspace at hx ⊢
  refine Submodule.span_induction (p := fun x _ => T x ∈ Submodule.span ℝ
      (Set.range fun i : Fin (n - (k.val + 1)) =>
        hT.isSymmetric.eigenvectorBasis hn
          ⟨k.val + 1 + i.val, by omega⟩)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    let j : Fin n := ⟨k.val + 1 + i.val, by omega⟩
    have heig : T (hT.isSymmetric.eigenvectorBasis hn j) =
        hT.isSymmetric.eigenvalues hn j •
          hT.isSymmetric.eigenvectorBasis hn j := by
      exact hT.isSymmetric.apply_eigenvectorBasis hn j
    change T (hT.isSymmetric.eigenvectorBasis hn j) ∈ _
    rw [heig]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ a hx

/-- Shows that leading eigen subspace is invariant under the indicated operator.

**Lean implementation helper.** -/
lemma leadingEigenSubspace_invariant {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {x : E}
    (hx : x ∈ leadingEigenSubspace T hT hn k) :
    T x ∈ leadingEigenSubspace T hT hn k := by
  rw [leadingEigenSubspace, Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  have hTy := followingEigenSubspace_invariant T hT hn k hy
  have hs := hT.isSymmetric y x
  change inner ℝ (T y) x = inner ℝ y (T x) at hs
  rw [real_inner_comm, ← hs, real_inner_comm]
  exact hx (T y) hTy

/-- Derives self adjoint commutes star projection from invariant.

**Lean implementation helper.** -/
lemma selfAdjoint_commutes_starProjection_of_invariant
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (U : Submodule ℝ E)
    (hU : ∀ x : E, x ∈ U → T x ∈ U) (x : E) :
    T (U.starProjection x) = U.starProjection (T x) := by
  let P := U.starProjection
  let Pperp := Uᗮ.starProjection
  have hTP : T (P x) ∈ U := hU _ (U.starProjection_apply_mem x)
  have hTperp : T (Pperp x) ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hTu := hU u hu
    have hs := hT.isSymmetric u (Pperp x)
    change inner ℝ (T u) (Pperp x) = inner ℝ u (T (Pperp x)) at hs
    rw [real_inner_comm, ← hs]
    exact Submodule.inner_right_of_mem_orthogonal hTu
      (Uᗮ.starProjection_apply_mem x)
  have hdecomp : x = P x + Pperp x := by
    have hp : Pperp = ContinuousLinearMap.id ℝ E - P := by
      simpa [Pperp, P] using (Submodule.starProjection_orthogonal (U := U))
    rw [hp]
    simp
  calc
    T (P x) = P (T (P x)) :=
      (U.starProjection_eq_self_iff.mpr hTP).symm
    _ = P (T (P x) + T (Pperp x)) := by
      have hz : P (T (Pperp x)) = 0 := by
        have hker : T (Pperp x) ∈ P.ker := by
          rw [U.ker_starProjection]
          exact hTperp
        exact hker
      rw [map_add, hz, add_zero]
    _ = P (T x) := by rw [← map_add, ← hdecomp]

/-- Every vector in the eigenspace following index `k` is orthogonal to eigenvectors with index at most `k`.

**Lean implementation helper.** -/
lemma mem_followingEigenSubspace_orthogonal_leading {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {x : E}
    (hx : x ∈ followingEigenSubspace T hT hn k) :
    ∀ i : Fin n, i ≤ k →
      inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0 := by
  classical
  intro i hik
  unfold followingEigenSubspace at hx
  refine Submodule.span_induction (p := fun x _ =>
      inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with ⟨j, rfl⟩
    have hne : i ≠ (⟨k.val + 1 + j.val, by omega⟩ : Fin n) := by
      intro heq
      have hval := congrArg Fin.val heq
      have hik' : i.val ≤ k.val := hik
      change i.val = k.val + 1 + j.val at hval
      omega
    simp [hne]
  · simp
  · intro x y _ _ hx hy
    simp [inner_add_right, hx, hy]
  · intro a x _ hx
    simp [inner_smul_right, hx]

/-- If `|a - λᵢ| ≤ r` through index `k`, then `‖(aI - T)x‖ ≤ r‖x‖` for every `x` in the leading eigenspace.

**Lean implementation helper.** -/
lemma norm_smul_id_sub_apply_le_on_leadingEigenSubspace {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {a r : ℝ}
    (hr : 0 ≤ r)
    (hcoeff : ∀ i : Fin n, i ≤ k →
      |a - hT.isSymmetric.eigenvalues hn i| ≤ r)
    {x : E} (hx : x ∈ leadingEigenSubspace T hT hn k) :
    ‖(a • (1 : E →L[ℝ] E) - T) x‖ ≤ r * ‖x‖ := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis hn
  let y : EuclideanSpace ℝ (Fin n) := b.repr x
  have hyzero : ∀ i : Fin n, k < i → y i = 0 := by
    intro i hik
    simpa [y, b, OrthonormalBasis.repr_apply_apply] using
      mem_leadingEigenSubspace_orthogonal_following T hT hn k hx i hik
  have hcoord (i : Fin n) :
      b.repr ((a • (1 : E →L[ℝ] E) - T) x) i =
        (a - hT.isSymmetric.eigenvalues hn i) * y i := by
    have hi := hT.isSymmetric.eigenvectorBasis_apply_self_apply hn x i
    simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
      map_sub, map_smul]
    change a * b.repr x i - b.repr (T x) i = _
    rw [show b.repr (T x) i =
      hT.isSymmetric.eigenvalues hn i * b.repr x i by simpa [b] using hi]
    simp [y]
    ring
  have hxnorm : ‖x‖ ^ 2 = ∑ i, y i ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖y‖ ^ 2 := by rw [b.repr.norm_map]
      _ = ∑ i, y i ^ 2 := EuclideanSpace.real_norm_sq_eq y
  have houtnorm : ‖(a • (1 : E →L[ℝ] E) - T) x‖ ^ 2 =
      ∑ i, ((a - hT.isSymmetric.eigenvalues hn i) * y i) ^ 2 := by
    calc
      ‖(a • (1 : E →L[ℝ] E) - T) x‖ ^ 2 =
          ‖b.repr ((a • (1 : E →L[ℝ] E) - T) x)‖ ^ 2 := by
            rw [b.repr.norm_map]
      _ = ∑ i, (b.repr ((a • (1 : E →L[ℝ] E) - T) x) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      _ = _ := by simp_rw [hcoord]
  have hsum :
      ∑ i, ((a - hT.isSymmetric.eigenvalues hn i) * y i) ^ 2 ≤
        r ^ 2 * ∑ i, y i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hik : k < i
    · simp [hyzero i hik]
    · have hi := hcoeff i (le_of_not_gt hik)
      have hsq : (a - hT.isSymmetric.eigenvalues hn i) ^ 2 ≤ r ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (a - hT.isSymmetric.eigenvalues hn i)) hr).2 hi
      calc
        ((a - hT.isSymmetric.eigenvalues hn i) * y i) ^ 2 =
            (a - hT.isSymmetric.eigenvalues hn i) ^ 2 * (y i) ^ 2 := by ring
        _ ≤ r ^ 2 * (y i) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg (y i))
  rw [← hxnorm, ← houtnorm] at hsum
  nlinarith [norm_nonneg ((a • (1 : E →L[ℝ] E) - T) x),
    mul_nonneg hr (norm_nonneg x)]

/-- If `c ≤ |a - λᵢ|` after index `k`, then `c‖x‖ ≤ ‖(aI - T)x‖` for every `x` in the following eigenspace.

**Lean implementation helper.** -/
lemma norm_smul_id_sub_apply_ge_on_followingEigenSubspace {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) {a c : ℝ}
    (hc : 0 ≤ c)
    (hcoeff : ∀ i : Fin n, k < i →
      c ≤ |a - hT.isSymmetric.eigenvalues hn i|)
    {x : E} (hx : x ∈ followingEigenSubspace T hT hn k) :
    c * ‖x‖ ≤ ‖(a • (1 : E →L[ℝ] E) - T) x‖ := by
  classical
  let b := hT.isSymmetric.eigenvectorBasis hn
  let y : EuclideanSpace ℝ (Fin n) := b.repr x
  have hyzero : ∀ i : Fin n, i ≤ k → y i = 0 := by
    intro i hik
    simpa [y, b, OrthonormalBasis.repr_apply_apply] using
      mem_followingEigenSubspace_orthogonal_leading T hT hn k hx i hik
  have hcoord (i : Fin n) :
      b.repr ((a • (1 : E →L[ℝ] E) - T) x) i =
        (a - hT.isSymmetric.eigenvalues hn i) * y i := by
    have hi := hT.isSymmetric.eigenvectorBasis_apply_self_apply hn x i
    simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
      map_sub, map_smul]
    change a * b.repr x i - b.repr (T x) i = _
    rw [show b.repr (T x) i =
      hT.isSymmetric.eigenvalues hn i * b.repr x i by simpa [b] using hi]
    simp [y]
    ring
  have hxnorm : ‖x‖ ^ 2 = ∑ i, y i ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖y‖ ^ 2 := by rw [b.repr.norm_map]
      _ = ∑ i, y i ^ 2 := EuclideanSpace.real_norm_sq_eq y
  have houtnorm : ‖(a • (1 : E →L[ℝ] E) - T) x‖ ^ 2 =
      ∑ i, ((a - hT.isSymmetric.eigenvalues hn i) * y i) ^ 2 := by
    calc
      ‖(a • (1 : E →L[ℝ] E) - T) x‖ ^ 2 =
          ‖b.repr ((a • (1 : E →L[ℝ] E) - T) x)‖ ^ 2 := by
            rw [b.repr.norm_map]
      _ = ∑ i, (b.repr ((a • (1 : E →L[ℝ] E) - T) x) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      _ = _ := by simp_rw [hcoord]
  have hsum : c ^ 2 * ∑ i, y i ^ 2 ≤
      ∑ i, ((a - hT.isSymmetric.eigenvalues hn i) * y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hik : i ≤ k
    · simp [hyzero i hik]
    · have hi := hcoeff i (lt_of_not_ge hik)
      have hsq : c ^ 2 ≤ (a - hT.isSymmetric.eigenvalues hn i) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ hc (abs_nonneg (a - hT.isSymmetric.eigenvalues hn i))).2 hi
      calc
        c ^ 2 * (y i) ^ 2 ≤
            (a - hT.isSymmetric.eigenvalues hn i) ^ 2 * (y i) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg (y i))
        _ = ((a - hT.isSymmetric.eigenvalues hn i) * y i) ^ 2 := by ring
  rw [← hxnorm, ← houtnorm] at hsum
  nlinarith [norm_nonneg ((a • (1 : E →L[ℝ] E) - T) x),
    mul_nonneg hc (norm_nonneg x)]

/-- Davis--Kahan bound for leading eigenspace projections.

**Book Exercise 4.13.** -/
theorem exercise_4_13_davisKahan_topEigenprojections {n : ℕ}
    (A B : E →L[ℝ] E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hn : Module.finrank ℝ E = n) (k : Fin n)
    (hk : k.val + 1 < n) :
    let ksucc : Fin n := ⟨k.val + 1, hk⟩
    let gap := hA.isSymmetric.eigenvalues hn k -
      hA.isSymmetric.eigenvalues hn ksucc
    0 < gap →
      ‖(leadingEigenSubspace A hA hn k).starProjection -
          (leadingEigenSubspace B hB hn k).starProjection‖ ≤
        2 * ‖A - B‖ / gap := by
  dsimp only
  intro hgap
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  let ksucc : Fin n := ⟨k.val + 1, hk⟩
  let PA := leadingEigenSubspace A hA hn k
  let PB := leadingEigenSubspace B hB hn k
  let VA := followingEigenSubspace A hA hn k
  let ε := ‖A - B‖
  let alpha := hB.isSymmetric.eigenvalues hn ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  let r := alpha - hB.isSymmetric.eigenvalues hn k
  let delta := hB.isSymmetric.eigenvalues hn k -
    hA.isSymmetric.eigenvalues hn ksucc
  have hr : 0 ≤ r := by
    dsimp [r, alpha]
    exact sub_nonneg.mpr (hB.isSymmetric.eigenvalues_antitone hn (Fin.zero_le k))
  have hrank : Module.finrank ℝ PA = Module.finrank ℝ PB := by
    simp [PA, PB, finrank_leadingEigenSubspace]
  by_cases hlarge :
      (hA.isSymmetric.eigenvalues hn k -
        hA.isSymmetric.eigenvalues hn ksucc) / 2 ≤ ε
  · have hone := norm_sub_starProjections_le_one PA PB
    have hright : 1 ≤ 2 * ε /
        (hA.isSymmetric.eigenvalues hn k -
          hA.isSymmetric.eigenvalues hn ksucc) := by
      apply (le_div_iff₀ hgap).2
      nlinarith
    exact hone.trans hright
  · have hsmall : ε <
        (hA.isSymmetric.eigenvalues hn k -
          hA.isSymmetric.eigenvalues hn ksucc) / 2 := lt_of_not_ge hlarge
    have hweyl := weylEigenvalue A B hA hB hn k
    have hdelta :
        (hA.isSymmetric.eigenvalues hn k -
          hA.isSymmetric.eigenvalues hn ksucc) - ε ≤ delta := by
      dsimp [delta, ε]
      have habs : hA.isSymmetric.eigenvalues hn k -
          hB.isSymmetric.eigenvalues hn k ≤ ‖A - B‖ :=
        (le_abs_self _).trans hweyl
      linarith
    have hdelta_pos : 0 < delta := by
      dsimp [ε] at hsmall
      linarith
    let Bshift := alpha • (1 : E →L[ℝ] E) - B
    let Ashift := alpha • (1 : E →L[ℝ] E) - A
    have hBinv : ∀ x : E, x ∈ PB → Bshift x ∈ PB := by
      intro x hx
      change alpha • x - B x ∈ PB
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hx)
        (leadingEigenSubspace_invariant B hB hn k hx)
    have hBcontract : ∀ x : E, x ∈ PB → ‖Bshift x‖ ≤ r * ‖x‖ := by
      intro x hx
      refine norm_smul_id_sub_apply_le_on_leadingEigenSubspace B hB hn k hr
        (x := x) ?_ hx
      intro i hik
      have htop := hB.isSymmetric.eigenvalues_antitone hn (Fin.zero_le i)
      have hbottom := hB.isSymmetric.eigenvalues_antitone hn hik
      dsimp [alpha, r]
      rw [abs_of_nonneg (sub_nonneg.mpr htop)]
      linarith
    have hAexpand : ∀ x : E, x ∈ VA →
        (r + delta) * ‖x‖ ≤ ‖Ashift x‖ := by
      intro x hx
      refine norm_smul_id_sub_apply_ge_on_followingEigenSubspace A hA hn k
        (a := alpha) (c := r + delta) (by linarith) (x := x) ?_ hx
      intro i hik
      have hmono := hA.isSymmetric.eigenvalues_antitone hn
        (show ksucc ≤ i by
          change k.val + 1 ≤ i.val
          omega)
      have hnonneg : 0 ≤ alpha - hA.isSymmetric.eigenvalues hn i := by
        dsimp [r, delta] at hdelta_pos
        linarith
      rw [abs_of_nonneg hnonneg]
      dsimp [r, delta]
      linarith
    have hAcomm : ∀ x : E,
        Ashift (VA.starProjection x) = VA.starProjection (Ashift x) := by
      intro x
      have hcomm := selfAdjoint_commutes_starProjection_of_invariant A hA VA
        (fun y hy => followingEigenSubspace_invariant A hA hn k hy) x
      change (alpha • (1 : E →L[ℝ] E) - A) (VA.starProjection x) =
        VA.starProjection ((alpha • (1 : E →L[ℝ] E) - A) x)
      simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
        map_sub, map_smul]
      rw [hcomm]
    have hcross := davisKahanSpectralProjections Bshift Ashift PB VA hr
      hdelta_pos hBinv hBcontract hAcomm hAexpand
    have hVA : VA = PAᗮ := by
      simp [VA, PA, leadingEigenSubspace]
    have hdiff : Ashift - Bshift = B - A := by
      ext x
      simp [Ashift, Bshift]
    rw [hVA, hdiff] at hcross
    have heq := (exercise_4_12c_projection_difference_of_finrank_eq PA PB hrank).1
    rw [heq]
    calc
      ‖PAᗮ.starProjection ∘L PB.starProjection‖ ≤ ‖B - A‖ / delta := hcross
      _ = ε / delta := by rw [show ‖B - A‖ = ‖A - B‖ by rw [← norm_neg, neg_sub]]
      _ ≤ 2 * ε /
          (hA.isSymmetric.eigenvalues hn k -
            hA.isSymmetric.eigenvalues hn ksucc) := by
        have hε : 0 ≤ ε := norm_nonneg _
        have hhalf :
            (hA.isSymmetric.eigenvalues hn k -
              hA.isSymmetric.eigenvalues hn ksucc) / 2 < delta := by
          linarith
        calc
          ε / delta ≤ ε /
              ((hA.isSymmetric.eigenvalues hn k -
                hA.isSymmetric.eigenvalues hn ksucc) / 2) :=
            div_le_div_of_nonneg_left hε (by linarith) hhalf.le
          _ = 2 * ε /
              (hA.isSymmetric.eigenvalues hn k -
                hA.isSymmetric.eigenvalues hn ksucc) := by
            field_simp [ne_of_gt hgap]

/-! ### Exercise 4.14: Hermitian dilation -/

/-- The real Hermitian dilation `[[0,A],[Aᵀ,0]]`.

**Lean implementation helper.** -/
def hermitianDilation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 A Aᵀ 0

/-- Shows that hermitian dilation is Hermitian.

**Lean implementation helper.** -/
lemma hermitianDilation_isHermitian {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (hermitianDilation A).IsHermitian := by
  rw [hermitianDilation, Matrix.isHermitian_fromBlocks_iff]
  simp

/-- Hermitian dilation is additive.

**Lean implementation helper.** -/
@[simp] lemma hermitianDilation_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    hermitianDilation (A + B) = hermitianDilation A + hermitianDilation B := by
  simp [hermitianDilation, Matrix.fromBlocks_add]

/-- Plus eigenvector assembled from a left/right singular pair.

**Lean implementation helper.** -/
def dilationPlus {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ) :
    (Fin m ⊕ Fin n) → ℝ := Sum.elim u v

/-- Minus eigenvector assembled from a left/right singular pair.

**Lean implementation helper.** -/
def dilationMinus {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ) :
    (Fin m ⊕ Fin n) → ℝ := Sum.elim u (-v)

/-- Hermitian dilation converts singular triples into positive/negative eigenpairs.

**Book Exercise 4.14.** -/
theorem exercise_4_14_hermitianDilation_eigenpair {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (s : ℝ) (hAv : A *ᵥ v = s • u) (hATu : Aᵀ *ᵥ u = s • v) :
    hermitianDilation A *ᵥ dilationPlus u v = s • dilationPlus u v ∧
      hermitianDilation A *ᵥ dilationMinus u v =
        (-s) • dilationMinus u v := by
  constructor
  · rw [hermitianDilation, Matrix.fromBlocks_mulVec]
    ext i
    cases i with
    | inl i => simpa [dilationPlus] using congrFun hAv i
    | inr i => simpa [dilationPlus] using congrFun hATu i
  · rw [hermitianDilation, Matrix.fromBlocks_mulVec]
    ext i
    cases i with
    | inl i =>
        have hi := congrFun hAv i
        simp only [dilationMinus, Sum.elim_inl,
          zero_mulVec, zero_add, Pi.smul_apply, smul_eq_mul]
        simpa [Matrix.mulVec] using congrArg Neg.neg hi
    | inr i =>
        have hi := congrFun hATu i
        simpa [dilationMinus] using hi

/-- The left singular equation supplied by a source-strength rectangular SVD.

**Lean implementation helper.** -/
theorem RealSVD.apply_left {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (d : RealSVD A) (j : Fin (min m n)) :
    A.toEuclideanLin.adjoint (d.left j) =
      d.singularValue j • d.right j := by
  have htranspose : Aᵀ = ∑ i : Fin (min m n),
      d.singularValue i • outerMatrix (d.right i) (d.left i) := by
    calc
      Aᵀ = (∑ i : Fin (min m n), d.singularValue i •
          outerMatrix (d.left i) (d.right i))ᵀ := congrArg Matrix.transpose d.eq_sum_outer
      _ = ∑ i : Fin (min m n),
          (d.singularValue i • outerMatrix (d.left i) (d.right i))ᵀ := by
            simpa using Matrix.transpose_sum (Finset.univ : Finset (Fin (min m n)))
              (fun i => d.singularValue i • outerMatrix (d.left i) (d.right i))
      _ = _ := by simp
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial, htranspose]
  simp only [map_sum, map_smul, toEuclideanLin_outerMatrix,
    LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_eq_single j]
  · change d.singularValue j •
      (inner ℝ (d.left j) (d.left j) • d.right j) = _
    rw [inner_self_eq_norm_sq_to_K, d.left_orthonormal.1]
    simp
  · intro i _ hij
    change d.singularValue i •
      (inner ℝ (d.left i) (d.left j) • d.right i) = 0
    rw [d.left_orthonormal.2 hij]
    simp
  · simp

/-- Every singular triple in an SVD gives the two advertised eigenpairs of the Hermitian
dilation.

**Book Exercise 4.14.** -/
theorem exercise_4_14_hermitianDilation_svd_eigenpairs {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (d : RealSVD A)
    (i : Fin (min m n)) :
    hermitianDilation A *ᵥ
        dilationPlus (WithLp.ofLp (d.left i)) (WithLp.ofLp (d.right i)) =
      d.singularValue i •
        dilationPlus (WithLp.ofLp (d.left i)) (WithLp.ofLp (d.right i)) ∧
    hermitianDilation A *ᵥ
        dilationMinus (WithLp.ofLp (d.left i)) (WithLp.ofLp (d.right i)) =
      (-d.singularValue i) •
        dilationMinus (WithLp.ofLp (d.left i)) (WithLp.ofLp (d.right i)) := by
  apply exercise_4_14_hermitianDilation_eigenpair
  · exact congrArg (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))
      (d.apply_right i)
  · have h := congrArg (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (d.apply_left i)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h

/-- Algebraic completeness of Hermitian dilation: every nonzero eigenvalue has absolute value
equal to one of the authoritative singular values of `A`.

**Book Exercise 4.14.** -/
theorem exercise_4_14_hermitianDilation_only_nonzero_eigenvalues_of_blocks
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n))
    (lambda : ℝ)
    (hAv : A.toEuclideanLin v = lambda • u)
    (hATu : A.toEuclideanLin.adjoint u = lambda • v)
    (hpair : u ≠ 0 ∨ v ≠ 0) (hlambda : lambda ≠ 0) :
    ∃ i : Fin n, |lambda| = HDP.matrixSingularValue A i := by
  have hv : v ≠ 0 := by
    intro hv
    have hu : u = 0 := by
      have hz : lambda • u = 0 := by simpa [hv] using hAv.symm
      rcases smul_eq_zero.mp hz with hlam | hu'
      · exact (hlambda hlam).elim
      · exact hu'
    exact hpair.elim (fun h => h hu) (fun h => h hv)
  have hgram :
      (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) v =
        lambda ^ 2 • v := by
    rw [LinearMap.comp_apply, hAv, map_smul, hATu, smul_smul]
    congr 1
    ring
  have heigen : Module.End.HasEigenvalue
      (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) (lambda ^ 2) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hgram, hv⟩
  obtain ⟨i, hi⟩ :=
    A.toEuclideanLin.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) heigen
  have hsvsq := A.toEuclideanLin.sq_singularValues_fin
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) i
  refine ⟨i, ?_⟩
  have hnonneg := HDP.matrixSingularValue_nonneg A i
  have habsnonneg : 0 ≤ |lambda| := abs_nonneg _
  have hsquares : HDP.matrixSingularValue A i ^ 2 = |lambda| ^ 2 := by
    rw [sq_abs]
    exact hsvsq.trans hi
  nlinarith

/-- Together with `exercise_4_14_hermitianDilation_svd_eigenpairs`, this proves that the only
nonzero eigenvalues are the advertised `±sᵢ`.

**Book Exercise 4.14.** -/
theorem exercise_4_14_hermitianDilation_only_nonzero_eigenvalues
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n))
    (lambda : ℝ)
    (hvec : dilationPlus (WithLp.ofLp u) (WithLp.ofLp v) ≠ 0)
    (heigen : hermitianDilation A *ᵥ
        dilationPlus (WithLp.ofLp u) (WithLp.ofLp v) =
      lambda • dilationPlus (WithLp.ofLp u) (WithLp.ofLp v))
    (hlambda : lambda ≠ 0) :
    ∃ i : Fin n, |lambda| = HDP.matrixSingularValue A i := by
  have hblocks := heigen
  rw [hermitianDilation, Matrix.fromBlocks_mulVec] at hblocks
  have hAvfun : A *ᵥ WithLp.ofLp v = lambda • WithLp.ofLp u := by
    ext i
    have hi := congrFun hblocks (Sum.inl i)
    simpa [dilationPlus] using hi
  have hATufun : Aᵀ *ᵥ WithLp.ofLp u = lambda • WithLp.ofLp v := by
    ext i
    have hi := congrFun hblocks (Sum.inr i)
    simpa [dilationPlus] using hi
  have hAv : A.toEuclideanLin v = lambda • u :=
    congrArg (WithLp.toLp 2) hAvfun
  have hATu : A.toEuclideanLin.adjoint u = lambda • v := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact congrArg (WithLp.toLp 2) hATufun
  have hpair : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hvec (by ext i; cases i <;> simp [dilationPlus, h.1, h.2])
  exact exercise_4_14_hermitianDilation_only_nonzero_eigenvalues_of_blocks
    A u v lambda hAv hATu hpair hlambda

/-! ### Exercise 4.16: angle to sign-distance -/

/-- Small acute angle implies closeness up to a global sign.

**Book Exercise 4.16.** -/
theorem exercise_4_16_angle_sign_distance {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsin : 1 - |inner ℝ u v| ^ 2 ≤ ε ^ 2) :
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧ ‖u - θ • v‖ ≤ Real.sqrt 2 * ε := by
  have hinner : |inner ℝ u v| ≤ 1 := by
    calc
      |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hu, hv, one_mul]
  let θ : ℝ := if 0 ≤ inner ℝ u v then 1 else -1
  have hθ : θ = 1 ∨ θ = -1 := by
    by_cases h : 0 ≤ inner ℝ u v <;> simp [θ, h]
  have hθinner : θ * inner ℝ u v = |inner ℝ u v| := by
    by_cases h : 0 ≤ inner ℝ u v
    · simp [θ, h, abs_of_nonneg h]
    · have hle : inner ℝ u v ≤ 0 := le_of_not_ge h
      simp [θ, h, abs_of_nonpos hle]
  have hθsq : θ ^ 2 = 1 := by rcases hθ with h | h <;> rw [h] <;> norm_num
  have hnormsq : ‖u - θ • v‖ ^ 2 = 2 - 2 * |inner ℝ u v| := by
    rcases hθ with hθ | hθ
    · rw [hθ] at hθinner
      rw [hθ, one_smul, norm_sub_sq_real, hu, hv]
      norm_num at hθinner ⊢
      linarith
    · rw [hθ] at hθinner
      rw [hθ, neg_one_smul, sub_neg_eq_add, norm_add_sq_real, hu, hv]
      norm_num at hθinner ⊢
      linarith
  have hone : 0 ≤ |inner ℝ u v| := abs_nonneg _
  have hsq : ‖u - θ • v‖ ^ 2 ≤ (Real.sqrt 2 * ε) ^ 2 := by
    rw [hnormsq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_nonneg (1 - |inner ℝ u v|)]
  refine ⟨θ, hθ, ?_⟩
  nlinarith [norm_nonneg (u - θ • v), Real.sqrt_nonneg 2,
    mul_nonneg (Real.sqrt_nonneg 2) hε]

/-- Canonical source-numbered public name for Lemma 4.1.14. -/
alias lemma_4_1_14 := weylEigenvalue

/-- Canonical source-numbered public name for Theorem 4.1.15. -/
alias theorem_4_1_15 := davisKahan

/-- Canonical source-numbered public name for Lemma 4.1.16. -/
alias lemma_4_1_16 := davisKahanSpectralProjections

end HDP.Chapter4

end Source_05_SpectralPerturbation

/-! ## Material formerly in `06_ApproximateIsometries.lean` -/

section Source_06_ApproximateIsometries

/-!
# Chapter 4, §4.1.7: isometries and approximate isometries

The operator formulation below is definitionally compatible with Mathlib's
Euclidean Gram operator.  A separate bridge identifies it with the matrix
`Aᵀ A - I`, so downstream results can use either interface without hiding a
change of norm.
-/

open Matrix WithLp Real
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter4

set_option linter.unusedSectionVars false

/-- The self-adjoint Gram error `A* A - I` as a continuous operator.

**Lean implementation helper.** -/
noncomputable def gramDeviationOperator {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (HDP.gramMatrix A - 1).toEuclideanLin.toContinuousLinearMap

/-- Shows that gram deviation operator is self-adjoint.

**Lean implementation helper.** -/
lemma gramDeviationOperator_isSelfAdjoint {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsSelfAdjoint (gramDeviationOperator A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  rw [gramDeviationOperator]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((HDP.gramMatrix_isHermitian A).sub Matrix.isHermitian_one)

/-- The Rayleigh quotient of the Gram-deviation operator `AᵀA-I` is `‖Ax‖²-‖x‖²`.

**Lean implementation helper.** -/
lemma gramDeviationOperator_rayleigh {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (gramDeviationOperator A).reApplyInnerSelf x =
      ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
  change inner ℝ (((HDP.gramMatrix A - 1).toEuclideanLin) x) x = _
  have hgram : (HDP.gramMatrix A).toEuclideanLin =
      A.toEuclideanLin.adjoint.comp A.toEuclideanLin := by
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [HDP.gramMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    have hmul := Matrix.toLin_mul_apply
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Aᵀ A y
    change (Aᵀ * A).toEuclideanLin y =
      Aᵀ.toEuclideanLin (A.toEuclideanLin y) at hmul
    exact hmul
  simp only [map_sub]
  rw [hgram, LinearMap.sub_apply, LinearMap.comp_apply]
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ).toEuclideanLin = LinearMap.id :=
    Matrix.toLpLin_one 2
  rw [hone]
  simp only [LinearMap.id_apply, inner_sub_left,
    LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- The matrix and continuous-operator realizations of the Gram error agree.

**Lean implementation helper.** -/
lemma gramDeviationOperator_eq_matrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    gramDeviationOperator A =
      (HDP.gramMatrix A - 1).toEuclideanLin.toContinuousLinearMap := by
  rfl

/-- Consequently the authoritative matrix norm is the norm of the Gram-error operator used in
the proof.

**Lean implementation helper.** -/
lemma matrixOpNorm_gramDeviation {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixOpNorm (HDP.gramMatrix A - 1) = ‖gramDeviationOperator A‖ := by
  rw [gramDeviationOperator_eq_matrix A]
  rfl

/-- The extreme singular values control every vector. This is equation (4.14) in its homogeneous
form.

**Book (4.14).** -/
theorem extremeSingularValues_bound {m n : ℕ} [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HDP.matrixSingularValue A (n - 1) * ‖x‖ ≤ ‖A.toEuclideanLin x‖ ∧
      ‖A.toEuclideanLin x‖ ≤ HDP.matrixSingularValue A 0 * ‖x‖ := by
  let i0 : Fin n := ⟨0, NeZero.pos n⟩
  have hnpos : 0 < n := NeZero.pos n
  let ilast : Fin n := ⟨n - 1, by omega⟩
  have hunit (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ = 1) :
      HDP.matrixSingularValue A ilast ≤ ‖A.toEuclideanLin z‖ ∧
        ‖A.toEuclideanLin z‖ ≤ HDP.matrixSingularValue A i0 := by
    rcases (singularValueMinMax A ilast).1.2 with
      ⟨Vlo, hVlodim, hlo, _zlo, _hzloV, _hzlonorm, _hzloattain⟩
    rcases (singularValueMinMax A i0).2.2 with
      ⟨Vhi, hVhidim, hhi, _zhi, _hzhiV, _hzhinorm, _hzhiattain⟩
    have hVlo : Vlo = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa [ilast, finrank_euclideanSpace_fin, Nat.sub_add_cancel hnpos] using hVlodim
    have hVhi : Vhi = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa [i0, finrank_euclideanSpace_fin] using hVhidim
    exact ⟨hlo z (by simp [hVlo]) hz, hhi z (by simp [hVhi]) hz⟩
  by_cases hx : x = 0
  · simp [hx]
  · let z := ‖x‖⁻¹ • x
    have hz : ‖z‖ = 1 := by simp [z, norm_smul, hx]
    have hbounds := hunit z hz
    have hxrep : x = ‖x‖ • z := by simp [z, smul_smul, hx]
    have hA : ‖A.toEuclideanLin x‖ = ‖x‖ * ‖A.toEuclideanLin z‖ := by
      calc
        ‖A.toEuclideanLin x‖ = ‖A.toEuclideanLin (‖x‖ • z)‖ := by rw [← hxrep]
        _ = ‖x‖ * ‖A.toEuclideanLin z‖ := by
          rw [map_smul, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg x)]
    change HDP.matrixSingularValue A ilast * ‖x‖ ≤ _ ∧
      _ ≤ HDP.matrixSingularValue A i0 * ‖x‖
    rw [hA]
    constructor <;> nlinarith [norm_nonneg x]

/-- Extreme singular values bound distortion; condition number measures worst-case distortion;
exact isometries are equivalent to orthonormal columns/Gram identity/all singular values one.

**Book (4.14).** -/
theorem gramBound_iff_quadraticBounds {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    HDP.matrixOpNorm (HDP.gramMatrix A - 1) ≤ ε ↔
      ∀ x : EuclideanSpace ℝ (Fin n),
        (1 - ε) * ‖x‖ ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 ∧
          ‖A.toEuclideanLin x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2 := by
  rw [matrixOpNorm_gramDeviation]
  constructor
  · intro h x
    have hray := (gramDeviationOperator A).rayleighQuotient_le_norm x
    have hinner : |(gramDeviationOperator A).reApplyInnerSelf x| ≤
        ε * ‖x‖ ^ 2 := by
      by_cases hx : x = 0
      · simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
      · rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq,
          div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))] at hray
        exact hray.trans (mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖))
    rw [gramDeviationOperator_rayleigh] at hinner
    rw [abs_le] at hinner
    constructor <;> nlinarith
  · intro h
    rw [(gramDeviationOperator A).norm_eq_iSup_rayleighQuotient
      (gramDeviationOperator_isSelfAdjoint A).isSymmetric]
    refine ciSup_le fun x => ?_
    by_cases hx : x = 0
    · simp [hx, hε]
    · have hx2 : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
      have hb := h x
      have hdiff : |‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2| ≤
          ε * ‖x‖ ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith
      rw [ContinuousLinearMap.rayleighQuotient,
        gramDeviationOperator_rayleigh, abs_div, abs_sq]
      exact (div_le_iff₀ hx2).2 hdiff

/-- Extreme singular values bound distortion; condition number measures worst-case distortion;
exact isometries are equivalent to orthonormal columns/Gram identity/all singular values one.

**Book (4.14).** -/
theorem quadraticBounds_iff_extremeSingularValues {m n : ℕ} [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} :
    (∀ x : EuclideanSpace ℝ (Fin n),
        (1 - ε) * ‖x‖ ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 ∧
          ‖A.toEuclideanLin x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2) ↔
      1 - ε ≤ HDP.matrixSingularValue A (n - 1) ^ 2 ∧
        HDP.matrixSingularValue A (n - 1) ^ 2 ≤
          HDP.matrixSingularValue A 0 ^ 2 ∧
        HDP.matrixSingularValue A 0 ^ 2 ≤ 1 + ε := by
  let i0 : Fin n := ⟨0, NeZero.pos n⟩
  have hnpos : 0 < n := NeZero.pos n
  let ilast : Fin n := ⟨n - 1, by omega⟩
  constructor
  · intro h
    have hlo := h (rightSingularBasis A ilast)
    have hhi := h (rightSingularBasis A i0)
    rw [(rightSingularBasis A).norm_eq_one,
      norm_apply_rightSingularVector] at hlo hhi
    have hmono : HDP.matrixSingularValue A ilast ≤
        HDP.matrixSingularValue A i0 :=
      HDP.matrixSingularValue_antitone A (by simp [i0])
    change 1 - ε ≤ HDP.matrixSingularValue A ilast ^ 2 ∧
      HDP.matrixSingularValue A ilast ^ 2 ≤
        HDP.matrixSingularValue A i0 ^ 2 ∧
      HDP.matrixSingularValue A i0 ^ 2 ≤ 1 + ε
    exact ⟨by simpa using hlo.1,
      (sq_le_sq₀ (HDP.matrixSingularValue_nonneg A ilast)
        (HDP.matrixSingularValue_nonneg A i0)).2 hmono,
      by simpa using hhi.2⟩
  · rintro ⟨hlo, _horder, hhi⟩ x
    have hb := extremeSingularValues_bound A x
    have hslo := HDP.matrixSingularValue_nonneg A (n - 1)
    have hshi := HDP.matrixSingularValue_nonneg A 0
    constructor
    · calc
        (1 - ε) * ‖x‖ ^ 2
            ≤ HDP.matrixSingularValue A (n - 1) ^ 2 * ‖x‖ ^ 2 := by
              gcongr
        _ = (HDP.matrixSingularValue A (n - 1) * ‖x‖) ^ 2 := by ring
        _ ≤ ‖A.toEuclideanLin x‖ ^ 2 :=
          (sq_le_sq₀ (mul_nonneg hslo (norm_nonneg x))
            (norm_nonneg _)).2 hb.1
    · calc
        ‖A.toEuclideanLin x‖ ^ 2
            ≤ (HDP.matrixSingularValue A 0 * ‖x‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hshi (norm_nonneg x))).2 hb.2
        _ = HDP.matrixSingularValue A 0 ^ 2 * ‖x‖ ^ 2 := by ring
        _ ≤ (1 + ε) * ‖x‖ ^ 2 := by gcongr

/-- Gram error, quadratic distortion, and squared extreme-singular-value bounds are equivalent
approximate-isometry conditions.

**Book Lemma 4.1.17.** -/
theorem approximateIsometries {m n : ℕ} [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    HDP.matrixOpNorm (HDP.gramMatrix A - 1) ≤ ε ↔
      (∀ x : EuclideanSpace ℝ (Fin n),
        (1 - ε) * ‖x‖ ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 ∧
          ‖A.toEuclideanLin x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2) :=
  gramBound_iff_quadraticBounds A hε

/-- The full three-way equivalence in the corresponding lemma.

**Book Lemma 4.1.17.** -/
theorem approximateIsometries_threeWay {m n : ℕ} [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (HDP.matrixOpNorm (HDP.gramMatrix A - 1) ≤ ε ↔
      ∀ x : EuclideanSpace ℝ (Fin n),
        (1 - ε) * ‖x‖ ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 ∧
          ‖A.toEuclideanLin x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2) ∧
    ((∀ x : EuclideanSpace ℝ (Fin n),
        (1 - ε) * ‖x‖ ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 ∧
          ‖A.toEuclideanLin x‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2) ↔
      1 - ε ≤ HDP.matrixSingularValue A (n - 1) ^ 2 ∧
        HDP.matrixSingularValue A (n - 1) ^ 2 ≤
          HDP.matrixSingularValue A 0 ^ 2 ∧
        HDP.matrixSingularValue A 0 ^ 2 ≤ 1 + ε) :=
  ⟨gramBound_iff_quadraticBounds A hε,
    quadraticBounds_iff_extremeSingularValues A⟩

/-- Scalar inequality used in the corresponding remark.

**Lean implementation helper.** -/
theorem sq_sub_one_control {z δ : ℝ} (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (h : |z ^ 2 - 1| ≤ max δ (δ ^ 2)) : |z - 1| ≤ δ := by
  by_cases hδ1 : δ ≤ 1
  · rw [max_eq_left (by nlinarith [sq_nonneg δ])] at h
    rw [abs_le] at h ⊢
    constructor <;> nlinarith [sq_nonneg (z - 1)]
  · have hδge : 1 ≤ δ := le_of_not_ge hδ1
    rw [max_eq_right (by nlinarith)] at h
    rw [abs_le] at h
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (z - 1)]

/-- A Gram error `max(delta,delta^2)` implies unsquared singular values lie in
`[1-delta,1+delta]`.

**Book Remark 4.1.18.** -/
theorem gramError_implies_singularValueBounds {m n : ℕ} [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : HDP.matrixOpNorm (HDP.gramMatrix A - 1) ≤ max δ (δ ^ 2)) :
    1 - δ ≤ HDP.matrixSingularValue A (n - 1) ∧
      HDP.matrixSingularValue A 0 ≤ 1 + δ := by
  have hmax : 0 ≤ max δ (δ ^ 2) := hδ.trans (le_max_left _ _)
  have hthree := (approximateIsometries_threeWay A hmax).1.1 hA
  have hext := (quadraticBounds_iff_extremeSingularValues A).1 hthree
  have hloabs := sq_sub_one_control
    (HDP.matrixSingularValue_nonneg A (n - 1)) hδ
    (by rw [abs_le]; constructor <;> nlinarith [hext.1])
  have hhiabs := sq_sub_one_control
    (HDP.matrixSingularValue_nonneg A 0) hδ
    (by rw [abs_le]; constructor <;> nlinarith [hext.2.2])
  rw [abs_le] at hloabs hhiabs
  exact ⟨by linarith, by linarith⟩

/-- Canonical source-numbered public name for Lemma 4.1.17. -/
alias lemma_4_1_17 := approximateIsometries_threeWay

/-- Canonical source-numbered public name for Remark 4.1.18. -/
alias remark_4_1_18 := gramError_implies_singularValueBounds

end HDP.Chapter4

end Source_06_ApproximateIsometries

/-! ## Material formerly in `07_MetricNets.lean` -/

section Source_07_MetricNets

/-!
# Chapter 4, Section 4.2: nets, covering, and packing

The extended-natural-valued Mathlib covering and packing numbers are used
directly.  In particular, none of the statements below silently assumes that a
covering number is finite.
-/

open Set
open scoped ENNReal NNReal

namespace HDP.Chapter4

variable {X : Type*} [PseudoEMetricSpace X]

/-- This is the exact Mathlib correspondence, with the source's requirement that the centers lie
in `K`.

**Book Definition 4.2.1.** -/
theorem definition_4_2_1 {ε : ℝ≥0} {K N : Set X} :
    HDP.IsEpsilonNet ε K N ↔ N ⊆ K ∧ Metric.IsCover ε K N :=
  Iff.rfl

/-- Expresses the covering number as the infimum of cardinalities of internal covers.

**Book Definition 4.2.2.** -/
theorem definition_4_2_2 (ε : ℝ≥0) (K : Set X) :
    Metric.coveringNumber ε K =
      ⨅ (N : Set X) (_ : N ⊆ K) (_ : Metric.IsCover ε K N), N.encard :=
  rfl

/-- Expresses the packing number as the supremum of cardinalities of separated subsets.

**Book Definition 4.2.4.** -/
theorem definition_4_2_4 (ε : ℝ≥0) (K : Set X) :
    Metric.packingNumber ε K =
      ⨆ (N : Set X) (_ : N ⊆ K) (_ : Metric.IsSeparated ε N), N.encard :=
  rfl

/-- In a complete metric space, relative compactness is equivalent to the existence of finite
internal covers at every positive scale.

**Book Remark 4.2.3.** -/
theorem remark_4_2_3 {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (K : Set Y) :
    IsCompact (closure K) ↔
      ∀ ε : ℝ≥0, ε ≠ 0 → ∃ N ⊆ K, N.Finite ∧ Metric.IsCover ε K N := by
  constructor
  · intro hK ε hε
    exact Metric.exists_finite_isCover_of_isCompact_closure hε hK
  · intro h
    have htot : TotallyBounded K := by
      rw [Metric.totallyBounded_iff]
      intro δ hδ
      let ε : ℝ≥0 := ⟨δ / 2, by positivity⟩
      have hεpos : 0 < ε := by
        change 0 < δ / 2
        positivity
      have hε : ε ≠ 0 := ne_of_gt hεpos
      obtain ⟨N, hNK, hNfin, hNcover⟩ := h ε hε
      refine ⟨N, hNfin, ?_⟩
      intro x hx
      obtain ⟨y, hyN, hxy⟩ := hNcover hx
      simp only [Set.mem_iUnion, exists_prop]
      refine ⟨y, hyN, ?_⟩
      rw [Metric.mem_ball]
      change edist x y ≤ (ε : ℝ≥0∞) at hxy
      have hnn : nndist x y ≤ ε := edist_le_coe.mp hxy
      have hd : dist x y ≤ (ε : ℝ) := by simpa using hnn
      change dist x y < δ
      change dist x y ≤ δ / 2 at hd
      exact hd.trans_lt (by linarith)
    exact htot.closure.isCompact_of_isClosed isClosed_closure

/-- Closed `ε/2`-balls centered at distinct points of an `ε`-separated set are disjoint. This
corrects the radius `ε` typo in the source proof's footnote.

**Book Remark 4.2.5.** -/
theorem remark_4_2_5 {Y : Type*} [MetricSpace Y] {ε : ℝ≥0} {N : Set Y}
    (hN : Metric.IsSeparated ε N) {x y : Y} (hx : x ∈ N) (hy : y ∈ N)
    (hxy : x ≠ y) :
    Disjoint (Metric.closedBall x ((ε : ℝ) / 2))
      (Metric.closedBall y ((ε : ℝ) / 2)) := by
  apply Metric.closedBall_disjoint_closedBall
  have hsep : (ε : ℝ≥0∞) < edist x y := hN hx hy hxy
  rw [edist_nndist] at hsep
  have hnn : ε < nndist x y := ENNReal.coe_lt_coe.mp hsep
  have hreal : (ε : ℝ) < dist x y := NNReal.coe_lt_coe.mpr hnn
  convert hreal using 1
  ring

/-- Shows that a maximal separated subset is a cover at the same radius.

**Book Lemma 4.2.6.** -/
theorem lemma_4_2_6 {ε : ℝ≥0} {K N : Set X}
    (hN : Maximal (fun M : Set X => M ⊆ K ∧ Metric.IsSeparated ε M) N) :
    Metric.IsCover ε K N :=
  Metric.IsCover.of_maximal_isSeparated hN

/-- For a relatively compact set, a maximal separated set exists, is finite, and is an internal
net.

**Book Remark 4.2.7.** -/
theorem remark_4_2_7 {Y : Type*} [MetricSpace Y] {ε : ℝ≥0} (hε : ε ≠ 0)
    {K : Set Y} (hK : IsCompact (closure K)) :
    ∃ N ⊆ K, N.Finite ∧ Metric.IsSeparated ε N ∧ Metric.IsCover ε K N := by
  have hhalf : ε / 2 ≠ 0 := div_ne_zero hε (by norm_num)
  obtain ⟨C, hCK, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact_closure hhalf hK
  have hext : Metric.externalCoveringNumber (ε / 2) K ≠ ⊤ := by
    exact ne_top_of_le_ne_top hCfin.encard_lt_top.ne
      hCcover.externalCoveringNumber_le_encard
  have hpack : Metric.packingNumber ε K ≠ ⊤ := by
    have hle := Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) K
    have htwo : (2 : ℝ≥0) * (ε / 2) = ε := mul_div_cancel₀ ε (by norm_num)
    rw [htwo] at hle
    exact ne_top_of_le_ne_top hext hle
  refine ⟨Metric.maximalSeparatedSet ε K, Metric.maximalSeparatedSet_subset,
    ?_, Metric.isSeparated_maximalSeparatedSet, Metric.isCover_maximalSeparatedSet hpack⟩
  apply Set.encard_ne_top_iff.mp
  rw [Metric.encard_maximalSeparatedSet hpack]
  exact hpack

/-- Relates covering and packing numbers at radii `ε` and `2ε`.

**Book Lemma 4.2.8.** -/
theorem lemma_4_2_8 (ε : ℝ≥0) (K : Set X) :
    Metric.packingNumber (2 * ε) K ≤ Metric.coveringNumber ε K ∧
      Metric.coveringNumber ε K ≤ Metric.packingNumber ε K := by
  constructor
  · exact (Metric.packingNumber_two_mul_le_externalCoveringNumber ε K).trans
      (Metric.externalCoveringNumber_le_coveringNumber ε K)
  · exact Metric.coveringNumber_le_packingNumber ε K

/-- This result is used as shared metric-entropy infrastructure.

**Book Exercise 4.25.** -/
theorem exercise_4_25 (ε : ℝ≥0) (K : Set X) :
    Metric.externalCoveringNumber ε K ≤ Metric.coveringNumber ε K ∧
      Metric.coveringNumber ε K ≤ Metric.externalCoveringNumber (ε / 2) K := by
  constructor
  · exact Metric.externalCoveringNumber_le_coveringNumber ε K
  · have htwo : (2 : ℝ≥0) * (ε / 2) = ε := mul_div_cancel₀ ε (by norm_num)
    simpa [htwo] using
      Metric.coveringNumber_two_mul_le_externalCoveringNumber (ε / 2) K

end HDP.Chapter4

end Source_07_MetricNets

/-! ## Material formerly in `08_VolumetricCovering.lean` -/

section Source_08_VolumetricCovering

/-!
# Chapter 4, Section 4.2.1: volumetric covering bounds

The source writes quotients of volumes.  The main theorem below uses the
equivalent cross-multiplied inequalities in `ℝ≥0∞`; this remains meaningful
without an implicit finiteness convention and avoids division by the volume of
a zero-dimensional or zero-radius ball.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HDP.Chapter4

/-! ## Finite-union volume lemmas -/

variable {n : ℕ} [NeZero n]
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Bounds volume by card mul ball.

**Lean implementation helper.** -/
private theorem volume_le_card_mul_ball {K : Set (Euc n)} {N : Finset (Euc n)}
    {r : ℝ} (hcover : K ⊆ ⋃ x ∈ N, Metric.closedBall x r) :
    volume K ≤ (N.card : ℝ≥0∞) * volume (Metric.closedBall (0 : Euc n) r) := by
  calc
    volume K ≤ volume (⋃ x ∈ N, Metric.closedBall x r) := measure_mono hcover
    _ ≤ ∑ x ∈ N, volume (Metric.closedBall x r) :=
      measure_biUnion_finset_le N (fun x => Metric.closedBall x r)
    _ = (N.card : ℝ≥0∞) * volume (Metric.closedBall (0 : Euc n) r) := by
      simp [EuclideanSpace.volume_closedBall]

/-- Bounds card mul ball by volume minkowski.

**Lean implementation helper.** -/
private theorem card_mul_ball_le_volume_minkowski {K : Set (Euc n)}
    {N : Finset (Euc n)} {r : ℝ}
    (hNK : ∀ x ∈ N, x ∈ K)
    (hsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → 2 * r < dist x y) :
    (N.card : ℝ≥0∞) * volume (Metric.closedBall (0 : Euc n) r) ≤
      volume (HDP.minkowskiSum K (Metric.closedBall (0 : Euc n) r)) := by
  have hdisj : Set.PairwiseDisjoint (↑N : Set (Euc n))
      (fun x => Metric.closedBall x r) := by
    intro x hx y hy hxy
    apply Metric.closedBall_disjoint_closedBall
    simpa [two_mul] using hsep x hx y hy hxy
  have hunion : (⋃ x ∈ N, Metric.closedBall x r) ⊆
      HDP.minkowskiSum K (Metric.closedBall (0 : Euc n) r) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx⟩ := hz
    obtain ⟨hxN, hzx⟩ := hx
    refine HDP.mem_minkowskiSum.mpr ⟨x, hNK x hxN, z - x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzx
    · abel
  calc
    (N.card : ℝ≥0∞) * volume (Metric.closedBall (0 : Euc n) r) =
        ∑ x ∈ N, volume (Metric.closedBall x r) := by
          simp [EuclideanSpace.volume_closedBall]
    _ = volume (⋃ x ∈ N, Metric.closedBall x r) := by
      symm
      exact measure_biUnion_finset hdisj (fun _ _ => measurableSet_closedBall)
    _ ≤ volume (HDP.minkowskiSum K (Metric.closedBall (0 : Euc n) r)) :=
      measure_mono hunion

omit [NeZero n] in
/-- Every subset with a fixed positive pairwise separation in a separable metric space is countable.

**Lean implementation helper.** -/
private theorem positive_separated_countable {ε : ℝ≥0} (hε : 0 < ε)
    {C : Set (Euc n)} (hC : Metric.IsSeparated ε C) : C.Countable := by
  have hdisc : DiscreteTopology C := discreteTopology_subtype_iff'.mpr (by
    intro x hx
    refine ⟨Metric.ball x (ε : ℝ), Metric.isOpen_ball, ?_⟩
    ext y
    constructor
    · rintro ⟨hyball, hyC⟩
      have : y = x := by
        by_contra hyx
        have hsep := hC hyC hx hyx
        change (ε : ℝ≥0∞) < edist y x at hsep
        rw [edist_nndist] at hsep
        have hnn : ε < nndist y x := ENNReal.coe_lt_coe.mp hsep
        have hreal : (ε : ℝ) < dist y x := NNReal.coe_lt_coe.mpr hnn
        exact (not_lt_of_ge hreal.le) hyball
      simp [this]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      exact ⟨by simpa using hε, hx⟩)
  letI : DiscreteTopology C := hdisc
  haveI : Countable C := TopologicalSpace.separableSpace_iff_countable.mp
    (inferInstance : TopologicalSpace.SeparableSpace C)
  exact Set.to_countable C

/-- Bounds encard mul ball by volume minkowski.

**Lean implementation helper.** -/
private theorem encard_mul_ball_le_volume_minkowski {K C : Set (Euc n)}
    {ε : ℝ≥0} (hε : 0 < ε) (hCK : C ⊆ K)
    (hsep : Metric.IsSeparated ε C) :
    (C.encard : ℝ≥0∞) *
        volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ≤
      volume (HDP.minkowskiSum K
        (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2))) := by
  have hCcount : C.Countable := positive_separated_countable hε hsep
  have hdisj : Set.PairwiseDisjoint C
      (fun x => Metric.closedBall x ((ε : ℝ) / 2)) := by
    intro x hx y hy hxy
    apply Metric.closedBall_disjoint_closedBall
    have hs := hsep hx hy hxy
    change (ε : ℝ≥0∞) < edist x y at hs
    rw [edist_nndist] at hs
    have hnn : ε < nndist x y := ENNReal.coe_lt_coe.mp hs
    have hr : (ε : ℝ) < dist x y := NNReal.coe_lt_coe.mpr hnn
    convert hr using 1
    ring
  have hunion : (⋃ x ∈ C, Metric.closedBall x ((ε : ℝ) / 2)) ⊆
      HDP.minkowskiSum K (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hxC, hzx⟩ := hz
    refine HDP.mem_minkowskiSum.mpr ⟨x, hCK hxC, z - x, ?_, by abel⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzx
  calc
    (C.encard : ℝ≥0∞) *
          volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) =
        ∑' x : C, volume (Metric.closedBall (x : Euc n) ((ε : ℝ) / 2)) := by
      calc
        _ = ∑' _ : C, volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) :=
          (ENNReal.tsum_set_const C _).symm
        _ = _ := by
          apply tsum_congr
          intro x
          simp [EuclideanSpace.volume_closedBall]
    _ = volume (⋃ x ∈ C, Metric.closedBall x ((ε : ℝ) / 2)) := by
      symm
      exact measure_biUnion hCcount hdisj (fun _ _ => measurableSet_closedBall)
    _ ≤ volume (HDP.minkowskiSum K
        (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2))) := measure_mono hunion

/-- Shows that volume closed ball is positive.

**Lean implementation helper.** -/
private theorem volume_closedBall_pos {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.closedBall (0 : Euc n) r) := by
  rw [EuclideanSpace.volume_closedBall]
  positivity

omit [NeZero n] in
/-- Identifies Minkowski addition with pointwise addition of sets.

**Book Definition 4.2.9.** -/
theorem definition_4_2_9 (A B : Set (Euc n)) :
    HDP.minkowskiSum A B = {x | ∃ a ∈ A, ∃ b ∈ B, a + b = x} :=
  rfl

/-- Finite certificate underlying the corresponding source proposition. The hypotheses `hK`
and `hε` guarantee that the internal covering and packing numbers are finite. The returned
natural numbers are certified to be exactly Mathlib's extended-natural covering and packing
numbers.

**Lean implementation helper.** -/
theorem volumetric_finite_certificate {K : Set (Euc n)} (hK : IsCompact (closure K))
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ NC NP : ℕ,
      (NC : ℕ∞) = Metric.coveringNumber ε K ∧
      (NP : ℕ∞) = Metric.packingNumber ε K ∧
      volume K ≤ (NC : ℝ≥0∞) *
        volume (Metric.closedBall (0 : Euc n) (ε : ℝ)) ∧
      Metric.coveringNumber ε K ≤ Metric.packingNumber ε K ∧
      (NP : ℝ≥0∞) *
          volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ≤
        volume (HDP.minkowskiSum K
          (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2))) := by
  have hcoverfin : Metric.coveringNumber ε K ≠ ⊤ := by
    obtain ⟨N, hNK, hNfin, hNcover⟩ :=
      Metric.exists_finite_isCover_of_isCompact_closure hε hK
    exact ne_top_of_le_ne_top hNfin.encard_lt_top.ne
      (hNcover.coveringNumber_le_encard hNK)
  have hhalf : ε / 2 ≠ 0 := div_ne_zero hε (by norm_num)
  obtain ⟨C, hCK, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact_closure hhalf hK
  have hext : Metric.externalCoveringNumber (ε / 2) K ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin.encard_lt_top.ne
      hCcover.externalCoveringNumber_le_encard
  have htwo : (2 : ℝ≥0) * (ε / 2) = ε := mul_div_cancel₀ ε (by norm_num)
  have hpackfin : Metric.packingNumber ε K ≠ ⊤ := by
    have hle := Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) K
    rw [htwo] at hle
    exact ne_top_of_le_ne_top hext hle
  let Ncov : Set (Euc n) := Metric.minimalCover ε K
  let Npack : Set (Euc n) := Metric.maximalSeparatedSet ε K
  have hNcovfin : Ncov.Finite := Metric.finite_minimalCover
  have hNpackfin : Npack.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet hpackfin]
    exact hpackfin
  let FC : Finset (Euc n) := hNcovfin.toFinset
  let FP : Finset (Euc n) := hNpackfin.toFinset
  have hFCcard : FC.card = (Metric.coveringNumber ε K).toNat := by
    calc
      FC.card = Ncov.ncard := (Set.ncard_eq_toFinset_card Ncov hNcovfin).symm
      _ = (Metric.coveringNumber ε K).toNat := by
        rw [Set.ncard_def, Metric.encard_minimalCover hcoverfin]
  have hFPcard : FP.card = (Metric.packingNumber ε K).toNat := by
    calc
      FP.card = Npack.ncard := (Set.ncard_eq_toFinset_card Npack hNpackfin).symm
      _ = (Metric.packingNumber ε K).toNat := by
        rw [Set.ncard_def, Metric.encard_maximalSeparatedSet hpackfin]
  have hFCcover : K ⊆ ⋃ x ∈ FC, Metric.closedBall x (ε : ℝ) := by
    have hc := (Metric.isCover_minimalCover hcoverfin).subset_iUnion_closedBall
    simpa [FC, Ncov] using hc
  have hlower : volume K ≤ (FC.card : ℝ≥0∞) *
      volume (Metric.closedBall (0 : Euc n) (ε : ℝ)) :=
    volume_le_card_mul_ball hFCcover
  have hFPK : ∀ x ∈ FP, x ∈ K := by
    intro x hx
    exact Metric.maximalSeparatedSet_subset (by simpa [FP, Npack] using hx)
  have hFPsep : ∀ x ∈ FP, ∀ y ∈ FP, x ≠ y →
      2 * ((ε : ℝ) / 2) < dist x y := by
    intro x hx y hy hxy
    have hs := Metric.isSeparated_maximalSeparatedSet
      (by simpa [FP, Npack] using hx) (by simpa [FP, Npack] using hy) hxy
    change (ε : ℝ≥0∞) < edist x y at hs
    rw [edist_nndist] at hs
    have hnn : ε < nndist x y := ENNReal.coe_lt_coe.mp hs
    have hr : (ε : ℝ) < dist x y := NNReal.coe_lt_coe.mpr hnn
    convert hr using 1
    ring
  have hupper := card_mul_ball_le_volume_minkowski
    (K := K) (N := FP) (r := (ε : ℝ) / 2) hFPK hFPsep
  refine ⟨(Metric.coveringNumber ε K).toNat,
    (Metric.packingNumber ε K).toNat, ENat.coe_toNat hcoverfin,
    ENat.coe_toNat hpackfin, ?_, Metric.coveringNumber_le_packingNumber ε K, ?_⟩
  · simpa [hFCcard] using hlower
  · simpa [hFPcard] using hupper

/-- This has the full source strength for an arbitrary subset `K`. Coercion from `ℕ∞` to `ℝ≥0∞`
sends an infinite covering or packing number to `∞`, so the statement also handles unbounded
sets without a hidden finiteness hypothesis.

**Book Proposition 4.2.10.** -/
theorem proposition_4_2_10 {K : Set (Euc n)} {ε : ℝ≥0} (hε : 0 < ε) :
    volume K ≤ (Metric.coveringNumber ε K : ℝ≥0∞) *
        volume (Metric.closedBall (0 : Euc n) (ε : ℝ)) ∧
      Metric.coveringNumber ε K ≤ Metric.packingNumber ε K ∧
      (Metric.packingNumber ε K : ℝ≥0∞) *
          volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ≤
        volume (HDP.minkowskiSum K
          (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2))) := by
  have hlower : volume K ≤ (Metric.coveringNumber ε K : ℝ≥0∞) *
      volume (Metric.closedBall (0 : Euc n) (ε : ℝ)) := by
    by_cases hfin : Metric.coveringNumber ε K ≠ ⊤
    · let N : Set (Euc n) := Metric.minimalCover ε K
      have hNfin : N.Finite := Metric.finite_minimalCover
      let F : Finset (Euc n) := hNfin.toFinset
      have hFcover : K ⊆ ⋃ x ∈ F, Metric.closedBall x (ε : ℝ) := by
        have hc := (Metric.isCover_minimalCover hfin).subset_iUnion_closedBall
        simpa [F, N] using hc
      have hbound := volume_le_card_mul_ball hFcover
      have hcardENat : (F.card : ℕ∞) = Metric.coveringNumber ε K := by
        rw [← hNfin.encard_eq_coe_toFinset_card]
        exact Metric.encard_minimalCover hfin
      have hcardENN : (F.card : ℝ≥0∞) =
          (Metric.coveringNumber ε K : ℝ≥0∞) := by
        exact_mod_cast hcardENat
      simpa [hcardENN] using hbound
    · have htop : Metric.coveringNumber ε K = ⊤ := not_ne_iff.mp hfin
      have hball : volume (Metric.closedBall (0 : Euc n) (ε : ℝ)) ≠ 0 :=
        (volume_closedBall_pos (by exact_mod_cast hε)).ne'
      simp [htop, hball]
  have hupper : (Metric.packingNumber ε K : ℝ≥0∞) *
      volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ≤
      volume (HDP.minkowskiSum K
        (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2))) := by
    rw [Metric.packingNumber]
    simp only [ENat.toENNReal_iSup, ENNReal.iSup_mul]
    refine iSup_le fun C => iSup_le fun hCK => iSup_le fun hsep => ?_
    exact encard_mul_ball_le_volume_minkowski hε hCK hsep
  exact ⟨hlower, Metric.coveringNumber_le_packingNumber ε K, hupper⟩

/-- This exact Mathlib correspondence is the normalization used to simplify the corresponding
proposition into the familiar powers `(1/ε)^n` and `(1+2/ε)^n`.

**Book Corollary 4.2.11.** -/
theorem corollary_4_2_11_volume_formula (x : Euc n) (r : ℝ) :
    volume (Metric.closedBall x r) =
      (ENNReal.ofReal r) ^ n *
        ENNReal.ofReal (Real.sqrt Real.pi ^ n /
          Real.Gamma ((n : ℝ) / 2 + 1)) := by
  simpa using EuclideanSpace.volume_closedBall (Fin n) x r

omit [NeZero n] in
/-- Thickening a subset of the unit ball by a closed ball of radius `ε/2` stays inside the closed ball of radius `1+ε/2`.

**Lean implementation helper.** -/
private theorem minkowski_unitBall_subset {ε : ℝ≥0} {K : Set (Euc n)}
    (hK : K ⊆ Metric.closedBall (0 : Euc n) 1) :
    HDP.minkowskiSum K (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ⊆
      Metric.closedBall (0 : Euc n) (1 + (ε : ℝ) / 2) := by
  intro x hx
  obtain ⟨a, haK, b, hb, rfl⟩ := HDP.mem_minkowskiSum.mp hx
  have ha := hK haK
  rw [Metric.mem_closedBall, dist_zero_right] at ha hb ⊢
  exact (norm_add_le a b).trans (add_le_add ha hb)

/-- A subset of the Euclidean unit ball has covering number at radius `ε` at most `(2/ε+1)^n`.

**Lean implementation helper.** -/
private theorem coveringNumber_unit_subset_upper {ε : ℝ≥0} (hε : 0 < ε)
    {K : Set (Euc n)} (hK : K ⊆ Metric.closedBall (0 : Euc n) 1) :
    (Metric.coveringNumber ε K : ℝ≥0∞) ≤
      (((2 / ε + 1 : ℝ≥0) : ℝ≥0∞) ^ n) := by
  have hp := (proposition_4_2_10 (n := n) (K := K) hε).2.2
  have hM : volume (HDP.minkowskiSum K
        (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2))) ≤
      volume (Metric.closedBall (0 : Euc n) (1 + (ε : ℝ) / 2)) :=
    measure_mono (minkowski_unitBall_subset (n := n) (ε := ε) hK)
  have hp' : (Metric.packingNumber ε K : ℝ≥0∞) *
        volume (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ≤
      volume (Metric.closedBall (0 : Euc n) (1 + (ε : ℝ) / 2)) :=
    hp.trans hM
  let c : ℝ≥0∞ := ENNReal.ofReal
    (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have hct : c ≠ ⊤ := by simp [c]
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall] at hp'
  simp only [Fintype.card_fin] at hp'
  rw [← mul_assoc] at hp'
  change (Metric.packingNumber ε K : ℝ≥0∞) *
      ENNReal.ofReal ((ε : ℝ) / 2) ^ n * c ≤
        ENNReal.ofReal (1 + (ε : ℝ) / 2) ^ n * c at hp'
  rw [ENNReal.mul_le_mul_iff_left hc0 hct] at hp'
  have he : ENNReal.ofReal ((ε : ℝ) / 2) = ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  have hone : ENNReal.ofReal (1 + (ε : ℝ) / 2) =
      ((1 + ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  rw [he, hone] at hp'
  have hden0 : (((ε / 2 : ℝ≥0) : ℝ≥0∞) ^ n) ≠ 0 := by
    positivity
  have hdent : (((ε / 2 : ℝ≥0) : ℝ≥0∞) ^ n) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hpack : (Metric.packingNumber ε K : ℝ≥0∞) ≤
      (((1 + ε / 2 : ℝ≥0) : ℝ≥0∞) ^ n) /
        (((ε / 2 : ℝ≥0) : ℝ≥0∞) ^ n) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)).2 hp'
  have hratio : (((1 + ε / 2 : ℝ≥0) : ℝ≥0∞) ^ n) /
        (((ε / 2 : ℝ≥0) : ℝ≥0∞) ^ n) =
      (((2 / ε + 1 : ℝ≥0) : ℝ≥0∞) ^ n) := by
    have hbase : (1 + ε / 2 : ℝ≥0) / (ε / 2) = 2 / ε + 1 := by
      apply NNReal.eq
      simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
      have he0 : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
      field_simp
    have hdenNN : (ε / 2 : ℝ≥0) ≠ 0 := div_ne_zero hε.ne' (by norm_num)
    have hdenPow : (ε / 2 : ℝ≥0) ^ n ≠ 0 := pow_ne_zero n hdenNN
    rw [← ENNReal.coe_pow, ← ENNReal.coe_pow,
      ← ENNReal.coe_div hdenPow]
    norm_cast
    rw [← div_pow, hbase]
  rw [hratio] at hpack
  exact (show (Metric.coveringNumber ε K : ℝ≥0∞) ≤
      (Metric.packingNumber ε K : ℝ≥0∞) by exact_mod_cast
        Metric.coveringNumber_le_packingNumber ε K).trans hpack

/-- The inequalities are stated in `ℝ≥0∞`, preserving the source values while retaining the
possibility of an infinite covering number.

**Book Corollary 4.2.11.** -/
theorem corollary_4_2_11 {ε : ℝ≥0} (hε : 0 < ε) :
    (((1 / ε : ℝ≥0) : ℝ≥0∞) ^ n) ≤
        (Metric.coveringNumber ε (Metric.closedBall (0 : Euc n) 1) : ℝ≥0∞) ∧
      (Metric.coveringNumber ε (Metric.closedBall (0 : Euc n) 1) : ℝ≥0∞) ≤
        (((2 / ε + 1 : ℝ≥0) : ℝ≥0∞) ^ n) ∧
      (Metric.coveringNumber ε (Metric.sphere (0 : Euc n) 1) : ℝ≥0∞) ≤
        (((2 / ε + 1 : ℝ≥0) : ℝ≥0∞) ^ n) := by
  have hl := (proposition_4_2_10 (n := n)
    (K := Metric.closedBall (0 : Euc n) 1) hε).1
  let c : ℝ≥0∞ := ENNReal.ofReal
    (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have hct : c ≠ ⊤ := by simp [c]
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall] at hl
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul] at hl
  rw [← mul_assoc] at hl
  have hl' : (1 : ℝ≥0∞) * c ≤
      ((Metric.coveringNumber ε (Metric.closedBall (0 : Euc n) 1) : ℝ≥0∞) *
        ENNReal.ofReal (ε : ℝ) ^ n) * c := by
    simpa [c] using hl
  rw [ENNReal.mul_le_mul_iff_left hc0 hct] at hl'
  have he : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  rw [he] at hl'
  have he0 : ((ε : ℝ≥0∞) ^ n) ≠ 0 := by positivity
  have het : ((ε : ℝ≥0∞) ^ n) ≠ ⊤ := by simp
  have hlower : (((1 / ε : ℝ≥0) : ℝ≥0∞) ^ n) ≤
      (Metric.coveringNumber ε (Metric.closedBall (0 : Euc n) 1) : ℝ≥0∞) := by
    have : (1 : ℝ≥0∞) / ((ε : ℝ≥0∞) ^ n) ≤
        (Metric.coveringNumber ε (Metric.closedBall (0 : Euc n) 1) : ℝ≥0∞) :=
      (ENNReal.div_le_iff he0 het).2 (by simpa [mul_comm] using hl')
    have hinv : (((1 / ε : ℝ≥0) : ℝ≥0∞) ^ n) =
        (1 : ℝ≥0∞) / ((ε : ℝ≥0∞) ^ n) := by
      have hεpow : ε ^ n ≠ 0 := pow_ne_zero n hε.ne'
      calc
        _ = (((((1 : ℝ≥0) ^ n) / (ε ^ n) : ℝ≥0)) : ℝ≥0∞) := by
          norm_cast
          norm_num [div_pow]
        _ = ((1 : ℝ≥0) ^ n : ℝ≥0∞) / (ε ^ n : ℝ≥0∞) :=
          ENNReal.coe_div hεpow
        _ = _ := by simp
    rw [hinv]
    exact this
  refine ⟨hlower,
    coveringNumber_unit_subset_upper hε (K := Metric.closedBall (0 : Euc n) 1) (by simp), ?_⟩
  exact coveringNumber_unit_subset_upper hε
    (K := Metric.sphere (0 : Euc n) 1) Metric.sphere_subset_closedBall

noncomputable section

variable {n : ℕ} [NeZero n]
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The inward-shifted center at margin `r` inside radius `R` is `(1 - r / R) • y`.

**Lean implementation helper.** -/
def inwardCenter (R r : ℝ) (y : E n) : E n :=
  (1 - r / R) • y

/-- The inner cube around `sqrt n • inwardCenter R r y` consists of points whose every coordinate differs from that center by at most `r`.

**Lean implementation helper.** -/
def innerCube (R r : ℝ) (y : E n) : Set (E n) :=
  {z | ∀ i, |z i - Real.sqrt n * (inwardCenter R r y) i| ≤ r}

omit [NeZero n] in
/-- Identifies inner cube with preimage icc.

**Lean implementation helper.** -/
lemma innerCube_eq_preimage_Icc (R r : ℝ) (y : E n) :
    innerCube R r y = WithLp.ofLp ⁻¹'
      Set.Icc (fun i : Fin n => Real.sqrt n * (inwardCenter R r y) i - r)
        (fun i : Fin n => Real.sqrt n * (inwardCenter R r y) i + r) := by
  ext z
  simp only [innerCube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc,
    Pi.le_def]
  constructor
  · intro hz
    constructor
    · intro i
      have := hz i
      rw [abs_le] at this
      linarith
    · intro i
      have := hz i
      rw [abs_le] at this
      linarith
  · intro hz i
    rw [abs_le]
    constructor <;> have := hz.1 i <;> have := hz.2 i <;> linarith

omit [NeZero n] in
/-- Establishes measurability of the set inner cube.

**Lean implementation helper.** -/
lemma measurableSet_innerCube (R r : ℝ) (y : E n) :
    MeasurableSet (innerCube R r y) := by
  rw [innerCube_eq_preimage_Icc]
  exact measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin n)).measurable

omit [NeZero n] in
/-- An axis-aligned `n`-dimensional cube of half-side length `r` has volume `(2r)^n`.

**Lean implementation helper.** -/
lemma volume_innerCube (R r : ℝ) (y : E n) :
    volume (innerCube R r y) = ENNReal.ofReal (2 * r) ^ n := by
  rw [innerCube_eq_preimage_Icc,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  have hterm :
      (fun i : Fin n => ENNReal.ofReal
        (Real.sqrt n * (inwardCenter R r y) i + r -
          (Real.sqrt n * (inwardCenter R r y) i - r))) =
        fun _i : Fin n => ENNReal.ofReal (2 * r) := by
    funext i
    congr 1
    ring
  rw [hterm, Finset.prod_const, Finset.card_fin]

omit [NeZero n] in
/-- Every point `z` in `innerCube R r y` satisfies `‖z - sqrt n • inwardCenter R r y‖ ≤ sqrt n * r`.

**Lean implementation helper.** -/
lemma norm_sub_center_le {R r : ℝ} (hr : 0 ≤ r) {y z : E n}
    (hz : z ∈ innerCube R r y) :
    ‖z - Real.sqrt n • inwardCenter R r y‖ ≤ Real.sqrt n * r := by
  have hi : ∀ i : Fin n,
      |(z - Real.sqrt n • inwardCenter R r y) i| ≤ r := by
    intro i
    simpa [innerCube] using hz i
  have hsum : ∑ i : Fin n,
      ((z - Real.sqrt n • inwardCenter R r y) i) ^ 2 ≤
        ∑ _i : Fin n, r ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi_mem
    have hsqi := (sq_le_sq₀ (abs_nonneg _) hr).2 (hi i)
    simpa [sq_abs] using hsqi
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, r ^ 2 := hsum
    _ = (Real.sqrt n * r) ^ 2 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- A point in the inner cube, after normalization by `√n`, lies within distance `r` of the inward-shifted center.

**Lean implementation helper.** -/
lemma normalized_close {R r : ℝ} (hr : 0 ≤ r) {y z : E n}
    (hz : z ∈ innerCube R r y) :
    dist ((Real.sqrt n)⁻¹ • z) (inwardCenter R r y) ≤ r := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have heq : (Real.sqrt n)⁻¹ • z - inwardCenter R r y =
      (Real.sqrt n)⁻¹ • (z - Real.sqrt n • inwardCenter R r y) := by
    rw [smul_sub, inv_smul_smul₀ hs]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (Real.sqrt n)⁻¹ * ‖z - Real.sqrt n • inwardCenter R r y‖ ≤
        (Real.sqrt n)⁻¹ * (Real.sqrt n * r) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_center_le hr hz) (by positivity)
    _ = r := by field_simp

omit [NeZero n] in
/-- The inward-shifted center has norm at most `R-r`.

**Lean implementation helper.** -/
lemma inwardCenter_norm_le {R r : ℝ} (hR : 0 < R)
    (hrR : r ≤ R) {y : E n} (hy : ‖y‖ ≤ R) :
    ‖inwardCenter R r y‖ ≤ R - r := by
  have hfac : 0 ≤ 1 - r / R := by
    rw [sub_nonneg, div_le_one hR]
    exact hrR
  rw [inwardCenter, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac]
  calc
    (1 - r / R) * ‖y‖ ≤ (1 - r / R) * R :=
      mul_le_mul_of_nonneg_left hy hfac
    _ = R - r := by field_simp

omit [NeZero n] in
/-- Moving a center inward by radius `r` changes it by at most `r`.

**Lean implementation helper.** -/
lemma dist_inwardCenter_le {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    {y : E n} (hy : ‖y‖ ≤ R) :
    dist y (inwardCenter R r y) ≤ r := by
  rw [dist_eq_norm, inwardCenter]
  have heq : y - (1 - r / R) • y = (r / R) • y := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hR.le)]
  calc
    r / R * ‖y‖ ≤ r / R * R :=
      mul_le_mul_of_nonneg_left hy (div_nonneg hr hR.le)
    _ = r := by field_simp

/-- A normalized point in the inner cube lies in the radius-`R` ball and within distance `2r` of the original center.

**Lean implementation helper.** -/
lemma normalized_innerCube_geometry {R r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) {y z : E n}
    (hy : y ∈ Metric.closedBall (0 : E n) R)
    (hz : z ∈ innerCube R r y) :
    (Real.sqrt n)⁻¹ • z ∈ Metric.closedBall (0 : E n) R ∧
      dist ((Real.sqrt n)⁻¹ • z) y ≤ 2 * r := by
  have hy' : ‖y‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hc := inwardCenter_norm_le hR hrR hy'
  have hxc := normalized_close hr hz
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖(Real.sqrt n)⁻¹ • z‖ ≤
          dist ((Real.sqrt n)⁻¹ • z) (inwardCenter R r y) +
            ‖inwardCenter R r y‖ := by
        simpa [dist_eq_norm] using
          norm_add_le ((Real.sqrt n)⁻¹ • z - inwardCenter R r y)
            (inwardCenter R r y)
      _ ≤ r + (R - r) := add_le_add hxc hc
      _ = R := by ring
  · calc
      dist ((Real.sqrt n)⁻¹ • z) y ≤
          dist ((Real.sqrt n)⁻¹ • z) (inwardCenter R r y) +
            dist (inwardCenter R r y) y := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hxc (by
        rw [dist_comm]
        exact dist_inwardCenter_le hR hr hy')
      _ = 2 * r := by ring

omit [NeZero n] in
/-- Bounds norm by sqrt mul radius.

**Lean implementation helper.** -/
lemma norm_le_sqrt_mul_radius {R r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) {y z : E n}
    (hy : y ∈ Metric.closedBall (0 : E n) R)
    (hz : z ∈ innerCube R r y) :
    ‖z‖ ≤ Real.sqrt n * R := by
  have hy' : ‖y‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hc := inwardCenter_norm_le hR hrR hy'
  calc
    ‖z‖ ≤ ‖z - Real.sqrt n • inwardCenter R r y‖ +
        ‖Real.sqrt n • inwardCenter R r y‖ := by
      simpa using norm_add_le
        (z - Real.sqrt n • inwardCenter R r y)
        (Real.sqrt n • inwardCenter R r y)
    _ ≤ Real.sqrt n * r + Real.sqrt n * (R - r) := by
      gcongr
      · exact norm_sub_center_le hr hz
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
    _ = Real.sqrt n * R := by ring

/-- The Gaussian density floor in dimension `n` and radius `R` is `gaussianRadialNormalizer(E n)⁻¹ * exp (-(1/2) * n * R²)`.

**Lean implementation helper.** -/
def gaussianCubeDensityFloor (n : ℕ) (R : ℝ) : ℝ :=
  (HDP.gaussianRadialNormalizer (E n))⁻¹ *
    Real.exp (-(1 / 2 : ℝ) * n * R ^ 2)

omit [NeZero n] in
/-- Shows that gaussian cube density floor is positive.

**Lean implementation helper.** -/
lemma gaussianCubeDensityFloor_pos (R : ℝ) :
    0 < gaussianCubeDensityFloor n R := by
  dsimp [gaussianCubeDensityFloor]
  exact mul_pos (inv_pos.mpr (HDP.gaussianRadialNormalizer_pos (E n)))
    (Real.exp_pos _)

/-- Throughout the inner cube, Gaussian density is bounded below by the explicit radial density floor.

**Lean implementation helper.** -/
lemma gaussianRadialDensity_lower_on_innerCube {R r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) {y z : E n}
    (hy : y ∈ Metric.closedBall (0 : E n) R)
    (hz : z ∈ innerCube R r y) :
    ENNReal.ofReal (gaussianCubeDensityFloor n R) ≤
      (HDP.gaussianRadialDensity (E n) z : ℝ≥0∞) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hnorm := norm_le_sqrt_mul_radius hR hr hrR hy hz
  have hsq : ‖z‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
    calc
      ‖z‖ ^ 2 ≤ (Real.sqrt n * R) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hR.le)).2 hnorm
      _ = (n : ℝ) * R ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hexp : Real.exp (-(1 / 2 : ℝ) * n * R ^ 2) ≤
      Real.exp (-(1 / 2 : ℝ) * ‖z‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hreal : gaussianCubeDensityFloor n R ≤
      (HDP.gaussianRadialDensity (E n) z : ℝ) := by
    rw [HDP.coe_gaussianRadialDensity]
    exact mul_le_mul_of_nonneg_left hexp (by
      exact inv_nonneg.mpr (HDP.gaussianRadialNormalizer_pos (E n)).le)
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa using h

/-- The Gaussian mass of the inner cube is at least its volume times the explicit density floor.

**Lean implementation helper.** -/
lemma stdGaussian_innerCube_lower {R r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) {y : E n}
    (hy : y ∈ Metric.closedBall (0 : E n) R) :
    ENNReal.ofReal (gaussianCubeDensityFloor n R) *
        ENNReal.ofReal (2 * r) ^ n ≤
      stdGaussian (E n) (innerCube R r y) := by
  rw [← volume_innerCube R r y]
  rw [← HDP.gaussianRadialMeasure_eq_stdGaussian,
    HDP.gaussianRadialMeasure,
    withDensity_apply _ (measurableSet_innerCube R r y)]
  calc
    ENNReal.ofReal (gaussianCubeDensityFloor n R) * volume (innerCube R r y) =
        ∫⁻ _z in innerCube R r y,
          ENNReal.ofReal (gaussianCubeDensityFloor n R) ∂volume := by
      simp
    _ ≤ ∫⁻ z in innerCube R r y,
          (HDP.gaussianRadialDensity (E n) z : ℝ≥0∞) ∂volume := by
      apply setLIntegral_mono' (measurableSet_innerCube R r y)
      intro z hz
      exact gaussianRadialDensity_lower_on_innerCube hR hr hrR hy hz

omit [NeZero n] in
/-- The Gaussian radial normalizer in `n`-dimensional Euclidean space is `(√(2π))^n`.

**Lean implementation helper.** -/
lemma gaussianRadialNormalizer_euc :
    HDP.gaussianRadialNormalizer (E n) =
      Real.sqrt (2 * Real.pi) ^ n := by
  rw [HDP.gaussianRadialNormalizer, finrank_euclideanSpace]
  have hbase : 0 ≤ 2 * Real.pi := by positivity
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hbase]
  congr 2
  norm_num
  ring

/-- The one-dimensional base for the Gaussian cube-mass bound is `2r / sqrt(2π) * exp (-(1/2)R²)`.

**Lean implementation helper.** -/
def gaussianCubeBase (R r : ℝ) : ℝ :=
  2 * r * (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * R ^ 2)

/-- Shows that gaussian cube base is positive.

**Lean implementation helper.** -/
lemma gaussianCubeBase_pos (R : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < gaussianCubeBase R r := by
  dsimp [gaussianCubeBase]
  positivity

omit [NeZero n] in
/-- Identifies gaussian cube mass with base pow.

**Lean implementation helper.** -/
lemma gaussianCube_mass_eq_base_pow (R : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (gaussianCubeDensityFloor n R) *
        ENNReal.ofReal (2 * r) ^ n =
      ENNReal.ofReal (gaussianCubeBase R r) ^ n := by
  have hb : 0 ≤ gaussianCubeBase R r := by
    dsimp [gaussianCubeBase]
    positivity
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * r),
    ← ENNReal.ofReal_mul (gaussianCubeDensityFloor_pos (n := n) R).le,
    ← ENNReal.ofReal_pow hb]
  congr 1
  rw [gaussianCubeDensityFloor, gaussianRadialNormalizer_euc]
  rw [← inv_pow]
  rw [show -(1 / 2 : ℝ) * n * R ^ 2 =
      (n : ℝ) * (-(1 / 2 : ℝ) * R ^ 2) by ring,
    Real.exp_nat_mul]
  rw [gaussianCubeBase, mul_pow, mul_pow]
  ring

omit [NeZero n] in
/-- For an independent Gaussian cloud of `N` points, the probability that every point misses `B` is the `N`th power of the complement mass.

**Lean implementation helper.** -/
lemma gaussianCloud_all_miss (N : ℕ) {B : Set (E n)} :
    HDP.Chapter3.gaussianCloudMeasure N n
        {g | ∀ i, g i ∉ B} =
      (stdGaussian (E n) Bᶜ) ^ N := by
  have hevent : {g : HDP.Chapter3.GaussianCloud N n | ∀ i, g i ∉ B} =
      Set.univ.pi (fun _i : Fin N => Bᶜ) := by
    ext g
    simp
  rw [hevent, HDP.Chapter3.gaussianCloudMeasure, Measure.pi_pi]
  simp

omit [NeZero n] in
/-- If a set has Gaussian mass at least `p`, an `N`-point Gaussian cloud misses it entirely with probability at most `(1-p)^N`.

**Lean implementation helper.** -/
lemma gaussianCloud_all_miss_le (N : ℕ) {B : Set (E n)}
    (hB : MeasurableSet B) {p : ℝ≥0∞}
    (hp : p ≤ stdGaussian (E n) B) :
    HDP.Chapter3.gaussianCloudMeasure N n
        {g | ∀ i, g i ∉ B} ≤ (1 - p) ^ N := by
  rw [gaussianCloud_all_miss N]
  gcongr
  rw [measure_compl hB (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left hp 1

/-- Bounds ennreal one sub pow by exp.

**Lean implementation helper.** -/
lemma ennreal_one_sub_pow_le_exp (N : ℕ) {p : ℝ≥0∞} (hp : p ≤ 1) :
    (1 - p) ^ N ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) * p.toReal)) := by
  have hp_top : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hone_sub_top : 1 - p ≠ ⊤ := by simp
  have hpR : p.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hp_top ENNReal.one_ne_top).mpr hp
  apply (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hone_sub_top) (by simp)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top, ENNReal.toReal_one]
  calc
    (1 - p.toReal) ^ N ≤ Real.exp (-p.toReal) ^ N := by
      exact pow_le_pow_left₀ (sub_nonneg.mpr hpR)
        (Real.one_sub_le_exp_neg p.toReal) N
    _ = Real.exp (-(N : ℝ) * p.toReal) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- For `R, ε > 0`, the radius-`R` ball has an `ε/2`-net of centers in the ball with cardinality at most `(2 / η + 1)^n`, where `η = ε / (2R)`.

**Lean implementation helper.** -/
lemma exists_scaled_ball_net {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    let η : ℝ≥0 := Real.toNNReal (ε / (2 * R))
    ∃ F : Finset (E n),
      (∀ y ∈ F, y ∈ Metric.closedBall (0 : E n) R) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) R,
        ∃ y ∈ F, dist x y ≤ ε / 2) ∧
      (F.card : ℝ≥0∞) ≤ (((2 / η + 1 : ℝ≥0) : ℝ≥0∞) ^ n) := by
  dsimp only
  let η : ℝ≥0 := Real.toNNReal (ε / (2 * R))
  have hηr : (η : ℝ) = ε / (2 * R) := by
    dsimp [η]
    rw [max_eq_left]
    positivity
  have hη : 0 < η := by
    rw [← NNReal.coe_pos, hηr]
    positivity
  have hbound := (corollary_4_2_11 (n := n) hη).2.1
  have hbound_top : (((2 / η + 1 : ℝ≥0) : ℝ≥0∞) ^ n) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hfin : Metric.coveringNumber η
      (Metric.closedBall (0 : E n) 1) ≠ ⊤ := by
    intro hc
    rw [hc] at hbound
    exact hbound_top (top_unique hbound)
  let S : Set (E n) := Metric.minimalCover η (Metric.closedBall (0 : E n) 1)
  have hSfin : S.Finite := Metric.finite_minimalCover
  let FS : Finset (E n) := hSfin.toFinset
  let F : Finset (E n) := FS.image (fun z => R • z)
  have hcardS : (FS.card : ℝ≥0∞) =
      (Metric.coveringNumber η (Metric.closedBall (0 : E n) 1) : ℝ≥0∞) := by
    have hcardENat : (FS.card : ℕ∞) =
        Metric.coveringNumber η (Metric.closedBall (0 : E n) 1) := by
      rw [← hSfin.encard_eq_coe_toFinset_card]
      exact Metric.encard_minimalCover hfin
    exact_mod_cast hcardENat
  refine ⟨F, ?_, ?_, ?_⟩
  · intro y hy
    simp only [F, Finset.mem_image] at hy
    obtain ⟨z, hzFS, rfl⟩ := hy
    have hzS : z ∈ S := by simpa [FS] using hzFS
    have hzball := Metric.minimalCover_subset hzS
    rw [Metric.mem_closedBall, dist_zero_right] at hzball ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left hzball hR.le).trans_eq (mul_one R)
  · intro x hx
    let u : E n := R⁻¹ • x
    have hu : u ∈ Metric.closedBall (0 : E n) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖R⁻¹ • x‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      have hx' : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      calc
        R⁻¹ * ‖x‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left hx' (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    obtain ⟨z, hzS, huz⟩ := Metric.isCover_minimalCover hfin hu
    refine ⟨R • z, ?_, ?_⟩
    · simp only [F, Finset.mem_image]
      exact ⟨z, by simpa [FS, S] using hzS, rfl⟩
    · have hdist : dist u z ≤ (η : ℝ) := by
        change edist u z ≤ (η : ℝ≥0∞) at huz
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at huz
        exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg η)).mp huz
      have hxu : R • u = x := by
        change R • (R⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      rw [← hxu, dist_smul₀]
      rw [Real.norm_eq_abs, abs_of_pos hR]
      rw [hηr] at hdist
      calc
        R * dist u z ≤ R * (ε / (2 * R)) :=
          mul_le_mul_of_nonneg_left hdist hR.le
        _ = ε / 2 := by field_simp
  · calc
      (F.card : ℝ≥0∞) ≤ (FS.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_image_le
      _ = (Metric.coveringNumber η
          (Metric.closedBall (0 : E n) 1) : ℝ≥0∞) := hcardS
      _ ≤ (((2 / η + 1 : ℝ≥0) : ℝ≥0∞) ^ n) := hbound

/-- Bounds exp neg by inv.

**Lean implementation helper.** -/
lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg]
  have hxexp : x ≤ Real.exp x :=
    le_trans (by linarith) (Real.add_one_le_exp x)
  exact (inv_le_inv₀ (Real.exp_pos x) hx).2 hxexp

/-- The random-net sampling exponent is `1 + log B - log a`.

**Lean implementation helper.** -/
def randomNetExponent (B a : ℝ) : ℝ :=
  1 + Real.log B - Real.log a

/-- The exponential of the random-net exponent expands as `e^n B^n/a^n`.

**Lean implementation helper.** -/
lemma exp_randomNetExponent_mul (n : ℕ) {B a : ℝ}
    (hB : 0 < B) (ha : 0 < a) :
    Real.exp (randomNetExponent B a * n) =
      Real.exp n * B ^ n / a ^ n := by
  rw [randomNetExponent]
  rw [show (1 + Real.log B - Real.log a) * (n : ℝ) =
      (n : ℝ) + (n : ℝ) * Real.log B - (n : ℝ) * Real.log a by ring]
  rw [Real.exp_sub, Real.exp_add, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_log hB, Real.exp_log ha]

/-- The numerical sampling condition makes the exponential union bound at most `e^{-n}`.

**Lean implementation helper.** -/
lemma exponential_union_bound {n N : ℕ}
    {B a : ℝ} (hB : 0 < B) (ha : 0 < a)
    (hN : Real.exp (randomNetExponent B a * n) ≤ N) :
    B ^ n * Real.exp (-((N : ℝ) * a ^ n)) ≤ Real.exp (-(n : ℝ)) := by
  have hBn : 0 < B ^ n := pow_pos hB n
  have han : 0 < a ^ n := pow_pos ha n
  have hNpos : 0 < N := by
    have : 0 < Real.exp (randomNetExponent B a * n) := Real.exp_pos _
    exact_mod_cast lt_of_lt_of_le this hN
  have hx : Real.exp n * B ^ n ≤ (N : ℝ) * a ^ n := by
    have hN' := hN
    rw [exp_randomNetExponent_mul n hB ha] at hN'
    exact (div_le_iff₀ han).1 hN'
  have hxpos : 0 < (N : ℝ) * a ^ n := mul_pos (by exact_mod_cast hNpos) han
  calc
    B ^ n * Real.exp (-((N : ℝ) * a ^ n)) ≤
        B ^ n * ((N : ℝ) * a ^ n)⁻¹ :=
      mul_le_mul_of_nonneg_left (exp_neg_le_inv hxpos) hBn.le
    _ = B ^ n / ((N : ℝ) * a ^ n) := by rw [div_eq_mul_inv]
    _ ≤ Real.exp (-(n : ℝ)) := by
      apply (div_le_iff₀ hxpos).2
      calc
        B ^ n = Real.exp (-(n : ℝ)) * (Real.exp n * B ^ n) := by
          symm
          calc
            Real.exp (-(n : ℝ)) * (Real.exp n * B ^ n) =
                (Real.exp (-(n : ℝ)) * Real.exp n) * B ^ n := by ring
            _ = B ^ n := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp (-(n : ℝ)) * ((N : ℝ) * a ^ n) :=
          mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le

/-- The Gaussian-net failure event is the union, over centers `y ∈ F`, of clouds whose points all miss `innerCube R r y`.

**Lean implementation helper.** -/
def gaussianNetFailure (N : ℕ) (F : Finset (E n)) (R r : ℝ) :
    Set (HDP.Chapter3.GaussianCloud N n) :=
  ⋃ y ∈ F, {g | ∀ i, g i ∉ innerCube R r y}

omit [NeZero n] in
/-- Establishes measurability of the set gaussian cloud all miss.

**Lean implementation helper.** -/
lemma measurableSet_gaussianCloud_all_miss (N : ℕ) {B : Set (E n)}
    (hB : MeasurableSet B) :
    MeasurableSet {g : HDP.Chapter3.GaussianCloud N n | ∀ i, g i ∉ B} := by
  have hevent : {g : HDP.Chapter3.GaussianCloud N n | ∀ i, g i ∉ B} =
      Set.univ.pi (fun _i : Fin N => Bᶜ) := by
    ext g
    simp
  rw [hevent]
  exact MeasurableSet.pi countable_univ fun _ _ => hB.compl

omit [NeZero n] in
/-- Establishes measurability of the set gaussian net failure.

**Lean implementation helper.** -/
lemma measurableSet_gaussianNetFailure (N : ℕ) (F : Finset (E n))
    (R r : ℝ) : MeasurableSet (gaussianNetFailure N F R r) := by
  apply Finset.measurableSet_biUnion F
  intro y hy
  exact measurableSet_gaussianCloud_all_miss N (measurableSet_innerCube R r y)

omit [NeZero n] in
/-- The probability that a Gaussian cloud misses one of the prescribed neighborhoods is at most the number of centers times `(1-p)^N`.

**Lean implementation helper.** -/
lemma gaussianNetFailure_measure_le (N : ℕ) (F : Finset (E n))
    {R r : ℝ} {p : ℝ≥0∞}
    (hp : ∀ y ∈ F, p ≤ stdGaussian (E n) (innerCube R r y)) :
    HDP.Chapter3.gaussianCloudMeasure N n (gaussianNetFailure N F R r) ≤
      (F.card : ℝ≥0∞) * (1 - p) ^ N := by
  calc
    HDP.Chapter3.gaussianCloudMeasure N n (gaussianNetFailure N F R r) ≤
        ∑ y ∈ F, HDP.Chapter3.gaussianCloudMeasure N n
          {g | ∀ i, g i ∉ innerCube R r y} := by
      exact measure_biUnion_finset_le F _
    _ ≤ ∑ _y ∈ F, (1 - p) ^ N := by
      apply Finset.sum_le_sum
      intro y hy
      exact gaussianCloud_all_miss_le N (measurableSet_innerCube R r y) (hp y hy)
    _ = (F.card : ℝ≥0∞) * (1 - p) ^ N := by
      simp

/-- The normalized Gaussian cloud in the radius-`R` ball is the range of `i ↦ (sqrt n)⁻¹ • g i`, intersected with that ball.

**Lean implementation helper.** -/
def normalizedGaussianCloudInBall (n N : ℕ) (R : ℝ)
    (g : HDP.Chapter3.GaussianCloud N n) : Set (E n) :=
  Set.range (fun i => (Real.sqrt n)⁻¹ • g i) ∩
    Metric.closedBall (0 : E n) R

/-- The auxiliary random-net radius is `min (ε / 4) (R / 2)`.

**Lean implementation helper.** -/
def randomNetRadius (R ε : ℝ) : ℝ :=
  min (ε / 4) (R / 2)

/-- The nonnegative cover scale is `Real.toNNReal (ε / (2R))`.

**Lean implementation helper.** -/
def randomNetCoverScale (R ε : ℝ) : ℝ≥0 :=
  Real.toNNReal (ε / (2 * R))

/-- The cover-cardinality base is `2 / randomNetCoverScale R ε + 1`.

**Lean implementation helper.** -/
def randomNetCoverBase (R ε : ℝ) : ℝ :=
  (2 / randomNetCoverScale R ε + 1 : ℝ≥0)

/-- The sampling exponent for Exercise 4.39 is the maximum of `1` and the random-net exponent built from the cover base and Gaussian cube base.

**Lean implementation helper.** -/
def exercise439Exponent (R ε : ℝ) : ℝ :=
  max 1 (randomNetExponent (randomNetCoverBase R ε)
    (gaussianCubeBase R (randomNetRadius R ε)))

/-- Shows that exercise439 exponent is positive.

**Lean implementation helper.** -/
lemma exercise439Exponent_pos (R ε : ℝ) : 0 < exercise439Exponent R ε := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The coordinate cubes are shifted inward before the product/union argument, so the sampled
centers used by the net really lie in the intersected ball.

**Book Exercise 4.39.** -/
theorem exercise_4_39_fixed {n N : ℕ} [NeZero n]
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hN : Real.exp (exercise439Exponent R ε * n) ≤ N) :
    1 - ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
      HDP.Chapter3.gaussianCloudMeasure N n
        {g | HDP.IsEpsilonNet (Real.toNNReal ε)
          (Metric.closedBall (0 : E n) R)
          (normalizedGaussianCloudInBall n N R g)} := by
  let r : ℝ := randomNetRadius R ε
  let η : ℝ≥0 := randomNetCoverScale R ε
  let B : ℝ := randomNetCoverBase R ε
  let a : ℝ := gaussianCubeBase R r
  let p : ℝ≥0∞ := ENNReal.ofReal a ^ n
  have hn : 0 < n := Nat.pos_of_neZero n
  have hr : 0 < r := by
    dsimp [r, randomNetRadius]
    exact lt_min (by positivity) (by positivity)
  have hrR : r ≤ R := by
    dsimp [r, randomNetRadius]
    exact (min_le_right _ _).trans (by linarith)
  have htwo_r : 2 * r ≤ ε / 2 := by
    dsimp [r, randomNetRadius]
    nlinarith [min_le_left (ε / 4) (R / 2)]
  have hη : η = Real.toNNReal (ε / (2 * R)) := rfl
  have hB : 0 < B := by
    dsimp [B, randomNetCoverBase]
    exact_mod_cast (by positivity : (0 : ℝ≥0) < 2 / randomNetCoverScale R ε + 1)
  have ha : 0 < a := gaussianCubeBase_pos R hr
  obtain ⟨F, hFsub, hFcover, hFcard⟩ :=
    exists_scaled_ball_net (n := n) hR hε
  have hFcard' : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal B ^ n := by
    have hBcoe : ENNReal.ofReal B =
        (((2 / randomNetCoverScale R ε + 1 : ℝ≥0) : ℝ≥0∞)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hB.le]
      rfl
    rw [hBcoe]
    simpa [η, randomNetCoverScale] using hFcard
  have hp_hit : ∀ y ∈ F, p ≤ stdGaussian (E n) (innerCube R r y) := by
    intro y hy
    have hsmall := stdGaussian_innerCube_lower (n := n) hR hr.le hrR (hFsub y hy)
    rw [gaussianCube_mass_eq_base_pow R hr.le] at hsmall
    simpa [p, a] using hsmall
  have hp_one : p ≤ 1 := by
    obtain ⟨y, hy, _⟩ := hFcover (0 : E n) (by
      simp [Metric.mem_closedBall, hR.le])
    exact (hp_hit y hy).trans ((measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  have hp_real : p.toReal = a ^ n := by
    simp [p, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le]
  have hbaseN : Real.exp (randomNetExponent B a * n) ≤ N := by
    have hle : randomNetExponent B a ≤ exercise439Exponent R ε := by
      dsimp [exercise439Exponent, B, a, r]
      exact le_max_right _ _
    exact (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg n))).trans hN
  have hfailure : HDP.Chapter3.gaussianCloudMeasure N n
      (gaussianNetFailure N F R r) ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    calc
      HDP.Chapter3.gaussianCloudMeasure N n (gaussianNetFailure N F R r) ≤
          (F.card : ℝ≥0∞) * (1 - p) ^ N :=
        gaussianNetFailure_measure_le N F hp_hit
      _ ≤ ENNReal.ofReal B ^ n *
          ENNReal.ofReal (Real.exp (-(N : ℝ) * p.toReal)) :=
        mul_le_mul' hFcard' (ennreal_one_sub_pow_le_exp N hp_one)
      _ = ENNReal.ofReal
          (B ^ n * Real.exp (-((N : ℝ) * a ^ n))) := by
        rw [hp_real]
        rw [← ENNReal.ofReal_pow hB.le,
          ← ENNReal.ofReal_mul (pow_nonneg hB.le n)]
        congr 1
        congr 2
        ring
      _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ))) :=
        ENNReal.ofReal_le_ofReal
          (exponential_union_bound hB ha hbaseN)
  have hfailure_meas := measurableSet_gaussianNetFailure N F R r
  have hgood : (gaussianNetFailure N F R r)ᶜ ⊆
      {g | HDP.IsEpsilonNet (Real.toNNReal ε)
        (Metric.closedBall (0 : E n) R)
        (normalizedGaussianCloudInBall n N R g)} := by
    intro g hg
    constructor
    · intro z hz
      exact hz.2
    · intro x hx
      obtain ⟨y, hyF, hxy⟩ := hFcover x hx
      have hnotmiss : ¬ ∀ i, g i ∉ innerCube R r y := by
        intro hmiss
        exact hg (by
          simp only [gaussianNetFailure, Set.mem_iUnion]
          exact ⟨y, ⟨hyF, hmiss⟩⟩)
      push Not at hnotmiss
      obtain ⟨i, hi⟩ := hnotmiss
      let z : E n := (Real.sqrt n)⁻¹ • g i
      have hgeom := normalized_innerCube_geometry (n := n) hR hr.le hrR
        (hFsub y hyF) hi
      refine ⟨z, ?_, ?_⟩
      · exact ⟨⟨i, rfl⟩, hgeom.1⟩
      · have hdist : dist x z ≤ ε := by
          calc
            dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
            _ ≤ ε / 2 + 2 * r := add_le_add hxy (by
              rw [dist_comm]
              exact hgeom.2)
            _ ≤ ε / 2 + ε / 2 := add_le_add (le_refl _) htwo_r
            _ = ε := by ring
        change edist x z ≤ (Real.toNNReal ε : ℝ≥0∞)
        rw [edist_dist]
        simpa [Real.coe_toNNReal, max_eq_left hε.le] using hdist
  calc
    1 - ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
        1 - HDP.Chapter3.gaussianCloudMeasure N n
          (gaussianNetFailure N F R r) := by
      exact tsub_le_tsub_left hfailure 1
    _ = HDP.Chapter3.gaussianCloudMeasure N n
        (gaussianNetFailure N F R r)ᶜ := by
      rw [measure_compl hfailure_meas, measure_univ]
      exact measure_ne_top _ _
    _ ≤ HDP.Chapter3.gaussianCloudMeasure N n
        {g | HDP.IsEpsilonNet (Real.toNNReal ε)
          (Metric.closedBall (0 : E n) R)
          (normalizedGaussianCloudInBall n N R g)} := measure_mono hgood

/-- The constant depends only on `R` and `ε`, while the statement is uniform over the dimension
and number of independent standard Gaussian samples. The explicit proof above gives the source's
probability `1 - exp (-n)` (so the absolute constant `c` is `1`).

**Book Remark 4.2.13.** -/
theorem exercise_4_39 {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n N : ℕ, 0 < n →
      Real.exp (C * n) ≤ N →
      1 - ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
        HDP.Chapter3.gaussianCloudMeasure N n
          {g | HDP.IsEpsilonNet (Real.toNNReal ε)
            (Metric.closedBall (0 : E n) R)
            (normalizedGaussianCloudInBall n N R g)} := by
  refine ⟨exercise439Exponent R ε, exercise439Exponent_pos R ε, ?_⟩
  intro n N hn hN
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact exercise_4_39_fixed hR hε hN

end
end HDP.Chapter4

end Source_08_VolumetricCovering

/-! ## Material formerly in `09_HammingCube.lean` -/

section Source_09_HammingCube

/-!
# Chapter 4, Section 4.2: the Hamming cube
-/

open Set
open scoped ENNReal NNReal BigOperators

namespace HDP.Chapter4

/-! ## Hamming balls -/

/-- The number of binary words in a Hamming ball of integer radius `m`.

**Lean implementation helper.** -/
def hammingBallVolume (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), n.choose k

/-- Shows that hamming ball volume is positive.

**Lean implementation helper.** -/
theorem hammingBallVolume_pos (n m : ℕ) : 0 < hammingBallVolume n m := by
  have hmem : 0 ∈ Finset.range (m + 1) := by simp
  have hle : n.choose 0 ≤ hammingBallVolume n m :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  simpa [hammingBallVolume] using lt_of_lt_of_le (by simp : 0 < n.choose 0) hle

/-- For a fixed binary word `x`, this equivalence sends `y` to the finite set of coordinates on which `x` and `y` differ.

**Lean implementation helper.** -/
private noncomputable def binaryWordDiffEquiv (x : HDP.BinaryWord n) :
    HDP.BinaryWord n ≃ Finset (Fin n) where
  toFun y := Finset.univ.filter fun i =>
    Hamming.ofHamming y i ≠ Hamming.ofHamming x i
  invFun S := Hamming.toHamming (fun i =>
    if i ∈ S then !(Hamming.ofHamming x i) else Hamming.ofHamming x i)
  left_inv y := by
    apply Hamming.ofHamming.injective
    funext i
    simp only [Hamming.ofHamming_toHamming, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : Hamming.ofHamming y i = Hamming.ofHamming x i
    · simp [h]
    · have hbool : Hamming.ofHamming y i = !(Hamming.ofHamming x i) := by
        cases hy : Hamming.ofHamming y i <;>
          cases hx : Hamming.ofHamming x i <;> simp_all
      simp [hbool]
  right_inv S := by
    ext i
    simp only [Hamming.ofHamming_toHamming, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S
    · have hne : !(Hamming.ofHamming x i) ≠ Hamming.ofHamming x i := by
        cases Hamming.ofHamming x i <;> simp
      simp [hi]
    · simp [hi]

/-- Computes the cardinality of diff equiv.

**Lean implementation helper.** -/
private theorem card_diff_equiv (x y : HDP.BinaryWord n) :
    (binaryWordDiffEquiv x y).card = HDP.hammingDistance x y := by
  simp only [binaryWordDiffEquiv, HDP.hammingDistance, hammingDist]
  congr 1
  ext i
  simp [ne_comm]

/-- Finite subsets of `Fin n` of size at most `m` are equivalently a choice of `k ≤ m` together with a subset of cardinality `k`.

**Lean implementation helper.** -/
private noncomputable def finsetCardLEEquiv (n m : ℕ) :
    {S : Finset (Fin n) // S.card ≤ m} ≃
      Σ k : Fin (m + 1), {S : Finset (Fin n) // S.card = k} where
  toFun S := ⟨⟨S.1.card, Nat.lt_succ_of_le S.2⟩, S.1, rfl⟩
  invFun S := ⟨S.2.1, by rw [S.2.2]; omega⟩
  left_inv _ := rfl
  right_inv S := by
    rcases S with ⟨k, S, hS⟩
    rcases k with ⟨k, hk⟩
    dsimp at hS
    subst k
    rfl

/-- Computes the cardinality of finset card le.

**Lean implementation helper.** -/
private theorem card_finset_card_le (n m : ℕ) :
    Fintype.card {S : Finset (Fin n) // S.card ≤ m} = hammingBallVolume n m := by
  rw [Fintype.card_congr (finsetCardLEEquiv n m), Fintype.card_sigma]
  simpa [hammingBallVolume] using
    (Fin.sum_univ_eq_sum_range (fun k : ℕ => n.choose k) (m + 1))

/-- A radius-`m` Hamming ball about `x` is equivalent to the finite subsets of coordinates of cardinality at most `m`.

**Lean implementation helper.** -/
private noncomputable def hammingBallEquiv (x : HDP.BinaryWord n) (m : ℕ) :
    {y : HDP.BinaryWord n // HDP.hammingDistance x y ≤ m} ≃
      {S : Finset (Fin n) // S.card ≤ m} :=
  (binaryWordDiffEquiv x).subtypeEquiv fun y => by
    rw [card_diff_equiv]

/-- Every radius-`m` ball in the binary Hamming cube has cardinality `∑_{k=0}^m choose n k`.

**Lean implementation helper.** -/
theorem card_hammingBall (x : HDP.BinaryWord n) (m : ℕ) :
    Fintype.card {y : HDP.BinaryWord n // HDP.hammingDistance x y ≤ m} =
      hammingBallVolume n m := by
  rw [Fintype.card_congr (hammingBallEquiv x m), card_finset_card_le]

/-- Expresses Hamming distance as the number of differing coordinates.

**Book Definition 4.2.14.** -/
theorem definition_4_2_14 (x y : HDP.BinaryWord n) :
    HDP.hammingDistance x y =
      (Finset.univ.filter fun i =>
        Hamming.ofHamming x i ≠ Hamming.ofHamming y i).card := by
  simp [HDP.hammingDistance, hammingDist]

/-! ## Natural-valued covering and packing numbers of the finite cube -/

/-- Shows that hamming covering is finite.

**Lean implementation helper.** -/
private theorem hamming_covering_finite (n m : ℕ) :
    Metric.coveringNumber (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n)) ≠ ⊤ :=
  (HDP.finite_covering_packing_of_finite Set.finite_univ (m : ℝ≥0)).1

/-- Shows that hamming packing is finite.

**Lean implementation helper.** -/
private theorem hamming_packing_finite (n m : ℕ) :
    Metric.packingNumber (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n)) ≠ ⊤ :=
  (HDP.finite_covering_packing_of_finite Set.finite_univ (m : ℝ≥0)).2

/-- The natural-valued Hamming covering number is the finite `toNat` value of the metric covering number of the full binary cube.

**Lean implementation helper.** -/
noncomputable def hammingCoveringNumber (n m : ℕ) : ℕ :=
  (Metric.coveringNumber (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n))).toNat

/-- The natural-valued Hamming packing number is the finite `toNat` value of the metric packing number of the full binary cube.

**Lean implementation helper.** -/
noncomputable def hammingPackingNumber (n m : ℕ) : ℕ :=
  (Metric.packingNumber (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n))).toNat

/-- The finite Hamming covering number agrees, after coercion, with the metric covering number of the binary cube.

**Lean implementation helper.** -/
@[simp]
theorem coe_hammingCoveringNumber (n m : ℕ) :
    (hammingCoveringNumber n m : ℕ∞) =
      Metric.coveringNumber (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n)) :=
  ENat.coe_toNat (hamming_covering_finite n m)

/-- The finite Hamming packing number agrees, after coercion, with the metric packing number of the binary cube.

**Lean implementation helper.** -/
@[simp]
theorem coe_hammingPackingNumber (n m : ℕ) :
    (hammingPackingNumber n m : ℕ∞) =
      Metric.packingNumber (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n)) :=
  ENat.coe_toNat (hamming_packing_finite n m)

/-- Computes the cardinality of closed ball binary word.

**Lean implementation helper.** -/
theorem card_closedBall_binaryWord (x : HDP.BinaryWord n) (m : ℕ) :
    (Metric.closedBall x (m : ℝ)).ncard = hammingBallVolume n m := by
  classical
  let e : {y : HDP.BinaryWord n // y ∈ Metric.closedBall x (m : ℝ)} ≃
      {y : HDP.BinaryWord n // HDP.hammingDistance x y ≤ m} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun y => by
      simp only [Metric.mem_closedBall, Equiv.refl_apply,
        HDP.dist_binaryWord_eq_hammingDistance, Nat.cast_le]
      rw [HDP.hammingDistance_comm y x])
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_hammingBall x m

/-- The size `2^n` of the binary cube is at most the covering number times the volume of a Hamming ball.

**Lean implementation helper.** -/
private theorem hamming_covering_lower (n m : ℕ) :
    2 ^ n ≤ hammingCoveringNumber n m * hammingBallVolume n m := by
  let C : Set (HDP.BinaryWord n) :=
    Metric.minimalCover (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n))
  have hCfin : C.Finite := Metric.finite_minimalCover
  let F : Finset (HDP.BinaryWord n) := hCfin.toFinset
  have hcover :=
    (Metric.isCover_minimalCover (hamming_covering_finite n m)).subset_iUnion_closedBall
  have hcard_union : (Set.univ : Set (HDP.BinaryWord n)).ncard ≤
      ∑ x ∈ F, (Metric.closedBall x (m : ℝ)).ncard := by
    calc
      (Set.univ : Set (HDP.BinaryWord n)).ncard ≤
          (⋃ x ∈ F, Metric.closedBall x (m : ℝ)).ncard :=
        Set.ncard_le_ncard (by simpa [F, C] using hcover)
      _ ≤ ∑ x ∈ F, (Metric.closedBall x (m : ℝ)).ncard :=
        Finset.set_ncard_biUnion_le F _
  have hFcard : F.card = hammingCoveringNumber n m := by
    rw [← ENat.coe_inj]
    rw [← hCfin.encard_eq_coe_toFinset_card, Metric.encard_minimalCover
      (hamming_covering_finite n m), ← coe_hammingCoveringNumber]
  simpa [Fintype.card_congr Hamming.ofHamming, card_closedBall_binaryWord,
    hFcard] using hcard_union

/-- The packing number times the volume of a half-radius Hamming ball is at most `2^n`.

**Lean implementation helper.** -/
private theorem hamming_packing_upper (n m : ℕ) :
    hammingPackingNumber n m * hammingBallVolume n (m / 2) ≤ 2 ^ n := by
  let C : Set (HDP.BinaryWord n) :=
    Metric.maximalSeparatedSet (m : ℝ≥0) (Set.univ : Set (HDP.BinaryWord n))
  have hCfin : C.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet (hamming_packing_finite n m)]
    exact hamming_packing_finite n m
  let F : Finset (HDP.BinaryWord n) := hCfin.toFinset
  have hdisj : Set.PairwiseDisjoint (↑F : Set (HDP.BinaryWord n))
      (fun x => Metric.closedBall x ((m / 2 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hs := Metric.isSeparated_maximalSeparatedSet
      (by simpa [F, C] using hx) (by simpa [F, C] using hy) hxy
    change ((m : ℝ≥0) : ℝ≥0∞) < edist x y at hs
    rw [edist_nndist] at hs
    have hmn : m < HDP.hammingDistance x y := by
      have hn := ENNReal.coe_lt_coe.mp hs
      rw [HDP.nndist_binaryWord_eq_hammingDistance] at hn
      exact_mod_cast hn
    have htri := HDP.hammingDistance_triangle x z y
    have hzx' : HDP.hammingDistance x z ≤ m / 2 := by
      have hr : (HDP.hammingDistance x z : ℝ) ≤ (m / 2 : ℕ) := by
        rw [← HDP.dist_binaryWord_eq_hammingDistance]
        simpa [Metric.mem_closedBall, dist_comm] using hzx
      exact_mod_cast hr
    have hzy' : HDP.hammingDistance z y ≤ m / 2 := by
      have hr : (HDP.hammingDistance z y : ℝ) ≤ (m / 2 : ℕ) := by
        rw [← HDP.dist_binaryWord_eq_hammingDistance]
        simpa [Metric.mem_closedBall] using hzy
      exact_mod_cast hr
    omega
  have hunion : (⋃ x ∈ F, Metric.closedBall x ((m / 2 : ℕ) : ℝ)) ⊆
      (Set.univ : Set (HDP.BinaryWord n)) := Set.subset_univ _
  have hcard : ∑ x ∈ F, (Metric.closedBall x ((m / 2 : ℕ) : ℝ)).ncard ≤
      (Set.univ : Set (HDP.BinaryWord n)).ncard := by
    have heq : (⋃ x ∈ F, Metric.closedBall x ((m / 2 : ℕ) : ℝ)).ncard =
        ∑ x ∈ F, (Metric.closedBall x ((m / 2 : ℕ) : ℝ)).ncard := by
      calc
        _ = ∑ᶠ x ∈ (↑F : Set (HDP.BinaryWord n)),
              (Metric.closedBall x ((m / 2 : ℕ) : ℝ)).ncard :=
          (Set.toFinite (↑F : Set (HDP.BinaryWord n))).ncard_biUnion
            (fun _ _ => Set.toFinite _) hdisj
        _ = ∑ x ∈ (Set.toFinite (↑F : Set (HDP.BinaryWord n))).toFinset,
              (Metric.closedBall x ((m / 2 : ℕ) : ℝ)).ncard :=
          finsum_mem_eq_finite_toFinset_sum _ _
        _ = ∑ x ∈ F, (Metric.closedBall x ((m / 2 : ℕ) : ℝ)).ncard := by
          apply Finset.sum_congr
          · ext x
            simp
          · simp
    rw [← heq]
    exact Set.ncard_le_ncard hunion
  have hFcard : F.card = hammingPackingNumber n m := by
    rw [← ENat.coe_inj]
    rw [← hCfin.encard_eq_coe_toFinset_card, Metric.encard_maximalSeparatedSet
      (hamming_packing_finite n m), ← coe_hammingPackingNumber]
  simpa [card_closedBall_binaryWord, hFcard,
    Fintype.card_congr Hamming.ofHamming] using hcard

/-- Covering and packing numbers of the binary Hamming cube. The rational inequalities are
exactly the three source bounds, with no truncating natural-number division.

**Book Proposition 4.2.15.** -/
theorem proposition_4_2_15_exercise_4_32 (n m : ℕ) (_hm : m ≤ n) :
    (2 ^ n : ℚ) / hammingBallVolume n m ≤ hammingCoveringNumber n m ∧
      hammingCoveringNumber n m ≤ hammingPackingNumber n m ∧
      (hammingPackingNumber n m : ℚ) ≤
        (2 ^ n : ℚ) / hammingBallVolume n (m / 2) := by
  have hv : (0 : ℚ) < hammingBallVolume n m := by exact_mod_cast hammingBallVolume_pos n m
  have hvhalf : (0 : ℚ) < hammingBallVolume n (m / 2) := by
    exact_mod_cast hammingBallVolume_pos n (m / 2)
  constructor
  · rw [div_le_iff₀ hv]
    exact_mod_cast hamming_covering_lower n m
  constructor
  · have h := Metric.coveringNumber_le_packingNumber (m : ℝ≥0)
        (Set.univ : Set (HDP.BinaryWord n))
    rw [← coe_hammingCoveringNumber, ← coe_hammingPackingNumber] at h
    exact ENat.coe_le_coe.mp h
  · rw [le_div_iff₀ hvhalf]
    exact_mod_cast hamming_packing_upper n m

/-- Source-facing name for the promoted proof exercise.

**Book Proposition 4.2.15.** -/
theorem exercise_4_32 (n m : ℕ) (hm : m ≤ n) :
    (2 ^ n : ℚ) / hammingBallVolume n m ≤ hammingCoveringNumber n m ∧
      hammingCoveringNumber n m ≤ hammingPackingNumber n m ∧
      (hammingPackingNumber n m : ℚ) ≤
        (2 ^ n : ℚ) / hammingBallVolume n (m / 2) :=
  proposition_4_2_15_exercise_4_32 n m hm

end HDP.Chapter4

end Source_09_HammingCube

/-! ## Material formerly in `10_MetricEntropy.lean` -/

section Source_10_MetricEntropy

/-!
# Chapter 4, Section 4.3: metric entropy and coding

The source's phrase “specify with accuracy `ε`” is made precise by requiring
every fibre of the encoder to have diameter at most `ε`.  This is exactly the
property used in both halves of the printed proof.  The theorem is stated in
the equivalent exponentiated form, avoiding partial real logarithms at infinite
covering numbers.
-/

open Set
open scoped ENNReal NNReal

namespace HDP.Chapter4

variable {X : Type*} [PseudoEMetricSpace X]

/-- An `N`-bit encoding of `K` whose fibres have diameter at most `ε`.

The codomain `Fin (2^N)` is the set of available bit strings; no surjectivity is
required. -/
structure FibreDiameterCode (K : Set X) (ε : ℝ≥0) (N : ℕ) where
  encode : K → Fin (2 ^ N)
  fibres_close : ∀ x y : K, encode x = encode y → edist x.1 y.1 ≤ ε

namespace FibreDiameterCode

variable {K : Set X} {ε : ℝ≥0} {N : ℕ}

/-- Bit strings actually used by an encoder.

**Lean implementation helper.** -/
def usedWords (code : FibreDiameterCode K ε N) : Set (Fin (2 ^ N)) :=
  Set.range code.encode

/-- A chosen point in each nonempty fibre.

**Lean implementation helper.** -/
noncomputable def representative (code : FibreDiameterCode K ε N)
    (c : code.usedWords) : K :=
  Classical.choose c.2

/-- Encoding the chosen representative of a codeword recovers that codeword.

**Lean implementation helper.** -/
@[simp]
theorem encode_representative (code : FibreDiameterCode K ε N)
    (c : code.usedWords) : code.encode (code.representative c) = c.1 :=
  Classical.choose_spec c.2

/-- The internal set of chosen fibre representatives.

**Lean implementation helper.** -/
noncomputable def centers (code : FibreDiameterCode K ε N) : Set X :=
  Set.range fun c : code.usedWords => (code.representative c).1

/-- Every chosen code center belongs to the covered set.

**Lean implementation helper.** -/
theorem centers_subset (code : FibreDiameterCode K ε N) : code.centers ⊆ K := by
  rintro _ ⟨c, rfl⟩
  exact (code.representative c).2

/-- A code using `N` bits has at most `2^N` distinct centers.

**Lean implementation helper.** -/
theorem centers_encard_le (code : FibreDiameterCode K ε N) :
    code.centers.encard ≤ (2 ^ N : ℕ) := by
  calc
    code.centers.encard ≤ ENat.card code.usedWords := by
      simpa [centers] using
        Set.encard_image_le
          (fun c : code.usedWords => (code.representative c).1) Set.univ
    _ ≤ ENat.card (Fin (2 ^ N)) :=
      ENat.card_le_card_of_injective Subtype.val_injective
    _ = (2 ^ N : ℕ) := by simp

/-- The selected code centers form an `ε`-cover of the source set.

**Lean implementation helper.** -/
theorem isCover_centers (code : FibreDiameterCode K ε N) :
    Metric.IsCover ε K code.centers := by
  intro x hx
  let a : K := ⟨x, hx⟩
  let c : code.usedWords := ⟨code.encode a, ⟨a, rfl⟩⟩
  refine ⟨(code.representative c).1, ⟨c, rfl⟩, ?_⟩
  exact code.fibres_close a (code.representative c)
    (code.encode_representative c).symm

end FibreDiameterCode

/-- The lower-bound half for the source result: an `N`-bit fibre-diameter code yields an
internal cover by at most `2^N` balls.

**Book Proposition 4.3.1.** -/
theorem metricEntropyCoding_lower {K : Set X} {ε : ℝ≥0} {N : ℕ}
    (code : FibreDiameterCode K ε N) :
    Metric.coveringNumber ε K ≤ (2 ^ N : ℕ) :=
  (code.isCover_centers.coveringNumber_le_encard code.centers_subset).trans
    code.centers_encard_le

/-- A finite internal `(ε/2)`-net with at most `2^N` centers produces an `N`-bit encoding whose
fibres have diameter at most `ε`. This is the upper half of.

**Book Proposition 4.3.1.** -/
theorem metricEntropyCoding_upper {K C : Set X} {ε : ℝ≥0} {N : ℕ}
    (hCfin : C.Finite) (_hCK : C ⊆ K)
    (hcover : Metric.IsCover (ε / 2) K C) (hcard : C.ncard ≤ 2 ^ N) :
    Nonempty (FibreDiameterCode K ε N) := by
  letI : Fintype C := hCfin.fintype
  have hcard' : Fintype.card C ≤ 2 ^ N := by
    simpa [Set.fintypeCard_eq_ncard] using hcard
  let label : C ↪ Fin (2 ^ N) :=
    (Fintype.equivFin C).toEmbedding.trans (Fin.castLEEmb hcard')
  let center : K → C := fun x =>
    ⟨Classical.choose (hcover x.2), (Classical.choose_spec (hcover x.2)).1⟩
  have hcenter (x : K) : edist x.1 (center x).1 ≤ (ε / 2 : ℝ≥0) :=
    (Classical.choose_spec (hcover x.2)).2
  refine ⟨{
    encode := fun x => label (center x)
    fibres_close := ?_ }⟩
  intro x y hxy
  have hc : center x = center y := label.injective hxy
  calc
    edist x.1 y.1 ≤ edist x.1 (center x).1 + edist (center x).1 y.1 :=
      edist_triangle _ _ _
    _ = edist x.1 (center x).1 + edist (center y).1 y.1 := by rw [hc]
    _ ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
      add_le_add (hcenter x) (by simpa [edist_comm] using hcenter y)
    _ = (ε : ℝ≥0∞) := by
      rw [← ENNReal.coe_add]
      congr 1
      exact add_halves ε

/-- Source-facing upper bound: a covering-number bound at radius `ε/2` directly supplies an
`N`-bit fibre-diameter code.

**Lean implementation helper.** -/
theorem metricEntropyCoding_upper_of_coveringNumber {K : Set X} {ε : ℝ≥0} {N : ℕ}
    (hcovering : Metric.coveringNumber (ε / 2) K ≤ (2 ^ N : ℕ)) :
    Nonempty (FibreDiameterCode K ε N) := by
  have hfinite : Metric.coveringNumber (ε / 2) K ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hcovering
  let C : Set X := Metric.minimalCover (ε / 2) K
  have hCfinite : C.Finite := Metric.finite_minimalCover
  have hcard : C.ncard ≤ 2 ^ N := by
    rw [← ENat.coe_le_coe, hCfinite.cast_ncard_eq,
      Metric.encard_minimalCover hfinite]
    exact hcovering
  exact metricEntropyCoding_upper hCfinite Metric.minimalCover_subset
    (Metric.isCover_minimalCover hfinite) hcard

/-- The first implication is valid for arbitrary covering numbers. The second uses an explicit
finite net, which is precisely what the finite upper metric-entropy bound supplies.

**Book Proposition 4.3.1.** -/
theorem proposition_4_3_1 (K : Set X) (ε : ℝ≥0) :
    (∀ (N : ℕ), FibreDiameterCode K ε N →
        Metric.coveringNumber ε K ≤ (2 ^ N : ℕ)) ∧
      (∀ (N : ℕ), Metric.coveringNumber (ε / 2) K ≤ (2 ^ N : ℕ) →
        Nonempty (FibreDiameterCode K ε N)) := by
  exact ⟨fun _ code => metricEntropyCoding_lower code,
    fun _ hcovering => metricEntropyCoding_upper_of_coveringNumber hcovering⟩

end HDP.Chapter4

end Source_10_MetricEntropy

/-! ## Material formerly in `11_ErrorCorrectingCodes.lean` -/

section Source_11_ErrorCorrectingCodes

/-!
# Chapter 4, Section 4.3: error-correcting codes

The definition below follows the source literally: corruption is measured by
Hamming distance, and decoding must succeed for every received word in the
closed radius-`r` ball around the transmitted codeword.
-/

open Set
open scoped ENNReal NNReal BigOperators

namespace HDP.Chapter4

/-- An error-correcting code encodes binary words and decodes every word within the prescribed
Hamming radius back to its transmitted message.

**Book Definition 4.3.3.** -/
structure ErrorCorrectingCode (k n r : ℕ) where
  encode : HDP.BinaryWord k → HDP.BinaryWord n
  decode : HDP.BinaryWord n → HDP.BinaryWord k
  corrects : ∀ (x : HDP.BinaryWord k) (y : HDP.BinaryWord n),
    HDP.hammingDistance (encode x) y ≤ r → decode y = x

namespace ErrorCorrectingCode

variable {k n r : ℕ}

/-- Shows that encode is injective.

**Lean implementation helper.** -/
theorem encode_injective (code : ErrorCorrectingCode k n r) :
    Function.Injective code.encode := by
  intro x y hxy
  have hx := code.corrects x (code.encode x) (by simp [HDP.hammingDistance])
  have hy := code.corrects y (code.encode x) (by
    rw [hxy]
    simp [HDP.hammingDistance])
  exact hx.symm.trans hy

/-- Radius-`r` decoding balls of distinct codewords are disjoint.

**Lean implementation helper.** -/
theorem disjoint_decodingBalls (code : ErrorCorrectingCode k n r)
    {x y : HDP.BinaryWord k} (hxy : x ≠ y) :
    Disjoint (Metric.closedBall (code.encode x) (r : ℝ))
      (Metric.closedBall (code.encode y) (r : ℝ)) := by
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  have hx : code.decode z = x := code.corrects x z (by
    have hz : dist z (code.encode x) ≤ (r : ℝ) := by
      simpa [Metric.mem_closedBall] using hzx
    have hz' : HDP.hammingDistance z (code.encode x) ≤ r := by
      rw [HDP.dist_binaryWord_eq_hammingDistance] at hz
      exact_mod_cast hz
    simpa [HDP.hammingDistance_comm] using hz')
  have hy : code.decode z = y := code.corrects y z (by
    have hz : dist z (code.encode y) ≤ (r : ℝ) := by
      simpa [Metric.mem_closedBall] using hzy
    have hz' : HDP.hammingDistance z (code.encode y) ≤ r := by
      rw [HDP.dist_binaryWord_eq_hammingDistance] at hz
      exact_mod_cast hz
    simpa [HDP.hammingDistance_comm] using hz')
  exact hxy (hx.symm.trans hy)

end ErrorCorrectingCode

/-! ## Constructing a decoder from separated codewords -/

/-- Nearest-feasible-word decoding with arbitrary fallback outside all decoding balls.

**Lean implementation helper.** -/
noncomputable def separatedDecoder {k n : ℕ} (r : ℕ)
    (E : HDP.BinaryWord k → HDP.BinaryWord n) :
    HDP.BinaryWord n → HDP.BinaryWord k := fun y =>
  if h : ∃ x, HDP.hammingDistance (E x) y ≤ r then Classical.choose h else default

/-- A nearest-codeword decoder recovers the transmitted word whenever the received word is within the decoding radius and codewords are sufficiently separated.

**Lean implementation helper.** -/
theorem separatedDecoder_correct {k n r : ℕ}
    (E : HDP.BinaryWord k → HDP.BinaryWord n)
    (hsep : ∀ x y, x ≠ y → 2 * r < HDP.hammingDistance (E x) (E y))
    (x : HDP.BinaryWord k) (y : HDP.BinaryWord n)
    (hy : HDP.hammingDistance (E x) y ≤ r) :
    separatedDecoder r E y = x := by
  rw [separatedDecoder, dif_pos ⟨x, hy⟩]
  let x₀ := Classical.choose (show ∃ z, HDP.hammingDistance (E z) y ≤ r from ⟨x, hy⟩)
  have hx₀ : HDP.hammingDistance (E x₀) y ≤ r :=
    Classical.choose_spec (show ∃ z, HDP.hammingDistance (E z) y ≤ r from ⟨x, hy⟩)
  change x₀ = x
  by_contra hne
  have hfar := hsep x₀ x hne
  have htri := HDP.hammingDistance_triangle (E x₀) y (E x)
  have hyx : HDP.hammingDistance y (E x) ≤ r := by
    simpa [HDP.hammingDistance_comm] using hy
  omega

/-- A separated encoder canonically yields an error-correcting code.

**Lean implementation helper.** -/
noncomputable def codeOfSeparated {k n r : ℕ}
    (E : HDP.BinaryWord k → HDP.BinaryWord n)
    (hsep : ∀ x y, x ≠ y → 2 * r < HDP.hammingDistance (E x) (E y)) :
    ErrorCorrectingCode k n r where
  encode := E
  decode := separatedDecoder r E
  corrects := separatedDecoder_correct E hsep

/-! ## The repetition code -/

/-- Repeat every input bit `2r+1` times. The product index makes the block structure explicit
while the output is still a word indexed by `Fin ((2r+1)k)`.

**Lean implementation helper.** -/
def repeatEncode (r : ℕ) (x : HDP.BinaryWord k) :
    HDP.BinaryWord ((2 * r + 1) * k) :=
  Hamming.toHamming fun t =>
    Hamming.ofHamming x ((@finProdFinEquiv (2 * r + 1) k).symm t).2

/-- Repeating each bit `2r+1` times makes distinct encoded words have Hamming distance greater than `2r`.

**Lean implementation helper.** -/
theorem repeatEncode_separated (r : ℕ) {x y : HDP.BinaryWord k} (hxy : x ≠ y) :
    2 * r < HDP.hammingDistance (repeatEncode r x) (repeatEncode r y) := by
  have hfun : Hamming.ofHamming x ≠ Hamming.ofHamming y := fun h =>
    hxy (Hamming.ofHamming.injective h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfun
  let e : Fin (2 * r + 1) ↪ Fin ((2 * r + 1) * k) :=
    ⟨fun j => @finProdFinEquiv (2 * r + 1) k (j, i), by
      intro a b hab
      exact congrArg Prod.fst ((@finProdFinEquiv (2 * r + 1) k).injective hab)⟩
  have hsub : Finset.univ.map e ⊆
      Finset.univ.filter (fun t =>
        Hamming.ofHamming (repeatEncode r x) t ≠
          Hamming.ofHamming (repeatEncode r y) t) := by
    intro t ht
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at ht
    obtain ⟨j, rfl⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      repeatEncode, Hamming.ofHamming_toHamming]
    simpa [e] using hi
  have hcard : 2 * r + 1 ≤
      HDP.hammingDistance (repeatEncode r x) (repeatEncode r y) := by
    rw [HDP.hammingDistance, hammingDist]
    simpa using Finset.card_le_card hsub
  omega

/-- The concrete majority/repetition code of length `(2r+1)k`.

**Lean implementation helper.** -/
noncomputable def repetitionCode (k r : ℕ) :
    ErrorCorrectingCode k ((2 * r + 1) * k) r :=
  codeOfSeparated (repeatEncode (k := k) r) fun _ _ hxy =>
    repeatEncode_separated r hxy

/-- Any word suffering at most `r` corruptions from a `(2r+1)`-fold repetition is decoded
correctly.

**Book Example 4.3.2.** -/
theorem example_4_3_2 (k r : ℕ) (x : HDP.BinaryWord k)
    (y : HDP.BinaryWord ((2 * r + 1) * k))
    (hy : HDP.hammingDistance (repeatEncode r x) y ≤ r) :
    (repetitionCode k r).decode y = x :=
  (repetitionCode k r).corrects x y hy

/-! ## Packing construction -/

/-- There are exactly `2^n` binary words of length `n`.

**Lean implementation helper.** -/
private theorem binaryWord_card (n : ℕ) :
    Fintype.card (HDP.BinaryWord n) = 2 ^ n := by
  rw [Fintype.card_congr Hamming.ofHamming]
  simp

/-- The source hypothesis `log₂ P ≥ k` is equivalent to the displayed natural inequality because
the Hamming cube is finite.

**Book Lemma 4.3.4.** -/
theorem lemma_4_3_4 {k n r : ℕ}
    (hpack : 2 ^ k ≤ hammingPackingNumber n (2 * r)) :
    Nonempty (ErrorCorrectingCode k n r) := by
  let C : Set (HDP.BinaryWord n) :=
    Metric.maximalSeparatedSet ((2 * r : ℕ) : ℝ≥0)
      (Set.univ : Set (HDP.BinaryWord n))
  have hfinite : Metric.packingNumber ((2 * r : ℕ) : ℝ≥0)
      (Set.univ : Set (HDP.BinaryWord n)) ≠ ⊤ :=
    (HDP.finite_covering_packing_of_finite Set.finite_univ
      ((2 * r : ℕ) : ℝ≥0)).2
  have hCencard : C.encard = hammingPackingNumber n (2 * r) := by
    rw [Metric.encard_maximalSeparatedSet hfinite, ← coe_hammingPackingNumber]
  have hpow : (2 ^ k : ℕ∞) ≤ C.encard := by
    rw [hCencard]
    exact ENat.coe_le_coe.mpr hpack
  obtain ⟨T, hTC, hTcard⟩ := Set.exists_subset_encard_eq hpow
  have hTfinite : T.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [hTcard]
    simp
  letI : Fintype T := hTfinite.fintype
  have hTncard : T.ncard = 2 ^ k := by
    apply ENat.coe_inj.mp
    calc
      (T.ncard : ℕ∞) = T.encard := hTfinite.cast_ncard_eq
      _ = (2 ^ k : ℕ) := hTcard
  have hcard : Fintype.card (HDP.BinaryWord k) = Fintype.card T := by
    rw [binaryWord_card]
    simpa [Set.fintypeCard_eq_ncard] using hTncard.symm
  let e : HDP.BinaryWord k ≃ T := Fintype.equivOfCardEq hcard
  let E : HDP.BinaryWord k → HDP.BinaryWord n := fun x => (e x).1
  have hsep : ∀ x y, x ≠ y → 2 * r < HDP.hammingDistance (E x) (E y) := by
    intro x y hxy
    have hexy : (e x).1 ≠ (e y).1 := by
      intro h
      apply hxy
      apply e.injective
      exact Subtype.ext h
    have hs := Metric.isSeparated_maximalSeparatedSet
      (hTC (e x).2) (hTC (e y).2) hexy
    change ((((2 * r : ℕ) : ℝ≥0) : ℝ≥0∞) < edist (E x) (E y)) at hs
    rw [edist_nndist] at hs
    have hs' := ENNReal.coe_lt_coe.mp hs
    rw [HDP.nndist_binaryWord_eq_hammingDistance] at hs'
    exact_mod_cast hs'
  exact ⟨codeOfSeparated E hsep⟩

/-- The exact finite-ball hypothesis that drives the Gilbert--Varshamov guarantee. It is also
useful independently of logarithmic relaxations.

**Lean implementation helper.** -/
theorem codingGuarantee_of_ballVolume {k n r : ℕ} (hfeasible : 2 * r ≤ n)
    (hvolume : 2 ^ k * hammingBallVolume n (2 * r) ≤ 2 ^ n) :
    Nonempty (ErrorCorrectingCode k n r) := by
  have hprop := proposition_4_2_15_exercise_4_32 n (2 * r) hfeasible
  have hv : (0 : ℚ) < hammingBallVolume n (2 * r) := by
    exact_mod_cast hammingBallVolume_pos n (2 * r)
  have hkcover : 2 ^ k ≤ hammingCoveringNumber n (2 * r) := by
    have hq : (2 ^ k : ℚ) ≤ hammingCoveringNumber n (2 * r) := by
      calc
        (2 ^ k : ℚ) ≤ (2 ^ n : ℚ) / hammingBallVolume n (2 * r) := by
          rw [le_div_iff₀ hv]
          exact_mod_cast hvolume
        _ ≤ hammingCoveringNumber n (2 * r) := hprop.1
    exact_mod_cast hq
  exact lemma_4_3_4 (hkcover.trans hprop.2.1)

/-! The Chapter 0 binomial estimate used in the printed proof is established
locally because Chapter 0 is not yet part of the Lean import graph. -/

/-- Binomial partial-sum estimate `∑_{i=0}^s choose n i ≤ (e n / s)^s`.

**Lean implementation helper.** -/
theorem binomialPartialSum_le (n s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) :
    (hammingBallVolume n s : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s := by
  let x : ℝ := (s : ℝ) / (n : ℝ)
  have hnNat : 1 ≤ n := hs.trans hsn
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hsR : 0 < (s : ℝ) := by positivity
  have hx : 0 < x := div_pos hsR hn
  have hxle : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hn).2 (by exact_mod_cast hsn)
  have hpow (i : ℕ) (hi : i ∈ Finset.range (s + 1)) : x ^ s ≤ x ^ i := by
    apply pow_le_pow_of_le_one hx.le hxle
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hweighted : x ^ s * (hammingBallVolume n s : ℝ) ≤ (x + 1) ^ n := by
    rw [hammingBallVolume, Nat.cast_sum, Finset.mul_sum]
    calc
      ∑ i ∈ Finset.range (s + 1), x ^ s * (n.choose i : ℝ) ≤
          ∑ i ∈ Finset.range (s + 1), x ^ i * (n.choose i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hpow i hi) (by positivity)
      _ ≤ ∑ i ∈ Finset.range (n + 1), x ^ i * (n.choose i : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i _ _
          positivity
      _ = (x + 1) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro i hi
        simp
  have honeexp : (x + 1) ^ n ≤ Real.exp (s : ℝ) := by
    calc
      (x + 1) ^ n ≤ (Real.exp x) ^ n :=
        pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using Real.add_one_le_exp x) n
      _ = Real.exp ((n : ℝ) * x) := (Real.exp_nat_mul x n).symm
      _ = Real.exp (s : ℝ) := by
        congr 1
        dsimp [x]
        field_simp
  have hmain : x ^ s * (hammingBallVolume n s : ℝ) ≤ Real.exp (s : ℝ) :=
    hweighted.trans honeexp
  have hid : x ^ s * (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s =
      Real.exp (s : ℝ) := by
    rw [← mul_pow]
    have hbase : x * (Real.exp 1 * (n : ℝ) / (s : ℝ)) = Real.exp 1 := by
      dsimp [x]
      field_simp
    rw [hbase, ← Real.exp_nat_mul]
    congr 1
    ring
  apply le_of_mul_le_mul_left (a := x ^ s)
  · rw [hid]
    exact hmain
  · exact pow_pos hx s

/-- The logarithmic hypothesis in the corresponding theorem implies the exact finite-ball
counting condition.

**Lean implementation helper.** -/
theorem ballVolumeCondition_of_log {k n s : ℕ} (hk : k ≤ n)
    (hs : 1 ≤ s) (hsn : s ≤ n)
    (hcond : (s : ℝ) * Real.logb 2
        (Real.exp 1 * (n : ℝ) / (s : ℝ)) ≤ (n : ℝ) - (k : ℝ)) :
    2 ^ k * hammingBallVolume n s ≤ 2 ^ n := by
  let b : ℝ := Real.exp 1 * (n : ℝ) / (s : ℝ)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hs.trans hsn
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled : (s : ℝ) * Real.log b ≤
      ((n : ℝ) - (k : ℝ)) * Real.log 2 := by
    have hm := mul_le_mul_of_nonneg_right hcond hlog2.le
    rw [Real.logb] at hm
    field_simp at hm
    simpa [b, mul_comm] using hm
  have hsub : (n : ℝ) - (k : ℝ) = ((n - k : ℕ) : ℝ) :=
    (Nat.cast_sub hk).symm
  have hbpow : b ^ s ≤ (2 : ℝ) ^ (n - k) := by
    calc
      b ^ s = Real.exp ((s : ℝ) * Real.log b) := by
        rw [Real.exp_nat_mul, Real.exp_log hb]
      _ ≤ Real.exp (((n : ℝ) - (k : ℝ)) * Real.log 2) :=
        Real.exp_le_exp.mpr hscaled
      _ = Real.exp (((n - k : ℕ) : ℝ) * Real.log 2) := by rw [hsub]
      _ = (2 : ℝ) ^ (n - k) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hbin : (hammingBallVolume n s : ℝ) ≤ b ^ s := by
    simpa [b] using binomialPartialSum_le n s hs hsn
  have hreal : ((2 ^ k * hammingBallVolume n s : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    calc
      ((2 ^ k * hammingBallVolume n s : ℕ) : ℝ) =
          (2 : ℝ) ^ k * (hammingBallVolume n s : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ k * b ^ s :=
        mul_le_mul_of_nonneg_left hbin (by positivity)
      _ ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ (n - k) :=
        mul_le_mul_of_nonneg_left hbpow (by positivity)
      _ = (2 : ℝ) ^ n := by rw [← pow_add, Nat.add_sub_of_le hk]
  exact_mod_cast hreal

/-- The feasibility assumption `2r ≤ n` is made explicit.

**Book Theorem 4.3.5.** -/
theorem theorem_4_3_5 {k n r : ℕ} (_hkpos : 1 ≤ k) (hrpos : 1 ≤ r)
    (hk : k ≤ n) (hfeasible : 2 * r ≤ n)
    (hcond : ((2 * r : ℕ) : ℝ) * Real.logb 2
        (Real.exp 1 * (n : ℝ) / ((2 * r : ℕ) : ℝ)) ≤
      (n : ℝ) - (k : ℝ)) :
    Nonempty (ErrorCorrectingCode k n r) := by
  have hs : 1 ≤ 2 * r := by omega
  exact codingGuarantee_of_ballVolume hfeasible
    (ballVolumeCondition_of_log hk hs hfeasible hcond)

/-! ## Converse sphere-packing bound -/

/-- Distinct messages have disjoint decoding balls, so the total number of received words in
those balls cannot exceed the Hamming cube.

**Lean implementation helper.** -/
theorem errorCorrectingCode_spherePacking {k n r : ℕ}
    (code : ErrorCorrectingCode k n r) :
    2 ^ k * hammingBallVolume n r ≤ 2 ^ n := by
  let B : HDP.BinaryWord k → Set (HDP.BinaryWord n) := fun x =>
    Metric.closedBall (code.encode x) (r : ℝ)
  have hdisj : Pairwise fun x y => Disjoint (B x) (B y) := by
    intro x y hxy
    exact code.disjoint_decodingBalls hxy
  have hfinite : ∀ x, (B x).Finite := fun _ => Set.toFinite _
  have hunion : (⋃ x, B x) ⊆ (Set.univ : Set (HDP.BinaryWord n)) :=
    Set.subset_univ _
  have hcard : ∑ x : HDP.BinaryWord k, (B x).ncard ≤
      (Set.univ : Set (HDP.BinaryWord n)).ncard := by
    have heq : (⋃ x, B x).ncard = ∑ x : HDP.BinaryWord k, (B x).ncard := by
      calc
        _ = ∑ᶠ x : HDP.BinaryWord k, (B x).ncard :=
          Set.ncard_iUnion_of_finite hfinite hdisj
        _ = ∑ x : HDP.BinaryWord k, (B x).ncard :=
          finsum_eq_sum_of_fintype _
    rw [← heq]
    exact Set.ncard_le_ncard hunion
  simpa [B, card_closedBall_binaryWord, binaryWord_card] using hcard

/-- Elementary lower bound on a binomial coefficient.

**Lean implementation helper.** -/
theorem choose_lower_for_code (n r : ℕ) (hr0 : 0 < r) (hrn : r ≤ n) :
    ((n : ℝ) / (r : ℝ)) ^ r ≤ (n.choose r : ℝ) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial n r)
    (by exact_mod_cast Nat.factorial_ne_zero r)]
  rw [Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_self r,
    Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← Finset.prod_div_distrib]
  calc
    ((n : ℝ) / (r : ℝ)) ^ r =
        ∏ _i ∈ Finset.range r, ((n : ℝ) / (r : ℝ)) := by
          rw [div_pow]
          simp
    _ ≤ ∏ i ∈ Finset.range r,
        ((n - i : ℕ) : ℝ) / ((r - i : ℕ) : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hir : i < r := Finset.mem_range.mp hi
        have hi_le_n : i ≤ n := hir.le.trans hrn
        rw [Nat.cast_sub hi_le_n, Nat.cast_sub hir.le]
        have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
        have hir' : (i : ℝ) < r := by exact_mod_cast hir
        have hden : (0 : ℝ) < (r : ℝ) - i := sub_pos.mpr hir'
        rw [div_le_div_iff₀ hrpos hden]
        have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
        nlinarith

/-- Taking base-two logarithms in the sharp sphere-packing inequality.

**Lean implementation helper.** -/
theorem coding_log_lower {k n r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (hpack : 2 ^ k * n.choose r ≤ 2 ^ n) :
    (r : ℝ) * Real.logb 2 ((n : ℝ) / r) ≤ (n : ℝ) - k := by
  have hchoose := choose_lower_for_code n r hr0 hrn
  have hpack' : (2 : ℝ) ^ k * (n.choose r : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hpack
  have hmain : (2 : ℝ) ^ k * ((n : ℝ) / r) ^ r ≤ (2 : ℝ) ^ n :=
    (mul_le_mul_of_nonneg_left hchoose (by positivity)).trans hpack'
  have hxpos : 0 < (n : ℝ) / r := by
    have hn0 : 0 < n := lt_of_lt_of_le hr0 hrn
    positivity
  have hlog := (Real.logb_le_logb (b := 2) (by norm_num)
    (mul_pos (by positivity) (pow_pos hxpos r)) (by positivity)).2 hmain
  rw [Real.logb_mul (by positivity) (pow_ne_zero _ hxpos.ne'),
    Real.logb_pow, Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at hlog
  norm_num at hlog ⊢
  linarith

/-- The source conclusion is stated verbatim in base-two logarithms, with the audited positivity
and feasibility hypotheses.

**Book Exercise 4.33.** -/
theorem exercise_4_33 {k n r : ℕ} (code : ErrorCorrectingCode k n r)
    (hrpos : 1 ≤ r) (hfeasible : 2 * r ≤ n) :
    (r : ℝ) * Real.logb 2 ((n : ℝ) / r) ≤ (n : ℝ) - k := by
  have hrn : r ≤ n := by omega
  have hchooseVolume : n.choose r ≤ hammingBallVolume n r := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    simp
  have hpack : 2 ^ k * n.choose r ≤ 2 ^ n :=
    (Nat.mul_le_mul_left (2 ^ k) hchooseVolume).trans
      (errorCorrectingCode_spherePacking code)
  exact coding_log_lower (Nat.zero_lt_of_lt hrpos) hrn hpack

end HDP.Chapter4

end Source_11_ErrorCorrectingCodes

/-! ## Material formerly in `12_NetNormBounds.lean` -/

section Source_12_NetNormBounds

/-!
# Chapter 4, §4.4.1: computing operator norms on nets

The implementation uses a predicate for an internal net of the unit sphere.
It works for arbitrary real finite-dimensional inner-product spaces and is
therefore reusable for both rectangular matrices and self-adjoint Gram maps.
-/

open Set Real InnerProductSpace Filter
open scoped RealInnerProductSpace Matrix.Norms.L2Operator Topology

namespace HDP

/-- A set contained in the unit sphere which approximates every unit vector.

**Lean implementation helper.** -/
def IsUnitSphereNet {E : Type*} [NormedAddCommGroup E]
    (ε : ℝ) (N : Set E) : Prop :=
  (∀ x ∈ N, ‖x‖ = 1) ∧
    ∀ x : E, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ ≤ ε

end HDP

namespace HDP.Chapter4

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Bounds norm image of unit by bilinear bound.

**Lean implementation helper.** -/
private lemma norm_image_of_unit_le_bilinear_bound
    (T : E →L[ℝ] F) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ x : E, ‖x‖ = 1 → ∀ y : F, ‖y‖ = 1 →
      |inner ℝ (T x) y| ≤ B) {x : E} (hx : ‖x‖ = 1) :
    ‖T x‖ ≤ B := by
  by_cases hTx : T x = 0
  · simp [hTx, hB0]
  · let y : F := ‖T x‖⁻¹ • T x
    have hnorm : ‖T x‖ ≠ 0 := norm_ne_zero_iff.mpr hTx
    have hy : ‖y‖ = 1 := by
      simp [y, norm_smul, hnorm]
    have hi : inner ℝ (T x) y = ‖T x‖ := by
      rw [show y = ‖T x‖⁻¹ • T x by rfl, inner_smul_right]
      rw [real_inner_self_eq_norm_sq]
      field_simp [hnorm]
    simpa [hi] using hB x hx y hy

/-- Bilinear form control on two unit-sphere nets controls the full operator norm. This is the
source-neutral engine for the corresponding lemma.

**Lean implementation helper.** -/
theorem opNorm_le_of_bilinear_on_nets
    (T : E →L[ℝ] F) {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε < 1)
    {N : Set E} {M : Set F}
    (hN : HDP.IsUnitSphereNet ε N) (hM : HDP.IsUnitSphereNet ε M)
    (hR : 0 ≤ R)
    (hnet : ∀ x ∈ N, ∀ y ∈ M, |inner ℝ (T x) y| ≤ R) :
    ‖T‖ ≤ R / (1 - 2 * ε) := by
  have hden : 0 < 1 - 2 * ε := sub_pos.mpr hε
  have hunit : ∀ x : E, ‖x‖ = 1 → ∀ y : F, ‖y‖ = 1 →
      |inner ℝ (T x) y| ≤ R + 2 * ε * ‖T‖ := by
    intro x hx y hy
    obtain ⟨x₀, hx₀N, hxx₀⟩ := hN.2 x hx
    obtain ⟨y₀, hy₀M, hyy₀⟩ := hM.2 y hy
    have hx₀ : ‖x₀‖ = 1 := hN.1 x₀ hx₀N
    have hy₀ : ‖y₀‖ = 1 := hM.1 y₀ hy₀M
    have hsplit : inner ℝ (T x) y =
        inner ℝ (T x₀) y₀ + inner ℝ (T (x - x₀)) y +
          inner ℝ (T x₀) (y - y₀) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : |inner ℝ (T (x - x₀)) y| ≤ ‖T‖ * ε := by
      calc
        |inner ℝ (T (x - x₀)) y| ≤ ‖T (x - x₀)‖ * ‖y‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x - x₀‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖T‖ * ε := by
          rw [hy, mul_one]
          exact mul_le_mul_of_nonneg_left hxx₀ (ContinuousLinearMap.opNorm_nonneg T)
    have h2 : |inner ℝ (T x₀) (y - y₀)| ≤ ‖T‖ * ε := by
      calc
        |inner ℝ (T x₀) (y - y₀)| ≤ ‖T x₀‖ * ‖y - y₀‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x₀‖) * ε := by
          exact mul_le_mul (T.le_opNorm _) hyy₀ (norm_nonneg _) (by positivity)
        _ = ‖T‖ * ε := by rw [hx₀, mul_one]
    rw [hsplit]
    calc
      |inner ℝ (T x₀) y₀ + inner ℝ (T (x - x₀)) y +
          inner ℝ (T x₀) (y - y₀)|
          ≤ |inner ℝ (T x₀) y₀| +
              |inner ℝ (T (x - x₀)) y| +
              |inner ℝ (T x₀) (y - y₀)| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ R + (‖T‖ * ε) + (‖T‖ * ε) :=
        add_le_add (add_le_add (hnet x₀ hx₀N y₀ hy₀M) h1) h2
      _ = R + 2 * ε * ‖T‖ := by ring
  have hop_aux : ‖T‖ ≤ R + 2 * ε * ‖T‖ := by
    apply T.opNorm_le_bound
    · positivity
    · intro x
      by_cases hx0 : ‖x‖ = 0
      · have hx : x = 0 := norm_eq_zero.mp hx0
        simp [hx]
      · let z : E := ‖x‖⁻¹ • x
        have hz : ‖z‖ = 1 := by
          simp [z, norm_smul, hx0]
        have hTz := norm_image_of_unit_le_bilinear_bound T (by positivity) hunit hz
        have hx : x = ‖x‖ • z := by
          simp [z, smul_smul, hx0]
        calc
          ‖T x‖ = ‖T (‖x‖ • z)‖ := congrArg (fun w => ‖T w‖) hx
          _ = ‖x‖ * ‖T z‖ := by
            rw [map_smul, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg x)]
          _ ≤ ‖x‖ * (R + 2 * ε * ‖T‖) :=
            mul_le_mul_of_nonneg_left hTz (norm_nonneg x)
          _ = (R + 2 * ε * ‖T‖) * ‖x‖ := mul_comm _ _
  apply (le_div_iff₀ hden).2
  nlinarith

/-- A symmetric operator is controlled by its quadratic form on one unit net. This is the
diagonal, self-adjoint form of the engine behind the corresponding lemma.

**Lean implementation helper.** -/
theorem opNorm_le_of_quadratic_on_net [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε < 1)
    {N : Set E} (hN : HDP.IsUnitSphereNet ε N) (hR : 0 ≤ R)
    (hnet : ∀ x ∈ N, |inner ℝ (T x) x| ≤ R) :
    ‖T‖ ≤ R / (1 - 2 * ε) := by
  have hunit : ∀ x : E, ‖x‖ = 1 →
      |inner ℝ (T x) x| ≤ R + 2 * ε * ‖T‖ := by
    intro x hx
    obtain ⟨x₀, hx₀N, hxx₀⟩ := hN.2 x hx
    have hx₀ : ‖x₀‖ = 1 := hN.1 x₀ hx₀N
    have hsplit : inner ℝ (T x) x - inner ℝ (T x₀) x₀ =
        inner ℝ (T (x - x₀)) x + inner ℝ (T x₀) (x - x₀) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h₁ : |inner ℝ (T (x - x₀)) x| ≤ ‖T‖ * ε := by
      calc
        _ ≤ ‖T (x - x₀)‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x - x₀‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖T‖ * ε := by
          rw [hx, mul_one]
          exact mul_le_mul_of_nonneg_left hxx₀
            (ContinuousLinearMap.opNorm_nonneg T)
    have h₂ : |inner ℝ (T x₀) (x - x₀)| ≤ ‖T‖ * ε := by
      calc
        _ ≤ ‖T x₀‖ * ‖x - x₀‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x₀‖) * ‖x - x₀‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ ≤ (‖T‖ * ‖x₀‖) * ε :=
          mul_le_mul_of_nonneg_left hxx₀
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg T) (norm_nonneg _))
        _ = ‖T‖ * ε := by rw [hx₀, mul_one]
    calc
      |inner ℝ (T x) x| = |inner ℝ (T x₀) x₀ +
          (inner ℝ (T x) x - inner ℝ (T x₀) x₀)| := by
        congr 1
        ring
      _ ≤ |inner ℝ (T x₀) x₀| +
          |inner ℝ (T x) x - inner ℝ (T x₀) x₀| := abs_add_le _ _
      _ ≤ R + (|inner ℝ (T (x - x₀)) x| +
          |inner ℝ (T x₀) (x - x₀)|) := by
        rw [hsplit]
        exact add_le_add (hnet x₀ hx₀N) (abs_add_le _ _)
      _ ≤ R + (‖T‖ * ε + ‖T‖ * ε) :=
        add_le_add (le_refl R) (add_le_add h₁ h₂)
      _ = R + 2 * ε * ‖T‖ := by ring
  have hopAux : ‖T‖ ≤ R + 2 * ε * ‖T‖ := by
    have hnormeq := T.norm_eq_iSup_rayleighQuotient hT
    rw [hnormeq]
    apply ciSup_le
    intro z
    by_cases hz : z = 0
    · simp only [hz, T.rayleighQuotient_apply_zero, abs_zero]
      rw [← hnormeq]
      positivity
    · let w : E := ‖z‖⁻¹ • z
      have hw : ‖w‖ = 1 := by simp [w, norm_smul, hz]
      have hq := hunit w hw
      have hray : T.rayleighQuotient z = inner ℝ (T w) w := by
        rw [← T.rayleigh_smul z (inv_ne_zero (norm_ne_zero_iff.mpr hz))]
        simp [w, ContinuousLinearMap.rayleighQuotient,
          ContinuousLinearMap.reApplyInnerSelf_apply, hw]
      rw [hray]
      rw [← hnormeq]
      exact hq
  apply (le_div_iff₀ (sub_pos.mpr hε)).2
  nlinarith

/-- Norm control on an internal unit-sphere net. The explicit bound `R` is the finite
maximum/supremum appearing in the source.

**Book Lemma 4.4.1.** -/
theorem lemma_4_4_1
    (T : E →L[ℝ] F) {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    {N : Set E} (hN : HDP.IsUnitSphereNet ε N) (hR : 0 ≤ R)
    (hnet : ∀ x ∈ N, ‖T x‖ ≤ R) :
    ‖T‖ ≤ R / (1 - ε) := by
  have hden : 0 < 1 - ε := sub_pos.mpr hε
  have hop_aux : ‖T‖ ≤ R + ε * ‖T‖ := by
    apply T.opNorm_le_bound
    · positivity
    · intro x
      by_cases hx0 : ‖x‖ = 0
      · have hx : x = 0 := norm_eq_zero.mp hx0
        simp [hx]
      · let z : E := ‖x‖⁻¹ • x
        have hz : ‖z‖ = 1 := by simp [z, norm_smul, hx0]
        obtain ⟨z₀, hz₀N, hzz₀⟩ := hN.2 z hz
        have hpoint : ‖T z‖ ≤ R + ε * ‖T‖ := by
          have hdecomp : T z = T z₀ + T (z - z₀) := by
            rw [map_sub]
            abel
          calc
            ‖T z‖ = ‖T z₀ + T (z - z₀)‖ := congrArg norm hdecomp
            _ ≤ ‖T z₀‖ + ‖T (z - z₀)‖ :=
              norm_add_le (T z₀) (T (z - z₀))
            _ ≤ R + ‖T‖ * ‖z - z₀‖ := add_le_add (hnet z₀ hz₀N) (T.le_opNorm _)
            _ ≤ R + ε * ‖T‖ := by
              have hm := mul_le_mul_of_nonneg_left hzz₀
                (ContinuousLinearMap.opNorm_nonneg T)
              nlinarith
        have hx : x = ‖x‖ • z := by simp [z, smul_smul, hx0]
        calc
          ‖T x‖ = ‖T (‖x‖ • z)‖ := congrArg (fun w => ‖T w‖) hx
          _ = ‖x‖ * ‖T z‖ := by
            rw [map_smul, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg x)]
          _ ≤ ‖x‖ * (R + ε * ‖T‖) :=
            mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
          _ = (R + ε * ‖T‖) * ‖x‖ := mul_comm _ _
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Every unit vector has an exact convergent expansion in an internal `ε`-net, with
geometrically decaying nonnegative coefficients.

**Book Exercise 4.34.** -/
theorem exercise_4_34a [CompleteSpace E]
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    {N : Set E} (hN : HDP.IsUnitSphereNet ε N)
    {x : E} (hx : ‖x‖ = 1) :
    ∃ coeff : ℕ → ℝ, ∃ v : ℕ → E,
      (∀ k, 0 ≤ coeff k ∧ coeff k ≤ ε ^ k) ∧
      (∀ k, v k ∈ N) ∧
      HasSum (fun k => coeff k • v k) x := by
  classical
  obtain ⟨v₀, hv₀N, hv₀⟩ := hN.2 x hx
  let unitApprox : E → E := fun z =>
    if hz : z = 0 then v₀
    else Classical.choose (hN.2 (‖z‖⁻¹ • z) (by simp [hz, norm_smul]))
  have hunitApprox_mem (z : E) : unitApprox z ∈ N := by
    by_cases hz : z = 0
    · simp [unitApprox, hz, hv₀N]
    · simpa [unitApprox, hz] using
        (Classical.choose_spec (hN.2 (‖z‖⁻¹ • z) (by simp [hz, norm_smul]))).1
  have hunitApprox_norm (z : E) : ‖unitApprox z‖ = 1 :=
    hN.1 _ (hunitApprox_mem z)
  have hresidual (z : E) : ‖z - ‖z‖ • unitApprox z‖ ≤ ε * ‖z‖ := by
    by_cases hz : z = 0
    · simp [hz]
    · have hnear :=
        (Classical.choose_spec (hN.2 (‖z‖⁻¹ • z) (by simp [hz, norm_smul]))).2
      have hzscale : z = ‖z‖ • (‖z‖⁻¹ • z) := by
        simp [smul_smul, hz]
      have hdecomp : z - ‖z‖ • unitApprox z =
          ‖z‖ • ((‖z‖⁻¹ • z) - unitApprox z) := by
        calc
          z - ‖z‖ • unitApprox z =
              (‖z‖ • (‖z‖⁻¹ • z)) - ‖z‖ • unitApprox z :=
            congrArg (fun w => w - ‖z‖ • unitApprox z) hzscale
          _ = ‖z‖ • ((‖z‖⁻¹ • z) - unitApprox z) := by
            rw [smul_sub]
      rw [hdecomp, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z)]
      simpa [unitApprox, hz, mul_comm] using
        mul_le_mul_of_nonneg_left hnear (norm_nonneg z)
  let r : ℕ → E := fun k =>
    Nat.rec x (fun _ z => z - ‖z‖ • unitApprox z) k
  let coeff : ℕ → ℝ := fun k => ‖r k‖
  let v : ℕ → E := fun k => unitApprox (r k)
  have hr_succ (k : ℕ) : r (k + 1) = r k - ‖r k‖ • unitApprox (r k) := by
    simp [r]
  have hr_bound (k : ℕ) : ‖r k‖ ≤ ε ^ k := by
    induction k with
    | zero => simpa [r] using hx.le
    | succ k ih =>
        rw [show k + 1 = Nat.succ k by omega, hr_succ, pow_succ]
        exact (hresidual (r k)).trans (by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left ih hε0)
  have hpartial (q : ℕ) :
      ∑ k ∈ Finset.range q, coeff k • v k = x - r q := by
    induction q with
    | zero => simp [r]
    | succ q ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [coeff, v]
        rw [hr_succ]
        abel
  have hr_zero : Tendsto r atTop (𝓝 (0 : E)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg (r k)) hr_bound
      (tendsto_pow_atTop_nhds_zero_of_lt_one hε0 hε)
  have hsum_tendsto : Tendsto
      (fun q => ∑ k ∈ Finset.range q, coeff k • v k) atTop (𝓝 x) := by
    have : (fun q => ∑ k ∈ Finset.range q, coeff k • v k) = fun q => x - r q := by
      funext q
      exact hpartial q
    rw [this]
    simpa using (tendsto_const_nhds.sub hr_zero)
  have hsummableNorm : Summable (fun k => ‖coeff k • v k‖) := by
    apply (summable_geometric_of_lt_one hε0 hε).of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · intro k
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (r k)),
        show ‖v k‖ = 1 by exact hunitApprox_norm (r k), mul_one]
      exact hr_bound k
  refine ⟨coeff, v, ?_, ?_, ?_⟩
  · intro k
    exact ⟨norm_nonneg _, hr_bound k⟩
  · intro k
    exact hunitApprox_mem (r k)
  · exact (hasSum_iff_tendsto_nat_of_summable_norm hsummableNorm).2 hsum_tendsto

/-- Backward-compatible name for **Exercise 4.34(a)**. -/
alias exercise_4_34 := exercise_4_34a

/-- Applying the expansion from part (a) gives the net bound of the corresponding lemma. The
theorem is exposed as a source-facing wrapper because the exercise asks for this alternative
proof of exactly the same mathematical statement.

**Book Exercise 4.34.** -/
theorem exercise_4_34b
    (T : E →L[ℝ] F) {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    {N : Set E} (hN : HDP.IsUnitSphereNet ε N) (hR : 0 ≤ R)
    (hnet : ∀ x ∈ N, ‖T x‖ ≤ R) :
    ‖T‖ ≤ R / (1 - ε) :=
  lemma_4_4_1 T hε0 hε hN hR hnet

/-- A finite internal `ε`-net of the unit sphere absorbs the closed ball of radius `1-ε` in its
convex hull.

**Book Exercise 4.38.** -/
theorem exercise_4_38 [CompleteSpace E] [Nontrivial E]
    {ε : ℝ} (_hε0 : 0 ≤ ε) (_hε : ε < 1)
    (N : Finset E) (hN : HDP.IsUnitSphereNet ε (N : Set E)) :
    Metric.closedBall (0 : E) (1 - ε) ⊆ convexHull ℝ (N : Set E) := by
  classical
  intro z hz
  by_contra hzHull
  have hclosed : IsClosed (convexHull ℝ (N : Set E)) :=
    N.finite_toSet.isClosed_convexHull ℝ
  obtain ⟨f, u, hfHull, hufz⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (N : Set E)) hclosed hzHull
  obtain ⟨q : E, hq⟩ := exists_ne (0 : E)
  have hqunit : ‖‖q‖⁻¹ • q‖ = 1 := by simp [norm_smul, hq]
  obtain ⟨y₀, hy₀N, hy₀near⟩ := hN.2 (‖q‖⁻¹ • q) hqunit
  have hfy₀ : f y₀ < u := hfHull y₀ (subset_convexHull ℝ (N : Set E) hy₀N)
  let a : E := (InnerProductSpace.toDual ℝ E).symm f
  have hfa (w : E) : inner ℝ a w = f w := by
    exact InnerProductSpace.toDual_symm_apply
  have hnorma : ‖a‖ = ‖f‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map f
  have ha : a ≠ 0 := by
    intro ha0
    have hf0 : f = 0 := by
      apply (InnerProductSpace.toDual ℝ E).symm.injective
      simp [a, ha0]
    simp [hf0] at hfy₀ hufz
    linarith
  let w : E := ‖a‖⁻¹ • a
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, ha]
  obtain ⟨y, hyN, hwy⟩ := hN.2 w hw
  have hfyHull : f y < u := hfHull y (subset_convexHull ℝ (N : Set E) hyN)
  have hfw : f w = ‖f‖ := by
    calc
      f w = inner ℝ a w := (hfa w).symm
      _ = ‖a‖ := by
        change inner ℝ a (‖a‖⁻¹ • a) = ‖a‖
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr ha]
      _ = ‖f‖ := hnorma
  have hdiff : |f w - f y| ≤ ‖f‖ * ε := by
    calc
      |f w - f y| = ‖f (w - y)‖ := by
        rw [map_sub, Real.norm_eq_abs]
      _ ≤ ‖f‖ * ‖w - y‖ := f.le_opNorm (w - y)
      _ ≤ ‖f‖ * ε :=
        mul_le_mul_of_nonneg_left hwy (ContinuousLinearMap.opNorm_nonneg f)
  have hfyLower : (1 - ε) * ‖f‖ ≤ f y := by
    have hsub : ‖f‖ - f y ≤ ‖f‖ * ε := by
      calc
        ‖f‖ - f y = f w - f y := by rw [hfw]
        _ ≤ |f w - f y| := le_abs_self _
        _ ≤ ‖f‖ * ε := hdiff
    nlinarith
  have hznorm : ‖z‖ ≤ 1 - ε := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hfzUpper : f z ≤ (1 - ε) * ‖f‖ := by
    calc
      f z ≤ |f z| := le_abs_self _
      _ = ‖f z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
      _ ≤ ‖f‖ * (1 - ε) :=
        mul_le_mul_of_nonneg_left hznorm (ContinuousLinearMap.opNorm_nonneg f)
      _ = (1 - ε) * ‖f‖ := mul_comm _ _
  linarith

/-- Squared-norm auxiliary for. This is the quantity used by the published hint, although the
exercise itself asks about `|‖T x‖ - μ|`.

**Book Exercise 4.37.** -/
theorem exercise_4_37_squared_aux
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [CompleteSpace E]
    (T : E →L[ℝ] G) {μ ε B : ℝ}
    (hε0 : 0 ≤ ε) (hε : 2 * ε < 1) (hB : 0 ≤ B)
    {N : Set E} (hN : HDP.IsUnitSphereNet ε N)
    (hnet : ∀ x ∈ N, |‖T x‖ ^ 2 - μ| ≤ B) :
    ∀ x : E, ‖x‖ = 1 →
      |‖T x‖ ^ 2 - μ| ≤ B / (1 - 2 * ε) := by
  let R : E →L[ℝ] E := T.adjoint.comp T -
    μ • ContinuousLinearMap.id ℝ E
  have hRquad (z : E) :
      inner ℝ (R z) z = ‖T z‖ ^ 2 - μ * ‖z‖ ^ 2 := by
    change inner ℝ ((T.adjoint.comp T) z - μ • z) z =
      ‖T z‖ ^ 2 - μ * ‖z‖ ^ 2
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    have ht := T.apply_norm_sq_eq_inner_adjoint_left z
    change ‖T z‖ ^ 2 = inner ℝ ((T.adjoint.comp T) z) z at ht
    rw [← ht]
    simp
  have hRsymm : (R : E →ₗ[ℝ] E).IsSymmetric := by
    intro z w
    change inner ℝ ((T.adjoint.comp T) z - μ • z) w =
      inner ℝ z ((T.adjoint.comp T) w - μ • w)
    rw [inner_sub_left, inner_sub_right]
    simp only [ContinuousLinearMap.comp_apply]
    rw [T.adjoint_inner_left,
      T.adjoint_inner_right, inner_smul_left, inner_smul_right]
    simp
  have hRnet : ∀ z ∈ N, |inner ℝ (R z) z| ≤ B := by
    intro z hz
    rw [hRquad, hN.1 z hz, one_pow, mul_one]
    exact hnet z hz
  have hop := opNorm_le_of_quadratic_on_net R hRsymm hε0 hε hN hB hRnet
  intro x hx
  have hquadx := hRquad x
  rw [hx, one_pow, mul_one] at hquadx
  rw [← hquadx]
  exact (abs_real_inner_le_norm (R x) x).trans <| by
    calc
      ‖R x‖ * ‖x‖ ≤ (‖R‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (R.le_opNorm x) (norm_nonneg x)
      _ = ‖R‖ := by rw [hx]; ring
      _ ≤ B / (1 - 2 * ε) := hop

/-- Norm deviation on the whole unit sphere is controlled by norm deviation on one `ε`-net. The
explicit absolute constant is `3`. The proof also handles the printed statement's full range `μ:
ℝ`; positivity is used only in the internal case corresponding to the published squared-norm
hint.

**Book Exercise 4.37.** -/
theorem exercise_4_37
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [CompleteSpace E]
    (T : E →L[ℝ] G) {μ ε B : ℝ}
    (hε0 : 0 ≤ ε) (hε : 2 * ε < 1) (hB : 0 ≤ B)
    {N : Set E} (hN : HDP.IsUnitSphereNet ε N)
    (hnet : ∀ x ∈ N, |‖T x‖ - μ| ≤ B) :
    ∀ x : E, ‖x‖ = 1 →
      |‖T x‖ - μ| ≤ (3 * B) / (1 - 2 * ε) := by
  have hd : 0 < 1 - 2 * ε := sub_pos.mpr hε
  have he : 0 < 1 - ε := by linarith
  have hε1 : ε < 1 := by linarith
  have hdle : 1 - 2 * ε ≤ 1 - ε := by linarith
  have hdle1 : 1 - 2 * ε ≤ 1 := by linarith
  intro x hx
  by_cases hμ : μ ≤ 0
  · obtain ⟨y, hyN, _hy⟩ := hN.2 x hx
    have hydev := hnet y hyN
    have hyupper : ‖T y‖ - μ ≤ B := (le_abs_self _).trans hydev
    have hminus : -μ ≤ B := by nlinarith [norm_nonneg (T y)]
    have hR0 : 0 ≤ B + μ := by nlinarith [norm_nonneg (T y)]
    have hnetNorm : ∀ z ∈ N, ‖T z‖ ≤ B + μ := by
      intro z hz
      have hzdev := hnet z hz
      have hzupper : ‖T z‖ - μ ≤ B := (le_abs_self _).trans hzdev
      linarith
    have hop := lemma_4_4_1 T hε0 hε1 hN hR0 hnetNorm
    have hopmul : (1 - ε) * ‖T‖ ≤ B + μ := by
      have := (le_div_iff₀ he).mp hop
      nlinarith
    have hTx : ‖T x‖ ≤ ‖T‖ := by
      calc
        ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
        _ = ‖T‖ := by rw [hx, mul_one]
    have hfscaled : (1 - 2 * ε) * ‖T x‖ ≤ (1 - ε) * ‖T‖ := by
      calc
        (1 - 2 * ε) * ‖T x‖ ≤ (1 - 2 * ε) * ‖T‖ :=
          mul_le_mul_of_nonneg_left hTx hd.le
        _ ≤ (1 - ε) * ‖T‖ :=
          mul_le_mul_of_nonneg_right hdle (ContinuousLinearMap.opNorm_nonneg T)
    have hnegscaled : (1 - 2 * ε) * (-μ) ≤ B := by
      calc
        (1 - 2 * ε) * (-μ) ≤ 1 * (-μ) :=
          mul_le_mul_of_nonneg_right hdle1 (neg_nonneg.mpr hμ)
        _ ≤ B := by simpa using hminus
    rw [abs_of_nonneg (by nlinarith [norm_nonneg (T x)])]
    apply (le_div_iff₀ hd).2
    nlinarith
  · have hμpos : 0 < μ := lt_of_not_ge hμ
    have hnetSq : ∀ z ∈ N, |‖T z‖ ^ 2 - μ ^ 2| ≤ B * (2 * μ + B) := by
      intro z hz
      have hzdev := hnet z hz
      have hzsum : ‖T z‖ + μ ≤ 2 * μ + B := by
        have hzupper : ‖T z‖ - μ ≤ B := (le_abs_self _).trans hzdev
        linarith
      calc
        |‖T z‖ ^ 2 - μ ^ 2| = |(‖T z‖ - μ) * (‖T z‖ + μ)| := by
          congr 1
          ring
        _ = |‖T z‖ - μ| * |‖T z‖ + μ| := abs_mul _ _
        _ = |‖T z‖ - μ| * (‖T z‖ + μ) := by
          apply congrArg (fun r : ℝ => |‖T z‖ - μ| * r)
          exact abs_of_nonneg (by positivity)
        _ ≤ B * (2 * μ + B) :=
          mul_le_mul hzdev hzsum (by positivity) hB
    have hBsq : 0 ≤ B * (2 * μ + B) := by positivity
    have hsq := exercise_4_37_squared_aux T hε0 hε hBsq hN hnetSq x hx
    have hsqmul : |‖T x‖ ^ 2 - μ ^ 2| * (1 - 2 * ε) ≤
        B * (2 * μ + B) := (le_div_iff₀ hd).mp hsq
    by_cases hBμ : B ≤ μ
    · have hfactor : |‖T x‖ ^ 2 - μ ^ 2| =
          |‖T x‖ - μ| * (‖T x‖ + μ) := by
        calc
          |‖T x‖ ^ 2 - μ ^ 2| = |(‖T x‖ - μ) * (‖T x‖ + μ)| := by
            congr 1
            ring
          _ = |‖T x‖ - μ| * |‖T x‖ + μ| := abs_mul _ _
          _ = |‖T x‖ - μ| * (‖T x‖ + μ) := by
            apply congrArg (fun r : ℝ => |‖T x‖ - μ| * r)
            exact abs_of_nonneg (by positivity)
      rw [hfactor] at hsqmul
      have hprod : |‖T x‖ - μ| * μ ≤
          |‖T x‖ - μ| * (‖T x‖ + μ) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (T x)]) (abs_nonneg _)
      have hlower : (|‖T x‖ - μ| * (1 - 2 * ε)) * μ ≤
          (|‖T x‖ - μ| * (‖T x‖ + μ)) * (1 - 2 * ε) := by
        calc
          (|‖T x‖ - μ| * (1 - 2 * ε)) * μ =
              (1 - 2 * ε) * (|‖T x‖ - μ| * μ) := by ring
          _ ≤ (1 - 2 * ε) * (|‖T x‖ - μ| * (‖T x‖ + μ)) :=
            mul_le_mul_of_nonneg_left hprod hd.le
          _ = (|‖T x‖ - μ| * (‖T x‖ + μ)) * (1 - 2 * ε) := by ring
      have hBupper : B * (2 * μ + B) ≤ (3 * B) * μ := by
        nlinarith [mul_nonneg hB (sub_nonneg.mpr hBμ)]
      have hcancel : (|‖T x‖ - μ| * (1 - 2 * ε)) * μ ≤
          (3 * B) * μ := hlower.trans (hsqmul.trans hBupper)
      apply (le_div_iff₀ hd).2
      exact le_of_mul_le_mul_right hcancel hμpos
    · have hμB : μ < B := lt_of_not_ge hBμ
      have hdiff : (1 - 2 * ε) * (‖T x‖ ^ 2 - μ ^ 2) ≤
          B * (2 * μ + B) := by
        calc
          (1 - 2 * ε) * (‖T x‖ ^ 2 - μ ^ 2) ≤
              (1 - 2 * ε) * |‖T x‖ ^ 2 - μ ^ 2| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hd.le
          _ = |‖T x‖ ^ 2 - μ ^ 2| * (1 - 2 * ε) := by ring
          _ ≤ B * (2 * μ + B) := hsqmul
      have hdmu : (1 - 2 * ε) * μ ^ 2 ≤ μ ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg μ) hdle1
      have hadd : B + μ ≤ 2 * B := by linarith
      have hsquare : (B + μ) ^ 2 ≤ (2 * B) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (by positivity) hadd
      have hdfsq : (1 - 2 * ε) * ‖T x‖ ^ 2 ≤ 4 * B ^ 2 := by
        nlinarith
      have hdsq : (1 - 2 * ε) ^ 2 ≤ 1 - 2 * ε := by
        nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdle1)]
      have hdfsq' : ((1 - 2 * ε) * ‖T x‖) ^ 2 ≤ (2 * B) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hdsq (sq_nonneg ‖T x‖)
        nlinarith
      have hdf : (1 - 2 * ε) * ‖T x‖ ≤ 2 * B := by
        nlinarith [mul_nonneg hd.le (norm_nonneg (T x))]
      have habs : |‖T x‖ - μ| ≤ ‖T x‖ + μ := by
        calc
          |‖T x‖ - μ| ≤ |‖T x‖| + |μ| := abs_sub _ _
          _ = ‖T x‖ + μ := by
            rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hμpos]
      apply (le_div_iff₀ hd).2
      have hscale := mul_le_mul_of_nonneg_right habs hd.le
      nlinarith [mul_le_mul_of_nonneg_left hμB.le hd.le]
/-- Controls the full operator norm by bilinear or quadratic values on finite nets.

**Book Lemma 4.4.2.** -/
theorem lemma_4_4_2
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : 2 * ε < 1)
    {N : Set (EuclideanSpace ℝ n)} {M : Set (EuclideanSpace ℝ m)}
    (hN : HDP.IsUnitSphereNet ε N) (hM : HDP.IsUnitSphereNet ε M)
    (hR : 0 ≤ R)
    (hnet : ∀ x ∈ N, ∀ y ∈ M,
      |inner ℝ (WithLp.toLp 2 (A.mulVec x.ofLp)) y| ≤ R) :
    HDP.matrixOpNorm A ≤ R / (1 - 2 * ε) := by
  let T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 A)
  change ‖T‖ ≤ R / (1 - 2 * ε)
  apply opNorm_le_of_bilinear_on_nets T hε0 hε hN hM hR
  intro x hx y hy
  simpa [T, Matrix.toLpLin_apply] using hnet x hx y hy

/-- Bounds a vector norm from its inner products with an internal unit-sphere net.

**Book Exercise 4.35.** -/
theorem exercise_4_35
    {N : Set E} {ε R : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hN : HDP.IsUnitSphereNet ε N) (x : E)
    (hR : 0 ≤ R) (hnet : ∀ y ∈ N, inner ℝ x y ≤ R) :
    ‖x‖ ≤ R / (1 - ε) := by
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    exact div_nonneg hR (sub_pos.mpr hε).le
  · have hR' : ‖x‖ * (1 - ε) ≤ R := by
      let z : E := ‖x‖⁻¹ • x
      have hz : ‖z‖ = 1 := by simp [z, norm_smul, hx]
      obtain ⟨y, hyN, hzy⟩ := hN.2 z hz
      have hxy : inner ℝ x y = ‖x‖ * inner ℝ z y := by
        have hscale : x = ‖x‖ • z := by simp [z, smul_smul, hx]
        calc
          inner ℝ x y = inner ℝ (‖x‖ • z) y :=
            congrArg (fun w => inner ℝ w y) hscale
          _ = ‖x‖ * inner ℝ z y := real_inner_smul_left z y ‖x‖
      have hinner : 1 - ε ≤ inner ℝ z y := by
        have hs := norm_sub_sq_real z y
        have hy := hN.1 y hyN
        have hsq : ‖z - y‖ ^ 2 ≤ ε ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hε0).2 hzy
        rw [hz, hy] at hs
        nlinarith
      have hr := hnet y hyN
      rw [hxy] at hr
      nlinarith [norm_nonneg x]
    exact (le_div_iff₀ (sub_pos.mpr hε)).2 hR'

/-- Re-exports the net-based quadratic-form control under the exercise-facing name.

**Book Exercise 4.36.** -/
alias exercise_4_36 := lemma_4_4_2

end HDP.Chapter4

end Source_12_NetNormBounds

/-! ## Material formerly in `13_SubGaussianMatrixNorms.lean` -/

section Source_13_SubGaussianMatrixNorms

/-!
# Chapter 4, §4.4.2: matrices with subgaussian entries

The concentration step is proved for the actual entry family indexed by
`Fin m × Fin n`; no row-independence assumption is added.  The explicit
constant inherited from Chapter 2 is `√30`.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator
  Topology Interval

namespace HDP.Chapter4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Integrating a Gaussian quadratic tail. The proof uses layer cake and a monotone change of
variables; in particular, it does not assume that the tail function is continuous.

**Lean implementation helper.** -/
private theorem integral_le_of_quadratic_gaussian_tail_subgaussian_matrix [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {Q0 a b : ℝ} (hQ0 : 0 ≤ Q0) (ha : 0 < a) (hb : 0 ≤ b)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | Q0 + a * t + b * t ^ 2 < Z ω} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2))) :
    (∫ ω, Z ω ∂μ) ≤ Q0 + 4 * a + 4 * b := by
  let Q : ℝ → ℝ := fun t => Q0 + a * t + b * t ^ 2
  let Q' : ℝ → ℝ := fun t => a + 2 * b * t
  let g : ℝ → ℝ := fun s => μ.real {ω | s < Z ω}
  have hg0 : ∀ s, 0 ≤ g s := fun s => by positivity
  have hg_le_one : ∀ s, g s ≤ 1 := by
    intro s
    simp [g]
  have hg_meas : Measurable g := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun s t hst =>
      measure_mono fun ω hω => lt_of_le_of_lt hst hω
  have hlayer := hZ.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall hZ0)
  have hkey := lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall hZ0) hZ.aemeasurable
  have hrhsfinite : (∫⁻ s in Ioi (0 : ℝ), μ {ω | s < Z ω}) < ∞ := by
    rw [← hkey]
    exact hZ.lintegral_lt_top
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    refine ⟨hg_meas.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun s => hg0 s)]
    have heq : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g s)) =
        ∫⁻ s in Ioi (0 : ℝ), μ {ω | s < Z ω} := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change ENNReal.ofReal (μ.real {ω | s < Z ω}) = μ {ω | s < Z ω}
      rw [Measure.real_def, ENNReal.ofReal_toReal]
      exact (measure_lt_top μ _).ne
    rw [heq]
    exact hrhsfinite
  have hQderiv : ∀ t, HasDerivAt Q (Q' t) t := by
    intro t
    have h := (((hasDerivAt_const t Q0).add
      ((hasDerivAt_id t).mul_const a)).add
        (((hasDerivAt_id t).pow 2).mul_const b))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp [Q']
      ring
    · filter_upwards [] with x
      dsimp [Q]
      ring
  have hQcont : Continuous Q := by fun_prop
  have hQ'tpos : ∀ t, 0 ≤ t → 0 ≤ Q' t := by
    intro t ht
    dsimp [Q']
    positivity
  have hQtop : Tendsto Q atTop atTop := by
    have hlin : Tendsto (fun t : ℝ => Q0 + a * t) atTop atTop := by
      simpa [add_comm] using
        (tendsto_id.const_mul_atTop ha).atTop_add tendsto_const_nhds
    apply tendsto_atTop_mono' atTop _ hlin
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    dsimp [Q]
    nlinarith [mul_nonneg hb (sq_nonneg t)]
  have htailReal : ∀ t : ℝ, 0 ≤ t →
      g (Q t) ≤ 2 * Real.exp (-t ^ 2) := by
    intro t ht
    have h := htail t ht
    have hfin : ENNReal.ofReal (2 * Real.exp (-t ^ 2)) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal
      (by positivity : 0 ≤ 2 * Real.exp (-t ^ 2))] at hreal
    simpa [g, Q, Measure.real_def] using hreal
  have hgauss0 : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) volume := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hgauss1 : Integrable
      (fun t : ℝ => t * Real.exp (-t ^ 2)) volume := by
    simpa using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hdom : IntegrableOn (fun t : ℝ =>
      2 * Real.exp (-t ^ 2) * Q' t) (Ioi 0) := by
    have hfull : Integrable (fun t : ℝ =>
        2 * Real.exp (-t ^ 2) * (a + 2 * b * t)) := by
      refine ((hgauss0.const_mul (2 * a)).add
        (hgauss1.const_mul (4 * b))).congr ?_
      filter_upwards [] with t
      simp only [Pi.add_apply]
      ring
    simpa [Q'] using hfull.integrableOn
  have hcomp_int : IntegrableOn
      (fun t => (g ∘ Q) t * Q' t) (Ioi 0) := by
    apply Integrable.mono' hdom
    · exact ((hg_meas.comp hQcont.measurable).aestronglyMeasurable.mul
        (by fun_prop : AEStronglyMeasurable Q' (volume.restrict (Ioi 0))))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (hg0 _) (hQ'tpos t ht0))]
      exact mul_le_mul_of_nonneg_right (htailReal t ht0) (hQ'tpos t ht0)
  have hg_tail_int : IntegrableOn g (Ioi Q0) :=
    hg_int.mono_set (Ioi_subset_Ioi hQ0)
  have hsubst : (∫ t in Ioi (0 : ℝ), (g ∘ Q) t * Q' t) =
      ∫ s in Ioi Q0, g s := by
    have hleft := intervalIntegral_tendsto_integral_Ioi
      0 hcomp_int tendsto_id
    have hright0 := intervalIntegral_tendsto_integral_Ioi
      Q0 hg_tail_int tendsto_id
    have hright := hright0.comp hQtop
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hcv := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := T) (g := g)
      hQcont.continuousOn
      (fun x hx => hQderiv x)
      (fun x hx => hQ'tpos x (by
        rw [min_eq_left hT.le, max_eq_right hT.le] at hx
        exact hx.1.le))
    simpa [Q] using hcv.symm
  have htailIntegral : (∫ s in Ioi Q0, g s) ≤ 4 * a + 4 * b := by
    rw [← hsubst]
    calc
      (∫ t in Ioi (0 : ℝ), (g ∘ Q) t * Q' t) ≤
          ∫ t in Ioi (0 : ℝ), 2 * Real.exp (-t ^ 2) * Q' t := by
        exact setIntegral_mono_on hcomp_int hdom measurableSet_Ioi fun t ht =>
          mul_le_mul_of_nonneg_right (htailReal t (mem_Ioi.mp ht).le)
            (hQ'tpos t (mem_Ioi.mp ht).le)
      _ ≤ 4 * a + 4 * b := by
        have h0 : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) ≤ 2 := by
          have heq0 : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) =
              Real.sqrt (Real.pi / 1) / 2 := by
            simpa using integral_gaussian_Ioi 1
          rw [heq0]
          have hsqrt : Real.sqrt (Real.pi / 1) ≤ 4 := by
            nlinarith [Real.sqrt_nonneg (Real.pi / 1),
              Real.sq_sqrt (by positivity : 0 ≤ Real.pi / 1),
              Real.pi_lt_four.le]
          linarith
        have h1 : (∫ t in Ioi (0 : ℝ), t * Real.exp (-t ^ 2)) ≤ 1 := by
          have heq := integral_rpow_mul_exp_neg_rpow
            (show (0 : ℝ) < 2 by norm_num)
            (show (-1 : ℝ) < 1 by norm_num)
          have heq' : (∫ t in Ioi (0 : ℝ),
              t * Real.exp (-t ^ 2)) = 1 / 2 := by
            convert heq using 1
            · apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              simp [Real.rpow_one]
            · norm_num
          rw [heq']
          norm_num
        have heq : (∫ t in Ioi (0 : ℝ),
            2 * Real.exp (-t ^ 2) * Q' t) =
            2 * a * (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) +
              4 * b * (∫ t in Ioi (0 : ℝ),
                t * Real.exp (-t ^ 2)) := by
          rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
          · apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            dsimp [Q']
            ring
          · exact (hgauss0.const_mul (2 * a)).integrableOn
          · exact (hgauss1.const_mul (4 * b)).integrableOn
        rw [heq]
        nlinarith
  rw [hlayer]
  have hsplit : (∫ s in Ioi (0 : ℝ), g s) =
      (∫ s in Ioc (0 : ℝ) Q0, g s) + ∫ s in Ioi Q0, g s := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hg_int.mono_set Ioc_subset_Ioi_self) hg_tail_int]
    rw [Ioc_union_Ioi_eq_Ioi hQ0]
  rw [hsplit]
  have hhead : (∫ s in Ioc (0 : ℝ) Q0, g s) ≤ Q0 := by
    calc
      _ ≤ ∫ _s in Ioc (0 : ℝ) Q0, (1 : ℝ) :=
        setIntegral_mono_on (hg_int.mono_set Ioc_subset_Ioi_self)
          (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
          fun s hs => hg_le_one s
      _ = Q0 := by simp [hQ0]
  linarith

namespace RandomMatrixBounds

/-- The fixed bilinear form used in the net proof of the corresponding theorem.

**Lean implementation helper.** -/
def randomMatrixBilinear {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
    (ω : Ω) : ℝ :=
  ∑ i, ∑ j, x j * y i * A ω i j

/-- Identifies random matrix bilinear with inner.

**Lean implementation helper.** -/
theorem randomMatrixBilinear_eq_inner {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (ω : Ω) :
    randomMatrixBilinear A x y ω =
      inner ℝ (WithLp.toLp 2 ((A ω).mulVec x.ofLp)) y := by
  unfold randomMatrixBilinear
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end RandomMatrixBounds

open RandomMatrixBounds

/-- Concentration step in the corresponding theorem: a fixed bilinear form of independent
centered entries is subgaussian with ψ₂ norm at most `√30 K`.

**Lean implementation helper.** -/
theorem fixed_bilinear_subGaussian [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : HDP.RandomMatrix.IndependentEntries A μ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    HDP.SubGaussian (randomMatrixBilinear A x y) μ ∧
      HDP.psi2Norm (randomMatrixBilinear A x y) μ ≤ Real.sqrt 30 * K := by
  classical
  let Y : (Fin m × Fin n) → Ω → ℝ :=
    fun ij ω => (x ij.2 * y ij.1) * A ω ij.1 ij.2
  have hYm : ∀ ij, AEMeasurable (Y ij) μ := fun ij =>
    (hAm ij.1 ij.2).const_mul (x ij.2 * y ij.1)
  have hYsub : ∀ ij, HDP.SubGaussian (Y ij) μ := fun ij =>
    (hsub ij.1 ij.2).const_mul (x ij.2 * y ij.1)
  have hYmean : ∀ ij, ∫ ω, Y ij ω ∂μ = 0 := by
    intro ij
    rw [show Y ij = fun ω => (x ij.2 * y ij.1) * A ω ij.1 ij.2 by rfl,
      integral_const_mul, hmean, mul_zero]
  have hYindep : iIndepFun Y μ :=
    hindep.comp
      (fun (ij : Fin m × Fin n) z => (x ij.2 * y ij.1) * z)
      (fun _ => by fun_prop)
  have hsumfun : (fun ω => ∑ ij, Y ij ω) = randomMatrixBilinear A x y := by
    funext ω
    rw [Fintype.sum_prod_type]
    rfl
  have hs0 := HDP.psi2Norm_fintype_sum_sq_le hYm hYsub hYmean hYindep
  have hs : HDP.SubGaussian (randomMatrixBilinear A x y) μ ∧
      HDP.psi2Norm (randomMatrixBilinear A x y) μ ^ 2 ≤
        30 * ∑ ij, HDP.psi2Norm (Y ij) μ ^ 2 := by
    simpa only [hsumfun] using hs0
  have hYi : ∀ ij : Fin m × Fin n,
      HDP.psi2Norm (Y ij) μ ≤ |x ij.2 * y ij.1| * K := by
    intro ij
    rw [show Y ij = fun ω => (x ij.2 * y ij.1) * A ω ij.1 ij.2 by rfl,
      HDP.psi2Norm_const_mul]
    exact mul_le_mul_of_nonneg_left (hpsi ij.1 ij.2) (abs_nonneg _)
  have hsum : ∑ ij, HDP.psi2Norm (Y ij) μ ^ 2 ≤ K ^ 2 := by
    calc
      ∑ ij, HDP.psi2Norm (Y ij) μ ^ 2 ≤
          ∑ ij : Fin m × Fin n, (|x ij.2 * y ij.1| * K) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij hij
        exact (sq_le_sq₀ (HDP.psi2Norm_nonneg _ μ)
          (mul_nonneg (abs_nonneg _) hK)).2 (hYi ij)
      _ = K ^ 2 * (∑ j, x j ^ 2) * (∑ i, y i ^ 2) := by
        rw [Fintype.sum_prod_type]
        simp_rw [abs_mul, mul_pow, sq_abs]
        calc
          ∑ i, ∑ j, (x j ^ 2 * y i ^ 2) * K ^ 2 =
              ∑ i, (y i ^ 2 * K ^ 2) * ∑ j, x j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = (∑ i, y i ^ 2 * K ^ 2) * ∑ j, x j ^ 2 := by
            rw [Finset.sum_mul]
          _ = K ^ 2 * (∑ j, x j ^ 2) * (∑ i, y i ^ 2) := by
            rw [← Finset.sum_mul]
            ac_rfl
      _ = K ^ 2 := by
        rw [← EuclideanSpace.real_norm_sq_eq x,
          ← EuclideanSpace.real_norm_sq_eq y, hx, hy]
        ring
  have hsquare : HDP.psi2Norm (randomMatrixBilinear A x y) μ ^ 2 ≤ 30 * K ^ 2 := by
    exact hs.2.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
  refine ⟨?_, ?_⟩
  · exact hs.1
  · have hR : 0 ≤ Real.sqrt 30 * K := mul_nonneg (Real.sqrt_nonneg _) hK
    apply (sq_le_sq₀ (HDP.psi2Norm_nonneg _ μ) hR).1
    calc
      HDP.psi2Norm (randomMatrixBilinear A x y) μ ^ 2 ≤ 30 * K ^ 2 := hsquare
      _ = (Real.sqrt 30 * K) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

/-- A fixed pair of unit vectors has the stated subgaussian bilinear-form tail, with the explicit
constant `c = 1/30`.

**Book (4.22).** -/
theorem fixed_bilinear_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : HDP.RandomMatrix.IndependentEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |randomMatrixBilinear A x y ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by
  have hs := fixed_bilinear_subGaussian A hAm hsub hmean hindep hK.le hpsi x hx y hy
  have hm : AEMeasurable (randomMatrixBilinear A x y) μ := by
    unfold randomMatrixBilinear
    fun_prop
  have hscale : 0 < Real.sqrt 30 * K := mul_pos (Real.sqrt_pos.2 (by norm_num)) hK
  have hmgf := HDP.psi2MGF_le_two_of_ge hm hs.1 hs.2 hscale
  have ht := HDP.subgaussian_iii_to_i hm hscale hmgf hu
  convert ht using 1
  congr 3
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

/-- A reusable internal quarter-net of the Euclidean unit sphere, with the volumetric cardinal
bound used throughout the random-matrix arguments.

**Book (4.20).** -/
theorem exists_quarter_unitSphereNet (d : ℕ) [NeZero d] :
    ∃ N : Finset (EuclideanSpace ℝ (Fin d)),
      HDP.IsUnitSphereNet (1 / 4 : ℝ) (N : Set (EuclideanSpace ℝ (Fin d))) ∧
      (N.card : ℝ≥0∞) ≤ (9 : ℝ≥0∞) ^ d := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin d)) :=
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  let ε : ℝ≥0 := ⟨1 / 4, by norm_num⟩
  have hcoverBound :
      (Metric.coveringNumber ε S : ℝ≥0∞) ≤ (9 : ℝ≥0∞) ^ d := by
    have hε : 0 < ε := by
      change (0 : ℝ) < 1 / 4
      norm_num
    have h := (corollary_4_2_11 (n := d) (ε := ε) hε).2.2
    have hbase : 2 / ε + 1 = (9 : ℝ≥0) := by
      apply NNReal.eq
      change (2 : ℝ) / (1 / 4) + 1 = 9
      norm_num
    rw [hbase] at h
    simpa [S] using h
  have hcoverFinite : Metric.coveringNumber ε S ≠ ⊤ := by
    intro htop
    rw [htop] at hcoverBound
    exact (not_le_of_gt (by simp : (9 : ℝ≥0∞) ^ d < ∞)) hcoverBound
  let Nset : Set (EuclideanSpace ℝ (Fin d)) := Metric.minimalCover ε S
  have hNfinite : Nset.Finite := Metric.finite_minimalCover
  let N : Finset (EuclideanSpace ℝ (Fin d)) := hNfinite.toFinset
  refine ⟨N, ?_, ?_⟩
  · constructor
    · intro x hx
      have hxNset : x ∈ Nset := by simpa [N] using hx
      have hxS : x ∈ S := Metric.minimalCover_subset hxNset
      simpa [S, Metric.mem_sphere, dist_zero_right] using hxS
    · intro x hx
      have hxS : x ∈ S := by
        simpa [S, Metric.mem_sphere, dist_zero_right] using hx
      obtain ⟨y, hyNset, hxy⟩ := (Metric.isCover_minimalCover hcoverFinite) hxS
      refine ⟨y, by simpa [N] using hyNset, ?_⟩
      have hdist : dist x y ≤ (1 / 4 : ℝ) := by
        change edist x y ≤ (ε : ℝ≥0∞) at hxy
        rw [edist_nndist] at hxy
        have hnn : nndist x y ≤ ε := ENNReal.coe_le_coe.mp hxy
        change (nndist x y : ℝ) ≤ (ε : ℝ)
        exact NNReal.coe_le_coe.mpr hnn
      simpa [dist_eq_norm] using hdist
  · have hcard : (N.card : ℕ∞) = Metric.coveringNumber ε S := by
      rw [← hNfinite.encard_eq_coe_toFinset_card]
      exact Metric.encard_minimalCover hcoverFinite
    have hcard' : (N.card : ℝ≥0∞) =
        (Metric.coveringNumber ε S : ℝ≥0∞) := by
      exact_mod_cast hcard
    rw [hcard']
    exact hcoverBound

/-- The chosen net threshold absorbs the `9^(m+n)` union factor into the tail bound `2 exp(-t²)`.

**Lean implementation helper.** -/
private theorem net_union_numerics {m n : ℕ} {K t : ℝ}
    (hK : 0 < K) (ht : 0 ≤ t) :
    (9 : ℝ≥0∞) ^ (m + n) *
        ENNReal.ofReal (2 * Real.exp (
          -(50 * K * (Real.sqrt m + Real.sqrt n + t)) ^ 2 / (30 * K ^ 2))) ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  let d : ℝ := m + n
  let s : ℝ := Real.sqrt m + Real.sqrt n + t
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsm : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt hm
  have hsn : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hssq : d + t ^ 2 ≤ s ^ 2 := by
    dsimp [d, s]
    nlinarith [Real.sqrt_nonneg (m : ℝ), Real.sqrt_nonneg (n : ℝ)]
  have hcancel :
      (50 * K * s) ^ 2 / (30 * K ^ 2) = (250 / 3 : ℝ) * s ^ 2 := by
    field_simp [hK.ne']
    ring
  have hexponent :
      3 * d + t ^ 2 ≤ (50 * K * s) ^ 2 / (30 * K ^ 2) := by
    rw [hcancel]
    have hd0 : 0 ≤ d := by dsimp [d]; positivity
    nlinarith [sq_nonneg t]
  have h9 : (9 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hpow : (9 : ℝ) ^ (m + n) ≤ Real.exp (3 * d) := by
    calc
      (9 : ℝ) ^ (m + n) ≤ (Real.exp 3) ^ (m + n) :=
        pow_le_pow_left₀ (by norm_num) h9 (m + n)
      _ = Real.exp (3 * d) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [d]
        push_cast
        ring
  have htail :
      Real.exp (-((50 * K * s) ^ 2 / (30 * K ^ 2))) ≤
        Real.exp (-(3 * d + t ^ 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hreal :
      (9 : ℝ) ^ (m + n) *
          (2 * Real.exp (-((50 * K * s) ^ 2 / (30 * K ^ 2)))) ≤
        2 * Real.exp (-t ^ 2) := by
    calc
      _ ≤ Real.exp (3 * d) * (2 * Real.exp (-(3 * d + t ^ 2))) :=
        mul_le_mul hpow (mul_le_mul_of_nonneg_left htail (by norm_num))
          (by positivity) (by positivity)
      _ = 2 * (Real.exp (3 * d) * Real.exp (-(3 * d + t ^ 2))) := by ring
      _ = 2 * Real.exp (3 * d + -(3 * d + t ^ 2)) := by rw [Real.exp_add]
      _ = 2 * Real.exp (-t ^ 2) := by ring_nf
  rw [show (9 : ℝ≥0∞) ^ (m + n) =
      ENNReal.ofReal ((9 : ℝ) ^ (m + n)) by
        rw [ENNReal.ofReal_pow]
        · norm_num
        · norm_num]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (9 : ℝ) ^ (m + n))]
  apply ENNReal.ofReal_le_ofReal
  simpa [s, neg_div] using hreal

/-- The finite-net part of the corresponding theorem, separated from the scalar concentration
input. This lets the symmetric-matrix theorem use the natural independent upper-triangle family
without manufacturing independence for the deterministic lower-triangle zero entries.

**Lean implementation helper.** -/
theorem matrixOpNorm_tail_of_fixed_bilinear_tail [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    {K : ℝ} (hK : 0 < K)
    (hfixed : ∀ (x : EuclideanSpace ℝ (Fin n)), ‖x‖ = 1 →
      ∀ (y : EuclideanSpace ℝ (Fin m)), ‖y‖ = 1 →
      ∀ (u : ℝ), 0 ≤ u →
        μ {ω | u ≤ |randomMatrixBilinear A x y ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))))
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (A ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  classical
  obtain ⟨N, hN, hNcard⟩ := exists_quarter_unitSphereNet n
  obtain ⟨M, hM, hMcard⟩ := exists_quarter_unitSphereNet m
  let P := N.product M
  let u : ℝ := 50 * K * (Real.sqrt m + Real.sqrt n + t)
  let E : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → Set Ω :=
    fun z => {ω | u ≤ |randomMatrixBilinear A z.1 z.2 ω|}
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hbad : {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (A ω)} ⊆ ⋃ z ∈ P, E z := by
    intro ω hω
    simp only [Set.mem_iUnion]
    by_contra hnone
    push Not at hnone
    have hnet : ∀ x ∈ (N : Set (EuclideanSpace ℝ (Fin n))),
        ∀ y ∈ (M : Set (EuclideanSpace ℝ (Fin m))),
          |inner ℝ (WithLp.toLp 2 ((A ω).mulVec x.ofLp)) y| ≤ u := by
      intro x hx y hy
      have hzP : (x, y) ∈ P := by
        apply Finset.mem_product.mpr
        exact ⟨by simpa using hx, by simpa using hy⟩
      have hlt : |randomMatrixBilinear A x y ω| < u := by
        have hnot := hnone (x, y) hzP
        change ¬ u ≤ |randomMatrixBilinear A x y ω| at hnot
        exact lt_of_not_ge hnot
      rw [← randomMatrixBilinear_eq_inner]
      exact hlt.le
    have hop := lemma_4_4_2 (A ω) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : 2 * (1 / 4 : ℝ) < 1) hN hM hu hnet
    have hop' : HDP.matrixOpNorm (A ω) ≤ 2 * u := by
      calc
        HDP.matrixOpNorm (A ω) ≤ u / (1 - 2 * (1 / 4 : ℝ)) := hop
        _ = 2 * u := by ring
    change 100 * K * (Real.sqrt m + Real.sqrt n + t) <
      HDP.matrixOpNorm (A ω) at hω
    dsimp [u] at hop'
    nlinarith
  have hpair : ∀ z ∈ P, μ (E z) ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by
    intro z hz
    have hz' := Finset.mem_product.mp (by simpa [P] using hz)
    exact hfixed z.1 (hN.1 z.1 hz'.1) z.2 (hM.1 z.2 hz'.2) u hu
  have hPcard : (P.card : ℝ≥0∞) ≤ (9 : ℝ≥0∞) ^ (m + n) := by
    calc
      (P.card : ℝ≥0∞) = (N.card : ℝ≥0∞) * (M.card : ℝ≥0∞) := by
        simp [P, Finset.card_product]
      _ ≤ (9 : ℝ≥0∞) ^ n * (9 : ℝ≥0∞) ^ m :=
        mul_le_mul' hNcard hMcard
      _ = (9 : ℝ≥0∞) ^ (m + n) := by
        rw [pow_add]
        ac_rfl
  calc
    μ {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (A ω)} ≤ μ (⋃ z ∈ P, E z) := measure_mono hbad
    _ ≤ ∑ z ∈ P, μ (E z) := measure_biUnion_finset_le P E
    _ ≤ ∑ _z ∈ P,
        ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by
      exact Finset.sum_le_sum fun z hz => hpair z hz
    _ = (P.card : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by simp
    _ ≤ (9 : ℝ≥0∞) ^ (m + n) *
        ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) :=
      mul_le_mul_of_nonneg_right hPcard (by positivity)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
      simpa [u] using net_union_numerics (m := m) (n := n) hK ht

/-- An `m × n` matrix with independent, centered subgaussian entries has operator norm of order
`K (√m + √n + t)`. The displayed constant `100` is absolute and explicit. Positive dimensions
are made explicit because the source proof uses nonempty unit spheres.

**Book Theorem 4.4.3.** -/
theorem theorem_4_4_3 [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : HDP.RandomMatrix.IndependentEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (A ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  apply matrixOpNorm_tail_of_fixed_bilinear_tail A hK ?_ ht
  intro x hx y hy u hu
  exact fixed_bilinear_tail A hAm hsub hmean hindep hK hpsi x hx y hy hu

/-! ## Remarks 4.4.4--4.4.6 and promoted exercises -/

/-- A finite random matrix with integrable entries is integrable as a matrix for the Euclidean
operator norm. The proof expands it in the matrix-unit basis, so it is independent of any hidden
equivalence of finite-dimensional norms.

**Lean implementation helper.** -/
theorem integrable_matrixOpNorm_of_subGaussian [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ) :
    Integrable (fun ω => HDP.matrixOpNorm (A ω)) μ := by
  classical
  have hentry : ∀ i j, Integrable (fun ω => A ω i j) μ := by
    intro i j
    apply memLp_one_iff_integrable.mp
    simpa only [ENNReal.ofReal_one] using
      ((hsub i j).memLp (hAm i j) (le_refl (1 : ℝ)))
  let B : Ω → Matrix (Fin m) (Fin n) ℝ := fun ω =>
    ∑ i, ∑ j, A ω i j • Matrix.single i j 1
  have hB : Integrable B μ := by
    dsimp [B]
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (hentry i j).smul_const (Matrix.single i j 1)
  have hBA : B = A := by
    funext ω
    ext i j
    simp only [B, Matrix.sum_apply]
    rw [Fintype.sum_eq_single i]
    · rw [Fintype.sum_eq_single j]
      · simp
      · intro b hb
        simp [Matrix.single, hb]
    · intro a ha
      simp [Matrix.single, ha]
  rw [hBA] at hB
  simpa [HDP.matrixOpNorm] using hB.norm

/-- Integrating the corresponding theorem gives the source's expectation bound. The absolute
constant is made explicit as `300`; the positive-dimension assumptions are exactly those needed
by the unit-sphere net proof.

**Book Exercise 4.41.** -/
theorem exercise_4_41a [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : HDP.RandomMatrix.IndependentEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K) :
    (∫ ω, HDP.matrixOpNorm (A ω) ∂μ) ≤
      300 * K * (Real.sqrt m + Real.sqrt n) := by
  let Z : Ω → ℝ := fun ω => HDP.matrixOpNorm (A ω)
  have hZ : Integrable Z μ :=
    integrable_matrixOpNorm_of_subGaussian A hAm hsub
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => HDP.matrixOpNorm_nonneg (A ω)
  let Q0 : ℝ := 100 * K * (Real.sqrt m + Real.sqrt n)
  let a : ℝ := 100 * K
  have hQ0 : 0 ≤ Q0 := by dsimp [Q0]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | Q0 + a * t + 0 * t ^ 2 < Z ω} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
    intro t ht
    have h := theorem_4_4_3 A hAm hsub hmean hindep hK hpsi ht
    dsimp [Q0, a, Z]
    have hset :
        {ω | 100 * K * (Real.sqrt m + Real.sqrt n) + 100 * K * t +
            0 * t ^ 2 < HDP.matrixOpNorm (A ω)} =
          {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
            HDP.matrixOpNorm (A ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      ring_nf
    rw [hset]
    exact h
  have hraw : (∫ ω, Z ω ∂μ) ≤ Q0 + 4 * a + 4 * 0 :=
    integral_le_of_quadratic_gaussian_tail_subgaussian_matrix Z hZ hZ0 hQ0 ha
      (by norm_num) htail
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hsm : 1 ≤ Real.sqrt m := by
    nlinarith [Real.sqrt_nonneg (m : ℝ),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  have hsn : 1 ≤ Real.sqrt n := by
    nlinarith [Real.sqrt_nonneg (n : ℝ),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  change (∫ ω, Z ω ∂μ) ≤ _
  dsimp [Q0, a] at hraw
  nlinarith

/-- Source-facing wrapper around the promoted the corresponding exercise.

**Book Remark 4.4.4.** -/
theorem remark_4_4_4_expectation [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : HDP.RandomMatrix.IndependentEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K) :
    (∫ ω, HDP.matrixOpNorm (A ω) ∂μ) ≤
      300 * K * (Real.sqrt m + Real.sqrt n) :=
  exercise_4_41a A hAm hsub hmean hindep hK hpsi

/-- A matrix whose entries all have modulus one (in particular, every Rademacher realization)
already has operator norm at least half of `√m + √n`, deterministically.

**Book Remark 4.4.5.** -/
theorem remark_4_4_5_optimality {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) (hunit : ∀ i j, |A i j| = 1) :
    (1 / 2 : ℝ) * (Real.sqrt m + Real.sqrt n) ≤ HDP.matrixOpNorm A := by
  let i0 : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩
  let j0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hentrySq : ∀ i j, A i j ^ 2 = 1 := by
    intro i j
    have h := congrArg (fun z : ℝ => z ^ 2) (hunit i j)
    simpa [sq_abs] using h
  have hcolSq :
      ‖(WithLp.toLp 2 (A.col j0) : EuclideanSpace ℝ (Fin m))‖ ^ 2 = m := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : Fin m, A i j0 ^ 2) = (m : ℝ)
    simp_rw [hentrySq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hrowSq :
      ‖(WithLp.toLp 2 (A.row i0) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = n := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin n, A i0 j ^ 2) = (n : ℝ)
    simp_rw [hentrySq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hcolNorm :
      ‖(WithLp.toLp 2 (A.col j0) : EuclideanSpace ℝ (Fin m))‖ =
        Real.sqrt m := by
    calc
      _ = Real.sqrt
          (‖(WithLp.toLp 2 (A.col j0) : EuclideanSpace ℝ (Fin m))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt m := by rw [hcolSq]
  have hrowNorm :
      ‖(WithLp.toLp 2 (A.row i0) : EuclideanSpace ℝ (Fin n))‖ =
        Real.sqrt n := by
    calc
      _ = Real.sqrt
          (‖(WithLp.toLp 2 (A.row i0) : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt n := by rw [hrowSq]
  have hcol := exercise_4_7a_column_le A j0
  have hrow := exercise_4_7c_row_le A i0
  rw [hcolNorm] at hcol
  rw [hrowNorm] at hrow
  linarith

/-- A matrix assembled from a row family has the expected bilinear form.

**Lean implementation helper.** -/
lemma randomMatrixBilinear_of_rows {m n : ℕ}
    (R : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    (fun ω => ∑ i, y i * inner ℝ (R i ω) x) =
      randomMatrixBilinear (fun ω => Matrix.of fun i j => R i ω j) x y := by
  funext ω
  unfold randomMatrixBilinear
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Independence is unnecessary once every unit bilinear form is subgaussian with the stated
uniform ψ₂ bound.

**Book Exercise 4.43.** -/
theorem exercise_4_43a [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    {K : ℝ} (hK : 0 < K)
    (hm : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 →
        AEMeasurable (randomMatrixBilinear A x y) μ)
    (hsub : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 →
        HDP.SubGaussian (randomMatrixBilinear A x y) μ)
    (hpsi : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 →
        HDP.psi2Norm (randomMatrixBilinear A x y) μ ≤ Real.sqrt 30 * K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (A ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  apply matrixOpNorm_tail_of_fixed_bilinear_tail A hK ?_ ht
  intro x hx y hy u hu
  have hscale : 0 < Real.sqrt 30 * K := by positivity
  have hmgf := HDP.psi2MGF_le_two_of_ge (hm x hx y hy)
    (hsub x hx y hy) (hpsi x hx y hy) hscale
  have htail := HDP.subgaussian_iii_to_i (hm x hx y hy) hscale hmgf hu
  convert htail using 1
  congr 3
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

/-- Independent centered subgaussian rows suffice even when entries within each row are
dependent.

**Book Exercise 4.43.** -/
theorem exercise_4_43b_independentRows [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (R : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hRm : ∀ i v, AEMeasurable (fun ω => inner ℝ (R i ω) v) μ)
    (hsub : ∀ i, HDP.SubGaussianVector (R i) μ)
    (hmean : ∀ i v, ∫ ω, inner ℝ (R i ω) v ∂μ = 0)
    (hindep : iIndepFun R μ)
    (hbounded : ∀ i, BddAbove {r : ℝ |
      ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (R i ω) w) μ})
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HDP.psi2NormVector (R i) μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (Matrix.of fun i j => R i ω j)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  apply exercise_4_43a (A := fun ω => Matrix.of fun i j => R i ω j) hK ?_ ?_ ?_ ht
  · intro x hx y hy
    rw [← randomMatrixBilinear_of_rows R x y]
    exact Finset.aemeasurable_fun_sum Finset.univ fun i hi =>
      (hRm i x).const_mul (y i)
  · intro x hx y hy
    have hs := HDP.Chapter3.exercise_3_34 R hRm hsub hmean hindep
      hbounded hK.le hpsi y x
    rw [← randomMatrixBilinear_of_rows R x y]
    exact hs.1
  · intro x hx y hy
    have hs := HDP.Chapter3.exercise_3_34 R hRm hsub hmean hindep
      hbounded hK.le hpsi y x
    rw [← randomMatrixBilinear_of_rows R x y]
    simpa [hx, hy, mul_assoc] using hs.2

/-- This is the transpose of the independent-row statement.

**Book Exercise 4.43.** -/
theorem exercise_4_43b_independentColumns [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (C : Fin n → Ω → EuclideanSpace ℝ (Fin m))
    (hCm : ∀ j v, AEMeasurable (fun ω => inner ℝ (C j ω) v) μ)
    (hsub : ∀ j, HDP.SubGaussianVector (C j) μ)
    (hmean : ∀ j v, ∫ ω, inner ℝ (C j ω) v ∂μ = 0)
    (hindep : iIndepFun C μ)
    (hbounded : ∀ j, BddAbove {r : ℝ |
      ∃ w : EuclideanSpace ℝ (Fin m), ‖w‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (C j ω) w) μ})
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ j, HDP.psi2NormVector (C j) μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 100 * K * (Real.sqrt m + Real.sqrt n + t) <
        HDP.matrixOpNorm (Matrix.of fun i j => C j ω i)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  have h := exercise_4_43b_independentRows C hCm hsub hmean hindep hbounded hK hpsi ht
  convert h using 1
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [show (Matrix.of fun i j => C j ω i) =
      (Matrix.of (fun j i => C j ω i)).transpose by rfl,
    HDP.matrixOpNorm_transpose]
  ring_nf

/-- Re-exports the independent-row subgaussian matrix bound under the remark-facing name.

**Book Remark 4.4.6.** -/
alias remark_4_4_6_independentRows := exercise_4_43b_independentRows

/-- Re-exports the independent-column subgaussian matrix bound under the remark-facing name.

**Book Remark 4.4.6.** -/
alias remark_4_4_6_independentColumns := exercise_4_43b_independentColumns

/-- Expectation bound for the maximum absolute value of a finite subgaussian family; this is the
absolute-value counterpart of (2.22).

**Lean implementation helper.** -/
theorem expectation_max_abs_le [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin (N + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun i => |X i ω|) ∂μ) ≤
        2 * Real.sqrt (Real.log ((N : ℝ) + 2)) * K := by
  let Z : Ω → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty
    (fun i => |X i ω|)
  have hZm : Measurable Z := by
    have h := Finset.measurable_sup' Finset.univ_nonempty fun i hi =>
      (hXm i).abs
    have heq : (Finset.univ.sup' Finset.univ_nonempty
        fun i ω => |X i ω|) = Z := by
      funext ω
      simp only [Z, Finset.sup'_apply]
    rwa [heq] at h
  have hZsub := (HDP.psi2Norm_max_abs_le hXm hX hK hKb).1
  have hZpsi := HDP.psi2Norm_max_abs_le' hXm hX hK hKb
  have hZint : Integrable Z μ :=
    (hZsub.memLp hZm.aemeasurable (le_refl (1 : ℝ))).integrable
      (by norm_num)
  have hZ0 : ∀ ω, 0 ≤ Z ω := by
    intro ω
    obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := Fin (N + 2))
    exact (abs_nonneg (X i ω)).trans
      (Finset.le_sup' (fun j => |X j ω|) hi)
  have hmb := hZsub.moment_bound hZm.aemeasurable (le_refl (1 : ℝ))
  have hL1 : HDP.Chapter1.lpNormRV Z 1 μ = ∫ ω, |Z ω| ∂μ := by
    have hcong : (fun ω => |Z ω| ^ (1 : ℝ)) =ᵐ[μ] fun ω => |Z ω| :=
      Filter.Eventually.of_forall fun ω => Real.rpow_one _
    rw [HDP.Chapter1.lpNormRV, integral_congr_ae hcong,
      show (1 : ℝ) / 1 = 1 from by norm_num, Real.rpow_one]
  calc
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun i => |X i ω|) ∂μ) = ∫ ω, Z ω ∂μ := rfl
    _ = ∫ ω, |Z ω| ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        (abs_of_nonneg (hZ0 ω)).symm
    _ = HDP.Chapter1.lpNormRV Z 1 μ := hL1.symm
    _ ≤ HDP.psi2Norm Z μ * Real.sqrt 1 := hmb
    _ = HDP.psi2Norm Z μ := by rw [Real.sqrt_one, mul_one]
    _ ≤ 2 * Real.sqrt (Real.log ((N : ℝ) + 2)) * K := hZpsi

/-- The printed display omits expectation. For dimensions at least two, the expected `1 → ∞`
norm has the stated logarithmic bound.

**Book Exercise 4.44.** -/
theorem exercise_4_44a_expectation [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAm : ∀ i j, Measurable (fun ω => A ω i j))
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K) :
    (∫ ω, matrixLpToLpNorm 1 ∞ (A ω) ∂μ) ≤
      2 * K * (Real.sqrt (Real.log m) + Real.sqrt (Real.log n)) := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let N : ℕ := m * n - 2
  have hmn : 2 ≤ m * n := by nlinarith
  have hEq : N + 2 = m * n := Nat.sub_add_cancel hmn
  let eProd : (Fin m × Fin n) ≃ Fin (m * n) := by
    simpa using Fintype.equivFin (Fin m × Fin n)
  let e : Fin (N + 2) ≃ (Fin m × Fin n) :=
    (finCongr hEq).trans eProd.symm
  let X : Fin (N + 2) → Ω → ℝ := fun r ω => A ω (e r).1 (e r).2
  have hXm : ∀ r, Measurable (X r) := fun r => hAm (e r).1 (e r).2
  have hXsub : ∀ r, HDP.SubGaussian (X r) μ :=
    fun r => hsub (e r).1 (e r).2
  have hXpsi : ∀ r, HDP.psi2Norm (X r) μ ≤ K :=
    fun r => hpsi (e r).1 (e r).2
  have hmax := expectation_max_abs_le hXm hXsub hK hXpsi
  have hpoint : ∀ ω, matrixLpToLpNorm 1 ∞ (A ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun r => |X r ω|) := by
    intro ω
    rw [exercise_4_19a_one_to_infty]
    apply le_antisymm
    · obtain ⟨i, j, hij⟩ := exists_entry_eq_maxAbsEntry (A ω)
      rw [← hij]
      have hr : e (e.symm (i, j)) = (i, j) := e.apply_symm_apply (i, j)
      simpa [X, hr] using
        (Finset.le_sup' (fun r => |X r ω|)
          (Finset.mem_univ (e.symm (i, j))))
    · apply Finset.sup'_le
      intro r hr
      exact abs_entry_le_maxAbsEntry (A ω) (e r).1 (e r).2
  rw [show (fun ω => matrixLpToLpNorm 1 ∞ (A ω)) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun r => |X r ω|)) by
        funext ω
        exact hpoint ω]
  calc
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun r => |X r ω|) ∂μ) ≤
        2 * Real.sqrt (Real.log ((N : ℝ) + 2)) * K := hmax
    _ ≤ 2 * K * (Real.sqrt (Real.log m) + Real.sqrt (Real.log n)) := by
      have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
      have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hm)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
      have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
      have hcast : ((N : ℝ) + 2) = (m : ℝ) * n := by exact_mod_cast hEq
      rw [hcast, Real.log_mul hmR.ne' hnR.ne']
      have hsqrt : Real.sqrt (Real.log m + Real.log n) ≤
          Real.sqrt (Real.log m) + Real.sqrt (Real.log n) := by
        have hsq1 := Real.sq_sqrt (add_nonneg hlogm hlogn)
        have hsqm := Real.sq_sqrt hlogm
        have hsqn := Real.sq_sqrt hlogn
        nlinarith [Real.sqrt_nonneg (Real.log m),
          Real.sqrt_nonneg (Real.log n),
          Real.sqrt_nonneg (Real.log m + Real.log n)]
      nlinarith [hK.le]

/-- The printed display omits expectation. The expected `1 → 2` norm equals the expected
transpose `2 → ∞` norm and obeys the source-scale bound.

**Book Exercise 4.44.** -/
theorem exercise_4_44b_expectation [IsProbabilityMeasure μ]
    {N m : ℕ} (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin (N + 2)) ℝ)
    (hAm : ∀ i j, Measurable (fun ω => A ω i j))
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hsecond : ∀ i j, ∫ ω, A ω i j ^ 2 ∂μ = 1)
    (hindep : HDP.RandomMatrix.IndependentEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K) :
    (∫ ω, matrixLpToLpNorm 1 2 (A ω) ∂μ) =
        ∫ ω, matrixLpToLpNorm 2 ∞ (A ω).transpose ∂μ ∧
      (∫ ω, matrixLpToLpNorm 1 2 (A ω) ∂μ) ≤
        Real.sqrt m + 2 * Real.sqrt (Real.log ((N : ℝ) + 2)) *
          (HDP.Chapter3.normConcentrationConstant * K ^ 2) := by
  let X : Fin (N + 2) → Ω → EuclideanSpace ℝ (Fin m) :=
    fun j ω => WithLp.toLp 2 (A ω |>.col j)
  have hXm : ∀ j, Measurable (X j) := by
    intro j
    have hpi : Measurable (fun ω => fun i => A ω i j) :=
      measurable_pi_lambda _ fun i => hAm i j
    exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp hpi
  have hcolIndep : ∀ j, iIndepFun (fun i ω => X j ω i) μ := by
    intro j
    change iIndepFun (fun i ω => A ω i j) μ
    refine ProbabilityTheory.iIndepFun.precomp
      (g := fun i : Fin m => (i, j)) ?_ hindep
    intro i l h
    exact congrArg Prod.fst h
  have hmax := HDP.Chapter3.exercise_3_13a (N := N) (n := m) hm hXm
    (fun j i => hsub i j) (fun j i => hsecond i j) hcolIndep hK
    (fun j i => hpsi i j)
  have hpoint : ∀ ω, matrixLpToLpNorm 1 2 (A ω) =
      HDP.Chapter3.maxNormVectors X ω := by
    intro ω
    rw [exercise_4_19b_one_to_two]
    apply le_antisymm
    · obtain ⟨j, hj⟩ := exists_column_eq_maxColumnL2Norm (A ω)
      rw [← hj]
      exact Finset.le_sup' (fun r => ‖X r ω‖) (Finset.mem_univ j)
    · apply Finset.sup'_le
      intro j hj
      exact column_norm_le_maxColumnL2Norm (A ω) j
  constructor
  · apply integral_congr_ae
    filter_upwards [] with ω
    rw [exercise_4_19b_one_to_two, exercise_4_19b_two_to_infty]
    rfl
  · rw [show (fun ω => matrixLpToLpNorm 1 2 (A ω)) =
        HDP.Chapter3.maxNormVectors X by
      funext ω
      exact hpoint ω]
    exact hmax

end HDP.Chapter4

end Source_13_SubGaussianMatrixNorms

/-! ## Material formerly in `14_SymmetricSubGaussianMatrices.lean` -/

section Source_14_SymmetricSubGaussianMatrices

/-!
# Chapter 4, §4.4.3: symmetric subgaussian matrices

The source assumes independence only on and above the diagonal.  We encode
that family by the upper-half matrix below; its lower entries are deterministic
zeros and its diagonal is divided by two, so a symmetric matrix is exactly the
sum of this matrix and its transpose.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal Matrix.Norms.L2Operator

namespace HDP.Chapter4

open RandomMatrixBounds

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Upper triangular half of a matrix, with half of the diagonal.

**Lean implementation helper.** -/
noncomputable def upperHalf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i < j then A i j else if i = j then A i j / 2 else 0

/-- The natural index type for the on-and-above-diagonal coordinates. -/
abbrev UpperIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≤ ij.2}

/-- Independence of the on-and-above-diagonal coordinates, expressed without duplicating
symmetric lower-triangular entries or adding deterministic dummy coordinates.

**Lean implementation helper.** -/
def IndependentUpperEntries {n : ℕ}
    (A : Ω → Matrix (Fin n) (Fin n) ℝ) (μ : Measure Ω) : Prop :=
  iIndepFun (fun ij : UpperIndex n => fun ω => A ω ij.1.1 ij.1.2) μ

/-- A symmetric matrix is recovered by adding its upper-half matrix to its transpose.

**Lean implementation helper.** -/
theorem upperHalf_add_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) : upperHalf A + (upperHalf A).transpose = A := by
  ext i j
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt_of_ge hij.le
    have hne : i ≠ j := ne_of_lt hij
    simp [upperHalf, hij, hji, hne.symm]
  · by_cases hji : j < i
    · have hne : i ≠ j := ne_of_gt hji
      simpa [upperHalf, hij, hji, hne] using hA.apply i j
    · have heq : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
      subst j
      simp [upperHalf]

set_option maxHeartbeats 800000 in
-- The finite upper-triangle independence expansion needs extra elaboration time.
/-- Fixed-pair concentration for the upper-half matrix. Only the natural upper-triangle family
is assumed independent; the proof sums precisely over that subtype and then compares its
coefficient square-sum with the full product square-sum.

**Lean implementation helper.** -/
theorem fixed_bilinear_upperHalf_tail [IsProbabilityMeasure μ]
    {n : ℕ} (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : IndependentUpperEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |randomMatrixBilinear (fun ω => upperHalf (A ω)) x y ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by
  classical
  let U : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => upperHalf (A ω)
  have hUm : ∀ ij : UpperIndex n,
      AEMeasurable (fun ω => U ω ij.1.1 ij.1.2) μ := by
    intro ij
    by_cases hlt : ij.1.1 < ij.1.2
    · simpa [U, upperHalf, hlt] using hAm ij.1.1 ij.1.2
    · have heq : ij.1.1 = ij.1.2 := le_antisymm ij.2 (not_lt.mp hlt)
      simpa [U, upperHalf, hlt, heq, div_eq_mul_inv] using
        (hAm ij.1.1 ij.1.2).mul_const (2 : ℝ)⁻¹
  have hUsub : ∀ ij : UpperIndex n,
      HDP.SubGaussian (fun ω => U ω ij.1.1 ij.1.2) μ := by
    intro ij
    by_cases hlt : ij.1.1 < ij.1.2
    · simpa [U, upperHalf, hlt] using hsub ij.1.1 ij.1.2
    · have heq : ij.1.1 = ij.1.2 := le_antisymm ij.2 (not_lt.mp hlt)
      simpa [U, upperHalf, hlt, heq, div_eq_mul_inv, mul_comm] using
        (hsub ij.1.1 ij.1.2).const_mul (2 : ℝ)⁻¹
  have hUmean : ∀ ij : UpperIndex n,
      ∫ ω, U ω ij.1.1 ij.1.2 ∂μ = 0 := by
    intro ij
    by_cases hlt : ij.1.1 < ij.1.2
    · simpa [U, upperHalf, hlt] using hmean ij.1.1 ij.1.2
    · have heq : ij.1.1 = ij.1.2 := le_antisymm ij.2 (not_lt.mp hlt)
      simp [U, upperHalf, heq, integral_div, hmean]
  have hUpsi : ∀ ij : UpperIndex n,
      HDP.psi2Norm (fun ω => U ω ij.1.1 ij.1.2) μ ≤ K := by
    intro ij
    by_cases hlt : ij.1.1 < ij.1.2
    · simpa [U, upperHalf, hlt] using hpsi ij.1.1 ij.1.2
    · have heq : ij.1.1 = ij.1.2 := le_antisymm ij.2 (not_lt.mp hlt)
      rw [show (fun ω => U ω ij.1.1 ij.1.2) =
          fun ω => (2 : ℝ)⁻¹ * A ω ij.1.1 ij.1.2 by
            funext ω; simp [U, upperHalf, heq, div_eq_mul_inv, mul_comm],
        HDP.psi2Norm_const_mul]
      have hp := hpsi ij.1.1 ij.1.2
      norm_num at ⊢
      nlinarith [HDP.psi2Norm_nonneg (fun ω => A ω ij.1.1 ij.1.2) μ]
  have hUindep : iIndepFun
      (fun ij : UpperIndex n => fun ω => U ω ij.1.1 ij.1.2) μ := by
    let g : UpperIndex n → ℝ → ℝ := fun ij z =>
      if ij.1.1 < ij.1.2 then z else z / 2
    have hg := hindep.comp g (fun ij => by
      by_cases hlt : ij.1.1 < ij.1.2
      · simp only [g, if_pos hlt]
        fun_prop
      · simp only [g, if_neg hlt]
        fun_prop)
    convert hg using 1
    funext ij ω
    by_cases hlt : ij.1.1 < ij.1.2
    · simp [U, upperHalf, g, hlt]
    · have heq : ij.1.1 = ij.1.2 := le_antisymm ij.2 (not_lt.mp hlt)
      simp [U, upperHalf, g, heq]
  let Y : UpperIndex n → Ω → ℝ := fun ij ω =>
    (x ij.1.2 * y ij.1.1) * U ω ij.1.1 ij.1.2
  have hYm : ∀ ij, AEMeasurable (Y ij) μ := fun ij =>
    (hUm ij).const_mul (x ij.1.2 * y ij.1.1)
  have hYsub : ∀ ij, HDP.SubGaussian (Y ij) μ := fun ij =>
    (hUsub ij).const_mul (x ij.1.2 * y ij.1.1)
  have hYmean : ∀ ij, ∫ ω, Y ij ω ∂μ = 0 := by
    intro ij
    rw [show Y ij = fun ω => (x ij.1.2 * y ij.1.1) *
        U ω ij.1.1 ij.1.2 by rfl, integral_const_mul, hUmean, mul_zero]
  have hYindep : iIndepFun Y μ :=
    hUindep.comp (fun ij z => (x ij.1.2 * y ij.1.1) * z) (fun _ => by fun_prop)
  have hsumfun : (fun ω => ∑ ij, Y ij ω) =
      randomMatrixBilinear U x y := by
    funext ω
    change (∑ ij : UpperIndex n,
        (x ij.1.2 * y ij.1.1) * U ω ij.1.1 ij.1.2) =
      ∑ i, ∑ j, (x j * y i) * U ω i j
    let f : Fin n × Fin n → ℝ := fun ij =>
      (x ij.2 * y ij.1) * U ω ij.1 ij.2
    change (∑ ij : UpperIndex n,
        (x ij.1.2 * y ij.1.1) * U ω ij.1.1 ij.1.2) =
      ∑ i, ∑ j, f (i, j)
    rw [← Fintype.sum_prod_type]
    change (∑ ij : UpperIndex n, f ij.1) = ∑ ij, f ij
    rw [← Finset.sum_subtype (Finset.univ.filter
      (fun ij : Fin n × Fin n => ij.1 ≤ ij.2)) (by simp)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ij _
    by_cases hle : ij.1 ≤ ij.2
    · simp [hle]
    · have hlt : ¬ ij.1 < ij.2 := fun h => hle h.le
      have hne : ij.1 ≠ ij.2 := fun h => hle h.le
      simp [hle, f, U, upperHalf, hlt, hne]
  have hs0 := HDP.psi2Norm_fintype_sum_sq_le hYm hYsub hYmean hYindep
  have hYi : ∀ ij, HDP.psi2Norm (Y ij) μ ≤
      |x ij.1.2 * y ij.1.1| * K := by
    intro ij
    rw [show Y ij = fun ω => (x ij.1.2 * y ij.1.1) *
        U ω ij.1.1 ij.1.2 by rfl, HDP.psi2Norm_const_mul]
    exact mul_le_mul_of_nonneg_left (hUpsi ij) (abs_nonneg _)
  have hcoeff : ∑ ij : UpperIndex n,
      (|x ij.1.2 * y ij.1.1| * K) ^ 2 ≤ K ^ 2 := by
    let f : Fin n × Fin n → ℝ := fun ij =>
      (|x ij.2 * y ij.1| * K) ^ 2
    have hsubset : (∑ ij : UpperIndex n, f ij.1) ≤
        ∑ ij : Fin n × Fin n, f ij := by
      calc
        (∑ ij : UpperIndex n, f ij.1) ≤
            (∑ ij : UpperIndex n, f ij.1) +
              ∑ ij : {ij : Fin n × Fin n // ¬ ij.1 ≤ ij.2}, f ij.1 := by
                exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        _ = ∑ ij : Fin n × Fin n, f ij :=
          Fintype.sum_subtype_add_sum_subtype
            (fun ij : Fin n × Fin n => ij.1 ≤ ij.2) f
    have hfull : (∑ ij : Fin n × Fin n, f ij) = K ^ 2 := by
      calc
        ∑ ij : Fin n × Fin n, f ij =
            K ^ 2 * (∑ j, x j ^ 2) * (∑ i, y i ^ 2) := by
          rw [Fintype.sum_prod_type]
          simp_rw [f, abs_mul, mul_pow, sq_abs]
          calc
            ∑ i, ∑ j, (x j ^ 2 * y i ^ 2) * K ^ 2 =
                ∑ i, (y i ^ 2 * K ^ 2) * ∑ j, x j ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = (∑ i, y i ^ 2 * K ^ 2) * ∑ j, x j ^ 2 := by
              rw [Finset.sum_mul]
            _ = K ^ 2 * (∑ j, x j ^ 2) * (∑ i, y i ^ 2) := by
              rw [← Finset.sum_mul]
              ac_rfl
        _ = K ^ 2 := by
          rw [← EuclideanSpace.real_norm_sq_eq x,
            ← EuclideanSpace.real_norm_sq_eq y, hx, hy]
          ring
    have hactive : (∑ ij : UpperIndex n, f ij.1) ≤ K ^ 2 :=
      hsubset.trans_eq hfull
    simpa only [f] using hactive
  have hsum : ∑ ij : UpperIndex n, HDP.psi2Norm (Y ij) μ ^ 2 ≤ K ^ 2 := by
    apply (Finset.sum_le_sum fun ij _ =>
      (sq_le_sq₀ (HDP.psi2Norm_nonneg (Y ij) μ)
        (mul_nonneg (abs_nonneg _) hK.le)).2 (hYi ij)).trans
    exact hcoeff
  have hsquare : HDP.psi2Norm (fun ω => ∑ ij, Y ij ω) μ ^ 2 ≤
      30 * K ^ 2 := hs0.2.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hnorm : HDP.psi2Norm (fun ω => ∑ ij, Y ij ω) μ ≤
      Real.sqrt 30 * K := by
    apply (sq_le_sq₀ (HDP.psi2Norm_nonneg _ μ)
      (mul_nonneg (Real.sqrt_nonneg _) hK.le)).1
    calc
      HDP.psi2Norm (fun ω => ∑ ij, Y ij ω) μ ^ 2 ≤ 30 * K ^ 2 := hsquare
      _ = (Real.sqrt 30 * K) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]
  rw [hsumfun] at hs0 hnorm
  have hm : AEMeasurable (randomMatrixBilinear U x y) μ := by
    rw [← hsumfun]
    exact Finset.aemeasurable_fun_sum Finset.univ (fun ij _ => hYm ij)
  have hscale : 0 < Real.sqrt 30 * K := by positivity
  have hmgf := HDP.psi2MGF_le_two_of_ge hm hs0.1 hnorm hscale
  have ht := HDP.subgaussian_iii_to_i hm hscale hmgf hu
  convert ht using 1
  congr 3
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

/-- A symmetric matrix with independent centered subgaussian upper-triangular coordinates has
norm `O(K(√n+t))`. The explicit absolute constant is `400`; the probability bound `2 exp(-t²)`
is slightly stronger than the source's `4 exp(-t²)`.

**Book Corollary 4.4.7.** -/
theorem corollary_4_4_7 [IsProbabilityMeasure μ]
    {n : ℕ} [NeZero n]
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ ω, (A ω).IsSymm)
    (hAm : ∀ i j, AEMeasurable (fun ω => A ω i j) μ)
    (hsub : ∀ i j, HDP.SubGaussian (fun ω => A ω i j) μ)
    (hmean : ∀ i j, ∫ ω, A ω i j ∂μ = 0)
    (hindep : IndependentUpperEntries A μ)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i j, HDP.psi2Norm (fun ω => A ω i j) μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 400 * K * (Real.sqrt n + t) < HDP.matrixOpNorm (A ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  let U : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => upperHalf (A ω)
  have hUtail := matrixOpNorm_tail_of_fixed_bilinear_tail U hK (by
    intro x hx y hy u hu
    exact fixed_bilinear_upperHalf_tail A hAm hsub hmean hindep hK hpsi
      x y hx hy hu) ht
  have hop (ω : Ω) : HDP.matrixOpNorm (A ω) ≤ 2 * HDP.matrixOpNorm (U ω) := by
    rw [← upperHalf_add_transpose (hsymm ω)]
    calc
      HDP.matrixOpNorm (upperHalf (A ω) + (upperHalf (A ω)).transpose) ≤
          HDP.matrixOpNorm (upperHalf (A ω)) +
            HDP.matrixOpNorm ((upperHalf (A ω)).transpose) := HDP.matrixOpNorm_add_le _ _
      _ = 2 * HDP.matrixOpNorm (U ω) := by simp [U, two_mul]
  calc
    μ {ω | 400 * K * (Real.sqrt n + t) < HDP.matrixOpNorm (A ω)} ≤
        μ {ω | 100 * K * (Real.sqrt n + Real.sqrt n + t) <
          HDP.matrixOpNorm (U ω)} := by
      apply measure_mono
      intro ω hω
      change 400 * K * (Real.sqrt n + t) < HDP.matrixOpNorm (A ω) at hω
      change 100 * K * (Real.sqrt n + Real.sqrt n + t) < HDP.matrixOpNorm (U ω)
      have := hop ω
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := hUtail

end HDP.Chapter4

end Source_14_SymmetricSubGaussianMatrices

/-! ## Material formerly in `15_StochasticBlockModel.lean` -/

section Source_15_StochasticBlockModel

/-!
# Chapter 4, §4.5.1: the stochastic block model

the source's model allows self-loops, so this file uses the shared `Sym2`
coordinate model rather than `SimpleGraph`.  For `2k` vertices the expected
adjacency matrix has the exact decomposition

`((p+q)/2) 1 1ᵀ + ((p-q)/2) g gᵀ`,

where `g` is the balanced community-sign vector.  This proves, rather than
assumes, the two advertised eigenpairs and the rank-two assertion.
-/

open Matrix
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HDP.Chapter4

open HDP

/-- The balanced, loop-aware two-community stochastic block model on `2k` vertices.

**Book Definition 4.5.1.** -/
noncomputable def definition_4_5_1 (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) : Measure (SBMSample k) :=
  stochasticBlockModel k p q

/-- Balanced two-community stochastic block model with within/between probabilities and
self-loops.

**Book Definition 4.5.1.** -/
theorem definition_4_5_1_isProbabilityMeasure (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (definition_4_5_1 k p q) := by
  unfold definition_4_5_1
  infer_instance

/-- The coordinate expectations in the corresponding definition are exactly `p` within
communities and `q` across communities.

**Book Chapter 4, pp.119--122, SBM signal calculation.** -/
theorem definition_4_5_1_expectedAdjacency (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) (i j : SBMVertex k) :
    ∫ G, sbmAdjacencyMatrix G i j ∂(definition_4_5_1 k p q) =
      sbmExpectedAdjacency k p q i j := by
  exact integral_sbmAdjacencyMatrix_apply p q i j

/-- Vertices in the first block of the stochastic block model have community flag `false`.

**Lean implementation helper.** -/
@[simp]
lemma sbmCommunity_castAdd {k : ℕ} (i : Fin k) :
    sbmCommunity (Fin.cast (by omega) (Fin.castAdd k i) : SBMVertex k) = false := by
  simp [sbmCommunity]

/-- Vertices in the second block of the stochastic block model have community flag `true`.

**Lean implementation helper.** -/
@[simp]
lemma sbmCommunity_natAdd {k : ℕ} (i : Fin k) :
    sbmCommunity (Fin.cast (by omega) (Fin.natAdd k i) : SBMVertex k) = true := by
  simp [sbmCommunity]

/-- Vertices in the first block have community label `+1`.

**Lean implementation helper.** -/
@[simp]
lemma sbmCommunityLabel_castAdd {k : ℕ} (i : Fin k) :
    sbmCommunityLabel (Fin.cast (by omega) (Fin.castAdd k i) : SBMVertex k) = 1 := by
  rw [sbmCommunityLabel, sbmCommunity_castAdd]
  rfl

/-- Vertices in the second block have community label `-1`.

**Lean implementation helper.** -/
@[simp]
lemma sbmCommunityLabel_natAdd {k : ℕ} (i : Fin k) :
    sbmCommunityLabel (Fin.cast (by omega) (Fin.natAdd k i) : SBMVertex k) = -1 := by
  rw [sbmCommunityLabel, sbmCommunity_natAdd]
  rfl

/-- The balanced community vector has zero coordinate sum.

**Lean implementation helper.** -/
lemma sum_sbmCommunityLabel (k : ℕ) :
    (∑ i : SBMVertex k, sbmCommunityLabel i) = 0 := by
  let e : Fin (k + k) ≃ SBMVertex k :=
    { toFun := fun i => ⟨i.1, by omega⟩
      invFun := fun i => ⟨i.1, by omega⟩
      left_inv := fun i => by apply Fin.ext; rfl
      right_inv := fun i => by apply Fin.ext; rfl }
  calc
    (∑ i : SBMVertex k, sbmCommunityLabel i) =
        ∑ i : Fin (k + k), sbmCommunityLabel (e i) := by
      symm
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = (∑ i : Fin k, sbmCommunityLabel (e (Fin.castAdd k i))) +
          ∑ i : Fin k, sbmCommunityLabel (e (Fin.natAdd k i)) :=
      Fin.sum_univ_add _
    _ = 0 := by
      have hleft (i : Fin k) : sbmCommunityLabel (e (Fin.castAdd k i)) = 1 := by
        have hlt : (e (Fin.castAdd k i)).val < k := by
          dsimp [e]
          exact i.isLt
        simp [sbmCommunityLabel, sbmCommunity, not_le.mpr hlt]
      have hright (i : Fin k) : sbmCommunityLabel (e (Fin.natAdd k i)) = -1 := by
        have hc : sbmCommunity (e (Fin.natAdd k i)) = true := by
          simp [sbmCommunity, e]
        unfold sbmCommunityLabel
        rw [hc]
        rfl
      simp_rw [hleft, hright]
      simp

/-- Every stochastic-block-model community label has square `1`.

**Lean implementation helper.** -/
@[simp]
lemma sbmCommunityLabel_sq {k : ℕ} (i : SBMVertex k) :
    sbmCommunityLabel i ^ 2 = 1 := by
  simp [sbmCommunityLabel]

/-- Every stochastic-block-model community label has absolute value one.

**Lean implementation helper.** -/
@[simp]
lemma abs_sbmCommunityLabel {k : ℕ} (i : SBMVertex k) :
    |sbmCommunityLabel i| = 1 := by
  cases h : sbmCommunity i <;> simp [sbmCommunityLabel, h]

/-- Entrywise rank-two decomposition of the deterministic expected adjacency matrix.

**Lean implementation helper.** -/
lemma sbmExpectedAdjacency_eq_rankTwo (k : ℕ) (p q : Set.Icc (0 : ℝ) 1)
    (i j : SBMVertex k) :
    sbmExpectedAdjacency k p q i j =
      ((p : ℝ) + (q : ℝ)) / 2 +
        (((p : ℝ) - (q : ℝ)) / 2) * sbmCommunityLabel i * sbmCommunityLabel j := by
  unfold sbmExpectedAdjacency sbmSameCommunity sbmCommunityLabel
  cases hi : sbmCommunity i <;> cases hj : sbmCommunity j <;>
    simp_all <;> ring

/-- Every image vector of the expectation matrix lies in the span of the constant and
community-label vectors. This is the usable rank-at-most-two form of the source assertion.

**Lean implementation helper.** -/
theorem sbmExpectedAdjacency_mulVec_formula (k : ℕ) (p q : Set.Icc (0 : ℝ) 1)
    (x : SBMVertex k → ℝ) (i : SBMVertex k) :
    (sbmExpectedAdjacency k p q *ᵥ x) i =
      (((p : ℝ) + (q : ℝ)) / 2 * ∑ j, x j) +
        (((p : ℝ) - (q : ℝ)) / 2 * ∑ j, sbmCommunityLabel j * x j) *
          sbmCommunityLabel i := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [sbmExpectedAdjacency_eq_rankTwo]
  calc
    (∑ j, (((p : ℝ) + q) / 2 + ((p : ℝ) - q) / 2 *
        sbmCommunityLabel i * sbmCommunityLabel j) * x j) =
        ∑ j, (((p : ℝ) + q) / 2 * x j +
          ((((p : ℝ) - q) / 2 * sbmCommunityLabel i) *
            (sbmCommunityLabel j * x j))) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ((p : ℝ) + q) / 2 * ∑ j, x j +
          (((p : ℝ) - q) / 2 * sbmCommunityLabel i) *
            ∑ j, sbmCommunityLabel j * x j := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ((p : ℝ) + q) / 2 * ∑ j, x j +
          (((p : ℝ) - q) / 2 * ∑ j, sbmCommunityLabel j * x j) *
            sbmCommunityLabel i := by ring

/-- The all-ones vector is an eigenvector with eigenvalue `k(p+q)`.

**Lean implementation helper.** -/
theorem sbmExpectedAdjacency_mulVec_one (k : ℕ) (p q : Set.Icc (0 : ℝ) 1) :
    sbmExpectedAdjacency k p q *ᵥ (fun _ => (1 : ℝ)) =
      fun _ => (k : ℝ) * ((p : ℝ) + (q : ℝ)) := by
  funext i
  rw [sbmExpectedAdjacency_mulVec_formula]
  rw [show (∑ _j : SBMVertex k, (1 : ℝ)) = 2 * (k : ℝ) by simp]
  norm_num [sum_sbmCommunityLabel]
  ring

/-- The balanced sign vector is an eigenvector with eigenvalue `k(p-q)`.

**Lean implementation helper.** -/
theorem sbmExpectedAdjacency_mulVec_communityLabel
    (k : ℕ) (p q : Set.Icc (0 : ℝ) 1) :
    sbmExpectedAdjacency k p q *ᵥ sbmCommunityLabel =
      fun i => ((k : ℝ) * ((p : ℝ) - (q : ℝ))) * sbmCommunityLabel i := by
  funext i
  rw [sbmExpectedAdjacency_mulVec_formula]
  rw [show (∑ j : SBMVertex k, sbmCommunityLabel j) = 0 by
    exact sum_sbmCommunityLabel k]
  rw [show (∑ j : SBMVertex k, sbmCommunityLabel j * sbmCommunityLabel j) =
      2 * (k : ℝ) by
    simp_rw [← pow_two, sbmCommunityLabel_sq]
    simp]
  ring

/-- The image of the expected adjacency operator is contained in the span of the constant vector
and the community vector.

**Lean implementation helper.** -/
theorem sbmExpectedAdjacency_range_le_span (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) :
    LinearMap.range (sbmExpectedAdjacency k p q).mulVecLin ≤
      Submodule.span ℝ ({(fun _ : SBMVertex k => (1 : ℝ)), sbmCommunityLabel} :
        Set (SBMVertex k → ℝ)) := by
  rintro y ⟨x, rfl⟩
  let a : ℝ := ((p : ℝ) + (q : ℝ)) / 2 * ∑ j, x j
  let b : ℝ := ((p : ℝ) - (q : ℝ)) / 2 * ∑ j, sbmCommunityLabel j * x j
  have hone : (fun _ : SBMVertex k => (1 : ℝ)) ∈
      Submodule.span ℝ ({(fun _ : SBMVertex k => (1 : ℝ)), sbmCommunityLabel} :
        Set (SBMVertex k → ℝ)) := Submodule.subset_span (by simp)
  have hlabel : sbmCommunityLabel ∈
      Submodule.span ℝ ({(fun _ : SBMVertex k => (1 : ℝ)), sbmCommunityLabel} :
        Set (SBMVertex k → ℝ)) := Submodule.subset_span (by simp)
  have hsum := Submodule.add_mem _ (Submodule.smul_mem _ a hone)
    (Submodule.smul_mem _ b hlabel)
  rw [show (sbmExpectedAdjacency k p q).mulVecLin x =
      a • (fun _ : SBMVertex k => (1 : ℝ)) + b • sbmCommunityLabel by
    funext i
    simp only [Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_one, a, b]
    exact sbmExpectedAdjacency_mulVec_formula k p q x i]
  exact hsum

/-- The expected adjacency matrix has rank at most two. This remains true in the degenerate
cases `p=q` and `p=q=0`, where the rank can be smaller.

**Book Chapter 4, pp.119--122, SBM signal calculation.** -/
theorem sbmExpectedAdjacency_rank_le_two (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) :
    (sbmExpectedAdjacency k p q).rank ≤ 2 := by
  rw [Matrix.rank]
  calc
    Module.finrank ℝ (LinearMap.range (sbmExpectedAdjacency k p q).mulVecLin) ≤
        Module.finrank ℝ
          (Submodule.span ℝ ({(fun _ : SBMVertex k => (1 : ℝ)), sbmCommunityLabel} :
            Set (SBMVertex k → ℝ))) :=
      Submodule.finrank_mono (sbmExpectedAdjacency_range_le_span k p q)
    _ ≤ 2 := by
      calc
        _ ≤ ({(fun _ : SBMVertex k => (1 : ℝ)), sbmCommunityLabel} :
              Set (SBMVertex k → ℝ)).toFinset.card :=
          finrank_span_le_card (R := ℝ) _
        _ ≤ 2 := by
          rw [← Set.ncard_eq_toFinset_card']
          by_cases h : (fun _ : SBMVertex k => (1 : ℝ)) = sbmCommunityLabel
          · simp [h]
          · rw [Set.ncard_pair h]

/-- Away from the obvious degeneracies, the expected adjacency matrix has rank exactly two.

**Lean implementation helper.** -/
theorem sbmExpectedAdjacency_rank_eq_two {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hpq : (p : ℝ) ≠ q) :
    (sbmExpectedAdjacency k p q).rank = 2 := by
  let i₀ : SBMVertex k := ⟨0, by omega⟩
  let i₁ : SBMVertex k := ⟨k, by omega⟩
  let pick : Fin 2 → SBMVertex k := ![i₀, i₁]
  let B : Matrix (Fin 2) (Fin 2) ℝ :=
    (sbmExpectedAdjacency k p q).submatrix pick pick
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have h00 : B 0 0 = (p : ℝ) := by
    simp [B, pick, i₀, sbmExpectedAdjacency, sbmSameCommunity, sbmCommunity]
  have h01 : B 0 1 = (q : ℝ) := by
    simp [B, pick, i₀, i₁, sbmExpectedAdjacency, sbmSameCommunity, sbmCommunity, hk0]
  have h10 : B 1 0 = (q : ℝ) := by
    simp [B, pick, i₀, i₁, sbmExpectedAdjacency, sbmSameCommunity, sbmCommunity, hk0]
  have h11 : B 1 1 = (p : ℝ) := by
    simp [B, pick, i₁, sbmExpectedAdjacency, sbmSameCommunity, sbmCommunity]
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hq0 : 0 ≤ (q : ℝ) := q.2.1
  have hdet : B.det ≠ 0 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    intro hz
    apply hpq
    nlinarith
  have hBrank : B.rank = 2 := by
    have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
    have hmul := Matrix.rank_mul_eq_right_of_isUnit_det B
      (1 : Matrix (Fin 2) (Fin 2) ℝ) hunit
    simpa [Matrix.rank_one] using hmul
  apply Nat.le_antisymm (sbmExpectedAdjacency_rank_le_two k p q)
  have hsub : B.rank ≤ (sbmExpectedAdjacency k p q).rank := by
    exact Matrix.rank_submatrix_le (sbmExpectedAdjacency k p q) pick pick
  omega

/-- Correct spectral separation around the informative eigenvalue. For `0 ≤ q ≤ p`, its distance
both from zero and from the leading eigenvalue is at least `k * min (p-q) (2q)`.

**Book Chapter 4, pp.119--122, SBM signal calculation.** -/
theorem sbm_informative_eigenvalue_gap (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) (_hqp : (q : ℝ) ≤ p) :
    min ((k : ℝ) * ((p : ℝ) - q))
        ((k : ℝ) * ((p : ℝ) + q) - (k : ℝ) * ((p : ℝ) - q)) =
      (k : ℝ) * min ((p : ℝ) - q) (2 * q) := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hrewrite :
      (k : ℝ) * ((p : ℝ) + q) - (k : ℝ) * ((p : ℝ) - q) =
        (k : ℝ) * (2 * q) := by ring
  rw [hrewrite]
  exact (mul_min_of_nonneg _ _ hk).symm

end HDP.Chapter4

end Source_15_StochasticBlockModel

/-! ## Material formerly in `16_CommunityDetection.lean` -/

section Source_16_CommunityDetection

/-!
# Chapter 4, §4.5.2--4.5.5: community detection

This file separates the probabilistic noise estimate from the deterministic
sign-counting step.  The latter is invariant under the unavoidable global sign
of an eigenvector.
-/

open Matrix WithLp MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter4

open HDP

/-- Centered adjacency noise `A - 𝔼 A`.

**Lean implementation helper.** -/
noncomputable def sbmNoise {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (G : SBMSample k) : Matrix (SBMVertex k) (SBMVertex k) ℝ :=
  sbmAdjacencyMatrix G - sbmExpectedAdjacency k p q

/-- The `(i,j)` entry of `sbmNoise p q G` is the observed edge indicator minus `p` for same-community vertices and minus `q` otherwise.

**Lean implementation helper.** -/
@[simp]
lemma sbmNoise_apply {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (G : SBMSample k) (i j : SBMVertex k) :
    sbmNoise p q G i j = sbmEdgeIndicator s(i, j) G -
      (if sbmSameCommunity i j then (p : ℝ) else (q : ℝ)) := rfl

/-- Shows that sbm noise is symmetric.

**Lean implementation helper.** -/
lemma sbmNoise_symmetric {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (G : SBMSample k) : (sbmNoise p q G).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [sbmNoise, sbmAdjacencyMatrix, sbmExpectedAdjacency,
    sbmSameCommunity_comm, Sym2.eq_swap]

/-- Each entry of the stochastic-block-model noise matrix is almost-everywhere measurable.

**Lean implementation helper.** -/
lemma sbmNoise_aemeasurable {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (i j : SBMVertex k) :
    AEMeasurable (fun G => sbmNoise p q G i j)
      (stochasticBlockModel k p q) := by
  fun_prop

/-- Every entry of the centered stochastic-block-model noise matrix has expectation zero.

**Lean implementation helper.** -/
lemma integral_sbmNoise {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (i j : SBMVertex k) :
    ∫ G, sbmNoise p q G i j ∂(stochasticBlockModel k p q) = 0 := by
  have hA : Integrable (fun G => sbmAdjacencyMatrix G i j)
      (stochasticBlockModel k p q) := by
    simpa only [sbmAdjacencyMatrix, id_eq] using
      (sbmEdgeIndicator_isBernoulli p q s(i, j)).integrable_comp id
  have hD : Integrable (fun _G : SBMSample k =>
      sbmExpectedAdjacency k p q i j) (stochasticBlockModel k p q) :=
    integrable_const _
  rw [show (fun G => sbmNoise p q G i j) =
      fun G => sbmAdjacencyMatrix G i j - sbmExpectedAdjacency k p q i j by rfl,
    integral_sub hA hD, integral_sbmAdjacencyMatrix_apply]
  simp

/-- Every centered Bernoulli entry lies in `[-1,1]`.

**Lean implementation helper.** -/
lemma abs_sbmNoise_le_one {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (G : SBMSample k) (i j : SBMVertex k) :
    |sbmNoise p q G i j| ≤ 1 := by
  rw [sbmNoise_apply]
  by_cases hs : sbmSameCommunity i j
  · rw [if_pos hs]
    cases hG : G s(i, j)
    · simp only [sbmEdgeIndicator, hG, Bool.false_eq_true, if_false,
        zero_sub]
      change |-(p : ℝ)| ≤ 1
      rw [abs_neg, abs_of_nonneg p.2.1]
      exact p.2.2
    · simp only [sbmEdgeIndicator, hG, if_true]
      rw [abs_of_nonneg (sub_nonneg.mpr p.2.2)]
      linarith [p.2.1]
  · rw [if_neg hs]
    cases hG : G s(i, j)
    · simp only [sbmEdgeIndicator, hG, Bool.false_eq_true, if_false,
        zero_sub]
      change |-(q : ℝ)| ≤ 1
      rw [abs_neg, abs_of_nonneg q.2.1]
      exact q.2.2
    · simp only [sbmEdgeIndicator, hG, if_true]
      rw [abs_of_nonneg (sub_nonneg.mpr q.2.2)]
      linarith [q.2.1]

/-- Centered SBM entries are uniformly subgaussian with the explicit bounded random-variable
constant.

**Lean implementation helper.** -/
theorem sbmNoise_subGaussian_psi2 {k : ℕ} (p q : Set.Icc (0 : ℝ) 1)
    (i j : SBMVertex k) :
    HDP.SubGaussian (fun G => sbmNoise p q G i j)
        (stochasticBlockModel k p q) ∧
      HDP.psi2Norm (fun G => sbmNoise p q G i j)
          (stochasticBlockModel k p q) ≤
        1 / Real.sqrt (Real.log 2) := by
  exact HDP.psi2Norm_le_of_bounded (by norm_num)
    (Filter.Eventually.of_forall fun G => abs_sbmNoise_le_one p q G i j)

/-- Sending an ordered upper-triangle pair to its unordered edge is injective. This is where the
order condition prevents the `(i,j)/(j,i)` duplication.

**Lean implementation helper.** -/
lemma upperPairToSBMEdge_injective {k : ℕ} : Function.Injective
    (fun ij : UpperIndex (2 * k) => s(ij.1.1, ij.1.2) :
      UpperIndex (2 * k) → SBMEdge k) := by
  intro a b hab
  apply Subtype.ext
  rcases Sym2.eq_iff.mp hab with hdir | hswap
  · exact Prod.ext hdir.1 hdir.2
  · have harev : a.1.2 ≤ a.1.1 := by
      calc
        a.1.2 = b.1.1 := hswap.2
        _ ≤ b.1.2 := b.2
        _ = a.1.1 := hswap.1.symm
    have haa : a.1.1 = a.1.2 := le_antisymm a.2 harev
    apply Prod.ext
    · exact haa.trans hswap.2
    · exact haa.symm.trans hswap.1

/-- The concrete centered upper-triangle entries of the loop-aware SBM are independent. This is
derived from the product-coordinate theorem rather than assumed by the community-detection
result.

**Lean implementation helper.** -/
theorem sbmNoise_independentUpperEntries {k : ℕ}
    (p q : Set.Icc (0 : ℝ) 1) :
    IndependentUpperEntries (fun G => sbmNoise p q G)
      (stochasticBlockModel k p q) := by
  let edge : UpperIndex (2 * k) → SBMEdge k :=
    fun ij => s(ij.1.1, ij.1.2)
  have hedge : Function.Injective edge := upperPairToSBMEdge_injective
  have hcoord := (sbmEdgeIndicator_independent p q).precomp hedge
  let shift : UpperIndex (2 * k) → ℝ → ℝ := fun ij z =>
    z - if sbmSameCommunity ij.1.1 ij.1.2 then (p : ℝ) else (q : ℝ)
  have hshift := hcoord.comp shift (fun _ => by fun_prop)
  unfold IndependentUpperEntries
  convert hshift using 1
  funext ij G
  simp [edge, shift, sbmNoise_apply]

/-- The concrete high-probability operator-norm estimate (4.25), with an explicit constant
inherited from the corresponding corollary.

**Book (4.25).** -/
theorem sbmNoise_norm_tail {k : ℕ} [NeZero k]
    (p q : Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (stochasticBlockModel k p q)
        {G | 400 * (1 / Real.sqrt (Real.log 2)) *
            (Real.sqrt (2 * k) + t) < HDP.matrixOpNorm (sbmNoise p q G)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  have hK : 0 < 1 / Real.sqrt (Real.log 2) := by positivity
  have h := corollary_4_4_7 (μ := stochasticBlockModel k p q)
    (A := fun G => sbmNoise p q G)
    (fun G => sbmNoise_symmetric p q G)
    (sbmNoise_aemeasurable p q)
    (fun i j => (sbmNoise_subGaussian_psi2 p q i j).1)
    (integral_sbmNoise p q) (sbmNoise_independentUpperEntries p q) hK
    (fun i j => (sbmNoise_subGaussian_psi2 p q i j).2) ht
  simpa using h

/-- Every community label is either `+1` or `-1`.

**Lean implementation helper.** -/
lemma sbmCommunityLabel_sign {k : ℕ} (i : SBMVertex k) :
    sbmCommunityLabel i = 1 ∨ sbmCommunityLabel i = -1 := by
  cases h : sbmCommunity i <;> simp [sbmCommunityLabel, h]

/-- Bounds filter card sign mismatch by squared error.

**Lean implementation helper.** -/
private lemma filterCard_signMismatch_le_sqError {k : ℕ}
    (estimate : SBMVertex k → ℝ) :
    ((Finset.univ.filter fun i =>
      spectralSignLabel estimate i ≠ sbmCommunityLabel i).card : ℝ) ≤
      ∑ i, (sbmCommunityLabel i - estimate i) ^ 2 := by
  calc
    ((Finset.univ.filter fun i =>
        spectralSignLabel estimate i ≠ sbmCommunityLabel i).card : ℝ) =
        ∑ i ∈ Finset.univ.filter (fun i =>
          spectralSignLabel estimate i ≠ sbmCommunityLabel i), (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          spectralSignLabel estimate i ≠ sbmCommunityLabel i),
          (sbmCommunityLabel i - estimate i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact one_le_sq_sub_of_sign_mismatch (sbmCommunityLabel_sign i)
        (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ Finset.univ, (sbmCommunityLabel i - estimate i) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg (sbmCommunityLabel i - estimate i))
    _ = ∑ i, (sbmCommunityLabel i - estimate i) ^ 2 := rfl

/-- Sign disagreements, minimized over global sign, are bounded by the corresponding squared
Euclidean error.

**Lean implementation helper.** -/
theorem misclassifiedUpToSign_le_sqError {k : ℕ}
    (estimate : SBMVertex k → ℝ) :
    (misclassifiedUpToSign sbmCommunityLabel estimate : ℝ) ≤
      min (∑ i, (sbmCommunityLabel i - estimate i) ^ 2)
        (∑ i, (sbmCommunityLabel i + estimate i) ^ 2) := by
  have hpos := filterCard_signMismatch_le_sqError estimate
  have hneg := filterCard_signMismatch_le_sqError (fun i => -estimate i)
  rw [show (∑ i, (sbmCommunityLabel i - -estimate i) ^ 2) =
      ∑ i, (sbmCommunityLabel i + estimate i) ^ 2 by
    apply Finset.sum_congr rfl
    intro i _
    ring] at hneg
  rw [misclassifiedUpToSign, Nat.cast_min]
  exact min_le_min hpos hneg

/-- Deterministic final step of spectral clustering: an approximation to the community vector
yields the same bound on misclassified vertices, modulo the global eigenvector sign.

**Lean implementation helper.** -/
theorem spectralClustering_misclassified_of_sqError {k : ℕ}
    (estimate : SBMVertex k → ℝ) {η : ℝ}
    (herror : min (∑ i, (sbmCommunityLabel i - estimate i) ^ 2)
        (∑ i, (sbmCommunityLabel i + estimate i) ^ 2) ≤ η) :
    (misclassifiedUpToSign sbmCommunityLabel estimate : ℝ) ≤ η :=
  (misclassifiedUpToSign_le_sqError estimate).trans herror

/-- The expected degree (including the source's loop) is `k(p+q)` on `2k` vertices.

**Book Remark 4.5.3.** -/
theorem remark_4_5_3_expectedDegree (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) (i : SBMVertex k) :
    ∑ j, sbmExpectedAdjacency k p q i j =
      (k : ℝ) * ((p : ℝ) + q) := by
  have h := congrFun (sbmExpectedAdjacency_mulVec_one k p q) i
  simpa [Matrix.mulVec, dotProduct] using h

/-- If the the corresponding theorem error bound `C / μ²` is nontrivial on `2k` vertices, then
the expected degree is bounded below by an explicit constant times `√(2k)`.

**Book Remark 4.5.3.** -/
theorem remark_4_5_3_nontrivial_degree_lower {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (_hqp : (q : ℝ) ≤ p)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hμ : 0 < min (q : ℝ) ((p : ℝ) - q))
    (hnontrivial : C / (min (q : ℝ) ((p : ℝ) - q)) ^ 2 ≤ (2 * k : ℝ)) :
    Real.sqrt C / 2 * Real.sqrt (2 * k) ≤
      (k : ℝ) * ((p : ℝ) + q) := by
  let μ₀ : ℝ := min (q : ℝ) ((p : ℝ) - q)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hnR : 0 < (2 * k : ℝ) := by positivity
  have hC : C ≤ (2 * k : ℝ) * μ₀ ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hμ)).mp hnontrivial
    dsimp [μ₀]
    nlinarith
  have hμq : μ₀ ≤ (q : ℝ) := min_le_left _ _
  have hdegree : (k : ℝ) * μ₀ ≤ (k : ℝ) * ((p : ℝ) + q) := by
    apply mul_le_mul_of_nonneg_left _ hkR.le
    have hp0 : 0 ≤ (p : ℝ) := p.2.1
    linarith
  have hsqrtN : Real.sqrt (2 * k) ^ 2 = (2 * k : ℝ) :=
    Real.sq_sqrt hnR.le
  have hsqrtC : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC0
  have hsquare : (Real.sqrt C / 2 * Real.sqrt (2 * k)) ^ 2 ≤
      ((k : ℝ) * μ₀) ^ 2 := by
    dsimp [μ₀] at hC ⊢
    nlinarith [sq_nonneg ((k : ℝ) * min (q : ℝ) ((p : ℝ) - q))]
  have hroot : Real.sqrt C / 2 * Real.sqrt (2 * k) ≤ (k : ℝ) * μ₀ := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg hkR.le hμ.le)).mp
    exact hsquare
  exact hroot.trans hdegree

/-- If both `q` and `p-q` are at most constants divided by `√(2k)`, then the expected degree is
at most an explicit constant times `√(2k)`.

**Book Remark 4.5.3.** -/
theorem remark_4_5_3_scaled_degree_upper {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hq : (q : ℝ) ≤ a / Real.sqrt (2 * k))
    (hgap : (p : ℝ) - q ≤ b / Real.sqrt (2 * k)) :
    (k : ℝ) * ((p : ℝ) + q) ≤
      (2 * a + b) / 2 * Real.sqrt (2 * k) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hnR : 0 < (2 * k : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.2 hnR
  have hsqrtSq : Real.sqrt (2 * k) ^ 2 = (2 * k : ℝ) :=
    Real.sq_sqrt hnR.le
  have hsum : (p : ℝ) + q ≤ (2 * a + b) / Real.sqrt (2 * k) := by
    calc
      (p : ℝ) + q = ((p : ℝ) - q) + 2 * q := by ring
      _ ≤ b / Real.sqrt (2 * k) + 2 * (a / Real.sqrt (2 * k)) := by
        linarith
      _ = (2 * a + b) / Real.sqrt (2 * k) := by ring
  calc
    (k : ℝ) * ((p : ℝ) + q) ≤
        (k : ℝ) * ((2 * a + b) / Real.sqrt (2 * k)) :=
      mul_le_mul_of_nonneg_left hsum hkR.le
    _ = (2 * a + b) / 2 * Real.sqrt (2 * k) := by
      have hratio : (k : ℝ) / Real.sqrt (2 * k) =
          Real.sqrt (2 * k) / 2 := by
        apply (div_eq_iff hsqrt.ne').2
        nlinarith
      rw [show (k : ℝ) * ((2 * a + b) / Real.sqrt (2 * k)) =
          (2 * a + b) * ((k : ℝ) / Real.sqrt (2 * k)) by ring,
        hratio]
      ring

/-!
## Theorem 4.5.2: the actual ordered spectral estimator

The declarations below construct the second ordered adjacency eigenvector,
identify the complete expected eigensystem, and prove the source-facing
label-swap invariant high-probability guarantee.
-/

/-- The expected stochastic-block-model adjacency operator is the continuous Euclidean linear map induced by `sbmExpectedAdjacency k p q`.

**Lean implementation helper.** -/
noncomputable def sbmExpectedOperator (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) :
    EuclideanSpace ℝ (SBMVertex k) →L[ℝ] EuclideanSpace ℝ (SBMVertex k) :=
  (sbmExpectedAdjacency k p q).toEuclideanLin.toContinuousLinearMap

/-- The expected adjacency operator of the two-community stochastic block model is self-adjoint.

**Lean implementation helper.** -/
lemma sbmExpectedOperator_selfAdjoint (k : ℕ)
    (p q : Set.Icc (0 : ℝ) 1) :
    IsSelfAdjoint (sbmExpectedOperator k p q) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    have hsym : (sbmExpectedAdjacency k p q).IsSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      simp [sbmExpectedAdjacency, sbmSameCommunity_comm]
    exact isHermitian_iff_isSymm.mpr hsym)

/-- The Rayleigh quotient of the expected adjacency operator splits into squared all-ones and community-label components.

**Lean implementation helper.** -/
lemma rayleigh (k : ℕ) (p q : Set.Icc (0 : ℝ) 1)
    (x : EuclideanSpace ℝ (SBMVertex k)) :
    (sbmExpectedOperator k p q).reApplyInnerSelf x =
      (((p : ℝ) + q) / 2) * (∑ i, WithLp.ofLp x i) ^ 2 +
      (((p : ℝ) - q) / 2) *
        (∑ i, sbmCommunityLabel i * WithLp.ofLp x i) ^ 2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change inner ℝ
    ((sbmExpectedAdjacency k p q).toEuclideanLin x) x = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp]
  simp_rw [sbmExpectedAdjacency_mulVec_formula]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ i, WithLp.ofLp x i *
        (((p : ℝ) + q) / 2 * ∑ j, WithLp.ofLp x j)) =
        (∑ i, WithLp.ofLp x i) *
          (((p : ℝ) + q) / 2 * ∑ j, WithLp.ofLp x j) := by
    rw [Finset.sum_mul]
  have hsecond :
      (∑ i, WithLp.ofLp x i *
        ((((p : ℝ) - q) / 2 *
          ∑ j, sbmCommunityLabel j * WithLp.ofLp x j) *
            sbmCommunityLabel i)) =
        (∑ i, sbmCommunityLabel i * WithLp.ofLp x i) *
          (((p : ℝ) - q) / 2 *
            ∑ j, sbmCommunityLabel j * WithLp.ofLp x j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst, hsecond]
  ring

/-- The expected adjacency Rayleigh quotient is at most `k(p+q) ‖x‖²`.

**Lean implementation helper.** -/
lemma rayleigh_upper (k : ℕ) (p q : Set.Icc (0 : ℝ) 1)
    (x : EuclideanSpace ℝ (SBMVertex k)) :
    (sbmExpectedOperator k p q).reApplyInnerSelf x ≤
      ((k : ℝ) * ((p : ℝ) + q)) * ‖x‖ ^ 2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change inner ℝ
    ((sbmExpectedAdjacency k p q).toEuclideanLin x) x ≤ _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp]
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, WithLp.ofLp x i *
      (∑ j, sbmExpectedAdjacency k p q i j * WithLp.ofLp x j)) ≤ _
  rw [show (∑ i, WithLp.ofLp x i *
      (∑ j, sbmExpectedAdjacency k p q i j * WithLp.ofLp x j)) =
      ∑ i, ∑ j, WithLp.ofLp x i *
        (sbmExpectedAdjacency k p q i j * WithLp.ofLp x j) by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]]
  calc
    (∑ i, ∑ j, WithLp.ofLp x i *
        (sbmExpectedAdjacency k p q i j * WithLp.ofLp x j)) ≤
        ∑ i, ∑ j, sbmExpectedAdjacency k p q i j *
          (WithLp.ofLp x i ^ 2 + WithLp.ofLp x j ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hD : 0 ≤ sbmExpectedAdjacency k p q i j := by
        unfold sbmExpectedAdjacency
        split
        · exact p.2.1
        · exact q.2.1
      nlinarith [sq_nonneg (WithLp.ofLp x i - WithLp.ofLp x j),
        mul_nonneg hD (sq_nonneg (WithLp.ofLp x i - WithLp.ofLp x j))]
    _ = ((k : ℝ) * ((p : ℝ) + q)) *
        ∑ i, WithLp.ofLp x i ^ 2 := by
      have hrow (i : SBMVertex k) :
          ∑ j, sbmExpectedAdjacency k p q i j =
            (k : ℝ) * ((p : ℝ) + q) :=
        remark_4_5_3_expectedDegree k p q i
      have hcol (j : SBMVertex k) :
          ∑ i, sbmExpectedAdjacency k p q i j =
            (k : ℝ) * ((p : ℝ) + q) := by
        simpa [sbmExpectedAdjacency, sbmSameCommunity_comm] using hrow j
      simp_rw [mul_add, add_div]
      simp_rw [Finset.sum_add_distrib]
      have hone :
          (∑ i, ∑ j, sbmExpectedAdjacency k p q i j *
            WithLp.ofLp x i ^ 2 / 2) =
            ((k : ℝ) * ((p : ℝ) + q)) / 2 *
              ∑ i, WithLp.ofLp x i ^ 2 := by
        calc
          _ = ∑ i, (∑ j, sbmExpectedAdjacency k p q i j) *
              WithLp.ofLp x i ^ 2 / 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.sum_div, Finset.sum_mul]
          _ = _ := by simp_rw [hrow]; rw [Finset.mul_sum]; ring_nf
      have htwo :
          (∑ i, ∑ j, sbmExpectedAdjacency k p q i j *
            WithLp.ofLp x j ^ 2 / 2) =
            ((k : ℝ) * ((p : ℝ) + q)) / 2 *
              ∑ j, WithLp.ofLp x j ^ 2 := by
        rw [Finset.sum_comm]
        calc
          _ = ∑ j, (∑ i, sbmExpectedAdjacency k p q i j) *
              WithLp.ofLp x j ^ 2 / 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_div, Finset.sum_mul]
          _ = _ := by simp_rw [hcol]; rw [Finset.mul_sum]; ring_nf
      rw [hone, htwo]
      ring

/-- The stochastic-block-model all-ones Euclidean vector has every coordinate equal to `1`.

**Lean implementation helper.** -/
noncomputable def sbmOneVector (k : ℕ) :
    EuclideanSpace ℝ (SBMVertex k) :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

/-- The stochastic-block-model label vector has coordinate `i` equal to `sbmCommunityLabel i`.

**Lean implementation helper.** -/
noncomputable def sbmLabelVector (k : ℕ) :
    EuclideanSpace ℝ (SBMVertex k) :=
  WithLp.toLp 2 sbmCommunityLabel

/-- Every coordinate of `sbmOneVector k` is `1`.

**Lean implementation helper.** -/
@[simp] lemma sbmOneVector_apply (k : ℕ) (i : SBMVertex k) :
    WithLp.ofLp (sbmOneVector k) i = 1 := rfl

/-- Coordinate `i` of `sbmLabelVector k` is `sbmCommunityLabel i`.

**Lean implementation helper.** -/
@[simp] lemma sbmLabelVector_apply (k : ℕ) (i : SBMVertex k) :
    WithLp.ofLp (sbmLabelVector k) i = sbmCommunityLabel i := rfl

/-- The squared norm of the all-ones community vector is `2k`.

**Lean implementation helper.** -/
lemma one_norm_sq (k : ℕ) : ‖sbmOneVector k‖ ^ 2 = 2 * (k : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp

/-- The squared norm of the community-label vector is `2k`.

**Lean implementation helper.** -/
lemma label_norm_sq (k : ℕ) : ‖sbmLabelVector k‖ ^ 2 = 2 * (k : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp

/-- The all-ones vector and the community-label vector are orthogonal.

**Lean implementation helper.** -/
lemma inner_one_label (k : ℕ) :
    inner ℝ (sbmOneVector k) (sbmLabelVector k) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, sum_sbmCommunityLabel]

/-- The all-ones vector is an eigenvector of the expected adjacency operator with eigenvalue `k(p+q)`.

**Lean implementation helper.** -/
lemma expected_one_eigen (k : ℕ) (p q : Set.Icc (0 : ℝ) 1) :
    sbmExpectedOperator k p q (sbmOneVector k) =
      ((k : ℝ) * ((p : ℝ) + q)) • sbmOneVector k := by
  apply WithLp.ofLp_injective
  funext i
  change (sbmExpectedAdjacency k p q *ᵥ (fun _ => (1 : ℝ))) i = _
  rw [congrFun (sbmExpectedAdjacency_mulVec_one k p q) i]
  simp

/-- The community-label vector is an eigenvector of the expected adjacency operator with eigenvalue `k(p-q)`.

**Lean implementation helper.** -/
lemma expected_label_eigen (k : ℕ) (p q : Set.Icc (0 : ℝ) 1) :
    sbmExpectedOperator k p q (sbmLabelVector k) =
      ((k : ℝ) * ((p : ℝ) - q)) • sbmLabelVector k := by
  apply WithLp.ofLp_injective
  funext i
  change (sbmExpectedAdjacency k p q *ᵥ sbmCommunityLabel) i = _
  rw [congrFun (sbmExpectedAdjacency_mulVec_communityLabel k p q) i]
  simp

/-- The all-ones community direction is normalized as `‖sbmOneVector k‖⁻¹ • sbmOneVector k`.

**Lean implementation helper.** -/
noncomputable def sbmOneUnit (k : ℕ) :
    EuclideanSpace ℝ (SBMVertex k) :=
  ‖sbmOneVector k‖⁻¹ • sbmOneVector k

/-- The community-label direction is normalized as `‖sbmLabelVector k‖⁻¹ • sbmLabelVector k`.

**Lean implementation helper.** -/
noncomputable def sbmLabelUnit (k : ℕ) :
    EuclideanSpace ℝ (SBMVertex k) :=
  ‖sbmLabelVector k‖⁻¹ • sbmLabelVector k

/-- Shows that one norm is positive.

**Lean implementation helper.** -/
lemma one_norm_pos {k : ℕ} (hk : 0 < k) : 0 < ‖sbmOneVector k‖ := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  nlinarith [one_norm_sq k, norm_nonneg (sbmOneVector k)]

/-- Shows that label norm is positive.

**Lean implementation helper.** -/
lemma label_norm_pos {k : ℕ} (hk : 0 < k) : 0 < ‖sbmLabelVector k‖ := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  nlinarith [label_norm_sq k, norm_nonneg (sbmLabelVector k)]

/-- The normalized all-ones community vector has norm `1`.

**Lean implementation helper.** -/
lemma one_unit_norm {k : ℕ} (hk : 0 < k) : ‖sbmOneUnit k‖ = 1 := by
  rw [sbmOneUnit, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (one_norm_pos hk), inv_mul_cancel₀ (ne_of_gt (one_norm_pos hk))]

/-- The normalized community-label vector has norm `1`.

**Lean implementation helper.** -/
lemma label_unit_norm {k : ℕ} (hk : 0 < k) : ‖sbmLabelUnit k‖ = 1 := by
  rw [sbmLabelUnit, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (label_norm_pos hk),
    inv_mul_cancel₀ (ne_of_gt (label_norm_pos hk))]

/-- The normalized all-ones vector remains an eigenvector with eigenvalue `k(p+q)`.

**Lean implementation helper.** -/
lemma expected_one_unit_eigen {k : ℕ} (_hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) :
    sbmExpectedOperator k p q (sbmOneUnit k) =
      ((k : ℝ) * ((p : ℝ) + q)) • sbmOneUnit k := by
  simp only [sbmOneUnit, map_smul, expected_one_eigen]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The normalized community-label vector remains an eigenvector with eigenvalue `k(p-q)`.

**Lean implementation helper.** -/
lemma expected_label_unit_eigen {k : ℕ} (_hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) :
    sbmExpectedOperator k p q (sbmLabelUnit k) =
      ((k : ℝ) * ((p : ℝ) - q)) • sbmLabelUnit k := by
  simp only [sbmLabelUnit, map_smul, expected_label_eigen]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- A unit eigenvector with eigenvalue `a` has Rayleigh quotient `a`.

**Lean implementation helper.** -/
lemma eigen_rayleigh {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (x : E) (a : ℝ)
    (hx : T x = a • x) (hxnorm : ‖x‖ = 1) :
    T.reApplyInnerSelf x = a := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, hx, inner_smul_left,
    real_inner_self_eq_norm_sq, hxnorm]
  norm_num

/-- The largest eigenvalue of the expected stochastic-block-model adjacency operator is `k(p+q)`.

**Lean implementation helper.** -/
theorem lambda_zero {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) :
    let hT := sbmExpectedOperator_selfAdjoint k p q
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
      simp [finrank_euclideanSpace]
    hT.isSymmetric.eigenvalues hn ⟨0, by omega⟩ =
      (k : ℝ) * ((p : ℝ) + q) := by
  dsimp only
  let T := sbmExpectedOperator k p q
  let hT := sbmExpectedOperator_selfAdjoint k p q
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  have hvatt := kth_eigenvector_attains_leading_min T hT hn i0
  have hvnorm := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i0
  have hup := rayleigh_upper k p q
    (hT.isSymmetric.eigenvectorBasis hn i0)
  rw [hvatt.2, hvnorm] at hup
  norm_num at hup
  have hxmem : sbmOneUnit k ∈ trailingEigenSphere T hT hn i0 := by
    refine ⟨one_unit_norm hk, ?_⟩
    intro i hi
    change i.val < i0.val at hi
    change i.val < 0 at hi
    omega
  have hlo := (minmax_eigenvalue_trailing T hT hn i0).2
    ⟨sbmOneUnit k, hxmem, rfl⟩
  have hray : T.reApplyInnerSelf (sbmOneUnit k) =
      (k : ℝ) * ((p : ℝ) + q) :=
    eigen_rayleigh T _ _ (expected_one_unit_eigen hk p q)
      (one_unit_norm hk)
  rw [hray] at hlo
  exact le_antisymm hup hlo

/-- Inner product with the all-ones vector equals the sum of coordinates.

**Lean implementation helper.** -/
lemma inner_one (k : ℕ)
    (x : EuclideanSpace ℝ (SBMVertex k)) :
    inner ℝ (sbmOneVector k) x = ∑ i, WithLp.ofLp x i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]

/-- Inner product with the community-label vector equals the label-weighted sum of coordinates.

**Lean implementation helper.** -/
lemma inner_label (k : ℕ)
    (x : EuclideanSpace ℝ (SBMVertex k)) :
    inner ℝ (sbmLabelVector k) x =
      ∑ i, sbmCommunityLabel i * WithLp.ofLp x i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, sbmLabelVector_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- When `q>0`, every unit eigenvector for the top eigenvalue `k(p+q)` is a nonzero multiple of the all-ones vector.

**Lean implementation helper.** -/
lemma top_eigenvector_collinear {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (v : EuclideanSpace ℝ (SBMVertex k)) (hvnorm : ‖v‖ = 1)
    (hv : sbmExpectedOperator k p q v =
      ((k : ℝ) * ((p : ℝ) + q)) • v) :
    ∃ c : ℝ, c ≠ 0 ∧ v = c • sbmOneVector k := by
  let α : ℝ := (k : ℝ) * ((p : ℝ) + q)
  let β : ℝ := (k : ℝ) * ((p : ℝ) - q)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hα : 0 < α := by
    dsimp [α]
    exact mul_pos hkR (add_pos_of_nonneg_of_pos p.2.1 hq)
  have hβα : β < α := by
    dsimp [α, β]
    nlinarith
  have hsym := (sbmExpectedOperator_selfAdjoint k p q).isSymmetric v
    (sbmLabelVector k)
  have hlabelEig := expected_label_eigen k p q
  have hinter : inner ℝ v (sbmLabelVector k) = 0 := by
    change inner ℝ (sbmExpectedOperator k p q v) (sbmLabelVector k) =
      inner ℝ v (sbmExpectedOperator k p q (sbmLabelVector k)) at hsym
    rw [hv, hlabelEig, inner_smul_left, inner_smul_right] at hsym
    change α * inner ℝ v (sbmLabelVector k) =
      β * inner ℝ v (sbmLabelVector k) at hsym
    nlinarith
  have hsumLabel :
      ∑ i, sbmCommunityLabel i * WithLp.ofLp v i = 0 := by
    rw [real_inner_comm, inner_label] at hinter
    exact hinter
  let c : ℝ := (((p : ℝ) + q) / 2 *
    ∑ j, WithLp.ofLp v j) / α
  have hvapply (i : SBMVertex k) : WithLp.ofLp v i = c := by
    have hi := congrArg (fun z : EuclideanSpace ℝ (SBMVertex k) =>
      WithLp.ofLp z i) hv
    change (sbmExpectedAdjacency k p q *ᵥ WithLp.ofLp v) i =
      α * WithLp.ofLp v i at hi
    rw [sbmExpectedAdjacency_mulVec_formula, hsumLabel] at hi
    simp only [zero_mul, mul_zero, add_zero] at hi
    dsimp [c]
    apply (eq_div_iff hα.ne').2
    linarith
  have hvspan : v = c • sbmOneVector k := by
    apply WithLp.ofLp_injective
    funext i
    simp [hvapply i]
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hvspan
    rw [hvspan, norm_zero] at hvnorm
    norm_num at hvnorm
  exact ⟨c, hc, hvspan⟩

/-- Bounds rayleigh by second of orthogonal top.

**Lean implementation helper.** -/
lemma rayleigh_le_second_of_orthogonal_top {k : ℕ} (_hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hqp : (q : ℝ) ≤ p)
    (v x : EuclideanSpace ℝ (SBMVertex k))
    (hvspan : ∃ c : ℝ, c ≠ 0 ∧ v = c • sbmOneVector k)
    (hxorth : inner ℝ v x = 0) :
    (sbmExpectedOperator k p q).reApplyInnerSelf x ≤
      ((k : ℝ) * ((p : ℝ) - q)) * ‖x‖ ^ 2 := by
  obtain ⟨c, hc, rfl⟩ := hvspan
  rw [inner_smul_left, inner_one] at hxorth
  have hsum : ∑ i, WithLp.ofLp x i = 0 :=
    (mul_eq_zero.mp hxorth).resolve_left hc
  rw [rayleigh, hsum]
  norm_num only [zero_pow, mul_zero, zero_add]
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (SBMVertex k)))
    (f := fun i => sbmCommunityLabel i * WithLp.ofLp x i)
  have hcauchy' :
      (∑ i, sbmCommunityLabel i * WithLp.ofLp x i) ^ 2 ≤
        (2 * (k : ℝ)) * ∑ i, WithLp.ofLp x i ^ 2 := by
    simpa [mul_pow, sbmCommunityLabel_sq] using hcauchy
  have hb : 0 ≤ ((p : ℝ) - q) / 2 := by linarith
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ((p : ℝ) - q) / 2 *
        (∑ i, sbmCommunityLabel i * WithLp.ofLp x i) ^ 2 ≤
      ((p : ℝ) - q) / 2 *
        ((2 * (k : ℝ)) * ∑ i, WithLp.ofLp x i ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy' hb
    _ = ((k : ℝ) * ((p : ℝ) - q)) *
        ∑ i, WithLp.ofLp x i ^ 2 := by ring

/-- When `0<q<p`, the second eigenvalue of the expected adjacency operator is `k(p-q)`.

**Lean implementation helper.** -/
theorem lambda_one {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) :
    let hT := sbmExpectedOperator_selfAdjoint k p q
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
      simp [finrank_euclideanSpace]
    hT.isSymmetric.eigenvalues hn ⟨1, by omega⟩ =
      (k : ℝ) * ((p : ℝ) - q) := by
  dsimp only
  let T := sbmExpectedOperator k p q
  let hT := sbmExpectedOperator_selfAdjoint k p q
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let i1 : Fin (2 * k) := ⟨1, by omega⟩
  let v0 := hT.isSymmetric.eigenvectorBasis hn i0
  let v1 := hT.isSymmetric.eigenvectorBasis hn i1
  have hv0norm : ‖v0‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i0
  have hv1norm : ‖v1‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i1
  have hv0eig : T v0 = ((k : ℝ) * ((p : ℝ) + q)) • v0 := by
    have h := hT.isSymmetric.apply_eigenvectorBasis hn i0
    rw [lambda_zero hk p q] at h
    exact h
  have hv0span := top_eigenvector_collinear hk p q hq v0 hv0norm hv0eig
  have hv01 : inner ℝ v0 v1 = 0 := by
    dsimp [v0, v1]
    rw [(hT.isSymmetric.eigenvectorBasis hn).inner_eq_ite]
    simp [i0, i1]
  have hupRay := rayleigh_le_second_of_orthogonal_top hk p q hqp.le
    v0 v1 hv0span hv01
  have hv1ray := (kth_eigenvector_attains_leading_min T hT hn i1).2
  rw [hv1ray, hv1norm] at hupRay
  norm_num at hupRay
  have hv0label : inner ℝ v0 (sbmLabelUnit k) = 0 := by
    obtain ⟨c, _hc, hv0eq⟩ := hv0span
    rw [hv0eq, inner_smul_left, sbmLabelUnit, inner_smul_right,
      inner_one_label]
    simp
  have hlabelMem : sbmLabelUnit k ∈ trailingEigenSphere T hT hn i1 := by
    refine ⟨label_unit_norm hk, ?_⟩
    intro i hi
    have hi0 : i = i0 := by
      apply Fin.ext
      change i.val = 0
      change i.val < i1.val at hi
      change i.val < 1 at hi
      omega
    subst i
    exact hv0label
  have hlo := (minmax_eigenvalue_trailing T hT hn i1).2
    ⟨sbmLabelUnit k, hlabelMem, rfl⟩
  have hlabelRay : T.reApplyInnerSelf (sbmLabelUnit k) =
      (k : ℝ) * ((p : ℝ) - q) :=
    eigen_rayleigh T _ _ (expected_label_unit_eigen hk p q)
      (label_unit_norm hk)
  rw [hlabelRay] at hlo
  exact le_antisymm hupRay hlo

/-- A unit second eigenvector orthogonal to the top eigenspace is a nonzero multiple of the community-label vector.

**Lean implementation helper.** -/
lemma second_eigenvector_collinear {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hqp : (q : ℝ) < p)
    (v0 v1 : EuclideanSpace ℝ (SBMVertex k))
    (hv0span : ∃ c : ℝ, c ≠ 0 ∧ v0 = c • sbmOneVector k)
    (hv01 : inner ℝ v0 v1 = 0) (hv1norm : ‖v1‖ = 1)
    (hv1 : sbmExpectedOperator k p q v1 =
      ((k : ℝ) * ((p : ℝ) - q)) • v1) :
    ∃ c : ℝ, c ≠ 0 ∧ v1 = c • sbmLabelVector k := by
  let β : ℝ := (k : ℝ) * ((p : ℝ) - q)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hβ : 0 < β := by
    dsimp [β]
    exact mul_pos hkR (sub_pos.mpr hqp)
  obtain ⟨a, ha, hv0⟩ := hv0span
  rw [hv0, inner_smul_left, inner_one] at hv01
  have hsum : ∑ i, WithLp.ofLp v1 i = 0 :=
    (mul_eq_zero.mp hv01).resolve_left ha
  let c : ℝ := (((p : ℝ) - q) / 2 *
    ∑ j, sbmCommunityLabel j * WithLp.ofLp v1 j) / β
  have hvapply (i : SBMVertex k) :
      WithLp.ofLp v1 i = c * sbmCommunityLabel i := by
    have hi := congrArg (fun z : EuclideanSpace ℝ (SBMVertex k) =>
      WithLp.ofLp z i) hv1
    change (sbmExpectedAdjacency k p q *ᵥ WithLp.ofLp v1) i =
      β * WithLp.ofLp v1 i at hi
    rw [sbmExpectedAdjacency_mulVec_formula, hsum] at hi
    simp only [mul_zero, zero_add] at hi
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hβ.ne').2
    linarith
  have hvspan : v1 = c • sbmLabelVector k := by
    apply WithLp.ofLp_injective
    funext i
    simp [hvapply i]
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hvspan
    rw [hvspan, norm_zero] at hv1norm
    norm_num at hv1norm
  exact ⟨c, hc, hvspan⟩

/-- All eigenvalues of the expected adjacency operator after the first two are zero.

**Lean implementation helper.** -/
theorem lambda_tail_zero {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) (i : Fin (2 * k)) (hi : 2 ≤ i.val) :
    let hT := sbmExpectedOperator_selfAdjoint k p q
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
      simp [finrank_euclideanSpace]
    hT.isSymmetric.eigenvalues hn i = 0 := by
  dsimp only
  let T := sbmExpectedOperator k p q
  let hT := sbmExpectedOperator_selfAdjoint k p q
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let i1 : Fin (2 * k) := ⟨1, by omega⟩
  let v0 := hT.isSymmetric.eigenvectorBasis hn i0
  let v1 := hT.isSymmetric.eigenvectorBasis hn i1
  let vi := hT.isSymmetric.eigenvectorBasis hn i
  have hv0norm : ‖v0‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i0
  have hv1norm : ‖v1‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i1
  have hv0eig : T v0 = ((k : ℝ) * ((p : ℝ) + q)) • v0 := by
    have h := hT.isSymmetric.apply_eigenvectorBasis hn i0
    rw [lambda_zero hk p q] at h
    exact h
  have hv1eig : T v1 = ((k : ℝ) * ((p : ℝ) - q)) • v1 := by
    have h := hT.isSymmetric.apply_eigenvectorBasis hn i1
    rw [lambda_one hk p q hq hqp] at h
    exact h
  have hv0span := top_eigenvector_collinear hk p q hq v0 hv0norm hv0eig
  have hv01 : inner ℝ v0 v1 = 0 := by
    dsimp [v0, v1]
    rw [(hT.isSymmetric.eigenvectorBasis hn).inner_eq_ite]
    simp [i0, i1]
  have hv1span := second_eigenvector_collinear hk p q hqp v0 v1
    hv0span hv01 hv1norm hv1eig
  have hv0i : inner ℝ v0 vi = 0 := by
    have h0i : i0 ≠ i := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [i0] at hval
      omega
    dsimp [v0, vi]
    rw [(hT.isSymmetric.eigenvectorBasis hn).inner_eq_ite, if_neg h0i]
  have hv1i : inner ℝ v1 vi = 0 := by
    have h1i : i1 ≠ i := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [i1] at hval
      omega
    dsimp [v1, vi]
    rw [(hT.isSymmetric.eigenvectorBasis hn).inner_eq_ite, if_neg h1i]
  obtain ⟨a, ha, hv0⟩ := hv0span
  rw [hv0, inner_smul_left, inner_one] at hv0i
  have hsum : ∑ j, WithLp.ofLp vi j = 0 :=
    (mul_eq_zero.mp hv0i).resolve_left ha
  obtain ⟨b, hb, hv1⟩ := hv1span
  rw [hv1, inner_smul_left, inner_label] at hv1i
  have hsumLabel :
      ∑ j, sbmCommunityLabel j * WithLp.ofLp vi j = 0 :=
    (mul_eq_zero.mp hv1i).resolve_left hb
  have hzero : T.reApplyInnerSelf vi = 0 := by
    rw [rayleigh, hsum, hsumLabel]
    norm_num
  have hivray := (kth_eigenvector_attains_leading_min T hT hn i).2
  dsimp [vi] at hzero
  rw [hivray] at hzero
  exact hzero

/-- The second eigenvalue is separated from every other eigenvalue by at least `k·min(q,p-q)`.

**Lean implementation helper.** -/
theorem expected_gap {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) :
    let hT := sbmExpectedOperator_selfAdjoint k p q
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
      simp [finrank_euclideanSpace]
    let i1 : Fin (2 * k) := ⟨1, by omega⟩
    ∀ i : Fin (2 * k), i ≠ i1 →
      (k : ℝ) * min (q : ℝ) ((p : ℝ) - q) ≤
        |hT.isSymmetric.eigenvalues hn i1 -
          hT.isSymmetric.eigenvalues hn i| := by
  dsimp only
  let T := sbmExpectedOperator k p q
  let hT := sbmExpectedOperator_selfAdjoint k p q
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let i1 : Fin (2 * k) := ⟨1, by omega⟩
  intro i hi1
  rw [lambda_one hk p q hq hqp]
  by_cases hi0v : i.val = 0
  · have hi0 : i = i0 := Fin.ext hi0v
    subst i
    rw [lambda_zero hk p q]
    have hmin : min (q : ℝ) ((p : ℝ) - q) ≤ q := min_le_left _ _
    have hkR : 0 ≤ (k : ℝ) := by positivity
    have habs :
        |(k : ℝ) * ((p : ℝ) - q) -
          (k : ℝ) * ((p : ℝ) + q)| = 2 * (k : ℝ) * q := by
      rw [show (k : ℝ) * ((p : ℝ) - q) -
          (k : ℝ) * ((p : ℝ) + q) = -(2 * (k : ℝ) * q) by ring,
        abs_neg, abs_of_nonneg]
      positivity
    rw [habs]
    nlinarith
  · have hi2 : 2 ≤ i.val := by
      have hi1v : i.val ≠ 1 := by
        intro heq
        apply hi1
        apply Fin.ext
        exact heq
      omega
    rw [lambda_tail_zero hk p q hq hqp i hi2, sub_zero,
      abs_of_nonneg]
    · exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr hqp.le)

/-- A sampled adjacency matrix acts on Euclidean space through its associated continuous linear map.

**Lean implementation helper.** -/
noncomputable def sbmAdjacencyOperator {k : ℕ} (G : SBMSample k) :
    EuclideanSpace ℝ (SBMVertex k) →L[ℝ] EuclideanSpace ℝ (SBMVertex k) :=
  (sbmAdjacencyMatrix G).toEuclideanLin.toContinuousLinearMap

/-- Every realized stochastic-block-model adjacency operator is self-adjoint.

**Lean implementation helper.** -/
lemma sbmAdjacencyOperator_selfAdjoint {k : ℕ} (G : SBMSample k) :
    IsSelfAdjoint (sbmAdjacencyOperator G) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    have hsym : (sbmAdjacencyMatrix G).IsSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      simp [sbmAdjacencyMatrix, Sym2.eq_swap]
    exact isHermitian_iff_isSymm.mpr hsym)

/-- The norm of expected adjacency minus observed adjacency equals the operator norm of the noise matrix.

**Lean implementation helper.** -/
lemma expected_sub_adjacency_norm {k : ℕ}
    (p q : Set.Icc (0 : ℝ) 1) (G : SBMSample k) :
    ‖sbmExpectedOperator k p q - sbmAdjacencyOperator G‖ =
      HDP.matrixOpNorm (sbmNoise p q G) := by
  rw [show sbmExpectedOperator k p q - sbmAdjacencyOperator G =
      (sbmExpectedAdjacency k p q - sbmAdjacencyMatrix G).toEuclideanLin.toContinuousLinearMap by
    ext x
    simp [sbmExpectedOperator, sbmAdjacencyOperator]]
  change HDP.matrixOpNorm
      (sbmExpectedAdjacency k p q - sbmAdjacencyMatrix G) =
    HDP.matrixOpNorm (sbmNoise p q G)
  rw [show sbmExpectedAdjacency k p q - sbmAdjacencyMatrix G =
      -(sbmNoise p q G) by simp [sbmNoise], HDP.matrixOpNorm_neg]

/-- Identifies unit collinear with sign.

**Lean implementation helper.** -/
lemma unit_collinear_eq_sign {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hcol : ∃ c : ℝ, u = c • v) :
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧ u = θ • v := by
  obtain ⟨c, rfl⟩ := hcol
  have hcabs : |c| = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one] at hu
    exact hu
  by_cases hc0 : 0 ≤ c
  · have hc : c = 1 := by simpa [abs_of_nonneg hc0] using hcabs
    exact ⟨c, Or.inl hc, rfl⟩
  · have hcneg : c ≤ 0 := le_of_not_ge hc0
    have hc : c = -1 := by
      rw [abs_of_nonpos hcneg] at hcabs
      linarith
    exact ⟨c, Or.inr hc, rfl⟩

/-- Identifies label vector with norm smul unit.

**Lean implementation helper.** -/
lemma labelVector_eq_norm_smul_unit {k : ℕ} (hk : 0 < k) :
    sbmLabelVector k = ‖sbmLabelVector k‖ • sbmLabelUnit k := by
  rw [sbmLabelUnit, smul_smul]
  rw [mul_inv_cancel₀ (ne_of_gt (label_norm_pos hk)), one_smul]

/-- Identifies expected second eigenvector with sign label unit.

**Lean implementation helper.** -/
lemma expected_secondEigenvector_eq_sign_labelUnit {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) :
    let hT := sbmExpectedOperator_selfAdjoint k p q
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
      simp [finrank_euclideanSpace]
    let i1 : Fin (2 * k) := ⟨1, by omega⟩
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧
      hT.isSymmetric.eigenvectorBasis hn i1 = θ • sbmLabelUnit k := by
  dsimp only
  let T := sbmExpectedOperator k p q
  let hT := sbmExpectedOperator_selfAdjoint k p q
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let i1 : Fin (2 * k) := ⟨1, by omega⟩
  let v0 := hT.isSymmetric.eigenvectorBasis hn i0
  let v1 := hT.isSymmetric.eigenvectorBasis hn i1
  have hv0norm : ‖v0‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i0
  have hv1norm : ‖v1‖ = 1 := (hT.isSymmetric.eigenvectorBasis hn).norm_eq_one i1
  have hv0eig : T v0 = ((k : ℝ) * ((p : ℝ) + q)) • v0 := by
    have h := hT.isSymmetric.apply_eigenvectorBasis hn i0
    rw [lambda_zero hk p q] at h
    exact h
  have hv1eig : T v1 = ((k : ℝ) * ((p : ℝ) - q)) • v1 := by
    have h := hT.isSymmetric.apply_eigenvectorBasis hn i1
    rw [lambda_one hk p q hq hqp] at h
    exact h
  have hv01 : inner ℝ v0 v1 = 0 := by
    dsimp [v0, v1]
    rw [(hT.isSymmetric.eigenvectorBasis hn).inner_eq_ite]
    simp [i0, i1]
  have hv0span := top_eigenvector_collinear hk p q hq v0 hv0norm hv0eig
  obtain ⟨c, _hc, hv1span⟩ := second_eigenvector_collinear hk p q hqp
    v0 v1 hv0span hv01 hv1norm hv1eig
  have hcolUnit : ∃ d : ℝ, v1 = d • sbmLabelUnit k := by
    refine ⟨c * ‖sbmLabelVector k‖, ?_⟩
    calc
      v1 = c • sbmLabelVector k := hv1span
      _ = c • (‖sbmLabelVector k‖ • sbmLabelUnit k) := by
        rw [← labelVector_eq_norm_smul_unit hk]
      _ = (c * ‖sbmLabelVector k‖) • sbmLabelUnit k := by rw [smul_smul]
  exact unit_collinear_eq_sign v1 (sbmLabelUnit k) hv1norm
    (label_unit_norm hk) hcolUnit

/-- The actual second ordered adjacency eigenvector used by spectral clustering.

**Lean implementation helper.** -/
noncomputable def sbmSecondEigenvector {k : ℕ} (hk : 0 < k)
    (G : SBMSample k) : EuclideanSpace ℝ (SBMVertex k) :=
  let B := sbmAdjacencyOperator G
  let hB := sbmAdjacencyOperator_selfAdjoint G
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  hB.isSymmetric.eigenvectorBasis hn ⟨1, by omega⟩

/-- The source's unnormalized spectral estimate, with Euclidean length `sqrt (2k)`, exposed as a
coordinate function.

**Book Chapter 4, pp.121--123, SBM algorithm.** -/
noncomputable def sbmSpectralEstimate {k : ℕ} (hk : 0 < k)
    (G : SBMSample k) : SBMVertex k → ℝ :=
  fun i => ‖sbmLabelVector k‖ * WithLp.ofLp (sbmSecondEigenvector hk G) i

/-- The selected second eigenvector of the observed adjacency matrix has norm `1`.

**Lean implementation helper.** -/
lemma sbmSecondEigenvector_norm {k : ℕ} (hk : 0 < k)
    (G : SBMSample k) : ‖sbmSecondEigenvector hk G‖ = 1 := by
  dsimp [sbmSecondEigenvector]
  exact ((sbmAdjacencyOperator_selfAdjoint G).isSymmetric.eigenvectorBasis
    (by simp [finrank_euclideanSpace])).norm_eq_one ⟨1, by omega⟩

/-- Derives spectral unit distance from noise.

**Lean implementation helper.** -/
theorem spectral_unit_distance_of_noise {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) (G : SBMSample k) {M : ℝ} (hM : 0 ≤ M)
    (hnoise : HDP.matrixOpNorm (sbmNoise p q G) ≤ M) :
    let δ := (k : ℝ) * min (q : ℝ) ((p : ℝ) - q)
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧
      ‖sbmLabelUnit k - θ • sbmSecondEigenvector hk G‖ ≤
        Real.sqrt 2 * (2 * M / δ) := by
  dsimp only
  let D := sbmExpectedOperator k p q
  let B := sbmAdjacencyOperator G
  let hD := sbmExpectedOperator_selfAdjoint k p q
  let hB := sbmAdjacencyOperator_selfAdjoint G
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  let i1 : Fin (2 * k) := ⟨1, by omega⟩
  let u := hD.isSymmetric.eigenvectorBasis hn i1
  let v := hB.isSymmetric.eigenvectorBasis hn i1
  let δ : ℝ := (k : ℝ) * min (q : ℝ) ((p : ℝ) - q)
  have hμ : 0 < min (q : ℝ) ((p : ℝ) - q) :=
    lt_min hq (sub_pos.mpr hqp)
  have hδ : 0 < δ := mul_pos (Nat.cast_pos.mpr hk) hμ
  have hgap : ∀ i : Fin (2 * k), i ≠ i1 →
      δ ≤ |hD.isSymmetric.eigenvalues hn i1 -
        hD.isSymmetric.eigenvalues hn i| := by
    exact expected_gap hk p q hq hqp
  have hsqrt := davisKahan D B hD hB hn i1 hδ hgap
  have hop : ‖D - B‖ ≤ M := by
    rw [expected_sub_adjacency_norm]
    exact hnoise
  have hε : 0 ≤ 2 * M / δ := by positivity
  have hsqrt' : Real.sqrt (1 - |inner ℝ u v| ^ 2) ≤ 2 * M / δ := by
    exact hsqrt.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hop (by norm_num)) hδ.le)
  have hu : ‖u‖ = 1 := (hD.isSymmetric.eigenvectorBasis hn).norm_eq_one i1
  have hv : ‖v‖ = 1 := (hB.isSymmetric.eigenvectorBasis hn).norm_eq_one i1
  have hinner : |inner ℝ u v| ≤ 1 := by
    calc
      |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hu, hv]; norm_num
  have hnonneg : 0 ≤ 1 - |inner ℝ u v| ^ 2 := by
    have hsquare : |inner ℝ u v| ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hinner
    nlinarith
  have hsin : 1 - |inner ℝ u v| ^ 2 ≤ (2 * M / δ) ^ 2 := by
    rw [← Real.sq_sqrt hnonneg]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hε).2 hsqrt'
  obtain ⟨θ, hθ, hdist⟩ := exercise_4_16_angle_sign_distance u v hu hv hε hsin
  obtain ⟨σ, hσ, huLabel⟩ :=
    expected_secondEigenvector_eq_sign_labelUnit hk p q hq hqp
  change u = σ • sbmLabelUnit k at huLabel
  change ‖u - θ • v‖ ≤ Real.sqrt 2 * (2 * M / δ) at hdist
  change ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
    ‖sbmLabelUnit k - τ • v‖ ≤ Real.sqrt 2 * (2 * M / δ)
  rcases hσ with rfl | rfl <;> rcases hθ with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simpa [huLabel] using hdist⟩
  · exact ⟨-1, Or.inr rfl, by simpa [huLabel] using hdist⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [huLabel] at hdist
      calc
        ‖sbmLabelUnit k - (-1 : ℝ) • v‖ =
            ‖sbmLabelUnit k + v‖ := by rw [neg_one_smul, sub_neg_eq_add]
        _ = ‖-(sbmLabelUnit k + v)‖ := (norm_neg _).symm
        _ = ‖(-1 : ℝ) • sbmLabelUnit k - (1 : ℝ) • v‖ := by
          congr 1
          simp only [neg_one_smul, one_smul]
          abel
        _ ≤ _ := hdist⟩
  · exact ⟨1, Or.inl rfl, by
      rw [huLabel] at hdist
      calc
        ‖sbmLabelUnit k - (1 : ℝ) • v‖ =
            ‖sbmLabelUnit k - v‖ := by rw [one_smul]
        _ = ‖-(sbmLabelUnit k - v)‖ := (norm_neg _).symm
        _ = ‖(-1 : ℝ) • sbmLabelUnit k - (-1 : ℝ) • v‖ := by
          congr 1
          simp only [neg_one_smul]
          abel
        _ ≤ _ := hdist⟩

set_option maxHeartbeats 800000 in
-- The coordinate/Euclidean-norm bridge expands the ordered eigenvector definition.
/-- Second-eigenvector signs give a spectral classifier, with misclassification controlled by
eigenvector error modulo label swap.

**Book Chapter 4, pp.121--123, SBM algorithm.** -/
theorem spectral_misclassified_of_noise {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) (G : SBMSample k) {M : ℝ} (hM : 0 ≤ M)
    (hnoise : HDP.matrixOpNorm (sbmNoise p q G) ≤ M) :
    let δ := (k : ℝ) * min (q : ℝ) ((p : ℝ) - q)
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) ≤
      ‖sbmLabelVector k‖ ^ 2 *
        (Real.sqrt 2 * (2 * M / δ)) ^ 2 := by
  dsimp only
  let δ : ℝ := (k : ℝ) * min (q : ℝ) ((p : ℝ) - q)
  obtain ⟨θ, hθ, hdist⟩ :=
    spectral_unit_distance_of_noise hk p q hq hqp G hM hnoise
  let v := sbmSecondEigenvector hk G
  let r : ℝ := ‖sbmLabelVector k‖
  let f : SBMVertex k → ℝ :=
    fun i => sbmCommunityLabel i - θ * sbmSpectralEstimate hk G i
  have hr : 0 ≤ r := norm_nonneg _
  have hvec : WithLp.toLp 2 f =
      r • (sbmLabelUnit k - θ • v) := by
    apply WithLp.ofLp_injective
    funext i
    have hcoord := congrArg
      (fun z : EuclideanSpace ℝ (SBMVertex k) => WithLp.ofLp z i)
      (labelVector_eq_norm_smul_unit hk)
    change sbmCommunityLabel i =
      ‖sbmLabelVector k‖ * WithLp.ofLp (sbmLabelUnit k) i at hcoord
    change sbmCommunityLabel i - θ *
        (‖sbmLabelVector k‖ * WithLp.ofLp (sbmSecondEigenvector hk G) i) =
      r * (WithLp.ofLp (sbmLabelUnit k) i -
        θ * WithLp.ofLp v i)
    rw [hcoord]
    dsimp [r, v]
    ring
  have hsqdist : ‖sbmLabelUnit k - θ • v‖ ^ 2 ≤
      (Real.sqrt 2 * (2 * M / δ)) ^ 2 := by
    have hR : 0 ≤ Real.sqrt 2 * (2 * M / δ) := by
      have hμ : 0 < min (q : ℝ) ((p : ℝ) - q) :=
        lt_min hq (sub_pos.mpr hqp)
      have hδ : 0 < δ := mul_pos (Nat.cast_pos.mpr hk) hμ
      positivity
    exact (sq_le_sq₀ (norm_nonneg _) hR).2 hdist
  have hfbound : ∑ i, f i ^ 2 ≤
      r ^ 2 * (Real.sqrt 2 * (2 * M / δ)) ^ 2 := by
    calc
      ∑ i, f i ^ 2 = ‖WithLp.toLp 2 f‖ ^ 2 :=
        (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 f)).symm
      _ = ‖r • (sbmLabelUnit k - θ • v)‖ ^ 2 := by rw [hvec]
      _ = r ^ 2 * ‖sbmLabelUnit k - θ • v‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
        ring
      _ ≤ r ^ 2 * (Real.sqrt 2 * (2 * M / δ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsqdist (sq_nonneg r)
  have hmis := misclassifiedUpToSign_le_sqError (sbmSpectralEstimate hk G)
  rcases hθ with rfl | rfl
  · exact hmis.trans (le_trans (min_le_left _ _) (by simpa [f] using hfbound))
  · exact hmis.trans (le_trans (min_le_right _ _) (by
      simpa [f] using hfbound))

/-- One explicit absolute constant for the corresponding theorem.

**Lean implementation helper.** -/
noncomputable def sbmSpectralConstant : ℝ :=
  20480000 / Real.log 2

/-- Shows that sbm spectral constant is positive.

**Lean implementation helper.** -/
lemma sbmSpectralConstant_pos : 0 < sbmSpectralConstant := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

/-- On the spectral good event, the number of community-label errors up to global sign is bounded by an explicit constant divided by `min(q,p-q)²`.

**Lean implementation helper.** -/
theorem spectral_good_event_bound {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) (G : SBMSample k)
    (hnoise : HDP.matrixOpNorm (sbmNoise p q G) ≤
      800 * (1 / Real.sqrt (Real.log 2)) * Real.sqrt (2 * k)) :
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) ≤
      sbmSpectralConstant /
        (min (q : ℝ) ((p : ℝ) - q)) ^ 2 := by
  let μ₀ : ℝ := min (q : ℝ) ((p : ℝ) - q)
  let M : ℝ := 800 * (1 / Real.sqrt (Real.log 2)) * Real.sqrt (2 * k)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmis := spectral_misclassified_of_noise hk p q hq hqp G hM hnoise
  change _ ≤ ‖sbmLabelVector k‖ ^ 2 *
    (Real.sqrt 2 * (2 * M / ((k : ℝ) * μ₀))) ^ 2 at hmis
  have hμ : 0 < μ₀ := by
    dsimp [μ₀]
    exact lt_min hq (sub_pos.mpr hqp)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrtlog : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog
  calc
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) ≤
        ‖sbmLabelVector k‖ ^ 2 *
          (Real.sqrt 2 * (2 * M / ((k : ℝ) * μ₀))) ^ 2 := hmis
    _ = sbmSpectralConstant / μ₀ ^ 2 := by
      rw [label_norm_sq]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [M, sbmSpectralConstant]
      ring_nf
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) * 2)]
      field_simp [hkR.ne', hμ.ne', hlog.ne', hsqrtlog.ne']
      rw [Real.sq_sqrt hlog.le]
      ring
    _ = sbmSpectralConstant /
        (min (q : ℝ) ((p : ℝ) - q)) ^ 2 := rfl

/-- Spectral clustering with the actual second ordered adjacency eigenvector, stated in the
equivalent bad-event form.

**Book Theorem 4.5.2.** -/
theorem theorem_4_5_2 {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) :
    (stochasticBlockModel k p q)
      {G | sbmSpectralConstant /
          (min (q : ℝ) ((p : ℝ) - q)) ^ 2 <
        (misclassifiedUpToSign sbmCommunityLabel
          (sbmSpectralEstimate hk G) : ℝ)} ≤
      ENNReal.ofReal (4 * Real.exp (-(2 * k : ℝ))) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let t : ℝ := Real.sqrt (2 * k)
  let M : ℝ := 800 * (1 / Real.sqrt (Real.log 2)) * Real.sqrt (2 * k)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htail0 := sbmNoise_norm_tail (k := k) p q (t := t) ht
  have htSq : t ^ 2 = (2 * k : ℝ) := by
    dsimp [t]
    rw [Real.sq_sqrt]
    positivity
  have hthreshold :
      400 * (1 / Real.sqrt (Real.log 2)) *
        (Real.sqrt (2 * k) + t) = M := by
    dsimp [t, M]
    ring
  have htail :
      (stochasticBlockModel k p q)
        {G | M < HDP.matrixOpNorm (sbmNoise p q G)} ≤
          ENNReal.ofReal (2 * Real.exp (-(2 * k : ℝ))) := by
    rw [hthreshold] at htail0
    rw [htSq] at htail0
    exact htail0
  have hbad :
      {G | sbmSpectralConstant /
          (min (q : ℝ) ((p : ℝ) - q)) ^ 2 <
        (misclassifiedUpToSign sbmCommunityLabel
          (sbmSpectralEstimate hk G) : ℝ)} ⊆
        {G | M < HDP.matrixOpNorm (sbmNoise p q G)} := by
    intro G hG
    by_contra hnot
    have hnoise : HDP.matrixOpNorm (sbmNoise p q G) ≤ M := le_of_not_gt hnot
    have hgood := spectral_good_event_bound hk p q hq hqp G hnoise
    exact (not_lt_of_ge hgood) hG
  calc
    (stochasticBlockModel k p q)
        {G | sbmSpectralConstant /
            (min (q : ℝ) ((p : ℝ) - q)) ^ 2 <
          (misclassifiedUpToSign sbmCommunityLabel
            (sbmSpectralEstimate hk G) : ℝ)} ≤
        (stochasticBlockModel k p q)
          {G | M < HDP.matrixOpNorm (sbmNoise p q G)} := measure_mono hbad
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(2 * k : ℝ))) := htail
    _ ≤ ENNReal.ofReal (4 * Real.exp (-(2 * k : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.exp_pos (-(2 * k : ℝ))]


end HDP.Chapter4

end Source_16_CommunityDetection

/-! ## Material formerly in `17_TwoSidedSubGaussianMatrices.lean` -/

section Source_17_TwoSidedSubGaussianMatrices

/-!
# Chapter 4, §4.6: two-sided bounds for subgaussian matrices

The proof follows the three steps in the source.  We first apply Bernstein to
the squared marginal of each row, then take a union bound over a quarter-net,
and finally use the quadratic-form net lemma to control the normalized Gram
matrix.  The constants below are deliberately explicit; no asymptotic
notation or hidden finiteness convention is used.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator
  Topology Interval

namespace HDP.Chapter4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Integrating a Gaussian quadratic tail. The proof uses layer cake and a monotone change of
variables; in particular, it does not assume that the tail function is continuous.

**Lean implementation helper.** -/
private theorem integral_le_of_quadratic_gaussian_tail [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {Q0 a b : ℝ} (hQ0 : 0 ≤ Q0) (ha : 0 < a) (hb : 0 ≤ b)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | Q0 + a * t + b * t ^ 2 < Z ω} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2))) :
    (∫ ω, Z ω ∂μ) ≤ Q0 + 4 * a + 4 * b := by
  let Q : ℝ → ℝ := fun t => Q0 + a * t + b * t ^ 2
  let Q' : ℝ → ℝ := fun t => a + 2 * b * t
  let g : ℝ → ℝ := fun s => μ.real {ω | s < Z ω}
  have hg0 : ∀ s, 0 ≤ g s := fun s => by positivity
  have hg_le_one : ∀ s, g s ≤ 1 := by
    intro s
    simp [g]
  have hg_meas : Measurable g := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun s t hst =>
      measure_mono fun ω hω => lt_of_le_of_lt hst hω
  have hlayer := hZ.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall hZ0)
  have hkey := lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall hZ0) hZ.aemeasurable
  have hrhsfinite : (∫⁻ s in Ioi (0 : ℝ), μ {ω | s < Z ω}) < ∞ := by
    rw [← hkey]
    exact hZ.lintegral_lt_top
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    refine ⟨hg_meas.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun s => hg0 s)]
    have heq : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g s)) =
        ∫⁻ s in Ioi (0 : ℝ), μ {ω | s < Z ω} := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change ENNReal.ofReal (μ.real {ω | s < Z ω}) = μ {ω | s < Z ω}
      rw [Measure.real_def, ENNReal.ofReal_toReal]
      exact (measure_lt_top μ _).ne
    rw [heq]
    exact hrhsfinite
  have hQderiv : ∀ t, HasDerivAt Q (Q' t) t := by
    intro t
    have h := (((hasDerivAt_const t Q0).add
      ((hasDerivAt_id t).mul_const a)).add
        (((hasDerivAt_id t).pow 2).mul_const b))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp [Q']
      ring
    · filter_upwards [] with x
      dsimp [Q]
      ring
  have hQcont : Continuous Q := by fun_prop
  have hQ'tpos : ∀ t, 0 ≤ t → 0 ≤ Q' t := by
    intro t ht
    dsimp [Q']
    positivity
  have hQtop : Tendsto Q atTop atTop := by
    have hlin : Tendsto (fun t : ℝ => Q0 + a * t) atTop atTop := by
      simpa [add_comm] using
        (tendsto_id.const_mul_atTop ha).atTop_add tendsto_const_nhds
    apply tendsto_atTop_mono' atTop _ hlin
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    dsimp [Q]
    nlinarith [mul_nonneg hb (sq_nonneg t)]
  have htailReal : ∀ t : ℝ, 0 ≤ t →
      g (Q t) ≤ 2 * Real.exp (-t ^ 2) := by
    intro t ht
    have h := htail t ht
    have hfin : ENNReal.ofReal (2 * Real.exp (-t ^ 2)) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal
      (by positivity : 0 ≤ 2 * Real.exp (-t ^ 2))] at hreal
    simpa [g, Q, Measure.real_def] using hreal
  have hgauss0 : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) volume := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hgauss1 : Integrable
      (fun t : ℝ => t * Real.exp (-t ^ 2)) volume := by
    simpa using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hdom : IntegrableOn (fun t : ℝ =>
      2 * Real.exp (-t ^ 2) * Q' t) (Ioi 0) := by
    have hfull : Integrable (fun t : ℝ =>
        2 * Real.exp (-t ^ 2) * (a + 2 * b * t)) := by
      refine ((hgauss0.const_mul (2 * a)).add
        (hgauss1.const_mul (4 * b))).congr ?_
      filter_upwards [] with t
      simp only [Pi.add_apply]
      ring
    simpa [Q'] using hfull.integrableOn
  have hcomp_int : IntegrableOn
      (fun t => (g ∘ Q) t * Q' t) (Ioi 0) := by
    apply Integrable.mono' hdom
    · exact ((hg_meas.comp hQcont.measurable).aestronglyMeasurable.mul
        (by fun_prop : AEStronglyMeasurable Q' (volume.restrict (Ioi 0))))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (hg0 _) (hQ'tpos t ht0))]
      exact mul_le_mul_of_nonneg_right (htailReal t ht0) (hQ'tpos t ht0)
  have hg_tail_int : IntegrableOn g (Ioi Q0) :=
    hg_int.mono_set (Ioi_subset_Ioi hQ0)
  have hsubst : (∫ t in Ioi (0 : ℝ), (g ∘ Q) t * Q' t) =
      ∫ s in Ioi Q0, g s := by
    have hleft := intervalIntegral_tendsto_integral_Ioi
      0 hcomp_int tendsto_id
    have hright0 := intervalIntegral_tendsto_integral_Ioi
      Q0 hg_tail_int tendsto_id
    have hright := hright0.comp hQtop
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hcv := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := T) (g := g)
      hQcont.continuousOn
      (fun x hx => hQderiv x)
      (fun x hx => hQ'tpos x (by
        rw [min_eq_left hT.le, max_eq_right hT.le] at hx
        exact hx.1.le))
    simpa [Q] using hcv.symm
  have htailIntegral : (∫ s in Ioi Q0, g s) ≤ 4 * a + 4 * b := by
    rw [← hsubst]
    calc
      (∫ t in Ioi (0 : ℝ), (g ∘ Q) t * Q' t) ≤
          ∫ t in Ioi (0 : ℝ), 2 * Real.exp (-t ^ 2) * Q' t := by
        exact setIntegral_mono_on hcomp_int hdom measurableSet_Ioi fun t ht =>
          mul_le_mul_of_nonneg_right (htailReal t (mem_Ioi.mp ht).le)
            (hQ'tpos t (mem_Ioi.mp ht).le)
      _ ≤ 4 * a + 4 * b := by
        have h0 : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) ≤ 2 := by
          have heq0 : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) =
              Real.sqrt (Real.pi / 1) / 2 := by
            simpa using integral_gaussian_Ioi 1
          rw [heq0]
          have hsqrt : Real.sqrt (Real.pi / 1) ≤ 4 := by
            nlinarith [Real.sqrt_nonneg (Real.pi / 1),
              Real.sq_sqrt (by positivity : 0 ≤ Real.pi / 1),
              Real.pi_lt_four.le]
          linarith
        have h1 : (∫ t in Ioi (0 : ℝ), t * Real.exp (-t ^ 2)) ≤ 1 := by
          have heq := integral_rpow_mul_exp_neg_rpow
            (show (0 : ℝ) < 2 by norm_num)
            (show (-1 : ℝ) < 1 by norm_num)
          have heq' : (∫ t in Ioi (0 : ℝ),
              t * Real.exp (-t ^ 2)) = 1 / 2 := by
            convert heq using 1
            · apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              simp [Real.rpow_one]
            · norm_num
          rw [heq']
          norm_num
        have heq : (∫ t in Ioi (0 : ℝ),
            2 * Real.exp (-t ^ 2) * Q' t) =
            2 * a * (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) +
              4 * b * (∫ t in Ioi (0 : ℝ),
                t * Real.exp (-t ^ 2)) := by
          rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
          · apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            dsimp [Q']
            ring
          · exact (hgauss0.const_mul (2 * a)).integrableOn
          · exact (hgauss1.const_mul (4 * b)).integrableOn
        rw [heq]
        nlinarith
  rw [hlayer]
  have hsplit : (∫ s in Ioi (0 : ℝ), g s) =
      (∫ s in Ioc (0 : ℝ) Q0, g s) + ∫ s in Ioi Q0, g s := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hg_int.mono_set Ioc_subset_Ioi_self) hg_tail_int]
    rw [Ioc_union_Ioi_eq_Ioi hQ0]
  rw [hsplit]
  have hhead : (∫ s in Ioc (0 : ℝ) Q0, g s) ≤ Q0 := by
    calc
      _ ≤ ∫ _s in Ioc (0 : ℝ) Q0, (1 : ℝ) :=
        setIntegral_mono_on (hg_int.mono_set Ioc_subset_Ioi_self)
          (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
          fun s hs => hg_le_one s
      _ = Q0 := by simp [hQ0]
  linarith

/-- The normalized sample-Gram error as a continuous self-adjoint operator.

**Lean implementation helper.** -/
noncomputable def normalizedGramDeviationOperator {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (HDP.normalizedGram m A - 1).toEuclideanLin.toContinuousLinearMap

/-- Shows that normalized gram deviation operator is self-adjoint.

**Lean implementation helper.** -/
lemma normalizedGramDeviationOperator_isSelfAdjoint {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsSelfAdjoint (normalizedGramDeviationOperator A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  rw [normalizedGramDeviationOperator]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((HDP.gramMatrix_isHermitian A).smul (by simp) |>.sub Matrix.isHermitian_one)

/-- The operator norm of `normalizedGramDeviationOperator A` is exactly `matrixOpNorm (normalizedGram m A - 1)`.

**Lean implementation helper.** -/
@[simp]
lemma norm_normalizedGramDeviationOperator {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖normalizedGramDeviationOperator A‖ =
      HDP.matrixOpNorm (HDP.normalizedGram m A - 1) := by
  rfl

/-- The normalized Gram-deviation Rayleigh quotient is `m⁻¹‖Ax‖²-‖x‖²`.

**Lean implementation helper.** -/
lemma normalizedGramDeviationOperator_rayleigh {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (normalizedGramDeviationOperator A).reApplyInnerSelf x =
      (m : ℝ)⁻¹ * ‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
  change inner ℝ (((HDP.normalizedGram m A - 1).toEuclideanLin) x) x = _
  have hgram : (HDP.gramMatrix A).toEuclideanLin =
      A.toEuclideanLin.adjoint.comp A.toEuclideanLin := by
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp [HDP.gramMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ).toEuclideanLin = LinearMap.id :=
    Matrix.toLpLin_one 2
  change inner ℝ
    (((((m : ℝ)⁻¹ • HDP.gramMatrix A) - 1).toEuclideanLin) x) x = _
  have hsmul : (((m : ℝ)⁻¹ • HDP.gramMatrix A).toEuclideanLin) =
      (m : ℝ)⁻¹ • (HDP.gramMatrix A).toEuclideanLin := by
    ext y i
    simp [Matrix.toLpLin_apply, Matrix.mulVec]
  simp only [map_sub, hsmul,
    LinearMap.sub_apply, LinearMap.smul_apply, hgram, LinearMap.comp_apply,
    hone, LinearMap.id_apply, inner_sub_left, inner_smul_left,
    LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  simp

/-- Squared norm of a matrix-vector product as the sum of the squared row marginals.

**Lean implementation helper.** -/
lemma norm_toEuclideanLin_sq_eq_sum_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖A.toEuclideanLin x‖ ^ 2 =
      ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- Isotropy gives unit second moment in every unit direction. The subgaussian hypothesis
supplies the integrability needed to expand the finite quadratic form.

**Lean implementation helper.** -/
lemma isotropic_row_marginal_secondMoment [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ ω, inner ℝ (HDP.randomMatrixRow A i ω) x ^ 2 ∂μ = ‖x‖ ^ 2 := by
  have hcoordMem : ∀ j : Fin n,
      MemLp (fun ω => HDP.randomMatrixRow A i ω j) 2 μ := by
    intro j
    have hcoordSub : HDP.SubGaussian
        (fun ω => HDP.randomMatrixRow A i ω j) μ := by
      simpa [EuclideanSpace.inner_single_right] using
        hsub.marginal i (EuclideanSpace.single j 1)
    simpa using hcoordSub.memLp
        (by simpa using hrowsm.aemeasurable_entry i j)
        (p := (2 : ℝ)) (by norm_num)
  have hprod : ∀ j k : Fin n, Integrable
      (fun ω => HDP.randomMatrixRow A i ω j *
        HDP.randomMatrixRow A i ω k) μ := by
    intro j k
    exact MemLp.integrable_mul (p := 2) (q := 2) (hcoordMem j) (hcoordMem k)
  have hs := HDP.Chapter3.secondMoment_inner_sq
    (HDP.randomMatrixRow A i) x hprod
  rw [hiso i] at hs
  calc
    ∫ ω, inner ℝ (HDP.randomMatrixRow A i ω) x ^ 2 ∂μ =
        ∑ j : Fin n, x j * x j := by
      simpa [Matrix.one_apply] using hs
    _ = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      congr 1
      funext j
      ring

/-- Every scalar entry of a row-subgaussian matrix belongs to `L²`.

**Lean implementation helper.** -/
lemma randomMatrix_entry_memLp_two [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (i : Fin m) (j : Fin n) :
    MemLp (fun ω => A ω i j) 2 μ := by
  have hcoordSub : HDP.SubGaussian (fun ω => A ω i j) μ := by
    simpa [EuclideanSpace.inner_single_right] using
      hsub.marginal i (EuclideanSpace.single j 1)
  simpa using hcoordSub.memLp (hrowsm.aemeasurable_entry i j)
    (p := (2 : ℝ)) (by norm_num)

/-- A row-subgaussian random matrix has a genuine finite first moment in the finite-dimensional
matrix norm.

**Lean implementation helper.** -/
theorem randomMatrix_integrable [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ) :
    Integrable A μ := by
  have hentry : ∀ i j, Integrable (fun ω => A ω i j) μ := by
    intro i j
    exact (randomMatrix_entry_memLp_two A hrowsm hsub i j).integrable
      (by norm_num)
  have hsum : Integrable (fun ω =>
      ∑ i : Fin m, ∑ j : Fin n,
        (A ω i j) • (Matrix.single i j 1 : Matrix (Fin m) (Fin n) ℝ)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hentry i j).smul_const _
  have hdecomp : (fun ω =>
      ∑ i : Fin m, ∑ j : Fin n,
        (A ω i j) • (Matrix.single i j 1 : Matrix (Fin m) (Fin n) ℝ)) = A := by
    funext ω
    calc
      _ = Matrix.of (A ω) := by simpa using Matrix.sum_sum_single (A ω)
      _ = A ω := by ext i j; rfl
  rwa [hdecomp] at hsum

/-- Every singular value of a row-subgaussian random matrix is integrable. This follows from
Weyl's one-Lipschitz estimate and matrix integrability.

**Lean implementation helper.** -/
theorem matrixSingularValue_integrable [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (i : Fin n) :
    Integrable (fun ω => HDP.matrixSingularValue (A ω) i) μ := by
  have hA := randomMatrix_integrable A hrowsm hsub
  have hlip : LipschitzWith 1
      (fun M : Matrix (Fin m) (Fin n) ℝ => HDP.matrixSingularValue M i) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro X Y
    simpa [Real.dist_eq, HDP.matrixOpNorm, dist_eq_norm] using
      weylSingularValue X Y i
  have hmeas : AEStronglyMeasurable
      (fun ω => HDP.matrixSingularValue (A ω) i) μ :=
    hlip.continuous.comp_aestronglyMeasurable hA.aestronglyMeasurable
  apply Integrable.mono' hA.norm hmeas
  filter_upwards [] with ω
  have hw := weylSingularValue (A ω) 0 i
  simpa [HDP.matrixSingularValue, HDP.matrixOpNorm,
    abs_of_nonneg (HDP.matrixSingularValue_nonneg (A ω) i)] using hw

/-- The normalized Gram error has a genuine finite first moment. This is proved entrywise from
the `L²` row marginals and is used, rather than assumed, in the corresponding remark.

**Lean implementation helper.** -/
theorem normalizedGramDeviation_integrable [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ) :
    Integrable (fun ω =>
      HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1)) μ := by
  have hentry : ∀ i j : Fin n, Integrable (fun ω =>
      (m : ℝ)⁻¹ * (∑ r : Fin m, A ω r i * A ω r j) -
        (if i = j then 1 else 0)) μ := by
    intro i j
    have hsum : Integrable (fun ω => ∑ r : Fin m, A ω r i * A ω r j) μ :=
      integrable_finsetSum _ fun r _ =>
        MemLp.integrable_mul (p := 2) (q := 2)
          (randomMatrix_entry_memLp_two A hrowsm hsub r i)
          (randomMatrix_entry_memLp_two A hrowsm hsub r j)
    exact (hsum.const_mul (m : ℝ)⁻¹).sub (integrable_const _)
  have hmat : Integrable (fun ω => HDP.normalizedGram m (A ω) - 1) μ := by
    let M : Ω → Matrix (Fin n) (Fin n) ℝ :=
      fun ω => HDP.normalizedGram m (A ω) - 1
    have hMentry : ∀ i j : Fin n, Integrable (fun ω => M ω i j) μ := by
      intro i j
      convert hentry i j using 1
      funext ω
      simp [M, HDP.normalizedGram, HDP.gramMatrix, Matrix.mul_apply,
        Matrix.one_apply]
    have hsum : Integrable (fun ω =>
        ∑ i : Fin n, ∑ j : Fin n,
          (M ω i j) • (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℝ)) μ :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hMentry i j).smul_const _
    have hdecomp : (fun ω =>
        ∑ i : Fin n, ∑ j : Fin n,
          (M ω i j) • (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℝ)) = M := by
      funext ω
      calc
        _ = Matrix.of (M ω) := by simpa using (Matrix.sum_sum_single (M ω))
        _ = M ω := by ext i j; rfl
    rw [hdecomp] at hsum
    simpa [M] using hsum
  simpa [HDP.matrixOpNorm] using hmat.norm

/-- A fixed unit direction has the normalized squared-norm concentration used in Step 2 of the
proof of the corresponding theorem.

**Lean implementation helper.** -/
theorem fixed_direction_normalized_sq_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
        min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
          (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) := by
  let X : Fin m → Ω → ℝ :=
    fun i ω => inner ℝ (HDP.randomMatrixRow A i ω) x
  have hXm : ∀ i, AEMeasurable (X i) μ := fun i =>
    hrowsm.aemeasurable_marginal i x
  have hX : ∀ i, HDP.SubGaussian (X i) μ := fun i => hsub.marginal i x
  have hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1 := by
    intro i
    simpa [X, hx] using isotropic_row_marginal_secondMoment A hrowsm hsub hiso i x
  have hXindep : iIndepFun X μ :=
    hindep.comp (fun _ z => inner ℝ z x) (fun _ => by fun_prop)
  have hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K := by
    intro i
    exact (HDP.psi2Norm_marginal_le_vector (hfinite i) hx).trans (hpsi i)
  have hbern := HDP.Chapter3.norm_sq_bernstein hm hXm hX hsecond hXindep hK hKb hu
  have hsum : ∀ ω,
      (∑ i : Fin m, (1 / (m : ℝ)) * (X i ω ^ 2 - 1)) =
        (m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1 := by
    intro ω
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp_rw [X, HDP.inner_randomMatrixRow]
    rw [norm_toEuclideanLin_sq_eq_sum_rows]
    simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hm.ne']
  have hcoeff : ∑ _i : Fin m, (1 / (m : ℝ)) ^ 2 = 1 / (m : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hm.ne']
  simpa only [hsum, hcoeff] using hbern

/-- Explicit constant in the source's `δ = C(√(n/m)+t/√m)`.

**Lean implementation helper.** -/
def twoSidedGramConstant : ℝ := 100

/-- Shows that two sided gram constant is positive.

**Lean implementation helper.** -/
lemma twoSidedGramConstant_pos : 0 < twoSidedGramConstant := by
  norm_num [twoSidedGramConstant]

/-- The numerical estimate that absorbs the cardinality `9^n` of the net.

**Lean implementation helper.** -/
private theorem twoSided_net_union_numerics {m n : ℕ} (hm : 0 < m)
    {K t : ℝ} (hK : 0 < K) (ht : 0 ≤ t) :
    let δ := twoSidedGramConstant *
      (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
    let u := K ^ 2 * max δ (δ ^ 2) / 2
    (9 : ℝ≥0∞) ^ n * ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
        min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
          (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  dsimp only
  let δ : ℝ := twoSidedGramConstant *
    (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
  let v : ℝ := max δ (δ ^ 2)
  let u : ℝ := K ^ 2 * v / 2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hnm : 0 ≤ (n : ℝ) / m := by positivity
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg twoSidedGramConstant_pos.le (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hv : 0 ≤ v := hδ.trans (le_max_left _ _)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hδv : δ ≤ v := le_max_left _ _
  have hδsqv : δ ^ 2 ≤ v := le_max_right _ _
  have hsqroot : Real.sqrt ((n : ℝ) / m) ^ 2 = (n : ℝ) / m :=
    Real.sq_sqrt hnm
  have hsqrtmsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt hmR.le
  have hma : (m : ℝ) * Real.sqrt ((n : ℝ) / m) ^ 2 = (n : ℝ) := by
    rw [hsqroot]
    field_simp [hmR.ne']
  have hmb : (m : ℝ) * (t / Real.sqrt m) ^ 2 = t ^ 2 := by
    rw [div_pow, hsqrtmsq]
    field_simp [hmR.ne']
  have hmdelta : (10000 : ℝ) * ((n : ℝ) + t ^ 2) ≤ (m : ℝ) * δ ^ 2 := by
    calc
      (10000 : ℝ) * ((n : ℝ) + t ^ 2) =
          10000 * ((m : ℝ) * Real.sqrt ((n : ℝ) / m) ^ 2 +
            (m : ℝ) * (t / Real.sqrt m) ^ 2) := by rw [hma, hmb]
      _ ≤ 10000 * (m : ℝ) *
          (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m) ^ 2 := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg ((n : ℝ) / m))
          (div_nonneg ht hsqrtm.le)]
      _ = (m : ℝ) * δ ^ 2 := by
        dsimp [δ, twoSidedGramConstant]
        ring
  have hfirst : (m : ℝ) * δ ^ 2 / 64 ≤
      u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))) := by
    dsimp [u]
    field_simp [hK.ne', hmR.ne']
    nlinarith [sq_le_sq₀ hδ hv |>.2 hδv]
  have hsecond : (m : ℝ) * δ ^ 2 / 8 ≤
      u / ((4 * K ^ 2) * (1 / (m : ℝ))) := by
    dsimp [u]
    field_simp [hK.ne', hmR.ne']
    nlinarith
  have hsecond64 : (m : ℝ) * δ ^ 2 / 64 ≤
      u / ((4 * K ^ 2) * (1 / (m : ℝ))) := by
    apply le_trans (b := (m : ℝ) * δ ^ 2 / 8)
    · nlinarith [mul_nonneg hmR.le (sq_nonneg δ)]
    · exact hsecond
  have hmin : (m : ℝ) * δ ^ 2 / 64 ≤
      min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
        (u / ((4 * K ^ 2) * (1 / (m : ℝ)))) :=
    le_min hfirst hsecond64
  have hexponent : 3 * (n : ℝ) + t ^ 2 ≤
      (1 / 8 : ℝ) * min
        (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
        (u / ((4 * K ^ 2) * (1 / (m : ℝ)))) := by
    calc
      3 * (n : ℝ) + t ^ 2 ≤
          (1 / 8 : ℝ) * ((m : ℝ) * δ ^ 2 / 64) := by
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by norm_num)
  have h9 : (9 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hpow : (9 : ℝ) ^ n ≤ Real.exp (3 * (n : ℝ)) := by
    calc
      (9 : ℝ) ^ n ≤ (Real.exp 3) ^ n :=
        pow_le_pow_left₀ (by norm_num) h9 n
      _ = Real.exp (3 * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have htail : Real.exp (-(1 / 8 : ℝ) * min
        (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
        (u / ((4 * K ^ 2) * (1 / (m : ℝ))))) ≤
      Real.exp (-(3 * (n : ℝ) + t ^ 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hreal : (9 : ℝ) ^ n *
        (2 * Real.exp (-(1 / 8 : ℝ) * min
          (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
          (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) ≤
      2 * Real.exp (-t ^ 2) := by
    calc
      _ ≤ Real.exp (3 * (n : ℝ)) *
          (2 * Real.exp (-(3 * (n : ℝ) + t ^ 2))) :=
        mul_le_mul hpow (mul_le_mul_of_nonneg_left htail (by norm_num))
          (by positivity) (by positivity)
      _ = 2 * (Real.exp (3 * (n : ℝ)) *
          Real.exp (-(3 * (n : ℝ) + t ^ 2))) := by ring
      _ = 2 * Real.exp (3 * (n : ℝ) + -(3 * (n : ℝ) + t ^ 2)) := by
        rw [Real.exp_add]
      _ = 2 * Real.exp (-t ^ 2) := by ring_nf
  rw [show (9 : ℝ≥0∞) ^ n = ENNReal.ofReal ((9 : ℝ) ^ n) by
      rw [ENNReal.ofReal_pow] <;> norm_num]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (9 : ℝ) ^ n)]
  apply ENNReal.ofReal_le_ofReal
  simpa [δ, v, u] using hreal

/-- The rows are genuinely assumed independent, isotropic and subgaussian. The boundedness
hypotheses are the safety conditions needed by the real-valued vector `ψ₂` supremum.

**Book Theorem 4.6.1.** -/
theorem theorem_4_6_1_gram [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    {t : ℝ} (ht : 0 ≤ t) :
    let δ := twoSidedGramConstant *
      (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
    μ {ω | K ^ 2 * max δ (δ ^ 2) <
        HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  dsimp only
  classical
  let δ : ℝ := twoSidedGramConstant *
    (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
  let q : ℝ := K ^ 2 * max δ (δ ^ 2)
  let u : ℝ := q / 2
  have hm : 0 < m := NeZero.pos m
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg twoSidedGramConstant_pos.le
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  obtain ⟨N, hN, hNcard⟩ := exists_quarter_unitSphereNet n
  let E : EuclideanSpace ℝ (Fin n) → Set Ω := fun x =>
    {ω | u ≤ |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1|}
  have hbad : {ω | q < HDP.matrixOpNorm
        (HDP.normalizedGram m (A ω) - 1)} ⊆ ⋃ x ∈ N, E x := by
    intro ω hω
    simp only [Set.mem_iUnion]
    by_contra hnone
    push Not at hnone
    have hnet : ∀ x ∈ (N : Set (EuclideanSpace ℝ (Fin n))),
        |inner ℝ (normalizedGramDeviationOperator (A ω) x) x| ≤ u := by
      intro x hx
      have hlt := hnone x (by simpa using hx)
      have hxunit := hN.1 x hx
      have hray := normalizedGramDeviationOperator_rayleigh (A ω) x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real] at hray
      rw [hray, hxunit, one_pow]
      have hnot : ¬u ≤ |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1| := by
        simpa [E] using hlt
      exact (lt_of_not_ge hnot).le
    have hop := opNorm_le_of_quadratic_on_net
      (normalizedGramDeviationOperator (A ω))
      (normalizedGramDeviationOperator_isSelfAdjoint (A ω)).isSymmetric
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : 2 * (1 / 4 : ℝ) < 1) hN hu hnet
    have hop' : HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1) ≤ q := by
      rw [← norm_normalizedGramDeviationOperator]
      calc
        ‖normalizedGramDeviationOperator (A ω)‖ ≤
            u / (1 - 2 * (1 / 4 : ℝ)) := hop
        _ = q := by dsimp [u]; ring
    exact (not_le_of_gt hω) hop'
  have hpoint : ∀ x ∈ N, μ (E x) ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
        min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
          (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) := by
    intro x hx
    exact fixed_direction_normalized_sq_tail hm A hrowsm hsub hiso hindep
      hfinite hK hpsi x (hN.1 x (by simpa using hx)) hu
  calc
    μ {ω | q < HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1)}
        ≤ μ (⋃ x ∈ N, E x) := measure_mono hbad
    _ ≤ ∑ x ∈ N, μ (E x) := measure_biUnion_finset_le N E
    _ ≤ ∑ _x ∈ N, ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
          min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
            (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) :=
      Finset.sum_le_sum fun x hx => hpoint x hx
    _ = (N.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
          min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
            (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) := by simp
    _ ≤ (9 : ℝ≥0∞) ^ n * ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
          min (u ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
            (u / ((4 * K ^ 2) * (1 / (m : ℝ)))))) :=
      mul_le_mul_of_nonneg_right hNcard (by positivity)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
      simpa [δ, q, u] using
        twoSided_net_union_numerics (m := m) (n := n) hm hK ht

/-- Explicit absolute constant for the corresponding remark.

**Lean implementation helper.** -/
def gramExpectationConstant : ℝ := 200000

/-- Shows that gram expectation constant is positive.

**Lean implementation helper.** -/
lemma gramExpectationConstant_pos : 0 < gramExpectationConstant := by
  norm_num [gramExpectationConstant]

/-- This is derived from the tail statement of the corresponding theorem. Integrability is
proved entrywise above, rather than included as an additional hypothesis.

**Book Remark 4.6.2.** -/
theorem theorem_4_6_1_gram_expectation [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    (∫ ω, HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1) ∂μ) ≤
      gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m) := by
  let r : ℝ := Real.sqrt ((n : ℝ) / m)
  let d : ℝ := twoSidedGramConstant / Real.sqrt m
  let δ0 : ℝ := twoSidedGramConstant * r
  let Q0 : ℝ := K ^ 2 * (δ0 + δ0 ^ 2)
  let a : ℝ := K ^ 2 * (d + 2 * δ0 * d)
  let b : ℝ := K ^ 2 * d ^ 2
  let Z : Ω → ℝ := fun ω =>
    HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg twoSidedGramConstant_pos.le (Real.sqrt_nonneg _)
  have hδ0 : 0 ≤ δ0 := by
    dsimp [δ0]
    exact mul_nonneg twoSidedGramConstant_pos.le hr0
  have hQ0 : 0 ≤ Q0 := by dsimp [Q0]; positivity
  have ha : 0 < a := by
    dsimp [a]
    have hdpos : 0 < d := by
      dsimp [d]
      exact div_pos twoSidedGramConstant_pos hsqrtm
    positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hZint : Integrable Z μ := by
    simpa [Z] using normalizedGramDeviation_integrable A hrowsm hsub
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by
    dsimp [Z]
    exact HDP.matrixOpNorm_nonneg _
  have htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | Q0 + a * t + b * t ^ 2 < Z ω} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
    intro t ht
    let δ : ℝ := twoSidedGramConstant *
      (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact mul_nonneg twoSidedGramConstant_pos.le
        (add_nonneg (Real.sqrt_nonneg _) (div_nonneg ht hsqrtm.le))
    have hδeq : δ = δ0 + d * t := by
      dsimp [δ, δ0, d, r]
      ring
    have hmax : max δ (δ ^ 2) ≤ δ + δ ^ 2 := by
      exact max_le (by nlinarith [sq_nonneg δ]) (by linarith)
    have hthreshold : K ^ 2 * max δ (δ ^ 2) ≤
        Q0 + a * t + b * t ^ 2 := by
      calc
        K ^ 2 * max δ (δ ^ 2) ≤ K ^ 2 * (δ + δ ^ 2) :=
          mul_le_mul_of_nonneg_left hmax (sq_nonneg K)
        _ = Q0 + a * t + b * t ^ 2 := by
          rw [hδeq]
          dsimp [Q0, a, b]
          ring
    calc
      μ {ω | Q0 + a * t + b * t ^ 2 < Z ω} ≤
          μ {ω | K ^ 2 * max δ (δ ^ 2) < Z ω} := by
        apply measure_mono
        intro ω hω
        exact lt_of_le_of_lt hthreshold hω
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
        simpa [δ, Z] using theorem_4_6_1_gram
          A hrowsm hsub hiso hindep hfinite hK hpsi ht
  have hmain := integral_le_of_quadratic_gaussian_tail
    Z hZint hZ0 hQ0 ha hb htail
  have hr2 : r ^ 2 = (n : ℝ) / m := by
    dsimp [r]
    exact Real.sq_sqrt (by positivity)
  have hs2 : (1 / Real.sqrt (m : ℝ)) ^ 2 = 1 / (m : ℝ) := by
    rw [div_pow, Real.sq_sqrt hmR.le]
    norm_num
  have hratio : (1 / (m : ℝ)) ≤ (n : ℝ) / m := by
    rw [div_le_div_iff_of_pos_right hmR]
    exact hnR
  have hsle : 1 / Real.sqrt (m : ℝ) ≤ r := by
    apply (sq_le_sq₀ (by positivity) hr0).mp
    rw [hs2, hr2]
    exact hratio
  have hdle : d ≤ twoSidedGramConstant * r := by
    dsimp [d]
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hsle twoSidedGramConstant_pos.le
  have hrdle : r * d ≤ twoSidedGramConstant * r ^ 2 := by
    calc
      r * d ≤ r * (twoSidedGramConstant * r) :=
        mul_le_mul_of_nonneg_left hdle hr0
      _ = twoSidedGramConstant * r ^ 2 := by ring
  have hd2le : d ^ 2 ≤ twoSidedGramConstant ^ 2 * r ^ 2 := by
    have hdδ : d ≤ δ0 := by simpa [δ0] using hdle
    simpa [δ0, mul_pow] using (sq_le_sq₀ hd0 hδ0).2 hdδ
  have hbound : Q0 + 4 * a + 4 * b ≤
      gramExpectationConstant * K ^ 2 * (r + r ^ 2) := by
    dsimp [Q0, a, b, δ0, twoSidedGramConstant,
      gramExpectationConstant] at *
    nlinarith [sq_nonneg K, sq_nonneg r]
  calc
    (∫ ω, Z ω ∂μ) ≤ Q0 + 4 * a + 4 * b := hmain
    _ ≤ gramExpectationConstant * K ^ 2 * (r + r ^ 2) := hbound
    _ = gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m) := by
      rw [hr2]

/-- Compatibility name matching the source's numbering of the expectation consequence.

**Book Remark 4.6.2.** -/
theorem remark_4_6_2 [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    (∫ ω, HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1) ∂μ) ≤
      gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m) :=
  theorem_4_6_1_gram_expectation A hrowsm hsub hiso hindep hfinite hK hpsi

/-- Scalar square-root transfer used to pass from normalized Gram eigenvalues to singular
values.

**Lean implementation helper.** -/
private lemma abs_sub_one_le_of_abs_sq_sub_one_le {z η : ℝ}
    (hz : 0 ≤ z) (hη : 0 ≤ η)
    (h : |z ^ 2 - 1| ≤ max η (η ^ 2)) : |z - 1| ≤ η := by
  by_cases hη1 : η ≤ 1
  · rw [max_eq_left (by nlinarith [sq_nonneg η])] at h
    rw [abs_le] at h ⊢
    constructor <;> nlinarith [sq_nonneg (z - 1)]
  · have hηge : 1 ≤ η := le_of_not_ge hη1
    rw [max_eq_right (by nlinarith)] at h
    rw [abs_le] at h
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (z - 1)]

/-- A normalized Gram-error bound controls every (not only the extreme) singular value.

**Lean implementation helper.** -/
theorem normalizedGramError_singularValue_ratio {m n : ℕ}
    (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) {η : ℝ} (hη : 0 ≤ η)
    (hA : HDP.matrixOpNorm (HDP.normalizedGram m A - 1) ≤
      max η (η ^ 2)) :
    |HDP.matrixSingularValue A i / Real.sqrt m - 1| ≤ η := by
  let v := rightSingularBasis A i
  have hv := singularValue_attained A i
  have hq := (normalizedGramDeviationOperator A).rayleighQuotient_le_norm v
  have hinner : |(normalizedGramDeviationOperator A).reApplyInnerSelf v| ≤
      max η (η ^ 2) := by
    have hq' : |(normalizedGramDeviationOperator A).reApplyInnerSelf v| ≤
        ‖normalizedGramDeviationOperator A‖ := by
      simpa [ContinuousLinearMap.rayleighQuotient, v, hv.1] using hq
    exact hq'.trans (by simpa using hA)
  rw [normalizedGramDeviationOperator_rayleigh, hv.1, hv.2, one_pow] at hinner
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsqrtsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  have hrewrite :
      (HDP.matrixSingularValue A i / Real.sqrt m) ^ 2 =
        (m : ℝ)⁻¹ * HDP.matrixSingularValue A i ^ 2 := by
    field_simp [hsqrt.ne']
    rw [hsqrtsq]
  apply abs_sub_one_le_of_abs_sq_sub_one_le
    (div_nonneg (HDP.matrixSingularValue_nonneg A i) hsqrt.le) hη
  rwa [hrewrite]

/-- Isotropy prevents the uniform row `ψ₂` bound from being arbitrarily small. This quantitative
lower bound is what makes (4.27) imply (4.26).

**Lean implementation helper.** -/
lemma half_le_sq_of_isotropic_rowPsi2Bound [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    (1 / 2 : ℝ) ≤ K ^ 2 := by
  let i : Fin m := ⟨0, NeZero.pos m⟩
  let j : Fin n := ⟨0, NeZero.pos n⟩
  let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have hx : ‖x‖ = 1 := by simp [x]
  let X : Ω → ℝ := fun ω => inner ℝ (HDP.randomMatrixRow A i ω) x
  have hXm : AEMeasurable X μ := hrowsm.aemeasurable_marginal i x
  have hX : HDP.SubGaussian X μ := hsub.marginal i x
  have hsecond : ∫ ω, X ω ^ 2 ∂μ = 1 := by
    simpa [X, hx] using isotropic_row_marginal_secondMoment A hrowsm hsub hiso i x
  have hKb : HDP.psi2Norm X μ ≤ K :=
    (HDP.psi2Norm_marginal_le_vector (hfinite i) hx).trans (hpsi i)
  have h := HDP.Chapter3.one_le_two_mul_sq_of_secondMoment_one
    hXm hX hsecond hK hKb
  linarith

/-- Explicit absolute constant in the singular-value form (4.26).

**Lean implementation helper.** -/
def twoSidedSingularConstant : ℝ := 200

/-- Shows that two sided singular constant is positive.

**Lean implementation helper.** -/
lemma twoSidedSingularConstant_pos : 0 < twoSidedSingularConstant := by
  norm_num [twoSidedSingularConstant]

/-- This first wrapper keeps the dimensionless source parameter `δ`; the following theorem
rewrites it into the displayed `√m ± C K²(√n+t)` form.

**Book Theorem 4.6.1.** -/
theorem theorem_4_6_1_singular_normalized [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    {t : ℝ} (ht : 0 ≤ t) :
    let δ := twoSidedGramConstant *
      (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
    let η := 2 * K ^ 2 * δ
    μ {ω | Real.sqrt m * (1 - η) >
          HDP.matrixSingularValue (A ω) (n - 1) ∨
        HDP.matrixSingularValue (A ω) 0 > Real.sqrt m * (1 + η)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  dsimp only
  let δ : ℝ := twoSidedGramConstant *
    (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m)
  let η : ℝ := 2 * K ^ 2 * δ
  let q : ℝ := K ^ 2 * max δ (δ ^ 2)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg twoSidedGramConstant_pos.le
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hKlower := half_le_sq_of_isotropic_rowPsi2Bound
    A hrowsm hsub hiso hfinite hK hpsi
  have hqη : q ≤ max η (η ^ 2) := by
    by_cases hcase : δ ≤ δ ^ 2
    · rw [show q = K ^ 2 * δ ^ 2 by simp [q, max_eq_right hcase] ]
      exact (show K ^ 2 * δ ^ 2 ≤ η ^ 2 by
        dsimp [η]
        nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg δ)]).trans
          (le_max_right _ _)
    · have hcase' : δ ^ 2 ≤ δ := le_of_not_ge hcase
      rw [show q = K ^ 2 * δ by simp [q, max_eq_left hcase'] ]
      exact (show K ^ 2 * δ ≤ η by
        dsimp [η]
        nlinarith [mul_nonneg (sq_nonneg K) hδ]).trans (le_max_left _ _)
  have hsubset :
      {ω | Real.sqrt m * (1 - η) >
            HDP.matrixSingularValue (A ω) (n - 1) ∨
          HDP.matrixSingularValue (A ω) 0 > Real.sqrt m * (1 + η)} ⊆
        {ω | q < HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1)} := by
    intro ω hω
    by_contra hnot
    have hgram : HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1) ≤
        max η (η ^ 2) := (le_of_not_gt hnot).trans hqη
    have hn : 0 < n := NeZero.pos n
    have hlo := normalizedGramError_singularValue_ratio (NeZero.pos m)
      (A ω) ⟨n - 1, by omega⟩ hη hgram
    have hhi := normalizedGramError_singularValue_ratio (NeZero.pos m)
      (A ω) ⟨0, NeZero.pos n⟩ hη hgram
    rw [abs_le] at hlo hhi
    have hsqrt : 0 < Real.sqrt (m : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (NeZero.pos m))
    have hlower : Real.sqrt m * (1 - η) ≤
        HDP.matrixSingularValue (A ω) (n - 1) := by
      have hdiv : 1 - η ≤
          HDP.matrixSingularValue (A ω) (n - 1) / Real.sqrt m := by
        linarith [hlo.1]
      have := (le_div_iff₀ hsqrt).mp hdiv
      simpa [mul_comm] using this
    have hupper : HDP.matrixSingularValue (A ω) 0 ≤
        Real.sqrt m * (1 + η) := by
      have hdiv : HDP.matrixSingularValue (A ω) 0 / Real.sqrt m ≤
          1 + η := by
        linarith [hhi.2]
      have := (div_le_iff₀ hsqrt).mp hdiv
      simpa [mul_comm] using this
    exact hω.elim (not_lt_of_ge hlower) (not_lt_of_ge hupper)
  calc
    μ {ω | Real.sqrt m * (1 - η) >
          HDP.matrixSingularValue (A ω) (n - 1) ∨
        HDP.matrixSingularValue (A ω) 0 > Real.sqrt m * (1 + η)}
        ≤ μ {ω | q < HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω) - 1)} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
      simpa [δ, q] using theorem_4_6_1_gram
        A hrowsm hsub hiso hindep hfinite hK hpsi ht

/-- Cancellation identity needed to rewrite the dimensionless Gram parameter into the source's
`√n` normalization.

**Lean implementation helper.** -/
lemma sqrt_mul_sqrt_nat_div {m n : ℕ} (hm : 0 < m) :
    Real.sqrt (m : ℝ) * Real.sqrt ((n : ℝ) / m) = Real.sqrt n := by
  have hsqrtm : Real.sqrt (m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne'
  rw [Real.sqrt_div (by positivity : 0 ≤ (n : ℝ))]
  field_simp [hsqrtm]

/-- Gives simultaneous upper and lower singular-value deviations for a matrix with independent
isotropic subgaussian rows.

**Book Theorem 4.6.1.** -/
theorem theorem_4_6_1_singular [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
          (Real.sqrt n + t) > HDP.matrixSingularValue (A ω) (n - 1) ∨
        HDP.matrixSingularValue (A ω) 0 >
          Real.sqrt m + twoSidedSingularConstant * K ^ 2 *
            (Real.sqrt n + t)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  have h := theorem_4_6_1_singular_normalized
    A hrowsm hsub hiso hindep hfinite hK hpsi ht
  have hsqrt := sqrt_mul_sqrt_nat_div (n := n) (NeZero.pos m)
  have hsqrtm : Real.sqrt (m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos m)).ne'
  have htdiv : Real.sqrt (m : ℝ) * (t / Real.sqrt m) = t := by
    field_simp [hsqrtm]
  have hid : Real.sqrt (m : ℝ) *
      (2 * K ^ 2 * (100 *
        (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m))) =
        200 * K ^ 2 * (Real.sqrt n + t) := by
    calc
      _ = 200 * K ^ 2 *
          (Real.sqrt m * Real.sqrt ((n : ℝ) / m) +
            Real.sqrt m * (t / Real.sqrt m)) := by ring
      _ = _ := by rw [hsqrt, htdiv]
  have hminus : Real.sqrt (m : ℝ) *
      (1 - 2 * K ^ 2 * (100 *
        (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m))) =
      Real.sqrt m - 200 * K ^ 2 * (Real.sqrt n + t) := by
    rw [mul_sub, mul_one, hid]
  have hplus : Real.sqrt (m : ℝ) *
      (1 + 2 * K ^ 2 * (100 *
        (Real.sqrt ((n : ℝ) / m) + t / Real.sqrt m))) =
      Real.sqrt m + 200 * K ^ 2 * (Real.sqrt n + t) := by
    rw [mul_add, mul_one, hid]
  simpa only [twoSidedSingularConstant, twoSidedGramConstant,
    hminus, hplus] using h

/-- Explicit absolute constant for the singular-value expectation bounds in the corresponding
exercise.

**Lean implementation helper.** -/
def singularExpectationConstant : ℝ := 1000

/-- Shows that singular expectation constant is positive.

**Lean implementation helper.** -/
lemma singularExpectationConstant_pos : 0 < singularExpectationConstant := by
  norm_num [singularExpectationConstant]

/-- This is promoted to the core because it supplies the expectation form of the two-sided
random-matrix theorem.

**Book Exercise 4.41.** -/
theorem exercise_4_41b_singular_expectation [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    Real.sqrt m - singularExpectationConstant * K ^ 2 * Real.sqrt n ≤
        ∫ ω, HDP.matrixSingularValue (A ω) (n - 1) ∂μ ∧
      (∫ ω, HDP.matrixSingularValue (A ω) 0 ∂μ) ≤
        Real.sqrt m + singularExpectationConstant * K ^ 2 * Real.sqrt n := by
  let slo : Ω → ℝ := fun ω => HDP.matrixSingularValue (A ω) (n - 1)
  let shi : Ω → ℝ := fun ω => HDP.matrixSingularValue (A ω) 0
  let Zlo : Ω → ℝ := fun ω => max (Real.sqrt m - slo ω) 0
  let Zhi : Ω → ℝ := fun ω => max (shi ω - Real.sqrt m) 0
  let Q0 : ℝ := twoSidedSingularConstant * K ^ 2 * Real.sqrt n
  let a : ℝ := twoSidedSingularConstant * K ^ 2
  have hslo : Integrable slo μ := by
    simpa [slo] using matrixSingularValue_integrable A hrowsm hsub
      ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩
  have hshi : Integrable shi μ := by
    simpa [shi] using matrixSingularValue_integrable A hrowsm hsub
      ⟨0, NeZero.pos n⟩
  have integrable_max_zero {f : Ω → ℝ} (hf : Integrable f μ) :
      Integrable (fun ω => max (f ω) 0) μ := by
    refine ⟨(hf.aemeasurable.max aemeasurable_const).aestronglyMeasurable, ?_⟩
    exact hf.hasFiniteIntegral.max_zero
  have hZlo : Integrable Zlo μ := by
    exact integrable_max_zero ((integrable_const _).sub hslo)
  have hZhi : Integrable Zhi μ := by
    exact integrable_max_zero (hshi.sub (integrable_const _))
  have hQ0 : 0 ≤ Q0 := by
    dsimp [Q0, twoSidedSingularConstant]
    positivity
  have ha : 0 < a := by
    dsimp [a, twoSidedSingularConstant]
    positivity
  have htailLo : ∀ t : ℝ, 0 ≤ t →
      μ {ω | Q0 + a * t + 0 * t ^ 2 < Zlo ω} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
    intro t ht
    calc
      μ {ω | Q0 + a * t + 0 * t ^ 2 < Zlo ω} ≤
          μ {ω | Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
                (Real.sqrt n + t) > slo ω ∨
            shi ω > Real.sqrt m + twoSidedSingularConstant * K ^ 2 *
                (Real.sqrt n + t)} := by
        apply measure_mono
        intro ω hω
        left
        change Q0 + a * t + 0 * t ^ 2 < Zlo ω at hω
        have hthreshold : Q0 + a * t + 0 * t ^ 2 =
            twoSidedSingularConstant * K ^ 2 * (Real.sqrt n + t) := by
          dsimp [Q0, a]
          ring
        rw [hthreshold] at hω
        have hle : Real.sqrt m - slo ω ≤ 0 → False := by
          intro hnonpos
          rw [show Zlo ω = 0 by simp [Zlo, max_eq_right hnonpos] ] at hω
          exact (not_lt_of_ge (by positivity)) hω
        have hpos : 0 ≤ Real.sqrt m - slo ω := by
          by_contra hnot
          exact hle (lt_of_not_ge hnot).le
        rw [show Zlo ω = Real.sqrt m - slo ω by
          simp [Zlo, max_eq_left hpos] ] at hω
        linarith
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
        simpa [slo, shi] using theorem_4_6_1_singular
          A hrowsm hsub hiso hindep hfinite hK hpsi ht
  have htailHi : ∀ t : ℝ, 0 ≤ t →
      μ {ω | Q0 + a * t + 0 * t ^ 2 < Zhi ω} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
    intro t ht
    calc
      μ {ω | Q0 + a * t + 0 * t ^ 2 < Zhi ω} ≤
          μ {ω | Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
                (Real.sqrt n + t) > slo ω ∨
            shi ω > Real.sqrt m + twoSidedSingularConstant * K ^ 2 *
                (Real.sqrt n + t)} := by
        apply measure_mono
        intro ω hω
        right
        change Q0 + a * t + 0 * t ^ 2 < Zhi ω at hω
        have hthreshold : Q0 + a * t + 0 * t ^ 2 =
            twoSidedSingularConstant * K ^ 2 * (Real.sqrt n + t) := by
          dsimp [Q0, a]
          ring
        rw [hthreshold] at hω
        have hle : shi ω - Real.sqrt m ≤ 0 → False := by
          intro hnonpos
          rw [show Zhi ω = 0 by simp [Zhi, max_eq_right hnonpos] ] at hω
          exact (not_lt_of_ge (by positivity)) hω
        have hpos : 0 ≤ shi ω - Real.sqrt m := by
          by_contra hnot
          exact hle (lt_of_not_ge hnot).le
        rw [show Zhi ω = shi ω - Real.sqrt m by
          simp [Zhi, max_eq_left hpos] ] at hω
        linarith
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
        simpa [slo, shi] using theorem_4_6_1_singular
          A hrowsm hsub hiso hindep hfinite hK hpsi ht
  have hEZlo := integral_le_of_quadratic_gaussian_tail
    Zlo hZlo (fun ω => by dsimp [Zlo]; exact le_max_right _ _)
    hQ0 ha (le_refl 0) htailLo
  have hEZhi := integral_le_of_quadratic_gaussian_tail
    Zhi hZhi (fun ω => by dsimp [Zhi]; exact le_max_right _ _)
    hQ0 ha (le_refl 0) htailHi
  have hsqrtn : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast NeZero.pos n
  have hEbound : Q0 + 4 * a + 4 * 0 ≤
      singularExpectationConstant * K ^ 2 * Real.sqrt n := by
    dsimp [Q0, a, twoSidedSingularConstant, singularExpectationConstant]
    nlinarith [mul_le_mul_of_nonneg_left hsqrtn (sq_nonneg K)]
  have hloPoint : ∀ ω, Real.sqrt m - Zlo ω ≤ slo ω := by
    intro ω
    have := le_max_left (Real.sqrt m - slo ω) 0
    dsimp [Zlo]
    linarith
  have hhiPoint : ∀ ω, shi ω ≤ Real.sqrt m + Zhi ω := by
    intro ω
    have := le_max_left (shi ω - Real.sqrt m) 0
    dsimp [Zhi]
    linarith
  constructor
  · calc
      Real.sqrt m - singularExpectationConstant * K ^ 2 * Real.sqrt n ≤
          Real.sqrt m - ∫ ω, Zlo ω ∂μ := by
        linarith [hEZlo.trans hEbound]
      _ = ∫ ω, (Real.sqrt m - Zlo ω) ∂μ := by
        rw [integral_sub (integrable_const _) hZlo]
        simp
      _ ≤ ∫ ω, slo ω ∂μ :=
        integral_mono ((integrable_const _).sub hZlo) hslo hloPoint
  · calc
      (∫ ω, shi ω ∂μ) ≤
          ∫ ω, (Real.sqrt m + Zhi ω) ∂μ :=
        integral_mono hshi ((integrable_const _).add hZhi) hhiPoint
      _ = Real.sqrt m + ∫ ω, Zhi ω ∂μ := by
        rw [integral_add (integrable_const _) hZhi]
        simp
      _ ≤ Real.sqrt m +
          singularExpectationConstant * K ^ 2 * Real.sqrt n := by
        linarith [hEZhi.trans hEbound]

/-- Bounds the expected normalized Gram error and the expected extreme singular values.

**Book Exercise 4.41.** -/
theorem exercise_4_41b [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    ((∫ ω, HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1) ∂μ) ≤
        gramExpectationConstant * K ^ 2 *
          (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m)) ∧
      (Real.sqrt m - singularExpectationConstant * K ^ 2 * Real.sqrt n ≤
          ∫ ω, HDP.matrixSingularValue (A ω) (n - 1) ∂μ ∧
        (∫ ω, HDP.matrixSingularValue (A ω) 0 ∂μ) ≤
          Real.sqrt m + singularExpectationConstant * K ^ 2 * Real.sqrt n) := by
  exact ⟨theorem_4_6_1_gram_expectation
      A hrowsm hsub hiso hindep hfinite hK hpsi,
    exercise_4_41b_singular_expectation
      A hrowsm hsub hiso hindep hfinite hK hpsi⟩

/-! ### Column restriction infrastructure for Exercise 4.47 -/

/-- The coordinate inclusion `ℝᵏ → ℝⁿ`, padded by zeros after coordinate `k`.

**Lean implementation helper.** -/
noncomputable def leadingCoordinateLinearMap {k n : ℕ} (_hkn : k ≤ n) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun u := WithLp.toLp 2 fun j =>
    if hj : j.val < k then u ⟨j.val, hj⟩ else 0
  map_add' u v := by
    ext j
    by_cases hj : j.val < k <;> simp [hj]
  map_smul' c u := by
    ext j
    by_cases hj : j.val < k <;> simp [hj]

/-- The leading-coordinate inclusion sends coordinate `j` to `u j` when `j < k` and to `0` otherwise.

**Lean implementation helper.** -/
@[simp]
lemma leadingCoordinateLinearMap_apply {k n : ℕ} (hkn : k ≤ n)
    (u : EuclideanSpace ℝ (Fin k)) (j : Fin n) :
    leadingCoordinateLinearMap hkn u j =
      if hj : j.val < k then u ⟨j.val, hj⟩ else 0 := rfl

/-- The linear map retaining the first `k` coordinates preserves Euclidean norm on `ℝ^k`.

**Lean implementation helper.** -/
lemma leadingCoordinateLinearMap_norm {k n : ℕ} (hkn : k ≤ n)
    (u : EuclideanSpace ℝ (Fin k)) :
    ‖leadingCoordinateLinearMap hkn u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  change (∑ j : Fin n, ‖leadingCoordinateLinearMap hkn u j‖ ^ 2) =
    ∑ i : Fin k, ‖u i‖ ^ 2
  calc
    (∑ j : Fin n, ‖leadingCoordinateLinearMap hkn u j‖ ^ 2) =
        ∑ j ∈ (Finset.univ.filter fun j : Fin n => j.val < k),
          ‖leadingCoordinateLinearMap hkn u j‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      have hjnot : ¬j.val < k := by simpa using hnot
      simp [leadingCoordinateLinearMap_apply, hjnot]
    _ = ∑ i : Fin k, ‖u i‖ ^ 2 := by
      symm
      apply Finset.sum_bij (fun i _ => Fin.castLE hkn i)
      · intro i hi
        simp
      · intro i₁ hi₁ i₂ hi₂ heq
        exact Fin.castLE_injective hkn heq
      · intro j hj
        have hjlt : j.val < k := (Finset.mem_filter.mp hj).2
        exact ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro i hi
        simp [leadingCoordinateLinearMap_apply]

/-- The coordinate inclusion as a genuine linear isometry.

**Lean implementation helper.** -/
noncomputable def leadingCoordinateIsometry {k n : ℕ} (hkn : k ≤ n) :
    EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearMap := leadingCoordinateLinearMap hkn
  norm_map' := leadingCoordinateLinearMap_norm hkn

/-- The leading-coordinate isometry sends coordinate `j` to `u j` when `j < k` and to `0` otherwise.

**Lean implementation helper.** -/
@[simp]
lemma leadingCoordinateIsometry_apply {k n : ℕ} (hkn : k ≤ n)
    (u : EuclideanSpace ℝ (Fin k)) (j : Fin n) :
    leadingCoordinateIsometry hkn u j =
      if hj : j.val < k then u ⟨j.val, hj⟩ else 0 := rfl

/-- Restriction to the first `k` columns.

**Lean implementation helper.** -/
def leadingColumnRestriction {m k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin k) ℝ :=
  A.submatrix id (Fin.castLE hkn)

/-- Entry `(i,j)` of the leading-column restriction is `A i (Fin.castLE hkn j)`.

**Lean implementation helper.** -/
@[simp]
lemma leadingColumnRestriction_apply {m k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin k) :
    leadingColumnRestriction hkn A i j = A i (Fin.castLE hkn j) := rfl

/-- A coordinate sum against the leading-coordinate embedding reduces to the corresponding sum over the first `k` coordinates.

**Lean implementation helper.** -/
lemma sum_mul_leadingCoordinateIsometry {k n : ℕ} (hkn : k ≤ n)
    (a : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin k)) :
    (∑ j : Fin n, a j * leadingCoordinateIsometry hkn u j) =
      ∑ i : Fin k, a (Fin.castLE hkn i) * u i := by
  calc
    (∑ j : Fin n, a j * leadingCoordinateIsometry hkn u j) =
        ∑ j ∈ (Finset.univ.filter fun j : Fin n => j.val < k),
          a j * leadingCoordinateIsometry hkn u j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      have hjnot : ¬j.val < k := by simpa using hnot
      simp [leadingCoordinateIsometry_apply, hjnot]
    _ = ∑ i : Fin k, a (Fin.castLE hkn i) * u i := by
      symm
      apply Finset.sum_bij (fun i _ => Fin.castLE hkn i)
      · intro i hi
        simp
      · intro i₁ hi₁ i₂ hi₂ heq
        exact Fin.castLE_injective hkn heq
      · intro j hj
        have hjlt : j.val < k := (Finset.mem_filter.mp hj).2
        exact ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro i hi
        simp [leadingCoordinateIsometry_apply]

/-- Pairing a row of the leading-column restriction with `u` equals pairing the original row with the embedded vector.

**Lean implementation helper.** -/
lemma inner_leadingColumnRestriction_row {Ω' : Type*} {m k n : ℕ}
    (hkn : k ≤ n) (A : Ω' → Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (ω : Ω') (u : EuclideanSpace ℝ (Fin k)) :
    inner ℝ
        (HDP.randomMatrixRow
          (fun ω => leadingColumnRestriction hkn (A ω)) i ω) u =
      inner ℝ (HDP.randomMatrixRow A i ω)
        (leadingCoordinateIsometry hkn u) := by
  rw [HDP.inner_randomMatrixRow, HDP.inner_randomMatrixRow]
  exact (sum_mul_leadingCoordinateIsometry hkn (A ω i) u).symm

/-- Applying the leading-column restriction equals applying the original matrix after embedding the first `k` coordinates.

**Lean implementation helper.** -/
lemma toEuclideanLin_leadingColumnRestriction {m k n : ℕ}
    (hkn : k ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    (leadingColumnRestriction hkn A).toEuclideanLin u =
      A.toEuclideanLin (leadingCoordinateIsometry hkn u) := by
  ext i
  simp only [Matrix.toLpLin_apply]
  exact (sum_mul_leadingCoordinateIsometry hkn (A i) u).symm

/-- Restricting a random matrix to its first `k` columns preserves almost-everywhere measurability of rows.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_aemeasurableRows {m k n : ℕ} (hkn : k ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ) :
    HDP.RandomMatrix.AEMeasurableRows
      (fun ω => leadingColumnRestriction hkn (A ω)) μ := by
  apply HDP.RandomMatrix.AEMeasurableEntries.aemeasurable_rows
  intro i j
  exact hrowsm.aemeasurable_entry i (Fin.castLE hkn j)

/-- Restricting a random matrix to its first `k` columns preserves subgaussian rows.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_subGaussianRows {m k n : ℕ} (hkn : k ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ) :
    HDP.RandomMatrix.SubGaussianRows
      (fun ω => leadingColumnRestriction hkn (A ω)) μ := by
  intro i u
  simpa only [inner_leadingColumnRestriction_row] using
    hsub.marginal i (leadingCoordinateIsometry hkn u)

/-- Restricting a random matrix to its first `k` columns preserves isotropic rows.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_isotropicRows {m k n : ℕ} (hkn : k ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ) :
    HDP.RandomMatrix.IsotropicRows
      (fun ω => leadingColumnRestriction hkn (A ω)) μ := by
  intro i
  apply HDP.isIsotropic_iff.mpr
  intro a b
  have h := HDP.isIsotropic_iff.mp (hiso i)
    (Fin.castLE hkn a) (Fin.castLE hkn b)
  simpa [leadingColumnRestriction,
    (Fin.castLE_injective hkn).eq_iff] using h

/-- Restricting a random matrix to its first `k` columns preserves independence of rows.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_independentRows {m k n : ℕ} (hkn : k ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ) :
    HDP.RandomMatrix.IndependentRows
      (fun ω => leadingColumnRestriction hkn (A ω)) μ := by
  let proj : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k) :=
    fun z => WithLp.toLp 2 (fun j => z (Fin.castLE hkn j))
  have hproj : Measurable proj := by
    dsimp [proj]
    fun_prop
  have h := hindep.comp (fun _ => proj) (fun _ => hproj)
  apply h.congr
  intro i
  filter_upwards [] with ω
  ext j
  rfl

/-- Every unit-direction marginal of a leading-column-restricted row has `ψ₂` norm at most the original row bound `K`.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_direction_psi2_le {m k n : ℕ} (hkn : k ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (i : Fin m) (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    HDP.psi2Norm (fun ω => inner ℝ
      (HDP.randomMatrixRow
        (fun ω => leadingColumnRestriction hkn (A ω)) i ω) u) μ ≤ K := by
  have hunit : ‖leadingCoordinateIsometry hkn u‖ = 1 := by
    rw [LinearIsometry.norm_map, hu]
  have h :=
    (HDP.psi2Norm_marginal_le_vector (hfinite i) hunit).trans (hpsi i)
  simpa only [inner_leadingColumnRestriction_row] using h

/-- Restricting to leading columns preserves finiteness of all row `ψ₂` norms.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_rowPsi2Finite {m k n : ℕ} (hkn : k ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    HDP.RandomMatrix.RowPsi2Finite
      (fun ω => leadingColumnRestriction hkn (A ω)) μ := by
  intro i
  refine ⟨K, ?_⟩
  intro r hr
  rcases hr with ⟨u, hu, rfl⟩
  exact leadingColumnRestriction_direction_psi2_le hkn A hfinite hpsi i u hu

/-- Restricting to leading columns preserves a uniform row `ψ₂` bound.

**Lean implementation helper.** -/
lemma leadingColumnRestriction_rowPsi2Bound {m k n : ℕ} [NeZero k]
    (hkn : k ≤ n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    HDP.RandomMatrix.RowPsi2Bound
      (fun ω => leadingColumnRestriction hkn (A ω)) μ K := by
  intro i
  rw [HDP.psi2NormVector]
  apply csSup_le
  · let u0 : EuclideanSpace ℝ (Fin k) :=
      EuclideanSpace.single ⟨0, NeZero.pos k⟩ 1
    exact ⟨HDP.psi2Norm (fun ω => inner ℝ
      (HDP.randomMatrixRow
        (fun ω => leadingColumnRestriction hkn (A ω)) i ω) u0) μ,
      u0, by simp [u0], rfl⟩
  · intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact leadingColumnRestriction_direction_psi2_le hkn A hfinite hpsi i u hu

/-- Restricting to `k` columns can only decrease the least singular value of the restriction
below the `k`th singular value of the original matrix.

**Lean implementation helper.** -/
lemma leastSingularValue_le_intermediate {m k n : ℕ} [NeZero k]
    (hkn : k ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixSingularValue (leadingColumnRestriction hkn A) (k - 1) ≤
      HDP.matrixSingularValue A (k - 1) := by
  have hkpos : 0 < k := NeZero.pos k
  let L := leadingCoordinateIsometry hkn
  let B := leadingColumnRestriction hkn A
  let iA : Fin n :=
    ⟨k - 1, lt_of_lt_of_le (Nat.sub_lt hkpos zero_lt_one) hkn⟩
  have hVdim : Module.finrank ℝ L.toLinearMap.range = iA.val + 1 := by
    rw [LinearMap.finrank_range_of_inj L.injective,
      finrank_euclideanSpace_fin]
    dsimp [iA]
    omega
  obtain ⟨x, hxV, hxnorm, hxA⟩ :=
    (singularValueMinMax A iA).1.1 L.toLinearMap.range hVdim
  rcases LinearMap.mem_range.mp hxV with ⟨u, hu⟩
  change L u = x at hu
  have huNorm : ‖u‖ = 1 := by
    rw [← L.norm_map u, hu]
    exact hxnorm
  have hB := (extremeSingularValues_bound B u).1
  calc
    HDP.matrixSingularValue (leadingColumnRestriction hkn A) (k - 1) =
        HDP.matrixSingularValue B (k - 1) * ‖u‖ := by
      rw [huNorm, mul_one]
    _ ≤ ‖B.toEuclideanLin u‖ := hB
    _ = ‖A.toEuclideanLin (L u)‖ :=
      congrArg norm (toEuclideanLin_leadingColumnRestriction hkn A u)
    _ = ‖A.toEuclideanLin x‖ := by rw [hu]
    _ ≤ HDP.matrixSingularValue A iA := hxA
    _ = HDP.matrixSingularValue A (k - 1) := rfl

/-- The `k`th singular value has the same lower-tail bound as the least singular value of an `m
× k` column restriction.

**Book Exercise 4.47.** -/
theorem exercise_4_47 [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
          (Real.sqrt k + t) > HDP.matrixSingularValue (A ω) (k - 1)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  letI : NeZero k := ⟨by omega⟩
  let B : Ω → Matrix (Fin m) (Fin k) ℝ :=
    fun ω => leadingColumnRestriction hkn (A ω)
  have hBm : HDP.RandomMatrix.AEMeasurableRows B μ :=
    leadingColumnRestriction_aemeasurableRows hkn A hrowsm
  have hBs : HDP.RandomMatrix.SubGaussianRows B μ :=
    leadingColumnRestriction_subGaussianRows hkn A hsub
  have hBi : HDP.RandomMatrix.IsotropicRows B μ :=
    leadingColumnRestriction_isotropicRows hkn A hiso
  have hBind : HDP.RandomMatrix.IndependentRows B μ :=
    leadingColumnRestriction_independentRows hkn A hindep
  have hBfinite : HDP.RandomMatrix.RowPsi2Finite B μ :=
    leadingColumnRestriction_rowPsi2Finite hkn A hfinite hpsi
  have hBpsi : HDP.RandomMatrix.RowPsi2Bound B μ K :=
    leadingColumnRestriction_rowPsi2Bound hkn A hfinite hpsi
  calc
    μ {ω | Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
          (Real.sqrt k + t) > HDP.matrixSingularValue (A ω) (k - 1)} ≤
        μ {ω | Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
              (Real.sqrt k + t) > HDP.matrixSingularValue (B ω) (k - 1) ∨
            HDP.matrixSingularValue (B ω) 0 >
              Real.sqrt m + twoSidedSingularConstant * K ^ 2 *
                (Real.sqrt k + t)} := by
      apply measure_mono
      intro ω hω
      left
      change Real.sqrt m - twoSidedSingularConstant * K ^ 2 *
          (Real.sqrt k + t) > HDP.matrixSingularValue (A ω) (k - 1) at hω
      exact lt_of_le_of_lt (leastSingularValue_le_intermediate hkn (A ω)) hω
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
      exact theorem_4_6_1_singular
        B hBm hBs hBi hBind hBfinite hK hBpsi ht

end HDP.Chapter4

end Source_17_TwoSidedSubGaussianMatrices

/-! ## Material formerly in `18_CovarianceEstimation.lean` -/

section Source_18_CovarianceEstimation

/-!
# Chapter 4, §4.7: covariance estimation

The sample covariance in the source is an uncentered sample second moment.  This
file keeps that distinction explicit.  The factorized API below also covers
singular population covariance matrices: a rectangular factor `B` is allowed,
so no inverse or whitening map is hidden in the statement.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace Topology

namespace HDP.Chapter4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The rank-one matrix `x xᵀ`.

**Lean implementation helper.** -/
def outerProductMatrix {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j k => x j * x k

/-- The data matrix whose rows are the observations.

**Lean implementation helper.** -/
def dataMatrix {m n : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => X i j

/-- Source-facing name for the uncentered sample covariance/second-moment matrix. It agrees
definitionally with the shared Prelude construction.

**Book Theorem 4.7.1.** -/
noncomputable def sampleCovarianceMatrix {m n : ℕ}
    (X : Fin m → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  HDP.sampleSecondMoment m X

/-- Entry `(j,k)` of the sample covariance matrix is `m⁻¹ * ∑ i, X i j * X i k`.

**Lean implementation helper.** -/
@[simp]
theorem sampleCovarianceMatrix_apply {m n : ℕ}
    (X : Fin m → EuclideanSpace ℝ (Fin n)) (j k : Fin n) :
    sampleCovarianceMatrix X j k =
      (m : ℝ)⁻¹ * ∑ i, X i j * X i k :=
  rfl

/-- The sample second moment is the normalized Gram matrix of the data matrix.

**Lean implementation helper.** -/
theorem sampleCovarianceMatrix_eq_normalizedGram {m n : ℕ}
    (X : Fin m → EuclideanSpace ℝ (Fin n)) :
    sampleCovarianceMatrix X = HDP.normalizedGram m (dataMatrix X) := by
  ext j k
  simp [sampleCovarianceMatrix, HDP.sampleSecondMoment, HDP.normalizedGram,
    HDP.gramMatrix, dataMatrix, Matrix.mul_apply]

/-- The finite-sample estimator is unbiased, entry by entry. Product integrability is stated
explicitly instead of being smuggled through a real valued expectation notation.

**Book Theorem 4.7.1.** -/
theorem sampleCovarianceMatrix_unbiased_entry [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (X : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hint : ∀ i j k, Integrable (fun ω => X i ω j * X i ω k) μ)
    (hsecond : ∀ i j k,
      ∫ ω, X i ω j * X i ω k ∂μ = Sigma j k)
    (j k : Fin n) :
    ∫ ω, sampleCovarianceMatrix (fun i => X i ω) j k ∂μ = Sigma j k := by
  rw [show (fun ω => sampleCovarianceMatrix (fun i => X i ω) j k) =
      fun ω => (m : ℝ)⁻¹ * ∑ i, X i ω j * X i ω k by rfl,
    integral_const_mul, integral_finsetSum]
  · simp_rw [hsecond]
    simp [hm.ne']
  · intro i hi
    exact hint i j k

/-- Entrywise strong law for sample second moments. Since there are finitely many entries,
intersecting these almost-sure events gives the matrix convergence asserted in the discussion
preceding the corresponding theorem.

**Book Theorem 4.7.1.** -/
theorem sampleSecondMoment_strongLaw_entry
    {n : ℕ} (X : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (j k : Fin n)
    (hint : Integrable (fun ω => X 0 ω j * X 0 ω k) μ)
    (hindep : ∀ ⦃i l : ℕ⦄, i ≠ l →
      (fun ω => X i ω j * X i ω k) ⟂ᵢ[μ]
        (fun ω => X l ω j * X l ω k))
    (hident : ∀ i, IdentDistrib
      (fun ω => X i ω j * X i ω k)
      (fun ω => X 0 ω j * X 0 ω k) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun m : ℕ =>
        (∑ i ∈ Finset.range m, X i ω j * X i ω k) / (m : ℝ))
      atTop (𝓝 (∫ ω, X 0 ω j * X 0 ω k ∂μ)) := by
  exact strong_law_ae_real
    (fun i ω => X i ω j * X i ω k) hint hindep hident

/-- Normalized Gram matrices commute with a deterministic right factor.

**Lean implementation helper.** -/
theorem normalizedGram_mul_transpose {m n r : ℕ}
    (Z : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin n) (Fin r) ℝ) :
    HDP.normalizedGram m (Z * B.transpose) =
      B * HDP.normalizedGram m Z * B.transpose := by
  simp [HDP.normalizedGram, HDP.gramMatrix, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Factors the sample second-moment error through the normalized Gram error, for rectangular
`B`.

**Book (4.30).** -/
theorem factorized_sampleCovariance_sub {m n r : ℕ}
    (Z : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin n) (Fin r) ℝ) :
    HDP.normalizedGram m (Z * B.transpose) - B * B.transpose =
      B * (HDP.normalizedGram m Z - 1) * B.transpose := by
  rw [normalizedGram_mul_transpose]
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- Bounds the factorized sample second-moment error in operator norm even when the population
second moment `B Bᵀ` is singular.

**Book (4.30).** -/
theorem factorized_sampleCovariance_error_le {m n r : ℕ}
    (Z : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin n) (Fin r) ℝ) :
    HDP.matrixOpNorm
        (HDP.normalizedGram m (Z * B.transpose) - B * B.transpose) ≤
      HDP.matrixOpNorm (HDP.normalizedGram m Z - 1) *
        HDP.matrixOpNorm (B * B.transpose) := by
  rw [factorized_sampleCovariance_sub]
  have h1 := HDP.matrixOpNorm_mul B (HDP.normalizedGram m Z - 1)
  have h2 := HDP.matrixOpNorm_mul
    (B * (HDP.normalizedGram m Z - 1)) B.transpose
  have hBt : HDP.matrixOpNorm B.transpose = HDP.matrixOpNorm B :=
    HDP.matrixOpNorm_transpose B
  have hSigma : HDP.matrixOpNorm (B * B.transpose) =
      HDP.matrixOpNorm B ^ 2 := by
    have h := HDP.matrixOpNorm_sq_eq_gram B.transpose
    simpa [HDP.gramMatrix] using h.symm
  calc
    HDP.matrixOpNorm (B * (HDP.normalizedGram m Z - 1) * B.transpose)
        ≤ HDP.matrixOpNorm (B * (HDP.normalizedGram m Z - 1)) *
            HDP.matrixOpNorm B.transpose := h2
    _ ≤ (HDP.matrixOpNorm B *
          HDP.matrixOpNorm (HDP.normalizedGram m Z - 1)) *
            HDP.matrixOpNorm B.transpose :=
      mul_le_mul_of_nonneg_right h1 (HDP.matrixOpNorm_nonneg _)
    _ = HDP.matrixOpNorm (HDP.normalizedGram m Z - 1) *
          HDP.matrixOpNorm (B * B.transpose) := by
      rw [hBt, hSigma]
      ring

/-- A Gram tail bound transfers directly to covariance estimation without an invertibility
assumption.

**Lean implementation helper.** -/
theorem factorized_covariance_tail_of_gram_tail
    {m n r : ℕ} (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) (q : ℝ) :
    μ {ω | q * HDP.matrixOpNorm (B * B.transpose) <
        HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)} ≤
      μ {ω | q < HDP.matrixOpNorm
        (HDP.normalizedGram m (A ω) - 1)} := by
  apply measure_mono
  intro ω hω
  by_contra hnot
  have hgram : HDP.matrixOpNorm (HDP.normalizedGram m (A ω) - 1) ≤ q :=
    le_of_not_gt hnot
  have hdet := factorized_sampleCovariance_error_le (A ω) B
  exact (not_le_of_gt hω) (hdet.trans (mul_le_mul_of_nonneg_right hgram
    (HDP.matrixOpNorm_nonneg _)))

/-- Strong measurability of the factorized covariance error.

**Lean implementation helper.** -/
theorem factorized_covariance_error_aestronglyMeasurable
    {m n r : ℕ} (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ) :
    AEStronglyMeasurable (fun ω => HDP.matrixOpNorm
      (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)) μ := by
  let G : Ω → Matrix (Fin r) (Fin r) ℝ :=
    fun ω => HDP.normalizedGram m (A ω) - 1
  have hGentry : ∀ j k, AEStronglyMeasurable (fun ω => G ω j k) μ := by
    intro j k
    dsimp [G]
    simp only [HDP.normalizedGram, HDP.gramMatrix, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.transpose_apply,
      smul_eq_mul, Matrix.one_apply]
    have hsum : AEMeasurable
        (fun ω => ∑ i : Fin m, A ω i j * A ω i k) μ :=
      by
        have hsum' : AEMeasurable
            (∑ i : Fin m, fun ω => A ω i j * A ω i k) μ :=
          Finset.aemeasurable_sum Finset.univ fun i _ =>
            (hrowsm.aemeasurable_entry i j).mul
              (hrowsm.aemeasurable_entry i k)
        exact hsum'.congr (Filter.Eventually.of_forall fun ω => by simp)
    exact ((hsum.const_mul ((m : ℝ)⁻¹)).sub
      aemeasurable_const).aestronglyMeasurable
  have hGsum : AEStronglyMeasurable (fun ω =>
      ∑ j : Fin r, ∑ k : Fin r,
        (G ω j k) • (Matrix.single j k 1 : Matrix (Fin r) (Fin r) ℝ)) μ :=
    by
      have hsum' : AEStronglyMeasurable
          (∑ j : Fin r, ∑ k : Fin r, fun ω =>
            (G ω j k) • (Matrix.single j k 1 : Matrix (Fin r) (Fin r) ℝ)) μ :=
        Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
          Finset.aestronglyMeasurable_sum Finset.univ fun k _ =>
            (hGentry j k).smul_const
              (Matrix.single j k 1 : Matrix (Fin r) (Fin r) ℝ)
      exact hsum'.congr (Filter.Eventually.of_forall fun ω => by simp)
  have hdecomp : (fun ω =>
      ∑ j : Fin r, ∑ k : Fin r,
        (G ω j k) • (Matrix.single j k 1 : Matrix (Fin r) (Fin r) ℝ)) = G := by
    funext ω
    calc
      _ = Matrix.of (G ω) := by simpa using Matrix.sum_sum_single (G ω)
      _ = G ω := by ext j k; rfl
  have hG : AEStronglyMeasurable G μ := by
    rwa [hdecomp] at hGsum
  have hprod : AEStronglyMeasurable (fun ω => B * G ω * B.transpose) μ := by
    exact (by fun_prop : Continuous
      (fun M : Matrix (Fin r) (Fin r) ℝ => B * M * B.transpose)).comp_aestronglyMeasurable hG
  change AEStronglyMeasurable (fun ω => ‖HDP.normalizedGram m
    (A ω * B.transpose) - B * B.transpose‖) μ
  convert hprod.norm using 1
  funext ω
  simpa [G] using congrArg norm (factorized_sampleCovariance_sub (A ω) B)

/-- Integrability of the factorized covariance error, obtained by domination by the normalized
Gram deviation.

**Lean implementation helper.** -/
theorem factorized_covariance_error_integrable [IsProbabilityMeasure μ]
    {m n r : ℕ} (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ) :
    Integrable (fun ω => HDP.matrixOpNorm
      (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)) μ := by
  let g : Ω → ℝ := fun ω => HDP.matrixOpNorm
    (HDP.normalizedGram m (A ω) - 1)
  let s : ℝ := HDP.matrixOpNorm (B * B.transpose)
  have hg : Integrable g μ := by
    simpa [g] using normalizedGramDeviation_integrable A hrowsm hsub
  have hgs : Integrable (fun ω => g ω * s) μ := hg.mul_const s
  apply hgs.mono_nonneg
  · exact factorized_covariance_error_aestronglyMeasurable A B hrowsm
  · exact Filter.Eventually.of_forall fun _ => HDP.matrixOpNorm_nonneg _
  · exact Filter.Eventually.of_forall fun ω => by
      simpa [g, s] using factorized_sampleCovariance_error_le (A ω) B

/-- The population second-moment matrix is `B Bᵀ`, and the observations are the rows of `A Bᵀ`.
The rectangular factor permits every singular rank, including rank zero.

**Book Theorem 4.7.1.** -/
theorem theorem_4_7_1_factorized [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m]
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    ∫ ω, HDP.matrixOpNorm
        (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose) ∂μ ≤
      gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
          HDP.matrixOpNorm (B * B.transpose) := by
  by_cases hr : r = 0
  · subst r
    simp [HDP.normalizedGram, HDP.gramMatrix]
  · letI : NeZero r := ⟨hr⟩
    let f : Ω → ℝ := fun ω => HDP.matrixOpNorm
      (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)
    let g : Ω → ℝ := fun ω => HDP.matrixOpNorm
      (HDP.normalizedGram m (A ω) - 1)
    let s : ℝ := HDP.matrixOpNorm (B * B.transpose)
    have hf : Integrable f μ := by
      simpa [f] using factorized_covariance_error_integrable A B hrowsm hsub
    have hg : Integrable g μ := by
      simpa [g] using normalizedGramDeviation_integrable A hrowsm hsub
    have hgs : Integrable (fun ω => g ω * s) μ := hg.mul_const s
    have htransfer : (∫ ω, f ω ∂μ) ≤ (∫ ω, g ω ∂μ) * s := by
      calc
        (∫ ω, f ω ∂μ) ≤ ∫ ω, g ω * s ∂μ :=
          integral_mono hf hgs fun ω => by
            simpa [f, g, s] using factorized_sampleCovariance_error_le (A ω) B
        _ = (∫ ω, g ω ∂μ) * s := integral_mul_const s g
    have hgram := theorem_4_6_1_gram_expectation
      A hrowsm hsub hiso hindep hfinite hK hpsi
    calc
      (∫ ω, HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose) ∂μ)
          = ∫ ω, f ω ∂μ := rfl
      _ ≤ (∫ ω, g ω ∂μ) * s := htransfer
      _ ≤ (gramExpectationConstant * K ^ 2 *
          (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m)) * s :=
        mul_le_mul_of_nonneg_right hgram (HDP.matrixOpNorm_nonneg _)
      _ = gramExpectationConstant * K ^ 2 *
          (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
            HDP.matrixOpNorm (B * B.transpose) := by
        dsimp [s]

/-- Ambient-dimension form of the corresponding theorem. This is the source display: the latent
support rank can only improve the bound.

**Book Theorem 4.7.1.** -/
theorem theorem_4_7_1 [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m] (hrn : r ≤ n)
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    ∫ ω, HDP.matrixOpNorm
        (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose) ∂μ ≤
      gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m) *
          HDP.matrixOpNorm (B * B.transpose) := by
  have hmain := theorem_4_7_1_factorized
    A B hrowsm hsub hiso hindep hfinite hK hpsi
  have hmR : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hdiv : (r : ℝ) / m ≤ (n : ℝ) / m := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hrn) hmR.le
  have hsqrt : Real.sqrt ((r : ℝ) / m) ≤ Real.sqrt ((n : ℝ) / m) :=
    Real.sqrt_le_sqrt hdiv
  have hfactor :
      Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m ≤
        Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m := add_le_add hsqrt hdiv
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg gramExpectationConstant_pos.le (sq_nonneg K)))
    (HDP.matrixOpNorm_nonneg _))

/-- Explicit sample-complexity constant in the corresponding remark.

**Lean implementation helper.** -/
def covarianceSampleComplexityConstant : ℝ :=
  4 * gramExpectationConstant ^ 2

/-- Shows that covariance sample complexity constant is positive.

**Lean implementation helper.** -/
lemma covarianceSampleComplexityConstant_pos :
    0 < covarianceSampleComplexityConstant := by
  dsimp [covarianceSampleComplexityConstant]
  positivity [gramExpectationConstant_pos]

/-- The scalar estimate behind the `K⁴ n / ε²` sample complexity.

**Lean implementation helper.** -/
lemma covariance_sampleComplexity_numerics {m n : ℕ} (hm : 0 < m)
    {K ε : ℝ} (hK : 1 ≤ K) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : covarianceSampleComplexityConstant * K ^ 4 * (n : ℝ) ≤
      ε ^ 2 * (m : ℝ)) :
    gramExpectationConstant * K ^ 2 *
      (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m) ≤ ε := by
  let q : ℝ := (n : ℝ) / m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hroot : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hrootSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hscaled : 4 * gramExpectationConstant ^ 2 * K ^ 4 * q ≤ ε ^ 2 := by
    calc
      4 * gramExpectationConstant ^ 2 * K ^ 4 * q =
          (covarianceSampleComplexityConstant * K ^ 4 * (n : ℝ)) /
            (m : ℝ) := by
        dsimp [q, covarianceSampleComplexityConstant]
        ring
      _ ≤ (ε ^ 2 * (m : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hsize hmR.le
      _ = ε ^ 2 := by field_simp [hmR.ne']
  have hrootBound : 2 * gramExpectationConstant * K ^ 2 *
      Real.sqrt q ≤ ε := by
    apply (sq_le_sq₀
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) gramExpectationConstant_pos.le)
          (sq_nonneg K)) hroot) hε0.le).mp
    calc
      (2 * gramExpectationConstant * K ^ 2 * Real.sqrt q) ^ 2 =
          4 * gramExpectationConstant ^ 2 * K ^ 4 *
            (Real.sqrt q) ^ 2 := by
        ring
      _ = 4 * gramExpectationConstant ^ 2 * K ^ 4 * q := by
        rw [hrootSq]
      _ ≤ ε ^ 2 := hscaled
  have hKpow : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hD : 1 ≤ covarianceSampleComplexityConstant := by
    norm_num [covarianceSampleComplexityConstant, gramExpectationConstant]
  have hnle : n ≤ m := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hleft : (n : ℝ) ≤
        covarianceSampleComplexityConstant * K ^ 4 * (n : ℝ) := by
      calc
        (n : ℝ) = 1 * (n : ℝ) := by ring
        _ ≤ (covarianceSampleComplexityConstant * K ^ 4) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hD hKpow) hn0
    have hepsSq : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
    have hright : ε ^ 2 * (m : ℝ) ≤ (m : ℝ) := by
      nlinarith
    exact_mod_cast hleft.trans (hsize.trans hright)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (div_le_one hmR).2 (by exact_mod_cast hnle)
  have hqroot : q ≤ Real.sqrt q := by
    have hqsq : q ^ 2 ≤ q := by
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1)]
    have hqsq' : q ^ 2 ≤ (Real.sqrt q) ^ 2 := by
      rwa [hrootSq]
    exact (sq_le_sq₀ hq hroot).mp hqsq'
  calc
    gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((n : ℝ) / m) + (n : ℝ) / m) =
        gramExpectationConstant * K ^ 2 * (Real.sqrt q + q) := rfl
    _ ≤ gramExpectationConstant * K ^ 2 *
        (Real.sqrt q + Real.sqrt q) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hqroot)
        (mul_nonneg gramExpectationConstant_pos.le (sq_nonneg K))
    _ = 2 * gramExpectationConstant * K ^ 2 * Real.sqrt q := by ring
    _ ≤ ε := hrootBound

/-- The expectation is at most `ε ‖Σ‖` once `m` is an explicit constant multiple of `K⁴ n / ε²`.

**Book Remark 4.7.2.** -/
theorem remark_4_7_2 [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m] (hrn : r ≤ n)
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K ε : ℝ} (hK : 1 ≤ K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : covarianceSampleComplexityConstant * K ^ 4 * (n : ℝ) ≤
      ε ^ 2 * (m : ℝ)) :
    ∫ ω, HDP.matrixOpNorm
        (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose) ∂μ ≤
      ε * HDP.matrixOpNorm (B * B.transpose) := by
  have hmain := theorem_4_7_1 hrn A B hrowsm hsub hiso hindep hfinite
    (lt_of_lt_of_le zero_lt_one hK) hpsi
  have hscalar := covariance_sampleComplexity_numerics
    (NeZero.pos m) hK hε0 hε1 hsize
  exact hmain.trans (mul_le_mul_of_nonneg_right hscalar
    (HDP.matrixOpNorm_nonneg _))

/-- The exact high-probability transfer before simplifying the deviation parameter.

**Book Exercise 4.49.** -/
theorem exercise_4_49_factorized [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m]
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    {t : ℝ} (ht : 0 ≤ t) :
    let δ := twoSidedGramConstant *
      (Real.sqrt ((r : ℝ) / m) + t / Real.sqrt m)
    μ {ω | K ^ 2 * max δ (δ ^ 2) *
          HDP.matrixOpNorm (B * B.transpose) <
        HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  dsimp only
  by_cases hr : r = 0
  · subst r
    simp [HDP.normalizedGram, HDP.gramMatrix]
  · letI : NeZero r := ⟨hr⟩
    exact (factorized_covariance_tail_of_gram_tail A B
      (K ^ 2 * max
        (twoSidedGramConstant *
          (Real.sqrt ((r : ℝ) / m) + t / Real.sqrt m))
        ((twoSidedGramConstant *
          (Real.sqrt ((r : ℝ) / m) + t / Real.sqrt m)) ^ 2))).trans
      (theorem_4_6_1_gram A hrowsm hsub hiso hindep hfinite hK hpsi ht)

/-- Explicit absolute constant in the corresponding remark.

**Lean implementation helper.** -/
def covarianceTailConstant : ℝ := 40200

/-- Shows that covariance tail constant is positive.

**Lean implementation helper.** -/
lemma covarianceTailConstant_pos : 0 < covarianceTailConstant := by
  norm_num [covarianceTailConstant]

/-- Numerical simplification from the Gram parameter to the source's `sqrt ((r+u)/m) + (r+u)/m`
expression.

**Lean implementation helper.** -/
lemma covariance_tail_numerics {m r : ℕ} (hm : 0 < m)
    {u : ℝ} (hu : 0 ≤ u) :
    let δ := twoSidedGramConstant *
      (Real.sqrt ((r : ℝ) / m) + Real.sqrt u / Real.sqrt m)
    max δ (δ ^ 2) ≤ covarianceTailConstant *
      (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) := by
  dsimp only
  let a : ℝ := Real.sqrt (((r : ℝ) + u) / m)
  let x : ℝ := Real.sqrt ((r : ℝ) / m)
  let y : ℝ := Real.sqrt u / Real.sqrt m
  let δ : ℝ := twoSidedGramConstant * (x + y)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfracx : (r : ℝ) / m ≤ ((r : ℝ) + u) / m := by
    exact div_le_div_of_nonneg_right (by linarith) hmR.le
  have hfracy : u / (m : ℝ) ≤ ((r : ℝ) + u) / m := by
    exact div_le_div_of_nonneg_right
      (by
        have hr0 : (0 : ℝ) ≤ r := by positivity
        linarith) hmR.le
  have hxa : x ≤ a := by
    dsimp [x, a]
    exact Real.sqrt_le_sqrt hfracx
  have hya : y ≤ a := by
    dsimp [y, a]
    rw [← Real.sqrt_div hu]
    exact Real.sqrt_le_sqrt hfracy
  have hδ : 0 ≤ δ := by
    exact mul_nonneg twoSidedGramConstant_pos.le (add_nonneg hx hy)
  have hδa : δ ≤ 200 * a := by
    dsimp [δ, twoSidedGramConstant]
    nlinarith
  have hmax1 : δ ≤ covarianceTailConstant * (a + a ^ 2) := by
    dsimp [covarianceTailConstant]
    nlinarith [sq_nonneg a]
  have hmax2 : δ ^ 2 ≤ covarianceTailConstant * (a + a ^ 2) := by
    have hsquare : δ ^ 2 ≤ (200 * a) ^ 2 :=
      (sq_le_sq₀ hδ (mul_nonneg (by norm_num) ha)).2 hδa
    dsimp [covarianceTailConstant]
    nlinarith
  have ha2 : a ^ 2 = ((r : ℝ) + u) / m := by
    dsimp [a]
    exact Real.sq_sqrt (div_nonneg (by positivity) hmR.le)
  change max δ (δ ^ 2) ≤ covarianceTailConstant *
    (a + ((r : ℝ) + u) / m)
  rw [← ha2]
  exact max_le hmax1 hmax2

/-- High-probability covariance estimation with the source normalization.

**Book Remark 4.7.3.** -/
theorem exercise_4_49 [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m]
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | covarianceTailConstant * K ^ 2 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) <
        HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)} ≤
      ENNReal.ofReal (2 * Real.exp (-u)) := by
  let δ := twoSidedGramConstant *
    (Real.sqrt ((r : ℝ) / m) + Real.sqrt u / Real.sqrt m)
  have hnum := covariance_tail_numerics (r := r) (NeZero.pos m) hu
  have hnum' : max δ (δ ^ 2) ≤ covarianceTailConstant *
      (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) := by
    exact hnum
  have hthreshold : K ^ 2 * max δ (δ ^ 2) *
      HDP.matrixOpNorm (B * B.transpose) ≤
      covarianceTailConstant * K ^ 2 *
        (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
          HDP.matrixOpNorm (B * B.transpose) := by
    have hscaled : K ^ 2 * max δ (δ ^ 2) ≤
        covarianceTailConstant * K ^ 2 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hnum' (sq_nonneg K))
    exact mul_le_mul_of_nonneg_right
      hscaled
      (HDP.matrixOpNorm_nonneg _)
  calc
    μ {ω | covarianceTailConstant * K ^ 2 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) <
        HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)}
        ≤ μ {ω | K ^ 2 * max δ (δ ^ 2) *
          HDP.matrixOpNorm (B * B.transpose) <
        HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)} := by
      apply measure_mono
      intro ω hω
      exact lt_of_le_of_lt hthreshold hω
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(Real.sqrt u) ^ 2)) := by
      simpa [δ] using exercise_4_49_factorized
        A B hrowsm hsub hiso hindep hfinite hK hpsi (Real.sqrt_nonneg u)
    _ = ENNReal.ofReal (2 * Real.exp (-u)) := by
      rw [Real.sq_sqrt hu]

/-- Source-facing alias for the high-probability remark. -/
alias remark_4_7_3 := exercise_4_49

end HDP.Chapter4

end Source_18_CovarianceEstimation

/-! ## Material formerly in `19_GaussianMixtureClustering.lean` -/

section Source_19_GaussianMixtureClustering

/-!
# Chapter 4, §4.7.4--4.7.5: Gaussian-mixture clustering

We use the canonical labelled model
`X = theta * mu + g`, where `theta` is Rademacher and `g` is an independent
standard Gaussian vector.  A finite sample is the product of copies of this
labelled model.  The empirical matrix below is the uncentered second moment,
as in the source.

The last probability statement is deliberately phrased as a bound by a
measurable exceptional event.  Mathlib's ordered eigenbasis is deterministic,
but its dependence on the operator is not currently supplied with a
measurability theorem.  This formulation proves the source's operational
`0.99` guarantee without assuming a nonexistent measurable spectral selector.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Chapter4

noncomputable section

abbrev GMMEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The symmetric two-point law on `{1,-1}`.

**Lean implementation helper.** -/
def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- One labelled observation before applying the mixture map. -/
abbrev GaussianMixtureAtom (n : ℕ) := ℝ × GMMEuclidean n

/-- The canonical independent Rademacher/Gaussian atom.

**Lean implementation helper.** -/
def gaussianMixtureAtomMeasure (n : ℕ) : Measure (GaussianMixtureAtom n) :=
  rademacherMeasure.prod (stdGaussian (GMMEuclidean n))

instance (n : ℕ) : IsProbabilityMeasure (gaussianMixtureAtomMeasure n) := by
  unfold gaussianMixtureAtomMeasure
  infer_instance

/-- A labelled sample of size `m`. -/
abbrev GaussianMixtureSample (m n : ℕ) := Fin m → GaussianMixtureAtom n

/-- The canonical law of `m` independent labelled mixture observations.

**Book Definition 4.7.4.** -/
def gaussianMixtureSampleMeasure (m n : ℕ) :
    Measure (GaussianMixtureSample m n) :=
  Measure.pi (fun _ : Fin m => gaussianMixtureAtomMeasure n)

instance (m n : ℕ) : IsProbabilityMeasure (gaussianMixtureSampleMeasure m n) := by
  unfold gaussianMixtureSampleMeasure
  infer_instance

/-- The hidden Rademacher label of observation `i`.

**Lean implementation helper.** -/
def gaussianMixtureLabel {m n : ℕ} (w : GaussianMixtureSample m n)
    (i : Fin m) : ℝ :=
  (w i).1

/-- The standard Gaussian noise of observation `i`.

**Lean implementation helper.** -/
def gaussianMixtureNoise {m n : ℕ} (w : GaussianMixtureSample m n)
    (i : Fin m) : GMMEuclidean n :=
  (w i).2

/-- The observed point `theta_i mu + g_i`.

**Book Definition 4.7.4.** -/
def gaussianMixturePoint {m n : ℕ} (mu : GMMEuclidean n)
    (w : GaussianMixtureSample m n) (i : Fin m) : GMMEuclidean n :=
  gaussianMixtureLabel w i • mu + gaussianMixtureNoise w i

/-- The unlabelled one-point mixture law.

**Book Definition 4.7.4.** -/
def gaussianMixtureMeasure {n : ℕ} (mu : GMMEuclidean n) :
    Measure (GMMEuclidean n) :=
  (gaussianMixtureAtomMeasure n).map (fun z => z.1 • mu + z.2)

/-- Establishes measurability of gaussian mixture point map.

**Lean implementation helper.** -/
lemma measurable_gaussianMixturePointMap {n : ℕ} (mu : GMMEuclidean n) :
    Measurable (fun z : GaussianMixtureAtom n => z.1 • mu + z.2) := by
  fun_prop

/-- Identifies the probability law described by has law gaussian mixture point.

**Lean implementation helper.** -/
lemma hasLaw_gaussianMixturePoint {m n : ℕ} (mu : GMMEuclidean n)
    (i : Fin m) :
    HasLaw (fun w : GaussianMixtureSample m n => gaussianMixturePoint mu w i)
      (gaussianMixtureMeasure mu) (gaussianMixtureSampleMeasure m n) := by
  let eval : GaussianMixtureSample m n → GaussianMixtureAtom n := fun w => w i
  have heval : HasLaw eval (gaussianMixtureAtomMeasure n)
      (gaussianMixtureSampleMeasure m n) := by
    exact (measurePreserving_eval
      (fun _ : Fin m => gaussianMixtureAtomMeasure n) i).hasLaw
  have hatom : HasLaw
      (fun z : GaussianMixtureAtom n => z.1 • mu + z.2)
      (gaussianMixtureMeasure mu) (gaussianMixtureAtomMeasure n) := by
    refine ⟨(measurable_gaussianMixturePointMap mu).aemeasurable, ?_⟩
    rfl
  simpa [eval, gaussianMixturePoint, gaussianMixtureLabel,
    gaussianMixtureNoise, Function.comp_def] using hatom.comp heval

/-- The atom coordinates of the product Gaussian-mixture sample are independent.

**Lean implementation helper.** -/
lemma iIndepFun_gaussianMixtureAtoms (m n : ℕ) :
    iIndepFun (fun i (w : GaussianMixtureSample m n) => w i)
      (gaussianMixtureSampleMeasure m n) := by
  unfold gaussianMixtureSampleMeasure
  simpa only [id_eq] using
    (iIndepFun_pi (X := fun _ : Fin m => id) (fun _ => aemeasurable_id))

/-- Applying the Gaussian-mixture point map coordinatewise preserves independence of the sampled points.

**Lean implementation helper.** -/
lemma iIndepFun_gaussianMixturePoints {m n : ℕ} (mu : GMMEuclidean n) :
    iIndepFun (fun i (w : GaussianMixtureSample m n) =>
      gaussianMixturePoint mu w i) (gaussianMixtureSampleMeasure m n) := by
  have h := (iIndepFun_gaussianMixtureAtoms m n).comp
    (fun _ : Fin m => fun z : GaussianMixtureAtom n => z.1 • mu + z.2)
    (fun _ => measurable_gaussianMixturePointMap mu)
  simpa [Function.comp_def, gaussianMixturePoint, gaussianMixtureLabel,
    gaussianMixtureNoise] using h

/-- On the atom space the first coordinate is a Rademacher variable.

**Lean implementation helper.** -/
lemma isRademacher_fst_gaussianMixtureAtom (n : ℕ) :
    HDP.IsRademacher (fun z : GaussianMixtureAtom n => z.1)
      (gaussianMixtureAtomMeasure n) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [gaussianMixtureAtomMeasure, measurePreserving_fst.map_eq]
  rfl

/-- The label of each sampled point is Rademacher.

**Lean implementation helper.** -/
lemma isRademacher_gaussianMixtureLabel {m n : ℕ} (i : Fin m) :
    HDP.IsRademacher (fun w : GaussianMixtureSample m n =>
      gaussianMixtureLabel w i) (gaussianMixtureSampleMeasure m n) := by
  let eval : GaussianMixtureSample m n → GaussianMixtureAtom n := fun w => w i
  have heval := (measurePreserving_eval
    (fun _ : Fin m => gaussianMixtureAtomMeasure n) i)
  have hatom : HasLaw (fun z : GaussianMixtureAtom n => z.1)
      rademacherMeasure (gaussianMixtureAtomMeasure n) := by
    exact ⟨(isRademacher_fst_gaussianMixtureAtom n).aemeasurable,
      (isRademacher_fst_gaussianMixtureAtom n).map_eq⟩
  have hlabel := hatom.comp heval.hasLaw
  have hlabel' : HasLaw
      (fun w : Fin m → GaussianMixtureAtom n => (w i).1)
      rademacherMeasure
      (Measure.pi (fun _ : Fin m => gaussianMixtureAtomMeasure n)) := by
    simpa [Function.comp_def, eval] using hlabel
  constructor
  · change AEMeasurable
      (fun w : Fin m → GaussianMixtureAtom n => (w i).1)
      (Measure.pi (fun _ : Fin m => gaussianMixtureAtomMeasure n))
    exact hlabel'.aemeasurable
  · change Measure.map
      (fun w : Fin m → GaussianMixtureAtom n => (w i).1)
      (Measure.pi (fun _ : Fin m => gaussianMixtureAtomMeasure n)) =
        bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩
    simpa only [rademacherMeasure] using hlabel'.map_eq

/-! ### An isotropic augmented-row factorization

The mixture row `theta * mu + g` is the deterministic image of the augmented
row `(theta,g)`.  This factorization is the point at which the proof avoids a
singular-whitening assumption: the augmented row is isotropic even when the
population second moment `I + mu mu^T` is singular as a covariance model. -/

/-- The augmented isotropic row `(theta,g)` in `R^(n+1)`.

**Lean implementation helper.** -/
def gaussianMixtureAugmentedVector {n : ℕ} (z : GaussianMixtureAtom n) :
    GMMEuclidean (n + 1) :=
  WithLp.toLp 2 (Fin.cases z.1 (fun j => z.2 j))

/-- Establishes measurability of gaussian mixture augmented vector.

**Lean implementation helper.** -/
lemma measurable_gaussianMixtureAugmentedVector {n : ℕ} :
    Measurable (gaussianMixtureAugmentedVector :
      GaussianMixtureAtom n → GMMEuclidean (n + 1)) := by
  apply (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [Fin.cases_zero] using
      (measurable_fst : Measurable (fun z : GaussianMixtureAtom n => z.1))
  · simpa only [Fin.cases_succ] using
      (by fun_prop : Measurable (fun z : GaussianMixtureAtom n => z.2 k))

/-- The first coordinate of an augmented Gaussian-mixture vector is its scalar label.

**Lean implementation helper.** -/
@[simp] lemma gaussianMixtureAugmentedVector_zero {n : ℕ}
    (z : GaussianMixtureAtom n) :
    gaussianMixtureAugmentedVector z 0 = z.1 := rfl

/-- The remaining coordinates of an augmented Gaussian-mixture vector are its Gaussian coordinates.

**Lean implementation helper.** -/
@[simp] lemma gaussianMixtureAugmentedVector_succ {n : ℕ}
    (z : GaussianMixtureAtom n) (j : Fin n) :
    gaussianMixtureAugmentedVector z j.succ = z.2 j := rfl

/-- The random matrix whose rows are the augmented observations.

**Lean implementation helper.** -/
def gaussianMixtureAugmentedMatrix {m n : ℕ} (w : GaussianMixtureSample m n) :
    Matrix (Fin m) (Fin (n + 1)) ℝ :=
  fun i j => gaussianMixtureAugmentedVector (w i) j

/-- Each row of the augmented Gaussian-mixture data matrix is the corresponding augmented sample vector.

**Lean implementation helper.** -/
@[simp] lemma randomMatrixRow_gaussianMixtureAugmentedMatrix {m n : ℕ}
    (w : GaussianMixtureSample m n) (i : Fin m) :
    HDP.randomMatrixRow
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w) i w =
      gaussianMixtureAugmentedVector (w i) := rfl

/-- The deterministic map `(theta,g) |-> theta * mu + g`.

**Lean implementation helper.** -/
def gaussianMixtureFactorMatrix {n : ℕ} (mu : GMMEuclidean n) :
    Matrix (Fin n) (Fin (n + 1)) ℝ :=
  fun i => Fin.cases (mu i) (fun j => if i = j then 1 else 0)

/-- The first column of the Gaussian-mixture factor matrix is the mean vector.

**Lean implementation helper.** -/
@[simp] lemma gaussianMixtureFactorMatrix_zero {n : ℕ}
    (mu : GMMEuclidean n) (i : Fin n) :
    gaussianMixtureFactorMatrix mu i 0 = mu i := rfl

/-- The remaining columns of the Gaussian-mixture factor matrix form the identity matrix.

**Lean implementation helper.** -/
@[simp] lemma gaussianMixtureFactorMatrix_succ {n : ℕ}
    (mu : GMMEuclidean n) (i j : Fin n) :
    gaussianMixtureFactorMatrix mu i j.succ = if i = j then 1 else 0 := rfl

/-- Exact sample factorization used by the covariance tail theorem.

**Lean implementation helper.** -/
lemma dataMatrix_gaussianMixturePoint_factorization {m n : ℕ}
    (mu : GMMEuclidean n) (w : GaussianMixtureSample m n) :
    dataMatrix (fun i => gaussianMixturePoint mu w i) =
      gaussianMixtureAugmentedMatrix w *
        (gaussianMixtureFactorMatrix mu).transpose := by
  ext i j
  simp [dataMatrix, gaussianMixturePoint, gaussianMixtureLabel,
    gaussianMixtureNoise, gaussianMixtureAugmentedMatrix,
    gaussianMixtureFactorMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The deterministic factor has Gram matrix `I + mu mu^T`.

**Lean implementation helper.** -/
lemma gaussianMixtureFactorMatrix_mul_transpose {n : ℕ}
    (mu : GMMEuclidean n) :
    gaussianMixtureFactorMatrix mu *
        (gaussianMixtureFactorMatrix mu).transpose =
      1 + outerProductMatrix mu := by
  ext i j
  simp [gaussianMixtureFactorMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply, outerProductMatrix, mul_comm]
  all_goals ring

/-- Identifies psi2 mgf with of same law.

**Lean implementation helper.** -/
private lemma psi2MGF_eq_of_sameLaw
    {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {ν : Measure ℝ}
    {X : Ω₁ → ℝ} {Y : Ω₂ → ℝ}
    (hX : HasLaw X ν P₁) (hY : HasLaw Y ν P₂) (K : ℝ) :
    HDP.psi2MGF X P₁ K = HDP.psi2MGF Y P₂ K := by
  rw [HDP.psi2MGF_eq_of_hasLaw hX, HDP.psi2MGF_eq_of_hasLaw hY]

/-- Derives sub gaussian from same law.

**Lean implementation helper.** -/
private lemma subGaussian_of_sameLaw
    {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {ν : Measure ℝ}
    {X : Ω₁ → ℝ} {Y : Ω₂ → ℝ}
    (hX : HasLaw X ν P₁) (hY : HasLaw Y ν P₂)
    (hYsub : HDP.SubGaussian Y P₂) :
    HDP.SubGaussian X P₁ := by
  rcases hYsub with ⟨K, hK, hKb⟩
  exact ⟨K, hK, (psi2MGF_eq_of_sameLaw hX hY K).trans_le hKb⟩

/-- Identifies psi2 norm with of same law.

**Lean implementation helper.** -/
private lemma psi2Norm_eq_of_sameLaw
    {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {ν : Measure ℝ}
    {X : Ω₁ → ℝ} {Y : Ω₂ → ℝ}
    (hX : HasLaw X ν P₁) (hY : HasLaw Y ν P₂) :
    HDP.psi2Norm X P₁ = HDP.psi2Norm Y P₂ := by
  rw [HDP.psi2Norm_eq_of_hasLaw hX, HDP.psi2Norm_eq_of_hasLaw hY]

/-- Delete the label coordinate from an augmented direction.

**Lean implementation helper.** -/
def gaussianMixtureAugmentedTail {n : ℕ} (u : GMMEuclidean (n + 1)) :
    GMMEuclidean n :=
  WithLp.toLp 2 (fun j => u j.succ)

/-- Coordinate `j` of the augmented Gaussian-mixture tail is the successor coordinate `u j.succ`.

**Lean implementation helper.** -/
@[simp] lemma gaussianMixtureAugmentedTail_apply {n : ℕ}
    (u : GMMEuclidean (n + 1)) (j : Fin n) :
    gaussianMixtureAugmentedTail u j = u j.succ := rfl

/-- The inner product with an augmented mixture vector splits into the label coordinate plus the Gaussian-tail inner product.

**Lean implementation helper.** -/
lemma inner_gaussianMixtureAugmentedVector {n : ℕ}
    (z : GaussianMixtureAtom n) (u : GMMEuclidean (n + 1)) :
    inner ℝ (gaussianMixtureAugmentedVector z) u =
      u 0 * z.1 + inner ℝ z.2 (gaussianMixtureAugmentedTail u) := by
  simp [gaussianMixtureAugmentedVector, gaussianMixtureAugmentedTail,
    PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]

/-- Deleting the leading coordinate cannot increase norm: `‖gaussianMixtureAugmentedTail u‖ ≤ ‖u‖`.

**Lean implementation helper.** -/
lemma norm_gaussianMixtureAugmentedTail_le {n : ℕ}
    (u : GMMEuclidean (n + 1)) :
    ‖gaussianMixtureAugmentedTail u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [gaussianMixtureAugmentedTail_apply, Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg (u 0))

/-- A standard real Gaussian random variable is subgaussian.

**Lean implementation helper.** -/
private lemma subGaussian_id_standardGaussianReal :
    HDP.SubGaussian (fun x : ℝ => x) (gaussianReal 0 1) := by
  letI : IsProbabilityMeasure HDP.Chapter3.projectiveProbability := by
    dsimp [HDP.Chapter3.projectiveProbability]
    infer_instance
  exact subGaussian_of_sameLaw (HasLaw.id (μ := gaussianReal 0 1))
    (HDP.Chapter3.hasLaw_projectiveGaussianCoordinate 0)
    (HDP.Chapter3.projectiveGaussianCoordinate_subGaussian 0)

/-- Derives sub gaussian from centered gaussian law.

**Lean implementation helper.** -/
private lemma subGaussian_of_centeredGaussianLaw
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (sigma : ℝ)
    (hX : HasLaw X
      (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) P) :
    HDP.SubGaussian X P := by
  let ν : Measure ℝ := gaussianReal 0 1
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hid : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) ν := by
    exact HasLaw.id
  have hscaled : HasLaw (fun x : ℝ => sigma * x)
      (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) ν := by
    have h := ProbabilityTheory.gaussianReal_const_mul hid sigma
    convert h using 1
    rw [mul_zero, mul_one]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    rfl
  exact subGaussian_of_sameLaw hX hscaled
    (subGaussian_id_standardGaussianReal.const_mul sigma)

/-- Identifies the probability law described by has law gaussian mixture atom noise inner.

**Lean implementation helper.** -/
private lemma hasLaw_gaussianMixtureAtom_noise_inner {n : ℕ}
    (u : GMMEuclidean n) :
    HasLaw (fun z : GaussianMixtureAtom n => inner ℝ z.2 u)
      (gaussianReal 0 ⟨‖u‖ ^ 2, sq_nonneg ‖u‖⟩)
      (gaussianMixtureAtomMeasure n) := by
  have hsnd : HasLaw (fun z : GaussianMixtureAtom n => z.2)
      (stdGaussian (GMMEuclidean n)) (gaussianMixtureAtomMeasure n) := by
    simpa [gaussianMixtureAtomMeasure] using
      (measurePreserving_snd (μ := rademacherMeasure)
        (ν := stdGaussian (GMMEuclidean n))).hasLaw
  have h := (HDP.Chapter3.standardGaussian_inner_hasLaw u).comp hsnd
  convert h using 1
  · funext z
    simp [real_inner_comm]
  · apply congrArg (gaussianReal 0)
    apply NNReal.eq
    change ‖u‖ ^ 2 =
      ((‖u‖ ^ 2).toNNReal : ℝ)
    rw [Real.coe_toNNReal']
    exact (max_eq_left (sq_nonneg ‖u‖)).symm

/-- Every unit-direction marginal of an augmented Gaussian-mixture atom is subgaussian.

**Lean implementation helper.** -/
private lemma gaussianMixtureAugmentedAtom_marginal_subGaussian {n : ℕ}
    (u : GMMEuclidean (n + 1)) :
    HDP.SubGaussian
      (fun z : GaussianMixtureAtom n =>
        inner ℝ (gaussianMixtureAugmentedVector z) u)
      (gaussianMixtureAtomMeasure n) := by
  let tail := gaussianMixtureAugmentedTail u
  have hlabel : HDP.SubGaussian
      (fun z : GaussianMixtureAtom n => u 0 * z.1)
      (gaussianMixtureAtomMeasure n) := by
    have hb := (HDP.psi2Norm_le_of_bounded (μ := gaussianMixtureAtomMeasure n)
      (X := fun z : GaussianMixtureAtom n => z.1) (M := 1)
      one_pos (by
        filter_upwards [(isRademacher_fst_gaussianMixtureAtom n).ae_mem]
          with z hz
        rcases hz with hz | hz <;> simp [hz])).1
    exact hb.const_mul (u 0)
  have hnoise : HDP.SubGaussian
      (fun z : GaussianMixtureAtom n => inner ℝ z.2 tail)
      (gaussianMixtureAtomMeasure n) :=
    subGaussian_of_centeredGaussianLaw ‖tail‖
      (hasLaw_gaussianMixtureAtom_noise_inner tail)
  have hadd := HDP.SubGaussian.add
    (μ := gaussianMixtureAtomMeasure n)
    (by fun_prop : AEMeasurable
      (fun z : GaussianMixtureAtom n => u 0 * z.1) _)
    (by fun_prop : AEMeasurable
      (fun z : GaussianMixtureAtom n => inner ℝ z.2 tail) _)
    hlabel hnoise
  simpa [inner_gaussianMixtureAugmentedVector, tail] using hadd

/-- Bounds gaussian mixture augmented atom marginal psi2 by four.

**Lean implementation helper.** -/
private lemma gaussianMixtureAugmentedAtom_marginal_psi2_le_four {n : ℕ}
    (u : GMMEuclidean (n + 1)) (hu : ‖u‖ = 1) :
    HDP.psi2Norm
      (fun z : GaussianMixtureAtom n =>
        inner ℝ (gaussianMixtureAugmentedVector z) u)
      (gaussianMixtureAtomMeasure n) ≤ 4 := by
  let tail := gaussianMixtureAugmentedTail u
  have hlabelSub : HDP.SubGaussian
      (fun z : GaussianMixtureAtom n => u 0 * z.1)
      (gaussianMixtureAtomMeasure n) := by
    have hb := (HDP.psi2Norm_le_of_bounded (μ := gaussianMixtureAtomMeasure n)
      (X := fun z : GaussianMixtureAtom n => z.1) (M := 1)
      one_pos (by
        filter_upwards [(isRademacher_fst_gaussianMixtureAtom n).ae_mem]
          with z hz
        rcases hz with hz | hz <;> simp [hz])).1
    exact hb.const_mul (u 0)
  have hnoiseLaw := hasLaw_gaussianMixtureAtom_noise_inner tail
  have hnoiseSub : HDP.SubGaussian
      (fun z : GaussianMixtureAtom n => inner ℝ z.2 tail)
      (gaussianMixtureAtomMeasure n) :=
    subGaussian_of_centeredGaussianLaw ‖tail‖ hnoiseLaw
  have htri := HDP.psi2Norm_add_le
    (μ := gaussianMixtureAtomMeasure n)
    (by fun_prop : AEMeasurable
      (fun z : GaussianMixtureAtom n => u 0 * z.1) _)
    (by fun_prop : AEMeasurable
      (fun z : GaussianMixtureAtom n => inner ℝ z.2 tail) _)
    hlabelSub hnoiseSub
  have hu0 : |u 0| ≤ 1 := by
    have hu0sq : (u 0) ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (u i))
        (Finset.mem_univ (0 : Fin (n + 1)))
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa [sq_abs, hu] using hu0sq
  have htail : ‖tail‖ ≤ 1 := by
    simpa [tail, hu] using norm_gaussianMixtureAugmentedTail_le u
  have hlog : (1 : ℝ) / Real.sqrt (Real.log 2) < 2 := by
    have hsqrt : (1 / 2 : ℝ) < Real.sqrt (Real.log 2) := by
      rw [lt_sqrt (by norm_num)]
      nlinarith [Real.log_two_gt_d9]
    rw [div_lt_iff₀ (Real.sqrt_pos.2 (Real.log_pos (by norm_num)))]
    nlinarith
  have hgauss : Real.sqrt (8 / 3 : ℝ) < 2 :=
    HDP.Chapter3.sqrt_eight_thirds_lt_two
  have hlabelNorm : HDP.psi2Norm
      (fun z : GaussianMixtureAtom n => u 0 * z.1)
      (gaussianMixtureAtomMeasure n) =
      |u 0| * (1 / Real.sqrt (Real.log 2)) := by
    rw [HDP.psi2Norm_const_mul,
      HDP.psi2Norm_rademacher (isRademacher_fst_gaussianMixtureAtom n)]
  have hnoiseNorm : HDP.psi2Norm
      (fun z : GaussianMixtureAtom n => inner ℝ z.2 tail)
      (gaussianMixtureAtomMeasure n) =
      ‖tail‖ * Real.sqrt (8 / 3) := by
    simpa [abs_of_nonneg (norm_nonneg tail)] using
      (HDP.psi2Norm_gaussian ‖tail‖ hnoiseLaw)
  have hfun : (fun z : GaussianMixtureAtom n =>
      inner ℝ (gaussianMixtureAugmentedVector z) u) =
      fun z => u 0 * z.1 + inner ℝ z.2 tail := by
    funext z
    simpa [tail] using inner_gaussianMixtureAugmentedVector z u
  rw [hfun]
  calc
    HDP.psi2Norm
        (fun z : GaussianMixtureAtom n =>
          u 0 * z.1 + inner ℝ z.2 tail)
        (gaussianMixtureAtomMeasure n)
        ≤ HDP.psi2Norm (fun z : GaussianMixtureAtom n => u 0 * z.1) _ +
            HDP.psi2Norm (fun z : GaussianMixtureAtom n => inner ℝ z.2 tail) _ :=
      htri
    _ = |u 0| * (1 / Real.sqrt (Real.log 2)) +
          ‖tail‖ * Real.sqrt (8 / 3) := by rw [hlabelNorm, hnoiseNorm]
    _ ≤ 1 * (1 / Real.sqrt (Real.log 2)) +
          1 * Real.sqrt (8 / 3) := by
      gcongr
    _ ≤ 4 := by linarith

/-- The augmented Gaussian-mixture atom is isotropic.

**Lean implementation helper.** -/
private lemma gaussianMixtureAugmentedAtom_isIsotropic (n : ℕ) :
    HDP.IsIsotropic gaussianMixtureAugmentedVector
      (gaussianMixtureAtomMeasure n) := by
  apply HDP.isIsotropic_iff.mpr
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · have h := (isRademacher_fst_gaussianMixtureAtom n).integral_comp
        (fun x : ℝ => x ^ 2)
      norm_num at h
      simpa [pow_two] using h
    · have hbase : (Prod.fst : GaussianMixtureAtom n → ℝ) ⟂ᵢ[
          gaussianMixtureAtomMeasure n]
          (Prod.snd : GaussianMixtureAtom n → GMMEuclidean n) := by
        simpa [gaussianMixtureAtomMeasure] using
          (indepFun_prod (X := id) (Y := id)
            (μ := rademacherMeasure) (ν := stdGaussian (GMMEuclidean n))
            measurable_id measurable_id)
      have hind : (fun z : GaussianMixtureAtom n => z.1) ⟂ᵢ[
          gaussianMixtureAtomMeasure n] (fun z => z.2 j) := by
        simpa [Function.comp_def] using
          hbase.comp measurable_id (by fun_prop : Measurable
            (fun g : GMMEuclidean n => g j))
      have hprod := hind.integral_fun_mul_eq_mul_integral
        (by fun_prop : AEStronglyMeasurable
          (fun z : GaussianMixtureAtom n => z.1) _)
        (by fun_prop : AEStronglyMeasurable
          (fun z : GaussianMixtureAtom n => z.2 j) _)
      rw [(isRademacher_fst_gaussianMixtureAtom n).integral_eq_zero,
        zero_mul] at hprod
      have hne : (0 : Fin (n + 1)) ≠ j.succ :=
        (Fin.succ_ne_zero j).symm
      rw [if_neg hne]
      exact hprod
  · refine Fin.cases ?_ (fun j => ?_) j
    · have hbase : (Prod.fst : GaussianMixtureAtom n → ℝ) ⟂ᵢ[
          gaussianMixtureAtomMeasure n]
          (Prod.snd : GaussianMixtureAtom n → GMMEuclidean n) := by
        simpa [gaussianMixtureAtomMeasure] using
          (indepFun_prod (X := id) (Y := id)
            (μ := rademacherMeasure) (ν := stdGaussian (GMMEuclidean n))
            measurable_id measurable_id)
      have hind : (fun z : GaussianMixtureAtom n => z.1) ⟂ᵢ[
          gaussianMixtureAtomMeasure n] (fun z => z.2 i) := by
        simpa [Function.comp_def] using
          hbase.comp measurable_id (by fun_prop : Measurable
            (fun g : GMMEuclidean n => g i))
      have hprod := hind.integral_fun_mul_eq_mul_integral
        (by fun_prop : AEStronglyMeasurable
          (fun z : GaussianMixtureAtom n => z.1) _)
        (by fun_prop : AEStronglyMeasurable
          (fun z : GaussianMixtureAtom n => z.2 i) _)
      rw [(isRademacher_fst_gaussianMixtureAtom n).integral_eq_zero,
        zero_mul] at hprod
      simpa [mul_comm] using hprod
    · have hsnd : HasLaw (fun z : GaussianMixtureAtom n => z.2)
          (stdGaussian (GMMEuclidean n)) (gaussianMixtureAtomMeasure n) := by
        simpa [gaussianMixtureAtomMeasure] using
          (measurePreserving_snd (μ := rademacherMeasure)
            (ν := stdGaussian (GMMEuclidean n))).hasLaw
      have hcomp := hsnd.integral_comp
        (f := fun g : GMMEuclidean n => g i * g j)
        (by fun_prop : AEStronglyMeasurable
          (fun g : GMMEuclidean n => g i * g j) _)
      have hstd := HDP.isIsotropic_iff.mp
        (HDP.Chapter3.standardGaussian_isIsotropic n) i j
      simpa using hcomp.trans hstd

/-- Identifies the probability law described by has law gaussian mixture augmented row.

**Lean implementation helper.** -/
private lemma hasLaw_gaussianMixtureAugmentedRow {m n : ℕ} (i : Fin m) :
    HasLaw
      (HDP.randomMatrixRow
        (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w) i)
      ((gaussianMixtureAtomMeasure n).map gaussianMixtureAugmentedVector)
      (gaussianMixtureSampleMeasure m n) := by
  let eval : GaussianMixtureSample m n → GaussianMixtureAtom n := fun w => w i
  have heval : HasLaw eval (gaussianMixtureAtomMeasure n)
      (gaussianMixtureSampleMeasure m n) :=
    (measurePreserving_eval
      (fun _ : Fin m => gaussianMixtureAtomMeasure n) i).hasLaw
  have hatom : HasLaw gaussianMixtureAugmentedVector
      ((gaussianMixtureAtomMeasure n).map gaussianMixtureAugmentedVector)
      (gaussianMixtureAtomMeasure n) := by
    exact ⟨measurable_gaussianMixtureAugmentedVector.aemeasurable, rfl⟩
  convert hatom.comp heval using 1
  funext w
  rfl

/-- Derives is isotropic from same law.

**Lean implementation helper.** -/
private lemma isIsotropic_of_sameLaw
    {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {n : ℕ}
    {ν : Measure (GMMEuclidean n)}
    {X : Ω₁ → GMMEuclidean n} {Y : Ω₂ → GMMEuclidean n}
    (hX : HasLaw X ν P₁) (hY : HasLaw Y ν P₂)
    (hYiso : HDP.IsIsotropic Y P₂) :
    HDP.IsIsotropic X P₁ := by
  apply HDP.isIsotropic_iff.mpr
  intro i j
  have hXi := hX.integral_comp (f := fun x => x i * x j)
    (by fun_prop : AEStronglyMeasurable
      (fun x : GMMEuclidean n => x i * x j) _)
  have hYi := hY.integral_comp (f := fun x => x i * x j)
    (by fun_prop : AEStronglyMeasurable
      (fun x : GMMEuclidean n => x i * x j) _)
  have hXi' : (∫ ω, X ω i * X ω j ∂P₁) =
      ∫ x : GMMEuclidean n, x i * x j ∂ν := by
    simpa [Function.comp_def] using hXi
  have hYi' : (∫ ω, Y ω i * Y ω j ∂P₂) =
      ∫ x : GMMEuclidean n, x i * x j ∂ν := by
    simpa [Function.comp_def] using hYi
  rw [hXi', ← hYi']
  exact HDP.isIsotropic_iff.mp hYiso i j

/-- The augmented Gaussian-mixture data matrix has almost-everywhere measurable rows.

**Lean implementation helper.** -/
lemma gaussianMixtureAugmentedMatrix_aemeasurableRows {m n : ℕ} :
    HDP.RandomMatrix.AEMeasurableRows
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w)
      (gaussianMixtureSampleMeasure m n) :=
  fun i => (hasLaw_gaussianMixtureAugmentedRow i).aemeasurable

/-- The augmented Gaussian-mixture data matrix has subgaussian rows.

**Lean implementation helper.** -/
lemma gaussianMixtureAugmentedMatrix_subGaussianRows {m n : ℕ} :
    HDP.RandomMatrix.SubGaussianRows
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w)
      (gaussianMixtureSampleMeasure m n) := by
  intro i u
  let ν := (gaussianMixtureAtomMeasure n).map gaussianMixtureAugmentedVector
  let f : GMMEuclidean (n + 1) → ℝ := fun x => inner ℝ x u
  have hf : HasLaw f (ν.map f) ν := ⟨(by fun_prop), rfl⟩
  have hrow := hf.comp (hasLaw_gaussianMixtureAugmentedRow i)
  have hatom : HasLaw gaussianMixtureAugmentedVector ν
      (gaussianMixtureAtomMeasure n) :=
    ⟨measurable_gaussianMixtureAugmentedVector.aemeasurable, rfl⟩
  have hatomScalar := hf.comp hatom
  exact subGaussian_of_sameLaw hrow hatomScalar
    (gaussianMixtureAugmentedAtom_marginal_subGaussian u)

/-- The augmented Gaussian-mixture data matrix has isotropic rows.

**Lean implementation helper.** -/
lemma gaussianMixtureAugmentedMatrix_isotropicRows {m n : ℕ} :
    HDP.RandomMatrix.IsotropicRows
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w)
      (gaussianMixtureSampleMeasure m n) := by
  intro i
  let ν := (gaussianMixtureAtomMeasure n).map gaussianMixtureAugmentedVector
  have hatom : HasLaw gaussianMixtureAugmentedVector ν
      (gaussianMixtureAtomMeasure n) :=
    ⟨measurable_gaussianMixtureAugmentedVector.aemeasurable, rfl⟩
  exact isIsotropic_of_sameLaw (hasLaw_gaussianMixtureAugmentedRow i) hatom
    (gaussianMixtureAugmentedAtom_isIsotropic n)

/-- The augmented Gaussian-mixture data matrix has independent rows.

**Lean implementation helper.** -/
lemma gaussianMixtureAugmentedMatrix_independentRows {m n : ℕ} :
    HDP.RandomMatrix.IndependentRows
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w)
      (gaussianMixtureSampleMeasure m n) := by
  have h := (iIndepFun_gaussianMixtureAtoms m n).comp
    (fun _ : Fin m => gaussianMixtureAugmentedVector)
    (fun _ => measurable_gaussianMixtureAugmentedVector)
  have heq :
      (fun i => HDP.randomMatrixRow
        (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w) i) =
      (fun i w => gaussianMixtureAugmentedVector (w i)) := by
    funext i w
    rfl
  change iIndepFun
    (fun i => HDP.randomMatrixRow
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w) i)
    (gaussianMixtureSampleMeasure m n)
  rw [heq]
  simpa [Function.comp_def] using h

/-- Every row of the augmented Gaussian-mixture data matrix has `ψ₂` norm at most `4`.

**Lean implementation helper.** -/
lemma gaussianMixtureAugmentedMatrix_rowPsi2Bound {m n : ℕ} :
    HDP.RandomMatrix.RowPsi2Bound
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w)
      (gaussianMixtureSampleMeasure m n) 4 := by
  intro i
  rw [HDP.psi2NormVector]
  apply csSup_le
  · let u : GMMEuclidean (n + 1) := EuclideanSpace.single 0 1
    exact ⟨HDP.psi2Norm
      (fun w => inner ℝ
        (HDP.randomMatrixRow
          (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w) i w) u)
      (gaussianMixtureSampleMeasure m n), u, by simp [u], rfl⟩
  · intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    let ν := (gaussianMixtureAtomMeasure n).map gaussianMixtureAugmentedVector
    let f : GMMEuclidean (n + 1) → ℝ := fun x => inner ℝ x u
    have hf : HasLaw f (ν.map f) ν := ⟨(by fun_prop), rfl⟩
    have hrow := hf.comp (hasLaw_gaussianMixtureAugmentedRow i)
    have hatom : HasLaw gaussianMixtureAugmentedVector ν
        (gaussianMixtureAtomMeasure n) :=
      ⟨measurable_gaussianMixtureAugmentedVector.aemeasurable, rfl⟩
    have hatomScalar := hf.comp hatom
    have heq := psi2Norm_eq_of_sameLaw hrow hatomScalar
    have heq' : HDP.psi2Norm
        (fun w => inner ℝ
          (HDP.randomMatrixRow
            (fun w : GaussianMixtureSample m n =>
              gaussianMixtureAugmentedMatrix w) i w) u)
        (gaussianMixtureSampleMeasure m n) =
        HDP.psi2Norm
          (fun z : GaussianMixtureAtom n =>
            inner ℝ (gaussianMixtureAugmentedVector z) u)
          (gaussianMixtureAtomMeasure n) := by
      simpa [f, Function.comp_def] using heq
    rw [heq']
    exact gaussianMixtureAugmentedAtom_marginal_psi2_le_four u hu

/-- Every row of the augmented Gaussian-mixture data matrix has finite `ψ₂` norm.

**Lean implementation helper.** -/
lemma gaussianMixtureAugmentedMatrix_rowPsi2Finite {m n : ℕ} :
    HDP.RandomMatrix.RowPsi2Finite
      (fun w : GaussianMixtureSample m n => gaussianMixtureAugmentedMatrix w)
      (gaussianMixtureSampleMeasure m n) := by
  intro i
  refine ⟨4, ?_⟩
  rintro r ⟨u, hu, rfl⟩
  let ν := (gaussianMixtureAtomMeasure n).map gaussianMixtureAugmentedVector
  let f : GMMEuclidean (n + 1) → ℝ := fun x => inner ℝ x u
  have hf : HasLaw f (ν.map f) ν := ⟨(by fun_prop), rfl⟩
  have hrow := hf.comp (hasLaw_gaussianMixtureAugmentedRow i)
  have hatom : HasLaw gaussianMixtureAugmentedVector ν
      (gaussianMixtureAtomMeasure n) :=
    ⟨measurable_gaussianMixtureAugmentedVector.aemeasurable, rfl⟩
  have hatomScalar := hf.comp hatom
  have heq := psi2Norm_eq_of_sameLaw hrow hatomScalar
  have heq' : HDP.psi2Norm
      (fun w => inner ℝ
        (HDP.randomMatrixRow
          (fun w : GaussianMixtureSample m n =>
            gaussianMixtureAugmentedMatrix w) i w) u)
      (gaussianMixtureSampleMeasure m n) =
      HDP.psi2Norm
        (fun z : GaussianMixtureAtom n =>
          inner ℝ (gaussianMixtureAugmentedVector z) u)
        (gaussianMixtureAtomMeasure n) := by
    simpa [f, Function.comp_def] using heq
  rw [heq']
  exact gaussianMixtureAugmentedAtom_marginal_psi2_le_four u hu

/-! ### Exact population second moment -/

/-- Every fixed Gaussian linear functional belongs to `L²` under the standard Gaussian measure.

**Lean implementation helper.** -/
private lemma memLp_two_stdGaussian_inner {n : ℕ} (x : GMMEuclidean n) :
    MemLp (fun g : GMMEuclidean n => inner ℝ g x) 2
      (stdGaussian (GMMEuclidean n)) := by
  have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
    MemLp (id : GMMEuclidean n → GMMEuclidean n) 2
      (stdGaussian (GMMEuclidean n))).continuousLinearMap_comp
      ((innerSL ℝ) x)
  simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm] using h

/-- Identifies integral std gaussian inner with zero.

**Lean implementation helper.** -/
private lemma integral_stdGaussian_inner_eq_zero {n : ℕ}
    (x : GMMEuclidean n) :
    ∫ g : GMMEuclidean n, inner ℝ g x ∂stdGaussian (GMMEuclidean n) = 0 := by
  have h := ProbabilityTheory.integral_strongDual_stdGaussian
    (E := GMMEuclidean n) ((innerSL ℝ) x)
  simpa [innerSL_apply_apply, real_inner_comm] using h

/-- For a standard Gaussian vector `g`, `∫ ⟨g,x⟩ * ⟨g,y⟩ = ⟨x,y⟩`.

**Lean implementation helper.** -/
private lemma integral_stdGaussian_inner_mul_inner {n : ℕ}
    (x y : GMMEuclidean n) :
    ∫ g : GMMEuclidean n, inner ℝ g x * inner ℝ g y
        ∂stdGaussian (GMMEuclidean n) = inner ℝ x y := by
  have hmemid : MemLp (id : GMMEuclidean n → GMMEuclidean n) 2
      (stdGaussian (GMMEuclidean n)) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hmemx : MemLp (fun g : GMMEuclidean n => inner ℝ x g) 2
      (stdGaussian (GMMEuclidean n)) := by
    simpa [Function.comp_def, innerSL_apply_apply] using
      hmemid.continuousLinearMap_comp ((innerSL ℝ) x)
  have hmemy : MemLp (fun g : GMMEuclidean n => inner ℝ y g) 2
      (stdGaussian (GMMEuclidean n)) := by
    simpa [Function.comp_def, innerSL_apply_apply] using
      hmemid.continuousLinearMap_comp ((innerSL ℝ) y)
  have hmeanx : ∫ g : GMMEuclidean n, inner ℝ x g
      ∂stdGaussian (GMMEuclidean n) = 0 := by
    simpa [real_inner_comm] using integral_stdGaussian_inner_eq_zero x
  have hmeany : ∫ g : GMMEuclidean n, inner ℝ y g
      ∂stdGaussian (GMMEuclidean n) = 0 := by
    simpa [real_inner_comm] using integral_stdGaussian_inner_eq_zero y
  have hcov := congrArg (fun B => B x y)
    (ProbabilityTheory.covarianceBilin_stdGaussian (E := GMMEuclidean n))
  rw [ProbabilityTheory.covarianceBilin_apply_eq_cov hmemid,
    ProbabilityTheory.covariance_eq_sub hmemx hmemy,
    hmeanx, hmeany] at hcov
  change (∫ g : GMMEuclidean n, inner ℝ x g * inner ℝ y g
      ∂stdGaussian (GMMEuclidean n)) - 0 * 0 = ((innerSL ℝ) x) y at hcov
  rw [mul_zero, sub_zero] at hcov
  calc
    ∫ g : GMMEuclidean n, inner ℝ g x * inner ℝ g y
        ∂stdGaussian (GMMEuclidean n) =
        ∫ g : GMMEuclidean n, inner ℝ x g * inner ℝ y g
          ∂stdGaussian (GMMEuclidean n) := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [real_inner_comm g x, real_inner_comm g y]
    _ = ((innerSL ℝ) x) y := hcov
    _ = inner ℝ x y := innerSL_apply_apply ℝ x y

/-- Every fixed linear functional of a Gaussian-mixture atom belongs to `L²`.

**Lean implementation helper.** -/
private lemma memLp_two_gaussianMixtureAtom_inner {n : ℕ}
    (mu x : GMMEuclidean n) :
    MemLp (fun z : GaussianMixtureAtom n => inner ℝ (z.1 • mu + z.2) x) 2
      (gaussianMixtureAtomMeasure n) := by
  have htheta : MemLp (fun z : GaussianMixtureAtom n => z.1) 2
      (gaussianMixtureAtomMeasure n) :=
    (isRademacher_fst_gaussianMixtureAtom n).memLp 2
  have hg0 := (memLp_two_stdGaussian_inner x).comp_measurePreserving
    (measurePreserving_snd (μ := rademacherMeasure)
      (ν := stdGaussian (GMMEuclidean n)))
  have hg : MemLp (fun z : GaussianMixtureAtom n => inner ℝ z.2 x) 2
      (gaussianMixtureAtomMeasure n) := by
    simpa [gaussianMixtureAtomMeasure, Function.comp_def] using hg0
  have hsum := (htheta.mul_const (inner ℝ mu x)).add hg
  convert hsum using 1
  funext z
  simp [inner_add_left, inner_smul_left]

/-- Exact bilinear second moment of one labelled mixture observation.

**Lean implementation helper.** -/
theorem gaussianMixtureAtom_inner_secondMoment {n : ℕ}
    (mu x y : GMMEuclidean n) :
    ∫ z : GaussianMixtureAtom n,
        inner ℝ (z.1 • mu + z.2) x * inner ℝ (z.1 • mu + z.2) y
        ∂gaussianMixtureAtomMeasure n =
      inner ℝ x y + inner ℝ mu x * inner ℝ mu y := by
  let a : ℝ := inner ℝ mu x
  let b : ℝ := inner ℝ mu y
  let gx : GMMEuclidean n → ℝ := fun g => inner ℝ g x
  let gy : GMMEuclidean n → ℝ := fun g => inner ℝ g y
  have hgx : Integrable gx (stdGaussian (GMMEuclidean n)) :=
    (memLp_two_stdGaussian_inner x).integrable (by norm_num)
  have hgy : Integrable gy (stdGaussian (GMMEuclidean n)) :=
    (memLp_two_stdGaussian_inner y).integrable (by norm_num)
  have hgxy : Integrable (fun g => gx g * gy g)
      (stdGaussian (GMMEuclidean n)) :=
    MemLp.integrable_mul (p := 2) (q := 2)
      (memLp_two_stdGaussian_inner x) (memLp_two_stdGaussian_inner y)
  have hint : Integrable
      (fun z : GaussianMixtureAtom n =>
        inner ℝ (z.1 • mu + z.2) x * inner ℝ (z.1 • mu + z.2) y)
      (gaussianMixtureAtomMeasure n) :=
    MemLp.integrable_mul (p := 2) (q := 2)
      (memLp_two_gaussianMixtureAtom_inner mu x)
      (memLp_two_gaussianMixtureAtom_inner mu y)
  have hinner (theta : ℝ) :
      ∫ g : GMMEuclidean n,
          inner ℝ (theta • mu + g) x * inner ℝ (theta • mu + g) y
          ∂stdGaussian (GMMEuclidean n) =
        theta ^ 2 * (a * b) + inner ℝ x y := by
    have hconst : Integrable (fun _g : GMMEuclidean n => theta ^ 2 * (a * b))
        (stdGaussian (GMMEuclidean n)) := integrable_const _
    have hcross1 : Integrable (fun g => theta * a * gy g)
        (stdGaussian (GMMEuclidean n)) := hgy.const_mul _
    have hcross2 : Integrable (fun g => theta * b * gx g)
        (stdGaussian (GMMEuclidean n)) := hgx.const_mul _
    calc
      ∫ g : GMMEuclidean n,
          inner ℝ (theta • mu + g) x * inner ℝ (theta • mu + g) y
          ∂stdGaussian (GMMEuclidean n) =
          ∫ g : GMMEuclidean n,
            (theta ^ 2 * (a * b) + theta * a * gy g) +
              (theta * b * gx g + gx g * gy g)
            ∂stdGaussian (GMMEuclidean n) := by
        apply integral_congr_ae
        filter_upwards [] with g
        simp only [inner_add_left, inner_smul_left]
        dsimp only [a, b, gx, gy]
        simp only [starRingEnd_apply, star_trivial]
        ring
      _ = (∫ _g : GMMEuclidean n, theta ^ 2 * (a * b)
              ∂stdGaussian (GMMEuclidean n)) +
            (∫ g : GMMEuclidean n, theta * a * gy g
              ∂stdGaussian (GMMEuclidean n)) +
          ((∫ g : GMMEuclidean n, theta * b * gx g
              ∂stdGaussian (GMMEuclidean n)) +
            ∫ g : GMMEuclidean n, gx g * gy g
              ∂stdGaussian (GMMEuclidean n)) := by
        have hleft := integral_add hconst hcross1
        have hright := integral_add hcross2 hgxy
        have hall := integral_add (hconst.add hcross1) (hcross2.add hgxy)
        simpa only [Pi.add_apply] using hall.trans (congrArg₂ (· + ·) hleft hright)
      _ = theta ^ 2 * (a * b) + inner ℝ x y := by
        rw [integral_const, probReal_univ, one_smul,
          integral_const_mul, integral_const_mul,
          show (∫ g : GMMEuclidean n, gy g
              ∂stdGaussian (GMMEuclidean n)) = 0 by
            exact integral_stdGaussian_inner_eq_zero y,
          show (∫ g : GMMEuclidean n, gx g
              ∂stdGaussian (GMMEuclidean n)) = 0 by
            exact integral_stdGaussian_inner_eq_zero x,
          show (∫ g : GMMEuclidean n, gx g * gy g
              ∂stdGaussian (GMMEuclidean n)) = inner ℝ x y by
            exact integral_stdGaussian_inner_mul_inner x y]
        ring
  have hr : HDP.IsRademacher (id : ℝ → ℝ) rademacherMeasure := by
    refine ⟨aemeasurable_id, ?_⟩
    rw [Measure.map_id]
    rfl
  have hthetaSq :
      ∫ theta : ℝ, theta ^ 2 ∂rademacherMeasure = 1 := by
    have h := hr.integral_comp (fun theta => theta ^ 2)
    simpa [rademacherMeasure] using h
  rw [gaussianMixtureAtomMeasure, integral_prod _ hint]
  simp_rw [hinner]
  rw [integral_add]
  · rw [integral_mul_const, hthetaSq, one_mul, integral_const,
      probReal_univ, one_smul]
    dsimp only [a, b]
    ring
  · exact (hr.integrable_comp (fun theta => theta ^ 2)).mul_const _
  · exact integrable_const _

/-- Computes the second moment of gaussian mixture atom inner squared.

**Lean implementation helper.** -/
theorem gaussianMixtureAtom_inner_sq_secondMoment {n : ℕ}
    (mu x : GMMEuclidean n) :
    ∫ z : GaussianMixtureAtom n, inner ℝ (z.1 • mu + z.2) x ^ 2
        ∂gaussianMixtureAtomMeasure n =
      ‖x‖ ^ 2 + inner ℝ mu x ^ 2 := by
  simpa [pow_two, real_inner_self_eq_norm_sq] using
    gaussianMixtureAtom_inner_secondMoment mu x x

/-- The population second-moment matrix `I + mu mu^T`.

**Lean implementation helper.** -/
def gaussianMixturePopulationMatrix {n : ℕ} (mu : GMMEuclidean n) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 + outerProductMatrix mu

/-- Identifies gaussian mixture factor matrix gram with population.

**Lean implementation helper.** -/
lemma gaussianMixtureFactorMatrix_gram_eq_population {n : ℕ}
    (mu : GMMEuclidean n) :
    gaussianMixtureFactorMatrix mu *
        (gaussianMixtureFactorMatrix mu).transpose =
      gaussianMixturePopulationMatrix mu := by
  simpa [gaussianMixturePopulationMatrix] using
    gaussianMixtureFactorMatrix_mul_transpose mu

/-- Entry `(j,k)` of the Gaussian-mixture population matrix is `(if j = k then 1 else 0) + mu j * mu k`.

**Lean implementation helper.** -/
@[simp]
lemma gaussianMixturePopulationMatrix_apply {n : ℕ} (mu : GMMEuclidean n)
    (j k : Fin n) :
    gaussianMixturePopulationMatrix mu j k =
      (if j = k then 1 else 0) + mu j * mu k := by
  simp [gaussianMixturePopulationMatrix, outerProductMatrix, Matrix.one_apply]

/-- Mixture second moment has spike `I+mu mu^T`; its top eigendirection is the mean direction
and drives classification.

**Book Chapter 4, pp.129--130, GMM signal calculation.** -/
theorem exercise_4_51_secondMomentMatrix {n : ℕ} (mu : GMMEuclidean n) :
    HDP.secondMomentMatrix
        (fun z : GaussianMixtureAtom n => z.1 • mu + z.2)
        (gaussianMixtureAtomMeasure n) =
      gaussianMixturePopulationMatrix mu := by
  ext j k
  let ej : GMMEuclidean n := EuclideanSpace.single j 1
  let ek : GMMEuclidean n := EuclideanSpace.single k 1
  have h := gaussianMixtureAtom_inner_secondMoment mu ej ek
  simpa [HDP.secondMomentMatrix, ej, ek,
    EuclideanSpace.inner_single_right, gaussianMixturePopulationMatrix,
    outerProductMatrix, Matrix.one_apply, eq_comm] using h

/-- The self-adjoint population second-moment operator.

**Lean implementation helper.** -/
def gaussianMixturePopulationOperator {n : ℕ} (mu : GMMEuclidean n) :
    GMMEuclidean n →L[ℝ] GMMEuclidean n :=
  ContinuousLinearMap.id ℝ _ + InnerProductSpace.rankOne ℝ mu mu

/-- The Gaussian-mixture population operator acts by `x ↦ x + ⟨mu,x⟩ • mu`.

**Lean implementation helper.** -/
@[simp]
lemma gaussianMixturePopulationOperator_apply {n : ℕ} (mu x : GMMEuclidean n) :
    gaussianMixturePopulationOperator mu x =
      x + inner ℝ mu x • mu := by
  simp [gaussianMixturePopulationOperator, InnerProductSpace.rankOne_apply]

/-- Shows that gaussian mixture population operator is self-adjoint.

**Lean implementation helper.** -/
lemma gaussianMixturePopulationOperator_isSelfAdjoint {n : ℕ}
    (mu : GMMEuclidean n) :
    IsSelfAdjoint (gaussianMixturePopulationOperator mu) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  change ((LinearMap.id : GMMEuclidean n →ₗ[ℝ] GMMEuclidean n) +
    (InnerProductSpace.rankOne ℝ mu mu).toLinearMap).IsSymmetric
  exact LinearMap.IsSymmetric.id.add
    (InnerProductSpace.isSymmetric_rankOne_self mu)

/-- The population second-moment quadratic form of the balanced Gaussian mixture is `‖x‖²+⟨μ,x⟩²`.

**Lean implementation helper.** -/
lemma gaussianMixturePopulationOperator_reApplyInnerSelf {n : ℕ}
    (mu x : GMMEuclidean n) :
    (gaussianMixturePopulationOperator mu).reApplyInnerSelf x =
      ‖x‖ ^ 2 + inner ℝ mu x ^ 2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply,
    gaussianMixturePopulationOperator_apply]
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    real_inner_self_eq_norm_sq, RCLike.re_to_real]
  ring

/-- The population operator is the continuous-operator realization of the exact population
matrix.

**Lean implementation helper.** -/
theorem gaussianMixturePopulationMatrix_toOperator {n : ℕ}
    (mu : GMMEuclidean n) :
    (gaussianMixturePopulationMatrix mu).toEuclideanLin.toContinuousLinearMap =
      gaussianMixturePopulationOperator mu := by
  apply ContinuousLinearMap.ext
  intro x
  have hmatrix : outerProductMatrix mu = outerMatrix mu mu := by
    ext j k
    simp [outerProductMatrix, outerMatrix, Matrix.vecMulVec]
  change (gaussianMixturePopulationMatrix mu).toEuclideanLin x =
    gaussianMixturePopulationOperator mu x
  rw [gaussianMixturePopulationMatrix, hmatrix, map_add,
    toEuclideanLin_outerMatrix]
  simp [gaussianMixturePopulationOperator,
    InnerProductSpace.rankOne_apply]

/-- Unit direction of a nonzero mixture mean.

**Lean implementation helper.** -/
def gaussianMixtureDirection {n : ℕ} (mu : GMMEuclidean n) : GMMEuclidean n :=
  ‖mu‖⁻¹ • mu

/-- For nonzero `mu`, the normalized Gaussian-mixture direction has norm one.

**Lean implementation helper.** -/
lemma norm_gaussianMixtureDirection {n : ℕ} {mu : GMMEuclidean n}
    (hmu : mu ≠ 0) :
    ‖gaussianMixtureDirection mu‖ = 1 := by
  have hr : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  simp [gaussianMixtureDirection, norm_smul, hr.ne']

/-- The mixture direction is an eigenvector of the population second-moment operator with eigenvalue `1+‖μ‖²`.

**Lean implementation helper.** -/
lemma gaussianMixturePopulationOperator_direction {n : ℕ}
    {mu : GMMEuclidean n} (hmu : mu ≠ 0) :
    gaussianMixturePopulationOperator mu (gaussianMixtureDirection mu) =
      (1 + ‖mu‖ ^ 2) • gaussianMixtureDirection mu := by
  have hr : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  rw [gaussianMixturePopulationOperator_apply]
  simp only [gaussianMixtureDirection, inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [← add_smul, smul_smul]
  congr 1
  field_simp [hr.ne']

/-- The inner product of the mean vector with its normalized mixture direction is `‖μ‖`.

**Lean implementation helper.** -/
lemma inner_mu_gaussianMixtureDirection {n : ℕ} {mu : GMMEuclidean n}
    (hmu : mu ≠ 0) :
    inner ℝ mu (gaussianMixtureDirection mu) = ‖mu‖ := by
  have hr : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  simp only [gaussianMixtureDirection, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [hr.ne']

/-- The ordered top population eigenvalue is `1 + ‖mu‖²`.

**Book Chapter 4, pp.129--130, GMM signal calculation.** -/
theorem gaussianMixture_topEigenvalue {n : ℕ} (hn : 0 < n)
    {mu : GMMEuclidean n} (hmu : mu ≠ 0) :
    let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
    hT.isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨0, hn⟩ : Fin n) =
      1 + ‖mu‖ ^ 2 := by
  dsimp only
  let T := gaussianMixturePopulationOperator mu
  let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
  let hdim : Module.finrank ℝ (GMMEuclidean n) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let i0 : Fin n := ⟨0, hn⟩
  let b := hT.isSymmetric.eigenvectorBasis hdim i0
  let u := gaussianMixtureDirection mu
  have hb : ‖b‖ = 1 :=
    (hT.isSymmetric.eigenvectorBasis hdim).norm_eq_one i0
  have hu : ‖u‖ = 1 := norm_gaussianMixtureDirection hmu
  have hattain : ‖b‖ = 1 ∧
      T.reApplyInnerSelf b = hT.isSymmetric.eigenvalues hdim i0 := by
    simpa [b] using HDP.Chapter3.pca_kth_eigenvector_attains T hT hdim i0
  have hupper : hT.isSymmetric.eigenvalues hdim i0 ≤ 1 + ‖mu‖ ^ 2 := by
    rw [← hattain.2, gaussianMixturePopulationOperator_reApplyInnerSelf]
    have hinner : |inner ℝ mu b| ≤ ‖mu‖ := by
      calc
        |inner ℝ mu b| ≤ ‖mu‖ * ‖b‖ := abs_real_inner_le_norm _ _
        _ = ‖mu‖ := by rw [hb, mul_one]
    have hinnersq : inner ℝ mu b ^ 2 ≤ ‖mu‖ ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ mu b)) (norm_nonneg mu)).2 hinner
      simpa [sq_abs] using hs
    rw [hb]
    nlinarith
  have hmax := HDP.Chapter3.pca_kth_maximum_principle T hT hdim i0
  have huorth : ∀ i : Fin n, i < i0 →
      inner ℝ (hT.isSymmetric.eigenvectorBasis hdim i) u = 0 := by
    intro i hi
    change i.val < 0 at hi
    omega
  have hulower := hmax.2 ⟨u, ⟨hu, huorth⟩, rfl⟩
  have hlower : 1 + ‖mu‖ ^ 2 ≤
      hT.isSymmetric.eigenvalues hdim i0 := by
    have hinner := inner_mu_gaussianMixtureDirection hmu
    rw [gaussianMixturePopulationOperator_reApplyInnerSelf, hu, hinner] at hulower
    nlinarith
  exact le_antisymm hupper hlower

/-- The canonical top population eigenvector agrees with the mean direction up to the
unavoidable global sign.

**Lean implementation helper.** -/
theorem gaussianMixture_topEigenvector_eq_sign_direction {n : ℕ}
    (hn : 0 < n) {mu : GMMEuclidean n} (hmu : mu ≠ 0) :
    let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
    let b := hT.isSymmetric.eigenvectorBasis
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨0, hn⟩ : Fin n)
    ∃ theta : ℝ, (theta = 1 ∨ theta = -1) ∧
      gaussianMixtureDirection mu = theta • b := by
  dsimp only
  let T := gaussianMixturePopulationOperator mu
  let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
  let hdim : Module.finrank ℝ (GMMEuclidean n) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let i0 : Fin n := ⟨0, hn⟩
  let b := hT.isSymmetric.eigenvectorBasis hdim i0
  let u := gaussianMixtureDirection mu
  have hb : ‖b‖ = 1 :=
    (hT.isSymmetric.eigenvectorBasis hdim).norm_eq_one i0
  have hu : ‖u‖ = 1 := norm_gaussianMixtureDirection hmu
  have hattain : ‖b‖ = 1 ∧
      T.reApplyInnerSelf b = hT.isSymmetric.eigenvalues hdim i0 := by
    simpa [b] using HDP.Chapter3.pca_kth_eigenvector_attains T hT hdim i0
  have hlambda := gaussianMixture_topEigenvalue hn hmu
  change hT.isSymmetric.eigenvalues hdim i0 = 1 + ‖mu‖ ^ 2 at hlambda
  have hmusq : inner ℝ mu b ^ 2 = ‖mu‖ ^ 2 := by
    have hq : ‖b‖ ^ 2 + inner ℝ mu b ^ 2 = 1 + ‖mu‖ ^ 2 := by
      calc
        ‖b‖ ^ 2 + inner ℝ mu b ^ 2 = T.reApplyInnerSelf b :=
          (gaussianMixturePopulationOperator_reApplyInnerSelf mu b).symm
        _ = hT.isSymmetric.eigenvalues hdim i0 := hattain.2
        _ = 1 + ‖mu‖ ^ 2 := hlambda
    rw [hb] at hq
    nlinarith
  have hr : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  have hinner : inner ℝ u b = ‖mu‖⁻¹ * inner ℝ mu b := by
    simp [u, gaussianMixtureDirection, inner_smul_left]
  have habs : |inner ℝ u b| ^ 2 = 1 := by
    rw [hinner, abs_mul, abs_inv, abs_of_pos hr, mul_pow, sq_abs,
      hmusq]
    field_simp [hr.ne']
  have hsin : 1 - |inner ℝ u b| ^ 2 ≤ (0 : ℝ) ^ 2 := by
    rw [habs]
    norm_num
  obtain ⟨theta, htheta, hdist⟩ :=
    exercise_4_16_angle_sign_distance u b hu hb (by norm_num) hsin
  refine ⟨theta, htheta, ?_⟩
  have hdist0 : ‖u - theta • b‖ ≤ 0 := by simpa using hdist
  have hz : ‖u - theta • b‖ = 0 := le_antisymm hdist0 (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Every remaining ordered population eigenvalue is exactly `1`.

**Lean implementation helper.** -/
theorem gaussianMixture_tailEigenvalue {n : ℕ} (hn : 0 < n)
    {mu : GMMEuclidean n} (hmu : mu ≠ 0) (i : Fin n)
    (hi : i ≠ (⟨0, hn⟩ : Fin n)) :
    let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
    hT.isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) i = 1 := by
  dsimp only
  let T := gaussianMixturePopulationOperator mu
  let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
  let hdim : Module.finrank ℝ (GMMEuclidean n) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let i0 : Fin n := ⟨0, hn⟩
  let b0 := hT.isSymmetric.eigenvectorBasis hdim i0
  let bi := hT.isSymmetric.eigenvectorBasis hdim i
  let u := gaussianMixtureDirection mu
  obtain ⟨theta, htheta, hu⟩ :=
    gaussianMixture_topEigenvector_eq_sign_direction hn hmu
  change u = theta • b0 at hu
  have horth0 : inner ℝ b0 bi = 0 := by
    dsimp only [b0, bi]
    rw [(hT.isSymmetric.eigenvectorBasis hdim).inner_eq_ite]
    have hne : i0 ≠ i := by
      intro h
      apply hi
      simpa [i0] using h.symm
    simp [hne]
  have huorth : inner ℝ u bi = 0 := by
    rw [hu, inner_smul_left, horth0]
    simp
  have hr : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  have hmueq : mu = ‖mu‖ • u := by
    dsimp [u, gaussianMixtureDirection]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hmuorth : inner ℝ mu bi = 0 := by
    rw [hmueq, inner_smul_left, huorth]
    simp
  have hone : T bi = (1 : ℝ) • bi := by
    rw [gaussianMixturePopulationOperator_apply, hmuorth]
    simp
  have heig := hT.isSymmetric.apply_eigenvectorBasis hdim i
  change T bi = hT.isSymmetric.eigenvalues hdim i • bi at heig
  have hbi : ‖bi‖ = 1 :=
    (hT.isSymmetric.eigenvectorBasis hdim).norm_eq_one i
  have hbi0 : bi ≠ 0 := by
    rw [← norm_ne_zero_iff, hbi]
    norm_num
  have heq' : (1 : ℝ) = hT.isSymmetric.eigenvalues hdim i :=
    smul_left_injective ℝ hbi0 (hone.symm.trans heig)
  exact heq'.symm

/-- Exact eigengap used by Davis--Kahan in the corresponding exercise.

**Lean implementation helper.** -/
theorem gaussianMixture_populationEigengap {n : ℕ} (hn : 0 < n)
    {mu : GMMEuclidean n} (hmu : mu ≠ 0) (i : Fin n)
    (hi : i ≠ (⟨0, hn⟩ : Fin n)) :
    let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
    |hT.isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) (⟨0, hn⟩ : Fin n) -
      hT.isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) i| = ‖mu‖ ^ 2 := by
  dsimp only
  rw [gaussianMixture_topEigenvalue hn hmu,
    gaussianMixture_tailEigenvalue hn hmu i hi]
  rw [show (1 + ‖mu‖ ^ 2 - 1) = ‖mu‖ ^ 2 by ring,
    abs_of_nonneg (sq_nonneg ‖mu‖)]

/-! ### Empirical operator and the spectral algorithm -/

/-- The empirical uncentered second-moment operator `m^{-1} sum_i X_i X_i^T`.

**Lean implementation helper.** -/
def gaussianMixtureEmpiricalOperator {m n : ℕ}
    (X : Fin m → GMMEuclidean n) : GMMEuclidean n →L[ℝ] GMMEuclidean n :=
  (sampleCovarianceMatrix X).toEuclideanLin.toContinuousLinearMap

/-- Shows that gaussian mixture empirical operator is self-adjoint.

**Lean implementation helper.** -/
lemma gaussianMixtureEmpiricalOperator_isSelfAdjoint {m n : ℕ}
    (X : Fin m → GMMEuclidean n) :
    IsSelfAdjoint (gaussianMixtureEmpiricalOperator X) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  rw [gaussianMixtureEmpiricalOperator]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    have hsym : (sampleCovarianceMatrix X).IsSymm := by
      apply Matrix.IsSymm.ext
      intro j k
      simp [sampleCovarianceMatrix_apply, mul_comm]
    exact Matrix.isHermitian_iff_isSymm.mpr hsym)

/-- The empirical second-moment quadratic form is the average of the squared sample projections onto `x`.

**Lean implementation helper.** -/
lemma gaussianMixtureEmpiricalOperator_reApplyInnerSelf {m n : ℕ}
    (X : Fin m → GMMEuclidean n) (x : GMMEuclidean n) :
    (gaussianMixtureEmpiricalOperator X).reApplyInnerSelf x =
      (m : ℝ)⁻¹ * ∑ i, inner ℝ (X i) x ^ 2 := by
  let A := dataMatrix X
  have hop : normalizedGramDeviationOperator A =
      gaussianMixtureEmpiricalOperator X - ContinuousLinearMap.id ℝ _ := by
    rw [normalizedGramDeviationOperator, gaussianMixtureEmpiricalOperator,
      sampleCovarianceMatrix_eq_normalizedGram]
    change (HDP.normalizedGram m A - 1).toEuclideanLin.toContinuousLinearMap =
      (HDP.normalizedGram m A).toEuclideanLin.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ _
    rw [map_sub]
    apply ContinuousLinearMap.ext
    intro y
    simp
  have hdev := normalizedGramDeviationOperator_rayleigh A x
  have hleft : (normalizedGramDeviationOperator A).reApplyInnerSelf x =
      (gaussianMixtureEmpiricalOperator X).reApplyInnerSelf x - ‖x‖ ^ 2 := by
    rw [hop]
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, inner_sub_left]
  rw [hleft] at hdev
  have hrows := norm_toEuclideanLin_sq_eq_sum_rows A x
  have hrowinner : ∀ i : Fin m,
      (∑ j : Fin n, A i j * x j) = inner ℝ (X i) x := by
    intro i
    simp [A, dataMatrix, PiLp.inner_apply, mul_comm]
  simp_rw [hrowinner] at hrows
  rw [hrows] at hdev
  linarith

/-- Agreement with the source-facing sample covariance matrix.

**Lean implementation helper.** -/
theorem gaussianMixtureEmpiricalOperator_eq_sampleCovariance {m n : ℕ}
    (X : Fin m → GMMEuclidean n) :
    gaussianMixtureEmpiricalOperator X =
      (sampleCovarianceMatrix X).toEuclideanLin.toContinuousLinearMap := by
  rfl

/-- The deterministic ordered top empirical eigenvector.

**Book Chapter 4, pp.129--130, GMM signal calculation.** -/
def gaussianMixtureSpectralVector {m n : ℕ} (hn : 0 < n)
    (X : Fin m → GMMEuclidean n) : GMMEuclidean n :=
  ((gaussianMixtureEmpiricalOperator_isSelfAdjoint X).isSymmetric.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ))) (⟨0, hn⟩ : Fin n)

/-- The ordered top empirical eigenvector `gaussianMixtureSpectralVector hn X` has norm one.

**Lean implementation helper.** -/
lemma norm_gaussianMixtureSpectralVector {m n : ℕ} (hn : 0 < n)
    (X : Fin m → GMMEuclidean n) :
    ‖gaussianMixtureSpectralVector hn X‖ = 1 := by
  let hS := (gaussianMixtureEmpiricalOperator_isSelfAdjoint X).isSymmetric
  exact (hS.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ))).norm_eq_one (⟨0, hn⟩ : Fin n)

/-- Scores used by the source's spectral classifier.

**Lean implementation helper.** -/
def gaussianMixtureSpectralScore {m n : ℕ} (hn : 0 < n)
    (X : Fin m → GMMEuclidean n) (i : Fin m) : ℝ :=
  inner ℝ (X i) (gaussianMixtureSpectralVector hn X)

/-- Number of errors, minimized over the global eigenvector sign.

**Lean implementation helper.** -/
def gaussianMixtureMisclassified {m n : ℕ} (hn : 0 < n)
    (mu : GMMEuclidean n) (w : GaussianMixtureSample m n) : ℕ :=
  HDP.misclassifiedUpToSign (fun i => gaussianMixtureLabel w i)
    (gaussianMixtureSpectralScore hn (fun i => gaussianMixturePoint mu w i))

/-! ### Deterministic aggregate classification bound -/

/-- When a predicted sign disagrees with a nonzero label, label times score is nonpositive.

**Lean implementation helper.** -/
private lemma signMismatch_mul_score_nonpos {a s : ℝ}
    (ha : a = 1 ∨ a = -1)
    (hmis : HDP.spectralSignLabel (fun _ : Unit => s) () ≠ a) :
    a * s ≤ 0 := by
  rcases ha with rfl | rfl
  · unfold HDP.spectralSignLabel at hmis
    split_ifs at hmis with hs
    · exact (hmis rfl).elim
    · nlinarith
  · unfold HDP.spectralSignLabel at hmis
    split_ifs at hmis with hs
    · nlinarith
    · exact (hmis rfl).elim

/-- Bounds half by abs projection of sign mismatch.

**Lean implementation helper.** -/
private lemma half_le_abs_projection_of_signMismatch {n : ℕ}
    {a r : ℝ} (ha : a = 1 ∨ a = -1)
    (x u v : GMMEuclidean n)
    (hmargin : r / 2 < a * inner ℝ x u)
    (hmis : HDP.spectralSignLabel (fun _ : Unit => inner ℝ x v) () ≠ a) :
    r / 2 ≤ |inner ℝ x (v - u)| := by
  have hscore := signMismatch_mul_score_nonpos ha hmis
  have hsub : inner ℝ x (v - u) = inner ℝ x v - inner ℝ x u := by
    rw [inner_sub_right]
  rcases ha with rfl | rfl
  · norm_num at hmargin hscore
    rw [hsub]
    nlinarith [neg_le_abs (inner ℝ x v - inner ℝ x u)]
  · norm_num at hmargin hscore
    rw [hsub]
    nlinarith [le_abs_self (inner ℝ x v - inner ℝ x u)]

/-- Purely deterministic aggregate estimate. It is valid even when `v` is chosen from the same
data `X`; no conditional-independence step occurs.

**Lean implementation helper.** -/
theorem deterministic_sign_misclassification_le {m n : ℕ}
    (X : Fin m → GMMEuclidean n) (truth : Fin m → ℝ)
    (htruth : ∀ i, truth i = 1 ∨ truth i = -1)
    (u v : GMMEuclidean n) {r : ℝ} (hr : 0 < r) :
    let bad := Finset.univ.filter fun i =>
      truth i * inner ℝ (X i) u ≤ r / 2
    ((Finset.univ.filter fun i =>
        HDP.spectralSignLabel (fun j => inner ℝ (X j) v) i ≠ truth i).card : ℝ) ≤
      (bad.card : ℝ) +
        (4 / r ^ 2) * ∑ i, inner ℝ (X i) (v - u) ^ 2 := by
  classical
  dsimp only
  let M := Finset.univ.filter fun i =>
    HDP.spectralSignLabel (fun j => inner ℝ (X j) v) i ≠ truth i
  let B := Finset.univ.filter fun i =>
    truth i * inner ℝ (X i) u ≤ r / 2
  let L := Finset.univ.filter fun i =>
    (r / 2) ^ 2 ≤ inner ℝ (X i) (v - u) ^ 2
  have hsubset : M ⊆ B ∪ L := by
    intro i hi
    have hiM := (Finset.mem_filter.mp hi).2
    by_cases hiB : truth i * inner ℝ (X i) u ≤ r / 2
    · exact Finset.mem_union_left L (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiB⟩)
    · apply Finset.mem_union_right B
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hlarge := half_le_abs_projection_of_signMismatch
        (htruth i) (X i) u v (lt_of_not_ge hiB) (by
          simpa [HDP.spectralSignLabel] using hiM)
      have hs := (sq_le_sq₀ (by positivity : 0 ≤ r / 2)
        (abs_nonneg (inner ℝ (X i) (v - u)))).2 hlarge
      simpa [sq_abs] using hs
  have hcardNat : M.card ≤ B.card + L.card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le B L)
  have hcard : (M.card : ℝ) ≤ (B.card : ℝ) + (L.card : ℝ) := by
    exact_mod_cast hcardNat
  have hsum : (L.card : ℝ) * (r / 2) ^ 2 ≤
      ∑ i, inner ℝ (X i) (v - u) ^ 2 := by
    calc
      (L.card : ℝ) * (r / 2) ^ 2 =
          ∑ i ∈ L, (r / 2) ^ 2 := by simp
      _ ≤ ∑ i ∈ L, inner ℝ (X i) (v - u) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i ∈ Finset.univ, inner ℝ (X i) (v - u) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi hnot => sq_nonneg (inner ℝ (X i) (v - u)))
      _ = ∑ i, inner ℝ (X i) (v - u) ^ 2 := rfl
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hL : (L.card : ℝ) ≤
      (4 / r ^ 2) * ∑ i, inner ℝ (X i) (v - u) ^ 2 := by
    rw [show (4 / r ^ 2) * (∑ i, inner ℝ (X i) (v - u) ^ 2) =
      (4 * ∑ i, inner ℝ (X i) (v - u) ^ 2) / r ^ 2 by ring]
    apply (le_div_iff₀ hr2).2
    nlinarith
  change (M.card : ℝ) ≤ (B.card : ℝ) + _
  linarith

/-- Bounds projection energy by empirical op norm.

**Lean implementation helper.** -/
lemma projectionEnergy_le_empiricalOpNorm {m n : ℕ} (hm : 0 < m)
    (X : Fin m → GMMEuclidean n) (d : GMMEuclidean n) :
    (∑ i, inner ℝ (X i) d ^ 2) ≤
      (m : ℝ) * ‖gaussianMixtureEmpiricalOperator X‖ * ‖d‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq0 := gaussianMixtureEmpiricalOperator_reApplyInnerSelf X d
  have heq : (∑ i, inner ℝ (X i) d ^ 2) =
      (m : ℝ) * (gaussianMixtureEmpiricalOperator X).reApplyInnerSelf d := by
    rw [heq0]
    field_simp [hmR.ne']
  have hq : (gaussianMixtureEmpiricalOperator X).reApplyInnerSelf d ≤
      ‖gaussianMixtureEmpiricalOperator X‖ * ‖d‖ ^ 2 := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
    calc
      inner ℝ (gaussianMixtureEmpiricalOperator X d) d
          ≤ |inner ℝ (gaussianMixtureEmpiricalOperator X d) d| := le_abs_self _
      _ ≤ ‖gaussianMixtureEmpiricalOperator X d‖ * ‖d‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (‖gaussianMixtureEmpiricalOperator X‖ * ‖d‖) * ‖d‖ := by
        exact mul_le_mul_of_nonneg_right
          ((gaussianMixtureEmpiricalOperator X).le_opNorm d) (norm_nonneg d)
      _ = ‖gaussianMixtureEmpiricalOperator X‖ * ‖d‖ ^ 2 := by ring
  rw [heq]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hq hmR.le

/-- Global-sign version of the deterministic aggregate estimate.

**Lean implementation helper.** -/
theorem deterministic_misclassifiedUpToSign_le {m n : ℕ}
    (X : Fin m → GMMEuclidean n) (truth : Fin m → ℝ)
    (htruth : ∀ i, truth i = 1 ∨ truth i = -1)
    (u v : GMMEuclidean n) {theta r : ℝ}
    (htheta : theta = 1 ∨ theta = -1) (hr : 0 < r) :
    let bad := Finset.univ.filter fun i =>
      truth i * inner ℝ (X i) u ≤ r / 2
    (HDP.misclassifiedUpToSign truth (fun i => inner ℝ (X i) v) : ℝ) ≤
      (bad.card : ℝ) + (4 / r ^ 2) *
        ∑ i, inner ℝ (X i) (theta • v - u) ^ 2 := by
  classical
  dsimp only
  have hraw := deterministic_sign_misclassification_le X truth htruth u
    (theta • v) hr
  rcases htheta with rfl | rfl
  · rw [one_smul] at hraw ⊢
    calc
      (HDP.misclassifiedUpToSign truth (fun i => inner ℝ (X i) v) : ℝ)
          ≤ ((Finset.univ.filter fun i =>
              HDP.spectralSignLabel (fun j => inner ℝ (X j) v) i ≠
                truth i).card : ℝ) := by
            exact_mod_cast (min_le_left _ _ :
              HDP.misclassifiedUpToSign truth (fun i => inner ℝ (X i) v) ≤ _)
      _ ≤ _ := hraw
  · have hraw' :
        ((Finset.univ.filter fun i =>
          HDP.spectralSignLabel (fun j => -inner ℝ (X j) v) i ≠ truth i).card : ℝ) ≤
        ((Finset.univ.filter fun i =>
          truth i * inner ℝ (X i) u ≤ r / 2).card : ℝ) +
          (4 / r ^ 2) * ∑ i, inner ℝ (X i) ((-1 : ℝ) • v - u) ^ 2 := by
      simpa [inner_neg_right] using hraw
    calc
      (HDP.misclassifiedUpToSign truth (fun i => inner ℝ (X i) v) : ℝ)
          ≤ ((Finset.univ.filter fun i =>
              HDP.spectralSignLabel (fun j => -inner ℝ (X j) v) i ≠
                truth i).card : ℝ) := by
            exact_mod_cast (min_le_right _ _ :
              HDP.misclassifiedUpToSign truth (fun i => inner ℝ (X i) v) ≤ _)
      _ ≤ _ := hraw'

/-- Operator-norm form of the aggregate estimate.

**Lean implementation helper.** -/
theorem deterministic_misclassifiedUpToSign_le_opNorm {m n : ℕ}
    (hm : 0 < m) (X : Fin m → GMMEuclidean n) (truth : Fin m → ℝ)
    (htruth : ∀ i, truth i = 1 ∨ truth i = -1)
    (u v : GMMEuclidean n) {theta r : ℝ}
    (htheta : theta = 1 ∨ theta = -1) (hr : 0 < r) :
    let bad := Finset.univ.filter fun i =>
      truth i * inner ℝ (X i) u ≤ r / 2
    (HDP.misclassifiedUpToSign truth (fun i => inner ℝ (X i) v) : ℝ) ≤
      (bad.card : ℝ) + (4 / r ^ 2) * (m : ℝ) *
        ‖gaussianMixtureEmpiricalOperator X‖ * ‖theta • v - u‖ ^ 2 := by
  dsimp only
  have hraw := deterministic_misclassifiedUpToSign_le X truth htruth u v
    htheta hr
  have henergy := projectionEnergy_le_empiricalOpNorm hm X (theta • v - u)
  have hc : 0 ≤ 4 / r ^ 2 := by positivity
  calc
    _ ≤ ((Finset.univ.filter fun i =>
        truth i * inner ℝ (X i) u ≤ r / 2).card : ℝ) +
        (4 / r ^ 2) * ∑ i, inner ℝ (X i) (theta • v - u) ^ 2 := hraw
    _ ≤ ((Finset.univ.filter fun i =>
        truth i * inner ℝ (X i) u ≤ r / 2).card : ℝ) +
        (4 / r ^ 2) * ((m : ℝ) *
          ‖gaussianMixtureEmpiricalOperator X‖ * ‖theta • v - u‖ ^ 2) := by
      gcongr
    _ = _ := by ring

/-! ### Davis--Kahan for the concrete mixture operators -/

/-- The Gaussian-mixture population operator satisfies `‖gaussianMixturePopulationOperator mu‖ ≤ 1 + ‖mu‖²`.

**Lean implementation helper.** -/
lemma norm_gaussianMixturePopulationOperator_le {n : ℕ} (hn : 0 < n)
    (mu : GMMEuclidean n) :
    ‖gaussianMixturePopulationOperator mu‖ ≤ 1 + ‖mu‖ ^ 2 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  calc
    ‖gaussianMixturePopulationOperator mu‖ ≤
        ‖ContinuousLinearMap.id ℝ (GMMEuclidean n)‖ +
          ‖InnerProductSpace.rankOne ℝ mu mu‖ := by
      exact norm_add_le _ _
    _ = 1 + ‖mu‖ ^ 2 := by
      simp [pow_two]

/-- Bounds norm gaussian mixture empirical operator by of error.

**Lean implementation helper.** -/
lemma norm_gaussianMixtureEmpiricalOperator_le_of_error {m n : ℕ}
    (hn : 0 < n) (mu : GMMEuclidean n) (X : Fin m → GMMEuclidean n)
    {eps : ℝ} (herror :
      ‖gaussianMixturePopulationOperator mu -
        gaussianMixtureEmpiricalOperator X‖ ≤ eps) :
    ‖gaussianMixtureEmpiricalOperator X‖ ≤ 1 + ‖mu‖ ^ 2 + eps := by
  let T := gaussianMixturePopulationOperator mu
  let S := gaussianMixtureEmpiricalOperator X
  have hrev : ‖S - T‖ = ‖T - S‖ := by
    rw [show S - T = -(T - S) by abel, norm_neg]
  calc
    ‖S‖ = ‖(S - T) + T‖ := by rw [sub_add_cancel]
    _ ≤ ‖S - T‖ + ‖T‖ := norm_add_le _ _
    _ ≤ eps + (1 + ‖mu‖ ^ 2) := by
      rw [hrev]
      gcongr
      exact norm_gaussianMixturePopulationOperator_le hn mu
    _ = 1 + ‖mu‖ ^ 2 + eps := by ring

/-- Empirical and population top directions are close modulo the eigenvector sign.

**Book Exercise 4.51.** -/
theorem exercise_4_51_davisKahan {m n : ℕ} (hn : 0 < n)
    {mu : GMMEuclidean n} (hmu : mu ≠ 0)
    (X : Fin m → GMMEuclidean n) {eps : ℝ} (heps : 0 ≤ eps)
    (herror : ‖gaussianMixturePopulationOperator mu -
        gaussianMixtureEmpiricalOperator X‖ ≤ eps) :
    ∃ theta : ℝ, (theta = 1 ∨ theta = -1) ∧
      ‖gaussianMixtureDirection mu -
          theta • gaussianMixtureSpectralVector hn X‖ ≤
        Real.sqrt 2 * (2 * eps / ‖mu‖ ^ 2) := by
  let T := gaussianMixturePopulationOperator mu
  let S := gaussianMixtureEmpiricalOperator X
  let hT := gaussianMixturePopulationOperator_isSelfAdjoint mu
  let hS := gaussianMixtureEmpiricalOperator_isSelfAdjoint X
  let hdim : Module.finrank ℝ (GMMEuclidean n) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  let i0 : Fin n := ⟨0, hn⟩
  let p := hT.isSymmetric.eigenvectorBasis hdim i0
  let v := hS.isSymmetric.eigenvectorBasis hdim i0
  let delta : ℝ := ‖mu‖ ^ 2
  have hdelta : 0 < delta := sq_pos_of_pos (norm_pos_iff.mpr hmu)
  have hgap : ∀ i : Fin n, i ≠ i0 →
      delta ≤ |hT.isSymmetric.eigenvalues hdim i0 -
        hT.isSymmetric.eigenvalues hdim i| := by
    intro i hi
    have h := gaussianMixture_populationEigengap hn hmu i (by
      simpa [i0] using hi)
    change |hT.isSymmetric.eigenvalues hdim i0 -
      hT.isSymmetric.eigenvalues hdim i| = ‖mu‖ ^ 2 at h
    rw [h]
  have hsqrt := davisKahan T S hT hS hdim i0 hdelta hgap
  have hsqrt' : Real.sqrt (1 - |inner ℝ p v| ^ 2) ≤
      2 * eps / delta := by
    calc
      Real.sqrt (1 - |inner ℝ p v| ^ 2)
          ≤ 2 * ‖T - S‖ / delta := by simpa [p, v] using hsqrt
      _ ≤ 2 * eps / delta := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left herror (by norm_num)) hdelta.le
  have hp : ‖p‖ = 1 := (hT.isSymmetric.eigenvectorBasis hdim).norm_eq_one i0
  have hv : ‖v‖ = 1 := (hS.isSymmetric.eigenvectorBasis hdim).norm_eq_one i0
  have hinner : |inner ℝ p v| ≤ 1 := by
    calc
      |inner ℝ p v| ≤ ‖p‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hp, hv]; norm_num
  have hnonneg : 0 ≤ 1 - |inner ℝ p v| ^ 2 := by
    have hsquare : |inner ℝ p v| ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hinner
    nlinarith
  have hR : 0 ≤ 2 * eps / delta := by positivity
  have hsin : 1 - |inner ℝ p v| ^ 2 ≤ (2 * eps / delta) ^ 2 := by
    rw [← Real.sq_sqrt hnonneg]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hR).2 hsqrt'
  obtain ⟨theta, htheta, hdist⟩ :=
    exercise_4_16_angle_sign_distance p v hp hv hR hsin
  obtain ⟨sigma, hsigma, hup⟩ :=
    gaussianMixture_topEigenvector_eq_sign_direction hn hmu
  change gaussianMixtureDirection mu = sigma • p at hup
  change ‖p - theta • v‖ ≤ Real.sqrt 2 * (2 * eps / delta) at hdist
  change ∃ tau : ℝ, (tau = 1 ∨ tau = -1) ∧
    ‖gaussianMixtureDirection mu - tau • v‖ ≤
      Real.sqrt 2 * (2 * eps / ‖mu‖ ^ 2)
  rcases hsigma with rfl | rfl <;> rcases htheta with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simpa [hup, delta] using hdist⟩
  · exact ⟨-1, Or.inr rfl, by simpa [hup, delta] using hdist⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [hup, neg_one_smul, neg_one_smul, sub_neg_eq_add]
      calc
        ‖-p + v‖ = ‖-(p - v)‖ := by
          congr 1
          abel
        _ = ‖p - v‖ := norm_neg _
        _ ≤ _ := by simpa [delta] using hdist⟩
  · exact ⟨1, Or.inl rfl, by
      rw [hup, neg_one_smul, one_smul]
      calc
        ‖-p - v‖ = ‖-(p + v)‖ := by
          congr 1
          abel
        _ = ‖p + v‖ := norm_neg _
        _ ≤ _ := by simpa [delta] using hdist⟩

/-! ### Concrete covariance concentration for the canonical sample -/

/-- The dimensionless relative covariance-error parameter obtained from the corresponding
theorem with the augmented-row bound `K = 4` and tail parameter `t = 4`.

**Lean implementation helper.** -/
def gaussianMixtureCovarianceScale (m n : ℕ) : ℝ :=
  let delta := twoSidedGramConstant *
    (Real.sqrt (((n + 1 : ℕ) : ℝ) / m) + 4 / Real.sqrt m)
  16 * max delta (delta ^ 2)

/-- The sample-covariance deviation exceeds the prescribed population-scaled threshold with probability at most `2e^{-16}`.

**Lean implementation helper.** -/
lemma gaussianMixture_covariance_tail_exact {m n : ℕ} [NeZero m]
    (mu : GMMEuclidean n) :
    gaussianMixtureSampleMeasure m n
      {w | gaussianMixtureCovarianceScale m n *
            HDP.matrixOpNorm (gaussianMixturePopulationMatrix mu) <
          HDP.matrixOpNorm
            (sampleCovarianceMatrix
                (fun i => gaussianMixturePoint mu w i) -
              gaussianMixturePopulationMatrix mu)} ≤
      ENNReal.ofReal (2 * Real.exp (-16)) := by
  letI : NeZero (n + 1) := ⟨by omega⟩
  let A : GaussianMixtureSample m n → Matrix (Fin m) (Fin (n + 1)) ℝ :=
    fun w => gaussianMixtureAugmentedMatrix w
  let B : Matrix (Fin n) (Fin (n + 1)) ℝ :=
    gaussianMixtureFactorMatrix mu
  have h := exercise_4_49_factorized
    (μ := gaussianMixtureSampleMeasure m n) A B
    gaussianMixtureAugmentedMatrix_aemeasurableRows
    gaussianMixtureAugmentedMatrix_subGaussianRows
    gaussianMixtureAugmentedMatrix_isotropicRows
    gaussianMixtureAugmentedMatrix_independentRows
    gaussianMixtureAugmentedMatrix_rowPsi2Finite
    (K := (4 : ℝ)) (by norm_num)
    gaussianMixtureAugmentedMatrix_rowPsi2Bound
    (t := (4 : ℝ)) (by norm_num)
  have hevent :
      {w | gaussianMixtureCovarianceScale m n *
            HDP.matrixOpNorm (gaussianMixturePopulationMatrix mu) <
          HDP.matrixOpNorm
            (sampleCovarianceMatrix
                (fun i => gaussianMixturePoint mu w i) -
              gaussianMixturePopulationMatrix mu)} =
      {w | (4 : ℝ) ^ 2 * max
              (twoSidedGramConstant *
                (Real.sqrt (((n + 1 : ℕ) : ℝ) / m) +
                  4 / Real.sqrt m))
              ((twoSidedGramConstant *
                (Real.sqrt (((n + 1 : ℕ) : ℝ) / m) +
                  4 / Real.sqrt m)) ^ 2) *
            HDP.matrixOpNorm (B * B.transpose) <
          HDP.matrixOpNorm
            (HDP.normalizedGram m (A w * B.transpose) -
              B * B.transpose)} := by
    ext w
    simp only [Set.mem_setOf_eq]
    rw [show B * B.transpose = gaussianMixturePopulationMatrix mu by
      simpa [B] using gaussianMixtureFactorMatrix_gram_eq_population mu]
    rw [show A w * B.transpose =
        dataMatrix (fun i => gaussianMixturePoint mu w i) by
      simpa [A, B] using
        (dataMatrix_gaussianMixturePoint_factorization mu w).symm]
    rw [← sampleCovarianceMatrix_eq_normalizedGram]
    simp [gaussianMixtureCovarianceScale]
    norm_num
  rw [hevent]
  convert h using 1
  all_goals norm_num

/-- Identifies matrix operator norm sub population with operator norm.

**Lean implementation helper.** -/
lemma matrixOpNorm_sub_population_eq_operatorNorm {m n : ℕ}
    (mu : GMMEuclidean n) (X : Fin m → GMMEuclidean n) :
    HDP.matrixOpNorm
        (gaussianMixturePopulationMatrix mu - sampleCovarianceMatrix X) =
      ‖gaussianMixturePopulationOperator mu -
        gaussianMixtureEmpiricalOperator X‖ := by
  rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
  rw [map_sub]
  change ‖(gaussianMixturePopulationMatrix mu).toEuclideanLin.toContinuousLinearMap -
      (sampleCovarianceMatrix X).toEuclideanLin.toContinuousLinearMap‖ = _
  rw [gaussianMixturePopulationMatrix_toOperator,
    gaussianMixtureEmpiricalOperator_eq_sampleCovariance]

/-! ### Gaussian margins and the number of intrinsically ambiguous points -/

/-- A point whose population-direction score has margin at most `‖mu‖/2`.

**Lean implementation helper.** -/
def gaussianMixtureMarginBadSet {m n : ℕ} (mu : GMMEuclidean n)
    (i : Fin m) : Set (GaussianMixtureSample m n) :=
  {w | gaussianMixtureLabel w i *
      inner ℝ (gaussianMixturePoint mu w i) (gaussianMixtureDirection mu) ≤
        ‖mu‖ / 2}

/-- Establishes measurability of the set gaussian mixture margin bad set.

**Lean implementation helper.** -/
lemma measurableSet_gaussianMixtureMarginBadSet {m n : ℕ}
    (mu : GMMEuclidean n) (i : Fin m) :
    MeasurableSet (gaussianMixtureMarginBadSet mu i) := by
  unfold gaussianMixtureMarginBadSet
  apply measurableSet_le
  · simp only [gaussianMixtureLabel, gaussianMixturePoint,
      gaussianMixtureNoise]
    fun_prop
  · fun_prop

/-- The real-valued indicator count used for Markov's inequality.

**Lean implementation helper.** -/
def gaussianMixtureMarginBadCount {m n : ℕ} (mu : GMMEuclidean n)
    (w : GaussianMixtureSample m n) : ℝ :=
  ∑ i : Fin m, (gaussianMixtureMarginBadSet mu i).indicator
    (fun _ => (1 : ℝ)) w

/-- Identifies gaussian mixture margin bad count with card.

**Lean implementation helper.** -/
lemma gaussianMixtureMarginBadCount_eq_card {m n : ℕ}
    (mu : GMMEuclidean n) (w : GaussianMixtureSample m n) :
    gaussianMixtureMarginBadCount mu w =
      ((Finset.univ.filter fun i =>
        gaussianMixtureLabel w i *
          inner ℝ (gaussianMixturePoint mu w i)
            (gaussianMixtureDirection mu) ≤ ‖mu‖ / 2).card : ℝ) := by
  classical
  simp only [gaussianMixtureMarginBadCount, Set.indicator_apply,
    gaussianMixtureMarginBadSet, Set.mem_setOf_eq]
  exact_mod_cast
    (Finset.sum_boole (fun i : Fin m =>
      gaussianMixtureLabel w i *
        inner ℝ (gaussianMixturePoint mu w i)
          (gaussianMixtureDirection mu) ≤ ‖mu‖ / 2) Finset.univ)

/-- Identifies the probability law described by has law gaussian mixture noise inner.

**Lean implementation helper.** -/
private lemma hasLaw_gaussianMixtureNoise_inner {m n : ℕ}
    (i : Fin m) (u : GMMEuclidean n) :
    HasLaw
      (fun w : GaussianMixtureSample m n =>
        inner ℝ (gaussianMixtureNoise w i) u)
      (gaussianReal 0 ⟨‖u‖ ^ 2, sq_nonneg ‖u‖⟩)
      (gaussianMixtureSampleMeasure m n) := by
  let eval : GaussianMixtureSample m n → GaussianMixtureAtom n := fun w => w i
  have heval : HasLaw eval (gaussianMixtureAtomMeasure n)
      (gaussianMixtureSampleMeasure m n) :=
    (measurePreserving_eval
      (fun _ : Fin m => gaussianMixtureAtomMeasure n) i).hasLaw
  have h := (hasLaw_gaussianMixtureAtom_noise_inner u).comp heval
  simpa [eval, Function.comp_def, gaussianMixtureNoise] using h

/-- A Gaussian-mixture margin error forces the noise projection onto the mixture direction to have magnitude at least `‖μ‖/2`.

**Lean implementation helper.** -/
private lemma marginBad_imp_noise_large {m n : ℕ}
    {mu : GMMEuclidean n} (hmu : mu ≠ 0)
    (w : GaussianMixtureSample m n) (i : Fin m)
    (hlabel : gaussianMixtureLabel w i = 1 ∨
      gaussianMixtureLabel w i = -1)
    (hbad : w ∈ gaussianMixtureMarginBadSet mu i) :
    ‖mu‖ / 2 ≤
      |inner ℝ (gaussianMixtureNoise w i)
        (gaussianMixtureDirection mu)| := by
  have hinner := inner_mu_gaussianMixtureDirection hmu
  change gaussianMixtureLabel w i *
      inner ℝ (gaussianMixturePoint mu w i) (gaussianMixtureDirection mu) ≤
        ‖mu‖ / 2 at hbad
  rcases hlabel with hlabel | hlabel
  · rw [hlabel] at hbad
    simp only [gaussianMixturePoint, inner_add_left, inner_smul_left,
      one_mul, starRingEnd_apply, star_trivial] at hbad
    rw [hlabel, hinner] at hbad
    nlinarith [neg_le_abs
      (inner ℝ (gaussianMixtureNoise w i) (gaussianMixtureDirection mu))]
  · rw [hlabel] at hbad
    simp only [gaussianMixturePoint, inner_add_left, inner_smul_left,
      neg_mul, one_mul, starRingEnd_apply, star_trivial] at hbad
    rw [hlabel, hinner] at hbad
    nlinarith [le_abs_self
      (inner ℝ (gaussianMixtureNoise w i) (gaussianMixtureDirection mu))]

/-- A fixed sample point has bad mixture margin with probability at most `2 exp(-(3/32)‖μ‖²)`.

**Lean implementation helper.** -/
lemma gaussianMixture_marginBad_measure_le {m n : ℕ}
    {mu : GMMEuclidean n} (hmu : mu ≠ 0) (i : Fin m) :
    gaussianMixtureSampleMeasure m n (gaussianMixtureMarginBadSet mu i) ≤
      ENNReal.ofReal (2 * Real.exp (-(3 / 32 : ℝ) * ‖mu‖ ^ 2)) := by
  let u := gaussianMixtureDirection mu
  have hu : ‖u‖ = 1 := norm_gaussianMixtureDirection hmu
  have hlaw := hasLaw_gaussianMixtureNoise_inner i u
  have hsub : HDP.SubGaussian
      (fun w : GaussianMixtureSample m n =>
        inner ℝ (gaussianMixtureNoise w i) u)
      (gaussianMixtureSampleMeasure m n) :=
    subGaussian_of_centeredGaussianLaw ‖u‖ hlaw
  have hpsi := HDP.psi2Norm_gaussian ‖u‖ hlaw
  have htail := hsub.tail_bound
    hlaw.aemeasurable
    (t := ‖mu‖ / 2) (by positivity)
  have hmono : gaussianMixtureSampleMeasure m n
      (gaussianMixtureMarginBadSet mu i) ≤
      gaussianMixtureSampleMeasure m n
        {w | ‖mu‖ / 2 ≤
          |inner ℝ (gaussianMixtureNoise w i) u|} := by
    apply measure_mono_ae
    filter_upwards [(isRademacher_gaussianMixtureLabel i).ae_mem]
      with w hw
    exact fun hbad => marginBad_imp_noise_large hmu w i hw hbad
  calc
    gaussianMixtureSampleMeasure m n (gaussianMixtureMarginBadSet mu i)
        ≤ gaussianMixtureSampleMeasure m n
            {w | ‖mu‖ / 2 ≤
              |inner ℝ (gaussianMixtureNoise w i) u|} := hmono
    _ ≤ ENNReal.ofReal
        (2 * Real.exp (-(‖mu‖ / 2) ^ 2 /
          (HDP.psi2Norm
            (fun w : GaussianMixtureSample m n =>
              inner ℝ (gaussianMixtureNoise w i) u)
            (gaussianMixtureSampleMeasure m n)) ^ 2)) := htail
    _ = ENNReal.ofReal (2 * Real.exp (-(3 / 32 : ℝ) * ‖mu‖ ^ 2)) := by
      rw [hpsi, hu]
      congr 2
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3)]
      ring_nf

/-- Bounds gaussian mixture margin bad measure by exp16.

**Lean implementation helper.** -/
lemma gaussianMixture_marginBad_measure_le_exp16 {m n : ℕ}
    {mu : GMMEuclidean n} (hmu20 : 20 ≤ ‖mu‖) (i : Fin m) :
    gaussianMixtureSampleMeasure m n (gaussianMixtureMarginBadSet mu i) ≤
      ENNReal.ofReal (2 * Real.exp (-16)) := by
  have hmu : mu ≠ 0 := by
    intro h
    subst mu
    norm_num at hmu20
  have htail := gaussianMixture_marginBad_measure_le hmu i
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (‖mu‖ - 20)]

/-- Shows that gaussian mixture margin bad count is integrable.

**Lean implementation helper.** -/
lemma gaussianMixtureMarginBadCount_integrable {m n : ℕ}
    (mu : GMMEuclidean n) :
    Integrable (gaussianMixtureMarginBadCount mu)
      (gaussianMixtureSampleMeasure m n) := by
  classical
  unfold gaussianMixtureMarginBadCount
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_gaussianMixtureMarginBadSet mu i)

/-- When `‖mu‖ ≥ 20`, the expected Gaussian-mixture bad-margin count is at most `m * 2 * exp (-16)`.

**Lean implementation helper.** -/
lemma integral_gaussianMixtureMarginBadCount_le {m n : ℕ}
    {mu : GMMEuclidean n} (hmu20 : 20 ≤ ‖mu‖) :
    ∫ w, gaussianMixtureMarginBadCount mu w
        ∂gaussianMixtureSampleMeasure m n ≤
      (m : ℝ) * (2 * Real.exp (-16)) := by
  classical
  change (∫ w, ∑ i : Fin m,
      (gaussianMixtureMarginBadSet mu i).indicator
        (fun _ => (1 : ℝ)) w ∂gaussianMixtureSampleMeasure m n) ≤ _
  rw [integral_finsetSum]
  · calc
      ∑ i : Fin m,
          ∫ w, (gaussianMixtureMarginBadSet mu i).indicator
            (fun _ => (1 : ℝ)) w ∂gaussianMixtureSampleMeasure m n =
          ∑ i : Fin m,
            (gaussianMixtureSampleMeasure m n).real
              (gaussianMixtureMarginBadSet mu i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_indicator_one
          (measurableSet_gaussianMixtureMarginBadSet mu i)
      _ ≤ ∑ _i : Fin m, 2 * Real.exp (-16) := by
        apply Finset.sum_le_sum
        intro i hi
        have htail := gaussianMixture_marginBad_measure_le_exp16 hmu20 i
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
        change ((gaussianMixtureSampleMeasure m n)
          (gaussianMixtureMarginBadSet mu i)).toReal ≤ _
        calc
          ((gaussianMixtureSampleMeasure m n)
              (gaussianMixtureMarginBadSet mu i)).toReal ≤
              (ENNReal.ofReal (2 * Real.exp (-16))).toReal := hreal
          _ = 2 * Real.exp (-16) :=
            ENNReal.toReal_ofReal (by positivity)
      _ = (m : ℝ) * (2 * Real.exp (-16)) := by
        simp
  · intro i hi
    exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_gaussianMixtureMarginBadSet mu i)

/-- The event that more than a `1/400` fraction have small population margin.

**Lean implementation helper.** -/
def gaussianMixtureMarginCountBadSet {m n : ℕ} (mu : GMMEuclidean n) :
    Set (GaussianMixtureSample m n) :=
  {w | (m : ℝ) / 400 ≤ gaussianMixtureMarginBadCount mu w}

/-- Establishes measurability of the set gaussian mixture margin count bad set.

**Lean implementation helper.** -/
lemma measurableSet_gaussianMixtureMarginCountBadSet {m n : ℕ}
    (mu : GMMEuclidean n) :
    MeasurableSet (gaussianMixtureMarginCountBadSet (m := m) mu) := by
  apply measurableSet_le measurable_const
  unfold gaussianMixtureMarginBadCount
  exact Finset.measurable_sum Finset.univ fun i _ =>
    measurable_const.indicator (measurableSet_gaussianMixtureMarginBadSet mu i)

/-- The event that too many sample points have bad margin has probability at most `400·2e^{-16}`.

**Lean implementation helper.** -/
lemma gaussianMixture_marginCountBad_measure_le {m n : ℕ}
    (hm : 0 < m) {mu : GMMEuclidean n} (hmu20 : 20 ≤ ‖mu‖) :
    gaussianMixtureSampleMeasure m n
        (gaussianMixtureMarginCountBadSet mu) ≤
      ENNReal.ofReal (400 * (2 * Real.exp (-16))) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < (m : ℝ) / 400 := by positivity
  have hmark := HDP.Chapter1.markov_inequality
    (μ := gaussianMixtureSampleMeasure m n)
    (X := gaussianMixtureMarginBadCount mu)
    (Filter.Eventually.of_forall fun w => by
      rw [gaussianMixtureMarginBadCount_eq_card]
      positivity)
    (gaussianMixtureMarginBadCount_integrable mu) ht
  have hreal : (gaussianMixtureSampleMeasure m n).real
      (gaussianMixtureMarginCountBadSet mu) ≤
      400 * (2 * Real.exp (-16)) := by
    calc
      (gaussianMixtureSampleMeasure m n).real
          (gaussianMixtureMarginCountBadSet mu) ≤
          (∫ w, gaussianMixtureMarginBadCount mu w
            ∂gaussianMixtureSampleMeasure m n) / ((m : ℝ) / 400) := by
        simpa [gaussianMixtureMarginCountBadSet] using hmark
      _ ≤ ((m : ℝ) * (2 * Real.exp (-16))) / ((m : ℝ) / 400) :=
        div_le_div_of_nonneg_right
          (integral_gaussianMixtureMarginBadCount_le hmu20) ht.le
      _ = 400 * (2 * Real.exp (-16)) := by
        field_simp
  rw [← MeasureTheory.ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### Explicit sample size and the final high-probability guarantee -/

/-- A concrete absolute sample-size constant. No attempt is made to optimize it: the source only
asserts the existence of an absolute constant.

**Lean implementation helper.** -/
def gaussianMixtureSampleConstant : ℕ := 10000000000000000

/-- Under the concrete sample-size hypothesis, the relative covariance error from the two-sided
subgaussian theorem is at most `10⁻³`.

**Lean implementation helper.** -/
lemma gaussianMixtureCovarianceScale_le {m n : ℕ} (hn : 0 < n)
    (hsize : gaussianMixtureSampleConstant * n ≤ m) :
    gaussianMixtureCovarianceScale m n ≤ (1 : ℝ) / 1000 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 0 < m := by
    have hC : 0 < gaussianMixtureSampleConstant := by
      norm_num [gaussianMixtureSampleConstant]
    exact lt_of_lt_of_le (Nat.mul_pos hC hn) hsize
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsizeR :
      (10000000000000000 : ℝ) * (n : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hsize
  have hmC : (10000000000000000 : ℝ) ≤ (m : ℝ) := by
    nlinarith
  have hratioN : (((n + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
      (1 : ℝ) / 5000000000000000 := by
    rw [div_le_iff₀ hmR]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hsqrtN : Real.sqrt (((n + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
      (1 : ℝ) / 10000000 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · calc
        (((n + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
            (1 : ℝ) / 5000000000000000 := hratioN
        _ ≤ ((1 : ℝ) / 10000000) ^ 2 := by norm_num
  have hsqrtM : (100000000 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [Real.le_sqrt (by norm_num)] <;> nlinarith
  have hdivM : (4 : ℝ) / Real.sqrt (m : ℝ) ≤ 4 / 100000000 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrtM
  let delta : ℝ := twoSidedGramConstant *
    (Real.sqrt (((n + 1 : ℕ) : ℝ) / m) + 4 / Real.sqrt m)
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact mul_nonneg twoSidedGramConstant_pos.le
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hdelta : delta ≤ (7 : ℝ) / 500000 := by
    dsimp [delta, twoSidedGramConstant]
    nlinarith
  have hdeltaSq : delta ^ 2 ≤ delta := by
    nlinarith
  rw [gaussianMixtureCovarianceScale]
  change 16 * max delta (delta ^ 2) ≤ (1 : ℝ) / 1000
  rw [max_eq_left hdeltaSq]
  nlinarith

/-- The matrix operator norm of the Gaussian-mixture population matrix equals the norm of its associated continuous operator.

**Lean implementation helper.** -/
lemma matrixOpNorm_gaussianMixturePopulationMatrix {n : ℕ}
    (mu : GMMEuclidean n) :
    HDP.matrixOpNorm (gaussianMixturePopulationMatrix mu) =
      ‖gaussianMixturePopulationOperator mu‖ := by
  rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
  exact congrArg norm (gaussianMixturePopulationMatrix_toOperator mu)

/-- The actual covariance-deviation event for the canonical sample.

**Lean implementation helper.** -/
def gaussianMixtureCovarianceBadSet {m n : ℕ} (mu : GMMEuclidean n) :
    Set (GaussianMixtureSample m n) :=
  {w | gaussianMixtureCovarianceScale m n *
          HDP.matrixOpNorm (gaussianMixturePopulationMatrix mu) <
        HDP.matrixOpNorm
          (sampleCovarianceMatrix
              (fun i => gaussianMixturePoint mu w i) -
            gaussianMixturePopulationMatrix mu)}

/-- The Gaussian-mixture covariance failure event has probability at most `2e^{-16}`.

**Lean implementation helper.** -/
lemma gaussianMixture_covarianceBad_measure_le {m n : ℕ} [NeZero m]
    (mu : GMMEuclidean n) :
    gaussianMixtureSampleMeasure m n
        (gaussianMixtureCovarianceBadSet mu) ≤
      ENNReal.ofReal (2 * Real.exp (-16)) := by
  simpa [gaussianMixtureCovarianceBadSet] using
    gaussianMixture_covariance_tail_exact (m := m) mu

/-- Bounds covariance error by of not mem bad.

**Lean implementation helper.** -/
lemma covariance_error_le_of_not_mem_bad {m n : ℕ}
    (mu : GMMEuclidean n) (w : GaussianMixtureSample m n)
    (hw : w ∉ gaussianMixtureCovarianceBadSet mu) :
    ‖gaussianMixturePopulationOperator mu -
        gaussianMixtureEmpiricalOperator
          (fun i => gaussianMixturePoint mu w i)‖ ≤
      gaussianMixtureCovarianceScale m n *
        ‖gaussianMixturePopulationOperator mu‖ := by
  have hmatrix :
      HDP.matrixOpNorm
          (sampleCovarianceMatrix
              (fun i => gaussianMixturePoint mu w i) -
            gaussianMixturePopulationMatrix mu) ≤
        gaussianMixtureCovarianceScale m n *
          HDP.matrixOpNorm (gaussianMixturePopulationMatrix mu) := by
    simpa [gaussianMixtureCovarianceBadSet] using (not_lt.mp hw)
  have hrev :
      HDP.matrixOpNorm
          (sampleCovarianceMatrix
              (fun i => gaussianMixturePoint mu w i) -
            gaussianMixturePopulationMatrix mu) =
        HDP.matrixOpNorm
          (gaussianMixturePopulationMatrix mu -
            sampleCovarianceMatrix
              (fun i => gaussianMixturePoint mu w i)) := by
    rw [show sampleCovarianceMatrix
          (fun i => gaussianMixturePoint mu w i) -
          gaussianMixturePopulationMatrix mu =
        -(gaussianMixturePopulationMatrix mu -
          sampleCovarianceMatrix
            (fun i => gaussianMixturePoint mu w i)) by abel,
      ]
    simp only [HDP.matrixOpNorm, Matrix.l2_opNorm_def, map_neg, norm_neg]
  rw [hrev, matrixOpNorm_sub_population_eq_operatorNorm,
    matrixOpNorm_gaussianMixturePopulationMatrix] at hmatrix
  exact hmatrix

/-- Null exceptional set on which at least one product-coordinate label is not one of the two
Rademacher values.

**Lean implementation helper.** -/
def gaussianMixtureInvalidLabelSet {m n : ℕ} :
    Set (GaussianMixtureSample m n) :=
  ⋃ i : Fin m, {w | ¬ (gaussianMixtureLabel w i = 1 ∨
    gaussianMixtureLabel w i = -1)}

/-- Establishes measurability of the set gaussian mixture invalid label set.

**Lean implementation helper.** -/
lemma measurableSet_gaussianMixtureInvalidLabelSet {m n : ℕ} :
    MeasurableSet (gaussianMixtureInvalidLabelSet (m := m) (n := n)) := by
  unfold gaussianMixtureInvalidLabelSet
  apply MeasurableSet.iUnion
  intro i
  have hlabel : Measurable
      (fun w : GaussianMixtureSample m n => gaussianMixtureLabel w i) := by
    exact measurable_fst.comp (measurable_pi_apply i)
  rw [show {w : GaussianMixtureSample m n |
      ¬ (gaussianMixtureLabel w i = 1 ∨ gaussianMixtureLabel w i = -1)} =
      ({w | gaussianMixtureLabel w i = 1} ∪
        {w | gaussianMixtureLabel w i = -1})ᶜ by
    ext w
    simp]
  exact ((measurableSet_eq_fun hlabel measurable_const).union
    (measurableSet_eq_fun hlabel measurable_const)).compl

/-- Invalid Gaussian-mixture labels form a null event under the product sample measure.

**Lean implementation helper.** -/
lemma gaussianMixture_invalidLabel_measure_zero {m n : ℕ} :
    gaussianMixtureSampleMeasure m n
      (gaussianMixtureInvalidLabelSet (m := m) (n := n)) = 0 := by
  unfold gaussianMixtureInvalidLabelSet
  apply measure_iUnion_null
  intro i
  exact (MeasureTheory.ae_iff.mp
    (isRademacher_gaussianMixtureLabel (m := m) (n := n) i).ae_mem)

/-- Derives labels valid from not mem invalid.

**Lean implementation helper.** -/
lemma labels_valid_of_not_mem_invalid {m n : ℕ}
    (w : GaussianMixtureSample m n)
    (hw : w ∉ gaussianMixtureInvalidLabelSet) :
    ∀ i, gaussianMixtureLabel w i = 1 ∨
      gaussianMixtureLabel w i = -1 := by
  intro i
  by_contra hi
  exact hw (Set.mem_iUnion_of_mem i hi)

/-- On the covariance, margin, and label good events, the concrete spectral classifier makes at
most a one-percent fraction of errors. The estimate is deterministic and therefore remains valid
for the data-dependent empirical eigenvector.

**Lean implementation helper.** -/
theorem gaussianMixture_classification_le_on_good_events {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {mu : GMMEuclidean n}
    (hmu20 : 20 ≤ ‖mu‖) (w : GaussianMixtureSample m n)
    (hcov : ‖gaussianMixturePopulationOperator mu -
        gaussianMixtureEmpiricalOperator
          (fun i => gaussianMixturePoint mu w i)‖ ≤
      (1 : ℝ) / 1000 * (1 + ‖mu‖ ^ 2))
    (hmargin : gaussianMixtureMarginBadCount mu w < (m : ℝ) / 400)
    (hlabels : ∀ i, gaussianMixtureLabel w i = 1 ∨
      gaussianMixtureLabel w i = -1) :
    (gaussianMixtureMisclassified hn mu w : ℝ) ≤ (m : ℝ) / 100 := by
  let X : Fin m → GMMEuclidean n := fun i => gaussianMixturePoint mu w i
  let truth : Fin m → ℝ := fun i => gaussianMixtureLabel w i
  let u : GMMEuclidean n := gaussianMixtureDirection mu
  let v : GMMEuclidean n := gaussianMixtureSpectralVector hn X
  let r : ℝ := ‖mu‖
  let eps : ℝ := (1 : ℝ) / 1000 * (1 + r ^ 2)
  have hmu : mu ≠ 0 := by
    intro h
    subst mu
    norm_num at hmu20
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr hmu
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr400 : (400 : ℝ) ≤ r ^ 2 := by
    dsimp [r]
    nlinarith [sq_nonneg (‖mu‖ - 20)]
  have heps0 : 0 ≤ eps := by
    dsimp [eps]
    positivity
  have hcov' : ‖gaussianMixturePopulationOperator mu -
        gaussianMixtureEmpiricalOperator X‖ ≤ eps := by
    simpa [X, eps, r] using hcov
  obtain ⟨theta, htheta, hdist⟩ :=
    exercise_4_51_davisKahan hn hmu X heps0 hcov'
  have hdist' : ‖theta • v - u‖ ≤
      Real.sqrt 2 * (2 * eps / r ^ 2) := by
    rw [norm_sub_rev]
    simpa [u, v, r] using hdist
  have hraw := deterministic_misclassifiedUpToSign_le_opNorm
    hm X truth (by simpa [truth] using hlabels) u v htheta hr
  have hraw' : (gaussianMixtureMisclassified hn mu w : ℝ) ≤
      (gaussianMixtureMarginBadCount mu w) +
        (4 / r ^ 2) * (m : ℝ) *
          ‖gaussianMixtureEmpiricalOperator X‖ * ‖theta • v - u‖ ^ 2 := by
    dsimp only at hraw
    have hbadcard :
        ((Finset.univ.filter fun i =>
          truth i * inner ℝ (X i) u ≤ r / 2).card : ℝ) =
          gaussianMixtureMarginBadCount mu w := by
      simpa [X, truth, u, r] using
        (gaussianMixtureMarginBadCount_eq_card mu w).symm
    rw [hbadcard] at hraw
    change (HDP.misclassifiedUpToSign
      (fun i => gaussianMixtureLabel w i)
      (fun i => inner ℝ (gaussianMixturePoint mu w i)
        (gaussianMixtureSpectralVector hn
          (fun j => gaussianMixturePoint mu w j))) : ℝ) ≤ _
    simpa [X, truth, u, v, r] using hraw
  have hepsScaled : eps ≤ (401 : ℝ) / 400000 * r ^ 2 := by
    dsimp [eps]
    nlinarith
  have hemp : ‖gaussianMixtureEmpiricalOperator X‖ ≤
      1 + r ^ 2 + eps := by
    simpa [r] using
      norm_gaussianMixtureEmpiricalOperator_le_of_error hn mu X hcov'
  have hempScaled : ‖gaussianMixtureEmpiricalOperator X‖ ≤
      (201 : ℝ) / 200 * r ^ 2 := by
    nlinarith
  have hsqrtTwo : Real.sqrt 2 ≤ (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hfrac : 2 * eps / r ^ 2 ≤ (401 : ℝ) / 200000 := by
    apply (div_le_iff₀ hr2).2
    nlinarith
  have hfrac0 : 0 ≤ 2 * eps / r ^ 2 := by positivity
  have hdistConst : ‖theta • v - u‖ ≤ (401 : ℝ) / 100000 := by
    calc
      ‖theta • v - u‖ ≤ Real.sqrt 2 * (2 * eps / r ^ 2) := hdist'
      _ ≤ 2 * ((401 : ℝ) / 200000) :=
        mul_le_mul hsqrtTwo hfrac hfrac0 (by positivity)
      _ = (401 : ℝ) / 100000 := by norm_num
  have hdistSq : ‖theta • v - u‖ ^ 2 ≤
      ((401 : ℝ) / 100000) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hdistConst
  have hproduct : ‖gaussianMixtureEmpiricalOperator X‖ *
        ‖theta • v - u‖ ^ 2 ≤
      ((201 : ℝ) / 200 * r ^ 2) *
        ((401 : ℝ) / 100000) ^ 2 := by
    exact mul_le_mul hempScaled hdistSq (sq_nonneg _) (by positivity)
  have hcoefficient : (4 / r ^ 2) *
        ‖gaussianMixtureEmpiricalOperator X‖ *
          ‖theta • v - u‖ ^ 2 ≤ (1 : ℝ) / 1000 := by
    calc
      (4 / r ^ 2) * ‖gaussianMixtureEmpiricalOperator X‖ *
            ‖theta • v - u‖ ^ 2 =
          (4 / r ^ 2) *
            (‖gaussianMixtureEmpiricalOperator X‖ *
              ‖theta • v - u‖ ^ 2) := by ring
      _ ≤ (4 / r ^ 2) *
          (((201 : ℝ) / 200 * r ^ 2) *
            ((401 : ℝ) / 100000) ^ 2) := by
        gcongr
      _ = 4 * ((201 : ℝ) / 200) *
          ((401 : ℝ) / 100000) ^ 2 := by
        field_simp [hr2.ne']
      _ ≤ (1 : ℝ) / 1000 := by norm_num
  have herrorTerm :
      (4 / r ^ 2) * (m : ℝ) *
          ‖gaussianMixtureEmpiricalOperator X‖ * ‖theta • v - u‖ ^ 2 ≤
        (m : ℝ) / 1000 := by
    have hmR : (0 : ℝ) ≤ m := by positivity
    calc
      (4 / r ^ 2) * (m : ℝ) *
            ‖gaussianMixtureEmpiricalOperator X‖ * ‖theta • v - u‖ ^ 2 =
          (m : ℝ) * ((4 / r ^ 2) *
            ‖gaussianMixtureEmpiricalOperator X‖ *
              ‖theta • v - u‖ ^ 2) := by ring
      _ ≤ (m : ℝ) * ((1 : ℝ) / 1000) :=
        mul_le_mul_of_nonneg_left hcoefficient hmR
      _ = (m : ℝ) / 1000 := by ring
  calc
    (gaussianMixtureMisclassified hn mu w : ℝ) ≤
        gaussianMixtureMarginBadCount mu w +
          (4 / r ^ 2) * (m : ℝ) *
            ‖gaussianMixtureEmpiricalOperator X‖ *
              ‖theta • v - u‖ ^ 2 := hraw'
    _ ≤ (m : ℝ) / 400 + (m : ℝ) / 1000 := by
      exact add_le_add (le_of_lt hmargin) herrorTerm
    _ ≤ (m : ℝ) / 100 := by
      have hmR : (0 : ℝ) ≤ m := by positivity
      nlinarith

/-- The covariance and margin-count failure bounds sum to at most `1/100`.

**Lean implementation helper.** -/
private lemma gaussianMixture_exp16_numeric :
    2 * Real.exp (-16) + 400 * (2 * Real.exp (-16)) ≤
      (1 : ℝ) / 100 := by
  have hbase : (27 : ℝ) / 10 < Real.exp 1 :=
    (by norm_num : (27 : ℝ) / 10 < 2.7182818283).trans
      Real.exp_one_gt_d9
  have hpow : ((27 : ℝ) / 10) ^ 16 < (Real.exp 1) ^ 16 :=
    pow_lt_pow_left₀ hbase (by norm_num) (by norm_num)
  have hexp : (100000 : ℝ) < Real.exp 16 := by
    rw [show (16 : ℝ) = (16 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact (by norm_num : (100000 : ℝ) < ((27 : ℝ) / 10) ^ 16).trans hpow
  have hneg : Real.exp (-16) < (1 : ℝ) / 100000 := by
    rw [Real.exp_neg]
    rw [one_div]
    exact (inv_lt_inv₀ (by positivity) (by norm_num)).2 hexp
  nlinarith [Real.exp_pos (-16)]

/-- The direct (possibly outer-measurable) failure event of the source's spectral classifier.

**Lean implementation helper.** -/
def gaussianMixtureClassificationFailureSet {m n : ℕ} (hn : 0 < n)
    (mu : GMMEuclidean n) : Set (GaussianMixtureSample m n) :=
  {w | (m : ℝ) / 100 < (gaussianMixtureMisclassified hn mu w : ℝ)}

/-- For the canonical labelled two-component spherical Gaussian mixture, the empirical leading
eigenvector classifier recovers all but one percent of the labels, up to the unavoidable global
sign, with probability at least `0.99`. The stated sample-size constant is explicit and
absolute.

**Book Theorem 4.7.5.** -/
theorem theorem_4_7_5 {m n : ℕ} (hn : 0 < n)
    {mu : GMMEuclidean n} (hmu20 : 20 ≤ ‖mu‖)
    (hsize : gaussianMixtureSampleConstant * n ≤ m) :
    gaussianMixtureSampleMeasure m n
        (gaussianMixtureClassificationFailureSet hn mu) ≤
      (1 : ℝ≥0∞) / 100 := by
  have hm : 0 < m := by
    have hC : 0 < gaussianMixtureSampleConstant := by
      norm_num [gaussianMixtureSampleConstant]
    exact lt_of_lt_of_le (Nat.mul_pos hC hn) hsize
  letI : NeZero m := ⟨hm.ne'⟩
  let C : Set (GaussianMixtureSample m n) :=
    gaussianMixtureCovarianceBadSet mu
  let M : Set (GaussianMixtureSample m n) :=
    gaussianMixtureMarginCountBadSet mu
  let L : Set (GaussianMixtureSample m n) :=
    gaussianMixtureInvalidLabelSet
  have hscale0 : 0 ≤ gaussianMixtureCovarianceScale m n := by
    simp only [gaussianMixtureCovarianceScale]
    positivity [twoSidedGramConstant_pos]
  have hscale := gaussianMixtureCovarianceScale_le hn hsize
  have hsubset : gaussianMixtureClassificationFailureSet hn mu ⊆
      C ∪ (M ∪ L) := by
    intro w hw
    by_contra hwUnion
    have hgood : w ∉ C ∧ w ∉ M ∧ w ∉ L := by
      simpa only [Set.mem_union, not_or] using hwUnion
    have herr0 := covariance_error_le_of_not_mem_bad mu w (by
      simpa [C] using hgood.1)
    have hpop := norm_gaussianMixturePopulationOperator_le hn mu
    have herr : ‖gaussianMixturePopulationOperator mu -
          gaussianMixtureEmpiricalOperator
            (fun i => gaussianMixturePoint mu w i)‖ ≤
        (1 : ℝ) / 1000 * (1 + ‖mu‖ ^ 2) := by
      calc
        _ ≤ gaussianMixtureCovarianceScale m n *
              ‖gaussianMixturePopulationOperator mu‖ := herr0
        _ ≤ ((1 : ℝ) / 1000) * (1 + ‖mu‖ ^ 2) := by
          exact mul_le_mul hscale hpop (norm_nonneg _) (by norm_num)
    have hmargin : gaussianMixtureMarginBadCount mu w < (m : ℝ) / 400 := by
      have hnot : w ∉ gaussianMixtureMarginCountBadSet mu := by
        simpa [M] using hgood.2.1
      exact lt_of_not_ge (by
        simpa [gaussianMixtureMarginCountBadSet] using hnot)
    have hlabels : ∀ i, gaussianMixtureLabel w i = 1 ∨
        gaussianMixtureLabel w i = -1 :=
      labels_valid_of_not_mem_invalid w (by simpa [L] using hgood.2.2)
    have hclass := gaussianMixture_classification_le_on_good_events
      hm hn hmu20 w herr hmargin hlabels
    exact (not_lt_of_ge hclass) hw
  have hC : gaussianMixtureSampleMeasure m n C ≤
      ENNReal.ofReal (2 * Real.exp (-16)) := by
    simpa [C] using gaussianMixture_covarianceBad_measure_le
      (m := m) mu
  have hM : gaussianMixtureSampleMeasure m n M ≤
      ENNReal.ofReal (400 * (2 * Real.exp (-16))) := by
    simpa [M] using gaussianMixture_marginCountBad_measure_le hm hmu20
  have hL : gaussianMixtureSampleMeasure m n L = 0 := by
    simpa [L] using
      (gaussianMixture_invalidLabel_measure_zero (m := m) (n := n))
  calc
    gaussianMixtureSampleMeasure m n
        (gaussianMixtureClassificationFailureSet hn mu) ≤
        gaussianMixtureSampleMeasure m n (C ∪ (M ∪ L)) :=
      measure_mono hsubset
    _ ≤ gaussianMixtureSampleMeasure m n C +
        gaussianMixtureSampleMeasure m n (M ∪ L) :=
      measure_union_le C (M ∪ L)
    _ ≤ gaussianMixtureSampleMeasure m n C +
        (gaussianMixtureSampleMeasure m n M +
          gaussianMixtureSampleMeasure m n L) := by
      gcongr
      exact measure_union_le M L
    _ ≤ ENNReal.ofReal (2 * Real.exp (-16)) +
        (ENNReal.ofReal (400 * (2 * Real.exp (-16))) + 0) := by
      exact add_le_add hC (add_le_add hM hL.le)
    _ = ENNReal.ofReal
        (2 * Real.exp (-16) + 400 * (2 * Real.exp (-16))) := by
      rw [add_zero, ENNReal.ofReal_add]
      · positivity
      · positivity
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 100) :=
      ENNReal.ofReal_le_ofReal gaussianMixture_exp16_numeric
    _ = (1 : ℝ≥0∞) / 100 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

/-- The exercise's moment, eigengap, Davis--Kahan, and aggregate-error steps are assembled by
`theorem_4_7_5` into the concrete high-probability clustering conclusion.

**Book Theorem 4.7.5.** -/
theorem exercise_4_51 {m n : ℕ} (hn : 0 < n)
    {mu : GMMEuclidean n} (hmu20 : 20 ≤ ‖mu‖)
    (hsize : gaussianMixtureSampleConstant * n ≤ m) :
    gaussianMixtureSampleMeasure m n
        (gaussianMixtureClassificationFailureSet hn mu) ≤
      (1 : ℝ≥0∞) / 100 :=
  theorem_4_7_5 hn hmu20 hsize






end

end HDP.Chapter4

end Source_19_GaussianMixtureClustering
