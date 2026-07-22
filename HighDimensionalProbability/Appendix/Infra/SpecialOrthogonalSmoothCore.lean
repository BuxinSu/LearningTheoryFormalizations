import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalAveraging
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSubgroup
import HighDimensionalProbability.Prelude.GaussianMatrix
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Ambient and tangent gradients on the special orthogonal group

This file gives a concrete gradient for restrictions of Euclidean `C¹`
functions to `SO(n)`.  The ambient derivative is identified with a matrix
using the Riesz isometry.  After translating it to the identity by `Uᵀ`, its
skew projection is the right-trivialized tangent gradient.

The normalization is chosen so that differentiation in the elementary
direction `U * skewGenerator i j` gives twice the `(i,j)` entry of the
tangent gradient.  Its squared Frobenius energy is bounded by the squared
operator norm of the ambient derivative.
-/

open Matrix
open scoped BigOperators RealInnerProductSpace

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

/-- Euclidean space obtained by vectorizing an `n × n` real matrix. -/
abbrev FrobeniusEuclidean (n : ℕ) :=
  EuclideanSpace ℝ (Fin n × Fin n)

/-- Vectorization preserves the Frobenius inner product. -/
lemma inner_gaussianMatrixVectorize {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    inner ℝ (HDP.gaussianMatrixVectorize A)
        (HDP.gaussianMatrixVectorize B) =
      ∑ i : Fin m, ∑ j : Fin n, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp only [HDP.gaussianMatrixVectorize, HDP.gaussianMatrixFlatten,
    RCLike.inner_apply, conj_trivial, WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type]
  simp [mul_comm]

/-- Vectorization preserves the square of the Frobenius norm. -/
lemma norm_gaussianMatrixVectorize_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖HDP.gaussianMatrixVectorize A‖ ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    inner_gaussianMatrixVectorize]
  simp [pow_two]

/-- Vectorization is an isometry for the Frobenius norm. -/
lemma norm_gaussianMatrixVectorize {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖HDP.gaussianMatrixVectorize A‖ =
      HDP.matrixFrobeniusNorm A := by
  rw [← sq_eq_sq₀ (norm_nonneg _)
    (HDP.matrixFrobeniusNorm_nonneg A)]
  rw [norm_gaussianMatrixVectorize_sq,
    HDP.matrixFrobeniusNorm_sq]

/-- The Riesz representative of the derivative of an ambient function,
written as a matrix. -/
noncomputable def ambientGradientMatrix {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (y : FrobeniusEuclidean n) :
    Matrix (Fin n) (Fin n) ℝ :=
  HDP.gaussianMatrixUnvectorize
    ((InnerProductSpace.toDual ℝ
      (FrobeniusEuclidean n)).symm (fderiv ℝ H y))

/-- Applying the derivative in a matrix direction is Frobenius pairing with
the ambient gradient matrix. -/
lemma fderiv_vectorize_eq_sum_ambientGradientMatrix {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (y : FrobeniusEuclidean n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    fderiv ℝ H y (HDP.gaussianMatrixVectorize A) =
      ∑ i : Fin n, ∑ j : Fin n,
        ambientGradientMatrix H y i j * A i j := by
  have h :=
    (InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := FrobeniusEuclidean n)
      (x := HDP.gaussianMatrixVectorize A)
      (y := fderiv ℝ H y))
  rw [← HDP.gaussianMatrixVectorize_unvectorize
    ((InnerProductSpace.toDual ℝ
      (FrobeniusEuclidean n)).symm (fderiv ℝ H y)),
    inner_gaussianMatrixVectorize] at h
  simpa [ambientGradientMatrix] using h.symm

private lemma sum_mul_mul_skewGenerator {n : ℕ}
    (G U : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n,
        G a b * (U * skewGenerator i j) a b =
      (Uᵀ * G) i j - (Uᵀ * G) j i := by
  have hmul (a b : Fin n) :
      (U * skewGenerator i j) a b =
        (if b = j then U a i else 0) -
          (if b = i then U a j else 0) := by
    rw [skewGenerator, mul_sub]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hbj : b = j
      · subst b
        rw [Matrix.sub_apply, Matrix.mul_single_apply_same]
        rw [Matrix.mul_single_apply_of_ne (1 : ℝ) j i a j
          (fun h : j = i => hij h.symm) U]
        rw [if_neg (fun h : j = i => hij h.symm)]
        simp
      · by_cases hbi : b = i
        · subst b
          simp [hij]
        · simp [hbj, hbi]
  simp_rw [hmul, mul_sub, Finset.sum_sub_distrib]
  simp [Matrix.mul_apply, mul_comm]

/-- The ambient gradient, translated to the identity using right
trivialization. -/
noncomputable def rightAmbientMatrix {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  U.1ᵀ *
    ambientGradientMatrix H
      (HDP.gaussianMatrixVectorize U.1)

/-- Right-trivialized tangent gradient: the skew projection of the translated
ambient gradient. -/
noncomputable def tangentGradient {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (rightAmbientMatrix H U i j -
      rightAmbientMatrix H U j i) / 2

lemma tangentGradient_transpose {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    (tangentGradient H U)ᵀ = -tangentGradient H U := by
  ext i j
  simp [tangentGradient]
  ring

/-- Directional differentiation along an elementary right rotation. -/
lemma fderiv_skewGenerator_eq_tangentGradient {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (i j : Fin n) :
    fderiv ℝ H (HDP.gaussianMatrixVectorize U.1)
        (HDP.gaussianMatrixVectorize
          (U.1 * skewGenerator i j)) =
      2 * tangentGradient H U i j := by
  rw [fderiv_vectorize_eq_sum_ambientGradientMatrix,
    sum_mul_mul_skewGenerator]
  simp [tangentGradient, rightAmbientMatrix]
  ring

/-- Orthogonal projection to skew matrices cannot increase Frobenius
energy. -/
lemma matrixFrobeniusNorm_skewProjection_sq_le {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm
        (fun i j => (M i j - M j i) / 2) ^ 2 ≤
      HDP.matrixFrobeniusNorm M ^ 2 := by
  rw [HDP.matrixFrobeniusNorm_sq,
    HDP.matrixFrobeniusNorm_sq]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        ((M i j - M j i) / 2) ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n,
          (M i j ^ 2 + M j i ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (M i j + M j i)]
    _ = ∑ i : Fin n, ∑ j : Fin n, M i j ^ 2 := by
      simp only [div_eq_mul_inv, add_mul,
        Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [Finset.sum_comm]
      ring

/-- Left multiplication by a special orthogonal matrix preserves the
Frobenius norm. -/
lemma matrixFrobeniusNorm_transpose_mul_special {n : ℕ}
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm (U.1ᵀ * A) =
      HDP.matrixFrobeniusNorm A := by
  have hUt :
      U.1ᵀ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ,
      Matrix.transpose_transpose]
    exact
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2.1
  have hOne :
      (1 : Matrix (Fin n) (Fin n) ℝ) ∈
        Matrix.orthogonalGroup (Fin n) ℝ := by
    simp
  have h :=
    (HDP.Chapter4.orthogonalInvariance A U.1ᵀ 1
      hUt hOne).1
  simpa using h

/-- The Riesz identification and vectorization are isometries. -/
lemma matrixFrobeniusNorm_ambientGradientMatrix {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (y : FrobeniusEuclidean n) :
    HDP.matrixFrobeniusNorm (ambientGradientMatrix H y) =
      ‖fderiv ℝ H y‖ := by
  rw [← norm_gaussianMatrixVectorize]
  simp [ambientGradientMatrix]

/-- Tangent energy is controlled by the ambient derivative norm. -/
lemma tangentGradient_energy_le_fderiv {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2 ≤
      ‖fderiv ℝ H
        (HDP.gaussianMatrixVectorize U.1)‖ ^ 2 := by
  calc
    HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2 ≤
        HDP.matrixFrobeniusNorm
          (rightAmbientMatrix H U) ^ 2 := by
      exact matrixFrobeniusNorm_skewProjection_sq_le _
    _ = HDP.matrixFrobeniusNorm
          (ambientGradientMatrix H
            (HDP.gaussianMatrixVectorize U.1)) ^ 2 := by
      rw [rightAmbientMatrix,
        matrixFrobeniusNorm_transpose_mul_special]
    _ = ‖fderiv ℝ H
          (HDP.gaussianMatrixVectorize U.1)‖ ^ 2 := by
      rw [matrixFrobeniusNorm_ambientGradientMatrix]

lemma continuous_gaussianMatrixVectorize {m n : ℕ} :
    Continuous (HDP.gaussianMatrixVectorize :
      Matrix (Fin m) (Fin n) ℝ →
        EuclideanSpace ℝ (Fin m × Fin n)) := by
  unfold HDP.gaussianMatrixVectorize
    HDP.gaussianMatrixFlatten
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin m × Fin n => ℝ)).comp
  apply continuous_pi
  intro p
  exact (continuous_apply p.2).comp
    (continuous_apply p.1)

lemma continuous_gaussianMatrixUnvectorize {m n : ℕ} :
    Continuous (HDP.gaussianMatrixUnvectorize :
      EuclideanSpace ℝ (Fin m × Fin n) →
        Matrix (Fin m) (Fin n) ℝ) := by
  unfold HDP.gaussianMatrixUnvectorize
  fun_prop

/-- A continuous ambient derivative gives a continuous ambient gradient
matrix. -/
lemma continuous_ambientGradientMatrix {n : ℕ}
    {H : FrobeniusEuclidean n → ℝ}
    (hH : Continuous (fun y => fderiv ℝ H y)) :
    Continuous (ambientGradientMatrix H) := by
  unfold ambientGradientMatrix
  exact continuous_gaussianMatrixUnvectorize.comp
    ((InnerProductSpace.toDual ℝ
      (FrobeniusEuclidean n)).symm.continuous.comp hH)

/-- A continuous ambient derivative gives a continuous tangent gradient on
the group. -/
lemma continuous_tangentGradient {n : ℕ}
    {H : FrobeniusEuclidean n → ℝ}
    (hH : Continuous (fun y => fderiv ℝ H y)) :
    Continuous (tangentGradient H) := by
  have hg :
      Continuous
        (fun U :
            Matrix.specialOrthogonalGroup (Fin n) ℝ =>
          ambientGradientMatrix H
            (HDP.gaussianMatrixVectorize U.1)) :=
    (continuous_ambientGradientMatrix hH).comp
      (continuous_gaussianMatrixVectorize.comp
        continuous_subtype_val)
  have hm : Continuous (rightAmbientMatrix H) := by
    unfold rightAmbientMatrix
    fun_prop
  unfold tangentGradient
  fun_prop

end

end HDP.Appendix.SpecialOrthogonal
