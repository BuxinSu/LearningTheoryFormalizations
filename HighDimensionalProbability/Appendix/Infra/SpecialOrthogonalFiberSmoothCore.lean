import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSmoothCore
import Mathlib.Data.Fin.SuccPred

/-!
# Smooth restrictions to special-orthogonal stabilizer fibers

This file constructs the ambient `C¹` representative obtained by restricting
a function on `(n+1) × (n+1)` matrices to a left coset of a coordinate
stabilizer.  Its right-trivialized tangent gradient is exactly the submatrix
of the ambient tangent gradient that avoids the fixed coordinate.  Hence its
Frobenius energy is exactly the corresponding vertical energy.
-/

open Matrix
open scoped BigOperators RealInnerProductSpace

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

/-- The infinitesimal coordinate-stabilizer embedding.  Unlike
`coordinateStabilizerMatrix`, its fixed singleton block is zero. -/
noncomputable def coordinateStabilizerTangentMatrix {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.reindex (coordinateBlockEquiv i).symm
    (coordinateBlockEquiv i).symm
    (Matrix.fromBlocks A 0 0
      (0 : Matrix PUnit.{1} PUnit.{1} ℝ))

@[simp] lemma coordinateStabilizerTangentMatrix_succAbove
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) (j k : Fin n) :
    coordinateStabilizerTangentMatrix i A
        (i.succAbove j) (i.succAbove k) = A j k := by
  simp [coordinateStabilizerTangentMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerTangentMatrix_fixed
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerTangentMatrix i A i i = 0 := by
  simp [coordinateStabilizerTangentMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerTangentMatrix_fixed_succAbove
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    coordinateStabilizerTangentMatrix i A i (i.succAbove j) = 0 := by
  simp [coordinateStabilizerTangentMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerTangentMatrix_succAbove_fixed
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    coordinateStabilizerTangentMatrix i A (i.succAbove j) i = 0 := by
  simp [coordinateStabilizerTangentMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerTangentMatrix_add
    {n : ℕ} (i : Fin (n + 1))
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerTangentMatrix i (A + B) =
      coordinateStabilizerTangentMatrix i A +
        coordinateStabilizerTangentMatrix i B := by
  ext a b
  rcases ha : coordinateBlockEquiv i a with a' | a'
    <;> rcases hb : coordinateBlockEquiv i b with b' | b'
    <;> simp [coordinateStabilizerTangentMatrix,
      Matrix.reindex_apply, Matrix.fromBlocks, ha, hb]

@[simp] lemma coordinateStabilizerTangentMatrix_smul
    {n : ℕ} (i : Fin (n + 1)) (c : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerTangentMatrix i (c • A) =
      c • coordinateStabilizerTangentMatrix i A := by
  ext a b
  rcases ha : coordinateBlockEquiv i a with a' | a'
    <;> rcases hb : coordinateBlockEquiv i b with b' | b'
    <;> simp [coordinateStabilizerTangentMatrix,
      Matrix.reindex_apply, Matrix.fromBlocks, ha, hb]

lemma coordinateStabilizerMatrix_sub
    {n : ℕ} (i : Fin (n + 1))
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerMatrix i A -
        coordinateStabilizerMatrix i B =
      coordinateStabilizerTangentMatrix i (A - B) := by
  classical
  change
    (Matrix.reindexLinearEquiv ℝ ℝ
      (coordinateBlockEquiv i).symm
      (coordinateBlockEquiv i).symm)
        (Matrix.fromBlocks A 0 0 1) -
      (Matrix.reindexLinearEquiv ℝ ℝ
        (coordinateBlockEquiv i).symm
        (coordinateBlockEquiv i).symm)
          (Matrix.fromBlocks B 0 0 1) =
    (Matrix.reindexLinearEquiv ℝ ℝ
      (coordinateBlockEquiv i).symm
      (coordinateBlockEquiv i).symm)
        (Matrix.fromBlocks (A - B) 0 0 0)
  rw [← map_sub]
  congr 1
  ext a b
  cases a <;> cases b <;> simp

lemma coordinateStabilizerMatrix_eq_tangent_add_zero
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerMatrix i A =
      coordinateStabilizerTangentMatrix i A +
        coordinateStabilizerMatrix i 0 := by
  have h := coordinateStabilizerMatrix_sub i A 0
  simp only [sub_zero] at h
  exact sub_eq_iff_eq_add.mp h

lemma coordinateStabilizerTangentMatrix_mul
    {n : ℕ} (i : Fin (n + 1))
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerTangentMatrix i (A * B) =
      coordinateStabilizerMatrix i A *
        coordinateStabilizerTangentMatrix i B := by
  classical
  unfold coordinateStabilizerMatrix
    coordinateStabilizerTangentMatrix
  change
    (Matrix.reindexAlgEquiv ℝ ℝ
      (coordinateBlockEquiv i).symm)
        (Matrix.fromBlocks (A * B) 0 0 0) =
      (Matrix.reindexAlgEquiv ℝ ℝ
        (coordinateBlockEquiv i).symm)
          (Matrix.fromBlocks A 0 0 1) *
      (Matrix.reindexAlgEquiv ℝ ℝ
        (coordinateBlockEquiv i).symm)
          (Matrix.fromBlocks B 0 0 0)
  rw [← map_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

@[simp] lemma coordinateStabilizerTangentMatrix_skewGenerator
    {n : ℕ} (i : Fin (n + 1)) (j k : Fin n) :
    coordinateStabilizerTangentMatrix i (skewGenerator j k) =
      skewGenerator (i.succAbove j) (i.succAbove k) := by
  ext a b
  cases a using i.succAboveCases
    <;> cases b using i.succAboveCases
    <;> simp [skewGenerator, Matrix.single_apply,
      i.succAbove_right_injective.eq_iff]

/-- The affine ambient map whose restriction to `SO(n)` parametrizes a left
coset of the coordinate stabilizer. -/
noncomputable def fiberAmbientMap {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : FrobeniusEuclidean n) :
    FrobeniusEuclidean (n + 1) :=
  HDP.gaussianMatrixVectorize
    (U * coordinateStabilizerMatrix i
      (HDP.gaussianMatrixUnvectorize y))

/-- Restriction of an ambient function to a moving stabilizer fiber. -/
noncomputable def fiberAmbientFunction {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (H : FrobeniusEuclidean (n + 1) → ℝ) :
    FrobeniusEuclidean n → ℝ :=
  H ∘ fiberAmbientMap i U

/-- Linear part of `fiberAmbientMap`. -/
noncomputable def fiberTangentCLM {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    FrobeniusEuclidean n →L[ℝ] FrobeniusEuclidean (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y =>
        HDP.gaussianMatrixVectorize
          (U * coordinateStabilizerTangentMatrix i
            (HDP.gaussianMatrixUnvectorize y))
      map_add' := by
        intro y z
        apply WithLp.ofLp_injective
        ext p
        change
          (U * coordinateStabilizerTangentMatrix i
            (HDP.gaussianMatrixUnvectorize (y + z))) p.1 p.2 =
          (U * coordinateStabilizerTangentMatrix i
            (HDP.gaussianMatrixUnvectorize y)) p.1 p.2 +
          (U * coordinateStabilizerTangentMatrix i
            (HDP.gaussianMatrixUnvectorize z)) p.1 p.2
        rw [show HDP.gaussianMatrixUnvectorize (y + z) =
            HDP.gaussianMatrixUnvectorize y +
              HDP.gaussianMatrixUnvectorize z by rfl,
          coordinateStabilizerTangentMatrix_add,
          Matrix.mul_add]
        rfl
      map_smul' := by
        intro c y
        apply WithLp.ofLp_injective
        ext p
        change
          (U * coordinateStabilizerTangentMatrix i
            (HDP.gaussianMatrixUnvectorize (c • y))) p.1 p.2 =
          c * (U * coordinateStabilizerTangentMatrix i
            (HDP.gaussianMatrixUnvectorize y)) p.1 p.2
        rw [show HDP.gaussianMatrixUnvectorize (c • y) =
            c • HDP.gaussianMatrixUnvectorize y by rfl,
          coordinateStabilizerTangentMatrix_smul,
          Matrix.mul_smul]
        rfl }

@[simp] lemma fiberTangentCLM_apply {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : FrobeniusEuclidean n) :
    fiberTangentCLM i U y =
      HDP.gaussianMatrixVectorize
        (U * coordinateStabilizerTangentMatrix i
          (HDP.gaussianMatrixUnvectorize y)) := rfl

lemma fiberAmbientMap_eq_tangent_add_const {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : FrobeniusEuclidean n) :
    fiberAmbientMap i U y =
      fiberTangentCLM i U y + fiberAmbientMap i U 0 := by
  apply WithLp.ofLp_injective
  ext p
  change
    (U * coordinateStabilizerMatrix i
      (HDP.gaussianMatrixUnvectorize y)) p.1 p.2 =
      (U * coordinateStabilizerTangentMatrix i
        (HDP.gaussianMatrixUnvectorize y)) p.1 p.2 +
      (U * coordinateStabilizerMatrix i
        (HDP.gaussianMatrixUnvectorize
          (0 : FrobeniusEuclidean n))) p.1 p.2
  rw [coordinateStabilizerMatrix_eq_tangent_add_zero,
    Matrix.mul_add]
  rfl

lemma hasFDerivAt_fiberAmbientMap {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : FrobeniusEuclidean n) :
    HasFDerivAt (fiberAmbientMap i U)
      (fiberTangentCLM i U) y := by
  have h :
      fiberAmbientMap i U =
        fun z => fiberTangentCLM i U z +
          fiberAmbientMap i U 0 := by
    funext z
    exact fiberAmbientMap_eq_tangent_add_const i U z
  rw [h]
  fun_prop

lemma fderiv_fiberAmbientMap {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : FrobeniusEuclidean n) :
    fderiv ℝ (fiberAmbientMap i U) y =
      fiberTangentCLM i U :=
  (hasFDerivAt_fiberAmbientMap i U y).fderiv

@[simp] lemma fiberAmbientMap_vectorize {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    fiberAmbientMap i U
        (HDP.gaussianMatrixVectorize V) =
      HDP.gaussianMatrixVectorize
        (U * coordinateStabilizerMatrix i V) := by
  simp [fiberAmbientMap]

@[simp] lemma fiberTangentCLM_vectorize_mul_skewGenerator
    {n : ℕ} (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (j k : Fin n) :
    fiberTangentCLM i U
        (HDP.gaussianMatrixVectorize
          (V * skewGenerator j k)) =
      HDP.gaussianMatrixVectorize
        ((U * coordinateStabilizerMatrix i V) *
          skewGenerator (i.succAbove j)
            (i.succAbove k)) := by
  simp only [fiberTangentCLM_apply,
    HDP.gaussianMatrixUnvectorize_vectorize,
    coordinateStabilizerTangentMatrix_mul,
    coordinateStabilizerTangentMatrix_skewGenerator]
  rw [Matrix.mul_assoc]

private lemma contDiff_coordinateStabilizerMatrix_unvectorize_apply
    {n : ℕ} (i : Fin (n + 1)) (a b : Fin (n + 1)) :
    ContDiff ℝ ⊤
      (fun y : FrobeniusEuclidean n =>
        coordinateStabilizerMatrix i
          (HDP.gaussianMatrixUnvectorize y) a b) := by
  unfold coordinateStabilizerMatrix Matrix.reindex
    HDP.gaussianMatrixUnvectorize
  rcases ha : coordinateBlockEquiv i a with a' | a'
    <;> rcases hb : coordinateBlockEquiv i b with b' | b'
    <;> simp [Matrix.fromBlocks, ha, hb]
    <;> fun_prop

lemma contDiff_fiberAmbientMap {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ContDiff ℝ ⊤ (fiberAmbientMap i U) := by
  unfold fiberAmbientMap
    HDP.gaussianMatrixVectorize HDP.gaussianMatrixFlatten
  change ContDiff ℝ ⊤
    ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (n + 1) × Fin (n + 1) => ℝ)).symm ∘
        fun (y : FrobeniusEuclidean n)
            (p : Fin (n + 1) × Fin (n + 1)) =>
          (U * coordinateStabilizerMatrix i
            (HDP.gaussianMatrixUnvectorize y)) p.1 p.2)
  apply
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (n + 1) × Fin (n + 1) => ℝ)).symm.contDiff.comp
  rw [contDiff_pi]
  intro p
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro c _
  exact
    (contDiff_const.mul
      (contDiff_coordinateStabilizerMatrix_unvectorize_apply
        i c p.2))

lemma differentiable_fiberAmbientMap {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Differentiable ℝ (fiberAmbientMap i U) :=
  (contDiff_fiberAmbientMap i U).differentiable (by simp)

lemma continuous_fderiv_fiberAmbientMap {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Continuous (fun y => fderiv ℝ (fiberAmbientMap i U) y) :=
  (contDiff_fiberAmbientMap i U).continuous_fderiv (by simp)

lemma differentiable_fiberAmbientFunction {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (H : FrobeniusEuclidean (n + 1) → ℝ)
    (hH : Differentiable ℝ H) :
    Differentiable ℝ (fiberAmbientFunction i U H) :=
  hH.comp (differentiable_fiberAmbientMap i U)

lemma continuous_fderiv_fiberAmbientFunction {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (H : FrobeniusEuclidean (n + 1) → ℝ)
    (hHd : Differentiable ℝ H)
    (hHc : Continuous (fun y => fderiv ℝ H y)) :
    Continuous
      (fun y => fderiv ℝ (fiberAmbientFunction i U H) y) := by
  have heq :
      (fun y => fderiv ℝ
        (fiberAmbientFunction i U H) y) =
        fun y =>
          fderiv ℝ H (fiberAmbientMap i U y) ∘L
            fderiv ℝ (fiberAmbientMap i U) y := by
    funext y
    exact fderiv_comp y (hHd _)
      ((differentiable_fiberAmbientMap i U) y)
  rw [heq]
  have ho :
      Continuous
        (fun y => fderiv ℝ H (fiberAmbientMap i U y)) :=
    hHc.comp (contDiff_fiberAmbientMap i U).continuous
  have hi :
      Continuous
        (fun y => fderiv ℝ (fiberAmbientMap i U) y) :=
    continuous_fderiv_fiberAmbientMap i U
  fun_prop

lemma fderiv_fiberAmbientFunction_skewGenerator
    {n : ℕ} (i : Fin (n + 1))
    (U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (V : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (H : FrobeniusEuclidean (n + 1) → ℝ)
    (hHd : Differentiable ℝ H) (j k : Fin n) :
    fderiv ℝ (fiberAmbientFunction i U.1 H)
        (HDP.gaussianMatrixVectorize V.1)
        (HDP.gaussianMatrixVectorize
          (V.1 * skewGenerator j k)) =
      2 * tangentGradient H
        (U * coordinateStabilizerHom i V)
        (i.succAbove j) (i.succAbove k) := by
  unfold fiberAmbientFunction
  rw [fderiv_comp _ (hHd _)
      ((differentiable_fiberAmbientMap i U.1) _),
    ContinuousLinearMap.comp_apply,
    fderiv_fiberAmbientMap,
    fiberTangentCLM_vectorize_mul_skewGenerator,
    fiberAmbientMap_vectorize]
  exact fderiv_skewGenerator_eq_tangentGradient H
    (U * coordinateStabilizerHom i V)
    (i.succAbove j) (i.succAbove k)

/-- The lower-dimensional tangent gradient is the ambient gradient submatrix
obtained by deleting the fixed row and column. -/
lemma tangentGradient_fiberAmbientFunction_apply
    {n : ℕ} (i : Fin (n + 1))
    (U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (V : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (H : FrobeniusEuclidean (n + 1) → ℝ)
    (hHd : Differentiable ℝ H) (j k : Fin n) :
    tangentGradient (fiberAmbientFunction i U.1 H) V j k =
      tangentGradient H (U * coordinateStabilizerHom i V)
        (i.succAbove j) (i.succAbove k) := by
  have hlower :=
    fderiv_skewGenerator_eq_tangentGradient
      (fiberAmbientFunction i U.1 H) V j k
  have hambient :=
    fderiv_fiberAmbientFunction_skewGenerator
      i U V H hHd j k
  rw [hlower] at hambient
  linarith

/-- For a skew matrix, deleting row and column `i` leaves precisely the
vertical energy associated with the `i`-th stabilizer. -/
lemma verticalSquareEnergy_eq_succAbove_sum
    {n : ℕ} (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hX : Xᵀ = -X) (i : Fin (n + 1)) :
    verticalSquareEnergy X i =
      ∑ j : Fin n, ∑ k : Fin n,
        X (i.succAbove j) (i.succAbove k) ^ 2 := by
  have hdiag : X i i = 0 := by
    have h := congrArg (fun M => M i i) hX
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    linarith
  have hsym (j : Fin n) :
      X (i.succAbove j) i ^ 2 =
        X i (i.succAbove j) ^ 2 := by
    have h :=
      congrArg (fun M => M i (i.succAbove j)) hX
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    rw [h]
    ring
  have hinner (j : Fin n) :
      (∑ b : Fin (n + 1),
          X (i.succAbove j) b ^ 2) =
        X (i.succAbove j) i ^ 2 +
          ∑ k : Fin n,
            X (i.succAbove j) (i.succAbove k) ^ 2 :=
    Fin.sum_univ_succAbove
      (fun b => X (i.succAbove j) b ^ 2) i
  have htotal :
      (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
          X a b ^ 2) =
        X i i ^ 2 +
          (∑ k : Fin n, X i (i.succAbove k) ^ 2) +
          (∑ j : Fin n, X (i.succAbove j) i ^ 2) +
          ∑ j : Fin n, ∑ k : Fin n,
            X (i.succAbove j) (i.succAbove k) ^ 2 := by
    rw [Fin.sum_univ_succAbove
      (fun a => ∑ b : Fin (n + 1), X a b ^ 2) i]
    rw [Fin.sum_univ_succAbove
      (fun b => X i b ^ 2) i]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib]
    ring
  have hrow :
      (∑ b : Fin (n + 1), X i b ^ 2) =
        X i i ^ 2 +
          ∑ k : Fin n, X i (i.succAbove k) ^ 2 :=
    Fin.sum_univ_succAbove (fun b => X i b ^ 2) i
  unfold verticalSquareEnergy horizontalSquareEnergy
    rowSquareEnergy
  rw [HDP.matrixFrobeniusNorm_sq, htotal, hrow, hdiag]
  simp_rw [hsym]
  ring

/-- Pointwise exact vertical-energy bridge for a smooth stabilizer fiber. -/
lemma tangentGradient_fiberAmbientFunction_energy
    {n : ℕ} (i : Fin (n + 1))
    (U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (V : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (H : FrobeniusEuclidean (n + 1) → ℝ)
    (hHd : Differentiable ℝ H) :
    HDP.matrixFrobeniusNorm
        (tangentGradient (fiberAmbientFunction i U.1 H) V) ^ 2 =
      verticalSquareEnergy
        (tangentGradient H
          (U * coordinateStabilizerHom i V)) i := by
  rw [verticalSquareEnergy_eq_succAbove_sum _
    (tangentGradient_transpose H
      (U * coordinateStabilizerHom i V)) i]
  rw [HDP.matrixFrobeniusNorm_sq]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [tangentGradient_fiberAmbientFunction_apply
    i U V H hHd j k]

end

end HDP.Appendix.SpecialOrthogonal
