import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Shared real-matrix infrastructure

This file is the source-neutral matrix layer used from Book Chapter 4 onward.  The
authoritative operator norm is Mathlib's `Matrix.Norms.L2Operator` norm, and the
authoritative singular values are the zero-indexed, zero-padded singular values of
`Matrix.toEuclideanLin`.
-/

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace HDP

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

/-- Product Borel sigma-algebra on finite real matrices.  This instance lives
in the source-neutral matrix layer so probability constructions do not need
to import the matrix-concentration bridge. -/
noncomputable instance instMeasurableSpaceRealMatrix :
    MeasurableSpace (Matrix m n ℝ) := MeasurableSpace.pi

-- Finiteness is the hypothesis under which the finite product Borel structure
-- agrees with the coordinatewise measurable structure.
set_option linter.unusedFintypeInType false in
instance instBorelSpaceRealMatrix : BorelSpace (Matrix m n ℝ) := Pi.borelSpace

/-- A descriptive alias for finite real matrices. -/
abbrev RealMatrix (m n : Type*) := Matrix m n ℝ

/-- The Euclidean operator norm of a real matrix.

**Lean implementation helper.** -/
noncomputable def matrixOpNorm [DecidableEq n] (A : Matrix m n ℝ) : ℝ := ‖A‖

/-- The Frobenius (Hilbert–Schmidt) norm of a real matrix.

**Lean implementation helper.** -/
noncomputable def matrixFrobeniusNorm (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The Euclidean matrix inner product.

**Lean implementation helper.** -/
noncomputable def matrixFrobeniusInner (A B : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The `k`th (zero-indexed) singular value, padded by zeros after the domain
dimension.

**Lean implementation helper.** -/
noncomputable def matrixSingularValue [DecidableEq n] (A : Matrix m n ℝ) (k : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues k

/-- The Gram matrix `Aᵀ A`.

**Lean implementation helper.** -/
def gramMatrix (A : Matrix m n ℝ) : Matrix n n ℝ := Aᵀ * A

/-- Rank of a real matrix through the range of its authoritative Euclidean
linear map. This avoids switching between incompatible matrix-rank wrappers.

**Lean implementation helper.** -/
noncomputable def matrixRank [DecidableEq n] (A : Matrix m n ℝ) : ℕ :=
  Module.finrank ℝ A.toEuclideanLin.range

/-- The orthogonal projection onto a finite-dimensional real subspace, exposed
as a source-neutral continuous operator.

**Lean implementation helper.** -/
noncomputable def orthogonalProjectionOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) : E →L[ℝ] E :=
  K.starProjection

/-- A square real matrix as a continuous Euclidean operator.

**Lean implementation helper.** -/
noncomputable def matrixOperator [DecidableEq n]
    (A : Matrix n n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  A.toEuclideanLin.toContinuousLinearMap

omit [Fintype m] in
/-- Matrix rank is the real dimension of the range of the associated Euclidean linear map.

**Lean implementation helper.** -/
lemma matrixRank_eq_finrank_range [DecidableEq n] (A : Matrix m n ℝ) :
    matrixRank A = Module.finrank ℝ A.toEuclideanLin.range := rfl

omit [Fintype m] in
/-- Bounds `matrixRank` above by `domain`.

**Lean implementation helper.** -/
lemma matrixRank_le_domain [DecidableEq n] (A : Matrix m n ℝ) :
    matrixRank A ≤ Fintype.card n := by
  simpa [matrixRank, finrank_euclideanSpace] using A.toEuclideanLin.finrank_range_le

/-- Bounds `matrixRank` above by `codomain`.

**Lean implementation helper.** -/
lemma matrixRank_le_codomain [DecidableEq n] (A : Matrix m n ℝ) :
    matrixRank A ≤ Fintype.card m := by
  calc
    matrixRank A = Module.finrank ℝ A.toEuclideanLin.range := rfl
    _ ≤ Module.finrank ℝ (EuclideanSpace ℝ m) := Submodule.finrank_le _
    _ = Fintype.card m := finrank_euclideanSpace

/-- Orthogonal projection onto a finite-dimensional subspace is self-adjoint.

**Lean implementation helper.** -/
lemma orthogonalProjectionOperator_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) :
    IsSelfAdjoint (orthogonalProjectionOperator K) := by
  simp [orthogonalProjectionOperator]

/-- Orthogonal projection onto a subspace is idempotent.

**Lean implementation helper.** -/
lemma orthogonalProjectionOperator_isIdempotent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) :
    IsIdempotentElem (orthogonalProjectionOperator K) := by
  simp [orthogonalProjectionOperator, K.isIdempotentElem_starProjection]

/-- The Euclidean operator associated with a real square matrix is self-adjoint exactly when the matrix is symmetric.

**Lean implementation helper.** -/
lemma matrixOperator_isSelfAdjoint_iff [DecidableEq n]
    (A : Matrix n n ℝ) :
    IsSelfAdjoint (matrixOperator A) ↔ A.IsHermitian := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact Matrix.isSymmetric_toEuclideanLin_iff

/-- The Euclidean operator norm of every real matrix is nonnegative.

**Lean implementation helper.** -/
lemma matrixOpNorm_nonneg [DecidableEq n] (A : Matrix m n ℝ) : 0 ≤ matrixOpNorm A :=
  norm_nonneg _

/-- The Euclidean operator norm of the zero matrix is zero.

**Lean implementation helper.** -/
@[simp] lemma matrixOpNorm_zero [DecidableEq n] :
    matrixOpNorm (0 : Matrix m n ℝ) = 0 := norm_zero

/-- The Euclidean operator norm satisfies the triangle inequality.

**Lean implementation helper.** -/
lemma matrixOpNorm_add_le [DecidableEq n] (A B : Matrix m n ℝ) :
    matrixOpNorm (A + B) ≤ matrixOpNorm A + matrixOpNorm B := norm_add_le _ _

/-- Scalar multiplication scales the Euclidean operator norm by the scalar's absolute value.

**Lean implementation helper.** -/
@[simp] lemma matrixOpNorm_smul [DecidableEq n] (c : ℝ) (A : Matrix m n ℝ) :
    matrixOpNorm (c • A) = |c| * matrixOpNorm A := by
  change ‖c • A‖ = |c| * ‖A‖
  rw [Matrix.l2_opNorm_def (c • A), Matrix.l2_opNorm_def A, map_smul, norm_smul,
    Real.norm_eq_abs]

/-- Negating a matrix does not change its Euclidean operator norm.

**Lean implementation helper.** -/
@[simp] lemma matrixOpNorm_neg [DecidableEq n] (A : Matrix m n ℝ) :
    matrixOpNorm (-A) = matrixOpNorm A := norm_neg _

/-- The operator norm of a matrix difference is at most the sum of the two operator norms.

**Lean implementation helper.** -/
lemma matrixOpNorm_sub_le [DecidableEq n] (A B : Matrix m n ℝ) :
    matrixOpNorm (A - B) ≤ matrixOpNorm A + matrixOpNorm B := by
  simpa [sub_eq_add_neg] using matrixOpNorm_add_le A (-B)

/-- The Euclidean operator norm is submultiplicative under matrix multiplication.

**Lean implementation helper.** -/
lemma matrixOpNorm_mul [DecidableEq n] [DecidableEq l]
    (A : Matrix m n ℝ) (B : Matrix n l ℝ) :
    matrixOpNorm (A * B) ≤ matrixOpNorm A * matrixOpNorm B :=
  Matrix.l2_opNorm_mul A B

/-- Transposition preserves the Euclidean operator norm of a real matrix.

**Lean implementation helper.** -/
@[simp] lemma matrixOpNorm_transpose [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    matrixOpNorm Aᵀ = matrixOpNorm A := by
  simpa [matrixOpNorm, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.l2_opNorm_conjTranspose A)

/-- Matrix-vector multiplication is bounded by the operator norm times the vector norm.

**Lean implementation helper.** -/
lemma norm_mulVec_le [DecidableEq n] (A : Matrix m n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖WithLp.toLp 2 (A *ᵥ (WithLp.ofLp x : n → ℝ))‖ ≤ matrixOpNorm A * ‖x‖ := by
  simpa [matrixOpNorm] using A.l2_opNorm_mulVec x

/-- The Frobenius norm of every real matrix is nonnegative.

**Lean implementation helper.** -/
lemma matrixFrobeniusNorm_nonneg (A : Matrix m n ℝ) :
    0 ≤ matrixFrobeniusNorm A := Real.sqrt_nonneg _

/-- The squared Frobenius norm is the sum of the squared matrix entries.

**Lean implementation helper.** -/
lemma matrixFrobeniusNorm_sq (A : Matrix m n ℝ) :
    matrixFrobeniusNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [matrixFrobeniusNorm, Real.sq_sqrt]
  positivity

/-- The Frobenius norm of the zero matrix is zero.

**Lean implementation helper.** -/
@[simp] lemma matrixFrobeniusNorm_zero :
    matrixFrobeniusNorm (0 : Matrix m n ℝ) = 0 := by
  simp [matrixFrobeniusNorm]

/-- Transposition preserves the Frobenius norm.

**Lean implementation helper.** -/
@[simp] lemma matrixFrobeniusNorm_transpose (A : Matrix m n ℝ) :
    matrixFrobeniusNorm Aᵀ = matrixFrobeniusNorm A := by
  simp only [matrixFrobeniusNorm, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Scalar multiplication scales the Frobenius norm by the scalar's absolute value.

**Lean implementation helper.** -/
@[simp] lemma matrixFrobeniusNorm_smul (c : ℝ) (A : Matrix m n ℝ) :
    matrixFrobeniusNorm (c • A) = |c| * matrixFrobeniusNorm A := by
  rw [matrixFrobeniusNorm, matrixFrobeniusNorm]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hsum : (∑ i, ∑ j, (c * A i j) ^ 2) = c ^ 2 * (∑ i, ∑ j, A i j ^ 2) := by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
    congr 1
    funext i
    rw [Finset.mul_sum]
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The Frobenius inner product of a matrix with itself is the square of its Frobenius norm.

**Lean implementation helper.** -/
lemma matrixInner_self (A : Matrix m n ℝ) :
    matrixFrobeniusInner A A = matrixFrobeniusNorm A ^ 2 := by
  rw [matrixFrobeniusInner, matrixFrobeniusNorm_sq]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Frobenius inner product `⟨A,B⟩` equals `trace (AᵀB)`.

**Lean implementation helper.** -/
lemma matrixInner_eq_trace (A B : Matrix m n ℝ) :
    matrixFrobeniusInner A B = (Aᵀ * B).trace := by
  simp only [matrixFrobeniusInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Every singular value of a finite real matrix is nonnegative.

**Lean implementation helper.** -/
lemma matrixSingularValue_nonneg [DecidableEq n] (A : Matrix m n ℝ) (k : ℕ) :
    0 ≤ matrixSingularValue A k :=
  A.toEuclideanLin.singularValues_nonneg k

/-- The singular-value sequence of a finite matrix is nonincreasing.

**Lean implementation helper.** -/
lemma matrixSingularValue_antitone [DecidableEq n] (A : Matrix m n ℝ) :
    Antitone (matrixSingularValue A) :=
  A.toEuclideanLin.singularValues_antitone

/-- Singular values indexed beyond the column-space dimension vanish.

**Lean implementation helper.** -/
lemma matrixSingularValue_of_finrank_le [DecidableEq n] (A : Matrix m n ℝ) {k : ℕ}
    (hk : Fintype.card n ≤ k) : matrixSingularValue A k = 0 := by
  apply A.toEuclideanLin.singularValues_of_finrank_le
  simpa using hk

/-- The square of each singular value is the corresponding eigenvalue of the Gram operator.

**Lean implementation helper.** -/
lemma sq_matrixSingularValue [DecidableEq n]
    (A : Matrix m n ℝ) (k : Fin (Fintype.card n)) :
    matrixSingularValue A k ^ 2 =
      A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace (ι := n) (𝕜 := ℝ)) k := by
  exact A.toEuclideanLin.sq_singularValues_fin
    (finrank_euclideanSpace (ι := n) (𝕜 := ℝ)) k

omit [Fintype n] in
/-- Every real Gram matrix is symmetric.

**Lean implementation helper.** -/
lemma gramMatrix_isHermitian (A : Matrix m n ℝ) : (gramMatrix A).IsHermitian := by
  simpa [gramMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.isHermitian_conjTranspose_mul_self A)

omit [Fintype n] in
/-- Every real Gram matrix is positive semidefinite.

**Lean implementation helper.** -/
lemma gramMatrix_posSemidef [Finite n] (A : Matrix m n ℝ) : (gramMatrix A).PosSemidef := by
  letI := Fintype.ofFinite n
  simpa [gramMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self A)

/-- The squared operator norm of a matrix equals the operator norm of its Gram matrix.

**Lean implementation helper.** -/
lemma matrixOpNorm_sq_eq_gram [DecidableEq n] (A : Matrix m n ℝ) :
    matrixOpNorm A ^ 2 = matrixOpNorm (gramMatrix A) := by
  rw [matrixOpNorm, matrixOpNorm, gramMatrix, pow_two]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.l2_opNorm_conjTranspose_mul_self A).symm

end HDP
