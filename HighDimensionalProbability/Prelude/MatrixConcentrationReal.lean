import HighDimensionalProbability.Prelude.Matrix
import HighDimensionalProbability.Prelude.MatrixConcentration

/-!
# Real-to-complex bridges for matrix concentration

The verified matrix-Laplace development is formulated for complex matrices,
whereas Book uses real matrices.  This file proves the correspondence instead
of changing the frozen library or exposing complex matrices as the book API.
-/

open Matrix WithLp Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace HDP

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]

/-- Entrywise complexification of a real matrix.

**Lean implementation helper.** -/
noncomputable def complexifyMatrix (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofReal

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Each entry of the complexified matrix is the complex embedding of the corresponding real entry.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_apply (A : Matrix m n ℝ) (i : m) (j : n) :
    complexifyMatrix A i j = A i j := rfl

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexification sends the zero real matrix to the zero complex matrix.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_zero :
    complexifyMatrix (0 : Matrix m n ℝ) = 0 := by
  ext i j
  simp [complexifyMatrix]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexification preserves matrix addition.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_add (A B : Matrix m n ℝ) :
    complexifyMatrix (A + B) = complexifyMatrix A + complexifyMatrix B := by
  ext i j
  simp [complexifyMatrix]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexification preserves additive negation.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_neg (A : Matrix m n ℝ) :
    complexifyMatrix (-A) = -complexifyMatrix A := by
  ext i j
  simp [complexifyMatrix]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexification preserves matrix subtraction.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_sub (A B : Matrix m n ℝ) :
    complexifyMatrix (A - B) = complexifyMatrix A - complexifyMatrix B := by
  ext i j
  simp [complexifyMatrix]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexification intertwines real scalar multiplication with the corresponding complex scalar action.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_smul (c : ℝ) (A : Matrix m n ℝ) :
    complexifyMatrix (c • A) = (c : ℂ) • complexifyMatrix A := by
  ext i j
  simp [complexifyMatrix]

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
/-- Complexification preserves matrix multiplication.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_mul (A : Matrix m n ℝ) (B : Matrix n l ℝ) :
    complexifyMatrix (A * B) = complexifyMatrix A * complexifyMatrix B := by
  ext i j
  simp [complexifyMatrix, Matrix.mul_apply]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexifying a real transpose gives the conjugate transpose of the complexified matrix.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_transpose (A : Matrix m n ℝ) :
    complexifyMatrix Aᵀ = (complexifyMatrix A)ᴴ := by
  ext i j
  simp [complexifyMatrix, Matrix.conjTranspose_apply]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Complexification commutes with finite matrix sums.

**Lean implementation helper.** -/
@[simp] lemma complexifyMatrix_sum {ι : Type*} (s : Finset ι)
    (A : ι → Matrix m n ℝ) :
    complexifyMatrix (∑ i ∈ s, A i) = ∑ i ∈ s, complexifyMatrix (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Complexified matrix-vector multiplication acts separately on the real and imaginary parts of the vector.

**Lean implementation helper.** -/
lemma complexifyMatrix_mulVec (A : Matrix m n ℝ) (x : n → ℂ) :
    complexifyMatrix A *ᵥ x = fun i =>
      ((A *ᵥ fun j => (x j).re) i : ℂ) +
        Complex.I * ((A *ᵥ fun j => (x j).im) i : ℂ) := by
  funext i
  apply Complex.ext
  · simp [complexifyMatrix, Matrix.mulVec, dotProduct, Complex.mul_re]
  · simp [complexifyMatrix, Matrix.mulVec, dotProduct, Complex.mul_im]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- On a real vector embedded in complex space, complexified matrix action is the complex embedding of real matrix action.

**Lean implementation helper.** -/
lemma complexifyMatrix_mulVec_ofReal (A : Matrix m n ℝ) (x : n → ℝ) :
    complexifyMatrix A *ᵥ (fun i => (x i : ℂ)) =
      fun i => ((A *ᵥ x) i : ℂ) := by
  rw [complexifyMatrix_mulVec]
  funext i
  simp [Matrix.mulVec]

omit [DecidableEq n] in
/-- The squared complex `ℓ²` norm is the sum of the squared Euclidean norms of the real and imaginary parts.

**Lean implementation helper.** -/
lemma complex_l2norm_sq_eq_re_add_im (x : n → ℂ) :
    MatrixConcentration.l2norm x ^ 2 =
      ‖(WithLp.toLp 2 (fun i => (x i).re) : EuclideanSpace ℝ n)‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => (x i).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
  classical
  rw [MatrixConcentration.l2norm_sq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

omit [DecidableEq n] in
/-- Embedding a real vector into complex coordinates preserves its Euclidean `ℓ²` norm.

**Lean implementation helper.** -/
lemma complex_l2norm_ofReal (x : n → ℝ) :
    MatrixConcentration.l2norm (fun i => (x i : ℂ)) =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  classical
  rw [← sq_eq_sq₀ (MatrixConcentration.l2norm_nonneg _) (norm_nonneg _),
    MatrixConcentration.l2norm_sq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

omit [DecidableEq m] in
/-- Complexification preserves the Euclidean operator norm, including for
rectangular matrices.

**Lean implementation helper.** -/
@[simp] theorem complexifyMatrix_opNorm (A : Matrix m n ℝ) :
    ‖complexifyMatrix A‖ = ‖A‖ := by
  classical
  apply le_antisymm
  · refine MatrixConcentration.l2_opNorm_le_bound (complexifyMatrix A) (norm_nonneg A) ?_
    intro x
    let xr : n → ℝ := fun i => (x i).re
    let xi : n → ℝ := fun i => (x i).im
    have hr := A.l2_opNorm_mulVec (WithLp.toLp 2 xr)
    have hi := A.l2_opNorm_mulVec (WithLp.toLp 2 xi)
    have hr' : ‖(WithLp.toLp 2 (A *ᵥ xr) : EuclideanSpace ℝ m)‖ ≤
        ‖A‖ * ‖(WithLp.toLp 2 xr : EuclideanSpace ℝ n)‖ := by
      simpa [Matrix.toLpLin_apply] using hr
    have hi' : ‖(WithLp.toLp 2 (A *ᵥ xi) : EuclideanSpace ℝ m)‖ ≤
        ‖A‖ * ‖(WithLp.toLp 2 xi : EuclideanSpace ℝ n)‖ := by
      simpa [Matrix.toLpLin_apply] using hi
    have hout : MatrixConcentration.l2norm (complexifyMatrix A *ᵥ x) ^ 2 =
        ‖(WithLp.toLp 2 (A *ᵥ xr) : EuclideanSpace ℝ m)‖ ^ 2 +
          ‖(WithLp.toLp 2 (A *ᵥ xi) : EuclideanSpace ℝ m)‖ ^ 2 := by
      rw [complexifyMatrix_mulVec, complex_l2norm_sq_eq_re_add_im]
      simp [xr, xi]
    have hin : MatrixConcentration.l2norm x ^ 2 =
        ‖(WithLp.toLp 2 xr : EuclideanSpace ℝ n)‖ ^ 2 +
          ‖(WithLp.toLp 2 xi : EuclideanSpace ℝ n)‖ ^ 2 :=
      complex_l2norm_sq_eq_re_add_im x
    have hr0 : 0 ≤ ‖(WithLp.toLp 2 (A *ᵥ xr) : EuclideanSpace ℝ m)‖ := norm_nonneg _
    have hi0 : 0 ≤ ‖(WithLp.toLp 2 (A *ᵥ xi) : EuclideanSpace ℝ m)‖ := norm_nonneg _
    have hxr0 : 0 ≤ ‖(WithLp.toLp 2 xr : EuclideanSpace ℝ n)‖ := norm_nonneg _
    have hxi0 : 0 ≤ ‖(WithLp.toLp 2 xi : EuclideanSpace ℝ n)‖ := norm_nonneg _
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have hsquare : MatrixConcentration.l2norm (complexifyMatrix A *ᵥ x) ^ 2 ≤
        (‖A‖ * MatrixConcentration.l2norm x) ^ 2 := by
      rw [hout, mul_pow, hin]
      nlinarith [sq_le_sq₀ hr0 (mul_nonneg hA0 hxr0) |>.mpr hr',
        sq_le_sq₀ hi0 (mul_nonneg hA0 hxi0) |>.mpr hi']
    nlinarith [MatrixConcentration.l2norm_nonneg (complexifyMatrix A *ᵥ x),
      MatrixConcentration.l2norm_nonneg x,
      mul_nonneg hA0 (MatrixConcentration.l2norm_nonneg x)]
  · rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro x
    have hc := MatrixConcentration.l2norm_mulVec_le (complexifyMatrix A)
      (fun i => ((WithLp.ofLp x i : ℝ) : ℂ))
    rw [complexifyMatrix_mulVec_ofReal, complex_l2norm_ofReal,
      complex_l2norm_ofReal] at hc
    simpa [Matrix.toLpLin_apply, MatrixConcentration.l2norm] using hc

-- The frozen complex bridge currently requires these finite-index instances;
-- keep the compatibility signature localized to this correspondence lemma.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Complexifying a symmetric real matrix produces a Hermitian complex matrix.

**Lean implementation helper.** -/
lemma complexifyMatrix_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (complexifyMatrix A).IsHermitian := by
  simpa [complexifyMatrix] using MatrixConcentration.isHermitian_map_ofReal hA

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Entrywise complexification is a measurable map between finite matrix spaces.

**Lean implementation helper.** -/
lemma measurable_complexifyMatrix :
    Measurable (complexifyMatrix : Matrix m n ℝ → Matrix m n ℂ) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hi : Measurable (fun A : Matrix m n ℝ => A i) := measurable_pi_apply i
  have hij : Measurable (fun A : Matrix m n ℝ => A i j) :=
    (measurable_pi_apply j).comp hi
  exact Complex.continuous_ofReal.measurable.comp hij

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Entrywise expectation of a real random matrix. This mirrors the verified
complex `MatrixConcentration.expectation` interface and avoids imposing a
Bochner-integrability hypothesis merely to state centering.

**Lean implementation helper.** -/
noncomputable def realMatrixExpectation (μ : Measure Ω)
    (X : Ω → Matrix m n ℝ) : Matrix m n ℝ :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂μ

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Each entry of the real matrix expectation is the integral of the corresponding random entry.

**Lean implementation helper.** -/
@[simp] lemma realMatrixExpectation_apply (X : Ω → Matrix m n ℝ) (i : m) (j : n) :
    realMatrixExpectation μ X i j = ∫ ω, X ω i j ∂μ := rfl

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Composing a measurable real random matrix with entrywise complexification remains measurable.

**Lean implementation helper.** -/
lemma measurable_complexifyMatrix_comp {X : Ω → Matrix m n ℝ}
    (hX : Measurable X) : Measurable (fun ω => complexifyMatrix (X ω)) :=
  measurable_complexifyMatrix.comp hX

-- The verified complex expectation API is finite-matrix indexed.  Retain its
-- instance parameters here so downstream conversions remain definitionally
-- compatible with that frozen interface.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Complexification commutes with the entrywise matrix expectation.

**Lean implementation helper.** -/
lemma expectation_complexifyMatrix (X : Ω → Matrix m n ℝ) :
    MatrixConcentration.expectation μ (fun ω => complexifyMatrix (X ω)) =
      complexifyMatrix (realMatrixExpectation μ X) := by
  ext i j
  rw [MatrixConcentration.expectation_apply]
  exact integral_ofReal

omit [DecidableEq m] in
/-- Complexification preserves the pointwise operator norm and hence its integral.

**Lean implementation helper.** -/
lemma complexifyMatrix_integral_norm (X : Ω → Matrix m n ℝ) :
    (∫ ω, ‖complexifyMatrix (X ω)‖ ∂μ) = ∫ ω, ‖X ω‖ ∂μ := by
  classical
  congr 1
  funext ω
  exact complexifyMatrix_opNorm (X ω)

end HDP
