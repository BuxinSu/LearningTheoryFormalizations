import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Shared finite-dimensional random-vector infrastructure

The book distinguishes the centered covariance matrix from the uncentered
second-moment matrix.  In Chapter 3, isotropy means that the latter is the
identity; it does **not** include a zero-mean assumption.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The uncentered second-moment matrix `𝔼 XXᵀ`.

**Book Chapter 3.** -/
noncomputable def secondMomentMatrix {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ ω, X ω i * X ω j ∂μ

/-- The `(i,j)` entry of the second-moment matrix is `∫ X_i X_j dμ`.

**Lean implementation helper.** -/
@[simp]
theorem secondMomentMatrix_apply {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) (i j : Fin n) :
    secondMomentMatrix X μ i j = ∫ ω, X ω i * X ω j ∂μ := rfl

/-- The centered covariance matrix, re-exported from Chapter 1 under a
book-wide name. -/
noncomputable abbrev covarianceMatrix {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) : Matrix (Fin n) (Fin n) ℝ :=
  Chapter1.covMatrix X μ

/-- The uncentered second-moment matrix viewed as a continuous operator on
Euclidean space.

**Lean implementation helper.** -/
noncomputable def secondMomentOperator {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLpLin 2 2 (secondMomentMatrix X μ))

/-- The centered covariance matrix viewed as a continuous operator.

**Lean implementation helper.** -/
noncomputable def covarianceOperator {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLpLin 2 2 (covarianceMatrix X μ))

/-- Applying the second-moment operator is multiplication by the second-moment matrix.

**Lean implementation helper.** -/
@[simp]
theorem secondMomentOperator_apply {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω)
    (v : EuclideanSpace ℝ (Fin n)) :
    secondMomentOperator X μ v =
      WithLp.toLp 2 ((secondMomentMatrix X μ).mulVec v.ofLp) := by
  simp [secondMomentOperator, Matrix.toLpLin_apply]

/-- Applying the covariance operator is multiplication by the covariance matrix.

**Lean implementation helper.** -/
@[simp]
theorem covarianceOperator_apply {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω)
    (v : EuclideanSpace ℝ (Fin n)) :
    covarianceOperator X μ v =
      WithLp.toLp 2 ((covarianceMatrix X μ).mulVec v.ofLp) := by
  simp [covarianceOperator, Matrix.toLpLin_apply]

/-- A random vector is isotropic when its uncentered second-moment matrix is
the identity. This is Definition 3.2.5.

**Book Definition 3.2.5.** -/
def IsIsotropic {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) : Prop :=
  secondMomentMatrix X μ = 1

/-- Isotropy means `E[XX^T]=I`, equivalently `E<X,v>^2=‖v‖^2`.

**Book Definition 3.2.5.** -/
theorem isIsotropic_iff {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)} :
    IsIsotropic X μ ↔ ∀ i j, ∫ ω, X ω i * X ω j ∂μ = if i = j then 1 else 0 := by
  rw [IsIsotropic]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    simpa [secondMomentMatrix, Matrix.one_apply] using hij
  · intro h
    ext i j
    simpa [secondMomentMatrix, Matrix.one_apply] using h i j

/-- Source-facing isotropy packages the probability-space, measurability, and
finite-second-moment conditions implicit in ordinary expectation notation,
together with the raw isotropy equation.

**Book Definition 3.2.5.** -/
structure IsIsotropicRandomVector {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  aemeasurable : AEMeasurable X μ
  memLp_two : MemLp X 2 μ
  isIsotropic : IsIsotropic X μ

/-- For an isotropic random vector, each coordinate has second moment one.

**Lean implementation helper.** -/
theorem IsIsotropic.secondMoment_coord {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} (hX : IsIsotropic X μ) (i : Fin n) :
    ∫ ω, (X ω i) ^ 2 ∂μ = 1 := by
  have h := (isIsotropic_iff.mp hX i i)
  simpa [pow_two] using h

/-- Isotropy is equivalently the statement that the shared second-moment
operator is the identity operator.

**Book Definition 3.2.5.** -/
theorem isIsotropic_iff_secondMomentOperator_eq_id {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} :
    IsIsotropic X μ ↔
      secondMomentOperator X μ = ContinuousLinearMap.id ℝ _ := by
  constructor
  · intro h
    rw [IsIsotropic] at h
    ext v
    simp [secondMomentOperator_apply, h]
  · intro h
    rw [IsIsotropic]
    apply (Matrix.toLpLin 2 2).injective
    have hlin := congrArg ContinuousLinearMap.toLinearMap h
    simpa [secondMomentOperator] using hlin

/-- The second-moment matrix of a random vector is symmetric.

**Lean implementation helper.** -/
theorem secondMomentMatrix_transpose {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    (secondMomentMatrix X μ).transpose = secondMomentMatrix X μ := by
  ext i j
  simp [secondMomentMatrix, mul_comm]

/-- The centered covariance matrix is symmetric.

**Book Chapter 3.** -/
theorem covarianceMatrix_transpose {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    (covarianceMatrix X μ).transpose = covarianceMatrix X μ := by
  ext i j
  simp [covarianceMatrix, Chapter1.covMatrix, mul_comm]

/-- The second-moment operator is self-adjoint.

**Lean implementation helper.** -/
theorem secondMomentOperator_isSelfAdjoint {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    IsSelfAdjoint (secondMomentOperator X μ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  change (Matrix.toEuclideanLin (secondMomentMatrix X μ)).IsSymmetric
  rw [Matrix.isSymmetric_toEuclideanLin_iff]
  simpa [Matrix.IsHermitian] using secondMomentMatrix_transpose (μ := μ) X

/-- The covariance operator is self-adjoint.

**Lean implementation helper.** -/
theorem covarianceOperator_isSelfAdjoint {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    IsSelfAdjoint (covarianceOperator X μ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  change (Matrix.toEuclideanLin (covarianceMatrix X μ)).IsSymmetric
  rw [Matrix.isSymmetric_toEuclideanLin_iff]
  simpa [Matrix.IsHermitian] using covarianceMatrix_transpose (μ := μ) X

/-- A vector is subgaussian if every one-dimensional marginal is
subgaussian. Uniform control is recorded separately by `psi2NormVector`.

**Book Definition 3.4.1.** -/
def SubGaussianVector {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin n),
    SubGaussian (fun ω => inner ℝ (X ω) u) μ

/-- The Chapter 3 vector ψ₂ norm, defined as the supremum over unit
directions. Results using this real-valued supremum carry the boundedness
hypothesis required by `csSup`; this avoids silently treating an infinite
supremum as finite.

**Book Definition 3.4.1.** -/
noncomputable def psi2NormVector {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) : ℝ :=
  sSup {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
    r = psi2Norm (fun ω => inner ℝ (X ω) u) μ}

/-- A vector is subgaussian if every one-dimensional marginal is; its vector `psi_2` norm is the supremum over unit directions.

**Book Definition 3.4.1.** -/
theorem psi2Norm_marginal_le_vector {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hbounded : BddAbove {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
      r = psi2Norm (fun ω => inner ℝ (X ω) u) μ})
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) :
    psi2Norm (fun ω => inner ℝ (X ω) u) μ ≤ psi2NormVector X μ := by
  exact le_csSup hbounded ⟨u, hu, rfl⟩

/-- A source-facing specified multivariate Gaussian law.

**Book Chapter 3.** -/
def HasGaussianVectorLaw {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω) (m : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  AEMeasurable X μ ∧ Measure.map X μ = multivariateGaussian m S

end HDP
