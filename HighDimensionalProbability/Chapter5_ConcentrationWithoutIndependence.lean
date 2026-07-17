/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import HighDimensionalProbability.Prelude.Sphere
import MatrixConcentration.Appendix_GaussianConcentration
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Distributions.Uniform
import HighDimensionalProbability.Prelude.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Probability.CDF
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Constructions.UnitInterval
import HighDimensionalProbability.Chapter4_RandomMatrices
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Complex.ExponentialBounds
import HighDimensionalProbability.Prelude.MatrixConcentrationReal
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# Chapter 5 — Concentration Without Independence

## Contents

- §5.1 Concentration of Lipschitz functions on the sphere — spherical concentration
  (Theorem 5.1.3), sharp elementary Lipschitz constants (Example 5.1.2),
  Euclidean and spherical isoperimetry (Theorems 5.1.4--5.1.5), and metric
  blow-up (Lemma 5.1.6)
- §5.2 Concentration on other metric-measure spaces — Gaussian, Hamming-cube,
  permutation, Grassmannian, convex-body, and product-measure concentration
  (Theorems 5.2.2--5.2.12), including existence and comparison of medians
  (Remark 5.2.1)
- §5.3 Johnson--Lindenstrauss lemma — dimension reduction (Theorem 5.3.1) and
  random-projection concentration (Lemma 5.3.2)
- §5.4 Matrix Bernstein inequality — matrix Bernstein (Theorem 5.4.1),
  spectral functional calculus and Loewner order (Definitions 5.4.2--5.4.3),
  the noncommutative failure of scalar monotonicity (Remark 5.4.6),
  the failure of the scalar exponential addition law without commutation
  (Section 5.4.2; Exercise 5.19),
  Golden--Thompson and Lieb (Theorems 5.4.7--5.4.8), and matrix
  Hoeffding/Khintchine (Theorems 5.4.13--5.4.14)
- §5.5 Community detection in sparse networks — spectral recovery
  (Theorem 5.5.1)
- §5.6 Covariance estimation for general distributions — bounded-distribution
  covariance estimation (Theorem 5.6.1)
- §5.7 Bounded differences — McDiarmid's inequality (Theorem 5.7.1)

The detailed entries below identify the chapter's key source-facing definitions and
results by the numbering printed in the second-edition book PDF.
-/

/-! ## Material formerly in `01_LipschitzFunctions.lean` -/

section Source_01_LipschitzFunctions

/-!
# Lipschitz functions

This file introduces the source-facing Chapter 5 interface for Lipschitz
functions.  Mathlib's `LipschitzWith` and `LipschitzOnWith` are authoritative;
in particular, the constant is a nonnegative real and no finiteness claim is
hidden in a real-valued infimum.

The differentiability assertion printed before Book Exercise 5.1 is false as
stated on an unbounded domain.  The corrected theorem below records the
necessary uniform bound on the Fréchet derivative.
-/

open Set InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

/-- The least Lipschitz constant of a map, valued in `ℝ≥0∞` so that a
non-Lipschitz map has value `∞`. For a genuine Lipschitz map, the theorem
`lipschitzSeminorm_le_iff` characterizes this as exactly the book's
`‖f‖_Lip`.

**Book Definition 5.1.1.** -/
noncomputable def lipschitzSeminorm
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : ℝ≥0∞ :=
  ⨆ x, ⨆ y, edist (f x) (f y) / edist x y

/-- `lipschitzSeminorm f` is at most `K` exactly when `f` is
`K`-Lipschitz; hence it is the least admissible Lipschitz constant.

**Book Definition 5.1.1.** -/
theorem lipschitzSeminorm_le_iff
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (K : ℝ≥0) :
    lipschitzSeminorm f ≤ K ↔ LipschitzWith K f := by
  constructor
  · intro h x y
    by_cases hxy : x = y
    · simp [hxy]
    have hratio :
        edist (f x) (f y) / edist x y ≤ (K : ℝ≥0∞) := by
      calc
        _ ≤ ⨆ y, edist (f x) (f y) / edist x y := le_iSup _ y
        _ ≤ ⨆ x, ⨆ y, edist (f x) (f y) / edist x y :=
          le_iSup (fun z => ⨆ y, edist (f z) (f y) / edist z y) x
        _ ≤ K := h
    exact (ENNReal.div_le_iff_le_mul
      (Or.inl (by simpa using hxy))
      (Or.inl (edist_ne_top _ _))).mp hratio
  · intro h
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : x = y
    · simp [hxy]
    exact (ENNReal.div_le_iff_le_mul
      (Or.inl (by simpa using hxy))
      (Or.inl (edist_ne_top _ _))).mpr (h x y)

/-- Every Lipschitz map is uniformly continuous.

**Book §5.1.2.** -/
theorem exercise_5_1a_lipschitz_uniformContinuous
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} {f : X → Y} (hf : LipschitzWith K f) :
    UniformContinuous f :=
  hf.uniformContinuous

/-- A differentiable map whose Fréchet derivative is uniformly bounded by `K` on a convex set is
`K`-Lipschitz on that set. The derivative bound is essential.

**Book §5.1.2.** -/
theorem exercise_5_1b_lipschitzOn_of_bounded_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {K : ℝ≥0}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ s, ‖fderiv ℝ f x‖₊ ≤ K) :
    LipschitzOnWith K f s :=
  hs.lipschitzOnWith_of_nnnorm_fderiv_le hf hderiv

/-- Lipschitz implies uniformly continuous; a uniformly bounded derivative on a convex domain
implies Lipschitz.

**Book §5.1.2.** -/
theorem exercise_5_1b_lipschitz_of_bounded_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : ℝ≥0}
    (hf : Differentiable ℝ f)
    (hderiv : ∀ x, ‖fderiv ℝ f x‖₊ ≤ K) :
    LipschitzWith K f :=
  lipschitzWith_of_nnnorm_fderiv_le hf hderiv

/-- A Euclidean linear functional has the norm of its representing vector as
its sharp Lipschitz constant.

**Book Example 5.1.2.** -/
theorem example_5_1_2a {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) :
    LipschitzWith ⟨‖a‖, norm_nonneg a⟩
      (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ a x) ∧
    (∀ K : ℝ≥0, LipschitzWith K
        (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ a x) →
      ‖a‖ ≤ (K : ℝ)) := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← inner_sub_right]
    exact abs_real_inner_le_norm a (x - y)
  · intro K hK
    by_cases ha : a = 0
    · simp [ha]
    let u := ‖a‖⁻¹ • a
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, ha]
    have h := hK.dist_le_mul u 0
    rw [dist_zero_right, hu, mul_one, Real.dist_eq] at h
    have hcancel : ‖a‖⁻¹ * ‖a‖ ^ 2 = ‖a‖ := by field_simp
    simpa [u, inner_smul_right, real_inner_self_eq_norm_sq, ha,
      abs_of_nonneg (norm_nonneg a), hcancel] using h

/-- An `m × n` matrix acts from `ℝⁿ` to `ℝᵐ`, and its Euclidean operator norm
is its sharp Lipschitz constant.

**Book Example 5.1.2.** -/
theorem example_5_1_2b {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    LipschitzWith
        (⟨HDP.matrixOpNorm A, HDP.matrixOpNorm_nonneg A⟩ : ℝ≥0)
        A.toEuclideanLin ∧
      (∀ K : ℝ≥0, LipschitzWith K A.toEuclideanLin →
        HDP.matrixOpNorm A ≤ (K : ℝ)) := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖A.toEuclideanLin x - A.toEuclideanLin y‖ ≤
      HDP.matrixOpNorm A * ‖x - y‖
    rw [← map_sub]
    simpa [HDP.matrixOpNorm, Matrix.l2_opNorm_def] using
      A.toEuclideanLin.toContinuousLinearMap.le_opNorm (x - y)
  · intro K hK
    rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg
    intro x
    have h := hK.dist_le_mul x 0
    simpa using h

/-- The norm map is one-Lipschitz, and the constant is sharp on every
nontrivial real normed space.

**Book Example 5.1.2.** -/
theorem example_5_1_2c {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] :
    LipschitzWith 1 (fun x : E => ‖x‖) ∧
      ∀ K : ℝ≥0, LipschitzWith K (fun x : E => ‖x‖) → (1 : ℝ) ≤ K := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm,
      Real.norm_eq_abs] using abs_norm_sub_norm_le x y
  · intro K hK
    obtain ⟨x : E, hx⟩ := exists_ne (0 : E)
    have h := hK.dist_le_mul x 0
    rw [Real.dist_eq, norm_zero, sub_zero,
      abs_of_nonneg (norm_nonneg x), dist_zero_right] at h
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith

/-- Restricting a global Lipschitz map to a subtype preserves its constant. This is the basic
bridge used for observables on spheres, cubes, and balls.

**Lean implementation helper.** -/
theorem lipschitzWith_subtype_restrict
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} {K : ℝ≥0} {f : X → Y} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x : s ↦ f x) := by
  simpa [Function.comp_def] using hf.comp (LipschitzWith.subtype_val s)

/-- A Lipschitz observable on a set has a global real-valued extension with the same constant
(the nonlinear Hahn--Banach/McShane extension theorem).

**Lean implementation helper.** -/
theorem exists_lipschitz_extension_real
    {X : Type*} [PseudoMetricSpace X] {s : Set X}
    {K : ℝ≥0} {f : X → ℝ} (hf : LipschitzOnWith K f s) :
    ∃ F : X → ℝ, LipschitzWith K F ∧ Set.EqOn F f s := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_real
  exact ⟨F, hF, hEq.symm⟩

end HDP.Chapter5

end Source_01_LipschitzFunctions

/-! ## Material formerly in `02_SphereConcentration.lean` -/

section Source_02_SphereConcentration

/-!
# Concentration of Lipschitz functions on the sphere

The proof here is independent of the source-level external isoperimetric
theorems.  A real-valued Lipschitz observable is extended to the ambient
Euclidean space and coupled to a standard Gaussian.  Gaussian concentration
controls the extension, while the already proved Gaussian norm tail controls
the radial error.  The Gaussian direction has exactly normalized surface law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace BigOperators

namespace HDP.Chapter5

noncomputable section

/-- An explicit absolute constant for the Gaussian-coupling proof of spherical concentration. It
is intentionally not optimized.

**Lean implementation helper.** -/
def sphereConcentrationConstant : ℝ :=
  Real.sqrt 5 *
    (2 + (1 + 1 / Real.sqrt (Real.log 2)) * 256)

/-- Shows that sphere concentration constant is positive.

**Lean implementation helper.** -/
lemma sphereConcentrationConstant_pos : 0 < sphereConcentrationConstant := by
  unfold sphereConcentrationConstant
  have hlog : 0 < Real.sqrt (Real.log 2) :=
    Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  positivity

/-- A usual sub-Gaussian MGF estimate with variance proxy `K²` implies the source's `ψ₂` estimate.
This bridges Mathlib's `HasSubgaussianMGF` API and the authoritative the source Orlicz
interface.

**Lean implementation helper.** -/
lemma psi2Norm_le_of_hasSubgaussianMGF_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hX : HasSubgaussianMGF X ⟨K ^ 2, sq_nonneg K⟩ μ) :
    HDP.SubGaussian X μ ∧
      HDP.psi2Norm X μ ≤ Real.sqrt 5 * (2 * K) := by
  apply HDP.psi2Norm_le_of_mgf_bound hX.aemeasurable hK
  intro lam
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hX.integrable_exp_mul lam)
    (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ∫ ω, Real.exp (lam * X ω) ∂μ
        = ProbabilityTheory.mgf X μ lam := rfl
    _ ≤ Real.exp (((⟨K ^ 2, sq_nonneg K⟩ : ℝ≥0) : ℝ) * lam ^ 2 / 2) :=
      hX.mgf_le lam
    _ = Real.exp ((K ^ 2 : ℝ) * lam ^ 2 / 2) := rfl
    _ ≤ Real.exp (K ^ 2 * lam ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg K, sq_nonneg lam,
        mul_nonneg (sq_nonneg K) (sq_nonneg lam)]

/-- Turn a proved `ψ₂`-norm upper bound into an explicit tail parameter. The zero-parameter
branch is kept total: real division by zero makes the displayed right-hand side equal to `2`, so
the probability bound is automatic.

**Lean implementation helper.** -/
lemma tail_le_of_subGaussian_psi2Norm_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : HDP.SubGaussian X μ)
    {B : ℝ} (hB : 0 ≤ B) (hnorm : HDP.psi2Norm X μ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / B ^ 2)) := by
  rcases hB.eq_or_lt with rfl | hBpos
  · calc
      μ {ω | t ≤ |X ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (0 : ℝ) ^ 2)) := by
        norm_num
  · have hmgf := HDP.psi2MGF_le_two_of_ge hXm hX hnorm hBpos
    exact HDP.subgaussian_iii_to_i hXm hBpos hmgf ht

/-- Scaling the Gaussian direction of a vector by that vector's norm recovers the vector.

**Lean implementation helper.** -/
private lemma norm_smul_gaussianDirection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (x : E) :
    ‖x‖ • ((HDP.gaussianDirection (E := E) x :
      Metric.sphere (0 : E) 1) : E) = x := by
  by_cases hx : x = 0
  · simp [hx]
  · let y : ({0}ᶜ : Set E) := ⟨x, by simpa using hx⟩
    have hdir := HDP.gaussianDirection_coe (E := E) y
    change ‖x‖ • ((HDP.gaussianDirection (E := E) x :
      Metric.sphere (0 : E) 1) : E) = x
    rw [show x = (y : E) from rfl, hdir]
    rw [homeomorphUnitSphereProd_apply_fst_coe]
    simp only [smul_smul]
    rw [mul_inv_cancel₀]
    · simp
    · exact norm_ne_zero_iff.mpr hx

/-- The distance from `x` to the point of radius `r` in its Gaussian direction is `|r-‖x‖|`.

**Lean implementation helper.** -/
private lemma radial_projection_distance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (r : ℝ) (x : E) :
    dist (r • ((HDP.gaussianDirection (E := E) x :
      Metric.sphere (0 : E) 1) : E)) x = |r - ‖x‖| := by
  have hnorm : ‖((HDP.gaussianDirection (E := E) x :
      Metric.sphere (0 : E) 1) : E)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using
      (HDP.gaussianDirection (E := E) x).property
  calc
    dist (r • ((HDP.gaussianDirection (E := E) x :
        Metric.sphere (0 : E) 1) : E)) x =
        dist (r • ((HDP.gaussianDirection (E := E) x :
          Metric.sphere (0 : E) 1) : E))
          (‖x‖ • ((HDP.gaussianDirection (E := E) x :
            Metric.sphere (0 : E) 1) : E)) := by
          rw [norm_smul_gaussianDirection x]
    _ = |r - ‖x‖| := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, hnorm, mul_one,
        Real.norm_eq_abs]

/-- Identifies the probability law described by has law pi gaussian to euclidean.

**Lean implementation helper.** -/
private lemma hasLaw_piGaussian_toEuclidean (n : ℕ) :
    HasLaw (WithLp.toLp 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  refine ⟨(WithLp.measurable_toLp 2 (Fin n → ℝ)).aemeasurable, ?_⟩
  exact map_pi_eq_stdGaussian

/-- Identifies the probability law described by has law pi gaussian direction.

**Lean implementation helper.** -/
private lemma hasLaw_piGaussian_direction (n : ℕ) [Nonempty (Fin n)] :
    HasLaw
      (fun z : Fin n → ℝ ↦
        HDP.gaussianDirection
          (E := EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  have hdir : HasLaw
      (HDP.gaussianDirection (E := EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    refine ⟨HDP.measurable_gaussianDirection.aemeasurable, ?_⟩
    exact HDP.map_gaussianDirection_stdGaussian
  simpa only [Function.comp_def] using
    hdir.comp (hasLaw_piGaussian_toEuclidean n)

/-- The scaled-sphere observable induced by an ambient function.

**Lean implementation helper.** -/
def scaledSphereObservable (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
  fun x ↦ F (Real.sqrt n • (x : EuclideanSpace ℝ (Fin n)))

/-- Establishes measurability of scaled sphere observable.

**Lean implementation helper.** -/
lemma measurable_scaledSphereObservable {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Continuous F) :
    Measurable (scaledSphereObservable n F) := by
  unfold scaledSphereObservable
  exact hF.measurable.comp (by fun_prop)

/-- If `F` is `K`-Lipschitz on Euclidean space, its restriction to the sphere of radius `√n` has
a dimension-free centered `ψ₂` bound. The result is zero-safe.

**Book Theorem 5.1.3.** -/
theorem sphere_lipschitz_concentration_ambient
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) :
    HDP.psi2Norm
      (fun x ↦ scaledSphereObservable n F x -
        ∫ y, scaledSphereObservable n F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        sphereConcentrationConstant * K := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let γ : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  let σ : Measure (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let G : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := WithLp.toLp 2
  let U : (Fin n → ℝ) → Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun z ↦ HDP.gaussianDirection (E := EuclideanSpace ℝ (Fin n)) (G z)
  let W : (Fin n → ℝ) → ℝ := fun z ↦ F (G z)
  let Y : (Fin n → ℝ) → ℝ :=
    fun z ↦ F (Real.sqrt n • (U z : EuclideanSpace ℝ (Fin n)))
  let D : (Fin n → ℝ) → ℝ := fun z ↦ Y z - W z
  have hGm : Measurable G := WithLp.measurable_toLp 2 (Fin n → ℝ)
  have hWm : Measurable W := hF.continuous.measurable.comp hGm
  have hUm : Measurable U :=
    HDP.measurable_gaussianDirection.comp hGm
  have hYm : Measurable Y := hF.continuous.measurable.comp (by
    fun_prop)
  have hDm : Measurable D := hYm.sub hWm
  by_cases hK0 : (K : ℝ) = 0
  · have hKzero : K = 0 := NNReal.eq (by simpa using hK0)
    have hconst : ∀ x y, F x = F y :=
      (LipschitzWith.zero_iff F).mp (by simpa [hKzero] using hF)
    have hobs : scaledSphereObservable n F = fun _ ↦ F 0 := by
      funext x
      exact hconst _ _
    rw [hKzero, NNReal.coe_zero, mul_zero, hobs]
    simp [HDP.psi2Norm_const]
  · have hKpos : 0 < (K : ℝ) := lt_of_le_of_ne K.coe_nonneg (Ne.symm hK0)
    let V : (Fin n → ℝ) → ℝ := fun z ↦ W z / (K : ℝ)
    have hVmeas : Measurable V := hWm.div_const _
    have hVLip : ∀ x y, |V x - V y| ≤
        Real.sqrt (∑ i, (x i - y i) ^ 2) := by
      intro x y
      rw [show V x - V y = (W x - W y) / (K : ℝ) by
        simp [V]; ring, abs_div, abs_of_pos hKpos]
      apply (div_le_iff₀ hKpos).2
      have hdist := hF.dist_le_mul (G x) (G y)
      rw [Real.dist_eq] at hdist
      simpa [G, EuclideanSpace.dist_eq, Real.dist_eq, mul_comm] using hdist
    have hVmgf :=
      MatrixConcentration.gaussian_lipschitz_hasSubgaussianMGF_one
        (Fin n) V hVLip hVmeas
    have hWmgf : HasSubgaussianMGF
        (fun z ↦ W z - ∫ q, W q ∂γ)
        ⟨(K : ℝ) ^ 2, sq_nonneg (K : ℝ)⟩ γ := by
      have hs := hVmgf.const_mul (K : ℝ)
      convert hs using 1
      · funext z
        simp only [V, γ, integral_div]
        field_simp [hK0]
      · ext
        simp
    have hWsub := psi2Norm_le_of_hasSubgaussianMGF_sq hKpos hWmgf
    have hRtail : ∀ t : ℝ, 0 ≤ t →
        γ {z | t ≤ |‖G z‖ - Real.sqrt n|} ≤
          ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (256 : ℝ) ^ 2)) := by
      intro t ht
      have hs := HDP.Chapter3.stdGaussian_norm_deviation_tail n hn ht
      have hset : MeasurableSet
          {x : EuclideanSpace ℝ (Fin n) |
            t ≤ |‖x‖ - Real.sqrt n|} :=
        measurableSet_le measurable_const
          ((measurable_norm.sub_const (Real.sqrt n)).abs)
      rw [show γ {z | t ≤ |‖G z‖ - Real.sqrt n|} =
          (Measure.map G γ)
            {x | t ≤ |‖x‖ - Real.sqrt n|} by
        rw [Measure.map_apply hGm hset]
        rfl,
        show Measure.map G γ =
          stdGaussian (EuclideanSpace ℝ (Fin n)) from map_pi_eq_stdGaussian]
      exact hs
    have hR := HDP.psi2Norm_le_of_tail_bound
      (μ := γ) (X := fun z ↦ ‖G z‖ - Real.sqrt n)
      (hGm.norm.sub_const _).aemeasurable (by norm_num : (0 : ℝ) < 256)
      hRtail
    let Z : (Fin n → ℝ) → ℝ :=
      fun z ↦ (K : ℝ) * (‖G z‖ - Real.sqrt n)
    have hZsub : HDP.SubGaussian Z γ := hR.1.const_mul (K : ℝ)
    have hZnorm : HDP.psi2Norm Z γ ≤
        (K : ℝ) * (Real.sqrt 5 * 256) := by
      rw [show Z = fun z ↦ (K : ℝ) *
          (‖G z‖ - Real.sqrt n) from rfl,
        HDP.psi2Norm_const_mul, abs_of_pos hKpos]
      exact mul_le_mul_of_nonneg_left hR.2 K.coe_nonneg
    have hDdom : ∀ z, |D z| ≤ |Z z| := by
      intro z
      have hdist := hF.dist_le_mul
        (Real.sqrt n • (U z : EuclideanSpace ℝ (Fin n))) (G z)
      rw [Real.dist_eq] at hdist
      have hrad := radial_projection_distance
        (E := EuclideanSpace ℝ (Fin n)) (Real.sqrt n) (G z)
      change |Y z - W z| ≤ |Z z|
      calc
        |Y z - W z| ≤ (K : ℝ) *
            dist (Real.sqrt n • (U z : EuclideanSpace ℝ (Fin n))) (G z) := by
          simpa [Y, W] using hdist
        _ = (K : ℝ) * |Real.sqrt n - ‖G z‖| := by
          rw [hrad]
        _ = |Z z| := by
          simp [Z, abs_mul, abs_of_pos hKpos, abs_sub_comm]
    have hDsub := HDP.psi2Norm_mono_abs
      (μ := γ) (Filter.Eventually.of_forall hDdom) hZsub
    have hDcenter := HDP.psi2Norm_centering hDm.aemeasurable hDsub.1
    have hWint : Integrable W γ := by
      have hc : Integrable (fun _ : Fin n → ℝ ↦ ∫ q, W q ∂γ) γ :=
        integrable_const _
      have hs := hWmgf.integrable.add hc
      exact hs.congr (Filter.Eventually.of_forall fun z ↦ by
        change (W z - ∫ q, W q ∂γ) + (∫ q, W q ∂γ) = W z
        ring)
    have hDmem : MemLp D 1 γ := by
      simpa using hDsub.1.memLp hDm.aemeasurable (p := (1 : ℝ)) (le_refl 1)
    have hDint : Integrable D γ := hDmem.integrable (le_refl 1)
    have hYint : Integrable Y γ := by
      have hs := hDint.add hWint
      exact hs.congr (Filter.Eventually.of_forall fun z ↦ by simp [D])
    have hdecomp : (fun z ↦ Y z - ∫ q, Y q ∂γ) =
        fun z ↦ (W z - ∫ q, W q ∂γ) +
          (D z - ∫ q, D q ∂γ) := by
      have hint : (∫ q, Y q ∂γ) =
          (∫ q, W q ∂γ) + ∫ q, D q ∂γ := by
        rw [show Y = fun z ↦ W z + D z by
          funext z; simp [D]]
        exact integral_add hWint hDint
      funext z
      rw [hint]
      simp [D]
      ring
    have hRawSub : HDP.SubGaussian
        (fun z ↦ Y z - ∫ q, Y q ∂γ) γ := by
      rw [hdecomp]
      exact HDP.SubGaussian.add
        (hWm.sub_const _).aemeasurable (hDm.sub_const _).aemeasurable
        hWsub.1 hDcenter.1
    have hRawNorm : HDP.psi2Norm
        (fun z ↦ Y z - ∫ q, Y q ∂γ) γ ≤
          sphereConcentrationConstant * (K : ℝ) := by
      rw [hdecomp]
      calc
        HDP.psi2Norm
            (fun z ↦ (W z - ∫ q, W q ∂γ) +
              (D z - ∫ q, D q ∂γ)) γ
            ≤ HDP.psi2Norm (fun z ↦ W z - ∫ q, W q ∂γ) γ +
                HDP.psi2Norm (fun z ↦ D z - ∫ q, D q ∂γ) γ :=
          HDP.psi2Norm_add_le
            (hWm.sub_const _).aemeasurable (hDm.sub_const _).aemeasurable
            hWsub.1 hDcenter.1
        _ ≤ Real.sqrt 5 * (2 * (K : ℝ)) +
            (1 + 1 / Real.sqrt (Real.log 2)) *
              ((K : ℝ) * (Real.sqrt 5 * 256)) := by
          apply add_le_add hWsub.2
          have hfactor : 0 ≤ 1 + 1 / Real.sqrt (Real.log 2) := by
            positivity
          calc
            HDP.psi2Norm (fun z ↦ D z - ∫ q, D q ∂γ) γ
                ≤ (1 + 1 / Real.sqrt (Real.log 2)) *
                    HDP.psi2Norm D γ := hDcenter.2
            _ ≤ (1 + 1 / Real.sqrt (Real.log 2)) *
                    HDP.psi2Norm Z γ :=
              mul_le_mul_of_nonneg_left hDsub.2 hfactor
            _ ≤ (1 + 1 / Real.sqrt (Real.log 2)) *
                    ((K : ℝ) * (Real.sqrt 5 * 256)) :=
              mul_le_mul_of_nonneg_left hZnorm hfactor
        _ = sphereConcentrationConstant * (K : ℝ) := by
          unfold sphereConcentrationConstant
          ring
    have hdir := hasLaw_piGaussian_direction n
    have hmean : (∫ z, Y z ∂γ) =
        ∫ x, scaledSphereObservable n F x ∂σ := by
      simpa [Y, U, scaledSphereObservable, γ, σ] using
        hdir.integral_comp
          (measurable_scaledSphereObservable hF.continuous).aestronglyMeasurable
    let Scenter : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
      fun x ↦ scaledSphereObservable n F x -
        ∫ y, scaledSphereObservable n F y ∂σ
    let ν : Measure ℝ := Measure.map Scenter σ
    have hScenter : HasLaw Scenter ν σ := by
      refine ⟨(measurable_scaledSphereObservable hF.continuous).sub_const
        (∫ y, scaledSphereObservable n F y ∂σ) |>.aemeasurable, rfl⟩
    have hRawLaw : HasLaw
        (fun z ↦ Y z - ∫ q, Y q ∂γ) ν γ := by
      have hc := hScenter.comp hdir
      apply hc.congr
      filter_upwards [] with z
      simp only [Function.comp_apply, Scenter]
      rw [hmean]
      rfl
    have hSphereNorm : HDP.psi2Norm Scenter σ =
        HDP.psi2Norm (fun z ↦ Y z - ∫ q, Y q ∂γ) γ := by
      rw [HDP.psi2Norm_eq_of_hasLaw hScenter,
        HDP.psi2Norm_eq_of_hasLaw hRawLaw]
    change HDP.psi2Norm Scenter σ ≤ _
    rw [hSphereNorm]
    exact hRawNorm

/-- The centered spherical observable in the corresponding theorem is genuinely sub-Gaussian,
not merely assigned a finite real upper bound. This separate packaging lemma is useful for
invoking the tail and moment APIs.

**Lean implementation helper.** -/
theorem sphere_lipschitz_subGaussian_ambient
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) :
    HDP.SubGaussian
      (fun x ↦ scaledSphereObservable n F x -
        ∫ y, scaledSphereObservable n F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let B : ℝ := |F 0| + (K : ℝ) * Real.sqrt n
  have hB : 0 ≤ B := by positivity
  have hobsBound : ∀ x : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1,
      |scaledSphereObservable n F x| ≤ B := by
    intro x
    have hdist := hF.dist_le_mul
      (Real.sqrt n • (x : EuclideanSpace ℝ (Fin n))) 0
    rw [Real.dist_eq, dist_zero_right, norm_smul] at hdist
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
    calc
      |scaledSphereObservable n F x|
          ≤ |scaledSphereObservable n F x - F 0| + |F 0| := by
        calc
          |scaledSphereObservable n F x| =
              |(scaledSphereObservable n F x - F 0) + F 0| := by
                rw [sub_add_cancel]
          _ ≤ |scaledSphereObservable n F x - F 0| + |F 0| :=
            abs_add_le _ _
      _ ≤ (K : ℝ) * Real.sqrt n + |F 0| := by
        gcongr
        simpa [scaledSphereObservable, abs_of_nonneg (Real.sqrt_nonneg _)] using hdist
      _ = B := by simp [B, add_comm]
  have hobsInt : Integrable (scaledSphereObservable n F) σ := by
    apply Integrable.of_bound
      (measurable_scaledSphereObservable hF.continuous).aestronglyMeasurable B
    filter_upwards [] with x
    simpa [Real.norm_eq_abs] using hobsBound x
  have hmean : |∫ x, scaledSphereObservable n F x ∂σ| ≤ B := by
    calc
      |∫ x, scaledSphereObservable n F x ∂σ|
          ≤ ∫ x, |scaledSphereObservable n F x| ∂σ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x, B ∂σ := by
        apply integral_mono_ae hobsInt.abs (integrable_const B)
        exact Filter.Eventually.of_forall hobsBound
      _ = B := by simp
  have hcenterBound : ∀ x : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1,
      |scaledSphereObservable n F x -
          ∫ y, scaledSphereObservable n F y ∂σ| ≤ 2 * B + 1 := by
    intro x
    calc
      |scaledSphereObservable n F x -
          ∫ y, scaledSphereObservable n F y ∂σ|
          ≤ |scaledSphereObservable n F x| +
              |∫ y, scaledSphereObservable n F y ∂σ| := abs_sub _ _
      _ ≤ B + B := add_le_add (hobsBound x) hmean
      _ ≤ 2 * B + 1 := by linarith
  exact (HDP.psi2Norm_le_of_bounded
    (μ := σ)
    (X := fun x ↦ scaledSphereObservable n F x -
      ∫ y, scaledSphereObservable n F y ∂σ)
    (M := 2 * B + 1) (by linarith)
    (Filter.Eventually.of_forall hcenterBound)).1

/-- The exponent is expressed directly in the Lipschitz constant, including the zero-constant
case.

**Book Theorem 5.1.3.** -/
theorem sphere_lipschitz_tail_ambient
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |scaledSphereObservable n F x -
          ∫ y, scaledSphereObservable n F y
            ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 / (sphereConcentrationConstant * K) ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsub := sphere_lipschitz_subGaussian_ambient n hn F K hF
  have hnorm := sphere_lipschitz_concentration_ambient n hn F K hF
  exact tail_le_of_subGaussian_psi2Norm_le
    ((measurable_scaledSphereObservable hF.continuous).sub_const _).aemeasurable
    hsub (mul_nonneg sphereConcentrationConstant_pos.le K.property) hnorm ht

/-- Canonical parametrization of the sphere of radius `√n` by the unit sphere.

**Lean implementation helper.** -/
def scaleUnitSphere (n : ℕ) (hn : 0 < n) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) :=
  fun x ↦ ⟨Real.sqrt n • (x : EuclideanSpace ℝ (Fin n)), by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
    simp [hx, Real.norm_eq_abs, abs_of_pos
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))]⟩

/-- Establishes measurability of scale unit sphere.

**Lean implementation helper.** -/
lemma measurable_scaleUnitSphere (n : ℕ) (hn : 0 < n) :
    Measurable (scaleUnitSphere n hn) := by
  unfold scaleUnitSphere
  exact Measurable.subtype_mk (by fun_prop)

/-- The uniform random point is represented on the canonical unit-sphere probability space and
then scaled by `scaleUnitSphere`. This is definitionally the normalized surface law on the
radius-`√n` sphere.

**Book Theorem 5.1.3.** -/
theorem sphere_lipschitz_concentration
    (n : ℕ) (hn : 0 < n)
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) → ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) :
    HDP.psi2Norm
      (fun x ↦ f (scaleUnitSphere n hn x) -
        ∫ y, f (scaleUnitSphere n hn y)
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        sphereConcentrationConstant * K := by
  classical
  let s : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.sphere 0 (Real.sqrt n)
  let f₀ : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    if hx : x ∈ s then f ⟨x, hx⟩ else 0
  have hf₀ : LipschitzOnWith K f₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [f₀, dif_pos hx, dif_pos hy, Subtype.dist_eq] using
      hf.dist_le_mul (⟨x, hx⟩ : s) ⟨y, hy⟩
  obtain ⟨F, hF, hEq⟩ := exists_lipschitz_extension_real hf₀
  have hobs : (fun x ↦ f (scaleUnitSphere n hn x)) =
      scaledSphereObservable n F := by
    funext x
    have hx : (Real.sqrt n • (x : EuclideanSpace ℝ (Fin n))) ∈ s :=
      (scaleUnitSphere n hn x).property
    have he := hEq hx
    simpa [f₀, hx, scaledSphereObservable, scaleUnitSphere] using he.symm
  have hmean : (∫ y, f (scaleUnitSphere n hn y)
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      ∫ y, scaledSphereObservable n F y
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
    rw [hobs]
  have hcenter : (fun x ↦ f (scaleUnitSphere n hn x) -
      ∫ y, f (scaleUnitSphere n hn y)
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      fun x ↦ scaledSphereObservable n F x -
        ∫ y, scaledSphereObservable n F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
    funext x
    rw [congrFun hobs x, hmean]
  rw [hcenter]
  exact sphere_lipschitz_concentration_ambient n hn F K hF

/-- Source-domain companion asserting genuine sub-Gaussianity.

**Lean implementation helper.** -/
theorem sphere_lipschitz_subGaussian
    (n : ℕ) (hn : 0 < n)
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) → ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) :
    HDP.SubGaussian
      (fun x ↦ f (scaleUnitSphere n hn x) -
        ∫ y, f (scaleUnitSphere n hn y)
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let s : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.sphere 0 (Real.sqrt n)
  let f₀ : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    if hx : x ∈ s then f ⟨x, hx⟩ else 0
  have hf₀ : LipschitzOnWith K f₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [f₀, dif_pos hx, dif_pos hy, Subtype.dist_eq] using
      hf.dist_le_mul (⟨x, hx⟩ : s) ⟨y, hy⟩
  obtain ⟨F, hF, hEq⟩ := exists_lipschitz_extension_real hf₀
  have hobs : (fun x ↦ f (scaleUnitSphere n hn x)) =
      scaledSphereObservable n F := by
    funext x
    have hx : (Real.sqrt n • (x : EuclideanSpace ℝ (Fin n))) ∈ s :=
      (scaleUnitSphere n hn x).property
    have he := hEq hx
    simpa [f₀, hx, scaledSphereObservable, scaleUnitSphere] using he.symm
  have hmean : (∫ y, f (scaleUnitSphere n hn y)
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      ∫ y, scaledSphereObservable n F y
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
    rw [hobs]
  have hcenter : (fun x ↦ f (scaleUnitSphere n hn x) -
      ∫ y, f (scaleUnitSphere n hn y)
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      fun x ↦ scaledSphereObservable n F x -
        ∫ y, scaledSphereObservable n F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
    funext x
    rw [congrFun hobs x, hmean]
  rw [hcenter]
  exact sphere_lipschitz_subGaussian_ambient n hn F K hF

/-- Two-sided subgaussian tail for a Lipschitz sphere observable.

**Book (5.1).** -/
theorem sphere_lipschitz_tail
    (n : ℕ) (hn : 0 < n)
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) → ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |f (scaleUnitSphere n hn x) -
          ∫ y, f (scaleUnitSphere n hn y)
            ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 / (sphereConcentrationConstant * K) ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsub := sphere_lipschitz_subGaussian n hn f K hf
  have hnorm := sphere_lipschitz_concentration n hn f K hf
  have hm : Measurable (fun x ↦ f (scaleUnitSphere n hn x)) :=
    hf.continuous.measurable.comp (measurable_scaleUnitSphere n hn)
  exact tail_le_of_subGaussian_psi2Norm_le
    (hm.sub_const _).aemeasurable hsub
    (mul_nonneg sphereConcentrationConstant_pos.le K.property) hnorm ht

/-- Rescaling the corresponding theorem gives the expected `1/√n` concentration scale on the
unit sphere.

**Book Exercise 5.5.** -/
theorem unitSphere_lipschitz_concentration_ambient
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) :
    HDP.psi2Norm
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
        F x - ∫ y : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1, F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        sphereConcentrationConstant * K / Real.sqrt n := by
  let a : ℝ := (Real.sqrt n)⁻¹
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ F (a • z)
  have hG : LipschitzWith (K * ‖a‖₊) G := by
    simpa [G, Function.comp_def] using hF.comp (lipschitzWith_smul a)
  have hobs : scaledSphereObservable n G =
      fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ F x := by
    funext x
    simp only [scaledSphereObservable, G, a, smul_smul]
    rw [inv_mul_cancel₀ (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne']
    simp
  have h := sphere_lipschitz_concentration_ambient n hn G (K * ‖a‖₊) hG
  rw [hobs] at h
  calc
    HDP.psi2Norm
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
          F x - ∫ y : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1, F y
            ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        ≤ sphereConcentrationConstant * (K * ‖a‖₊) := h
    _ = sphereConcentrationConstant * K / Real.sqrt n := by
      have hs : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hn)
      simp [a, Real.nnnorm_of_nonneg hs.le]
      field_simp

/-- Unit-sphere Lipschitz observable has bounded psi2 norm.

**Book (5.30).** -/
theorem unitSphere_lipschitz_subGaussian_ambient
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) :
    HDP.SubGaussian
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
        F x - ∫ y : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1, F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  let a : ℝ := (Real.sqrt n)⁻¹
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ F (a • z)
  have hG : LipschitzWith (K * ‖a‖₊) G := by
    simpa [G, Function.comp_def] using hF.comp (lipschitzWith_smul a)
  have hobs : scaledSphereObservable n G =
      fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ F x := by
    funext x
    simp only [scaledSphereObservable, G, a, smul_smul]
    rw [inv_mul_cancel₀ (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne']
    simp
  have h := sphere_lipschitz_subGaussian_ambient n hn G (K * ‖a‖₊) hG
  rwa [hobs] at h

/-- Unit-sphere concentration with the explicit `K/√n` scale and safe `K=0` behavior.

**Book (5.31).** -/
theorem unitSphere_lipschitz_tail_ambient
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |F x - ∫ y : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1, F y
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 /
          (sphereConcentrationConstant * K / Real.sqrt n) ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsub := unitSphere_lipschitz_subGaussian_ambient n hn F K hF
  have hnorm := unitSphere_lipschitz_concentration_ambient n hn F K hF
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hB : 0 ≤ sphereConcentrationConstant * K / Real.sqrt n :=
    div_nonneg (mul_nonneg sphereConcentrationConstant_pos.le K.property) hs
  have hm : Measurable
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ F x) :=
    hF.continuous.measurable.comp measurable_subtype_coe
  exact tail_le_of_subGaussian_psi2Norm_le
    (hm.sub_const _).aemeasurable hsub hB hnorm ht

end

end HDP.Chapter5

end Source_02_SphereConcentration

/-! ## Material formerly in `03_SphericalBlowUp.lean` -/

section Source_03_SphericalBlowUp

/-!
# Blow-up of sets on the sphere

We use closed distance neighborhoods, defined with `infDist`.  This avoids the
false implicit assumption that a closest point exists in an arbitrary metric
space.  The main abstract lemma derives blow-up from centered `ψ₂`
concentration; the spherical endpoint then applies Theorem 5.1.3 to the
distance function.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

noncomputable section

/-- Closed `t`-neighborhood of a set, with safe distance semantics.

**Lean implementation helper.** -/
def closedDistanceNeighborhood {T : Type*} [PseudoMetricSpace T]
    (A : Set T) (t : ℝ) : Set T :=
  {x | infDist x A ≤ t}

/-- Establishes measurability of the set closed distance neighborhood.

**Lean implementation helper.** -/
lemma measurableSet_closedDistanceNeighborhood
    {T : Type*} [PseudoMetricSpace T] [MeasurableSpace T] [BorelSpace T]
    (A : Set T) (t : ℝ) :
    MeasurableSet (closedDistanceNeighborhood A t) := by
  exact measurableSet_le ((Metric.lipschitz_infDist_pt A).continuous.measurable)
    measurable_const

/-- Distance to a set is one-Lipschitz.

**Book Exercise 5.7.** -/
theorem exercise_5_7_distance_lipschitz
    {T : Type*} [PseudoMetricSpace T] (A : Set T) :
    LipschitzWith 1 (fun x : T ↦ infDist x A) :=
  Metric.lipschitz_infDist_pt A

/-- The mean of a nonnegative random variable that vanishes on a set of probability at least one
half is controlled by twice the `ψ₂` norm of its centered version. This is the quantitative
median-to-mean step needed in the blow-up argument.

**Lean implementation helper.** -/
lemma mean_le_two_psi2Norm_of_half_zero
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {A : Set T} (hAmeas : MeasurableSet A)
    (hAhalf : (1 / 2 : ℝ) ≤ μ.real A)
    {D : T → ℝ} (hDm : AEMeasurable D μ)
    (hDnonneg : ∀ᵐ x ∂μ, 0 ≤ D x)
    (hDzero : ∀ x ∈ A, D x = 0)
    (hsub : HDP.SubGaussian
      (fun x ↦ D x - ∫ y, D y ∂μ) μ) :
    ∫ x, D x ∂μ ≤
      2 * HDP.psi2Norm (fun x ↦ D x - ∫ y, D y ∂μ) μ := by
  let m : ℝ := ∫ x, D x ∂μ
  let C : T → ℝ := fun x ↦ D x - m
  have hCm : AEMeasurable C μ := hDm.sub_const m
  have hCmem : MemLp C 1 μ := by
    simpa using hsub.memLp hCm (p := (1 : ℝ)) (le_refl 1)
  have hCint : Integrable C μ := hCmem.integrable (le_refl 1)
  have hm : 0 ≤ m := integral_nonneg_of_ae hDnonneg
  have hpoint : ∀ x ∈ A, m ≤ |C x| := by
    intro x hx
    rw [show C x = -m by simp [C, hDzero x hx], abs_neg,
      abs_of_nonneg hm]
  have hsetLower : m * μ.real A ≤ ∫ x in A, |C x| ∂μ := by
    have hconst : IntegrableOn (fun _ : T ↦ m) A μ :=
      (integrable_const m).integrableOn
    have habs : IntegrableOn (fun x ↦ |C x|) A μ := hCint.abs.integrableOn
    have h := setIntegral_mono_on hconst habs hAmeas hpoint
    simpa [MeasureTheory.integral_const, hAmeas, mul_comm] using h
  have hsetUpper : (∫ x in A, |C x| ∂μ) ≤ ∫ x, |C x| ∂μ := by
    exact setIntegral_le_integral hCint.abs
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg (C x))
  have hmhalf : m / 2 ≤ ∫ x, |C x| ∂μ := by
    calc
      m / 2 ≤ m * μ.real A := by
        nlinarith [mul_le_mul_of_nonneg_left hAhalf hm]
      _ ≤ ∫ x in A, |C x| ∂μ := hsetLower
      _ ≤ ∫ x, |C x| ∂μ := hsetUpper
  have hmom := hsub.moment_bound hCm (p := (1 : ℝ)) (le_refl 1)
  have hL1 : (∫ x, |C x| ∂μ) ≤ HDP.psi2Norm C μ := by
    have heq : (∫ x, |C x| ∂μ) = HDP.Chapter1.lpNormRV C 1 μ := by
      rw [HDP.Chapter1.lpNormRV]
      simp only [div_one, Real.rpow_one]
    rw [heq]
    simpa using hmom
  dsimp only [C] at hL1 ⊢
  nlinarith

/-- The conclusion is stated as an upper bound for the complement of the closed neighborhood.

**Book Lemma 5.1.6.** -/
theorem blowUp_of_centered_concentration
    {T : Type*} {mT : MeasurableSpace T}
    {μ : Measure T} [IsProbabilityMeasure μ]
    {A : Set T} (hAmeas : MeasurableSet A)
    (hAhalf : (1 / 2 : ℝ) ≤ μ.real A)
    {D : T → ℝ} (hDm : AEMeasurable D μ)
    (hDnonneg : ∀ᵐ x ∂μ, 0 ≤ D x)
    (hDzero : ∀ x ∈ A, D x = 0)
    {K : ℝ} (hK : 0 < K)
    (hconcSub : HDP.SubGaussian
      (fun x ↦ D x - ∫ y, D y ∂μ) μ)
    (hconcNorm : HDP.psi2Norm
      (fun x ↦ D x - ∫ y, D y ∂μ) μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {x | 2 * K + t < D x} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / K ^ 2)) := by
  let m : ℝ := ∫ x, D x ∂μ
  have hm : m ≤ 2 * K := by
    calc
      m ≤ 2 * HDP.psi2Norm (fun x ↦ D x - ∫ y, D y ∂μ) μ := by
        apply mean_le_two_psi2Norm_of_half_zero hAmeas hAhalf hDm
          hDnonneg hDzero hconcSub
      _ ≤ 2 * K := by gcongr
  have hmgf := HDP.psi2MGF_le_two_of_ge
    (hDm.sub_const (∫ y, D y ∂μ)) hconcSub hconcNorm hK
  have htail := HDP.subgaussian_iii_to_i
    (hDm.sub_const (∫ y, D y ∂μ)) hK hmgf ht
  calc
    μ {x | 2 * K + t < D x}
        ≤ μ {x | t ≤ |D x - m|} := by
      apply measure_mono
      intro x hx
      change 2 * K + t < D x at hx
      change t ≤ |D x - m|
      have : t ≤ D x - m := by linarith
      exact this.trans (le_abs_self _)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / K ^ 2)) := by
      simpa [m] using htail

/-- Turns centered subgaussian concentration of distance into a quantitative neighborhood-growth
bound.

**Book Exercise 5.7.** -/
theorem exercise_5_7_blowUp_of_concentration
    {T : Type*} [PseudoMetricSpace T] [MeasurableSpace T] [BorelSpace T]
    {μ : Measure T} [IsProbabilityMeasure μ]
    (A : Set T) (hAmeas : MeasurableSet A) (_hAne : A.Nonempty)
    (hAhalf : (1 / 2 : ℝ) ≤ μ.real A)
    {K : ℝ} (hK : 0 < K)
    (hconcSub : HDP.SubGaussian
      (fun x ↦ infDist x A - ∫ y, infDist y A ∂μ) μ)
    (hconcNorm : HDP.psi2Norm
      (fun x ↦ infDist x A - ∫ y, infDist y A ∂μ) μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {x | 2 * K + t < infDist x A} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / K ^ 2)) := by
  exact blowUp_of_centered_concentration hAmeas hAhalf
    ((Metric.lipschitz_infDist_pt A).continuous.measurable.aemeasurable)
    (Filter.Eventually.of_forall fun _ ↦ infDist_nonneg)
    (fun x hx ↦ infDist_zero_of_mem hx) hK hconcSub hconcNorm ht

/-! ## Exercise 5.3: exponentially small sets -/

/-- This is the exact amplification argument behind the corresponding remark. Its hypothesis is
the source's preceding blow-up lemma, with the explicit tail `2 exp (-r²/C²)`. Open metric
thickenings give the clean separation identity needed at the boundary.

**Book Remark 5.1.7.** -/
theorem exercise_5_3a_exponentially_small_blowUp
    {T : Type*} [PseudoMetricSpace T] [MeasurableSpace T] [BorelSpace T]
    {μ : Measure T} [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 < C)
    (hblow : ∀ (B : Set T), MeasurableSet B →
      (1 / 2 : ℝ) ≤ μ.real B → ∀ r : ℝ, 0 ≤ r →
        μ.real (Metric.thickening r B)ᶜ ≤
          2 * Real.exp (-r ^ 2 / C ^ 2))
    (A : Set T) {s : ℝ} (hs : 0 ≤ s)
    (hA : 2 * Real.exp (-s ^ 2 / C ^ 2) < μ.real A) :
    (1 / 2 : ℝ) < μ.real (Metric.thickening s A) := by
  by_contra hhalf
  have hhalf' : μ.real (Metric.thickening s A) ≤ 1 / 2 :=
    le_of_not_gt hhalf
  let D : Set T := (Metric.thickening s A)ᶜ
  have hDmeas : MeasurableSet D := Metric.isOpen_thickening.measurableSet.compl
  have hDhalf : (1 / 2 : ℝ) ≤ μ.real D := by
    change (1 / 2 : ℝ) ≤ μ.real (Metric.thickening s A)ᶜ
    rw [MeasureTheory.measureReal_compl
      Metric.isOpen_thickening.measurableSet, probReal_univ]
    linarith
  have hDtail := hblow D hDmeas hDhalf s hs
  have hsubset : A ⊆ (Metric.thickening s D)ᶜ := by
    change A ⊆ (Metric.thickening s (Metric.thickening s A)ᶜ)ᶜ
    exact
      (Metric.subset_compl_thickening_compl_thickening_self s A)
  have hmono : μ.real A ≤ μ.real (Metric.thickening s D)ᶜ :=
    MeasureTheory.measureReal_mono hsubset
  linarith

/-- Once `A_s` has half the mass, a second blow-up and `s ≤ t` place its `t`-thickening inside
`A_{2t}`.

**Book Remark 5.1.7.** -/
theorem exercise_5_3b_exponentially_small_blowUp
    {T : Type*} [PseudoMetricSpace T] [MeasurableSpace T] [BorelSpace T]
    {μ : Measure T} [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 < C)
    (hblow : ∀ (B : Set T), MeasurableSet B →
      (1 / 2 : ℝ) ≤ μ.real B → ∀ r : ℝ, 0 ≤ r →
        μ.real (Metric.thickening r B)ᶜ ≤
          2 * Real.exp (-r ^ 2 / C ^ 2))
    (A : Set T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hA : 2 * Real.exp (-s ^ 2 / C ^ 2) < μ.real A) :
    1 - 2 * Real.exp (-t ^ 2 / C ^ 2) ≤
      μ.real (Metric.thickening (2 * t) A) := by
  have ht : 0 ≤ t := hs.trans hst
  have hhalfStrict :=
    exercise_5_3a_exponentially_small_blowUp hC hblow A hs hA
  have hhalf : (1 / 2 : ℝ) ≤ μ.real (Metric.thickening s A) :=
    hhalfStrict.le
  have htail := hblow (Metric.thickening s A)
    Metric.isOpen_thickening.measurableSet hhalf t ht
  have hnested : Metric.thickening t (Metric.thickening s A) ⊆
      Metric.thickening (2 * t) A := by
    refine (Metric.thickening_thickening_subset t s A).trans ?_
    apply Metric.thickening_mono
    linarith
  have hcompl : (Metric.thickening (2 * t) A)ᶜ ⊆
      (Metric.thickening t (Metric.thickening s A))ᶜ := by
    intro x hx hsmall
    exact hx (hnested hsmall)
  have hmono : μ.real (Metric.thickening (2 * t) A)ᶜ ≤
      μ.real (Metric.thickening t (Metric.thickening s A))ᶜ :=
    MeasureTheory.measureReal_mono hcompl
  have hcompEq : μ.real (Metric.thickening (2 * t) A)ᶜ =
      1 - μ.real (Metric.thickening (2 * t) A) := by
    rw [MeasureTheory.measureReal_compl
      Metric.isOpen_thickening.measurableSet, probReal_univ]
  linarith

/-! ## Exercise 5.4: geodesic versus chordal distance -/

/-- Arc length between two points on a Euclidean sphere of radius `r`.

**Lean implementation helper.** -/
def sphereGeodesicDist {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {r : ℝ}
    (x y : Metric.sphere (0 : E) r) : ℝ :=
  r * InnerProductGeometry.angle (x : E) (y : E)

/-- Chordal distance is at most spherical arc length.

**Lean implementation helper.** -/
lemma sphere_chordal_le_geodesic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (x y : Metric.sphere (0 : E) r) :
    dist x y ≤ sphereGeodesicDist x y := by
  let θ : ℝ := InnerProductGeometry.angle (x : E) (y : E)
  have hx : ‖(x : E)‖ = r := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
  have hy : ‖(y : E)‖ = r := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using y.property
  have hθ : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hlaw :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      (x : E) (y : E)
  rw [hx, hy] at hlaw
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hmul := mul_le_mul_of_nonneg_left hcos
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg r))
  have hsq : ‖(x : E) - (y : E)‖ ^ 2 ≤ (r * θ) ^ 2 := by
    dsimp [θ] at hcos hmul hlaw ⊢
    nlinarith
  rw [sphereGeodesicDist, Subtype.dist_eq, dist_eq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr.le hθ)).mp hsq

/-- Arc length is at most `π/2` times chordal distance. This is the sharp endpoint comparison on
a sphere and is the substantive geometric step in the corresponding exercise.

**Lean implementation helper.** -/
lemma sphere_geodesic_le_pi_div_two_chordal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (x y : Metric.sphere (0 : E) r) :
    sphereGeodesicDist x y ≤ Real.pi / 2 * dist x y := by
  let θ : ℝ := InnerProductGeometry.angle (x : E) (y : E)
  have hx : ‖(x : E)‖ = r := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
  have hy : ‖(y : E)‖ = r := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using y.property
  have hθ0 : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hθpi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
  have hcos : Real.cos θ ≤ 1 - 2 / Real.pi ^ 2 * θ ^ 2 :=
    Real.cos_le_one_sub_mul_cos_sq (by
      rw [abs_of_nonneg hθ0]
      exact hθpi)
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcore : 2 * θ ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos θ) := by
    have hm := mul_le_mul_of_nonneg_left hcos hpi2.le
    field_simp [Real.pi_ne_zero] at hm
    nlinarith
  have hlaw :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      (x : E) (y : E)
  rw [hx, hy] at hlaw
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hscaled := mul_le_mul_of_nonneg_left hcore hr2
  have hsq : (r * θ) ^ 2 ≤
      (Real.pi / 2 * ‖(x : E) - (y : E)‖) ^ 2 := by
    nlinarith [hscaled]
  rw [sphereGeodesicDist, Subtype.dist_eq, dist_eq_norm]
  exact (sq_le_sq₀ (mul_nonneg hr.le hθ0)
    (mul_nonneg (by positivity : 0 ≤ Real.pi / 2) (norm_nonneg _))).mp hsq

/-- A function that is `K`-Lipschitz for shortest-arc distance is `(pi/2)K`-Lipschitz for the
ambient chordal metric, so the corresponding theorem applies with exactly that constant loss.

**Book Exercise 5.4.** -/
theorem exercise_5_4_geodesic_concentration
    (n : ℕ) (hn : 0 < n)
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) → ℝ)
    (K : ℝ≥0)
    (hf : ∀ x y, |f x - f y| ≤ (K : ℝ) * sphereGeodesicDist x y) :
    HDP.psi2Norm
      (fun x ↦ f (scaleUnitSphere n hn x) -
        ∫ y, f (scaleUnitSphere n hn y)
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        sphereConcentrationConstant * (K : ℝ) * (Real.pi / 2) := by
  let L : ℝ≥0 := ⟨Real.pi / 2, by positivity⟩
  have hLip : LipschitzWith (K * L) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    calc
      |f x - f y| ≤ (K : ℝ) * sphereGeodesicDist x y := hf x y
      _ ≤ (K : ℝ) * (Real.pi / 2 * dist x y) := by
        gcongr
        exact sphere_geodesic_le_pi_div_two_chordal
          (Real.sqrt_pos.2 (by exact_mod_cast hn)) x y
      _ = ((K * L : ℝ≥0) : ℝ) * dist x y := by
        change (K : ℝ) * (Real.pi / 2 * dist x y) =
          ((K : ℝ) * (Real.pi / 2)) * dist x y
        ring
  have h := sphere_lipschitz_concentration n hn f (K * L) hLip
  calc
    HDP.psi2Norm
        (fun x ↦ f (scaleUnitSphere n hn x) -
          ∫ y, f (scaleUnitSphere n hn y)
            ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        ≤ sphereConcentrationConstant * ((K * L : ℝ≥0) : ℝ) := h
    _ = sphereConcentrationConstant * (K : ℝ) * (Real.pi / 2) := by
      change sphereConcentrationConstant * ((K : ℝ) * (Real.pi / 2)) = _
      ring

/-- The scaled copy of a subset of the unit sphere in the ambient Euclidean space.

**Lean implementation helper.** -/
def scaledSphereSet (n : ℕ)
    (A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
    Real.sqrt n • (x : EuclideanSpace ℝ (Fin n))) '' A

/-- Shows that scaled sphere set is nonempty.

**Lean implementation helper.** -/
lemma scaledSphereSet_nonempty {n : ℕ}
    {A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hA : A.Nonempty) : (scaledSphereSet n A).Nonempty :=
  hA.image _

/-- Any set occupying at least half the sphere has exponentially large metric blow-ups.

**Book Lemma 5.1.6.** -/
theorem sphere_blowUp
    (n : ℕ) (hn : 0 < n)
    (A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hAmeas : MeasurableSet A) (_hAne : A.Nonempty)
    (hAhalf : (1 / 2 : ℝ) ≤
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))).real A)
    {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | 2 * sphereConcentrationConstant + t <
          infDist (Real.sqrt n • (x : EuclideanSpace ℝ (Fin n)))
            (scaledSphereSet n A)} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 / sphereConcentrationConstant ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z ↦ infDist z (scaledSphereSet n A)
  have hF : LipschitzWith (1 : ℝ≥0) F :=
    Metric.lipschitz_infDist_pt (scaledSphereSet n A)
  have hsub := sphere_lipschitz_subGaussian_ambient n hn F 1 hF
  have hnorm := sphere_lipschitz_concentration_ambient n hn F 1 hF
  let D : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
    fun x ↦ F (Real.sqrt n • (x : EuclideanSpace ℝ (Fin n)))
  have hDzero : ∀ x ∈ A, D x = 0 := by
    intro x hx
    apply infDist_zero_of_mem
    exact ⟨x, hx, rfl⟩
  simpa [D, F, scaledSphereObservable] using
    blowUp_of_centered_concentration hAmeas hAhalf
      ((measurable_scaledSphereObservable hF.continuous).aemeasurable)
      (Filter.Eventually.of_forall fun _ ↦ infDist_nonneg) hDzero
      sphereConcentrationConstant_pos hsub (by simpa using hnorm) ht

end

end HDP.Chapter5

end Source_03_SphericalBlowUp

/-! ## Material formerly in `04_ConcentrationCenters.lean` -/

section Source_04_ConcentrationCenters

/-!
# Centers of concentration

This file formalizes Remark 5.2.1 and the load-bearing Exercises 5.6 and
5.10.  A median is defined measure-theoretically.  The comparison with the
mean is proved by integrating on a half-mass set; the comparison with an
`Lᵖ` norm uses Minkowski and the Chapter 2 sub-Gaussian moment bound.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace HDP.Chapter5

noncomputable section

/-- A measure-theoretic median of a real random variable. The use of `Measure.real` makes both
half-mass inequalities real-valued.

**Book Remark 5.2.1.** -/
def IsMedian {T : Type*} [MeasurableSpace T]
    (X : T → ℝ) (M : ℝ) (μ : Measure T) : Prop :=
  (1 / 2 : ℝ) ≤ μ.real {x | X x ≤ M} ∧
    (1 / 2 : ℝ) ≤ μ.real {x | M ≤ X x}

/-- Every real probability measure has a median. The construction takes the
infimum of the points where the CDF reaches one half. Right continuity gives
the lower-half inequality, while the left limit controls the open lower tail
and hence gives the upper-half inequality.

**Book pages 145–146 (median existence used in Remark 5.2.1).** -/
theorem exists_measureMedian (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ M : ℝ, (1 / 2 : ℝ) ≤ ν.real (Set.Iic M) ∧
      (1 / 2 : ℝ) ≤ ν.real (Set.Ici M) := by
  let S : Set ℝ := {x | (1 / 2 : ℝ) ≤ cdf ν x}
  have hSne : S.Nonempty := by
    have hev : ∀ᶠ x : ℝ in atTop, (3 / 4 : ℝ) < cdf ν x :=
      (tendsto_order.1 (tendsto_cdf_atTop ν)).1 (3 / 4) (by norm_num)
    obtain ⟨a, ha⟩ := eventually_atTop.1 hev
    refine ⟨a, ?_⟩
    exact (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4).trans
      (ha a le_rfl).le
  have hSbdd : BddBelow S := by
    have hev : ∀ᶠ x : ℝ in atBot, cdf ν x < (1 / 2 : ℝ) :=
      (tendsto_order.1 (tendsto_cdf_atBot ν)).2 (1 / 2) (by norm_num)
    obtain ⟨a, ha⟩ := eventually_atBot.1 hev
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hxa
    have hle : x ≤ a := le_of_not_ge hxa
    exact (not_lt_of_ge hx) (ha x hle)
  let M : ℝ := sInf S
  have hbelow (x : ℝ) (hx : x < M) :
      cdf ν x < (1 / 2 : ℝ) := by
    apply lt_of_not_ge
    intro hxhalf
    have hxS : x ∈ S := hxhalf
    exact (not_le_of_gt hx) (csInf_le hSbdd hxS)
  have habove (x : ℝ) (hx : M < x) :
      (1 / 2 : ℝ) ≤ cdf ν x := by
    obtain ⟨s, hsS, hsx⟩ :=
      (csInf_lt_iff hSbdd hSne).1 hx
    exact hsS.trans (monotone_cdf ν hsx.le)
  have hleft :
      Function.leftLim (cdf ν) M ≤ (1 / 2 : ℝ) := by
    rw [(monotone_cdf ν).leftLim_eq_sSup
      (Filter.NeBot.ne (nhdsLT_neBot M))]
    apply csSup_le
    · exact (nonempty_Iio : (Set.Iio M).Nonempty).image _
    · rintro y ⟨x, hx, rfl⟩
      exact (hbelow x hx).le
  have hright : (1 / 2 : ℝ) ≤ cdf ν M := by
    rw [← (cdf ν).rightLim_eq M,
      (monotone_cdf ν).rightLim_eq_sInf
        (Filter.NeBot.ne (nhdsGT_neBot M))]
    apply le_csInf
    · exact (nonempty_Ioi : (Set.Ioi M).Nonempty).image _
    · rintro y ⟨x, hx, rfl⟩
      exact habove x hx
  refine ⟨M, ?_, ?_⟩
  · simpa [cdf_eq_real] using hright
  · rw [measureReal_def, ← measure_cdf ν,
      (cdf ν).measure_Ici (tendsto_cdf_atTop ν),
      ENNReal.toReal_ofReal]
    · linarith
    · linarith

/-- Every a.e.-measurable real random variable on a probability space has a
measure-theoretic median, including variables with atoms.

**Book pages 145–146 (median existence used in Remark 5.2.1).** -/
theorem exists_isMedian
    {T : Type*} [MeasurableSpace T] {μ : Measure T}
    [IsProbabilityMeasure μ] (X : T → ℝ) (hX : AEMeasurable X μ) :
    ∃ M : ℝ, IsMedian X M μ := by
  let ν : Measure ℝ := μ.map X
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hX
  obtain ⟨M, hleft, hright⟩ := exists_measureMedian ν
  refine ⟨M, ?_, ?_⟩
  · change (1 / 2 : ℝ) ≤ μ.real (X ⁻¹' Set.Iic M)
    rw [← MeasureTheory.map_measureReal_apply_of_aemeasurable hX
      measurableSet_Iic]
    simpa [ν] using hleft
  · change (1 / 2 : ℝ) ≤ μ.real (X ⁻¹' Set.Ici M)
    rw [← MeasureTheory.map_measureReal_apply_of_aemeasurable hX
      measurableSet_Ici]
    simpa [ν] using hright

/-- If `|C|` is at least `d` on a set of mass at least one half, then `d` is at most twice the
`ψ₂` norm of `C`.

**Lean implementation helper.** -/
private lemma le_two_psi2Norm_of_half_abs_lower
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {C : T → ℝ}
    (hCm : AEMeasurable C μ) (hC : HDP.SubGaussian C μ)
    {A : Set T} (hAmeas : MeasurableSet A)
    (hAhalf : (1 / 2 : ℝ) ≤ μ.real A)
    {d : ℝ} (hd : 0 ≤ d) (hpoint : ∀ x ∈ A, d ≤ |C x|) :
    d ≤ 2 * HDP.psi2Norm C μ := by
  have hCmem : MemLp C 1 μ := by
    simpa using hC.memLp hCm (p := (1 : ℝ)) (le_refl 1)
  have hCint : Integrable C μ := hCmem.integrable (le_refl 1)
  have hsetLower : d * μ.real A ≤ ∫ x in A, |C x| ∂μ := by
    have hconst : IntegrableOn (fun _ : T ↦ d) A μ :=
      (integrable_const d).integrableOn
    have habs : IntegrableOn (fun x ↦ |C x|) A μ := hCint.abs.integrableOn
    have h := setIntegral_mono_on hconst habs hAmeas hpoint
    simpa [MeasureTheory.integral_const, hAmeas, mul_comm] using h
  have hsetUpper : (∫ x in A, |C x| ∂μ) ≤ ∫ x, |C x| ∂μ := by
    exact setIntegral_le_integral hCint.abs
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg (C x))
  have hdhalf : d / 2 ≤ ∫ x, |C x| ∂μ := by
    calc
      d / 2 ≤ d * μ.real A := by
        nlinarith [mul_le_mul_of_nonneg_left hAhalf hd]
      _ ≤ ∫ x in A, |C x| ∂μ := hsetLower
      _ ≤ ∫ x, |C x| ∂μ := hsetUpper
  have hmom := hC.moment_bound hCm (p := (1 : ℝ)) (le_refl 1)
  have hL1 : (∫ x, |C x| ∂μ) ≤ HDP.psi2Norm C μ := by
    have heq : (∫ x, |C x| ∂μ) = HDP.Chapter1.lpNormRV C 1 μ := by
      rw [HDP.Chapter1.lpNormRV]
      simp only [div_one, Real.rpow_one]
    rw [heq]
    simpa using hmom
  linarith

/-- A median differs from the mean by at most twice the centered `ψ₂` norm.

**Book Remark 5.2.1.** -/
theorem median_sub_mean_le_two_psi2Norm
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {X : T → ℝ}
    (hXm : Measurable X) (_hXint : Integrable X μ) {M : ℝ}
    (hM : IsMedian X M μ)
    (hC : HDP.SubGaussian
      (fun x ↦ X x - ∫ y, X y ∂μ) μ) :
    |M - ∫ x, X x ∂μ| ≤
      2 * HDP.psi2Norm (fun x ↦ X x - ∫ y, X y ∂μ) μ := by
  let m : ℝ := ∫ x, X x ∂μ
  let C : T → ℝ := fun x ↦ X x - m
  have hCm : AEMeasurable C μ := hXm.aemeasurable.sub_const m
  by_cases hMm : m ≤ M
  · have hset : MeasurableSet {x | M ≤ X x} :=
      measurableSet_le measurable_const hXm
    have hp := le_two_psi2Norm_of_half_abs_lower hCm hC hset hM.2
      (sub_nonneg.mpr hMm) (fun x hx ↦ by
        change M - m ≤ |X x - m|
        exact (sub_le_sub_right hx m).trans (le_abs_self _))
    simpa [C, m, abs_of_nonneg (sub_nonneg.mpr hMm)] using hp
  · have hMm' : M ≤ m := le_of_not_ge hMm
    have hset : MeasurableSet {x | X x ≤ M} :=
      measurableSet_le hXm measurable_const
    have hp := le_two_psi2Norm_of_half_abs_lower hCm hC hset hM.1
      (sub_nonneg.mpr hMm') (fun x hx ↦ by
        change m - M ≤ |X x - m|
        have : X x - m ≤ M - m := sub_le_sub_right hx m
        rw [abs_of_nonpos (this.trans (sub_nonpos.mpr hMm'))]
        linarith)
    simpa [C, m, abs_of_nonpos (sub_nonpos.mpr hMm')] using hp

/-- Explicit comparison constant for replacing the mean by a median.

**Lean implementation helper.** -/
def medianCenterConstant : ℝ :=
  1 + 2 / Real.sqrt (Real.log 2)

/-- Shows that median center constant is positive.

**Lean implementation helper.** -/
theorem medianCenterConstant_pos : 0 < medianCenterConstant := by
  dsimp [medianCenterConstant]
  positivity

/-- Centering at a median costs only the explicit universal factor `1 + 2 / √(log 2)` in `ψ₂`.

**Book Remark 5.2.1.** -/
theorem exercise_5_6_median_center_le_mean_center
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {X : T → ℝ}
    (hXm : Measurable X) (hXint : Integrable X μ) {M : ℝ}
    (hM : IsMedian X M μ)
    (hC : HDP.SubGaussian
      (fun x ↦ X x - ∫ y, X y ∂μ) μ) :
    HDP.SubGaussian (fun x ↦ X x - M) μ ∧
      HDP.psi2Norm (fun x ↦ X x - M) μ ≤
        medianCenterConstant *
          HDP.psi2Norm (fun x ↦ X x - ∫ y, X y ∂μ) μ := by
  let m : ℝ := ∫ x, X x ∂μ
  let C : T → ℝ := fun x ↦ X x - m
  let a : ℝ := m - M
  have hCm : AEMeasurable C μ := hXm.aemeasurable.sub_const m
  have haSub : HDP.SubGaussian (fun _ : T ↦ a) μ :=
    (HDP.psi2Norm_le_of_bounded (X := fun _ : T ↦ a) (M := |a| + 1)
      (by positivity) (Filter.Eventually.of_forall fun _ ↦ by linarith)).1
  have hsumSub := HDP.SubGaussian.add hCm (aemeasurable_const (b := a)) hC haSub
  have htri := HDP.psi2Norm_add_le hCm (aemeasurable_const (b := a)) hC haSub
  have hshift := median_sub_mean_le_two_psi2Norm hXm hXint hM hC
  have hfun : (fun x ↦ X x - M) = fun x ↦ C x + a := by
    funext x
    simp [C, a, m]
  constructor
  · simpa only [hfun] using hsumSub
  · rw [hfun]
    calc
      HDP.psi2Norm (fun x ↦ C x + a) μ
          ≤ HDP.psi2Norm C μ + HDP.psi2Norm (fun _ : T ↦ a) μ := htri
      _ = HDP.psi2Norm C μ + |a| / Real.sqrt (Real.log 2) := by
        rw [HDP.psi2Norm_const]
      _ ≤ HDP.psi2Norm C μ +
          (2 * HDP.psi2Norm C μ) / Real.sqrt (Real.log 2) := by
        gcongr
        simpa [a, m, abs_sub_comm] using hshift
      _ = medianCenterConstant * HDP.psi2Norm C μ := by
        simp only [medianCenterConstant]
        ring

/-- This is the converse comparison, obtained by applying the Chapter 2 centering lemma to
`X-M`.

**Book Exercise 5.6.** -/
theorem exercise_5_6_mean_center_le_median_center
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {X : T → ℝ}
    (hXm : AEMeasurable X μ) (hXint : Integrable X μ) (M : ℝ)
    (hY : HDP.SubGaussian (fun x ↦ X x - M) μ) :
    HDP.SubGaussian (fun x ↦ X x - ∫ y, X y ∂μ) μ ∧
      HDP.psi2Norm (fun x ↦ X x - ∫ y, X y ∂μ) μ ≤
        (1 + 1 / Real.sqrt (Real.log 2)) *
          HDP.psi2Norm (fun x ↦ X x - M) μ := by
  have hYm : AEMeasurable (fun x ↦ X x - M) μ := hXm.sub_const M
  have hcenter := HDP.psi2Norm_centering hYm hY
  have hmean : (∫ x, X x - M ∂μ) = (∫ x, X x ∂μ) - M := by
    rw [integral_sub hXint (integrable_const M)]
    simp
  have hfun :
      (fun x ↦ (X x - M) - ∫ y, X y - M ∂μ) =
        (fun x ↦ X x - ∫ y, X y ∂μ) := by
    funext x
    rw [hmean]
    ring
  simpa only [hfun] using hcenter

/-- On a probability space the real `Lᵖ` norm of a constant is its absolute value (for positive
finite `p`).

**Lean implementation helper.** -/
private lemma lpNormRV_const
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] (c : ℝ) {p : ℝ} (hp : 0 < p) :
    HDP.Chapter1.lpNormRV (fun _ : T ↦ c) p μ = |c| := by
  rw [HDP.Chapter1.lpNormRV]
  simp [MeasureTheory.integral_const, hp.ne']

/-- The `Lᵖ` norm differs from a nonnegative mean by at most the `Lᵖ` norm of the centered
variable.

**Lean implementation helper.** -/
private lemma lpNormRV_sub_mean_le_center
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {Z : T → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hZ : MemLp Z (ENNReal.ofReal p) μ)
    (hmean : 0 ≤ ∫ x, Z x ∂μ) :
    |HDP.Chapter1.lpNormRV Z p μ - ∫ x, Z x ∂μ| ≤
      HDP.Chapter1.lpNormRV
        (fun x ↦ Z x - ∫ y, Z y ∂μ) p μ := by
  let m : ℝ := ∫ x, Z x ∂μ
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hconst : MemLp (fun _ : T ↦ m) (ENNReal.ofReal p) μ :=
    memLp_const m
  have hcenter : MemLp (fun x ↦ Z x - m) (ENNReal.ofReal p) μ :=
    hZ.sub hconst
  have htri := HDP.Chapter1.minkowski_Lp hp hcenter hconst
  have hdecomp : (fun x ↦ (Z x - m) + m) = Z := by
    funext x
    simp
  rw [hdecomp, lpNormRV_const m hp0] at htri
  have hmeanAbs : |m| = m := abs_of_nonneg hmean
  rw [hmeanAbs] at htri
  have hmean_le_l1 : m ≤ HDP.Chapter1.lpNormRV Z 1 μ := by
    have habs : |m| ≤ ∫ x, |Z x| ∂μ := by
      dsimp [m]
      exact abs_integral_le_integral_abs
    have hL1 : (∫ x, |Z x| ∂μ) = HDP.Chapter1.lpNormRV Z 1 μ := by
      rw [HDP.Chapter1.lpNormRV]
      simp only [div_one, Real.rpow_one]
    rwa [hmeanAbs, hL1] at habs
  have hmono : HDP.Chapter1.lpNormRV Z 1 μ ≤
      HDP.Chapter1.lpNormRV Z p μ :=
    HDP.Chapter1.exercise_1_11a one_pos hp hZ
  rw [abs_of_nonneg (sub_nonneg.mpr (hmean_le_l1.trans hmono))]
  linarith

/-- Concentration may be centered at the `Lᵖ` norm. The real-valued wrapper carries the `MemLp`
hypothesis guaranteeing finiteness.

**Book Remark 5.2.1.** -/
theorem exercise_5_10_lp_center
    {T : Type*} {mT : MeasurableSpace T} {μ : Measure T}
    [IsProbabilityMeasure μ] {Z : T → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hZm : AEMeasurable Z μ)
    (hZp : MemLp Z (ENNReal.ofReal p) μ)
    (hmean : 0 ≤ ∫ x, Z x ∂μ)
    (hC : HDP.SubGaussian
      (fun x ↦ Z x - ∫ y, Z y ∂μ) μ) :
    HDP.SubGaussian
        (fun x ↦ Z x - HDP.Chapter1.lpNormRV Z p μ) μ ∧
      HDP.psi2Norm
          (fun x ↦ Z x - HDP.Chapter1.lpNormRV Z p μ) μ ≤
        (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt p *
          HDP.psi2Norm (fun x ↦ Z x - ∫ y, Z y ∂μ) μ := by
  let m : ℝ := ∫ x, Z x ∂μ
  let q : ℝ := HDP.Chapter1.lpNormRV Z p μ
  let C : T → ℝ := fun x ↦ Z x - m
  let a : ℝ := m - q
  have hCm : AEMeasurable C μ := hZm.sub_const m
  have haSub : HDP.SubGaussian (fun _ : T ↦ a) μ :=
    (HDP.psi2Norm_le_of_bounded (X := fun _ : T ↦ a) (M := |a| + 1)
      (by positivity) (Filter.Eventually.of_forall fun _ ↦ by linarith)).1
  have hsumSub := HDP.SubGaussian.add hCm (aemeasurable_const (b := a)) hC haSub
  have htri := HDP.psi2Norm_add_le hCm (aemeasurable_const (b := a)) hC haSub
  have hdist := lpNormRV_sub_mean_le_center hp hZp hmean
  have hmom := hC.moment_bound hCm hp
  have hshift : |a| ≤ Real.sqrt p * HDP.psi2Norm C μ := by
    calc
      |a| = |q - m| := by simp [a, q, m, abs_sub_comm]
      _ ≤ HDP.Chapter1.lpNormRV C p μ := by simpa [C, q, m] using hdist
      _ ≤ HDP.psi2Norm C μ * Real.sqrt p := hmom
      _ = Real.sqrt p * HDP.psi2Norm C μ := mul_comm _ _
  have hsqrt : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr hp
  have hfun : (fun x ↦ Z x - q) = fun x ↦ C x + a := by
    funext x
    simp [C, a, m, q]
  constructor
  · rw [hfun]
    exact hsumSub
  · rw [hfun]
    calc
      HDP.psi2Norm (fun x ↦ C x + a) μ
          ≤ HDP.psi2Norm C μ + HDP.psi2Norm (fun _ : T ↦ a) μ := htri
      _ = HDP.psi2Norm C μ + |a| / Real.sqrt (Real.log 2) := by
        rw [HDP.psi2Norm_const]
      _ ≤ HDP.psi2Norm C μ +
          (Real.sqrt p * HDP.psi2Norm C μ) /
            Real.sqrt (Real.log 2) := by gcongr
      _ ≤ Real.sqrt p * HDP.psi2Norm C μ +
          (Real.sqrt p * HDP.psi2Norm C μ) /
            Real.sqrt (Real.log 2) := by
        gcongr
        nlinarith [HDP.psi2Norm_nonneg C μ]
      _ = (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt p *
          HDP.psi2Norm C μ := by ring

end

end HDP.Chapter5

end Source_04_ConcentrationCenters

/-! ## Material formerly in `05_GaussianConcentration.lean` -/

section Source_05_GaussianConcentration

/-!
# Gaussian concentration

The analytic input is the already verified Prékopa--Leindler development in
`MatrixConcentration.Appendix_GaussianConcentration`.  This file supplies the
real Euclidean, `HasSubgaussianMGF`, `ψ₂`, and tail interfaces used by the
book.  No Gaussian isoperimetric theorem from the source-level appendix is used.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace BigOperators

namespace HDP.Chapter5

noncomputable section

/-- Product standard Gaussian measure in coordinate form. -/
abbrev gaussianPiMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n ↦ gaussianReal 0 1

/-- Center a real observable under the coordinate standard Gaussian law.

**Lean implementation helper.** -/
def gaussianCentered {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : Fin n → ℝ) : ℝ :=
  F (WithLp.toLp 2 z) -
    ∫ y, F (WithLp.toLp 2 y) ∂gaussianPiMeasure n

/-- A `K`-Lipschitz function on Euclidean `L²` space changes by at most `K` times the square root of the coordinatewise squared differences.

**Lean implementation helper.** -/
private lemma euclidean_lipschitz_to_coordinate
    {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (x y : Fin n → ℝ) :
    |F (WithLp.toLp 2 x) - F (WithLp.toLp 2 y)| ≤
      (K : ℝ) * Real.sqrt (∑ k, (x k - y k) ^ 2) := by
  have h := hF.dist_le_mul (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [Real.dist_eq] at h
  simpa only [PiLp.dist_eq_of_L2, Real.dist_eq, sq_abs] using h

/-- A positive-constant `K`-Lipschitz functional of a finite standard Gaussian vector has
centered sub-Gaussian MGF with variance proxy `K²`.

**Book Theorem 5.2.3.** -/
theorem gaussian_lipschitz_hasSubgaussianMGF
    (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : ℝ) (hK : 0 < K)
    (hF : LipschitzWith ⟨K, hK.le⟩ F) :
    HasSubgaussianMGF (gaussianCentered F)
      ⟨K ^ 2, sq_nonneg K⟩ (gaussianPiMeasure n) := by
  let W : (Fin n → ℝ) → ℝ := fun z ↦ F (WithLp.toLp 2 z)
  let V : (Fin n → ℝ) → ℝ := fun z ↦ W z / K
  have hWm : Measurable W := hF.continuous.measurable.comp
    (WithLp.measurable_toLp 2 (Fin n → ℝ))
  have hVm : Measurable V := hWm.div_const K
  have hVLip : ∀ x y, |V x - V y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2) := by
    intro x y
    rw [show V x - V y = (W x - W y) / K by simp [V]; ring,
      abs_div, abs_of_pos hK]
    rw [div_le_iff₀ hK]
    have hraw := euclidean_lipschitz_to_coordinate hF x y
    change |F (WithLp.toLp 2 x) - F (WithLp.toLp 2 y)| ≤
      K * Real.sqrt (∑ k, (x k - y k) ^ 2) at hraw
    simpa only [W, mul_comm] using hraw
  have hV := MatrixConcentration.gaussian_lipschitz_hasSubgaussianMGF_one
    (Fin n) V hVLip hVm
  have hscaled := hV.const_mul K
  have hmean : (∫ y, V y ∂gaussianPiMeasure n) =
      (∫ y, W y ∂gaussianPiMeasure n) / K := by
    simp only [V, integral_div]
  have hfun : (fun z ↦ K *
      (V z - ∫ y, V y ∂gaussianPiMeasure n)) = gaussianCentered F := by
    funext z
    rw [hmean]
    simp [V, W, gaussianCentered]
    field_simp
  simpa only [hfun, NNReal.coe_one, mul_one] using hscaled

/-- A zero Lipschitz observable is constant, hence its centered version is identically zero.

**Lean implementation helper.** -/
private lemma gaussianCentered_eq_zero_of_lipschitz_zero
    {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : LipschitzWith 0 F) : gaussianCentered F = 0 := by
  have hconst : ∀ x, F x = F 0 := by
    intro x
    have h := hF.dist_le_mul x 0
    simp only [NNReal.coe_zero, zero_mul] at h
    exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
  funext z
  simp only [gaussianCentered, Pi.zero_apply]
  rw [hconst (WithLp.toLp 2 z)]
  have hfun : (fun y : Fin n → ℝ ↦ F (WithLp.toLp 2 y)) =
      fun _ ↦ F 0 := by
    funext y
    exact hconst _
  rw [hfun]
  simp

/-- The statement is zero-safe and uses an explicit universal constant.

**Book Theorem 5.2.3.** -/
theorem gaussian_lipschitz_concentration
    (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : ℝ≥0) (hF : LipschitzWith K F) :
    HDP.SubGaussian (gaussianCentered F) (gaussianPiMeasure n) ∧
      HDP.psi2Norm (gaussianCentered F) (gaussianPiMeasure n) ≤
        2 * Real.sqrt 5 * K := by
  by_cases hK0 : (K : ℝ) = 0
  · have hzero : gaussianCentered F = 0 := by
      apply gaussianCentered_eq_zero_of_lipschitz_zero
      have hKnn : K = 0 := NNReal.eq hK0
      simpa [hKnn] using hF
    have hsub : HDP.SubGaussian (gaussianCentered F) (gaussianPiMeasure n) := by
      rw [hzero]
      exact (HDP.psi2Norm_le_of_bounded (X := fun _ : Fin n → ℝ ↦ (0 : ℝ))
        (M := 1) zero_lt_one (Filter.Eventually.of_forall fun _ ↦ by simp)).1
    constructor
    · exact hsub
    · have hrawm : Measurable
          (fun z : Fin n → ℝ ↦ F (WithLp.toLp 2 z)) :=
        hF.continuous.measurable.comp
          (WithLp.measurable_toLp 2 (Fin n → ℝ))
      have hcm : AEMeasurable (gaussianCentered F) (gaussianPiMeasure n) :=
        hrawm.sub_const (∫ y, F (WithLp.toLp 2 y) ∂gaussianPiMeasure n) |>.aemeasurable
      have hz : HDP.psi2Norm (gaussianCentered F) (gaussianPiMeasure n) = 0 :=
        (HDP.psi2Norm_eq_zero_iff hcm hsub).2 (by rw [hzero])
      simp [hz, hK0]
  · have hK : 0 < (K : ℝ) := lt_of_le_of_ne K.property (Ne.symm hK0)
    have hmgf := gaussian_lipschitz_hasSubgaussianMGF n F K hK hF
    have h := psi2Norm_le_of_hasSubgaussianMGF_sq hK hmgf
    constructor
    · exact h.1
    · calc
        HDP.psi2Norm (gaussianCentered F) (gaussianPiMeasure n)
            ≤ Real.sqrt 5 * (2 * (K : ℝ)) := h.2
        _ = 2 * Real.sqrt 5 * K := by ring

/-- Gives the intrinsic `ψ₂` tail bound for a centered Lipschitz function of a standard Gaussian
vector, with an explicit absolute constant.

**Book (5.6).** -/
theorem gaussian_lipschitz_tail
    (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : ℝ≥0) (hF : LipschitzWith K F) {t : ℝ} (ht : 0 ≤ t) :
    gaussianPiMeasure n {z | t ≤ |gaussianCentered F z|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 /
          (HDP.psi2Norm (gaussianCentered F) (gaussianPiMeasure n)) ^ 2)) := by
  exact (gaussian_lipschitz_concentration n F K hF).1.tail_bound
    (hF.continuous.measurable.comp
      (WithLp.measurable_toLp 2 (Fin n → ℝ)) |>.sub_const _ |>.aemeasurable) ht

/-- Unlike `gaussian_lipschitz_tail`, the denominator here is the supplied Lipschitz constant,
not an endogenous norm. The statement is total at `K=0`.

**Book (5.6).** -/
theorem gaussian_lipschitz_tail_explicit
    (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : ℝ≥0) (hF : LipschitzWith K F) {t : ℝ} (ht : 0 ≤ t) :
    gaussianPiMeasure n {z | t ≤ |gaussianCentered F z|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 / (2 * Real.sqrt 5 * K) ^ 2)) := by
  have hconc := gaussian_lipschitz_concentration n F K hF
  have hm : AEMeasurable (gaussianCentered F) (gaussianPiMeasure n) :=
    (hF.continuous.measurable.comp
      (WithLp.measurable_toLp 2 (Fin n → ℝ))).sub_const _ |>.aemeasurable
  have hB : 0 ≤ 2 * Real.sqrt 5 * (K : ℝ) := by positivity
  exact tail_le_of_subGaussian_psi2Norm_le hm hconc.1 hB hconc.2 ht

/-- Gaussian linear functionals and the Euclidean norm are special cases of Gaussian
concentration.

**Book Example 5.2.4.** -/
theorem gaussian_norm_concentration (n : ℕ) :
    HDP.SubGaussian
        (gaussianCentered (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖))
        (gaussianPiMeasure n) ∧
      HDP.psi2Norm
          (gaussianCentered (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖))
          (gaussianPiMeasure n) ≤ 2 * Real.sqrt 5 := by
  have hnorm : LipschitzWith (1 : ℝ≥0)
      (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le x y
  simpa using gaussian_lipschitz_concentration n
    (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖) 1 hnorm

/-! ## Finite Gaussian maxima (Exercise 5.9) -/

/-- Maximum of a nonempty finite family of real functions.

**Lean implementation helper.** -/
def finiteMaximum {I T : Type*} [Fintype I] [Nonempty I]
    (f : I → T → ℝ) (x : T) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ f i x

/-- The pointwise maximum of a finite family of `K`-Lipschitz functions is again `K`-Lipschitz.

**Lean implementation helper.** -/
private lemma lipschitzWith_finiteMaximum
    {I T : Type*} [Fintype I] [Nonempty I] [PseudoMetricSpace T]
    {f : I → T → ℝ} {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i)) :
    LipschitzWith K (finiteMaximum f) := by
  unfold finiteMaximum
  have hsup : LipschitzWith K
      (Finset.univ.sup' Finset.univ_nonempty fun i ↦ f i) := by
    refine Finset.sup'_induction Finset.univ_nonempty (fun i ↦ f i) ?_ ?_
    · intro g hg h hh
      rw [show (g ⊔ h) = fun x ↦ max (g x) (h x) from rfl]
      simpa only [max_self] using hg.max hh
    · intro i _
      exact hf i
  have heq : (Finset.univ.sup' Finset.univ_nonempty fun i ↦ f i) =
      (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ f i x) := by
    funext x
    exact Finset.sup'_apply Finset.univ_nonempty (fun i ↦ f i) x
  rw [← heq]
  exact hsup

/-- An affine Gaussian family represented as linear functionals of a standard Gaussian vector.
This representation permits singular (degenerate) covariance matrices.

**Lean implementation helper.** -/
def gaussianAffineFamily {I : Type*} {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ)
    (i : I) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  b i + inner ℝ (a i) x

/-- Maximum row norm, the square root of the largest marginal variance in the affine Gaussian
representation.

**Lean implementation helper.** -/
def gaussianMaximumScale {I : Type*} [Fintype I] [Nonempty I] {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ ‖a i‖

/-- Shows that gaussian maximum scale is nonnegative.

**Lean implementation helper.** -/
lemma gaussianMaximumScale_nonneg
    {I : Type*} [Fintype I] [Nonempty I] {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) :
    0 ≤ gaussianMaximumScale a := by
  exact (norm_nonneg (a (Classical.choice inferInstance))).trans
    (Finset.le_sup' (fun i ↦ ‖a i‖) (Finset.mem_univ _))

/-- Each affine Gaussian coordinate functional has Lipschitz constant bounded by the maximum coefficient norm.

**Lean implementation helper.** -/
private lemma gaussianAffineFamily_lipschitz
    {I : Type*} [Fintype I] [Nonempty I] {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ) (i : I) :
    LipschitzWith ⟨gaussianMaximumScale a, gaussianMaximumScale_nonneg a⟩
      (gaussianAffineFamily a b i) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq]
  change |(b i + inner ℝ (a i) x) - (b i + inner ℝ (a i) y)| ≤ _
  have hinner : |inner ℝ (a i) (x - y)| ≤ ‖a i‖ * ‖x - y‖ := by
    simpa [Real.norm_eq_abs] using
      (@norm_inner_le_norm ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
        (a i) (x - y))
  calc
    |(b i + inner ℝ (a i) x) - (b i + inner ℝ (a i) y)|
        = |inner ℝ (a i) (x - y)| := by rw [inner_sub_right]; ring_nf
    _ ≤ ‖a i‖ * ‖x - y‖ := hinner
    _ ≤ gaussianMaximumScale a * ‖x - y‖ := by
      gcongr
      exact Finset.le_sup' (fun j ↦ ‖a j‖) (Finset.mem_univ i)
    _ = gaussianMaximumScale a * dist x y := by rw [dist_eq_norm]

/-- The maximum of a finite jointly Gaussian family, including degenerate covariance,
concentrates at the largest marginal standard deviation. The family is exposed through its exact
affine standard- Gaussian representation.

**Book Exercise 5.9.** -/
theorem exercise_5_9b_gaussian_maximum
    {I : Type*} [Fintype I] [Nonempty I] {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ) :
    let M : EuclideanSpace ℝ (Fin n) → ℝ :=
      finiteMaximum (gaussianAffineFamily a b)
    HDP.SubGaussian (gaussianCentered M) (gaussianPiMeasure n) ∧
      HDP.psi2Norm (gaussianCentered M) (gaussianPiMeasure n) ≤
        2 * Real.sqrt 5 * gaussianMaximumScale a := by
  dsimp only
  let K : ℝ≥0 := ⟨gaussianMaximumScale a, gaussianMaximumScale_nonneg a⟩
  have hM : LipschitzWith K (finiteMaximum (gaussianAffineFamily a b)) :=
    lipschitzWith_finiteMaximum (fun i ↦ gaussianAffineFamily_lipschitz a b i)
  have h := gaussian_lipschitz_concentration n
    (finiteMaximum (gaussianAffineFamily a b)) K hM
  change HDP.SubGaussian
      (gaussianCentered (finiteMaximum (gaussianAffineFamily a b)))
      (gaussianPiMeasure n) ∧
    HDP.psi2Norm (gaussianCentered (finiteMaximum (gaussianAffineFamily a b)))
      (gaussianPiMeasure n) ≤ 2 * Real.sqrt 5 * gaussianMaximumScale a at h
  exact h

/-- Independent standard coordinates are the special case of the corresponding exercise with
coefficient vectors from the standard basis.

**Book Exercise 5.9.** -/
theorem exercise_5_9a_standard_coordinate_maximum (n : ℕ) [Nonempty (Fin n)] :
    let M : EuclideanSpace ℝ (Fin n) → ℝ :=
      finiteMaximum (fun i : Fin n ↦ fun x ↦ x i)
    HDP.SubGaussian (gaussianCentered M) (gaussianPiMeasure n) ∧
      HDP.psi2Norm (gaussianCentered M) (gaussianPiMeasure n) ≤
        2 * Real.sqrt 5 := by
  dsimp only
  have hcoord : ∀ i : Fin n,
      LipschitzWith (1 : ℝ≥0) (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) := by
    intro i
    exact LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq]
      have h := PiLp.norm_apply_le (x - y) i
      simpa [Real.norm_eq_abs, dist_eq_norm] using h
  have hM := lipschitzWith_finiteMaximum hcoord
  simpa using gaussian_lipschitz_concentration n
    (finiteMaximum (fun i : Fin n ↦ fun x : EuclideanSpace ℝ (Fin n) ↦ x i)) 1 hM

end

end HDP.Chapter5

end Source_05_GaussianConcentration

/-! ## Material formerly in `06_DiscreteConcentration.lean` -/

section Source_06_DiscreteConcentration

/-!
# Discrete metric-probability spaces

This module supplies the concrete Hamming-cube and permutation models used in
§5.2.2.  The external concentration inequalities themselves are deliberately
isolated in the source-level `Appendix.lean`; the core model and all elementary
metric/probability facts below are fully proved.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace HDP.Chapter5

noncomputable section

/-- Normalized Hamming distance. The zero-coordinate case is defined safely as zero by real
division; concentration statements add a nonempty-index hypothesis.

**Lean implementation helper.** -/
def normalizedHammingDist {I A : Type*} [Fintype I] [DecidableEq A]
    (x y : I → A) : ℝ :=
  (∑ i : I, if x i = y i then (0 : ℝ) else 1) / Fintype.card I

/-- Computes normalized hamming dist when both inputs agree.

**Lean implementation helper.** -/
@[simp] theorem normalizedHammingDist_self
    {I A : Type*} [Fintype I] [DecidableEq A] (x : I → A) :
    normalizedHammingDist x x = 0 := by
  simp [normalizedHammingDist]

/-- Shows that normalized hamming dist is nonnegative.

**Lean implementation helper.** -/
theorem normalizedHammingDist_nonneg
    {I A : Type*} [Fintype I] [DecidableEq A] (x y : I → A) :
    0 ≤ normalizedHammingDist x y := by
  unfold normalizedHammingDist
  positivity

/-- Shows that normalized hamming dist is symmetric in its two arguments.

**Lean implementation helper.** -/
theorem normalizedHammingDist_comm
    {I A : Type*} [Fintype I] [DecidableEq A] (x y : I → A) :
    normalizedHammingDist x y = normalizedHammingDist y x := by
  simp only [normalizedHammingDist]
  congr 2
  funext i
  by_cases h : x i = y i
  · rw [if_pos h, if_pos h.symm]
  · have h' : ¬y i = x i := fun h' ↦ h h'.symm
    rw [if_neg h, if_neg h']

/-- Bounds normalized hamming dist by one.

**Lean implementation helper.** -/
theorem normalizedHammingDist_le_one
    {I A : Type*} [Fintype I] [DecidableEq A] (x y : I → A) :
    normalizedHammingDist x y ≤ 1 := by
  by_cases hI : Fintype.card I = 0
  · simp [normalizedHammingDist, hI]
  · have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Nat.pos_of_ne_zero hI
    rw [normalizedHammingDist, div_le_one hcard]
    calc
      (∑ i : I, if x i = y i then (0 : ℝ) else 1)
          ≤ ∑ _i : I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split <;> norm_num
      _ = Fintype.card I := by simp

/-- Proves the triangle inequality for normalized hamming dist.

**Lean implementation helper.** -/
theorem normalizedHammingDist_triangle
    {I A : Type*} [Fintype I] [Nonempty I] [DecidableEq A]
    (x y z : I → A) :
    normalizedHammingDist x z ≤
      normalizedHammingDist x y + normalizedHammingDist y z := by
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  rw [normalizedHammingDist, normalizedHammingDist, normalizedHammingDist,
    ← add_div]
  apply (div_le_div_iff_of_pos_right hcard).2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp_all

/-- The discrete Boolean cube. -/
abbrev HammingCube (n : ℕ) := Fin n → Bool

/-- Uniform probability measure on the Boolean cube.

**Lean implementation helper.** -/
def cubeUniformMeasure (n : ℕ) : Measure (HammingCube n) :=
  (PMF.uniformOfFintype (HammingCube n)).toMeasure

instance instIsProbabilityMeasureCubeUniform (n : ℕ) :
    IsProbabilityMeasure (cubeUniformMeasure n) := by
  unfold cubeUniformMeasure
  infer_instance

/-- A measurable subset of the Hamming cube has uniform mass equal to its relative cardinality.

**Lean implementation helper.** -/
theorem cubeUniformMeasure_apply (n : ℕ) (A : Set (HammingCube n))
    (hA : MeasurableSet A) [Fintype A] :
    cubeUniformMeasure n A = Fintype.card A / Fintype.card (HammingCube n) := by
  exact PMF.toMeasure_uniformOfFintype_apply A hA

/-- Uniform probability measure on the symmetric group. -/
instance instMeasurableSpacePermutation (n : ℕ) :
    MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The uniform probability measure on permutations of `Fin n`.

**Lean implementation helper.** -/
def permutationUniformMeasure (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance instIsProbabilityMeasurePermutationUniform (n : ℕ) :
    IsProbabilityMeasure (permutationUniformMeasure n) := by
  unfold permutationUniformMeasure
  infer_instance

/-- The source's normalized Hamming distance on permutations.

**Lean implementation helper.** -/
def permutationHammingDist (n : ℕ)
    (p q : Equiv.Perm (Fin n)) : ℝ :=
  normalizedHammingDist p q

/-- Computes permutation hamming dist when both inputs agree.

**Lean implementation helper.** -/
@[simp] theorem permutationHammingDist_self (n : ℕ)
    (p : Equiv.Perm (Fin n)) : permutationHammingDist n p p = 0 :=
  normalizedHammingDist_self p

/-- Shows that permutation hamming dist is symmetric in its two arguments.

**Lean implementation helper.** -/
theorem permutationHammingDist_comm (n : ℕ)
    (p q : Equiv.Perm (Fin n)) :
    permutationHammingDist n p q = permutationHammingDist n q p :=
  normalizedHammingDist_comm p q

/-- Proves the triangle inequality for permutation hamming dist.

**Lean implementation helper.** -/
theorem permutationHammingDist_triangle (n : ℕ) (hn : 0 < n)
    (p q r : Equiv.Perm (Fin n)) :
    permutationHammingDist n p r ≤
      permutationHammingDist n p q + permutationHammingDist n q r := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact normalizedHammingDist_triangle p q r

/-- A measurable set of permutations has uniform mass equal to its relative cardinality.

**Lean implementation helper.** -/
theorem permutationUniformMeasure_apply (n : ℕ)
    (A : Set (Equiv.Perm (Fin n))) (hA : MeasurableSet A) [Fintype A] :
    permutationUniformMeasure n A =
      Fintype.card A / Fintype.card (Equiv.Perm (Fin n)) := by
  exact PMF.toMeasure_uniformOfFintype_apply A hA

end

end HDP.Chapter5

end Source_06_DiscreteConcentration

/-! ## Material formerly in `07_RotationsAndGrassmannians.lean` -/

section Source_07_RotationsAndGrassmannians

/-!
# Random rotations and Grassmannians

This file supplies the genuine probability spaces used in §5.2.5--§5.3.
The normalized Haar laws are constructed from Mathlib's Haar measure on the
compact orthogonal groups.  The Grassmannian is represented faithfully by
orthogonal-projection matrices in the orbit of the coordinate projection.

The printed Remark 5.2.8 incorrectly places the uncorrected Gaussian polar
factor in `SO(n)`: its law is Haar on `O(n)`.  Accordingly the two Haar laws
are kept separate here.  A determinant correction is required when a random
orthogonal matrix is to be turned into a special-orthogonal one.
-/

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal BigOperators Matrix.Norms.Elementwise

namespace HDP.Chapter5

noncomputable section

/-! ## Compact orthogonal groups and normalized Haar probability -/

/- Reuse the source-neutral finite-matrix Borel structure from `Prelude.Matrix`.
Keeping these square-matrix compatibility names definitionally equal to the
shared instances prevents distinct measurable structures when later chapters
combine Gaussian matrix laws with the rotation/Grassmannian API. -/
instance instMeasurableSpaceRealSquareMatrix (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  HDP.instMeasurableSpaceRealMatrix

instance instBorelSpaceRealSquareMatrix (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  HDP.instBorelSpaceRealMatrix

/-- The real finite-dimensional orthogonal group is compact. -/
instance instCompactSpaceOrthogonalGroup (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) := by
  have hc : IsClosed
      (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) :=
    isClosed_unitary
  have hb : Bornology.IsBounded
      (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro U hU
    exact entrywise_sup_norm_bound_of_unitary hU
  exact isCompact_iff_compactSpace.mp <|
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc, hb⟩

instance instMeasurableSpaceOrthogonalGroup (n : ℕ) :
    MeasurableSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace
    {A : Matrix (Fin n) (Fin n) ℝ //
      A ∈ Matrix.orthogonalGroup (Fin n) ℝ})

instance instBorelSpaceOrthogonalGroup (n : ℕ) :
    BorelSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace
    {A : Matrix (Fin n) (Fin n) ℝ //
      A ∈ Matrix.orthogonalGroup (Fin n) ℝ})

/-- Canonical normalized Haar probability on `O(n)`.

**Book Remark 5.2.8.** -/
def orthogonalHaarMeasure (n : ℕ) :
    Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts
    (Matrix.orthogonalGroup (Fin n) ℝ))

instance instIsProbabilityMeasureOrthogonalHaar (n : ℕ) :
    IsProbabilityMeasure (orthogonalHaarMeasure n) := by
  refine ⟨?_⟩
  simpa [orthogonalHaarMeasure] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.orthogonalGroup (Fin n) ℝ))))

instance instIsHaarMeasureOrthogonalHaar (n : ℕ) :
    Measure.IsHaarMeasure (orthogonalHaarMeasure n) := by
  unfold orthogonalHaarMeasure
  infer_instance

/-- Haar probability is invariant under every fixed left rotation.

**Lean implementation helper.** -/
theorem orthogonalHaarMeasure_left_invariant (n : ℕ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : Set (Matrix.orthogonalGroup (Fin n) ℝ)) :
    orthogonalHaarMeasure n ((fun V ↦ U * V) ⁻¹' A) =
      orthogonalHaarMeasure n A :=
  measure_preimage_mul (orthogonalHaarMeasure n) U A

/-- The special orthogonal group is a closed subset of the compact matrix
space, hence compact. -/
instance instCompactSpaceSpecialOrthogonalGroup (n : ℕ) :
    CompactSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ) := by
  have hset :
      (Matrix.specialOrthogonalGroup (Fin n) ℝ :
          Set (Matrix (Fin n) (Fin n) ℝ)) =
        {A | A ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧ A.det = 1} := by
    ext A
    exact Matrix.mem_specialOrthogonalGroup_iff
  have hc : IsClosed
      (Matrix.specialOrthogonalGroup (Fin n) ℝ :
        Set (Matrix (Fin n) (Fin n) ℝ)) := by
    rw [hset]
    exact isClosed_unitary.inter
      (isClosed_singleton.preimage
        (continuous_id.matrix_det :
          Continuous (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A.det)))
  have hb : Bornology.IsBounded
      (Matrix.specialOrthogonalGroup (Fin n) ℝ :
        Set (Matrix (Fin n) (Fin n) ℝ)) := by
    rw [hset, isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro U hU
    exact entrywise_sup_norm_bound_of_unitary hU.1
  exact isCompact_iff_compactSpace.mp <|
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc, hb⟩

instance instMeasurableSpaceSpecialOrthogonalGroup (n : ℕ) :
    MeasurableSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace
    {A : Matrix (Fin n) (Fin n) ℝ //
      A ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ})

instance instBorelSpaceSpecialOrthogonalGroup (n : ℕ) :
    BorelSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace
    {A : Matrix (Fin n) (Fin n) ℝ //
      A ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ})

instance instContinuousInvSpecialOrthogonalGroup (n : ℕ) :
    ContinuousInv (Matrix.specialOrthogonalGroup (Fin n) ℝ) where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun U : Matrix.specialOrthogonalGroup (Fin n) ℝ ↦
      star (U.1 : Matrix (Fin n) (Fin n) ℝ))
    fun_prop

instance instIsTopologicalGroupSpecialOrthogonalGroup (n : ℕ) :
    IsTopologicalGroup (Matrix.specialOrthogonalGroup (Fin n) ℝ) where

/-- Canonical normalized Haar probability on `SO(n)`.

**Book Remark 5.2.8.** -/
def specialOrthogonalHaarMeasure (n : ℕ) :
    Measure (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts
    (Matrix.specialOrthogonalGroup (Fin n) ℝ))

instance instIsProbabilityMeasureSpecialOrthogonalHaar (n : ℕ) :
    IsProbabilityMeasure (specialOrthogonalHaarMeasure n) := by
  refine ⟨?_⟩
  simpa [specialOrthogonalHaarMeasure] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.specialOrthogonalGroup (Fin n) ℝ))))

instance instIsHaarMeasureSpecialOrthogonalHaar (n : ℕ) :
    Measure.IsHaarMeasure (specialOrthogonalHaarMeasure n) := by
  unfold specialOrthogonalHaarMeasure
  infer_instance

/-! ## The determinant correction from `O(n)` to `SO(n)` -/

/-- The determinant of a real orthogonal matrix has square `1`.

**Lean implementation helper.** -/
private lemma orthogonal_det_sq {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : U.1.det ^ 2 = 1 := by
  have h := congrArg Matrix.det
    ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp U.2)
  simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using h

/-- Reflection in the first coordinate. Its determinant is `-1`, so right multiplication by it
switches the two connected components of `O(n)`.

**Lean implementation helper.** -/
def firstCoordinateReflection (n : ℕ) (hn : 0 < n) :
    Matrix.orthogonalGroup (Fin n) ℝ := by
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨Matrix.diagonal (fun i ↦ if i = i₀ then -1 else 1), ?_⟩
  rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ]
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = i₀ <;> simp [hi]
  · simp [hij]

/-- Reflection of the first coordinate has determinant `-1`.

**Lean implementation helper.** -/
@[simp] theorem firstCoordinateReflection_det (n : ℕ) (hn : 0 < n) :
    (firstCoordinateReflection n hn).1.det = -1 := by
  let i₀ : Fin n := ⟨0, hn⟩
  change (Matrix.diagonal (fun i : Fin n ↦
    if i = i₀ then (-1 : ℝ) else 1)).det = -1
  rw [Matrix.det_diagonal]
  exact
    (Fintype.prod_ite_eq' i₀ (fun _ : Fin n ↦ (-1 : ℝ)))

/-- The canonical inclusion `SO(n) → O(n)`.

**Lean implementation helper.** -/
def specialToOrthogonal (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →*
      Matrix.orthogonalGroup (Fin n) ℝ where
  toFun U := ⟨U.1, U.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Correct an orthogonal matrix with negative determinant by multiplying it on the right by the
fixed first-coordinate reflection. This is the precise correction omitted by the printed the
corresponding remark.

**Book Remark 5.2.8.** -/
def orthogonalToSpecial (n : ℕ) (hn : 0 < n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  classical
  by_cases hdet : U.1.det = 1
  · exact ⟨U.1, ⟨U.2, hdet⟩⟩
  · have hdetneg : U.1.det = -1 := by
      have hfactor : (U.1.det - 1) * (U.1.det + 1) = 0 := by
        nlinarith [orthogonal_det_sq U]
      rcases mul_eq_zero.mp hfactor with h | h
      · exact (hdet (sub_eq_zero.mp h)).elim
      · linarith
    let R := firstCoordinateReflection n hn
    refine ⟨(U * R).1, ⟨(U * R).2, ?_⟩⟩
    change (U.1 * R.1).det = 1
    rw [Matrix.det_mul, hdetneg, firstCoordinateReflection_det]
    norm_num

/-- An orthogonal matrix is moved into the special orthogonal group by composing with the first-coordinate reflection exactly when its determinant is `-1`.

**Lean implementation helper.** -/
@[simp] theorem orthogonalToSpecial_val (n : ℕ) (hn : 0 < n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (orthogonalToSpecial n hn U).1 =
      if U.1.det = 1 then U.1
      else (U * firstCoordinateReflection n hn).1 := by
  classical
  by_cases hU : U.1.det = 1 <;> simp [orthogonalToSpecial, hU]

/-- Establishes measurability of orthogonal to special.

**Lean implementation helper.** -/
lemma measurable_orthogonalToSpecial (n : ℕ) (hn : 0 < n) :
    Measurable (orthogonalToSpecial n hn) := by
  classical
  apply Measurable.subtype_mk
  have hU : Measurable
      (fun U : Matrix.orthogonalGroup (Fin n) ℝ ↦
        (U.1 : Matrix (Fin n) (Fin n) ℝ)) :=
    continuous_subtype_val.measurable
  have hdet : Measurable
      (fun U : Matrix.orthogonalGroup (Fin n) ℝ ↦ U.1.det) :=
    continuous_subtype_val.matrix_det.measurable
  have hset : MeasurableSet
      {U : Matrix.orthogonalGroup (Fin n) ℝ | U.1.det = 1} :=
    measurableSet_eq_fun hdet measurable_const
  have hUR : Measurable
      (fun U : Matrix.orthogonalGroup (Fin n) ℝ ↦
        U.1 * (firstCoordinateReflection n hn).1) :=
    (continuous_subtype_val.mul continuous_const).measurable
  convert hU.ite hset hUR using 1
  · funext U
    exact orthogonalToSpecial_val n hn U

/-- Derives orthogonal to special from det one.

**Lean implementation helper.** -/
@[simp] theorem orthogonalToSpecial_of_det_one (n : ℕ) (hn : 0 < n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (hU : U.1.det = 1) :
    (orthogonalToSpecial n hn U).1 = U.1 := by
  simp [orthogonalToSpecial, hU]

/-- The map from the orthogonal group to the special orthogonal group is equivariant under left multiplication by special orthogonal matrices.

**Lean implementation helper.** -/
theorem orthogonalToSpecial_equivariant (n : ℕ) (hn : 0 < n)
    (S : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    orthogonalToSpecial n hn (specialToOrthogonal n S * U) =
      S * orthogonalToSpecial n hn U := by
  classical
  have hdet : ((specialToOrthogonal n S * U).1).det = U.1.det := by
    have hSdet : S.1.det = 1 := S.2.2
    change (S.1 * U.1).det = U.1.det
    rw [Matrix.det_mul, hSdet, one_mul]
  apply Subtype.ext
  by_cases hU : U.1.det = 1
  · have hSU : ((specialToOrthogonal n S * U).1).det = 1 := hdet.trans hU
    simp only [orthogonalToSpecial, hU, hSU]
    rfl
  · have hSU : ¬((specialToOrthogonal n S * U).1).det = 1 := by
      intro h
      exact hU (hdet.symm.trans h)
    simp only [orthogonalToSpecial, hU, hSU]
    change (S.1 * U.1) * (firstCoordinateReflection n hn).1 =
      S.1 * (U.1 * (firstCoordinateReflection n hn).1)
    rw [mul_assoc]

/-- Law obtained by applying the explicit determinant correction to Haar `O(n)`.

**Lean implementation helper.** -/
def determinantCorrectedOrthogonalMeasure (n : ℕ) (hn : 0 < n) :
    Measure (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  Measure.map (orthogonalToSpecial n hn) (orthogonalHaarMeasure n)

instance instIsProbabilityMeasureDeterminantCorrected (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (determinantCorrectedOrthogonalMeasure n hn) := by
  unfold determinantCorrectedOrthogonalMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_orthogonalToSpecial n hn).aemeasurable

instance instIsMulLeftInvariantDeterminantCorrected (n : ℕ) (hn : 0 < n) :
    Measure.IsMulLeftInvariant (determinantCorrectedOrthogonalMeasure n hn) := by
  rw [← forall_measure_preimage_mul_iff]
  intro S A hA
  have hf := measurable_orthogonalToSpecial n hn
  have hSA : MeasurableSet
      ((fun V : Matrix.specialOrthogonalGroup (Fin n) ℝ ↦ S * V) ⁻¹' A) :=
    (measurable_const_mul S hA)
  rw [determinantCorrectedOrthogonalMeasure,
    Measure.map_apply hf hSA, Measure.map_apply hf hA]
  rw [← orthogonalHaarMeasure_left_invariant n (specialToOrthogonal n S)
    ((orthogonalToSpecial n hn) ⁻¹' A)]
  congr 1
  ext U
  simp only [Set.mem_preimage]
  rw [orthogonalToSpecial_equivariant]

/-- The determinant-corrected Haar orthogonal matrix has exactly the normalized Haar law on
`SO(n)`.

**Book Remark 5.2.8.** -/
theorem determinantCorrectedOrthogonalMeasure_eq_specialOrthogonalHaar
    (n : ℕ) (hn : 0 < n) :
    determinantCorrectedOrthogonalMeasure n hn =
      specialOrthogonalHaarMeasure n := by
  have heq := Measure.isMulInvariant_eq_smul_of_compactSpace
    (determinantCorrectedOrthogonalMeasure n hn)
    (specialOrthogonalHaarMeasure n)
  have hmass := congrArg (fun μ : Measure
      (Matrix.specialOrthogonalGroup (Fin n) ℝ) ↦ μ Set.univ) heq
  have hscalar : Measure.haarScalarFactor
      (determinantCorrectedOrthogonalMeasure n hn)
      (specialOrthogonalHaarMeasure n) = 1 := by
    simpa using hmass.symm
  simpa [hscalar] using heq

/-- Equivalent `HasLaw` form of the corrected Haar construction.

**Book Chapter 5, p.157, Haar discussion.** -/
theorem orthogonalToSpecial_hasLaw (n : ℕ) (hn : 0 < n) :
    HasLaw (orthogonalToSpecial n hn) (specialOrthogonalHaarMeasure n)
      (orthogonalHaarMeasure n) := by
  refine ⟨(measurable_orthogonalToSpecial n hn).aemeasurable, ?_⟩
  exact determinantCorrectedOrthogonalMeasure_eq_specialOrthogonalHaar n hn

/-! ## Projection-matrix model of the Grassmannian -/

/-- Projection onto the first `m` coordinate axes. Public theorems using it assume `m ≤ n`; the
definition itself remains total.

**Lean implementation helper.** -/
def coordinateProjectionMatrix (n m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i ↦ if (i : ℕ) < m then 1 else 0

/-- The coordinate-projection matrix is diagonal, with ones on the first `m` coordinates and
zeros elsewhere.

**Lean implementation helper.** -/
@[simp] theorem coordinateProjectionMatrix_apply (n m : ℕ) (i j : Fin n) :
    coordinateProjectionMatrix n m i j =
      if i = j then (if (i : ℕ) < m then 1 else 0) else 0 := by
  rw [coordinateProjectionMatrix, Matrix.diagonal_apply]

/-- The diagonal coordinate-projection matrix is symmetric.

**Lean implementation helper.** -/
@[simp] theorem coordinateProjectionMatrix_transpose (n m : ℕ) :
    (coordinateProjectionMatrix n m)ᵀ = coordinateProjectionMatrix n m := by
  exact Matrix.diagonal_transpose _

/-- Computes coordinate projection matrix mul when both inputs agree.

**Lean implementation helper.** -/
@[simp] theorem coordinateProjectionMatrix_mul_self (n m : ℕ) :
    coordinateProjectionMatrix n m * coordinateProjectionMatrix n m =
      coordinateProjectionMatrix n m := by
  rw [coordinateProjectionMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> norm_num

/-- The ordinary real Grassmannian, represented by the orbit of the coordinate orthogonal
projection under `O(n)`. This representation identifies a subspace with its projection and
therefore handles the antipodal `m = 1` case correctly.

**Book Theorem 5.2.9.** -/
def Grassmannian (n m : ℕ) :=
  {P : Matrix (Fin n) (Fin n) ℝ //
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      P = U.1 * coordinateProjectionMatrix n m * U.1ᵀ}

instance instTopologicalSpaceGrassmannian (n m : ℕ) :
    TopologicalSpace (Grassmannian n m) :=
  inferInstanceAs (TopologicalSpace
    {P : Matrix (Fin n) (Fin n) ℝ //
      ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
        P = U.1 * coordinateProjectionMatrix n m * U.1ᵀ})

instance instMeasurableSpaceGrassmannian (n m : ℕ) :
    MeasurableSpace (Grassmannian n m) :=
  inferInstanceAs (MeasurableSpace
    {P : Matrix (Fin n) (Fin n) ℝ //
      ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
        P = U.1 * coordinateProjectionMatrix n m * U.1ᵀ})

instance instBorelSpaceGrassmannian (n m : ℕ) :
    BorelSpace (Grassmannian n m) :=
  inferInstanceAs (BorelSpace
    {P : Matrix (Fin n) (Fin n) ℝ //
      ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
        P = U.1 * coordinateProjectionMatrix n m * U.1ᵀ})

/-- Orbit map from a random rotation to its rotated coordinate subspace.

**Lean implementation helper.** -/
def grassmannOrbit (n m : ℕ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : Grassmannian n m :=
  ⟨U.1 * coordinateProjectionMatrix n m * U.1ᵀ, U, rfl⟩

/-- Establishes continuity of grassmann orbit.

**Lean implementation helper.** -/
lemma continuous_grassmannOrbit (n m : ℕ) :
    Continuous (grassmannOrbit n m) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ ↦
    U.1 * coordinateProjectionMatrix n m * U.1ᵀ)
  fun_prop

/-- Uniform probability on `G(n,m)`, obtained by pushing Haar `O(n)` through the orbit map.

**Book Theorem 5.2.9.** -/
def grassmannHaarMeasure (n m : ℕ) : Measure (Grassmannian n m) :=
  Measure.map (grassmannOrbit n m) (orthogonalHaarMeasure n)

instance instIsProbabilityMeasureGrassmannHaar (n m : ℕ) :
    IsProbabilityMeasure (grassmannHaarMeasure n m) := by
  unfold grassmannHaarMeasure
  exact Measure.isProbabilityMeasure_map
    (continuous_grassmannOrbit n m).measurable.aemeasurable

/-- The source metric on the Grassmannian: operator norm of the difference of orthogonal
projections.

**Book Theorem 5.2.9.** -/
def grassmannDistance {n m : ℕ} (P Q : Grassmannian n m) : ℝ :=
  HDP.matrixOpNorm (P.1 - Q.1)

/-- Shows that grassmann distance is nonnegative.

**Lean implementation helper.** -/
theorem grassmannDistance_nonneg {n m : ℕ} (P Q : Grassmannian n m) :
    0 ≤ grassmannDistance P Q :=
  HDP.matrixOpNorm_nonneg _

/-- Computes grassmann distance when both inputs agree.

**Lean implementation helper.** -/
@[simp] theorem grassmannDistance_self {n m : ℕ} (P : Grassmannian n m) :
    grassmannDistance P P = 0 := by
  simp [grassmannDistance]

/-- Shows that grassmann distance is symmetric in its two arguments.

**Lean implementation helper.** -/
theorem grassmannDistance_comm {n m : ℕ} (P Q : Grassmannian n m) :
    grassmannDistance P Q = grassmannDistance Q P := by
  rw [grassmannDistance, grassmannDistance,
    show Q.1 - P.1 = -(P.1 - Q.1) by abel, HDP.matrixOpNorm_neg]

/-- Orthogonal projection associated with a Grassmannian point.

**Book Chapter 5, p.157, Grassmann discussion.** -/
def randomProjection {n m : ℕ} (P : Grassmannian n m) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  HDP.matrixOperator P.1

/-- Shows that grassmann projection is Hermitian.

**Lean implementation helper.** -/
theorem grassmann_projection_isHermitian {n m : ℕ} (P : Grassmannian n m) :
    P.1.IsHermitian := by
  rcases P.2 with ⟨U, hU⟩
  rw [hU]
  rw [Matrix.isHermitian_iff_isSymm]
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
    coordinateProjectionMatrix_transpose]
  rw [← mul_assoc]

/-- Shows that grassmann projection is idempotent.

**Lean implementation helper.** -/
theorem grassmann_projection_isIdempotent {n m : ℕ} (P : Grassmannian n m) :
    P.1 * P.1 = P.1 := by
  rcases P.2 with ⟨U, hU⟩
  rw [hU]
  calc
    (U.1 * coordinateProjectionMatrix n m * U.1ᵀ) *
        (U.1 * coordinateProjectionMatrix n m * U.1ᵀ) =
        U.1 * coordinateProjectionMatrix n m * (U.1ᵀ * U.1) *
          coordinateProjectionMatrix n m * U.1ᵀ := by noncomm_ring
    _ = U.1 * coordinateProjectionMatrix n m * 1 *
          coordinateProjectionMatrix n m * U.1ᵀ := by
      rw [(Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2]
    _ = U.1 * coordinateProjectionMatrix n m * U.1ᵀ := by
      rw [mul_one, mul_assoc U.1 (coordinateProjectionMatrix n m),
        coordinateProjectionMatrix_mul_self]

/-- Shows that random projection is self-adjoint.

**Lean implementation helper.** -/
theorem randomProjection_isSelfAdjoint {n m : ℕ} (P : Grassmannian n m) :
    IsSelfAdjoint (randomProjection P) := by
  rw [randomProjection, HDP.matrixOperator_isSelfAdjoint_iff]
  exact grassmann_projection_isHermitian P

/-- Shows that random projection is idempotent.

**Lean implementation helper.** -/
theorem randomProjection_isIdempotent {n m : ℕ} (P : Grassmannian n m) :
    IsIdempotentElem (randomProjection P) := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro x
  change (P.1.toEuclideanLin ∘ₗ P.1.toEuclideanLin) x =
    P.1.toEuclideanLin x
  rw [← Matrix.toLpLin_mul_same, grassmann_projection_isIdempotent]

end

end HDP.Chapter5

end Source_07_RotationsAndGrassmannians

/-! ## Material formerly in `08_ContinuousMeasures.lean` -/

section Source_08_ContinuousMeasures

/-!
# Continuous cube and Euclidean-ball measures

This file proves the probability-integral transform for the standard
Gaussian directly from Mathlib's CDF and Stieltjes-measure APIs.  Taking
finite products gives a genuine Gaussian-to-cube transport, from which the
continuous-cube concentration theorem follows.  The target cube law is the
ordinary product of Lebesgue probability measures on `[0,1]`; it is not
defined as the push-forward whose equality we prove.  The second half of the
file constructs the genuine polar decomposition of normalized Lebesgue measure
on a Euclidean ball, proves its radial tail, and combines it with sphere
concentration to obtain the ball case of Theorem 5.2.10.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace BigOperators Topology Pointwise

namespace HDP.Chapter5

noncomputable section

private abbrev standardGaussianMeasure : Measure ℝ := gaussianReal 0 1

/-- The standard Gaussian CDF. -/
abbrev standardGaussianCDF : ℝ → ℝ :=
  ProbabilityTheory.cdf standardGaussianMeasure

/-- Shows that standard gaussian cdf is nonnegative.

**Lean implementation helper.** -/
lemma standardGaussianCDF_nonneg (x : ℝ) :
    0 ≤ standardGaussianCDF x :=
  ProbabilityTheory.cdf_nonneg standardGaussianMeasure x

/-- Bounds standard gaussian cdf by one.

**Lean implementation helper.** -/
lemma standardGaussianCDF_le_one (x : ℝ) :
    standardGaussianCDF x ≤ 1 :=
  ProbabilityTheory.cdf_le_one standardGaussianMeasure x

/-- The standard Gaussian CDF is strictly increasing. Positivity of every nonempty interval
follows from mutual absolute continuity with Lebesgue measure; no analytic formula for `erf` is
needed.

**Lean implementation helper.** -/
theorem standardGaussianCDF_strictMono : StrictMono standardGaussianCDF := by
  intro x y hxy
  have hvol : (volume : Measure ℝ) (Ioc x y) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hxy)
  have hgauss : standardGaussianMeasure (Ioc x y) ≠ 0 := by
    intro hzero
    exact hvol (gaussianReal_absolutelyContinuous' 0
      (by norm_num : (1 : ℝ≥0) ≠ 0) hzero)
  have hmeasure : standardGaussianMeasure (Ioc x y) =
      ENNReal.ofReal (standardGaussianCDF y - standardGaussianCDF x) := by
    rw [← ProbabilityTheory.measure_cdf standardGaussianMeasure,
      StieltjesFunction.measure_Ioc]
  have hof : ENNReal.ofReal
      (standardGaussianCDF y - standardGaussianCDF x) ≠ 0 := by
    rwa [← hmeasure]
  exact sub_pos.mp (ENNReal.ofReal_ne_zero_iff.mp hof)

/-- The standard Gaussian CDF is continuous.

**Lean implementation helper.** -/
theorem continuous_standardGaussianCDF : Continuous standardGaussianCDF := by
  rw [continuous_iff_continuousAt]
  intro x
  have hsingle :
      (ProbabilityTheory.cdf standardGaussianMeasure).measure {x} = 0 := by
    rw [ProbabilityTheory.measure_cdf standardGaussianMeasure]
    letI : NoAtoms standardGaussianMeasure :=
      noAtoms_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
    exact measure_singleton x
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsingle
  have hleft : Function.leftLim standardGaussianCDF x =
      standardGaussianCDF x := by
    apply le_antisymm
    · exact (ProbabilityTheory.monotone_cdf standardGaussianMeasure).leftLim_le le_rfl
    · linarith
  apply (ProbabilityTheory.monotone_cdf
    standardGaussianMeasure).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [hleft, StieltjesFunction.rightLim_eq]

/-- Shows that standard gaussian cdf is positive.

**Lean implementation helper.** -/
lemma standardGaussianCDF_pos (x : ℝ) :
    0 < standardGaussianCDF x := by
  exact lt_of_le_of_lt (standardGaussianCDF_nonneg (x - 1))
    (standardGaussianCDF_strictMono (by linarith))

/-- Proves the strict bound comparing standard gaussian cdf with one.

**Lean implementation helper.** -/
lemma standardGaussianCDF_lt_one (x : ℝ) :
    standardGaussianCDF x < 1 := by
  exact lt_of_lt_of_le (standardGaussianCDF_strictMono (by linarith : x < x + 1))
    (standardGaussianCDF_le_one (x + 1))

/-- The CDF bundled as a map into the unit interval.

**Lean implementation helper.** -/
def standardGaussianCDFUnit (x : ℝ) : unitInterval :=
  ⟨standardGaussianCDF x,
    standardGaussianCDF_nonneg x, standardGaussianCDF_le_one x⟩

/-- Establishes measurability of standard gaussian cdfunit.

**Lean implementation helper.** -/
lemma measurable_standardGaussianCDFUnit :
    Measurable standardGaussianCDFUnit := by
  exact continuous_standardGaussianCDF.subtype_mk _ |>.measurable

/-- Every probability level strictly between zero and one is attained by the standard Gaussian
cumulative distribution function.

**Lean implementation helper.** -/
private lemma exists_standardGaussianCDF_eq
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ x : ℝ, standardGaussianCDF x = t := by
  have hrange : t ∈ standardGaussianCDF '' (Set.univ : Set ℝ) := by
    apply isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop)
    · simp
    · simp
    · exact continuous_standardGaussianCDF.continuousOn
    · exact ProbabilityTheory.tendsto_cdf_atBot standardGaussianMeasure
    · exact ProbabilityTheory.tendsto_cdf_atTop standardGaussianMeasure
    · exact ⟨ht0, ht1⟩
  simpa only [Set.image_univ, Set.mem_range] using hrange

/-- The standard Gaussian CDF pushes the standard Gaussian law exactly to normalized Lebesgue
measure on `[0,1]`.

**Book Exercise 5.11.** -/
theorem map_standardGaussianCDFUnit :
    Measure.map standardGaussianCDFUnit standardGaussianMeasure =
      (volume : Measure unitInterval) := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply measurable_standardGaussianCDFUnit measurableSet_Iic,
    unitInterval.volume_Iic]
  rcases t with ⟨t, ht0, ht1⟩
  change standardGaussianMeasure
      {x : ℝ | standardGaussianCDF x ≤ t} = ENNReal.ofReal t
  rcases ht0.eq_or_lt with rfl | ht0
  · have hempty : {x : ℝ | standardGaussianCDF x ≤ 0} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · exact fun hx ↦ (not_le.mpr (standardGaussianCDF_pos x)) hx
      · exact False.elim
    rw [hempty, measure_empty, ENNReal.ofReal_zero]
  · rcases ht1.eq_or_lt with rfl | ht1
    · have huniv : {x : ℝ | standardGaussianCDF x ≤ 1} = Set.univ := by
        ext x
        simp [standardGaussianCDF_le_one]
      rw [huniv, measure_univ, ENNReal.ofReal_one]
    · obtain ⟨x, hx⟩ := exists_standardGaussianCDF_eq ht0 ht1
      have hset : {z : ℝ | standardGaussianCDF z ≤ t} = Iic x := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_Iic]
        rw [← hx, standardGaussianCDF_strictMono.le_iff_le]
      rw [hset, ← ProbabilityTheory.ofReal_cdf standardGaussianMeasure x]
      change ENNReal.ofReal (standardGaussianCDF x) = ENNReal.ofReal t
      rw [hx]

/-! ## Quantitative transport -/

/-- Bounds standard gaussian pdfreal by one.

**Lean implementation helper.** -/
private lemma standardGaussianPDFReal_le_one (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    rw [Real.one_le_sqrt]
    have hp := Real.pi_gt_three
    norm_num at *
    linarith
  have hcoeff : (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ ≤ (1 : ℝ) :=
    inv_le_one_of_one_le₀ hsqrt
  have hexp : Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ≥0))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [sq_nonneg x]
  have hexp0 : 0 ≤ Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ≥0))) := by
    positivity
  exact (mul_le_mul hcoeff hexp hexp0 (by norm_num)).trans_eq (mul_one 1)

/-- Bounds standard gaussian measure by volume.

**Lean implementation helper.** -/
private lemma standardGaussianMeasure_le_volume :
    standardGaussianMeasure ≤ (volume : Measure ℝ) := by
  change gaussianReal 0 1 ≤ (volume : Measure ℝ)
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    volume.withDensity (gaussianPDF 0 1)
        ≤ volume.withDensity (fun _ : ℝ ↦ 1) := by
      apply withDensity_mono
      filter_upwards [] with x
      rw [gaussianPDF, ENNReal.ofReal_le_one]
      exact standardGaussianPDFReal_le_one x
    _ = volume := withDensity_one

/-- Bounds standard gaussian cdf sub by sub.

**Lean implementation helper.** -/
private lemma standardGaussianCDF_sub_le_sub {x y : ℝ} (hxy : x ≤ y) :
    standardGaussianCDF y - standardGaussianCDF x ≤ y - x := by
  have hm : ENNReal.ofReal
      (standardGaussianCDF y - standardGaussianCDF x) =
      standardGaussianMeasure (Ioc x y) := by
    rw [← ProbabilityTheory.measure_cdf standardGaussianMeasure,
      StieltjesFunction.measure_Ioc]
  have hle : standardGaussianMeasure (Ioc x y) ≤
      (volume : Measure ℝ) (Ioc x y) :=
    standardGaussianMeasure_le_volume (Ioc x y)
  rw [Real.volume_Ioc] at hle
  rw [← hm] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hxy)).mp hle

/-- The Gaussian CDF transport is globally one-Lipschitz. The sharp constant is smaller, but one
is the convenient dimension-free bound used below.

**Book Exercise 5.12(a).** -/
theorem standardGaussianCDF_lipschitz :
    LipschitzWith (1 : ℝ≥0) standardGaussianCDF := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm (standardGaussianCDF x), abs_sub_comm x,
      abs_of_nonneg
      (sub_nonneg.mpr ((ProbabilityTheory.monotone_cdf standardGaussianMeasure) hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact standardGaussianCDF_sub_le_sub hxy
  · rw [abs_of_nonneg
        (sub_nonneg.mpr ((ProbabilityTheory.monotone_cdf standardGaussianMeasure) hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact standardGaussianCDF_sub_le_sub hyx

/-! ## Finite products: the continuous cube -/

/-- The product-coordinate model of the continuous unit cube. -/
abbrev ContinuousCube (n : ℕ) := Fin n → unitInterval

/-- Ordinary product Lebesgue probability measure on `[0,1]^n`.

**Lean implementation helper.** -/
def continuousCubeMeasure (n : ℕ) : Measure (ContinuousCube n) :=
  Measure.pi fun _ : Fin n ↦ (volume : Measure unitInterval)

instance instIsProbabilityMeasureContinuousCube (n : ℕ) :
    IsProbabilityMeasure (continuousCubeMeasure n) := by
  unfold continuousCubeMeasure
  infer_instance

/-- The coordinatewise standard Gaussian CDF map from `R^n` into the continuous cube `[0,1]^n`.

**Lean implementation helper.** -/
def gaussianCDFProduct (n : ℕ) (z : Fin n → ℝ) : ContinuousCube n :=
  fun i ↦ standardGaussianCDFUnit (z i)

/-- Establishes measurability of gaussian cdfproduct.

**Lean implementation helper.** -/
lemma measurable_gaussianCDFProduct (n : ℕ) :
    Measurable (gaussianCDFProduct n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_standardGaussianCDFUnit.comp (measurable_pi_apply i)

/-- Coordinatewise Gaussian CDF sends the standard Gaussian product law exactly to product
Lebesgue measure on the continuous cube.

**Book Exercise 5.11.** -/
theorem map_gaussianCDFProduct (n : ℕ) :
    Measure.map (gaussianCDFProduct n) (gaussianPiMeasure n) =
      continuousCubeMeasure n := by
  rw [show gaussianPiMeasure n =
      Measure.pi (fun _ : Fin n ↦ standardGaussianMeasure) from rfl]
  rw [show gaussianCDFProduct n =
      (fun z i ↦ standardGaussianCDFUnit (z i)) from rfl]
  rw [Measure.pi_map_pi]
  · simp only [map_standardGaussianCDFUnit, continuousCubeMeasure]
  · intro i
    exact measurable_standardGaussianCDFUnit.aemeasurable

/-- The canonical Euclidean realization of `[0,1]^n`.

**Lean implementation helper.** -/
def continuousCubeEmbedding (n : ℕ) (u : ContinuousCube n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ (u i : ℝ)

/-- Establishes measurability of continuous cube embedding.

**Lean implementation helper.** -/
lemma measurable_continuousCubeEmbedding (n : ℕ) :
    Measurable (continuousCubeEmbedding n) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

/-- Uniform probability measure on the Euclidean unit cube, constructed from the ordinary
product Lebesgue law.

**Lean implementation helper.** -/
def continuousEuclideanCubeMeasure (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (continuousCubeEmbedding n) (continuousCubeMeasure n)

instance instIsProbabilityMeasureContinuousEuclideanCube (n : ℕ) :
    IsProbabilityMeasure (continuousEuclideanCubeMeasure n) :=
  Measure.isProbabilityMeasure_map (measurable_continuousCubeEmbedding n).aemeasurable

/-- The coordinatewise CDF transport with Euclidean codomain.

**Lean implementation helper.** -/
def gaussianCDFCubeTransport (n : ℕ) (z : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ standardGaussianCDF (z i)

/-- Establishes measurability of gaussian cdfcube transport.

**Lean implementation helper.** -/
lemma measurable_gaussianCDFCubeTransport (n : ℕ) :
    Measurable (gaussianCDFCubeTransport n) := by
  exact (measurable_continuousCubeEmbedding n).comp
    (measurable_gaussianCDFProduct n)

/-- The finite-dimensional transport law in Euclidean coordinates.

**Lean implementation helper.** -/
theorem map_gaussianCDFCubeTransport (n : ℕ) :
    Measure.map (gaussianCDFCubeTransport n) (gaussianPiMeasure n) =
      continuousEuclideanCubeMeasure n := by
  rw [show gaussianCDFCubeTransport n =
      continuousCubeEmbedding n ∘ gaussianCDFProduct n from rfl,
    ← Measure.map_map (measurable_continuousCubeEmbedding n)
      (measurable_gaussianCDFProduct n),
    map_gaussianCDFProduct]
  rfl

/-- The same coordinatewise transport, now viewed as a self-map of Euclidean space.

**Lean implementation helper.** -/
def gaussianCDFEuclideanTransport (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ standardGaussianCDF ((WithLp.ofLp x) i)

/-- The Euclidean Gaussian-CDF transport agrees with the cube-coordinate transport after the `L²` identification.

**Lean implementation helper.** -/
@[simp] lemma gaussianCDFEuclideanTransport_toLp (n : ℕ)
    (z : Fin n → ℝ) :
    gaussianCDFEuclideanTransport n (WithLp.toLp 2 z) =
      gaussianCDFCubeTransport n z := by
  rfl

/-- The coordinatewise Gaussian-to-cube transport is one-Lipschitz for Euclidean distance.

**Book Exercise 5.12.** -/
theorem gaussianCDFEuclideanTransport_lipschitz (n : ℕ) :
    LipschitzWith (1 : ℝ≥0) (gaussianCDFEuclideanTransport n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [PiLp.dist_eq_of_L2, PiLp.dist_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i hi
  have h := standardGaussianCDF_lipschitz.dist_le_mul
    ((WithLp.ofLp x) i) ((WithLp.ofLp y) i)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 h

/-- Center a Euclidean observable under the ordinary continuous-cube law.

**Lean implementation helper.** -/
def continuousCubeCentered {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  F x - ∫ y, F y ∂continuousEuclideanCubeMeasure n

/-- Every `K`-Lipschitz observable on the continuous unit cube satisfies a dimension-free
Gaussian tail bound. The proof uses the genuine product-law identity above and the one-Lipschitz
CDF transport.

**Book Theorem 5.2.10.** -/
theorem continuous_cube_lipschitz_concentration
    (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : ℝ≥0) (hF : LipschitzWith K F) {t : ℝ} (ht : 0 ≤ t) :
    continuousEuclideanCubeMeasure n
        {x | t ≤ |continuousCubeCentered F x|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 / (2 * Real.sqrt 5 * K) ^ 2)) := by
  let T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    gaussianCDFEuclideanTransport n
  let H : EuclideanSpace ℝ (Fin n) → ℝ := F ∘ T
  have hT : LipschitzWith (1 : ℝ≥0) T :=
    gaussianCDFEuclideanTransport_lipschitz n
  have hH : LipschitzWith K H := by
    simpa [H] using hF.comp hT
  have hLaw : HasLaw (gaussianCDFCubeTransport n)
      (continuousEuclideanCubeMeasure n) (gaussianPiMeasure n) :=
    ⟨(measurable_gaussianCDFCubeTransport n).aemeasurable,
      map_gaussianCDFCubeTransport n⟩
  have hmean :
      (∫ z, F (gaussianCDFCubeTransport n z) ∂gaussianPiMeasure n) =
        ∫ x, F x ∂continuousEuclideanCubeMeasure n :=
    hLaw.integral_comp hF.continuous.aestronglyMeasurable
  have hmeanH :
      (∫ z, H (WithLp.toLp 2 z) ∂gaussianPiMeasure n) =
        ∫ x, F x ∂continuousEuclideanCubeMeasure n := by
    calc
      (∫ z, H (WithLp.toLp 2 z) ∂gaussianPiMeasure n) =
          ∫ z, F (gaussianCDFCubeTransport n z) ∂gaussianPiMeasure n := by
            apply integral_congr_ae
            filter_upwards [] with z
            rfl
      _ = _ := hmean
  have hset : MeasurableSet {x | t ≤ |continuousCubeCentered F x|} := by
    exact measurableSet_le measurable_const
      ((hF.continuous.measurable.sub_const _).abs)
  rw [← hLaw.measure_eq hset]
  have hfun :
      (fun z ↦ continuousCubeCentered F (gaussianCDFCubeTransport n z)) =
        gaussianCentered H := by
    funext z
    rw [gaussianCentered, continuousCubeCentered, hmeanH]
    rfl
  change gaussianPiMeasure n
      {z | t ≤ |continuousCubeCentered F (gaussianCDFCubeTransport n z)|} ≤ _
  have hevent :
      {z | t ≤ |continuousCubeCentered F (gaussianCDFCubeTransport n z)|} =
        {z | t ≤ |gaussianCentered H z|} := by
    ext z
    simp only [Set.mem_setOf_eq]
    rw [show continuousCubeCentered F (gaussianCDFCubeTransport n z) =
      gaussianCentered H z from congrFun hfun z]
  rw [hevent]
  exact gaussian_lipschitz_tail_explicit n H K hH ht

/-! ## Polar coordinates in a Euclidean ball -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- The polar-coordinate rectangle corresponding to the punctured open unit ball: an arbitrary
unit direction and a radius in `(0,1)`.

**Lean implementation helper.** -/
def unitBallRadialSet : Set
    (Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
  Set.univ ×ˢ Set.Iio ⟨1, by norm_num⟩

/-- Reassemble a nonzero vector from its unit direction and positive radius.

**Lean implementation helper.** -/
def unitBallPolarMap
    (p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) : E :=
  ((homeomorphUnitSphereProd E).symm p : ({0}ᶜ : Set E))

omit [InnerProductSpace ℝ E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Establishes measurability of the set unit ball radial set.

**Lean implementation helper.** -/
lemma measurableSet_unitBallRadialSet :
    MeasurableSet (unitBallRadialSet (E := E)) := by
  exact MeasurableSet.univ.prod measurableSet_Iio

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E] in
/-- Polar reconstruction maps the unit-ball radial parameter space onto the punctured open unit ball.

**Lean implementation helper.** -/
lemma image_unitBallRadialSet :
    unitBallPolarMap (E := E) '' unitBallRadialSet (E := E) =
      Metric.ball (0 : E) 1 \ {0} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨-, hp⟩
    have hr : ‖unitBallPolarMap (E := E) p‖ = p.2 := by
      rw [unitBallPolarMap, homeomorphUnitSphereProd_symm_apply_coe,
        norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property]
      have hs : ‖(p.1 : E)‖ = 1 := by
        exact mem_sphere_zero_iff_norm.mp p.1.property
      rw [hs, mul_one]
    constructor
    · rw [Metric.mem_ball, dist_zero_right, hr]
      exact hp
    · exact (homeomorphUnitSphereProd E).symm p |>.property
  · rintro ⟨hxball, hx0⟩
    let y : ({0}ᶜ : Set E) := ⟨x, by simpa using hx0⟩
    refine ⟨homeomorphUnitSphereProd E y, ?_, ?_⟩
    · refine ⟨Set.mem_univ _, ?_⟩
      change (((homeomorphUnitSphereProd E) y).2 : ℝ) < 1
      rw [homeomorphUnitSphereProd_apply_snd_coe]
      simpa [Metric.mem_ball, dist_zero_right] using hxball
    · simp [unitBallPolarMap, y]

/-- Polar integration restricted to radii below one. This is the unnormalized geometric identity
from which the probability law below is derived.

**Lean implementation helper.** -/
theorem map_unitBallPolar_restrict :
    Measure.map (unitBallPolarMap (E := E))
        (((volume : Measure E).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))).restrict
            (unitBallRadialSet (E := E))) =
      (volume : Measure E).restrict (Metric.ball 0 1) := by
  let H := homeomorphUnitSphereProd E
  have hp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hps : MeasurePreserving H.symm
      ((volume : Measure E).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)))
      ((volume : Measure E).comap ((↑) : ({0}ᶜ : Set E) → E)) := by
    exact MeasurePreserving.symm H.toMeasurableEquiv hp
  have hpr := hps.restrict_image_emb H.symm.measurableEmbedding
    (unitBallRadialSet (E := E))
  have hcoe : MeasurePreserving ((↑) : ({0}ᶜ : Set E) → E)
      ((volume : Measure E).comap ((↑) : ({0}ᶜ : Set E) → E))
      ((volume : Measure E).restrict ({0}ᶜ : Set E)) :=
    measurePreserving_subtype_coe (measurableSet_singleton (0 : E)).compl
  have hcr := hcoe.restrict_image_emb
    (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl)
    (H.symm '' unitBallRadialSet (E := E))
  have hc := hcr.comp hpr
  have hmap := hc.map_eq
  change Measure.map (unitBallPolarMap (E := E))
      (((volume : Measure E).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))).restrict
          (unitBallRadialSet (E := E))) = _
  rw [show unitBallPolarMap (E := E) =
      ((↑) : ({0}ᶜ : Set E) → E) ∘ H.symm from rfl]
  rw [hmap]
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  have himage :
      (fun x => ((H.symm x : ({0}ᶜ : Set E)) : E)) ''
          unitBallRadialSet (E := E) = Metric.ball (0 : E) 1 \ {0} := by
    simpa [H, unitBallPolarMap] using image_unitBallRadialSet (E := E)
  rw [image_image]
  change (volume.restrict ({0}ᶜ : Set E))
      (A ∩ (fun x => ((H.symm x : ({0}ᶜ : Set E)) : E)) ''
        unitBallRadialSet (E := E)) = _
  rw [himage]
  rw [Measure.restrict_apply
    (hA.inter (measurableSet_ball.diff (measurableSet_singleton 0)))]
  have hseteq :
      A ∩ (Metric.ball (0 : E) 1 \ {0}) ∩ {0}ᶜ =
        (A ∩ Metric.ball (0 : E) 1) \ {0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_compl_iff, Metric.mem_ball, dist_zero_right]
    tauto
  rw [hseteq, measure_sdiff_null]
  simp

/-- The radius law of a uniform point in a positive-dimensional unit ball. Its density is `d
r^(d-1)` on `(0,1)`.

**Lean implementation helper.** -/
def unitBallRadiusMeasure : Measure (Set.Ioi (0 : ℝ)) :=
  (Module.finrank ℝ E : ℝ≥0∞) •
    (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).restrict
      (Set.Iio ⟨1, by norm_num⟩)

instance instIsProbabilityMeasureUnitBallRadius :
    IsProbabilityMeasure (unitBallRadiusMeasure (E := E)) := by
  constructor
  rw [unitBallRadiusMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  rw [Measure.volumeIoiPow_apply_Iio]
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hcast : (((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1) =
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hd
  rw [Nat.sub_add_cancel hd, hcast]
  norm_num
  rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hd),
    ENNReal.ofReal_natCast]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hd.ne')
    (ENNReal.natCast_ne_top _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The radius measure of `[0,a)` in a `d`-dimensional unit ball is `a^d`.

**Lean implementation helper.** -/
lemma unitBallRadiusMeasure_Iio (a : Set.Ioi (0 : ℝ))
    (ha : (a : ℝ) ≤ 1) :
    unitBallRadiusMeasure (E := E) (Set.Iio a) =
      ENNReal.ofReal ((a : ℝ) ^ Module.finrank ℝ E) := by
  rw [unitBallRadiusMeasure, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iio]
  have hset : Set.Iio a ∩
      Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)) = Set.Iio a := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iio]
    constructor
    · exact fun h => h.1
    · intro hr
      exact ⟨hr, lt_of_lt_of_le hr ha⟩
  rw [hset, Measure.volumeIoiPow_apply_Iio]
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  rw [Nat.sub_add_cancel hd]
  have hcast : (((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1) =
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hd
  rw [hcast]
  have hdreal : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast hd
  rw [ENNReal.ofReal_div_of_pos hdreal]
  rw [ENNReal.ofReal_natCast]
  change (Module.finrank ℝ E : ℝ≥0∞) *
      (ENNReal.ofReal ((a : ℝ) ^ Module.finrank ℝ E) /
        (Module.finrank ℝ E : ℝ≥0∞)) = _
  calc
    (Module.finrank ℝ E : ℝ≥0∞) *
        (ENNReal.ofReal ((a : ℝ) ^ Module.finrank ℝ E) /
          (Module.finrank ℝ E : ℝ≥0∞)) =
        ENNReal.ofReal ((a : ℝ) ^ Module.finrank ℝ E) *
          ((Module.finrank ℝ E : ℝ≥0∞) *
            (Module.finrank ℝ E : ℝ≥0∞)⁻¹) := by
      rw [div_eq_mul_inv]
      ac_rfl
    _ = ENNReal.ofReal ((a : ℝ) ^ Module.finrank ℝ E) := by
      rw [ENNReal.mul_inv_cancel (by exact_mod_cast hd.ne')
        (ENNReal.natCast_ne_top _), mul_one]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E] in
/-- The unit-ball radius measure has no atoms.

**Lean implementation helper.** -/
lemma unitBallRadiusMeasure_singleton (a : Set.Ioi (0 : ℝ)) :
    unitBallRadiusMeasure (E := E) {a} = 0 := by
  rw [unitBallRadiusMeasure, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton a)]
  rw [show {a} ∩ Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)) =
      if a < (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)) then {a} else ∅ by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_Iio,
      Set.mem_ite_empty_right, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨rfl, h⟩]
  split_ifs
  · have hbase : (Measure.comap Subtype.val (volume : Measure ℝ)) {a} = 0 := by
      rw [comap_subtype_coe_apply measurableSet_Ioi]
      simp
    have hvolpow :
        Measure.volumeIoiPow (Module.finrank ℝ E - 1) {a} = 0 :=
      withDensity_absolutelyContinuous _ _ hbase
    rw [hvolpow]
    simp
  · simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The radius measure of `[0,a]` in a `d`-dimensional unit ball is `a^d`.

**Lean implementation helper.** -/
lemma unitBallRadiusMeasure_Iic (a : Set.Ioi (0 : ℝ))
    (ha : (a : ℝ) ≤ 1) :
    unitBallRadiusMeasure (E := E) (Set.Iic a) =
      ENNReal.ofReal ((a : ℝ) ^ Module.finrank ℝ E) := by
  rw [← Set.Iio_union_right]
  rw [measure_union]
  · rw [unitBallRadiusMeasure_singleton, add_zero,
      unitBallRadiusMeasure_Iio (E := E) a ha]
  · exact Set.disjoint_singleton_right.mpr (by simp)
  · exact measurableSet_singleton a

/-- Bounds one sub pow by exp.

**Lean implementation helper.** -/
private lemma one_sub_pow_le_exp (d : ℕ) (s : ℝ) (hs1 : s ≤ 1) :
    (1 - s) ^ d ≤ Real.exp (-(d : ℝ) * s) := by
  have hbase0 : 0 ≤ 1 - s := by linarith
  have hbase : 1 - s ≤ Real.exp (-s) := by
    have h := Real.add_one_le_exp (-s)
    linarith
  calc
    (1 - s) ^ d ≤ (Real.exp (-s)) ^ d :=
      pow_le_pow_left₀ hbase0 hbase d
    _ = Real.exp ((d : ℝ) * (-s)) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-(d : ℝ) * s) := by ring_nf

omit [MeasurableSpace E] [BorelSpace E] in
/-- The radius deficit of a uniform unit-ball point has an exponential tail.

**Lean implementation helper.** -/
lemma unitBallRadiusMeasure_lowerTail (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    unitBallRadiusMeasure (E := E) {r | (r : ℝ) ≤ 1 - s} ≤
      ENNReal.ofReal (Real.exp (-(Module.finrank ℝ E : ℝ) * s)) := by
  let a : Set.Ioi (0 : ℝ) := ⟨1 - s, sub_pos.mpr hs1⟩
  have hset : {r : Set.Ioi (0 : ℝ) | (r : ℝ) ≤ 1 - s} =
      Set.Iic a := by
    ext r
    rfl
  rw [hset, unitBallRadiusMeasure_Iic (E := E) a (by dsimp [a]; linarith)]
  apply ENNReal.ofReal_le_ofReal
  exact one_sub_pow_le_exp (Module.finrank ℝ E) s hs1.le

/-- In dimension `n`, scaling the radius deficit by `√n` gives a dimension-free Gaussian upper
bound (a deliberately weaker consequence of the sharper exponential-in-`t√n` estimate).

**Lean implementation helper.** -/
lemma unitBallRadiusDeficit_tail (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    unitBallRadiusMeasure (E := EuclideanSpace ℝ (Fin n))
        {r | t ≤ Real.sqrt n * (1 - (r : ℝ))} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsqrt : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  by_cases hts : t < Real.sqrt n
  · let s : ℝ := t / Real.sqrt n
    have hs0 : 0 ≤ s := div_nonneg ht hsqrt.le
    have hs1 : s < 1 := (div_lt_one hsqrt).2 hts
    let A : Set (Set.Ioi (0 : ℝ)) :=
      fun r : Set.Ioi (0 : ℝ) =>
        t ≤ Real.sqrt n * (1 - (r : ℝ))
    have hset : A =
        (show Set (Set.Ioi (0 : ℝ)) from
          {r | (r : ℝ) ≤ 1 - s}) := by
      apply Set.ext
      intro r
      change (t ≤ Real.sqrt n * (1 - (r : ℝ))) ↔
        ((r : ℝ) ≤ 1 - s)
      constructor
      · intro h
        have hdiv : t / Real.sqrt n ≤ 1 - (r : ℝ) :=
          (div_le_iff₀ hsqrt).2 (by simpa [mul_comm] using h)
        dsimp [s]
        linarith
      · intro h
        have hdiv : t / Real.sqrt n ≤ 1 - (r : ℝ) := by
          dsimp [s] at h
          linarith
        have hmul := (div_le_iff₀ hsqrt).1 hdiv
        simpa [mul_comm] using hmul
    change unitBallRadiusMeasure
        (E := EuclideanSpace ℝ (Fin n)) A ≤ _
    rw [hset]
    refine (unitBallRadiusMeasure_lowerTail
      (E := EuclideanSpace ℝ (Fin n)) s hs0 hs1).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hsq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hratio : (n : ℝ) * (t / Real.sqrt n) =
        Real.sqrt n * t := by
      field_simp
      nlinarith
    simp only [s]
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp]
    calc
      -(n : ℝ) * (t / Real.sqrt n) = -(Real.sqrt n * t) := by
        linarith [hratio]
      _ ≤ -t ^ 2 := by
        nlinarith [mul_nonneg ht (sub_nonneg.mpr (le_of_lt hts))]
  · have hst : Real.sqrt n ≤ t := le_of_not_gt hts
    let A : Set (Set.Ioi (0 : ℝ)) :=
      fun r : Set.Ioi (0 : ℝ) =>
        t ≤ Real.sqrt n * (1 - (r : ℝ))
    have hempty : A = ∅ := by
      ext r
      change (t ≤ Real.sqrt n * (1 - (r : ℝ))) ↔ False
      constructor
      · intro h
        have hr : 0 < (r : ℝ) := r.property
        have hprod : 0 < Real.sqrt n * (r : ℝ) := mul_pos hsqrt hr
        nlinarith
      · exact False.elim
    change unitBallRadiusMeasure
        (E := EuclideanSpace ℝ (Fin n)) A ≤ _
    rw [hempty, measure_empty]
    exact bot_le

/-- Independent unit direction and unit-ball radius.

**Lean implementation helper.** -/
def unitBallPolarMeasure : Measure
    (Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
  (HDP.unitSphereMeasure E).prod (unitBallRadiusMeasure (E := E))

/-- The genuine polar representation of normalized Lebesgue measure on the unit ball. In
particular, the direction and radius used here are independent and the displayed law is proved
rather than imposed by definition.

**Lean implementation helper.** -/
theorem map_unitBallPolarMeasure :
    Measure.map (unitBallPolarMap (E := E))
        (unitBallPolarMeasure (E := E)) = HDP.unitBallMeasure E := by
  let d := Module.finrank ℝ E
  let M := (volume : Measure E).toSphere Set.univ
  let B := (volume : Measure E) (Metric.closedBall (0 : E) 1)
  have hd : 0 < d := Module.finrank_pos
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hdtop : (d : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top d
  have hBopen : (volume : Measure E) (Metric.ball (0 : E) 1) = B := by
    dsimp [B]
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
  have hM : M = (d : ℝ≥0∞) * B := by
    dsimp [M]
    rw [Measure.toSphere_apply_univ, hBopen]
  have hcoeff : M⁻¹ * (d : ℝ≥0∞) = B⁻¹ := by
    rw [hM, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdtop)]
    calc
      (d : ℝ≥0∞)⁻¹ * B⁻¹ * d =
          B⁻¹ * ((d : ℝ≥0∞)⁻¹ * d) := by ac_rfl
      _ = B⁻¹ := by rw [ENNReal.inv_mul_cancel hd0 hdtop, mul_one]
  rw [unitBallPolarMeasure, unitBallRadiusMeasure]
  simp only [HDP.unitSphereMeasure, ProbabilityTheory.cond,
    Measure.restrict_univ]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul]
  rw [← show ((volume : Measure E).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ E - 1))).restrict
        (unitBallRadialSet (E := E)) =
      (volume : Measure E).toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).restrict
          (Set.Iio ⟨1, by norm_num⟩)) by
      simpa [unitBallRadialSet] using
        (Measure.prod_restrict
          (μ := (volume : Measure E).toSphere)
          (ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          (Set.univ : Set (Metric.sphere (0 : E) 1))
          (Set.Iio ⟨1, by norm_num⟩)).symm]
  rw [map_unitBallPolar_restrict (E := E)]
  change (M⁻¹ * (d : ℝ≥0∞)) •
      (volume : Measure E).restrict (Metric.ball 0 1) = _
  rw [hcoeff]
  unfold HDP.unitBallMeasure
  dsimp [B]
  congr 1
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  rw [← Metric.closedBall_sdiff_sphere, ← Set.inter_sdiff_assoc,
    measure_sdiff_null (Measure.addHaar_sphere (volume : Measure E) 0 1)]

instance instIsProbabilityMeasureUnitBall :
    IsProbabilityMeasure (HDP.unitBallMeasure E) := by
  constructor
  unfold HDP.unitBallMeasure
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  exact ENNReal.inv_mul_cancel
    (Metric.measure_closedBall_pos (volume : Measure E) 0 (by norm_num)).ne'
    measure_closedBall_lt_top.ne

instance instIsProbabilityMeasureUnitBallPolar :
    IsProbabilityMeasure (unitBallPolarMeasure (E := E)) := by
  letI : IsProbabilityMeasure
      (Measure.map (unitBallPolarMap (E := E))
        (unitBallPolarMeasure (E := E))) := by
    rw [map_unitBallPolarMeasure (E := E)]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (unitBallPolarMap (E := E))

/-! ## The ball of radius `√n` -/

/-- Uniform probability measure on the Euclidean ball of radius `√n`, obtained by scaling
normalized Lebesgue measure on the unit ball.

**Lean implementation helper.** -/
def scaledUnitBallMeasure (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (fun x : EuclideanSpace ℝ (Fin n) => Real.sqrt n • x)
    (HDP.unitBallMeasure (EuclideanSpace ℝ (Fin n)))

/-- Polar parametrization of the Euclidean ball of radius `√n`.

**Lean implementation helper.** -/
def scaledUnitBallPolarMap (n : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) :
    EuclideanSpace ℝ (Fin n) :=
  Real.sqrt n • unitBallPolarMap p

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Establishes measurability of unit ball polar map.

**Lean implementation helper.** -/
lemma measurable_unitBallPolarMap :
    Measurable (unitBallPolarMap (E := E)) := by
  exact measurable_subtype_coe.comp
    (homeomorphUnitSphereProd E).symm.measurable

/-- Establishes measurability of scaled unit ball polar map.

**Lean implementation helper.** -/
lemma measurable_scaledUnitBallPolarMap (n : ℕ) :
    Measurable (scaledUnitBallPolarMap n) := by
  change Measurable (fun p => (Real.sqrt n : ℝ) •
    unitBallPolarMap (E := EuclideanSpace ℝ (Fin n)) p)
  exact (measurable_unitBallPolarMap
    (E := EuclideanSpace ℝ (Fin n))).const_smul (Real.sqrt n : ℝ)

/-- The polar product law pushes forward exactly to the uniform law on `√n B₂ⁿ`.

**Book Exercise 5.13.** -/
theorem map_scaledUnitBallPolarMap (n : ℕ) (hn : 0 < n) :
    Measure.map (scaledUnitBallPolarMap n)
        (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) =
      scaledUnitBallMeasure n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold scaledUnitBallMeasure scaledUnitBallPolarMap
  change Measure.map
      ((fun x : EuclideanSpace ℝ (Fin n) => (Real.sqrt n : ℝ) • x) ∘
        unitBallPolarMap (E := EuclideanSpace ℝ (Fin n)))
      (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) = _
  rw [← Measure.map_map
      (show Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt n : ℝ) • x) by fun_prop)
      (measurable_unitBallPolarMap
        (E := EuclideanSpace ℝ (Fin n)))]
  rw [map_unitBallPolarMeasure]

instance instIsProbabilityMeasureScaledUnitBall (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (scaledUnitBallMeasure n) := by
  exact Measure.isProbabilityMeasure_map
    (show AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (Real.sqrt n : ℝ) • x) _ by fun_prop)

/-- Proves the strict bound comparing unit ball radius ae with one.

**Lean implementation helper.** -/
lemma unitBallRadius_ae_lt_one (n : ℕ) :
    ∀ᵐ r : Set.Ioi (0 : ℝ) ∂(unitBallRadiusMeasure
        (E := EuclideanSpace ℝ (Fin n))), (r : ℝ) < 1 := by
  change ∀ᵐ r : Set.Ioi (0 : ℝ) ∂
    ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ≥0∞) •
      (Measure.volumeIoiPow
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)).restrict
        (Set.Iio ⟨1, by norm_num⟩)), (r : ℝ) < 1
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem
    (μ := Measure.volumeIoiPow
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))
    (measurableSet_Iio : MeasurableSet
      (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ))))] with r hr
  exact hr

/-- Identifies the probability law described by unit ball polar fst law.

**Lean implementation helper.** -/
lemma unitBallPolar_fst_law (n : ℕ) (hn : 0 < n) :
    HasLaw Prod.fst
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  simp [unitBallPolarMeasure]

/-- Identifies the probability law described by unit ball polar snd law.

**Lean implementation helper.** -/
lemma unitBallPolar_snd_law (n : ℕ) (hn : 0 < n) :
    HasLaw Prod.snd
      (unitBallRadiusMeasure (E := EuclideanSpace ℝ (Fin n)))
      (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨measurable_snd.aemeasurable, ?_⟩
  simp [unitBallPolarMeasure]

/-- Radial displacement created when the unit ball is scaled to radius `√n`.

**Lean implementation helper.** -/
def scaledUnitBallRadiusDeficit (n : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) : ℝ :=
  Real.sqrt n * (1 - (p.2 : ℝ))

/-- Establishes measurability of scaled unit ball radius deficit.

**Lean implementation helper.** -/
lemma measurable_scaledUnitBallRadiusDeficit (n : ℕ) :
    Measurable (scaledUnitBallRadiusDeficit n) := by
  unfold scaledUnitBallRadiusDeficit
  exact measurable_const.mul
    (measurable_const.sub (measurable_subtype_coe.comp measurable_snd))

/-- Shows that scaled unit ball radius deficit ae is nonnegative.

**Lean implementation helper.** -/
lemma scaledUnitBallRadiusDeficit_ae_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ᵐ[unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))]
      scaledUnitBallRadiusDeficit n := by
  have hsnd := unitBallPolar_snd_law n hn
  have hr := unitBallRadius_ae_lt_one n
  have hp : ∀ᵐ p : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)
      ∂(unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))),
      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) < 1 :=
    (hsnd.ae_iff
      (measurable_subtype_coe.lt measurable_const)).2 hr
  filter_upwards [hp] with p hp
  exact mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hp.le)

/-- Gaussian tail for the scaled radius deficit on the full polar probability space.

**Lean implementation helper.** -/
lemma scaledUnitBallRadiusDeficit_tail (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n)))
        {p | t ≤ |scaledUnitBallRadiusDeficit n p|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))
  let ρ := unitBallRadiusMeasure (E := EuclideanSpace ℝ (Fin n))
  have hsnd := unitBallPolar_snd_law n hn
  have hnonneg := scaledUnitBallRadiusDeficit_ae_nonneg n hn
  have heq : μ {p | t ≤ |scaledUnitBallRadiusDeficit n p|} =
      μ {p | t ≤ scaledUnitBallRadiusDeficit n p} := by
    apply measure_congr
    filter_upwards [hnonneg] with p hp
    have hp' : 0 ≤ scaledUnitBallRadiusDeficit n p := by simpa using hp
    apply propext
    change (t ≤ |scaledUnitBallRadiusDeficit n p|) ↔
      (t ≤ scaledUnitBallRadiusDeficit n p)
    rw [abs_of_nonneg hp']
  rw [heq]
  have hraw := unitBallRadiusDeficit_tail n hn t ht
  have hmeasure : μ {p | t ≤ scaledUnitBallRadiusDeficit n p} =
      ρ {r | t ≤ Real.sqrt n * (1 - (r : ℝ))} := by
    have hbase : MeasurableSet
        {r : Set.Ioi (0 : ℝ) |
          t ≤ Real.sqrt n * (1 - (r : ℝ))} := by
      exact measurableSet_le measurable_const
        (measurable_const.mul
          (measurable_const.sub measurable_subtype_coe))
    simpa [μ, ρ, scaledUnitBallRadiusDeficit] using hsnd.measure_eq hbase
  rw [hmeasure]
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have he : 0 < Real.exp (-t ^ 2) := Real.exp_pos _
  nlinarith

/-- The scaled deficit between the unit-ball radius and `√n` is subgaussian with `ψ₂` norm at most `√5`.

**Lean implementation helper.** -/
lemma scaledUnitBallRadiusDeficit_subGaussian (n : ℕ) (hn : 0 < n) :
    HDP.SubGaussian (scaledUnitBallRadiusDeficit n)
        (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) ∧
      HDP.psi2Norm (scaledUnitBallRadiusDeficit n)
        (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) ≤ Real.sqrt 5 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa using HDP.psi2Norm_le_of_tail_bound
    (μ := unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n)))
    (measurable_scaledUnitBallRadiusDeficit n).aemeasurable
    (by norm_num : (0 : ℝ) < 1)
    (fun t ht => by simpa using scaledUnitBallRadiusDeficit_tail n hn t ht)

/-- Pull an ambient observable back to polar coordinates in `√n B₂ⁿ`.

**Lean implementation helper.** -/
def scaledBallPolarObservable (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) : ℝ :=
  F (scaledUnitBallPolarMap n p)

/-- The same observable evaluated at the boundary point in the chosen direction.

**Lean implementation helper.** -/
def scaledSpherePolarObservable (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) : ℝ :=
  scaledSphereObservable n F p.1

/-- Error between a ball point and the boundary point in the same direction.

**Lean implementation helper.** -/
def scaledBallRadialError (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) : ℝ :=
  scaledBallPolarObservable n F p - scaledSpherePolarObservable n F p

/-- Establishes measurability of scaled ball polar observable.

**Lean implementation helper.** -/
lemma measurable_scaledBallPolarObservable (n : ℕ)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Continuous F) :
    Measurable (scaledBallPolarObservable n F) := by
  exact hF.measurable.comp (measurable_scaledUnitBallPolarMap n)

/-- Establishes measurability of scaled sphere polar observable.

**Lean implementation helper.** -/
lemma measurable_scaledSpherePolarObservable (n : ℕ)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Continuous F) :
    Measurable (scaledSpherePolarObservable n F) := by
  exact (measurable_scaledSphereObservable hF).comp measurable_fst

/-- Establishes measurability of scaled ball radial error.

**Lean implementation helper.** -/
lemma measurable_scaledBallRadialError (n : ℕ)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Continuous F) :
    Measurable (scaledBallRadialError n F) := by
  exact (measurable_scaledBallPolarObservable n hF).sub
    (measurable_scaledSpherePolarObservable n hF)

/-- The distance between the scaled polar point and the sphere point of radius `√n` equals the absolute scaled radial deficit.

**Lean implementation helper.** -/
lemma scaledUnitBallPolar_distance (n : ℕ) (_hn : 0 < n)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) :
    dist (scaledUnitBallPolarMap n p)
        (Real.sqrt n • (p.1 : EuclideanSpace ℝ (Fin n))) =
      |scaledUnitBallRadiusDeficit n p| := by
  letI : Nonempty (Fin n) := ⟨⟨0, _hn⟩⟩
  have hu : ‖(p.1 : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp p.1.property
  rw [scaledUnitBallPolarMap, unitBallPolarMap,
    homeomorphUnitSphereProd_symm_apply_coe]
  rw [dist_eq_norm]
  have hvec :
      Real.sqrt n • ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))) -
          Real.sqrt n • (p.1 : EuclideanSpace ℝ (Fin n)) =
        (Real.sqrt n * ((p.2 : ℝ) - 1)) •
          (p.1 : EuclideanSpace ℝ (Fin n)) := by
    module
  rw [hvec, norm_smul, hu, mul_one]
  simp only [scaledUnitBallRadiusDeficit, Real.norm_eq_abs]
  rw [abs_mul, abs_sub_comm]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- For a `K`-Lipschitz function, radial replacement in the scaled ball changes its value by at most `K` times the absolute radial deficit.

**Lean implementation helper.** -/
lemma scaledBallRadialError_abs_le (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) :
    |scaledBallRadialError n F p| ≤
      (K : ℝ) * |scaledUnitBallRadiusDeficit n p| := by
  have h := hF.dist_le_mul
    (scaledUnitBallPolarMap n p)
    (Real.sqrt n • (p.1 : EuclideanSpace ℝ (Fin n)))
  rw [Real.dist_eq] at h
  simpa [scaledBallRadialError, scaledBallPolarObservable,
    scaledSpherePolarObservable, scaledSphereObservable,
    scaledUnitBallPolar_distance n hn p] using h

/-- Derives sub gaussian from same law.

**Lean implementation helper.** -/
private lemma subGaussian_of_sameLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    {ν : Measure ℝ} (hX : HasLaw X ν μ) (hY : HasLaw Y ν μ')
    (hSub : HDP.SubGaussian X μ) : HDP.SubGaussian Y μ' := by
  rcases hSub with ⟨K, hK, hψ⟩
  refine ⟨K, hK, ?_⟩
  rw [HDP.psi2MGF_eq_of_hasLaw hY,
    ← HDP.psi2MGF_eq_of_hasLaw hX]
  exact hψ

/-- Explicit universal constant for concentration on the continuous ball.

**Lean implementation helper.** -/
def continuousBallConcentrationConstant : ℝ :=
  (1 + 1 / Real.sqrt (Real.log 2)) *
    (sphereConcentrationConstant + Real.sqrt 5)

/-- Shows that continuous ball concentration constant is positive.

**Lean implementation helper.** -/
theorem continuousBallConcentrationConstant_pos :
    0 < continuousBallConcentrationConstant := by
  unfold continuousBallConcentrationConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcenter : 0 < 1 + 1 / Real.sqrt (Real.log 2) := by
    positivity
  exact mul_pos hcenter (add_pos sphereConcentrationConstant_pos (by positivity))

/-- Concentration on the polar product probability space. The proof combines the sphere theorem
with the independent radius-deficit bound.

**Book Theorem 5.2.10.** -/
theorem polar_ball_lipschitz_concentration
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) :
    HDP.SubGaussian
        (fun p => scaledBallPolarObservable n F p -
          ∫ q, scaledBallPolarObservable n F q
            ∂unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n)))
        (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) ∧
      HDP.psi2Norm
        (fun p => scaledBallPolarObservable n F p -
          ∫ q, scaledBallPolarObservable n F q
            ∂unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n)))
        (unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n))) ≤
      continuousBallConcentrationConstant * (K : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let μ := unitBallPolarMeasure (E := E)
  let σ := HDP.unitSphereMeasure E
  let X : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    scaledBallPolarObservable n F
  let Y : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    scaledSpherePolarObservable n F
  let D : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    scaledBallRadialError n F
  let S : Metric.sphere (0 : E) 1 → ℝ := scaledSphereObservable n F
  let m : ℝ := ∫ u, S u ∂σ
  let YC : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p => Y p - m
  let W : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p => X p - m
  have hXm : Measurable X :=
    measurable_scaledBallPolarObservable n hF.continuous
  have hYm : Measurable Y :=
    measurable_scaledSpherePolarObservable n hF.continuous
  have hDm : Measurable D :=
    measurable_scaledBallRadialError n hF.continuous
  have hSm : Measurable S :=
    measurable_scaledSphereObservable hF.continuous
  have hYCm : Measurable YC := hYm.sub_const m
  have hWm : Measurable W := hXm.sub_const m
  have hfst := unitBallPolar_fst_law n hn
  let SC : Metric.sphere (0 : E) 1 → ℝ := fun u => S u - m
  let νS : Measure ℝ := Measure.map SC σ
  have hSlaw : HasLaw SC νS σ :=
    ⟨(hSm.sub_const m).aemeasurable, rfl⟩
  have hYlaw : HasLaw YC νS μ := by
    have hc := hSlaw.comp hfst
    simpa [YC, Y, SC, S, scaledSpherePolarObservable,
      Function.comp_def, μ, σ] using hc
  have hSsub : HDP.SubGaussian SC σ := by
    simpa [SC, S, m, σ] using
      sphere_lipschitz_subGaussian_ambient n hn F K hF
  have hYsub : HDP.SubGaussian YC μ :=
    subGaussian_of_sameLaw hSlaw hYlaw hSsub
  have hYnorm : HDP.psi2Norm YC μ ≤
      sphereConcentrationConstant * (K : ℝ) := by
    calc
      HDP.psi2Norm YC μ = HDP.psi2Norm SC σ := by
        rw [HDP.psi2Norm_eq_of_hasLaw hYlaw,
          HDP.psi2Norm_eq_of_hasLaw hSlaw]
      _ ≤ sphereConcentrationConstant * (K : ℝ) := by
        simpa [SC, S, m, σ] using
          sphere_lipschitz_concentration_ambient n hn F K hF
  let R : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    scaledUnitBallRadiusDeficit n
  let Z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p => (K : ℝ) * R p
  have hR := scaledUnitBallRadiusDeficit_subGaussian n hn
  have hZsub : HDP.SubGaussian Z μ := by
    simpa [Z, R, μ] using hR.1.const_mul (K : ℝ)
  have hZnorm : HDP.psi2Norm Z μ ≤ (K : ℝ) * Real.sqrt 5 := by
    rw [show Z = fun p => (K : ℝ) * R p from rfl,
      HDP.psi2Norm_const_mul, abs_of_nonneg K.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (by simpa [R, μ] using hR.2) K.coe_nonneg
  have hDdom : ∀ p, |D p| ≤ |Z p| := by
    intro p
    have h := scaledBallRadialError_abs_le n hn F K hF p
    simpa [D, Z, R, abs_mul, abs_of_nonneg K.coe_nonneg] using h
  have hDsub := HDP.psi2Norm_mono_abs
    (μ := μ) (Filter.Eventually.of_forall hDdom) hZsub
  have hWdecomp : W = fun p => YC p + D p := by
    funext p
    simp only [W, YC, D, X, Y, scaledBallRadialError]
    ring
  have hWsub : HDP.SubGaussian W μ := by
    rw [hWdecomp]
    exact HDP.SubGaussian.add hYCm.aemeasurable hDm.aemeasurable
      hYsub hDsub.1
  have hWnorm : HDP.psi2Norm W μ ≤
      (sphereConcentrationConstant + Real.sqrt 5) * (K : ℝ) := by
    rw [hWdecomp]
    calc
      HDP.psi2Norm (fun p => YC p + D p) μ ≤
          HDP.psi2Norm YC μ + HDP.psi2Norm D μ :=
        HDP.psi2Norm_add_le hYCm.aemeasurable hDm.aemeasurable
          hYsub hDsub.1
      _ ≤ sphereConcentrationConstant * (K : ℝ) +
          (K : ℝ) * Real.sqrt 5 :=
        add_le_add hYnorm (hDsub.2.trans hZnorm)
      _ = (sphereConcentrationConstant + Real.sqrt 5) * (K : ℝ) := by
        ring
  have hWcenter := HDP.psi2Norm_centering hWm.aemeasurable hWsub
  have hWmem : MemLp W 1 μ := by
    simpa using hWsub.memLp hWm.aemeasurable
      (p := (1 : ℝ)) (le_refl 1)
  have hWint : Integrable W μ := hWmem.integrable (le_refl 1)
  have hXeq : X = fun p => W p + m := by
    funext p
    simp [W]
  have hXint : Integrable X μ := by
    rw [hXeq]
    exact hWint.add (integrable_const m)
  have hmeanW : (∫ p, W p ∂μ) = (∫ p, X p ∂μ) - m := by
    rw [show W = fun p => X p - m by funext p; simp [W]]
    rw [integral_sub hXint (integrable_const m)]
    simp
  have hcenterEq :
      (fun p => W p - ∫ q, W q ∂μ) =
        fun p => X p - ∫ q, X q ∂μ := by
    funext p
    rw [hmeanW]
    simp [W]
  rw [show unitBallPolarMeasure (E := EuclideanSpace ℝ (Fin n)) = μ from rfl]
  change HDP.SubGaussian (fun p => X p - ∫ q, X q ∂μ) μ ∧
    HDP.psi2Norm (fun p => X p - ∫ q, X q ∂μ) μ ≤ _
  rw [← hcenterEq]
  constructor
  · exact hWcenter.1
  · calc
      HDP.psi2Norm (fun p => W p - ∫ q, W q ∂μ) μ ≤
          (1 + 1 / Real.sqrt (Real.log 2)) * HDP.psi2Norm W μ :=
        hWcenter.2
      _ ≤ (1 + 1 / Real.sqrt (Real.log 2)) *
          ((sphereConcentrationConstant + Real.sqrt 5) * (K : ℝ)) := by
        gcongr
      _ = continuousBallConcentrationConstant * (K : ℝ) := by
        unfold continuousBallConcentrationConstant
        ring

/-- Center an observable under the uniform law on `√n B₂ⁿ`.

**Lean implementation helper.** -/
def scaledBallCentered {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  F x - ∫ y, F y ∂scaledUnitBallMeasure n

/-- Every `K`-Lipschitz observable on the uniform ball `√n B₂ⁿ` is sub-Gaussian around its mean,
with a dimension-free explicit constant.

**Book Theorem 5.2.10.** -/
theorem continuous_ball_lipschitz_concentration
    (n : ℕ) (hn : 0 < n)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0)
    (hF : LipschitzWith K F) :
    HDP.SubGaussian (scaledBallCentered F) (scaledUnitBallMeasure n) ∧
      HDP.psi2Norm (scaledBallCentered F) (scaledUnitBallMeasure n) ≤
        continuousBallConcentrationConstant * (K : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let μ := unitBallPolarMeasure (E := E)
  let β := scaledUnitBallMeasure n
  let T := scaledUnitBallPolarMap n
  let X : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    scaledBallPolarObservable n F
  let B : E → ℝ := scaledBallCentered F
  let P : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p => X p - ∫ q, X q ∂μ
  have hLaw : HasLaw T β μ :=
    ⟨(measurable_scaledUnitBallPolarMap n).aemeasurable,
      map_scaledUnitBallPolarMap n hn⟩
  have hmean : (∫ p, X p ∂μ) = ∫ x, F x ∂β := by
    simpa [X, scaledBallPolarObservable, T, μ, β] using
      hLaw.integral_comp hF.continuous.aestronglyMeasurable
  let ν : Measure ℝ := Measure.map B β
  have hBlaw : HasLaw B ν β :=
    ⟨(hF.continuous.measurable.sub_const _).aemeasurable, rfl⟩
  have hPlaw : HasLaw P ν μ := by
    have hc := hBlaw.comp hLaw
    apply hc.congr
    filter_upwards [] with p
    simp only [Function.comp_apply, P, B, scaledBallCentered]
    rw [hmean]
    rfl
  have hPolar := polar_ball_lipschitz_concentration n hn F K hF
  have hPsub : HDP.SubGaussian P μ := by
    simpa [P, X, μ] using hPolar.1
  have hPnorm : HDP.psi2Norm P μ ≤
      continuousBallConcentrationConstant * (K : ℝ) := by
    simpa [P, X, μ] using hPolar.2
  change HDP.SubGaussian B β ∧
    HDP.psi2Norm B β ≤ continuousBallConcentrationConstant * (K : ℝ)
  constructor
  · exact subGaussian_of_sameLaw hPlaw hBlaw hPsub
  · calc
      HDP.psi2Norm B β = HDP.psi2Norm P μ := by
        rw [HDP.psi2Norm_eq_of_hasLaw hBlaw,
          HDP.psi2Norm_eq_of_hasLaw hPlaw]
      _ ≤ continuousBallConcentrationConstant * (K : ℝ) := hPnorm

end

end HDP.Chapter5

end Source_08_ContinuousMeasures

/-! ## Material formerly in `09_JohnsonLindenstrauss.lean` -/

section Source_09_JohnsonLindenstrauss

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
  Matrix.Norms.Elementwise Matrix.Norms.L2Operator

namespace HDP.Chapter5

noncomputable section

/-!
# Random projections and the Johnson–Lindenstrauss lemma

This file formalizes §5.3 and the load-bearing Exercises 5.14–5.15.  It
constructs the Haar-to-sphere law explicitly, proves the exact second moment
and fixed-vector tail for the genuine Grassmannian projection, derives the
finite-set Johnson–Lindenstrauss theorem by a union bound, proves its
subgaussian/Rademacher version, and proves the nonlinear logarithmic lower
bound.  No statement here imports an exercise leaf or the source appendix.
-/

instance instContinuousInvOrthogonalGroup (n : ℕ) :
    ContinuousInv (Matrix.orthogonalGroup (Fin n) ℝ) where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      star (U.1 : Matrix (Fin n) (Fin n) ℝ))
    fun_prop

/-- The action of an orthogonal matrix on a Euclidean vector.

**Lean implementation helper.** -/
def orthogonalAction {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  U.1.toEuclideanLin x

/-- Orthogonal matrices preserve the Euclidean norm.

**Lean implementation helper.** -/
lemma norm_orthogonalAction {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖orthogonalAction U x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  change inner ℝ (U.1.toEuclideanLin x) (U.1.toEuclideanLin x) = inner ℝ x x
  rw [← LinearMap.adjoint_inner_right]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  have hU : U.1ᴴ * U.1 = 1 := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2
  rw [hU]
  simp

/-- An orthogonal matrix regarded as a linear isometric equivalence of Euclidean space.

**Lean implementation helper.** -/
def orthogonalLinearIsometryEquiv {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  let f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    U.1.toEuclideanLin
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := {
    toFun := f
    invFun := U.1ᵀ.toEuclideanLin
    map_add' := f.map_add
    map_smul' := f.map_smul
    left_inv := by
      intro x
      change U.1ᵀ.toEuclideanLin (U.1.toEuclideanLin x) = x
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      rw [(Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2]
      simp
    right_inv := by
      intro x
      change U.1.toEuclideanLin (U.1ᵀ.toEuclideanLin x) = x
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      rw [(Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp U.2]
      simp }
  e.isometryOfInner fun x y => by
    change inner ℝ (U.1.toEuclideanLin x) (U.1.toEuclideanLin y) = inner ℝ x y
    rw [← LinearMap.adjoint_inner_right]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
    have hU : U.1ᴴ * U.1 = 1 := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2
    rw [hU]
    simp

/-- The linear isometry induced by an orthogonal matrix acts by ordinary matrix multiplication.

**Lean implementation helper.** -/
@[simp] lemma orthogonalLinearIsometryEquiv_apply {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalLinearIsometryEquiv U x = orthogonalAction U x := rfl

/-- The orthogonal matrix of reflection across the orthogonal complement of the line spanned by
`v - w`.

**Lean implementation helper.** -/
def reflectionOrthogonalMatrix {n : ℕ}
    (v w : EuclideanSpace ℝ (Fin n)) : Matrix.orthogonalGroup (Fin n) ℝ := by
  let L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ℝ ∙ (v - w))ᗮ.reflection
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  exact ⟨L.toMatrix b.toBasis b.toBasis, L.toMatrix_mem_unitaryGroup b b⟩

/-- The orthogonal matrix sending `v` toward `w` acts as reflection across the orthogonal complement of `v-w`.

**Lean implementation helper.** -/
lemma reflectionOrthogonalMatrix_action {n : ℕ}
    (v w x : EuclideanSpace ℝ (Fin n)) :
    orthogonalAction (reflectionOrthogonalMatrix v w) x =
      (ℝ ∙ (v - w))ᗮ.reflection x := by
  unfold orthogonalAction reflectionOrthogonalMatrix
  dsimp only
  change (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      ((ℝ ∙ (v - w))ᗮ.reflection :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))).toEuclideanLin x = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [Matrix.toLin_toMatrix]
  rfl

/-- Any two points on the Euclidean unit sphere are related by an orthogonal transformation.

**Lean implementation helper.** -/
theorem exists_orthogonalAction_eq {n : ℕ}
    (v w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      orthogonalAction U v = w := by
  refine ⟨reflectionOrthogonalMatrix v w, ?_⟩
  rw [reflectionOrthogonalMatrix_action]
  exact Submodule.reflection_sub (by simp)

/-- Orthogonal matrix multiplication corresponds to composition of the induced actions.

**Lean implementation helper.** -/
lemma orthogonalAction_mul {n : ℕ}
    (U V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalAction (U * V) x = orthogonalAction U (orthogonalAction V x) := by
  unfold orthogonalAction
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  rfl

/-- The unit-sphere point obtained by applying the inverse of an orthogonal matrix to `v`.

**Lean implementation helper.** -/
def inverseOrthogonalSphereOrbit {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨orthogonalAction U⁻¹ v, by
    simpa [Metric.mem_sphere, dist_zero_right] using
      congrArg (fun r : ℝ => r) (norm_orthogonalAction U⁻¹ v)⟩

/-- Establishes continuity of inverse orthogonal sphere orbit.

**Lean implementation helper.** -/
lemma continuous_inverseOrthogonalSphereOrbit {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Continuous (inverseOrthogonalSphereOrbit v) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
    (U⁻¹.1.toEuclideanLin) (v : EuclideanSpace ℝ (Fin n)))
  change Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
    WithLp.toLp 2 (fun i : Fin n =>
      ∑ j : Fin n, U⁻¹.1 i j * (v : EuclideanSpace ℝ (Fin n)) j))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hval : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U⁻¹.1 : Matrix (Fin n) (Fin n) ℝ)) :=
    continuous_subtype_val.comp continuous_inv
  have hij : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => U⁻¹.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hval)
  exact hij.mul continuous_const

/-- Establishes continuity of inverse orthogonal sphere orbit prod.

**Lean implementation helper.** -/
lemma continuous_inverseOrthogonalSphereOrbit_prod {n : ℕ} :
    Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      inverseOrthogonalSphereOrbit p.2 p.1) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
    (p.1⁻¹.1.toEuclideanLin)
      (p.2 : EuclideanSpace ℝ (Fin n)))
  change Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
    WithLp.toLp 2 (fun i : Fin n =>
      ∑ j : Fin n, p.1⁻¹.1 i j *
        (p.2 : EuclideanSpace ℝ (Fin n)) j))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hval : Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (p.1⁻¹.1 : Matrix (Fin n) (Fin n) ℝ)) :=
    continuous_subtype_val.comp (continuous_inv.comp continuous_fst)
  have hij : Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => p.1⁻¹.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hval)
  have hxj : Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (p.2 : EuclideanSpace ℝ (Fin n)) j) :=
    (continuous_apply j).comp
      ((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp
        (continuous_subtype_val.comp continuous_snd))
  exact hij.mul hxj

/-- The Haar pushforward along the inverse orbit map is independent of the chosen unit vector.

**Lean implementation helper.** -/
theorem map_inverseOrthogonalSphereOrbit_eq {n : ℕ}
    (v w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.map (inverseOrthogonalSphereOrbit v) (orthogonalHaarMeasure n) =
      Measure.map (inverseOrthogonalSphereOrbit w) (orthogonalHaarMeasure n) := by
  obtain ⟨V, hV⟩ := exists_orthogonalAction_eq v w
  have hfun : inverseOrthogonalSphereOrbit w =
      inverseOrthogonalSphereOrbit v ∘ (fun U => V⁻¹ * U) := by
    funext U
    apply Subtype.ext
    change orthogonalAction U⁻¹ w = orthogonalAction (V⁻¹ * U)⁻¹ v
    calc
      orthogonalAction U⁻¹ w =
          orthogonalAction U⁻¹ (orthogonalAction V v) := by rw [hV]
      _ = orthogonalAction (U⁻¹ * V) v :=
        (orthogonalAction_mul U⁻¹ V v).symm
      _ = orthogonalAction (V⁻¹ * U)⁻¹ v := by simp
  rw [hfun]
  calc
    Measure.map (inverseOrthogonalSphereOrbit v) (orthogonalHaarMeasure n) =
        Measure.map (inverseOrthogonalSphereOrbit v)
          (Measure.map (fun U => V⁻¹ * U) (orthogonalHaarMeasure n)) := by
      rw [map_mul_left_eq_self]
    _ = Measure.map (inverseOrthogonalSphereOrbit v ∘ fun U => V⁻¹ * U)
          (orthogonalHaarMeasure n) := by
      rw [Measure.map_map]
      · exact (continuous_inverseOrthogonalSphereOrbit v).measurable
      · fun_prop

/-- The inverse orthogonal orbit of a fixed unit vector pushes Haar measure forward to uniform measure on the sphere.

**Lean implementation helper.** -/
theorem map_inverseOrthogonalSphereOrbit {n : ℕ} (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.map (inverseOrthogonalSphereOrbit v) (orthogonalHaarMeasure n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  let μ := orthogonalHaarMeasure n
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply Measure.ext
  intro A hA
  have hF : MeasurableSet
      ((fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        inverseOrthogonalSphereOrbit p.2 p.1) ⁻¹' A) :=
    hA.preimage continuous_inverseOrthogonalSphereOrbit_prod.measurable
  rw [Measure.map_apply (continuous_inverseOrthogonalSphereOrbit v).measurable hA]
  calc
    μ {U | inverseOrthogonalSphereOrbit v U ∈ A} =
        ∫⁻ _x, μ {U | inverseOrthogonalSphereOrbit v U ∈ A} ∂σ := by simp [σ]
    _ = ∫⁻ x, μ {U | inverseOrthogonalSphereOrbit x U ∈ A} ∂σ := by
      apply lintegral_congr
      intro x
      change μ (inverseOrthogonalSphereOrbit v ⁻¹' A) =
        μ (inverseOrthogonalSphereOrbit x ⁻¹' A)
      rw [← Measure.map_apply (continuous_inverseOrthogonalSphereOrbit v).measurable hA,
        ← Measure.map_apply (continuous_inverseOrthogonalSphereOrbit x).measurable hA,
        map_inverseOrthogonalSphereOrbit_eq v x]
    _ = (μ.prod σ)
        ((fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          inverseOrthogonalSphereOrbit p.2 p.1) ⁻¹' A) := by
      rw [Measure.prod_apply_symm hF]
      rfl
    _ = ∫⁻ U, σ {x | inverseOrthogonalSphereOrbit x U ∈ A} ∂μ := by
      rw [Measure.prod_apply hF]
      rfl
    _ = ∫⁻ _U, σ A ∂μ := by
      apply lintegral_congr
      intro U
      let L := orthogonalLinearIsometryEquiv U⁻¹
      have hmap := HDP.map_unitSphereMeasure L
      have hfunU : (fun x => inverseOrthogonalSphereOrbit x U) =
          HDP.unitSphereHomeomorph L := by
        funext x
        apply Subtype.ext
        rfl
      change σ ((fun x => inverseOrthogonalSphereOrbit x U) ⁻¹' A) = σ A
      rw [hfunU]
      rw [← Measure.map_apply]
      · simpa [σ] using congrArg (fun ν : Measure _ => ν A) hmap
      · exact (HDP.unitSphereHomeomorph L).measurable
      · exact hA
    _ = σ A := by simp [μ]

/-! Coordinate projections of a uniform sphere point. -/

/-- The linear map that retains the first `m` coordinates of a vector in `R^n`.

**Lean implementation helper.** -/
def firstCoordinateRestriction {m n : ℕ} (hmn : m ≤ n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun x := WithLp.toLp 2 fun i => x (Fin.castLE hmn i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Restricting to the first `m` coordinates sends coordinate `i` to the corresponding coordinate
of the original vector.

**Lean implementation helper.** -/
@[simp] lemma firstCoordinateRestriction_apply {m n : ℕ} (hmn : m ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    firstCoordinateRestriction hmn x i = x (Fin.castLE hmn i) := rfl

/-- Discarding all but the first `m` coordinates cannot increase Euclidean norm.

**Lean implementation helper.** -/
lemma norm_firstCoordinateRestriction_le {m n : ℕ} (hmn : m ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖firstCoordinateRestriction hmn x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  gcongr 1
  change (∑ i : Fin m, ‖x (Fin.castLE hmn i)‖ ^ 2) ≤
    ∑ j : Fin n, ‖x j‖ ^ 2
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < m
  calc
    (∑ i : Fin m, ‖x (Fin.castLE hmn i)‖ ^ 2) =
      ∑ j ∈ S, ‖x j‖ ^ 2 := by
      apply Finset.sum_bij (fun i _ => Fin.castLE hmn i)
      · intro i hi; simp [S]
      · intro i₁ hi₁ i₂ hi₂ heq; exact Fin.castLE_injective hmn heq
      · intro j hj
        have hjlt : j.val < m := (Finset.mem_filter.mp hj).2
        exact ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro i hi; rfl
    _ ≤ ∑ j : Fin n, ‖x j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)

/-- The Euclidean norm of the first `m` coordinates of a vector in `R^n`.

**Lean implementation helper.** -/
def coordinateProjectionNorm {m n : ℕ} (hmn : m ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖firstCoordinateRestriction hmn x‖

/-- The norm of the first `m` coordinates is a `1`-Lipschitz function on the sphere.

**Lean implementation helper.** -/
lemma coordinateProjectionNorm_lipschitz {m n : ℕ} (hmn : m ≤ n) :
    LipschitzWith 1 (coordinateProjectionNorm hmn) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, coordinateProjectionNorm]
  calc
    |‖firstCoordinateRestriction hmn x‖ -
        ‖firstCoordinateRestriction hmn y‖| ≤
        ‖firstCoordinateRestriction hmn x -
          firstCoordinateRestriction hmn y‖ := abs_norm_sub_norm_le _ _
    _ = ‖firstCoordinateRestriction hmn (x - y)‖ := by rw [map_sub]
    _ ≤ ‖x - y‖ := norm_firstCoordinateRestriction_le hmn _

/-- The square of the coordinate-projection norm is the sum of squares of the first `m` coordinates.

**Lean implementation helper.** -/
lemma coordinateProjectionNorm_sq {m n : ℕ} (hmn : m ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateProjectionNorm hmn x ^ 2 =
      ∑ i : Fin m, x (Fin.castLE hmn i) ^ 2 := by
  rw [coordinateProjectionNorm, EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Each coordinate of a uniform point on the unit sphere has second moment `1/n`.

**Lean implementation helper.** -/
private lemma sphere_coordinate_sq_integral {n : ℕ} (hn : 0 < n)
    (i : Fin n) :
    (∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ((x : EuclideanSpace ℝ (Fin n)) i) ^ 2
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) = 1 / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := HDP.Chapter3.sphericalProjection_coordinate_secondMoment hn i
  simp only [HDP.Chapter3.sphericalProjection_coordinate, mul_pow] at h
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have h' : (n : ℝ) *
      (∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ((x : EuclideanSpace ℝ (Fin n)) i) ^ 2
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) = 1 := by
    rw [← integral_const_mul]
    simpa [hs] using h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hn0).2
  simpa [mul_comm] using h'

/-- Computes the second moment of coordinate projection norm.

**Lean implementation helper.** -/
theorem coordinateProjectionNorm_secondMoment {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) :
    (∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        coordinateProjectionNorm hmn x ^ 2
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) = (m : ℝ) / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hint (i : Fin m) : Integrable
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        ((x : EuclideanSpace ℝ (Fin n)) (Fin.castLE hmn i)) ^ 2)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hcoord := PiLp.norm_apply_le (x : EuclideanSpace ℝ (Fin n))
      (Fin.castLE hmn i)
    have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      have hx' := x.2
      change dist (x : EuclideanSpace ℝ (Fin n)) 0 = 1 at hx'
      rw [dist_zero_right] at hx'
      exact hx'
    have habs : |(x : EuclideanSpace ℝ (Fin n)) (Fin.castLE hmn i)| ≤ 1 := by
      simpa [Real.norm_eq_abs, hx] using hcoord
    nlinarith [sq_abs ((x : EuclideanSpace ℝ (Fin n)) (Fin.castLE hmn i)),
      abs_nonneg ((x : EuclideanSpace ℝ (Fin n)) (Fin.castLE hmn i))]
  rw [show (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      coordinateProjectionNorm hmn x ^ 2) =
      fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => ∑ i : Fin m,
        ((x : EuclideanSpace ℝ (Fin n)) (Fin.castLE hmn i)) ^ 2 by
    funext x; exact coordinateProjectionNorm_sq hmn x]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [sphere_coordinate_sq_integral hn]
  simp [div_eq_mul_inv]

/-- The coordinate-projection norm on the unit sphere belongs to `L²`.

**Lean implementation helper.** -/
private lemma coordinateProjectionNorm_memLp_two {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) :
    MemLp
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        coordinateProjectionNorm hmn x) 2
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply MemLp.of_bound
    ((coordinateProjectionNorm_lipschitz hmn).continuous.measurable.comp
      measurable_subtype_coe).aestronglyMeasurable 1
  filter_upwards [] with x
  change |coordinateProjectionNorm hmn x| ≤ 1
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hx' := x.2
    change dist (x : EuclideanSpace ℝ (Fin n)) 0 = 1 at hx'
    rw [dist_zero_right] at hx'
    exact hx'
  have hle : coordinateProjectionNorm hmn x ≤ 1 :=
    (norm_firstCoordinateRestriction_le hmn x).trans_eq hx
  exact abs_le.2 ⟨by
    have := norm_nonneg (firstCoordinateRestriction hmn x)
    simp only [coordinateProjectionNorm] at *
    linarith, hle⟩

/-- The `L²` norm of the first-`m` coordinate projection on the unit sphere is `√(m/n)`.

**Lean implementation helper.** -/
theorem lpNormRV_coordinateProjectionNorm {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) :
    HDP.Chapter1.lpNormRV
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        coordinateProjectionNorm hmn x) 2
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      Real.sqrt ((m : ℝ) / n) := by
  let Z := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
    coordinateProjectionNorm hmn x
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hmem : MemLp Z 2 σ := coordinateProjectionNorm_memLp_two hn hmn
  have hsquare := HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV hmem
  have hsquare' : (HDP.Chapter1.lpNormRV Z 2 σ) ^ 2 = (m : ℝ) / n := by
    rw [hsquare]
    change (∫ x, Z x * Z x ∂σ) = _
    rw [show (fun x => Z x * Z x) = fun x => Z x ^ 2 by funext x; ring]
    exact coordinateProjectionNorm_secondMoment hn hmn
  have hleft : 0 ≤ HDP.Chapter1.lpNormRV Z 2 σ := by
    rw [HDP.Chapter1.lpNormRV]
    exact Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have hmnR : 0 ≤ (m : ℝ) / n := by positivity
  apply (sq_eq_sq₀ hleft (Real.sqrt_nonneg _)).mp
  rw [hsquare', Real.sq_sqrt hmnR]

/-- Absolute constant in the fixed-vector random-projection inequality.

**Lean implementation helper.** -/
def randomProjectionTailConstant : ℝ :=
  (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt 2 *
    sphereConcentrationConstant

/-- Shows that random projection tail constant is positive.

**Lean implementation helper.** -/
lemma randomProjectionTailConstant_pos : 0 < randomProjectionTailConstant := by
  unfold randomProjectionTailConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrtlog : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog
  have hfac : 0 < 1 + 1 / Real.sqrt (Real.log 2) := by positivity
  exact mul_pos (mul_pos hfac (Real.sqrt_pos.2 (by norm_num)))
    sphereConcentrationConstant_pos

/-- For a uniform point on the unit sphere, the first-`m` coordinate norm differs from `√(m/n)` by at least the relative amount `ε` with probability at most `2 exp(-ε²m/C²)`.

**Lean implementation helper.** -/
theorem coordinateProjectionNorm_tail {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | ε * Real.sqrt ((m : ℝ) / n) ≤
          |coordinateProjectionNorm hmn x - Real.sqrt ((m : ℝ) / n)|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-(ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let Z := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
    coordinateProjectionNorm hmn x
  have hZm : Measurable Z :=
    (coordinateProjectionNorm_lipschitz hmn).continuous.measurable.comp measurable_subtype_coe
  have hZp : MemLp Z (ENNReal.ofReal 2) σ := by
    simpa using coordinateProjectionNorm_memLp_two hn hmn
  have hmean : 0 ≤ ∫ x, Z x ∂σ := integral_nonneg fun _ => norm_nonneg _
  have hCsub := unitSphere_lipschitz_subGaussian_ambient n hn
    (coordinateProjectionNorm hmn) 1 (coordinateProjectionNorm_lipschitz hmn)
  have hCnorm := unitSphere_lipschitz_concentration_ambient n hn
    (coordinateProjectionNorm hmn) 1 (coordinateProjectionNorm_lipschitz hmn)
  have hCnorm' : HDP.psi2Norm (fun x => Z x - ∫ y, Z y ∂σ) σ ≤
      sphereConcentrationConstant / Real.sqrt n := by
    simpa [Z, σ] using hCnorm
  have hshift := exercise_5_10_lp_center (p := (2 : ℝ)) (by norm_num)
    hZm.aemeasurable hZp hmean hCsub
  have hLp := lpNormRV_coordinateProjectionNorm hn hmn
  have hbound : HDP.psi2Norm
      (fun x => Z x - Real.sqrt ((m : ℝ) / n)) σ ≤
      randomProjectionTailConstant / Real.sqrt n := by
    rw [← hLp]
    calc
      HDP.psi2Norm
          (fun x => Z x - HDP.Chapter1.lpNormRV Z 2 σ) σ ≤
          (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt 2 *
            HDP.psi2Norm (fun x => Z x - ∫ y, Z y ∂σ) σ := hshift.2
      _ ≤ (1 + 1 / Real.sqrt (Real.log 2)) * Real.sqrt 2 *
          (sphereConcentrationConstant / Real.sqrt n) := by
        exact mul_le_mul_of_nonneg_left hCnorm' (by positivity)
      _ = randomProjectionTailConstant / Real.sqrt n := by
        simp [randomProjectionTailConstant]
        ring
  have hsub : HDP.SubGaussian
      (fun x => Z x - Real.sqrt ((m : ℝ) / n)) σ := by
    rw [← hLp]
    exact hshift.1
  have htail := tail_le_of_subGaussian_psi2Norm_le
    (B := randomProjectionTailConstant / Real.sqrt n)
    (t := ε * Real.sqrt ((m : ℝ) / n))
    (hZm.sub_const _).aemeasurable hsub
    (div_nonneg randomProjectionTailConstant_pos.le (Real.sqrt_nonneg _)) hbound
    (mul_nonneg hε (Real.sqrt_nonneg _))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hmnR : 0 ≤ (m : ℝ) / n := by positivity
  have hcalc :
      -(ε * Real.sqrt ((m : ℝ) / n)) ^ 2 /
          (randomProjectionTailConstant / Real.sqrt n) ^ 2 =
        -(ε ^ 2 * m / randomProjectionTailConstant ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hmnR, div_pow, Real.sq_sqrt hnR.le]
    field_simp [hnR.ne', randomProjectionTailConstant_pos.ne']
  rw [hcalc] at htail
  simpa [Z, σ] using htail

/-- The coordinate-projection matrix keeps coordinate `i` when `i < m` and sends it to zero
otherwise.

**Lean implementation helper.** -/
lemma coordinateProjectionMatrix_action_apply {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (coordinateProjectionMatrix n m).toEuclideanLin x i =
      if (i : ℕ) < m then x i else 0 := by
  change ((coordinateProjectionMatrix n m) *ᵥ x.ofLp) i = _
  rw [coordinateProjectionMatrix, Matrix.mulVec_diagonal]
  split <;> simp_all

/-- Matrix projection onto the first `m` coordinates has norm equal to
`coordinateProjectionNorm`.

**Lean implementation helper.** -/
lemma norm_coordinateProjectionMatrix_action {m n : ℕ}
    (hmn : m ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(coordinateProjectionMatrix n m).toEuclideanLin x‖ =
      coordinateProjectionNorm hmn x := by
  unfold coordinateProjectionNorm
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [coordinateProjectionMatrix_action_apply, firstCoordinateRestriction_apply]
  simp only [ite_pow]
  norm_num
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < m
  rw [show (∑ j : Fin n, if j.val < m then x j ^ 2 else 0) =
      ∑ j ∈ S, x j ^ 2 by
        simp only [S, Finset.sum_filter]]
  symm
  apply Finset.sum_bij (fun i _ => Fin.castLE hmn i)
  · intro i hi; simp [S]
  · intro i₁ hi₁ i₂ hi₂ heq; exact Fin.castLE_injective hmn heq
  · intro j hj
    have hjlt : j.val < m := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i hi; rfl

/-- Identifies orthogonal action inv with transpose.

**Lean implementation helper.** -/
lemma orthogonalAction_inv_eq_transpose {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalAction U⁻¹ x = U.1ᵀ.toEuclideanLin x := by
  rfl

/-- The norm of projection onto a random Grassmannian subspace equals the first-coordinate projection norm after inverse orthogonal rotation.

**Lean implementation helper.** -/
lemma randomProjection_grassmannOrbit_norm {m n : ℕ}
    (hmn : m ≤ n) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖randomProjection (grassmannOrbit n m U) z‖ =
      coordinateProjectionNorm hmn (orthogonalAction U⁻¹ z) := by
  change ‖(U.1 * coordinateProjectionMatrix n m * U.1ᵀ).toEuclideanLin z‖ = _
  have hact :
      (U.1 * coordinateProjectionMatrix n m * U.1ᵀ).toEuclideanLin z =
        orthogonalAction U
          ((coordinateProjectionMatrix n m).toEuclideanLin
            (orthogonalAction U⁻¹ z)) := by
    rw [orthogonalAction_inv_eq_transpose]
    unfold orthogonalAction
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  rw [hact, norm_orthogonalAction,
    norm_coordinateProjectionMatrix_action hmn]

/-- Norm of the orthogonal projection onto a Grassmannian point.

**Lean implementation helper.** -/
def grassmannProjectedNorm {m n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (P : Grassmannian n m) : ℝ :=
  ‖randomProjection P z‖

/-- Establishes continuity of grassmann projected norm.

**Lean implementation helper.** -/
lemma continuous_grassmannProjectedNorm {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin n)) :
    Continuous (grassmannProjectedNorm (m := m) z) := by
  unfold grassmannProjectedNorm randomProjection HDP.matrixOperator
  apply continuous_norm.comp
  change Continuous (fun P : Grassmannian n m =>
    WithLp.toLp 2 (fun i : Fin n =>
      ∑ j : Fin n, P.1 i j * z j))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hval : Continuous (fun P : Grassmannian n m =>
      (P.1 : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val
  have hi : Continuous (fun P : Grassmannian n m => P.1 i) :=
    (continuous_apply i).comp hval
  have hij : Continuous (fun P : Grassmannian n m => P.1 i j) :=
    (continuous_apply j).comp hi
  exact hij.mul continuous_const

/-- For a Haar-random `m`-dimensional subspace and a fixed unit vector, the projected norm differs from `√(m/n)` by at least the relative amount `ε` with probability at most `2 exp(-ε²m/C²)`.

**Lean implementation helper.** -/
theorem grassmannProjectedNorm_unit_tail {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (grassmannHaarMeasure n m)
        {P | ε * Real.sqrt ((m : ℝ) / n) ≤
          |grassmannProjectedNorm (v : EuclideanSpace ℝ (Fin n)) P -
            Real.sqrt ((m : ℝ) / n)|} ≤
      ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
  let A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {x | ε * Real.sqrt ((m : ℝ) / n) ≤
      |coordinateProjectionNorm hmn x - Real.sqrt ((m : ℝ) / n)|}
  have hA : MeasurableSet A := by
    apply measurableSet_le
    · fun_prop
    · exact (((coordinateProjectionNorm_lipschitz hmn).continuous.measurable.comp
        measurable_subtype_coe).sub_const _).abs
  rw [grassmannHaarMeasure, Measure.map_apply
    (continuous_grassmannOrbit n m).measurable]
  · change (orthogonalHaarMeasure n)
      {U | ε * Real.sqrt ((m : ℝ) / n) ≤
        |‖randomProjection (grassmannOrbit n m U) v‖ -
          Real.sqrt ((m : ℝ) / n)|} ≤ _
    simp_rw [randomProjection_grassmannOrbit_norm hmn]
    change (orthogonalHaarMeasure n)
      ((inverseOrthogonalSphereOrbit v) ⁻¹' A) ≤ _
    rw [← Measure.map_apply (continuous_inverseOrthogonalSphereOrbit v).measurable hA,
      map_inverseOrthogonalSphereOrbit hn v]
    exact coordinateProjectionNorm_tail hn hmn hε
  · exact measurableSet_le
      (by fun_prop)
      (((continuous_grassmannProjectedNorm (m := m)
        (v : EuclideanSpace ℝ (Fin n))).measurable.sub_const _).abs)

/-- Computes the second moment of grassmann projected norm unit.

**Lean implementation helper.** -/
theorem grassmannProjectedNorm_unit_secondMoment {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (∫ P, grassmannProjectedNorm
        (v : EuclideanSpace ℝ (Fin n)) P ^ 2
      ∂grassmannHaarMeasure n m) = (m : ℝ) / n := by
  have hgrass :
      (∫ P, grassmannProjectedNorm
          (v : EuclideanSpace ℝ (Fin n)) P ^ 2
        ∂grassmannHaarMeasure n m) =
        ∫ U, coordinateProjectionNorm hmn
          (inverseOrthogonalSphereOrbit v U) ^ 2
          ∂orthogonalHaarMeasure n := by
    rw [grassmannHaarMeasure, integral_map
      (continuous_grassmannOrbit n m).measurable.aemeasurable]
    · simp_rw [grassmannProjectedNorm,
        randomProjection_grassmannOrbit_norm hmn]
      rfl
    · exact ((continuous_grassmannProjectedNorm (m := m)
        (v : EuclideanSpace ℝ (Fin n))).pow 2).aestronglyMeasurable
  rw [hgrass]
  have hmap := map_inverseOrthogonalSphereOrbit hn v
  have hsphere :
      (∫ x, coordinateProjectionNorm hmn x ^ 2
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
        ∫ U, coordinateProjectionNorm hmn
          (inverseOrthogonalSphereOrbit v U) ^ 2
          ∂orthogonalHaarMeasure n := by
    rw [← hmap, integral_map
      (continuous_inverseOrthogonalSphereOrbit v).measurable.aemeasurable]
    exact (((coordinateProjectionNorm_lipschitz hmn).continuous.comp
      continuous_subtype_val).pow 2).aestronglyMeasurable
  rw [← hsphere]
  exact coordinateProjectionNorm_secondMoment hn hmn

/-- Projected norm is absolutely homogeneous in the input vector.

**Lean implementation helper.** -/
@[simp] lemma grassmannProjectedNorm_smul {m n : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (P : Grassmannian n m) :
    grassmannProjectedNorm (c • z) P =
      |c| * grassmannProjectedNorm z P := by
  simp [grassmannProjectedNorm, map_smul, norm_smul, Real.norm_eq_abs]

/-- A nonzero vector normalized to a point of the Euclidean unit sphere.

**Lean implementation helper.** -/
private def normalizedSpherePoint {n : ℕ}
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨‖z‖⁻¹ • z, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz)), inv_mul_cancel₀]
    exact (norm_pos_iff.mpr hz).ne'⟩

/-- Rescaling a normalized nonzero vector by its original norm recovers the vector.

**Lean implementation helper.** -/
private lemma norm_smul_normalizedSpherePoint {n : ℕ}
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    ‖z‖ • (normalizedSpherePoint z hz : EuclideanSpace ℝ (Fin n)) = z := by
  change ‖z‖ • (‖z‖⁻¹ • z) = z
  rw [smul_smul, mul_inv_cancel₀ (norm_pos_iff.mpr hz).ne', one_smul]

/-- A random `m`-dimensional projection has exact second moment and concentrates for each fixed
vector.

**Book Lemma 5.3.2.** -/
theorem randomProjection_secondMoment {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin n)) :
    (∫ P, grassmannProjectedNorm z P ^ 2
      ∂grassmannHaarMeasure n m) =
      ((m : ℝ) / n) * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · subst z
    simp [grassmannProjectedNorm]
  · let v := normalizedSpherePoint z hz
    have hzrep : z = ‖z‖ • (v : EuclideanSpace ℝ (Fin n)) :=
      (norm_smul_normalizedSpherePoint z hz).symm
    have hproj (P : Grassmannian n m) :
        grassmannProjectedNorm z P = ‖z‖ *
          grassmannProjectedNorm
            (v : EuclideanSpace ℝ (Fin n)) P := by
      calc
        grassmannProjectedNorm z P =
            grassmannProjectedNorm
              (‖z‖ • (v : EuclideanSpace ℝ (Fin n))) P :=
          congrArg (fun w => grassmannProjectedNorm w P) hzrep
        _ = _ := by rw [grassmannProjectedNorm_smul,
          abs_of_nonneg (norm_nonneg z)]
    simp_rw [hproj, mul_pow]
    rw [integral_const_mul]
    rw [grassmannProjectedNorm_unit_secondMoment hn hmn v]
    ring

/-- Exact RMS/second-moment norm of a random projection.

**Book (5.10).** -/
theorem randomProjection_rms {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∫ P, grassmannProjectedNorm z P ^ 2
      ∂grassmannHaarMeasure n m) =
      Real.sqrt ((m : ℝ) / n) * ‖z‖ := by
  rw [randomProjection_secondMoment hn hmn]
  have hmnR : 0 ≤ (m : ℝ) / n := by positivity
  rw [Real.sqrt_mul hmnR, Real.sqrt_sq (norm_nonneg z)]

/-- Fixed-difference random-projection tail before the union bound.

**Book (5.11).** -/
theorem randomProjection_fixedVector_tail {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 ≤ ε) :
    (grassmannHaarMeasure n m)
        {P | ε * Real.sqrt ((m : ℝ) / n) * ‖z‖ <
          |grassmannProjectedNorm z P -
            Real.sqrt ((m : ℝ) / n) * ‖z‖|} ≤
      ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
  by_cases hz : z = 0
  · subst z
    simp [grassmannProjectedNorm]
  · let v := normalizedSpherePoint z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzrep : z = ‖z‖ • (v : EuclideanSpace ℝ (Fin n)) :=
      (norm_smul_normalizedSpherePoint z hz).symm
    have hproj (P : Grassmannian n m) :
        grassmannProjectedNorm z P = ‖z‖ *
          grassmannProjectedNorm
            (v : EuclideanSpace ℝ (Fin n)) P := by
      calc
        grassmannProjectedNorm z P =
            grassmannProjectedNorm
              (‖z‖ • (v : EuclideanSpace ℝ (Fin n))) P :=
          congrArg (fun w => grassmannProjectedNorm w P) hzrep
        _ = _ := by rw [grassmannProjectedNorm_smul,
          abs_of_nonneg (norm_nonneg z)]
    have hset :
        {P : Grassmannian n m |
          ε * Real.sqrt ((m : ℝ) / n) * ‖z‖ <
            |grassmannProjectedNorm z P -
              Real.sqrt ((m : ℝ) / n) * ‖z‖|} =
        {P : Grassmannian n m |
          ε * Real.sqrt ((m : ℝ) / n) <
            |grassmannProjectedNorm
              (v : EuclideanSpace ℝ (Fin n)) P -
              Real.sqrt ((m : ℝ) / n)|} := by
      ext P
      simp only [Set.mem_setOf_eq]
      rw [hproj]
      have hfactor : ‖z‖ * grassmannProjectedNorm
            (v : EuclideanSpace ℝ (Fin n)) P -
            Real.sqrt ((m : ℝ) / n) * ‖z‖ =
          ‖z‖ * (grassmannProjectedNorm
            (v : EuclideanSpace ℝ (Fin n)) P -
            Real.sqrt ((m : ℝ) / n)) := by ring
      rw [hfactor, abs_mul, abs_of_pos hzpos]
      rw [mul_comm (ε * Real.sqrt ((m : ℝ) / n)) ‖z‖]
      constructor <;> intro h <;> nlinarith
    rw [hset]
    refine (measure_mono ?_).trans
      (grassmannProjectedNorm_unit_tail hn hmn v hε)
    intro P hP
    change ε * Real.sqrt ((m : ℝ) / n) ≤
      |grassmannProjectedNorm (v : EuclideanSpace ℝ (Fin n)) P -
        Real.sqrt ((m : ℝ) / n)|
    exact hP.le

/-- Failure form of the corresponding lemma.

**Lean implementation helper.** -/
theorem randomProjection_relative_failure {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 ≤ ε) :
    (grassmannHaarMeasure n m)
        {P | ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖z‖ ≤
              grassmannProjectedNorm z P ∧
            grassmannProjectedNorm z P ≤
              (1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖z‖)} ≤
      ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
  have hsubset :
      {P : Grassmannian n m |
        ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖z‖ ≤
              grassmannProjectedNorm z P ∧
            grassmannProjectedNorm z P ≤
              (1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖z‖)} ⊆
      {P | ε * Real.sqrt ((m : ℝ) / n) * ‖z‖ <
          |grassmannProjectedNorm z P -
            Real.sqrt ((m : ℝ) / n) * ‖z‖|} := by
    intro P hP
    simp only [Set.mem_setOf_eq] at hP ⊢
    by_contra hnot
    have habs : |grassmannProjectedNorm z P -
        Real.sqrt ((m : ℝ) / n) * ‖z‖| ≤
        ε * Real.sqrt ((m : ℝ) / n) * ‖z‖ := le_of_not_gt hnot
    have hsqrt : 0 ≤ Real.sqrt ((m : ℝ) / n) := Real.sqrt_nonneg _
    have hnorm : 0 ≤ ‖z‖ := norm_nonneg _
    apply hP
    rw [abs_le] at habs
    constructor <;> nlinarith
  exact (measure_mono hsubset).trans
    (randomProjection_fixedVector_tail hn hmn z hε)

/-- Union-bound form of Johnson--Lindenstrauss before imposing a dimension condition.

**Book (5.11).** -/
theorem finitePoint_randomProjection_failure {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (grassmannHaarMeasure n m)
        {P | ∃ x ∈ X, ∃ y ∈ X,
          ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖ ≤
                grassmannProjectedNorm (x - y) P ∧
              grassmannProjectedNorm (x - y) P ≤
                (1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖)} ≤
      (X.card : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (2 * Real.exp
          (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
  classical
  let E : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) → Set (Grassmannian n m) :=
    fun x y => {P | ¬
      ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖ ≤
          grassmannProjectedNorm (x - y) P ∧
        grassmannProjectedNorm (x - y) P ≤
          (1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖)}
  have hbad : {P : Grassmannian n m | ∃ x ∈ X, ∃ y ∈ X,
        ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖ ≤
              grassmannProjectedNorm (x - y) P ∧
            grassmannProjectedNorm (x - y) P ≤
              (1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖)} =
      ⋃ x ∈ X, ⋃ y ∈ X, E x y := by
    ext P
    simp [E]
  rw [hbad]
  calc
    (grassmannHaarMeasure n m) (⋃ x ∈ X, ⋃ y ∈ X, E x y) ≤
        ∑ x ∈ X, (grassmannHaarMeasure n m) (⋃ y ∈ X, E x y) :=
      measure_biUnion_finset_le X _
    _ ≤ ∑ x ∈ X, ∑ y ∈ X,
        (grassmannHaarMeasure n m) (E x y) := by
      apply Finset.sum_le_sum
      intro x hx
      exact measure_biUnion_finset_le X (E x)
    _ ≤ ∑ _x ∈ X, ∑ _y ∈ X,
        ENNReal.ofReal (2 * Real.exp
          (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact randomProjection_relative_failure hn hmn (x - y) hε
    _ = (X.card : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (2 * Real.exp
          (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
      simp [pow_two]
      ring

/-- The source's data-independent scaled projection `Q = sqrt (n/m) P`.

**Lean implementation helper.** -/
def johnsonLindenstraussMap {m n : ℕ} (P : Grassmannian n m) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Real.sqrt ((n : ℝ) / m) • randomProjection P

/-- The Johnson--Lindenstrauss map scales the projected norm by `sqrt (n / m)`.

**Lean implementation helper.** -/
@[simp] theorem norm_johnsonLindenstraussMap {m n : ℕ}
    (P : Grassmannian n m) (z : EuclideanSpace ℝ (Fin n)) :
    ‖johnsonLindenstraussMap P z‖ =
      Real.sqrt ((n : ℝ) / m) * grassmannProjectedNorm z P := by
  simp [johnsonLindenstraussMap, grassmannProjectedNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- For positive dimensions, `√(n/m) · √(m/n) = 1`.

**Lean implementation helper.** -/
lemma sqrt_dimensionRatio_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt ((n : ℝ) / m) * Real.sqrt ((m : ℝ) / n) = 1 := by
  have hnm : 0 ≤ (n : ℝ) / m := by positivity
  rw [← Real.sqrt_mul hnm]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : ((n : ℝ) / m) * ((m : ℝ) / n) = 1 := by
    field_simp [hmR.ne', hnR.ne']
  rw [hprod, Real.sqrt_one]

/-- The random map is chosen independently of `X`; the bound contains no ambient-dimension
factor.

**Book Theorem 5.3.1.** -/
theorem theorem_5_3_1 {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (grassmannHaarMeasure n m)
        {P | ∃ x ∈ X, ∃ y ∈ X,
          ¬ ((1 - ε) * ‖x - y‖ ≤
                ‖johnsonLindenstraussMap P (x - y)‖ ∧
              ‖johnsonLindenstraussMap P (x - y)‖ ≤
                (1 + ε) * ‖x - y‖)} ≤
      (X.card : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (2 * Real.exp
          (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) := by
  have hscale := sqrt_dimensionRatio_mul hm hn
  have hsubset :
      {P : Grassmannian n m | ∃ x ∈ X, ∃ y ∈ X,
        ¬ ((1 - ε) * ‖x - y‖ ≤
              ‖johnsonLindenstraussMap P (x - y)‖ ∧
            ‖johnsonLindenstraussMap P (x - y)‖ ≤
              (1 + ε) * ‖x - y‖)} ⊆
      {P | ∃ x ∈ X, ∃ y ∈ X,
        ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖ ≤
              grassmannProjectedNorm (x - y) P ∧
            grassmannProjectedNorm (x - y) P ≤
              (1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖)} := by
    intro P hP
    simp only [Set.mem_setOf_eq] at hP ⊢
    obtain ⟨x, hx, y, hy, hbad⟩ := hP
    refine ⟨x, hx, y, hy, ?_⟩
    intro hgood
    apply hbad
    rw [norm_johnsonLindenstraussMap]
    constructor
    · calc
        (1 - ε) * ‖x - y‖ = Real.sqrt ((n : ℝ) / m) *
            ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖) := by
          calc
            _ = (1 - ε) *
                (Real.sqrt ((n : ℝ) / m) *
                  Real.sqrt ((m : ℝ) / n)) * ‖x - y‖ := by
              rw [hscale, mul_one]
            _ = _ := by ring
        _ ≤ Real.sqrt ((n : ℝ) / m) *
            grassmannProjectedNorm (x - y) P :=
          mul_le_mul_of_nonneg_left hgood.1 (Real.sqrt_nonneg _)
    · calc
        Real.sqrt ((n : ℝ) / m) *
            grassmannProjectedNorm (x - y) P ≤
            Real.sqrt ((n : ℝ) / m) *
              ((1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hgood.2 (Real.sqrt_nonneg _)
        _ = (1 + ε) * ‖x - y‖ := by
          calc
            _ = (1 + ε) *
                (Real.sqrt ((n : ℝ) / m) *
                  Real.sqrt ((m : ℝ) / n)) * ‖x - y‖ := by ring
            _ = _ := by rw [hscale, mul_one]
  exact (measure_mono hsubset).trans
    (finitePoint_randomProjection_failure hn hmn X hε)

/-- Under the Johnson--Lindenstrauss dimension condition, the pair-count union factor is absorbed into a weaker exponential tail.

**Lean implementation helper.** -/
private lemma jl_union_factor_le {N m : ℕ} {ε : ℝ}
    (hlog : 2 * Real.log (N : ℝ) ≤
      (ε ^ 2 * m / randomProjectionTailConstant ^ 2) / 2) :
    (N : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m / randomProjectionTailConstant ^ 2))) ≤
      ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m /
          (2 * randomProjectionTailConstant ^ 2)))) := by
  let a : ℝ := ε ^ 2 * m / randomProjectionTailConstant ^ 2
  have ha : -(ε ^ 2 * (m : ℝ) /
        (2 * randomProjectionTailConstant ^ 2)) = -a / 2 := by
    dsimp [a]
    ring
  rw [ha]
  have hreal : (N : ℝ) ^ 2 * (2 * Real.exp (-a)) ≤
      2 * Real.exp (-a / 2) := by
    by_cases hN : N = 0
    · subst N
      norm_num
      positivity
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hNpow : (N : ℝ) ^ 2 =
          Real.exp (2 * Real.log (N : ℝ)) := by
        calc
          (N : ℝ) ^ 2 =
              (Real.exp (Real.log (N : ℝ))) ^ 2 := by
            rw [Real.exp_log hNpos]
          _ = Real.exp (2 * Real.log (N : ℝ)) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
      calc
        (N : ℝ) ^ 2 * (2 * Real.exp (-a)) =
            2 * Real.exp (2 * Real.log (N : ℝ) - a) := by
          rw [hNpow]
          calc
            Real.exp (2 * Real.log (N : ℝ)) *
                (2 * Real.exp (-a)) =
                2 * (Real.exp (2 * Real.log (N : ℝ)) *
                  Real.exp (-a)) := by ring
            _ = 2 * Real.exp (2 * Real.log (N : ℝ) + -a) := by
              rw [Real.exp_add]
            _ = _ := by ring_nf
        _ ≤ 2 * Real.exp (-a / 2) := by
          gcongr
          change 2 * Real.log (N : ℝ) ≤ a / 2 at hlog
          linarith
  calc
    (N : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-a)) =
        ENNReal.ofReal ((N : ℝ) ^ 2) *
          ENNReal.ofReal (2 * Real.exp (-a)) := by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg N)]
      simp
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 *
          (2 * Real.exp (-a))) := by
      rw [ENNReal.ofReal_mul (sq_nonneg (N : ℝ))]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-a / 2)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The advertised exponentially small failure probability under the log-cardinality dimension
condition.

**Book Theorem 5.3.1.** -/
theorem theorem_5_3_1_exponential {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hlog : 2 * Real.log (X.card : ℝ) ≤
      (ε ^ 2 * m / randomProjectionTailConstant ^ 2) / 2) :
    (grassmannHaarMeasure n m)
        {P | ∃ x ∈ X, ∃ y ∈ X,
          ¬ ((1 - ε) * ‖x - y‖ ≤
                ‖johnsonLindenstraussMap P (x - y)‖ ∧
              ‖johnsonLindenstraussMap P (x - y)‖ ≤
                (1 + ε) * ‖x - y‖)} ≤
      ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m /
          (2 * randomProjectionTailConstant ^ 2)))) :=
  (theorem_5_3_1 hm hn hmn X hε).trans (jl_union_factor_le hlog)

/-- Source-style sufficient condition `m ≥ C ε⁻² log N`, with the explicit absolute constant
generated by the proof.

**Book Theorem 5.3.1.** -/
theorem theorem_5_3_1_of_dimension {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 < ε) (_hε1 : ε < 1)
    (hdim : 4 * randomProjectionTailConstant ^ 2 *
        Real.log (X.card : ℝ) / ε ^ 2 ≤ m) :
    (grassmannHaarMeasure n m)
        {P | ∃ x ∈ X, ∃ y ∈ X,
          ¬ ((1 - ε) * ‖x - y‖ ≤
                ‖johnsonLindenstraussMap P (x - y)‖ ∧
              ‖johnsonLindenstraussMap P (x - y)‖ ≤
                (1 + ε) * ‖x - y‖)} ≤
      ENNReal.ofReal (2 * Real.exp
        (- (ε ^ 2 * m /
          (2 * randomProjectionTailConstant ^ 2)))) := by
  apply theorem_5_3_1_exponential hm hn hmn X hε.le
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hC : 0 < 2 * randomProjectionTailConstant ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos randomProjectionTailConstant_pos)
  rw [show ε ^ 2 * (m : ℝ) / randomProjectionTailConstant ^ 2 / 2 =
      ε ^ 2 * (m : ℝ) /
        (2 * randomProjectionTailConstant ^ 2) by ring]
  apply (le_div_iff₀ hC).2
  have hd := (div_le_iff₀ hεsq).mp hdim
  nlinarith


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The one-direction Bernstein tail appearing in the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def subGaussianJLPointTail (m : ℕ) (K ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
    min (ε ^ 2 / ((4 * K ^ 2) ^ 2 * (1 / (m : ℝ))))
      (ε / ((4 * K ^ 2) * (1 / (m : ℝ))))))

/-- The Chapter 4 unit-direction estimate, rescaled to an arbitrary vector. The strict failure
event makes the zero vector harmless.

**Book Exercise 5.14.** -/
theorem fixed_vector_normalized_sq_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ {ω | ε * ‖z‖ ^ 2 <
        |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin z‖ ^ 2 - ‖z‖ ^ 2|} ≤
      subGaussianJLPointTail m K ε := by
  by_cases hz : z = 0
  · subst z
    simp [subGaussianJLPointTail]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let x : EuclideanSpace ℝ (Fin n) := ‖z‖⁻¹ • z
    have hx : ‖x‖ = 1 := by
      simp [x, norm_smul, hzpos.ne']
    have hscale (ω : Ω) :
        |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1| =
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin z‖ ^ 2 - ‖z‖ ^ 2| /
            ‖z‖ ^ 2 := by
      have hnorm : ‖(A ω).toEuclideanLin x‖ =
          ‖z‖⁻¹ * ‖(A ω).toEuclideanLin z‖ := by
        rw [show (A ω).toEuclideanLin x = ‖z‖⁻¹ •
            (A ω).toEuclideanLin z by simp [x], norm_smul,
          Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzpos)]
      rw [hnorm]
      have hsqpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hzpos
      have halg :
          (m : ℝ)⁻¹ * (‖z‖⁻¹ * ‖(A ω).toEuclideanLin z‖) ^ 2 - 1 =
            ((m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin z‖ ^ 2 - ‖z‖ ^ 2) /
              ‖z‖ ^ 2 := by
        field_simp [hzpos.ne']
      rw [halg, abs_div, abs_of_pos hsqpos]
    have hsubevent :
        {ω | ε * ‖z‖ ^ 2 <
            |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin z‖ ^ 2 - ‖z‖ ^ 2|} ⊆
          {ω | ε ≤
            |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1|} := by
      intro ω hω
      change ε ≤
        |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1|
      rw [hscale]
      apply le_of_lt
      rw [lt_div_iff₀ (sq_pos_of_pos hzpos)]
      simpa [mul_comm] using hω
    calc
      μ {ω | ε * ‖z‖ ^ 2 <
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin z‖ ^ 2 - ‖z‖ ^ 2|}
          ≤ μ {ω | ε ≤
            |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin x‖ ^ 2 - 1|} :=
        measure_mono hsubevent
      _ ≤ subGaussianJLPointTail m K ε := by
        simpa [subGaussianJLPointTail] using
          HDP.Chapter4.fixed_direction_normalized_sq_tail hm A hrowsm hsub hiso
            hindep hfinite hK hpsi x hx hε

/-- Subgaussian/Rademacher random matrices give a JL embedding.

**Book Exercise 5.14.** -/
theorem finitePoint_subGaussianJL_sq_failure [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (S : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ {ω | ∃ x ∈ S, ∃ y ∈ S,
        ε * ‖x - y‖ ^ 2 <
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin (x - y)‖ ^ 2 -
            ‖x - y‖ ^ 2|} ≤
      (S.card : ℝ≥0∞) ^ 2 * subGaussianJLPointTail m K ε := by
  classical
  let E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → Set Ω :=
    fun x y => {ω | ε * ‖x - y‖ ^ 2 <
      |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin (x - y)‖ ^ 2 - ‖x - y‖ ^ 2|}
  have hbad : {ω | ∃ x ∈ S, ∃ y ∈ S,
        ε * ‖x - y‖ ^ 2 <
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin (x - y)‖ ^ 2 -
            ‖x - y‖ ^ 2|} =
      ⋃ x ∈ S, ⋃ y ∈ S, E x y := by
    ext ω
    simp [E]
  rw [hbad]
  calc
    μ (⋃ x ∈ S, ⋃ y ∈ S, E x y)
        ≤ ∑ x ∈ S, μ (⋃ y ∈ S, E x y) := measure_biUnion_finset_le S _
    _ ≤ ∑ x ∈ S, ∑ y ∈ S, μ (E x y) := by
      apply Finset.sum_le_sum
      intro x hx
      exact measure_biUnion_finset_le S (E x)
    _ ≤ ∑ _x ∈ S, ∑ _y ∈ S, subGaussianJLPointTail m K ε := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact fixed_vector_normalized_sq_tail hm A hrowsm hsub hiso hindep
        hfinite hK hpsi (x - y) hε
    _ = (S.card : ℝ≥0∞) ^ 2 * subGaussianJLPointTail m K ε := by
      simp [pow_two]
      ring

/-! ## Binary/Rademacher specialization -/

/-- An explicit row-`psi2` constant for independent Rademacher coordinates. It is not optimized;
the extra `sqrt 5` comes from converting the proved tail bound back to the authoritative Orlicz
norm.

**Lean implementation helper.** -/
noncomputable def rademacherJLRowConstant : ℝ :=
  Real.sqrt 5 * Real.sqrt (30 / Real.log 2)

/-- Shows that rademacher jlrow constant is positive.

**Lean implementation helper.** -/
lemma rademacherJLRowConstant_pos : 0 < rademacherJLRowConstant := by
  unfold rademacherJLRowConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- Every unit marginal of a row with independent Rademacher coordinates has the same explicit
dimension-free `psi2` bound.

**Lean implementation helper.** -/
theorem rademacher_row_direction_psi2_le [IsProbabilityMeasure μ]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrad : ∀ i j, HDP.IsRademacher (fun ω => A ω i j) μ)
    (hwithin : ∀ i, iIndepFun (fun j ω => A ω i j) μ)
    (i : Fin m) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    HDP.psi2Norm
        (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) u) μ ≤
      rademacherJLRowConstant := by
  let K₁ : ℝ := Real.sqrt (30 / Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₁ : 0 < K₁ := Real.sqrt_pos.2 (by positivity)
  have hsum : ∑ j : Fin n, (u j) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hu]
    norm_num
  have hmeas : AEMeasurable
      (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) u) μ :=
    (HDP.RandomMatrix.AEMeasurableEntries.aemeasurable_rows
      (fun i j => (hrad i j).aemeasurable)).aemeasurable_marginal i u
  have htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |inner ℝ (HDP.randomMatrixRow A i ω) u|} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / K₁ ^ 2)) := by
    intro t ht
    have h := HDP.example_2_7_4 (fun j => hrad i j) (hwithin i)
      (fun j => u j) ht
    have hKsq : K₁ ^ 2 = 30 / Real.log 2 := by
      dsimp [K₁]
      rw [Real.sq_sqrt (by positivity)]
    have hexp :
        -(t ^ 2 * Real.log 2) / (30 * ∑ j : Fin n, (u j) ^ 2) =
          -t ^ 2 / K₁ ^ 2 := by
      rw [hsum, mul_one, hKsq]
      field_simp [hlog.ne']
    simpa [HDP.inner_randomMatrixRow, mul_comm, hexp] using h
  have h := HDP.psi2Norm_le_of_tail_bound hmeas hK₁ htail
  simpa [rademacherJLRowConstant, K₁] using h.2

/-- Binary specialization of the corresponding exercise. The assumptions say that each row has
independent Rademacher coordinates and that the row vectors are independent. All generic
random-matrix hypotheses, including the technical boundedness certificate for the real-valued
vector supremum, are proved here.

**Book Exercise 5.14.** -/
theorem finitePoint_rademacherJL_sq_failure [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m) [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrad : ∀ i j, HDP.IsRademacher (fun ω => A ω i j) μ)
    (hwithin : ∀ i, iIndepFun (fun j ω => A ω i j) μ)
    (hrowind : HDP.RandomMatrix.IndependentRows A μ)
    (S : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ {ω | ∃ x ∈ S, ∃ y ∈ S,
        ε * ‖x - y‖ ^ 2 <
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin (x - y)‖ ^ 2 -
            ‖x - y‖ ^ 2|} ≤
      (S.card : ℝ≥0∞) ^ 2 *
        subGaussianJLPointTail m rademacherJLRowConstant ε := by
  have hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ :=
    HDP.RandomMatrix.AEMeasurableEntries.aemeasurable_rows
      (fun i j => (hrad i j).aemeasurable)
  have hsub : HDP.RandomMatrix.SubGaussianRows A μ := by
    intro i
    have h := (HDP.Chapter3.rademacherVector_subGaussian
      (fun j => hrad i j) (hwithin i)).1
    have heq : HDP.randomMatrixRow A i =
        HDP.Chapter3.vectorOfCoordinates (fun j ω => A ω i j) := by
      rfl
    rw [heq]
    exact h
  have hiso : HDP.RandomMatrix.IsotropicRows A μ := by
    intro i
    have h := HDP.Chapter3.rademacherVector_isIsotropic
      (fun j => hrad i j) (hwithin i)
    have heq : HDP.randomMatrixRow A i =
        HDP.Chapter3.vectorOfCoordinates (fun j ω => A ω i j) := by
      rfl
    rw [heq]
    exact h
  have hfinite : HDP.RandomMatrix.RowPsi2Finite A μ := by
    intro i
    refine ⟨rademacherJLRowConstant, ?_⟩
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact rademacher_row_direction_psi2_le A hrad hwithin i u hu
  have hpsi : HDP.RandomMatrix.RowPsi2Bound A μ
      rademacherJLRowConstant := by
    intro i
    rw [HDP.psi2NormVector]
    apply csSup_le
    · let e : EuclideanSpace ℝ (Fin n) :=
        EuclideanSpace.single ⟨0, NeZero.pos n⟩ 1
      exact ⟨HDP.psi2Norm
        (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) e) μ,
          e, by simp [e], rfl⟩
    · intro r hr
      rcases hr with ⟨u, hu, rfl⟩
      exact rademacher_row_direction_psi2_le A hrad hwithin i u hu
  exact finitePoint_subGaussianJL_sq_failure hm A hrowsm hsub hiso hrowind
    hfinite rademacherJLRowConstant_pos hpsi S hε

/-- Controls all pairwise squared-distance distortions of a finite set under a subgaussian
random matrix.

**Book Exercise 5.14.** -/
theorem exercise_5_14_subGaussian [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 0 < K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (S : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ {ω | ∃ x ∈ S, ∃ y ∈ S,
        ε * ‖x - y‖ ^ 2 <
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin (x - y)‖ ^ 2 -
            ‖x - y‖ ^ 2|} ≤
      (S.card : ℝ≥0∞) ^ 2 * subGaussianJLPointTail m K ε :=
  finitePoint_subGaussianJL_sq_failure hm A hrowsm hsub hiso hindep
    hfinite hK hpsi S hε

/-- Specializes the finite-set squared-distance distortion bound to independent Rademacher rows.

**Book Exercise 5.14.** -/
theorem exercise_5_14_rademacher [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m) [NeZero n]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hrad : ∀ i j, HDP.IsRademacher (fun ω => A ω i j) μ)
    (hwithin : ∀ i, iIndepFun (fun j ω => A ω i j) μ)
    (hrowind : HDP.RandomMatrix.IndependentRows A μ)
    (S : Finset (EuclideanSpace ℝ (Fin n)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ {ω | ∃ x ∈ S, ∃ y ∈ S,
        ε * ‖x - y‖ ^ 2 <
          |(m : ℝ)⁻¹ * ‖(A ω).toEuclideanLin (x - y)‖ ^ 2 -
            ‖x - y‖ ^ 2|} ≤
      (S.card : ℝ≥0∞) ^ 2 *
        subGaussianJLPointTail m rademacherJLRowConstant ε :=
  finitePoint_rademacherJL_sq_failure hm A hrad hwithin hrowind S hε


abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n N : ℕ} [NeZero n]

/-- A finite Euclidean set with pairwise distances greater than `1` and diameter at most `2` has at most `5^n` points.

**Lean implementation helper.** -/
theorem separated_diameter_two_card_le (F : Finset (Euc n))
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 1 < dist x y)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, dist x y ≤ 2) :
    F.card ≤ 5 ^ n := by
  by_cases hF : F.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hF
    let ε : ℝ≥0 := 1
    have hε : 0 < ε := by norm_num [ε]
    have hsep' : Metric.IsSeparated ε (↑F : Set (Euc n)) := by
      intro x hx y hy hxy
      change (ε : ℝ≥0∞) < edist x y
      rw [edist_dist]
      simpa [ε] using
        (ENNReal.ofReal_lt_ofReal_iff (dist_pos.mpr hxy) |>.2
          (hsep x hx y hy hxy))
    have hpack : ((F.card : ℕ∞) : ℝ≥0∞) ≤
        (Metric.packingNumber ε (↑F : Set (Euc n)) : ℝ≥0∞) := by
      have h := hsep'.encard_le_packingNumber (A := (↑F : Set (Euc n)))
        (Set.Subset.rfl)
      exact_mod_cast h
    have hp := (HDP.Chapter4.proposition_4_2_10
      (n := n) (K := (↑F : Set (Euc n))) hε).2.2
    have hM : HDP.minkowskiSum (↑F : Set (Euc n))
          (Metric.closedBall (0 : Euc n) ((ε : ℝ) / 2)) ⊆
        Metric.closedBall z₀ (5 / 2 : ℝ) := by
      intro z hz
      obtain ⟨x, hxF, b, hb, rfl⟩ := HDP.mem_minkowskiSum.mp hz
      rw [Metric.mem_closedBall] at hb ⊢
      calc
        dist (x + b) z₀ ≤ dist (x + b) x + dist x z₀ := dist_triangle _ _ _
        _ = ‖b‖ + dist x z₀ := by simp [dist_eq_norm]
        _ ≤ (1 / 2 : ℝ) + 2 := by
          gcongr
          · simpa [ε, Metric.mem_closedBall, dist_zero_right] using hb
          · exact hdiam x hxF z₀ hz₀
        _ = 5 / 2 := by norm_num
    have hp' : (Metric.packingNumber ε (↑F : Set (Euc n)) : ℝ≥0∞) *
          volume (Metric.closedBall (0 : Euc n) (1 / 2 : ℝ)) ≤
        volume (Metric.closedBall z₀ (5 / 2 : ℝ)) := by
      simpa [ε] using hp.trans (measure_mono hM)
    let c : ℝ≥0∞ := ENNReal.ofReal
      (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
    have hc0 : c ≠ 0 := by
      dsimp [c]
      positivity
    have hct : c ≠ ⊤ := by simp [c]
    rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall] at hp'
    simp only [Fintype.card_fin] at hp'
    change (Metric.packingNumber ε (↑F : Set (Euc n)) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 2 : ℝ) ^ n * c) ≤
      ENNReal.ofReal (5 / 2 : ℝ) ^ n * c at hp'
    rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hc0 hct] at hp'
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
      rfl
    have hfivehalf : ENNReal.ofReal (5 / 2 : ℝ) = ((5 / 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
      rfl
    rw [hhalf, hfivehalf] at hp'
    have hden0 : ((((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n)) ≠ 0 := by positivity
    have hdent : ((((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n)) ≠ ⊤ := by simp
    have hpacking_le :
        (Metric.packingNumber ε (↑F : Set (Euc n)) : ℝ≥0∞) ≤
          (((5 : ℝ≥0) : ℝ≥0∞) ^ n) := by
      rw [← ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)] at hp'
      calc
        _ ≤ ((((5 / 2 : ℝ≥0) : ℝ≥0∞) ^ n) /
            (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n)) := hp'
        _ = (((5 : ℝ≥0) : ℝ≥0∞) ^ n) := by
          have hdenNN : (1 / 2 : ℝ≥0) ^ n ≠ 0 := by positivity
          rw [← ENNReal.coe_pow, ← ENNReal.coe_pow]
          rw [← ENNReal.coe_div hdenNN]
          norm_cast
          rw [← div_pow]
          norm_num
    have hcardENN : ((F.card : ℕ∞) : ℝ≥0∞) ≤
        (((5 : ℝ≥0) : ℝ≥0∞) ^ n) := hpack.trans hpacking_le
    have hcardENN' : (F.card : ℝ≥0∞) ≤ ((5 ^ n : ℕ) : ℝ≥0∞) := by
      simpa using hcardENN
    exact_mod_cast hcardENN'
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp

/-- Unit-ball specialization: a finite `1`-separated subset of the Euclidean unit ball has at
most `5^n` elements.

**Lean implementation helper.** -/
theorem unitBall_oneSeparated_card_le (F : Finset (Euc n))
    (hunit : ∀ x ∈ F, x ∈ Metric.closedBall (0 : Euc n) 1)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 1 < dist x y) :
    F.card ≤ 5 ^ n := by
  apply separated_diameter_two_card_le F hsep
  intro x hx y hy
  have hx' : dist x 0 ≤ 1 := by
    simpa [Metric.mem_closedBall] using hunit x hx
  have hy' : dist 0 y ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_comm] using hunit y hy
  calc
    dist x y ≤ dist x 0 + dist 0 y := dist_triangle _ _ _
    _ ≤ 1 + 1 := add_le_add hx' hy'
    _ = 2 := by norm_num

/-- The logarithmic target dimension is optimal in general, even for nonlinear embeddings.

**Book Remark 5.3.4.** -/
theorem exercise_5_15a (F : Finset (Euc n))
    (hunit : ∀ x ∈ F, x ∈ Metric.closedBall (0 : Euc n) 1)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 1 < dist x y) :
    F.card ≤ 5 ^ n :=
  unitBall_oneSeparated_card_le F hunit hsep

/-- Indexed-family version of the corresponding exercise.

**Lean implementation helper.** -/
theorem separated_diameter_two_family_card_le (z : Fin N → Euc n)
    (hsep : ∀ i j, i ≠ j → 1 < dist (z i) (z j))
    (hdiam : ∀ i j, dist (z i) (z j) ≤ 2) :
    N ≤ 5 ^ n := by
  classical
  have hz_inj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have hs := hsep i j hne
    rw [hij, dist_self] at hs
    norm_num at hs
  let F : Finset (Euc n) := Finset.univ.image z
  have hFcard : F.card = N := by
    simpa [F] using Finset.card_image_of_injective Finset.univ hz_inj
  have hFsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 1 < dist x y := by
    intro x hx y hy hxy
    simp only [F, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hsep i j (fun hij => hxy (congrArg z hij))
  have hFdiam : ∀ x ∈ F, ∀ y ∈ F, dist x y ≤ 2 := by
    intro x hx y hy
    simp only [F, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hdiam i j
  rw [← hFcard]
  exact separated_diameter_two_card_le F hFsep hFdiam

/-- The explicit orthogonal point configuration suggested for the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def orthogonalPoints (N : ℕ) (i : Fin N) : Euc N :=
  EuclideanSpace.single i 1

/-- Distinct points in the orthogonal-point construction are exactly `√2` apart.

**Lean implementation helper.** -/
lemma orthogonalPoints_dist {i j : Fin N} (hij : i ≠ j) :
    dist (orthogonalPoints N i) (orthogonalPoints N j) = Real.sqrt 2 := by
  have hsq : dist (orthogonalPoints N i) (orthogonalPoints N j) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real]
    simp [orthogonalPoints, EuclideanSpace.inner_single_left, hij]
    norm_num
  have hd : 0 ≤ dist (orthogonalPoints N i) (orthogonalPoints N j) := dist_nonneg
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- Proves the strict bound comparing five pow with of dimension lt half log.

**Lean implementation helper.** -/
lemma five_pow_lt_of_dimension_lt_half_log
    (hsmall : (n : ℝ) < (1 / 2 : ℝ) * Real.log (N : ℝ)) :
    5 ^ n < N := by
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hNgt : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp hlogNpos
  have hNpos : (0 : ℝ) < N := lt_trans (by norm_num) hNgt
  have hlog5 : Real.log 5 < 2 :=
    Real.log_five_lt_d9.trans (by norm_num)
  have hlogs : Real.log ((5 ^ n : ℕ) : ℝ) < Real.log (N : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_neZero n
    have hmul := mul_lt_mul_of_pos_left hlog5 hnpos
    have hdim : (n : ℝ) * 2 < Real.log (N : ℝ) := by
      nlinarith [hsmall]
    exact hmul.trans hdim
  have hreal : (((5 ^ n : ℕ) : ℝ)) < (N : ℝ) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < ((5 ^ n : ℕ) : ℝ)),
      ← Real.exp_log hNpos]
    exact Real.exp_lt_exp.mpr hlogs
  exact_mod_cast hreal

/-- The logarithmic target dimension is optimal in general, even for nonlinear embeddings.

**Book Remark 5.3.4.** -/
theorem exercise_5_15b
    (hsmall : (n : ℝ) < (1 / 2 : ℝ) * Real.log (N : ℝ)) :
    ∃ x : Fin N → Euc N, ∀ T : Euc N → Euc n,
      ¬(∀ i j,
        (99 / 100 : ℝ) * dist (x i) (x j) ≤ dist (T (x i)) (T (x j)) ∧
        dist (T (x i)) (T (x j)) ≤
          (101 / 100 : ℝ) * dist (x i) (x j)) := by
  refine ⟨orthogonalPoints N, ?_⟩
  intro T hT
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := hsqrt.ne'
  let a : ℝ := 50 / (49 * Real.sqrt 2)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let z : Fin N → Euc n := fun i => a • T (orthogonalPoints N i)
  have hscale_dist (i j : Fin N) :
      dist (z i) (z j) = a *
        dist (T (orthogonalPoints N i)) (T (orthogonalPoints N j)) := by
    simp only [z]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, dist_eq_norm]
  have hlowcalc :
      1 < a * ((99 / 100 : ℝ) * Real.sqrt 2) := by
    have heq : a * ((99 / 100 : ℝ) * Real.sqrt 2) = 99 / 98 := by
      dsimp [a]
      field_simp [hsqrt0]; ring
    rw [heq]
    norm_num
  have huppcalc :
      a * ((101 / 100 : ℝ) * Real.sqrt 2) ≤ 2 := by
    have heq : a * ((101 / 100 : ℝ) * Real.sqrt 2) = 101 / 98 := by
      dsimp [a]
      field_simp [hsqrt0]; ring
    rw [heq]
    norm_num
  have hzsep : ∀ i j, i ≠ j → 1 < dist (z i) (z j) := by
    intro i j hij
    rw [hscale_dist]
    calc
      1 < a * ((99 / 100 : ℝ) * Real.sqrt 2) := hlowcalc
      _ ≤ a * dist (T (orthogonalPoints N i)) (T (orthogonalPoints N j)) := by
        gcongr
        simpa [orthogonalPoints_dist hij] using (hT i j).1
  have hzdiam : ∀ i j, dist (z i) (z j) ≤ 2 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [hscale_dist]
      calc
        a * dist (T (orthogonalPoints N i)) (T (orthogonalPoints N j)) ≤
            a * ((101 / 100 : ℝ) * Real.sqrt 2) := by
          gcongr
          simpa [orthogonalPoints_dist hij] using (hT i j).2
        _ ≤ 2 := huppcalc
  have hcard : N ≤ 5 ^ n :=
    separated_diameter_two_family_card_le z hzsep hzdiam
  exact (not_le_of_gt (five_pow_lt_of_dimension_lt_half_log hsmall)) hcard

end
end HDP.Chapter5

end Source_09_JohnsonLindenstrauss

/-! ## Material formerly in `10_MatrixCalculus.lean` -/

section Source_10_MatrixCalculus

/-!
# Matrix calculus and the Loewner order

the source works with real symmetric matrices.  We expose that interface through
entrywise complexification and use Mathlib's basis-independent continuous
functional calculus.  Inverse and logarithm statements are guarded by positive
definiteness, as required in the source correction audit.
-/

open Matrix Finset Filter
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace HDP.Chapter5

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The standard matrix function of a real symmetric matrix, represented in the complex
Hermitian functional calculus.

**Book Definition 5.4.2.** -/
noncomputable def matrixFunction (f : ℝ → ℝ) (A : Matrix n n ℝ) : Matrix n n ℂ :=
  cfc f (HDP.complexifyMatrix A)

/-- The Loewner order on real symmetric matrices.

**Book Definition 5.4.3.** -/
def RealLoewnerLE (A B : Matrix n n ℝ) : Prop :=
  HDP.complexifyMatrix A ≤ HDP.complexifyMatrix B

omit [Fintype n] [DecidableEq n] in
/-- Loewner order compares symmetric matrices by positive semidefiniteness.

**Book Definition 5.4.3.** -/
lemma realLoewnerLE_iff (A B : Matrix n n ℝ) :
    RealLoewnerLE A B ↔
      (HDP.complexifyMatrix B - HDP.complexifyMatrix A).PosSemidef := by
  exact Matrix.le_iff

/-- Spectral functional calculus defines `f(X)` by applying `f` to eigenvalues.

**Book Definition 5.4.2.** -/
lemma matrixFunction_isHermitian (f : ℝ → ℝ) (A : Matrix n n ℝ) :
    (matrixFunction f A).IsHermitian :=
  MatrixConcentration.isHermitian_cfc f _

/-- Spectral formulas for matrix powers, inverse, and exponential.

**Book (5.12).** -/
theorem matrixFunction_power (A : Matrix n n ℝ) (hA : A.IsHermitian) (q : ℕ) :
    matrixFunction (fun x : ℝ => x ^ q) A =
      (HDP.complexifyMatrix A) ^ q := by
  exact MatrixConcentration.cfc_pow_eq (HDP.complexifyMatrix_isHermitian hA) q

/-- Spectral formulas for matrix powers, inverse, and exponential.

**Book (5.12).** -/
theorem matrixFunction_powerSeries (A : Matrix n n ℝ) (hA : A.IsHermitian)
    {I : Set ℝ} (hspec : ∀ i,
      (HDP.complexifyMatrix_isHermitian hA).eigenvalues i ∈ I)
    {c : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ a ∈ I, Tendsto
      (fun N => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * a ^ q)
      atTop (nhds (f a))) :
    Tendsto
      (fun N => (c 0 : ℂ) • (1 : Matrix n n ℂ) +
        ∑ q ∈ Finset.Icc 1 N, (c q : ℂ) • (HDP.complexifyMatrix A) ^ q)
      atTop (nhds (matrixFunction f A)) := by
  exact MatrixConcentration.matrixFun_powerSeries
    (HDP.complexifyMatrix_isHermitian hA) hspec hf

/-- The power-series exponential agrees with the corresponding definition.

**Book Definition 5.4.2.** -/
theorem matrixExponential_eq_function (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    NormedSpace.exp (HDP.complexifyMatrix A) = matrixFunction Real.exp A :=
  MatrixConcentration.matrixExp_eq_cfc (HDP.complexifyMatrix_isHermitian hA)

/-- Loewner order implies eigenvalue/trace monotonicity, norm intervals, and scalar spectral
inequalities.

**Book Proposition 5.4.4.** -/
theorem loewner_lambdaMax_mono [Nonempty n] {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : RealLoewnerLE A B) :
    MatrixConcentration.lambdaMax (HDP.complexifyMatrix_isHermitian hA) ≤
      MatrixConcentration.lambdaMax (HDP.complexifyMatrix_isHermitian hB) :=
  MatrixConcentration.lambdaMax_le_of_loewner_le
    (HDP.complexifyMatrix_isHermitian hA)
    (HDP.complexifyMatrix_isHermitian hB) hAB

/-- The corresponding minimum-eigenvalue monotonicity.

**Lean implementation helper.** -/
theorem loewner_lambdaMin_mono [Nonempty n] {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : RealLoewnerLE A B) :
    MatrixConcentration.lambdaMin (HDP.complexifyMatrix_isHermitian hA) ≤
      MatrixConcentration.lambdaMin (HDP.complexifyMatrix_isHermitian hB) :=
  MatrixConcentration.lambdaMin_le_of_loewner_le
    (HDP.complexifyMatrix_isHermitian hA)
    (HDP.complexifyMatrix_isHermitian hB) hAB

omit [DecidableEq n] in
/-- Loewner order between real symmetric matrices implies monotonicity of the trace.

**Lean implementation helper.** -/
theorem loewner_trace_mono {A B : Matrix n n ℝ} (hAB : RealLoewnerLE A B) :
    A.trace ≤ B.trace := by
  classical
  have h := MatrixConcentration.trace_re_le_of_loewner_le hAB
  simpa [HDP.complexifyMatrix, Matrix.trace] using h

/-- Loewner order implies eigenvalue/trace monotonicity, norm intervals, and scalar spectral
inequalities.

**Book Proposition 5.4.4.** -/
theorem scalarInequality_to_matrix {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {I : Set ℝ} (hspec : ∀ i,
      (HDP.complexifyMatrix_isHermitian hA).eigenvalues i ∈ I)
    {f g : ℝ → ℝ} (hfg : ∀ x ∈ I, f x ≤ g x) :
    matrixFunction f A ≤ matrixFunction g A := by
  exact MatrixConcentration.transfer_rule
    (HDP.complexifyMatrix_isHermitian hA) hspec hfg

/-- `‖X‖<=a` is equivalent to `-aI <= X <= aI`.

**Book Remark 5.4.5.** -/
theorem matrixNorm_gives_loewnerInterval {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a : ℝ} (ha : ‖A‖ ≤ a) :
    -(a : ℂ) • (1 : Matrix n n ℂ) ≤ HDP.complexifyMatrix A ∧
      HDP.complexifyMatrix A ≤ (a : ℂ) • (1 : Matrix n n ℂ) := by
  have hAc := HDP.complexifyMatrix_isHermitian hA
  have hn : ‖HDP.complexifyMatrix A‖ ≤ a := by
    rw [HDP.complexifyMatrix_opNorm]
    exact ha
  have hnorm := MatrixConcentration.l2_opNorm_eq_max_lambda hAc
  have hlower : ∀ i, -a ≤ hAc.eigenvalues i := by
    intro i
    have hmin := MatrixConcentration.lambdaMin_le_eigenvalues hAc i
    have hnegmin : -(MatrixConcentration.lambdaMin hAc) ≤ a := by
      calc
        -(MatrixConcentration.lambdaMin hAc) ≤
            max (MatrixConcentration.lambdaMax hAc)
              (-(MatrixConcentration.lambdaMin hAc)) := le_max_right _ _
        _ = ‖HDP.complexifyMatrix A‖ := hnorm.symm
        _ ≤ a := hn
    linarith
  have hupper : ∀ i, hAc.eigenvalues i ≤ a := by
    intro i
    calc
      hAc.eigenvalues i ≤ MatrixConcentration.lambdaMax hAc :=
        MatrixConcentration.eigenvalues_le_lambdaMax hAc i
      _ ≤ max (MatrixConcentration.lambdaMax hAc)
          (-(MatrixConcentration.lambdaMin hAc)) := le_max_left _ _
      _ = ‖HDP.complexifyMatrix A‖ := hnorm.symm
      _ ≤ a := hn
  constructor
  · have h' := MatrixConcentration.transfer_rule hAc
      (I := Set.range hAc.eigenvalues) (fun i => ⟨i, rfl⟩)
      (f := fun _ : ℝ => -a) (g := id)
      (fun x hx => by rcases hx with ⟨i, rfl⟩; simpa using hlower i)
    rw [cfc_const (-a) _ hAc.isSelfAdjoint, cfc_id ℝ _ hAc.isSelfAdjoint] at h'
    simpa [Algebra.algebraMap_eq_smul_one, Complex.real_smul] using h'
  · have h := MatrixConcentration.transfer_rule hAc
      (I := Set.range hAc.eigenvalues) (fun i => ⟨i, rfl⟩)
      (f := id) (g := fun _ : ℝ => a)
      (fun x hx => by rcases hx with ⟨i, rfl⟩; simpa using hupper i)
    rw [cfc_id ℝ _ hAc.isSelfAdjoint, cfc_const a _ hAc.isSelfAdjoint] at h
    simpa [Algebra.algebraMap_eq_smul_one, Complex.real_smul] using h

/-- The Rayleigh quotient of the scalar matrix `aI` at a unit vector is `a`.

**Lean implementation helper.** -/
private lemma rayleigh_complex_smul_one {a : ℝ} {u : n → ℂ}
    (hu : MatrixConcentration.l2norm u = 1) :
    MatrixConcentration.rayleigh
      ((a : ℂ) • (1 : Matrix n n ℂ)) u = a := by
  have hcast : (a : ℂ) • (1 : Matrix n n ℂ) =
      a • (1 : Matrix n n ℂ) := by
    ext i j
    simp [Complex.real_smul]
  rw [hcast, MatrixConcentration.rayleigh_smul]
  have hone : MatrixConcentration.rayleigh (1 : Matrix n n ℂ) u = 1 := by
    rw [show MatrixConcentration.rayleigh (1 : Matrix n n ℂ) u =
      (star u ⬝ᵥ u).re from by simp [MatrixConcentration.rayleigh]]
    rw [MatrixConcentration.dotProduct_star_self_eq, Complex.ofReal_re, hu,
      one_pow]
  rw [hone, mul_one]

/-- `‖X‖<=a` is equivalent to `-aI <= X <= aI`.

**Book Remark 5.4.5.** -/
theorem loewnerInterval_gives_matrixNorm [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a : ℝ}
    (hlow : -(a : ℂ) • (1 : Matrix n n ℂ) ≤ HDP.complexifyMatrix A)
    (hhigh : HDP.complexifyMatrix A ≤ (a : ℂ) • (1 : Matrix n n ℂ)) :
    ‖A‖ ≤ a := by
  have hAc := HDP.complexifyMatrix_isHermitian hA
  have hmax : MatrixConcentration.lambdaMax hAc ≤ a := by
    apply MatrixConcentration.lambdaMax_le_of_forall_rayleigh hAc
    intro u hu
    have h := MatrixConcentration.rayleigh_mono_of_loewner_le hhigh u
    rwa [rayleigh_complex_smul_one hu] at h
  have hmin : -a ≤ MatrixConcentration.lambdaMin hAc := by
    apply MatrixConcentration.le_lambdaMin_of_forall_rayleigh hAc
    intro u hu
    have h := MatrixConcentration.rayleigh_mono_of_loewner_le hlow u
    have hneg : MatrixConcentration.rayleigh
        ((-(a : ℂ)) • (1 : Matrix n n ℂ)) u = -a := by
      simpa using (rayleigh_complex_smul_one (a := -a) hu)
    rwa [hneg] at h
  rw [← HDP.complexifyMatrix_opNorm,
    MatrixConcentration.l2_opNorm_eq_max_lambda hAc]
  exact max_le hmax (by linarith)

/-- Packaged as an equivalence in positive dimension.

**Book Remark 5.4.5.** -/
theorem matrixNorm_le_iff_loewnerInterval [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a : ℝ} :
    ‖A‖ ≤ a ↔
      (-(a : ℂ) • (1 : Matrix n n ℂ) ≤ HDP.complexifyMatrix A ∧
        HDP.complexifyMatrix A ≤ (a : ℂ) • (1 : Matrix n n ℂ)) :=
  ⟨matrixNorm_gives_loewnerInterval hA,
    fun h => loewnerInterval_gives_matrixNorm hA h.1 h.2⟩

/-- The first matrix in the explicit counterexample to unrestricted matrix
monotonicity. -/
def matrixMonotonicityCounterexampleA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- The second matrix in the explicit counterexample to unrestricted matrix
monotonicity. -/
def matrixMonotonicityCounterexampleB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 1]

/-- Scalar monotonicity does not imply matrix monotonicity. Both displayed
matrices are positive semidefinite and `B - A` is positive semidefinite, but
`B² - A²` has determinant `-1` and hence is not positive semidefinite.
Thus the increasing scalar function `x ↦ x²` on `[0,∞)` does not preserve
Loewner order for noncommuting matrices.

**Book Remark 5.4.6; Exercise 5.17.** -/
theorem square_not_matrixMonotone_counterexample :
    matrixMonotonicityCounterexampleA.PosSemidef ∧
      matrixMonotonicityCounterexampleB.PosSemidef ∧
      (matrixMonotonicityCounterexampleB -
        matrixMonotonicityCounterexampleA).PosSemidef ∧
      ¬ (matrixMonotonicityCounterexampleB *
          matrixMonotonicityCounterexampleB -
        matrixMonotonicityCounterexampleA *
          matrixMonotonicityCounterexampleA).PosSemidef := by
  have hA : matrixMonotonicityCounterexampleA.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [matrixMonotonicityCounterexampleA]
    · intro x
      simp [matrixMonotonicityCounterexampleA, dotProduct, Matrix.mulVec,
        Fin.sum_univ_two]
      simpa [pow_two] using sq_nonneg (x 0)
  have hB : matrixMonotonicityCounterexampleB.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [matrixMonotonicityCounterexampleB]
    · intro x
      simp [matrixMonotonicityCounterexampleB, dotProduct, Matrix.mulVec,
        Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 + x 1)]
  have hdiff :
      (matrixMonotonicityCounterexampleB -
        matrixMonotonicityCounterexampleA).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [matrixMonotonicityCounterexampleA,
          matrixMonotonicityCounterexampleB]
    · intro x
      simp [matrixMonotonicityCounterexampleA,
        matrixMonotonicityCounterexampleB, dotProduct, Matrix.mulVec,
        Fin.sum_univ_two]
      nlinarith [sq_nonneg (x 0 + x 1)]
  refine ⟨hA, hB, hdiff, ?_⟩
  intro hsq
  have hd := hsq.det_nonneg
  norm_num [matrixMonotonicityCounterexampleA,
    matrixMonotonicityCounterexampleB, Matrix.det_fin_two] at hd

/-- Simultaneous-diagonalization helper for the corresponding exercise. The direct source-facing
endpoint below constructs this certificate from commutation.

**Lean implementation helper.** -/
theorem commutingMatrixFunction_monotone
    {A B U : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) {a b : n → ℝ}
    (hAdiag : A = U * diagonal (RCLike.ofReal ∘ a) * Uᴴ)
    (hBdiag : B = U * diagonal (RCLike.ofReal ∘ b) * Uᴴ)
    (hab : ∀ i, a i ≤ b i) {f : ℝ → ℝ} (hf : Monotone f) :
    cfc f A ≤ cfc f B := by
  rw [MatrixConcentration.cfc_unitary_diagonal hA hU hAdiag f,
    MatrixConcentration.cfc_unitary_diagonal hB hU hBdiag f]
  have hdiag :
      (diagonal (RCLike.ofReal ∘ f ∘ a) : Matrix n n ℂ) ≤
        diagonal (RCLike.ofReal ∘ f ∘ b) := by
    rw [Matrix.le_iff]
    have hpsd := (MatrixConcentration.posSemidef_diagonal_real_iff
      (fun i => f (b i) - f (a i))).mpr
      (fun i => sub_nonneg.mpr (hf (hab i)))
    have heq :
        diagonal (RCLike.ofReal ∘ f ∘ b) -
            diagonal (RCLike.ofReal ∘ f ∘ a) =
          (diagonal (RCLike.ofReal ∘
            (fun i => f (b i) - f (a i))) : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Function.comp_apply]
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [heq]
    exact hpsd
  exact MatrixConcentration.conjugation_rule hdiag U

set_option maxHeartbeats 800000 in
-- The finite joint-eigenspace construction and basis conversion require an enlarged budget.
/-- Matrix monotonicity: inverse is antitone and logarithm monotone on positive definite
matrices; scalar monotonicity does not suffice generally.

**Book Remark 5.4.6.** -/
theorem exercise_5_17a_commutingMatrixFunction_monotone
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hcomm : Commute A B) (hAB : A ≤ B) {f : ℝ → ℝ} (hf : Monotone f) :
    cfc f A ≤ cfc f B := by
  classical
  let s : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := EuclideanSpace.basisFun n ℂ
  let TA : (EuclideanSpace ℂ n) →ₗ[ℂ] (EuclideanSpace ℂ n) :=
    (Matrix.toLin s.toBasis s.toBasis) A
  let TB : (EuclideanSpace ℂ n) →ₗ[ℂ] (EuclideanSpace ℂ n) :=
    (Matrix.toLin s.toBasis s.toBasis) B
  have hsA : TA.IsSymmetric := (Matrix.isSymmetric_toLin_iff s).2 hA
  have hsB : TB.IsSymmetric := (Matrix.isSymmetric_toLin_iff s).2 hB
  have hc : Commute TA TB := by
    rw [Commute]
    apply (LinearMap.toMatrix s.toBasis s.toBasis).injective
    simp only [LinearMap.toMatrix_mul]
    simpa only [TA, TB, LinearMap.toMatrix_toLin] using hcomm.eq
  let V : (Module.End.Eigenvalues TB × Module.End.Eigenvalues TA) →
      Submodule ℂ (EuclideanSpace ℂ n) := fun i =>
    Module.End.eigenspace TA (i.2 : ℂ) ⊓ Module.End.eigenspace TB (i.1 : ℂ)
  let emb : (Module.End.Eigenvalues TB × Module.End.Eigenvalues TA) → ℂ × ℂ :=
    fun i => ((i.1 : ℂ), (i.2 : ℂ))
  have hemb : Function.Injective emb := by
    intro i j hij
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hij
    · apply Subtype.ext
      exact congrArg Prod.snd hij
  have hOrth : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    simpa [V, emb] using
      (hsA.orthogonalFamily_eigenspace_inf_eigenspace hsB).comp hemb
  have htop : (⨆ i, V i) = (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) := by
    apply le_antisymm le_top
    rw [← hsA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hsB hc]
    refine iSup_le fun α => iSup_le fun γ => ?_
    by_cases hα : Module.End.eigenspace TA α = ⊥
    · simp [hα]
    by_cases hγ : Module.End.eigenspace TB γ = ⊥
    · simp [hγ]
    exact le_iSup (fun i => V i)
      (⟨γ, (Module.End.hasEigenvalue_iff).2 hγ⟩,
        ⟨α, (Module.End.hasEigenvalue_iff).2 hα⟩)
  have hInt : DirectSum.IsInternal V := by
    apply hOrth.isInternal_iff.mpr
    rw [Submodule.orthogonal_eq_bot_iff, htop]
  have hn : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := by simp
  let b0 : OrthonormalBasis (Fin (Fintype.card n)) ℂ (EuclideanSpace ℂ n) :=
    hInt.subordinateOrthonormalBasis hn hOrth
  let b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
    b0.reindex (Fintype.equivFin n).symm
  let joint : n → Module.End.Eigenvalues TB × Module.End.Eigenvalues TA := fun i =>
    hInt.subordinateOrthonormalBasisIndex hn (Fintype.equivFin n i) hOrth
  have hbmem (i : n) : b i ∈ V (joint i) := by
    simpa [b, b0, joint, OrthonormalBasis.reindex_apply] using
      hInt.subordinateOrthonormalBasis_subordinate hn (Fintype.equivFin n i) hOrth
  let a : n → ℝ := fun i => RCLike.re ((joint i).2 : ℂ)
  let d : n → ℝ := fun i => RCLike.re ((joint i).1 : ℂ)
  have hrealA (i : n) : RCLike.ofReal (a i) = ((joint i).2 : ℂ) := by
    dsimp [a]
    exact RCLike.conj_eq_iff_re.mp
      (hsA.conj_eigenvalue_eq_self ((joint i).2.property))
  have hrealB (i : n) : RCLike.ofReal (d i) = ((joint i).1 : ℂ) := by
    dsimp [d]
    exact RCLike.conj_eq_iff_re.mp
      (hsB.conj_eigenvalue_eq_self ((joint i).1.property))
  have hTA (i : n) : TA (b i) = (RCLike.ofReal (a i) : ℂ) • b i := by
    calc
      TA (b i) = ((joint i).2 : ℂ) • b i :=
        Module.End.mem_eigenspace_iff.mp (hbmem i).1
      _ = (RCLike.ofReal (a i) : ℂ) • b i :=
        congrArg (fun z : ℂ => z • b i) (hrealA i).symm
  have hTB (i : n) : TB (b i) = (RCLike.ofReal (d i) : ℂ) • b i := by
    calc
      TB (b i) = ((joint i).1 : ℂ) • b i :=
        Module.End.mem_eigenspace_iff.mp (hbmem i).2
      _ = (RCLike.ofReal (d i) : ℂ) • b i :=
        congrArg (fun z : ℂ => z • b i) (hrealB i).symm
  have hTAdiag : LinearMap.toMatrix b.toBasis b.toBasis TA =
      diagonal (RCLike.ofReal ∘ a) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.toBasis.repr (TA (b j)) i =
      (diagonal (RCLike.ofReal ∘ a) : Matrix n n ℂ) i j
    rw [hTA, b.coe_toBasis_repr_apply, b.repr_apply_apply]
    by_cases hij : i = j
    · subst hij
      rw [inner_smul_right]
      simp [Function.comp_apply]
    · rw [inner_smul_right, b.inner_eq_zero hij]
      simp [Matrix.diagonal_apply_ne _ hij]
  have hTBdiag : LinearMap.toMatrix b.toBasis b.toBasis TB =
      diagonal (RCLike.ofReal ∘ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.toBasis.repr (TB (b j)) i =
      (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ) i j
    rw [hTB, b.coe_toBasis_repr_apply, b.repr_apply_apply]
    by_cases hij : i = j
    · subst hij
      rw [inner_smul_right]
      simp [Function.comp_apply]
    · rw [inner_smul_right, b.inner_eq_zero hij]
      simp [Matrix.diagonal_apply_ne _ hij]
  let U : Matrix n n ℂ := s.toBasis.toMatrix b
  have hU : U ∈ Matrix.unitaryGroup n ℂ := by
    exact s.toMatrix_orthonormalBasis_mem_unitary b
  have hUstarU : Uᴴ * U = 1 := by
    dsimp only [U]
    exact s.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hUUstar : U * Uᴴ = 1 := by
    dsimp only [U]
    exact s.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hUflip : U * b.toBasis.toMatrix s = 1 := by
    exact Module.Basis.toMatrix_mul_toMatrix_flip s.toBasis b.toBasis
  have hflip : b.toBasis.toMatrix s = Uᴴ := by
    calc
      b.toBasis.toMatrix s = 1 * b.toBasis.toMatrix s := (Matrix.one_mul _).symm
      _ = (Uᴴ * U) * b.toBasis.toMatrix s := by rw [hUstarU]
      _ = Uᴴ * (U * b.toBasis.toMatrix s) := by rw [Matrix.mul_assoc]
      _ = Uᴴ := by rw [hUflip, Matrix.mul_one]
  have hAdiag : A = U * diagonal (RCLike.ofReal ∘ a) * Uᴴ := by
    calc
      A = LinearMap.toMatrix s.toBasis s.toBasis TA := by simp [TA]
      _ = U * LinearMap.toMatrix b.toBasis b.toBasis TA * b.toBasis.toMatrix s :=
        (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
          s.toBasis b.toBasis s.toBasis b.toBasis TA).symm
      _ = U * diagonal (RCLike.ofReal ∘ a) * Uᴴ := by rw [hTAdiag, hflip]
  have hBdiag : B = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ := by
    calc
      B = LinearMap.toMatrix s.toBasis s.toBasis TB := by simp [TB]
      _ = U * LinearMap.toMatrix b.toBasis b.toBasis TB * b.toBasis.toMatrix s :=
        (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
          s.toBasis b.toBasis s.toBasis b.toBasis TB).symm
      _ = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ := by rw [hTBdiag, hflip]
  have hdiagOrder :
      (diagonal (RCLike.ofReal ∘ a) : Matrix n n ℂ) ≤
        diagonal (RCLike.ofReal ∘ d) := by
    have h := MatrixConcentration.conjugation_rule hAB Uᴴ
    have hconjA : Uᴴ * A * U = diagonal (RCLike.ofReal ∘ a) := by
      rw [hAdiag]
      calc
        Uᴴ * (U * diagonal (RCLike.ofReal ∘ a) * Uᴴ) * U =
            (Uᴴ * U) * diagonal (RCLike.ofReal ∘ a) * (Uᴴ * U) := by
          noncomm_ring
        _ = diagonal (RCLike.ofReal ∘ a) := by rw [hUstarU]; simp
    have hconjB : Uᴴ * B * U = diagonal (RCLike.ofReal ∘ d) := by
      rw [hBdiag]
      calc
        Uᴴ * (U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) * U =
            (Uᴴ * U) * diagonal (RCLike.ofReal ∘ d) * (Uᴴ * U) := by
          noncomm_ring
        _ = diagonal (RCLike.ofReal ∘ d) := by rw [hUstarU]; simp
    simpa only [Matrix.conjTranspose_conjTranspose, hconjA, hconjB] using h
  have had : ∀ i, a i ≤ d i := by
    rw [Matrix.le_iff] at hdiagOrder
    have heq :
        diagonal (RCLike.ofReal ∘ d) - diagonal (RCLike.ofReal ∘ a) =
          (diagonal (RCLike.ofReal ∘ fun i => d i - a i) : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Function.comp_apply]
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [heq, MatrixConcentration.posSemidef_diagonal_real_iff] at hdiagOrder
    exact fun i => sub_nonneg.mp (hdiagOrder i)
  exact commutingMatrixFunction_monotone hA hB hU hAdiag hBdiag had hf

/-- Inverse antitonicity and logarithm monotonicity.

**Book Exercise 5.18.** -/
theorem scalarLog_integral {x : ℝ} (hx : 0 < x) :
    Real.log x = ∫ t in Set.Ioi (0 : ℝ),
      ((1 + t)⁻¹ - (x + t)⁻¹) :=
  MatrixConcentration.log_eq_integral_inv hx

/-- Matrix monotonicity: inverse is antitone and logarithm monotone on positive definite
matrices; scalar monotonicity does not suffice generally.

**Book Remark 5.4.6.** -/
theorem inverse_loewner_antitone {A B : Matrix n n ℝ}
    (hA : (HDP.complexifyMatrix A).PosDef)
    (hB : (HDP.complexifyMatrix B).PosDef)
    (hAB : RealLoewnerLE A B) :
    (HDP.complexifyMatrix B)⁻¹ ≤ (HDP.complexifyMatrix A)⁻¹ := by
  simpa using MatrixConcentration.inv_shift_loewner_anti
    (A := HDP.complexifyMatrix A) (H := HDP.complexifyMatrix B)
    (u := 0) (le_refl 0) hA hB hAB

/-- Matrix monotonicity: inverse is antitone and logarithm monotone on positive definite
matrices; scalar monotonicity does not suffice generally.

**Book Remark 5.4.6.** -/
theorem logarithm_loewner_monotone {A B : Matrix n n ℝ}
    (hA : (HDP.complexifyMatrix A).PosDef)
    (hB : (HDP.complexifyMatrix B).PosDef)
    (hAB : RealLoewnerLE A B) :
    CFC.log (HDP.complexifyMatrix A) ≤ CFC.log (HDP.complexifyMatrix B) :=
  MatrixConcentration.log_monotone hA hB hAB

end HDP.Chapter5

end Source_10_MatrixCalculus

/-! ## Material formerly in `11_TraceInequalities.lean` -/

section Source_11_TraceInequalities

/-!
# Trace inequalities

Real symmetric source matrices are complexified only at the verified
functional-calculus boundary.  The three principal results below are direct
specializations of the independently verified Golden--Thompson and Lieb
developments.
-/

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace HDP.Chapter5

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Commuting matrix exponentials multiply.

**Book Exercise 5.19.** -/
theorem matrixExponential_add_of_commute {A B : Matrix n n ℝ}
    (hcomm : Commute (HDP.complexifyMatrix A) (HDP.complexifyMatrix B)) :
    NormedSpace.exp (HDP.complexifyMatrix (A + B)) =
      NormedSpace.exp (HDP.complexifyMatrix A) *
        NormedSpace.exp (HDP.complexifyMatrix B) := by
  rw [HDP.complexifyMatrix_add]
  exact MatrixConcentration.matrix_exp_add_of_commute hcomm

/-- The diagonal symmetric matrix in the explicit noncommuting-exponential
counterexample. -/
def matrixExponentialCounterexampleX : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- The symmetric coordinate-swap matrix in the explicit
noncommuting-exponential counterexample. -/
def matrixExponentialCounterexampleY : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

private noncomputable def matrixExponentialHadamardUnit :
    (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := !![1, 1; 1, -1]
  inv := (1 / 2 : ℂ) • !![1, 1; 1, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrixExponentialCounterexampleX_formula :
    NormedSpace.exp
        (HDP.complexifyMatrix matrixExponentialCounterexampleX) =
      !![Complex.exp 1, 0; 0, 1] := by
  have hdiag :
      HDP.complexifyMatrix matrixExponentialCounterexampleX =
        diagonal ![(1 : ℂ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixExponentialCounterexampleX,
        HDP.complexifyMatrix]
  rw [hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Complex.exp_eq_exp_ℂ]

private theorem matrixExponentialCounterexampleY_formula :
    NormedSpace.exp
        (HDP.complexifyMatrix matrixExponentialCounterexampleY) =
      !![(Complex.exp 1 + Complex.exp (-1)) / 2,
          (Complex.exp 1 - Complex.exp (-1)) / 2;
          (Complex.exp 1 - Complex.exp (-1)) / 2,
          (Complex.exp 1 + Complex.exp (-1)) / 2] := by
  let D : Matrix (Fin 2) (Fin 2) ℂ :=
    diagonal ![(1 : ℂ), -1]
  have hdiag :
      HDP.complexifyMatrix matrixExponentialCounterexampleY =
        (matrixExponentialHadamardUnit :
            Matrix (Fin 2) (Fin 2) ℂ) * D *
          (↑(matrixExponentialHadamardUnit⁻¹) :
            Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixExponentialCounterexampleY,
        HDP.complexifyMatrix, matrixExponentialHadamardUnit, D,
        Matrix.mul_apply, dotProduct, Matrix.vecMul, Fin.sum_univ_two]
  rw [hdiag]
  have hexp :=
    Matrix.exp_units_conj matrixExponentialHadamardUnit D
  change NormedSpace.exp
      ((matrixExponentialHadamardUnit :
          Matrix (Fin 2) (Fin 2) ℂ) * D *
        (↑(matrixExponentialHadamardUnit⁻¹) :
          Matrix (Fin 2) (Fin 2) ℂ)) =
      (matrixExponentialHadamardUnit :
          Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp D *
        (↑(matrixExponentialHadamardUnit⁻¹) :
          Matrix (Fin 2) (Fin 2) ℂ) at hexp
  rw [hexp, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixExponentialHadamardUnit, D, Matrix.mul_apply,
      dotProduct, Matrix.vecMul, Fin.sum_univ_two,
      Complex.exp_eq_exp_ℂ] <;> ring

/-- The scalar identity `exp(x+y)=exp(x)exp(y)` fails for symmetric
noncommuting matrices. For the two explicit matrices above, the exponential
of their sum is Hermitian, whereas the product of their exponentials has
unequal off-diagonal entries.

**Book Section 5.4.2; Exercise 5.19.** -/
theorem matrixExponential_add_ne_mul_counterexample :
    NormedSpace.exp (HDP.complexifyMatrix
        (matrixExponentialCounterexampleX +
          matrixExponentialCounterexampleY)) ≠
      NormedSpace.exp
          (HDP.complexifyMatrix matrixExponentialCounterexampleX) *
        NormedSpace.exp
          (HDP.complexifyMatrix matrixExponentialCounterexampleY) := by
  intro h
  have hXY :
      (HDP.complexifyMatrix
        (matrixExponentialCounterexampleX +
          matrixExponentialCounterexampleY)).IsHermitian := by
    apply HDP.complexifyMatrix_isHermitian
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixExponentialCounterexampleX,
        matrixExponentialCounterexampleY]
  have hprod :
      (NormedSpace.exp
          (HDP.complexifyMatrix matrixExponentialCounterexampleX) *
        NormedSpace.exp
          (HDP.complexifyMatrix
            matrixExponentialCounterexampleY)).IsHermitian := by
    rw [← h]
    exact hXY.exp
  rw [matrixExponentialCounterexampleX_formula,
    matrixExponentialCounterexampleY_formula] at hprod
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hprod
  simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
    Fin.sum_univ_two] at hentry
  have hreal := congrArg Complex.re hentry
  simp [Complex.exp_re, Complex.exp_im] at hreal
  have hsinh :
      0 < (Real.exp 1 - Real.exp (-1)) / 2 := by
    have hexp := Real.exp_lt_exp.mpr
      (by norm_num : (-1 : ℝ) < 1)
    linarith
  have hexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1))
  nlinarith

/-- Golden--Thompson trace-exponential inequality.

**Book Theorem 5.4.7.** -/
theorem goldenThompsonReal {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((NormedSpace.exp (HDP.complexifyMatrix (A + B))).trace).re ≤
      ((NormedSpace.exp (HDP.complexifyMatrix A) *
        NormedSpace.exp (HDP.complexifyMatrix B)).trace).re := by
  rw [HDP.complexifyMatrix_add]
  exact MatrixConcentration.golden_thompson
    (HDP.complexifyMatrix_isHermitian hA)
    (HDP.complexifyMatrix_isHermitian hB)

/-- For fixed real symmetric `H`, the standard Lieb trace function is concave on the full
positive-definite Hermitian cone.

**Book Theorem 5.4.8.** -/
theorem liebConcavityReal (H : Matrix n n ℝ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A => ((NormedSpace.exp
        (HDP.complexifyMatrix H + CFC.log A)).trace).re) :=
  MatrixConcentration.lieb_trace_exp_log_concave
    (HDP.complexifyMatrix H) (HDP.complexifyMatrix_isHermitian hH)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Measurability and a uniform operator-norm bound make all exponential expectations legal;
positivity of the matrix exponential is supplied by the functional calculus.

**Book Lemma 5.4.9.** -/
theorem randomLiebReal {H : Matrix n n ℝ} (hH : H.IsHermitian)
    {X : Ω → Matrix n n ℝ} (hX : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) {R : ℝ}
    (hR : ∀ ω, ‖X ω‖ ≤ R) :
    ∫ ω, ((NormedSpace.exp
        (HDP.complexifyMatrix H + HDP.complexifyMatrix (X ω))).trace).re ∂μ ≤
      ((NormedSpace.exp (HDP.complexifyMatrix H + CFC.log
        (MatrixConcentration.expectation μ fun ω =>
          NormedSpace.exp (HDP.complexifyMatrix (X ω))))).trace).re := by
  refine MatrixConcentration.expectation_trace_exp_add_le (R := R)
    (HDP.complexifyMatrix_isHermitian hH)
    (HDP.measurable_complexifyMatrix_comp hX)
    (fun ω => HDP.complexifyMatrix_isHermitian (hHerm ω)) ?_
  intro ω
  rw [HDP.complexifyMatrix_opNorm]
  exact hR ω

end HDP.Chapter5

end Source_11_TraceInequalities

/-! ## Material formerly in `12_MatrixBernstein.lean` -/

section Source_12_MatrixBernstein

/-!
# Matrix Bernstein inequality

This file gives the real-matrix formulation used in Chapter 5.  The proof is
obtained from the verified Hermitian-dilation theorem in the shared matrix
Laplace layer.  In particular, the entrywise real expectation and both
rectangular variance matrices are visible in the public interface.
-/

open Matrix WithLp Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace HDP.Chapter5

-- These finite-index instances intentionally mirror the frozen matrix-Laplace
-- API used below. Removing them declaration-by-declaration would change the
-- public compatibility signature without changing mathematical content.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {Ω ι m n : Type*} [MeasurableSpace Ω] [Fintype ι]
  [Fintype m] [Fintype n] [DecidableEq ι] [DecidableEq m] [DecidableEq n]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The row-side variance matrix of a finite family of real rectangular random matrices.

**Lean implementation helper.** -/
noncomputable def matrixVarianceLeft (X : ι → Ω → Matrix m n ℝ) : Matrix m m ℝ :=
  ∑ k, HDP.realMatrixExpectation μ (fun ω => X k ω * (X k ω)ᵀ)

/-- The column-side variance matrix of a finite family of real rectangular random matrices.

**Lean implementation helper.** -/
noncomputable def matrixVarianceRight (X : ι → Ω → Matrix m n ℝ) : Matrix n n ℝ :=
  ∑ k, HDP.realMatrixExpectation μ (fun ω => (X k ω)ᵀ * X k ω)

/-- The variance statistic in rectangular Matrix Bernstein.

**Lean implementation helper.** -/
noncomputable def matrixVariance (X : ι → Ω → Matrix m n ℝ) : ℝ :=
  max ‖matrixVarianceLeft (μ := μ) X‖ ‖matrixVarianceRight (μ := μ) X‖

/-- Variance statistic for a family of real symmetric random matrices.

**Lean implementation helper.** -/
noncomputable def symmetricMatrixVariance
    (X : ι → Ω → Matrix n n ℝ) : ℝ :=
  ‖∑ k, HDP.realMatrixExpectation μ (fun ω => X k ω * X k ω)‖

/-- For symmetric summands, both rectangular variance matrices are the same sum of expected
squares.

**Lean implementation helper.** -/
lemma matrixVariance_eq_symmetricMatrixVariance
    (X : ι → Ω → Matrix n n ℝ)
    (hHerm : ∀ k ω, (X k ω).IsHermitian) :
    matrixVariance (μ := μ) X = symmetricMatrixVariance (μ := μ) X := by
  have htrans : ∀ k ω, (X k ω)ᵀ = X k ω := fun k ω => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (hHerm k ω).eq
  have hl : matrixVarianceLeft (μ := μ) X =
      ∑ k, HDP.realMatrixExpectation μ (fun ω => X k ω * X k ω) := by
    unfold matrixVarianceLeft
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext ω
    rw [htrans k ω]
  have hr : matrixVarianceRight (μ := μ) X =
      ∑ k, HDP.realMatrixExpectation μ (fun ω => X k ω * X k ω) := by
    unfold matrixVarianceRight
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext ω
    rw [htrans k ω]
  unfold matrixVariance symmetricMatrixVariance
  rw [hl, hr, max_self]

/-- Scalar conversion behind the source's Bernstein `min` form. The theorem is deliberately
total at `v = 0` and `L = 0` (Lean's real division convention makes the corresponding minimum
zero), so downstream statements need no artificial positivity hypotheses.

**Lean implementation helper.** -/
lemma bernsteinRateMin {t v L : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v) (hL : 0 ≤ L) :
    (3 / 8 : ℝ) * min (t ^ 2 / v) (t / L) ≤
      t ^ 2 / 2 / (v + L * t / 3) := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num
  rcases hv.eq_or_lt with rfl | hv
  · rcases hL.eq_or_lt with rfl | hL
    · norm_num
    · rw [div_zero, min_eq_left]
      · rw [mul_zero]
        exact div_nonneg
          (div_nonneg (sq_nonneg t) (show (0 : ℝ) ≤ 2 by norm_num))
          (show 0 ≤ 0 + L * t / 3 by positivity)
      · exact div_nonneg ht.le hL.le
  · rcases hL.eq_or_lt with rfl | hL
    · rw [div_zero, min_eq_right]
      · rw [mul_zero]
        exact div_nonneg
          (div_nonneg (sq_nonneg t) (show (0 : ℝ) ≤ 2 by norm_num))
          (show 0 ≤ v + 0 * t / 3 by positivity)
      · exact div_nonneg (sq_nonneg t) hv.le
    · have hden : 0 < v + L * t / 3 := by positivity
      have hm1 : min (t ^ 2 / v) (t / L) * v ≤ t ^ 2 := by
        calc
          min (t ^ 2 / v) (t / L) * v ≤ (t ^ 2 / v) * v :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hv.le
          _ = t ^ 2 := by field_simp
      have hm2 : min (t ^ 2 / v) (t / L) * L ≤ t := by
        calc
          min (t ^ 2 / v) (t / L) * L ≤ (t / L) * L :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le
          _ = t := by field_simp
      have hm0 : 0 ≤ min (t ^ 2 / v) (t / L) := by positivity
      rw [le_div_iff₀ hden]
      have hm2t : (min (t ^ 2 / v) (t / L) * L) * t ≤ t * t :=
        mul_le_mul_of_nonneg_right hm2 ht.le
      nlinarith [hm1, hm2t]

/-- Increasing the nonnegative Bernstein variance denominator weakens the exponential bound. The
additional comparison `w ≤ 2v` makes the statement total at `v = 0`: then necessarily `w = 0`,
so both denominators agree.

**Lean implementation helper.** -/
lemma bernsteinExponentMono {t v w a : ℝ}
    (hv : 0 ≤ v) (hw : 0 ≤ w) (ha : 0 ≤ a)
    (hvw : v ≤ w) (hwv : w ≤ 2 * v) :
    Real.exp (-(t ^ 2) / 2 / (v + a)) ≤
      Real.exp (-(t ^ 2) / 2 / (w + a)) := by
  rcases hv.eq_or_lt with hv | hv
  · have hwz : w = 0 := by nlinarith
    rw [← hv, hwz]
  · have hdv : 0 < v + a := by positivity
    have hdenle : v + a ≤ w + a := by linarith
    have hrate : t ^ 2 / 2 / (w + a) ≤ t ^ 2 / 2 / (v + a) :=
      div_le_div_of_nonneg_left (by positivity) hdv hdenle
    apply Real.exp_le_exp.mpr
    have heqv : -(t ^ 2) / 2 / (v + a) =
        -(t ^ 2 / 2 / (v + a)) := by ring
    have heqw : -(t ^ 2) / 2 / (w + a) =
        -(t ^ 2 / 2 / (w + a)) := by ring
    rw [heqv, heqw]
    exact neg_le_neg hrate

/-- Complexification sends `A Aᵀ` to `Aℂ Aℂᴴ`.

**Lean implementation helper.** -/
private lemma complexify_mul_transpose (A : Matrix m n ℝ) :
    HDP.complexifyMatrix A * (HDP.complexifyMatrix A)ᴴ =
      HDP.complexifyMatrix (A * Aᵀ) := by
  rw [← HDP.complexifyMatrix_transpose, ← HDP.complexifyMatrix_mul]

/-- Complexification sends `Aᵀ A` to `Aℂᴴ Aℂ`.

**Lean implementation helper.** -/
private lemma complexify_transpose_mul (A : Matrix m n ℝ) :
    (HDP.complexifyMatrix A)ᴴ * HDP.complexifyMatrix A =
      HDP.complexifyMatrix (Aᵀ * A) := by
  rw [← HDP.complexifyMatrix_transpose, ← HDP.complexifyMatrix_mul]

/-- Expectation of the complexified left Gram matrix is the complexification of the real expected left Gram matrix.

**Lean implementation helper.** -/
private lemma expectation_complexify_left (X : Ω → Matrix m n ℝ) :
    MatrixConcentration.expectation μ (fun ω =>
        HDP.complexifyMatrix (X ω) * (HDP.complexifyMatrix (X ω))ᴴ) =
      HDP.complexifyMatrix
        (HDP.realMatrixExpectation μ (fun ω => X ω * (X ω)ᵀ)) := by
  rw [show (fun ω => HDP.complexifyMatrix (X ω) *
      (HDP.complexifyMatrix (X ω))ᴴ) =
      fun ω => HDP.complexifyMatrix (X ω * (X ω)ᵀ) from
        funext fun ω => complexify_mul_transpose (X ω)]
  exact HDP.expectation_complexifyMatrix _

/-- Expectation of the complexified right Gram matrix is the complexification of the real expected right Gram matrix.

**Lean implementation helper.** -/
private lemma expectation_complexify_right (X : Ω → Matrix m n ℝ) :
    MatrixConcentration.expectation μ (fun ω =>
        (HDP.complexifyMatrix (X ω))ᴴ * HDP.complexifyMatrix (X ω)) =
      HDP.complexifyMatrix
        (HDP.realMatrixExpectation μ (fun ω => (X ω)ᵀ * X ω)) := by
  rw [show (fun ω => (HDP.complexifyMatrix (X ω))ᴴ *
      HDP.complexifyMatrix (X ω)) =
      fun ω => HDP.complexifyMatrix ((X ω)ᵀ * X ω) from
        funext fun ω => complexify_transpose_mul (X ω)]
  exact HDP.expectation_complexifyMatrix _

/-- The sum of expected complexified left Gram matrices is the complexification of the real left variance matrix.

**Lean implementation helper.** -/
private lemma complex_variance_left (X : ι → Ω → Matrix m n ℝ) :
    (∑ k, MatrixConcentration.expectation μ (fun ω =>
        HDP.complexifyMatrix (X k ω) * (HDP.complexifyMatrix (X k ω))ᴴ)) =
      HDP.complexifyMatrix (matrixVarianceLeft (μ := μ) X) := by
  unfold matrixVarianceLeft
  rw [HDP.complexifyMatrix_sum]
  exact Finset.sum_congr rfl fun k _ => expectation_complexify_left (X k)

/-- The sum of expected complexified right Gram matrices is the complexification of the real right variance matrix.

**Lean implementation helper.** -/
private lemma complex_variance_right (X : ι → Ω → Matrix m n ℝ) :
    (∑ k, MatrixConcentration.expectation μ (fun ω =>
        (HDP.complexifyMatrix (X k ω))ᴴ * HDP.complexifyMatrix (X k ω))) =
      HDP.complexifyMatrix (matrixVarianceRight (μ := μ) X) := by
  unfold matrixVarianceRight
  rw [HDP.complexifyMatrix_sum]
  exact Finset.sum_congr rfl fun k _ => expectation_complexify_right (X k)

section HermitianMgf

variable {p : Type*} [Fintype p] [DecidableEq p] [Nonempty p]

/-- Expectation of the square of a complexified real matrix is the complexification of the expected real square.

**Lean implementation helper.** -/
private lemma expectation_complexify_square (X : Ω → Matrix p p ℝ) :
    MatrixConcentration.expectation μ (fun ω =>
        HDP.complexifyMatrix (X ω) * HDP.complexifyMatrix (X ω)) =
      HDP.complexifyMatrix
        (HDP.realMatrixExpectation μ (fun ω => X ω * X ω)) := by
  rw [show (fun ω => HDP.complexifyMatrix (X ω) *
      HDP.complexifyMatrix (X ω)) =
      fun ω => HDP.complexifyMatrix (X ω * X ω) from
        funext fun ω => (HDP.complexifyMatrix_mul (X ω) (X ω)).symm]
  exact HDP.expectation_complexifyMatrix _

/-- Matrix-MGF form, for a real symmetric, centered random matrix bounded in operator norm. The
legal range is written without division: `0 < θ` and `θ K < 3`, so the `K=0` branch remains
meaningful.

**Book Lemma 5.4.10.** -/
theorem matrixBernsteinMgf
    (X : Ω → Matrix p p ℝ) (hmeas : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) (hbd : ∀ ω, ‖X ω‖ ≤ K)
    (hcent : HDP.realMatrixExpectation μ X = 0)
    {θ : ℝ} (hθ : 0 < θ) (hθK : θ * K < 3) :
    MatrixConcentration.matrixMgf μ
        (fun ω => HDP.complexifyMatrix (X ω)) θ ≤
      NormedSpace.exp (MatrixConcentration.gBernstein θ K •
        HDP.complexifyMatrix
          (HDP.realMatrixExpectation μ (fun ω => X ω * X ω))) := by
  have hcmeas := HDP.measurable_complexifyMatrix_comp hmeas
  have hcHerm : ∀ ω, (HDP.complexifyMatrix (X ω)).IsHermitian :=
    fun ω => HDP.complexifyMatrix_isHermitian (hHerm ω)
  have hcbd : ∀ ω, ‖HDP.complexifyMatrix (X ω)‖ ≤ K := fun ω => by
    rw [HDP.complexifyMatrix_opNorm]
    exact hbd ω
  have hccent : MatrixConcentration.expectation μ
      (fun ω => HDP.complexifyMatrix (X ω)) = 0 := by
    rw [HDP.expectation_complexifyMatrix, hcent, HDP.complexifyMatrix_zero]
  have hcmax : ∀ ω, MatrixConcentration.lambdaMax (hcHerm ω) ≤ K := fun ω =>
    (le_abs_self _).trans
      ((MatrixConcentration.abs_lambdaMax_le (hcHerm ω)).trans (hcbd ω))
  have h := MatrixConcentration.bernstein_matrix_mgf_le
    (μ := μ) hcmeas hcHerm hcbd hccent hcmax hθ hθK
  rwa [expectation_complexify_square (μ := μ) X] at h

/-- Matrix MGF is bounded by the variance term in the Bernstein range.

**Book Lemma 5.4.10.** -/
theorem matrixBernsteinCgf
    (X : Ω → Matrix p p ℝ) (hmeas : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) (hbd : ∀ ω, ‖X ω‖ ≤ K)
    (hcent : HDP.realMatrixExpectation μ X = 0)
    {θ : ℝ} (hθ : 0 < θ) (hθK : θ * K < 3) :
    MatrixConcentration.matrixCgf μ
        (fun ω => HDP.complexifyMatrix (X ω)) θ ≤
      MatrixConcentration.gBernstein θ K •
        HDP.complexifyMatrix
          (HDP.realMatrixExpectation μ (fun ω => X ω * X ω)) := by
  have hcmeas := HDP.measurable_complexifyMatrix_comp hmeas
  have hcHerm : ∀ ω, (HDP.complexifyMatrix (X ω)).IsHermitian :=
    fun ω => HDP.complexifyMatrix_isHermitian (hHerm ω)
  have hcbd : ∀ ω, ‖HDP.complexifyMatrix (X ω)‖ ≤ K := fun ω => by
    rw [HDP.complexifyMatrix_opNorm]
    exact hbd ω
  have hccent : MatrixConcentration.expectation μ
      (fun ω => HDP.complexifyMatrix (X ω)) = 0 := by
    rw [HDP.expectation_complexifyMatrix, hcent, HDP.complexifyMatrix_zero]
  have hcmax : ∀ ω, MatrixConcentration.lambdaMax (hcHerm ω) ≤ K := fun ω =>
    (le_abs_self _).trans
      ((MatrixConcentration.abs_lambdaMax_le (hcHerm ω)).trans (hcbd ω))
  have h := MatrixConcentration.bernstein_matrix_cgf_le
    (μ := μ) hcmeas hcHerm hcbd hccent hcmax hθ hθK
  rwa [expectation_complexify_square (μ := μ) X] at h

end HermitianMgf

/-- For independent, centered real random matrices bounded by `L`, the expected operator norm of
their sum is controlled by the rectangular variance statistic. The formula also covers `L = 0`
and zero variance.

**Book Remark 5.4.11.** -/
theorem matrixBernsteinExpectation [Nonempty (m ⊕ n)]
    (X : ι → Ω → Matrix m n ℝ)
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k ω, ‖X k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, HDP.realMatrixExpectation μ (X k) = 0)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, ‖∑ k, X k ω‖ ∂μ ≤
      Real.sqrt (2 * matrixVariance (μ := μ) X *
        Real.log (Fintype.card m + Fintype.card n)) +
      L / 3 * Real.log (Fintype.card m + Fintype.card n) := by
  classical
  let S : ι → Ω → Matrix m n ℂ := fun k ω => HDP.complexifyMatrix (X k ω)
  have hSmeas : ∀ k, Measurable (S k) := fun k =>
    HDP.measurable_complexifyMatrix_comp (hmeas k)
  have hSbd : ∀ k ω, ‖S k ω‖ ≤ L := fun k ω => by
    rw [show S k ω = HDP.complexifyMatrix (X k ω) from rfl,
      HDP.complexifyMatrix_opNorm]
    exact hbd k ω
  have hScent : ∀ k, MatrixConcentration.expectation μ (S k) = 0 := fun k => by
    rw [show S k = fun ω => HDP.complexifyMatrix (X k ω) from rfl,
      HDP.expectation_complexifyMatrix, hcent k, HDP.complexifyMatrix_zero]
  have hSind : ProbabilityTheory.iIndepFun S μ :=
    hind.comp (fun _ A => HDP.complexifyMatrix A)
      (fun _ => HDP.measurable_complexifyMatrix)
  have h := MatrixConcentration.matrix_bernstein_rect_expectation
    (μ := μ) hSmeas hSbd hL hScent hSind
  have hleft : (∫ ω, ‖∑ k, S k ω‖ ∂μ) = ∫ ω, ‖∑ k, X k ω‖ ∂μ := by
    congr 1
    funext ω
    rw [show (∑ k, S k ω) = HDP.complexifyMatrix (∑ k, X k ω) from by
      change (∑ k, HDP.complexifyMatrix (X k ω)) =
        HDP.complexifyMatrix (∑ k, X k ω)
      exact (HDP.complexifyMatrix_sum Finset.univ (fun k => X k ω)).symm,
      HDP.complexifyMatrix_opNorm]
  rw [hleft, complex_variance_left (μ := μ) X,
    complex_variance_right (μ := μ) X,
    HDP.complexifyMatrix_opNorm, HDP.complexifyMatrix_opNorm] at h
  exact h

/-- Matrix Bernstein tail bound for sums of independent centered bounded random matrices.

**Book Theorem 5.4.1.** -/
theorem matrixBernsteinTail [Nonempty (m ⊕ n)]
    (X : ι → Ω → Matrix m n ℝ)
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k ω, ‖X k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, HDP.realMatrixExpectation μ (X k) = 0)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, X k ω‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(t ^ 2) / 2 / (matrixVariance (μ := μ) X + L * t / 3)) := by
  classical
  let S : ι → Ω → Matrix m n ℂ := fun k ω => HDP.complexifyMatrix (X k ω)
  have hSmeas : ∀ k, Measurable (S k) := fun k =>
    HDP.measurable_complexifyMatrix_comp (hmeas k)
  have hSbd : ∀ k ω, ‖S k ω‖ ≤ L := fun k ω => by
    rw [show S k ω = HDP.complexifyMatrix (X k ω) from rfl,
      HDP.complexifyMatrix_opNorm]
    exact hbd k ω
  have hScent : ∀ k, MatrixConcentration.expectation μ (S k) = 0 := fun k => by
    rw [show S k = fun ω => HDP.complexifyMatrix (X k ω) from rfl,
      HDP.expectation_complexifyMatrix, hcent k, HDP.complexifyMatrix_zero]
  have hSind : ProbabilityTheory.iIndepFun S μ :=
    hind.comp (fun _ A => HDP.complexifyMatrix A)
      (fun _ => HDP.measurable_complexifyMatrix)
  have h := MatrixConcentration.matrix_bernstein_rect_tail
    (μ := μ) hSmeas hSbd hL hScent hSind ht
  have hset : {ω | t ≤ ‖∑ k, S k ω‖} = {ω | t ≤ ‖∑ k, X k ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [show (∑ k, S k ω) = HDP.complexifyMatrix (∑ k, X k ω) from by
      change (∑ k, HDP.complexifyMatrix (X k ω)) =
        HDP.complexifyMatrix (∑ k, X k ω)
      exact (HDP.complexifyMatrix_sum Finset.univ (fun k => X k ω)).symm,
      HDP.complexifyMatrix_opNorm]
  rw [hset, complex_variance_left (μ := μ) X,
    complex_variance_right (μ := μ) X,
    HDP.complexifyMatrix_opNorm, HDP.complexifyMatrix_opNorm] at h
  exact h

/-- The variance is exactly the source's sum `‖∑ 𝔼 XₖᵀXₖ‖ + ‖∑ 𝔼 XₖXₖᵀ‖`, and the displayed
prefactor is `2(m+n)`. It follows from the sharper max-variance rectangular theorem above; the
proof also covers zero variance and `L = 0`.

**Book Remark 5.4.15.** -/
theorem exercise_5_23_matrixBernsteinRectangular [Nonempty (m ⊕ n)]
    (X : ι → Ω → Matrix m n ℝ)
    (hmeas : ∀ k, Measurable (X k))
    (hbd : ∀ k ω, ‖X k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, HDP.realMatrixExpectation μ (X k) = 0)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, X k ω‖} ≤
      2 * ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(t ^ 2) / 2 /
          (‖∑ k, HDP.realMatrixExpectation μ
              (fun ω => (X k ω)ᵀ * X k ω)‖ +
            ‖∑ k, HDP.realMatrixExpectation μ
              (fun ω => X k ω * (X k ω)ᵀ)‖ +
            L * t / 3)) := by
  have h := matrixBernsteinTail (μ := μ) X hmeas hbd hL hcent hind ht
  let vL : ℝ := ‖matrixVarianceLeft (μ := μ) X‖
  let vR : ℝ := ‖matrixVarianceRight (μ := μ) X‖
  let v : ℝ := matrixVariance (μ := μ) X
  let w : ℝ := vR + vL
  have hv : 0 ≤ v := by dsimp [v, matrixVariance]; positivity
  have hw : 0 ≤ w := by dsimp [w, vL, vR]; positivity
  have hvw : v ≤ w := by
    dsimp [v, w, vL, vR, matrixVariance]
    have hl0 := norm_nonneg (matrixVarianceLeft (μ := μ) X)
    have hr0 := norm_nonneg (matrixVarianceRight (μ := μ) X)
    exact max_le (by linarith) (by linarith)
  have hwv : w ≤ 2 * v := by
    have hl : vL ≤ v := by
      dsimp [vL, v, matrixVariance]
      exact le_max_left _ _
    have hr : vR ≤ v := by
      dsimp [vR, v, matrixVariance]
      exact le_max_right _ _
    dsimp [w]
    linarith
  have hexp := bernsteinExponentMono (t := t) (v := v) (w := w)
    (a := L * t / 3) hv hw
    (div_nonneg (mul_nonneg hL ht) (by norm_num)) hvw hwv
  have hD : 0 ≤ (Fintype.card m : ℝ) + Fintype.card n := by positivity
  have hstep := mul_le_mul_of_nonneg_left hexp hD
  calc
    μ.real {ω | t ≤ ‖∑ k, X k ω‖} ≤
        ((Fintype.card m : ℝ) + Fintype.card n) *
          Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) := by
      simpa [v] using h
    _ ≤ 2 * ((Fintype.card m : ℝ) + Fintype.card n) *
          Real.exp (-(t ^ 2) / 2 / (w + L * t / 3)) := by
      nlinarith [Real.exp_pos (-(t ^ 2) / 2 / (w + L * t / 3))]
    _ = _ := by
      dsimp [w, vL, vR, matrixVarianceLeft, matrixVarianceRight]

/-- With `σ² = ‖∑ 𝔼 Xₖ²‖`, the tail is bounded by `2n exp (-(3/8) min (t²/σ²) (t/L))`. No
positivity assumption is imposed on `σ²` or `L`; hence the declaration is safe for degenerate
families as well.

**Book Theorem 5.4.1.** -/
theorem matrixBernsteinSymmetricTail [Nonempty n]
    (X : ι → Ω → Matrix n n ℝ)
    (hmeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, HDP.realMatrixExpectation μ (X k) = 0)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, X k ω‖} ≤
      (2 * Fintype.card n : ℝ) * Real.exp
        (-(3 / 8 : ℝ) *
          min (t ^ 2 / symmetricMatrixVariance (μ := μ) X) (t / L)) := by
  have h := matrixBernsteinTail (μ := μ) X hmeas hbd hL hcent hind ht
  rw [matrixVariance_eq_symmetricMatrixVariance (μ := μ) X hHerm] at h
  have hdim : ((Fintype.card n : ℝ) + Fintype.card n) =
      (2 * Fintype.card n : ℝ) := by ring
  rw [hdim] at h
  have hrate := bernsteinRateMin ht
    (norm_nonneg (∑ k, HDP.realMatrixExpectation μ (fun ω => X k ω * X k ω))) hL
  have harg : -(t ^ 2) / 2 /
        (symmetricMatrixVariance (μ := μ) X + L * t / 3) ≤
      -(3 / 8 : ℝ) *
        min (t ^ 2 / symmetricMatrixVariance (μ := μ) X) (t / L) := by
    have hneg : -(t ^ 2) / 2 /
        (symmetricMatrixVariance (μ := μ) X + L * t / 3) =
        -(t ^ 2 / 2 /
          (symmetricMatrixVariance (μ := μ) X + L * t / 3)) := by ring
    rw [hneg]
    simpa [symmetricMatrixVariance] using neg_le_neg hrate
  exact h.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity))

end HDP.Chapter5

end Source_12_MatrixBernstein

/-! ## Material formerly in `13_MatrixHoeffdingKhintchine.lean` -/

section Source_13_MatrixHoeffdingKhintchine

/-!
# Matrix Hoeffding and Khintchine inequalities

The Rademacher variables are specified by their law, not by a chosen pointwise
representative.  The underlying verified theorem removes null-set support
issues before applying Hermitian dilation.
-/

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace HDP.Chapter5

-- Keep the finite-index instance profile of the frozen rectangular
-- concentration API. These linter findings are compatibility artifacts, not
-- unused mathematical hypotheses in the source-facing statements.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {Ω ι m n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The finite-dimensional prefactor in a Gaussian tail costs only a `sqrt (log D)` term in
every `L^p` norm. This is the integrated-tail step in the proof of the corresponding theorem. It
is stated for a general nonnegative random variable so the same proof serves the Hermitian and
rectangular forms.

**Lean implementation helper.** -/
theorem lpNorm_of_gaussian_prefactor_tail
    {Z : Ω → ℝ} (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {D σ : ℝ} (hD : 1 ≤ D) (hσ : 0 < σ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ Z ω} ≤ ENNReal.ofReal
        (D * Real.exp (-(t ^ 2) / (2 * σ ^ 2))))
    {p : ℝ} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV Z p μ ≤
      2 * σ * (Real.sqrt (Real.log D) + Real.sqrt 5 * Real.sqrt p) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  let a : ℝ := 2 * σ * Real.sqrt (Real.log D)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 4 * σ ^ 2 * Real.log D := by
    dsimp [a]
    calc
      (2 * σ * Real.sqrt (Real.log D)) ^ 2 =
          4 * σ ^ 2 * (Real.sqrt (Real.log D)) ^ 2 := by ring
      _ = 4 * σ ^ 2 * Real.log D := by rw [Real.sq_sqrt hlog]
  let W : Ω → ℝ := fun ω => max (Z ω - a) 0
  have hW : Measurable W := (hZ.sub_const a).max measurable_const
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => le_max_right _ _
  have htailW : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |W ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ) ^ 2)) := by
    intro t ht
    rcases ht.eq_or_lt with rfl | htpos
    · calc
        μ {ω | 0 ≤ |W ω|} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(0 : ℝ) ^ 2 / (2 * σ) ^ 2)) := by
          norm_num
    · have hsub : {ω | t ≤ |W ω|} ⊆ {ω | a + t ≤ Z ω} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        rw [abs_of_nonneg (hW0 ω)] at hω
        dsimp [W] at hω
        rcases le_total (Z ω - a) 0 with hz | hz
        · rw [max_eq_right hz] at hω
          linarith
        · rw [max_eq_left hz] at hω
          linarith
      have hat0 : 0 ≤ a + t := add_nonneg ha0 ht
      calc
        μ {ω | t ≤ |W ω|} ≤ μ {ω | a + t ≤ Z ω} := measure_mono hsub
        _ ≤ ENNReal.ofReal
            (D * Real.exp (-((a + t) ^ 2) / (2 * σ ^ 2))) := htail (a + t) hat0
        _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          have hden : 0 < 4 * σ ^ 2 := by positivity
          have heq1 : -((a + t) ^ 2) / (2 * σ ^ 2) =
              (-2 * (a + t) ^ 2) / (4 * σ ^ 2) := by
            field_simp
            ring
          have heq2 : -Real.log D - t ^ 2 / (4 * σ ^ 2) =
              (-4 * σ ^ 2 * Real.log D - t ^ 2) / (4 * σ ^ 2) := by
            field_simp
          have harg : -((a + t) ^ 2) / (2 * σ ^ 2) ≤
              -Real.log D - t ^ 2 / (4 * σ ^ 2) := by
            rw [heq1, heq2, div_le_div_iff_of_pos_right hden]
            rw [show (a + t) ^ 2 = a ^ 2 + 2 * a * t + t ^ 2 by ring, ha2]
            nlinarith [mul_nonneg ha0 ht, mul_nonneg (sq_nonneg σ) hlog]
          have hexp := Real.exp_le_exp.mpr harg
          have hcancel : D * Real.exp
              (-Real.log D - t ^ 2 / (4 * σ ^ 2)) =
              Real.exp (-t ^ 2 / (4 * σ ^ 2)) := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
              Real.exp_log hDpos]
            field_simp
          calc
            D * Real.exp (-((a + t) ^ 2) / (2 * σ ^ 2))
                ≤ D * Real.exp (-Real.log D - t ^ 2 / (4 * σ ^ 2)) :=
              mul_le_mul_of_nonneg_left hexp hDpos.le
            _ = Real.exp (-t ^ 2 / (4 * σ ^ 2)) := hcancel
            _ ≤ 2 * Real.exp (-t ^ 2 / (2 * σ) ^ 2) := by
              have hsq : (2 * σ) ^ 2 = 4 * σ ^ 2 := by ring
              rw [hsq]
              nlinarith [Real.exp_pos (-t ^ 2 / (4 * σ ^ 2))]
  obtain ⟨hWsub, hpsiW⟩ := HDP.psi2Norm_le_of_tail_bound
    hW.aemeasurable (show 0 < 2 * σ by positivity) htailW
  have hWmem := hWsub.memLp hW.aemeasurable hp
  have haMem : MemLp (fun _ : Ω => a) (ENNReal.ofReal p) μ := memLp_const a
  have haddMem : MemLp ((fun _ : Ω => a) + W) (ENNReal.ofReal p) μ :=
    haMem.add hWmem
  have hZW : ∀ ω, |Z ω| ≤ |a + W ω| := by
    intro ω
    rw [abs_of_nonneg (hZ0 ω), abs_of_nonneg (add_nonneg ha0 (hW0 ω))]
    dsimp [W]
    have hmax := le_max_left (Z ω - a) 0
    linarith
  have hmono : HDP.Chapter1.lpNormRV Z p μ ≤
      HDP.Chapter1.lpNormRV ((fun _ : Ω => a) + W) p μ := by
    have hZmem : MemLp Z (ENNReal.ofReal p) μ :=
      haddMem.mono hZ.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          simpa only [Pi.add_apply, Real.norm_eq_abs] using hZW ω)
    rw [HDP.Chapter1.lpNormRV_eq_toReal_eLpNorm hp0 hZmem,
      HDP.Chapter1.lpNormRV_eq_toReal_eLpNorm hp0 haddMem]
    exact ENNReal.toReal_mono haddMem.eLpNorm_ne_top
      (eLpNorm_mono_ae (Filter.Eventually.of_forall fun ω => by
        simpa only [Pi.add_apply, Real.norm_eq_abs] using hZW ω))
  have hmink := HDP.Chapter1.minkowski_Lp hp haMem hWmem
  have hconst : HDP.Chapter1.lpNormRV (fun _ : Ω => a) p μ = a := by
    rw [HDP.Chapter1.lpNormRV]
    have hint : ∫ _ : Ω, |a| ^ p ∂μ = a ^ p := by
      simp [abs_of_nonneg ha0]
    rw [hint, ← Real.rpow_mul ha0]
    rw [show p * (1 / p) = 1 by field_simp, Real.rpow_one]
  have hWmom := hWsub.moment_bound hW.aemeasurable hp
  calc
    HDP.Chapter1.lpNormRV Z p μ
        ≤ HDP.Chapter1.lpNormRV ((fun _ : Ω => a) + W) p μ := hmono
    _ ≤ HDP.Chapter1.lpNormRV (fun _ : Ω => a) p μ +
        HDP.Chapter1.lpNormRV W p μ := by
          convert hmink using 1
          congr 1
    _ ≤ a + (Real.sqrt 5 * (2 * σ)) * Real.sqrt p := by
      rw [hconst]
      gcongr
      exact hWmom.trans (mul_le_mul_of_nonneg_right hpsiW (Real.sqrt_nonneg p))
    _ = 2 * σ * (Real.sqrt (Real.log D) + Real.sqrt 5 * Real.sqrt p) := by
      dsimp [a]
      ring

/-- Elementary consolidation of the two square-root terms into the source's `sqrt (p + log D)`
form.

**Lean implementation helper.** -/
lemma sqrtLog_add_sqrtP_le {D p : ℝ} (hD : 1 ≤ D) (hp : 1 ≤ p) :
    Real.sqrt (Real.log D) + Real.sqrt 5 * Real.sqrt p ≤
      (1 + Real.sqrt 5) * Real.sqrt (p + Real.log D) := by
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hx : Real.sqrt (Real.log D) ≤ Real.sqrt (p + Real.log D) :=
    Real.sqrt_le_sqrt (by linarith)
  have hy : Real.sqrt p ≤ Real.sqrt (p + Real.log D) :=
    Real.sqrt_le_sqrt (by linarith)
  have hy' := mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg 5)
  nlinarith

/-- Deterministic rectangular row-variance statistic for a Rademacher series.

**Lean implementation helper.** -/
noncomputable def rademacherVarianceLeft (A : ι → Matrix m n ℝ) : Matrix m m ℝ :=
  ∑ k, A k * (A k)ᵀ

/-- Deterministic rectangular column-variance statistic for a Rademacher series.

**Lean implementation helper.** -/
noncomputable def rademacherVarianceRight (A : ι → Matrix m n ℝ) : Matrix n n ℝ :=
  ∑ k, (A k)ᵀ * A k

/-- The sharp rectangular variance statistic.

**Lean implementation helper.** -/
noncomputable def rademacherVariance (A : ι → Matrix m n ℝ) : ℝ :=
  max ‖rademacherVarianceLeft A‖ ‖rademacherVarianceRight A‖

/-- Complexification commutes with finite real-weighted matrix sums.

**Lean implementation helper.** -/
private lemma complexify_signed_sum (A : ι → Matrix m n ℝ) (f : ι → ℝ) :
    (∑ k, f k • HDP.complexifyMatrix (A k)) =
      HDP.complexifyMatrix (∑ k, f k • A k) := by
  rw [HDP.complexifyMatrix_sum]
  exact Finset.sum_congr rfl fun k _ =>
    (HDP.complexifyMatrix_smul (f k) (A k)).symm

/-- The complex left variance sum of a deterministic rectangular family is the complexification of its real left variance matrix.

**Lean implementation helper.** -/
private lemma complexify_rect_left (A : ι → Matrix m n ℝ) :
    (∑ k, HDP.complexifyMatrix (A k) *
        (HDP.complexifyMatrix (A k))ᴴ) =
      HDP.complexifyMatrix (rademacherVarianceLeft A) := by
  unfold rademacherVarianceLeft
  rw [HDP.complexifyMatrix_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← HDP.complexifyMatrix_transpose, ← HDP.complexifyMatrix_mul]

/-- The complex right variance sum of a deterministic rectangular family is the complexification of its real right variance matrix.

**Lean implementation helper.** -/
private lemma complexify_rect_right (A : ι → Matrix m n ℝ) :
    (∑ k, (HDP.complexifyMatrix (A k))ᴴ *
        HDP.complexifyMatrix (A k)) =
      HDP.complexifyMatrix (rademacherVarianceRight A) := by
  unfold rademacherVarianceRight
  rw [HDP.complexifyMatrix_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← HDP.complexifyMatrix_transpose, ← HDP.complexifyMatrix_mul]

/-- Hermitian dilation extends matrix concentration to nonsymmetric rectangular matrices.

**Book Remark 5.4.15.** -/
theorem rectangularRademacherExpectation [Nonempty m] [Nonempty n]
    (A : ι → Matrix m n ℝ) {ε : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) :
    ∫ ω, ‖∑ k, ε k ω • A k‖ ∂μ ≤
      Real.sqrt (2 * rademacherVariance A *
        Real.log (Fintype.card m + Fintype.card n)) := by
  have h := MatrixConcentration.rademacher_series_rect_expectation_of_isRademacher
    (μ := μ) (B := fun k => HDP.complexifyMatrix (A k)) hmeas hlaw hind
  rw [complexify_rect_left A, complexify_rect_right A,
    HDP.complexifyMatrix_opNorm, HDP.complexifyMatrix_opNorm] at h
  have hleft : (∫ ω, ‖∑ k, ε k ω • HDP.complexifyMatrix (A k)‖ ∂μ) =
      ∫ ω, ‖∑ k, ε k ω • A k‖ ∂μ := by
    congr 1
    funext ω
    rw [complexify_signed_sum, HDP.complexifyMatrix_opNorm]
  rwa [hleft] at h

/-- Gives the rectangular matrix-series tail bound obtained from Hermitian dilation.

**Book Exercise 5.24.** -/
theorem rectangularRademacherTail [Nonempty m] [Nonempty n]
    (A : ι → Matrix m n ℝ) {ε : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, ε k ω • A k‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(t ^ 2) / (2 * rademacherVariance A)) := by
  have h := MatrixConcentration.rademacher_series_rect_tail_of_isRademacher
    (μ := μ) (B := fun k => HDP.complexifyMatrix (A k)) hmeas hlaw hind ht
  rw [complexify_rect_left A, complexify_rect_right A,
    HDP.complexifyMatrix_opNorm, HDP.complexifyMatrix_opNorm] at h
  have hset : {ω | t ≤ ‖∑ k, ε k ω • HDP.complexifyMatrix (A k)‖} =
      {ω | t ≤ ‖∑ k, ε k ω • A k‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [complexify_signed_sum, HDP.complexifyMatrix_opNorm]
  rwa [hset] at h

/-- For every real `p ≥ 1`, this is the source quantity `(𝔼 ‖∑ εₖ Aₖ‖^p)^(1/p)`. The explicit
constant comes from integrating the rectangular Gaussian tail. The zero-variance branch is
included: in that case integrability of the Rademacher series and the expectation endpoint show
that the series vanishes almost surely.

**Book Remark 5.4.15.** -/
theorem rectangularMatrixKhintchine [Nonempty m] [Nonempty n]
    (A : ι → Matrix m n ℝ) {ε : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) {p : ℝ} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ ≤
      2 * Real.sqrt (rademacherVariance A) *
        (Real.sqrt (Real.log (Fintype.card m + Fintype.card n)) +
          Real.sqrt 5 * Real.sqrt p) := by
  let Z : Ω → ℝ := fun ω => ‖∑ k, ε k ω • A k‖
  have hsum : Measurable (fun ω => ∑ k, ε k ω • A k) :=
    Finset.measurable_sum _ fun k _ => (hmeas k).smul_const (A k)
  have hZ : Measurable Z := hsum.norm
  have hD : (1 : ℝ) ≤ Fintype.card m + Fintype.card n := by
    exact_mod_cast (show 1 ≤ Fintype.card m + Fintype.card n by
      have hm := Fintype.card_pos (α := m)
      omega)
  have hv0 : 0 ≤ rademacherVariance A := by
    unfold rademacherVariance
    positivity
  rcases eq_or_lt_of_le hv0 with hv | hv
  · have hεint : ∀ k, Integrable (ε k) μ := fun k =>
      MatrixConcentration.integrable_isRademacher (hmeas k) (hlaw k) measurable_id
    have hsumInt : Integrable (fun ω => ∑ k, ε k ω • A k) μ :=
      integrable_finsetSum _ fun k _ => (hεint k).smul_const (A k)
    have hZint : Integrable Z μ := hsumInt.norm
    have hexp := rectangularRademacherExpectation (μ := μ) A hmeas hlaw hind
    have hle : ∫ ω, Z ω ∂μ ≤ 0 := by
      simpa [Z, ← hv] using hexp
    have hint : ∫ ω, Z ω ∂μ = 0 :=
      le_antisymm hle (integral_nonneg fun _ => norm_nonneg _)
    have hZae : Z =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hZint).mp hint
    have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
    have hLp : HDP.Chapter1.lpNormRV Z p μ = 0 := by
      rw [HDP.Chapter1.lpNormRV]
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by
        filter_upwards [hZae] with ω hω
        rw [Pi.zero_apply] at hω
        rw [hω, abs_zero, Real.zero_rpow hp0.ne'])]
      rw [integral_zero, Real.zero_rpow (by positivity)]
    rw [show (fun ω => ‖∑ k, ε k ω • A k‖) = Z from rfl, hLp]
    simp [← hv]
  · have hsqrt : 0 < Real.sqrt (rademacherVariance A) := Real.sqrt_pos.2 hv
    refine lpNorm_of_gaussian_prefactor_tail hZ (fun _ => norm_nonneg _) hD hsqrt ?_ hp
    intro t ht
    have hreal := rectangularRademacherTail (μ := μ) A hmeas hlaw hind ht
    have hsquare : (Real.sqrt (rademacherVariance A)) ^ 2 =
        rademacherVariance A := Real.sq_sqrt hv.le
    calc
      μ {ω | t ≤ Z ω} = ENNReal.ofReal (μ.real {ω | t ≤ Z ω}) := by
        exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal (((Fintype.card m : ℝ) + Fintype.card n) *
          Real.exp (-(t ^ 2) / (2 * rademacherVariance A))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (((Fintype.card m : ℝ) + Fintype.card n) *
          Real.exp (-(t ^ 2) / (2 * (Real.sqrt (rademacherVariance A)) ^ 2))) := by
        rw [hsquare]

/-- 24 in the source's single-square-root notation, with the explicit absolute constant
`2(1+√5)`.

**Lean implementation helper.** -/
theorem rectangularMatrixKhintchineSource [Nonempty m] [Nonempty n]
    (A : ι → Matrix m n ℝ) {ε : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) {p : ℝ} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ ≤
      2 * (1 + Real.sqrt 5) *
        Real.sqrt (p + Real.log (Fintype.card m + Fintype.card n)) *
          Real.sqrt (rademacherVariance A) := by
  have h := rectangularMatrixKhintchine (μ := μ) A hmeas hlaw hind hp
  have hD : (1 : ℝ) ≤ Fintype.card m + Fintype.card n := by
    exact_mod_cast (show 1 ≤ Fintype.card m + Fintype.card n by
      have hm := Fintype.card_pos (α := m)
      omega)
  have hs := sqrtLog_add_sqrtP_le hD hp
  calc
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ
        ≤ 2 * Real.sqrt (rademacherVariance A) *
          (Real.sqrt (Real.log (Fintype.card m + Fintype.card n)) +
            Real.sqrt 5 * Real.sqrt p) := h
    _ ≤ 2 * Real.sqrt (rademacherVariance A) *
          ((1 + Real.sqrt 5) *
            Real.sqrt (p + Real.log (Fintype.card m + Fintype.card n))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Here `σ²` is exactly `‖∑ AₖᵀAₖ‖ + ‖∑ AₖAₖᵀ‖`, rather than the sharper maximum used by the
preceding helper. The explicit absolute constant is `2(1+√5)`.

**Book Remark 5.4.15.** -/
theorem exercise_5_24_matrixKhintchineRectangular [Nonempty m] [Nonempty n]
    (A : ι → Matrix m n ℝ) {ε : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) {p : ℝ} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ ≤
      2 * (1 + Real.sqrt 5) *
        Real.sqrt (p + Real.log (Fintype.card m + Fintype.card n)) *
          Real.sqrt
            (‖∑ k, (A k)ᵀ * A k‖ + ‖∑ k, A k * (A k)ᵀ‖) := by
  have h := rectangularMatrixKhintchineSource (μ := μ) A hmeas hlaw hind hp
  have hv : rademacherVariance A ≤
      ‖∑ k, (A k)ᵀ * A k‖ + ‖∑ k, A k * (A k)ᵀ‖ := by
    unfold rademacherVariance rademacherVarianceLeft rademacherVarianceRight
    have hl0 := norm_nonneg (∑ k, A k * (A k)ᵀ)
    have hr0 := norm_nonneg (∑ k, (A k)ᵀ * A k)
    exact max_le (by linarith) (by linarith)
  have hsqrt := Real.sqrt_le_sqrt hv
  exact h.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))

section Symmetric

variable [Nonempty n]

/-- For a symmetric matrix family, the Rademacher variance is the operator norm of the sum of squares.

**Lean implementation helper.** -/
private lemma symmetric_variance_eq (A : ι → Matrix n n ℝ)
    (hA : ∀ k, (A k).IsHermitian) :
    rademacherVariance A = ‖∑ k, (A k) ^ 2‖ := by
  have htrans : ∀ k, (A k)ᵀ = A k := fun k => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (hA k).eq
  unfold rademacherVariance rademacherVarianceLeft rademacherVarianceRight
  have hl : (∑ k, A k * (A k)ᵀ) = ∑ k, (A k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [htrans k, pow_two]
  have hr : (∑ k, (A k)ᵀ * A k) = ∑ k, (A k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [htrans k, pow_two]
  rw [hl, hr, max_self]

/-- Matrix Hoeffding tail inequality for a Rademacher matrix series.

**Book Theorem 5.4.13.** -/
theorem matrixHoeffding
    (A : ι → Matrix n n ℝ) (hA : ∀ k, (A k).IsHermitian)
    {ε : ι → Ω → ℝ} (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, ε k ω • A k‖} ≤
      (2 * Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  have h := rectangularRademacherTail (μ := μ) A hmeas hlaw hind ht
  rw [symmetric_variance_eq A hA] at h
  have hdim : ((Fintype.card n : ℝ) + Fintype.card n) =
      (2 * Fintype.card n : ℝ) := by ring
  rwa [hdim] at h

/-- The `p=1` endpoint of the corresponding theorem, used by Chapter 6.

**Book Theorem 5.4.14.** -/
theorem matrixKhintchineOne
    (A : ι → Matrix n n ℝ) (hA : ∀ k, (A k).IsHermitian)
    {ε : ι → Ω → ℝ} (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) :
    ∫ ω, ‖∑ k, ε k ω • A k‖ ∂μ ≤
      Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ *
        Real.log (2 * Fintype.card n)) := by
  have h := rectangularRademacherExpectation (μ := μ) A hmeas hlaw hind
  rw [symmetric_variance_eq A hA] at h
  have hdim : ((Fintype.card n : ℝ) + Fintype.card n) =
      (2 * Fintype.card n : ℝ) := by ring
  rwa [hdim] at h

/-- For every real `p ≥ 1`, the `L^p` norm of a symmetric Rademacher matrix series is bounded by
an explicit absolute constant times `sqrt ‖∑ Aₖ²‖ * (sqrt p + sqrt (log (2n)))`. The declaration
uses the source's real-valued `L^p` interface; its left side is definitionally `(𝔼 ‖∑ εₖ
Aₖ‖^p)^(1/p)`.

**Book Theorem 5.4.14.** -/
theorem matrixKhintchine
    (A : ι → Matrix n n ℝ) (hA : ∀ k, (A k).IsHermitian)
    {ε : ι → Ω → ℝ} (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) {p : ℝ} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ ≤
      2 * Real.sqrt ‖∑ k, (A k) ^ 2‖ *
        (Real.sqrt (Real.log (2 * Fintype.card n)) +
          Real.sqrt 5 * Real.sqrt p) := by
  have h := rectangularMatrixKhintchine (μ := μ) A hmeas hlaw hind hp
  rw [symmetric_variance_eq A hA] at h
  have hdim : ((Fintype.card n : ℝ) + Fintype.card n) =
      (2 * Fintype.card n : ℝ) := by ring
  rwa [hdim] at h

/-- Matrix Khintchine moment bound for a Rademacher matrix series.

**Book Theorem 5.4.14.** -/
theorem matrixKhintchineSource
    (A : ι → Matrix n n ℝ) (hA : ∀ k, (A k).IsHermitian)
    {ε : ι → Ω → ℝ} (hmeas : ∀ k, Measurable (ε k))
    (hlaw : ∀ k, MatrixConcentration.IsRademacher (ε k) μ)
    (hind : iIndepFun ε μ) {p : ℝ} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ ≤
      2 * (1 + Real.sqrt 5) *
        Real.sqrt (p + Real.log (2 * Fintype.card n)) *
          Real.sqrt ‖∑ k, (A k) ^ 2‖ := by
  have h := matrixKhintchine (μ := μ) A hA hmeas hlaw hind hp
  have hD : (1 : ℝ) ≤ 2 * Fintype.card n := by
    exact_mod_cast (show 1 ≤ 2 * Fintype.card n by
      have hn := Fintype.card_pos (α := n)
      omega)
  have hs := sqrtLog_add_sqrtP_le hD hp
  calc
    HDP.Chapter1.lpNormRV (fun ω => ‖∑ k, ε k ω • A k‖) p μ
        ≤ 2 * Real.sqrt ‖∑ k, (A k) ^ 2‖ *
          (Real.sqrt (Real.log (2 * Fintype.card n)) +
            Real.sqrt 5 * Real.sqrt p) := h
    _ ≤ 2 * Real.sqrt ‖∑ k, (A k) ^ 2‖ *
          ((1 + Real.sqrt 5) *
            Real.sqrt (p + Real.log (2 * Fintype.card n))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end Symmetric

end HDP.Chapter5

end Source_13_MatrixHoeffdingKhintchine

/-! ## Material formerly in `14_SparseStochasticBlockModel.lean` -/

section Source_14_SparseStochasticBlockModel

/-!
# Chapter 5, §5.5: sparse stochastic block models

The loop-aware model has one independent coordinate for every `Sym2` edge.
This file decomposes its centered adjacency matrix into those independent
rank-at-most-two edge matrices and applies matrix Bernstein.  In particular,
the diagonal coordinates (self-loops) are not discarded.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter5

open HDP HDP.Chapter4

variable {k : ℕ}

/-- The symmetric `0/1` matrix supported by one unordered edge. A loop has one nonzero entry; a
non-loop has the two transposed entries.

**Lean implementation helper.** -/
def sbmEdgeMatrix (e : SBMEdge k) : Matrix (SBMVertex k) (SBMVertex k) ℝ :=
  fun i j => if s(i, j) = e then 1 else 0

/-- The matrix associated with an undirected edge has entry one exactly at that edge's two
ordered endpoint positions.

**Lean implementation helper.** -/
@[simp] lemma sbmEdgeMatrix_apply (e : SBMEdge k) (i j : SBMVertex k) :
    sbmEdgeMatrix e i j = if s(i, j) = e then 1 else 0 := rfl

/-- Shows that sbm edge matrix is symmetric.

**Lean implementation helper.** -/
lemma sbmEdgeMatrix_symmetric (e : SBMEdge k) : (sbmEdgeMatrix e).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [sbmEdgeMatrix, Sym2.eq_swap]

/-- The squared Frobenius norm of a stochastic-block-model edge matrix is at most `2`.

**Lean implementation helper.** -/
private lemma sbmEdgeMatrix_frobenius_sq_le (e : SBMEdge k) :
    ∑ i, ∑ j, sbmEdgeMatrix e i j ^ 2 ≤ 2 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      calc
        ∑ i, ∑ j, sbmEdgeMatrix s(a, b) i j ^ 2 ≤
            ∑ i, ∑ j,
              ((if i = a ∧ j = b then (1 : ℝ) else 0) +
                if i = b ∧ j = a then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simp only [sbmEdgeMatrix_apply, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
            Prod.swap_prod_mk, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, zero_pow]
          by_cases hdir : i = a ∧ j = b
          · rw [if_pos (Or.inl hdir), if_pos hdir]
            exact le_add_of_nonneg_right (ite_nonneg (by norm_num) (by norm_num))
          · by_cases hswap : i = b ∧ j = a
            · rw [if_pos (Or.inr hswap), if_neg hdir, if_pos hswap]
              norm_num
            · rw [if_neg (not_or_intro hdir hswap), if_neg hdir, if_neg hswap]
              norm_num
        _ = 2 := by
          have hsingle (u v : SBMVertex k) :
              (∑ i, ∑ j,
                if i = u ∧ j = v then (1 : ℝ) else 0) = 1 := by
            rw [Finset.sum_eq_single u]
            · simp
            · intro c _ hcu
              simp [hcu]
            · simp
          rw [show (∑ i, ∑ j,
                ((if i = a ∧ j = b then (1 : ℝ) else 0) +
                  if i = b ∧ j = a then (1 : ℝ) else 0)) =
              (∑ i, ∑ j, if i = a ∧ j = b then (1 : ℝ) else 0) +
              (∑ i, ∑ j, if i = b ∧ j = a then (1 : ℝ) else 0) by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_add_distrib]]
          rw [hsingle a b, hsingle b a]
          norm_num

/-- The Frobenius norm of a stochastic-block-model edge matrix is at most `√2`.

**Lean implementation helper.** -/
lemma sbmEdgeMatrix_frobenius_le (e : SBMEdge k) :
    HDP.matrixFrobeniusNorm (sbmEdgeMatrix e) ≤ Real.sqrt 2 := by
  have hs := sbmEdgeMatrix_frobenius_sq_le e
  have hsq := HDP.matrixFrobeniusNorm_sq (sbmEdgeMatrix e)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [HDP.matrixFrobeniusNorm_nonneg (sbmEdgeMatrix e),
    Real.sqrt_nonneg 2]

/-- The operator norm of a stochastic-block-model edge matrix is at most `√2`.

**Lean implementation helper.** -/
lemma sbmEdgeMatrix_opNorm_le (e : SBMEdge k) :
    HDP.matrixOpNorm (sbmEdgeMatrix e) ≤ Real.sqrt 2 :=
  (HDP.Chapter4.operatorNorm_le_frobeniusNorm (sbmEdgeMatrix e)).trans
    (sbmEdgeMatrix_frobenius_le e)

/-- The `2k` unordered edge coordinates incident to a fixed vertex, including its loop
coordinate.

**Lean implementation helper.** -/
def sbmIncidentEdges (i : SBMVertex k) : Finset (SBMEdge k) :=
  Finset.univ.image (fun j => s(i,j))

/-- Shows that sbm incident edge map is injective.

**Lean implementation helper.** -/
private lemma sbmIncidentEdgeMap_injective (i : SBMVertex k) :
    Function.Injective (fun j : SBMVertex k => s(i,j)) := by
  intro a b h
  rcases Sym2.eq_iff.mp h with h | h
  · exact h.2
  · exact h.2.trans h.1

/-- Computes the cardinality of sbm incident edges.

**Lean implementation helper.** -/
@[simp] lemma card_sbmIncidentEdges (i : SBMVertex k) :
    (sbmIncidentEdges i).card = 2 * k := by
  classical
  rw [sbmIncidentEdges,
    Finset.card_image_of_injective _ (sbmIncidentEdgeMap_injective i)]
  simp

/-- Squaring an edge matrix gives the diagonal projector onto its two incident vertices.

**Lean implementation helper.** -/
private lemma sbmEdgeMatrix_sq_mk (a b i j : SBMVertex k) :
    (sbmEdgeMatrix s(a,b) * sbmEdgeMatrix s(a,b)) i j =
      if i = j ∧ (i = a ∨ i = b) then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, sbmEdgeMatrix_apply]
  simp only [Sym2.eq_iff, ite_mul, one_mul, zero_mul]
  by_cases hij : i = j
  · subst j
    by_cases hia : i = a
    · subst a
      rw [Finset.sum_eq_single b]
      all_goals simp_all [eq_comm]
      all_goals aesop
    · by_cases hib : i = b
      · subst b
        rw [Finset.sum_eq_single a] <;> simp_all [eq_comm]
      · simp [hia, hib]
  · by_cases hia : i = a
    · subst a
      rw [Finset.sum_eq_single b]
      all_goals simp_all [eq_comm]
      all_goals aesop
    · by_cases hib : i = b
      · subst b
        rw [Finset.sum_eq_single a] <;> simp_all [eq_comm]
      · simp [hia, hib, hij]

/-- Squaring a single symmetric edge matrix produces the diagonal projection onto the endpoints
of that edge.

**Lean implementation helper.** -/
lemma sbmEdgeMatrix_sq_apply (e : SBMEdge k) (i j : SBMVertex k) :
    (sbmEdgeMatrix e * sbmEdgeMatrix e) i j =
      if i = j ∧ e ∈ sbmIncidentEdges i then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [sbmEdgeMatrix_sq_mk]
      congr 2
      simp [sbmIncidentEdges, eq_comm]
      all_goals aesop

/-- Independent centered edge summands for the adjacency noise.

**Lean implementation helper.** -/
noncomputable def sbmEdgeSummand (p q : Set.Icc (0 : ℝ) 1)
    (e : SBMEdge k) (G : SBMSample k) :
    Matrix (SBMVertex k) (SBMVertex k) ℝ :=
  (sbmEdgeIndicator e G - (sbmEdgeProbability p q e : ℝ)) • sbmEdgeMatrix e

/-- Bounds abs sbm centered edge by one.

**Lean implementation helper.** -/
private lemma abs_sbmCenteredEdge_le_one (p q : Set.Icc (0 : ℝ) 1)
    (e : SBMEdge k) (G : SBMSample k) :
    |sbmEdgeIndicator e G - (sbmEdgeProbability p q e : ℝ)| ≤ 1 := by
  have hrange : (0 : ℝ) ≤ (sbmEdgeProbability p q e : ℝ) ∧
      (sbmEdgeProbability p q e : ℝ) ≤ 1 :=
    ⟨(sbmEdgeProbability p q e).2.1, (sbmEdgeProbability p q e).2.2⟩
  cases hG : G e
  · simp only [sbmEdgeIndicator, hG, Bool.false_eq_true, if_false, zero_sub,
      abs_neg]
    rw [abs_of_nonneg hrange.1]
    exact hrange.2
  · simp only [sbmEdgeIndicator, hG, if_true]
    rw [abs_of_nonneg (sub_nonneg.mpr hrange.2)]
    linarith [hrange.1]

/-- Every centered stochastic-block-model edge summand has operator norm at most `√2`.

**Lean implementation helper.** -/
lemma sbmEdgeSummand_norm_le (p q : Set.Icc (0 : ℝ) 1)
    (e : SBMEdge k) (G : SBMSample k) :
    HDP.matrixOpNorm (sbmEdgeSummand p q e G) ≤ Real.sqrt 2 := by
  rw [sbmEdgeSummand, HDP.matrixOpNorm_smul]
  calc
    |sbmEdgeIndicator e G - (sbmEdgeProbability p q e : ℝ)| *
        HDP.matrixOpNorm (sbmEdgeMatrix e) ≤
      1 * Real.sqrt 2 := mul_le_mul
        (abs_sbmCenteredEdge_le_one p q e G)
        (sbmEdgeMatrix_opNorm_le e) (HDP.matrixOpNorm_nonneg _) (by norm_num)
    _ = Real.sqrt 2 := one_mul _

/-- Shows that sbm edge summand is measurable.

**Lean implementation helper.** -/
lemma sbmEdgeSummand_measurable (p q : Set.Icc (0 : ℝ) 1)
    (e : SBMEdge k) : Measurable (sbmEdgeSummand p q e) := by
  fun_prop

/-- Shows that sbm edge summand is independent.

**Lean implementation helper.** -/
lemma sbmEdgeSummand_independent (p q : Set.Icc (0 : ℝ) 1) :
    iIndepFun (sbmEdgeSummand (k := k) p q) (stochasticBlockModel k p q) := by
  exact (sbmEdgeIndicator_independent p q).comp
    (fun e z => (z - (sbmEdgeProbability p q e : ℝ)) • sbmEdgeMatrix e)
    (fun _ => by fun_prop)

/-- Summing all centered edge summands gives the stochastic-block-model noise matrix.

**Lean implementation helper.** -/
lemma sum_sbmEdgeSummand (p q : Set.Icc (0 : ℝ) 1) (G : SBMSample k) :
    ∑ e, sbmEdgeSummand p q e G = sbmNoise p q G := by
  ext i j
  simp only [sbmEdgeSummand, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, sbmEdgeMatrix_apply]
  rw [Finset.sum_eq_single s(i, j)]
  · rw [sbmNoise_apply, sbmEdgeProbability_mk]
    by_cases hs : sbmSameCommunity i j <;> simp [hs]
  · intro b _ hne
    rw [if_neg (fun h => hne h.symm)]
    ring
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Shows that sbm edge summand is centered.

**Lean implementation helper.** -/
lemma sbmEdgeSummand_centered (p q : Set.Icc (0 : ℝ) 1)
    (e : SBMEdge k) :
    HDP.realMatrixExpectation (stochasticBlockModel k p q)
      (sbmEdgeSummand p q e) = 0 := by
  ext i j
  simp only [HDP.realMatrixExpectation_apply, sbmEdgeSummand,
    Matrix.smul_apply, smul_eq_mul]
  rw [integral_mul_const]
  change (∫ a, sbmEdgeIndicator e a - (sbmEdgeProbability p q e : ℝ)
      ∂(stochasticBlockModel k p q)) * sbmEdgeMatrix e i j = (0 : ℝ)
  have hI : Integrable (sbmEdgeIndicator e) (stochasticBlockModel k p q) := by
    simpa only [id_eq] using
      (sbmEdgeIndicator_isBernoulli p q e).integrable_comp id
  have hcoef : (∫ a, sbmEdgeIndicator e a -
      (sbmEdgeProbability p q e : ℝ) ∂(stochasticBlockModel k p q)) = 0 := by
    rw [integral_sub hI (integrable_const _),
      (sbmEdgeIndicator_isBernoulli p q e).integral_eq]
    simp
  rw [hcoef, zero_mul]

/-- A centered stochastic-block-model edge indicator has variance `p_e (1 - p_e)`.

**Lean implementation helper.** -/
private lemma integral_sbmCenteredEdge_sq (p q : Set.Icc (0 : ℝ) 1)
    (e : SBMEdge k) :
    (∫ G, (sbmEdgeIndicator e G - (sbmEdgeProbability p q e : ℝ)) ^ 2
        ∂(stochasticBlockModel k p q)) =
      (sbmEdgeProbability p q e : ℝ) *
        (1 - (sbmEdgeProbability p q e : ℝ)) := by
  have h := (sbmEdgeIndicator_isBernoulli p q e).integral_comp
    (fun z : ℝ => (z - (sbmEdgeProbability p q e : ℝ)) ^ 2)
  rw [h]
  ring

/-- The expected square of an edge summand is diagonal: its incident diagonal entries equal the
edge variance and all other entries vanish.

**Lean implementation helper.** -/
private lemma expectation_sbmEdgeSummand_sq_apply
    (p q : Set.Icc (0 : ℝ) 1) (e : SBMEdge k) (i j : SBMVertex k) :
    HDP.realMatrixExpectation (stochasticBlockModel k p q) (fun G =>
      sbmEdgeSummand p q e G * sbmEdgeSummand p q e G) i j =
      if i = j ∧ e ∈ sbmIncidentEdges i then
        (sbmEdgeProbability p q e : ℝ) *
          (1 - (sbmEdgeProbability p q e : ℝ)) else 0 := by
  rw [HDP.realMatrixExpectation_apply]
  simp only [sbmEdgeSummand]
  simp_rw [smul_mul_smul_comm]
  rw [show (fun G =>
      (((sbmEdgeIndicator e G - (sbmEdgeProbability p q e : ℝ)) *
        (sbmEdgeIndicator e G - (sbmEdgeProbability p q e : ℝ))) •
          (sbmEdgeMatrix e * sbmEdgeMatrix e)) i j) =
      fun G => (sbmEdgeIndicator e G -
        (sbmEdgeProbability p q e : ℝ)) ^ 2 *
          (sbmEdgeMatrix e * sbmEdgeMatrix e) i j by
        funext G
        simp [pow_two]]
  rw [integral_mul_const, integral_sbmCenteredEdge_sq,
    sbmEdgeMatrix_sq_apply]
  split_ifs <;> ring

/-- Bounds sbm edge probability by of le.

**Lean implementation helper.** -/
private lemma sbmEdgeProbability_le_of_le (p q : Set.Icc (0 : ℝ) 1)
    (hqp : (q : ℝ) ≤ p) (e : SBMEdge k) :
    (sbmEdgeProbability p q e : ℝ) ≤ p := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      rw [sbmEdgeProbability_mk]
      split <;> simp_all

/-- The edgewise matrix variance is diagonal.

**Lean implementation helper.** -/
lemma sum_expectation_sbmEdgeSummand_sq (p q : Set.Icc (0 : ℝ) 1) :
    (∑ e, HDP.realMatrixExpectation (stochasticBlockModel k p q) (fun G =>
      sbmEdgeSummand p q e G * sbmEdgeSummand p q e G)) =
      Matrix.diagonal (fun i => ∑ e,
        if e ∈ sbmIncidentEdges i then
          (sbmEdgeProbability p q e : ℝ) *
            (1 - (sbmEdgeProbability p q e : ℝ)) else 0) := by
  ext i j
  simp only [Matrix.sum_apply, expectation_sbmEdgeSummand_sq_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Shows that sbm variance diagonal is nonnegative.

**Lean implementation helper.** -/
private lemma sbmVarianceDiagonal_nonneg (p q : Set.Icc (0 : ℝ) 1)
    (i : SBMVertex k) :
    0 ≤ ∑ e, if e ∈ sbmIncidentEdges i then
      (sbmEdgeProbability p q e : ℝ) *
        (1 - (sbmEdgeProbability p q e : ℝ)) else 0 := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact mul_nonneg (sbmEdgeProbability p q e).2.1
      (sub_nonneg.mpr (sbmEdgeProbability p q e).2.2)
  · exact le_rfl

/-- The variance contribution incident to any vertex is at most `2kp`.

**Lean implementation helper.** -/
private lemma sbmVarianceDiagonal_le (p q : Set.Icc (0 : ℝ) 1)
    (hqp : (q : ℝ) ≤ p) (i : SBMVertex k) :
    (∑ e, if e ∈ sbmIncidentEdges i then
      (sbmEdgeProbability p q e : ℝ) *
        (1 - (sbmEdgeProbability p q e : ℝ)) else 0) ≤
      (2 * k : ℝ) * p := by
  calc
    (∑ e, if e ∈ sbmIncidentEdges i then
        (sbmEdgeProbability p q e : ℝ) *
          (1 - (sbmEdgeProbability p q e : ℝ)) else 0) ≤
        ∑ e, if e ∈ sbmIncidentEdges i then (p : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs
      · calc
          (sbmEdgeProbability p q e : ℝ) *
              (1 - (sbmEdgeProbability p q e : ℝ)) ≤
              (sbmEdgeProbability p q e : ℝ) := by
                nlinarith [(sbmEdgeProbability p q e).2.1,
                  (sbmEdgeProbability p q e).2.2]
          _ ≤ p := sbmEdgeProbability_le_of_le p q hqp e
      · exact le_rfl
    _ = (2 * k : ℝ) * p := by
      rw [show (∑ e : SBMEdge k,
          if e ∈ sbmIncidentEdges i then (p : ℝ) else 0) =
          (sbmIncidentEdges i).card * (p : ℝ) by simp]
      rw [card_sbmIncidentEdges]
      push_cast
      ring

/-- The sparse SBM matrix-variance statistic is bounded by the largest expected row degree `2k
p` when `q ≤ p`.

**Book Chapter 5, pp.168--170, sparse SBM proof.** -/
theorem sbmEdgeVariance_le (p q : Set.Icc (0 : ℝ) 1)
    (hqp : (q : ℝ) ≤ p) :
    matrixVariance (μ := stochasticBlockModel k p q)
        (sbmEdgeSummand p q) ≤ (2 * k : ℝ) * p := by
  rw [matrixVariance_eq_symmetricMatrixVariance
    (μ := stochasticBlockModel k p q) (sbmEdgeSummand p q)
    (fun e G => Matrix.isHermitian_iff_isSymm.mpr
      ((sbmEdgeMatrix_symmetric e).smul _))]
  rw [symmetricMatrixVariance, sum_expectation_sbmEdgeSummand_sq]
  change HDP.matrixOpNorm (Matrix.diagonal (fun i => ∑ e,
    if e ∈ sbmIncidentEdges i then
      (sbmEdgeProbability p q e : ℝ) *
        (1 - (sbmEdgeProbability p q e : ℝ)) else 0)) ≤ (2 * k : ℝ) * p
  rw [HDP.Chapter4.exercise_4_3b_diagonal]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by positivity) p.2.1)).2
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (sbmVarianceDiagonal_nonneg p q i)]
  exact sbmVarianceDiagonal_le p q hqp i

/-- The exact sparse-edge Matrix Bernstein expectation estimate. Its variance statistic is
computable from the independent Bernoulli edge summands and is refined below by degree
information.

**Book (5.19).** -/
theorem sparseSBM_expectedNoise_exact {k : ℕ} [NeZero k]
    (p q : Set.Icc (0 : ℝ) 1) :
    ∫ G, HDP.matrixOpNorm (sbmNoise p q G)
        ∂(stochasticBlockModel k p q) ≤
      Real.sqrt (2 * matrixVariance (μ := stochasticBlockModel k p q)
        (sbmEdgeSummand p q) * Real.log (4 * k)) +
      Real.sqrt 2 / 3 * Real.log (4 * k) := by
  have h := matrixBernsteinExpectation
    (μ := stochasticBlockModel k p q) (sbmEdgeSummand p q)
    (sbmEdgeSummand_measurable p q)
    (sbmEdgeSummand_norm_le p q) (Real.sqrt_nonneg _)
    (sbmEdgeSummand_centered p q) (sbmEdgeSummand_independent p q)
  simp only [Fintype.card_fin] at h
  have hcast : ((2 * k : ℕ) : ℝ) + (2 * k : ℕ) = 4 * (k : ℝ) := by
    push_cast
    ring
  rw [hcast] at h
  simpa [sum_sbmEdgeSummand, HDP.matrixOpNorm] using h

/-- Explicit degree-scale expectation form.

**Book Remark 5.5.2.** -/
theorem sparseSBM_expectedNoise_degree {k : ℕ} [NeZero k]
    (p q : Set.Icc (0 : ℝ) 1) (hqp : (q : ℝ) ≤ p) :
    ∫ G, HDP.matrixOpNorm (sbmNoise p q G)
        ∂(stochasticBlockModel k p q) ≤
      Real.sqrt (4 * k * (p : ℝ) * Real.log (4 * k)) +
        Real.sqrt 2 / 3 * Real.log (4 * k) := by
  have hmain := sparseSBM_expectedNoise_exact (k := k) p q
  have hvar := sbmEdgeVariance_le (k := k) p q hqp
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hlog : 0 ≤ Real.log (4 * k) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  calc
    ∫ G, HDP.matrixOpNorm (sbmNoise p q G)
        ∂(stochasticBlockModel k p q) ≤
      Real.sqrt (2 * matrixVariance (μ := stochasticBlockModel k p q)
        (sbmEdgeSummand p q) * Real.log (4 * k)) +
      Real.sqrt 2 / 3 * Real.log (4 * k) := hmain
    _ ≤ Real.sqrt (4 * k * (p : ℝ) * Real.log (4 * k)) +
        Real.sqrt 2 / 3 * Real.log (4 * k) := by
      have hsqrt : Real.sqrt (2 * matrixVariance
          (μ := stochasticBlockModel k p q) (sbmEdgeSummand p q) *
            Real.log (4 * k)) ≤
          Real.sqrt (4 * k * (p : ℝ) * Real.log (4 * k)) := by
        apply Real.sqrt_le_sqrt
        calc
          2 * matrixVariance (μ := stochasticBlockModel k p q)
                (sbmEdgeSummand p q) * Real.log (4 * k) ≤
              2 * ((2 * k : ℝ) * p) * Real.log (4 * k) := by
            gcongr
          _ = 4 * k * (p : ℝ) * Real.log (4 * k) := by ring
      simpa [add_comm] using
        add_le_add_right hsqrt (Real.sqrt 2 / 3 * Real.log (4 * k))

/-- Expected degree is `(a+b)/2`, and logarithmic degree is enough in the theorem's regime.

**Book Remark 5.5.2.** -/
theorem remark_5_5_2_expectedDegree {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (a b : ℝ)
    (hp : (p : ℝ) = a / (2 * k)) (hq : (q : ℝ) = b / (2 * k))
    (i : SBMVertex k) :
    ∑ j, sbmExpectedAdjacency k p q i j = (a + b) / 2 := by
  rw [HDP.Chapter4.remark_4_5_3_expectedDegree, hp, hq]
  have hkR : (k : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr hk.ne')
  field_simp

/-- High-probability sparse SBM noise estimate with its exact edge variance statistic.

**Book Chapter 5, pp.168--170, sparse SBM proof.** -/
theorem sparseSBM_noise_tail_exact {k : ℕ} [NeZero k]
    (p q : Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (stochasticBlockModel k p q).real
        {G | t ≤ HDP.matrixOpNorm (sbmNoise p q G)} ≤
      (4 * k : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (matrixVariance (μ := stochasticBlockModel k p q)
          (sbmEdgeSummand p q) + Real.sqrt 2 * t / 3)) := by
  have h := matrixBernsteinTail
    (μ := stochasticBlockModel k p q) (sbmEdgeSummand p q)
    (sbmEdgeSummand_measurable p q)
    (sbmEdgeSummand_norm_le p q) (Real.sqrt_nonneg _)
    (sbmEdgeSummand_centered p q) (sbmEdgeSummand_independent p q) ht
  simp only [Fintype.card_fin] at h
  have hcast : ((2 * k : ℕ) : ℝ) + (2 * k : ℕ) = 4 * (k : ℝ) := by
    push_cast
    ring
  rw [hcast] at h
  simpa [sum_sbmEdgeSummand, HDP.matrixOpNorm] using h

/-- Deterministic recovery endpoint for the sparse Bernstein noise scale.

**Lean implementation helper.** -/
theorem sparseSBM_misclassified_of_noise {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (hqp : (q : ℝ) < p) (G : SBMSample k) {M : ℝ} (hM : 0 ≤ M)
    (hnoise : HDP.matrixOpNorm (sbmNoise p q G) ≤ M) :
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) ≤
      ‖sbmLabelVector k‖ ^ 2 *
        (Real.sqrt 2 *
          (2 * M / ((k : ℝ) * min (q : ℝ) ((p : ℝ) - q)))) ^ 2 := by
  simpa using spectral_misclassified_of_noise hk p q hq hqp G hM hnoise

/-- Deterministic `99%`-accuracy endpoint in the source parametrization `p=a/(2k)`, `q=b/(2k)`.

**Book Chapter 5, pp.168--170, sparse SBM proof.** -/
theorem sparseSBM_accuracy_of_small_noise {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) {a b : ℝ}
    (hp : (p : ℝ) = a / (2 * k)) (hqscale : (q : ℝ) = b / (2 * k))
    (hba : b < a) (hab3 : a < 3 * b) (G : SBMSample k)
    (hnoise : HDP.matrixOpNorm (sbmNoise p q G) ≤ (a - b) / 120) :
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) ≤
      (2 * k : ℝ) / 100 := by
  let gap : ℝ := a - b
  let δ : ℝ := (k : ℝ) * min (q : ℝ) ((p : ℝ) - q)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hb : 0 < b := by nlinarith
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hqpos : 0 < (q : ℝ) := by rw [hqscale]; positivity
  have hqp : (q : ℝ) < p := by
    rw [hqscale, hp]
    exact (div_lt_div_iff_of_pos_right (by positivity)).2 hba
  have hhalf : gap / (4 * k : ℝ) ≤
      min (q : ℝ) ((p : ℝ) - q) := by
    apply le_min
    · rw [hqscale]
      have hgb : gap ≤ 2 * b := by dsimp [gap]; linarith
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * k)
        (by positivity : (0 : ℝ) < 2 * k)]
      nlinarith
    · rw [hp, hqscale]
      have hden : (2 * k : ℝ) ≠ 0 := by positivity
      field_simp [hden]
      nlinarith
  have hδ : gap / 4 ≤ δ := by
    calc
      gap / 4 = (k : ℝ) * (gap / (4 * k)) := by field_simp
      _ ≤ (k : ℝ) * min (q : ℝ) ((p : ℝ) - q) :=
        mul_le_mul_of_nonneg_left hhalf hkR.le
      _ = δ := rfl
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  have ht0 : 0 ≤ gap / 120 := by positivity
  have hmis := sparseSBM_misclassified_of_noise hk p q hqpos hqp G ht0 hnoise
  change _ ≤ ‖sbmLabelVector k‖ ^ 2 *
    (Real.sqrt 2 * (2 * (gap / 120) / δ)) ^ 2 at hmis
  have hratio : 2 * (gap / 120) / δ ≤ (1 : ℝ) / 15 := by
    rw [div_le_iff₀ hδpos]
    nlinarith
  have hratio0 : 0 ≤ 2 * (gap / 120) / δ := by positivity
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquare : (Real.sqrt 2 * (2 * (gap / 120) / δ)) ^ 2 ≤
      (2 : ℝ) / 225 := by
    rw [mul_pow, hsqrt2]
    have := (sq_le_sq₀ hratio0 (by norm_num : (0 : ℝ) ≤ 1 / 15)).2 hratio
    nlinarith
  calc
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) ≤
        ‖sbmLabelVector k‖ ^ 2 *
          (Real.sqrt 2 * (2 * (gap / 120) / δ)) ^ 2 := hmis
    _ ≤ (2 * (k : ℝ)) * ((2 : ℝ) / 225) := by
      rw [HDP.Chapter4.label_norm_sq]
      gcongr
    _ ≤ (2 * k : ℝ) / 100 := by
      nlinarith [hkR.le]

/-- An explicit absolute constant witnessing the unspecified `C` in the corresponding theorem.
No optimization is intended.

**Lean implementation helper.** -/
def sparseSBMRecoveryConstant : ℝ := 600000

/-- Shows that sparse sbmrecovery constant is positive.

**Lean implementation helper.** -/
lemma sparseSBMRecoveryConstant_pos : 0 < sparseSBMRecoveryConstant := by
  norm_num [sparseSBMRecoveryConstant]

/-- Under the sparse recovery signal condition, the stochastic-block-model noise exceeds `(a-b)/120` with probability at most `1/100`.

**Lean implementation helper.** -/
private theorem sparseSBM_smallNoise_probability {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) {a b : ℝ}
    (hp : (p : ℝ) = a / (2 * k)) (hqscale : (q : ℝ) = b / (2 * k))
    (hba : b < a) (hab3 : a < 3 * b)
    (hsignal : sparseSBMRecoveryConstant * a * Real.log (2 * k) ≤
      (a - b) ^ 2) :
    (stochasticBlockModel k p q).real
        {G | (a - b) / 120 ≤ HDP.matrixOpNorm (sbmNoise p q G)} ≤
      (1 : ℝ) / 100 := by
  letI : NeZero k := ⟨hk.ne'⟩
  let gap : ℝ := a - b
  let t : ℝ := gap / 120
  let v : ℝ := matrixVariance (μ := stochasticBlockModel k p q)
    (sbmEdgeSummand p q)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hb : 0 < b := by nlinarith
  have ha : 0 < a := by linarith
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hqp : (q : ℝ) ≤ p := by
    rw [hqscale, hp]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 hba.le
  have hvar0 := sbmEdgeVariance_le (k := k) p q hqp
  have hvar : v ≤ a := by
    calc
      v ≤ (2 * k : ℝ) * p := hvar0
      _ = a := by rw [hp]; field_simp
  have hv : 0 ≤ v := by
    dsimp [v, matrixVariance]
    exact le_max_of_le_left (norm_nonneg _)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hgaplt : gap < a := by dsimp [gap]; linarith
  have hdenle : v + Real.sqrt 2 * t / 3 ≤ 2 * a := by
    dsimp [t]
    have hmul : Real.sqrt 2 * gap ≤ 2 * a :=
      (mul_le_mul_of_nonneg_left hgaplt.le (Real.sqrt_nonneg 2)).trans
        (mul_le_mul_of_nonneg_right hsqrt2 ha.le)
    nlinarith
  have hdenpos : 0 < v + Real.sqrt 2 * t / 3 := by positivity
  have hlog : 0 < Real.log (2 * k) := Real.log_pos (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith)
  have hscale : 20 * a * Real.log (2 * k) ≤ t ^ 2 / 2 := by
    dsimp [t, gap, sparseSBMRecoveryConstant] at hsignal ⊢
    nlinarith
  have hrate : 10 * Real.log (2 * k) ≤
      t ^ 2 / 2 / (v + Real.sqrt 2 * t / 3) := by
    rw [le_div_iff₀ hdenpos]
    calc
      10 * Real.log (2 * k) * (v + Real.sqrt 2 * t / 3) ≤
          10 * Real.log (2 * k) * (2 * a) :=
        mul_le_mul_of_nonneg_left hdenle (by positivity)
      _ = 20 * a * Real.log (2 * k) := by ring
      _ ≤ t ^ 2 / 2 := hscale
  have hlog200 : Real.log 200 ≤ 9 * Real.log 2 := by
    calc
      Real.log 200 ≤ Real.log ((2 : ℝ) ^ 9) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 9 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlog2le : Real.log 2 ≤ Real.log (2 * k) := by
    apply Real.log_le_log (by norm_num)
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hlog400 : Real.log (400 * k) ≤ 10 * Real.log (2 * k) := by
    rw [show (400 * k : ℝ) = 200 * (2 * k) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    nlinarith
  have htail := sparseSBM_noise_tail_exact (k := k) p q ht.le
  change (stochasticBlockModel k p q).real
      {G | t ≤ HDP.matrixOpNorm (sbmNoise p q G)} ≤
    (4 * k : ℝ) * Real.exp (-(t ^ 2) / 2 /
      (v + Real.sqrt 2 * t / 3)) at htail
  calc
    (stochasticBlockModel k p q).real
        {G | (a - b) / 120 ≤ HDP.matrixOpNorm (sbmNoise p q G)} =
      (stochasticBlockModel k p q).real
        {G | t ≤ HDP.matrixOpNorm (sbmNoise p q G)} := by rfl
    _ ≤ (4 * k : ℝ) * Real.exp (-(t ^ 2) / 2 /
          (v + Real.sqrt 2 * t / 3)) := htail
    _ ≤ (4 * k : ℝ) * Real.exp (-Real.log (400 * k)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        rw [show -(t ^ 2) / 2 / (v + Real.sqrt 2 * t / 3) =
          -(t ^ 2 / 2 / (v + Real.sqrt 2 * t / 3)) by ring]
        exact (neg_le_neg hrate).trans (neg_le_neg hlog400)
      · positivity
    _ = (1 : ℝ) / 100 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 400 * k)]
      field_simp
      norm_num

/-- For `p=a/(2k)`, `q=b/(2k)`, the explicit signal condition below makes the bad classification
event have probability at most `0.01`, equivalently giving success probability at least `0.99`.

**Book Theorem 5.5.1.** -/
theorem theorem_5_5_1 {k : ℕ} (hk : 0 < k)
    (p q : Set.Icc (0 : ℝ) 1) {a b : ℝ}
    (hp : (p : ℝ) = a / (2 * k)) (hqscale : (q : ℝ) = b / (2 * k))
    (hba : b < a) (hab3 : a < 3 * b)
    (hsignal : sparseSBMRecoveryConstant * a * Real.log (2 * k) ≤
      (a - b) ^ 2) :
    (stochasticBlockModel k p q).real
      {G | (2 * k : ℝ) / 100 <
        (misclassifiedUpToSign sbmCommunityLabel
          (sbmSpectralEstimate hk G) : ℝ)} ≤ (1 : ℝ) / 100 := by
  have htail := sparseSBM_smallNoise_probability hk p q hp hqscale hba hab3 hsignal
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans htail
  intro G hbad
  change (2 * k : ℝ) / 100 <
    (misclassifiedUpToSign sbmCommunityLabel (sbmSpectralEstimate hk G) : ℝ) at hbad
  change (a - b) / 120 ≤ HDP.matrixOpNorm (sbmNoise p q G)
  by_contra hnot
  have hacc := sparseSBM_accuracy_of_small_noise hk p q hp hqscale hba hab3 G
    (le_of_lt (lt_of_not_ge hnot))
  linarith

end HDP.Chapter5

end Source_14_SparseStochasticBlockModel

/-! ## Material formerly in `15_GeneralCovarianceEstimation.lean` -/

section Source_15_GeneralCovarianceEstimation

/-!
# Chapter 5, §5.6: covariance estimation for bounded distributions

This file keeps the source's uncentered second moment separate from centered
covariance.  The source-neutral ranks below are total at zero (`0 / 0 = 0` in
Lean), while every lower bound that divides by the operator norm carries a
nonzero hypothesis.  In particular, continuity is asserted only on the
nonzero locus, correcting the printed Exercise 5.29(c).
-/

open Matrix WithLp MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
  RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace HDP

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The effective rank `tr(A) / ‖A‖` of a real square matrix. The intended use is for
positive-semidefinite matrices. This definition is deliberately total, with `effectiveRank 0 =
0`.

**Book Remark 5.6.3.** -/
noncomputable def effectiveRank [DecidableEq n] (A : Matrix n n ℝ) : ℝ :=
  A.trace / matrixOpNorm A

/-- The stable rank `‖A‖_F² / ‖A‖²` of a real rectangular matrix, total at zero.

**Book Remark 5.6.4.** -/
noncomputable def stableRank [DecidableEq n] (A : Matrix m n ℝ) : ℝ :=
  matrixFrobeniusNorm A ^ 2 / matrixOpNorm A ^ 2

/-- The effective rank of the zero square matrix is zero.

**Lean implementation helper.** -/
@[simp] theorem effectiveRank_zero [DecidableEq n] :
    effectiveRank (0 : Matrix n n ℝ) = 0 := by
  simp [effectiveRank]

/-- The stable rank of the zero rectangular matrix is zero.

**Lean implementation helper.** -/
@[simp] theorem stableRank_zero [DecidableEq n] :
    stableRank (0 : Matrix m n ℝ) = 0 := by
  simp [stableRank]

/-- Effective rank is invariant under positive rescaling.

**Lean implementation helper.** -/
theorem effectiveRank_smul {c : ℝ} (hc : 0 < c) [DecidableEq n]
    (A : Matrix n n ℝ) : effectiveRank (c • A) = effectiveRank A := by
  rw [effectiveRank, effectiveRank, Matrix.trace_smul, matrixOpNorm_smul,
    abs_of_pos hc]
  exact mul_div_mul_left _ _ hc.ne'

/-- Stable rank is invariant under every nonzero real rescaling.

**Lean implementation helper.** -/
theorem stableRank_smul {c : ℝ} (hc : c ≠ 0) [DecidableEq n]
    (A : Matrix m n ℝ) : stableRank (c • A) = stableRank A := by
  rw [stableRank, stableRank, matrixFrobeniusNorm_smul, matrixOpNorm_smul]
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  field_simp

/-- Establishes continuity of matrix Frobenius norm.

**Lean implementation helper.** -/
private lemma continuous_matrixFrobeniusNorm :
    Continuous (matrixFrobeniusNorm : Matrix m n ℝ → ℝ) := by
  unfold matrixFrobeniusNorm
  fun_prop

/-- Establishes continuity of matrix operator norm.

**Lean implementation helper.** -/
private lemma continuous_matrixOpNorm [DecidableEq n] :
    Continuous (matrixOpNorm : Matrix m n ℝ → ℝ) := by
  exact continuous_norm

/-- Establishes continuity of matrix trace.

**Lean implementation helper.** -/
private lemma continuous_matrixTrace :
    Continuous (fun A : Matrix n n ℝ => A.trace) := by
  unfold Matrix.trace Matrix.diag
  fun_prop

/-- Effective/stable rank identities, bounds, continuity, and support-subspace behavior.

**Book Remark 5.6.4.** -/
theorem continuousAt_effectiveRank [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A ≠ 0) :
    ContinuousAt (effectiveRank : Matrix n n ℝ → ℝ) A := by
  have hn : matrixOpNorm A ≠ 0 := by
    change ‖A‖ ≠ 0
    exact norm_ne_zero_iff.mpr hA
  exact continuous_matrixTrace.continuousAt.div
    continuous_matrixOpNorm.continuousAt hn

/-- The stable-rank analogue of the corrected continuity statement.

**Book Remark 5.6.4.** -/
theorem continuousAt_stableRank [DecidableEq n]
    {A : Matrix m n ℝ} (hA : A ≠ 0) :
    ContinuousAt (stableRank : Matrix m n ℝ → ℝ) A := by
  have hn : matrixOpNorm A ^ 2 ≠ 0 := by
    apply pow_ne_zero
    change ‖A‖ ≠ 0
    exact norm_ne_zero_iff.mpr hA
  exact (continuous_matrixFrobeniusNorm.pow 2).continuousAt.div
    (continuous_matrixOpNorm.pow 2).continuousAt hn

/-- Stable rank is the effective rank of the Gram matrix. This identity is zero-safe and
therefore needs no nondegeneracy hypothesis.

**Book Remark 5.6.4.** -/
theorem stableRank_eq_effectiveRank_gram {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) :
    stableRank A = effectiveRank (gramMatrix A) := by
  rw [stableRank, effectiveRank, ← matrixOpNorm_sq_eq_gram A]
  congr 1
  rw [gramMatrix, ← matrixInner_eq_trace A A, matrixInner_self]

/-- A nonzero matrix has stable rank at least one.

**Lean implementation helper.** -/
theorem one_le_stableRank {p q : ℕ}
    {A : Matrix (Fin p) (Fin q) ℝ} (hA : A ≠ 0) :
    1 ≤ stableRank A := by
  have hop : 0 < matrixOpNorm A := by
    change 0 < ‖A‖
    exact norm_pos_iff.mpr hA
  have hle := Chapter4.operatorNorm_le_frobeniusNorm A
  rw [stableRank, le_div_iff₀ (sq_pos_of_pos hop)]
  nlinarith [matrixFrobeniusNorm_nonneg A]

/-- Stable rank is at most the dimension of the range. This is the rank bound in the
corresponding exercise, stated using the source's authoritative matrix-rank wrapper.

**Lean implementation helper.** -/
theorem stableRank_le_matrixRank {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) :
    stableRank A ≤ matrixRank A := by
  by_cases hA : A = 0
  · subst A
    simp [stableRank, matrixRank]
  · have hop : 0 < matrixOpNorm A := by
      change 0 < ‖A‖
      exact norm_pos_iff.mpr hA
    have hf := Chapter4.frobeniusNorm_le_sqrt_rank_mul_operatorNorm A le_rfl
    have hsqrt : (Real.sqrt (matrixRank A)) ^ 2 = (matrixRank A : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsq : matrixFrobeniusNorm A ^ 2 ≤
        (matrixRank A : ℝ) * matrixOpNorm A ^ 2 := by
      have hnF := matrixFrobeniusNorm_nonneg A
      have hnR : 0 ≤ Real.sqrt (matrixRank A) * matrixOpNorm A :=
        mul_nonneg (Real.sqrt_nonneg _) hop.le
      nlinarith
    rw [stableRank, div_le_iff₀ (sq_pos_of_pos hop)]
    simpa [mul_comm] using hsq

/-- The corrected stable-rank chain, including the zero-safe upper bound.

**Book Remark 5.6.4.** -/
theorem stableRank_bounds {p q : ℕ}
    {A : Matrix (Fin p) (Fin q) ℝ} (hA : A ≠ 0) :
    1 ≤ stableRank A ∧ stableRank A ≤ matrixRank A :=
  ⟨one_le_stableRank hA, stableRank_le_matrixRank A⟩

/-! ## Real/complex positivity bridge

The verified matrix-Laplace layer is complex.  The following bridge is proved
from quadratic forms; it is not an assumption hidden in the public API.
-/

/-- Shows that real dot mul vec is symmetric in its two arguments.

**Lean implementation helper.** -/
private lemma real_dot_mulVec_comm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x y : n → ℝ) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, mulVec]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hs : A j i = A i j :=
    (Matrix.isHermitian_iff_isSymm.mp hA).apply i j
  rw [hs]
  ring

/-- Positive semidefiniteness is preserved by entrywise complexification.

**Lean implementation helper.** -/
theorem complexifyMatrix_posSemidef {n : Type*} [Finite n]
    {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : (complexifyMatrix A).PosSemidef := by
  letI := Fintype.ofFinite n
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (complexifyMatrix_isHermitian hA.isHermitian) ?_
  intro z
  let xr : n → ℝ := fun i => (z i).re
  let xi : n → ℝ := fun i => (z i).im
  have hr : 0 ≤ xr ⬝ᵥ (A *ᵥ xr) := by
    simpa using hA.dotProduct_mulVec_nonneg xr
  have hi : 0 ≤ xi ⬝ᵥ (A *ᵥ xi) := by
    simpa using hA.dotProduct_mulVec_nonneg xi
  have hcross : xr ⬝ᵥ (A *ᵥ xi) = xi ⬝ᵥ (A *ᵥ xr) :=
    real_dot_mulVec_comm hA.isHermitian xr xi
  have hz : star z ⬝ᵥ (complexifyMatrix A *ᵥ z) =
      ((xr ⬝ᵥ (A *ᵥ xr) + xi ⬝ᵥ (A *ᵥ xi) : ℝ) : ℂ) := by
    rw [complexifyMatrix_mulVec]
    change (∑ i, star (z i) *
        (((A *ᵥ xr) i : ℂ) + Complex.I * ((A *ᵥ xi) i : ℂ))) = _
    have hcoord (i : n) :
        star (z i) *
            (((A *ᵥ xr) i : ℂ) + Complex.I * ((A *ᵥ xi) i : ℂ)) =
          ((xr i * (A *ᵥ xr) i + xi i * (A *ᵥ xi) i : ℝ) : ℂ) +
            Complex.I *
              ((xr i * (A *ᵥ xi) i - xi i * (A *ᵥ xr) i : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [xr, xi]
      · simp [xr, xi]
        ring
    rw [Finset.sum_congr rfl fun i _ => hcoord i,
      Finset.sum_add_distrib]
    push_cast
    simp only [dotProduct]
    rw [Finset.sum_add_distrib]
    have hzero :
        (∑ x, Complex.I *
          ((xr x : ℂ) * (A *ᵥ xi) x - (xi x : ℂ) * (A *ᵥ xr) x)) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      have hc := congrArg (fun r : ℝ => (r : ℂ)) hcross
      simp only [dotProduct] at hc
      push_cast at hc
      rw [hc, sub_self, mul_zero]
    rw [hzero, add_zero]
    push_cast
    rfl
  rw [hz]
  exact_mod_cast add_nonneg hr hi

/-- The real part of the trace of a complexified real matrix equals its real trace.

**Lean implementation helper.** -/
@[simp] theorem complexifyMatrix_trace_re (A : Matrix n n ℝ) :
    (complexifyMatrix A).trace.re = A.trace := by
  simp [complexifyMatrix, Matrix.trace]

/-- A real positive-semidefinite matrix satisfies `‖A‖ ≤ tr A`.

**Lean implementation helper.** -/
theorem matrixOpNorm_le_trace_of_posSemidef [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : matrixOpNorm A ≤ A.trace := by
  let hC : (complexifyMatrix A).PosSemidef := complexifyMatrix_posSemidef hA
  calc
    matrixOpNorm A = ‖complexifyMatrix A‖ :=
      (complexifyMatrix_opNorm A).symm
    _ = MatrixConcentration.lambdaMax hC.isHermitian :=
      MatrixConcentration.posSemidef_l2_opNorm_eq_lambdaMax hC
    _ ≤ (complexifyMatrix A).trace.re :=
      MatrixConcentration.lambdaMax_le_trace_re_of_posSemidef hC
    _ = A.trace := complexifyMatrix_trace_re A

/-- Bounds pos semidef eigenvalue by op norm.

**Lean implementation helper.** -/
private lemma posSemidef_eigenvalue_le_opNorm [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (i : n) :
    hA.isHermitian.eigenvalues i ≤ matrixOpNorm A := by
  let v : EuclideanSpace ℝ n := hA.isHermitian.eigenvectorBasis i
  have hvnorm : ‖v‖ = 1 := hA.isHermitian.eigenvectorBasis.orthonormal.1 i
  have hbound := A.l2_opNorm_mulVec v
  have heig := hA.isHermitian.mulVec_eigenvectorBasis i
  have heig' : A.toEuclideanLin v = hA.isHermitian.eigenvalues i • v := by
    change WithLp.toLp 2 (A *ᵥ (WithLp.ofLp v)) =
      hA.isHermitian.eigenvalues i • v
    simpa [v] using congrArg (WithLp.toLp 2) heig
  change hA.isHermitian.eigenvalues i ≤ ‖A‖
  rw [show (EuclideanSpace.equiv n ℝ).symm (A *ᵥ v) = A.toEuclideanLin v by rfl,
    heig', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (hA.eigenvalues_nonneg i), hvnorm, mul_one] at hbound
  simpa using hbound

/-- The trace is at most algebraic rank times operator norm for a PSD matrix.

**Lean implementation helper.** -/
theorem trace_le_rank_mul_opNorm_of_posSemidef [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.trace ≤ (A.rank : ℝ) * matrixOpNorm A := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  change (∑ i, hA.isHermitian.eigenvalues i) ≤ (A.rank : ℝ) * ‖A‖
  have hfilter : ∑ i, hA.isHermitian.eigenvalues i =
      ∑ i ∈ Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i ≠ 0),
        hA.isHermitian.eigenvalues i := by
    rw [Finset.sum_filter_of_ne]
    intro i _ hi
    exact hi
  rw [hfilter]
  have hsum := Finset.sum_le_card_nsmul
    (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i ≠ 0))
    (fun i => hA.isHermitian.eigenvalues i) ‖A‖
    (fun i _ => posSemidef_eigenvalue_le_opNorm hA i)
  have hcard :
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i ≠ 0)).card =
        A.rank := by
    rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  simpa [hcard, nsmul_eq_mul] using hsum

/-- Bounds one by effective rank.

**Lean implementation helper.** -/
theorem one_le_effectiveRank [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (hA0 : A ≠ 0) : 1 ≤ effectiveRank A := by
  have hn : 0 < matrixOpNorm A := by
    change 0 < ‖A‖
    exact norm_pos_iff.mpr hA0
  rw [effectiveRank, le_div_iff₀ hn, one_mul]
  exact matrixOpNorm_le_trace_of_posSemidef hA

/-- Bounds effective rank by rank.

**Lean implementation helper.** -/
theorem effectiveRank_le_rank [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : effectiveRank A ≤ A.rank := by
  by_cases hA0 : A = 0
  · subst A
    simp [effectiveRank]
  · have hn : 0 < matrixOpNorm A := by
      change 0 < ‖A‖
      exact norm_pos_iff.mpr hA0
    rw [effectiveRank, div_le_iff₀ hn]
    simpa [mul_comm] using trace_le_rank_mul_opNorm_of_posSemidef hA

/-- Stable rank is also bounded by Mathlib's algebraic matrix rank. This follows transparently
by viewing stable rank as the effective rank of the positive-semidefinite Gram matrix.

**Lean implementation helper.** -/
theorem stableRank_le_rank {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) :
    stableRank A ≤ A.rank := by
  rw [stableRank_eq_effectiveRank_gram]
  have h := effectiveRank_le_rank (gramMatrix_posSemidef A)
  simpa [gramMatrix, Matrix.rank_transpose_mul_self] using h

/-- The corrected stable-rank chain with Mathlib's algebraic rank.

**Lean implementation helper.** -/
theorem stableRank_rank_bounds {p q : ℕ}
    {A : Matrix (Fin p) (Fin q) ℝ} (hA : A ≠ 0) :
    1 ≤ stableRank A ∧ stableRank A ≤ A.rank :=
  ⟨one_le_stableRank hA, stableRank_le_rank A⟩

/-- The remaining dimension bound in the corresponding exercise.

**Lean implementation helper.** -/
theorem effectiveRank_le_card [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : effectiveRank A ≤ Fintype.card n :=
  (effectiveRank_le_rank hA).trans (by exact_mod_cast A.rank_le_card_width)

/-- Effective/stable rank identities, bounds, continuity, and support-subspace behavior.

**Book Remark 5.6.4.** -/
theorem exercise_5_29a [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    1 ≤ effectiveRank A ∧ effectiveRank A ≤ A.rank ∧
      A.rank ≤ Fintype.card n :=
  ⟨one_le_effectiveRank hA hA0, effectiveRank_le_rank hA,
    A.rank_le_card_width⟩

/-- Effective/stable rank identities, bounds, continuity, and support-subspace behavior.

**Book Remark 5.6.4.** -/
theorem exercise_5_29b {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosSemidef ∧ A.rank = 2 ∧ effectiveRank A < 1 + δ := by
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by norm_num)
  have hεδ : ε < δ :=
    (min_le_left (δ / 2) (1 / 2)).trans_lt (by linarith)
  let d : Fin 2 → ℝ := ![1, ε]
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal d
  have hpsd : A.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp [d, hε.le]
  have hrank : A.rank = 2 := by
    change (Matrix.diagonal d).rank = 2
    rw [Matrix.rank_diagonal]
    have hz : Fintype.card {i // d i = 0} = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun i => by
        rcases i with ⟨i, hi⟩
        fin_cases i <;> simp [d, hε.ne'] at hi⟩
    simp [hz]
  have htrace : A.trace = 1 + ε := by
    simp [A, d, Matrix.trace]
  have hnorm1 : 1 ≤ matrixOpNorm A := by
    change 1 ≤ matrixOpNorm (Matrix.diagonal d)
    rw [HDP.Chapter4.exercise_4_3b_diagonal]
    have h := norm_le_pi_norm d (0 : Fin 2)
    simpa [d] using h
  have hnormpos : 0 < matrixOpNorm A := lt_of_lt_of_le zero_lt_one hnorm1
  have heff : effectiveRank A ≤ 1 + ε := by
    rw [effectiveRank, htrace]
    exact (div_le_iff₀ hnormpos).2 (by
      have hnonneg : 0 ≤ 1 + ε := by positivity
      nlinarith)
  exact ⟨A, hpsd, hrank, heff.trans_lt (by linarith)⟩

end HDP

namespace HDP.Chapter5

open HDP Chapter4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A finite-law population second moment. This is the exact algebraic model used for the
finite-support case of the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def weightedSecondMoment {ι n : Type*} [Fintype ι] [Fintype n]
    (w : ι → ℝ) (x : ι → n → ℝ) : Matrix n n ℝ :=
  ∑ a, w a • Matrix.vecMulVec (x a) (x a)

/-- Applying a weighted second-moment matrix to `y` expands as the weighted sum of `⟨xₐ,y⟩ xₐ`.

**Lean implementation helper.** -/
lemma weightedSecondMoment_mulVec {ι n : Type*} [Fintype ι] [Fintype n]
    (w : ι → ℝ) (x : ι → n → ℝ) (y : n → ℝ) :
    weightedSecondMoment w x *ᵥ y =
      ∑ a, (w a * ∑ j, x a j * y j) • x a := by
  classical
  funext i
  simp only [weightedSecondMoment, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j, (∑ a, w a * (x a i * x a j)) * y j) =
        ∑ j, ∑ a, (w a * (x a i * x a j)) * y j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ j, (w a * (x a i * x a j)) * y j := Finset.sum_comm
    _ = ∑ a, (w a * ∑ j, x a j * y j) * x a i := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- If every atom lies in a `r`-dimensional subspace, then the population second moment has rank
at most `r`. No positivity or nonzero hypothesis is needed for this range argument.

**Book Exercise 5.29(d).** -/
theorem exercise_5_29d_finiteSupport {ι n : Type*} [Fintype ι] [Fintype n]
    (w : ι → ℝ) (x : ι → n → ℝ)
    (S : Submodule ℝ (n → ℝ)) (hx : ∀ a, x a ∈ S) :
    (weightedSecondMoment w x).rank ≤ Module.finrank ℝ S := by
  classical
  rw [Matrix.rank]
  apply Submodule.finrank_mono
  rintro _ ⟨y, rfl⟩
  rw [Matrix.mulVecLin_apply, weightedSecondMoment_mulVec]
  exact Submodule.sum_mem S fun a _ => S.smul_mem _ (hx a)

/-! ## The finite-sample second-moment estimator -/

namespace CovarianceAux

open MatrixConcentration

variable {d : Type*} [Fintype d]

/-- The rank-one matrix `x xᴴ` is positive semidefinite.

**Lean implementation helper.** -/
private lemma posSemidef_vecMulVec_star {d : Type*} [Finite d] (x : d → ℂ) :
    (vecMulVec x (star x)).PosSemidef := by
  letI := Fintype.ofFinite d
  classical
  have h : vecMulVec x (star x) =
      Matrix.replicateCol Unit x * (Matrix.replicateCol Unit x)ᴴ := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Establishes measurability of vec mul vec star.

**Lean implementation helper.** -/
private lemma measurable_vecMulVec_star {d : Type*} {x : Ω → d → ℂ}
    (hx : Measurable x) :
    Measurable fun ω => vecMulVec (x ω) (star (x ω)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  change Measurable fun ω => x ω i * (starRingEnd ℂ) (x ω j)
  exact ((measurable_pi_apply i).comp hx).mul
    (RCLike.continuous_conj.measurable.comp ((measurable_pi_apply j).comp hx))

/-- Every entry of the rank-one matrix `x x*` is bounded by `‖x‖₂²`.

**Lean implementation helper.** -/
private lemma abs_entry_vecMulVec_le (x : d → ℂ) (i j : d) :
    ‖vecMulVec x (star x) i j‖ ≤ MatrixConcentration.l2norm x ^ 2 := by
  classical
  have hentry : ‖vecMulVec x (star x) i j‖ = ‖x i‖ * ‖x j‖ := by
    rw [vecMulVec_apply, norm_mul]
    congr 1
    exact RCLike.norm_conj _
  rw [hentry]
  have hcoord : ∀ k, ‖x k‖ ≤ MatrixConcentration.l2norm x := fun k => by
    have hsq : ‖x k‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg ‖x i‖) (Finset.mem_univ k)
    rw [← MatrixConcentration.l2norm_sq] at hsq
    nlinarith [MatrixConcentration.l2norm_nonneg x, norm_nonneg (x k)]
  calc
    ‖x i‖ * ‖x j‖ ≤
        MatrixConcentration.l2norm x * MatrixConcentration.l2norm x :=
      mul_le_mul (hcoord i) (hcoord j) (norm_nonneg _)
        (MatrixConcentration.l2norm_nonneg x)
    _ = MatrixConcentration.l2norm x ^ 2 := (sq _).symm

/-- Derives mintegrable vec mul vec from bound.

**Lean implementation helper.** -/
private lemma mintegrable_vecMulVec_of_bound [IsProbabilityMeasure μ]
    {x : Ω → d → ℂ} (hx : Measurable x) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B) :
    MatrixConcentration.MIntegrable
      (fun ω => vecMulVec (x ω) (star (x ω))) μ := by
  classical
  refine MatrixConcentration.MIntegrable.of_bound
    (measurable_vecMulVec_star hx) B ?_
  filter_upwards [hB] with ω hω
  intro i j
  exact (abs_entry_vecMulVec_le (x ω) i j).trans hω

/-- Complex second-moment matrix used internally to transport the verified matrix-Bernstein
proof to real vectors.

**Lean implementation helper.** -/
noncomputable def covarianceMatrixC (x : Ω → d → ℂ) : Matrix d d ℂ :=
  MatrixConcentration.expectation μ fun ω => vecMulVec (x ω) (star (x ω))

/-- The complex covariance matrix is positive semidefinite.

**Lean implementation helper.** -/
private theorem posSemidef_covarianceMatrixC {d : Type*} [Finite d]
    [IsProbabilityMeasure μ]
    {x : Ω → d → ℂ}
    (hxx : MatrixConcentration.MIntegrable
      (fun ω => vecMulVec (x ω) (star (x ω))) μ) :
    (covarianceMatrixC (μ := μ) x).PosSemidef := by
  letI := Fintype.ofFinite d
  classical
  exact MatrixConcentration.posSemidef_expectation hxx
    (Filter.Eventually.of_forall fun ω => posSemidef_vecMulVec_star (x ω))

/-- An almost-sure bound `‖x‖₂² ≤ B` bounds the operator norm of the complex second-moment
matrix by `B`.

**Lean implementation helper.** -/
private theorem norm_covarianceMatrixC_le [DecidableEq d] [IsProbabilityMeasure μ]
    {x : Ω → d → ℂ} (hx : Measurable x) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B) :
    ‖covarianceMatrixC (μ := μ) x‖ ≤ B := by
  classical
  have hxx := mintegrable_vecMulVec_of_bound (μ := μ) hx hB
  have hm : Measurable fun ω => ‖vecMulVec (x ω) (star (x ω))‖ :=
    continuous_norm.measurable.comp (measurable_vecMulVec_star hx)
  have hnorm : ∀ᵐ ω ∂μ, ‖vecMulVec (x ω) (star (x ω))‖ ≤ B := by
    filter_upwards [hB] with ω hω
    rw [MatrixConcentration.l2_opNorm_vecMulVec_star_self]
    exact hω
  have hint : Integrable (fun ω => ‖vecMulVec (x ω) (star (x ω))‖) μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable B ?_
    filter_upwards [hnorm] with ω hω
    simpa using hω
  calc
    ‖covarianceMatrixC (μ := μ) x‖ ≤
        ∫ ω, ‖vecMulVec (x ω) (star (x ω))‖ ∂μ :=
      MatrixConcentration.norm_expectation_le hxx hint
    _ ≤ ∫ _, B ∂μ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω => norm_nonneg _) (integrable_const B) hnorm
    _ = B := by simp

variable {p s : ℕ}

/-- The complex empirical second-moment matrix, the average of the rank-one matrices `x_k x_k*`.

**Lean implementation helper.** -/
noncomputable def sampleCovarianceC (s : ℕ)
    (xs : Fin s → Ω → Fin p → ℂ) (ω : Ω) : Matrix (Fin p) (Fin p) ℂ :=
  (s : ℝ)⁻¹ • ∑ k, vecMulVec (xs k ω) (star (xs k ω))

/-- Matrix expectation commutes with multiplication by a real scalar.

**Lean implementation helper.** -/
private lemma expectation_smul_real
    {a b : Type*}
    (c : ℝ) (Z : Ω → Matrix a b ℂ) :
    MatrixConcentration.expectation μ (fun ω => c • Z ω) =
      c • MatrixConcentration.expectation μ Z := by
  ext i j
  change (∫ ω, (c • Z ω) i j ∂μ) =
    c • MatrixConcentration.expectation μ Z i j
  have h1 : (fun ω => (c • Z ω) i j) = fun ω => c • (Z ω i j) := rfl
  rw [h1, MeasureTheory.integral_smul]
  rfl

/-- Identically distributed complex random vectors have equal expected rank-one outer products.

**Lean implementation helper.** -/
private lemma expectation_outer_identDistrib
    {x y : Ω → Fin p → ℂ} (hid : IdentDistrib y x μ μ) :
    MatrixConcentration.expectation μ (fun ω => vecMulVec (y ω) (star (y ω))) =
      MatrixConcentration.expectation μ (fun ω => vecMulVec (x ω) (star (x ω))) := by
  ext i j
  rw [MatrixConcentration.expectation_apply,
    MatrixConcentration.expectation_apply]
  have hg : Measurable fun v : Fin p → ℂ => v i * (starRingEnd ℂ) (v j) :=
    (measurable_pi_apply i).mul
      (RCLike.continuous_conj.measurable.comp (measurable_pi_apply j))
  exact (hid.comp hg).integral_eq

/-- One centered, `1/s`-scaled rank-one summand in the complex empirical covariance error.

**Lean implementation helper.** -/
noncomputable def sampleCovSummandC (x : Ω → Fin p → ℂ) (s : ℕ)
    (xs : Fin s → Ω → Fin p → ℂ) (k : Fin s) (ω : Ω) :
    Matrix (Fin p) (Fin p) ℂ :=
  (s : ℝ)⁻¹ •
    (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrixC (μ := μ) x)

/-- The complex sample-covariance error decomposes as the sum of centered covariance summands.

**Lean implementation helper.** -/
private lemma sampleCov_decompositionC (hs : s ≠ 0)
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ} (ω : Ω) :
    sampleCovarianceC s xs ω - covarianceMatrixC (μ := μ) x =
      ∑ k, sampleCovSummandC (μ := μ) x s xs k ω := by
  rw [sampleCovarianceC]
  rw [show (∑ k, sampleCovSummandC (μ := μ) x s xs k ω) =
      (s : ℝ)⁻¹ • ∑ k,
        (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrixC (μ := μ) x) from
      (Finset.smul_sum).symm]
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul]
  rw [show ((s : ℝ)⁻¹ * (s : ℝ)) = 1 from by field_simp, one_smul]

/-- Each complex sample-covariance summand has zero matrix expectation.

**Lean implementation helper.** -/
private lemma sampleCov_summand_centeredC [IsProbabilityMeasure μ]
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hxs : ∀ k, MatrixConcentration.MIntegrable
      (fun ω => vecMulVec (xs k ω) (star (xs k ω))) μ) (k : Fin s) :
    MatrixConcentration.expectation μ (sampleCovSummandC (μ := μ) x s xs k) = 0 := by
  rw [show sampleCovSummandC (μ := μ) x s xs k = fun ω =>
      (s : ℝ)⁻¹ •
        (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrixC (μ := μ) x) from rfl]
  rw [expectation_smul_real, MatrixConcentration.expectation_sub (hxs k)
    (MatrixConcentration.MIntegrable.const _),
    MatrixConcentration.expectation_const, expectation_outer_identDistrib (hid k)]
  simp [covarianceMatrixC]

/-- Each complex sample-covariance summand has norm at most `2B/s` almost everywhere.

**Lean implementation helper.** -/
private theorem sampleCov_summand_norm_leC [IsProbabilityMeasure μ]
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hx : Measurable x)
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xs k ω) ^ 2 ≤ B)
    (k : Fin s) :
    ∀ᵐ ω ∂μ, ‖sampleCovSummandC (μ := μ) x s xs k ω‖ ≤ 2 * B / s := by
  have hA := norm_covarianceMatrixC_le (μ := μ) hx hB
  filter_upwards [hBs k] with ω hω
  rw [sampleCovSummandC, norm_smul]
  have h1 : ‖vecMulVec (xs k ω) (star (xs k ω)) -
      covarianceMatrixC (μ := μ) x‖ ≤ 2 * B := by
    calc
      _ ≤ ‖vecMulVec (xs k ω) (star (xs k ω))‖ +
          ‖covarianceMatrixC (μ := μ) x‖ := norm_sub_le _ _
      _ ≤ B + B := by
        exact add_le_add (by simpa [MatrixConcentration.l2_opNorm_vecMulVec_star_self]
          using hω) hA
      _ = 2 * B := by ring
  calc
    ‖(s : ℝ)⁻¹‖ * ‖vecMulVec (xs k ω) (star (xs k ω)) -
        covarianceMatrixC (μ := μ) x‖ ≤ ‖(s : ℝ)⁻¹‖ * (2 * B) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = 2 * B / s := by
      rw [Real.norm_of_nonneg (by positivity)]
      ring

/-- Multiplication by a nonnegative real scalar preserves Loewner order.

**Lean implementation helper.** -/
private lemma loewner_smul_le {a : Type*} [Finite a]
    {M N : Matrix a a ℂ} {c : ℝ} (hc : 0 ≤ c) (h : M ≤ N) : c • M ≤ c • N := by
  letI := Fintype.ofFinite a
  classical
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact MatrixConcentration.posSemidef_smul_nonneg h hc

/-- Establishes measurability of matrix mul.

**Lean implementation helper.** -/
private lemma measurable_matrix_mul
    {a b c : Type*} [Finite a] [Fintype b] [Finite c]
    {f : Ω → Matrix a b ℂ} {g : Ω → Matrix b c ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω * g ω := by
  letI := Fintype.ofFinite a
  letI := Fintype.ofFinite c
  classical
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  change Measurable fun ω => ∑ k, f ω i k * g ω k j
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_entry i k).comp hf).mul ((measurable_entry k j).comp hg)

/-- A real scalar multiple of a Hermitian matrix is Hermitian.

**Lean implementation helper.** -/
private lemma isHermitian_smul_real {a : Type*}
    {M : Matrix a a ℂ} (hM : M.IsHermitian) (c : ℝ) : (c • M).IsHermitian := by
  ext i j
  simpa [Complex.real_smul] using congrArg (fun z : ℂ => c * z) (hM.apply i j)

/-- A real scalar multiple of a matrix-integrable random matrix remains matrix-integrable.

**Lean implementation helper.** -/
private lemma MIntegrable.smul_real
    {a b : Type*}
    {Z : Ω → Matrix a b ℂ} (hZ : MatrixConcentration.MIntegrable Z μ) (c : ℝ) :
    MatrixConcentration.MIntegrable (fun ω => c • Z ω) μ := fun i j => by
  change Integrable (fun ω => c • Z ω i j) μ
  exact (hZ i j).smul c

/-- The square of the rank-one matrix `v vᴴ` is `‖v‖₂²` times `v vᴴ`.

**Lean implementation helper.** -/
private lemma vecMulVec_star_sq (v : Fin p → ℂ) :
    vecMulVec v (star v) * vecMulVec v (star v) =
      (MatrixConcentration.l2norm v ^ 2 : ℝ) • vecMulVec v (star v) := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have h : (star v ⬝ᵥ v) • star v =
      ((MatrixConcentration.l2norm v ^ 2 : ℝ) : ℂ) • star v := by
    rw [MatrixConcentration.dotProduct_star_self_eq]
  rw [h, Matrix.vecMulVec_smul]
  ext i j
  simp [Complex.real_smul]

/-- The expected square of each complex covariance summand is Loewner-bounded by `(B/s²)` times the population covariance.

**Lean implementation helper.** -/
private theorem sampleCov_summand_sq_leC [IsProbabilityMeasure μ]
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ) (k : Fin s) :
    MatrixConcentration.expectation μ (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω) ≤
      (B / (s : ℝ) ^ 2) • covarianceMatrixC (μ := μ) x := by
  let M : Ω → Matrix (Fin p) (Fin p) ℂ :=
    fun ω => vecMulVec (xs k ω) (star (xs k ω))
  have hMint : MatrixConcentration.MIntegrable M μ :=
    mintegrable_vecMulVec_of_bound (μ := μ) (hxsMeas k) (hBs k)
  have hEM : MatrixConcentration.expectation μ M = covarianceMatrixC (μ := μ) x :=
    expectation_outer_identDistrib (hid k)
  have hMM : ∀ ω, M ω * M ω =
      (MatrixConcentration.l2norm (xs k ω) ^ 2 : ℝ) • M ω :=
    fun ω => vecMulVec_star_sq (xs k ω)
  have hMMint : MatrixConcentration.MIntegrable (fun ω => M ω * M ω) μ := by
    refine MatrixConcentration.MIntegrable.of_bound
      (measurable_matrix_mul (measurable_vecMulVec_star (hxsMeas k))
        (measurable_vecMulVec_star (hxsMeas k))) (B * B) ?_
    filter_upwards [hBs k] with ω hω
    intro i j
    rw [hMM ω]
    change ‖(MatrixConcentration.l2norm (xs k ω) ^ 2 : ℝ) • M ω i j‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    have he := abs_entry_vecMulVec_le (xs k ω) i j
    nlinarith [norm_nonneg (M ω i j), MatrixConcentration.l2norm_nonneg (xs k ω)]
  have hEMM : MatrixConcentration.expectation μ (fun ω => M ω * M ω) ≤
      B • covarianceMatrixC (μ := μ) x := by
    have heq : MatrixConcentration.expectation μ (fun ω => B • M ω) =
        B • covarianceMatrixC (μ := μ) x := by
      rw [expectation_smul_real, hEM]
    rw [← heq]
    refine MatrixConcentration.expectation_loewner_mono hMMint
      (MIntegrable.smul_real hMint B) ?_
    filter_upwards [hBs k] with ω hω
    rw [hMM ω, Matrix.le_iff, ← sub_smul]
    exact MatrixConcentration.posSemidef_smul_nonneg
      (posSemidef_vecMulVec_star (xs k ω)) (by linarith)
  have hvar : MatrixConcentration.expectation μ (fun ω =>
      (M ω - covarianceMatrixC (μ := μ) x) *
        (M ω - covarianceMatrixC (μ := μ) x)) =
      MatrixConcentration.expectation μ (fun ω => M ω * M ω) -
        covarianceMatrixC (μ := μ) x * covarianceMatrixC (μ := μ) x := by
    have hv := MatrixConcentration.matrixVar_eq_sub hMint hMMint
    rw [MatrixConcentration.matrixVar, hEM] at hv
    exact hv
  have hA2 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤
      covarianceMatrixC (μ := μ) x * covarianceMatrixC (μ := μ) x := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact MatrixConcentration.posSemidef_sq
      (posSemidef_covarianceMatrixC
        (mintegrable_vecMulVec_of_bound (μ := μ) hx hB)).isHermitian
  have hsummand : (fun ω => sampleCovSummandC (μ := μ) x s xs k ω *
      sampleCovSummandC (μ := μ) x s xs k ω) = fun ω =>
      ((s : ℝ)⁻¹ * (s : ℝ)⁻¹) •
        ((M ω - covarianceMatrixC (μ := μ) x) *
          (M ω - covarianceMatrixC (μ := μ) x)) := by
    funext ω
    rw [sampleCovSummandC, smul_mul_smul_comm]
  rw [hsummand, expectation_smul_real, hvar]
  calc
    ((s : ℝ)⁻¹ * (s : ℝ)⁻¹) •
        (MatrixConcentration.expectation μ (fun ω => M ω * M ω) -
          covarianceMatrixC (μ := μ) x * covarianceMatrixC (μ := μ) x) ≤
      ((s : ℝ)⁻¹ * (s : ℝ)⁻¹) •
        (B • covarianceMatrixC (μ := μ) x -
          covarianceMatrixC (μ := μ) x * covarianceMatrixC (μ := μ) x) := by
      exact loewner_smul_le (by positivity) (sub_le_sub_right hEMM _)
    _ ≤ ((s : ℝ)⁻¹ * (s : ℝ)⁻¹) •
        (B • covarianceMatrixC (μ := μ) x) := by
      exact loewner_smul_le (by positivity) (sub_le_self _ hA2)
    _ = (B / (s : ℝ) ^ 2) • covarianceMatrixC (μ := μ) x := by
      rw [smul_smul]
      congr 1
      ring

/-- The norm of the summed covariance-summand second moments is at most `B ‖Σ‖ / s`.

**Lean implementation helper.** -/
private theorem sampleCov_norm_sum_sq_leC [IsProbabilityMeasure μ]
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hSqInt : ∀ k, MatrixConcentration.MIntegrable (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω) μ) :
    ‖∑ k, MatrixConcentration.expectation μ (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω)‖ ≤
      B * ‖covarianceMatrixC (μ := μ) x‖ / s := by
  have h0 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤
      ∑ k, MatrixConcentration.expectation μ (fun ω =>
        sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) := by
    rw [Matrix.nonneg_iff_posSemidef]
    refine Matrix.posSemidef_sum _ fun k _ => ?_
    refine MatrixConcentration.posSemidef_expectation (hSqInt k)
      (Filter.Eventually.of_forall fun ω => ?_)
    refine MatrixConcentration.posSemidef_sq ?_
    exact isHermitian_smul_real
      ((posSemidef_vecMulVec_star (xs k ω)).isHermitian.sub
        (posSemidef_covarianceMatrixC
          (mintegrable_vecMulVec_of_bound (μ := μ) hx hB)).isHermitian) _
  have hle : (∑ k, MatrixConcentration.expectation μ (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω)) ≤
      (B / (s : ℝ)) • covarianceMatrixC (μ := μ) x := by
    calc
      _ ≤ ∑ _k : Fin s, (B / (s : ℝ) ^ 2) •
          covarianceMatrixC (μ := μ) x :=
        Finset.sum_le_sum fun k _ =>
          sampleCov_summand_sq_leC (μ := μ) hx hxsMeas hB0 hB hBs hid k
      _ = (B / (s : ℝ)) • covarianceMatrixC (μ := μ) x := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul]
        congr 1
        by_cases hs : s = 0
        · subst s
          norm_num
        · field_simp
  have h0psd := Matrix.nonneg_iff_posSemidef.mp h0
  have hn := MatrixConcentration.norm_le_norm_of_loewner_le h0psd hle
  calc
    _ ≤ ‖(B / (s : ℝ)) • covarianceMatrixC (μ := μ) x‖ := hn
    _ = B * ‖covarianceMatrixC (μ := μ) x‖ / s := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      ring

/-- Establishes measurability of sample cov summand map c.

**Lean implementation helper.** -/
private lemma measurable_sampleCovSummand_mapC
    {x : Ω → Fin p → ℂ} :
    Measurable fun v : Fin p → ℂ =>
      (s : ℝ)⁻¹ •
        (vecMulVec v (star v) - covarianceMatrixC (μ := μ) x) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  change Measurable fun v : Fin p → ℂ =>
    (((s : ℝ)⁻¹ : ℝ) : ℂ) *
      (v i * (starRingEnd ℂ) (v j) - covarianceMatrixC (μ := μ) x i j)
  exact (((measurable_pi_apply i).mul
    (RCLike.continuous_conj.measurable.comp (measurable_pi_apply j))).sub_const _).const_mul _

/-- Establishes measurability of sample cov summand c.

**Lean implementation helper.** -/
private lemma measurable_sampleCovSummandC
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hxsMeas : ∀ k, Measurable (xs k)) (k : Fin s) :
    Measurable (sampleCovSummandC (μ := μ) x s xs k) :=
  measurable_sampleCovSummand_mapC.comp (hxsMeas k)

/-- Independent samples yield independent centered complex covariance summands.

**Lean implementation helper.** -/
private lemma sampleCov_indep_summandsC
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hind : iIndepFun xs μ) :
    iIndepFun (sampleCovSummandC (μ := μ) x s xs) μ :=
  hind.comp _ fun _ => measurable_sampleCovSummand_mapC

/-- The exact complex expected-error estimate underlying the corresponding theorem.

**Lean implementation helper.** -/
theorem sampleCovariance_expected_errorC [IsProbabilityMeasure μ]
    (hp : 0 < p) (hs : s ≠ 0)
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) :
    ∫ ω, ‖sampleCovarianceC s xs ω - covarianceMatrixC (μ := μ) x‖ ∂μ ≤
      Real.sqrt (2 * (B * ‖covarianceMatrixC (μ := μ) x‖) *
        Real.log (2 * p) / s) +
      2 * B * Real.log (2 * p) / (3 * s) := by
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  have hxx := mintegrable_vecMulVec_of_bound (μ := μ) hx hB
  have hHerm : ∀ k ω,
      (sampleCovSummandC (μ := μ) x s xs k ω).IsHermitian := fun k ω =>
    isHermitian_smul_real
      ((posSemidef_vecMulVec_star (xs k ω)).isHermitian.sub
        (posSemidef_covarianceMatrixC hxx).isHermitian) _
  have hmeas : ∀ k, Measurable (sampleCovSummandC (μ := μ) x s xs k) :=
    measurable_sampleCovSummandC hxsMeas
  have hnorm := sampleCov_summand_norm_leC (μ := μ) hx hB hBs
  have hSqInt : ∀ k, MatrixConcentration.MIntegrable (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω) μ := by
    intro k
    refine MatrixConcentration.MIntegrable.of_bound
      (measurable_matrix_mul (hmeas k) (hmeas k)) ((2 * B / s) ^ 2) ?_
    filter_upwards [hnorm k] with ω hω
    intro i j
    calc
      ‖(sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) i j‖
          ≤ ‖sampleCovSummandC (μ := μ) x s xs k ω *
              sampleCovSummandC (μ := μ) x s xs k ω‖ :=
            MatrixConcentration.norm_entry_le_l2_opNorm _ _ _
      _ ≤ ‖sampleCovSummandC (μ := μ) x s xs k ω‖ *
          ‖sampleCovSummandC (μ := μ) x s xs k ω‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ (2 * B / s) * (2 * B / s) := by
        exact mul_le_mul hω hω (norm_nonneg _) (by positivity)
      _ = (2 * B / s) ^ 2 := by ring
  have hcent : ∀ k,
      MatrixConcentration.expectation μ (sampleCovSummandC (μ := μ) x s xs k) = 0 :=
    fun k => sampleCov_summand_centeredC (μ := μ) hid
      (fun j => mintegrable_vecMulVec_of_bound (μ := μ) (hxsMeas j) (hBs j)) k
  have hbern := MatrixConcentration.matrix_bernstein_rect_expectation_ae
    (μ := μ) (S := sampleCovSummandC (μ := μ) x s xs)
    hmeas hnorm (by positivity) hcent (sampleCov_indep_summandsC hind)
  have hleft : (∑ k, MatrixConcentration.expectation μ (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        (sampleCovSummandC (μ := μ) x s xs k ω)ᴴ)) =
      ∑ k, MatrixConcentration.expectation μ (fun ω =>
        sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext ω
    rw [hHerm k ω]
  have hright : (∑ k, MatrixConcentration.expectation μ (fun ω =>
      (sampleCovSummandC (μ := μ) x s xs k ω)ᴴ *
        sampleCovSummandC (μ := μ) x s xs k ω)) =
      ∑ k, MatrixConcentration.expectation μ (fun ω =>
        sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext ω
    rw [hHerm k ω]
  rw [hleft, hright, max_self] at hbern
  have hvar := sampleCov_norm_sum_sq_leC (μ := μ) hx hxsMeas hB0 hB hBs hid hSqInt
  have hdecomp : (∫ ω, ‖∑ k, sampleCovSummandC (μ := μ) x s xs k ω‖ ∂μ) =
      ∫ ω, ‖sampleCovarianceC s xs ω - covarianceMatrixC (μ := μ) x‖ ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg norm (sampleCov_decompositionC (μ := μ) hs ω).symm
  rw [hdecomp] at hbern
  simp only [Fintype.card_fin] at hbern
  have hlog : 0 ≤ Real.log ((p : ℝ) + p) := by
    apply Real.log_nonneg
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hmono :
      2 * ‖∑ k, MatrixConcentration.expectation μ (fun ω =>
        sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω)‖ * Real.log ((p : ℝ) + p) ≤
      2 * (B * ‖covarianceMatrixC (μ := μ) x‖ / s) *
        Real.log ((p : ℝ) + p) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvar (by positivity)) hlog
  calc
    ∫ ω, ‖sampleCovarianceC s xs ω - covarianceMatrixC (μ := μ) x‖ ∂μ
        ≤ Real.sqrt (2 * ‖∑ k, MatrixConcentration.expectation μ (fun ω =>
            sampleCovSummandC (μ := μ) x s xs k ω *
              sampleCovSummandC (μ := μ) x s xs k ω)‖ *
              Real.log ((p : ℝ) + p)) +
          (2 * B / s) / 3 * Real.log ((p : ℝ) + p) := hbern
    _ ≤ Real.sqrt (2 * (B * ‖covarianceMatrixC (μ := μ) x‖ / s) *
            Real.log ((p : ℝ) + p)) +
          (2 * B / s) / 3 * Real.log ((p : ℝ) + p) :=
        add_le_add (Real.sqrt_le_sqrt hmono) le_rfl
    _ = Real.sqrt (2 * (B * ‖covarianceMatrixC (μ := μ) x‖) *
          Real.log (2 * p) / s) +
        2 * B * Real.log (2 * p) / (3 * s) := by
      rw [show ((p : ℝ) + p) = 2 * p by ring]
      congr 1 <;> ring_nf

/-- The complex sample-covariance error has tail at most `2p exp(-t² / (2(V+(2B/s)t/3)))`, where `V` is the summed second-moment norm.

**Lean implementation helper.** -/
theorem sampleCovariance_tailC [IsProbabilityMeasure μ]
    (hp : 0 < p) (hs : s ≠ 0)
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤
        ‖sampleCovarianceC s xs ω - covarianceMatrixC (μ := μ) x‖} ≤
      (2 * p : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, MatrixConcentration.expectation μ (fun ω =>
            sampleCovSummandC (μ := μ) x s xs k ω *
              sampleCovSummandC (μ := μ) x s xs k ω)‖ +
          (2 * B / s) * t / 3)) := by
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  have hxx := mintegrable_vecMulVec_of_bound (μ := μ) hx hB
  have hHerm : ∀ k ω,
      (sampleCovSummandC (μ := μ) x s xs k ω).IsHermitian := fun k ω =>
    isHermitian_smul_real
      ((posSemidef_vecMulVec_star (xs k ω)).isHermitian.sub
        (posSemidef_covarianceMatrixC hxx).isHermitian) _
  have hmeas : ∀ k, Measurable (sampleCovSummandC (μ := μ) x s xs k) :=
    measurable_sampleCovSummandC hxsMeas
  have hnorm := sampleCov_summand_norm_leC (μ := μ) hx hB hBs
  have hcent : ∀ k,
      MatrixConcentration.expectation μ (sampleCovSummandC (μ := μ) x s xs k) = 0 :=
    fun k => sampleCov_summand_centeredC (μ := μ) hid
      (fun j => mintegrable_vecMulVec_of_bound (μ := μ) (hxsMeas j) (hBs j)) k
  have htail := MatrixConcentration.matrix_bernstein_rect_tail_ae
    (μ := μ) (S := sampleCovSummandC (μ := μ) x s xs)
    hmeas hnorm (by positivity) hcent (sampleCov_indep_summandsC hind) ht
  have hleft : (∑ k, MatrixConcentration.expectation μ (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        (sampleCovSummandC (μ := μ) x s xs k ω)ᴴ)) =
      ∑ k, MatrixConcentration.expectation μ (fun ω =>
        sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext ω
    rw [hHerm k ω]
  have hright : (∑ k, MatrixConcentration.expectation μ (fun ω =>
      (sampleCovSummandC (μ := μ) x s xs k ω)ᴴ *
        sampleCovSummandC (μ := μ) x s xs k ω)) =
      ∑ k, MatrixConcentration.expectation μ (fun ω =>
        sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext ω
    rw [hHerm k ω]
  rw [hleft, hright, max_self] at htail
  have hset : {ω | t ≤ ‖∑ k, sampleCovSummandC (μ := μ) x s xs k ω‖} =
      {ω | t ≤ ‖sampleCovarianceC s xs ω - covarianceMatrixC (μ := μ) x‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [sampleCov_decompositionC (μ := μ) hs]
  rw [hset] at htail
  simp only [Fintype.card_fin] at htail
  rw [show (p : ℝ) + p = 2 * p by ring] at htail
  exact htail

/-- The variance proxy in the covariance Bernstein argument is bounded by `B ‖Sigma‖ / s`. This
public helper is the bridge from the exact tail theorem to the source's effective-rank and
dimension forms.

**Lean implementation helper.** -/
theorem sampleCovariance_variance_leC [IsProbabilityMeasure μ]
    {x : Ω → Fin p → ℂ} {xs : Fin s → Ω → Fin p → ℂ}
    (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ) :
    ‖∑ k, MatrixConcentration.expectation μ (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω)‖ ≤
      B * ‖covarianceMatrixC (μ := μ) x‖ / s := by
  have hmeas : ∀ k, Measurable (sampleCovSummandC (μ := μ) x s xs k) :=
    measurable_sampleCovSummandC hxsMeas
  have hnorm := sampleCov_summand_norm_leC (μ := μ) hx hB hBs
  have hSqInt : ∀ k, MatrixConcentration.MIntegrable (fun ω =>
      sampleCovSummandC (μ := μ) x s xs k ω *
        sampleCovSummandC (μ := μ) x s xs k ω) μ := by
    intro k
    refine MatrixConcentration.MIntegrable.of_bound
      (measurable_matrix_mul (hmeas k) (hmeas k)) ((2 * B / s) ^ 2) ?_
    filter_upwards [hnorm k] with ω hω
    intro i j
    calc
      ‖(sampleCovSummandC (μ := μ) x s xs k ω *
          sampleCovSummandC (μ := μ) x s xs k ω) i j‖
          ≤ ‖sampleCovSummandC (μ := μ) x s xs k ω *
              sampleCovSummandC (μ := μ) x s xs k ω‖ :=
            MatrixConcentration.norm_entry_le_l2_opNorm _ _ _
      _ ≤ ‖sampleCovSummandC (μ := μ) x s xs k ω‖ *
          ‖sampleCovSummandC (μ := μ) x s xs k ω‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ (2 * B / s) * (2 * B / s) :=
        mul_le_mul hω hω (norm_nonneg _) (by positivity)
      _ = (2 * B / s) ^ 2 := by ring
  exact sampleCov_norm_sum_sq_leC (μ := μ) hx hxsMeas hB0 hB hBs hid hSqInt

/-- A bounded complex second moment is positive semidefinite.

**Lean implementation helper.** -/
theorem covarianceMatrixC_posSemidef_of_bound [IsProbabilityMeasure μ]
    {x : Ω → d → ℂ} (hx : Measurable x) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (x ω) ^ 2 ≤ B) :
    (covarianceMatrixC (μ := μ) x).PosSemidef := by
  classical
  exact posSemidef_covarianceMatrixC
    (mintegrable_vecMulVec_of_bound (μ := μ) hx hB)

end CovarianceAux

/-- Coordinatewise embedding of a real Euclidean vector into complex space.

**Lean implementation helper.** -/
def complexifyEuclidean {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : Fin n → ℂ :=
  fun i => v i

/-- Establishes measurability of complexify euclidean.

**Lean implementation helper.** -/
private lemma measurable_complexifyEuclidean {n : ℕ} :
    Measurable (@complexifyEuclidean n) := by
  refine measurable_pi_lambda _ fun i => ?_
  change Measurable fun v : EuclideanSpace ℝ (Fin n) => (v i : ℂ)
  fun_prop

/-- Complexifying a real Euclidean vector preserves its Euclidean norm.

**Lean implementation helper.** -/
@[simp] lemma complexifyEuclidean_l2norm {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) :
    MatrixConcentration.l2norm (complexifyEuclidean v) = ‖v‖ := by
  change MatrixConcentration.l2norm (fun i => (v i : ℂ)) = ‖v‖
  simpa only using HDP.complex_l2norm_ofReal (fun i => v i)

/-- The complex rank-one outer product of a real vector equals the complexification of its real outer-product matrix.

**Lean implementation helper.** -/
private lemma complex_outer_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    vecMulVec (complexifyEuclidean v) (star (complexifyEuclidean v)) =
      HDP.complexifyMatrix (outerProductMatrix v) := by
  ext i j
  change (v i : ℂ) * star (v j : ℂ) = ((v i * v j : ℝ) : ℂ)
  simp

/-- Population (uncentered) second moment of a real random vector.

**Lean implementation helper.** -/
noncomputable def populationSecondMoment {n : ℕ}
    (x : Ω → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  HDP.realMatrixExpectation μ (fun ω => outerProductMatrix (x ω))

/-- Effective/stable rank identities, bounds, continuity, and support-subspace behavior.

**Book Remark 5.6.4.** -/
theorem exercise_5_29d [IsProbabilityMeasure μ] {n : ℕ}
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (S : Submodule ℝ (Fin n → ℝ))
    (hxS : ∀ᵐ ω ∂μ, (WithLp.ofLp (x ω) : Fin n → ℝ) ∈ S)
    (hint : ∀ i j, Integrable (fun ω => x ω i * x ω j) μ) :
    (populationSecondMoment (μ := μ) x).rank ≤ Module.finrank ℝ S := by
  rw [Matrix.rank]
  apply Submodule.finrank_mono
  rintro _ ⟨y, rfl⟩
  rw [Matrix.mulVecLin_apply]
  let f : Ω → (Fin n → ℝ) := fun ω =>
    (∑ j, x ω j * y j) • (WithLp.ofLp (x ω) : Fin n → ℝ)
  have hfcoord : ∀ i, Integrable (fun ω => f ω i) μ := by
    intro i
    have hsum : Integrable
        (fun ω => ∑ j : Fin n, (y j) * (x ω j * x ω i)) μ := by
      exact integrable_finsetSum _ fun j _ => (hint j i).const_mul (y j)
    convert hsum using 1
    funext ω
    simp only [f, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfint : Integrable f μ := Integrable.of_eval hfcoord
  have hfmem : ∀ᵐ ω ∂μ, f ω ∈ S := by
    filter_upwards [hxS] with ω hω
    exact S.smul_mem _ hω
  have hintegral : (∫ ω, f ω ∂μ) ∈ S :=
    S.convex.integral_mem S.closed_of_finiteDimensional hfmem hfint
  suffices populationSecondMoment (μ := μ) x *ᵥ y = ∫ ω, f ω ∂μ by
    rw [this]
    exact hintegral
  funext i
  rw [MeasureTheory.eval_integral hfcoord i]
  have hfapply : (fun ω => f ω i) =
      fun ω => ∑ j : Fin n, (x ω i * x ω j) * y j := by
    funext ω
    simp only [f, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfapply, integral_finsetSum]
  · simp only [populationSecondMoment, HDP.realMatrixExpectation_apply,
      Chapter4.outerProductMatrix, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const]
  · intro j _
    exact (hint i j).mul_const (y j)

/-- Squared/tracial reformulation of the boundedness assumption.

**Book (5.22).** -/
theorem populationSecondMoment_trace_eq_energy {n : ℕ}
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (hint : ∀ i, Integrable (fun ω => (x ω i) ^ 2) μ) :
    (populationSecondMoment (μ := μ) x).trace =
      ∫ ω, ‖x ω‖ ^ 2 ∂μ := by
  have hpop : populationSecondMoment (μ := μ) x =
      HDP.secondMomentMatrix x μ := by
    ext i j
    rfl
  rw [hpop]
  exact (HDP.Chapter3.secondMoment_norm_sq_eq_trace (μ := μ) x hint).symm

/-- The complex covariance of complexified real vectors is the complexification of their real population second moment.

**Lean implementation helper.** -/
private lemma covarianceMatrixC_complexifyEuclidean {n : ℕ}
    (x : Ω → EuclideanSpace ℝ (Fin n)) :
    CovarianceAux.covarianceMatrixC (μ := μ) (fun ω => complexifyEuclidean (x ω)) =
      HDP.complexifyMatrix (populationSecondMoment (μ := μ) x) := by
  rw [CovarianceAux.covarianceMatrixC, populationSecondMoment]
  calc
    MatrixConcentration.expectation μ (fun ω =>
        vecMulVec (complexifyEuclidean (x ω))
          (star (complexifyEuclidean (x ω)))) =
      MatrixConcentration.expectation μ (fun ω =>
        HDP.complexifyMatrix (outerProductMatrix (x ω))) := by
        congr 1
        funext ω
        exact complex_outer_eq (x ω)
    _ = HDP.complexifyMatrix
        (HDP.realMatrixExpectation μ (fun ω => outerProductMatrix (x ω))) :=
      HDP.expectation_complexifyMatrix _

/-- A bounded population second moment is positive semidefinite. This is proved by transporting
the verified complex expectation result back along entrywise complexification.

**Lean implementation helper.** -/
theorem populationSecondMoment_posSemidef [IsProbabilityMeasure μ] {n : ℕ}
    (x : Ω → EuclideanSpace ℝ (Fin n)) (hx : Measurable x) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ B) :
    (populationSecondMoment (μ := μ) x).PosSemidef := by
  let xc : Ω → Fin n → ℂ := fun ω => complexifyEuclidean (x ω)
  have hxc : Measurable xc := measurable_complexifyEuclidean.comp hx
  have hBc : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xc ω) ^ 2 ≤ B := by
    filter_upwards [hB] with ω hω
    simpa [xc] using hω
  have hc := CovarianceAux.covarianceMatrixC_posSemidef_of_bound
    (μ := μ) hxc hBc
  have hcov := covarianceMatrixC_complexifyEuclidean (μ := μ) x
  change CovarianceAux.covarianceMatrixC (μ := μ) xc =
    HDP.complexifyMatrix (populationSecondMoment (μ := μ) x) at hcov
  rw [hcov] at hc
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr ?_) ?_
  · have hpop : populationSecondMoment (μ := μ) x =
        HDP.secondMomentMatrix x μ := by
      ext i j
      rfl
    rw [hpop]
    exact HDP.secondMomentMatrix_transpose (μ := μ) x
  · intro v
    let z : Fin n → ℂ := fun i => v i
    have hz := hc.dotProduct_mulVec_nonneg z
    have heq : star z ⬝ᵥ (HDP.complexifyMatrix
        (populationSecondMoment (μ := μ) x) *ᵥ z) =
        ((v ⬝ᵥ (populationSecondMoment (μ := μ) x *ᵥ v) : ℝ) : ℂ) := by
      simp [z, dotProduct, Matrix.mulVec, HDP.complexifyMatrix]
    rw [heq] at hz
    simpa using (Complex.zero_le_real.mp hz)

/-- Complexifying a real empirical second-moment matrix agrees with forming the complex empirical
second moment of the complexified samples.

**Lean implementation helper.** -/
private lemma sampleCovarianceC_complexifyEuclidean_apply {m n : ℕ}
    (X : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    CovarianceAux.sampleCovarianceC m
        (fun i ω => complexifyEuclidean (X i ω)) ω =
      HDP.complexifyMatrix (sampleCovarianceMatrix (fun i => X i ω)) := by
  ext j k
  simp only [CovarianceAux.sampleCovarianceC, sampleCovarianceMatrix,
    HDP.sampleSecondMoment, HDP.complexifyMatrix, complexifyEuclidean,
    Matrix.vecMulVec, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
    Pi.star_apply, Matrix.map_apply]
  rw [Complex.real_smul]
  have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  simp only [hstar]
  norm_cast

/-- The exact variance statistic of the Hermitian covariance summands. It is kept explicit in
the sharp tail form of the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def covarianceBernsteinVariance {m n : ℕ}
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)) : ℝ :=
  let xc : Ω → Fin n → ℂ := fun ω => complexifyEuclidean (x ω)
  let xsc : Fin m → Ω → Fin n → ℂ :=
    fun k ω => complexifyEuclidean (xs k ω)
  ‖∑ k, MatrixConcentration.expectation μ (fun ω =>
      CovarianceAux.sampleCovSummandC (μ := μ) xc m xsc k ω *
      CovarianceAux.sampleCovSummandC (μ := μ) xc m xsc k ω)‖

/-- The exact covariance Bernstein variance is at most `B * ‖E XXᵀ‖ / m` under the almost-sure
squared-radius bound.

**Book (5.24).** -/
theorem covarianceBernsteinVariance_le [IsProbabilityMeasure μ]
    {m n : ℕ} (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    {B : ℝ} (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (hB0 : 0 ≤ B) (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, ‖xs k ω‖ ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ) :
    covarianceBernsteinVariance (μ := μ) x xs ≤
      B * HDP.matrixOpNorm (populationSecondMoment (μ := μ) x) / m := by
  let xc : Ω → Fin n → ℂ := fun ω => complexifyEuclidean (x ω)
  let xsc : Fin m → Ω → Fin n → ℂ :=
    fun k ω => complexifyEuclidean (xs k ω)
  have hxc : Measurable xc := measurable_complexifyEuclidean.comp hx
  have hxsc : ∀ k, Measurable (xsc k) := fun k =>
    measurable_complexifyEuclidean.comp (hxsMeas k)
  have hBc : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xc ω) ^ 2 ≤ B := by
    filter_upwards [hB] with ω hω
    simpa [xc] using hω
  have hBsc : ∀ k, ∀ᵐ ω ∂μ,
      MatrixConcentration.l2norm (xsc k ω) ^ 2 ≤ B := fun k => by
    filter_upwards [hBs k] with ω hω
    simpa [xsc] using hω
  have hidc : ∀ k, IdentDistrib (xsc k) xc μ μ := fun k =>
    (hid k).comp measurable_complexifyEuclidean
  have hmain := CovarianceAux.sampleCovariance_variance_leC
    (μ := μ) hxc hxsc hB0 hBc hBsc hidc
  have hcov := covarianceMatrixC_complexifyEuclidean (μ := μ) x
  change CovarianceAux.covarianceMatrixC (μ := μ) xc =
    HDP.complexifyMatrix (populationSecondMoment (μ := μ) x) at hcov
  rw [hcov, HDP.complexifyMatrix_opNorm] at hmain
  simpa [covarianceBernsteinVariance, xc, xsc, HDP.matrixOpNorm] using hmain

/-- The standard Bernstein threshold `√(2vs)+2Ls/3` yields an exponent at least `s`.

**Lean implementation helper.** -/
private lemma bernstein_threshold_rate {v L s : ℝ}
    (hv : 0 ≤ v) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hpos : 0 < v + L *
      (Real.sqrt (2 * v * s) + 2 * L * s / 3) / 3) :
    s ≤ (Real.sqrt (2 * v * s) + 2 * L * s / 3) ^ 2 / 2 /
      (v + L * (Real.sqrt (2 * v * s) + 2 * L * s / 3) / 3) := by
  let a := Real.sqrt (2 * v * s)
  let b := 2 * L * s / 3
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha2 : a ^ 2 = 2 * v * s := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  rw [le_div_iff₀ hpos]
  change s * (v + L * (a + b) / 3) ≤ (a + b) ^ 2 / 2
  have hbdef : 3 * b = 2 * L * s := by dsimp [b]; ring
  nlinarith [mul_nonneg ha hb]

/-- The iid bounded-vector assumptions used by Theorem 5.6.1.  Separating
them into a structure keeps the source-facing theorems readable and makes the
second-moment/covariance distinction explicit. -/
structure BoundedSecondMomentSample (m n : ℕ)
    (X : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (K : ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  independent : ProbabilityTheory.iIndepFun X μ
  identical : ∀ i j k,
    ∫ ω, X i ω j * X i ω k ∂μ = Sigma j k
  productIntegrable : ∀ i j k, Integrable (fun ω => X i ω j * X i ω k) μ
  sigma_psd : Sigma.PosSemidef
  K_one : 1 ≤ K
  bounded : ∀ i, ∀ᵐ ω ∂μ,
    ‖X i ω‖ ≤ K * Real.sqrt Sigma.trace

/-- The sample second moment is unbiased. It is a covariance estimator when the common
distribution is centered.

**Lean implementation helper.** -/
theorem sampleSecondMoment_expectation [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (X : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ) {K : ℝ}
    (h : BoundedSecondMomentSample (μ := μ) m n X Sigma K) (j k : Fin n) :
    ∫ ω, sampleCovarianceMatrix (fun i => X i ω) j k ∂μ = Sigma j k := by
  exact sampleCovarianceMatrix_unbiased_entry hm X Sigma
    h.productIntegrable h.identical j k

/-- A source-neutral exact Bernstein endpoint for sample second moments. The variance and
envelope remain the actual computable statistics; subsequent lemmas bound them using the
hypotheses of the corresponding theorem.

**Book Theorem 5.6.1.** -/
theorem sampleSecondMoment_bernstein_exact [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (X : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (S : Fin m → Ω → Matrix (Fin n) (Fin n) ℝ)
    {L : ℝ} (hmeas : ∀ i, Measurable (S i))
    (hbd : ∀ i ω, ‖S i ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ i, HDP.realMatrixExpectation μ (S i) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hsum : ∀ ω, ∑ i, S i ω =
      sampleCovarianceMatrix (fun i => X i ω) - Sigma) :
    ∫ ω, ‖sampleCovarianceMatrix (fun i => X i ω) - Sigma‖ ∂μ ≤
      Real.sqrt (2 * matrixVariance (μ := μ) S * Real.log (2 * n)) +
        L / 3 * Real.log (2 * n) := by
  have h := matrixBernsteinExpectation (μ := μ) S hmeas hbd hL hcent hind
  simp only [Fintype.card_fin] at h
  rw [show (n : ℝ) + n = 2 * n by ring] at h
  simpa [hsum] using h

/-- For iid bounded vectors, the expected operator-norm error of the empirical second moment is
controlled by the dimension logarithm, the almost-sure squared-radius bound, and the population
operator norm. This theorem is proved by complexifying the real matrices and applying the
verified rectangular matrix Bernstein theorem; no invertibility of the population matrix is
assumed.

**Book Theorem 5.6.1.** -/
theorem boundedCovarianceEstimation_expected [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 0 < n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    {B : ℝ} (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (hB0 : 0 ≤ B) (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, ‖xs k ω‖ ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) :
    ∫ ω, HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) -
          populationSecondMoment (μ := μ) x) ∂μ ≤
      Real.sqrt (2 * (B * HDP.matrixOpNorm
        (populationSecondMoment (μ := μ) x)) * Real.log (2 * n) / m) +
      2 * B * Real.log (2 * n) / (3 * m) := by
  let xc : Ω → Fin n → ℂ := fun ω => complexifyEuclidean (x ω)
  let xsc : Fin m → Ω → Fin n → ℂ :=
    fun k ω => complexifyEuclidean (xs k ω)
  have hxc : Measurable xc := measurable_complexifyEuclidean.comp hx
  have hxsc : ∀ k, Measurable (xsc k) := fun k =>
    measurable_complexifyEuclidean.comp (hxsMeas k)
  have hBc : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xc ω) ^ 2 ≤ B := by
    filter_upwards [hB] with ω hω
    simpa [xc] using hω
  have hBsc : ∀ k, ∀ᵐ ω ∂μ,
      MatrixConcentration.l2norm (xsc k ω) ^ 2 ≤ B := fun k => by
    filter_upwards [hBs k] with ω hω
    simpa [xsc] using hω
  have hidc : ∀ k, IdentDistrib (xsc k) xc μ μ := fun k => by
    exact (hid k).comp measurable_complexifyEuclidean
  have hindc : iIndepFun xsc μ :=
    hind.comp (fun _ => complexifyEuclidean) fun _ => measurable_complexifyEuclidean
  have hmain := CovarianceAux.sampleCovariance_expected_errorC
    (μ := μ) hn hm hxc hxsc hB0 hBc hBsc hidc hindc
  have hcov := covarianceMatrixC_complexifyEuclidean (μ := μ) x
  change CovarianceAux.covarianceMatrixC (μ := μ) xc =
    HDP.complexifyMatrix (populationSecondMoment (μ := μ) x) at hcov
  rw [hcov] at hmain
  have hsamp : ∀ ω,
      CovarianceAux.sampleCovarianceC m xsc ω =
        HDP.complexifyMatrix (sampleCovarianceMatrix (fun k => xs k ω)) := by
    intro ω
    exact sampleCovarianceC_complexifyEuclidean_apply (X := xs) ω
  simp_rw [hsamp, ← HDP.complexifyMatrix_sub,
    HDP.complexifyMatrix_opNorm] at hmain
  simpa [HDP.matrixOpNorm] using hmain

/-- High-probability covariance estimation with the exact Bernstein variance statistic. The
preceding square-moment computation bounds this statistic by `B * ‖Sigma‖ / m`, yielding the
usual effective-rank corollaries without any invertibility assumption.

**Book Exercise 5.26.** -/
theorem boundedCovarianceEstimation_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 0 < n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    {B t : ℝ} (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (hB0 : 0 ≤ B) (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, ‖xs k ω‖ ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) -
          populationSecondMoment (μ := μ) x)} ≤
      (2 * n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (covarianceBernsteinVariance (μ := μ) x xs +
          (2 * B / m) * t / 3)) := by
  let xc : Ω → Fin n → ℂ := fun ω => complexifyEuclidean (x ω)
  let xsc : Fin m → Ω → Fin n → ℂ :=
    fun k ω => complexifyEuclidean (xs k ω)
  have hxc : Measurable xc := measurable_complexifyEuclidean.comp hx
  have hxsc : ∀ k, Measurable (xsc k) := fun k =>
    measurable_complexifyEuclidean.comp (hxsMeas k)
  have hBc : ∀ᵐ ω ∂μ, MatrixConcentration.l2norm (xc ω) ^ 2 ≤ B := by
    filter_upwards [hB] with ω hω
    simpa [xc] using hω
  have hBsc : ∀ k, ∀ᵐ ω ∂μ,
      MatrixConcentration.l2norm (xsc k ω) ^ 2 ≤ B := fun k => by
    filter_upwards [hBs k] with ω hω
    simpa [xsc] using hω
  have hidc : ∀ k, IdentDistrib (xsc k) xc μ μ := fun k =>
    (hid k).comp measurable_complexifyEuclidean
  have hindc : iIndepFun xsc μ :=
    hind.comp (fun _ => complexifyEuclidean) fun _ => measurable_complexifyEuclidean
  have hmain := CovarianceAux.sampleCovariance_tailC
    (μ := μ) hn hm hxc hxsc hB0 hBc hBsc hidc hindc ht
  have hcov := covarianceMatrixC_complexifyEuclidean (μ := μ) x
  change CovarianceAux.covarianceMatrixC (μ := μ) xc =
    HDP.complexifyMatrix (populationSecondMoment (μ := μ) x) at hcov
  rw [hcov] at hmain
  have hsamp : ∀ ω,
      CovarianceAux.sampleCovarianceC m xsc ω =
        HDP.complexifyMatrix (sampleCovarianceMatrix (fun k => xs k ω)) := by
    intro ω
    exact sampleCovarianceC_complexifyEuclidean_apply (X := xs) ω
  simp_rw [hsamp, ← HDP.complexifyMatrix_sub,
    HDP.complexifyMatrix_opNorm] at hmain
  simpa [HDP.matrixOpNorm, covarianceBernsteinVariance, xc, xsc] using hmain

/-- For `n ≥ 2`, the failure probability at the displayed Bernstein threshold is at most `2 exp
(-u)`. This is the direct probability statement used to obtain equation (5.29).

**Book Exercise 5.26.** -/
theorem boundedCovarianceEstimation_uTail [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 2 ≤ n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    {B u : ℝ} (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (hBpos : 0 < B) (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, ‖xs k ω‖ ^ 2 ≤ B)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ)
    (hSigma0 : populationSecondMoment (μ := μ) x ≠ 0) (hu : 0 ≤ u) :
    let Sigma := populationSecondMoment (μ := μ) x
    let s := Real.log n + u
    let threshold :=
      Real.sqrt (2 * (B * HDP.matrixOpNorm Sigma / m) * s) +
        4 * B * s / (3 * m)
    μ.real {ω | threshold ≤ HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma)} ≤
      2 * Real.exp (-u) := by
  dsimp only
  let Sigma := populationSecondMoment (μ := μ) x
  let V : ℝ := B * HDP.matrixOpNorm Sigma / m
  let L : ℝ := 2 * B / m
  let s : ℝ := Real.log n + u
  let t : ℝ := Real.sqrt (2 * V * s) + 2 * L * s / 3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hlogpos : 0 < Real.log n := Real.log_pos (by
    exact_mod_cast (show 1 < n by omega))
  have hs : 0 < s := by dsimp [s]; linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hN : 0 < HDP.matrixOpNorm Sigma := by
    change 0 < ‖Sigma‖
    exact norm_pos_iff.mpr hSigma0
  have hV : 0 < V := by dsimp [V]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have ht : 0 < t := by
    dsimp [t]
    have : 0 < 2 * V * s := by positivity
    positivity
  have hvar := covarianceBernsteinVariance_le (μ := μ) x xs hx hxsMeas
    hBpos.le hB hBs hid
  change covarianceBernsteinVariance (μ := μ) x xs ≤ V at hvar
  let v := covarianceBernsteinVariance (μ := μ) x xs
  have hv : 0 ≤ v := by
    dsimp [v, covarianceBernsteinVariance]
    exact norm_nonneg _
  have hdenV : 0 < V + L * t / 3 := by positivity
  have hden : 0 < v + L * t / 3 := by positivity
  have hrateV : s ≤ t ^ 2 / 2 / (V + L * t / 3) := by
    simpa [t] using bernstein_threshold_rate hV.le hL.le hs.le hdenV
  have hdenle : v + L * t / 3 ≤ V + L * t / 3 := by linarith
  have hfrac : t ^ 2 / 2 / (V + L * t / 3) ≤
      t ^ 2 / 2 / (v + L * t / 3) := by
    rw [div_le_div_iff₀ hdenV hden]
    exact mul_le_mul_of_nonneg_left hdenle (by positivity)
  have hrate : s ≤ t ^ 2 / 2 / (v + L * t / 3) := hrateV.trans hfrac
  have htail := boundedCovarianceEstimation_tail (μ := μ)
    (lt_of_lt_of_le (by norm_num) hn) hm x xs hx hxsMeas hBpos.le hB hBs hid hind ht.le
  change μ.real {ω | t ≤ HDP.matrixOpNorm
      (sampleCovarianceMatrix (fun k => xs k ω) - Sigma)} ≤
    (2 * n : ℝ) * Real.exp (-(t ^ 2) / 2 /
      (v + L * t / 3)) at htail
  calc
    μ.real {ω |
        Real.sqrt (2 * (B * HDP.matrixOpNorm Sigma / m) *
            (Real.log n + u)) +
          4 * B * (Real.log n + u) / (3 * m) ≤
          HDP.matrixOpNorm
            (sampleCovarianceMatrix (fun k => xs k ω) - Sigma)}
        = μ.real {ω | t ≤ HDP.matrixOpNorm
            (sampleCovarianceMatrix (fun k => xs k ω) - Sigma)} := by
          congr 2
          funext ω
          dsimp [t, V, L, s]
          ring_nf
    _ ≤ (2 * n : ℝ) * Real.exp (-(t ^ 2) / 2 /
          (v + L * t / 3)) := htail
    _ ≤ (2 * n : ℝ) * Real.exp (-s) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        rw [show -(t ^ 2) / 2 / (v + L * t / 3) =
          -(t ^ 2 / 2 / (v + L * t / 3)) by ring]
        exact neg_le_neg hrate
      · positivity
    _ = 2 * Real.exp (-u) := by
      dsimp [s]
      rw [show -(Real.log (n : ℝ) + u) = -Real.log (n : ℝ) + -u by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hn0]
      field_simp

/-- The effective-rank form of the corresponding theorem. The nonzero hypothesis is exactly what
is needed to rewrite `tr Sigma` as `effectiveRank Sigma * ‖Sigma‖`; the zero covariance case is
already covered by `boundedCovarianceEstimation_expected`.

**Book Remark 5.6.3.** -/
theorem boundedCovarianceEstimation_effectiveRank [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 0 < n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ) {K : ℝ}
    (hpop : populationSecondMoment (μ := μ) x = Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma0 : Sigma ≠ 0)
    (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (_hK : 0 ≤ K)
    (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ K ^ 2 * Sigma.trace)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, ‖xs k ω‖ ^ 2 ≤ K ^ 2 * Sigma.trace)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) :
    ∫ ω, HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma) ∂μ ≤
      (Real.sqrt (2 * K ^ 2 * HDP.effectiveRank Sigma *
          Real.log (2 * n) / m) +
        2 * K ^ 2 * HDP.effectiveRank Sigma *
          Real.log (2 * n) / (3 * m)) * HDP.matrixOpNorm Sigma := by
  have htrace0 : 0 ≤ Sigma.trace := hSigma.trace_nonneg
  have hmain := boundedCovarianceEstimation_expected (μ := μ) hn hm x xs
    hx hxsMeas (mul_nonneg (sq_nonneg K) htrace0) hB hBs hid hind
  rw [hpop] at hmain
  have hN : 0 ≤ HDP.matrixOpNorm Sigma := HDP.matrixOpNorm_nonneg _
  have hN0 : HDP.matrixOpNorm Sigma ≠ 0 := by
    change ‖Sigma‖ ≠ 0
    exact norm_ne_zero_iff.mpr hSigma0
  have hr : 0 ≤ HDP.effectiveRank Sigma := by
    rw [HDP.effectiveRank]
    exact div_nonneg htrace0 hN
  have hlog : 0 ≤ Real.log (2 * n) := by
    apply Real.log_nonneg
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have htrace : Sigma.trace =
      HDP.effectiveRank Sigma * HDP.matrixOpNorm Sigma := by
    rw [HDP.effectiveRank]
    field_simp
  let a := 2 * K ^ 2 * HDP.effectiveRank Sigma * Real.log (2 * n) / m
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hsqrt : Real.sqrt (a * HDP.matrixOpNorm Sigma ^ 2) =
      Real.sqrt a * HDP.matrixOpNorm Sigma := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hN)).mp
    rw [Real.sq_sqrt (mul_nonneg ha (sq_nonneg _)), mul_pow,
      Real.sq_sqrt ha]
  calc
    ∫ ω, HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma) ∂μ
        ≤ Real.sqrt (2 * (K ^ 2 * Sigma.trace * HDP.matrixOpNorm Sigma) *
            Real.log (2 * n) / m) +
          2 * (K ^ 2 * Sigma.trace) * Real.log (2 * n) / (3 * m) := hmain
    _ = (Real.sqrt a +
          2 * K ^ 2 * HDP.effectiveRank Sigma *
            Real.log (2 * n) / (3 * m)) * HDP.matrixOpNorm Sigma := by
      rw [htrace]
      rw [show 2 * (K ^ 2 *
          (HDP.effectiveRank Sigma * HDP.matrixOpNorm Sigma) *
          HDP.matrixOpNorm Sigma) * Real.log (2 * n) / m =
          a * HDP.matrixOpNorm Sigma ^ 2 by simp [a]; ring]
      rw [hsqrt]
      ring
    _ = (Real.sqrt (2 * K ^ 2 * HDP.effectiveRank Sigma *
            Real.log (2 * n) / m) +
          2 * K ^ 2 * HDP.effectiveRank Sigma *
            Real.log (2 * n) / (3 * m)) * HDP.matrixOpNorm Sigma := by
      rfl

/-- With probability at least `1 - 2 exp (-u)`, the error is below the displayed threshold. The
theorem is written as an equivalent failure-probability upper bound, which avoids subtraction in
`Measure.real`.

**Book Remark 5.6.5.** -/
theorem covarianceEstimation_effectiveRank_uTail [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 2 ≤ n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ) {K u : ℝ}
    (hpop : populationSecondMoment (μ := μ) x = Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma0 : Sigma ≠ 0)
    (hK : 1 ≤ K) (hx : Measurable x) (hxsMeas : ∀ k, Measurable (xs k))
    (hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ K ^ 2 * Sigma.trace)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, ‖xs k ω‖ ^ 2 ≤ K ^ 2 * Sigma.trace)
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) (hu : 0 ≤ u) :
    let s := Real.log n + u
    let threshold :=
      (Real.sqrt (2 * K ^ 2 * HDP.effectiveRank Sigma * s / m) +
        4 * K ^ 2 * HDP.effectiveRank Sigma * s / (3 * m)) *
          HDP.matrixOpNorm Sigma
    μ.real {ω | threshold ≤ HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma)} ≤
      2 * Real.exp (-u) := by
  dsimp only
  have hN : 0 < HDP.matrixOpNorm Sigma := by
    change 0 < ‖Sigma‖
    exact norm_pos_iff.mpr hSigma0
  have htrace : 0 < Sigma.trace :=
    lt_of_lt_of_le hN (HDP.matrixOpNorm_le_trace_of_posSemidef hSigma)
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hBpos : 0 < K ^ 2 * Sigma.trace := by positivity
  have hmain := boundedCovarianceEstimation_uTail (μ := μ) hn hm x xs hx hxsMeas
    hBpos hB hBs hid hind (hpop.trans_ne hSigma0) hu
  rw [hpop] at hmain
  let s : ℝ := Real.log n + u
  have hs : 0 ≤ s := by
    dsimp [s]
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n by omega))
    linarith
  have hr : 0 ≤ HDP.effectiveRank Sigma := by
    rw [HDP.effectiveRank]
    positivity
  have htraceEq : Sigma.trace =
      HDP.effectiveRank Sigma * HDP.matrixOpNorm Sigma := by
    rw [HDP.effectiveRank]
    field_simp
  let a : ℝ := 2 * K ^ 2 * HDP.effectiveRank Sigma * s / m
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsqrt : Real.sqrt (a * HDP.matrixOpNorm Sigma ^ 2) =
      Real.sqrt a * HDP.matrixOpNorm Sigma := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hN.le)).mp
    rw [Real.sq_sqrt (mul_nonneg ha (sq_nonneg _)), mul_pow,
      Real.sq_sqrt ha]
  have hthreshold :
      Real.sqrt (2 * (K ^ 2 * Sigma.trace * HDP.matrixOpNorm Sigma / m) * s) +
          4 * (K ^ 2 * Sigma.trace) * s / (3 * m) =
        (Real.sqrt (2 * K ^ 2 * HDP.effectiveRank Sigma * s / m) +
          4 * K ^ 2 * HDP.effectiveRank Sigma * s / (3 * m)) *
            HDP.matrixOpNorm Sigma := by
    rw [htraceEq]
    rw [show 2 * (K ^ 2 *
        (HDP.effectiveRank Sigma * HDP.matrixOpNorm Sigma) *
          HDP.matrixOpNorm Sigma / m) * s =
        a * HDP.matrixOpNorm Sigma ^ 2 by dsimp [a]; ring,
      hsqrt]
    dsimp [a]
    ring
  simpa [s, hthreshold] using hmain

/-- The hypothesis is the source's literal energy-normalized bound. The displayed constant is
explicit: the source's unspecified absolute `C` may be taken large enough to dominate `sqrt 2`
and `2/3`.

**Book Theorem 5.6.1.** -/
theorem generalCovarianceEstimation [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 2 ≤ n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)) {K : ℝ}
    (hK : 1 ≤ K) (hx : Measurable x)
    (hxsMeas : ∀ k, Measurable (xs k))
    (hint : ∀ i, Integrable (fun ω => (x ω i) ^ 2) μ)
    (hbound : ∀ᵐ ω ∂μ,
      ‖x ω‖ ≤ K * Real.sqrt (∫ z, ‖x z‖ ^ 2 ∂μ))
    (hboundSamples : ∀ k, ∀ᵐ ω ∂μ,
      ‖xs k ω‖ ≤ K * Real.sqrt (∫ z, ‖x z‖ ^ 2 ∂μ))
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ) :
    let Sigma := populationSecondMoment (μ := μ) x
    ∫ ω, HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma) ∂μ ≤
      (Real.sqrt (2 * K ^ 2 * n * Real.log (2 * n) / m) +
        2 * K ^ 2 * n * Real.log (2 * n) / (3 * m)) *
          HDP.matrixOpNorm Sigma := by
  dsimp only
  let Sigma := populationSecondMoment (μ := μ) x
  let energy : ℝ := ∫ z, ‖x z‖ ^ 2 ∂μ
  have htrace : Sigma.trace = energy := by
    exact populationSecondMoment_trace_eq_energy (μ := μ) x hint
  have henergy0 : 0 ≤ energy := by
    dsimp [energy]
    exact integral_nonneg fun _ => sq_nonneg _
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hB : ∀ᵐ ω ∂μ, ‖x ω‖ ^ 2 ≤ K ^ 2 * Sigma.trace := by
    filter_upwards [hbound] with ω hω
    rw [htrace]
    calc
      ‖x ω‖ ^ 2 ≤ (K * Real.sqrt energy) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (Real.sqrt_nonneg _))).2 hω
      _ = K ^ 2 * energy := by rw [mul_pow, Real.sq_sqrt henergy0]
  have hBs : ∀ k, ∀ᵐ ω ∂μ,
      ‖xs k ω‖ ^ 2 ≤ K ^ 2 * Sigma.trace := fun k => by
    filter_upwards [hboundSamples k] with ω hω
    rw [htrace]
    calc
      ‖xs k ω‖ ^ 2 ≤ (K * Real.sqrt energy) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (Real.sqrt_nonneg _))).2 hω
      _ = K ^ 2 * energy := by rw [mul_pow, Real.sq_sqrt henergy0]
  have hSigma : Sigma.PosSemidef :=
    populationSecondMoment_posSemidef (μ := μ) x hx hB
  have hmain := boundedCovarianceEstimation_expected (μ := μ)
    (lt_of_lt_of_le (by norm_num) hn) hm x xs hx hxsMeas
    (mul_nonneg (sq_nonneg K) hSigma.trace_nonneg) hB hBs hid hind
  change ∫ ω, HDP.matrixOpNorm
      (sampleCovarianceMatrix (fun k => xs k ω) - Sigma) ∂μ ≤ _ at hmain
  have hN : 0 ≤ HDP.matrixOpNorm Sigma := HDP.matrixOpNorm_nonneg _
  have htr : Sigma.trace ≤ (n : ℝ) * HDP.matrixOpNorm Sigma := by
    calc
      Sigma.trace ≤ (Sigma.rank : ℝ) * HDP.matrixOpNorm Sigma :=
        HDP.trace_le_rank_mul_opNorm_of_posSemidef hSigma
      _ ≤ (n : ℝ) * HDP.matrixOpNorm Sigma := by
        gcongr
        have hrank : Sigma.rank ≤ n := by
          simpa using Sigma.rank_le_card_width
        exact_mod_cast hrank
  have hlog : 0 ≤ Real.log (2 * n) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  let a : ℝ := 2 * K ^ 2 * n * Real.log (2 * n) / m
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsqrt : Real.sqrt (a * HDP.matrixOpNorm Sigma ^ 2) =
      Real.sqrt a * HDP.matrixOpNorm Sigma := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hN)).mp
    rw [Real.sq_sqrt (mul_nonneg ha (sq_nonneg _)), mul_pow,
      Real.sq_sqrt ha]
  calc
    ∫ ω, HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma) ∂μ
        ≤ Real.sqrt (2 * (K ^ 2 * Sigma.trace * HDP.matrixOpNorm Sigma) *
            Real.log (2 * n) / m) +
          2 * (K ^ 2 * Sigma.trace) * Real.log (2 * n) / (3 * m) := hmain
    _ ≤ Real.sqrt (a * HDP.matrixOpNorm Sigma ^ 2) +
          (2 * K ^ 2 * n * Real.log (2 * n) / (3 * m)) *
            HDP.matrixOpNorm Sigma := by
      apply add_le_add
      · apply Real.sqrt_le_sqrt
        calc
          2 * (K ^ 2 * Sigma.trace * HDP.matrixOpNorm Sigma) *
                Real.log (2 * n) / m =
              (2 * Real.log (2 * n)) *
                (K ^ 2 * Sigma.trace * HDP.matrixOpNorm Sigma) / m := by ring
          _ ≤ (2 * Real.log (2 * n)) *
                (K ^ 2 * ((n : ℝ) * HDP.matrixOpNorm Sigma) *
                  HDP.matrixOpNorm Sigma) / m := by
            gcongr
          _ = a * HDP.matrixOpNorm Sigma ^ 2 := by
            dsimp [a]
            ring
      · calc
          2 * (K ^ 2 * Sigma.trace) * Real.log (2 * n) / (3 * m) =
              (2 * K ^ 2 * Real.log (2 * n) / (3 * m)) * Sigma.trace := by ring
          _ ≤ (2 * K ^ 2 * Real.log (2 * n) / (3 * m)) *
                ((n : ℝ) * HDP.matrixOpNorm Sigma) := by
            gcongr
          _ = (2 * K ^ 2 * n * Real.log (2 * n) / (3 * m)) *
                HDP.matrixOpNorm Sigma := by ring
    _ = (Real.sqrt (2 * K ^ 2 * n * Real.log (2 * n) / m) +
          2 * K ^ 2 * n * Real.log (2 * n) / (3 * m)) *
            HDP.matrixOpNorm Sigma := by
      rw [hsqrt]
      dsimp [a]
      ring

/-- The scalar inequality behind the corresponding remark. The factor `8` is a safe explicit
absolute constant: under the displayed sample-size condition the square-root term is at most `ε
/ 2`, and so is the lower-order linear term.

**Lean implementation helper.** -/
private lemma generalCovariance_sampleComplexity_numerics
    {m n : ℕ} (hn : 2 ≤ n) (hm : m ≠ 0)
    {K ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : 8 * K ^ 2 * ε⁻¹ ^ 2 * (n : ℝ) * Real.log (2 * n) ≤ (m : ℝ)) :
    Real.sqrt (2 * K ^ 2 * n * Real.log (2 * n) / m) +
        2 * K ^ 2 * n * Real.log (2 * n) / (3 * m) ≤ ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hscaled :
      8 * K ^ 2 * (n : ℝ) * Real.log (2 * n) ≤ ε ^ 2 * (m : ℝ) := by
    calc
      8 * K ^ 2 * (n : ℝ) * Real.log (2 * n) =
          ε ^ 2 * (8 * K ^ 2 * ε⁻¹ ^ 2 * (n : ℝ) * Real.log (2 * n)) := by
            field_simp [hε0.ne']
      _ ≤ ε ^ 2 * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hsize (sq_nonneg ε)
  let q : ℝ := K ^ 2 * (n : ℝ) * Real.log (2 * n) / m
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq : q ≤ ε ^ 2 / 8 := by
    rw [div_le_iff₀ hmR]
    nlinarith
  have hsqrt : Real.sqrt (2 * q) ≤ ε / 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith
  have hlinear : 2 * q / 3 ≤ ε / 2 := by
    have heprod : 0 ≤ ε * (1 - ε) :=
      mul_nonneg hε0.le (sub_nonneg.mpr hε1)
    nlinarith
  have hfirst : 2 * K ^ 2 * (n : ℝ) * Real.log (2 * n) / m = 2 * q := by
    dsimp [q]
    ring
  have hsecond :
      2 * K ^ 2 * (n : ℝ) * Real.log (2 * n) / (3 * m) = 2 * q / 3 := by
    dsimp [q]
    ring
  rw [hfirst, hsecond]
  linarith

/-- For `0 < ε ≤ 1`, the explicit sufficient condition `m ≥ 8 K² ε⁻² n log (2n)` makes the
expected operator-norm error at most `ε ‖Σ‖`, with no auxiliary numerical-error premise. Here
`ε⁻²` is written as `(ε⁻¹)²` in Lean.

**Book Remark 5.6.2.** -/
theorem remark_5_6_2 [IsProbabilityMeasure μ]
    {m n : ℕ} (hn : 2 ≤ n) (hm : m ≠ 0)
    (x : Ω → EuclideanSpace ℝ (Fin n))
    (xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)) {K ε : ℝ}
    (hK : 1 ≤ K) (hx : Measurable x)
    (hxsMeas : ∀ k, Measurable (xs k))
    (hint : ∀ i, Integrable (fun ω => (x ω i) ^ 2) μ)
    (hbound : ∀ᵐ ω ∂μ,
      ‖x ω‖ ≤ K * Real.sqrt (∫ z, ‖x z‖ ^ 2 ∂μ))
    (hboundSamples : ∀ k, ∀ᵐ ω ∂μ,
      ‖xs k ω‖ ≤ K * Real.sqrt (∫ z, ‖x z‖ ^ 2 ∂μ))
    (hid : ∀ k, IdentDistrib (xs k) x μ μ)
    (hind : iIndepFun xs μ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : 8 * K ^ 2 * ε⁻¹ ^ 2 * (n : ℝ) * Real.log (2 * n) ≤ (m : ℝ)) :
    let Sigma := populationSecondMoment (μ := μ) x
    ∫ ω, HDP.matrixOpNorm
        (sampleCovarianceMatrix (fun k => xs k ω) - Sigma) ∂μ ≤
      ε * HDP.matrixOpNorm Sigma := by
  dsimp only
  have hmain := generalCovarianceEstimation (μ := μ) hn hm x xs hK hx
    hxsMeas hint hbound hboundSamples hid hind
  have hscalar := generalCovariance_sampleComplexity_numerics
    hn hm hε0 hε1 hsize
  exact hmain.trans (mul_le_mul_of_nonneg_right hscalar
    (HDP.matrixOpNorm_nonneg _))

/-- Algebraic sample-complexity transfer: once the relative error bound is at most `epsilon`,
the estimator has the advertised accuracy.

**Book Remark 5.6.2.** -/
theorem covariance_sampleComplexity_transfer
    {m n : ℕ} (X : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ) {epsilon rhs : ℝ}
    (hrhs : rhs ≤ epsilon * HDP.matrixOpNorm Sigma)
    (hmain : ∫ ω, HDP.matrixOpNorm
      (sampleCovarianceMatrix (fun i => X i ω) - Sigma) ∂μ ≤ rhs) :
    ∫ ω, HDP.matrixOpNorm
      (sampleCovarianceMatrix (fun i => X i ω) - Sigma) ∂μ ≤
        epsilon * HDP.matrixOpNorm Sigma :=
  hmain.trans hrhs

/-! The next two deterministic declarations are the reusable mathematical
content of Exercises 5.27--5.28.  Concrete finite probability-space witnesses
can instantiate them without adding assumptions to the covariance theorem. -/

/-- If all observed vectors vanish while the population second moment is nonzero, the
operator-norm estimation error is exactly `‖Sigma‖`. This is the failure mechanism behind the
rare-atom counterexample.

**Lean implementation helper.** -/
theorem zeroSample_covarianceFailure {m n : ℕ}
    (X : Fin m → EuclideanSpace ℝ (Fin n))
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hzero : ∀ i, X i = 0) :
    HDP.matrixOpNorm (sampleCovarianceMatrix X - Sigma) =
      HDP.matrixOpNorm Sigma := by
  have hsample : sampleCovarianceMatrix X = 0 := by
    ext j k
    simp [sampleCovarianceMatrix_apply, hzero]
  rw [hsample, zero_sub, HDP.matrixOpNorm_neg]

/-- Product law used by the rare-atom counterexample in the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def rareAtomProductMeasure (m : ℕ) (r : Set.Icc (0 : ℝ) 1) :
    Measure (Fin m → Bool) :=
  Measure.pi fun _ : Fin m => bernoulliMeasure true false r

noncomputable instance rareAtomProductMeasure_isProbability
    {m : ℕ} {r : Set.Icc (0 : ℝ) 1} :
    IsProbabilityMeasure (rareAtomProductMeasure m r) := by
  unfold rareAtomProductMeasure
  infer_instance

/-- For `m` independent rare Bernoulli atoms of rate `r`, the all-false outcome has probability `(1-r)^m`.

**Lean implementation helper.** -/
@[simp] theorem rareAtomProductMeasure_allFalse_real {m : ℕ}
    (r : Set.Icc (0 : ℝ) 1) :
    (rareAtomProductMeasure m r).real
        ({fun _ : Fin m => false} : Set (Fin m → Bool)) =
      (1 - (r : ℝ)) ^ m := by
  rw [measureReal_def, rareAtomProductMeasure, Measure.pi_singleton]
  simp

/-- The one-dimensional rare atom: zero with high probability and `1/sqrt r` on the rare
coordinate.

**Lean implementation helper.** -/
noncomputable def rareAtomVector (r : Set.Icc (0 : ℝ) 1) (b : Bool) :
    EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun _ => if b then (Real.sqrt (r : ℝ))⁻¹ else 0

/-- The vector associated with the false rare-atom outcome is zero.

**Lean implementation helper.** -/
@[simp] lemma rareAtomVector_false (r : Set.Icc (0 : ℝ) 1) :
    rareAtomVector r false = 0 := by
  apply WithLp.ofLp_injective
  funext i
  simp [rareAtomVector]

/-- The rare atom is isotropic in one dimension: its population second moment is exactly the
identity whenever the rare probability is positive.

**Book Remark 5.6.6.** -/
theorem rareAtomVector_secondMoment (r : Set.Icc (0 : ℝ) 1)
    (hr : 0 < (r : ℝ)) :
    populationSecondMoment
        (μ := bernoulliMeasure true false r) (rareAtomVector r) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i
  fin_cases j
  rw [populationSecondMoment, HDP.realMatrixExpectation_apply,
    integral_bernoulliMeasure]
  simp [outerProductMatrix, rareAtomVector]
  have hs : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  field_simp [hs]
  exact (Real.sq_sqrt hr.le).symm

/-- Without a boundedness assumption, covariance estimation can fail badly.

**Book Remark 5.6.6.** -/
theorem exercise_5_27_rareAtom_failure {m : ℕ}
    (r : Set.Icc (0 : ℝ) 1) :
    (rareAtomProductMeasure m r).real
        ({fun _ : Fin m => false} : Set (Fin m → Bool)) ≤
      (rareAtomProductMeasure m r).real
        {G | 1 ≤ HDP.matrixOpNorm
          (sampleCovarianceMatrix (fun i => rareAtomVector r (G i)) -
            (1 : Matrix (Fin 1) (Fin 1) ℝ))} := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro G hG
  have hG0 : G = fun _ : Fin m => false := Set.mem_singleton_iff.mp hG
  subst G
  have hfail := zeroSample_covarianceFailure
    (X := fun _ : Fin m => rareAtomVector r false)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun i => rareAtomVector_false r)
  change 1 ≤ HDP.matrixOpNorm
    (sampleCovarianceMatrix (fun _ : Fin m => rareAtomVector r false) - 1)
  rw [hfail]
  simp [HDP.matrixOpNorm]

/-- 27 with the product probability evaluated explicitly.

**Book Exercise 5.27.** -/
theorem exercise_5_27_rareAtom_failure_probability {m : ℕ}
    (r : Set.Icc (0 : ℝ) 1) :
    (1 - (r : ℝ)) ^ m ≤
      (rareAtomProductMeasure m r).real
        {G | 1 ≤ HDP.matrixOpNorm
          (sampleCovarianceMatrix (fun i => rareAtomVector r (G i)) -
            (1 : Matrix (Fin 1) (Fin 1) ℝ))} := by
  rw [← rareAtomProductMeasure_allFalse_real]
  exact exercise_5_27_rareAtom_failure r

/-- The logarithmic dimension factor is a genuine price and can be necessary.

**Book Remark 5.4.12.** -/
theorem missingCoordinate_error_ge_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (hcol : ∀ i, A i j = 0) :
    1 ≤ HDP.matrixOpNorm (A - 1) := by
  let e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single j 1)
  have he : ‖e‖ = 1 := by simp [e]
  have hmul : (A - 1).toEuclideanLin e = -e := by
    apply WithLp.ofLp_injective
    funext i
    simp [e, Matrix.toLpLin_apply, hcol]
  have h := HDP.norm_mulVec_le (A - 1) e
  change ‖(A - 1).toEuclideanLin e‖ ≤
    HDP.matrixOpNorm (A - 1) * ‖e‖ at h
  rw [hmul, norm_neg, he, mul_one] at h
  exact h

/-! ## Exercise 5.28: the coupon-collector obstruction -/

/-- The zero-one product indicating that coupon `j` is absent from every sample `G i`.

**Lean implementation helper.** -/
noncomputable def couponMissingIndicator {m n : ℕ}
    (j : Fin n) (G : Fin m → Fin n) : ℝ :=
  ∏ i, if G i = j then 0 else 1

/-- The number of coupon values that do not occur in the sample, written as a real-valued sum of
missing indicators.

**Lean implementation helper.** -/
noncomputable def couponMissingCount {m n : ℕ}
    (G : Fin m → Fin n) : ℝ :=
  ∑ j, couponMissingIndicator j G

/-- Among `n` coordinates, exactly `n-1` avoid a fixed coordinate `j`.

**Lean implementation helper.** -/
@[simp] lemma sum_avoid_one {n : ℕ} (j : Fin n) :
    (∑ a : Fin n, if a = j then (0 : ℝ) else 1) = n - 1 := by
  classical
  rw [show (∑ a : Fin n, if a = j then (0 : ℝ) else 1) =
      ∑ a : Fin n, if a ≠ j then (1 : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a = j <;> simp [h]]
  rw [Finset.sum_boole]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Fin.pos_iff_nonempty.mpr ⟨j⟩))]
  norm_num

/-- Exactly `(n-1)^m` length-`m` coupon samples omit a fixed coupon.

**Lean implementation helper.** -/
lemma sum_couponMissingIndicator {m n : ℕ} (j : Fin n) :
    (∑ G : Fin m → Fin n, couponMissingIndicator j G) =
      (n - 1 : ℝ) ^ m := by
  classical
  simp only [couponMissingIndicator]
  calc
    (∑ x : Fin m → Fin n, ∏ i, if x i = j then (0 : ℝ) else 1) =
        ∏ _i : Fin m, ∑ a : Fin n, if a = j then (0 : ℝ) else 1 :=
      (Fintype.prod_sum (fun _i : Fin m => fun a : Fin n =>
        if a = j then (0 : ℝ) else 1)).symm
    _ = ∏ _i : Fin m, (n - 1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_avoid_one j
    _ = (n - 1 : ℝ) ^ m := by simp

/-- When `j ≠ k`, exactly `n-2` coordinates avoid both fixed coordinates.

**Lean implementation helper.** -/
@[simp] lemma sum_avoid_two {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    (∑ a : Fin n,
      (if a = j then (0 : ℝ) else 1) *
        (if a = k then (0 : ℝ) else 1)) = n - 2 := by
  classical
  rw [show (∑ a : Fin n,
      (if a = j then (0 : ℝ) else 1) *
        (if a = k then (0 : ℝ) else 1)) =
      ∑ a : Fin n, if a ≠ j ∧ a ≠ k then (1 : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro a _
    by_cases haj : a = j <;> by_cases hak : a = k <;> simp [haj, hak]]
  rw [Finset.sum_boole]
  have hfilter : (Finset.univ.filter fun a : Fin n => a ≠ j ∧ a ≠ k) =
      (Finset.univ.erase j).erase k := by
    ext a
    simp [and_comm]
  rw [hfilter]
  have hkmem : k ∈ Finset.univ.erase j := by simp [Ne.symm hjk]
  rw [Finset.card_erase_of_mem hkmem,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin]
  have hn2 : 2 ≤ n := by
    have hcard : ({j, k} : Finset (Fin n)).card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [Finset.card_pair, hjk] using hcard
  rw [Nat.sub_sub, Nat.cast_sub hn2]
  norm_num

/-- Exactly `(n-2)^m` length-`m` coupon samples omit two distinct fixed coupons.

**Lean implementation helper.** -/
lemma sum_couponMissingIndicator_mul {m n : ℕ} {j k : Fin n}
    (hjk : j ≠ k) :
    (∑ G : Fin m → Fin n,
      couponMissingIndicator j G * couponMissingIndicator k G) =
      (n - 2 : ℝ) ^ m := by
  classical
  simp only [couponMissingIndicator, ← Finset.prod_mul_distrib]
  calc
    (∑ x : Fin m → Fin n, ∏ i,
        (if x i = j then (0 : ℝ) else 1) *
          (if x i = k then (0 : ℝ) else 1)) =
        ∏ _i : Fin m, ∑ a : Fin n,
          (if a = j then (0 : ℝ) else 1) *
            (if a = k then (0 : ℝ) else 1) :=
      (Fintype.prod_sum (fun _i : Fin m => fun a : Fin n =>
        (if a = j then (0 : ℝ) else 1) *
          (if a = k then (0 : ℝ) else 1))).symm
    _ = ∏ _i : Fin m, (n - 2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_avoid_two hjk
    _ = (n - 2 : ℝ) ^ m := by simp

/-- Identifies coupon missing indicator with ite.

**Lean implementation helper.** -/
lemma couponMissingIndicator_eq_ite {m n : ℕ}
    (j : Fin n) (G : Fin m → Fin n) :
    couponMissingIndicator j G =
      if (∀ i, G i ≠ j) then 1 else 0 := by
  classical
  by_cases h : ∀ i, G i ≠ j
  · simp [couponMissingIndicator, h]
  · rw [if_neg h]
    unfold couponMissingIndicator
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [ite_eq_left_iff, one_ne_zero, imp_false]
    simpa using hi

/-- The zero-one missing-coupon indicator is idempotent under squaring.

**Lean implementation helper.** -/
@[simp] lemma couponMissingIndicator_sq {m n : ℕ}
    (j : Fin n) (G : Fin m → Fin n) :
    couponMissingIndicator j G ^ 2 = couponMissingIndicator j G := by
  rw [couponMissingIndicator_eq_ite]
  split <;> norm_num

/-- Summing the number of missing coupons over all samples gives `n(n-1)^m`.

**Lean implementation helper.** -/
lemma sum_couponMissingCount {m n : ℕ} :
    (∑ G : Fin m → Fin n, couponMissingCount G) =
      n * (n - 1 : ℝ) ^ m := by
  classical
  simp only [couponMissingCount]
  rw [Finset.sum_comm]
  simp [sum_couponMissingIndicator]

/-- For a fixed coupon, summing joint missing indicators over all comparison coupons gives `(n-1)^m + (n-1)(n-2)^m`.

**Lean implementation helper.** -/
lemma sum_couponMissingIndicator_mul_all {m n : ℕ} (j : Fin n) :
    (∑ k : Fin n, ∑ G : Fin m → Fin n,
      couponMissingIndicator j G * couponMissingIndicator k G) =
      (n - 1 : ℝ) ^ m + (n - 1 : ℝ) * (n - 2 : ℝ) ^ m := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun k : Fin n => ∑ G : Fin m → Fin n,
      couponMissingIndicator j G * couponMissingIndicator k G)
    (Finset.mem_univ j)]
  have hoff : (∑ k ∈ Finset.univ.erase j,
      ∑ G : Fin m → Fin n,
        couponMissingIndicator j G * couponMissingIndicator k G) =
      (n - 1 : ℝ) * (n - 2 : ℝ) ^ m := by
    calc
      (∑ k ∈ Finset.univ.erase j,
          ∑ G : Fin m → Fin n,
            couponMissingIndicator j G * couponMissingIndicator k G) =
          ∑ _k ∈ Finset.univ.erase j, (n - 2 : ℝ) ^ m := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_couponMissingIndicator_mul
          ((Finset.mem_erase.mp hk).1.symm)
      _ = (n - 1 : ℝ) * (n - 2 : ℝ) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
          Fintype.card_fin]
        have hn : 1 ≤ n := Nat.succ_le_iff.mpr
          (Fin.pos_iff_nonempty.mpr ⟨j⟩)
        rw [Nat.cast_sub hn]
        norm_num
  have hdiag : (∑ G : Fin m → Fin n,
      couponMissingIndicator j G * couponMissingIndicator j G) =
      (n - 1 : ℝ) ^ m := by
    calc
      (∑ G : Fin m → Fin n,
          couponMissingIndicator j G * couponMissingIndicator j G) =
          ∑ G : Fin m → Fin n, couponMissingIndicator j G := by
        apply Finset.sum_congr rfl
        intro G _
        rw [← pow_two, couponMissingIndicator_sq]
      _ = (n - 1 : ℝ) ^ m := sum_couponMissingIndicator j
  rw [hoff, hdiag, add_comm]

/-- The second moment sum of the missing-coupon count equals `n((n-1)^m + (n-1)(n-2)^m)`.

**Lean implementation helper.** -/
lemma sum_couponMissingCount_sq {m n : ℕ} :
    (∑ G : Fin m → Fin n, couponMissingCount G ^ 2) =
      n * ((n - 1 : ℝ) ^ m +
        (n - 1 : ℝ) * (n - 2 : ℝ) ^ m) := by
  classical
  calc
    (∑ G : Fin m → Fin n, couponMissingCount G ^ 2) =
        ∑ G : Fin m → Fin n, ∑ j : Fin n, ∑ k : Fin n,
          couponMissingIndicator j G * couponMissingIndicator k G := by
      apply Finset.sum_congr rfl
      intro G _
      simp only [couponMissingCount, pow_two, Finset.sum_mul_sum]
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ G : Fin m → Fin n,
          couponMissingIndicator j G * couponMissingIndicator k G := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n,
        ((n - 1 : ℝ) ^ m + (n - 1 : ℝ) * (n - 2 : ℝ) ^ m) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_couponMissingIndicator_mul_all j
    _ = n * ((n - 1 : ℝ) ^ m +
        (n - 1 : ℝ) * (n - 2 : ℝ) ^ m) := by simp; ring

/-- Shows that coupon missing indicator is nonnegative.

**Lean implementation helper.** -/
lemma couponMissingIndicator_nonneg {m n : ℕ}
    (j : Fin n) (G : Fin m → Fin n) :
    0 ≤ couponMissingIndicator j G := by
  rw [couponMissingIndicator_eq_ite]
  split <;> norm_num

/-- Shows that coupon missing count is nonnegative.

**Lean implementation helper.** -/
lemma couponMissingCount_nonneg {m n : ℕ} (G : Fin m → Fin n) :
    0 ≤ couponMissingCount G := by
  unfold couponMissingCount
  exact Finset.sum_nonneg fun j _ => couponMissingIndicator_nonneg j G

/-- Identifies coupon missing count with card.

**Lean implementation helper.** -/
lemma couponMissingCount_eq_card {m n : ℕ} (G : Fin m → Fin n) :
    couponMissingCount G =
      ((Finset.univ.filter fun j : Fin n => ∀ i, G i ≠ j).card : ℝ) := by
  classical
  unfold couponMissingCount
  simp_rw [couponMissingIndicator_eq_ite]
  rw [Finset.sum_boole]

/-- Characterizes coupon missing count positivity by an equivalent condition.

**Lean implementation helper.** -/
lemma couponMissingCount_pos_iff {m n : ℕ} (G : Fin m → Fin n) :
    0 < couponMissingCount G ↔ ∃ j, ∀ i, G i ≠ j := by
  classical
  rw [couponMissingCount_eq_card]
  norm_cast
  simp only [Finset.card_pos, Finset.filter_nonempty_iff,
    Finset.mem_univ, true_and]

/-- Samples that miss at least one coordinate.

**Lean implementation helper.** -/
noncomputable def couponMissingSamples (m n : ℕ) :
    Finset (Fin m → Fin n) :=
  Finset.univ.filter fun G => 0 < couponMissingCount G

/-- Cauchy--Schwarz bounds the square of the total missing count by the number of deficient samples times its second-moment sum.

**Lean implementation helper.** -/
lemma couponMissingSamples_card_cauchy {m n : ℕ} :
    (n * (n - 1 : ℝ) ^ m) ^ 2 ≤
      (couponMissingSamples m n).card *
        (n * ((n - 1 : ℝ) ^ m +
          (n - 1 : ℝ) * (n - 2 : ℝ) ^ m)) := by
  classical
  let s := couponMissingSamples m n
  have hsum : (∑ G ∈ s, couponMissingCount G) =
      ∑ G : Fin m → Fin n, couponMissingCount G := by
    apply Finset.sum_subset (by
      intro G hG
      exact Finset.mem_univ G)
    intro G _ hG
    have hnot : ¬ 0 < couponMissingCount G := by
      simpa [s, couponMissingSamples] using hG
    exact le_antisymm (not_lt.mp hnot) (couponMissingCount_nonneg G)
  have hsumsq : (∑ G ∈ s, couponMissingCount G ^ 2) =
      ∑ G : Fin m → Fin n, couponMissingCount G ^ 2 := by
    apply Finset.sum_subset (by
      intro G hG
      exact Finset.mem_univ G)
    intro G _ hG
    have hnot : ¬ 0 < couponMissingCount G := by
      simpa [s, couponMissingSamples] using hG
    have hz : couponMissingCount G = 0 :=
      le_antisymm (not_lt.mp hnot) (couponMissingCount_nonneg G)
    simp [hz]
  have hc := sq_sum_le_card_mul_sum_sq
    (s := s) (f := couponMissingCount)
  rw [hsum, hsumsq, sum_couponMissingCount, sum_couponMissingCount_sq] at hc
  simpa [s] using hc

/-- The two-coupon omission term satisfies `n^m(n-2)^m ≤ (n-1)^(2m)`.

**Lean implementation helper.** -/
private lemma coupon_pair_moment_bound {m n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ m * (n - 2 : ℝ) ^ m ≤ (n - 1 : ℝ) ^ (2 * m) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : 0 ≤ (n - 2 : ℝ) := by linarith
  have hbase : (n : ℝ) * (n - 2 : ℝ) ≤ (n - 1 : ℝ) ^ 2 := by
    nlinarith
  calc
    (n : ℝ) ^ m * (n - 2 : ℝ) ^ m =
        ((n : ℝ) * (n - 2 : ℝ)) ^ m := (mul_pow _ _ _).symm
    _ ≤ ((n - 1 : ℝ) ^ 2) ^ m := by
      exact pow_le_pow_left₀ (mul_nonneg hn0 hn2) hbase m
    _ = (n - 1 : ℝ) ^ (2 * m) := by rw [← pow_mul]

/-- Coupon-collector second-moment lower bound in cardinal form. The right side is the fraction
of all `n^m` equally likely samples that miss a coupon.

**Book Remark 5.4.12.** -/
theorem couponCollector_missing_fraction_lower {m n : ℕ} (hn : 2 ≤ n) :
    (n * (n - 1 : ℝ) ^ m) /
        ((n : ℝ) ^ m + n * (n - 1 : ℝ) ^ m) ≤
      (couponMissingSamples m n).card / (n : ℝ) ^ m := by
  let T : ℝ := (n : ℝ) ^ m
  let A : ℝ := (n - 1 : ℝ) ^ m
  let B : ℝ := (n - 2 : ℝ) ^ m
  let S1 : ℝ := n * A
  let S2 : ℝ := n * (A + (n - 1 : ℝ) * B)
  let C : ℝ := (couponMissingSamples m n).card
  have hnR : 0 < (n : ℝ) := by positivity
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1R : 0 < (n - 1 : ℝ) := by linarith
  have hT : 0 < T := by positivity
  have hA : 0 < A := by positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact pow_nonneg (by linarith) _
  have hS1 : 0 < S1 := mul_pos hnR hA
  have hC : 0 ≤ C := by positivity
  have hCS : S1 ^ 2 ≤ C * S2 := by
    simpa [S1, S2, A, B, C] using
      (couponMissingSamples_card_cauchy (m := m) (n := n))
  have hpair := coupon_pair_moment_bound (m := m) hn
  have hpair' : T * B ≤ A ^ 2 := by
    calc
      T * B ≤ (n - 1 : ℝ) ^ (2 * m) := by simpa [T, B] using hpair
      _ = A ^ 2 := by simp [A, mul_comm, pow_mul]
  have hnminus : (n - 1 : ℝ) ≤ n := by linarith
  have hS2 : T * S2 ≤ S1 * (T + S1) := by
    dsimp [T, A, B, S1, S2] at hpair' ⊢
    have hmul := mul_le_mul_of_nonneg_left hpair'
      (mul_nonneg hnR.le hn1R.le)
    nlinarith [mul_nonneg hA.le hT.le, mul_nonneg hA.le hA.le]
  have hchain1 : S1 ^ 2 * T ≤ C * S2 * T :=
    mul_le_mul_of_nonneg_right hCS hT.le
  have hchain2 : C * (T * S2) ≤ C * (S1 * (T + S1)) :=
    mul_le_mul_of_nonneg_left hS2 hC
  have hcross : S1 * T ≤ C * (T + S1) := by
    have hscaled : S1 * (S1 * T) ≤ S1 * (C * (T + S1)) := calc
      S1 * (S1 * T) = S1 ^ 2 * T := by ring
      _ ≤ C * S2 * T := hchain1
      _ = C * (T * S2) := by ring
      _ ≤ C * (S1 * (T + S1)) := hchain2
      _ = S1 * (C * (T + S1)) := by ring
    nlinarith
  rw [div_le_div_iff₀ (by positivity : 0 < T + S1) hT]
  simpa [T, A, S1, C] using hcross

/-- Explicit `90%` coupon-collector obstruction. The power condition is the exact
finite-dimensional version of `m` being below the `n log n` collection threshold.

**Lean implementation helper.** -/
theorem couponCollector_missing_fraction_nine_tenths {m n : ℕ}
    (hn : 2 ≤ n)
    (hthreshold : 9 * (n : ℝ) ^ m ≤ n * (n - 1 : ℝ) ^ m) :
    (9 : ℝ) / 10 ≤ (couponMissingSamples m n).card / (n : ℝ) ^ m := by
  have hlower := couponCollector_missing_fraction_lower (m := m) hn
  apply le_trans ?_ hlower
  have hnR : 0 < (n : ℝ) := by positivity
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1R : 0 < (n - 1 : ℝ) := by linarith
  have hden : 0 < (n : ℝ) ^ m + n * (n - 1 : ℝ) ^ m :=
    add_pos (pow_pos hnR _) (mul_pos hnR (pow_pos hn1R _))
  rw [div_le_div_iff₀ (by norm_num : 0 < (10 : ℝ)) hden]
  nlinarith

/-- A concrete logarithmic sufficient condition for the finite coupon threshold above. This is
the elementary estimate `log (1 - 1/n) ≥ -1/(n-1)` written without asymptotic notation.

**Book Remark 5.4.12.** -/
theorem coupon_log_threshold {m n : ℕ} (hn : 10 ≤ n)
    (hm : (m : ℝ) ≤ (n - 1 : ℝ) * Real.log ((n : ℝ) / 9)) :
    9 * (n : ℝ) ^ m ≤ n * (n - 1 : ℝ) ^ m := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hncast : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1R : 0 < (n - 1 : ℝ) := by linarith
  let q : ℝ := (n - 1 : ℝ) / n
  have hq : 0 < q := div_pos hn1R hnR
  have hident : -(1 : ℝ) / (n - 1 : ℝ) = 1 - q⁻¹ := by
    dsimp [q]
    field_simp
    ring
  have hlogq : -(1 : ℝ) / (n - 1 : ℝ) ≤ Real.log q := by
    rw [hident]
    exact Real.one_sub_inv_le_log_of_pos hq
  have hmdiv : (m : ℝ) / (n - 1 : ℝ) ≤ Real.log ((n : ℝ) / 9) := by
    rw [div_le_iff₀ hn1R]
    simpa [mul_comm] using hm
  have hmlog : -Real.log ((n : ℝ) / 9) ≤ (m : ℝ) * Real.log q := by
    have hmul := mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg m)
    have hneg : -Real.log ((n : ℝ) / 9) ≤
        -((m : ℝ) / (n - 1 : ℝ)) := neg_le_neg hmdiv
    calc
      -Real.log ((n : ℝ) / 9) ≤ -((m : ℝ) / (n - 1 : ℝ)) := hneg
      _ = (m : ℝ) * (-(1 : ℝ) / (n - 1 : ℝ)) := by ring
      _ ≤ (m : ℝ) * Real.log q := hmul
  have hexp := Real.exp_monotone hmlog
  have hqpow : (9 : ℝ) / n ≤ q ^ m := by
    rw [Real.exp_neg, Real.exp_log (div_pos hnR (by norm_num : (0 : ℝ) < 9)),
      inv_div, Real.exp_nat_mul, Real.exp_log hq] at hexp
    exact hexp
  have hcross := (div_le_div_iff₀ hnR (pow_pos hnR m)).mp (by
    simpa [q, div_pow] using hqpow)
  simpa [mul_comm] using hcross

/-- The isotropic one-hot vector `sqrt n e_j` from the hint to the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def couponVector (n : ℕ) (j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  Real.sqrt n • EuclideanSpace.basisFun (Fin n) ℝ j

/-- The coupon vector for index `j` is `sqrt n` in coordinate `j` and zero elsewhere.

**Lean implementation helper.** -/
@[simp] lemma couponVector_apply (n : ℕ) (j k : Fin n) :
    couponVector n j k = if j = k then Real.sqrt n else 0 := by
  classical
  simp [couponVector, EuclideanSpace.basisFun_apply, eq_comm]

/-- The exact finite uniform population second moment of the one-hot law.

**Lean implementation helper.** -/
noncomputable def couponPopulationSecondMoment (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ)⁻¹ • ∑ j, Chapter4.outerProductMatrix (couponVector n j)

/-- Identifies coupon population second moment with one.

**Lean implementation helper.** -/
@[simp] theorem couponPopulationSecondMoment_eq_one {n : ℕ} (hn : 0 < n) :
    couponPopulationSecondMoment n = 1 := by
  classical
  unfold couponPopulationSecondMoment
  ext i k
  simp only [Matrix.smul_apply, Matrix.sum_apply,
    Chapter4.outerProductMatrix, smul_eq_mul, Matrix.one_apply]
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl]
    rw [show (∑ j : Fin n, couponVector n j i * couponVector n j i) = n by
      simp [couponVector_apply]]
    field_simp
  · rw [if_neg hik]
    simp [couponVector_apply, Ne.symm hik]

/-- If coupon `j` is absent from a sample, the `j`th column of its sample covariance matrix is zero.

**Lean implementation helper.** -/
lemma couponSample_missing_column {m n : ℕ} (G : Fin m → Fin n)
    (j : Fin n) (hmiss : ∀ i, G i ≠ j) :
    ∀ k, sampleCovarianceMatrix (fun i => couponVector n (G i)) k j = 0 := by
  intro k
  simp [sampleCovarianceMatrix_apply, couponVector_apply, hmiss]

/-- Uniform samples for which the empirical covariance has full operator error relative to the
isotropic population.

**Lean implementation helper.** -/
noncomputable def couponCovarianceFailureSamples (m n : ℕ) :
    Finset (Fin m → Fin n) :=
  Finset.univ.filter fun G =>
    1 ≤ HDP.matrixOpNorm
      (sampleCovarianceMatrix (fun i => couponVector n (G i)) - 1)

/-- Every coupon sample missing some coordinate belongs to the covariance-failure event.

**Lean implementation helper.** -/
lemma couponMissingSamples_subset_covarianceFailure {m n : ℕ} :
    couponMissingSamples m n ⊆ couponCovarianceFailureSamples m n := by
  classical
  intro G hG
  unfold couponMissingSamples at hG
  unfold couponCovarianceFailureSamples
  rw [Finset.mem_filter] at hG ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨j, hj⟩ := (couponMissingCount_pos_iff G).mp hG.2
  exact missingCoordinate_error_ge_one
    (sampleCovarianceMatrix (fun i => couponVector n (G i))) j
    (couponSample_missing_column G j hj)

/-- The logarithmic dimension factor is a genuine price and can be necessary.

**Book Remark 5.4.12.** -/
theorem exercise_5_28a {m n : ℕ} (hn : 2 ≤ n)
    (hthreshold : 9 * (n : ℝ) ^ m ≤ n * (n - 1 : ℝ) ^ m) :
    (9 : ℝ) / 10 ≤
      (couponCovarianceFailureSamples m n).card / (n : ℝ) ^ m := by
  have hmissing := couponCollector_missing_fraction_nine_tenths
    (m := m) hn hthreshold
  have hcard : (couponMissingSamples m n).card ≤
      (couponCovarianceFailureSamples m n).card :=
    Finset.card_le_card couponMissingSamples_subset_covarianceFailure
  calc
    (9 : ℝ) / 10 ≤
        (couponMissingSamples m n).card / (n : ℝ) ^ m := hmissing
    _ ≤ (couponCovarianceFailureSamples m n).card / (n : ℝ) ^ m := by
      gcongr

/-- Below the displayed sample-size threshold the covariance estimate fails with probability at
least `0.9`.

**Book Exercise 5.28(a).** -/
theorem exercise_5_28a_log {m n : ℕ} (hn : 10 ≤ n)
    (hm : (m : ℝ) ≤ (n - 1 : ℝ) * Real.log ((n : ℝ) / 9)) :
    (9 : ℝ) / 10 ≤
      (couponCovarianceFailureSamples m n).card / (n : ℝ) ^ m :=
  exercise_5_28a (by omega) (coupon_log_threshold hn hm)

/-- The centered matrix summand attached to one coupon draw.

**Lean implementation helper.** -/
noncomputable def couponCenteredMatrix (n : ℕ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Chapter4.outerProductMatrix (couponVector n j) - 1

/-- The summands are exactly centered under the uniform one-hot law.

**Lean implementation helper.** -/
theorem couponCenteredMatrix_uniform_sum {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ • ∑ j, couponCenteredMatrix n j = 0 := by
  simp only [couponCenteredMatrix]
  rw [Finset.sum_sub_distrib, smul_sub]
  have hpop := couponPopulationSecondMoment_eq_one hn
  change (n : ℝ)⁻¹ • ∑ j,
      Chapter4.outerProductMatrix (couponVector n j) = 1 at hpop
  rw [hpop]
  have hone : (n : ℝ)⁻¹ • ∑ _j : Fin n,
      (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
      field_simp
    · simp [hij]
  rw [hone, sub_self]

/-- Identifies coupon centered sample with covariance error.

**Lean implementation helper.** -/
lemma couponCenteredSample_eq_covarianceError {m n : ℕ} (hm : 0 < m)
    (G : Fin m → Fin n) :
    (m : ℝ)⁻¹ • ∑ i, couponCenteredMatrix n (G i) =
      sampleCovarianceMatrix (fun i => couponVector n (G i)) - 1 := by
  simp only [couponCenteredMatrix, Finset.sum_sub_distrib, smul_sub]
  have hout : (m : ℝ)⁻¹ • ∑ i,
      Chapter4.outerProductMatrix (couponVector n (G i)) =
      sampleCovarianceMatrix (fun i => couponVector n (G i)) := by
    ext j k
    simp only [Matrix.smul_apply, Matrix.sum_apply,
      Chapter4.outerProductMatrix, smul_eq_mul,
      sampleCovarianceMatrix_apply]
  have hone : (m : ℝ)⁻¹ • ∑ _i : Fin m,
      (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext j k
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hjk : j = k
    · subst k
      simp
      field_simp
    · simp [hjk]
  rw [hout, hone]

/-- The logarithmic dimension factor is a genuine price and can be necessary.

**Book Remark 5.4.12.** -/
theorem exercise_5_28b {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (hthreshold : 9 * (n : ℝ) ^ m ≤ n * (n - 1 : ℝ) ^ m) :
    (9 : ℝ) / 10 ≤
      (Finset.univ.filter fun G : Fin m → Fin n =>
        1 ≤ HDP.matrixOpNorm
          ((m : ℝ)⁻¹ • ∑ i, couponCenteredMatrix n (G i))).card /
        (n : ℝ) ^ m := by
  have hmain := exercise_5_28a (m := m) hn hthreshold
  simpa only [couponCovarianceFailureSamples,
    couponCenteredSample_eq_covarianceError hm] using hmain

/-- When `m ≤ (n-1) log(n/9)`, at least nine tenths of coupon samples have covariance error of operator norm at least `1`.

**Book Exercise 5.28(b).** -/
theorem exercise_5_28b_log {m n : ℕ} (hm0 : 0 < m) (hn : 10 ≤ n)
    (hm : (m : ℝ) ≤ (n - 1 : ℝ) * Real.log ((n : ℝ) / 9)) :
    (9 : ℝ) / 10 ≤
      (Finset.univ.filter fun G : Fin m → Fin n =>
        1 ≤ HDP.matrixOpNorm
          ((m : ℝ)⁻¹ • ∑ i, couponCenteredMatrix n (G i))).card /
        (n : ℝ) ^ m :=
  exercise_5_28b hm0 (by omega) (coupon_log_threshold hn hm)

end HDP.Chapter5

end Source_15_GeneralCovarianceEstimation
