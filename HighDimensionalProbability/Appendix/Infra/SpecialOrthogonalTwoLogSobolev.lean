import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSmoothCore
import HighDimensionalProbability.Appendix.Infra.GaussianEuclideanLSI
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Fourier.AddCircle

/-!
# A logarithmic Sobolev base case on `SO(2)`

This file supplies the base of the stabilizer induction on special orthogonal
groups.  We transport the one-dimensional Gaussian logarithmic Sobolev
inequality to the circle by the Gaussian CDF.  Constants are intentionally
coarse: the CDF is bounded by `1` in derivative and `2 * pi < 8`.
-/

open Matrix MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

/-! ## The circle as `SO(2)` -/

/-- The usual real matrix of multiplication by a unit complex number. -/
noncomputable def circleRotationMatrix (z : Circle) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.1.re, -z.1.im; z.1.im, z.1.re]

/-- A unit complex number acts as an orientation-preserving orthogonal map
of the real plane. -/
noncomputable def circleToSpecialOrthogonal (z : Circle) :
    Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  have hz : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
    have hz' := Circle.normSq_coe z
    simpa [Complex.normSq_apply, pow_two] using hz'
  refine ⟨circleRotationMatrix z, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [circleRotationMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        pow_two]
      <;> nlinarith [hz]
  · simp [circleRotationMatrix, Matrix.det_fin_two,
      pow_two]
    nlinarith [hz]

@[simp] lemma circleToSpecialOrthogonal_val (z : Circle) :
    (circleToSpecialOrthogonal z).1 = circleRotationMatrix z := rfl

/-- The circle parametrization is multiplicative. -/
lemma circleToSpecialOrthogonal_mul (z w : Circle) :
    circleToSpecialOrthogonal (z * w) =
      circleToSpecialOrthogonal z * circleToSpecialOrthogonal w := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [circleToSpecialOrthogonal, circleRotationMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]
    <;> ring

@[simp] lemma circleToSpecialOrthogonal_one :
    circleToSpecialOrthogonal 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleToSpecialOrthogonal, circleRotationMatrix]

/-- Circle multiplication, viewed as a monoid homomorphism into `SO(2)`. -/
noncomputable def circleToSpecialOrthogonalHom :
    Circle →* Matrix.specialOrthogonalGroup (Fin 2) ℝ where
  toFun := circleToSpecialOrthogonal
  map_one' := circleToSpecialOrthogonal_one
  map_mul' := circleToSpecialOrthogonal_mul

lemma continuous_circleToSpecialOrthogonal :
    Continuous circleToSpecialOrthogonal := by
  apply continuous_induced_rng.mpr
  change Continuous circleRotationMatrix
  unfold circleRotationMatrix
  fun_prop

/-- Every orientation-preserving orthogonal matrix in dimension two is a
complex rotation. -/
lemma surjective_circleToSpecialOrthogonal :
    Function.Surjective circleToSpecialOrthogonal := by
  intro U
  let a : ℝ := U.1 0 0
  let b : ℝ := -U.1 0 1
  have hmem : U.1 ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := U.2
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hmem
  have horth := hmem.1
  rw [Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ] at horth
  have h00 := congr_fun (congr_fun horth (0 : Fin 2)) (0 : Fin 2)
  have h01 := congr_fun (congr_fun horth (0 : Fin 2)) (1 : Fin 2)
  have hdet := U.2.2
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simpa [a, b, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using h00
  let z : Circle := ⟨⟨a, b⟩, by
    apply mem_sphere_zero_iff_norm.2
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    simpa [pow_two] using hab⟩
  have hdet' : a * U.1 1 1 - U.1 0 1 * U.1 1 0 = 1 := by
    simpa [a, Matrix.det_fin_two] using hdet
  have horth' : a * U.1 1 0 + U.1 0 1 * U.1 1 1 = 0 := by
    simpa [a, Matrix.mul_apply, Fin.sum_univ_two] using h01
  have hab' : a ^ 2 + (U.1 0 1) ^ 2 = 1 := by
    simpa [b] using hab
  have h10 : U.1 1 0 = -U.1 0 1 := by
    linear_combination
      a * horth' - U.1 0 1 * hdet' - U.1 1 0 * hab'
  have h11 : U.1 1 1 = a := by
    linear_combination
      a * hdet' + U.1 0 1 * horth' - U.1 1 1 * hab'
  refine ⟨z, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [circleToSpecialOrthogonal, circleRotationMatrix, z, a]
  · simp [circleToSpecialOrthogonal, circleRotationMatrix, z, b]
  · simpa [circleToSpecialOrthogonal, circleRotationMatrix, z, b] using h10.symm
  · simpa [circleToSpecialOrthogonal, circleRotationMatrix, z] using h11.symm

/-! ## The normalized additive-circle law -/

/-- The measurable structure on the multiplicative copy of `UnitAddCircle`. -/
local instance multiplicativeUnitAddCircleMeasurableSpace :
    MeasurableSpace (Multiplicative UnitAddCircle) :=
  inferInstanceAs (MeasurableSpace UnitAddCircle)

local instance multiplicativeUnitAddCircleBorelSpace :
    BorelSpace (Multiplicative UnitAddCircle) :=
  inferInstanceAs (BorelSpace UnitAddCircle)

/-- Normalized Haar measure on the additive circle, regarded as a
multiplicative group. -/
noncomputable def multiplicativeUnitAddCircleMeasure :
    Measure (Multiplicative UnitAddCircle) :=
  (volume : Measure UnitAddCircle)

local instance multiplicativeUnitAddCircleProbability :
    IsProbabilityMeasure multiplicativeUnitAddCircleMeasure := by
  constructor
  change (volume : Measure UnitAddCircle) Set.univ = 1
  exact UnitAddCircle.measure_univ

local instance multiplicativeUnitAddCircleFiniteCompacts :
    IsFiniteMeasureOnCompacts multiplicativeUnitAddCircleMeasure := by
  change IsFiniteMeasureOnCompacts (volume : Measure UnitAddCircle)
  infer_instance

local instance multiplicativeUnitAddCircleOpenPos :
    Measure.IsOpenPosMeasure multiplicativeUnitAddCircleMeasure := by
  change Measure.IsOpenPosMeasure (volume : Measure UnitAddCircle)
  infer_instance

local instance multiplicativeUnitAddCircleLeftInvariant :
    Measure.IsMulLeftInvariant multiplicativeUnitAddCircleMeasure where
  map_mul_left_eq_self q := by
    change Measure.map (fun x : UnitAddCircle => q.toAdd + x)
        (volume : Measure UnitAddCircle) = volume
    exact Measure.IsAddLeftInvariant.map_add_left_eq_self q.toAdd

local instance multiplicativeUnitAddCircleHaar :
    Measure.IsHaarMeasure multiplicativeUnitAddCircleMeasure where

/-- The additive circle, written multiplicatively, maps onto `SO(2)`. -/
noncomputable def addCircleToSpecialOrthogonalHom :
    Multiplicative UnitAddCircle →*
      Matrix.specialOrthogonalGroup (Fin 2) ℝ where
  toFun q := circleToSpecialOrthogonal (AddCircle.toCircle q.toAdd)
  map_one' := by simp
  map_mul' q r := by
    change circleToSpecialOrthogonal
        (AddCircle.toCircle (q.toAdd + r.toAdd)) = _
    rw [AddCircle.toCircle_add, circleToSpecialOrthogonal_mul]

lemma continuous_addCircleToSpecialOrthogonalHom :
    Continuous addCircleToSpecialOrthogonalHom := by
  exact continuous_circleToSpecialOrthogonal.comp
    AddCircle.continuous_toCircle

lemma surjective_addCircleToSpecialOrthogonalHom :
    Function.Surjective addCircleToSpecialOrthogonalHom := by
  intro U
  obtain ⟨z, rfl⟩ := surjective_circleToSpecialOrthogonal U
  let q : UnitAddCircle :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z
  refine ⟨Multiplicative.ofAdd q, ?_⟩
  change circleToSpecialOrthogonal (AddCircle.toCircle q) =
    circleToSpecialOrthogonal z
  congr 1
  rw [← AddCircle.homeomorphCircle_apply (T := (1 : ℝ)) one_ne_zero]
  exact (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply z

/-- The normalized additive-circle law is sent to normalized Haar measure
on `SO(2)`. -/
lemma measurePreserving_addCircleToSpecialOrthogonalHom :
    MeasurePreserving addCircleToSpecialOrthogonalHom
      multiplicativeUnitAddCircleMeasure
      (HDP.Chapter5.specialOrthogonalHaarMeasure 2) := by
  apply MonoidHom.measurePreserving
  · exact continuous_addCircleToSpecialOrthogonalHom
  · exact surjective_addCircleToSpecialOrthogonalHom
  · change multiplicativeUnitAddCircleMeasure Set.univ =
      (HDP.Chapter5.specialOrthogonalHaarMeasure 2) Set.univ
    rw [measure_univ, measure_univ]

/-- The ordinary unit interval, with its endpoints identified, parametrizes
the normalized additive circle. -/
noncomputable def unitIntervalToMultiplicativeAddCircle
    (u : unitInterval) : Multiplicative UnitAddCircle :=
  Multiplicative.ofAdd (QuotientAddGroup.mk u.1)

lemma measurePreserving_unitIntervalToMultiplicativeAddCircle :
    MeasurePreserving unitIntervalToMultiplicativeAddCircle
      (volume : Measure unitInterval)
      multiplicativeUnitAddCircleMeasure := by
  have hcoe := unitInterval.measurePreserving_coe
  have hmk := AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hrest :
      (volume : Measure ℝ).restrict (Set.Icc 0 1) =
        (volume : Measure ℝ).restrict (Set.Ioc 0 (0 + 1)) := by
    simpa using
      (Measure.restrict_congr_set
        (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1))).symm
  have hmk' :
      MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
        ((volume : Measure ℝ).restrict (Set.Icc 0 1))
        (volume : Measure UnitAddCircle) := by
    rw [hrest]
    simpa using hmk
  have hcomp := hmk'.comp hcoe
  change MeasurePreserving
    (fun u : unitInterval =>
      (QuotientAddGroup.mk u.1 : UnitAddCircle))
    (volume : Measure unitInterval) (volume : Measure UnitAddCircle)
  simpa [Function.comp_def] using hcomp

/-! ## Smoothness of the Gaussian CDF -/

private abbrev standardGaussianPDF (x : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x

private lemma standardGaussianCDF_sub_eq_intervalIntegral
    {x y : ℝ} (hxy : x ≤ y) :
    HDP.Chapter5.standardGaussianCDF y -
        HDP.Chapter5.standardGaussianCDF x =
      ∫ t in x..y, standardGaussianPDF t := by
  have hmeasure :
      gaussianReal 0 1 (Set.Ioc x y) =
        ENNReal.ofReal
          (HDP.Chapter5.standardGaussianCDF y -
            HDP.Chapter5.standardGaussianCDF x) := by
    rw [← ProbabilityTheory.measure_cdf (gaussianReal 0 1),
      StieltjesFunction.measure_Ioc]
  have hint :
      IntegrableOn standardGaussianPDF (Set.Ioc x y) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hof :
      ENNReal.ofReal
          (∫ t in Set.Ioc x y, standardGaussianPDF t) =
        ∫⁻ t in Set.Ioc x y,
          ENNReal.ofReal (standardGaussianPDF t) := by
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t =>
        gaussianPDFReal_nonneg 0 1 t)
  have heq :
      ENNReal.ofReal
          (HDP.Chapter5.standardGaussianCDF y -
            HDP.Chapter5.standardGaussianCDF x) =
        ENNReal.ofReal
          (∫ t in Set.Ioc x y, standardGaussianPDF t) := by
    rw [← hmeasure, gaussianReal_apply 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simpa [gaussianPDF, standardGaussianPDF] using hof.symm
  have hleft :
      0 ≤ HDP.Chapter5.standardGaussianCDF y -
        HDP.Chapter5.standardGaussianCDF x :=
    sub_nonneg.mpr
      (ProbabilityTheory.monotone_cdf (gaussianReal 0 1) hxy)
  have hright :
      0 ≤ ∫ t in Set.Ioc x y, standardGaussianPDF t :=
    integral_nonneg fun t => gaussianPDFReal_nonneg 0 1 t
  have hreal :=
    (ENNReal.ofReal_eq_ofReal_iff hleft hright).mp heq
  rw [intervalIntegral.integral_of_le hxy]
  exact hreal

private lemma standardGaussianCDF_eq_integral (x : ℝ) :
    HDP.Chapter5.standardGaussianCDF x =
      HDP.Chapter5.standardGaussianCDF 0 +
        ∫ t in (0 : ℝ)..x, standardGaussianPDF t := by
  rcases le_total 0 x with hx | hx
  · have h := standardGaussianCDF_sub_eq_intervalIntegral hx
    linarith
  · have h := standardGaussianCDF_sub_eq_intervalIntegral hx
    rw [intervalIntegral.integral_symm] at h
    linarith

lemma hasDerivAt_standardGaussianCDF (x : ℝ) :
    HasDerivAt HDP.Chapter5.standardGaussianCDF
      (standardGaussianPDF x) x := by
  have hpdf : Continuous standardGaussianPDF := by
    unfold standardGaussianPDF gaussianPDFReal
    fun_prop
  have hderiv :=
    (hasDerivAt_const x (HDP.Chapter5.standardGaussianCDF 0)).add
      (intervalIntegral.integral_hasDerivAt_right
        (hpdf.intervalIntegrable 0 x)
        (hpdf.stronglyMeasurableAtFilter volume (𝓝 x)) hpdf.continuousAt)
  simpa using hderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y =>
      standardGaussianCDF_eq_integral y)

lemma differentiable_standardGaussianCDF :
    Differentiable ℝ HDP.Chapter5.standardGaussianCDF :=
  fun x => (hasDerivAt_standardGaussianCDF x).differentiableAt

lemma continuous_fderiv_standardGaussianCDF :
    Continuous
      (fun x => fderiv ℝ HDP.Chapter5.standardGaussianCDF x) := by
  have hformula :
      (fun x => fderiv ℝ HDP.Chapter5.standardGaussianCDF x) =
        fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (standardGaussianPDF x) := by
    funext x
    exact (hasDerivAt_standardGaussianCDF x).hasFDerivAt.fderiv
  rw [hformula]
  have hpdf : Continuous standardGaussianPDF := by
    unfold standardGaussianPDF gaussianPDFReal
    fun_prop
  fun_prop

lemma norm_fderiv_standardGaussianCDF_le_one (x : ℝ) :
    ‖fderiv ℝ HDP.Chapter5.standardGaussianCDF x‖ ≤ 1 := by
  simpa using
    (norm_fderiv_le_of_lipschitz ℝ
      HDP.Chapter5.standardGaussianCDF_lipschitz :
        ‖fderiv ℝ HDP.Chapter5.standardGaussianCDF x‖ ≤ (1 : ℝ))

/-! ## The Gaussian rotation curve -/

private abbrev rotationAngle (t : ℝ) : ℝ := 2 * Real.pi * t

/-- The ordinary rotation matrix with one full turn on the interval
`[0,1]`. -/
noncomputable def realCircleRotationMatrix (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (rotationAngle t), -Real.sin (rotationAngle t);
    Real.sin (rotationAngle t), Real.cos (rotationAngle t)]

/-- The rotation matrix bundled as an element of `SO(2)`. -/
noncomputable def realCircleRotation (t : ℝ) :
    Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  circleToSpecialOrthogonal (Circle.exp (rotationAngle t))

@[simp] lemma realCircleRotation_val (t : ℝ) :
    (realCircleRotation t).1 = realCircleRotationMatrix t := by
  have hcast :
      (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) =
        ((rotationAngle t : ℝ) : ℂ) := by
    push_cast
    rfl
  have hre :
      (Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I)).re =
        Real.cos (rotationAngle t) := by
    rw [hcast]
    exact Complex.exp_ofReal_mul_I_re (rotationAngle t)
  have him :
      (Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I)).im =
        Real.sin (rotationAngle t) := by
    rw [hcast]
    exact Complex.exp_ofReal_mul_I_im (rotationAngle t)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCircleRotation, realCircleRotationMatrix,
      circleRotationMatrix, Circle.coe_exp, hre, him]

/-- Gaussian CDF followed by the normalized circle parametrization. -/
noncomputable def gaussianSO2Transport (x : ℝ) :
    Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  addCircleToSpecialOrthogonalHom
    (unitIntervalToMultiplicativeAddCircle
      (HDP.Chapter5.standardGaussianCDFUnit x))

lemma gaussianSO2Transport_eq_rotation (x : ℝ) :
    gaussianSO2Transport x =
      realCircleRotation (HDP.Chapter5.standardGaussianCDF x) := by
  apply Subtype.ext
  simp [gaussianSO2Transport, addCircleToSpecialOrthogonalHom,
    unitIntervalToMultiplicativeAddCircle, realCircleRotation,
    AddCircle.toCircle_apply_mk, rotationAngle,
    HDP.Chapter5.standardGaussianCDFUnit]

/-- The Gaussian rotation curve has exactly normalized Haar law on
`SO(2)`. -/
lemma measurePreserving_gaussianSO2Transport :
    MeasurePreserving gaussianSO2Transport (gaussianReal 0 1)
      (HDP.Chapter5.specialOrthogonalHaarMeasure 2) := by
  have hCDF : MeasurePreserving
      HDP.Chapter5.standardGaussianCDFUnit (gaussianReal 0 1)
      (volume : Measure unitInterval) :=
    ⟨HDP.Chapter5.measurable_standardGaussianCDFUnit,
      HDP.Chapter5.map_standardGaussianCDFUnit⟩
  have hcomp := measurePreserving_addCircleToSpecialOrthogonalHom.comp
    (measurePreserving_unitIntervalToMultiplicativeAddCircle.comp hCDF)
  change MeasurePreserving
    (fun x => addCircleToSpecialOrthogonalHom
      (unitIntervalToMultiplicativeAddCircle
        (HDP.Chapter5.standardGaussianCDFUnit x)))
    (gaussianReal 0 1) (HDP.Chapter5.specialOrthogonalHaarMeasure 2)
  exact hcomp

private noncomputable def gaussianMatrixVectorizeCLM :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] FrobeniusEuclidean 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := HDP.gaussianMatrixVectorize
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] private lemma gaussianMatrixVectorizeCLM_apply
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    gaussianMatrixVectorizeCLM A = HDP.gaussianMatrixVectorize A := rfl

private noncomputable def realCircleRotationVelocity (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(Real.sin (rotationAngle t) * (2 * Real.pi)),
      -(Real.cos (rotationAngle t) * (2 * Real.pi));
    Real.cos (rotationAngle t) * (2 * Real.pi),
      -(Real.sin (rotationAngle t) * (2 * Real.pi))]

private lemma hasDerivAt_vectorizedRotation (t : ℝ) :
    HasDerivAt
      (fun s => HDP.gaussianMatrixVectorize (realCircleRotationMatrix s))
      (HDP.gaussianMatrixVectorize (realCircleRotationVelocity t)) t := by
  have hangle : HasDerivAt rotationAngle (2 * Real.pi) t := by
    simpa [rotationAngle] using
      (hasDerivAt_id t).const_mul (2 * Real.pi)
  let I : FrobeniusEuclidean 2 :=
    HDP.gaussianMatrixVectorize (!![1, 0; 0, 1])
  let J : FrobeniusEuclidean 2 :=
    HDP.gaussianMatrixVectorize (!![0, -1; 1, 0])
  have hc := (Real.hasDerivAt_cos (rotationAngle t)).comp t hangle
  have hs := (Real.hasDerivAt_sin (rotationAngle t)).comp t hangle
  have hmatrix := (hc.smul_const I).add (hs.smul_const J)
  have hfun :
      ((fun s => (Real.cos ∘ rotationAngle) s • I) +
        fun s => (Real.sin ∘ rotationAngle) s • J) =
      fun s => HDP.gaussianMatrixVectorize (realCircleRotationMatrix s) := by
    funext s
    apply WithLp.ofLp_injective
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [I, J, realCircleRotationMatrix,
        HDP.gaussianMatrixVectorize, HDP.gaussianMatrixFlatten]
  have hvelocity :
      (-Real.sin (rotationAngle t) * (2 * Real.pi)) • I +
          (Real.cos (rotationAngle t) * (2 * Real.pi)) • J =
        HDP.gaussianMatrixVectorize (realCircleRotationVelocity t) := by
    apply WithLp.ofLp_injective
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [I, J, realCircleRotationVelocity,
        HDP.gaussianMatrixVectorize, HDP.gaussianMatrixFlatten]
  rw [hfun, hvelocity] at hmatrix
  exact hmatrix

private lemma realCircleRotationVelocity_eq (t : ℝ) :
    realCircleRotationVelocity t =
      (-(2 * Real.pi)) •
        (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCircleRotationVelocity, realCircleRotationMatrix,
      skewGenerator, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, Matrix.single_apply] <;> ring

private lemma hasDerivAt_vectorizedRotation_tangent (t : ℝ) :
    HasDerivAt
      (fun s => HDP.gaussianMatrixVectorize (realCircleRotationMatrix s))
      (HDP.gaussianMatrixVectorize
        ((-(2 * Real.pi)) •
          (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1))) t := by
  have hmatrix := hasDerivAt_vectorizedRotation t
  rw [realCircleRotationVelocity_eq] at hmatrix
  exact hmatrix

/-- Restriction of an ambient function to the one-parameter rotation
curve. -/
noncomputable def rotationRestriction
    (H : FrobeniusEuclidean 2 → ℝ) (t : ℝ) : ℝ :=
  H (HDP.gaussianMatrixVectorize (realCircleRotationMatrix t))

private lemma hasDerivAt_rotationRestriction
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H) (t : ℝ) :
    HasDerivAt (rotationRestriction H)
      (-(2 * Real.pi) *
        (2 * tangentGradient H (realCircleRotation t) 0 1)) t := by
  have hcomp := (hHd _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_vectorizedRotation_tangent t)
  have hval := realCircleRotation_val t
  change HasDerivAt (rotationRestriction H)
    (fderiv ℝ H
      (HDP.gaussianMatrixVectorize (realCircleRotationMatrix t))
      (HDP.gaussianMatrixVectorize
        ((-(2 * Real.pi)) •
          (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1)))) t at hcomp
  have hbase :
      fderiv ℝ H
          (HDP.gaussianMatrixVectorize (realCircleRotationMatrix t))
          (HDP.gaussianMatrixVectorize
            (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1)) =
        2 * tangentGradient H (realCircleRotation t) 0 1 := by
    simpa [hval] using
      fderiv_skewGenerator_eq_tangentGradient H
        (realCircleRotation t) (0 : Fin 2) 1
  have hscaled :
      fderiv ℝ H
          (HDP.gaussianMatrixVectorize (realCircleRotationMatrix t))
          (HDP.gaussianMatrixVectorize
            ((-(2 * Real.pi)) •
              (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1))) =
        -(2 * Real.pi) *
          (2 * tangentGradient H (realCircleRotation t) 0 1) := by
    calc
      _ = fderiv ℝ H
          (HDP.gaussianMatrixVectorize (realCircleRotationMatrix t))
          ((-(2 * Real.pi)) •
            HDP.gaussianMatrixVectorize
              (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1)) := by
            rfl
      _ = (-(2 * Real.pi)) •
          fderiv ℝ H
            (HDP.gaussianMatrixVectorize (realCircleRotationMatrix t))
            (HDP.gaussianMatrixVectorize
              (realCircleRotationMatrix t * skewGenerator (0 : Fin 2) 1)) := by
            rw [map_smul]
      _ = _ := by rw [hbase]; rfl
  exact hcomp.congr_deriv hscaled

private lemma realSelfModule_eq :
    (Semiring.toModule : Module ℝ ℝ) =
      (NormedAlgebra.toNormedSpace ℝ).toModule := rfl

private lemma hasDerivAt_real_module_iff
    (f : ℝ → ℝ) (f' x : ℝ) :
    (@HasDerivAt ℝ _ ℝ _ Semiring.toModule _ _ f f' x) ↔
      (@HasDerivAt ℝ _ ℝ NormedField.toNormedCommRing.toAddCommGroup
        (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x) := by
  with_reducible_and_instances rfl

/-- The one-dimensional function to which the Gaussian logarithmic Sobolev
inequality is applied. -/
noncomputable def gaussianRotationRestriction
    (H : FrobeniusEuclidean 2 → ℝ) (x : ℝ) : ℝ :=
  rotationRestriction H (HDP.Chapter5.standardGaussianCDF x)

lemma gaussianRotationRestriction_eq_transport
    (H : FrobeniusEuclidean 2 → ℝ) (x : ℝ) :
    gaussianRotationRestriction H x =
      H (HDP.gaussianMatrixVectorize (gaussianSO2Transport x).1) := by
  rw [gaussianSO2Transport_eq_rotation]
  simp [gaussianRotationRestriction, rotationRestriction]

private lemma hasDerivAt_gaussianRotationRestriction
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H) (x : ℝ) :
    HasDerivAt (gaussianRotationRestriction H)
      ((-(2 * Real.pi) *
          (2 * tangentGradient H (gaussianSO2Transport x) 0 1)) *
        standardGaussianPDF x) x := by
  have hcomp :=
    (hasDerivAt_rotationRestriction H hHd
      (HDP.Chapter5.standardGaussianCDF x)).comp x
        (hasDerivAt_standardGaussianCDF x)
  have hrot := (gaussianSO2Transport_eq_rotation x).symm
  let d := ((-(2 * Real.pi) *
      (2 * tangentGradient H (gaussianSO2Transport x) 0 1)) *
    standardGaussianPDF x)
  have hcomp' :
      @HasDerivAt ℝ _ ℝ NormedField.toNormedCommRing.toAddCommGroup
        (NormedAlgebra.toNormedSpace ℝ).toModule _ _
        (gaussianRotationRestriction H) d x := by
    change @HasDerivAt ℝ _ ℝ NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun y => rotationRestriction H
        (HDP.Chapter5.standardGaussianCDF y)) d x
    simpa [Function.comp_def, hrot, d] using hcomp
  exact (hasDerivAt_real_module_iff
    (gaussianRotationRestriction H) d x).2 hcomp'

lemma differentiable_gaussianRotationRestriction
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H) :
    Differentiable ℝ (gaussianRotationRestriction H) :=
  fun x => (hasDerivAt_gaussianRotationRestriction H hHd x).differentiableAt

private lemma continuous_realCircleRotation :
    Continuous realCircleRotation := by
  unfold realCircleRotation
  exact continuous_circleToSpecialOrthogonal.comp
    (Circle.exp.continuous.comp (by fun_prop))

lemma continuous_gaussianSO2Transport :
    Continuous gaussianSO2Transport := by
  have hfun : gaussianSO2Transport =
      fun x => realCircleRotation (HDP.Chapter5.standardGaussianCDF x) := by
    funext x
    exact gaussianSO2Transport_eq_rotation x
  rw [hfun]
  exact continuous_realCircleRotation.comp
    HDP.Chapter5.continuous_standardGaussianCDF

lemma continuous_fderiv_gaussianRotationRestriction
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H)
    (hHc : Continuous (fun y => fderiv ℝ H y)) :
    Continuous (fun x => fderiv ℝ (gaussianRotationRestriction H) x) := by
  have hformula :
      (fun x => fderiv ℝ (gaussianRotationRestriction H) x) =
        fun x => (1 : ℝ →L[ℝ] ℝ).smulRight
          ((-(2 * Real.pi) *
              (2 * tangentGradient H (gaussianSO2Transport x) 0 1)) *
            standardGaussianPDF x) := by
    funext x
    exact (hasDerivAt_gaussianRotationRestriction H hHd x).hasFDerivAt.fderiv
  rw [hformula]
  have htangent : Continuous
      (fun x => tangentGradient H (gaussianSO2Transport x) 0 1) := by
    exact ((continuous_apply (1 : Fin 2)).comp
      ((continuous_apply (0 : Fin 2)).comp
        ((continuous_tangentGradient hHc).comp
          continuous_gaussianSO2Transport)))
  have hpdf : Continuous standardGaussianPDF := by
    unfold standardGaussianPDF gaussianPDFReal
    fun_prop
  have hscalar : Continuous
      (fun x =>
        ((-(2 * Real.pi) *
            (2 * tangentGradient H (gaussianSO2Transport x) 0 1)) *
          standardGaussianPDF x)) := by
    fun_prop
  have heq :
      (fun x =>
        (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ))
          (((-(2 * Real.pi) *
              (2 * tangentGradient H (gaussianSO2Transport x) 0 1)) *
            standardGaussianPDF x))) =
        fun x => (1 : ℝ →L[ℝ] ℝ).smulRight
          (((-(2 * Real.pi) *
              (2 * tangentGradient H (gaussianSO2Transport x) 0 1)) *
            standardGaussianPDF x)) := by
    funext x
    rfl
  rw [← heq]
  exact
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp
      hscalar

private lemma tangentGradient_two_frobenius_sq
    (H : FrobeniusEuclidean 2 → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2 =
      2 * (tangentGradient H U 0 1) ^ 2 := by
  let X := tangentGradient H U
  have hskew : Xᵀ = -X := tangentGradient_transpose H U
  have h00 : X 0 0 = 0 := by
    have h := congr_fun (congr_fun hskew (0 : Fin 2)) (0 : Fin 2)
    change X 0 0 = -X 0 0 at h
    linarith
  have h11 : X 1 1 = 0 := by
    have h := congr_fun (congr_fun hskew (1 : Fin 2)) (1 : Fin 2)
    change X 1 1 = -X 1 1 at h
    linarith
  have h10 : X 1 0 = -X 0 1 := by
    have h := congr_fun (congr_fun hskew (0 : Fin 2)) (1 : Fin 2)
    exact h
  rw [HDP.matrixFrobeniusNorm_sq]
  simp [Fin.sum_univ_two, X, h00, h11, h10]
  ring

private lemma standardGaussianPDF_le_one (x : ℝ) :
    standardGaussianPDF x ≤ 1 := by
  have h := norm_fderiv_standardGaussianCDF_le_one x
  rw [(hasDerivAt_standardGaussianCDF x).hasFDerivAt.fderiv] at h
  simpa [abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)] using h

private lemma fderiv_gaussianRotationRestriction_sq_le
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H) (x : ℝ) :
    ‖fderiv ℝ (gaussianRotationRestriction H) x‖ ^ 2 ≤
      128 * HDP.matrixFrobeniusNorm
        (tangentGradient H (gaussianSO2Transport x)) ^ 2 := by
  let X := tangentGradient H (gaussianSO2Transport x) 0 1
  let p := standardGaussianPDF x
  let c := 2 * Real.pi
  have hder :=
    (hasDerivAt_gaussianRotationRestriction H hHd x).hasFDerivAt.fderiv
  have hnorm :
      ‖fderiv ℝ (gaussianRotationRestriction H) x‖ =
        |((-c * (2 * X)) * p)| := by
    rw [hder]
    simp [c, X, p]
  have hc0 : 0 ≤ c := by positivity
  have hc : c ≤ 8 := by
    dsimp [c]
    nlinarith [Real.pi_lt_four]
  have hc2 : c ^ 2 ≤ 64 := by nlinarith [sq_nonneg (c - 8)]
  have hp0 : 0 ≤ p := gaussianPDFReal_nonneg 0 1 x
  have hp : p ≤ 1 := standardGaussianPDF_le_one x
  have hp2 : p ^ 2 ≤ 1 := by nlinarith
  rw [hnorm, sq_abs, tangentGradient_two_frobenius_sq H
    (gaussianSO2Transport x)]
  calc
    ((-c * (2 * X)) * p) ^ 2 =
        (c ^ 2 * 4 * p ^ 2) * X ^ 2 := by ring
    _ ≤ (64 * 4 * 1) * X ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · calc
          c ^ 2 * 4 * p ^ 2 ≤ 64 * 4 * p ^ 2 := by
            gcongr
          _ ≤ 64 * 4 * 1 := by gcongr
      · positivity
    _ = 128 * (2 * X ^ 2) := by ring

private lemma exists_uniform_norm_bound
    {α E : Type*} [TopologicalSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (f : α → E) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  have hb := isCompact_univ.bddAbove_image
    (continuous_norm.comp hf).continuousOn
  rcases hb with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  exact (hC ⟨x, Set.mem_univ x, rfl⟩).trans (le_max_left _ _)

private lemma gaussianRotationRestriction_memW12
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H)
    (hHc : Continuous (fun y => fderiv ℝ H y)) :
    GaussianSobolevReal.MemW12GaussianReal
      (gaussianRotationRestriction H) (gaussianReal 0 1) := by
  let F : Matrix.specialOrthogonalGroup (Fin 2) ℝ → ℝ :=
    fun U => H (HDP.gaussianMatrixVectorize U.1)
  have hF : Continuous F := by
    exact hHd.continuous.comp
      (continuous_gaussianMatrixVectorize.comp continuous_subtype_val)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_norm_bound F hF
  let T : Matrix.specialOrthogonalGroup (Fin 2) ℝ → ℝ :=
    fun U => tangentGradient H U 0 1
  have hT : Continuous T := by
    exact (continuous_apply (1 : Fin 2)).comp
      ((continuous_apply (0 : Fin 2)).comp
        (continuous_tangentGradient hHc))
  obtain ⟨D, hD0, hD⟩ := exists_uniform_norm_bound T hT
  have hgdiff := differentiable_gaussianRotationRestriction H hHd
  have hgcont := continuous_fderiv_gaussianRotationRestriction H hHd hHc
  constructor
  · apply MemLp.of_bound hgdiff.continuous.aestronglyMeasurable C
    filter_upwards [] with x
    rw [gaussianRotationRestriction_eq_transport]
    exact hC (gaussianSO2Transport x)
  · apply MemLp.of_bound hgcont.aestronglyMeasurable (16 * D)
    filter_upwards [] with x
    have hder :=
      (hasDerivAt_gaussianRotationRestriction H hHd x).hasFDerivAt.fderiv
    rw [hder]
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have hc : |-(2 * Real.pi)| ≤ 8 := by
      rw [abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.pi_lt_four]
    have hx : |tangentGradient H (gaussianSO2Transport x) 0 1| ≤ D := by
      simpa [T, Real.norm_eq_abs] using hD (gaussianSO2Transport x)
    have hp0 : 0 ≤ standardGaussianPDF x :=
      gaussianPDFReal_nonneg 0 1 x
    have hp : |standardGaussianPDF x| ≤ 1 := by
      rw [abs_of_nonneg hp0]
      exact standardGaussianPDF_le_one x
    calc
      |-(2 * Real.pi)| *
          (|2| * |tangentGradient H (gaussianSO2Transport x) 0 1|) *
          |standardGaussianPDF x| ≤ 8 * (2 * D) * 1 := by
            gcongr <;> norm_num
      _ = 16 * D := by ring

private theorem gaussianRotationRestriction_logSobolev
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H)
    (hHc : Continuous (fun y => fderiv ℝ H y)) :
    boltzmannEntropy (gaussianReal 0 1)
        (fun x => gaussianRotationRestriction H x ^ 2) ≤
      2 * ∫ x, ‖fderiv ℝ (gaussianRotationRestriction H) x‖ ^ 2
        ∂gaussianReal 0 1 := by
  have hlsi := GaussianSobolevReal.gaussian_logSobolev_W12_real
    (gaussianRotationRestriction_memW12 H hHd hHc)
    (differentiable_gaussianRotationRestriction H hHd)
    (continuous_fderiv_gaussianRotationRestriction H hHd hHc)
  simpa [LogSobolev.entropy, boltzmannEntropy] using hlsi

private lemma gaussianRotationRestriction_entropy_eq
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H) :
    boltzmannEntropy (gaussianReal 0 1)
        (fun x => gaussianRotationRestriction H x ^ 2) =
      boltzmannEntropy (HDP.Chapter5.specialOrthogonalHaarMeasure 2)
        (fun U => H (HDP.gaussianMatrixVectorize U.1) ^ 2) := by
  let q : Matrix.specialOrthogonalGroup (Fin 2) ℝ → ℝ :=
    fun U => H (HDP.gaussianMatrixVectorize U.1) ^ 2
  have hq : Continuous q := by
    exact (hHd.continuous.comp
      (continuous_gaussianMatrixVectorize.comp continuous_subtype_val)).pow 2
  have hsq :
      (∫ x, gaussianRotationRestriction H x ^ 2 ∂gaussianReal 0 1) =
        ∫ U, q U ∂HDP.Chapter5.specialOrthogonalHaarMeasure 2 := by
    calc
      _ = ∫ x, q (gaussianSO2Transport x) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [q, gaussianRotationRestriction_eq_transport]
      _ = ∫ U, q U ∂Measure.map gaussianSO2Transport (gaussianReal 0 1) :=
        (integral_map measurePreserving_gaussianSO2Transport.measurable.aemeasurable
          hq.aestronglyMeasurable).symm
      _ = _ := by rw [measurePreserving_gaussianSO2Transport.map_eq]
  have hlog :
      (∫ x, gaussianRotationRestriction H x ^ 2 *
          Real.log (gaussianRotationRestriction H x ^ 2) ∂gaussianReal 0 1) =
        ∫ U, q U * Real.log (q U)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure 2 := by
    calc
      _ = ∫ x, q (gaussianSO2Transport x) *
          Real.log (q (gaussianSO2Transport x)) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [q, gaussianRotationRestriction_eq_transport]
      _ = ∫ U, q U * Real.log (q U)
          ∂Measure.map gaussianSO2Transport (gaussianReal 0 1) :=
        (integral_map measurePreserving_gaussianSO2Transport.measurable.aemeasurable
          hq.mul_log.aestronglyMeasurable).symm
      _ = _ := by rw [measurePreserving_gaussianSO2Transport.map_eq]
  unfold boltzmannEntropy
  rw [hsq, hlog]

/-- Logarithmic Sobolev inequality on `SO(2)`, with a deliberately coarse
fixed constant suitable for the stabilizer induction. -/
theorem specialOrthogonal_two_logSobolev
    (H : FrobeniusEuclidean 2 → ℝ)
    (hHd : Differentiable ℝ H)
    (hHc : Continuous (fun y => fderiv ℝ H y)) :
    boltzmannEntropy (HDP.Chapter5.specialOrthogonalHaarMeasure 2)
        (fun U => H (HDP.gaussianMatrixVectorize U.1) ^ 2) ≤
      2 * (256 / (2 : ℝ)) *
        ∫ U, HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure 2 := by
  let E : Matrix.specialOrthogonalGroup (Fin 2) ℝ → ℝ :=
    fun U => HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2
  have hE : Continuous E := by
    have ht := continuous_tangentGradient hHc
    unfold E HDP.matrixFrobeniusNorm
    fun_prop
  have hEint : Integrable E
      (HDP.Chapter5.specialOrthogonalHaarMeasure 2) := by
    simpa using hE.continuousOn.integrableOn_compact
      (μ := HDP.Chapter5.specialOrthogonalHaarMeasure 2) isCompact_univ
  have hEcomp : Integrable (fun x => E (gaussianSO2Transport x))
      (gaussianReal 0 1) := by
    simpa [Function.comp_def] using
      measurePreserving_gaussianSO2Transport.integrable_comp_of_integrable hEint
  have hW := gaussianRotationRestriction_memW12 H hHd hHc
  have hDint : Integrable
      (fun x => ‖fderiv ℝ (gaussianRotationRestriction H) x‖ ^ 2)
      (gaussianReal 0 1) := by
    exact hW.2.integrable_norm_pow (by norm_num)
  have hpoint :
      (∫ x, ‖fderiv ℝ (gaussianRotationRestriction H) x‖ ^ 2
          ∂gaussianReal 0 1) ≤
        128 * ∫ x, E (gaussianSO2Transport x) ∂gaussianReal 0 1 := by
    have hi := integral_mono hDint (hEcomp.const_mul 128)
      (fun x => fderiv_gaussianRotationRestriction_sq_le H hHd x)
    simpa [E, integral_const_mul] using hi
  have hmapE :
      (∫ x, E (gaussianSO2Transport x) ∂gaussianReal 0 1) =
        ∫ U, E U ∂HDP.Chapter5.specialOrthogonalHaarMeasure 2 := by
    calc
      _ = ∫ U, E U ∂Measure.map gaussianSO2Transport (gaussianReal 0 1) :=
        (integral_map measurePreserving_gaussianSO2Transport.measurable.aemeasurable
          hE.aestronglyMeasurable).symm
      _ = _ := by rw [measurePreserving_gaussianSO2Transport.map_eq]
  calc
    boltzmannEntropy (HDP.Chapter5.specialOrthogonalHaarMeasure 2)
        (fun U => H (HDP.gaussianMatrixVectorize U.1) ^ 2) =
        boltzmannEntropy (gaussianReal 0 1)
          (fun x => gaussianRotationRestriction H x ^ 2) :=
      (gaussianRotationRestriction_entropy_eq H hHd).symm
    _ ≤ 2 * ∫ x, ‖fderiv ℝ (gaussianRotationRestriction H) x‖ ^ 2
          ∂gaussianReal 0 1 :=
      gaussianRotationRestriction_logSobolev H hHd hHc
    _ ≤ 2 * (128 * ∫ x, E (gaussianSO2Transport x)
          ∂gaussianReal 0 1) := by gcongr
    _ = 2 * (256 / (2 : ℝ)) *
        ∫ U, HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure 2 := by
      rw [hmapE]
      simp [E]
      ring

end

end HDP.Appendix.SpecialOrthogonal
