import HighDimensionalProbability.Appendix.Infra.BerryEsseenInversion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian principal-value inversion

This file proves the sine-integral inversion formula for the standard
Gaussian distribution.  The proof differentiates under the integral sign,
uses the exact Gaussian characteristic function for the resulting cosine
transform, and identifies the antiderivative with the Gaussian cdf.
-/

open Real Complex Filter MeasureTheory ProbabilityTheory intervalIntegral Set
open scoped Interval Topology FourierTransform

namespace HDP.Appendix

lemma integrable_gaussianPDFReal_mul_cexp (a : ℝ) :
    Integrable (fun u : ℝ =>
      (gaussianPDFReal 0 1 u : ℂ) *
        Complex.exp (((u * a : ℝ) : ℂ) * Complex.I)) := by
  apply (integrable_gaussianPDFReal 0 1).mono'
  · fun_prop
  · filter_upwards with u
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 u),
      Complex.norm_exp]
    simp

/-- The real part of the standard Gaussian characteristic function. -/
lemma integral_gaussianPDFReal_mul_cos (a : ℝ) :
    ∫ u : ℝ, gaussianPDFReal 0 1 u * Real.cos (a * u) =
      Real.exp (-a ^ 2 / 2) := by
  have hchar := charFun_gaussianReal
    (μ := (0 : ℝ)) (v := (1 : NNReal)) a
  rw [charFun, integral_gaussianReal_eq_integral_smul one_ne_zero] at hchar
  simp_rw [Complex.real_smul] at hchar
  have hint :
      Integrable (fun u : ℝ =>
        (gaussianPDFReal 0 1 u : ℂ) *
          Complex.exp
            (((inner ℝ u a : ℝ) : ℂ) * Complex.I)) := by
    convert integrable_gaussianPDFReal_mul_cexp a using 1
    funext u
    congr 3
    push_cast
    simp [mul_comm]
  calc
    ∫ u : ℝ, gaussianPDFReal 0 1 u * Real.cos (a * u) =
        ∫ u : ℝ, Complex.re
          ((gaussianPDFReal 0 1 u : ℂ) *
            Complex.exp
              (((inner ℝ u a : ℝ) : ℂ) * Complex.I)) := by
          congr with u
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
          congr 1
          rw [show
              (((inner ℝ u a : ℝ) : ℂ) * Complex.I) =
                (((a * u : ℝ) : ℂ) * Complex.I) by
              push_cast
              simp [mul_comm],
            Complex.exp_mul_I]
          simp only [Complex.add_re,
            Complex.cos_ofReal_re, Complex.mul_re,
            Complex.sin_ofReal_re, Complex.sin_ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero,
            zero_mul, sub_zero, add_zero]
    _ = Complex.re
        (∫ u : ℝ, (gaussianPDFReal 0 1 u : ℂ) *
          Complex.exp
            (((inner ℝ u a : ℝ) : ℂ) * Complex.I)) :=
      integral_re hint
    _ = Complex.re
        (Complex.exp
          ((a : ℂ) * (0 : ℂ) * Complex.I -
            (((1 : NNReal) : ℝ) : ℂ) *
              (a : ℂ) ^ 2 / 2)) := by
      exact congrArg Complex.re hchar
    _ = Real.exp (-a ^ 2 / 2) := by
      rw [show
          (a : ℂ) * (0 : ℂ) * Complex.I -
              (((1 : NNReal) : ℝ) : ℂ) *
                (a : ℂ) ^ 2 / 2 =
            ((-a ^ 2 / 2 : ℝ) : ℂ) by
          push_cast
          ring,
        Complex.exp_ofReal_re]

lemma abs_sin_mul_div_le (a u : ℝ) :
    |Real.sin (a * u) / u| ≤ |a| := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [abs_div]
    have hsin : |Real.sin (a * u)| ≤ |a * u| :=
      abs_sin_le_abs
    calc
      |Real.sin (a * u)| / |u| ≤ |a * u| / |u| := by
        gcongr
      _ = |a| := by
        rw [abs_mul]
        field_simp [abs_ne_zero.mpr hu]

lemma integrable_gaussianPDFReal_mul_sin_div (a : ℝ) :
    Integrable (fun u : ℝ =>
      gaussianPDFReal 0 1 u * Real.sin (a * u) / u) := by
  apply ((integrable_gaussianPDFReal 0 1).const_mul |a|).mono'
  · exact
      (((measurable_gaussianPDFReal 0 1).mul
        (Real.measurable_sin.comp
          (measurable_const.mul measurable_id))).div
          measurable_id).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 u)]
    have hratio := abs_sin_mul_div_le a u
    rw [abs_div] at hratio
    calc
      gaussianPDFReal 0 1 u * |Real.sin (a * u)| / |u| =
          gaussianPDFReal 0 1 u *
            (|Real.sin (a * u)| / |u|) := by ring
      _ ≤ gaussianPDFReal 0 1 u * |a| :=
        mul_le_mul_of_nonneg_left hratio
          (gaussianPDFReal_nonneg 0 1 u)
      _ = |a| * gaussianPDFReal 0 1 u := mul_comm _ _

lemma gaussianPDFSineIntegrand_hasDerivAt
    (a : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt
      (fun x : ℝ =>
        gaussianPDFReal 0 1 u * Real.sin (x * u) / u)
      (gaussianPDFReal 0 1 u * Real.cos (a * u)) a := by
  have hsin :
      HasDerivAt (fun x : ℝ => Real.sin (x * u))
        (Real.cos (a * u) * u) a := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin (a * u)).comp a
        ((hasDerivAt_id a).mul_const u)
  simpa [hu, mul_comm, mul_left_comm, mul_assoc] using
    ((hasDerivAt_const a (gaussianPDFReal 0 1 u)).mul
      hsin).div_const u

/-- The Gaussian-weighted sine integral used in the principal-value inversion formula. -/
noncomputable def gaussianSinePV (a : ℝ) : ℝ :=
  ∫ u : ℝ, gaussianPDFReal 0 1 u *
    Real.sin (a * u) / u

lemma hasDerivAt_gaussianSinePV (a : ℝ) :
    HasDerivAt gaussianSinePV
      (Real.exp (-a ^ 2 / 2)) a := by
  have hparam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume)
      (bound := fun u : ℝ => gaussianPDFReal 0 1 u)
      (F := fun x u : ℝ =>
        gaussianPDFReal 0 1 u * Real.sin (x * u) / u)
      (F' := fun x u : ℝ =>
        gaussianPDFReal 0 1 u * Real.cos (x * u))
      (x₀ := a) (s := Set.univ)
      (Filter.univ_mem)
      (Filter.Eventually.of_forall fun x =>
        (integrable_gaussianPDFReal_mul_sin_div x).aestronglyMeasurable)
      (integrable_gaussianPDFReal_mul_sin_div a)
      (by fun_prop)
      (by
        filter_upwards with u
        intro x hx
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (gaussianPDFReal_nonneg 0 1 u)]
        calc
          gaussianPDFReal 0 1 u * |Real.cos (x * u)| ≤
              gaussianPDFReal 0 1 u * 1 := by
            exact mul_le_mul_of_nonneg_left
              (abs_cos_le_one (x * u))
              (gaussianPDFReal_nonneg 0 1 u)
          _ = gaussianPDFReal 0 1 u := mul_one _)
      (integrable_gaussianPDFReal 0 1)
      (by
        filter_upwards [(volume : Measure ℝ).ae_ne 0] with u hu
        intro x hx
        exact gaussianPDFSineIntegrand_hasDerivAt x hu)
  change HasDerivAt
    (fun x : ℝ =>
      ∫ u : ℝ, gaussianPDFReal 0 1 u *
        Real.sin (x * u) / u)
    (Real.exp (-a ^ 2 / 2)) a
  rw [integral_gaussianPDFReal_mul_cos] at hparam
  exact hparam.2

/-- The normalization constant `2 / sqrt (2π)` for Gaussian inversion. -/
noncomputable def gaussianInversionConstant : ℝ :=
  2 * (Real.sqrt (2 * Real.pi))⁻¹

/-- The normalized Gaussian principal-value inversion term at `a`. -/
noncomputable def gaussianPVInversion (a : ℝ) : ℝ :=
  gaussianInversionConstant * gaussianSinePV a

lemma gaussianInversionConstant_mul_exp (a : ℝ) :
    gaussianInversionConstant * Real.exp (-a ^ 2 / 2) =
      2 * gaussianPDFReal 0 1 a := by
  simp only [gaussianInversionConstant, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  ring

lemma hasDerivAt_gaussianPVInversion (a : ℝ) :
    HasDerivAt gaussianPVInversion
      (2 * gaussianPDFReal 0 1 a) a := by
  have h :=
    (hasDerivAt_gaussianSinePV a).const_mul
      gaussianInversionConstant
  rw [gaussianInversionConstant_mul_exp] at h
  change HasDerivAt
    (fun y : ℝ =>
      gaussianInversionConstant * gaussianSinePV y)
    (2 * gaussianPDFReal 0 1 a) a
  exact h

lemma gaussianPVInversion_zero :
    gaussianPVInversion 0 = 0 := by
  simp [gaussianPVInversion, gaussianSinePV]

lemma gaussianPVInversion_eq_intervalIntegral (a : ℝ) :
    gaussianPVInversion a =
      ∫ x : ℝ in 0..a, 2 * gaussianPDFReal 0 1 x := by
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := a)
      (f := gaussianPVInversion)
      (f' := fun x : ℝ => 2 * gaussianPDFReal 0 1 x)
      (fun x hx => hasDerivAt_gaussianPVInversion x)
      ((integrable_gaussianPDFReal 0 1).const_mul 2).intervalIntegrable
  rw [gaussianPVInversion_zero, sub_zero] at hFTC
  exact hFTC.symm

lemma gaussianReal_real_Iic_eq_integral (a : ℝ) :
    (gaussianReal 0 1).real (Set.Iic a) =
      ∫ x : ℝ in Set.Iic a, gaussianPDFReal 0 1 x := by
  rw [Measure.real,
    gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg
    (fun x => gaussianPDFReal_nonneg 0 1 x)

lemma integral_gaussianPDFReal_Iic_zero_eq_half :
    (∫ x : ℝ in Set.Iic 0, gaussianPDFReal 0 1 x) =
      1 / 2 := by
  have hsymm :
      (∫ x : ℝ in Set.Ioi 0, gaussianPDFReal 0 1 x) =
        ∫ x : ℝ in Set.Iic 0, gaussianPDFReal 0 1 x := by
    simpa [gaussianPDFReal] using
      (integral_comp_neg_Iic (0 : ℝ)
        (gaussianPDFReal 0 1)).symm
  have htotal :=
    intervalIntegral.integral_Iic_add_Ioi
      (b := (0 : ℝ))
      (f := gaussianPDFReal 0 1)
      (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn
  rw [integral_gaussianPDFReal_eq_one 0 one_ne_zero] at htotal
  linarith

lemma gaussianReal_real_Iic_zero_eq_half :
    (gaussianReal 0 1).real (Set.Iic 0) = 1 / 2 := by
  rw [gaussianReal_real_Iic_eq_integral,
    integral_gaussianPDFReal_Iic_zero_eq_half]

lemma gaussianReal_real_Iic_sub_half (a : ℝ) :
    (gaussianReal 0 1).real (Set.Iic a) - 1 / 2 =
      ∫ x : ℝ in 0..a, gaussianPDFReal 0 1 x := by
  rw [← gaussianReal_real_Iic_zero_eq_half,
    gaussianReal_real_Iic_eq_integral,
    gaussianReal_real_Iic_eq_integral]
  exact intervalIntegral.integral_Iic_sub_Iic
    (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn

/-- Exact Gaussian sine-integral inversion in cdf form. -/
lemma gaussianPVInversion_eq_cdf (a : ℝ) :
    gaussianPVInversion a =
      2 * (gaussianReal 0 1).real (Set.Iic a) - 1 := by
  rw [gaussianPVInversion_eq_intervalIntegral,
    intervalIntegral.integral_const_mul]
  have h := gaussianReal_real_Iic_sub_half a
  linarith

lemma gaussianInversionConstant_mul_pdf (u : ℝ) :
    gaussianInversionConstant * gaussianPDFReal 0 1 u =
      Real.exp (-u ^ 2 / 2) / Real.pi := by
  simp only [gaussianInversionConstant, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  have hsqrt :
      Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) =
        2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hsqrt0 : Real.sqrt (2 * Real.pi) ≠ 0 := by
    positivity
  field_simp [hsqrt0, Real.pi_ne_zero]
  nlinarith

/-- The normalized principal-value integral written with the unnormalized
Gaussian characteristic function.  The integrand is defined to be zero at
the origin by Lean's division convention. -/
lemma gaussianPVInversion_eq_raw_integral (a : ℝ) :
    gaussianPVInversion a =
      ∫ u : ℝ, Real.exp (-u ^ 2 / 2) *
        Real.sin (a * u) / (Real.pi * u) := by
  rw [gaussianPVInversion, gaussianSinePV,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  calc
    gaussianInversionConstant *
        (gaussianPDFReal 0 1 u *
          Real.sin (a * u) / u) =
        (gaussianInversionConstant *
          gaussianPDFReal 0 1 u) *
          Real.sin (a * u) / u := by ring
    _ = (Real.exp (-u ^ 2 / 2) / Real.pi) *
          Real.sin (a * u) / u := by
      rw [gaussianInversionConstant_mul_pdf]
    _ = Real.exp (-u ^ 2 / 2) *
          Real.sin (a * u) / (Real.pi * u) := by ring

/-- Exact full-line Gaussian sine inversion in its classical form. -/
lemma gaussian_raw_sine_inversion (a : ℝ) :
    ∫ u : ℝ, Real.exp (-u ^ 2 / 2) *
        Real.sin (a * u) / (Real.pi * u) =
      2 * (gaussianReal 0 1).real (Set.Iic a) - 1 := by
  rw [← gaussianPVInversion_eq_raw_integral,
    gaussianPVInversion_eq_cdf]

lemma integral_sq_mul_gaussianPDFReal_eq_one :
    ∫ u : ℝ, u ^ 2 * gaussianPDFReal 0 1 u = 1 := by
  have hvar :=
    variance_fun_id_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral measurable_id'.aemeasurable,
    integral_id_gaussianReal,
    integral_gaussianReal_eq_integral_smul one_ne_zero] at hvar
  simpa [smul_eq_mul, mul_comm] using hvar

lemma integrable_sq_mul_gaussianPDFReal :
    Integrable (fun u : ℝ => u ^ 2 * gaussianPDFReal 0 1 u) := by
  have h :=
    (integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (2 : ℝ)) (by norm_num)).const_mul
        (Real.sqrt (2 * Real.pi))⁻¹
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one,
    sub_zero, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2),
    Real.rpow_two] at *
  convert h using 1
  funext u
  ring

/-- The unnormalized Gaussian sine-inversion kernel at threshold `a` and frequency `u`. -/
noncomputable def gaussianRawSineKernel (a u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / 2) * Real.sin (a * u) /
    (Real.pi * u)

lemma gaussianRawSineKernel_eq (a u : ℝ) :
    gaussianRawSineKernel a u =
      gaussianInversionConstant *
        (gaussianPDFReal 0 1 u * Real.sin (a * u) / u) := by
  rw [gaussianRawSineKernel]
  calc
    Real.exp (-u ^ 2 / 2) * Real.sin (a * u) /
        (Real.pi * u) =
      (Real.exp (-u ^ 2 / 2) / Real.pi) *
        Real.sin (a * u) / u := by ring
    _ = (gaussianInversionConstant *
        gaussianPDFReal 0 1 u) *
          Real.sin (a * u) / u := by
      rw [gaussianInversionConstant_mul_pdf]
    _ = _ := by ring

lemma integrable_gaussianRawSineKernel (a : ℝ) :
    Integrable (gaussianRawSineKernel a) := by
  have h :=
    (integrable_gaussianPDFReal_mul_sin_div a).const_mul
      gaussianInversionConstant
  exact h.congr (ae_of_all _ fun u =>
    (gaussianRawSineKernel_eq a u).symm)

lemma gaussianInversionConstant_nonneg :
    0 ≤ gaussianInversionConstant := by
  unfold gaussianInversionConstant
  positivity

lemma gaussianRawSineKernel_abs_le_moment
    {T : ℝ} (hT : 0 < T) (a u : ℝ)
    (hu : T ≤ |u|) :
    |gaussianRawSineKernel a u| ≤
      (gaussianInversionConstant / T ^ 3) *
        (u ^ 2 * gaussianPDFReal 0 1 u) := by
  have hu0 : 0 < |u| := lt_of_lt_of_le hT hu
  have hT3 : 0 < T ^ 3 := pow_pos hT 3
  have hcube : T ^ 3 ≤ |u| ^ 3 := by
    exact pow_le_pow_left₀ hT.le hu 3
  have hinv :
      1 / |u| ≤ u ^ 2 / T ^ 3 := by
    apply (div_le_div_iff₀ hu0 hT3).2
    simpa [pow_succ, sq_abs, mul_comm,
      mul_left_comm, mul_assoc] using hcube
  rw [gaussianRawSineKernel_eq, abs_mul,
    abs_div, abs_mul,
    abs_of_nonneg gaussianInversionConstant_nonneg,
    abs_of_nonneg (gaussianPDFReal_nonneg 0 1 u)]
  calc
    gaussianInversionConstant *
          (gaussianPDFReal 0 1 u *
            |Real.sin (a * u)| / |u|) =
        gaussianInversionConstant *
          (gaussianPDFReal 0 1 u *
            (|Real.sin (a * u)| / |u|)) := by ring
    _ ≤
        gaussianInversionConstant *
          (gaussianPDFReal 0 1 u * (1 / |u|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (abs_sin_le_one (a * u)) hu0.le)
          (gaussianPDFReal_nonneg 0 1 u))
        gaussianInversionConstant_nonneg
    _ ≤ gaussianInversionConstant *
          (gaussianPDFReal 0 1 u *
            (u ^ 2 / T ^ 3)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinv
          (gaussianPDFReal_nonneg 0 1 u))
        gaussianInversionConstant_nonneg
    _ = (gaussianInversionConstant / T ^ 3) *
          (u ^ 2 * gaussianPDFReal 0 1 u) := by ring

lemma abs_integral_gaussianRawSineKernel_compl_le
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    |∫ u : ℝ in (Set.Ioc (-T) T)ᶜ,
        gaussianRawSineKernel a u| ≤
      gaussianInversionConstant / T ^ 3 := by
  let g : ℝ → ℝ := fun u =>
    (gaussianInversionConstant / T ^ 3) *
      (u ^ 2 * gaussianPDFReal 0 1 u)
  have hg : Integrable g :=
    (integrable_sq_mul_gaussianPDFReal.const_mul
      (gaussianInversionConstant / T ^ 3))
  have hg0 : ∀ u : ℝ, 0 ≤ g u := by
    intro u
    dsimp [g]
    exact mul_nonneg
      (div_nonneg gaussianInversionConstant_nonneg
        (pow_nonneg hT.le 3))
      (mul_nonneg (sq_nonneg u)
        (gaussianPDFReal_nonneg 0 1 u))
  have hraw := integrable_gaussianRawSineKernel a
  calc
    |∫ u : ℝ in (Set.Ioc (-T) T)ᶜ,
        gaussianRawSineKernel a u| =
        ‖∫ u : ℝ in (Set.Ioc (-T) T)ᶜ,
          gaussianRawSineKernel a u‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ u : ℝ in (Set.Ioc (-T) T)ᶜ,
        ‖gaussianRawSineKernel a u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in (Set.Ioc (-T) T)ᶜ, g u := by
      apply setIntegral_mono_on
        hraw.norm.integrableOn hg.integrableOn
        measurableSet_Ioc.compl
      intro u hu
      rw [Real.norm_eq_abs]
      have huAbs : T ≤ |u| := by
        simp only [Set.mem_compl_iff, Set.mem_Ioc] at hu
        by_cases hleft : u ≤ -T
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · have hminus : -T < u := lt_of_not_ge hleft
          have hright : T < u := by
            exact lt_of_not_ge (fun hut => hu ⟨hminus, hut⟩)
          rw [abs_of_pos (by linarith)]
          exact hright.le
      exact gaussianRawSineKernel_abs_le_moment hT a u huAbs
    _ ≤ ∫ u : ℝ, g u :=
      setIntegral_le_integral hg
        (ae_of_all _ hg0)
    _ = gaussianInversionConstant / T ^ 3 := by
      dsimp [g]
      rw [MeasureTheory.integral_const_mul,
        integral_sq_mul_gaussianPDFReal_eq_one,
        mul_one]

lemma abs_full_sub_interval_gaussianRawSineKernel_le
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    |(∫ u : ℝ, gaussianRawSineKernel a u) -
        ∫ u : ℝ in -T..T, gaussianRawSineKernel a u| ≤
      gaussianInversionConstant / T ^ 3 := by
  have hle : -T ≤ T := by linarith
  have hraw := integrable_gaussianRawSineKernel a
  have hdiff :
      (∫ u : ℝ, gaussianRawSineKernel a u) -
          ∫ u : ℝ in -T..T, gaussianRawSineKernel a u =
        ∫ u : ℝ in (Set.Ioc (-T) T)ᶜ,
          gaussianRawSineKernel a u := by
    rw [intervalIntegral.integral_of_le hle]
    exact (setIntegral_compl measurableSet_Ioc hraw).symm
  rw [hdiff]
  exact abs_integral_gaussianRawSineKernel_compl_le hT a

/-- A finite-frequency Gaussian inversion formula with a uniform cubic
tail.  This polynomial estimate is sufficient for the Berry--Esseen
parameter range and avoids any conditional-integral argument. -/
lemma gaussian_raw_sine_inversion_truncated
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    |(2 * (gaussianReal 0 1).real (Set.Iic a) - 1) -
        ∫ u : ℝ in -T..T, gaussianRawSineKernel a u| ≤
      gaussianInversionConstant / T ^ 3 := by
  rw [← gaussian_raw_sine_inversion a]
  simpa only [gaussianRawSineKernel] using
    abs_full_sub_interval_gaussianRawSineKernel_le hT a

end HDP.Appendix
