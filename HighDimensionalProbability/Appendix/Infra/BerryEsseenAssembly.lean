import HighDimensionalProbability.Appendix.Infra.BerryEsseenGaussianInversion
import HighDimensionalProbability.Appendix.Infra.BerryEsseenCharacteristic

/-!
# Prawitz smoothing assembly

This file combines the Vaaler cdf majorants, their compact Fourier
representations, and the Prawitz cancellation kernel.  All singular terms
occur only in differences which vanish at the origin.
-/

open Real Complex Filter MeasureTheory ProbabilityTheory intervalIntegral Set
open scoped Interval Topology FourierTransform

namespace HDP.Appendix

lemma integrable_vaalerKFourierProduct
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    Integrable
      (Function.uncurry (fun t y : ℝ =>
        vaalerOsc (y - a) t * ((1 - |t| : ℝ) : ℂ)))
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) := by
  letI : IsFiniteMeasure
      (volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))) := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    infer_instance
  letI : IsFiniteMeasure
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) :=
    inferInstance
  let f : ℝ × ℝ → ℂ := fun z =>
    vaalerOsc (z.2 - a) z.1 * ((1 - |z.1| : ℝ) : ℂ)
  have hf : Measurable f := by
    exact
      (show Measurable (fun z : ℝ × ℝ =>
          vaalerOsc (z.2 - a) z.1) by
        apply Continuous.measurable
        unfold vaalerOsc
        fun_prop).mul
      (show Measurable (fun z : ℝ × ℝ =>
          ((1 - |z.1| : ℝ) : ℂ)) by fun_prop)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    hf.aestronglyMeasurable ?_
  have hp : MeasurableSet {z : ℝ × ℝ | ‖f z‖ ≤ 1} :=
    measurableSet_le hf.norm measurable_const
  apply (Measure.ae_prod_iff_ae_ae hp).2
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  filter_upwards with y
  dsimp [f]
  rw [norm_mul, norm_vaalerOsc, one_mul, norm_real, Real.norm_eq_abs]
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
  have htAbs : |t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  rw [abs_of_nonneg (by linarith)]
  linarith [abs_nonneg t]

/-- Fourier representation of the Vaaler triangle majorant averaged against
a probability measure. -/
lemma integral_vaalerK_sub_fourier
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    ((∫ y : ℝ, vaalerK (y - a) ∂μ : ℝ) : ℂ) =
      ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) *
          ((1 - |t| : ℝ) : ℂ) := by
  let f : ℝ → ℝ → ℂ := fun t y =>
    vaalerOsc (y - a) t * ((1 - |t| : ℝ) : ℂ)
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) := by
    simpa only [f] using integrable_vaalerKFourierProduct μ a
  have hswap := intervalIntegral_integral_swap hf
  calc
    ((∫ y : ℝ, vaalerK (y - a) ∂μ : ℝ) : ℂ) =
        ∫ y : ℝ, (vaalerK (y - a) : ℂ) ∂μ := by
      rw [integral_complex_ofReal]
    _ = ∫ y : ℝ, (∫ t : ℝ in -1..1, f t y) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [show (fun t : ℝ =>
          vaalerOsc (y - a) t * ((1 - |t| : ℝ) : ℂ)) =
          fun t : ℝ =>
            ((1 - |t| : ℝ) : ℂ) * vaalerOsc (y - a) t by
        funext t
        ring,
        intervalIntegral_vaalerTriangleOsc]
    _ = ∫ t : ℝ in -1..1, (∫ y : ℝ, f t y ∂μ) := hswap.symm
    _ = ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) *
          ((1 - |t| : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [f]
      rw [MeasureTheory.integral_mul_const,
        integral_vaalerOsc_sub]

lemma integral_vaalerK_sub_difference_fourier
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) :
    (((∫ y : ℝ, vaalerK (y - a) ∂μ) -
        ∫ y : ℝ, vaalerK (y - a) ∂ν : ℝ) : ℂ) =
      ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          ((1 - |t| : ℝ) : ℂ) := by
  have hμ := integral_vaalerK_sub_fourier μ a
  have hν := integral_vaalerK_sub_fourier ν a
  have hiμ : IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) *
          ((1 - |t| : ℝ) : ℂ)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact ((continuous_vaalerOsc (-a)).mul
      (continuous_charFun.comp (by fun_prop))).mul (by fun_prop)
  have hiν : IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t * charFun ν (2 * Real.pi * t) *
          ((1 - |t| : ℝ) : ℂ)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact ((continuous_vaalerOsc (-a)).mul
      (continuous_charFun.comp (by fun_prop))).mul (by fun_prop)
  rw [ofReal_sub, hμ, hν,
    ← intervalIntegral.integral_sub hiμ hiν]
  apply intervalIntegral.integral_congr
  intro t ht
  unfold vaalerCharDifference
  ring

/-- The real Prawitz inversion integrand built from the centered characteristic function of `ν`. -/
noncomputable def prawitzRawKernel
    (ν : Measure ℝ) (t : ℝ) : ℝ :=
  2 * Complex.re
    ((charFun ν (2 * Real.pi * t) - 1) *
      prawitzSingularKernel t)

/-- The pushforward of `μ` under centering at `a` and scaling by `T / (2π)`. -/
noncomputable def scaledCenteredMeasure
    (μ : Measure ℝ) (a T : ℝ) : Measure ℝ :=
  μ.map (fun x : ℝ =>
    (T / (2 * Real.pi)) * (x - a))

noncomputable instance instIsProbabilityMeasureScaledCentered
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a T : ℝ) :
    IsProbabilityMeasure (scaledCenteredMeasure μ a T) := by
  unfold scaledCenteredMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma cdf_scaledCenteredMeasure_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a T : ℝ} (hT : 0 < T) :
    cdf (scaledCenteredMeasure μ a T) 0 = cdf μ a := by
  rw [cdf_eq_real, cdf_eq_real]
  unfold scaledCenteredMeasure
  rw [Measure.real, Measure.real,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  have hscale : 0 < T / (2 * Real.pi) := by positivity
  constructor
  · intro hx
    nlinarith
  · intro hx
    exact mul_nonpos_of_nonneg_of_nonpos hscale.le (sub_nonpos.mpr hx)

lemma charFun_scaledCenteredMeasure_vaaler
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a T t : ℝ) :
    charFun (scaledCenteredMeasure μ a T)
        (2 * Real.pi * t) =
      Complex.exp (((-a * T * t : ℝ) : ℂ) * Complex.I) *
        charFun μ (T * t) := by
  rw [charFun_apply_real]
  unfold scaledCenteredMeasure
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  rw [charFun_apply_real]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

lemma charFun_scaledCenteredGaussian_vaaler
    (a T t : ℝ) :
    charFun
        (scaledCenteredMeasure (gaussianReal 0 1) a T)
        (2 * Real.pi * t) =
      Complex.exp (((-a * T * t : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-(T * t) ^ 2 / 2) : ℂ) := by
  rw [charFun_scaledCenteredMeasure_vaaler,
    charFun_gaussianReal]
  congr 1
  norm_num
  congr 1
  ring

lemma prawitzRawKernel_scaledCenteredGaussian
    (a T t : ℝ) :
    prawitzRawKernel
        (scaledCenteredMeasure (gaussianReal 0 1) a T) t =
      T * gaussianRawSineKernel a (T * t) := by
  rw [prawitzRawKernel, charFun_scaledCenteredGaussian_vaaler,
    gaussianRawSineKernel]
  by_cases hT : T = 0
  · subst T
    simp [prawitzSingularKernel]
  by_cases ht : t = 0
  · subst t
    simp [prawitzSingularKernel]
  let g : ℝ := Real.exp (-(T * t) ^ 2 / 2)
  let θ : ℝ := a * T * t
  let z : ℂ :=
    Complex.exp (((-a * T * t : ℝ) : ℂ) * Complex.I) *
      (g : ℂ) - 1
  let S : ℂ := prawitzSingularKernel t
  have hexpre :
      (Complex.exp (((-a * T * t : ℝ) : ℂ) *
        Complex.I)).re =
        Real.cos (-a * T * t) :=
    Complex.exp_ofReal_mul_I_re (-a * T * t)
  have hexpim :
      (Complex.exp (((-a * T * t : ℝ) : ℂ) *
        Complex.I)).im =
        Real.sin (-a * T * t) :=
    Complex.exp_ofReal_mul_I_im (-a * T * t)
  have hzre : z.re = g * Real.cos θ - 1 := by
    dsimp [z]
    rw [Complex.mul_re, hexpre, hexpim]
    simp [θ, Real.cos_neg]
    ring
  have hzim : z.im = -(g * Real.sin θ) := by
    dsimp [z]
    rw [Complex.mul_im, hexpre, hexpim]
    simp [θ, Real.sin_neg]
    ring
  have hSre : S.re = 0 := by
    dsimp [S, prawitzSingularKernel]
    simp [Complex.div_re]
  have hSim : S.im = 1 / (2 * Real.pi * t) := by
    dsimp [S, prawitzSingularKernel]
    simp [Complex.div_im]
    field_simp [Real.pi_ne_zero, ht]
  change 2 * (z * S).re =
    T * (Real.exp (-(T * t) ^ 2 / 2) *
      Real.sin (a * (T * t)) / (Real.pi * (T * t)))
  rw [Complex.mul_re, hzre, hzim, hSre, hSim]
  dsimp [g, θ]
  field_simp [Real.pi_ne_zero, hT, ht]
  ring

lemma intervalIntegrable_prawitzRawKernel_scaledCenteredGaussian
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    IntervalIntegrable
      (prawitzRawKernel
        (scaledCenteredMeasure (gaussianReal 0 1) a T))
      volume (-1) 1 := by
  have hcompFull : Integrable
      (fun t : ℝ => gaussianRawSineKernel a (T * t)) :=
    (integrable_comp_mul_left_iff
      (gaussianRawSineKernel a) (ne_of_gt hT)).2
        (integrable_gaussianRawSineKernel a)
  have hcomp : IntervalIntegrable
      (fun t : ℝ => gaussianRawSineKernel a (T * t))
      volume (-1) 1 :=
    hcompFull.intervalIntegrable
  have hmul := hcomp.const_mul T
  apply IntervalIntegrable.congr (fun t ht => ?_) hmul
  exact (prawitzRawKernel_scaledCenteredGaussian a T t).symm

lemma intervalIntegral_prawitzRawKernel_scaledCenteredGaussian
    (a : ℝ) (T : ℝ) :
    (∫ t : ℝ in -1..1,
      prawitzRawKernel
        (scaledCenteredMeasure (gaussianReal 0 1) a T) t) =
      ∫ u : ℝ in -T..T, gaussianRawSineKernel a u := by
  simp_rw [prawitzRawKernel_scaledCenteredGaussian]
  rw [intervalIntegral.integral_const_mul]
  simpa only [mul_neg, mul_one, mul_neg_one] using
    (intervalIntegral.mul_integral_comp_mul_left
      (f := gaussianRawSineKernel a)
      (a := (-1 : ℝ)) (b := 1) T)

lemma scaledCenteredGaussian_inversion
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    |(2 * cdf
        (scaledCenteredMeasure (gaussianReal 0 1) a T) 0 - 1) -
        ∫ t : ℝ in -1..1,
          prawitzRawKernel
            (scaledCenteredMeasure
              (gaussianReal 0 1) a T) t| ≤
      gaussianInversionConstant / T ^ 3 := by
  rw [cdf_scaledCenteredMeasure_zero
      (gaussianReal 0 1) hT,
    intervalIntegral_prawitzRawKernel_scaledCenteredGaussian]
  simpa only [cdf_eq_real] using
    gaussian_raw_sine_inversion_truncated hT a

lemma norm_vaalerCharDifference_scaledCenteredGaussian_dirac_le
    {T : ℝ} (hT : 0 < T) (a t : ℝ)
    (ht : |t| ≤ 1 / 2) :
    ‖vaalerCharDifference
        (scaledCenteredMeasure (gaussianReal 0 1) a T)
        (Measure.dirac 0) t‖ ≤
      (2 * (|a| * T + T ^ 2 / 4)) * |t| := by
  let L : ℝ := |a| * T + T ^ 2 / 4
  let x : ℂ :=
    (((-a * T * t : ℝ) : ℂ) * Complex.I) +
      (((-(T * t) ^ 2 / 2 : ℝ) : ℂ))
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have htSq : t ^ 2 ≤ |t| / 2 := by
    rw [← sq_abs]
    nlinarith
  have hxnorm : ‖x‖ ≤ L * |t| := by
    calc
      ‖x‖ ≤
          ‖(((-a * T * t : ℝ) : ℂ) * Complex.I)‖ +
            ‖(((-(T * t) ^ 2 / 2 : ℝ) : ℂ))‖ :=
        norm_add_le _ _
      _ = (T * t) ^ 2 / 2 + |a * T * t| := by
        have hlinear :
            |-a * T * t| = |a * T * t| := by
          rw [show -a * T * t = -(a * T * t) by ring, abs_neg]
        have hquadratic :
            |-(T * t) ^ 2 / 2| = (T * t) ^ 2 / 2 := by
          have hn : -(T * t) ^ 2 / 2 ≤ 0 := by
            nlinarith [sq_nonneg (T * t)]
          rw [abs_of_nonpos hn]
          ring
        rw [norm_real, norm_mul, norm_real, norm_I,
          Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
          hlinear, hquadratic]
        ring
      _ ≤ L * |t| := by
        rw [abs_mul, abs_mul, abs_of_pos hT]
        dsimp [L]
        have hmul :=
          mul_le_mul_of_nonneg_left htSq (sq_nonneg T)
        nlinarith
  have hchar :
      vaalerCharDifference
          (scaledCenteredMeasure (gaussianReal 0 1) a T)
          (Measure.dirac 0) t =
        Complex.exp x - 1 := by
    rw [vaalerCharDifference,
      charFun_scaledCenteredGaussian_vaaler]
    simp only [charFun_dirac, inner_zero_left,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    have hexpReal :
        (Real.exp (-(T * t) ^ 2 / 2) : ℂ) =
          Complex.exp (((-(T * t) ^ 2 / 2 : ℝ) : ℂ)) := by
      apply Complex.ext
      · simp [Complex.exp_ofReal_re]
      · simp [Complex.exp_ofReal_im]
    rw [hexpReal]
    rw [← Complex.exp_add]
  rw [hchar]
  by_cases hx : ‖x‖ ≤ 1
  · calc
      ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖ :=
        Complex.norm_exp_sub_one_le hx
      _ ≤ 2 * (L * |t|) :=
        mul_le_mul_of_nonneg_left hxnorm (by norm_num)
      _ = (2 * (|a| * T + T ^ 2 / 4)) * |t| := by
        dsimp [L]
        ring
  · have hxlarge : 1 < L * |t| :=
      lt_of_not_ge hx |>.trans_le hxnorm
    have htwo : (2 : ℝ) ≤ 2 * (L * |t|) := by
      nlinarith
    calc
      ‖Complex.exp x - 1‖ ≤
          ‖Complex.exp x‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := by
        have hxre : x.re ≤ 0 := by
          dsimp [x]
          simp
          nlinarith [sq_nonneg (T * t)]
        rw [Complex.norm_exp]
        exact add_le_add (Real.exp_le_one_iff.mpr hxre) (by norm_num)
      _ ≤ 2 * (L * |t|) := by norm_num at htwo ⊢; exact htwo
      _ = (2 * (|a| * T + T ^ 2 / 4)) * |t| := by
        dsimp [L]
        ring

lemma prawitzRawKernel_eq
    (ν : Measure ℝ) (t : ℝ) :
    prawitzRawKernel ν t =
      2 * Complex.re
        ((charFun ν (2 * Real.pi * t) - 1) *
          prawitzSingularKernel t) := rfl

lemma two_mul_re_prawitzKernel_sub_singular
    (t : ℝ) :
    2 * Complex.re
        (prawitzKernel t - prawitzSingularKernel t) =
      1 - |t| := by
  unfold prawitzKernel prawitzSingularKernel
  simp [Complex.div_re, Complex.mul_re]
  ring

lemma triangle_add_vaalerHLimitKernel_eq_two_prawitzKernel_neg
    (t : ℝ) :
    ((1 - |t| : ℝ) : ℂ) + vaalerHLimitKernel t =
      2 * prawitzKernel (-t) := by
  have h := congrArg (starRingEnd ℂ)
    (triangle_sub_vaalerHLimitKernel t)
  have hH :
      (starRingEnd ℂ) (vaalerHLimitKernel t) =
        -vaalerHLimitKernel t := by
    let A : ℝ :=
      (1 - |t|) * Real.cot (Real.pi * t) +
        Real.sign t / Real.pi
    change (starRingEnd ℂ) (-Complex.I * (A : ℂ)) =
      -(-Complex.I * (A : ℂ))
    simp
  rw [map_sub, map_mul, hH, ← prawitzKernel_neg] at h
  simpa only [map_ofNat, Complex.conj_ofReal, sub_neg_eq_add] using h

lemma intervalIntegral_triangle_real :
    (∫ t : ℝ in -1..1, (1 - |t|)) = 1 := by
  have hneg : IntervalIntegrable
      (fun t : ℝ => 1 - |t|) volume (-1) 0 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpos : IntervalIntegrable
      (fun t : ℝ => 1 - |t|) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← integral_add_adjacent_intervals hneg hpos]
  have hleft :
      (∫ t : ℝ in -1..0, (1 - |t|)) =
        ∫ t : ℝ in -1..0, (1 + t) := by
    apply integral_congr
    intro t ht
    change 1 - |t| = 1 + t
    rw [abs_of_nonpos (by simpa using ht.2)]
    ring
  have hright :
      (∫ t : ℝ in 0..1, (1 - |t|)) =
        ∫ t : ℝ in 0..1, (1 - t) := by
    apply integral_congr
    intro t ht
    change 1 - |t| = 1 - t
    rw [abs_of_nonneg (by simpa using ht.1)]
  rw [hleft, hright]
  rw [intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const,
    integral_id, integral_id]
  norm_num

lemma intervalIntegrable_charDifference_mul_prawitzKernel
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t * prawitzKernel t)
      volume (-1) 1 := by
  have hH0 := intervalIntegrable_vaalerCharLimitKernel
    μ ν hC hsmall 0
  have hH : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t * vaalerHLimitKernel t)
      volume (-1) 1 := by
    apply IntervalIntegrable.congr (fun t ht => ?_) hH0
    simp [vaalerOsc_zero]
  have htri : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t *
          ((1 - |t| : ℝ) : ℂ))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_charFun.comp (by fun_prop) |>.sub
      (continuous_charFun.comp (by fun_prop))).mul (by fun_prop)
  have hsub := htri.sub hH
  have hhalf := hsub.const_mul (1 / 2 : ℂ)
  apply IntervalIntegrable.congr (fun t ht => ?_) hhalf
  have hk := triangle_sub_vaalerHLimitKernel t
  calc
    (1 / 2 : ℂ) *
        (vaalerCharDifference μ ν t * ((1 - |t| : ℝ) : ℂ) -
          vaalerCharDifference μ ν t * vaalerHLimitKernel t) =
      vaalerCharDifference μ ν t *
        ((1 / 2 : ℂ) *
          (((1 - |t| : ℝ) : ℂ) - vaalerHLimitKernel t)) := by
        ring
    _ = vaalerCharDifference μ ν t * prawitzKernel t := by
      rw [hk]
      ring

lemma intervalIntegrable_charDifference_mul_prawitzKernel_neg
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t * prawitzKernel (-t))
      volume (-1) 1 := by
  have hH0 := intervalIntegrable_vaalerCharLimitKernel
    μ ν hC hsmall 0
  have hH : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t * vaalerHLimitKernel t)
      volume (-1) 1 := by
    apply IntervalIntegrable.congr (fun t ht => ?_) hH0
    simp [vaalerOsc_zero]
  have htri : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t *
          ((1 - |t| : ℝ) : ℂ))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_charFun.comp (by fun_prop) |>.sub
      (continuous_charFun.comp (by fun_prop))).mul (by fun_prop)
  have hadd := htri.add hH
  have hhalf := hadd.const_mul (1 / 2 : ℂ)
  apply IntervalIntegrable.congr (fun t ht => ?_) hhalf
  have hk :
      2 * prawitzKernel (-t) =
        ((1 - |t| : ℝ) : ℂ) + vaalerHLimitKernel t := by
    exact (triangle_add_vaalerHLimitKernel_eq_two_prawitzKernel_neg t).symm
  calc
    (1 / 2 : ℂ) *
        (vaalerCharDifference μ ν t * ((1 - |t| : ℝ) : ℂ) +
          vaalerCharDifference μ ν t * vaalerHLimitKernel t) =
      vaalerCharDifference μ ν t *
        ((1 / 2 : ℂ) *
          (((1 - |t| : ℝ) : ℂ) + vaalerHLimitKernel t)) := by
        ring
    _ = vaalerCharDifference μ ν t * prawitzKernel (-t) := by
      rw [← hk]
      ring

lemma intervalIntegrable_prawitzKernel_sub_singular :
    IntervalIntegrable
      (fun t : ℝ =>
        prawitzKernel t - prawitzSingularKernel t)
      volume (-1) 1 := by
  have htri : IntervalIntegrable
      (fun t : ℝ => ((1 - |t| : ℝ) : ℂ))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hreg := intervalIntegrable_vaalerHLimitKernel_add_two_singular
  have hsub := htri.sub hreg
  have hhalf := hsub.const_mul (1 / 2 : ℂ)
  apply IntervalIntegrable.congr (fun t ht => ?_) hhalf
  rw [vaalerHLimitKernel_add_two_singular]
  ring

lemma intervalIntegrable_prawitzKernel_neg_sub_singular_neg :
    IntervalIntegrable
      (fun t : ℝ =>
        prawitzKernel (-t) - prawitzSingularKernel (-t))
      volume (-1) 1 := by
  have htri : IntervalIntegrable
      (fun t : ℝ => ((1 - |t| : ℝ) : ℂ))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hreg := intervalIntegrable_vaalerHLimitKernel_add_two_singular
  have hadd := htri.add hreg
  have hhalf := hadd.const_mul (1 / 2 : ℂ)
  apply IntervalIntegrable.congr (fun t ht => ?_) hhalf
  have hk :
      2 * prawitzKernel (-t) =
        ((1 - |t| : ℝ) : ℂ) + vaalerHLimitKernel t := by
    exact (triangle_add_vaalerHLimitKernel_eq_two_prawitzKernel_neg t).symm
  calc
    (1 / 2 : ℂ) *
        (((1 - |t| : ℝ) : ℂ) +
          (vaalerHLimitKernel t + 2 * prawitzSingularKernel t)) =
      (1 / 2 : ℂ) *
        ((((1 - |t| : ℝ) : ℂ) + vaalerHLimitKernel t) +
          2 * prawitzSingularKernel t) := by ring
    _ = prawitzKernel (-t) + prawitzSingularKernel t := by
      rw [← hk]
      ring
    _ = prawitzKernel (-t) - prawitzSingularKernel (-t) := by
      rw [prawitzSingularKernel_neg]
      ring

lemma intervalIntegrable_charFun_mul_prawitzRegular
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IntervalIntegrable
      (fun t : ℝ =>
        charFun ν (2 * Real.pi * t) *
          (prawitzKernel t - prawitzSingularKernel t))
      volume (-1) 1 := by
  have hc : Continuous (fun t : ℝ =>
      charFun ν (2 * Real.pi * t)) :=
    (continuous_charFun (μ := ν)).comp (by fun_prop)
  have h :=
    intervalIntegrable_prawitzKernel_sub_singular.mul_continuousOn
      hc.continuousOn
  apply IntervalIntegrable.congr (fun t ht => by ring) h

lemma intervalIntegrable_charFun_mul_prawitzRegular_neg
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IntervalIntegrable
      (fun t : ℝ =>
        charFun ν (2 * Real.pi * t) *
          (prawitzKernel (-t) - prawitzSingularKernel (-t)))
      volume (-1) 1 := by
  have hc : Continuous (fun t : ℝ =>
      charFun ν (2 * Real.pi * t)) :=
    (continuous_charFun (μ := ν)).comp (by fun_prop)
  have h :=
    intervalIntegrable_prawitzKernel_neg_sub_singular_neg.mul_continuousOn
      hc.continuousOn
  apply IntervalIntegrable.congr (fun t ht => by ring) h

lemma prawitz_upper_difference_fourier
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|) :
    (((-(∫ y : ℝ, vaalerH y ∂μ) +
          ∫ y : ℝ, vaalerK y ∂μ) -
        (-(∫ y : ℝ, vaalerH y ∂ν) +
          ∫ y : ℝ, vaalerK y ∂ν) : ℝ) : ℂ) =
      2 * ∫ t : ℝ in -1..1,
        vaalerCharDifference μ ν t * prawitzKernel t := by
  have hH0 :=
    integral_vaalerH_sub_difference_fourier_limit
      μ ν hC hsmall 0
  have hH :
      ((((∫ y : ℝ, vaalerH y ∂μ) -
          ∫ y : ℝ, vaalerH y ∂ν : ℝ) : ℂ)) =
        ∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t *
            vaalerHLimitKernel t := by
    simpa [vaalerOsc_zero] using hH0
  have hK0 := integral_vaalerK_sub_difference_fourier μ ν 0
  have hK :
      ((((∫ y : ℝ, vaalerK y ∂μ) -
          ∫ y : ℝ, vaalerK y ∂ν : ℝ) : ℂ)) =
        ∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t *
            ((1 - |t| : ℝ) : ℂ) := by
    simpa [vaalerOsc_zero] using hK0
  have hiH := intervalIntegrable_vaalerCharLimitKernel
    μ ν hC hsmall 0
  have hiH' : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t *
          vaalerHLimitKernel t) volume (-1) 1 := by
    apply IntervalIntegrable.congr (fun t ht => ?_) hiH
    simp [vaalerOsc_zero]
  have hiK : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t *
          ((1 - |t| : ℝ) : ℂ)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_charFun.comp (by fun_prop) |>.sub
      (continuous_charFun.comp (by fun_prop))).mul (by fun_prop)
  calc
    (((-(∫ y : ℝ, vaalerH y ∂μ) +
            ∫ y : ℝ, vaalerK y ∂μ) -
          (-(∫ y : ℝ, vaalerH y ∂ν) +
            ∫ y : ℝ, vaalerK y ∂ν) : ℝ) : ℂ) =
        -((((∫ y : ℝ, vaalerH y ∂μ) -
            ∫ y : ℝ, vaalerH y ∂ν : ℝ) : ℂ)) +
          ((((∫ y : ℝ, vaalerK y ∂μ) -
            ∫ y : ℝ, vaalerK y ∂ν : ℝ) : ℂ)) := by
      push_cast
      ring
    _ = -(∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t * vaalerHLimitKernel t) +
        ∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t *
            ((1 - |t| : ℝ) : ℂ) := by rw [hH, hK]
    _ = ∫ t : ℝ in -1..1,
        (vaalerCharDifference μ ν t *
            ((1 - |t| : ℝ) : ℂ) -
          vaalerCharDifference μ ν t *
            vaalerHLimitKernel t) := by
      rw [intervalIntegral.integral_sub hiK hiH']
      ring
    _ = ∫ t : ℝ in -1..1,
        2 * (vaalerCharDifference μ ν t *
          prawitzKernel t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change
        vaalerCharDifference μ ν t * ((1 - |t| : ℝ) : ℂ) -
            vaalerCharDifference μ ν t * vaalerHLimitKernel t =
          2 * (vaalerCharDifference μ ν t * prawitzKernel t)
      have hk := triangle_sub_vaalerHLimitKernel t
      calc
        vaalerCharDifference μ ν t * ((1 - |t| : ℝ) : ℂ) -
            vaalerCharDifference μ ν t * vaalerHLimitKernel t =
          vaalerCharDifference μ ν t *
            (((1 - |t| : ℝ) : ℂ) - vaalerHLimitKernel t) := by ring
        _ = 2 * (vaalerCharDifference μ ν t * prawitzKernel t) := by
          rw [hk]
          ring
    _ = 2 * ∫ t : ℝ in -1..1,
        vaalerCharDifference μ ν t * prawitzKernel t := by
      rw [intervalIntegral.integral_const_mul]

lemma prawitz_lower_difference_fourier
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|) :
    ((((∫ y : ℝ, vaalerH y ∂μ) +
          ∫ y : ℝ, vaalerK y ∂μ) -
        ((∫ y : ℝ, vaalerH y ∂ν) +
          ∫ y : ℝ, vaalerK y ∂ν) : ℝ) : ℂ) =
      2 * ∫ t : ℝ in -1..1,
        vaalerCharDifference μ ν t * prawitzKernel (-t) := by
  have hH0 :=
    integral_vaalerH_sub_difference_fourier_limit
      μ ν hC hsmall 0
  have hH :
      ((((∫ y : ℝ, vaalerH y ∂μ) -
          ∫ y : ℝ, vaalerH y ∂ν : ℝ) : ℂ)) =
        ∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t *
            vaalerHLimitKernel t := by
    simpa [vaalerOsc_zero] using hH0
  have hK0 := integral_vaalerK_sub_difference_fourier μ ν 0
  have hK :
      ((((∫ y : ℝ, vaalerK y ∂μ) -
          ∫ y : ℝ, vaalerK y ∂ν : ℝ) : ℂ)) =
        ∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t *
            ((1 - |t| : ℝ) : ℂ) := by
    simpa [vaalerOsc_zero] using hK0
  have hiH := intervalIntegrable_vaalerCharLimitKernel
    μ ν hC hsmall 0
  have hiH' : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t *
          vaalerHLimitKernel t) volume (-1) 1 := by
    apply IntervalIntegrable.congr (fun t ht => ?_) hiH
    simp [vaalerOsc_zero]
  have hiK : IntervalIntegrable
      (fun t : ℝ =>
        vaalerCharDifference μ ν t *
          ((1 - |t| : ℝ) : ℂ)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_charFun.comp (by fun_prop) |>.sub
      (continuous_charFun.comp (by fun_prop))).mul (by fun_prop)
  calc
    ((((∫ y : ℝ, vaalerH y ∂μ) +
            ∫ y : ℝ, vaalerK y ∂μ) -
          ((∫ y : ℝ, vaalerH y ∂ν) +
            ∫ y : ℝ, vaalerK y ∂ν) : ℝ) : ℂ) =
        ((((∫ y : ℝ, vaalerH y ∂μ) -
            ∫ y : ℝ, vaalerH y ∂ν : ℝ) : ℂ)) +
          ((((∫ y : ℝ, vaalerK y ∂μ) -
            ∫ y : ℝ, vaalerK y ∂ν : ℝ) : ℂ)) := by
      push_cast
      ring
    _ = (∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t * vaalerHLimitKernel t) +
        ∫ t : ℝ in -1..1,
          vaalerCharDifference μ ν t *
            ((1 - |t| : ℝ) : ℂ) := by rw [hH, hK]
    _ = ∫ t : ℝ in -1..1,
        (vaalerCharDifference μ ν t *
            vaalerHLimitKernel t +
          vaalerCharDifference μ ν t *
            ((1 - |t| : ℝ) : ℂ)) := by
      rw [intervalIntegral.integral_add hiH' hiK]
    _ = ∫ t : ℝ in -1..1,
        2 * (vaalerCharDifference μ ν t *
          prawitzKernel (-t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change
        vaalerCharDifference μ ν t * vaalerHLimitKernel t +
            vaalerCharDifference μ ν t * ((1 - |t| : ℝ) : ℂ) =
          2 * (vaalerCharDifference μ ν t * prawitzKernel (-t))
      have hk := triangle_add_vaalerHLimitKernel_eq_two_prawitzKernel_neg t
      calc
        vaalerCharDifference μ ν t * vaalerHLimitKernel t +
            vaalerCharDifference μ ν t * ((1 - |t| : ℝ) : ℂ) =
          vaalerCharDifference μ ν t *
            (((1 - |t| : ℝ) : ℂ) + vaalerHLimitKernel t) := by ring
        _ = 2 * (vaalerCharDifference μ ν t * prawitzKernel (-t)) := by
          rw [hk]
          ring
    _ = 2 * ∫ t : ℝ in -1..1,
        vaalerCharDifference μ ν t * prawitzKernel (-t) := by
      rw [intervalIntegral.integral_const_mul]

lemma vaalerH_integral_dirac_zero :
    ∫ y : ℝ, vaalerH y ∂(Measure.dirac 0) = 0 := by
  rw [integral_dirac]
  simp [vaalerH]

lemma vaalerK_integral_dirac_zero :
    ∫ y : ℝ, vaalerK y ∂(Measure.dirac 0) = 1 := by
  rw [integral_dirac]
  simp [vaalerK]

lemma prawitz_reference_upper_approximation
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference ν (Measure.dirac 0) t‖ ≤ C * |t|) :
    -(∫ y : ℝ, vaalerH y ∂ν) +
        ∫ y : ℝ, vaalerK y ∂ν =
      1 + 2 * Complex.re
        (∫ t : ℝ in -1..1,
          (charFun ν (2 * Real.pi * t) - 1) *
            prawitzKernel t) := by
  have h := prawitz_upper_difference_fourier
    ν (Measure.dirac 0) hC hsmall
  rw [vaalerH_integral_dirac_zero,
    vaalerK_integral_dirac_zero] at h
  have hre := congrArg Complex.re h
  have hchar :
      (fun t : ℝ =>
        vaalerCharDifference ν (Measure.dirac 0) t *
          prawitzKernel t) =
      fun t : ℝ =>
        (charFun ν (2 * Real.pi * t) - 1) *
          prawitzKernel t := by
    funext t
    simp [vaalerCharDifference]
  rw [hchar] at hre
  norm_num at hre
  linarith

lemma prawitz_reference_lower_approximation
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference ν (Measure.dirac 0) t‖ ≤ C * |t|) :
    (∫ y : ℝ, vaalerH y ∂ν) +
        ∫ y : ℝ, vaalerK y ∂ν =
      1 + 2 * Complex.re
        (∫ t : ℝ in -1..1,
          (charFun ν (2 * Real.pi * t) - 1) *
            prawitzKernel (-t)) := by
  have h := prawitz_lower_difference_fourier
    ν (Measure.dirac 0) hC hsmall
  rw [vaalerH_integral_dirac_zero,
    vaalerK_integral_dirac_zero] at h
  have hre := congrArg Complex.re h
  have hchar :
      (fun t : ℝ =>
        vaalerCharDifference ν (Measure.dirac 0) t *
          prawitzKernel (-t)) =
      fun t : ℝ =>
        (charFun ν (2 * Real.pi * t) - 1) *
          prawitzKernel (-t) := by
    funext t
    simp [vaalerCharDifference]
  rw [hchar] at hre
  norm_num at hre
  linarith

lemma prawitz_reference_upper_residual
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference ν (Measure.dirac 0) t‖ ≤ C * |t|)
    (hraw : IntervalIntegrable (prawitzRawKernel ν)
      volume (-1) 1) :
    -(∫ y : ℝ, vaalerH y ∂ν) +
        ∫ y : ℝ, vaalerK y ∂ν -
        ∫ t : ℝ in -1..1, prawitzRawKernel ν t =
      2 * Complex.re
        (∫ t : ℝ in -1..1,
          charFun ν (2 * Real.pi * t) *
            (prawitzKernel t - prawitzSingularKernel t)) := by
  let fP : ℝ → ℂ := fun t =>
    (charFun ν (2 * Real.pi * t) - 1) *
      prawitzKernel t
  let q : ℝ → ℂ := fun t =>
    charFun ν (2 * Real.pi * t) *
      (prawitzKernel t - prawitzSingularKernel t)
  have hfP0 := intervalIntegrable_charDifference_mul_prawitzKernel
    ν (Measure.dirac 0) hC hsmall
  have hfP : IntervalIntegrable fP volume (-1) 1 := by
    apply IntervalIntegrable.congr (fun t ht => ?_) hfP0
    simp [fP, vaalerCharDifference]
  have hq : IntervalIntegrable q volume (-1) 1 := by
    simpa only [q] using
      intervalIntegrable_charFun_mul_prawitzRegular ν
  have htri : IntervalIntegrable
      (fun t : ℝ => 1 - |t|) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hreP : IntervalIntegrable
      (fun t : ℝ => 2 * Complex.re (fP t))
      volume (-1) 1 := by
    have hre : IntervalIntegrable
        (fun t : ℝ => Complex.re (fP t))
        volume (-1) 1 :=
      ⟨Complex.reCLM.integrable_comp hfP.1,
        Complex.reCLM.integrable_comp hfP.2⟩
    exact hre.const_mul 2
  have hreq : IntervalIntegrable
      (fun t : ℝ => 2 * Complex.re (q t))
      volume (-1) 1 := by
    have hre : IntervalIntegrable
        (fun t : ℝ => Complex.re (q t))
        volume (-1) 1 :=
      ⟨Complex.reCLM.integrable_comp hq.1,
        Complex.reCLM.integrable_comp hq.2⟩
    exact hre.const_mul 2
  have hpoint : ∀ t : ℝ,
      (1 - |t|) + 2 * Complex.re (fP t) -
          prawitzRawKernel ν t =
        2 * Complex.re (q t) := by
    intro t
    let z : ℂ := charFun ν (2 * Real.pi * t)
    let P : ℂ := prawitzKernel t
    let S : ℂ := prawitzSingularKernel t
    have htriRe :
        2 * Complex.re (P - S) = 1 - |t| := by
      simpa [P, S] using
        two_mul_re_prawitzKernel_sub_singular t
    have halg :
        (P - S) + (z - 1) * P - (z - 1) * S =
          z * (P - S) := by ring
    have hre := congrArg Complex.re halg
    simp only [Complex.add_re, Complex.sub_re] at hre
    dsimp [fP, q, prawitzRawKernel, z, P, S]
    dsimp [z, P, S] at htriRe hre
    linarith
  have hint :
      (∫ t : ℝ in -1..1, (1 - |t|)) +
          (∫ t : ℝ in -1..1, 2 * Complex.re (fP t)) -
          (∫ t : ℝ in -1..1, prawitzRawKernel ν t) =
        ∫ t : ℝ in -1..1, 2 * Complex.re (q t) := by
    rw [← intervalIntegral.integral_add htri hreP,
      ← intervalIntegral.integral_sub (htri.add hreP) hraw]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hpoint t
  have hrePcomm :
      (∫ t : ℝ in -1..1, Complex.re (fP t)) =
        Complex.re (∫ t : ℝ in -1..1, fP t) :=
    intervalIntegral_re hfP
  have hreqcomm :
      (∫ t : ℝ in -1..1, Complex.re (q t)) =
        Complex.re (∫ t : ℝ in -1..1, q t) :=
    intervalIntegral_re hq
  have happ := prawitz_reference_upper_approximation
    ν hC hsmall
  rw [happ]
  calc
    1 + 2 * Complex.re (∫ t : ℝ in -1..1, fP t) -
          ∫ t : ℝ in -1..1, prawitzRawKernel ν t =
        (∫ t : ℝ in -1..1, (1 - |t|)) +
          (∫ t : ℝ in -1..1, 2 * Complex.re (fP t)) -
          ∫ t : ℝ in -1..1, prawitzRawKernel ν t := by
      rw [intervalIntegral_triangle_real,
        intervalIntegral.integral_const_mul,
        ← hrePcomm]
    _ = ∫ t : ℝ in -1..1, 2 * Complex.re (q t) := hint
    _ = 2 * Complex.re
        (∫ t : ℝ in -1..1, q t) := by
      rw [intervalIntegral.integral_const_mul, hreqcomm]

lemma prawitz_reference_lower_residual
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference ν (Measure.dirac 0) t‖ ≤ C * |t|)
    (hraw : IntervalIntegrable (prawitzRawKernel ν)
      volume (-1) 1) :
    (∫ y : ℝ, vaalerH y ∂ν) +
        ∫ y : ℝ, vaalerK y ∂ν +
        ∫ t : ℝ in -1..1, prawitzRawKernel ν t =
      2 * Complex.re
        (∫ t : ℝ in -1..1,
          charFun ν (2 * Real.pi * t) *
            (prawitzKernel (-t) -
              prawitzSingularKernel (-t))) := by
  let fP : ℝ → ℂ := fun t =>
    (charFun ν (2 * Real.pi * t) - 1) *
      prawitzKernel (-t)
  let q : ℝ → ℂ := fun t =>
    charFun ν (2 * Real.pi * t) *
      (prawitzKernel (-t) - prawitzSingularKernel (-t))
  have hfP0 :=
    intervalIntegrable_charDifference_mul_prawitzKernel_neg
      ν (Measure.dirac 0) hC hsmall
  have hfP : IntervalIntegrable fP volume (-1) 1 := by
    apply IntervalIntegrable.congr (fun t ht => ?_) hfP0
    simp [fP, vaalerCharDifference]
  have hq : IntervalIntegrable q volume (-1) 1 := by
    simpa only [q] using
      intervalIntegrable_charFun_mul_prawitzRegular_neg ν
  have htri : IntervalIntegrable
      (fun t : ℝ => 1 - |t|) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hreP : IntervalIntegrable
      (fun t : ℝ => 2 * Complex.re (fP t))
      volume (-1) 1 := by
    have hre : IntervalIntegrable
        (fun t : ℝ => Complex.re (fP t))
        volume (-1) 1 :=
      ⟨Complex.reCLM.integrable_comp hfP.1,
        Complex.reCLM.integrable_comp hfP.2⟩
    exact hre.const_mul 2
  have hreq : IntervalIntegrable
      (fun t : ℝ => 2 * Complex.re (q t))
      volume (-1) 1 := by
    have hre : IntervalIntegrable
        (fun t : ℝ => Complex.re (q t))
        volume (-1) 1 :=
      ⟨Complex.reCLM.integrable_comp hq.1,
        Complex.reCLM.integrable_comp hq.2⟩
    exact hre.const_mul 2
  have hpoint : ∀ t : ℝ,
      (1 - |t|) + 2 * Complex.re (fP t) +
          prawitzRawKernel ν t =
        2 * Complex.re (q t) := by
    intro t
    let z : ℂ := charFun ν (2 * Real.pi * t)
    let P : ℂ := prawitzKernel (-t)
    let S : ℂ := prawitzSingularKernel t
    have htriRe :
        2 * Complex.re (P + S) = 1 - |t| := by
      have h :=
        two_mul_re_prawitzKernel_sub_singular (-t)
      rw [prawitzSingularKernel_neg, abs_neg] at h
      simpa [P, S] using h
    have halg :
        (P + S) + (z - 1) * P + (z - 1) * S =
          z * (P + S) := by ring
    have hre := congrArg Complex.re halg
    simp only [Complex.add_re, Complex.sub_re] at hre
    dsimp [fP, q, prawitzRawKernel, z, P, S]
    rw [prawitzSingularKernel_neg]
    simp only [sub_neg_eq_add]
    dsimp [z, P, S] at htriRe hre
    linarith
  have hint :
      (∫ t : ℝ in -1..1, (1 - |t|)) +
          (∫ t : ℝ in -1..1, 2 * Complex.re (fP t)) +
          (∫ t : ℝ in -1..1, prawitzRawKernel ν t) =
        ∫ t : ℝ in -1..1, 2 * Complex.re (q t) := by
    rw [← intervalIntegral.integral_add htri hreP,
      ← intervalIntegral.integral_add (htri.add hreP) hraw]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hpoint t
  have hrePcomm :
      (∫ t : ℝ in -1..1, Complex.re (fP t)) =
        Complex.re (∫ t : ℝ in -1..1, fP t) :=
    intervalIntegral_re hfP
  have hreqcomm :
      (∫ t : ℝ in -1..1, Complex.re (q t)) =
        Complex.re (∫ t : ℝ in -1..1, q t) :=
    intervalIntegral_re hq
  have happ := prawitz_reference_lower_approximation
    ν hC hsmall
  rw [happ]
  calc
    1 + 2 * Complex.re (∫ t : ℝ in -1..1, fP t) +
          ∫ t : ℝ in -1..1, prawitzRawKernel ν t =
        (∫ t : ℝ in -1..1, (1 - |t|)) +
          (∫ t : ℝ in -1..1, 2 * Complex.re (fP t)) +
          ∫ t : ℝ in -1..1, prawitzRawKernel ν t := by
      rw [intervalIntegral_triangle_real,
        intervalIntegral.integral_const_mul,
        ← hrePcomm]
    _ = ∫ t : ℝ in -1..1, 2 * Complex.re (q t) := hint
    _ = 2 * Complex.re
        (∫ t : ℝ in -1..1, q t) := by
      rw [intervalIntegral.integral_const_mul, hreqcomm]

/-- Abstract two-sided Prawitz smoothing inequality at the origin.  The four
norm hypotheses are deliberately separated so that upper and lower kernels
can be bounded by the same even majorant later. -/
lemma abs_cdf_sub_le_of_prawitz
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C Cν D R E : ℝ}
    (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (hCν : 0 ≤ Cν)
    (hνsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference ν (Measure.dirac 0) t‖ ≤ Cν * |t|)
    (hraw : IntervalIntegrable (prawitzRawKernel ν)
      volume (-1) 1)
    (hE : 0 ≤ E)
    (hinversion :
      |(2 * cdf ν 0 - 1) -
        ∫ t : ℝ in -1..1, prawitzRawKernel ν t| ≤ E)
    (hDp :
      ‖∫ t : ℝ in -1..1,
        vaalerCharDifference μ ν t * prawitzKernel t‖ ≤ D)
    (hDm :
      ‖∫ t : ℝ in -1..1,
        vaalerCharDifference μ ν t * prawitzKernel (-t)‖ ≤ D)
    (hRp :
      ‖∫ t : ℝ in -1..1,
        charFun ν (2 * Real.pi * t) *
          (prawitzKernel t - prawitzSingularKernel t)‖ ≤ R)
    (hRm :
      ‖∫ t : ℝ in -1..1,
        charFun ν (2 * Real.pi * t) *
          (prawitzKernel (-t) -
            prawitzSingularKernel (-t))‖ ≤ R) :
    |cdf μ 0 - cdf ν 0| ≤ D + R + E / 2 := by
  let Hμ : ℝ := ∫ y : ℝ, vaalerH y ∂μ
  let Kμ : ℝ := ∫ y : ℝ, vaalerK y ∂μ
  let Hν : ℝ := ∫ y : ℝ, vaalerH y ∂ν
  let Kν : ℝ := ∫ y : ℝ, vaalerK y ∂ν
  let raw : ℝ :=
    ∫ t : ℝ in -1..1, prawitzRawKernel ν t
  let Jp : ℂ :=
    ∫ t : ℝ in -1..1,
      vaalerCharDifference μ ν t * prawitzKernel t
  let Jm : ℂ :=
    ∫ t : ℝ in -1..1,
      vaalerCharDifference μ ν t * prawitzKernel (-t)
  let Qp : ℂ :=
    ∫ t : ℝ in -1..1,
      charFun ν (2 * Real.pi * t) *
        (prawitzKernel t - prawitzSingularKernel t)
  let Qm : ℂ :=
    ∫ t : ℝ in -1..1,
      charFun ν (2 * Real.pi * t) *
        (prawitzKernel (-t) -
          prawitzSingularKernel (-t))
  have hμup := cdf_vaaler_upper_bound μ 0
  have hμlo := cdf_vaaler_lower_bound μ 0
  simp only [sub_zero] at hμup hμlo
  change 2 * cdf μ 0 - 1 ≤ -Hμ + Kμ at hμup
  change -Hμ - Kμ ≤ 2 * cdf μ 0 - 1 at hμlo
  have hdiffp0 :=
    prawitz_upper_difference_fourier μ ν hC hsmall
  have hdiffp := congrArg Complex.re hdiffp0
  norm_num at hdiffp
  change -Hμ + Kμ - (-Hν + Kν) =
      2 * Complex.re Jp at hdiffp
  have hdiffm0 :=
    prawitz_lower_difference_fourier μ ν hC hsmall
  have hdiffm := congrArg Complex.re hdiffm0
  norm_num at hdiffm
  change (Hμ + Kμ) - (Hν + Kν) =
      2 * Complex.re Jm at hdiffm
  have hresp := prawitz_reference_upper_residual
    ν hCν hνsmall hraw
  change -Hν + Kν - raw = 2 * Complex.re Qp at hresp
  have hresm := prawitz_reference_lower_residual
    ν hCν hνsmall hraw
  change Hν + Kν + raw = 2 * Complex.re Qm at hresm
  change |(2 * cdf ν 0 - 1) - raw| ≤ E at hinversion
  change ‖Jp‖ ≤ D at hDp
  change ‖Jm‖ ≤ D at hDm
  change ‖Qp‖ ≤ R at hRp
  change ‖Qm‖ ≤ R at hRm
  have hJp : Complex.re Jp ≤ D :=
    (Complex.re_le_norm Jp).trans hDp
  have hJm : Complex.re Jm ≤ D :=
    (Complex.re_le_norm Jm).trans hDm
  have hQp : Complex.re Qp ≤ R :=
    (Complex.re_le_norm Qp).trans hRp
  have hQm : Complex.re Qm ≤ R :=
    (Complex.re_le_norm Qm).trans hRm
  have hinvUpper : raw - (2 * cdf ν 0 - 1) ≤ E :=
    by linarith [(abs_le.mp hinversion).1]
  have hinvLower : (2 * cdf ν 0 - 1) - raw ≤ E :=
    (abs_le.mp hinversion).2
  have hupper :
      cdf μ 0 - cdf ν 0 ≤ D + R + E / 2 := by
    linarith
  have hlower :
      -(D + R + E / 2) ≤ cdf μ 0 - cdf ν 0 := by
    linarith
  exact (abs_le).2 ⟨hlower, hupper⟩

/-! ## Gaussian regular-kernel correction -/

lemma integral_exp_neg_sq_div_two_Ioi :
    (∫ x : ℝ in Ioi 0, Real.exp (-(x ^ 2 / 2))) =
      Real.sqrt (Real.pi / 2) := by
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  rw [show (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) =
      (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
    funext x
    congr 1
    ring, h]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rw [show Real.pi / (1 / 2 : ℝ) =
      4 * (Real.pi / 2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
      Real.sqrt_nonneg 4]
  rw [hsqrt4]
  ring

lemma integral_mul_exp_neg_sq_div_two_Ioi :
    (∫ x : ℝ in Ioi 0,
      x * Real.exp (-(x ^ 2 / 2))) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (by norm_num)
  have hi := (integrable_mul_cexp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (by norm_num)).integrableOn
      (s := Ioi 0)
  have hre := integral_re hi
  calc
    (∫ x : ℝ in Ioi 0,
        x * Real.exp (-(x ^ 2 / 2))) =
        ∫ x : ℝ in Ioi 0,
          Complex.re (((x : ℂ)) *
            Complex.exp
              (-((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [show -((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2 =
          ((-(x ^ 2 / 2) : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [Complex.exp_ofReal_re]
    _ = Complex.re (∫ x : ℝ in Ioi 0,
          ((x : ℂ)) * Complex.exp
            (-((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)) := hre
    _ = Complex.re
        (((2 : ℂ) * ((1 / 2 : ℝ) : ℂ))⁻¹) := by rw [h]
    _ = 1 := by norm_num

lemma integral_sq_mul_gaussianPDFReal_Ioi_eq_half :
    (∫ x : ℝ in Ioi 0,
      x ^ 2 * gaussianPDFReal 0 1 x) = 1 / 2 := by
  let f : ℝ → ℝ :=
    fun x => x ^ 2 * gaussianPDFReal 0 1 x
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f, gaussianPDFReal]
    rw [show (-x - 0) ^ 2 = (x - 0) ^ 2 by ring]
    ring
  have hhalves :
      (∫ x : ℝ in Iic 0, f x) =
        ∫ x : ℝ in Ioi 0, f x := by
    have hneg := integral_comp_neg_Ioi 0 f
    rw [show (fun x : ℝ => f (-x)) = f by
      funext x
      exact heven x] at hneg
    simpa using hneg.symm
  have hfull := integral_add_compl
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
      integrable_sq_mul_gaussianPDFReal
  change (∫ x : ℝ in Ioi 0, f x) +
      (∫ x : ℝ in (Ioi 0)ᶜ, f x) =
        ∫ x : ℝ, f x at hfull
  rw [compl_Ioi, hhalves] at hfull
  have hone : (∫ x : ℝ, f x) = 1 := by
    simpa [f] using integral_sq_mul_gaussianPDFReal_eq_one
  rw [hone] at hfull
  have hhalf :
      (∫ x : ℝ in Ioi 0, f x) = 1 / 2 := by
    linarith
  simpa [f] using hhalf

lemma integral_sq_mul_exp_neg_sq_div_two_Ioi :
    (∫ x : ℝ in Ioi 0,
      x ^ 2 * Real.exp (-(x ^ 2 / 2))) =
        Real.sqrt (Real.pi / 2) := by
  have hpdf := integral_sq_mul_gaussianPDFReal_Ioi_eq_half
  let c : ℝ := Real.sqrt (2 * Real.pi)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hpdf' :
      c⁻¹ * (∫ x : ℝ in Ioi 0,
        x ^ 2 * Real.exp (-(x ^ 2 / 2))) = 1 / 2 := by
    rw [← hpdf]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [c, gaussianPDFReal]
    simp only [mul_one, sub_zero]
    rw [show -(x ^ 2 / 2) = -x ^ 2 / 2 by ring]
    ring
  calc
    (∫ x : ℝ in Ioi 0,
        x ^ 2 * Real.exp (-(x ^ 2 / 2))) =
        c * (c⁻¹ * (∫ x : ℝ in Ioi 0,
          x ^ 2 * Real.exp (-(x ^ 2 / 2)))) := by
      field_simp [hc.ne']
    _ = c / 2 := by rw [hpdf']; ring
    _ = Real.sqrt (Real.pi / 2) := by
      dsimp [c]
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      rw [show 2 * Real.pi =
          4 * (Real.pi / 2) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        nlinarith [Real.sq_sqrt
          (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_nonneg 4]
      rw [hsqrt4]
      ring

lemma integral_exp_neg_scaled_sq_div_two_Ioi
    {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in Ioi 0,
      Real.exp (-((T * t) ^ 2 / 2))) =
        Real.sqrt (Real.pi / 2) / T := by
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) 0 hT
  simpa [smul_eq_mul, inv_mul_eq_div,
    integral_exp_neg_sq_div_two_Ioi] using h

lemma integral_mul_exp_neg_scaled_sq_div_two_Ioi
    {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in Ioi 0,
      t * Real.exp (-((T * t) ^ 2 / 2))) =
        1 / T ^ 2 := by
  let I : ℝ := ∫ t : ℝ in Ioi 0,
    t * Real.exp (-((T * t) ^ 2 / 2))
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ =>
      u * Real.exp (-(u ^ 2 / 2))) 0 hT
  have hTI : T * I = T⁻¹ := by
    calc
      T * I = ∫ t : ℝ in Ioi 0,
          T * (t * Real.exp
            (-((T * t) ^ 2 / 2))) := by
        dsimp [I]
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ t : ℝ in Ioi 0,
          (T * t) * Real.exp
            (-((T * t) ^ 2 / 2)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        ring
      _ = T⁻¹ := by
        simpa [smul_eq_mul,
          integral_mul_exp_neg_sq_div_two_Ioi] using h
  dsimp [I] at hTI ⊢
  field_simp [hT.ne'] at hTI ⊢
  exact hTI

lemma integral_sq_mul_exp_neg_scaled_sq_div_two_Ioi
    {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in Ioi 0,
      t ^ 2 * Real.exp (-((T * t) ^ 2 / 2))) =
        Real.sqrt (Real.pi / 2) / T ^ 3 := by
  let I : ℝ := ∫ t : ℝ in Ioi 0,
    t ^ 2 * Real.exp (-((T * t) ^ 2 / 2))
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ =>
      u ^ 2 * Real.exp (-(u ^ 2 / 2))) 0 hT
  have hT2I :
      T ^ 2 * I =
        T⁻¹ * Real.sqrt (Real.pi / 2) := by
    calc
      T ^ 2 * I = ∫ t : ℝ in Ioi 0,
          T ^ 2 * (t ^ 2 * Real.exp
            (-((T * t) ^ 2 / 2))) := by
        dsimp [I]
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ t : ℝ in Ioi 0,
          (T * t) ^ 2 * Real.exp
            (-((T * t) ^ 2 / 2)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        ring
      _ = T⁻¹ * Real.sqrt (Real.pi / 2) := by
        simpa [smul_eq_mul,
          integral_sq_mul_exp_neg_sq_div_two_Ioi] using h
  dsimp [I] at hT2I ⊢
  field_simp [hT.ne'] at hT2I ⊢
  nlinarith

lemma integrable_exp_neg_scaled_sq_div_two
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ =>
      Real.exp (-((T * t) ^ 2 / 2))) := by
  have h := integrable_exp_neg_mul_sq
    (by positivity : 0 < T ^ 2 / 2)
  convert h using 1
  funext t
  congr 1
  ring

lemma integrable_mul_exp_neg_scaled_sq_div_two
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ =>
      t * Real.exp (-((T * t) ^ 2 / 2))) := by
  have h := integrable_mul_exp_neg_mul_sq
    (by positivity : 0 < T ^ 2 / 2)
  convert h using 1
  funext t
  congr 2
  ring

lemma integrable_sq_mul_exp_neg_scaled_sq_div_two
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ =>
      t ^ 2 * Real.exp (-((T * t) ^ 2 / 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (by positivity : 0 < T ^ 2 / 2)
    (by norm_num : (-1 : ℝ) < 2)
  convert h using 1
  funext t
  rw [Real.rpow_two]
  congr 2
  ring

/-- The Gaussian reference contribution from the regular part of the
Prawitz kernel, bounded by its exact three half-line Gaussian moments. -/
lemma gaussian_regular_majorant_integral_le_closed
    {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in 0..1,
        Real.exp (-((T * t) ^ 2 / 2)) *
          (1 - t + Real.pi ^ 2 * t ^ 2 / 18)) ≤
      Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
        (Real.pi ^ 2 / 18) *
          Real.sqrt (Real.pi / 2) / T ^ 3 := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-((T * t) ^ 2 / 2)) *
      (1 - t + Real.pi ^ 2 * t ^ 2 / 18)
  have h0 := integrable_exp_neg_scaled_sq_div_two hT
  have h1 := integrable_mul_exp_neg_scaled_sq_div_two hT
  have h2 := integrable_sq_mul_exp_neg_scaled_sq_div_two hT
  have hg : Integrable g := by
    have h :=
      h0.sub h1 |>.add
        (h2.const_mul (Real.pi ^ 2 / 18))
    apply h.congr
    filter_upwards with t
    dsimp [g]
    ring
  have hg0 : ∀ t : ℝ, 0 ≤ g t := by
    intro t
    dsimp [g]
    apply mul_nonneg (Real.exp_pos _).le
    have hpiSq : (9 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg (t - 1)]
  have hmono :
      (∫ t : ℝ in 0..1, g t) ≤
        ∫ t : ℝ in Ioi 0, g t := by
    rw [intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    apply setIntegral_mono_set hg.integrableOn
    · exact ae_of_all _ hg0
    · filter_upwards with t
      intro ht
      exact ht.1
  have hwhole :
      (∫ t : ℝ in Ioi 0, g t) =
        Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
          (Real.pi ^ 2 / 18) *
            Real.sqrt (Real.pi / 2) / T ^ 3 := by
    have h0on := h0.integrableOn (s := Ioi 0)
    have h1on := h1.integrableOn (s := Ioi 0)
    have h2on := h2.integrableOn (s := Ioi 0)
    calc
      (∫ t : ℝ in Ioi 0, g t) =
          ∫ t : ℝ in Ioi 0,
            (Real.exp (-((T * t) ^ 2 / 2)) -
              t * Real.exp (-((T * t) ^ 2 / 2))) +
              (Real.pi ^ 2 / 18) *
                (t ^ 2 *
                  Real.exp (-((T * t) ^ 2 / 2))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp [g]
        ring
      _ =
          (∫ t : ℝ in Ioi 0,
              (Real.exp (-((T * t) ^ 2 / 2)) -
                t * Real.exp (-((T * t) ^ 2 / 2)))) +
            (∫ t : ℝ in Ioi 0,
              (Real.pi ^ 2 / 18) *
                (t ^ 2 *
                  Real.exp (-((T * t) ^ 2 / 2)))) :=
        MeasureTheory.integral_add (h0on.sub h1on)
          (h2on.const_mul (Real.pi ^ 2 / 18))
      _ =
          (∫ t : ℝ in Ioi 0,
              Real.exp (-((T * t) ^ 2 / 2))) -
            (∫ t : ℝ in Ioi 0,
              t * Real.exp (-((T * t) ^ 2 / 2))) +
            (Real.pi ^ 2 / 18) *
              (∫ t : ℝ in Ioi 0,
                t ^ 2 *
                  Real.exp (-((T * t) ^ 2 / 2))) := by
        rw [MeasureTheory.integral_sub h0on h1on,
          MeasureTheory.integral_const_mul]
      _ = Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
          (Real.pi ^ 2 / 18) *
            Real.sqrt (Real.pi / 2) / T ^ 3 := by
        rw [integral_exp_neg_scaled_sq_div_two_Ioi hT,
          integral_mul_exp_neg_scaled_sq_div_two_Ioi hT,
          integral_sq_mul_exp_neg_scaled_sq_div_two_Ioi hT]
        ring
  change (∫ t : ℝ in 0..1, g t) ≤ _
  rw [← hwhole]
  exact hmono

lemma norm_prawitzKernel_sub_singular_le_refined_abs
    {t : ℝ} (ht : |t| < 1) :
    ‖prawitzKernel t - prawitzSingularKernel t‖ ≤
      (1 - |t| + Real.pi ^ 2 * |t| ^ 2 / 18) / 2 := by
  rcases lt_trichotomy t 0 with htneg | rfl | htpos
  · have h := norm_prawitzKernel_sub_singular_le_refined
      (t := -t) (by linarith)
        (by simpa [abs_of_neg htneg] using ht)
    change ‖prawitzKernel (-t) -
      prawitzSingularKernel (-t)‖ ≤ _ at h
    have hstarS :
        (starRingEnd ℂ) (prawitzSingularKernel t) =
          prawitzSingularKernel (-t) := by
      rw [prawitzSingularKernel_neg]
      unfold prawitzSingularKernel
      change star
        (Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)) =
          -(Complex.I / ((2 * Real.pi * t : ℝ) : ℂ))
      rw [star_div₀]
      simp
      ring
    calc
      ‖prawitzKernel t - prawitzSingularKernel t‖ =
          ‖(starRingEnd ℂ)
            (prawitzKernel t -
              prawitzSingularKernel t)‖ := by
        exact (norm_star _).symm
      _ = ‖prawitzKernel (-t) -
          prawitzSingularKernel (-t)‖ := by
        rw [map_sub, ← prawitzKernel_neg, hstarS]
      _ ≤ (1 - (-t) +
          Real.pi ^ 2 * (-t) ^ 2 / 18) / 2 := h
      _ = (1 - |t| +
          Real.pi ^ 2 * |t| ^ 2 / 18) / 2 := by
        rw [abs_of_neg htneg]
  · unfold prawitzKernel prawitzSingularKernel
    simp [Real.cot_eq_cos_div_sin]
    rw [Complex.norm_def]
    simp [Complex.normSq_apply]
  · change ‖prawitzKernel t -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤ _
    simpa [abs_of_pos htpos] using
      norm_prawitzKernel_sub_singular_le_refined htpos
        ((le_abs_self t).trans_lt ht)

lemma intervalIntegral_even_neg_one_one
    (g : ℝ → ℝ)
    (heven : ∀ t : ℝ, g (-t) = g t)
    (hg : IntervalIntegrable g volume (-1) 1) :
    (∫ t : ℝ in -1..1, g t) =
      2 * ∫ t : ℝ in 0..1, g t := by
  have hneg : IntervalIntegrable g volume (-1) 0 :=
    hg.mono_set (by
      intro x hx
      simp only [
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx ⊢
      exact ⟨hx.1, hx.2.trans (by norm_num)⟩)
  have hpos : IntervalIntegrable g volume 0 1 :=
    hg.mono_set (by
      intro x hx
      simp only [
        uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx ⊢
      exact ⟨(by linarith [hx.1]), hx.2⟩)
  have hsymmetric :
      (∫ t : ℝ in -1..0, g t) =
        ∫ t : ℝ in 0..1, g t := by
    have hchange := intervalIntegral.integral_comp_neg
      (f := g) (a := 0) (b := 1)
    rw [show (fun t : ℝ => g (-t)) = g by
      funext t
      exact heven t] at hchange
    simpa using hchange.symm
  rw [← integral_add_adjacent_intervals hneg hpos]
  rw [hsymmetric]
  ring

lemma norm_charFun_scaledCenteredGaussian
    {T : ℝ} (a t : ℝ) :
    ‖charFun
        (scaledCenteredMeasure (gaussianReal 0 1) a T)
        (2 * Real.pi * t)‖ =
      Real.exp (-((T * t) ^ 2 / 2)) := by
  rw [charFun_scaledCenteredGaussian_vaaler,
    norm_mul, Complex.norm_exp, norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp
  ring

lemma norm_integral_scaledCenteredGaussian_prawitzRegular_le
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ‖∫ t : ℝ in -1..1,
        charFun
            (scaledCenteredMeasure (gaussianReal 0 1) a T)
            (2 * Real.pi * t) *
          (prawitzKernel t - prawitzSingularKernel t)‖ ≤
      Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
        (Real.pi ^ 2 / 18) *
          Real.sqrt (Real.pi / 2) / T ^ 3 := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-((T * |t|) ^ 2 / 2)) *
      ((1 - |t| + Real.pi ^ 2 * |t| ^ 2 / 18) / 2)
  have hg : IntervalIntegrable g volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hnorm :
      ‖∫ t : ℝ in -1..1,
          charFun
              (scaledCenteredMeasure (gaussianReal 0 1) a T)
              (2 * Real.pi * t) *
            (prawitzKernel t - prawitzSingularKernel t)‖ ≤
        ∫ t : ℝ in -1..1, g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le
      (by norm_num : (-1 : ℝ) ≤ 1) _ hg
    filter_upwards [(volume : Measure ℝ).ae_ne 1] with t htne
    intro htmem
    have htlt : t < 1 := lt_of_le_of_ne htmem.2 htne
    have habt : |t| < 1 :=
      (abs_lt).2 ⟨htmem.1, htlt⟩
    rw [norm_mul, norm_charFun_scaledCenteredGaussian]
    calc
      Real.exp (-((T * t) ^ 2 / 2)) *
          ‖prawitzKernel t - prawitzSingularKernel t‖ ≤
        Real.exp (-((T * t) ^ 2 / 2)) *
          ((1 - |t| +
            Real.pi ^ 2 * |t| ^ 2 / 18) / 2) :=
        mul_le_mul_of_nonneg_left
          (norm_prawitzKernel_sub_singular_le_refined_abs
            habt) (Real.exp_pos _).le
      _ = g t := by
        dsimp [g]
        have hsquare :
            (T * t) ^ 2 = (T * |t|) ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
        rw [hsquare, sq_abs]
  have heven : ∀ t : ℝ, g (-t) = g t := by
    intro t
    dsimp [g]
    rw [abs_neg]
  have hsymm :=
    intervalIntegral_even_neg_one_one g heven hg
  have hpositive :
      2 * (∫ t : ℝ in 0..1, g t) =
        ∫ t : ℝ in 0..1,
          Real.exp (-((T * t) ^ 2 / 2)) *
            (1 - t + Real.pi ^ 2 * t ^ 2 / 18) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp [g]
    rw [abs_of_nonneg ht.1]
    ring
  calc
    ‖∫ t : ℝ in -1..1,
        charFun
            (scaledCenteredMeasure (gaussianReal 0 1) a T)
            (2 * Real.pi * t) *
          (prawitzKernel t - prawitzSingularKernel t)‖ ≤
        ∫ t : ℝ in -1..1, g t := hnorm
    _ = 2 * (∫ t : ℝ in 0..1, g t) := hsymm
    _ = ∫ t : ℝ in 0..1,
          Real.exp (-((T * t) ^ 2 / 2)) *
            (1 - t + Real.pi ^ 2 * t ^ 2 / 18) :=
      hpositive
    _ ≤ Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
        (Real.pi ^ 2 / 18) *
          Real.sqrt (Real.pi / 2) / T ^ 3 :=
      gaussian_regular_majorant_integral_le_closed hT

lemma norm_integral_scaledCenteredGaussian_prawitzRegular_neg_le
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ‖∫ t : ℝ in -1..1,
        charFun
            (scaledCenteredMeasure (gaussianReal 0 1) a T)
            (2 * Real.pi * t) *
          (prawitzKernel (-t) -
            prawitzSingularKernel (-t))‖ ≤
      Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
        (Real.pi ^ 2 / 18) *
          Real.sqrt (Real.pi / 2) / T ^ 3 := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-((T * |t|) ^ 2 / 2)) *
      ((1 - |t| + Real.pi ^ 2 * |t| ^ 2 / 18) / 2)
  have hg : IntervalIntegrable g volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hnorm :
      ‖∫ t : ℝ in -1..1,
          charFun
              (scaledCenteredMeasure (gaussianReal 0 1) a T)
              (2 * Real.pi * t) *
            (prawitzKernel (-t) -
              prawitzSingularKernel (-t))‖ ≤
        ∫ t : ℝ in -1..1, g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le
      (by norm_num : (-1 : ℝ) ≤ 1) _ hg
    filter_upwards [(volume : Measure ℝ).ae_ne 1] with t htne
    intro htmem
    have htlt : t < 1 := lt_of_le_of_ne htmem.2 htne
    have habt : |-t| < 1 := by
      simpa using (abs_lt).2 ⟨htmem.1, htlt⟩
    rw [norm_mul, norm_charFun_scaledCenteredGaussian]
    calc
      Real.exp (-((T * t) ^ 2 / 2)) *
          ‖prawitzKernel (-t) -
            prawitzSingularKernel (-t)‖ ≤
        Real.exp (-((T * t) ^ 2 / 2)) *
          ((1 - |-t| +
            Real.pi ^ 2 * |-t| ^ 2 / 18) / 2) :=
        mul_le_mul_of_nonneg_left
          (norm_prawitzKernel_sub_singular_le_refined_abs
            habt) (Real.exp_pos _).le
      _ = g t := by
        dsimp [g]
        have hsquare :
            (T * t) ^ 2 = (T * |t|) ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
        rw [abs_neg, hsquare, sq_abs]
  have heven : ∀ t : ℝ, g (-t) = g t := by
    intro t
    dsimp [g]
    rw [abs_neg]
  have hsymm :=
    intervalIntegral_even_neg_one_one g heven hg
  have hpositive :
      2 * (∫ t : ℝ in 0..1, g t) =
        ∫ t : ℝ in 0..1,
          Real.exp (-((T * t) ^ 2 / 2)) *
            (1 - t + Real.pi ^ 2 * t ^ 2 / 18) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp [g]
    rw [abs_of_nonneg ht.1]
    ring
  calc
    ‖∫ t : ℝ in -1..1,
        charFun
            (scaledCenteredMeasure (gaussianReal 0 1) a T)
            (2 * Real.pi * t) *
          (prawitzKernel (-t) -
            prawitzSingularKernel (-t))‖ ≤
        ∫ t : ℝ in -1..1, g t := hnorm
    _ = 2 * (∫ t : ℝ in 0..1, g t) := hsymm
    _ = ∫ t : ℝ in 0..1,
          Real.exp (-((T * t) ^ 2 / 2)) *
            (1 - t + Real.pi ^ 2 * t ^ 2 / 18) :=
      hpositive
    _ ≤ Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
        (Real.pi ^ 2 / 18) *
          Real.sqrt (Real.pi / 2) / T ^ 3 :=
      gaussian_regular_majorant_integral_le_closed hT

lemma norm_vaalerCharDifference_scaledCentered_gaussian
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a T t : ℝ) :
    ‖vaalerCharDifference
        (scaledCenteredMeasure μ a T)
        (scaledCenteredMeasure (gaussianReal 0 1) a T) t‖ =
      ‖charFun μ (T * t) -
        (Real.exp (-((T * t) ^ 2 / 2)) : ℂ)‖ := by
  unfold vaalerCharDifference
  rw [charFun_scaledCenteredMeasure_vaaler,
    charFun_scaledCenteredGaussian_vaaler]
  rw [show -(T * t) ^ 2 / 2 =
      -((T * t) ^ 2 / 2) by ring]
  rw [show
      Complex.exp
            (((-a * T * t : ℝ) : ℂ) * Complex.I) *
          charFun μ (T * t) -
        Complex.exp
            (((-a * T * t : ℝ) : ℂ) * Complex.I) *
          (Real.exp (-((T * t) ^ 2 / 2)) : ℂ) =
      Complex.exp
          (((-a * T * t : ℝ) : ℂ) * Complex.I) *
        (charFun μ (T * t) -
          (Real.exp (-((T * t) ^ 2 / 2)) : ℂ)) by
    ring,
    norm_mul, Complex.norm_exp]
  simp

/-- Low-frequency normalized-sum characteristic-function estimate expressed
only through `δ = E|X|³ / √n`. -/
lemma norm_charFun_normalizedSum_sub_gaussian_le_berryLow
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n) (u : ℝ)
    (hu : (∫ ω, |X 0 ω| ^ 3 ∂P) /
        Real.sqrt n * |u| ≤ 1) :
    ‖charFun
          (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, X k ω)) u -
        (Real.exp (-(u ^ 2 / 2)) : ℂ)‖ ≤
      ((∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n) *
          |u| ^ 3 / 6 *
          Real.exp (-((1 -
            ((∫ ω, |X 0 ω| ^ 3 ∂P) /
              Real.sqrt n) ^ 2) * u ^ 2 / 3)) +
        ((∫ ω, |X 0 ω| ^ 3 ∂P) /
            Real.sqrt n) ^ 2 * u ^ 4 / 8 *
          Real.exp (-((1 -
            ((∫ ω, |X 0 ω| ^ 3 ∂P) /
              Real.sqrt n) ^ 2) * u ^ 2 / 2)) := by
  let β : ℝ := ∫ ω, |X 0 ω| ^ 3 ∂P
  let δ : ℝ := β / Real.sqrt n
  have hs : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hβ : 1 ≤ β := by
    simpa [β] using
      third_absolute_moment_ge_one hX hsecond
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hcond :
      |(Real.sqrt n)⁻¹ * u| * β ≤ 1 := by
    rw [abs_mul, abs_inv, abs_of_pos hs]
    simpa [δ, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hu
  have h :=
    norm_charFun_inv_sqrt_mul_sum_sub_gaussian_le_decay
      hindep hident hX hmean hsecond hn u hcond
  have hinvN : (1 : ℝ) / n ≤ δ ^ 2 := by
    have hβsq : 1 ≤ β ^ 2 := by nlinarith
    dsimp [δ]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact div_le_div_of_nonneg_right hβsq
      (Nat.cast_nonneg n)
  have hdecay :
      1 - δ ^ 2 ≤ 1 - (1 : ℝ) / n := by
    linarith
  have hscaleSq :
      ((Real.sqrt n)⁻¹ * u) ^ 2 =
        u ^ 2 / n := by
    field_simp [hs.ne', hnR]
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hfirstCoeff :
      (n : ℝ) *
          (|(Real.sqrt n)⁻¹ * u| ^ 3 / 6 * β) =
        δ * |u| ^ 3 / 6 := by
    rw [abs_mul, abs_inv, abs_of_pos hs]
    dsimp [δ]
    field_simp [hs.ne', hnR]
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsecondCoeff :
      (n : ℝ) *
          (((((Real.sqrt n)⁻¹ * u) ^ 2 / 2) ^ 2) / 2) =
        u ^ 4 / (8 * n) := by
    rw [hscaleSq]
    field_simp [hnR]
    ring
  have hexpThird :
      Real.exp (-(((n : ℝ) - 1) *
          (((Real.sqrt n)⁻¹ * u) ^ 2 / 3))) ≤
        Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3)) := by
    apply Real.exp_le_exp.mpr
    rw [hscaleSq]
    have huSq : 0 ≤ u ^ 2 := sq_nonneg u
    have hm :=
      mul_le_mul_of_nonneg_right hdecay huSq
    field_simp [hnR] at hm ⊢
    nlinarith
  have hexpHalf :
      Real.exp (-(((n : ℝ) - 1) *
          (((Real.sqrt n)⁻¹ * u) ^ 2 / 2))) ≤
        Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)) := by
    apply Real.exp_le_exp.mpr
    rw [hscaleSq]
    have huSq : 0 ≤ u ^ 2 := sq_nonneg u
    have hm :=
      mul_le_mul_of_nonneg_right hdecay huSq
    field_simp [hnR] at hm ⊢
    nlinarith
  have hsecondLe :
      u ^ 4 / (8 * n) ≤
        δ ^ 2 * u ^ 4 / 8 := by
    have hu4 : 0 ≤ u ^ 4 := by positivity
    have hm :=
      mul_le_mul_of_nonneg_right hinvN hu4
    calc
      u ^ 4 / (8 * n) =
          ((1 : ℝ) / n * u ^ 4) / 8 := by
        field_simp [hnR]
      _ ≤ (δ ^ 2 * u ^ 4) / 8 :=
        div_le_div_of_nonneg_right hm (by norm_num)
      _ = δ ^ 2 * u ^ 4 / 8 := rfl
  calc
    ‖charFun
          (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, X k ω)) u -
        (Real.exp (-(u ^ 2 / 2)) : ℂ)‖ ≤
      (n : ℝ) *
          (|(Real.sqrt n)⁻¹ * u| ^ 3 / 6 * β) *
          Real.exp (-(((n : ℝ) - 1) *
            (((Real.sqrt n)⁻¹ * u) ^ 2 / 3))) +
        (n : ℝ) *
          (((((Real.sqrt n)⁻¹ * u) ^ 2 / 2) ^ 2) / 2) *
          Real.exp (-(((n : ℝ) - 1) *
            (((Real.sqrt n)⁻¹ * u) ^ 2 / 2))) := by
        simpa [β] using h
    _ ≤ δ * |u| ^ 3 / 6 *
          Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3)) +
        δ ^ 2 * u ^ 4 / 8 *
          Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)) := by
      rw [hfirstCoeff, hsecondCoeff]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          hexpThird (by positivity))
        (calc
          u ^ 4 / (8 * n) *
              Real.exp (-(((n : ℝ) - 1) *
                (((Real.sqrt n)⁻¹ * u) ^ 2 / 2))) ≤
            u ^ 4 / (8 * n) *
              Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)) :=
              mul_le_mul_of_nonneg_left
                hexpHalf (by positivity)
          _ ≤ δ ^ 2 * u ^ 4 / 8 *
              Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)) :=
              mul_le_mul_of_nonneg_right hsecondLe
                (Real.exp_pos _).le)
    _ = _ := by rfl

/-- Medium-frequency normalized-sum bound, retaining the Gaussian
characteristic function as a separate summand. -/
lemma norm_charFun_normalizedSum_sub_gaussian_le_berryMedium
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n) (u : ℝ)
    (hu : (∫ ω, |X 0 ω| ^ 3 ∂P) /
        Real.sqrt n * |u| ≤ 3 / 2) :
    ‖charFun
          (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, X k ω)) u -
        (Real.exp (-(u ^ 2 / 2)) : ℂ)‖ ≤
      Real.exp (-(u ^ 2 / 8)) +
        Real.exp (-(u ^ 2 / 2)) := by
  have hs : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hcond :
      |(Real.sqrt n)⁻¹ * u| *
          (∫ ω, |X 0 ω| ^ 3 ∂P) ≤ 3 / 2 := by
    rw [abs_mul, abs_inv, abs_of_pos hs]
    simpa [div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hu
  have hsum :=
    norm_charFun_inv_sqrt_mul_sum_le_exp_neg_sq_div_eight
      hindep hident hX hmean hsecond hn u hcond
  calc
    ‖charFun
          (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, X k ω)) u -
        (Real.exp (-(u ^ 2 / 2)) : ℂ)‖ ≤
      ‖charFun
          (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, X k ω)) u‖ +
        ‖(Real.exp (-(u ^ 2 / 2)) : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ Real.exp (-(u ^ 2 / 8)) +
        Real.exp (-(u ^ 2 / 2)) := by
      apply add_le_add hsum
      rw [norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]

end HDP.Appendix
