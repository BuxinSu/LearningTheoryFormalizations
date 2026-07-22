import HighDimensionalProbability.Appendix.Infra.BerryEsseenVaaler
import HighDimensionalProbability.Appendix.Infra.BerryEsseenPrawitz

/-!
# Prawitz inversion for Berry--Esseen

This file combines the Vaaler majorant with the Prawitz kernel.
-/

open Real Complex Filter MeasureTheory ProbabilityTheory intervalIntegral Set
open scoped Interval Topology FourierTransform

namespace HDP.Appendix

/-- The singular term `i / (2πt)` isolated from the Prawitz kernel. -/
noncomputable def prawitzSingularKernel (t : ℝ) : ℂ :=
  Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)

lemma triangle_sub_vaalerHLimitKernel
    (t : ℝ) :
    ((1 - |t| : ℝ) : ℂ) - vaalerHLimitKernel t =
      2 * prawitzKernel t := by
  let A : ℝ :=
    (1 - |t|) * Real.cot (Real.pi * t) +
      Real.sign t / Real.pi
  change ((1 - |t| : ℝ) : ℂ) - -Complex.I * (A : ℂ) =
    2 * ⟨(1 - |t|) / 2, A / 2⟩
  apply Complex.ext
  · norm_num
    ring
  · norm_num
    ring

lemma vaalerHLimitKernel_add_two_singular
    (t : ℝ) :
    vaalerHLimitKernel t + 2 * prawitzSingularKernel t =
      ((1 - |t| : ℝ) : ℂ) -
        2 * (prawitzKernel t - prawitzSingularKernel t) := by
  have hH :
      vaalerHLimitKernel t =
        ((1 - |t| : ℝ) : ℂ) - 2 * prawitzKernel t := by
    calc
      vaalerHLimitKernel t =
          ((1 - |t| : ℝ) : ℂ) -
            (((1 - |t| : ℝ) : ℂ) -
              vaalerHLimitKernel t) := by ring
      _ = ((1 - |t| : ℝ) : ℂ) -
          2 * prawitzKernel t := by
        rw [triangle_sub_vaalerHLimitKernel]
  rw [hH]
  ring

lemma prawitzSingularKernel_neg (t : ℝ) :
    prawitzSingularKernel (-t) = -prawitzSingularKernel t := by
  unfold prawitzSingularKernel
  push_cast
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [Real.pi_ne_zero, ht, Complex.I_ne_zero]

lemma vaalerHLimitKernel_neg (t : ℝ) :
    vaalerHLimitKernel (-t) = -vaalerHLimitKernel t := by
  unfold vaalerHLimitKernel
  rw [abs_neg, Real.sign_neg]
  simp_rw [Real.cot_eq_cos_div_sin,
    show Real.pi * -t = -(Real.pi * t) by ring,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma prawitzKernel_neg (t : ℝ) :
    prawitzKernel (-t) =
      (starRingEnd ℂ) (prawitzKernel t) := by
  unfold prawitzKernel
  apply Complex.ext
  · change (1 - |-t|) / 2 = (1 - |t|) / 2
    rw [abs_neg]
  · change
      ((1 - |-t|) * Real.cot (Real.pi * -t) +
          Real.sign (-t) / Real.pi) / 2 =
        -(((1 - |t|) * Real.cot (Real.pi * t) +
          Real.sign t / Real.pi) / 2)
    rw [abs_neg, Real.sign_neg]
    simp_rw [Real.cot_eq_cos_div_sin]
    rw [show Real.pi * -t = -(Real.pi * t) by ring,
      Real.cos_neg, Real.sin_neg, div_neg]
    ring

lemma vaalerHLimitKernel_add_two_singular_neg (t : ℝ) :
    vaalerHLimitKernel (-t) +
        2 * prawitzSingularKernel (-t) =
      -(vaalerHLimitKernel t +
        2 * prawitzSingularKernel t) := by
  rw [vaalerHLimitKernel_neg, prawitzSingularKernel_neg]
  ring

lemma intervalIntegrable_vaalerHLimitKernel_add_two_singular :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerHLimitKernel t +
          2 * prawitzSingularKernel t)
      volume (-1) 1 := by
  apply IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ => (2 : ℝ))
    (_root_.intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (2 : ℝ))
        volume (-1) 1)
  · have hm : Measurable (fun t : ℝ =>
        vaalerHLimitKernel t +
          2 * prawitzSingularKernel t) := by
      have habs : Measurable (fun t : ℝ => |t|) :=
        (continuous_abs.comp continuous_id).measurable
      have hsin : Measurable (fun t : ℝ =>
          Real.sin (Real.pi * t)) := by fun_prop
      have hcos : Measurable (fun t : ℝ =>
          Real.cos (Real.pi * t)) := by fun_prop
      have hcot : Measurable (fun t : ℝ =>
          Real.cot (Real.pi * t)) := by
        simpa only [Real.cot_eq_cos_div_sin] using hcos.div hsin
      have hA : Measurable (fun t : ℝ =>
          (1 - |t|) * Real.cot (Real.pi * t) +
            Real.sign t / Real.pi) :=
        ((measurable_const.sub habs).mul hcot).add
          (measurable_real_sign.div measurable_const)
      unfold vaalerHLimitKernel prawitzSingularKernel
      exact (measurable_const.mul hA.complex_ofReal).add
        (measurable_const.mul
          (measurable_const.div
            ((measurable_const.mul measurable_id).complex_ofReal)))
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc (-1 : ℝ) 1)).ae_ne 1]
      with t ht ht1
    rw [vaalerHLimitKernel_add_two_singular]
    have htmem : t ∈ Ioc (-1 : ℝ) 1 := by
      simpa [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htAbs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [htmem.1, htmem.2]
    have htri0 : 0 ≤ 1 - |t| := by linarith
    have htri :
        ‖((1 - |t| : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg htri0]
      linarith [abs_nonneg t]
    have hnorm :
        ‖prawitzKernel t - prawitzSingularKernel t‖ ≤
          1 / 2 := by
      by_cases ht0 : t = 0
      · subst t
        have hz :
            prawitzKernel 0 - prawitzSingularKernel 0 =
              (1 / 2 : ℝ) := by
          apply Complex.ext <;>
            simp [prawitzKernel, prawitzSingularKernel,
              Real.cot_eq_cos_div_sin]
        rw [hz, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      · rcases lt_or_gt_of_ne ht0 with htneg | htpos
        · have hk := norm_prawitzKernel_sub_singular_le_half
            (neg_pos.mpr htneg) (by linarith [htmem.1])
          have heq :
                prawitzKernel (-t) -
                  prawitzSingularKernel (-t) =
                (starRingEnd ℂ) (prawitzKernel t -
                  prawitzSingularKernel t) := by
            have hSstar :
                (starRingEnd ℂ)
                    (prawitzSingularKernel t) =
                  -prawitzSingularKernel t := by
              unfold prawitzSingularKernel
              rw [map_div₀, Complex.conj_I,
                Complex.conj_ofReal, neg_div]
            rw [prawitzKernel_neg,
              prawitzSingularKernel_neg, map_sub,
              hSstar]
          rw [← Complex.norm_conj
            (prawitzKernel t - prawitzSingularKernel t),
            ← heq]
          simpa [prawitzSingularKernel] using hk
        · simpa [prawitzSingularKernel] using
            norm_prawitzKernel_sub_singular_le_half
              htpos (lt_of_le_of_ne htmem.2 ht1)
    have htwo :
        ‖2 * (prawitzKernel t -
          prawitzSingularKernel t)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_ofNat]
      nlinarith
    exact (norm_sub_le _ _).trans (by linarith)

lemma intervalIntegral_vaalerHLimitKernel_add_two_singular :
    (∫ t : ℝ in -1..1,
      (vaalerHLimitKernel t +
        2 * prawitzSingularKernel t)) = 0 := by
  let q : ℝ → ℂ := fun t =>
    vaalerHLimitKernel t +
      2 * prawitzSingularKernel t
  have hneg :
      (fun t : ℝ => q (-t)) = fun t : ℝ => -q t := by
    funext t
    exact vaalerHLimitKernel_add_two_singular_neg t
  have hcomp := intervalIntegral.integral_comp_neg
    (f := q) (a := (-1 : ℝ)) (b := 1)
  have hsymm :
      (∫ t : ℝ in -1..1, q (-t)) =
        ∫ t : ℝ in -1..1, q t := by
    simpa using hcomp
  rw [hneg, intervalIntegral.integral_neg] at hsymm
  let J : ℂ := ∫ t : ℝ in -1..1, q t
  have hJ : -J = J := by
    simpa [J] using hsymm
  have hJJ : J + J = 0 := by
    calc
      J + J = -J + J := by rw [hJ]
      _ = 0 := neg_add_cancel J
  calc
    (∫ t : ℝ in -1..1,
      (vaalerHLimitKernel t +
        2 * prawitzSingularKernel t)) =
        J := rfl
    _ = (J + J) / 2 := by ring
    _ = 0 := by rw [hJJ]; simp

end HDP.Appendix
