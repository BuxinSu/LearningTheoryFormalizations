import HighDimensionalProbability.Appendix.Infra.BerryEsseenNumerics

/-!
# Explicit scalar certificate for Berry--Esseen

This file closes the low- and high-frequency numerical estimates and
packages them as the scalar inequality consumed by the analytic assembly.
-/

open Real Filter MeasureTheory intervalIntegral Set
open scoped Topology Interval

namespace HDP.Appendix

lemma integral_sq_exp_scaled_tail_eq
    {T A : ℝ} (hT : 0 < T) :
    (∫ u : ℝ in Ioi A,
        u ^ 2 * Real.exp (-((T * u) ^ 2 / 2))) =
      A * Real.exp (-((T * A) ^ 2 / 2)) / T ^ 2 +
        (1 / T ^ 2) *
          ∫ u : ℝ in Ioi A,
            Real.exp (-((T * u) ^ 2 / 2)) := by
  let g : ℝ → ℝ := fun u =>
    Real.exp (-((T * u) ^ 2 / 2))
  have hg : Integrable g :=
    integrable_exp_neg_scaled_sq_div_two hT
  have hsq : Integrable (fun u : ℝ => u ^ 2 * g u) := by
    simpa [g] using
      integrable_sq_mul_exp_neg_scaled_sq_div_two hT
  have hderivg (u : ℝ) :
      HasDerivAt g (-T ^ 2 * u * g u) u := by
    have hd :=
      (Real.hasDerivAt_exp (-((T * u) ^ 2 / 2))).comp u
        (((((hasDerivAt_const (x := u) T).mul
          (hasDerivAt_id u)).pow 2).div_const 2).neg)
    have hderiv :
        Real.exp (-((T * u) ^ 2 / 2)) *
            -((2 : ℝ) * (T * u) ^ (2 - 1) *
              (0 * u + T * 1) / 2) =
          -T ^ 2 * u *
            (Real.exp ∘ fun x : ℝ => -((T * x) ^ 2 / 2)) u := by
      dsimp [g]
      ring
    have hfun :
        (Real.exp ∘ fun x : ℝ => -((T * x) ^ 2 / 2)) = g := by
      funext x
      rfl
    rw [← hfun]
    exact hd.congr_deriv hderiv
  have hprod0 :
      Tendsto ((fun u : ℝ => u) * g)
        (𝓝[>] A) (𝓝 (A * g A)) := by
    have hcont :
        ContinuousAt (fun u : ℝ => u * g u) A := by
      dsimp [g]
      fun_prop
    change Tendsto (fun u : ℝ => u * g u) _ _
    exact hcont.tendsto.mono_left inf_le_left
  have hnum :
      Tendsto (fun u : ℝ => u * g u) atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ u : ℝ in atTop, 0 ≤ u * g u := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      exact mul_nonneg hu (by dsimp [g]; positivity)
    have hupper : ∀ᶠ u : ℝ in atTop,
        u * g u ≤ Real.exp (-1) / ((T ^ 2 / 2) * u) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hc : 0 < T ^ 2 / 2 := by positivity
      have hm :=
        Real.mul_exp_neg_le_exp_neg_one ((T ^ 2 / 2) * u ^ 2)
      have hcu : 0 < (T ^ 2 / 2) * u := mul_pos hc hu
      dsimp [g]
      have heq :
          u * Real.exp (-((T * u) ^ 2 / 2)) =
            ((T ^ 2 / 2) * u ^ 2 *
                Real.exp (-((T ^ 2 / 2) * u ^ 2))) /
              ((T ^ 2 / 2) * u) := by
        rw [show (T * u) ^ 2 / 2 =
          (T ^ 2 / 2) * u ^ 2 by ring]
        field_simp [hc.ne', hu.ne']
      rw [heq]
      apply (div_le_div_iff_of_pos_right hcu).2
      simpa using hm
    have hzero :
        Tendsto
          (fun u : ℝ => Real.exp (-1) / ((T ^ 2 / 2) * u))
          atTop (𝓝 0) := by
      have hc : 0 < T ^ 2 / 2 := by positivity
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul
          (tendsto_inv_atTop_zero.comp
            ((tendsto_const_mul_atTop_of_pos hc).2 tendsto_id)))
    exact squeeze_zero' hnonneg hupper hzero
  have hparts :=
    integral_Ioi_deriv_mul_eq_sub
      (a := A) (a' := A * g A) (b' := 0)
      (u := fun u : ℝ => u) (u' := fun _ => 1)
      (v := g) (v' := fun u => -T ^ 2 * u * g u)
      (fun u hu => hasDerivAt_id u)
      (fun u hu => hderivg u)
      (by
        have hi := hg.add
          ((hsq.const_mul (-T ^ 2)))
        apply hi.integrableOn.congr
        filter_upwards with u
        dsimp
        ring)
      hprod0
      (by
        change Tendsto (fun u : ℝ => u * g u) atTop (𝓝 0)
        exact hnum)
  have hparts' :
      (∫ u : ℝ in Ioi A, g u) -
          T ^ 2 *
            (∫ u : ℝ in Ioi A, u ^ 2 * g u) =
        -(A * g A) := by
    calc
      (∫ u : ℝ in Ioi A, g u) -
          T ^ 2 * (∫ u : ℝ in Ioi A, u ^ 2 * g u) =
          (∫ u : ℝ in Ioi A,
            g u - T ^ 2 * (u ^ 2 * g u)) := by
              rw [integral_sub hg.integrableOn
                (hsq.const_mul (T ^ 2)).integrableOn,
                MeasureTheory.integral_const_mul]
      _ = ∫ u : ℝ in Ioi A,
          1 * g u + u * (-T ^ 2 * u * g u) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            ring
      _ = -(A * g A) := by simpa using hparts
  have hT2 : T ^ 2 ≠ 0 := pow_ne_zero 2 hT.ne'
  dsimp [g] at hparts' ⊢
  calc
    (∫ u : ℝ in Ioi A,
        u ^ 2 * Real.exp (-((T * u) ^ 2 / 2))) =
        (A * Real.exp (-((T * A) ^ 2 / 2)) +
          ∫ u : ℝ in Ioi A,
            Real.exp (-((T * u) ^ 2 / 2))) / T ^ 2 := by
      apply (eq_div_iff hT2).2
      nlinarith [hparts']
    _ = A * Real.exp (-((T * A) ^ 2 / 2)) / T ^ 2 +
        (1 / T ^ 2) *
          ∫ u : ℝ in Ioi A,
            Real.exp (-((T * u) ^ 2 / 2)) := by ring

lemma integral_sq_exp_scaled_tail_lower
    {T A : ℝ} (hT : 0 < T) (hA : 0 < A) :
    A * Real.exp (-((T * A) ^ 2 / 2)) / T ^ 2 *
        (1 + 1 / ((T * A) ^ 2 + 1)) ≤
      ∫ u : ℝ in Ioi A,
        u ^ 2 * Real.exp (-((T * u) ^ 2 / 2)) := by
  have hm := gaussianTail_mills_lower
    (c := T ^ 2 / 2) (A := A) (by positivity) hA
  have he :
      Real.exp (-((T * A) ^ 2 / 2)) =
        Real.exp (-((T ^ 2 / 2) * A ^ 2)) := by
    congr 1
    ring
  rw [integral_sq_exp_scaled_tail_eq hT]
  rw [he]
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  have hmul :=
    mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ 1 / T ^ 2)
  calc
    A * Real.exp (-((T ^ 2 / 2) * A ^ 2)) / T ^ 2 *
        (1 + 1 / ((T * A) ^ 2 + 1)) =
      A * Real.exp (-((T ^ 2 / 2) * A ^ 2)) / T ^ 2 +
        (1 / T ^ 2) *
          (A * Real.exp (-((T ^ 2 / 2) * A ^ 2)) /
            (2 * (T ^ 2 / 2) * A ^ 2 + 1)) := by
      field_simp [hT.ne']
    _ ≤ A * Real.exp (-((T ^ 2 / 2) * A ^ 2)) / T ^ 2 +
        (1 / T ^ 2) *
          ∫ u : ℝ in Ioi A,
            Real.exp (-((T ^ 2 / 2) * u ^ 2)) := by
      gcongr
    _ = A * Real.exp (-((T ^ 2 / 2) * A ^ 2)) / T ^ 2 +
        (1 / T ^ 2) *
          ∫ u : ℝ in Ioi A,
            Real.exp (-((T * u) ^ 2 / 2)) := by
      congr 2
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      congr 1
      ring

lemma integral_sq_exp_scaled_zero_to_le
    {T A L : ℝ} (hT : 0 < T) (hA : 0 < A)
    (hL :
      L ≤ A * Real.exp (-((T * A) ^ 2 / 2)) / T ^ 2 *
        (1 + 1 / ((T * A) ^ 2 + 1))) :
    (∫ u : ℝ in 0..A,
        u ^ 2 * Real.exp (-((T * u) ^ 2 / 2))) ≤
      Real.sqrt (Real.pi / 2) / T ^ 3 - L := by
  let f : ℝ → ℝ := fun u =>
    u ^ 2 * Real.exp (-((T * u) ^ 2 / 2))
  have hf : Integrable f := by
    simpa [f] using
      integrable_sq_mul_exp_neg_scaled_sq_div_two hT
  have hsplit :=
    intervalIntegral.integral_Ici_sub_Ici'
      (a := 0) (b := A) hf.integrableOn hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ici_eq_integral_Ioi] at hsplit
  have hfull :
      (∫ u : ℝ in Ioi 0, f u) =
        Real.sqrt (Real.pi / 2) / T ^ 3 := by
    simpa [f] using
      integral_sq_mul_exp_neg_scaled_sq_div_two_Ioi hT
  have htail :
      L ≤ ∫ u : ℝ in Ioi A, f u := by
    exact hL.trans
      (by simpa [f] using
        integral_sq_exp_scaled_tail_lower hT hA)
  rw [hfull] at hsplit
  linarith

lemma integral_cube_exp_neg_mul_sq_zero_to
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    (∫ u : ℝ in 0..A,
        u ^ 3 * Real.exp (-(c * u ^ 2))) =
      (1 - (1 + c * A ^ 2) *
          Real.exp (-(c * A ^ 2))) / (2 * c ^ 2) := by
  let F : ℝ → ℝ := fun u =>
    -((1 + c * u ^ 2) * Real.exp (-(c * u ^ 2))) /
      (2 * c ^ 2)
  have hderiv (u : ℝ) :
      HasDerivAt F
        (u ^ 3 * Real.exp (-(c * u ^ 2))) u := by
    have hd :=
      (((hasDerivAt_const (x := u) 1).add
          ((hasDerivAt_pow 2 u).const_mul c)).mul
        ((Real.hasDerivAt_exp (-(c * u ^ 2))).comp u
          (((hasDerivAt_pow 2 u).const_mul c).neg))).neg.div_const
        (2 * c ^ 2)
    have hfun :
        (fun x : ℝ =>
          -((1 + c * x ^ 2) *
            Real.exp (-(c * x ^ 2))) / (2 * c ^ 2)) = F := by
      rfl
    have hval :
        -(((0 + c * ((2 : ℝ) * u ^ (2 - 1))) *
              Real.exp (-(c * u ^ 2)) +
            (1 + c * u ^ 2) *
              (Real.exp (-(c * u ^ 2)) *
                -(c * ((2 : ℝ) * u ^ (2 - 1)))))) /
            (2 * c ^ 2) =
          u ^ 3 * Real.exp (-(c * u ^ 2)) := by
      field_simp [hc.ne']
      ring
    rw [← hfun]
    exact hd.congr_deriv hval
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hderiv u)]
  · dsimp [F]
    field_simp [hc.ne']
    norm_num [Real.exp_zero]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

lemma exp_neg_lower_pow_32
    {y : ℝ} (hy0 : 0 ≤ y) (hy32 : y ≤ 32) :
    (1 - y / 32) ^ 32 ≤ Real.exp (-y) := by
  have hb : 0 ≤ 1 - y / 32 := by linarith
  have hbase :
      1 - y / 32 ≤ Real.exp (-(y / 32)) := by
    convert Real.add_one_le_exp (-(y / 32)) using 1 <;> ring
  have hp := pow_le_pow_left₀ hb hbase 32
  calc
    (1 - y / 32) ^ 32 ≤
        Real.exp (-(y / 32)) ^ 32 := hp
    _ = Real.exp (-y) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

set_option maxHeartbeats 1000000 in
/-- A fixed-window estimate for the low-frequency integral.  The parameters
`l` and `b` are the lower and upper endpoints of a numerical δ-window. -/
lemma integral_berryLowMajorant_le_of_window
    {δ l b T S E₁ E₂ C : ℝ}
    (hδ0 : 0 < δ) (hl0 : 0 < l) (hlδ : l ≤ δ)
    (hδb : δ ≤ b) (hb1 : b < 1)
    (hT : 0 < T)
    (hTcomp : T ^ 2 / 2 ≤ (1 - b ^ 2) / 3)
    (hsqrt : Real.sqrt (Real.pi / 2) ≤ S)
    (hE₁ :
      E₁ ≤ Real.exp (-((T / l) ^ 2 / 2)))
    (hE₂ :
      E₂ ≤ Real.exp (-((1 - b ^ 2) / (2 * l ^ 2))))
    (hcert :
      (1 / 6 : ℝ) *
          (S / T ^ 3 -
            (1 / l) * E₁ / T ^ 2 *
              (1 + 1 / ((T / l) ^ 2 + 1))) +
        b / 8 *
          ((1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
            (2 * ((1 - b ^ 2) / 2) ^ 2)) ≤ C) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      C * δ := by
  have hb0 : 0 < b := hδ0.trans_le hδb
  have hbone : 0 < 1 - b ^ 2 := by nlinarith
  have hAδ : 0 ≤ 1 / δ := by positivity
  have hAl : 0 < 1 / l := by positivity
  have hAA : 1 / δ ≤ 1 / l := by
    exact one_div_le_one_div_of_le hl0 hlδ
  let f₁ : ℝ → ℝ := fun u =>
    u ^ 2 * Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3))
  let g₁ : ℝ → ℝ := fun u =>
    u ^ 2 * Real.exp (-((T * u) ^ 2 / 2))
  let f₂ : ℝ → ℝ := fun u =>
    u ^ 3 * Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2))
  let g₂ : ℝ → ℝ := fun u =>
    u ^ 3 * Real.exp (-(((1 - b ^ 2) / 2) * u ^ 2))
  have hcoeff :
      T ^ 2 / 2 ≤ (1 - δ ^ 2) / 3 := by
    calc
      T ^ 2 / 2 ≤ (1 - b ^ 2) / 3 := hTcomp
      _ ≤ (1 - δ ^ 2) / 3 := by
        have hs : δ ^ 2 ≤ b ^ 2 := by
          nlinarith
        linarith
  have hf₁ : IntervalIntegrable f₁ volume 0 (1 / δ) := by
    apply Continuous.intervalIntegrable
    dsimp [f₁]
    fun_prop
  have hg₁δ : IntervalIntegrable g₁ volume 0 (1 / δ) := by
    apply Continuous.intervalIntegrable
    dsimp [g₁]
    fun_prop
  have hg₁l : IntervalIntegrable g₁ volume 0 (1 / l) := by
    apply Continuous.intervalIntegrable
    dsimp [g₁]
    fun_prop
  have hf₂ : IntervalIntegrable f₂ volume 0 (1 / δ) := by
    apply Continuous.intervalIntegrable
    dsimp [f₂]
    fun_prop
  have hg₂δ : IntervalIntegrable g₂ volume 0 (1 / δ) := by
    apply Continuous.intervalIntegrable
    dsimp [g₂]
    fun_prop
  have hg₂l : IntervalIntegrable g₂ volume 0 (1 / l) := by
    apply Continuous.intervalIntegrable
    dsimp [g₂]
    fun_prop
  have hpoint₁ (u : ℝ) : f₁ u ≤ g₁ u := by
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have he :
        Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3)) ≤
          Real.exp (-((T * u) ^ 2 / 2)) := by
      apply Real.exp_le_exp.mpr
      have hm :=
        mul_le_mul_of_nonneg_right hcoeff hu2
      nlinarith
    exact mul_le_mul_of_nonneg_left he hu2
  have hpoint₂ (u : ℝ) (hu : 0 ≤ u) : f₂ u ≤ g₂ u := by
    have hs : δ ^ 2 ≤ b ^ 2 := by nlinarith
    have he :
        Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)) ≤
          Real.exp (-(((1 - b ^ 2) / 2) * u ^ 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg u]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hfirst :
      (∫ u : ℝ in 0..1 / δ, f₁ u) ≤
        ∫ u : ℝ in 0..1 / l, g₁ u := by
    calc
      (∫ u : ℝ in 0..1 / δ, f₁ u) ≤
          ∫ u : ℝ in 0..1 / δ, g₁ u :=
        intervalIntegral.integral_mono
          hAδ hf₁ hg₁δ hpoint₁
      _ ≤ ∫ u : ℝ in 0..1 / l, g₁ u := by
        apply intervalIntegral.integral_mono_interval
          (c := 0) (d := 1 / l)
          (by rfl) hAδ hAA
        · filter_upwards with u
          dsimp [g₁]
          positivity
        · exact hg₁l
  have hsecond :
      (∫ u : ℝ in 0..1 / δ, f₂ u) ≤
        ∫ u : ℝ in 0..1 / l, g₂ u := by
    calc
      (∫ u : ℝ in 0..1 / δ, f₂ u) ≤
          ∫ u : ℝ in 0..1 / δ, g₂ u := by
        apply intervalIntegral.integral_mono_on
          hAδ hf₂ hg₂δ
        intro u hu
        exact hpoint₂ u hu.1
      _ ≤ ∫ u : ℝ in 0..1 / l, g₂ u := by
        apply intervalIntegral.integral_mono_interval
          (c := 0) (d := 1 / l)
          (by rfl) hAδ hAA
        · filter_upwards
            [ae_restrict_mem measurableSet_Ioc] with u hu
          dsimp [g₂]
          exact mul_nonneg (pow_nonneg hu.1.le 3)
            (Real.exp_pos _).le
        · exact hg₂l
  have htailE :
      (1 / l) * E₁ / T ^ 2 *
          (1 + 1 / ((T / l) ^ 2 + 1)) ≤
        (1 / l) * Real.exp (-((T / l) ^ 2 / 2)) /
            T ^ 2 *
          (1 + 1 / ((T / l) ^ 2 + 1)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ (sq_nonneg T)
    exact mul_le_mul_of_nonneg_left hE₁ (by positivity)
  have hfirstClosed :
      (∫ u : ℝ in 0..1 / l, g₁ u) ≤
        S / T ^ 3 -
          (1 / l) * E₁ / T ^ 2 *
            (1 + 1 / ((T / l) ^ 2 + 1)) := by
    have htailE' :
        (1 / l) * E₁ / T ^ 2 *
            (1 + 1 / ((T * (1 / l)) ^ 2 + 1)) ≤
          (1 / l) * Real.exp (-((T * (1 / l)) ^ 2 / 2)) /
              T ^ 2 *
            (1 + 1 / ((T * (1 / l)) ^ 2 + 1)) := by
      simpa [div_eq_mul_inv, mul_assoc] using htailE
    have hbase :=
      integral_sq_exp_scaled_zero_to_le hT hAl htailE'
    have hbase' :
        (∫ u : ℝ in 0..1 / l, g₁ u) ≤
          Real.sqrt (Real.pi / 2) / T ^ 3 -
            (1 / l) * E₁ / T ^ 2 *
              (1 + 1 / ((T / l) ^ 2 + 1)) := by
      simpa [g₁, div_eq_mul_inv, mul_assoc] using hbase
    have hsdiv :
        Real.sqrt (Real.pi / 2) / T ^ 3 ≤ S / T ^ 3 := by
      apply (div_le_div_iff_of_pos_right (by positivity)).2
      exact hsqrt
    dsimp [g₁]
    exact hbase'.trans (by linarith)
  have hsecondEq :
      (∫ u : ℝ in 0..1 / l, g₂ u) =
        (1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) *
            Real.exp (-((1 - b ^ 2) / (2 * l ^ 2)))) /
          (2 * ((1 - b ^ 2) / 2) ^ 2) := by
    have h :=
      integral_cube_exp_neg_mul_sq_zero_to
        (c := (1 - b ^ 2) / 2) (A := 1 / l)
        (by positivity) hAl.le
    dsimp [g₂]
    convert h using 1 <;>
      field_simp [hl0.ne'] <;> ring
  have hsecondClosed :
      (∫ u : ℝ in 0..1 / l, g₂ u) ≤
        (1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
          (2 * ((1 - b ^ 2) / 2) ^ 2) := by
    rw [hsecondEq]
    have hcpos :
        0 < 2 * ((1 - b ^ 2) / 2) ^ 2 := by positivity
    apply (div_le_div_iff_of_pos_right hcpos).2
    have hfac :
        0 ≤ 1 + (1 - b ^ 2) / (2 * l ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hE₂ hfac]
  have hdecomp :
      (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) =
        (δ / 6) * (∫ u : ℝ in 0..1 / δ, f₁ u) +
          (δ ^ 2 / 8) *
            (∫ u : ℝ in 0..1 / δ, f₂ u) := by
    dsimp [berryLowMajorant, f₁, f₂]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro u hu
      ring
    · exact hf₁.const_mul _
    · exact hf₂.const_mul _
  rw [hdecomp]
  calc
    (δ / 6) * (∫ u : ℝ in 0..1 / δ, f₁ u) +
        (δ ^ 2 / 8) *
          (∫ u : ℝ in 0..1 / δ, f₂ u) ≤
      (δ / 6) *
          (S / T ^ 3 -
            (1 / l) * E₁ / T ^ 2 *
              (1 + 1 / ((T / l) ^ 2 + 1))) +
        (δ ^ 2 / 8) *
          ((1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
            (2 * ((1 - b ^ 2) / 2) ^ 2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (hfirst.trans hfirstClosed) (by positivity))
        (mul_le_mul_of_nonneg_left
          (hsecond.trans hsecondClosed) (by positivity))
    _ ≤ δ *
        ((1 / 6 : ℝ) *
            (S / T ^ 3 -
              (1 / l) * E₁ / T ^ 2 *
                (1 + 1 / ((T / l) ^ 2 + 1))) +
          b / 8 *
            ((1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
              (2 * ((1 - b ^ 2) / 2) ^ 2))) := by
      have hsecondNonneg :
          0 ≤ (∫ u : ℝ in 0..1 / l, g₂ u) := by
        apply intervalIntegral.integral_nonneg hAl.le
        intro u hu
        dsimp [g₂]
        exact mul_nonneg (pow_nonneg hu.1 3)
          (Real.exp_pos _).le
      have hclosedNonneg :
          0 ≤
            (1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
              (2 * ((1 - b ^ 2) / 2) ^ 2) :=
        hsecondNonneg.trans hsecondClosed
      have hm :
          δ ^ 2 *
              ((1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
                (2 * ((1 - b ^ 2) / 2) ^ 2)) ≤
            δ * b *
              ((1 - (1 + (1 - b ^ 2) / (2 * l ^ 2)) * E₂) /
                (2 * ((1 - b ^ 2) / 2) ^ 2)) := by
        have hd2 : δ ^ 2 ≤ δ * b := by nlinarith
        exact mul_le_mul_of_nonneg_right hd2 hclosedNonneg
      nlinarith
    _ ≤ δ * C := by
      exact mul_le_mul_of_nonneg_left hcert hδ0.le
    _ = C * δ := by ring

lemma sqrt_pi_div_two_le :
    Real.sqrt (Real.pi / 2) ≤ 627 / 500 := by
  have hpi0 : 0 ≤ Real.pi / 2 := by positivity
  have hs := Real.sq_sqrt hpi0
  have hn := Real.sqrt_nonneg (Real.pi / 2)
  have hp := Real.pi_lt_d4
  nlinarith

lemma integral_berryLowMajorant_le_small
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 3 / 10) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (107 / 200) * δ := by
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := δ) (b := 3 / 10)
    (T := 389 / 500) (S := 627 / 500)
    (E₁ := 0) (E₂ := 0) (C := 107 / 200)
    hδ0 hδ0 le_rfl hδ
  · norm_num
  · norm_num
  · norm_num
  · exact sqrt_pi_div_two_le
  · positivity
  · positivity
  · norm_num

lemma integral_berryLowMajorant_le_small_tenth
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (417 / 1000) * δ := by
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := δ) (b := 1 / 10)
    (T := 203 / 250) (S := 627 / 500)
    (E₁ := 0) (E₂ := 0) (C := 417 / 1000)
    hδ0 hδ0 le_rfl hδ
  · norm_num
  · norm_num
  · norm_num
  · exact sqrt_pi_div_two_le
  · positivity
  · positivity
  · norm_num

lemma integral_berryLowMajorant_le_window_10_20
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 1 / 10 ≤ δ) (hu : δ ≤ 1 / 5) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (463 / 1000) * δ := by
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 1 / 10) (b := 1 / 5)
    (T := 4 / 5) (S := 627 / 500)
    (E₁ := 0) (E₂ := 0) (C := 463 / 1000)
    hδ0 (by norm_num) hl hu
  · norm_num
  · norm_num
  · norm_num
  · exact sqrt_pi_div_two_le
  · positivity
  · positivity
  · norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_30_33
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 3 / 10 ≤ δ) (hu : δ ≤ 33 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (263 / 500) * δ := by
  let T : ℝ := 770757 / 1000000
  let y₁ : ℝ := (T / (3 / 10)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (33 / 100 : ℝ) ^ 2) /
      (2 * (3 / 10 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 3 / 10) (b := 33 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 263 / 500)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_33_36
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 33 / 100 ≤ δ) (hu : δ ≤ 36 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (261 / 500) * δ := by
  let T : ℝ := 95219 / 125000
  let y₁ : ℝ := (T / (33 / 100)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (36 / 100 : ℝ) ^ 2) /
      (2 * (33 / 100 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 33 / 100) (b := 36 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 261 / 500)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_36_39
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 36 / 100 ≤ δ) (hu : δ ≤ 39 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (509 / 1000) * δ := by
  let T : ℝ := 375921 / 500000
  let y₁ : ℝ := (T / (36 / 100)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (39 / 100 : ℝ) ^ 2) /
      (2 * (36 / 100 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 36 / 100) (b := 39 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 509 / 1000)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_39_43
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 39 / 100 ≤ δ) (hu : δ ≤ 43 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (62 / 125) * δ := by
  let T : ℝ := 184289 / 250000
  let y₁ : ℝ := (T / (39 / 100)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (43 / 100 : ℝ) ^ 2) /
      (2 * (39 / 100 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 39 / 100) (b := 43 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 62 / 125)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_43_49
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 43 / 100 ≤ δ) (hu : δ ≤ 49 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (477 / 1000) * δ := by
  let T : ℝ := 355879 / 500000
  let y₁ : ℝ := (T / (43 / 100)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (49 / 100 : ℝ) ^ 2) /
      (2 * (43 / 100 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 43 / 100) (b := 49 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 477 / 1000)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_49_57
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 49 / 100 ≤ δ) (hu : δ ≤ 57 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (217 / 500) * δ := by
  let T : ℝ := 67087 / 100000
  let y₁ : ℝ := (T / (49 / 100)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (57 / 100 : ℝ) ^ 2) /
      (2 * (49 / 100 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 49 / 100) (b := 57 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 217 / 500)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

set_option maxHeartbeats 1000000 in
lemma integral_berryLowMajorant_le_window_57_60
    {δ : ℝ} (hδ0 : 0 < δ)
    (hl : 57 / 100 ≤ δ) (hu : δ ≤ 60 / 100) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      (69 / 200) * δ := by
  let T : ℝ := 653197 / 1000000
  let y₁ : ℝ := (T / (57 / 100)) ^ 2 / 2
  let y₂ : ℝ :=
    (1 - (60 / 100 : ℝ) ^ 2) /
      (2 * (57 / 100 : ℝ) ^ 2)
  let E₁ : ℝ := (1 - y₁ / 32) ^ 32
  let E₂ : ℝ := (1 - y₂ / 32) ^ 32
  apply integral_berryLowMajorant_le_of_window
    (δ := δ) (l := 57 / 100) (b := 60 / 100)
    (T := T) (S := 627 / 500)
    (E₁ := E₁) (E₂ := E₂) (C := 69 / 200)
    hδ0 (by norm_num) hl hu
  · norm_num
  · dsimp [T]
    norm_num
  · dsimp [T]
    norm_num
  · exact sqrt_pi_div_two_le
  · dsimp [E₁, y₁]
    apply exp_neg_lower_pow_32 <;>
      dsimp [T] <;> norm_num
  · dsimp [E₂, y₂]
    apply exp_neg_lower_pow_32 <;> norm_num
  · dsimp [T, E₁, E₂, y₁, y₂]
    norm_num

lemma integral_berryLowMajorant_le_crude
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
      25 / (288 * δ ^ 2) := by
  let g : ℝ → ℝ := fun u =>
    δ * u ^ 2 / 6 + δ ^ 2 * u ^ 3 / 8
  have hA : 0 ≤ 1 / δ := by positivity
  have hf :
      IntervalIntegrable (berryLowMajorant δ) volume
        0 (1 / δ) := by
    apply Continuous.intervalIntegrable
    change Continuous (fun u : ℝ =>
      δ * u ^ 2 / 6 *
          Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3)) +
        δ ^ 2 * u ^ 3 / 8 *
          Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)))
    fun_prop
  have hg : IntervalIntegrable g volume 0 (1 / δ) := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hmono :
      (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
        ∫ u : ℝ in 0..1 / δ, g u := by
    apply intervalIntegral.integral_mono_on hA hf hg
    intro u hu
    have ha : 0 ≤ 1 - δ ^ 2 := by nlinarith
    have he3 :
        Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        apply neg_nonpos.mpr
        positivity)
    have he2 :
        Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        apply neg_nonpos.mpr
        positivity)
    have hc1 : 0 ≤ δ * u ^ 2 / 6 := by positivity
    have hc2 : 0 ≤ δ ^ 2 * u ^ 3 / 8 := by
      exact div_nonneg
        (mul_nonneg (sq_nonneg δ) (pow_nonneg hu.1 3))
        (by norm_num)
    dsimp [berryLowMajorant, g]
    simpa only [mul_one] using
      add_le_add
        (mul_le_mul_of_nonneg_left he3 hc1)
        (mul_le_mul_of_nonneg_left he2 hc2)
  calc
    (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) ≤
        ∫ u : ℝ in 0..1 / δ, g u := hmono
    _ = 25 / (288 * δ ^ 2) := by
      have h2 : IntervalIntegrable
          (fun u : ℝ => δ * u ^ 2 / 6) volume
          0 (1 / δ) := by
        apply Continuous.intervalIntegrable
        fun_prop
      have h3 : IntervalIntegrable
          (fun u : ℝ => δ ^ 2 * u ^ 3 / 8) volume
          0 (1 / δ) := by
        apply Continuous.intervalIntegrable
        fun_prop
      dsimp [g]
      rw [intervalIntegral.integral_add h2 h3,
        intervalIntegral.integral_div,
        intervalIntegral.integral_const_mul,
        integral_pow,
        intervalIntegral.integral_div,
        intervalIntegral.integral_const_mul,
        integral_pow]
      norm_num
      field_simp [hδ0.ne']
      norm_num

lemma exp_neg_le_quadratic
    {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F : ℝ → ℝ := fun y =>
    1 - y + y ^ 2 / 2 - Real.exp (-y)
  let dF : ℝ → ℝ := fun y =>
    -1 + y + Real.exp (-y)
  have hderiv (y : ℝ) : HasDerivAt F (dF y) y := by
    have hd :=
      (((((hasDerivAt_const (x := y) 1).sub
        (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub
        ((Real.hasDerivAt_exp (-y)).comp y
          (hasDerivAt_id y).neg)))
    have hfun :
        (fun z : ℝ =>
          1 - z + z ^ 2 / 2 - Real.exp (-z)) = F := by
      rfl
    have hval :
        (0 - 1 + (2 * y ^ (2 - 1)) / 2) -
            Real.exp (-y) * -1 =
          dF y := by
      dsimp [dF]
      ring
    rw [← hfun]
    exact hd.congr_deriv hval
  have hnonneg (y : ℝ) : 0 ≤ dF y := by
    have h := Real.add_one_le_exp (-y)
    dsimp [dF]
    linarith
  have hFint : IntervalIntegrable dF volume 0 x := by
    apply Continuous.intervalIntegrable
    dsimp [dF]
    fun_prop
  have hFTC :
      (∫ y : ℝ in 0..x, dF y) = F x - F 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y) hFint]
  have hint : 0 ≤ ∫ y : ℝ in 0..x, dF y :=
    intervalIntegral.integral_nonneg hx
      (fun y hy => hnonneg y)
  have hFx : 0 ≤ F x := by
    dsimp [F] at hFTC ⊢
    norm_num [Real.exp_zero] at hFTC
    linarith
  dsimp [F] at hFx
  linarith

lemma log_three_halves_le :
    Real.log (3 / 2) ≤ 13 / 32 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := berryExpTaylorSeven_le_exp
    (y := 13 / 32) (by norm_num)
  calc
    (3 / 2 : ℝ) ≤ berryExpTaylorSeven (13 / 32) := by
      norm_num [berryExpTaylorSeven]
    _ ≤ Real.exp (13 / 32) := h

lemma integral_berryMediumMajorant_le_polynomial
    {δ : ℝ} (hδ0 : 0 < δ) :
    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
        berryMediumMajorant u) ≤
      13 / 16 - 25 / (64 * δ ^ 2) +
        1105 / (8192 * δ ^ 4) := by
  let A : ℝ := 1 / δ
  let B : ℝ := 3 / (2 * δ)
  let q : ℝ → ℝ := fun u =>
    2 / u - 5 * u / 8 + 17 * u ^ 3 / 128
  let Q : ℝ → ℝ := fun u =>
    2 * Real.log u - 5 * u ^ 2 / 16 +
      17 * u ^ 4 / 512
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hAB : A ≤ B := by
    dsimp [A, B]
    field_simp [hδ0.ne']
    norm_num
  have hf :
      IntervalIntegrable berryMediumMajorant volume A B := by
    apply ContinuousOn.intervalIntegrable
    change ContinuousOn
      (fun u : ℝ =>
        (Real.exp (-(u ^ 2 / 8)) +
          Real.exp (-(u ^ 2 / 2))) / u) _
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hAB] at hu
      exact (hA.trans_le hu.1).ne'
  have hq : IntervalIntegrable q volume A B := by
    apply ContinuousOn.intervalIntegrable
    dsimp [q]
    apply ContinuousOn.add
    · apply ContinuousOn.sub
      · apply ContinuousOn.div continuousOn_const
          continuousOn_id
        intro u hu
        rw [uIcc_of_le hAB] at hu
        exact (hA.trans_le hu.1).ne'
      · fun_prop
    · fun_prop
  have hpoint (u : ℝ) (hu : u ∈ Icc A B) :
      berryMediumMajorant u ≤ q u := by
    have hu0 : 0 < u := hA.trans_le hu.1
    have h1 := exp_neg_le_quadratic
      (x := u ^ 2 / 8) (by positivity)
    have h2 := exp_neg_le_quadratic
      (x := u ^ 2 / 2) (by positivity)
    dsimp [berryMediumMajorant, q]
    rw [div_le_iff₀ hu0]
    calc
      Real.exp (-(u ^ 2 / 8)) +
          Real.exp (-(u ^ 2 / 2)) ≤
        (1 - u ^ 2 / 8 + (u ^ 2 / 8) ^ 2 / 2) +
          (1 - u ^ 2 / 2 + (u ^ 2 / 2) ^ 2 / 2) :=
        add_le_add h1 h2
      _ = (2 / u - 5 * u / 8 + 17 * u ^ 3 / 128) * u := by
        field_simp [hu0.ne']
        ring
  have hmono :
      (∫ u : ℝ in A..B, berryMediumMajorant u) ≤
        ∫ u : ℝ in A..B, q u :=
    intervalIntegral.integral_mono_on hAB hf hq hpoint
  have hQderiv (u : ℝ) (hu : u ∈ Icc A B) :
      HasDerivAt Q (q u) u := by
    have hu0 : u ≠ 0 := (hA.trans_le hu.1).ne'
    have hd :=
      (((Real.hasDerivAt_log hu0).const_mul 2).sub
        ((hasDerivAt_pow 2 u).const_mul 5 |>.div_const 16)).add
        ((hasDerivAt_pow 4 u).const_mul 17 |>.div_const 512)
    have hfun :
        (fun z : ℝ =>
          2 * Real.log z - 5 * z ^ 2 / 16 +
            17 * z ^ 4 / 512) = Q := by rfl
    have hval :
        2 * u⁻¹ -
              (5 * (2 * u ^ (2 - 1))) / 16 +
            (17 * (4 * u ^ (4 - 1))) / 512 =
          q u := by
      dsimp [q]
      field_simp [hu0]
      ring
    rw [← hfun]
    exact hd.congr_deriv hval
  have hqeq :
      (∫ u : ℝ in A..B, q u) = Q B - Q A := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hQderiv u
        (by simpa [uIcc_of_le hAB] using hu)) hq]
  have hlog :
      Real.log B - Real.log A = Real.log (3 / 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    dsimp [A, B]
    field_simp [hδ0.ne']
  calc
    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
        berryMediumMajorant u) =
        ∫ u : ℝ in A..B, berryMediumMajorant u := rfl
    _ ≤ ∫ u : ℝ in A..B, q u := hmono
    _ = Q B - Q A := hqeq
    _ = 2 * Real.log (3 / 2) -
          25 / (64 * δ ^ 2) +
          1105 / (8192 * δ ^ 4) := by
      dsimp [Q]
      rw [show
        2 * Real.log B - 5 * B ^ 2 / 16 +
              17 * B ^ 4 / 512 -
            (2 * Real.log A - 5 * A ^ 2 / 16 +
              17 * A ^ 4 / 512) =
          2 * (Real.log B - Real.log A) -
            5 * (B ^ 2 - A ^ 2) / 16 +
            17 * (B ^ 4 - A ^ 4) / 512 by ring,
        hlog]
      dsimp [A, B]
      field_simp [hδ0.ne']
      ring
    _ ≤ 13 / 16 - 25 / (64 * δ ^ 2) +
          1105 / (8192 * δ ^ 4) := by
      linarith [log_three_halves_le]

lemma prawitz_coefficient_le :
    (21 / 20 : ℝ) / Real.pi ≤ 2100 / 6283 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_d4]

lemma inv_sqrt_two_pi_le :
    1 / Real.sqrt (2 * Real.pi) ≤ 399 / 1000 := by
  have harg : 0 ≤ 2 * Real.pi := by positivity
  have hspos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hs := Real.sq_sqrt harg
  have hpi := Real.pi_gt_d4
  have hlower :
      (1000 / 399 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have hrat : 0 ≤ (1000 / 399 : ℝ) := by norm_num
    nlinarith [sq_nonneg
      (Real.sqrt (2 * Real.pi) - (1000 / 399 : ℝ))]
  rw [div_le_iff₀ hspos]
  nlinarith

lemma gaussian_regular_add_inversion_le
    {δ : ℝ} (hδ0 : 0 < δ) :
    let T : ℝ := 3 / (2 * δ)
    berryGaussianRegularBound T +
        gaussianInversionConstant / (2 * T ^ 3) ≤
      δ * (209 / 250 - 4 * δ / 9 +
        (188643343 / 585937500) * δ ^ 2) := by
  let T : ℝ := 3 / (2 * δ)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hs := sqrt_pi_div_two_le
  have hp : Real.pi ≤ 3927 / 1250 := by
    nlinarith [Real.pi_lt_d4]
  have hp2 :
      Real.pi ^ 2 ≤ (3927 / 1250 : ℝ) ^ 2 := by
    nlinarith [Real.pi_pos.le]
  have hi := inv_sqrt_two_pi_le
  have h1 :
      Real.sqrt (Real.pi / 2) / T ≤
        (209 / 250) * δ := by
    rw [div_le_iff₀ hT]
    dsimp [T]
    field_simp [hδ0.ne']
    nlinarith
  have h2 :
      -1 / T ^ 2 = -(4 / 9) * δ ^ 2 := by
    dsimp [T]
    field_simp [hδ0.ne']
    ring
  have h3 :
      (Real.pi ^ 2 / 18) *
          Real.sqrt (Real.pi / 2) / T ^ 3 ≤
        (358117529 / 1757812500 : ℝ) * δ ^ 3 := by
    have hm :
        (Real.pi ^ 2 / 18) *
            Real.sqrt (Real.pi / 2) ≤
          ((3927 / 1250 : ℝ) ^ 2 / 18) *
            (627 / 500) := by
      have hpi2nonneg : 0 ≤ Real.pi ^ 2 / 18 := by positivity
      have hp2' :
          Real.pi ^ 2 / 18 ≤
            (3927 / 1250 : ℝ) ^ 2 / 18 := by
        linarith
      exact mul_le_mul hp2' hs (Real.sqrt_nonneg _)
        (by positivity)
    rw [div_le_iff₀ (pow_pos hT 3)]
    dsimp [T]
    field_simp [hδ0.ne']
    nlinarith
  have h4 :
      gaussianInversionConstant / (2 * T ^ 3) ≤
        (133 / 1125 : ℝ) * δ ^ 3 := by
    have hconst :
        gaussianInversionConstant / 2 =
          1 / Real.sqrt (2 * Real.pi) := by
      unfold gaussianInversionConstant
      rw [inv_eq_one_div]
      ring
    calc
      gaussianInversionConstant / (2 * T ^ 3) =
          (8 / 27 : ℝ) * δ ^ 3 *
            (1 / Real.sqrt (2 * Real.pi)) := by
        rw [show
          gaussianInversionConstant / (2 * T ^ 3) =
            (gaussianInversionConstant / 2) / T ^ 3 by ring,
          hconst]
        dsimp [T]
        field_simp [hδ0.ne']
        ring
      _ ≤ (8 / 27 : ℝ) * δ ^ 3 * (399 / 1000) := by
        exact mul_le_mul_of_nonneg_left hi (by positivity)
      _ = (133 / 1125 : ℝ) * δ ^ 3 := by ring
  dsimp [berryGaussianRegularBound]
  dsimp only [T] at h1 h2 h3 h4 ⊢
  have hc :
      (358117529 / 1757812500 : ℝ) +
          133 / 1125 =
        188643343 / 585937500 := by norm_num
  rw [show
    Real.sqrt (Real.pi / 2) / (3 / (2 * δ)) -
        1 / (3 / (2 * δ)) ^ 2 =
      Real.sqrt (Real.pi / 2) / (3 / (2 * δ)) +
        (-1 / (3 / (2 * δ)) ^ 2) by ring]
  rw [h2]
  calc
    Real.sqrt (Real.pi / 2) / (3 / (2 * δ)) +
          (-(4 / 9) * δ ^ 2) +
        (Real.pi ^ 2 / 18) *
            Real.sqrt (Real.pi / 2) /
              (3 / (2 * δ)) ^ 3 +
        gaussianInversionConstant /
            (2 * (3 / (2 * δ)) ^ 3) ≤
      (209 / 250) * δ + (-(4 / 9) * δ ^ 2) +
        (358117529 / 1757812500) * δ ^ 3 +
        (133 / 1125) * δ ^ 3 := by
      linarith
    _ = δ * (209 / 250 - 4 * δ / 9 +
        188643343 / 585937500 * δ ^ 2) := by
      rw [← hc]
      ring

lemma berryMediumPolynomial_le_eleven_twentieths
    {δ : ℝ} (hl : 19 / 25 ≤ δ) (hu : δ ≤ 9 / 10) :
    13 / 16 - 25 / (64 * δ ^ 2) +
        1105 / (8192 * δ ^ 4) ≤ 11 / 20 := by
  have hδ0 : 0 < δ := (by norm_num : (0 : ℝ) < 19 / 25).trans_le hl
  have hzlo : (19 / 25 : ℝ) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hzhi : δ ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by nlinarith
  have hp :
      (δ ^ 2 - (19 / 25 : ℝ) ^ 2) *
          (δ ^ 2 - (9 / 10 : ℝ) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by linarith) (by linarith)
  field_simp [hδ0.ne']
  nlinarith

lemma berryMediumPolynomial_le_nine_sixteenths
    {δ : ℝ} (hl : 9 / 10 ≤ δ) (hu : δ ≤ 1) :
    13 / 16 - 25 / (64 * δ ^ 2) +
        1105 / (8192 * δ ^ 4) ≤ 9 / 16 := by
  have hδ0 : 0 < δ := (by norm_num : (0 : ℝ) < 9 / 10).trans_le hl
  have hzlo : (9 / 10 : ℝ) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hzhi : δ ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith
  have hp :
      (δ ^ 2 - (9 / 10 : ℝ) ^ 2) *
          (δ ^ 2 - (1 : ℝ) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by linarith) (by linarith)
  field_simp [hδ0.ne']
  nlinarith

lemma berryScalarCertificate_of_integral_bound
    {δ D : ℝ} (hδ0 : 0 < δ)
    (hint :
      (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
          (∫ u : ℝ in 1 / δ..3 / (2 * δ),
            berryMediumMajorant u) ≤ D * δ)
    (hnum :
      (2100 / 6283 : ℝ) * D +
          (209 / 250 - 4 * δ / 9 +
            (188643343 / 585937500) * δ ^ 2) ≤ 1) :
    let T : ℝ := 3 / (2 * δ)
    berryPrawitzIntegralBound δ +
          berryGaussianRegularBound T +
        gaussianInversionConstant / (2 * T ^ 3) ≤ δ := by
  let T : ℝ := 3 / (2 * δ)
  have hcoef := prawitz_coefficient_le
  have hcoef0 : 0 ≤ (21 / 20 : ℝ) / Real.pi := by
    positivity
  have hpraw :
      berryPrawitzIntegralBound δ ≤
        (2100 / 6283 : ℝ) * D * δ := by
    dsimp [berryPrawitzIntegralBound]
    calc
      (21 / 20 : ℝ) / Real.pi *
          ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
            ∫ u : ℝ in 1 / δ..3 / (2 * δ),
              berryMediumMajorant u) ≤
        (21 / 20 : ℝ) / Real.pi * (D * δ) :=
          mul_le_mul_of_nonneg_left hint hcoef0
      _ ≤ (2100 / 6283 : ℝ) * (D * δ) := by
        exact mul_le_mul_of_nonneg_right hcoef
          (by
            have hsum_nonneg :
                0 ≤
                  (∫ u : ℝ in 0..1 / δ,
                      berryLowMajorant δ u) +
                    ∫ u : ℝ in 1 / δ..3 / (2 * δ),
                      berryMediumMajorant u := by
              have hlow0 :
                  0 ≤ ∫ u : ℝ in 0..1 / δ,
                    berryLowMajorant δ u := by
                apply intervalIntegral.integral_nonneg
                  (by positivity)
                intro u hu
                dsimp [berryLowMajorant]
                have hu0 : 0 ≤ u := hu.1
                positivity
              have hmed0 :
                  0 ≤ ∫ u : ℝ in 1 / δ..3 / (2 * δ),
                    berryMediumMajorant u := by
                have hab : 1 / δ ≤ 3 / (2 * δ) := by
                  field_simp [hδ0.ne']
                  norm_num
                apply intervalIntegral.integral_nonneg hab
                intro u hu
                dsimp [berryMediumMajorant]
                have hu0 : 0 < u :=
                  (by positivity : 0 < 1 / δ).trans_le hu.1
                exact div_nonneg (by positivity) hu0.le
              exact add_nonneg hlow0 hmed0
            exact hsum_nonneg.trans hint)
      _ = (2100 / 6283 : ℝ) * D * δ := by ring
  have hreg :=
    gaussian_regular_add_inversion_le hδ0
  dsimp only [T] at hreg ⊢
  calc
    berryPrawitzIntegralBound δ +
          berryGaussianRegularBound (3 / (2 * δ)) +
        gaussianInversionConstant /
          (2 * (3 / (2 * δ)) ^ 3) ≤
      (2100 / 6283 : ℝ) * D * δ +
        δ * (209 / 250 - 4 * δ / 9 +
          (188643343 / 585937500) * δ ^ 2) :=
      by
        rw [add_assoc]
        exact add_le_add hpraw hreg
    _ ≤ δ := by
      nlinarith

/-- The polynomial numerical expression whose bound closes the Berry–Esseen certificate. -/
noncomputable def berryNumericalExpr (C δ : ℝ) : ℝ :=
  (2100 / 6283 : ℝ) * (C + 7 / 8 * δ) +
    (209 / 250 - 4 * δ / 9 +
      (188643343 / 585937500) * δ ^ 2)

lemma berryNumericalExpr_le_of_increasing
    {C δ a b : ℝ} (ha : a ≤ δ) (hb : δ ≤ b)
    (hderiv :
      0 ≤ (2100 / 6283 : ℝ) * (7 / 8) - 4 / 9 +
        2 * (188643343 / 585937500) * a)
    (hend : berryNumericalExpr C b ≤ 1) :
    berryNumericalExpr C δ ≤ 1 := by
  have hsec :
      0 ≤ (2100 / 6283 : ℝ) * (7 / 8) - 4 / 9 +
        (188643343 / 585937500) * (b + δ) := by
    nlinarith
  have hp :=
    mul_nonneg (sub_nonneg.mpr hb) hsec
  have hmono :
      berryNumericalExpr C δ ≤ berryNumericalExpr C b := by
    dsimp [berryNumericalExpr]
    nlinarith
  exact hmono.trans hend

lemma berryNumericalExpr_le_of_decreasing
    {C δ a b : ℝ} (ha : a ≤ δ) (hb : δ ≤ b)
    (hderiv :
      (2100 / 6283 : ℝ) * (7 / 8) - 4 / 9 +
        2 * (188643343 / 585937500) * b ≤ 0)
    (hend : berryNumericalExpr C a ≤ 1) :
    berryNumericalExpr C δ ≤ 1 := by
  have hsec :
      (2100 / 6283 : ℝ) * (7 / 8) - 4 / 9 +
        (188643343 / 585937500) * (δ + a) ≤ 0 := by
    nlinarith
  have hp :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hsec
  have hmono :
      berryNumericalExpr C δ ≤ berryNumericalExpr C a := by
    dsimp [berryNumericalExpr]
    nlinarith
  exact hmono.trans hend

set_option maxHeartbeats 1000000 in
lemma berryScalarCertificate
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let T : ℝ := 3 / (2 * δ)
    berryPrawitzIntegralBound δ +
          berryGaussianRegularBound T +
        gaussianInversionConstant / (2 * T ^ 3) ≤ δ := by
  have hmed :=
    integral_berryMediumMajorant_le hδ0
  by_cases h10 : δ ≤ 1 / 10
  · have hlow :=
      integral_berryLowMajorant_le_small_tenth hδ0 h10
    have hint :
        (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
            (∫ u : ℝ in 1 / δ..3 / (2 * δ),
              berryMediumMajorant u) ≤
          (417 / 1000 + 7 / 8 * δ) * δ := by
      nlinarith
    apply berryScalarCertificate_of_integral_bound hδ0 hint
    change berryNumericalExpr (417 / 1000) δ ≤ 1
    apply berryNumericalExpr_le_of_decreasing
      (a := 0) (b := 1 / 10) hδ0.le h10
    · norm_num
    · norm_num [berryNumericalExpr]
  · have hl10 : 1 / 10 ≤ δ := by linarith
    by_cases h20 : δ ≤ 1 / 5
    · have hlow :=
        integral_berryLowMajorant_le_window_10_20
          hδ0 hl10 h20
      have hint :
          (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
              (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                berryMediumMajorant u) ≤
            (463 / 1000 + 7 / 8 * δ) * δ := by
        nlinarith
      apply berryScalarCertificate_of_integral_bound hδ0 hint
      change berryNumericalExpr (463 / 1000) δ ≤ 1
      apply berryNumericalExpr_le_of_decreasing
        (a := 1 / 10) (b := 1 / 5) hl10 h20
      · norm_num
      · norm_num [berryNumericalExpr]
    · have hl20 : 1 / 5 ≤ δ := by linarith
      by_cases h30 : δ ≤ 3 / 10
      · have hlow :=
          integral_berryLowMajorant_le_small hδ0 h30
        have hint :
            (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
                (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                  berryMediumMajorant u) ≤
              (107 / 200 + 7 / 8 * δ) * δ := by
          nlinarith
        apply berryScalarCertificate_of_integral_bound hδ0 hint
        change berryNumericalExpr (107 / 200) δ ≤ 1
        have hp :
            (δ - (1 / 5 : ℝ)) *
                (δ - (3 / 10 : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (by linarith) (by linarith)
        dsimp [berryNumericalExpr]
        nlinarith
      · have hl30 : 3 / 10 ≤ δ := by linarith
        by_cases h33 : δ ≤ 33 / 100
        · have hlow :=
            integral_berryLowMajorant_le_window_30_33
              hδ0 hl30 h33
          have hint :
              (∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
                  (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                    berryMediumMajorant u) ≤
                (263 / 500 + 7 / 8 * δ) * δ := by
            nlinarith
          apply berryScalarCertificate_of_integral_bound hδ0 hint
          change berryNumericalExpr (263 / 500) δ ≤ 1
          apply berryNumericalExpr_le_of_increasing
            (a := 3 / 10) (b := 33 / 100) hl30 h33
          · norm_num
          · norm_num [berryNumericalExpr]
        · have hl33 : 33 / 100 ≤ δ := by linarith
          by_cases h36 : δ ≤ 36 / 100
          · have hlow :=
              integral_berryLowMajorant_le_window_33_36
                hδ0 hl33 h36
            have hint :
                (∫ u : ℝ in 0..1 / δ,
                    berryLowMajorant δ u) +
                    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                      berryMediumMajorant u) ≤
                  (261 / 500 + 7 / 8 * δ) * δ := by
              nlinarith
            apply berryScalarCertificate_of_integral_bound hδ0 hint
            change berryNumericalExpr (261 / 500) δ ≤ 1
            apply berryNumericalExpr_le_of_increasing
              (a := 33 / 100) (b := 36 / 100) hl33 h36
            · norm_num
            · norm_num [berryNumericalExpr]
          · have hl36 : 36 / 100 ≤ δ := by linarith
            by_cases h39 : δ ≤ 39 / 100
            · have hlow :=
                integral_berryLowMajorant_le_window_36_39
                  hδ0 hl36 h39
              have hint :
                  (∫ u : ℝ in 0..1 / δ,
                      berryLowMajorant δ u) +
                      (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                        berryMediumMajorant u) ≤
                    (509 / 1000 + 7 / 8 * δ) * δ := by
                nlinarith
              apply berryScalarCertificate_of_integral_bound hδ0 hint
              change berryNumericalExpr (509 / 1000) δ ≤ 1
              apply berryNumericalExpr_le_of_increasing
                (a := 36 / 100) (b := 39 / 100) hl36 h39
              · norm_num
              · norm_num [berryNumericalExpr]
            · have hl39 : 39 / 100 ≤ δ := by linarith
              by_cases h43 : δ ≤ 43 / 100
              · have hlow :=
                  integral_berryLowMajorant_le_window_39_43
                    hδ0 hl39 h43
                have hint :
                    (∫ u : ℝ in 0..1 / δ,
                        berryLowMajorant δ u) +
                        (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                          berryMediumMajorant u) ≤
                      (62 / 125 + 7 / 8 * δ) * δ := by
                  nlinarith
                apply berryScalarCertificate_of_integral_bound hδ0 hint
                change berryNumericalExpr (62 / 125) δ ≤ 1
                apply berryNumericalExpr_le_of_increasing
                  (a := 39 / 100) (b := 43 / 100) hl39 h43
                · norm_num
                · norm_num [berryNumericalExpr]
              · have hl43 : 43 / 100 ≤ δ := by linarith
                by_cases h49 : δ ≤ 49 / 100
                · have hlow :=
                    integral_berryLowMajorant_le_window_43_49
                      hδ0 hl43 h49
                  have hint :
                      (∫ u : ℝ in 0..1 / δ,
                          berryLowMajorant δ u) +
                          (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                            berryMediumMajorant u) ≤
                        (477 / 1000 + 7 / 8 * δ) * δ := by
                    nlinarith
                  apply berryScalarCertificate_of_integral_bound hδ0 hint
                  change berryNumericalExpr (477 / 1000) δ ≤ 1
                  apply berryNumericalExpr_le_of_increasing
                    (a := 43 / 100) (b := 49 / 100) hl43 h49
                  · norm_num
                  · norm_num [berryNumericalExpr]
                · have hl49 : 49 / 100 ≤ δ := by linarith
                  by_cases h57 : δ ≤ 57 / 100
                  · have hlow :=
                      integral_berryLowMajorant_le_window_49_57
                        hδ0 hl49 h57
                    have hint :
                        (∫ u : ℝ in 0..1 / δ,
                            berryLowMajorant δ u) +
                            (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                              berryMediumMajorant u) ≤
                          (217 / 500 + 7 / 8 * δ) * δ := by
                      nlinarith
                    apply berryScalarCertificate_of_integral_bound hδ0 hint
                    change berryNumericalExpr (217 / 500) δ ≤ 1
                    apply berryNumericalExpr_le_of_increasing
                      (a := 49 / 100) (b := 57 / 100) hl49 h57
                    · norm_num
                    · norm_num [berryNumericalExpr]
                  · have hl57 : 57 / 100 ≤ δ := by linarith
                    by_cases h60 : δ ≤ 3 / 5
                    · have hlow :=
                        integral_berryLowMajorant_le_window_57_60
                          hδ0 hl57 (by norm_num at h60 ⊢; exact h60)
                      have hint :
                          (∫ u : ℝ in 0..1 / δ,
                              berryLowMajorant δ u) +
                              (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                berryMediumMajorant u) ≤
                            (69 / 200 + 7 / 8 * δ) * δ := by
                        nlinarith
                      apply berryScalarCertificate_of_integral_bound
                        hδ0 hint
                      change berryNumericalExpr (69 / 200) δ ≤ 1
                      apply berryNumericalExpr_le_of_increasing
                        (a := 57 / 100) (b := 3 / 5) hl57 h60
                      · norm_num
                      · norm_num [berryNumericalExpr]
                    · have hl60 : 3 / 5 ≤ δ := by linarith
                      have hlowCrude :=
                        integral_berryLowMajorant_le_crude
                          hδ0 hδ1.le
                      by_cases h62 : δ ≤ 31 / 50
                      · have hp :
                            (3 / 5 : ℝ) ^ 3 ≤ δ ^ 3 :=
                          pow_le_pow_left₀ (by norm_num) hl60 3
                        have hlow :
                            (∫ u : ℝ in 0..1 / δ,
                              berryLowMajorant δ u) ≤
                                (201 / 500) * δ := by
                          apply hlowCrude.trans
                          rw [div_le_iff₀ (by positivity :
                            0 < 288 * δ ^ 2)]
                          nlinarith
                        have hint :
                            (∫ u : ℝ in 0..1 / δ,
                                berryLowMajorant δ u) +
                                (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                  berryMediumMajorant u) ≤
                              (201 / 500 + 7 / 8 * δ) * δ := by
                          nlinarith
                        apply berryScalarCertificate_of_integral_bound
                          hδ0 hint
                        change berryNumericalExpr (201 / 500) δ ≤ 1
                        apply berryNumericalExpr_le_of_increasing
                          (a := 3 / 5) (b := 31 / 50) hl60 h62
                        · norm_num
                        · norm_num [berryNumericalExpr]
                      · have hl62 : 31 / 50 ≤ δ := by linarith
                        by_cases h65 : δ ≤ 13 / 20
                        · have hp :
                              (31 / 50 : ℝ) ^ 3 ≤ δ ^ 3 :=
                            pow_le_pow_left₀ (by norm_num) hl62 3
                          have hlow :
                              (∫ u : ℝ in 0..1 / δ,
                                berryLowMajorant δ u) ≤
                                  (73 / 200) * δ := by
                            apply hlowCrude.trans
                            rw [div_le_iff₀ (by positivity :
                              0 < 288 * δ ^ 2)]
                            nlinarith
                          have hint :
                              (∫ u : ℝ in 0..1 / δ,
                                  berryLowMajorant δ u) +
                                  (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                    berryMediumMajorant u) ≤
                                (73 / 200 + 7 / 8 * δ) * δ := by
                            nlinarith
                          apply berryScalarCertificate_of_integral_bound
                            hδ0 hint
                          change berryNumericalExpr (73 / 200) δ ≤ 1
                          apply berryNumericalExpr_le_of_increasing
                            (a := 31 / 50) (b := 13 / 20) hl62 h65
                          · norm_num
                          · norm_num [berryNumericalExpr]
                        · have hl65 : 13 / 20 ≤ δ := by linarith
                          by_cases h70 : δ ≤ 7 / 10
                          · have hp :
                                (13 / 20 : ℝ) ^ 3 ≤ δ ^ 3 :=
                              pow_le_pow_left₀ (by norm_num) hl65 3
                            have hlow :
                                (∫ u : ℝ in 0..1 / δ,
                                  berryLowMajorant δ u) ≤
                                    (317 / 1000) * δ := by
                              apply hlowCrude.trans
                              rw [div_le_iff₀ (by positivity :
                                0 < 288 * δ ^ 2)]
                              nlinarith
                            have hint :
                                (∫ u : ℝ in 0..1 / δ,
                                    berryLowMajorant δ u) +
                                    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                      berryMediumMajorant u) ≤
                                  (317 / 1000 + 7 / 8 * δ) * δ := by
                              nlinarith
                            apply berryScalarCertificate_of_integral_bound
                              hδ0 hint
                            change berryNumericalExpr (317 / 1000) δ ≤ 1
                            apply berryNumericalExpr_le_of_increasing
                              (a := 13 / 20) (b := 7 / 10) hl65 h70
                            · norm_num
                            · norm_num [berryNumericalExpr]
                          · have hl70 : 7 / 10 ≤ δ := by linarith
                            by_cases h76 : δ ≤ 19 / 25
                            · have hp :
                                  (7 / 10 : ℝ) ^ 3 ≤ δ ^ 3 :=
                                pow_le_pow_left₀ (by norm_num) hl70 3
                              have hlow :
                                  (∫ u : ℝ in 0..1 / δ,
                                    berryLowMajorant δ u) ≤
                                      (127 / 500) * δ := by
                                apply hlowCrude.trans
                                rw [div_le_iff₀ (by positivity :
                                  0 < 288 * δ ^ 2)]
                                nlinarith
                              have hint :
                                  (∫ u : ℝ in 0..1 / δ,
                                      berryLowMajorant δ u) +
                                      (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                        berryMediumMajorant u) ≤
                                    (127 / 500 + 7 / 8 * δ) * δ := by
                                nlinarith
                              apply
                                berryScalarCertificate_of_integral_bound
                                  hδ0 hint
                              change
                                berryNumericalExpr (127 / 500) δ ≤ 1
                              apply berryNumericalExpr_le_of_increasing
                                (a := 7 / 10) (b := 19 / 25) hl70 h76
                              · norm_num
                              · norm_num [berryNumericalExpr]
                            · have hl76 : 19 / 25 ≤ δ := by linarith
                              have hmedPoly :=
                                integral_berryMediumMajorant_le_polynomial
                                  hδ0
                              by_cases h80 : δ ≤ 4 / 5
                              · have hmedClosed :=
                                  hmedPoly.trans
                                    (berryMediumPolynomial_le_eleven_twentieths
                                      hl76 (h80.trans (by norm_num)))
                                have hp :
                                    (19 / 25 : ℝ) ^ 3 ≤ δ ^ 3 :=
                                  pow_le_pow_left₀ (by norm_num) hl76 3
                                have hlow :
                                    (∫ u : ℝ in 0..1 / δ,
                                      berryLowMajorant δ u) ≤
                                        (99 / 500) * δ := by
                                  apply hlowCrude.trans
                                  rw [div_le_iff₀ (by positivity :
                                    0 < 288 * δ ^ 2)]
                                  nlinarith
                                have hmed' :
                                    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                      berryMediumMajorant u) ≤
                                        (55 / 76) * δ := by
                                  calc
                                    _ ≤ 11 / 20 := hmedClosed
                                    _ ≤ (55 / 76) * δ := by
                                      nlinarith
                                have hint :
                                    (∫ u : ℝ in 0..1 / δ,
                                        berryLowMajorant δ u) +
                                        (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                          berryMediumMajorant u) ≤
                                      (923 / 1000) * δ := by
                                  nlinarith
                                apply
                                  berryScalarCertificate_of_integral_bound
                                    hδ0 hint
                                have hsec :
                                    0 ≤ -(4 / 9 : ℝ) +
                                      (188643343 / 585937500) *
                                        ((4 / 5 : ℝ) + δ) := by
                                  nlinarith
                                have hpmono :=
                                  mul_nonneg
                                    (sub_nonneg.mpr h80) hsec
                                norm_num
                                nlinarith
                              · have hl80 : 4 / 5 ≤ δ := by linarith
                                by_cases h90 : δ ≤ 9 / 10
                                · have hmedClosed :=
                                    hmedPoly.trans
                                      (berryMediumPolynomial_le_eleven_twentieths
                                        (by linarith) h90)
                                  have hp :
                                      (4 / 5 : ℝ) ^ 3 ≤ δ ^ 3 :=
                                    pow_le_pow_left₀ (by norm_num) hl80 3
                                  have hlow :
                                      (∫ u : ℝ in 0..1 / δ,
                                        berryLowMajorant δ u) ≤
                                          (625 / 36864) * 10 * δ := by
                                    apply hlowCrude.trans
                                    rw [div_le_iff₀ (by positivity :
                                      0 < 288 * δ ^ 2)]
                                    nlinarith
                                  have hmed' :
                                      (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                        berryMediumMajorant u) ≤
                                          (11 / 16) * δ := by
                                    calc
                                      _ ≤ 11 / 20 := hmedClosed
                                      _ ≤ (11 / 16) * δ := by
                                        nlinarith
                                  have hint :
                                      (∫ u : ℝ in 0..1 / δ,
                                          berryLowMajorant δ u) +
                                          (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                            berryMediumMajorant u) ≤
                                        (429 / 500) * δ := by
                                    nlinarith
                                  apply
                                    berryScalarCertificate_of_integral_bound
                                      hδ0 hint
                                  have hsec :
                                      0 ≤ -(4 / 9 : ℝ) +
                                        (188643343 / 585937500) *
                                          ((9 / 10 : ℝ) + δ) := by
                                    nlinarith
                                  have hpmono :=
                                    mul_nonneg
                                      (sub_nonneg.mpr h90) hsec
                                  norm_num
                                  nlinarith
                                · have hl90 : 9 / 10 ≤ δ := by linarith
                                  have hmedClosed :=
                                    hmedPoly.trans
                                      (berryMediumPolynomial_le_nine_sixteenths
                                        hl90 hδ1.le)
                                  have hp :
                                      (9 / 10 : ℝ) ^ 3 ≤ δ ^ 3 :=
                                    pow_le_pow_left₀ (by norm_num) hl90 3
                                  have hlow :
                                      (∫ u : ℝ in 0..1 / δ,
                                        berryLowMajorant δ u) ≤
                                          (3125 / 26244) * δ := by
                                    apply hlowCrude.trans
                                    rw [div_le_iff₀ (by positivity :
                                      0 < 288 * δ ^ 2)]
                                    nlinarith
                                  have hmed' :
                                      (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                        berryMediumMajorant u) ≤
                                          (5 / 8) * δ := by
                                    calc
                                      _ ≤ 9 / 16 := hmedClosed
                                      _ ≤ (5 / 8) * δ := by
                                        nlinarith
                                  have hint :
                                      (∫ u : ℝ in 0..1 / δ,
                                          berryLowMajorant δ u) +
                                          (∫ u : ℝ in 1 / δ..3 / (2 * δ),
                                            berryMediumMajorant u) ≤
                                        (149 / 200) * δ := by
                                    nlinarith
                                  apply
                                    berryScalarCertificate_of_integral_bound
                                      hδ0 hint
                                  have hsec :
                                      0 ≤ -(4 / 9 : ℝ) +
                                        (188643343 / 585937500) *
                                          ((1 : ℝ) + δ) := by
                                    nlinarith
                                  have hpmono :=
                                    mul_nonneg
                                      (sub_nonneg.mpr hδ1.le) hsec
                                  norm_num
                                  nlinarith

end HDP.Appendix
