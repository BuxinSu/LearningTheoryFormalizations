import HighDimensionalProbability.Appendix.Infra.BerryEsseenIntegral

open Real Filter MeasureTheory intervalIntegral Set
open scoped Topology Interval

namespace HDP.Appendix

/-! ## A rational exponential certificate -/

/-- The seventh Taylor polynomial of the exponential function. -/
noncomputable def berryExpTaylorSeven (y : ℝ) : ℝ :=
  1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 +
    y ^ 5 / 120 + y ^ 6 / 720 + y ^ 7 / 5040

lemma berryExpTaylorSeven_le_exp {y : ℝ} (hy : 0 ≤ y) :
    berryExpTaylorSeven y ≤ Real.exp y := by
  have h := Real.sum_le_exp_of_nonneg hy 8
  norm_num [Finset.sum_range_succ, Nat.factorial,
    berryExpTaylorSeven] at h ⊢
  exact h

lemma exp_neg_le_inv_berryExpTaylorSeven
    {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 / berryExpTaylorSeven y := by
  have hp := berryExpTaylorSeven_le_exp hy
  have hp0 : 0 < berryExpTaylorSeven y := by
    dsimp [berryExpTaylorSeven]
    positivity
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos y) hp0).2 hp

/-- Exact rational positivity certificate behind the exponential estimate
used for the medium-frequency integral.  The two cases are respectively a
Bernstein-basis certificate on `[0,4/5]` and a positive-coefficient expansion
about `4/5`. -/
lemma berryExpTaylorSeven_rational_certificate
    (y : ℝ) (hy : 0 ≤ y) :
    160 * y *
        (berryExpTaylorSeven y +
          berryExpTaylorSeven (4 * y)) ≤
      63 * berryExpTaylorSeven y *
        berryExpTaylorSeven (4 * y) := by
  let R : ℝ :=
    63 * berryExpTaylorSeven y *
        berryExpTaylorSeven (4 * y) -
      160 * y *
        (berryExpTaylorSeven y +
          berryExpTaylorSeven (4 * y))
  have hR : 0 ≤ R := by
    by_cases hsmall : y ≤ 4 / 5
    · let x : ℝ := 5 * y / 4
      have hx0 : 0 ≤ x := by
        dsimp [x]
        positivity
      have hx1 : x ≤ 1 := by
        dsimp [x]
        linarith
      have hid :
          R =
            63 * (1 - x) ^ 14 +
            878 * x * (1 - x) ^ 13 +
            5673 * x ^ 2 * (1 - x) ^ 12 +
            (562492 / 25 : ℝ) * x ^ 3 * (1 - x) ^ 11 +
            (4581413 / 75 : ℝ) * x ^ 4 * (1 - x) ^ 10 +
            (74853026 / 625 : ℝ) * x ^ 5 * (1 - x) ^ 9 +
            (326522083 / 1875 : ℝ) * x ^ 6 * (1 - x) ^ 8 +
            (133306070504 / 703125 : ℝ) *
              x ^ 7 * (1 - x) ^ 7 +
            (2103011787967 / 13671875 : ℝ) *
              x ^ 8 * (1 - x) ^ 6 +
            (3738456130594 / 41015625 : ℝ) *
              x ^ 9 * (1 - x) ^ 5 +
            (582001523421341 / 15380859375 : ℝ) *
              x ^ 10 * (1 - x) ^ 4 +
            (17414865518532 / 1708984375 : ℝ) *
              x ^ 11 * (1 - x) ^ 3 +
            (119070895690463 / 76904296875 : ℝ) *
              x ^ 12 * (1 - x) ^ 2 +
            (43629352434898 / 384521484375 : ℝ) *
              x ^ 13 * (1 - x) +
            (30771753107503 / 3204345703125 : ℝ) *
              x ^ 14 := by
        dsimp [R, x, berryExpTaylorSeven]
        ring
      rw [hid]
      positivity
    · let z : ℝ := y - 4 / 5
      have hz : 0 ≤ z := by
        dsimp [z]
        linarith
      have hid :
          R =
            (30771753107503 / 3204345703125 : ℝ) +
            (50419954910669 / 1922607421875 : ℝ) * z +
            (18065498052211 / 12207031250 : ℝ) * z ^ 2 +
            (14470854235761 / 2441406250 : ℝ) * z ^ 3 +
            (218744385258041 / 17578125000 : ℝ) * z ^ 4 +
            (59123830197733 / 3515625000 : ℝ) * z ^ 5 +
            (2446368413959 / 156250000 : ℝ) * z ^ 6 +
            (20106771947987 / 1968750000 : ℝ) * z ^ 7 +
            (456270077453 / 98437500 : ℝ) * z ^ 8 +
            (227447413 / 156250 : ℝ) * z ^ 9 +
            (15472504 / 46875 : ℝ) * z ^ 10 +
            (1684942 / 28125 : ℝ) * z ^ 11 +
            (15704 / 1875 : ℝ) * z ^ 12 +
            (304 / 375 : ℝ) * z ^ 13 +
            (64 / 1575 : ℝ) * z ^ 14 := by
        dsimp [R, z, berryExpTaylorSeven]
        ring
      rw [hid]
      positivity
  dsimp [R] at hR
  linarith

lemma mul_exp_neg_add_exp_neg_four_le
    (y : ℝ) (hy : 0 ≤ y) :
    y * (Real.exp (-y) + Real.exp (-(4 * y))) ≤
      63 / 160 := by
  have h1 := exp_neg_le_inv_berryExpTaylorSeven hy
  have h4 := exp_neg_le_inv_berryExpTaylorSeven
    (y := 4 * y) (mul_nonneg (by norm_num) hy)
  have hp0 : 0 < berryExpTaylorSeven y := by
    dsimp [berryExpTaylorSeven]
    positivity
  have hp40 : 0 < berryExpTaylorSeven (4 * y) := by
    dsimp [berryExpTaylorSeven]
    positivity
  have hsum :
      Real.exp (-y) + Real.exp (-(4 * y)) ≤
        1 / berryExpTaylorSeven y +
          1 / berryExpTaylorSeven (4 * y) :=
    add_le_add h1 h4
  calc
    y * (Real.exp (-y) + Real.exp (-(4 * y))) ≤
        y * (1 / berryExpTaylorSeven y +
          1 / berryExpTaylorSeven (4 * y)) :=
      mul_le_mul_of_nonneg_left hsum hy
    _ ≤ 63 / 160 := by
      have hcert :=
        berryExpTaylorSeven_rational_certificate y hy
      have hp40' : berryExpTaylorSeven (y * 4) ≠ 0 := by
        simpa [mul_comm] using hp40.ne'
      rw [show
        y * (1 / berryExpTaylorSeven y +
            1 / berryExpTaylorSeven (4 * y)) =
          y * (berryExpTaylorSeven y +
              berryExpTaylorSeven (4 * y)) /
            (berryExpTaylorSeven y *
              berryExpTaylorSeven (4 * y)) by
        field_simp [hp0.ne', hp40.ne', hp40', mul_comm]
        ring]
      rw [div_le_iff₀ (mul_pos hp0 hp40)]
      nlinarith

/-! ## Medium-frequency integral -/

lemma berryMediumMajorant_le_inv_cube
    {u : ℝ} (hu : 0 < u) :
    berryMediumMajorant u ≤ 63 / (20 * u ^ 3) := by
  let y : ℝ := u ^ 2 / 8
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have h := mul_exp_neg_add_exp_neg_four_le y hy
  have hexp :
      Real.exp (-(u ^ 2 / 8)) +
          Real.exp (-(u ^ 2 / 2)) =
        Real.exp (-y) + Real.exp (-(4 * y)) := by
    dsimp [y]
    congr 1
    ring
  dsimp [berryMediumMajorant]
  rw [hexp]
  calc
    (Real.exp (-y) + Real.exp (-(4 * y))) / u =
        8 * (y * (Real.exp (-y) +
          Real.exp (-(4 * y)))) / u ^ 3 := by
      dsimp [y]
      field_simp [hu.ne']
    _ ≤ 8 * (63 / 160) / u ^ 3 := by
      gcongr
    _ = 63 / (20 * u ^ 3) := by ring

/-- Exact medium-frequency contribution used in the constant-one
Berry--Esseen certificate. -/
lemma integral_berryMediumMajorant_le
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
      berryMediumMajorant u) ≤
        7 / 8 * δ ^ 2 := by
  have hA : 0 < 1 / δ := by positivity
  have hAB : 1 / δ ≤ 3 / (2 * δ) := by
    field_simp [hδ.ne']
    nlinarith
  have hf : IntervalIntegrable berryMediumMajorant volume
      (1 / δ) (3 / (2 * δ)) := by
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
  have hg : IntervalIntegrable
      (fun u : ℝ => 63 / (20 * u ^ 3)) volume
      (1 / δ) (3 / (2 * δ)) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro u hu
      rw [uIcc_of_le hAB] at hu
      exact mul_ne_zero (by norm_num)
        (pow_ne_zero 3 (hA.trans_le hu.1).ne')
  have hmono :
      (∫ u : ℝ in 1 / δ..3 / (2 * δ),
        berryMediumMajorant u) ≤
      ∫ u : ℝ in 1 / δ..3 / (2 * δ),
        63 / (20 * u ^ 3) := by
    apply intervalIntegral.integral_mono_on hAB hf hg
    intro u hu
    exact berryMediumMajorant_le_inv_cube
      (hA.trans_le hu.1)
  calc
    (∫ u : ℝ in 1 / δ..3 / (2 * δ),
      berryMediumMajorant u) ≤
        ∫ u : ℝ in 1 / δ..3 / (2 * δ),
          63 / (20 * u ^ 3) := hmono
    _ = 7 / 8 * δ ^ 2 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => -(63 / 40) / u ^ 2)
        (f' := fun u : ℝ => 63 / (20 * u ^ 3))]
      · field_simp [hδ.ne']
        ring
      · intro u hu
        rw [uIcc_of_le hAB] at hu
        have hu0 : u ≠ 0 := (hA.trans_le hu.1).ne'
        have hd :=
          (hasDerivAt_const (x := u) (-(63 / 40))).div
            (hasDerivAt_pow 2 u) (pow_ne_zero 2 hu0)
        have hderiv :
            (0 * u ^ 2 -
                -(63 / 40) * ((2 : ℝ) * u ^ (2 - 1))) /
                (u ^ 2) ^ 2 =
              63 / (20 * u ^ 3) := by
          field_simp [hu0]
          ring
        have hfun :
            ((fun x : ℝ => -(63 / 40)) /
                fun x : ℝ => x ^ 2) =
              (fun x : ℝ => -(63 / 40) / x ^ 2) := by
          rfl
        rw [← hfun]
        exact hd.congr_deriv hderiv
      · exact hg

/-! ## Gaussian tail estimates -/

/-- A one-sided Mills lower bound, in the normalization used by the
low-frequency Berry--Esseen integral. -/
lemma gaussianTail_mills_lower
    {c A : ℝ} (hc : 0 < c) (_hA : 0 < A) :
    A * Real.exp (-(c * A ^ 2)) / (2 * c * A ^ 2 + 1) ≤
      ∫ u : ℝ in Ioi A, Real.exp (-(c * u ^ 2)) := by
  let g : ℝ → ℝ := fun u => Real.exp (-(c * u ^ 2))
  let F : ℝ → ℝ := fun u =>
    u * g u / (2 * c * u ^ 2 + 1)
  let dF : ℝ → ℝ := fun u =>
    g u * (1 - 4 * c * u ^ 2 -
      4 * c ^ 2 * u ^ 4) /
        (2 * c * u ^ 2 + 1) ^ 2
  have hg : Integrable g := by
    dsimp [g]
    simpa [mul_comm] using integrable_exp_neg_mul_sq hc
  have hden (u : ℝ) : 0 < 2 * c * u ^ 2 + 1 := by
    positivity
  have hFderiv (u : ℝ) : HasDerivAt F (dF u) u := by
    have hd :=
      (((hasDerivAt_id u).mul
        ((Real.hasDerivAt_exp (-(c * u ^ 2))).comp u
          (((hasDerivAt_pow 2 u).const_mul c).neg))).div
        (((hasDerivAt_pow 2 u).const_mul (2 * c)).add_const 1)
        (hden u).ne')
    have hderiv :
        ((1 * Real.exp (-(c * u ^ 2)) +
              u * (Real.exp (-(c * u ^ 2)) *
                -(c * ((2 : ℝ) * u ^ (2 - 1))))) *
              (2 * c * u ^ 2 + 1) -
            u * Real.exp (-(c * u ^ 2)) *
              ((2 * c) * ((2 : ℝ) * u ^ (2 - 1)) + 0)) /
            (2 * c * u ^ 2 + 1) ^ 2 =
          dF u := by
      dsimp [dF, g]
      field_simp [(hden u).ne']
      ring
    have hfun :
        ((fun x : ℝ => x) *
            (fun x : ℝ => Real.exp (-(c * x ^ 2)))) /
            (fun x : ℝ => 2 * c * x ^ 2 + 1) =
          F := by
      funext x
      rfl
    rw [← hfun]
    exact hd.congr_deriv (by
      simpa [Function.comp_apply] using hderiv)
  have hdFint (B : ℝ) :
      IntervalIntegrable dF volume A B := by
    apply Continuous.intervalIntegrable
    dsimp [dF, g]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro u
      exact pow_ne_zero 2 (hden u).ne'
  have hpoint (u : ℝ) :
      -dF u ≤ g u := by
    have hg0 : 0 ≤ g u := by
      dsimp [g]
      positivity
    have hd0 : 0 < (2 * c * u ^ 2 + 1) ^ 2 := by
      positivity
    dsimp only [dF]
    rw [show
      -(g u * (1 - 4 * c * u ^ 2 -
          4 * c ^ 2 * u ^ 4) /
        (2 * c * u ^ 2 + 1) ^ 2) =
      (-g u * (1 - 4 * c * u ^ 2 -
          4 * c ^ 2 * u ^ 4)) /
        (2 * c * u ^ 2 + 1) ^ 2 by ring]
    rw [div_le_iff₀ hd0]
    nlinarith [sq_nonneg (2 * c * u ^ 2)]
  have hfinite (B : ℝ) (hB : A ≤ B) :
      F A - F B ≤ ∫ u : ℝ in A..B, g u := by
    have hneg :
        (∫ u : ℝ in A..B, -dF u) =
          F A - F B := by
      rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun u hu => hFderiv u) (hdFint B)]
      ring
    rw [← hneg]
    apply intervalIntegral.integral_mono_on hB
    · exact (hdFint B).neg
    · exact hg.intervalIntegrable
    · intro u hu
      exact hpoint u
  have hnum :
      Tendsto (fun u : ℝ => u * g u) atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ u : ℝ in atTop, 0 ≤ u * g u := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      exact mul_nonneg hu (by dsimp [g]; positivity)
    have hupper : ∀ᶠ u : ℝ in atTop,
        u * g u ≤ Real.exp (-1) / (c * u) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hm := Real.mul_exp_neg_le_exp_neg_one (c * u ^ 2)
      have hcu : 0 < c * u := mul_pos hc hu
      dsimp [g]
      have heq : u * Real.exp (-(c * u ^ 2)) =
          (c * u ^ 2 * Real.exp (-(c * u ^ 2))) /
            (c * u) := by
        field_simp [hc.ne', hu.ne']
      rw [heq]
      apply (div_le_div_iff_of_pos_right hcu).2
      simpa using hm
    have hzero :
        Tendsto (fun u : ℝ => Real.exp (-1) / (c * u))
          atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul
          (tendsto_inv_atTop_zero.comp
            ((tendsto_const_mul_atTop_of_pos hc).2 tendsto_id)))
    exact squeeze_zero' hnonneg hupper hzero
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ u : ℝ in atTop, 0 ≤ F u := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      dsimp [F]
      positivity
    have hupper : ∀ᶠ u : ℝ in atTop, F u ≤ u * g u := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      dsimp [F]
      have hn : 0 ≤ u * g u := by
        exact mul_nonneg hu (by dsimp [g]; positivity)
      exact (div_le_iff₀ (hden u)).2 (by
        have hx : 0 ≤ (u * g u) * (2 * c * u ^ 2) := by
          positivity
        nlinarith)
    exact squeeze_zero' hnonneg hupper hnum
  have hintlim :
      Tendsto (fun B : ℝ => ∫ u : ℝ in A..B, g u)
        atTop (𝓝 (∫ u : ℝ in Ioi A, g u)) :=
    intervalIntegral_tendsto_integral_Ioi A
      hg.integrableOn tendsto_id
  have hleft :
      Tendsto (fun B : ℝ => F A - F B)
        atTop (𝓝 (F A)) := by
    simpa using tendsto_const_nhds.sub hFlim
  have hevent :
      ∀ᶠ B : ℝ in atTop,
        F A - F B ≤ ∫ u : ℝ in A..B, g u := by
    filter_upwards [eventually_ge_atTop A] with B hB
    exact hfinite B hB
  have hlim :=
    le_of_tendsto_of_tendsto hleft hintlim hevent
  simpa [F, g] using hlim

end HDP.Appendix
