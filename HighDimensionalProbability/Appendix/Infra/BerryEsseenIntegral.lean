import HighDimensionalProbability.Appendix.Infra.BerryEsseenAssembly

open Real Complex Filter MeasureTheory ProbabilityTheory intervalIntegral Set
open scoped Interval Topology FourierTransform

namespace HDP.Appendix

/-- The low-frequency majorant used in the Berry--Esseen integral estimate. -/
noncomputable def berryLowMajorant (δ u : ℝ) : ℝ :=
  δ * u ^ 2 / 6 *
      Real.exp (-((1 - δ ^ 2) * u ^ 2 / 3)) +
    δ ^ 2 * u ^ 3 / 8 *
      Real.exp (-((1 - δ ^ 2) * u ^ 2 / 2))

/-- The medium-frequency majorant used in the Berry--Esseen integral estimate. -/
noncomputable def berryMediumMajorant (u : ℝ) : ℝ :=
  (Real.exp (-(u ^ 2 / 8)) +
    Real.exp (-(u ^ 2 / 2))) / u

/-- The characteristic-function contribution to the final Prawitz
smoothing estimate. -/
noncomputable def berryPrawitzIntegralBound (δ : ℝ) : ℝ :=
  (21 / 20 : ℝ) / Real.pi *
    ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
      ∫ u : ℝ in 1 / δ..3 / (2 * δ),
        berryMediumMajorant u)

/-- The closed Gaussian regular-kernel contribution at scale `T`. -/
noncomputable def berryGaussianRegularBound (T : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 2) / T - 1 / T ^ 2 +
    (Real.pi ^ 2 / 18) *
      Real.sqrt (Real.pi / 2) / T ^ 3

lemma norm_vaalerCharDifference_neg
    (μ ν : Measure ℝ) (t : ℝ) :
    ‖vaalerCharDifference μ ν (-t)‖ =
      ‖vaalerCharDifference μ ν t‖ := by
  unfold vaalerCharDifference
  rw [show 2 * Real.pi * -t =
    -(2 * Real.pi * t) by ring,
    charFun_neg, charFun_neg, ← map_sub, Complex.norm_conj]

/-- On the central half of the Prawitz window, the scaled characteristic
difference has a removable singularity with an explicit linear majorant. -/
lemma norm_vaalerCharDifference_scaledNormalizedSum_gaussian_le_small
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n)
    {δ T : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT0 : 0 < T)
    (hδ : δ =
      (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n)
    (hwindow : δ * T / 2 ≤ 1) (a : ℝ) :
    ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference
          (scaledCenteredMeasure
            (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
              ∑ k ∈ Finset.range n, X k ω)) a T)
          (scaledCenteredMeasure
            (gaussianReal 0 1) a T) t‖ ≤
        (δ * |T| ^ 3 / 6 + δ ^ 2 * |T| ^ 4 / 8) *
          |t| := by
  intro t ht
  have ht1 : |t| ≤ 1 := ht.trans (by norm_num)
  have hcond :
      (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n *
          |T * t| ≤ 1 := by
    rw [← hδ, abs_mul]
    rw [abs_of_pos hT0]
    calc
      δ * (T * |t|) ≤ δ * (T * (1 / 2)) := by
        gcongr
      _ = δ * T / 2 := by ring
      _ ≤ 1 := hwindow
  have hlow :=
    norm_charFun_normalizedSum_sub_gaussian_le_berryLow
      hindep hident hX hmean hsecond hn (T * t) hcond
  letI : IsProbabilityMeasure
      (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, X k ω)) := by
    apply Measure.isProbabilityMeasure_map
    apply AEMeasurable.const_mul
    have hsume := Finset.aemeasurable_sum
      (Finset.range n) (fun i hi =>
        (hident i).aemeasurable_fst)
    exact hsume.congr (ae_of_all _ fun x => by
      simp only [Finset.sum_apply])
  rw [norm_vaalerCharDifference_scaledCentered_gaussian]
  calc
    ‖charFun
          (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, X k ω)) (T * t) -
        (Real.exp (-((T * t) ^ 2 / 2)) : ℂ)‖ ≤
      δ * |T * t| ^ 3 / 6 *
          Real.exp (-((1 - δ ^ 2) * (T * t) ^ 2 / 3)) +
        δ ^ 2 * (T * t) ^ 4 / 8 *
          Real.exp (-((1 - δ ^ 2) * (T * t) ^ 2 / 2)) := by
      simpa [hδ] using hlow
    _ ≤ δ * |T * t| ^ 3 / 6 +
        δ ^ 2 * (T * t) ^ 4 / 8 := by
      have hc : 0 ≤ 1 - δ ^ 2 := by nlinarith
      have he3 :
          Real.exp (-((1 - δ ^ 2) * (T * t) ^ 2 / 3)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          apply neg_nonpos.mpr
          positivity)
      have he2 :
          Real.exp (-((1 - δ ^ 2) * (T * t) ^ 2 / 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          apply neg_nonpos.mpr
          positivity)
      have hcfirst :
          0 ≤ δ * |T * t| ^ 3 / 6 :=
        div_nonneg
          (mul_nonneg hδ0.le
            (pow_nonneg (abs_nonneg (T * t)) 3))
          (by norm_num)
      have hcsecond :
          0 ≤ δ ^ 2 * (T * t) ^ 4 / 8 :=
        div_nonneg
          (mul_nonneg (sq_nonneg δ)
            (Even.pow_nonneg (by decide) (T * t)))
          (by norm_num)
      simpa only [mul_one] using
        add_le_add
          (mul_le_mul_of_nonneg_left he3 hcfirst)
          (mul_le_mul_of_nonneg_left he2 hcsecond)
    _ ≤ (δ * |T| ^ 3 / 6 + δ ^ 2 * |T| ^ 4 / 8) *
          |t| := by
      rw [abs_mul]
      have hpow :
          (T * t) ^ 4 = |T| ^ 4 * |t| ^ 4 := by
        rw [abs_of_pos hT0, mul_pow]
        congr 1
        rw [show t ^ 4 = (t ^ 2) ^ 2 by ring,
          show |t| ^ 4 = (|t| ^ 2) ^ 2 by ring,
          sq_abs]
      rw [hpow]
      have ht2 : |t| ^ 2 ≤ |t| := by
        have hm :=
          mul_le_mul_of_nonneg_left ht1 (abs_nonneg t)
        nlinarith
      have ht3 : |t| ^ 3 ≤ |t| := by
        calc
          |t| ^ 3 = |t| ^ 2 * |t| := by ring
          _ ≤ |t| * |t| :=
            mul_le_mul_of_nonneg_right ht2 (abs_nonneg t)
          _ = |t| ^ 2 := by ring
          _ ≤ |t| := ht2
      have ht4 : |t| ^ 4 ≤ |t| := by
        calc
          |t| ^ 4 = |t| ^ 3 * |t| := by ring
          _ ≤ |t| * |t| :=
            mul_le_mul_of_nonneg_right ht3 (abs_nonneg t)
          _ = |t| ^ 2 := by ring
          _ ≤ |t| := ht2
      have hfirst := mul_le_mul_of_nonneg_left ht3
        (by positivity : 0 ≤ δ * |T| ^ 3 / 6)
      have hsecond := mul_le_mul_of_nonneg_left ht4
        (by positivity : 0 ≤ δ ^ 2 * |T| ^ 4 / 8)
      calc
        δ * (|T| * |t|) ^ 3 / 6 +
            δ ^ 2 * (|T| ^ 4 * |t| ^ 4) / 8 =
          (δ * |T| ^ 3 / 6) * |t| ^ 3 +
            (δ ^ 2 * |T| ^ 4 / 8) * |t| ^ 4 := by
          ring
        _ ≤ (δ * |T| ^ 3 / 6) * |t| +
            (δ ^ 2 * |T| ^ 4 / 8) * |t| :=
          add_le_add hfirst hsecond
        _ = (δ * |T| ^ 3 / 6 +
            δ ^ 2 * |T| ^ 4 / 8) * |t| := by
          ring

/-- Both orientations of the Prawitz integral for a centered, variance-one
normalized sum are controlled by explicit low- and medium-frequency
one-dimensional majorants. -/
lemma norm_integral_scaledNormalizedSum_gaussian_prawitz_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : δ =
      (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n)
    (a : ℝ) :
    let T : ℝ := 3 / (2 * δ)
    let μs := scaledCenteredMeasure
      (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, X k ω)) a T
    let νs := scaledCenteredMeasure
      (gaussianReal 0 1) a T
    (‖∫ t : ℝ in -1..1,
        vaalerCharDifference μs νs t *
          prawitzKernel t‖ ≤
      (21 / 20 : ℝ) / Real.pi *
        ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
          ∫ u : ℝ in 1 / δ..3 / (2 * δ),
            berryMediumMajorant u)) ∧
    (‖∫ t : ℝ in -1..1,
        vaalerCharDifference μs νs t *
          prawitzKernel (-t)‖ ≤
      (21 / 20 : ℝ) / Real.pi *
        ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
          ∫ u : ℝ in 1 / δ..3 / (2 * δ),
            berryMediumMajorant u)) := by
  let T : ℝ := 3 / (2 * δ)
  let Z : Ω → ℝ := fun ω =>
    (Real.sqrt n)⁻¹ *
      ∑ k ∈ Finset.range n, X k ω
  let μ0 : Measure ℝ := P.map Z
  let μs := scaledCenteredMeasure μ0 a T
  let νs := scaledCenteredMeasure (gaussianReal 0 1) a T
  have hT0 : 0 < T := by
    dsimp [T]
    positivity
  letI : IsProbabilityMeasure μ0 := by
    dsimp [μ0, Z]
    apply Measure.isProbabilityMeasure_map
    apply AEMeasurable.const_mul
    have hsume := Finset.aemeasurable_sum
      (Finset.range n) (fun i hi =>
        (hident i).aemeasurable_fst)
    exact hsume.congr (ae_of_all _ fun x => by
      simp only [Finset.sum_apply])
  have hwindow : δ * T / 2 ≤ 1 := by
    dsimp [T]
    field_simp [hδ0.ne']
    norm_num
  let C : ℝ :=
    δ * |T| ^ 3 / 6 + δ ^ 2 * |T| ^ 4 / 8
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μs νs t‖ ≤ C * |t| := by
    simpa [μs, νs, μ0, Z, C] using
      norm_vaalerCharDifference_scaledNormalizedSum_gaussian_le_small
        hindep hident hX hmean hsecond hn
        hδ0 hδ1 hT0 hδ hwindow a
  have hfP :
      IntervalIntegrable
        (fun t : ℝ =>
          vaalerCharDifference μs νs t *
            prawitzKernel t)
        volume (-1) 1 :=
    intervalIntegrable_charDifference_mul_prawitzKernel
      μs νs hC hsmall
  have hfM :
      IntervalIntegrable
        (fun t : ℝ =>
          vaalerCharDifference μs νs t *
            prawitzKernel (-t))
        volume (-1) 1 :=
    intervalIntegrable_charDifference_mul_prawitzKernel_neg
      μs νs hC hsmall
  have hbound : ∀ (κ : ℝ → ℂ),
      (∀ t : ℝ, ‖κ t‖ = ‖prawitzKernel t‖) →
      IntervalIntegrable
        (fun t : ℝ => vaalerCharDifference μs νs t * κ t)
        volume (-1) 1 →
      ‖∫ t : ℝ in -1..1,
          vaalerCharDifference μs νs t * κ t‖ ≤
        (21 / 20 : ℝ) / Real.pi *
          ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
            ∫ u : ℝ in 1 / δ..3 / (2 * δ),
              berryMediumMajorant u) := by
    intro κ hκ hf
    let f : ℝ → ℂ := fun t =>
      vaalerCharDifference μs νs t * κ t
    have heven : ∀ t : ℝ, ‖f (-t)‖ = ‖f t‖ := by
      intro t
      dsimp [f]
      rw [norm_mul, norm_mul, norm_vaalerCharDifference_neg,
        hκ, hκ, prawitzKernel_neg, Complex.norm_conj]
    have hfnorm : IntervalIntegrable
        (fun t : ℝ => ‖f t‖) volume (-1) 1 :=
      hf.norm
    have hnorm :
        ‖∫ t : ℝ in -1..1, f t‖ ≤
          2 * ∫ t : ℝ in 0..1, ‖f t‖ := by
      calc
        ‖∫ t : ℝ in -1..1, f t‖ ≤
            ∫ t : ℝ in -1..1, ‖f t‖ :=
          intervalIntegral.norm_integral_le_integral_norm
            (by norm_num)
        _ = 2 * ∫ t : ℝ in 0..1, ‖f t‖ :=
          intervalIntegral_even_neg_one_one
            (fun t => ‖f t‖) heven hfnorm
    let r : ℝ := 2 / 3
    let bLow : ℝ → ℝ := fun t =>
      (21 / 20 : ℝ) / (2 * Real.pi) *
        T * berryLowMajorant δ (T * t)
    let bMed : ℝ → ℝ := fun t =>
      (21 / 20 : ℝ) / (2 * Real.pi) *
        T * berryMediumMajorant (T * t)
    have hflow : IntervalIntegrable
        (fun t : ℝ => ‖f t‖) volume 0 r :=
      hfnorm.mono_set (by
        intro x hx
        dsimp [r] at hx
        simp only [
          uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2 / 3),
          uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx ⊢
        constructor <;> linarith [hx.1, hx.2])
    have hfmed : IntervalIntegrable
        (fun t : ℝ => ‖f t‖) volume r 1 :=
      hfnorm.mono_set (by
        intro x hx
        dsimp [r] at hx
        simp only [
          uIcc_of_le (by norm_num : (2 / 3 : ℝ) ≤ 1),
          uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx ⊢
        constructor <;> linarith [hx.1, hx.2])
    have hbLow : IntervalIntegrable bLow volume 0 r := by
      apply Continuous.intervalIntegrable
      dsimp [bLow, berryLowMajorant]
      fun_prop
    have hbMed : IntervalIntegrable bMed volume r 1 := by
      apply ContinuousOn.intervalIntegrable
      dsimp [bMed, berryMediumMajorant]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro t ht
        have htpos : 0 < t := by
          rw [uIcc_of_le (by norm_num :
            (2 / 3 : ℝ) ≤ 1)] at ht
          linarith [ht.1]
        exact mul_ne_zero hT0.ne' htpos.ne'
    have hlowPoint : ∀ t ∈ Icc (0 : ℝ) r,
        ‖f t‖ ≤ bLow t := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        simp [f, bLow, berryLowMajorant, vaalerCharDifference]
      · have htpos : 0 < t := lt_of_le_of_ne ht.1
          (Ne.symm ht0)
        have htlt : t < 1 := by
          dsimp [r] at ht
          linarith [ht.2]
        have hcond :
            (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n *
                |T * t| ≤ 1 := by
          rw [← hδ, abs_mul, abs_of_pos hT0,
            abs_of_pos htpos]
          have hδT : δ * T = 3 / 2 := by
            dsimp [T]
            field_simp [hδ0.ne']
          dsimp [r] at ht
          calc
            δ * (T * t) = (δ * T) * t := by ring
            _ = (3 / 2) * t := by rw [hδT]
            _ ≤ 1 := by nlinarith [ht.2]
        have hchar0 :=
          norm_charFun_normalizedSum_sub_gaussian_le_berryLow
            hindep hident hX hmean hsecond hn
              (T * t) hcond
        have hchar :
            ‖vaalerCharDifference μs νs t‖ ≤
              δ * (T * t) ^ 3 / 6 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 3)) +
                δ ^ 2 * (T * t) ^ 4 / 8 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 2)) := by
          rw [norm_vaalerCharDifference_scaledCentered_gaussian]
          simpa [μ0, Z, μs, νs, hδ,
            abs_of_pos (mul_pos hT0 htpos)] using hchar0
        have hk :=
          norm_prawitzKernel_le_twenty_one_twentieths_div
            htpos htlt
        have hcharNonneg :
            0 ≤ δ * (T * t) ^ 3 / 6 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 3)) +
                δ ^ 2 * (T * t) ^ 4 / 8 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 2)) := by
          positivity
        calc
          ‖f t‖ =
              ‖vaalerCharDifference μs νs t‖ *
                ‖κ t‖ := norm_mul _ _
          _ ≤ (δ * (T * t) ^ 3 / 6 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 3)) +
                δ ^ 2 * (T * t) ^ 4 / 8 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 2))) *
                ‖κ t‖ :=
            mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
          _ = (δ * (T * t) ^ 3 / 6 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 3)) +
                δ ^ 2 * (T * t) ^ 4 / 8 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 2))) *
                ‖prawitzKernel t‖ := by rw [hκ]
          _ ≤ (δ * (T * t) ^ 3 / 6 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 3)) +
                δ ^ 2 * (T * t) ^ 4 / 8 *
                  Real.exp (-((1 - δ ^ 2) *
                    (T * t) ^ 2 / 2))) *
                ((21 / 20 : ℝ) /
                  (2 * Real.pi * t)) :=
            mul_le_mul_of_nonneg_left hk hcharNonneg
          _ = bLow t := by
            dsimp [bLow, berryLowMajorant]
            field_simp [Real.pi_ne_zero, ht0]
    have hmedPoint : ∀ t ∈ Icc r 1,
        ‖f t‖ ≤ bMed t := by
      intro t ht
      have htpos : 0 < t := by
        dsimp [r] at ht
        linarith [ht.1]
      have htlt : t < 1 ∨ t = 1 := lt_or_eq_of_le ht.2
      have hcond :
          (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n *
              |T * t| ≤ 3 / 2 := by
        rw [← hδ, abs_mul, abs_of_pos hT0,
          abs_of_pos htpos]
        have hδT : δ * T = 3 / 2 := by
          dsimp [T]
          field_simp [hδ0.ne']
        calc
          δ * (T * t) = (δ * T) * t := by ring
          _ = (3 / 2) * t := by rw [hδT]
          _ ≤ 3 / 2 := by nlinarith [ht.2]
      have hchar0 :=
        norm_charFun_normalizedSum_sub_gaussian_le_berryMedium
          hindep hident hX hmean hsecond hn (T * t) hcond
      have hchar :
          ‖vaalerCharDifference μs νs t‖ ≤
            Real.exp (-((T * t) ^ 2 / 8)) +
              Real.exp (-((T * t) ^ 2 / 2)) := by
        rw [norm_vaalerCharDifference_scaledCentered_gaussian]
        simpa [μ0, Z, μs, νs] using hchar0
      have hk : ‖prawitzKernel t‖ ≤
          (21 / 20 : ℝ) / (2 * Real.pi * t) := by
        rcases htlt with htlt | rfl
        · exact
            norm_prawitzKernel_le_twenty_one_twentieths_div
              htpos htlt
        · unfold prawitzKernel
          simp [Real.cot_eq_cos_div_sin]
          rw [Complex.norm_def]
          simp [Complex.normSq_apply]
          rw [show Real.pi⁻¹ / 2 * (Real.pi⁻¹ / 2) =
                (Real.pi⁻¹ / 2) ^ 2 by ring,
            Real.sqrt_sq_eq_abs,
            abs_of_pos (by positivity : 0 < Real.pi⁻¹ / 2)]
          have hrewrite :
              Real.pi⁻¹ / 2 = 1 / (2 * Real.pi) := by
            field_simp [Real.pi_ne_zero]
          rw [hrewrite]
          exact div_le_div_of_nonneg_right
            (by norm_num : (1 : ℝ) ≤ 21 / 20)
            (by positivity)
      have hcharNonneg :
          0 ≤ Real.exp (-((T * t) ^ 2 / 8)) +
            Real.exp (-((T * t) ^ 2 / 2)) := by
        positivity
      calc
        ‖f t‖ =
            ‖vaalerCharDifference μs νs t‖ *
              ‖κ t‖ := norm_mul _ _
        _ ≤ (Real.exp (-((T * t) ^ 2 / 8)) +
              Real.exp (-((T * t) ^ 2 / 2))) *
              ‖κ t‖ :=
          mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
        _ = (Real.exp (-((T * t) ^ 2 / 8)) +
              Real.exp (-((T * t) ^ 2 / 2))) *
              ‖prawitzKernel t‖ := by rw [hκ]
        _ ≤ (Real.exp (-((T * t) ^ 2 / 8)) +
              Real.exp (-((T * t) ^ 2 / 2))) *
              ((21 / 20 : ℝ) /
                (2 * Real.pi * t)) :=
          mul_le_mul_of_nonneg_left hk hcharNonneg
        _ = bMed t := by
          dsimp [bMed, berryMediumMajorant]
          field_simp [Real.pi_ne_zero, hT0.ne', htpos.ne']
    have hlowInt :
        (∫ t : ℝ in 0..r, ‖f t‖) ≤
          ∫ t : ℝ in 0..r, bLow t :=
      intervalIntegral.integral_mono_on
        (by norm_num) hflow hbLow hlowPoint
    have hmedInt :
        (∫ t : ℝ in r..1, ‖f t‖) ≤
          ∫ t : ℝ in r..1, bMed t :=
      intervalIntegral.integral_mono_on
        (by norm_num) hfmed hbMed hmedPoint
    have hsplit :
        (∫ t : ℝ in 0..1, ‖f t‖) =
          (∫ t : ℝ in 0..r, ‖f t‖) +
            ∫ t : ℝ in r..1, ‖f t‖ := by
      rw [integral_add_adjacent_intervals hflow hfmed]
    have hscalar :
        2 * ((∫ t : ℝ in 0..r, bLow t) +
          ∫ t : ℝ in r..1, bMed t) =
        (21 / 20 : ℝ) / Real.pi *
          ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
            ∫ u : ℝ in 1 / δ..3 / (2 * δ),
              berryMediumMajorant u) := by
      have hTr : T * r = 1 / δ := by
        dsimp [T, r]
        field_simp [hδ0.ne']
      have hT : T * 1 = 3 / (2 * δ) := by
        simp [T]
      have hchangeLow :
          (∫ t : ℝ in 0..r,
              T * berryLowMajorant δ (T * t)) =
            ∫ u : ℝ in 0..T * r,
              berryLowMajorant δ u := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [smul_eq_mul, mul_zero] using
          (intervalIntegral.smul_integral_comp_mul_left
            (f := berryLowMajorant δ) (a := 0) (b := r) T)
      have hchangeMed :
          (∫ t : ℝ in r..1,
              T * berryMediumMajorant (T * t)) =
            ∫ u : ℝ in T * r..T * 1,
              berryMediumMajorant u := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [smul_eq_mul] using
          (intervalIntegral.smul_integral_comp_mul_left
            (f := berryMediumMajorant) (a := r) (b := 1) T)
      have hbLowEq :
          (∫ t : ℝ in 0..r, bLow t) =
            (21 / 20 : ℝ) / (2 * Real.pi) *
              ∫ u : ℝ in 0..1 / δ,
                berryLowMajorant δ u := by
        dsimp [bLow]
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul, hchangeLow, hTr]
      have hbMedEq :
          (∫ t : ℝ in r..1, bMed t) =
            (21 / 20 : ℝ) / (2 * Real.pi) *
              ∫ u : ℝ in 1 / δ..3 / (2 * δ),
                berryMediumMajorant u := by
        dsimp [bMed]
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul, hchangeMed,
          hTr, hT]
      rw [hbLowEq, hbMedEq]
      ring
    calc
      ‖∫ t : ℝ in -1..1,
          vaalerCharDifference μs νs t * κ t‖ =
          ‖∫ t : ℝ in -1..1, f t‖ := rfl
      _ ≤ 2 * ∫ t : ℝ in 0..1, ‖f t‖ := hnorm
      _ = 2 * ((∫ t : ℝ in 0..r, ‖f t‖) +
          ∫ t : ℝ in r..1, ‖f t‖) := by rw [hsplit]
      _ ≤ 2 * ((∫ t : ℝ in 0..r, bLow t) +
          ∫ t : ℝ in r..1, bMed t) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add hlowInt hmedInt) (by norm_num)
      _ = (21 / 20 : ℝ) / Real.pi *
          ((∫ u : ℝ in 0..1 / δ, berryLowMajorant δ u) +
            ∫ u : ℝ in 1 / δ..3 / (2 * δ),
              berryMediumMajorant u) := hscalar
  dsimp only
  constructor
  · apply hbound (fun t => prawitzKernel t)
    · intro t
      rfl
    · exact hfP
  · apply hbound (fun t => prawitzKernel (-t))
    · intro t
      rw [prawitzKernel_neg, Complex.norm_conj]
    · exact hfM

/-- Analytic Berry--Esseen assembly.  Once the remaining explicit scalar
inequality is supplied, the Prawitz estimate gives the cdf error at every
threshold. -/
lemma abs_cdf_normalizedSum_sub_gaussian_le_of_scalarCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : δ =
      (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n)
    (hcert :
      let T : ℝ := 3 / (2 * δ)
      berryPrawitzIntegralBound δ +
          berryGaussianRegularBound T +
        gaussianInversionConstant / (2 * T ^ 3) ≤ δ)
    (a : ℝ) :
    |cdf
        (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
          ∑ k ∈ Finset.range n, X k ω)) a -
      cdf (gaussianReal 0 1) a| ≤ δ := by
  let T : ℝ := 3 / (2 * δ)
  let Z : Ω → ℝ := fun ω =>
    (Real.sqrt n)⁻¹ *
      ∑ k ∈ Finset.range n, X k ω
  let μ0 : Measure ℝ := P.map Z
  let μs := scaledCenteredMeasure μ0 a T
  let νs := scaledCenteredMeasure (gaussianReal 0 1) a T
  have hT0 : 0 < T := by
    dsimp [T]
    positivity
  letI : IsProbabilityMeasure μ0 := by
    dsimp [μ0, Z]
    apply Measure.isProbabilityMeasure_map
    apply AEMeasurable.const_mul
    have hsume := Finset.aemeasurable_sum
      (Finset.range n) (fun i hi =>
        (hident i).aemeasurable_fst)
    exact hsume.congr (ae_of_all _ fun x => by
      simp only [Finset.sum_apply])
  have hwindow : δ * T / 2 ≤ 1 := by
    dsimp [T]
    field_simp [hδ0.ne']
    norm_num
  let C : ℝ :=
    δ * |T| ^ 3 / 6 + δ ^ 2 * |T| ^ 4 / 8
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μs νs t‖ ≤ C * |t| := by
    simpa [μs, νs, μ0, Z, C] using
      norm_vaalerCharDifference_scaledNormalizedSum_gaussian_le_small
        hindep hident hX hmean hsecond hn
        hδ0 hδ1 hT0 hδ hwindow a
  let Cν : ℝ := 2 * (|a| * T + T ^ 2 / 4)
  have hCν : 0 ≤ Cν := by
    dsimp [Cν]
    positivity
  have hνsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference νs (Measure.dirac 0) t‖ ≤
        Cν * |t| := by
    intro t ht
    simpa [νs, Cν] using
      norm_vaalerCharDifference_scaledCenteredGaussian_dirac_le
        hT0 a t ht
  have hraw :
      IntervalIntegrable (prawitzRawKernel νs)
        volume (-1) 1 := by
    simpa [νs] using
      intervalIntegrable_prawitzRawKernel_scaledCenteredGaussian
        hT0 a
  let E : ℝ := gaussianInversionConstant / T ^ 3
  have hE : 0 ≤ E := by
    dsimp [E]
    exact div_nonneg gaussianInversionConstant_nonneg
      (pow_nonneg hT0.le 3)
  have hinversion :
      |(2 * cdf νs 0 - 1) -
        ∫ t : ℝ in -1..1, prawitzRawKernel νs t| ≤ E := by
    simpa [νs, E] using
      scaledCenteredGaussian_inversion hT0 a
  have hpraw :=
    norm_integral_scaledNormalizedSum_gaussian_prawitz_le
      hindep hident hX hmean hsecond hn hδ0 hδ1 hδ a
  change
    (‖∫ t : ℝ in -1..1,
        vaalerCharDifference μs νs t *
          prawitzKernel t‖ ≤ berryPrawitzIntegralBound δ) ∧
    (‖∫ t : ℝ in -1..1,
        vaalerCharDifference μs νs t *
          prawitzKernel (-t)‖ ≤
      berryPrawitzIntegralBound δ) at hpraw
  have hregp :
      ‖∫ t : ℝ in -1..1,
          charFun νs (2 * Real.pi * t) *
            (prawitzKernel t -
              prawitzSingularKernel t)‖ ≤
        berryGaussianRegularBound T := by
    simpa [νs, berryGaussianRegularBound] using
      norm_integral_scaledCenteredGaussian_prawitzRegular_le
        hT0 a
  have hregm :
      ‖∫ t : ℝ in -1..1,
          charFun νs (2 * Real.pi * t) *
            (prawitzKernel (-t) -
              prawitzSingularKernel (-t))‖ ≤
        berryGaussianRegularBound T := by
    simpa [νs, berryGaussianRegularBound] using
      norm_integral_scaledCenteredGaussian_prawitzRegular_neg_le
        hT0 a
  have hcdf :=
    abs_cdf_sub_le_of_prawitz μs νs
      hC hsmall hCν hνsmall hraw hE hinversion
      hpraw.1 hpraw.2 hregp hregm
  rw [cdf_scaledCenteredMeasure_zero μ0 hT0,
    cdf_scaledCenteredMeasure_zero (gaussianReal 0 1) hT0] at hcdf
  change
    |cdf μ0 a - cdf (gaussianReal 0 1) a| ≤
      berryPrawitzIntegralBound δ +
        berryGaussianRegularBound T + E / 2 at hcdf
  dsimp [E] at hcdf
  have hcert' :
      berryPrawitzIntegralBound δ +
          berryGaussianRegularBound T +
        gaussianInversionConstant / (2 * T ^ 3) ≤ δ := by
    simpa only [T] using hcert
  apply hcdf.trans
  calc
    berryPrawitzIntegralBound δ +
          berryGaussianRegularBound T +
        (gaussianInversionConstant / T ^ 3) / 2 =
      berryPrawitzIntegralBound δ +
          berryGaussianRegularBound T +
        gaussianInversionConstant / (2 * T ^ 3) := by ring
    _ ≤ δ := hcert'

end HDP.Appendix
