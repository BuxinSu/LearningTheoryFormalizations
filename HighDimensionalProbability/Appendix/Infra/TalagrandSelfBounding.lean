import HighDimensionalProbability.Appendix.Infra.TalagrandEntropy

/-!
# The self-bounding Herbst argument

The entropy inequality

`Ent (exp (t X)) ≤ t² E[X exp (t X)]`

implies both the standard positive sub-gamma cumulant bound and a useful
negative-tilt estimate.  The latter is what turns a half-mass zero set into a
dimension-free bound on `E X`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace HDP.Appendix

noncomputable section

/-- Analytic consequences of the self-bounding entropy estimate. -/
theorem cgf_bounds_of_hasSelfBoundingEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hH : HasSelfBoundingEntropyBound μ X) :
    (∀ t : ℝ, 0 < t → t < 1 →
      cgf X μ t ≤ t * (∫ ω, X ω ∂μ) / (1 - t)) ∧
    cgf X μ (-1) ≤ -(∫ ω, X ω ∂μ) / 2 := by
  have hset : integrableExpSet X μ = Set.univ := by
    ext u
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hH.1 u
  have hmem (u : ℝ) : u ∈ interior (integrableExpSet X μ) := by
    rw [hset, interior_univ]
    exact Set.mem_univ u
  have hXint : Integrable X μ :=
    integrable_of_mem_interior_integrableExpSet (hmem 0)
  have hc0 : HasDerivAt (cgf X μ) (∫ ω, X ω ∂μ) 0 := by
    have h := (hasDerivAt_mgf (hmem 0)).log
      (by simpa using (mgf_pos (hH.1 0)).ne')
    convert h using 1
    · rfl
    · simp
  have hRderiv (u : ℝ) (hu : u ≠ 0) :
      HasDerivAt
        ((cgf X μ / id) - cgf X μ)
        (((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
              mgf X μ u) * id u - cgf X μ u * 1) / (id u) ^ 2) -
            ((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
              mgf X μ u)) u := by
    have hc : HasDerivAt (cgf X μ)
        ((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
          mgf X μ u) u := by
      exact
        (analyticAt_cgf (hmem u)).differentiableAt.hasDerivAt.congr_deriv
          (deriv_cgf (hmem u))
    exact (hc.div (hasDerivAt_id u) hu).sub hc
  have hRderiv_nonpos (u : ℝ) (hu : u ≠ 0) (hu2 : |u| ≤ 2) :
      ((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
            mgf X μ u) * u - cgf X μ u) / u ^ 2) -
          ((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
            mgf X μ u) ≤ 0 := by
    have hMpos : 0 < mgf X μ u := mgf_pos (hH.1 u)
    have hent := hH.2 u hu2
    have husq : 0 < u ^ 2 := sq_pos_of_ne_zero hu
    rw [cgf]
    apply sub_nonpos.mpr
    rw [div_le_iff₀ husq]
    apply (mul_le_mul_iff_of_pos_right hMpos).mp
    calc
      (((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
            mgf X μ u) * u - Real.log (mgf X μ u))) *
          mgf X μ u) =
          u * ∫ ω, X ω * Real.exp (u * X ω) ∂μ -
            mgf X μ u * Real.log (mgf X μ u) := by
              field_simp [hMpos.ne']
              ring
      _ ≤ u ^ 2 * ∫ ω, X ω * Real.exp (u * X ω) ∂μ := hent
      _ = ((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
            mgf X μ u) * u ^ 2) * mgf X μ u) := by
              field_simp [hMpos.ne']
  have hRanti_pos :
      AntitoneOn ((cgf X μ / id) - cgf X μ) (Set.Ioo 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
    · intro u hu
      exact (hRderiv u hu.1.ne').continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ioo] at hu
      exact (hRderiv u hu.1.ne').differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioo] at hu
      rw [(hRderiv u hu.1.ne').deriv]
      have habs : |u| ≤ 2 := by
        rw [abs_of_pos hu.1]
        linarith [hu.2]
      simpa only [id_eq, mul_one] using
        hRderiv_nonpos u hu.1.ne' habs
  have hRanti_neg :
      AntitoneOn ((cgf X μ / id) - cgf X μ) (Set.Ioo (-2) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo (-2) 0)
    · intro u hu
      exact (hRderiv u hu.2.ne).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ioo] at hu
      exact (hRderiv u hu.2.ne).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioo] at hu
      rw [(hRderiv u hu.2.ne).deriv]
      have habs : |u| ≤ 2 := by
        rw [abs_of_neg hu.2]
        linarith [hu.1]
      simpa only [id_eq, mul_one] using
        hRderiv_nonpos u hu.2.ne habs
  have hQlim_pos :
      Tendsto (fun u : ℝ => cgf X μ u / u)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (∫ ω, X ω ∂μ)) := by
    have hs := hc0.tendsto_slope_zero_right
    convert hs using 1
    · funext u
      simp [cgf_zero, div_eq_inv_mul]
  have hQlim_neg :
      Tendsto (fun u : ℝ => cgf X μ u / u)
        (nhdsWithin 0 (Set.Iio 0)) (𝓝 (∫ ω, X ω ∂μ)) := by
    have hs := hc0.tendsto_slope_zero_left
    convert hs using 1
    · funext u
      simp [cgf_zero, div_eq_inv_mul]
  have hClim_pos :
      Tendsto (cgf X μ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hc := hc0.continuousAt.tendsto
    rw [cgf_zero] at hc
    exact hc.mono_left inf_le_left
  have hClim_neg :
      Tendsto (cgf X μ) (nhdsWithin 0 (Set.Iio 0)) (𝓝 0) := by
    have hc := hc0.continuousAt.tendsto
    rw [cgf_zero] at hc
    exact hc.mono_left inf_le_left
  have hRlim_pos :
      Tendsto (fun u : ℝ => cgf X μ u / u - cgf X μ u)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (∫ ω, X ω ∂μ)) := by
    simpa only [sub_zero] using hQlim_pos.sub hClim_pos
  have hRlim_neg :
      Tendsto (fun u : ℝ => cgf X μ u / u - cgf X μ u)
        (nhdsWithin 0 (Set.Iio 0)) (𝓝 (∫ ω, X ω ∂μ)) := by
    simpa only [sub_zero] using hQlim_neg.sub hClim_neg
  constructor
  · intro t ht0 ht1
    have hev : ∀ᶠ u in nhdsWithin 0 (Set.Ioi 0),
        cgf X μ t / t - cgf X μ t ≤
          cgf X μ u / u - cgf X μ u := by
      filter_upwards [
        (eventually_lt_nhds ht0).filter_mono inf_le_left,
        self_mem_nhdsWithin] with u hut hu
      exact hRanti_pos ⟨hu, hut.trans ht1⟩ ⟨ht0, ht1⟩ hut.le
    have hRle :
        cgf X μ t / t - cgf X μ t ≤ ∫ ω, X ω ∂μ :=
      ge_of_tendsto hRlim_pos hev
    have hdiv :
        cgf X μ t / t ≤ (∫ ω, X ω ∂μ) + cgf X μ t := by
      linarith
    have hmul := (div_le_iff₀ ht0).mp hdiv
    have hone : 0 < 1 - t := by linarith
    apply (le_div_iff₀ hone).2
    nlinarith
  · have hev : ∀ᶠ u in nhdsWithin 0 (Set.Iio 0),
        cgf X μ u / u - cgf X μ u ≤
          cgf X μ (-1) / (-1) - cgf X μ (-1) := by
      filter_upwards [
        (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono
          inf_le_left,
        self_mem_nhdsWithin] with u huLower hu
      exact hRanti_neg (by norm_num) ⟨by linarith, hu⟩ huLower.le
    have hmean :
        (∫ ω, X ω ∂μ) ≤
          cgf X μ (-1) / (-1) - cgf X μ (-1) :=
      le_of_tendsto hRlim_neg hev
    norm_num at hmean ⊢
    linarith

lemma integrable_exp_centered_of_hasSelfBoundingEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Ω → ℝ)
    (hH : HasSelfBoundingEntropyBound μ X) (t : ℝ) :
    Integrable
      (fun ω => Real.exp (t * (X ω - ∫ η, X η ∂μ))) μ := by
  let m : ℝ := ∫ η, X η ∂μ
  have heq :
      (fun ω => Real.exp (t * (X ω - m))) =
        (fun ω => Real.exp (-t * m) * Real.exp (t * X ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact (hH.1 t).const_mul _

/-- Centered sub-gamma MGF estimate for a self-bounding variable. -/
theorem mgf_centered_le_of_hasSelfBoundingEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hH : HasSelfBoundingEntropyBound μ X)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mgf (fun ω => X ω - ∫ η, X η ∂μ) μ t ≤
      Real.exp (t ^ 2 * (∫ ω, X ω ∂μ) / (1 - t)) := by
  let m : ℝ := ∫ η, X η ∂μ
  have hcgf :=
    (cgf_bounds_of_hasSelfBoundingEntropyBound μ X hH).1 t ht0 ht1
  have hMpos : 0 < mgf X μ t := mgf_pos (hH.1 t)
  have hM :
      mgf X μ t ≤ Real.exp (t * m / (1 - t)) := by
    rw [← Real.exp_log hMpos]
    exact Real.exp_le_exp.mpr hcgf
  have heq :
      (fun ω => Real.exp (t * (X ω - m))) =
        (fun ω => Real.exp (-t * m) * Real.exp (t * X ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mgf, heq, integral_const_mul]
  calc
    Real.exp (-t * m) * mgf X μ t ≤
        Real.exp (-t * m) * Real.exp (t * m / (1 - t)) :=
      mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = Real.exp (t ^ 2 * m / (1 - t)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [ne_of_gt (sub_pos.mpr ht1)]
      ring

/-- Chernoff tail for a nonnegative-mean self-bounding variable. -/
theorem measure_ge_mean_add_le_of_hasSelfBoundingEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hH : HasSelfBoundingEntropyBound μ X)
    (hmean0 : 0 ≤ ∫ ω, X ω ∂μ)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | (∫ η, X η ∂μ) + s ≤ X ω} ≤
      Real.exp (-(s ^ 2) / (4 * (∫ ω, X ω ∂μ) + 2 * s)) := by
  let m : ℝ := ∫ ω, X ω ∂μ
  let Y : Ω → ℝ := fun ω => X ω - m
  have hset : {ω | m + s ≤ X ω} = {ω | s ≤ Y ω} := by
    ext ω
    change (m + s ≤ X ω) ↔ (s ≤ X ω - m)
    constructor <;> intro h <;> linarith
  change μ.real {ω | m + s ≤ X ω} ≤
    Real.exp (-(s ^ 2) / (4 * m + 2 * s))
  rw [hset]
  rcases hs.eq_or_lt with rfl | hspos
  · simp
  · by_cases hm : m = 0
    · have hlam0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
      have hlampos : (0 : ℝ) < 1 / 2 := by norm_num
      have hlamone : (1 / 2 : ℝ) < 1 := by norm_num
      have hchernoff :=
        measure_ge_le_exp_mul_mgf (μ := μ) (X := Y) s hlam0
          (integrable_exp_centered_of_hasSelfBoundingEntropyBound X hH (1 / 2))
      have hmgf :=
        mgf_centered_le_of_hasSelfBoundingEntropyBound μ X hH hlampos hlamone
      calc
        μ.real {ω | s ≤ Y ω} ≤
            Real.exp (-(1 / 2 : ℝ) * s) * mgf Y μ (1 / 2) :=
          hchernoff
        _ ≤ Real.exp (-(1 / 2 : ℝ) * s) *
            Real.exp ((1 / 2 : ℝ) ^ 2 * m / (1 - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
        _ = Real.exp (-(s ^ 2) / (4 * m + 2 * s)) := by
          rw [hm, ← Real.exp_add]
          congr 1
          field_simp [hspos.ne']
          ring
    · have hmpos : 0 < m := lt_of_le_of_ne hmean0 (Ne.symm hm)
      let lam : ℝ := s / (2 * m + s)
      have hden : 0 < 2 * m + s := by positivity
      have hlampos : 0 < lam := div_pos hspos hden
      have hlamone : lam < 1 := by
        rw [div_lt_one hden]
        linarith
      have hchernoff :=
        measure_ge_le_exp_mul_mgf (μ := μ) (X := Y) s hlampos.le
          (integrable_exp_centered_of_hasSelfBoundingEntropyBound X hH lam)
      have hmgf :=
        mgf_centered_le_of_hasSelfBoundingEntropyBound μ X hH hlampos hlamone
      calc
        μ.real {ω | s ≤ Y ω} ≤
            Real.exp (-lam * s) * mgf Y μ lam :=
          hchernoff
        _ ≤ Real.exp (-lam * s) *
            Real.exp (lam ^ 2 * m / (1 - lam)) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
        _ = Real.exp (-(s ^ 2) / (4 * m + 2 * s)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [lam]
          field_simp [hden.ne', hspos.ne', hmpos.ne']
          ring

/-- If a self-bounding variable vanishes on a measurable set of mass at
least one half, its mean is at most `2`.  This deliberately uses the simple
bound `log 2 ≤ 1`, avoiding an unnecessary transcendental constant. -/
theorem mean_le_two_of_hasSelfBoundingEntropyBound_zero_on_half
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hH : HasSelfBoundingEntropyBound μ X)
    {A : Set Ω} (hA : MeasurableSet A)
    (hhalf : (1 / 2 : ℝ) ≤ μ.real A)
    (hzero : ∀ ω ∈ A, X ω = 0) :
    (∫ ω, X ω ∂μ) ≤ 2 := by
  have hindInt :
      Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have hpoint (ω : Ω) :
      A.indicator (fun _ : Ω => (1 : ℝ)) ω ≤
        Real.exp ((-1 : ℝ) * X ω) := by
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω, hzero ω hω]
    · simp [Set.indicator_of_notMem hω, (Real.exp_pos _).le]
  have hhalfMgf :
      (1 / 2 : ℝ) ≤ mgf X μ (-1) := by
    calc
      (1 / 2 : ℝ) ≤ μ.real A := hhalf
      _ = ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ := by
        exact (integral_indicator_one hA).symm
      _ ≤ ∫ ω, Real.exp ((-1 : ℝ) * X ω) ∂μ :=
        integral_mono hindInt (hH.1 (-1)) hpoint
      _ = mgf X μ (-1) := rfl
  have hloghalf :
      Real.log (1 / 2 : ℝ) ≤ Real.log (mgf X μ (-1)) :=
    Real.log_le_log (by norm_num) hhalfMgf
  have hcgf :=
    (cgf_bounds_of_hasSelfBoundingEntropyBound μ X hH).2
  rw [cgf] at hcgf
  have hloglower :
      (-1 : ℝ) ≤ Real.log (1 / 2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 1 / 2 by norm_num)
    norm_num at h ⊢
    exact h
  linarith

/-- Dimension-free upper tail for the normalized squared distance from a
half-mass compact convex subset of the cube. -/
theorem talagrandClampedEnergy_half_mass_tail {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    (hKhalf : (1 / 2 : ℝ) ≤ (Measure.pi μ).real K)
    (r : ℝ) :
    (Measure.pi μ).real
        {x | r ^ 2 / 16 ≤ talagrandClampedEnergy K x} ≤
      2 * Real.exp (-(r ^ 2) / 192) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi μ
  let E : (Fin n → ℝ) → ℝ := talagrandClampedEnergy K
  let m : ℝ := ∫ x, E x ∂ν
  have hH : HasSelfBoundingEntropyBound ν E :=
    hasSelfBoundingEntropyBound_talagrandClampedEnergy
      μ hK hKne hKconv hKcube
  have hE0 (x : Fin n → ℝ) : 0 ≤ E x :=
    (talagrandClampedEnergy_bounds hK hKne hKcube x).1
  have hm0 : 0 ≤ m := integral_nonneg hE0
  have hzero (x : Fin n → ℝ) (hx : x ∈ K) : E x = 0 := by
    have hxcube := hKcube hx
    change talagrandClampedEnergy K x = 0
    rw [talagrandClampedEnergy_eq hxcube]
    dsimp [talagrandDistanceEnergy]
    rw [finEuclideanSetDistSq_eq_zero_of_mem hK hKne hx]
    norm_num
  have hm2 : m ≤ 2 :=
    mean_le_two_of_hasSelfBoundingEntropyBound_zero_on_half
      ν E hH hK.measurableSet hKhalf hzero
  by_cases hsmall : r ^ 2 / 16 ≤ 4
  · have hq : r ^ 2 / 192 ≤ 1 / 3 := by
      nlinarith [hsmall]
    have hexp := Real.add_one_le_exp (-(r ^ 2) / 192)
    have hhalfexp : (1 / 2 : ℝ) ≤ Real.exp (-(r ^ 2) / 192) := by
      nlinarith
    calc
      ν.real {x | r ^ 2 / 16 ≤ E x} ≤ 1 := measureReal_le_one
      _ ≤ 2 * Real.exp (-(r ^ 2) / 192) := by nlinarith
  · have ha : 4 < r ^ 2 / 16 := lt_of_not_ge hsmall
    let s : ℝ := r ^ 2 / 16 - m
    have hs : 0 < s := by
      dsimp [s]
      linarith
    have htail :=
      measure_ge_mean_add_le_of_hasSelfBoundingEntropyBound
        ν E hH hm0 hs.le
    have hset :
        {x | m + s ≤ E x} = {x | r ^ 2 / 16 ≤ E x} := by
      ext x
      change (m + (r ^ 2 / 16 - m) ≤ E x) ↔
        (r ^ 2 / 16 ≤ E x)
      ring_nf
    rw [hset] at htail
    have hden : 0 < 4 * m + 2 * s := by positivity
    have hfactor1 : 0 ≤ 5 * (r ^ 2 / 16) - 3 * m := by
      nlinarith
    have hfactor2 : 0 ≤ r ^ 2 / 16 - 2 * m := by
      nlinarith
    have hpoly :
        0 ≤ (5 * (r ^ 2 / 16) - 3 * m) *
          (r ^ 2 / 16 - 2 * m) :=
      mul_nonneg hfactor1 hfactor2
    have hratio :
        r ^ 2 / 192 ≤ s ^ 2 / (4 * m + 2 * s) := by
      rw [le_div_iff₀ hden]
      dsimp [s]
      nlinarith
    calc
      ν.real {x | r ^ 2 / 16 ≤ E x} ≤
          Real.exp (-(s ^ 2) / (4 * m + 2 * s)) := htail
      _ ≤ Real.exp (-(r ^ 2) / 192) :=
        Real.exp_le_exp.mpr (by
          simpa only [neg_div] using neg_le_neg hratio)
      _ ≤ 2 * Real.exp (-(r ^ 2) / 192) := by
        nlinarith [Real.exp_pos (-(r ^ 2) / 192)]

/-- Talagrand's convex-distance product inequality in the normalized energy
form.  No lower bound on the mass of `K` is required. -/
theorem talagrandClampedEnergy_product_bound {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    (a : ℝ) :
    ((Measure.pi μ).real K) ^ 2 *
        (Measure.pi μ).real
          {x | a ≤ talagrandClampedEnergy K x} ≤
      Real.exp (-a / 2) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi μ
  let E : (Fin n → ℝ) → ℝ := talagrandClampedEnergy K
  let m : ℝ := ∫ x, E x ∂ν
  let p : ℝ := ν.real K
  let q : ℝ := ν.real {x | a ≤ E x}
  have hH : HasSelfBoundingEntropyBound ν E :=
    hasSelfBoundingEntropyBound_talagrandClampedEnergy
      μ hK hKne hKconv hKcube
  have hzero (x : Fin n → ℝ) (hx : x ∈ K) : E x = 0 := by
    have hxcube := hKcube hx
    change talagrandClampedEnergy K x = 0
    rw [talagrandClampedEnergy_eq hxcube]
    dsimp [talagrandDistanceEnergy]
    rw [finEuclideanSetDistSq_eq_zero_of_mem hK hKne hx]
    norm_num
  have hindInt :
      Integrable (K.indicator (fun _ : Fin n → ℝ => (1 : ℝ))) ν :=
    (integrable_const 1).indicator hK.measurableSet
  have hpMgf : p ≤ mgf E ν (-1) := by
    have hpoint (x : Fin n → ℝ) :
        K.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) x ≤
          Real.exp ((-1 : ℝ) * E x) := by
      by_cases hx : x ∈ K
      · simp [Set.indicator_of_mem hx, hzero x hx]
      · simp [Set.indicator_of_notMem hx, (Real.exp_pos _).le]
    calc
      p = ∫ x, K.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) x ∂ν := by
        exact (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, Real.exp ((-1 : ℝ) * E x) ∂ν :=
        integral_mono hindInt (hH.1 (-1)) hpoint
      _ = mgf E ν (-1) := rfl
  have hMgfNeg :
      mgf E ν (-1) ≤ Real.exp (-m / 2) := by
    have hpos : 0 < mgf E ν (-1) := mgf_pos (hH.1 (-1))
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr
      (cgf_bounds_of_hasSelfBoundingEntropyBound ν E hH).2
  have hpExp : p ≤ Real.exp (-m / 2) := hpMgf.trans hMgfNeg
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hpSq :
      p ^ 2 ≤ Real.exp (-m) := by
    calc
      p ^ 2 ≤ (Real.exp (-m / 2)) ^ 2 :=
        (sq_le_sq₀ hp0 (Real.exp_pos _).le).2 hpExp
      _ = Real.exp (-m) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hpSqExp : p ^ 2 * Real.exp m ≤ 1 := by
    calc
      p ^ 2 * Real.exp m ≤ Real.exp (-m) * Real.exp m :=
        mul_le_mul_of_nonneg_right hpSq (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hMgfPos :
      mgf E ν (1 / 2) ≤ Real.exp m := by
    have hpos : 0 < mgf E ν (1 / 2) := mgf_pos (hH.1 (1 / 2))
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    have hc :=
      (cgf_bounds_of_hasSelfBoundingEntropyBound ν E hH).1
        (1 / 2) (by norm_num) (by norm_num)
    norm_num at hc ⊢
    exact hc
  have hq :
      q ≤ Real.exp (-(1 / 2 : ℝ) * a) * Real.exp m := by
    calc
      q ≤ Real.exp (-(1 / 2 : ℝ) * a) * mgf E ν (1 / 2) :=
        measure_ge_le_exp_mul_mgf a (by norm_num) (hH.1 (1 / 2))
      _ ≤ Real.exp (-(1 / 2 : ℝ) * a) * Real.exp m :=
        mul_le_mul_of_nonneg_left hMgfPos (Real.exp_pos _).le
  have hq0 : 0 ≤ q := measureReal_nonneg
  change p ^ 2 * q ≤ Real.exp (-a / 2)
  calc
    p ^ 2 * q ≤ p ^ 2 *
        (Real.exp (-(1 / 2 : ℝ) * a) * Real.exp m) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg p)
    _ = Real.exp (-a / 2) * (p ^ 2 * Real.exp m) := by ring
    _ ≤ Real.exp (-a / 2) * 1 :=
      mul_le_mul_of_nonneg_left hpSqExp (Real.exp_pos _).le
    _ = Real.exp (-a / 2) := by ring

end

end HDP.Appendix
