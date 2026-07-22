import HighDimensionalProbability.Appendix.Infra.Concentration
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The logarithmic-Sobolev-to-concentration bridge

This file isolates the analytic Herbst argument.  It proves, without any
geometric assumptions hidden in the conclusion, that a logarithmic Sobolev
inequality plus the exponential gradient-chain-rule estimate gives centered
sub-Gaussian concentration.

For a Riemannian manifold the remaining geometric inputs are precisely:

* a logarithmic Sobolev inequality for the Dirichlet energy `‖∇g‖²`;
* closure of the analytic domain under the exponential tilts used below; and
* the ordinary chain-rule estimate for Lipschitz observables.

The first item is the genuine Bochner/Bakry--Émery theorem that must be proved
separately from a Ricci lower bound.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace HDP.Appendix

/-- The entropy estimate for all exponential tilts that drives Herbst's
argument. -/
def HasHerbstEntropyBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (ρ : ℝ) : Prop :=
  (∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) ∧
  ∀ t : ℝ, t ≠ 0 →
    t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ -
        mgf X μ t * Real.log (mgf X μ t) ≤
      (ρ * t ^ 2 / 2) * mgf X μ t

/-- Entropy of a nonnegative density-like function relative to `μ`. -/
noncomputable def boltzmannEntropy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : ℝ :=
  (∫ ω, g ω * Real.log (g ω) ∂μ) -
    (∫ ω, g ω ∂μ) * Real.log (∫ ω, g ω ∂μ)

/-- An abstract logarithmic Sobolev inequality for a Dirichlet energy.

The predicate `admissible` records the analytic domain of the energy, so the
definition applies equally to smooth functions on a compact manifold and to a
closed Dirichlet form. -/
def HasLogSobolevInequality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (admissible : (Ω → ℝ) → Prop)
    (energy : (Ω → ℝ) → Ω → ℝ) (ρ : ℝ) : Prop :=
  ∀ g : Ω → ℝ, admissible g →
    boltzmannEntropy μ (fun ω => g ω ^ 2) ≤
      2 * ρ * ∫ ω, energy g ω ∂μ

/-- The integrated gradient-chain-rule estimate for exponential tilts of `X`.

For the carré-du-champ energy `energy g = ‖∇g‖²`, this follows from
`‖∇X‖ ≤ L` and the ordinary chain rule. -/
def HasExponentialEnergyBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (energy : (Ω → ℝ) → Ω → ℝ)
    (X : Ω → ℝ) (L : ℝ) : Prop :=
  ∀ t : ℝ,
    (∫ ω, energy (fun η => Real.exp (t * X η / 2)) ω ∂μ) ≤
      (t ^ 2 * L ^ 2 / 4) * mgf X μ t

private lemma boltzmannEntropy_sq_exp_half
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    boltzmannEntropy μ
        (fun ω => Real.exp (t * X ω / 2) ^ 2) =
      t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ -
        mgf X μ t * Real.log (mgf X μ t) := by
  have hsquare (ω : Ω) :
      Real.exp (t * X ω / 2) ^ 2 = Real.exp (t * X ω) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [boltzmannEntropy, mgf]
  simp_rw [hsquare]
  congr 1
  calc
    (∫ ω, Real.exp (t * X ω) *
          Real.log (Real.exp (t * X ω)) ∂μ) =
        ∫ ω, t * (X ω * Real.exp (t * X ω)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Real.log_exp]
          ring
    _ = t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ :=
      integral_const_mul _ _

/-- A logarithmic Sobolev inequality and the exponential energy chain rule
imply the entropy estimate used in Herbst's argument. -/
theorem hasHerbstEntropyBound_of_logSobolev
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (admissible : (Ω → ℝ) → Prop)
    (energy : (Ω → ℝ) → Ω → ℝ)
    (X : Ω → ℝ) {ρ L : ℝ} (hρ : 0 ≤ ρ)
    (hLSI : HasLogSobolevInequality μ admissible energy ρ)
    (hExp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hAdmissible :
      ∀ t : ℝ, admissible (fun ω => Real.exp (t * X ω / 2)))
    (hEnergy : HasExponentialEnergyBound μ energy X L) :
    HasHerbstEntropyBound μ X (ρ * L ^ 2) := by
  refine ⟨hExp, ?_⟩
  intro t _
  have hlsi := hLSI (fun ω => Real.exp (t * X ω / 2))
    (hAdmissible t)
  rw [boltzmannEntropy_sq_exp_half] at hlsi
  calc
    t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ -
          mgf X μ t * Real.log (mgf X μ t) ≤
        2 * ρ *
          ∫ ω, energy (fun η => Real.exp (t * X η / 2)) ω ∂μ :=
      hlsi
    _ ≤ 2 * ρ * ((t ^ 2 * L ^ 2 / 4) * mgf X μ t) :=
      mul_le_mul_of_nonneg_left (hEnergy t) (mul_nonneg (by norm_num) hρ)
    _ = (ρ * L ^ 2 * t ^ 2 / 2) * mgf X μ t := by ring

/-- Herbst's differential argument: the cumulant generating function is
bounded by its tangent at zero plus the quadratic entropy parameter. -/
theorem cgf_le_of_hasHerbstEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {ρ : ℝ}
    (hH : HasHerbstEntropyBound μ X ρ) (t : ℝ) :
    cgf X μ t ≤ t * ∫ ω, X ω ∂μ + ρ * t ^ 2 / 2 := by
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
        ((cgf X μ / id) - (fun v : ℝ => ρ * id v / 2))
        (((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
              mgf X μ u) * id u - cgf X μ u * 1) / (id u) ^ 2) -
            (ρ * 1 / 2)) u := by
    have hc : HasDerivAt (cgf X μ)
        ((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
          mgf X μ u) u := by
      exact
        (analyticAt_cgf (hmem u)).differentiableAt.hasDerivAt.congr_deriv
          (deriv_cgf (hmem u))
    exact
      (hc.div (hasDerivAt_id u) hu).sub
        (((hasDerivAt_id u).const_mul ρ).div_const 2)
  have hRderiv_nonpos (u : ℝ) (hu : u ≠ 0) :
      ((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
            mgf X μ u) * u - cgf X μ u) / u ^ 2) - ρ / 2 ≤ 0 := by
    have hMpos : 0 < mgf X μ u := mgf_pos (hH.1 u)
    have hent := hH.2 u hu
    rw [cgf]
    have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
    apply sub_nonpos.mpr
    rw [div_le_iff₀ hu2]
    apply (mul_le_mul_iff_of_pos_right hMpos).mp
    calc
      ((((∫ ω, X ω * Real.exp (u * X ω) ∂μ) /
          mgf X μ u) * u - Real.log (mgf X μ u)) *
          mgf X μ u) =
          u * ∫ ω, X ω * Real.exp (u * X ω) ∂μ -
            mgf X μ u * Real.log (mgf X μ u) := by
              field_simp [hMpos.ne']
              ring
      _ ≤ (ρ * u ^ 2 / 2) * mgf X μ u := hent
      _ = (ρ / 2 * u ^ 2) * mgf X μ u := by ring
  have hRanti_pos :
      AntitoneOn ((cgf X μ / id) - (fun u : ℝ => ρ * id u / 2))
        (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro u hu
      exact (hRderiv u hu.ne').continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      exact (hRderiv u hu.ne').differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      rw [(hRderiv u hu.ne').deriv]
      simpa only [id_eq, mul_one] using hRderiv_nonpos u hu.ne'
  have hRanti_neg :
      AntitoneOn ((cgf X μ / id) - (fun u : ℝ => ρ * id u / 2))
        (Set.Iio 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iio 0)
    · intro u hu
      exact (hRderiv u hu.ne).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Iio] at hu
      exact (hRderiv u hu.ne).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Iio] at hu
      rw [(hRderiv u hu.ne).deriv]
      simpa only [id_eq, mul_one] using hRderiv_nonpos u hu.ne
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
  have hRlim_pos :
      Tendsto (fun u : ℝ => cgf X μ u / u - ρ * u / 2)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (∫ ω, X ω ∂μ)) := by
    have hrho : Tendsto (fun u : ℝ => ρ * u / 2)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      have hu0 : Tendsto (fun u : ℝ => u)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      simpa using (tendsto_const_nhds.mul hu0).div_const 2
    simpa only [sub_zero] using hQlim_pos.sub hrho
  have hRlim_neg :
      Tendsto (fun u : ℝ => cgf X μ u / u - ρ * u / 2)
        (nhdsWithin 0 (Set.Iio 0)) (𝓝 (∫ ω, X ω ∂μ)) := by
    have hrho : Tendsto (fun u : ℝ => ρ * u / 2)
        (nhdsWithin 0 (Set.Iio 0)) (𝓝 0) := by
      have hu0 : Tendsto (fun u : ℝ => u)
          (nhdsWithin 0 (Set.Iio 0)) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      simpa using (tendsto_const_nhds.mul hu0).div_const 2
    simpa only [sub_zero] using hQlim_neg.sub hrho
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hev : ∀ᶠ u in nhdsWithin 0 (Set.Iio 0),
        cgf X μ u / u - ρ * u / 2 ≤
          cgf X μ t / t - ρ * t / 2 := by
      filter_upwards [
        (eventually_gt_nhds ht).filter_mono inf_le_left,
        self_mem_nhdsWithin] with u htu hu
      exact hRanti_neg ht hu htu.le
    have hmle :
        (∫ ω, X ω ∂μ) ≤ cgf X μ t / t - ρ * t / 2 :=
      le_of_tendsto hRlim_neg hev
    have htneg : t < 0 := ht
    have hq : (∫ ω, X ω ∂μ) + ρ * t / 2 ≤ cgf X μ t / t := by
      linarith
    have := (le_div_iff_of_neg htneg).mp hq
    nlinarith
  · simp
  · have hev : ∀ᶠ u in nhdsWithin 0 (Set.Ioi 0),
        cgf X μ t / t - ρ * t / 2 ≤
          cgf X μ u / u - ρ * u / 2 := by
      filter_upwards [
        (eventually_lt_nhds ht).filter_mono inf_le_left,
        self_mem_nhdsWithin] with u hut hu
      exact hRanti_pos hu ht hut.le
    have hle :
        cgf X μ t / t - ρ * t / 2 ≤ (∫ ω, X ω ∂μ) :=
      ge_of_tendsto hRlim_pos hev
    have hq : cgf X μ t / t ≤ (∫ ω, X ω ∂μ) + ρ * t / 2 := by
      linarith
    have := (div_le_iff₀ ht).mp hq
    nlinarith

/-- Exponentiating the cumulant-generating-function bound. -/
theorem mgf_le_of_hasHerbstEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {ρ : ℝ}
    (hH : HasHerbstEntropyBound μ X ρ) (t : ℝ) :
    mgf X μ t ≤
      Real.exp (t * ∫ ω, X ω ∂μ + ρ * t ^ 2 / 2) := by
  have hMpos : 0 < mgf X μ t := mgf_pos (hH.1 t)
  rw [← Real.exp_log hMpos]
  exact Real.exp_le_exp.mpr
    (cgf_le_of_hasHerbstEntropyBound μ X hH t)

/-- The entropy estimate gives a centered sub-Gaussian MGF with the same
variance proxy. -/
theorem hasSubgaussianMGF_centered_of_hasHerbstEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hH : HasHerbstEntropyBound μ X ρ) :
    HasSubgaussianMGF
      (fun ω => X ω - ∫ η, X η ∂μ) ⟨ρ, hρ⟩ μ := by
  let m : ℝ := ∫ η, X η ∂μ
  constructor
  · intro t
    have heq :
        (fun ω => Real.exp (t * (X ω - m))) =
          (fun ω => Real.exp (-t * m) * Real.exp (t * X ω)) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact (hH.1 t).const_mul _
  · intro t
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
          Real.exp (-t * m) *
            Real.exp (t * ∫ ω, X ω ∂μ + ρ * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left
          (mgf_le_of_hasHerbstEntropyBound μ X hH t)
          (Real.exp_pos _).le
      _ = Real.exp (ρ * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [m]
        ring
      _ = Real.exp ((⟨ρ, hρ⟩ : ℝ≥0) * t ^ 2 / 2) := rfl

/-- A logarithmic Sobolev inequality gives the standard centered sub-Gaussian
MGF after the exponential energy estimate is supplied. -/
theorem hasSubgaussianMGF_centered_of_logSobolev
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (admissible : (Ω → ℝ) → Prop)
    (energy : (Ω → ℝ) → Ω → ℝ)
    (X : Ω → ℝ) {ρ L : ℝ} (hρ : 0 ≤ ρ)
    (hLSI : HasLogSobolevInequality μ admissible energy ρ)
    (hExp : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hAdmissible :
      ∀ t : ℝ, admissible (fun ω => Real.exp (t * X ω / 2)))
    (hEnergy : HasExponentialEnergyBound μ energy X L) :
    HasSubgaussianMGF
      (fun ω => X ω - ∫ η, X η ∂μ)
      ⟨ρ * L ^ 2, mul_nonneg hρ (sq_nonneg L)⟩ μ :=
  hasSubgaussianMGF_centered_of_hasHerbstEntropyBound μ X
    (mul_nonneg hρ (sq_nonneg L))
    (hasHerbstEntropyBound_of_logSobolev μ admissible energy X hρ
      hLSI hExp hAdmissible hEnergy)

/-- A uniform Herbst entropy estimate for all one-Lipschitz observables gives
the appendix's mean-concentration predicate. -/
theorem hasMeanConcentration_of_hasHerbstEntropyBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Ω → ℝ) (s : ℝ)
    (hHerbst :
      ∀ f : Ω → ℝ, Measurable f →
        (∀ x y, |f x - f y| ≤ d x y) → Integrable f μ →
        HasHerbstEntropyBound μ f (s ^ 2)) :
    HDP.Chapter5.HasMeanConcentration μ d s := by
  intro f hf hLip hfint t ht
  have hSubG :=
    hasSubgaussianMGF_centered_of_hasHerbstEntropyBound μ f
      (sq_nonneg s) (hHerbst f hf hLip hfint)
  convert
    twoSidedTail_of_hasSubgaussianMGF μ
      (fun ω => f ω - ∫ η, f η ∂μ) ⟨s ^ 2, sq_nonneg s⟩
      hSubG t ht using 1
  rfl

/-- Fully packaged LSI-to-mean-concentration theorem for unit-energy
Lipschitz observables.  The hypotheses expose the exact analytic/geometric
work still needed in a concrete application. -/
theorem hasMeanConcentration_of_logSobolev
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Ω → ℝ) (admissible : (Ω → ℝ) → Prop)
    (energy : (Ω → ℝ) → Ω → ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hLSI : HasLogSobolevInequality μ admissible energy ρ)
    (hExp :
      ∀ f : Ω → ℝ, Measurable f →
        (∀ x y, |f x - f y| ≤ d x y) → Integrable f μ →
        ∀ t : ℝ, Integrable (fun ω => Real.exp (t * f ω)) μ)
    (hAdmissible :
      ∀ f : Ω → ℝ, Measurable f →
        (∀ x y, |f x - f y| ≤ d x y) → Integrable f μ →
        ∀ t : ℝ, admissible (fun ω => Real.exp (t * f ω / 2)))
    (hEnergy :
      ∀ f : Ω → ℝ, Measurable f →
        (∀ x y, |f x - f y| ≤ d x y) → Integrable f μ →
        HasExponentialEnergyBound μ energy f 1) :
    HDP.Chapter5.HasMeanConcentration μ d (Real.sqrt ρ) := by
  apply hasMeanConcentration_of_hasHerbstEntropyBound
  intro f hf hLip hfint
  have hH :=
    hasHerbstEntropyBound_of_logSobolev μ admissible energy f hρ
      hLSI (hExp f hf hLip hfint) (hAdmissible f hf hLip hfint)
      (hEnergy f hf hLip hfint)
  simpa [Real.sq_sqrt hρ] using hH

end HDP.Appendix
