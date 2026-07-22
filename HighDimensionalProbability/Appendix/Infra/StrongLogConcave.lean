import HighDimensionalProbability.Appendix.Infra.Concentration
import HighDimensionalProbability.Appendix.Infra.PrekopaLeindler
import HighDimensionalProbability.Prelude.Sphere
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Strong

/-!
# Strongly log-concave measures

This file develops the Prékopa--Leindler/property-`(τ)` route from a strongly
convex potential to dimension-free concentration.  It stays entirely in the
isolated appendix tree.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

/-- The probability measure with density proportional to `exp (-U)`. -/
noncomputable def exponentialPotentialMeasure {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))

end HDP.Chapter5

namespace HDP.Appendix

open HDP.Chapter5

/-- A strongly convex density satisfies the corresponding
quadratic-cost Prékopa--Leindler inequality. -/
theorem gaussPL_exponentialPotentialMeasure {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) → ℝ) (hUm : Measurable U)
    {κ : ℝ} (hU : StrongConvexOn Set.univ κ U) :
    MatrixConcentration.GaussPL (exponentialPotentialMeasure U)
      (fun p x y => (1 - p) • x + p • y)
      (fun x y => κ * dist x y ^ 2) := by
  intro p hp0 hp1 F G H hF hG hH hcond
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-U x))
  have hρm : Measurable ρ :=
    ENNReal.measurable_ofReal.comp (hUm.neg.exp)
  have hFm : Measurable fun x => F x * ρ x := hF.mul hρm
  have hGm : Measurable fun x => G x * ρ x := hG.mul hρm
  have hHm : Measurable fun x => H x * ρ x := hH.mul hρm
  have hρcombo : ∀ x y,
      ρ x ^ (1 - p) * ρ y ^ p ≤
        ENNReal.ofReal
            (Real.exp (-(p * (1 - p) / 2) * (κ * dist x y ^ 2))) *
          ρ ((1 - p) • x + p • y) := by
    intro x y
    have hconv := hU.2 (Set.mem_univ x) (Set.mem_univ y)
      h1p.le hp0.le (by ring : (1 - p) + p = 1)
    simp only [smul_eq_mul] at hconv
    have harg :
        -U x * (1 - p) + -U y * p ≤
          -(p * (1 - p) / 2) * (κ * dist x y ^ 2) +
            -U ((1 - p) • x + p • y) := by
      rw [dist_eq_norm]
      nlinarith [hconv]
    simp only [ρ]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ← Real.exp_mul, ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    convert harg using 1 <;> ring
  have hpoint : ∀ x y,
      (F x * ρ x) ^ (1 - p) * (G y * ρ y) ^ p ≤
        (H ((1 - p) • x + p • y) *
          ρ ((1 - p) • x + p • y)) := by
    intro x y
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1p.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    calc
      (F x ^ (1 - p) * ρ x ^ (1 - p)) *
          (G y ^ p * ρ y ^ p) =
          (F x ^ (1 - p) * G y ^ p) *
            (ρ x ^ (1 - p) * ρ y ^ p) := by ring
      _ ≤ (F x ^ (1 - p) * G y ^ p) *
          (ENNReal.ofReal
              (Real.exp (-(p * (1 - p) / 2) *
                (κ * dist x y ^ 2))) *
            ρ ((1 - p) • x + p • y)) :=
        mul_le_mul_left' (hρcombo x y) _
      _ = (F x ^ (1 - p) * G y ^ p *
          ENNReal.ofReal
            (Real.exp (-(p * (1 - p) / 2) *
              (κ * dist x y ^ 2)))) *
          ρ ((1 - p) • x + p • y) := by ring
      _ ≤ H ((1 - p) • x + p • y) *
          ρ ((1 - p) • x + p • y) :=
        mul_le_mul_right' (hcond x y) _
  have hPL := prekopaLeindler_euclideanSpace n p hp0 hp1
    (fun x => F x * ρ x) (fun x => G x * ρ x)
    (fun x => H x * ρ x) hFm hGm hHm hpoint
  have hFI :
      (∫⁻ x, F x ∂volume.withDensity ρ) = ∫⁻ x, F x * ρ x := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hρm hF]
    exact lintegral_congr fun x => mul_comm _ _
  have hGI :
      (∫⁻ x, G x ∂volume.withDensity ρ) = ∫⁻ x, G x * ρ x := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hρm hG]
    exact lintegral_congr fun x => mul_comm _ _
  have hHI :
      (∫⁻ x, H x ∂volume.withDensity ρ) = ∫⁻ x, H x * ρ x := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hρm hH]
    exact lintegral_congr fun x => mul_comm _ _
  simpa [exponentialPotentialMeasure, ρ, hFI, hGI, hHI] using hPL

/-- The property-`(τ)` estimate at an intermediate Prékopa--Leindler
parameter.  Notice that no exponential-integrability hypothesis is needed:
the Prékopa--Leindler inequality itself forces the two positive exponential
integrals appearing in the proof to be finite. -/
lemma gaussPL_metric_pl_bound
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (comb : ℝ → α → α → α) {κ : ℝ} (hκ : 0 < κ)
    (hPL : MatrixConcentration.GaussPL μ comb
      (fun x y => κ * dist x y ^ 2))
    (W : α → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤ dist x y)
    (hmeas : Measurable W) (hWint : Integrable W μ)
    {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : 0 < s) :
    Integrable (fun x => Real.exp (p * s * W x)) μ ∧
    (∫ x, Real.exp (p * s * W x) ∂μ) ≤
      Real.exp (p * (s * (∫ x, W x ∂μ) + s ^ 2 / (2 * κ))) := by
  have h1p : 0 < 1 - p := by linarith
  let F : α → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (p * (s * W x - s ^ 2 / (2 * κ))))
  let G : α → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (-(1 - p) * s * W y))
  let H : α → ℝ≥0∞ := fun _ => 1
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hHm : Measurable H := measurable_const
  have hcond : ∀ x y : α,
      F x ^ (1 - p) * G y ^ p *
          ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) *
            (κ * dist x y ^ 2))) ≤ H (comb p x y) := by
    intro x y
    let d : ℝ := dist x y
    have hdiff : W x - W y ≤ d :=
      (le_abs_self _).trans (by simpa [d] using hLip x y)
    have hamgm0 : 2 * κ * (s * d) ≤ s ^ 2 + (κ * d) ^ 2 := by
      nlinarith [sq_nonneg (κ * d - s)]
    have hamgm1 : s * d ≤ (s ^ 2 + (κ * d) ^ 2) / (2 * κ) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * κ)]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hamgm0
    have hamgm : s * d ≤ s ^ 2 / (2 * κ) + κ * d ^ 2 / 2 := by
      calc
        s * d ≤ (s ^ 2 + (κ * d) ^ 2) / (2 * κ) := hamgm1
        _ = s ^ 2 / (2 * κ) + κ * d ^ 2 / 2 := by
          field_simp [hκ.ne']
    have hbase :
        s * (W x - W y) - s ^ 2 / (2 * κ) - κ * d ^ 2 / 2 ≤ 0 := by
      have hmul := mul_le_mul_of_nonneg_left hdiff hs.le
      linarith
    have harg : p * (1 - p) *
        (s * (W x - W y) - s ^ 2 / (2 * κ) - κ * d ^ 2 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp0.le h1p.le) hbase
    simp only [F, G, H]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← Real.exp_mul, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add]
    apply ENNReal.ofReal_le_one.mpr
    rw [Real.exp_le_one_iff]
    convert harg using 1
    simp only [d]
    ring
  have hPL0 := hPL p hp0 hp1 F G H hFm hGm hHm hcond
  let AF : ℝ≥0∞ := ∫⁻ x, F x ∂μ
  let AG : ℝ≥0∞ := ∫⁻ x, G x ∂μ
  have hprod : AF ^ (1 - p) * AG ^ p ≤ 1 := by
    simpa only [AF, AG, H, lintegral_const, measure_univ, one_mul] using hPL0
  have hFpos : 0 < AF := by
    change 0 < ∫⁻ x, F x ∂μ
    rw [lintegral_pos_iff_support hFm]
    have hsupp : Function.support F = Set.univ := by
      ext x
      simp [Function.support, F, ENNReal.ofReal_eq_zero, Real.exp_pos]
    rw [hsupp, measure_univ]
    exact zero_lt_one
  have hGpos : 0 < AG := by
    change 0 < ∫⁻ x, G x ∂μ
    rw [lintegral_pos_iff_support hGm]
    have hsupp : Function.support G = Set.univ := by
      ext x
      simp [Function.support, G, ENNReal.ofReal_eq_zero, Real.exp_pos]
    rw [hsupp, measure_univ]
    exact zero_lt_one
  have hprodlt : AF ^ (1 - p) * AG ^ p < ∞ :=
    hprod.trans_lt (by simp)
  have hpowsfin : AF ^ (1 - p) < ∞ ∧ AG ^ p < ∞ := by
    rcases ENNReal.mul_lt_top_iff.mp hprodlt with h | h | h
    · exact h
    · exact False.elim ((ENNReal.rpow_pos_of_nonneg hFpos h1p.le).ne' h)
    · exact False.elim ((ENNReal.rpow_pos_of_nonneg hGpos hp0.le).ne' h)
  have hAFfin : AF < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos h1p).mp hpowsfin.1
  have hAGfin : AG < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hpowsfin.2
  have hFint : Integrable
      (fun x => Real.exp (p * (s * W x - s ^ 2 / (2 * κ)))) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).mp
    simpa only [AF, F] using hAFfin.ne
  have hGint :
      Integrable (fun x => Real.exp (-(1 - p) * s * W x)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).mp
    simpa only [AG, G] using hAGfin.ne
  have hFL : AF = ENNReal.ofReal
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) ∂μ) := by
    change (∫⁻ x, F x ∂μ) = _
    simp only [F]
    rw [← ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
  have hGL : AG = ENNReal.ofReal
      (∫ x, Real.exp (-(1 - p) * s * W x) ∂μ) := by
    change (∫⁻ x, G x ∂μ) = _
    simp only [G]
    rw [← ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
  have hFrealpos : 0 <
      ∫ x, Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) ∂μ :=
    integral_exp_pos hFint
  have hGrealpos : 0 <
      ∫ x, Real.exp (-(1 - p) * s * W x) ∂μ :=
    integral_exp_pos hGint
  have hPLreal :
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) ∂μ) ^ (1 - p) *
        (∫ x, Real.exp (-(1 - p) * s * W x) ∂μ) ^ p ≤ 1 := by
    rw [hFL, hGL] at hprod
    have ht := ENNReal.toReal_mono (by simp) hprod
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hFrealpos.le,
      ENNReal.toReal_ofReal hGrealpos.le, ENNReal.toReal_one] at ht
    exact ht
  let m : ℝ := ∫ x, W x ∂μ
  let J : ℝ := Real.exp (-(1 - p) * s * m)
  have hJpos : 0 < J := Real.exp_pos _
  have hJ : J ≤ ∫ x, Real.exp (-(1 - p) * s * W x) ∂μ := by
    have hjensen := convexOn_exp.map_integral_le Real.continuousOn_exp
      isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      (hWint.const_mul (-(1 - p) * s)) hGint
    simpa only [Function.comp_apply, integral_const_mul, J, m] using hjensen
  have hcore :
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) ∂μ) ^ (1 - p) *
        J ^ p ≤ 1 := by
    calc
      _ ≤ (∫ x, Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) ∂μ) ^
          (1 - p) *
          (∫ x, Real.exp (-(1 - p) * s * W x) ∂μ) ^ p := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hJpos.le hJ hp0.le)
          (Real.rpow_nonneg hFrealpos.le _)
      _ ≤ 1 := hPLreal
  let A : ℝ := ∫ x, Real.exp (p * s * W x) ∂μ
  have hAint : Integrable (fun x => Real.exp (p * s * W x)) μ := by
    have heq : (fun x => Real.exp (p * s * W x)) =
        fun x => Real.exp (p * (s ^ 2 / (2 * κ))) *
          Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hFint.const_mul _
  have hApos : 0 < A := integral_exp_pos hAint
  have hFeq :
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / (2 * κ))) ∂μ) =
        Real.exp (-p * (s ^ 2 / (2 * κ))) * A := by
    have heq :
        (fun x => Real.exp (p * (s * W x - s ^ 2 / (2 * κ)))) =
          fun x => Real.exp (-p * (s ^ 2 / (2 * κ))) *
            Real.exp (p * s * W x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, integral_const_mul]
  have hlog :
      (1 - p) *
          Real.log (Real.exp (-p * (s ^ 2 / (2 * κ))) * A) +
        p * Real.log J ≤ 0 := by
    have hleftpos : 0 <
        (Real.exp (-p * (s ^ 2 / (2 * κ))) * A) ^ (1 - p) *
          J ^ p := by
      positivity
    have hlogle : Real.log
        ((Real.exp (-p * (s ^ 2 / (2 * κ))) * A) ^ (1 - p) *
          J ^ p) ≤ Real.log 1 := by
      apply Real.log_le_log hleftpos
      simpa only [hFeq] using hcore
    rw [Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne'
        (Real.rpow_pos_of_pos hJpos _).ne',
      Real.log_rpow (by positivity), Real.log_rpow hJpos,
      Real.log_one] at hlogle
    exact hlogle
  have hlogA :
      Real.log A ≤ p * (s * m + s ^ 2 / (2 * κ)) := by
    rw [Real.log_mul (Real.exp_ne_zero _) hApos.ne', Real.log_exp] at hlog
    simp only [J, Real.log_exp] at hlog
    nlinarith
  have hAle :
      A ≤ Real.exp (p * (s * m + s ^ 2 / (2 * κ))) :=
    Real.le_exp_of_log_le hlogA
  exact ⟨hAint, by simpa only [A, m] using hAle⟩

/-- A one-Lipschitz integrable function under a probability measure with the
quadratic Gauss--Prékopa--Leindler property has sub-Gaussian MGF parameter
`2 / κ`.  The harmless factor two comes from fixing the interpolation
parameter to `p = 1/2`. -/
theorem gaussPL_metric_hasSubgaussianMGF
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (comb : ℝ → α → α → α) {κ : ℝ} (hκ : 0 < κ)
    (hPL : MatrixConcentration.GaussPL μ comb
      (fun x y => κ * dist x y ^ 2))
    (W : α → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤ dist x y)
    (hmeas : Measurable W) (hWint : Integrable W μ) :
    HasSubgaussianMGF (fun x => W x - ∫ y, W y ∂μ)
      ⟨2 / κ, by positivity⟩ μ := by
  have hpos : ∀ {u : ℝ}, 0 < u →
      Integrable (fun x => Real.exp (u * W x)) μ ∧
      (∫ x, Real.exp (u * (W x - ∫ y, W y ∂μ)) ∂μ) ≤
        Real.exp (u ^ 2 / κ) := by
    intro u hu
    have hhalf := gaussPL_metric_pl_bound μ comb hκ hPL W hLip hmeas hWint
      (p := 1 / 2) (s := 2 * u) (by norm_num) (by norm_num) (by positivity)
    have hunc :
        (∫ x, Real.exp (u * W x) ∂μ) ≤
          Real.exp (u * (∫ x, W x ∂μ) + u ^ 2 / κ) := by
      convert hhalf.2 using 1
      · congr 3
        ring
      · congr 2
        field_simp [hκ.ne']
    have hcenterEq :
        (fun x => Real.exp (u * (W x - ∫ y, W y ∂μ))) =
          fun x => Real.exp (-u * ∫ y, W y ∂μ) *
            Real.exp (u * W x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    constructor
    · convert hhalf.1 using 1
      congr 2
      ring
    · rw [hcenterEq, integral_const_mul]
      calc
        Real.exp (-u * ∫ y, W y ∂μ) *
              ∫ x, Real.exp (u * W x) ∂μ ≤
            Real.exp (-u * ∫ y, W y ∂μ) *
              Real.exp (u * (∫ x, W x ∂μ) + u ^ 2 / κ) :=
          mul_le_mul_of_nonneg_left hunc (Real.exp_nonneg _)
        _ = Real.exp (u ^ 2 / κ) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hall : ∀ u : ℝ,
      Integrable (fun x => Real.exp
        (u * (W x - ∫ y, W y ∂μ))) μ ∧
      (∫ x, Real.exp (u * (W x - ∫ y, W y ∂μ)) ∂μ) ≤
        Real.exp (u ^ 2 / κ) := by
    intro u
    rcases lt_trichotomy u 0 with hu | hu | hu
    · let V : α → ℝ := fun x => -W x
      have hVLip : ∀ x y, |V x - V y| ≤ dist x y := by
        intro x y
        change |-W x - -W y| ≤ _
        rw [show -W x - -W y = -(W x - W y) by ring, abs_neg]
        exact hLip x y
      have hV' := gaussPL_metric_pl_bound μ comb hκ hPL V hVLip hmeas.neg
        hWint.neg (p := 1 / 2) (s := 2 * (-u))
        (by norm_num) (by norm_num)
        (mul_pos (by norm_num) (neg_pos.mpr hu))
      have hcenterEq :
          (fun x => Real.exp ((-u) *
            (V x - ∫ y, V y ∂μ))) =
            fun x => Real.exp (u * (W x - ∫ y, W y ∂μ)) := by
        funext x
        congr 1
        simp only [V, integral_neg]
        ring
      have huncV :
          (∫ x, Real.exp ((-u) * V x) ∂μ) ≤
            Real.exp ((-u) * (∫ x, V x ∂μ) + (-u) ^ 2 / κ) := by
        convert hV'.2 using 1
        · congr 3
          ring
        · congr 2
          field_simp [hκ.ne']
      have hcenterV :
          (∫ x, Real.exp ((-u) * (V x - ∫ y, V y ∂μ)) ∂μ) ≤
            Real.exp ((-u) ^ 2 / κ) := by
        have heq :
            (fun x => Real.exp ((-u) * (V x - ∫ y, V y ∂μ))) =
              fun x => Real.exp (-(-u) * ∫ y, V y ∂μ) *
                Real.exp ((-u) * V x) := by
          funext x
          rw [← Real.exp_add]
          congr 1
          ring
        rw [heq, integral_const_mul]
        calc
          Real.exp (-(-u) * ∫ y, V y ∂μ) *
                ∫ x, Real.exp ((-u) * V x) ∂μ ≤
              Real.exp (-(-u) * ∫ y, V y ∂μ) *
                Real.exp ((-u) * (∫ x, V x ∂μ) + (-u) ^ 2 / κ) :=
            mul_le_mul_of_nonneg_left huncV (Real.exp_nonneg _)
          _ = Real.exp ((-u) ^ 2 / κ) := by
            rw [← Real.exp_add]
            congr 1
            ring
      constructor
      · rw [← hcenterEq]
        have heq :
            (fun x => Real.exp ((-u) * (V x - ∫ y, V y ∂μ))) =
              fun x => Real.exp (-(-u) * ∫ y, V y ∂μ) *
                Real.exp ((-u) * V x) := by
          funext x
          rw [← Real.exp_add]
          congr 1
          ring
        rw [heq]
        have hVexp : Integrable (fun x => Real.exp ((-u) * V x)) μ := by
          convert hV'.1 using 1
          congr 2
          ring
        exact hVexp.const_mul _
      · rw [← hcenterEq]
        convert hcenterV using 1
        ring
    · subst u
      simp
    · have hu' := hpos hu
      have hcenterEq :
          (fun x => Real.exp (u * (W x - ∫ y, W y ∂μ))) =
            fun x => Real.exp (-u * ∫ y, W y ∂μ) *
              Real.exp (u * W x) := by
        funext x
        rw [← Real.exp_add]
        congr 1
        ring
      exact ⟨by
        rw [hcenterEq]
        exact hu'.1.const_mul _, hu'.2⟩
  constructor
  · exact fun u => (hall u).1
  · intro u
    have h := (hall u).2
    change ProbabilityTheory.mgf
      (fun x => W x - ∫ y, W y ∂μ) μ u ≤
        Real.exp (((2 / κ : ℝ) * u ^ 2) / 2)
    simpa only [ProbabilityTheory.mgf] using
      (show (∫ x, Real.exp (u * (W x - ∫ y, W y ∂μ)) ∂μ) ≤
          Real.exp (((2 / κ : ℝ) * u ^ 2) / 2) by
        convert h using 1
        field_simp [hκ.ne'])

/-- Mean concentration supplied directly by the quadratic
Gauss--Prékopa--Leindler property. -/
theorem gaussPL_metric_hasMeanConcentration
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (comb : ℝ → α → α → α) {κ : ℝ} (hκ : 0 < κ)
    (hPL : MatrixConcentration.GaussPL μ comb
      (fun x y => κ * dist x y ^ 2)) :
    HDP.Chapter5.HasMeanConcentration μ (fun x y => dist x y)
      (Real.sqrt 2 / Real.sqrt κ) := by
  intro f hf hLip hfint t ht
  have hsubg := gaussPL_metric_hasSubgaussianMGF
    μ comb hκ hPL f hLip hf hfint
  let cκ : ℝ≥0 := ⟨2 / κ, by positivity⟩
  have htail := twoSidedTail_of_hasSubgaussianMGF μ
    (fun x => f x - ∫ y, f y ∂μ) cκ
    hsubg t ht
  have hcκ : (cκ : ℝ) = 2 / κ := rfl
  have hscale :
      (Real.sqrt 2 / Real.sqrt κ) ^ 2 = 2 / κ := by
    rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hκ.le]
  simpa only [hscale, hcκ] using htail

end HDP.Appendix
