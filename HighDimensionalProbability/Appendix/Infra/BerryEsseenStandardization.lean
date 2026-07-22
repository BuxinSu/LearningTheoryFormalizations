import HighDimensionalProbability.Appendix.Infra.BerryEsseenTaylor
import Mathlib.Probability.Moments.Variance

/-!
# Standardization lemmas for Berry--Esseen

This file records the moment identities for `(X - m) / σ` in the exact form
used by the quantitative characteristic-function argument.
-/

open MeasureTheory ProbabilityTheory Real

namespace HDP.Appendix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Standardize a real-valued random variable by a prescribed mean and positive
standard deviation. -/
noncomputable def standardized (X : Ω → ℝ) (m σ : ℝ) : Ω → ℝ :=
  fun ω => (X ω - m) / σ

lemma memLp_standardized [IsFiniteMeasure P]
    {X : Ω → ℝ} {m σ : ℝ} (hX : MemLp X 3 P) :
    MemLp (standardized X m σ) 3 P := by
  change MemLp (fun ω => (X ω - m) / σ) 3 P
  simpa only [div_eq_mul_inv, Pi.sub_apply] using
    (hX.sub (memLp_const m)).mul_const σ⁻¹

lemma integral_standardized_eq_zero [IsProbabilityMeasure P]
    {X : Ω → ℝ} {m σ : ℝ} (_hσ : 0 < σ) (hX : MemLp X 3 P)
    (hmean : ∫ ω, X ω ∂P = m) :
    ∫ ω, standardized X m σ ω ∂P = 0 := by
  have hXint : Integrable X P :=
    hX.integrable (by norm_num)
  rw [show (fun ω => standardized X m σ ω) =
      fun ω => (X ω - m) / σ by rfl,
    integral_div, integral_sub hXint (integrable_const m), hmean]
  simp

lemma integral_standardized_sq_eq_one [IsProbabilityMeasure P]
    {X : Ω → ℝ} {m σ : ℝ} (hσ : 0 < σ) (hX : MemLp X 3 P)
    (hmean : ∫ ω, X ω ∂P = m)
    (hvar : ProbabilityTheory.variance X P = σ ^ 2) :
    ∫ ω, standardized X m σ ω ^ 2 ∂P = 1 := by
  have hXm : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hcenter :
      ∫ ω, (X ω - m) ^ 2 ∂P = σ ^ 2 := by
    rw [← hvar, variance_eq_integral hXm, hmean]
  have hpoint :
      (fun ω => standardized X m σ ω ^ 2) =
        fun ω => (X ω - m) ^ 2 / σ ^ 2 := by
    funext ω
    simp only [standardized]
    field_simp [hσ.ne']
  rw [hpoint, integral_div, hcenter, div_self]
  exact pow_ne_zero 2 hσ.ne'

lemma integral_abs_standardized_pow_three [IsProbabilityMeasure P]
    {X : Ω → ℝ} {m σ : ℝ} (hσ : 0 < σ) :
    (∫ ω, |standardized X m σ ω| ^ 3 ∂P) =
      (∫ ω, |X ω - m| ^ 3 ∂P) / σ ^ 3 := by
  have hpoint :
      (fun ω => |standardized X m σ ω| ^ 3) =
        fun ω => |X ω - m| ^ 3 / σ ^ 3 := by
    funext ω
    simp only [standardized, abs_div, abs_of_pos hσ]
    ring
  rw [hpoint, integral_div]

end HDP.Appendix
