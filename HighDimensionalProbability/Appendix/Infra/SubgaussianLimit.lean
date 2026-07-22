import HighDimensionalProbability.Appendix.Infra.Concentration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded limits of sub-Gaussian observables

This file records the elementary closure argument needed when a Lipschitz
observable on a compact space is approximated by smooth observables.  A
pointwise-convergent, uniformly bounded sequence with a common centered
sub-Gaussian MGF bound has the same bound in the limit.
-/

open Filter MeasureTheory ProbabilityTheory Real
open scoped NNReal Topology

namespace HDP.Appendix

noncomputable section

/-- Centered sub-Gaussian MGF bounds are closed under pointwise convergence
when the approximating observables and their limit share a uniform bound. -/
theorem hasSubgaussianMGF_centered_of_bounded_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ≥0) (B : ℝ)
    (hXn : ∀ n, Measurable (Xn n))
    (hX : Measurable X)
    (hXnB : ∀ n ω, |Xn n ω| ≤ B)
    (hXB : ∀ ω, |X ω| ≤ B)
    (hlim : ∀ ω, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω)))
    (hsub :
      ∀ n,
        HasSubgaussianMGF
          (fun ω => Xn n ω - ∫ η, Xn n η ∂μ) c μ) :
    HasSubgaussianMGF
      (fun ω => X ω - ∫ η, X η ∂μ) c μ := by
  have hmean :
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop
        (𝓝 (∫ ω, X ω ∂μ)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Filter.Eventually.of_forall fun n =>
        (hXn n).aestronglyMeasurable
    · refine ⟨B, Filter.Eventually.of_forall fun n =>
        Filter.Eventually.of_forall fun ω => ?_⟩
      simpa [Real.norm_eq_abs] using hXnB n ω
    · exact ae_of_all μ hlim
  have hmean_n_bound (n : ℕ) :
      |∫ ω, Xn n ω ∂μ| ≤ B := by
    have h :=
      norm_integral_le_of_norm_le_const
        (μ := μ) (f := Xn n) (C := B)
        (Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using hXnB n ω)
    simpa [Real.norm_eq_abs] using h
  have hmean_bound :
      |∫ ω, X ω ∂μ| ≤ B := by
    have h :=
      norm_integral_le_of_norm_le_const
        (μ := μ) (f := X) (C := B)
        (Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using hXB ω)
    simpa [Real.norm_eq_abs] using h
  have hcenter_n_bound (n : ℕ) (ω : Ω) :
      |Xn n ω - ∫ η, Xn n η ∂μ| ≤ 2 * B := by
    calc
      |Xn n ω - ∫ η, Xn n η ∂μ| ≤
          |Xn n ω| + |∫ η, Xn n η ∂μ| := abs_sub _ _
      _ ≤ B + B := add_le_add (hXnB n ω) (hmean_n_bound n)
      _ = 2 * B := by ring
  have hcenter_bound (ω : Ω) :
      |X ω - ∫ η, X η ∂μ| ≤ 2 * B := by
    calc
      |X ω - ∫ η, X η ∂μ| ≤
          |X ω| + |∫ η, X η ∂μ| := abs_sub _ _
      _ ≤ B + B := add_le_add (hXB ω) hmean_bound
      _ = 2 * B := by ring
  refine
    { integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t
    have hmeas :
        AEStronglyMeasurable
          (fun ω => Real.exp
            (t * (X ω - ∫ η, X η ∂μ))) μ := by
      exact
        (hX.sub measurable_const).const_mul t |>.exp
          |>.aestronglyMeasurable
    apply Integrable.mono'
      (integrable_const (Real.exp (|t| * (2 * B))))
      hmeas
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * (X ω - ∫ η, X η ∂μ) ≤
          |t| * |X ω - ∫ η, X η ∂μ| := by
        exact le_trans (le_abs_self _) (abs_mul _ _).le
      _ ≤ |t| * (2 * B) :=
        mul_le_mul_of_nonneg_left (hcenter_bound ω) (abs_nonneg t)
  · intro t
    have hcenter_lim (ω : Ω) :
        Tendsto
          (fun n => Xn n ω - ∫ η, Xn n η ∂μ) atTop
          (𝓝 (X ω - ∫ η, X η ∂μ)) :=
      (hlim ω).sub hmean
    have hexp_lim (ω : Ω) :
        Tendsto
          (fun n =>
            Real.exp
              (t * (Xn n ω - ∫ η, Xn n η ∂μ))) atTop
          (𝓝
            (Real.exp
              (t * (X ω - ∫ η, X η ∂μ)))) :=
      (Real.continuous_exp.tendsto _).comp
        ((tendsto_const_nhds.mul (hcenter_lim ω)))
    have hint_lim :
        Tendsto
          (fun n =>
            ∫ ω,
              Real.exp
                (t * (Xn n ω - ∫ η, Xn n η ∂μ)) ∂μ)
          atTop
          (𝓝
            (∫ ω,
              Real.exp
                (t * (X ω - ∫ η, X η ∂μ)) ∂μ)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Filter.Eventually.of_forall fun n =>
          ((hXn n).sub measurable_const).const_mul t |>.exp
            |>.aestronglyMeasurable
      · refine
          ⟨Real.exp (|t| * (2 * B)),
            Filter.Eventually.of_forall fun n =>
            Filter.Eventually.of_forall fun ω => ?_⟩
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          t * (Xn n ω - ∫ η, Xn n η ∂μ) ≤
              |t| * |Xn n ω - ∫ η, Xn n η ∂μ| := by
            exact le_trans (le_abs_self _) (abs_mul _ _).le
          _ ≤ |t| * (2 * B) :=
            mul_le_mul_of_nonneg_left
              (hcenter_n_bound n ω) (abs_nonneg t)
      · exact ae_of_all μ hexp_lim
    unfold mgf
    exact le_of_tendsto hint_lim
      (Filter.Eventually.of_forall fun n => (hsub n).mgf_le t)

end

end HDP.Appendix
