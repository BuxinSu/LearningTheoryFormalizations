import HighDimensionalProbability.Chapter7_RandomProcesses
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.ProductMeasure

/-!
# Vanishing Brownian grid error

This file proves that the expected largest increment on a uniform Gaussian
grid tends to zero.  It is the quantitative mesh-error input for the discrete
proof of the Brownian reflection endpoint.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP.Chapter7.BrownianGridError

noncomputable section

/-- The deterministic Gaussian maximum bound on a grid tends to zero. -/
lemma tendsto_uniformGaussianMaxBound (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt ((t : ℝ) / (n + 2 : ℝ)) *
          Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ))))
      atTop (𝓝 0) := by
  have harg :
      Tendsto (fun n : ℕ => 2 * (n + 2 : ℝ)) atTop atTop := by
    exact (tendsto_atTop_add_const_right atTop 2
      tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have hlog :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinside :
      Tendsto
        (fun n : ℕ =>
          (4 * (t : ℝ)) *
            (Real.log (2 * (n + 2 : ℝ)) /
              (2 * (n + 2 : ℝ))))
        atTop (𝓝 0) := by
    simpa using (hlog.comp harg).const_mul (4 * (t : ℝ))
  have hsqrt := hinside.sqrt
  convert hsqrt using 1
  · funext n
    rw [← Real.sqrt_mul (by positivity :
      0 ≤ (t : ℝ) / (n + 2 : ℝ))]
    congr 1
    field_simp
    all_goals ring
  · simp

/-- A uniform finite-dimensional bound for the expected largest Gaussian
increment.  Independence is present in the canonical product model, although
the Gaussian maximum estimate itself only needs the coordinate laws. -/
lemma integral_uniformGaussianMax_le (t : ℝ≥0) (n : ℕ) :
    (∫ x : Fin (n + 2) → ℝ,
      Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)
      ∂Measure.pi (fun _ : Fin (n + 2) =>
        gaussianReal 0 (t / (n + 2)))) ≤
      Real.sqrt ((t : ℝ) / (n + 2 : ℝ)) *
        Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ))) := by
  let v : ℝ≥0 := t / (n + 2)
  let s : ℝ := Real.sqrt (v : ℝ)
  let γ : Measure (Fin (n + 2) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 2) => gaussianReal 0 1)
  let scale : (Fin (n + 2) → ℝ) → (Fin (n + 2) → ℝ) :=
    fun x i => s * x i
  let F : (Fin (n + 2) → ℝ) → ℝ :=
    fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hF : Measurable F := by
    dsimp [F]
    rw [show
      (fun x : Fin (n + 2) → ℝ =>
        Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (n + 2) => fun x => |x i|) by
      funext x
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i : Fin (n + 2) =>
          fun x : Fin (n + 2) → ℝ => |x i|) x).symm]
    exact Finset.measurable_sup' Finset.univ_nonempty
      (fun i _ => (measurable_pi_apply i).abs)
  have hmap :
      γ.map scale =
        Measure.pi (fun _ : Fin (n + 2) =>
          gaussianReal 0 (t / (n + 2))) := by
    dsimp [γ, scale]
    rw [Measure.pi_map_pi]
    · apply congrArg Measure.pi
      funext i
      rw [gaussianReal_map_const_mul]
      congr 2
      · simp
      · apply NNReal.eq
        change s ^ 2 * 1 = (v : ℝ)
        rw [mul_one]
        exact Real.sq_sqrt (NNReal.coe_nonneg v)
    · intro i
      fun_prop
  have hstd :
      (∫ x : Fin (n + 2) → ℝ, F x ∂γ) ≤
        Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ))) := by
    apply HDP.Chapter2.exercise_2_38a_max_abs
    · intro i
      exact measurable_pi_apply i
    · intro i
      simpa [γ] using
        (measurePreserving_eval
          (fun _ : Fin (n + 2) => gaussianReal 0 1) i).hasLaw
  have hscale (x : Fin (n + 2) → ℝ) :
      F (scale x) = s * F x := by
    dsimp [F, scale]
    simp_rw [abs_mul, abs_of_nonneg hs0]
    exact (Finset.mul₀_sup' hs0 (fun i : Fin (n + 2) => |x i|)
      Finset.univ Finset.univ_nonempty).symm
  calc
    (∫ x : Fin (n + 2) → ℝ,
        Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)
        ∂Measure.pi (fun _ : Fin (n + 2) =>
          gaussianReal 0 (t / (n + 2)))) =
        ∫ x, F (scale x) ∂γ := by
      change (∫ x, F x ∂Measure.pi (fun _ : Fin (n + 2) =>
        gaussianReal 0 (t / (n + 2)))) = _
      rw [← hmap, integral_map (by fun_prop) hF.aestronglyMeasurable]
    _ = s * ∫ x, F x ∂γ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hscale
    _ ≤ s * Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hstd hs0
    _ = Real.sqrt ((t : ℝ) / (n + 2 : ℝ)) *
        Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ))) := by
      simp [s, v]

/-- Expected maximum absolute increment on a uniform centered Gaussian grid
tends to zero as the number of grid intervals tends to infinity. -/
theorem tendsto_integral_uniformGaussianMax (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        ∫ x : Fin (n + 2) → ℝ,
          Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)
          ∂Measure.pi (fun _ : Fin (n + 2) =>
            gaussianReal 0 (t / (n + 2))))
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    apply integral_nonneg
    intro x
    exact (abs_nonneg (x 0)).trans
      (Finset.le_sup' (fun i : Fin (n + 2) => |x i|)
        (Finset.mem_univ 0))
  · exact integral_uniformGaussianMax_le t
  · exact tendsto_uniformGaussianMaxBound t

end

end HDP.Chapter7.BrownianGridError
