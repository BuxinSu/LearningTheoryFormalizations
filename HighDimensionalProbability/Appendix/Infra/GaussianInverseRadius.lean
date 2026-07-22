import HighDimensionalProbability.Prelude.Sphere
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The inverse-square radial moment of a standard Gaussian

For a standard Gaussian vector in real dimension `n ≥ 3`,

`E ‖G‖⁻² = 1 / (n - 2)`.

This is the radial calculation needed to transfer the dimension-free
Gaussian logarithmic Sobolev inequality to the unit sphere.  The proof first
records the elementary Gamma-integral recurrence for the unnormalized radial
density.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace HDP.Appendix

/-- The radial Gaussian integrals in exponents differing by two satisfy the
usual integration-by-parts recurrence. -/
lemma radialGaussianIntegral_succ_succ (k : ℕ) :
    (∫ r : ℝ in Set.Ioi 0,
        r ^ (k + 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) =
      (k + 1 : ℝ) *
        ∫ r : ℝ in Set.Ioi 0,
          r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (-1 : ℝ) < (k : ℝ) := by linarith
  have hk20 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg (k + 2)
  have hk2 : (-1 : ℝ) < ((k + 2 : ℕ) : ℝ) := by linarith
  have hbase := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) hk (by norm_num)
  have hnext := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := ((k + 2 : ℕ) : ℝ))
    (b := (1 / 2 : ℝ)) (by norm_num) hk2 (by norm_num)
  have hbase_nat :
      (∫ r : ℝ in Set.Ioi 0,
          r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) =
        (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
          Real.Gamma (((k : ℝ) + 1) / 2) := by
    simpa only [Real.rpow_natCast, Real.rpow_two] using hbase
  have hnext_nat :
      (∫ r : ℝ in Set.Ioi 0,
          r ^ (k + 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) =
        (1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2) * (1 / 2 : ℝ) *
          Real.Gamma (((k : ℝ) + 2 + 1) / 2) := by
    have hnext_nat' :
        (∫ r : ℝ in Set.Ioi 0,
            r ^ (k + 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) =
          (1 / 2 : ℝ) ^ (-(((k + 2 : ℕ) : ℝ) + 1) / 2) *
            (1 / 2 : ℝ) *
            Real.Gamma ((((k + 2 : ℕ) : ℝ) + 1) / 2) := by
      simpa only [Real.rpow_natCast, Real.rpow_two] using hnext
    convert hnext_nat' using 1 <;> norm_num
  have hgamma :
      Real.Gamma (((k : ℝ) + 2 + 1) / 2) =
        (((k : ℝ) + 1) / 2) *
          Real.Gamma (((k : ℝ) + 1) / 2) := by
    convert Real.Gamma_add_one
      (show ((k : ℝ) + 1) / 2 ≠ 0 by positivity) using 1 <;> ring
  rw [hnext_nat, hbase_nat, hgamma]
  have hpow :
      (1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2) =
        2 * (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
    rw [show -((k : ℝ) + 2 + 1) / 2 =
        -((k : ℝ) + 1) / 2 - 1 by ring,
      Real.rpow_sub_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    ring
  rw [hpow]
  ring

/-- Polar coordinates for the unnormalized standard-Gaussian density in
dimension `k + 3`. -/
private lemma gaussianFullRadialVolume (k : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) =
      (k + 3 : ℝ) *
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 3)))).real
          (Metric.ball 0 1) *
        ∫ r : ℝ in Set.Ioi 0,
          r ^ (k + 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
  letI : Nonempty (Fin (k + 3)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  have h := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 3))))
    (fun r : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * r ^ 2))
  convert h using 1 <;>
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul,
      smul_eq_mul] <;>
    norm_num <;>
    ring

/-- Polar coordinates for the inverse-square weighted Gaussian density in
dimension `k + 3`. -/
private lemma gaussianInverseSquareRadialVolume (k : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        (‖x‖ ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) =
      (k + 3 : ℝ) *
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 3)))).real
          (Metric.ball 0 1) *
        ∫ r : ℝ in Set.Ioi 0,
          r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
  letI : Nonempty (Fin (k + 3)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  have h := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 3))))
    (fun r : ℝ ↦
      (r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * r ^ 2))
  have hrad :
      (∫ r : ℝ in Set.Ioi 0,
          r ^ (k + 2) *
            ((r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * r ^ 2))) =
        ∫ r : ℝ in Set.Ioi 0,
          r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    change r ^ (k + 2) *
        ((r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) =
      r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2)
    rw [pow_add]
    field_simp
  calc
    (∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        (‖x‖ ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) =
        (k + 3 : ℝ) *
          (volume : Measure (EuclideanSpace ℝ (Fin (k + 3)))).real
            (Metric.ball 0 1) *
          ∫ r : ℝ in Set.Ioi 0,
            r ^ (k + 2) *
              ((r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
      convert h using 1 <;>
        simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul,
          smul_eq_mul] <;>
        norm_num <;>
        ring
    _ = _ := by rw [hrad]

/-- In dimension `k + 3`, the inverse-square radial moment of a standard
Gaussian is exactly `1 / (k + 1)`. -/
theorem integral_norm_sq_inv_stdGaussian (k : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        (‖x‖ ^ 2)⁻¹
          ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 3)))) =
      ((k + 1 : ℕ) : ℝ)⁻¹ := by
  let E := EuclideanSpace ℝ (Fin (k + 3))
  letI : Nonempty (Fin (k + 3)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  have hfull := gaussianFullRadialVolume k
  have hinv := gaussianInverseSquareRadialVolume k
  have hrec := radialGaussianIntegral_succ_succ k
  have hvolume :
      (∫ x : E, Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) =
        (k + 1 : ℝ) *
          ∫ x : E,
            (‖x‖ ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
    calc
      (∫ x : E, Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) =
          (k + 3 : ℝ) *
            (volume : Measure E).real (Metric.ball 0 1) *
            ∫ r : ℝ in Set.Ioi 0,
              r ^ (k + 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := hfull
      _ = (k + 3 : ℝ) *
            (volume : Measure E).real (Metric.ball 0 1) *
            ((k + 1 : ℝ) *
              ∫ r : ℝ in Set.Ioi 0,
                r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
          rw [hrec]
      _ = (k + 1 : ℝ) *
            ∫ x : E,
              (‖x‖ ^ 2)⁻¹ *
                Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
          rw [hinv]
          ring
  have hnormalization := HDP.integral_gaussianRadialDensity E
  simp_rw [HDP.coe_gaussianRadialDensity] at hnormalization
  rw [integral_const_mul] at hnormalization
  rw [← HDP.gaussianRadialMeasure_eq_stdGaussian E,
    HDP.gaussianRadialMeasure,
    integral_withDensity_eq_integral_smul
      (HDP.measurable_gaussianRadialDensity E)]
  simp_rw [NNReal.smul_def, smul_eq_mul, HDP.coe_gaussianRadialDensity]
  rw [show (fun x : E ↦
      ((HDP.gaussianRadialNormalizer E)⁻¹ *
          Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) *
        (‖x‖ ^ 2)⁻¹) =
      fun x : E ↦
        (HDP.gaussianRadialNormalizer E)⁻¹ *
          ((‖x‖ ^ 2)⁻¹ *
            Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) by
      funext x
      ring]
  rw [integral_const_mul]
  have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
  calc
    (HDP.gaussianRadialNormalizer E)⁻¹ *
          ∫ x : E,
            (‖x‖ ^ 2)⁻¹ *
              Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) =
        (k + 1 : ℝ)⁻¹ *
          ((HDP.gaussianRadialNormalizer E)⁻¹ *
            ∫ x : E,
              Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) := by
      rw [hvolume]
      field_simp
    _ = ((k + 1 : ℕ) : ℝ)⁻¹ := by
      rw [hnormalization]
      norm_num

end HDP.Appendix
