import HighDimensionalProbability.Appendix.Infra.MetricExpansion
import HighDimensionalProbability.Appendix.Infra.PrekopaLeindler
import HighDimensionalProbability.Prelude.Matrix
import HighDimensionalProbability.Prelude.Sphere

/-!
# Euclidean isoperimetry

The old appendix allowed `r = 0`, making the theorem false for `A = ∅`.
This source-faithfulness correction uses `0 < r` and the book's literal
closed existential expansion (physical PDF page 151 / printed page 143).
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise RealInnerProductSpace

namespace HDP.Chapter5

/-- **HDP Theorem 5.1.4 (Euclidean isoperimetric inequality).**

The proof derives finite-dimensional Brunn--Minkowski from the tensorized
Prékopa--Leindler theorem in `Appendix.Infra.PrekopaLeindler`, then applies the
usual equal-volume dilation argument.
-/
theorem euclidean_isoperimetric {n : ℕ} [NeZero n]
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (hmass : volume A = volume
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)) :
    volume (HDP.Appendix.closedExpansion ε
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)) ≤
      volume (HDP.Appendix.closedExpansion ε A) := by
  let E := EuclideanSpace ℝ (Fin n)
  let R : ℝ := r + ε
  let p : ℝ := ε / R
  let q : ℝ := R / r
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hp0 : 0 < p := by
    dsimp [p]
    positivity
  have hp1 : p < 1 := by
    dsimp [p, R]
    rw [div_lt_one hR]
    linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos hR hr
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hqA : MeasurableSet (q • A : Set E) :=
    hA.const_smul_of_ne_zero hqne
  have hcomb : ∀ x ∈ (q • A : Set E),
      ∀ y ∈ Metric.ball (0 : E) R,
        (1 - p) • x + p • y ∈ Metric.thickening ε A := by
    intro x hx y hy
    rcases hx with ⟨a, ha, rfl⟩
    rw [Metric.mem_thickening_iff]
    refine ⟨a, ha, ?_⟩
    rw [dist_eq_norm]
    have hqp : (1 - p) * q = 1 := by
      dsimp [p, q, R]
      field_simp [ne_of_gt hr, ne_of_gt hR]
      ring
    have hpR : p * R = ε := by
      dsimp [p]
      field_simp [ne_of_gt hR]
    rw [smul_smul, hqp, one_smul, add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp0]
    have hy' : ‖y‖ < R := by
      simpa [mem_ball, dist_eq_norm] using hy
    calc
      p * ‖y‖ < p * R := mul_lt_mul_of_pos_left hy' hp0
      _ = ε := hpR
  have hBM :=
    HDP.Appendix.PrekopaLeindler.measure_rpow_mul_measure_rpow_le
      (HDP.Appendix.prekopaLeindler_euclideanSpace n)
      hqA measurableSet_ball Metric.isOpen_thickening.measurableSet
      p hp0 hp1 hcomb
  have hqBall :
      q • Metric.closedBall (0 : E) r =
        Metric.closedBall (0 : E) R := by
    rw [smul_closedBall (q : ℝ) (0 : E) hr.le]
    simp only [smul_zero, Real.norm_eq_abs, abs_of_nonneg hq0]
    congr 1
    dsimp [q, R]
    field_simp [ne_of_gt hr]
  have hqvol :
      volume (q • A : Set E) = volume (Metric.ball (0 : E) R) := by
    calc
      volume (q • A : Set E) =
          ENNReal.ofReal (q ^ Module.finrank ℝ E) * volume A := by
            exact Measure.addHaar_smul_of_nonneg volume hq0 A
      _ = ENNReal.ofReal (q ^ Module.finrank ℝ E) *
          volume (Metric.closedBall (0 : E) r) := by rw [hmass]
      _ = volume (q • Metric.closedBall (0 : E) r) := by
          rw [Measure.addHaar_smul_of_nonneg volume hq0]
      _ = volume (Metric.closedBall (0 : E) R) := by rw [hqBall]
      _ = volume (Metric.ball (0 : E) R) :=
        Measure.addHaar_closedBall_eq_addHaar_ball volume 0 R
  rw [hqvol] at hBM
  have hpnonneg : 0 ≤ p := hp0.le
  have h1pnonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  rw [← ENNReal.rpow_add_of_nonneg (1 - p) p h1pnonneg hpnonneg] at hBM
  have hsum : (1 - p) + p = 1 := by ring
  rw [hsum, ENNReal.rpow_one] at hBM
  have hopen_closed :
      volume (Metric.thickening ε A) ≤
        volume (HDP.Appendix.closedExpansion ε A) := by
    apply measure_mono
    intro x hx
    rw [Metric.mem_thickening_iff] at hx
    rcases hx with ⟨y, hyA, hxy⟩
    exact ⟨y, hyA, hxy.le⟩
  calc
    volume (HDP.Appendix.closedExpansion ε
        (Metric.closedBall (0 : E) r)) =
        volume (Metric.closedBall (0 : E) R) := by
          rw [HDP.Appendix.closedExpansion_eq_cthickening
            isClosed_closedBall hε.le,
            cthickening_closedBall hε.le hr.le]
          simp [R, add_comm]
    _ = volume (Metric.ball (0 : E) R) :=
      Measure.addHaar_closedBall_eq_addHaar_ball volume 0 R
    _ ≤ volume (Metric.thickening ε A) := hBM
    _ ≤ volume (HDP.Appendix.closedExpansion ε A) := hopen_closed

end HDP.Chapter5
