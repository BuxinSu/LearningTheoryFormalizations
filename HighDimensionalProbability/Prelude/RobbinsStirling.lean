import Mathlib

/-!
# Robbins' exact global Stirling bounds

This module supplies the sharp nonasymptotic two-sided endpoint quoted in the
notes following Chapter 1: for every positive `n`, the Stirling main term is
multiplied by factors between `exp (1 / (12n + 1))` and `exp (1 / (12n))`.
-/

open Filter Topology

namespace HDP.Chapter1

open Real

/-- The upper logarithmic Robbins remainder bound for the normalized Stirling
sequence.

**Lean implementation helper.** -/
theorem log_stirlingSeq_robbins_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) ≤
      Real.log (Real.sqrt Real.pi) + 1 / (12 * (n : ℝ)) := by
  have hfinite : ∀ k : ℕ,
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + k)) ≤
        1 / (12 * (n : ℝ)) - 1 / (12 * ((n + k : ℕ) : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := Stirling.log_stirlingSeq_sdiff_le (n + k)
      have hnk : (0 : ℝ) < (n + k : ℕ) := by positivity
      have hnks : (0 : ℝ) < (n + k + 1 : ℕ) := by positivity
      calc
        Real.log (Stirling.stirlingSeq n) -
            Real.log (Stirling.stirlingSeq (n + (k + 1)))
            = (Real.log (Stirling.stirlingSeq n) -
                Real.log (Stirling.stirlingSeq (n + k))) +
              (Real.log (Stirling.stirlingSeq (n + k)) -
                Real.log (Stirling.stirlingSeq (n + k + 1))) := by
                rw [Nat.add_assoc]
                ring
        _ ≤ (1 / (12 * (n : ℝ)) - 1 / (12 * ((n + k : ℕ) : ℝ))) +
              1 / (12 * ((n + k : ℕ) : ℝ) * ((n + k : ℕ) + 1)) := by
                gcongr
        _ = 1 / (12 * (n : ℝ)) -
              1 / (12 * ((n + (k + 1) : ℕ) : ℝ)) := by
                push_cast
                field_simp
                ring
  have hlim :
      Tendsto (fun k : ℕ =>
          Real.log (Stirling.stirlingSeq (n + k))) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    exact (Real.continuousAt_log (by positivity)).tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n))
  have hrecip :
      Tendsto (fun k : ℕ => 1 / (12 * ((n + k : ℕ) : ℝ))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_natCast_atTop_atTop.comp
      (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 12)
  have ht : Tendsto (fun k : ℕ =>
      Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + k))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq n) -
        Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun k : ℕ =>
      1 / (12 * (n : ℝ)) - 1 / (12 * ((n + k : ℕ) : ℝ))) atTop
      (𝓝 (1 / (12 * (n : ℝ)) - 0)) :=
    tendsto_const_nhds.sub hrecip
  have hbound := le_of_tendsto_of_tendsto ht hr (Eventually.of_forall hfinite)
  simpa only [sub_zero, add_comm] using (sub_le_iff_le_add.mp hbound)

/-- The one-step lower Robbins remainder bound for the normalized Stirling
sequence.

**Lean implementation helper.** -/
theorem log_stirlingSeq_sdiff_robbins_lower {n : ℕ} (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ) + 1) - 1 / (12 * ((n + 1 : ℕ) : ℝ) + 1) ≤
      Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let f : ℕ → ℝ := fun k =>
    (1 : ℝ) / (2 * (k + 1 : ℕ) + 1) *
      ((1 / (2 * ((m + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (k + 1)
  have hs : HasSum f
      (Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2))) := by
    simpa [f] using Stirling.log_stirlingSeq_sdiff_hasSum m
  have hterm : f 0 ≤
      Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2)) := by
    rw [← hs.tsum_eq]
    simpa using hs.summable.sum_le_tsum {0} (by
      intro i hi
      positivity)
  have halg :
      1 / (12 * (((m + 1 : ℕ) : ℝ)) + 1) -
          1 / (12 * (((m + 2 : ℕ) : ℝ)) + 1) ≤ f 0 := by
    dsimp [f]
    push_cast
    field_simp
    ring_nf
    nlinarith [sq_nonneg (m : ℝ)]
  simpa [Nat.add_assoc] using halg.trans hterm

/-- The lower logarithmic Robbins remainder bound for the normalized Stirling
sequence.

**Lean implementation helper.** -/
theorem log_stirlingSeq_robbins_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Real.sqrt Real.pi) + 1 / (12 * (n : ℝ) + 1) ≤
      Real.log (Stirling.stirlingSeq n) := by
  have hfinite : ∀ k : ℕ,
      1 / (12 * (n : ℝ) + 1) -
          1 / (12 * ((n + k : ℕ) : ℝ) + 1) ≤
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hnk : 1 ≤ n + k := hn.trans (Nat.le_add_right n k)
      have hstep := log_stirlingSeq_sdiff_robbins_lower hnk
      calc
        1 / (12 * (n : ℝ) + 1) -
            1 / (12 * ((n + (k + 1) : ℕ) : ℝ) + 1)
            = (1 / (12 * (n : ℝ) + 1) -
                1 / (12 * ((n + k : ℕ) : ℝ) + 1)) +
              (1 / (12 * ((n + k : ℕ) : ℝ) + 1) -
                1 / (12 * ((n + k + 1 : ℕ) : ℝ) + 1)) := by
                  rw [Nat.add_assoc]
                  ring
        _ ≤ (Real.log (Stirling.stirlingSeq n) -
              Real.log (Stirling.stirlingSeq (n + k))) +
            (Real.log (Stirling.stirlingSeq (n + k)) -
              Real.log (Stirling.stirlingSeq (n + k + 1))) := by
                gcongr
        _ = Real.log (Stirling.stirlingSeq n) -
              Real.log (Stirling.stirlingSeq (n + (k + 1))) := by
                rw [Nat.add_assoc]
                ring
  have hshift : Tendsto (fun k : ℕ => n + k) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat n
  have hlim :
      Tendsto (fun k : ℕ =>
          Real.log (Stirling.stirlingSeq (n + k))) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hshift)
  have hrecip :
      Tendsto (fun k : ℕ => 1 / (12 * ((n + k : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop.comp hshift).const_mul_atTop
        (by norm_num : (0 : ℝ) < 12))
  have hl : Tendsto (fun k : ℕ =>
      1 / (12 * (n : ℝ) + 1) -
        1 / (12 * ((n + k : ℕ) : ℝ) + 1)) atTop
      (𝓝 (1 / (12 * (n : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub hrecip
  have hr : Tendsto (fun k : ℕ =>
      Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + k))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq n) -
        Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hlim
  have hbound := le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hfinite)
  linarith

/-- Robbins' exact global two-sided nonasymptotic Stirling estimate.

**Book Lemma 1.7.7, following notes.** -/
theorem factorial_robbins_two_sided {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ) + 1)) ≤ (n.factorial : ℝ) ∧
      (n.factorial : ℝ) ≤
        Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ))) := by
  have hn0 : n ≠ 0 := by omega
  have hseqpos : 0 < Stirling.stirlingSeq n := by
    rcases n with _ | n
    · contradiction
    exact Stirling.stirlingSeq'_pos n
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  have hl := log_stirlingSeq_robbins_lower hn
  have hu := log_stirlingSeq_robbins_upper hn
  have hl' :
      Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ) + 1)) ≤
        Stirling.stirlingSeq n := by
    rw [← Real.exp_log hsqrt, ← Real.exp_add, ← Real.exp_log hseqpos]
    exact Real.exp_le_exp.mpr hl
  have hu' :
      Stirling.stirlingSeq n ≤
        Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ))) := by
    rw [← Real.exp_log hsqrt, ← Real.exp_add, ← Real.exp_log hseqpos]
    exact Real.exp_le_exp.mpr hu
  have hden :
      0 < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by
    positivity
  rw [Stirling.stirlingSeq] at hl' hu'
  constructor
  · rw [le_div_iff₀ hden] at hl'
    calc
      Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ) + 1))
          = (Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ) + 1))) *
              (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
              rw [show Real.sqrt (2 * Real.pi * n) =
                Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ)) by
                  rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi)]
                  congr 1
                  ring]
              ring
      _ ≤ (n.factorial : ℝ) := hl'
  · rw [div_le_iff₀ hden] at hu'
    calc
      (n.factorial : ℝ) ≤
          (Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ)))) *
            (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := hu'
      _ = Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ))) := by
            rw [show Real.sqrt (2 * Real.pi * n) =
              Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ)) by
                rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi)]
                congr 1
                ring]
            ring

end HDP.Chapter1
