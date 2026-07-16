import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries
import MatrixConcentration.Chapter5_SumOfPSDMatrices
import MatrixConcentration.Appendix_SymmetricLowerBound
import MatrixConcentration.Appendix_RosenthalPinelis

/-!
# Chapter 6: Sums of bounded random matrices

This consolidated chapter contains:

* **Book §6.6:** scalar, mgf, and cgf ingredients for matrix Bernstein;
* **Book §6.1:** Hermitian and rectangular Bernstein inequalities;
* **Book §6.2–§6.3:** random matrix sampling and sparsification;
* **Book §6.4–§6.5:** randomized matrix multiplication and random-feature bounds;
* **Book §6.1.2 and §6.7:** optimality, Rosenthal–Pinelis variants, and variance comparisons.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Scalar toolkit for the Bernstein mgf bound (Tropp §6.6.3)

The proof of the matrix Bernstein mgf bound (Lemma 6.6.2) rests on properties
of the scalar function

`f(x) = (e^{θx} − θx − 1)/x²`, `f(0) = θ²/2`,

which the source asserts with one-line justifications:

* "The function `f` is increasing because its derivative is positive."
  (hidden derivative-sign obligation; C6-36);
* the "clever application of Taylor series"
  `f(L) ≤ (θ²/2)/(1 − θL/3)` via `q! ≥ 2·3^{q−2}` (C6-36).

Writing `f(x) = θ²·H(θx)` with `H(u) = (e^u − u − 1)/u²`, `H(0) = 1/2`, this
file proves, as recovered prerequisites (classification 3):

* `bernstein_kprime_nonneg`, `bernstein_k_nonneg`, `bernstein_k_nonpos` — the
  sign analysis of `k(u) = (u−2)eᵘ + u + 2` (with `k′(u) = (u−1)eᵘ + 1`,
  `k″(u) = u eᵘ`), which controls `H′(u) = k(u)/u³`;
* `exp_quadratic_lower`/`exp_quadratic_upper` — `1 + u + u²/2 ≤ eᵘ` for
  `u ≥ 0` and the reverse for `u ≤ 0`;
* `bernsteinH_mono` — `H` is increasing on all of `ℝ` (the source's
  monotonicity claim for `f`);
* `bernsteinH_le_geom` — `H(u) ≤ (1/2)/(1 − u/3)` on `[0, 3)` (the source's
  Taylor-series estimate, proved here by a derivative argument through the
  same function `k`; mathematically equivalent, documented in the proof
  audit);
* `exp_le_one_add_bernstein_quadratic` — the combined scalar inequality
  `e^{θa} ≤ 1 + θa + (θ²/2)/(1 − θL/3)·a²` for `a ≤ L`, which is exactly
  what the Transfer Rule needs in Lemma 6.6.2.

-/

namespace MatrixConcentration

open Real

section KFunction

/-- Lean implementation helper: recovered prerequisite from **Book §6.6.3**,
`k′(u) = (u−1)eᵘ + 1 ≥ 0` for all
`u` (the inner derivative in the source's "its derivative is positive"). -/
lemma bernstein_kprime_nonneg (u : ℝ) : 0 ≤ (u - 1) * Real.exp u + 1 := by
  set κ : ℝ → ℝ := fun x => (x - 1) * Real.exp x + 1 with hκdef
  have hderiv : ∀ x : ℝ, HasDerivAt κ (x * Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y)
        (1 * Real.exp x + (x - 1) * Real.exp x) x :=
      h1.mul (Real.hasDerivAt_exp x)
    have h3 := h2.add_const 1
    have heq : 1 * Real.exp x + (x - 1) * Real.exp x = x * Real.exp x := by
      ring
    rw [heq] at h3
    exact h3
  have hκ0 : κ 0 = 0 := by
    rw [hκdef]
    norm_num
  rcases le_total 0 u with hu | hu
  · -- on `[0, u]` the derivative `x eˣ` is nonnegative
    have hmono : MonotoneOn κ (Set.Icc 0 u) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
        (fun x hx => (hderiv x).differentiableAt.differentiableWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have hx0 : 0 ≤ x := hx.1.le
      positivity
    have h := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
    rw [hκ0] at h
    exact h
  · -- on `[u, 0]` the derivative `x eˣ` is nonpositive
    have hanti : AntitoneOn κ (Set.Icc u 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc u 0)
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
        (fun x hx => (hderiv x).differentiableAt.differentiableWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have hx0 : x ≤ 0 := hx.2.le
      have hexp : 0 < Real.exp x := Real.exp_pos x
      nlinarith
    have h := hanti (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
    rw [hκ0] at h
    exact h

/-- Lean implementation helper: `HasDerivAt` for `k(u) = (u−2)eᵘ + u + 2`. -/
lemma bernstein_k_hasDeriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2)
      ((x - 1) * Real.exp x + 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 2
  have h2 : HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y)
      (1 * Real.exp x + (x - 2) * Real.exp x) x :=
    h1.mul (Real.hasDerivAt_exp x)
  have h3 := (h2.add (hasDerivAt_id x)).add_const 2
  have heq : 1 * Real.exp x + (x - 2) * Real.exp x + 1 =
      (x - 1) * Real.exp x + 1 := by
    ring
  rw [heq] at h3
  exact h3

/-- Lean implementation helper: recovered prerequisite from **Book §6.6.3**,
`k(u) = (u−2)eᵘ + u + 2 ≥ 0` for
`u ≥ 0`. -/
lemma bernstein_k_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (u - 2) * Real.exp u + u + 2 := by
  set k : ℝ → ℝ := fun y => (y - 2) * Real.exp y + y + 2 with hkdef
  have hk0 : k 0 = 0 := by
    rw [hkdef]
    norm_num
  have hmono : MonotoneOn k (Set.Icc 0 u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      (fun x _ => (bernstein_k_hasDeriv x).continuousAt.continuousWithinAt)
      (fun x hx => (bernstein_k_hasDeriv x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [(bernstein_k_hasDeriv x).deriv]
    exact bernstein_kprime_nonneg x
  have h := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  rw [hk0] at h
  exact h

/-- Lean implementation helper: recovered prerequisite from **Book §6.6.3**,
`k(u) ≤ 0` for `u ≤ 0`. -/
lemma bernstein_k_nonpos {u : ℝ} (hu : u ≤ 0) :
    (u - 2) * Real.exp u + u + 2 ≤ 0 := by
  set k : ℝ → ℝ := fun y => (y - 2) * Real.exp y + y + 2 with hkdef
  have hk0 : k 0 = 0 := by
    rw [hkdef]
    norm_num
  have hmono : MonotoneOn k (Set.Icc u 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc u 0)
      (fun x _ => (bernstein_k_hasDeriv x).continuousAt.continuousWithinAt)
      (fun x hx => (bernstein_k_hasDeriv x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [(bernstein_k_hasDeriv x).deriv]
    exact bernstein_kprime_nonneg x
  have h := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  rw [hk0] at h
  exact h

end KFunction

section QuadraticExpBounds

/-- Lean implementation helper: the quadratic lower bound
`1 + u + u²/2 ≤ eᵘ` for `u ≥ 0`. -/
lemma exp_quadratic_lower {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 2 ≤ Real.exp u := by
  set φ : ℝ → ℝ := fun x => Real.exp x - 1 - x - x ^ 2 / 2 with hφdef
  have hφ0 : φ 0 = 0 := by
    rw [hφdef]
    norm_num
  have hderiv : ∀ x : ℝ, HasDerivAt φ (Real.exp x - 1 - x) x := by
    intro x
    have h1 := ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have h3 := (hasDerivAt_pow 2 x).div_const 2
      have heq : (2 : ℕ) * x ^ (2 - 1) / 2 = x := by
        push_cast
        ring
      rwa [heq] at h3
    have h4 := h1.sub h2
    exact h4
  have hmono : MonotoneOn φ (Set.Icc 0 u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [(hderiv x).deriv]
    have h5 := Real.add_one_le_exp x
    linarith
  have h := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  rw [hφ0, hφdef] at h
  simp only at h
  linarith

/-- Lean implementation helper: the quadratic upper bound
`eᵘ ≤ 1 + u + u²/2` for `u ≤ 0`. -/
lemma exp_quadratic_upper {u : ℝ} (hu : u ≤ 0) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  set φ : ℝ → ℝ := fun x => Real.exp x - 1 - x - x ^ 2 / 2 with hφdef
  have hφ0 : φ 0 = 0 := by
    rw [hφdef]
    norm_num
  have hderiv : ∀ x : ℝ, HasDerivAt φ (Real.exp x - 1 - x) x := by
    intro x
    have h1 := ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have h3 := (hasDerivAt_pow 2 x).div_const 2
      have heq : (2 : ℕ) * x ^ (2 - 1) / 2 = x := by
        push_cast
        ring
      rwa [heq] at h3
    exact h1.sub h2
  have hmono : MonotoneOn φ (Set.Icc u 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc u 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [(hderiv x).deriv]
    have h5 := Real.add_one_le_exp x
    linarith
  have h := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  rw [hφ0, hφdef] at h
  simp only at h
  linarith

end QuadraticExpBounds

section HFunction

/-- **Book §6.6.3**, proof of **Lemma 6.6.2**: the scalar profile of the
Bernstein mgf bound; the source's
`f(x) = (e^{θx} − θx − 1)/x²` equals `θ²·bernsteinH(θx)`, where
`H(u) = (eᵘ − u − 1)/u²` with the removable value `H(0) = 1/2`.  Implicit
source declaration. -/
noncomputable def bernsteinH (u : ℝ) : ℝ :=
  if u = 0 then 1 / 2 else (Real.exp u - u - 1) / u ^ 2

/-- Lean implementation helper: the removable value of `bernsteinH` at zero. -/
lemma bernsteinH_zero : bernsteinH 0 = 1 / 2 := if_pos rfl

/-- Lean implementation helper: the quotient formula for nonzero arguments. -/
lemma bernsteinH_of_ne {u : ℝ} (hu : u ≠ 0) :
    bernsteinH u = (Real.exp u - u - 1) / u ^ 2 := if_neg hu

/-- Lean implementation helper: the defining identity
`H(u)·u² = eᵘ − u − 1` (valid for every `u`, including `u = 0`). -/
lemma bernsteinH_mul_sq (u : ℝ) :
    bernsteinH u * u ^ 2 = Real.exp u - u - 1 := by
  by_cases hu : u = 0
  · subst hu
    rw [bernsteinH_zero]
    norm_num
  · rw [bernsteinH_of_ne hu, div_mul_cancel₀]
    exact pow_ne_zero 2 hu

/-- Lean implementation helper: `H ≤ 1/2` on the nonpositive axis. -/
lemma bernsteinH_le_half {u : ℝ} (hu : u ≤ 0) : bernsteinH u ≤ 1 / 2 := by
  by_cases h0 : u = 0
  · subst h0
    rw [bernsteinH_zero]
  · have hlt : u < 0 := lt_of_le_of_ne hu h0
    rw [bernsteinH_of_ne h0, div_le_iff₀ (by positivity)]
    have h1 := exp_quadratic_upper hu
    nlinarith

/-- Lean implementation helper: `1/2 ≤ H` on the nonnegative axis. -/
lemma half_le_bernsteinH {u : ℝ} (hu : 0 ≤ u) : 1 / 2 ≤ bernsteinH u := by
  by_cases h0 : u = 0
  · subst h0
    rw [bernsteinH_zero]
  · have hlt : 0 < u := lt_of_le_of_ne hu (Ne.symm h0)
    rw [bernsteinH_of_ne h0, le_div_iff₀ (by positivity)]
    have h1 := exp_quadratic_lower hu
    nlinarith

/-- Lean implementation helper: derivative of the quotient
`q(x) = (eˣ − x − 1)/x²` away from `0`. -/
lemma bernstein_q_hasDeriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (Real.exp y - y - 1) / y ^ 2)
      (((x - 2) * Real.exp x + x + 2) / x ^ 3) x := by
  have hN : HasDerivAt (fun y : ℝ => Real.exp y - y - 1)
      (Real.exp x - 1) x := by
    have h1 := ((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).sub_const 1
    simpa using h1
  have hD : HasDerivAt (fun y : ℝ => y ^ 2) ((2 : ℕ) * x ^ (2 - 1)) x :=
    hasDerivAt_pow 2 x
  have hD' : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    have heq : ((2 : ℕ) : ℝ) * x ^ (2 - 1) = 2 * x := by
      push_cast
      ring
    rwa [heq] at hD
  have h2 := hN.div hD' (pow_ne_zero 2 hx)
  have heq : ((Real.exp x - 1) * x ^ 2 - (Real.exp x - x - 1) * (2 * x)) /
      (x ^ 2) ^ 2 = ((x - 2) * Real.exp x + x + 2) / x ^ 3 := by
    rw [show ((Real.exp x - 1) * x ^ 2 - (Real.exp x - x - 1) * (2 * x)) =
      x * (((x - 2) * Real.exp x + x + 2)) from by ring,
      show ((x ^ 2) ^ 2 : ℝ) = x * x ^ 3 from by ring]
    rw [mul_div_mul_left _ _ hx]
  rwa [heq] at h2

/-- Lean implementation helper: recovered prerequisite from **Book §6.6.3**;
the scalar profile `H` is monotone on `ℝ`, reduced to the sign of
`H′(u) = k(u)/u³`. -/
lemma bernsteinH_mono : Monotone bernsteinH := by
  intro u w huw
  rcases lt_trichotomy w 0 with hw | hw | hw
  · -- `u ≤ w < 0`: monotone on the negative axis
    have hu : u < 0 := lt_of_le_of_lt huw hw
    have hmono : MonotoneOn (fun y : ℝ => (Real.exp y - y - 1) / y ^ 2)
        (Set.Icc u w) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc u w)
        (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
      · have hx0 : x ≠ 0 := by
          rcases hx with ⟨_, hx2⟩
          exact ne_of_lt (lt_of_le_of_lt hx2 hw)
        exact (bernstein_q_hasDeriv hx0).continuousAt.continuousWithinAt
      · rw [interior_Icc] at hx
        have hx0 : x ≠ 0 := ne_of_lt (lt_trans hx.2 hw)
        exact (bernstein_q_hasDeriv hx0).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hx
        have hxneg : x < 0 := lt_trans hx.2 hw
        rw [(bernstein_q_hasDeriv (ne_of_lt hxneg)).deriv]
        have hk := bernstein_k_nonpos hxneg.le
        have hx3 : x ^ 3 < 0 := by
          have h7 : x ^ 3 = x * x ^ 2 := by ring
          have h8 : 0 < x ^ 2 := pow_two_pos_of_ne_zero (ne_of_lt hxneg)
          nlinarith
        have h9 : 0 ≤ (-((x - 2) * Real.exp x + x + 2)) / (-(x ^ 3)) :=
          div_nonneg (by linarith) (by linarith)
        rwa [neg_div_neg_eq] at h9
    have h := hmono (Set.left_mem_Icc.mpr huw) (Set.right_mem_Icc.mpr huw) huw
    rwa [bernsteinH_of_ne (ne_of_lt hu), bernsteinH_of_ne (ne_of_lt hw)]
  · -- `w = 0`
    subst hw
    rw [bernsteinH_zero]
    exact bernsteinH_le_half huw
  · rcases le_or_gt u 0 with hu | hu
    · -- `u ≤ 0 < w`
      exact (bernsteinH_le_half hu).trans (half_le_bernsteinH hw.le)
    · -- `0 < u ≤ w`: monotone on the positive axis
      have hmono : MonotoneOn (fun y : ℝ => (Real.exp y - y - 1) / y ^ 2)
          (Set.Icc u w) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc u w)
          (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
        · have hx0 : x ≠ 0 := by
            rcases hx with ⟨hx1, _⟩
            exact ne_of_gt (lt_of_lt_of_le hu hx1)
          exact (bernstein_q_hasDeriv hx0).continuousAt.continuousWithinAt
        · rw [interior_Icc] at hx
          have hx0 : x ≠ 0 := ne_of_gt (lt_trans hu hx.1)
          exact (bernstein_q_hasDeriv hx0).differentiableAt.differentiableWithinAt
        · rw [interior_Icc] at hx
          have hxpos : 0 < x := lt_trans hu hx.1
          rw [(bernstein_q_hasDeriv (ne_of_gt hxpos)).deriv]
          have hk := bernstein_k_nonneg hxpos.le
          have hx3 : (0 : ℝ) < x ^ 3 := by positivity
          exact div_nonneg hk hx3.le
      have h := hmono (Set.left_mem_Icc.mpr huw) (Set.right_mem_Icc.mpr huw)
        huw
      rwa [bernsteinH_of_ne (ne_of_gt hu), bernsteinH_of_ne (ne_of_gt hw)]

/-- Lean implementation helper: recovered prerequisite from **Book §6.6.3**;
`H(u) ≤ (1/2)/(1 − u/3)` for `0 ≤ u < 3`, via the auxiliary function
`ψ(v) = (1 − v/3)(eᵛ − v − 1) − v²/2`. -/
lemma bernsteinH_le_geom {u : ℝ} (hu : 0 ≤ u) (hu3 : u < 3) :
    bernsteinH u ≤ (1 / 2) / (1 - u / 3) := by
  have hden : 0 < 1 - u / 3 := by linarith
  -- the auxiliary function ψ
  set ψ : ℝ → ℝ := fun v => (1 - v / 3) * (Real.exp v - v - 1) - v ^ 2 / 2
    with hψdef
  have hψ0 : ψ 0 = 0 := by
    rw [hψdef]
    norm_num
  have hderiv : ∀ x : ℝ, HasDerivAt ψ
      (-(((x - 2) * Real.exp x + x + 2)) / 3) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 - y / 3) (-(1 / 3)) x := by
      have := ((hasDerivAt_id x).div_const 3).const_sub 1
      simpa using this
    have h2 : HasDerivAt (fun y : ℝ => Real.exp y - y - 1)
        (Real.exp x - 1) x := by
      have := ((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).sub_const 1
      simpa using this
    have h3 := h1.mul h2
    have h4 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have h5 := (hasDerivAt_pow 2 x).div_const 2
      have heq : ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 2 = x := by
        push_cast
        ring
      rwa [heq] at h5
    have h6 := h3.sub h4
    have heq : -(1 / 3) * (Real.exp x - x - 1) +
        (1 - x / 3) * (Real.exp x - 1) - x =
        -(((x - 2) * Real.exp x + x + 2)) / 3 := by
      ring
    rwa [heq] at h6
  have hanti : AntitoneOn ψ (Set.Icc 0 u) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 u)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv]
    have hk := bernstein_k_nonneg hx.1.le
    linarith
  have hψu : ψ u ≤ 0 := by
    have h := hanti (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
    rwa [hψ0] at h
  -- unfold ψ and rearrange
  rw [hψdef] at hψu
  simp only at hψu
  by_cases h0 : u = 0
  · subst h0
    rw [bernsteinH_zero]
    norm_num
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm h0)
    rw [bernsteinH_of_ne h0, div_le_div_iff₀ (by positivity) hden]
    nlinarith

/-- **Book §6.6.3**, proof of **Lemma 6.6.2**: for `θ > 0`,
`a ≤ L`, `0 ≤ L` and `θL < 3`,

`e^{θa} ≤ 1 + θa + (θ²/2)/(1 − θL/3) · a²`.

This is the pointwise form of the source's chain (6.6.5)–(6.6.6) together
with the Taylor estimate for `f(L)`; the Transfer Rule turns it into the
matrix mgf bound.  Implicit source declaration. -/
theorem exp_le_one_add_bernstein_quadratic {θ a L : ℝ} (hθ : 0 < θ)
    (ha : a ≤ L) (hL : 0 ≤ L) (hθL : θ * L < 3) :
    Real.exp (θ * a) ≤ 1 + θ * a + (θ ^ 2 / 2 / (1 - θ * L / 3)) * a ^ 2 := by
  have h1 : Real.exp (θ * a) - θ * a - 1 = bernsteinH (θ * a) * (θ * a) ^ 2 :=
    (bernsteinH_mul_sq _).symm
  have h2 : bernsteinH (θ * a) ≤ bernsteinH (θ * L) :=
    bernsteinH_mono (by nlinarith)
  have h3 : bernsteinH (θ * L) ≤ (1 / 2) / (1 - θ * L / 3) :=
    bernsteinH_le_geom (by positivity) hθL
  have h4 : (0 : ℝ) ≤ (θ * a) ^ 2 := sq_nonneg _
  have h5 : bernsteinH (θ * a) * (θ * a) ^ 2 ≤
      ((1 / 2) / (1 - θ * L / 3)) * (θ * a) ^ 2 :=
    mul_le_mul_of_nonneg_right (h2.trans h3) h4
  have h6 : ((1 / 2) / (1 - θ * L / 3)) * (θ * a) ^ 2 =
      (θ ^ 2 / 2 / (1 - θ * L / 3)) * a ^ 2 := by
    ring
  linarith [h1, h5, h6.le, h6.ge]

end HFunction

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The Bernstein mgf and cgf bound: Lemma 6.6.2 (Tropp §6.6.3)

**Lemma 6.6.2 (Matrix Bernstein: Mgf and Cgf Bound)**: for a random Hermitian
matrix `X` with `𝔼X = 0` and `λ_max(X) ≤ L`, and `0 < θ < 3/L`,

`𝔼 e^{θX} ≼ exp(g(θ)·𝔼X²)` and `log 𝔼 e^{θX} ≼ g(θ)·𝔼X²`,

where `g(θ) = (θ²/2)/(1 − θL/3)`.

* `gBernstein` — the coefficient `g(θ)`;
* `cfc_quadratic` — evaluation of a quadratic polynomial under the standard
  matrix function calculus.  The source proof expands
  `e^{θX} = I + θX + X·f(X)·X` (6.6.4) and inserts `f(X) ≼ f(L)·I` by the
  Conjugation Rule (6.6.5); in Lean the same pointwise semidefinite bound
  `e^{θX} ≼ I + θX + g(θ)X²` is obtained in one Transfer-Rule step from the
  combined scalar inequality `exp_le_one_add_bernstein_quadratic`;
* `bernstein_matrix_mgf_le`, `bernstein_matrix_cgf_le` — Lemma 6.6.2.

The θ-range is rendered as `0 < θ` and `θ·L < 3` (equivalent to the book's
`0 < θ < 3/L` for `L > 0`, and meaningful also for `L = 0` where the book's
`3/L` is undefined).  The standing Chapter-3 regularity convention (bounded
random matrices) is carried as the explicit hypothesis `‖X ω‖ ≤ R`; the sign
condition `0 ≤ L` is *derived* (`bernstein_L_nonneg`), not assumed: `𝔼X = 0`
and `λ_max(X) ≤ L` force it.

-/

namespace MatrixConcentration

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable [IsProbabilityMeasure μ]

section CfcQuadratic

variable {A : Matrix n n ℂ}

/-- Lean implementation helper: `A² = cfc (x ↦ x²) A` for Hermitian `A`. -/
lemma sq_eq_cfc (hA : A.IsHermitian) :
    A * A = cfc (fun x : ℝ => x * x) A := by
  rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A, cfc_id' ℝ A]

/-- Lean implementation helper: a Hermitian square is Hermitian. -/
lemma isHermitian_sq (hA : A.IsHermitian) : (A * A).IsHermitian := by
  have h : (A * A)ᴴ = A * A := by
    rw [Matrix.conjTranspose_mul, hA.eq]
  exact h

/-- Lean implementation helper: evaluation of a quadratic polynomial under the
standard matrix function calculus:
`cfc (x ↦ a + s·x + γ·x²) A = a•I + s•A + γ•A²`. -/
lemma cfc_quadratic (hA : A.IsHermitian) (a s γ : ℝ) :
    cfc (fun x : ℝ => a + s * x + γ * (x * x)) A =
      a • (1 : Matrix n n ℂ) + s • A + γ • (A * A) := by
  have h1 : cfc (fun x : ℝ => a + s * x + γ * (x * x)) A =
      cfc (fun x : ℝ => a + s * x) A + cfc (fun x : ℝ => γ * (x * x)) A :=
    cfc_add A _ _
  have h2 : cfc (fun x : ℝ => γ * (x * x)) A =
      γ • cfc (fun x : ℝ => x * x) A :=
    cfc_const_mul γ (fun x : ℝ => x * x) A
  rw [h1, h2, cfc_affine hA a s, ← sq_eq_cfc hA]

end CfcQuadratic

section MgfCgfBound

variable [Nonempty n]
variable {X : Ω → Matrix n n ℂ} {L R : ℝ}

/-- **Book Lemma 6.6.2**: the coefficient `g(θ) = (θ²/2)/(1 − θL/3)` (§6.6.3).
Explicit source declaration (the displayed function of the lemma). -/
noncomputable def gBernstein (θ L : ℝ) : ℝ := (θ ^ 2 / 2) / (1 - θ * L / 3)

/-- Lean implementation helper: nonnegativity of the Bernstein coefficient. -/
lemma gBernstein_nonneg {θ L : ℝ} (hθL : θ * L < 3) : 0 ≤ gBernstein θ L := by
  rw [gBernstein]
  have h1 : 0 < 1 - θ * L / 3 := by linarith
  positivity

/-- Lean implementation helper: entrywise integrability from a norm bound. -/
lemma mintegrable_of_norm_bound (hXm : Measurable X)
    (hbd : ∀ ω, ‖X ω‖ ≤ R) : MIntegrable X μ := by
  refine MIntegrable.of_bound hXm R (Filter.Eventually.of_forall fun ω i j => ?_)
  exact (norm_entry_le_l2_opNorm _ _ _).trans (hbd ω)

/-- Lean implementation helper: measurability of `ω ↦ X(ω)²`. -/
lemma measurable_matrix_sq (hXm : Measurable X) :
    Measurable fun ω => X ω * X ω := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => (X ω * X ω) i j) = fun ω => ∑ k, X ω i k * X ω k j := by
    funext ω
    exact Matrix.mul_apply
  rw [h]
  exact Finset.measurable_sum _ fun k _ => Measurable.mul
    ((measurable_entry i k).comp hXm) ((measurable_entry k j).comp hXm)

/-- Lean implementation helper: entrywise integrability of `X²` from a norm
bound on `X`. -/
lemma mintegrable_sq_of_norm_bound (hXm : Measurable X)
    (hbd : ∀ ω, ‖X ω‖ ≤ R) : MIntegrable (fun ω => X ω * X ω) μ := by
  refine MIntegrable.of_bound (measurable_matrix_sq hXm) (R * R)
    (Filter.Eventually.of_forall fun ω i j => ?_)
  calc ‖(X ω * X ω) i j‖ ≤ ‖X ω * X ω‖ := norm_entry_le_l2_opNorm _ _ _
  _ ≤ ‖X ω‖ * ‖X ω‖ := Matrix.l2_opNorm_mul _ _
  _ ≤ R * R := by
      have h0 : 0 ≤ ‖X ω‖ := norm_nonneg _
      have h1 := hbd ω
      nlinarith

/-- Lean implementation helper: `𝔼X = 0` and `λ_max(X) ≤ L` force `0 ≤ L`
(the book's implicit sign convention for the uniform upper bound). -/
lemma bernstein_L_nonneg (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hbd : ∀ ω, ‖X ω‖ ≤ R) (hcent : expectation μ X = 0)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L) : 0 ≤ L := by
  have hEherm : (expectation μ X).IsHermitian :=
    isHermitian_expectation (Filter.Eventually.of_forall hherm)
  have h0 : lambdaMax hEherm ≤ ∫ ω, lambdaMax (hherm ω) ∂μ :=
    lambdaMax_expectation_le (mintegrable_of_norm_bound hXm hbd) hherm hEherm
      (integrable_lambdaMax hXm hherm hbd)
  have h1 : lambdaMax hEherm = 0 := by
    rw [lambdaMax_congr hcent hEherm Matrix.isHermitian_zero]
    exact lambdaMax_zero_matrix _
  have h3 : ∫ ω, lambdaMax (hherm ω) ∂μ ≤ L := by
    have h4 : ∫ ω, lambdaMax (hherm ω) ∂μ ≤ ∫ _ : Ω, L ∂μ :=
      integral_mono (integrable_lambdaMax hXm hherm hbd) (integrable_const L)
        fun ω => hmax ω
    rwa [integral_const, probReal_univ, one_smul] at h4
  linarith

/-- Lean implementation helper: the expectation of the quadratic image,
`𝔼(I + s•X + γ•X²) = I + s•𝔼X + γ•𝔼X²`. -/
lemma expectation_one_add_smul_add_smul_sq (hX : MIntegrable X μ)
    (hX2 : MIntegrable (fun ω => X ω * X ω) μ) (s γ : ℝ) :
    expectation μ (fun ω => (1 : Matrix n n ℂ) + s • X ω + γ • (X ω * X ω)) =
      1 + s • expectation μ X + γ • expectation μ (fun ω => X ω * X ω) := by
  ext i j
  rw [expectation_apply]
  have h1 : (fun ω => ((1 : Matrix n n ℂ) + s • X ω + γ • (X ω * X ω)) i j) =
      fun ω => ((1 : Matrix n n ℂ) i j + s • X ω i j) +
        γ • (X ω * X ω) i j := by
    funext ω
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
  have h2 : Integrable (fun ω => s • X ω i j) μ := (hX i j).smul s
  have h3 : Integrable (fun ω => γ • (X ω * X ω) i j) μ := (hX2 i j).smul γ
  have h4 : Integrable (fun ω => (1 : Matrix n n ℂ) i j + s • X ω i j) μ :=
    (integrable_const _).add h2
  rw [h1, MeasureTheory.integral_add h4 h3,
    MeasureTheory.integral_add (integrable_const _) h2,
    MeasureTheory.integral_const, MeasureTheory.integral_smul,
    MeasureTheory.integral_smul, probReal_univ, one_smul]
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    expectation_apply, expectation_apply]

/-- **Book Lemma 6.6.2 (Matrix Bernstein: Mgf Bound)** (§6.6.3), first half:
if `𝔼X = 0` and
`λ_max(X) ≤ L`, then for `0 < θ < 3/L`

`𝔼 e^{θX} ≼ exp( (θ²/2)/(1 − θL/3) · 𝔼X² )`.

Explicit source declaration.  Faithful translation of the source proof
(quadratic expansion + Transfer Rule + expectation monotonicity + `I+A ≼ e^A`);
the standing boundedness hypothesis `‖X ω‖ ≤ R` is the Chapter-3 regularity
convention.

**Author note.** `bernstein_matrix_mgf_le_one_sided` removes that two-sided
bound, replacing it by explicit first/second-moment integrability and retaining
only the source's upper spectral-edge assumption;
`bernstein_matrix_mgf_le_one_sided_ae` also gives that assumption its
source-faithful almost-sure interpretation. -/
theorem bernstein_matrix_mgf_le
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hbd : ∀ ω, ‖X ω‖ ≤ R) (hcent : expectation μ X = 0)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    matrixMgf μ X θ ≤ NormedSpace.exp
      (gBernstein θ L • expectation μ (fun ω => X ω * X ω)) := by
  have hL : 0 ≤ L := bernstein_L_nonneg hXm hherm hbd hcent hmax
  set γ : ℝ := gBernstein θ L with hγdef
  -- pointwise transfer: `e^{θX(ω)} ≼ I + θ•X(ω) + γ•X(ω)²`
  have hpt : ∀ ω, NormedSpace.exp (θ • X ω) ≤
      1 + θ • X ω + γ • (X ω * X ω) := by
    intro ω
    have h1 : NormedSpace.exp (θ • X ω) =
        cfc (fun x : ℝ => Real.exp (θ * x)) (X ω) :=
      exp_smul_eq_cfc (hherm ω) θ
    have h2 : (1 : Matrix n n ℂ) + θ • X ω + γ • (X ω * X ω) =
        cfc (fun x : ℝ => 1 + θ * x + γ * (x * x)) (X ω) := by
      rw [cfc_quadratic (hherm ω) 1 θ γ, one_smul]
    rw [h1, h2]
    refine transfer_rule (hherm ω) (I := Set.Iic L) (fun i => ?_) fun x hx => ?_
    · exact (eigenvalues_le_lambdaMax (hherm ω) i).trans (hmax ω)
    · have h3 := exp_le_one_add_bernstein_quadratic hθ hx hL hθL
      calc Real.exp (θ * x) ≤ 1 + θ * x + (θ ^ 2 / 2 / (1 - θ * L / 3)) * x ^ 2 :=
            h3
      _ = 1 + θ * x + γ * (x * x) := by
            rw [hγdef, gBernstein]
            ring
  -- integrate the pointwise bound
  have hXint : MIntegrable X μ := mintegrable_of_norm_bound hXm hbd
  have hX2int : MIntegrable (fun ω => X ω * X ω) μ :=
    mintegrable_sq_of_norm_bound hXm hbd
  have hexpint : MIntegrable (fun ω => NormedSpace.exp (θ • X ω)) μ :=
    mintegrable_matrixExp_of_bound (μ := μ) (hXm.const_smul θ)
      (fun ω => isHermitian_real_smul (hherm ω) θ) (R := |θ| * R) (fun ω => by
        show ‖θ • X ω‖ ≤ |θ| * R
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hbd ω) (abs_nonneg θ))
  have hquadint : MIntegrable
      (fun ω => (1 : Matrix n n ℂ) + θ • X ω + γ • (X ω * X ω)) μ := by
    intro i j
    have h1 : (fun ω =>
        ((1 : Matrix n n ℂ) + θ • X ω + γ • (X ω * X ω)) i j) =
        fun ω => ((1 : Matrix n n ℂ) i j + θ • X ω i j) +
          γ • (X ω * X ω) i j := by
      funext ω
      rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.smul_apply]
    rw [h1]
    exact ((integrable_const _).add ((hXint i j).smul θ)).add
      ((hX2int i j).smul γ)
  have hmono := expectation_loewner_mono hexpint hquadint
    (Filter.Eventually.of_forall hpt)
  rw [expectation_one_add_smul_add_smul_sq hXint hX2int θ γ, hcent, smul_zero,
    add_zero] at hmono
  -- `I + γ•𝔼X² ≼ exp(γ•𝔼X²)`
  have hE2herm : (expectation μ (fun ω => X ω * X ω)).IsHermitian :=
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm ω))
  have hfinal := one_add_le_exp_matrix (isHermitian_real_smul hE2herm γ)
  exact le_trans hmono hfinal

/-- **Book Lemma 6.6.2 (Matrix Bernstein: Cgf Bound)** (§6.6.3), second half:
`log 𝔼 e^{θX} ≼ (θ²/2)/(1 − θL/3) · 𝔼X²` for `0 < θ < 3/L` — "we extract the
logarithm of the mgf bound using the fact (2.1.18) that the logarithm is
operator monotone."  Explicit source declaration.

**Author note.** See `bernstein_matrix_cgf_le_one_sided` for the corresponding
one-sided, explicitly integrable formulation, and
`bernstein_matrix_cgf_le_one_sided_ae` for its source-faithful almost-sure
counterpart. -/
theorem bernstein_matrix_cgf_le
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hbd : ∀ ω, ‖X ω‖ ≤ R) (hcent : expectation μ X = 0)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    matrixCgf μ X θ ≤
      gBernstein θ L • expectation μ (fun ω => X ω * X ω) := by
  have hmgf := bernstein_matrix_mgf_le (μ := μ) hXm hherm hbd hcent hmax hθ hθL
  have hpd : (matrixMgf μ X θ).PosDef := posDef_matrixMgf hXm hherm hbd θ
  have hE2herm : (expectation μ (fun ω => X ω * X ω)).IsHermitian :=
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm ω))
  have hgherm : (gBernstein θ L • expectation μ (fun ω => X ω * X ω)).IsHermitian :=
    isHermitian_real_smul hE2herm _
  have hpd2 : (NormedSpace.exp
      (gBernstein θ L • expectation μ (fun ω => X ω * X ω))).PosDef :=
    posDef_exp hgherm
  have hlog := log_monotone hpd hpd2 hmgf
  rwa [show CFC.log (NormedSpace.exp
      (gBernstein θ L • expectation μ (fun ω => X ω * X ω))) =
    gBernstein θ L • expectation μ (fun ω => X ω * X ω) from
    CFC.log_exp _ hgherm.isSelfAdjoint] at hlog

section OneSidedIntegrability

/-- Lean implementation helper: entrywise matrix integrability implies
integrability of the spectral norm in finite dimensions. -/
lemma integrable_l2_opNorm_of_mintegrable (hXm : Measurable X)
    (hXint : MIntegrable X μ) : Integrable (fun ω => ‖X ω‖) μ := by
  have hsumint : Integrable (fun ω => ∑ i, ∑ j, ‖X ω i j‖) μ :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => (hXint i j).norm
  refine Integrable.mono' hsumint
    (continuous_l2_opNorm.measurable.comp hXm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine (l2_opNorm_le_frobeniusNorm (X ω)).trans ?_
  have hsum0 : 0 ≤ ∑ i, ∑ j, ‖X ω i j‖ := by positivity
  have hinner : ∀ i, (∑ j, ‖X ω i j‖ ^ 2) ≤ (∑ j, ‖X ω i j‖) ^ 2 :=
    fun i => Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  have hrows : (∑ i, ∑ j, ‖X ω i j‖ ^ 2) ≤
      ∑ i, (∑ j, ‖X ω i j‖) ^ 2 :=
    Finset.sum_le_sum fun i _ => hinner i
  have houter : (∑ i, (∑ j, ‖X ω i j‖) ^ 2) ≤
      (∑ i, ∑ j, ‖X ω i j‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => by positivity)
  have hsquare : frobeniusNorm (X ω) ^ 2 ≤
      (∑ i, ∑ j, ‖X ω i j‖) ^ 2 := by
    rw [frobeniusNorm_sq]
    exact hrows.trans houter
  nlinarith [frobeniusNorm_nonneg (X ω)]

/-- Lean implementation helper: for positive `θ`, a one-sided upper spectral
edge uniformly bounds `exp (θX)` even when the opposite edge is unbounded. -/
lemma mintegrable_matrixExp_of_lambdaMax_bound
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L) {θ : ℝ} (hθ : 0 < θ) :
    MIntegrable (fun ω => NormedSpace.exp (θ • X ω)) μ := by
  refine MIntegrable.of_bound (measurable_matrixExp_comp (hXm.const_smul θ))
    (Real.exp (θ * L)) (Filter.Eventually.of_forall fun ω i j => ?_)
  calc
    ‖NormedSpace.exp (θ • X ω) i j‖ ≤ ‖NormedSpace.exp (θ • X ω)‖ :=
      norm_entry_le_l2_opNorm _ _ _
    _ = Real.exp (lambdaMax (isHermitian_real_smul (hherm ω) θ)) := by
      rw [posSemidef_l2_opNorm_eq_lambdaMax
        (posDef_exp (isHermitian_real_smul (hherm ω) θ)).posSemidef,
        lambdaMax_exp]
    _ = Real.exp (θ * lambdaMax (hherm ω)) := by
      rw [lambdaMax_smul_nonneg (hherm ω) hθ.le]
    _ ≤ Real.exp (θ * L) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hmax ω) hθ.le)

/-- Lean implementation helper: a one-sided-integrable matrix mgf is positive
definite.  Pointwise strict positivity of the exponential is integrated in
each nonzero quadratic direction. -/
theorem posDef_matrixMgf_one_sided
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L) {θ : ℝ} (hθ : 0 < θ) :
    (matrixMgf μ X θ).PosDef := by
  have hExpint : MIntegrable (fun ω => NormedSpace.exp (θ • X ω)) μ :=
    mintegrable_matrixExp_of_lambdaMax_bound hXm hherm hmax hθ
  have hEherm : (matrixMgf μ X θ).IsHermitian :=
    isHermitian_expectation (Filter.Eventually.of_forall fun ω =>
      (posDef_exp (isHermitian_real_smul (hherm ω) θ)).1)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hEherm fun u hu => ?_
  rw [star_dotProduct_mulVec_eq_rayleigh hEherm u, Complex.zero_lt_real]
  rw [rayleigh, matrixMgf_def, star_dotProduct_expectation hExpint u u]
  have hqint := integrable_star_dotProduct hExpint u u
  have hpos : 0 < ∫ ω,
      (star u ⬝ᵥ (NormedSpace.exp (θ • X ω) *ᵥ u)).re ∂μ := by
    apply integral_pos_of_ae_pos
    · exact Filter.Eventually.of_forall fun ω =>
        (posDef_exp (isHermitian_real_smul (hherm ω) θ)).re_dotProduct_pos hu
    · exact hqint.re
  have hre := integral_re hqint
  simp only [RCLike.re_to_complex] at hre
  rw [hre] at hpos
  exact hpos

/-- Lean implementation helper: centering and a one-sided upper edge force
the edge parameter to be nonnegative without any lower spectral bound. -/
lemma bernstein_L_nonneg_one_sided
    (hXint : MIntegrable X μ) (hcent : expectation μ X = 0)
    (hherm : ∀ ω, (X ω).IsHermitian)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L) : 0 ≤ L := by
  let i₀ : n := Classical.arbitrary n
  have hint : Integrable (fun ω => (X ω i₀ i₀).re) μ := (hXint i₀ i₀).re
  have hdiag : ∀ ω, (X ω i₀ i₀).re ≤ L := fun ω => by
    have hunit : l2norm (Pi.single i₀ (1 : ℂ)) = 1 := l2norm_single_one i₀
    have hle := rayleigh_le_lambdaMax_of_unit (hherm ω) hunit
    have hray : rayleigh (X ω) (Pi.single i₀ (1 : ℂ)) = (X ω i₀ i₀).re := by
      rw [rayleigh]
      congr 1
      rw [show star (Pi.single i₀ (1 : ℂ)) =
          (Pi.single i₀ (1 : ℂ) : n → ℂ) from by
        funext i
        rw [Pi.star_apply]
        by_cases hi : i = i₀
        · subst i
          simp
        · rw [Pi.single_eq_of_ne hi, star_zero], single_dotProduct, one_mul]
      rw [show (X ω *ᵥ Pi.single i₀ (1 : ℂ)) i₀ =
          (fun j => X ω i₀ j) ⬝ᵥ Pi.single i₀ (1 : ℂ) from rfl,
        dotProduct_single, mul_one]
    rw [hray] at hle
    exact hle.trans (hmax ω)
  have hmono : (∫ ω, (X ω i₀ i₀).re ∂μ) ≤ ∫ _ : Ω, L ∂μ :=
    integral_mono hint (integrable_const L) hdiag
  have hzero : ∫ ω, (X ω i₀ i₀).re ∂μ = 0 := by
    have hre : ∫ ω, (X ω i₀ i₀).re ∂μ = (∫ ω, X ω i₀ i₀ ∂μ).re :=
      integral_re (hXint i₀ i₀)
    rw [hre, show (∫ ω, X ω i₀ i₀ ∂μ) = expectation μ X i₀ i₀ from
      (expectation_apply _ _ _).symm, hcent]
    simp
  rw [hzero, integral_const, probReal_univ, one_smul] at hmono
  exact hmono

/-- **Book Lemma 6.6.2 (Matrix Bernstein: MGF Bound)** under its genuine
one-sided hypothesis.  The explicit integrability assumptions merely make
the displayed first and second moments meaningful and do not bound the
opposite spectral edge. -/
theorem bernstein_matrix_mgf_le_one_sided
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hXint : MIntegrable X μ)
    (hX2int : MIntegrable (fun ω => X ω * X ω) μ)
    (hcent : expectation μ X = 0)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    matrixMgf μ X θ ≤ NormedSpace.exp
      (gBernstein θ L • expectation μ (fun ω => X ω * X ω)) := by
  have hL : 0 ≤ L := bernstein_L_nonneg_one_sided hXint hcent hherm hmax
  set γ : ℝ := gBernstein θ L with hγdef
  have hpt : ∀ ω, NormedSpace.exp (θ • X ω) ≤
      1 + θ • X ω + γ • (X ω * X ω) := by
    intro ω
    rw [exp_smul_eq_cfc (hherm ω) θ]
    rw [show (1 : Matrix n n ℂ) + θ • X ω + γ • (X ω * X ω) =
        cfc (fun x : ℝ => 1 + θ * x + γ * (x * x)) (X ω) from by
      rw [cfc_quadratic (hherm ω) 1 θ γ, one_smul]]
    refine transfer_rule (hherm ω) (I := Set.Iic L)
      (fun i => (eigenvalues_le_lambdaMax (hherm ω) i).trans (hmax ω))
      fun x hx => ?_
    have h3 := exp_le_one_add_bernstein_quadratic hθ hx hL hθL
    calc
      Real.exp (θ * x) ≤
          1 + θ * x + (θ ^ 2 / 2 / (1 - θ * L / 3)) * x ^ 2 := h3
      _ = 1 + θ * x + γ * (x * x) := by
        rw [hγdef, gBernstein]
        ring
  have hexpint : MIntegrable (fun ω => NormedSpace.exp (θ • X ω)) μ :=
    mintegrable_matrixExp_of_lambdaMax_bound hXm hherm hmax hθ
  have hquadint : MIntegrable
      (fun ω => (1 : Matrix n n ℂ) + θ • X ω + γ • (X ω * X ω)) μ := by
    intro i j
    change Integrable (fun ω => ((1 : Matrix n n ℂ) i j + θ • X ω i j) +
      γ • (X ω * X ω) i j) μ
    exact ((integrable_const _).add ((hXint i j).smul θ)).add
      ((hX2int i j).smul γ)
  have hmono := expectation_loewner_mono hexpint hquadint
    (Filter.Eventually.of_forall hpt)
  rw [expectation_one_add_smul_add_smul_sq hXint hX2int θ γ, hcent,
    smul_zero, add_zero] at hmono
  have hE2herm : (expectation μ (fun ω => X ω * X ω)).IsHermitian :=
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm ω))
  exact hmono.trans (one_add_le_exp_matrix
    (isHermitian_real_smul hE2herm γ))

/-- **Book Lemma 6.6.2 (Matrix Bernstein: CGF Bound)** under the genuine
one-sided hypothesis. -/
theorem bernstein_matrix_cgf_le_one_sided
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hXint : MIntegrable X μ)
    (hX2int : MIntegrable (fun ω => X ω * X ω) μ)
    (hcent : expectation μ X = 0)
    (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    matrixCgf μ X θ ≤
      gBernstein θ L • expectation μ (fun ω => X ω * X ω) := by
  have hmgf := bernstein_matrix_mgf_le_one_sided hXm hherm hXint hX2int
    hcent hmax hθ hθL
  have hpd : (matrixMgf μ X θ).PosDef :=
    posDef_matrixMgf_one_sided hXm hherm hmax hθ
  have hE2herm : (expectation μ (fun ω => X ω * X ω)).IsHermitian :=
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm ω))
  have hgherm := isHermitian_real_smul hE2herm (gBernstein θ L)
  have hpd2 := posDef_exp hgherm
  have hlog := log_monotone hpd hpd2 hmgf
  rwa [show CFC.log (NormedSpace.exp
      (gBernstein θ L • expectation μ (fun ω => X ω * X ω))) =
    gBernstein θ L • expectation μ (fun ω => X ω * X ω) from
    CFC.log_exp _ hgherm.isSelfAdjoint] at hlog

end OneSidedIntegrability

end MgfCgfBound

section OneSidedPeeling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [Nonempty n]

/-- Lean implementation helper: entrywise integrability of a measurable finite
matrix-valued function implies Bochner integrability. -/
lemma integrable_matrix_of_mintegrable {Y : Ω → Matrix n n ℂ}
    (hYmeas : Measurable Y) (hYint : MIntegrable Y μ) : Integrable Y μ := by
  exact (MeasureTheory.integrable_norm_iff hYmeas.aestronglyMeasurable).mp
    (integrable_l2_opNorm_of_mintegrable hYmeas hYint)

/-- Lean implementation helper: the trace exponential is controlled by the
upper spectral edge, with no lower-edge hypothesis. -/
lemma abs_trace_exp_re_le_lambdaMax {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    |((NormedSpace.exp A).trace).re| ≤
      (Fintype.card n : ℝ) * Real.exp (lambdaMax hA) := by
  rw [abs_of_pos (trace_exp_re_pos hA)]
  have h := trace_re_le_card_mul_lambdaMax (isHermitian_exp hA)
  rwa [lambdaMax_exp hA] at h

/-- Lean implementation helper: the maximum eigenvalue of a finite Hermitian
sum is at most the sum of per-summand upper edges. -/
lemma lambdaMax_matsum_le_sum (s : Finset ι)
    {X : ι → Ω → Matrix n n ℂ}
    (hherm : ∀ k ω, (X k ω).IsHermitian) {U : ι → ℝ}
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ U k) (ω : Ω) :
    lambdaMax (isHermitian_matsum s fun k => hherm k ω) ≤ ∑ k ∈ s, U k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lambdaMax_zero_matrix]
  | @insert a s ha ih =>
      have hadd := lambdaMax_add_le (hherm a ω)
        (isHermitian_matsum s fun k => hherm k ω)
      have hsum : (∑ k ∈ insert a s, X k ω) = X a ω + ∑ k ∈ s, X k ω := by
        rw [Finset.sum_insert ha]
      rw [lambdaMax_congr hsum
        (isHermitian_matsum (insert a s) fun k => hherm k ω)
        ((hherm a ω).add (isHermitian_matsum s fun k => hherm k ω)),
        Finset.sum_insert ha]
      exact hadd.trans (add_le_add (hmax a ω) ih)

/-- Lean implementation helper: the independent peeling step when only upper
spectral edges are bounded. -/
theorem indep_peel_trace_exp_one_sided {U V : Ω → Matrix n n ℂ}
    (hUmeas : Measurable U) (hVmeas : Measurable V)
    (hUherm : ∀ ω, (U ω).IsHermitian) (hVherm : ∀ ω, (V ω).IsHermitian)
    {LU LV : ℝ} (hUmax : ∀ ω, lambdaMax (hUherm ω) ≤ LU)
    (hVmax : ∀ ω, lambdaMax (hVherm ω) ≤ LV)
    (hindep : ProbabilityTheory.IndepFun U V μ) :
    ∫ ω, ((NormedSpace.exp (U ω + V ω)).trace).re ∂μ ≤
      ∫ ω, ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re ∂μ := by
  classical
  set F : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun q => ((NormedSpace.exp (q.1 + q.2)).trace).re with hFdef
  have hFmeas : Measurable F :=
    measurable_trace_exp_re (measurable_matadd measurable_fst measurable_snd)
  have hpairmeas : Measurable fun ω => (U ω, V ω) := hUmeas.prodMk hVmeas
  have hlaw : μ.map (fun ω => (U ω, V ω)) =
      (μ.prod μ).map (Prod.map U V) := by
    rw [hindep.map_prod_eq_prod_map_map hUmeas.aemeasurable hVmeas.aemeasurable]
    exact MeasureTheory.Measure.map_prod_map μ μ hUmeas hVmeas
  have hghost : (∫ ω, F (U ω, V ω) ∂μ) =
      ∫ p, F (U p.1, V p.2) ∂(μ.prod μ) := by
    have h1 : (∫ ω, F (U ω, V ω) ∂μ) =
        ∫ q, F q ∂(μ.map fun ω => (U ω, V ω)) :=
      (integral_map hpairmeas.aemeasurable hFmeas.aestronglyMeasurable).symm
    have h2 : (∫ q, F q ∂((μ.prod μ).map (Prod.map U V))) =
        ∫ p, F (Prod.map U V p) ∂(μ.prod μ) :=
      integral_map (hUmeas.prodMap hVmeas).aemeasurable hFmeas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    rfl
  have hGmeas : Measurable fun p : Ω × Ω => F (U p.1, V p.2) :=
    hFmeas.comp ((hUmeas.comp measurable_fst).prodMk
      (hVmeas.comp measurable_snd))
  have hGint : Integrable (fun p : Ω × Ω => F (U p.1, V p.2))
      (μ.prod μ) := by
    refine Integrable.of_bound hGmeas.aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (LU + LV))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_trace_exp_re_le_lambdaMax
      ((hUherm p.1).add (hVherm p.2))).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (by positivity)
    exact (lambdaMax_add_le (hUherm p.1) (hVherm p.2)).trans
      (add_le_add (hUmax p.1) (hVmax p.2))
  have hfubini : (∫ p, F (U p.1, V p.2) ∂(μ.prod μ)) =
      ∫ ω, (∫ ω', F (U ω, V ω') ∂μ) ∂μ :=
    MeasureTheory.integral_prod _ hGint
  have hVexpint : MIntegrable (fun ω => NormedSpace.exp (V ω)) μ :=
    by simpa only [one_smul] using
      (mintegrable_matrixExp_of_lambdaMax_bound
        (μ := μ) hVmeas hVherm hVmax (θ := (1 : ℝ)) one_pos)
  have hVexpint' : Integrable (fun ω => NormedSpace.exp (V ω)) μ :=
    integrable_matrix_of_mintegrable
      (measurable_matrixExp_comp hVmeas) hVexpint
  have hVpd : (expectation μ fun ω => NormedSpace.exp (V ω)).PosDef :=
    by simpa only [matrixMgf, one_smul] using
      (posDef_matrixMgf_one_sided
        (μ := μ) hVmeas hVherm hVmax (θ := (1 : ℝ)) one_pos)
  have hinner : ∀ ω, (∫ ω', F (U ω, V ω') ∂μ) ≤
      ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re := fun ω => by
    refine expectation_trace_exp_add_le' (hUherm ω) hVmeas hVherm hVexpint' ?_ hVpd
    refine Integrable.of_bound
      (measurable_trace_exp_re
        (measurable_matadd measurable_const hVmeas)).aestronglyMeasurable
      ((Fintype.card n : ℝ) *
        Real.exp (lambdaMax (hUherm ω) + LV))
      (Filter.Eventually.of_forall fun ω' => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_trace_exp_re_le_lambdaMax
      ((hUherm ω).add (hVherm ω'))).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact (lambdaMax_add_le (hUherm ω) (hVherm ω')).trans
      (add_le_add_right (hVmax ω') _)
  have hInt1 : Integrable (fun ω => ∫ ω', F (U ω, V ω') ∂μ) μ :=
    hGint.integral_prod_left
  have hInt2 : Integrable (fun ω => ((NormedSpace.exp (U ω + CFC.log
      (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re) μ := by
    have hKherm : (CFC.log (expectation μ fun ω' =>
        NormedSpace.exp (V ω')) : Matrix n n ℂ).IsHermitian :=
      isHermitian_cfc_log _
    refine Integrable.of_bound
      (measurable_trace_exp_re
        (measurable_matadd hUmeas measurable_const)).aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (LU + lambdaMax hKherm))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_trace_exp_re_le_lambdaMax
      ((hUherm ω).add hKherm)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact (lambdaMax_add_le (hUherm ω) hKherm).trans
      (add_le_add (hUmax ω) (le_refl (lambdaMax hKherm)))
  calc
    (∫ ω, ((NormedSpace.exp (U ω + V ω)).trace).re ∂μ) =
        ∫ ω, (∫ ω', F (U ω, V ω') ∂μ) ∂μ := by rw [← hfubini, ← hghost]
    _ ≤ ∫ ω, ((NormedSpace.exp (U ω + CFC.log
          (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re ∂μ :=
      integral_mono hInt1 hInt2 hinner

/-- Lean implementation helper: the cgf subadditivity theorem under upper
spectral-edge bounds only. -/
theorem trace_exp_sum_le_aux_one_sided (s : Finset ι)
    {X : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian) {U : ι → ℝ}
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ U k)
    (hind : ProbabilityTheory.iIndepFun X μ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫ ω, ((NormedSpace.exp (H + ∑ k ∈ s, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (H + ∑ k ∈ s,
        CFC.log (expectation μ fun ω => NormedSpace.exp (X k ω)))).trace).re := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty =>
      simp only [Finset.sum_empty, add_zero]
      rw [integral_const, probReal_univ, one_smul]
  | insert a s ha ih =>
      have hUmeas : Measurable fun ω => H + ∑ k ∈ s, X k ω :=
        measurable_matadd measurable_const (measurable_matsum s hmeas)
      have hUherm : ∀ ω, (H + ∑ k ∈ s, X k ω).IsHermitian := fun ω =>
        hH.add (isHermitian_matsum s fun k => hherm k ω)
      have hUmax : ∀ ω, lambdaMax (hUherm ω) ≤
          lambdaMax hH + ∑ k ∈ s, U k := fun ω =>
        (lambdaMax_add_le hH
          (isHermitian_matsum s fun k => hherm k ω)).trans
          (add_le_add (le_refl (lambdaMax hH))
            (lambdaMax_matsum_le_sum s hherm hmax ω))
      have hVindep : ProbabilityTheory.IndepFun
          (fun ω => H + ∑ k ∈ s, X k ω) (X a) μ := by
        have h1 : ProbabilityTheory.IndepFun
            (fun ω => ∑ k ∈ s, X k ω) (X a) μ := by
          have h2 := ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem
            hind hmeas ha
          have h3 : (∑ k ∈ s, X k) = fun ω => ∑ k ∈ s, X k ω := by
            funext ω
            exact Finset.sum_apply ω s X
          rwa [h3] at h2
        exact h1.comp (φ := fun M : Matrix n n ℂ => H + M) (ψ := id)
          (measurable_matadd measurable_const measurable_id) measurable_id
      have hpeel := indep_peel_trace_exp_one_sided hUmeas (hmeas a) hUherm
        (hherm a) hUmax (hmax a) hVindep
      have hstep1 : (∫ ω, ((NormedSpace.exp
          (H + ∑ k ∈ insert a s, X k ω)).trace).re ∂μ) =
          ∫ ω, ((NormedSpace.exp
            ((H + ∑ k ∈ s, X k ω) + X a ω)).trace).re ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        apply congrArg (fun A : Matrix n n ℂ => ((NormedSpace.exp A).trace).re)
        rw [Finset.sum_insert ha]
        abel
      have hstep2 : (∫ ω, ((NormedSpace.exp ((H + ∑ k ∈ s, X k ω) +
          CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω')))).trace).re ∂μ) =
          ∫ ω, ((NormedSpace.exp ((H +
            CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω'))) +
            ∑ k ∈ s, X k ω)).trace).re ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        apply congrArg (fun A : Matrix n n ℂ => ((NormedSpace.exp A).trace).re)
        abel
      have hih := ih (H := H +
        CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω')))
        (hH.add (isHermitian_cfc_log _))
      rw [hstep1]
      refine hpeel.trans ?_
      rw [hstep2]
      refine hih.trans_eq ?_
      apply congrArg (fun A : Matrix n n ℂ => ((NormedSpace.exp A).trace).re)
      rw [Finset.sum_insert ha]
      abel

/-- **Book Lemma 3.5.1** specialized to positive parameters and random
Hermitian matrices with only upper spectral-edge bounds. -/
theorem trace_exp_sum_le_trace_exp_sum_cgf_one_sided
    {X : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian) {U : ι → ℝ}
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ U k)
    (hind : ProbabilityTheory.iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  have hmeasθ : ∀ k, Measurable fun ω => θ • X k ω := fun k =>
    (hmeas k).const_smul θ
  have hhermθ : ∀ k ω, (θ • X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hherm k ω) θ
  have hmaxθ : ∀ k ω, lambdaMax (hhermθ k ω) ≤ θ * U k := fun k ω => by
    rw [lambdaMax_smul_nonneg (hherm k ω) hθ.le]
    exact mul_le_mul_of_nonneg_left (hmax k ω) hθ.le
  have hsmulmeas : Measurable fun M : Matrix n n ℂ => θ • M := by fun_prop
  have hindθ : ProbabilityTheory.iIndepFun (fun k ω => θ • X k ω) μ :=
    hind.comp _ fun _ => hsmulmeas
  have h := trace_exp_sum_le_aux_one_sided (μ := μ) Finset.univ hmeasθ
    hhermθ hmaxθ hindθ (Matrix.isHermitian_zero (n := n))
  simpa only [zero_add, matrixCgf, matrixMgf] using h

end OneSidedPeeling

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Bernstein, Hermitian case: Theorem 6.6.1 (Tropp §6.6)

**Theorem 6.6.1 (Matrix Bernstein: Hermitian Case)**: for independent random
Hermitian `d`-dimensional matrices with `𝔼X_k = 0` and `λ_max(X_k) ≤ L`, with
`Y = ΣX_k` and `v(Y) = ‖𝔼Y²‖ = ‖Σ𝔼X_k²‖`,

* **Book (6.6.2)** `𝔼λ_max(Y) ≤ √(2v(Y)log d) + (1/3)L·log d`
  (`matrix_bernstein_herm_expectation`);
* **Book (6.6.3)** `P(λ_max(Y) ≥ t) ≤ d·exp(−t²/2/(v(Y) + Lt/3))` for `t ≥ 0`
  (`matrix_bernstein_herm_tail`);

and the §6.6.2 minimum-eigenvalue variants under `λ_min(X_k) ≥ −L̲`
(`matrix_bernstein_herm_min_expectation`, `matrix_bernstein_herm_min_tail`),
which the source obtains by "applying the expectation bound to `−Y`".

The proofs follow §6.6.4: substitute the Bernstein cgf bound (Lemma 6.6.2)
into the master inequalities (3.6.1)/(3.6.3) and optimize over
`θ ∈ (0, 3/L)`.

The matrix variance statistic is stated in the summand form `‖Σ_k 𝔼(X_k²)‖`
(the form of (6.6.1) used downstream); the display equalities with
`‖𝔼Y²‖` and the Chapter-2 `varStat` are proved in the next file.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ} {R : ι → ℝ}

section TraceBound

/-- **Book §6.6.4, first display chain** (C6-37): substituting the Bernstein
cgf bound into the trace exponential,
`tr exp(Σ_k Ξ_{X_k}(θ)) ≤ d·exp(g(θ)·v)` for `0 < θ < 3/L`, where
`v = ‖Σ_k 𝔼X_k²‖`.  Implicit source declaration (the "well-oiled track"). -/
lemma bernstein_cgf_trace_bound
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      (Fintype.card n : ℝ) * Real.exp (gBernstein θ L *
        ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖) := by
  have hg : 0 ≤ gBernstein θ L := gBernstein_nonneg hθL
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤
      gBernstein θ L • expectation μ (fun ω => X k ω * X k ω) :=
    fun k => bernstein_matrix_cgf_le (μ := μ) (hmeas k) (hherm k) (hbd k)
      (hcent k) (hmax k) hθ hθL
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gBernstein θ L • ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hE2herm : ∀ k, (expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    fun k => isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm k ω))
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hEsumHerm : (∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => hE2herm k
  have hgEHerm : (gBernstein θ L •
      ∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_real_smul hEsumHerm _
  have h1 := trace_exp_monotone hcgfHerm hgEHerm hsum_le
  refine h1.trans ?_
  have h2 := trace_re_le_card_mul_lambdaMax (isHermitian_exp hgEHerm)
  refine h2.trans ?_
  rw [lambdaMax_exp hgEHerm, lambdaMax_smul_nonneg hEsumHerm hg hgEHerm]
  have h3 : lambdaMax hEsumHerm ≤
      ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ :=
    (le_abs_self _).trans (abs_lambdaMax_le _)
  have h4 : gBernstein θ L * lambdaMax hEsumHerm ≤
      gBernstein θ L * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ :=
    mul_le_mul_of_nonneg_left h3 hg
  have h5 : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h4) h5.le

end TraceBound

section DimensionOne

/-- Lean implementation helper: in dimension `1`, `λ_max` is the real part of
the unique diagonal entry, so `𝔼λ_max(Y) = 0` for a centered sum (the
degenerate `log d = 0` branch of Theorem 6.6.1). -/
lemma integral_lambdaMax_eq_zero_of_card_one
    (hcard : Fintype.card n = 1)
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ
      = 0 := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  -- in dimension one, `λ_max = λ_min = ` the Rayleigh value at `e_{i₀}`
  have hsingle : ∀ (A : Matrix n n ℂ) (hA : A.IsHermitian),
      lambdaMax hA = (A i₀ i₀).re := by
    intro A hA
    have hminmax : lambdaMin hA = lambdaMax hA := by
      obtain ⟨imax, himax⟩ := exists_eigenvalues_eq_lambdaMax hA
      obtain ⟨imin, himin⟩ := exists_eigenvalues_eq_lambdaMin hA
      have hii : imin = imax := Fintype.card_le_one_iff.mp hcard.le imin imax
      rw [← himax, ← himin, hii]
    have hunit : l2norm (Pi.single i₀ (1 : ℂ)) = 1 := l2norm_single i₀
    have hup : rayleigh A (Pi.single i₀ (1 : ℂ)) ≤ lambdaMax hA :=
      rayleigh_le_lambdaMax_of_unit hA hunit
    have hlo : lambdaMin hA ≤ rayleigh A (Pi.single i₀ (1 : ℂ)) :=
      lambdaMin_le_rayleigh_of_unit hA hunit
    have hray : rayleigh A (Pi.single i₀ (1 : ℂ)) = (A i₀ i₀).re := by
      rw [rayleigh]
      congr 1
      have hstar : star (Pi.single i₀ (1 : ℂ)) =
          (Pi.single i₀ (1 : ℂ) : n → ℂ) := by
        funext i
        rw [Pi.star_apply]
        by_cases h : i = i₀
        · subst h
          rw [Pi.single_eq_same, star_one]
        · rw [Pi.single_eq_of_ne h, star_zero]
      rw [hstar, single_dotProduct, one_mul]
      rw [show (A *ᵥ Pi.single i₀ (1 : ℂ)) i₀ =
          (fun j => A i₀ j) ⬝ᵥ Pi.single i₀ (1 : ℂ) from rfl]
      rw [dotProduct_single, mul_one]
    rw [← hray]
    linarith
  have hfun : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω))) = fun ω => ((∑ k, X k ω) i₀ i₀).re :=
    funext fun ω => hsingle _ _
  rw [hfun]
  have hint : ∀ k, Integrable (fun ω => X k ω i₀ i₀) μ := fun k =>
    mintegrable_of_norm_bound (hmeas k) (hbd k) i₀ i₀
  have h1 : (fun ω => ((∑ k, X k ω) i₀ i₀).re) =
      fun ω => ∑ k, (X k ω i₀ i₀).re := by
    funext ω
    rw [show (∑ k, X k ω) i₀ i₀ = ∑ k, X k ω i₀ i₀ from by
      rw [Matrix.sum_apply], Complex.re_sum]
  rw [h1, MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
    (f := fun k (ω : Ω) => (X k ω i₀ i₀).re) fun k _ => (hint k).re]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h2 : ∫ ω, (X k ω i₀ i₀).re ∂μ = (∫ ω, X k ω i₀ i₀ ∂μ).re :=
    integral_re (hint k)
  rw [h2, show (∫ ω, X k ω i₀ i₀ ∂μ) = expectation μ (X k) i₀ i₀ from
    (expectation_apply _ _ _).symm, hcent k]
  simp

end DimensionOne

section MainTheorem

/-- Lean implementation helper: subadditivity of the square root. -/
lemma sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt (add_nonneg ha hb)
  have h4 := Real.sqrt_nonneg a
  have h5 := Real.sqrt_nonneg b
  have h6 := Real.sqrt_nonneg (a + b)
  nlinarith [mul_nonneg h4 h5]

/-- **Book Theorem 6.6.1, equation (6.6.2)** (Matrix Bernstein: Hermitian Case),
expectation bound:

`𝔼 λ_max(Y) ≤ √(2 v(Y) log d) + (1/3) L log d`

with `v(Y) = ‖Σ_k 𝔼X_k²‖`.  Explicit source declaration; §6.6.4 proof (master
bound (3.6.1) + Lemma 6.6.2 + optimization over `θ ∈ (0, 3/L)`); the standing
`0 ≤ L` is the book's implicit sign convention.

**Author note.** Lean carries the additional pointwise norm bound
`‖X_k ω‖ ≤ R k` as an explicit integrability regularity hypothesis.
`matrix_bernstein_herm_expectation_one_sided_ae` is the source-faithful sibling
with explicit moments and an almost-sure one-sided edge. -/
theorem matrix_bernstein_herm_expectation
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      Real.sqrt (2 * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ *
        Real.log (Fintype.card n)) +
      L / 3 * Real.log (Fintype.card n) := by
  classical
  set v : ℝ := ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ with hvdef
  have hv0 : 0 ≤ v := norm_nonneg _
  set D : ℝ := Real.log (Fintype.card n) with hDdef
  have hD0 : 0 ≤ D := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  rcases eq_or_lt_of_le hD0 with hD | hD
  · -- `log d = 0`, i.e. `d = 1`
    have hcard : Fintype.card n = 1 := by
      by_contra hne
      have h2 : 1 < Fintype.card n :=
        lt_of_le_of_ne Fintype.card_pos (Ne.symm hne)
      have h3 : 0 < D := by
        rw [hDdef]
        exact Real.log_pos (by exact_mod_cast h2)
      linarith [hD]
    rw [integral_lambdaMax_eq_zero_of_card_one hcard hmeas hherm hbd hcent,
      ← hD]
    rw [mul_zero, Real.sqrt_zero, mul_zero, add_zero]
  · -- main case `0 < log d`: ε-argument over admissible witnesses
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ : ℝ := ε ^ 2 / (2 * D) with hδdef
    have hδ0 : 0 < δ := by positivity
    set s : ℝ := Real.sqrt ((v + δ) / (2 * D)) with hsdef
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hssq : s ^ 2 = (v + δ) / (2 * D) := Real.sq_sqrt (by positivity)
    have hsl0 : 0 < s + L / 3 := by linarith
    set θ : ℝ := (s + L / 3)⁻¹ with hθdef
    have hθpos : 0 < θ := inv_pos.mpr hsl0
    have hθs : θ * (s + L / 3) = 1 := inv_mul_cancel₀ (ne_of_gt hsl0)
    have h1mθL : 1 - θ * L / 3 = θ * s := by
      have h : θ * s + θ * L / 3 = 1 := by
        rw [← hθs]
        ring
      linarith
    have hθL3 : θ * L < 3 := by
      have h2 : 0 < θ * s := mul_pos hθpos hs0
      nlinarith [h1mθL]
    -- master bound + cgf trace bound
    have h1 := master_expectation_upper (μ := μ) hmeas hherm hbd hind hθpos
    have h2 := bernstein_cgf_trace_bound (μ := μ) hmeas hherm hbd hcent hmax
      hθpos hθL3
    have hpos : 0 < ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re :=
      trace_exp_re_pos (isHermitian_matsum Finset.univ fun k =>
        isHermitian_cfc_log _)
    have h4 : Real.log ((Fintype.card n : ℝ) *
        Real.exp (gBernstein θ L * v)) = D + gBernstein θ L * v := by
      rw [Real.log_mul (by exact_mod_cast Fintype.card_pos.ne')
        (Real.exp_pos _).ne', Real.log_exp, hDdef]
    have hchain : ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ ≤ θ⁻¹ * (D + gBernstein θ L * v) := by
      refine h1.trans ?_
      have h3 : Real.log ((NormedSpace.exp
          (∑ k, matrixCgf μ (X k) θ)).trace).re ≤ D + gBernstein θ L * v :=
        (Real.log_le_log hpos h2).trans (le_of_eq h4)
      exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hθpos).le
    refine hchain.trans ?_
    -- the algebra: `θ⁻¹(D + g(θ)v) = (s + L/3)D + v/(2s) ≤ √(2vD) + (L/3)D + ε`
    have hginv : θ⁻¹ * (D + gBernstein θ L * v) =
        (s + L / 3) * D + v / (2 * s) := by
      have hg : gBernstein θ L = θ / (2 * s) := by
        rw [gBernstein, h1mθL]
        field_simp
      rw [hg, hθdef, inv_inv]
      have hθne : ((s + L / 3)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (ne_of_gt hsl0)
      field_simp
    rw [hginv]
    have h5 : v / (2 * s) ≤ D * s := by
      have h6 : v + δ = 2 * D * s ^ 2 := by
        rw [hssq]
        field_simp
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hδ0]
    have h7 : 2 * (D * s) ≤ Real.sqrt (2 * v * D) + ε := by
      have h9 : 2 * D * s = Real.sqrt (2 * D * (v + δ)) := by
        have h8 : 2 * D * (v + δ) = (2 * D * s) ^ 2 := by
          have h8a : (2 * D * s) ^ 2 = 4 * D ^ 2 * ((v + δ) / (2 * D)) := by
            rw [← hssq]
            ring
          rw [h8a]
          field_simp
          ring
        rw [h8, Real.sqrt_sq (by positivity)]
      have h10 : Real.sqrt (2 * D * (v + δ)) ≤
          Real.sqrt (2 * D * v) + Real.sqrt (2 * D * δ) := by
        rw [show 2 * D * (v + δ) = 2 * D * v + 2 * D * δ from by ring]
        exact sqrt_add_le (by positivity) (by positivity)
      have h11 : Real.sqrt (2 * D * δ) = ε := by
        rw [hδdef, show 2 * D * (ε ^ 2 / (2 * D)) = ε ^ 2 from by
          field_simp, Real.sqrt_sq hε.le]
      have h12 : Real.sqrt (2 * D * v) = Real.sqrt (2 * v * D) := by
        rw [show 2 * D * v = 2 * v * D from by ring]
      nlinarith [h9, h10, h11, h12]
    linarith [h5, h7]

/-- **Book Theorem 6.6.1, equation (6.6.3)** (Matrix Bernstein: Hermitian Case),
tail bound:

`P(λ_max(Y) ≥ t) ≤ d · exp( −t²/2 / (v(Y) + Lt/3) )` for `t ≥ 0`.

Explicit source declaration; §6.6.4 proof (master tail bound (3.6.3) + Lemma
6.6.2 + the "inspired choice" `θ = t/(v + Lt/3)`).

**Author note.** Lean carries the additional pointwise norm bound
`‖X_k ω‖ ≤ R k` as an explicit integrability regularity hypothesis.
`matrix_bernstein_herm_tail_one_sided_ae` is the source-faithful sibling with
explicit moments and an almost-sure one-sided edge. -/
theorem matrix_bernstein_herm_tail
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ + L * t / 3)) := by
  classical
  set v : ℝ := ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ with hvdef
  have hv0 : 0 ≤ v := norm_nonneg _
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [probReal_univ] at h
  have hden0 : (0 : ℝ) ≤ v + L * t / 3 := by positivity
  rcases eq_or_lt_of_le hden0 with hden | hden
  · -- degenerate denominator: the bound reads `P ≤ d·exp(0/0) = d`
    rw [← hden, div_zero, Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- `t = 0`: the bound reads `P ≤ d·exp(0) = d`
    rw [← ht0]
    rw [show (-((0 : ℝ) ^ 2) / 2 / (v + L * 0 / 3)) = 0 by norm_num,
      Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  rcases eq_or_lt_of_le hv0 with hv | hv
  · -- `v = 0 < Lt`: use `θ = 2/L`
    have hLt : 0 < L * t := by
      rw [← hv] at hden
      nlinarith [hden]
    have hLpos : 0 < L := by
      rcases mul_pos_iff.mp hLt with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    set θ : ℝ := 2 / L with hθdef
    have hθpos : 0 < θ := by positivity
    have hθL3 : θ * L < 3 := by
      rw [hθdef, div_mul_cancel₀ _ (ne_of_gt hLpos)]
      norm_num
    have h1 := master_tail_upper (μ := μ) hmeas hherm hbd hind t hθpos
    have h2 := bernstein_cgf_trace_bound (μ := μ) hmeas hherm hbd hcent hmax
      hθpos hθL3
    rw [← hvdef, ← hv, mul_zero, Real.exp_zero, mul_one] at h2
    have key : -(t ^ 2) / 2 / (v + L * t / 3) = -(3 * t) / (2 * L) := by
      rw [← hv]
      rw [show (0 : ℝ) + L * t / 3 = L * t / 3 from by ring]
      rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hfrac : -θ * t = -(4 * t) / (2 * L) := by
      rw [hθdef]
      field_simp
      ring
    calc μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
          (fun k => hherm k ω))}
        ≤ Real.exp (-θ * t) *
          ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := h1
      _ ≤ Real.exp (-θ * t) * (Fintype.card n : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) * Real.exp (-θ * t) := by ring
      _ ≤ (Fintype.card n : ℝ) *
          Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine Real.exp_le_exp.mpr ?_
          have h2L : (0 : ℝ) < 2 * L := by linarith
          rw [key, hfrac, div_le_div_iff₀ h2L h2L]
          nlinarith [mul_pos htpos hLpos]
  · -- main case `v > 0`: the inspired choice `θ = t/(v + Lt/3)`
    have hdne : (v + L * t / 3) ≠ 0 := ne_of_gt hden
    set θ : ℝ := t / (v + L * t / 3) with hθdef
    have hθpos : 0 < θ := div_pos htpos hden
    have hθL3 : θ * L < 3 := by
      rw [hθdef, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [hv, htpos, hL]
    have h1mθL : 1 - θ * L / 3 = v / (v + L * t / 3) := by
      rw [hθdef]
      field_simp
      ring
    have hexpid : gBernstein θ L * v + -θ * t =
        -(t ^ 2) / 2 / (v + L * t / 3) := by
      rw [gBernstein, h1mθL, hθdef]
      have hvne : v ≠ 0 := ne_of_gt hv
      field_simp
      ring
    have h1 := master_tail_upper (μ := μ) hmeas hherm hbd hind t hθpos
    have h2 := bernstein_cgf_trace_bound (μ := μ) hmeas hherm hbd hcent hmax
      hθpos hθL3
    rw [← hvdef] at h2
    calc μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
          (fun k => hherm k ω))}
        ≤ Real.exp (-θ * t) *
          ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := h1
      _ ≤ Real.exp (-θ * t) * ((Fintype.card n : ℝ) *
          Real.exp (gBernstein θ L * v)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) *
          Real.exp (gBernstein θ L * v + -θ * t) := by
          rw [Real.exp_add]
          ring
      _ = (Fintype.card n : ℝ) *
          Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) := by rw [hexpid]

end MainTheorem

section MinEigenvalue

variable {Lm : ℝ}

/-- Lean implementation helper: measurability of matrix negation (as a map on
matrices). -/
lemma measurable_matrix_neg_fun :
    Measurable fun M : Matrix n n ℂ => -M := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  show Measurable fun M : Matrix n n ℂ => -(M i j)
  exact (measurable_entry i j).neg

/-- **Book §6.6.2, first display** (C6-34): under `𝔼X_k = 0` and
`λ_min(X_k) ≥ −L̲`,

`𝔼 λ_min(Y) ≥ −√(2 v(Y) log d) − (1/3) L̲ log d`

— "Applying the expectation bound (6.6.2) to `−Y`". Explicit source
declaration.

**Author note.** `matrix_bernstein_herm_min_expectation_one_sided_ae` removes
the two-sided norm bound and accepts the source's almost-sure lower edge. -/
theorem matrix_bernstein_herm_min_expectation
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hminbd : ∀ k ω, -Lm ≤ lambdaMin (hherm k ω)) (hLm : 0 ≤ Lm)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    -(Real.sqrt (2 * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ *
        Real.log (Fintype.card n))) -
      Lm / 3 * Real.log (Fintype.card n) ≤
    ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  classical
  set X' : ι → Ω → Matrix n n ℂ := fun k ω => -(X k ω) with hX'def
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_matrix_neg_fun.comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω => (hherm k ω).neg
  have hbd' : ∀ k ω, ‖X' k ω‖ ≤ R k := fun k ω => by
    rw [hX'def]
    show ‖-(X k ω)‖ ≤ R k
    rw [norm_neg]
    exact hbd k ω
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    have h := expectation_neg (μ := μ) (X k)
    rw [show X' k = fun ω => -(X k ω) from rfl, h, hcent k, neg_zero]
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ Lm := fun k ω => by
    have h1 : lambdaMax ((hherm k ω).neg) = -(lambdaMin (hherm k ω)) :=
      lambdaMax_neg (hherm k ω)
    have h2 := hminbd k ω
    calc lambdaMax (hherm' k ω) = -(lambdaMin (hherm k ω)) := h1
    _ ≤ Lm := by linarith
  have hind' : ProbabilityTheory.iIndepFun X' μ :=
    hind.comp (fun _ M => -M) fun _ => measurable_matrix_neg_fun
  have hsq : (fun k => expectation μ (fun ω => X' k ω * X' k ω)) =
      fun k => expectation μ (fun ω => X k ω * X k ω) := by
    funext k
    congr 1
    funext ω
    show -(X k ω) * -(X k ω) = X k ω * X k ω
    rw [neg_mul_neg]
  have h := matrix_bernstein_herm_expectation (μ := μ) hmeas' hherm' hbd'
    hcent' hmax' hLm hind'
  rw [show (∑ k, expectation μ (fun ω => X' k ω * X' k ω)) =
      ∑ k, expectation μ (fun ω => X k ω * X k ω) from by rw [hsq]] at h
  -- `λ_max(−Y) = −λ_min(Y)`
  have hfun : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))) =
      fun ω => -(lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))) := by
    funext ω
    have hsumneg : (∑ k, X' k ω) = -(∑ k, X k ω) := by
      rw [hX'def]
      rw [show (∑ k, (fun k ω => -(X k ω)) k ω) = ∑ k, -(X k ω) from rfl,
        Finset.sum_neg_distrib]
    rw [lambdaMax_congr hsumneg (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))
      ((isHermitian_matsum Finset.univ (fun k => hherm k ω)).neg)]
    exact lambdaMax_neg (isHermitian_matsum Finset.univ (fun k => hherm k ω))
  rw [hfun, integral_neg] at h
  linarith

/-- **Book §6.6.2, second display** (C6-34): under the same hypotheses,
`P(λ_min(Y) ≤ −t) ≤ d·exp(−t²/2/(v(Y) + L̲t/3))` for `t ≥ 0`.  Explicit source
declaration.

**Author note.** `matrix_bernstein_herm_min_tail_one_sided_ae` is the
explicitly integrable, almost-sure one-sided counterpart. -/
theorem matrix_bernstein_herm_min_tail
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hminbd : ∀ k ω, -Lm ≤ lambdaMin (hherm k ω)) (hLm : 0 ≤ Lm)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ≤ -t} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ + Lm * t / 3)) := by
  classical
  set X' : ι → Ω → Matrix n n ℂ := fun k ω => -(X k ω) with hX'def
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_matrix_neg_fun.comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω => (hherm k ω).neg
  have hbd' : ∀ k ω, ‖X' k ω‖ ≤ R k := fun k ω => by
    show ‖-(X k ω)‖ ≤ R k
    rw [norm_neg]
    exact hbd k ω
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    have h := expectation_neg (μ := μ) (X k)
    rw [show X' k = fun ω => -(X k ω) from rfl, h, hcent k, neg_zero]
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ Lm := fun k ω => by
    have h1 : lambdaMax ((hherm k ω).neg) = -(lambdaMin (hherm k ω)) :=
      lambdaMax_neg (hherm k ω)
    have h2 := hminbd k ω
    calc lambdaMax (hherm' k ω) = -(lambdaMin (hherm k ω)) := h1
    _ ≤ Lm := by linarith
  have hind' : ProbabilityTheory.iIndepFun X' μ :=
    hind.comp (fun _ M => -M) fun _ => measurable_matrix_neg_fun
  have hsq : (∑ k, expectation μ (fun ω => X' k ω * X' k ω)) =
      ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext ω
    show -(X k ω) * -(X k ω) = X k ω * X k ω
    rw [neg_mul_neg]
  have h := matrix_bernstein_herm_tail (μ := μ) hmeas' hherm' hbd' hcent'
    hmax' hLm hind' ht
  rw [hsq] at h
  -- event identification: `{λ_min(Y) ≤ −t} = {t ≤ λ_max(−Y)}`
  have hset : {ω | lambdaMin (isHermitian_matsum Finset.univ
      (fun k => hherm k ω)) ≤ -t} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm' k ω))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hsumneg : (∑ k, X' k ω) = -(∑ k, X k ω) := by
      rw [show (∑ k, X' k ω) = ∑ k, -(X k ω) from rfl,
        Finset.sum_neg_distrib]
    rw [lambdaMax_congr hsumneg (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))
      ((isHermitian_matsum Finset.univ (fun k => hherm k ω)).neg),
      lambdaMax_neg (isHermitian_matsum Finset.univ (fun k => hherm k ω))]
    constructor
    · intro h1
      linarith
    · intro h1
      linarith
  rw [hset]
  exact h

end MinEigenvalue


end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Bernstein, general case: Theorem 6.1.1 (Tropp §6.1, §6.6.5)

**Theorem 6.1.1 (Matrix Bernstein)**: for independent `d₁ × d₂` random
matrices with `𝔼S_k = 0` and `‖S_k‖ ≤ L`, with `Z = ΣS_k` and
`v(Z) = max{‖Σ𝔼S_kS_k*‖, ‖Σ𝔼S_k*S_k‖}` ((6.1.1)/(6.1.2)),

* (6.1.3) `𝔼‖Z‖ ≤ √(2v(Z)log(d₁+d₂)) + (1/3)L log(d₁+d₂)`
  (`matrix_bernstein_rect_expectation`);
* (6.1.4) `P(‖Z‖ ≥ t) ≤ (d₁+d₂)·exp(−t²/2/(v(Z)+Lt/3))`
  (`matrix_bernstein_rect_tail`);

proved from the Hermitian case via the Hermitian dilation (§6.6.5).  Also:

* `variance_max_eq_of_hermitian` — §6.1.1's remark that for Hermitian
  summands the two maximands coincide (C6-03);
* the split-Bernstein estimate **Book (6.1.5)**
  (`matrix_bernstein_split_subgaussian`, `_subexponential`, C6-04);
* the uncentered corollary (`matrix_bernstein_uncentered_expectation`,
  `_tail`, C6-05) — "This result follows as an immediate corollary";
* a.e.-boundedness wrappers (`matrix_bernstein_rect_expectation_ae`,
  `_tail_ae`, C6-42) via norm truncation.

Statement conventions: `0 ≤ L` is carried explicitly (the book's implicit
sign convention for a norm bound; without it the statement fails for the
empty family); the equality of (6.1.1) with the
Chapter-2 `varStat` for centered sums is `matrix_bernstein_variance_eq`
(proved in `Chapter1/03_MatrixBernstein.lean` from the Chapter-2 additivity
laws).
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {S : ι → Ω → Matrix m n ℂ} {L : ℝ}

section DilationPlumbing

/-- Lean implementation helper: `H(0) = 0`. -/
lemma hermDilation_zero : hermDilation (0 : Matrix m n ℂ) = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [hermDilation, Matrix.fromBlocks]

/-- Lean implementation helper: the dilation commutes with finite sums
(§6.6.5: "the dilation is a real-linear map"). -/
lemma hermDilation_sum (B : ι → Matrix m n ℂ) :
    hermDilation (∑ k, B k) = ∑ k, hermDilation (B k) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hermDilation_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hermDilation_add, ih]

/-- Lean implementation helper: a finite sum of block-diagonal matrices. -/
lemma sum_fromBlocks_diag (A : ι → Matrix m m ℂ) (D : ι → Matrix n n ℂ) :
    (∑ k, Matrix.fromBlocks (A k) 0 0 (D k)) =
      Matrix.fromBlocks (∑ k, A k) 0 0 (∑ k, D k) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.sum_apply]
    show (∑ k, Matrix.fromBlocks (A k) 0 0 (D k) (Sum.inl i) (Sum.inl j)) = _
    rw [show (∑ k, Matrix.fromBlocks (A k) 0 0 (D k) (Sum.inl i) (Sum.inl j)) =
      ∑ k, A k i j from Finset.sum_congr rfl fun k _ => rfl]
    rw [show (Matrix.fromBlocks (∑ k, A k) 0 0 (∑ k, D k) (Sum.inl i)
      (Sum.inl j)) = (∑ k, A k) i j from rfl, Matrix.sum_apply]
  · rw [Matrix.sum_apply]
    show (∑ k, (0 : Matrix m n ℂ) i j) = (0 : Matrix m n ℂ) i j
    simp
  · rw [Matrix.sum_apply]
    show (∑ k, (0 : Matrix n m ℂ) i j) = (0 : Matrix n m ℂ) i j
    simp
  · rw [Matrix.sum_apply]
    show (∑ k, Matrix.fromBlocks (A k) 0 0 (D k) (Sum.inr i) (Sum.inr j)) = _
    rw [show (∑ k, Matrix.fromBlocks (A k) 0 0 (D k) (Sum.inr i) (Sum.inr j)) =
      ∑ k, D k i j from Finset.sum_congr rfl fun k _ => rfl]
    rw [show (Matrix.fromBlocks (∑ k, A k) 0 0 (∑ k, D k) (Sum.inr i)
      (Sum.inr j)) = (∑ k, D k) i j from rfl, Matrix.sum_apply]

/-- Lean implementation helper: the variance identification of §6.6.5 — the
summand second moments of the dilated family assemble into the block-diagonal
matrix of the rectangular second moments, so their norm is the rectangular
matrix variance statistic (the calculation (2.2.10) at the level of sums). -/
lemma dilation_variance_eq
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) :
    ‖∑ k, expectation μ (fun ω => hermDilation (S k ω) *
        hermDilation (S k ω))‖ =
      max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
        ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ := by
  have h1 : ∀ k, expectation μ (fun ω => hermDilation (S k ω) *
      hermDilation (S k ω)) =
      Matrix.fromBlocks (expectation μ (fun ω => S k ω * (S k ω)ᴴ)) 0 0
        (expectation μ (fun ω => (S k ω)ᴴ * S k ω)) := by
    intro k
    rw [show (fun ω => hermDilation (S k ω) * hermDilation (S k ω)) =
      fun ω => Matrix.fromBlocks (S k ω * (S k ω)ᴴ) 0 0 ((S k ω)ᴴ * S k ω)
      from funext fun ω => hermDilation_sq (S k ω)]
    exact expectation_fromBlocks_diag
  rw [Finset.sum_congr rfl fun k _ => h1 k, sum_fromBlocks_diag,
    l2_opNorm_fromBlocks_diagonal]

/-- **Book §6.1.1** (C6-03): "when the summands `S_k` are Hermitian, the two
terms in the maximum coincide."  Implicit source claim. -/
lemma variance_max_eq_of_hermitian {p : Type*} [Fintype p] [DecidableEq p]
    {W : Ω → Matrix p p ℂ} (hherm : ∀ ω, (W ω).IsHermitian) :
    expectation μ (fun ω => W ω * (W ω)ᴴ) =
      expectation μ (fun ω => (W ω)ᴴ * W ω) := by
  congr 1
  funext ω
  rw [(hherm ω).eq]

end DilationPlumbing

section RectTheorem

variable [Nonempty (m ⊕ n)]

/-- **Book Theorem 6.1.1, equation (6.1.3)** (Matrix Bernstein), expectation bound:

`𝔼‖Z‖ ≤ √(2 v(Z) log(d₁+d₂)) + (1/3) L log(d₁+d₂)`

with `v(Z) = max{‖Σ𝔼S_kS_k*‖, ‖Σ𝔼S_k*S_k‖}` ((6.1.1)/(6.1.2)).  Explicit
source declaration; §6.6.5 proof by Hermitian dilation. -/
theorem matrix_bernstein_rect_expectation
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ) :
    ∫ ω, ‖∑ k, S k ω‖ ∂μ ≤
      Real.sqrt (2 * max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ *
        Real.log (Fintype.card m + Fintype.card n)) +
      L / 3 * Real.log (Fintype.card m + Fintype.card n) := by
  classical
  set Y : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    fun k ω => hermDilation (S k ω) with hYdef
  have hYmeas : ∀ k, Measurable (Y k) := fun k =>
    measurable_hermDilation_fun.comp (hmeas k)
  have hYherm : ∀ k ω, (Y k ω).IsHermitian := fun k ω =>
    isHermitian_hermDilation (S k ω)
  have hYbd : ∀ k ω, ‖Y k ω‖ ≤ (fun _ : ι => L) k := fun k ω => by
    show ‖hermDilation (S k ω)‖ ≤ L
    rw [l2_opNorm_hermDilation]
    exact hbd k ω
  have hYcent : ∀ k, expectation μ (Y k) = 0 := fun k => by
    rw [show Y k = fun ω => hermDilation (S k ω) from rfl,
      expectation_hermDilation, hcent k, hermDilation_zero]
  have hYmax : ∀ k ω, lambdaMax (hYherm k ω) ≤ L := fun k ω =>
    ((le_abs_self _).trans (abs_lambdaMax_le _)).trans (hYbd k ω)
  have hYind : ProbabilityTheory.iIndepFun Y μ :=
    hind.comp (fun _ B => hermDilation B) fun _ => measurable_hermDilation_fun
  have h := matrix_bernstein_herm_expectation (μ := μ) hYmeas hYherm hYbd
    hYcent hYmax hL hYind
  -- identify the left-hand side: `λ_max(ΣY_k) = ‖ΣS_k‖`
  have hfun : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hYherm k ω))) = fun ω => ‖∑ k, S k ω‖ := by
    funext ω
    have hsum : (∑ k, Y k ω) = hermDilation (∑ k, S k ω) :=
      (hermDilation_sum _).symm
    rw [lambdaMax_congr hsum (isHermitian_matsum Finset.univ
      (fun k => hYherm k ω)) (isHermitian_hermDilation _)]
    exact lambdaMax_hermDilation _
  rw [hfun] at h
  -- identify the variance and the dimension
  have hvar := dilation_variance_eq (μ := μ) (S := S) (L := L) hmeas hbd
  rw [show (∑ k, expectation μ (fun ω => Y k ω * Y k ω)) =
      ∑ k, expectation μ (fun ω => hermDilation (S k ω) *
        hermDilation (S k ω)) from rfl] at h
  rw [hvar] at h
  rw [show ((Fintype.card (m ⊕ n) : ℝ)) =
      ((Fintype.card m + Fintype.card n : ℕ) : ℝ) from by
    rw [Fintype.card_sum]] at h
  rw [show (((Fintype.card m + Fintype.card n : ℕ) : ℝ)) =
      ((Fintype.card m : ℝ) + (Fintype.card n : ℝ)) from by push_cast; rfl] at h
  exact h

/-- **Book Theorem 6.1.1, equation (6.1.4)** (Matrix Bernstein), tail bound:

`P(‖Z‖ ≥ t) ≤ (d₁+d₂)·exp(−t²/2 / (v(Z) + Lt/3))` for `t ≥ 0`.

Explicit source declaration; §6.6.5 proof. -/
theorem matrix_bernstein_rect_tail
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) * Real.exp (-(t ^ 2) / 2 /
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ + L * t / 3)) := by
  classical
  set Y : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    fun k ω => hermDilation (S k ω) with hYdef
  have hYmeas : ∀ k, Measurable (Y k) := fun k =>
    measurable_hermDilation_fun.comp (hmeas k)
  have hYherm : ∀ k ω, (Y k ω).IsHermitian := fun k ω =>
    isHermitian_hermDilation (S k ω)
  have hYbd : ∀ k ω, ‖Y k ω‖ ≤ (fun _ : ι => L) k := fun k ω => by
    show ‖hermDilation (S k ω)‖ ≤ L
    rw [l2_opNorm_hermDilation]
    exact hbd k ω
  have hYcent : ∀ k, expectation μ (Y k) = 0 := fun k => by
    rw [show Y k = fun ω => hermDilation (S k ω) from rfl,
      expectation_hermDilation, hcent k, hermDilation_zero]
  have hYmax : ∀ k ω, lambdaMax (hYherm k ω) ≤ L := fun k ω =>
    ((le_abs_self _).trans (abs_lambdaMax_le _)).trans (hYbd k ω)
  have hYind : ProbabilityTheory.iIndepFun Y μ :=
    hind.comp (fun _ B => hermDilation B) fun _ => measurable_hermDilation_fun
  have h := matrix_bernstein_herm_tail (μ := μ) hYmeas hYherm hYbd hYcent
    hYmax hL hYind ht
  have hset : {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hYherm k ω))} = {ω | t ≤ ‖∑ k, S k ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hsum : (∑ k, Y k ω) = hermDilation (∑ k, S k ω) :=
      (hermDilation_sum _).symm
    rw [lambdaMax_congr hsum (isHermitian_matsum Finset.univ
      (fun k => hYherm k ω)) (isHermitian_hermDilation _),
      lambdaMax_hermDilation]
  rw [hset] at h
  have hvar := dilation_variance_eq (μ := μ) (S := S) (L := L) hmeas hbd
  rw [show (∑ k, expectation μ (fun ω => Y k ω * Y k ω)) =
      ∑ k, expectation μ (fun ω => hermDilation (S k ω) *
        hermDilation (S k ω)) from rfl, hvar] at h
  rw [show ((Fintype.card (m ⊕ n) : ℝ)) =
      ((Fintype.card m : ℝ) + Fintype.card n) from by
    rw [Fintype.card_sum]; push_cast; rfl] at h
  exact h

end RectTheorem

section SplitBernstein

variable [Nonempty (m ⊕ n)]

/-- **Book (6.1.5)**, subgaussian branch (C6-04):
for `t·L ≤ v(Z)` (the book's `t ≤ v(Z)/L`),
`P(‖Z‖ ≥ t) ≤ (d₁+d₂)·e^{−3t²/(8v(Z))}`. Explicit source display. -/
theorem matrix_bernstein_split_subgaussian
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ) {t : ℝ} (ht : 0 ≤ t)
    (htv : t * L ≤ max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
      ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(3 * t ^ 2) /
          (8 * max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
            ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖)) := by
  set v : ℝ := max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
    ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ with hvdef
  have hv0 : 0 ≤ v := le_max_of_le_left (norm_nonneg _)
  have h := matrix_bernstein_rect_tail (μ := μ) hmeas hbd hL hcent hind ht
  rw [← hvdef] at h
  refine h.trans ?_
  have hcard : (0 : ℝ) ≤ (Fintype.card m : ℝ) + Fintype.card n := by
    positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcard
  rcases eq_or_lt_of_le hv0 with hv | hv
  · -- `v = 0`: both sides are `0` by the division convention
    have htL : t * L = 0 := le_antisymm (by rw [← hv] at htv; exact htv)
      (by positivity)
    rw [← hv, mul_zero, div_zero]
    rw [show (0 : ℝ) + L * t / 3 = L * t / 3 from by ring,
      show L * t = 0 from by rw [mul_comm]; exact htL, zero_div, div_zero]
  · -- `v > 0`
    have hden : 0 < v + L * t / 3 := by positivity
    rw [div_le_div_iff₀ hden (by positivity)]
    have hLt : L * t ≤ v := by rw [mul_comm]; exact htv
    nlinarith [sq_nonneg t, hv, hLt, ht]

/-- **Book (6.1.5)**, subexponential branch
(C6-04): for `v(Z) ≤ t·L`,
`P(‖Z‖ ≥ t) ≤ (d₁+d₂)·e^{−3t/(8L)}`. Explicit source display. -/
theorem matrix_bernstein_split_subexponential
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ) {t : ℝ} (ht : 0 ≤ t)
    (hvt : max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
      ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ ≤ t * L) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(3 * t) / (8 * L)) := by
  set v : ℝ := max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
    ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ with hvdef
  have hv0 : 0 ≤ v := le_max_of_le_left (norm_nonneg _)
  have h := matrix_bernstein_rect_tail (μ := μ) hmeas hbd hL hcent hind ht
  rw [← hvdef] at h
  refine h.trans ?_
  have hcard : (0 : ℝ) ≤ (Fintype.card m : ℝ) + Fintype.card n := by
    positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcard
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- `L = 0`: then `v = 0` and both sides are `0`
    have hv00 : v = 0 := le_antisymm (by rw [← hL0, mul_zero] at hvt; exact hvt)
      hv0
    rw [hv00, ← hL0, mul_zero, div_zero]
    rw [show (0 : ℝ) + 0 * t / 3 = 0 from by ring, div_zero]
  · -- `L > 0`
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · -- `t = 0` forces `v = 0`; both sides reduce to `0`
      rw [← ht0, zero_mul] at hvt
      have hv00 : v = 0 := le_antisymm hvt hv0
      rw [hv00, ← ht0]
      norm_num
    · -- `t > 0`
      have hden : 0 < v + L * t / 3 := by positivity
      rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 8 * L)]
      nlinarith [htpos, hvt, hLpos, sq_nonneg t]

end SplitBernstein

section Uncentered

variable [Nonempty (m ⊕ n)]

/-- Lean implementation helper: expectation congruence for a.e.-equal random
matrices. -/
lemma expectation_congr_ae {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {Y Z : Ω → Matrix p q ℂ} (h : Y =ᵐ[μ] Z) :
    expectation μ Y = expectation μ Z := by
  ext i j
  rw [expectation_apply, expectation_apply]
  refine integral_congr_ae (h.mono fun ω hω => ?_)
  show Y ω i j = Z ω i j
  rw [hω]

/-- **Book Corollary 6.1.2 (Matrix Bernstein: Uncentered Summands)**,
expectation bound: under `‖S_k − 𝔼S_k‖ ≤ L`,
`𝔼‖Z − 𝔼Z‖ ≤ √(2v(Z)log(d₁+d₂)) + (1/3)L log(d₁+d₂)` with `v(Z)` computed
from the centered summands.  Explicit source declaration; the source calls it
"an immediate corollary of Theorem 6.1.1". -/
theorem matrix_bernstein_uncentered_expectation
    (hmeas : ∀ k, Measurable (S k))
    (hbd : ∀ k ω, ‖S k ω - expectation μ (S k)‖ ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun S μ) :
    ∫ ω, ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖ ∂μ ≤
      Real.sqrt (2 * max
          ‖∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k)) *
            (S k ω - expectation μ (S k))ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k))ᴴ *
            (S k ω - expectation μ (S k)))‖ *
        Real.log (Fintype.card m + Fintype.card n)) +
      L / 3 * Real.log (Fintype.card m + Fintype.card n) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ :=
    fun k ω => S k ω - expectation μ (S k) with hS'def
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    (measurable_sub_const (expectation μ (S k))).comp (hmeas k)
  have hSint : ∀ k, MIntegrable (S k) μ := fun k => by
    refine mintegrable_rect_of_norm_bound (C := L + ‖expectation μ (S k)‖)
      (hmeas k) fun ω => ?_
    calc ‖S k ω‖ = ‖(S k ω - expectation μ (S k)) + expectation μ (S k)‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖S k ω - expectation μ (S k)‖ + ‖expectation μ (S k)‖ := norm_add_le _ _
    _ ≤ L + ‖expectation μ (S k)‖ := by
          have := hbd k ω
          linarith
  have hcent' : ∀ k, expectation μ (S' k) = 0 := by
    intro k
    have hconst : MIntegrable (fun _ : Ω => expectation μ (S k)) μ :=
      mintegrable_rect_of_norm_bound (C := ‖expectation μ (S k)‖)
        measurable_const fun ω => le_refl _
    have hsub := expectation_sub (μ := μ) (hSint k) hconst
    rw [show S' k = fun ω => S k ω - (fun _ : Ω => expectation μ (S k)) ω
      from rfl, hsub, expectation_const (μ := μ), sub_self]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun k M => M - expectation μ (S k)) fun k =>
      measurable_sub_const _
  have h := matrix_bernstein_rect_expectation (μ := μ) hmeas' hbd hL hcent'
    hind'
  have hsum_eq : ∀ ω, (∑ k, S' k ω) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k) := by
    intro ω
    show (∑ k, (S k ω - expectation μ (S k))) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k)
    rw [Finset.sum_sub_distrib]
  rw [show (fun ω => ‖∑ k, S' k ω‖) =
      fun ω => ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖ from
    funext fun ω => by rw [hsum_eq ω]] at h
  exact h

/-- **Book Corollary 6.1.2 (Matrix Bernstein: Uncentered Summands)**, tail
bound: `P(‖Z − 𝔼Z‖ ≥ t) ≤ (d₁+d₂)·exp(−t²/2/(v(Z)+Lt/3))`.  Explicit source
declaration. -/
theorem matrix_bernstein_uncentered_tail
    (hmeas : ∀ k, Measurable (S k))
    (hbd : ∀ k ω, ‖S k ω - expectation μ (S k)‖ ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun S μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) * Real.exp (-(t ^ 2) / 2 /
        (max ‖∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k)) *
            (S k ω - expectation μ (S k))ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k))ᴴ *
            (S k ω - expectation μ (S k)))‖ + L * t / 3)) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ :=
    fun k ω => S k ω - expectation μ (S k) with hS'def
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    (measurable_sub_const (expectation μ (S k))).comp (hmeas k)
  have hSint : ∀ k, MIntegrable (S k) μ := fun k => by
    refine mintegrable_rect_of_norm_bound (C := L + ‖expectation μ (S k)‖)
      (hmeas k) fun ω => ?_
    calc ‖S k ω‖ = ‖(S k ω - expectation μ (S k)) + expectation μ (S k)‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖S k ω - expectation μ (S k)‖ + ‖expectation μ (S k)‖ := norm_add_le _ _
    _ ≤ L + ‖expectation μ (S k)‖ := by
          have := hbd k ω
          linarith
  have hcent' : ∀ k, expectation μ (S' k) = 0 := by
    intro k
    have hconst : MIntegrable (fun _ : Ω => expectation μ (S k)) μ :=
      mintegrable_rect_of_norm_bound (C := ‖expectation μ (S k)‖)
        measurable_const fun ω => le_refl _
    have hsub := expectation_sub (μ := μ) (hSint k) hconst
    rw [show S' k = fun ω => S k ω - (fun _ : Ω => expectation μ (S k)) ω
      from rfl, hsub, expectation_const (μ := μ), sub_self]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun k M => M - expectation μ (S k)) fun k =>
      measurable_sub_const _
  have h := matrix_bernstein_rect_tail (μ := μ) hmeas' hbd hL hcent' hind' ht
  have hsum_eq : ∀ ω, (∑ k, S' k ω) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k) := by
    intro ω
    show (∑ k, (S k ω - expectation μ (S k))) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k)
    rw [Finset.sum_sub_distrib]
  rw [show {ω | t ≤ ‖∑ k, S' k ω‖} =
      {ω | t ≤ ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖} from by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hsum_eq ω]] at h
  exact h

end Uncentered

section AeWrappers

variable [Nonempty (m ⊕ n)]

/-- Lean implementation helper (C6-42): the norm truncation used to upgrade
a.e. boundedness to pointwise boundedness. -/
noncomputable def truncateNorm (L : ℝ) (B : Matrix m n ℂ) : Matrix m n ℂ :=
  if ‖B‖ ≤ L then B else 0

/-- Lean implementation helper: measurability of norm truncation. -/
lemma measurable_truncateNorm :
    Measurable (truncateNorm (m := m) (n := n) L) := by
  have hset : MeasurableSet {B : Matrix m n ℂ | ‖B‖ ≤ L} :=
    continuous_l2_opNorm.measurable measurableSet_Iic
  exact Measurable.ite hset measurable_id measurable_const

/-- Lean implementation helper: the truncated matrix satisfies the pointwise norm bound. -/
lemma truncateNorm_norm_le (hL : 0 ≤ L) (B : Matrix m n ℂ) :
    ‖truncateNorm L B‖ ≤ L := by
  rw [truncateNorm]
  split_ifs with h
  · exact h
  · rw [norm_zero]
    exact hL

/-- Lean implementation helper: an almost-everywhere-bounded wrapper for the
expectation form of **Book Theorem 6.1.1**, obtained by norm truncation.

**Author note.** This version weakens the pointwise norm bound to an
almost-everywhere bound. -/
theorem matrix_bernstein_rect_expectation_ae
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L)
    (hL : 0 ≤ L) (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ) :
    ∫ ω, ‖∑ k, S k ω‖ ∂μ ≤
      Real.sqrt (2 * max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ *
        Real.log (Fintype.card m + Fintype.card n)) +
      L / 3 * Real.log (Fintype.card m + Fintype.card n) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ := fun k ω => truncateNorm L (S k ω)
    with hS'def
  have hae : ∀ k, S' k =ᵐ[μ] S k := fun k => (hbd k).mono fun ω h => by
    show truncateNorm L (S k ω) = S k ω
    rw [truncateNorm, if_pos h]
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    measurable_truncateNorm.comp (hmeas k)
  have hbd' : ∀ k ω, ‖S' k ω‖ ≤ L := fun k ω => truncateNorm_norm_le hL _
  have hcent' : ∀ k, expectation μ (S' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun _ => truncateNorm L) fun _ => measurable_truncateNorm
  have h := matrix_bernstein_rect_expectation (μ := μ) hmeas' hbd' hL hcent'
    hind'
  have hsum_ae : (fun ω => ∑ k, S' k ω) =ᵐ[μ] fun ω => ∑ k, S k ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ k, S' k ω = S k ω :=
      (MeasureTheory.ae_all_iff).mpr hae
    refine hall.mono fun ω h => ?_
    show (∑ k, S' k ω) = ∑ k, S k ω
    exact Finset.sum_congr rfl fun k _ => h k
  -- transfer the left-hand side
  have hlhs : ∫ ω, ‖∑ k, S' k ω‖ ∂μ = ∫ ω, ‖∑ k, S k ω‖ ∂μ := by
    refine integral_congr_ae (hsum_ae.mono fun ω h => ?_)
    have h' : (∑ k, S' k ω) = ∑ k, S k ω := h
    show ‖∑ k, S' k ω‖ = ‖∑ k, S k ω‖
    rw [h']
  rw [hlhs] at h
  -- transfer the variance terms
  have hv1 : ∀ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ) =
      expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show S' k ω * (S' k ω)ᴴ = S k ω * (S k ω)ᴴ
    rw [h']
  have hv2 : ∀ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω) =
      expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show (S' k ω)ᴴ * S' k ω = (S k ω)ᴴ * S k ω
    rw [h']
  rw [Finset.sum_congr rfl fun k _ => hv1 k,
    Finset.sum_congr rfl fun k _ => hv2 k] at h
  exact h

/-- Lean implementation helper: an almost-everywhere-bounded wrapper for the
tail form of **Book Theorem 6.1.1**, obtained by norm truncation.

**Author note.** This version weakens the pointwise norm bound to an
almost-everywhere bound. -/
theorem matrix_bernstein_rect_tail_ae
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L)
    (hL : 0 ≤ L) (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) * Real.exp (-(t ^ 2) / 2 /
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ + L * t / 3)) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ := fun k ω => truncateNorm L (S k ω)
    with hS'def
  have hae : ∀ k, S' k =ᵐ[μ] S k := fun k => (hbd k).mono fun ω h => by
    show truncateNorm L (S k ω) = S k ω
    rw [truncateNorm, if_pos h]
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    measurable_truncateNorm.comp (hmeas k)
  have hbd' : ∀ k ω, ‖S' k ω‖ ≤ L := fun k ω => truncateNorm_norm_le hL _
  have hcent' : ∀ k, expectation μ (S' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun _ => truncateNorm L) fun _ => measurable_truncateNorm
  have h := matrix_bernstein_rect_tail (μ := μ) hmeas' hbd' hL hcent' hind' ht
  have hsum_ae : (fun ω => ∑ k, S' k ω) =ᵐ[μ] fun ω => ∑ k, S k ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ k, S' k ω = S k ω :=
      (MeasureTheory.ae_all_iff).mpr hae
    refine hall.mono fun ω h => ?_
    show (∑ k, S' k ω) = ∑ k, S k ω
    exact Finset.sum_congr rfl fun k _ => h k
  have hmeq : μ {ω | t ≤ ‖∑ k, S' k ω‖} = μ {ω | t ≤ ‖∑ k, S k ω‖} := by
    refine MeasureTheory.measure_congr ?_
    refine hsum_ae.mono fun ω hω => ?_
    have h' : (∑ k, S' k ω) = ∑ k, S k ω := hω
    show (t ≤ ‖∑ k, S' k ω‖) = (t ≤ ‖∑ k, S k ω‖)
    rw [h']
  have hreal : μ.real {ω | t ≤ ‖∑ k, S' k ω‖} =
      μ.real {ω | t ≤ ‖∑ k, S k ω‖} := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, hmeq]
  rw [hreal] at h
  have hv1 : ∀ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ) =
      expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show S' k ω * (S' k ω)ᴴ = S k ω * (S k ω)ᴴ
    rw [h']
  have hv2 : ∀ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω) =
      expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show (S' k ω)ᴴ * S' k ω = (S k ω)ᴴ * S k ω
    rw [h']
  rw [Finset.sum_congr rfl fun k _ => hv1 k,
    Finset.sum_congr rfl fun k _ => hv2 k] at h
  exact h

end AeWrappers

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix approximation by random sampling: Corollary 6.2.1 (Tropp §6.2)

The empirical-approximation framework: a template random matrix `R₀` with
`𝔼R₀ = B` and `‖R₀‖ ≤ L`, and `n` independent copies averaged into the
matrix sampling estimator `R̄_n = n⁻¹ Σ R_k` (6.2.1).

* `secondMoment` — the per-sample second moment `m₂(R)`, **Book (6.2.4)**;
* **Book Corollary 6.2.1** — `matrix_sampling_estimator_expectation` **(6.2.5)**
  and `matrix_sampling_estimator_tail` **(6.2.6)**, translations of the
  source proof (center, bound `‖S_k‖ ≤ 2L/n` by triangle + Jensen, bound
  `v(Z) ≤ m₂(R)/n` by dropping the psd term `(𝔼R)(𝔼R)*`, then Theorem 6.1.1);
* `matrix_sampling_sample_cost` — **Book (6.2.7)**;
* `abs_trace_mul_le_schattenOne` and `trace_control_of_norm_le` — the §6.2.3
  discussion display "`‖R̄_n − B‖ ≤ ε` implies
  `|tr(R̄_nC) − tr(BC)| ≤ ε` when `‖C‖_{S1} ≤ 1`" (C6-16), via an SVD
  trace-duality argument.

Model conventions: "independent copies of `R`" is rendered as a family
`R : Fin n → Ω → 𝕄` with `iIndepFun R μ` and `IdentDistrib (R k) R₀ μ μ`; the
copies inherit the norm bound only almost everywhere (a law transfer), which
is why Theorem 6.1.1's a.e. wrappers are used.  This model also covers the
book's "general sampling model" of §6.2.3 (C6-18): `R₀` may have any law, not
just a finitely supported one.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [IsProbabilityMeasure μ]

section SecondMoment

/-- **Book (6.2.4)** (C6-13): the per-sample
second moment `m₂(R) = max{‖𝔼(RR*)‖, ‖𝔼(R*R)‖}`.  Explicit source
declaration. -/
noncomputable def secondMoment (μ : MeasureTheory.Measure Ω)
    (R₀ : Ω → Matrix m n ℂ) : ℝ :=
  max ‖expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ)‖
    ‖expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω)‖

/-- Lean implementation helper: nonnegativity of the second-moment statistic. -/
lemma secondMoment_nonneg (R₀ : Ω → Matrix m n ℂ) :
    0 ≤ secondMoment μ R₀ :=
  le_max_of_le_left (norm_nonneg _)

/-- Lean implementation helper: the per-sample second moment depends only on
the almost-everywhere equivalence class of the random matrix. -/
lemma secondMoment_congr_ae {R₀ R₁ : Ω → Matrix m n ℂ}
    (h : R₀ =ᵐ[μ] R₁) : secondMoment μ R₀ = secondMoment μ R₁ := by
  rw [secondMoment, secondMoment]
  apply congrArg₂ max
  · congr 1
    exact expectation_congr_ae (h.mono fun ω hω => by
      show R₀ ω * (R₀ ω)ᴴ = R₁ ω * (R₁ ω)ᴴ
      rw [hω])
  · congr 1
    exact expectation_congr_ae (h.mono fun ω hω => by
      show (R₀ ω)ᴴ * R₀ ω = (R₁ ω)ᴴ * R₁ ω
      rw [hω])

/-- Lean implementation helper: an almost-sure bound on a matrix norm over a
probability space forces the bound parameter to be nonnegative. -/
lemma nonneg_of_ae_norm_le {R₀ : Ω → Matrix m n ℂ} (hR₀m : Measurable R₀)
    (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L) : 0 ≤ L := by
  have hnormm : Measurable fun ω => ‖R₀ ω‖ :=
    continuous_l2_opNorm.measurable.comp hR₀m
  have hnormint : Integrable (fun ω => ‖R₀ ω‖) μ := by
    refine Integrable.of_bound hnormm.aestronglyMeasurable |L| ?_
    filter_upwards [hbd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hω.trans (le_abs_self L)
  have hmono : (∫ ω, ‖R₀ ω‖ ∂μ) ≤ ∫ _ : Ω, L ∂μ :=
    integral_mono_ae hnormint (integrable_const L) hbd
  rw [integral_const, probReal_univ, one_smul] at hmono
  exact (integral_nonneg fun _ => norm_nonneg _).trans hmono

/-- Lean implementation helper: `𝔼(c • Z) = c • 𝔼Z` for a real scalar. -/
lemma expectation_real_smul (c : ℝ) (Z : Ω → Matrix m n ℂ) :
    expectation μ (fun ω => c • Z ω) = c • expectation μ Z := by
  ext i j
  rw [expectation_apply, Matrix.smul_apply,
    show (fun ω => (c • Z ω) i j) = fun ω => c • Z ω i j from rfl,
    integral_smul, expectation_apply]

/-- Lean implementation helper (proof step of Cor 6.2.1): the rectangular
variance identity `𝔼[(Z−𝔼Z)(Z−𝔼Z)*] = 𝔼(ZZ*) − (𝔼Z)(𝔼Z)*`. -/
lemma matrixVar1_eq_sub {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (hZ1 : MIntegrable (fun ω => Z ω * (Z ω)ᴴ) μ) :
    matrixVar1 μ Z = expectation μ (fun ω => Z ω * (Z ω)ᴴ) -
      expectation μ Z * (expectation μ Z)ᴴ := by
  rw [matrixVar1]
  have h1 : (fun ω => (Z ω - expectation μ Z) * (Z ω - expectation μ Z)ᴴ) =
      fun ω => (Z ω * (Z ω)ᴴ - Z ω * (expectation μ Z)ᴴ -
        expectation μ Z * (Z ω)ᴴ) + expectation μ Z * (expectation μ Z)ᴴ := by
    funext ω
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub]
    abel
  rw [h1, expectation_add ((hZ1.sub (hZ.mul_const _)).sub
      (hZ.conjTranspose.const_mul _)) (MIntegrable.const _),
    expectation_sub (hZ1.sub (hZ.mul_const _)) (hZ.conjTranspose.const_mul _),
    expectation_sub hZ1 (hZ.mul_const _), expectation_mul_const hZ,
    expectation_const_mul hZ.conjTranspose, expectation_const,
    expectation_conjTranspose Z]
  abel

/-- Lean implementation helper (mirror for `Z*Z`). -/
lemma matrixVar2_eq_sub {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (hZ2 : MIntegrable (fun ω => (Z ω)ᴴ * Z ω) μ) :
    matrixVar2 μ Z = expectation μ (fun ω => (Z ω)ᴴ * Z ω) -
      (expectation μ Z)ᴴ * expectation μ Z := by
  rw [matrixVar2]
  have h1 : (fun ω => (Z ω - expectation μ Z)ᴴ * (Z ω - expectation μ Z)) =
      fun ω => ((Z ω)ᴴ * Z ω - (Z ω)ᴴ * expectation μ Z -
        (expectation μ Z)ᴴ * Z ω) + (expectation μ Z)ᴴ * expectation μ Z := by
    funext ω
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub]
    abel
  rw [h1, expectation_add ((hZ2.sub (hZ.conjTranspose.mul_const _)).sub
      (hZ.const_mul _)) (MIntegrable.const _),
    expectation_sub (hZ2.sub (hZ.conjTranspose.mul_const _)) (hZ.const_mul _),
    expectation_sub hZ2 (hZ.conjTranspose.mul_const _),
    expectation_mul_const hZ.conjTranspose, expectation_const_mul hZ,
    expectation_const, expectation_conjTranspose Z]
  abel

/-- **Book (proof of Cor 6.2.1)** (C6-14): dropping the psd term,
`𝔼[(R−𝔼R)(R−𝔼R)*] ≼ 𝔼(RR*)` — "The last relation holds because
`(𝔼R)(𝔼R)*` is positive semidefinite."  Implicit source claim. -/
lemma centered_second_moment_le {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (hZ1 : MIntegrable (fun ω => Z ω * (Z ω)ᴴ) μ) :
    matrixVar1 μ Z ≤ expectation μ (fun ω => Z ω * (Z ω)ᴴ) := by
  rw [matrixVar1_eq_sub hZ hZ1]
  have hpsd : (0 : Matrix m m ℂ) ≤
      expectation μ Z * (expectation μ Z)ᴴ := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  calc expectation μ (fun ω => Z ω * (Z ω)ᴴ) -
      expectation μ Z * (expectation μ Z)ᴴ
      ≤ expectation μ (fun ω => Z ω * (Z ω)ᴴ) - 0 := by
        exact sub_le_sub_left hpsd _
    _ = expectation μ (fun ω => Z ω * (Z ω)ᴴ) := sub_zero _

/-- Lean implementation helper (mirror for `Z*Z`). -/
lemma centered_second_moment_le₂ {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (hZ2 : MIntegrable (fun ω => (Z ω)ᴴ * Z ω) μ) :
    matrixVar2 μ Z ≤ expectation μ (fun ω => (Z ω)ᴴ * Z ω) := by
  rw [matrixVar2_eq_sub hZ hZ2]
  have hpsd : (0 : Matrix n n ℂ) ≤
      (expectation μ Z)ᴴ * expectation μ Z := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  calc expectation μ (fun ω => (Z ω)ᴴ * Z ω) -
      (expectation μ Z)ᴴ * expectation μ Z
      ≤ expectation μ (fun ω => (Z ω)ᴴ * Z ω) - 0 := sub_le_sub_left hpsd _
    _ = expectation μ (fun ω => (Z ω)ᴴ * Z ω) := sub_zero _

end SecondMoment

section LawTransfer

variable {R₀ : Ω → Matrix m n ℂ} {L : ℝ}

/-- Lean implementation helper: identically distributed random matrices have
the same expectation. -/
lemma expectation_of_identDistrib {X Y : Ω → Matrix m n ℂ}
    (hid : ProbabilityTheory.IdentDistrib X Y μ μ) :
    expectation μ X = expectation μ Y := by
  ext i j
  exact (hid.comp (measurable_entry i j)).integral_eq

/-- Lean implementation helper: transfer of the second-moment matrices along
identical distribution. -/
lemma expectation_mul_conjTranspose_of_identDistrib
    {X Y : Ω → Matrix m n ℂ}
    (hid : ProbabilityTheory.IdentDistrib X Y μ μ) :
    expectation μ (fun ω => X ω * (X ω)ᴴ) =
      expectation μ (fun ω => Y ω * (Y ω)ᴴ) := by
  ext i j
  have hg : Measurable fun M : Matrix m n ℂ => (M * Mᴴ) i j := by
    have h1 : (fun M : Matrix m n ℂ => (M * Mᴴ) i j) =
        fun M : Matrix m n ℂ => ∑ l, M i l * star (M j l) := by
      funext M
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.conjTranspose_apply]
    rw [h1]
    exact Finset.measurable_sum _ fun l _ => (measurable_entry i l).mul
      (continuous_star.measurable.comp (measurable_entry j l))
  exact (hid.comp hg).integral_eq

/-- Lean implementation helper: the conjugate-transposed version. -/
lemma expectation_conjTranspose_mul_of_identDistrib
    {X Y : Ω → Matrix m n ℂ}
    (hid : ProbabilityTheory.IdentDistrib X Y μ μ) :
    expectation μ (fun ω => (X ω)ᴴ * X ω) =
      expectation μ (fun ω => (Y ω)ᴴ * Y ω) := by
  ext i j
  have hg : Measurable fun M : Matrix m n ℂ => (Mᴴ * M) i j := by
    have h1 : (fun M : Matrix m n ℂ => (Mᴴ * M) i j) =
        fun M : Matrix m n ℂ => ∑ l, star (M l i) * M l j := by
      funext M
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.conjTranspose_apply]
    rw [h1]
    exact Finset.measurable_sum _ fun l _ =>
      (continuous_star.measurable.comp (measurable_entry l i)).mul
        (measurable_entry l j)
  exact (hid.comp hg).integral_eq

/-- Lean implementation helper: a pointwise norm bound on the template
transfers to an a.e. bound on each copy. -/
lemma identDistrib_norm_bound {X : Ω → Matrix m n ℂ}
    (hid : ProbabilityTheory.IdentDistrib X R₀ μ μ)
    (hbd : ∀ ω, ‖R₀ ω‖ ≤ L) : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ L := by
  have hcomp : ProbabilityTheory.IdentDistrib (fun ω => ‖X ω‖)
      (fun ω => ‖R₀ ω‖) μ μ := hid.comp continuous_l2_opNorm.measurable
  have h1 : μ {ω | L < ‖X ω‖} = μ {ω | L < ‖R₀ ω‖} := by
    have h2 := hcomp.measure_mem_eq (measurableSet_Ioi (a := L))
    have h3 : (fun ω => ‖X ω‖) ⁻¹' Set.Ioi L = {ω | L < ‖X ω‖} := rfl
    have h4 : (fun ω => ‖R₀ ω‖) ⁻¹' Set.Ioi L = {ω | L < ‖R₀ ω‖} := rfl
    rw [h3, h4] at h2
    exact h2
  have h3 : μ {ω | L < ‖R₀ ω‖} = 0 := by
    rw [show {ω | L < ‖R₀ ω‖} = ∅ from Set.eq_empty_iff_forall_notMem.mpr
      fun ω h => absurd (hbd ω) (not_le.mpr h)]
    exact measure_empty
  rw [ae_iff, show {ω | ¬‖X ω‖ ≤ L} = {ω | L < ‖X ω‖} from by
    ext ω
    simp [not_le], h1, h3]

/-- Lean implementation helper: `‖𝔼R‖ ≤ L` (triangle + Jensen, the source's
"the second is Jensen's inequality"). -/
lemma norm_expectation_le_of_bound (hm : Measurable R₀)
    (hbd : ∀ ω, ‖R₀ ω‖ ≤ L) : ‖expectation μ R₀‖ ≤ L := by
  have hint : MIntegrable R₀ μ := mintegrable_rect_of_norm_bound hm hbd
  have hnormint : Integrable (fun ω => ‖R₀ ω‖) μ :=
    Integrable.of_bound (continuous_l2_opNorm.measurable.comp
      hm).aestronglyMeasurable L (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hbd ω)
  refine (norm_expectation_le hint hnormint).trans ?_
  calc ∫ ω, ‖R₀ ω‖ ∂μ ≤ ∫ _ : Ω, L ∂μ :=
        integral_mono hnormint (integrable_const L) fun ω => hbd ω
  _ = L := by rw [integral_const, probReal_univ, one_smul]

end LawTransfer

section SamplingEstimator

variable [Nonempty (m ⊕ n)]
variable {nn : ℕ} {R : Fin nn → Ω → Matrix m n ℂ} {R₀ : Ω → Matrix m n ℂ}
variable {B : Matrix m n ℂ} {L : ℝ}

/-- Lean implementation helper: `(c • M)ᴴ = c • Mᴴ` for a real scalar. -/
lemma conjTranspose_real_smul_rect (c : ℝ) (M : Matrix m n ℂ) :
    (c • M)ᴴ = c • Mᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.conjTranspose_apply]
  simp [Complex.real_smul, Complex.conj_ofReal]

/-- Lean implementation helper: nonnegative real scaling preserves the
Loewner order. -/
lemma real_smul_loewner_mono {p : Type*} [Fintype p] [DecidableEq p]
    {A H : Matrix p p ℂ} {c : ℝ} (hc : 0 ≤ c) (hAH : A ≤ H) :
    c • A ≤ c • H := by
  rw [← sub_nonneg, ← smul_sub, Matrix.nonneg_iff_posSemidef]
  have hpsd : (H - A).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    rwa [← sub_nonneg] at hAH
  refine posSemidef_iff_isHermitian_quadratic.mpr
    ⟨isHermitian_real_smul hpsd.1 c, fun u => ?_⟩
  have h1 : (star u ⬝ᵥ ((c • (H - A)) *ᵥ u)) = (c : ℂ) * (star u ⬝ᵥ ((H - A) *ᵥ u)) := by
    rw [show (c • (H - A)) = ((c : ℂ)) • (H - A) from by
      ext i j
      rw [Matrix.smul_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]]
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [h1]
  have h2 := hpsd.re_dotProduct_nonneg u
  have h3 : (star u ⬝ᵥ ((H - A) *ᵥ u)).im = 0 := by
    rw [star_dotProduct_mulVec_eq_rayleigh hpsd.1]
    exact Complex.ofReal_im _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, h3, mul_zero,
    sub_zero]
  exact mul_nonneg hc h2

/-- Lean implementation helper: measurability of `M ↦ MMᴴ`-type products of a
measurable random matrix (rectangular; local name to avoid clashing with the
Chapter-1 helper). -/
lemma measurable_matrix_mul_conjTranspose {Z : Ω → Matrix m n ℂ}
    (hZ : Measurable Z) : Measurable fun ω => Z ω * (Z ω)ᴴ := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => (Z ω * (Z ω)ᴴ) i j) =
      fun ω => ∑ l, Z ω i l * star (Z ω j l) := by
    funext ω
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.conjTranspose_apply]
  rw [h]
  exact Finset.measurable_sum _ fun l _ =>
    ((measurable_entry i l).comp hZ).mul
      (continuous_star.measurable.comp ((measurable_entry j l).comp hZ))

/-- Lean implementation helper: the conjugate-transposed version. -/
lemma measurable_matrix_conjTranspose_mul {Z : Ω → Matrix m n ℂ}
    (hZ : Measurable Z) : Measurable fun ω => (Z ω)ᴴ * Z ω := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => ((Z ω)ᴴ * Z ω) i j) =
      fun ω => ∑ l, star (Z ω l i) * Z ω l j := by
    funext ω
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.conjTranspose_apply]
  rw [h]
  exact Finset.measurable_sum _ fun l _ =>
    (continuous_star.measurable.comp ((measurable_entry l i).comp hZ)).mul
      ((measurable_entry l j).comp hZ)

/-- **Book Corollary 6.2.1, equation (6.2.5)** (Matrix Approximation by Random
Sampling), expectation bound:

`𝔼‖R̄_n − B‖ ≤ √(2 m₂(R) log(d₁+d₂)/n) + 2L log(d₁+d₂)/(3n)`.

Explicit source declaration.

**Author note.** This pointwise-template form is retained for compatibility;
see `matrix_sampling_estimator_expectation_ae` for the source-faithful
almost-sure counterpart. -/
theorem matrix_sampling_estimator_expectation (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤
      Real.sqrt (2 * secondMoment μ R₀ *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n) / nn) +
      2 * L * Real.log ((Fintype.card m : ℝ) + Fintype.card n) / (3 * nn) := by
  classical
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  set D : ℝ := Real.log ((Fintype.card m : ℝ) + Fintype.card n) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    refine Real.log_nonneg ?_
    have h := Fintype.card_pos (α := m ⊕ n)
    rw [Fintype.card_sum] at h
    exact_mod_cast h
  have hBnorm : ‖B‖ ≤ L := hmean ▸ norm_expectation_le_of_bound hR₀m hbd
  have hL0 : 0 ≤ L := (norm_nonneg B).trans hBnorm
  set c : ℝ := (nn : ℝ)⁻¹ with hcdef
  have hc0 : 0 ≤ c := by positivity
  set S : Fin nn → Ω → Matrix m n ℂ := fun k ω => c • (R k ω - B) with hSdef
  have hSmeas : ∀ k, Measurable (S k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => (c • (R k ω - B)) i j
    have h1 : (fun ω => (c • (R k ω - B)) i j) =
        fun ω => c • (R k ω i j - B i j) := rfl
    rw [h1]
    exact Measurable.const_smul
      (((measurable_entry i j).comp (hmeas k)).sub_const (B i j)) c
  have hRE : ∀ k, expectation μ (R k) = B := fun k =>
    (expectation_of_identDistrib (hid k)).trans hmean
  have hRbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L := fun k =>
    identDistrib_norm_bound (hid k) hbd
  have hRint : ∀ k, MIntegrable (R k) μ := fun k =>
    MIntegrable.of_bound (hmeas k) L ((hRbd_ae k).mono fun ω h i j =>
      (norm_entry_le_l2_opNorm_rect _ _ _).trans h)
  have hScent : ∀ k, expectation μ (S k) = 0 := by
    intro k
    have h1 := expectation_real_smul (μ := μ) c (fun ω => R k ω - B)
    rw [show S k = fun ω => c • (R k ω - B) from rfl, h1,
      show (fun ω => R k ω - B) = fun ω => R k ω - (fun _ : Ω => B) ω from rfl,
      expectation_sub (hRint k) (MIntegrable.const B),
      expectation_const (μ := μ), hRE k, sub_self, smul_zero]
  have hSbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ 2 * L / nn := by
    intro k
    filter_upwards [hRbd_ae k] with ω hω
    show ‖c • (R k ω - B)‖ ≤ 2 * L / nn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    have h1 : ‖R k ω - B‖ ≤ 2 * L := (norm_sub_le _ _).trans (by linarith)
    calc c * ‖R k ω - B‖ ≤ c * (2 * L) :=
          mul_le_mul_of_nonneg_left h1 hc0
    _ = 2 * L / nn := by
          rw [hcdef]
          field_simp
  have hL' : (0 : ℝ) ≤ 2 * L / nn := by positivity
  have hSind : ProbabilityTheory.iIndepFun S μ := by
    refine hind.comp (fun k M => c • (M - B)) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
    exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
  have h := matrix_bernstein_rect_expectation_ae (μ := μ) hSmeas hSbd_ae hL'
    hScent hSind
  -- identify the left-hand side
  have hsum : ∀ ω, (∑ k, S k ω) = (nn : ℝ)⁻¹ • (∑ k, R k ω) - B := by
    intro ω
    show (∑ k, c • (R k ω - B)) = _
    rw [← Finset.smul_sum,
      show (∑ k, (R k ω - B)) = (∑ k, R k ω) - ∑ _k : Fin nn, B from by
        rw [Finset.sum_sub_distrib],
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub, hcdef]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hnn.ne' : (nn : ℝ) ≠ 0), one_smul]
  rw [show (fun ω => ‖∑ k, S k ω‖) =
      fun ω => ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ from
    funext fun ω => by rw [hsum ω]] at h
  -- the variance bound `v(Z) ≤ m₂(R)/n`
  have hSid : ∀ k, ProbabilityTheory.IdentDistrib (S k)
      (fun ω => c • (R₀ ω - B)) μ μ := fun k => by
    have hg : Measurable fun M : Matrix m n ℂ => c • (M - B) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
      exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
    exact (hid k).comp hg
  have hS₀int : MIntegrable (fun ω => R₀ ω - B) μ := by
    have h1 : MIntegrable R₀ μ := mintegrable_rect_of_norm_bound hR₀m hbd
    rw [show (fun ω => R₀ ω - B) = fun ω => R₀ ω - (fun _ : Ω => B) ω from rfl]
    exact h1.sub (MIntegrable.const B)
  have hR₀1 : MIntegrable (fun ω => R₀ ω * (R₀ ω)ᴴ) μ :=
    MIntegrable.of_bound (measurable_matrix_mul_conjTranspose hR₀m) (L * L)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖(R₀ ω * (R₀ ω)ᴴ) i j‖ ≤ ‖R₀ ω * (R₀ ω)ᴴ‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖R₀ ω‖ * ‖(R₀ ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖R₀ ω‖ * ‖R₀ ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (R₀ ω), hbd ω])
  have hR₀2 : MIntegrable (fun ω => (R₀ ω)ᴴ * R₀ ω) μ :=
    MIntegrable.of_bound (measurable_matrix_conjTranspose_mul hR₀m) (L * L)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖((R₀ ω)ᴴ * R₀ ω) i j‖ ≤ ‖(R₀ ω)ᴴ * R₀ ω‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖(R₀ ω)ᴴ‖ * ‖R₀ ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖R₀ ω‖ * ‖R₀ ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (R₀ ω), hbd ω])
  -- the per-copy second-moment matrices, transported to the template
  have hSS : ∀ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ) =
      (c * c) • matrixVar1 μ R₀ := by
    intro k
    have h1 := expectation_mul_conjTranspose_of_identDistrib (hSid k)
    rw [h1]
    have h2 : (fun ω => (c • (R₀ ω - B)) * (c • (R₀ ω - B))ᴴ) =
        fun ω => (c * c) • ((R₀ ω - B) * (R₀ ω - B)ᴴ) := by
      funext ω
      rw [conjTranspose_real_smul_rect, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    rw [h2, expectation_real_smul]
    congr 1
    rw [matrixVar1, hmean]
  have hSS2 : ∀ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω) =
      (c * c) • matrixVar2 μ R₀ := by
    intro k
    have h1 := expectation_conjTranspose_mul_of_identDistrib (hSid k)
    rw [h1]
    have h2 : (fun ω => (c • (R₀ ω - B))ᴴ * (c • (R₀ ω - B))) =
        fun ω => (c * c) • ((R₀ ω - B)ᴴ * (R₀ ω - B)) := by
      funext ω
      rw [conjTranspose_real_smul_rect, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    rw [h2, expectation_real_smul]
    congr 1
    rw [matrixVar2, hmean]
  have hnorm1 : ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖ ≤
      secondMoment μ R₀ / nn := by
    rw [Finset.sum_congr rfl fun k _ => hSS k, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    have hle : matrixVar1 μ R₀ ≤ expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) :=
      centered_second_moment_le (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀1
    have hpsd : (matrixVar1 μ R₀).PosSemidef :=
      posSemidef_matrixVar1 (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀1
    have h3 : ‖matrixVar1 μ R₀‖ ≤ secondMoment μ R₀ :=
      (norm_le_norm_of_loewner_le hpsd hle).trans (le_max_left _ _)
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, norm_smul, Real.norm_eq_abs]
    have h4 : (nn : ℝ) * (c * c) = c := by
      rw [hcdef]
      field_simp
    rw [h4, abs_of_nonneg hc0, hcdef]
    calc (nn : ℝ)⁻¹ * ‖matrixVar1 μ R₀‖ ≤
        (nn : ℝ)⁻¹ * secondMoment μ R₀ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = secondMoment μ R₀ / nn := by ring
  have hnorm2 : ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ ≤
      secondMoment μ R₀ / nn := by
    rw [Finset.sum_congr rfl fun k _ => hSS2 k, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    have hle : matrixVar2 μ R₀ ≤ expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) :=
      centered_second_moment_le₂ (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀2
    have hpsd : (matrixVar2 μ R₀).PosSemidef :=
      posSemidef_matrixVar2 (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀2
    have h3 : ‖matrixVar2 μ R₀‖ ≤ secondMoment μ R₀ :=
      (norm_le_norm_of_loewner_le hpsd hle).trans (le_max_right _ _)
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, norm_smul, Real.norm_eq_abs]
    have h4 : (nn : ℝ) * (c * c) = c := by
      rw [hcdef]
      field_simp
    rw [h4, abs_of_nonneg hc0, hcdef]
    calc (nn : ℝ)⁻¹ * ‖matrixVar2 μ R₀‖ ≤
        (nn : ℝ)⁻¹ * secondMoment μ R₀ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = secondMoment μ R₀ / nn := by ring
  refine h.trans ?_
  have hmaxle : max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
      ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ ≤
      secondMoment μ R₀ / nn := max_le hnorm1 hnorm2
  have hsqrt : Real.sqrt (2 * max ‖∑ k, expectation μ
        (fun ω => S k ω * (S k ω)ᴴ)‖
      ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ * D) ≤
      Real.sqrt (2 * secondMoment μ R₀ * D / nn) := by
    have harg : 2 * max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
        ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ * D ≤
        2 * secondMoment μ R₀ * D / nn := by
      have h5 : 2 * (secondMoment μ R₀ / nn) * D =
          2 * secondMoment μ R₀ * D / nn := by ring
      nlinarith [hmaxle, hD0]
    exact Real.sqrt_le_sqrt harg
  have hlin : 2 * L / (nn : ℝ) / 3 * D = 2 * L * D / (3 * nn) := by
    field_simp
  rw [← hDdef]
  calc Real.sqrt (2 * max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
        ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ * D) +
      2 * L / (nn : ℝ) / 3 * D
      ≤ Real.sqrt (2 * secondMoment μ R₀ * D / nn) + 2 * L * D / (3 * nn) := by
        rw [hlin]
        exact add_le_add hsqrt (le_refl _)
  _ = Real.sqrt (2 * secondMoment μ R₀ * D / nn) +
      2 * L * D / (3 * nn) := rfl

end SamplingEstimator

section SamplingTail

variable [Nonempty (m ⊕ n)]
variable {nn : ℕ} {R : Fin nn → Ω → Matrix m n ℂ} {R₀ : Ω → Matrix m n ℂ}
variable {B : Matrix m n ℂ} {L : ℝ}

/-- **Book Corollary 6.2.1, equation (6.2.6)** (Matrix Approximation by Random
Sampling), tail bound:

`P(‖R̄_n − B‖ ≥ t) ≤ (d₁+d₂)·exp(−nt²/2 / (m₂(R) + 2Lt/3))` for `t ≥ 0`.

Explicit source declaration.

**Author note.** This pointwise-template form is retained for compatibility;
see `matrix_sampling_estimator_tail_ae` for the source-faithful almost-sure
counterpart. -/
theorem matrix_sampling_estimator_tail (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) * Real.exp
        (-(nn * t ^ 2) / 2 / (secondMoment μ R₀ + 2 * L * t / 3)) := by
  classical
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hBnorm : ‖B‖ ≤ L := hmean ▸ norm_expectation_le_of_bound hR₀m hbd
  have hL0 : 0 ≤ L := (norm_nonneg B).trans hBnorm
  have hM0 : 0 ≤ secondMoment μ R₀ := secondMoment_nonneg R₀
  set c : ℝ := (nn : ℝ)⁻¹ with hcdef
  have hc0 : 0 ≤ c := by positivity
  set S : Fin nn → Ω → Matrix m n ℂ := fun k ω => c • (R k ω - B) with hSdef
  have hSmeas : ∀ k, Measurable (S k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => (c • (R k ω - B)) i j
    have h1 : (fun ω => (c • (R k ω - B)) i j) =
        fun ω => c • (R k ω i j - B i j) := rfl
    rw [h1]
    exact Measurable.const_smul
      (((measurable_entry i j).comp (hmeas k)).sub_const (B i j)) c
  have hRE : ∀ k, expectation μ (R k) = B := fun k =>
    (expectation_of_identDistrib (hid k)).trans hmean
  have hRbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L := fun k =>
    identDistrib_norm_bound (hid k) hbd
  have hRint : ∀ k, MIntegrable (R k) μ := fun k =>
    MIntegrable.of_bound (hmeas k) L ((hRbd_ae k).mono fun ω h i j =>
      (norm_entry_le_l2_opNorm_rect _ _ _).trans h)
  have hScent : ∀ k, expectation μ (S k) = 0 := by
    intro k
    have h1 := expectation_real_smul (μ := μ) c (fun ω => R k ω - B)
    rw [show S k = fun ω => c • (R k ω - B) from rfl, h1,
      show (fun ω => R k ω - B) = fun ω => R k ω - (fun _ : Ω => B) ω from rfl,
      expectation_sub (hRint k) (MIntegrable.const B),
      expectation_const (μ := μ), hRE k, sub_self, smul_zero]
  have hSbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ 2 * L / nn := by
    intro k
    filter_upwards [hRbd_ae k] with ω hω
    show ‖c • (R k ω - B)‖ ≤ 2 * L / nn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    have h1 : ‖R k ω - B‖ ≤ 2 * L := (norm_sub_le _ _).trans (by linarith)
    calc c * ‖R k ω - B‖ ≤ c * (2 * L) :=
          mul_le_mul_of_nonneg_left h1 hc0
    _ = 2 * L / nn := by
          rw [hcdef]
          field_simp
  have hL' : (0 : ℝ) ≤ 2 * L / nn := by positivity
  have hSind : ProbabilityTheory.iIndepFun S μ := by
    refine hind.comp (fun k M => c • (M - B)) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
    exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
  have h := matrix_bernstein_rect_tail_ae (μ := μ) hSmeas hSbd_ae hL' hScent
    hSind ht
  -- identify the event
  have hsum : ∀ ω, (∑ k, S k ω) = (nn : ℝ)⁻¹ • (∑ k, R k ω) - B := by
    intro ω
    show (∑ k, c • (R k ω - B)) = _
    rw [← Finset.smul_sum,
      show (∑ k, (R k ω - B)) = (∑ k, R k ω) - ∑ _k : Fin nn, B from by
        rw [Finset.sum_sub_distrib],
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub, hcdef]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hnn.ne' : (nn : ℝ) ≠ 0), one_smul]
  rw [show {ω | t ≤ ‖∑ k, S k ω‖} =
      {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} from by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hsum ω]] at h
  -- the variance bound, transported to the template as before
  have hSid : ∀ k, ProbabilityTheory.IdentDistrib (S k)
      (fun ω => c • (R₀ ω - B)) μ μ := fun k => by
    have hg : Measurable fun M : Matrix m n ℂ => c • (M - B) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
      exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
    exact (hid k).comp hg
  have hR₀1 : MIntegrable (fun ω => R₀ ω * (R₀ ω)ᴴ) μ :=
    MIntegrable.of_bound (measurable_matrix_mul_conjTranspose hR₀m) (L * L)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖(R₀ ω * (R₀ ω)ᴴ) i j‖ ≤ ‖R₀ ω * (R₀ ω)ᴴ‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖R₀ ω‖ * ‖(R₀ ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖R₀ ω‖ * ‖R₀ ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (R₀ ω), hbd ω])
  have hR₀2 : MIntegrable (fun ω => (R₀ ω)ᴴ * R₀ ω) μ :=
    MIntegrable.of_bound (measurable_matrix_conjTranspose_mul hR₀m) (L * L)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖((R₀ ω)ᴴ * R₀ ω) i j‖ ≤ ‖(R₀ ω)ᴴ * R₀ ω‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖(R₀ ω)ᴴ‖ * ‖R₀ ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖R₀ ω‖ * ‖R₀ ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (R₀ ω), hbd ω])
  have hSS : ∀ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ) =
      (c * c) • matrixVar1 μ R₀ := by
    intro k
    have h1 := expectation_mul_conjTranspose_of_identDistrib (hSid k)
    rw [h1]
    have h2 : (fun ω => (c • (R₀ ω - B)) * (c • (R₀ ω - B))ᴴ) =
        fun ω => (c * c) • ((R₀ ω - B) * (R₀ ω - B)ᴴ) := by
      funext ω
      rw [conjTranspose_real_smul_rect, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    rw [h2, expectation_real_smul]
    congr 1
    rw [matrixVar1, hmean]
  have hSS2 : ∀ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω) =
      (c * c) • matrixVar2 μ R₀ := by
    intro k
    have h1 := expectation_conjTranspose_mul_of_identDistrib (hSid k)
    rw [h1]
    have h2 : (fun ω => (c • (R₀ ω - B))ᴴ * (c • (R₀ ω - B))) =
        fun ω => (c * c) • ((R₀ ω - B)ᴴ * (R₀ ω - B)) := by
      funext ω
      rw [conjTranspose_real_smul_rect, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    rw [h2, expectation_real_smul]
    congr 1
    rw [matrixVar2, hmean]
  have hnorm1 : ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖ ≤
      secondMoment μ R₀ / nn := by
    rw [Finset.sum_congr rfl fun k _ => hSS k, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    have hle : matrixVar1 μ R₀ ≤ expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) :=
      centered_second_moment_le (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀1
    have hpsd : (matrixVar1 μ R₀).PosSemidef :=
      posSemidef_matrixVar1 (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀1
    have h3 : ‖matrixVar1 μ R₀‖ ≤ secondMoment μ R₀ :=
      (norm_le_norm_of_loewner_le hpsd hle).trans (le_max_left _ _)
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, norm_smul, Real.norm_eq_abs]
    have h4 : (nn : ℝ) * (c * c) = c := by
      rw [hcdef]
      field_simp
    rw [h4, abs_of_nonneg hc0, hcdef]
    calc (nn : ℝ)⁻¹ * ‖matrixVar1 μ R₀‖ ≤
        (nn : ℝ)⁻¹ * secondMoment μ R₀ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = secondMoment μ R₀ / nn := by ring
  have hnorm2 : ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ ≤
      secondMoment μ R₀ / nn := by
    rw [Finset.sum_congr rfl fun k _ => hSS2 k, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    have hle : matrixVar2 μ R₀ ≤ expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) :=
      centered_second_moment_le₂ (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀2
    have hpsd : (matrixVar2 μ R₀).PosSemidef :=
      posSemidef_matrixVar2 (mintegrable_rect_of_norm_bound hR₀m hbd) hR₀2
    have h3 : ‖matrixVar2 μ R₀‖ ≤ secondMoment μ R₀ :=
      (norm_le_norm_of_loewner_le hpsd hle).trans (le_max_right _ _)
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, norm_smul, Real.norm_eq_abs]
    have h4 : (nn : ℝ) * (c * c) = c := by
      rw [hcdef]
      field_simp
    rw [h4, abs_of_nonneg hc0, hcdef]
    calc (nn : ℝ)⁻¹ * ‖matrixVar2 μ R₀‖ ≤
        (nn : ℝ)⁻¹ * secondMoment μ R₀ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = secondMoment μ R₀ / nn := by ring
  refine h.trans ?_
  have hcard0 : (0 : ℝ) ≤ (Fintype.card m : ℝ) + Fintype.card n := by
    positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcard0
  set v : ℝ := max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
    ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ with hvdef
  have hv0 : 0 ≤ v := le_max_of_le_left (norm_nonneg _)
  have hvle : v ≤ secondMoment μ R₀ / nn := max_le hnorm1 hnorm2
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- `t = 0`: both exponents vanish
    rw [← ht0]
    norm_num
  rcases eq_or_lt_of_le hL0 with hLz | hLpos
  · -- `L = 0`: `m₂ = 0` and `v = 0`; both exponents vanish
    have hM00 : secondMoment μ R₀ = 0 := by
      have hR00 : R₀ = fun _ => 0 := funext fun ω =>
        norm_le_zero_iff.mp (le_trans (hbd ω) hLz.symm.le)
      rw [secondMoment, hR00]
      rw [show (fun ω => (0 : Matrix m n ℂ) * (0 : Matrix m n ℂ)ᴴ) =
        fun _ : Ω => (0 : Matrix m m ℂ) from by
          funext ω
          rw [Matrix.zero_mul],
        show (fun ω => (0 : Matrix m n ℂ)ᴴ * (0 : Matrix m n ℂ)) =
        fun _ : Ω => (0 : Matrix n n ℂ) from by
          funext ω
          rw [Matrix.mul_zero],
        expectation_const (μ := μ), expectation_const (μ := μ)]
      simp
    have hv00 : v = 0 := le_antisymm (by
      rw [hM00, zero_div] at hvle
      exact hvle) hv0
    rw [hv00, hM00, ← hLz]
    norm_num
  · -- main case `t > 0`, `L > 0`
    have hden1 : 0 < v + 2 * L / (nn : ℝ) * t / 3 := by positivity
    have hden2 : 0 < secondMoment μ R₀ + 2 * L * t / 3 := by positivity
    have hkey : -(nn * t ^ 2) / 2 / (secondMoment μ R₀ + 2 * L * t / 3) =
        -(t ^ 2) / 2 / ((secondMoment μ R₀ + 2 * L * t / 3) / nn) := by
      have hd : (0 : ℝ) < 2 * (secondMoment μ R₀ + 2 * L * t / 3) := by
        positivity
      have hd' : (0 : ℝ) <
          2 * ((secondMoment μ R₀ + 2 * L * t / 3) / nn) := by positivity
      rw [div_div, div_div, div_eq_div_iff hd.ne' hd'.ne']
      field_simp
    rw [hkey]
    have hdle : v + 2 * L / (nn : ℝ) * t / 3 ≤
        (secondMoment μ R₀ + 2 * L * t / 3) / nn := by
      rw [add_div]
      refine add_le_add hvle (le_of_eq ?_)
      field_simp
    have hden2' : 0 < (secondMoment μ R₀ + 2 * L * t / 3) / (nn : ℝ) := by
      positivity
    rw [div_le_div_iff₀ hden1 hden2']
    nlinarith [sq_nonneg t, htpos, hdle, hden1]

end SamplingTail

section SampleCost

variable [Nonempty (m ⊕ n)]
variable {nn : ℕ} {R : Fin nn → Ω → Matrix m n ℂ} {R₀ : Ω → Matrix m n ℂ}
variable {B : Matrix m n ℂ} {L : ℝ}

/-- **Book (6.2.7)** (C6-15):
`n ≥ 2m₂(R)log(d₁+d₂)/ε² + 2L log(d₁+d₂)/(3ε)` implies
`𝔼‖R̄_n − B‖ ≤ 2ε`. Explicit source display.

**Author note.** This pointwise-template form is retained for compatibility;
see `matrix_sampling_sample_cost_ae` for the source-faithful almost-sure
counterpart. -/
theorem matrix_sampling_sample_cost (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) {ε : ℝ} (hε : 0 < ε)
    (hcost : 2 * secondMoment μ R₀ *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n) / ε ^ 2 +
      2 * L * Real.log ((Fintype.card m : ℝ) + Fintype.card n) / (3 * ε) ≤
        nn) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤ 2 * ε := by
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hBnorm : ‖B‖ ≤ L := hmean ▸ norm_expectation_le_of_bound hR₀m hbd
  have hL0 : 0 ≤ L := (norm_nonneg B).trans hBnorm
  have hM0 : 0 ≤ secondMoment μ R₀ := secondMoment_nonneg R₀
  set D : ℝ := Real.log ((Fintype.card m : ℝ) + Fintype.card n) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    refine Real.log_nonneg ?_
    have h := Fintype.card_pos (α := m ⊕ n)
    rw [Fintype.card_sum] at h
    exact_mod_cast h
  have h := matrix_sampling_estimator_expectation (μ := μ) hnn hR₀m hbd hmean
    hmeas hid hind
  rw [← hDdef] at h
  refine h.trans ?_
  have h1 : Real.sqrt (2 * secondMoment μ R₀ * D / nn) ≤ ε := by
    rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hnR]
    have h2 : 2 * secondMoment μ R₀ * D / ε ^ 2 ≤ (nn : ℝ) := by
      have h3 : 0 ≤ 2 * L * D / (3 * ε) := by positivity
      rw [hDdef]
      rw [hDdef] at hcost
      linarith
    calc 2 * secondMoment μ R₀ * D =
        (2 * secondMoment μ R₀ * D / ε ^ 2) * ε ^ 2 := by
          field_simp
    _ ≤ (nn : ℝ) * ε ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = ε ^ 2 * nn := by ring
  have h4 : 2 * L * D / (3 * nn) ≤ ε := by
    have h5 : 2 * L * D / (3 * ε) ≤ (nn : ℝ) := by
      have h6 : 0 ≤ 2 * secondMoment μ R₀ * D / ε ^ 2 := by positivity
      rw [hDdef]
      rw [hDdef] at hcost
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * nn)]
    calc 2 * L * D = (2 * L * D / (3 * ε)) * (3 * ε) := by
          field_simp
    _ ≤ (nn : ℝ) * (3 * ε) := mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = ε * (3 * nn) := by ring
  linarith

end SampleCost

section SamplingAeCounterparts

variable [Nonempty (m ⊕ n)]
variable {nn : ℕ} {R : Fin nn → Ω → Matrix m n ℂ} {R₀ : Ω → Matrix m n ℂ}
variable {B : Matrix m n ℂ} {L : ℝ}

/-- **Book Corollary 6.2.1, equation (6.2.5)** with the source's
almost-sure reading of `‖R‖ ≤ L`.

This is the book-faithful counterpart of
`matrix_sampling_estimator_expectation`, whose template bound is pointwise. -/
theorem matrix_sampling_estimator_expectation_ae (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤
      Real.sqrt (2 * secondMoment μ R₀ *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n) / nn) +
      2 * L * Real.log ((Fintype.card m : ℝ) + Fintype.card n) / (3 * nn) := by
  let R₀' : Ω → Matrix m n ℂ := fun ω => truncateNorm L (R₀ ω)
  have hL : 0 ≤ L := nonneg_of_ae_norm_le hR₀m hbd
  have hae : R₀' =ᵐ[μ] R₀ := hbd.mono fun ω hω => by
    simp only [R₀', truncateNorm, if_pos hω]
  have hR₀m' : Measurable R₀' := measurable_truncateNorm.comp hR₀m
  have hbd' : ∀ ω, ‖R₀' ω‖ ≤ L := fun ω => truncateNorm_norm_le hL _
  have hmean' : expectation μ R₀' = B := by
    rw [expectation_congr_ae hae, hmean]
  have hid' : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀' μ μ := fun k =>
    (hid k).trans (ProbabilityTheory.IdentDistrib.of_ae_eq
      hR₀m.aemeasurable hae.symm)
  have h := matrix_sampling_estimator_expectation (μ := μ) hnn hR₀m' hbd'
    hmean' hmeas hid' hind
  rw [secondMoment_congr_ae hae] at h
  exact h

/-- **Book Corollary 6.2.1, equation (6.2.6)** with the source's
almost-sure template bound.  This is the book-faithful counterpart of
`matrix_sampling_estimator_tail`. -/
theorem matrix_sampling_estimator_tail_ae (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) * Real.exp
        (-(nn * t ^ 2) / 2 / (secondMoment μ R₀ + 2 * L * t / 3)) := by
  let R₀' : Ω → Matrix m n ℂ := fun ω => truncateNorm L (R₀ ω)
  have hL : 0 ≤ L := nonneg_of_ae_norm_le hR₀m hbd
  have hae : R₀' =ᵐ[μ] R₀ := hbd.mono fun ω hω => by
    simp only [R₀', truncateNorm, if_pos hω]
  have hR₀m' : Measurable R₀' := measurable_truncateNorm.comp hR₀m
  have hbd' : ∀ ω, ‖R₀' ω‖ ≤ L := fun ω => truncateNorm_norm_le hL _
  have hmean' : expectation μ R₀' = B := by
    rw [expectation_congr_ae hae, hmean]
  have hid' : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀' μ μ := fun k =>
    (hid k).trans (ProbabilityTheory.IdentDistrib.of_ae_eq
      hR₀m.aemeasurable hae.symm)
  have h := matrix_sampling_estimator_tail (μ := μ) hnn hR₀m' hbd' hmean'
    hmeas hid' hind ht
  rw [secondMoment_congr_ae hae] at h
  exact h

/-- **Book equation (6.2.7)** with an almost-sure template bound.  This is the
book-faithful counterpart of `matrix_sampling_sample_cost`. -/
theorem matrix_sampling_sample_cost_ae (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) {ε : ℝ} (hε : 0 < ε)
    (hcost : 2 * secondMoment μ R₀ *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n) / ε ^ 2 +
      2 * L * Real.log ((Fintype.card m : ℝ) + Fintype.card n) / (3 * ε) ≤
        nn) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤ 2 * ε := by
  let R₀' : Ω → Matrix m n ℂ := fun ω => truncateNorm L (R₀ ω)
  have hL : 0 ≤ L := nonneg_of_ae_norm_le hR₀m hbd
  have hae : R₀' =ᵐ[μ] R₀ := hbd.mono fun ω hω => by
    simp only [R₀', truncateNorm, if_pos hω]
  have hR₀m' : Measurable R₀' := measurable_truncateNorm.comp hR₀m
  have hbd' : ∀ ω, ‖R₀' ω‖ ≤ L := fun ω => truncateNorm_norm_le hL _
  have hmean' : expectation μ R₀' = B := by
    rw [expectation_congr_ae hae, hmean]
  have hid' : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀' μ μ := fun k =>
    (hid k).trans (ProbabilityTheory.IdentDistrib.of_ae_eq
      hR₀m.aemeasurable hae.symm)
  have hcost' : 2 * secondMoment μ R₀' *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n) / ε ^ 2 +
      2 * L * Real.log ((Fintype.card m : ℝ) + Fintype.card n) / (3 * ε) ≤
        nn := by
    rw [secondMoment_congr_ae hae]
    exact hcost
  exact matrix_sampling_sample_cost (μ := μ) hnn hR₀m' hbd' hmean' hmeas
    hid' hind hε hcost'

end SamplingAeCounterparts

section TraceControl

/-- **Book §6.2.3, first discussion display** (C6-16), trace-duality half:
`|tr(AC)| ≤ ‖A‖·‖C‖_{S1}` — the implicit inequality behind "This type of
estimate simultaneously controls the error in every linear function of the
approximation." Implicit source declaration; proved by the SVD of `C`. -/
theorem abs_trace_mul_le_schattenOne {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) :
    ‖(A * C).trace‖ ≤ ‖A‖ * schattenOneNorm C := by
  classical
  obtain ⟨U, W, σ, hU, hW, hσ0, -, ⟨e, hσe⟩, -, hC⟩ := exists_svd C
  set Sig : Matrix (Fin q) (Fin p) ℂ := Matrix.of fun (j : Fin q) (i : Fin p) =>
    if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0 with hSigdef
  set N : Matrix (Fin p) (Fin q) ℂ := Wᴴ * A * U with hNdef
  -- cyclic permutation of the trace
  have htr : (A * C).trace = (N * Sig).trace := by
    rw [hC]
    rw [show A * (U * Sig * Wᴴ) = A * U * Sig * Wᴴ from by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm (A * U * Sig) Wᴴ]
    rw [show Wᴴ * (A * U * Sig) = (Wᴴ * A * U) * Sig from by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
  -- entrywise bound on the diagonal of `NΣ`
  have hNnorm : ‖N‖ = ‖A‖ := by
    rw [hNdef, Matrix.mul_assoc,
      show (Wᴴ : Matrix (Fin p) (Fin p) ℂ) = star W from
        (Matrix.star_eq_conjTranspose W).symm,
      l2_opNorm_unitary_mul (Unitary.star_mem hW) (A * U),
      l2_opNorm_mul_unitary A hU]
  have hentry : ∀ i : Fin p, ‖(N * Sig) i i‖ ≤ ‖A‖ * σ i := by
    intro i
    rw [Matrix.mul_apply]
    calc ‖∑ j, N i j * Sig j i‖ ≤ ∑ j, ‖N i j * Sig j i‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin q, (if (j : ℕ) = (i : ℕ) then ‖A‖ * σ i else 0) := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hji : (j : ℕ) = (i : ℕ)
        · rw [if_pos hji, hSigdef]
          rw [show (Matrix.of fun (j : Fin q) (i : Fin p) =>
            if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0) j i =
            ((σ i : ℝ) : ℂ) from by rw [Matrix.of_apply, if_pos hji]]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hσ0 i)]
          refine mul_le_mul_of_nonneg_right ?_ (hσ0 i)
          rw [← hNnorm]
          exact norm_entry_le_l2_opNorm_rect N i j
        · rw [if_neg hji, hSigdef]
          rw [show (Matrix.of fun (j : Fin q) (i : Fin p) =>
            if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0) j i =
            0 from by rw [Matrix.of_apply, if_neg hji]]
          rw [mul_zero, norm_zero]
    _ ≤ ‖A‖ * σ i := by
        have hAσ : 0 ≤ ‖A‖ * σ i := mul_nonneg (norm_nonneg A) (hσ0 i)
        by_cases hi : (i : ℕ) < q
        · rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin q)]
          · rw [if_pos rfl]
          · intro b _ hb
            refine if_neg fun hbi => hb (Fin.ext hbi)
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        · have hz : (∑ j : Fin q,
              (if (j : ℕ) = (i : ℕ) then ‖A‖ * σ i else 0)) = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            refine if_neg fun hji => ?_
            exact hi (hji ▸ j.isLt)
          rw [hz]
          exact hAσ
  -- assemble
  rw [htr]
  calc ‖(N * Sig).trace‖ = ‖∑ i, (N * Sig) i i‖ := by rw [Matrix.trace]; rfl
  _ ≤ ∑ i, ‖(N * Sig) i i‖ := norm_sum_le _ _
  _ ≤ ∑ i, ‖A‖ * σ i := Finset.sum_le_sum fun i _ => hentry i
  _ = ‖A‖ * ∑ i, σ i := by rw [Finset.mul_sum]
  _ = ‖A‖ * schattenOneNorm C := by
      congr 1
      rw [schattenOneNorm, hσe]
      exact Fintype.sum_equiv e _ _ fun i => rfl

/-- **Book §6.2.3, first discussion display** (C6-16):
"`‖R̄_n − B‖ ≤ ε` implies `|tr(R̄_nC) − tr(BC)| ≤ ε` when `‖C‖_{S1} ≤ 1`."
Explicit source display. -/
theorem trace_control_of_norm_le {p q : ℕ}
    {A B' : Matrix (Fin p) (Fin q) ℂ} {C : Matrix (Fin q) (Fin p) ℂ} {ε : ℝ}
    (hAB : ‖A - B'‖ ≤ ε) (hC : schattenOneNorm C ≤ 1) :
    ‖(A * C).trace - (B' * C).trace‖ ≤ ε := by
  have hdiff : (A * C).trace - (B' * C).trace = ((A - B') * C).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
  rw [hdiff]
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hAB
  calc ‖((A - B') * C).trace‖ ≤ ‖A - B'‖ * schattenOneNorm C :=
        abs_trace_mul_le_schattenOne _ _
  _ ≤ ε * 1 := mul_le_mul hAB hC (schattenOneNorm_nonneg C) hε0
  _ = ε := mul_one ε

end TraceControl

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Randomized sparsification of a matrix (Tropp §6.3)

The Kundu–Drineas sparsification scheme: sample single entries of a target
matrix `B` with the probabilities **Book (6.3.1)**

`p_ij = |b_ij|²/(2‖B‖_F²) + |b_ij|/(2‖B‖_{ℓ1})`,

and average `n` independent copies of `R = p_ij⁻¹ b_ij E_ij` (with the
convention `0/0 = 0`, which is automatic for Lean's division).

* `expectation_discrete` — the reusable finite-sampling computation
  `𝔼 V(J) = Σ_k P(J = k)·V_k` (Lean helper for all §6.3–§6.5 models);
* `sparsifyProb`, `sparsifyValue`, `sparsifyProb_sum_eq_one` (C6-21; the
  source: "It is easy to check that the numbers `p_ij` form a probability
  distribution");
* `expectation_sparsifyValue` — `𝔼R = B` (C6-21, "It is immediate");
* `sparsify_norm_le` — `L = 2‖B‖_{ℓ1}` (§6.3.3);
* `sparsify_second_moment_le` — `m₂(R) ≤ 2·max{d₁,d₂}·‖B‖_F²` (§6.3.3);
* `sparsification_error_bound` — the error estimate **Book (6.3.2)**.

The model: a measurable random index `J : Ω → Fin d₁ × Fin d₂` whose law
gives each pair probability `p_ij`; the estimator is `R₀ = sparsifyValue B ∘ J`
(so the book's "`R` has exactly one nonzero entry" holds pointwise), and the
`n` samples are independent identically distributed copies as in §6.2.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [IsProbabilityMeasure μ]

section DiscreteSampling

/-- Lean implementation helper (used by §§6.3–6.4): the expectation of a
finitely-valued random matrix `V ∘ J` is the probability-weighted sum of its
values. -/
lemma expectation_discrete {ι' : Type*} [Fintype ι'] [MeasurableSpace ι']
    [MeasurableSingletonClass ι'] {p q : Type*} [Fintype p] [Fintype q]
    {J : Ω → ι'} (hJ : Measurable J) (hV : Measurable (fun k : ι' => k))
    (V : ι' → Matrix p q ℂ) :
    expectation μ (fun ω => V (J ω)) =
      ∑ k, (μ.real (J ⁻¹' {k})) • V k := by
  classical
  ext i j
  rw [expectation_apply]
  have hVm : Measurable fun k : ι' => V k i j := by
    exact measurable_of_countable _
  have h1 : ∫ ω, V (J ω) i j ∂μ = ∫ k, V k i j ∂(μ.map J) :=
    (integral_map hJ.aemeasurable hVm.aestronglyMeasurable).symm
  have h2 : Integrable (fun k => V k i j) (μ.map J) := by
    haveI : IsFiniteMeasure (μ.map J) := by
      constructor
      rw [Measure.map_apply hJ MeasurableSet.univ]
      exact measure_lt_top μ _
    refine Integrable.of_bound hVm.aestronglyMeasurable (∑ k, ‖V k i j‖)
      (Filter.Eventually.of_forall fun k =>
        Finset.single_le_sum (f := fun k => ‖V k i j‖)
          (fun k _ => norm_nonneg _) (Finset.mem_univ k))
  rw [h1, integral_fintype h2]
  rw [show ((∑ k, (μ.real (J ⁻¹' {k})) • V k) i j) =
    ∑ k, (μ.real (J ⁻¹' {k})) • V k i j from by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ => rfl]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [measureReal_def, measureReal_def, Measure.map_apply hJ
    (MeasurableSet.singleton k)]

/-- Lean implementation helper: `expectation_discrete` without its historically
redundant measurability argument on the finite index type.  This is an add-only
API cleanup; the original declaration is retained verbatim. -/
lemma expectation_discrete_no_hV {ι' : Type*} [Fintype ι'] [MeasurableSpace ι']
    [MeasurableSingletonClass ι'] {p q : Type*} [Fintype p] [Fintype q]
    {J : Ω → ι'} (hJ : Measurable J) (V : ι' → Matrix p q ℂ) :
    expectation μ (fun ω => V (J ω)) =
      ∑ k, (μ.real (J ⁻¹' {k})) • V k := by
  exact expectation_discrete hJ (measurable_of_countable _) V

/-- Lean implementation helper: `‖E_ij‖ = 1` for the matrix unit. -/
lemma l2_opNorm_single_one {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (i : p) (j : q) :
    ‖Matrix.single i j (1 : ℂ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine (l2_opNorm_le_frobeniusNorm _).trans (le_of_eq ?_)
    have h : frobeniusNorm (Matrix.single i j (1 : ℂ)) ^ 2 = 1 := by
      rw [frobeniusNorm_sq]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
          norm_num
        · intro b _ hb
          rw [Matrix.single_apply, if_neg fun hc => hb hc.2.symm]
          norm_num
        · intro h
          exact absurd (Finset.mem_univ j) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Matrix.single_apply, if_neg fun hc => ha hc.1.symm]
        norm_num
      · intro h
        exact absurd (Finset.mem_univ i) h
    have h0 := frobeniusNorm_nonneg (Matrix.single i j (1 : ℂ))
    nlinarith
  · have h := norm_entry_le_l2_opNorm_rect (Matrix.single i j (1 : ℂ)) i j
    rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩] at h
    simpa using h

end DiscreteSampling

section SparsifyModel

variable {d₁ d₂ : ℕ}

/-- **Book (6.3.1)** (C6-21): the sampling probabilities
`p_ij = |b_ij|²/(2‖B‖_F²) + |b_ij|/(2‖B‖_{ℓ1})`.  Explicit source
declaration. -/
noncomputable def sparsifyProb (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) : ℝ :=
  ‖B k.1 k.2‖ ^ 2 / (2 * frobeniusNorm B ^ 2) +
    ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B)

/-- **Book §6.3.1** (C6-21): the single-entry sample
`R = p_ij⁻¹ · b_ij E_ij` ("we use the convention that `0/0 = 0`", which is
Lean's division).  Explicit source declaration. -/
noncomputable def sparsifyValue (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) : Matrix (Fin d₁) (Fin d₂) ℂ :=
  (sparsifyProb B k)⁻¹ • (B k.1 k.2 • Matrix.single k.1 k.2 (1 : ℂ))

/-- Lean implementation helper: nonnegativity of the entrywise `ℓ₁` norm. -/
lemma entrywiseL1Norm_nonneg' (B : Matrix (Fin d₁) (Fin d₂) ℂ) :
    0 ≤ entrywiseL1Norm B := by
  rw [entrywiseL1Norm]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _

/-- Lean implementation helper: nonnegativity of each sparsification probability. -/
lemma sparsifyProb_nonneg (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) : 0 ≤ sparsifyProb B k := by
  rw [sparsifyProb]
  have h1 : (0 : ℝ) ≤ ‖B k.1 k.2‖ ^ 2 / (2 * frobeniusNorm B ^ 2) :=
    div_nonneg (by positivity) (by positivity)
  have h2 : (0 : ℝ) ≤ ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B) :=
    div_nonneg (norm_nonneg _) (by linarith [entrywiseL1Norm_nonneg' B])
  linarith

/-- Lean implementation helper: positivity of the norms of a nonzero matrix. -/
lemma frobeniusNorm_pos {B : Matrix (Fin d₁) (Fin d₂) ℂ} (hB : B ≠ 0) :
    0 < frobeniusNorm B := by
  rcases eq_or_lt_of_le (frobeniusNorm_nonneg B) with h | h
  · exfalso
    apply hB
    have h2 : frobeniusNorm B ^ 2 = 0 := by rw [← h]; ring
    rw [frobeniusNorm_sq] at h2
    ext i j
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg ‖B i j‖).mp h2 i (Finset.mem_univ i)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      sq_nonneg ‖B i j‖).mp h3 j (Finset.mem_univ j)
    have h5 : ‖B i j‖ = 0 := by nlinarith [norm_nonneg (B i j)]
    rw [Matrix.zero_apply]
    exact norm_eq_zero.mp h5
  · exact h

/-- Lean implementation helper: positivity of the entrywise `ℓ₁` norm for a nonzero matrix. -/
lemma entrywiseL1Norm_pos {B : Matrix (Fin d₁) (Fin d₂) ℂ} (hB : B ≠ 0) :
    0 < entrywiseL1Norm B := by
  have h0 : (0 : ℝ) ≤ entrywiseL1Norm B := by
    rw [entrywiseL1Norm]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      norm_nonneg _
  rcases eq_or_lt_of_le h0 with h | h
  · exfalso
    apply hB
    rw [entrywiseL1Norm] at h
    ext i j
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => norm_nonneg (B i j)).mp h.symm i
      (Finset.mem_univ i)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      norm_nonneg (B i j)).mp h3 j (Finset.mem_univ j)
    rw [Matrix.zero_apply]
    exact norm_eq_zero.mp h4
  · exact h

/-- **Book §6.3.1** (C6-21): "It is easy to check that the numbers `p_ij`
form a probability distribution."  Implicit source claim, fully proved. -/
theorem sparsifyProb_sum_eq_one {B : Matrix (Fin d₁) (Fin d₂) ℂ}
    (hB : B ≠ 0) : ∑ k, sparsifyProb B k = 1 := by
  have hF := frobeniusNorm_pos hB
  have hL1 := entrywiseL1Norm_pos hB
  rw [show (∑ k, sparsifyProb B k) =
    (∑ k : Fin d₁ × Fin d₂, ‖B k.1 k.2‖ ^ 2) / (2 * frobeniusNorm B ^ 2) +
      (∑ k : Fin d₁ × Fin d₂, ‖B k.1 k.2‖) / (2 * entrywiseL1Norm B) from by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => rfl]
  have h1 : (∑ k : Fin d₁ × Fin d₂, ‖B k.1 k.2‖ ^ 2) = frobeniusNorm B ^ 2 := by
    rw [frobeniusNorm_sq, ← Finset.sum_product']
    rfl
  have h2 : (∑ k : Fin d₁ × Fin d₂, ‖B k.1 k.2‖) = entrywiseL1Norm B := by
    rw [entrywiseL1Norm, ← Finset.sum_product']
    rfl
  rw [h1, h2]
  field_simp
  ring

/-- **Book (6.3.3)** (C6-21): the first lower bound
on the sampling probabilities ("Each estimate follows by neglecting one
term").  Explicit source display. -/
lemma sparsifyProb_lower₁ (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) :
    ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B) ≤ sparsifyProb B k := by
  rw [sparsifyProb]
  have h : (0 : ℝ) ≤ ‖B k.1 k.2‖ ^ 2 / (2 * frobeniusNorm B ^ 2) := by
    positivity
  linarith

/-- **Book (6.3.3)** (C6-21): the second lower bound on the sparsification
probabilities. -/
lemma sparsifyProb_lower₂ (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) :
    ‖B k.1 k.2‖ ^ 2 / (2 * frobeniusNorm B ^ 2) ≤ sparsifyProb B k := by
  rw [sparsifyProb]
  have h : (0 : ℝ) ≤ ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B) :=
    div_nonneg (norm_nonneg _) (by linarith [entrywiseL1Norm_nonneg' B])
  linarith

/-- **Book §6.3.1** (C6-21): the weighted values recover the target,
`Σ_ij p_ij (p_ij⁻¹ b_ij E_ij) = Σ_ij b_ij E_ij = B` — "Therefore, `R` is an
unbiased estimate of `B`."  Implicit source computation. -/
theorem sum_sparsifyProb_smul_value {B : Matrix (Fin d₁) (Fin d₂) ℂ}
    (hB : B ≠ 0) :
    (∑ k, sparsifyProb B k • sparsifyValue B k) = B := by
  have hF := frobeniusNorm_pos hB
  have hL1 := entrywiseL1Norm_pos hB
  have h1 : ∀ k : Fin d₁ × Fin d₂, sparsifyProb B k • sparsifyValue B k =
      B k.1 k.2 • Matrix.single k.1 k.2 (1 : ℂ) := by
    intro k
    rw [sparsifyValue, smul_smul]
    by_cases hb : B k.1 k.2 = 0
    · rw [hb, zero_smul, smul_zero]
    · have hp : sparsifyProb B k ≠ 0 := by
        have h2 := sparsifyProb_lower₁ B k
        have h3 : 0 < ‖B k.1 k.2‖ := norm_pos_iff.mpr hb
        have h4 : 0 < ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B) :=
          div_pos h3 (by linarith)
        linarith [h2]
      rw [mul_inv_cancel₀ hp, one_smul]
  rw [Finset.sum_congr rfl fun k _ => h1 k]
  rw [show (∑ k : Fin d₁ × Fin d₂, B k.1 k.2 • Matrix.single k.1 k.2 (1 : ℂ)) =
    ∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ) from by
      rw [← Finset.sum_product']
      rfl]
  have h5 : ∀ (i : Fin d₁) (j : Fin d₂),
      B i j • Matrix.single i j (1 : ℂ) = Matrix.single i j (B i j) := by
    intro i j
    ext a b
    rw [Matrix.smul_apply, Matrix.single_apply, Matrix.single_apply]
    split_ifs with h
    · rw [smul_eq_mul, mul_one]
    · rw [smul_zero]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h5 i j]
  exact (Matrix.matrix_eq_sum_single B).symm

/-- **Book §6.3.3, first display** (C6-22): the uniform bound
`‖R‖ ≤ 2‖B‖_{ℓ1}` ("Therefore, we may take `L = 2‖B‖_{ℓ1}`").  Explicit
source display. -/
theorem sparsify_norm_le {B : Matrix (Fin d₁) (Fin d₂) ℂ} (hB : B ≠ 0)
    (k : Fin d₁ × Fin d₂) :
    ‖sparsifyValue B k‖ ≤ 2 * entrywiseL1Norm B := by
  have hL1 := entrywiseL1Norm_pos hB
  by_cases hb : B k.1 k.2 = 0
  · rw [sparsifyValue, hb, zero_smul, smul_zero, norm_zero]
    positivity
  · have h3 : 0 < ‖B k.1 k.2‖ := norm_pos_iff.mpr hb
    have hp : 0 < sparsifyProb B k := by
      have h2 := sparsifyProb_lower₁ B k
      have h4 : 0 < ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B) :=
        div_pos h3 (by linarith)
      linarith
    rw [sparsifyValue, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hp.le), l2_opNorm_single_one, mul_one]
    -- `p⁻¹ ‖b‖ ≤ 2ℓ1` from `p ≥ ‖b‖/(2ℓ1)`
    have h5 := sparsifyProb_lower₁ B k
    rw [inv_mul_le_iff₀ hp]
    calc ‖B k.1 k.2‖ = (‖B k.1 k.2‖ / (2 * entrywiseL1Norm B)) *
        (2 * entrywiseL1Norm B) := by
          field_simp
    _ ≤ sparsifyProb B k * (2 * entrywiseL1Norm B) := by
          have h6 : (0 : ℝ) ≤ 2 * entrywiseL1Norm B := by linarith
          exact mul_le_mul_of_nonneg_right h5 h6

end SparsifyModel

section SecondMomentBound

variable {d₁ d₂ : ℕ}

/-- Lean implementation helper: `E_ij E_ij* = E_ii`. -/
lemma single_mul_conjTranspose_single (i : Fin d₁) (j : Fin d₂) :
    Matrix.single i j (1 : ℂ) * (Matrix.single i j (1 : ℂ))ᴴ =
      Matrix.single i i (1 : ℂ) := by
  ext a b
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
      Matrix.single_apply]
    split_ifs <;> simp_all <;>
      (rename_i hne hconj
       exact hne (hconj.1.symm.trans hconj.2))
  · intro l _ hl
    rw [Matrix.single_apply, if_neg fun hc => hl hc.2.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Lean implementation helper: `E_ij* E_ij = E_jj`. -/
lemma conjTranspose_single_mul_single (i : Fin d₁) (j : Fin d₂) :
    (Matrix.single i j (1 : ℂ))ᴴ * Matrix.single i j (1 : ℂ) =
      Matrix.single j j (1 : ℂ) := by
  ext a b
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply,
      Matrix.single_apply]
    split_ifs <;> simp_all <;>
      (rename_i hne hconj
       exact hne (hconj.1.symm.trans hconj.2))
  · intro l _ hl
    rw [Matrix.conjTranspose_apply, Matrix.single_apply,
      if_neg fun hc => hl hc.1.symm, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Lean implementation helper: assembling weighted matrix units on the first
coordinate into a diagonal matrix. -/
lemma sum_smul_single_diag_fst (w : Fin d₁ × Fin d₂ → ℝ) :
    (∑ k : Fin d₁ × Fin d₂, w k • Matrix.single k.1 k.1 (1 : ℂ)) =
      Matrix.diagonal (fun i => (((∑ j, w (i, j) : ℝ)) : ℂ)) := by
  classical
  ext a b
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  have hterm : ∀ k : Fin d₁ × Fin d₂,
      (w k • Matrix.single k.1 k.1 (1 : ℂ)) a b =
        if k.1 = a ∧ a = b then ((w k : ℝ) : ℂ) else 0 := by
    intro k
    rw [Matrix.smul_apply, Matrix.single_apply]
    by_cases h1 : k.1 = a
    · by_cases h2 : a = b
      · rw [if_pos ⟨h1, h1.trans h2⟩, if_pos ⟨h1, h2⟩]
        rw [show w k • (1 : ℂ) = ((w k : ℝ) : ℂ) from by
          rw [Complex.real_smul, mul_one]]
      · rw [if_neg fun hc => h2 (h1.symm.trans hc.2),
          if_neg fun hc => h2 hc.2, smul_zero]
    · rw [if_neg fun hc => h1 hc.1, if_neg fun hc => h1 hc.1, smul_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · rw [show (((∑ j, w (a, j) : ℝ)) : ℂ) =
        ∑ j, ((w (a, j) : ℝ) : ℂ) from by push_cast; rfl]
      exact Finset.sum_congr rfl fun j _ => if_pos ⟨rfl, rfl⟩
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => if_neg fun hc => hi hc.1
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun k _ => if_neg fun hc => hab hc.2

/-- Lean implementation helper: the second-coordinate version. -/
lemma sum_smul_single_diag_snd (w : Fin d₁ × Fin d₂ → ℝ) :
    (∑ k : Fin d₁ × Fin d₂, w k • Matrix.single k.2 k.2 (1 : ℂ)) =
      Matrix.diagonal (fun j => (((∑ i, w (i, j) : ℝ)) : ℂ)) := by
  classical
  ext a b
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  have hterm : ∀ k : Fin d₁ × Fin d₂,
      (w k • Matrix.single k.2 k.2 (1 : ℂ)) a b =
        if k.2 = a ∧ a = b then ((w k : ℝ) : ℂ) else 0 := by
    intro k
    rw [Matrix.smul_apply, Matrix.single_apply]
    by_cases h1 : k.2 = a
    · by_cases h2 : a = b
      · rw [if_pos ⟨h1, h1.trans h2⟩, if_pos ⟨h1, h2⟩]
        rw [show w k • (1 : ℂ) = ((w k : ℝ) : ℂ) from by
          rw [Complex.real_smul, mul_one]]
      · rw [if_neg fun hc => h2 (h1.symm.trans hc.2),
          if_neg fun hc => h2 hc.2, smul_zero]
    · rw [if_neg fun hc => h1 hc.1, if_neg fun hc => h1 hc.1, smul_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rw [Fintype.sum_prod_type]
    rw [show (((∑ i, w (i, a) : ℝ)) : ℂ) =
      ∑ i, ((w (i, a) : ℝ) : ℂ) from by push_cast; rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single a]
    · exact if_pos ⟨rfl, rfl⟩
    · intro j _ hj
      exact if_neg fun hc => hj hc.1
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun k _ => if_neg fun hc => hab hc.2

/-- Lean implementation helper: the sample value as a single complex scaling. -/
lemma sparsifyValue_eq (B : Matrix (Fin d₁) (Fin d₂) ℂ) (k : Fin d₁ × Fin d₂) :
    sparsifyValue B k = (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) • B k.1 k.2 •
      Matrix.single k.1 k.2 (1 : ℂ) := by
  rw [sparsifyValue]
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Lean implementation helper: the value's Gram forms. -/
lemma sparsifyValue_mul_conjTranspose (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) :
    sparsifyValue B k * (sparsifyValue B k)ᴴ =
      (((sparsifyProb B k)⁻¹) ^ 2 * ‖B k.1 k.2‖ ^ 2) •
        Matrix.single k.1 k.1 (1 : ℂ) := by
  rw [sparsifyValue_eq]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
  rw [single_mul_conjTranspose_single, smul_smul, smul_smul, smul_smul]
  have h7 : (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) *
      star (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) * B k.1 k.2 *
      star (B k.1 k.2) =
      ((((sparsifyProb B k)⁻¹ ^ 2 * ‖B k.1 k.2‖ ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
    have h8 := Complex.mul_conj (B k.1 k.2)
    rw [show (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) *
      (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) * B k.1 k.2 *
      (starRingEnd ℂ) (B k.1 k.2) =
      (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) * (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) *
        (B k.1 k.2 * (starRingEnd ℂ) (B k.1 k.2)) from by ring, h8,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [h7]
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Lean implementation helper: the conjugate Gram form. -/
lemma conjTranspose_mul_sparsifyValue (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (k : Fin d₁ × Fin d₂) :
    (sparsifyValue B k)ᴴ * sparsifyValue B k =
      (((sparsifyProb B k)⁻¹) ^ 2 * ‖B k.1 k.2‖ ^ 2) •
        Matrix.single k.2 k.2 (1 : ℂ) := by
  rw [sparsifyValue_eq]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
  rw [conjTranspose_single_mul_single, smul_smul, smul_smul, smul_smul]
  have h7 : star (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) *
      (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) * star (B k.1 k.2) * B k.1 k.2 =
      ((((sparsifyProb B k)⁻¹ ^ 2 * ‖B k.1 k.2‖ ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
    have h8 := Complex.mul_conj (B k.1 k.2)
    rw [show (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) *
      (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (B k.1 k.2) *
      B k.1 k.2 =
      (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) * (((sparsifyProb B k)⁻¹ : ℝ) : ℂ) *
        (B k.1 k.2 * (starRingEnd ℂ) (B k.1 k.2)) from by ring, h8,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [h7]
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- **Book §6.3.3, second display chain** (C6-22): the second-moment
computation — `𝔼(RR*) = Σ_ij (|b_ij|²/p_ij)·E_ii ≼ 2d₂‖B‖_F²·I` and its
conjugate, packaged as `m₂(R) ≤ 2·max{d₁,d₂}·‖B‖_F²`.  Explicit source
displays. -/
theorem sparsify_second_moment_le {B : Matrix (Fin d₁) (Fin d₂) ℂ}
    (hB : B ≠ 0) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {J : Ω → Fin d₁ × Fin d₂} (hJ : Measurable J)
    (hJlaw : ∀ k, μ.real (J ⁻¹' {k}) = sparsifyProb B k) :
    secondMoment μ (fun ω => sparsifyValue B (J ω)) ≤
      2 * max (d₁ : ℝ) d₂ * frobeniusNorm B ^ 2 := by
  classical
  haveI : Nonempty (Fin d₁) := ⟨⟨0, hd₁⟩⟩
  haveI : Nonempty (Fin d₂) := ⟨⟨0, hd₂⟩⟩
  have hF := frobeniusNorm_pos hB
  have hL1 := entrywiseL1Norm_pos hB
  set c : Fin d₁ × Fin d₂ → ℝ :=
    fun k => sparsifyProb B k * ((sparsifyProb B k)⁻¹ ^ 2 * ‖B k.1 k.2‖ ^ 2)
    with hcdef
  have hc_nonneg : ∀ k, 0 ≤ c k := fun k => by
    show 0 ≤ sparsifyProb B k *
      ((sparsifyProb B k)⁻¹ ^ 2 * ‖B k.1 k.2‖ ^ 2)
    have := sparsifyProb_nonneg B k
    positivity
  have hc_le : ∀ k, c k ≤ 2 * frobeniusNorm B ^ 2 := by
    intro k
    show sparsifyProb B k * ((sparsifyProb B k)⁻¹ ^ 2 * ‖B k.1 k.2‖ ^ 2) ≤
      2 * frobeniusNorm B ^ 2
    by_cases hb : B k.1 k.2 = 0
    · rw [hb]
      norm_num
      positivity
    · have h3 : 0 < ‖B k.1 k.2‖ := norm_pos_iff.mpr hb
      have hp : 0 < sparsifyProb B k := by
        have h2 := sparsifyProb_lower₁ B k
        have h4 : 0 < ‖B k.1 k.2‖ / (2 * entrywiseL1Norm B) :=
          div_pos h3 (by linarith)
        linarith
      have h5 := sparsifyProb_lower₂ B k
      have h6 : sparsifyProb B k * ((sparsifyProb B k)⁻¹ ^ 2 *
          ‖B k.1 k.2‖ ^ 2) = ‖B k.1 k.2‖ ^ 2 / sparsifyProb B k := by
        field_simp
      rw [h6, div_le_iff₀ hp]
      calc ‖B k.1 k.2‖ ^ 2 =
          (‖B k.1 k.2‖ ^ 2 / (2 * frobeniusNorm B ^ 2)) *
            (2 * frobeniusNorm B ^ 2) := by
            field_simp
      _ ≤ sparsifyProb B k * (2 * frobeniusNorm B ^ 2) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 2 * frobeniusNorm B ^ 2 * sparsifyProb B k := by ring
  rw [secondMoment]
  -- first moment matrix, as a diagonal
  have hE1 : expectation μ (fun ω => sparsifyValue B (J ω) *
      (sparsifyValue B (J ω))ᴴ) =
      Matrix.diagonal (fun i => (((∑ j, c (i, j) : ℝ)) : ℂ)) := by
    have h8 := expectation_discrete (μ := μ) hJ measurable_id
      (fun k => sparsifyValue B k * (sparsifyValue B k)ᴴ)
    rw [show (fun ω => sparsifyValue B (J ω) * (sparsifyValue B (J ω))ᴴ) =
      fun ω => (fun k => sparsifyValue B k * (sparsifyValue B k)ᴴ) (J ω)
      from rfl, h8]
    rw [show (∑ k, μ.real (J ⁻¹' {k}) •
        (sparsifyValue B k * (sparsifyValue B k)ᴴ)) =
      ∑ k, c k • Matrix.single k.1 k.1 (1 : ℂ) from
      Finset.sum_congr rfl fun k _ => by
        rw [hJlaw k, sparsifyValue_mul_conjTranspose, smul_smul]]
    exact sum_smul_single_diag_fst c
  have hE2 : expectation μ (fun ω => (sparsifyValue B (J ω))ᴴ *
      sparsifyValue B (J ω)) =
      Matrix.diagonal (fun j => (((∑ i, c (i, j) : ℝ)) : ℂ)) := by
    have h8 := expectation_discrete (μ := μ) hJ measurable_id
      (fun k => (sparsifyValue B k)ᴴ * sparsifyValue B k)
    rw [show (fun ω => (sparsifyValue B (J ω))ᴴ * sparsifyValue B (J ω)) =
      fun ω => (fun k => (sparsifyValue B k)ᴴ * sparsifyValue B k) (J ω)
      from rfl, h8]
    rw [show (∑ k, μ.real (J ⁻¹' {k}) •
        ((sparsifyValue B k)ᴴ * sparsifyValue B k)) =
      ∑ k, c k • Matrix.single k.2 k.2 (1 : ℂ) from
      Finset.sum_congr rfl fun k _ => by
        rw [hJlaw k, conjTranspose_mul_sparsifyValue, smul_smul]]
    exact sum_smul_single_diag_snd c
  rw [hE1, hE2]
  have hnorm1 : ‖Matrix.diagonal (fun i : Fin d₁ =>
      (((∑ j, c (i, j) : ℝ)) : ℂ))‖ ≤
      2 * max (d₁ : ℝ) d₂ * frobeniusNorm B ^ 2 := by
    rw [l2_opNorm_diagonal_ofReal
      (fun i => Finset.sum_nonneg fun j _ => hc_nonneg (i, j))]
    refine Finset.sup'_le _ _ fun i _ => ?_
    calc (∑ j, c (i, j)) ≤ ∑ _j : Fin d₂, 2 * frobeniusNorm B ^ 2 :=
          Finset.sum_le_sum fun j _ => hc_le (i, j)
    _ = (d₂ : ℝ) * (2 * frobeniusNorm B ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
    _ ≤ max (d₁ : ℝ) d₂ * (2 * frobeniusNorm B ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = 2 * max (d₁ : ℝ) d₂ * frobeniusNorm B ^ 2 := by ring
  have hnorm2 : ‖Matrix.diagonal (fun j : Fin d₂ =>
      (((∑ i, c (i, j) : ℝ)) : ℂ))‖ ≤
      2 * max (d₁ : ℝ) d₂ * frobeniusNorm B ^ 2 := by
    rw [l2_opNorm_diagonal_ofReal
      (fun j => Finset.sum_nonneg fun i _ => hc_nonneg (i, j))]
    refine Finset.sup'_le _ _ fun j _ => ?_
    calc (∑ i, c (i, j)) ≤ ∑ _i : Fin d₁, 2 * frobeniusNorm B ^ 2 :=
          Finset.sum_le_sum fun i _ => hc_le (i, j)
    _ = (d₁ : ℝ) * (2 * frobeniusNorm B ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
    _ ≤ max (d₁ : ℝ) d₂ * (2 * frobeniusNorm B ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = 2 * max (d₁ : ℝ) d₂ * frobeniusNorm B ^ 2 := by ring
  exact max_le hnorm1 hnorm2

end SecondMomentBound


section MainBound

variable {d₁ d₂ : ℕ}

/-- **Book §6.3.1** (C6-21): the sampling estimator is unbiased, `𝔼R = B` —
"It is immediate that `𝔼R = Σ_ij p_ij⁻¹ b_ij E_ij · p_ij = B`."  Explicit
source computation. -/
theorem expectation_sparsifyEstimator {B : Matrix (Fin d₁) (Fin d₂) ℂ}
    (hB : B ≠ 0) {J : Ω → Fin d₁ × Fin d₂} (hJ : Measurable J)
    (hJlaw : ∀ k, μ.real (J ⁻¹' {k}) = sparsifyProb B k) :
    expectation μ (fun ω => sparsifyValue B (J ω)) = B := by
  rw [expectation_discrete (μ := μ) hJ measurable_id (sparsifyValue B)]
  rw [Finset.sum_congr rfl fun k _ => by rw [hJlaw k]]
  exact sum_sparsifyProb_smul_value hB

/-- **Book (6.3.2)** (C6-22):

`𝔼‖R̄_n − B‖ ≤ √(4‖B‖_F²·max{d₁,d₂}·log(d₁+d₂)/n) + 4‖B‖_{ℓ1}log(d₁+d₂)/(3n)`.

Explicit source display; §6.3.3 analysis (Corollary 6.2.1 with `L = 2‖B‖_{ℓ1}`
and `m₂(R) ≤ 2·max{d₁,d₂}·‖B‖_F²`). -/
theorem sparsification_error_bound {B : Matrix (Fin d₁) (Fin d₂) ℂ}
    (hB : B ≠ 0) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) {nn : ℕ} (hnn : 0 < nn)
    {J : Ω → Fin d₁ × Fin d₂} (hJ : Measurable J)
    (hJlaw : ∀ k, μ.real (J ⁻¹' {k}) = sparsifyProb B k)
    {R : Fin nn → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k)
      (fun ω => sparsifyValue B (J ω)) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤
      Real.sqrt (4 * frobeniusNorm B ^ 2 * max (d₁ : ℝ) d₂ *
        Real.log ((d₁ : ℝ) + d₂) / nn) +
      4 * entrywiseL1Norm B * Real.log ((d₁ : ℝ) + d₂) / (3 * nn) := by
  classical
  haveI : Nonempty (Fin d₁) := ⟨⟨0, hd₁⟩⟩
  haveI : Nonempty (Fin d₂) := ⟨⟨0, hd₂⟩⟩
  haveI : Nonempty (Fin d₁ ⊕ Fin d₂) := ⟨Sum.inl ⟨0, hd₁⟩⟩
  have hL1 := entrywiseL1Norm_pos hB
  have hR₀m : Measurable fun ω => sparsifyValue B (J ω) :=
    (measurable_of_countable (sparsifyValue B)).comp hJ
  have hbd : ∀ ω, ‖sparsifyValue B (J ω)‖ ≤ 2 * entrywiseL1Norm B :=
    fun ω => sparsify_norm_le hB (J ω)
  have hmean := expectation_sparsifyEstimator (μ := μ) hB hJ hJlaw
  have h := matrix_sampling_estimator_expectation (μ := μ) hnn hR₀m hbd hmean
    hmeas hid hind
  have hM := sparsify_second_moment_le (μ := μ) hB hd₁ hd₂ hJ hJlaw
  have hM0 : 0 ≤ secondMoment μ (fun ω => sparsifyValue B (J ω)) :=
    secondMoment_nonneg _
  have hD0 : (0 : ℝ) ≤ Real.log ((Fintype.card (Fin d₁) : ℝ) +
      Fintype.card (Fin d₂)) := by
    refine Real.log_nonneg ?_
    rw [Fintype.card_fin, Fintype.card_fin]
    have : (1 : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hd₁
    have : (0 : ℝ) ≤ (d₂ : ℝ) := by positivity
    linarith
  refine h.trans ?_
  rw [show ((Fintype.card (Fin d₁) : ℝ)) = (d₁ : ℝ) from by
      rw [Fintype.card_fin],
    show ((Fintype.card (Fin d₂) : ℝ)) = (d₂ : ℝ) from by
      rw [Fintype.card_fin]]
  rw [show ((Fintype.card (Fin d₁) : ℝ)) = (d₁ : ℝ) from by
      rw [Fintype.card_fin],
    show ((Fintype.card (Fin d₂) : ℝ)) = (d₂ : ℝ) from by
      rw [Fintype.card_fin]] at hD0
  refine add_le_add ?_ (le_of_eq ?_)
  · refine Real.sqrt_le_sqrt ?_
    have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
    rw [div_le_div_iff₀ hnR hnR]
    have hDlog : (0 : ℝ) ≤ Real.log ((d₁ : ℝ) + d₂) := hD0
    have h1 : 2 * secondMoment μ (fun ω => sparsifyValue B (J ω)) *
        Real.log ((d₁ : ℝ) + d₂) ≤
        2 * (2 * max (d₁ : ℝ) d₂ * frobeniusNorm B ^ 2) *
          Real.log ((d₁ : ℝ) + d₂) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM (by norm_num)) hDlog
    nlinarith [mul_le_mul_of_nonneg_right h1 hnR.le]
  · ring

/-- **Book §6.3.2, relative-error chain** (C6-23): if the sparsity level
satisfies `n ≥ ε⁻²·srank(B)·max{d₁,d₂}·log(d₁+d₂)` with `ε ∈ (0,1]`, then
`𝔼‖R̄_n − B‖ ≤ 4ε·‖B‖` (the book's "relative error ≤ 4ε", multiplied out by
`‖B‖`; it uses `‖B‖_{ℓ1} ≤ √(d₁d₂)‖B‖_F ≤ max{d₁,d₂}‖B‖_F` (2.1.30) and
`1 ≤ srank(B)`). Explicit source displays. -/
theorem sparsification_relative_error {B : Matrix (Fin d₁) (Fin d₂) ℂ}
    (hB : B ≠ 0) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) {nn : ℕ} (hnn : 0 < nn)
    {J : Ω → Fin d₁ × Fin d₂} (hJ : Measurable J)
    (hJlaw : ∀ k, μ.real (J ⁻¹' {k}) = sparsifyProb B k)
    {R : Fin nn → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k)
      (fun ω => sparsifyValue B (J ω)) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcost : ε⁻¹ ^ 2 * stableRank B * max (d₁ : ℝ) d₂ *
      Real.log ((d₁ : ℝ) + d₂) ≤ nn) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤ 4 * ε * ‖B‖ := by
  classical
  have h := sparsification_error_bound (μ := μ) hB hd₁ hd₂ hnn hJ hJlaw hmeas
    hid hind
  refine h.trans ?_
  set F : ℝ := frobeniusNorm B with hFdef
  set D : ℝ := Real.log ((d₁ : ℝ) + d₂) with hDdef
  set M : ℝ := max (d₁ : ℝ) d₂ with hMdef
  have hF : 0 < F := frobeniusNorm_pos hB
  have hb : 0 < ‖B‖ := by
    rcases eq_or_lt_of_le (norm_nonneg B) with h0 | h0
    · exact absurd (norm_eq_zero.mp h0.symm) hB
    · exact h0
  have hbF : ‖B‖ ≤ F := l2_opNorm_le_frobeniusNorm B
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hd₁
    have h2 : (0 : ℝ) ≤ (d₂ : ℝ) := by positivity
    linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]
    have h1 : (1 : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hd₁
    exact le_max_of_le_left h1
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  -- the cost hypothesis, multiplied out
  have hkey : F ^ 2 * M * D ≤ ε ^ 2 * ‖B‖ ^ 2 * nn := by
    have h1 : stableRank B = F ^ 2 / ‖B‖ ^ 2 := rfl
    have h2 := hcost
    rw [h1] at h2
    have h3 : ε⁻¹ ^ 2 * (F ^ 2 / ‖B‖ ^ 2) * M * D =
        F ^ 2 * M * D / (ε ^ 2 * ‖B‖ ^ 2) := by
      field_simp
    rw [h3, div_le_iff₀ (by positivity)] at h2
    nlinarith [h2]
  -- first term
  have hterm1 : Real.sqrt (4 * F ^ 2 * M * D / nn) ≤ 2 * ε * ‖B‖ := by
    rw [show (2 * ε * ‖B‖ : ℝ) = Real.sqrt ((2 * ε * ‖B‖) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hnR]
    nlinarith [hkey]
  -- second term: `ℓ1 ≤ M·F`
  have hl1 : entrywiseL1Norm B ≤ M * F := by
    refine (entrywiseL1Norm_le B).trans ?_
    rw [Fintype.card_fin, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_right ?_ hF.le
    rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    refine Real.sqrt_le_sqrt ?_
    have h4 : (d₁ : ℝ) ≤ M := le_max_left _ _
    have h5 : (d₂ : ℝ) ≤ M := le_max_right _ _
    have h6 : (0 : ℝ) ≤ (d₁ : ℝ) := by positivity
    have h7 : (0 : ℝ) ≤ (d₂ : ℝ) := by positivity
    nlinarith
  have hterm2 : 4 * entrywiseL1Norm B * D / (3 * nn) ≤ 2 * ε * ‖B‖ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * nn)]
    -- `4·ℓ1·D ≤ 4·M·F·D` and `4·M·F·D ≤ 6·ε·b·n` from `hkey`, `b ≤ F ≤ …`
    have h9 : 4 * entrywiseL1Norm B * D ≤ 4 * (M * F) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl1 (by norm_num)) hD0
    -- from `hkey`: `M·D·F² ≤ ε²b²n`, so `M·D·F ≤ ε²b²n/F ≤ ε²·b·n` (b ≤ F)
    have h10 : M * D * F ^ 2 ≤ ε ^ 2 * ‖B‖ ^ 2 * nn := by nlinarith [hkey]
    have h11 : 4 * (M * F) * D * F ≤ 4 * (ε ^ 2 * ‖B‖ ^ 2 * nn) := by
      nlinarith [h10]
    -- divide by `F` and use `b ≤ F`, `ε ≤ 1`
    have h12 : 4 * (M * F) * D ≤ 4 * ε ^ 2 * ‖B‖ ^ 2 * nn / F := by
      rw [le_div_iff₀ hF]
      nlinarith [h11]
    have h13 : 4 * ε ^ 2 * ‖B‖ ^ 2 * nn / F ≤ 4 * ε ^ 2 * ‖B‖ * nn := by
      rw [div_le_iff₀ hF]
      have h13a : 4 * ε ^ 2 * nn * (‖B‖ * ‖B‖) ≤ 4 * ε ^ 2 * nn * (‖B‖ * F) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hbF hb.le
      nlinarith [h13a]
    have h14 : 4 * ε ^ 2 * ‖B‖ * nn ≤ 2 * ε * ‖B‖ * (3 * nn) := by
      have h14a : 4 * (ε * ε) * (‖B‖ * nn) ≤ 4 * (ε * 1) * (‖B‖ * nn) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hε1 hε.le
      nlinarith [h14a, mul_nonneg (mul_nonneg hε.le hb.le) hnR.le]
    exact ((h9.trans h12).trans h13).trans h14
  linarith [hterm1, hterm2]

end MainBound

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Randomized matrix multiplication (Tropp §6.4)

The Magen–Zouzias randomized product approximation: view `BC = Σ_j b_{:j}c_{j:}`
(6.4.2), sample the outer products with probabilities (6.4.3)
`p_j = (‖b_{:j}‖² + ‖c_{j:}‖²)/(‖B‖_F² + ‖C‖_F²)`, and average `n` copies.

* `mul_eq_sum_outer` — the outer-product representation (6.4.2);
* `matmulProb`, `matmulValue`, `matmulProb_sum_eq_one` (C6-24; "we can
  easily check that (p_j) forms a bonafide probability distribution");
* `expectation_matmulEstimator` — `𝔼R = BC` (C6-24, "It is straightforward");
* `matmul_norm_le` — `‖R‖ ≤ (‖B‖_F² + ‖C‖_F²)/2` (AM–GM step, §6.4.3);
* `matmul_second_moment_le` — `m₂(R) ≤ (‖B‖_F²+‖C‖_F²)·max{‖BB*‖,‖C*C‖}`
  (§6.4.3);
* `randomized_matmul_error_bound` — the error estimate **Book (6.4.5)** under
  the normalization `‖B‖ = ‖C‖ = 1`, in terms
  of the average stable rank `asr = (srank B + srank C)/2`;
* `randomized_matmul_relative_error` — the §6.4.2 consequence
  `n ≥ ε⁻²·asr·log(d₁+d₂)` ⟹ error `≤ 2ε + (2/3)ε²`.

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [IsProbabilityMeasure μ]

section OuterProducts

variable {d₁ d₂ N : ℕ}

/-- Lean implementation helper: the row-Gram summand `c_{j:}* c_{j:}`,
realized as `C* E_jj C` (the mirror of `colGram`). -/
noncomputable def rowGram (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) :
    Matrix (Fin d₂) (Fin d₂) ℂ :=
  Cᴴ * Matrix.single j j (1 : ℂ) * C

/-- Lean implementation helper: entrywise formula for a row-Gram summand. -/
lemma rowGram_apply (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N)
    (a b : Fin d₂) : rowGram C j a b = star (C j a) * C j b := by
  rw [rowGram, Matrix.mul_apply]
  have h1 : ∀ l, (Cᴴ * Matrix.single j j (1 : ℂ)) a l * C l b =
      (if l = j then star (C j a) else 0) * C l b := by
    intro l
    congr 1
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.conjTranspose_apply, Matrix.single_apply]
      by_cases hlj : j = l
      · subst hlj
        rw [if_pos ⟨rfl, rfl⟩, if_pos rfl, mul_one]
      · rw [if_neg fun hc => hlj hc.2, if_neg fun hc => hlj hc.symm, mul_zero]
    · intro m _ hm
      rw [Matrix.single_apply, if_neg fun hc => hm hc.1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro l _ hl
    rw [if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Lean implementation helper: `rowGram` is positive semidefinite. -/
lemma posSemidef_rowGram (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) :
    (rowGram C j).PosSemidef := by
  have hE : (Matrix.single j j (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ).PosSemidef := by
    have h := posSemidef_colGram (1 : Matrix (Fin N) (Fin N) ℂ) j
    rwa [colGram, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
      at h
  have h := hE.mul_mul_conjTranspose_same Cᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- Lean implementation helper: `Σ_j colGram B j = BB*`. -/
lemma sum_colGram (B : Matrix (Fin d₁) (Fin N) ℂ) :
    (∑ j, colGram B j) = B * Bᴴ := by
  rw [show (∑ j, colGram B j) = ∑ j, B * Matrix.single j j (1 : ℂ) * Bᴴ from
    Finset.sum_congr rfl fun j _ => rfl]
  rw [show (∑ j : Fin N, B * Matrix.single j j (1 : ℂ) * Bᴴ) =
    B * (∑ j : Fin N, Matrix.single j j (1 : ℂ)) * Bᴴ from by
      rw [Matrix.mul_sum, Matrix.sum_mul]]
  rw [sum_single_diag_one, Matrix.mul_one]

/-- Lean implementation helper: `Σ_j rowGram C j = C*C`. -/
lemma sum_rowGram (C : Matrix (Fin N) (Fin d₂) ℂ) :
    (∑ j, rowGram C j) = Cᴴ * C := by
  rw [show (∑ j, rowGram C j) = ∑ j, Cᴴ * Matrix.single j j (1 : ℂ) * C from
    Finset.sum_congr rfl fun j _ => rfl]
  rw [show (∑ j : Fin N, Cᴴ * Matrix.single j j (1 : ℂ) * C) =
    Cᴴ * (∑ j : Fin N, Matrix.single j j (1 : ℂ)) * C from by
      rw [Matrix.mul_sum, Matrix.sum_mul]]
  rw [sum_single_diag_one, Matrix.mul_one]

/-- **Book (6.4.2)** (C6-24): the product as
a sum of outer products, `BC = Σ_j b_{:j} c_{j:}`.  Explicit source display
(the outer product is `vecMulVec`). -/
lemma mul_eq_sum_outer (B : Matrix (Fin d₁) (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin d₂) ℂ) :
    B * C = ∑ j, Matrix.vecMulVec (fun i => B i j) (fun k => C j k) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.vecMulVec_apply]

/-- Lean implementation helper: the operator norm of an outer product is at
most the product of the vector norms. -/
lemma l2_opNorm_vecMulVec_le (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) :
    ‖Matrix.vecMulVec u v‖ ≤ l2norm u * l2norm v := by
  refine l2_opNorm_le_of_forall_dotProduct _
    (mul_nonneg (l2norm_nonneg u) (l2norm_nonneg v)) fun x y => ?_
  have h1 : star x ⬝ᵥ (Matrix.vecMulVec u v *ᵥ y) =
      (star x ⬝ᵥ u) * (v ⬝ᵥ y) := by
    rw [show (Matrix.vecMulVec u v *ᵥ y) = fun i => u i * (v ⬝ᵥ y) from
      funext fun i => by
        rw [show (Matrix.vecMulVec u v *ᵥ y) i =
          ∑ k, Matrix.vecMulVec u v i k * y k from rfl]
        rw [show (v ⬝ᵥ y) = ∑ k, v k * y k from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Matrix.vecMulVec_apply]
          ring]
    rw [show star x ⬝ᵥ (fun i => u i * (v ⬝ᵥ y)) =
      ∑ i, star x i * (u i * (v ⬝ᵥ y)) from rfl]
    rw [show (star x ⬝ᵥ u) = ∑ i, star x i * u i from rfl, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, norm_mul]
  have h2 : ‖star x ⬝ᵥ u‖ ≤ l2norm x * l2norm u := norm_dotProduct_le x u
  have h3 : ‖v ⬝ᵥ y‖ ≤ l2norm v * l2norm y := by
    have h4 := norm_dotProduct_le (star v) y
    have hsv : l2norm (star v) = l2norm v := by
      rw [l2norm_eq_sqrt_sum, l2norm_eq_sqrt_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by
        rw [Pi.star_apply, norm_star]
    rwa [star_star, hsv] at h4
  calc ‖star x ⬝ᵥ u‖ * ‖v ⬝ᵥ y‖ ≤
      (l2norm x * l2norm u) * (l2norm v * l2norm y) := by
        exact mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg (l2norm_nonneg _) (l2norm_nonneg _))
  _ = l2norm u * l2norm v * l2norm x * l2norm y := by ring

end OuterProducts

section MatmulModel

variable {d₁ d₂ N : ℕ}

/-- Lean implementation helper: the squared row norms of the second factor. -/
noncomputable def rowNormSq (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) : ℝ :=
  ∑ k, ‖C j k‖ ^ 2

/-- Lean implementation helper: nonnegativity of a squared row norm. -/
lemma rowNormSq_nonneg (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) :
    0 ≤ rowNormSq C j :=
  Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **Book (6.4.3)** (C6-24): the sampling
probabilities `p_j = (‖b_{:j}‖² + ‖c_{j:}‖²)/(‖B‖_F² + ‖C‖_F²)`.  Explicit
source declaration. -/
noncomputable def matmulProb (B : Matrix (Fin d₁) (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) : ℝ :=
  (colNormSq B j + rowNormSq C j) /
    (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2)

/-- **Book §6.4.1** (C6-24): the rank-one sample `R = p_j⁻¹ b_{:j} c_{j:}`
(with the `0/0 = 0` convention).  Explicit source declaration. -/
noncomputable def matmulValue (B : Matrix (Fin d₁) (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) :
    Matrix (Fin d₁) (Fin d₂) ℂ :=
  (matmulProb B C j)⁻¹ •
    Matrix.vecMulVec (fun i => B i j) (fun k => C j k)

/-- Lean implementation helper: nonnegativity of each matrix-product sampling probability. -/
lemma matmulProb_nonneg (B : Matrix (Fin d₁) (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin d₂) ℂ) (j : Fin N) : 0 ≤ matmulProb B C j := by
  rw [matmulProb]
  have h1 := colNormSq_nonneg B j
  have h2 := rowNormSq_nonneg C j
  exact div_nonneg (by linarith) (by positivity)

/-- Lean implementation helper: the column norms sum to the squared Frobenius
norm. -/
lemma sum_colNormSq (B : Matrix (Fin d₁) (Fin N) ℂ) :
    (∑ j, colNormSq B j) = frobeniusNorm B ^ 2 := by
  rw [frobeniusNorm_sq]
  rw [Finset.sum_comm]
  rfl

/-- Lean implementation helper: the row norms sum to the squared Frobenius norm. -/
lemma sum_rowNormSq (C : Matrix (Fin N) (Fin d₂) ℂ) :
    (∑ j, rowNormSq C j) = frobeniusNorm C ^ 2 := by
  rw [frobeniusNorm_sq]
  rfl

/-- **Book §6.4.1** (C6-24): "(p_j) forms a bonafide probability
distribution." Implicit source claim.

**Author note.** This Lean lemma assumes `B ≠ 0`; see
`matmulProb_sum_eq_one_of_pair_ne_zero` for the source-faithful nondegenerate
form, where only the pair may not vanish simultaneously. -/
theorem matmulProb_sum_eq_one {B : Matrix (Fin d₁) (Fin N) ℂ}
    {C : Matrix (Fin N) (Fin d₂) ℂ} (hB : B ≠ 0) :
    ∑ j, matmulProb B C j = 1 := by
  have hF := frobeniusNorm_pos hB
  have hden : 0 < frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 := by
    have := frobeniusNorm_nonneg C
    nlinarith
  rw [show (∑ j, matmulProb B C j) = (∑ j, (colNormSq B j + rowNormSq C j)) /
      (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) from by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => rfl]
  rw [Finset.sum_add_distrib, sum_colNormSq, sum_rowNormSq]
  field_simp

/-- **Book §6.4.1**, source-faithful nondegenerate form of the assertion that
`(p_j)` is a probability distribution.  Unlike `matmulProb_sum_eq_one`, this
allows `B = 0, C ≠ 0`; only the pair may not vanish simultaneously.

At `B = C = 0` the displayed denominator is zero and Lean's totalized
division makes every `p_j` zero, so no normalization theorem is asserted for
that source-degenerate corner. -/
theorem matmulProb_sum_eq_one_of_pair_ne_zero
    {B : Matrix (Fin d₁) (Fin N) ℂ} {C : Matrix (Fin N) (Fin d₂) ℂ}
    (hpair : B ≠ 0 ∨ C ≠ 0) :
    ∑ j, matmulProb B C j = 1 := by
  have hden : 0 < frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 := by
    rcases hpair with hB | hC
    · have hF := frobeniusNorm_pos hB
      have hC0 := frobeniusNorm_nonneg C
      nlinarith
    · have hF := frobeniusNorm_pos hC
      have hB0 := frobeniusNorm_nonneg B
      nlinarith
  rw [show (∑ j, matmulProb B C j) =
      (∑ j, (colNormSq B j + rowNormSq C j)) /
        (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) from by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => rfl]
  rw [Finset.sum_add_distrib, sum_colNormSq, sum_rowNormSq]
  exact div_self hden.ne'

/-- Lean implementation helper: a zero probability forces a zero sample. -/
lemma matmulValue_eq_zero_of_prob_eq_zero {B : Matrix (Fin d₁) (Fin N) ℂ}
    {C : Matrix (Fin N) (Fin d₂) ℂ} (hB : B ≠ 0) {j : Fin N}
    (hp : matmulProb B C j = 0) :
    Matrix.vecMulVec (fun i => B i j) (fun k => C j k) = 0 := by
  have hF := frobeniusNorm_pos hB
  have hden : 0 < frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 := by
    have := frobeniusNorm_nonneg C
    nlinarith
  have hnum : colNormSq B j + rowNormSq C j = 0 := by
    rw [matmulProb, div_eq_zero_iff] at hp
    rcases hp with h | h
    · exact h
    · exact absurd h (ne_of_gt hden)
  have hcol : colNormSq B j = 0 := by
    have h1 := colNormSq_nonneg B j
    have h2 := rowNormSq_nonneg C j
    linarith
  have hrow : rowNormSq C j = 0 := by
    have h1 := colNormSq_nonneg B j
    linarith
  ext i k
  rw [Matrix.vecMulVec_apply, Matrix.zero_apply]
  have hBij : B i j = 0 := by
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      sq_nonneg ‖B i j‖).mp hcol i (Finset.mem_univ i)
    have h4 : ‖B i j‖ = 0 := by nlinarith [norm_nonneg (B i j)]
    exact norm_eq_zero.mp h4
  rw [hBij, zero_mul]

/-- **Book §6.4.1** (C6-24): the estimator is unbiased, `𝔼R = BC`.  Explicit
source computation ("It is straightforward to compute the expectation").

**Author note.** This form retains the earlier `B ≠ 0` premise for
compatibility; see `expectation_matmulEstimator_book` for the unrestricted
source-faithful counterpart. -/
theorem expectation_matmulEstimator {B : Matrix (Fin d₁) (Fin N) ℂ}
    {C : Matrix (Fin N) (Fin d₂) ℂ} (hB : B ≠ 0)
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j) :
    expectation μ (fun ω => matmulValue B C (J ω)) = B * C := by
  rw [expectation_discrete (μ := μ) hJ measurable_id (matmulValue B C)]
  rw [Finset.sum_congr rfl fun j _ => by rw [hJlaw j]]
  rw [mul_eq_sum_outer]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [matmulValue, smul_smul]
  by_cases hp : matmulProb B C j = 0
  · rw [matmulValue_eq_zero_of_prob_eq_zero hB hp, smul_zero]
  · rw [mul_inv_cancel₀ hp, one_smul]

/-- **Book §6.4.1**: the matrix-product estimator is unbiased, including the
valid case `B = 0, C ≠ 0`.  This is the unrestricted counterpart of
`expectation_matmulEstimator`; no nonzero hypothesis is needed for the
algebraic expectation identity itself. -/
theorem expectation_matmulEstimator_book
    {B : Matrix (Fin d₁) (Fin N) ℂ} {C : Matrix (Fin N) (Fin d₂) ℂ}
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j) :
    expectation μ (fun ω => matmulValue B C (J ω)) = B * C := by
  by_cases hB : B = 0
  · subst B
    have hvalue : ∀ j, matmulValue (0 : Matrix (Fin d₁) (Fin N) ℂ) C j = 0 := by
      intro j
      rw [matmulValue]
      apply smul_eq_zero.mpr
      right
      ext i k
      simp [Matrix.vecMulVec_apply]
    rw [show (fun ω => matmulValue (0 : Matrix (Fin d₁) (Fin N) ℂ) C (J ω)) =
        fun _ : Ω => (0 : Matrix (Fin d₁) (Fin d₂) ℂ) from by
      funext ω
      exact hvalue (J ω), expectation_const (μ := μ), Matrix.zero_mul]
  · exact expectation_matmulEstimator hB hJ hJlaw

end MatmulModel

section MatmulAnalysis

variable {d₁ d₂ N : ℕ}
variable {B : Matrix (Fin d₁) (Fin N) ℂ} {C : Matrix (Fin N) (Fin d₂) ℂ}

/-- **Book §6.4.3, first display** (C6-25): the uniform bound
`‖R‖ ≤ (‖B‖_F² + ‖C‖_F²)/2` via the AM–GM inequality.  Explicit source
display. -/
theorem matmul_norm_le (hB : B ≠ 0) (j : Fin N) :
    ‖matmulValue B C j‖ ≤
      (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) / 2 := by
  have hF := frobeniusNorm_pos hB
  have hden : 0 < frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 := by
    have := frobeniusNorm_nonneg C
    nlinarith
  by_cases hp : matmulProb B C j = 0
  · rw [matmulValue, matmulValue_eq_zero_of_prob_eq_zero hB hp, smul_zero,
      norm_zero]
    positivity
  · have hp' : 0 < matmulProb B C j :=
      lt_of_le_of_ne (matmulProb_nonneg B C j) (Ne.symm hp)
    rw [matmulValue, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hp'.le)]
    have h1 := l2_opNorm_vecMulVec_le (fun i => B i j) (fun k => C j k)
    have hu : l2norm (fun i => B i j) ^ 2 = colNormSq B j := by
      rw [l2norm_sq]
      rfl
    have hv : l2norm (fun k => C j k) ^ 2 = rowNormSq C j := by
      rw [l2norm_sq]
      rfl
    have hAMGM : l2norm (fun i => B i j) * l2norm (fun k => C j k) ≤
        (colNormSq B j + rowNormSq C j) / 2 := by
      nlinarith [sq_nonneg (l2norm (fun i => B i j) -
        l2norm (fun k => C j k)), hu, hv]
    have hnum : 0 < colNormSq B j + rowNormSq C j := by
      by_contra h
      push Not at h
      have h2 : colNormSq B j + rowNormSq C j = 0 := le_antisymm h
        (by linarith [colNormSq_nonneg B j, rowNormSq_nonneg C j])
      exact hp (by rw [matmulProb, h2, zero_div])
    have hpval : (matmulProb B C j)⁻¹ =
        (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) /
          (colNormSq B j + rowNormSq C j) := by
      rw [matmulProb]
      rw [inv_div]
    rw [hpval]
    calc (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) /
        (colNormSq B j + rowNormSq C j) *
        ‖Matrix.vecMulVec (fun i => B i j) (fun k => C j k)‖
        ≤ (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) /
          (colNormSq B j + rowNormSq C j) *
          ((colNormSq B j + rowNormSq C j) / 2) := by
          refine mul_le_mul_of_nonneg_left (h1.trans hAMGM) ?_
          positivity
    _ = (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) / 2 := by
          field_simp
    
/-- Lean implementation helper: the Gram form of the sample,
`RR* = (p⁻²‖c_{j:}‖²)·b_{:j}b_{:j}*`. -/
lemma matmulValue_mul_conjTranspose (j : Fin N) :
    matmulValue B C j * (matmulValue B C j)ᴴ =
      ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j) • colGram B j := by
  ext a b
  rw [Matrix.mul_apply]
  have hterm : ∀ k, matmulValue B C j a k * (matmulValue B C j)ᴴ k b =
      ((((matmulProb B C j)⁻¹ ^ 2 : ℝ)) : ℂ) *
        (B a j * star (B b j)) * ((‖C j k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Matrix.conjTranspose_apply]
    rw [show matmulValue B C j a k =
      (((matmulProb B C j)⁻¹ : ℝ) : ℂ) * (B a j * C j k) from by
        rw [matmulValue, Matrix.smul_apply, Matrix.vecMulVec_apply,
          Complex.real_smul]]
    rw [show matmulValue B C j b k =
      (((matmulProb B C j)⁻¹ : ℝ) : ℂ) * (B b j * C j k) from by
        rw [matmulValue, Matrix.smul_apply, Matrix.vecMulVec_apply,
          Complex.real_smul]]
    have h8 : C j k * (starRingEnd ℂ) (C j k) = ((‖C j k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [star_mul', star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [show (((matmulProb B C j)⁻¹ : ℝ) : ℂ) * (B a j * C j k) *
      ((((matmulProb B C j)⁻¹ : ℝ) : ℂ) *
        ((starRingEnd ℂ) (B b j) * (starRingEnd ℂ) (C j k))) =
      ((((matmulProb B C j)⁻¹ : ℝ) : ℂ) *
        (((matmulProb B C j)⁻¹ : ℝ) : ℂ)) *
        (B a j * (starRingEnd ℂ) (B b j)) *
        (C j k * (starRingEnd ℂ) (C j k)) from by ring, h8]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  rw [Matrix.smul_apply, colGram_apply]
  rw [show (∑ k, ((‖C j k‖ ^ 2 : ℝ) : ℂ)) = ((rowNormSq C j : ℝ) : ℂ) from by
    rw [rowNormSq]
    push_cast
    rfl]
  rw [Complex.real_smul]
  push_cast
  ring

/-- Lean implementation helper: the conjugate Gram form,
`R*R = (p⁻²‖b_{:j}‖²)·c_{j:}*c_{j:}`. -/
lemma conjTranspose_mul_matmulValue (j : Fin N) :
    (matmulValue B C j)ᴴ * matmulValue B C j =
      ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j) • rowGram C j := by
  ext a b
  rw [Matrix.mul_apply]
  have hterm : ∀ i, (matmulValue B C j)ᴴ a i * matmulValue B C j i b =
      ((((matmulProb B C j)⁻¹ ^ 2 : ℝ)) : ℂ) *
        (star (C j a) * C j b) * ((‖B i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Matrix.conjTranspose_apply]
    rw [show matmulValue B C j i a =
      (((matmulProb B C j)⁻¹ : ℝ) : ℂ) * (B i j * C j a) from by
        rw [matmulValue, Matrix.smul_apply, Matrix.vecMulVec_apply,
          Complex.real_smul]]
    rw [show matmulValue B C j i b =
      (((matmulProb B C j)⁻¹ : ℝ) : ℂ) * (B i j * C j b) from by
        rw [matmulValue, Matrix.smul_apply, Matrix.vecMulVec_apply,
          Complex.real_smul]]
    have h8 : B i j * (starRingEnd ℂ) (B i j) = ((‖B i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [star_mul', star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [show (((matmulProb B C j)⁻¹ : ℝ) : ℂ) *
      ((starRingEnd ℂ) (B i j) * (starRingEnd ℂ) (C j a)) *
      ((((matmulProb B C j)⁻¹ : ℝ) : ℂ) * (B i j * C j b)) =
      ((((matmulProb B C j)⁻¹ : ℝ) : ℂ) *
        (((matmulProb B C j)⁻¹ : ℝ) : ℂ)) *
        ((starRingEnd ℂ) (C j a) * C j b) *
        (B i j * (starRingEnd ℂ) (B i j)) from by ring, h8]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  rw [Matrix.smul_apply, rowGram_apply]
  rw [show (∑ i, ((‖B i j‖ ^ 2 : ℝ) : ℂ)) = ((colNormSq B j : ℝ) : ℂ) from by
    rw [colNormSq]
    push_cast
    rfl]
  rw [Complex.real_smul]
  push_cast
  ring

end MatmulAnalysis

section MatmulMain

variable {d₁ d₂ N : ℕ}
variable {B : Matrix (Fin d₁) (Fin N) ℂ} {C : Matrix (Fin N) (Fin d₂) ℂ}

/-- Lean implementation helper: scaling a psd matrix is monotone in the
scalar. -/
lemma smul_le_smul_of_posSemidef {p' : Type*} [Fintype p'] [DecidableEq p']
    {P : Matrix p' p' ℂ} (hP : P.PosSemidef) {a c : ℝ} (hac : a ≤ c) :
    a • P ≤ c • P := by
  rw [← sub_nonneg, ← sub_smul]
  have h0 : (0 : Matrix p' p' ℂ) ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP
  have h1 := real_smul_loewner_mono (by linarith : (0 : ℝ) ≤ c - a) h0
  rwa [smul_zero] at h1

/-- **Book §6.4.3, second display chain** (C6-25): the second-moment bound —
`𝔼(RR*) ≼ (‖B‖_F²+‖C‖_F²)·BB*` and `𝔼(R*R) ≼ (‖B‖_F²+‖C‖_F²)·C*C`, packaged
as `m₂(R) ≤ (‖B‖_F²+‖C‖_F²)·max{‖BB*‖, ‖C*C‖}`.  Explicit source displays
("The semidefinite relation holds because each fraction lies between zero and
one"). -/
theorem matmul_second_moment_le (hB : B ≠ 0)
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j) :
    secondMoment μ (fun ω => matmulValue B C (J ω)) ≤
      (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) *
        max (‖B‖ ^ 2) (‖C‖ ^ 2) := by
  classical
  have hF := frobeniusNorm_pos hB
  set S : ℝ := frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 with hSdef
  have hS : 0 < S := by
    have := frobeniusNorm_nonneg C
    nlinarith
  -- the per-index coefficients
  set a1 : Fin N → ℝ := fun j => matmulProb B C j *
    ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j) with ha1def
  set a2 : Fin N → ℝ := fun j => matmulProb B C j *
    ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j) with ha2def
  have ha1le : ∀ j, a1 j ≤ S := by
    intro j
    show matmulProb B C j * ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j) ≤ S
    by_cases hp : matmulProb B C j = 0
    · rw [hp, zero_mul]
      exact hS.le
    · have hp' : 0 < matmulProb B C j :=
        lt_of_le_of_ne (matmulProb_nonneg B C j) (Ne.symm hp)
      have h6 : matmulProb B C j * ((matmulProb B C j)⁻¹ ^ 2 *
          rowNormSq C j) = rowNormSq C j / matmulProb B C j := by
        field_simp
      rw [h6, div_le_iff₀ hp']
      have h7 : rowNormSq C j / S ≤ matmulProb B C j := by
        rw [matmulProb, ← hSdef, div_le_div_iff₀ hS hS]
        have := colNormSq_nonneg B j
        nlinarith
      calc rowNormSq C j = (rowNormSq C j / S) * S := by field_simp
      _ ≤ matmulProb B C j * S := mul_le_mul_of_nonneg_right h7 hS.le
      _ = S * matmulProb B C j := by ring
  have ha2le : ∀ j, a2 j ≤ S := by
    intro j
    show matmulProb B C j * ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j) ≤ S
    by_cases hp : matmulProb B C j = 0
    · rw [hp, zero_mul]
      exact hS.le
    · have hp' : 0 < matmulProb B C j :=
        lt_of_le_of_ne (matmulProb_nonneg B C j) (Ne.symm hp)
      have h6 : matmulProb B C j * ((matmulProb B C j)⁻¹ ^ 2 *
          colNormSq B j) = colNormSq B j / matmulProb B C j := by
        field_simp
      rw [h6, div_le_iff₀ hp']
      have h7 : colNormSq B j / S ≤ matmulProb B C j := by
        rw [matmulProb, ← hSdef, div_le_div_iff₀ hS hS]
        have := rowNormSq_nonneg C j
        nlinarith
      calc colNormSq B j = (colNormSq B j / S) * S := by field_simp
      _ ≤ matmulProb B C j * S := mul_le_mul_of_nonneg_right h7 hS.le
      _ = S * matmulProb B C j := by ring
  rw [secondMoment]
  -- the two expectation matrices
  have hE1 : expectation μ (fun ω => matmulValue B C (J ω) *
      (matmulValue B C (J ω))ᴴ) = ∑ j, a1 j • colGram B j := by
    have h8 := expectation_discrete (μ := μ) hJ measurable_id
      (fun j => matmulValue B C j * (matmulValue B C j)ᴴ)
    rw [show (fun ω => matmulValue B C (J ω) * (matmulValue B C (J ω))ᴴ) =
      fun ω => (fun j => matmulValue B C j * (matmulValue B C j)ᴴ) (J ω)
      from rfl, h8]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJlaw j, matmulValue_mul_conjTranspose, smul_smul]
  have hE2 : expectation μ (fun ω => (matmulValue B C (J ω))ᴴ *
      matmulValue B C (J ω)) = ∑ j, a2 j • rowGram C j := by
    have h8 := expectation_discrete (μ := μ) hJ measurable_id
      (fun j => (matmulValue B C j)ᴴ * matmulValue B C j)
    rw [show (fun ω => (matmulValue B C (J ω))ᴴ * matmulValue B C (J ω)) =
      fun ω => (fun j => (matmulValue B C j)ᴴ * matmulValue B C j) (J ω)
      from rfl, h8]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJlaw j, conjTranspose_mul_matmulValue, smul_smul]
  rw [hE1, hE2]
  -- Loewner bounds and norms
  have ha1nn : ∀ j, 0 ≤ a1 j := fun j => by
    show 0 ≤ matmulProb B C j * ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j)
    have h1 := matmulProb_nonneg B C j
    have h2 := rowNormSq_nonneg C j
    positivity
  have ha2nn : ∀ j, 0 ≤ a2 j := fun j => by
    show 0 ≤ matmulProb B C j * ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j)
    have h1 := matmulProb_nonneg B C j
    have h2 := colNormSq_nonneg B j
    positivity
  have hpsd1 : ∀ j, (a1 j • colGram B j).PosSemidef := fun j => by
    have h0 : (0 : Matrix (Fin d₁) (Fin d₁) ℂ) ≤ colGram B j :=
      Matrix.nonneg_iff_posSemidef.mpr (posSemidef_colGram B j)
    have h1 := real_smul_loewner_mono (ha1nn j) h0
    rw [smul_zero] at h1
    exact Matrix.nonneg_iff_posSemidef.mp h1
  have hpsd2 : ∀ j, (a2 j • rowGram C j).PosSemidef := fun j => by
    have h0 : (0 : Matrix (Fin d₂) (Fin d₂) ℂ) ≤ rowGram C j :=
      Matrix.nonneg_iff_posSemidef.mpr (posSemidef_rowGram C j)
    have h1 := real_smul_loewner_mono (ha2nn j) h0
    rw [smul_zero] at h1
    exact Matrix.nonneg_iff_posSemidef.mp h1
  have hle1 : (∑ j, a1 j • colGram B j) ≤ S • (B * Bᴴ) := by
    rw [← sum_colGram, Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun j _ =>
      smul_le_smul_of_posSemidef (posSemidef_colGram B j) (ha1le j)
  have hle2 : (∑ j, a2 j • rowGram C j) ≤ S • (Cᴴ * C) := by
    rw [← sum_rowGram, Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun j _ =>
      smul_le_smul_of_posSemidef (posSemidef_rowGram C j) (ha2le j)
  have hn1 : ‖∑ j, a1 j • colGram B j‖ ≤ S * ‖B‖ ^ 2 := by
    have hpsdsum : (∑ j, a1 j • colGram B j).PosSemidef :=
      posSemidef_matsum Finset.univ hpsd1
    refine (norm_le_norm_of_loewner_le hpsdsum hle1).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hS.le,
      ← (l2_opNorm_sq_eq B).1]
  have hn2 : ‖∑ j, a2 j • rowGram C j‖ ≤ S * ‖C‖ ^ 2 := by
    have hpsdsum : (∑ j, a2 j • rowGram C j).PosSemidef :=
      posSemidef_matsum Finset.univ hpsd2
    refine (norm_le_norm_of_loewner_le hpsdsum hle2).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hS.le,
      ← (l2_opNorm_sq_eq C).2]
  refine max_le (hn1.trans ?_) (hn2.trans ?_)
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) hS.le
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hS.le

end MatmulMain

section MatmulErrorBound

variable {d₁ d₂ N : ℕ}
variable {B : Matrix (Fin d₁) (Fin N) ℂ} {C : Matrix (Fin N) (Fin d₂) ℂ}

/-- **Book (6.4.5)** (C6-25): under the normalization
`‖B‖ = ‖C‖ = 1`, with `asr = (srank(B) + srank(C))/2`,

`𝔼‖R̄_n − BC‖ ≤ √(4·asr·log(d₁+d₂)/n) + 2·asr·log(d₁+d₂)/(3n)`.

Explicit source display; §6.4.3 analysis (Corollary 6.2.1 with `L = asr`,
`m₂(R) ≤ 2·asr`). -/
theorem randomized_matmul_error_bound
    (hBn : ‖B‖ = 1) (hCn : ‖C‖ = 1) (hd₁ : 0 < d₁) {nn : ℕ} (hnn : 0 < nn)
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j)
    {R : Fin nn → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k)
      (fun ω => matmulValue B C (J ω)) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B * C‖ ∂μ ≤
      Real.sqrt (4 * ((stableRank B + stableRank C) / 2) *
        Real.log ((Fintype.card (Fin d₁) : ℝ) + Fintype.card (Fin d₂)) / nn) +
      2 * ((stableRank B + stableRank C) / 2) *
        Real.log ((Fintype.card (Fin d₁) : ℝ) + Fintype.card (Fin d₂)) /
        (3 * nn) := by
  classical
  haveI : Nonempty (Fin d₁ ⊕ Fin d₂) := ⟨Sum.inl ⟨0, hd₁⟩⟩
  have hB : B ≠ 0 := by
    intro h
    rw [h, norm_zero] at hBn
    norm_num at hBn
  -- the stable ranks under the normalization
  have hsB : stableRank B = frobeniusNorm B ^ 2 := by
    rw [stableRank, hBn]
    norm_num
  have hsC : stableRank C = frobeniusNorm C ^ 2 := by
    rw [stableRank, hCn]
    norm_num
  set S : ℝ := frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 with hSdef
  have hasr : (stableRank B + stableRank C) / 2 = S / 2 := by
    rw [hsB, hsC]
  have hR₀m : Measurable fun ω => matmulValue B C (J ω) :=
    (measurable_of_countable (matmulValue B C)).comp hJ
  have hbd : ∀ ω, ‖matmulValue B C (J ω)‖ ≤ S / 2 := fun ω =>
    matmul_norm_le hB (J ω)
  have hmean := expectation_matmulEstimator (μ := μ) hB hJ hJlaw
  have h := matrix_sampling_estimator_expectation (μ := μ) hnn hR₀m hbd hmean
    hmeas hid hind
  have hM := matmul_second_moment_le (μ := μ) hB hJ hJlaw
  rw [hBn, hCn] at hM
  have hM' : secondMoment μ (fun ω => matmulValue B C (J ω)) ≤ S := by
    rw [hSdef]
    refine hM.trans (le_of_eq ?_)
    norm_num
  refine h.trans ?_
  rw [hasr]
  set D : ℝ := Real.log ((Fintype.card (Fin d₁) : ℝ) + Fintype.card (Fin d₂))
    with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    refine Real.log_nonneg ?_
    rw [Fintype.card_fin, Fintype.card_fin]
    have h1 : (1 : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hd₁
    have h2 : (0 : ℝ) ≤ (d₂ : ℝ) := by positivity
    linarith
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  refine add_le_add ?_ (le_of_eq ?_)
  · refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hnR hnR]
    have h1 : 2 * secondMoment μ (fun ω => matmulValue B C (J ω)) * D ≤
        2 * S * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM' (by norm_num)) hD0
    have h2 : 4 * (S / 2) * D = 2 * S * D := by ring
    nlinarith [mul_le_mul_of_nonneg_right h1 hnR.le]
  · ring

/-- **Book §6.4.2, relative-error display** (C6-26): if
`n ≥ ε⁻²·asr·log(d₁+d₂)` then the (relative) error satisfies
`𝔼‖R̄_n − BC‖ ≤ 2ε + (2/3)ε²` (the normalization makes `‖B‖‖C‖ = 1`).
Explicit source display. -/
theorem randomized_matmul_relative_error
    (hBn : ‖B‖ = 1) (hCn : ‖C‖ = 1) (hd₁ : 0 < d₁) {nn : ℕ} (hnn : 0 < nn)
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j)
    {R : Fin nn → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k)
      (fun ω => matmulValue B C (J ω)) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ)
    {ε : ℝ} (hε : 0 < ε)
    (hcost : ε⁻¹ ^ 2 * ((stableRank B + stableRank C) / 2) *
      Real.log ((Fintype.card (Fin d₁) : ℝ) + Fintype.card (Fin d₂)) ≤ nn) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B * C‖ ∂μ ≤
      2 * ε + 2 / 3 * ε ^ 2 := by
  have h := randomized_matmul_error_bound (μ := μ) hBn hCn hd₁ hnn hJ hJlaw
    hmeas hid hind
  refine h.trans ?_
  set A : ℝ := (stableRank B + stableRank C) / 2 with hAdef
  set D : ℝ := Real.log ((Fintype.card (Fin d₁) : ℝ) + Fintype.card (Fin d₂))
    with hDdef
  have hA0 : 0 ≤ A := by
    rw [hAdef, stableRank, stableRank]
    positivity
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    refine Real.log_nonneg ?_
    rw [Fintype.card_fin, Fintype.card_fin]
    have h1 : (1 : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hd₁
    have h2 : (0 : ℝ) ≤ (d₂ : ℝ) := by positivity
    linarith
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  -- `A·D/n ≤ ε²`
  have hkey : A * D ≤ ε ^ 2 * nn := by
    have h1 : ε⁻¹ ^ 2 * A * D ≤ (nn : ℝ) := hcost
    have h2 : ε⁻¹ ^ 2 * A * D = A * D / ε ^ 2 := by
      field_simp
    rw [h2, div_le_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hterm1 : Real.sqrt (4 * A * D / nn) ≤ 2 * ε := by
    rw [show (2 * ε : ℝ) = Real.sqrt ((2 * ε) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hnR]
    nlinarith [hkey]
  have hterm2 : 2 * A * D / (3 * nn) ≤ 2 / 3 * ε ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * nn)]
    nlinarith [hkey]
  linarith

end MatmulErrorBound

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Random features (Tropp §6.5)

The Rahimi–Recht/Lopez-Paz et al. analysis of low-rank kernel approximation:
a kernel `Φ : X × X → [−1,1]` with a random feature map `(ψ, w)` satisfying
the reproducing property `Φ(x,y) = 𝔼[ψ(x;w)ψ(y;w)]`; the random
feature `z = (ψ(x_i; w))_i` gives the unbiased rank-one estimator `R = zz*`
of the kernel matrix `G`, and `n` independent features are averaged.

* `kernelMatrix`, `IsPosDefKernel` (C6-27);
* `HasReproducingProperty`, `featureVector`, `featureOuter` — the abstract
  random-feature model (C6-30) and the identity `G = 𝔼(zz*)`
  (`kernelMatrix_eq_expectation_outer`);
* `random_feature_error_bound` — the performance estimate **Book (6.5.7)**:
  `𝔼‖R̄_n − G‖ ≤ √(2bN‖G‖log(2N)/n) + 2bN log(2N)/(3n)`.
  the source hypothesizes
  `ψ : X×W → [−b, b]` but its analysis uses `‖z‖² ≤ bN`, which requires
  `ψ² ≤ b`; as literally stated (with `|ψ| ≤ b`) the display is falsifiable.
  The theorem here carries the hypothesis `ψ(x;w)² ≤ b` under which the
  source's displayed bound is recovered;
  `random_feature_error_bound_of_abs_le` is the `|ψ| ≤ b ⟹ b²`-version;
* `trace_kernelMatrix` — `tr G = N` from `Φ(x,x) = 1` (C6-32);
* `random_feature_relative_error` — the §6.5.4 consequence with right-hand
  side `(ε + ε²/3)‖G‖`.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [IsProbabilityMeasure μ]

section KernelDefs

variable {X : Type*}

/-- **Book §6.5.1** (C6-27): the kernel matrix `G = [Φ(x_i, x_j)]` of a data
set.  Explicit source declaration. -/
noncomputable def kernelMatrix (Φ : X → X → ℝ) {N : ℕ} (x : Fin N → X) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ((Φ (x i) (x j) : ℝ) : ℂ)

/-- **Book §6.5.1** (C6-27): "we say that the kernel `Φ` is *positive
definite* if the kernel matrix `G` is positive semidefinite for any choice of
observations."  Explicit source declaration. -/
def IsPosDefKernel (Φ : X → X → ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → X), (kernelMatrix Φ x).PosSemidef

/-- **Book §6.5.2** (C6-30): the reproducing
property of a random feature map, `Φ(x,y) = 𝔼_w[ψ(x;w)·ψ(y;w)]`.  Explicit
source declaration. -/
def HasReproducingProperty (Φ : X → X → ℝ) {W : Type*} [MeasurableSpace W]
    (ν : MeasureTheory.Measure W) (ψ : X → W → ℝ) : Prop :=
  ∀ x y : X, Φ x y = ∫ w, ψ x w * ψ y w ∂ν

/-- **Book §6.5.2** (C6-30): the random feature vector
`z = (ψ(x_1;w), …, ψ(x_N;w))` — here realized along a random element
`w : Ω → W`.  Explicit source declaration. -/
noncomputable def featureVector (ψ : X → W → ℝ) {N : ℕ} (x : Fin N → X)
    (w : Ω → W) (ω : Ω) : Fin N → ℝ :=
  fun i => ψ (x i) (w ω)

/-- **Book §6.5.2** (C6-30): the rank-one estimator `R = zz*`.  Explicit
source declaration. -/
noncomputable def featureOuter {N : ℕ} (z : Ω → Fin N → ℝ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.vecMulVec (fun i => ((z ω i : ℝ) : ℂ)) (fun j => ((z ω j : ℝ) : ℂ))

/-- **Book §6.5.2** (C6-30): "We can write this relation in matrix form as
`G = 𝔼(zz*)`. Therefore, the random matrix `R = zz*` is an unbiased rank-one
estimator for the kernel matrix."  Explicit source computation. -/
theorem kernelMatrix_eq_expectation_outer {Φ : X → X → ℝ} {W : Type*}
    [MeasurableSpace W] {ν : MeasureTheory.Measure W} {ψ : X → W → ℝ}
    (hrep : HasReproducingProperty Φ ν ψ) {N : ℕ} (x : Fin N → X)
    {w : Ω → W} (hw : Measurable w) (hlaw : μ.map w = ν)
    (hψ : ∀ x', Measurable (ψ x')) :
    kernelMatrix Φ x =
      expectation μ (featureOuter (fun ω => featureVector ψ x w ω)) := by
  ext i j
  rw [expectation_apply]
  rw [show (fun ω => featureOuter (fun ω' => featureVector ψ x w ω') ω i j) =
    fun ω => ((ψ (x i) (w ω) * ψ (x j) (w ω) : ℝ) : ℂ) from by
      funext ω
      rw [featureOuter, Matrix.vecMulVec_apply]
      push_cast
      rfl]
  rw [show kernelMatrix Φ x i j = ((Φ (x i) (x j) : ℝ) : ℂ) from rfl]
  rw [hrep (x i) (x j)]
  rw [show (∫ w', ψ (x i) w' * ψ (x j) w' ∂ν) =
    ∫ ω, ψ (x i) (w ω) * ψ (x j) (w ω) ∂μ from by
      rw [← hlaw]
      exact integral_map hw.aemeasurable
        (((hψ (x i)).mul (hψ (x j))).aestronglyMeasurable)]
  exact integral_complex_ofReal.symm

end KernelDefs

section FeatureAnalysis

variable {N : ℕ} {z : Ω → Fin N → ℝ} {b : ℝ}

/-- Lean implementation helper: measurability of the outer estimator. -/
lemma measurable_featureOuter (hz : Measurable z) :
    Measurable (featureOuter z) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  rw [show (fun ω => featureOuter z ω i j) =
    fun ω => ((z ω i * z ω j : ℝ) : ℂ) from by
      funext ω
      rw [featureOuter, Matrix.vecMulVec_apply]
      push_cast
      rfl]
  exact Complex.measurable_ofReal.comp
    (((measurable_pi_apply i).comp hz).mul ((measurable_pi_apply j).comp hz))

/-- **Book §6.5.5, first display** (C6-31): the uniform bound
`‖R‖ = ‖z‖² ≤ bN` under the square-bound hypothesis `ψ² ≤ b`.
Explicit source display. -/
lemma featureOuter_norm_le (hb2 : ∀ ω i, (z ω i) ^ 2 ≤ b) (ω : Ω) :
    ‖featureOuter z ω‖ ≤ b * N := by
  rw [featureOuter]
  refine (l2_opNorm_vecMulVec_le _ _).trans ?_
  have h1 : l2norm (fun i => ((z ω i : ℝ) : ℂ)) ^ 2 ≤ b * N := by
    rw [l2norm_sq]
    calc (∑ i, ‖((z ω i : ℝ) : ℂ)‖ ^ 2) = ∑ i, (z ω i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ _i : Fin N, b := Finset.sum_le_sum fun i _ => hb2 ω i
    _ = b * N := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  have h2 := l2norm_nonneg (fun i => ((z ω i : ℝ) : ℂ))
  nlinarith [h1, h2]

/-- Lean implementation helper: `R = zz*` is positive semidefinite (and in
particular Hermitian). -/
lemma posSemidef_featureOuter (z : Ω → Fin N → ℝ) (ω : Ω) :
    (featureOuter z ω).PosSemidef := by
  set zc : Fin N → ℂ := fun i => ((z ω i : ℝ) : ℂ) with hzc
  have hherm : (featureOuter z ω).IsHermitian := by
    have h : (featureOuter z ω)ᴴ = featureOuter z ω := by
      ext i j
      rw [Matrix.conjTranspose_apply, featureOuter, Matrix.vecMulVec_apply,
        Matrix.vecMulVec_apply]
      rw [star_mul', Complex.star_def, Complex.conj_ofReal,
        Complex.conj_ofReal]
      ring
    exact h
  refine posSemidef_iff_isHermitian_quadratic.mpr ⟨hherm, fun u => ?_⟩
  have h1 : star u ⬝ᵥ (featureOuter z ω *ᵥ u) =
      (star u ⬝ᵥ zc) * (zc ⬝ᵥ u) := by
    rw [show (featureOuter z ω *ᵥ u) = fun i => zc i * (zc ⬝ᵥ u) from
      funext fun i => by
        rw [show (featureOuter z ω *ᵥ u) i =
          ∑ k, featureOuter z ω i k * u k from rfl]
        rw [show (zc ⬝ᵥ u) = ∑ k, zc k * u k from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [featureOuter, Matrix.vecMulVec_apply]
        show ((z ω i : ℝ) : ℂ) * ((z ω k : ℝ) : ℂ) * u k = _
        rw [hzc]
        ring]
    rw [show star u ⬝ᵥ (fun i => zc i * (zc ⬝ᵥ u)) =
      ∑ i, star u i * (zc i * (zc ⬝ᵥ u)) from rfl]
    rw [show (star u ⬝ᵥ zc) = ∑ i, star u i * zc i from rfl, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : star u ⬝ᵥ zc = star (zc ⬝ᵥ u) := by
    rw [show (zc ⬝ᵥ u) = ∑ i, zc i * u i from rfl, star_sum]
    rw [show star u ⬝ᵥ zc = ∑ i, star (u i) * zc i from rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul']
    have hzci : star (zc i) = zc i := by
      show star ((z ω i : ℝ) : ℂ) = ((z ω i : ℝ) : ℂ)
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [hzci]
    ring
  rw [h1, h2]
  have h3 : star (zc ⬝ᵥ u) * (zc ⬝ᵥ u) =
      ((‖zc ⬝ᵥ u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [h3]
  rw [Complex.ofReal_re]
  positivity

end FeatureAnalysis

section FeatureErrorBound

variable {N : ℕ}

/-- Lean implementation helper: for psd `P` with `‖P‖ ≤ c`, `P² ≼ c·P`
(the source's step `𝔼R² ≼ bN·𝔼(zz*)`).  Via the Transfer Rule with
`x² ≤ cx` on `[0, c]`. -/
lemma sq_le_smul_of_posSemidef {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : P.PosSemidef) {c : ℝ} (hc : ‖P‖ ≤ c) : P * P ≤ c • P := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · haveI : IsEmpty (Fin N) := by
      rw [hN]
      exact Fin.isEmpty'
    have h1 : P * P = 0 := Subsingleton.elim _ _
    have h2 : c • P = 0 := Subsingleton.elim _ _
    rw [h1, h2]
  · haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    rw [sq_eq_cfc hP.1, smul_eq_cfc hP.1 c]
    refine transfer_rule hP.1 (I := Set.Icc 0 c) (fun i => ?_) fun a ha => ?_
    · refine ⟨hP.eigenvalues_nonneg i, ?_⟩
      exact (eigenvalues_le_lambdaMax hP.1 i).trans
        (((le_abs_self _).trans (abs_lambdaMax_le _)).trans hc)
    · nlinarith [ha.1, ha.2]

/-- **Book (6.5.7)** (C6-31): the random-feature
approximation error,

`𝔼‖R̄_n − G‖ ≤ √(2bN‖G‖·log(2N)/n) + 2bN·log(2N)/(3n)`,

under the boundedness hypothesis `ψ(x;w)² ≤ b`. Explicit source display;
§6.5.5 analysis (Corollary 6.2.1 with `L = bN` and `m₂(R) ≤ bN‖G‖`).

**Author note.** The Book states `|ψ| ≤ b` but uses `‖z‖² ≤ bN`; Lean makes
the square-bound needed for the displayed coefficient explicit. -/
theorem random_feature_error_bound (hN : 0 < N) {nn : ℕ} (hnn : 0 < nn)
    {z : Ω → Fin N → ℝ} {b : ℝ} (hz : Measurable z) (hb0 : 0 ≤ b)
    (hb2 : ∀ ω i, (z ω i) ^ 2 ≤ b)
    {G : Matrix (Fin N) (Fin N) ℂ} (hG : expectation μ (featureOuter z) = G)
    {R : Fin nn → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) (featureOuter z) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - G‖ ∂μ ≤
      Real.sqrt (2 * (b * N * ‖G‖) * Real.log (2 * N) / nn) +
      2 * (b * N) * Real.log (2 * N) / (3 * nn) := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  haveI : Nonempty (Fin N ⊕ Fin N) := ⟨Sum.inl ⟨0, hN⟩⟩
  have hbd : ∀ ω, ‖featureOuter z ω‖ ≤ b * N := featureOuter_norm_le hb2
  have hR₀m : Measurable (featureOuter z) := measurable_featureOuter hz
  have h := matrix_sampling_estimator_expectation (μ := μ) hnn hR₀m hbd hG
    hmeas hid hind
  -- collapse the dimension factor `N + N = 2N`
  have hcard : ((Fintype.card (Fin N) : ℝ) + Fintype.card (Fin N)) =
      2 * N := by
    rw [Fintype.card_fin]
    ring
  rw [hcard] at h
  refine h.trans ?_
  -- the second-moment bound `m₂ ≤ bN‖G‖`
  have hM : secondMoment μ (featureOuter z) ≤ b * N * ‖G‖ := by
    rw [secondMoment]
    have hHerm : ∀ ω, (featureOuter z ω).IsHermitian := fun ω =>
      (posSemidef_featureOuter z ω).1
    have heq1 : (fun ω => featureOuter z ω * (featureOuter z ω)ᴴ) =
        fun ω => featureOuter z ω * featureOuter z ω := by
      funext ω
      rw [(hHerm ω).eq]
    have heq2 : (fun ω => (featureOuter z ω)ᴴ * featureOuter z ω) =
        fun ω => featureOuter z ω * featureOuter z ω := by
      funext ω
      rw [(hHerm ω).eq]
    rw [heq1, heq2, max_self]
    -- `𝔼R² ≼ bN·G`
    have hpt : ∀ ω, featureOuter z ω * featureOuter z ω ≤
        (b * N) • featureOuter z ω := fun ω =>
      sq_le_smul_of_posSemidef (posSemidef_featureOuter z ω) (hbd ω)
    have hRint : MIntegrable (featureOuter z) μ :=
      mintegrable_rect_of_norm_bound hR₀m hbd
    have hR2int : MIntegrable
        (fun ω => featureOuter z ω * featureOuter z ω) μ := by
      exact mintegrable_sq_of_norm_bound (μ := μ) (R := b * N) hR₀m hbd
    have hsmulint : MIntegrable (fun ω => (b * N) • featureOuter z ω) μ := by
      intro i j
      have h1 : (fun ω => ((b * N) • featureOuter z ω) i j) =
          fun ω => (b * N) • featureOuter z ω i j := rfl
      rw [h1]
      exact Integrable.smul (b * (N : ℝ)) (hRint i j)
    have hmono := expectation_loewner_mono hR2int hsmulint
      (Filter.Eventually.of_forall hpt)
    rw [expectation_real_smul, hG] at hmono
    have hpsd : (expectation μ
        (fun ω => featureOuter z ω * featureOuter z ω)).PosSemidef :=
      posSemidef_expectation hR2int (Filter.Eventually.of_forall fun ω =>
        posSemidef_sq (posSemidef_featureOuter z ω).1)
    refine (norm_le_norm_of_loewner_le hpsd hmono).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- monotonicity of the final bound in `m₂`
  have hD0 : 0 ≤ Real.log (2 * N) := by
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  refine add_le_add ?_ (le_of_eq ?_)
  · refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hnR hnR]
    have h1 : 2 * secondMoment μ (featureOuter z) * Real.log (2 * N) ≤
        2 * (b * N * ‖G‖) * Real.log (2 * N) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM (by norm_num)) hD0
    nlinarith [mul_le_mul_of_nonneg_right h1 hnR.le]
  · ring

/-- Lean implementation helper: the `|ψ| ≤ b` form of **Book (6.5.7)**,
whose conclusion has `b²` in place of `b`. -/
theorem random_feature_error_bound_of_abs_le (hN : 0 < N) {nn : ℕ}
    (hnn : 0 < nn) {z : Ω → Fin N → ℝ} {b : ℝ} (hz : Measurable z)
    (hb0 : 0 ≤ b) (hb : ∀ ω i, |z ω i| ≤ b)
    {G : Matrix (Fin N) (Fin N) ℂ} (hG : expectation μ (featureOuter z) = G)
    {R : Fin nn → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) (featureOuter z) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - G‖ ∂μ ≤
      Real.sqrt (2 * (b * b * N * ‖G‖) * Real.log (2 * N) / nn) +
      2 * (b * b * N) * Real.log (2 * N) / (3 * nn) := by
  have h := random_feature_error_bound (μ := μ) (b := b * b) hN hnn hz
    (by positivity) (fun ω i => by
      nlinarith [hb ω i, abs_nonneg (z ω i), sq_abs (z ω i)])
    hG hmeas hid hind
  exact h

end FeatureErrorBound

section IntrinsicDiscussion

variable {X : Type*}

/-- **Book §6.5.4** (C6-32): `tr G = N` "because of the requirement that
`Φ(x,x) = +1`" (the diagonal of the kernel matrix is identically one).
Explicit source computation (the display for `intdim(G) = N/‖G‖`). -/
theorem trace_kernelMatrix {Φ : X → X → ℝ} {N : ℕ} {x : Fin N → X}
    (hdiag : ∀ x', Φ x' x' = 1) :
    (kernelMatrix Φ x).trace = (N : ℂ) := by
  rw [Matrix.trace]
  rw [show (∑ i, (kernelMatrix Φ x).diag i) =
    ∑ _i : Fin N, (1 : ℂ) from Finset.sum_congr rfl fun i _ => by
      show ((Φ (x i) (x i) : ℝ) : ℂ) = 1
      rw [hdiag (x i)]
      norm_num]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

/-- **Book §6.5.4, relative-error consequence** (C6-32): if
`n ≥ 2b·ε⁻²·(N/‖G‖)·log(2N)` then
`𝔼‖R̄_n − G‖ ≤ (ε + ε²/3)·‖G‖`.

**Author note.** The source display has `ε + ε⁻²`; the cost calculation gives
the dimensionally consistent coefficient `ε + ε²/3` formalized here. -/
theorem random_feature_relative_error (hN : 0 < N) {nn : ℕ} (hnn : 0 < nn)
    {z : Ω → Fin N → ℝ} {b : ℝ} (hz : Measurable z) (hb0 : 0 ≤ b)
    (hb2 : ∀ ω i, (z ω i) ^ 2 ≤ b)
    {G : Matrix (Fin N) (Fin N) ℂ} (hG : expectation μ (featureOuter z) = G)
    (hGpos : 0 < ‖G‖)
    {R : Fin nn → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) (featureOuter z) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ)
    {ε : ℝ} (hε : 0 < ε)
    (hcost : 2 * b * ε⁻¹ ^ 2 * ((N : ℝ) / ‖G‖) * Real.log (2 * N) ≤ nn) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - G‖ ∂μ ≤ (ε + ε ^ 2 / 3) * ‖G‖ := by
  have h := random_feature_error_bound (μ := μ) hN hnn hz hb0 hb2 hG hmeas
    hid hind
  refine h.trans ?_
  set D : ℝ := Real.log (2 * N) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  -- the cost hypothesis, multiplied out: `2bND/n ≤ ε²‖G‖`
  have hkey : 2 * b * N * D ≤ ε ^ 2 * ‖G‖ * nn := by
    have h1 : 2 * b * ε⁻¹ ^ 2 * ((N : ℝ) / ‖G‖) * D =
        2 * b * N * D / (ε ^ 2 * ‖G‖) := by
      field_simp
    rw [h1, div_le_iff₀ (by positivity)] at hcost
    nlinarith [hcost]
  have hterm1 : Real.sqrt (2 * (b * N * ‖G‖) * D / nn) ≤ ε * ‖G‖ := by
    rw [show (ε * ‖G‖ : ℝ) = Real.sqrt ((ε * ‖G‖) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hnR]
    nlinarith [hkey, hGpos]
  have hterm2 : 2 * (b * N) * D / (3 * nn) ≤ ε ^ 2 / 3 * ‖G‖ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * nn)]
    nlinarith [hkey]
  nlinarith [hterm1, hterm2]

end IntrinsicDiscussion

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Optimality of the matrix Bernstein inequality (Tropp §6.1.1–§6.1.2, §6.7)

* `matrix_rosenthal_pinelis_symmetric` and
  `matrix_rosenthal_pinelis_centered_with_loss` — two proved variants of
  **Book (6.1.6)**: exact CGT coefficients under distributional symmetry, and
  a centered result with explicit independent-copy losses;
* `varStat_le_expectation_norm_sq` (C6-07) — the Jensen lower bound
  `v(Z) ≤ 𝔼‖Z‖²` ("the quantity `v(Z)` cannot be omitted");
* `symmetric_sum_lower_bound` — the symmetric lower bound **Book (6.1.7)**;
* `l2_opNorm_diagonal_abs` (C6-10) — the deterministic identity
  `‖Σ c_k E_kk‖ = max_k |c_k|` behind the log-necessity examples (whose
  CLT/Skorokhod asymptotics are omitted, as in Chapters 4–5);
* `varAW`, `varStat_summand_le_varAW`, `varAW_eq_of_identDistrib` (C6-39) —
  the Ahlswede–Winter variance parameter of the Notes (§6.7.1) and its
  comparison with the matrix variance statistic.

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [IsProbabilityMeasure μ]

section JensenLower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Book §6.1.2, first display** (C6-07): the Jensen lower bound —
`v(Z) = max{‖𝔼(ZZ*)‖, ‖𝔼(Z*Z)‖} ≤ 𝔼max{‖ZZ*‖,‖Z*Z‖} = 𝔼‖Z‖²` — "the
quantity `v(Z)` cannot be omitted because Jensen's inequality implies…".
Explicit source display.

**Author note.** Lean includes measurability and a pointwise norm bound to
supply the integrability regularity used by Jensen's inequality. -/
theorem varStat_le_expectation_norm_sq {Z : Ω → Matrix m n ℂ} {R : ℝ}
    (hZm : Measurable Z) (hbd : ∀ ω, ‖Z ω‖ ≤ R) :
    max ‖expectation μ (fun ω => Z ω * (Z ω)ᴴ)‖
      ‖expectation μ (fun ω => (Z ω)ᴴ * Z ω)‖ ≤ ∫ ω, ‖Z ω‖ ^ 2 ∂μ := by
  have hint1 : MIntegrable (fun ω => Z ω * (Z ω)ᴴ) μ :=
    MIntegrable.of_bound (measurable_mul_conjTranspose_self hZm) (R * R)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖(Z ω * (Z ω)ᴴ) i j‖ ≤ ‖Z ω * (Z ω)ᴴ‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖Z ω‖ * ‖(Z ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖Z ω‖ * ‖Z ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ R * R := by nlinarith [norm_nonneg (Z ω), hbd ω])
  have hint2 : MIntegrable (fun ω => (Z ω)ᴴ * Z ω) μ :=
    MIntegrable.of_bound (measurable_conjTranspose_mul_self hZm) (R * R)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖((Z ω)ᴴ * Z ω) i j‖ ≤ ‖(Z ω)ᴴ * Z ω‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖(Z ω)ᴴ‖ * ‖Z ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖Z ω‖ * ‖Z ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ R * R := by nlinarith [norm_nonneg (Z ω), hbd ω])
  have hnormint : Integrable (fun ω => ‖Z ω‖ ^ 2) μ := by
    refine Integrable.of_bound ?_ (R ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((continuous_l2_opNorm.measurable.comp hZm).pow_const
        2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hbd ω
      have h2 := norm_nonneg (Z ω)
      nlinarith
  refine max_le ?_ ?_
  · -- `‖𝔼(ZZ*)‖ ≤ 𝔼‖ZZ*‖ = 𝔼‖Z‖²`
    have hnorm1 : Integrable (fun ω => ‖Z ω * (Z ω)ᴴ‖) μ := by
      refine Integrable.of_bound ?_ (R * R)
        (Filter.Eventually.of_forall fun ω => ?_)
      · refine (Continuous.measurable continuous_l2_opNorm).comp
          (measurable_mul_conjTranspose_self hZm) |>.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        calc ‖Z ω * (Z ω)ᴴ‖ ≤ ‖Z ω‖ * ‖(Z ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖Z ω‖ * ‖Z ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ R * R := by nlinarith [norm_nonneg (Z ω), hbd ω]
    refine (norm_expectation_le hint1 hnorm1).trans ?_
    refine integral_mono hnorm1 hnormint fun ω => ?_
    rw [← (l2_opNorm_sq_eq (Z ω)).1]
  · have hnorm2 : Integrable (fun ω => ‖(Z ω)ᴴ * Z ω‖) μ := by
      refine Integrable.of_bound ?_ (R * R)
        (Filter.Eventually.of_forall fun ω => ?_)
      · refine (Continuous.measurable continuous_l2_opNorm).comp
          (measurable_conjTranspose_mul_self hZm) |>.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        calc ‖(Z ω)ᴴ * Z ω‖ ≤ ‖(Z ω)ᴴ‖ * ‖Z ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖Z ω‖ * ‖Z ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ R * R := by nlinarith [norm_nonneg (Z ω), hbd ω]
    refine (norm_expectation_le hint2 hnorm2).trans ?_
    refine integral_mono hnorm2 hnormint fun ω => ?_
    rw [← (l2_opNorm_sq_eq (Z ω)).2]

end JensenLower

section RosenthalPinelis

variable {d₁ d₂ : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Book (6.1.6), symmetric exact-coefficient variant.** With the
distributional symmetry required by [CGT12, Theorem A.1(2)], Hermitian
dilation gives the Book's displayed coefficients without loss.

**Author note.** This theorem adds symmetry in law. The literal centered,
exact-coefficient display in the Book is not asserted as a Lean theorem.  See
`matrix_rosenthal_pinelis_symmetric_integrable` for the finite-heavy-tail
counterpart that removes this theorem's uniform boundedness regularity. -/
theorem matrix_rosenthal_pinelis_symmetric
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : ProbabilityTheory.iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) μ)
    {R : ι → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 *
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d₁ + d₂)) +
      4 * Real.exp 1 * (maxSummandSq S μ) ^ ((1 : ℝ) / 2) *
        Real.log (d₁ + d₂) := by
  exact matrix_rosenthal_pinelis_symmetric_aux h_indep h_meas h_symm h_bdd

/-- **Book (6.1.6), centered variant with explicit symmetrization loss.**
Without distributional symmetry, the independent-copy argument gives a
factor `sqrt 2` loss in the variance coefficient and a factor `2` loss in the
maximum-summand coefficient.

**Author note.** This theorem retains the Book's centering assumption but not
its exact coefficients. The literal centered, exact-coefficient display is
not asserted as a Lean theorem; this does not assert that display is false.
See `matrix_rosenthal_pinelis_centered_with_loss_integrable` for the
finite-heavy-tail counterpart that removes this theorem's uniform boundedness
regularity. -/
theorem matrix_rosenthal_pinelis_centered_with_loss
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : ProbabilityTheory.iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation μ (S k) = 0)
    {R : ι → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (4 * Real.exp 1 *
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d₁ + d₂)) +
      8 * Real.exp 1 * (maxSummandSq S μ) ^ ((1 : ℝ) / 2) *
        Real.log (d₁ + d₂) := by
  exact matrix_rosenthal_pinelis_centered_with_loss_aux
    h_indep h_meas h_cent h_bdd

end RosenthalPinelis

section SymmetricLower

variable {d₁ d₂ : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Book (6.1.7)**: for independent
symmetric summands, `𝔼‖Z‖² ≥ (1/4)·𝔼 max_k ‖S_k‖²` (the source's
unspecified "const" instantiated at the classical value).

**Author note.** The auxiliary sign-reflection argument proves coefficient
`1` under the stated boundedness regularity; this public theorem retains
coefficient `1/4`.  See `symmetric_sum_lower_bound_integrable` for the
source-faithful finite-moment counterpart. -/
theorem symmetric_sum_lower_bound
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : ProbabilityTheory.iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) μ)
    {R : ι → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    (1 / 4 : ℝ) * maxSummandSq S μ ≤ ∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ := by
  exact symmetric_sum_lower_bound_aux h_indep h_meas h_symm h_bdd

end SymmetricLower

section DiagonalExamples

/-- **Book §6.1.2, log-example identity** (C6-10): the deterministic core of
"`𝔼‖Σγ_k E_kk‖ = 𝔼max_k|γ_k|`" — the spectral norm of a real diagonal matrix
is the largest absolute diagonal entry.  Implicit source claim; the
CLT/Skorokhod limit arguments are not part of this deterministic identity. -/
theorem l2_opNorm_diagonal_abs [Nonempty n] (c : n → ℝ) :
    ‖Matrix.diagonal (fun k => ((c k : ℝ) : ℂ))‖ =
      Finset.univ.sup' Finset.univ_nonempty (fun k => |c k|) := by
  -- square the norm: `‖D‖² = ‖DD*‖ = ‖diag(c²)‖ = max c²`
  have h1 : ‖Matrix.diagonal (fun k => ((c k : ℝ) : ℂ))‖ ^ 2 =
      ‖Matrix.diagonal (fun k => ((c k ^ 2 : ℝ) : ℂ))‖ := by
    rw [(l2_opNorm_sq_eq (Matrix.diagonal fun k => ((c k : ℝ) : ℂ))).1]
    congr 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have h2 : ‖Matrix.diagonal (fun k => ((c k ^ 2 : ℝ) : ℂ))‖ =
      Finset.univ.sup' Finset.univ_nonempty (fun k => c k ^ 2) :=
    l2_opNorm_diagonal_ofReal fun k => sq_nonneg _
  have h3 : Finset.univ.sup' Finset.univ_nonempty (fun k => c k ^ 2) =
      (Finset.univ.sup' Finset.univ_nonempty (fun k => |c k|)) ^ 2 := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ fun k _ => ?_
      have h4 : |c k| ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun k => |c k|) :=
        Finset.le_sup' (f := fun k => |c k|) (Finset.mem_univ k)
      nlinarith [abs_nonneg (c k), sq_abs (c k)]
    · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun k => |c k|)
      rw [hk]
      have h5 : c k ^ 2 ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun k => c k ^ 2) :=
        Finset.le_sup' (f := fun k => c k ^ 2) (Finset.mem_univ k)
      nlinarith [sq_abs (c k)]
  have h6 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun k => |c k|) :=
    le_trans (abs_nonneg (c (Classical.arbitrary n)))
      (Finset.le_sup' (f := fun k => |c k|)
        (Finset.mem_univ (Classical.arbitrary n)))
  have h7 := norm_nonneg (Matrix.diagonal fun k => ((c k : ℝ) : ℂ))
  nlinarith [h1, h2, h3]

end DiagonalExamples

section AhlswedeWinter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Book §6.7.1 display** (C6-39): the Ahlswede–Winter variance parameter
`v_AW(Y) = Σ_k ‖𝔼X_k²‖`.  Explicit source display (Notes). -/
noncomputable def varAW (μ : MeasureTheory.Measure Ω)
    (X : ι → Ω → Matrix n n ℂ) : ℝ :=
  ∑ k, ‖expectation μ (fun ω => X k ω * X k ω)‖

/-- **Book §6.7.1** (C6-39): "This parameter can be significantly larger
than the matrix variance statistic" — the comparison
`‖Σ𝔼X_k²‖ ≤ v_AW(Y)` (triangle inequality).  Implicit source claim. -/
theorem varStat_summand_le_varAW (X : ι → Ω → Matrix n n ℂ) :
    ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ ≤ varAW μ X :=
  norm_sum_le _ _

/-- **Book §6.7.1** (C6-39): "They do coincide in some special cases, such
as when the summands are independent and identically distributed" — for
identically distributed summands `v_AW(Y) = card ι · ‖𝔼X₀²‖`, which equals
the summand form of `v(Y)` computed through the same distribution.  Implicit
source claim (the iid coincidence, stated at the level of the two variance
formulas).

**Author note.** Independence is not needed for this identity; identical
distribution alone suffices. -/
theorem varAW_eq_of_identDistrib [Nonempty ι] {X : ι → Ω → Matrix n n ℂ}
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (X k)
      (X (Classical.arbitrary ι)) μ μ) :
    varAW μ X = ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ := by
  classical
  have hsq : ∀ k, expectation μ (fun ω => X k ω * X k ω) =
      expectation μ (fun ω => X (Classical.arbitrary ι) ω *
        X (Classical.arbitrary ι) ω) := by
    intro k
    ext i j
    have hg : Measurable fun M : Matrix n n ℂ => (M * M) i j := by
      have h1 : (fun M : Matrix n n ℂ => (M * M) i j) =
          fun M : Matrix n n ℂ => ∑ l, M i l * M l j := by
        funext M
        rw [Matrix.mul_apply]
      rw [h1]
      exact Finset.measurable_sum _ fun l _ =>
        (measurable_entry i l).mul (measurable_entry l j)
    exact ((hid k).comp hg).integral_eq
  rw [varAW, Finset.sum_congr rfl fun k _ => by rw [hsq k],
    Finset.sum_congr rfl fun k _ => hsq k]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ (Fintype.card ι),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    smul_eq_mul]

end AhlswedeWinter

end MatrixConcentration

/-!
# One-sided matrix Bernstein counterparts

This section records the book-faithful one-sided forms of the Hermitian matrix
Bernstein argument.  Unlike the earlier bounded wrappers, these declarations do
not impose a bound on the lower spectral edge.  First- and second-moment
integrability is stated explicitly; the public `_ae` declarations below also
interpret the spectral-edge hypothesis almost everywhere.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ}

section OneSidedMasterBounds

/-- Lean implementation helper: the upper matrix Laplace-transform tail step
under a one-sided spectral bound and entrywise first-moment integrability. -/
lemma master_tail_upper_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ) {U : ι → ℝ}
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ U k)
    (hind : ProbabilityTheory.iIndepFun X μ) (t : ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      Real.exp (-θ * t) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  classical
  let Y : Ω → Matrix n n ℂ := fun ω => ∑ k, X k ω
  have hYmeas : Measurable Y := measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (Y ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYmax : ∀ ω, lambdaMax (hYherm ω) ≤ ∑ k, U k := fun ω =>
    lambdaMax_matsum_le_sum Finset.univ hherm hmax ω
  have hYint : MIntegrable Y μ :=
    MIntegrable.finsetSum (μ := μ) Finset.univ fun k _ => hXint k
  have hHermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  let Z : Ω → ℝ := fun ω => Real.exp (θ * lambdaMax (hYherm ω))
  have hZmeas : Measurable Z :=
    Real.measurable_exp.comp
      ((measurable_lambdaMax_of_forall hYmeas hYherm).const_mul θ)
  have hZint : Integrable Z μ := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable
      (Real.exp (θ * ∑ k, U k)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hYmax ω) hθ.le)
  have hExpint : MIntegrable (fun ω => NormedSpace.exp (θ • Y ω)) μ :=
    mintegrable_matrixExp_of_lambdaMax_bound hYmeas hYherm hYmax hθ
  have htrint : Integrable
      (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ := by
    have hdiag : ∀ i, Integrable
        (fun ω => (NormedSpace.exp (θ • Y ω) i i).re) μ :=
      fun i => (hExpint i i).re
    simpa [Matrix.trace] using
      (integrable_finsetSum Finset.univ fun i _ => hdiag i)
  have hpoint : ∀ ω, Z ω ≤
      ((NormedSpace.exp (θ • Y ω)).trace).re := fun ω => by
    have hscale : θ * lambdaMax (hYherm ω) = lambdaMax (hHermθ ω) :=
      (lambdaMax_smul_nonneg (hYherm ω) hθ.le (hHermθ ω)).symm
    change Real.exp (θ * lambdaMax (hYherm ω)) ≤ _
    rw [hscale]
    exact exp_lambdaMax_le_trace_exp (hHermθ ω)
  have hmarkov := markov_inequality
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hZint
    (Real.exp_pos (θ * t))
  have hevent : {ω | t ≤ lambdaMax (hYherm ω)} =
      {ω | Real.exp (θ * t) ≤ Z ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Z, Real.exp_le_exp]
    exact ⟨fun h => mul_le_mul_of_nonneg_left h hθ.le,
      fun h => le_of_mul_le_mul_left h hθ⟩
  have hmono : (∫ ω, Z ω ∂μ) ≤
      ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ :=
    integral_mono hZint htrint hpoint
  have hpeel := trace_exp_sum_le_trace_exp_sum_cgf_one_sided
    (μ := μ) hmeas hherm hmax hind hθ
  have hswap : (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) =
      ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re = _
    rw [Finset.smul_sum]
  rw [hevent, show Real.exp (-θ * t) = (Real.exp (θ * t))⁻¹ by
    rw [show -θ * t = -(θ * t) by ring, Real.exp_neg], inv_mul_eq_div]
  refine hmarkov.trans ?_
  gcongr
  exact hmono.trans (hswap.trans_le hpeel)

/-- Lean implementation helper: the expectation half of the master bound under
one-sided spectral edges and explicit first-moment integrability. -/
lemma master_expectation_upper_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ) {U : ι → ℝ}
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ U k)
    (hind : ProbabilityTheory.iIndepFun X μ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ ≤
      θ⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  classical
  let Y : Ω → Matrix n n ℂ := fun ω => ∑ k, X k ω
  have hYmeas : Measurable Y := measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (Y ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYmax : ∀ ω, lambdaMax (hYherm ω) ≤ ∑ k, U k := fun ω =>
    lambdaMax_matsum_le_sum Finset.univ hherm hmax ω
  have hYint : MIntegrable Y μ :=
    MIntegrable.finsetSum (μ := μ) Finset.univ fun k _ => hXint k
  have hnormY : Integrable (fun ω => ‖Y ω‖) μ :=
    integrable_l2_opNorm_of_mintegrable hYmeas hYint
  have hlamint : Integrable (fun ω => lambdaMax (hYherm ω)) μ := by
    refine Integrable.mono' hnormY
      (measurable_lambdaMax_of_forall hYmeas hYherm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_lambdaMax_le (hYherm ω)
  have hHermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  let Z : Ω → ℝ := fun ω => Real.exp (lambdaMax (hHermθ ω))
  have hZmeas : Measurable Z :=
    Real.measurable_exp.comp
      (measurable_lambdaMax_of_forall (hYmeas.const_smul θ) hHermθ)
  have hZint : Integrable Z μ := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable
      (Real.exp (θ * ∑ k, U k)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    rw [lambdaMax_smul_nonneg (hYherm ω) hθ.le]
    exact mul_le_mul_of_nonneg_left (hYmax ω) hθ.le
  have hlogZint : Integrable (fun ω => Real.log (Z ω)) μ := by
    have heq : (fun ω => Real.log (Z ω)) =
      fun ω => θ * lambdaMax (hYherm ω) := by
      funext ω
      simp only [Z, Real.log_exp]
      exact lambdaMax_smul_nonneg (hYherm ω) hθ.le (hHermθ ω)
    rw [heq]
    exact hlamint.const_mul θ
  have hExpint : MIntegrable (fun ω => NormedSpace.exp (θ • Y ω)) μ :=
    mintegrable_matrixExp_of_lambdaMax_bound hYmeas hYherm hYmax hθ
  have htrint : Integrable
      (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ := by
    have hdiag : ∀ i, Integrable
        (fun ω => (NormedSpace.exp (θ • Y ω) i i).re) μ :=
      fun i => (hExpint i i).re
    simpa [Matrix.trace] using
      (integrable_finsetSum Finset.univ fun i _ => hdiag i)
  have hlogeq : θ * (∫ ω, lambdaMax (hYherm ω) ∂μ) =
      ∫ ω, Real.log (Z ω) ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Z, Real.log_exp]
    exact (lambdaMax_smul_nonneg (hYherm ω) hθ.le (hHermθ ω)).symm
  have hjensen : (∫ ω, Real.log (Z ω) ∂μ) ≤
      Real.log (∫ ω, Z ω ∂μ) :=
    integral_log_le_log_integral'
      (Filter.Eventually.of_forall fun ω => Real.exp_pos _) hZint hlogZint
  have hZtrace : (∫ ω, Z ω ∂μ) ≤
      ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
    refine integral_mono hZint htrint fun ω => ?_
    exact exp_lambdaMax_le_trace_exp (hHermθ ω)
  have hZpos : 0 < ∫ ω, Z ω ∂μ :=
    integral_pos_of_ae_pos (Filter.Eventually.of_forall fun ω => Real.exp_pos _)
      hZint
  have hpeel := trace_exp_sum_le_trace_exp_sum_cgf_one_sided
    (μ := μ) hmeas hherm hmax hind hθ
  have hswap : (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) =
      ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re = _
    rw [Finset.smul_sum]
  have hlogmono : Real.log (∫ ω, Z ω ∂μ) ≤
      Real.log ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    refine Real.log_le_log hZpos ?_
    exact hZtrace.trans (hswap.trans_le hpeel)
  have hchain : θ * (∫ ω, lambdaMax (hYherm ω) ∂μ) ≤
      Real.log ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    rw [hlogeq]
    exact hjensen.trans hlogmono
  rw [inv_mul_eq_div, le_div_iff₀ hθ, mul_comm]
  exact hchain

/-- **Book §6.6.4, first display chain**, with only the genuine one-sided
spectral hypothesis and explicit first/second-moment integrability. -/
lemma bernstein_cgf_trace_bound_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      (Fintype.card n : ℝ) * Real.exp (gBernstein θ L *
        ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖) := by
  have hg : 0 ≤ gBernstein θ L := gBernstein_nonneg hθL
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤
      gBernstein θ L • expectation μ (fun ω => X k ω * X k ω) :=
    fun k => bernstein_matrix_cgf_le_one_sided (μ := μ) (hmeas k)
      (hherm k) (hXint k) (hX2int k) (hcent k) (hmax k) hθ hθL
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gBernstein θ L • ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hE2herm : ∀ k,
      (expectation μ (fun ω => X k ω * X k ω)).IsHermitian := fun k =>
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm k ω))
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hEsumHerm :
      (∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => hE2herm k
  have hgEHerm := isHermitian_real_smul hEsumHerm (gBernstein θ L)
  have h1 := trace_exp_monotone hcgfHerm hgEHerm hsum_le
  refine h1.trans ?_
  have h2 := trace_re_le_card_mul_lambdaMax (isHermitian_exp hgEHerm)
  refine h2.trans ?_
  rw [lambdaMax_exp hgEHerm, lambdaMax_smul_nonneg hEsumHerm hg hgEHerm]
  have h3 : lambdaMax hEsumHerm ≤
      ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ :=
    (le_abs_self _).trans (abs_lambdaMax_le _)
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h3 hg))
    (by positivity)

end OneSidedMasterBounds

end MatrixConcentration


namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ}

section OneSidedHermitianBernstein

/-- Lean implementation helper: the dimension-one centered identity using
explicit first-moment integrability. -/
lemma integral_lambdaMax_eq_zero_of_card_one_one_sided
    (hcard : Fintype.card n = 1)
    (_hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hcent : ∀ k, expectation μ (X k) = 0) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ
      = 0 := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  -- in dimension one, `λ_max = λ_min = ` the Rayleigh value at `e_{i₀}`
  have hsingle : ∀ (A : Matrix n n ℂ) (hA : A.IsHermitian),
      lambdaMax hA = (A i₀ i₀).re := by
    intro A hA
    have hminmax : lambdaMin hA = lambdaMax hA := by
      obtain ⟨imax, himax⟩ := exists_eigenvalues_eq_lambdaMax hA
      obtain ⟨imin, himin⟩ := exists_eigenvalues_eq_lambdaMin hA
      have hii : imin = imax := Fintype.card_le_one_iff.mp hcard.le imin imax
      rw [← himax, ← himin, hii]
    have hunit : l2norm (Pi.single i₀ (1 : ℂ)) = 1 := l2norm_single i₀
    have hup : rayleigh A (Pi.single i₀ (1 : ℂ)) ≤ lambdaMax hA :=
      rayleigh_le_lambdaMax_of_unit hA hunit
    have hlo : lambdaMin hA ≤ rayleigh A (Pi.single i₀ (1 : ℂ)) :=
      lambdaMin_le_rayleigh_of_unit hA hunit
    have hray : rayleigh A (Pi.single i₀ (1 : ℂ)) = (A i₀ i₀).re := by
      rw [rayleigh]
      congr 1
      have hstar : star (Pi.single i₀ (1 : ℂ)) =
          (Pi.single i₀ (1 : ℂ) : n → ℂ) := by
        funext i
        rw [Pi.star_apply]
        by_cases h : i = i₀
        · subst h
          rw [Pi.single_eq_same, star_one]
        · rw [Pi.single_eq_of_ne h, star_zero]
      rw [hstar, single_dotProduct, one_mul]
      rw [show (A *ᵥ Pi.single i₀ (1 : ℂ)) i₀ =
          (fun j => A i₀ j) ⬝ᵥ Pi.single i₀ (1 : ℂ) from rfl]
      rw [dotProduct_single, mul_one]
    rw [← hray]
    linarith
  have hfun : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω))) = fun ω => ((∑ k, X k ω) i₀ i₀).re :=
    funext fun ω => hsingle _ _
  rw [hfun]
  have hint : ∀ k, Integrable (fun ω => X k ω i₀ i₀) μ := fun k =>
    hXint k i₀ i₀
  have h1 : (fun ω => ((∑ k, X k ω) i₀ i₀).re) =
      fun ω => ∑ k, (X k ω i₀ i₀).re := by
    funext ω
    rw [show (∑ k, X k ω) i₀ i₀ = ∑ k, X k ω i₀ i₀ from by
      rw [Matrix.sum_apply], Complex.re_sum]
  rw [h1, MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
    (f := fun k (ω : Ω) => (X k ω i₀ i₀).re) fun k _ => (hint k).re]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h2 : ∫ ω, (X k ω i₀ i₀).re ∂μ = (∫ ω, X k ω i₀ i₀ ∂μ).re :=
    integral_re (hint k)
  rw [h2, show (∫ ω, X k ω i₀ i₀ ∂μ) = expectation μ (X k) i₀ i₀ from
    (expectation_apply _ _ _).symm, hcent k]
  simp

/-- **Book Theorem 6.6.1, equation (6.6.2)** under its literal one-sided
spectral hypothesis.  The explicit integrability assumptions replace the
earlier auxiliary two-sided norm bound. -/
theorem matrix_bernstein_herm_expectation_one_sided
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      Real.sqrt (2 * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ *
        Real.log (Fintype.card n)) +
      L / 3 * Real.log (Fintype.card n) := by
  classical
  set v : ℝ := ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ with hvdef
  have hv0 : 0 ≤ v := norm_nonneg _
  set D : ℝ := Real.log (Fintype.card n) with hDdef
  have hD0 : 0 ≤ D := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  rcases eq_or_lt_of_le hD0 with hD | hD
  · -- `log d = 0`, i.e. `d = 1`
    have hcard : Fintype.card n = 1 := by
      by_contra hne
      have h2 : 1 < Fintype.card n :=
        lt_of_le_of_ne Fintype.card_pos (Ne.symm hne)
      have h3 : 0 < D := by
        rw [hDdef]
        exact Real.log_pos (by exact_mod_cast h2)
      linarith [hD]
    rw [integral_lambdaMax_eq_zero_of_card_one_one_sided hcard hmeas hherm hXint hcent,
      ← hD]
    rw [mul_zero, Real.sqrt_zero, mul_zero, add_zero]
  · -- main case `0 < log d`: ε-argument over admissible witnesses
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ : ℝ := ε ^ 2 / (2 * D) with hδdef
    have hδ0 : 0 < δ := by positivity
    set s : ℝ := Real.sqrt ((v + δ) / (2 * D)) with hsdef
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hssq : s ^ 2 = (v + δ) / (2 * D) := Real.sq_sqrt (by positivity)
    have hsl0 : 0 < s + L / 3 := by linarith
    set θ : ℝ := (s + L / 3)⁻¹ with hθdef
    have hθpos : 0 < θ := inv_pos.mpr hsl0
    have hθs : θ * (s + L / 3) = 1 := inv_mul_cancel₀ (ne_of_gt hsl0)
    have h1mθL : 1 - θ * L / 3 = θ * s := by
      have h : θ * s + θ * L / 3 = 1 := by
        rw [← hθs]
        ring
      linarith
    have hθL3 : θ * L < 3 := by
      have h2 : 0 < θ * s := mul_pos hθpos hs0
      nlinarith [h1mθL]
    -- master bound + cgf trace bound
    have h1 := master_expectation_upper_one_sided (μ := μ) hmeas hherm hXint hmax hind hθpos
    have h2 := bernstein_cgf_trace_bound_one_sided (μ := μ) hmeas hherm hXint hX2int hcent hmax
      hθpos hθL3
    have hpos : 0 < ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re :=
      trace_exp_re_pos (isHermitian_matsum Finset.univ fun k =>
        isHermitian_cfc_log _)
    have h4 : Real.log ((Fintype.card n : ℝ) *
        Real.exp (gBernstein θ L * v)) = D + gBernstein θ L * v := by
      rw [Real.log_mul (by exact_mod_cast Fintype.card_pos.ne')
        (Real.exp_pos _).ne', Real.log_exp, hDdef]
    have hchain : ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ ≤ θ⁻¹ * (D + gBernstein θ L * v) := by
      refine h1.trans ?_
      have h3 : Real.log ((NormedSpace.exp
          (∑ k, matrixCgf μ (X k) θ)).trace).re ≤ D + gBernstein θ L * v :=
        (Real.log_le_log hpos h2).trans (le_of_eq h4)
      exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hθpos).le
    refine hchain.trans ?_
    -- the algebra: `θ⁻¹(D + g(θ)v) = (s + L/3)D + v/(2s) ≤ √(2vD) + (L/3)D + ε`
    have hginv : θ⁻¹ * (D + gBernstein θ L * v) =
        (s + L / 3) * D + v / (2 * s) := by
      have hg : gBernstein θ L = θ / (2 * s) := by
        rw [gBernstein, h1mθL]
        field_simp
      rw [hg, hθdef, inv_inv]
      have hθne : ((s + L / 3)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (ne_of_gt hsl0)
      field_simp
    rw [hginv]
    have h5 : v / (2 * s) ≤ D * s := by
      have h6 : v + δ = 2 * D * s ^ 2 := by
        rw [hssq]
        field_simp
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hδ0]
    have h7 : 2 * (D * s) ≤ Real.sqrt (2 * v * D) + ε := by
      have h9 : 2 * D * s = Real.sqrt (2 * D * (v + δ)) := by
        have h8 : 2 * D * (v + δ) = (2 * D * s) ^ 2 := by
          have h8a : (2 * D * s) ^ 2 = 4 * D ^ 2 * ((v + δ) / (2 * D)) := by
            rw [← hssq]
            ring
          rw [h8a]
          field_simp
          ring
        rw [h8, Real.sqrt_sq (by positivity)]
      have h10 : Real.sqrt (2 * D * (v + δ)) ≤
          Real.sqrt (2 * D * v) + Real.sqrt (2 * D * δ) := by
        rw [show 2 * D * (v + δ) = 2 * D * v + 2 * D * δ from by ring]
        exact sqrt_add_le (by positivity) (by positivity)
      have h11 : Real.sqrt (2 * D * δ) = ε := by
        rw [hδdef, show 2 * D * (ε ^ 2 / (2 * D)) = ε ^ 2 from by
          field_simp, Real.sqrt_sq hε.le]
      have h12 : Real.sqrt (2 * D * v) = Real.sqrt (2 * v * D) := by
        rw [show 2 * D * v = 2 * v * D from by ring]
      nlinarith [h9, h10, h11, h12]
    linarith [h5, h7]

/-- **Book Theorem 6.6.1, equation (6.6.3)** under its literal one-sided
spectral hypothesis.  The explicit integrability assumptions replace the
earlier auxiliary two-sided norm bound. -/
theorem matrix_bernstein_herm_tail_one_sided
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ + L * t / 3)) := by
  classical
  set v : ℝ := ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ with hvdef
  have hv0 : 0 ≤ v := norm_nonneg _
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [probReal_univ] at h
  have hden0 : (0 : ℝ) ≤ v + L * t / 3 := by positivity
  rcases eq_or_lt_of_le hden0 with hden | hden
  · -- degenerate denominator: the bound reads `P ≤ d·exp(0/0) = d`
    rw [← hden, div_zero, Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- `t = 0`: the bound reads `P ≤ d·exp(0) = d`
    rw [← ht0]
    rw [show (-((0 : ℝ) ^ 2) / 2 / (v + L * 0 / 3)) = 0 by norm_num,
      Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  rcases eq_or_lt_of_le hv0 with hv | hv
  · -- `v = 0 < Lt`: use `θ = 2/L`
    have hLt : 0 < L * t := by
      rw [← hv] at hden
      nlinarith [hden]
    have hLpos : 0 < L := by
      rcases mul_pos_iff.mp hLt with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    set θ : ℝ := 2 / L with hθdef
    have hθpos : 0 < θ := by positivity
    have hθL3 : θ * L < 3 := by
      rw [hθdef, div_mul_cancel₀ _ (ne_of_gt hLpos)]
      norm_num
    have h1 := master_tail_upper_one_sided (μ := μ) hmeas hherm hXint hmax hind t hθpos
    have h2 := bernstein_cgf_trace_bound_one_sided (μ := μ) hmeas hherm hXint hX2int hcent hmax
      hθpos hθL3
    rw [← hvdef, ← hv, mul_zero, Real.exp_zero, mul_one] at h2
    have key : -(t ^ 2) / 2 / (v + L * t / 3) = -(3 * t) / (2 * L) := by
      rw [← hv]
      rw [show (0 : ℝ) + L * t / 3 = L * t / 3 from by ring]
      rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hfrac : -θ * t = -(4 * t) / (2 * L) := by
      rw [hθdef]
      field_simp
      ring
    calc μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
          (fun k => hherm k ω))}
        ≤ Real.exp (-θ * t) *
          ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := h1
      _ ≤ Real.exp (-θ * t) * (Fintype.card n : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) * Real.exp (-θ * t) := by ring
      _ ≤ (Fintype.card n : ℝ) *
          Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine Real.exp_le_exp.mpr ?_
          have h2L : (0 : ℝ) < 2 * L := by linarith
          rw [key, hfrac, div_le_div_iff₀ h2L h2L]
          nlinarith [mul_pos htpos hLpos]
  · -- main case `v > 0`: the inspired choice `θ = t/(v + Lt/3)`
    have hdne : (v + L * t / 3) ≠ 0 := ne_of_gt hden
    set θ : ℝ := t / (v + L * t / 3) with hθdef
    have hθpos : 0 < θ := div_pos htpos hden
    have hθL3 : θ * L < 3 := by
      rw [hθdef, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [hv, htpos, hL]
    have h1mθL : 1 - θ * L / 3 = v / (v + L * t / 3) := by
      rw [hθdef]
      field_simp
      ring
    have hexpid : gBernstein θ L * v + -θ * t =
        -(t ^ 2) / 2 / (v + L * t / 3) := by
      rw [gBernstein, h1mθL, hθdef]
      have hvne : v ≠ 0 := ne_of_gt hv
      field_simp
      ring
    have h1 := master_tail_upper_one_sided (μ := μ) hmeas hherm hXint hmax hind t hθpos
    have h2 := bernstein_cgf_trace_bound_one_sided (μ := μ) hmeas hherm hXint hX2int hcent hmax
      hθpos hθL3
    rw [← hvdef] at h2
    calc μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
          (fun k => hherm k ω))}
        ≤ Real.exp (-θ * t) *
          ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := h1
      _ ≤ Real.exp (-θ * t) * ((Fintype.card n : ℝ) *
          Real.exp (gBernstein θ L * v)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) *
          Real.exp (gBernstein θ L * v + -θ * t) := by
          rw [Real.exp_add]
          ring
      _ = (Fintype.card n : ℝ) *
          Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) := by rw [hexpid]

end OneSidedHermitianBernstein

end MatrixConcentration

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ}

section OneSidedAe

/-- Lean implementation helper: entrywise matrix integrability is invariant
under almost-everywhere equality. -/
lemma MIntegrable.congr_ae {Y Z : Ω → Matrix n n ℂ}
    (hY : MIntegrable Y μ) (h : Y =ᵐ[μ] Z) : MIntegrable Z μ := fun i j =>
  (hY i j).congr (h.mono fun _ hω => congrArg (fun A => A i j) hω)

/-- Lean implementation helper: replace a Hermitian matrix by zero precisely
where its upper spectral edge exceeds `L`. -/
noncomputable def truncateLambdaMax (L : ℝ) (Y : Ω → Matrix n n ℂ)
    (hY : ∀ ω, (Y ω).IsHermitian) (ω : Ω) : Matrix n n ℂ :=
  if lambdaMax (hY ω) ≤ L then Y ω else 0

/-- Lean implementation helper: upper-edge truncation is measurable. -/
lemma measurable_truncateLambdaMax {Y : Ω → Matrix n n ℂ}
    (hYm : Measurable Y) (hY : ∀ ω, (Y ω).IsHermitian) :
    Measurable (truncateLambdaMax L Y hY) := by
  classical
  apply Measurable.ite
    (measurableSet_le (measurable_lambdaMax_of_forall hYm hY) measurable_const)
    hYm measurable_const

/-- Lean implementation helper: upper-edge truncation remains Hermitian. -/
lemma isHermitian_truncateLambdaMax {Y : Ω → Matrix n n ℂ}
    (hY : ∀ ω, (Y ω).IsHermitian) (ω : Ω) :
    (truncateLambdaMax L Y hY ω).IsHermitian := by
  classical
  rw [truncateLambdaMax]
  split_ifs
  · exact hY ω
  · exact Matrix.isHermitian_zero

/-- Lean implementation helper: upper-edge truncation enforces the bound
pointwise when `L ≥ 0`. -/
lemma lambdaMax_truncateLambdaMax_le {Y : Ω → Matrix n n ℂ}
    (hY : ∀ ω, (Y ω).IsHermitian) (hL : 0 ≤ L) (ω : Ω) :
    lambdaMax (isHermitian_truncateLambdaMax (L := L) hY ω) ≤ L := by
  classical
  by_cases h : lambdaMax (hY ω) ≤ L
  · simpa only [truncateLambdaMax, if_pos h] using h
  · have hz : truncateLambdaMax L Y hY ω = 0 := by
      simp only [truncateLambdaMax, if_neg h]
    rw [lambdaMax_congr hz (isHermitian_truncateLambdaMax (L := L) hY ω)
      Matrix.isHermitian_zero, lambdaMax_zero_matrix]
    exact hL

/-- Lean implementation helper: an a.e. upper spectral bound makes the
truncation a.e. equal to the original family. -/
lemma truncateLambdaMax_ae_eq {Y : Ω → Matrix n n ℂ}
    (hY : ∀ ω, (Y ω).IsHermitian)
    (hmax : ∀ᵐ ω ∂μ, lambdaMax (hY ω) ≤ L) :
    truncateLambdaMax L Y hY =ᵐ[μ] Y :=
  hmax.mono fun ω hω => by simp only [truncateLambdaMax, if_pos hω]

/-- **Book Lemma 6.6.2 (Matrix Bernstein: MGF Bound)** with the source's
almost-sure interpretation of the one-sided upper spectral edge.  This is the
almost-sure counterpart of `bernstein_matrix_mgf_le_one_sided`; unlike the
earlier `bernstein_matrix_mgf_le`, it needs no two-sided norm bound. -/
theorem bernstein_matrix_mgf_le_one_sided_ae {Y : Ω → Matrix n n ℂ}
    (hYm : Measurable Y) (hherm : ∀ ω, (Y ω).IsHermitian)
    (hYint : MIntegrable Y μ)
    (hY2int : MIntegrable (fun ω => Y ω * Y ω) μ)
    (hcent : expectation μ Y = 0)
    (hmax : ∀ᵐ ω ∂μ, lambdaMax (hherm ω) ≤ L) (hL : 0 ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    matrixMgf μ Y θ ≤ NormedSpace.exp
      (gBernstein θ L • expectation μ (fun ω => Y ω * Y ω)) := by
  let Y' : Ω → Matrix n n ℂ := truncateLambdaMax L Y hherm
  have hae : Y' =ᵐ[μ] Y := truncateLambdaMax_ae_eq hherm hmax
  have hYm' : Measurable Y' := measurable_truncateLambdaMax hYm hherm
  have hherm' : ∀ ω, (Y' ω).IsHermitian := isHermitian_truncateLambdaMax hherm
  have hmax' : ∀ ω, lambdaMax (hherm' ω) ≤ L :=
    lambdaMax_truncateLambdaMax_le hherm hL
  have hYint' : MIntegrable Y' μ := hYint.congr_ae hae.symm
  have hsquare : (fun ω => Y' ω * Y' ω) =ᵐ[μ]
      fun ω => Y ω * Y ω :=
    hae.mono fun ω hω => congrArg (fun A : Matrix n n ℂ => A * A) hω
  have hY2int' : MIntegrable (fun ω => Y' ω * Y' ω) μ :=
    hY2int.congr_ae hsquare.symm
  have hcent' : expectation μ Y' = 0 := by
    rw [expectation_congr_ae hae, hcent]
  have h := bernstein_matrix_mgf_le_one_sided hYm' hherm' hYint' hY2int'
    hcent' hmax' hθ hθL
  have hmgf : matrixMgf μ Y' θ = matrixMgf μ Y θ := by
    rw [matrixMgf_def, matrixMgf_def]
    exact expectation_congr_ae (hae.mono fun ω hω => congrArg
      (fun A : Matrix n n ℂ => NormedSpace.exp (θ • A)) hω)
  rw [hmgf, expectation_congr_ae hsquare] at h
  exact h

/-- **Book Lemma 6.6.2 (Matrix Bernstein: CGF Bound)** with the source's
almost-sure interpretation of the one-sided upper spectral edge.  This is the
almost-sure counterpart of `bernstein_matrix_cgf_le_one_sided`; unlike the
earlier `bernstein_matrix_cgf_le`, it needs no two-sided norm bound. -/
theorem bernstein_matrix_cgf_le_one_sided_ae {Y : Ω → Matrix n n ℂ}
    (hYm : Measurable Y) (hherm : ∀ ω, (Y ω).IsHermitian)
    (hYint : MIntegrable Y μ)
    (hY2int : MIntegrable (fun ω => Y ω * Y ω) μ)
    (hcent : expectation μ Y = 0)
    (hmax : ∀ᵐ ω ∂μ, lambdaMax (hherm ω) ≤ L) (hL : 0 ≤ L)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    matrixCgf μ Y θ ≤
      gBernstein θ L • expectation μ (fun ω => Y ω * Y ω) := by
  let Y' : Ω → Matrix n n ℂ := truncateLambdaMax L Y hherm
  have hae : Y' =ᵐ[μ] Y := truncateLambdaMax_ae_eq hherm hmax
  have hYm' : Measurable Y' := measurable_truncateLambdaMax hYm hherm
  have hherm' : ∀ ω, (Y' ω).IsHermitian := isHermitian_truncateLambdaMax hherm
  have hmax' : ∀ ω, lambdaMax (hherm' ω) ≤ L :=
    lambdaMax_truncateLambdaMax_le hherm hL
  have hYint' : MIntegrable Y' μ := hYint.congr_ae hae.symm
  have hsquare : (fun ω => Y' ω * Y' ω) =ᵐ[μ]
      fun ω => Y ω * Y ω :=
    hae.mono fun ω hω => congrArg (fun A : Matrix n n ℂ => A * A) hω
  have hY2int' : MIntegrable (fun ω => Y' ω * Y' ω) μ :=
    hY2int.congr_ae hsquare.symm
  have hcent' : expectation μ Y' = 0 := by
    rw [expectation_congr_ae hae, hcent]
  have h := bernstein_matrix_cgf_le_one_sided hYm' hherm' hYint' hY2int'
    hcent' hmax' hθ hθL
  have hmgf : matrixMgf μ Y' θ = matrixMgf μ Y θ := by
    rw [matrixMgf_def, matrixMgf_def]
    exact expectation_congr_ae (hae.mono fun ω hω => congrArg
      (fun A : Matrix n n ℂ => NormedSpace.exp (θ • A)) hω)
  have hcgf : matrixCgf μ Y' θ = matrixCgf μ Y θ := by
    rw [matrixCgf, matrixCgf, hmgf]
  rw [hcgf, expectation_congr_ae hsquare] at h
  exact h

/-- **Book Theorem 6.6.1, equation (6.6.2)** with the source's almost-sure
interpretation of the one-sided upper spectral edge. -/
theorem matrix_bernstein_herm_expectation_one_sided_ae
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      Real.sqrt (2 * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ *
        Real.log (Fintype.card n)) +
      L / 3 * Real.log (Fintype.card n) := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k =>
    truncateLambdaMax L (X k) (hherm k)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    truncateLambdaMax_ae_eq (hherm k) (hmax k)
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_truncateLambdaMax (hmeas k) (hherm k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k =>
    isHermitian_truncateLambdaMax (hherm k)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k =>
    lambdaMax_truncateLambdaMax_le (hherm k) hL
  have hXint' : ∀ k, MIntegrable (X' k) μ := fun k =>
    (hXint k).congr_ae (hae k).symm
  have hX2int' : ∀ k, MIntegrable (fun ω => X' k ω * X' k ω) μ := fun k =>
    (hX2int k).congr_ae ((hae k).symm.mono fun ω hω =>
      congrArg (fun A : Matrix n n ℂ => A * A) hω)
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hind' : ProbabilityTheory.iIndepFun X' μ :=
    ProbabilityTheory.iIndepFun.congr (fun k => (hae k).symm) hind
  have h := matrix_bernstein_herm_expectation_one_sided (μ := μ) hmeas'
    hherm' hXint' hX2int' hcent' hmax' hL hind'
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω :=
    (MeasureTheory.ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ] fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hlhs : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))) =ᵐ[μ]
      fun ω => lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) := hsum.mono fun ω hω =>
    lambdaMax_congr hω _ _
  have hsquare : ∀ k, (fun ω => X' k ω * X' k ω) =ᵐ[μ]
      fun ω => X k ω * X k ω := fun k =>
    (hae k).mono fun ω hω => congrArg (fun A : Matrix n n ℂ => A * A) hω
  rw [integral_congr_ae hlhs,
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hsquare k)] at h
  exact h

/-- **Book Theorem 6.6.1, equation (6.6.3)** with an almost-sure one-sided
upper spectral edge. -/
theorem matrix_bernstein_herm_tail_one_sided_ae
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ + L * t / 3)) := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k =>
    truncateLambdaMax L (X k) (hherm k)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    truncateLambdaMax_ae_eq (hherm k) (hmax k)
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_truncateLambdaMax (hmeas k) (hherm k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k =>
    isHermitian_truncateLambdaMax (hherm k)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k =>
    lambdaMax_truncateLambdaMax_le (hherm k) hL
  have hXint' : ∀ k, MIntegrable (X' k) μ := fun k =>
    (hXint k).congr_ae (hae k).symm
  have hX2int' : ∀ k, MIntegrable (fun ω => X' k ω * X' k ω) μ := fun k =>
    (hX2int k).congr_ae ((hae k).symm.mono fun ω hω =>
      congrArg (fun A : Matrix n n ℂ => A * A) hω)
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hind' : ProbabilityTheory.iIndepFun X' μ :=
    ProbabilityTheory.iIndepFun.congr (fun k => (hae k).symm) hind
  have h := matrix_bernstein_herm_tail_one_sided (μ := μ) hmeas' hherm'
    hXint' hX2int' hcent' hmax' hL hind' ht
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω :=
    (MeasureTheory.ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ] fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hevent : ∀ᵐ ω ∂μ,
      (t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm' k ω))) =
      (t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))) := hsum.mono fun ω hω => by
    rw [lambdaMax_congr hω _ _]
  have hmeasure : μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))} =
      μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    congr 1
    exact MeasureTheory.measure_congr hevent
  have hsquare : ∀ k, (fun ω => X' k ω * X' k ω) =ᵐ[μ]
      fun ω => X k ω * X k ω := fun k =>
    (hae k).mono fun ω hω => congrArg (fun A : Matrix n n ℂ => A * A) hω
  rw [hmeasure,
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hsquare k)] at h
  exact h

end OneSidedAe

end MatrixConcentration

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {Lm : ℝ}

section OneSidedLowerBernstein

/-- **Book §6.6.2, first display**, with the source's almost-sure lower
spectral-edge hypothesis and explicit first/second-moment integrability. -/
theorem matrix_bernstein_herm_min_expectation_one_sided_ae
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hminbd : ∀ k, ∀ᵐ ω ∂μ, -Lm ≤ lambdaMin (hherm k ω))
    (hLm : 0 ≤ Lm) (hind : ProbabilityTheory.iIndepFun X μ) :
    -(Real.sqrt (2 * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ *
        Real.log (Fintype.card n))) -
      Lm / 3 * Real.log (Fintype.card n) ≤
    ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k ω => -(X k ω)
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_matrix_neg_fun.comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω => (hherm k ω).neg
  have hXint' : ∀ k, MIntegrable (X' k) μ := fun k => (hXint k).neg
  have hsqfun : ∀ k, (fun ω => X' k ω * X' k ω) =
      fun ω => X k ω * X k ω := fun k => by
    funext ω
    exact neg_mul_neg (X k ω) (X k ω)
  have hX2int' : ∀ k, MIntegrable (fun ω => X' k ω * X' k ω) μ := fun k => by
    rw [hsqfun k]
    exact hX2int k
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    rw [show X' k = fun ω => -(X k ω) from rfl, expectation_neg, hcent k,
      neg_zero]
  have hmax' : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm' k ω) ≤ Lm := fun k =>
    (hminbd k).mono fun ω hω => by
      rw [lambdaMax_neg (hherm k ω)]
      linarith
  have hind' : ProbabilityTheory.iIndepFun X' μ :=
    hind.comp (fun _ M => -M) fun _ => measurable_matrix_neg_fun
  have h := matrix_bernstein_herm_expectation_one_sided_ae (μ := μ) hmeas'
    hherm' hXint' hX2int' hcent' hmax' hLm hind'
  have hsq : (∑ k, expectation μ (fun ω => X' k ω * X' k ω)) =
      ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    exact Finset.sum_congr rfl fun k _ => by rw [hsqfun k]
  rw [hsq] at h
  have hfun : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))) =
      fun ω => -(lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))) := by
    funext ω
    have hsumneg : (∑ k, X' k ω) = -(∑ k, X k ω) := by
      change (∑ k, -(X k ω)) = -(∑ k, X k ω)
      rw [Finset.sum_neg_distrib]
    rw [lambdaMax_congr hsumneg (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))
      ((isHermitian_matsum Finset.univ (fun k => hherm k ω)).neg)]
    exact lambdaMax_neg (isHermitian_matsum Finset.univ (fun k => hherm k ω))
  rw [hfun, integral_neg] at h
  linarith

/-- **Book §6.6.2, second display**, with an almost-sure lower spectral edge
and explicit first/second-moment integrability. -/
theorem matrix_bernstein_herm_min_tail_one_sided_ae
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hminbd : ∀ k, ∀ᵐ ω ∂μ, -Lm ≤ lambdaMin (hherm k ω))
    (hLm : 0 ≤ Lm) (hind : ProbabilityTheory.iIndepFun X μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ≤ -t} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ + Lm * t / 3)) := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k ω => -(X k ω)
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_matrix_neg_fun.comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω => (hherm k ω).neg
  have hXint' : ∀ k, MIntegrable (X' k) μ := fun k => (hXint k).neg
  have hsqfun : ∀ k, (fun ω => X' k ω * X' k ω) =
      fun ω => X k ω * X k ω := fun k => by
    funext ω
    exact neg_mul_neg (X k ω) (X k ω)
  have hX2int' : ∀ k, MIntegrable (fun ω => X' k ω * X' k ω) μ := fun k => by
    rw [hsqfun k]
    exact hX2int k
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    rw [show X' k = fun ω => -(X k ω) from rfl, expectation_neg, hcent k,
      neg_zero]
  have hmax' : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm' k ω) ≤ Lm := fun k =>
    (hminbd k).mono fun ω hω => by
      rw [lambdaMax_neg (hherm k ω)]
      linarith
  have hind' : ProbabilityTheory.iIndepFun X' μ :=
    hind.comp (fun _ M => -M) fun _ => measurable_matrix_neg_fun
  have h := matrix_bernstein_herm_tail_one_sided_ae (μ := μ) hmeas' hherm'
    hXint' hX2int' hcent' hmax' hLm hind' ht
  have hsq : (∑ k, expectation μ (fun ω => X' k ω * X' k ω)) =
      ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    exact Finset.sum_congr rfl fun k _ => by rw [hsqfun k]
  rw [hsq] at h
  have hset : {ω | lambdaMin (isHermitian_matsum Finset.univ
      (fun k => hherm k ω)) ≤ -t} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm' k ω))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hsumneg : (∑ k, X' k ω) = -(∑ k, X k ω) := by
      change (∑ k, -(X k ω)) = -(∑ k, X k ω)
      rw [Finset.sum_neg_distrib]
    rw [lambdaMax_congr hsumneg (isHermitian_matsum Finset.univ
      (fun k => hherm' k ω))
      ((isHermitian_matsum Finset.univ (fun k => hherm k ω)).neg),
      lambdaMax_neg (isHermitian_matsum Finset.univ (fun k => hherm k ω))]
    constructor <;> intro h1 <;> linarith
  rw [hset]
  exact h

/-- Pointwise-edge form of `matrix_bernstein_herm_min_expectation_one_sided_ae`. -/
theorem matrix_bernstein_herm_min_expectation_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hminbd : ∀ k ω, -Lm ≤ lambdaMin (hherm k ω))
    (hLm : 0 ≤ Lm) (hind : ProbabilityTheory.iIndepFun X μ) :
    -(Real.sqrt (2 * ‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ *
        Real.log (Fintype.card n))) -
      Lm / 3 * Real.log (Fintype.card n) ≤
    ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ :=
  matrix_bernstein_herm_min_expectation_one_sided_ae hmeas hherm hXint hX2int
    hcent (fun k => Filter.Eventually.of_forall (hminbd k)) hLm hind

/-- Pointwise-edge form of `matrix_bernstein_herm_min_tail_one_sided_ae`. -/
theorem matrix_bernstein_herm_min_tail_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hminbd : ∀ k ω, -Lm ≤ lambdaMin (hherm k ω))
    (hLm : 0 ≤ Lm) (hind : ProbabilityTheory.iIndepFun X μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ≤ -t} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / 2 /
        (‖∑ k, expectation μ (fun ω => X k ω * X k ω)‖ + Lm * t / 3)) :=
  matrix_bernstein_herm_min_tail_one_sided_ae hmeas hherm hXint hX2int hcent
    (fun k => Filter.Eventually.of_forall (hminbd k)) hLm hind ht

end OneSidedLowerBernstein

end MatrixConcentration

namespace MatrixConcentration

open Matrix MeasureTheory Finset ProbabilityTheory
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

section IntegrableRosenthalPinelisAliases

variable {d₁ d₂ : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Book display (6.1.6)** with the distributional-symmetry hypothesis used
by CGT12a, Theorem A.1(2), under the natural finite-heavy-tail assumption.
This strengthens the bounded `matrix_rosenthal_pinelis_symmetric` by replacing
its uniform bound with integrability of the maximum squared summand. -/
theorem matrix_rosenthal_pinelis_symmetric_integrable
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) μ)
    (hM : Integrable (fun ω => ⨆ k, ‖S k ω‖ ^ 2) μ) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 *
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d₁ + d₂)) +
      4 * Real.exp 1 * (maxSummandSq S μ) ^ ((1 : ℝ) / 2) *
        Real.log (d₁ + d₂) :=
  matrix_rosenthal_pinelis_symmetric_integrable_aux h_indep h_meas h_symm hM

/-- Centered finite-heavy-tail counterpart of **Book display (6.1.6)** with
the explicit `sqrt 2` variance and `2` maximum-summand coefficient losses.
This strengthens the bounded `matrix_rosenthal_pinelis_centered_with_loss` by
replacing its uniform bound with integrability of the maximum squared
summand. -/
theorem matrix_rosenthal_pinelis_centered_with_loss_integrable
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation μ (S k) = 0)
    (hM : Integrable (fun ω => ⨆ k, ‖S k ω‖ ^ 2) μ) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (4 * Real.exp 1 *
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d₁ + d₂)) +
      8 * Real.exp 1 * (maxSummandSq S μ) ^ ((1 : ℝ) / 2) *
        Real.log (d₁ + d₂) :=
  matrix_rosenthal_pinelis_centered_with_loss_integrable_aux
    h_indep h_meas h_cent hM

end IntegrableRosenthalPinelisAliases

end MatrixConcentration
