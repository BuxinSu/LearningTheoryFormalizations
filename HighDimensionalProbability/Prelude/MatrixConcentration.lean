import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries
import MatrixConcentration.Chapter5_SumOfPSDMatrices

/- This compatibility bridge intentionally preserves the explicit finite-index
instances of the frozen upstream API, even where a particular result does not
mention every instance in its conclusion.  Removing them would create an API
delta from the ported declarations merely to satisfy signature linters. -/
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/- The ported Bernstein development uses a common enlarged heartbeat budget
across several tightly coupled proof sections.  The repeated unscoped settings
below mirror those section boundaries; keeping that structure avoids a large,
non-mathematical reindentation of the verified upstream proofs. -/
set_option linter.style.setOption false

/-!
# Project-owned matrix Bernstein infrastructure

This file contains the buildable Bernstein portion of the frozen upstream
bounded-random-matrices development.  That upstream module currently imports
the broken, unused
`MatrixConcentration.Appendix_RosenthalPinelis`; this project-owned module
deliberately omits that import and stops before the sampling material that is
irrelevant to this project's uses.  The frozen sources themselves are unchanged.

All declarations below retain the verified upstream proofs and namespace.  No
module in this project may import both this helper and the frozen upstream module,
since that would duplicate the declaration names.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset Function
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

section PortedInterfaceHelpers

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Measurability of Hermitian dilation. This small helper is copied from the
front of the frozen Rosenthal appendix because the Bernstein proof needs it,
while importing that appendix is currently impossible.

**Lean implementation helper.** -/
lemma measurable_hermDilation_fun :
    Measurable fun B : Matrix m n ℂ => hermDilation B := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  rcases i with i | i <;> rcases j with j | j
  · exact measurable_const
  · exact measurable_entry i j
  · exact continuous_star.measurable.comp (measurable_entry j i)
  · exact measurable_const

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [IsProbabilityMeasure μ]

/-- Rectangular entry bound `|a_ij| <= ||A||`.

**Lean implementation helper.** -/
lemma norm_entry_le_l2_opNorm_rect {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (A : Matrix p q ℂ) (i : p) (j : q) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h := norm_dotProduct_mulVec_le A (Pi.single i 1) (Pi.single j 1)
  have h1 : star (Pi.single i (1 : ℂ)) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
    rw [Matrix.mulVec_single]
    change (∑ k, star ((Pi.single i (1 : ℂ) : p → ℂ) k) * (A k j * 1)) = A i j
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  letI : Nonempty p := ⟨i⟩
  letI : Nonempty q := ⟨j⟩
  have hsingle1 : l2norm (Pi.single i (1 : ℂ) : p → ℂ) = 1 := l2norm_single i
  have hsingle2 : l2norm (Pi.single j (1 : ℂ) : q → ℂ) = 1 := l2norm_single j
  rw [h1, hsingle1, hsingle2] at h
  simpa using h

/-- Entrywise integrability of a rectangular random matrix from a uniform
operator-norm bound.

**Lean implementation helper.** -/
lemma mintegrable_rect_of_norm_bound {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] {Z : Ω → Matrix p q ℂ} {C : ℝ}
    (hZm : Measurable Z) (hbd : ∀ ω, ‖Z ω‖ ≤ C) : MIntegrable Z μ := by
  refine MIntegrable.of_bound hZm C
    (Filter.Eventually.of_forall fun ω i j => ?_)
  exact (norm_entry_le_l2_opNorm_rect _ _ _).trans (hbd ω)

end PortedInterfaceHelpers

end MatrixConcentration

/-!
# Shared matrix-concentration infrastructure

This project-owned port follows a separate Tropp-style matrix-concentration
source and is shared Lean infrastructure; its section numbers are not citations
to Vershynin's *High-Dimensional Probability*. It contains:

* scalar, mgf, and cgf ingredients for matrix Bernstein;
* Hermitian and rectangular Bernstein inequalities;
* random matrix sampling and sparsification;
* randomized matrix multiplication and random-feature bounds;
* optimality, Rosenthal–Pinelis variants, and variance comparisons.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Scalar toolkit for the Bernstein mgf bound

The proof of the matrix Bernstein mgf bound rests on properties of the scalar
function

`f(x) = (e^{θx} − θx − 1)/x²`, `f(0) = θ²/2`,

which the source asserts with one-line justifications:

* the monotonicity of `f`, obtained from the sign of its derivative;
* the "clever application of Taylor series"
  `f(L) ≤ (θ²/2)/(1 − θL/3)` via `q! ≥ 2·3^{q−2}`.

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
  what the Transfer Rule needs in the matrix mgf proof.

-/

namespace MatrixConcentration

open Real

section KFunction

/-- Recovered prerequisite from,
`k′(u) = (u−1)eᵘ + 1 ≥ 0` for all
`u` (the inner derivative in the source's "its derivative is positive").

**Lean implementation helper.** -/
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

/-- `HasDerivAt` for `k(u) = (u−2)eᵘ + u + 2`.

**Lean implementation helper.** -/
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

/-- Recovered prerequisite from,
`k(u) = (u−2)eᵘ + u + 2 ≥ 0` for
`u ≥ 0`.

**Lean implementation helper.** -/
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

/-- Recovered prerequisite from,
`k(u) ≤ 0` for `u ≤ 0`.

**Lean implementation helper.** -/
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

/-- The quadratic lower bound
`1 + u + u²/2 ≤ eᵘ` for `u ≥ 0`.

**Lean implementation helper.** -/
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

/-- The quadratic upper bound
`eᵘ ≤ 1 + u + u²/2` for `u ≤ 0`.

**Lean implementation helper.** -/
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

/-- The scalar profile of the Bernstein mgf bound; the ported source's
`f(x) = (e^{θx} − θx − 1)/x²` equals `θ²·bernsteinH(θx)`, where
`H(u) = (eᵘ − u − 1)/u²` with the removable value `H(0) = 1/2`.

**Lean implementation helper.** -/
noncomputable def bernsteinH (u : ℝ) : ℝ :=
  if u = 0 then 1 / 2 else (Real.exp u - u - 1) / u ^ 2

/-- The removable value of `bernsteinH` at zero.

**Lean implementation helper.** -/
lemma bernsteinH_zero : bernsteinH 0 = 1 / 2 := if_pos rfl

/-- The quotient formula for nonzero arguments.

**Lean implementation helper.** -/
lemma bernsteinH_of_ne {u : ℝ} (hu : u ≠ 0) :
    bernsteinH u = (Real.exp u - u - 1) / u ^ 2 := if_neg hu

/-- The defining identity
`H(u)·u² = eᵘ − u − 1` (valid for every `u`, including `u = 0`).

**Lean implementation helper.** -/
lemma bernsteinH_mul_sq (u : ℝ) :
    bernsteinH u * u ^ 2 = Real.exp u - u - 1 := by
  by_cases hu : u = 0
  · subst hu
    rw [bernsteinH_zero]
    norm_num
  · rw [bernsteinH_of_ne hu, div_mul_cancel₀]
    exact pow_ne_zero 2 hu

/-- `H ≤ 1/2` on the nonpositive axis.

**Lean implementation helper.** -/
lemma bernsteinH_le_half {u : ℝ} (hu : u ≤ 0) : bernsteinH u ≤ 1 / 2 := by
  by_cases h0 : u = 0
  · subst h0
    rw [bernsteinH_zero]
  · have hlt : u < 0 := lt_of_le_of_ne hu h0
    rw [bernsteinH_of_ne h0, div_le_iff₀ (by positivity)]
    have h1 := exp_quadratic_upper hu
    nlinarith

/-- `1/2 ≤ H` on the nonnegative axis.

**Lean implementation helper.** -/
lemma half_le_bernsteinH {u : ℝ} (hu : 0 ≤ u) : 1 / 2 ≤ bernsteinH u := by
  by_cases h0 : u = 0
  · subst h0
    rw [bernsteinH_zero]
  · have hlt : 0 < u := lt_of_le_of_ne hu (Ne.symm h0)
    rw [bernsteinH_of_ne h0, le_div_iff₀ (by positivity)]
    have h1 := exp_quadratic_lower hu
    nlinarith

/-- Derivative of the quotient
`q(x) = (eˣ − x − 1)/x²` away from `0`.

**Lean implementation helper.** -/
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

/-- Recovered prerequisite from;
the scalar profile `H` is monotone on `ℝ`, reduced to the sign of
`H′(u) = k(u)/u³`.

**Lean implementation helper.** -/
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

/-- Recovered prerequisite from;
`H(u) ≤ (1/2)/(1 − u/3)` for `0 ≤ u < 3`, via the auxiliary function
`ψ(v) = (1 − v/3)(eᵛ − v − 1) − v²/2`.

**Lean implementation helper.** -/
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

/-- For `θ > 0`, `a ≤ L`, `0 ≤ L`, and `θL < 3`,

`e^{θa} ≤ 1 + θa + (θ²/2)/(1 − θL/3) · a²`.

This pointwise scalar estimate combines monotonicity of the Bernstein profile
with its Taylor bound; the Transfer Rule turns it into the matrix mgf bound.

**Lean implementation helper.** -/
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
# The Bernstein mgf and cgf bounds

For a random Hermitian matrix `X` with `𝔼X = 0`, `λ_max(X) ≤ L`, and
`0 < θ < 3/L`,

`𝔼 e^{θX} ≼ exp(g(θ)·𝔼X²)` and `log 𝔼 e^{θX} ≼ g(θ)·𝔼X²`,

where `g(θ) = (θ²/2)/(1 − θL/3)`.

* `gBernstein` — the coefficient `g(θ)`;
* `cfc_quadratic` — evaluation of a quadratic polynomial under the standard
  matrix function calculus.  The source proof expands the matrix exponential
  into its affine and quadratic parts and inserts `f(X) ≼ f(L)·I` by
  conjugation; in Lean the same pointwise semidefinite bound
  `e^{θX} ≼ I + θX + g(θ)X²` is obtained in one Transfer-Rule step from the
  combined scalar inequality `exp_le_one_add_bernstein_quadratic`;
* `bernstein_matrix_mgf_le`, `bernstein_matrix_cgf_le` — the resulting matrix
  mgf and cgf bounds.

The θ-range is rendered as `0 < θ` and `θ·L < 3` (equivalent to the source's
`0 < θ < 3/L` for `L > 0`, and meaningful also for `L = 0` where `3/L` is
undefined).  Boundedness of the random matrices is carried as the explicit
hypothesis `‖X ω‖ ≤ R`; the sign
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

/-- `A² = cfc (x ↦ x²) A` for Hermitian `A`.

**Lean implementation helper.** -/
lemma sq_eq_cfc (hA : A.IsHermitian) :
    A * A = cfc (fun x : ℝ => x * x) A := by
  rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A, cfc_id' ℝ A]

/-- A Hermitian square is Hermitian.

**Lean implementation helper.** -/
lemma isHermitian_sq (hA : A.IsHermitian) : (A * A).IsHermitian := by
  have h : (A * A)ᴴ = A * A := by
    rw [Matrix.conjTranspose_mul, hA.eq]
  exact h

/-- Evaluation of a quadratic polynomial under the
standard matrix function calculus:
`cfc (x ↦ a + s·x + γ·x²) A = a•I + s•A + γ•A²`.

**Lean implementation helper.** -/
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

/-- The Bernstein coefficient `g(θ) = (θ²/2)/(1 − θL/3)` used in the matrix
mgf and cgf bounds.

**Lean implementation helper.** -/
noncomputable def gBernstein (θ L : ℝ) : ℝ := (θ ^ 2 / 2) / (1 - θ * L / 3)

/-- Nonnegativity of the Bernstein coefficient.

**Lean implementation helper.** -/
lemma gBernstein_nonneg {θ L : ℝ} (hθL : θ * L < 3) : 0 ≤ gBernstein θ L := by
  rw [gBernstein]
  have h1 : 0 < 1 - θ * L / 3 := by linarith
  positivity

/-- Entrywise integrability from a norm bound.

**Lean implementation helper.** -/
lemma mintegrable_of_norm_bound (hXm : Measurable X)
    (hbd : ∀ ω, ‖X ω‖ ≤ R) : MIntegrable X μ := by
  refine MIntegrable.of_bound hXm R (Filter.Eventually.of_forall fun ω i j => ?_)
  exact (norm_entry_le_l2_opNorm _ _ _).trans (hbd ω)

/-- Measurability of `ω ↦ X(ω)²`.

**Lean implementation helper.** -/
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

/-- Entrywise integrability of `X²` from a norm
bound on `X`.

**Lean implementation helper.** -/
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

/-- `𝔼X = 0` and `λ_max(X) ≤ L` force the uniform upper-bound parameter to
satisfy `0 ≤ L`.

**Lean implementation helper.** -/
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

/-- The expectation of the quadratic image,
`𝔼(I + s•X + γ•X²) = I + s•𝔼X + γ•𝔼X²`.

**Lean implementation helper.** -/
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

/-- If `𝔼X = 0` and
`λ_max(X) ≤ L`, then for `0 < θ < 3/L`

`𝔼 e^{θX} ≼ exp( (θ²/2)/(1 − θL/3) · 𝔼X² )`.

Faithful translation of the source proof
(quadratic expansion + Transfer Rule + expectation monotonicity + `I+A ≼ e^A`);
the standing boundedness hypothesis `‖X ω‖ ≤ R` supplies integrability.

**Lean implementation helper.** -/
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

/-- The cgf bound
`log 𝔼 e^{θX} ≼ (θ²/2)/(1 − θL/3) · 𝔼X²` for `0 < θ < 3/L` follows from the
mgf bound and operator monotonicity of the matrix logarithm.

**Lean implementation helper.** -/
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

end MgfCgfBound

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Bernstein for Hermitian matrices

For independent random Hermitian `d`-dimensional matrices with `𝔼X_k = 0`
and `λ_max(X_k) ≤ L`, write `Y = ΣX_k` and
`v(Y) = ‖𝔼Y²‖ = ‖Σ𝔼X_k²‖`.  The main conclusions are:

* expectation formula `𝔼λ_max(Y) ≤ √(2v(Y)log d) + (1/3)L·log d`
  (`matrix_bernstein_herm_expectation`);
* tail formula `P(λ_max(Y) ≥ t) ≤ d·exp(−t²/2/(v(Y) + Lt/3))` for `t ≥ 0`
  (`matrix_bernstein_herm_tail`);

The corresponding minimum-eigenvalue variants assume `λ_min(X_k) ≥ −L̲`
(`matrix_bernstein_herm_min_expectation`, `matrix_bernstein_herm_min_tail`),
and follow by applying the expectation and tail bounds to `−Y`.

The proofs substitute the Bernstein cgf estimate into the trace-exponential
expectation and tail bounds and optimize over `θ ∈ (0, 3/L)`.

The matrix variance statistic is stated in the summand form
`‖Σ_k 𝔼(X_k²)‖`; its equality with `‖𝔼Y²‖` and `varStat` is established by
the companion variance identities.
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

/-- Substituting the Bernstein cgf bound into the trace exponential gives
`tr exp(Σ_k Ξ_{X_k}(θ)) ≤ d·exp(g(θ)·v)` for `0 < θ < 3/L`, where
`v = ‖Σ_k 𝔼X_k²‖`.

**Lean implementation helper.** -/
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

/-- In dimension `1`, `λ_max` is the real part of the unique diagonal entry,
so `𝔼λ_max(Y) = 0` for a centered sum; this handles the degenerate
`log d = 0` branch.

**Lean implementation helper.** -/
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

/-- Subadditivity of the square root.

**Lean implementation helper.** -/
lemma sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt (add_nonneg ha hb)
  have h4 := Real.sqrt_nonneg a
  have h5 := Real.sqrt_nonneg b
  have h6 := Real.sqrt_nonneg (a + b)
  nlinarith [mul_nonneg h4 h5]

/-- The Hermitian Matrix Bernstein expectation bound:

`𝔼 λ_max(Y) ≤ √(2 v(Y) log d) + (1/3) L log d`

with `v(Y) = ‖Σ_k 𝔼X_k²‖`.  The proof combines the trace-exponential
expectation bound with the Bernstein cgf estimate and optimizes over
`θ ∈ (0, 3/L)`; the standing `0 ≤ L` records the sign convention for the
one-sided eigenvalue bound.

**Author note.** `MatrixConcentration.matrix_bernstein_herm_expectation` in
`Prelude/MatrixConcentration.lean` carries the additional pointwise norm bound
`‖X_k ω‖ ≤ R k` as an explicit integrability regularity hypothesis.

**Lean implementation helper.** -/
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

/-- The Hermitian Matrix Bernstein tail bound:

`P(λ_max(Y) ≥ t) ≤ d · exp( −t²/2 / (v(Y) + Lt/3) )` for `t ≥ 0`.

The proof combines the trace-exponential tail bound with the Bernstein cgf
estimate and chooses `θ = t/(v + Lt/3)`.

**Author note.** `MatrixConcentration.matrix_bernstein_herm_tail` in
`Prelude/MatrixConcentration.lean` carries the additional pointwise norm bound
`‖X_k ω‖ ≤ R k` as an explicit integrability regularity hypothesis.

**Lean implementation helper.** -/
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

/-- Measurability of matrix negation (as a map on
matrices).

**Lean implementation helper.** -/
lemma measurable_matrix_neg_fun :
    Measurable fun M : Matrix n n ℂ => -M := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable fun M : Matrix n n ℂ => -(M i j)
  exact (measurable_entry i j).neg

/-- Under `𝔼X_k = 0` and `λ_min(X_k) ≥ −L̲`,

`𝔼 λ_min(Y) ≥ −√(2 v(Y) log d) − (1/3) L̲ log d`

This follows by applying the Hermitian expectation bound to `−Y`.

**Lean implementation helper.** -/
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
    change ‖-(X k ω)‖ ≤ R k
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
    change -(X k ω) * -(X k ω) = X k ω * X k ω
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

/-- Under the same hypotheses,
`P(λ_min(Y) ≤ −t) ≤ d·exp(−t²/2/(v(Y) + L̲t/3))` for `t ≥ 0`, by applying
the Hermitian tail bound to `−Y`.

**Lean implementation helper.** -/
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
    change ‖-(X k ω)‖ ≤ R k
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
    change -(X k ω) * -(X k ω) = X k ω * X k ω
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
# Matrix Bernstein for rectangular matrices

For independent `d₁ × d₂` random matrices with `𝔼S_k = 0` and
`‖S_k‖ ≤ L`, write `Z = ΣS_k` and
`v(Z) = max{‖Σ𝔼S_kS_k*‖, ‖Σ𝔼S_k*S_k‖}`.  The main conclusions are:

* `𝔼‖Z‖ ≤ √(2v(Z)log(d₁+d₂)) + (1/3)L log(d₁+d₂)`
  (`matrix_bernstein_rect_expectation`);
* `P(‖Z‖ ≥ t) ≤ (d₁+d₂)·exp(−t²/2/(v(Z)+Lt/3))`
  (`matrix_bernstein_rect_tail`);

Both follow from the Hermitian case through Hermitian dilation.  The file also
provides:

* `variance_max_eq_of_hermitian` — for Hermitian summands, the two variance
  terms coincide;
* split subgaussian and subexponential Bernstein estimates
  (`matrix_bernstein_split_subgaussian`, `_subexponential`);
* the uncentered corollary (`matrix_bernstein_uncentered_expectation`,
  `_tail`);
* a.e.-boundedness wrappers (`matrix_bernstein_rect_expectation_ae`,
  `_tail_ae`) via norm truncation.

Statement conventions: `0 ≤ L` is carried explicitly because the statement
fails for the empty family without this sign condition.  For centered sums,
`matrix_bernstein_variance_eq` identifies the displayed variance statistic
with `varStat`.
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

/-- `H(0) = 0`.

**Lean implementation helper.** -/
lemma hermDilation_zero : hermDilation (0 : Matrix m n ℂ) = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [hermDilation, Matrix.fromBlocks]

/-- Hermitian dilation commutes with finite sums because it is real-linear.

**Lean implementation helper.** -/
lemma hermDilation_sum (B : ι → Matrix m n ℂ) :
    hermDilation (∑ k, B k) = ∑ k, hermDilation (B k) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hermDilation_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hermDilation_add, ih]

/-- A finite sum of block-diagonal matrices.

**Lean implementation helper.** -/
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
    change (∑ k, (0 : Matrix m n ℂ) i j) = (0 : Matrix m n ℂ) i j
    simp
  · rw [Matrix.sum_apply]
    change (∑ k, (0 : Matrix n m ℂ) i j) = (0 : Matrix n m ℂ) i j
    simp
  · rw [Matrix.sum_apply]
    show (∑ k, Matrix.fromBlocks (A k) 0 0 (D k) (Sum.inr i) (Sum.inr j)) = _
    rw [show (∑ k, Matrix.fromBlocks (A k) 0 0 (D k) (Sum.inr i) (Sum.inr j)) =
      ∑ k, D k i j from Finset.sum_congr rfl fun k _ => rfl]
    rw [show (Matrix.fromBlocks (∑ k, A k) 0 0 (∑ k, D k) (Sum.inr i)
      (Sum.inr j)) = (∑ k, D k) i j from rfl, Matrix.sum_apply]

/-- The summand second moments of the dilated family assemble into the
block-diagonal matrix of the rectangular second moments, so their norm is the
rectangular matrix variance statistic.

**Lean implementation helper.** -/
lemma dilation_variance_eq
    (_hmeas : ∀ k, Measurable (S k)) (_hbd : ∀ k ω, ‖S k ω‖ ≤ L) :
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

/-- For Hermitian summands, the two rectangular variance terms coincide.

**Lean implementation helper.** -/
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

/-- Matrix Bernstein expectation bound:

`𝔼‖Z‖ ≤ √(2 v(Z) log(d₁+d₂)) + (1/3) L log(d₁+d₂)`

with `v(Z) = max{‖Σ𝔼S_kS_k*‖, ‖Σ𝔼S_k*S_k‖}`.  The proof uses Hermitian
dilation.

**Lean implementation helper.** -/
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
    change ‖hermDilation (S k ω)‖ ≤ L
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

/-- Matrix Bernstein tail bound:

`P(‖Z‖ ≥ t) ≤ (d₁+d₂)·exp(−t²/2 / (v(Z) + Lt/3))` for `t ≥ 0`.

The proof uses Hermitian dilation.

**Lean implementation helper.** -/
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
    change ‖hermDilation (S k ω)‖ ≤ L
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

/-- In the subgaussian regime `t·L ≤ v(Z)`,
`P(‖Z‖ ≥ t) ≤ (d₁+d₂)·e^{−3t²/(8v(Z))}`.

**Lean implementation helper.** -/
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

/-- In the subexponential regime `v(Z) ≤ t·L`,
`P(‖Z‖ ≥ t) ≤ (d₁+d₂)·e^{−3t/(8L)}`.

**Lean implementation helper.** -/
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

/-- Expectation congruence for a.e.-equal random
matrices.

**Lean implementation helper.** -/
lemma expectation_congr_ae {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {Y Z : Ω → Matrix p q ℂ} (h : Y =ᵐ[μ] Z) :
    expectation μ Y = expectation μ Z := by
  ext i j
  rw [expectation_apply, expectation_apply]
  refine integral_congr_ae (h.mono fun ω hω => ?_)
  change Y ω i j = Z ω i j
  rw [hω]

/-- Under `‖S_k − 𝔼S_k‖ ≤ L`, the centered sum satisfies
`𝔼‖Z − 𝔼Z‖ ≤ √(2v(Z)log(d₁+d₂)) + (1/3)L log(d₁+d₂)`, with `v(Z)` computed
from the centered summands.  This is an immediate consequence of the centered
rectangular expectation bound.

**Lean implementation helper.** -/
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
    change (∑ k, (S k ω - expectation μ (S k))) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k)
    rw [Finset.sum_sub_distrib]
  rw [show (fun ω => ‖∑ k, S' k ω‖) =
      fun ω => ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖ from
    funext fun ω => by rw [hsum_eq ω]] at h
  exact h

/-- The centered sum satisfies the tail bound
`P(‖Z − 𝔼Z‖ ≥ t) ≤ (d₁+d₂)·exp(−t²/2/(v(Z)+Lt/3))`.

**Lean implementation helper.** -/
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
    change (∑ k, (S k ω - expectation μ (S k))) =
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

/-- Norm truncation upgrades an almost-everywhere norm bound to a pointwise
one without changing the random matrix almost everywhere.

**Lean implementation helper.** -/
noncomputable def truncateNorm (L : ℝ) (B : Matrix m n ℂ) : Matrix m n ℂ :=
  if ‖B‖ ≤ L then B else 0

/-- Measurability of norm truncation.

**Lean implementation helper.** -/
lemma measurable_truncateNorm :
    Measurable (truncateNorm (m := m) (n := n) L) := by
  have hset : MeasurableSet {B : Matrix m n ℂ | ‖B‖ ≤ L} :=
    continuous_l2_opNorm.measurable measurableSet_Iic
  exact Measurable.ite hset measurable_id measurable_const

/-- The truncated matrix satisfies the pointwise norm bound.

**Lean implementation helper.** -/
lemma truncateNorm_norm_le (hL : 0 ≤ L) (B : Matrix m n ℂ) :
    ‖truncateNorm L B‖ ≤ L := by
  rw [truncateNorm]
  split_ifs with h
  · exact h
  · rw [norm_zero]
    exact hL

/-- Norm truncation extends the rectangular Matrix Bernstein expectation bound from a
pointwise norm hypothesis to an almost-everywhere one.

**Author note.** `MatrixConcentration.matrix_bernstein_rect_expectation_ae` in
`Prelude/MatrixConcentration.lean` weakens the pointwise norm bound used by
`matrix_bernstein_rect_expectation` to an almost-everywhere bound.

**Lean implementation helper.** -/
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
    change truncateNorm L (S k ω) = S k ω
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
    change (∑ k, S' k ω) = ∑ k, S k ω
    exact Finset.sum_congr rfl fun k _ => h k
  -- transfer the left-hand side
  have hlhs : ∫ ω, ‖∑ k, S' k ω‖ ∂μ = ∫ ω, ‖∑ k, S k ω‖ ∂μ := by
    refine integral_congr_ae (hsum_ae.mono fun ω h => ?_)
    have h' : (∑ k, S' k ω) = ∑ k, S k ω := h
    change ‖∑ k, S' k ω‖ = ‖∑ k, S k ω‖
    rw [h']
  rw [hlhs] at h
  -- transfer the variance terms
  have hv1 : ∀ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ) =
      expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    change S' k ω * (S' k ω)ᴴ = S k ω * (S k ω)ᴴ
    rw [h']
  have hv2 : ∀ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω) =
      expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    change (S' k ω)ᴴ * S' k ω = (S k ω)ᴴ * S k ω
    rw [h']
  rw [Finset.sum_congr rfl fun k _ => hv1 k,
    Finset.sum_congr rfl fun k _ => hv2 k] at h
  exact h

/-- Norm truncation extends the rectangular Matrix Bernstein tail bound from a pointwise norm
hypothesis to an almost-everywhere one.

**Author note.** `MatrixConcentration.matrix_bernstein_rect_tail_ae` in
`Prelude/MatrixConcentration.lean` weakens the pointwise norm bound used by
`matrix_bernstein_rect_tail` to an almost-everywhere bound.

**Lean implementation helper.** -/
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
    change truncateNorm L (S k ω) = S k ω
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
    change (∑ k, S' k ω) = ∑ k, S k ω
    exact Finset.sum_congr rfl fun k _ => h k
  have hmeq : μ {ω | t ≤ ‖∑ k, S' k ω‖} = μ {ω | t ≤ ‖∑ k, S k ω‖} := by
    refine MeasureTheory.measure_congr ?_
    refine hsum_ae.mono fun ω hω => ?_
    have h' : (∑ k, S' k ω) = ∑ k, S k ω := hω
    change (t ≤ ‖∑ k, S' k ω‖) = (t ≤ ‖∑ k, S k ω‖)
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
    change S' k ω * (S' k ω)ᴴ = S k ω * (S k ω)ᴴ
    rw [h']
  have hv2 : ∀ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω) =
      expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    change (S' k ω)ᴴ * S' k ω = (S k ω)ᴴ * S k ω
    rw [h']
  rw [Finset.sum_congr rfl fun k _ => hv1 k,
    Finset.sum_congr rfl fun k _ => hv2 k] at h
  exact h

end AeWrappers

end MatrixConcentration
