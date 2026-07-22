import HighDimensionalProbability.Appendix.Infra.GaussianEuclideanLSI
import HighDimensionalProbability.Appendix.Infra.GaussianInverseRadius
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth regularization of radial projection

For `ε > 0`, the map

`x ↦ x / sqrt (‖x‖² + ε²)`

is a smooth replacement for radial projection onto the unit sphere.  Its
derivative converges to the tangential projection divided by the radius.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Smooth radial projection into the open unit ball. -/
def regularizedDirection (ε : ℝ) (x : E) : E :=
  (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ • x

private lemma regularizedRadius_pos (hε : 0 < ε) (x : E) :
    0 < Real.sqrt (‖x‖ ^ 2 + ε ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hε]

/-- Exact Fréchet derivative of the regularized radial projection. -/
lemma hasFDerivAt_regularizedDirection
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    HasFDerivAt (regularizedDirection ε)
      ((Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ •
          ContinuousLinearMap.id ℝ E -
        (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 3 •
          (innerSL ℝ x).smulRight x) x := by
  let q : E → ℝ := fun y => ‖y‖ ^ 2 + ε ^ 2
  let r : E → ℝ := fun y => Real.sqrt (q y)
  let a : E → ℝ := fun y => (r y)⁻¹
  have hq :
      HasFDerivAt q (2 • innerSL ℝ x) x := by
    simpa [q] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)
  have hq0 : q x ≠ 0 := by
    have : 0 < q x := by
      dsimp [q]
      nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hε]
    exact this.ne'
  have hr :
      HasFDerivAt r
        ((1 / (2 * Real.sqrt (q x))) •
          (2 • innerSL ℝ x)) x := by
    simpa [r] using hq.sqrt hq0
  have hr0 : r x ≠ 0 := by
    dsimp [r]
    exact (regularizedRadius_pos hε x).ne'
  have ha := (hasFDerivAt_inv' hr0).comp x hr
  have hsmul := ha.smul (hasFDerivAt_id x)
  convert hsmul using 1
  · ext y
    simp [regularizedDirection, a, r, q]
  · ext v
    simp [a, r, q, sub_eq_add_neg]
    have hsqrt0 :
        Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ≠ 0 :=
      (regularizedRadius_pos hε x).ne'
    field_simp
    ring
    rw [smul_smul]

/-- The regularized radial projection is differentiable for positive
regularization parameter. -/
lemma differentiable_regularizedDirection
    {ε : ℝ} (hε : 0 < ε) :
    Differentiable ℝ (regularizedDirection (E := E) ε) :=
  fun x => (hasFDerivAt_regularizedDirection hε x).differentiableAt

/-- The Fréchet derivative of the regularized radial projection. -/
lemma fderiv_regularizedDirection
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    fderiv ℝ (regularizedDirection ε) x =
      (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ •
          ContinuousLinearMap.id ℝ E -
        (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 3 •
          (innerSL ℝ x).smulRight x :=
  (hasFDerivAt_regularizedDirection hε x).fderiv

/-- Pointwise action of the derivative. -/
lemma fderiv_regularizedDirection_apply
    {ε : ℝ} (hε : 0 < ε) (x v : E) :
    fderiv ℝ (regularizedDirection ε) x v =
      (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ • v -
        ((Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 3 *
          inner ℝ x v) • x := by
  rw [fderiv_regularizedDirection hε x]
  simp [smul_smul]

/-- Squared-norm expansion for the derivative action.  This form avoids
absolute values and is convenient for sharp energy estimates. -/
lemma norm_fderiv_regularizedDirection_apply_sq
    {ε : ℝ} (hε : 0 < ε) (x v : E) :
    ‖fderiv ℝ (regularizedDirection ε) x v‖ ^ 2 =
      (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 2 * ‖v‖ ^ 2 -
        2 * (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 4 *
          (inner ℝ x v) ^ 2 +
        (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 6 *
          (inner ℝ x v) ^ 2 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [fderiv_regularizedDirection_apply hε x v]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm v x]
  ring

/-- Sharp pointwise derivative bound.  The derivative is no larger than
inverse regularized radius, with no loss in the constant. -/
lemma norm_fderiv_regularizedDirection_apply_le
    {ε : ℝ} (hε : 0 < ε) (x v : E) :
    ‖fderiv ℝ (regularizedDirection ε) x v‖ ≤
      (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ * ‖v‖ := by
  let r : ℝ := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)
  have hr : 0 < r := regularizedRadius_pos hε x
  have hrsq : r ^ 2 = ‖x‖ ^ 2 + ε ^ 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by positivity)
  have hratio : r⁻¹ ^ 2 * ‖x‖ ^ 2 ≤ 1 := by
    have heq : r⁻¹ ^ 2 * ‖x‖ ^ 2 = ‖x‖ ^ 2 / r ^ 2 := by
      field_simp [hr.ne']
    rw [heq]
    apply (div_le_one (sq_pos_of_pos hr)).2
    rw [hrsq]
    exact le_add_of_nonneg_right (sq_nonneg ε)
  have hcoeff : r⁻¹ ^ 2 * ‖x‖ ^ 2 - 2 ≤ 0 := by
    linarith
  have hcorrection :
      r⁻¹ ^ 4 * (inner ℝ x v) ^ 2 *
          (r⁻¹ ^ 2 * ‖x‖ ^ 2 - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) 4)
        (sq_nonneg (inner ℝ x v)))
      hcoeff
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg v))).mp
  calc
    ‖fderiv ℝ (regularizedDirection ε) x v‖ ^ 2 =
        r⁻¹ ^ 2 * ‖v‖ ^ 2 -
          2 * r⁻¹ ^ 4 * (inner ℝ x v) ^ 2 +
          r⁻¹ ^ 6 * (inner ℝ x v) ^ 2 * ‖x‖ ^ 2 := by
            simpa [r] using
              norm_fderiv_regularizedDirection_apply_sq hε x v
    _ = r⁻¹ ^ 2 * ‖v‖ ^ 2 +
        r⁻¹ ^ 4 * (inner ℝ x v) ^ 2 *
          (r⁻¹ ^ 2 * ‖x‖ ^ 2 - 2) := by ring
    _ ≤ r⁻¹ ^ 2 * ‖v‖ ^ 2 := by linarith
    _ = (r⁻¹ * ‖v‖) ^ 2 := by ring

/-- Sharp operator-norm version of
`norm_fderiv_regularizedDirection_apply_le`. -/
lemma norm_fderiv_regularizedDirection_le
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (regularizedDirection ε) x‖ ≤
      (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact norm_fderiv_regularizedDirection_apply_le hε x

/-- Away from the origin, the derivative is dominated by inverse radius,
uniformly in the positive regularization parameter. -/
lemma norm_fderiv_regularizedDirection_le_inv_norm
    {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (regularizedDirection ε) x‖ ≤ ‖x‖⁻¹ := by
  refine (norm_fderiv_regularizedDirection_le hε x).trans ?_
  apply (inv_le_inv₀ (regularizedRadius_pos hε x)
    (norm_pos_iff.mpr hx)).2
  simpa [Real.sqrt_sq (norm_nonneg x)] using
    Real.sqrt_le_sqrt
      (show ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ε ^ 2 from
        le_add_of_nonneg_right (sq_nonneg ε))

/-- The derivative field of the regularized radial projection is continuous
for every positive regularization parameter. -/
lemma continuous_fderiv_regularizedDirection
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : E =>
      fderiv ℝ (regularizedDirection ε) x) := by
  simp_rw [fderiv_regularizedDirection hε]
  have hden :
      Continuous (fun x : E =>
        Real.sqrt (‖x‖ ^ 2 + ε ^ 2)) := by
    fun_prop
  have hinv :
      Continuous (fun x : E =>
        (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹) :=
    hden.inv₀ fun x => (regularizedRadius_pos hε x).ne'
  have hrank :
      Continuous (fun x : E =>
        (innerSL ℝ x).smulRight x) := by
    fun_prop
  exact (hinv.smul continuous_const).sub
    ((hinv.pow 3).smul hrank)

/-- Derivative of the ordinary radial projection away from the origin:
inverse radius times orthogonal projection onto the tangent hyperplane. -/
def radialDirectionDerivative (x : E) : E →L[ℝ] E :=
  ‖x‖⁻¹ • ContinuousLinearMap.id ℝ E -
    ‖x‖⁻¹ ^ 3 • (innerSL ℝ x).smulRight x

/-- The inverse regularized radius converges to inverse radius away from the
origin. -/
lemma tendsto_regularizedRadius_inv
    (x : E) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹)
      (𝓝 0) (𝓝 ‖x‖⁻¹) := by
  have hsqrt :
      ContinuousAt
        (fun ε : ℝ => Real.sqrt (‖x‖ ^ 2 + ε ^ 2)) 0 :=
    Real.continuous_sqrt.continuousAt.comp'
      (continuousAt_const.add (continuousAt_id.pow 2))
  have hsqrt0 :
      Real.sqrt (‖x‖ ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
    simpa [Real.sqrt_sq (norm_nonneg x)] using
      (norm_ne_zero_iff.mpr hx)
  simpa [Real.sqrt_sq (norm_nonneg x)] using
    (hsqrt.inv₀ hsqrt0).tendsto

/-- The explicit regularized derivative converges in operator norm to the
derivative of radial projection at every nonzero point. -/
lemma tendsto_regularizedDirectionDerivative
    (x : E) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ •
            ContinuousLinearMap.id ℝ E -
          (Real.sqrt (‖x‖ ^ 2 + ε ^ 2))⁻¹ ^ 3 •
            (innerSL ℝ x).smulRight x)
      (𝓝 0) (𝓝 (radialDirectionDerivative x)) := by
  have hinv := tendsto_regularizedRadius_inv x hx
  simpa [radialDirectionDerivative] using
    (hinv.smul_const (ContinuousLinearMap.id ℝ E)).sub
      ((hinv.pow 3).smul_const ((innerSL ℝ x).smulRight x))

/-- Along positive regularization parameters, the actual Fréchet derivatives
converge in operator norm to the derivative of radial projection. -/
lemma tendsto_fderiv_regularizedDirection
    (x : E) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => fderiv ℝ (regularizedDirection ε) x)
      (𝓝[>] 0) (𝓝 (radialDirectionDerivative x)) := by
  refine ((tendsto_regularizedDirectionDerivative x hx).mono_left
    inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (fderiv_regularizedDirection hε x).symm

/-- The regularized direction converges pointwise to radial projection away
from the origin. -/
lemma tendsto_regularizedDirection
    (x : E) (hx : x ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => regularizedDirection ε x)
      (𝓝 0) (𝓝 (‖x‖⁻¹ • x)) := by
  simpa [regularizedDirection] using
    (tendsto_regularizedRadius_inv x hx).smul_const x

end

end HDP.Appendix
