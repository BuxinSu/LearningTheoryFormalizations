/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Prelude.RandomMatrix
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import HighDimensionalProbability.Chapter8_Chaining
import HighDimensionalProbability.Chapter4_RandomMatrices
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.MeasureTheory.Function.LpOrder
import HighDimensionalProbability.Chapter7_RandomProcesses
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Option
import HighDimensionalProbability.Prelude.GaussianMatrix
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Caratheodory

/-!
# Chapter 9 — Deviations of Random Matrices on Sets

## Contents

- §9.1 Matrix deviations
  - Equations (9.1)–(9.7), Theorem 9.1.1, and Theorem 9.1.2
- §9.2 Random projections and covariance
  - Proposition 9.2.1 and Theorem 9.2.2: projection size and covariance estimation
  - §9.2.3: covariance-ellipsoid radius and Gaussian-complexity bounds
  - Lemma 9.2.4: additive Johnson–Lindenstrauss
- §9.3 Random sections
  - Theorem 9.3.1: the M* bound
  - Theorem 9.3.4: escape through a mesh
- §9.4 High-dimensional linear models
  - Theorem 9.4.4 and Corollaries 9.4.8 and 9.4.11
  - Constrained, sparse, low-rank, noisy, and penalized recovery
- §9.5 Exact sparse recovery and restricted isometries
  - Theorem 9.5.1, Definition 9.5.5, and Theorems 9.5.6–9.5.7
- §9.6 General-norm matrix deviations
  - Definition 9.6.1 and Theorems 9.6.3–9.6.4
- §9.7 Two-sided Chevet and Dvoretzky–Milman
  - Theorems 9.7.1–9.7.2 and the effective-dimension consequences

The detailed entries below identify the chapter's key source-facing definitions and
results by the numbering printed in the second-edition book PDF.
-/

/-! ## Material formerly in `01_MatrixDeviation.lean` -/

section Source_01_MatrixDeviation

/-!
# Book Chapter 9, §9.1: matrix deviations

This file fixes the concrete finite random-matrix process used throughout the
chapter.  The Euclidean norm is kept definitionally compatible with the
coordinate-square expression in Theorem 3.1.1.  Arbitrary-set statements later
use the finite-subfamily convention of Remark 7.2.1; no unmeasurable raw
supremum is silently integrated.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The concrete matrix process -/

/-- The action of a finite real matrix on a Euclidean vector.

**Lean implementation helper.** -/
def matrixAction {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 ((A ω).mulVec x.ofLp)

/-- Each coordinate of the matrix action is the inner product of the corresponding random row with the input vector.

**Lean implementation helper.** -/
@[simp]
theorem matrixAction_apply {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) (i : Fin m) :
    matrixAction A x ω i =
      inner ℝ (HDP.randomMatrixRow A i ω) x := by
  simp [matrixAction, HDP.inner_randomMatrixRow, Matrix.mulVec, dotProduct]

/-- Matrix norm-deviation process `Z_x=‖Ax‖-sqrt(m)‖x‖`. The process in display (9.2): `Z_x = ‖Ax‖₂ - √m ‖x‖₂`.

**Book Equation (9.2).** -/
def matrixDeviationProcess {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  ‖matrixAction A x ω‖ - Real.sqrt m * ‖x‖

/-- The matrix action vanishes at zero.

**Lean implementation helper.** -/
@[simp]
theorem matrixAction_zero {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) (ω : Ω) :
    matrixAction A 0 ω = 0 := by
  ext i
  simp

/-- The matrix deviation process vanishes at zero.

**Lean implementation helper.** -/
@[simp]
theorem matrixDeviationProcess_zero {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) :
    matrixDeviationProcess A 0 = 0 := by
  funext ω
  simp [matrixDeviationProcess]

/-- The matrix action commutes with scalar multiplication.

**Lean implementation helper.** -/
theorem matrixAction_smul {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    matrixAction A (c • x) ω = c • matrixAction A x ω := by
  ext i
  simp [matrixAction_apply, inner_smul_right]

/-- The matrix action commutes with subtraction.

**Lean implementation helper.** -/
theorem matrixAction_sub {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x y : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    matrixAction A (x - y) ω = matrixAction A x ω - matrixAction A y ω := by
  ext i
  simp [matrixAction_apply, inner_sub_right]

/-- The matrix-deviation process is homogeneous under multiplication by a nonnegative scalar.

**Lean implementation helper.** -/
theorem matrixDeviationProcess_smul_of_nonneg {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) {c : ℝ} (hc : 0 ≤ c)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixDeviationProcess A (c • x) =
      fun ω => c * matrixDeviationProcess A x ω := by
  funext ω
  simp [matrixDeviationProcess, matrixAction_smul, norm_smul,
    abs_of_nonneg hc]
  ring

/-- The norm of the matrix action is the square root of the sum of squared row inner products.

**Lean implementation helper.** -/
theorem norm_matrixAction_eq_sqrt_sum {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    ‖matrixAction A x ω‖ =
      Real.sqrt (∑ i : Fin m,
        inner ℝ (HDP.randomMatrixRow A i ω) x ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixAction_apply]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The matrix action is almost everywhere measurable.

**Lean implementation helper.** -/
theorem aemeasurable_matrixAction {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hA : A.AEMeasurableRows μ)
    (x : EuclideanSpace ℝ (Fin n)) :
    AEMeasurable (matrixAction A x) μ := by
  have hraw : AEMeasurable
      (fun ω => (A ω).mulVec x.ofLp) μ := by
    apply aemeasurable_pi_lambda
    intro i
    simpa [Matrix.mulVec, dotProduct, HDP.inner_randomMatrixRow]
      using hA.aemeasurable_marginal i x
  change AEMeasurable
    (fun ω => WithLp.toLp 2 ((A ω).mulVec x.ofLp)) μ
  exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp_aemeasurable hraw

/-- The matrix deviation process is almost everywhere measurable.

**Lean implementation helper.** -/
theorem aemeasurable_matrixDeviationProcess {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hA : A.AEMeasurableRows μ)
    (x : EuclideanSpace ℝ (Fin n)) :
    AEMeasurable (matrixDeviationProcess A x) μ := by
  exact (aemeasurable_matrixAction A hA x).norm.sub aemeasurable_const

/-! ## Exercise 9.1: the radial reverse-triangle estimate -/

/-- Scalar square-root form of the geometric estimate used in Exercise 9.1.

**Book Exercise 9.1.** -/
private lemma add_le_sqrt_two_mul_of_sq_add_sq_le
    {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (h : a ^ 2 + b ^ 2 ≤ d ^ 2) :
    a + b ≤ Real.sqrt 2 * d := by
  have hab0 : 0 ≤ a + b := add_nonneg ha hb
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hrhs0 : 0 ≤ Real.sqrt 2 * d := mul_nonneg hs2 hd
  apply (sq_le_sq₀ hab0 hrhs0).mp
  calc
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    _ ≤ 2 * d ^ 2 := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (Real.sqrt 2 * d) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Radial reduction bounds general increments by unit-sphere increments. If `x` is on the unit sphere and `y` is outside the unit ball, radial
projection of `y` to the sphere gives the approximate reverse triangle
inequality used in Step 4 of Theorem 9.1.2. The source's undefined `y/‖y‖`
at `y=0` is ruled out by `1 ≤ ‖y‖`.

**Book Equation (9.10).** -/
theorem exercise_9_1_reverse_triangle {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : 1 ≤ ‖y‖) :
    let ybar := ‖y‖⁻¹ • y
    ‖x - y‖ ≤ ‖x - ybar‖ + ‖ybar - y‖ ∧
      ‖x - ybar‖ + ‖ybar - y‖ ≤ Real.sqrt 2 * ‖x - y‖ := by
  dsimp only
  let r : ℝ := ‖y‖
  let ybar : EuclideanSpace ℝ (Fin n) := r⁻¹ • y
  have hr : 1 ≤ r := hy
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hybar : ‖ybar‖ = 1 := by
    simp [ybar, r, norm_smul, hrpos.ne']
  have hfirst : ‖x - y‖ ≤ ‖x - ybar‖ + ‖ybar - y‖ := by
    have h := norm_add_le (x - ybar) (ybar - y)
    simpa only [sub_add_sub_cancel] using h
  have hradial : ‖ybar - y‖ = r - 1 := by
    have hy_eq : y = r • ybar := by
      simp [ybar, r, hrpos.ne']
    rw [hy_eq]
    have hdiff : ybar - r • ybar = (1 - r) • ybar := by
      module
    rw [hdiff, norm_smul, hybar, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hsq : ‖x - ybar‖ ^ 2 + ‖ybar - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have hxybar : ‖x - ybar‖ ^ 2 =
        2 - 2 * inner ℝ x ybar := by
      rw [norm_sub_sq_real, hx, hybar]
      ring
    have hy_eq : y = r • ybar := by
      simp [ybar, r, hrpos.ne']
    have hxy : ‖x - y‖ ^ 2 =
        (r - 1) ^ 2 + 2 * r * (1 - inner ℝ x ybar) := by
      rw [hy_eq, norm_sub_sq_real, hx, norm_smul, hybar,
        inner_smul_right, Real.norm_eq_abs, abs_of_nonneg hrpos.le]
      ring
    have hinner : inner ℝ x ybar ≤ 1 := by
      calc
        inner ℝ x ybar ≤ ‖x‖ * ‖ybar‖ := real_inner_le_norm _ _
        _ = 1 := by rw [hx, hybar, one_mul]
    rw [hxybar, hradial, hxy]
    nlinarith
  refine ⟨hfirst, ?_⟩
  exact add_le_sqrt_two_mul_of_sq_add_sq_le
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hsq

/-! ## Finite-subfamily deviation envelopes -/

/-- Pointwise absolute supremum of the matrix-deviation process on a finite
nonempty set.

**Lean implementation helper.** -/
def finiteMatrixDeviation {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (HDP.Chapter8.finiteEuclideanProcess T (matrixDeviationProcess A)) ω

/-- The finite matrix deviation is nonnegative.

**Lean implementation helper.** -/
theorem finiteMatrixDeviation_nonneg {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) :
    0 ≤ finiteMatrixDeviation A T ω := by
  unfold finiteMatrixDeviation HDP.Chapter8.finiteProcessAbsoluteSup
  let x0 : ↥T := Classical.choice inferInstance
  calc
    0 ≤ |HDP.Chapter8.finiteEuclideanProcess T
        (matrixDeviationProcess A) x0 ω| := abs_nonneg _
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun x : ↥T =>
          |HDP.Chapter8.finiteEuclideanProcess T
            (matrixDeviationProcess A) x ω|) :=
      Finset.le_sup'
        (fun x : ↥T =>
          |HDP.Chapter8.finiteEuclideanProcess T
            (matrixDeviationProcess A) x ω|)
        (Finset.mem_univ x0)

end

end HDP.Chapter9

end Source_01_MatrixDeviation

/-! ## Material formerly in `02_SubGaussianIncrements.lean` -/

section Source_02_SubGaussianIncrements

/-!
# Book Chapter 9, §9.1: subgaussian increments

This is the four-step proof of Theorem 9.1.2.  The fixed-direction input is
Theorem 3.1.1, the squared-process input is Bernstein's inequality, and the
last step is the radial estimate proved as promoted Exercise 9.1.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The explicit fixed-direction constant inherited from Theorem 3.1.1.

**Lean implementation helper.** -/
def matrixFixedDirectionConstant : ℝ :=
  HDP.Chapter3.normConcentrationConstant

/-- The matrix fixed direction constant is strictly positive.

**Lean implementation helper.** -/
theorem matrixFixedDirectionConstant_pos :
    0 < matrixFixedDirectionConstant :=
  HDP.Chapter3.normConcentrationConstant_pos

/-- One explicit scale which simultaneously absorbs the squared-increment
Bernstein exponent and the two fixed-direction exceptional events.

**Lean implementation helper.** -/
def matrixUnitIncrementScale (K : ℝ) : ℝ :=
  (Real.sqrt 128 + 2 * matrixFixedDirectionConstant) * K ^ 2

/-- The matrix unit increment scale is strictly positive.

**Lean implementation helper.** -/
theorem matrixUnitIncrementScale_pos {K : ℝ} (hK : 0 < K) :
    0 < matrixUnitIncrementScale K := by
  unfold matrixUnitIncrementScale
  exact mul_pos
    (add_pos (Real.sqrt_pos.2 (by norm_num))
      (mul_pos (by norm_num) matrixFixedDirectionConstant_pos))
    (sq_pos_of_pos hK)

/-- Increasing a positive Gaussian-tail scale weakens the bound.

**Lean implementation helper.** -/
private lemma gaussianTail_mono_scale {t a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Real.exp (-t ^ 2 / a ^ 2) ≤ Real.exp (-t ^ 2 / b ^ 2) := by
  apply Real.exp_le_exp.mpr
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb : 0 < b := ha.trans_le hab
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hab2 : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha.le hb.le).2 hab
  have hdiv : t ^ 2 / b ^ 2 ≤ t ^ 2 / a ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg t) ha2 hab2
  simpa only [neg_div] using neg_le_neg hdiv

/-- A six-prefactor Gaussian tail can be put into the canonical Chapter 2
two-prefactor form after multiplying the scale by four.

**Lean implementation helper.** -/
private theorem psi2Norm_le_of_six_tail [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) {B : ℝ} (hB : 0 < B)
    (h : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤
        ENNReal.ofReal (6 * Real.exp (-t ^ 2 / B ^ 2))) :
    HDP.SubGaussian X μ ∧
      HDP.psi2Norm X μ ≤ Real.sqrt 5 * (4 * B) := by
  apply HDP.psi2Norm_le_of_tail_bound hXm (show 0 < 4 * B by positivity)
  intro t ht
  by_cases htSmall : t < 2 * B
  · calc
      μ {ω | t ≤ |X ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal
          (2 * Real.exp (-t ^ 2 / (4 * B) ^ 2)) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
        apply ENNReal.ofReal_le_ofReal
        have hden : 0 < (4 * B) ^ 2 := sq_pos_of_pos (by positivity)
        have hratio : t ^ 2 / (4 * B) ^ 2 < 1 / 4 := by
          rw [div_lt_iff₀ hden]
          nlinarith [sq_nonneg t, sq_nonneg B]
        have hexp := Real.add_one_le_exp (-t ^ 2 / (4 * B) ^ 2)
        have hbase : (3 / 4 : ℝ) <
            Real.exp (-t ^ 2 / (4 * B) ^ 2) := by
          calc
            (3 / 4 : ℝ) < 1 - t ^ 2 / (4 * B) ^ 2 := by linarith
            _ ≤ Real.exp (-t ^ 2 / (4 * B) ^ 2) := by
              calc
                1 - t ^ 2 / (4 * B) ^ 2 =
                    -t ^ 2 / (4 * B) ^ 2 + 1 := by ring
                _ ≤ Real.exp (-t ^ 2 / (4 * B) ^ 2) := hexp
        nlinarith
  · have htLarge : 2 * B ≤ t := le_of_not_gt htSmall
    calc
      μ {ω | t ≤ |X ω|} ≤
          ENNReal.ofReal (6 * Real.exp (-t ^ 2 / B ^ 2)) := h t ht
      _ ≤ ENNReal.ofReal
          (2 * Real.exp (-t ^ 2 / (4 * B) ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        let q : ℝ := t ^ 2 / B ^ 2
        have hq : 4 ≤ q := by
          dsimp [q]
          rw [le_div_iff₀ (sq_pos_of_pos hB)]
          nlinarith [sq_nonneg (t - 2 * B)]
        have hq0 : 0 ≤ q := le_trans (by norm_num) hq
        have hthree : (3 : ℝ) ≤ Real.exp (15 * q / 16) := by
          calc
            (3 : ℝ) ≤ 1 + 15 * q / 16 := by nlinarith
            _ ≤ Real.exp (15 * q / 16) := by
              simpa [add_comm] using Real.add_one_le_exp (15 * q / 16)
        calc
          6 * Real.exp (-t ^ 2 / B ^ 2) =
              2 * (3 * Real.exp (-q)) := by
            dsimp [q]
            ring_nf
          _ ≤ 2 * (Real.exp (15 * q / 16) * Real.exp (-q)) := by
            gcongr
          _ = 2 * Real.exp (-q / 16) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
          _ = 2 * Real.exp (-t ^ 2 / (4 * B) ^ 2) := by
            congr 2
            dsimp [q]
            field_simp [hB.ne']
            ring

/-- A fixed vector is approximately norm-preserved by an isotropic subgaussian matrix. Step 1 of the proof of Theorem 9.1.2: concentration in one unit
direction.

**Book Equation (9.1).** -/
theorem matrixDeviation_unit [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    HDP.SubGaussian (matrixDeviationProcess A x) μ ∧
      HDP.psi2Norm (matrixDeviationProcess A x) μ ≤
        matrixFixedDirectionConstant * K ^ 2 := by
  let X : Fin m → Ω → ℝ :=
    fun i ω => inner ℝ (HDP.randomMatrixRow A i ω) x
  have hXm : ∀ i, AEMeasurable (X i) μ := fun i =>
    hrowsm.aemeasurable_marginal i x
  have hX : ∀ i, HDP.SubGaussian (X i) μ := fun i =>
    hsub.marginal i x
  have hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1 := by
    intro i
    simpa [X, hx] using
      HDP.Chapter4.isotropic_row_marginal_secondMoment
        A hrowsm hsub hiso i x
  have hXindep : iIndepFun X μ :=
    hindep.comp (fun _ z => inner ℝ z x) (fun _ => by fun_prop)
  have hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K := by
    intro i
    exact (HDP.psi2Norm_marginal_le_vector (hfinite i) hx).trans (hpsi i)
  have h := HDP.Chapter3.concentration_norm hm hXm hX hsecond hXindep hK hKb
  have hfun : (fun ω => Real.sqrt (∑ i : Fin m, X i ω ^ 2) - Real.sqrt m) =
      matrixDeviationProcess A x := by
    funext ω
    rw [matrixDeviationProcess, hx, mul_one,
      norm_matrixAction_eq_sqrt_sum]
  simpa [matrixFixedDirectionConstant, hfun] using h

/-- Fixed-direction tail with the explicit common scale, including the case
where the attained ψ₂ norm itself vanishes.

**Lean implementation helper.** -/
private theorem matrixDeviation_unit_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |matrixDeviationProcess A x ω|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 / (matrixFixedDirectionConstant * K ^ 2) ^ 2)) := by
  have hfixed := matrixDeviation_unit hm A hrowsm hsub hiso hindep
    hfinite hK hpsi x hx
  have hscale : 0 < matrixFixedDirectionConstant * K ^ 2 := by
    exact mul_pos matrixFixedDirectionConstant_pos (sq_pos_of_pos hK)
  have hmgf := HDP.psi2MGF_le_two_of_ge
    (aemeasurable_matrixDeviationProcess A hrowsm x) hfixed.1 hfixed.2 hscale
  exact HDP.subgaussian_iii_to_i
    (aemeasurable_matrixDeviationProcess A hrowsm x) hscale hmgf ht

/-- Normalized squared-norm difference is a sum of independent products. The bilinear summands in display (9.7).

**Book Equation (9.7).** -/
def squaredIncrementSummand {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (u v : EuclideanSpace ℝ (Fin n)) (i : Fin m) (ω : Ω) : ℝ :=
  inner ℝ (HDP.randomMatrixRow A i ω) u *
    inner ℝ (HDP.randomMatrixRow A i ω) v

/-- Difference of squared matrix norms, divided by `‖x-y‖`.

**Lean implementation helper.** -/
def squaredMatrixIncrement {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x y : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  (‖matrixAction A x ω‖ ^ 2 - ‖matrixAction A y ω‖ ^ 2) / ‖x - y‖

/-- Normalized squared-norm difference is a sum of independent products. Algebraic identity (9.7).

**Book Equation (9.7).** -/
theorem squaredMatrixIncrement_eq_sum {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y) (ω : Ω) :
    squaredMatrixIncrement A x y ω =
      ∑ i : Fin m, squaredIncrementSummand A (x + y)
        (‖x - y‖⁻¹ • (x - y)) i ω := by
  have hd : ‖x - y‖ ≠ 0 := by
    simpa [norm_eq_zero, sub_eq_zero] using hxy
  rw [squaredMatrixIncrement, div_eq_iff hd]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [matrixAction_apply, squaredIncrementSummand,
    inner_add_right, inner_smul_right, inner_sub_right]
  field_simp [hd]
  ring

/-- Factorization of the absolute squared increment.

**Lean implementation helper.** -/
private theorem abs_squaredMatrixIncrement {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y) (ω : Ω) :
    |squaredMatrixIncrement A x y ω| =
      |‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| *
        (‖matrixAction A x ω‖ + ‖matrixAction A y ω‖) /
          ‖x - y‖ := by
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [squaredMatrixIncrement, abs_div, abs_of_pos hd]
  rw [show ‖matrixAction A x ω‖ ^ 2 - ‖matrixAction A y ω‖ ^ 2 =
      (‖matrixAction A x ω‖ - ‖matrixAction A y ω‖) *
        (‖matrixAction A x ω‖ + ‖matrixAction A y ω‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- Each summand in (9.7) has the source's `2K²` ψ₁ bound.

**Book Equation (9.7).** -/
private theorem squaredIncrementSummand_control [IsProbabilityMeasure μ]
    {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (i : Fin m) :
    let u := x + y
    let v := ‖x - y‖⁻¹ • (x - y)
    HDP.SubExponential (squaredIncrementSummand A u v i) μ ∧
      HDP.psi1Norm (squaredIncrementSummand A u v i) μ ≤ 2 * K ^ 2 := by
  dsimp only
  let u := x + y
  let v := ‖x - y‖⁻¹ • (x - y)
  have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hdpos.ne']
  have hu : ‖u‖ ≤ 2 := by
    calc
      ‖u‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ = 2 := by rw [hx, hy]; norm_num
  let Xu : Ω → ℝ := fun ω => inner ℝ (HDP.randomMatrixRow A i ω) u
  let Xv : Ω → ℝ := fun ω => inner ℝ (HDP.randomMatrixRow A i ω) v
  have hXum : AEMeasurable Xu μ := hrowsm.aemeasurable_marginal i u
  have hXvm : AEMeasurable Xv μ := hrowsm.aemeasurable_marginal i v
  have hXu : HDP.SubGaussian Xu μ := hsub.marginal i u
  have hXv : HDP.SubGaussian Xv μ := hsub.marginal i v
  have hvec0 : 0 ≤ HDP.psi2NormVector (HDP.randomMatrixRow A i) μ := by
    calc
      0 ≤ HDP.psi2Norm
          (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) x) μ :=
        HDP.psi2Norm_nonneg _ μ
      _ ≤ HDP.psi2NormVector (HDP.randomMatrixRow A i) μ :=
        HDP.psi2Norm_marginal_le_vector (hfinite i) hx
  have hXuNorm : HDP.psi2Norm Xu μ ≤ 2 * K := by
    calc
      HDP.psi2Norm Xu μ ≤ ‖u‖ * HDP.psi2NormVector (HDP.randomMatrixRow A i) μ :=
        HDP.Chapter3.psi2Norm_marginal_le_norm_mul_vector (hfinite i) u
      _ ≤ 2 * K := by
        exact mul_le_mul hu (hpsi i) hvec0 (by norm_num)
  have hXvNorm : HDP.psi2Norm Xv μ ≤ K := by
    exact (HDP.psi2Norm_marginal_le_vector (hfinite i) hv).trans (hpsi i)
  have hprod := HDP.psi1Norm_mul_le hXum hXvm hXu hXv
  change HDP.SubExponential (fun ω => Xu ω * Xv ω) μ ∧
    HDP.psi1Norm (fun ω => Xu ω * Xv ω) μ ≤ 2 * K ^ 2
  refine ⟨hprod.1, ?_⟩
  calc
    HDP.psi1Norm (fun ω => Xu ω * Xv ω) μ ≤
        HDP.psi2Norm Xu μ * HDP.psi2Norm Xv μ := hprod.2
    _ ≤ (2 * K) * K := mul_le_mul hXuNorm hXvNorm
      (HDP.psi2Norm_nonneg _ μ) (by positivity)
    _ = 2 * K ^ 2 := by ring

/-- The summands in (9.7) are centered by isotropy.

**Book Equation (9.7).** -/
private theorem integral_squaredIncrementSummand_eq_zero [IsProbabilityMeasure μ]
    {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (i : Fin m) :
    ∫ ω, squaredIncrementSummand A (x + y)
      (‖x - y‖⁻¹ • (x - y)) i ω ∂μ = 0 := by
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hxx := HDP.Chapter4.isotropic_row_marginal_secondMoment
    A hrowsm hsub hiso i x
  have hyy := HDP.Chapter4.isotropic_row_marginal_secondMoment
    A hrowsm hsub hiso i y
  have hfun : (fun ω => squaredIncrementSummand A (x + y)
      (‖x - y‖⁻¹ • (x - y)) i ω) =
      fun ω => ‖x - y‖⁻¹ *
        (inner ℝ (HDP.randomMatrixRow A i ω) x ^ 2 -
          inner ℝ (HDP.randomMatrixRow A i ω) y ^ 2) := by
    funext ω
    simp [squaredIncrementSummand, inner_add_right, inner_smul_right,
      inner_sub_right]
    ring
  rw [hfun, integral_const_mul,
    integral_sub]
  · rw [hxx, hyy, hx, hy]
    norm_num
  · have hm : MemLp
        (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) x) 2 μ := by
      simpa using (hsub.marginal i x).memLp
        (hrowsm.aemeasurable_marginal i x) (p := (2 : ℝ)) (by norm_num)
    exact hm.integrable_sq
  · have hm : MemLp
        (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) y) 2 μ := by
      simpa using (hsub.marginal i y).memLp
        (hrowsm.aemeasurable_marginal i y) (p := (2 : ℝ)) (by norm_num)
    exact hm.integrable_sq

/-- Squared norm differences have the expected `sqrt m ‖x-y‖` scale. Step 2: the squared process has a Gaussian tail up to scale `√m`.
The explicit exponent `1/(32K⁴)` is obtained from Bernstein's `1/8` and
the `2K²` summand bound.

**Book Equation (9.6).** -/
theorem squaredMatrixIncrement_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y)
    {t : ℝ} (ht : 0 ≤ t) (htm : t ≤ Real.sqrt m) :
    μ {ω | t * Real.sqrt m ≤ |squaredMatrixIncrement A x y ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (32 * K ^ 4))) := by
  let u := x + y
  let v := ‖x - y‖⁻¹ • (x - y)
  let Y : Fin m → Ω → ℝ := fun i => squaredIncrementSummand A u v i
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i =>
    (hrowsm.aemeasurable_marginal i u).mul
      (hrowsm.aemeasurable_marginal i v)
  have hY : ∀ i, HDP.SubExponential (Y i) μ := fun i => by
    simpa [Y, u, v] using
      (squaredIncrementSummand_control A hrowsm hsub hfinite hK hpsi
        x y hx hy hxy i).1
  have hYnorm : ∀ i, HDP.psi1Norm (Y i) μ ≤ 2 * K ^ 2 := fun i => by
    simpa [Y, u, v] using
      (squaredIncrementSummand_control A hrowsm hsub hfinite hK hpsi
        x y hx hy hxy i).2
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := fun i => by
    simpa [Y, u, v] using integral_squaredIncrementSummand_eq_zero
      A hrowsm hsub hiso x y hx hy hxy i
  have hYindep : iIndepFun Y μ :=
    hindep.comp
      (fun i z => inner ℝ z u * inner ℝ z v) (fun _ => by fun_prop)
  have hbern := HDP.bernstein_weighted
    (X := Y) (fun _ : Fin m => (1 : ℝ))
    hYm hY hYmean hYindep
    (show 0 < 2 * K ^ 2 by positivity) (show (0 : ℝ) < 1 by norm_num)
    hYnorm (fun _ => by simp)
    (show 0 ≤ t * Real.sqrt m by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hKlower : 1 ≤ 2 * K ^ 2 := by
    let i0 : Fin m := ⟨0, hm⟩
    let X0 : Ω → ℝ := fun ω => inner ℝ (HDP.randomMatrixRow A i0 ω) x
    have hsecond : ∫ ω, X0 ω ^ 2 ∂μ = 1 := by
      simpa [X0, hx] using
        HDP.Chapter4.isotropic_row_marginal_secondMoment
          A hrowsm hsub hiso i0 x
    have hnorm : HDP.psi2Norm X0 μ ≤ K :=
      (HDP.psi2Norm_marginal_le_vector (hfinite i0) hx).trans (hpsi i0)
    exact HDP.Chapter3.one_le_two_mul_sq_of_secondMoment_one
      (hrowsm.aemeasurable_marginal i0 x) (hsub.marginal i0 x)
      hsecond hK hnorm
  have hsqrtSq : (Real.sqrt m) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  have hsumOne : ∑ _i : Fin m, (1 : ℝ) ^ 2 = (m : ℝ) := by simp
  have hfirst :
      (t * Real.sqrt m) ^ 2 /
          ((2 * K ^ 2) ^ 2 * ∑ _i : Fin m, (1 : ℝ) ^ 2) =
        t ^ 2 / (4 * K ^ 4) := by
    rw [hsumOne, mul_pow, hsqrtSq]
    field_simp
    ring
  have hsecond : t ^ 2 / (4 * K ^ 4) ≤
      (t * Real.sqrt m) / (2 * K ^ 2) := by
    have htK : t ≤ 2 * K ^ 2 * Real.sqrt m := by
      calc
        t ≤ Real.sqrt m := htm
        _ ≤ 2 * K ^ 2 * Real.sqrt m :=
          by simpa using mul_le_mul_of_nonneg_right hKlower hsqrt.le
    have hmul := mul_le_mul_of_nonneg_left htK ht
    field_simp [hK.ne']
    nlinarith
  have hmin : t ^ 2 / (4 * K ^ 4) ≤
      min ((t * Real.sqrt m) ^ 2 /
        ((2 * K ^ 2) ^ 2 * ∑ _i : Fin m, (1 : ℝ) ^ 2))
        ((t * Real.sqrt m) / ((2 * K ^ 2) * 1)) := by
    rw [hfirst]
    simpa using hsecond
  have hexp : ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
      min ((t * Real.sqrt m) ^ 2 /
        ((2 * K ^ 2) ^ 2 * ∑ _i : Fin m, (1 : ℝ) ^ 2))
        ((t * Real.sqrt m) / ((2 * K ^ 2) * 1)))) ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (32 * K ^ 4))) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc
      -(1 / 8 : ℝ) * min ((t * Real.sqrt m) ^ 2 /
          ((2 * K ^ 2) ^ 2 * ∑ _i : Fin m, (1 : ℝ) ^ 2))
          (t * Real.sqrt m / (2 * K ^ 2 * 1)) ≤
          -(1 / 8 : ℝ) * (t ^ 2 / (4 * K ^ 4)) :=
        mul_le_mul_of_nonpos_left hmin (by norm_num)
      _ = -t ^ 2 / (32 * K ^ 4) := by
        field_simp [hK.ne']
        ring
  have hsumEq : (fun ω => ∑ i, Y i ω) = squaredMatrixIncrement A x y := by
    funext ω
    exact (squaredMatrixIncrement_eq_sum A x y hxy ω).symm
  have hweighted : (fun ω => ∑ i, (1 : ℝ) * Y i ω) =
      squaredMatrixIncrement A x y := by
    simpa using hsumEq
  rw [← hweighted]
  exact hbern.trans hexp

/-- Step 3, small-deviation range. For unit `x,y`, the normalized increment
is controlled by the squared process unless one of the two matrix norms falls
below half of its isotropic location.

**Lean implementation helper.** -/
private theorem unitNormalizedIncrement_small_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y)
    {t : ℝ} (ht : 0 ≤ t) (htm : t ≤ Real.sqrt m) :
    μ {ω | t ≤
        |(matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) /
          ‖x - y‖|} ≤
      ENNReal.ofReal (6 * Real.exp
        (-t ^ 2 / matrixUnitIncrementScale K ^ 2)) := by
  let B : ℝ := matrixUnitIncrementScale K
  let a : ℝ := matrixFixedDirectionConstant * K ^ 2
  let d : ℝ := ‖x - y‖
  let s : ℝ := t * a / B
  let E : Set Ω :=
    {ω | t * Real.sqrt m ≤ |squaredMatrixIncrement A x y ω|}
  let Ex : Set Ω := {ω | ‖matrixAction A x ω‖ < Real.sqrt m / 2}
  let Ey : Set Ω := {ω | ‖matrixAction A y ω‖ < Real.sqrt m / 2}
  have hB : 0 < B := matrixUnitIncrementScale_pos hK
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos matrixFixedDirectionConstant_pos (sq_pos_of_pos hK)
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have htwoa : 2 * a ≤ B := by
    dsimp [a, B, matrixUnitIncrementScale]
    have hs128 : 0 ≤ Real.sqrt 128 := Real.sqrt_nonneg _
    have hKsq : 0 ≤ K ^ 2 := sq_nonneg K
    nlinarith [mul_nonneg hs128 hKsq]
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsHalf : s ≤ Real.sqrt m / 2 := by
    have hatio : a / B ≤ 1 / 2 := by
      rw [div_le_iff₀ hB]
      nlinarith
    calc
      s = t * (a / B) := by dsimp [s]; ring
      _ ≤ t * (1 / 2) := mul_le_mul_of_nonneg_left hatio ht
      _ ≤ Real.sqrt m * (1 / 2) :=
        mul_le_mul_of_nonneg_right htm (by norm_num)
      _ = Real.sqrt m / 2 := by ring
  have hsource :
      {ω | t ≤
          |(matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) /
            ‖x - y‖|} ⊆ E ∪ (Ex ∪ Ey) := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    have hxlow : Real.sqrt m / 2 ≤ ‖matrixAction A x ω‖ := by
      exact le_of_not_gt (show ¬ ω ∈ Ex from hnot.2.1)
    have hylow : Real.sqrt m / 2 ≤ ‖matrixAction A y ω‖ := by
      exact le_of_not_gt (show ¬ ω ∈ Ey from hnot.2.2)
    have hsum : Real.sqrt m ≤
        ‖matrixAction A x ω‖ + ‖matrixAction A y ω‖ := by
      linarith
    have hZ : matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω =
          ‖matrixAction A x ω‖ - ‖matrixAction A y ω‖ := by
      simp [matrixDeviationProcess, hx, hy]
    have htd : t * d ≤
        |‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| := by
      rw [hZ, abs_div, abs_of_pos hd] at hω
      exact (le_div_iff₀ hd).mp hω
    have hq : t * Real.sqrt m ≤
        |squaredMatrixIncrement A x y ω| := by
      rw [abs_squaredMatrixIncrement A x y hxy ω]
      have htquot : t ≤
          |‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| / d :=
        (le_div_iff₀ hd).2 htd
      calc
        t * Real.sqrt m ≤
            (|‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| / d) *
              Real.sqrt m :=
          mul_le_mul_of_nonneg_right htquot (Real.sqrt_nonneg m)
        _ ≤ (|‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| / d) *
              (‖matrixAction A x ω‖ + ‖matrixAction A y ω‖) :=
            mul_le_mul_of_nonneg_left hsum (div_nonneg (abs_nonneg _) hd.le)
        _ = |‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| *
              (‖matrixAction A x ω‖ + ‖matrixAction A y ω‖) / d := by
            ring
    exact hnot.1 hq
  have hE : μ E ≤ ENNReal.ofReal
      (2 * Real.exp (-t ^ 2 / B ^ 2)) := by
    have hb := squaredMatrixIncrement_tail hm A hrowsm hsub hiso hindep
      hfinite hK hpsi x y hx hy hxy ht htm
    have hc : Real.exp (-t ^ 2 / (32 * K ^ 4)) ≤
        Real.exp (-t ^ 2 / B ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hden : 0 < 32 * K ^ 4 := by positivity
      have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
      have hdenB : 32 * K ^ 4 ≤ B ^ 2 := by
        dsimp [B, matrixUnitIncrementScale]
        have hs : 0 ≤ Real.sqrt 128 := Real.sqrt_nonneg _
        have hsSq : (Real.sqrt 128) ^ 2 = 128 := Real.sq_sqrt (by norm_num)
        have hC : 0 ≤ 2 * matrixFixedDirectionConstant :=
          mul_nonneg (by norm_num) matrixFixedDirectionConstant_pos.le
        have hsumSq : (Real.sqrt 128) ^ 2 ≤
            (Real.sqrt 128 + 2 * matrixFixedDirectionConstant) ^ 2 :=
          (sq_le_sq₀ hs (add_nonneg hs hC)).2 (by linarith)
        nlinarith [sq_nonneg (K ^ 2)]
      have hdiv := div_le_div_of_nonneg_left (sq_nonneg t) hden hdenB
      simpa only [neg_div] using neg_le_neg hdiv
    exact hb.trans (by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hc (by norm_num))
  have hEx : μ Ex ≤ ENNReal.ofReal
      (2 * Real.exp (-t ^ 2 / B ^ 2)) := by
    have hmono : Ex ⊆ {ω | s ≤ |matrixDeviationProcess A x ω|} := by
      intro ω hω
      change ‖matrixAction A x ω‖ < Real.sqrt m / 2 at hω
      change s ≤ |‖matrixAction A x ω‖ - Real.sqrt m * ‖x‖|
      rw [hx, mul_one, abs_of_nonpos (by linarith)]
      linarith
    have htX := matrixDeviation_unit_tail hm A hrowsm hsub hiso hindep
      hfinite hK hpsi x hx hs0
    calc
      μ Ex ≤ μ {ω | s ≤ |matrixDeviationProcess A x ω|} := measure_mono hmono
      _ ≤ ENNReal.ofReal (2 * Real.exp (-s ^ 2 / a ^ 2)) := by
        simpa [a] using htX
      _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / B ^ 2)) := by
        congr 3
        dsimp [s]
        field_simp [ha.ne', hB.ne']
  have hEy : μ Ey ≤ ENNReal.ofReal
      (2 * Real.exp (-t ^ 2 / B ^ 2)) := by
    have hmono : Ey ⊆ {ω | s ≤ |matrixDeviationProcess A y ω|} := by
      intro ω hω
      change ‖matrixAction A y ω‖ < Real.sqrt m / 2 at hω
      change s ≤ |‖matrixAction A y ω‖ - Real.sqrt m * ‖y‖|
      rw [hy, mul_one, abs_of_nonpos (by linarith)]
      linarith
    have htY := matrixDeviation_unit_tail hm A hrowsm hsub hiso hindep
      hfinite hK hpsi y hy hs0
    calc
      μ Ey ≤ μ {ω | s ≤ |matrixDeviationProcess A y ω|} := measure_mono hmono
      _ ≤ ENNReal.ofReal (2 * Real.exp (-s ^ 2 / a ^ 2)) := by
        simpa [a] using htY
      _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / B ^ 2)) := by
        congr 3
        dsimp [s]
        field_simp [ha.ne', hB.ne']
  calc
    μ {ω | t ≤
        |(matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) /
          ‖x - y‖|} ≤ μ (E ∪ (Ex ∪ Ey)) := measure_mono hsource
    _ ≤ μ E + μ (Ex ∪ Ey) := measure_union_le _ _
    _ ≤ μ E + (μ Ex + μ Ey) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / B ^ 2)) +
          (ENNReal.ofReal (2 * Real.exp (-t ^ 2 / B ^ 2)) +
            ENNReal.ofReal (2 * Real.exp (-t ^ 2 / B ^ 2))) :=
      add_le_add hE (add_le_add hEx hEy)
    _ = ENNReal.ofReal (6 * Real.exp
          (-t ^ 2 / matrixUnitIncrementScale K ^ 2)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp [B]
      ring

/-- The all-scale version of Step 3. The middle range reuses the estimate at
`t = √m`; above `2√m`, reverse triangle reduces the event to a fixed
direction.

**Lean implementation helper.** -/
private theorem unitNormalizedIncrement_tail [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤
        |(matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) /
          ‖x - y‖|} ≤
      ENNReal.ofReal (6 * Real.exp
        (-t ^ 2 / (2 * matrixUnitIncrementScale K) ^ 2)) := by
  let B : ℝ := matrixUnitIncrementScale K
  let d : ℝ := ‖x - y‖
  have hB : 0 < B := matrixUnitIncrementScale_pos hK
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  by_cases hsmall : t ≤ Real.sqrt m
  · have hs := unitNormalizedIncrement_small_tail hm A hrowsm hsub hiso
      hindep hfinite hK hpsi x y hx hy hxy ht hsmall
    exact hs.trans (by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (gaussianTail_mono_scale hB (by linarith : B ≤ 2 * B))
        (by norm_num))
  · have hlarge : Real.sqrt m < t := lt_of_not_ge hsmall
    by_cases hmiddle : t ≤ 2 * Real.sqrt m
    · let W : Ω → ℝ := fun ω =>
          (matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) / d
      have hmono : {ω | t ≤ |W ω|} ⊆
          {ω | Real.sqrt m ≤ |W ω|} := by
        intro ω hω
        exact hlarge.le.trans hω
      have hs := unitNormalizedIncrement_small_tail hm A hrowsm hsub hiso
        hindep hfinite hK hpsi x y hx hy hxy hsqrt.le le_rfl
      have hsqrtSq : (Real.sqrt m) ^ 2 = (m : ℝ) :=
        Real.sq_sqrt hmR.le
      have hexp : Real.exp (-(Real.sqrt m) ^ 2 / B ^ 2) ≤
          Real.exp (-t ^ 2 / (2 * B) ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
        have htSq : t ^ 2 ≤ (2 * Real.sqrt m) ^ 2 :=
          (sq_le_sq₀ ht
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg m))).2 hmiddle
        field_simp [hB.ne']
        nlinarith [hsqrtSq]
      calc
        μ {ω | t ≤
            |(matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) /
              ‖x - y‖|} = μ {ω | t ≤ |W ω|} := by rfl
        _ ≤ μ {ω | Real.sqrt m ≤ |W ω|} := measure_mono hmono
        _ ≤ ENNReal.ofReal
            (6 * Real.exp (-(Real.sqrt m) ^ 2 / B ^ 2)) := by
          simpa [W, d, B] using hs
        _ ≤ ENNReal.ofReal (6 * Real.exp (-t ^ 2 / (2 * B) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)
        _ = ENNReal.ofReal (6 * Real.exp
            (-t ^ 2 / (2 * matrixUnitIncrementScale K) ^ 2)) := by rfl
    · have htTwo : 2 * Real.sqrt m < t := lt_of_not_ge hmiddle
      let v : EuclideanSpace ℝ (Fin n) := d⁻¹ • (x - y)
      let W : Ω → ℝ := fun ω =>
        (matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) / d
      have hv : ‖v‖ = 1 := by
        simp [v, d, norm_smul, hd.ne']
      have hscaleVec : d • v = x - y := by
        simp [v, d, hd.ne']
      have hmono : {ω | t ≤ |W ω|} ⊆
          {ω | t / 2 ≤ |matrixDeviationProcess A v ω|} := by
        intro ω hω
        have hZd : matrixDeviationProcess A x ω -
            matrixDeviationProcess A y ω =
              ‖matrixAction A x ω‖ - ‖matrixAction A y ω‖ := by
          simp [matrixDeviationProcess, hx, hy]
        have htdiff : t * d ≤
            |‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| := by
          change t ≤ |(matrixDeviationProcess A x ω -
            matrixDeviationProcess A y ω) / d| at hω
          rw [hZd, abs_div, abs_of_pos hd] at hω
          exact (le_div_iff₀ hd).mp hω
        have hreverse :
            |‖matrixAction A x ω‖ - ‖matrixAction A y ω‖| ≤
              ‖matrixAction A (x - y) ω‖ := by
          rw [matrixAction_sub]
          exact abs_norm_sub_norm_le _ _
        have hAv : ‖matrixAction A (x - y) ω‖ =
            d * ‖matrixAction A v ω‖ := by
          rw [← hscaleVec, matrixAction_smul, norm_smul,
            Real.norm_eq_abs, abs_of_pos hd]
        have htRv : t ≤ ‖matrixAction A v ω‖ := by
          rw [hAv] at hreverse
          exact le_of_mul_le_mul_left
            (by simpa [mul_comm] using htdiff.trans hreverse) hd
        have hdev : t / 2 ≤ matrixDeviationProcess A v ω := by
          rw [matrixDeviationProcess, hv, mul_one]
          nlinarith
        exact hdev.trans (le_abs_self _)
      have ht2 : 0 ≤ t / 2 := div_nonneg ht (by norm_num)
      have hf := matrixDeviation_unit_tail hm A hrowsm hsub hiso hindep
        hfinite hK hpsi v hv ht2
      have ha : 0 < matrixFixedDirectionConstant * K ^ 2 :=
        mul_pos matrixFixedDirectionConstant_pos (sq_pos_of_pos hK)
      have haB : matrixFixedDirectionConstant * K ^ 2 ≤ B := by
        dsimp [B, matrixUnitIncrementScale]
        have hs : 0 ≤ Real.sqrt 128 := Real.sqrt_nonneg _
        have hk : 0 ≤ K ^ 2 := sq_nonneg K
        nlinarith [mul_nonneg hs hk,
          mul_pos matrixFixedDirectionConstant_pos (sq_pos_of_pos hK)]
      have hexp : Real.exp (-(t / 2) ^ 2 /
          (matrixFixedDirectionConstant * K ^ 2) ^ 2) ≤
          Real.exp (-t ^ 2 / (2 * B) ^ 2) := by
        have hmTail := gaussianTail_mono_scale (t := t / 2) ha haB
        convert hmTail using 1
        all_goals ring_nf
      calc
        μ {ω | t ≤
            |(matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) /
              ‖x - y‖|} = μ {ω | t ≤ |W ω|} := by rfl
        _ ≤ μ {ω | t / 2 ≤ |matrixDeviationProcess A v ω|} :=
          measure_mono hmono
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(t / 2) ^ 2 /
            (matrixFixedDirectionConstant * K ^ 2) ^ 2)) := hf
        _ ≤ ENNReal.ofReal (6 * Real.exp (-t ^ 2 / (2 * B) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          calc
            2 * Real.exp (-(t / 2) ^ 2 /
                (matrixFixedDirectionConstant * K ^ 2) ^ 2) ≤
                2 * Real.exp (-t ^ 2 / (2 * B) ^ 2) :=
              mul_le_mul_of_nonneg_left hexp (by norm_num)
            _ ≤ 6 * Real.exp (-t ^ 2 / (2 * B) ^ 2) := by
              nlinarith [Real.exp_pos (-t ^ 2 / (2 * B) ^ 2)]
        _ = ENNReal.ofReal (6 * Real.exp
            (-t ^ 2 / (2 * matrixUnitIncrementScale K) ^ 2)) := by rfl

/-- Explicit unit-sphere increment constant from Step 3.

**Lean implementation helper.** -/
def matrixUnitIncrementConstant : ℝ :=
  8 * Real.sqrt 5 *
    (Real.sqrt 128 + 2 * matrixFixedDirectionConstant)

/-- The matrix unit increment constant is strictly positive.

**Lean implementation helper.** -/
theorem matrixUnitIncrementConstant_pos :
    0 < matrixUnitIncrementConstant := by
  unfold matrixUnitIncrementConstant
  exact mul_pos
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
    (add_pos (Real.sqrt_pos.2 (by norm_num))
      (mul_pos (by norm_num) matrixFixedDirectionConstant_pos))

/-- The matrix fixed direction constant is bounded above by the unit increment constant.

**Lean implementation helper.** -/
theorem matrixFixedDirectionConstant_le_unitIncrementConstant :
    matrixFixedDirectionConstant ≤ matrixUnitIncrementConstant := by
  have hsqrt5 : 1 ≤ Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
      Real.sqrt_nonneg 5]
  have hfactor : 1 ≤ 8 * Real.sqrt 5 := by nlinarith
  have hsum : 0 ≤ Real.sqrt 128 + 2 * matrixFixedDirectionConstant :=
    add_nonneg (Real.sqrt_nonneg 128)
      (mul_nonneg (by norm_num) matrixFixedDirectionConstant_pos.le)
  have hfirst : matrixFixedDirectionConstant ≤
      Real.sqrt 128 + 2 * matrixFixedDirectionConstant := by
    nlinarith [Real.sqrt_nonneg 128, matrixFixedDirectionConstant_pos]
  calc
    matrixFixedDirectionConstant ≤
        Real.sqrt 128 + 2 * matrixFixedDirectionConstant := hfirst
    _ ≤ (8 * Real.sqrt 5) *
        (Real.sqrt 128 + 2 * matrixFixedDirectionConstant) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hsum]
    _ = matrixUnitIncrementConstant := by
      simp [matrixUnitIncrementConstant]

/-- Norm increments for two unit vectors are subgaussian. Step 3 of Theorem 9.1.2, including the coincident-point case.

**Book Equation (9.5).** -/
theorem matrixDeviation_unit_pair [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    HDP.SubGaussian (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) μ ∧
      HDP.psi2Norm (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) μ ≤
        matrixUnitIncrementConstant * K ^ 2 * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    have hbase := matrixDeviation_unit hm A hrowsm hsub hiso hindep
      hfinite hK hpsi x hx
    have hz : (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A x ω) =
        fun ω => (0 : ℝ) * matrixDeviationProcess A x ω := by
      funext ω
      ring
    rw [hz]
    refine ⟨hbase.1.const_mul 0, ?_⟩
    rw [HDP.psi2Norm_const_mul]
    simp
  · let d : ℝ := ‖x - y‖
    let W : Ω → ℝ := fun ω =>
      (matrixDeviationProcess A x ω - matrixDeviationProcess A y ω) / d
    have hd : 0 < d := by
      dsimp [d]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hWm : AEMeasurable W μ :=
      ((aemeasurable_matrixDeviationProcess A hrowsm x).sub
        (aemeasurable_matrixDeviationProcess A hrowsm y)).div_const d
    have htail : ∀ t : ℝ, 0 ≤ t →
        μ {ω | t ≤ |W ω|} ≤ ENNReal.ofReal
          (6 * Real.exp (-t ^ 2 / (2 * matrixUnitIncrementScale K) ^ 2)) := by
      intro t ht
      simpa [W, d] using unitNormalizedIncrement_tail hm A hrowsm hsub hiso
        hindep hfinite hK hpsi x y hx hy hxy ht
    have hW := psi2Norm_le_of_six_tail hWm
      (show 0 < 2 * matrixUnitIncrementScale K by
        exact mul_pos (by norm_num) (matrixUnitIncrementScale_pos hK))
      htail
    have hfun : (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) = fun ω => d * W ω := by
      funext ω
      dsimp [W]
      field_simp [hd.ne']
    rw [hfun]
    refine ⟨hW.1.const_mul d, ?_⟩
    rw [HDP.psi2Norm_const_mul, abs_of_pos hd]
    calc
      d * HDP.psi2Norm W μ ≤
          d * (Real.sqrt 5 * (4 * (2 * matrixUnitIncrementScale K))) :=
        mul_le_mul_of_nonneg_left hW.2 hd.le
      _ = matrixUnitIncrementConstant * K ^ 2 * ‖x - y‖ := by
        simp [d, matrixUnitIncrementConstant, matrixUnitIncrementScale]
        ring

/-! ## Step 4: radial extension -/

/-- The final explicit constant in Theorem 9.1.2. The factor `√2` is
exactly the loss in promoted Exercise 9.1.

**Book Theorem 9.1.2.** -/
def matrixDeviationIncrementConstant : ℝ :=
  Real.sqrt 2 * matrixUnitIncrementConstant

/-- The matrix deviation increment constant is strictly positive.

**Lean implementation helper.** -/
theorem matrixDeviationIncrementConstant_pos :
    0 < matrixDeviationIncrementConstant := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num))
    matrixUnitIncrementConstant_pos

/-- Step 4 in the ordered nonzero case. Normalize the shorter vector, split
the increment into a unit-sphere increment and one radial increment, and use
Exercise 9.1 to recombine the two distances.

**Book Exercise 9.1.** -/
private theorem matrixDeviation_pair_of_norm_le [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n)) (hx0 : x ≠ 0)
    (hxyNorm : ‖x‖ ≤ ‖y‖) :
    HDP.SubGaussian (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) μ ∧
      HDP.psi2Norm (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) μ ≤
        matrixDeviationIncrementConstant * K ^ 2 * ‖x - y‖ := by
  let r : ℝ := ‖x‖
  let xbar : EuclideanSpace ℝ (Fin n) := r⁻¹ • x
  let yprime : EuclideanSpace ℝ (Fin n) := r⁻¹ • y
  let q : ℝ := ‖yprime‖
  let ybar : EuclideanSpace ℝ (Fin n) := q⁻¹ • yprime
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr hx0
  have hxbar : ‖xbar‖ = 1 := by
    simp [xbar, r, norm_smul, hr.ne']
  have hyprime : ‖yprime‖ = r⁻¹ * ‖y‖ := by
    rw [show yprime = r⁻¹ • y by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  have hq : 1 ≤ q := by
    rw [show q = r⁻¹ * ‖y‖ by simpa [q] using hyprime]
    rw [show (1 : ℝ) = r⁻¹ * r by field_simp]
    exact mul_le_mul_of_nonneg_left hxyNorm (inv_nonneg.mpr hr.le)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hybar : ‖ybar‖ = 1 := by
    simp [ybar, q, norm_smul, hqpos.ne']
  have hxrepr : x = r • xbar := by
    simp [xbar, r, hr.ne']
  have hyrepr : y = r • yprime := by
    simp [yprime, r, hr.ne']
  have hyprime_repr : yprime = q • ybar := by
    simp [ybar, q, hqpos.ne']
  have hradial : ‖ybar - yprime‖ = q - 1 := by
    rw [hyprime_repr]
    have heq : ybar - q • ybar = (1 - q) • ybar := by module
    rw [heq, norm_smul, hybar, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  let P : Ω → ℝ := fun ω =>
    matrixDeviationProcess A xbar ω - matrixDeviationProcess A ybar ω
  let R : Ω → ℝ := fun ω =>
    (1 - q) * matrixDeviationProcess A ybar ω
  have hP := matrixDeviation_unit_pair hm A hrowsm hsub hiso hindep
    hfinite hK hpsi xbar ybar hxbar hybar
  have hY := matrixDeviation_unit hm A hrowsm hsub hiso hindep
    hfinite hK hpsi ybar hybar
  have hPm : AEMeasurable P μ :=
    (aemeasurable_matrixDeviationProcess A hrowsm xbar).sub
      (aemeasurable_matrixDeviationProcess A hrowsm ybar)
  have hRm : AEMeasurable R μ :=
    (aemeasurable_matrixDeviationProcess A hrowsm ybar).const_mul (1 - q)
  have hRsg : HDP.SubGaussian R μ := by
    exact hY.1.const_mul (1 - q)
  have hsumSG : HDP.SubGaussian (fun ω => P ω + R ω) μ :=
    hP.1.add hPm hRm hRsg
  have hRnorm : HDP.psi2Norm R μ ≤
      matrixUnitIncrementConstant * K ^ 2 * ‖ybar - yprime‖ := by
    rw [HDP.psi2Norm_const_mul]
    have habs : |1 - q| = q - 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hq)]
      ring
    rw [habs, hradial]
    have hcoeff : 0 ≤ q - 1 := sub_nonneg.mpr hq
    calc
      (q - 1) * HDP.psi2Norm (matrixDeviationProcess A ybar) μ ≤
          (q - 1) * (matrixFixedDirectionConstant * K ^ 2) :=
        mul_le_mul_of_nonneg_left hY.2 hcoeff
      _ ≤ (q - 1) * (matrixUnitIncrementConstant * K ^ 2) := by
        gcongr
        exact matrixFixedDirectionConstant_le_unitIncrementConstant
      _ = matrixUnitIncrementConstant * K ^ 2 * (q - 1) := by ring
  have hsumNorm : HDP.psi2Norm (fun ω => P ω + R ω) μ ≤
      matrixUnitIncrementConstant * K ^ 2 *
        (‖xbar - ybar‖ + ‖ybar - yprime‖) := by
    calc
      HDP.psi2Norm (fun ω => P ω + R ω) μ ≤
          HDP.psi2Norm P μ + HDP.psi2Norm R μ :=
        HDP.psi2Norm_add_le hPm hRm hP.1 hRsg
      _ ≤ matrixUnitIncrementConstant * K ^ 2 * ‖xbar - ybar‖ +
          matrixUnitIncrementConstant * K ^ 2 * ‖ybar - yprime‖ :=
        add_le_add hP.2 hRnorm
      _ = matrixUnitIncrementConstant * K ^ 2 *
          (‖xbar - ybar‖ + ‖ybar - yprime‖) := by ring
  have hreverse : ‖xbar - ybar‖ + ‖ybar - yprime‖ ≤
      Real.sqrt 2 * ‖xbar - yprime‖ := by
    simpa [ybar, q] using
      (exercise_9_1_reverse_triangle xbar yprime hxbar
        (show 1 ≤ ‖yprime‖ by simpa [q] using hq)).2
  have hZx : matrixDeviationProcess A x =
      fun ω => r * matrixDeviationProcess A xbar ω := by
    rw [hxrepr]
    exact matrixDeviationProcess_smul_of_nonneg A hr.le xbar
  have hZy : matrixDeviationProcess A y =
      fun ω => r * (q * matrixDeviationProcess A ybar ω) := by
    rw [hyrepr, hyprime_repr]
    funext ω
    rw [congrFun (matrixDeviationProcess_smul_of_nonneg A hr.le
      (q • ybar)) ω,
      congrFun (matrixDeviationProcess_smul_of_nonneg A hqpos.le ybar) ω]
  have hfun : (fun ω => matrixDeviationProcess A x ω -
      matrixDeviationProcess A y ω) =
      fun ω => r * (P ω + R ω) := by
    funext ω
    rw [congrFun hZx ω, congrFun hZy ω]
    simp only [P, R]
    ring
  have hnormdiff : ‖x - y‖ = r * ‖xbar - yprime‖ := by
    rw [hxrepr, hyrepr, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
  rw [hfun]
  refine ⟨hsumSG.const_mul r, ?_⟩
  rw [HDP.psi2Norm_const_mul, abs_of_pos hr]
  calc
    r * HDP.psi2Norm (fun ω => P ω + R ω) μ ≤
        r * (matrixUnitIncrementConstant * K ^ 2 *
          (‖xbar - ybar‖ + ‖ybar - yprime‖)) :=
      mul_le_mul_of_nonneg_left hsumNorm hr.le
    _ ≤ r * (matrixUnitIncrementConstant * K ^ 2 *
          (Real.sqrt 2 * ‖xbar - yprime‖)) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      exact mul_le_mul_of_nonneg_left hreverse
        (mul_nonneg matrixUnitIncrementConstant_pos.le (sq_nonneg K))
    _ = matrixDeviationIncrementConstant * K ^ 2 * ‖x - y‖ := by
      rw [hnormdiff]
      simp [matrixDeviationIncrementConstant]
      ring

/-- The increment from a nonzero vector to the origin is subgaussian with the fixed-direction scale.

**Lean implementation helper.** -/
private theorem matrixDeviation_pair_zero [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx0 : x ≠ 0) :
    HDP.SubGaussian (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A 0 ω) μ ∧
      HDP.psi2Norm (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A 0 ω) μ ≤
        matrixDeviationIncrementConstant * K ^ 2 * ‖x - 0‖ := by
  let r : ℝ := ‖x‖
  let xbar : EuclideanSpace ℝ (Fin n) := r⁻¹ • x
  have hr : 0 < r := by
    dsimp [r]
    exact norm_pos_iff.mpr hx0
  have hxbar : ‖xbar‖ = 1 := by
    simp [xbar, r, norm_smul, hr.ne']
  have hxrepr : x = r • xbar := by
    simp [xbar, r, hr.ne']
  have hunit := matrixDeviation_unit hm A hrowsm hsub hiso hindep
    hfinite hK hpsi xbar hxbar
  have hfun : (fun ω => matrixDeviationProcess A x ω -
      matrixDeviationProcess A 0 ω) =
      fun ω => r * matrixDeviationProcess A xbar ω := by
    funext ω
    rw [congrFun (matrixDeviationProcess_zero A) ω]
    simp only [Pi.zero_apply, sub_zero]
    rw [hxrepr, congrFun
      (matrixDeviationProcess_smul_of_nonneg A hr.le xbar) ω]
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hfixedFinal : matrixFixedDirectionConstant ≤
      matrixDeviationIncrementConstant := by
    calc
      matrixFixedDirectionConstant ≤ matrixUnitIncrementConstant :=
        matrixFixedDirectionConstant_le_unitIncrementConstant
      _ ≤ Real.sqrt 2 * matrixUnitIncrementConstant := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt)
          matrixUnitIncrementConstant_pos.le]
      _ = matrixDeviationIncrementConstant := rfl
  rw [hfun]
  refine ⟨hunit.1.const_mul r, ?_⟩
  rw [HDP.psi2Norm_const_mul, abs_of_pos hr]
  have hcoeff : 0 ≤ r := hr.le
  calc
    r * HDP.psi2Norm (matrixDeviationProcess A xbar) μ ≤
        r * (matrixFixedDirectionConstant * K ^ 2) :=
      mul_le_mul_of_nonneg_left hunit.2 hcoeff
    _ ≤ r * (matrixDeviationIncrementConstant * K ^ 2) := by
      gcongr
    _ = matrixDeviationIncrementConstant * K ^ 2 * ‖x - 0‖ := by
      simp [r]
      ring

/-- The matrix norm-deviation process has subgaussian increments.

**Book Theorem 9.1.2.** -/
theorem theorem_9_1_2_subGaussianIncrements [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x y : EuclideanSpace ℝ (Fin n)) :
    HDP.SubGaussian (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) μ ∧
      HDP.psi2Norm (fun ω => matrixDeviationProcess A x ω -
        matrixDeviationProcess A y ω) μ ≤
        matrixDeviationIncrementConstant * K ^ 2 * ‖x - y‖ := by
  by_cases hx0 : x = 0
  · subst x
    by_cases hy0 : y = 0
    · subst y
      have hzfun : (fun ω => matrixDeviationProcess A 0 ω -
          matrixDeviationProcess A 0 ω) = fun _ : Ω => (0 : ℝ) := by
        funext ω
        ring
      have hzae : (fun _ : Ω => (0 : ℝ)) =ᵐ[μ] 0 :=
        Filter.Eventually.of_forall fun _ => rfl
      have hzsg : HDP.SubGaussian (fun _ : Ω => (0 : ℝ)) μ := by
        refine ⟨1, one_pos, ?_⟩
        rw [HDP.psi2MGF_of_ae_zero hzae]
        norm_num
      have hznorm : HDP.psi2Norm (fun _ : Ω => (0 : ℝ)) μ = 0 := by
        have hhom := HDP.psi2Norm_const_mul (μ := μ)
          (fun _ : Ω => (0 : ℝ)) 0
        simpa using hhom
      rw [hzfun]
      refine ⟨hzsg, ?_⟩
      rw [hznorm]
      exact mul_nonneg
        (mul_nonneg matrixDeviationIncrementConstant_pos.le (sq_nonneg K))
        (norm_nonneg _)
    · have hordered := matrixDeviation_pair_zero hm A hrowsm hsub
        hiso hindep hfinite hK hpsi y hy0
      have hfun : (fun ω => matrixDeviationProcess A 0 ω -
          matrixDeviationProcess A y ω) =
          fun ω => (-1 : ℝ) *
            (matrixDeviationProcess A y ω - matrixDeviationProcess A 0 ω) := by
        funext ω
        ring
      rw [hfun]
      refine ⟨hordered.1.const_mul (-1), ?_⟩
      rw [HDP.psi2Norm_const_mul]
      simpa [norm_sub_rev] using hordered.2
  · by_cases hy0 : y = 0
    · subst y
      exact matrixDeviation_pair_zero hm A hrowsm hsub hiso hindep
        hfinite hK hpsi x hx0
    · rcases le_total ‖x‖ ‖y‖ with hxy | hyx
      · exact matrixDeviation_pair_of_norm_le hm A hrowsm hsub hiso hindep
          hfinite hK hpsi x y hx0 hxy
      · have hordered := matrixDeviation_pair_of_norm_le hm A hrowsm hsub
          hiso hindep hfinite hK hpsi y x hy0 hyx
        have hfun : (fun ω => matrixDeviationProcess A x ω -
            matrixDeviationProcess A y ω) =
            fun ω => (-1 : ℝ) *
              (matrixDeviationProcess A y ω - matrixDeviationProcess A x ω) := by
          funext ω
          ring
        rw [hfun]
        refine ⟨hordered.1.const_mul (-1), ?_⟩
        rw [HDP.psi2Norm_const_mul]
        simpa [norm_sub_rev] using hordered.2

end

end HDP.Chapter9

end Source_02_SubGaussianIncrements

/-! ## Material formerly in `03_MatrixDeviationInequality.lean` -/

section Source_03_MatrixDeviationInequality

/-!
# Book Chapter 9, §9.1: the matrix deviation inequality

The source writes suprema over arbitrary bounded sets.  The expectation form
uses the book-wide finite-subfamily convention, while the high-probability
form below constructs the actual bad event on the whole set.  Its
measurability follows by identifying it with the increasing union over a
canonical countable dense exhaustion; no unmeasurable raw supremum is put
under a Bochner integral.

Theorem 9.1.1 follows from the increment theorem in module 02 and the fully
proved anchored Talagrand comparison from Chapter 8.  The two variants which
the source delegates to Exercises 9.2 and 9.3 are promoted here because the
quadratic version is used in covariance estimation.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Measurability and finite moments -/

/-- The matrix action is measurable.

**Lean implementation helper.** -/
theorem measurable_matrixAction {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (x : EuclideanSpace ℝ (Fin n)) :
    Measurable (matrixAction A x) := by
  have hraw : Measurable (fun ω => (A ω).mulVec x.ofLp) := by
    apply measurable_pi_lambda
    intro i
    simpa [Matrix.mulVec, dotProduct, HDP.inner_randomMatrixRow]
      using hrowsm.measurable_marginal i x
  change Measurable (fun ω => WithLp.toLp 2 ((A ω).mulVec x.ofLp))
  exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp hraw

/-- The matrix deviation process is measurable.

**Lean implementation helper.** -/
theorem measurable_matrixDeviationProcess {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (x : EuclideanSpace ℝ (Fin n)) :
    Measurable (matrixDeviationProcess A x) := by
  exact (measurable_matrixAction A hrowsm x).norm.sub measurable_const

/-- The absolute finite supremum is genuinely measurable.

**Lean implementation helper.** -/
theorem measurable_finiteMatrixDeviation {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] :
    Measurable (finiteMatrixDeviation A T) := by
  apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
  intro x
  exact measurable_matrixDeviationProcess A hrowsm x.1

/-- Every coordinate of the deviation process has a finite second moment.

**Lean implementation helper.** -/
theorem matrixDeviationProcess_memLp_two
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n)) :
    MemLp (matrixDeviationProcess A x) 2 μ := by
  have hinc := theorem_9_1_2_subGaussianIncrements hm A
    (hrowsm.aemeasurable_rows μ) hsub hiso hindep hfinite hK hpsi x 0
  have hsg : HDP.SubGaussian (matrixDeviationProcess A x) μ := by
    simpa [matrixDeviationProcess_zero] using hinc.1
  simpa using hsg.memLp
    (measurable_matrixDeviationProcess A hrowsm x).aemeasurable
    (p := (2 : ℝ)) (by norm_num)

/-- The finite absolute supremum has a finite second moment.

**Lean implementation helper.** -/
theorem finiteMatrixDeviation_memLp_two
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] :
    MemLp (finiteMatrixDeviation A T) 2 μ := by
  let Z : HDP.RandomProcess ↥T Ω :=
    HDP.Chapter8.finiteEuclideanProcess T (matrixDeviationProcess A)
  have hraw : MemLp
      (Finset.univ.sup' Finset.univ_nonempty
        (fun x : ↥T => fun ω => |Z x ω|)) 2 μ :=
    Finset.sup'_induction Finset.univ_nonempty
      (fun x : ↥T => fun ω => |Z x ω|)
      (p := fun f : Ω → ℝ => MemLp f 2 μ)
      (fun _ hf _ hg => hf.sup hg)
      (fun x _ => by
        simpa only [Z, HDP.Chapter8.finiteEuclideanProcess,
          Real.norm_eq_abs]
          using (matrixDeviationProcess_memLp_two hm A hrowsm hsub hiso
            hindep hfinite hK hpsi x.1).norm)
  have heq :
      (Finset.univ.sup' Finset.univ_nonempty
        (fun x : ↥T => fun ω => |Z x ω|)) =
        HDP.Chapter8.finiteProcessAbsoluteSup Z := by
    funext ω
    simp only [HDP.Chapter8.finiteProcessAbsoluteSup, Finset.sup'_apply]
  rw [heq] at hraw
  change MemLp (HDP.Chapter8.finiteProcessAbsoluteSup Z) 2 μ
  exact hraw

/-- The finite matrix deviation is integrable.

**Lean implementation helper.** -/
theorem integrable_finiteMatrixDeviation
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] :
    Integrable (finiteMatrixDeviation A T) μ :=
  (finiteMatrixDeviation_memLp_two hm A hrowsm hsub hiso hindep
    hfinite hK hpsi T).integrable (by norm_num)

/-- The finite supremum of the deviation process dominates the absolute deviation at every point of the indexing set.

**Lean implementation helper.** -/
theorem abs_matrixDeviationProcess_le_finite {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (ω : Ω) :
    |matrixDeviationProcess A x ω| ≤ finiteMatrixDeviation A T ω := by
  let Z : HDP.RandomProcess ↥T Ω :=
    HDP.Chapter8.finiteEuclideanProcess T (matrixDeviationProcess A)
  let z : ↥T := ⟨x, hx⟩
  change |Z z ω| ≤ HDP.Chapter8.finiteProcessAbsoluteSup Z ω
  unfold HDP.Chapter8.finiteProcessAbsoluteSup
  exact Finset.le_sup'
    (fun q : ↥T => |Z q ω|)
    (Finset.mem_univ z)

/-! ## Theorem 9.1.1 and its tail form -/

/-- Explicit universal constant in the finite form of Theorem 9.1.1.

**Book Theorem 9.1.1.** -/
def matrixDeviationConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  HDP.Chapter8.exercise837ExpectationConstant *
    matrixDeviationIncrementConstant

/-- The matrix deviation constant is strictly positive.

**Lean implementation helper.** -/
theorem matrixDeviationConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < matrixDeviationConstant := by
  exact mul_pos HDP.Chapter8.exercise837ExpectationConstant_pos
    matrixDeviationIncrementConstant_pos

/-- Matrix deviations on a set are controlled in expectation by its Gaussian complexity. Finite-subfamily form.

**Book Theorem 9.1.1.** -/
theorem theorem_9_1_1_matrixDeviation
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteMatrixDeviation A T ω ∂μ) ≤
      matrixDeviationConstant * K ^ 2 *
        HDP.Chapter7.gaussianComplexity T := by
  have hmain := HDP.Chapter8.exercise_8_37a_expectation μ T hT
    (matrixDeviationProcess A)
    (fun x _ => measurable_matrixDeviationProcess A hrowsm x)
    (matrixDeviationProcess_zero A)
    (mul_nonneg matrixDeviationIncrementConstant_pos.le (sq_nonneg K))
    (fun x _ y _ => theorem_9_1_2_subGaussianIncrements hm A
      (hrowsm.aemeasurable_rows μ) hsub hiso hindep hfinite hK hpsi x y)
  simpa [finiteMatrixDeviation, matrixDeviationConstant, mul_assoc]
    using hmain

/-! The book states Theorem 9.1.1 for an arbitrary subset.  A pointwise
supremum over a nonseparable set need not be measurable, so the authoritative
arbitrary-set interface is the extended-valued envelope over all nonempty
finite subfamilies.  On a finite set it specializes to the real-valued theorem
above, while no boundedness or hidden measurability assumption is needed in
the definition itself. -/

/-- Extended envelope of the expected matrix deviation over all nonempty
finite subfamilies of `T`.

**Lean implementation helper.** -/
def matrixDeviationExpectationEnvelope
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal (∫ ω, finiteMatrixDeviation A F ω ∂μ)

/-- Extended Gaussian-complexity envelope over the same finite subfamilies.
This is the arbitrary-set interpretation of the right-hand side of Theorem
9.1.1.

**Book Theorem 9.1.1.** -/
def gaussianComplexityEnvelope {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F)

/-- Matrix deviations on a set are controlled in expectation by its Gaussian complexity. Arbitrary-set finite-subfamily-envelope form.

**Book Theorem 9.1.1.** -/
theorem theorem_9_1_1_matrixDeviation_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    matrixDeviationExpectationEnvelope (μ := μ) A T ≤
      ENNReal.ofReal (matrixDeviationConstant * K ^ 2) *
        gaussianComplexityEnvelope T := by
  unfold matrixDeviationExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  have hmain := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi F hF
  have hcoef : 0 ≤ matrixDeviationConstant * K ^ 2 :=
    mul_nonneg matrixDeviationConstant_pos.le (sq_nonneg K)
  have hcomplexity :
      ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) ≤
        gaussianComplexityEnvelope T := by
    unfold gaussianComplexityEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  calc
    ENNReal.ofReal (∫ ω, finiteMatrixDeviation A F ω ∂μ) ≤
        ENNReal.ofReal
          (matrixDeviationConstant * K ^ 2 *
            HDP.Chapter7.gaussianComplexity F) :=
      ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (matrixDeviationConstant * K ^ 2) *
        ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (matrixDeviationConstant * K ^ 2) *
        gaussianComplexityEnvelope T := by gcongr

/-- Explicit universal constant in display (9.11).

**Book Equation (9.11).** -/
def matrixDeviationHighProbabilityConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  HDP.Chapter8.exercise837HighProbabilityConstant *
    matrixDeviationIncrementConstant

/-- The matrix deviation high probability constant is strictly positive.

**Lean implementation helper.** -/
theorem matrixDeviationHighProbabilityConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < matrixDeviationHighProbabilityConstant := by
  exact mul_pos HDP.Chapter8.exercise837HighProbabilityConstant_pos
    matrixDeviationIncrementConstant_pos

/-- Finite-subfamily form.

**Book Remark 9.1.4.** -/
theorem remark_9_1_4_matrixDeviation_highProbability
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K u : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hu : 0 ≤ u)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    μ {ω | matrixDeviationHighProbabilityConstant * K ^ 2 *
          (HDP.Chapter7.gaussianWidth T +
            u * HDP.Chapter7.finiteRadius T) <
        finiteMatrixDeviation A T ω} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  have hmain := HDP.Chapter8.exercise_8_37b_highProbability μ T hT
    (matrixDeviationProcess A)
    (fun x _ => measurable_matrixDeviationProcess A hrowsm x)
    (matrixDeviationProcess_zero A)
    (mul_nonneg matrixDeviationIncrementConstant_pos.le (sq_nonneg K)) hu
    (fun x _ y _ => theorem_9_1_2_subGaussianIncrements hm A
      (hrowsm.aemeasurable_rows μ) hsub hiso hindep hfinite hK hpsi x y)
  simpa [finiteMatrixDeviation, matrixDeviationHighProbabilityConstant,
    mul_assoc] using hmain

/-- Extended envelope of the finite-family bad-event probabilities in
Remark 9.1.4. The threshold is evaluated on the same finite family as the
deviation, so this definition does not silently replace an uncountable
supremum by a measurable random variable.

**Book Remark 9.1.4.** -/
def matrixDeviationHighProbabilityEnvelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (K u : ℝ) (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    μ {ω | matrixDeviationHighProbabilityConstant * K ^ 2 *
          (HDP.Chapter7.gaussianWidth F +
            u * HDP.Chapter7.finiteRadius F) <
        finiteMatrixDeviation A F ω}

/-- Arbitrary-set
finite-subfamily-envelope form. Equivalently, the displayed tail estimate
holds uniformly over every nonempty finite subfamily of `T`.

**Book Remark 9.1.4.** -/
theorem remark_9_1_4_matrixDeviation_highProbability_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K u : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hu : 0 ≤ u) (T : Set (EuclideanSpace ℝ (Fin n))) :
    matrixDeviationHighProbabilityEnvelope (μ := μ) A K u T ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  unfold matrixDeviationHighProbabilityEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  exact remark_9_1_4_matrixDeviation_highProbability hm A hrowsm hsub
    hiso hindep hfinite hK hpsi hu F hF

/-! ### The actual arbitrary-set bad event

The preceding envelope is retained for compatibility.  It is not, however,
the source's single event involving the supremum over `T`: its finite-family
threshold varies with the family.  The following construction recovers the
actual source event.  Finite-dimensional Euclidean sets are separable, and
the deviation process is continuous in its vector argument, so the event is
the increasing union of the corresponding events on canonical finite dense
prefixes. -/

/-- Canonical dense point of a nonempty Euclidean set, as a subtype value.

**Lean implementation helper.** -/
def matrixDeviationDenseSubtypePoint {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (i : ℕ) : T :=
  TopologicalSpace.denseSeq T i

/-- Canonical dense point, coerced to the ambient Euclidean space.

**Lean implementation helper.** -/
def matrixDeviationDensePoint {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (i : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (matrixDeviationDenseSubtypePoint T i : EuclideanSpace ℝ (Fin n))

/-- The first `k + 1` canonical dense points used in the §9.1 exhaustion.

**Book Section 9.1.** -/
def matrixDeviationDensePrefix {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (k : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  (Finset.range (k + 1)).image (matrixDeviationDensePoint T)

/-- Every point chosen by the dense enumeration belongs to the original set.

**Lean implementation helper.** -/
theorem matrixDeviationDensePoint_mem {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (i : ℕ) :
    matrixDeviationDensePoint T i ∈ T :=
  (matrixDeviationDenseSubtypePoint T i).property

/-- The point with index `i` belongs to every dense prefix whose terminal index is at least `i`.

**Lean implementation helper.** -/
theorem matrixDeviationDensePoint_mem_prefix {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    {i k : ℕ} (hik : i ≤ k) :
    matrixDeviationDensePoint T i ∈ matrixDeviationDensePrefix T k := by
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- Every finite prefix of the dense enumeration contains at least its initial point.

**Lean implementation helper.** -/
theorem matrixDeviationDensePrefix_nonempty {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (k : ℕ) :
    (matrixDeviationDensePrefix T k).Nonempty := by
  exact ⟨matrixDeviationDensePoint T 0,
    matrixDeviationDensePoint_mem_prefix T (Nat.zero_le k)⟩

/-- Every finite prefix of the dense enumeration is contained in the original set.

**Lean implementation helper.** -/
theorem matrixDeviationDensePrefix_subset {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (k : ℕ) :
    (matrixDeviationDensePrefix T k :
      Set (EuclideanSpace ℝ (Fin n))) ⊆ T := by
  intro x hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  exact matrixDeviationDensePoint_mem T i

/-- Increasing the terminal index can only enlarge the finite dense prefix.

**Lean implementation helper.** -/
theorem matrixDeviationDensePrefix_mono {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    {j k : ℕ} (hjk : j ≤ k) :
    matrixDeviationDensePrefix T j ⊆ matrixDeviationDensePrefix T k := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hi
    omega), rfl⟩

/-- A continuous function is bounded on the set once it is bounded on the
canonical dense sequence.

**Lean implementation helper.** -/
theorem continuous_le_of_matrixDeviationDenseSubtypePoint_le {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (f : T → ℝ) (hf : Continuous f) {c : ℝ}
    (hseq : ∀ i, f (matrixDeviationDenseSubtypePoint T i) ≤ c) :
    ∀ x, f x ≤ c := by
  intro x
  have hclosed : IsClosed {y : T | f y ≤ c} :=
    isClosed_le hf continuous_const
  have hrange : Set.range (TopologicalSpace.denseSeq T) ⊆
      {y : T | f y ≤ c} := by
    rintro _ ⟨i, rfl⟩
    exact hseq i
  have hx : x ∈ closure (Set.range (TopologicalSpace.denseSeq T)) := by
    rw [(TopologicalSpace.denseRange_denseSeq T).closure_range]
    trivial
  exact (closure_minimal hrange hclosed) hx

/-- Finite deviation suprema are monotone under inclusion.

**Lean implementation helper.** -/
theorem finiteMatrixDeviation_mono_of_subset {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    {F G : Finset (EuclideanSpace ℝ (Fin n))}
    (hF : F.Nonempty) (hG : G.Nonempty) (hFG : F ⊆ G) (ω : Ω) :
    letI : Nonempty ↥F := hF.to_subtype
    letI : Nonempty ↥G := hG.to_subtype
    finiteMatrixDeviation A F ω ≤ finiteMatrixDeviation A G ω := by
  letI : Nonempty ↥F := hF.to_subtype
  letI : Nonempty ↥G := hG.to_subtype
  unfold finiteMatrixDeviation HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro x _hx
  let y : ↥G := ⟨x.1, hFG x.2⟩
  simpa [HDP.Chapter8.finiteEuclideanProcess, y] using
    (Finset.le_sup'
      (fun z : ↥G =>
        |HDP.Chapter8.finiteEuclideanProcess G
          (matrixDeviationProcess A) z ω|)
      (Finset.mem_univ y))

/-- Safe real radius of an arbitrary bounded set, obtained from the
authoritative extended finite-subfamily envelope.

**Lean implementation helper.** -/
def matrixDeviationSetRadius {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (HDP.Chapter8.setRadiusEnvelope T).toReal

/-- A nonempty finite subfamily has radius no larger than the actual-set
radius.

**Lean implementation helper.** -/
theorem finiteRadius_le_matrixDeviationSetRadius {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
    (hF : F.Nonempty) :
    HDP.Chapter7.finiteRadius F ≤ matrixDeviationSetRadius T := by
  let U : HDP.Chapter8.NonemptyFiniteSubset T := ⟨F, hF, hFT⟩
  have hENN : ENNReal.ofReal (HDP.Chapter7.finiteRadius F) ≤
      HDP.Chapter8.setRadiusEnvelope T := by
    unfold HDP.Chapter8.setRadiusEnvelope
    exact le_iSup
      (fun V : HDP.Chapter8.NonemptyFiniteSubset T =>
        ENNReal.ofReal (HDP.Chapter7.finiteRadius V.carrier)) U
  have hfin : HDP.Chapter8.setRadiusEnvelope T ≠ ⊤ :=
    HDP.Chapter8.setRadiusEnvelope_ne_top_of_isBounded hTb
  have hreal := ENNReal.toReal_mono hfin hENN
  simpa [matrixDeviationSetRadius,
    ENNReal.toReal_ofReal (HDP.Chapter7.finiteRadius_nonneg F)] using hreal

/-- A nonempty finite subfamily has Gaussian width no larger than the
actual-set Gaussian-width envelope.

**Lean implementation helper.** -/
theorem finiteGaussianWidth_le_matrixDeviationSetWidth {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hTne : T.Nonempty) (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
    (hF : F.Nonempty) :
    HDP.Chapter7.gaussianWidth F ≤
      HDP.Chapter8.euclideanSetGaussianWidth T := by
  have hENN : ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
      HDP.Chapter8.euclideanSetGaussianWidthENN T := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  have hfin : HDP.Chapter8.euclideanSetGaussianWidthENN T ≠ ⊤ :=
    HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top hTne hTb
  have hreal := ENNReal.toReal_mono hfin hENN
  simpa [HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal
      (HDP.Chapter7.gaussianWidth_nonneg F hF)] using hreal

/-- The genuine arbitrary-set bad event in Remark 9.1.4. The existential
form is definitionally the strict inequality for the pointwise supremum, but
does not presuppose measurability of an uncountable supremum.

**Book Remark 9.1.4.** -/
def matrixDeviationSetBadEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (threshold : ℝ) : Set Ω :=
  {ω | ∃ x, x ∈ T ∧ threshold < |matrixDeviationProcess A x ω|}

/-- Bad event on a canonical finite dense prefix.

**Lean implementation helper.** -/
def matrixDeviationDensePrefixBadEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (threshold : ℝ) (k : ℕ) : Set Ω :=
  letI : Nonempty ↥(matrixDeviationDensePrefix T k) :=
    (matrixDeviationDensePrefix_nonempty T k).to_subtype
  {ω | threshold <
    finiteMatrixDeviation A (matrixDeviationDensePrefix T k) ω}

/-- Continuity identifies the actual-set event with the countable union of
finite-prefix events.

**Lean implementation helper.** -/
theorem matrixDeviationSetBadEvent_eq_iUnion {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (threshold : ℝ) :
    matrixDeviationSetBadEvent A T threshold =
      ⋃ k, matrixDeviationDensePrefixBadEvent A T threshold k := by
  ext ω
  constructor
  · rintro ⟨x, hxT, hx⟩
    by_contra hnot
    have hnotEvent : ∀ k,
        ω ∉ matrixDeviationDensePrefixBadEvent A T threshold k := by
      intro k hk
      exact hnot (Set.mem_iUnion.mpr ⟨k, hk⟩)
    have hdenseBound : ∀ k,
        |matrixDeviationProcess A (matrixDeviationDensePoint T k) ω| ≤
          threshold := by
      intro k
      let F := matrixDeviationDensePrefix T k
      have hF : F.Nonempty := matrixDeviationDensePrefix_nonempty T k
      letI : Nonempty ↥F := hF.to_subtype
      have hpoint := abs_matrixDeviationProcess_le_finite A F
        (matrixDeviationDensePoint_mem_prefix T (le_refl k)) ω
      have hdev : finiteMatrixDeviation A F ω ≤ threshold := by
        exact not_lt.mp (hnotEvent k)
      exact hpoint.trans hdev
    let f : T → ℝ := fun y => |matrixDeviationProcess A y.1 ω|
    have haction : Continuous (fun y : T => matrixAction A y.1 ω) := by
      change Continuous (fun y : T => (A ω).toEuclideanLin y.1)
      exact (A ω).toEuclideanLin.toContinuousLinearMap.continuous.comp
        continuous_subtype_val
    have hfcont : Continuous f := by
      exact (haction.norm.sub
        (continuous_const.mul
          (continuous_subtype_val.norm :
            Continuous (fun y : T => ‖y.1‖)))).abs
    have hdenseSubtypeBound : ∀ k,
        f (matrixDeviationDenseSubtypePoint T k) ≤ threshold := by
      intro k
      exact hdenseBound k
    have hxbound : f ⟨x, hxT⟩ ≤ threshold :=
      continuous_le_of_matrixDeviationDenseSubtypePoint_le T f hfcont
        hdenseSubtypeBound ⟨x, hxT⟩
    exact (not_le_of_gt hx) hxbound
  · intro hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
    let F := matrixDeviationDensePrefix T k
    have hF : F.Nonempty := matrixDeviationDensePrefix_nonempty T k
    letI : Nonempty ↥F := hF.to_subtype
    change threshold < finiteMatrixDeviation A F ω at hk
    by_contra hnot
    have hpoint : ∀ x ∈ F,
        |matrixDeviationProcess A x ω| ≤ threshold := by
      intro x hx
      exact not_lt.mp (fun hlt => hnot
        ⟨x, matrixDeviationDensePrefix_subset T k hx, hlt⟩)
    have hsup : finiteMatrixDeviation A F ω ≤ threshold := by
      unfold finiteMatrixDeviation HDP.Chapter8.finiteProcessAbsoluteSup
      apply Finset.sup'_le
      intro x _hx
      exact hpoint x.1 x.2
    exact (not_le_of_gt hk) hsup

/-- The actual-set bad event is measurable, with no measurability hypothesis
on `T`.

**Lean implementation helper.** -/
theorem measurableSet_matrixDeviationSetBadEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (threshold : ℝ) :
    MeasurableSet (matrixDeviationSetBadEvent A T threshold) := by
  rw [matrixDeviationSetBadEvent_eq_iUnion]
  apply MeasurableSet.iUnion
  intro k
  letI : Nonempty ↥(matrixDeviationDensePrefix T k) :=
    (matrixDeviationDensePrefix_nonempty T k).to_subtype
  exact measurableSet_lt measurable_const
    (measurable_finiteMatrixDeviation A hrowsm
      (matrixDeviationDensePrefix T k))

/-- The finite-prefix bad events increase with the prefix.

**Lean implementation helper.** -/
theorem matrixDeviationDensePrefixBadEvent_mono {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (threshold : ℝ) :
    Monotone (matrixDeviationDensePrefixBadEvent A T threshold) := by
  intro k l hkl ω hω
  let F := matrixDeviationDensePrefix T k
  let G := matrixDeviationDensePrefix T l
  have hF : F.Nonempty := matrixDeviationDensePrefix_nonempty T k
  have hG : G.Nonempty := matrixDeviationDensePrefix_nonempty T l
  letI : Nonempty ↥F := hF.to_subtype
  letI : Nonempty ↥G := hG.to_subtype
  change threshold < finiteMatrixDeviation A F ω at hω
  change threshold < finiteMatrixDeviation A G ω
  exact hω.trans_le (finiteMatrixDeviation_mono_of_subset A hF hG
    (matrixDeviationDensePrefix_mono T hkl) ω)

/-- The source threshold `C K² (w(T) + u rad(T))`, with both arbitrary-set
quantities converted to reals only through their finite extended envelopes.

**Lean implementation helper.** -/
def matrixDeviationSetHighProbabilityThreshold
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {n : ℕ} (K u : ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  matrixDeviationHighProbabilityConstant * K ^ 2 *
    (HDP.Chapter8.euclideanSetGaussianWidth T +
      u * matrixDeviationSetRadius T)

/-- Matrix deviations obey the corresponding high-probability bound. For one actual nonempty bounded
set. This is the source-facing arbitrary-set theorem; the older `_envelope`
endpoint above is only a compatibility theorem about varying finite-family
thresholds.

**Book Remark 9.1.4.** -/
theorem remark_9_1_4_matrixDeviation_highProbability_set
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K u : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hu : 0 ≤ u)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTne : T.Nonempty) (hTb : Bornology.IsBounded T) :
    μ (matrixDeviationSetBadEvent A T
      (matrixDeviationSetHighProbabilityThreshold K u T)) ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  letI : Nonempty T := hTne.to_subtype
  let threshold := matrixDeviationSetHighProbabilityThreshold K u T
  let event : ℕ → Set Ω :=
    matrixDeviationDensePrefixBadEvent A T threshold
  have heventTail : ∀ k, μ (event k) ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
    intro k
    let F := matrixDeviationDensePrefix T k
    have hF : F.Nonempty := matrixDeviationDensePrefix_nonempty T k
    letI : Nonempty ↥F := hF.to_subtype
    have hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T :=
      matrixDeviationDensePrefix_subset T k
    have hwidth : HDP.Chapter7.gaussianWidth F ≤
        HDP.Chapter8.euclideanSetGaussianWidth T :=
      finiteGaussianWidth_le_matrixDeviationSetWidth hTne hTb F hFT hF
    have hradius : HDP.Chapter7.finiteRadius F ≤
        matrixDeviationSetRadius T :=
      finiteRadius_le_matrixDeviationSetRadius hTb F hFT hF
    have hfiniteThreshold :
        matrixDeviationHighProbabilityConstant * K ^ 2 *
            (HDP.Chapter7.gaussianWidth F +
              u * HDP.Chapter7.finiteRadius F) ≤ threshold := by
      dsimp [threshold, matrixDeviationSetHighProbabilityThreshold]
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hwidth
          (mul_le_mul_of_nonneg_left hradius hu)
      · exact mul_nonneg matrixDeviationHighProbabilityConstant_pos.le
          (sq_nonneg K)
    have htail := remark_9_1_4_matrixDeviation_highProbability hm A hrowsm
      hsub hiso hindep hfinite hK hpsi hu F hF
    calc
      μ (event k) ≤ μ {ω |
          matrixDeviationHighProbabilityConstant * K ^ 2 *
              (HDP.Chapter7.gaussianWidth F +
                u * HDP.Chapter7.finiteRadius F) <
            finiteMatrixDeviation A F ω} := by
        apply measure_mono
        intro ω hω
        change threshold < finiteMatrixDeviation A F ω at hω
        exact hfiniteThreshold.trans_lt hω
      _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := htail
  rw [matrixDeviationSetBadEvent_eq_iUnion]
  rw [(matrixDeviationDensePrefixBadEvent_mono A T threshold).measure_iUnion]
  exact iSup_le heventTail

/-! ## Exercise 9.2: deviations around the mean -/

/-- Finite supremum of the centered process from Remark 9.1.3. Since the
deterministic term `sqrt m * ‖x‖` cancels under centering, this is exactly
`sup_x |‖Ax‖ - E ‖Ax‖|`.

**Book Remark 9.1.3.** -/
def finiteCenteredMatrixDeviation {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (μ : Measure Ω) (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (HDP.Chapter8.finiteEuclideanProcess T
      (fun x ω => matrixDeviationProcess A x ω -
        ∫ ξ, matrixDeviationProcess A x ξ ∂μ)) ω

/-- The centered finite deviation is bounded by the uncentered deviation plus its expectation.

**Lean implementation helper.** -/
theorem finiteCenteredMatrixDeviation_le
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) :
    finiteCenteredMatrixDeviation A T μ ω ≤
      finiteMatrixDeviation A T ω +
        ∫ ξ, finiteMatrixDeviation A T ξ ∂μ := by
  unfold finiteCenteredMatrixDeviation
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro x hx
  have hxmem : x.1 ∈ T := x.2
  have hZint := (matrixDeviationProcess_memLp_two hm A hrowsm hsub hiso
    hindep hfinite hK hpsi x.1).integrable (by norm_num)
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T
  have habsInt : |∫ ξ, matrixDeviationProcess A x.1 ξ ∂μ| ≤
      ∫ ξ, finiteMatrixDeviation A T ξ ∂μ := by
    calc
      |∫ ξ, matrixDeviationProcess A x.1 ξ ∂μ| ≤
          ∫ ξ, |matrixDeviationProcess A x.1 ξ| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ξ, finiteMatrixDeviation A T ξ ∂μ :=
        integral_mono hZint.abs hFint
          (fun ξ => abs_matrixDeviationProcess_le_finite A T hxmem ξ)
  calc
    |HDP.Chapter8.finiteEuclideanProcess T
        (fun x ω => matrixDeviationProcess A x ω -
          ∫ ξ, matrixDeviationProcess A x ξ ∂μ) x ω| ≤
        |matrixDeviationProcess A x.1 ω| +
          |∫ ξ, matrixDeviationProcess A x.1 ξ ∂μ| := abs_sub _ _
    _ ≤ finiteMatrixDeviation A T ω +
        ∫ ξ, finiteMatrixDeviation A T ξ ∂μ :=
      add_le_add (abs_matrixDeviationProcess_le_finite A T hxmem ω) habsInt

/-- Explicit constant for the centered form.

**Lean implementation helper.** -/
def centeredMatrixDeviationConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  2 * matrixDeviationConstant

/-- / Remark 9.1.3.

**Book Exercise 9.2.** -/
theorem exercise_9_2_centeredMatrixDeviation
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteCenteredMatrixDeviation A T μ ω ∂μ) ≤
      centeredMatrixDeviationConstant * K ^ 2 *
        HDP.Chapter7.gaussianComplexity T := by
  let F := finiteMatrixDeviation A T
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T
  have hcenterMeas : Measurable (finiteCenteredMatrixDeviation A T μ) := by
    apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
    intro x
    exact (measurable_matrixDeviationProcess A hrowsm x.1).sub_const _
  have hcenterInt : Integrable (finiteCenteredMatrixDeviation A T μ) μ := by
    refine (hFint.add (integrable_const (∫ ξ, F ξ ∂μ))).mono'
      hcenterMeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact finiteCenteredMatrixDeviation_le hm A hrowsm hsub hiso hindep
        hfinite hK hpsi T ω
    · unfold finiteCenteredMatrixDeviation
        HDP.Chapter8.finiteProcessAbsoluteSup
      let x0 : ↥T := Classical.choice inferInstance
      exact (abs_nonneg _).trans
        (Finset.le_sup'
          (fun x : ↥T =>
            |HDP.Chapter8.finiteEuclideanProcess T
              (fun x ω => matrixDeviationProcess A x ω -
                ∫ ξ, matrixDeviationProcess A x ξ ∂μ) x ω|)
          (Finset.mem_univ x0))
  have hmono :
      (∫ ω, finiteCenteredMatrixDeviation A T μ ω ∂μ) ≤
        ∫ ω, (F ω + ∫ ξ, F ξ ∂μ) ∂μ :=
    integral_mono hcenterInt (hFint.add (integrable_const _))
      (fun ω => finiteCenteredMatrixDeviation_le hm A hrowsm hsub hiso
        hindep hfinite hK hpsi T ω)
  have htwice :
      (∫ ω, (F ω + ∫ ξ, F ξ ∂μ) ∂μ) =
        2 * ∫ ξ, F ξ ∂μ := by
    rw [integral_add hFint (integrable_const _)]
    simp
    ring
  have hmain := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hT
  calc
    (∫ ω, finiteCenteredMatrixDeviation A T μ ω ∂μ) ≤
        ∫ ω, (F ω + ∫ ξ, F ξ ∂μ) ∂μ := hmono
    _ = 2 * ∫ ξ, F ξ ∂μ := htwice
    _ ≤ 2 * (matrixDeviationConstant * K ^ 2 *
        HDP.Chapter7.gaussianComplexity T) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = centeredMatrixDeviationConstant * K ^ 2 *
        HDP.Chapter7.gaussianComplexity T := by
      simp [centeredMatrixDeviationConstant]
      ring

/-- The centered matrix deviation constant is strictly positive.

**Lean implementation helper.** -/
theorem centeredMatrixDeviationConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < centeredMatrixDeviationConstant := by
  exact mul_pos (by norm_num) matrixDeviationConstant_pos

/-- Expected centered-deviation envelope over all nonempty finite
subfamilies of an arbitrary set.

**Lean implementation helper.** -/
def centeredMatrixDeviationExpectationEnvelope
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal
      (∫ ω, finiteCenteredMatrixDeviation A F μ ω ∂μ)

/-- Centering converts the matrix-deviation theorem into deviation around `E ‖Ax‖`. Arbitrary-set finite-subfamily-envelope form.

**Book Remark 9.1.3.** -/
theorem exercise_9_2_centeredMatrixDeviation_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    centeredMatrixDeviationExpectationEnvelope (μ := μ) A T ≤
      ENNReal.ofReal (centeredMatrixDeviationConstant * K ^ 2) *
        gaussianComplexityEnvelope T := by
  unfold centeredMatrixDeviationExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  have hmain := exercise_9_2_centeredMatrixDeviation hm A hrowsm hsub
    hiso hindep hfinite hK hpsi F hF
  have hcoef : 0 ≤ centeredMatrixDeviationConstant * K ^ 2 :=
    mul_nonneg centeredMatrixDeviationConstant_pos.le (sq_nonneg K)
  have hcomplexity :
      ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) ≤
        gaussianComplexityEnvelope T := by
    unfold gaussianComplexityEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  calc
    ENNReal.ofReal
        (∫ ω, finiteCenteredMatrixDeviation A F μ ω ∂μ) ≤
        ENNReal.ofReal (centeredMatrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianComplexity F) :=
      ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (centeredMatrixDeviationConstant * K ^ 2) *
        ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (centeredMatrixDeviationConstant * K ^ 2) *
        gaussianComplexityEnvelope T := by gcongr

/-! ## Exercise 9.3: quadratic deviations -/

/-- Finite supremum of the quadratic process in Remark 9.1.5.

**Book Remark 9.1.5.** -/
def finiteMatrixQuadraticDeviation {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (HDP.Chapter8.finiteEuclideanProcess T
      (fun x ω => ‖matrixAction A x ω‖ ^ 2 - m * ‖x‖ ^ 2)) ω

/-- Quadratic norm deviations are controlled by the squared linear deviation and a radius-dependent cross term.

**Lean implementation helper.** -/
theorem finiteMatrixQuadraticDeviation_le {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (ω : Ω) :
    finiteMatrixQuadraticDeviation A T ω ≤
      finiteMatrixDeviation A T ω ^ 2 +
        2 * Real.sqrt m * HDP.Chapter7.finiteRadius T *
          finiteMatrixDeviation A T ω := by
  unfold finiteMatrixQuadraticDeviation
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro x hx
  let a : ℝ := ‖matrixAction A x.1 ω‖
  let b : ℝ := Real.sqrt m * ‖x.1‖
  let F : ℝ := finiteMatrixDeviation A T ω
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hF : 0 ≤ F := finiteMatrixDeviation_nonneg A T ω
  have hz : |a - b| ≤ F := by
    simpa [a, b, F, matrixDeviationProcess]
      using abs_matrixDeviationProcess_le_finite A T x.2 ω
  have har : a ≤ |a - b| + b := by
    linarith [le_abs_self (a - b)]
  have hbr : b ≤ Real.sqrt m * HDP.Chapter7.finiteRadius T := by
    exact mul_le_mul_of_nonneg_left
      (HDP.Chapter7.norm_le_finiteRadius T hT x.2)
      (Real.sqrt_nonneg _)
  have hbSq : b ^ 2 = (m : ℝ) * ‖x.1‖ ^ 2 := by
    dsimp [b]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)]
  change |a ^ 2 - (m : ℝ) * ‖x.1‖ ^ 2| ≤ F ^ 2 +
    2 * Real.sqrt m * HDP.Chapter7.finiteRadius T * F
  rw [← hbSq]
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring,
    abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    |a - b| * (a + b) ≤ F * (F + 2 * b) := by
      apply mul_le_mul hz
      · linarith
      · exact add_nonneg ha hb
      · exact hF
    _ ≤ F * (F + 2 * (Real.sqrt m *
        HDP.Chapter7.finiteRadius T)) := by
      gcongr
    _ = F ^ 2 + 2 * Real.sqrt m *
        HDP.Chapter7.finiteRadius T * F := by ring

/-- Square-term constant in Exercise 9.3.

**Book Exercise 9.3.** -/
def quadraticMatrixDeviationSquareConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  2 * HDP.Chapter8.exercise837MomentConstant ^ 2 *
    matrixDeviationIncrementConstant ^ 2

/-- Linear-term constant in Exercise 9.3.

**Book Exercise 9.3.** -/
def quadraticMatrixDeviationLinearConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  2 * matrixDeviationConstant

/-- / Remark 9.1.5. Both terms
from the printed estimate are retained.

**Book Exercise 9.3.** -/
theorem exercise_9_3_quadraticMatrixDeviation
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteMatrixQuadraticDeviation A T ω ∂μ) ≤
      quadraticMatrixDeviationSquareConstant * K ^ 4 *
          HDP.Chapter7.gaussianComplexity T ^ 2 +
        quadraticMatrixDeviationLinearConstant * K ^ 2 *
          Real.sqrt m * HDP.Chapter7.finiteRadius T *
            HDP.Chapter7.gaussianComplexity T := by
  let F : Ω → ℝ := finiteMatrixDeviation A T
  let G : ℝ := HDP.Chapter7.gaussianComplexity T
  let L : ℝ := matrixDeviationIncrementConstant * K ^ 2
  have hF2 := finiteMatrixDeviation_memLp_two hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T
  have hFint : Integrable F μ := hF2.integrable (by norm_num)
  have hFsqInt : Integrable (fun ω => F ω ^ 2) μ := hF2.integrable_sq
  have hG : 0 ≤ G := HDP.Chapter7.gaussianComplexity_nonneg T
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg matrixDeviationIncrementConstant_pos.le (sq_nonneg K)
  have hlp := HDP.Chapter8.exercise_8_37c_moments μ T hT
    (matrixDeviationProcess A)
    (fun x _ => measurable_matrixDeviationProcess A hrowsm x)
    (matrixDeviationProcess_zero A) hL (show (1 : ℝ) ≤ 2 by norm_num)
    (fun x _ y _ => by
      simpa [L] using theorem_9_1_2_subGaussianIncrements hm A
        (hrowsm.aemeasurable_rows μ) hsub hiso hindep hfinite hK hpsi x y)
  have hlp' : HDP.Chapter1.lpNormRV F 2 μ ≤
      HDP.Chapter8.exercise837MomentConstant * Real.sqrt 2 * L * G := by
    change HDP.Chapter1.lpNormRV
      (HDP.Chapter8.finiteProcessAbsoluteSup
        (HDP.Chapter8.finiteEuclideanProcess T
          (matrixDeviationProcess A))) 2 μ ≤ _
    simpa [G, L] using hlp
  have hlp0 : 0 ≤ HDP.Chapter1.lpNormRV F 2 μ := by
    unfold HDP.Chapter1.lpNormRV
    positivity
  have hrhs0 : 0 ≤
      HDP.Chapter8.exercise837MomentConstant * Real.sqrt 2 * L * G := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg HDP.Chapter8.exercise837MomentConstant_pos.le
          (Real.sqrt_nonneg 2)) hL) hG
  have hlpSq : HDP.Chapter1.lpNormRV F 2 μ ^ 2 ≤
      (HDP.Chapter8.exercise837MomentConstant * Real.sqrt 2 * L * G) ^ 2 :=
    (sq_le_sq₀ hlp0 hrhs0).2 hlp'
  have hFsecond : (∫ ω, F ω ^ 2 ∂μ) ≤
      quadraticMatrixDeviationSquareConstant * K ^ 4 * G ^ 2 := by
    have hid := HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV hF2
    calc
      (∫ ω, F ω ^ 2 ∂μ) = HDP.Chapter1.lpNormRV F 2 μ ^ 2 := by
        rw [hid]
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ ≤ (HDP.Chapter8.exercise837MomentConstant *
          Real.sqrt 2 * L * G) ^ 2 := hlpSq
      _ = quadraticMatrixDeviationSquareConstant * K ^ 4 * G ^ 2 := by
        have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
          Real.sq_sqrt (by norm_num)
        calc
          (HDP.Chapter8.exercise837MomentConstant *
              Real.sqrt 2 * L * G) ^ 2 =
              HDP.Chapter8.exercise837MomentConstant ^ 2 *
                (Real.sqrt 2) ^ 2 * L ^ 2 * G ^ 2 := by ring
          _ = quadraticMatrixDeviationSquareConstant * K ^ 4 * G ^ 2 := by
            rw [hsqrt2]
            dsimp only [quadraticMatrixDeviationSquareConstant, L]
            ring
  have hFmean := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hT
  have hradius0 : 0 ≤ HDP.Chapter7.finiteRadius T := by
    obtain ⟨x, hx⟩ := hT.exists_mem
    exact (norm_nonneg x).trans
      (HDP.Chapter7.norm_le_finiteRadius T hT hx)
  have hQmeas : Measurable (finiteMatrixQuadraticDeviation A T) := by
    apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
    intro x
    exact ((measurable_matrixAction A hrowsm x.1).norm.pow_const 2).sub_const _
  let R : Ω → ℝ := fun ω => F ω ^ 2 +
    2 * Real.sqrt m * HDP.Chapter7.finiteRadius T * F ω
  have hRint : Integrable R μ := by
    exact hFsqInt.add (hFint.const_mul
      (2 * Real.sqrt m * HDP.Chapter7.finiteRadius T))
  have hQint : Integrable (finiteMatrixQuadraticDeviation A T) μ := by
    refine hRint.mono' hQmeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact finiteMatrixQuadraticDeviation_le A T hT ω
    · unfold finiteMatrixQuadraticDeviation
        HDP.Chapter8.finiteProcessAbsoluteSup
      let x0 : ↥T := Classical.choice inferInstance
      exact (abs_nonneg _).trans
        (Finset.le_sup'
          (fun x : ↥T =>
            |HDP.Chapter8.finiteEuclideanProcess T
              (fun x ω => ‖matrixAction A x ω‖ ^ 2 - m * ‖x‖ ^ 2)
              x ω|)
          (Finset.mem_univ x0))
  calc
    (∫ ω, finiteMatrixQuadraticDeviation A T ω ∂μ) ≤
        ∫ ω, R ω ∂μ :=
      integral_mono hQint hRint (fun ω =>
        finiteMatrixQuadraticDeviation_le A T hT ω)
    _ = (∫ ω, F ω ^ 2 ∂μ) +
        2 * Real.sqrt m * HDP.Chapter7.finiteRadius T *
          ∫ ω, F ω ∂μ := by
      rw [integral_add hFsqInt
        (hFint.const_mul (2 * Real.sqrt m * HDP.Chapter7.finiteRadius T)),
        integral_const_mul]
    _ ≤ quadraticMatrixDeviationSquareConstant * K ^ 4 * G ^ 2 +
        2 * Real.sqrt m * HDP.Chapter7.finiteRadius T *
          (matrixDeviationConstant * K ^ 2 * G) := by
      exact add_le_add hFsecond
        (mul_le_mul_of_nonneg_left hFmean
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg m)) hradius0))
    _ = quadraticMatrixDeviationSquareConstant * K ^ 4 * G ^ 2 +
        quadraticMatrixDeviationLinearConstant * K ^ 2 *
          Real.sqrt m * HDP.Chapter7.finiteRadius T * G := by
      simp [quadraticMatrixDeviationLinearConstant]
      ring

/-- Expected quadratic-deviation envelope over all nonempty finite
subfamilies of an arbitrary set.

**Lean implementation helper.** -/
def quadraticMatrixDeviationExpectationEnvelope
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal
      (∫ ω, finiteMatrixQuadraticDeviation A F ω ∂μ)

/-- Exact extended envelope of the two-term right side in Exercise 9.3.
Keeping the radius and complexity indexed by the same finite family retains
the sharp source normalization and is safer than multiplying two unrelated
extended suprema.

**Book Exercise 9.3.** -/
def quadraticMatrixDeviationBoundEnvelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {n : ℕ} (m : ℕ) (K : ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal
      (quadraticMatrixDeviationSquareConstant * K ^ 4 *
          HDP.Chapter7.gaussianComplexity F ^ 2 +
        quadraticMatrixDeviationLinearConstant * K ^ 2 *
          Real.sqrt m * HDP.Chapter7.finiteRadius F *
            HDP.Chapter7.gaussianComplexity F)

/-- Deviations of squared norms follow from deviations of norms. Arbitrary-set finite-subfamily-envelope form.

**Book Remark 9.1.5.** -/
theorem exercise_9_3_quadraticMatrixDeviation_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    quadraticMatrixDeviationExpectationEnvelope (μ := μ) A T ≤
      quadraticMatrixDeviationBoundEnvelope m K T := by
  unfold quadraticMatrixDeviationExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  have hmain := exercise_9_3_quadraticMatrixDeviation hm A hrowsm hsub
    hiso hindep hfinite hK hpsi F hF
  exact (ENNReal.ofReal_le_ofReal hmain).trans
    (by
      unfold quadraticMatrixDeviationBoundEnvelope
      exact le_iSup_of_le F
        (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl)))

end

end HDP.Chapter9

end Source_03_MatrixDeviationInequality

/-! ## Material formerly in `04_RandomProjectionSizes.lean` -/

section Source_04_RandomProjectionSizes

/-!
# Book Chapter 9, §9.2.2: sizes of random projections

Finite sets provide the measurable proof engine.  The canonical source-facing
Proposition 9.2.1 below uses extended-real envelopes over all nonempty finite
subfamilies of an arbitrary bounded set; dividing by `sqrt n` gives the
subgaussian projection `P = A / sqrt n`.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Applying matrix deviation to the unit sphere recovers two-sided singular-value bounds.

**Book Section 9.2.1, before Proposition 9.2.1.** -/
theorem section_9_2_1_twoSidedSingularValues [IsProbabilityMeasure μ]
    {m n : ℕ} [NeZero m] [NeZero n]
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.AEMeasurableRows μ)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | Real.sqrt m - HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
          (Real.sqrt n + u) > HDP.matrixSingularValue (A ω) (n - 1) ∨
        HDP.matrixSingularValue (A ω) 0 >
          Real.sqrt m + HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
            (Real.sqrt n + u)} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  exact HDP.Chapter4.theorem_4_6_1_singular A hrowsm hsub hiso hindep
    hfinite hK hpsi hu

/-- Diameter of the image of a finite set under a random matrix.

**Lean implementation helper.** -/
def finiteRandomMatrixImageDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (fun p : ↥T × ↥T => fun ω =>
      ‖matrixAction A p.1.1 ω - matrixAction A p.2.1 ω‖) ω

/-- The finite random matrix image diameter is nonnegative.

**Lean implementation helper.** -/
theorem finiteRandomMatrixImageDiameter_nonneg {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : 0 ≤ finiteRandomMatrixImageDiameter A T ω := by
  unfold finiteRandomMatrixImageDiameter
    HDP.Chapter8.finiteProcessAbsoluteSup
  let p0 : ↥T × ↥T := Classical.choice inferInstance
  exact (abs_nonneg _).trans
    (Finset.le_sup'
      (fun p : ↥T × ↥T =>
        |‖matrixAction A p.1.1 ω - matrixAction A p.2.1 ω‖|)
      (Finset.mem_univ p0))

/-- The finite random matrix image diameter is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteRandomMatrixImageDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] :
    Measurable (finiteRandomMatrixImageDiameter A T) := by
  apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
  intro p
  exact ((measurable_matrixAction A hrowsm p.1.1).sub
    (measurable_matrixAction A hrowsm p.2.1)).norm

/-- Pointwise deterministic reduction of an image diameter to the matrix
deviation process on `T-T`.

**Lean implementation helper.** -/
theorem finiteRandomMatrixImageDiameter_le {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (ω : Ω) :
    finiteRandomMatrixImageDiameter A T ω ≤
      Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
        letI : Nonempty ↥(HDP.Chapter7.differenceFinset T T) :=
          (HDP.Chapter7.differenceFinset_nonempty hT hT).to_subtype
        finiteMatrixDeviation A (HDP.Chapter7.differenceFinset T T) ω := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  unfold finiteRandomMatrixImageDiameter
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro p hp
  have hp1 : p.1.1 ∈ T := p.1.2
  have hp2 : p.2.1 ∈ T := p.2.2
  have hdmem : p.1.1 - p.2.1 ∈ D := by
    unfold D HDP.Chapter7.differenceFinset
      HDP.Chapter7.minkowskiSumFinset HDP.Chapter7.negFinset
    apply Finset.mem_image.mpr
    refine ⟨(p.1.1, -p.2.1), Finset.mem_product.mpr ⟨hp1, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨p.2.1, hp2, rfl⟩
    · simp [sub_eq_add_neg]
  have hdiam := HDP.Chapter7.norm_sub_le_finiteEuclideanDiameter
    T hT hp1 hp2
  have hdev := abs_matrixDeviationProcess_le_finite A D hdmem ω
  have haction : matrixAction A p.1.1 ω - matrixAction A p.2.1 ω =
      matrixAction A (p.1.1 - p.2.1) ω := by
    rw [matrixAction_sub]
  rw [abs_of_nonneg (norm_nonneg _), haction]
  have hbase : ‖matrixAction A (p.1.1 - p.2.1) ω‖ ≤
      Real.sqrt m * ‖p.1.1 - p.2.1‖ +
        finiteMatrixDeviation A D ω := by
    have hz :
        ‖matrixAction A (p.1.1 - p.2.1) ω‖ -
            Real.sqrt m * ‖p.1.1 - p.2.1‖ ≤
          finiteMatrixDeviation A D ω :=
      (le_abs_self _).trans hdev
    linarith
  exact hbase.trans (by
    simpa [D] using add_le_add
      (mul_le_mul_of_nonneg_left hdiam (Real.sqrt_nonneg _))
      (le_refl (finiteMatrixDeviation A D ω)))

/-- Universal constant for Proposition 9.2.1 before normalization.

**Book Proposition 9.2.1.** -/
def randomProjectionDiameterConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  2 * matrixDeviationConstant

/-- The random projection diameter constant is strictly positive.

**Lean implementation helper.** -/
theorem randomProjectionDiameterConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < randomProjectionDiameterConstant := by
  exact mul_pos (by norm_num) matrixDeviationConstant_pos

/-- Unscaled expectation form used in the proof of Proposition 9.2.1.

**Book Proposition 9.2.1.** -/
theorem randomMatrixImageDiameter_expectation
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteRandomMatrixImageDiameter A T ω ∂μ) ≤
      Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
        randomProjectionDiameterConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  let F : Ω → ℝ := finiteMatrixDeviation A D
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have hdiamMeas := measurable_finiteRandomMatrixImageDiameter A hrowsm T
  have hdiamInt : Integrable (finiteRandomMatrixImageDiameter A T) μ := by
    refine ((integrable_const
      (Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T)).add hFint).mono'
      hdiamMeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (finiteRandomMatrixImageDiameter_nonneg A T ω)]
    simpa [D, F] using finiteRandomMatrixImageDiameter_le A T hT ω
  have hmono :
      (∫ ω, finiteRandomMatrixImageDiameter A T ω ∂μ) ≤
        ∫ ω, (Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
          F ω) ∂μ := by
    apply integral_mono hdiamInt
      ((integrable_const
        (Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T)).add hFint)
    intro ω
    simpa [D, F] using finiteRandomMatrixImageDiameter_le A T hT ω
  have hmain := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D hD
  have hwidth := HDP.Chapter7.gaussianComplexity_difference T hT
  calc
    (∫ ω, finiteRandomMatrixImageDiameter A T ω ∂μ) ≤
        ∫ ω, (Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
          F ω) ∂μ := hmono
    _ = Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
        ∫ ω, F ω ∂μ := by
      rw [integral_add (integrable_const _) hFint]
      simp [F]
    _ ≤ Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
        matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianComplexity D := by
      simpa [F] using
        add_le_add_left hmain
          (Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T)
    _ = Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
        randomProjectionDiameterConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T := by
      rw [hwidth]
      simp [randomProjectionDiameterConstant]
      ring

/-- Diameter after applying the source's scaled projection `A / sqrt n`.

**Lean implementation helper.** -/
def finiteSubGaussianProjectionDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * finiteRandomMatrixImageDiameter A T ω

/-- Exact finite form with Gaussian width divided
by `sqrt n`. Lemma `gaussianWidth_div_sqrt_le_sphericalWidth` below converts
this to the printed spherical-width notation.

**Book Proposition 9.2.1.** -/
theorem theorem_9_2_1_randomProjectionSizes_finite
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteSubGaussianProjectionDiameter A T ω ∂μ) ≤
      Real.sqrt ((m : ℝ) / n) *
          HDP.Chapter7.finiteEuclideanDiameter T +
        randomProjectionDiameterConstant * K ^ 2 *
          (HDP.Chapter7.gaussianWidth T / Real.sqrt n) := by
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hmain := randomMatrixImageDiameter_expectation hm A hrowsm hsub
    hiso hindep hfinite hK hpsi T hT
  have hscale : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr hsqrtn.le
  calc
    (∫ ω, finiteSubGaussianProjectionDiameter A T ω ∂μ) =
        (Real.sqrt n)⁻¹ *
          ∫ ω, finiteRandomMatrixImageDiameter A T ω ∂μ := by
      change (∫ ω, (Real.sqrt n)⁻¹ *
        finiteRandomMatrixImageDiameter A T ω ∂μ) = _
      rw [integral_const_mul]
    _ ≤ (Real.sqrt n)⁻¹ *
        (Real.sqrt m * HDP.Chapter7.finiteEuclideanDiameter T +
          randomProjectionDiameterConstant * K ^ 2 *
            HDP.Chapter7.gaussianWidth T) :=
      mul_le_mul_of_nonneg_left hmain hscale
    _ = Real.sqrt ((m : ℝ) / n) *
          HDP.Chapter7.finiteEuclideanDiameter T +
        randomProjectionDiameterConstant * K ^ 2 *
          (HDP.Chapter7.gaussianWidth T / Real.sqrt n) := by
      rw [Real.sqrt_div (by positivity)]
      field_simp [hsqrtn.ne']

/-- Gaussian width divided by `sqrt n` is at most spherical width.

**Lean implementation helper.** -/
theorem gaussianWidth_div_sqrt_le_sphericalWidth {n : ℕ} (hn : 0 < n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    HDP.Chapter7.gaussianWidth T / Real.sqrt n ≤
      HDP.Chapter7.sphericalWidth T := by
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsw : 0 ≤ HDP.Chapter7.sphericalWidth T :=
    HDP.Chapter7.sphericalWidth_nonneg T hT hn
  obtain ⟨C, hC, hrad⟩ := HDP.Chapter7.gaussianRadialMean_bounds
  have hradle := (hrad hn).2
  have hpolar :=
    HDP.Chapter7.gaussianWidth_eq_radialMean_mul_sphericalWidth T hT hn
  rw [hpolar]
  calc
    HDP.Chapter7.gaussianRadialMean n *
        HDP.Chapter7.sphericalWidth T / Real.sqrt n =
      (HDP.Chapter7.gaussianRadialMean n / Real.sqrt n) *
        HDP.Chapter7.sphericalWidth T := by ring
    _ ≤ 1 * HDP.Chapter7.sphericalWidth T := by
      gcongr
      exact (div_le_one hsqrtn).2 hradle
    _ = HDP.Chapter7.sphericalWidth T := one_mul _

/-- Printed spherical-width form of Proposition 9.2.1.

**Book Proposition 9.2.1.** -/
theorem theorem_9_2_1_randomProjectionSizes_spherical_finite
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteSubGaussianProjectionDiameter A T ω ∂μ) ≤
      Real.sqrt ((m : ℝ) / n) *
          HDP.Chapter7.finiteEuclideanDiameter T +
        randomProjectionDiameterConstant * K ^ 2 *
          HDP.Chapter7.sphericalWidth T := by
  have hmain := theorem_9_2_1_randomProjectionSizes_finite hm hn A hrowsm hsub
    hiso hindep hfinite hK hpsi T hT
  have hwidth := mul_le_mul_of_nonneg_left
    (gaussianWidth_div_sqrt_le_sphericalWidth hn T hT)
    (mul_nonneg randomProjectionDiameterConstant_pos.le (sq_nonneg K))
  exact hmain.trans (add_le_add (le_refl _) hwidth)

/-! ### Arbitrary bounded-set envelope form -/

/-- Extended envelope of the expected diameter of the scaled random image,
taken over all nonempty finite subfamilies of an arbitrary set.

**Lean implementation helper.** -/
def subGaussianProjectionDiameterExpectationEnvelope {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal
      (∫ ω, finiteSubGaussianProjectionDiameter A F ω ∂μ)

/-- The printed spherical width of an arbitrary set, interpreted safely as
the extended supremum of the finite spherical widths.

**Lean implementation helper.** -/
def sphericalWidthEnvelope {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (_hF : F.Nonempty),
    ENNReal.ofReal (HDP.Chapter7.sphericalWidth F)

/-- The spherical width of a finite set is bounded by its Euclidean radius.

**Lean implementation helper.** -/
theorem sphericalWidth_le_finiteRadius {n : ℕ} (hn : 0 < n)
    (F : Finset (EuclideanSpace ℝ (Fin n))) :
    HDP.Chapter7.sphericalWidth F ≤ HDP.Chapter7.finiteRadius F := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  calc
    HDP.Chapter7.sphericalWidth F =
        ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          HDP.Chapter7.finiteGaussianSupport F θ
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := rfl
    _ ≤ ∫ _θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          HDP.Chapter7.finiteRadius F
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
      apply integral_mono
        (HDP.Chapter7.integrable_finiteGaussianSupport_unitSphere F hn)
        (integrable_const _)
      intro θ
      exact (le_abs_self _).trans
        (HDP.Chapter7.abs_finiteGaussianSupport_unitSphere_le F θ)
    _ = HDP.Chapter7.finiteRadius F := by simp

/-- A finite subfamily has no larger Euclidean diameter than its bounded
ambient set.

**Lean implementation helper.** -/
theorem finiteEuclideanDiameter_le_setDiameter {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T) :
    HDP.Chapter7.finiteEuclideanDiameter F ≤ Metric.diam T := by
  rw [HDP.Chapter7.finiteEuclideanDiameter_eq_sup' F hF]
  apply Finset.sup'_le
  intro p hp
  have hp' := Finset.mem_product.mp hp
  simpa [dist_eq_norm] using
    Metric.dist_le_diam_of_mem hTb (hFT hp'.1) (hFT hp'.2)

/-- A finite spherical width is one of the terms in the arbitrary-set
spherical-width envelope.

**Lean implementation helper.** -/
theorem ofReal_sphericalWidth_le_sphericalWidthEnvelope {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
    (hF : F.Nonempty) :
    ENNReal.ofReal (HDP.Chapter7.sphericalWidth F) ≤
      sphericalWidthEnvelope T := by
  unfold sphericalWidthEnvelope
  exact le_iSup_of_le F
    (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))

/-- For a nonempty bounded set the spherical-width envelope is a finite
extended real, so the printed right-hand side is nonvacuous.

**Lean implementation helper.** -/
theorem sphericalWidthEnvelope_ne_top_of_isBounded {n : ℕ} (hn : 0 < n)
    {T : Set (EuclideanSpace ℝ (Fin n))} (_hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    sphericalWidthEnvelope T ≠ ⊤ := by
  obtain ⟨R, hTR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hTb
  have hEnvelope : sphericalWidthEnvelope T ≤ ENNReal.ofReal R := by
    unfold sphericalWidthEnvelope
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    have hRadius : HDP.Chapter7.finiteRadius F ≤ R := by
      rw [HDP.Chapter7.finiteRadius_eq_sup' F hF]
      apply Finset.sup'_le
      intro x hx
      simpa [Metric.mem_closedBall, dist_zero_right] using
        hTR (hFT hx)
    exact ENNReal.ofReal_le_ofReal
      ((sphericalWidth_le_finiteRadius hn F).trans hRadius)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEnvelope

/-- A subgaussian projection approximately preserves all pairwise distances in a bounded set, with width-dependent additive error. Arbitrary bounded-set form. The left-hand
side is the safe finite-subfamily expectation envelope, and the last term is
the printed spherical-width envelope.

**Book Proposition 9.2.1.** -/
theorem theorem_9_2_1_randomProjectionSizes
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (_hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    subGaussianProjectionDiameterExpectationEnvelope (μ := μ) A T ≤
      ENNReal.ofReal (Real.sqrt ((m : ℝ) / n)) *
          ENNReal.ofReal (Metric.diam T) +
        ENNReal.ofReal (randomProjectionDiameterConstant * K ^ 2) *
          sphericalWidthEnvelope T := by
  unfold subGaussianProjectionDiameterExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  have hmain := theorem_9_2_1_randomProjectionSizes_spherical_finite
    hm hn A hrowsm hsub hiso hindep hfinite hK hpsi F hF
  have hsqrt : 0 ≤ Real.sqrt ((m : ℝ) / n) := Real.sqrt_nonneg _
  have hdiamF : 0 ≤ HDP.Chapter7.finiteEuclideanDiameter F :=
    HDP.Chapter7.finiteEuclideanDiameter_nonneg F
  have hcoef : 0 ≤ randomProjectionDiameterConstant * K ^ 2 :=
    mul_nonneg randomProjectionDiameterConstant_pos.le (sq_nonneg K)
  have hwidthF : 0 ≤ HDP.Chapter7.sphericalWidth F :=
    HDP.Chapter7.sphericalWidth_nonneg F hF hn
  have hdiam := finiteEuclideanDiameter_le_setDiameter hTb F hF hFT
  have hwidth := ofReal_sphericalWidth_le_sphericalWidthEnvelope F hFT hF
  calc
    ENNReal.ofReal
        (∫ ω, finiteSubGaussianProjectionDiameter A F ω ∂μ) ≤
        ENNReal.ofReal
          (Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter F +
            randomProjectionDiameterConstant * K ^ 2 *
              HDP.Chapter7.sphericalWidth F) :=
      ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (Real.sqrt ((m : ℝ) / n)) *
          ENNReal.ofReal (HDP.Chapter7.finiteEuclideanDiameter F) +
        ENNReal.ofReal (randomProjectionDiameterConstant * K ^ 2) *
          ENNReal.ofReal (HDP.Chapter7.sphericalWidth F) := by
      rw [ENNReal.ofReal_add (mul_nonneg hsqrt hdiamF)
          (mul_nonneg hcoef hwidthF),
        ENNReal.ofReal_mul hsqrt, ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (Real.sqrt ((m : ℝ) / n)) *
          ENNReal.ofReal (Metric.diam T) +
        ENNReal.ofReal (randomProjectionDiameterConstant * K ^ 2) *
          sphericalWidthEnvelope T := by
      exact add_le_add
        (mul_right_mono (ENNReal.ofReal_le_ofReal hdiam))
        (mul_right_mono hwidth)

/-- The expected-diameter envelope is finite under the source hypotheses.

**Lean implementation helper.** -/
theorem subGaussianProjectionDiameterExpectationEnvelope_ne_top_of_isBounded
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    subGaussianProjectionDiameterExpectationEnvelope (μ := μ) A T ≠ ⊤ := by
  have hwidth := sphericalWidthEnvelope_ne_top_of_isBounded hn hT hTb
  have hrhs :
      ENNReal.ofReal (Real.sqrt ((m : ℝ) / n)) *
          ENNReal.ofReal (Metric.diam T) +
        ENNReal.ofReal (randomProjectionDiameterConstant * K ^ 2) *
          sphericalWidthEnvelope T ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwidth⟩
  exact ne_top_of_le_ne_top hrhs
    (theorem_9_2_1_randomProjectionSizes hm hn A hrowsm hsub hiso
      hindep hfinite hK hpsi T hT hTb)

end

end HDP.Chapter9

end Source_04_RandomProjectionSizes

/-! ## Material formerly in `05_LowRankCovarianceEstimation.lean` -/

section Source_05_LowRankCovarianceEstimation

/-!
# Book Chapter 9, §9.2.3: covariance estimation

The factorized proof engines use a rectangular matrix `B`, so their
population second moment is `B Bᵀ` and no inverse whitening map is hidden.
The source-facing APIs additionally accept arbitrary rows satisfying the
relative ψ₂/L² hypothesis.  They derive positive semidefiniteness from the
common second moment, whiten only its strictly positive eigenspace, and map
back almost everywhere.  Consequently singular covariance matrices,
including zero, are covered without an invertibility assumption.  The
quadratic-process estimate from Exercise 9.3 is separately available in
module 03 and is the sharp effective-rank engine used by finite ellipsoid
exhaustions.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The population second moment in the singular-safe factor model.

**Lean implementation helper.** -/
def factorPopulationSecondMoment {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  B * B.transpose

/-- The empirical second moment of the factorized observations.

**Lean implementation helper.** -/
def factorSampleSecondMoment {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  HDP.normalizedGram m (A * B.transpose)

/-- Explicit constant used for the expectation form of Theorem 9.2.2.

**Book Theorem 9.2.2.** -/
def lowRankCovarianceExpectationConstant : ℝ :=
  HDP.Chapter4.gramExpectationConstant

/-- The constant in the low-rank covariance expectation bound is strictly positive.

**Lean implementation helper.** -/
theorem lowRankCovarianceExpectationConstant_pos :
    0 < lowRankCovarianceExpectationConstant :=
  HDP.Chapter4.gramExpectationConstant_pos

/-- A real number at least one has square no larger than its fourth power.

**Lean implementation helper.** -/
private lemma sq_le_fourth_of_one_le {K : ℝ} (hK : 1 ≤ K) :
    K ^ 2 ≤ K ^ 4 := by
  have hKsq : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hprod := mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hKsq)
  nlinarith

/-- The rows of `D` share the (uncentered) second-moment matrix `Sigma`. This is the direct row-model hypothesis in Book Theorem 9.2.2.

**Book Theorem 9.2.2.** -/
def CommonSecondMoment {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω) (μ : Measure Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, HDP.secondMomentMatrix (HDP.randomMatrixRow D i) μ = Sigma

/-- Products of two coordinates of a measurable subgaussian row are
integrable.

**Lean implementation helper.** -/
theorem row_coordinate_product_integrable [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : D.AEMeasurableRows μ) (hsub : D.SubGaussianRows μ)
    (i : Fin m) (j k : Fin n) :
    Integrable (fun ω => D ω i j * D ω i k) μ := by
  let ej : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ j
  let ek : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ k
  have hj : MemLp (fun ω => D ω i j) 2 μ := by
    have h := (hsub.marginal i ej).memLp
      (hrowsm.aemeasurable_marginal i ej) (p := (2 : ℝ)) (by norm_num)
    simpa [ej, HDP.inner_randomMatrixRow] using h
  have hk : MemLp (fun ω => D ω i k) 2 μ := by
    have h := (hsub.marginal i ek).memLp
      (hrowsm.aemeasurable_marginal i ek) (p := (2 : ℝ)) (by norm_num)
    simpa [ek, HDP.inner_randomMatrixRow] using h
  exact MemLp.integrable_mul (p := 2) (q := 2) hj hk

/-- Polarized form of a common row second moment.

**Lean implementation helper.** -/
theorem commonSecondMoment_bilinear [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hrowsm : D.AEMeasurableRows μ) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma)
    (i : Fin m) (x y : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (HDP.randomMatrixRow D i ω) x *
        inner ℝ (HDP.randomMatrixRow D i ω) y ∂μ) =
      inner ℝ (Sigma.toEuclideanLin x) y := by
  have hfun : (fun ω => inner ℝ (HDP.randomMatrixRow D i ω) x *
      inner ℝ (HDP.randomMatrixRow D i ω) y) =
      fun ω => ∑ j : Fin n, ∑ k : Fin n,
        (x j * y k) * (D ω i j * D ω i k) := by
    funext ω
    rw [HDP.inner_randomMatrixRow, HDP.inner_randomMatrixRow]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hterm (j k : Fin n) : Integrable
      (fun ω => (x j * y k) * (D ω i j * D ω i k)) μ :=
    (row_coordinate_product_integrable D hrowsm hsub i j k).const_mul _
  have hsym : Sigma.transpose = Sigma := by
    rw [← hsecond i]
    exact HDP.secondMomentMatrix_transpose (HDP.randomMatrixRow D i)
  rw [hfun]
  calc
    (∫ ω, ∑ j : Fin n, ∑ k : Fin n,
        (x j * y k) * (D ω i j * D ω i k) ∂μ) =
        ∑ j : Fin n, ∫ ω, ∑ k : Fin n,
          (x j * y k) * (D ω i j * D ω i k) ∂μ := by
      rw [integral_finsetSum]
      intro j _
      exact integrable_finsetSum _ fun k _ => hterm j k
    _ = ∑ j : Fin n, ∑ k : Fin n,
        ∫ ω, (x j * y k) * (D ω i j * D ω i k) ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum]
      intro k _
      exact hterm j k
    _ = ∑ j : Fin n, ∑ k : Fin n, (x j * y k) * Sigma j k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_const_mul]
      have he := congrFun (congrFun (hsecond i) j) k
      simpa [HDP.secondMomentMatrix] using
        congrArg (fun z => (x j * y k) * z) he
    _ = inner ℝ (Sigma.toEuclideanLin x) y := by
      rw [PiLp.inner_apply]
      simp only [Real.inner_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      have hjk := congrFun (congrFun hsym k) j
      simp only [Matrix.transpose_apply] at hjk
      rw [← hjk]
      ring

/-- A common second-moment matrix of measurable subgaussian rows is positive
semidefinite.

**Lean implementation helper.** -/
theorem commonSecondMoment_posSemidef [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hrowsm : D.AEMeasurableRows μ) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma) (i : Fin m) :
    Sigma.PosSemidef := by
  have hsym : Sigma.transpose = Sigma := by
    rw [← hsecond i]
    exact HDP.secondMomentMatrix_transpose (HDP.randomMatrixRow D i)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa [Matrix.IsHermitian] using hsym
  · intro x
    let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
    have hbil := commonSecondMoment_bilinear D Sigma hrowsm hsub hsecond i u u
    have hnonneg : 0 ≤ ∫ ω,
        inner ℝ (HDP.randomMatrixRow D i ω) u ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    have hinner : inner ℝ (Sigma.toEuclideanLin u) u =
        x ⬝ᵥ Sigma.mulVec x := by
      simp [u, PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct]
    have hxnonneg : 0 ≤ x ⬝ᵥ Sigma.mulVec x := by
      rw [← hinner, ← hbil]
      simpa [pow_two] using hnonneg
    simpa using hxnonneg

/-- Indices of the strictly positive eigenvalues of a positive semidefinite
second-moment matrix. -/
abbrev covariancePositiveIndex {n : ℕ} (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hSigma : Sigma.PosSemidef) :=
  {j : Fin n // 0 < hSigma.1.eigenvalues j}

/-- Dimension of the strictly positive spectral subspace.

**Lean implementation helper.** -/
noncomputable def covarianceLatentDim {n : ℕ} (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hSigma : Sigma.PosSemidef) : ℕ :=
  Fintype.card (covariancePositiveIndex Sigma hSigma)

/-- Canonical finite indexing of the strictly positive spectral subspace.

**Lean implementation helper.** -/
noncomputable def covariancePositiveEquiv {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef) :
    covariancePositiveIndex Sigma hSigma ≃ Fin (covarianceLatentDim Sigma hSigma) :=
  Fintype.equivFin _

/-- Rectangular spectral square root of a positive semidefinite matrix, with
zero eigenvalue directions removed.

**Lean implementation helper.** -/
noncomputable def covarianceEigenFactor {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef) :
    Matrix (Fin n) (Fin (covarianceLatentDim Sigma hSigma)) ℝ :=
  fun i q =>
    let j := (covariancePositiveEquiv Sigma hSigma).symm q
    Real.sqrt (hSigma.1.eigenvalues j.1) *
      hSigma.1.eigenvectorBasis j.1 i

/-- Entrywise real spectral expansion of a positive semidefinite matrix.

**Lean implementation helper.** -/
theorem posSemidef_spectral_entry {n : ℕ}
    {Sigma : Matrix (Fin n) (Fin n) ℝ} (hSigma : Sigma.PosSemidef)
    (i k : Fin n) :
    Sigma i k = ∑ j : Fin n, hSigma.1.eigenvalues j *
      hSigma.1.eigenvectorBasis j i * hSigma.1.eigenvectorBasis j k := by
  have hs := congrFun (congrFun hSigma.1.spectral_theorem i) k
  simpa [Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.diagonal_apply,
    mul_comm, mul_left_comm, mul_assoc] using hs

/-- The rectangular positive-spectral factor reconstructs the original
matrix, including in the singular case.

**Lean implementation helper.** -/
theorem covarianceEigenFactor_mul_transpose {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef) :
    covarianceEigenFactor Sigma hSigma *
        (covarianceEigenFactor Sigma hSigma).transpose = Sigma := by
  ext i k
  rw [Matrix.mul_apply, posSemidef_spectral_entry hSigma]
  simp only [Matrix.transpose_apply, covarianceEigenFactor]
  let e := covariancePositiveEquiv Sigma hSigma
  change (∑ q : Fin (covarianceLatentDim Sigma hSigma),
      Real.sqrt (hSigma.1.eigenvalues (e.symm q).1) *
        hSigma.1.eigenvectorBasis (e.symm q).1 i *
          (Real.sqrt (hSigma.1.eigenvalues (e.symm q).1) *
            hSigma.1.eigenvectorBasis (e.symm q).1 k)) = _
  let f : covariancePositiveIndex Sigma hSigma → ℝ := fun j =>
    Real.sqrt (hSigma.1.eigenvalues j.1) *
      hSigma.1.eigenvectorBasis j.1 i *
        (Real.sqrt (hSigma.1.eigenvalues j.1) *
          hSigma.1.eigenvectorBasis j.1 k)
  have hsum : (∑ q : Fin (covarianceLatentDim Sigma hSigma), f (e.symm q)) =
      ∑ j : covariancePositiveIndex Sigma hSigma, f j :=
    e.symm.sum_comp f
  change (∑ q : Fin (covarianceLatentDim Sigma hSigma), f (e.symm q)) = _
  rw [hsum]
  let g : Fin n → ℝ := fun j => hSigma.1.eigenvalues j *
    hSigma.1.eigenvectorBasis j i * hSigma.1.eigenvectorBasis j k
  have hfg : (∑ j : covariancePositiveIndex Sigma hSigma, f j) =
      ∑ j : covariancePositiveIndex Sigma hSigma, g j.1 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : 0 ≤ hSigma.1.eigenvalues j.1 :=
      hSigma.eigenvalues_nonneg j.1
    dsimp [f, g]
    calc
      Real.sqrt (hSigma.1.eigenvalues j.1) *
          hSigma.1.eigenvectorBasis j.1 i *
          (Real.sqrt (hSigma.1.eigenvalues j.1) *
            hSigma.1.eigenvectorBasis j.1 k) =
          (Real.sqrt (hSigma.1.eigenvalues j.1) *
            Real.sqrt (hSigma.1.eigenvalues j.1)) *
            hSigma.1.eigenvectorBasis j.1 i *
              hSigma.1.eigenvectorBasis j.1 k := by ring
      _ = hSigma.1.eigenvalues j.1 *
            hSigma.1.eigenvectorBasis j.1 i *
              hSigma.1.eigenvectorBasis j.1 k := by
        rw [Real.mul_self_sqrt hj]
  rw [hfg]
  have hzero : (∑ j : {j : Fin n // ¬ 0 < hSigma.1.eigenvalues j},
      g j.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj0 : hSigma.1.eigenvalues j.1 = 0 := by
      have hjnonneg := hSigma.eigenvalues_nonneg j.1
      exact le_antisymm (le_of_not_gt j.2) hjnonneg
    simp [g, hj0]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun j : Fin n => 0 < hSigma.1.eigenvalues j) g
  rw [hzero, add_zero] at hsplit
  exact hsplit

/-- The source's relative subgaussian hypothesis
`‖⟨Dᵢ,x⟩‖_{ψ₂} ≤ K (E⟨Dᵢ,x⟩²)^{1/2}`.

**Lean implementation helper.** -/
def RelativeRowPsi2Bound {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω) (μ : Measure Ω) (K : ℝ) : Prop :=
  ∀ i x, HDP.psi2Norm
      (fun ω => inner ℝ (HDP.randomMatrixRow D i ω) x) μ ≤
    K * Real.sqrt (∫ ω,
      inner ℝ (HDP.randomMatrixRow D i ω) x ^ 2 ∂μ)

/-- Whiten each row only along the strictly positive eigenspace of its common
second moment.

**Lean implementation helper.** -/
noncomputable def covarianceWhitenedSample {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef) :
    HDP.RandomMatrix (Fin m) (Fin (covarianceLatentDim Sigma hSigma)) Ω :=
  fun ω i q =>
    let j := (covariancePositiveEquiv Sigma hSigma).symm q
    inner ℝ (HDP.randomMatrixRow D i ω)
      (hSigma.1.eigenvectorBasis j.1) /
        Real.sqrt (hSigma.1.eigenvalues j.1)

/-- The ambient vector whose original marginal equals a marginal of the
positive-eigenspace-whitened row.

**Lean implementation helper.** -/
noncomputable def covarianceWhiteningLift {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (z : EuclideanSpace ℝ (Fin (covarianceLatentDim Sigma hSigma))) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ q, (z q / Real.sqrt
      (hSigma.1.eigenvalues ((covariancePositiveEquiv Sigma hSigma).symm q).1)) •
    hSigma.1.eigenvectorBasis
      ((covariancePositiveEquiv Sigma hSigma).symm q).1

/-- Marginals of the whitened sample are original-row marginals composed with
the whitening lift.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_marginal {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (i : Fin m) (z : EuclideanSpace ℝ
      (Fin (covarianceLatentDim Sigma hSigma))) :
    (fun ω => inner ℝ
      (HDP.randomMatrixRow (covarianceWhitenedSample D Sigma hSigma) i ω) z) =
      fun ω => inner ℝ (HDP.randomMatrixRow D i ω)
        (covarianceWhiteningLift Sigma hSigma z) := by
  funext ω
  rw [HDP.inner_randomMatrixRow]
  simp only [covarianceWhitenedSample]
  rw [covarianceWhiteningLift, inner_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [inner_smul_right]
  ring

/-- Positive-eigenspace whitening preserves row measurability.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_measurableRows {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hrowsm : D.MeasurableRows) :
    (covarianceWhitenedSample D Sigma hSigma).MeasurableRows := by
  apply HDP.RandomMatrix.MeasurableEntries.measurable_rows
  intro i q
  let j := (covariancePositiveEquiv Sigma hSigma).symm q
  simpa [covarianceWhitenedSample, j] using
    (hrowsm.measurable_marginal i
      (hSigma.1.eigenvectorBasis j.1)).div_const
        (Real.sqrt (hSigma.1.eigenvalues j.1))

/-- Positive-eigenspace whitening preserves row subgaussianity.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_subGaussianRows {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hsub : D.SubGaussianRows μ) :
    (covarianceWhitenedSample D Sigma hSigma).SubGaussianRows μ := by
  intro i z
  rw [covarianceWhitenedSample_marginal]
  exact hsub.marginal i (covarianceWhiteningLift Sigma hSigma z)

/-- The positive-eigenspace-whitened rows are isotropic, even when the
original common second moment is singular.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_isotropicRows [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hrowsm : D.AEMeasurableRows μ) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma) :
    (covarianceWhitenedSample D Sigma hSigma).IsotropicRows μ := by
  intro i
  apply HDP.isIsotropic_iff.mpr
  intro q p
  let jq := (covariancePositiveEquiv Sigma hSigma).symm q
  let jp := (covariancePositiveEquiv Sigma hSigma).symm p
  have hlq : 0 < hSigma.1.eigenvalues jq.1 := jq.2
  have hlp : 0 < hSigma.1.eigenvalues jp.1 := jp.2
  have hqroot : Real.sqrt (hSigma.1.eigenvalues jq.1) ≠ 0 :=
    (Real.sqrt_pos.2 hlq).ne'
  have hproot : Real.sqrt (hSigma.1.eigenvalues jp.1) ≠ 0 :=
    (Real.sqrt_pos.2 hlp).ne'
  have hbil := commonSecondMoment_bilinear D Sigma hrowsm hsub hsecond i
    (hSigma.1.eigenvectorBasis jq.1) (hSigma.1.eigenvectorBasis jp.1)
  have heig := hSigma.1.mulVec_eigenvectorBasis jq.1
  have hinner : inner ℝ
      (Sigma.toEuclideanLin (hSigma.1.eigenvectorBasis jq.1))
      (hSigma.1.eigenvectorBasis jp.1) =
      hSigma.1.eigenvalues jq.1 * (if jq.1 = jp.1 then 1 else 0) := by
    rw [show Sigma.toEuclideanLin (hSigma.1.eigenvectorBasis jq.1) =
        hSigma.1.eigenvalues jq.1 • hSigma.1.eigenvectorBasis jq.1 by
      apply PiLp.ext
      intro k
      simpa [Matrix.toLpLin_apply] using congrFun heig k]
    rw [inner_smul_left, hSigma.1.eigenvectorBasis.inner_eq_ite]
    simp
  rw [hinner] at hbil
  simp only [HDP.randomMatrixRow_apply, covarianceWhitenedSample]
  rw [show (fun ω =>
      (inner ℝ (HDP.randomMatrixRow D i ω) (hSigma.1.eigenvectorBasis jq.1) /
          Real.sqrt (hSigma.1.eigenvalues jq.1)) *
      (inner ℝ (HDP.randomMatrixRow D i ω) (hSigma.1.eigenvectorBasis jp.1) /
          Real.sqrt (hSigma.1.eigenvalues jp.1))) =
      fun ω => (Real.sqrt (hSigma.1.eigenvalues jq.1) *
          Real.sqrt (hSigma.1.eigenvalues jp.1))⁻¹ *
        (inner ℝ (HDP.randomMatrixRow D i ω) (hSigma.1.eigenvectorBasis jq.1) *
          inner ℝ (HDP.randomMatrixRow D i ω) (hSigma.1.eigenvectorBasis jp.1)) by
    funext ω; field_simp]
  rw [integral_const_mul, hbil]
  by_cases hqp : q = p
  · subst p
    simp [jq, jp, Real.mul_self_sqrt hlq.le, hlq.ne']
  · have hjneq : jq.1 ≠ jp.1 := by
      intro h
      apply hqp
      exact (covariancePositiveEquiv Sigma hSigma).symm.injective
        (Subtype.ext h)
    simp [hqp, hjneq]

/-- Applying the deterministic whitening map rowwise preserves mutual row
independence.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_independentRows {m n : ℕ}
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hindep : D.IndependentRows μ) :
    (covarianceWhitenedSample D Sigma hSigma).IndependentRows μ := by
  let L : Fin m → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (covarianceLatentDim Sigma hSigma)) :=
    fun _ x => WithLp.toLp 2 fun q =>
      let j := (covariancePositiveEquiv Sigma hSigma).symm q
      inner ℝ x (hSigma.1.eigenvectorBasis j.1) /
        Real.sqrt (hSigma.1.eigenvalues j.1)
  have hcomp := hindep.comp L (fun _ => by
    dsimp [L]
    fun_prop)
  have heq : (fun i => L i ∘ HDP.randomMatrixRow D i) =
      fun i => HDP.randomMatrixRow (covarianceWhitenedSample D Sigma hSigma) i := by
    funext i ω
    apply PiLp.ext
    intro q
    rfl
  change iIndepFun
    (fun i => HDP.randomMatrixRow (covarianceWhitenedSample D Sigma hSigma) i) μ
  rw [← heq]
  exact hcomp

/-- The original marginal associated with a whitening lift has second moment
equal to the squared Euclidean norm in latent coordinates.

**Lean implementation helper.** -/
theorem covarianceWhiteningLift_secondMoment [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hrowsm : D.MeasurableRows) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma)
    (i : Fin m) (z : EuclideanSpace ℝ
      (Fin (covarianceLatentDim Sigma hSigma))) :
    (∫ ω, inner ℝ (HDP.randomMatrixRow D i ω)
        (covarianceWhiteningLift Sigma hSigma z) ^ 2 ∂μ) = ‖z‖ ^ 2 := by
  let A := covarianceWhitenedSample D Sigma hSigma
  have hm := covarianceWhitenedSample_measurableRows D Sigma hSigma hrowsm
  have hs := covarianceWhitenedSample_subGaussianRows D Sigma hSigma hsub
  have hi := covarianceWhitenedSample_isotropicRows D Sigma hSigma
    (hrowsm.aemeasurable_rows μ) hsub hsecond
  have hbase := HDP.Chapter4.isotropic_row_marginal_secondMoment
    A (hm.aemeasurable_rows μ) hs hi i z
  have hfun := covarianceWhitenedSample_marginal D Sigma hSigma i z
  calc
    (∫ ω, inner ℝ (HDP.randomMatrixRow D i ω)
        (covarianceWhiteningLift Sigma hSigma z) ^ 2 ∂μ) =
        ∫ ω, inner ℝ (HDP.randomMatrixRow A i ω) z ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [congrFun hfun ω]
    _ = ‖z‖ ^ 2 := hbase

/-- The relative ψ₂ hypothesis makes the whitened row ψ₂ suprema finite.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_rowPsi2Finite [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hrowsm : D.MeasurableRows) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma)
    {K : ℝ} (hrelative : RelativeRowPsi2Bound D μ K) :
    (covarianceWhitenedSample D Sigma hSigma).RowPsi2Finite μ := by
  intro i
  refine ⟨K, ?_⟩
  rintro r ⟨z, hz, rfl⟩
  rw [covarianceWhitenedSample_marginal]
  have h := hrelative i (covarianceWhiteningLift Sigma hSigma z)
  rw [covarianceWhiteningLift_secondMoment D Sigma hSigma hrowsm hsub
    hsecond i z, hz, one_pow, Real.sqrt_one, mul_one] at h
  exact h

/-- The source relative ψ₂ constant is also a uniform ψ₂ bound for the
whitened rows.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_rowPsi2Bound [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hrowsm : D.MeasurableRows) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma)
    {K : ℝ} (hK : 0 ≤ K) (hrelative : RelativeRowPsi2Bound D μ K) :
    (covarianceWhitenedSample D Sigma hSigma).RowPsi2Bound μ K := by
  intro i
  unfold HDP.psi2NormVector
  apply Real.sSup_le
  · rintro r ⟨z, hz, rfl⟩
    rw [covarianceWhitenedSample_marginal]
    have h := hrelative i (covarianceWhiteningLift Sigma hSigma z)
    rw [covarianceWhiteningLift_secondMoment D Sigma hSigma hrowsm hsub
      hsecond i z, hz, one_pow, Real.sqrt_one, mul_one] at h
    exact h
  · exact hK

/-- Singular-safe factorization of the original sample: the whitened sample
times the spectral factor transpose agrees with `D` almost everywhere.

**Lean implementation helper.** -/
theorem covarianceWhitenedSample_mul_factor_ae [IsProbabilityMeasure μ]
    {m n : ℕ} (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (hSigma : Sigma.PosSemidef)
    (hrowsm : D.MeasurableRows) (hsub : D.SubGaussianRows μ)
    (hsecond : CommonSecondMoment D μ Sigma) :
    (fun ω => covarianceWhitenedSample D Sigma hSigma ω *
        (covarianceEigenFactor Sigma hSigma).transpose) =ᵐ[μ] D := by
  have hzero (i : Fin m) (j : Fin n)
      (hj : hSigma.1.eigenvalues j = 0) :
      ∀ᵐ ω ∂μ, inner ℝ (HDP.randomMatrixRow D i ω)
        (hSigma.1.eigenvectorBasis j) = 0 := by
    let X : Ω → ℝ := fun ω => inner ℝ (HDP.randomMatrixRow D i ω)
      (hSigma.1.eigenvectorBasis j)
    have hXmem : MemLp X 2 μ := by
      have hraw := (hsub.marginal i (hSigma.1.eigenvectorBasis j)).memLp
        (hrowsm.aemeasurable_rows μ |>.aemeasurable_marginal i
          (hSigma.1.eigenvectorBasis j)) (p := (2 : ℝ)) (by norm_num)
      simpa [X] using hraw
    have hint : Integrable (fun ω => X ω ^ 2) μ := hXmem.integrable_sq
    have hbil := commonSecondMoment_bilinear D Sigma
      (hrowsm.aemeasurable_rows μ) hsub hsecond i
      (hSigma.1.eigenvectorBasis j) (hSigma.1.eigenvectorBasis j)
    have heig := hSigma.1.mulVec_eigenvectorBasis j
    have hinner : inner ℝ
        (Sigma.toEuclideanLin (hSigma.1.eigenvectorBasis j))
        (hSigma.1.eigenvectorBasis j) = hSigma.1.eigenvalues j := by
      rw [show Sigma.toEuclideanLin (hSigma.1.eigenvectorBasis j) =
          hSigma.1.eigenvalues j • hSigma.1.eigenvectorBasis j by
        apply PiLp.ext
        intro k
        simpa [Matrix.toLpLin_apply] using congrFun heig k]
      rw [inner_smul_left,
        hSigma.1.eigenvectorBasis.inner_eq_ite]
      simp
    rw [hinner, hj] at hbil
    have hsq : (fun ω => X ω ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp
        (by simpa [X, pow_two] using hbil)
    filter_upwards [hsq] with ω hω
    have : X ω ^ 2 = 0 := by simpa using hω
    exact (sq_eq_zero_iff.mp this)
  have hall : ∀ᵐ ω ∂μ, ∀ i j,
      hSigma.1.eigenvalues j = 0 →
        inner ℝ (HDP.randomMatrixRow D i ω)
          (hSigma.1.eigenvectorBasis j) = 0 := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    by_cases hj : hSigma.1.eigenvalues j = 0
    · exact (hzero i j hj).mono fun ω hω _ => hω
    · exact Filter.Eventually.of_forall fun ω hzero => (hj hzero).elim
  filter_upwards [hall] with ω hω
  ext i k
  rw [Matrix.mul_apply]
  let e := covariancePositiveEquiv Sigma hSigma
  let b := hSigma.1.eigenvectorBasis
  let x : EuclideanSpace ℝ (Fin n) := HDP.randomMatrixRow D i ω
  let f : covariancePositiveIndex Sigma hSigma → ℝ := fun j =>
    inner ℝ x (b j.1) * b j.1 k
  have hfirst :
      (∑ q : Fin (covarianceLatentDim Sigma hSigma),
        covarianceWhitenedSample D Sigma hSigma ω i q *
          (covarianceEigenFactor Sigma hSigma).transpose q k) =
        ∑ q : Fin (covarianceLatentDim Sigma hSigma), f (e.symm q) := by
    apply Finset.sum_congr rfl
    intro q _
    let j := e.symm q
    have hjroot : Real.sqrt (hSigma.1.eigenvalues j.1) ≠ 0 :=
      (Real.sqrt_pos.2 j.2).ne'
    simp only [covarianceWhitenedSample, covarianceEigenFactor,
      Matrix.transpose_apply]
    dsimp [f, x, b, e, j]
    rw [div_eq_mul_inv]
    calc
      inner ℝ (HDP.randomMatrixRow D i ω)
            (hSigma.1.eigenvectorBasis j.1) *
          (Real.sqrt (hSigma.1.eigenvalues j.1))⁻¹ *
          (Real.sqrt (hSigma.1.eigenvalues j.1) *
            hSigma.1.eigenvectorBasis j.1 k) =
          inner ℝ (HDP.randomMatrixRow D i ω)
            (hSigma.1.eigenvectorBasis j.1) *
          hSigma.1.eigenvectorBasis j.1 k *
            ((Real.sqrt (hSigma.1.eigenvalues j.1))⁻¹ *
              Real.sqrt (hSigma.1.eigenvalues j.1)) := by ring
      _ = inner ℝ (HDP.randomMatrixRow D i ω)
            (hSigma.1.eigenvectorBasis j.1) *
          hSigma.1.eigenvectorBasis j.1 k := by
        rw [inv_mul_cancel₀ hjroot, mul_one]
  rw [hfirst, e.symm.sum_comp]
  let g : Fin n → ℝ := fun j => inner ℝ x (b j) * b j k
  have hfg : (∑ j : covariancePositiveIndex Sigma hSigma, f j) =
      ∑ j : covariancePositiveIndex Sigma hSigma, g j.1 := by
    rfl
  rw [hfg]
  have hcomp : (∑ j : {j : Fin n // ¬ 0 < hSigma.1.eigenvalues j}, g j.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj0 : hSigma.1.eigenvalues j.1 = 0 :=
      le_antisymm (le_of_not_gt j.2) (hSigma.eigenvalues_nonneg j.1)
    have hz := hω i j.1 hj0
    simp [g, x, b, hz]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun j : Fin n => 0 < hSigma.1.eigenvalues j) g
  rw [hcomp, add_zero] at hsplit
  rw [hsplit]
  have hexpand := b.sum_repr' x
  have hk := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z k) hexpand
  simpa [g, x, b, Finset.sum_apply, real_inner_comm] using hk

/-! ## Ellipsoid-net estimates -/

/-- Image of a finite ambient net under the transpose of a covariance
factor. This is the finite ellipsoid used in the proof of Theorem 9.2.2.

**Book Theorem 9.2.2.** -/
def factorEllipsoidNet {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin r)) := by
  classical
  exact N.image B.transpose.toEuclideanLin

/-- The factor ellipsoid net is nonempty.

**Lean implementation helper.** -/
theorem factorEllipsoidNet_nonempty {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ)
    {N : Finset (EuclideanSpace ℝ (Fin n))} (hN : N.Nonempty) :
    (factorEllipsoidNet B N).Nonempty := by
  classical
  simpa [factorEllipsoidNet] using hN.image B.transpose.toEuclideanLin

/-- For the covariance ellipsoid, radius is the square root of operator norm and Gaussian complexity is at most the square root of trace. The ellipsoid-net radius is bounded by the operator norm of its factor.

**Book Section 9.2.3, proof of Theorem 9.2.2.** -/
theorem factorEllipsoidNet_radius_le {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n))) (hN0 : N.Nonempty)
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (N : Set (EuclideanSpace ℝ (Fin n)))) :
    HDP.Chapter7.finiteRadius (factorEllipsoidNet B N) ≤
      HDP.matrixOpNorm B := by
  classical
  let T := factorEllipsoidNet B N
  have hT : T.Nonempty := factorEllipsoidNet_nonempty B hN0
  rw [HDP.Chapter7.finiteRadius_eq_sup' T hT]
  apply Finset.sup'_le
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  calc
    ‖B.transpose.toEuclideanLin x‖ ≤
        HDP.matrixOpNorm B.transpose * ‖x‖ :=
      HDP.Chapter4.matrixOpNorm_apply_le B.transpose x
    _ = HDP.matrixOpNorm B := by
      rw [hN.1 x (by simpa using hx), mul_one,
        HDP.matrixOpNorm_transpose]

/-- The expected squared norm of a fixed matrix applied to a standard Gaussian equals its squared Frobenius norm.

**Lean implementation helper.** -/
private theorem integral_norm_matrix_stdGaussian {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ) :
    (∫ g : EuclideanSpace ℝ (Fin r), ‖B.toEuclideanLin g‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin r))) =
      HDP.matrixFrobeniusNorm B ^ 2 := by
  simp_rw [HDP.Chapter4.norm_toEuclideanLin_sq_eq_sum_rows]
  rw [integral_finsetSum]
  · rw [HDP.matrixFrobeniusNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    let b : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j => B i j)
    have hb := HDP.Chapter8.integral_inner_sq_stdGaussian b
    calc
      (∫ g : EuclideanSpace ℝ (Fin r),
          (∑ j : Fin r, B i j * g j) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin r))) = ‖b‖ ^ 2 := by
        simpa [b, PiLp.inner_apply, Real.inner_apply, mul_comm] using hb
      _ = ∑ j : Fin r, B i j ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  · intro i hi
    let b : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j => B i j)
    have hbmem : MemLp
        (fun g : EuclideanSpace ℝ (Fin r) => inner ℝ b g) 2
        (stdGaussian (EuclideanSpace ℝ (Fin r))) := by
      have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
        MemLp (id : EuclideanSpace ℝ (Fin r) →
          EuclideanSpace ℝ (Fin r)) 2
          (stdGaussian (EuclideanSpace ℝ (Fin r)))).continuousLinearMap_comp
            ((innerSL ℝ) b)
      simpa [Function.comp_def, innerSL_apply_apply] using h
    simpa [b, PiLp.inner_apply, Real.inner_apply, mul_comm] using
      hbmem.integrable_sq

/-- For the covariance ellipsoid, radius is the square root of operator norm and Gaussian complexity is at most the square root of trace. Gaussian complexity of the finite ellipsoid net is at most the
Hilbert--Schmidt norm of the defining factor.

**Book Section 9.2.3, proof of Theorem 9.2.2.** -/
theorem factorEllipsoidNet_gaussianComplexity_le {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n))) (hN0 : N.Nonempty)
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (N : Set (EuclideanSpace ℝ (Fin n)))) :
    HDP.Chapter7.gaussianComplexity (factorEllipsoidNet B N) ≤
      HDP.matrixFrobeniusNorm B := by
  classical
  let T := factorEllipsoidNet B N
  have hT : T.Nonempty := factorEllipsoidNet_nonempty B hN0
  have hpoint (g : EuclideanSpace ℝ (Fin r)) :
      HDP.Chapter7.finiteGaussianAbsSupport T g ≤
        ‖B.toEuclideanLin g‖ := by
    rw [HDP.Chapter7.finiteGaussianAbsSupport_eq_sup' T hT]
    apply Finset.sup'_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxnorm : ‖x‖ = 1 := hN.1 x (by simpa using hx)
    have hadj : inner ℝ g (B.transpose.toEuclideanLin x) =
        inner ℝ (B.toEuclideanLin g) x := by
      rw [← LinearMap.adjoint_inner_left]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hadj]
    calc
      |inner ℝ (B.toEuclideanLin g) x| ≤
          ‖B.toEuclideanLin g‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ = ‖B.toEuclideanLin g‖ := by rw [hxnorm, mul_one]
  have hleftInt : Integrable
      (fun g : EuclideanSpace ℝ (Fin r) =>
        HDP.Chapter7.finiteGaussianAbsSupport T g ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin r))) :=
    (HDP.Chapter7.memLp_two_finiteGaussianAbsSupport T).integrable_sq
  have hrightMem : MemLp (fun g : EuclideanSpace ℝ (Fin r) =>
      B.toEuclideanLin g) 2
      (stdGaussian (EuclideanSpace ℝ (Fin r))) := by
    have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
      MemLp (id : EuclideanSpace ℝ (Fin r) →
        EuclideanSpace ℝ (Fin r)) 2
        (stdGaussian (EuclideanSpace ℝ (Fin r)))).continuousLinearMap_comp
          B.toEuclideanLin.toContinuousLinearMap
    simpa [Function.comp_def] using h
  have hrightInt : Integrable (fun g : EuclideanSpace ℝ (Fin r) =>
      ‖B.toEuclideanLin g‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin r))) :=
    hrightMem.integrable_norm_pow' (p := 2)
  have hsecond :
      (∫ g : EuclideanSpace ℝ (Fin r),
          HDP.Chapter7.finiteGaussianAbsSupport T g ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin r))) ≤
        HDP.matrixFrobeniusNorm B ^ 2 := by
    rw [← integral_norm_matrix_stdGaussian B]
    exact integral_mono hleftInt hrightInt fun g =>
      (sq_le_sq₀
        (HDP.Chapter7.finiteGaussianAbsSupport_nonneg T g)
        (norm_nonneg _)).2 (hpoint g)
  calc
    HDP.Chapter7.gaussianComplexity T ≤
        HDP.Chapter7.gaussianL2Width T :=
      HDP.Chapter7.gaussianComplexity_le_gaussianL2Width T
    _ ≤ Real.sqrt (HDP.matrixFrobeniusNorm B ^ 2) := by
      exact Real.sqrt_le_sqrt hsecond
    _ = HDP.matrixFrobeniusNorm B :=
      Real.sqrt_sq (HDP.matrixFrobeniusNorm_nonneg B)

/-! ## From quadratic deviations to covariance operator norm -/

/-- The factorized sample-covariance error as a continuous self-adjoint
operator on the ambient space.

**Lean implementation helper.** -/
noncomputable def factorCovarianceDeviationOperator {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (factorSampleSecondMoment A B - factorPopulationSecondMoment B).toEuclideanLin
    |>.toContinuousLinearMap

/-- The norm of the covariance-deviation operator equals the matrix operator norm of the sample-minus-population second moment.

**Lean implementation helper.** -/
@[simp]
theorem norm_factorCovarianceDeviationOperator {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) :
    ‖factorCovarianceDeviationOperator A B‖ =
      HDP.matrixOpNorm
        (factorSampleSecondMoment A B - factorPopulationSecondMoment B) := by
  rfl

/-- The covariance-deviation operator associated with a matrix factor is self-adjoint.

**Lean implementation helper.** -/
theorem factorCovarianceDeviationOperator_isSelfAdjoint {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ) :
    IsSelfAdjoint (factorCovarianceDeviationOperator A B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  rw [factorCovarianceDeviationOperator]
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  have hsample : (factorSampleSecondMoment A B).IsHermitian := by
    exact (HDP.gramMatrix_isHermitian (A * B.transpose)).smul (by simp)
  have hpop : (factorPopulationSecondMoment B).IsHermitian := by
    simpa [factorPopulationSecondMoment, HDP.gramMatrix,
      Matrix.transpose_transpose] using
        HDP.gramMatrix_isHermitian B.transpose
  exact hsample.sub hpop

/-- Rayleigh quotient of the factorized covariance error.

**Lean implementation helper.** -/
theorem factorCovarianceDeviationOperator_rayleigh {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (factorCovarianceDeviationOperator A B).reApplyInnerSelf x =
      (m : ℝ)⁻¹ * ‖A.toEuclideanLin (B.transpose.toEuclideanLin x)‖ ^ 2 -
        ‖B.transpose.toEuclideanLin x‖ ^ 2 := by
  have hs := HDP.Chapter4.normalizedGramDeviationOperator_rayleigh
    (A * B.transpose) x
  have hp := HDP.Chapter4.gramDeviationOperator_rayleigh B.transpose x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real] at hs hp ⊢
  change inner ℝ
      (((HDP.normalizedGram m (A * B.transpose) - 1).toEuclideanLin) x) x = _
    at hs
  change inner ℝ
      (((HDP.gramMatrix B.transpose - 1).toEuclideanLin) x) x = _ at hp
  have hsample :
      factorSampleSecondMoment A B - factorPopulationSecondMoment B =
        (HDP.normalizedGram m (A * B.transpose) - 1) -
          (HDP.gramMatrix B.transpose - 1) := by
    simp [factorSampleSecondMoment, factorPopulationSecondMoment,
      HDP.gramMatrix, Matrix.transpose_transpose]
  change inner ℝ
      ((factorSampleSecondMoment A B - factorPopulationSecondMoment B).toEuclideanLin x)
      x = _
  rw [hsample]
  simp only [map_sub, LinearMap.sub_apply, inner_sub_left] at hs hp ⊢
  rw [hs, hp]
  have hmul : (A * B.transpose).toEuclideanLin x =
      A.toEuclideanLin (B.transpose.toEuclideanLin x) := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  rw [hmul]
  ring

/-- The finite quadratic-deviation supremum dominates the absolute quadratic deviation at each indexed vector.

**Lean implementation helper.** -/
theorem abs_quadraticProcess_le_finite {m r : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin r) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin r))) [Nonempty ↥T]
    {y : EuclideanSpace ℝ (Fin r)} (hy : y ∈ T) (ω : Ω) :
    |‖matrixAction A y ω‖ ^ 2 - m * ‖y‖ ^ 2| ≤
      finiteMatrixQuadraticDeviation A T ω := by
  let Z : HDP.RandomProcess ↥T Ω :=
    HDP.Chapter8.finiteEuclideanProcess T
      (fun y ω => ‖matrixAction A y ω‖ ^ 2 - m * ‖y‖ ^ 2)
  let z : ↥T := ⟨y, hy⟩
  change |Z z ω| ≤ HDP.Chapter8.finiteProcessAbsoluteSup Z ω
  unfold HDP.Chapter8.finiteProcessAbsoluteSup
  exact Finset.le_sup' (fun q : ↥T => |Z q ω|) (Finset.mem_univ z)

/-- Totalized notation for the quadratic deviation on an ellipsoid net.

**Lean implementation helper.** -/
def factorEllipsoidQuadraticDeviation {m n r : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin r) Ω)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n))) (hN0 : N.Nonempty)
    (ω : Ω) : ℝ :=
  letI : Nonempty ↥(factorEllipsoidNet B N) :=
    (factorEllipsoidNet_nonempty B hN0).to_subtype
  finiteMatrixQuadraticDeviation A (factorEllipsoidNet B N) ω

/-- A quarter-net and the quadratic process control the full factorized
covariance error.

**Lean implementation helper.** -/
theorem factorCovarianceError_le_quadraticDeviation {m n r : ℕ}
    (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin r) Ω)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (N : Finset (EuclideanSpace ℝ (Fin n))) (hN0 : N.Nonempty)
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (N : Set (EuclideanSpace ℝ (Fin n)))) (ω : Ω) :
    HDP.matrixOpNorm
        (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B) ≤
      2 * (m : ℝ)⁻¹ *
        factorEllipsoidQuadraticDeviation A B N hN0 ω := by
  classical
  let T := factorEllipsoidNet B N
  have hT : T.Nonempty := factorEllipsoidNet_nonempty B hN0
  letI : Nonempty ↥T := hT.to_subtype
  let Q : ℝ := finiteMatrixQuadraticDeviation A T ω
  have hQ0 : 0 ≤ Q := by
    obtain ⟨y, hy⟩ := hT
    exact (abs_nonneg (‖matrixAction A y ω‖ ^ 2 - m * ‖y‖ ^ 2)).trans
      (by simpa [Q] using abs_quadraticProcess_le_finite A T hy ω)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnet : ∀ x ∈ (N : Set (EuclideanSpace ℝ (Fin n))),
      |inner ℝ (factorCovarianceDeviationOperator (A ω) B x) x| ≤
        (m : ℝ)⁻¹ * Q := by
    intro x hx
    let y : EuclideanSpace ℝ (Fin r) := B.transpose.toEuclideanLin x
    have hy : y ∈ T := by
      unfold T factorEllipsoidNet
      exact Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩
    have hq := abs_quadraticProcess_le_finite A T hy ω
    have hray := factorCovarianceDeviationOperator_rayleigh (A ω) B x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real] at hray
    rw [hray]
    have haction : (A ω).toEuclideanLin y = matrixAction A y ω := by
      rfl
    rw [haction]
    have heq :
        (m : ℝ)⁻¹ * ‖matrixAction A y ω‖ ^ 2 - ‖y‖ ^ 2 =
          (m : ℝ)⁻¹ *
            (‖matrixAction A y ω‖ ^ 2 - m * ‖y‖ ^ 2) := by
      field_simp [hmR.ne']
    rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hmR.le)]
    exact mul_le_mul_of_nonneg_left (by simpa [Q] using hq)
      (inv_nonneg.mpr hmR.le)
  have hop := HDP.Chapter4.opNorm_le_of_quadratic_on_net
    (factorCovarianceDeviationOperator (A ω) B)
    (factorCovarianceDeviationOperator_isSelfAdjoint (A ω) B).isSymmetric
    (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (2 : ℝ) * (1 / 4) < 1 by norm_num)
    hN (mul_nonneg (inv_nonneg.mpr hmR.le) hQ0) hnet
  calc
    HDP.matrixOpNorm
        (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B) =
        ‖factorCovarianceDeviationOperator (A ω) B‖ :=
      (norm_factorCovarianceDeviationOperator (A ω) B).symm
    _ ≤ (m : ℝ)⁻¹ * Q / (1 - 2 * (1 / 4 : ℝ)) := hop
    _ = 2 * (m : ℝ)⁻¹ *
        factorEllipsoidQuadraticDeviation A B N hN0 ω := by
      dsimp only [Q]
      simp only [factorEllipsoidQuadraticDeviation]
      change (m : ℝ)⁻¹ * finiteMatrixQuadraticDeviation A T ω /
          (1 - 2 * (1 / 4 : ℝ)) =
        2 * (m : ℝ)⁻¹ * finiteMatrixQuadraticDeviation A T ω
      ring

/-- The trace of the factored population second moment is the squared Frobenius norm of the factor.

**Lean implementation helper.** -/
theorem trace_factorPopulationSecondMoment {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ) :
    (factorPopulationSecondMoment B).trace =
      HDP.matrixFrobeniusNorm B ^ 2 := by
  rw [HDP.matrixFrobeniusNorm_sq]
  simp [factorPopulationSecondMoment, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]

/-- The operator norm of the factored population second moment is the square of the factor's operator norm.

**Lean implementation helper.** -/
theorem opNorm_factorPopulationSecondMoment {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ) :
    HDP.matrixOpNorm (factorPopulationSecondMoment B) =
      HDP.matrixOpNorm B ^ 2 := by
  have h := HDP.matrixOpNorm_sq_eq_gram B.transpose
  simpa [factorPopulationSecondMoment, HDP.gramMatrix] using h.symm

/-- The effective rank of the factored population second moment equals the stable rank of the factor.

**Lean implementation helper.** -/
theorem effectiveRank_factorPopulationSecondMoment {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ) :
    HDP.effectiveRank (factorPopulationSecondMoment B) =
      HDP.stableRank B := by
  calc
    HDP.effectiveRank (factorPopulationSecondMoment B) =
        HDP.effectiveRank (HDP.gramMatrix B.transpose) := by
      congr 1
    _ = HDP.stableRank B.transpose :=
      (HDP.stableRank_eq_effectiveRank_gram B.transpose).symm
    _ = HDP.stableRank B := by
      simp [HDP.stableRank]

/-- Rewrites the two covariance-error scales in terms of stable rank and operator norm.

**Lean implementation helper.** -/
private theorem stableRank_factor_scaling {m n r : ℕ} (hm : 0 < m)
    (B : Matrix (Fin n) (Fin r) ℝ) (hB : B ≠ 0) :
    (m : ℝ)⁻¹ * HDP.matrixFrobeniusNorm B ^ 2 =
        (HDP.stableRank B / m) * HDP.matrixOpNorm B ^ 2 ∧
      (m : ℝ)⁻¹ * Real.sqrt m * HDP.matrixOpNorm B *
          HDP.matrixFrobeniusNorm B =
        Real.sqrt (HDP.stableRank B / m) * HDP.matrixOpNorm B ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < HDP.matrixOpNorm B := by
    change 0 < ‖B‖
    exact norm_pos_iff.mpr hB
  have hf : 0 ≤ HDP.matrixFrobeniusNorm B :=
    HDP.matrixFrobeniusNorm_nonneg B
  have hs : 0 ≤ HDP.stableRank B := by
    rw [HDP.stableRank]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · rw [HDP.stableRank]
    field_simp [hmR.ne', ha.ne']
  · apply (sq_eq_sq₀
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (inv_nonneg.mpr hmR.le) (Real.sqrt_nonneg m)) ha.le) hf)
      (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).mp
    rw [mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt hmR.le,
      Real.sq_sqrt (div_nonneg hs hmR.le)]
    rw [HDP.stableRank]
    field_simp [hmR.ne', ha.ne']

/-- The finite matrix quadratic deviation is integrable.

**Lean implementation helper.** -/
theorem integrable_finiteMatrixQuadraticDeviation
    [IsProbabilityMeasure μ] {m r : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin r) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin r))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    Integrable (finiteMatrixQuadraticDeviation A T) μ := by
  let F : Ω → ℝ := finiteMatrixDeviation A T
  have hF2 := finiteMatrixDeviation_memLp_two hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T
  have hFint : Integrable F μ := hF2.integrable (by norm_num)
  have hFsqInt : Integrable (fun ω => F ω ^ 2) μ := hF2.integrable_sq
  let R : Ω → ℝ := fun ω => F ω ^ 2 +
    2 * Real.sqrt m * HDP.Chapter7.finiteRadius T * F ω
  have hRint : Integrable R μ :=
    hFsqInt.add (hFint.const_mul
      (2 * Real.sqrt m * HDP.Chapter7.finiteRadius T))
  have hQmeas : Measurable (finiteMatrixQuadraticDeviation A T) := by
    apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
    intro x
    exact ((measurable_matrixAction A hrowsm x.1).norm.pow_const 2).sub_const _
  refine hRint.mono' hQmeas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact finiteMatrixQuadraticDeviation_le A T hT ω
  · obtain ⟨y, hy⟩ := hT
    exact (abs_nonneg (‖matrixAction A y ω‖ ^ 2 - m * ‖y‖ ^ 2)).trans
      (abs_quadraticProcess_le_finite A T hy ω)

/-- Singular-safe latent-rank formulation. The source's `K⁴` dependence is retained even though the earlier Chapter 4
factor theorem proves the stronger `K²` estimate under these normalized
isotropic-row hypotheses.

**Book Theorem 9.2.2.** -/
theorem theorem_9_2_2_lowRankCovariance_factorized
    [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m]
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K : ℝ} (hK : 1 ≤ K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K) :
    ∫ ω, HDP.matrixOpNorm
        (factorSampleSecondMoment (A ω) B -
          factorPopulationSecondMoment B) ∂μ ≤
      lowRankCovarianceExpectationConstant * K ^ 4 *
        (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
          HDP.matrixOpNorm (factorPopulationSecondMoment B) := by
  have hbase := HDP.Chapter4.theorem_4_7_1_factorized A B hrowsm hsub
    hiso hindep hfinite (lt_of_lt_of_le zero_lt_one hK) hpsi
  have hpow : K ^ 2 ≤ K ^ 4 := sq_le_fourth_of_one_le hK
  have hq : 0 ≤ Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m := by positivity
  have hN : 0 ≤ HDP.matrixOpNorm (B * B.transpose) :=
    HDP.matrixOpNorm_nonneg _
  calc
    ∫ ω, HDP.matrixOpNorm
        (factorSampleSecondMoment (A ω) B -
          factorPopulationSecondMoment B) ∂μ ≤
      HDP.Chapter4.gramExpectationConstant * K ^ 2 *
        (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
          HDP.matrixOpNorm (B * B.transpose) := by
      simpa [factorSampleSecondMoment, factorPopulationSecondMoment,
        mul_assoc] using hbase
    _ ≤ HDP.Chapter4.gramExpectationConstant * K ^ 4 *
        (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
          HDP.matrixOpNorm (B * B.transpose) := by
      have hrest : 0 ≤
          HDP.Chapter4.gramExpectationConstant *
            ((Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
              HDP.matrixOpNorm (B * B.transpose)) :=
        mul_nonneg HDP.Chapter4.gramExpectationConstant_pos.le
          (mul_nonneg hq hN)
      calc
        HDP.Chapter4.gramExpectationConstant * K ^ 2 *
            (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
              HDP.matrixOpNorm (B * B.transpose) =
            K ^ 2 * (HDP.Chapter4.gramExpectationConstant *
              ((Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
                HDP.matrixOpNorm (B * B.transpose))) := by ring
        _ ≤ K ^ 4 * (HDP.Chapter4.gramExpectationConstant *
              ((Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
                HDP.matrixOpNorm (B * B.transpose))) :=
          mul_le_mul_of_nonneg_right hpow hrest
        _ = HDP.Chapter4.gramExpectationConstant * K ^ 4 *
            (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
              HDP.matrixOpNorm (B * B.transpose) := by ring
    _ = lowRankCovarianceExpectationConstant * K ^ 4 *
        (Real.sqrt ((r : ℝ) / m) + (r : ℝ) / m) *
          HDP.matrixOpNorm (factorPopulationSecondMoment B) := rfl

/-- Explicit constant in the effective-rank form of Theorem 9.2.2.

**Book Theorem 9.2.2.** -/
def lowRankCovarianceEffectiveConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  2 * (quadraticMatrixDeviationSquareConstant +
    quadraticMatrixDeviationLinearConstant)

/-- The low rank covariance effective constant is strictly positive.

**Lean implementation helper.** -/
theorem lowRankCovarianceEffectiveConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < lowRankCovarianceEffectiveConstant := by
  have hs : 0 < quadraticMatrixDeviationSquareConstant := by
    dsimp [quadraticMatrixDeviationSquareConstant]
    positivity [HDP.Chapter8.exercise837MomentConstant_pos,
      matrixDeviationIncrementConstant_pos]
  have hl : 0 < quadraticMatrixDeviationLinearConstant := by
    dsimp [quadraticMatrixDeviationLinearConstant]
    positivity [matrixDeviationConstant_pos]
  dsimp [lowRankCovarianceEffectiveConstant]
  positivity

/-- Effective-rank operator-norm form. This is the
source-facing result: the complexity is `r(Σ)=tr(Σ)/‖Σ‖`, not the latent
factor dimension. The proof uses a quarter-net of the ambient sphere and
Exercise 9.3 on its image under `Bᵀ`; the zero covariance is handled
separately.

**Book Theorem 9.2.2.** -/
theorem theorem_9_2_2_lowRankCovariance_effectiveRank
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ]
    {m n r : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin r) Ω)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 1 ≤ K) (hpsi : A.RowPsi2Bound μ K) :
    ∫ ω, HDP.matrixOpNorm
        (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B) ∂μ ≤
      lowRankCovarianceEffectiveConstant * K ^ 4 *
        (Real.sqrt (HDP.effectiveRank (factorPopulationSecondMoment B) / m) +
          HDP.effectiveRank (factorPopulationSecondMoment B) / m) *
        HDP.matrixOpNorm (factorPopulationSecondMoment B) := by
  by_cases hB : B = 0
  · subst B
    simp [factorSampleSecondMoment, factorPopulationSecondMoment,
      HDP.normalizedGram, HDP.gramMatrix]
  by_cases hn : n = 0
  · subst n
    have hzero : B = 0 := by
      ext i
      exact Fin.elim0 i
    exact (hB hzero).elim
  letI : NeZero n := ⟨hn⟩
  obtain ⟨N, hN, hNcard⟩ := HDP.Chapter4.exists_quarter_unitSphereNet n
  have hN0 : N.Nonempty := by
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i
    have he : ‖e‖ = 1 := by simp [e]
    obtain ⟨x, hx, hxe⟩ := hN.2 e he
    exact ⟨x, by simpa using hx⟩
  let T := factorEllipsoidNet B N
  have hT : T.Nonempty := factorEllipsoidNet_nonempty B hN0
  letI : Nonempty ↥T := hT.to_subtype
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hquad := exercise_9_3_quadraticMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hKpos hpsi T hT
  have hGle := factorEllipsoidNet_gaussianComplexity_le B N hN0 hN
  have hRle := factorEllipsoidNet_radius_le B N hN0 hN
  let G := HDP.Chapter7.gaussianComplexity T
  let R := HDP.Chapter7.finiteRadius T
  let f := HDP.matrixFrobeniusNorm B
  let a := HDP.matrixOpNorm B
  have hG0 : 0 ≤ G := HDP.Chapter7.gaussianComplexity_nonneg T
  have hf0 : 0 ≤ f := HDP.matrixFrobeniusNorm_nonneg B
  have ha0 : 0 ≤ a := HDP.matrixOpNorm_nonneg B
  have hs0 : 0 ≤ quadraticMatrixDeviationSquareConstant := by
    dsimp [quadraticMatrixDeviationSquareConstant]
    positivity
  have hl0 : 0 ≤ quadraticMatrixDeviationLinearConstant := by
    exact mul_nonneg (by norm_num) matrixDeviationConstant_pos.le
  have hGsq : G ^ 2 ≤ f ^ 2 :=
    (sq_le_sq₀ hG0 hf0).2 (by simpa [G, f, T] using hGle)
  have hRG : R * G ≤ a * f := by
    exact mul_le_mul (by simpa [R, a, T] using hRle)
      (by simpa [G, f, T] using hGle) hG0 ha0
  have hquad' :
      (∫ ω, finiteMatrixQuadraticDeviation A T ω ∂μ) ≤
        quadraticMatrixDeviationSquareConstant * K ^ 4 * f ^ 2 +
          quadraticMatrixDeviationLinearConstant * K ^ 2 *
            Real.sqrt m * a * f := by
    calc
      (∫ ω, finiteMatrixQuadraticDeviation A T ω ∂μ) ≤
          quadraticMatrixDeviationSquareConstant * K ^ 4 * G ^ 2 +
            quadraticMatrixDeviationLinearConstant * K ^ 2 *
              Real.sqrt m * R * G := by
        simpa [G, R] using hquad
      _ ≤ quadraticMatrixDeviationSquareConstant * K ^ 4 * f ^ 2 +
          quadraticMatrixDeviationLinearConstant * K ^ 2 *
            Real.sqrt m * a * f := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hGsq
            (mul_nonneg hs0 (by positivity))
        · have hc : 0 ≤ quadraticMatrixDeviationLinearConstant * K ^ 2 *
              Real.sqrt m := by positivity
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hRG hc
  have hErrInt := HDP.Chapter4.factorized_covariance_error_integrable
    A B (hrowsm.aemeasurable_rows μ) hsub
  have hQInt := integrable_finiteMatrixQuadraticDeviation hm A hrowsm hsub
    hiso hindep hfinite hKpos hpsi T hT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale0 : 0 ≤ 2 * (m : ℝ)⁻¹ := by positivity
  have hraw :
      (∫ ω, HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B) ∂μ) ≤
        2 * (m : ℝ)⁻¹ *
          (quadraticMatrixDeviationSquareConstant * K ^ 4 * f ^ 2 +
            quadraticMatrixDeviationLinearConstant * K ^ 2 *
              Real.sqrt m * a * f) := by
    calc
      (∫ ω, HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B) ∂μ) ≤
          ∫ ω, 2 * (m : ℝ)⁻¹ *
            factorEllipsoidQuadraticDeviation A B N hN0 ω ∂μ := by
        apply integral_mono hErrInt
        · simpa [factorEllipsoidQuadraticDeviation, T] using
            hQInt.const_mul (2 * (m : ℝ)⁻¹)
        · intro ω
          exact factorCovarianceError_le_quadraticDeviation
            hm A B N hN0 hN ω
      _ = 2 * (m : ℝ)⁻¹ *
          ∫ ω, finiteMatrixQuadraticDeviation A T ω ∂μ := by
        rw [integral_const_mul]
        rfl
      _ ≤ 2 * (m : ℝ)⁻¹ *
          (quadraticMatrixDeviationSquareConstant * K ^ 4 * f ^ 2 +
            quadraticMatrixDeviationLinearConstant * K ^ 2 *
              Real.sqrt m * a * f) :=
        mul_le_mul_of_nonneg_left hquad' hscale0
  have hpow : K ^ 2 ≤ K ^ 4 := sq_le_fourth_of_one_le hK
  have hscale := stableRank_factor_scaling hm B hB
  let q : ℝ := HDP.stableRank B / m
  have hq0 : 0 ≤ q := by
    dsimp [q, HDP.stableRank]
    positivity
  have hextra : 0 ≤ 2 * K ^ 4 * a ^ 2 *
      (quadraticMatrixDeviationSquareConstant * Real.sqrt q +
        quadraticMatrixDeviationLinearConstant * q) := by
    positivity
  calc
    (∫ ω, HDP.matrixOpNorm
        (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B) ∂μ) ≤
        2 * (m : ℝ)⁻¹ *
          (quadraticMatrixDeviationSquareConstant * K ^ 4 * f ^ 2 +
            quadraticMatrixDeviationLinearConstant * K ^ 2 *
              Real.sqrt m * a * f) := hraw
    _ = 2 * quadraticMatrixDeviationSquareConstant * K ^ 4 * q * a ^ 2 +
        2 * quadraticMatrixDeviationLinearConstant * K ^ 2 *
          Real.sqrt q * a ^ 2 := by
      calc
        2 * (m : ℝ)⁻¹ *
            (quadraticMatrixDeviationSquareConstant * K ^ 4 * f ^ 2 +
              quadraticMatrixDeviationLinearConstant * K ^ 2 *
                Real.sqrt m * a * f) =
            2 * quadraticMatrixDeviationSquareConstant * K ^ 4 *
                ((m : ℝ)⁻¹ * f ^ 2) +
              2 * quadraticMatrixDeviationLinearConstant * K ^ 2 *
                ((m : ℝ)⁻¹ * Real.sqrt m * a * f) := by ring
        _ = 2 * quadraticMatrixDeviationSquareConstant * K ^ 4 * q * a ^ 2 +
            2 * quadraticMatrixDeviationLinearConstant * K ^ 2 *
              Real.sqrt q * a ^ 2 := by
          rw [show (m : ℝ)⁻¹ * f ^ 2 = q * a ^ 2 by
              simpa [q, f, a] using hscale.1,
            show (m : ℝ)⁻¹ * Real.sqrt m * a * f =
                Real.sqrt q * a ^ 2 by
              simpa [q, f, a] using hscale.2]
          ring
    _ ≤ 2 * quadraticMatrixDeviationSquareConstant * K ^ 4 * q * a ^ 2 +
        2 * quadraticMatrixDeviationLinearConstant * K ^ 4 *
          Real.sqrt q * a ^ 2 := by
      have hcoef :
          2 * quadraticMatrixDeviationLinearConstant * K ^ 2 ≤
            2 * quadraticMatrixDeviationLinearConstant * K ^ 4 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (by norm_num) hl0)
      have htail0 : 0 ≤ Real.sqrt q * a ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg q) (sq_nonneg a)
      have htail := mul_le_mul_of_nonneg_right hcoef htail0
      exact add_le_add (le_refl _) (by
        convert htail using 1 <;> ring)
    _ ≤ lowRankCovarianceEffectiveConstant * K ^ 4 *
          (Real.sqrt q + q) * a ^ 2 := by
      have hid : lowRankCovarianceEffectiveConstant * K ^ 4 *
            (Real.sqrt q + q) * a ^ 2 =
          (2 * quadraticMatrixDeviationSquareConstant * K ^ 4 * q * a ^ 2 +
            2 * quadraticMatrixDeviationLinearConstant * K ^ 4 *
              Real.sqrt q * a ^ 2) +
            2 * K ^ 4 * a ^ 2 *
              (quadraticMatrixDeviationSquareConstant * Real.sqrt q +
                quadraticMatrixDeviationLinearConstant * q) := by
        dsimp [lowRankCovarianceEffectiveConstant]
        ring
      rw [hid]
      exact le_add_of_nonneg_right hextra
    _ = lowRankCovarianceEffectiveConstant * K ^ 4 *
        (Real.sqrt (HDP.effectiveRank (factorPopulationSecondMoment B) / m) +
          HDP.effectiveRank (factorPopulationSecondMoment B) / m) *
        HDP.matrixOpNorm (factorPopulationSecondMoment B) := by
      rw [effectiveRank_factorPopulationSecondMoment,
        opNorm_factorPopulationSecondMoment]

set_option maxHeartbeats 800000 in
-- Positive-eigenspace whitening and the effective-rank normalization require
-- a larger deterministic elaboration budget than the project default.
/-- Empirical covariance has an effective-rank operator-norm error bound. Direct source-facing Theorem 9.2.2 for arbitrary relatively subgaussian
rows; the positive-eigenspace whitening above supplies the factorization.

**Book Theorem 9.2.2.** -/
theorem theorem_9_2_2_lowRankCovariance_direct
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hrowsm : D.MeasurableRows)
    (hsub : D.SubGaussianRows μ)
    (hindep : D.IndependentRows μ)
    (hsecond : CommonSecondMoment D μ Sigma)
    {K : ℝ} (hK : 1 ≤ K) (hrelative : RelativeRowPsi2Bound D μ K) :
    ∫ ω, HDP.matrixOpNorm (HDP.normalizedGram m (D ω) - Sigma) ∂μ ≤
      lowRankCovarianceEffectiveConstant * K ^ 4 *
        (Real.sqrt (HDP.effectiveRank Sigma / m) +
          HDP.effectiveRank Sigma / m) * HDP.matrixOpNorm Sigma := by
  let i0 : Fin m := ⟨0, hm⟩
  let hSigma : Sigma.PosSemidef := commonSecondMoment_posSemidef D Sigma
    (hrowsm.aemeasurable_rows μ) hsub hsecond i0
  let A := covarianceWhitenedSample D Sigma hSigma
  let B := covarianceEigenFactor Sigma hSigma
  have hAm : A.MeasurableRows :=
    covarianceWhitenedSample_measurableRows D Sigma hSigma hrowsm
  have hAsub : A.SubGaussianRows μ :=
    covarianceWhitenedSample_subGaussianRows D Sigma hSigma hsub
  have hAiso : A.IsotropicRows μ :=
    covarianceWhitenedSample_isotropicRows D Sigma hSigma
      (hrowsm.aemeasurable_rows μ) hsub hsecond
  have hAind : A.IndependentRows μ :=
    covarianceWhitenedSample_independentRows D Sigma hSigma hindep
  have hAfin : A.RowPsi2Finite μ :=
    covarianceWhitenedSample_rowPsi2Finite D Sigma hSigma hrowsm hsub
      hsecond hrelative
  have hApsi : A.RowPsi2Bound μ K :=
    covarianceWhitenedSample_rowPsi2Bound D Sigma hSigma hrowsm hsub
      hsecond (zero_le_one.trans hK) hrelative
  have hmain := theorem_9_2_2_lowRankCovariance_effectiveRank hm A B
    hAm hAsub hAiso hAind hAfin hK hApsi
  have hpop : factorPopulationSecondMoment B = Sigma := by
    simpa [B, factorPopulationSecondMoment] using
      covarianceEigenFactor_mul_transpose Sigma hSigma
  have hprod : (fun ω => A ω * B.transpose) =ᵐ[μ] D := by
    simpa [A, B] using
      covarianceWhitenedSample_mul_factor_ae D Sigma hSigma hrowsm hsub hsecond
  have herr : (fun ω => HDP.matrixOpNorm
      (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B)) =ᵐ[μ]
      fun ω => HDP.matrixOpNorm (HDP.normalizedGram m (D ω) - Sigma) := by
    filter_upwards [hprod] with ω hω
    simp [factorSampleSecondMoment, hω, hpop]
  rw [← integral_congr_ae herr]
  simpa [hpop] using hmain

/-- For a nonzero matrix, the Frobenius norm is the operator norm times the square root of stable rank.

**Lean implementation helper.** -/
private theorem frobenius_eq_opNorm_mul_sqrt_stableRank {n r : ℕ}
    (B : Matrix (Fin n) (Fin r) ℝ) (hB : B ≠ 0) :
    HDP.matrixFrobeniusNorm B =
      HDP.matrixOpNorm B * Real.sqrt (HDP.stableRank B) := by
  have ha : 0 < HDP.matrixOpNorm B := by
    change 0 < ‖B‖
    exact norm_pos_iff.mpr hB
  have hf := HDP.matrixFrobeniusNorm_nonneg B
  have hs : 0 ≤ HDP.stableRank B := by
    rw [HDP.stableRank]
    positivity
  apply (sq_eq_sq₀ hf
    (mul_nonneg ha.le (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hs, HDP.stableRank]
  field_simp [ha.ne']

/-- Converts the high-probability deviation scale into the effective-rank covariance tail expression.

**Lean implementation helper.** -/
private theorem effectiveTail_numerics
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m : ℕ} (hm : 0 < m) {K t a L : ℝ}
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ha : 0 ≤ a) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * matrixDeviationHighProbabilityConstant * K ^ 2 *
      a * Real.sqrt t) :
    2 * (m : ℝ)⁻¹ * (L ^ 2 + 2 * Real.sqrt m * a * L) ≤
      (8 * (matrixDeviationHighProbabilityConstant ^ 2 +
        matrixDeviationHighProbabilityConstant)) * K ^ 4 *
        (Real.sqrt (t / m) + t / m) * a ^ 2 := by
  let C : ℝ := matrixDeviationHighProbabilityConstant
  let D : ℝ := 2 * C * K ^ 2 * a * Real.sqrt t
  have hC : 0 ≤ C := matrixDeviationHighProbabilityConstant_pos.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : L ^ 2 ≤ D ^ 2 := (sq_le_sq₀ hL0 hD).2 (by simpa [D, C] using hL)
  have hlin : 2 * Real.sqrt m * a * L ≤
      2 * Real.sqrt m * a * D := by
    exact mul_le_mul_of_nonneg_left (by simpa [D, C] using hL)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg m)) ha)
  have hmono :
      2 * (m : ℝ)⁻¹ * (L ^ 2 + 2 * Real.sqrt m * a * L) ≤
        2 * (m : ℝ)⁻¹ * (D ^ 2 + 2 * Real.sqrt m * a * D) :=
    mul_le_mul_of_nonneg_left (add_le_add hsq hlin) (by positivity)
  have hsqrtScale : (m : ℝ)⁻¹ * Real.sqrt m * Real.sqrt t =
      Real.sqrt (t / m) := by
    rw [Real.sqrt_div ht]
    have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
    field_simp [hsqrtm.ne']
    rw [Real.sq_sqrt hmR.le]
  have hpow : K ^ 2 ≤ K ^ 4 := sq_le_fourth_of_one_le hK
  have hq0 : 0 ≤ t / (m : ℝ) := div_nonneg ht hmR.le
  have hDsq : D ^ 2 = 4 * C ^ 2 * K ^ 4 * a ^ 2 * t := by
    calc
      D ^ 2 = 4 * C ^ 2 * K ^ 4 * a ^ 2 * (Real.sqrt t) ^ 2 := by
        dsimp [D]
        ring
      _ = 4 * C ^ 2 * K ^ 4 * a ^ 2 * t := by
        rw [Real.sq_sqrt ht]
  calc
    2 * (m : ℝ)⁻¹ * (L ^ 2 + 2 * Real.sqrt m * a * L) ≤
        2 * (m : ℝ)⁻¹ * (D ^ 2 + 2 * Real.sqrt m * a * D) := hmono
    _ = 8 * C ^ 2 * K ^ 4 * (t / m) * a ^ 2 +
        8 * C * K ^ 2 * Real.sqrt (t / m) * a ^ 2 := by
      calc
        2 * (m : ℝ)⁻¹ * (D ^ 2 + 2 * Real.sqrt m * a * D) =
            8 * C ^ 2 * K ^ 4 * ((m : ℝ)⁻¹ * t) * a ^ 2 +
              8 * C * K ^ 2 *
                ((m : ℝ)⁻¹ * Real.sqrt m * Real.sqrt t) * a ^ 2 := by
          rw [hDsq]
          dsimp [D]
          ring
        _ = 8 * C ^ 2 * K ^ 4 * (t / m) * a ^ 2 +
            8 * C * K ^ 2 * Real.sqrt (t / m) * a ^ 2 := by
          rw [hsqrtScale]
          ring
    _ ≤ 8 * C ^ 2 * K ^ 4 * (t / m) * a ^ 2 +
        8 * C * K ^ 4 * Real.sqrt (t / m) * a ^ 2 := by
      have hcoef : 8 * C * K ^ 2 ≤ 8 * C * K ^ 4 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (by norm_num) hC)
      have htail := mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (Real.sqrt_nonneg (t / (m : ℝ))) (sq_nonneg a))
      nlinarith [htail]
    _ ≤ (8 * (C ^ 2 + C)) * K ^ 4 *
          (Real.sqrt (t / m) + t / m) * a ^ 2 := by
      have hextra : 0 ≤ 8 * K ^ 4 * a ^ 2 *
          (C ^ 2 * Real.sqrt (t / m) + C * (t / m)) := by
        positivity
      have hid : (8 * (C ^ 2 + C)) * K ^ 4 *
            (Real.sqrt (t / m) + t / m) * a ^ 2 =
          (8 * C ^ 2 * K ^ 4 * (t / m) * a ^ 2 +
            8 * C * K ^ 4 * Real.sqrt (t / m) * a ^ 2) +
            8 * K ^ 4 * a ^ 2 *
              (C ^ 2 * Real.sqrt (t / m) + C * (t / m)) := by ring
      rw [hid]
      exact le_add_of_nonneg_right hextra
    _ = (8 * (matrixDeviationHighProbabilityConstant ^ 2 +
          matrixDeviationHighProbabilityConstant)) * K ^ 4 *
          (Real.sqrt (t / m) + t / m) * a ^ 2 := rfl

/-- Explicit constant for the source's high-probability covariance bound.

**Lean implementation helper.** -/
def lowRankCovarianceTailConstant : ℝ :=
  HDP.Chapter4.covarianceTailConstant

/-- The low rank covariance tail constant is strictly positive.

**Lean implementation helper.** -/
theorem lowRankCovarianceTailConstant_pos :
    0 < lowRankCovarianceTailConstant :=
  HDP.Chapter4.covarianceTailConstant_pos

/-- / Remark 9.2.3. The failure probability is at most `2 exp (-u)`. The zero covariance and all
singular factors are covered without a separate invertibility assumption.

**Book Exercise 9.9.** -/
theorem exercise_9_9_lowRankCovariance_highProbability_latentRank
    [IsProbabilityMeasure μ]
    {m n r : ℕ} [NeZero m]
    (A : Ω → Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : HDP.RandomMatrix.AEMeasurableRows A μ)
    (hsub : HDP.RandomMatrix.SubGaussianRows A μ)
    (hiso : HDP.RandomMatrix.IsotropicRows A μ)
    (hindep : HDP.RandomMatrix.IndependentRows A μ)
    (hfinite : HDP.RandomMatrix.RowPsi2Finite A μ)
    {K u : ℝ} (hK : 1 ≤ K) (hpsi : HDP.RandomMatrix.RowPsi2Bound A μ K)
    (hu : 0 ≤ u) :
    μ {ω | lowRankCovarianceTailConstant * K ^ 4 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (factorPopulationSecondMoment B) <
        HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B -
            factorPopulationSecondMoment B)} ≤
      ENNReal.ofReal (2 * Real.exp (-u)) := by
  have hbase := HDP.Chapter4.exercise_4_49 A B hrowsm hsub hiso hindep
    hfinite (lt_of_lt_of_le zero_lt_one hK) hpsi hu
  have hpow : K ^ 2 ≤ K ^ 4 := sq_le_fourth_of_one_le hK
  have hq : 0 ≤
      Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m := by
    positivity
  have hN : 0 ≤ HDP.matrixOpNorm (B * B.transpose) :=
    HDP.matrixOpNorm_nonneg _
  have hthreshold :
      HDP.Chapter4.covarianceTailConstant * K ^ 2 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) ≤
        HDP.Chapter4.covarianceTailConstant * K ^ 4 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) := by
    have hrest : 0 ≤ HDP.Chapter4.covarianceTailConstant *
        ((Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
          HDP.matrixOpNorm (B * B.transpose)) :=
      mul_nonneg HDP.Chapter4.covarianceTailConstant_pos.le
        (mul_nonneg hq hN)
    calc
      HDP.Chapter4.covarianceTailConstant * K ^ 2 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) = K ^ 2 *
          (HDP.Chapter4.covarianceTailConstant *
            ((Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
              HDP.matrixOpNorm (B * B.transpose))) := by ring
      _ ≤ K ^ 4 * (HDP.Chapter4.covarianceTailConstant *
            ((Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
              HDP.matrixOpNorm (B * B.transpose))) :=
        mul_le_mul_of_nonneg_right hpow hrest
      _ = HDP.Chapter4.covarianceTailConstant * K ^ 4 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) := by ring
  calc
    μ {ω | lowRankCovarianceTailConstant * K ^ 4 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (factorPopulationSecondMoment B) <
        HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B -
            factorPopulationSecondMoment B)} ≤
      μ {ω | HDP.Chapter4.covarianceTailConstant * K ^ 2 *
          (Real.sqrt (((r : ℝ) + u) / m) + ((r : ℝ) + u) / m) *
            HDP.matrixOpNorm (B * B.transpose) <
        HDP.matrixOpNorm
          (HDP.normalizedGram m (A ω * B.transpose) - B * B.transpose)} := by
        apply measure_mono
        intro ω hω
        exact lt_of_le_of_lt hthreshold (by
          simpa [lowRankCovarianceTailConstant, factorPopulationSecondMoment,
            factorSampleSecondMoment] using hω)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u)) := hbase

/-- Explicit absolute constant in the effective-rank tail form.

**Lean implementation helper.** -/
def lowRankCovarianceEffectiveTailConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  8 * (matrixDeviationHighProbabilityConstant ^ 2 +
    matrixDeviationHighProbabilityConstant)

/-- The low rank covariance effective tail constant is strictly positive.

**Lean implementation helper.** -/
theorem lowRankCovarianceEffectiveTailConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < lowRankCovarianceEffectiveTailConstant := by
  have hC := matrixDeviationHighProbabilityConstant_pos
  dsimp [lowRankCovarianceEffectiveTailConstant]
  nlinarith [sq_nonneg matrixDeviationHighProbabilityConstant]

/-- / Remark 9.2.3, in the
source's effective-rank form. The failure probability is at most
`2 exp (-u)` and the threshold depends on `effectiveRank Σ + u`, not on a
chosen latent dimension.

**Book Exercise 9.9.** -/
theorem exercise_9_9_lowRankCovariance_highProbability
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ]
    {m n r : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin r) Ω)
    (B : Matrix (Fin n) (Fin r) ℝ)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K u : ℝ} (hK : 1 ≤ K) (hpsi : A.RowPsi2Bound μ K)
    (hu : 0 ≤ u) :
    μ {ω | lowRankCovarianceEffectiveTailConstant * K ^ 4 *
          (Real.sqrt
              ((HDP.effectiveRank (factorPopulationSecondMoment B) + u) / m) +
            (HDP.effectiveRank (factorPopulationSecondMoment B) + u) / m) *
            HDP.matrixOpNorm (factorPopulationSecondMoment B) <
        HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B -
            factorPopulationSecondMoment B)} ≤
      ENNReal.ofReal (2 * Real.exp (-u)) := by
  by_cases hB : B = 0
  · subst B
    simp [factorSampleSecondMoment, factorPopulationSecondMoment,
      HDP.normalizedGram, HDP.gramMatrix]
  by_cases hn : n = 0
  · subst n
    have hzero : B = 0 := by
      ext i
      exact Fin.elim0 i
    exact (hB hzero).elim
  letI : NeZero n := ⟨hn⟩
  obtain ⟨N, hN, hNcard⟩ := HDP.Chapter4.exists_quarter_unitSphereNet n
  have hN0 : N.Nonempty := by
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i
    have he : ‖e‖ = 1 := by simp [e]
    obtain ⟨x, hx, hxe⟩ := hN.2 e he
    exact ⟨x, by simpa using hx⟩
  let T := factorEllipsoidNet B N
  have hT : T.Nonempty := factorEllipsoidNet_nonempty B hN0
  letI : Nonempty ↥T := hT.to_subtype
  let f : ℝ := HDP.matrixFrobeniusNorm B
  let a : ℝ := HDP.matrixOpNorm B
  let s : ℝ := HDP.stableRank B
  let t : ℝ := s + u
  let L : ℝ := matrixDeviationHighProbabilityConstant * K ^ 2 *
    (f + Real.sqrt u * a)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ha0 : 0 ≤ a := HDP.matrixOpNorm_nonneg B
  have hf0 : 0 ≤ f := HDP.matrixFrobeniusNorm_nonneg B
  have hs0 : 0 ≤ s := by dsimp [s, HDP.stableRank]; positivity
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg matrixDeviationHighProbabilityConstant_pos.le (sq_nonneg K))
      (add_nonneg hf0 (mul_nonneg (Real.sqrt_nonneg u) ha0))
  have hfEq : f = a * Real.sqrt s := by
    simpa [f, a, s] using frobenius_eq_opNorm_mul_sqrt_stableRank B hB
  have hsqrtS : Real.sqrt s ≤ Real.sqrt t :=
    Real.sqrt_le_sqrt (by dsimp [t]; linarith)
  have hsqrtU : Real.sqrt u ≤ Real.sqrt t :=
    Real.sqrt_le_sqrt (by dsimp [t]; linarith)
  have hLupper : L ≤ 2 * matrixDeviationHighProbabilityConstant *
      K ^ 2 * a * Real.sqrt t := by
    dsimp only [L]
    rw [hfEq]
    have hadd : a * Real.sqrt s + Real.sqrt u * a ≤
        2 * a * Real.sqrt t := by
      calc
        a * Real.sqrt s + Real.sqrt u * a =
            a * (Real.sqrt s + Real.sqrt u) := by ring
        _ ≤ a * (Real.sqrt t + Real.sqrt t) :=
          mul_le_mul_of_nonneg_left (add_le_add hsqrtS hsqrtU) ha0
        _ = 2 * a * Real.sqrt t := by ring
    exact (mul_le_mul_of_nonneg_left hadd
      (mul_nonneg matrixDeviationHighProbabilityConstant_pos.le
        (sq_nonneg K))).trans_eq (by ring)
  have hnum := effectiveTail_numerics hm hK ht0 ha0 hL0 hLupper
  have hnum' :
      2 * (m : ℝ)⁻¹ * (L ^ 2 + 2 * Real.sqrt m * a * L) ≤
        lowRankCovarianceEffectiveTailConstant * K ^ 4 *
          (Real.sqrt (t / m) + t / m) * a ^ 2 := by
    simpa [lowRankCovarianceEffectiveTailConstant] using hnum
  have hwidth := (HDP.Chapter7.gaussianWidth_le_gaussianComplexity T).trans
    (by simpa [T, f] using
      factorEllipsoidNet_gaussianComplexity_le B N hN0 hN)
  have hR := factorEllipsoidNet_radius_le B N hN0 hN
  have hbaseThreshold :
      matrixDeviationHighProbabilityConstant * K ^ 2 *
          (HDP.Chapter7.gaussianWidth T +
            Real.sqrt u * HDP.Chapter7.finiteRadius T) ≤ L := by
    dsimp [L]
    apply mul_le_mul_of_nonneg_left
    · exact add_le_add hwidth
        (mul_le_mul_of_nonneg_left (by simpa [T, a] using hR)
          (Real.sqrt_nonneg u))
    · exact mul_nonneg matrixDeviationHighProbabilityConstant_pos.le
        (sq_nonneg K)
  have hbase := remark_9_1_4_matrixDeviation_highProbability hm A hrowsm
    hsub hiso hindep hfinite hKpos hpsi (Real.sqrt_nonneg u) T hT
  calc
    μ {ω | lowRankCovarianceEffectiveTailConstant * K ^ 4 *
          (Real.sqrt
              ((HDP.effectiveRank (factorPopulationSecondMoment B) + u) / m) +
            (HDP.effectiveRank (factorPopulationSecondMoment B) + u) / m) *
            HDP.matrixOpNorm (factorPopulationSecondMoment B) <
        HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B -
            factorPopulationSecondMoment B)} ≤
      μ {ω | matrixDeviationHighProbabilityConstant * K ^ 2 *
          (HDP.Chapter7.gaussianWidth T +
            Real.sqrt u * HDP.Chapter7.finiteRadius T) <
          finiteMatrixDeviation A T ω} := by
      apply measure_mono
      intro ω hω
      have htarget :
          lowRankCovarianceEffectiveTailConstant * K ^ 4 *
              (Real.sqrt (t / m) + t / m) * a ^ 2 <
            HDP.matrixOpNorm
              (factorSampleSecondMoment (A ω) B -
                factorPopulationSecondMoment B) := by
        simpa [t, s, a, effectiveRank_factorPopulationSecondMoment,
          opNorm_factorPopulationSecondMoment] using hω
      have hLF : L < finiteMatrixDeviation A T ω := by
        by_contra hnot
        have hFL : finiteMatrixDeviation A T ω ≤ L := le_of_not_gt hnot
        have hF0 := finiteMatrixDeviation_nonneg A T ω
        have hR0 : 0 ≤ HDP.Chapter7.finiteRadius T := by
          obtain ⟨y, hy⟩ := hT.exists_mem
          exact (norm_nonneg y).trans
            (HDP.Chapter7.norm_le_finiteRadius T hT hy)
        have hsq : finiteMatrixDeviation A T ω ^ 2 ≤ L ^ 2 :=
          (sq_le_sq₀ hF0 hL0).2 hFL
        have hprod : HDP.Chapter7.finiteRadius T *
            finiteMatrixDeviation A T ω ≤ a * L :=
          mul_le_mul (by simpa [T, a] using hR) hFL hF0 ha0
        have hQ : finiteMatrixQuadraticDeviation A T ω ≤
            L ^ 2 + 2 * Real.sqrt m * a * L := by
          refine (finiteMatrixQuadraticDeviation_le A T hT ω).trans ?_
          exact add_le_add hsq (by
            have hc : 0 ≤ 2 * Real.sqrt m := by positivity
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod hc)
        have hErr := factorCovarianceError_le_quadraticDeviation
          hm A B N hN0 hN ω
        have hscale : 0 ≤ 2 * (m : ℝ)⁻¹ := by positivity
        have hErr' : HDP.matrixOpNorm
              (factorSampleSecondMoment (A ω) B -
                factorPopulationSecondMoment B) ≤
            2 * (m : ℝ)⁻¹ * (L ^ 2 + 2 * Real.sqrt m * a * L) :=
          hErr.trans (mul_le_mul_of_nonneg_left hQ hscale)
        exact (not_lt_of_ge (hErr'.trans hnum')) htarget
      exact lt_of_le_of_lt hbaseThreshold hLF
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(Real.sqrt u) ^ 2)) := hbase
    _ = ENNReal.ofReal (2 * Real.exp (-u)) := by
      rw [Real.sq_sqrt hu]

end

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

set_option maxHeartbeats 800000 in
-- Reusing the singular-safe whitening construction inside the tail event
-- requires the same larger deterministic elaboration budget.
/-- The covariance-estimation error has a high-probability version. Direct source-facing Exercise 9.9 / Remark 9.2.3 for arbitrary rows
satisfying the relative ψ₂/L² hypothesis.

**Book Remark 9.2.3.** -/
theorem exercise_9_9_lowRankCovariance_highProbability_direct
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (D : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hrowsm : D.MeasurableRows)
    (hsub : D.SubGaussianRows μ)
    (hindep : D.IndependentRows μ)
    (hsecond : CommonSecondMoment D μ Sigma)
    {K u : ℝ} (hK : 1 ≤ K) (hrelative : RelativeRowPsi2Bound D μ K)
    (hu : 0 ≤ u) :
    μ {ω | lowRankCovarianceEffectiveTailConstant * K ^ 4 *
          (Real.sqrt ((HDP.effectiveRank Sigma + u) / m) +
            (HDP.effectiveRank Sigma + u) / m) * HDP.matrixOpNorm Sigma <
        HDP.matrixOpNorm (HDP.normalizedGram m (D ω) - Sigma)} ≤
      ENNReal.ofReal (2 * Real.exp (-u)) := by
  let i0 : Fin m := ⟨0, hm⟩
  let hSigma : Sigma.PosSemidef := commonSecondMoment_posSemidef D Sigma
    (hrowsm.aemeasurable_rows μ) hsub hsecond i0
  let A := covarianceWhitenedSample D Sigma hSigma
  let B := covarianceEigenFactor Sigma hSigma
  have hAm : A.MeasurableRows :=
    covarianceWhitenedSample_measurableRows D Sigma hSigma hrowsm
  have hAsub : A.SubGaussianRows μ :=
    covarianceWhitenedSample_subGaussianRows D Sigma hSigma hsub
  have hAiso : A.IsotropicRows μ :=
    covarianceWhitenedSample_isotropicRows D Sigma hSigma
      (hrowsm.aemeasurable_rows μ) hsub hsecond
  have hAind : A.IndependentRows μ :=
    covarianceWhitenedSample_independentRows D Sigma hSigma hindep
  have hAfin : A.RowPsi2Finite μ :=
    covarianceWhitenedSample_rowPsi2Finite D Sigma hSigma hrowsm hsub
      hsecond hrelative
  have hApsi : A.RowPsi2Bound μ K :=
    covarianceWhitenedSample_rowPsi2Bound D Sigma hSigma hrowsm hsub
      hsecond (zero_le_one.trans hK) hrelative
  have hmain := exercise_9_9_lowRankCovariance_highProbability hm A B
    hAm hAsub hAiso hAind hAfin hK hApsi hu
  have hpop : factorPopulationSecondMoment B = Sigma := by
    simpa [B, factorPopulationSecondMoment] using
      covarianceEigenFactor_mul_transpose Sigma hSigma
  have hprod : (fun ω => A ω * B.transpose) =ᵐ[μ] D := by
    simpa [A, B] using
      covarianceWhitenedSample_mul_factor_ae D Sigma hSigma hrowsm hsub hsecond
  calc
    μ {ω | lowRankCovarianceEffectiveTailConstant * K ^ 4 *
          (Real.sqrt ((HDP.effectiveRank Sigma + u) / m) +
            (HDP.effectiveRank Sigma + u) / m) * HDP.matrixOpNorm Sigma <
        HDP.matrixOpNorm (HDP.normalizedGram m (D ω) - Sigma)} =
      μ {ω | lowRankCovarianceEffectiveTailConstant * K ^ 4 *
          (Real.sqrt
              ((HDP.effectiveRank (factorPopulationSecondMoment B) + u) / m) +
            (HDP.effectiveRank (factorPopulationSecondMoment B) + u) / m) *
            HDP.matrixOpNorm (factorPopulationSecondMoment B) <
        HDP.matrixOpNorm
          (factorSampleSecondMoment (A ω) B - factorPopulationSecondMoment B)} := by
      apply measure_congr
      filter_upwards [hprod] with ω hω
      simp only [factorSampleSecondMoment, hpop]
      change
        (lowRankCovarianceEffectiveTailConstant * K ^ 4 *
              (Real.sqrt ((HDP.effectiveRank Sigma + u) / m) +
                (HDP.effectiveRank Sigma + u) / m) * HDP.matrixOpNorm Sigma <
            HDP.matrixOpNorm (HDP.normalizedGram m (D ω) - Sigma)) =
          (lowRankCovarianceEffectiveTailConstant * K ^ 4 *
              (Real.sqrt ((HDP.effectiveRank Sigma + u) / m) +
                (HDP.effectiveRank Sigma + u) / m) * HDP.matrixOpNorm Sigma <
            HDP.matrixOpNorm
              (HDP.normalizedGram m (A ω * B.transpose) - Sigma))
      rw [hω]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u)) := hmain

end

end HDP.Chapter9

end Source_05_LowRankCovarianceEstimation

/-! ## Material formerly in `06_AdditiveJohnsonLindenstrauss.lean` -/

section Source_06_AdditiveJohnsonLindenstrauss

/-!
# Book Chapter 9, §9.2.4: additive Johnson--Lindenstrauss

The finite form below is fully measurable and has the source's explicit
`0.99` success probability.  The proof applies Theorem 9.1.1 to `X-X` and
then uses Markov's inequality, exactly as described in the text.  Notice that
both endpoints of a difference come from the same set; this corrects the
printed `x in X, y in Y` typo.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The normalized random map `Q = A / sqrt m`.

**Lean implementation helper.** -/
def normalizedMatrixAction {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    EuclideanSpace ℝ (Fin m) :=
  (Real.sqrt m)⁻¹ • matrixAction A x ω

/-- The normalized matrix action commutes with subtraction.

**Lean implementation helper.** -/
theorem normalizedMatrixAction_sub {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x y : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    normalizedMatrixAction A (x - y) ω =
      normalizedMatrixAction A x ω - normalizedMatrixAction A y ω := by
  simp [normalizedMatrixAction, matrixAction_sub, smul_sub]

/-- Maximum additive distance distortion on a finite set.

**Lean implementation helper.** -/
def finiteAdditiveDistortion {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X]
    (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (fun p : ↥X × ↥X => fun ω =>
      ‖normalizedMatrixAction A p.1.1 ω -
          normalizedMatrixAction A p.2.1 ω‖ - ‖p.1.1 - p.2.1‖) ω

/-- The finite additive distortion is nonnegative.

**Lean implementation helper.** -/
theorem finiteAdditiveDistortion_nonneg {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X]
    (ω : Ω) : 0 ≤ finiteAdditiveDistortion A X ω := by
  unfold finiteAdditiveDistortion HDP.Chapter8.finiteProcessAbsoluteSup
  let p0 : ↥X × ↥X := Classical.choice inferInstance
  exact (abs_nonneg _).trans
    (Finset.le_sup' (fun p : ↥X × ↥X =>
      |‖normalizedMatrixAction A p.1.1 ω -
          normalizedMatrixAction A p.2.1 ω‖ - ‖p.1.1 - p.2.1‖|)
      (Finset.mem_univ p0))

/-- The finite additive distortion is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteAdditiveDistortion {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X] :
    Measurable (finiteAdditiveDistortion A X) := by
  apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
  intro p
  exact (((measurable_matrixAction A hrowsm p.1.1).const_smul
      (Real.sqrt m)⁻¹).sub
    ((measurable_matrixAction A hrowsm p.2.1).const_smul
      (Real.sqrt m)⁻¹)).norm.sub_const _

/-- For a fixed matrix outcome, the normalized matrix action is continuous in
the Euclidean input. This is the deterministic continuity input used to pass
from finite dense prefixes to an arbitrary set.

**Lean implementation helper.** -/
theorem continuous_normalizedMatrixAction {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) (ω : Ω) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      normalizedMatrixAction A x ω) := by
  change Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
    (Real.sqrt m)⁻¹ • (A ω).toEuclideanLin x)
  exact (A ω).toEuclideanLin.toContinuousLinearMap.continuous.const_smul _

/-- Additive distortion is monotone under enlargement of the finite cloud.

**Lean implementation helper.** -/
theorem finiteAdditiveDistortion_mono {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    {X Y : Finset (EuclideanSpace ℝ (Fin n))}
    [Nonempty ↥X] [Nonempty ↥Y] (hXY : X ⊆ Y) (ω : Ω) :
    finiteAdditiveDistortion A X ω ≤ finiteAdditiveDistortion A Y ω := by
  unfold finiteAdditiveDistortion HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro p _hp
  let q : ↥Y × ↥Y :=
    (⟨p.1.1, hXY p.1.2⟩, ⟨p.2.1, hXY p.2.2⟩)
  simpa [q] using
    (Finset.le_sup'
      (fun r : ↥Y × ↥Y =>
        |‖normalizedMatrixAction A r.1.1 ω -
            normalizedMatrixAction A r.2.1 ω‖ - ‖r.1.1 - r.2.1‖|)
      (Finset.mem_univ q))

/-- The distortion of an individual pair is bounded by the finite-cloud
distortion.

**Lean implementation helper.** -/
theorem pairAdditiveDistortion_le_finiteAdditiveDistortion {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X]
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ X) (hy : y ∈ X)
    (ω : Ω) :
    |‖normalizedMatrixAction A x ω - normalizedMatrixAction A y ω‖ -
        ‖x - y‖| ≤ finiteAdditiveDistortion A X ω := by
  unfold finiteAdditiveDistortion HDP.Chapter8.finiteProcessAbsoluteSup
  let p : ↥X × ↥X := (⟨x, hx⟩, ⟨y, hy⟩)
  simpa [p] using
    (Finset.le_sup'
      (fun q : ↥X × ↥X =>
        |‖normalizedMatrixAction A q.1.1 ω -
            normalizedMatrixAction A q.2.1 ω‖ - ‖q.1.1 - q.2.1‖|)
      (Finset.mem_univ p))

/-! ## Reusable dense finite prefixes of an arbitrary Euclidean set -/

/-- The canonical countable dense sequence in a nonempty Euclidean set,
viewed in the subtype. This is public infrastructure for the arbitrary-set
results later in Chapter 9.

**Lean implementation helper.** -/
def setDenseSubtypePoint {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (i : ℕ) : X :=
  TopologicalSpace.denseSeq X i

/-- The canonical dense point, coerced back to the ambient Euclidean space.

**Lean implementation helper.** -/
def setDensePoint {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (i : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (setDenseSubtypePoint X i : EuclideanSpace ℝ (Fin n))

/-- The first `k + 1` canonical dense points of a nonempty Euclidean set.

**Lean implementation helper.** -/
def setDensePrefix {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (k : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  (Finset.range (k + 1)).image (setDensePoint X)

/-- Every point selected by the set enumeration lies in the original set.

**Lean implementation helper.** -/
theorem setDensePoint_mem {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (i : ℕ) :
    setDensePoint X i ∈ X :=
  (setDenseSubtypePoint X i).property

/-- An enumerated point lies in each finite prefix extending past its index.

**Lean implementation helper.** -/
theorem setDensePoint_mem_prefix {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    {i k : ℕ} (hik : i ≤ k) :
    setDensePoint X i ∈ setDensePrefix X k := by
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- Every finite prefix of the selected dense sequence contains at least one point.

**Lean implementation helper.** -/
theorem setDensePrefix_nonempty {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (k : ℕ) :
    (setDensePrefix X k).Nonempty := by
  exact ⟨setDensePoint X 0, setDensePoint_mem_prefix X (Nat.zero_le k)⟩

/-- Each finite dense prefix is contained in the set from which it was selected.

**Lean implementation helper.** -/
theorem setDensePrefix_subset {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (k : ℕ) :
    (setDensePrefix X k : Set (EuclideanSpace ℝ (Fin n))) ⊆ X := by
  intro x hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  exact setDensePoint_mem X i

/-- The finite dense prefixes form an increasing sequence of sets.

**Lean implementation helper.** -/
theorem setDensePrefix_mono {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    {j k : ℕ} (hjk : j ≤ k) :
    setDensePrefix X j ⊆ setDensePrefix X k := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hi
    omega), rfl⟩

/-- A continuous real function on a nonempty Euclidean set is bounded above
once it is bounded on the canonical dense sequence.

**Lean implementation helper.** -/
theorem continuous_le_of_setDenseSubtypePoint_le {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (f : X → ℝ) (hf : Continuous f) {c : ℝ}
    (hseq : ∀ i, f (setDenseSubtypePoint X i) ≤ c) :
    ∀ x, f x ≤ c := by
  intro x
  have hclosed : IsClosed {y : X | f y ≤ c} :=
    isClosed_le hf continuous_const
  have hrange : Set.range (TopologicalSpace.denseSeq X) ⊆
      {y : X | f y ≤ c} := by
    rintro _ ⟨i, rfl⟩
    exact hseq i
  have hx : x ∈ closure (Set.range (TopologicalSpace.denseSeq X)) := by
    rw [(TopologicalSpace.denseRange_denseSeq X).closure_range]
    trivial
  exact (closure_minimal hrange hclosed) hx

/-! ## Finite Gaussian widths inside the bounded-set width envelope -/

/-- Every nonempty finite subfamily has Gaussian width at most the canonical
arbitrary-set Gaussian-width envelope.

**Lean implementation helper.** -/
theorem finiteGaussianWidth_le_euclideanSetGaussianWidth {n : ℕ}
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hXne : X.Nonempty) (hXb : Bornology.IsBounded X)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFX : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ X)
    (hF : F.Nonempty) :
    HDP.Chapter7.gaussianWidth F ≤
      HDP.Chapter8.euclideanSetGaussianWidth X := by
  have hENN : ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
      HDP.Chapter8.euclideanSetGaussianWidthENN X := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    exact le_iSup_of_le F
      (le_iSup_of_le hFX (le_iSup_of_le hF le_rfl))
  have hfin : HDP.Chapter8.euclideanSetGaussianWidthENN X ≠ ⊤ :=
    HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top hXne hXb
  have hreal := ENNReal.toReal_mono hfin hENN
  simpa [HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal (HDP.Chapter7.gaussianWidth_nonneg F hF)] using hreal

/-- The Gaussian width of every finite dense prefix is bounded by the Gaussian width of the full bounded set.

**Lean implementation helper.** -/
theorem densePrefix_gaussianWidth_le {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (hXne : X.Nonempty) (hXb : Bornology.IsBounded X) (k : ℕ) :
    HDP.Chapter7.gaussianWidth (setDensePrefix X k) ≤
      HDP.Chapter8.euclideanSetGaussianWidth X :=
  finiteGaussianWidth_le_euclideanSetGaussianWidth hXne hXb
    (setDensePrefix X k) (setDensePrefix_subset X k)
    (setDensePrefix_nonempty X k)

/-- Every difference vector from `X-X` has norm at most `diam X`.

**Lean implementation helper.** -/
theorem finiteRadius_difference_le_diameter {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : X.Nonempty) :
    HDP.Chapter7.finiteRadius (HDP.Chapter7.differenceFinset X X) ≤
      HDP.Chapter7.finiteEuclideanDiameter X := by
  let D := HDP.Chapter7.differenceFinset X X
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hX hX
  rw [HDP.Chapter7.finiteRadius_eq_sup' D hD]
  apply Finset.sup'_le
  intro z hz
  unfold D HDP.Chapter7.differenceFinset
    HDP.Chapter7.minkowskiSumFinset HDP.Chapter7.negFinset at hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hpX, hpneg⟩ := Finset.mem_product.mp hp
  obtain ⟨y, hyX, hy⟩ := Finset.mem_image.mp hpneg
  rw [← hy]
  change ‖p.1 - y‖ ≤ HDP.Chapter7.finiteEuclideanDiameter X
  exact HDP.Chapter7.norm_sub_le_finiteEuclideanDiameter X hX hpX hyX

/-- Deterministic reduction of additive distortion to the deviation process
on the difference set.

**Lean implementation helper.** -/
theorem finiteAdditiveDistortion_le {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X]
    (hX : X.Nonempty) (ω : Ω) :
    finiteAdditiveDistortion A X ω ≤
      letI : Nonempty ↥(HDP.Chapter7.differenceFinset X X) :=
        (HDP.Chapter7.differenceFinset_nonempty hX hX).to_subtype
      (Real.sqrt m)⁻¹ *
        finiteMatrixDeviation A (HDP.Chapter7.differenceFinset X X) ω := by
  let D := HDP.Chapter7.differenceFinset X X
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hX hX
  letI : Nonempty ↥D := hD.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  unfold finiteAdditiveDistortion
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro p hp
  have hdmem : p.1.1 - p.2.1 ∈ D := by
    unfold D HDP.Chapter7.differenceFinset
      HDP.Chapter7.minkowskiSumFinset HDP.Chapter7.negFinset
    apply Finset.mem_image.mpr
    refine ⟨(p.1.1, -p.2.1),
      Finset.mem_product.mpr ⟨p.1.2, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨p.2.1, p.2.2, rfl⟩
    · simp [sub_eq_add_neg]
  have hdev := abs_matrixDeviationProcess_le_finite A D hdmem ω
  have heq :
      ‖normalizedMatrixAction A p.1.1 ω -
          normalizedMatrixAction A p.2.1 ω‖ - ‖p.1.1 - p.2.1‖ =
        (Real.sqrt m)⁻¹ *
          matrixDeviationProcess A (p.1.1 - p.2.1) ω := by
    rw [← normalizedMatrixAction_sub]
    simp only [normalizedMatrixAction, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hsqrt, matrixDeviationProcess]
    field_simp [hsqrt.ne']
  change |‖normalizedMatrixAction A p.1.1 ω -
      normalizedMatrixAction A p.2.1 ω‖ - ‖p.1.1 - p.2.1‖| ≤
    (Real.sqrt m)⁻¹ * finiteMatrixDeviation A D ω
  rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hsqrt.le)]
  exact mul_le_mul_of_nonneg_left hdev (inv_nonneg.mpr hsqrt.le)

/-- Universal constant in the `0.99` additive JL statement.

**Lean implementation helper.** -/
def additiveJLConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  200 * matrixDeviationConstant

/-- The additive Johnson–Lindenstrauss constant is strictly positive.

**Lean implementation helper.** -/
theorem additiveJLConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < additiveJLConstant :=
  mul_pos (by norm_num) matrixDeviationConstant_pos

/-- The additive error in Lemma 9.2.4.

**Book Lemma 9.2.4.** -/
def additiveJLError [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (K : ℝ)
    (X : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  additiveJLConstant * K ^ 2 * HDP.Chapter7.gaussianWidth X /
    Real.sqrt m

/-- Finite exact
form. With failure probability at most `1/100`, every pairwise distance is
preserved up to the displayed additive error.

**Book Lemma 9.2.4.** -/
theorem theorem_9_2_4_additiveJohnsonLindenstrauss_finite
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X]
    (hX : X.Nonempty) :
    μ.real {ω | additiveJLError (m := m) K X <
        finiteAdditiveDistortion A X ω} ≤
      1 / 100 := by
  let D := HDP.Chapter7.differenceFinset X X
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hX hX
  letI : Nonempty ↥D := hD.to_subtype
  let F : Ω → ℝ := finiteMatrixDeviation A D
  let Q : Ω → ℝ := finiteAdditiveDistortion A X
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have hQint : Integrable Q μ := by
    refine (hFint.const_mul (Real.sqrt m)⁻¹).mono'
      (measurable_finiteAdditiveDistortion A hrowsm X).aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hprod : 0 ≤ (Real.sqrt m)⁻¹ * F ω :=
      mul_nonneg (inv_nonneg.mpr hsqrt.le)
        (finiteMatrixDeviation_nonneg A D ω)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (finiteAdditiveDistortion_nonneg A X ω),
      abs_of_nonneg hprod, Q, F, D] using
        finiteAdditiveDistortion_le hm A X hX ω
  have hmean : (∫ ω, Q ω ∂μ) ≤
      2 * matrixDeviationConstant * K ^ 2 *
        HDP.Chapter7.gaussianWidth X / Real.sqrt m := by
    have hpoint : ∀ ω, Q ω ≤ (Real.sqrt m)⁻¹ * F ω := fun ω => by
      simpa [Q, F, D] using finiteAdditiveDistortion_le hm A X hX ω
    have hmono : (∫ ω, Q ω ∂μ) ≤
        ∫ ω, (Real.sqrt m)⁻¹ * F ω ∂μ :=
      integral_mono hQint (hFint.const_mul _) hpoint
    have hmain := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
      hindep hfinite hK hpsi D hD
    have hscale : 0 ≤ (Real.sqrt m)⁻¹ := inv_nonneg.mpr hsqrt.le
    calc
      (∫ ω, Q ω ∂μ) ≤
          ∫ ω, (Real.sqrt m)⁻¹ * F ω ∂μ := hmono
      _ = (Real.sqrt m)⁻¹ * ∫ ω, F ω ∂μ := integral_const_mul _ _
      _ ≤ (Real.sqrt m)⁻¹ *
          (matrixDeviationConstant * K ^ 2 *
            HDP.Chapter7.gaussianComplexity D) :=
        mul_le_mul_of_nonneg_left hmain hscale
      _ = 2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth X / Real.sqrt m := by
        rw [HDP.Chapter7.gaussianComplexity_difference X hX]
        ring
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω =>
    finiteAdditiveDistortion_nonneg A X ω
  have hw0 : 0 ≤ HDP.Chapter7.gaussianWidth X :=
    HDP.Chapter7.gaussianWidth_nonneg X hX
  by_cases hw : HDP.Chapter7.gaussianWidth X = 0
  · have hmean0 : (∫ ω, Q ω ∂μ) = 0 := by
      apply le_antisymm
      · simpa [hw] using hmean
      · exact integral_nonneg hQ0
    have hQae : Q =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hQ0 hQint).mp hmean0
    have herr0 : additiveJLError (m := m) K X = 0 := by
      simp [additiveJLError, hw]
    have hevent : μ {ω | additiveJLError (m := m) K X < Q ω} = 0 := by
      refine measure_eq_zero_iff_ae_notMem.mpr ?_
      filter_upwards [hQae] with ω hω
      have hω' : Q ω = 0 := by simpa only [Pi.zero_apply] using hω
      change ¬ (additiveJLError (m := m) K X < Q ω)
      rw [herr0, hω']
      exact lt_irrefl 0
    change μ.real {ω | additiveJLError (m := m) K X < Q ω} ≤ 1 / 100
    rw [Measure.real, hevent]
    norm_num
  · have hwpos : 0 < HDP.Chapter7.gaussianWidth X :=
      lt_of_le_of_ne hw0 (Ne.symm hw)
    have ht : 0 < additiveJLError (m := m) K X := by
      dsimp [additiveJLError, additiveJLConstant]
      positivity [matrixDeviationConstant_pos]
    have hmark := HDP.Chapter1.markov_inequality
      (μ := μ) (X := Q) (Filter.Eventually.of_forall hQ0) hQint ht
    calc
      μ.real {ω | additiveJLError (m := m) K X < Q ω} ≤
          μ.real {ω | additiveJLError (m := m) K X ≤ Q ω} := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        change additiveJLError (m := m) K X < Q ω at hω
        change additiveJLError (m := m) K X ≤ Q ω
        exact hω.le
      _ ≤ (∫ ω, Q ω ∂μ) / additiveJLError (m := m) K X := hmark
      _ ≤ (2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth X / Real.sqrt m) /
          additiveJLError (m := m) K X :=
        div_le_div_of_nonneg_right hmean ht.le
      _ = 1 / 100 := by
        simp [additiveJLError, additiveJLConstant]
        field_simp [matrixDeviationConstant_pos.ne', hK.ne', hw,
          hsqrt.ne']
        ring

/-! ## The source-facing arbitrary bounded-set form -/

/-- The additive error in Lemma 9.2.4 for an arbitrary Euclidean set. The
ordinary-real width is safe here because the source-facing theorem assumes
that the set is nonempty and bounded.

**Book Lemma 9.2.4.** -/
def setAdditiveJLError [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (K : ℝ) (X : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  additiveJLConstant * K ^ 2 *
    HDP.Chapter8.euclideanSetGaussianWidth X / Real.sqrt m

/-- The exact uniform pairwise additive-distance-distortion event on a set.

**Lean implementation helper.** -/
def uniformAdditiveDistortionEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Set (EuclideanSpace ℝ (Fin n))) (error : ℝ) : Set Ω :=
  {ω | ∀ x ∈ X, ∀ y ∈ X,
    |‖normalizedMatrixAction A x ω - normalizedMatrixAction A y ω‖ -
      ‖x - y‖| ≤ error}

/-- The bad event on the `k`th canonical finite dense prefix.

**Lean implementation helper.** -/
def densePrefixAdditiveDistortionBadEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (error : ℝ) (k : ℕ) : Set Ω :=
  letI : Nonempty ↥(setDensePrefix X k) :=
    (setDensePrefix_nonempty X k).to_subtype
  {ω | error < finiteAdditiveDistortion A (setDensePrefix X k) ω}

/-- The event that a finite dense prefix violates the additive-distortion tolerance is measurable.

**Lean implementation helper.** -/
theorem measurableSet_densePrefixAdditiveDistortionBadEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (error : ℝ) (k : ℕ) :
    MeasurableSet (densePrefixAdditiveDistortionBadEvent A X error k) := by
  letI : Nonempty ↥(setDensePrefix X k) :=
    (setDensePrefix_nonempty X k).to_subtype
  exact measurableSet_lt measurable_const
    (measurable_finiteAdditiveDistortion A hrowsm (setDensePrefix X k))

/-- Testing distortion on larger dense prefixes produces an increasing sequence of bad events.

**Lean implementation helper.** -/
theorem densePrefixAdditiveDistortionBadEvent_mono {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (error : ℝ) :
    Monotone (densePrefixAdditiveDistortionBadEvent A X error) := by
  intro j k hjk ω hω
  letI : Nonempty ↥(setDensePrefix X j) :=
    (setDensePrefix_nonempty X j).to_subtype
  letI : Nonempty ↥(setDensePrefix X k) :=
    (setDensePrefix_nonempty X k).to_subtype
  change error < finiteAdditiveDistortion A (setDensePrefix X j) ω at hω
  change error < finiteAdditiveDistortion A (setDensePrefix X k) ω
  exact hω.trans_le
    (finiteAdditiveDistortion_mono A (setDensePrefix_mono X hjk) ω)

/-- Finite-prefix JL errors are bounded by the arbitrary-set JL error.

**Lean implementation helper.** -/
theorem additiveJLError_densePrefix_le_setAdditiveJLError
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (hm : 0 < m) (K : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (hXne : X.Nonempty) (hXb : Bornology.IsBounded X) (k : ℕ) :
    additiveJLError (m := m) K (setDensePrefix X k) ≤
      setAdditiveJLError (m := m) K X := by
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  unfold additiveJLError setAdditiveJLError
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (densePrefix_gaussianWidth_le X hXne hXb k)
      (mul_nonneg additiveJLConstant_pos.le (sq_nonneg K))) hsqrt.le

/-- Uniform additive distortion on a nonempty set is exactly the complement
of the increasing union of bad canonical finite-prefix events. Continuity of
the fixed matrix action supplies both passages from the dense sequence to the
whole set.

**Lean implementation helper.** -/
theorem uniformAdditiveDistortionEvent_eq_compl_iUnion_densePrefix
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (error : ℝ) :
    uniformAdditiveDistortionEvent A X error =
      (⋃ k, densePrefixAdditiveDistortionBadEvent A X error k)ᶜ := by
  ext ω
  constructor
  · intro hω
    change ∀ x ∈ X, ∀ y ∈ X,
      |‖normalizedMatrixAction A x ω - normalizedMatrixAction A y ω‖ -
        ‖x - y‖| ≤ error at hω
    change ω ∉ ⋃ k, densePrefixAdditiveDistortionBadEvent A X error k
    intro hbad
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hbad
    letI : Nonempty ↥(setDensePrefix X k) :=
      (setDensePrefix_nonempty X k).to_subtype
    change error < finiteAdditiveDistortion A (setDensePrefix X k) ω at hk
    have hle : finiteAdditiveDistortion A (setDensePrefix X k) ω ≤ error := by
      unfold finiteAdditiveDistortion HDP.Chapter8.finiteProcessAbsoluteSup
      apply Finset.sup'_le
      intro p _hp
      exact hω p.1.1 (setDensePrefix_subset X k p.1.2)
        p.2.1 (setDensePrefix_subset X k p.2.2)
    exact (not_lt_of_ge hle) hk
  · intro hω
    change ω ∉ ⋃ k, densePrefixAdditiveDistortionBadEvent A X error k at hω
    have hk : ∀ k,
        letI : Nonempty ↥(setDensePrefix X k) :=
          (setDensePrefix_nonempty X k).to_subtype
        finiteAdditiveDistortion A (setDensePrefix X k) ω ≤ error := by
      intro k
      letI : Nonempty ↥(setDensePrefix X k) :=
        (setDensePrefix_nonempty X k).to_subtype
      apply not_lt.mp
      intro hbad
      apply hω
      exact Set.mem_iUnion_of_mem k hbad
    let d : X → X → ℝ := fun x y =>
      |‖normalizedMatrixAction A x.1 ω -
          normalizedMatrixAction A y.1 ω‖ - ‖x.1 - y.1‖|
    have haction := continuous_normalizedMatrixAction A ω
    have hcontRight (x : X) : Continuous (d x) := by
      dsimp [d]
      exact (((continuous_const.sub
        (haction.comp continuous_subtype_val)).norm).sub
          ((continuous_const.sub continuous_subtype_val).norm)).abs
    have hcontLeft (y : X) : Continuous (fun x : X => d x y) := by
      dsimp [d]
      exact ((((haction.comp continuous_subtype_val).sub
        continuous_const).norm).sub
          ((continuous_subtype_val.sub continuous_const).norm)).abs
    have hdense (i j : ℕ) :
        d (setDenseSubtypePoint X i) (setDenseSubtypePoint X j) ≤ error := by
      let k := max i j
      letI : Nonempty ↥(setDensePrefix X k) :=
        (setDensePrefix_nonempty X k).to_subtype
      have hpair := pairAdditiveDistortion_le_finiteAdditiveDistortion A
        (setDensePrefix X k)
        (setDensePoint_mem_prefix X (Nat.le_max_left i j))
        (setDensePoint_mem_prefix X (Nat.le_max_right i j)) ω
      simpa [d, setDensePoint, k] using hpair.trans (hk k)
    have hdenseRight (i : ℕ) :
        ∀ y : X, d (setDenseSubtypePoint X i) y ≤ error :=
      continuous_le_of_setDenseSubtypePoint_le X
        (d (setDenseSubtypePoint X i))
        (hcontRight (setDenseSubtypePoint X i)) (hdense i)
    have hall (y : X) : ∀ x : X, d x y ≤ error :=
      continuous_le_of_setDenseSubtypePoint_le X (fun x : X => d x y)
        (hcontLeft y) (fun i => hdenseRight i y)
    change ∀ x ∈ X, ∀ y ∈ X,
      |‖normalizedMatrixAction A x ω - normalizedMatrixAction A y ω‖ -
        ‖x - y‖| ≤ error
    intro x hx y hy
    simpa [d] using hall ⟨y, hy⟩ ⟨x, hx⟩

/-- The event of uniformly bounded additive distortion on the whole set is measurable.

**Lean implementation helper.** -/
theorem measurableSet_uniformAdditiveDistortionEvent {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X] (error : ℝ) :
    MeasurableSet (uniformAdditiveDistortionEvent A X error) := by
  rw [uniformAdditiveDistortionEvent_eq_compl_iUnion_densePrefix]
  exact (MeasurableSet.iUnion fun k =>
    measurableSet_densePrefixAdditiveDistortionBadEvent A hrowsm X error k).compl

/-- The probability of excessive distortion on a finite dense prefix satisfies the stated Gaussian tail bound.

**Lean implementation helper.** -/
theorem measureReal_densePrefixAdditiveDistortionBadEvent_le
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) [Nonempty X]
    (hXne : X.Nonempty) (hXb : Bornology.IsBounded X) (k : ℕ) :
    μ.real (densePrefixAdditiveDistortionBadEvent A X
      (setAdditiveJLError (m := m) K X) k) ≤ 1 / 100 := by
  let F := setDensePrefix X k
  have hF : F.Nonempty := setDensePrefix_nonempty X k
  letI : Nonempty ↥F := hF.to_subtype
  have hfiniteJL := theorem_9_2_4_additiveJohnsonLindenstrauss_finite
    hm A hrowsm hsub hiso hindep hfinite hK hpsi F hF
  calc
    μ.real (densePrefixAdditiveDistortionBadEvent A X
        (setAdditiveJLError (m := m) K X) k) ≤
        μ.real {ω | additiveJLError (m := m) K F <
          finiteAdditiveDistortion A F ω} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change setAdditiveJLError (m := m) K X <
        finiteAdditiveDistortion A F ω at hω
      change additiveJLError (m := m) K F <
        finiteAdditiveDistortion A F ω
      have herr : additiveJLError (m := m) K F ≤
          setAdditiveJLError (m := m) K X := by
        simpa [F] using additiveJLError_densePrefix_le_setAdditiveJLError
          hm K X hXne hXb k
      exact herr.trans_lt hω
    _ ≤ 1 / 100 := hfiniteJL

/-- Additive Johnson--Lindenstrauss embeds any bounded set with an error governed by Gaussian complexity. Exact source-facing
form for an arbitrary nonempty bounded set. With probability at least
`0.99`, the normalized random map simultaneously preserves every pairwise
distance up to `C K² w(X) / sqrt m`.

**Book Lemma 9.2.4.** -/
theorem theorem_9_2_4_additiveJohnsonLindenstrauss
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXne : X.Nonempty) (hXb : Bornology.IsBounded X) :
    99 / 100 ≤ μ.real (uniformAdditiveDistortionEvent A X
      (setAdditiveJLError (m := m) K X)) := by
  letI : Nonempty X := hXne.to_subtype
  let error := setAdditiveJLError (m := m) K X
  let bad : ℕ → Set Ω :=
    densePrefixAdditiveDistortionBadEvent A X error
  have hbadMono : Monotone bad := by
    simpa [bad] using densePrefixAdditiveDistortionBadEvent_mono A X error
  have hbadReal (k : ℕ) : μ.real (bad k) ≤ 1 / 100 := by
    simpa [bad, error] using
      measureReal_densePrefixAdditiveDistortionBadEvent_le hm A hrowsm
        hsub hiso hindep hfinite hK hpsi X hXne hXb k
  have hbadENN (k : ℕ) :
      μ (bad k) ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
    calc
      μ (bad k) = ENNReal.ofReal (μ.real (bad k)) := by
        rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (1 / 100 : ℝ) :=
        ENNReal.ofReal_mono (hbadReal k)
  have hunionENN :
      μ (⋃ k, bad k) ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
    rw [hbadMono.measure_iUnion]
    exact iSup_le hbadENN
  have hunionReal : μ.real (⋃ k, bad k) ≤ 1 / 100 := by
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hunionENN
    simpa [Measure.real, ENNReal.toReal_ofReal (by norm_num :
      (0 : ℝ) ≤ 1 / 100)] using htoReal
  have hbadMeas : MeasurableSet (⋃ k, bad k) :=
    MeasurableSet.iUnion fun k => by
      simpa [bad, error] using
        measurableSet_densePrefixAdditiveDistortionBadEvent A hrowsm X
          (setAdditiveJLError (m := m) K X) k
  rw [uniformAdditiveDistortionEvent_eq_compl_iUnion_densePrefix,
    measureReal_compl hbadMeas, probReal_univ]
  linarith

/-- Width-based effective dimension used in Remark 9.2.5, totalized at
zero for a singleton set.

**Book Remark 9.2.5.** -/
def widthEffectiveDimension {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if HDP.Chapter7.finiteEuclideanDiameter X = 0 then 0
  else HDP.Chapter7.gaussianWidth X ^ 2 /
    HDP.Chapter7.finiteEuclideanDiameter X ^ 2

/-- Algebraic content of Remark 9.2.5: an additive error which is at most an
`ε` fraction of the diameter gives the advertised diameter-scale control.

**Book Remark 9.2.5.** -/
theorem additive_distortion_le_fraction_of_diameter
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} {K ε : ℝ}
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (_hε : 0 ≤ ε)
    (hbound : additiveJLError (m := m) K X ≤
      ε * HDP.Chapter7.finiteEuclideanDiameter X)
    {δ : ℝ} (hδ : δ ≤ additiveJLError (m := m) K X) :
    δ ≤ ε * HDP.Chapter7.finiteEuclideanDiameter X :=
  hδ.trans hbound

/-- A nonempty finite set of diameter zero has zero Gaussian width. This is
the degenerate branch needed to state Remark 9.2.5 without silently dividing
by the diameter.

**Book Remark 9.2.5.** -/
theorem gaussianWidth_eq_zero_of_finiteEuclideanDiameter_eq_zero
    {n : ℕ} (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : X.Nonempty)
    (hdiam : HDP.Chapter7.finiteEuclideanDiameter X = 0) :
    HDP.Chapter7.gaussianWidth X = 0 := by
  apply le_antisymm
  · calc
      HDP.Chapter7.gaussianWidth X ≤
          Real.sqrt n / 2 * HDP.Chapter7.finiteEuclideanDiameter X :=
        HDP.Chapter7.gaussianWidth_le_sqrt_card_mul_diameter X hX
      _ = 0 := by rw [hdiam]; ring
  · exact HDP.Chapter7.gaussianWidth_nonneg X hX

/-- Quantitative algebraic form. The printed `d(T)`
is corrected to `d(X)`. The zero-diameter case is discharged separately;
otherwise the displayed sample-size condition makes the additive JL error at
most an `ε` fraction of the diameter.

**Book Remark 9.2.5.** -/
theorem remark_9_2_5_additiveJLError_le
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (hm : 0 < m) {K ε : ℝ} (hε : 0 < ε)
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : X.Nonempty)
    (hsize : additiveJLConstant ^ 2 * K ^ 4 *
        widthEffectiveDimension X / ε ^ 2 ≤ (m : ℝ)) :
    additiveJLError (m := m) K X ≤
      ε * HDP.Chapter7.finiteEuclideanDiameter X := by
  let D := HDP.Chapter7.finiteEuclideanDiameter X
  let w := HDP.Chapter7.gaussianWidth X
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  have hw0 : 0 ≤ w := HDP.Chapter7.gaussianWidth_nonneg X hX
  have hD0 : 0 ≤ D := HDP.Chapter7.finiteEuclideanDiameter_nonneg X
  by_cases hD : D = 0
  · have hw : w = 0 := by
      simpa [w, D] using
        gaussianWidth_eq_zero_of_finiteEuclideanDiameter_eq_zero X hX
          (by simpa [D] using hD)
    simp [additiveJLError, w, D, hw, hD]
  · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD)
    have hsize' : additiveJLConstant ^ 2 * K ^ 4 *
        (w ^ 2 / D ^ 2) / ε ^ 2 ≤ (m : ℝ) := by
      simpa [widthEffectiveDimension, D, w, hD] using hsize
    have hsize₁ : additiveJLConstant ^ 2 * K ^ 4 *
        (w ^ 2 / D ^ 2) ≤ (m : ℝ) * ε ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hε)).mp hsize'
    have hsize₂ :
        (additiveJLConstant ^ 2 * K ^ 4 * w ^ 2) / D ^ 2 ≤
          (m : ℝ) * ε ^ 2 := by
      simpa [mul_div_assoc] using hsize₁
    have hpoly : additiveJLConstant ^ 2 * K ^ 4 * w ^ 2 ≤
        ((m : ℝ) * ε ^ 2) * D ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hDpos)).mp hsize₂
    have hleft : 0 ≤ additiveJLConstant * K ^ 2 * w :=
      mul_nonneg
        (mul_nonneg additiveJLConstant_pos.le (sq_nonneg K)) hw0
    have hright : 0 ≤ ε * D * Real.sqrt m := by positivity
    have hsq : (additiveJLConstant * K ^ 2 * w) ^ 2 ≤
        (ε * D * Real.sqrt m) ^ 2 := by
      nlinarith [Real.sq_sqrt hm0]
    have hlinear : additiveJLConstant * K ^ 2 * w ≤
        ε * D * Real.sqrt m :=
      (sq_le_sq₀ hleft hright).mp hsq
    change additiveJLConstant * K ^ 2 * w / Real.sqrt m ≤ ε * D
    exact (div_le_iff₀ hsqrt).mpr (by simpa [mul_assoc] using hlinear)

/-- Probability form of Remark 9.2.5. Under the explicit sample-size
condition, the same `0.99` event from Lemma 9.2.4 controls every pairwise
distance up to `ε · diam(X)`.

**Book Remark 9.2.5.** -/
theorem remark_9_2_5_effectiveDimension
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K ε : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hε : 0 < ε)
    (X : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥X]
    (hX : X.Nonempty)
    (hsize : additiveJLConstant ^ 2 * K ^ 4 *
        widthEffectiveDimension X / ε ^ 2 ≤ (m : ℝ)) :
    μ.real {ω | ε * HDP.Chapter7.finiteEuclideanDiameter X <
        finiteAdditiveDistortion A X ω} ≤ 1 / 100 := by
  have herr := remark_9_2_5_additiveJLError_le hm hε X hX hsize
  calc
    μ.real {ω | ε * HDP.Chapter7.finiteEuclideanDiameter X <
        finiteAdditiveDistortion A X ω} ≤
        μ.real {ω | additiveJLError (m := m) K X <
          finiteAdditiveDistortion A X ω} := by
      exact measureReal_mono (fun _ hω => lt_of_le_of_lt herr hω)
        (measure_ne_top _ _)
    _ ≤ 1 / 100 := theorem_9_2_4_additiveJohnsonLindenstrauss_finite hm A
      hrowsm hsub hiso hindep hfinite hK hpsi X hX

/-- Width effective dimension for an arbitrary Euclidean set. Division is
totalized by Lean at diameter zero; source-facing quantitative theorems below
carry the mathematically necessary positive-diameter hypothesis.

**Lean implementation helper.** -/
def setWidthEffectiveDimension {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if Metric.diam X = 0 then 0
  else HDP.Chapter8.euclideanSetGaussianWidth X ^ 2 /
    Metric.diam X ^ 2

/-- The additive JL error is small once the target dimension dominates effective dimension. Arbitrary-set algebraic form of Remark 9.2.5. This is the exact analogue
of `remark_9_2_5_additiveJLError_le`, with Mathlib's actual set diameter and
the book-wide finite-subfamily Gaussian-width envelope.

**Book Remark 9.2.5.** -/
theorem remark_9_2_5_setAdditiveJLError_le
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (hm : 0 < m) {K ε : ℝ} (hε : 0 < ε)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hdiam : 0 < Metric.diam X)
    (hsize : additiveJLConstant ^ 2 * K ^ 4 *
        setWidthEffectiveDimension X / ε ^ 2 ≤ (m : ℝ)) :
    setAdditiveJLError (m := m) K X ≤ ε * Metric.diam X := by
  let D := Metric.diam X
  let w := HDP.Chapter8.euclideanSetGaussianWidth X
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hDpos : 0 < D := by simpa [D] using hdiam
  have hsize' : additiveJLConstant ^ 2 * K ^ 4 *
      (w ^ 2 / D ^ 2) / ε ^ 2 ≤ (m : ℝ) := by
    simpa [setWidthEffectiveDimension, D, w, hDpos.ne'] using hsize
  have hsize₁ : additiveJLConstant ^ 2 * K ^ 4 *
      (w ^ 2 / D ^ 2) ≤ (m : ℝ) * ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp hsize'
  have hsize₂ :
      (additiveJLConstant ^ 2 * K ^ 4 * w ^ 2) / D ^ 2 ≤
        (m : ℝ) * ε ^ 2 := by
    simpa [mul_div_assoc] using hsize₁
  have hpoly : additiveJLConstant ^ 2 * K ^ 4 * w ^ 2 ≤
      ((m : ℝ) * ε ^ 2) * D ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hDpos)).mp hsize₂
  have hleft : 0 ≤ additiveJLConstant * K ^ 2 * w :=
    mul_nonneg (mul_nonneg additiveJLConstant_pos.le (sq_nonneg K)) hw0
  have hright : 0 ≤ ε * D * Real.sqrt m := by positivity
  have hsq : (additiveJLConstant * K ^ 2 * w) ^ 2 ≤
      (ε * D * Real.sqrt m) ^ 2 := by
    nlinarith [Real.sq_sqrt hm0]
  have hlinear : additiveJLConstant * K ^ 2 * w ≤
      ε * D * Real.sqrt m :=
    (sq_le_sq₀ hleft hright).mp hsq
  change additiveJLConstant * K ^ 2 * w / Real.sqrt m ≤ ε * D
  exact (div_le_iff₀ hsqrt).mpr (by simpa [mul_assoc] using hlinear)

/-- The additive JL error is small once the target dimension dominates effective dimension. Actual arbitrary bounded-set probability form.
The event controls all pairs in `X`, not merely a chosen finite family.

**Book Remark 9.2.5.** -/
theorem remark_9_2_5_effectiveDimension_set
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K ε : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hε : 0 < ε)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXne : X.Nonempty) (hXb : Bornology.IsBounded X)
    (hdiam : 0 < Metric.diam X)
    (hsize : additiveJLConstant ^ 2 * K ^ 4 *
        setWidthEffectiveDimension X / ε ^ 2 ≤ (m : ℝ)) :
    99 / 100 ≤ μ.real (uniformAdditiveDistortionEvent A X
      (ε * Metric.diam X)) := by
  have hbase := theorem_9_2_4_additiveJohnsonLindenstrauss hm A hrowsm
    hsub hiso hindep hfinite hK hpsi X hXne hXb
  have herr := remark_9_2_5_setAdditiveJLError_le hm hε X hdiam hsize
  exact hbase.trans (measureReal_mono
    (by
      intro ω hω x hx y hy
      exact (hω x hx y hy).trans herr)
    (measure_ne_top _ _))

/-! Exercise 9.11 is used here as a conceptual guardrail, so its witness is
kept in the core rather than an exercise leaf. -/

/-- The bounded infinite set used for the Exercise 9.11 counterexample.

**Book Exercise 9.11.** -/
def exercise911CounterexampleSet : Set (EuclideanSpace ℝ (Fin 1)) :=
  Metric.closedBall 0 1

/-- The first counterexample set for Exercise 9.11 is bounded.

**Lean implementation helper.** -/
theorem exercise911CounterexampleSet_bounded :
    Bornology.IsBounded exercise911CounterexampleSet := by
  exact Metric.isBounded_closedBall

/-- The first counterexample set for Exercise 9.11 contains infinitely many points.

**Lean implementation helper.** -/
theorem exercise911CounterexampleSet_infinite :
    exercise911CounterexampleSet.Infinite := by
  have hball : (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1).Infinite :=
    infinite_of_mem_nhds 0 (Metric.ball_mem_nhds 0 zero_lt_one)
  exact hball.mono Metric.ball_subset_closedBall

/-- Compatibility version of Exercise 9.11 using the degenerate target
`Fin 0`. The source-facing theorem below replaces it by an admissible
positive-dimensional `ℝ² → ℝ¹` witness.

**Book Exercise 9.11.** -/
theorem exercise_9_11_additive_error_is_necessary_zeroDim_compat
    (Q : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 0))
    {ε : ℝ} (hε : ε < 1) :
    ∃ x ∈ exercise911CounterexampleSet,
      ∃ y ∈ exercise911CounterexampleSet,
        ¬ ((1 - ε) * ‖x - y‖ ≤ ‖Q x - Q y‖) := by
  let e : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.basisFun (Fin 1) ℝ 0
  refine ⟨e, ?_, 0, ?_, ?_⟩
  · simp [exercise911CounterexampleSet, e]
  · simp [exercise911CounterexampleSet]
  · have hQ : Q e = Q 0 := Subsingleton.elim _ _
    rw [hQ]
    simp only [sub_self, norm_zero, not_le]
    simpa [e] using sub_pos.mpr hε

/-- The explicit coordinate projection used in the corrected Exercise 9.11
witness.

**Book Exercise 9.11.** -/
def exercise911ProjectionMatrix : Matrix (Fin 1) (Fin 2) ℝ :=
  fun _ j => if j = 0 then 1 else 0

/-- The admissible positive-target map `ℝ² → ℝ¹`.

**Lean implementation helper.** -/
def exercise911Projection :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  exercise911ProjectionMatrix.toEuclideanLin.toContinuousLinearMap

/-- The bounded infinite source set for the positive-target witness.

**Lean implementation helper.** -/
def exercise911PositiveTargetCounterexampleSet :
    Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 1

/-- The positive-target counterexample set for Exercise 9.11 is bounded.

**Lean implementation helper.** -/
theorem exercise911PositiveTargetCounterexampleSet_bounded :
    Bornology.IsBounded exercise911PositiveTargetCounterexampleSet := by
  exact Metric.isBounded_closedBall

/-- The positive-target counterexample set for Exercise 9.11 contains infinitely many points.

**Lean implementation helper.** -/
theorem exercise911PositiveTargetCounterexampleSet_infinite :
    exercise911PositiveTargetCounterexampleSet.Infinite := by
  have hball : (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1).Infinite :=
    infinite_of_mem_nhds 0 (Metric.ball_mem_nhds 0 zero_lt_one)
  exact hball.mono Metric.ball_subset_closedBall

/-- The counterexample projection annihilates the second standard basis vector.

**Lean implementation helper.** -/
theorem exercise911Projection_secondBasis_eq_zero :
    exercise911Projection
      (EuclideanSpace.basisFun (Fin 2) ℝ (1 : Fin 2)) = 0 := by
  ext i
  fin_cases i
  simp [exercise911Projection, exercise911ProjectionMatrix,
    Matrix.toLpLin_apply]

/-- Additive JL error cannot in general be replaced by a uniform relative error. The coordinate projection `ℝ² → ℝ¹` collapses a nonzero direction in the
unit ball, so no purely multiplicative lower-distance estimate with
`ε < 1` can hold on this bounded infinite set.

**Book Exercise 9.11.** -/
theorem exercise_9_11_additive_error_is_necessary
    {ε : ℝ} (hε : ε < 1) :
    ∃ x ∈ exercise911PositiveTargetCounterexampleSet,
      ∃ y ∈ exercise911PositiveTargetCounterexampleSet,
        ¬ ((1 - ε) * ‖x - y‖ ≤
          ‖exercise911Projection x - exercise911Projection y‖) := by
  let e : EuclideanSpace ℝ (Fin 2) :=
    EuclideanSpace.basisFun (Fin 2) ℝ (1 : Fin 2)
  refine ⟨e, ?_, 0, ?_, ?_⟩
  · simp [exercise911PositiveTargetCounterexampleSet, e]
  · simp [exercise911PositiveTargetCounterexampleSet]
  · have hQ : exercise911Projection e = exercise911Projection 0 := by
      rw [show exercise911Projection e = 0 by
        simpa [e] using exercise911Projection_secondBasis_eq_zero]
      simp
    rw [hQ]
    simp only [sub_self, norm_zero, not_le]
    simpa [e] using sub_pos.mpr hε

end

end HDP.Chapter9

end Source_06_AdditiveJohnsonLindenstrauss

/-! ## Material formerly in `07_MStarBound.lean` -/

section Source_07_MStarBound

/-!
# Book Chapter 9, §9.3.1: the M-star bound

The source's affine Exercise 9.12 is proved first.  A single finite maximum
over pairs with equal matrix image is exactly the supremum over all affine
fibres, and avoids an ill-defined `max_z` over an unbounded ambient space.  The
kernel-section theorem is then an immediate specialization.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! The source first notes that the kernel of an `m × n` matrix has
dimension at least `n - m`.  This is deterministic rank--nullity; no
distributional claim about the kernel is needed. -/

/-- Deterministic dimension bound `dim (ker A) ≥ n - m`.

**Lean implementation helper.** -/
theorem finrank_kernel_toEuclideanLin_ge_sub {m n : ℕ}
    (hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) :
    n - m ≤ Module.finrank ℝ A.toEuclideanLin.ker := by
  have hrank : HDP.Chapter4.euclideanMatrixRank A ≤ m := by
    have h := A.toEuclideanLin.range.finrank_le
    simpa [HDP.Chapter4.euclideanMatrixRank,
      finrank_euclideanSpace_fin] using h
  have hnull := HDP.Chapter4.finrank_ker_toEuclideanLin A
  omega

/-- A random full-row-rank matrix has kernel dimension `n-m`.

**Book Section 9.3.1, after Theorem 9.3.1.** -/
theorem ae_finrank_kernel_eq_sub_of_ae_fullRowRank {m n : ℕ}
    (hmn : m ≤ n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hfull : ∀ᵐ ω ∂μ, HDP.Chapter4.euclideanMatrixRank (A ω) = m) :
    ∀ᵐ ω ∂μ, Module.finrank ℝ (A ω).toEuclideanLin.ker = n - m := by
  filter_upwards [hfull] with ω hω
  have hnull := HDP.Chapter4.finrank_ker_toEuclideanLin (A ω)
  omega

/-- Maximum distance between two points of `T` in the same affine fibre of
the random matrix. This is the finite safe form of
`sup_z diam (T ∩ (z + ker A))`.

**Lean implementation helper.** -/
def finiteAffineFiberDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (fun p : ↥T × ↥T => fun ω =>
      if matrixAction A p.1.1 ω = matrixAction A p.2.1 ω then
        ‖p.1.1 - p.2.1‖ else 0) ω

/-- Diameter of the section through the origin.

**Lean implementation helper.** -/
def finiteKernelSectionDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (fun p : ↥T × ↥T => fun ω =>
      if matrixAction A p.1.1 ω = 0 ∧ matrixAction A p.2.1 ω = 0 then
        ‖p.1.1 - p.2.1‖ else 0) ω

/-- The finite affine fiber diameter is nonnegative.

**Lean implementation helper.** -/
theorem finiteAffineFiberDiameter_nonneg {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : 0 ≤ finiteAffineFiberDiameter A T ω := by
  unfold finiteAffineFiberDiameter HDP.Chapter8.finiteProcessAbsoluteSup
  let p0 : ↥T × ↥T := Classical.choice inferInstance
  exact (abs_nonneg _).trans
    (Finset.le_sup'
      (fun p : ↥T × ↥T =>
        |if matrixAction A p.1.1 ω = matrixAction A p.2.1 ω then
          ‖p.1.1 - p.2.1‖ else 0|)
      (Finset.mem_univ p0))

/-- The finite kernel section diameter is nonnegative.

**Lean implementation helper.** -/
theorem finiteKernelSectionDiameter_nonneg {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) : 0 ≤ finiteKernelSectionDiameter A T ω := by
  unfold finiteKernelSectionDiameter HDP.Chapter8.finiteProcessAbsoluteSup
  let p0 : ↥T × ↥T := Classical.choice inferInstance
  exact (abs_nonneg _).trans
    (Finset.le_sup'
      (fun p : ↥T × ↥T =>
        |if matrixAction A p.1.1 ω = 0 ∧ matrixAction A p.2.1 ω = 0 then
          ‖p.1.1 - p.2.1‖ else 0|)
      (Finset.mem_univ p0))

/-- The finite affine fiber diameter is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteAffineFiberDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] :
    Measurable (finiteAffineFiberDiameter A T) := by
  apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
  intro p
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_matrixAction A hrowsm p.1.1)
      (measurable_matrixAction A hrowsm p.2.1))
    measurable_const measurable_const

/-- The finite kernel section diameter is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteKernelSectionDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T] :
    Measurable (finiteKernelSectionDiameter A T) := by
  apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
  intro p
  have h1 : MeasurableSet {ω | matrixAction A p.1.1 ω = 0} :=
    measurableSet_eq_fun (measurable_matrixAction A hrowsm p.1.1) measurable_const
  have h2 : MeasurableSet {ω | matrixAction A p.2.1 ω = 0} :=
    measurableSet_eq_fun (measurable_matrixAction A hrowsm p.2.1) measurable_const
  exact Measurable.ite (h1.inter h2) measurable_const measurable_const

/-- A kernel section is contained in an affine fibre.

**Lean implementation helper.** -/
theorem finiteKernelSectionDiameter_le_affine {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (ω : Ω) :
    finiteKernelSectionDiameter A T ω ≤ finiteAffineFiberDiameter A T ω := by
  unfold finiteKernelSectionDiameter finiteAffineFiberDiameter
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro p hp
  have hpoint :
      |if matrixAction A p.1.1 ω = 0 ∧
          matrixAction A p.2.1 ω = 0 then
        ‖p.1.1 - p.2.1‖ else 0| ≤
      |if matrixAction A p.1.1 ω = matrixAction A p.2.1 ω then
        ‖p.1.1 - p.2.1‖ else 0| := by
    by_cases hker : matrixAction A p.1.1 ω = 0 ∧
        matrixAction A p.2.1 ω = 0
    · have heq : matrixAction A p.1.1 ω = matrixAction A p.2.1 ω := by
        rw [hker.1, hker.2]
      simp [hker]
    · simp [hker]
  exact hpoint.trans (Finset.le_sup'
    (fun q : ↥T × ↥T =>
      |if matrixAction A q.1.1 ω = matrixAction A q.2.1 ω then
        ‖q.1.1 - q.2.1‖ else 0|) hp)

/-- Deterministic core of the affine M-star argument.

**Lean implementation helper.** -/
theorem finiteAffineFiberDiameter_le {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (ω : Ω) :
    finiteAffineFiberDiameter A T ω ≤
      letI : Nonempty ↥(HDP.Chapter7.differenceFinset T T) :=
        (HDP.Chapter7.differenceFinset_nonempty hT hT).to_subtype
      (Real.sqrt m)⁻¹ *
        finiteMatrixDeviation A (HDP.Chapter7.differenceFinset T T) ω := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  unfold finiteAffineFiberDiameter
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro p hp
  by_cases heq : matrixAction A p.1.1 ω = matrixAction A p.2.1 ω
  · have hdmem : p.1.1 - p.2.1 ∈ D := by
      unfold D HDP.Chapter7.differenceFinset
        HDP.Chapter7.minkowskiSumFinset HDP.Chapter7.negFinset
      apply Finset.mem_image.mpr
      refine ⟨(p.1.1, -p.2.1),
        Finset.mem_product.mpr ⟨p.1.2, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨p.2.1, p.2.2, rfl⟩
      · simp [sub_eq_add_neg]
    have hzero : matrixAction A (p.1.1 - p.2.1) ω = 0 := by
      rw [matrixAction_sub, sub_eq_zero]
      exact heq
    have hdev := abs_matrixDeviationProcess_le_finite A D hdmem ω
    have hsqrtNorm : Real.sqrt m * ‖p.1.1 - p.2.1‖ ≤
        finiteMatrixDeviation A D ω := by
      simpa [matrixDeviationProcess, hzero, abs_of_nonneg,
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)] using hdev
    change |if matrixAction A p.1.1 ω = matrixAction A p.2.1 ω then
        ‖p.1.1 - p.2.1‖ else 0| ≤
      (Real.sqrt m)⁻¹ * finiteMatrixDeviation A D ω
    rw [if_pos heq, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖p.1.1 - p.2.1‖ = (Real.sqrt m)⁻¹ *
          (Real.sqrt m * ‖p.1.1 - p.2.1‖) := by
        field_simp [hsqrt.ne']
      _ ≤ (Real.sqrt m)⁻¹ * finiteMatrixDeviation A D ω :=
        mul_le_mul_of_nonneg_left hsqrtNorm (inv_nonneg.mpr hsqrt.le)
  · change |if matrixAction A p.1.1 ω = matrixAction A p.2.1 ω then
        ‖p.1.1 - p.2.1‖ else 0| ≤
      (Real.sqrt m)⁻¹ * finiteMatrixDeviation A D ω
    rw [if_neg heq, abs_zero]
    exact mul_nonneg (inv_nonneg.mpr hsqrt.le)
      (finiteMatrixDeviation_nonneg A D ω)

/-- Universal constant in Theorem 9.3.1 and Exercise 9.12.

**Book Theorem 9.3.1.** -/
def mStarConstant [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  2 * matrixDeviationConstant

/-- The M-star constant is strictly positive.

**Lean implementation helper.** -/
theorem mStarConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < mStarConstant := mul_pos (by norm_num) matrixDeviationConstant_pos

/-- Affine M-star bound.

**Book Exercise 9.12.** -/
theorem exercise_9_12_affineMStar
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteAffineFiberDiameter A T ω ∂μ) ≤
      mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
        Real.sqrt m := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  let F : Ω → ℝ := finiteMatrixDeviation A D
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have hAffInt : Integrable (finiteAffineFiberDiameter A T) μ := by
    refine (hFint.const_mul (Real.sqrt m)⁻¹).mono'
      (measurable_finiteAffineFiberDiameter A hrowsm T).aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hprod : 0 ≤ (Real.sqrt m)⁻¹ * F ω :=
      mul_nonneg (inv_nonneg.mpr hsqrt.le)
        (finiteMatrixDeviation_nonneg A D ω)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (finiteAffineFiberDiameter_nonneg A T ω),
      abs_of_nonneg hprod, D, F] using
        finiteAffineFiberDiameter_le hm A T hT ω
  have hmono :
      (∫ ω, finiteAffineFiberDiameter A T ω ∂μ) ≤
        ∫ ω, (Real.sqrt m)⁻¹ * F ω ∂μ :=
    integral_mono hAffInt (hFint.const_mul _)
      (fun ω => by
        simpa [D, F] using finiteAffineFiberDiameter_le hm A T hT ω)
  have hmain := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D hD
  have hscale : 0 ≤ (Real.sqrt m)⁻¹ := inv_nonneg.mpr hsqrt.le
  calc
    (∫ ω, finiteAffineFiberDiameter A T ω ∂μ) ≤
        ∫ ω, (Real.sqrt m)⁻¹ * F ω ∂μ := hmono
    _ = (Real.sqrt m)⁻¹ * ∫ ω, F ω ∂μ := integral_const_mul _ _
    _ ≤ (Real.sqrt m)⁻¹ *
        (matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianComplexity D) :=
      mul_le_mul_of_nonneg_left hmain hscale
    _ = mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
        Real.sqrt m := by
      rw [HDP.Chapter7.gaussianComplexity_difference T hT]
      simp [mStarConstant]
      ring

/-- Section through the origin.

**Book Theorem 9.3.1.** -/
theorem theorem_9_3_1_mStar
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) :
    (∫ ω, finiteKernelSectionDiameter A T ω ∂μ) ≤
      mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
        Real.sqrt m := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have hAffInt : Integrable (finiteAffineFiberDiameter A T) μ := by
    refine (hFint.const_mul (Real.sqrt m)⁻¹).mono'
      (measurable_finiteAffineFiberDiameter A hrowsm T).aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hprod : 0 ≤ (Real.sqrt m)⁻¹ * finiteMatrixDeviation A D ω :=
      mul_nonneg (inv_nonneg.mpr hsqrt.le)
        (finiteMatrixDeviation_nonneg A D ω)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (finiteAffineFiberDiameter_nonneg A T ω),
      abs_of_nonneg hprod, D] using
        finiteAffineFiberDiameter_le hm A T hT ω
  have hKerInt : Integrable (finiteKernelSectionDiameter A T) μ := by
    refine hAffInt.mono'
      (measurable_finiteKernelSectionDiameter A hrowsm T).aestronglyMeasurable ?_
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (finiteKernelSectionDiameter_nonneg A T ω),
      abs_of_nonneg (finiteAffineFiberDiameter_nonneg A T ω)] using
        finiteKernelSectionDiameter_le_affine A T ω
  calc
    (∫ ω, finiteKernelSectionDiameter A T ω ∂μ) ≤
        ∫ ω, finiteAffineFiberDiameter A T ω ∂μ :=
      integral_mono hKerInt hAffInt
        (fun ω => finiteKernelSectionDiameter_le_affine A T ω)
    _ ≤ mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
        Real.sqrt m :=
      exercise_9_12_affineMStar hm A hrowsm hsub hiso hindep hfinite
        hK hpsi T hT

/-- Finite differences are monotone in their generating finite set.

**Lean implementation helper.** -/
theorem differenceFinset_mono {n : ℕ}
    {S T : Finset (EuclideanSpace ℝ (Fin n))} (hST : S ⊆ T) :
    HDP.Chapter7.differenceFinset S S ⊆
      HDP.Chapter7.differenceFinset T T := by
  intro z hz
  unfold HDP.Chapter7.differenceFinset HDP.Chapter7.minkowskiSumFinset
    HDP.Chapter7.negFinset at hz ⊢
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_product.mpr ⟨hST hp₁, ?_⟩, rfl⟩
  obtain ⟨y, hy, hpy⟩ := Finset.mem_image.mp hp₂
  exact Finset.mem_image.mpr ⟨y, hST hy, hpy⟩

/-- The finite matrix-deviation supremum is monotone in the index set.

**Lean implementation helper.** -/
theorem finiteMatrixDeviation_mono {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    {S T : Finset (EuclideanSpace ℝ (Fin n))}
    [Nonempty ↑S] [Nonempty ↑T] (hST : S ⊆ T) (ω : Ω) :
    finiteMatrixDeviation A S ω ≤ finiteMatrixDeviation A T ω := by
  unfold finiteMatrixDeviation HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro x _hx
  let y : ↑T := ⟨x.1, hST x.2⟩
  simpa [HDP.Chapter8.finiteEuclideanProcess, y] using
    (Finset.le_sup'
      (fun z : ↑T =>
        |HDP.Chapter8.finiteEuclideanProcess T
          (matrixDeviationProcess A) z ω|)
      (Finset.mem_univ y))

/-- Difference set of the `k`th canonical dense prefix of `T`.

**Lean implementation helper.** -/
def setDenseDifferencePrefix {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (k : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  HDP.Chapter7.differenceFinset (setDensePrefix T k) (setDensePrefix T k)

/-- Every finite prefix of pairwise dense-set differences contains at least the zero difference.

**Lean implementation helper.** -/
theorem setDenseDifferencePrefix_nonempty {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (k : ℕ) :
    (setDenseDifferencePrefix T k).Nonempty :=
  HDP.Chapter7.differenceFinset_nonempty
    (setDensePrefix_nonempty T k) (setDensePrefix_nonempty T k)

/-- Prefixes of pairwise dense-set differences increase with the prefix index.

**Lean implementation helper.** -/
theorem setDenseDifferencePrefix_mono {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    {k l : ℕ} (hkl : k ≤ l) :
    setDenseDifferencePrefix T k ⊆ setDenseDifferencePrefix T l :=
  differenceFinset_mono (setDensePrefix_mono T hkl)

/-- Countable, measurable envelope of matrix deviations over the actual
difference set `T - T`. Dense finite prefixes are used so that no
measurability of an uncountable supremum is assumed.

**Lean implementation helper.** -/
def setDifferenceMatrixDeviationENN {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (ω : Ω) : ℝ≥0∞ :=
  ⨆ k : ℕ,
    letI : Nonempty ↑(setDenseDifferencePrefix T k) :=
      (setDenseDifferencePrefix_nonempty T k).to_subtype
    ENNReal.ofReal (finiteMatrixDeviation A (setDenseDifferencePrefix T k) ω)

/-- The extended-real matrix-deviation envelope over all dense-set differences is measurable.

**Lean implementation helper.** -/
theorem measurable_setDifferenceMatrixDeviationENN {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] :
    Measurable (setDifferenceMatrixDeviationENN A T) := by
  apply Measurable.iSup
  intro k
  letI : Nonempty ↑(setDenseDifferencePrefix T k) :=
    (setDenseDifferencePrefix_nonempty T k).to_subtype
  exact ENNReal.measurable_ofReal.comp
    (measurable_finiteMatrixDeviation A hrowsm (setDenseDifferencePrefix T k))

/-- Monotone convergence transfers Theorem 9.1.1 from finite prefixes to the
actual bounded set.

**Book Theorem 9.1.1.** -/
theorem lintegral_setDifferenceMatrixDeviationENN_le
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (hTne : T.Nonempty) (hTb : Bornology.IsBounded T) :
    (∫⁻ ω, setDifferenceMatrixDeviationENN A T ω ∂μ) ≤
      ENNReal.ofReal (mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T) := by
  let F : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    letI : Nonempty ↑(setDenseDifferencePrefix T k) :=
      (setDenseDifferencePrefix_nonempty T k).to_subtype
    ENNReal.ofReal (finiteMatrixDeviation A (setDenseDifferencePrefix T k) ω)
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    letI : Nonempty ↑(setDenseDifferencePrefix T k) :=
      (setDenseDifferencePrefix_nonempty T k).to_subtype
    exact ENNReal.measurable_ofReal.comp
      (measurable_finiteMatrixDeviation A hrowsm (setDenseDifferencePrefix T k))
  have hFmono : Monotone F := by
    intro k l hkl ω
    letI : Nonempty ↑(setDenseDifferencePrefix T k) :=
      (setDenseDifferencePrefix_nonempty T k).to_subtype
    letI : Nonempty ↑(setDenseDifferencePrefix T l) :=
      (setDenseDifferencePrefix_nonempty T l).to_subtype
    exact ENNReal.ofReal_le_ofReal
      (finiteMatrixDeviation_mono A (setDenseDifferencePrefix_mono T hkl) ω)
  change (∫⁻ ω, ⨆ k, F k ω ∂μ) ≤ _
  rw [lintegral_iSup hFm hFmono]
  apply iSup_le
  intro k
  let P := setDensePrefix T k
  let D := setDenseDifferencePrefix T k
  have hP : P.Nonempty := setDensePrefix_nonempty T k
  have hD : D.Nonempty := setDenseDifferencePrefix_nonempty T k
  letI : Nonempty ↑D := hD.to_subtype
  have hDint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have hD0 : ∀ ω, 0 ≤ finiteMatrixDeviation A D ω :=
    fun ω => finiteMatrixDeviation_nonneg A D ω
  rw [← ofReal_integral_eq_lintegral_ofReal hDint
    (Filter.Eventually.of_forall hD0)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ ω, finiteMatrixDeviation A D ω ∂μ) ≤
        matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianComplexity D :=
      theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso hindep
        hfinite hK hpsi D hD
    _ = mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth P := by
      rw [show D = HDP.Chapter7.differenceFinset P P by rfl,
        HDP.Chapter7.gaussianComplexity_difference P hP]
      simp [mStarConstant]
      ring
    _ ≤ mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T := by
      exact mul_le_mul_of_nonneg_left
        (densePrefix_gaussianWidth_le T hTne hTb k)
        (mul_nonneg mStarConstant_pos.le (sq_nonneg K))

/-- The envelope dominates each pair of canonical dense points.

**Lean implementation helper.** -/
theorem densePair_matrixDeviation_le_setDifferenceMatrixDeviationENN
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (i j : ℕ) (ω : Ω) :
    ENNReal.ofReal |matrixDeviationProcess A
        (setDensePoint T i - setDensePoint T j) ω| ≤
      setDifferenceMatrixDeviationENN A T ω := by
  let k := max i j
  let P := setDensePrefix T k
  let D := setDenseDifferencePrefix T k
  have hD : D.Nonempty := setDenseDifferencePrefix_nonempty T k
  letI : Nonempty ↑D := hD.to_subtype
  have hiP : setDensePoint T i ∈ P :=
    setDensePoint_mem_prefix T (le_max_left i j)
  have hjP : setDensePoint T j ∈ P :=
    setDensePoint_mem_prefix T (le_max_right i j)
  have hijD : setDensePoint T i - setDensePoint T j ∈ D := by
    unfold D setDenseDifferencePrefix HDP.Chapter7.differenceFinset
      HDP.Chapter7.minkowskiSumFinset HDP.Chapter7.negFinset
    apply Finset.mem_image.mpr
    refine ⟨(setDensePoint T i, -setDensePoint T j),
      Finset.mem_product.mpr ⟨hiP, ?_⟩, by simp [sub_eq_add_neg]⟩
    exact Finset.mem_image.mpr ⟨setDensePoint T j, hjP, rfl⟩
  calc
    ENNReal.ofReal |matrixDeviationProcess A
        (setDensePoint T i - setDensePoint T j) ω| ≤
        ENNReal.ofReal (finiteMatrixDeviation A D ω) :=
      ENNReal.ofReal_le_ofReal
        (abs_matrixDeviationProcess_le_finite A D hijD ω)
    _ ≤ setDifferenceMatrixDeviationENN A T ω := by
      unfold setDifferenceMatrixDeviationENN
      exact le_iSup (fun l : ℕ =>
        letI : Nonempty ↑(setDenseDifferencePrefix T l) :=
          (setDenseDifferencePrefix_nonempty T l).to_subtype
        ENNReal.ofReal
          (finiteMatrixDeviation A (setDenseDifferencePrefix T l) ω)) k

/-- Continuity extends the dense-pair estimate in its second coordinate.

**Lean implementation helper.** -/
theorem denseLeft_matrixDeviation_le_setDifferenceMatrixDeviationENN
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    (i : ℕ) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ T) (ω : Ω) :
    ENNReal.ofReal |matrixDeviationProcess A (setDensePoint T i - y) ω| ≤
      setDifferenceMatrixDeviationENN A T ω := by
  let C : ℝ≥0∞ := setDifferenceMatrixDeviationENN A T ω
  by_cases hC : C = ⊤
  · simp [C, hC]
  let f : T → ℝ := fun q =>
    |matrixDeviationProcess A (setDensePoint T i - q.1) ω|
  have hvec : Continuous (fun q : T => setDensePoint T i - q.1) :=
    continuous_const.sub continuous_subtype_val
  have haction : Continuous (fun q : T =>
      matrixAction A (setDensePoint T i - q.1) ω) := by
    change Continuous (fun q : T =>
      (A ω).toEuclideanLin (setDensePoint T i - q.1))
    exact (A ω).toEuclideanLin.toContinuousLinearMap.continuous.comp hvec
  have hf : Continuous f :=
    (haction.norm.sub (continuous_const.mul hvec.norm)).abs
  have hdenseReal : ∀ j, f (setDenseSubtypePoint T j) ≤ C.toReal := by
    intro j
    have hENN := densePair_matrixDeviation_le_setDifferenceMatrixDeviationENN
      A T i j ω
    have hreal := ENNReal.toReal_mono hC hENN
    simpa [f, C, setDensePoint,
      ENNReal.toReal_ofReal (abs_nonneg _)] using hreal
  have hyreal := continuous_le_of_setDenseSubtypePoint_le
    T f hf hdenseReal ⟨y, hy⟩
  have hof := ENNReal.ofReal_le_ofReal hyreal
  calc
    ENNReal.ofReal |matrixDeviationProcess A (setDensePoint T i - y) ω| ≤
        ENNReal.ofReal C.toReal := by simpa [f] using hof
    _ = C := ENNReal.ofReal_toReal hC
    _ = setDifferenceMatrixDeviationENN A T ω := rfl

/-- Every deviation on the actual difference set is dominated by the
countable dense-prefix envelope.

**Lean implementation helper.** -/
theorem abs_matrixDeviationProcess_le_setDifferenceMatrixDeviationENN
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (hy : y ∈ T)
    (ω : Ω) :
    ENNReal.ofReal |matrixDeviationProcess A (x - y) ω| ≤
      setDifferenceMatrixDeviationENN A T ω := by
  let C : ℝ≥0∞ := setDifferenceMatrixDeviationENN A T ω
  by_cases hC : C = ⊤
  · simp [C, hC]
  let g : T → ℝ := fun q => |matrixDeviationProcess A (q.1 - y) ω|
  have hvec : Continuous (fun q : T => q.1 - y) :=
    continuous_subtype_val.sub continuous_const
  have haction : Continuous (fun q : T => matrixAction A (q.1 - y) ω) := by
    change Continuous (fun q : T => (A ω).toEuclideanLin (q.1 - y))
    exact (A ω).toEuclideanLin.toContinuousLinearMap.continuous.comp hvec
  have hg : Continuous g :=
    (haction.norm.sub (continuous_const.mul hvec.norm)).abs
  have hdenseReal : ∀ i, g (setDenseSubtypePoint T i) ≤ C.toReal := by
    intro i
    have hENN := denseLeft_matrixDeviation_le_setDifferenceMatrixDeviationENN
      A T i hy ω
    have hreal := ENNReal.toReal_mono hC hENN
    simpa [g, C, setDensePoint,
      ENNReal.toReal_ofReal (abs_nonneg _)] using hreal
  have hxreal := continuous_le_of_setDenseSubtypePoint_le
    T g hg hdenseReal ⟨x, hx⟩
  have hof := ENNReal.ofReal_le_ofReal hxreal
  calc
    ENNReal.ofReal |matrixDeviationProcess A (x - y) ω| ≤
        ENNReal.ofReal C.toReal := by simpa [g] using hof
    _ = C := ENNReal.ofReal_toReal hC
    _ = setDifferenceMatrixDeviationENN A T ω := rfl

/-- Extended diameter of the part of `T` in one affine measurement fibre.

**Lean implementation helper.** -/
def setAffineFiberDiameterENN {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (x : EuclideanSpace ℝ (Fin n)) (_hx : x ∈ T)
      (y : EuclideanSpace ℝ (Fin n)) (_hy : y ∈ T)
      (_hxy : matrixAction A x ω = matrixAction A y ω),
    ENNReal.ofReal ‖x - y‖

/-- Extended diameter of the section of `T` by the random kernel.

**Lean implementation helper.** -/
def setKernelSectionDiameterENN {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (x : EuclideanSpace ℝ (Fin n)) (_hx : x ∈ T)
      (y : EuclideanSpace ℝ (Fin n)) (_hy : y ∈ T)
      (_hx0 : matrixAction A x ω = 0)
      (_hy0 : matrixAction A y ω = 0),
    ENNReal.ofReal ‖x - y‖

/-- Two points of the set with the same matrix image are separated by at most the affine-fiber diameter.

**Lean implementation helper.** -/
theorem pair_le_setAffineFiberDiameterENN {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : matrixAction A x ω = matrixAction A y ω) :
    ENNReal.ofReal ‖x - y‖ ≤ setAffineFiberDiameterENN A T ω := by
  unfold setAffineFiberDiameterENN
  exact le_iSup_of_le x (le_iSup_of_le hx
    (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl))))

/-- The diameter of the kernel section is bounded by the largest affine-fiber diameter.

**Lean implementation helper.** -/
theorem setKernelSectionDiameterENN_le_affine {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω) :
    setKernelSectionDiameterENN A T ω ≤ setAffineFiberDiameterENN A T ω := by
  unfold setKernelSectionDiameterENN
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hx0
  apply iSup_le
  intro hy0
  exact pair_le_setAffineFiberDiameterENN A T ω hx hy (hx0.trans hy0.symm)

/-- Every actual affine-fibre diameter is controlled by the measurable
dense-prefix deviation on `T - T`.

**Lean implementation helper.** -/
theorem setAffineFiberDiameterENN_le_deviation_div {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T] (ω : Ω) :
    setAffineFiberDiameterENN A T ω ≤
      setDifferenceMatrixDeviationENN A T ω / ENNReal.ofReal (Real.sqrt m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hs0 : ENNReal.ofReal (Real.sqrt m) ≠ 0 := by positivity
  have hstop : ENNReal.ofReal (Real.sqrt m) ≠ ∞ := ENNReal.ofReal_ne_top
  unfold setAffineFiberDiameterENN
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hxy
  rw [ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl hstop)]
  have hzero : matrixAction A (x - y) ω = 0 := by
    rw [matrixAction_sub, hxy, sub_self]
  have hdev := abs_matrixDeviationProcess_le_setDifferenceMatrixDeviationENN
    A T hx hy ω
  have hproc : |matrixDeviationProcess A (x - y) ω| =
      Real.sqrt m * ‖x - y‖ := by
    simp [matrixDeviationProcess, hzero]
  rw [hproc] at hdev
  calc
    ENNReal.ofReal ‖x - y‖ * ENNReal.ofReal (Real.sqrt m) =
        ENNReal.ofReal (Real.sqrt m) * ENNReal.ofReal ‖x - y‖ := by
      rw [mul_comm]
    _ = ENNReal.ofReal (Real.sqrt m * ‖x - y‖) := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    _ ≤ setDifferenceMatrixDeviationENN A T ω := hdev

/-- M-star bound for every affine kernel section. Actual affine-fibre form of Book Exercise 9.12. The expectation is the
authoritative extended integral, so no uncountable-supremum measurability is
hidden.

**Book Exercise 9.12.** -/
theorem exercise_9_12_affineMStar_set
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    (∫⁻ ω, setAffineFiberDiameterENN A T ω ∂μ) ≤
      ENNReal.ofReal (mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T / Real.sqrt m) := by
  letI : Nonempty T := hT.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  let s : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt m)
  let D : Ω → ℝ≥0∞ := setDifferenceMatrixDeviationENN A T
  have hDmeas : Measurable D :=
    measurable_setDifferenceMatrixDeviationENN A hrowsm T
  have hpoint : ∀ ω, setAffineFiberDiameterENN A T ω ≤ D ω / s := by
    intro ω
    simpa [D, s] using setAffineFiberDiameterENN_le_deviation_div hm A T ω
  have hmain := lintegral_setDifferenceMatrixDeviationENN_le hm A hrowsm hsub
    hiso hindep hfinite hK hpsi T hT hTb
  calc
    (∫⁻ ω, setAffineFiberDiameterENN A T ω ∂μ) ≤
        ∫⁻ ω, D ω / s ∂μ := lintegral_mono hpoint
    _ = s⁻¹ * ∫⁻ ω, D ω ∂μ := by
      have hfun : (fun ω => D ω / s) = fun ω => s⁻¹ * D ω := by
        funext ω
        simp [div_eq_mul_inv, mul_comm]
      rw [hfun, MeasureTheory.lintegral_const_mul _ hDmeas]
    _ ≤ s⁻¹ * ENNReal.ofReal (mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth T) := by gcongr
    _ = ENNReal.ofReal (mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth T / Real.sqrt m) := by
      rw [ENNReal.ofReal_div_of_pos hsqrt]
      simp [s, div_eq_mul_inv, mul_comm]

/-- The expected diameter of a random kernel section is bounded by width divided by `sqrt m`. Actual-set form of Book Theorem 9.3.1.

**Book Theorem 9.3.1.** -/
theorem theorem_9_3_1_mStar_set
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    (∫⁻ ω, setKernelSectionDiameterENN A T ω ∂μ) ≤
      ENNReal.ofReal (mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T / Real.sqrt m) := by
  exact (lintegral_mono fun ω => setKernelSectionDiameterENN_le_affine A T ω).trans
    (exercise_9_12_affineMStar_set hm A hrowsm hsub hiso hindep hfinite
      hK hpsi T hT hTb)

/-! For an arbitrary set, a raw pointwise supremum can have hidden
measurability and separability obligations.  The following extended-valued
interface takes the supremum over all nonempty finite subfamilies and is
therefore unconditional and source-honest. -/

/-- Envelope of expected kernel-section diameters over nonempty finite
subfamilies of an arbitrary set.

**Lean implementation helper.** -/
def mStarExpectationEnvelope {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal (∫ ω, finiteKernelSectionDiameter A F ω ∂μ)

/-- Envelope of Gaussian widths over the same finite subfamilies.

**Lean implementation helper.** -/
def gaussianWidthEnvelope {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal (HDP.Chapter7.gaussianWidth F)

/-- Envelope of expected affine-fibre diameters over all nonempty finite
subfamilies of an arbitrary set.

**Lean implementation helper.** -/
def affineMStarExpectationEnvelope {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (hF : F.Nonempty),
    letI : Nonempty ↥F := hF.to_subtype
    ENNReal.ofReal (∫ ω, finiteAffineFiberDiameter A F ω ∂μ)

/-- Finite-subfamily compatibility envelope for . The
source-facing actual affine-fibre theorem is `exercise_9_12_affineMStar_set`.

**Book Exercise 9.12.** -/
theorem exercise_9_12_affineMStar_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    affineMStarExpectationEnvelope (μ := μ) A T ≤
      ENNReal.ofReal
          (mStarConstant * K ^ 2 / Real.sqrt m) *
        gaussianWidthEnvelope T := by
  unfold affineMStarExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  have hmain := exercise_9_12_affineMStar hm A hrowsm hsub hiso hindep
    hfinite hK hpsi F hF
  have hbound : (∫ ω, finiteAffineFiberDiameter A F ω ∂μ) ≤
      (mStarConstant * K ^ 2 / Real.sqrt m) *
        HDP.Chapter7.gaussianWidth F := by
    calc
      (∫ ω, finiteAffineFiberDiameter A F ω ∂μ) ≤
          mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth F /
            Real.sqrt m := hmain
      _ = (mStarConstant * K ^ 2 / Real.sqrt m) *
          HDP.Chapter7.gaussianWidth F := by ring
  have hcoef : 0 ≤ mStarConstant * K ^ 2 / Real.sqrt m :=
    div_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K))
      (Real.sqrt_nonneg m)
  have hwidth : ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
      gaussianWidthEnvelope T := by
    unfold gaussianWidthEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  calc
    ENNReal.ofReal (∫ ω, finiteAffineFiberDiameter A F ω ∂μ) ≤
        ENNReal.ofReal ((mStarConstant * K ^ 2 / Real.sqrt m) *
          HDP.Chapter7.gaussianWidth F) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
        ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
        gaussianWidthEnvelope T := by gcongr

/-- Finite-subfamily compatibility envelope for . The
source-facing actual kernel-section theorem is `theorem_9_3_1_mStar_set`.

**Book Theorem 9.3.1.** -/
theorem theorem_9_3_1_mStar_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    mStarExpectationEnvelope (μ := μ) A T ≤
      ENNReal.ofReal
          (mStarConstant * K ^ 2 / Real.sqrt m) *
        gaussianWidthEnvelope T := by
  unfold mStarExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↥F := hF.to_subtype
  have hmain := theorem_9_3_1_mStar hm A hrowsm hsub hiso hindep
    hfinite hK hpsi F hF
  have hbound : (∫ ω, finiteKernelSectionDiameter A F ω ∂μ) ≤
      (mStarConstant * K ^ 2 / Real.sqrt m) *
        HDP.Chapter7.gaussianWidth F := by
    calc
      (∫ ω, finiteKernelSectionDiameter A F ω ∂μ) ≤
          mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth F /
            Real.sqrt m := hmain
      _ = (mStarConstant * K ^ 2 / Real.sqrt m) *
          HDP.Chapter7.gaussianWidth F := by ring
  have hcoef : 0 ≤ mStarConstant * K ^ 2 / Real.sqrt m :=
    div_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K))
      (Real.sqrt_nonneg m)
  have hwidth : ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
      gaussianWidthEnvelope T := by
    unfold gaussianWidthEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  calc
    ENNReal.ofReal (∫ ω, finiteKernelSectionDiameter A F ω ∂μ) ≤
        ENNReal.ofReal ((mStarConstant * K ^ 2 / Real.sqrt m) *
          HDP.Chapter7.gaussianWidth F) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
        ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
        gaussianWidthEnvelope T := by gcongr

/-- The finite `M*` error scale.

**Lean implementation helper.** -/
def mStarError [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (K : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
    Real.sqrt m

/-- Quantitative algebra behind Remark 9.3.3, including the zero-diameter
branch. The sample size is expressed using the exact finite width-effective
dimension introduced in Remark 9.2.5.

**Book Remark 9.3.3.** -/
theorem remark_9_3_3_mStarError_le
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (hm : 0 < m) {K ε : ℝ} (hε : 0 < ε)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hsize : mStarConstant ^ 2 * K ^ 4 *
        widthEffectiveDimension T / ε ^ 2 ≤ (m : ℝ)) :
    mStarError (m := m) K T ≤
      ε * HDP.Chapter7.finiteEuclideanDiameter T := by
  let D := HDP.Chapter7.finiteEuclideanDiameter T
  let w := HDP.Chapter7.gaussianWidth T
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  have hw0 : 0 ≤ w := HDP.Chapter7.gaussianWidth_nonneg T hT
  have hD0 : 0 ≤ D := HDP.Chapter7.finiteEuclideanDiameter_nonneg T
  by_cases hD : D = 0
  · have hw : w = 0 := by
      simpa [w, D] using
        gaussianWidth_eq_zero_of_finiteEuclideanDiameter_eq_zero T hT
          (by simpa [D] using hD)
    simp [mStarError, w, D, hw, hD]
  · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD)
    have hsize' : mStarConstant ^ 2 * K ^ 4 *
        (w ^ 2 / D ^ 2) / ε ^ 2 ≤ (m : ℝ) := by
      simpa [widthEffectiveDimension, D, w, hD] using hsize
    have hsize₁ : mStarConstant ^ 2 * K ^ 4 *
        (w ^ 2 / D ^ 2) ≤ (m : ℝ) * ε ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hε)).mp hsize'
    have hsize₂ : (mStarConstant ^ 2 * K ^ 4 * w ^ 2) / D ^ 2 ≤
        (m : ℝ) * ε ^ 2 := by
      simpa [mul_div_assoc] using hsize₁
    have hpoly : mStarConstant ^ 2 * K ^ 4 * w ^ 2 ≤
        ((m : ℝ) * ε ^ 2) * D ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hDpos)).mp hsize₂
    have hleft : 0 ≤ mStarConstant * K ^ 2 * w :=
      mul_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K)) hw0
    have hright : 0 ≤ ε * D * Real.sqrt m := by positivity
    have hsq : (mStarConstant * K ^ 2 * w) ^ 2 ≤
        (ε * D * Real.sqrt m) ^ 2 := by
      nlinarith [Real.sq_sqrt hm0]
    have hlinear : mStarConstant * K ^ 2 * w ≤
        ε * D * Real.sqrt m :=
      (sq_le_sq₀ hleft hright).mp hsq
    change mStarConstant * K ^ 2 * w / Real.sqrt m ≤ ε * D
    exact (div_le_iff₀ hsqrt).mpr (by simpa [mul_assoc] using hlinear)

/-- Effective-dimension shrinkage endpoint.

**Book Remark 9.3.3.** -/
theorem remark_9_3_3_effectiveDimension
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K ε : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hε : 0 < ε)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty)
    (hsize : mStarConstant ^ 2 * K ^ 4 *
        widthEffectiveDimension T / ε ^ 2 ≤ (m : ℝ)) :
    (∫ ω, finiteKernelSectionDiameter A T ω ∂μ) ≤
      ε * HDP.Chapter7.finiteEuclideanDiameter T := by
  exact (theorem_9_3_1_mStar hm A hrowsm hsub hiso hindep hfinite
    hK hpsi T hT).trans
      (remark_9_3_3_mStarError_le hm hε T hT hsize)

/-- The real-valued M-star error scale for a nonempty bounded arbitrary set.
Its width is the safe real wrapper of the authoritative ENN envelope.

**Lean implementation helper.** -/
def setMStarError [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (K : ℝ) (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  mStarConstant * K ^ 2 *
    HDP.Chapter8.euclideanSetGaussianWidth T / Real.sqrt m

/-- Arbitrary-set algebra behind Remark 9.3.3.

**Book Remark 9.3.3.** -/
theorem remark_9_3_3_setMStarError_le
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {m n : ℕ} (hm : 0 < m) {K ε : ℝ} (hε : 0 < ε)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hdiam : 0 < Metric.diam T)
    (hsize : mStarConstant ^ 2 * K ^ 4 *
        setWidthEffectiveDimension T / ε ^ 2 ≤ (m : ℝ)) :
    setMStarError (m := m) K T ≤ ε * Metric.diam T := by
  let D := Metric.diam T
  let w := HDP.Chapter8.euclideanSetGaussianWidth T
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hDpos : 0 < D := by simpa [D] using hdiam
  have hsize' : mStarConstant ^ 2 * K ^ 4 *
      (w ^ 2 / D ^ 2) / ε ^ 2 ≤ (m : ℝ) := by
    simpa [setWidthEffectiveDimension, D, w, hDpos.ne'] using hsize
  have hsize₁ : mStarConstant ^ 2 * K ^ 4 *
      (w ^ 2 / D ^ 2) ≤ (m : ℝ) * ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp hsize'
  have hsize₂ : (mStarConstant ^ 2 * K ^ 4 * w ^ 2) / D ^ 2 ≤
      (m : ℝ) * ε ^ 2 := by
    simpa [mul_div_assoc] using hsize₁
  have hpoly : mStarConstant ^ 2 * K ^ 4 * w ^ 2 ≤
      ((m : ℝ) * ε ^ 2) * D ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hDpos)).mp hsize₂
  have hleft : 0 ≤ mStarConstant * K ^ 2 * w :=
    mul_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K)) hw0
  have hright : 0 ≤ ε * D * Real.sqrt m := by positivity
  have hsq : (mStarConstant * K ^ 2 * w) ^ 2 ≤
      (ε * D * Real.sqrt m) ^ 2 := by
    nlinarith [Real.sq_sqrt hm0]
  have hlinear : mStarConstant * K ^ 2 * w ≤
      ε * D * Real.sqrt m :=
    (sq_le_sq₀ hleft hright).mp hsq
  change mStarConstant * K ^ 2 * w / Real.sqrt m ≤ ε * D
  exact (div_le_iff₀ hsqrt).mpr (by simpa [mul_assoc] using hlinear)

/-- The M-star bound is nontrivial once codimension dominates effective dimension. Actual nonempty bounded-set endpoint. The
positive-diameter hypothesis is the missing guard needed by the printed
effective-dimension quotient.

**Book Remark 9.3.3.** -/
theorem remark_9_3_3_effectiveDimension_set
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K ε : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hε : 0 < ε)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTne : T.Nonempty) (hTb : Bornology.IsBounded T)
    (hdiam : 0 < Metric.diam T)
    (hsize : mStarConstant ^ 2 * K ^ 4 *
        setWidthEffectiveDimension T / ε ^ 2 ≤ (m : ℝ)) :
    (∫⁻ ω, setKernelSectionDiameterENN A T ω ∂μ) ≤
      ENNReal.ofReal (ε * Metric.diam T) := by
  have hmain := theorem_9_3_1_mStar_set hm A hrowsm hsub hiso hindep
    hfinite hK hpsi T hTne hTb
  have herr := remark_9_3_3_setMStarError_le hm hε T hdiam hsize
  exact hmain.trans (ENNReal.ofReal_le_ofReal (by
    simpa [setMStarError] using herr))

/-- Finite-subfamily compatibility envelope for Book Remark 9.3.3. The
source-facing result is `remark_9_3_3_effectiveDimension_set`.

**Book Remark 9.3.3.** -/
theorem remark_9_3_3_effectiveDimension_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K ε : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hε : 0 < ε)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTne : T.Nonempty) (hTb : Bornology.IsBounded T)
    (hdiam : 0 < Metric.diam T)
    (hsize : mStarConstant ^ 2 * K ^ 4 *
        setWidthEffectiveDimension T / ε ^ 2 ≤ (m : ℝ)) :
    mStarExpectationEnvelope (μ := μ) A T ≤
      ENNReal.ofReal (ε * Metric.diam T) := by
  have hmain := theorem_9_3_1_mStar_envelope hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T
  have htop := HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top hTne hTb
  have hwidthEq : gaussianWidthEnvelope T =
      ENNReal.ofReal (HDP.Chapter8.euclideanSetGaussianWidth T) := by
    change HDP.Chapter8.euclideanSetGaussianWidthENN T =
      ENNReal.ofReal
        (HDP.Chapter8.euclideanSetGaussianWidthENN T).toReal
    exact (ENNReal.ofReal_toReal htop).symm
  have hcoef : 0 ≤ mStarConstant * K ^ 2 / Real.sqrt m :=
    div_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K))
      (Real.sqrt_nonneg m)
  have herr := remark_9_3_3_setMStarError_le hm hε T hdiam hsize
  calc
    mStarExpectationEnvelope (μ := μ) A T ≤
        ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
          gaussianWidthEnvelope T := hmain
    _ = ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
        ENNReal.ofReal (HDP.Chapter8.euclideanSetGaussianWidth T) := by
      rw [hwidthEq]
    _ = ENNReal.ofReal ((mStarConstant * K ^ 2 / Real.sqrt m) *
        HDP.Chapter8.euclideanSetGaussianWidth T) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ = ENNReal.ofReal (setMStarError (m := m) K T) := by
      congr 1
      simp [setMStarError]
      ring
    _ ≤ ENNReal.ofReal (ε * Metric.diam T) :=
      ENNReal.ofReal_le_ofReal herr

/-- Rank--nullity form of the dimension comparison in Remark 9.3.3.

**Book Remark 9.3.3.** -/
theorem fullRowRank_kernelDimension_add_le {m n : ℕ}
    (hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (hfull : HDP.Chapter4.euclideanMatrixRank A = m)
    {c d : ℝ} (hcodim : c * d ≤ m) :
    (Module.finrank ℝ A.toEuclideanLin.ker : ℝ) + c * d ≤ n := by
  have hnull := HDP.Chapter4.finrank_ker_toEuclideanLin A
  have hker : Module.finrank ℝ A.toEuclideanLin.ker = n - m := by omega
  rw [hker, Nat.cast_sub hmn]
  linarith

/-- The actual cross-polytope body `B₁ⁿ`, expressed on Mathlib's Euclidean
space without replacing it by its finite vertex set.

**Lean implementation helper.** -/
def crossPolytopeBody (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∑ i, |x i| ≤ 1}

/-- Membership in the cross-polytope is equivalent to having `ℓ¹` norm at most one.

**Lean implementation helper.** -/
@[simp] theorem mem_crossPolytopeBody_iff {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ crossPolytopeBody n ↔
      HDP.Chapter1.lpNorm 1 (fun i => x i) ≤ 1 := by
  simp [crossPolytopeBody, HDP.Chapter1.lpNorm_one]

/-- The cross-polytope contains the origin and is therefore nonempty.

**Lean implementation helper.** -/
theorem crossPolytopeBody_nonempty (n : ℕ) :
    (crossPolytopeBody n).Nonempty := by
  exact ⟨0, by simp [crossPolytopeBody]⟩

/-- The cross-polytope body is contained in the Euclidean unit ball. This
is the boundedness input needed by the actual-set M-star theorem.

**Lean implementation helper.** -/
theorem crossPolytopeBody_isBounded (n : ℕ) :
    Bornology.IsBounded (crossPolytopeBody n) := by
  apply (Metric.isBounded_iff_subset_closedBall 0).2
  refine ⟨1, ?_⟩
  intro x hx
  have h21 : HDP.Chapter1.lpNorm 2 (fun i => x i) ≤
      HDP.Chapter1.lpNorm 1 (fun i => x i) :=
    HDP.Chapter1.lpNorm_anti (p := (1 : ℝ)) (q := (2 : ℝ))
      (by norm_num) (by norm_num) _
  have h1 : HDP.Chapter1.lpNorm 1 (fun i => x i) ≤ 1 :=
    (mem_crossPolytopeBody_iff x).1 hx
  rw [Metric.mem_closedBall, dist_zero_right,
    ← HDP.Chapter1.lpNorm_two_eq_euclidean]
  exact h21.trans h1

/-- The finite symmetric coordinate-vertex set `{ ±eᵢ }`.

**Lean implementation helper.** -/
def finiteCrossPolytopeVertices (n : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  (Finset.univ.image (fun i : Fin n =>
      EuclideanSpace.basisFun (Fin n) ℝ i)) ∪
    (Finset.univ.image (fun i : Fin n =>
      -EuclideanSpace.basisFun (Fin n) ℝ i))

/-- In positive dimension, the signed coordinate vertex set of the cross-polytope is nonempty.

**Lean implementation helper.** -/
theorem finiteCrossPolytopeVertices_nonempty {n : ℕ} (hn : 0 < n) :
    (finiteCrossPolytopeVertices n).Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨EuclideanSpace.basisFun (Fin n) ℝ i, ?_⟩
  simp [finiteCrossPolytopeVertices]

/-- The support function of the symmetric coordinate vertices is the
coordinate sup norm.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_finiteCrossPolytopeVertices
    {n : ℕ} (hn : 0 < n) (g : EuclideanSpace ℝ (Fin n)) :
    HDP.Chapter7.finiteGaussianSupport (finiteCrossPolytopeVertices n) g =
      Finset.univ.sup'
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
        (fun i : Fin n => |g i|) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let V := finiteCrossPolytopeVertices n
  have hV : V.Nonempty := finiteCrossPolytopeVertices_nonempty hn
  rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' V hV]
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    change x ∈ finiteCrossPolytopeVertices n at hx
    rw [finiteCrossPolytopeVertices, Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hcoord : inner ℝ g (EuclideanSpace.basisFun (Fin n) ℝ i) =
          g i := by simp [PiLp.inner_apply]
      rw [hcoord]
      exact (le_abs_self _).trans
        (Finset.le_sup' (fun j : Fin n => |g j|) hi)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hcoord : inner ℝ g (-EuclideanSpace.basisFun (Fin n) ℝ i) =
          -g i := by simp [PiLp.inner_apply]
      rw [hcoord]
      exact (neg_le_abs _).trans
        (Finset.le_sup' (fun j : Fin n => |g j|) hi)
  · apply (Finset.sup'_le_iff Finset.univ_nonempty
      (fun i : Fin n => |g i|)).mpr
    intro i hi
    have hplus : EuclideanSpace.basisFun (Fin n) ℝ i ∈ V := by
      simp [V, finiteCrossPolytopeVertices]
    have hminus : -EuclideanSpace.basisFun (Fin n) ℝ i ∈ V := by
      simp [V, finiteCrossPolytopeVertices]
    have hp := HDP.Chapter7.inner_le_finiteGaussianSupport V hV hplus g
    have hm := HDP.Chapter7.inner_le_finiteGaussianSupport V hV hminus g
    have hcoordPlus :
        inner ℝ g (EuclideanSpace.basisFun (Fin n) ℝ i) = g i := by
      simp [PiLp.inner_apply]
    have hcoordMinus :
        inner ℝ g (-EuclideanSpace.basisFun (Fin n) ℝ i) = -g i := by
      simp [PiLp.inner_apply]
    rw [hcoordPlus] at hp
    rw [hcoordMinus] at hm
    rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' V hV] at hp hm
    rw [abs_le]
    constructor <;> linarith

/-- The Gaussian width of the signed coordinate vertices is the expected maximum absolute Gaussian coordinate.

**Lean implementation helper.** -/
theorem gaussianWidth_finiteCrossPolytopeVertices
    {n : ℕ} (hn : 0 < n) :
    HDP.Chapter7.gaussianWidth (finiteCrossPolytopeVertices n) =
      HDP.Chapter7.crossPolytopeGaussianWidth n := by
  rw [HDP.Chapter7.gaussianWidth,
    HDP.Chapter7.crossPolytopeGaussianWidth, dif_pos hn]
  simp_rw [finiteGaussianSupport_finiteCrossPolytopeVertices hn]

/-- The coordinate sup norm is the support function of the signed coordinate
vertices.

**Lean implementation helper.** -/
theorem linftyNorm_eq_finiteGaussianSupport_crossPolytopeVertices
    {n : ℕ} (hn : 0 < n) (g : EuclideanSpace ℝ (Fin n)) :
    HDP.Chapter1.linftyNorm (fun i => g i) =
      HDP.Chapter7.finiteGaussianSupport
        (finiteCrossPolytopeVertices n) g := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [finiteGaussianSupport_finiteCrossPolytopeVertices hn]
  let M := Finset.univ.sup'
    (Finset.univ_nonempty_iff.mpr inferInstance)
      (fun i : Fin n => |g i|)
  have hM0 : 0 ≤ M := by
    let i : Fin n := Classical.arbitrary (Fin n)
    exact (abs_nonneg (g i)).trans
      (Finset.le_sup' (fun j : Fin n => |g j|) (Finset.mem_univ i))
  apply le_antisymm
  · rw [HDP.Chapter1.linftyNorm_le_iff hM0]
    intro i
    exact Finset.le_sup' (fun j : Fin n => |g j|) (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i _hi
    exact (HDP.Chapter1.linftyNorm_le_iff
      (HDP.Chapter1.linftyNorm_nonneg (fun j => g j))).mp le_rfl i

/-- Every point of the full `B₁` body has support at most the support of its
signed coordinate vertices.

**Lean implementation helper.** -/
theorem inner_le_finiteGaussianSupport_crossPolytopeVertices
    {n : ℕ} (hn : 0 < n)
    {x g : EuclideanSpace ℝ (Fin n)} (hx : x ∈ crossPolytopeBody n) :
    inner ℝ g x ≤ HDP.Chapter7.finiteGaussianSupport
      (finiteCrossPolytopeVertices n) g := by
  have hxlp : HDP.Chapter1.lpNorm 1 (fun i => x i) ≤ 1 :=
    (mem_crossPolytopeBody_iff x).mp hx
  have hh := HDP.Chapter1.holder_top_one
    (fun i => g i) (fun i => x i)
  calc
    inner ℝ g x = HDP.Chapter1.dotProduct
        (fun i => g i) (fun i => x i) := by
      simp [HDP.Chapter1.dotProduct, PiLp.inner_apply, mul_comm]
    _ ≤ |HDP.Chapter1.dotProduct
        (fun i => g i) (fun i => x i)| := le_abs_self _
    _ ≤ HDP.Chapter1.linftyNorm (fun i => g i) *
        HDP.Chapter1.lpNorm 1 (fun i => x i) := hh
    _ ≤ HDP.Chapter1.linftyNorm (fun i => g i) * 1 :=
      mul_le_mul_of_nonneg_left hxlp
        (HDP.Chapter1.linftyNorm_nonneg (fun i => g i))
    _ = HDP.Chapter7.finiteGaussianSupport
        (finiteCrossPolytopeVertices n) g := by
      rw [mul_one,
        linftyNorm_eq_finiteGaussianSupport_crossPolytopeVertices hn]

/-- A finite subset of the cross-polytope has Gaussian support no larger than that of its signed vertices.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_le_crossPolytopeVertices_of_subset_body
    {n : ℕ} (hn : 0 < n)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (hsub : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆
      crossPolytopeBody n) (g : EuclideanSpace ℝ (Fin n)) :
    HDP.Chapter7.finiteGaussianSupport F g ≤
      HDP.Chapter7.finiteGaussianSupport
        (finiteCrossPolytopeVertices n) g := by
  rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF]
  apply Finset.sup'_le
  intro x hx
  exact inner_le_finiteGaussianSupport_crossPolytopeVertices hn (hsub hx)

/-- Every finite subset of the cross-polytope has Gaussian width bounded by the cross-polytope width.

**Lean implementation helper.** -/
theorem gaussianWidth_le_crossPolytopeGaussianWidth_of_subset_body
    {n : ℕ} (hn : 0 < n)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (hsub : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆
      crossPolytopeBody n) :
    HDP.Chapter7.gaussianWidth F ≤
      HDP.Chapter7.crossPolytopeGaussianWidth n := by
  rw [← gaussianWidth_finiteCrossPolytopeVertices hn]
  exact integral_mono (HDP.Chapter7.integrable_finiteGaussianSupport F)
    (HDP.Chapter7.integrable_finiteGaussianSupport
      (finiteCrossPolytopeVertices n))
    (finiteGaussianSupport_le_crossPolytopeVertices_of_subset_body
      hn F hF hsub)

/-- The Gaussian-width envelope of the entire `B₁` body, not just its
vertices, is controlled by the exact cross-polytope support integral.

**Lean implementation helper.** -/
theorem gaussianWidthEnvelope_crossPolytopeBody_le
    {n : ℕ} (hn : 0 < n) :
    gaussianWidthEnvelope (crossPolytopeBody n) ≤
      ENNReal.ofReal (HDP.Chapter7.crossPolytopeGaussianWidth n) := by
  unfold gaussianWidthEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  exact ENNReal.ofReal_le_ofReal
    (gaussianWidth_le_crossPolytopeGaussianWidth_of_subset_body
      hn F hF hFT)

/-- Safe real form of the preceding extended-width estimate.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidth_crossPolytopeBody_le
    {n : ℕ} (hn : 0 < n) :
    HDP.Chapter8.euclideanSetGaussianWidth (crossPolytopeBody n) ≤
      HDP.Chapter7.crossPolytopeGaussianWidth n := by
  have henn : HDP.Chapter8.euclideanSetGaussianWidthENN
        (crossPolytopeBody n) ≤
      ENNReal.ofReal (HDP.Chapter7.crossPolytopeGaussianWidth n) := by
    simpa [gaussianWidthEnvelope,
      HDP.Chapter8.euclideanSetGaussianWidthENN] using
      gaussianWidthEnvelope_crossPolytopeBody_le hn
  have hw0 : 0 ≤ HDP.Chapter7.crossPolytopeGaussianWidth n := by
    rw [← gaussianWidth_finiteCrossPolytopeVertices hn]
    exact HDP.Chapter7.gaussianWidth_nonneg _
      (finiteCrossPolytopeVertices_nonempty hn)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top henn
  simpa [HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal hw0] using hreal

/-- Numerical width estimate used in Example 9.3.2 for the cross-polytope.
The geometric section is supplied by Theorem 9.3.1; this lemma discharges the
remaining Gaussian-maximum calculation.

**Book Example 9.3.2.** -/
theorem example_9_3_2_crossPolytope_width_numerics
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (k : ℕ) {m : ℕ} (hm : 0 < m) {K : ℝ} (_hK : 0 ≤ K) :
    mStarConstant * K ^ 2 *
        HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) / Real.sqrt m ≤
      mStarConstant * K ^ 2 *
        Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) / Real.sqrt m := by
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (HDP.Chapter7.crossPolytopeGaussianWidth_upper k)
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K))) hsqrt.le

/-- Fully proved finite symmetric-vertex endpoint.
This is an actual M-star section bound for `{ ±eᵢ }`. It deliberately does
not identify this finite section with `B₁ⁿ ∩ ker A`; that convex-hull
identification would require a separate compact exhaustion/convexification
theorem for the arbitrary-set supremum.

**Book Example 9.3.2.** -/
theorem example_9_3_2_crossPolytopeVertices_mStar
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) (k : ℕ)
    (A : HDP.RandomMatrix (Fin m) (Fin (k + 2)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K) :
    let V := finiteCrossPolytopeVertices (k + 2)
    letI : Nonempty ↥V := (finiteCrossPolytopeVertices_nonempty
      (show 0 < k + 2 by omega)).to_subtype
    (∫ ω, finiteKernelSectionDiameter A V ω ∂μ) ≤
      mStarConstant * K ^ 2 *
        Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) / Real.sqrt m := by
  dsimp only
  let V := finiteCrossPolytopeVertices (k + 2)
  have hV : V.Nonempty := finiteCrossPolytopeVertices_nonempty (by omega)
  letI : Nonempty ↥V := hV.to_subtype
  calc
    (∫ ω, finiteKernelSectionDiameter A V ω ∂μ) ≤
        mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth V /
          Real.sqrt m :=
      theorem_9_3_1_mStar hm A hrowsm hsub hiso hindep hfinite
        hK hpsi V hV
    _ = mStarConstant * K ^ 2 *
        HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) /
          Real.sqrt m := by
      rw [gaussianWidth_finiteCrossPolytopeVertices (by omega)]
    _ ≤ mStarConstant * K ^ 2 *
        Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) / Real.sqrt m :=
      example_9_3_2_crossPolytope_width_numerics k hm hK.le

/-- A random high-dimensional section of the cross-polytope has diameter `O(sqrt(log n/n))`. Actual full-body endpoint. The random section is
the genuine set `B₁^(k+2) ∩ ker A`, rather than a finite-family proxy.

**Book Example 9.3.2.** -/
theorem example_9_3_2_crossPolytopeBody_mStar
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) (k : ℕ)
    (A : HDP.RandomMatrix (Fin m) (Fin (k + 2)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K) :
    (∫⁻ ω, setKernelSectionDiameterENN A
        (crossPolytopeBody (k + 2)) ω ∂μ) ≤
      ENNReal.ofReal (mStarConstant * K ^ 2 *
        Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) / Real.sqrt m) := by
  have hmain := theorem_9_3_1_mStar_set hm A hrowsm hsub hiso hindep
    hfinite hK hpsi (crossPolytopeBody (k + 2))
    (crossPolytopeBody_nonempty _) (crossPolytopeBody_isBounded _)
  have hwidth := euclideanSetGaussianWidth_crossPolytopeBody_le
    (show 0 < k + 2 by omega)
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hscale :
      mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth
            (crossPolytopeBody (k + 2)) / Real.sqrt m ≤
        mStarConstant * K ^ 2 *
          HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) /
            Real.sqrt m := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwidth
        (mul_nonneg mStarConstant_pos.le (sq_nonneg K))) hsqrt.le
  have hnum := hscale.trans
    (example_9_3_2_crossPolytope_width_numerics k hm hK.le)
  exact hmain.trans (ENNReal.ofReal_le_ofReal hnum)

/-- Finite-subfamily compatibility envelope for Book Example 9.3.2. The
source-facing actual-body result is `example_9_3_2_crossPolytopeBody_mStar`.

**Book Example 9.3.2.** -/
theorem example_9_3_2_crossPolytopeBody_mStar_envelope
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m) (k : ℕ)
    (A : HDP.RandomMatrix (Fin m) (Fin (k + 2)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K) :
    mStarExpectationEnvelope (μ := μ) A
        (crossPolytopeBody (k + 2)) ≤
      ENNReal.ofReal (mStarConstant * K ^ 2 *
        Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) / Real.sqrt m) := by
  have hmain := theorem_9_3_1_mStar_envelope hm A hrowsm hsub hiso
    hindep hfinite hK hpsi (crossPolytopeBody (k + 2))
  have hwidth := gaussianWidthEnvelope_crossPolytopeBody_le
    (show 0 < k + 2 by omega)
  have hcoef : 0 ≤ mStarConstant * K ^ 2 / Real.sqrt m :=
    div_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K))
      (Real.sqrt_nonneg m)
  have hnum :
      (mStarConstant * K ^ 2 / Real.sqrt m) *
          HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) ≤
        mStarConstant * K ^ 2 *
          Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) /
            Real.sqrt m := by
    calc
      (mStarConstant * K ^ 2 / Real.sqrt m) *
          HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) =
          mStarConstant * K ^ 2 *
            HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) /
              Real.sqrt m := by ring
      _ ≤ mStarConstant * K ^ 2 *
          Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) /
            Real.sqrt m :=
        example_9_3_2_crossPolytope_width_numerics k hm hK.le
  calc
    mStarExpectationEnvelope (μ := μ) A
        (crossPolytopeBody (k + 2)) ≤
        ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
          gaussianWidthEnvelope (crossPolytopeBody (k + 2)) := hmain
    _ ≤ ENNReal.ofReal (mStarConstant * K ^ 2 / Real.sqrt m) *
        ENNReal.ofReal
          (HDP.Chapter7.crossPolytopeGaussianWidth (k + 2)) := by
      gcongr
    _ = ENNReal.ofReal ((mStarConstant * K ^ 2 / Real.sqrt m) *
        HDP.Chapter7.crossPolytopeGaussianWidth (k + 2)) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (mStarConstant * K ^ 2 *
        Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) /
          Real.sqrt m) := ENNReal.ofReal_le_ofReal hnum

end

end HDP.Chapter9

end Source_07_MStarBound

/-! ## Material formerly in `08_EscapeTheorem.lean` -/

section Source_08_EscapeTheorem

/-!
# Book Chapter 9, §9.3.2: escape through a mesh

The conclusion is stated as an upper bound on the failure event
`T ∩ ker A != empty`.  This is equivalent to the source's success-probability
form and avoids subtraction in `ENNReal`.  The quantitative theorem retains
both characteristic dependences: sample size `K^4 w(T)^2` and exponent
`-c m / K^4`.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The event that an arbitrary set meets the random kernel. The set need
not be measurable: the escape theorem controls its outer measure by a
countable measurable deviation event.

**Lean implementation helper.** -/
def kernelHits {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω) : Prop :=
  ∃ x ∈ T, matrixAction A x ω = 0

/-- The event that a finite set meets the random kernel.

**Lean implementation helper.** -/
def finiteKernelHits {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (ω : Ω) : Prop :=
  ∃ x, x ∈ T ∧ matrixAction A x ω = 0

/-- For a finite set, the event that the random kernel meets the set is measurable.

**Lean implementation helper.** -/
theorem measurableSet_finiteKernelHits {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    MeasurableSet {ω | finiteKernelHits A T ω} := by
  classical
  have hU : MeasurableSet
      (⋃ x : ↥T, {ω | matrixAction A x.1 ω = 0}) := by
    exact MeasurableSet.iUnion fun x =>
      measurableSet_eq_fun (measurable_matrixAction A hrowsm x.1)
        measurable_const
  convert hU using 1
  ext ω
  simp [finiteKernelHits]

/-- A nonempty finite subset of the unit sphere has radius one.

**Lean implementation helper.** -/
theorem finiteRadius_eq_one_of_unit {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hsphere : ∀ x ∈ T, ‖x‖ = 1) :
    HDP.Chapter7.finiteRadius T = 1 := by
  rw [HDP.Chapter7.finiteRadius_eq_sup' T hT]
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    exact (hsphere x hx).le
  · obtain ⟨x, hx⟩ := hT
    rw [← hsphere x hx]
    exact Finset.le_sup' norm hx

/-- If the kernel meets a unit-sphere set, its deviation supremum is at least
`sqrt m`.

**Lean implementation helper.** -/
theorem sqrt_le_finiteMatrixDeviation_of_kernelHits {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hsphere : ∀ x ∈ T, ‖x‖ = 1) (ω : Ω)
    (hhit : finiteKernelHits A T ω) :
    Real.sqrt m ≤ finiteMatrixDeviation A T ω := by
  obtain ⟨x, hx, hzero⟩ := hhit
  have hdev := abs_matrixDeviationProcess_le_finite A T hx ω
  simpa [matrixDeviationProcess, hzero, hsphere x hx,
    abs_of_nonneg (Real.sqrt_nonneg m)] using hdev

/-- Tail-parameter form of the escape argument, corresponding directly to
display (9.15).

**Book Equation (9.15).** -/
theorem escape_of_matrixDeviation_threshold
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K u : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hu : 0 ≤ u)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty)
    (hsphere : ∀ x ∈ T, ‖x‖ = 1)
    (hthreshold : matrixDeviationHighProbabilityConstant * K ^ 2 *
        (HDP.Chapter7.gaussianWidth T +
          u * HDP.Chapter7.finiteRadius T) < Real.sqrt m) :
    μ {ω | finiteKernelHits A T ω} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  have htail := remark_9_1_4_matrixDeviation_highProbability hm A hrowsm
    hsub hiso hindep hfinite hK hpsi hu T hT
  calc
    μ {ω | finiteKernelHits A T ω} ≤
        μ {ω | matrixDeviationHighProbabilityConstant * K ^ 2 *
            (HDP.Chapter7.gaussianWidth T +
              u * HDP.Chapter7.finiteRadius T) <
          finiteMatrixDeviation A T ω} := by
      apply measure_mono
      intro ω hω
      exact hthreshold.trans_le
        (sqrt_le_finiteMatrixDeviation_of_kernelHits A T hsphere ω hω)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := htail

/-- Absolute constant in the sample-size condition (9.14).

**Book Equation (9.14).** -/
def escapeSampleConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  16 * matrixDeviationHighProbabilityConstant ^ 2

/-- The escape sample constant is strictly positive.

**Lean implementation helper.** -/
theorem escapeSampleConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < escapeSampleConstant := by
  dsimp [escapeSampleConstant]
  positivity [matrixDeviationHighProbabilityConstant_pos]

/-- Absolute constant in the exponent of Theorem 9.3.4.

**Book Theorem 9.3.4.** -/
def escapeTailConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  1 / (4 * matrixDeviationHighProbabilityConstant ^ 2)

/-- The escape tail constant is strictly positive.

**Lean implementation helper.** -/
theorem escapeTailConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < escapeTailConstant := by
  dsimp [escapeTailConstant]
  positivity [matrixDeviationHighProbabilityConstant_pos]

/-- Finite-subfamily helper for . The source writes `m >= C K^4 w(T)^2`; the explicit constant chosen here is
`escapeSampleConstant`.

**Book Theorem 9.3.4.** -/
theorem theorem_9_3_4_escape_finite
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty)
    (hsphere : ∀ x ∈ T, ‖x‖ = 1)
    (hsize : escapeSampleConstant * K ^ 4 *
      HDP.Chapter7.gaussianWidth T ^ 2 ≤ (m : ℝ)) :
    μ {ω | finiteKernelHits A T ω} ≤
      ENNReal.ofReal (2 * Real.exp
        (-escapeTailConstant * (m : ℝ) / K ^ 4)) := by
  let C0 : ℝ := matrixDeviationHighProbabilityConstant
  let w : ℝ := HDP.Chapter7.gaussianWidth T
  let u : ℝ := Real.sqrt m / (2 * C0 * K ^ 2)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hC0 : 0 < C0 := by
    exact matrixDeviationHighProbabilityConstant_pos
  have hw : 0 ≤ w := HDP.Chapter7.gaussianWidth_nonneg T hT
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hradius : HDP.Chapter7.finiteRadius T = 1 :=
    finiteRadius_eq_one_of_unit T hT hsphere
  have hquarter : C0 * K ^ 2 * w ≤ Real.sqrt m / 4 := by
    have hleft0 : 0 ≤ 4 * C0 * K ^ 2 * w := by positivity
    have hsquare : (4 * C0 * K ^ 2 * w) ^ 2 ≤
        (Real.sqrt m) ^ 2 := by
      rw [Real.sq_sqrt hmR.le]
      calc
        (4 * C0 * K ^ 2 * w) ^ 2 =
            16 * C0 ^ 2 * K ^ 4 * w ^ 2 := by ring
        _ ≤ (m : ℝ) := by
          simpa [escapeSampleConstant, C0, w] using hsize
    have hlin := (sq_le_sq₀ hleft0 hsqrt.le).mp hsquare
    nlinarith
  have hthreshold : matrixDeviationHighProbabilityConstant * K ^ 2 *
      (HDP.Chapter7.gaussianWidth T +
        u * HDP.Chapter7.finiteRadius T) < Real.sqrt m := by
    have hhalf : C0 * K ^ 2 * u = Real.sqrt m / 2 := by
      dsimp [u]
      field_simp [hC0.ne', hK.ne']
    rw [hradius]
    change C0 * K ^ 2 * (w + u * 1) < Real.sqrt m
    rw [mul_add, mul_one, hhalf]
    nlinarith
  have hbase := escape_of_matrixDeviation_threshold hm A hrowsm hsub
    hiso hindep hfinite hK hpsi hu T hT hsphere hthreshold
  have hexponent : u ^ 2 = escapeTailConstant * (m : ℝ) / K ^ 4 := by
    dsimp [u, escapeTailConstant, C0]
    rw [div_pow, Real.sq_sqrt hmR.le]
    field_simp [matrixDeviationHighProbabilityConstant_pos.ne', hK.ne']
    ring
  have hnegative : -u ^ 2 =
      -escapeTailConstant * (m : ℝ) / K ^ 4 := by
    rw [hexponent]
    ring
  simpa only [hnegative] using hbase

/-! ## Arbitrary-set source theorem -/

/-- Matrix-deviation suprema increase along the canonical dense prefixes of
an arbitrary nonempty set.

**Lean implementation helper.** -/
private theorem finiteMatrixDeviation_setDensePrefix_mono
    {m n : ℕ} (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) [Nonempty T]
    {k l : ℕ} (hkl : k ≤ l) (ω : Ω) :
    letI : Nonempty ↑(setDensePrefix T k) :=
      (setDensePrefix_nonempty T k).to_subtype
    letI : Nonempty ↑(setDensePrefix T l) :=
      (setDensePrefix_nonempty T l).to_subtype
    finiteMatrixDeviation A (setDensePrefix T k) ω ≤
      finiteMatrixDeviation A (setDensePrefix T l) ω := by
  let Fk := setDensePrefix T k
  let Fl := setDensePrefix T l
  have hFk : Fk.Nonempty := setDensePrefix_nonempty T k
  have hFl : Fl.Nonempty := setDensePrefix_nonempty T l
  letI : Nonempty ↑Fk := hFk.to_subtype
  letI : Nonempty ↑Fl := hFl.to_subtype
  unfold finiteMatrixDeviation HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro x _hx
  let y : ↑Fl := ⟨x.1, setDensePrefix_mono T hkl x.2⟩
  simpa [HDP.Chapter8.finiteEuclideanProcess, y] using
    (Finset.le_sup'
      (fun z : ↑Fl ↦
        |HDP.Chapter8.finiteEuclideanProcess Fl
          (matrixDeviationProcess A) z ω|)
      (Finset.mem_univ y))

/-- A random kernel avoids a spherical set once `m` dominates its squared width. Let `T` be any nonempty subset of the Euclidean unit sphere. If the number
of independent isotropic subgaussian rows is at least a constant times
`K^4 w(T)^2`, then the outer probability that `T` meets the random kernel has
the source's exponential upper bound. The proof applies the finite tail
theorem to increasing canonical dense prefixes. Continuity closes the gap
from the dense sequence to every point of `T`; consequently no measurability
assumption on the arbitrary set `T` is needed.

**Book Theorem 9.3.4.** -/
theorem theorem_9_3_4_escape
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTne : T.Nonempty)
    (hsphere : ∀ x ∈ T, ‖x‖ = 1)
    (hsize : escapeSampleConstant * K ^ 4 *
      HDP.Chapter8.euclideanSetGaussianWidth T ^ 2 ≤ (m : ℝ)) :
    μ {ω | kernelHits A T ω} ≤
      ENNReal.ofReal (2 * Real.exp
        (-escapeTailConstant * (m : ℝ) / K ^ 4)) := by
  letI : Nonempty T := hTne.to_subtype
  let C0 : ℝ := matrixDeviationHighProbabilityConstant
  let w : ℝ := HDP.Chapter8.euclideanSetGaussianWidth T
  let u : ℝ := Real.sqrt m / (2 * C0 * K ^ 2)
  let threshold : ℝ := C0 * K ^ 2 * (w + u)
  let event : ℕ → Set Ω := fun k =>
    letI : Nonempty ↑(setDensePrefix T k) :=
      (setDensePrefix_nonempty T k).to_subtype
    {ω | threshold < finiteMatrixDeviation A (setDensePrefix T k) ω}
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hC0 : 0 < C0 := matrixDeviationHighProbabilityConstant_pos
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hTb : Bornology.IsBounded T := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨1, fun x hx => (hsphere x hx).le⟩
  have hquarter : C0 * K ^ 2 * w ≤ Real.sqrt m / 4 := by
    have hleft0 : 0 ≤ 4 * C0 * K ^ 2 * w := by positivity
    have hsquare : (4 * C0 * K ^ 2 * w) ^ 2 ≤
        (Real.sqrt m) ^ 2 := by
      rw [Real.sq_sqrt hmR.le]
      calc
        (4 * C0 * K ^ 2 * w) ^ 2 =
            16 * C0 ^ 2 * K ^ 4 * w ^ 2 := by ring
        _ ≤ (m : ℝ) := by
          simpa [escapeSampleConstant, C0, w] using hsize
    have hlin := (sq_le_sq₀ hleft0 hsqrt.le).mp hsquare
    nlinarith
  have hhalf : C0 * K ^ 2 * u = Real.sqrt m / 2 := by
    dsimp [u]
    field_simp [hC0.ne', hK.ne']
  have hthreshold : threshold < Real.sqrt m := by
    dsimp [threshold]
    rw [mul_add, hhalf]
    nlinarith
  have heventMeas : ∀ k, MeasurableSet (event k) := by
    intro k
    letI : Nonempty ↑(setDensePrefix T k) :=
      (setDensePrefix_nonempty T k).to_subtype
    exact measurableSet_lt measurable_const
      (measurable_finiteMatrixDeviation A hrowsm (setDensePrefix T k))
  have _hunionMeas : MeasurableSet (⋃ k, event k) :=
    MeasurableSet.iUnion heventMeas
  have heventMono : Monotone event := by
    intro k l hkl ω hω
    letI : Nonempty ↑(setDensePrefix T k) :=
      (setDensePrefix_nonempty T k).to_subtype
    letI : Nonempty ↑(setDensePrefix T l) :=
      (setDensePrefix_nonempty T l).to_subtype
    change threshold < finiteMatrixDeviation A (setDensePrefix T k) ω at hω
    change threshold < finiteMatrixDeviation A (setDensePrefix T l) ω
    exact hω.trans_le
      (finiteMatrixDeviation_setDensePrefix_mono A T hkl ω)
  have heventTail : ∀ k, μ (event k) ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
    intro k
    let F := setDensePrefix T k
    have hF : F.Nonempty := setDensePrefix_nonempty T k
    letI : Nonempty ↑F := hF.to_subtype
    have hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T :=
      setDensePrefix_subset T k
    have hsphereF : ∀ x ∈ F, ‖x‖ = 1 :=
      fun x hx => hsphere x (hFT hx)
    have hradius : HDP.Chapter7.finiteRadius F = 1 :=
      finiteRadius_eq_one_of_unit F hF hsphereF
    have hwidth : HDP.Chapter7.gaussianWidth F ≤ w := by
      simpa [F, w] using densePrefix_gaussianWidth_le T hTne hTb k
    have hfiniteThreshold :
        matrixDeviationHighProbabilityConstant * K ^ 2 *
            (HDP.Chapter7.gaussianWidth F +
              u * HDP.Chapter7.finiteRadius F) ≤ threshold := by
      rw [hradius, mul_one]
      change C0 * K ^ 2 * (HDP.Chapter7.gaussianWidth F + u) ≤
        C0 * K ^ 2 * (w + u)
      gcongr
    have htail := remark_9_1_4_matrixDeviation_highProbability hm A hrowsm
      hsub hiso hindep hfinite hK hpsi hu F hF
    calc
      μ (event k) ≤ μ {ω |
          matrixDeviationHighProbabilityConstant * K ^ 2 *
              (HDP.Chapter7.gaussianWidth F +
                u * HDP.Chapter7.finiteRadius F) <
            finiteMatrixDeviation A F ω} := by
        apply measure_mono
        intro ω hω
        change threshold < finiteMatrixDeviation A F ω at hω
        exact hfiniteThreshold.trans_lt hω
      _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := htail
  have hunionTail : μ (⋃ k, event k) ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
    rw [heventMono.measure_iUnion]
    exact iSup_le heventTail
  have hhitSubset : {ω | kernelHits A T ω} ⊆ ⋃ k, event k := by
    intro ω hω
    obtain ⟨x, hxT, hAx⟩ := hω
    by_contra hnot
    have hnotEvent : ∀ k, ω ∉ event k := by
      intro k hk
      exact hnot (Set.mem_iUnion.mpr ⟨k, hk⟩)
    have hdenseBound : ∀ k,
        |matrixDeviationProcess A (setDensePoint T k) ω| ≤ threshold := by
      intro k
      let F := setDensePrefix T k
      have hF : F.Nonempty := setDensePrefix_nonempty T k
      letI : Nonempty ↑F := hF.to_subtype
      have hpoint := abs_matrixDeviationProcess_le_finite A F
        (setDensePoint_mem_prefix T (le_refl k)) ω
      have hdev : finiteMatrixDeviation A F ω ≤ threshold := by
        exact not_lt.mp (hnotEvent k)
      exact hpoint.trans hdev
    let f : T → ℝ := fun y => |matrixDeviationProcess A y.1 ω|
    have haction : Continuous (fun y : T => matrixAction A y.1 ω) := by
      change Continuous (fun y : T => (A ω).toEuclideanLin y.1)
      exact (A ω).toEuclideanLin.toContinuousLinearMap.continuous.comp
        continuous_subtype_val
    have hfcont : Continuous f := by
      exact (haction.norm.sub
        (continuous_const.mul
          (continuous_subtype_val.norm : Continuous (fun y : T => ‖y.1‖)))).abs
    have hdenseSubtypeBound : ∀ k,
        f (setDenseSubtypePoint T k) ≤ threshold := by
      intro k
      exact hdenseBound k
    have hxbound : f ⟨x, hxT⟩ ≤ threshold :=
      continuous_le_of_setDenseSubtypePoint_le T f hfcont
        hdenseSubtypeBound ⟨x, hxT⟩
    have hxvalue : f ⟨x, hxT⟩ = Real.sqrt m := by
      simp [f, matrixDeviationProcess, hAx, hsphere x hxT,
        abs_of_nonneg (Real.sqrt_nonneg m)]
    rw [hxvalue] at hxbound
    exact (not_le_of_gt hthreshold) hxbound
  have hbase : μ {ω | kernelHits A T ω} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) :=
    (measure_mono hhitSubset).trans hunionTail
  have hexponent : u ^ 2 = escapeTailConstant * (m : ℝ) / K ^ 4 := by
    dsimp [u, escapeTailConstant, C0]
    rw [div_pow, Real.sq_sqrt hmR.le]
    field_simp [matrixDeviationHighProbabilityConstant_pos.ne', hK.ne']
    ring
  have hnegative : -u ^ 2 =
      -escapeTailConstant * (m : ℝ) / K ^ 4 := by
    rw [hexponent]
    ring
  simpa only [hnegative] using hbase

end

end HDP.Chapter9

end Source_08_EscapeTheorem

/-! ## Material formerly in `09_LinearModels.lean` -/

section Source_09_LinearModels

/-!
# Book Chapter 9, §9.4: high-dimensional linear models

This file supplies the deterministic model used by all recovery theorems.
Keeping the feasible fibre as a set makes “any solution” a uniform statement;
no non-measurable choice of an optimizer is hidden in an expectation.
-/

open Set InnerProductSpace
open scoped RealInnerProductSpace Pointwise

namespace HDP.Chapter9

noncomputable section

/-- A deterministic matrix acts on the Euclidean coordinate spaces through
Mathlib's canonical matrix linear map.

**Lean implementation helper.** -/
def deterministicMatrixAction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  A.toEuclideanLin x

/-- The deterministic matrix action agrees with the random-matrix action for a constant matrix.

**Lean implementation helper.** -/
theorem deterministicMatrixAction_eq_matrixAction
    {Ω : Type*} {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (omega : Ω) :
    deterministicMatrixAction (A omega) x = matrixAction A x omega := by
  ext i
  simp [deterministicMatrixAction, matrixAction, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]

/-- The deterministic matrix action vanishes at zero.

**Lean implementation helper.** -/
@[simp] theorem deterministicMatrixAction_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    deterministicMatrixAction A 0 = 0 := by
  simp [deterministicMatrixAction]

/-- The deterministic matrix action commutes with addition.

**Lean implementation helper.** -/
theorem deterministicMatrixAction_add {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    deterministicMatrixAction A (x + y) =
      deterministicMatrixAction A x + deterministicMatrixAction A y := by
  simp [deterministicMatrixAction]

/-- The deterministic matrix action commutes with subtraction.

**Lean implementation helper.** -/
theorem deterministicMatrixAction_sub {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    deterministicMatrixAction A (x - y) =
      deterministicMatrixAction A x - deterministicMatrixAction A y := by
  simp [deterministicMatrixAction]

/-- Noisy linear observation model `y=Ax+w`. Display (9.16): a noisy high-dimensional linear observation.

**Book Equation (9.16).** -/
def noisyLinearObservation {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  deterministicMatrixAction A x + w

/-- With zero noise, the noisy observation reduces to the exact matrix image of the signal.

**Lean implementation helper.** -/
@[simp] theorem noisyLinearObservation_zeroNoise {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    noisyLinearObservation A x 0 = deterministicMatrixAction A x := by
  simp [noisyLinearObservation]

/-- Sampling a digitized signal at selected time coordinates, as in Example
9.4.1.

**Book Example 9.4.1.** -/
def audioSamplingMatrix {m n : ℕ} (sample : Fin m → Fin n) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if j = sample i then 1 else 0

/-- Audio sampling is a high-dimensional linear inverse problem. The linear observation associated
with the coordinate sampling matrix returns exactly the selected signal
values.

**Book Example 9.4.1.** -/
theorem example_9_4_1_audioSampling {m n : ℕ}
    (sample : Fin m → Fin n) (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    deterministicMatrixAction (audioSamplingMatrix sample) x i = x (sample i) := by
  simp [deterministicMatrixAction, audioSamplingMatrix, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]

/-- Linear regression is a noisy linear inverse problem. The response vector in the
linear-regression model is the chapter's noisy linear observation.

**Book Example 9.4.2.** -/
theorem example_9_4_2_linearRegression {m n : ℕ}
    (predictors : Matrix (Fin m) (Fin n) ℝ)
    (theta : EuclideanSpace ℝ (Fin n))
    (noise : EuclideanSpace ℝ (Fin m)) :
    noisyLinearObservation predictors theta noise =
      predictors.toEuclideanLin theta + noise := rfl

/-- Structural prior `x in T`. The feasible fibre of display (9.18).

**Book Equation (9.17).** -/
def measurementFiber {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | z ∈ T ∧ deterministicMatrixAction A z = y}

/-- Constrained feasibility program `Ax'=y`, `x' in T`. A source-facing predicate for an arbitrary feasible recovery solution.

**Book Equation (9.18).** -/
def IsConstrainedRecoverySolution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (xhat : EuclideanSpace ℝ (Fin n)) : Prop :=
  xhat ∈ measurementFiber A y T

/-- The true signal belongs to the fiber determined by its noiseless observation.

**Lean implementation helper.** -/
theorem trueSignal_mem_measurementFiber {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) :
    x ∈ measurementFiber A (deterministicMatrixAction A x) T := by
  exact ⟨hx, rfl⟩

/-- Every constrained-recovery solution lies in the prescribed prior set.

**Lean implementation helper.** -/
theorem constrainedSolution_mem_prior {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {y : EuclideanSpace ℝ (Fin m)}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    {xhat : EuclideanSpace ℝ (Fin n)}
    (h : IsConstrainedRecoverySolution A y T xhat) : xhat ∈ T :=
  h.1

/-- A constrained-recovery solution has the same measurements as the true signal.

**Lean implementation helper.** -/
theorem constrainedSolution_measurement_eq {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {y : EuclideanSpace ℝ (Fin m)}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    {xhat : EuclideanSpace ℝ (Fin n)}
    (h : IsConstrainedRecoverySolution A y T xhat) :
    deterministicMatrixAction A xhat = y :=
  h.2

/-- Two feasible points differ by a vector in the kernel.

**Lean implementation helper.** -/
theorem feasible_sub_mem_ker {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {y : EuclideanSpace ℝ (Fin m)}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    {x z : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ measurementFiber A y T)
    (hz : z ∈ measurementFiber A y T) :
    deterministicMatrixAction A (z - x) = 0 := by
  rw [deterministicMatrixAction_sub, hz.2, hx.2, sub_self]

/-- The error between two feasible points belongs to the difference set of
the prior.

**Lean implementation helper.** -/
theorem feasible_sub_mem_diff {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {y : EuclideanSpace ℝ (Fin m)}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    {x z : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ measurementFiber A y T)
    (hz : z ∈ measurementFiber A y T) :
    z - x ∈ T - T := by
  exact ⟨z, hz.1, x, hx.1, rfl⟩

/-- A safe replacement for a raw real-valued diameter of an arbitrary set.

**Lean implementation helper.** -/
def HasDiameterBound {E : Type*} [NormedAddCommGroup E]
    (T : Set E) (d : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → ‖x - y‖ ≤ d

/-- A uniform bound on measurement-fiber diameters yields the corresponding constrained-recovery error bound.

**Lean implementation helper.** -/
theorem constrainedRecovery_of_diameterBound {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ T)
    (hxhat : IsConstrainedRecoverySolution A
      (deterministicMatrixAction A x) T xhat)
    {d : ℝ} (hd : HasDiameterBound
      (measurementFiber A (deterministicMatrixAction A x) T) d) :
    ‖xhat - x‖ ≤ d := by
  exact hd hxhat (trueSignal_mem_measurementFiber A T hx)

/-- When `m<n`, recovery needs a structural prior because the measurement map has a nontrivial kernel. The deterministic dimension obstruction in Remark 9.4.3: the kernel of an
`m × n` measurement map has dimension at least `n-m`.

**Book Remark 9.4.3.** -/
theorem measurementKernel_finrank_ge {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    n - m ≤ Module.finrank ℝ A.toEuclideanLin.ker := by
  have hsum := A.toEuclideanLin.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ A.toEuclideanLin.range ≤ m := by
    simpa [finrank_euclideanSpace_fin] using A.toEuclideanLin.range.finrank_le
  have hdomain : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  rw [hdomain] at hsum
  omega

/-- When `m<n`, recovery needs a structural prior because the measurement map has a nontrivial kernel. In the noiseless model the true signal is a feasible point of the structural
fibre. The preceding theorem records the source's large-kernel obstruction.

**Book Remark 9.4.3.** -/
theorem remark_9_4_3_structuralPrior {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) :
    IsConstrainedRecoverySolution A
      (noisyLinearObservation A x 0) T x := by
  simpa [IsConstrainedRecoverySolution] using
    trueSignal_mem_measurementFiber A T hx

end

end HDP.Chapter9

end Source_09_LinearModels

/-! ## Material formerly in `10_ConstrainedRecovery.lean` -/

section Source_10_ConstrainedRecovery

/-!
# Book Chapter 9, §9.4.1: constrained recovery

The main theorem is factored into the deterministic fibre-diameter implication
and an expectation transfer.  This formulation fixes the source's measurable
selection gap: the bound is uniform for every measurable feasible selector.
The affine `M*` theorem is composed directly into the source-facing recovery
bound; no caller-supplied diameter or expected-diameter premise remains.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A random constrained-recovery selector, stated pointwise.

**Lean implementation helper.** -/
def IsRandomConstrainedRecoverySolution {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (T : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ ω, IsConstrainedRecoverySolution (A ω)
    (deterministicMatrixAction (A ω) x) T (xhat ω)

/-- The deterministic core of Theorem 9.4.4.

**Book Theorem 9.4.4.** -/
theorem constrainedRecovery_error_le_fiberDiameter {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hx : x ∈ T)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x T)
    (D : Ω → ℝ)
    (hdiam : ∀ ω, HasDiameterBound
      (measurementFiber (A ω) (deterministicMatrixAction (A ω) x) T)
      (D ω)) :
    ∀ ω, ‖xhat ω - x‖ ≤ D ω := by
  intro ω
  exact constrainedRecovery_of_diameterBound hx (hsol ω) (hdiam ω)

/-- Expected-error transfer for an arbitrary measurable feasible selector.

**Lean implementation helper.** -/
theorem constrainedRecovery_expectedError_le {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hx : x ∈ T)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x T)
    (D : Ω → ℝ)
    (hdiam : ∀ ω, HasDiameterBound
      (measurementFiber (A ω) (deterministicMatrixAction (A ω) x) T)
      (D ω))
    (herr : Integrable (fun ω => ‖xhat ω - x‖) μ)
    (hD : Integrable D μ) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤ ∫ ω, D ω ∂μ := by
  exact integral_mono herr hD
    (constrainedRecovery_error_le_fiberDiameter A xhat x T hx hsol D hdiam)

/-- The affine-fibre maximum really dominates every pair of feasible points
in the finite prior.

**Lean implementation helper.** -/
theorem constrainedRecovery_error_le_finiteAffineFiberDiameter {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    {x xhat : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (omega : Ω)
    (hsol : IsConstrainedRecoverySolution (A omega)
      (deterministicMatrixAction (A omega) x) (T : Set _) xhat) :
    ‖xhat - x‖ ≤ finiteAffineFiberDiameter A T omega := by
  unfold finiteAffineFiberDiameter HDP.Chapter8.finiteProcessAbsoluteSup
  let p : ↥T × ↥T := (⟨xhat, hsol.1⟩, ⟨x, hx⟩)
  have heq : matrixAction A p.1.1 omega = matrixAction A p.2.1 omega := by
    rw [← deterministicMatrixAction_eq_matrixAction A p.1.1 omega,
      ← deterministicMatrixAction_eq_matrixAction A p.2.1 omega]
    exact hsol.2
  calc
    ‖xhat - x‖ =
        |if matrixAction A p.1.1 omega = matrixAction A p.2.1 omega then
          ‖p.1.1 - p.2.1‖ else 0| := by simp [p, heq]
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun q : ↥T × ↥T =>
          |if matrixAction A q.1.1 omega = matrixAction A q.2.1 omega then
            ‖q.1.1 - q.2.1‖ else 0|) :=
      Finset.le_sup'
        (fun q : ↥T × ↥T =>
          |if matrixAction A q.1.1 omega = matrixAction A q.2.1 omega then
            ‖q.1.1 - q.2.1‖ else 0|)
        (Finset.mem_univ p)

/-- The finite affine fiber diameter is integrable.

**Lean implementation helper.** -/
theorem integrable_finiteAffineFiberDiameter [IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) : Integrable (finiteAffineFiberDiameter A T) μ := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  refine (hFint.const_mul (Real.sqrt m)⁻¹).mono'
    (measurable_finiteAffineFiberDiameter A hrowsm T).aestronglyMeasurable ?_
  filter_upwards [] with omega
  have hprod : 0 ≤ (Real.sqrt m)⁻¹ * finiteMatrixDeviation A D omega :=
    mul_nonneg (inv_nonneg.mpr hsqrt.le)
      (finiteMatrixDeviation_nonneg A D omega)
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (finiteAffineFiberDiameter_nonneg A T omega),
    abs_of_nonneg hprod, D] using
      finiteAffineFiberDiameter_le hm A T hT omega

/-- This is the actual composition with the affine M-star theorem. There is no
caller-supplied diameter or mean bound: the row assumptions construct it.
The finite-prior interface is the chapter-wide measurable finite-subfamily
convention.

**Book Theorem 9.4.4.** -/
theorem theorem_9_4_4_constrainedRecovery_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x (T : Set _)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
        Real.sqrt m := by
  have hdiamInt := integrable_finiteAffineFiberDiameter hm A hrowsm hsub
    hiso hindep hfinite hK hpsi T hT
  have herrInt : Integrable (fun omega => ‖xhat omega - x‖) μ := by
    refine hdiamInt.mono' (hxhatm.sub measurable_const).norm.aestronglyMeasurable ?_
    filter_upwards [] with omega
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (finiteAffineFiberDiameter_nonneg A T omega)] using
        constrainedRecovery_error_le_finiteAffineFiberDiameter A T hx omega (hsol omega)
  calc
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
        ∫ omega, finiteAffineFiberDiameter A T omega ∂μ :=
      integral_mono herrInt hdiamInt fun omega =>
        constrainedRecovery_error_le_finiteAffineFiberDiameter A T hx omega (hsol omega)
    _ ≤ mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T /
        Real.sqrt m :=
      exercise_9_12_affineMStar hm A hrowsm hsub hiso hindep hfinite
        hK hpsi T hT

/-! ## Actual bounded-set constrained recovery -/

/-- Constrained recovery over a bounded prior has expected error `O(K^2 w(T)/sqrt m)`. For every nonempty bounded structural prior `T`, every measurable feasible
selector satisfies the source's expected Euclidean-error bound. The proof
uses a countable dense-prefix envelope only internally; the public statement
quantifies over the actual set and its canonical arbitrary-set Gaussian
width.

**Book Theorem 9.4.4.** -/
theorem theorem_9_4_4_constrainedRecovery
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hTne : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x T) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T / Real.sqrt m := by
  letI : Nonempty T := hTne.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le.mp hTb)
  have hR0 : 0 ≤ R :=
    (norm_nonneg x).trans (hR x hx)
  have herrMeas : Measurable (fun ω => ‖xhat ω - x‖) :=
    (hxhatm.sub measurable_const).norm
  have herrInt : Integrable (fun ω => ‖xhat ω - x‖) μ := by
    refine Integrable.of_bound herrMeas.aestronglyMeasurable (2 * R) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖xhat ω - x‖ ≤ ‖xhat ω‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hR (xhat ω) (hsol ω).1) (hR x hx)
      _ = 2 * R := by ring
  have hpoint : ∀ ω,
      ENNReal.ofReal (Real.sqrt m * ‖xhat ω - x‖) ≤
        setDifferenceMatrixDeviationENN A T ω := by
    intro ω
    have hzero : matrixAction A (xhat ω - x) ω = 0 := by
      rw [matrixAction_sub, sub_eq_zero,
        ← deterministicMatrixAction_eq_matrixAction A (xhat ω) ω,
        ← deterministicMatrixAction_eq_matrixAction A x ω]
      exact (hsol ω).2
    have hdev :=
      abs_matrixDeviationProcess_le_setDifferenceMatrixDeviationENN
        A T (hsol ω).1 hx ω
    have hvalue : |matrixDeviationProcess A (xhat ω - x) ω| =
        Real.sqrt m * ‖xhat ω - x‖ := by
      simp [matrixDeviationProcess, hzero,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    simpa [hvalue] using hdev
  have hdevMean := lintegral_setDifferenceMatrixDeviationENN_le hm A hrowsm
    hsub hiso hindep hfinite hK hpsi T hTne hTb
  have hscaledInt : Integrable
      (fun ω => Real.sqrt m * ‖xhat ω - x‖) μ :=
    herrInt.const_mul (Real.sqrt m)
  have hscaled0 : ∀ ω, 0 ≤ Real.sqrt m * ‖xhat ω - x‖ :=
    fun ω => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hENN : ENNReal.ofReal
      (∫ ω, Real.sqrt m * ‖xhat ω - x‖ ∂μ) ≤
      ENNReal.ofReal (mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T) := by
    rw [ofReal_integral_eq_lintegral_ofReal hscaledInt
      (Filter.Eventually.of_forall hscaled0)]
    exact (lintegral_mono hpoint).trans hdevMean
  have hrhs0 : 0 ≤ mStarConstant * K ^ 2 *
      HDP.Chapter8.euclideanSetGaussianWidth T := by
    exact mul_nonneg
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)) ENNReal.toReal_nonneg
  have hreal : (∫ ω, Real.sqrt m * ‖xhat ω - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        HDP.Chapter8.euclideanSetGaussianWidth T :=
    (ENNReal.ofReal_le_ofReal_iff hrhs0).mp hENN
  apply (le_div_iff₀ hsqrt).2
  rw [integral_const_mul] at hreal
  simpa [mul_comm] using hreal

/-- The displayed sample-size condition is exactly the algebraic statement that
the Theorem 9.4.4 rate is at most one percent of a chosen positive diameter.
It exposes the `width² / diameter²` dependence without suppressing `K`.

**Book Remark 9.4.5.** -/
theorem remark_9_4_5_effectiveDimension_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x (T : Set _))
    {diameter : ℝ} (hdiameter : 0 < diameter)
    (hsize : (100 * (mStarConstant * K ^ 2 *
      HDP.Chapter7.gaussianWidth T) / diameter) ^ 2 ≤ (m : ℝ)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤ diameter / 100 := by
  have hmain := theorem_9_4_4_constrainedRecovery_finitePrior hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hT x hx xhat hxhatm hsol
  let a : ℝ := mStarConstant * K ^ 2 * HDP.Chapter7.gaussianWidth T
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity [mStarConstant_pos, HDP.Chapter7.gaussianWidth_nonneg T hT]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hq : 0 ≤ 100 * a / diameter := by positivity
  have hqle : 100 * a / diameter ≤ Real.sqrt m := by
    apply (sq_le_sq₀ hq hsqrt.le).mp
    rw [Real.sq_sqrt hmR.le]
    simpa [a] using hsize
  have hmul : 100 * a ≤ Real.sqrt m * diameter :=
    (div_le_iff₀ hdiameter).mp hqle
  have hrate : a / Real.sqrt m ≤ diameter / 100 := by
    apply (div_le_iff₀ hsqrt).2
    nlinarith
  exact hmain.trans (by simpa [a] using hrate)

/-- The finite generator and its
convex hull have exactly the same Gaussian width, so the recovery rate in
Theorem 9.4.4 is unchanged.

**Book Remark 9.4.6.** -/
theorem remark_9_4_6_convexRelaxation_finitePrior {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    HDP.Chapter7.convexHullGaussianWidth T =
      HDP.Chapter7.gaussianWidth T :=
  HDP.Chapter7.gaussianWidth_convexHull T hT

/-! ## Noisy constrained recovery (promoted Exercise 9.19) -/

/-- A least-residual solution over a structural prior; this predicate does not
silently assume that a minimizer exists.

**Lean implementation helper.** -/
def IsNoisyConstrainedRecoveryMinimizer {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (xhat : EuclideanSpace ℝ (Fin n)) : Prop :=
  xhat ∈ T ∧ ∀ z ∈ T,
    ‖y - deterministicMatrixAction A xhat‖ ≤
      ‖y - deterministicMatrixAction A z‖

/-- The measurement error of a noisy constrained solution is at most twice the noise level.

**Lean implementation helper.** -/
theorem noisyConstrained_action_error_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (w : EuclideanSpace ℝ (Fin m))
    (T : Set (EuclideanSpace ℝ (Fin n))) (hx : x ∈ T)
    (hmin : IsNoisyConstrainedRecoveryMinimizer A
      (noisyLinearObservation A x w) T xhat) :
    ‖deterministicMatrixAction A (xhat - x)‖ ≤ 2 * ‖w‖ := by
  have hres := hmin.2 x hx
  have hid : noisyLinearObservation A x w - deterministicMatrixAction A xhat =
      w - deterministicMatrixAction A (xhat - x) := by
    simp [noisyLinearObservation, deterministicMatrixAction_sub]
    abel
  have htrue : noisyLinearObservation A x w - deterministicMatrixAction A x = w := by
    simp [noisyLinearObservation]
  have hres' : ‖w - deterministicMatrixAction A (xhat - x)‖ ≤ ‖w‖ := by
    rw [hid, htrue] at hres
    exact hres
  have hsplit : deterministicMatrixAction A (xhat - x) =
      w - (w - deterministicMatrixAction A (xhat - x)) := by abel
  rw [hsplit]
  calc
    ‖w - (w - deterministicMatrixAction A (xhat - x))‖ ≤
        ‖w‖ + ‖w - deterministicMatrixAction A (xhat - x)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ + ‖w‖ := add_le_add (le_refl _) hres'
    _ = 2 * ‖w‖ := by ring

/-- The noise may depend on the matrix. Its only analytic requirements are
measurability and integrability of its Euclidean norm. The proof combines
the residual-minimization inequality with the actual matrix-deviation theorem;
there is no supplied recovery-geometry premise.

**Book Exercise 9.19.** -/
theorem exercise_9_19_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m)) (_hwm : Measurable w)
    (hwInt : Integrable (fun omega => ‖w omega‖) μ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hmin : ∀ omega, IsNoisyConstrainedRecoveryMinimizer (A omega)
      (noisyLinearObservation (A omega) x (w omega)) (T : Set _) (xhat omega)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      (2 * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have herrMeas : Measurable (fun omega => ‖xhat omega - x‖) :=
    (hxhatm.sub measurable_const).norm
  have hpoint (omega : Ω) :
      ‖xhat omega - x‖ ≤
        (2 * ‖w omega‖ + finiteMatrixDeviation A D omega) /
          Real.sqrt m := by
    let h := xhat omega - x
    have hhD : h ∈ D := by
      unfold D HDP.Chapter7.differenceFinset HDP.Chapter7.minkowskiSumFinset
        HDP.Chapter7.negFinset
      apply Finset.mem_image.mpr
      refine ⟨(xhat omega, -x), Finset.mem_product.mpr ⟨(hmin omega).1, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · simp [h, sub_eq_add_neg]
    have hdev := abs_matrixDeviationProcess_le_finite A D hhD omega
    have haction : ‖matrixAction A h omega‖ ≤ 2 * ‖w omega‖ := by
      rw [← deterministicMatrixAction_eq_matrixAction A h omega]
      exact noisyConstrained_action_error_le (A omega) (w omega) (T : Set _) hx
        (hmin omega)
    have hsqrtBound : Real.sqrt m * ‖h‖ ≤
        ‖matrixAction A h omega‖ + finiteMatrixDeviation A D omega := by
      dsimp [matrixDeviationProcess] at hdev
      nlinarith [neg_le_of_abs_le hdev]
    apply (le_div_iff₀ hsqrt).2
    calc
      ‖h‖ * Real.sqrt m = Real.sqrt m * ‖h‖ := by ring
      _ ≤ ‖matrixAction A h omega‖ + finiteMatrixDeviation A D omega := hsqrtBound
      _ ≤ 2 * ‖w omega‖ + finiteMatrixDeviation A D omega :=
        add_le_add haction (le_refl _)
  have hrhsInt : Integrable (fun omega =>
      (2 * ‖w omega‖ + finiteMatrixDeviation A D omega) / Real.sqrt m) μ :=
    ((hwInt.const_mul 2).add hFint).div_const _
  have herrInt : Integrable (fun omega => ‖xhat omega - x‖) μ := by
    refine hrhsInt.mono' herrMeas.aestronglyMeasurable ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hrhs0 : 0 ≤
        (2 * ‖w omega‖ + finiteMatrixDeviation A D omega) / Real.sqrt m := by
      exact div_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
          (finiteMatrixDeviation_nonneg A D omega))
        hsqrt.le
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg hrhs0] using hpoint omega
  have hdevMean := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D hD
  calc
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
        ∫ omega, (2 * ‖w omega‖ + finiteMatrixDeviation A D omega) /
          Real.sqrt m ∂μ := integral_mono herrInt hrhsInt hpoint
    _ = (2 * (∫ omega, ‖w omega‖ ∂μ) +
        ∫ omega, finiteMatrixDeviation A D omega ∂μ) /
          Real.sqrt m := by
      rw [integral_div, integral_add (hwInt.const_mul 2) hFint,
        integral_const_mul]
    _ ≤ (2 * (∫ omega, ‖w omega‖ ∂μ) +
        matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianComplexity D) / Real.sqrt m := by
      exact div_le_div_of_nonneg_right (add_le_add (le_refl _) hdevMean)
        (Real.sqrt_nonneg _)
    _ = (2 * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m := by
      rw [HDP.Chapter7.gaussianComplexity_difference T hT]
      ring

/-- Penalized unconstrained recovery objective. Objective in the penalized program (9.20).

**Book Equation (9.20).** -/
def penalizedRecoveryObjective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (lam : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖y - deterministicMatrixAction A z‖ ^ 2 + lam * penalty z

/-- A minimizer predicate avoids silently assuming attainment.

**Lean implementation helper.** -/
def IsPenalizedRecoveryMinimizer {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (lam : ℝ) (xhat : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z, penalizedRecoveryObjective A y penalty lam xhat ≤
    penalizedRecoveryObjective A y penalty lam z

/-- The basic inequality for the penalized estimator, the deterministic first
step of promoted Exercise 9.20.

**Book Exercise 9.20.** -/
theorem penalizedRecovery_basicInequality {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin m))
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (lam : ℝ) (xhat : EuclideanSpace ℝ (Fin n))
    (hmin : IsPenalizedRecoveryMinimizer A
      (noisyLinearObservation A x w) penalty lam xhat) :
    penalizedRecoveryObjective A (noisyLinearObservation A x w)
        penalty lam xhat ≤
      ‖w‖ ^ 2 + lam * penalty x := by
  have h := hmin x
  simpa [penalizedRecoveryObjective, noisyLinearObservation,
    deterministicMatrixAction_sub] using h

/-- A penalized minimizer has controlled measurement residual relative to the true signal.

**Lean implementation helper.** -/
theorem penalizedRecovery_action_error_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin m))
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpen0 : ∀ z, 0 ≤ penalty z)
    {lam : ℝ} (hlam : 0 < lam)
    (htune : lam * penalty x ≤ ‖w‖ ^ 2)
    (xhat : EuclideanSpace ℝ (Fin n))
    (hmin : IsPenalizedRecoveryMinimizer A
      (noisyLinearObservation A x w) penalty lam xhat) :
    ‖deterministicMatrixAction A (xhat - x)‖ ≤ 3 * ‖w‖ := by
  have hbasic := penalizedRecovery_basicInequality A x w penalty lam xhat hmin
  have hresSq :
      ‖w - deterministicMatrixAction A (xhat - x)‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    dsimp [penalizedRecoveryObjective] at hbasic
    have hpenhat : 0 ≤ lam * penalty xhat := mul_nonneg hlam.le (hpen0 xhat)
    have hres :
        ‖noisyLinearObservation A x w - deterministicMatrixAction A xhat‖ ^ 2 ≤
          ‖w‖ ^ 2 + lam * penalty x := by
      nlinarith
    have hid : noisyLinearObservation A x w - deterministicMatrixAction A xhat =
        w - deterministicMatrixAction A (xhat - x) := by
      simp [noisyLinearObservation, deterministicMatrixAction_sub]
      abel
    rw [hid] at hres
    linarith
  have hres : ‖w - deterministicMatrixAction A (xhat - x)‖ ≤ 2 * ‖w‖ := by
    nlinarith [norm_nonneg (w - deterministicMatrixAction A (xhat - x)), norm_nonneg w]
  have hsplit : deterministicMatrixAction A (xhat - x) =
      w - (w - deterministicMatrixAction A (xhat - x)) := by abel
  rw [hsplit]
  calc
    ‖w - (w - deterministicMatrixAction A (xhat - x))‖ ≤
        ‖w‖ + ‖w - deterministicMatrixAction A (xhat - x)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add (le_refl _) hres
    _ = 3 * ‖w‖ := by ring

/-- Matrix-deviation transfer used by the promoted penalized theorem. Its
hypothesis controls measurement error, not the desired Euclidean conclusion.

**Lean implementation helper.** -/
theorem expected_error_of_action_bound
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun omega => ‖w omega‖) μ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hxhatT : ∀ omega, xhat omega ∈ T)
    {c : ℝ} (hc : 0 ≤ c)
    (haction : ∀ omega,
      ‖matrixAction A (xhat omega - x) omega‖ ≤ c * ‖w omega‖) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      (c * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m := by
  let D := HDP.Chapter7.differenceFinset T T
  have hD : D.Nonempty := HDP.Chapter7.differenceFinset_nonempty hT hT
  letI : Nonempty ↥D := hD.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hFint := integrable_finiteMatrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D
  have herrMeas : Measurable (fun omega => ‖xhat omega - x‖) :=
    (hxhatm.sub measurable_const).norm
  have hpoint (omega : Ω) :
      ‖xhat omega - x‖ ≤
        (c * ‖w omega‖ + finiteMatrixDeviation A D omega) /
          Real.sqrt m := by
    let h := xhat omega - x
    have hhD : h ∈ D := by
      unfold D HDP.Chapter7.differenceFinset HDP.Chapter7.minkowskiSumFinset
        HDP.Chapter7.negFinset
      apply Finset.mem_image.mpr
      refine ⟨(xhat omega, -x), Finset.mem_product.mpr ⟨hxhatT omega, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · simp [h, sub_eq_add_neg]
    have hdev := abs_matrixDeviationProcess_le_finite A D hhD omega
    have hsqrtBound : Real.sqrt m * ‖h‖ ≤
        ‖matrixAction A h omega‖ + finiteMatrixDeviation A D omega := by
      dsimp [matrixDeviationProcess] at hdev
      nlinarith [neg_le_of_abs_le hdev]
    apply (le_div_iff₀ hsqrt).2
    calc
      ‖h‖ * Real.sqrt m = Real.sqrt m * ‖h‖ := by ring
      _ ≤ ‖matrixAction A h omega‖ + finiteMatrixDeviation A D omega := hsqrtBound
      _ ≤ c * ‖w omega‖ + finiteMatrixDeviation A D omega :=
        add_le_add (haction omega) (le_refl _)
  have hrhsInt : Integrable (fun omega =>
      (c * ‖w omega‖ + finiteMatrixDeviation A D omega) / Real.sqrt m) μ :=
    ((hwInt.const_mul c).add hFint).div_const _
  have herrInt : Integrable (fun omega => ‖xhat omega - x‖) μ := by
    refine hrhsInt.mono' herrMeas.aestronglyMeasurable ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hrhs0 : 0 ≤
        (c * ‖w omega‖ + finiteMatrixDeviation A D omega) / Real.sqrt m := by
      exact div_nonneg (add_nonneg (mul_nonneg hc (norm_nonneg _))
        (finiteMatrixDeviation_nonneg A D omega)) hsqrt.le
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg hrhs0] using hpoint omega
  have hdevMean := theorem_9_1_1_matrixDeviation hm A hrowsm hsub hiso
    hindep hfinite hK hpsi D hD
  calc
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
        ∫ omega, (c * ‖w omega‖ + finiteMatrixDeviation A D omega) /
          Real.sqrt m ∂μ := integral_mono herrInt hrhsInt hpoint
    _ = (c * (∫ omega, ‖w omega‖ ∂μ) +
        ∫ omega, finiteMatrixDeviation A D omega ∂μ) /
          Real.sqrt m := by
      rw [integral_div, integral_add (hwInt.const_mul c) hFint,
        integral_const_mul]
    _ ≤ (c * (∫ omega, ‖w omega‖ ∂μ) +
        matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianComplexity D) / Real.sqrt m := by
      exact div_le_div_of_nonneg_right (add_le_add (le_refl _) hdevMean)
        (Real.sqrt_nonneg _)
    _ = (c * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m := by
      rw [HDP.Chapter7.gaussianComplexity_difference T hT]
      ring

/-- The source tuning is corrected at `penalty x = 0`: the proof only needs
`lambda > 0` and `lambda * penalty x ≤ ‖w‖²`. The finite set encloses the
measurable optimizer's range; minimization remains over the full space.

**Book Exercise 9.20.** -/
theorem exercise_9_20_finiteCandidates
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun omega => ‖w omega‖) μ)
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpen0 : ∀ z, 0 ≤ penalty z)
    (lam : Ω → ℝ) (hlam : ∀ omega, 0 < lam omega)
    (htune : ∀ omega, lam omega * penalty x ≤ ‖w omega‖ ^ 2)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hxhatT : ∀ omega, xhat omega ∈ T)
    (hmin : ∀ omega, IsPenalizedRecoveryMinimizer (A omega)
      (noisyLinearObservation (A omega) x (w omega)) penalty (lam omega) (xhat omega)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      (3 * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m := by
  apply expected_error_of_action_bound hm A hrowsm hsub hiso hindep hfinite
    hK hpsi T hT x hx w hwInt xhat hxhatm hxhatT (by norm_num : (0 : ℝ) ≤ 3)
  intro omega
  rw [← deterministicMatrixAction_eq_matrixAction A (xhat omega - x) omega]
  exact penalizedRecovery_action_error_le (A omega) x (w omega) penalty hpen0
    (hlam omega) (htune omega) (xhat omega) (hmin omega)

/-- The displayed penalized program and its recovery estimate are the
fully proved Exercise 9.20 result; this source-numbered wrapper records the
main-text dependency explicitly.

**Book Remark 9.4.7.** -/
theorem remark_9_4_7_unconstrainedOptimization_finiteCandidates
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun omega => ‖w omega‖) μ)
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpen0 : ∀ z, 0 ≤ penalty z)
    (lam : Ω → ℝ) (hlam : ∀ omega, 0 < lam omega)
    (htune : ∀ omega, lam omega * penalty x ≤ ‖w omega‖ ^ 2)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hxhatT : ∀ omega, xhat omega ∈ T)
    (hmin : ∀ omega, IsPenalizedRecoveryMinimizer (A omega)
      (noisyLinearObservation (A omega) x (w omega)) penalty
        (lam omega) (xhat omega)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      (3 * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m :=
  exercise_9_20_finiteCandidates hm A hrowsm hsub hiso hindep hfinite hK hpsi T hT x hx
    w hwInt penalty hpen0 lam hlam htune xhat hxhatm hxhatT hmin

/-- Exercise 9.20 with an explicit two-sided interpretation of the source's
`lambda asymp ‖w‖² / penalty x`. The lower comparison constant records the
intended nondegenerate tuning regime; the proof uses the upper comparison,
which is the exact sufficient condition isolated in `exercise_9_20`. The
zero-penalty case is intentionally handled by that more general theorem
instead of dividing by zero here.

**Book Exercise 9.20.** -/
theorem exercise_9_20_finiteCandidates_twoSidedTuning
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun omega => ‖w omega‖) μ)
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpen0 : ∀ z, 0 ≤ penalty z) (hxpen : 0 < penalty x)
    (cLower : ℝ) (_hcLower : 0 < cLower) (_hcLowerOne : cLower ≤ 1)
    (lam : Ω → ℝ) (hlam : ∀ omega, 0 < lam omega)
    (_htuneLower : ∀ omega,
      cLower * (‖w omega‖ ^ 2 / penalty x) ≤ lam omega)
    (htuneUpper : ∀ omega,
      lam omega ≤ ‖w omega‖ ^ 2 / penalty x)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hxhatT : ∀ omega, xhat omega ∈ T)
    (hmin : ∀ omega, IsPenalizedRecoveryMinimizer (A omega)
      (noisyLinearObservation (A omega) x (w omega)) penalty
        (lam omega) (xhat omega)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      (3 * (∫ omega, ‖w omega‖ ∂μ) +
        2 * matrixDeviationConstant * K ^ 2 *
          HDP.Chapter7.gaussianWidth T) / Real.sqrt m := by
  have htune : ∀ omega, lam omega * penalty x ≤ ‖w omega‖ ^ 2 := by
    intro omega
    exact (le_div_iff₀ hxpen).mp (htuneUpper omega)
  exact exercise_9_20_finiteCandidates hm A hrowsm hsub hiso hindep hfinite hK hpsi
    T hT x hx w hwInt penalty hpen0 lam hlam htune xhat hxhatm hxhatT hmin

/-! ## Actual-set width geometry used by Remarks 9.4.5--9.4.7 -/

/-- Every point of an arbitrary convex hull already belongs to the convex
hull of a nonempty finite subfamily of the generating set.

**Lean implementation helper.** -/
private theorem exists_finset_generator_of_mem_convexHull_constrained_recovery {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ T) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin n)),
      F.Nonempty ∧ (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T ∧
        x ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  obtain ⟨x0, hx0⟩ := hT
  rw [mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩
  let F : Finset (EuclideanSpace ℝ (Fin n)) := insert x0 (Finset.univ.image z)
  refine ⟨F, ⟨x0, by simp [F]⟩, ?_, ?_⟩
  · intro y hy
    simp only [F, Finset.coe_insert, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_insert_iff, Set.mem_range] at hy
    rcases hy with rfl | ⟨i, rfl⟩
    · exact hx0
    · exact hz i
  · exact mem_convexHull_of_exists_fintype w z hw0 hw1 (fun i => by
      have hzi : z i ∈ Finset.univ.image z :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact by simp [F]) hsum

/-- If every point of one finite set belongs to the convex hull of another,
then its Gaussian width is no larger.

**Lean implementation helper.** -/
theorem finiteGaussianWidth_le_of_subset_convexHull {n : ℕ}
    (F G : Finset (EuclideanSpace ℝ (Fin n)))
    (hF : F.Nonempty) (hG : G.Nonempty)
    (hFG : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆
      convexHull ℝ (G : Set _)) :
    HDP.Chapter7.gaussianWidth F ≤ HDP.Chapter7.gaussianWidth G := by
  apply integral_mono (HDP.Chapter7.integrable_finiteGaussianSupport F)
    (HDP.Chapter7.integrable_finiteGaussianSupport G)
  intro g
  rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF,
    HDP.Chapter7.finiteGaussianSupport_eq_sup' G hG]
  apply (Finset.sup'_le_iff hF (fun x => inner ℝ g x)).mpr
  intro x hx
  have hlinear : ConvexOn ℝ Set.univ
      (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ g z) := by
    simpa [real_inner_comm] using
      (((innerSL ℝ) g).toLinearMap.convexOn (convex_univ :
        Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))))
  exact hlinear.le_sup_of_mem_convexHull (Set.subset_univ _) (hFG hx)

/-- Monotonicity of the authoritative arbitrary-set Gaussian-width
envelope.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidthENN_mono_set {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))} (hST : S ⊆ T) :
    HDP.Chapter8.euclideanSetGaussianWidthENN S ≤
      HDP.Chapter8.euclideanSetGaussianWidthENN T := by
  unfold HDP.Chapter8.euclideanSetGaussianWidthENN
  apply iSup_le
  intro F
  apply iSup_le
  intro hFS
  apply iSup_le
  intro hF
  exact le_iSup_of_le F (le_iSup_of_le (hFS.trans hST)
    (le_iSup_of_le hF (le_refl _)))

/-- Gaussian width is unchanged by taking the genuine convex hull of an
arbitrary nonempty set. The proof gathers finite generators for each finite
subfamily of the hull, so no uncountable supremum is treated as measurable.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidthENN_convexHull {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    HDP.Chapter8.euclideanSetGaussianWidthENN (convexHull ℝ T) =
      HDP.Chapter8.euclideanSetGaussianWidthENN T := by
  apply le_antisymm
  · unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    apply iSup_le
    intro F
    apply iSup_le
    intro hFhull
    apply iSup_le
    intro hF
    classical
    have hTne := hT
    obtain ⟨t0, ht0⟩ := hT
    have hgen : ∀ x : EuclideanSpace ℝ (Fin n),
        ∃ G : Finset (EuclideanSpace ℝ (Fin n)),
          G.Nonempty ∧ (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ T ∧
            (x ∈ F → x ∈ convexHull ℝ (G : Set _)) := by
      intro x
      by_cases hx : x ∈ F
      · rcases exists_finset_generator_of_mem_convexHull_constrained_recovery hTne (hFhull hx) with
          ⟨G, hG, hGT, hxG⟩
        exact ⟨G, hG, hGT, fun _ => hxG⟩
      · exact ⟨{t0}, by simp, by simpa using ht0,
          fun hxF => (hx hxF).elim⟩
    choose G hGne hGT hxG using hgen
    let U : Finset (EuclideanSpace ℝ (Fin n)) := F.biUnion G
    have hFne := hF
    obtain ⟨x0, hx0⟩ := hF
    obtain ⟨u0, hu0⟩ := hGne x0
    have hU : U.Nonempty :=
      ⟨u0, Finset.mem_biUnion.mpr ⟨x0, hx0, hu0⟩⟩
    have hUT : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ T := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨x, hx, huG⟩
      exact hGT x huG
    have hFU : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆
        convexHull ℝ (U : Set _) := by
      intro x hx
      exact convexHull_mono
        (fun u hu => Finset.mem_biUnion.mpr ⟨x, hx, hu⟩) (hxG x hx)
    calc
      ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
          ENNReal.ofReal (HDP.Chapter7.gaussianWidth U) :=
        ENNReal.ofReal_le_ofReal
          (finiteGaussianWidth_le_of_subset_convexHull F U hFne hU hFU)
      _ ≤ HDP.Chapter8.euclideanSetGaussianWidthENN T := by
        unfold HDP.Chapter8.euclideanSetGaussianWidthENN
        exact le_iSup_of_le U (le_iSup_of_le hUT
          (le_iSup_of_le hU (le_refl _)))
  · exact euclideanSetGaussianWidthENN_mono_set (subset_convexHull ℝ T)

/-- Taking a convex hull does not change the Gaussian width of a bounded set.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidth_convexHull {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    HDP.Chapter8.euclideanSetGaussianWidth (convexHull ℝ T) =
      HDP.Chapter8.euclideanSetGaussianWidth T := by
  unfold HDP.Chapter8.euclideanSetGaussianWidth
  rw [euclideanSetGaussianWidthENN_convexHull T hT]

/-- Positive dilation bound for the actual-set width envelope.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidthENN_smul_le {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) {a : ℝ} (ha : 0 < a) :
    HDP.Chapter8.euclideanSetGaussianWidthENN (a • T) ≤
      ENNReal.ofReal a * HDP.Chapter8.euclideanSetGaussianWidthENN T := by
  classical
  unfold HDP.Chapter8.euclideanSetGaussianWidthENN
  apply iSup_le
  intro F
  apply iSup_le
  intro hFa
  apply iSup_le
  intro hF
  let G : Finset (EuclideanSpace ℝ (Fin n)) :=
    F.image (fun x => a⁻¹ • x)
  have hG : G.Nonempty := hF.image _
  have hGT : (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxF, rfl⟩
    rcases Set.mem_smul_set.mp (hFa hxF) with ⟨z, hzT, hzx⟩
    rw [← hzx, ← mul_smul]
    simpa [ha.ne'] using hzT
  have hscale : HDP.Chapter7.scaleFinset a G = F := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hyG, rfl⟩
      rcases Finset.mem_image.mp hyG with ⟨z, hzF, rfl⟩
      simpa [HDP.Chapter7.scaleFinset, ha.ne'] using hzF
    · intro hx
      unfold HDP.Chapter7.scaleFinset
      apply Finset.mem_image.mpr
      refine ⟨a⁻¹ • x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      rw [← mul_smul]
      simp [ha.ne']
  calc
    ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) =
        ENNReal.ofReal (a * HDP.Chapter7.gaussianWidth G) := by
      rw [← HDP.Chapter7.gaussianWidth_scale_of_nonneg G hG ha.le, hscale]
    _ = ENNReal.ofReal a *
        ENNReal.ofReal (HDP.Chapter7.gaussianWidth G) := by
      rw [ENNReal.ofReal_mul ha.le]
    _ ≤ ENNReal.ofReal a *
        (⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
          (_ : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
          (_ : F.Nonempty), ENNReal.ofReal (HDP.Chapter7.gaussianWidth F)) := by
      gcongr
      exact le_iSup_of_le G (le_iSup_of_le hGT
        (le_iSup_of_le hG (le_refl _)))

/-- Scaling a bounded set scales its Gaussian width by at most the absolute value of the scalar.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidth_smul_le {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) {a : ℝ} (ha : 0 < a) :
    HDP.Chapter8.euclideanSetGaussianWidth (a • T) ≤
      a * HDP.Chapter8.euclideanSetGaussianWidth T := by
  have hTtop := HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top hT hTb
  have haTne : (a • T).Nonempty := Set.Nonempty.smul_set hT
  have haTb : Bornology.IsBounded (a • T) := hTb.smul₀ a
  have haTtop := HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top haTne haTb
  have hENN := euclideanSetGaussianWidthENN_smul_le T ha
  have hprodtop : ENNReal.ofReal a *
      HDP.Chapter8.euclideanSetGaussianWidthENN T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTtop
  have hreal := ENNReal.toReal_mono hprodtop hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le] at hreal
  simpa [HDP.Chapter8.euclideanSetGaussianWidth] using hreal

/-- Constrained recovery becomes accurate above the prior's effective dimension.

**Book Remark 9.4.5.** -/
theorem remark_9_4_5_effectiveDimension
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ) (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hTne : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x T)
    {diameter : ℝ} (hdiameter : 0 < diameter)
    (hsize : (100 * (mStarConstant * K ^ 2 *
      HDP.Chapter8.euclideanSetGaussianWidth T) / diameter) ^ 2 ≤ (m : ℝ)) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤ diameter / 100 := by
  have hmain := theorem_9_4_4_constrainedRecovery hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hTne hTb x hx xhat hxhatm hsol
  let a : ℝ := mStarConstant * K ^ 2 *
    HDP.Chapter8.euclideanSetGaussianWidth T
  have ha : 0 ≤ a := by
    exact mul_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K))
      ENNReal.toReal_nonneg
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hq : 0 ≤ 100 * a / diameter := by positivity
  have hqle : 100 * a / diameter ≤ Real.sqrt m := by
    apply (sq_le_sq₀ hq hsqrt.le).mp
    rw [Real.sq_sqrt hmR.le]
    simpa [a] using hsize
  have hmul : 100 * a ≤ Real.sqrt m * diameter :=
    (div_le_iff₀ hdiameter).mp hqle
  have hrate : a / Real.sqrt m ≤ diameter / 100 := by
    apply (div_le_iff₀ hsqrt).2
    nlinarith
  exact hmain.trans (by simpa [a] using hrate)

/-- Convexifying the prior does not change Gaussian width or the recovery guarantee.

**Book Remark 9.4.6.** -/
theorem remark_9_4_6_convexRelaxation {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    HDP.Chapter8.euclideanSetGaussianWidth (convexHull ℝ T) =
      HDP.Chapter8.euclideanSetGaussianWidth T :=
  euclideanSetGaussianWidth_convexHull T hT

/-! ## Actual structural priors in noisy and penalized recovery -/

/-- Actual-set matrix-deviation transfer. Unlike the finite compatibility
engine above, this theorem controls every measurable selector whose values
belong to an arbitrary nonempty bounded prior.

**Lean implementation helper.** -/
theorem expected_error_of_action_bound_set
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ) (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hTne : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun ω => ‖w ω‖) μ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hxhatT : ∀ ω, xhat ω ∈ T)
    {c : ℝ} (hc : 0 ≤ c)
    (haction : ∀ ω,
      ‖matrixAction A (xhat ω - x) ω‖ ≤ c * ‖w ω‖) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤
      (c * (∫ ω, ‖w ω‖ ∂μ) +
        mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth T) / Real.sqrt m := by
  letI : Nonempty T := hTne.to_subtype
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hTb
  have herrMeas : Measurable (fun ω => ‖xhat ω - x‖) :=
    (hxhatm.sub measurable_const).norm
  have herrInt : Integrable (fun ω => ‖xhat ω - x‖) μ := by
    refine Integrable.of_bound herrMeas.aestronglyMeasurable (2 * R) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖xhat ω - x‖ ≤ ‖xhat ω‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hR (xhat ω) (hxhatT ω)) (hR x hx)
      _ = 2 * R := by ring
  have hpoint : ∀ ω,
      ENNReal.ofReal (Real.sqrt m * ‖xhat ω - x‖) ≤
        ENNReal.ofReal (c * ‖w ω‖) +
          setDifferenceMatrixDeviationENN A T ω := by
    intro ω
    have hdev := abs_matrixDeviationProcess_le_setDifferenceMatrixDeviationENN
      A T (hxhatT ω) hx ω
    have hsqrtBound : Real.sqrt m * ‖xhat ω - x‖ ≤
        ‖matrixAction A (xhat ω - x) ω‖ +
          |matrixDeviationProcess A (xhat ω - x) ω| := by
      have h := le_abs_self
        (Real.sqrt m * ‖xhat ω - x‖ -
          ‖matrixAction A (xhat ω - x) ω‖)
      rw [sub_le_iff_le_add] at h
      simpa [matrixDeviationProcess, abs_sub_comm, add_comm] using h
    calc
      ENNReal.ofReal (Real.sqrt m * ‖xhat ω - x‖) ≤
          ENNReal.ofReal
            (c * ‖w ω‖ + |matrixDeviationProcess A (xhat ω - x) ω|) :=
        ENNReal.ofReal_le_ofReal (hsqrtBound.trans
          (add_le_add (haction ω) (le_refl _)))
      _ = ENNReal.ofReal (c * ‖w ω‖) +
          ENNReal.ofReal |matrixDeviationProcess A (xhat ω - x) ω| := by
        rw [ENNReal.ofReal_add]
        · exact mul_nonneg hc (norm_nonneg _)
        · exact abs_nonneg _
      _ ≤ ENNReal.ofReal (c * ‖w ω‖) +
          setDifferenceMatrixDeviationENN A T ω := by gcongr
  have hdevMean := lintegral_setDifferenceMatrixDeviationENN_le hm A hrowsm
    hsub hiso hindep hfinite hK hpsi T hTne hTb
  have hscaledInt : Integrable
      (fun ω => Real.sqrt m * ‖xhat ω - x‖) μ :=
    herrInt.const_mul (Real.sqrt m)
  have hscaled0 : ∀ ω, 0 ≤ Real.sqrt m * ‖xhat ω - x‖ :=
    fun ω => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnoiseInt : Integrable (fun ω => c * ‖w ω‖) μ :=
    hwInt.const_mul c
  have hnoise0 : ∀ ω, 0 ≤ c * ‖w ω‖ :=
    fun ω => mul_nonneg hc (norm_nonneg _)
  have hENN : ENNReal.ofReal
      (∫ ω, Real.sqrt m * ‖xhat ω - x‖ ∂μ) ≤
      ENNReal.ofReal (c * (∫ ω, ‖w ω‖ ∂μ)) +
        ENNReal.ofReal (mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth T) := by
    rw [ofReal_integral_eq_lintegral_ofReal hscaledInt
      (Filter.Eventually.of_forall hscaled0)]
    calc
      (∫⁻ ω, ENNReal.ofReal (Real.sqrt m * ‖xhat ω - x‖) ∂μ) ≤
          ∫⁻ ω, (ENNReal.ofReal (c * ‖w ω‖) +
            setDifferenceMatrixDeviationENN A T ω) ∂μ :=
        lintegral_mono hpoint
      _ = (∫⁻ ω, ENNReal.ofReal (c * ‖w ω‖) ∂μ) +
          ∫⁻ ω, setDifferenceMatrixDeviationENN A T ω ∂μ :=
        lintegral_add_right _
          (measurable_setDifferenceMatrixDeviationENN A hrowsm T)
      _ ≤ ENNReal.ofReal (c * (∫ ω, ‖w ω‖ ∂μ)) +
          ENNReal.ofReal (mStarConstant * K ^ 2 *
            HDP.Chapter8.euclideanSetGaussianWidth T) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hnoiseInt
          (Filter.Eventually.of_forall hnoise0), integral_const_mul]
        exact add_le_add (le_refl _) hdevMean
  have hnoiseMean0 : 0 ≤ ∫ ω, ‖w ω‖ ∂μ :=
    integral_nonneg fun _ => norm_nonneg _
  have hwidth0 : 0 ≤ HDP.Chapter8.euclideanSetGaussianWidth T :=
    ENNReal.toReal_nonneg
  have hrhs0 : 0 ≤ c * (∫ ω, ‖w ω‖ ∂μ) +
      mStarConstant * K ^ 2 * HDP.Chapter8.euclideanSetGaussianWidth T :=
    add_nonneg (mul_nonneg hc hnoiseMean0)
      (mul_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K)) hwidth0)
  have hreal : (∫ ω, Real.sqrt m * ‖xhat ω - x‖ ∂μ) ≤
      c * (∫ ω, ‖w ω‖ ∂μ) +
        mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth T := by
    apply (ENNReal.ofReal_le_ofReal_iff hrhs0).mp
    simpa [ENNReal.ofReal_add,
      mul_nonneg hc hnoiseMean0,
      mul_nonneg (mul_nonneg mStarConstant_pos.le (sq_nonneg K)) hwidth0]
      using hENN
  apply (le_div_iff₀ hsqrt).2
  rw [integral_const_mul] at hreal
  simpa [mul_comm] using hreal

/-- Constrained recovery in the noisy linear model.

**Book Exercise 9.19.** -/
theorem exercise_9_19
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ) (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hTne : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun ω => ‖w ω‖) μ)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hmin : ∀ ω, IsNoisyConstrainedRecoveryMinimizer (A ω)
      (noisyLinearObservation (A ω) x (w ω)) T (xhat ω)) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤
      (2 * (∫ ω, ‖w ω‖ ∂μ) +
        mStarConstant * K ^ 2 *
          HDP.Chapter8.euclideanSetGaussianWidth T) / Real.sqrt m := by
  apply expected_error_of_action_bound_set hm A hrowsm hsub hiso hindep hfinite
    hK hpsi T hTne hTb x hx w hwInt xhat hxhatm
    (fun ω => (hmin ω).1) (by norm_num : (0 : ℝ) ≤ 2)
  intro ω
  rw [← deterministicMatrixAction_eq_matrixAction A (xhat ω - x) ω]
  exact noisyConstrained_action_error_le (A ω) (w ω) T hx (hmin ω)

/-- The actual unit ball of the penalty norm in Remark 9.4.7.

**Book Remark 9.4.7.** -/
def penaltyUnitBall {n : ℕ}
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | penalty z ≤ 1}

/-- A real-valued norm supplied as a function, together with the boundedness
of its unit ball in the ambient Euclidean norm. -/
structure IsPenaltyNorm {n : ℕ}
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ penalty z
  eq_zero_iff : ∀ z, penalty z = 0 ↔ z = 0
  add_le : ∀ x y, penalty (x + y) ≤ penalty x + penalty y
  smul : ∀ (a : ℝ) z, penalty (a • z) = |a| * penalty z
  unitBall_isBounded : Bornology.IsBounded (penaltyUnitBall penalty)

/-- The unit ball of a penalty norm is nonempty because it contains the origin.

**Lean implementation helper.** -/
theorem IsPenaltyNorm.unitBall_nonempty {n : ℕ}
    {penalty : EuclideanSpace ℝ (Fin n) → ℝ}
    (hp : IsPenaltyNorm penalty) :
    (penaltyUnitBall penalty).Nonempty := by
  refine ⟨0, ?_⟩
  have hp0 : penalty 0 = 0 := (hp.eq_zero_iff 0).2 rfl
  simp [penaltyUnitBall, hp0]

/-- Every vector lies in the penalty unit ball scaled by its own penalty value.

**Lean implementation helper.** -/
theorem mem_scaledPenaltyUnitBall {n : ℕ}
    {penalty : EuclideanSpace ℝ (Fin n) → ℝ}
    (hp : IsPenaltyNorm penalty)
    {R : ℝ} (hR : 0 < R) {x : EuclideanSpace ℝ (Fin n)}
    (hx : penalty x ≤ R) :
    x ∈ R • penaltyUnitBall penalty := by
  apply Set.mem_smul_set.mpr
  refine ⟨R⁻¹ • x, ?_, ?_⟩
  · change penalty (R⁻¹ • x) ≤ 1
    rw [hp.smul, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_one₀ hR).2 hx
  · rw [← mul_smul]
    simp [hR.ne']

/-- The lower half of the source's two-sided tuning condition places every
penalized minimizer in a fixed dilation of the actual norm unit ball.

**Lean implementation helper.** -/
theorem penalizedRecovery_penalty_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin m))
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    {cLower lam : ℝ} (hcLower : 0 < cLower) (hlam : 0 < lam)
    (htuneLower : cLower * ‖w‖ ^ 2 ≤ lam * penalty x)
    (xhat : EuclideanSpace ℝ (Fin n))
    (hmin : IsPenalizedRecoveryMinimizer A
      (noisyLinearObservation A x w) penalty lam xhat) :
    penalty xhat ≤ (1 + cLower⁻¹) * penalty x := by
  have hbasic := penalizedRecovery_basicInequality A x w penalty lam xhat hmin
  have hmul : lam * penalty xhat ≤ ‖w‖ ^ 2 + lam * penalty x := by
    dsimp [penalizedRecoveryObjective] at hbasic
    have hres0 : 0 ≤
        ‖noisyLinearObservation A x w - deterministicMatrixAction A xhat‖ ^ 2 :=
      sq_nonneg _
    linarith
  have hwle : ‖w‖ ^ 2 ≤ cLower⁻¹ * (lam * penalty x) :=
    (le_inv_mul_iff₀ hcLower).2 htuneLower
  have hscaled : lam * penalty xhat ≤
      lam * ((1 + cLower⁻¹) * penalty x) := by
    calc
      lam * penalty xhat ≤ ‖w‖ ^ 2 + lam * penalty x := hmul
      _ ≤ cLower⁻¹ * (lam * penalty x) + lam * penalty x :=
        add_le_add hwle (le_refl _)
      _ = lam * ((1 + cLower⁻¹) * penalty x) := by ring
  exact (mul_le_mul_iff_of_pos_left hlam).mp hscaled

/-- Penalized unconstrained optimization gives a robust alternative to exact feasibility. The displayed geometric term is the Gaussian width of the genuine unit ball
times `penalty x`; the factor `1 + cLower⁻¹` records the explicit two-sided
tuning constant.

**Book Remark 9.4.7.** -/
theorem exercise_9_20
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ) (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n))
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun ω => ‖w ω‖) μ)
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpen : IsPenaltyNorm penalty) (hxpen : 0 < penalty x)
    {cLower : ℝ} (hcLower : 0 < cLower)
    (lam : Ω → ℝ) (hlam : ∀ ω, 0 < lam ω)
    (htuneLower : ∀ ω,
      cLower * ‖w ω‖ ^ 2 ≤ lam ω * penalty x)
    (htuneUpper : ∀ ω,
      lam ω * penalty x ≤ ‖w ω‖ ^ 2)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hmin : ∀ ω, IsPenalizedRecoveryMinimizer (A ω)
      (noisyLinearObservation (A ω) x (w ω)) penalty (lam ω) (xhat ω)) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤
      (3 * (∫ ω, ‖w ω‖ ∂μ) +
        mStarConstant * K ^ 2 *
          ((1 + cLower⁻¹) * penalty x *
            HDP.Chapter8.euclideanSetGaussianWidth
              (penaltyUnitBall penalty))) / Real.sqrt m := by
  let R : ℝ := (1 + cLower⁻¹) * penalty x
  let T : Set (EuclideanSpace ℝ (Fin n)) :=
    R • penaltyUnitBall penalty
  have hfactor : 0 < 1 + cLower⁻¹ := by positivity
  have hR : 0 < R := mul_pos hfactor hxpen
  have hxR : penalty x ≤ R := by
    dsimp [R]
    have hinv0 : 0 ≤ cLower⁻¹ := (inv_pos.mpr hcLower).le
    nlinarith
  have hxT : x ∈ T := mem_scaledPenaltyUnitBall hpen hR hxR
  have hxhatT : ∀ ω, xhat ω ∈ T := by
    intro ω
    apply mem_scaledPenaltyUnitBall hpen hR
    exact penalizedRecovery_penalty_le (A ω) x (w ω) penalty
      hcLower (hlam ω) (htuneLower ω) (xhat ω) (hmin ω)
  have hTne : T.Nonempty := ⟨x, hxT⟩
  have hTb : Bornology.IsBounded T := hpen.unitBall_isBounded.smul₀ R
  have hwidth : HDP.Chapter8.euclideanSetGaussianWidth T ≤
      R * HDP.Chapter8.euclideanSetGaussianWidth (penaltyUnitBall penalty) :=
    euclideanSetGaussianWidth_smul_le (penaltyUnitBall penalty)
      hpen.unitBall_nonempty hpen.unitBall_isBounded hR
  have hmain := expected_error_of_action_bound_set hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hTne hTb x hxT w hwInt xhat hxhatm hxhatT
    (by norm_num : (0 : ℝ) ≤ 3) (fun ω => by
      rw [← deterministicMatrixAction_eq_matrixAction A (xhat ω - x) ω]
      exact penalizedRecovery_action_error_le (A ω) x (w ω) penalty
        hpen.nonneg (hlam ω) (htuneUpper ω) (xhat ω) (hmin ω))
  apply hmain.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply add_le_add_right
  have hw := mul_le_mul_of_nonneg_left hwidth
    (mul_nonneg mStarConstant_pos.le (sq_nonneg K))
  simpa [R] using hw

/-- Penalized unconstrained optimization gives a robust alternative to exact feasibility.

**Book Remark 9.4.7.** -/
theorem remark_9_4_7_unconstrainedOptimization
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ) (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n))
    (w : Ω → EuclideanSpace ℝ (Fin m))
    (hwInt : Integrable (fun ω => ‖w ω‖) μ)
    (penalty : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpen : IsPenaltyNorm penalty) (hxpen : 0 < penalty x)
    {cLower : ℝ} (hcLower : 0 < cLower)
    (lam : Ω → ℝ) (hlam : ∀ ω, 0 < lam ω)
    (htuneLower : ∀ ω,
      cLower * ‖w ω‖ ^ 2 ≤ lam ω * penalty x)
    (htuneUpper : ∀ ω,
      lam ω * penalty x ≤ ‖w ω‖ ^ 2)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hmin : ∀ ω, IsPenalizedRecoveryMinimizer (A ω)
      (noisyLinearObservation (A ω) x (w ω)) penalty (lam ω) (xhat ω)) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤
      (3 * (∫ ω, ‖w ω‖ ∂μ) +
        mStarConstant * K ^ 2 *
          ((1 + cLower⁻¹) * penalty x *
            HDP.Chapter8.euclideanSetGaussianWidth
              (penaltyUnitBall penalty))) / Real.sqrt m :=
  exercise_9_20 hm A hrowsm hsub hiso hindep hfinite hK hpsi x w hwInt
    penalty hpen hxpen hcLower lam hlam htuneLower htuneUpper xhat hxhatm hmin

end

end HDP.Chapter9

end Source_10_ConstrainedRecovery

/-! ## Material formerly in `11_SparseRecovery.lean` -/

section Source_11_SparseRecovery

/-!
# Book Chapter 9, §9.4.2: sparse recovery

Support sizes are natural numbers and every logarithmic endpoint later assumes
`1 ≤ s ≤ n`.  Exercise 9.22(a) is corrected here: an underdetermined system
cannot have a unique unrestricted solution; the valid conclusion is uniqueness
inside the class of `s`-sparse vectors.
-/

open Filter MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators ENNReal Pointwise RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `ell0` counts nonzero coordinates and defines sparsity. Coordinate support of a finite Euclidean vector.

**Book Equation (9.21).** -/
def coordinateSupport {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ≠ 0

/-- An index belongs to the coordinate support exactly when the corresponding coordinate is nonzero.

**Lean implementation helper.** -/
@[simp] theorem mem_coordinateSupport {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    i ∈ coordinateSupport x ↔ x i ≠ 0 := by
  simp [coordinateSupport]

/-- `ell0` counts nonzero coordinates and defines sparsity. Display (9.21): the `ℓ⁰` support count.

**Book Equation (9.21).** -/
def ellZero {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  (coordinateSupport x).card

/-- `ell0` counts nonzero coordinates and defines sparsity. A vector has at most `s` nonzero coordinates.

**Book Equation (9.21).** -/
def IsSparse {n : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ellZero x ≤ s

/-! ## Exercise 9.23: the quasi-norm range `0 ≤ p < 1` -/

/-- `ell0` and `ellp` for `p<1` fail norm axioms, and `ellp^p` tends to support size. In positive dimension the support count fails
absolute homogeneity, hence cannot be a norm.

**Book Exercise 9.23(a--c).** -/
theorem exercise_9_23a_ellZero_not_homogeneous {n : ℕ} (hn : 0 < n) :
    ¬(∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      (ellZero (c • x) : ℝ) = |c| * ellZero x) := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have hxSupport : coordinateSupport x = {i} := by
    ext j
    simp [coordinateSupport, x]
  have h2Support : coordinateSupport ((2 : ℝ) • x) = {i} := by
    ext j
    simp [coordinateSupport, x]
  have hh := h 2 x
  simp [ellZero, hxSupport, h2Support] at hh

/-- `ell0` and `ellp` for `p<1` fail norm axioms, and `ellp^p` tends to support size. For
`0 < p < 1`, the finite `ℓᵖ` functional violates the triangle inequality
as soon as two coordinates are available.

**Book Exercise 9.23(a--c).** -/
theorem exercise_9_23b_lp_not_triangle {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ x y : EuclideanSpace ℝ (Fin n),
      HDP.Chapter1.lpNorm p (fun i => (x + y) i) >
        HDP.Chapter1.lpNorm p (fun i => x i) +
          HDP.Chapter1.lpNorm p (fun i => y i) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  let y : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  have hexp : (2 : ℝ) < 2 ^ (1 / p) := by
    have hone : (1 : ℝ) < 1 / p := by
      rw [lt_div_iff₀ hp0]
      simpa using hp1
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hone
  refine ⟨x, y, ?_⟩
  rw [HDP.Chapter1.lpNorm_eq_sum hp0, HDP.Chapter1.lpNorm_eq_sum hp0,
    HDP.Chapter1.lpNorm_eq_sum hp0]
  have hxsum : (∑ k : Fin n, |x k| ^ p) = 1 := by
    classical
    simp only [x, PiLp.single_apply]
    have hterm : ∀ k : Fin n,
        |if k = i then (1 : ℝ) else 0| ^ p = if k = i then 1 else 0 := by
      intro k
      split_ifs <;> simp [hp0.ne']
    simp_rw [hterm]
    simp
  have hysum : (∑ k : Fin n, |y k| ^ p) = 1 := by
    classical
    simp only [y, PiLp.single_apply]
    have hterm : ∀ k : Fin n,
        |if k = j then (1 : ℝ) else 0| ^ p = if k = j then 1 else 0 := by
      intro k
      split_ifs <;> simp [hp0.ne']
    simp_rw [hterm]
    simp
  have hxysum : (∑ k : Fin n, |(x + y) k| ^ p) = 2 := by
    classical
    rw [WithLp.ofLp_add]
    simp only [x, y, Pi.add_apply, PiLp.single_apply]
    have hterm : ∀ k : Fin n,
        |(if k = i then (1 : ℝ) else 0) + (if k = j then 1 else 0)| ^ p =
          if k = i then 1 else if k = j then 1 else 0 := by
      intro k
      by_cases hki : k = i
      · have hkj : k ≠ j := by simpa [hki] using hij
        simp [hki, hij]
      · by_cases hkj : k = j <;> simp [hki, hkj, hij.symm, hp0.ne']
    calc
      (∑ k : Fin n,
          |(if k = i then (1 : ℝ) else 0) + (if k = j then 1 else 0)| ^ p) =
          ∑ k : Fin n, if k = i then 1 else if k = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
      _ = 2 := by
        have hsplit : ∀ k : Fin n,
            (if k = i then (1 : ℝ) else if k = j then 1 else 0) =
              (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
          intro k
          by_cases hki : k = i <;> by_cases hkj : k = j <;>
            simp [hki, hkj, hij, hij.symm]
        simp_rw [hsplit, Finset.sum_add_distrib]
        rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
        norm_num
  rw [hxsum, hysum, hxysum]
  norm_num
  simpa only [one_div] using hexp

/-- The source expression `‖x‖ᵖᵖ`, kept meaningful also while taking the
one-sided limit `p →0+`.

**Lean implementation helper.** -/
def ellPQuasiPower {n : ℕ} (p : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, |x i| ^ p

/-- The coordinate `p`-power sum is the `ℓᵖ` norm raised to the power `p`.

**Lean implementation helper.** -/
theorem ellPQuasiPower_eq_lpNorm_rpow {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : EuclideanSpace ℝ (Fin n)) :
    ellPQuasiPower p x = HDP.Chapter1.lpNorm p (fun i => x i) ^ p := by
  rw [ellPQuasiPower, HDP.Chapter1.lpNorm_eq_sum hp]
  have hsum : 0 ≤ ∑ i, |x i| ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  simpa [one_div] using (Real.rpow_inv_rpow hsum hp.ne').symm

/-- `ell0` and `ellp` for `p<1` fail norm axioms, and `ellp^p` tends to support size.

**Book Exercise 9.23(a--c).** -/
theorem exercise_9_23c_tendsto_ellPQuasiPower {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun p : ℝ => ellPQuasiPower p x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ellZero x : ℝ)) := by
  have hcoord : ∀ i : Fin n,
      Tendsto (fun p : ℝ => |x i| ^ p) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (if x i = 0 then 0 else 1)) := by
    intro i
    by_cases hi : x i = 0
    · have heq : (fun p : ℝ => |x i| ^ p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun _ => 0 := by
        filter_upwards [self_mem_nhdsWithin] with p hp
        have hp0 : 0 < p := hp
        simp [hi, Real.zero_rpow hp0.ne']
      simpa [hi] using tendsto_const_nhds.congr' heq.symm
    · have hcont : ContinuousAt (fun p : ℝ => |x i| ^ p) 0 :=
        Real.continuousAt_const_rpow (abs_ne_zero.mpr hi)
      have ht := hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa [hi] using ht
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  have hlimit : (∑ i : Fin n, if x i = 0 then (0 : ℝ) else 1) = ellZero x := by
    rw [ellZero, coordinateSupport]
    simpa [Finset.sum_boole] using
      (Finset.sum_boole (R := ℝ) (fun i : Fin n => x i ≠ 0) Finset.univ)
  simpa [ellPQuasiPower, hlimit] using hsum

/-- The finite `ℓ¹` norm used by the recovery programs.

**Lean implementation helper.** -/
def ellOne {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, |x i|

/-- Coordinate restriction, padded by zero in the original ambient space.

**Lean implementation helper.** -/
def coordinateRestriction {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i ∈ S then x i else 0)

/-- Coordinate restriction keeps entries on the selected support and sets all other entries to zero.

**Lean implementation helper.** -/
@[simp] theorem coordinateRestriction_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) (i : Fin n) :
    coordinateRestriction x S i = if i ∈ S then x i else 0 :=
  rfl

/-- Restricting a vector to a set of coordinates cannot introduce new support.

**Lean implementation helper.** -/
theorem coordinateSupport_restriction_subset {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) :
    coordinateSupport (coordinateRestriction x S) ⊆ S := by
  intro i hi
  by_contra hiS
  have hne := (mem_coordinateSupport (coordinateRestriction x S) i).1 hi
  exact hne (by simp [coordinateRestriction, hiS])

/-- Restriction to a set of cardinality at most `s` produces an `s`-sparse vector.

**Lean implementation helper.** -/
theorem restriction_isSparse {n s : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {S : Finset (Fin n)}
    (hS : S.card ≤ s) : IsSparse s (coordinateRestriction x S) := by
  exact (Finset.card_le_card (coordinateSupport_restriction_subset x S)).trans hS

/-- A vector is the sum of its restrictions to a coordinate set and its complement.

**Lean implementation helper.** -/
theorem restriction_add_compl {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) :
    coordinateRestriction x S + coordinateRestriction x Sᶜ = x := by
  ext i
  by_cases hi : i ∈ S <;> simp [coordinateRestriction, hi]

/-- The coordinate `ℓ¹` functional is nonnegative.

**Lean implementation helper.** -/
theorem ellOne_nonneg {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ellOne x := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The coordinate `ℓ¹` functional vanishes at the zero vector.

**Lean implementation helper.** -/
@[simp] theorem ellOne_zero {n : ℕ} :
    ellOne (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [ellOne]

/-- The coordinate `ℓ¹` functional satisfies the triangle inequality.

**Lean implementation helper.** -/
theorem ellOne_add_le {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) :
    ellOne (x + y) ≤ ellOne x + ellOne y := by
  dsimp [ellOne]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (x i) (y i)

/-- Scalar multiplication scales the coordinate `ℓ¹` functional by the scalar's absolute value.

**Lean implementation helper.** -/
theorem ellOne_smul {n : ℕ} (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ellOne (c • x) = |c| * ellOne x := by
  simp [ellOne, abs_mul, Finset.mul_sum]

/-- The `ℓ¹` distance is bounded by the sum of the two `ℓ¹` norms.

**Lean implementation helper.** -/
theorem ellOne_sub_le {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) :
    ellOne (x - y) ≤ ellOne x + ellOne y := by
  simpa [sub_eq_add_neg, ellOne] using ellOne_add_le x (-y)

/-- The coordinate `ℓ¹` functional vanishes exactly at the zero vector.

**Lean implementation helper.** -/
theorem ellOne_eq_zero_iff {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : ellOne x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hi : |x i| = 0 := by
      have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |x j| :=
        fun _ _ => abs_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h i (Finset.mem_univ i)
    simpa using (abs_eq_zero.mp hi)
  · rintro rfl
    exact ellOne_zero

/-- The `ℓ¹` norm is the sum of absolute coordinates over the vector's support.

**Lean implementation helper.** -/
theorem ellOne_eq_sum_coordinateSupport {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ellOne x = ∑ i ∈ coordinateSupport x, |x i| := by
  rw [ellOne]
  symm
  apply Finset.sum_subset (coordinateSupport x).subset_univ
  intro i hi hiSupport
  have hxi : x i = 0 := not_ne_iff.mp ((mem_coordinateSupport x i).not.mp hiSupport)
  simp [hxi]

/-- The `ℓ¹` norm is at most the square root of support size times the Euclidean norm.

**Lean implementation helper.** -/
theorem ellOne_le_sqrt_support_mul_norm {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ellOne x ≤ Real.sqrt (ellZero x) * ‖x‖ := by
  let S := coordinateSupport x
  have hsumSq : ∑ i ∈ S, |x i| ^ 2 ≤ ∑ i, |x i| ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
      (fun i hi hnot => by positivity)
  have hnormSq : ∑ i, |x i| ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact sq_abs (x i)
  have hsq0 := sq_sum_le_card_mul_sum_sq
    (s := S) (f := fun i => |x i|)
  have hsq : ellOne x ^ 2 ≤ (S.card : ℝ) * ‖x‖ ^ 2 := by
    rw [ellOne_eq_sum_coordinateSupport]
    calc
      (∑ i ∈ S, |x i|) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, |x i| ^ 2 := hsq0
      _ ≤ (S.card : ℝ) * ∑ i, |x i| ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq (by positivity)
      _ = (S.card : ℝ) * ‖x‖ ^ 2 := by rw [hnormSq]
  have hrhs0 : 0 ≤ Real.sqrt (ellZero x) * ‖x‖ := by positivity
  apply (sq_le_sq₀ (ellOne_nonneg x) hrhs0).mp
  calc
    ellOne x ^ 2 ≤ (S.card : ℝ) * ‖x‖ ^ 2 := hsq
    _ = (Real.sqrt (ellZero x) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ellZero x)]
      rfl

/-- Every `s`-sparse unit vector has `l1` norm at most `sqrt s`.

**Book Section 9.4.2, before (9.22).** -/
theorem ellOne_le_sqrt_sparse_mul_norm {n s : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : IsSparse s x) :
    ellOne x ≤ Real.sqrt s * ‖x‖ := by
  exact (ellOne_le_sqrt_support_mul_norm x).trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by exact_mod_cast hx)) (norm_nonneg x))

/-- Unit `s`-sparse set. Display (9.46), with the source's “unit” interpreted as the closed unit
Euclidean ball exactly as printed.

**Book Equation (9.46), Exercise 9.25.** -/
def sparseUnitSet (n s : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | IsSparse s x ∧ ‖x‖ ≤ 1}

/-- Truncated `l1` ball. Display (9.47): the truncated `ℓ¹` ball.

**Book Equation (9.47), Exercise 9.25.** -/
def truncatedL1Ball (n s : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ellOne x ≤ Real.sqrt s ∧ ‖x‖ ≤ 1}

/-- The `ℓ¹` norm of a coordinate restriction is the absolute-coordinate sum over the restricted set.

**Lean implementation helper.** -/
theorem ellOne_coordinateRestriction_eq_sum {n : ℕ}
    (S : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    ellOne (coordinateRestriction x S) = ∑ i ∈ S, |x i| := by
  classical
  unfold ellOne
  calc
    ∑ i, |coordinateRestriction x S i| =
        ∑ i ∈ S, |coordinateRestriction x S i| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hiS
      simp [coordinateRestriction, hiS]
    _ = ∑ i ∈ S, |x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [coordinateRestriction, hi]

/-- The coordinate permutation which lists coefficients in nonincreasing
absolute value. Ties are resolved by `Tuple.sort`; no argument below depends
on the tie-breaking convention.

**Lean implementation helper.** -/
noncomputable def magnitudePermutation {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -|x i|)

/-- The `k`-th consecutive block of `b` coordinates after sorting by
decreasing magnitude. The final block may have fewer than `b` coordinates.

**Lean implementation helper.** -/
def magnitudeBlock {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (b k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    k * b ≤ ((magnitudePermutation x).symm i).val ∧
      ((magnitudePermutation x).symm i).val < (k + 1) * b

/-- Membership in a magnitude block means that a coordinate's rank lies in the corresponding dyadic range.

**Lean implementation helper.** -/
@[simp] theorem mem_magnitudeBlock {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) (i : Fin n) :
    i ∈ magnitudeBlock x b k ↔
      k * b ≤ ((magnitudePermutation x).symm i).val ∧
        ((magnitudePermutation x).symm i).val < (k + 1) * b := by
  simp [magnitudeBlock]

/-- Each magnitude block contains at most its prescribed block size.

**Lean implementation helper.** -/
theorem magnitudeBlock_card_le {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    (magnitudeBlock x b k).card ≤ b := by
  classical
  let σ := magnitudePermutation x
  calc
    (magnitudeBlock x b k).card ≤
        (Finset.Ico (k * b) ((k + 1) * b)).card := by
      apply Finset.card_le_card_of_injOn
        (fun i : Fin n => (σ.symm i).val)
      · intro i hi
        exact Finset.mem_Ico.mpr ((mem_magnitudeBlock x b k i).mp hi)
      · intro i hi j hj hij
        apply σ.symm.injective
        exact Fin.ext hij
    _ = b := by
      rw [Nat.card_Ico]
      simp [Nat.add_mul]

/-- Restricting to a magnitude block produces a vector sparse at the block's size.

**Lean implementation helper.** -/
theorem magnitudeBlock_restriction_sparse {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    IsSparse b (coordinateRestriction x (magnitudeBlock x b k)) :=
  restriction_isSparse x (magnitudeBlock_card_le x b k)

/-- A coordinate restriction cannot increase the Euclidean norm.

**Lean implementation helper.** -/
theorem norm_coordinateRestriction_le {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) :
    ‖coordinateRestriction x S‖ ≤ ‖x‖ := by
  have hsum : ∑ i ∈ S, |x i| ^ 2 ≤ ∑ i, |x i| ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
      (fun i hi hnot => by positivity)
  have hleft : ‖coordinateRestriction x S‖ ^ 2 = ∑ i ∈ S, |x i| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    classical
    simp [coordinateRestriction, sq_abs]
  have hright : ‖x‖ ^ 2 = ∑ i, |x i| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact (sq_abs (x i)).symm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    rw [hleft, hright]
    exact hsum)

/-- If every selected coordinate is bounded by `c`, its restricted Euclidean
norm is at most `sqrt (#S) * c`.

**Lean implementation helper.** -/
theorem norm_coordinateRestriction_le_sqrt_card_mul {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) {c : ℝ}
    (hc : 0 ≤ c) (hcoord : ∀ i ∈ S, |x i| ≤ c) :
    ‖coordinateRestriction x S‖ ≤ Real.sqrt S.card * c := by
  have hsum : ∑ i ∈ S, |x i| ^ 2 ≤ (S.card : ℝ) * c ^ 2 := by
    calc
      ∑ i ∈ S, |x i| ^ 2 ≤ ∑ _i ∈ S, c ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hic := hcoord i hi
        nlinarith [abs_nonneg (x i)]
      _ = (S.card : ℝ) * c ^ 2 := by simp
  have hleft : ‖coordinateRestriction x S‖ ^ 2 = ∑ i ∈ S, |x i| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    classical
    simp [coordinateRestriction, sq_abs]
  have hrhs : 0 ≤ Real.sqrt S.card * c := mul_nonneg (Real.sqrt_nonneg _) hc
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).mp
  rw [hleft, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ S.card)]
  exact hsum

/-- Every entry in a later magnitude block is bounded by every entry in the
preceding block.

**Lean implementation helper.** -/
theorem abs_le_of_mem_magnitudeBlock_succ {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b k : ℕ} {i j : Fin n}
    (hi : i ∈ magnitudeBlock x b (k + 1))
    (hj : j ∈ magnitudeBlock x b k) :
    |x i| ≤ |x j| := by
  let σ := magnitudePermutation x
  have hrank : σ.symm j ≤ σ.symm i := by
    apply Fin.le_iff_val_le_val.mpr
    have hi' := (mem_magnitudeBlock x b (k + 1) i).mp hi
    have hj' := (mem_magnitudeBlock x b k j).mp hj
    exact (Nat.lt_of_lt_of_le hj'.2 hi'.1).le
  have hmono := Tuple.monotone_sort (fun r : Fin n => -|x r|) hrank
  change -|x (σ (σ.symm j))| ≤ -|x (σ (σ.symm i))| at hmono
  simp only [Equiv.apply_symm_apply] at hmono
  linarith

/-- If the next magnitude block is nonempty, the current block has the full prescribed cardinality.

**Lean implementation helper.** -/
theorem magnitudeBlock_card_eq_of_succ_nonempty {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b k : ℕ}
    (hnext : (magnitudeBlock x b (k + 1)).Nonempty) :
    (magnitudeBlock x b k).card = b := by
  classical
  obtain ⟨i, hi⟩ := hnext
  have hi' := (mem_magnitudeBlock x b (k + 1) i).mp hi
  have hupper : (k + 1) * b < n :=
    lt_of_le_of_lt hi'.1 ((magnitudePermutation x).symm i).isLt
  have hkab : k * b < n :=
    (Nat.mul_le_mul_right b (Nat.le_succ k)).trans_lt hupper
  let a : Fin n := ⟨k * b, hkab⟩
  let c : Fin n := ⟨(k + 1) * b, hupper⟩
  let σ := magnitudePermutation x
  have hcard : (magnitudeBlock x b k).card = (Finset.Ico a c).card := by
    apply Finset.card_bijective σ.symm σ.symm.bijective
    intro j
    simp only [Finset.mem_Ico, mem_magnitudeBlock]
    change (k * b ≤ (σ.symm j).val ∧ (σ.symm j).val < (k + 1) * b) ↔
      a ≤ σ.symm j ∧ σ.symm j < c
    rfl
  rw [hcard, Fin.card_Ico]
  change (k + 1) * b - k * b = b
  simp [Nat.add_mul]

/-- The quantitative sorted-block estimate used both in Exercise 9.25 and
in the proof of Theorem 9.5.6.

**Book Exercise 9.25.** -/
theorem norm_magnitudeBlock_succ_le {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b k : ℕ} (hb : 0 < b) :
    ‖coordinateRestriction x (magnitudeBlock x b (k + 1))‖ ≤
      ellOne (coordinateRestriction x (magnitudeBlock x b k)) /
        Real.sqrt b := by
  classical
  by_cases hnext : (magnitudeBlock x b (k + 1)).Nonempty
  · have hprevCard := magnitudeBlock_card_eq_of_succ_nonempty x hnext
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hcoord : ∀ i ∈ magnitudeBlock x b (k + 1),
        |x i| ≤ ellOne (coordinateRestriction x (magnitudeBlock x b k)) / b := by
      intro i hi
      apply (le_div_iff₀ hbR).mpr
      rw [ellOne_coordinateRestriction_eq_sum]
      calc
        |x i| * (b : ℝ) = ∑ _j ∈ magnitudeBlock x b k, |x i| := by
          simp [hprevCard, mul_comm]
        _ ≤ ∑ j ∈ magnitudeBlock x b k, |x j| := by
          apply Finset.sum_le_sum
          intro j hj
          exact abs_le_of_mem_magnitudeBlock_succ x hi hj
    have hc0 : 0 ≤ ellOne (coordinateRestriction x (magnitudeBlock x b k)) / b :=
      div_nonneg (ellOne_nonneg _) hbR.le
    have hnorm := norm_coordinateRestriction_le_sqrt_card_mul x
      (magnitudeBlock x b (k + 1)) hc0 hcoord
    have hcard := magnitudeBlock_card_le x b (k + 1)
    have hsqrt : Real.sqrt (magnitudeBlock x b (k + 1)).card ≤ Real.sqrt b :=
      Real.sqrt_le_sqrt (by exact_mod_cast hcard)
    calc
      ‖coordinateRestriction x (magnitudeBlock x b (k + 1))‖ ≤
          Real.sqrt (magnitudeBlock x b (k + 1)).card *
            (ellOne (coordinateRestriction x (magnitudeBlock x b k)) / b) := hnorm
      _ ≤ Real.sqrt b *
            (ellOne (coordinateRestriction x (magnitudeBlock x b k)) / b) :=
        mul_le_mul_of_nonneg_right hsqrt hc0
      _ = ellOne (coordinateRestriction x (magnitudeBlock x b k)) /
            Real.sqrt b := by
        have hsqrtpos : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.2 hbR
        field_simp [hbR.ne', hsqrtpos.ne']
        rw [Real.sq_sqrt hbR.le]
        ring
  · have hempty : magnitudeBlock x b (k + 1) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnext
    have hz : coordinateRestriction x (magnitudeBlock x b (k + 1)) = 0 := by
      rw [hempty]
      ext i
      simp [coordinateRestriction]
    rw [hz, norm_zero]
    exact div_nonneg (ellOne_nonneg _) (Real.sqrt_nonneg _)

/-- A coordinate belongs to the block indexed by its rank divided by the block size.

**Lean implementation helper.** -/
theorem mem_magnitudeBlock_rank_div {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b : ℕ} (hb : 0 < b) (i : Fin n) :
    i ∈ magnitudeBlock x b (((magnitudePermutation x).symm i).val / b) := by
  rw [mem_magnitudeBlock]
  have hle := Nat.div_mul_le_self ((magnitudePermutation x).symm i).val b
  constructor
  · simpa [Nat.mul_comm] using hle
  · simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ ((magnitudePermutation x).symm i).val hb)

/-- The block index of a member is its coordinate rank divided by the block size.

**Lean implementation helper.** -/
theorem block_eq_rank_div_of_mem {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b k : ℕ} (hb : 0 < b) {i : Fin n}
    (hi : i ∈ magnitudeBlock x b k) :
    k = ((magnitudePermutation x).symm i).val / b := by
  have hi' := (mem_magnitudeBlock x b k i).mp hi
  apply le_antisymm
  · exact (Nat.le_div_iff_mul_le hb).2 hi'.1
  · have hlt : ((magnitudePermutation x).symm i).val / b < k + 1 :=
      (Nat.div_lt_iff_lt_mul hb).2 hi'.2
    omega

/-- The quotient of a coordinate rank by the block size lies in the admissible block-index range.

**Lean implementation helper.** -/
theorem rank_div_mem_range {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b : ℕ} (_hb : 0 < b) (i : Fin n) :
    ((magnitudePermutation x).symm i).val / b ∈ Finset.range (n + 1) := by
  rw [Finset.mem_range]
  exact lt_of_le_of_lt
    (Nat.div_le_self ((magnitudePermutation x).symm i).val b)
    (Nat.lt_succ_of_lt ((magnitudePermutation x).symm i).isLt)

/-- The sorted blocks cover every coordinate exactly once.

**Lean implementation helper.** -/
theorem sum_coordinateRestriction_magnitudeBlocks {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b : ℕ} (hb : 0 < b) :
    (∑ k ∈ Finset.range (n + 1),
      coordinateRestriction x (magnitudeBlock x b k)) = x := by
  classical
  ext i
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [coordinateRestriction_apply]
  let k₀ := ((magnitudePermutation x).symm i).val / b
  have hk₀ : k₀ ∈ Finset.range (n + 1) := rank_div_mem_range x hb i
  rw [Finset.sum_eq_single k₀]
  · simp [k₀, mem_magnitudeBlock_rank_div x hb i]
  · intro k hk hne
    have hnot : i ∉ magnitudeBlock x b k := by
      intro hi
      apply hne
      exact block_eq_rank_div_of_mem x hb hi
    simp [hnot]
  · exact fun h => (h hk₀).elim

/-- The `ℓ¹` masses of all sorted blocks add up exactly to the original
`ℓ¹` mass.

**Lean implementation helper.** -/
theorem sum_ellOne_magnitudeBlocks {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b : ℕ} (hb : 0 < b) :
    (∑ k ∈ Finset.range (n + 1),
      ellOne (coordinateRestriction x (magnitudeBlock x b k))) = ellOne x := by
  classical
  simp_rw [ellOne_coordinateRestriction_eq_sum]
  calc
    (∑ k ∈ Finset.range (n + 1), ∑ i ∈ magnitudeBlock x b k, |x i|) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ i : Fin n, if i ∈ magnitudeBlock x b k then |x i| else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp
    _ = ∑ i : Fin n, ∑ k ∈ Finset.range (n + 1),
          if i ∈ magnitudeBlock x b k then |x i| else 0 := by
      rw [Finset.sum_comm]
    _ = ellOne x := by
      unfold ellOne
      apply Finset.sum_congr rfl
      intro i hi
      let k₀ := ((magnitudePermutation x).symm i).val / b
      have hk₀ : k₀ ∈ Finset.range (n + 1) := rank_div_mem_range x hb i
      rw [Finset.sum_eq_single k₀]
      · simp [k₀, mem_magnitudeBlock_rank_div x hb i]
      · intro k hk hne
        have hnot : i ∉ magnitudeBlock x b k := by
          intro hik
          apply hne
          exact block_eq_rank_div_of_mem x hb hik
        simp [hnot]
      · exact fun h => (h hk₀).elim

/-- The sum of all blocks after the largest one is controlled by the `ℓ¹`
mass. This is the substantive estimate behind the source's sorted-block
argument.

**Lean implementation helper.** -/
theorem sum_tail_norm_magnitudeBlocks_le {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {b : ℕ} (hb : 0 < b) :
    (∑ k ∈ Finset.range n,
      ‖coordinateRestriction x (magnitudeBlock x b (k + 1))‖) ≤
        ellOne x / Real.sqrt b := by
  classical
  have hsqrt0 : 0 ≤ Real.sqrt (b : ℝ) := Real.sqrt_nonneg _
  calc
    (∑ k ∈ Finset.range n,
        ‖coordinateRestriction x (magnitudeBlock x b (k + 1))‖) ≤
        ∑ k ∈ Finset.range n,
          ellOne (coordinateRestriction x (magnitudeBlock x b k)) /
            Real.sqrt b := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_magnitudeBlock_succ_le x hb
    _ = (∑ k ∈ Finset.range n,
          ellOne (coordinateRestriction x (magnitudeBlock x b k))) /
            Real.sqrt b := by rw [Finset.sum_div]
    _ ≤ (∑ k ∈ Finset.range (n + 1),
          ellOne (coordinateRestriction x (magnitudeBlock x b k))) /
            Real.sqrt b := by
      apply div_le_div_of_nonneg_right _ hsqrt0
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_succ n)
      · intro k hk hnot
        exact ellOne_nonneg _
    _ = ellOne x / Real.sqrt b := by rw [sum_ellOne_magnitudeBlocks x hb]

/-- Exercise 9.25's displayed auxiliary estimate, in a finite indexing form
which includes harmless empty terminal blocks.

**Book Exercise 9.25.** -/
theorem exercise_9_25_sum_block_norms_le {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {s : ℕ} (hs : 0 < s)
    (hxOne : ellOne x ≤ Real.sqrt s) (hxTwo : ‖x‖ ≤ 1) :
    (∑ k ∈ Finset.range (n + 1),
      ‖coordinateRestriction x (magnitudeBlock x s k)‖) ≤ 2 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqrtpos : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hsR
  rw [Finset.sum_range_succ']
  calc
    (∑ k ∈ Finset.range n,
          ‖coordinateRestriction x (magnitudeBlock x s (k + 1))‖) +
        ‖coordinateRestriction x (magnitudeBlock x s 0)‖ ≤
        ellOne x / Real.sqrt s + ‖x‖ :=
      add_le_add (sum_tail_norm_magnitudeBlocks_le x hs)
        (norm_coordinateRestriction_le x _)
    _ = ‖x‖ + ellOne x / Real.sqrt s := add_comm _ _
    _ ≤ 1 + Real.sqrt s / Real.sqrt s :=
      add_le_add hxTwo (div_le_div_of_nonneg_right hxOne hsqrtpos.le)
    _ = 2 := by rw [div_self hsqrtpos.ne']; norm_num

/-- Scalar multiplication cannot enlarge coordinate support.

**Lean implementation helper.** -/
theorem coordinateSupport_smul_subset {n : ℕ} (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateSupport (c • x) ⊆ coordinateSupport x := by
  intro i hi
  rw [mem_coordinateSupport] at hi ⊢
  intro hxi
  exact hi (by simp [hxi])

/-- Scalar multiples of an `s`-sparse vector remain `s`-sparse.

**Lean implementation helper.** -/
theorem IsSparse.smul {n s : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x) (c : ℝ) : IsSparse s (c • x) := by
  exact (Finset.card_le_card (coordinateSupport_smul_subset c x)).trans hx

/-- Unit normalization of one sorted block, with the zero block left at zero.

**Lean implementation helper.** -/
noncomputable def normalizedMagnitudeBlock {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  let v := coordinateRestriction x (magnitudeBlock x b k)
  if ‖v‖ = 0 then 0 else ‖v‖⁻¹ • v

/-- Every normalized magnitude-block component is sparse at the block size.

**Lean implementation helper.** -/
theorem normalizedMagnitudeBlock_sparse {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    IsSparse b (normalizedMagnitudeBlock x b k) := by
  change IsSparse b (if ‖coordinateRestriction x (magnitudeBlock x b k)‖ = 0 then
    0 else ‖coordinateRestriction x (magnitudeBlock x b k)‖⁻¹ •
      coordinateRestriction x (magnitudeBlock x b k))
  split_ifs with h
  · simp [IsSparse, ellZero, coordinateSupport]
  · exact (magnitudeBlock_restriction_sparse x b k).smul _

/-- Each normalized magnitude-block component has Euclidean norm at most one.

**Lean implementation helper.** -/
theorem norm_normalizedMagnitudeBlock_le_one {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    ‖normalizedMagnitudeBlock x b k‖ ≤ 1 := by
  change ‖if ‖coordinateRestriction x (magnitudeBlock x b k)‖ = 0 then
    0 else ‖coordinateRestriction x (magnitudeBlock x b k)‖⁻¹ •
      coordinateRestriction x (magnitudeBlock x b k)‖ ≤ 1
  split_ifs with h
  · simp
  · have hvpos : 0 < ‖coordinateRestriction x (magnitudeBlock x b k)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    simp [norm_smul, h]

/-- Rescaling a normalized magnitude block by the original norm reconstructs the block restriction.

**Lean implementation helper.** -/
theorem norm_smul_normalizedMagnitudeBlock {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    ‖coordinateRestriction x (magnitudeBlock x b k)‖ •
        normalizedMagnitudeBlock x b k =
      coordinateRestriction x (magnitudeBlock x b k) := by
  change ‖coordinateRestriction x (magnitudeBlock x b k)‖ •
      (if ‖coordinateRestriction x (magnitudeBlock x b k)‖ = 0 then
        0 else ‖coordinateRestriction x (magnitudeBlock x b k)‖⁻¹ •
          coordinateRestriction x (magnitudeBlock x b k)) =
    coordinateRestriction x (magnitudeBlock x b k)
  split_ifs with h
  · have hz : coordinateRestriction x (magnitudeBlock x b k) = 0 :=
      norm_eq_zero.mp h
    simp [hz]
  · rw [smul_smul]
    simp [h]

/-- A normalized magnitude-block component belongs to the sparse Euclidean unit set.

**Lean implementation helper.** -/
theorem normalizedMagnitudeBlock_mem_sparseUnitSet {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (b k : ℕ) :
    normalizedMagnitudeBlock x b k ∈ sparseUnitSet n b :=
  ⟨normalizedMagnitudeBlock_sparse x b k,
    norm_normalizedMagnitudeBlock_le_one x b k⟩

/-- Second inclusion in promoted Exercise 9.25. The proof uses the actual
sorted-block decomposition above, normalizes every nonzero block, and adds
the unused convex weight at the zero vector.

**Book Exercise 9.25.** -/
theorem exercise_9_25_truncated_subset_two_smul_convexHull (n s : ℕ) :
    truncatedL1Ball n s ⊆
      (2 : ℝ) • convexHull ℝ (sparseUnitSet n s) := by
  classical
  intro x hx
  by_cases hs0 : s = 0
  · subst s
    have hxell : ellOne x = 0 := by
      apply le_antisymm
      · simpa using hx.1
      · exact ellOne_nonneg x
    have hzero : x = 0 := (ellOne_eq_zero_iff x).mp hxell
    subst x
    apply Set.zero_mem_smul_set
    exact subset_convexHull ℝ _ (by
      simp [sparseUnitSet, IsSparse, ellZero, coordinateSupport])
  · have hs : 0 < s := Nat.pos_of_ne_zero hs0
    let v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := fun i =>
      coordinateRestriction x (magnitudeBlock x s i.val)
    let a : Fin (n + 1) → ℝ := fun i => ‖v i‖
    let L : ℝ := ∑ i, a i
    have hfinNorm : (∑ i : Fin (n + 1),
        ‖coordinateRestriction x (magnitudeBlock x s i.val)‖) =
        ∑ k ∈ Finset.range (n + 1),
          ‖coordinateRestriction x (magnitudeBlock x s k)‖ := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      simp [hk']
    have hL : L ≤ 2 := by
      change (∑ i, a i) ≤ 2
      change (∑ i : Fin (n + 1),
        ‖coordinateRestriction x (magnitudeBlock x s i.val)‖) ≤ 2
      rw [hfinNorm]
      exact exercise_9_25_sum_block_norms_le x hs hx.1 hx.2
    let w : Option (Fin (n + 1)) → ℝ
      | none => 1 - L / 2
      | some i => a i / 2
    let z : Option (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)
      | none => 0
      | some i => normalizedMagnitudeBlock x s i.val
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i
      cases i with
      | none =>
          dsimp [w]
          linarith
      | some i =>
          dsimp [w, a]
          positivity
    have hw1 : ∑ i, w i = 1 := by
      rw [Fintype.sum_option]
      change (1 - L / 2) + ∑ i, a i / 2 = 1
      rw [← Finset.sum_div]
      simp [L]
    have hz : ∀ i, z i ∈ sparseUnitSet n s := by
      intro i
      cases i with
      | none =>
          simp [z, sparseUnitSet, IsSparse, ellZero, coordinateSupport]
      | some i =>
          exact normalizedMagnitudeBlock_mem_sparseUnitSet x s i.val
    have hvsum : ∑ i, v i = x := by
      change (∑ i : Fin (n + 1),
        coordinateRestriction x (magnitudeBlock x s i.val)) = x
      rw [Finset.sum_fin_eq_sum_range]
      calc
        (∑ i ∈ Finset.range (n + 1),
            if h : i < n + 1 then
              coordinateRestriction x (magnitudeBlock x s (⟨i, h⟩ : Fin (n + 1)).val)
            else 0) =
            ∑ i ∈ Finset.range (n + 1),
              coordinateRestriction x (magnitudeBlock x s i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' := Finset.mem_range.mp hi
          simp [hi']
        _ = x := sum_coordinateRestriction_magnitudeBlocks x hs
    have hcomb : ∑ i, w i • z i = (1 / 2 : ℝ) • x := by
      rw [Fintype.sum_option]
      simp only [w, z, smul_zero, zero_add]
      calc
        (∑ i, (a i / 2) • normalizedMagnitudeBlock x s i.val) =
            ∑ i, (1 / 2 : ℝ) • v i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [show a i / 2 = (1 / 2 : ℝ) * a i by ring, mul_smul]
          exact congrArg ((1 / 2 : ℝ) • ·)
            (by simpa [a, v] using norm_smul_normalizedMagnitudeBlock x s i.val)
        _ = (1 / 2 : ℝ) • x := by rw [← Finset.smul_sum, hvsum]
    have hhalf : (1 / 2 : ℝ) • x ∈
        convexHull ℝ (sparseUnitSet n s) :=
      mem_convexHull_of_exists_fintype w z hw0 hw1 hz hcomb
    have hxscale : (2 : ℝ) • ((1 / 2 : ℝ) • x) = x := by
      rw [smul_smul]
      norm_num
    rw [← hxscale]
    exact Set.smul_mem_smul_set hhalf

/-- Every sparse Euclidean unit vector lies in the corresponding truncated `ℓ¹` ball.

**Lean implementation helper.** -/
theorem sparseUnitSet_subset_truncatedL1Ball (n s : ℕ) :
    sparseUnitSet n s ⊆ truncatedL1Ball n s := by
  intro x hx
  refine ⟨?_, hx.2⟩
  calc
    ellOne x ≤ Real.sqrt s * ‖x‖ := ellOne_le_sqrt_sparse_mul_norm hx.1
    _ ≤ Real.sqrt s * 1 :=
      mul_le_mul_of_nonneg_left hx.2 (Real.sqrt_nonneg _)
    _ = Real.sqrt s := mul_one _

/-- The intersection of the Euclidean unit ball with the scaled `ℓ¹` ball is convex.

**Lean implementation helper.** -/
theorem convex_truncatedL1Ball (n s : ℕ) :
    Convex ℝ (truncatedL1Ball n s) := by
  intro x hx y hy a b ha hb hab
  constructor
  · calc
      ellOne (a • x + b • y) ≤ ellOne (a • x) + ellOne (b • y) :=
        ellOne_add_le _ _
      _ = a * ellOne x + b * ellOne y := by
        rw [ellOne_smul, ellOne_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * Real.sqrt s + b * Real.sqrt s :=
        add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
          (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = Real.sqrt s := by rw [← add_mul, hab, one_mul]
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by linarith

/-- First inclusion in promoted Exercise 9.25.

**Book Exercise 9.25.** -/
theorem exercise_9_25_convexHull_sparse_subset_truncated (n s : ℕ) :
    convexHull ℝ (sparseUnitSet n s) ⊆ truncatedL1Ball n s := by
  exact convexHull_min (sparseUnitSet_subset_truncatedL1Ball n s)
    (convex_truncatedL1Ball n s)

/-- Sparse unit set and truncated `l1` ball approximate one another through convex hulls.

**Book Exercise 9.25.** -/
theorem exercise_9_25_convexification (n s : ℕ) :
    convexHull ℝ (sparseUnitSet n s) ⊆ truncatedL1Ball n s ∧
      truncatedL1Ball n s ⊆
        (2 : ℝ) • convexHull ℝ (sparseUnitSet n s) :=
  ⟨exercise_9_25_convexHull_sparse_subset_truncated n s,
    exercise_9_25_truncated_subset_two_smul_convexHull n s⟩

/-- Every point of a convex hull is a convex combination of a finite set of generators.

**Lean implementation helper.** -/
private theorem exists_finset_generator_of_mem_convexHull {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ T)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ T) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin n)),
      0 ∈ F ∧ (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T ∧
        x ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  rw [mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩
  let F : Finset (EuclideanSpace ℝ (Fin n)) := insert 0 (Finset.univ.image z)
  refine ⟨F, by simp [F], ?_, ?_⟩
  · intro y hy
    simp only [F, Finset.coe_insert, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_insert_iff, Set.mem_range] at hy
    rcases hy with rfl | ⟨i, rfl⟩
    · exact hzero
    · exact hz i
  · exact mem_convexHull_of_exists_fintype w z hw0 hw1 (fun i => by
      have hzi : z i ∈ Finset.univ.image z :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hziF : z i ∈ F := by
        simp [F, hzi]
      exact hziF) hsum

/-- Every point in twice a convex hull has a finite convex representation after scaling by one half.

**Lean implementation helper.** -/
private theorem exists_finset_generator_of_mem_two_convexHull {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ T)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (2 : ℝ) • convexHull ℝ T) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin n)),
      0 ∈ F ∧ (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T ∧
        x ∈ (2 : ℝ) • convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin n))) := by
  rcases Set.mem_smul_set.mp hx with ⟨z, hz, rfl⟩
  rcases exists_finset_generator_of_mem_convexHull hzero hz with ⟨F, h0F, hFT, hzF⟩
  exact ⟨F, h0F, hFT, Set.smul_mem_smul_set hzF⟩

/-- A finite set contained in twice a convex hull has Gaussian width at most twice the generator width.

**Lean implementation helper.** -/
private theorem finiteGaussianWidth_le_two_of_scaledConvexHull {n : ℕ}
    (F G : Finset (EuclideanSpace ℝ (Fin n)))
    (hF : F.Nonempty) (hG : G.Nonempty)
    (hFG : ∀ x ∈ F, x ∈ (2 : ℝ) • convexHull ℝ (G : Set _)) :
    HDP.Chapter7.gaussianWidth F ≤ 2 * HDP.Chapter7.gaussianWidth G := by
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin n),
      HDP.Chapter7.finiteGaussianSupport F g ≤
        2 * HDP.Chapter7.finiteGaussianSupport G g := by
    intro g
    rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF,
      HDP.Chapter7.finiteGaussianSupport_eq_sup' G hG]
    apply (Finset.sup'_le_iff hF (fun x => inner ℝ g x)).mpr
    intro x hx
    rcases Set.mem_smul_set.mp (hFG x hx) with ⟨z, hz, rfl⟩
    have hlinear : ConvexOn ℝ Set.univ
        (fun y : EuclideanSpace ℝ (Fin n) => inner ℝ g y) := by
      simpa [real_inner_comm] using
        (((innerSL ℝ) g).toLinearMap.convexOn
          (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))))
    have hzle := hlinear.le_sup_of_mem_convexHull (Set.subset_univ _) hz
    simpa [inner_smul_right] using (mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 2))
  rw [HDP.Chapter7.gaussianWidth, HDP.Chapter7.gaussianWidth]
  calc
    (∫ g, HDP.Chapter7.finiteGaussianSupport F g
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        ∫ g, 2 * HDP.Chapter7.finiteGaussianSupport G g
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      apply integral_mono
      · exact HDP.Chapter7.integrable_finiteGaussianSupport F
      · exact (HDP.Chapter7.integrable_finiteGaussianSupport G).const_mul 2
      · exact hpoint
    _ = 2 * (∫ g, HDP.Chapter7.finiteGaussianSupport G g
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := integral_const_mul _ _

/-- A finite set contained in four times a convex hull has Gaussian width at most four times the generator width.

**Lean implementation helper.** -/
private theorem finiteGaussianWidth_le_four_of_scaledConvexHull {n : ℕ}
    (F G : Finset (EuclideanSpace ℝ (Fin n)))
    (hF : F.Nonempty) (hG : G.Nonempty)
    (hFG : ∀ x ∈ F, x ∈ (4 : ℝ) • convexHull ℝ (G : Set _)) :
    HDP.Chapter7.gaussianWidth F ≤ 4 * HDP.Chapter7.gaussianWidth G := by
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin n),
      HDP.Chapter7.finiteGaussianSupport F g ≤
        4 * HDP.Chapter7.finiteGaussianSupport G g := by
    intro g
    rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF,
      HDP.Chapter7.finiteGaussianSupport_eq_sup' G hG]
    apply (Finset.sup'_le_iff hF (fun x => inner ℝ g x)).mpr
    intro x hx
    rcases Set.mem_smul_set.mp (hFG x hx) with ⟨z, hz, rfl⟩
    have hlinear : ConvexOn ℝ Set.univ
        (fun y : EuclideanSpace ℝ (Fin n) => inner ℝ g y) := by
      simpa [real_inner_comm] using
        (((innerSL ℝ) g).toLinearMap.convexOn
          (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))))
    have hzle := hlinear.le_sup_of_mem_convexHull (Set.subset_univ _) hz
    simpa [inner_smul_right] using
      (mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 4))
  rw [HDP.Chapter7.gaussianWidth, HDP.Chapter7.gaussianWidth]
  calc
    (∫ g, HDP.Chapter7.finiteGaussianSupport F g
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        ∫ g, 4 * HDP.Chapter7.finiteGaussianSupport G g
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      apply integral_mono
      · exact HDP.Chapter7.integrable_finiteGaussianSupport F
      · exact (HDP.Chapter7.integrable_finiteGaussianSupport G).const_mul 4
      · exact hpoint
    _ = 4 * (∫ g, HDP.Chapter7.finiteGaussianSupport G g
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := integral_const_mul _ _

/-- Monotonicity of the authoritative finite-subfamily Gaussian-width
envelope.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidthENN_mono {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))} (hST : S ⊆ T) :
    HDP.Chapter8.euclideanSetGaussianWidthENN S ≤
      HDP.Chapter8.euclideanSetGaussianWidthENN T := by
  unfold HDP.Chapter8.euclideanSetGaussianWidthENN
  apply iSup_le
  intro F
  apply iSup_le
  intro hFS
  apply iSup_le
  intro hF
  exact le_iSup_of_le F (le_iSup_of_le (hFS.trans hST)
    (le_iSup_of_le hF le_rfl))

/-- Gaussian width is unchanged by convexification and scales linearly; this
finite-subfamily formulation is the exact implication needed in Exercise
9.26.

**Book Exercise 9.26.** -/
theorem euclideanSetGaussianWidthENN_le_two_of_subset_scaledConvexHull {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ S)
    (hTS : T ⊆ (2 : ℝ) • convexHull ℝ S) :
    HDP.Chapter8.euclideanSetGaussianWidthENN T ≤
      ENNReal.ofReal 2 * HDP.Chapter8.euclideanSetGaussianWidthENN S := by
  unfold HDP.Chapter8.euclideanSetGaussianWidthENN
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  classical
  have hgen : ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ G : Finset (EuclideanSpace ℝ (Fin n)),
        0 ∈ G ∧ (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ S ∧
          (x ∈ F → x ∈ (2 : ℝ) • convexHull ℝ (G : Set _)) := by
    intro x
    by_cases hx : x ∈ F
    · rcases exists_finset_generator_of_mem_two_convexHull hzero (hTS (hFT hx)) with
        ⟨G, h0G, hGS, hxG⟩
      exact ⟨G, h0G, hGS, fun _ => hxG⟩
    · exact ⟨{0}, by simp, by simpa using hzero, fun h => (hx h).elim⟩
  choose G h0G hGS hxG using hgen
  let U : Finset (EuclideanSpace ℝ (Fin n)) := F.biUnion G
  obtain ⟨x0, hx0⟩ := hF
  have hFne : F.Nonempty := ⟨x0, hx0⟩
  have h0U : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by
    exact Finset.mem_biUnion.mpr ⟨x0, hx0, h0G x0⟩
  have hUS : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ S := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨x, hx, hyG⟩
    exact hGS x hyG
  have hFU : ∀ x ∈ F, x ∈ (2 : ℝ) • convexHull ℝ (U : Set _) := by
    intro x hx
    rcases Set.mem_smul_set.mp (hxG x hx) with ⟨z, hz, hxz⟩
    rw [← hxz]
    apply Set.smul_mem_smul_set
    exact convexHull_mono (fun y hy => Finset.mem_biUnion.mpr ⟨x, hx, hy⟩) hz
  have hwidth := finiteGaussianWidth_le_two_of_scaledConvexHull F U hFne ⟨0, h0U⟩ hFU
  calc
    ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
        ENNReal.ofReal (2 * HDP.Chapter7.gaussianWidth U) :=
      ENNReal.ofReal_le_ofReal hwidth
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (HDP.Chapter7.gaussianWidth U) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ENNReal.ofReal 2 *
        (⨆ (G : Finset (EuclideanSpace ℝ (Fin n)))
          (_ : (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ S)
          (_ : G.Nonempty), ENNReal.ofReal (HDP.Chapter7.gaussianWidth G)) := by
      gcongr
      exact le_iSup_of_le U (le_iSup_of_le hUS
        (le_iSup_of_le ⟨0, h0U⟩ le_rfl))

/-! ## The logarithmic sparse-width estimate -/

/-- Each coordinate of a standard Gaussian vector is a subgaussian random variable.

**Lean implementation helper.** -/
private theorem subGaussian_stdGaussian_coordinate {n : ℕ} (i : Fin n) :
    HDP.SubGaussian (fun g : EuclideanSpace ℝ (Fin n) => g i)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  refine ⟨2, by norm_num, ?_⟩
  rw [HDP.psi2MGF_eq_of_hasLaw_standardGaussian
    (HDP.Chapter7.hasLaw_stdGaussian_coordinate i)]
  unfold HDP.psi2MGF
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / (2 : ℝ) ^ 2))
        ∂gaussianReal 0 1) ≤
        ∫⁻ x, ENNReal.ofReal (Real.exp ((3 / 8 : ℝ) * x ^ 2))
          ∂gaussianReal 0 1 := by
      refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg x]
    _ = 2 := HDP.Chapter2.lintegral_exp_three_eighths_sq_standardGaussian

/-- The expected finite-dimensional `ℓᵖ` norm of a standard Gaussian
vector. Unlike the range-specialized Chapter 3 wrapper, this form is valid
for every real `p ≥ 1`, which is needed when `p = 2 log(en/s)`.

**Lean implementation helper.** -/
theorem integral_lpNorm_stdGaussian_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p) :
    (∫ g : EuclideanSpace ℝ (Fin n),
        HDP.Chapter1.lpNorm p (fun i => g i)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      Real.sqrt (8 / 3) * Real.sqrt p * (n : ℝ) ^ (1 / p) := by
  let ν := stdGaussian (EuclideanSpace ℝ (Fin n))
  let X : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i g => |g i|
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hXm : ∀ i, Measurable (X i) := by
    intro i
    dsimp [X]
    fun_prop
  have hX0 : ∀ i, 0 ≤ᵐ[ν] X i := fun i =>
    Filter.Eventually.of_forall fun g => abs_nonneg (g i)
  have hsub : ∀ i, HDP.SubGaussian (fun g : EuclideanSpace ℝ (Fin n) => g i) ν :=
    fun i => subGaussian_stdGaussian_coordinate i
  have hXp : ∀ i, Integrable (fun g => X i g ^ p) ν := by
    intro i
    have hiMem := (hsub i).memLp (by fun_prop : AEMeasurable
      (fun g : EuclideanSpace ℝ (Fin n) => g i) ν) hp
    have hi := hiMem.integrable_norm_rpow
      (by simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp0) (by simp)
    simpa [X, ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hi
  have hsumInt : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) => ∑ i, |g i|) ν := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact (HDP.Chapter2.integrable_of_hasLaw_standardGaussian
      (HDP.Chapter7.hasLaw_stdGaussian_coordinate i)).abs
  have hrootMeas : Measurable
      (fun g : EuclideanSpace ℝ (Fin n) =>
        HDP.Chapter1.lpNorm p (fun i => X i g)) := by
    have heq : (fun g : EuclideanSpace ℝ (Fin n) =>
        HDP.Chapter1.lpNorm p (fun i => X i g)) =
        fun g => (∑ i, |X i g| ^ p) ^ (1 / p) := by
      funext g
      exact HDP.Chapter1.lpNorm_eq_sum hp0 _
    rw [heq]
    fun_prop
  have hrootInt : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) =>
        HDP.Chapter1.lpNorm p (fun i => X i g)) ν := by
    refine hsumInt.mono' hrootMeas.aestronglyMeasurable ?_
    filter_upwards [] with g
    rw [Real.norm_eq_abs, abs_of_nonneg (HDP.Chapter1.lpNorm_nonneg hp0 _)]
    calc
      HDP.Chapter1.lpNorm p (fun i => X i g) ≤
          HDP.Chapter1.lpNorm 1 (fun i => X i g) :=
        HDP.Chapter1.lpNorm_anti le_rfl hp _
      _ = ∑ i, |g i| := by simp [HDP.Chapter1.lpNorm_one, X]
  have hbase := HDP.Chapter1.exercise_1_14_upper (μ := ν) hp hX0 hXp hrootInt
  have hmoment : ∀ i, HDP.Chapter1.lpNormRV (fun g : EuclideanSpace ℝ (Fin n) => g i)
      p ν ≤ Real.sqrt (8 / 3) * Real.sqrt p := by
    intro i
    calc
      HDP.Chapter1.lpNormRV (fun g : EuclideanSpace ℝ (Fin n) => g i) p ν ≤
          HDP.psi2Norm (fun g : EuclideanSpace ℝ (Fin n) => g i) ν *
            Real.sqrt p :=
        (hsub i).moment_bound (by fun_prop) hp
      _ = Real.sqrt (8 / 3) * Real.sqrt p := by
        rw [HDP.psi2Norm_standardGaussian
          (HDP.Chapter7.hasLaw_stdGaussian_coordinate i)]
  have hmomentPow : ∀ i,
      (∫ g : EuclideanSpace ℝ (Fin n), |g i| ^ p ∂ν) ≤
        (Real.sqrt (8 / 3) * Real.sqrt p) ^ p := by
    intro i
    have hI0 : 0 ≤ ∫ g : EuclideanSpace ℝ (Fin n), |g i| ^ p ∂ν :=
      integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
    have hlp0 : 0 ≤ HDP.Chapter1.lpNormRV
        (fun g : EuclideanSpace ℝ (Fin n) => g i) p ν := by
      rw [HDP.Chapter1.lpNormRV]
      positivity
    calc
      (∫ g : EuclideanSpace ℝ (Fin n), |g i| ^ p ∂ν) =
          (HDP.Chapter1.lpNormRV
            (fun g : EuclideanSpace ℝ (Fin n) => g i) p ν) ^ p := by
        rw [HDP.Chapter1.lpNormRV]
        simpa [one_div] using (Real.rpow_inv_rpow hI0 hp0.ne').symm
      _ ≤ (Real.sqrt (8 / 3) * Real.sqrt p) ^ p :=
        Real.rpow_le_rpow hlp0 (hmoment i) hp0.le
  have hsum : (∑ i : Fin n, ∫ g : EuclideanSpace ℝ (Fin n),
      X i g ^ p ∂ν) ≤
      (n : ℝ) * (Real.sqrt (8 / 3) * Real.sqrt p) ^ p := by
    calc
      (∑ i : Fin n, ∫ g : EuclideanSpace ℝ (Fin n), X i g ^ p ∂ν) ≤
          ∑ _i : Fin n, (Real.sqrt (8 / 3) * Real.sqrt p) ^ p := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [X] using hmomentPow i
      _ = (n : ℝ) * (Real.sqrt (8 / 3) * Real.sqrt p) ^ p := by simp
  have hKpos : 0 < Real.sqrt (8 / 3) * Real.sqrt p := by positivity
  calc
    (∫ g : EuclideanSpace ℝ (Fin n),
        HDP.Chapter1.lpNorm p (fun i => g i) ∂ν) =
        ∫ g : EuclideanSpace ℝ (Fin n),
          HDP.Chapter1.lpNorm p (fun i => X i g) ∂ν := by
      congr 1
      funext g
      rw [HDP.Chapter1.lpNorm_eq_sum hp0,
        HDP.Chapter1.lpNorm_eq_sum hp0]
      simp [X]
    _ ≤ (∑ i, ∫ g : EuclideanSpace ℝ (Fin n), X i g ^ p ∂ν) ^
          (1 / p) := hbase
    _ ≤ ((n : ℝ) * (Real.sqrt (8 / 3) * Real.sqrt p) ^ p) ^
          (1 / p) :=
      Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
          Real.rpow_nonneg (abs_nonneg _) _)
        hsum (by positivity)
    _ = Real.sqrt (8 / 3) * Real.sqrt p * (n : ℝ) ^ (1 / p) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ n)
        (Real.rpow_nonneg hKpos.le p), ← Real.rpow_mul hKpos.le]
      have hpne : p ≠ 0 := hp0.ne'
      rw [show p * (1 / p) = 1 by field_simp, Real.rpow_one]
      ring

/-- Restricting a finite vector to a subtype cannot increase its `ℓᵖ` norm.

**Lean implementation helper.** -/
private theorem lpNorm_subtype_le_lpNorm {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n))
    {p : ℝ} (hp : 0 < p) :
    HDP.Chapter1.lpNorm p (fun i : ↥S => g i) ≤
      HDP.Chapter1.lpNorm p (fun i : Fin n => g i) := by
  rw [HDP.Chapter1.lpNorm_eq_sum hp, HDP.Chapter1.lpNorm_eq_sum hp]
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  · calc
      (∑ i : ↥S, |g i| ^ p) = ∑ i ∈ S, |g i| ^ p :=
        (Finset.sum_subtype S (by simp) (fun i => |g i| ^ p)).symm
      _ ≤ ∑ i, |g i| ^ p :=
        Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
          (fun i hi hnot => Real.rpow_nonneg (abs_nonneg (g i)) p)
  · positivity

/-- Pointwise sparse support estimate obtained from Hölder on the actual
coordinate support, followed by finite-dimensional norm comparison.

**Lean implementation helper.** -/
theorem inner_le_sparse_lpNorm {n s : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ sparseUnitSet n s)
    (g : EuclideanSpace ℝ (Fin n)) {p : ℝ} (hp : 2 ≤ p) :
    inner ℝ g x ≤
      (s : ℝ) ^ (1 / 2 - 1 / p) *
        HDP.Chapter1.lpNorm p (fun i => g i) := by
  by_cases hzero : x = 0
  · subst x
    simp only [inner_zero_right, one_div]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (HDP.Chapter1.lpNorm_nonneg (lt_of_lt_of_le (by norm_num) hp) _)
  let S := coordinateSupport x
  have hSpos : 0 < S.card := by
    by_contra hcard
    have hSempty : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcard)
    apply hzero
    ext i
    by_contra hxi
    have : i ∈ S := (mem_coordinateSupport x i).2 hxi
    simp [hSempty] at this
  have hScard : S.card ≤ s := hx.1
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hexp0 : 0 ≤ (1 / 2 : ℝ) - 1 / p := by
    exact sub_nonneg.mpr
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp)
  have hdot : inner ℝ g x =
      HDP.Chapter1.dotProduct (fun i : ↥S => g i) (fun i : ↥S => x i) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    dsimp [HDP.Chapter1.dotProduct]
    symm
    calc
      (∑ i : ↥S, g i * x i) = ∑ i ∈ S, g i * x i :=
        (Finset.sum_subtype S (by simp) (fun i => g i * x i)).symm
      _ = ∑ i, g i * x i := by
        apply Finset.sum_subset S.subset_univ
        intro i hi hiS
        have hxi : x i = 0 :=
          not_ne_iff.mp ((mem_coordinateSupport x i).not.mp hiS)
        simp [hxi]
  have hxSNorm : HDP.Chapter1.lpNorm 2 (fun i : ↥S => x i) ≤ 1 := by
    rw [HDP.Chapter1.lpNorm_two]
    calc
      Real.sqrt (∑ i : ↥S, x i ^ 2) ≤
          Real.sqrt (∑ i : Fin n, x i ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc
          (∑ i : ↥S, x i ^ 2) = ∑ i ∈ S, x i ^ 2 :=
            (Finset.sum_subtype S (by simp) (fun i => x i ^ 2)).symm
          _ ≤ ∑ i, x i ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
              (fun i hi hnot => sq_nonneg (x i))
      _ = ‖x‖ := by
        simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_eq x).symm
      _ ≤ 1 := hx.2
  have hholder := HDP.Chapter1.cauchy_schwarz_vector
    (fun i : ↥S => g i) (fun i : ↥S => x i)
  have hinnerLp : inner ℝ g x ≤ HDP.Chapter1.lpNorm 2 (fun i : ↥S => g i) := by
    rw [hdot]
    calc
      HDP.Chapter1.dotProduct (fun i : ↥S => g i) (fun i : ↥S => x i) ≤
          |HDP.Chapter1.dotProduct (fun i : ↥S => g i) (fun i : ↥S => x i)| :=
        le_abs_self _
      _ ≤ HDP.Chapter1.lpNorm 2 (fun i : ↥S => g i) *
          HDP.Chapter1.lpNorm 2 (fun i : ↥S => x i) := hholder
      _ ≤ HDP.Chapter1.lpNorm 2 (fun i : ↥S => g i) * 1 :=
        mul_le_mul_of_nonneg_left hxSNorm
          (HDP.Chapter1.lpNorm_nonneg (by norm_num) _)
      _ = _ := mul_one _
  have hcompare := (HDP.Chapter1.exercise_1_17_finite
    (p := (2 : ℝ)) (q := p) (by norm_num) hp
    (fun i : ↥S => g i)).2
  have hcompare' : HDP.Chapter1.lpNorm 2 (fun i : ↥S => g i) ≤
      (S.card : ℝ) ^ (1 / 2 - 1 / p) *
        HDP.Chapter1.lpNorm p (fun i : ↥S => g i) := by
    simpa [Fintype.card_coe] using hcompare
  have hcardpow : (S.card : ℝ) ^ (1 / 2 - 1 / p) ≤
      (s : ℝ) ^ (1 / 2 - 1 / p) := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hScard) hexp0
  calc
    inner ℝ g x ≤ HDP.Chapter1.lpNorm 2 (fun i : ↥S => g i) := hinnerLp
    _ ≤ (S.card : ℝ) ^ (1 / 2 - 1 / p) *
        HDP.Chapter1.lpNorm p (fun i : ↥S => g i) := hcompare'
    _ ≤ (s : ℝ) ^ (1 / 2 - 1 / p) *
        HDP.Chapter1.lpNorm p (fun i : ↥S => g i) :=
      mul_le_mul_of_nonneg_right hcardpow
        (HDP.Chapter1.lpNorm_nonneg hp0 _)
    _ ≤ (s : ℝ) ^ (1 / 2 - 1 / p) *
        HDP.Chapter1.lpNorm p (fun i : Fin n => g i) :=
      mul_le_mul_of_nonneg_left (lpNorm_subtype_le_lpNorm g S hp0)
        (Real.rpow_nonneg (by positivity) _)

/-- The finite-dimensional `ℓᵖ` norm of a standard Gaussian vector is integrable.

**Lean implementation helper.** -/
theorem integrable_lpNorm_stdGaussian {n : ℕ} {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
      HDP.Chapter1.lpNorm p (fun i => g i))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hsumInt : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) => ∑ i, |g i|)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact (HDP.Chapter2.integrable_of_hasLaw_standardGaussian
      (HDP.Chapter7.hasLaw_stdGaussian_coordinate i)).abs
  have hmeas : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      HDP.Chapter1.lpNorm p (fun i => g i)) := by
    have heq : (fun g : EuclideanSpace ℝ (Fin n) =>
        HDP.Chapter1.lpNorm p (fun i => g i)) =
        fun g => (∑ i, |g i| ^ p) ^ (1 / p) := by
      funext g
      exact HDP.Chapter1.lpNorm_eq_sum hp0 _
    rw [heq]
    fun_prop
  refine hsumInt.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [] with g
  rw [Real.norm_eq_abs, abs_of_nonneg (HDP.Chapter1.lpNorm_nonneg hp0 _)]
  calc
    HDP.Chapter1.lpNorm p (fun i => g i) ≤
        HDP.Chapter1.lpNorm 1 (fun i => g i) :=
      HDP.Chapter1.lpNorm_anti le_rfl hp _
    _ = ∑ i, |g i| := HDP.Chapter1.lpNorm_one _

/-- Finite-subfamily sparse Gaussian-width estimate, with an explicit
absolute constant.

**Lean implementation helper.** -/
theorem gaussianWidth_sparseUnit_finset_le {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (hFS : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ sparseUnitSet n s) :
    HDP.Chapter7.gaussianWidth F ≤
      4 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by
  let L : ℝ := Real.log (Real.exp 1 * (n : ℝ) / s)
  let p : ℝ := 2 * L
  let r : ℝ := (n : ℝ) / s
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : 0 < n := lt_of_lt_of_le hs hsn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ hsR).2
    rw [one_mul]
    exact_mod_cast hsn
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hL : L = 1 + Real.log r := by
    change Real.log (Real.exp 1 * (n : ℝ) / (s : ℝ)) =
      1 + Real.log ((n : ℝ) / (s : ℝ))
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) hnR.ne') hsR.ne',
      Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp,
      Real.log_div hnR.ne' hsR.ne']
    ring
  have hLpos : 0 < L := by rw [hL]; linarith
  have hp2 : 2 ≤ p := by dsimp [p]; linarith
  have hp0 : 0 < p := (by norm_num : (0 : ℝ) < 2).trans_le hp2
  have hlogratio : Real.log r * (1 / p) ≤ 1 / 2 := by
    change Real.log r * (1 / (2 * L)) ≤ 1 / 2
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).2
    rw [hL]
    nlinarith
  have hrfactor : r ^ (1 / p) ≤ Real.exp (1 / 2) := by
    rw [Real.rpow_def_of_pos hrpos]
    exact Real.exp_le_exp.mpr hlogratio
  have hrfactorSq : (r ^ (1 / p)) ^ 2 ≤ 3 := by
    calc
      (r ^ (1 / p)) ^ 2 ≤ (Real.exp (1 / 2)) ^ 2 := by
        nlinarith [Real.rpow_pos_of_pos hrpos (1 / p), Real.exp_pos (1 / 2)]
      _ = Real.exp 1 := by rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hscaleIdentity :
      (s : ℝ) ^ (1 / 2 - 1 / p) * (n : ℝ) ^ (1 / p) =
        Real.sqrt s * r ^ (1 / p) := by
    rw [Real.rpow_sub hsR (1 / 2) (1 / p),
      ← Real.sqrt_eq_rpow, Real.div_rpow hnR.le hsR.le]
    have hsPowPos : 0 < (s : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos hsR _
    field_simp [hsPowPos.ne']
  have hcoefSq :
      (Real.sqrt (8 / 3) * Real.sqrt p * r ^ (1 / p)) ^ 2 ≤ 16 * L := by
    have h8 : (0 : ℝ) ≤ 8 / 3 := by norm_num
    have hpnonneg : 0 ≤ p := hp0.le
    rw [mul_pow, mul_pow, Real.sq_sqrt h8, Real.sq_sqrt hpnonneg]
    nlinarith [hrfactorSq, Real.rpow_nonneg hrpos.le (1 / p)]
  have hcoef : Real.sqrt (8 / 3) * Real.sqrt p * r ^ (1 / p) ≤
      4 * Real.sqrt L := by
    have hleft : 0 ≤ Real.sqrt (8 / 3) * Real.sqrt p * r ^ (1 / p) := by positivity
    have hright : 0 ≤ 4 * Real.sqrt L := by positivity
    apply (sq_le_sq₀ hleft hright).1
    calc
      (Real.sqrt (8 / 3) * Real.sqrt p * r ^ (1 / p)) ^ 2 ≤ 16 * L := hcoefSq
      _ = (4 * Real.sqrt L) ^ 2 := by rw [mul_pow, Real.sq_sqrt hLpos.le]; norm_num
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin n),
      HDP.Chapter7.finiteGaussianSupport F g ≤
        (s : ℝ) ^ (1 / 2 - 1 / p) *
          HDP.Chapter1.lpNorm p (fun i => g i) := by
    intro g
    rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF]
    apply Finset.sup'_le
    intro x hxF
    exact inner_le_sparse_lpNorm (hFS hxF) g hp2
  have hwidthLp : HDP.Chapter7.gaussianWidth F ≤
      (s : ℝ) ^ (1 / 2 - 1 / p) *
        (Real.sqrt (8 / 3) * Real.sqrt p * (n : ℝ) ^ (1 / p)) := by
    rw [HDP.Chapter7.gaussianWidth]
    calc
      (∫ g, HDP.Chapter7.finiteGaussianSupport F g
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
          ∫ g, (s : ℝ) ^ (1 / 2 - 1 / p) *
            HDP.Chapter1.lpNorm p (fun i => g i)
            ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        apply integral_mono
        · exact HDP.Chapter7.integrable_finiteGaussianSupport F
        · exact (integrable_lpNorm_stdGaussian ((by norm_num : (1 : ℝ) ≤ 2).trans hp2)).const_mul _
        · exact hpoint
      _ = (s : ℝ) ^ (1 / 2 - 1 / p) *
          ∫ g, HDP.Chapter1.lpNorm p (fun i => g i)
            ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := integral_const_mul _ _
      _ ≤ (s : ℝ) ^ (1 / 2 - 1 / p) *
          (Real.sqrt (8 / 3) * Real.sqrt p * (n : ℝ) ^ (1 / p)) := by
        exact mul_le_mul_of_nonneg_left
          (integral_lpNorm_stdGaussian_le ((by norm_num : (1 : ℝ) ≤ 2).trans hp2))
          (Real.rpow_nonneg hsR.le _)
  calc
    HDP.Chapter7.gaussianWidth F ≤
        (s : ℝ) ^ (1 / 2 - 1 / p) *
          (Real.sqrt (8 / 3) * Real.sqrt p * (n : ℝ) ^ (1 / p)) := hwidthLp
    _ = Real.sqrt s *
        (Real.sqrt (8 / 3) * Real.sqrt p * r ^ (1 / p)) := by
      calc
        (s : ℝ) ^ (1 / 2 - 1 / p) *
            (Real.sqrt (8 / 3) * Real.sqrt p * (n : ℝ) ^ (1 / p)) =
            (Real.sqrt (8 / 3) * Real.sqrt p) *
              ((s : ℝ) ^ (1 / 2 - 1 / p) * (n : ℝ) ^ (1 / p)) := by ring
        _ = (Real.sqrt (8 / 3) * Real.sqrt p) *
              (Real.sqrt s * r ^ (1 / p)) := by rw [hscaleIdentity]
        _ = _ := by ring
    _ ≤ Real.sqrt s * (4 * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hcoef (Real.sqrt_nonneg _)
    _ = 4 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by
      rw [show Real.log (Real.exp 1 * (n : ℝ) / s) = L by rfl,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ s)]
      ring

/-- Width of a finite family of unit vectors satisfying the approximate
sparsity estimate `‖h‖₁ ≤ 2 sqrt s`. This is the finite source-neutral bridge
from Lemma 9.5.3 to the escape theorem.

**Book Lemma 9.5.3.** -/
theorem gaussianWidth_approximatelySparseUnit_finset_le {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (happrox : ∀ h ∈ F, ‖h‖ = 1 ∧ ellOne h ≤ 2 * Real.sqrt s) :
    HDP.Chapter7.gaussianWidth F ≤
      16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by
  classical
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ sparseUnitSet n s := by
    simp [sparseUnitSet, IsSparse, ellZero, coordinateSupport]
  have hgen : ∀ h : EuclideanSpace ℝ (Fin n),
      ∃ G : Finset (EuclideanSpace ℝ (Fin n)),
        0 ∈ G ∧ (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ sparseUnitSet n s ∧
          (h ∈ F → h ∈ (4 : ℝ) • convexHull ℝ (G : Set _)) := by
    intro h
    by_cases hh : h ∈ F
    · have hhalf : (2 : ℝ)⁻¹ • h ∈ truncatedL1Ball n s := by
        constructor
        · rw [ellOne_smul, abs_inv,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          have hbound := happrox h hh |>.2
          nlinarith [Real.sqrt_nonneg (s : ℝ)]
        · rw [norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), happrox h hh |>.1]
          norm_num
      have hscaled := exercise_9_25_truncated_subset_two_smul_convexHull n s hhalf
      rcases Set.mem_smul_set.mp hscaled with ⟨z, hz, hzEq⟩
      rcases exists_finset_generator_of_mem_convexHull hzero hz with
        ⟨G, h0G, hGS, hzG⟩
      refine ⟨G, h0G, hGS, fun _ => Set.mem_smul_set.mpr ⟨z, hzG, ?_⟩⟩
      have htwo : (2 : ℝ) • z = (2 : ℝ)⁻¹ • h := hzEq
      calc
        (4 : ℝ) • z = (2 : ℝ) • ((2 : ℝ) • z) := by
          rw [← mul_smul]
          norm_num
        _ = (2 : ℝ) • ((2 : ℝ)⁻¹ • h) := by rw [htwo]
        _ = h := by rw [← mul_smul]; norm_num
    · exact ⟨{0}, by simp, by simpa using hzero,
        fun hhF => (hh hhF).elim⟩
  choose G h0G hGS hxG using hgen
  let U : Finset (EuclideanSpace ℝ (Fin n)) := F.biUnion G
  obtain ⟨h0, hh0⟩ := hF
  have hFne : F.Nonempty := ⟨h0, hh0⟩
  have h0U : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by
    exact Finset.mem_biUnion.mpr ⟨h0, hh0, h0G h0⟩
  have hUS : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ sparseUnitSet n s := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨h, hh, hyG⟩
    exact hGS h hyG
  have hFU : ∀ h ∈ F, h ∈ (4 : ℝ) • convexHull ℝ (U : Set _) := by
    intro h hh
    rcases Set.mem_smul_set.mp (hxG h hh) with ⟨z, hz, hzh⟩
    rw [← hzh]
    apply Set.smul_mem_smul_set
    exact convexHull_mono
      (fun y hy => Finset.mem_biUnion.mpr ⟨h, hh, hy⟩) hz
  have hconv := finiteGaussianWidth_le_four_of_scaledConvexHull
    F U hFne ⟨0, h0U⟩ hFU
  have hsparse := gaussianWidth_sparseUnit_finset_le
    hs hsn U ⟨0, h0U⟩ hUS
  calc
    HDP.Chapter7.gaussianWidth F ≤
        4 * HDP.Chapter7.gaussianWidth U := hconv
    _ ≤ 4 * (4 * Real.sqrt
        (s * Real.log (Real.exp 1 * n / s))) :=
      mul_le_mul_of_nonneg_left hsparse (by norm_num)
    _ = 16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by ring

/-- Bound the truncated sparse width and derive the `s log(en/s)` recovery improvement.

**Book Exercise 9.26.** -/
theorem exercise_9_26_sparse_width (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) :
    HDP.Chapter8.euclideanSetGaussianWidthENN (sparseUnitSet n s) ≤
      ENNReal.ofReal
        (4 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) := by
  unfold HDP.Chapter8.euclideanSetGaussianWidthENN
  apply iSup_le
  intro F
  apply iSup_le
  intro hFS
  apply iSup_le
  intro hF
  exact ENNReal.ofReal_le_ofReal
    (gaussianWidth_sparseUnit_finset_le hs hsn F hF hFS)

/-- This proves the exact
`w(T_{n,s}) ≤ 2 w(S_{n,s})` statement in the authoritative extended-valued
arbitrary-set interface.

**Book Exercise 9.26.** -/
theorem exercise_9_26_width_convexification (n s : ℕ) :
    HDP.Chapter8.euclideanSetGaussianWidthENN (truncatedL1Ball n s) ≤
      ENNReal.ofReal 2 *
        HDP.Chapter8.euclideanSetGaussianWidthENN (sparseUnitSet n s) := by
  apply euclideanSetGaussianWidthENN_le_two_of_subset_scaledConvexHull
  · simp [sparseUnitSet, IsSparse, ellZero, coordinateSupport]
  · exact exercise_9_25_truncated_subset_two_smul_convexHull n s

/-- Truncating the `l1` ball improves `log n` to `log(en/s)`. The first conjunct is
the exact convexification comparison; the second is the logarithmically
improved sparse width estimate.

**Book Remark 9.4.10.** -/
theorem exercise_9_26 (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) :
    HDP.Chapter8.euclideanSetGaussianWidthENN (truncatedL1Ball n s) ≤
        ENNReal.ofReal 2 *
          HDP.Chapter8.euclideanSetGaussianWidthENN (sparseUnitSet n s) ∧
      HDP.Chapter8.euclideanSetGaussianWidthENN (sparseUnitSet n s) ≤
        ENNReal.ofReal
          (4 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) :=
  ⟨exercise_9_26_width_convexification n s,
    exercise_9_26_sparse_width n s hs hsn⟩

/-- Finite-prior form of the complete width estimate in Exercise 9.26. The
finite sparse generator is extracted from the actual convex-hull proof, so
the real-valued finite width used by Theorem 9.4.4 is not obtained by a
potentially lossy `ENNReal.toReal` conversion.

**Book Exercise 9.26.** -/
theorem gaussianWidth_truncatedL1Ball_finset_le {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTS : (T : Set (EuclideanSpace ℝ (Fin n))) ⊆ truncatedL1Ball n s) :
    HDP.Chapter7.gaussianWidth T ≤
      8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by
  classical
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ sparseUnitSet n s := by
    simp [sparseUnitSet, IsSparse, ellZero, coordinateSupport]
  have hgen : ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ G : Finset (EuclideanSpace ℝ (Fin n)),
        0 ∈ G ∧ (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ sparseUnitSet n s ∧
          (x ∈ T → x ∈ (2 : ℝ) • convexHull ℝ (G : Set _)) := by
    intro x
    by_cases hx : x ∈ T
    · have hxscaled := exercise_9_25_truncated_subset_two_smul_convexHull n s
          (hTS hx)
      rcases exists_finset_generator_of_mem_two_convexHull hzero hxscaled with
        ⟨G, h0G, hGS, hxG⟩
      exact ⟨G, h0G, hGS, fun _ => hxG⟩
    · exact ⟨{0}, by simp, by simpa using hzero,
        fun hxT => (hx hxT).elim⟩
  choose G h0G hGS hxG using hgen
  let U : Finset (EuclideanSpace ℝ (Fin n)) := T.biUnion G
  obtain ⟨x0, hx0⟩ := hT
  have hTne : T.Nonempty := ⟨x0, hx0⟩
  have h0U : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by
    exact Finset.mem_biUnion.mpr ⟨x0, hx0, h0G x0⟩
  have hUS : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ sparseUnitSet n s := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨x, hx, hyG⟩
    exact hGS x hyG
  have hTU : ∀ x ∈ T,
      x ∈ (2 : ℝ) • convexHull ℝ (U : Set _) := by
    intro x hx
    rcases Set.mem_smul_set.mp (hxG x hx) with ⟨z, hz, hzx⟩
    rw [← hzx]
    apply Set.smul_mem_smul_set
    exact convexHull_mono
      (fun y hy => Finset.mem_biUnion.mpr ⟨x, hx, hy⟩) hz
  have hconv := finiteGaussianWidth_le_two_of_scaledConvexHull
    T U hTne ⟨0, h0U⟩ hTU
  have hsparse := gaussianWidth_sparseUnit_finset_le
    hs hsn U ⟨0, h0U⟩ hUS
  calc
    HDP.Chapter7.gaussianWidth T ≤
        2 * HDP.Chapter7.gaussianWidth U := hconv
    _ ≤ 2 * (4 * Real.sqrt
        (s * Real.log (Real.exp 1 * n / s))) :=
      mul_le_mul_of_nonneg_left hsparse (by norm_num)
    _ = 8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by ring

/-- The finite truncated
prior has width of order `sqrt (s log (e*n/s))`; this is the exact
source-numbered bridge used by the promoted recovery estimate below.

**Book Remark 9.4.10.** -/
theorem remark_9_4_10_logImprovement_finitePrior {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTS : (T : Set (EuclideanSpace ℝ (Fin n))) ⊆ truncatedL1Ball n s) :
    HDP.Chapter7.gaussianWidth T ≤
      8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) :=
  gaussianWidth_truncatedL1Ball_finset_le hs hsn T hT hTS

/-- This is the logarithmically improved form of Corollary 9.4.8. The finite
prior lies in `B₂ ∩ sqrt(s) B₁`, and its width is reconstructed from the
sparse convex-hull decomposition rather than supplied as a hypothesis.

**Book Exercise 9.26(ii).** -/
theorem exercise_9_26_improvedSparseRecovery_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↥T]
    (hT : T.Nonempty)
    (hprior : (T : Set (EuclideanSpace ℝ (Fin n))) ⊆ truncatedL1Ball n s)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ T)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x (T : Set _)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        (8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) /
          Real.sqrt m := by
  have hmain := theorem_9_4_4_constrainedRecovery_finitePrior hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hT x hx xhat hxhatm hsol
  have hwidth := gaussianWidth_truncatedL1Ball_finset_le
    hs hsn T hT hprior
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)))
    (Real.sqrt_nonneg _))

/-! ### Exercise 9.26 on the actual truncated `ℓ¹` body -/

/-- The truncated `ℓ¹` ball contains the origin.

**Lean implementation helper.** -/
theorem truncatedL1Ball_nonempty (n s : ℕ) :
    (truncatedL1Ball n s).Nonempty := by
  exact ⟨0, by simp [truncatedL1Ball, ellOne]⟩

/-- The truncated `ℓ¹` ball is bounded by its Euclidean-ball constraint.

**Lean implementation helper.** -/
theorem truncatedL1Ball_isBounded (n s : ℕ) :
    Bornology.IsBounded (truncatedL1Ball n s) := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨1, fun _ hx => hx.2⟩

/-- The complete arbitrary-set width estimate of Exercise 9.26, converted to
the safe real wrapper only after boundedness has certified finiteness.

**Book Exercise 9.26.** -/
theorem euclideanSetGaussianWidth_truncatedL1Ball_le {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n) :
    HDP.Chapter8.euclideanSetGaussianWidth (truncatedL1Ball n s) ≤
      8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by
  let q : ℝ := s * Real.log (Real.exp 1 * n / s)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hs.trans_le hsn
  have hratio : (1 : ℝ) ≤ Real.exp 1 * n / s := by
    apply (le_div_iff₀ hsR).2
    have hexp : (1 : ℝ) ≤ Real.exp 1 := by
      exact Real.one_le_exp (by norm_num)
    have hsnR : (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
    calc
      1 * (s : ℝ) ≤ 1 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsnR (by norm_num)
      _ ≤ Real.exp 1 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hexp hnR.le
  have hq0 : 0 ≤ q :=
    mul_nonneg (by positivity) (Real.log_nonneg hratio)
  have hENN :
      HDP.Chapter8.euclideanSetGaussianWidthENN (truncatedL1Ball n s) ≤
        ENNReal.ofReal (8 * Real.sqrt q) := by
    calc
      HDP.Chapter8.euclideanSetGaussianWidthENN (truncatedL1Ball n s) ≤
          ENNReal.ofReal 2 *
            HDP.Chapter8.euclideanSetGaussianWidthENN (sparseUnitSet n s) :=
        exercise_9_26_width_convexification n s
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (4 * Real.sqrt q) := by
        gcongr
        simpa [q] using exercise_9_26_sparse_width n s hs hsn
      _ = ENNReal.ofReal (8 * Real.sqrt q) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  have hC0 : 0 ≤ 8 * Real.sqrt q :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rw [ENNReal.toReal_ofReal hC0] at hreal
  simpa [HDP.Chapter8.euclideanSetGaussianWidth, q] using hreal

/-- Truncating the `l1` ball improves `log n` to `log(en/s)`.

**Book Remark 9.4.10.** -/
theorem remark_9_4_10_logImprovement {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n) :
    HDP.Chapter8.euclideanSetGaussianWidth (truncatedL1Ball n s) ≤
      8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) :=
  euclideanSetGaussianWidth_truncatedL1Ball_le hs hsn

/-- Truncating the `l1` ball improves `log n` to `log(en/s)`. The feasible selector ranges over the genuine uncountable body
`B₂ ∩ sqrt(s) B₁`; no finite-range proxy remains.

**Book Remark 9.4.10.** -/
theorem exercise_9_26_improvedSparseRecovery
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ) (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n))
    (hxSparse : IsSparse s x) (hxNorm : ‖x‖ ≤ 1)
    (xhat : Ω → EuclideanSpace ℝ (Fin n)) (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x
      (truncatedL1Ball n s)) :
    (∫ ω, ‖xhat ω - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        (8 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) /
          Real.sqrt m := by
  have hxOne : ellOne x ≤ Real.sqrt s :=
    (ellOne_le_sqrt_sparse_mul_norm hxSparse).trans
      (by simpa using mul_le_mul_of_nonneg_left hxNorm (Real.sqrt_nonneg s))
  have hxPrior : x ∈ truncatedL1Ball n s := ⟨hxOne, hxNorm⟩
  have hmain := theorem_9_4_4_constrainedRecovery hm A hrowsm hsub hiso
    hindep hfinite hK hpsi (truncatedL1Ball n s)
      (truncatedL1Ball_nonempty n s) (truncatedL1Ball_isBounded n s)
      x hxPrior xhat hxhatm hsol
  have hwidth := euclideanSetGaussianWidth_truncatedL1Ball_le hs hsn
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)))
    (Real.sqrt_nonneg _))

/-- The maximum absolute coordinate of a standard Gaussian vector is integrable.

**Lean implementation helper.** -/
private theorem integrable_maxAbs_stdGaussian (k : ℕ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin (k + 2)) =>
      Finset.univ.sup' Finset.univ_nonempty (fun i => |g i|))
      (stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))) := by
  have hsup : Integrable
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (k + 2) =>
          fun g : EuclideanSpace ℝ (Fin (k + 2)) => |g i|))
      (stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))) := by
    refine Finset.sup'_induction
      (p := fun f : EuclideanSpace ℝ (Fin (k + 2)) → ℝ =>
        Integrable f (stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))))
      Finset.univ_nonempty
      (fun i : Fin (k + 2) =>
        fun g : EuclideanSpace ℝ (Fin (k + 2)) => |g i|) ?_ ?_
    · intro f hf g hg
      exact hf.sup hg
    · intro i hi
      exact (HDP.Chapter2.integrable_of_hasLaw_standardGaussian
        (HDP.Chapter7.hasLaw_stdGaussian_coordinate i)).abs
  have heq :
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (k + 2) =>
          fun g : EuclideanSpace ℝ (Fin (k + 2)) => |g i|)) =
      (fun g : EuclideanSpace ℝ (Fin (k + 2)) =>
        Finset.univ.sup' Finset.univ_nonempty (fun i => |g i|)) := by
    funext g
    exact Finset.sup'_apply Finset.univ_nonempty _ g
  rw [← heq]
  exact hsup

/-- The elementary `sqrt s B₁` Gaussian-width estimate used in Corollary
9.4.8.

**Book Corollary 9.4.8.** -/
theorem gaussianWidth_le_sqrt_sparse_crossPolytope {k s : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin (k + 2)))) (hT : T.Nonempty)
    (hprior : ∀ x ∈ T, ellOne x ≤ Real.sqrt s) :
    HDP.Chapter7.gaussianWidth T ≤
      Real.sqrt s * HDP.Chapter7.crossPolytopeGaussianWidth (k + 2) := by
  have hpoint (g : EuclideanSpace ℝ (Fin (k + 2))) :
      HDP.Chapter7.finiteGaussianSupport T g ≤
        Real.sqrt s *
          Finset.univ.sup' Finset.univ_nonempty (fun i => |g i|) := by
    rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' T hT]
    apply Finset.sup'_le
    intro x hx
    simp only [PiLp.inner_apply, Real.inner_apply]
    calc
      ∑ i, g i * x i ≤ ∑ i, |g i * x i| :=
        Finset.sum_le_sum fun i hi => le_abs_self _
      _ = ∑ i, |g i| * |x i| := by simp [abs_mul]
      _ ≤ ∑ i,
          (Finset.univ.sup' Finset.univ_nonempty (fun j => |g j|)) * |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (Finset.le_sup' (fun j => |g j|) (Finset.mem_univ i)) (abs_nonneg _)
      _ = (Finset.univ.sup' Finset.univ_nonempty (fun j => |g j|)) * ellOne x := by
        rw [ellOne, Finset.mul_sum]
      _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun j => |g j|)) *
          Real.sqrt s :=
        mul_le_mul_of_nonneg_left (hprior x hx) (by
          exact (abs_nonneg (g 0)).trans
            (Finset.le_sup' (fun j => |g j|) (Finset.mem_univ 0)))
      _ = _ := mul_comm _ _
  rw [HDP.Chapter7.gaussianWidth, HDP.Chapter7.crossPolytopeGaussianWidth,
    dif_pos (by omega)]
  calc
    (∫ g, HDP.Chapter7.finiteGaussianSupport T g
        ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))) ≤
        ∫ g, Real.sqrt s *
          Finset.univ.sup' Finset.univ_nonempty (fun i => |g i|)
          ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 2))) := by
      apply integral_mono
      · exact HDP.Chapter7.integrable_finiteGaussianSupport T
      · exact (integrable_maxAbs_stdGaussian k).const_mul _
      · exact hpoint
    _ = Real.sqrt s *
        ∫ g, Finset.univ.sup' Finset.univ_nonempty (fun i => |g i|)
          ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 2))) := integral_const_mul _ _

/-- The prior consists of finitely many candidates in `sqrt s B₁`; the final
displayed `sqrt(s log n / m)` rate is proved here from the cross-polytope width,
not accepted as a width premise.

**Book Corollary 9.4.8.** -/
theorem theorem_9_4_8_sparseRecovery_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m k s : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin (k + 2)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin (k + 2)))) [Nonempty ↥T]
    (hT : T.Nonempty) (hprior : ∀ z ∈ T, ellOne z ≤ Real.sqrt s)
    (x : EuclideanSpace ℝ (Fin (k + 2))) (hx : x ∈ T)
    (xhat : Ω → EuclideanSpace ℝ (Fin (k + 2)))
    (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x (T : Set _)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        (Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ)))) /
          Real.sqrt m := by
  have hmain := theorem_9_4_4_constrainedRecovery_finitePrior hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hT x hx xhat hxhatm hsol
  have hwidth : HDP.Chapter7.gaussianWidth T ≤
      Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) :=
    (gaussianWidth_le_sqrt_sparse_crossPolytope T hT hprior).trans
      (mul_le_mul_of_nonneg_left
        (HDP.Chapter7.crossPolytopeGaussianWidth_upper k)
        (Real.sqrt_nonneg _))
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)))
    (Real.sqrt_nonneg _))

/-- The source assumptions `x` is `s`-sparse and `‖x‖₂ ≤ 1` now
construct the `ℓ¹` prior membership of the true signal; only the other values
in the measurable selector's finite range need a separate prior certificate.

**Book Corollary 9.4.8.** -/
theorem theorem_9_4_8_sparseRecovery_finiteRange
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m k s : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin (k + 2)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (EuclideanSpace ℝ (Fin (k + 2)))) [Nonempty ↥T]
    (hT : T.Nonempty)
    (x : EuclideanSpace ℝ (Fin (k + 2))) (hx : x ∈ T)
    (hxSparse : IsSparse s x) (hxNorm : ‖x‖ ≤ 1)
    (hpriorOther : ∀ z ∈ T, z ≠ x → ellOne z ≤ Real.sqrt s)
    (xhat : Ω → EuclideanSpace ℝ (Fin (k + 2)))
    (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x (T : Set _)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        (Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ)))) /
          Real.sqrt m := by
  have hxOne : ellOne x ≤ Real.sqrt s := by
    calc
      ellOne x ≤ Real.sqrt s * ‖x‖ := ellOne_le_sqrt_sparse_mul_norm hxSparse
      _ ≤ Real.sqrt s * 1 :=
        mul_le_mul_of_nonneg_left hxNorm (Real.sqrt_nonneg _)
      _ = Real.sqrt s := mul_one _
  have hprior : ∀ z ∈ T, ellOne z ≤ Real.sqrt s := by
    intro z hz
    by_cases hzx : z = x
    · simpa [hzx] using hxOne
    · exact hpriorOther z hz hzx
  exact theorem_9_4_8_sparseRecovery_finitePrior hm A hrowsm hsub hiso
    hindep hfinite hK hpsi T hT hprior x hx xhat hxhatm hsol

/-! ### The actual `sqrt s B₁` prior -/

/-- Convex sparse prior `sqrt(s) B_1^n`. The convex prior in display (9.22), represented as an actual set.

**Book Equation (9.22).** -/
def sparseRecoveryPrior (n s : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ellOne z ≤ Real.sqrt s}

/-- The sparse-recovery prior contains the zero vector.

**Lean implementation helper.** -/
theorem sparseRecoveryPrior_nonempty (n s : ℕ) :
    (sparseRecoveryPrior n s).Nonempty := by
  exact ⟨0, by simp [sparseRecoveryPrior]⟩

/-- The Euclidean norm is dominated by the coordinate `ℓ¹` norm.

**Lean implementation helper.** -/
theorem norm_le_ellOne {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ellOne x := by
  have hxrepr : (∑ i, x i • EuclideanSpace.basisFun (Fin n) ℝ i) = x := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  calc
    ‖x‖ = ‖∑ i, x i • EuclideanSpace.basisFun (Fin n) ℝ i‖ := by
      rw [hxrepr]
    _ ≤
        ∑ i, ‖x i • EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
      norm_sum_le _ _
    _ = ∑ i, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      simp [norm_smul, Real.norm_eq_abs]
    _ = ellOne x := by rfl

/-- The sparse-recovery prior is bounded by its Euclidean unit-ball constraint.

**Lean implementation helper.** -/
theorem sparseRecoveryPrior_isBounded (n s : ℕ) :
    Bornology.IsBounded (sparseRecoveryPrior n s) := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨Real.sqrt s, fun x hx =>
    (norm_le_ellOne x).trans hx⟩

/-- Gaussian-width bound for the actual prior `sqrt s B₁`.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidth_sparseRecoveryPrior_le {k s : ℕ} :
    HDP.Chapter8.euclideanSetGaussianWidth (sparseRecoveryPrior (k + 2) s) ≤
      Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) := by
  let C := Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ)))
  have harg : (1 : ℝ) ≤ 2 * (k + 2 : ℝ) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity [Real.log_nonneg harg]
  have hENN :
      HDP.Chapter8.euclideanSetGaussianWidthENN
          (sparseRecoveryPrior (k + 2) s) ≤ ENNReal.ofReal C := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    exact (gaussianWidth_le_sqrt_sparse_crossPolytope F hF
      (fun x hx => hFT hx)).trans
        (mul_le_mul_of_nonneg_left
          (HDP.Chapter7.crossPolytopeGaussianWidth_upper k)
          (Real.sqrt_nonneg _))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa [HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal hC0, C] using hreal

/-- Sparse vectors can be recovered from roughly `s log n` subgaussian measurements. The feasible program is exactly (9.23): the selector may take any value in
the uncountable convex set `sqrt s B₁`. No finite-range hypothesis remains.

**Book Corollary 9.4.8.** -/
theorem theorem_9_4_8_sparseRecovery
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m k s : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin (k + 2)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin (k + 2)))
    (hxSparse : IsSparse s x) (hxNorm : ‖x‖ ≤ 1)
    (xhat : Ω → EuclideanSpace ℝ (Fin (k + 2)))
    (hxhatm : Measurable xhat)
    (hsol : IsRandomConstrainedRecoverySolution A xhat x
      (sparseRecoveryPrior (k + 2) s)) :
    (∫ omega, ‖xhat omega - x‖ ∂μ) ≤
      mStarConstant * K ^ 2 *
        (Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ)))) /
          Real.sqrt m := by
  have hxOne : ellOne x ≤ Real.sqrt s := by
    calc
      ellOne x ≤ Real.sqrt s * ‖x‖ :=
        ellOne_le_sqrt_sparse_mul_norm hxSparse
      _ ≤ Real.sqrt s * 1 :=
        mul_le_mul_of_nonneg_left hxNorm (Real.sqrt_nonneg _)
      _ = Real.sqrt s := mul_one _
  have hxPrior : x ∈ sparseRecoveryPrior (k + 2) s := hxOne
  have hmain := theorem_9_4_4_constrainedRecovery hm A hrowsm hsub hiso
    hindep hfinite hK hpsi (sparseRecoveryPrior (k + 2) s)
    (sparseRecoveryPrior_nonempty (k + 2) s)
    (sparseRecoveryPrior_isBounded (k + 2) s)
    x hxPrior xhat hxhatm hsol
  have hwidth := euclideanSetGaussianWidth_sparseRecoveryPrior_le
    (k := k) (s := s)
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)))
    (Real.sqrt_nonneg _))

/-- The measurement count scales almost linearly with sparsity. The squared geometric factor in Corollary 9.4.8 is exactly a constant times
`s log n`, which is the source's sample-size interpretation.

**Book Remark 9.4.9.** -/
theorem remark_9_4_9_sparseSampleScale (k s : ℕ) :
    (Real.sqrt s * Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ)))) ^ 2 =
      2 * s * Real.log (2 * (k + 2 : ℝ)) := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have harg : (1 : ℝ) ≤ 2 * (k + 2 : ℝ) := by
    nlinarith
  have hlog : 0 ≤ Real.log (2 * (k + 2 : ℝ)) := Real.log_nonneg harg
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ s),
    Real.sq_sqrt (mul_nonneg (by norm_num) hlog)]
  ring

/-- Corrected general-position condition for Exercise 9.22(a): injectivity on
the sparse model, not on the whole underdetermined ambient space.

**Book Exercise 9.22(a).** -/
def SparseInjective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Prop :=
  ∀ ⦃x z : EuclideanSpace ℝ (Fin n)⦄,
    IsSparse s x → IsSparse s z →
    deterministicMatrixAction A x = deterministicMatrixAction A z → x = z

/-- This declaration formalizes the statement identified as Exercise 9.22(a) in the source.

**Book Exercise 9.22(a).** -/
theorem exercise_9_22a_sparseUniqueness_of_sparseInjective {m n s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : SparseInjective A s)
    {x z : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x) (hz : IsSparse s z)
    (hmeasurement : deterministicMatrixAction A x =
      deterministicMatrixAction A z) :
    x = z :=
  hA hx hz hmeasurement

/-- The `j`th column of a real matrix, as a Euclidean vector.

**Lean implementation helper.** -/
def matrixColumnVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => A i j)

/-- A concrete full-spark convention for “general position”: every collection
of at most `m` columns is linearly independent. This condition is logically
separate from sparse injectivity, which is derived below.

**Lean implementation helper.** -/
def MatrixColumnsInGeneralPosition {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ m →
    LinearIndepOn ℝ (matrixColumnVector A) (S : Set (Fin n))

/-- Under the general-position hypothesis, a sparse vector in the matrix kernel must be zero.

**Lean implementation helper.** -/
private theorem action_eq_zero_of_generalPosition {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hgp : MatrixColumnsInGeneralPosition A)
    {h : EuclideanSpace ℝ (Fin n)}
    (hcard : (coordinateSupport h).card ≤ m)
    (haction : deterministicMatrixAction A h = 0) :
    h = 0 := by
  let S := coordinateSupport h
  have hLI : LinearIndepOn ℝ (matrixColumnVector A) (S : Set (Fin n)) :=
    hgp S hcard
  have hsum : ∑ j ∈ S, h j • matrixColumnVector A j = 0 := by
    ext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v i) haction
    simp only [deterministicMatrixAction, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, WithLp.ofLp_zero, Pi.zero_apply] at hi
    rw [WithLp.ofLp_sum]
    simp only [WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, matrixColumnVector]
    rw [Finset.sum_subset (Finset.subset_univ S)]
    · simpa [mul_comm] using hi
    · intro j _hjU hjS
      have hj0 : h j = 0 := by
        by_contra hne
        have hj : j ∈ coordinateSupport h := (mem_coordinateSupport h j).2 hne
        exact hjS hj
      simp [hj0]
  have hcoef := linearIndepOn_finset_iff.mp hLI (fun j => h j) hsum
  ext j
  by_cases hj : j ∈ S
  · exact hcoef j hj
  · have hj' : j ∉ coordinateSupport h := hj
    exact not_ne_iff.mp ((mem_coordinateSupport h j).not.mp hj')

/-- A full-spark matrix gives uniqueness among sparse candidates. If `A` is full spark and `2s ≤ m`, measurements are injective on the
`s`-sparse model. Thus the corrected sparse-candidate uniqueness conclusion
is now derived from a genuine column-general-position hypothesis rather than
being assumed through `SparseInjective`.

**Book Exercise 9.22(a).** -/
theorem exercise_9_22a_sparseUniqueness {m n s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hgp : MatrixColumnsInGeneralPosition A) (hdim : 2 * s ≤ m)
    {x z : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x) (hz : IsSparse s z)
    (hmeasurement : deterministicMatrixAction A x =
      deterministicMatrixAction A z) :
    x = z := by
  let h := x - z
  have hsupport : coordinateSupport h ⊆
      coordinateSupport x ∪ coordinateSupport z := by
    intro i hi
    apply Finset.mem_union.mpr
    by_cases hxi : x i = 0
    · right
      apply (mem_coordinateSupport z i).2
      intro hzi
      exact ((mem_coordinateSupport h i).1 hi) (by simp [h, hxi, hzi])
    · left
      exact (mem_coordinateSupport x i).2 hxi
  have hcard : (coordinateSupport h).card ≤ m := by
    calc
      (coordinateSupport h).card ≤
          (coordinateSupport x ∪ coordinateSupport z).card :=
        Finset.card_le_card hsupport
      _ ≤ (coordinateSupport x).card + (coordinateSupport z).card :=
        Finset.card_union_le _ _
      _ ≤ s + s := Nat.add_le_add hx hz
      _ = 2 * s := by omega
      _ ≤ m := hdim
  have haction : deterministicMatrixAction A h = 0 := by
    rw [show h = x - z by rfl, deterministicMatrixAction_sub, sub_eq_zero]
    exact hmeasurement
  have hh : h = 0 := action_eq_zero_of_generalPosition hgp hcard haction
  exact sub_eq_zero.mp hh

/-- The known-support algorithmic subpart of Exercise 9.22 is constructive:
this predicate records that the chosen restricted inverse is a left inverse.

**Book Exercise 9.22.** -/
def IsKnownSupportDecoder {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n))
    (decode : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x, coordinateSupport x ⊆ S →
    decode (deterministicMatrixAction A x) = x

/-- The known-support decoder exactly recovers a signal supported on the designated coordinates.

**Lean implementation helper.** -/
theorem knownSupportDecoder_recovers {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {S : Finset (Fin n)}
    {decode : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hdecode : IsKnownSupportDecoder A S decode)
    {x : EuclideanSpace ℝ (Fin n)} (hx : coordinateSupport x ⊆ S) :
    decode (deterministicMatrixAction A x) = x :=
  hdecode x hx

end

end HDP.Chapter9

end Source_11_SparseRecovery

/-! ## Material formerly in `12_LowRankRecovery.lean` -/

section Source_12_LowRankRecovery

/-!
# Book Chapter 9, §9.4.3: low-rank recovery

The matrix ambient space and Frobenius/nuclear norms are explicit.  This file
does not identify matrices with vectors by an undocumented choice of basis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Coordinate reindexing from matrix entries to the chapter's `Fin N`
random-matrix convention.

**Lean implementation helper.** -/
noncomputable def matrixEntryReindex (d : ℕ) :
    EuclideanSpace ℝ (Fin d × Fin d) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d * d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv

/-- Row-major vectorization into `Fin (d*d)`.

**Lean implementation helper.** -/
noncomputable def matrixVectorizeFin {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin (d * d)) :=
  matrixEntryReindex d (HDP.gaussianMatrixVectorize X)

/-- Inverse row-major vectorization.

**Lean implementation helper.** -/
noncomputable def matrixUnvectorizeFin {d : ℕ}
    (x : EuclideanSpace ℝ (Fin (d * d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  HDP.gaussianMatrixUnvectorize ((matrixEntryReindex d).symm x)

/-- Unvectorizing a vectorized finite matrix recovers the original matrix.

**Lean implementation helper.** -/
@[simp] theorem matrixUnvectorizeFin_vectorize {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) :
    matrixUnvectorizeFin (matrixVectorizeFin X) = X := by
  simp [matrixUnvectorizeFin, matrixVectorizeFin]

/-- Vectorizing an unvectorized finite matrix recovers the original vector.

**Lean implementation helper.** -/
@[simp] theorem matrixVectorizeFin_unvectorize {d : ℕ}
    (x : EuclideanSpace ℝ (Fin (d * d))) :
    matrixVectorizeFin (matrixUnvectorizeFin x) = x := by
  simp [matrixUnvectorizeFin, matrixVectorizeFin]

/-- Finite matrix vectorization is measurable.

**Lean implementation helper.** -/
theorem matrixVectorizeFin_measurable {d : ℕ} :
    Measurable (matrixVectorizeFin : Matrix (Fin d) (Fin d) ℝ →
      EuclideanSpace ℝ (Fin (d * d))) := by
  exact (matrixEntryReindex d).continuous.measurable.comp
    HDP.gaussianMatrixVectorize_measurable

/-- Finite matrix unvectorization is measurable.

**Lean implementation helper.** -/
theorem matrixUnvectorizeFin_measurable {d : ℕ} :
    Measurable (matrixUnvectorizeFin : EuclideanSpace ℝ (Fin (d * d)) →
      Matrix (Fin d) (Fin d) ℝ) := by
  exact HDP.gaussianMatrixUnvectorize_measurable.comp
    (matrixEntryReindex d).symm.continuous.measurable

/-- Matrix vectorization preserves the Frobenius norm.

**Lean implementation helper.** -/
theorem norm_matrixVectorizeFin {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) :
    ‖matrixVectorizeFin X‖ = HDP.matrixFrobeniusNorm X := by
  rw [matrixVectorizeFin, LinearIsometryEquiv.norm_map,
    HDP.matrixFrobeniusNorm, EuclideanSpace.norm_eq]
  congr 1
  rw [← Finset.sum_product']
  simp [HDP.gaussianMatrixVectorize, HDP.gaussianMatrixFlatten,
    Real.norm_eq_abs, sq_abs]

/-- Matrix vectorization preserves the Frobenius inner product.

**Lean implementation helper.** -/
theorem inner_matrixVectorizeFin {d : ℕ}
    (X Y : Matrix (Fin d) (Fin d) ℝ) :
    inner ℝ (matrixVectorizeFin X) (matrixVectorizeFin Y) =
      HDP.matrixFrobeniusInner X Y := by
  rw [matrixVectorizeFin, matrixVectorizeFin,
    LinearIsometryEquiv.inner_map_map, PiLp.inner_apply]
  unfold HDP.matrixFrobeniusInner
  rw [← Finset.sum_product']
  simp [HDP.gaussianMatrixVectorize, HDP.gaussianMatrixFlatten,
    mul_comm]

/-- Matrix vectorization commutes with subtraction.

**Lean implementation helper.** -/
@[simp] theorem matrixVectorizeFin_sub {d : ℕ}
    (X Y : Matrix (Fin d) (Fin d) ℝ) :
    matrixVectorizeFin (X - Y) = matrixVectorizeFin X - matrixVectorizeFin Y := by
  unfold matrixVectorizeFin HDP.gaussianMatrixVectorize
  rw [← (matrixEntryReindex d).map_sub]
  congr 1

/-- Unvectorizing a standard Gaussian vector gives the standard Gaussian matrix law.

**Lean implementation helper.** -/
theorem matrixUnvectorizeFin_hasLaw (d : ℕ) :
    HasLaw (matrixUnvectorizeFin : EuclideanSpace ℝ (Fin (d * d)) →
      Matrix (Fin d) (Fin d) ℝ)
      (HDP.stdGaussianMatrixMeasure d d)
      (stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) := by
  refine ⟨matrixUnvectorizeFin_measurable.aemeasurable, ?_⟩
  have hreindex := ProbabilityTheory.stdGaussian_map
    (E := EuclideanSpace ℝ (Fin (d * d)))
    (F := EuclideanSpace ℝ (Fin d × Fin d)) (matrixEntryReindex d).symm
  have hvec := (HDP.gaussianMatrixVectorize_hasLaw d d).map_eq
  change Measure.map
      (HDP.gaussianMatrixUnvectorize ∘ (matrixEntryReindex d).symm)
        (stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) =
    HDP.stdGaussianMatrixMeasure d d
  rw [← Measure.map_map HDP.gaussianMatrixUnvectorize_measurable
    (matrixEntryReindex d).symm.continuous.measurable, hreindex]
  rw [← hvec, Measure.map_map HDP.gaussianMatrixUnvectorize_measurable
    HDP.gaussianMatrixVectorize_measurable]
  have hcomp :
      (HDP.gaussianMatrixUnvectorize ∘ HDP.gaussianMatrixVectorize :
        Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) = id := by
    funext X
    exact HDP.gaussianMatrixUnvectorize_vectorize X
  rw [hcomp, Measure.map_id]

/-- The expected operator norm of an unvectorized Gaussian matrix satisfies the stated dimension bound.

**Lean implementation helper.** -/
theorem integral_opNorm_matrixUnvectorizeFin_le (d : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin (d * d)),
      HDP.matrixOpNorm (matrixUnvectorizeFin g)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) ≤
      2 * Real.sqrt d := by
  classical
  have hop : Measurable
      (fun X : Matrix (Fin d) (Fin d) ℝ => HDP.matrixOpNorm X) := by
    change Measurable (fun X : Matrix (Fin d) (Fin d) ℝ => ‖X‖)
    exact continuous_norm.measurable
  have hlaw := matrixUnvectorizeFin_hasLaw d
  have heq := hlaw.integral_comp
    (f := fun X : Matrix (Fin d) (Fin d) ℝ => HDP.matrixOpNorm X)
    hop.aestronglyMeasurable
  calc
    (∫ g : EuclideanSpace ℝ (Fin (d * d)),
      HDP.matrixOpNorm (matrixUnvectorizeFin g)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) =
        ∫ X, HDP.matrixOpNorm X ∂HDP.stdGaussianMatrixMeasure d d := by
      simpa [Function.comp_def] using heq
    _ ≤ Real.sqrt d + Real.sqrt d :=
      HDP.Chapter7.gaussianMatrix_expected_opNorm d d
    _ = 2 * Real.sqrt d := by ring

/-- The operator norm of an unvectorized standard Gaussian matrix is integrable.

**Lean implementation helper.** -/
theorem integrable_opNorm_matrixUnvectorizeFin (d : ℕ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin (d * d)) =>
      HDP.matrixOpNorm (matrixUnvectorizeFin g))
      (stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) := by
  classical
  have hop : Measurable
      (fun X : Matrix (Fin d) (Fin d) ℝ => HDP.matrixOpNorm X) := by
    change Measurable (fun X : Matrix (Fin d) (Fin d) ℝ => ‖X‖)
    exact continuous_norm.measurable
  have hnorm : Integrable
      (fun g : EuclideanSpace ℝ (Fin (d * d)) => ‖g‖)
      (stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) :=
    (ProbabilityTheory.isGaussian_stdGaussian
      (E := EuclideanSpace ℝ (Fin (d * d)))).integrable_id.norm
  refine hnorm.mono'
    ((hop.comp matrixUnvectorizeFin_measurable).aestronglyMeasurable) ?_
  filter_upwards [] with g
  rw [Real.norm_eq_abs, abs_of_nonneg (HDP.matrixOpNorm_nonneg _)]
  calc
    HDP.matrixOpNorm (matrixUnvectorizeFin g) ≤
        HDP.matrixFrobeniusNorm (matrixUnvectorizeFin g) :=
      HDP.Chapter4.operatorNorm_le_frobeniusNorm _
    _ = ‖matrixVectorizeFin (matrixUnvectorizeFin g)‖ :=
      (norm_matrixVectorizeFin _).symm
    _ = ‖g‖ := by rw [matrixVectorizeFin_unvectorize]

/-- Rank-`r` matrices have nuclear norm at most `sqrt r` times Frobenius norm. The standard rank/Frobenius control of the nuclear norm. This is the
singular-value Cauchy--Schwarz step used in Corollary 9.4.11.

**Book Section 9.4.3, before (9.26).** -/
theorem matrixNuclearNorm_le_sqrt_rank_mul_frobenius {d r : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) (hrank : HDP.matrixRank X ≤ r) :
    HDP.Chapter7.matrixNuclearNorm X ≤
      Real.sqrt r * HDP.matrixFrobeniusNorm X := by
  classical
  by_cases hr : r = 0
  · have hrank0 : HDP.matrixRank X = 0 := Nat.eq_zero_of_le_zero (hr ▸ hrank)
    have hX : X = 0 := by
      apply (Matrix.toLpLin 2 2).injective
      have hrange : X.toEuclideanLin.range = ⊥ :=
        Submodule.finrank_eq_zero.mp hrank0
      have hlin : X.toEuclideanLin = 0 := LinearMap.range_eq_bot.mp hrange
      simpa using hlin
    subst X
    subst r
    unfold HDP.Chapter7.matrixNuclearNorm HDP.matrixSingularValue
    rw [show (0 : Matrix (Fin d) (Fin d) ℝ).toEuclideanLin = 0 by
      ext i j
      simp]
    simp [LinearMap.singularValues_zero]
  · let S := {i : Fin d // i.val < r}
    let emb : S → Fin r := fun i => ⟨i.val, i.property⟩
    have hemb : Function.Injective emb := by
      intro i j hij
      apply Subtype.ext
      apply Fin.ext
      simpa [emb] using congrArg Fin.val hij
    have hcard : Fintype.card S ≤ r := by
      simpa [S] using Fintype.card_le_of_injective emb hemb
    have hvanish : ∀ i : {i : Fin d // ¬i.val < r},
        HDP.matrixSingularValue X i.val = 0 := by
      intro i
      exact X.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr
        (hrank.trans (Nat.le_of_not_gt i.property))
    have hsumRestrict : HDP.Chapter7.matrixNuclearNorm X =
        ∑ i : S, HDP.matrixSingularValue X i.val := by
      have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun i : Fin d => i.val < r) (fun i => HDP.matrixSingularValue X i)
      have hzero : (∑ i : {i : Fin d // ¬i.val < r},
          HDP.matrixSingularValue X i.val) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hvanish i
      rw [hzero, add_zero] at hsplit
      exact (show (∑ i : Fin d, HDP.matrixSingularValue X i) = _ from
        hsplit.symm)
    have hsqRestrict : (∑ i : S, HDP.matrixSingularValue X i.val ^ 2) =
        HDP.matrixFrobeniusNorm X ^ 2 := by
      have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun i : Fin d => i.val < r)
        (fun i => HDP.matrixSingularValue X i ^ 2)
      have hzero : (∑ i : {i : Fin d // ¬i.val < r},
          HDP.matrixSingularValue X i.val ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hvanish i, zero_pow (by norm_num : 2 ≠ 0)]
      rw [hzero, add_zero] at hsplit
      rw [HDP.Chapter4.frobeniusNorm_sq_eq_sum_singularValues]
      exact hsplit
    have hcs : (∑ i : S, HDP.matrixSingularValue X i.val) ^ 2 ≤
        (Fintype.card S : ℝ) *
          ∑ i : S, HDP.matrixSingularValue X i.val ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset S))
        (f := fun i : S => HDP.matrixSingularValue X i.val)
    have hsq : HDP.Chapter7.matrixNuclearNorm X ^ 2 ≤
        (r : ℝ) * HDP.matrixFrobeniusNorm X ^ 2 := by
      rw [hsumRestrict]
      calc
        (∑ i : S, HDP.matrixSingularValue X i.val) ^ 2 ≤
            (Fintype.card S : ℝ) *
              ∑ i : S, HDP.matrixSingularValue X i.val ^ 2 := hcs
        _ = (Fintype.card S : ℝ) * HDP.matrixFrobeniusNorm X ^ 2 := by
          rw [hsqRestrict]
        _ ≤ (r : ℝ) * HDP.matrixFrobeniusNorm X ^ 2 := by
          gcongr
    have hsqrt : (Real.sqrt (r : ℝ)) ^ 2 = r := by
      rw [Real.sq_sqrt]
      positivity
    have hrhs : 0 ≤ Real.sqrt (r : ℝ) * HDP.matrixFrobeniusNorm X :=
      mul_nonneg (Real.sqrt_nonneg _) (HDP.matrixFrobeniusNorm_nonneg X)
    nlinarith [HDP.Chapter7.matrixNuclearNorm_nonneg X]

/-- The Frobenius norm is dominated by the nuclear norm.

**Lean implementation helper.** -/
theorem matrixFrobeniusNorm_le_matrixNuclearNorm {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) :
    HDP.matrixFrobeniusNorm X ≤ HDP.Chapter7.matrixNuclearNorm X := by
  have hsq : HDP.matrixFrobeniusNorm X ^ 2 ≤
      HDP.Chapter7.matrixNuclearNorm X ^ 2 := by
    rw [HDP.Chapter4.frobeniusNorm_sq_eq_sum_singularValues]
    unfold HDP.Chapter7.matrixNuclearNorm
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ =>
      HDP.matrixSingularValue_nonneg X i
  nlinarith [HDP.matrixFrobeniusNorm_nonneg X,
    HDP.Chapter7.matrixNuclearNorm_nonneg X]

/-- Vectorizing a finite matrix prior preserves nonemptiness.

**Lean implementation helper.** -/
theorem matrixVectorizeFin_image_nonempty {d : ℕ}
    {T : Finset (Matrix (Fin d) (Fin d) ℝ)} (hT : T.Nonempty) :
    (T.image matrixVectorizeFin).Nonempty :=
  hT.image _

/-- The nuclear/operator duality estimate integrated against the standard
Gaussian matrix gives the finite-prior width bound used in Corollary 9.4.11.

**Book Corollary 9.4.11.** -/
theorem gaussianWidth_matrixVectorization_le {d : ℕ} {r : ℝ}
    (_hr : 0 ≤ r) (T : Finset (Matrix (Fin d) (Fin d) ℝ))
    (hT : T.Nonempty)
    (hprior : ∀ X ∈ T, HDP.Chapter7.matrixNuclearNorm X ≤ Real.sqrt r) :
    HDP.Chapter7.gaussianWidth (T.image matrixVectorizeFin) ≤
      Real.sqrt r * (2 * Real.sqrt d) := by
  let V : Finset (EuclideanSpace ℝ (Fin (d * d))) :=
    T.image matrixVectorizeFin
  have hV : V.Nonempty := matrixVectorizeFin_image_nonempty hT
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin (d * d)),
      HDP.Chapter7.finiteGaussianSupport V g ≤
        Real.sqrt r * HDP.matrixOpNorm (matrixUnvectorizeFin g) := by
    intro g
    rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' V hV]
    apply Finset.sup'_le
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨X, hXT, rfl⟩
    calc
      inner ℝ g (matrixVectorizeFin X) =
          HDP.matrixFrobeniusInner X (matrixUnvectorizeFin g) := by
        rw [real_inner_comm]
        simpa only [matrixVectorizeFin_unvectorize] using
          inner_matrixVectorizeFin X (matrixUnvectorizeFin g)
      _ ≤
          |HDP.matrixFrobeniusInner X (matrixUnvectorizeFin g)| :=
        le_abs_self _
      _ ≤ HDP.Chapter7.matrixNuclearNorm X *
          HDP.matrixOpNorm (matrixUnvectorizeFin g) :=
        HDP.Chapter7.abs_matrixFrobeniusInner_le_nuclear_mul_opNorm _ _
      _ ≤ Real.sqrt r * HDP.matrixOpNorm (matrixUnvectorizeFin g) :=
        mul_le_mul_of_nonneg_right (hprior X hXT)
          (HDP.matrixOpNorm_nonneg _)
  rw [show T.image matrixVectorizeFin = V by rfl,
    HDP.Chapter7.gaussianWidth]
  calc
    (∫ g, HDP.Chapter7.finiteGaussianSupport V g
        ∂stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) ≤
        ∫ g, Real.sqrt r * HDP.matrixOpNorm (matrixUnvectorizeFin g)
          ∂stdGaussian (EuclideanSpace ℝ (Fin (d * d))) := by
      apply integral_mono
      · exact HDP.Chapter7.integrable_finiteGaussianSupport V
      · exact (integrable_opNorm_matrixUnvectorizeFin d).const_mul _
      · exact hpoint
    _ = Real.sqrt r *
        (∫ g, HDP.matrixOpNorm (matrixUnvectorizeFin g)
          ∂stdGaussian (EuclideanSpace ℝ (Fin (d * d)))) :=
      integral_const_mul _ _
    _ ≤ Real.sqrt r * (2 * Real.sqrt d) :=
      mul_le_mul_of_nonneg_left (integral_opNorm_matrixUnvectorizeFin_le d)
        (Real.sqrt_nonneg _)

/-- Low-rank matrix measurements are Frobenius inner products. Display (9.25): the vector of Frobenius measurements.

**Book Equation (9.25).** -/
def matrixMeasurements {m d : ℕ}
    (A : Fin m → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin d) ℝ) : Fin m → ℝ :=
  fun i => HDP.matrixFrobeniusInner (A i) X

/-- Nuclear-norm constrained recovery program. Nuclear-norm prior used in display (9.26).

**Book Equation (9.26).** -/
def nuclearPrior (d : ℕ) (radius : ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ) :=
  {X | HDP.Chapter7.matrixNuclearNorm X ≤ radius}

/-- The actual nuclear-norm prior in the Euclidean coordinates used by the
random-matrix deviation theorem.

**Lean implementation helper.** -/
def vectorizedNuclearPrior (d : ℕ) (radius : ℝ) :
    Set (EuclideanSpace ℝ (Fin (d * d))) :=
  {x | matrixUnvectorizeFin x ∈ nuclearPrior d radius}

/-- The vectorized nuclear-norm prior contains the vectorized zero matrix.

**Lean implementation helper.** -/
theorem vectorizedNuclearPrior_nonempty {d : ℕ} {radius : ℝ}
    (hradius : 0 ≤ radius) :
    (vectorizedNuclearPrior d radius).Nonempty := by
  refine ⟨0, ?_⟩
  have hzero : matrixUnvectorizeFin
      (0 : EuclideanSpace ℝ (Fin (d * d))) = 0 := by
    calc
      matrixUnvectorizeFin (0 : EuclideanSpace ℝ (Fin (d * d))) =
          matrixUnvectorizeFin
            (matrixVectorizeFin (0 : Matrix (Fin d) (Fin d) ℝ)) := by
        congr 1
      _ = 0 := matrixUnvectorizeFin_vectorize 0
  simpa [vectorizedNuclearPrior, nuclearPrior, hzero] using hradius

/-- The vectorized nuclear-norm prior is bounded in Euclidean space.

**Lean implementation helper.** -/
theorem vectorizedNuclearPrior_isBounded (d : ℕ) (radius : ℝ) :
    Bornology.IsBounded (vectorizedNuclearPrior d radius) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max radius 0, ?_⟩
  intro x hx
  calc
    ‖x‖ = HDP.matrixFrobeniusNorm (matrixUnvectorizeFin x) := by
      rw [← norm_matrixVectorizeFin, matrixVectorizeFin_unvectorize]
    _ ≤ HDP.Chapter7.matrixNuclearNorm (matrixUnvectorizeFin x) :=
      matrixFrobeniusNorm_le_matrixNuclearNorm _
    _ ≤ radius := hx
    _ ≤ max radius 0 := le_max_left _ _

/-- Gaussian-width bound for the actual vectorized nuclear ball.

**Lean implementation helper.** -/
theorem euclideanSetGaussianWidth_vectorizedNuclearPrior_le {d r : ℕ} :
    HDP.Chapter8.euclideanSetGaussianWidth
        (vectorizedNuclearPrior d (Real.sqrt r)) ≤
      Real.sqrt r * (2 * Real.sqrt d) := by
  let C := Real.sqrt r * (2 * Real.sqrt d)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hENN :
      HDP.Chapter8.euclideanSetGaussianWidthENN
          (vectorizedNuclearPrior d (Real.sqrt r)) ≤ ENNReal.ofReal C := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    apply iSup_le
    intro F
    apply iSup_le
    intro hFprior
    apply iSup_le
    intro hF
    let T : Finset (Matrix (Fin d) (Fin d) ℝ) :=
      F.image matrixUnvectorizeFin
    have hT : T.Nonempty := hF.image _
    have hprior : ∀ X ∈ T,
        HDP.Chapter7.matrixNuclearNorm X ≤ Real.sqrt r := by
      intro X hXT
      rcases Finset.mem_image.mp hXT with ⟨x, hxF, rfl⟩
      exact hFprior hxF
    have hfinite := gaussianWidth_matrixVectorization_le
      (r := (r : ℝ)) (by positivity) T hT hprior
    have himage : T.image matrixVectorizeFin = F := by
      ext x
      simp [T]
    rw [himage] at hfinite
    exact ENNReal.ofReal_le_ofReal hfinite
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa [HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal hC0, C] using hreal

/-- Nuclear-norm constrained recovery program.

**Book Equation (9.26).** -/
def IsNuclearRecoverySolution {m d : ℕ}
    (A : Fin m → Matrix (Fin d) (Fin d) ℝ)
    (y : Fin m → ℝ) (radius : ℝ)
    (Xhat : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Xhat ∈ nuclearPrior d radius ∧ matrixMeasurements A Xhat = y

/-- Compatibility interface for a measurable matrix-valued selector over a
finite low-rank prior.

**Lean implementation helper.** -/
def IsRandomNuclearRecoverySolution_finitePrior {m d : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin (d * d)) Ω)
    (Xhat : Ω → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin d) ℝ)
    (T : Finset (Matrix (Fin d) (Fin d) ℝ)) : Prop :=
  IsRandomConstrainedRecoverySolution A
    (fun omega => matrixVectorizeFin (Xhat omega))
    (matrixVectorizeFin X) (T.image matrixVectorizeFin : Set _)

/-- A measurable matrix-valued selector feasible in the actual nuclear ball.

**Lean implementation helper.** -/
def IsRandomNuclearRecoverySolution {m d : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin (d * d)) Ω)
    (Xhat : Ω → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin d) ℝ) (radius : ℝ) : Prop :=
  IsRandomConstrainedRecoverySolution A
    (fun omega => matrixVectorizeFin (Xhat omega))
    (matrixVectorizeFin X) (vectorizedNuclearPrior d radius)

/-- The true matrix is feasible for nuclear-norm recovery from its exact measurements.

**Lean implementation helper.** -/
theorem trueMatrix_isNuclearRecoverySolution {m d : ℕ}
    (A : Fin m → Matrix (Fin d) (Fin d) ℝ)
    {X : Matrix (Fin d) (Fin d) ℝ} {radius : ℝ}
    (hX : HDP.Chapter7.matrixNuclearNorm X ≤ radius) :
    IsNuclearRecoverySolution A (matrixMeasurements A X) radius X := by
  exact ⟨hX, rfl⟩

/-- Two feasible matrices have identical measurement difference.

**Lean implementation helper.** -/
theorem nuclearRecovery_error_in_kernel {m d : ℕ}
    {A : Fin m → Matrix (Fin d) (Fin d) ℝ}
    {y : Fin m → ℝ} {radius : ℝ}
    {X Xhat : Matrix (Fin d) (Fin d) ℝ}
    (hX : IsNuclearRecoverySolution A y radius X)
    (hXhat : IsNuclearRecoverySolution A y radius Xhat) :
    matrixMeasurements A (Xhat - X) = 0 := by
  funext i
  have hi := congrFun (hXhat.2.trans hX.2.symm) i
  simpa [matrixMeasurements, HDP.matrixFrobeniusInner, Matrix.sub_apply,
    mul_sub, Finset.sum_sub_distrib] using sub_eq_zero.mpr hi

/-- The finite matrix prior is contained in the nuclear ball of radius `sqrt r`.
The proof vectorizes the program isometrically, proves its Gaussian-width
bound from nuclear/operator duality, and applies Theorem 9.4.4. In
particular, no recovery-error bound occurs among the hypotheses.

**Book Corollary 9.4.11.** -/
theorem theorem_9_4_11_lowRankRecovery_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m d r : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin (d * d)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (T : Finset (Matrix (Fin d) (Fin d) ℝ)) [Nonempty ↥T]
    (hT : T.Nonempty)
    (hpriorRank : ∀ Z ∈ T, HDP.matrixRank Z ≤ r)
    (hpriorFrobenius : ∀ Z ∈ T, HDP.matrixFrobeniusNorm Z ≤ 1)
    (X : Matrix (Fin d) (Fin d) ℝ) (hX : X ∈ T)
    (Xhat : Ω → Matrix (Fin d) (Fin d) ℝ) (hXhatm : Measurable Xhat)
    (hsol : IsRandomNuclearRecoverySolution_finitePrior A Xhat X T) :
    (∫ omega, HDP.matrixFrobeniusNorm (Xhat omega - X) ∂μ) ≤
      mStarConstant * K ^ 2 *
        (Real.sqrt r * (2 * Real.sqrt d)) / Real.sqrt m := by
  let V : Finset (EuclideanSpace ℝ (Fin (d * d))) :=
    T.image matrixVectorizeFin
  letI : Nonempty ↥V := (matrixVectorizeFin_image_nonempty hT).to_subtype
  have hmain := theorem_9_4_4_constrainedRecovery_finitePrior hm A hrowsm hsub hiso
    hindep hfinite hK hpsi V (matrixVectorizeFin_image_nonempty hT)
    (matrixVectorizeFin X) (Finset.mem_image.mpr ⟨X, hX, rfl⟩)
    (fun omega => matrixVectorizeFin (Xhat omega))
    (matrixVectorizeFin_measurable.comp hXhatm) hsol
  have hwidth : HDP.Chapter7.gaussianWidth V ≤
      Real.sqrt r * (2 * Real.sqrt d) := by
    have hprior : ∀ Z ∈ T,
        HDP.Chapter7.matrixNuclearNorm Z ≤ Real.sqrt r := by
      intro Z hZT
      calc
        HDP.Chapter7.matrixNuclearNorm Z ≤
            Real.sqrt r * HDP.matrixFrobeniusNorm Z :=
          matrixNuclearNorm_le_sqrt_rank_mul_frobenius Z (hpriorRank Z hZT)
        _ ≤ Real.sqrt r * 1 :=
          mul_le_mul_of_nonneg_left (hpriorFrobenius Z hZT)
            (Real.sqrt_nonneg _)
        _ = Real.sqrt r := mul_one _
    simpa [V] using gaussianWidth_matrixVectorization_le
      (r := (r : ℝ)) (by positivity) T hT hprior
  have hnorm (omega : Ω) :
      ‖matrixVectorizeFin (Xhat omega) - matrixVectorizeFin X‖ =
        HDP.matrixFrobeniusNorm (Xhat omega - X) := by
    rw [← matrixVectorizeFin_sub, norm_matrixVectorizeFin]
  rw [show (∫ omega, HDP.matrixFrobeniusNorm (Xhat omega - X) ∂μ) =
      ∫ omega, ‖matrixVectorizeFin (Xhat omega) - matrixVectorizeFin X‖ ∂μ by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact (hnorm omega).symm]
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)))
    (Real.sqrt_nonneg _))

/-- Low-rank matrices can be recovered from roughly `rd` Gaussian measurements via nuclear norm. The selector ranges over the full nuclear ball `sqrt r B_*`; finite priors
occur only inside the arbitrary-set Gaussian-width envelope and the proof of
Theorem 9.4.4.

**Book Corollary 9.4.11.** -/
theorem theorem_9_4_11_lowRankRecovery
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m d r : ℕ} (hm : 0 < m)
    (A : HDP.RandomMatrix (Fin m) (Fin (d * d)) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (X : Matrix (Fin d) (Fin d) ℝ)
    (hXrank : HDP.matrixRank X ≤ r)
    (hXfrob : HDP.matrixFrobeniusNorm X ≤ 1)
    (Xhat : Ω → Matrix (Fin d) (Fin d) ℝ) (hXhatm : Measurable Xhat)
    (hsol : IsRandomNuclearRecoverySolution A Xhat X (Real.sqrt r)) :
    (∫ omega, HDP.matrixFrobeniusNorm (Xhat omega - X) ∂μ) ≤
      mStarConstant * K ^ 2 *
        (Real.sqrt r * (2 * Real.sqrt d)) / Real.sqrt m := by
  have hXnuclear :
      HDP.Chapter7.matrixNuclearNorm X ≤ Real.sqrt r := by
    calc
      HDP.Chapter7.matrixNuclearNorm X ≤
          Real.sqrt r * HDP.matrixFrobeniusNorm X :=
        matrixNuclearNorm_le_sqrt_rank_mul_frobenius X hXrank
      _ ≤ Real.sqrt r * 1 :=
        mul_le_mul_of_nonneg_left hXfrob (Real.sqrt_nonneg _)
      _ = Real.sqrt r := mul_one _
  have hXprior : matrixVectorizeFin X ∈
      vectorizedNuclearPrior d (Real.sqrt r) := by
    simpa [vectorizedNuclearPrior, nuclearPrior] using hXnuclear
  have hmain := theorem_9_4_4_constrainedRecovery hm A hrowsm hsub hiso
    hindep hfinite hK hpsi (vectorizedNuclearPrior d (Real.sqrt r))
    (vectorizedNuclearPrior_nonempty (Real.sqrt_nonneg _))
    (vectorizedNuclearPrior_isBounded d (Real.sqrt r))
    (matrixVectorizeFin X) hXprior
    (fun omega => matrixVectorizeFin (Xhat omega))
    (matrixVectorizeFin_measurable.comp hXhatm) hsol
  have hwidth := euclideanSetGaussianWidth_vectorizedNuclearPrior_le
    (d := d) (r := r)
  have hnorm (omega : Ω) :
      ‖matrixVectorizeFin (Xhat omega) - matrixVectorizeFin X‖ =
        HDP.matrixFrobeniusNorm (Xhat omega - X) := by
    rw [← matrixVectorizeFin_sub, norm_matrixVectorizeFin]
  rw [show (∫ omega, HDP.matrixFrobeniusNorm (Xhat omega - X) ∂μ) =
      ∫ omega, ‖matrixVectorizeFin (Xhat omega) - matrixVectorizeFin X‖ ∂μ by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact (hnorm omega).symm]
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg mStarConstant_pos.le (sq_nonneg K)))
    (Real.sqrt_nonneg _))

/-- Low-rank recovery needs far fewer than `d^2` observations. The squared
geometric factor in Corollary 9.4.11 is `4*r*d`, making the source's linear
`r*d` sample scale explicit. This is also where the printed cross-reference
is corrected from Corollary 9.4.8 to 9.4.11.

**Book Remark 9.4.12.** -/
theorem remark_9_4_12_lowRankSampleScale (r d : ℕ) :
    (Real.sqrt r * (2 * Real.sqrt d)) ^ 2 = 4 * r * d := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
  norm_num
  ring

end

end HDP.Chapter9

end Source_12_LowRankRecovery

/-! ## Material formerly in `13_ExactSparseRecovery.lean` -/

section Source_13_ExactSparseRecovery

/-!
# Book Chapter 9, §9.5.1: exact sparse recovery

The tangent-cone argument is represented by an exact deterministic
nullspace-avoidance theorem.  Coordinate restrictions remain in the original
ambient space, correcting the source's ill-typed `x_I ∈ ℝ^T` notation.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `ℓ¹` mass on a chosen coordinate set.

**Lean implementation helper.** -/
def ellOneOn {n : ℕ} (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i ∈ S, |x i|

/-- The `ℓ¹` norm of a coordinate restriction is the sum of absolute values on the selected coordinates.

**Lean implementation helper.** -/
theorem ellOne_coordinateRestriction {n : ℕ}
    (S : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    ellOne (coordinateRestriction x S) = ellOneOn S x := by
  rw [ellOne, ellOneOn]
  change (∑ i, |if i ∈ S then x i else 0|) = ∑ i ∈ S, |x i|
  calc
    (∑ i, |if i ∈ S then x i else 0|) =
        ∑ i ∈ S, |if i ∈ S then x i else 0| := by
      symm
      apply Finset.sum_subset S.subset_univ
      intro i hi hiS
      simp [hiS]
    _ = ∑ i ∈ S, |x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]

/-- The restricted `ℓ¹` functional is nonnegative.

**Lean implementation helper.** -/
theorem ellOneOn_nonneg {n : ℕ} (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ellOneOn S x := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The full `ℓ¹` norm splits into contributions on a support and its complement.

**Lean implementation helper.** -/
theorem ellOne_eq_on_add_off {n : ℕ} (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    ellOne x = ellOneOn S x + ellOneOn (Finset.univ \ S) x := by
  rw [ellOne, ellOneOn, ellOneOn]
  calc
    (∑ i, |x i|) =
        (∑ i ∈ Finset.univ \ S, |x i|) + ∑ i ∈ S, |x i| :=
      (Finset.sum_sdiff S.subset_univ).symm
    _ = (∑ i ∈ S, |x i|) + ∑ i ∈ Finset.univ \ S, |x i| := add_comm _ _

/-- Restricted `ℓ¹` mass is bounded by the square root of support size times Euclidean norm.

**Lean implementation helper.** -/
theorem ellOneOn_le_sqrt_card_mul_norm {n : ℕ}
    (S : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    ellOneOn S x ≤ Real.sqrt S.card * ‖x‖ := by
  have hsumSq : ∑ i ∈ S, |x i| ^ 2 ≤ ∑ i, |x i| ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
      fun i hi hnot => by positivity
  have hnormSq : ∑ i, |x i| ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact sq_abs (x i)
  have hsq0 := sq_sum_le_card_mul_sum_sq
    (s := S) (f := fun i => |x i|)
  have hsq : ellOneOn S x ^ 2 ≤ (S.card : ℝ) * ‖x‖ ^ 2 := by
    calc
      ellOneOn S x ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, |x i| ^ 2 := by
        simpa [ellOneOn] using hsq0
      _ ≤ (S.card : ℝ) * ∑ i, |x i| ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq (by positivity)
      _ = (S.card : ℝ) * ‖x‖ ^ 2 := by rw [hnormSq]
  have hrhs0 : 0 ≤ Real.sqrt S.card * ‖x‖ := by positivity
  apply (sq_le_sq₀ (ellOneOn_nonneg S x) hrhs0).mp
  calc
    ellOneOn S x ^ 2 ≤ (S.card : ℝ) * ‖x‖ ^ 2 := hsq
    _ = (Real.sqrt S.card * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ S.card)]

/-- Basis pursuit minimizes `l1` subject to `Ax'=y`. The `ℓ¹` minimizer predicate in display (9.27).

**Book Equation (9.27).** -/
def IsL1RecoveryMinimizer {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m))
    (xhat : EuclideanSpace ℝ (Fin n)) : Prop :=
  deterministicMatrixAction A xhat = y ∧
    ∀ z, deterministicMatrixAction A z = y → ellOne xhat ≤ ellOne z

/-- The descent cone of the `ℓ¹` objective at `x`, in error coordinates.

**Lean implementation helper.** -/
def l1DescentCone {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {h | ellOne (x + h) ≤ ellOne x}

/-- Its spherical part, used by the escape proof.

**Lean implementation helper.** -/
def l1SphericalDescentSet {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  l1DescentCone x ∩ Metric.sphere 0 1

/-- The error of an `ℓ¹` minimizer lies in the descent cone at the true signal.

**Lean implementation helper.** -/
theorem minimizer_error_mem_descentCone {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat) :
    xhat - x ∈ l1DescentCone x := by
  change ellOne (x + (xhat - x)) ≤ ellOne x
  simpa [add_sub_cancel_left] using hmin.2 x rfl

/-- The error of an exact-measurement minimizer lies in the measurement kernel.

**Lean implementation helper.** -/
theorem minimizer_error_mem_kernel {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat) :
    deterministicMatrixAction A (xhat - x) = 0 := by
  rw [deterministicMatrixAction_sub, hmin.1, sub_self]

/-- Exact deterministic form of the tangent-cone criterion in Figure 9.7.

**Lean implementation helper.** -/
theorem exactRecovery_of_kernel_disjoint_descentCone {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat)
    (havoid : ∀ h, h ∈ l1DescentCone x →
      deterministicMatrixAction A h = 0 → h = 0) :
    xhat = x := by
  have hz : xhat - x = 0 := havoid (xhat - x)
    (minimizer_error_mem_descentCone hmin)
    (minimizer_error_mem_kernel hmin)
  exact sub_eq_zero.mp hz

/-- An `l1`-minimizer's error is no heavier off the true support than on it. The source's restriction vectors are represented by
coordinate sums in the original ambient space.

**Book Lemma 9.5.2.** -/
theorem lemma_9_5_2_error_heavier_on_support
    {n : ℕ} (x h : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n))
    (hsupport : ∀ i, i ∉ S → x i = 0)
    (hmin : ellOne (x + h) ≤ ellOne x) :
    ellOneOn (Finset.univ \ S) h ≤ ellOneOn S h := by
  have hinside : ellOneOn S x - ellOneOn S h ≤ ellOneOn S (x + h) := by
    rw [ellOneOn, ellOneOn, ellOneOn, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi => by
      have ht := abs_sub (x i + h i) (h i)
      simp only [add_sub_cancel_right] at ht
      change |x i| - |h i| ≤ |x i + h i|
      linarith
  have houtside : ellOneOn (Finset.univ \ S) (x + h) =
      ellOneOn (Finset.univ \ S) h := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [hsupport i hiS]
  have hxoff : ellOneOn (Finset.univ \ S) x = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [hsupport i hiS]
  rw [ellOne_eq_on_add_off S (x + h), houtside,
    ellOne_eq_on_add_off S x, hxoff, add_zero] at hmin
  linarith

/-- The normalized recovery error lies in an approximately sparse set.

**Book Lemma 9.5.3.** -/
theorem lemma_9_5_3_error_approximatelySparse
    {n s : ℕ} (h : EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin n)) (hScard : S.card ≤ s)
    (hoff : ellOneOn (Finset.univ \ S) h ≤ ellOneOn S h) :
    ellOne h ≤ 2 * Real.sqrt s * ‖h‖ := by
  have hcauchy0 := ellOneOn_le_sqrt_card_mul_norm S h
  have hsqrt : Real.sqrt S.card ≤ Real.sqrt s := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hScard)
  have hcauchy : ellOneOn S h ≤ Real.sqrt s * ‖h‖ :=
    hcauchy0.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg h))
  rw [ellOne_eq_on_add_off S h]
  calc
    ellOneOn S h + ellOneOn (Finset.univ \ S) h
        ≤ ellOneOn S h + ellOneOn S h := by gcongr
    _ ≤ 2 * (Real.sqrt s * ‖h‖) := by nlinarith
    _ = 2 * Real.sqrt s * ‖h‖ := by ring

/-- The finite family of normalized nonzero candidate errors which do not
increase the `ℓ¹` objective. This is the measurable finite-subfamily version
of the spherical descent cone in the proof of Theorem 9.5.1.

**Book Theorem 9.5.1.** -/
def finiteL1DescentDirections {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin n)) := by
  classical
  exact ((T.erase x).filter fun z => ellOne z ≤ ellOne x).image
    (fun z => ‖z - x‖⁻¹ • (z - x))

/-- Failure of exact basis pursuit inside a finite candidate family.

**Lean implementation helper.** -/
def finiteL1RecoveryFailure {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) (omega : Ω) : Prop :=
  ∃ z, z ∈ T ∧ z ≠ x ∧
    IsL1RecoveryMinimizer (A omega)
      (deterministicMatrixAction (A omega) x) z

/-- Normalized finite collections of `ℓ¹` descent directions lie in the approximately sparse unit set.

**Lean implementation helper.** -/
theorem finiteL1DescentDirections_approximatelySparse
    {n s : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : IsSparse s x)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    {h : EuclideanSpace ℝ (Fin n)}
    (hh : h ∈ finiteL1DescentDirections x T) :
    ‖h‖ = 1 ∧ ellOne h ≤ 2 * Real.sqrt s := by
  classical
  rcases Finset.mem_image.mp hh with ⟨z, hz, rfl⟩
  have hzFilter := Finset.mem_filter.mp hz
  have hzErase := Finset.mem_erase.mp hzFilter.1
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr hzErase.1
  have hnormpos : 0 < ‖z - x‖ := norm_pos_iff.mpr hzx
  have hdescent : z - x ∈ l1DescentCone x := by
    change ellOne (x + (z - x)) ≤ ellOne x
    simpa [add_sub_cancel_left] using hzFilter.2
  let S := coordinateSupport x
  have hsupport : ∀ i, i ∉ S → x i = 0 := by
    intro i hi
    by_contra hxi
    exact hi ((mem_coordinateSupport x i).2 hxi)
  have hoff : ellOneOn (Finset.univ \ S) (z - x) ≤ ellOneOn S (z - x) :=
    lemma_9_5_2_error_heavier_on_support x (z - x) S hsupport hdescent
  have hraw : ellOne (z - x) ≤ 2 * Real.sqrt s * ‖z - x‖ :=
    lemma_9_5_3_error_approximatelySparse (z - x) S hx hoff
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hnormpos.ne'
  · rw [ellOne_smul, abs_inv, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖z - x‖⁻¹ * ellOne (z - x) ≤
          ‖z - x‖⁻¹ * (2 * Real.sqrt s * ‖z - x‖) :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hnormpos.le)
      _ = 2 * Real.sqrt s := by field_simp [hnormpos.ne']

/-- Failure of finite `ℓ¹` recovery implies that the kernel meets an approximately sparse direction set.

**Lean implementation helper.** -/
theorem finiteL1RecoveryFailure_subset_kernelHits {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    {omega | finiteL1RecoveryFailure A x T omega} ⊆
      {omega | finiteKernelHits A (finiteL1DescentDirections x T) omega} := by
  classical
  intro omega hfail
  rcases hfail with ⟨z, hzT, hzx, hmin⟩
  let h : EuclideanSpace ℝ (Fin n) := ‖z - x‖⁻¹ • (z - x)
  have hzDir : h ∈ finiteL1DescentDirections x T := by
    unfold finiteL1DescentDirections
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzx, hzT⟩, ?_⟩, rfl⟩
    exact hmin.2 x rfl
  refine ⟨h, hzDir, ?_⟩
  dsimp [h]
  rw [matrixAction_smul,
    ← deterministicMatrixAction_eq_matrixAction A (z - x) omega,
    minimizer_error_mem_kernel hmin, smul_zero]

/-- The theorem reconstructs the complete escape proof. Lemmas 9.5.2--9.5.3
place every normalized failing direction in the approximately sparse unit
set; Exercise 9.26 bounds that finite width; Theorem 9.3.4 then controls the
failure event. There is no nullspace-avoidance assumption in this interface.

**Book Theorem 9.5.1.** -/
theorem theorem_9_5_1_exactSparseRecovery_finitePrior
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : IsSparse s x)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hsize : escapeSampleConstant * K ^ 4 *
      (16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) ^ 2 ≤
        (m : ℝ)) :
    μ {omega | finiteL1RecoveryFailure A x T omega} ≤
      ENNReal.ofReal (2 * Real.exp
        (-escapeTailConstant * (m : ℝ) / K ^ 4)) := by
  classical
  let D := finiteL1DescentDirections x T
  by_cases hD : D.Nonempty
  · letI : Nonempty ↥D := hD.to_subtype
    have happrox : ∀ h ∈ D, ‖h‖ = 1 ∧ ellOne h ≤ 2 * Real.sqrt s := by
      intro h hh
      exact finiteL1DescentDirections_approximatelySparse hx T hh
    have hwidth : HDP.Chapter7.gaussianWidth D ≤
        16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) :=
      gaussianWidth_approximatelySparseUnit_finset_le hs hsn D hD happrox
    have hwidth0 : 0 ≤ HDP.Chapter7.gaussianWidth D :=
      HDP.Chapter7.gaussianWidth_nonneg D hD
    have hbound0 : 0 ≤
        16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by positivity
    have hwidthSq : HDP.Chapter7.gaussianWidth D ^ 2 ≤
        (16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) ^ 2 :=
      (sq_le_sq₀ hwidth0 hbound0).2 hwidth
    have hescapeSize : escapeSampleConstant * K ^ 4 *
        HDP.Chapter7.gaussianWidth D ^ 2 ≤ (m : ℝ) :=
      (mul_le_mul_of_nonneg_left hwidthSq
        (mul_nonneg escapeSampleConstant_pos.le (by positivity))).trans hsize
    have hescape := theorem_9_3_4_escape_finite hm A hrowsm hsub hiso hindep
      hfinite hK hpsi D hD (fun h hh => (happrox h hh).1) hescapeSize
    exact (measure_mono
      (finiteL1RecoveryFailure_subset_kernelHits A x T)).trans hescape
  · have hempty : {omega | finiteL1RecoveryFailure A x T omega} = ∅ := by
      ext omega
      constructor
      · intro hfail
        have hhit := finiteL1RecoveryFailure_subset_kernelHits A x T hfail
        rcases hhit with ⟨h, hhD, _⟩
        exact (hD ⟨h, hhD⟩).elim
      · intro h
        exact h.elim
    rw [hempty, measure_empty]
    exact bot_le

/-! ## Uniform exact recovery over all sparse signals -/

/-- The source's approximately sparse spherical set `Tₛ`.

**Lean implementation helper.** -/
def approximatelySparseUnitSet (n s : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {h | ‖h‖ = 1 ∧ ellOne h ≤ 2 * Real.sqrt s}

/-- The approximately sparse unit set contains the origin.

**Lean implementation helper.** -/
theorem approximatelySparseUnitSet_nonempty {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n) :
    (approximatelySparseUnitSet n s).Nonempty := by
  classical
  have hn : 0 < n := hs.trans_le hsn
  let i : Fin n := ⟨0, hn⟩
  let e : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ i
  have heNorm : ‖e‖ = 1 := by simp [e]
  have heOne : ellOne e = 1 := by
    unfold ellOne
    rw [Finset.sum_eq_single i]
    · simp [e, EuclideanSpace.basisFun_apply]
    · intro j _ hji
      simp [e, EuclideanSpace.basisFun_apply, hji]
    · simp
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsqrtSq : (Real.sqrt s) ^ 2 = (s : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  refine ⟨e, heNorm, ?_⟩
  rw [heOne]
  nlinarith

/-- The approximately sparse unit set is bounded by its Euclidean unit-ball constraint.

**Lean implementation helper.** -/
theorem approximatelySparseUnitSet_isBounded (n s : ℕ) :
    Bornology.IsBounded (approximatelySparseUnitSet n s) := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨1, fun h hh => hh.1.le⟩

/-- The approximate-sparse set has width `O(sqrt(s log n))`. Actual-set Gaussian-width estimate for the approximately sparse sphere.

**Book Equation (9.30).** -/
theorem euclideanSetGaussianWidth_approximatelySparseUnitSet_le
    {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    HDP.Chapter8.euclideanSetGaussianWidth
        (approximatelySparseUnitSet n s) ≤
      16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) := by
  let C := 16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))
  have hratio : (1 : ℝ) ≤ Real.exp 1 * n / s := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hnexp : (n : ℝ) ≤ Real.exp 1 * n := by
      simpa using mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n)
    apply (le_div_iff₀ hsR).2
    simpa using hsnR.trans hnexp
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity [Real.log_nonneg hratio]
  have hENN :
      HDP.Chapter8.euclideanSetGaussianWidthENN
          (approximatelySparseUnitSet n s) ≤ ENNReal.ofReal C := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    exact ENNReal.ofReal_le_ofReal
      (gaussianWidth_approximatelySparseUnit_finset_le hs hsn F hF
        (fun h hh => hFT hh))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa [HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal hC0, C] using hreal

/-- The normalized recovery error lies in an approximately sparse set. A nonzero failing minimizer produces a unit approximately sparse
direction in the kernel. This is Lemmas 9.5.2--9.5.3 composed without any
finite candidate family.

**Book Lemma 9.5.3.** -/
theorem normalized_minimizerError_mem_approximatelySparseUnitSet
    {m n s : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x)
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat)
    (hne : xhat ≠ x) :
    let h := xhat - x
    ‖h‖⁻¹ • h ∈ approximatelySparseUnitSet n s := by
  let h := xhat - x
  have hhne : h ≠ 0 := sub_ne_zero.mpr hne
  have hnormpos : 0 < ‖h‖ := norm_pos_iff.mpr hhne
  have hdescent : h ∈ l1DescentCone x :=
    minimizer_error_mem_descentCone hmin
  let S := coordinateSupport x
  have hsupport : ∀ i, i ∉ S → x i = 0 := by
    intro i hi
    by_contra hxi
    exact hi ((mem_coordinateSupport x i).2 hxi)
  have hoff : ellOneOn (Finset.univ \ S) h ≤ ellOneOn S h :=
    lemma_9_5_2_error_heavier_on_support x h S hsupport hdescent
  have hraw : ellOne h ≤ 2 * Real.sqrt s * ‖h‖ :=
    lemma_9_5_3_error_approximatelySparse h S hx hoff
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hnormpos.ne'
  · rw [ellOne_smul, abs_inv, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖h‖⁻¹ * ellOne h ≤ ‖h‖⁻¹ * (2 * Real.sqrt s * ‖h‖) :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hnormpos.le)
      _ = 2 * Real.sqrt s := by field_simp [hnormpos.ne']

/-- Failure of uniform exact `ℓ¹` recovery for at least one `s`-sparse
signal.

**Lean implementation helper.** -/
def uniformL1RecoveryFailure {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) (s : ℕ) (ω : Ω) : Prop :=
  ∃ x xhat : EuclideanSpace ℝ (Fin n),
    IsSparse s x ∧
    IsL1RecoveryMinimizer (A ω)
      (deterministicMatrixAction (A ω) x) xhat ∧ xhat ≠ x

/-- A nonzero normalized error lies in the approximate-sparse set and the kernel.

**Book Equation (9.29).** -/
theorem uniformL1RecoveryFailure_subset_kernelHits {m n s : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) :
    {ω | uniformL1RecoveryFailure A s ω} ⊆
      {ω | kernelHits A (approximatelySparseUnitSet n s) ω} := by
  intro ω hfail
  obtain ⟨x, xhat, hx, hmin, hne⟩ := hfail
  let h := xhat - x
  let u := ‖h‖⁻¹ • h
  have hu : u ∈ approximatelySparseUnitSet n s := by
    exact normalized_minimizerError_mem_approximatelySparseUnitSet
      hx hmin hne
  refine ⟨u, hu, ?_⟩
  dsimp [u, h]
  rw [matrixAction_smul,
    ← deterministicMatrixAction_eq_matrixAction A (xhat - x) ω,
    minimizer_error_mem_kernel hmin, smul_zero]

/-- `l1` minimization exactly recovers every sparse vector with high probability. With the advertised probability, one draw of `A` recovers every `s`-sparse
signal by basis pursuit. The bad event quantifies over all signals and all
minimizers; it is controlled by a single escape event for the actual
approximately sparse sphere.

**Book Theorem 9.5.1.** -/
theorem theorem_9_5_1_exactSparseRecovery
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hsize : escapeSampleConstant * K ^ 4 *
      (16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) ^ 2 ≤
        (m : ℝ)) :
    μ {ω | uniformL1RecoveryFailure A s ω} ≤
      ENNReal.ofReal (2 * Real.exp
        (-escapeTailConstant * (m : ℝ) / K ^ 4)) := by
  let T := approximatelySparseUnitSet n s
  have hTne : T.Nonempty := approximatelySparseUnitSet_nonempty hs hsn
  have hTb : Bornology.IsBounded T := approximatelySparseUnitSet_isBounded n s
  have hwidth : HDP.Chapter8.euclideanSetGaussianWidth T ≤
      16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) :=
    euclideanSetGaussianWidth_approximatelySparseUnitSet_le hs hsn
  have hw0 : 0 ≤ HDP.Chapter8.euclideanSetGaussianWidth T :=
    ENNReal.toReal_nonneg
  have hC0 : 0 ≤ 16 * Real.sqrt
      (s * Real.log (Real.exp 1 * n / s)) := by positivity
  have hwidthSq : HDP.Chapter8.euclideanSetGaussianWidth T ^ 2 ≤
      (16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) ^ 2 :=
    (sq_le_sq₀ hw0 hC0).2 hwidth
  have hescapeSize : escapeSampleConstant * K ^ 4 *
      HDP.Chapter8.euclideanSetGaussianWidth T ^ 2 ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_left hwidthSq
      (mul_nonneg escapeSampleConstant_pos.le (by positivity))).trans hsize
  have hescape := theorem_9_3_4_escape hm A hrowsm hsub hiso hindep
    hfinite hK hpsi T hTne (fun h hh => hh.1) hescapeSize
  exact (measure_mono
    (uniformL1RecoveryFailure_subset_kernelHits A)).trans hescape

/-- Finite-family compatibility form of .

**Book Remark 9.5.4.** -/
theorem remark_9_5_4_improvedExactRecoveryWidth_finite {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n)
    (D : Finset (EuclideanSpace ℝ (Fin n))) (hD : D.Nonempty)
    (happrox : ∀ h ∈ D, ‖h‖ = 1 ∧ ellOne h ≤ 2 * Real.sqrt s) :
    HDP.Chapter7.gaussianWidth D ≤
      16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) :=
  gaussianWidth_approximatelySparseUnit_finset_le hs hsn D hD happrox

/-- A sharper width bound improves exact recovery to `s log(en/s)` measurements. The Gaussian width is that of the complete approximately sparse
sphere, not of a preselected finite family.

**Book Remark 9.5.4.** -/
theorem remark_9_5_4_improvedExactRecoveryWidth {n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n) :
    HDP.Chapter8.euclideanSetGaussianWidth
        (approximatelySparseUnitSet n s) ≤
      16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s)) :=
  euclideanSetGaussianWidth_approximatelySparseUnitSet_le hs hsn

/-- A sharper width bound improves exact recovery to `s log(en/s)` measurements. The source writes the sufficient row count as
`m ≥ C K⁴ s log (e*n/s)`. Here the absolute constant is exposed as
`256 * escapeSampleConstant`; the conclusion is the uniform actual-set
recovery event from Theorem 9.5.1.

**Book Remark 9.5.4.** -/
theorem remark_9_5_4_improvedExactRecovery
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (hsize : 256 * escapeSampleConstant * K ^ 4 *
      (s * Real.log (Real.exp 1 * n / s)) ≤ (m : ℝ)) :
    μ {ω | uniformL1RecoveryFailure A s ω} ≤
      ENNReal.ofReal (2 * Real.exp
        (-escapeTailConstant * (m : ℝ) / K ^ 4)) := by
  apply theorem_9_5_1_exactSparseRecovery hm hs hsn A hrowsm hsub hiso
    hindep hfinite hK hpsi
  have hratio : (1 : ℝ) ≤ Real.exp 1 * n / s := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    apply (le_div_iff₀ hsR).2
    simpa only [one_mul] using hsnR.trans (by
      simpa using mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n))
  have hq : 0 ≤ (s : ℝ) * Real.log (Real.exp 1 * n / s) :=
    mul_nonneg (Nat.cast_nonneg s) (Real.log_nonneg hratio)
  calc
    escapeSampleConstant * K ^ 4 *
        (16 * Real.sqrt (s * Real.log (Real.exp 1 * n / s))) ^ 2 =
      256 * escapeSampleConstant * K ^ 4 *
        (s * Real.log (Real.exp 1 * n / s)) := by
      rw [mul_pow, Real.sq_sqrt hq]
      ring
    _ ≤ (m : ℝ) := hsize

end

end HDP.Chapter9

end Source_13_ExactSparseRecovery

/-! ## Material formerly in `14_RestrictedIsometry.lean` -/

section Source_14_RestrictedIsometry

/-!
# Book Chapter 9, §9.5.2: restricted isometries

RIP orders and block sizes are natural numbers.  This corrects the printed
Theorem 9.5.6, where the real quantity `(1+λ)s` is used as a cardinality.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- RIP uniformly bounds `‖Av‖` on sparse vectors. Definition 9.5.5: restricted isometry with lower and upper singular
bounds, without pretending the order is a real number.

**Book Definition 9.5.5.** -/
def IsRestrictedIsometry {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (order : ℕ) (alpha beta : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), IsSparse order x →
    alpha * ‖x‖ ≤ ‖deterministicMatrixAction A x‖ ∧
      ‖deterministicMatrixAction A x‖ ≤ beta * ‖x‖

/-- Restricted isometry gives the lower norm bound on every sparse vector.

**Lean implementation helper.** -/
theorem IsRestrictedIsometry.lower {m n order : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {alpha beta : ℝ}
    (h : IsRestrictedIsometry A order alpha beta)
    {x : EuclideanSpace ℝ (Fin n)} (hx : IsSparse order x) :
    alpha * ‖x‖ ≤ ‖deterministicMatrixAction A x‖ :=
  (h x hx).1

/-- Restricted isometry gives the upper norm bound on every sparse vector.

**Lean implementation helper.** -/
theorem IsRestrictedIsometry.upper {m n order : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {alpha beta : ℝ}
    (h : IsRestrictedIsometry A order alpha beta)
    {x : EuclideanSpace ℝ (Fin n)} (hx : IsSparse order x) :
    ‖deterministicMatrixAction A x‖ ≤ beta * ‖x‖ :=
  (h x hx).2

/-- RIP with a positive lower constant has no sparse kernel vector.

**Lean implementation helper.** -/
theorem rip_kernel_eq_zero {m n order : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {alpha beta : ℝ}
    (hRIP : IsRestrictedIsometry A order alpha beta)
    (halpha : 0 < alpha)
    {x : EuclideanSpace ℝ (Fin n)} (hx : IsSparse order x)
    (hAx : deterministicMatrixAction A x = 0) : x = 0 := by
  have hlow := hRIP.lower hx
  rw [hAx, norm_zero] at hlow
  have hxnorm : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hxnorm

/-- Exact nullspace criterion tailored to `ℓ¹` recovery.

**Lean implementation helper.** -/
def HasExactL1NullspaceProperty {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Prop :=
  ∀ (x h : EuclideanSpace ℝ (Fin n)), IsSparse s x → h ≠ 0 →
    deterministicMatrixAction A h = 0 → ellOne x < ellOne (x + h)

/-- The support-mass nullspace property printed in Exercise 9.32.

**Book Exercise 9.32.** -/
def NullspaceProperty {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Prop :=
  ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 →
    deterministicMatrixAction A h = 0 →
    ∀ S : Finset (Fin n), S.card ≤ s →
      ellOneOn S h < ellOneOn (Finset.univ \ S) h

/-- Uniform uniqueness of basis pursuit on the `s`-sparse model.

**Lean implementation helper.** -/
def UniformUniqueL1Recovery {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), IsSparse s x →
    ∀ z : EuclideanSpace ℝ (Fin n),
      deterministicMatrixAction A z = deterministicMatrixAction A x →
      ellOne z ≤ ellOne x → z = x

/-- The strict nullspace property implies exact `ℓ¹` recovery on the chosen support.

**Lean implementation helper.** -/
theorem exactL1NullspaceProperty_of_nullspaceProperty {m n s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hNSP : NullspaceProperty A s) :
    HasExactL1NullspaceProperty A s := by
  intro x h hx hh hker
  let S := coordinateSupport x
  have hcard : S.card ≤ s := hx
  have hmass := hNSP h hh hker S hcard
  have hsupport : ∀ i, i ∉ S → x i = 0 := by
    intro i hi
    by_contra hxi
    exact hi ((mem_coordinateSupport x i).2 hxi)
  have hinside : ellOneOn S x - ellOneOn S h ≤ ellOneOn S (x + h) := by
    rw [ellOneOn, ellOneOn, ellOneOn, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi => by
      have ht := abs_sub (x i + h i) (h i)
      simp only [add_sub_cancel_right] at ht
      change |x i| - |h i| ≤ |x i + h i|
      exact sub_le_iff_le_add.mpr ht
  have houtside : ellOneOn (Finset.univ \ S) (x + h) =
      ellOneOn (Finset.univ \ S) h := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [hsupport i hiS]
  have hxoff : ellOneOn (Finset.univ \ S) x = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [hsupport i hiS]
  rw [ellOne_eq_on_add_off S x, hxoff, add_zero,
    ellOne_eq_on_add_off S (x + h), houtside]
  linarith

/-- Uniform uniqueness of `ℓ¹` recovery implies the strict nullspace property.

**Lean implementation helper.** -/
theorem nullspaceProperty_of_uniformUniqueL1Recovery {m n s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hunique : UniformUniqueL1Recovery A s) :
    NullspaceProperty A s := by
  intro h hh hker S hScard
  by_contra hnot
  have hmass : ellOneOn (Finset.univ \ S) h ≤ ellOneOn S h :=
    le_of_not_gt hnot
  let x : EuclideanSpace ℝ (Fin n) := -coordinateRestriction h S
  let z : EuclideanSpace ℝ (Fin n) := coordinateRestriction h Sᶜ
  have hxSparse : IsSparse s x := by
    have hr := restriction_isSparse h hScard
    change IsSparse s (-coordinateRestriction h S)
    have hsupp : coordinateSupport (-coordinateRestriction h S) =
        coordinateSupport (coordinateRestriction h S) := by
      ext i
      simp [mem_coordinateSupport]
    simpa [IsSparse, ellZero, hsupp] using hr
  have hsum : coordinateRestriction h S + coordinateRestriction h Sᶜ = h :=
    restriction_add_compl h S
  have hzx : z - x = h := by
    dsimp [x, z]
    rw [sub_neg_eq_add]
    simpa [add_comm] using hsum
  have hmeasurement : deterministicMatrixAction A z =
      deterministicMatrixAction A x := by
    apply sub_eq_zero.mp
    rw [← deterministicMatrixAction_sub, hzx, hker]
  have hzNorm : ellOne z = ellOneOn (Finset.univ \ S) h := by
    dsimp [z]
    simpa [Finset.compl_eq_univ_sdiff] using
      ellOne_coordinateRestriction Sᶜ h
  have hxNorm : ellOne x = ellOneOn S h := by
    dsimp [x]
    rw [show ellOne (-coordinateRestriction h S) =
        ellOne (coordinateRestriction h S) by simp [ellOne]]
    exact ellOne_coordinateRestriction S h
  have hzxEq : z = x := hunique x hxSparse z hmeasurement (by
    rw [hzNorm, hxNorm]
    exact hmass)
  apply hh
  rw [← hzx, hzxEq, sub_self]

/-- The exact nullspace property implies uniqueness of the `ℓ¹` program.

**Lean implementation helper.** -/
theorem exactRecovery_of_exactL1NullspaceProperty {m n s : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hNSP : HasExactL1NullspaceProperty A s)
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x)
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat) :
    xhat = x := by
  by_contra hne
  have hhne : xhat - x ≠ 0 := sub_ne_zero.mpr hne
  have hker := minimizer_error_mem_kernel hmin
  have hstrict := hNSP x (xhat - x) hx hhne hker
  have hle := hmin.2 x rfl
  have hadd : x + (xhat - x) = xhat := by abel
  rw [hadd] at hstrict
  exact (not_lt_of_ge hle) hstrict

/-- This is the exact
nullspace-property/unique-recovery direction used later in the book.

**Book Exercise 9.32(a).** -/
theorem exercise_9_32a_nullspaceProperty_implies_uniqueRecovery
    {m n s : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hNSP : NullspaceProperty A s)
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x)
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat) :
    xhat = x :=
  exactRecovery_of_exactL1NullspaceProperty
    (exactL1NullspaceProperty_of_nullspaceProperty hNSP) hx hmin

/-- Nullspace property is equivalent to unique `l1` recovery of every sparse vector.

**Book Exercise 9.32(a).** -/
theorem exercise_9_32a_nullspaceProperty_iff_uniqueRecovery
    {m n s : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    NullspaceProperty A s ↔ UniformUniqueL1Recovery A s := by
  constructor
  · intro hNSP x hx z hmeasurement hnorm
    let h : EuclideanSpace ℝ (Fin n) := z - x
    by_cases hh : h = 0
    · exact sub_eq_zero.mp hh
    have hker : deterministicMatrixAction A h = 0 := by
      dsimp [h]
      rw [deterministicMatrixAction_sub, hmeasurement, sub_self]
    have hstrict := exactL1NullspaceProperty_of_nullspaceProperty hNSP x h hx hh hker
    have hxadd : x + h = z := by dsimp [h]; abel
    rw [hxadd] at hstrict
    exact (not_lt_of_ge hnorm hstrict).elim
  · exact nullspaceProperty_of_uniformUniqueL1Recovery

/-- The sorted-block core of Theorem 9.5.6. This is a proof, rather than a
caller-supplied bridge: the complement of the signal support is sorted by
magnitude, partitioned into blocks of size `q*s`, and the RIP lower and upper
bounds are applied to the first block and the tail respectively.

**Book Theorem 9.5.6.** -/
theorem exactL1NullspaceProperty_of_rip
    {m n s q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {alpha beta : ℝ}
    (hs : 0 < s) (hq : 0 < q) (halpha : 0 < alpha) (hbeta : 0 ≤ beta)
    (hconstants : beta ^ 2 < (q : ℝ) * alpha ^ 2)
    (hRIP : IsRestrictedIsometry A ((q + 1) * s) alpha beta) :
    HasExactL1NullspaceProperty A s := by
  classical
  intro x h hx hh hker
  by_contra hnot
  have hdescent : ellOne (x + h) ≤ ellOne x := le_of_not_gt hnot
  let S := coordinateSupport x
  let hS := coordinateRestriction h S
  let u := coordinateRestriction h Sᶜ
  let b := q * s
  let v₀ := coordinateRestriction u (magnitudeBlock u b 0)
  let core := hS + v₀
  let tail : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
    coordinateRestriction u (magnitudeBlock u b (k + 1))
  have hS_card : S.card ≤ s := hx
  have hb : 0 < b := Nat.mul_pos hq hs
  have hsupport : ∀ i, i ∉ S → x i = 0 := by
    intro i hi
    by_contra hxi
    exact hi ((mem_coordinateSupport x i).2 hxi)
  have hcone := lemma_9_5_2_error_heavier_on_support x h S hsupport hdescent
  have huOne : ellOne u ≤ ellOne hS := by
    change ellOne (coordinateRestriction h Sᶜ) ≤
      ellOne (coordinateRestriction h S)
    rw [ellOne_coordinateRestriction, ellOne_coordinateRestriction]
    simpa [Finset.compl_eq_univ_sdiff] using hcone
  have hblocks := sum_coordinateRestriction_magnitudeBlocks u hb
  rw [Finset.sum_range_succ'] at hblocks
  have hblocks' : v₀ + ∑ k ∈ Finset.range n, tail k = u := by
    simpa [v₀, tail, add_comm] using hblocks
  have hsplit : hS + u = h := by
    simpa [hS, u] using restriction_add_compl h S
  have hdecomp : core + (∑ k ∈ Finset.range n, tail k) = h := by
    calc
      core + (∑ k ∈ Finset.range n, tail k) =
          hS + (v₀ + ∑ k ∈ Finset.range n, tail k) := by
        simp only [core, tail]
        abel
      _ = hS + u := by rw [hblocks']
      _ = h := hsplit
  have hv₀_zero_on_S : ∀ i ∈ S, v₀ i = 0 := by
    intro i hi
    simp [v₀, u, coordinateRestriction, hi]
  have hcoreRestriction : coordinateRestriction core S = hS := by
    ext i
    by_cases hi : i ∈ S
    · simp [core, hS, coordinateRestriction, hi, hv₀_zero_on_S i hi]
    · simp [core, hS, coordinateRestriction, hi]
  have hcoreSparse : IsSparse ((q + 1) * s) core := by
    have hsupp : coordinateSupport core ⊆ S ∪ magnitudeBlock u b 0 := by
      intro i hi
      by_contra hnotmem
      have hiS : i ∉ S := fun his => hnotmem (Finset.mem_union_left _ his)
      have hiB : i ∉ magnitudeBlock u b 0 :=
        fun hib => hnotmem (Finset.mem_union_right _ hib)
      have hne := (mem_coordinateSupport core i).mp hi
      apply hne
      have hhSi : hS i = 0 := by
        change (if i ∈ S then h i else 0) = 0
        rw [if_neg hiS]
      have hv₀i : v₀ i = 0 := by
        change (if i ∈ magnitudeBlock u b 0 then u i else 0) = 0
        rw [if_neg hiB]
      simp [core, hhSi, hv₀i]
    calc
      ellZero core = (coordinateSupport core).card := rfl
      _ ≤ (S ∪ magnitudeBlock u b 0).card := Finset.card_le_card hsupp
      _ ≤ S.card + (magnitudeBlock u b 0).card := Finset.card_union_le _ _
      _ ≤ s + b := Nat.add_le_add hS_card (magnitudeBlock_card_le u b 0)
      _ = (q + 1) * s := by simp [b, Nat.add_mul, Nat.add_comm]
  have htailSparse : ∀ k, IsSparse ((q + 1) * s) (tail k) := by
    intro k
    have hk := magnitudeBlock_restriction_sparse u b (k + 1)
    exact hk.trans (by
      dsimp [b]
      simp [Nat.add_mul])
  have hAadd : deterministicMatrixAction A core +
      deterministicMatrixAction A (∑ k ∈ Finset.range n, tail k) = 0 := by
    rw [← deterministicMatrixAction_add, hdecomp, hker]
  have hAcore : deterministicMatrixAction A core =
      -deterministicMatrixAction A (∑ k ∈ Finset.range n, tail k) := by
    exact eq_neg_of_add_eq_zero_left hAadd
  have hA_tail_sum : deterministicMatrixAction A (∑ k ∈ Finset.range n, tail k) =
      ∑ k ∈ Finset.range n, deterministicMatrixAction A (tail k) := by
    simp [deterministicMatrixAction]
  have hupper : ‖deterministicMatrixAction A core‖ ≤
      beta * (∑ k ∈ Finset.range n, ‖tail k‖) := by
    rw [hAcore, norm_neg, hA_tail_sum]
    calc
      ‖∑ k ∈ Finset.range n, deterministicMatrixAction A (tail k)‖ ≤
          ∑ k ∈ Finset.range n, ‖deterministicMatrixAction A (tail k)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range n, beta * ‖tail k‖ := by
        apply Finset.sum_le_sum
        intro k hk
        exact hRIP.upper (htailSparse k)
      _ = beta * (∑ k ∈ Finset.range n, ‖tail k‖) := by
        rw [Finset.mul_sum]
  have htailOne : (∑ k ∈ Finset.range n, ‖tail k‖) ≤
      ellOne u / Real.sqrt b := by
    simpa [tail] using sum_tail_norm_magnitudeBlocks_le u hb
  have hhS_sparse : IsSparse s hS := restriction_isSparse h hS_card
  have hhS_norm : ‖hS‖ ≤ ‖core‖ := by
    rw [← hcoreRestriction]
    exact norm_coordinateRestriction_le core S
  have huOneCore : ellOne u ≤ Real.sqrt s * ‖core‖ := by
    calc
      ellOne u ≤ ellOne hS := huOne
      _ ≤ Real.sqrt s * ‖hS‖ := ellOne_le_sqrt_sparse_mul_norm hhS_sparse
      _ ≤ Real.sqrt s * ‖core‖ :=
        mul_le_mul_of_nonneg_left hhS_norm (Real.sqrt_nonneg _)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsqrtS : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hsR
  have hsqrtQ : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqR
  have hsqrtB : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.2 hbR
  have hsqrt_mul : Real.sqrt (b : ℝ) =
      Real.sqrt (q : ℝ) * Real.sqrt (s : ℝ) := by
    simp [b, Nat.cast_mul, Real.sqrt_mul hqR.le]
  have htailCore : (∑ k ∈ Finset.range n, ‖tail k‖) ≤
      ‖core‖ / Real.sqrt q := by
    calc
      (∑ k ∈ Finset.range n, ‖tail k‖) ≤ ellOne u / Real.sqrt b := htailOne
      _ ≤ (Real.sqrt s * ‖core‖) / Real.sqrt b :=
        div_le_div_of_nonneg_right huOneCore hsqrtB.le
      _ = ‖core‖ / Real.sqrt q := by
        rw [hsqrt_mul]
        field_simp [hsqrtS.ne', hsqrtQ.ne']
  have hmain : alpha * ‖core‖ ≤ beta * (‖core‖ / Real.sqrt q) := by
    calc
      alpha * ‖core‖ ≤ ‖deterministicMatrixAction A core‖ := hRIP.lower hcoreSparse
      _ ≤ beta * (∑ k ∈ Finset.range n, ‖tail k‖) := hupper
      _ ≤ beta * (‖core‖ / Real.sqrt q) :=
        mul_le_mul_of_nonneg_left htailCore hbeta
  have hbeta_lt : beta < alpha * Real.sqrt q := by
    apply (sq_lt_sq₀ hbeta (mul_nonneg halpha.le hsqrtQ.le)).mp
    calc
      beta ^ 2 < (q : ℝ) * alpha ^ 2 := hconstants
      _ = (alpha * Real.sqrt q) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hqR.le]
        ring
  have hcoreZero : core = 0 := by
    apply norm_eq_zero.mp
    by_contra hnorm
    have hnormpos : 0 < ‖core‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnorm)
    have hratio : alpha ≤ beta / Real.sqrt q := by
      apply (le_div_iff₀ hsqrtQ).mpr
      have hm := mul_le_mul_of_nonneg_right hmain hsqrtQ.le
      have hcancel :
          (beta * (‖core‖ / Real.sqrt q)) * Real.sqrt q = beta * ‖core‖ := by
        field_simp [hsqrtQ.ne']
      rw [hcancel] at hm
      nlinarith
    have hratioStrict : beta / Real.sqrt q < alpha :=
      (div_lt_iff₀ hsqrtQ).mpr (by simpa [mul_comm] using hbeta_lt)
    exact (not_lt_of_ge hratio) hratioStrict
  have hhSzero : hS = 0 := by
    rw [← hcoreRestriction, hcoreZero]
    ext i
    simp [coordinateRestriction]
  have huZero : u = 0 := by
    apply (ellOne_eq_zero_iff u).mp
    apply le_antisymm
    · calc
        ellOne u ≤ ellOne hS := huOne
        _ = 0 := by rw [hhSzero, ellOne_zero]
    · exact ellOne_nonneg u
  apply hh
  rw [← hsplit, hhSzero, huZero, add_zero]

/-- A sufficiently strong higher-order RIP implies exact `l1` recovery. The printed real cardinal `(1+λ)s` is replaced by the natural block multiplier
`q`; the exact source inequality is `beta² < q*alpha²`.

**Book Theorem 9.5.6.** -/
theorem theorem_9_5_6_rip_implies_exactRecovery
    {m n s q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {alpha beta : ℝ}
    (hs : 0 < s) (hq : 0 < q) (halpha : 0 < alpha) (hbeta : 0 ≤ beta)
    (hconstants : beta ^ 2 < (q : ℝ) * alpha ^ 2)
    (hRIP : IsRestrictedIsometry A ((q + 1) * s) alpha beta)
    {x xhat : EuclideanSpace ℝ (Fin n)}
    (hx : IsSparse s x)
    (hmin : IsL1RecoveryMinimizer A
      (deterministicMatrixAction A x) xhat) :
    xhat = x := by
  exact exactRecovery_of_exactL1NullspaceProperty
    (exactL1NullspaceProperty_of_rip hs hq halpha hbeta hconstants hRIP) hx hmin

/-! ### Arbitrary coordinate restrictions -/

/-- Zero-padded inclusion of the coordinates indexed by an `s`-element
support.

**Lean implementation helper.** -/
noncomputable def supportCoordinateLinearMap {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s) :
    EuclideanSpace ℝ (Fin s) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun u := WithLp.toLp 2 fun j =>
    if hj : j ∈ S then u ((S.orderIsoOfFin hS).symm ⟨j, hj⟩) else 0
  map_add' u v := by
    ext j
    by_cases hj : j ∈ S <;> simp [hj]
  map_smul' c u := by
    ext j
    by_cases hj : j ∈ S <;> simp [hj]

/-- The support-coordinate linear map evaluates a vector on the selected coordinates.

**Lean implementation helper.** -/
@[simp] theorem supportCoordinateLinearMap_apply {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (u : EuclideanSpace ℝ (Fin s)) (j : Fin n) :
    supportCoordinateLinearMap S hS u j =
      if hj : j ∈ S then u ((S.orderIsoOfFin hS).symm ⟨j, hj⟩) else 0 := rfl

/-- The support-coordinate linear map preserves the Euclidean norm on supported vectors.

**Lean implementation helper.** -/
theorem supportCoordinateLinearMap_norm {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (u : EuclideanSpace ℝ (Fin s)) :
    ‖supportCoordinateLinearMap S hS u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  change (∑ j : Fin n, ‖supportCoordinateLinearMap S hS u j‖ ^ 2) =
    ∑ i : Fin s, ‖u i‖ ^ 2
  calc
    (∑ j : Fin n, ‖supportCoordinateLinearMap S hS u j‖ ^ 2) =
        ∑ j ∈ S, ‖supportCoordinateLinearMap S hS u j‖ ^ 2 := by
      symm
      apply Finset.sum_subset S.subset_univ
      intro j hj hnot
      simp [supportCoordinateLinearMap_apply, hnot]
    _ = ∑ i : Fin s, ‖u i‖ ^ 2 := by
      symm
      apply Finset.sum_bij
          (fun i (_hi : i ∈ (Finset.univ : Finset (Fin s))) =>
            ((S.orderIsoOfFin hS) i : Fin n))
      · intro i hi
        exact (S.orderIsoOfFin hS i).property
      · intro i₁ hi₁ i₂ hi₂ heq
        exact (S.orderIsoOfFin hS).injective (Subtype.ext heq)
      · intro j hj
        let jS : ↑S := ⟨j, hj⟩
        exact ⟨(S.orderIsoOfFin hS).symm jS, Finset.mem_univ _, by
          simp [jS]⟩
      · intro i hi
        have hmem : ((S.orderIsoOfFin hS i : ↑S) : Fin n) ∈ S :=
          (S.orderIsoOfFin hS i).property
        have hidx : (S.orderIsoOfFin hS).symm
            ⟨((S.orderIsoOfFin hS i : ↑S) : Fin n), hmem⟩ = i := by
          have hsub :
              (⟨((S.orderIsoOfFin hS i : ↑S) : Fin n), hmem⟩ : ↑S) =
                (S.orderIsoOfFin hS) i := Subtype.ext rfl
          rw [hsub]
          exact (S.orderIsoOfFin hS).symm_apply_apply i
        rw [supportCoordinateLinearMap_apply, dif_pos hmem, hidx]

/-- The support inclusion as a linear isometry.

**Lean implementation helper.** -/
noncomputable def supportCoordinateIsometry {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s) :
    EuclideanSpace ℝ (Fin s) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearMap := supportCoordinateLinearMap S hS
  norm_map' := supportCoordinateLinearMap_norm S hS

/-- The support-coordinate isometry inserts subtype coordinates into the ambient vector and fills the complement with zero.

**Lean implementation helper.** -/
@[simp] theorem supportCoordinateIsometry_apply {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (u : EuclideanSpace ℝ (Fin s)) (j : Fin n) :
    supportCoordinateIsometry S hS u j =
      if hj : j ∈ S then u ((S.orderIsoOfFin hS).symm ⟨j, hj⟩) else 0 := rfl

/-- Restrict a matrix to an arbitrary ordered support.

**Lean implementation helper.** -/
def supportColumnRestriction {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin s) ℝ :=
  A.submatrix id (fun j => ((S.orderIsoOfFin hS) j : Fin n))

/-- A restricted-column matrix entry is the corresponding entry of the original matrix under the support ordering.

**Lean implementation helper.** -/
@[simp] theorem supportColumnRestriction_apply {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin s) :
    supportColumnRestriction S hS A i j =
      A i ((S.orderIsoOfFin hS j : ↑S) : Fin n) := rfl

/-- A supported linear combination of embedded coordinates agrees with the corresponding ambient sum.

**Lean implementation helper.** -/
theorem sum_mul_supportCoordinateIsometry {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (a : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin s)) :
    (∑ j : Fin n, a j * supportCoordinateIsometry S hS u j) =
      ∑ i : Fin s, a ((S.orderIsoOfFin hS i : ↑S) : Fin n) * u i := by
  calc
    (∑ j : Fin n, a j * supportCoordinateIsometry S hS u j) =
        ∑ j ∈ S, a j * supportCoordinateIsometry S hS u j := by
      symm
      apply Finset.sum_subset S.subset_univ
      intro j hj hnot
      simp [supportCoordinateIsometry_apply, hnot]
    _ = ∑ i : Fin s, a ((S.orderIsoOfFin hS i : ↑S) : Fin n) * u i := by
      symm
      apply Finset.sum_bij
          (fun i (_hi : i ∈ (Finset.univ : Finset (Fin s))) =>
            ((S.orderIsoOfFin hS) i : Fin n))
      · intro i hi
        exact (S.orderIsoOfFin hS i).property
      · intro i₁ hi₁ i₂ hi₂ heq
        exact (S.orderIsoOfFin hS).injective (Subtype.ext heq)
      · intro j hj
        let jS : ↑S := ⟨j, hj⟩
        exact ⟨(S.orderIsoOfFin hS).symm jS, Finset.mem_univ _, by
          simp [jS]⟩
      · intro i hi
        have hmem : ((S.orderIsoOfFin hS i : ↑S) : Fin n) ∈ S :=
          (S.orderIsoOfFin hS i).property
        have hidx : (S.orderIsoOfFin hS).symm
            ⟨((S.orderIsoOfFin hS i : ↑S) : Fin n), hmem⟩ = i := by
          have hsub :
              (⟨((S.orderIsoOfFin hS i : ↑S) : Fin n), hmem⟩ : ↑S) =
                (S.orderIsoOfFin hS) i := Subtype.ext rfl
          rw [hsub]
          exact (S.orderIsoOfFin hS).symm_apply_apply i
        rw [supportCoordinateIsometry_apply, dif_pos hmem, hidx]

/-- The Euclidean linear map of the restricted-column matrix equals composition with the support-coordinate isometry.

**Lean implementation helper.** -/
theorem toEuclideanLin_supportColumnRestriction {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : Matrix (Fin m) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin s)) :
    (supportColumnRestriction S hS A).toEuclideanLin u =
      A.toEuclideanLin (supportCoordinateIsometry S hS u) := by
  ext i
  simp only [Matrix.toLpLin_apply]
  exact (sum_mul_supportCoordinateIsometry S hS (A i) u).symm

/-- Row inner products after column restriction equal ambient row inner products with the embedded vector.

**Lean implementation helper.** -/
theorem inner_supportColumnRestriction_row {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (i : Fin m) (omega : Ω) (u : EuclideanSpace ℝ (Fin s)) :
    inner ℝ (HDP.randomMatrixRow
      (fun omega => supportColumnRestriction S hS (A omega)) i omega) u =
      inner ℝ (HDP.randomMatrixRow A i omega)
        (supportCoordinateIsometry S hS u) := by
  rw [HDP.inner_randomMatrixRow, HDP.inner_randomMatrixRow]
  exact (sum_mul_supportCoordinateIsometry S hS (A omega i) u).symm

/-- Restricting matrix columns preserves almost-everywhere row measurability.

**Lean implementation helper.** -/
theorem supportColumnRestriction_aemeasurableRows {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows) :
    HDP.RandomMatrix.AEMeasurableRows
      (fun omega => supportColumnRestriction S hS (A omega)) μ := by
  apply HDP.RandomMatrix.AEMeasurableEntries.aemeasurable_rows
  intro i j
  exact (hrowsm.measurable_entry i
    ((S.orderIsoOfFin hS j : ↑S) : Fin n)).aemeasurable

/-- Restricting matrix columns preserves the subgaussian-row property.

**Lean implementation helper.** -/
theorem supportColumnRestriction_subGaussianRows {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hsub : A.SubGaussianRows μ) :
    HDP.RandomMatrix.SubGaussianRows
      (fun omega => supportColumnRestriction S hS (A omega)) μ := by
  intro i u
  simpa only [inner_supportColumnRestriction_row] using
    hsub.marginal i (supportCoordinateIsometry S hS u)

/-- Restricting matrix columns preserves isotropy of the rows.

**Lean implementation helper.** -/
theorem supportColumnRestriction_isotropicRows {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hiso : A.IsotropicRows μ) :
    HDP.RandomMatrix.IsotropicRows
      (fun omega => supportColumnRestriction S hS (A omega)) μ := by
  intro i
  apply HDP.isIsotropic_iff.mpr
  intro a b
  have h := HDP.isIsotropic_iff.mp (hiso i)
    ((S.orderIsoOfFin hS a : ↑S) : Fin n)
    ((S.orderIsoOfFin hS b : ↑S) : Fin n)
  simpa [supportColumnRestriction,
    (S.orderIsoOfFin hS).injective.eq_iff] using h

/-- Restricting matrix columns preserves row independence.

**Lean implementation helper.** -/
theorem supportColumnRestriction_independentRows {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hindep : A.IndependentRows μ) :
    HDP.RandomMatrix.IndependentRows
      (fun omega => supportColumnRestriction S hS (A omega)) μ := by
  let proj : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin s) :=
    fun z => WithLp.toLp 2
      (fun j => z ((S.orderIsoOfFin hS j : ↑S) : Fin n))
  have hproj : Measurable proj := by
    dsimp [proj]
    fun_prop
  have h := hindep.comp (fun _ => proj) (fun _ => hproj)
  apply h.congr
  intro i
  filter_upwards [] with omega
  ext j
  rfl

/-- The directional `ψ₂` norm of a restricted row is bounded by the corresponding ambient direction.

**Lean implementation helper.** -/
theorem supportColumnRestriction_direction_psi2_le {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hfinite : A.RowPsi2Finite μ) {K : ℝ}
    (hpsi : A.RowPsi2Bound μ K)
    (i : Fin m) (u : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) :
    HDP.psi2Norm (fun omega => inner ℝ
      (HDP.randomMatrixRow
        (fun omega => supportColumnRestriction S hS (A omega)) i omega) u) μ ≤ K := by
  have hunit : ‖supportCoordinateIsometry S hS u‖ = 1 := by
    rw [LinearIsometry.norm_map, hu]
  have h := (HDP.psi2Norm_marginal_le_vector (hfinite i) hunit).trans (hpsi i)
  simpa only [inner_supportColumnRestriction_row] using h

/-- Column restriction preserves finiteness of row `ψ₂` norms.

**Lean implementation helper.** -/
theorem supportColumnRestriction_rowPsi2Finite {m n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hfinite : A.RowPsi2Finite μ) {K : ℝ}
    (hpsi : A.RowPsi2Bound μ K) :
    HDP.RandomMatrix.RowPsi2Finite
      (fun omega => supportColumnRestriction S hS (A omega)) μ := by
  intro i
  refine ⟨K, ?_⟩
  intro r hr
  rcases hr with ⟨u, hu, rfl⟩
  exact supportColumnRestriction_direction_psi2_le S hS A hfinite hpsi i u hu

/-- Column restriction preserves a uniform row `ψ₂` bound.

**Lean implementation helper.** -/
theorem supportColumnRestriction_rowPsi2Bound {m n s : ℕ} [NeZero s]
    (S : Finset (Fin n)) (hS : S.card = s)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hfinite : A.RowPsi2Finite μ) {K : ℝ}
    (hpsi : A.RowPsi2Bound μ K) :
    HDP.RandomMatrix.RowPsi2Bound
      (fun omega => supportColumnRestriction S hS (A omega)) μ K := by
  intro i
  rw [HDP.psi2NormVector]
  apply csSup_le
  · let u0 : EuclideanSpace ℝ (Fin s) :=
      EuclideanSpace.single ⟨0, NeZero.pos s⟩ 1
    exact ⟨HDP.psi2Norm (fun omega => inner ℝ
      (HDP.randomMatrixRow
        (fun omega => supportColumnRestriction S hS (A omega)) i omega) u0) μ,
      u0, by simp [u0], rfl⟩
  · intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact supportColumnRestriction_direction_psi2_le S hS A hfinite hpsi i u hu

/-- Read a vector on a chosen ordered support.

**Lean implementation helper.** -/
noncomputable def supportCoordinateProjection {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 fun i => x ((S.orderIsoOfFin hS i : ↑S) : Fin n)

/-- Projecting an embedded support vector back to the support recovers the original vector.

**Lean implementation helper.** -/
theorem supportCoordinateIsometry_projection {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (x : EuclideanSpace ℝ (Fin n))
    (hsupp : coordinateSupport x ⊆ S) :
    supportCoordinateIsometry S hS (supportCoordinateProjection S hS x) = x := by
  ext j
  by_cases hj : j ∈ S
  · let jS : ↑S := ⟨j, hj⟩
    rw [supportCoordinateIsometry_apply, dif_pos hj]
    change x (((S.orderIsoOfFin hS)
      ((S.orderIsoOfFin hS).symm jS) : ↑S) : Fin n) = x j
    rw [(S.orderIsoOfFin hS).apply_symm_apply jS]
  · have hjSupport : j ∉ coordinateSupport x := fun h => hj (hsupp h)
    have hxj : x j = 0 := by
      by_contra hne
      exact hjSupport ((mem_coordinateSupport x j).mpr hne)
    simp [supportCoordinateIsometry_apply, hj, hxj]

/-- Coordinate projection onto a support is norm nonincreasing.

**Lean implementation helper.** -/
theorem supportCoordinateProjection_norm {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (x : EuclideanSpace ℝ (Fin n))
    (hsupp : coordinateSupport x ⊆ S) :
    ‖supportCoordinateProjection S hS x‖ = ‖x‖ := by
  rw [← LinearIsometry.norm_map (supportCoordinateIsometry S hS),
    supportCoordinateIsometry_projection S hS x hsupp]

/-- Embedding a support-coordinate vector produces a sparse ambient vector.

**Lean implementation helper.** -/
theorem supportCoordinateIsometry_isSparse {n s : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s)
    (u : EuclideanSpace ℝ (Fin s)) :
    IsSparse s (supportCoordinateIsometry S hS u) := by
  have hsupp : coordinateSupport (supportCoordinateIsometry S hS u) ⊆ S := by
    intro j hj
    by_contra hjS
    have hne := (mem_coordinateSupport _ j).mp hj
    apply hne
    simp [supportCoordinateIsometry_apply, hjS]
  calc
    ellZero (supportCoordinateIsometry S hS u) =
        (coordinateSupport (supportCoordinateIsometry S hS u)).card := rfl
    _ ≤ S.card := Finset.card_le_card hsupp
    _ = s := hS

/-- RIP uniformly bounds `‖Av‖` on sparse vectors. Display (9.31): RIP is equivalent to simultaneous extreme singular-value
bounds on every `s`-column restriction.

**Book Definition 9.5.5.** -/
theorem rip_iff_supportSingularValues {m n s : ℕ}
    (hs : 0 < s) (hsn : s ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (alpha beta : ℝ) :
    IsRestrictedIsometry A s alpha beta ↔
      ∀ (S : Finset (Fin n)) (hS : S.card = s),
        alpha ≤ HDP.matrixSingularValue (supportColumnRestriction S hS A) (s - 1) ∧
          HDP.matrixSingularValue (supportColumnRestriction S hS A) 0 ≤ beta := by
  classical
  letI : NeZero s := ⟨hs.ne'⟩
  constructor
  · intro hRIP S hS
    let B := supportColumnRestriction S hS A
    let ulo := HDP.Chapter4.rightSingularBasis B ⟨s - 1, by omega⟩
    let uhi := HDP.Chapter4.rightSingularBasis B ⟨0, hs⟩
    have hloAttain := HDP.Chapter4.singularValue_attained B ⟨s - 1, by omega⟩
    have hhiAttain := HDP.Chapter4.singularValue_attained B ⟨0, hs⟩
    have hloRIP := hRIP (supportCoordinateIsometry S hS ulo)
      (supportCoordinateIsometry_isSparse S hS ulo)
    have hhiRIP := hRIP (supportCoordinateIsometry S hS uhi)
      (supportCoordinateIsometry_isSparse S hS uhi)
    constructor
    · have haction : deterministicMatrixAction A
          (supportCoordinateIsometry S hS ulo) = B.toEuclideanLin ulo := by
        symm
        exact toEuclideanLin_supportColumnRestriction S hS A ulo
      rw [haction, LinearIsometry.norm_map, hloAttain.1, mul_one,
        hloAttain.2] at hloRIP
      exact hloRIP.1
    · have haction : deterministicMatrixAction A
          (supportCoordinateIsometry S hS uhi) = B.toEuclideanLin uhi := by
        symm
        exact toEuclideanLin_supportColumnRestriction S hS A uhi
      rw [haction, LinearIsometry.norm_map, hhiAttain.1, mul_one,
        hhiAttain.2] at hhiRIP
      simpa [B] using hhiRIP.2
  · intro hSV x hx
    have hsn' : s ≤ Fintype.card (Fin n) := by simpa using hsn
    obtain ⟨S, hsuppS, hScard⟩ := Finset.exists_superset_card_eq hx hsn'
    let u := supportCoordinateProjection S hScard x
    let B := supportColumnRestriction S hScard A
    have hxrepr : supportCoordinateIsometry S hScard u = x :=
      supportCoordinateIsometry_projection S hScard x hsuppS
    have hunorm : ‖u‖ = ‖x‖ :=
      supportCoordinateProjection_norm S hScard x hsuppS
    have hextreme := HDP.Chapter4.extremeSingularValues_bound B u
    have hbounds := hSV S hScard
    have haction : B.toEuclideanLin u = deterministicMatrixAction A x := by
      rw [toEuclideanLin_supportColumnRestriction, hxrepr]
      rfl
    constructor
    · rw [← haction, ← hunorm]
      exact (mul_le_mul_of_nonneg_right hbounds.1 (norm_nonneg _)).trans
        hextreme.1
    · rw [← haction, ← hunorm]
      exact hextreme.2.trans
        (mul_le_mul_of_nonneg_right hbounds.2 (norm_nonneg _))

/-- The fixed-support event ruled out by Theorem 4.6.1.

**Lean implementation helper.** -/
def supportRIPBad {m n s : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (S : Finset (Fin n)) (hS : S.card = s) : Set Ω :=
  {omega | 9 / 10 * Real.sqrt m >
        HDP.matrixSingularValue (supportColumnRestriction S hS (A omega)) (s - 1) ∨
      HDP.matrixSingularValue (supportColumnRestriction S hS (A omega)) 0 >
        11 / 10 * Real.sqrt m}

/-- The probability that a fixed support violates restricted isometry satisfies the stated exponential bound.

**Lean implementation helper.** -/
theorem measure_supportRIPBad_le
    [IsProbabilityMeasure μ] {m n s : ℕ} [NeZero m] [NeZero s]
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    (S : Finset (Fin n)) (hS : S.card = s)
    {t : ℝ} (ht : 0 ≤ t)
    (hthreshold : HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
      (Real.sqrt s + t) ≤ Real.sqrt m / 10) :
    μ (supportRIPBad A S hS) ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  let B : Ω → Matrix (Fin m) (Fin s) ℝ :=
    fun omega => supportColumnRestriction S hS (A omega)
  have hBm : HDP.RandomMatrix.AEMeasurableRows B μ :=
    supportColumnRestriction_aemeasurableRows S hS A hrowsm
  have hBs : HDP.RandomMatrix.SubGaussianRows B μ :=
    supportColumnRestriction_subGaussianRows S hS A hsub
  have hBi : HDP.RandomMatrix.IsotropicRows B μ :=
    supportColumnRestriction_isotropicRows S hS A hiso
  have hBind : HDP.RandomMatrix.IndependentRows B μ :=
    supportColumnRestriction_independentRows S hS A hindep
  have hBfinite : HDP.RandomMatrix.RowPsi2Finite B μ :=
    supportColumnRestriction_rowPsi2Finite S hS A hfinite hpsi
  have hBpsi : HDP.RandomMatrix.RowPsi2Bound B μ K :=
    supportColumnRestriction_rowPsi2Bound S hS A hfinite hpsi
  have hsubset : supportRIPBad A S hS ⊆
      {omega | Real.sqrt m - HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
            (Real.sqrt s + t) > HDP.matrixSingularValue (B omega) (s - 1) ∨
        HDP.matrixSingularValue (B omega) 0 >
          Real.sqrt m + HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
            (Real.sqrt s + t)} := by
    intro omega hbad
    rcases hbad with hlo | hhi
    · left
      have hbase : 9 / 10 * Real.sqrt (m : ℝ) ≤
          Real.sqrt m - HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
            (Real.sqrt s + t) := by linarith
      exact lt_of_lt_of_le hlo hbase
    · right
      have hbase : Real.sqrt (m : ℝ) +
          HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
            (Real.sqrt s + t) ≤ 11 / 10 * Real.sqrt m := by linarith
      exact lt_of_le_of_lt hbase hhi
  calc
    μ (supportRIPBad A S hS) ≤ μ {omega |
        Real.sqrt m - HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
              (Real.sqrt s + t) > HDP.matrixSingularValue (B omega) (s - 1) ∨
          HDP.matrixSingularValue (B omega) 0 >
            Real.sqrt m + HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
              (Real.sqrt s + t)} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) :=
      HDP.Chapter4.theorem_4_6_1_singular B hBm hBs hBi hBind hBfinite
        hK hBpsi ht

/-- Event that a random matrix satisfies the source's normalized RIP bounds.

**Lean implementation helper.** -/
def randomRIPEvent {Ω : Type} {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) (s : ℕ) : Set Ω :=
  {ω | IsRestrictedIsometry (A ω) s
    (9 / 10 * Real.sqrt m) (11 / 10 * Real.sqrt m)}

/-- Failure of RIP is covered by the union of the bad singular-value events
over all supports of cardinality `s`.

**Lean implementation helper.** -/
theorem not_randomRIPEvent_subset_iUnion_supportRIPBad
    {m n s : ℕ} (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) :
    (randomRIPEvent A s)ᶜ ⊆
      ⋃ S : ↑((Finset.univ : Finset (Fin n)).powersetCard s),
        supportRIPBad A S.1 (Finset.mem_powersetCard.mp S.2).2 := by
  classical
  intro omega hnot
  by_contra hnoBad
  have hallGood : ∀ S : ↑((Finset.univ : Finset (Fin n)).powersetCard s),
      ¬supportRIPBad A S.1 (Finset.mem_powersetCard.mp S.2).2 omega := by
    intro S hbad
    apply hnoBad
    exact Set.mem_iUnion.mpr ⟨S, hbad⟩
  apply hnot
  apply (rip_iff_supportSingularValues hs hsn (A omega)
    (9 / 10 * Real.sqrt m) (11 / 10 * Real.sqrt m)).2
  intro S hScard
  have hSuniv : S ∈ (Finset.univ : Finset (Fin n)).powersetCard s := by
    exact Finset.mem_powersetCard.mpr ⟨S.subset_univ, hScard⟩
  let Ssub : ↑((Finset.univ : Finset (Fin n)).powersetCard s) := ⟨S, hSuniv⟩
  have hgood := hallGood Ssub
  change ¬(9 / 10 * Real.sqrt (m : ℝ) >
      HDP.matrixSingularValue (supportColumnRestriction S hScard (A omega)) (s - 1) ∨
    HDP.matrixSingularValue (supportColumnRestriction S hScard (A omega)) 0 >
      11 / 10 * Real.sqrt (m : ℝ)) at hgood
  exact ⟨le_of_not_gt (not_or.mp hgood).1,
    le_of_not_gt (not_or.mp hgood).2⟩

/-- The exact fixed-support union bound underlying Book Theorem 9.5.7. The fixed-support singular-value estimate is Theorem 4.6.1. A genuine union
bound over the `choose n s` supports gives the simultaneous RIP event; no
probability conclusion is supplied as a premise.

**Book Theorem 9.5.7.** -/
theorem randomRIP_unionBound
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    {t : ℝ} (ht : 0 ≤ t)
    (hthreshold : HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
      (Real.sqrt s + t) ≤ Real.sqrt m / 10) :
    μ (randomRIPEvent A s)ᶜ ≤
      (Nat.choose n s : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
  classical
  let P := (Finset.univ : Finset (Fin n)).powersetCard s
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero s := ⟨hs.ne'⟩
  have hfixed : ∀ S : ↑P,
      μ (supportRIPBad A S.1 (Finset.mem_powersetCard.mp S.2).2) ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
    intro S
    exact measure_supportRIPBad_le A hrowsm hsub hiso hindep hfinite hK hpsi
      S.1 (Finset.mem_powersetCard.mp S.2).2 ht hthreshold
  calc
    μ (randomRIPEvent A s)ᶜ ≤ μ (⋃ S : ↑P,
        supportRIPBad A S.1 (Finset.mem_powersetCard.mp S.2).2) :=
      measure_mono (not_randomRIPEvent_subset_iUnion_supportRIPBad hs hsn A)
    _ ≤ ∑ S : ↑P,
        μ (supportRIPBad A S.1 (Finset.mem_powersetCard.mp S.2).2) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _S : ↑P, ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
      exact Finset.sum_le_sum fun S hS => hfixed S
    _ = (Nat.choose n s : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
      simp [P, Finset.card_powersetCard]

/-- Threshold form of the random-RIP argument. This is the exact union-bound
helper used to prove the source-facing sample-complexity statement below.

**Lean implementation helper.** -/
theorem randomRIP_of_threshold
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    {u : ℝ} (hu : 0 ≤ u)
    (hthreshold : HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
      (Real.sqrt s +
        Real.sqrt (Real.log (Nat.choose n s) + u ^ 2)) ≤
          Real.sqrt m / 10) :
    μ (randomRIPEvent A s)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  let N : ℝ := Nat.choose n s
  have hchooseNat : 0 < Nat.choose n s := Nat.choose_pos hsn
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hchooseNat
  have hNone : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_iff.mpr hchooseNat)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNone
  let t : ℝ := Real.sqrt (Real.log N + u ^ 2)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htSq : t ^ 2 = Real.log N + u ^ 2 := by
    dsimp [t]
    rw [Real.sq_sqrt (add_nonneg hlog (pow_nonneg hu 2))]
  have hraw := randomRIP_unionBound hm hs hsn A hrowsm hsub hiso hindep
    hfinite hK hpsi ht (by simpa [t, N] using hthreshold)
  calc
    μ (randomRIPEvent A s)ᶜ ≤
        (Nat.choose n s : ℝ≥0∞) *
          ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := hraw
    _ = ENNReal.ofReal
        (N * (2 * Real.exp (-(Real.log N + u ^ 2)))) := by
      rw [htSq]
      simp [N, ENNReal.ofReal_mul (by positivity : 0 ≤ N)]
    _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      congr 1
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hN]
      field_simp [hN.ne']

/-- The elementary entropy estimate used in Theorem 9.5.7:
`choose n s ≤ (e*n/s)^s`. It is extracted from the stronger Chapter 4
binomial partial-sum estimate.

**Book Theorem 9.5.7.** -/
theorem choose_le_exp_mul_div_pow (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) :
    (Nat.choose n s : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s := by
  have hchooseVolume : n.choose s ≤ HDP.Chapter4.hammingBallVolume n s := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    simp
  calc
    (Nat.choose n s : ℝ) ≤
        (HDP.Chapter4.hammingBallVolume n s : ℝ) := by
      exact_mod_cast hchooseVolume
    _ ≤ (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s :=
      HDP.Chapter4.binomialPartialSum_le n s (Nat.succ_le_iff.mpr hs) hsn

/-- Logarithmic form of `choose_le_exp_mul_div_pow`.

**Lean implementation helper.** -/
theorem log_choose_le_mul_log_exp_mul_div (n s : ℕ)
    (hs : 0 < s) (hsn : s ≤ n) :
    Real.log (Nat.choose n s) ≤
      (s : ℝ) * Real.log (Real.exp 1 * (n : ℝ) / (s : ℝ)) := by
  have hchooseNat : 0 < Nat.choose n s := Nat.choose_pos hsn
  have hchoose : (0 : ℝ) < Nat.choose n s := by exact_mod_cast hchooseNat
  have hbound := choose_le_exp_mul_div_pow n s hs hsn
  have hlog := Real.log_le_log hchoose hbound
  rw [Real.log_pow] at hlog
  exact hlog

/-- One explicit universal constant for the sample-size form of Theorem
9.5.7. It is deliberately not optimized.

**Book Theorem 9.5.7.** -/
def randomRIPSampleConstant : ℝ :=
  400 * HDP.Chapter4.twoSidedSingularConstant ^ 2

/-- The random restricted isometry sample constant is strictly positive.

**Lean implementation helper.** -/
theorem randomRIPSampleConstant_pos : 0 < randomRIPSampleConstant := by
  dsimp [randomRIPSampleConstant]
  positivity [HDP.Chapter4.twoSidedSingularConstant_pos]

/-- A subgaussian random matrix satisfies RIP above the `s log(en/s)` sample scale. This is the source-facing formulation. The explicit absolute constant
`randomRIPSampleConstant` witnesses the book's universal `C` in
`m ≥ C K⁴ (s log(e*n/s) + u²)`. The proof combines the fixed-support
singular-value theorem, the union bound over all supports, and the standard
binomial entropy estimate above.

**Book Theorem 9.5.7.** -/
theorem theorem_9_5_7_randomRIP
    [IsProbabilityMeasure μ] {m n s : ℕ} (hm : 0 < m)
    (hs : 0 < s) (hsn : s ≤ n)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (hrowsm : A.MeasurableRows)
    (hsub : A.SubGaussianRows μ)
    (hiso : A.IsotropicRows μ)
    (hindep : A.IndependentRows μ)
    (hfinite : A.RowPsi2Finite μ)
    {K : ℝ} (hK : 0 < K) (hpsi : A.RowPsi2Bound μ K)
    {u : ℝ} (hu : 0 ≤ u)
    (hsize : randomRIPSampleConstant * K ^ 4 *
      ((s : ℝ) * Real.log
          (Real.exp 1 * (n : ℝ) / (s : ℝ)) + u ^ 2) ≤
        (m : ℝ)) :
    μ (randomRIPEvent A s)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  let C₀ : ℝ := HDP.Chapter4.twoSidedSingularConstant
  let L : ℝ := Real.log (Real.exp 1 * (n : ℝ) / (s : ℝ))
  let R : ℝ := (s : ℝ) * L + u ^ 2
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hs.trans_le hsn
  have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hratio : Real.exp 1 ≤
      Real.exp 1 * (n : ℝ) / (s : ℝ) := by
    rw [le_div_iff₀ hsR]
    exact mul_le_mul_of_nonneg_left hsnR (Real.exp_pos 1).le
  have hLone : 1 ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hratio
    simpa [L] using hlog
  have hLzero : 0 ≤ L := le_trans (by norm_num) hLone
  have hlogChoose : Real.log (Nat.choose n s) ≤ (s : ℝ) * L := by
    simpa [L] using log_choose_le_mul_log_exp_mul_div n s hs hsn
  have hchooseNat : 0 < Nat.choose n s := Nat.choose_pos hsn
  have hlogChooseZero : 0 ≤ Real.log (Nat.choose n s) :=
    Real.log_nonneg (by exact_mod_cast hchooseNat)
  have hRzero : 0 ≤ R := by
    dsimp [R]
    positivity
  have hsLeR : (s : ℝ) ≤ R := by
    dsimp [R]
    have hscale : (s : ℝ) ≤ (s : ℝ) * L := by
      nlinarith
    nlinarith [sq_nonneg u]
  have hlogLeR : Real.log (Nat.choose n s) + u ^ 2 ≤ R := by
    dsimp [R]
    linarith
  have hsqrtSSq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) :=
    Real.sq_sqrt hsR.le
  have hsqrtLogSq :
      Real.sqrt (Real.log (Nat.choose n s) + u ^ 2) ^ 2 =
        Real.log (Nat.choose n s) + u ^ 2 :=
    Real.sq_sqrt (add_nonneg hlogChooseZero (sq_nonneg u))
  have hsumSq :
      (Real.sqrt (s : ℝ) +
          Real.sqrt (Real.log (Nat.choose n s) + u ^ 2)) ^ 2 ≤
        4 * R := by
    have ha := Real.sqrt_nonneg (s : ℝ)
    have hb := Real.sqrt_nonneg
      (Real.log (Nat.choose n s) + u ^ 2)
    nlinarith [sq_nonneg
      (Real.sqrt (s : ℝ) -
        Real.sqrt (Real.log (Nat.choose n s) + u ^ 2))]
  have hC₀ : 0 < C₀ := by
    exact HDP.Chapter4.twoSidedSingularConstant_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hleft : 0 ≤ 10 * C₀ * K ^ 2 *
      (Real.sqrt (s : ℝ) +
        Real.sqrt (Real.log (Nat.choose n s) + u ^ 2)) := by
    positivity
  have hsquare :
      (10 * C₀ * K ^ 2 *
        (Real.sqrt (s : ℝ) +
          Real.sqrt (Real.log (Nat.choose n s) + u ^ 2))) ^ 2 ≤
        Real.sqrt (m : ℝ) ^ 2 := by
    rw [Real.sq_sqrt hmR.le]
    calc
      (10 * C₀ * K ^ 2 *
          (Real.sqrt (s : ℝ) +
            Real.sqrt (Real.log (Nat.choose n s) + u ^ 2))) ^ 2 =
          100 * C₀ ^ 2 * K ^ 4 *
            (Real.sqrt (s : ℝ) +
              Real.sqrt (Real.log (Nat.choose n s) + u ^ 2)) ^ 2 := by ring
      _ ≤ 100 * C₀ ^ 2 * K ^ 4 * (4 * R) :=
        mul_le_mul_of_nonneg_left hsumSq (by positivity)
      _ = randomRIPSampleConstant * K ^ 4 * R := by
        simp [randomRIPSampleConstant, C₀]
        ring
      _ ≤ (m : ℝ) := by simpa [R, L] using hsize
  have hlinear := (sq_le_sq₀ hleft (Real.sqrt_nonneg (m : ℝ))).mp hsquare
  have hthreshold : HDP.Chapter4.twoSidedSingularConstant * K ^ 2 *
      (Real.sqrt s +
        Real.sqrt (Real.log (Nat.choose n s) + u ^ 2)) ≤
          Real.sqrt m / 10 := by
    dsimp [C₀] at hlinear
    nlinarith
  exact randomRIP_of_threshold hm hs hsn A hrowsm hsub hiso hindep
    hfinite hK hpsi hu hthreshold

end

end HDP.Chapter9

end Source_14_RestrictedIsometry

/-! ## Material formerly in `15_SublinearFunctionals.lean` -/

section Source_15_SublinearFunctionals

/-!
# Book Chapter 9, §9.6: sublinear functionals

The source calls a real-valued functional “bounded”.  Literal boundedness is
incompatible with nonzero positive homogeneity.  The hypothesis actually used
in the proof is the Euclidean growth estimate `f z ≤ b * ‖z‖`; it is recorded
explicitly below.

Positive homogeneity is only required for nonnegative scalars, exactly as in
Definition 9.6.1.  No continuity is silently bundled into the definition.
-/

open InnerProductSpace
open scoped Pointwise RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

/-- A sublinear functional is positive-homogeneous and subadditive and may take negative values. Positive homogeneity for nonnegative scalars.

**Book Definition 9.6.1.** -/
def IsPositivelyHomogeneous {E : Type*} [SMul ℝ E]
    (f : E → ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∀ x, f (c • x) = c * f x

/-- A sublinear functional is positive-homogeneous and subadditive and may take negative values. Subadditivity.

**Book Definition 9.6.1.** -/
def IsSubadditive {E : Type*} [Add E] (f : E → ℝ) : Prop :=
  ∀ x y, f (x + y) ≤ f x + f y

/-- The two algebraic conditions in Definition 9.6.1, bundled for reuse. -/
structure SublinearFunctional (E : Type*) [Add E] [SMul ℝ E] where
  toFun : E → ℝ
  positivelyHomogeneous : IsPositivelyHomogeneous toFun
  subadditive : IsSubadditive toFun

instance {E : Type*} [Add E] [SMul ℝ E] :
    CoeFun (SublinearFunctional E) (fun _ => E → ℝ) :=
  ⟨SublinearFunctional.toFun⟩

/-- Sublinear functional has Euclidean linear growth `f(x) <= b ‖x‖`. Corrected growth hypothesis replacing the impossible literal boundedness
of a nonzero positively homogeneous functional.

**Book Equation (9.36).** -/
def HasEuclideanGrowth {E : Type*} [Norm E]
    (f : E → ℝ) (b : ℝ) : Prop :=
  ∀ z, f z ≤ b * ‖z‖

/-- Every sublinear functional maps the zero vector to zero.

**Lean implementation helper.** -/
theorem SublinearFunctional.map_zero {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (f : SublinearFunctional E) :
    f 0 = 0 := by
  have h := f.positivelyHomogeneous 0 (le_refl 0) (0 : E)
  simpa using h

/-- Subadditivity implies `f(x)-f(y)<=f(x-y)`. Subadditivity controls a
one-sided increment by the functional of the difference.

**Book Exercise 9.34.** -/
theorem exercise_9_34_subadditive_difference {E : Type*}
    [AddCommGroup E] (f : E → ℝ) (hf : IsSubadditive f) (x y : E) :
    f x - f y ≤ f (x - y) := by
  have h := hf (x - y) y
  rw [sub_add_cancel] at h
  linarith

/-- The same result through the bundled interface.

**Lean implementation helper.** -/
theorem SublinearFunctional.sub_difference {E : Type*}
    [AddCommGroup E] [SMul ℝ E] (f : SublinearFunctional E) (x y : E) :
    f x - f y ≤ f (x - y) :=
  exercise_9_34_subadditive_difference f f.subadditive x y

/-- A subadditive functional with Euclidean growth is Lipschitz. Notice that
the one-sided growth assumption suffices, since it is applied to both
`x - y` and `y - x`.

**Lean implementation helper.** -/
theorem abs_sub_le_of_subadditive_growth {E : Type*}
    [SeminormedAddCommGroup E] (f : E → ℝ) {b : ℝ}
    (hsub : IsSubadditive f) (hgrowth : HasEuclideanGrowth f b)
    (x y : E) :
    |f x - f y| ≤ b * ‖x - y‖ := by
  rw [abs_le]
  constructor
  · have hdiff := exercise_9_34_subadditive_difference f hsub y x
    have hg := hgrowth (y - x)
    rw [norm_sub_rev] at hg
    linarith
  · exact (exercise_9_34_subadditive_difference f hsub x y).trans
      (hgrowth (x - y))

/-- A sublinear functional with Euclidean growth is Lipschitz. The growth estimate turns a sublinear functional into a genuinely
Lipschitz map. This is the analytic interface used by Gaussian
concentration in Theorem 9.6.4.

**Book Section 9.6.4.** -/
theorem SublinearFunctional.lipschitzWith_of_growth {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SublinearFunctional E) {b : ℝ} (hb : 0 ≤ b)
    (hgrowth : HasEuclideanGrowth f b) :
    LipschitzWith (NNReal.mk b hb) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using
    abs_sub_le_of_subadditive_growth f f.subadditive hgrowth x y

/-- A sublinear functional with a global linear growth bound is continuous.

**Lean implementation helper.** -/
theorem SublinearFunctional.continuous_of_growth {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SublinearFunctional E) {b : ℝ} (hb : 0 ≤ b)
    (hgrowth : HasEuclideanGrowth f b) : Continuous f :=
  (f.lipschitzWith_of_growth hb hgrowth).continuous

/-! ## Examples 9.6.2 -/

/-- A norm is positively homogeneous.

**Lean implementation helper.** -/
theorem norm_isPositivelyHomogeneous {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    IsPositivelyHomogeneous (fun x : E => ‖x‖) := by
  intro c hc x
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

/-- A norm is subadditive.

**Lean implementation helper.** -/
theorem norm_isSubadditive {E : Type*} [SeminormedAddCommGroup E] :
    IsSubadditive (fun x : E => ‖x‖) :=
  fun x y => norm_add_le x y

/-- The ambient norm has the required linear growth relative to the Euclidean norm.

**Lean implementation helper.** -/
theorem norm_hasEuclideanGrowth {E : Type*} [SeminormedAddCommGroup E] :
    HasEuclideanGrowth (fun x : E => ‖x‖) 1 := by
  intro x
  simp

/-- Every real linear functional is sublinear.
No continuity or finite-dimensionality is needed for this algebraic example.

**Book Example 9.6.2(b).** -/
def linearMapSublinearFunctional {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (L : E →ₗ[ℝ] ℝ) :
    SublinearFunctional E where
  toFun := L
  positivelyHomogeneous := by
    intro c hc x
    simp
  subadditive := by
    intro x y
    rw [map_add]

/-- Norms, linear functionals, inner products, and support functions are sublinear examples. A fixed inner product is a sublinear functional (indeed, a linear one).

**Book Example 9.6.2.** -/
def innerSublinearFunctional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E) :
    SublinearFunctional E where
  toFun := fun z => inner ℝ z u
  positivelyHomogeneous := by
    intro c hc z
    simp [inner_smul_left]
  subadditive := by
    intro x y
    change inner ℝ (x + y) u ≤ inner ℝ x u + inner ℝ y u
    rw [inner_add_left]

/-- A fixed inner-product functional grows at most linearly with Euclidean norm.

**Lean implementation helper.** -/
theorem inner_hasEuclideanGrowth {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E) :
    HasEuclideanGrowth (fun z => inner ℝ z u) ‖u‖ := by
  intro z
  simpa [mul_comm] using real_inner_le_norm z u

/-! ### Example 9.6.2(d): support functions of arbitrary bounded sets -/

/-- Norms, linear functionals, inner products, and support functions are sublinear examples. The support functional of a set in a real inner-product space. Its
source-facing algebraic and growth properties below assume that the set is
nonempty and bounded, so this real supremum is finite.

**Book Example 9.6.2.** -/
def setSupportFunctional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (z : E) : ℝ :=
  sSup ((fun x => inner ℝ z x) '' S)

/-- The outer radius `sup {‖x‖ | x ∈ S}` of a set. For the source-facing
application the set is nonempty and bounded.

**Lean implementation helper.** -/
def setSupportRadius {E : Type*} [NormedAddCommGroup E]
    (S : Set E) : ℝ :=
  sSup (norm '' S)

/-- Boundedness of the scalar support values of a bounded set.

**Lean implementation helper.** -/
theorem setSupportFunctional_bddAbove {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (hSb : Bornology.IsBounded S) (z : E) :
    BddAbove ((fun x => inner ℝ z x) '' S) := by
  let L : E →L[ℝ] ℝ := innerSL ℝ z
  have hb : Bornology.IsBounded (L '' S) :=
    Bornology.IsBounded.image L hSb
  simpa [L] using hb.bddAbove

/-- A bounded set has a finite outer radius.

**Lean implementation helper.** -/
theorem setSupportRadius_bddAbove {E : Type*} [NormedAddCommGroup E]
    (S : Set E) (hSb : Bornology.IsBounded S) :
    BddAbove (norm '' S) := by
  obtain ⟨C, hC⟩ := hSb.exists_norm_le
  exact ⟨C, by
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx⟩

/-- Every point of a bounded set has norm at most its outer radius.

**Lean implementation helper.** -/
theorem norm_le_setSupportRadius {E : Type*} [NormedAddCommGroup E]
    (S : Set E) (hSb : Bornology.IsBounded S)
    {x : E} (hx : x ∈ S) :
    ‖x‖ ≤ setSupportRadius S := by
  exact le_csSup (setSupportRadius_bddAbove S hSb) ⟨x, hx, rfl⟩

/-- The outer radius of a nonempty bounded set is nonnegative.

**Lean implementation helper.** -/
theorem setSupportRadius_nonneg {E : Type*} [NormedAddCommGroup E]
    (S : Set E) (hS : S.Nonempty) (hSb : Bornology.IsBounded S) :
    0 ≤ setSupportRadius S := by
  obtain ⟨x, hx⟩ := hS
  exact (norm_nonneg x).trans (norm_le_setSupportRadius S hSb hx)

/-- The covariance ellipsoid generated by a rectangular matrix: the image of the
Euclidean unit ball under its transpose.

**Book Section 9.2.3.** -/
def covarianceEllipsoid {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ) :
    Set (EuclideanSpace ℝ (Fin r)) :=
  B.transpose.toEuclideanLin ''
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The outer radius of the covariance ellipsoid is exactly the operator norm
of its generating matrix.

**Book Section 9.2.3.** -/
theorem covarianceEllipsoid_radius {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (B : Matrix (Fin n) (Fin r) ℝ) :
    setSupportRadius (covarianceEllipsoid B) = HDP.matrixOpNorm B := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hne : (covarianceEllipsoid B).Nonempty := by
    refine ⟨0, 0, ?_, ?_⟩
    · simp
    · simp
  have hb : Bornology.IsBounded (covarianceEllipsoid B) := by
    simpa [covarianceEllipsoid] using
      (Bornology.IsBounded.image B.transpose.toEuclideanLin.toContinuousLinearMap
        (Metric.isBounded_closedBall : Bornology.IsBounded
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
  apply le_antisymm
  · unfold setSupportRadius
    apply csSup_le
    · exact hne.image norm
    · rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      calc
        ‖B.transpose.toEuclideanLin x‖ ≤
            HDP.matrixOpNorm B.transpose * ‖x‖ :=
          HDP.Chapter4.matrixOpNorm_apply_le B.transpose x
        _ ≤ HDP.matrixOpNorm B.transpose * 1 := by
          exact mul_le_mul_of_nonneg_left hx
            (HDP.matrixOpNorm_nonneg B.transpose)
        _ = HDP.matrixOpNorm B := by simp
  · have hgreat := (HDP.Chapter4.definition_4_1_8 B.transpose).2.2.1
    rcases hgreat.1 with ⟨x, hxnorm, hxval⟩
    have hxball : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right, hxnorm]
    have hy : B.transpose.toEuclideanLin x ∈ covarianceEllipsoid B :=
      ⟨x, hxball, rfl⟩
    have hle := norm_le_setSupportRadius (covarianceEllipsoid B) hb hy
    rw [← hxval, HDP.matrixOpNorm_transpose] at hle
    exact hle

/-- Every nonempty finite subfamily of a covariance ellipsoid has Gaussian
complexity at most the Frobenius norm of the defining factor.

**Lean implementation helper.** -/
theorem finiteGaussianComplexity_le_frobenius_of_subset_covarianceEllipsoid
    {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ)
    (F : Finset (EuclideanSpace ℝ (Fin r))) (hF : F.Nonempty)
    (hFE : (F : Set (EuclideanSpace ℝ (Fin r))) ⊆
      covarianceEllipsoid B) :
    HDP.Chapter7.gaussianComplexity F ≤
      HDP.matrixFrobeniusNorm B := by
  have hpoint (g : EuclideanSpace ℝ (Fin r)) :
      HDP.Chapter7.finiteGaussianAbsSupport F g ≤
        ‖B.toEuclideanLin g‖ := by
    rw [HDP.Chapter7.finiteGaussianAbsSupport_eq_sup' F hF]
    apply Finset.sup'_le
    intro y hy
    rcases hFE hy with ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hadj :
        inner ℝ g (B.transpose.toEuclideanLin x) =
          inner ℝ (B.toEuclideanLin g) x := by
      rw [← LinearMap.adjoint_inner_left]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hadj]
    calc
      |inner ℝ (B.toEuclideanLin g) x| ≤
          ‖B.toEuclideanLin g‖ * ‖x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖B.toEuclideanLin g‖ * 1 :=
        mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _)
      _ = ‖B.toEuclideanLin g‖ := mul_one _
  have hleftInt : MeasureTheory.Integrable
      (fun g : EuclideanSpace ℝ (Fin r) =>
        HDP.Chapter7.finiteGaussianAbsSupport F g ^ 2)
      (ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ (Fin r))) :=
    (HDP.Chapter7.memLp_two_finiteGaussianAbsSupport F).integrable_sq
  have hrightMem :
      MeasureTheory.MemLp (fun g : EuclideanSpace ℝ (Fin r) =>
        B.toEuclideanLin g) 2
        (ProbabilityTheory.stdGaussian
          (EuclideanSpace ℝ (Fin r))) := by
    have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
      MeasureTheory.MemLp
        (id : EuclideanSpace ℝ (Fin r) →
        EuclideanSpace ℝ (Fin r)) 2
        (ProbabilityTheory.stdGaussian
          (EuclideanSpace ℝ (Fin r)))).continuousLinearMap_comp
          B.toEuclideanLin.toContinuousLinearMap
    simpa [Function.comp_def] using h
  have hrightInt : MeasureTheory.Integrable
      (fun g : EuclideanSpace ℝ (Fin r) =>
        ‖B.toEuclideanLin g‖ ^ 2)
      (ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ (Fin r))) :=
    hrightMem.integrable_norm_pow' (p := 2)
  have hsecond :
      (∫ g : EuclideanSpace ℝ (Fin r),
          HDP.Chapter7.finiteGaussianAbsSupport F g ^ 2
          ∂ProbabilityTheory.stdGaussian
            (EuclideanSpace ℝ (Fin r))) ≤
        HDP.matrixFrobeniusNorm B ^ 2 := by
    rw [← integral_norm_matrix_stdGaussian B]
    exact MeasureTheory.integral_mono hleftInt hrightInt fun g =>
      (sq_le_sq₀
        (HDP.Chapter7.finiteGaussianAbsSupport_nonneg F g)
        (norm_nonneg _)).2 (hpoint g)
  calc
    HDP.Chapter7.gaussianComplexity F ≤
        HDP.Chapter7.gaussianL2Width F :=
      HDP.Chapter7.gaussianComplexity_le_gaussianL2Width F
    _ ≤ Real.sqrt (HDP.matrixFrobeniusNorm B ^ 2) :=
      Real.sqrt_le_sqrt hsecond
    _ = HDP.matrixFrobeniusNorm B :=
      Real.sqrt_sq (HDP.matrixFrobeniusNorm_nonneg B)

/-- The actual covariance ellipsoid has Gaussian complexity at most the
Frobenius norm of its defining factor.  The extended finite-subfamily envelope
is the authoritative arbitrary-set interface, so the statement does not hide
an uncountable-supremum measurability assumption.

For `Σ = BᵀB`, the right side is `√(tr Σ)`.

**Book Section 9.2.3.** -/
theorem covarianceEllipsoid_gaussianComplexityEnvelope_le
    {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ) :
    gaussianComplexityEnvelope (covarianceEllipsoid B) ≤
      ENNReal.ofReal (HDP.matrixFrobeniusNorm B) := by
  unfold gaussianComplexityEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFE
  apply iSup_le
  intro hF
  exact ENNReal.ofReal_le_ofReal
    (finiteGaussianComplexity_le_frobenius_of_subset_covarianceEllipsoid
      B F hF hFE)

/-- Safe real form of the covariance-ellipsoid Gaussian-complexity bound.

**Book Section 9.2.3.** -/
theorem covarianceEllipsoid_gaussianComplexityEnvelope_toReal_le
    {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℝ) :
    (gaussianComplexityEnvelope (covarianceEllipsoid B)).toReal ≤
      HDP.matrixFrobeniusNorm B := by
  have h := covarianceEllipsoid_gaussianComplexityEnvelope_le B
  have htop :
      ENNReal.ofReal (HDP.matrixFrobeniusNorm B) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop h
  simpa [ENNReal.toReal_ofReal (HDP.matrixFrobeniusNorm_nonneg B)] using
    hreal

/-- The support
functional of any set is positively homogeneous for nonnegative scalars.

**Book Example 9.6.2(d).** -/
theorem setSupportFunctional_posHom {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) :
    IsPositivelyHomogeneous (setSupportFunctional S) := by
  intro c hc z
  change sSup ((fun x => inner ℝ (c • z) x) '' S) =
    c * sSup ((fun x => inner ℝ z x) '' S)
  have hset : ((fun x => inner ℝ (c • z) x) '' S) =
      c • ((fun x => inner ℝ z x) '' S) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_smul_set]
      exact ⟨inner ℝ z x, ⟨x, hx, rfl⟩, by
        simp [inner_smul_left]⟩
    · rw [Set.mem_smul_set]
      rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [inner_smul_left]⟩
  rw [hset, Real.sSup_smul_of_nonneg hc]
  rfl

/-- The support functional of
a nonempty bounded set is subadditive.

**Book Example 9.6.2(d).** -/
theorem setSupportFunctional_subadditive {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSb : Bornology.IsBounded S) :
    IsSubadditive (setSupportFunctional S) := by
  intro x y
  change sSup ((fun z => inner ℝ (x + y) z) '' S) ≤
    sSup ((fun z => inner ℝ x z) '' S) +
      sSup ((fun z => inner ℝ y z) '' S)
  apply csSup_le (hS.image (fun z => inner ℝ (x + y) z))
  rintro _ ⟨z, hz, rfl⟩
  change inner ℝ (x + y) z ≤ _
  rw [inner_add_left]
  exact add_le_add
    (le_csSup (setSupportFunctional_bddAbove S hSb x) ⟨z, hz, rfl⟩)
    (le_csSup (setSupportFunctional_bddAbove S hSb y) ⟨z, hz, rfl⟩)

/-- Support functional grows at most as `rad(S) ‖x‖`. For every
nonempty bounded `S`, its support functional obeys the exact Euclidean growth
bound with coefficient `sup {‖x‖ | x ∈ S}`.

**Book Equation (9.43).** -/
theorem setSupportFunctional_growth {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSb : Bornology.IsBounded S) :
    HasEuclideanGrowth (setSupportFunctional S) (setSupportRadius S) := by
  intro z
  change sSup ((fun x => inner ℝ z x) '' S) ≤ setSupportRadius S * ‖z‖
  apply csSup_le (hS.image (fun x => inner ℝ z x))
  rintro _ ⟨x, hx, rfl⟩
  calc
    inner ℝ z x ≤ ‖z‖ * ‖x‖ := real_inner_le_norm z x
    _ ≤ ‖z‖ * setSupportRadius S :=
      mul_le_mul_of_nonneg_left
        (norm_le_setSupportRadius S hSb hx) (norm_nonneg z)
    _ = setSupportRadius S * ‖z‖ := mul_comm _ _

/-- Norms, linear functionals, inner products, and support functions are sublinear examples.

**Book Example 9.6.2.** -/
def setSupportSublinearFunctional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSb : Bornology.IsBounded S) :
    SublinearFunctional E where
  toFun := setSupportFunctional S
  positivelyHomogeneous := setSupportFunctional_posHom S
  subadditive := setSupportFunctional_subadditive S hS hSb

/-- Compatibility helper for the finite support function used in §9.7. The
ambient variable belongs to `ℝ^m`; this records the dimension correction to
display (9.36). `setSupportFunctional` is the authoritative arbitrary-set
interface for Example 9.6.2(d).

**Book Equation (9.36).** -/
def finiteSupportFunctional {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) → ℝ :=
  HDP.Chapter7.finiteGaussianSupport S

/-- The support functional of a finite set is positively homogeneous.

**Lean implementation helper.** -/
theorem finiteSupportFunctional_posHom {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty) :
    IsPositivelyHomogeneous (finiteSupportFunctional S) := by
  intro c hc z
  exact HDP.Chapter7.finiteGaussianSupport_smul_left S hS hc z

/-- The support functional of a finite set is subadditive.

**Lean implementation helper.** -/
theorem finiteSupportFunctional_subadditive {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty) :
    IsSubadditive (finiteSupportFunctional S) := by
  intro x y
  simp only [finiteSupportFunctional,
    HDP.Chapter7.finiteGaussianSupport_eq_sup' S hS]
  apply Finset.sup'_le
  intro z hz
  rw [inner_add_left]
  exact add_le_add
    (Finset.le_sup' (fun q => inner ℝ x q) hz)
    (Finset.le_sup' (fun q => inner ℝ y q) hz)

/-- A finite support function grows at most by the outer radius of its set.

**Lean implementation helper.** -/
theorem finiteSupportFunctional_growth {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty) :
    HasEuclideanGrowth (finiteSupportFunctional S)
      (HDP.Chapter7.finiteRadius S) := by
  intro x
  rw [finiteSupportFunctional,
    HDP.Chapter7.finiteGaussianSupport_eq_sup' S hS]
  apply Finset.sup'_le
  intro z hz
  calc
    inner ℝ x z ≤ ‖x‖ * ‖z‖ := real_inner_le_norm x z
    _ ≤ ‖x‖ * HDP.Chapter7.finiteRadius S :=
      mul_le_mul_of_nonneg_left
        (HDP.Chapter7.norm_le_finiteRadius S hS hz) (norm_nonneg x)
    _ = HDP.Chapter7.finiteRadius S * ‖x‖ := mul_comm _ _

/-- Bundled finite support functional.

**Lean implementation helper.** -/
def finiteSupportSublinearFunctional {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty) :
    SublinearFunctional (EuclideanSpace ℝ (Fin m)) where
  toFun := finiteSupportFunctional S
  positivelyHomogeneous := finiteSupportFunctional_posHom S hS
  subadditive := finiteSupportFunctional_subadditive S hS

/-- The finite compatibility helper agrees exactly with the arbitrary-set
support functional on the coercion of a nonempty finset.

**Lean implementation helper.** -/
theorem finiteSupportFunctional_eq_setSupportFunctional {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty)
    (z : EuclideanSpace ℝ (Fin m)) :
    finiteSupportFunctional S z = setSupportFunctional (S : Set _) z := by
  rw [finiteSupportFunctional,
    HDP.Chapter7.finiteGaussianSupport_eq_sup' S hS,
    Finset.sup'_eq_csSup_image]
  rfl

/-- The finite-radius compatibility helper is the arbitrary-set radius of the
coerced nonempty finset.

**Lean implementation helper.** -/
theorem finiteRadius_eq_setSupportRadius {m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty) :
    HDP.Chapter7.finiteRadius S =
      setSupportRadius
        (E := EuclideanSpace ℝ (Fin m))
        (S : Set (EuclideanSpace ℝ (Fin m))) := by
  rw [HDP.Chapter7.finiteRadius_eq_sup' S hS,
    Finset.sup'_eq_csSup_image]
  rfl

/-! ### Remark 9.6.5

The extension of Theorem 9.6.3 from Gaussian matrices to general subgaussian
matrices is stated in the source as an open problem.  It is therefore recorded
only as mathematical provenance here, rather than encoded as a Lean theorem or
as an external postulate.
-/

end

end HDP.Chapter9

end Source_15_SublinearFunctionals

/-! ## Material formerly in `16_GeneralMatrixDeviation.lean` -/

section Source_16_GeneralMatrixDeviation

/-!
# Book Chapter 9, §9.6: the general matrix deviation theorem

This file reconstructs the conditional-Gaussian proof of Theorem 9.6.4 for
Mathlib's canonical product measure `HDP.stdGaussianMatrixMeasure`.  In
particular, the increment estimate is a theorem, not a caller-supplied
certificate.  The proof follows the source: split two unit vectors into
orthogonal half-sum and half-difference, use independence, apply Gaussian
concentration conditionally, and then perform the radial extension from
§9.1.
-/

open InnerProductSpace MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

/-- Centered functional-deviation process `f(Ax)-E f(Ax)`. Centered process (9.37) under the canonical standard Gaussian matrix.

**Book Equation (9.37).** -/
def functionalDeviationProcess {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  f (HDP.gaussianMatrixAction A x) -
    ∫ B, f (HDP.gaussianMatrixAction B x)
      ∂HDP.stdGaussianMatrixMeasure m n

/-- Exact fixed-direction mean. This is display (9.44) for an arbitrary
sublinear functional.

**Book Equation (9.44).** -/
theorem integral_functional_gaussianMatrixAction_eq {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ A, f (HDP.gaussianMatrixAction A x)
        ∂HDP.stdGaussianMatrixMeasure m n) =
      ‖x‖ * ∫ g, f g ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  have hfm := (f.continuous_of_growth hb hgrowth).measurable
  have hlaw := (HDP.gaussianMatrixAction_hasLaw_scaledStdGaussian m n x).integral_comp
    hfm.aestronglyMeasurable
  rw [HDP.scaledStdGaussianMeasure,
    integral_map (by fun_prop) hfm.aestronglyMeasurable] at hlaw
  simpa only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    f.positivelyHomogeneous ‖x‖ (norm_nonneg x), integral_const_mul] using hlaw

/-- Coordinate realization of a finite standard Gaussian vector.

**Lean implementation helper.** -/
private theorem hasLaw_gaussianPi_to_stdGaussian (m : ℕ) :
    HasLaw (WithLp.toLp 2)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (HDP.Chapter5.gaussianPiMeasure m) := by
  refine ⟨(WithLp.measurable_toLp 2 (Fin m → ℝ)).aemeasurable, ?_⟩
  exact map_pi_eq_stdGaussian

/-- Gaussian concentration transported from the coordinate product measure
to Mathlib's intrinsic standard Gaussian measure.

**Lean implementation helper.** -/
private theorem stdGaussian_lipschitz_hasSubgaussianMGF {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) {K : ℝ} (hK : 0 < K)
    (hF : LipschitzWith ⟨K, hK.le⟩ F) :
    HasSubgaussianMGF
      (fun z ↦ F z - ∫ q, F q ∂stdGaussian (EuclideanSpace ℝ (Fin m)))
      ⟨K ^ 2, sq_nonneg K⟩
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  let γ := HDP.Chapter5.gaussianPiMeasure m
  let G : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun z ↦ F z - ∫ q, F q ∂stdGaussian (EuclideanSpace ℝ (Fin m))
  have hraw := HDP.Chapter5.gaussian_lipschitz_hasSubgaussianMGF
    m F K hK hF
  have hmean := (hasLaw_gaussianPi_to_stdGaussian m).integral_comp
    hF.continuous.measurable.aestronglyMeasurable
  have heq : HDP.Chapter5.gaussianCentered F =
      G ∘ WithLp.toLp 2 := by
    funext z
    simp only [HDP.Chapter5.gaussianCentered, G, Function.comp_apply]
    rw [show (∫ y, F (WithLp.toLp 2 y) ∂γ) =
        ∫ q, F q ∂stdGaussian (EuclideanSpace ℝ (Fin m)) by
      simpa only [Function.comp_apply] using hmean]
  have hcoord : HasSubgaussianMGF (G ∘ WithLp.toLp 2)
      ⟨K ^ 2, sq_nonneg K⟩ γ := by
    rw [← heq]
    exact hraw
  have hbase : IdentDistrib (WithLp.toLp 2)
      (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
      γ (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    (hasLaw_gaussianPi_to_stdGaussian m).identDistrib HasLaw.id
  have hGm : Measurable G := by
    exact hF.continuous.measurable.sub_const _
  have hident := hbase.comp hGm
  simpa [Function.comp_def, G] using hcoord.congr_identDistrib hident

/-- A centered Gaussian bound may be integrated over an independent outer
parameter when its MGF proxy is uniform in that parameter.

**Lean implementation helper.** -/
private theorem hasSubgaussianMGF_prod_of_forall
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure E) (Q : Measure F) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (H : E × F → ℝ) (hH : Measurable H)
    (c : ℝ≥0) (h : ∀ a, HasSubgaussianMGF (fun z ↦ H (a, z)) c Q) :
    HasSubgaussianMGF H c (P.prod Q) := by
  have hint : ∀ t : ℝ, Integrable (fun p ↦ Real.exp (t * H p)) (P.prod Q) := by
    intro t
    let W : E × F → ℝ := fun p ↦ Real.exp (t * H p)
    have hWm : AEStronglyMeasurable W (P.prod Q) :=
      (Real.measurable_exp.comp
        (measurable_const.mul hH)).aestronglyMeasurable
    apply (integrable_prod_iff hWm).2
    constructor
    · filter_upwards [] with a
      simpa [W] using (h a).integrable_exp_mul t
    · have hm : AEStronglyMeasurable
          (fun a ↦ ∫ z, ‖W (a, z)‖ ∂Q) P :=
        hWm.norm.integral_prod_right'
      refine Integrable.mono (integrable_const
        (Real.exp ((c : ℝ) * t ^ 2 / 2))) hm ?_
      filter_upwards [] with a
      have hnonneg : 0 ≤ ∫ y, Real.exp (t * H (a, y)) ∂Q :=
        integral_nonneg fun _ ↦ Real.exp_nonneg _
      simpa [W, Real.norm_eq_abs, abs_of_nonneg hnonneg, mgf] using
        (h a).mgf_le t
  constructor
  · exact hint
  · intro t
    rw [mgf, integral_prod _ (hint t)]
    have houter : Integrable
        (fun a ↦ ∫ z, Real.exp (t * H (a, z)) ∂Q) P :=
      (hint t).integral_prod_left
    calc
      (∫ a, ∫ z, Real.exp (t * H (a, z)) ∂Q ∂P) ≤
          ∫ _ : E, Real.exp ((c : ℝ) * t ^ 2 / 2) ∂P := by
        apply integral_mono houter (integrable_const _)
        intro a
        exact (h a).mgf_le t
      _ = Real.exp ((c : ℝ) * t ^ 2 / 2) := by simp

/-- The integral of an odd observable under a standard Gaussian is zero.

**Lean implementation helper.** -/
private theorem integral_odd_stdGaussian_eq_zero {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Integrable F (stdGaussian (EuclideanSpace ℝ (Fin m))))
    (hodd : ∀ z, F (-z) = -F z) :
    (∫ z, F z ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0 := by
  let U : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin m) := LinearIsometryEquiv.neg ℝ
  have hrot := HDP.Chapter3.standardGaussian_rotation_invariant U
  have hFmap : AEStronglyMeasurable F
      ((stdGaussian (EuclideanSpace ℝ (Fin m))).map U) := by
    rw [hrot]
    exact hF.aestronglyMeasurable
  have hi := integral_map U.continuous.measurable.aemeasurable hFmap
  rw [hrot] at hi
  have hneg : (∫ z, F z ∂stdGaussian (EuclideanSpace ℝ (Fin m))) =
      -∫ z, F z ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    calc
      _ = ∫ z, F (U z) ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := hi
      _ = ∫ z, -F z ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        simpa [U] using hodd z
      _ = -∫ z, F z ∂stdGaussian (EuclideanSpace ℝ (Fin m)) :=
        integral_neg F
  linarith

/-- Conditional difference from Steps 2--3 of the proof of Theorem 9.6.4.

**Book Theorem 9.6.4.** -/
private def conditionalFunctionalDifference {m : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    (a z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  f (a + z) - f (a - z)

/-- The leave-one-row conditional difference of the functional deviation is measurable.

**Lean implementation helper.** -/
private theorem conditionalFunctionalDifference_measurable {m : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b) :
    Measurable (fun p : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) ↦
        conditionalFunctionalDifference f p.1 p.2) := by
  have hfm := (f.continuous_of_growth hb hgrowth).measurable
  exact (hfm.comp (measurable_fst.add measurable_snd)).sub
    (hfm.comp (measurable_fst.sub measurable_snd))

/-- After the prescribed scaling, the conditional functional difference has a subgaussian moment-generating function.

**Lean implementation helper.** -/
private theorem conditionalFunctionalDifference_scaled_hasSubgaussianMGF
    {m : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hgrowth : HasEuclideanGrowth f b)
    (a : EuclideanSpace ℝ (Fin m)) :
    HasSubgaussianMGF
      (fun z ↦ conditionalFunctionalDifference f a z)
      ⟨(2 * b * c) ^ 2, sq_nonneg (2 * b * c)⟩
      (HDP.scaledStdGaussianMeasure
        (E := EuclideanSpace ℝ (Fin m)) c) := by
  let G : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun z ↦ conditionalFunctionalDifference f a (c • z)
  have hLip : LipschitzWith (NNReal.mk (2 * b * c) (by positivity)) G := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro z w
    have hp := abs_sub_le_of_subadditive_growth f f.subadditive hgrowth
      (a + c • z) (a + c • w)
    have hm := abs_sub_le_of_subadditive_growth f f.subadditive hgrowth
      (a - c • z) (a - c • w)
    rw [Real.dist_eq]
    calc
      |G z - G w| ≤
          |f (a + c • z) - f (a + c • w)| +
            |f (a - c • z) - f (a - c • w)| := by
        rw [show G z - G w =
            (f (a + c • z) - f (a + c • w)) -
              (f (a - c • z) - f (a - c • w)) by
          dsimp [G, conditionalFunctionalDifference]
          ring]
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (f (a + c • z) - f (a + c • w))
          (f (a - c • z) - f (a - c • w))
      _ ≤ b * ‖(a + c • z) - (a + c • w)‖ +
          b * ‖(a - c • z) - (a - c • w)‖ := add_le_add hp hm
      _ = (2 * b * c) * dist z w := by
        rw [show (a + c • z) - (a + c • w) = c • (z - w) by module,
          show (a - c • z) - (a - c • w) = -(c • (z - w)) by module,
          norm_neg, norm_smul, dist_eq_norm]
        simp only [Real.norm_eq_abs, abs_of_pos hc]
        ring
  have hcenter := stdGaussian_lipschitz_hasSubgaussianMGF G
    (show 0 < 2 * b * c by positivity) hLip
  have hGodd : ∀ z, G (-z) = -G z := by
    intro z
    dsimp [G, conditionalFunctionalDifference]
    rw [smul_neg, ← sub_eq_add_neg, sub_neg_eq_add]
    ring
  have hGint : Integrable G
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    ((ProbabilityTheory.IsGaussian.memLp_two_id.norm.const_mul
        (2 * b * c)).integrable (by norm_num)).add
      (integrable_const ‖G 0‖) |>.mono'
      hLip.continuous.aestronglyMeasurable (by
        filter_upwards [] with z
        have h := hLip.dist_le_mul z 0
        have h' : ‖G z - G 0‖ ≤ (2 * b * c) * ‖z‖ := by
          simpa only [Real.dist_eq, Real.norm_eq_abs, sub_zero,
            dist_zero_right, NNReal.coe_mk] using h
        calc
          ‖G z‖ = ‖(G z - G 0) + G 0‖ := by congr 1; ring
          _ ≤ ‖G z - G 0‖ + ‖G 0‖ := norm_add_le _ _
          _ ≤ (2 * b * c) * ‖z‖ + ‖G 0‖ :=
            by linarith)
  have hmean : (∫ z, G z
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 0 :=
    integral_odd_stdGaussian_eq_zero G hGint hGodd
  have hGraw : HasSubgaussianMGF G
      ⟨(2 * b * c) ^ 2, sq_nonneg (2 * b * c)⟩
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    simpa [G, hmean] using hcenter
  let L : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun z ↦ c • z
  have hLlaw : HasLaw L
      (HDP.scaledStdGaussianMeasure
        (E := EuclideanSpace ℝ (Fin m)) c)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    refine ⟨by fun_prop, ?_⟩
    rfl
  have hbase : IdentDistrib L
      (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (HDP.scaledStdGaussianMeasure
        (E := EuclideanSpace ℝ (Fin m)) c) :=
    hLlaw.identDistrib HasLaw.id
  have hHm : Measurable (fun z ↦ conditionalFunctionalDifference f a z) :=
    ((f.continuous_of_growth hb.le hgrowth).measurable.comp
      (measurable_const.add measurable_id)).sub
      ((f.continuous_of_growth hb.le hgrowth).measurable.comp
        (measurable_const.sub measurable_id))
  have hident := hbase.comp hHm
  simpa [G, L, Function.comp_def] using hGraw.congr_identDistrib hident

/-- Exact joint law of the half-sum and half-difference actions.

**Lean implementation helper.** -/
private theorem gaussianMatrixAction_half_pair_hasLaw {m n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) (huv : inner ℝ u v = 0) :
    HasLaw
      (fun A : Matrix (Fin m) (Fin n) ℝ ↦
        (HDP.gaussianMatrixAction A u, HDP.gaussianMatrixAction A v))
      ((HDP.scaledStdGaussianMeasure
          (E := EuclideanSpace ℝ (Fin m)) ‖u‖).prod
        (HDP.scaledStdGaussianMeasure
          (E := EuclideanSpace ℝ (Fin m)) ‖v‖))
      (HDP.stdGaussianMatrixMeasure m n) := by
  exact (HDP.gaussianMatrixAction_indep_of_inner_eq_zero m n u v huv).hasLaw_prod
    (HDP.gaussianMatrixAction_hasLaw_scaledStdGaussian m n u)
    (HDP.gaussianMatrixAction_hasLaw_scaledStdGaussian m n v)

/-- The explicit unit-sphere constant delivered by Gaussian concentration.

**Lean implementation helper.** -/
def generalFunctionalUnitIncrementConstant : ℝ := 2 * Real.sqrt 5

/-- The general functional unit increment constant is strictly positive.

**Lean implementation helper.** -/
theorem generalFunctionalUnitIncrementConstant_pos :
    0 < generalFunctionalUnitIncrementConstant := by
  unfold generalFunctionalUnitIncrementConstant
  positivity

/-- Fixed unit direction, used both at the origin and in the radial step.

**Lean implementation helper.** -/
private theorem functionalDeviation_unit {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 < b) (hgrowth : HasEuclideanGrowth f b)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    HDP.SubGaussian (functionalDeviationProcess f x)
        (HDP.stdGaussianMatrixMeasure m n) ∧
      HDP.psi2Norm (functionalDeviationProcess f x)
          (HDP.stdGaussianMatrixMeasure m n) ≤
        generalFunctionalUnitIncrementConstant * b := by
  have hLip := f.lipschitzWith_of_growth hb.le hgrowth
  have hstd := stdGaussian_lipschitz_hasSubgaussianMGF f hb hLip
  have hmap : (HDP.stdGaussianMatrixMeasure m n).map
      (fun A ↦ HDP.gaussianMatrixAction A x) =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    rw [HDP.gaussianMatrixAction_map_eq_scaledStdGaussian, hx]
    simp [HDP.scaledStdGaussianMeasure]
  have hmean := (HDP.gaussianMatrixAction_hasLaw_scaledStdGaussian m n x).integral_comp
    hLip.continuous.measurable.aestronglyMeasurable
  have hmean' : (∫ A, f (HDP.gaussianMatrixAction A x)
        ∂HDP.stdGaussianMatrixMeasure m n) =
      ∫ z, f z ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    simpa [hx, HDP.scaledStdGaussianMeasure] using hmean
  have haction : HasLaw (fun A ↦ HDP.gaussianMatrixAction A x)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (HDP.stdGaussianMatrixMeasure m n) :=
    ⟨(HDP.gaussianMatrixAction_measurable x).aemeasurable, hmap⟩
  let G : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun z ↦ f z - ∫ q, f q ∂stdGaussian (EuclideanSpace ℝ (Fin m))
  have hident := haction.identDistrib HasLaw.id
  have hGm : Measurable G := hLip.continuous.measurable.sub_const _
  have hprocG : functionalDeviationProcess f x =
      fun A ↦ G (HDP.gaussianMatrixAction A x) := by
    funext A
    simp only [functionalDeviationProcess, G]
    rw [hmean']
  have hGident : IdentDistrib G (functionalDeviationProcess f x)
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (HDP.stdGaussianMatrixMeasure m n) := by
    rw [hprocG]
    have hcomp := (hident.comp hGm).symm
    change IdentDistrib (fun z ↦ G z)
      (fun A ↦ G (HDP.gaussianMatrixAction A x))
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
      (HDP.stdGaussianMatrixMeasure m n) at hcomp
    exact hcomp
  have hmgf : HasSubgaussianMGF (functionalDeviationProcess f x)
      ⟨b ^ 2, sq_nonneg b⟩ (HDP.stdGaussianMatrixMeasure m n) := by
    exact hstd.congr_identDistrib hGident
  have hpsi := HDP.Chapter5.psi2Norm_le_of_hasSubgaussianMGF_sq hb hmgf
  refine ⟨hpsi.1, hpsi.2.trans_eq ?_⟩
  unfold generalFunctionalUnitIncrementConstant
  ring

/-- Unit-sphere increment calculation, including the conditional-product
step that was missing from the previous reconstruction.

**Lean implementation helper.** -/
private theorem functionalDeviation_unit_pair {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 < b) (hgrowth : HasEuclideanGrowth f b)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    HDP.SubGaussian (fun A ↦ functionalDeviationProcess f x A -
        functionalDeviationProcess f y A)
        (HDP.stdGaussianMatrixMeasure m n) ∧
      HDP.psi2Norm (fun A ↦ functionalDeviationProcess f x A -
          functionalDeviationProcess f y A)
          (HDP.stdGaussianMatrixMeasure m n) ≤
        generalFunctionalUnitIncrementConstant * b * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    have hunit := functionalDeviation_unit f hb hgrowth x hx
    have hz : (fun A ↦ functionalDeviationProcess f x A -
        functionalDeviationProcess f x A) =
        fun A ↦ (0 : ℝ) * functionalDeviationProcess f x A := by
      funext A
      ring
    rw [hz]
    refine ⟨hunit.1.const_mul 0, ?_⟩
    rw [HDP.psi2Norm_const_mul]
    simp
  · let u : EuclideanSpace ℝ (Fin n) := (2 : ℝ)⁻¹ • (x + y)
    let v : EuclideanSpace ℝ (Fin n) := (2 : ℝ)⁻¹ • (x - y)
    have huv : inner ℝ u v = 0 := by
      simp only [u, v, real_inner_smul_left, real_inner_smul_right,
        inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [hx, hy]
      rw [real_inner_comm y x]
      ring
    have hvnorm : ‖v‖ = ‖x - y‖ / 2 := by
      simp [v, norm_smul]
      ring
    have hvpos : 0 < ‖v‖ := by
      rw [hvnorm]
      exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) (by norm_num)
    let P := HDP.scaledStdGaussianMeasure
      (E := EuclideanSpace ℝ (Fin m)) ‖u‖
    let Q := HDP.scaledStdGaussianMeasure
      (E := EuclideanSpace ℝ (Fin m)) ‖v‖
    let H : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) → ℝ :=
      fun p ↦ conditionalFunctionalDifference f p.1 p.2
    have hHmgf : HasSubgaussianMGF H
        ⟨(2 * b * ‖v‖) ^ 2, sq_nonneg (2 * b * ‖v‖)⟩ (P.prod Q) := by
      apply hasSubgaussianMGF_prod_of_forall P Q H
        (conditionalFunctionalDifference_measurable f hb.le hgrowth)
      intro a
      exact conditionalFunctionalDifference_scaled_hasSubgaussianMGF
        f hb hvpos hgrowth a
    have hpair := gaussianMatrixAction_half_pair_hasLaw
      (m := m) u v huv
    have hHident : IdentDistrib H
        (fun A : Matrix (Fin m) (Fin n) ℝ ↦
          H (HDP.gaussianMatrixAction A u, HDP.gaussianMatrixAction A v))
        (P.prod Q) (HDP.stdGaussianMatrixMeasure m n) := by
      have hcomp := (hpair.identDistrib HasLaw.id).symm.comp
        (conditionalFunctionalDifference_measurable f hb.le hgrowth)
      simpa [Function.comp_def] using hcomp
    have htransport := hHmgf.congr_identDistrib hHident
    have hreprX : x = u + v := by
      simp [u, v]
      module
    have hreprY : y = u - v := by
      simp [u, v]
      module
    have hraw : HasSubgaussianMGF
        (fun A : Matrix (Fin m) (Fin n) ℝ ↦
          f (HDP.gaussianMatrixAction A x) -
            f (HDP.gaussianMatrixAction A y))
        ⟨(2 * b * ‖v‖) ^ 2, sq_nonneg (2 * b * ‖v‖)⟩
        (HDP.stdGaussianMatrixMeasure m n) := by
      simpa [H, conditionalFunctionalDifference, Function.comp_def,
        hreprX, hreprY, map_add, map_sub,
        HDP.gaussianMatrixAction_eq_toEuclideanLin] using htransport
    have hmeans : (∫ A, f (HDP.gaussianMatrixAction A x)
          ∂HDP.stdGaussianMatrixMeasure m n) =
        ∫ A, f (HDP.gaussianMatrixAction A y)
          ∂HDP.stdGaussianMatrixMeasure m n := by
      calc
        _ = ‖x‖ * ∫ g, f g ∂stdGaussian
            (EuclideanSpace ℝ (Fin m)) :=
          integral_functional_gaussianMatrixAction_eq f hb.le hgrowth x
        _ = ‖y‖ * ∫ g, f g ∂stdGaussian
            (EuclideanSpace ℝ (Fin m)) := by rw [hx, hy]
        _ = _ :=
          (integral_functional_gaussianMatrixAction_eq f hb.le hgrowth y).symm
    have hcenter : HasSubgaussianMGF
        (fun A ↦ functionalDeviationProcess f x A -
          functionalDeviationProcess f y A)
        ⟨(2 * b * ‖v‖) ^ 2, sq_nonneg (2 * b * ‖v‖)⟩
        (HDP.stdGaussianMatrixMeasure m n) := by
      convert hraw using 1
      funext A
      simp [functionalDeviationProcess, hmeans]
    have hpsi := HDP.Chapter5.psi2Norm_le_of_hasSubgaussianMGF_sq
      (show 0 < 2 * b * ‖v‖ by positivity) hcenter
    refine ⟨hpsi.1, ?_⟩
    calc
      HDP.psi2Norm (fun A ↦ functionalDeviationProcess f x A -
          functionalDeviationProcess f y A)
          (HDP.stdGaussianMatrixMeasure m n) ≤
          Real.sqrt 5 * (2 * (2 * b * ‖v‖)) := hpsi.2
      _ = generalFunctionalUnitIncrementConstant * b * ‖x - y‖ := by
        rw [hvnorm]
        simp [generalFunctionalUnitIncrementConstant]
        ring

/-- Positive homogeneity of the centered process.

**Lean implementation helper.** -/
private theorem functionalDeviationProcess_smul_of_nonneg {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    (c : ℝ) (hc : 0 ≤ c) (x : EuclideanSpace ℝ (Fin n)) :
    functionalDeviationProcess f (c • x) =
      fun A ↦ c * functionalDeviationProcess f x A := by
  funext A
  simp only [functionalDeviationProcess,
    HDP.gaussianMatrixAction_eq_toEuclideanLin, map_smul]
  simp_rw [f.positivelyHomogeneous c hc]
  rw [integral_const_mul]
  ring

/-- The functional deviation process vanishes at zero.

**Lean implementation helper.** -/
@[simp]
theorem functionalDeviationProcess_zero {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m))) :
    functionalDeviationProcess (n := n) f 0 = 0 := by
  funext A
  simp [functionalDeviationProcess, HDP.gaussianMatrixAction_eq_toEuclideanLin,
    f.map_zero]

/-- Final absolute constant in Theorems 9.6.3--9.6.4.

**Lean implementation helper.** -/
def generalFunctionalIncrementConstant : ℝ :=
  Real.sqrt 2 * generalFunctionalUnitIncrementConstant

/-- The general functional increment constant is strictly positive.

**Lean implementation helper.** -/
theorem generalFunctionalIncrementConstant_pos :
    0 < generalFunctionalIncrementConstant := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num))
    generalFunctionalUnitIncrementConstant_pos

/-- A functional-deviation increment over a vector of norm at most one has the required subgaussian bound.

**Lean implementation helper.** -/
private theorem functionalDeviation_pair_of_norm_le {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 < b) (hgrowth : HasEuclideanGrowth f b)
    (x y : EuclideanSpace ℝ (Fin n)) (hx0 : x ≠ 0)
    (hxyNorm : ‖x‖ ≤ ‖y‖) :
    HDP.SubGaussian (fun A ↦ functionalDeviationProcess f x A -
        functionalDeviationProcess f y A)
        (HDP.stdGaussianMatrixMeasure m n) ∧
      HDP.psi2Norm (fun A ↦ functionalDeviationProcess f x A -
          functionalDeviationProcess f y A)
          (HDP.stdGaussianMatrixMeasure m n) ≤
        generalFunctionalIncrementConstant * b * ‖x - y‖ := by
  let r : ℝ := ‖x‖
  let xbar : EuclideanSpace ℝ (Fin n) := r⁻¹ • x
  let yprime : EuclideanSpace ℝ (Fin n) := r⁻¹ • y
  let q : ℝ := ‖yprime‖
  let ybar : EuclideanSpace ℝ (Fin n) := q⁻¹ • yprime
  have hr : 0 < r := by
    exact norm_pos_iff.mpr hx0
  have hxbar : ‖xbar‖ = 1 := by
    simp [xbar, r, norm_smul, hr.ne']
  have hyprime : ‖yprime‖ = r⁻¹ * ‖y‖ := by
    rw [show yprime = r⁻¹ • y by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  have hq : 1 ≤ q := by
    rw [show q = r⁻¹ * ‖y‖ by simpa [q] using hyprime]
    rw [show (1 : ℝ) = r⁻¹ * r by field_simp]
    exact mul_le_mul_of_nonneg_left hxyNorm (inv_nonneg.mpr hr.le)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hybar : ‖ybar‖ = 1 := by
    simp [ybar, q, norm_smul, hqpos.ne']
  have hxrepr : x = r • xbar := by simp [xbar, r, hr.ne']
  have hyrepr : y = r • yprime := by simp [yprime, r, hr.ne']
  have hyprime_repr : yprime = q • ybar := by simp [ybar, q, hqpos.ne']
  have hradial : ‖ybar - yprime‖ = q - 1 := by
    rw [hyprime_repr]
    have heq : ybar - q • ybar = (1 - q) • ybar := by module
    rw [heq, norm_smul, hybar, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  let P : Matrix (Fin m) (Fin n) ℝ → ℝ := fun A ↦
    functionalDeviationProcess f xbar A - functionalDeviationProcess f ybar A
  let R : Matrix (Fin m) (Fin n) ℝ → ℝ := fun A ↦
    (1 - q) * functionalDeviationProcess f ybar A
  have hP := functionalDeviation_unit_pair f hb hgrowth xbar ybar hxbar hybar
  have hY := functionalDeviation_unit f hb hgrowth ybar hybar
  have hfm := (f.continuous_of_growth hb.le hgrowth).measurable
  have hZm : ∀ z, AEMeasurable (functionalDeviationProcess f z)
      (HDP.stdGaussianMatrixMeasure m n) := by
    intro z
    exact ((hfm.comp (HDP.gaussianMatrixAction_measurable z)).sub_const _).aemeasurable
  have hPm : AEMeasurable P (HDP.stdGaussianMatrixMeasure m n) :=
    (hZm xbar).sub (hZm ybar)
  have hRm : AEMeasurable R (HDP.stdGaussianMatrixMeasure m n) :=
    (hZm ybar).const_mul (1 - q)
  have hRsg : HDP.SubGaussian R (HDP.stdGaussianMatrixMeasure m n) :=
    hY.1.const_mul (1 - q)
  have hsumSG : HDP.SubGaussian (fun A ↦ P A + R A)
      (HDP.stdGaussianMatrixMeasure m n) :=
    hP.1.add hPm hRm hRsg
  have hRnorm : HDP.psi2Norm R (HDP.stdGaussianMatrixMeasure m n) ≤
      generalFunctionalUnitIncrementConstant * b * ‖ybar - yprime‖ := by
    rw [HDP.psi2Norm_const_mul]
    have habs : |1 - q| = q - 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hq)]
      ring
    rw [habs, hradial]
    have hcoeff : 0 ≤ q - 1 := sub_nonneg.mpr hq
    calc
      (q - 1) * HDP.psi2Norm (functionalDeviationProcess f ybar)
          (HDP.stdGaussianMatrixMeasure m n) ≤
          (q - 1) * (generalFunctionalUnitIncrementConstant * b) :=
        mul_le_mul_of_nonneg_left hY.2 hcoeff
      _ = generalFunctionalUnitIncrementConstant * b * (q - 1) := by ring
  have hsumNorm : HDP.psi2Norm (fun A ↦ P A + R A)
      (HDP.stdGaussianMatrixMeasure m n) ≤
      generalFunctionalUnitIncrementConstant * b *
        (‖xbar - ybar‖ + ‖ybar - yprime‖) := by
    calc
      HDP.psi2Norm (fun A ↦ P A + R A)
          (HDP.stdGaussianMatrixMeasure m n) ≤
          HDP.psi2Norm P (HDP.stdGaussianMatrixMeasure m n) +
            HDP.psi2Norm R (HDP.stdGaussianMatrixMeasure m n) :=
        HDP.psi2Norm_add_le hPm hRm hP.1 hRsg
      _ ≤ generalFunctionalUnitIncrementConstant * b * ‖xbar - ybar‖ +
          generalFunctionalUnitIncrementConstant * b * ‖ybar - yprime‖ :=
        add_le_add hP.2 hRnorm
      _ = _ := by ring
  have hreverse : ‖xbar - ybar‖ + ‖ybar - yprime‖ ≤
      Real.sqrt 2 * ‖xbar - yprime‖ := by
    simpa [ybar, q] using
      (exercise_9_1_reverse_triangle xbar yprime hxbar
        (show 1 ≤ ‖yprime‖ by simpa [q] using hq)).2
  have hZx : functionalDeviationProcess f x =
      fun A ↦ r * functionalDeviationProcess f xbar A := by
    rw [hxrepr]
    exact functionalDeviationProcess_smul_of_nonneg f r hr.le xbar
  have hZy : functionalDeviationProcess f y =
      fun A ↦ r * (q * functionalDeviationProcess f ybar A) := by
    rw [hyrepr, hyprime_repr]
    funext A
    rw [congrFun (functionalDeviationProcess_smul_of_nonneg
      f r hr.le (q • ybar)) A,
      congrFun (functionalDeviationProcess_smul_of_nonneg
        f q hqpos.le ybar) A]
  have hfun : (fun A ↦ functionalDeviationProcess f x A -
      functionalDeviationProcess f y A) = fun A ↦ r * (P A + R A) := by
    funext A
    rw [congrFun hZx A, congrFun hZy A]
    simp only [P, R]
    ring
  have hnormdiff : ‖x - y‖ = r * ‖xbar - yprime‖ := by
    rw [hxrepr, hyrepr, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
  rw [hfun]
  refine ⟨hsumSG.const_mul r, ?_⟩
  rw [HDP.psi2Norm_const_mul, abs_of_pos hr]
  calc
    r * HDP.psi2Norm (fun A ↦ P A + R A)
        (HDP.stdGaussianMatrixMeasure m n) ≤
        r * (generalFunctionalUnitIncrementConstant * b *
          (‖xbar - ybar‖ + ‖ybar - yprime‖)) :=
      mul_le_mul_of_nonneg_left hsumNorm hr.le
    _ ≤ r * (generalFunctionalUnitIncrementConstant * b *
        (Real.sqrt 2 * ‖xbar - yprime‖)) := by
      gcongr
      exact mul_nonneg generalFunctionalUnitIncrementConstant_pos.le hb.le
    _ = generalFunctionalIncrementConstant * b * ‖x - y‖ := by
      rw [hnormdiff]
      simp [generalFunctionalIncrementConstant]
      ring

/-- The functional deviation pair vanishes at zero.

**Lean implementation helper.** -/
private theorem functionalDeviation_pair_zero {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 < b) (hgrowth : HasEuclideanGrowth f b)
    (x : EuclideanSpace ℝ (Fin n)) (hx0 : x ≠ 0) :
    HDP.SubGaussian (fun A ↦ functionalDeviationProcess f x A -
        functionalDeviationProcess f 0 A)
        (HDP.stdGaussianMatrixMeasure m n) ∧
      HDP.psi2Norm (fun A ↦ functionalDeviationProcess f x A -
          functionalDeviationProcess f 0 A)
          (HDP.stdGaussianMatrixMeasure m n) ≤
        generalFunctionalIncrementConstant * b * ‖x - 0‖ := by
  let r : ℝ := ‖x‖
  let xbar : EuclideanSpace ℝ (Fin n) := r⁻¹ • x
  have hr : 0 < r := norm_pos_iff.mpr hx0
  have hxbar : ‖xbar‖ = 1 := by simp [xbar, r, norm_smul, hr.ne']
  have hxrepr : x = r • xbar := by simp [xbar, r, hr.ne']
  have hunit := functionalDeviation_unit f hb hgrowth xbar hxbar
  have hfun : (fun A ↦ functionalDeviationProcess f x A -
      functionalDeviationProcess f 0 A) =
      fun A ↦ r * functionalDeviationProcess f xbar A := by
    funext A
    rw [congrFun (functionalDeviationProcess_zero f) A]
    simp only [Pi.zero_apply, sub_zero]
    rw [hxrepr, congrFun
      (functionalDeviationProcess_smul_of_nonneg f r hr.le xbar) A]
  have hC : generalFunctionalUnitIncrementConstant ≤
      generalFunctionalIncrementConstant := by
    have hs : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    unfold generalFunctionalIncrementConstant
    nlinarith [generalFunctionalUnitIncrementConstant_pos]
  rw [hfun]
  refine ⟨hunit.1.const_mul r, ?_⟩
  rw [HDP.psi2Norm_const_mul, abs_of_pos hr]
  calc
    r * HDP.psi2Norm (functionalDeviationProcess f xbar)
        (HDP.stdGaussianMatrixMeasure m n) ≤
        r * (generalFunctionalUnitIncrementConstant * b) :=
      mul_le_mul_of_nonneg_left hunit.2 hr.le
    _ ≤ r * (generalFunctionalIncrementConstant * b) := by gcongr
    _ = generalFunctionalIncrementConstant * b * ‖x - 0‖ := by
      simp [r]
      ring

/-- The zero functional of a standard Gaussian matrix is subgaussian with zero scale.

**Lean implementation helper.** -/
private theorem zero_subGaussian_stdGaussianMatrix {m n : ℕ} :
    HDP.SubGaussian (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : ℝ))
        (HDP.stdGaussianMatrixMeasure m n) ∧
      HDP.psi2Norm (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : ℝ))
        (HDP.stdGaussianMatrixMeasure m n) = 0 := by
  constructor
  · refine ⟨1, one_pos, ?_⟩
    have hz : (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : ℝ)) =ᵐ[
        HDP.stdGaussianMatrixMeasure m n] 0 :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    rw [HDP.psi2MGF_of_ae_zero hz]
    norm_num
  · have h := HDP.psi2Norm_const_mul
      (μ := HDP.stdGaussianMatrixMeasure m n)
      (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : ℝ)) 0
    simpa only [zero_mul, abs_zero] using h

/-- The centered sublinear-functional process has subgaussian increments. The canonical Gaussian functional process has
subgaussian increments. No analytic estimate appears as a hypothesis.

**Book Theorem 9.6.4.** -/
theorem theorem_9_6_4_subgaussianIncrements {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    (x y : EuclideanSpace ℝ (Fin n)) :
    HDP.SubGaussian (fun A ↦ functionalDeviationProcess f x A -
        functionalDeviationProcess f y A)
        (HDP.stdGaussianMatrixMeasure m n) ∧
      HDP.psi2Norm (fun A ↦ functionalDeviationProcess f x A -
          functionalDeviationProcess f y A)
          (HDP.stdGaussianMatrixMeasure m n) ≤
        generalFunctionalIncrementConstant * b * ‖x - y‖ := by
  rcases hb.eq_or_lt with rfl | hb
  · have hfzero : ∀ z, f z = 0 := by
      intro z
      have h := (f.lipschitzWith_of_growth (le_refl 0) hgrowth).dist_le_mul z 0
      have hz : f z = f 0 :=
        dist_eq_zero.mp (le_antisymm (by simpa using h) dist_nonneg)
      simpa [f.map_zero] using hz
    have hproc : ∀ z, functionalDeviationProcess (n := n) f z = 0 := by
      intro z
      funext A
      simp [functionalDeviationProcess, hfzero]
    rw [hproc x, hproc y]
    have hzero := zero_subGaussian_stdGaussianMatrix (m := m) (n := n)
    simpa using ⟨hzero.1, le_of_eq hzero.2⟩
  · by_cases hx0 : x = 0
    · subst x
      by_cases hy0 : y = 0
      · subst y
        have hzero := zero_subGaussian_stdGaussianMatrix (m := m) (n := n)
        simpa using ⟨hzero.1, le_of_eq hzero.2⟩
      · have h := functionalDeviation_pair_zero f hb hgrowth y hy0
        have hfun : (fun A ↦ functionalDeviationProcess f 0 A -
            functionalDeviationProcess f y A) =
            fun A ↦ (-1 : ℝ) *
              (functionalDeviationProcess f y A -
                functionalDeviationProcess f 0 A) := by
          funext A
          ring
        rw [hfun]
        refine ⟨h.1.const_mul (-1), ?_⟩
        rw [HDP.psi2Norm_const_mul]
        simpa [norm_sub_rev] using h.2
    · by_cases hy0 : y = 0
      · subst y
        exact functionalDeviation_pair_zero f hb hgrowth x hx0
      · rcases le_total ‖x‖ ‖y‖ with hxy | hyx
        · exact functionalDeviation_pair_of_norm_le f hb hgrowth x y hx0 hxy
        · have h := functionalDeviation_pair_of_norm_le
            f hb hgrowth y x hy0 hyx
          have hfun : (fun A ↦ functionalDeviationProcess f x A -
              functionalDeviationProcess f y A) =
              fun A ↦ (-1 : ℝ) *
                (functionalDeviationProcess f y A -
                  functionalDeviationProcess f x A) := by
            funext A
            ring
          rw [hfun]
          refine ⟨h.1.const_mul (-1), ?_⟩
          rw [HDP.psi2Norm_const_mul]
          simpa [norm_sub_rev] using h.2

/- Explicit chaining constant in Theorem 9.6.3. -/
section MajorizingMeasure

variable [hMM : HDP.Chapter8.MajorizingMeasureLowerPrinciple]

/-- The general matrix-deviation constant is the product of the chaining expectation constant and the unit-increment constant.

**Lean implementation helper.** -/
def generalMatrixDeviationConstant : ℝ :=
  HDP.Chapter8.exercise837ExpectationConstant *
    generalFunctionalIncrementConstant

/-- The general matrix deviation constant is strictly positive.

**Lean implementation helper.** -/
theorem generalMatrixDeviationConstant_pos :
    0 < generalMatrixDeviationConstant := by
  exact mul_pos HDP.Chapter8.exercise837ExpectationConstant_pos
    generalFunctionalIncrementConstant_pos

/-- A Gaussian matrix obeys a general deviation inequality for sublinear functionals with linear growth.

**Book Theorem 9.6.3.** -/
theorem theorem_9_6_3_generalMatrixDeviation {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (hT : T.Nonempty) :
    (∫ A, HDP.Chapter8.finiteProcessAbsoluteSup
        (HDP.Chapter8.finiteEuclideanProcess T
          (functionalDeviationProcess f)) A
      ∂HDP.stdGaussianMatrixMeasure m n) ≤
      generalMatrixDeviationConstant * b *
        HDP.Chapter7.gaussianComplexity T := by
  have hfm := (f.continuous_of_growth hb hgrowth).measurable
  have hchain := HDP.Chapter8.exercise_8_37a_expectation
    (HDP.stdGaussianMatrixMeasure m n) T hT
    (functionalDeviationProcess f)
    (fun x _ ↦ ((hfm.comp
      (HDP.gaussianMatrixAction_measurable x)).sub_const _))
    (functionalDeviationProcess_zero f)
    (mul_nonneg generalFunctionalIncrementConstant_pos.le hb)
    (fun x _ y _ ↦ theorem_9_6_4_subgaussianIncrements f hb hgrowth x y)
  simpa [generalMatrixDeviationConstant, mul_assoc] using hchain

/-! The source quantifies Theorem 9.6.3 over an arbitrary subset `T`.
As in Theorem 9.1.1, the safe authoritative interpretation is the
extended-valued supremum over all nonempty finite subfamilies. -/

/-- Expected absolute-deviation envelope for an arbitrary index set.

**Lean implementation helper.** -/
def generalFunctionalDeviationExpectationEnvelope {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n))),
    ⨆ (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T),
    ⨆ (hF : F.Nonempty),
    letI : Nonempty ↑F := hF.to_subtype
    ENNReal.ofReal
      (∫ A, HDP.Chapter8.finiteProcessAbsoluteSup
          (HDP.Chapter8.finiteEuclideanProcess F
            (functionalDeviationProcess f)) A
        ∂HDP.stdGaussianMatrixMeasure m n)

/-- A Gaussian matrix obeys a general deviation inequality for sublinear functionals with linear growth.

**Book Theorem 9.6.3.** -/
theorem theorem_9_6_3_generalMatrixDeviation_envelope {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    generalFunctionalDeviationExpectationEnvelope f T ≤
      ENNReal.ofReal (generalMatrixDeviationConstant * b) *
        gaussianComplexityEnvelope T := by
  unfold generalFunctionalDeviationExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↑F := hF.to_subtype
  have hmain := theorem_9_6_3_generalMatrixDeviation
    f hb hgrowth F hF
  have hcoef : 0 ≤ generalMatrixDeviationConstant * b :=
    mul_nonneg generalMatrixDeviationConstant_pos.le hb
  have hcomplexity :
      ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) ≤
        gaussianComplexityEnvelope T := by
    unfold gaussianComplexityEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  calc
    ENNReal.ofReal
        (∫ A, HDP.Chapter8.finiteProcessAbsoluteSup
            (HDP.Chapter8.finiteEuclideanProcess F
              (functionalDeviationProcess f)) A
          ∂HDP.stdGaussianMatrixMeasure m n) ≤
        ENNReal.ofReal (generalMatrixDeviationConstant * b *
          HDP.Chapter7.gaussianComplexity F) :=
      ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (generalMatrixDeviationConstant * b) *
        ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (generalMatrixDeviationConstant * b) *
        gaussianComplexityEnvelope T := by
      gcongr

/-- High-probability form used by Exercises 9.36--9.37.

**Lean implementation helper.** -/
theorem generalMatrixDeviation_highProbability {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b u : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (hT : T.Nonempty) (hu : 0 ≤ u) :
    HDP.stdGaussianMatrixMeasure m n
      {A | HDP.Chapter8.exercise837HighProbabilityConstant *
          (generalFunctionalIncrementConstant * b) *
          (HDP.Chapter7.gaussianWidth T +
            u * HDP.Chapter7.finiteRadius T) <
        HDP.Chapter8.finiteProcessAbsoluteSup
          (HDP.Chapter8.finiteEuclideanProcess T
            (functionalDeviationProcess f)) A} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  have hfm := (f.continuous_of_growth hb hgrowth).measurable
  exact HDP.Chapter8.exercise_8_37b_highProbability
    (HDP.stdGaussianMatrixMeasure m n) T hT
    (functionalDeviationProcess f)
    (fun x _ ↦ ((hfm.comp
      (HDP.gaussianMatrixAction_measurable x)).sub_const _))
    (functionalDeviationProcess_zero f)
    (mul_nonneg generalFunctionalIncrementConstant_pos.le hb) hu
    (fun x _ y _ ↦ theorem_9_6_4_subgaussianIncrements f hb hgrowth x y)

end MajorizingMeasure

/-! ## Exercise 9.37: general-norm Johnson--Lindenstrauss -/

/-- The functional matrix distance applies the target functional to the matrix image of a point difference.

**Lean implementation helper.** -/
def functionalMatrixDistance {m n : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f (deterministicMatrixAction A (x - y))

/-- A functional epsilon embedding distorts every pairwise distance in the finite set by at most the prescribed relative error.

**Lean implementation helper.** -/
def IsFunctionalEpsilonEmbeddingOn {m n : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (normalization ε : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * normalization * ‖x - y‖ ≤
        functionalMatrixDistance f A x y ∧
      functionalMatrixDistance f A x y ≤
        (1 + ε) * normalization * ‖x - y‖

/-- Normalized difference set; zero differences are retained as zero.

**Lean implementation helper.** -/
def normalizedDifferenceFinset {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  (HDP.Chapter7.differenceFinset X X).image
    (fun z ↦ ‖z‖⁻¹ • z)

/-- The normalized difference finset is nonempty.

**Lean implementation helper.** -/
theorem normalizedDifferenceFinset_nonempty {n : ℕ}
    {X : Finset (EuclideanSpace ℝ (Fin n))} (hX : X.Nonempty) :
    (normalizedDifferenceFinset X).Nonempty :=
  (HDP.Chapter7.differenceFinset_nonempty hX hX).image _

/-- Every normalized difference vector has Euclidean norm at most one.

**Lean implementation helper.** -/
theorem norm_normalizedDifference_le_one {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ normalizedDifferenceFinset X) :
    ‖z‖ ≤ 1 := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  by_cases hw0 : w = 0
  · simp [hw0]
  · simp [norm_smul, norm_ne_zero_iff.mpr hw0]

/-- The finite set of normalized differences has radius at most one.

**Lean implementation helper.** -/
theorem finiteRadius_normalizedDifference_le_one {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : X.Nonempty) :
    HDP.Chapter7.finiteRadius (normalizedDifferenceFinset X) ≤ 1 := by
  rw [HDP.Chapter7.finiteRadius_eq_sup'
    (normalizedDifferenceFinset X) (normalizedDifferenceFinset_nonempty hX)]
  exact Finset.sup'_le (normalizedDifferenceFinset_nonempty hX) (fun z ↦ ‖z‖)
    (fun z hz ↦ norm_normalizedDifference_le_one X hz)

/-- The normalization for general-norm Johnson–Lindenstrauss is the Gaussian expectation of the target functional.

**Lean implementation helper.** -/
def generalNormJLNormalization {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  ∫ g, f g ∂stdGaussian (EuclideanSpace ℝ (Fin m))

/-- The general-norm Johnson–Lindenstrauss error combines Gaussian width, tail parameter, functional growth, and the chaining constant.

**Lean implementation helper.** -/
def generalNormJLError {n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (b u : ℝ) (X : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  HDP.Chapter8.exercise837HighProbabilityConstant *
    (generalFunctionalIncrementConstant * b) *
    (HDP.Chapter7.gaussianWidth (normalizedDifferenceFinset X) + u)

/-- Uniform functional-deviation control on normalized differences implies the desired pairwise epsilon-embedding inequalities.

**Lean implementation helper.** -/
private theorem normalized_difference_controls_embedding {m n : ℕ}
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    {b : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    [Nonempty ↑(normalizedDifferenceFinset X)]
    {A : Matrix (Fin m) (Fin n) ℝ} {error ε : ℝ}
    (herror : error ≤ ε * generalNormJLNormalization f)
    (hdev : HDP.Chapter8.finiteProcessAbsoluteSup
      (HDP.Chapter8.finiteEuclideanProcess (normalizedDifferenceFinset X)
        (functionalDeviationProcess f)) A ≤ error) :
    IsFunctionalEpsilonEmbeddingOn f A X (generalNormJLNormalization f) ε := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp [functionalMatrixDistance, deterministicMatrixAction,
      f.map_zero]
  · let z := ‖x - y‖⁻¹ • (x - y)
    have hz : z ∈ normalizedDifferenceFinset X := by
      apply Finset.mem_image.mpr
      refine ⟨x - y, ?_, rfl⟩
      unfold HDP.Chapter7.differenceFinset HDP.Chapter7.minkowskiSumFinset
        HDP.Chapter7.negFinset
      apply Finset.mem_image.mpr
      refine ⟨(x, -y), Finset.mem_product.mpr ⟨hx, ?_⟩, by
        simp only [sub_eq_add_neg]⟩
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have hpoint :
        |HDP.Chapter8.finiteEuclideanProcess (normalizedDifferenceFinset X)
            (functionalDeviationProcess f) ⟨z, hz⟩ A| ≤
          HDP.Chapter8.finiteProcessAbsoluteSup
            (HDP.Chapter8.finiteEuclideanProcess (normalizedDifferenceFinset X)
              (functionalDeviationProcess f)) A := by
      unfold HDP.Chapter8.finiteProcessAbsoluteSup
      exact Finset.le_sup'
        (fun q : ↑(normalizedDifferenceFinset X) ↦
          |HDP.Chapter8.finiteEuclideanProcess (normalizedDifferenceFinset X)
            (functionalDeviationProcess f) q A|)
        (Finset.mem_univ
        (⟨z, hz⟩ : ↑(normalizedDifferenceFinset X)))
    have hnormz : ‖z‖ = 1 := by
      simp [z, norm_smul, norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)]
    have hmean : (∫ B, f (HDP.gaussianMatrixAction B z)
        ∂HDP.stdGaussianMatrixMeasure m n) = generalNormJLNormalization f := by
      simpa [hnormz, generalNormJLNormalization] using
        integral_functional_gaussianMatrixAction_eq f hb hgrowth z
    have hscaled : x - y = ‖x - y‖ • z := by
      dsimp [z]
      rw [smul_smul, mul_inv_cancel₀
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)), one_smul]
    have hfdist : functionalMatrixDistance f A x y =
        ‖x - y‖ * f (HDP.gaussianMatrixAction A z) := by
      unfold functionalMatrixDistance deterministicMatrixAction
      calc
        f (A.toEuclideanLin (x - y)) =
            f (A.toEuclideanLin (‖x - y‖ • z)) :=
          congrArg (fun w ↦ f (A.toEuclideanLin w)) hscaled
        _ = f (‖x - y‖ • A.toEuclideanLin z) := by rw [map_smul]
        _ = ‖x - y‖ * f (A.toEuclideanLin z) :=
          f.positivelyHomogeneous ‖x - y‖ (norm_nonneg _) (A.toEuclideanLin z)
        _ = ‖x - y‖ * f (HDP.gaussianMatrixAction A z) := by
          rw [HDP.gaussianMatrixAction_eq_toEuclideanLin]
    have hproc : functionalDeviationProcess f z A =
        f (HDP.gaussianMatrixAction A z) - generalNormJLNormalization f := by
      unfold functionalDeviationProcess
      rw [hmean]
    have habs : |f (HDP.gaussianMatrixAction A z) -
        generalNormJLNormalization f| ≤ error := by
      have hp : |f (HDP.gaussianMatrixAction A z) -
          generalNormJLNormalization f| ≤
          HDP.Chapter8.finiteProcessAbsoluteSup
            (HDP.Chapter8.finiteEuclideanProcess (normalizedDifferenceFinset X)
              (functionalDeviationProcess f)) A := by
        simpa only [HDP.Chapter8.finiteEuclideanProcess, hproc] using hpoint
      exact hp.trans hdev
    rw [abs_le] at habs
    rw [hfdist]
    have hxy0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    constructor <;> nlinarith

/-- General-norm Johnson--Lindenstrauss from general matrix deviation. This is a genuine canonical
Gaussian probability theorem. Its deterministic error condition exposes the
norm-dependent dimension requirement; the conclusion no longer assumes the
probability that it is meant to prove.

**Book Exercise 9.37.** -/
theorem exercise_9_37_generalNormJL {m n : ℕ}
    [hMM : HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (f : SublinearFunctional (EuclideanSpace ℝ (Fin m)))
    {b u ε : ℝ} (hb : 0 ≤ b) (hgrowth : HasEuclideanGrowth f b)
    (hu : 0 ≤ u) (_hε : 0 ≤ ε)
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : X.Nonempty)
    (_hnorm : 0 ≤ generalNormJLNormalization f)
    (herror : generalNormJLError b u X ≤
      ε * generalNormJLNormalization f) :
    HDP.stdGaussianMatrixMeasure m n
      {A | ¬ IsFunctionalEpsilonEmbeddingOn f A X
        (generalNormJLNormalization f) ε} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  let D := normalizedDifferenceFinset X
  have hD : D.Nonempty := normalizedDifferenceFinset_nonempty hX
  letI : Nonempty ↑D := hD.to_subtype
  let M : Matrix (Fin m) (Fin n) ℝ → ℝ :=
    HDP.Chapter8.finiteProcessAbsoluteSup
      (HDP.Chapter8.finiteEuclideanProcess D (functionalDeviationProcess f))
  let error := generalNormJLError b u X
  have htail := generalMatrixDeviation_highProbability f hb hgrowth D hD hu
  have hradius := finiteRadius_normalizedDifference_le_one X hX
  have hwidth : 0 ≤ HDP.Chapter7.gaussianWidth D :=
    HDP.Chapter7.gaussianWidth_nonneg D hD
  have hthreshold :
      HDP.Chapter8.exercise837HighProbabilityConstant *
          (generalFunctionalIncrementConstant * b) *
          (HDP.Chapter7.gaussianWidth D +
            u * HDP.Chapter7.finiteRadius D) ≤ error := by
    dsimp [error, generalNormJLError, D]
    have hcoef : 0 ≤ HDP.Chapter8.exercise837HighProbabilityConstant *
        (generalFunctionalIncrementConstant * b) :=
      mul_nonneg HDP.Chapter8.exercise837HighProbabilityConstant_pos.le
        (mul_nonneg generalFunctionalIncrementConstant_pos.le hb)
    apply mul_le_mul_of_nonneg_left _ hcoef
    have hur : u * HDP.Chapter7.finiteRadius
        (normalizedDifferenceFinset X) ≤ u := by
      calc
        _ ≤ u * 1 := mul_le_mul_of_nonneg_left hradius hu
        _ = u := mul_one u
    linarith
  calc
    HDP.stdGaussianMatrixMeasure m n
        {A | ¬ IsFunctionalEpsilonEmbeddingOn f A X
          (generalNormJLNormalization f) ε} ≤
        HDP.stdGaussianMatrixMeasure m n {A | error < M A} := by
      apply measure_mono
      intro A hA
      by_contra hnot
      exact hA (normalized_difference_controls_embedding
        f X hb hgrowth herror (not_lt.mp hnot))
    _ ≤ HDP.stdGaussianMatrixMeasure m n
        {A | HDP.Chapter8.exercise837HighProbabilityConstant *
            (generalFunctionalIncrementConstant * b) *
            (HDP.Chapter7.gaussianWidth D +
              u * HDP.Chapter7.finiteRadius D) < M A} := by
      apply measure_mono
      intro A hA
      exact lt_of_le_of_lt hthreshold hA
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      simpa [M, D] using htail

end

end HDP.Chapter9

end Source_16_GeneralMatrixDeviation

/-! ## Material formerly in `17_TwoSidedChevet.lean` -/

section Source_17_TwoSidedChevet

/-!
# Book Chapter 9, §9.7: the two-sided Chevet inequality

The theorem is stated directly for `HDP.stdGaussianMatrixMeasure`; neither its
fixed-direction mean nor its increment estimate is supplied by the caller.
The support set lies in `ℝ^m`, the range of the matrix, correcting the
dimension mismatch in display (9.43).
-/

open InnerProductSpace MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

/-- Centered support-function process in Theorem 9.7.1.

**Book Theorem 9.7.1.** -/
def finiteTwoSidedChevetProcess {m n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  finiteSupportFunctional S (HDP.gaussianMatrixAction A x) -
    HDP.Chapter7.gaussianWidth S * ‖x‖

/-- Display (9.44), proved from the canonical fixed-direction Gaussian law.

**Book Equation (9.44).** -/
theorem integral_finiteSupport_gaussianMatrixAction {m n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ A, finiteSupportFunctional S (HDP.gaussianMatrixAction A x)
        ∂HDP.stdGaussianMatrixMeasure m n) =
      HDP.Chapter7.gaussianWidth S * ‖x‖ := by
  have h := integral_functional_gaussianMatrixAction_eq
    (finiteSupportSublinearFunctional S hS)
    (HDP.Chapter7.finiteRadius_nonneg S)
    (finiteSupportFunctional_growth S hS) x
  simpa [finiteSupportSublinearFunctional, finiteSupportFunctional,
    HDP.Chapter7.gaussianWidth, mul_comm] using h

/-- For a support functional, the general functional-deviation process is the support deviation of the matrix image.

**Lean implementation helper.** -/
theorem functionalDeviationProcess_support_eq {m n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) :
    functionalDeviationProcess (finiteSupportSublinearFunctional S hS) x =
      finiteTwoSidedChevetProcess S x := by
  funext A
  simp only [functionalDeviationProcess, finiteTwoSidedChevetProcess,
    finiteSupportSublinearFunctional]
  rw [integral_finiteSupport_gaussianMatrixAction S hS x]

/-- Pointwise finite maximum on the left of Theorem 9.7.1.

**Book Theorem 9.7.1.** -/
def finiteTwoSidedChevetDeviation {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m)))
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  HDP.Chapter8.finiteProcessAbsoluteSup
    (HDP.Chapter8.finiteEuclideanProcess T
      (finiteTwoSidedChevetProcess S)) A

/-- The finite two-sided Chevet deviation is measurable as a finite supremum of measurable support deviations.

**Lean implementation helper.** -/
theorem measurable_finiteTwoSidedChevetDeviation {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty) :
    Measurable (finiteTwoSidedChevetDeviation T S) := by
  apply HDP.Chapter8.measurable_finiteProcessAbsoluteSup
  intro x
  exact (((finiteSupportSublinearFunctional S hS).continuous_of_growth
      (HDP.Chapter7.finiteRadius_nonneg S)
      (finiteSupportFunctional_growth S hS)).measurable.comp
    (HDP.gaussianMatrixAction_measurable x.1)).sub_const _

/-- The finite two-sided Chevet deviation is integrable under the standard Gaussian matrix law.

**Lean implementation helper.** -/
theorem integrable_finiteTwoSidedChevetDeviation {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m)))
    (hS : S.Nonempty) :
    Integrable (finiteTwoSidedChevetDeviation T S)
      (HDP.stdGaussianMatrixMeasure m n) := by
  apply HDP.Chapter8.integrable_finiteProcessAbsoluteSup
  intro x
  have hinc := theorem_9_6_4_subgaussianIncrements
    (m := m) (n := n) (finiteSupportSublinearFunctional S hS)
    (HDP.Chapter7.finiteRadius_nonneg S)
    (finiteSupportFunctional_growth S hS) x.1 0
  have hzero := functionalDeviationProcess_zero
    (m := m) (n := n) (finiteSupportSublinearFunctional S hS)
  have hsg : HDP.SubGaussian
      (functionalDeviationProcess
        (finiteSupportSublinearFunctional S hS) x.1)
      (HDP.stdGaussianMatrixMeasure m n) := by
    simpa [hzero] using hinc.1
  have hm : AEMeasurable
      (functionalDeviationProcess
        (finiteSupportSublinearFunctional S hS) x.1)
      (HDP.stdGaussianMatrixMeasure m n) := by
    exact ((((finiteSupportSublinearFunctional S hS).continuous_of_growth
      (HDP.Chapter7.finiteRadius_nonneg S)
      (finiteSupportFunctional_growth S hS)).measurable.comp
      (HDP.gaussianMatrixAction_measurable x.1)).sub_const _).aemeasurable
  have hint := (hsg.memLp hm (show (1 : ℝ) ≤ 1 by rfl)).integrable
    (by norm_num)
  simpa [HDP.Chapter8.finiteEuclideanProcess,
    functionalDeviationProcess_support_eq S hS x.1] using hint

/-- The two-sided Chevet supremum dominates each pointwise support deviation from Gaussian width.

**Lean implementation helper.** -/
theorem abs_support_sub_width_le_finiteTwoSidedChevetDeviation
    {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    |finiteSupportFunctional S (HDP.gaussianMatrixAction A x) -
        HDP.Chapter7.gaussianWidth S * ‖x‖| ≤
      finiteTwoSidedChevetDeviation T S A := by
  unfold finiteTwoSidedChevetDeviation
    HDP.Chapter8.finiteProcessAbsoluteSup
  let q : ↑T := ⟨x, hx⟩
  simpa [HDP.Chapter8.finiteEuclideanProcess,
    finiteTwoSidedChevetProcess, q] using
    (Finset.le_sup'
      (fun z : ↑T ↦
        |HDP.Chapter8.finiteEuclideanProcess T
          (finiteTwoSidedChevetProcess S) z A|)
      (Finset.mem_univ q))

/- **Book Theorem 9.7.1 (two-sided Chevet), finite canonical form.** -/
section MajorizingMeasure

variable [hMM : HDP.Chapter8.MajorizingMeasureLowerPrinciple]

/-- The expected two-sided support deviation of a random matrix image satisfies the finite Chevet bound.

**Lean implementation helper.** -/
theorem theorem_9_7_1_twoSidedChevet {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m))) [Nonempty ↑S]
    (hT : T.Nonempty) (hS : S.Nonempty) :
    (∫ A, finiteTwoSidedChevetDeviation T S A
        ∂HDP.stdGaussianMatrixMeasure m n) ≤
      generalMatrixDeviationConstant *
        HDP.Chapter7.gaussianComplexity T *
        HDP.Chapter7.finiteRadius S := by
  have hgeneral := theorem_9_6_3_generalMatrixDeviation
    (m := m) (n := n) (finiteSupportSublinearFunctional S hS)
    (HDP.Chapter7.finiteRadius_nonneg S)
    (finiteSupportFunctional_growth S hS) T hT
  have hproc : functionalDeviationProcess (m := m) (n := n)
      (finiteSupportSublinearFunctional S hS) =
      finiteTwoSidedChevetProcess (m := m) (n := n) S := by
    funext x
    exact functionalDeviationProcess_support_eq (m := m) (n := n) S hS x
  calc
    (∫ A, finiteTwoSidedChevetDeviation T S A
        ∂HDP.stdGaussianMatrixMeasure m n) ≤
        generalMatrixDeviationConstant * HDP.Chapter7.finiteRadius S *
          HDP.Chapter7.gaussianComplexity T := by
      simpa [finiteTwoSidedChevetDeviation, hproc] using hgeneral
    _ = generalMatrixDeviationConstant * HDP.Chapter7.gaussianComplexity T *
        HDP.Chapter7.finiteRadius S := by ring

/-! ### The actual output-set theorem

The finite theorem above is the proof engine.  In the source, however, the
support set `S` is one fixed arbitrary bounded set.  It is important not to
center each finite subfamily of `S` by its own Gaussian width: absolute
centered deviations are not monotone under enlarging that subfamily.  The
following API therefore fixes the genuine support functional of `S` first;
only the expected supremum over the input index set `T` is represented by the
book's directed finite-subfamily convention.
-/

/-- Gaussian width in the source's literal form: the expectation of the
support functional of the actual set.

**Lean implementation helper.** -/
def setSupportGaussianWidth {m : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m))) : ℝ :=
  ∫ g, setSupportFunctional S g
    ∂stdGaussian (EuclideanSpace ℝ (Fin m))

/-- The actual-set centered support process in Theorem 9.7.1.

**Book Theorem 9.7.1.** -/
def setTwoSidedChevetProcess {m n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  setSupportFunctional S (HDP.gaussianMatrixAction A x) -
    setSupportGaussianWidth S * ‖x‖

omit hMM in
/-- Display (9.44) for the genuine nonempty bounded support set.

**Book Equation (9.44).** -/
theorem integral_setSupport_gaussianMatrixAction {m n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : S.Nonempty) (hSb : Bornology.IsBounded S)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ A, setSupportFunctional S (HDP.gaussianMatrixAction A x)
        ∂HDP.stdGaussianMatrixMeasure m n) =
      setSupportGaussianWidth S * ‖x‖ := by
  have h := integral_functional_gaussianMatrixAction_eq
    (setSupportSublinearFunctional S hS hSb)
    (setSupportRadius_nonneg S hS hSb)
    (setSupportFunctional_growth S hS hSb) x
  simpa [setSupportSublinearFunctional, setSupportGaussianWidth,
    mul_comm] using h

omit hMM in
/-- Mean support after Gaussian matrix action equals `‖x‖ w(S)`. The generic centered functional process specializes exactly to the
actual support-function process.

**Book Equation (9.44).** -/
theorem functionalDeviationProcess_setSupport_eq {m n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : S.Nonempty) (hSb : Bornology.IsBounded S)
    (x : EuclideanSpace ℝ (Fin n)) :
    functionalDeviationProcess (setSupportSublinearFunctional S hS hSb) x =
      setTwoSidedChevetProcess S x := by
  funext A
  simp only [functionalDeviationProcess, setTwoSidedChevetProcess,
    setSupportSublinearFunctional]
  rw [integral_setSupport_gaussianMatrixAction S hS hSb x]

omit hMM in
/-- A uniform Euclidean norm bound controls every finite Gaussian
complexity. This supplies the finiteness certificate for bounded `T`.

**Lean implementation helper.** -/
theorem gaussianComplexity_le_norm_bound {n : ℕ}
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    {C : ℝ} (hC : ∀ x ∈ F, ‖x‖ ≤ C) :
    HDP.Chapter7.gaussianComplexity F ≤ C * Real.sqrt n := by
  obtain ⟨x0, hx0⟩ := hF
  have hC0 : 0 ≤ C := (norm_nonneg x0).trans (hC x0 hx0)
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin n),
      HDP.Chapter7.finiteGaussianAbsSupport F g ≤ C * ‖g‖ := by
    intro g
    rw [HDP.Chapter7.finiteGaussianAbsSupport_eq_sup' F ⟨x0, hx0⟩]
    apply Finset.sup'_le
    intro x hx
    calc
      |inner ℝ g x| ≤ ‖g‖ * ‖x‖ := abs_real_inner_le_norm g x
      _ ≤ ‖g‖ * C :=
        mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg g)
      _ = C * ‖g‖ := mul_comm _ _
  calc
    HDP.Chapter7.gaussianComplexity F =
        ∫ g, HDP.Chapter7.finiteGaussianAbsSupport F g
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := rfl
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin n), C * ‖g‖
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      integral_mono (HDP.Chapter7.integrable_finiteGaussianAbsSupport F)
        (ProbabilityTheory.IsGaussian.integrable_id.norm.const_mul C) hpoint
    _ = C * ∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      rw [integral_const_mul]
    _ ≤ C * Real.sqrt n := mul_le_mul_of_nonneg_left
      (HDP.Chapter7.integral_norm_stdGaussian_le_sqrt_card n) hC0

omit hMM in
/-- A nonempty bounded input set has finite Gaussian-complexity envelope.

**Lean implementation helper.** -/
theorem gaussianComplexityEnvelope_ne_top_of_isBounded {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : T.Nonempty) (hTb : Bornology.IsBounded T) :
    gaussianComplexityEnvelope T ≠ ⊤ := by
  obtain ⟨C, hC⟩ := hTb.exists_norm_le
  obtain ⟨x0, hx0⟩ := hT
  have hC0 : 0 ≤ C := (norm_nonneg x0).trans (hC x0 hx0)
  have hle : gaussianComplexityEnvelope T ≤
      ENNReal.ofReal (C * Real.sqrt n) := by
    unfold gaussianComplexityEnvelope
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    exact ENNReal.ofReal_le_ofReal
      (gaussianComplexity_le_norm_bound F hF
        (fun x hx ↦ hC x (hFT hx)))
  exact (hle.trans_lt ENNReal.ofReal_lt_top).ne

/-- Expected absolute-deviation envelope for the actual fixed support set
`S`, with only the input supremum interpreted through nonempty finite
subfamilies as in Remark 7.2.1.

**Book Remark 7.2.1.** -/
def setTwoSidedChevetExpectationEnvelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin m))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n))),
    ⨆ (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T),
    ⨆ (hF : F.Nonempty),
    letI : Nonempty ↑F := hF.to_subtype
    ENNReal.ofReal
      (∫ A, HDP.Chapter8.finiteProcessAbsoluteSup
          (HDP.Chapter8.finiteEuclideanProcess F
            (setTwoSidedChevetProcess S)) A
        ∂HDP.stdGaussianMatrixMeasure m n)

/-- Two-sided Chevet controls the deviation of support suprema under a Gaussian matrix. Extended-valued actual-support-set form of Book Theorem 9.7.1.

**Book Theorem 9.7.1.** -/
theorem theorem_9_7_1_twoSidedChevet_set_ENN {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : S.Nonempty) (hSb : Bornology.IsBounded S) :
    setTwoSidedChevetExpectationEnvelope T S ≤
      ENNReal.ofReal
          (generalMatrixDeviationConstant * setSupportRadius S) *
        gaussianComplexityEnvelope T := by
  unfold setTwoSidedChevetExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  letI : Nonempty ↑F := hF.to_subtype
  let f := setSupportSublinearFunctional S hS hSb
  have hproc : functionalDeviationProcess (m := m) (n := n) f =
      setTwoSidedChevetProcess S := by
    funext x
    exact functionalDeviationProcess_setSupport_eq S hS hSb x
  have hmain := theorem_9_6_3_generalMatrixDeviation
    (m := m) (n := n) f (setSupportRadius_nonneg S hS hSb)
    (setSupportFunctional_growth S hS hSb) F hF
  have hcoef : 0 ≤ generalMatrixDeviationConstant * setSupportRadius S :=
    mul_nonneg generalMatrixDeviationConstant_pos.le
      (setSupportRadius_nonneg S hS hSb)
  have hcomplexity :
      ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) ≤
        gaussianComplexityEnvelope T := by
    unfold gaussianComplexityEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  calc
    ENNReal.ofReal
        (∫ A, HDP.Chapter8.finiteProcessAbsoluteSup
            (HDP.Chapter8.finiteEuclideanProcess F
              (setTwoSidedChevetProcess S)) A
          ∂HDP.stdGaussianMatrixMeasure m n) =
        ENNReal.ofReal
          (∫ A, HDP.Chapter8.finiteProcessAbsoluteSup
              (HDP.Chapter8.finiteEuclideanProcess F
                (functionalDeviationProcess f)) A
            ∂HDP.stdGaussianMatrixMeasure m n) := by rw [hproc]
    _ ≤ ENNReal.ofReal (generalMatrixDeviationConstant *
          setSupportRadius S * HDP.Chapter7.gaussianComplexity F) :=
      ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal
          (generalMatrixDeviationConstant * setSupportRadius S) *
        ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal
          (generalMatrixDeviationConstant * setSupportRadius S) *
        gaussianComplexityEnvelope T := by gcongr

/-- Two-sided Chevet controls the deviation of support suprema under a Gaussian matrix. Genuine nonempty bounded-set form. The left side
uses the actual support function of `S`, centered by its actual Gaussian
width; boundedness certifies that both extended envelopes convert safely to
ordinary real numbers.

**Book Theorem 9.7.1.** -/
theorem theorem_9_7_1_twoSidedChevet_set {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hT : T.Nonempty) (hS : S.Nonempty)
    (hTb : Bornology.IsBounded T) (hSb : Bornology.IsBounded S) :
    (setTwoSidedChevetExpectationEnvelope T S).toReal ≤
      generalMatrixDeviationConstant * setSupportRadius S *
        (gaussianComplexityEnvelope T).toReal := by
  have hmain := theorem_9_7_1_twoSidedChevet_set_ENN T S hS hSb
  have hγtop := gaussianComplexityEnvelope_ne_top_of_isBounded hT hTb
  have hcoef : 0 ≤ generalMatrixDeviationConstant * setSupportRadius S :=
    mul_nonneg generalMatrixDeviationConstant_pos.le
      (setSupportRadius_nonneg S hS hSb)
  have hrhs : ENNReal.ofReal
        (generalMatrixDeviationConstant * setSupportRadius S) *
      gaussianComplexityEnvelope T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hγtop
  have hreal := ENNReal.toReal_mono hrhs hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef] at hreal
  exact hreal

/-! The printed theorem allows arbitrary bounded `T` and `S`.  Its safe
finite-subfamily API below is retained only for compatibility.  The canonical
source theorem is `theorem_9_7_1_twoSidedChevet_set`, where the support set is
fixed before centering. -/

/-- Radius envelope of an arbitrary Euclidean set.

**Lean implementation helper.** -/
def setFiniteRadiusEnvelope {m : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m))) : ℝ≥0∞ :=
  ⨆ (G : Finset (EuclideanSpace ℝ (Fin m)))
      (_hGS : (G : Set (EuclideanSpace ℝ (Fin m))) ⊆ S)
      (_hG : G.Nonempty),
    ENNReal.ofReal (HDP.Chapter7.finiteRadius G)

/-- Expected two-sided Chevet-deviation envelope over finite subfamilies of
both arbitrary source sets.

**Lean implementation helper.** -/
def twoSidedChevetExpectationEnvelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin m))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n))),
    ⨆ (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T),
    ⨆ (hF : F.Nonempty),
    letI : Nonempty ↑F := hF.to_subtype
    ⨆ (G : Finset (EuclideanSpace ℝ (Fin m))),
    ⨆ (_hGS : (G : Set (EuclideanSpace ℝ (Fin m))) ⊆ S),
    ⨆ (_hG : G.Nonempty),
    ENNReal.ofReal
      (∫ A, finiteTwoSidedChevetDeviation F G A
        ∂HDP.stdGaussianMatrixMeasure m n)

/-- Finite-subfamily compatibility envelope for Book Theorem 9.7.1.

**Book Theorem 9.7.1.** -/
theorem theorem_9_7_1_twoSidedChevet_envelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin m))) :
    twoSidedChevetExpectationEnvelope T S ≤
      ENNReal.ofReal generalMatrixDeviationConstant *
        gaussianComplexityEnvelope T * setFiniteRadiusEnvelope S := by
  unfold twoSidedChevetExpectationEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  apply iSup_le
  intro G
  apply iSup_le
  intro hGS
  apply iSup_le
  intro hG
  letI : Nonempty ↑F := hF.to_subtype
  letI : Nonempty ↑G := hG.to_subtype
  have hmain := theorem_9_7_1_twoSidedChevet F G hF hG
  have hcomplexity :
      ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) ≤
        gaussianComplexityEnvelope T := by
    unfold gaussianComplexityEnvelope
    exact le_iSup_of_le F
      (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  have hradius : ENNReal.ofReal (HDP.Chapter7.finiteRadius G) ≤
      setFiniteRadiusEnvelope S := by
    unfold setFiniteRadiusEnvelope
    exact le_iSup_of_le G
      (le_iSup_of_le hGS (le_iSup_of_le hG le_rfl))
  have hC : 0 ≤ generalMatrixDeviationConstant :=
    generalMatrixDeviationConstant_pos.le
  have hgamma : 0 ≤ HDP.Chapter7.gaussianComplexity F :=
    HDP.Chapter7.gaussianComplexity_nonneg F
  calc
    ENNReal.ofReal
        (∫ A, finiteTwoSidedChevetDeviation F G A
          ∂HDP.stdGaussianMatrixMeasure m n) ≤
        ENNReal.ofReal (generalMatrixDeviationConstant *
          HDP.Chapter7.gaussianComplexity F *
          HDP.Chapter7.finiteRadius G) :=
      ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal generalMatrixDeviationConstant *
        ENNReal.ofReal (HDP.Chapter7.gaussianComplexity F) *
          ENNReal.ofReal (HDP.Chapter7.finiteRadius G) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC hgamma),
        ENNReal.ofReal_mul hC]
    _ ≤ ENNReal.ofReal generalMatrixDeviationConstant *
        gaussianComplexityEnvelope T *
          ENNReal.ofReal (HDP.Chapter7.finiteRadius G) := by
      gcongr
    _ ≤ ENNReal.ofReal generalMatrixDeviationConstant *
        gaussianComplexityEnvelope T * setFiniteRadiusEnvelope S := by
      gcongr

end MajorizingMeasure

/-- Deterministic two-sided consequence at one point.

**Lean implementation helper.** -/
theorem support_between_of_chevetDeviation {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T)
    (A : Matrix (Fin m) (Fin n) ℝ) {delta : ℝ}
    (hdev : finiteTwoSidedChevetDeviation T S A ≤ delta) :
    (HDP.Chapter7.gaussianWidth S * ‖x‖ - delta ≤
        finiteSupportFunctional S (HDP.gaussianMatrixAction A x)) ∧
      (finiteSupportFunctional S (HDP.gaussianMatrixAction A x) ≤
        HDP.Chapter7.gaussianWidth S * ‖x‖ + delta) := by
  have h := (abs_support_sub_width_le_finiteTwoSidedChevetDeviation
    T S hx A).trans hdev
  rw [abs_le] at h
  constructor <;> linarith

/-- The one-sided Chevet consequence.

**Lean implementation helper.** -/
theorem support_le_width_mul_radius_add_deviation {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) [Nonempty ↑T]
    (S : Finset (EuclideanSpace ℝ (Fin m)))
    (hT : T.Nonempty) (hS : S.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    finiteSupportFunctional S (HDP.gaussianMatrixAction A x) ≤
      HDP.Chapter7.gaussianWidth S * HDP.Chapter7.finiteRadius T +
        finiteTwoSidedChevetDeviation T S A := by
  have hpoint := (support_between_of_chevetDeviation
    T S hx A (le_refl _)).2
  have hw : 0 ≤ HDP.Chapter7.gaussianWidth S :=
    HDP.Chapter7.gaussianWidth_nonneg S hS
  have hr := HDP.Chapter7.norm_le_finiteRadius T hT hx
  have hmul := mul_le_mul_of_nonneg_left hr hw
  linarith

end

end HDP.Chapter9

end Source_17_TwoSidedChevet

/-! ## Material formerly in `18_DvoretzkyMilman.lean` -/

section Source_18_DvoretzkyMilman

/-!
# Book Chapter 9, §9.7: Dvoretzky--Milman via random images

The convex body is the **closed** convex hull.  For an arbitrary bounded set
the ordinary convex hull need not be closed, while the support function is
unchanged by taking this closure.  The inner radius is used only when it is
nonnegative; this is the exceptional case suppressed in the printed prose.

Exercise 9.40 is proved from first principles below.  The difficult reverse
inclusion uses Mathlib's geometric Hahn--Banach theorem together with the
Fréchet--Riesz representation of a continuous functional.
-/

open InnerProductSpace MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter9

noncomputable section

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Closed convex hull used by §9.7. This agrees with
`closure (convexHull ℝ T)` by `closedConvexHull_eq_closure_convexHull`.

**Book Section 9.7.** -/
def closedConvexHullSet {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] (T : Set E) : Set E :=
  closedConvexHull ℝ T

/-- Homogeneous support inequalities corresponding to two centered balls.

**Lean implementation helper.** -/
def FiniteSupportSandwich {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m)))
    (rMinus rPlus : ℝ) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin m),
    rMinus * ‖y‖ ≤ finiteSupportFunctional T y ∧
      finiteSupportFunctional T y ≤ rPlus * ‖y‖

/-- The corrected closed-hull ball sandwich.

**Lean implementation helper.** -/
def ClosedHullBallSandwich {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m)))
    (rMinus rPlus : ℝ) : Prop :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rMinus ⊆
      closedConvexHullSet (↑T : Set (EuclideanSpace ℝ (Fin m))) ∧
    closedConvexHullSet (↑T : Set (EuclideanSpace ℝ (Fin m))) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rPlus

/-- A continuous linear functional is bounded above on a closed convex hull
by the finite support function of its generators.

**Lean implementation helper.** -/
theorem inner_le_finiteSupport_of_mem_closedConvexHull {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m))) (hT : T.Nonempty)
    (y z : EuclideanSpace ℝ (Fin m))
    (hz : z ∈ closedConvexHullSet
      (↑T : Set (EuclideanSpace ℝ (Fin m)))) :
    inner ℝ y z ≤ finiteSupportFunctional T y := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := innerSL ℝ y
  let H : Set (EuclideanSpace ℝ (Fin m)) :=
    L ⁻¹' Set.Iic (finiteSupportFunctional T y)
  have hTH : (↑T : Set (EuclideanSpace ℝ (Fin m))) ⊆ H := by
    intro t ht
    change inner ℝ y t ≤ finiteSupportFunctional T y
    exact HDP.Chapter7.inner_le_finiteGaussianSupport T hT ht y
  have hconv : Convex ℝ H := by
    exact (convex_Iic (finiteSupportFunctional T y)).linear_preimage
      L.toLinearMap
  have hclosed : IsClosed H := by
    exact isClosed_Iic.preimage L.continuous
  exact closedConvexHull_min hTH hconv hclosed hz

/-- Support upper bounds put every generator, and hence its closed convex
hull, in the outer Euclidean ball.

**Lean implementation helper.** -/
theorem closedConvexHull_subset_closedBall_of_supportUpper {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m))) (hT : T.Nonempty)
    {r : ℝ} (hr : 0 ≤ r)
    (hupper : ∀ y : EuclideanSpace ℝ (Fin m),
      finiteSupportFunctional T y ≤ r * ‖y‖) :
    closedConvexHullSet (↑T : Set (EuclideanSpace ℝ (Fin m))) ⊆
      Metric.closedBall 0 r := by
  apply closedConvexHull_min
  · intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    have hpoint := HDP.Chapter7.inner_le_finiteGaussianSupport
      T hT ht t
    have hu := hupper t
    have hsq : inner ℝ t t = ‖t‖ ^ 2 := real_inner_self_eq_norm_sq t
    rw [hsq] at hpoint
    change ‖t‖ ^ 2 ≤ finiteSupportFunctional T t at hpoint
    by_cases ht0 : ‖t‖ = 0
    · simpa [ht0] using hr
    · have htpos : 0 < ‖t‖ := lt_of_le_of_ne (norm_nonneg t) (Ne.symm ht0)
      nlinarith
  · exact convex_closedBall 0 r
  · exact Metric.isClosed_closedBall

/-- A homogeneous support lower bound contains the corresponding centered
ball in the closed convex hull.

**Lean implementation helper.** -/
theorem closedBall_subset_closedConvexHull_of_supportLower {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m))) (hT : T.Nonempty)
    {r : ℝ} (_hr : 0 ≤ r)
    (hlower : ∀ y : EuclideanSpace ℝ (Fin m),
      r * ‖y‖ ≤ finiteSupportFunctional T y) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r ⊆
      closedConvexHullSet (↑T : Set (EuclideanSpace ℝ (Fin m))) := by
  intro z hz
  by_contra hzHull
  obtain ⟨L, u, hLu, huLz⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ))
    (isClosed_closedConvexHull (𝕜 := ℝ)) hzHull
  let y : EuclideanSpace ℝ (Fin m) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm L
  have hLy : ∀ w : EuclideanSpace ℝ (Fin m), L w = inner ℝ y w := by
    intro w
    exact (InnerProductSpace.toDual_symm_apply (x := w) (y := L)).symm
  have hsupp_lt : finiteSupportFunctional T y < u := by
    rw [finiteSupportFunctional,
      HDP.Chapter7.finiteGaussianSupport_eq_sup' T hT]
    obtain ⟨t, ht, hmax⟩ :=
      Finset.exists_mem_eq_sup' hT (fun q => inner ℝ y q)
    rw [hmax, ← hLy t]
    exact hLu t (subset_closedConvexHull ht)
  have hzNorm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hLz : L z ≤ ‖y‖ * r := by
    rw [hLy z]
    exact (real_inner_le_norm y z).trans
      (mul_le_mul_of_nonneg_left hzNorm (norm_nonneg y))
  have hl := hlower y
  nlinarith

/-- From a hull sandwich to the equivalent homogeneous support inequalities.

**Lean implementation helper.** -/
theorem finiteSupportSandwich_of_closedHullBallSandwich {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m))) (hT : T.Nonempty)
    {rMinus rPlus : ℝ} (hrMinus : 0 ≤ rMinus)
    (hHull : ClosedHullBallSandwich T rMinus rPlus) :
    FiniteSupportSandwich T rMinus rPlus := by
  intro y
  constructor
  · by_cases hy : y = 0
    · subst y
      simp [finiteSupportFunctional,
        HDP.Chapter7.finiteGaussianSupport_eq_sup' T hT]
    · have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
      let v : EuclideanSpace ℝ (Fin m) := ‖y‖⁻¹ • y
      have hvnorm : ‖v‖ = 1 := by
        simp [v, norm_smul, hynorm.ne']
      let z : EuclideanSpace ℝ (Fin m) := rMinus • v
      have hzball : z ∈ Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin m)) rMinus := by
        rw [Metric.mem_closedBall, dist_zero_right]
        simp [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrMinus,
          hvnorm]
      have hzhull := hHull.1 hzball
      have hzsupport := inner_le_finiteSupport_of_mem_closedConvexHull
        T hT y z hzhull
      have hinner : inner ℝ y z = rMinus * ‖y‖ := by
        simp only [z, v, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [hynorm.ne']
      rw [hinner] at hzsupport
      exact hzsupport
  · rw [finiteSupportFunctional,
      HDP.Chapter7.finiteGaussianSupport_eq_sup' T hT]
    apply Finset.sup'_le
    intro t ht
    have htHull : t ∈ closedConvexHullSet
        (↑T : Set (EuclideanSpace ℝ (Fin m))) :=
      subset_closedConvexHull ht
    have htBall := hHull.2 htHull
    have htNorm : ‖t‖ ≤ rPlus := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using htBall
    calc
      inner ℝ y t ≤ ‖y‖ * ‖t‖ := real_inner_le_norm y t
      _ ≤ ‖y‖ * rPlus :=
        mul_le_mul_of_nonneg_left htNorm (norm_nonneg y)
      _ = rPlus * ‖y‖ := mul_comm _ _

/-- Finite compatibility engine for Exercise 9.40.

**Book Exercise 9.40.** -/
theorem exercise_9_40_support_iff_closedHullBallSandwich_finite {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m))) (hT : T.Nonempty)
    {rMinus rPlus : ℝ} (hrMinus : 0 ≤ rMinus)
    (hrPlus : 0 ≤ rPlus) :
    FiniteSupportSandwich T rMinus rPlus ↔
      ClosedHullBallSandwich T rMinus rPlus := by
  constructor
  · intro hSupport
    exact ⟨
      closedBall_subset_closedConvexHull_of_supportLower
        T hT hrMinus (fun y => (hSupport y).1),
      closedConvexHull_subset_closedBall_of_supportUpper
        T hT hrPlus (fun y => (hSupport y).2)⟩
  · exact finiteSupportSandwich_of_closedHullBallSandwich
      T hT hrMinus

/-! ### Exercise 9.40 for arbitrary closed bounded sets -/

/-- The ordinary real support function of a nonempty bounded Euclidean set.
The proof arguments make the finiteness preconditions explicit at every use.

**Lean implementation helper.** -/
def boundedSetSupportFunctional {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (_hV : V.Nonempty) (_hVb : Bornology.IsBounded V)
    (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  sSup ((fun x => inner ℝ y x) '' V)

/-- Homogeneous support inequalities for a nonempty bounded set.

**Lean implementation helper.** -/
def BoundedSetSupportSandwich {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    (rMinus rPlus : ℝ) : Prop :=
  ∀ y,
    rMinus * ‖y‖ ≤ boundedSetSupportFunctional V hV hVb y ∧
      boundedSetSupportFunctional V hV hVb y ≤ rPlus * ‖y‖

/-- Ball sandwich for the closed convex hull of an arbitrary set.

**Lean implementation helper.** -/
def SetClosedHullBallSandwich {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (rMinus rPlus : ℝ) : Prop :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rMinus ⊆
      closedConvexHullSet V ∧
    closedConvexHullSet V ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rPlus

/-- The exact ball sandwich from Exercise 9.40, using the ordinary convex hull.

**Book Exercise 9.40.** -/
def SetConvexHullBallSandwich {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (rMinus rPlus : ℝ) : Prop :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rMinus ⊆
      convexHull ℝ V ∧
    convexHull ℝ V ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rPlus

/-- The support values of a bounded set are bounded above in every direction.

**Lean implementation helper.** -/
theorem boundedSetSupport_bddAbove {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hVb : Bornology.IsBounded V)
    (y : EuclideanSpace ℝ (Fin m)) :
    BddAbove ((fun x => inner ℝ y x) '' V) := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := innerSL ℝ y
  have hb : Bornology.IsBounded (L '' V) :=
    Bornology.IsBounded.image L hVb
  simpa [L] using hb.bddAbove

/-- Every point of a bounded set has directional inner product at most the set's support function.

**Lean implementation helper.** -/
theorem inner_le_boundedSetSupport {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ V)
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ y x ≤ boundedSetSupportFunctional V hV hVb y := by
  apply le_csSup (boundedSetSupport_bddAbove V hVb y)
  exact ⟨x, hx, rfl⟩

/-- A continuous functional is bounded by the support function on the closed
convex hull.

**Lean implementation helper.** -/
theorem inner_le_boundedSetSupport_of_mem_closedConvexHull {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    (y z : EuclideanSpace ℝ (Fin m))
    (hz : z ∈ closedConvexHullSet V) :
    inner ℝ y z ≤ boundedSetSupportFunctional V hV hVb y := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := innerSL ℝ y
  let H : Set (EuclideanSpace ℝ (Fin m)) :=
    L ⁻¹' Set.Iic (boundedSetSupportFunctional V hV hVb y)
  have hVH : V ⊆ H := by
    intro x hx
    change inner ℝ y x ≤ boundedSetSupportFunctional V hV hVb y
    exact inner_le_boundedSetSupport V hV hVb hx y
  have hconv : Convex ℝ H :=
    (convex_Iic (boundedSetSupportFunctional V hV hVb y)).linear_preimage
      L.toLinearMap
  have hclosed : IsClosed H := isClosed_Iic.preimage L.continuous
  exact closedConvexHull_min hVH hconv hclosed hz

/-- A uniform upper bound on the support function places the closed convex hull inside the corresponding ball.

**Lean implementation helper.** -/
theorem closedConvexHull_subset_closedBall_of_boundedSetSupportUpper {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    {r : ℝ} (hr : 0 ≤ r)
    (hupper : ∀ y,
      boundedSetSupportFunctional V hV hVb y ≤ r * ‖y‖) :
    closedConvexHullSet V ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r := by
  apply closedConvexHull_min
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hpoint := inner_le_boundedSetSupport V hV hVb hx x
    have hu := hupper x
    rw [real_inner_self_eq_norm_sq] at hpoint
    by_cases hx0 : ‖x‖ = 0
    · simpa [hx0] using hr
    · have hxpos : 0 < ‖x‖ :=
        lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
      nlinarith
  · exact convex_closedBall 0 r
  · exact Metric.isClosed_closedBall

/-- A uniform lower bound on the support function places the corresponding ball inside the closed convex hull.

**Lean implementation helper.** -/
theorem closedBall_subset_closedConvexHull_of_boundedSetSupportLower {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    {r : ℝ} (_hr : 0 ≤ r)
    (hlower : ∀ y,
      r * ‖y‖ ≤ boundedSetSupportFunctional V hV hVb y) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r ⊆
      closedConvexHullSet V := by
  intro z hz
  by_contra hzHull
  obtain ⟨L, u, hLu, huLz⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ))
    (isClosed_closedConvexHull (𝕜 := ℝ)) hzHull
  let y : EuclideanSpace ℝ (Fin m) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm L
  have hLy : ∀ w, L w = inner ℝ y w := by
    intro w
    exact (InnerProductSpace.toDual_symm_apply (x := w) (y := L)).symm
  have hsupp_le : boundedSetSupportFunctional V hV hVb y ≤ u := by
    rw [boundedSetSupportFunctional]
    apply csSup_le (hV.image fun x => inner ℝ y x)
    rintro _ ⟨x, hx, rfl⟩
    change inner ℝ y x ≤ u
    rw [← hLy x]
    exact (hLu x (subset_closedConvexHull hx)).le
  have hzNorm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hLz : L z ≤ ‖y‖ * r := by
    rw [hLy z]
    exact (real_inner_le_norm y z).trans
      (mul_le_mul_of_nonneg_left hzNorm (norm_nonneg y))
  have hl := hlower y
  nlinarith

/-- A ball sandwich for the closed convex hull yields the equivalent two-sided support-function bounds.

**Lean implementation helper.** -/
theorem boundedSetSupportSandwich_of_setClosedHullBallSandwich {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    {rMinus rPlus : ℝ} (hrMinus : 0 ≤ rMinus)
    (hHull : SetClosedHullBallSandwich V rMinus rPlus) :
    BoundedSetSupportSandwich V hV hVb rMinus rPlus := by
  intro y
  constructor
  · by_cases hy : y = 0
    · subst y
      simp only [norm_zero, mul_zero]
      obtain ⟨x, hx⟩ := hV
      exact le_csSup (boundedSetSupport_bddAbove V hVb 0)
        ⟨x, hx, by simp⟩
    · have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
      let v : EuclideanSpace ℝ (Fin m) := ‖y‖⁻¹ • y
      have hvnorm : ‖v‖ = 1 := by
        simp [v, norm_smul, hynorm.ne']
      let z : EuclideanSpace ℝ (Fin m) := rMinus • v
      have hzball : z ∈ Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin m)) rMinus := by
        rw [Metric.mem_closedBall, dist_zero_right]
        simp [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrMinus,
          hvnorm]
      have hzhull := hHull.1 hzball
      have hzsupport := inner_le_boundedSetSupport_of_mem_closedConvexHull
        V hV hVb y z hzhull
      have hinner : inner ℝ y z = rMinus * ‖y‖ := by
        simp only [z, v, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [hynorm.ne']
      rw [hinner] at hzsupport
      exact hzsupport
  · rw [boundedSetSupportFunctional]
    apply csSup_le (hV.image fun x => inner ℝ y x)
    rintro _ ⟨x, hx, rfl⟩
    have hxHull : x ∈ closedConvexHullSet V := subset_closedConvexHull hx
    have hxBall := hHull.2 hxHull
    have hxNorm : ‖x‖ ≤ rPlus := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxBall
    calc
      inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
      _ ≤ ‖y‖ * rPlus :=
        mul_le_mul_of_nonneg_left hxNorm (norm_nonneg y)
      _ = rPlus * ‖y‖ := mul_comm _ _

/-- Support/ball duality for an arbitrary nonempty bounded set, stated first
for the always-correct closed convex hull.

**Lean implementation helper.** -/
theorem boundedSetSupport_iff_setClosedHullBallSandwich {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVb : Bornology.IsBounded V)
    {rMinus rPlus : ℝ} (hrMinus : 0 ≤ rMinus)
    (hrPlus : 0 ≤ rPlus) :
    BoundedSetSupportSandwich V hV hVb rMinus rPlus ↔
      SetClosedHullBallSandwich V rMinus rPlus := by
  constructor
  · intro hSupport
    exact ⟨
      closedBall_subset_closedConvexHull_of_boundedSetSupportLower
        V hV hVb hrMinus (fun y => (hSupport y).1),
      closedConvexHull_subset_closedBall_of_boundedSetSupportUpper
        V hV hVb hrPlus (fun y => (hSupport y).2)⟩
  · exact boundedSetSupportSandwich_of_setClosedHullBallSandwich
      V hV hVb hrMinus

/-- The parameter space records nonnegative coefficients summing to one together with source points.

**Lean implementation helper.** -/
private def convexCombinationParameters {m k : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m))) :
    Set ((Fin k → ℝ) × (Fin k → EuclideanSpace ℝ (Fin m))) :=
  stdSimplex ℝ (Fin k) ×ˢ {p | ∀ i, p i ∈ V}

/-- The convex-combination map sends coefficients and source points to their weighted sum.

**Lean implementation helper.** -/
private def convexCombinationMap {m k : ℕ}
    (q : (Fin k → ℝ) × (Fin k → EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) :=
  ∑ i, q.1 i • q.2 i

/-- The image of the convex-combination map is the set of combinations using a fixed number of points.

**Lean implementation helper.** -/
private def convexCombinationImage {m k : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  convexCombinationMap (k := k) '' convexCombinationParameters (k := k) V

/-- Convex combinations using a fixed number of points from a compact set form a compact set.

**Lean implementation helper.** -/
private theorem isCompact_convexCombinationImage {m k : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin m))} (hVc : IsCompact V) :
    IsCompact (convexCombinationImage (k := k) V) := by
  apply IsCompact.image
  · exact (isCompact_stdSimplex ℝ (Fin k)).prod
      (isCompact_pi_infinite fun _ => hVc)
  · change Continuous (fun q :
        (Fin k → ℝ) × (Fin k → EuclideanSpace ℝ (Fin m)) =>
      ∑ i, q.1 i • q.2 i)
    fun_prop

/-- The convex hull is the union of the finite-point convex-combination images.

**Lean implementation helper.** -/
private theorem convexHull_eq_iUnion_convexCombinationImage {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m))) (_hV : V.Nonempty) :
    convexHull ℝ V = ⋃ k : Fin (m + 2), convexCombinationImage (k := k.1) V := by
  apply Set.Subset.antisymm
  · intro x hx
    let t := Caratheodory.minCardFinsetOfMemConvexHull hx
    have htV : (t : Set (EuclideanSpace ℝ (Fin m))) ⊆ V :=
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
    have htAI : AffineIndependent ℝ
        ((↑) : t → EuclideanSpace ℝ (Fin m)) :=
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
    have hxt : x ∈ convexHull ℝ
        (t : Set (EuclideanSpace ℝ (Fin m))) :=
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx
    have htcard : t.card ≤ m + 1 := by
      calc
        t.card = Fintype.card t := by simp
        _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range
              ((↑) : t → EuclideanSpace ℝ (Fin m)))) + 1 :=
          htAI.card_le_finrank_succ
        _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
        _ = m + 1 := by simp
    let k : Fin (m + 2) := ⟨t.card, Nat.lt_succ_iff.mpr htcard⟩
    let e : t ≃ Fin t.card := Fintype.equivOfCardEq (by simp)
    obtain ⟨w, hw0, hwsum, hwx⟩ := Finset.mem_convexHull'.mp hxt
    let a : Fin t.card → ℝ := fun i => w (e.symm i).1
    let p : Fin t.card → EuclideanSpace ℝ (Fin m) :=
      fun i => (e.symm i).1
    have ha0 : ∀ i, 0 ≤ a i := by
      intro i
      exact hw0 _ (e.symm i).2
    have hasum : ∑ i, a i = 1 := by
      calc
        ∑ i, a i = ∑ q : t, w q.1 := by
          exact (e.symm.sum_comp fun q : t => w q.1)
        _ = ∑ y ∈ t, w y := Finset.sum_coe_sort t w
        _ = 1 := hwsum
    have hpV : ∀ i, p i ∈ V := by
      intro i
      exact htV (e.symm i).2
    have hcombo : convexCombinationMap (a, p) = x := by
      rw [convexCombinationMap]
      calc
        ∑ i, a i • p i = ∑ q : t, w q.1 • q.1 := by
          exact (e.symm.sum_comp fun q : t => w q.1 • q.1)
        _ = ∑ y ∈ t, w y • y :=
          Finset.sum_coe_sort t (fun y => w y • y)
        _ = x := hwx
    rw [Set.mem_iUnion]
    refine ⟨k, ?_⟩
    change x ∈ convexCombinationImage (k := t.card) V
    exact ⟨(a, p), ⟨⟨ha0, hasum⟩, hpV⟩, hcombo⟩
  · apply Set.iUnion_subset
    intro k x hx
    rcases hx with ⟨q, hq, rfl⟩
    have hsumpos : 0 < ∑ i, q.1 i := by
      rw [hq.1.2]
      exact zero_lt_one
    have hmem := Finset.univ.centerMass_mem_convexHull
      (fun i _ => hq.1.1 i) hsumpos (fun i _ => hq.2 i)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hq.1.2] at hmem
    exact hmem

/-- The convex hull of a closed bounded Euclidean set is compact. The proof
uses Carathéodory to express it as a finite union of compact parameter images.

**Lean implementation helper.** -/
theorem isCompact_euclidean_convexHull_of_isClosed_isBounded {m : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin m))} (hV : V.Nonempty)
    (hVc : IsClosed V) (hVb : Bornology.IsBounded V) :
    IsCompact (convexHull ℝ V) := by
  rw [convexHull_eq_iUnion_convexCombinationImage V hV]
  exact isCompact_iUnion fun k =>
    isCompact_convexCombinationImage
      (Metric.isCompact_of_isClosed_isBounded hVc hVb)

/-- For a closed bounded Euclidean set, the closed and ordinary convex hulls
agree.

**Lean implementation helper.** -/
theorem closedConvexHullSet_eq_convexHull_of_isClosed_isBounded {m : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin m))} (hV : V.Nonempty)
    (hVc : IsClosed V) (hVb : Bornology.IsBounded V) :
    closedConvexHullSet V = convexHull ℝ V := by
  rw [closedConvexHullSet, closedConvexHull_eq_closure_convexHull,
    (isCompact_euclidean_convexHull_of_isClosed_isBounded
      hV hVc hVb).isClosed.closure_eq]

/-- Support-function bounds are equivalent to a closed-convex-hull ball sandwich. For an arbitrary nonempty,
closed, bounded set `V`, its real support function is sandwiched by the two
Euclidean norms exactly when its ordinary convex hull is sandwiched by the
corresponding centered balls.

**Book Exercise 9.40.** -/
theorem exercise_9_40_support_iff_closedHullBallSandwich {m : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin m)))
    (hV : V.Nonempty) (hVc : IsClosed V)
    (hVb : Bornology.IsBounded V)
    {rMinus rPlus : ℝ} (hrMinus : 0 ≤ rMinus)
    (hrPlus : 0 ≤ rPlus) :
    BoundedSetSupportSandwich V hV hVb rMinus rPlus ↔
      SetConvexHullBallSandwich V rMinus rPlus := by
  have hHull := boundedSetSupport_iff_setClosedHullBallSandwich
    V hV hVb hrMinus hrPlus
  have heq : closedConvexHullSet V = convexHull ℝ V :=
    closedConvexHullSet_eq_convexHull_of_isClosed_isBounded hV hVc hVb
  simpa only [SetClosedHullBallSandwich, SetConvexHullBallSandwich, heq]
    using hHull

/-! ## Random images -/

/-- Image of a finite set under a deterministic matrix.

**Lean implementation helper.** -/
def deterministicMatrixImageFinset {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin m)) :=
  T.image (deterministicMatrixAction A)

/-- The deterministic image of a nonempty finite set is nonempty.

**Lean implementation helper.** -/
theorem deterministicMatrixImageFinset_nonempty {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {T : Finset (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (deterministicMatrixImageFinset A T).Nonempty :=
  hT.image _

/-- Support-control event for a random image.

**Lean implementation helper.** -/
def RandomImageSupportEvent {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (rMinus rPlus : ℝ) : Set Ω :=
  {ω | FiniteSupportSandwich
    (deterministicMatrixImageFinset (A ω) T) rMinus rPlus}

/-- Closed-hull ball event for a random image.

**Lean implementation helper.** -/
def RandomImageHullEvent {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (rMinus rPlus : ℝ) : Set Ω :=
  {ω | ClosedHullBallSandwich
    (deterministicMatrixImageFinset (A ω) T) rMinus rPlus}

/-- The uniform support deviation produced by two-sided Chevet and Markov.

**Lean implementation helper.** -/
def RandomImageSupportDeviationEvent {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (width error : ℝ) : Set Ω :=
  {ω | ∀ y : EuclideanSpace ℝ (Fin m),
    |finiteSupportFunctional
        (deterministicMatrixImageFinset (A ω) T) y - width * ‖y‖| ≤
      error * ‖y‖}

/-- The radii `r_±` in Theorem 9.7.2.

**Book Theorem 9.7.2.** -/
def dvoretzkyMilmanInnerRadius (width error : ℝ) : ℝ :=
  width - error

/-- The outer Dvoretzky–Milman radius is the target width plus the allowed support error.

**Lean implementation helper.** -/
def dvoretzkyMilmanOuterRadius (width error : ℝ) : ℝ :=
  width + error

/-- Triangle-inequality step in the proof of Theorem 9.7.2.

**Book Theorem 9.7.2.** -/
theorem finiteSupportSandwich_of_uniformDeviation {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m)))
    (width error : ℝ)
    (hdev : ∀ y : EuclideanSpace ℝ (Fin m),
      |finiteSupportFunctional T y - width * ‖y‖| ≤ error * ‖y‖) :
    FiniteSupportSandwich T
      (dvoretzkyMilmanInnerRadius width error)
      (dvoretzkyMilmanOuterRadius width error) := by
  intro y
  have h := hdev y
  rw [abs_le] at h
  dsimp [dvoretzkyMilmanInnerRadius, dvoretzkyMilmanOuterRadius]
  constructor <;> nlinarith

/-- Uniform control of the random support deviation implies the corresponding two-sided support event.

**Lean implementation helper.** -/
theorem randomImageSupportDeviationEvent_subset_supportEvent {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (width error : ℝ) :
    RandomImageSupportDeviationEvent A T width error ⊆
      RandomImageSupportEvent A T
        (dvoretzkyMilmanInnerRadius width error)
        (dvoretzkyMilmanOuterRadius width error) := by
  intro ω hω
  exact finiteSupportSandwich_of_uniformDeviation
    (deterministicMatrixImageFinset (A ω) T) width error hω

/-- Two-sided support bounds imply the advertised inner and outer ball inclusions for the image hull.

**Lean implementation helper.** -/
theorem randomImageSupportEvent_subset_hullEvent {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {rMinus rPlus : ℝ} (hrMinus : 0 ≤ rMinus)
    (hrPlus : 0 ≤ rPlus) :
    RandomImageSupportEvent A T rMinus rPlus ⊆
      RandomImageHullEvent A T rMinus rPlus := by
  intro ω hω
  exact (exercise_9_40_support_iff_closedHullBallSandwich_finite
    (deterministicMatrixImageFinset (A ω) T)
    (deterministicMatrixImageFinset_nonempty (A ω) hT)
    hrMinus hrPlus).mp hω

/-! ### Canonical Gaussian proof of Theorem 9.7.2 -/

private noncomputable instance unitSphereSubtypeNonempty (m : ℕ) [NeZero m] :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  NormedSpace.sphere_nonempty_rclike ℝ (by norm_num)

/-- A deterministic dense sequence in the Euclidean unit sphere.

**Lean implementation helper.** -/
def unitSphereDensePoint (m : ℕ) [NeZero m] (k : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  (TopologicalSpace.denseSeq
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) k :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)

/-- Every point in the chosen dense enumeration of the unit sphere has norm one.

**Lean implementation helper.** -/
@[simp]
theorem norm_unitSphereDensePoint (m : ℕ) [NeZero m] (k : ℕ) :
    ‖unitSphereDensePoint m k‖ = 1 := by
  unfold unitSphereDensePoint
  rw [← dist_zero_right]
  exact (TopologicalSpace.denseSeq
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) k).property

/-- Increasing finite prefixes of the dense unit-sphere sequence.

**Lean implementation helper.** -/
def unitSpherePrefix (m : ℕ) [NeZero m] (k : ℕ) :
    Finset (EuclideanSpace ℝ (Fin m)) :=
  (Finset.range (k + 1)).image (unitSphereDensePoint m)

/-- Every finite prefix of the unit-sphere dense sequence is nonempty.

**Lean implementation helper.** -/
theorem unitSpherePrefix_nonempty (m : ℕ) [NeZero m] (k : ℕ) :
    (unitSpherePrefix m k).Nonempty := by
  exact ⟨unitSphereDensePoint m 0, Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩

/-- The finite prefixes of the unit-sphere dense sequence form an increasing family.

**Lean implementation helper.** -/
theorem unitSpherePrefix_mono (m : ℕ) [NeZero m] {k l : ℕ}
    (hkl : k ≤ l) : unitSpherePrefix m k ⊆ unitSpherePrefix m l := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hi
    omega), rfl⟩

/-- Every finite prefix has Gaussian complexity at most `sqrt m`.

**Lean implementation helper.** -/
theorem gaussianComplexity_unitSpherePrefix_le (m : ℕ) [NeZero m]
    (k : ℕ) :
    HDP.Chapter7.gaussianComplexity (unitSpherePrefix m k) ≤
      Real.sqrt m := by
  let N := unitSpherePrefix m k
  have hN : N.Nonempty := unitSpherePrefix_nonempty m k
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin m),
      HDP.Chapter7.finiteGaussianAbsSupport N g ≤ ‖g‖ := by
    intro g
    rw [HDP.Chapter7.finiteGaussianAbsSupport_eq_sup' N hN]
    apply Finset.sup'_le
    intro y hy
    calc
      |inner ℝ g y| ≤ ‖g‖ * ‖y‖ := abs_real_inner_le_norm g y
      _ = ‖g‖ := by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        rw [norm_unitSphereDensePoint, mul_one]
  calc
    HDP.Chapter7.gaussianComplexity N =
        ∫ g, HDP.Chapter7.finiteGaussianAbsSupport N g
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := rfl
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin m), ‖g‖
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
      exact integral_mono
        (HDP.Chapter7.integrable_finiteGaussianAbsSupport N)
        ProbabilityTheory.IsGaussian.integrable_id.norm hpoint
    _ ≤ Real.sqrt m :=
      HDP.Chapter7.integral_norm_stdGaussian_le_sqrt_card m

/-- Prefix deviations increase with the prefix.

**Lean implementation helper.** -/
theorem finiteTwoSidedChevetDeviation_prefix_mono {m n : ℕ}
    [NeZero m] (T : Finset (EuclideanSpace ℝ (Fin n)))
    (_hT : T.Nonempty) {k l : ℕ} (hkl : k ≤ l)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    letI : Nonempty ↑(unitSpherePrefix m k) :=
      (unitSpherePrefix_nonempty m k).to_subtype
    letI : Nonempty ↑(unitSpherePrefix m l) :=
      (unitSpherePrefix_nonempty m l).to_subtype
    finiteTwoSidedChevetDeviation (unitSpherePrefix m k) T B ≤
      finiteTwoSidedChevetDeviation (unitSpherePrefix m l) T B := by
  let Nk := unitSpherePrefix m k
  let Nl := unitSpherePrefix m l
  have hNk : Nk.Nonempty := unitSpherePrefix_nonempty m k
  have hNl : Nl.Nonempty := unitSpherePrefix_nonempty m l
  letI : Nonempty ↑Nk := hNk.to_subtype
  letI : Nonempty ↑Nl := hNl.to_subtype
  unfold finiteTwoSidedChevetDeviation
    HDP.Chapter8.finiteProcessAbsoluteSup
  apply Finset.sup'_le
  intro x hx
  let y : ↑Nl := ⟨x.1, unitSpherePrefix_mono m hkl x.2⟩
  simpa [HDP.Chapter8.finiteEuclideanProcess, y] using
    (Finset.le_sup'
      (fun z : ↑Nl ↦
        |HDP.Chapter8.finiteEuclideanProcess Nl
          (finiteTwoSidedChevetProcess T) z B|)
      (Finset.mem_univ y))

/-- Countable supremum of the finite-prefix deviations.

**Lean implementation helper.** -/
def dvoretzkyMilmanDeviationENN {m n : ℕ} [NeZero m]
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (B : Matrix (Fin n) (Fin m) ℝ) : ℝ≥0∞ :=
  ⨆ k : ℕ,
    letI : Nonempty ↑(unitSpherePrefix m k) :=
      (unitSpherePrefix_nonempty m k).to_subtype
    ENNReal.ofReal (finiteTwoSidedChevetDeviation
      (unitSpherePrefix m k) T B)

/-- The extended-real Dvoretzky–Milman deviation is measurable as a supremum of finite measurable deviations.

**Lean implementation helper.** -/
theorem measurable_dvoretzkyMilmanDeviationENN {m n : ℕ} [NeZero m]
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Measurable (dvoretzkyMilmanDeviationENN (m := m) T) := by
  apply Measurable.iSup
  intro k
  letI : Nonempty ↑(unitSpherePrefix m k) :=
    (unitSpherePrefix_nonempty m k).to_subtype
  exact ENNReal.measurable_ofReal.comp
    (measurable_finiteTwoSidedChevetDeviation
      (unitSpherePrefix m k) T hT)

/-- Monotone-convergence form of two-sided Chevet on the whole sphere.

**Lean implementation helper.** -/
theorem lintegral_dvoretzkyMilmanDeviationENN_le {m n : ℕ} [NeZero m]
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    (∫⁻ B, dvoretzkyMilmanDeviationENN T B
        ∂HDP.stdGaussianMatrixMeasure n m) ≤
      ENNReal.ofReal (generalMatrixDeviationConstant * Real.sqrt m *
        HDP.Chapter7.finiteRadius T) := by
  let F : ℕ → Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ := fun k B ↦
    letI : Nonempty ↑(unitSpherePrefix m k) :=
      (unitSpherePrefix_nonempty m k).to_subtype
    ENNReal.ofReal (finiteTwoSidedChevetDeviation
      (unitSpherePrefix m k) T B)
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    letI : Nonempty ↑(unitSpherePrefix m k) :=
      (unitSpherePrefix_nonempty m k).to_subtype
    exact ENNReal.measurable_ofReal.comp
      (measurable_finiteTwoSidedChevetDeviation
        (unitSpherePrefix m k) T hT)
  have hFmono : Monotone F := by
    intro k l hkl B
    exact ENNReal.ofReal_le_ofReal
      (finiteTwoSidedChevetDeviation_prefix_mono
        (m := m) (n := n) T hT hkl B)
  change (∫⁻ B, ⨆ k, F k B ∂HDP.stdGaussianMatrixMeasure n m) ≤ _
  rw [lintegral_iSup hFm hFmono]
  apply iSup_le
  intro k
  letI : Nonempty ↑(unitSpherePrefix m k) :=
    (unitSpherePrefix_nonempty m k).to_subtype
  letI : Nonempty ↑T := hT.to_subtype
  have hint := integrable_finiteTwoSidedChevetDeviation
    (unitSpherePrefix m k) T hT
  have hnonneg : ∀ B : Matrix (Fin n) (Fin m) ℝ,
      0 ≤ finiteTwoSidedChevetDeviation (unitSpherePrefix m k) T B := by
    intro B
    unfold finiteTwoSidedChevetDeviation
      HDP.Chapter8.finiteProcessAbsoluteSup
    let x : ↑(unitSpherePrefix m k) := Classical.choice inferInstance
    let f : ↑(unitSpherePrefix m k) → ℝ := fun z ↦
      |HDP.Chapter8.finiteEuclideanProcess (unitSpherePrefix m k)
        (finiteTwoSidedChevetProcess T) z B|
    exact (abs_nonneg _).trans
      (Finset.le_sup' f (Finset.mem_univ x))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hnonneg)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ B, finiteTwoSidedChevetDeviation (unitSpherePrefix m k) T B
        ∂HDP.stdGaussianMatrixMeasure n m) ≤
        generalMatrixDeviationConstant *
          HDP.Chapter7.gaussianComplexity (unitSpherePrefix m k) *
          HDP.Chapter7.finiteRadius T :=
      theorem_9_7_1_twoSidedChevet
        (unitSpherePrefix m k) T (unitSpherePrefix_nonempty m k) hT
    _ ≤ generalMatrixDeviationConstant * Real.sqrt m *
          HDP.Chapter7.finiteRadius T := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (gaussianComplexity_unitSpherePrefix_le m k)
          generalMatrixDeviationConstant_pos.le)
        (HDP.Chapter7.finiteRadius_nonneg T)

/-- Support of the transposed image equals the support process indexed by the
original set.

**Lean implementation helper.** -/
theorem finiteSupport_transposeImage_eq {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (y : EuclideanSpace ℝ (Fin m)) :
    finiteSupportFunctional
        (deterministicMatrixImageFinset B.transpose T) y =
      finiteSupportFunctional T (HDP.gaussianMatrixAction B y) := by
  rw [finiteSupportFunctional, finiteSupportFunctional,
    HDP.Chapter7.finiteGaussianSupport_eq_sup'
      (deterministicMatrixImageFinset B.transpose T)
      (deterministicMatrixImageFinset_nonempty B.transpose hT),
    HDP.Chapter7.finiteGaussianSupport_eq_sup' T hT]
  unfold deterministicMatrixImageFinset
  rw [Finset.sup'_image]
  apply Finset.sup'_congr hT rfl
  intro x hx
  simp only [HDP.gaussianMatrixAction_eq_toEuclideanLin]
  change inner ℝ y (B.transpose.toEuclideanLin x) =
    inner ℝ (B.toEuclideanLin y) x
  simp only [PiLp.inner_apply, Real.inner_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  change (∑ i : Fin m, y i * ∑ j : Fin n, B j i * x j) =
    ∑ j : Fin n, (∑ i : Fin m, B j i * y i) * x j
  calc
    (∑ i : Fin m, y i * ∑ j : Fin n, B j i * x j) =
        ∑ i : Fin m, ∑ j : Fin n, y i * (B j i * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin m, y i * (B j i * x j) :=
      Finset.sum_comm
    _ = ∑ j : Fin n, (∑ i : Fin m, B j i * y i) * x j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The corrected source conclusion: the outer inclusion always holds; the
inner inclusion is asserted only when the inner radius is nonnegative.

**Lean implementation helper.** -/
def DvoretzkyMilmanConclusion {m : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin m)))
    (rMinus rPlus : ℝ) : Prop :=
  closedConvexHullSet (↑T : Set (EuclideanSpace ℝ (Fin m))) ⊆
      Metric.closedBall 0 rPlus ∧
    (0 ≤ rMinus → Metric.closedBall 0 rMinus ⊆
      closedConvexHullSet (↑T : Set (EuclideanSpace ℝ (Fin m))))

/-- Weakening either radius preserves the Dvoretzky--Milman conclusion:
decrease the inner radius and increase the outer radius.

**Lean implementation helper.** -/
theorem DvoretzkyMilmanConclusion.mono {m : ℕ}
    {T : Finset (EuclideanSpace ℝ (Fin m))}
    {rMinus rPlus sMinus sPlus : ℝ}
    (h : DvoretzkyMilmanConclusion T rMinus rPlus)
    (hMinus : sMinus ≤ rMinus) (hPlus : rPlus ≤ sPlus) :
    DvoretzkyMilmanConclusion T sMinus sPlus := by
  constructor
  · exact h.1.trans (Metric.closedBall_subset_closedBall hPlus)
  · intro hsMinus
    exact (Metric.closedBall_subset_closedBall hMinus).trans
      (h.2 (hsMinus.trans hMinus))

/-- Absolute constant after the Markov step.

**Lean implementation helper.** -/
def dvoretzkyMilmanConstant
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] : ℝ :=
  100 * generalMatrixDeviationConstant

/-- The Dvoretzky–Milman constant is strictly positive.

**Lean implementation helper.** -/
theorem dvoretzkyMilmanConstant_pos
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] :
    0 < dvoretzkyMilmanConstant := by
  exact mul_pos (by norm_num) generalMatrixDeviationConstant_pos

/-- The finite-set Dvoretzky–Milman error combines Gaussian width and radius at the matrix-deviation scale.

**Lean implementation helper.** -/
def dvoretzkyMilmanError {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  dvoretzkyMilmanConstant * Real.sqrt m * HDP.Chapter7.finiteRadius T

/-- Dense-prefix control extends to every direction and hence to the required
hull inclusions.

**Lean implementation helper.** -/
theorem dvoretzkyMilmanConclusion_of_deviationENN_le {m n : ℕ}
    [NeZero m] (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (B : Matrix (Fin n) (Fin m) ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hdev : dvoretzkyMilmanDeviationENN T B ≤ ENNReal.ofReal error) :
    DvoretzkyMilmanConclusion
      (deterministicMatrixImageFinset B.transpose T)
      (dvoretzkyMilmanInnerRadius (HDP.Chapter7.gaussianWidth T) error)
      (dvoretzkyMilmanOuterRadius (HDP.Chapter7.gaussianWidth T) error) := by
  let E := EuclideanSpace ℝ (Fin m)
  let sphere := Metric.sphere (0 : E) 1
  let F : sphere → ℝ := fun y ↦
    |finiteSupportFunctional
      (deterministicMatrixImageFinset B.transpose T) y.1 -
        HDP.Chapter7.gaussianWidth T|
  have hFcont : Continuous F := by
    have himage := deterministicMatrixImageFinset_nonempty B.transpose hT
    have hsupp : Continuous (fun y : sphere ↦
        finiteSupportFunctional
          (deterministicMatrixImageFinset B.transpose T) y.1) :=
      ((finiteSupportSublinearFunctional
        (deterministicMatrixImageFinset B.transpose T) himage).continuous_of_growth
        (HDP.Chapter7.finiteRadius_nonneg _)
        (finiteSupportFunctional_growth _ himage)).comp continuous_subtype_val
    exact (hsupp.sub continuous_const).abs
  have hdense : ∀ k, F (TopologicalSpace.denseSeq sphere k) ≤ error := by
    intro k
    let N := unitSpherePrefix m k
    letI : Nonempty ↑N := (unitSpherePrefix_nonempty m k).to_subtype
    have hkN : unitSphereDensePoint m k ∈ N := by
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
    have hp := abs_support_sub_width_le_finiteTwoSidedChevetDeviation
      N T hkN B
    have hproc : F (TopologicalSpace.denseSeq sphere k) =
        |finiteSupportFunctional T
            (HDP.gaussianMatrixAction B (unitSphereDensePoint m k)) -
          HDP.Chapter7.gaussianWidth T *
            ‖unitSphereDensePoint m k‖| := by
      change |finiteSupportFunctional
          (deterministicMatrixImageFinset B.transpose T)
            (unitSphereDensePoint m k) - HDP.Chapter7.gaussianWidth T| = _
      rw [finiteSupport_transposeImage_eq B T hT,
        norm_unitSphereDensePoint, mul_one]
    have hof : ENNReal.ofReal (F (TopologicalSpace.denseSeq sphere k)) ≤
        dvoretzkyMilmanDeviationENN T B := by
      calc
        ENNReal.ofReal (F (TopologicalSpace.denseSeq sphere k)) ≤
            ENNReal.ofReal (finiteTwoSidedChevetDeviation N T B) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [hproc] using hp
        _ ≤ dvoretzkyMilmanDeviationENN T B := by
          exact le_iSup (fun j : ℕ ↦
            letI : Nonempty ↑(unitSpherePrefix m j) :=
              (unitSpherePrefix_nonempty m j).to_subtype
            ENNReal.ofReal (finiteTwoSidedChevetDeviation
              (unitSpherePrefix m j) T B)) k
    exact (ENNReal.ofReal_le_ofReal_iff herror).mp (hof.trans hdev)
  have hallSphere : ∀ y : sphere, F y ≤ error := by
    intro y
    have hclosedGood : IsClosed {q : sphere | F q ≤ error} :=
      isClosed_le hFcont continuous_const
    have hrangeGood : Set.range (TopologicalSpace.denseSeq sphere) ⊆
        {q : sphere | F q ≤ error} := by
      rintro _ ⟨k, rfl⟩
      exact hdense k
    have hyclosure : y ∈ closure (Set.range
        (TopologicalSpace.denseSeq sphere)) := by
      rw [(TopologicalSpace.denseRange_denseSeq sphere).closure_range]
      trivial
    exact (closure_minimal hrangeGood hclosedGood) hyclosure
  have huniform : ∀ y : EuclideanSpace ℝ (Fin m),
      |finiteSupportFunctional
          (deterministicMatrixImageFinset B.transpose T) y -
        HDP.Chapter7.gaussianWidth T * ‖y‖| ≤ error * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · subst y
      simp [finiteSupportFunctional,
        HDP.Chapter7.finiteGaussianSupport_eq_sup'
          _ (deterministicMatrixImageFinset_nonempty B.transpose hT)]
    · let q : sphere := ⟨‖y‖⁻¹ • y, by
          rw [Metric.mem_sphere, dist_zero_right]
          simp [norm_smul, norm_ne_zero_iff.mpr hy]⟩
      have hq := hallSphere q
      have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hyrepr : y = ‖y‖ • (q : E) := by
        simp [q, hypos.ne']
      have hpos := finiteSupportFunctional_posHom
        (deterministicMatrixImageFinset B.transpose T)
        (deterministicMatrixImageFinset_nonempty B.transpose hT)
        ‖y‖ hypos.le (q : E)
      have hqnorm : ‖(q : E)‖ = 1 := by
        rw [← dist_zero_right]
        exact q.property
      rw [hyrepr, hpos, norm_smul, Real.norm_eq_abs,
        abs_of_pos hypos, hqnorm, mul_one]
      rw [show ‖y‖ * finiteSupportFunctional
          (deterministicMatrixImageFinset B.transpose T) q -
          HDP.Chapter7.gaussianWidth T * ‖y‖ =
        ‖y‖ * (finiteSupportFunctional
          (deterministicMatrixImageFinset B.transpose T) q -
          HDP.Chapter7.gaussianWidth T) by ring,
        abs_mul, abs_of_pos hypos]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hypos.le
  have hsandwich := finiteSupportSandwich_of_uniformDeviation
    (deterministicMatrixImageFinset B.transpose T)
    (HDP.Chapter7.gaussianWidth T) error huniform
  have hrPlus : 0 ≤ dvoretzkyMilmanOuterRadius
      (HDP.Chapter7.gaussianWidth T) error := by
    exact add_nonneg (HDP.Chapter7.gaussianWidth_nonneg T hT) herror
  constructor
  · exact closedConvexHull_subset_closedBall_of_supportUpper
      (deterministicMatrixImageFinset B.transpose T)
      (deterministicMatrixImageFinset_nonempty B.transpose hT) hrPlus
      (fun y ↦ (hsandwich y).2)
  · intro hrMinus
    exact closedBall_subset_closedConvexHull_of_supportLower
      (deterministicMatrixImageFinset B.transpose T)
      (deterministicMatrixImageFinset_nonempty B.transpose hT) hrMinus
      (fun y ↦ (hsandwich y).1)

/-- Selects the `k`th point of a fixed dense sequence in a nonempty set.

**Lean implementation helper.** -/
def sourceDensePoint {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  letI : Nonempty T := hT.to_subtype
  (TopologicalSpace.denseSeq T k).1

/-- Every selected dense-sequence point belongs to the source set.

**Lean implementation helper.** -/
theorem sourceDensePoint_mem {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) (k : ℕ) :
    sourceDensePoint T hT k ∈ T := by
  letI : Nonempty T := hT.to_subtype
  exact (TopologicalSpace.denseSeq T k).2

/-- The `k`th source prefix is the finite set of the first `k+1` dense-sequence points.

**Lean implementation helper.** -/
def sourceDensePrefix {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) (k : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  (Finset.range (k + 1)).image (sourceDensePoint T hT)

/-- Every finite prefix of the source dense sequence contains its first selected point.

**Lean implementation helper.** -/
theorem sourceDensePrefix_nonempty {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) (k : ℕ) :
    (sourceDensePrefix T hT k).Nonempty := by
  exact ⟨sourceDensePoint T hT 0, Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩

/-- Every source dense prefix is contained in the original set.

**Lean implementation helper.** -/
theorem sourceDensePrefix_subset {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) (k : ℕ) :
    (↑(sourceDensePrefix T hT k) : Set _) ⊆ T := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact sourceDensePoint_mem T hT i

/-- The source dense prefixes form an increasing sequence of finsets.

**Lean implementation helper.** -/
theorem sourceDensePrefix_mono {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) {k l : ℕ}
    (hkl : k ≤ l) : sourceDensePrefix T hT k ⊆
      sourceDensePrefix T hT l := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by
    have := Finset.mem_range.mp hi
    omega), rfl⟩

/-- The set-level Dvoretzky width is the Gaussian width of the bounded source set.

**Lean implementation helper.** -/
def setDvoretzkyWidth {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  HDP.Chapter8.euclideanSetGaussianWidth T

/-- The set-level Dvoretzky radius is the supremum of Euclidean norms over the source set.

**Lean implementation helper.** -/
def setDvoretzkyRadius {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (HDP.Chapter8.setRadiusEnvelope T).toReal

/-- The set-level Dvoretzky width is nonnegative.

**Lean implementation helper.** -/
theorem setDvoretzkyWidth_nonneg {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    0 ≤ setDvoretzkyWidth T := ENNReal.toReal_nonneg

/-- The set-level Dvoretzky radius is nonnegative.

**Lean implementation helper.** -/
theorem setDvoretzkyRadius_nonneg {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    0 ≤ setDvoretzkyRadius T := ENNReal.toReal_nonneg

/-- Every finite subset has Gaussian width at most the set-level Dvoretzky width.

**Lean implementation helper.** -/
theorem finiteWidth_le_setDvoretzkyWidth {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (↑F : Set _) ⊆ T) (hF : F.Nonempty) :
    HDP.Chapter7.gaussianWidth F ≤ setDvoretzkyWidth T := by
  have htop := HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top hT hTb
  have hle : ENNReal.ofReal (HDP.Chapter7.gaussianWidth F) ≤
      HDP.Chapter8.euclideanSetGaussianWidthENN T := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    exact le_iSup_of_le F (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  have hreal := ENNReal.toReal_mono htop hle
  simpa [setDvoretzkyWidth, HDP.Chapter8.euclideanSetGaussianWidth,
    ENNReal.toReal_ofReal (HDP.Chapter7.gaussianWidth_nonneg F hF)] using hreal

/-- Every finite subset has radius at most the set-level Dvoretzky radius.

**Lean implementation helper.** -/
theorem finiteRadius_le_setDvoretzkyRadius {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (↑F : Set _) ⊆ T) (hF : F.Nonempty) :
    HDP.Chapter7.finiteRadius F ≤ setDvoretzkyRadius T := by
  have htop := HDP.Chapter8.setRadiusEnvelope_ne_top_of_isBounded hTb
  have hle : ENNReal.ofReal (HDP.Chapter7.finiteRadius F) ≤
      HDP.Chapter8.setRadiusEnvelope T := by
    unfold HDP.Chapter8.setRadiusEnvelope
    let U : HDP.Chapter8.NonemptyFiniteSubset T := ⟨F, hF, hFT⟩
    exact le_iSup_of_le U le_rfl
  have hreal := ENNReal.toReal_mono htop hle
  simpa [setDvoretzkyRadius,
    ENNReal.toReal_ofReal (HDP.Chapter7.finiteRadius_nonneg F)] using hreal

/-- Finite subsets of a bounded nonempty set approximate its Gaussian width arbitrarily well from below.

**Lean implementation helper.** -/
theorem exists_finite_width_approx {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset (EuclideanSpace ℝ (Fin n))),
      (↑F : Set _) ⊆ T ∧ F.Nonempty ∧
        setDvoretzkyWidth T - ε < HDP.Chapter7.gaussianWidth F := by
  let W := HDP.Chapter8.euclideanSetGaussianWidthENN T
  let w := setDvoretzkyWidth T
  have htop : W ≠ ∞ := by
    exact HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top hT hTb
  have hW : ENNReal.ofReal w = W := by
    exact ENNReal.ofReal_toReal htop
  by_cases hw : w = 0
  · obtain ⟨x, hx⟩ := hT
    refine ⟨{x}, by simpa using hx, by simp, ?_⟩
    have hnonneg := HDP.Chapter7.gaussianWidth_nonneg ({x} : Finset _) (by simp)
    change w - ε < HDP.Chapter7.gaussianWidth {x}
    rw [hw]
    linarith
  · have hwpos : 0 < w := lt_of_le_of_ne
      (setDvoretzkyWidth_nonneg T) (Ne.symm hw)
    have hlt : ENNReal.ofReal (w - ε) < W := by
      rw [← hW]
      exact (ENNReal.ofReal_lt_ofReal_iff hwpos).2 (sub_lt_self w hε)
    unfold W HDP.Chapter8.euclideanSetGaussianWidthENN at hlt
    rw [lt_iSup_iff] at hlt
    obtain ⟨F, hlt⟩ := hlt
    rw [lt_iSup_iff] at hlt
    obtain ⟨hFT, hlt⟩ := hlt
    rw [lt_iSup_iff] at hlt
    obtain ⟨hF, hlt⟩ := hlt
    have hwidthpos : 0 < HDP.Chapter7.gaussianWidth F := by
      exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hlt)
    exact ⟨F, hFT, hF,
      (ENNReal.ofReal_lt_ofReal_iff hwidthpos).mp hlt⟩

/-- Enlarging a nonempty finite set can only increase its support functional.

**Lean implementation helper.** -/
theorem finiteSupportFunctional_mono {n : ℕ}
    {F G : Finset (EuclideanSpace ℝ (Fin n))}
    (hF : F.Nonempty) (hG : G.Nonempty) (hFG : F ⊆ G)
    (y : EuclideanSpace ℝ (Fin n)) :
    finiteSupportFunctional F y ≤ finiteSupportFunctional G y := by
  change HDP.Chapter7.finiteGaussianSupport F y ≤
    HDP.Chapter7.finiteGaussianSupport G y
  rw [
    HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF,
    HDP.Chapter7.finiteGaussianSupport_eq_sup' G hG]
  apply Finset.sup'_le
  intro x hx
  exact Finset.le_sup' (fun z ↦ inner ℝ y z) (hFG hx)

/-- The finite outer deviation is the nonnegative supremum of excess support over the target width.

**Lean implementation helper.** -/
def finiteOuterDeviationENN {m n : ℕ} [NeZero m]
    (width : ℝ) (F : Finset (EuclideanSpace ℝ (Fin n)))
    (B : Matrix (Fin n) (Fin m) ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, ENNReal.ofReal
    (finiteSupportFunctional F
      (HDP.gaussianMatrixAction B (unitSphereDensePoint m j)) - width)

/-- The extended-real outer support deviation of a finite set is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteOuterDeviationENN {m n : ℕ} [NeZero m]
    (width : ℝ) (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) :
    Measurable (finiteOuterDeviationENN (m := m) width F) := by
  apply Measurable.iSup
  intro j
  exact ENNReal.measurable_ofReal.comp
    ((((finiteSupportSublinearFunctional F hF).continuous_of_growth
      (HDP.Chapter7.finiteRadius_nonneg F)
      (finiteSupportFunctional_growth F hF)).measurable.comp
        (HDP.gaussianMatrixAction_measurable (unitSphereDensePoint m j))).sub_const _)

/-- Enlarging the finite source set can only increase its outer support deviation.

**Lean implementation helper.** -/
theorem finiteOuterDeviationENN_mono {m n : ℕ} [NeZero m]
    (width : ℝ) {F G : Finset (EuclideanSpace ℝ (Fin n))}
    (hF : F.Nonempty) (hG : G.Nonempty) (hFG : F ⊆ G)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    finiteOuterDeviationENN (m := m) width F B ≤
      finiteOuterDeviationENN (m := m) width G B := by
  unfold finiteOuterDeviationENN
  apply iSup_mono
  intro j
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_sub_right
    (finiteSupportFunctional_mono hF hG hFG _) width

/-- The finite outer support deviation is bounded by the two-sided Dvoretzky–Milman deviation.

**Lean implementation helper.** -/
theorem finiteOuterDeviationENN_le_dvoretzky {m n : ℕ} [NeZero m]
    (width : ℝ) (F : Finset (EuclideanSpace ℝ (Fin n))) (_hF : F.Nonempty)
    (hwidth : HDP.Chapter7.gaussianWidth F ≤ width)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    finiteOuterDeviationENN (m := m) width F B ≤
      dvoretzkyMilmanDeviationENN F B := by
  unfold finiteOuterDeviationENN
  apply iSup_le
  intro j
  let N := unitSpherePrefix m j
  letI : Nonempty ↑N := (unitSpherePrefix_nonempty m j).to_subtype
  have hjN : unitSphereDensePoint m j ∈ N := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  have hp := abs_support_sub_width_le_finiteTwoSidedChevetDeviation
    N F hjN B
  calc
    ENNReal.ofReal (finiteSupportFunctional F
        (HDP.gaussianMatrixAction B (unitSphereDensePoint m j)) - width) ≤
        ENNReal.ofReal |finiteSupportFunctional F
          (HDP.gaussianMatrixAction B (unitSphereDensePoint m j)) -
            HDP.Chapter7.gaussianWidth F| := by
      apply ENNReal.ofReal_le_ofReal
      have habs := le_abs_self (finiteSupportFunctional F
        (HDP.gaussianMatrixAction B (unitSphereDensePoint m j)) -
          HDP.Chapter7.gaussianWidth F)
      linarith
    _ ≤ ENNReal.ofReal (finiteTwoSidedChevetDeviation N F B) :=
      ENNReal.ofReal_le_ofReal (by
        simpa [norm_unitSphereDensePoint] using hp)
    _ ≤ dvoretzkyMilmanDeviationENN F B := by
      exact le_iSup (fun k : ℕ ↦
        letI : Nonempty ↑(unitSpherePrefix m k) :=
          (unitSpherePrefix_nonempty m k).to_subtype
        ENNReal.ofReal (finiteTwoSidedChevetDeviation
          (unitSpherePrefix m k) F B)) j

/-- The expected finite outer support deviation is bounded by the set radius at the general matrix-deviation scale.

**Lean implementation helper.** -/
theorem lintegral_finiteOuterDeviationENN_le {m n : ℕ} [NeZero m]
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (↑F : Set _) ⊆ T) (hF : F.Nonempty) :
    (∫⁻ B, finiteOuterDeviationENN (m := m)
        (setDvoretzkyWidth T) F B
        ∂HDP.stdGaussianMatrixMeasure n m) ≤
      ENNReal.ofReal (generalMatrixDeviationConstant * Real.sqrt m *
        setDvoretzkyRadius T) := by
  calc
    (∫⁻ B, finiteOuterDeviationENN (m := m)
        (setDvoretzkyWidth T) F B
        ∂HDP.stdGaussianMatrixMeasure n m) ≤
        ∫⁻ B, dvoretzkyMilmanDeviationENN F B
          ∂HDP.stdGaussianMatrixMeasure n m := by
      apply lintegral_mono
      intro B
      exact finiteOuterDeviationENN_le_dvoretzky
        (setDvoretzkyWidth T) F hF
        (finiteWidth_le_setDvoretzkyWidth hT hTb F hFT hF) B
    _ ≤ ENNReal.ofReal (generalMatrixDeviationConstant * Real.sqrt m *
        HDP.Chapter7.finiteRadius F) :=
      lintegral_dvoretzkyMilmanDeviationENN_le F hF
    _ ≤ ENNReal.ofReal (generalMatrixDeviationConstant * Real.sqrt m *
        setDvoretzkyRadius T) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (finiteRadius_le_setDvoretzkyRadius hTb F hFT hF)
        (mul_nonneg generalMatrixDeviationConstant_pos.le
          (Real.sqrt_nonneg m))

/-- The set-level outer deviation is the supremum of excess support over all finite dense prefixes.

**Lean implementation helper.** -/
def setOuterDeviationENN {m n : ℕ} [NeZero m]
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (B : Matrix (Fin n) (Fin m) ℝ) : ℝ≥0∞ :=
  ⨆ k : ℕ, finiteOuterDeviationENN (m := m)
    (setDvoretzkyWidth T) (sourceDensePrefix T hT k) B

/-- The set-level outer support deviation is measurable as a countable supremum over dense prefixes.

**Lean implementation helper.** -/
theorem measurable_setOuterDeviationENN {m n : ℕ} [NeZero m]
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Measurable (setOuterDeviationENN (m := m) T hT) := by
  apply Measurable.iSup
  intro k
  exact measurable_finiteOuterDeviationENN
    (setDvoretzkyWidth T) (sourceDensePrefix T hT k)
      (sourceDensePrefix_nonempty T hT k)

/-- The expected set-level outer support deviation is bounded by the set radius at the general matrix-deviation scale.

**Lean implementation helper.** -/
theorem lintegral_setOuterDeviationENN_le {m n : ℕ} [NeZero m]
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    (∫⁻ B, setOuterDeviationENN (m := m) T hT B
        ∂HDP.stdGaussianMatrixMeasure n m) ≤
      ENNReal.ofReal (generalMatrixDeviationConstant * Real.sqrt m *
        setDvoretzkyRadius T) := by
  let F : ℕ → Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ := fun k B ↦
    finiteOuterDeviationENN (m := m) (setDvoretzkyWidth T)
      (sourceDensePrefix T hT k) B
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    exact measurable_finiteOuterDeviationENN _ _
      (sourceDensePrefix_nonempty T hT k)
  have hFmono : Monotone F := by
    intro k l hkl B
    exact finiteOuterDeviationENN_mono _
      (sourceDensePrefix_nonempty T hT k)
      (sourceDensePrefix_nonempty T hT l)
      (sourceDensePrefix_mono T hT hkl) B
  change (∫⁻ B, ⨆ k, F k B ∂HDP.stdGaussianMatrixMeasure n m) ≤ _
  rw [lintegral_iSup hFm hFmono]
  apply iSup_le
  intro k
  exact lintegral_finiteOuterDeviationENN_le hT hTb
    (sourceDensePrefix T hT k)
    (sourceDensePrefix_subset T hT k)
    (sourceDensePrefix_nonempty T hT k)

/-- The deterministic matrix image of a set consists of all matrix images of its points.

**Lean implementation helper.** -/
def deterministicMatrixImageSet {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  deterministicMatrixAction A '' T

/-- Coercing a finite matrix image to a set agrees with the image of the coerced source finset.

**Lean implementation helper.** -/
theorem coe_deterministicMatrixImageFinset {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (F : Finset (EuclideanSpace ℝ (Fin n))) :
    (↑(deterministicMatrixImageFinset A F) : Set _) =
      deterministicMatrixImageSet A (↑F : Set _) := by
  ext z
  simp [deterministicMatrixImageFinset, deterministicMatrixImageSet]

/-- A bound on finite outer support deviation places the finite image hull inside the corresponding ball.

**Lean implementation helper.** -/
theorem finiteHull_outer_of_outerDeviationENN_le {m n : ℕ} [NeZero m]
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty)
    (B : Matrix (Fin n) (Fin m) ℝ) {width error : ℝ}
    (hwidth : 0 ≤ width) (herror : 0 ≤ error)
    (hdev : finiteOuterDeviationENN (m := m) width F B ≤
      ENNReal.ofReal error) :
    closedConvexHullSet
        (↑(deterministicMatrixImageFinset B.transpose F) :
          Set (EuclideanSpace ℝ (Fin m))) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (width + error) := by
  let E := EuclideanSpace ℝ (Fin m)
  let sphere := Metric.sphere (0 : E) 1
  let imageF := deterministicMatrixImageFinset B.transpose F
  have himage : imageF.Nonempty :=
    deterministicMatrixImageFinset_nonempty B.transpose hF
  let f : sphere → ℝ := fun y ↦
    finiteSupportFunctional imageF y.1 - width
  have hfcont : Continuous f := by
    exact (((finiteSupportSublinearFunctional imageF himage).continuous_of_growth
      (HDP.Chapter7.finiteRadius_nonneg imageF)
      (finiteSupportFunctional_growth imageF himage)).comp
        continuous_subtype_val).sub continuous_const
  have hdense : ∀ j, f (TopologicalSpace.denseSeq sphere j) ≤ error := by
    intro j
    have hj : ENNReal.ofReal (f (TopologicalSpace.denseSeq sphere j)) ≤
        finiteOuterDeviationENN (m := m) width F B := by
      have heq : f (TopologicalSpace.denseSeq sphere j) =
          finiteSupportFunctional F
            (HDP.gaussianMatrixAction B (unitSphereDensePoint m j)) - width := by
        change finiteSupportFunctional imageF (unitSphereDensePoint m j) - width = _
        rw [show imageF = deterministicMatrixImageFinset B.transpose F by rfl,
          finiteSupport_transposeImage_eq B F hF]
      rw [heq]
      exact le_iSup (fun k : ℕ ↦ ENNReal.ofReal
        (finiteSupportFunctional F
          (HDP.gaussianMatrixAction B (unitSphereDensePoint m k)) - width)) j
    exact (ENNReal.ofReal_le_ofReal_iff herror).mp (hj.trans hdev)
  have hallSphere : ∀ y : sphere, f y ≤ error := by
    intro y
    have hclosed : IsClosed {q : sphere | f q ≤ error} :=
      isClosed_le hfcont continuous_const
    have hrange : Set.range (TopologicalSpace.denseSeq sphere) ⊆
        {q : sphere | f q ≤ error} := by
      rintro _ ⟨j, rfl⟩
      exact hdense j
    have hyclosure : y ∈ closure (Set.range
        (TopologicalSpace.denseSeq sphere)) := by
      rw [(TopologicalSpace.denseRange_denseSeq sphere).closure_range]
      trivial
    exact (closure_minimal hrange hclosed) hyclosure
  have hupper : ∀ y : E,
      finiteSupportFunctional imageF y ≤ (width + error) * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · subst y
      simp [finiteSupportFunctional,
        HDP.Chapter7.finiteGaussianSupport_eq_sup' imageF himage]
    · have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      let q : sphere := ⟨‖y‖⁻¹ • y, by
          rw [Metric.mem_sphere, dist_zero_right]
          simp [norm_smul, Real.norm_eq_abs, abs_of_pos hypos,
            hypos.ne']⟩
      have hq := hallSphere q
      have hyrepr : y = ‖y‖ • (q : E) := by
        simp [q, hypos.ne']
      have hpos := finiteSupportFunctional_posHom imageF himage
        ‖y‖ hypos.le (q : E)
      have hqnorm : ‖(q : E)‖ = 1 := by
        rw [← dist_zero_right]
        exact q.property
      rw [hyrepr, hpos, norm_smul, Real.norm_eq_abs,
        abs_of_pos hypos, hqnorm, mul_one]
      change finiteSupportFunctional imageF (q : E) - width ≤ error at hq
      nlinarith
  exact closedConvexHull_subset_closedBall_of_supportUpper
    imageF himage (add_nonneg hwidth herror) hupper

/-- A set-level outer-deviation bound places the full image hull inside the corresponding ball.

**Lean implementation helper.** -/
theorem arbitraryHull_outer_of_setOuterDeviationENN_le {m n : ℕ}
    [NeZero m]
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (B : Matrix (Fin n) (Fin m) ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hdev : setOuterDeviationENN (m := m) T hT B ≤
      ENNReal.ofReal error) :
    closedConvexHullSet (deterministicMatrixImageSet B.transpose T) ⊆
      Metric.closedBall 0 (setDvoretzkyWidth T + error) := by
  letI : Nonempty T := hT.to_subtype
  let E := EuclideanSpace ℝ (Fin m)
  let f : T → E := fun x ↦ deterministicMatrixAction B.transpose x.1
  have hfcont : Continuous f :=
    B.transpose.toEuclideanLin.toContinuousLinearMap.continuous.comp
      continuous_subtype_val
  have hprefix : ∀ k,
      closedConvexHullSet
          (↑(deterministicMatrixImageFinset B.transpose
            (sourceDensePrefix T hT k)) : Set E) ⊆
        Metric.closedBall 0 (setDvoretzkyWidth T + error) := by
    intro k
    apply finiteHull_outer_of_outerDeviationENN_le
      (sourceDensePrefix T hT k)
      (sourceDensePrefix_nonempty T hT k) B
      (setDvoretzkyWidth_nonneg T) herror
    exact (le_iSup (fun j : ℕ ↦ finiteOuterDeviationENN (m := m)
      (setDvoretzkyWidth T) (sourceDensePrefix T hT j) B) k).trans hdev
  have hdenseGood : Set.range (TopologicalSpace.denseSeq T) ⊆
      f ⁻¹' Metric.closedBall (0 : E) (setDvoretzkyWidth T + error) := by
    rintro _ ⟨k, rfl⟩
    have hk : sourceDensePoint T hT k ∈
        sourceDensePrefix T hT k := by
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
    have himage : deterministicMatrixAction B.transpose
        (sourceDensePoint T hT k) ∈
        deterministicMatrixImageFinset B.transpose
          (sourceDensePrefix T hT k) := by
      exact Finset.mem_image.mpr ⟨_, hk, rfl⟩
    exact hprefix k (subset_closedConvexHull himage)
  have hall : ∀ x : T, f x ∈
      Metric.closedBall (0 : E) (setDvoretzkyWidth T + error) := by
    intro x
    have hclosed : IsClosed (f ⁻¹'
        Metric.closedBall (0 : E) (setDvoretzkyWidth T + error)) :=
      Metric.isClosed_closedBall.preimage hfcont
    have hx : x ∈ closure (Set.range (TopologicalSpace.denseSeq T)) := by
      rw [(TopologicalSpace.denseRange_denseSeq T).closure_range]
      trivial
    exact (closure_minimal hdenseGood hclosed) hx
  apply closedConvexHull_min
  · rintro z ⟨x, hx, rfl⟩
    exact hall ⟨x, hx⟩
  · exact convex_closedBall 0 _
  · exact Metric.isClosed_closedBall

/-- A Gaussian image of a convex body is sandwiched between nearly concentric Euclidean balls.

**Book Theorem 9.7.2.** -/
def DvoretzkyMilmanSetConclusion {m : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (rMinus rPlus : ℝ) : Prop :=
  closedConvexHullSet S ⊆ Metric.closedBall 0 rPlus ∧
    (0 ≤ rMinus → Metric.closedBall 0 rMinus ⊆ closedConvexHullSet S)

/-- An inner ball contained in a finite image hull is also contained in the hull of the full image set.

**Lean implementation helper.** -/
theorem finiteInner_subset_arbitraryHull {m n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (↑F : Set _) ⊆ T)
    (B : Matrix (Fin n) (Fin m) ℝ) {rFinite rSet : ℝ}
    (hr : rSet ≤ rFinite)
    (hfinite : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) rFinite ⊆
      closedConvexHullSet
        (↑(deterministicMatrixImageFinset B.transpose F) : Set _)) :
    Metric.closedBall 0 rSet ⊆
      closedConvexHullSet (deterministicMatrixImageSet B.transpose T) := by
  refine (Metric.closedBall_subset_closedBall hr).trans (hfinite.trans ?_)
  unfold closedConvexHullSet
  apply (closedConvexHull ℝ).monotone
  rw [coe_deterministicMatrixImageFinset]
  exact image_mono hFT

/-- The base set-level Dvoretzky–Milman error combines width and radius with the matrix-deviation constant.

**Lean implementation helper.** -/
def setDvoretzkyMilmanBaseError {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  generalMatrixDeviationConstant * Real.sqrt m * setDvoretzkyRadius T

/-- The set-level Dvoretzky–Milman error is the nonnegative normalization of the base error.

**Lean implementation helper.** -/
def setDvoretzkyMilmanError {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  201 * setDvoretzkyMilmanBaseError (m := m) T

/-- The set Dvoretzky–Milman base error is nonnegative.

**Lean implementation helper.** -/
theorem setDvoretzkyMilmanBaseError_nonneg {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    0 ≤ setDvoretzkyMilmanBaseError (m := m) T := by
  exact mul_nonneg
    (mul_nonneg generalMatrixDeviationConstant_pos.le (Real.sqrt_nonneg m))
    (setDvoretzkyRadius_nonneg T)

/-- The set Dvoretzky–Milman error is nonnegative.

**Lean implementation helper.** -/
theorem setDvoretzkyMilmanError_nonneg {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    0 ≤ setDvoretzkyMilmanError (m := m) T := by
  exact mul_nonneg (by norm_num) (setDvoretzkyMilmanBaseError_nonneg T)

/-- A bounded set of zero radius contains only the origin.

**Lean implementation helper.** -/
theorem setDvoretzkyRadius_eq_zero_imp {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hTb : Bornology.IsBounded T)
    (hR : setDvoretzkyRadius T = 0) :
    ∀ x ∈ T, x = 0 := by
  intro x hx
  let F : Finset (EuclideanSpace ℝ (Fin n)) := {x}
  have hFT : (↑F : Set _) ⊆ T := by
    intro y hy
    have hyx : y = x := by simpa [F] using hy
    simpa [hyx] using hx
  have hF : F.Nonempty := by simp [F]
  have hFR := finiteRadius_le_setDvoretzkyRadius hTb F hFT hF
  have hxR := HDP.Chapter7.norm_le_finiteRadius F hF
    (by simp [F] : x ∈ F)
  have hxnorm : ‖x‖ = 0 := by
    apply le_antisymm
    · exact hxR.trans (by simpa [hR] using hFR)
    · exact norm_nonneg x
  exact norm_eq_zero.mp hxnorm

/-- A bounded set with zero radius has zero Gaussian width.

**Lean implementation helper.** -/
theorem setDvoretzkyWidth_eq_zero_of_radius_eq_zero {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hTb : Bornology.IsBounded T) (hR : setDvoretzkyRadius T = 0) :
    setDvoretzkyWidth T = 0 := by
  have hzero := setDvoretzkyRadius_eq_zero_imp hTb hR
  have hWle : HDP.Chapter8.euclideanSetGaussianWidthENN T ≤ 0 := by
    unfold HDP.Chapter8.euclideanSetGaussianWidthENN
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    have hFeq : F = {0} := by
      ext x
      constructor
      · intro hx
        have : x = 0 := hzero x (hFT hx)
        simp [this]
      · intro hx
        have hmem : (0 : EuclideanSpace ℝ (Fin n)) ∈ F := by
          obtain ⟨x, hxF⟩ := hF
          have hx0 := hzero x (hFT hxF)
          simpa [hx0] using hxF
        have hx0 : x = 0 := by simpa using hx
        simpa [hx0] using hmem
    rw [hFeq, HDP.Chapter7.gaussianWidth_singleton]
    simp
  have hWzero : HDP.Chapter8.euclideanSetGaussianWidthENN T = 0 :=
    le_antisymm hWle bot_le
  simp [setDvoretzkyWidth, HDP.Chapter8.euclideanSetGaussianWidth, hWzero]

/-- The closed convex hull of the singleton origin is the singleton origin.

**Lean implementation helper.** -/
theorem closedConvexHullSet_singleton_zero {m : ℕ} :
    closedConvexHullSet ({0} : Set (EuclideanSpace ℝ (Fin m))) = {0} := by
  apply Set.Subset.antisymm
  · exact closedConvexHull_min Subset.rfl (convex_singleton 0) isClosed_singleton
  · exact subset_closedConvexHull

/-- Finite-cloud engine for `B` is sampled from the canonical `n × m` product Gaussian measure and the
book's `m × n` Gaussian matrix is `Bᵀ`. This is an iid Gaussian constructor,
not a caller-supplied law. The outer inclusion always holds and the inner
inclusion is conditional on the lower radius being nonnegative.

**Book Theorem 9.7.2 (Dvoretzky--Milman).** -/
theorem theorem_9_7_2_dvoretzkyMilman_finite {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.stdGaussianMatrixMeasure n m
        {B | DvoretzkyMilmanConclusion
          (deterministicMatrixImageFinset B.transpose T)
          (dvoretzkyMilmanInnerRadius (HDP.Chapter7.gaussianWidth T)
            (dvoretzkyMilmanError (m := m) T))
          (dvoretzkyMilmanOuterRadius (HDP.Chapter7.gaussianWidth T)
            (dvoretzkyMilmanError (m := m) T))} := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let U := dvoretzkyMilmanDeviationENN (m := m) T
  let error := dvoretzkyMilmanError (m := m) T
  have herror : 0 ≤ error := by
    exact mul_nonneg
      (mul_nonneg dvoretzkyMilmanConstant_pos.le (Real.sqrt_nonneg m))
      (HDP.Chapter7.finiteRadius_nonneg T)
  have hgoodSubset : {B | U B ≤ ENNReal.ofReal error} ⊆
      {B | DvoretzkyMilmanConclusion
        (deterministicMatrixImageFinset B.transpose T)
        (dvoretzkyMilmanInnerRadius (HDP.Chapter7.gaussianWidth T) error)
        (dvoretzkyMilmanOuterRadius (HDP.Chapter7.gaussianWidth T) error)} := by
    intro B hB
    exact dvoretzkyMilmanConclusion_of_deviationENN_le T hT B herror hB
  by_cases hrad : HDP.Chapter7.finiteRadius T = 0
  · have hUzero : (∫⁻ B, U B ∂HDP.stdGaussianMatrixMeasure n m) = 0 := by
      apply le_antisymm
      · simpa [U, hrad] using lintegral_dvoretzkyMilmanDeviationENN_le T hT
      · exact bot_le
    have hUae : ∀ᵐ B ∂HDP.stdGaussianMatrixMeasure n m, U B = 0 :=
      (lintegral_eq_zero_iff
        (measurable_dvoretzkyMilmanDeviationENN T hT)).mp hUzero
    calc
      ENNReal.ofReal (99 / 100 : ℝ) ≤
          HDP.stdGaussianMatrixMeasure n m {B | U B ≤ ENNReal.ofReal error} := by
        rw [show HDP.stdGaussianMatrixMeasure n m {B | U B ≤
            ENNReal.ofReal error} = 1 by
          calc
            _ = HDP.stdGaussianMatrixMeasure n m Set.univ := by
              apply measure_congr
              filter_upwards [hUae] with B hB
              change (U B ≤ ENNReal.ofReal error) = True
              simp [hB]
            _ = 1 := measure_univ]
        norm_num
      _ ≤ _ := measure_mono hgoodSubset
  · have hradpos : 0 < HDP.Chapter7.finiteRadius T :=
      lt_of_le_of_ne (HDP.Chapter7.finiteRadius_nonneg T) (Ne.symm hrad)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hthreshold : ENNReal.ofReal error ≠ 0 := by
      exact ne_of_gt (ENNReal.ofReal_pos.2 (by
        dsimp [error, dvoretzkyMilmanError, dvoretzkyMilmanConstant]
        positivity [generalMatrixDeviationConstant_pos]))
    have hthresholdTop : ENNReal.ofReal error ≠ ∞ := ENNReal.ofReal_ne_top
    have hmarkov := meas_ge_le_lintegral_div
      (μ := HDP.stdGaussianMatrixMeasure n m)
      (measurable_dvoretzkyMilmanDeviationENN (m := m) T hT).aemeasurable
      hthreshold hthresholdTop
    have hlin := lintegral_dvoretzkyMilmanDeviationENN_le
      (m := m) (n := n) T hT
    have hfail : HDP.stdGaussianMatrixMeasure n m
        {B | ENNReal.ofReal error ≤ U B} ≤ 1 / 100 := by
      calc
        HDP.stdGaussianMatrixMeasure n m
            {B | ENNReal.ofReal error ≤ U B} ≤
            (∫⁻ B, U B ∂HDP.stdGaussianMatrixMeasure n m) /
              ENNReal.ofReal error := hmarkov
        _ ≤ ENNReal.ofReal (generalMatrixDeviationConstant * Real.sqrt m *
              HDP.Chapter7.finiteRadius T) / ENNReal.ofReal error := by
          gcongr
        _ = 1 / 100 := by
          have herrorpos : 0 < error := by
            dsimp [error, dvoretzkyMilmanError, dvoretzkyMilmanConstant]
            positivity [generalMatrixDeviationConstant_pos]
          have hquot :
              (generalMatrixDeviationConstant * Real.sqrt m *
                HDP.Chapter7.finiteRadius T) / error = (1 / 100 : ℝ) := by
            dsimp [error, dvoretzkyMilmanError, dvoretzkyMilmanConstant]
            field_simp [generalMatrixDeviationConstant_pos.ne',
              (Real.sqrt_pos.2 hmR).ne', hrad]
          rw [← ENNReal.ofReal_div_of_pos herrorpos, hquot,
            ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
          norm_num
    have hbadMeas : MeasurableSet {B | ENNReal.ofReal error ≤ U B} :=
      measurableSet_le measurable_const
        (measurable_dvoretzkyMilmanDeviationENN T hT)
    have hgood : ENNReal.ofReal (99 / 100 : ℝ) ≤
        HDP.stdGaussianMatrixMeasure n m {B | U B < ENNReal.ofReal error} := by
      rw [show {B | U B < ENNReal.ofReal error} =
          {B | ENNReal.ofReal error ≤ U B}ᶜ by ext B; simp]
      have hbadTop : HDP.stdGaussianMatrixMeasure n m
          {B | ENNReal.ofReal error ≤ U B} ≠ ∞ := measure_ne_top _ _
      rw [measure_compl hbadMeas hbadTop, measure_univ]
      exact ENNReal.le_sub_of_add_le_right hbadTop (by
        calc
          ENNReal.ofReal (99 / 100 : ℝ) +
              HDP.stdGaussianMatrixMeasure n m
                {B | ENNReal.ofReal error ≤ U B} ≤
              ENNReal.ofReal (99 / 100 : ℝ) + 1 / 100 :=
            add_le_add_right hfail _
          _ = 1 := by
            have hone : (1 / 100 : ℝ≥0∞) =
                ENNReal.ofReal (1 / 100 : ℝ) := by
              rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
              norm_num
            rw [hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            norm_num)
    calc
      ENNReal.ofReal (99 / 100 : ℝ) ≤
          HDP.stdGaussianMatrixMeasure n m
            {B | U B < ENNReal.ofReal error} := hgood
      _ ≤ HDP.stdGaussianMatrixMeasure n m
          {B | U B ≤ ENNReal.ofReal error} := by
        apply measure_mono
        intro B hB
        change U B < ENNReal.ofReal error at hB
        change U B ≤ ENNReal.ofReal error
        exact hB.le
      _ ≤ _ := by simpa [U, error] using measure_mono hgoodSubset

/-- A Gaussian image of a convex body is sandwiched between nearly concentric Euclidean balls. For a nonempty bounded `T`, `BᵀT` is the actual image of `T` under the
canonical iid Gaussian matrix. With probability at least `0.99`, its closed
convex hull lies in the outer centered ball; when the lower radius is
nonnegative it contains the corresponding inner ball. Gaussian width and
radius use the authoritative Chapter 8 finite-subfamily envelopes.

**Book Theorem 9.7.2.** -/
theorem theorem_9_7_2_dvoretzkyMilman {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (hm : 0 < m)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.stdGaussianMatrixMeasure n m
        {B | DvoretzkyMilmanSetConclusion
          (deterministicMatrixImageSet B.transpose T)
          (dvoretzkyMilmanInnerRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T))
          (dvoretzkyMilmanOuterRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T))} := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let R := setDvoretzkyRadius T
  let w := setDvoretzkyWidth T
  let a := setDvoretzkyMilmanBaseError (m := m) T
  by_cases hR : R = 0
  · have hzero : ∀ x ∈ T, x = 0 := by
      simpa [R] using setDvoretzkyRadius_eq_zero_imp hTb (by simpa [R] using hR)
    have hTeq : T = {0} := by
      apply Set.Subset.antisymm
      · intro x hx
        simp [hzero x hx]
      · obtain ⟨x, hx⟩ := hT
        have hx0 := hzero x hx
        simpa [hx0] using hx
    have hw : w = 0 := by
      simpa [w, R] using setDvoretzkyWidth_eq_zero_of_radius_eq_zero
        hTb (by simpa [R] using hR)
    have ha : a = 0 := by
      simp [a, setDvoretzkyMilmanBaseError, R, hR]
    have herr : setDvoretzkyMilmanError (m := m) T = 0 := by
      unfold setDvoretzkyMilmanError
      rw [show setDvoretzkyMilmanBaseError (m := m) T = 0 by
        simpa [a] using ha]
      norm_num
    have himage : ∀ B : Matrix (Fin n) (Fin m) ℝ,
        deterministicMatrixImageSet B.transpose T = {0} := by
      intro B
      rw [hTeq]
      ext z
      simp [deterministicMatrixImageSet]
    rw [show HDP.stdGaussianMatrixMeasure n m
        {B | DvoretzkyMilmanSetConclusion
          (deterministicMatrixImageSet B.transpose T)
          (dvoretzkyMilmanInnerRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T))
          (dvoretzkyMilmanOuterRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T))} = 1 by
      calc
        _ = HDP.stdGaussianMatrixMeasure n m Set.univ := by
          congr 1
          ext B
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          rw [himage B]
          simp [DvoretzkyMilmanSetConclusion, hw, w, herr,
            dvoretzkyMilmanInnerRadius, dvoretzkyMilmanOuterRadius,
            closedConvexHullSet_singleton_zero, Metric.closedBall_zero]
        _ = 1 := measure_univ]
    norm_num
  · have hRpos : 0 < R := lt_of_le_of_ne
      (by simpa [R] using setDvoretzkyRadius_nonneg T) (Ne.symm hR)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hapos : 0 < a := by
      dsimp [a, setDvoretzkyMilmanBaseError, R]
      positivity [generalMatrixDeviationConstant_pos]
    obtain ⟨F, hFT, hF, hgap⟩ :=
      exists_finite_width_approx hT hTb hapos
    let outer : Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ :=
      setOuterDeviationENN (m := m) T hT
    let inner : Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ :=
      dvoretzkyMilmanDeviationENN F
    let Z : Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ := fun B ↦ outer B + inner B
    let threshold : ℝ := 200 * a
    have hthreshold : 0 < threshold := mul_pos (by norm_num) hapos
    have houterMeas : Measurable outer := by
      exact measurable_setOuterDeviationENN T hT
    have hinnerMeas : Measurable inner := by
      exact measurable_dvoretzkyMilmanDeviationENN F hF
    have hZMeas : Measurable Z := houterMeas.add hinnerMeas
    have houterInt : (∫⁻ B, outer B ∂HDP.stdGaussianMatrixMeasure n m) ≤
        ENNReal.ofReal a := by
      simpa [outer, a, setDvoretzkyMilmanBaseError] using
        lintegral_setOuterDeviationENN_le T hT hTb
    have hinnerInt : (∫⁻ B, inner B ∂HDP.stdGaussianMatrixMeasure n m) ≤
        ENNReal.ofReal a := by
      have hbase := lintegral_dvoretzkyMilmanDeviationENN_le
        (m := m) F hF
      refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left
        (finiteRadius_le_setDvoretzkyRadius hTb F hFT hF)
        (mul_nonneg generalMatrixDeviationConstant_pos.le
          (Real.sqrt_nonneg m))
    have hZInt : (∫⁻ B, Z B ∂HDP.stdGaussianMatrixMeasure n m) ≤
        ENNReal.ofReal (2 * a) := by
      rw [show (∫⁻ B, Z B ∂HDP.stdGaussianMatrixMeasure n m) =
          (∫⁻ B, outer B ∂HDP.stdGaussianMatrixMeasure n m) +
            ∫⁻ B, inner B ∂HDP.stdGaussianMatrixMeasure n m by
        exact lintegral_add_left houterMeas inner]
      calc
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := add_le_add houterInt hinnerInt
        _ = ENNReal.ofReal (2 * a) := by
          rw [← ENNReal.ofReal_add hapos.le hapos.le]
          congr 1
          ring
    have hthresholdZero : ENNReal.ofReal threshold ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.2 hthreshold)
    have hmarkov := meas_ge_le_lintegral_div
      (μ := HDP.stdGaussianMatrixMeasure n m) hZMeas.aemeasurable
      hthresholdZero ENNReal.ofReal_ne_top
    have hfail : HDP.stdGaussianMatrixMeasure n m
        {B | ENNReal.ofReal threshold ≤ Z B} ≤ 1 / 100 := by
      calc
        HDP.stdGaussianMatrixMeasure n m
            {B | ENNReal.ofReal threshold ≤ Z B} ≤
            (∫⁻ B, Z B ∂HDP.stdGaussianMatrixMeasure n m) /
              ENNReal.ofReal threshold := hmarkov
        _ ≤ ENNReal.ofReal (2 * a) / ENNReal.ofReal threshold := by
          gcongr
        _ = 1 / 100 := by
          have h2a : 0 ≤ 2 * a := by positivity
          rw [← ENNReal.ofReal_div_of_pos hthreshold, show
            (2 * a) / threshold = (1 / 100 : ℝ) by
              dsimp [threshold]
              field_simp [hapos.ne']
              ring,
            ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
          norm_num
    have hbadMeas : MeasurableSet {B | ENNReal.ofReal threshold ≤ Z B} :=
      measurableSet_le measurable_const hZMeas
    have hgood : ENNReal.ofReal (99 / 100 : ℝ) ≤
        HDP.stdGaussianMatrixMeasure n m {B | Z B < ENNReal.ofReal threshold} := by
      rw [show {B | Z B < ENNReal.ofReal threshold} =
          {B | ENNReal.ofReal threshold ≤ Z B}ᶜ by ext B; simp]
      have hbadTop : HDP.stdGaussianMatrixMeasure n m
          {B | ENNReal.ofReal threshold ≤ Z B} ≠ ∞ := measure_ne_top _ _
      rw [measure_compl hbadMeas hbadTop, measure_univ]
      exact ENNReal.le_sub_of_add_le_right hbadTop (by
        calc
          ENNReal.ofReal (99 / 100 : ℝ) +
              HDP.stdGaussianMatrixMeasure n m
                {B | ENNReal.ofReal threshold ≤ Z B} ≤
              ENNReal.ofReal (99 / 100 : ℝ) + 1 / 100 :=
            add_le_add_right hfail _
          _ = 1 := by
            have hone : (1 / 100 : ℝ≥0∞) =
                ENNReal.ofReal (1 / 100 : ℝ) := by
              rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
              norm_num
            rw [hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            norm_num)
    have hgoodSubset : {B | Z B < ENNReal.ofReal threshold} ⊆
        {B | DvoretzkyMilmanSetConclusion
          (deterministicMatrixImageSet B.transpose T)
          (dvoretzkyMilmanInnerRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T))
          (dvoretzkyMilmanOuterRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T))} := by
      intro B hB
      have hZle : Z B ≤ ENNReal.ofReal threshold := hB.le
      have houter : outer B ≤ ENNReal.ofReal threshold :=
        (le_add_right (le_refl (outer B))).trans hZle
      have hinner : inner B ≤ ENNReal.ofReal threshold :=
        (le_add_left (le_refl (inner B))).trans hZle
      have hfinite := dvoretzkyMilmanConclusion_of_deviationENN_le
        F hF B hthreshold.le hinner
      have hErrEq : setDvoretzkyMilmanError (m := m) T = 201 * a := by
        rfl
      constructor
      · have hout := arbitraryHull_outer_of_setOuterDeviationENN_le
          T hT B hthreshold.le houter
        exact hout.trans (Metric.closedBall_subset_closedBall (by
          dsimp [dvoretzkyMilmanOuterRadius]
          rw [hErrEq]
          dsimp [threshold]
          nlinarith))
      · intro hrSet
        have hradii : dvoretzkyMilmanInnerRadius (setDvoretzkyWidth T)
            (setDvoretzkyMilmanError (m := m) T) ≤
            dvoretzkyMilmanInnerRadius (HDP.Chapter7.gaussianWidth F)
              threshold := by
          dsimp [dvoretzkyMilmanInnerRadius]
          rw [hErrEq]
          dsimp [threshold]
          change w - a < HDP.Chapter7.gaussianWidth F at hgap
          nlinarith
        have hrFinite : 0 ≤ dvoretzkyMilmanInnerRadius
            (HDP.Chapter7.gaussianWidth F) threshold :=
          hrSet.trans hradii
        exact finiteInner_subset_arbitraryHull F hFT B hradii
          (hfinite.2 hrFinite)
    exact hgood.trans (measure_mono hgoodSubset)

/-- If the
Chevet error is at most one percent of the Gaussian width, the source radii
are bounded by `0.99 w(T)` and `1.01 w(T)`. The ball here is in `ℝ^m`,
correcting the printed ambient superscript `n`.

**Book Remark 9.7.3.** -/
theorem remark_9_7_3_nearlyRoundRadii {width error : ℝ}
    (_hwidth : 0 ≤ width) (_herror : 0 ≤ error)
    (hsmall : error ≤ width / 100) :
    (99 / 100 : ℝ) * width ≤
        dvoretzkyMilmanInnerRadius width error ∧
      dvoretzkyMilmanOuterRadius width error ≤
        (101 / 100 : ℝ) * width := by
  dsimp [dvoretzkyMilmanInnerRadius, dvoretzkyMilmanOuterRadius]
  constructor <;> nlinarith

/-- Exact finite form of the effective-dimension condition in Remark 9.7.3.
It says `m ≤ c w(T)^2 / rad(T)^2` with the explicit absolute constant
`c = (100 * dvoretzkyMilmanConstant)⁻²`, but is written without division so
that the zero-radius case is safe.

**Book Remark 9.7.3.** -/
def WithinDvoretzkyEffectiveDimension {n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (m : ℕ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (100 * dvoretzkyMilmanConstant) ^ 2 * (m : ℝ) *
      HDP.Chapter7.finiteRadius T ^ 2 ≤
    HDP.Chapter7.gaussianWidth T ^ 2

/-- The explicit dimension condition forces the error in Theorem 9.7.2 below one
percent of the width, hence gives the advertised `0.99/1.01` radii.

**Book Remark 9.7.3.** -/
theorem remark_9_7_3_effectiveDimension {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hdim : WithinDvoretzkyEffectiveDimension m T) :
    (99 / 100 : ℝ) * HDP.Chapter7.gaussianWidth T ≤
        dvoretzkyMilmanInnerRadius (HDP.Chapter7.gaussianWidth T)
          (dvoretzkyMilmanError (m := m) T) ∧
      dvoretzkyMilmanOuterRadius (HDP.Chapter7.gaussianWidth T)
          (dvoretzkyMilmanError (m := m) T) ≤
        (101 / 100 : ℝ) * HDP.Chapter7.gaussianWidth T := by
  have hwidth : 0 ≤ HDP.Chapter7.gaussianWidth T :=
    HDP.Chapter7.gaussianWidth_nonneg T hT
  have hradius : 0 ≤ HDP.Chapter7.finiteRadius T :=
    HDP.Chapter7.finiteRadius_nonneg T
  have herror : 0 ≤ dvoretzkyMilmanError (m := m) T := by
    exact mul_nonneg
      (mul_nonneg dvoretzkyMilmanConstant_pos.le (Real.sqrt_nonneg m))
      hradius
  have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg m)
  have herrorSq : (dvoretzkyMilmanError (m := m) T) ^ 2 ≤
      (HDP.Chapter7.gaussianWidth T / 100) ^ 2 := by
    dsimp [WithinDvoretzkyEffectiveDimension] at hdim
    dsimp [dvoretzkyMilmanError]
    rw [mul_pow, mul_pow, hsqrt]
    nlinarith [sq_nonneg dvoretzkyMilmanConstant,
      sq_nonneg (HDP.Chapter7.finiteRadius T)]
  have hsmall : dvoretzkyMilmanError (m := m) T ≤
      HDP.Chapter7.gaussianWidth T / 100 := by
    nlinarith [sq_nonneg (dvoretzkyMilmanError (m := m) T +
      HDP.Chapter7.gaussianWidth T / 100)]
  exact remark_9_7_3_nearlyRoundRadii hwidth herror hsmall

/-- Effective-dimension condition for the authoritative arbitrary-set
Dvoretzky--Milman theorem. The constant `201` is the explicit exhaustion
constant in `setDvoretzkyMilmanError`; the division-free formulation remains
valid when the set radius is zero.

**Lean implementation helper.** -/
def WithinSetDvoretzkyEffectiveDimension {n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (m : ℕ)
    (T : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (100 * 201 * generalMatrixDeviationConstant) ^ 2 * (m : ℝ) *
      setDvoretzkyRadius T ^ 2 ≤ setDvoretzkyWidth T ^ 2

/-- The Dvoretzky--Milman sandwich is nearly round above effective dimension. Arbitrary-set numerical core of Remark 9.7.3.

**Book Remark 9.7.3.** -/
theorem remark_9_7_3_effectiveDimension_set_radii {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple]
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (hdim : WithinSetDvoretzkyEffectiveDimension m T) :
    (99 / 100 : ℝ) * setDvoretzkyWidth T ≤
        dvoretzkyMilmanInnerRadius (setDvoretzkyWidth T)
          (setDvoretzkyMilmanError (m := m) T) ∧
      dvoretzkyMilmanOuterRadius (setDvoretzkyWidth T)
          (setDvoretzkyMilmanError (m := m) T) ≤
        (101 / 100 : ℝ) * setDvoretzkyWidth T := by
  have hwidth : 0 ≤ setDvoretzkyWidth T := setDvoretzkyWidth_nonneg T
  have hradius : 0 ≤ setDvoretzkyRadius T := setDvoretzkyRadius_nonneg T
  have herror : 0 ≤ setDvoretzkyMilmanError (m := m) T :=
    setDvoretzkyMilmanError_nonneg T
  have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg m)
  have herrorSq : (setDvoretzkyMilmanError (m := m) T) ^ 2 ≤
      (setDvoretzkyWidth T / 100) ^ 2 := by
    dsimp [WithinSetDvoretzkyEffectiveDimension] at hdim
    dsimp [setDvoretzkyMilmanError, setDvoretzkyMilmanBaseError]
    rw [mul_pow, mul_pow, mul_pow, hsqrt]
    nlinarith [sq_nonneg generalMatrixDeviationConstant,
      sq_nonneg (setDvoretzkyRadius T)]
  have hsmall : setDvoretzkyMilmanError (m := m) T ≤
      setDvoretzkyWidth T / 100 := by
    nlinarith [sq_nonneg (setDvoretzkyMilmanError (m := m) T +
      setDvoretzkyWidth T / 100)]
  exact remark_9_7_3_nearlyRoundRadii hwidth herror hsmall

/-- The Dvoretzky--Milman sandwich is nearly round above effective dimension. For every nonempty bounded convex set containing the origin, the canonical
Gaussian image of the whole set—not a selected finite cloud—has a closed
convex hull between the `0.99` and `1.01` balls with probability at least
`0.99`. Closure is mathematically necessary because the source does not
assume that `T` is closed.

**Book Remark 9.7.3.** -/
theorem remark_9_7_3_effectiveDimension_set {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (hm : 0 < m)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) (_hconv : Convex ℝ T)
    (_hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ T)
    (hdim : WithinSetDvoretzkyEffectiveDimension m T) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.stdGaussianMatrixMeasure n m
        {B | SetClosedHullBallSandwich
          (deterministicMatrixImageSet B.transpose T)
          ((99 / 100 : ℝ) * setDvoretzkyWidth T)
          ((101 / 100 : ℝ) * setDvoretzkyWidth T)} := by
  have hbase := theorem_9_7_2_dvoretzkyMilman hm T hT hTb
  have hradii := remark_9_7_3_effectiveDimension_set_radii T hdim
  have htargetNonneg : 0 ≤ (99 / 100 : ℝ) * setDvoretzkyWidth T :=
    mul_nonneg (by norm_num) (setDvoretzkyWidth_nonneg T)
  refine hbase.trans (measure_mono ?_)
  intro B hB
  constructor
  · exact (Metric.closedBall_subset_closedBall hradii.1).trans
      (hB.2 (htargetNonneg.trans hradii.1))
  · exact hB.1.trans (Metric.closedBall_subset_closedBall hradii.2)

/-! ### Example 9.7.4: the cube -/

/-- A vertex of `[-1,1]^n`, indexed by a Boolean sign pattern.

**Lean implementation helper.** -/
def cubeSignVector {n : ℕ} (s : Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ if s i = true then 1 else -1

/-- The finite vertex set of the cube. Its closed convex hull is the full
cube, so applying Theorem 9.7.2 to this set is exactly the source example.

**Book Theorem 9.7.2.** -/
def cubeVertexFinset (n : ℕ) : Finset (EuclideanSpace ℝ (Fin n)) :=
  by
    classical
    exact Finset.univ.image cubeSignVector

/-- The finite set of Boolean cube vertices is nonempty in every dimension.

**Lean implementation helper.** -/
theorem cubeVertexFinset_nonempty (n : ℕ) :
    (cubeVertexFinset n).Nonempty := by
  classical
  refine ⟨cubeSignVector (fun _ ↦ false), ?_⟩
  exact Finset.mem_image.mpr
    ⟨(fun _ ↦ false), Finset.mem_univ _, rfl⟩

/-- The actual cube body `[-1,1]^n`, transported to Euclidean space. This is
the source object in Example 9.7.4; `cubeVertexFinset` is the finite engine
used to prove its Gaussian-image statement.

**Book Example 9.7.4.** -/
def cubeBodySet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm ''
    HDP.Chapter1.linftyUnitBall

/-- Membership in the cube is equivalent to every coordinate lying between minus one and one.

**Lean implementation helper.** -/
theorem mem_cubeBodySet_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ cubeBodySet n ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  rw [cubeBodySet, HDP.Chapter1.linftyUnitBall_eq_cube]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    exact hf i (Set.mem_univ i)
  · intro hx
    refine ⟨fun i ↦ x i, ?_, ?_⟩
    · intro i hi
      exact hx i
    · rfl

/-- The Boolean enumeration is exactly the transported `{-1,1}^n` vertex
set used in Chapter 1.

**Lean implementation helper.** -/
theorem coe_cubeVertexFinset_eq_image_cubeVertices (n : ℕ) :
    (cubeVertexFinset n : Set (EuclideanSpace ℝ (Fin n))) =
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm ''
        HDP.Chapter1.cubeVertices := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    refine ⟨fun i ↦ if s i = true then 1 else -1, ?_, ?_⟩
    · intro i hi
      by_cases hsi : s i = true
      · simp [hsi]
      · simp [hsi]
    · rfl
  · rintro ⟨f, hf, rfl⟩
    let s : Fin n → Bool := fun i ↦ if f i = 1 then true else false
    apply Finset.mem_coe.mpr
    apply Finset.mem_image.mpr
    refine ⟨s, Finset.mem_univ _, ?_⟩
    ext i
    have hi := hf i (Set.mem_univ i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    by_cases hf1 : f i = 1
    · simp [cubeSignVector, s, hf1]
    · have hfneg : f i = -1 := hi.resolve_right hf1
      have hsi : s i = false := by simp [s, hf1]
      simp [cubeSignVector, hsi, hfneg]

/-- The actual cube is the convex hull of its Boolean vertices.

**Lean implementation helper.** -/
theorem cubeBodySet_eq_convexHull_cubeVertexFinset (n : ℕ) :
    cubeBodySet n = convexHull ℝ
      (cubeVertexFinset n : Set (EuclideanSpace ℝ (Fin n))) := by
  let L := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  calc
    cubeBodySet n = L '' HDP.Chapter1.linftyUnitBall := rfl
    _ = L '' convexHull ℝ HDP.Chapter1.cubeVertices := by
      rw [HDP.Chapter1.linftyUnitBall_eq_convexHull_cubeVertices]
    _ = convexHull ℝ (L '' HDP.Chapter1.cubeVertices) :=
      L.toLinearMap.image_convexHull _
    _ = convexHull ℝ
        (cubeVertexFinset n : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [coe_cubeVertexFinset_eq_image_cubeVertices]

/-- The finite-dimensional cube is compact.

**Lean implementation helper.** -/
theorem isCompact_cubeBodySet (n : ℕ) : IsCompact (cubeBodySet n) := by
  rw [cubeBodySet, HDP.Chapter1.linftyUnitBall_eq_cube]
  apply IsCompact.image (isCompact_univ_pi fun _ ↦ isCompact_Icc)
  let L : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  exact L.toContinuousLinearEquiv.continuous

/-- Closing the convex hull of the cube vertices recovers the actual cube.

**Lean implementation helper.** -/
theorem closedConvexHullSet_cubeVertexFinset_eq_cubeBodySet (n : ℕ) :
    closedConvexHullSet
        (cubeVertexFinset n : Set (EuclideanSpace ℝ (Fin n))) =
      cubeBodySet n := by
  rw [closedConvexHullSet, closedConvexHull_eq_closure_convexHull,
    ← cubeBodySet_eq_convexHull_cubeVertexFinset,
    (isCompact_cubeBodySet n).isClosed.closure_eq]

/-- A linear image of the actual cube is the convex hull of the images of
its vertices.

**Lean implementation helper.** -/
theorem deterministicMatrixImageSet_cubeBody_eq_convexHull_vertices
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    deterministicMatrixImageSet A (cubeBodySet n) =
      convexHull ℝ (deterministicMatrixImageSet A
        (cubeVertexFinset n : Set (EuclideanSpace ℝ (Fin n)))) := by
  rw [cubeBodySet_eq_convexHull_cubeVertexFinset]
  exact A.toEuclideanLin.image_convexHull _

/-- Consequently, the closed hull appearing in the source theorem is
literally the same whether it is presented using the full cube or its finite
vertex engine.

**Lean implementation helper.** -/
theorem closedConvexHullSet_cubeBody_image_eq_vertices_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    closedConvexHullSet (deterministicMatrixImageSet A (cubeBodySet n)) =
      closedConvexHullSet
        (↑(deterministicMatrixImageFinset A (cubeVertexFinset n)) :
          Set (EuclideanSpace ℝ (Fin m))) := by
  rw [coe_deterministicMatrixImageFinset,
    deterministicMatrixImageSet_cubeBody_eq_convexHull_vertices]
  unfold closedConvexHullSet
  rw [closedConvexHull_eq_closure_convexHull,
    closedConvexHull_eq_closure_convexHull,
    (convex_convexHull ℝ
      (deterministicMatrixImageSet A
        (cubeVertexFinset n : Set (EuclideanSpace ℝ (Fin n))))).convexHull_eq]

/-- Every sign vector in dimension `n` has Euclidean norm `sqrt n`.

**Lean implementation helper.** -/
theorem norm_cubeSignVector {n : ℕ} (s : Fin n → Bool) :
    ‖cubeSignVector s‖ = Real.sqrt n := by
  rw [← Real.sqrt_sq (norm_nonneg (cubeSignVector s)),
    EuclideanSpace.real_norm_sq_eq]
  simp [cubeSignVector]

/-- The radius, rather than the diameter, is the quantity used by Theorem
9.7.2. For the cube it is exactly `sqrt n`.

**Book Theorem 9.7.2.** -/
theorem finiteRadius_cubeVertexFinset (n : ℕ) :
    HDP.Chapter7.finiteRadius (cubeVertexFinset n) = Real.sqrt n := by
  classical
  rw [HDP.Chapter7.finiteRadius_eq_sup' _ (cubeVertexFinset_nonempty n)]
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    exact (norm_cubeSignVector s).le
  · exact (norm_cubeSignVector (fun _ ↦ false)).ge.trans
      (Finset.le_sup' norm (Finset.mem_image.mpr
        ⟨(fun _ ↦ false), Finset.mem_univ _, rfl⟩))

/-- Pointwise support of the cube vertices is the `ℓ1` norm.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_cubeVertexFinset {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n)) :
    HDP.Chapter7.finiteGaussianSupport (cubeVertexFinset n) g =
      ∑ i, |g i| := by
  classical
  rw [HDP.Chapter7.finiteGaussianSupport_eq_sup' _
    (cubeVertexFinset_nonempty n)]
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
    rw [PiLp.inner_apply]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hsi : s i = true
    · simpa [cubeSignVector, hsi] using le_abs_self (g i)
    · have hsfalse : s i = false := Bool.eq_false_of_not_eq_true hsi
      simpa [cubeSignVector, hsi, hsfalse] using neg_le_abs (g i)
  · let s : Fin n → Bool := fun i ↦ decide (0 ≤ g i)
    have hs : cubeSignVector s ∈ cubeVertexFinset n :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    calc
      ∑ i, |g i| = inner ℝ g (cubeSignVector s) := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hgi : 0 ≤ g i
        · simp [s, cubeSignVector, hgi, abs_of_nonneg hgi]
        · have hgi' : g i ≤ 0 := le_of_not_ge hgi
          simp [s, cubeSignVector, hgi, abs_of_nonpos hgi']
      _ ≤ (cubeVertexFinset n).sup' (cubeVertexFinset_nonempty n)
          (fun x ↦ inner ℝ g x) :=
        Finset.le_sup' (fun x ↦ inner ℝ g x) hs

/-- The Gaussian width of the cube vertices equals the standard cube Gaussian width.

**Lean implementation helper.** -/
theorem gaussianWidth_cubeVertexFinset (n : ℕ) :
    HDP.Chapter7.gaussianWidth (cubeVertexFinset n) =
      HDP.Chapter7.cubeGaussianWidth n := by
  rw [HDP.Chapter7.gaussianWidth, HDP.Chapter7.cubeGaussianWidth]
  apply integral_congr_ae
  filter_upwards [] with g
  exact finiteGaussianSupport_cubeVertexFinset g

/-- Exact Gaussian width of the cube.

**Book Example 9.7.4.** -/
theorem example_9_7_4_cubeGaussianWidth (n : ℕ) :
    HDP.Chapter7.gaussianWidth (cubeVertexFinset n) =
      Real.sqrt (2 / Real.pi) * n := by
  rw [gaussianWidth_cubeVertexFinset]
  exact HDP.Chapter7.cubeGaussianWidth_eq_source n

/-- Under the explicit
`m ≤ c n` form of the one-percent error condition, the Gaussian image of the
cube is between the `0.99` and `1.01` Euclidean balls of the stated radius.

**Book Example 9.7.4.** -/
theorem example_9_7_4_cubeNearlyRound {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (hm : 0 < m)
    (hdim : dvoretzkyMilmanConstant * Real.sqrt m * Real.sqrt n ≤
      (Real.sqrt (2 / Real.pi) * n) / 100) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.stdGaussianMatrixMeasure n m
        {B | DvoretzkyMilmanConclusion
          (deterministicMatrixImageFinset B.transpose (cubeVertexFinset n))
          ((99 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))
          ((101 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))} := by
  let T := cubeVertexFinset n
  have hT : T.Nonempty := cubeVertexFinset_nonempty n
  have hwidth : HDP.Chapter7.gaussianWidth T =
      Real.sqrt (2 / Real.pi) * n := example_9_7_4_cubeGaussianWidth n
  have hradius : HDP.Chapter7.finiteRadius T = Real.sqrt n :=
    finiteRadius_cubeVertexFinset n
  have herror : dvoretzkyMilmanError (m := m) T ≤
      HDP.Chapter7.gaussianWidth T / 100 := by
    rw [hwidth]
    simpa [dvoretzkyMilmanError, hradius] using hdim
  have hbase := theorem_9_7_2_dvoretzkyMilman_finite hm T hT
  refine hbase.trans (measure_mono ?_)
  intro B hB
  apply hB.mono
  · rw [hwidth]
    dsimp [dvoretzkyMilmanInnerRadius]
    nlinarith
  · rw [hwidth]
    dsimp [dvoretzkyMilmanOuterRadius]
    nlinarith

/-- A random proportional-dimensional image of the cube is almost round. This is the
source-facing version of `example_9_7_4_cubeNearlyRound`: its random set is
the image of the whole body `[-1,1]^n`. The finite vertex theorem above is
only the proof engine, connected to this statement by the exact convex-hull
bridge.

**Book Example 9.7.4.** -/
theorem example_9_7_4_cubeNearlyRound_set {m n : ℕ}
    [HDP.Chapter8.MajorizingMeasureLowerPrinciple] (hm : 0 < m)
    (hdim : dvoretzkyMilmanConstant * Real.sqrt m * Real.sqrt n ≤
      (Real.sqrt (2 / Real.pi) * n) / 100) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.stdGaussianMatrixMeasure n m
        {B | DvoretzkyMilmanSetConclusion
          (deterministicMatrixImageSet B.transpose (cubeBodySet n))
          ((99 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))
          ((101 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))} := by
  have hfinite := example_9_7_4_cubeNearlyRound hm hdim
  refine hfinite.trans (measure_mono ?_)
  intro B hB
  change DvoretzkyMilmanConclusion
    (deterministicMatrixImageFinset B.transpose (cubeVertexFinset n))
    ((99 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))
    ((101 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n)) at hB
  change DvoretzkyMilmanSetConclusion
    (deterministicMatrixImageSet B.transpose (cubeBodySet n))
    ((99 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))
    ((101 / 100 : ℝ) * (Real.sqrt (2 / Real.pi) * n))
  unfold DvoretzkyMilmanConclusion DvoretzkyMilmanSetConclusion at *
  rw [closedConvexHullSet_cubeBody_image_eq_vertices_image]
  exact hB

/-! ### Exercise 9.43: true Haar projections -/

/-- Zero-padding of the first `m` coordinates into `n` coordinates.

**Lean implementation helper.** -/
def firstCoordinateEmbedding {m n : ℕ} (_hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j =>
    if hj : j.val < m then z ⟨j.val, hj⟩ else 0

/-- The first-coordinate embedding copies the first `m` entries and fills the remaining coordinates with zero.

**Lean implementation helper.** -/
@[simp]
theorem firstCoordinateEmbedding_apply {m n : ℕ} (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    firstCoordinateEmbedding hmn z j =
      if hj : j.val < m then z ⟨j.val, hj⟩ else 0 := rfl

/-- Embedding into the first coordinates preserves Euclidean norm.

**Lean implementation helper.** -/
theorem norm_firstCoordinateEmbedding {m n : ℕ} (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin m)) :
    ‖firstCoordinateEmbedding hmn z‖ = ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [firstCoordinateEmbedding_apply]
  let F : Fin n → ℝ := fun j =>
    (if hj : j.val < m then z ⟨j.val, hj⟩ else 0) ^ 2
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin n)) := by
    simp
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      j ∉ Finset.univ.map e → F j = 0 := by
    intro j hj hjnot
    simp only [F]
    split_ifs with hjlt
    · exfalso
      apply hjnot
      exact Finset.mem_map.mpr
        ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · simp
  calc
    (∑ j : Fin n,
        (if hj : j.val < m then z ⟨j.val, hj⟩ else 0) ^ 2) =
        ∑ j : Fin n, F j := by rfl
    _ = ∑ j ∈ Finset.univ.map e, F j :=
      (Finset.sum_subset hsub hzero).symm
    _ = ∑ i : Fin m, F (e i) := by rw [Finset.sum_map]
    _ = ∑ i : Fin m, z i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [F, e, Fin.castLEEmb_apply]

/-- Orthonormal coordinates of the projection onto the Haar subspace encoded
by `U`. The corresponding ambient projection is onto the span of the first
`m` rows of `U`; changing the orthonormal coordinates only rotates `ℝ^m` and
therefore does not change a centered Euclidean-ball conclusion.

**Lean implementation helper.** -/
def haarCoordinateProjection {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  HDP.Chapter5.firstCoordinateRestriction hmn
    (HDP.Chapter5.orthogonalAction U x)

/-- Image of a finite set in orthonormal coordinates on a Haar subspace.

**Lean implementation helper.** -/
def haarCoordinateImageFinset {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin m)) :=
  T.image (haarCoordinateProjection hmn U)

/-- Image of an arbitrary set in orthonormal coordinates on the Haar
subspace. This is the source-facing set operation; the finset construction
above remains as the measurable finite engine.

**Lean implementation helper.** -/
def haarCoordinateImageSet {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  haarCoordinateProjection hmn U '' T

/-- The set underlying a finite Haar-coordinate image is the Haar-coordinate image of the underlying finite set.

**Lean implementation helper.** -/
theorem coe_haarCoordinateImageFinset {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    (haarCoordinateImageFinset hmn U T :
        Set (EuclideanSpace ℝ (Fin m))) =
      haarCoordinateImageSet hmn U (T : Set _) := by
  ext z
  simp [haarCoordinateImageFinset, haarCoordinateImageSet]

/-- The Haar-coordinate image of a nonempty finset is nonempty.

**Lean implementation helper.** -/
theorem haarCoordinateImageFinset_nonempty {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    {T : Finset (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (haarCoordinateImageFinset hmn U T).Nonempty :=
  hT.image _

/-- Haar rotation followed by coordinate restriction is norm nonincreasing.

**Lean implementation helper.** -/
theorem norm_haarCoordinateProjection_le {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖haarCoordinateProjection hmn U x‖ ≤ ‖x‖ := by
  calc
    ‖haarCoordinateProjection hmn U x‖ ≤
        ‖HDP.Chapter5.orthogonalAction U x‖ :=
      HDP.Chapter5.norm_firstCoordinateRestriction_le hmn _
    _ = ‖x‖ := HDP.Chapter5.norm_orthogonalAction U x

/-- A Haar-coordinate image has radius no larger than the source finset.

**Lean implementation helper.** -/
theorem finiteRadius_haarCoordinateImage_le {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    HDP.Chapter7.finiteRadius (haarCoordinateImageFinset hmn U T) ≤
      HDP.Chapter7.finiteRadius T := by
  rw [HDP.Chapter7.finiteRadius_eq_sup'
    (haarCoordinateImageFinset hmn U T)
    (haarCoordinateImageFinset_nonempty hmn U hT)]
  apply Finset.sup'_le
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact (norm_haarCoordinateProjection_le hmn U x).trans
    (HDP.Chapter7.norm_le_finiteRadius T hT hx)

/-- Coordinate restriction is adjoint to the first-coordinate embedding.

**Lean implementation helper.** -/
theorem inner_firstCoordinateRestriction {m n : ℕ} (hmn : m ≤ n)
    (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (HDP.Chapter5.firstCoordinateRestriction hmn x) z =
      inner ℝ x (firstCoordinateEmbedding hmn z) := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    HDP.Chapter5.firstCoordinateRestriction_apply,
    firstCoordinateEmbedding_apply]
  let F : Fin n → ℝ := fun j =>
    x j * (if hj : j.val < m then z ⟨j.val, hj⟩ else 0)
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin n)) := by
    simp
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      j ∉ Finset.univ.map e → F j = 0 := by
    intro j hj hjnot
    simp only [F]
    split_ifs with hjlt
    · exfalso
      apply hjnot
      exact Finset.mem_map.mpr
        ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · simp
  calc
    (∑ i : Fin m, x (Fin.castLE hmn i) * z i) =
        ∑ i : Fin m, F (e i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [F, e, Fin.castLEEmb_apply]
    _ = ∑ j ∈ Finset.univ.map e, F j := by rw [Finset.sum_map]
    _ = ∑ j : Fin n, F j := Finset.sum_subset hsub hzero
    _ = ∑ j : Fin n,
        x j * (if hj : j.val < m then z ⟨j.val, hj⟩ else 0) := by rfl

/-- The support direction of a coordinate Haar projection is the inverse Haar
orbit of the zero-padded direction.

**Lean implementation helper.** -/
theorem inner_haarCoordinateProjection {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ y (haarCoordinateProjection hmn U x) =
      inner ℝ
        (HDP.Chapter5.orthogonalAction U⁻¹
          (firstCoordinateEmbedding hmn y)) x := by
  rw [real_inner_comm]
  unfold haarCoordinateProjection
  rw [inner_firstCoordinateRestriction]
  let L := HDP.Chapter5.orthogonalLinearIsometryEquiv U⁻¹
  calc
    inner ℝ (HDP.Chapter5.orthogonalAction U x)
        (firstCoordinateEmbedding hmn y) =
        inner ℝ
          (HDP.Chapter5.orthogonalAction U⁻¹
            (HDP.Chapter5.orthogonalAction U x))
          (HDP.Chapter5.orthogonalAction U⁻¹
            (firstCoordinateEmbedding hmn y)) := by
      exact (L.inner_map_map
        (HDP.Chapter5.orthogonalAction U x)
        (firstCoordinateEmbedding hmn y)).symm
    _ = inner ℝ x
          (HDP.Chapter5.orthogonalAction U⁻¹
            (firstCoordinateEmbedding hmn y)) := by
      rw [← HDP.Chapter5.orthogonalAction_mul, inv_mul_cancel]
      simp [HDP.Chapter5.orthogonalAction]
    _ = _ := real_inner_comm _ _

/-- The support function of a finite Haar-coordinate image pulls back along the inverse rotation and coordinate embedding.

**Lean implementation helper.** -/
theorem finiteSupport_haarCoordinateImage_eq {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (y : EuclideanSpace ℝ (Fin m)) :
    finiteSupportFunctional (haarCoordinateImageFinset hmn U T) y =
      finiteSupportFunctional T
        (HDP.Chapter5.orthogonalAction U⁻¹
          (firstCoordinateEmbedding hmn y)) := by
  rw [finiteSupportFunctional, finiteSupportFunctional,
    HDP.Chapter7.finiteGaussianSupport_eq_sup'
      (haarCoordinateImageFinset hmn U T)
      (haarCoordinateImageFinset_nonempty hmn U hT),
    HDP.Chapter7.finiteGaussianSupport_eq_sup' T hT]
  unfold haarCoordinateImageFinset
  rw [Finset.sup'_image]
  apply Finset.sup'_congr hT rfl
  intro x hx
  exact inner_haarCoordinateProjection hmn U x y

/-- The one-direction failure probability used in the finite-net proof of
Exercise 9.43.

**Book Exercise 9.43.** -/
def haarCoordinateSupportTailBound (n : ℕ) (radius t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.exp
    (-t ^ 2 /
      (HDP.Chapter5.sphereConcentrationConstant * radius /
        Real.sqrt n) ^ 2))

/-- A fixed support direction of a Haar projection has the spherical
concentration tail at scale `rad(T)/sqrt n`.

**Lean implementation helper.** -/
theorem haarCoordinateSupport_tail {m n : ℕ} (hn : 0 < n)
    (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HDP.Chapter5.orthogonalHaarMeasure n
      {U | t ≤ |finiteSupportFunctional
          (haarCoordinateImageFinset hmn U T) y -
        HDP.Chapter7.sphericalWidth T|} ≤
      haarCoordinateSupportTailBound n
        (HDP.Chapter7.finiteRadius T) t := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteSupportFunctional T
  have hR : 0 ≤ HDP.Chapter7.finiteRadius T :=
    HDP.Chapter7.finiteRadius_nonneg T
  have hLip : LipschitzWith
      (⟨HDP.Chapter7.finiteRadius T, hR⟩ : ℝ≥0) F :=
    (finiteSupportSublinearFunctional T hT).lipschitzWith_of_growth hR
      (finiteSupportFunctional_growth T hT)
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨firstCoordinateEmbedding hmn y, by
      simpa [Metric.mem_sphere, dist_zero_right,
        norm_firstCoordinateEmbedding] using hy⟩
  let E : Set (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {q | t ≤ |F q - HDP.Chapter7.sphericalWidth T|}
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    exact (((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const
      (HDP.Chapter7.sphericalWidth T)).abs)
  have hmap := HDP.Chapter7.exercise_7_24_haarOrbit_uniform hn v
  have hsphere := HDP.Chapter5.unitSphere_lipschitz_tail_ambient
    n hn F (⟨HDP.Chapter7.finiteRadius T, hR⟩ : ℝ≥0) hLip ht
  have hmean : (∫ q : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1, F q
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      HDP.Chapter7.sphericalWidth T := rfl
  rw [hmean] at hsphere
  rw [← hmap, Measure.map_apply
    (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable hE]
    at hsphere
  change HDP.Chapter5.orthogonalHaarMeasure n
      ((HDP.Chapter5.inverseOrthogonalSphereOrbit v) ⁻¹' E) ≤
    ENNReal.ofReal (2 * Real.exp
      (-t ^ 2 /
        (HDP.Chapter5.sphereConcentrationConstant *
          HDP.Chapter7.finiteRadius T / Real.sqrt n) ^ 2)) at hsphere
  have hsphere' : HDP.Chapter5.orthogonalHaarMeasure n
      {U | t ≤ |finiteSupportFunctional T
          (HDP.Chapter5.orthogonalAction U⁻¹
            (firstCoordinateEmbedding hmn y)) -
        HDP.Chapter7.sphericalWidth T|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 /
          (HDP.Chapter5.sphereConcentrationConstant *
            HDP.Chapter7.finiteRadius T / Real.sqrt n) ^ 2)) := by
    simpa [E, F, v, HDP.Chapter5.inverseOrthogonalSphereOrbit,
      NNReal.coe_mk] using hsphere
  have hevent :
      {U | t ≤ |finiteSupportFunctional
          (haarCoordinateImageFinset hmn U T) y -
        HDP.Chapter7.sphericalWidth T|} =
      {U | t ≤ |finiteSupportFunctional T
          (HDP.Chapter5.orthogonalAction U⁻¹
            (firstCoordinateEmbedding hmn y)) -
        HDP.Chapter7.sphericalWidth T|} := by
    ext U
    change (t ≤ |finiteSupportFunctional
      (haarCoordinateImageFinset hmn U T) y -
        HDP.Chapter7.sphericalWidth T|) ↔
      (t ≤ |finiteSupportFunctional T
        (HDP.Chapter5.orthogonalAction U⁻¹
          (firstCoordinateEmbedding hmn y)) -
        HDP.Chapter7.sphericalWidth T|)
    rw [finiteSupport_haarCoordinateImage_eq hmn U T hT y]
  rw [hevent]
  simpa only [haarCoordinateSupportTailBound] using hsphere'

/-- Deterministic net extension for the Haar projection. This is the step
that converts finitely many scalar spherical-concentration estimates into the
two centered ball inclusions.

**Lean implementation helper.** -/
theorem closedHullBallSandwich_of_haarNetControl {m n : ℕ}
    (hn : 0 < n) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    {δ t ε : ℝ} (_hδ : 0 ≤ δ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hN : HDP.IsUnitSphereNet δ (N : Set (EuclideanSpace ℝ (Fin m))))
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hgood : ∀ y ∈ N,
      |finiteSupportFunctional (haarCoordinateImageFinset hmn U T) y -
        HDP.Chapter7.sphericalWidth T| < t)
    (haccuracy : t + HDP.Chapter7.finiteRadius T * δ ≤
      ε * HDP.Chapter7.sphericalWidth T) :
    ClosedHullBallSandwich (haarCoordinateImageFinset hmn U T)
      ((1 - ε) * HDP.Chapter7.sphericalWidth T)
      ((1 + ε) * HDP.Chapter7.sphericalWidth T) := by
  let S := haarCoordinateImageFinset hmn U T
  let w := HDP.Chapter7.sphericalWidth T
  let R := HDP.Chapter7.finiteRadius T
  have hS : S.Nonempty := haarCoordinateImageFinset_nonempty hmn U hT
  have hSrad : HDP.Chapter7.finiteRadius S ≤ R :=
    finiteRadius_haarCoordinateImage_le hmn U T hT
  have hSrad0 : 0 ≤ HDP.Chapter7.finiteRadius S :=
    HDP.Chapter7.finiteRadius_nonneg S
  have hLip : LipschitzWith
      (⟨HDP.Chapter7.finiteRadius S, hSrad0⟩ : ℝ≥0)
      (finiteSupportFunctional S) :=
    (finiteSupportSublinearFunctional S hS).lipschitzWith_of_growth hSrad0
      (finiteSupportFunctional_growth S hS)
  have hunit : ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 →
      |finiteSupportFunctional S y - w| ≤ ε * w := by
    intro y hy
    obtain ⟨z, hzN, hyz⟩ := hN.2 y hy
    have hz := (hgood z hzN).le
    have hdist := hLip.dist_le_mul y z
    have hdiff : |finiteSupportFunctional S y -
        finiteSupportFunctional S z| ≤ R * δ := by
      calc
        |finiteSupportFunctional S y - finiteSupportFunctional S z| =
            dist (finiteSupportFunctional S y)
              (finiteSupportFunctional S z) := by
          rw [Real.dist_eq]
        _ ≤ HDP.Chapter7.finiteRadius S * dist y z := hdist
        _ ≤ R * δ := by
          rw [dist_eq_norm]
          exact mul_le_mul hSrad hyz (norm_nonneg _)
            (hSrad0.trans hSrad)
    calc
      |finiteSupportFunctional S y - w| ≤
          |finiteSupportFunctional S y - finiteSupportFunctional S z| +
            |finiteSupportFunctional S z - w| := by
        calc
          |finiteSupportFunctional S y - w| =
              |(finiteSupportFunctional S y -
                finiteSupportFunctional S z) +
                (finiteSupportFunctional S z - w)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      _ ≤ R * δ + t := add_le_add hdiff hz
      _ ≤ ε * w := by
        dsimp [R, w] at haccuracy ⊢
        linarith
  have huniform : ∀ y : EuclideanSpace ℝ (Fin m),
      |finiteSupportFunctional S y - w * ‖y‖| ≤
        (ε * w) * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · subst y
      simp [finiteSupportFunctional,
        HDP.Chapter7.finiteGaussianSupport_eq_sup' S hS]
    · let q : EuclideanSpace ℝ (Fin m) := ‖y‖⁻¹ • y
      have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hqnorm : ‖q‖ = 1 := by
        simp [q, norm_smul, hypos.ne']
      have hq := hunit q hqnorm
      have hyrepr : y = ‖y‖ • q := by
        simp [q, hypos.ne']
      have hpos := finiteSupportFunctional_posHom S hS
        ‖y‖ hypos.le q
      rw [hyrepr, hpos, norm_smul, Real.norm_eq_abs,
        abs_of_pos hypos, hqnorm, mul_one]
      rw [show ‖y‖ * finiteSupportFunctional S q - w * ‖y‖ =
          ‖y‖ * (finiteSupportFunctional S q - w) by ring,
        abs_mul, abs_of_pos hypos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hq hypos.le)
  have hsandwich := finiteSupportSandwich_of_uniformDeviation
    S w (ε * w) huniform
  have hw : 0 ≤ w := HDP.Chapter7.sphericalWidth_nonneg T hT hn
  have hrMinus : 0 ≤ (1 - ε) * w :=
    mul_nonneg (sub_nonneg.mpr hε1) hw
  have hrPlus : 0 ≤ (1 + ε) * w :=
    mul_nonneg (by linarith) hw
  have hclosed :=
    (exercise_9_40_support_iff_closedHullBallSandwich_finite S hS
      (show 0 ≤ dvoretzkyMilmanInnerRadius w (ε * w) by
        dsimp [dvoretzkyMilmanInnerRadius]
        nlinarith)
      (show 0 ≤ dvoretzkyMilmanOuterRadius w (ε * w) by
        dsimp [dvoretzkyMilmanOuterRadius]
        nlinarith)).mp hsandwich
  change ClosedHullBallSandwich S ((1 - ε) * w) ((1 + ε) * w)
  convert hclosed using 1 <;>
    simp only [dvoretzkyMilmanInnerRadius, dvoretzkyMilmanOuterRadius] <;>
    ring

/-- Bad finite-net event in the proof of Exercise 9.43.

**Book Exercise 9.43.** -/
def HaarProjectionNetBadEvent {m n : ℕ} (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin m))) (t : ℝ) :
    Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
  {U | ∃ y ∈ N,
    t ≤ |finiteSupportFunctional (haarCoordinateImageFinset hmn U T) y -
      HDP.Chapter7.sphericalWidth T|}

/-- A unit-sphere net at an arbitrary positive scale, with the volumetric
cardinality bound needed to discharge the auxiliary net in Exercise 9.43.

**Book Exercise 9.43.** -/
theorem exists_unitSphereNet_card (d : ℕ) [NeZero d]
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin d)),
      HDP.IsUnitSphereNet (δ : ℝ) (N : Set (EuclideanSpace ℝ (Fin d))) ∧
      (N.card : ℝ≥0∞) ≤ (((2 / δ + 1 : ℝ≥0) : ℝ≥0∞) ^ d) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin d)) :=
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  have hcoverBound :
      (Metric.coveringNumber δ S : ℝ≥0∞) ≤
        (((2 / δ + 1 : ℝ≥0) : ℝ≥0∞) ^ d) := by
    simpa [S] using
      (HDP.Chapter4.corollary_4_2_11 (n := d) (ε := δ) hδ).2.2
  have hcoverFinite : Metric.coveringNumber δ S ≠ ⊤ := by
    intro htop
    rw [htop] at hcoverBound
    exact (not_le_of_gt (by simp :
      (((2 / δ + 1 : ℝ≥0) : ℝ≥0∞) ^ d) < ∞)) hcoverBound
  let Nset : Set (EuclideanSpace ℝ (Fin d)) := Metric.minimalCover δ S
  have hNfinite : Nset.Finite := Metric.finite_minimalCover
  let N : Finset (EuclideanSpace ℝ (Fin d)) := hNfinite.toFinset
  refine ⟨N, ?_, ?_⟩
  · constructor
    · intro x hx
      have hxNset : x ∈ Nset := by simpa [N] using hx
      have hxS : x ∈ S := Metric.minimalCover_subset hxNset
      simpa [S, Metric.mem_sphere, dist_zero_right] using hxS
    · intro x hx
      have hxS : x ∈ S := by
        simpa [S, Metric.mem_sphere, dist_zero_right] using hx
      obtain ⟨y, hyNset, hxy⟩ :=
        (Metric.isCover_minimalCover hcoverFinite) hxS
      refine ⟨y, by simpa [N] using hyNset, ?_⟩
      have hdist : dist x y ≤ (δ : ℝ) := by
        change edist x y ≤ (δ : ℝ≥0∞) at hxy
        rw [edist_nndist] at hxy
        have hnn : nndist x y ≤ δ := ENNReal.coe_le_coe.mp hxy
        change (nndist x y : ℝ) ≤ (δ : ℝ)
        exact NNReal.coe_le_coe.mpr hnn
      simpa [dist_eq_norm] using hdist
  · have hcard : (N.card : ℕ∞) = Metric.coveringNumber δ S := by
      rw [← hNfinite.encard_eq_coe_toFinset_card]
      exact Metric.encard_minimalCover hcoverFinite
    have hcard' : (N.card : ℝ≥0∞) =
        (Metric.coveringNumber δ S : ℝ≥0∞) := by
      exact_mod_cast hcard
    rw [hcard']
    exact hcoverBound

/-- The projection is represented in orthonormal coordinates on its random image
subspace, so both comparison balls genuinely live in `ℝ^m`. The two final
hypotheses are explicit deterministic net and union-bound conditions; unlike
the former placeholder, the probability conclusion is proved from Haar
spherical concentration and is not assumed from the caller.

**Book Exercise 9.43.** -/
theorem exercise_9_43_haarProjection_of_net {m n : ℕ}
    (hn : 0 < n) (_hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    {δ t ε : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hN : HDP.IsUnitSphereNet δ (N : Set (EuclideanSpace ℝ (Fin m))))
    (haccuracy : t + HDP.Chapter7.finiteRadius T * δ ≤
      ε * HDP.Chapter7.sphericalWidth T)
    (hunion : (N.card : ℝ≥0∞) *
      haarCoordinateSupportTailBound n
        (HDP.Chapter7.finiteRadius T) t ≤ 1 / 100) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.Chapter5.orthogonalHaarMeasure n
        {U | ClosedHullBallSandwich (haarCoordinateImageFinset hmn U T)
          ((1 - ε) * HDP.Chapter7.sphericalWidth T)
          ((1 + ε) * HDP.Chapter7.sphericalWidth T)} := by
  let bad := HaarProjectionNetBadEvent hmn T N t
  let E : EuclideanSpace ℝ (Fin m) →
      Set (Matrix.orthogonalGroup (Fin n) ℝ) := fun y =>
    {U | t ≤ |finiteSupportFunctional
        (haarCoordinateImageFinset hmn U T) y -
      HDP.Chapter7.sphericalWidth T|}
  have hbadEq : bad = ⋃ y ∈ N, E y := by
    ext U
    simp [bad, HaarProjectionNetBadEvent, E]
  have hEmeas : ∀ y ∈ N, MeasurableSet (E y) := by
    intro y hyN
    have hy : ‖y‖ = 1 := hN.1 y hyN
    let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨firstCoordinateEmbedding hmn y, by
        simpa [Metric.mem_sphere, dist_zero_right,
          norm_firstCoordinateEmbedding] using hy⟩
    let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteSupportFunctional T
    have hR : 0 ≤ HDP.Chapter7.finiteRadius T :=
      HDP.Chapter7.finiteRadius_nonneg T
    have hLip : LipschitzWith
        (⟨HDP.Chapter7.finiteRadius T, hR⟩ : ℝ≥0) F :=
      (finiteSupportSublinearFunctional T hT).lipschitzWith_of_growth hR
        (finiteSupportFunctional_growth T hT)
    have hbase : MeasurableSet
        {q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          t ≤ |F q - HDP.Chapter7.sphericalWidth T|} := by
      apply measurableSet_le measurable_const
      exact (((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const
        (HDP.Chapter7.sphericalWidth T)).abs)
    have heq : E y =
        (HDP.Chapter5.inverseOrthogonalSphereOrbit v) ⁻¹'
          {q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
            t ≤ |F q - HDP.Chapter7.sphericalWidth T|} := by
      ext U
      simp only [Set.mem_preimage, Set.mem_setOf_eq, E]
      rw [finiteSupport_haarCoordinateImage_eq hmn U T hT y]
      rfl
    rw [heq]
    exact hbase.preimage
      (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable
  have hbadMeas : MeasurableSet bad := by
    rw [hbadEq]
    exact N.measurableSet_biUnion hEmeas
  have hbadBound : HDP.Chapter5.orthogonalHaarMeasure n bad ≤ 1 / 100 := by
    rw [hbadEq]
    calc
      HDP.Chapter5.orthogonalHaarMeasure n (⋃ y ∈ N, E y) ≤
          ∑ y ∈ N, HDP.Chapter5.orthogonalHaarMeasure n (E y) :=
        measure_biUnion_finset_le N E
      _ ≤ ∑ _y ∈ N, haarCoordinateSupportTailBound n
          (HDP.Chapter7.finiteRadius T) t := by
        apply Finset.sum_le_sum
        intro y hyN
        exact haarCoordinateSupport_tail hn hmn T hT y (hN.1 y hyN) ht
      _ = (N.card : ℝ≥0∞) * haarCoordinateSupportTailBound n
          (HDP.Chapter7.finiteRadius T) t := by
        simp
      _ ≤ 1 / 100 := hunion
  have hgoodProb : ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.Chapter5.orthogonalHaarMeasure n badᶜ := by
    have hbad_le_one : HDP.Chapter5.orthogonalHaarMeasure n bad ≤ 1 := by
      calc
        HDP.Chapter5.orthogonalHaarMeasure n bad ≤
            HDP.Chapter5.orthogonalHaarMeasure n Set.univ :=
          measure_mono (Set.subset_univ bad)
        _ = 1 := measure_univ
    have hbadTop : HDP.Chapter5.orthogonalHaarMeasure n bad ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hbad_le_one
    rw [measure_compl hbadMeas hbadTop, measure_univ]
    exact ENNReal.le_sub_of_add_le_left hbadTop (by
      calc
        HDP.Chapter5.orthogonalHaarMeasure n bad +
            ENNReal.ofReal (99 / 100 : ℝ) ≤
            1 / 100 + ENNReal.ofReal (99 / 100 : ℝ) :=
          add_le_add_left hbadBound _
        _ = 1 := by
          rw [add_comm]
          have hone : (1 / 100 : ℝ≥0∞) =
              ENNReal.ofReal (1 / 100 : ℝ) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
          rw [hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num)
  have hgoodSubset : badᶜ ⊆
      {U | ClosedHullBallSandwich (haarCoordinateImageFinset hmn U T)
        ((1 - ε) * HDP.Chapter7.sphericalWidth T)
        ((1 + ε) * HDP.Chapter7.sphericalWidth T)} := by
    intro U hU
    apply closedHullBallSandwich_of_haarNetControl hn hmn T hT N hδ
      hε0.le hε1.le hN U
    · intro y hyN
      have hnot : ¬ t ≤ |finiteSupportFunctional
          (haarCoordinateImageFinset hmn U T) y -
        HDP.Chapter7.sphericalWidth T| := by
        intro hybad
        exact hU ⟨y, hyN, hybad⟩
      exact lt_of_not_ge hnot
    · exact haccuracy
  exact hgoodProb.trans (measure_mono hgoodSubset)

/-- The auxiliary sphere net is
now constructed internally. The last hypothesis is the explicit
metric-entropy/tail numerical condition expressing the source's low-
dimensional regime; it contains no probability conclusion.

**Book Exercise 9.43.** -/
theorem exercise_9_43_haarProjection {m n : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (δ : ℝ≥0) (hδ : 0 < δ)
    {t ε : ℝ} (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (haccuracy : t + HDP.Chapter7.finiteRadius T * (δ : ℝ) ≤
      ε * HDP.Chapter7.sphericalWidth T)
    (hentropyTail : (((2 / δ + 1 : ℝ≥0) : ℝ≥0∞) ^ m) *
      haarCoordinateSupportTailBound n
        (HDP.Chapter7.finiteRadius T) t ≤ 1 / 100) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.Chapter5.orthogonalHaarMeasure n
        {U | ClosedHullBallSandwich (haarCoordinateImageFinset hmn U T)
          ((1 - ε) * HDP.Chapter7.sphericalWidth T)
          ((1 + ε) * HDP.Chapter7.sphericalWidth T)} := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨N, hN, hNcard⟩ := exists_unitSphereNet_card m δ hδ
  have hunion : (N.card : ℝ≥0∞) *
      haarCoordinateSupportTailBound n
        (HDP.Chapter7.finiteRadius T) t ≤ 1 / 100 := by
    exact (mul_le_mul_left hNcard _).trans hentropyTail
  exact exercise_9_43_haarProjection_of_net hn hm hmn T hT N
    (δ := (δ : ℝ)) (t := t) (ε := ε) hδ.le ht hε0 hε1 hN
    haccuracy hunion

/-! ### Exercise 9.43 for an actual bounded set -/
/-- Spherical width is average support over a uniform unit-sphere direction.

**Book Definition 7.5.4.** -/
def boundedSetSphericalWidth {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    setSupportFunctional T q
    ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))

/-- The Haar-coordinate image of a nonempty set is nonempty.

**Lean implementation helper.** -/
theorem haarCoordinateImageSet_nonempty {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (haarCoordinateImageSet hmn U T).Nonempty :=
  hT.image _

/-- Haar rotation followed by coordinate restriction is `1`-Lipschitz.

**Lean implementation helper.** -/
theorem haarCoordinateProjection_lipschitz {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    LipschitzWith 1 (haarCoordinateProjection hmn U) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  calc
    ‖haarCoordinateProjection hmn U x - haarCoordinateProjection hmn U y‖ =
        ‖haarCoordinateProjection hmn U (x - y)‖ := by
      unfold haarCoordinateProjection
      rw [← map_sub]
      change ‖(HDP.Chapter5.firstCoordinateRestriction hmn)
          ((HDP.Chapter5.orthogonalLinearIsometryEquiv U) x -
            (HDP.Chapter5.orthogonalLinearIsometryEquiv U) y)‖ = _
      rw [← map_sub]
      rfl
    _ ≤ ‖x - y‖ := norm_haarCoordinateProjection_le hmn U _

/-- A Haar-coordinate image of a bounded set remains bounded.

**Lean implementation helper.** -/
theorem haarCoordinateImageSet_isBounded {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hTb : Bornology.IsBounded T) :
    Bornology.IsBounded (haarCoordinateImageSet hmn U T) := by
  exact (haarCoordinateProjection_lipschitz hmn U).isBounded_image hTb

/-- The support function of a Haar-coordinate image pulls back along the inverse rotation and coordinate embedding.

**Lean implementation helper.** -/
theorem setSupport_haarCoordinateImage_eq {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin m)) :
    setSupportFunctional (haarCoordinateImageSet hmn U T) y =
      setSupportFunctional T
        (HDP.Chapter5.orthogonalAction U⁻¹
          (firstCoordinateEmbedding hmn y)) := by
  unfold setSupportFunctional haarCoordinateImageSet
  congr 1
  ext r
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (inner_haarCoordinateProjection hmn U x y).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨haarCoordinateProjection hmn U x, ⟨x, hx, rfl⟩,
      inner_haarCoordinateProjection hmn U x y⟩

/-- The support radius of a Haar-coordinate image is at most the source support radius.

**Lean implementation helper.** -/
theorem setSupportRadius_haarCoordinateImage_le {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    setSupportRadius (haarCoordinateImageSet hmn U T) ≤
      setSupportRadius T := by
  unfold setSupportRadius
  apply csSup_le ((hT.image (haarCoordinateProjection hmn U)).image norm)
  rintro _ ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  exact (norm_haarCoordinateProjection_le hmn U x).trans
    (norm_le_setSupportRadius T hTb hx)

/-- A fixed-direction support function of the Haar-coordinate image satisfies the stated spherical concentration tail.

**Lean implementation helper.** -/
theorem haarCoordinateSupport_set_tail {m n : ℕ} (hn : 0 < n)
    (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HDP.Chapter5.orthogonalHaarMeasure n
      {U | t ≤ |setSupportFunctional
          (haarCoordinateImageSet hmn U T) y -
        boundedSetSphericalWidth T|} ≤
      haarCoordinateSupportTailBound n (setSupportRadius T) t := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ := setSupportFunctional T
  have hR : 0 ≤ setSupportRadius T := setSupportRadius_nonneg T hT hTb
  have hLip : LipschitzWith
      (⟨setSupportRadius T, hR⟩ : ℝ≥0) F :=
    (setSupportSublinearFunctional T hT hTb).lipschitzWith_of_growth hR
      (setSupportFunctional_growth T hT hTb)
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨firstCoordinateEmbedding hmn y, by
      simpa [Metric.mem_sphere, dist_zero_right,
        norm_firstCoordinateEmbedding] using hy⟩
  let E : Set (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {q | t ≤ |F q - boundedSetSphericalWidth T|}
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    exact (((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const
      (boundedSetSphericalWidth T)).abs)
  have hmap := HDP.Chapter7.exercise_7_24_haarOrbit_uniform hn v
  have hsphere := HDP.Chapter5.unitSphere_lipschitz_tail_ambient
    n hn F (⟨setSupportRadius T, hR⟩ : ℝ≥0) hLip ht
  have hmean : (∫ q : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1, F q
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      boundedSetSphericalWidth T := rfl
  rw [hmean] at hsphere
  rw [← hmap, Measure.map_apply
    (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable hE]
    at hsphere
  change HDP.Chapter5.orthogonalHaarMeasure n
      ((HDP.Chapter5.inverseOrthogonalSphereOrbit v) ⁻¹' E) ≤
    ENNReal.ofReal (2 * Real.exp
      (-t ^ 2 /
        (HDP.Chapter5.sphereConcentrationConstant *
          setSupportRadius T / Real.sqrt n) ^ 2)) at hsphere
  have hsphere' : HDP.Chapter5.orthogonalHaarMeasure n
      {U | t ≤ |setSupportFunctional T
          (HDP.Chapter5.orthogonalAction U⁻¹
            (firstCoordinateEmbedding hmn y)) -
        boundedSetSphericalWidth T|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-t ^ 2 /
          (HDP.Chapter5.sphereConcentrationConstant *
            setSupportRadius T / Real.sqrt n) ^ 2)) := by
    simpa [E, F, v, HDP.Chapter5.inverseOrthogonalSphereOrbit,
      NNReal.coe_mk] using hsphere
  have hevent :
      {U | t ≤ |setSupportFunctional
          (haarCoordinateImageSet hmn U T) y -
        boundedSetSphericalWidth T|} =
      {U | t ≤ |setSupportFunctional T
          (HDP.Chapter5.orthogonalAction U⁻¹
            (firstCoordinateEmbedding hmn y)) -
        boundedSetSphericalWidth T|} := by
    ext U
    change (t ≤ |setSupportFunctional
      (haarCoordinateImageSet hmn U T) y - boundedSetSphericalWidth T|) ↔
      (t ≤ |setSupportFunctional T
        (HDP.Chapter5.orthogonalAction U⁻¹
          (firstCoordinateEmbedding hmn y)) - boundedSetSphericalWidth T|)
    rw [setSupport_haarCoordinateImage_eq hmn U T y]
  rw [hevent]
  simpa only [haarCoordinateSupportTailBound] using hsphere'

/-- Uniform support-function deviation from a radial width gives inner and outer ball support bounds.

**Lean implementation helper.** -/
theorem boundedSetSupportSandwich_of_uniformDeviation {m : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : S.Nonempty) (hSb : Bornology.IsBounded S)
    (width error : ℝ)
    (hdev : ∀ y : EuclideanSpace ℝ (Fin m),
      |setSupportFunctional S y - width * ‖y‖| ≤ error * ‖y‖) :
    BoundedSetSupportSandwich S hS hSb
      (dvoretzkyMilmanInnerRadius width error)
      (dvoretzkyMilmanOuterRadius width error) := by
  intro y
  have h := hdev y
  rw [abs_le] at h
  change dvoretzkyMilmanInnerRadius width error * ‖y‖ ≤
      setSupportFunctional S y ∧
    setSupportFunctional S y ≤
      dvoretzkyMilmanOuterRadius width error * ‖y‖
  dsimp [dvoretzkyMilmanInnerRadius, dvoretzkyMilmanOuterRadius]
  constructor <;> nlinarith

/-- Support control on a spherical net yields a ball sandwich for the closed convex hull of the Haar-coordinate image.

**Lean implementation helper.** -/
theorem setClosedHullBallSandwich_of_haarNetControl {m n : ℕ}
    (_hn : 0 < n) (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    {δ t ε : ℝ} (_hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hN : HDP.IsUnitSphereNet δ (N : Set (EuclideanSpace ℝ (Fin m))))
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hgood : ∀ y ∈ N,
      |setSupportFunctional (haarCoordinateImageSet hmn U T) y -
        boundedSetSphericalWidth T| < t)
    (haccuracy : t + setSupportRadius T * δ ≤
      ε * boundedSetSphericalWidth T) :
    SetClosedHullBallSandwich (haarCoordinateImageSet hmn U T)
      ((1 - ε) * boundedSetSphericalWidth T)
      ((1 + ε) * boundedSetSphericalWidth T) := by
  let S := haarCoordinateImageSet hmn U T
  let w := boundedSetSphericalWidth T
  let R := setSupportRadius T
  have hS : S.Nonempty := haarCoordinateImageSet_nonempty hmn U hT
  have hSb : Bornology.IsBounded S := haarCoordinateImageSet_isBounded hmn U hTb
  have hSrad : setSupportRadius S ≤ R := setSupportRadius_haarCoordinateImage_le hmn U T hT hTb
  have hSrad0 : 0 ≤ setSupportRadius S := setSupportRadius_nonneg S hS hSb
  have hLip : LipschitzWith
      (⟨setSupportRadius S, hSrad0⟩ : ℝ≥0)
      (setSupportFunctional S) :=
    (setSupportSublinearFunctional S hS hSb).lipschitzWith_of_growth hSrad0
      (setSupportFunctional_growth S hS hSb)
  have hunit : ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ = 1 →
      |setSupportFunctional S y - w| ≤ ε * w := by
    intro y hy
    obtain ⟨z, hzN, hyz⟩ := hN.2 y hy
    have hz := (hgood z hzN).le
    have hdist := hLip.dist_le_mul y z
    have hdiff : |setSupportFunctional S y -
        setSupportFunctional S z| ≤ R * δ := by
      calc
        |setSupportFunctional S y - setSupportFunctional S z| =
            dist (setSupportFunctional S y)
              (setSupportFunctional S z) := by
          rw [Real.dist_eq]
        _ ≤ setSupportRadius S * dist y z := hdist
        _ ≤ R * δ := by
          rw [dist_eq_norm]
          exact mul_le_mul hSrad hyz (norm_nonneg _)
            (hSrad0.trans hSrad)
    calc
      |setSupportFunctional S y - w| ≤
          |setSupportFunctional S y - setSupportFunctional S z| +
            |setSupportFunctional S z - w| := by
        calc
          |setSupportFunctional S y - w| =
              |(setSupportFunctional S y - setSupportFunctional S z) +
                (setSupportFunctional S z - w)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      _ ≤ R * δ + t := add_le_add hdiff hz
      _ ≤ ε * w := by
        dsimp [R, w] at haccuracy ⊢
        linarith
  have huniform : ∀ y : EuclideanSpace ℝ (Fin m),
      |setSupportFunctional S y - w * ‖y‖| ≤
        (ε * w) * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · subst y
      have hs0 : setSupportFunctional S 0 = 0 := by
        unfold setSupportFunctional
        simp [hS]
      simp [hs0]
    · let q : EuclideanSpace ℝ (Fin m) := ‖y‖⁻¹ • y
      have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hqnorm : ‖q‖ = 1 := by
        simp [q, norm_smul, hypos.ne']
      have hq := hunit q hqnorm
      have hyrepr : y = ‖y‖ • q := by
        simp [q, hypos.ne']
      have hpos := setSupportFunctional_posHom S ‖y‖ hypos.le q
      rw [hyrepr, hpos, norm_smul, Real.norm_eq_abs,
        abs_of_pos hypos, hqnorm, mul_one]
      rw [show ‖y‖ * setSupportFunctional S q - w * ‖y‖ =
          ‖y‖ * (setSupportFunctional S q - w) by ring,
        abs_mul, abs_of_pos hypos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hq hypos.le)
  have hw : 0 ≤ w := by
    have hR0 : 0 ≤ R := by
      dsimp [R]
      exact setSupportRadius_nonneg T hT hTb
    have hleft : 0 ≤ t + R * δ :=
      add_nonneg ht (mul_nonneg hR0 _hδ)
    have hew : 0 ≤ ε * w := hleft.trans haccuracy
    nlinarith
  have hsandwich := boundedSetSupportSandwich_of_uniformDeviation
    S hS hSb w (ε * w) huniform
  have hrMinus : 0 ≤ (1 - ε) * w :=
    mul_nonneg (sub_nonneg.mpr hε1) hw
  have hrPlus : 0 ≤ (1 + ε) * w :=
    mul_nonneg (by linarith) hw
  have hclosed :=
    (boundedSetSupport_iff_setClosedHullBallSandwich S hS hSb
      (show 0 ≤ dvoretzkyMilmanInnerRadius w (ε * w) by
        dsimp [dvoretzkyMilmanInnerRadius]
        nlinarith)
      (show 0 ≤ dvoretzkyMilmanOuterRadius w (ε * w) by
        dsimp [dvoretzkyMilmanOuterRadius]
        nlinarith)).mp hsandwich
  change SetClosedHullBallSandwich S ((1 - ε) * w) ((1 + ε) * w)
  convert hclosed using 1 <;>
    simp only [dvoretzkyMilmanInnerRadius, dvoretzkyMilmanOuterRadius] <;>
    ring

/-- The bad event records Haar rotations for which some net direction has excessive support deviation.

**Lean implementation helper.** -/
def HaarProjectionSetNetBadEvent {m n : ℕ} (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin m))) (t : ℝ) :
    Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
  {U | ∃ y ∈ N,
    t ≤ |setSupportFunctional (haarCoordinateImageSet hmn U T) y -
      boundedSetSphericalWidth T|}

/-- Spherical-net support control yields the high-probability ball sandwich asserted in Exercise 9.43.

**Lean implementation helper.** -/
theorem exercise_9_43_haarProjection_set_of_net {m n : ℕ}
    (hn : 0 < n) (_hm : 0 < m) (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    {δ t ε : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hN : HDP.IsUnitSphereNet δ (N : Set (EuclideanSpace ℝ (Fin m))))
    (haccuracy : t + setSupportRadius T * δ ≤
      ε * boundedSetSphericalWidth T)
    (hunion : (N.card : ℝ≥0∞) *
      haarCoordinateSupportTailBound n (setSupportRadius T) t ≤ 1 / 100) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.Chapter5.orthogonalHaarMeasure n
        {U | SetClosedHullBallSandwich (haarCoordinateImageSet hmn U T)
          ((1 - ε) * boundedSetSphericalWidth T)
          ((1 + ε) * boundedSetSphericalWidth T)} := by
  let bad := HaarProjectionSetNetBadEvent hmn T N t
  let E : EuclideanSpace ℝ (Fin m) →
      Set (Matrix.orthogonalGroup (Fin n) ℝ) := fun y ↦
    {U | t ≤ |setSupportFunctional
        (haarCoordinateImageSet hmn U T) y - boundedSetSphericalWidth T|}
  have hbadEq : bad = ⋃ y ∈ N, E y := by
    ext U
    simp [bad, HaarProjectionSetNetBadEvent, E]
  have hEmeas : ∀ y ∈ N, MeasurableSet (E y) := by
    intro y hyN
    have hy : ‖y‖ = 1 := hN.1 y hyN
    let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨firstCoordinateEmbedding hmn y, by
        simpa [Metric.mem_sphere, dist_zero_right,
          norm_firstCoordinateEmbedding] using hy⟩
    let F : EuclideanSpace ℝ (Fin n) → ℝ := setSupportFunctional T
    have hR : 0 ≤ setSupportRadius T := setSupportRadius_nonneg T hT hTb
    have hLip : LipschitzWith
        (⟨setSupportRadius T, hR⟩ : ℝ≥0) F :=
      (setSupportSublinearFunctional T hT hTb).lipschitzWith_of_growth hR
        (setSupportFunctional_growth T hT hTb)
    have hbase : MeasurableSet
        {q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          t ≤ |F q - boundedSetSphericalWidth T|} := by
      apply measurableSet_le measurable_const
      exact (((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const
        (boundedSetSphericalWidth T)).abs)
    have heq : E y =
        (HDP.Chapter5.inverseOrthogonalSphereOrbit v) ⁻¹'
          {q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
            t ≤ |F q - boundedSetSphericalWidth T|} := by
      ext U
      simp only [Set.mem_preimage, Set.mem_setOf_eq, E]
      rw [setSupport_haarCoordinateImage_eq hmn U T y]
      rfl
    rw [heq]
    exact hbase.preimage
      (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable
  have hbadMeas : MeasurableSet bad := by
    rw [hbadEq]
    exact N.measurableSet_biUnion hEmeas
  have hbadBound : HDP.Chapter5.orthogonalHaarMeasure n bad ≤ 1 / 100 := by
    rw [hbadEq]
    calc
      HDP.Chapter5.orthogonalHaarMeasure n (⋃ y ∈ N, E y) ≤
          ∑ y ∈ N, HDP.Chapter5.orthogonalHaarMeasure n (E y) :=
        measure_biUnion_finset_le N E
      _ ≤ ∑ _y ∈ N, haarCoordinateSupportTailBound n (setSupportRadius T) t := by
        apply Finset.sum_le_sum
        intro y hyN
        exact haarCoordinateSupport_set_tail hn hmn T hT hTb y (hN.1 y hyN) ht
      _ = (N.card : ℝ≥0∞) * haarCoordinateSupportTailBound n
          (setSupportRadius T) t := by simp
      _ ≤ 1 / 100 := hunion
  have hgoodProb : ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.Chapter5.orthogonalHaarMeasure n badᶜ := by
    have hbad_le_one : HDP.Chapter5.orthogonalHaarMeasure n bad ≤ 1 := by
      calc
        HDP.Chapter5.orthogonalHaarMeasure n bad ≤
            HDP.Chapter5.orthogonalHaarMeasure n Set.univ :=
          measure_mono (Set.subset_univ bad)
        _ = 1 := measure_univ
    have hbadTop : HDP.Chapter5.orthogonalHaarMeasure n bad ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hbad_le_one
    rw [measure_compl hbadMeas hbadTop, measure_univ]
    exact ENNReal.le_sub_of_add_le_left hbadTop (by
      calc
        HDP.Chapter5.orthogonalHaarMeasure n bad +
            ENNReal.ofReal (99 / 100 : ℝ) ≤
            1 / 100 + ENNReal.ofReal (99 / 100 : ℝ) :=
          add_le_add_left hbadBound _
        _ = 1 := by
          rw [add_comm]
          have hone : (1 / 100 : ℝ≥0∞) =
              ENNReal.ofReal (1 / 100 : ℝ) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
          rw [hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num)
  have hgoodSubset : badᶜ ⊆
      {U | SetClosedHullBallSandwich (haarCoordinateImageSet hmn U T)
        ((1 - ε) * boundedSetSphericalWidth T)
        ((1 + ε) * boundedSetSphericalWidth T)} := by
    intro U hU
    apply setClosedHullBallSandwich_of_haarNetControl hn hmn T hT hTb N hδ ht hε0 hε1.le hN U
    · intro y hyN
      have hnot : ¬ t ≤ |setSupportFunctional
          (haarCoordinateImageSet hmn U T) y - boundedSetSphericalWidth T| := by
        intro hybad
        exact hU ⟨y, hyN, hybad⟩
      exact lt_of_not_ge hnot
    · exact haccuracy
  exact hgoodProb.trans (measure_mono hgoodSubset)

/-- True Haar random projections satisfy the almost-round sandwich.

**Book Exercise 9.43.** -/
theorem exercise_9_43_haarProjection_set {m n : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (δ : ℝ≥0) (hδ : 0 < δ)
    {t ε : ℝ} (ht : 0 ≤ t)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (haccuracy : t + setSupportRadius T * (δ : ℝ) ≤
      ε * boundedSetSphericalWidth T)
    (hentropyTail : (((2 / δ + 1 : ℝ≥0) : ℝ≥0∞) ^ m) *
      haarCoordinateSupportTailBound n (setSupportRadius T) t ≤ 1 / 100) :
    ENNReal.ofReal (99 / 100 : ℝ) ≤
      HDP.Chapter5.orthogonalHaarMeasure n
        {U | SetClosedHullBallSandwich (haarCoordinateImageSet hmn U T)
          ((1 - ε) * boundedSetSphericalWidth T)
          ((1 + ε) * boundedSetSphericalWidth T)} := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨N, hN, hNcard⟩ := exists_unitSphereNet_card m δ hδ
  have hunion : (N.card : ℝ≥0∞) *
      haarCoordinateSupportTailBound n (setSupportRadius T) t ≤ 1 / 100 := by
    exact (mul_le_mul_left hNcard _).trans hentropyTail
  exact exercise_9_43_haarProjection_set_of_net hn hm hmn T hT hTb N
    (δ := (δ : ℝ)) (t := t) (ε := ε) hδ.le ht hε0 hε1 hN
    haccuracy hunion

/-- The support functional of a finite subset is bounded by that of the ambient bounded set.

**Lean implementation helper.** -/
theorem finiteSupport_le_setSupport {n : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hTb : Bornology.IsBounded T)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hFT : (F : Set _) ⊆ T) (hF : F.Nonempty)
    (y : EuclideanSpace ℝ (Fin n)) :
    finiteSupportFunctional F y ≤ setSupportFunctional T y := by
  rw [finiteSupportFunctional,
    HDP.Chapter7.finiteGaussianSupport_eq_sup' F hF]
  apply Finset.sup'_le
  intro x hx
  exact le_csSup (setSupportFunctional_bddAbove T hTb y)
    ⟨x, hFT hx, rfl⟩

/-- Support functionals of the increasing dense prefixes converge to the support functional of the full set.

**Lean implementation helper.** -/
theorem tendsto_sourceDensePrefix_support {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (y : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto (fun k ↦ finiteSupportFunctional
        (sourceDensePrefix T hT k) y)
      Filter.atTop (nhds (setSupportFunctional T y)) := by
  letI : Nonempty T := hT.to_subtype
  rw [tendsto_order]
  constructor
  · intro a ha
    have hvaluesNonempty : ((fun x ↦ inner ℝ y x) '' T).Nonempty :=
      hT.image _
    obtain ⟨b, ⟨x, hx, rfl⟩, hab⟩ :=
      (lt_csSup_iff (setSupportFunctional_bddAbove T hTb y)
        hvaluesNonempty).mp ha
    let U : Set T := {z | a < inner ℝ y z.1}
    have hUopen : IsOpen U := by
      exact isOpen_lt continuous_const
        (continuous_const.inner continuous_subtype_val)
    have hUne : U.Nonempty := ⟨⟨x, hx⟩, hab⟩
    obtain ⟨i, hiU⟩ :=
      (TopologicalSpace.denseRange_denseSeq T).exists_mem_open hUopen hUne
    filter_upwards [Filter.eventually_ge_atTop i] with k hik
    have hi : sourceDensePoint T hT i ∈ sourceDensePrefix T hT k := by
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
    have hle := HDP.Chapter7.inner_le_finiteGaussianSupport
      (sourceDensePrefix T hT k)
      (sourceDensePrefix_nonempty T hT k) hi y
    exact hiU.trans_le (by
      simpa [finiteSupportFunctional, sourceDensePoint] using hle)
  · intro a ha
    filter_upwards [] with k
    exact (finiteSupport_le_setSupport hTb
      (sourceDensePrefix T hT k) (sourceDensePrefix_subset T hT k)
      (sourceDensePrefix_nonempty T hT k) y).trans_lt ha

/-- On a unit direction, the absolute support value is bounded by the support radius.

**Lean implementation helper.** -/
theorem abs_setSupport_unit_le {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T)
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ = 1) :
    |setSupportFunctional T y| ≤ setSupportRadius T := by
  rw [abs_le]
  constructor
  · obtain ⟨x, hx⟩ := hT
    have hinner : -setSupportRadius T ≤ inner ℝ y x := by
      calc
        -setSupportRadius T ≤ -‖x‖ :=
          neg_le_neg (norm_le_setSupportRadius T hTb hx)
        _ = -(‖y‖ * ‖x‖) := by rw [hy, one_mul]
        _ ≤ inner ℝ y x :=
          neg_le_of_abs_le (abs_real_inner_le_norm y x)
    exact hinner.trans (by
      change inner ℝ y x ≤ setSupportFunctional T y
      exact le_csSup (setSupportFunctional_bddAbove T hTb y)
        ⟨x, hx, rfl⟩)
  · simpa [hy, mul_one] using setSupportFunctional_growth T hT hTb y

/-- The support value of every dense prefix is bounded by the full set's radius on unit directions.

**Lean implementation helper.** -/
theorem abs_sourceDensePrefixSupport_unit_le {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) (k : ℕ)
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ = 1) :
    |finiteSupportFunctional (sourceDensePrefix T hT k) y| ≤
      setSupportRadius T := by
  let F := sourceDensePrefix T hT k
  have hF : F.Nonempty := sourceDensePrefix_nonempty T hT k
  have hFT : (F : Set _) ⊆ T := sourceDensePrefix_subset T hT k
  rw [abs_le]
  constructor
  · obtain ⟨x, hx⟩ := sourceDensePrefix_nonempty T hT k
    have hinner : -setSupportRadius T ≤ inner ℝ y x := by
      calc
        -setSupportRadius T ≤ -‖x‖ :=
          neg_le_neg (norm_le_setSupportRadius T hTb (hFT hx))
        _ = -(‖y‖ * ‖x‖) := by rw [hy, one_mul]
        _ ≤ inner ℝ y x :=
          neg_le_of_abs_le (abs_real_inner_le_norm y x)
    exact hinner.trans
      (HDP.Chapter7.inner_le_finiteGaussianSupport F
        (sourceDensePrefix_nonempty T hT k) hx y)
  · exact (finiteSupport_le_setSupport hTb F hFT hF y).trans
      (by simpa [hy, mul_one] using setSupportFunctional_growth T hT hTb y)

/-- Spherical widths of the dense prefixes converge to the spherical width of the bounded set.

**Lean implementation helper.** -/
theorem tendsto_sourceDensePrefix_sphericalWidth {n : ℕ} (hn : 0 < n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    Filter.Tendsto (fun k ↦ HDP.Chapter7.sphericalWidth
        (sourceDensePrefix T hT k))
      Filter.atTop (nhds (boundedSetSphericalWidth T)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  let R : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
    fun _ ↦ setSupportRadius T
  have hRintegrable : Integrable R
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) :=
    integrable_const _
  have hmeas : ∀ k, AEStronglyMeasurable
      (fun q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
        finiteSupportFunctional (sourceDensePrefix T hT k) q)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
    intro k
    exact (HDP.Chapter7.integrable_finiteGaussianSupport_unitSphere
      (sourceDensePrefix T hT k) hn).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ q : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)),
      ‖finiteSupportFunctional (sourceDensePrefix T hT k) q‖ ≤ R q := by
    intro k
    filter_upwards [] with q
    rw [Real.norm_eq_abs]
    apply abs_sourceDensePrefixSupport_unit_le T hT hTb k q
    simpa [← dist_zero_right] using q.property
  have hlim : ∀ᵐ q : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)),
      Filter.Tendsto (fun k ↦
        finiteSupportFunctional (sourceDensePrefix T hT k) q)
        Filter.atTop (nhds (setSupportFunctional T q)) := by
    filter_upwards [] with q
    exact tendsto_sourceDensePrefix_support T hT hTb q
  simpa only [HDP.Chapter7.sphericalWidth, boundedSetSphericalWidth,
    finiteSupportFunctional] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      R hmeas hRintegrable hbound hlim)

/-- The finite Euclidean diameter equals the metric diameter of the underlying finite set.

**Lean implementation helper.** -/
theorem finiteEuclideanDiameter_eq_diam_coe {n : ℕ}
    (F : Finset (EuclideanSpace ℝ (Fin n))) :
    HDP.Chapter7.finiteEuclideanDiameter F =
      Metric.diam (F : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  by_cases hF : F.Nonempty
  · apply le_antisymm
    · rw [HDP.Chapter7.finiteEuclideanDiameter_eq_sup' F hF]
      apply Finset.sup'_le
      intro p hp
      have hp' := Finset.mem_product.mp hp
      simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem
        F.finite_toSet.isBounded hp'.1 hp'.2
    · apply Metric.diam_le_of_forall_dist_le
        (HDP.Chapter7.finiteEuclideanDiameter_nonneg F)
      intro x hx y hy
      simpa [dist_eq_norm] using
        HDP.Chapter7.norm_sub_le_finiteEuclideanDiameter F hF hx hy
  · have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp [HDP.Chapter7.finiteEuclideanDiameter]

/-- The range of the selected dense sequence has the same closure as the source set.

**Lean implementation helper.** -/
theorem closure_sourceDenseRange {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    closure (Set.range (sourceDensePoint T hT)) = closure T := by
  letI : Nonempty T := hT.to_subtype
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨k, rfl⟩
      exact subset_closure (sourceDensePoint_mem T hT k)
    · exact isClosed_closure
  · apply closure_minimal
    · intro x hx
      let f : T → EuclideanSpace ℝ (Fin n) := fun z ↦ z.1
      have hfcont : Continuous f := continuous_subtype_val
      have hdense : Set.range (TopologicalSpace.denseSeq T) ⊆
          f ⁻¹' closure (Set.range (sourceDensePoint T hT)) := by
        rintro _ ⟨k, rfl⟩
        exact subset_closure ⟨k, rfl⟩
      have hall : ∀ z : T, f z ∈ closure
          (Set.range (sourceDensePoint T hT)) := by
        intro z
        have hz : z ∈ closure (Set.range
            (TopologicalSpace.denseSeq T)) := by
          rw [(TopologicalSpace.denseRange_denseSeq T).closure_range]
          trivial
        exact (closure_minimal hdense
          (isClosed_closure.preimage hfcont)) hz
      exact hall ⟨x, hx⟩
    · exact isClosed_closure

set_option maxHeartbeats 1000000 in
-- Comparing all pairs of a dense sequence through a common finite prefix
-- unfolds nested `ediam` and `iSup` definitions during elaboration.
/-- The extended diameter of the dense range is the supremum of the diameters of its finite prefixes.

**Lean implementation helper.** -/
theorem ediam_sourceDenseRange {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Metric.ediam (Set.range (sourceDensePoint T hT)) =
      ⨆ k, Metric.ediam
        ((sourceDensePrefix T hT k :
            Finset (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  apply le_antisymm
  · apply Metric.ediam_le
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    let k := max i j
    have hi : sourceDensePoint T hT i ∈ sourceDensePrefix T hT k := by
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_range.mpr (by dsimp [k]; omega), rfl⟩
    have hj : sourceDensePoint T hT j ∈ sourceDensePrefix T hT k := by
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_range.mpr (by dsimp [k]; omega), rfl⟩
    calc
      edist (sourceDensePoint T hT i) (sourceDensePoint T hT j) ≤
          Metric.ediam ((sourceDensePrefix T hT k : Finset _) : Set _) :=
        Metric.edist_le_ediam_of_mem
          (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj)
      _ ≤ ⨆ l, Metric.ediam
          ((sourceDensePrefix T hT l :
              Finset (EuclideanSpace ℝ (Fin n))) :
            Set (EuclideanSpace ℝ (Fin n))) :=
        le_iSup (fun l : ℕ ↦ Metric.ediam
          ((sourceDensePrefix T hT l :
              Finset (EuclideanSpace ℝ (Fin n))) :
            Set (EuclideanSpace ℝ (Fin n)))) k
  · apply iSup_le
    intro k
    apply Metric.ediam_mono
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact ⟨i, rfl⟩

set_option maxHeartbeats 1000000 in
-- Rewriting the set diameter through the preceding `iSup` identity requires
-- normalization of the same nested extended-distance expressions.
/-- The extended diameter of the source set is the supremum of the finite-prefix diameters.

**Lean implementation helper.** -/
theorem set_ediam_eq_iSup_sourceDensePrefixDiameter {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Metric.ediam T = ⨆ k, ENNReal.ofReal
      (HDP.Chapter7.finiteEuclideanDiameter
        (sourceDensePrefix T hT k)) := by
  calc
    Metric.ediam T = Metric.ediam (closure T) :=
      (Metric.ediam_closure T).symm
    _ = Metric.ediam (closure (Set.range (sourceDensePoint T hT))) := by
      rw [closure_sourceDenseRange T hT]
    _ = Metric.ediam (Set.range (sourceDensePoint T hT)) :=
      Metric.ediam_closure _
    _ = ⨆ k, Metric.ediam
        ((sourceDensePrefix T hT k :
            Finset (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) :=
      ediam_sourceDenseRange T hT
    _ = ⨆ k, ENNReal.ofReal
        (HDP.Chapter7.finiteEuclideanDiameter
          (sourceDensePrefix T hT k)) := by
      congr 1
      funext k
      rw [finiteEuclideanDiameter_eq_diam_coe, Metric.diam]
      exact (ENNReal.ofReal_toReal
        (sourceDensePrefix T hT k).finite_toSet.isBounded.ediam_ne_top).symm

/-- Diameters of the increasing dense prefixes converge to the diameter of the bounded source set.

**Lean implementation helper.** -/
theorem tendsto_sourceDensePrefix_diameter {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    Filter.Tendsto (fun k ↦ HDP.Chapter7.finiteEuclideanDiameter
        (sourceDensePrefix T hT k))
      Filter.atTop (nhds (Metric.diam T)) := by
  let d : ℕ → ℝ := fun k ↦ HDP.Chapter7.finiteEuclideanDiameter
    (sourceDensePrefix T hT k)
  have hmono : Monotone d := by
    intro k l hkl
    dsimp [d]
    rw [finiteEuclideanDiameter_eq_diam_coe, finiteEuclideanDiameter_eq_diam_coe]
    exact Metric.diam_mono
      (sourceDensePrefix_mono T hT hkl)
      (sourceDensePrefix T hT l).finite_toSet.isBounded
  have hbdd : BddAbove (Set.range d) := by
    refine ⟨Metric.diam T, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact HDP.Chapter9.finiteEuclideanDiameter_le_setDiameter
      hTb (sourceDensePrefix T hT k)
      (sourceDensePrefix_nonempty T hT k)
      (sourceDensePrefix_subset T hT k)
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have hsup : (⨆ k, d k) = Metric.diam T := by
    have he := congrArg ENNReal.toReal
      (set_ediam_eq_iSup_sourceDensePrefixDiameter T hT)
    rw [ENNReal.toReal_iSup] at he
    · simpa [d, ENNReal.toReal_ofReal,
        HDP.Chapter7.finiteEuclideanDiameter_nonneg, Metric.diam] using he.symm
    · intro k
      exact ENNReal.ofReal_ne_top
  rw [hsup] at hlim
  exact hlim

/-- The support function of a bounded set is integrable on the unit sphere.

**Lean implementation helper.** -/
theorem integrable_setSupport_unitSphere {n : ℕ} (hn : 0 < n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    Integrable (fun q : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ setSupportFunctional T q)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  have hR : 0 ≤ setSupportRadius T := setSupportRadius_nonneg T hT hTb
  have hLip : LipschitzWith (⟨setSupportRadius T, hR⟩ : ℝ≥0)
      (setSupportFunctional T) :=
    (setSupportSublinearFunctional T hT hTb).lipschitzWith_of_growth hR
      (setSupportFunctional_growth T hT hTb)
  apply (integrable_const (setSupportRadius T)).mono'
    (hLip.continuous.comp continuous_subtype_val).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs]
  apply abs_setSupport_unit_le T hT hTb q
  simpa [← dist_zero_right] using q.property

/-- The bounded set spherical width is nonnegative.

**Lean implementation helper.** -/
theorem boundedSetSphericalWidth_nonneg {n : ℕ} (hn : 0 < n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    0 ≤ boundedSetSphericalWidth T := by
  apply ge_of_tendsto (tendsto_sourceDensePrefix_sphericalWidth hn T hT hTb)
  filter_upwards [] with k
  exact HDP.Chapter7.sphericalWidth_nonneg
    (sourceDensePrefix T hT k) (sourceDensePrefix_nonempty T hT k) hn

/-- The extended-real spherical-width envelope is the nonnegative embedding of the actual spherical width.

**Lean implementation helper.** -/
theorem sphericalWidthEnvelope_eq_boundedSetSphericalWidth {n : ℕ} (hn : 0 < n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    sphericalWidthEnvelope T = ENNReal.ofReal (boundedSetSphericalWidth T) := by
  have hactualInt := integrable_setSupport_unitSphere hn T hT hTb
  have hupper : sphericalWidthEnvelope T ≤
      ENNReal.ofReal (boundedSetSphericalWidth T) := by
    unfold sphericalWidthEnvelope
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    change (∫ q : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1,
        finiteSupportFunctional F q
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
      ∫ q : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1,
        setSupportFunctional T q
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
    apply integral_mono
      (HDP.Chapter7.integrable_finiteGaussianSupport_unitSphere F hn)
      hactualInt
    intro q
    exact finiteSupport_le_setSupport hTb F hFT hF q
  apply le_antisymm hupper
  have htop : sphericalWidthEnvelope T ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hlim := tendsto_sourceDensePrefix_sphericalWidth hn T hT hTb
  have hrealBound : ∀ k, HDP.Chapter7.sphericalWidth
      (sourceDensePrefix T hT k) ≤
      (sphericalWidthEnvelope T).toReal := by
    intro k
    have hk := ofReal_sphericalWidth_le_sphericalWidthEnvelope
      (sourceDensePrefix T hT k) (sourceDensePrefix_subset T hT k)
      (sourceDensePrefix_nonempty T hT k)
    have hkr := ENNReal.toReal_mono htop hk
    simpa [ENNReal.toReal_ofReal,
      HDP.Chapter7.sphericalWidth_nonneg,
      sourceDensePrefix_nonempty T hT k, hn] using hkr
  have hwle : boundedSetSphericalWidth T ≤
      (sphericalWidthEnvelope T).toReal :=
    le_of_tendsto' hlim hrealBound
  calc
    ENNReal.ofReal (boundedSetSphericalWidth T) ≤
        ENNReal.ofReal (sphericalWidthEnvelope T).toReal :=
      ENNReal.ofReal_le_ofReal hwle
    _ = sphericalWidthEnvelope T := ENNReal.ofReal_toReal htop



/-! ### Remark 9.7.5: the projection phase transition -/

/-- Extended envelope of expected Haar-projection diameters over all
nonempty finite subfamilies of an arbitrary set.

**Lean implementation helper.** -/
def haarProjectionExpectedDiameterEnvelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (_hF : F.Nonempty),
    ENNReal.ofReal
      (∫ P, HDP.Chapter7.grassmannProjectedDiameter P F
        ∂HDP.Chapter5.grassmannHaarMeasure n m)

/-- Envelope of the classical `sqrt (m/n) · diam` term over the same finite
subfamilies.

**Lean implementation helper.** -/
def haarProjectionDiameterTermEnvelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (_hF : F.Nonempty),
    ENNReal.ofReal (Real.sqrt ((m : ℝ) / n) *
      HDP.Chapter7.finiteEuclideanDiameter F)

/-- Matched finite-family envelope of the two terms in the random-projection
diameter theorem. Keeping both terms indexed by the same family avoids
silently multiplying unrelated suprema.

**Lean implementation helper.** -/
def haarProjectionScaleEnvelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : Finset (EuclideanSpace ℝ (Fin n)))
      (_hFT : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ T)
      (_hF : F.Nonempty),
    ENNReal.ofReal (HDP.Chapter7.sphericalWidth F +
      Real.sqrt ((m : ℝ) / n) *
        HDP.Chapter7.finiteEuclideanDiameter F)

/-- The Haar-projected set is the image of the source set under the Grassmannian orthogonal projection.

**Lean implementation helper.** -/
def haarProjectedSet {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  HDP.Chapter5.randomProjection P '' T

/-- The Haar-projected diameter is the metric diameter of the projected source set.

**Lean implementation helper.** -/
def haarProjectedSetDiameter {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Metric.diam (haarProjectedSet P T)

/-- For a nonempty finset, projected diameter is the maximum projected distance over all ordered pairs.

**Lean implementation helper.** -/
private theorem grassmannProjectedDiameter_eq_sup'_internal {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) :
    HDP.Chapter7.grassmannProjectedDiameter P F =
      (F.product F).sup' (hF.product hF) (fun p =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖) := by
  classical
  let R := (F.product F).sup' (hF.product hF) (fun p =>
    ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
  have hR : 0 ≤ R := by
    have hFF := hF.product hF
    obtain ⟨x, hx⟩ := hF
    change 0 ≤ (F.product F).sup' hFF (fun p =>
      ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
    have hle := Finset.le_sup' (fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
      (show (x, x) ∈ F.product F from by simp [hx])
    simpa using hle
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le hR
    rintro a ha b hb
    simp only [HDP.Chapter7.grassmannProjectedFinset, Finset.coe_image,
      Set.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [dist_eq_norm, ← map_sub]
    exact Finset.le_sup' (fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
      (show (x, y) ∈ F.product F from
        Finset.mem_product.mpr ⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hy⟩)
  · apply Finset.sup'_le
    intro p hp
    have hp' := Finset.mem_product.mp hp
    rw [map_sub, ← dist_eq_norm]
    apply Metric.dist_le_diam_of_mem
    · exact (HDP.Chapter7.grassmannProjectedFinset P F).finite_toSet.isBounded
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.1, hp'.1, rfl⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.2, hp'.2, rfl⟩)

/-- The projected diameter of a fixed finite set is measurable on the Grassmannian.

**Lean implementation helper.** -/
theorem measurable_grassmannProjectedDiameter {m n : ℕ}
    (F : Finset (EuclideanSpace ℝ (Fin n))) :
    Measurable (fun P : HDP.Chapter5.Grassmannian n m =>
      HDP.Chapter7.grassmannProjectedDiameter P F) := by
  classical
  by_cases hF : F.Nonempty
  · rw [show (fun P : HDP.Chapter5.Grassmannian n m =>
        HDP.Chapter7.grassmannProjectedDiameter P F) =
      (F.product F).sup' (hF.product hF) (fun p =>
        fun P : HDP.Chapter5.Grassmannian n m =>
          HDP.Chapter5.grassmannProjectedNorm (p.1 - p.2) P) by
      funext P
      rw [grassmannProjectedDiameter_eq_sup'_internal P F hF]
      exact (Finset.sup'_apply (hF.product hF) (fun p =>
        fun P : HDP.Chapter5.Grassmannian n m =>
          HDP.Chapter5.grassmannProjectedNorm (p.1 - p.2) P) P).symm]
    apply Finset.measurable_sup'
    intro p hp
    exact (HDP.Chapter5.continuous_grassmannProjectedNorm
      (m := m) (p.1 - p.2)).measurable
  · have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp [HDP.Chapter7.grassmannProjectedDiameter,
      HDP.Chapter7.grassmannProjectedFinset]

/-- The extended diameter of a projected finset is the nonnegative embedding of its real diameter.

**Lean implementation helper.** -/
theorem grassmannProjectedFinset_ediam_eq_ofReal_diameter {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (F : Finset (EuclideanSpace ℝ (Fin n))) :
    Metric.ediam
        (↑(HDP.Chapter7.grassmannProjectedFinset P F) :
          Set (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal (HDP.Chapter7.grassmannProjectedDiameter P F) := by
  rw [HDP.Chapter7.grassmannProjectedDiameter, Metric.diam,
    ENNReal.ofReal_toReal]
  exact (HDP.Chapter7.grassmannProjectedFinset P F).finite_toSet.isBounded.ediam_ne_top

/-- Projecting a dense source sequence has the same closure as projecting the full source set.

**Lean implementation helper.** -/
theorem closure_haarProjectedDenseRange {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    closure (Set.range (fun k =>
        HDP.Chapter5.randomProjection P
          (HDP.Chapter9.sourceDensePoint T hT k))) =
      closure (haarProjectedSet P T) := by
  letI : Nonempty T := hT.to_subtype
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨k, rfl⟩
      exact subset_closure ⟨_, HDP.Chapter9.sourceDensePoint_mem T hT k, rfl⟩
    · exact isClosed_closure
  · apply closure_minimal
    · rintro _ ⟨x, hx, rfl⟩
      let f : T → EuclideanSpace ℝ (Fin n) := fun z =>
        HDP.Chapter5.randomProjection P z.1
      have hfcont : Continuous f :=
        (HDP.Chapter5.randomProjection P).continuous.comp continuous_subtype_val
      have hdense : Set.range (TopologicalSpace.denseSeq T) ⊆
          f ⁻¹' closure (Set.range (fun k =>
            HDP.Chapter5.randomProjection P
              (HDP.Chapter9.sourceDensePoint T hT k))) := by
        rintro _ ⟨k, rfl⟩
        exact subset_closure ⟨k, rfl⟩
      have hall : ∀ z : T, f z ∈ closure (Set.range (fun k =>
          HDP.Chapter5.randomProjection P
            (HDP.Chapter9.sourceDensePoint T hT k))) := by
        intro z
        have hz : z ∈ closure (Set.range (TopologicalSpace.denseSeq T)) := by
          rw [(TopologicalSpace.denseRange_denseSeq T).closure_range]
          trivial
        exact (closure_minimal hdense (isClosed_closure.preimage hfcont)) hz
      exact hall ⟨x, hx⟩
    · exact isClosed_closure

/-- The projected dense range has extended diameter equal to the supremum of its projected finite-prefix diameters.

**Lean implementation helper.** -/
theorem ediam_haarProjectedDenseRange {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Metric.ediam (Set.range (fun k =>
        HDP.Chapter5.randomProjection P
          (HDP.Chapter9.sourceDensePoint T hT k))) =
      ⨆ k, Metric.ediam
        (↑(HDP.Chapter7.grassmannProjectedFinset P
          (HDP.Chapter9.sourceDensePrefix T hT k)) :
          Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  apply le_antisymm
  · apply Metric.ediam_le
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    let k := max i j
    have hi : HDP.Chapter9.sourceDensePoint T hT i ∈
        HDP.Chapter9.sourceDensePrefix T hT k := by
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_range.mpr (by dsimp [k]; omega), rfl⟩
    have hj : HDP.Chapter9.sourceDensePoint T hT j ∈
        HDP.Chapter9.sourceDensePrefix T hT k := by
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_range.mpr (by dsimp [k]; omega), rfl⟩
    calc
      edist (HDP.Chapter5.randomProjection P
          (HDP.Chapter9.sourceDensePoint T hT i))
          (HDP.Chapter5.randomProjection P
            (HDP.Chapter9.sourceDensePoint T hT j)) ≤
          Metric.ediam
            (↑(HDP.Chapter7.grassmannProjectedFinset P
              (HDP.Chapter9.sourceDensePrefix T hT k)) :
              Set (EuclideanSpace ℝ (Fin n))) :=
        Metric.edist_le_ediam_of_mem
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, hi, rfl⟩))
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, hj, rfl⟩))
      _ ≤ ⨆ k, Metric.ediam
          (↑(HDP.Chapter7.grassmannProjectedFinset P
            (HDP.Chapter9.sourceDensePrefix T hT k)) :
            Set (EuclideanSpace ℝ (Fin n))) :=
        le_iSup (fun l : ℕ => Metric.ediam
          (↑(HDP.Chapter7.grassmannProjectedFinset P
            (HDP.Chapter9.sourceDensePrefix T hT l)) :
            Set (EuclideanSpace ℝ (Fin n)))) k
  · apply iSup_le
    intro k
    apply Metric.ediam_mono
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, rfl⟩

/-- The extended diameter of the projected set is the supremum of projected dense-prefix diameters.

**Lean implementation helper.** -/
theorem haarProjectedSet_ediam_eq_iSup_sourceDensePrefix {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Metric.ediam (haarProjectedSet P T) =
      ⨆ k, ENNReal.ofReal (HDP.Chapter7.grassmannProjectedDiameter P
        (HDP.Chapter9.sourceDensePrefix T hT k)) := by
  calc
    Metric.ediam (haarProjectedSet P T) =
        Metric.ediam (closure (haarProjectedSet P T)) :=
      (Metric.ediam_closure _).symm
    _ = Metric.ediam (closure (Set.range (fun k =>
        HDP.Chapter5.randomProjection P
          (HDP.Chapter9.sourceDensePoint T hT k)))) := by
      rw [closure_haarProjectedDenseRange P T hT]
    _ = Metric.ediam (Set.range (fun k =>
        HDP.Chapter5.randomProjection P
          (HDP.Chapter9.sourceDensePoint T hT k))) := Metric.ediam_closure _
    _ = ⨆ k, Metric.ediam
        (↑(HDP.Chapter7.grassmannProjectedFinset P
          (HDP.Chapter9.sourceDensePrefix T hT k)) :
          Set (EuclideanSpace ℝ (Fin n))) := ediam_haarProjectedDenseRange P T hT
    _ = ⨆ k, ENNReal.ofReal
        (HDP.Chapter7.grassmannProjectedDiameter P
          (HDP.Chapter9.sourceDensePrefix T hT k)) := by
      congr 1
      funext k
      exact grassmannProjectedFinset_ediam_eq_ofReal_diameter P _

/-- The extended diameter of the Haar-projected set is measurable on the Grassmannian.

**Lean implementation helper.** -/
theorem measurable_haarProjectedSet_ediam {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Measurable (fun P : HDP.Chapter5.Grassmannian n m =>
      Metric.ediam (haarProjectedSet P T)) := by
  simp_rw [haarProjectedSet_ediam_eq_iSup_sourceDensePrefix (T := T) (hT := hT)]
  apply Measurable.iSup
  intro k
  exact (measurable_grassmannProjectedDiameter
    (m := m) (HDP.Chapter9.sourceDensePrefix T hT k)).ennreal_ofReal

/-- The real diameter of the Haar-projected set is measurable on the Grassmannian.

**Lean implementation helper.** -/
theorem measurable_haarProjectedSetDiameter {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Measurable (fun P : HDP.Chapter5.Grassmannian n m =>
      haarProjectedSetDiameter P T) := by
  exact (measurable_haarProjectedSet_ediam (m := m) T hT).ennreal_toReal

/-- Orthogonal projection onto a Grassmannian subspace cannot increase Euclidean norm.

**Lean implementation helper.** -/
theorem norm_randomProjection_le_norm {m n : ℕ} (hmn : m ≤ n)
    (P : HDP.Chapter5.Grassmannian n m)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖HDP.Chapter5.randomProjection P z‖ ≤ ‖z‖ := by
  obtain ⟨U, hU⟩ := P.property
  have hP : P = HDP.Chapter5.grassmannOrbit n m U := Subtype.ext hU
  rw [hP, HDP.Chapter5.randomProjection_grassmannOrbit_norm hmn]
  exact (HDP.Chapter5.norm_firstCoordinateRestriction_le hmn _).trans_eq
    (HDP.Chapter5.norm_orthogonalAction U⁻¹ z)

/-- Orthogonal projection preserves boundedness of the source set.

**Lean implementation helper.** -/
theorem haarProjectedSet_isBounded {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hTb : Bornology.IsBounded T) :
    Bornology.IsBounded (haarProjectedSet P T) := by
  exact hTb.image (HDP.Chapter5.randomProjection P)

/-- The diameter of an orthogonal projection is at most the diameter of the source set.

**Lean implementation helper.** -/
theorem haarProjectedSetDiameter_le {m n : ℕ} (hmn : m ≤ n)
    (P : HDP.Chapter5.Grassmannian n m)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hTb : Bornology.IsBounded T) :
    haarProjectedSetDiameter P T ≤ Metric.diam T := by
  apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [dist_eq_norm, ← map_sub]
  calc
    ‖HDP.Chapter5.randomProjection P (x - y)‖ ≤ ‖x - y‖ :=
      norm_randomProjection_le_norm hmn P _
    _ = dist x y := (dist_eq_norm x y).symm
    _ ≤ Metric.diam T := Metric.dist_le_diam_of_mem hTb hx hy

/-- The diameter of a bounded Haar-projected set is integrable over the Grassmannian.

**Lean implementation helper.** -/
theorem integrable_haarProjectedSetDiameter {m n : ℕ} (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    Integrable (fun P : HDP.Chapter5.Grassmannian n m =>
      haarProjectedSetDiameter P T) (HDP.Chapter5.grassmannHaarMeasure n m) := by
  apply Integrable.of_bound
    (measurable_haarProjectedSetDiameter (m := m) T hT).aestronglyMeasurable
    (Metric.diam T)
  filter_upwards [] with P
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ haarProjectedSetDiameter P T from
    Metric.diam_nonneg)]
  exact haarProjectedSetDiameter_le hmn P hTb

/-- The expected extended diameter of the projected set is the supremum of expected finite-prefix projected diameters.

**Lean implementation helper.** -/
theorem lintegral_haarProjectedSet_ediam_eq_iSup_sourceDensePrefix {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    (∫⁻ P, Metric.ediam (haarProjectedSet P T)
        ∂HDP.Chapter5.grassmannHaarMeasure n m) =
      ⨆ k, ∫⁻ P, ENNReal.ofReal
        (HDP.Chapter7.grassmannProjectedDiameter P
          (HDP.Chapter9.sourceDensePrefix T hT k))
        ∂HDP.Chapter5.grassmannHaarMeasure n m := by
  simp_rw [haarProjectedSet_ediam_eq_iSup_sourceDensePrefix (T := T) (hT := hT)]
  apply MeasureTheory.lintegral_iSup
  · intro k
    exact (measurable_grassmannProjectedDiameter
      (m := m) (HDP.Chapter9.sourceDensePrefix T hT k)).ennreal_ofReal
  · intro k l hkl P
    apply ENNReal.ofReal_le_ofReal
    apply Metric.diam_mono
    · simp only [HDP.Chapter7.grassmannProjectedFinset, Finset.coe_image]
      exact Set.image_mono (HDP.Chapter9.sourceDensePrefix_mono T hT hkl)
    · exact (HDP.Chapter7.grassmannProjectedFinset P
        (HDP.Chapter9.sourceDensePrefix T hT l)).finite_toSet.isBounded

/-- For a bounded source set, projected extended diameter is the nonnegative embedding of projected real diameter.

**Lean implementation helper.** -/
theorem haarProjectedSet_ediam_eq_ofReal_diameter {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hTb : Bornology.IsBounded T) :
    Metric.ediam (haarProjectedSet P T) =
      ENNReal.ofReal (haarProjectedSetDiameter P T) := by
  rw [haarProjectedSetDiameter, Metric.diam, ENNReal.ofReal_toReal]
  exact (haarProjectedSet_isBounded P hTb).ediam_ne_top

/-- For a finite source set, set-level projected diameter agrees with the finite projected diameter.

**Lean implementation helper.** -/
theorem haarProjectedSetDiameter_coe_finset {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (F : Finset (EuclideanSpace ℝ (Fin n))) :
    haarProjectedSetDiameter P (↑F : Set (EuclideanSpace ℝ (Fin n))) =
      HDP.Chapter7.grassmannProjectedDiameter P F := by
  simp only [haarProjectedSetDiameter, haarProjectedSet,
    HDP.Chapter7.grassmannProjectedDiameter,
    HDP.Chapter7.grassmannProjectedFinset, Finset.coe_image]

/-- The projected diameter of a nonempty finite set is integrable over the Grassmannian.

**Lean implementation helper.** -/
theorem integrable_grassmannProjectedDiameter {m n : ℕ} (hmn : m ≤ n)
    (F : Finset (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) :
    Integrable (fun P : HDP.Chapter5.Grassmannian n m =>
      HDP.Chapter7.grassmannProjectedDiameter P F)
      (HDP.Chapter5.grassmannHaarMeasure n m) := by
  simpa only [haarProjectedSetDiameter_coe_finset] using
    integrable_haarProjectedSetDiameter hmn
      (↑F : Set (EuclideanSpace ℝ (Fin n)))
      (by simpa using hF)
      F.finite_toSet.isBounded

/-- The nonnegative embedding of expected projected diameter equals the expected extended diameter.

**Lean implementation helper.** -/
theorem ofReal_integral_haarProjectedSetDiameter_eq_lintegral_ediam {m n : ℕ}
    (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    ENNReal.ofReal
        (∫ P, haarProjectedSetDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) =
      ∫⁻ P, Metric.ediam (haarProjectedSet P T)
        ∂HDP.Chapter5.grassmannHaarMeasure n m := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_haarProjectedSetDiameter hmn T hT hTb)
    (Filter.Eventually.of_forall (fun _ => Metric.diam_nonneg))]
  apply MeasureTheory.lintegral_congr
  intro P
  exact (haarProjectedSet_ediam_eq_ofReal_diameter P hTb).symm

/-- Expected projected diameter is recovered as the supremum of expected projected dense-prefix diameters.

**Lean implementation helper.** -/
theorem ofReal_haarProjectedSetExpectedDiameter_eq_iSup_sourceDensePrefix {m n : ℕ}
    (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    ENNReal.ofReal
        (∫ P, haarProjectedSetDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) =
      ⨆ k, ENNReal.ofReal
        (∫ P, HDP.Chapter7.grassmannProjectedDiameter P
            (HDP.Chapter9.sourceDensePrefix T hT k)
          ∂HDP.Chapter5.grassmannHaarMeasure n m) := by
  rw [ofReal_integral_haarProjectedSetDiameter_eq_lintegral_ediam hmn T hT hTb,
    lintegral_haarProjectedSet_ediam_eq_iSup_sourceDensePrefix T hT]
  congr 1
  funext k
  symm
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
  · exact integrable_grassmannProjectedDiameter hmn _
      (HDP.Chapter9.sourceDensePrefix_nonempty T hT k)
  · exact Filter.Eventually.of_forall (fun _ => Metric.diam_nonneg)

/-- The envelope for expected Haar-projection diameter equals the actual expectation for bounded nonempty sets.

**Lean implementation helper.** -/
theorem haarProjectionExpectedDiameterEnvelope_eq_actual {m n : ℕ}
    (hmn : m ≤ n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    HDP.Chapter9.haarProjectionExpectedDiameterEnvelope (m := m) T =
      ENNReal.ofReal
        (∫ P, haarProjectedSetDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) := by
  apply le_antisymm
  · unfold HDP.Chapter9.haarProjectionExpectedDiameterEnvelope
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    apply MeasureTheory.integral_mono
    · exact integrable_grassmannProjectedDiameter hmn F hF
    · exact integrable_haarProjectedSetDiameter hmn T hT hTb
    · intro P
      change HDP.Chapter7.grassmannProjectedDiameter P F ≤ haarProjectedSetDiameter P T
      rw [← haarProjectedSetDiameter_coe_finset P F]
      apply Metric.diam_mono
      · exact Set.image_mono hFT
      · exact haarProjectedSet_isBounded P hTb
  · rw [ofReal_haarProjectedSetExpectedDiameter_eq_iSup_sourceDensePrefix hmn T hT hTb]
    apply iSup_le
    intro k
    unfold HDP.Chapter9.haarProjectionExpectedDiameterEnvelope
    exact le_iSup_of_le (HDP.Chapter9.sourceDensePrefix T hT k)
      (le_iSup_of_le (HDP.Chapter9.sourceDensePrefix_subset T hT k)
        (le_iSup_of_le (HDP.Chapter9.sourceDensePrefix_nonempty T hT k) le_rfl))


/-- The genuine expected diameter of the Haar projection of the actual set.

**Lean implementation helper.** -/
def haarProjectionExpectedDiameter {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ P, haarProjectedSetDiameter P T
    ∂HDP.Chapter5.grassmannHaarMeasure n m

/-- The actual classical diameter term in Remark 9.7.5.

**Book Remark 9.7.5.** -/
def haarProjectionDiameterTerm {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Real.sqrt ((m : ℝ) / n) * Metric.diam T

/-- The actual two-term scale in the random-projection diameter theorem.

**Lean implementation helper.** -/
def haarProjectionScale {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  boundedSetSphericalWidth T + haarProjectionDiameterTerm (m := m) T

/-- The Haar-projection scale envelope agrees with the scale built from actual spherical width and expected projected diameter.

**Lean implementation helper.** -/
theorem haarProjectionScaleEnvelope_eq_actualScale {m n : ℕ}
    (hn : 0 < n)
    (T : Set (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hTb : Bornology.IsBounded T) :
    haarProjectionScaleEnvelope (m := m) T =
      ENNReal.ofReal (boundedSetSphericalWidth T +
        Real.sqrt ((m : ℝ) / n) * Metric.diam T) := by
  let a : ℝ := Real.sqrt ((m : ℝ) / n)
  let S : ℝ := boundedSetSphericalWidth T + a * Metric.diam T
  have hw0 := boundedSetSphericalWidth_nonneg hn T hT hTb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S :=
    add_nonneg hw0 (mul_nonneg ha0 Metric.diam_nonneg)
  have hactualInt := integrable_setSupport_unitSphere hn T hT hTb
  have hupper : haarProjectionScaleEnvelope (m := m) T ≤
      ENNReal.ofReal S := by
    unfold haarProjectionScaleEnvelope
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    have hwF : HDP.Chapter7.sphericalWidth F ≤
        boundedSetSphericalWidth T := by
      change (∫ q : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1,
          finiteSupportFunctional F q
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        ∫ q : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1,
          setSupportFunctional T q
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
      apply integral_mono
        (HDP.Chapter7.integrable_finiteGaussianSupport_unitSphere F hn)
        hactualInt
      intro q
      exact finiteSupport_le_setSupport hTb F hFT hF q
    have hdF := HDP.Chapter9.finiteEuclideanDiameter_le_setDiameter
      hTb F hF hFT
    dsimp [S, a]
    exact add_le_add hwF (mul_le_mul_of_nonneg_left hdF ha0)
  apply le_antisymm hupper
  have htop : haarProjectionScaleEnvelope (m := m) T ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hlim : Filter.Tendsto (fun k ↦
      HDP.Chapter7.sphericalWidth (sourceDensePrefix T hT k) +
        a * HDP.Chapter7.finiteEuclideanDiameter
          (sourceDensePrefix T hT k))
      Filter.atTop (nhds S) := by
    dsimp [S]
    exact (tendsto_sourceDensePrefix_sphericalWidth hn T hT hTb).add
      ((tendsto_sourceDensePrefix_diameter T hT hTb).const_mul a)
  have hrealBound : ∀ k,
      HDP.Chapter7.sphericalWidth (sourceDensePrefix T hT k) +
        a * HDP.Chapter7.finiteEuclideanDiameter
          (sourceDensePrefix T hT k) ≤
        (haarProjectionScaleEnvelope (m := m) T).toReal := by
    intro k
    have hk : ENNReal.ofReal
        (HDP.Chapter7.sphericalWidth (sourceDensePrefix T hT k) +
          a * HDP.Chapter7.finiteEuclideanDiameter
            (sourceDensePrefix T hT k)) ≤
        haarProjectionScaleEnvelope (m := m) T := by
      unfold haarProjectionScaleEnvelope
      exact le_iSup_of_le (sourceDensePrefix T hT k)
        (le_iSup_of_le (sourceDensePrefix_subset T hT k)
          (le_iSup_of_le (sourceDensePrefix_nonempty T hT k)
            (by rfl)))
    have hkr := ENNReal.toReal_mono htop hk
    rw [ENNReal.toReal_ofReal] at hkr
    · exact hkr
    · exact add_nonneg
        (HDP.Chapter7.sphericalWidth_nonneg
          (sourceDensePrefix T hT k)
          (sourceDensePrefix_nonempty T hT k) hn)
        (mul_nonneg ha0
          (HDP.Chapter7.finiteEuclideanDiameter_nonneg _))
  have hSle : S ≤
      (haarProjectionScaleEnvelope (m := m) T).toReal :=
    le_of_tendsto' hlim hrealBound
  calc
    ENNReal.ofReal S ≤
        ENNReal.ofReal (haarProjectionScaleEnvelope (m := m) T).toReal :=
      ENNReal.ofReal_le_ofReal hSle
    _ = haarProjectionScaleEnvelope (m := m) T :=
      ENNReal.ofReal_toReal htop


/-- Arbitrary-set finite-subfamily-envelope form of the two-sided expected
diameter theorem underlying Remark 9.7.5.

**Book Remark 9.7.5.** -/
theorem haarProjection_expectedDiameter_envelope :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ T : Set (EuclideanSpace ℝ (Fin n)),
        ENNReal.ofReal c * haarProjectionScaleEnvelope (m := m) T ≤
            haarProjectionExpectedDiameterEnvelope (m := m) T ∧
          haarProjectionExpectedDiameterEnvelope (m := m) T ≤
            ENNReal.ofReal C *
              haarProjectionScaleEnvelope (m := m) T := by
  obtain ⟨c, C, hc, hC, hprojection⟩ :=
    HDP.Chapter7.randomProjection_expectedDiameter
  refine ⟨c, C, hc, hC, ?_⟩
  intro m n hn hm hmn T
  constructor
  · rw [haarProjectionScaleEnvelope, ENNReal.mul_iSup]
    apply iSup_le
    intro F
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro hFT
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro hF
    have hbase := hprojection hn hm hmn F hF
    calc
      ENNReal.ofReal c * ENNReal.ofReal
          (HDP.Chapter7.sphericalWidth F +
            Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter F) =
          ENNReal.ofReal (c *
            (HDP.Chapter7.sphericalWidth F +
              Real.sqrt ((m : ℝ) / n) *
                HDP.Chapter7.finiteEuclideanDiameter F)) := by
        rw [ENNReal.ofReal_mul hc.le]
      _ ≤ ENNReal.ofReal
          (∫ P, HDP.Chapter7.grassmannProjectedDiameter P F
            ∂HDP.Chapter5.grassmannHaarMeasure n m) :=
        ENNReal.ofReal_le_ofReal hbase.1
      _ ≤ haarProjectionExpectedDiameterEnvelope (m := m) T := by
        unfold haarProjectionExpectedDiameterEnvelope
        exact le_iSup_of_le F
          (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
  · unfold haarProjectionExpectedDiameterEnvelope
    apply iSup_le
    intro F
    apply iSup_le
    intro hFT
    apply iSup_le
    intro hF
    have hbase := hprojection hn hm hmn F hF
    have hterm : ENNReal.ofReal
        (HDP.Chapter7.sphericalWidth F +
          Real.sqrt ((m : ℝ) / n) *
            HDP.Chapter7.finiteEuclideanDiameter F) ≤
        haarProjectionScaleEnvelope (m := m) T := by
      unfold haarProjectionScaleEnvelope
      exact le_iSup_of_le F
        (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))
    calc
      ENNReal.ofReal
          (∫ P, HDP.Chapter7.grassmannProjectedDiameter P F
            ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
          ENNReal.ofReal (C *
            (HDP.Chapter7.sphericalWidth F +
              Real.sqrt ((m : ℝ) / n) *
                HDP.Chapter7.finiteEuclideanDiameter F)) :=
        ENNReal.ofReal_le_ofReal hbase.2
      _ = ENNReal.ofReal C * ENNReal.ofReal
          (HDP.Chapter7.sphericalWidth F +
            Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter F) := by
        rw [ENNReal.ofReal_mul hC.le]
      _ ≤ ENNReal.ofReal C *
          haarProjectionScaleEnvelope (m := m) T := by gcongr

/-- Random projections exhibit high- and low-dimensional width/diameter phases. The genuine arbitrary-set expected-diameter theorem behind Remark 9.7.5.
Both the expectation and the comparison scale are evaluated on the actual
bounded set; the finite-family envelopes occur only inside the proof.

**Book Remark 9.7.5.** -/
theorem haarProjection_expectedDiameter_set :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Set (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        Bornology.IsBounded T →
        c * haarProjectionScale (m := m) T ≤
            haarProjectionExpectedDiameter (m := m) T ∧
          haarProjectionExpectedDiameter (m := m) T ≤
            C * haarProjectionScale (m := m) T := by
  obtain ⟨c, C, hc, hC, hbase⟩ :=
    haarProjection_expectedDiameter_envelope
  refine ⟨c, C, hc, hC, ?_⟩
  intro m n hn hm hmn T hT hTb
  have hmain := hbase hn hm hmn T
  rw [haarProjectionScaleEnvelope_eq_actualScale hn T hT hTb,
    haarProjectionExpectedDiameterEnvelope_eq_actual hmn T hT hTb]
    at hmain
  have hwidth : 0 ≤ boundedSetSphericalWidth T :=
    boundedSetSphericalWidth_nonneg hn T hT hTb
  have hscale : 0 ≤ haarProjectionScale (m := m) T := by
    exact add_nonneg hwidth
      (mul_nonneg (Real.sqrt_nonneg _) Metric.diam_nonneg)
  have hexpect : 0 ≤ haarProjectionExpectedDiameter (m := m) T := by
    apply integral_nonneg
    intro P
    exact Metric.diam_nonneg
  constructor
  · have h := hmain.1
    rw [← ENNReal.ofReal_mul hc.le] at h
    exact (ENNReal.ofReal_le_ofReal_iff hexpect).mp (by
      simpa [haarProjectionScale, haarProjectionDiameterTerm,
        haarProjectionExpectedDiameter] using h)
  · have h := hmain.2
    rw [← ENNReal.ofReal_mul hC.le] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le hscale)).mp (by
      simpa [haarProjectionScale, haarProjectionDiameterTerm,
        haarProjectionExpectedDiameter] using h)

/-- The spherical-width contribution is bounded by the full Haar-projection scale envelope.

**Lean implementation helper.** -/
theorem sphericalWidthEnvelope_le_haarProjectionScaleEnvelope {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    sphericalWidthEnvelope T ≤
      haarProjectionScaleEnvelope (m := m) T := by
  unfold sphericalWidthEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  calc
    ENNReal.ofReal (HDP.Chapter7.sphericalWidth F) ≤
        ENNReal.ofReal (HDP.Chapter7.sphericalWidth F +
          Real.sqrt ((m : ℝ) / n) *
            HDP.Chapter7.finiteEuclideanDiameter F) := by
      apply ENNReal.ofReal_le_ofReal
      exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _)
        (HDP.Chapter7.finiteEuclideanDiameter_nonneg F))
    _ ≤ haarProjectionScaleEnvelope (m := m) T := by
      unfold haarProjectionScaleEnvelope
      exact le_iSup_of_le F
        (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))

/-- The projected-diameter contribution is bounded by the full Haar-projection scale envelope.

**Lean implementation helper.** -/
theorem haarProjectionDiameterTermEnvelope_le_scale {m n : ℕ}
    (hn : 0 < n) (T : Set (EuclideanSpace ℝ (Fin n))) :
    haarProjectionDiameterTermEnvelope (m := m) T ≤
      haarProjectionScaleEnvelope (m := m) T := by
  unfold haarProjectionDiameterTermEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  calc
    ENNReal.ofReal (Real.sqrt ((m : ℝ) / n) *
        HDP.Chapter7.finiteEuclideanDiameter F) ≤
      ENNReal.ofReal (HDP.Chapter7.sphericalWidth F +
        Real.sqrt ((m : ℝ) / n) *
          HDP.Chapter7.finiteEuclideanDiameter F) := by
        apply ENNReal.ofReal_le_ofReal
        exact le_add_of_nonneg_left
          (HDP.Chapter7.sphericalWidth_nonneg F hF hn)
    _ ≤ haarProjectionScaleEnvelope (m := m) T := by
      unfold haarProjectionScaleEnvelope
      exact le_iSup_of_le F
        (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl))

/-- The Haar-projection scale is bounded by the sum of its width and diameter contributions.

**Lean implementation helper.** -/
theorem haarProjectionScaleEnvelope_le_add {m n : ℕ} (hn : 0 < n)
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    haarProjectionScaleEnvelope (m := m) T ≤
      sphericalWidthEnvelope T +
        haarProjectionDiameterTermEnvelope (m := m) T := by
  unfold haarProjectionScaleEnvelope
  apply iSup_le
  intro F
  apply iSup_le
  intro hFT
  apply iSup_le
  intro hF
  have hw0 : 0 ≤ HDP.Chapter7.sphericalWidth F :=
    HDP.Chapter7.sphericalWidth_nonneg F hF hn
  have hd0 : 0 ≤ Real.sqrt ((m : ℝ) / n) *
      HDP.Chapter7.finiteEuclideanDiameter F :=
    mul_nonneg (Real.sqrt_nonneg _)
      (HDP.Chapter7.finiteEuclideanDiameter_nonneg F)
  rw [ENNReal.ofReal_add hw0 hd0]
  exact add_le_add
    (ofReal_sphericalWidth_le_sphericalWidthEnvelope F hFT hF)
    (by
      unfold haarProjectionDiameterTermEnvelope
      exact le_iSup_of_le F
        (le_iSup_of_le hFT (le_iSup_of_le hF le_rfl)))

/-- Random projections exhibit high- and low-dimensional width/diameter phases. The
expectation is the genuine expectation of the diameter of the actual Haar
image of `T`.

**Book Remark 9.7.5.** -/
theorem remark_9_7_5_highDimensionalPhase_set :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Set (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        Bornology.IsBounded T →
        boundedSetSphericalWidth T ≤
          haarProjectionDiameterTerm (m := m) T →
        c * haarProjectionDiameterTerm (m := m) T ≤
            haarProjectionExpectedDiameter (m := m) T ∧
          haarProjectionExpectedDiameter (m := m) T ≤
            C * haarProjectionDiameterTerm (m := m) T := by
  obtain ⟨c, C, hc, hC, hbase⟩ :=
    haarProjection_expectedDiameter_set
  refine ⟨c, 2 * C, hc, mul_pos (by norm_num) hC, ?_⟩
  intro m n hn hm hmn T hT hTb hregime
  have hwidth : 0 ≤ boundedSetSphericalWidth T :=
    boundedSetSphericalWidth_nonneg hn T hT hTb
  have hterm : 0 ≤ haarProjectionDiameterTerm (m := m) T :=
    mul_nonneg (Real.sqrt_nonneg _) Metric.diam_nonneg
  have hmain := hbase hn hm hmn T hT hTb
  constructor
  · calc
      c * haarProjectionDiameterTerm (m := m) T ≤
          c * haarProjectionScale (m := m) T := by
        unfold haarProjectionScale
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hwidth) hc.le
      _ ≤ haarProjectionExpectedDiameter (m := m) T := hmain.1
  · calc
      haarProjectionExpectedDiameter (m := m) T ≤
          C * haarProjectionScale (m := m) T := hmain.2
      _ ≤ (2 * C) * haarProjectionDiameterTerm (m := m) T := by
        unfold haarProjectionScale
        nlinarith

/-- Random projections exhibit high- and low-dimensional width/diameter phases.

**Book Remark 9.7.5.** -/
theorem remark_9_7_5_lowDimensionalPhase_set :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Set (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        Bornology.IsBounded T →
        haarProjectionDiameterTerm (m := m) T ≤
          boundedSetSphericalWidth T →
        c * boundedSetSphericalWidth T ≤
            haarProjectionExpectedDiameter (m := m) T ∧
          haarProjectionExpectedDiameter (m := m) T ≤
            C * boundedSetSphericalWidth T := by
  obtain ⟨c, C, hc, hC, hbase⟩ :=
    haarProjection_expectedDiameter_set
  refine ⟨c, 2 * C, hc, mul_pos (by norm_num) hC, ?_⟩
  intro m n hn hm hmn T hT hTb hregime
  have hwidth : 0 ≤ boundedSetSphericalWidth T :=
    boundedSetSphericalWidth_nonneg hn T hT hTb
  have hterm : 0 ≤ haarProjectionDiameterTerm (m := m) T :=
    mul_nonneg (Real.sqrt_nonneg _) Metric.diam_nonneg
  have hmain := hbase hn hm hmn T hT hTb
  constructor
  · calc
      c * boundedSetSphericalWidth T ≤
          c * haarProjectionScale (m := m) T := by
        unfold haarProjectionScale
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hterm) hc.le
      _ ≤ haarProjectionExpectedDiameter (m := m) T := hmain.1
  · calc
      haarProjectionExpectedDiameter (m := m) T ≤
          C * haarProjectionScale (m := m) T := hmain.2
      _ ≤ (2 * C) * boundedSetSphericalWidth T := by
        unfold haarProjectionScale
        nlinarith

/-- When the classical
`sqrt (m/n) * diam(T)` term dominates spherical width, the expected diameter
of a Haar projection is comparable to that term with absolute constants.

**Book Remark 9.7.5.** -/
theorem remark_9_7_5_highDimensionalPhase :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        HDP.Chapter7.sphericalWidth T ≤
          Real.sqrt ((m : ℝ) / n) *
            HDP.Chapter7.finiteEuclideanDiameter T →
        c * (Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter T) ≤
            (∫ P, HDP.Chapter7.grassmannProjectedDiameter P T
              ∂HDP.Chapter5.grassmannHaarMeasure n m) ∧
          (∫ P, HDP.Chapter7.grassmannProjectedDiameter P T
              ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
            C * (Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter T) := by
  obtain ⟨c, C, hc, hC, hprojection⟩ :=
    HDP.Chapter7.randomProjection_expectedDiameter
  refine ⟨c, 2 * C, hc, mul_pos (by norm_num) hC, ?_⟩
  intro m n hn hm hmn T hT hregime
  have hwidth : 0 ≤ HDP.Chapter7.sphericalWidth T :=
    HDP.Chapter7.sphericalWidth_nonneg T hT hn
  have hterm : 0 ≤ Real.sqrt ((m : ℝ) / n) *
      HDP.Chapter7.finiteEuclideanDiameter T :=
    mul_nonneg (Real.sqrt_nonneg _)
      (HDP.Chapter7.finiteEuclideanDiameter_nonneg T)
  have hbase := hprojection hn hm hmn T hT
  constructor
  · calc
      c * (Real.sqrt ((m : ℝ) / n) *
          HDP.Chapter7.finiteEuclideanDiameter T) ≤
          c * (HDP.Chapter7.sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter T) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hwidth) hc.le
      _ ≤ _ := hbase.1
  · calc
      (∫ P, HDP.Chapter7.grassmannProjectedDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
          C * (HDP.Chapter7.sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter T) := hbase.2
      _ ≤ (2 * C) * (Real.sqrt ((m : ℝ) / n) *
            HDP.Chapter7.finiteEuclideanDiameter T) := by
        nlinarith

/-- Once the spherical-width
term dominates, the expected diameter of a Haar projection is comparable to
the spherical width and therefore no longer shrinks with `m`.

**Book Remark 9.7.5.** -/
theorem remark_9_7_5_lowDimensionalPhase :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        Real.sqrt ((m : ℝ) / n) *
            HDP.Chapter7.finiteEuclideanDiameter T ≤
          HDP.Chapter7.sphericalWidth T →
        c * HDP.Chapter7.sphericalWidth T ≤
            (∫ P, HDP.Chapter7.grassmannProjectedDiameter P T
              ∂HDP.Chapter5.grassmannHaarMeasure n m) ∧
          (∫ P, HDP.Chapter7.grassmannProjectedDiameter P T
              ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
            C * HDP.Chapter7.sphericalWidth T := by
  obtain ⟨c, C, hc, hC, hprojection⟩ :=
    HDP.Chapter7.randomProjection_expectedDiameter
  refine ⟨c, 2 * C, hc, mul_pos (by norm_num) hC, ?_⟩
  intro m n hn hm hmn T hT hregime
  have hwidth : 0 ≤ HDP.Chapter7.sphericalWidth T :=
    HDP.Chapter7.sphericalWidth_nonneg T hT hn
  have hterm : 0 ≤ Real.sqrt ((m : ℝ) / n) *
      HDP.Chapter7.finiteEuclideanDiameter T :=
    mul_nonneg (Real.sqrt_nonneg _)
      (HDP.Chapter7.finiteEuclideanDiameter_nonneg T)
  have hbase := hprojection hn hm hmn T hT
  constructor
  · calc
      c * HDP.Chapter7.sphericalWidth T ≤
          c * (HDP.Chapter7.sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter T) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hterm) hc.le
      _ ≤ _ := hbase.1
  · calc
      (∫ P, HDP.Chapter7.grassmannProjectedDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
          C * (HDP.Chapter7.sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) *
              HDP.Chapter7.finiteEuclideanDiameter T) := hbase.2
      _ ≤ (2 * C) * HDP.Chapter7.sphericalWidth T := by
        nlinarith

end

end HDP.Chapter9

end Source_18_DvoretzkyMilman
