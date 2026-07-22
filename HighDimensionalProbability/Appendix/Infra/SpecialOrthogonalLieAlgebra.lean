import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence

/-!
# The Casimir computation for the orthogonal Lie algebra

This file formalizes the finite matrix identity behind the Ricci-curvature
computation for `SO(n)` with its Frobenius bi-invariant metric.  If

`Bᵢⱼ = Eᵢⱼ - Eⱼᵢ`,

then, for every skew-symmetric matrix `X`,

`∑ i, j, ‖[X, Bᵢⱼ]‖_F² = 4 (n - 2) ‖X‖_F²`.

The sum here is over ordered pairs and uses the unnormalized generators.
Passing to one representative of each unordered pair and dividing each
generator by `√2` gives the standard orthonormal-basis identity
`∑_{i<j} ‖[X,Eᵢⱼ]‖_F² = (n-2) ‖X‖_F²`.

This is the algebraic part of the usual proof that the Ricci tensor of
`SO(n)` is bounded below by a constant multiple of `n-2`.  The analytic
Bakry--Émery/log-Sobolev bridge is separate.
-/

open Matrix
open scoped BigOperators

namespace HDP.Appendix.SpecialOrthogonal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The unnormalized elementary skew-symmetric generator
`Eᵢⱼ - Eⱼᵢ`. -/
def skewGenerator (i j : α) : Matrix α α ℝ :=
  Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ)

/-- Matrix commutator. -/
def commutator (X Y : Matrix α α ℝ) : Matrix α α ℝ :=
  X * Y - Y * X

private lemma skewGenerator_transpose (i j : α) :
    (skewGenerator i j).transpose = -skewGenerator i j := by
  simp [skewGenerator, Matrix.transpose_sub, Matrix.transpose_single]

private lemma commutator_transpose_of_skew
    (X Y : Matrix α α ℝ) (hX : X.transpose = -X)
    (hY : Y.transpose = -Y) :
    (commutator X Y).transpose = -commutator X Y := by
  simp [commutator, Matrix.transpose_sub, Matrix.transpose_mul, hX, hY]

private lemma commutator_sq (X Y : Matrix α α ℝ) :
    commutator X Y * commutator X Y =
      X * Y * X * Y - X * (Y * Y) * X -
        Y * (X * X) * Y + Y * X * Y * X := by
  simp only [commutator]
  noncomm_ring

private lemma trace_commutator_sq (X Y : Matrix α α ℝ) :
    (commutator X Y * commutator X Y).trace =
      2 * (Y * X * Y * X).trace -
        2 * (Y * Y * X * X).trace := by
  rw [commutator_sq, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_sub]
  have h₁ : (X * Y * X * Y).trace = (Y * X * Y * X).trace := by
    calc
      (X * Y * X * Y).trace = (X * (Y * X * Y)).trace := by
        congr 1
        noncomm_ring
      _ = ((Y * X * Y) * X).trace := Matrix.trace_mul_comm _ _
      _ = (Y * X * Y * X).trace := by
        congr 1
  have h₂ : (X * (Y * Y) * X).trace = (Y * Y * X * X).trace := by
    calc
      (X * (Y * Y) * X).trace = (X * (Y * Y * X)).trace := by
        congr 1
        noncomm_ring
      _ = ((Y * Y * X) * X).trace := Matrix.trace_mul_comm _ _
      _ = (Y * Y * X * X).trace := rfl
  have h₃ : (Y * (X * X) * Y).trace = (Y * Y * X * X).trace := by
    calc
      (Y * (X * X) * Y).trace = (Y * (X * X * Y)).trace := by
        congr 1
        noncomm_ring
      _ = ((X * X * Y) * Y).trace := Matrix.trace_mul_comm _ _
      _ = ((X * X) * (Y * Y)).trace := by
        congr 1
        noncomm_ring
      _ = ((Y * Y) * (X * X)).trace := Matrix.trace_mul_comm _ _
      _ = (Y * Y * X * X).trace := by
        congr 1
        noncomm_ring
  rw [h₁, h₂, h₃]
  ring

private lemma single_mul_apply (X : Matrix α α ℝ)
    (i j a b : α) :
    (Matrix.single i j (1 : ℝ) * X) a b =
      if a = i then X j b else 0 := by
  by_cases h : a = i
  · subst a
    simp [Matrix.mul_apply, Matrix.single]
  · simp [Matrix.mul_apply, Matrix.single, h, Ne.symm h]

private lemma mul_single_apply (X : Matrix α α ℝ)
    (i j a b : α) :
    (X * Matrix.single i j (1 : ℝ)) a b =
      if b = j then X a i else 0 := by
  by_cases h : b = j
  · subst b
    simp [Matrix.mul_apply, Matrix.single]
  · simp [Matrix.mul_apply, Matrix.single, h, Ne.symm h]

private lemma skewGenerator_mul_mul_apply
    (X : Matrix α α ℝ) (i j a b : α) :
    (skewGenerator i j * X * skewGenerator i j) a b =
      (if b = j then if a = i then X j i else 0 else 0)
      - (if b = j then if a = j then X i i else 0 else 0)
      - (if b = i then if a = i then X j j else 0 else 0)
      + (if b = i then if a = j then X i j else 0 else 0) := by
  simp only [skewGenerator, sub_mul, mul_sub, Matrix.sub_apply]
  simp [mul_single_apply, single_mul_apply]
  ring

private lemma sum_skewGenerator_mul_mul (X : Matrix α α ℝ) :
    ∑ i, ∑ j, skewGenerator i j * X * skewGenerator i j =
      2 • X.transpose -
        (2 * Matrix.trace X) • (1 : Matrix α α ℝ) := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.transpose_apply, Matrix.one_apply]
  simp_rw [skewGenerator_mul_mul_apply]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hab : a = b
  · subst b
    simp [Matrix.trace, Finset.mul_sum]
    have hsum : (∑ i : α, 2 * X i i) =
        2 * ∑ i : α, X i i := by
      rw [Finset.mul_sum]
    rw [hsum]
    ring
  · simp [hab, Matrix.trace, Finset.mul_sum]
    ring

private lemma sum_skewGenerator_sq :
    ∑ i : α, ∑ j : α, skewGenerator i j * skewGenerator i j =
      2 • (1 : Matrix α α ℝ) -
        (2 * (Fintype.card α : ℝ)) •
          (1 : Matrix α α ℝ) := by
  rw [← show
      ∑ i : α, ∑ j : α,
          skewGenerator i j * (1 : Matrix α α ℝ) *
            skewGenerator i j =
        ∑ i : α, ∑ j : α,
          skewGenerator i j * skewGenerator i j by simp]
  rw [sum_skewGenerator_mul_mul]
  rw [Matrix.transpose_one, Matrix.trace_one]

private lemma sum_trace_generator_sq_mul_sq (X : Matrix α α ℝ) :
    ∑ i : α, ∑ j : α,
        (skewGenerator i j * skewGenerator i j * X * X).trace =
      ((2 • (1 : Matrix α α ℝ) -
          (2 * (Fintype.card α : ℝ)) •
            (1 : Matrix α α ℝ)) * X * X).trace := by
  calc
    ∑ i : α, ∑ j : α,
        (skewGenerator i j * skewGenerator i j * X * X).trace =
        (∑ i : α, ∑ j : α,
          skewGenerator i j * skewGenerator i j * X * X).trace := by
            rw [Matrix.trace_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Matrix.trace_sum]
    _ = ((∑ i : α, ∑ j : α,
        skewGenerator i j * skewGenerator i j) * X * X).trace := by
      congr 1
      rw [Matrix.sum_mul, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.sum_mul, Matrix.sum_mul]
    _ = _ := by rw [sum_skewGenerator_sq]

private lemma sum_trace_generator_mul (X : Matrix α α ℝ)
    (hskew : X.transpose = -X) :
    ∑ i : α, ∑ j : α,
        (skewGenerator i j * X * skewGenerator i j * X).trace =
      (((-2 : ℝ) • X) * X).trace := by
  calc
    ∑ i : α, ∑ j : α,
        (skewGenerator i j * X * skewGenerator i j * X).trace =
        (∑ i : α, ∑ j : α,
          skewGenerator i j * X * skewGenerator i j * X).trace := by
            rw [Matrix.trace_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Matrix.trace_sum]
    _ = ((∑ i : α, ∑ j : α,
        skewGenerator i j * X * skewGenerator i j) * X).trace := by
      congr 1
      rw [Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.sum_mul]
    _ = _ := by
      rw [show ∑ i : α, ∑ j : α,
          skewGenerator i j * X * skewGenerator i j =
          (-2 : ℝ) • X by
        rw [sum_skewGenerator_mul_mul]
        have htrace : Matrix.trace X = 0 := by
          have hdiag (i : α) : X i i = 0 := by
            have h := congrFun (congrFun hskew i) i
            simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
            linarith
          simp [Matrix.trace, hdiag]
        rw [htrace]
        simp [hskew]
        have htwo : (2 : Matrix α α ℝ) = 1 + 1 := by
          norm_num
        rw [htwo, add_mul, one_mul]
        module]

private lemma frobenius_sq_eq_neg_trace_mul_self
    (X : Matrix α α ℝ) (hskew : X.transpose = -X) :
    HDP.matrixFrobeniusNorm X ^ 2 = -(X * X).trace := by
  have hsym (a b : α) : X b a = -X a b := by
    have h := congrFun (congrFun hskew a) b
    simpa using h
  rw [HDP.matrixFrobeniusNorm_sq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [show -(∑ i, ∑ j, X i j * X j i) =
      ∑ i, ∑ j, X i j ^ 2 by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [hsym i j]
    ring]

/-- The exact ordered-generator Casimir identity for skew-symmetric matrices.

For `α = Fin n`, the coefficient is `4 * (n - 2)`. -/
theorem skew_casimir_identity
    (X : Matrix α α ℝ) (hskew : X.transpose = -X) :
    ∑ i : α, ∑ j : α,
        HDP.matrixFrobeniusNorm
          (commutator X (skewGenerator i j)) ^ 2 =
      4 * ((Fintype.card α : ℝ) - 2) *
        HDP.matrixFrobeniusNorm X ^ 2 := by
  have hpoint (i j : α) :
      HDP.matrixFrobeniusNorm
          (commutator X (skewGenerator i j)) ^ 2 =
        -(commutator X (skewGenerator i j) *
            commutator X (skewGenerator i j)).trace :=
    frobenius_sq_eq_neg_trace_mul_self _
      (commutator_transpose_of_skew X (skewGenerator i j)
        hskew (skewGenerator_transpose i j))
  simp_rw [hpoint, trace_commutator_sq]
  have hcollect :
      (∑ i : α, ∑ j : α,
          -(2 * (skewGenerator i j * X *
              skewGenerator i j * X).trace -
            2 * (skewGenerator i j * skewGenerator i j *
              X * X).trace)) =
        2 * (∑ i : α, ∑ j : α,
          (skewGenerator i j * skewGenerator i j * X * X).trace) -
        2 * (∑ i : α, ∑ j : α,
          (skewGenerator i j * X * skewGenerator i j * X).trace) := by
    simp only [neg_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hcollect, sum_trace_generator_sq_mul_sq,
    sum_trace_generator_mul X hskew]
  have htraceNorm :
      -(X * X).trace = HDP.matrixFrobeniusNorm X ^ 2 :=
    (frobenius_sq_eq_neg_trace_mul_self X hskew).symm
  simp only [sub_mul, smul_mul, one_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  rw [← htraceNorm]
  ring

/-- `Fin n` specialization of `skew_casimir_identity`. -/
theorem skew_casimir_identity_fin {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (hskew : X.transpose = -X) :
    ∑ i : Fin n, ∑ j : Fin n,
        HDP.matrixFrobeniusNorm
          (commutator X (skewGenerator i j)) ^ 2 =
      4 * ((n : ℝ) - 2) * HDP.matrixFrobeniusNorm X ^ 2 := by
  simpa using skew_casimir_identity X hskew

/-- The Ricci quadratic form obtained from the bi-invariant Frobenius metric,
written using the ordered, unnormalized generators.

The factor `1 / 16` simultaneously accounts for passing from ordered pairs
to `i < j`, normalizing `Eᵢⱼ - Eⱼᵢ` by `√2`, and the standard
`Ric(X,X) = 1 / 4 * ∑ ‖[X,eₐ]‖²` formula for a bi-invariant metric. -/
noncomputable def ricciQuadraticForm {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 16 : ℝ) *
    ∑ i : Fin n, ∑ j : Fin n,
      HDP.matrixFrobeniusNorm
        (commutator X (skewGenerator i j)) ^ 2

/-- Exact Ricci tensor computation for the Frobenius bi-invariant metric on
`SO(n)`, expressed at the identity on a skew-symmetric tangent matrix. -/
theorem ricciQuadraticForm_eq {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (hskew : X.transpose = -X) :
    ricciQuadraticForm X =
      (((n : ℝ) - 2) / 4) * HDP.matrixFrobeniusNorm X ^ 2 := by
  rw [ricciQuadraticForm, skew_casimir_identity_fin X hskew]
  ring

end HDP.Appendix.SpecialOrthogonal
