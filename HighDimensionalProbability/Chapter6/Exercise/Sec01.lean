import HighDimensionalProbability.Chapter6_QuadraticFormsSymmetrizationContraction

/-!
# Chapter 6 exercises attached to Section 6.1

Only the non-load-bearing decoupling variants live here.  Exercise 6.1 proves
Remark 6.1.2 and therefore belongs exclusively to the Chapter 6 core.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace unitInterval

noncomputable section

namespace HDP.Chapter6.Exercise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The off-diagonal scalar quadratic chaos used in Exercises 6.2 and 6.3.

**Lean implementation helper.** -/
def offDiagonalChaos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, A i j * X i ω * X j ω

/-- The fully decoupled scalar chaos.

**Lean implementation helper.** -/
def decoupledChaos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, A i j * X i ω * X' j ω

/-- The hypotheses saying that `X'` is an independent coordinatewise copy of the independent
family `X`.

**Lean implementation helper.** -/
def IsIndependentScalarCopy {n : ℕ} (X X' : Fin n → Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  iIndepFun X μ ∧ iIndepFun X' μ ∧
    IndepFun (fun ω i => X i ω) (fun ω i => X' i ω) μ ∧
    (∀ i, IdentDistrib (X' i) (X i) μ μ)

/-- The authoritative potentially-infinite `L^p` interface is `eLpNorm`; `p ≠ ⊤` records the
source's range `p < ∞`.

**Book Exercise 6.2(a).** -/
theorem exercise_6_2a {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → ℝ) (_hcopy : IsIndependentScalarCopy X X' μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {p : ℝ≥0∞}
    (_hp : 1 ≤ p) (_hpTop : p ≠ ⊤) :
    eLpNorm (offDiagonalChaos A X) p μ ≤
      4 * eLpNorm (decoupledChaos A X X') p μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.2(a).
  sorry

/-- Decoupling in the scalar `ψ₂` norm.

**Book Exercise 6.2(b).** -/
theorem exercise_6_2b {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → ℝ) (_hcopy : IsIndependentScalarCopy X X' μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    HDP.psi2Norm (offDiagonalChaos A X) μ ≤
      4 * HDP.psi2Norm (decoupledChaos A X X') μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.2(b).
  sorry

/-- The off-diagonal vector-valued chaos from the corresponding exercise.

**Lean implementation helper.** -/
def offDiagonalVectorChaos {n : ℕ} {V : Type*} [AddCommMonoid V]
    [Module ℝ V] (v : Fin n → Fin n → V) (X : Fin n → Ω → ℝ)
    (ω : Ω) : V :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (X i ω * X j ω) • v i j

/-- The decoupled vector-valued chaos from the corresponding exercise.

**Lean implementation helper.** -/
def decoupledVectorChaos {n : ℕ} {V : Type*} [AddCommMonoid V]
    [Module ℝ V] (v : Fin n → Fin n → V) (X X' : Fin n → Ω → ℝ)
    (ω : Ω) : V :=
  ∑ i, ∑ j, (X i ω * X' j ω) • v i j

/-- Extends quadratic-chaos decoupling to convex functions of vector-valued off-diagonal forms.

**Book Exercise 6.3(a).** -/
theorem exercise_6_3a {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v : Fin n → Fin n → V)
    (X X' : Fin n → Ω → ℝ) (_hcopy : IsIndependentScalarCopy X X' μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (F : V → ℝ)
    (_hF : ConvexOn ℝ Set.univ F)
    (_hintOff : Integrable (fun ω => F (offDiagonalVectorChaos v X ω)) μ)
    (_hintDec : Integrable (fun ω => F (4 • decoupledVectorChaos v X X' ω)) μ) :
    (∫ ω, F (offDiagonalVectorChaos v X ω) ∂μ) ≤
      ∫ ω, F (4 • decoupledVectorChaos v X X' ω) ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.3(a).
  sorry

/-- The off-diagonal inner-product chaos from the corresponding exercise.

**Lean implementation helper.** -/
def offDiagonalInnerChaos {n N : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin N)) (ω : Ω) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    A i j * inner ℝ (X i ω) (X j ω)

/-- Its fully decoupled counterpart.

**Lean implementation helper.** -/
def decoupledInnerChaos {n N : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → EuclideanSpace ℝ (Fin N)) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, A i j * inner ℝ (X i ω) (X' j ω)

/-- The independent-copy hypotheses for finite-dimensional random vectors.

**Lean implementation helper.** -/
def IsIndependentVectorCopy {n N : ℕ}
    (X X' : Fin n → Ω → EuclideanSpace ℝ (Fin N)) (μ : Measure Ω) : Prop :=
  iIndepFun X μ ∧ iIndepFun X' μ ∧
    IndepFun (fun ω i => X i ω) (fun ω i => X' i ω) μ ∧
    (∀ i, IdentDistrib (X' i) (X i) μ μ)

/-- Vector decoupling for inner-product quadratic forms.

**Book Exercise 6.3(b).** -/
theorem exercise_6_3b {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → EuclideanSpace ℝ (Fin N))
    (_hcopy : IsIndependentVectorCopy X X' μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (F : ℝ → ℝ) (_hF : ConvexOn ℝ Set.univ F)
    (_hintOff : Integrable (fun ω => F (offDiagonalInnerChaos A X ω)) μ)
    (_hintDec : Integrable (fun ω => F (4 * decoupledInnerChaos A X X' ω)) μ) :
    (∫ ω, F (offDiagonalInnerChaos A X ω) ∂μ) ≤
      ∫ ω, F (4 * decoupledInnerChaos A X X' ω) ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.3(b).
  sorry

/-- The matrix-valued off-diagonal chaos from the corresponding exercise.

**Lean implementation helper.** -/
def offDiagonalOuterChaos {n N : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin N)) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    A i j • Matrix.of (fun a b => X i ω a * X j ω b)

/-- The decoupled matrix-valued chaos from the corresponding exercise.

**Lean implementation helper.** -/
def decoupledOuterChaos {n N : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → EuclideanSpace ℝ (Fin N)) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  ∑ i, ∑ j,
    A i j • Matrix.of (fun a b => X i ω a * X' j ω b)

/-- Vector decoupling for matrix outer products.

**Book Exercise 6.3(c).** -/
theorem exercise_6_3c {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X X' : Fin n → Ω → EuclideanSpace ℝ (Fin N))
    (_hcopy : IsIndependentVectorCopy X X' μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (F : Matrix (Fin N) (Fin N) ℝ → ℝ)
    (_hF : ConvexOn ℝ Set.univ F)
    (_hintOff : Integrable (fun ω => F (offDiagonalOuterChaos A X ω)) μ)
    (_hintDec : Integrable (fun ω => F (4 • decoupledOuterChaos A X X' ω)) μ) :
    (∫ ω, F (offDiagonalOuterChaos A X ω) ∂μ) ≤
      ∫ ω, F (4 • decoupledOuterChaos A X X' ω) ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.3(c).
  sorry

/-- A fixed-ambient realization of the random submatrix `A_{J × K}`.

**Lean implementation helper.** -/
def maskedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (δ η : Fin n → Ω → ℝ) (ω : Ω) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => δ i ω * A i j * η j ω

/-- Decoupling the operator norm of a random submatrix, using coordinate masks so that all
submatrices have one fixed ambient type.

**Book Exercise 6.4.** -/
theorem exercise_6_4 [IsProbabilityMeasure μ] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (_hdiag : ∀ i, A i i = 0)
    {p : I} (_hp0 : 0 < (p : ℝ)) (_hp1 : (p : ℝ) < 1)
    (δ δ' : Fin n → Ω → ℝ)
    (_hδ : ∀ i, HDP.IsBernoulli (δ i) p μ)
    (_hδ' : ∀ i, HDP.IsBernoulli (δ' i) p μ)
    (_hind : iIndepFun δ μ ∧ iIndepFun δ' μ ∧
      IndepFun (fun ω i => δ i ω) (fun ω i => δ' i ω) μ)
    (_hintSame : Integrable (fun ω => HDP.matrixOpNorm (maskedMatrix A δ δ ω)) μ)
    (_hintDec : Integrable (fun ω => HDP.matrixOpNorm (maskedMatrix A δ δ' ω)) μ) :
    (∫ ω, HDP.matrixOpNorm (maskedMatrix A δ δ ω) ∂μ) ≤
      4 * ∫ ω, HDP.matrixOpNorm (maskedMatrix A δ δ' ω) ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.4.
  sorry

end HDP.Chapter6.Exercise
