/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter9.Main

/-!
# Book Chapter 9 exercises attached to Section 9.1

Exercises 9.1--9.3 are used by the Chapter 9 main line and therefore occur
only in core.  This leaf contains the four non-load-bearing proof atoms from
Exercises 9.4--9.6.  The arbitrary-set suprema below carry explicit
boundedness, measurability, and integrability hypotheses whenever they are
used as real-valued random variables.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology
  Matrix.Norms.L2Operator

namespace HDP.Chapter9.Exercise

noncomputable section

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Action of a real matrix on Euclidean coordinate space.

**Lean implementation helper.** -/
def matrixApply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Euc n) : Euc m :=
  WithLp.toLp 2 (A.mulVec x)

/-- Image of a Euclidean set under a real matrix.

**Lean implementation helper.** -/
def matrixImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Set (Euc n)) : Set (Euc m) :=
  matrixApply A '' T

/-- Radius of an arbitrary Euclidean set.

**Lean implementation helper.** -/
def setRadius {n : ℕ} (T : Set (Euc n)) : ℝ :=
  sSup (norm '' T)

/-- Diameter of an arbitrary Euclidean set.

**Lean implementation helper.** -/
def setDiameter {n : ℕ} (T : Set (Euc n)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ T, ∃ y ∈ T, r = ‖x - y‖}

/-- Gaussian complexity `E sup_{x∈T} |⟨g,x⟩|` of an arbitrary set.

**Lean implementation helper.** -/
def setGaussianComplexity {n : ℕ} (T : Set (Euc n)) : ℝ :=
  ∫ g, sSup ((fun x : Euc n => |inner ℝ g x|) '' T)
    ∂stdGaussian (Euc n)

/-- Gaussian width of an arbitrary Euclidean set, using Chapter 8's safe
finite-subfamily envelope.

**Lean implementation helper.** -/
def setGaussianWidth {n : ℕ} (T : Set (Euc n)) : ℝ :=
  HDP.Chapter8.euclideanSetGaussianWidth T

/-- Spherical width obtained from the Gaussian polar decomposition.

**Lean implementation helper.** -/
def setSphericalWidth {n : ℕ} (T : Set (Euc n)) : ℝ :=
  setGaussianWidth T / HDP.Chapter7.gaussianRadialMean n

/-- Supremum of the norm deviation of a matrix on a set.

**Lean implementation helper.** -/
def setNormDeviation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Set (Euc n)) (target : Euc n → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ T, r = |‖matrixApply A x‖ - target x|}

/-- The `L²` metric of a class of random functions.

**Lean implementation helper.** -/
def functionL2Metric {α Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → α) (μ : Measure Ω) (f g : α → ℝ) : ℝ :=
  Real.sqrt (∫ ω, (f (X ω) - g (X ω)) ^ 2 ∂μ)

/-- An admissible sequence for the arbitrary-set `γ₂` functional. -/
structure SetAdmissibleChain (T : Type*) where
  level : ℕ → Set T
  level_finite : ∀ k, (level k).Finite
  level_nonempty : ∀ k, (level k).Nonempty
  level_zero_card : (level 0).ncard = 1
  level_card_le : ∀ k, (level k).ncard ≤ 2 ^ (2 ^ k)

/-- Extended `γ₂` functional for an arbitrary set and a real metric.

**Lean implementation helper.** -/
def setGammaTwoENN {T : Type*} (S : Set T) (d : T → T → ℝ) : ℝ≥0∞ :=
  ⨅ A : SetAdmissibleChain S,
    ⨆ t : S, ∑' k : ℕ,
      ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ k)) *
        (⨅ s : A.level k, ENNReal.ofReal (d t.1 s.1))

/-- Safe real wrapper of the arbitrary-set `γ₂` functional.

**Lean implementation helper.** -/
def setGammaTwo {T : Type*} (S : Set T) (d : T → T → ℝ) : ℝ :=
  (setGammaTwoENN S d).toReal

/-- Pointwise deviation of the empirical `L²` mean from the population
`L²` mean over a function class.

**Lean implementation helper.** -/
def quadraticEmpiricalDeviation {α Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ} (F : Set (α → ℝ)) (X : Fin m → Ω → α)
    (X₀ : Ω → α) (μ : Measure Ω) (ω : Ω) : ℝ :=
  sSup {r : ℝ | ∃ f ∈ F,
    r = |Real.sqrt (((m : ℝ)⁻¹ * ∑ i, (f (X i ω)) ^ 2)) -
      Real.sqrt (∫ ξ, (f (X₀ ξ)) ^ 2 ∂μ)|}

/-- **Exercise 9.4 (anisotropic matrix deviation).** The covariance is
represented by a factorization `Σ = S Sᵀ`, so its quadratic form is
`x ↦ ‖Sᵀx‖²`. This formulation also handles singular covariances without
introducing an inverse.

**Book Exercise 9.4.** -/
theorem exercise_9_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {hm : 0 < m} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (S : Matrix (Fin n) (Fin n) ℝ) (T : Set (Euc n)) (K : ℝ),
        T.Nonempty → Bornology.IsBounded T → 0 ≤ K →
        A.AEMeasurableEntries μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        (∀ i, HDP.secondMomentMatrix (HDP.randomMatrixRow A i) μ = S * Sᵀ) →
        (∀ i x, HDP.psi2Norm
          (fun ω => inner ℝ (HDP.randomMatrixRow A i ω) x) μ ≤
            K * Real.sqrt (∫ ω,
              (inner ℝ (HDP.randomMatrixRow A i ω) x) ^ 2 ∂μ)) →
        (∀ ω, BddAbove {r : ℝ | ∃ x ∈ T,
          r = |‖matrixApply (A ω) x‖ -
            Real.sqrt m * ‖matrixApply S.transpose x‖|}) →
        Measurable (fun ω => setNormDeviation (A ω) T
          (fun x => Real.sqrt m * ‖matrixApply S.transpose x‖)) →
        Integrable (fun ω => setNormDeviation (A ω) T
          (fun x => Real.sqrt m * ‖matrixApply S.transpose x‖)) μ →
        (∫ ω, setNormDeviation (A ω) T
          (fun x => Real.sqrt m * ‖matrixApply S.transpose x‖) ∂μ) ≤
          C * K ^ 2 * setGaussianComplexity (matrixImage S.transpose T) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.4.
  sorry

/-- **Exercise 9.5 (quadratic empirical process).** The source accidentally
declares only `X₁,…,Xₙ` while summing to `m`; here the samples are an
honest `Fin m` iid family. Separability/measurability and finiteness of the
real `γ₂` wrapper are made explicit.

**Book Exercise 9.5.** -/
theorem exercise_9_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m : ℕ} {hm : 0 < m} {α Ω : Type*}
        {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ]
        (F : Set (α → ℝ)) (X : Fin m → Ω → α)
        (X₀ : Ω → α) (K : ℝ),
        F.Nonempty →
        (∀ f ∈ F, ∀ a ∈ Set.Icc (0 : ℝ) 1,
          (fun x => a * f x) ∈ F) →
        iIndepFun X μ → (∀ i, IdentDistrib (X i) X₀ μ μ) →
        0 ≤ K →
        (∀ f ∈ F, Measurable (fun ω => f (X₀ ω))) →
        (∀ f ∈ F, Integrable (fun ω => (f (X₀ ω)) ^ 2) μ) →
        (∀ f ∈ F, ∀ g ∈ F,
          HDP.psi2Norm (fun ω => f (X₀ ω) - g (X₀ ω)) μ ≤
            K * functionL2Metric X₀ μ f g) →
        setGammaTwoENN F (functionL2Metric X₀ μ) ≠ ⊤ →
        (∀ ω, BddAbove {r : ℝ | ∃ f ∈ F,
          r = |Real.sqrt (((m : ℝ)⁻¹ * ∑ i, (f (X i ω)) ^ 2)) -
            Real.sqrt (∫ ξ, (f (X₀ ξ)) ^ 2 ∂μ)|}) →
        Measurable (quadraticEmpiricalDeviation F X X₀ μ) →
        Integrable (quadraticEmpiricalDeviation F X X₀ μ) μ →
        (∫ ω, quadraticEmpiricalDeviation F X X₀ μ ω ∂μ) ≤
          C * K ^ 2 * setGammaTwo F (functionL2Metric X₀ μ) /
            Real.sqrt m := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.5, process bound.
  sorry

/-- **Exercise 9.5 (linear specialization).** For the class of linear
functionals indexed by a subset of the Euclidean sphere, the preceding
quadratic-process conclusion is exactly the matrix-deviation conclusion.

**Book Exercise 9.5.** -/
theorem exercise_9_5_linear_specialization :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {hm : 0 < m} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (T : Set (Euc n)) (K : ℝ),
        T.Nonempty → Bornology.IsBounded T →
        (∀ x ∈ T, ‖x‖ = 1) → 0 ≤ K →
        A.AEMeasurableEntries μ → A.IsotropicRows μ →
        iIndepFun (fun i ω => HDP.randomMatrixRow A i ω) μ →
        A.RowPsi2Bound μ K →
        (∀ ω, BddAbove {r : ℝ | ∃ x ∈ T,
          r = |‖matrixApply (A ω) x‖ - Real.sqrt m * ‖x‖|}) →
        Measurable (fun ω => setNormDeviation (A ω) T
          (fun x => Real.sqrt m * ‖x‖)) →
        Integrable (fun ω => setNormDeviation (A ω) T
          (fun x => Real.sqrt m * ‖x‖)) μ →
        (∫ ω, setNormDeviation (A ω) T
          (fun x => Real.sqrt m * ‖x‖) ∂μ) ≤
          C * K ^ 2 * setGaussianComplexity T := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.5, specialization.
  sorry

/-- Norm-deviation supremum for a true Haar orthogonal projection.

**Lean implementation helper.** -/
def projectionNormDeviation {n m : ℕ}
    (P : HDP.Chapter5.Grassmannian n m) (T : Set (Euc n)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ T,
    r = |‖HDP.Chapter5.randomProjection P x‖ -
      Real.sqrt ((m : ℝ) / n) * ‖x‖|}

/-- **Exercise 9.6 (deviation of random projections).**.

**Book Exercise 9.6.** -/
theorem exercise_9_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Set (Euc n)), T.Nonempty → Bornology.IsBounded T →
        (∀ P : HDP.Chapter5.Grassmannian n m,
          BddAbove {r : ℝ | ∃ x ∈ T,
          r = |‖HDP.Chapter5.randomProjection P x‖ -
            Real.sqrt ((m : ℝ) / n) * ‖x‖|}) →
        Measurable (fun P : HDP.Chapter5.Grassmannian n m =>
          projectionNormDeviation P T) →
        Integrable (fun P : HDP.Chapter5.Grassmannian n m =>
          projectionNormDeviation P T)
            (HDP.Chapter5.grassmannHaarMeasure n m) →
        (∫ P, projectionNormDeviation P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
            C * setGaussianComplexity T / Real.sqrt n := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.6.
  sorry

end

end HDP.Chapter9.Exercise
