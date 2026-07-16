/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter8_Chaining

/-!
# Book Chapter 8 exercises attached to Section 8.5

Exercises 8.35, 8.36, and 8.37 are promoted into Chapter 8 core and are not
redeclared here.  The proof-question part of Exercise 8.34 is stated directly
on the finite metric space isometric to the source's weighted coordinate
example.  Its construction-only part (a) is recorded but skipped under the
book-wide exercise policy.
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Chapter8.Exercise

noncomputable section

/-- Source-level infinite admissible sequence for an arbitrary nonempty
index type.  Unlike the optimized finite core certificate, this definition
does not assume that the index type itself is finite. -/
structure AdmissibleSequence (T : Type*) [Nonempty T] where
  level : ℕ → Finset T
  level_nonempty : ∀ k, (level k).Nonempty
  level_zero_card : (level 0).card = 1
  level_card_le : ∀ k, (level k).card ≤ 2 ^ (2 ^ k)

/-- Weighted approximation cost of one point along an infinite admissible
sequence.

**Lean implementation helper.** -/
def admissibleSequencePointCost {T : Type*} [Nonempty T]
    (d : T → T → ℝ≥0∞) (A : AdmissibleSequence T) (t : T) : ℝ≥0∞ :=
  ∑' k : ℕ, HDP.gammaTwoWeight k *
    HDP.finiteSetEDistance d (A.level k) (A.level_nonempty k) t

/-- Supremal source cost of an infinite admissible sequence.

**Lean implementation helper.** -/
def admissibleSequenceCost {T : Type*} [Nonempty T]
    (d : T → T → ℝ≥0∞) (A : AdmissibleSequence T) : ℝ≥0∞ :=
  ⨆ t : T, admissibleSequencePointCost d A t

/-- Definition 8.5.1 on an arbitrary nonempty index type.

**Book Definition 8.5.1.** -/
def gamma2General {T : Type*} [Nonempty T]
    (d : T → T → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ A : AdmissibleSequence T, admissibleSequenceCost d A

/-- Dudley's entropy integral for an arbitrary metric space.

**Lean implementation helper.** -/
def generalGammaDudleyEntropyIntegral (T : Type*) [PseudoMetricSpace T] : ℝ :=
  ∫ ε in Set.Ioi (0 : ℝ), Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ))

/-- Dudley's entropy integral for a finite metric space.

**Lean implementation helper.** -/
def gammaDudleyEntropyIntegral (T : Type*) [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] : ℝ :=
  ∫ ε in Set.Ioi (0 : ℝ), Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ))

/-- **Exercise 8.33.** The source-level gamma-two functional on an arbitrary
metric space is bounded by Dudley's entropy integral. Finiteness of every
positive-radius covering number is explicit because Mathlib's authoritative
covering number takes values in `ℕ∞`.

**Book Exercise 8.33.** -/
theorem exercise_8_33_gamma2_le_dudley :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Type*) [Nonempty T] [PseudoMetricSpace T],
        (∀ ε : ℝ, 0 < ε →
          Metric.coveringNumber (Real.toNNReal ε) (Set.univ : Set T) ≠ ⊤) →
        gamma2General (fun s t : T => edist s t) ≤
          ENNReal.ofReal (C * generalGammaDudleyEntropyIntegral T) :=
  -- EXERCISE-SORRY: Exercise 8.33.
  by sorry

/-! ## Exercise 8.34: weighted coordinate example -/

/-- Norm of the point indexed by `i`; index zero is the added origin and the
remaining points have norm `1 / sqrt(1 + log i)`.

**Lean implementation helper.** -/
def looseDudleyWeight {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  if (i : ℕ) = 0 then 0
  else (Real.sqrt (1 + Real.log (i : ℕ)))⁻¹

/-- Metric of the orthogonal weighted-coordinate family from Exercise 8.34.

**Book Exercise 8.34.** -/
def looseDudleyMetric {n : ℕ} (i j : Fin (n + 1)) : ℝ≥0∞ :=
  if i = j then 0
  else ENNReal.ofReal (Real.sqrt
    (looseDudleyWeight i ^ 2 + looseDudleyWeight j ^ 2))

/-- Dudley's order-of-operations cost: sum over scales after taking the
largest approximation error at each scale.

**Lean implementation helper.** -/
def dudleyUniformChainCost {T : Type*} [Fintype T] [Nonempty T]
    (d : T → T → ℝ≥0∞) (A : HDP.FiniteAdmissibleChain T) : ℝ≥0∞ :=
  ∑ k : Fin (A.terminal + 1), HDP.gammaTwoWeight (k : ℕ) *
    Finset.univ.sup' Finset.univ_nonempty (fun t =>
      HDP.finiteSetEDistance d (A.level k) (A.level_nonempty k) t)

/-- Infimum of Dudley's uniform chain costs.

**Lean implementation helper.** -/
def dudleyUniformChainFunctional {T : Type*} [Fintype T] [Nonempty T]
    (d : T → T → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ A : HDP.FiniteAdmissibleChain T, dudleyUniformChainCost d A

/- **Exercise 8.34(a), skipped construction task.**  The source asks the
reader to *construct* a particular admissible sequence for the weighted
coordinate family.  This is a non-proof witness task under the exercise
policy, is not used later, and therefore has no theorem declaration or
placeholder. -/

/-- **Exercise 8.34(b).** Every Dudley uniform chain has an unbounded cost on
the same family as the dimension grows.

**Book Exercise 8.34(b).** -/
theorem exercise_8_34b_dudley_chain_diverges :
    Tendsto (fun n : ℕ =>
      dudleyUniformChainFunctional
        (looseDudleyMetric (n := n))) atTop atTop :=
  -- EXERCISE-SORRY: Exercise 8.34(b).
  by sorry

/-! ## Exercise 8.38: correlated subgaussian vectors -/

/-- Finite-coordinate `ℓᵖ` norm for a real exponent.

**Lean implementation helper.** -/
def finiteEllPNorm {ι : Type*} [Fintype ι]
    (p : ℝ) (x : ι → ℝ) : ℝ :=
  Real.rpow (∑ i, |x i| ^ p) (1 / p)

/-- Maximum absolute coordinate, expressed as a real supremum so the definition
also has a harmless value on the empty index type.

**Lean implementation helper.** -/
def finiteSupCoordinateNorm {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  sSup (Set.range fun i => |x i|)

/-- Uniform subgaussianity of all one-dimensional marginals, without any
coordinate-independence assumption.

**Lean implementation helper.** -/
def IsSubGaussianVectorWith {N : ℕ} {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (X : Ω → EuclideanSpace ℝ (Fin N))
    (μ : Measure Ω) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 →
    HDP.SubGaussian (fun ω => inner ℝ u (X ω)) μ ∧
      HDP.psi2Norm (fun ω => inner ℝ u (X ω)) μ ≤ K

/-- **Exercise 8.38, the regime `1 ≤ p ≤ log N`.**.

**Book Exercise 8.38.** -/
theorem exercise_8_38_expected_ellp_low_exponent :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (X : Ω → EuclideanSpace ℝ (Fin N)) (K p : ℝ),
        2 ≤ N → 1 ≤ p → p ≤ Real.log N →
        IsSubGaussianVectorWith X μ K →
        Integrable (fun ω => finiteEllPNorm p (X ω)) μ →
        (∫ ω, finiteEllPNorm p (X ω) ∂μ) ≤
          C * K * Real.sqrt p * Real.rpow N (1 / p) :=
  -- EXERCISE-SORRY: Exercise 8.38 (the regime p ≤ log N).
  by sorry

/-- **Exercise 8.38, the regime `p ≥ log N`.**.

**Book Exercise 8.38.** -/
theorem exercise_8_38_expected_ellp_high_exponent :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (X : Ω → EuclideanSpace ℝ (Fin N)) (K p : ℝ),
        2 ≤ N → 1 ≤ p → Real.log N ≤ p →
        IsSubGaussianVectorWith X μ K →
        Integrable (fun ω => finiteEllPNorm p (X ω)) μ →
        (∫ ω, finiteEllPNorm p (X ω) ∂μ) ≤
          C * K * Real.sqrt (Real.log N) :=
  -- EXERCISE-SORRY: Exercise 8.38 (the regime p ≥ log N).
  by sorry

/-- **Exercise 8.38, the endpoint `p = ∞`.**.

**Book Exercise 8.38.** -/
theorem exercise_8_38_expected_ellp_infinity :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (X : Ω → EuclideanSpace ℝ (Fin N)) (K : ℝ),
        2 ≤ N → IsSubGaussianVectorWith X μ K →
        Integrable (fun ω => finiteSupCoordinateNorm (X ω)) μ →
        (∫ ω, finiteSupCoordinateNorm (X ω) ∂μ) ≤
          C * K * Real.sqrt (Real.log N) :=
  -- EXERCISE-SORRY: Exercise 8.38 (the endpoint p = ∞).
  by sorry

end

end HDP.Chapter8.Exercise
