/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter8_Chaining

/-!
# Book Chapter 8 exercises attached to Section 8.1

Exercises 8.1, 8.3, 8.4, and 8.5 are promoted into Chapter 8 core and are
therefore not redeclared here.  This leaf contains only the remaining
non-load-bearing proof exercises.
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Chapter8.Exercise

noncomputable section

/-- Diameter of a finite family presented by an index type.

**Lean implementation helper.** -/
def indexedEuclideanDiameter {T E : Type*} [Fintype T] [Nonempty T]
    [NormedAddCommGroup E] (a : T → E) : ℝ :=
  (Finset.univ.product Finset.univ).sup'
    (Finset.univ_nonempty.product Finset.univ_nonempty)
    fun p => ‖a p.1 - a p.2‖

/-- Dudley's entropy integral for the actual finite set of index vectors.

**Lean implementation helper.** -/
def indexedEuclideanEntropyIntegral {T E : Type*} [Fintype T]
    [NormedAddCommGroup E] (a : T → E) : ℝ :=
  ∫ ε in Set.Ioi (0 : ℝ), Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.range a)).toNat : ℝ))

/-- Entropy integral of a finite metric space over all positive radii.

**Lean implementation helper.** -/
def finiteSqrtEntropyIntegral (T : Type*) [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] : ℝ :=
  ∫ ε in Set.Ioi (0 : ℝ), Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ))

/-- Entropy integral with the square root removed, as in subexponential
chaining.

**Lean implementation helper.** -/
def finiteLinearEntropyIntegral (T : Type*) [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] : ℝ :=
  ∫ ε in Set.Ioi (0 : ℝ),
    Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ)

/-- Gaussian width of an arbitrary Euclidean set. This set-valued wrapper is
used in Exercise 8.6, whose source statement is for every bounded set rather
than only for a caller-supplied finite discretization.

**Book Exercise 8.6.** -/
def setGaussianWidth {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ g, sSup ((fun x => inner ℝ g x) '' S)
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Dudley's entropy integral for an arbitrary Euclidean set between the
source's refined lower and upper limits.

**Lean implementation helper.** -/
def setEuclideanEntropyIntegralBetween {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (a b : ℝ) : ℝ :=
  ∫ ε in Set.Icc a b, Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε) S).toNat : ℝ))

/-- Entropy integral truncated to radii at most `δ`.

**Lean implementation helper.** -/
def finiteLocalSqrtEntropyIntegral (T : Type*) [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (δ : ℝ≥0) : ℝ :=
  ∫ ε in Set.Icc (0 : ℝ) (δ : ℝ), Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ))

/-- Largest process increment among pairs at distance at most `δ`.

**Lean implementation helper.** -/
def finiteLocalProcessOscillation {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (X : HDP.RandomProcess T Ω) (δ : ℝ≥0)
    (ω : Ω) : ℝ :=
  (Finset.univ.product Finset.univ).sup'
    (Finset.univ_nonempty.product Finset.univ_nonempty) fun p =>
      if edist p.1 p.2 ≤ δ then |X p.1 ω - X p.2 ω| else 0

/-! The next wrappers retain the source's arbitrary metric index set.  Since
the source writes real-valued expectations and entropy integrals, the deferred
statements expose the boundedness, measurability, integrability, and finite
covering-number conditions that make those expressions meaningful. -/

/-- Pointwise supremum of a process over an arbitrary nonempty index type.

**Lean implementation helper.** -/
def processSupremum {T Ω : Type*} (X : HDP.RandomProcess T Ω) (ω : Ω) : ℝ :=
  sSup (Set.range fun t => X t ω)

/-- Entropy integral without the square root for an arbitrary metric space.

**Lean implementation helper.** -/
def linearEntropyIntegral (T : Type*) [PseudoMetricSpace T] : ℝ :=
  ∫ ε in Set.Ioi (0 : ℝ),
    Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ)

/-- Entropy integral up to `δ` for an arbitrary metric space.

**Lean implementation helper.** -/
def localSqrtEntropyIntegral (T : Type*) [PseudoMetricSpace T]
    (δ : ℝ) : ℝ :=
  ∫ ε in Set.Icc (0 : ℝ) δ, Real.sqrt
    (Real.log ((Metric.coveringNumber (Real.toNNReal ε)
      (Set.univ : Set T)).toNat : ℝ))

/-- Pointwise local oscillation over all pairs at distance at most `δ`.

**Lean implementation helper.** -/
def localProcessOscillation {T Ω : Type*} [PseudoMetricSpace T]
    (X : HDP.RandomProcess T Ω) (δ : ℝ) (ω : Ω) : ℝ :=
  sSup {z : ℝ | ∃ s t : T, dist s t ≤ δ ∧ z = |X s ω - X t ω|}

/-- **Exercise 8.2.** Gaussian concentration turns the expected Dudley bound
into the high-probability oscillation estimate of Remark 8.1.6. The universal
constant multiplies the entropy integral and diameter term as in (8.15).

**Book Exercise 8.2.** -/
theorem exercise_8_2_gaussian_dudley_high_probability :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T E : Type*} [Fintype T] [Nonempty T]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (a : T → E) {u : ℝ}, 0 ≤ u →
        (stdGaussian E).real
            {g | C * (indexedEuclideanEntropyIntegral a +
                u * indexedEuclideanDiameter a) <
              HDP.Chapter8.finiteProcessOscillation
                (HDP.Chapter7.canonicalGaussianProcess a) g} ≤
          2 * Real.exp (-u ^ 2) :=
  -- EXERCISE-SORRY: Exercise 8.2.
  by sorry

/-- **Exercise 8.6.** Dudley's lower integration limit can be raised to the
width scale `c w(T) / sqrt(n)` for every nonempty bounded Euclidean set, as
stated in the source.

**Book Exercise 8.6.** -/
theorem exercise_8_6_refined_dudley_limits :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {n : ℕ}, 0 < n →
      ∀ (S : Set (EuclideanSpace ℝ (Fin n))), S.Nonempty → Bornology.IsBounded S →
        setGaussianWidth S ≤
          C * setEuclideanEntropyIntegralBetween S
            (c * setGaussianWidth S / Real.sqrt n) (Metric.diam S) :=
  -- EXERCISE-SORRY: Exercise 8.6.
  by sorry

/-- **Exercise 8.7.** Subexponential Dudley inequality on the source's
arbitrary metric index set.

**Book Exercise 8.7.** -/
theorem exercise_8_7_subexponential_dudley :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T Ω : Type*} [Nonempty T] [PseudoMetricSpace T]
        {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
        (X : HDP.RandomProcess T Ω) (K : ℝ),
        0 ≤ K →
        (∀ s t,
          HDP.psi1Norm (fun ω => X t ω - X s ω) μ ≤ K * dist t s) →
        (∀ t, Measurable (X t)) →
        (∀ t, Integrable (X t) μ) →
        HDP.IsCenteredProcess X μ →
        (∀ ω, BddAbove (Set.range fun t => X t ω)) →
        Measurable (processSupremum X) → Integrable (processSupremum X) μ →
        (∀ ε : ℝ, 0 < ε →
          Metric.coveringNumber (Real.toNNReal ε) (Set.univ : Set T) ≠ ⊤) →
        (∫ ω, processSupremum X ω ∂μ) ≤
          C * K * linearEntropyIntegral T :=
  -- EXERCISE-SORRY: Exercise 8.7.
  by sorry

/-- **Exercise 8.8.** Local Dudley inequality on the source's arbitrary
metric index set.

**Book Exercise 8.8.** -/
theorem exercise_8_8_local_dudley :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T Ω : Type*} [Nonempty T] [PseudoMetricSpace T]
        {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
        (X : HDP.RandomProcess T Ω) (K δ : ℝ),
        0 < δ →
        HDP.HasSubGaussianIncrementsWith X μ
          (fun s t => dist s t) K →
        (∀ t, Measurable (X t)) →
        (∀ t, Integrable (X t) μ) →
        (∀ ω, BddAbove
          {z : ℝ | ∃ s t : T, dist s t ≤ δ ∧ z = |X s ω - X t ω|}) →
        Measurable (localProcessOscillation X δ) →
        Integrable (localProcessOscillation X δ) μ →
        (∀ ε : ℝ, 0 < ε → ε ≤ δ →
          Metric.coveringNumber (Real.toNNReal ε) (Set.univ : Set T) ≠ ⊤) →
        (∫ ω, localProcessOscillation X δ ω ∂μ) ≤
          C * K * localSqrtEntropyIntegral T δ :=
  -- EXERCISE-SORRY: Exercise 8.8.
  by sorry

end

end HDP.Chapter8.Exercise
