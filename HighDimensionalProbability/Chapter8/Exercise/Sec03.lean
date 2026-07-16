/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter8_Chaining
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Nat.Log

/-!
# Book Chapter 8 exercises attached to Section 8.3

Exercises 8.13, 8.17, and 8.28 are promoted into Chapter 8 core and are not
redeclared here.  The geometric VC exercises use a set-family shattering API,
so their statements refer to the actual infinite classes in the source rather
than to an unrelated finite surrogate.

Exercise 8.22(b), which asks only for an extremizing construction, is omitted
under the requested construction-witness policy.  Exercise 8.27(b) is omitted
for the same reason; its quantitative claim is recorded in the module-level
documentation below part (a).
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace HDP.Chapter8.Exercise

noncomputable section

/-! ## Geometric VC dimension -/

/-- Shattering by a possibly infinite family of sets.

**Lean implementation helper.** -/
def SetFamilyShatters {α : Type*} (𝒜 : Set (Set α))
    (s : Finset α) : Prop :=
  ∀ t : Finset α, t ⊆ s →
    ∃ u ∈ 𝒜, ∀ x ∈ s, (x ∈ u ↔ x ∈ t)

/-- Exact finite VC dimension for a possibly infinite set family.

**Lean implementation helper.** -/
def HasSetFamilyVCDimension {α : Type*} (𝒜 : Set (Set α))
    (d : ℕ) : Prop :=
  (∃ s : Finset α, s.card = d ∧ SetFamilyShatters 𝒜 s) ∧
    ∀ s : Finset α, SetFamilyShatters 𝒜 s → s.card ≤ d

/-- Infinite VC dimension for a possibly infinite set family.

**Lean implementation helper.** -/
def HasInfiniteSetFamilyVCDimension {α : Type*}
    (𝒜 : Set (Set α)) : Prop :=
  ∀ d : ℕ, ∃ s : Finset α, s.card = d ∧ SetFamilyShatters 𝒜 s

/-- Unions of two closed real intervals.

**Lean implementation helper.** -/
def twoClosedIntervalFamily : Set (Set ℝ) :=
  {u | ∃ a b c d : ℝ, u = Set.Icc a b ∪ Set.Icc c d}

/-- Closed axis-aligned rectangles in the plane.

**Lean implementation helper.** -/
def axisAlignedRectangleFamily : Set (Set (ℝ × ℝ)) :=
  {u | ∃ a b c d : ℝ, u = Set.Icc a b ×ˢ Set.Icc c d}

/-- Closed axis-aligned squares in the plane.

**Lean implementation helper.** -/
def axisAlignedSquareFamily : Set (Set (ℝ × ℝ)) :=
  {u | ∃ a b r : ℝ, 0 ≤ r ∧
    u = Set.Icc a (a + r) ×ˢ Set.Icc b (b + r)}

/-- Convex hulls of arbitrary finite vertex sets.

**Lean implementation helper.** -/
def convexPolygonFamily : Set (Set (ℝ × ℝ)) :=
  {u | ∃ vertices : Finset (ℝ × ℝ),
    u = convexHull ℝ (vertices : Set (ℝ × ℝ))}

/-- **Exercise 8.12.** Two intervals have VC dimension four.

**Book Exercise 8.12.** -/
theorem exercise_8_12_vc_dimension_two_intervals :
    HasSetFamilyVCDimension twoClosedIntervalFamily 4 :=
  -- EXERCISE-SORRY: Exercise 8.12.
  by sorry

/-- **Exercise 8.14.** Axis-aligned rectangles have VC dimension four.

**Book Exercise 8.14.** -/
theorem exercise_8_14_vc_dimension_rectangles :
    HasSetFamilyVCDimension axisAlignedRectangleFamily 4 :=
  -- EXERCISE-SORRY: Exercise 8.14.
  by sorry

/-- **Exercise 8.15.** Axis-aligned squares have VC dimension three.

**Book Exercise 8.15.** -/
theorem exercise_8_15_vc_dimension_squares :
    HasSetFamilyVCDimension axisAlignedSquareFamily 3 :=
  -- EXERCISE-SORRY: Exercise 8.15.
  by sorry

/-- **Exercise 8.16.** Convex polygons with no vertex bound have infinite VC
dimension.

**Book Exercise 8.16.** -/
theorem exercise_8_16_vc_dimension_convex_polygons :
    HasInfiniteSetFamilyVCDimension convexPolygonFamily :=
  -- EXERCISE-SORRY: Exercise 8.16.
  by sorry

/-! ## Algebraic and combinatorial exercises -/

/-- Linear span of the indicator functions represented by a Boolean family.

**Lean implementation helper.** -/
def booleanLinearSpan {α : Type*} [DecidableEq α]
    (F : BooleanFamily α) : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ
    (booleanIndicator '' (F : Set (Finset α)))

/-- Indicator of an arbitrary support, used to view a Boolean class as a
family of real-valued functions.

**Lean implementation helper.** -/
noncomputable def setBooleanIndicator {α : Type*} (u : Set α) : α → ℝ :=
  by
    classical
    exact fun x => if x ∈ u then 1 else 0

/-- Linear span of all functions in an arbitrary Boolean class.

**Lean implementation helper.** -/
def booleanClassLinearSpan {α : Type*} (F : HDP.BooleanClass α) :
    Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ (setBooleanIndicator '' F)

/-- **Exercise 8.18.** VC dimension is at most the linear-algebraic dimension
of the Boolean indicators.

**Book Exercise 8.18.** -/
theorem exercise_8_18_vc_le_linear_dimension
    {α : Type*} (F : HDP.BooleanClass α)
    [FiniteDimensional ℝ (booleanClassLinearSpan F)] :
    F.VCDimLE (Module.finrank ℝ (booleanClassLinearSpan F)) :=
  -- EXERCISE-SORRY: Exercise 8.18.
  by sorry

/-- The Hamming ball of supports with at most `d` ones.

**Lean implementation helper.** -/
def hammingBallFamily (n d : ℕ) : BooleanFamily (Fin n) :=
  Finset.univ.filter fun u : Finset (Fin n) => u.card ≤ d

/-- **Exercise 8.19.** Hamming balls simultaneously attain equality in the
Pajor and Sauer--Shelah bounds.

**Book Exercise 8.19.** -/
theorem exercise_8_19_hamming_ball_sharpness
    {n d : ℕ} (hd : d ≤ n) :
    (hammingBallFamily n d).vcDim = d ∧
      (hammingBallFamily n d).shatterer = hammingBallFamily n d ∧
      (hammingBallFamily n d).card =
        ∑ k ∈ Finset.range (d + 1), Nat.choose n k :=
  -- EXERCISE-SORRY: Exercise 8.19.
  by sorry

/-- Trace of a possibly infinite set family on a finite support.

**Lean implementation helper.** -/
def setFamilyTrace {α : Type*} [DecidableEq α]
    (𝒜 : Set (Set α)) (s : Finset α) : Finset (Finset α) := by
  classical
  exact s.powerset.filter fun t =>
    ∃ u ∈ 𝒜, ∀ x ∈ s, (x ∈ u ↔ x ∈ t)

/-- **Exercise 8.20.** The growth function has the polynomial/exponential
dichotomy. The first alternative is full growth at every size; the second is
the Sauer polynomial bound for one fixed degree.

**Book Exercise 8.20.** -/
theorem exercise_8_20_vc_growth_dichotomy
    {α : Type*} [DecidableEq α] (𝒜 : Set (Set α)) :
    (∀ n : ℕ, ∃ s : Finset α,
      s.card = n ∧ (setFamilyTrace 𝒜 s).card = 2 ^ n) ∨
    ∃ d : ℕ, ∀ s : Finset α,
      (setFamilyTrace 𝒜 s).card ≤
        ∑ k ∈ Finset.range (d + 1), Nat.choose s.card k :=
  -- EXERCISE-SORRY: Exercise 8.20.
  by sorry

/-- Pointwise application of a Boolean formula to one member of each finite
Boolean class.

**Lean implementation helper.** -/
def combineBooleanFamilies {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (classes : Fin k → BooleanFamily α)
    (φ : (Fin k → Bool) → Bool) : BooleanFamily α := by
  classical
  exact Finset.univ.filter fun u : Finset α =>
    ∃ choice : Fin k → Finset α,
      (∀ i, choice i ∈ classes i) ∧
        ∀ x, (x ∈ u ↔ φ (fun i => decide (x ∈ choice i)) = true)

/-- Pointwise application of a Boolean formula to one member of each
arbitrary Boolean class.

**Lean implementation helper.** -/
noncomputable def combineBooleanClasses {α : Type*} {k : ℕ}
    (classes : Fin k → HDP.BooleanClass α)
    (φ : (Fin k → Bool) → Bool) : HDP.BooleanClass α := by
  classical
  exact {u | ∃ choice : Fin k → Set α,
    (∀ i, choice i ∈ classes i) ∧
      u = {x | φ (fun i => decide (x ∈ choice i)) = true}}

/-- **Exercise 8.21.** Stability under an arbitrary `k`-ary Boolean formula.

**Book Exercise 8.21.** -/
theorem exercise_8_21_vc_stability
    : ∃ C : ℕ, 0 < C ∧
      ∀ {α : Type*} {k d : ℕ}, 0 < k →
      ∀ (classes : Fin k → HDP.BooleanClass α)
        (φ : (Fin k → Bool) → Bool),
        (∀ i, (classes i).VCDimLE d) →
        (combineBooleanClasses classes φ).VCDimLE
          (C * d * k * (Nat.log2 k + 1)) :=
  -- EXERCISE-SORRY: Exercise 8.21.
  by sorry

/-- **Exercise 8.22(a).** VC dimension of a union of two classes.

**Book Exercise 8.22(a).** -/
theorem exercise_8_22a_vc_dimension_union
    {α : Type*} (F G : HDP.BooleanClass α) {d e : ℕ}
    (hF : HDP.BooleanClass.VCDimEq F d)
    (hG : HDP.BooleanClass.VCDimEq G e) :
    (F ∪ G).VCDimLE (d + e + 1) :=
  -- EXERCISE-SORRY: Exercise 8.22(a).
  by sorry

/-!
Exercise 8.22(b) is intentionally omitted: it asks only for an example
attaining equality in the preceding bound, hence is a pure construction
witness under the requested leaf policy.
-/

/-! ## Covering, uniform laws, and applications -/

/-- Boolean `L²(μ)` distance written without installing a quotient metric.

**Lean implementation helper.** -/
def booleanL2Distance {α : Type*} [DecidableEq α]
    {mα : MeasurableSpace α} (μ : Measure α)
    (u v : Finset α) : ℝ :=
  Real.sqrt (∫ x, (booleanIndicator u x - booleanIndicator v x) ^ 2 ∂μ)

/-- **Exercise 8.23.** For radius at least one, any nonempty arbitrary class
of measurable Boolean functions is covered by one ball in `L²(μ)`.

**Book Exercise 8.23.** -/
theorem exercise_8_23_large_radius_covering
    {α : Type*} {mα : MeasurableSpace α}
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : HDP.BooleanClass α) (hFne : F.Nonempty)
    (hF : ∀ u ∈ F, MeasurableSet u)
    {ε : ℝ≥0} (hε : 1 ≤ ε) :
    Metric.coveringNumber ε (HDP.Chapter8.booleanClassLp μ F hF) ≤ 1 :=
  -- EXERCISE-SORRY: Exercise 8.23.
  by sorry

/-- **Exercise 8.24.** The direct Sauer--Shelah argument gives the weaker
VC law with its extra logarithmic factor. This is stated for the source's
possibly infinite Boolean class; `E` is the same explicit separability /
measurability certificate used by the arbitrary-class Theorem 8.3.15.

**Book Exercise 8.24.** -/
theorem exercise_8_24_weaker_vc_law :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α Ω : Type*}
        {mα : MeasurableSpace α}
        {mΩ : MeasurableSpace Ω} {μ : Measure α} {P : Measure Ω}
        [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
        {n d : ℕ} (F : HDP.BooleanClass α)
        (hF : ∀ u ∈ F, MeasurableSet u)
        (E : HDP.Chapter8.BooleanDeviationExhaustion μ F)
        (X : Fin n → Ω → α),
        0 < d → d ≤ n → F.VCDimLE d →
        (∀ i, Measurable (X i)) →
        (∀ i, HasLaw (X i) μ P) →
        iIndepFun X P →
        (∫ ω, HDP.Chapter8.booleanClassUniformDeviation μ
            (fun i => X i ω) F ∂P) ≤
          C * Real.sqrt (((d : ℝ) / n) *
            Real.log (Real.exp 1 * (n : ℝ) / d)) :=
  -- EXERCISE-SORRY: Exercise 8.24.
  by sorry

/-- Finite measurable supremum of CDF deviations over directions and
thresholds.

**Lean implementation helper.** -/
def finiteMarginalCDFDeviation {n m : ℕ}
    (directions : Finset (EuclideanSpace ℝ (Fin n)))
    (thresholds : Finset ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (sample : Fin m → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖fun p : ↥(directions.product thresholds) =>
    empiricalProcessValue μ sample fun x =>
      if inner ℝ p.1.1 x ≤ p.1.2 then (1 : ℝ) else 0‖

/-- Uniform CDF deviation over every unit direction and every threshold.

**Lean implementation helper.** -/
def marginalCDFDeviation {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (sample : Fin m → EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
    ∃ t : ℝ, r = |empiricalProcessValue μ sample fun x =>
      if inner ℝ u x ≤ t then (1 : ℝ) else 0|}

/-- **Exercise 8.25.** The CDFs of all one-dimensional marginals are learned
uniformly at the dimension/sample rate.

**Book Exercise 8.25.** -/
theorem exercise_8_25_learning_marginals :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n m : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (μ : Measure (EuclideanSpace ℝ (Fin n)))
        (X : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        0 < n → 0 < m →
        (∀ i, Measurable (X i)) →
        (∀ i, Measure.map (X i) P = μ) →
        iIndepFun X P →
        Integrable (fun ω => marginalCDFDeviation
          μ (fun i => X i ω)) P →
        (∫ ω, marginalCDFDeviation μ
            (fun i => X i ω) ∂P) ≤
          C * Real.sqrt ((n : ℝ) / m) :=
  -- EXERCISE-SORRY: Exercise 8.25.
  by sorry

/-- The source's sign convention, with zero assigned the positive bit.

**Lean implementation helper.** -/
def signBit (x : ℝ) : Bool := decide (0 ≤ x)

/- **Exercise 8.26, skipped preamble construction.**  Before parts (a) and
(b), the source asks the reader to see why arbitrarily close vectors can be
sent to very different one-bit outputs.  This is a non-load-bearing
counterexample/witness prompt, so it is recorded here without manufacturing
a theorem or a proof placeholder. -/

/-- One-bit code generated by a list of measurement rows.

**Lean implementation helper.** -/
def oneBitCode {m n : ℕ}
    (rows : Fin m → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) : Fin m → Bool :=
  fun i => signBit (inner ℝ (rows i) u)

/-- Hamming distance on a finite Boolean cube.

**Lean implementation helper.** -/
def boolHammingDistance {m : ℕ} (x y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/-- **Exercise 8.26(a).** Expected one-bit Hamming distance is normalized
spherical geodesic distance.

**Book Exercise 8.26(a).** -/
theorem exercise_8_26a_expected_one_bit_distance
    {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (rows : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hrows : ∀ i, HasLaw (rows i)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) P) :
    (∫ ω, (boolHammingDistance
        (oneBitCode (fun i => rows i ω) u)
        (oneBitCode (fun i => rows i ω) v) : ℝ) / m ∂P) =
      Real.arccos (inner ℝ u v) / Real.pi :=
  -- EXERCISE-SORRY: Exercise 8.26(a).
  by sorry

/-- **Exercise 8.26(b).** Uniform one-bit embedding of the entire Euclidean
unit sphere, not merely a caller-supplied finite subset.

**Book Exercise 8.26(b).** -/
theorem exercise_8_26b_uniform_one_bit_quantization :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (rows : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        0 < n → 0 < m →
        (∀ i, HasLaw (rows i)
          (stdGaussian (EuclideanSpace ℝ (Fin n))) P) →
        iIndepFun rows P →
        P.real {ω | ∀ u v : EuclideanSpace ℝ (Fin n),
          ‖u‖ = 1 → ‖v‖ = 1 →
          |(boolHammingDistance
              (oneBitCode (fun i => rows i ω) u)
              (oneBitCode (fun i => rows i ω) v) : ℝ) / m -
            Real.arccos (inner ℝ u v) / Real.pi| ≤
              C * Real.sqrt ((n : ℝ) / m)} ≥ 0.99 :=
  -- EXERCISE-SORRY: Exercise 8.26(b).
  by sorry

/-- Matrix whose rows are the sampled vectors.

**Lean implementation helper.** -/
def matrixOfRows {m n : ℕ} {Ω : Type*}
    (rows : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => rows i ω j

/-- Euclidean norm of a coordinate vector, used for `A u`.

**Lean implementation helper.** -/
def coordinateL2Norm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- **Exercise 8.27(a).** The small-ball/VC lower singular-value bound. The printed hint contains a missing square: from
`|⟪X,u⟫| ≥ ε` one obtains `⟪X,u⟫² ≥ ε²`, not `≥ ε`. The conclusion below
uses the corrected `ε * sqrt(δ m)` scale.

**Book Exercise 8.27(a).** -/
theorem exercise_8_27a_small_ball_invertibility :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (X : Ω → EuclideanSpace ℝ (Fin n))
        (rows : Fin m → Ω → EuclideanSpace ℝ (Fin n))
        (ε δ : ℝ),
        0 < ε → 0 < δ →
        (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
          P.real {ω | ε ≤ |inner ℝ (X ω) u|} ≥ δ) →
        (∀ i, Measurable (rows i)) → Measurable X →
        (∀ i, Measure.map (rows i) P = Measure.map X P) →
        iIndepFun rows P →
        C * δ⁻¹ ^ 2 * n ≤ m →
        P.real {ω | ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
          0.99 * ε * Real.sqrt (δ * m) ≤
            coordinateL2Norm ((matrixOfRows rows ω).mulVec u)} ≥ 0.99 :=
  -- EXERCISE-SORRY: Exercise 8.27(a).
  by sorry

/-!
Exercise 8.27(b) is intentionally omitted because it asks only for a random
vector/matrix construction witnessing optimality.  Its target scale is
`E s_n(A) ≤ 1.01 ε sqrt(δ m)` under the same anti-concentration condition.
-/

end

end HDP.Chapter8.Exercise
