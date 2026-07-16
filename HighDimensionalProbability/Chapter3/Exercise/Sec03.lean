import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# Book Chapter 3 non-load-bearing exercises 3.14--3.31

Only category-A, non-load-bearing proof questions remain in this leaf. The
results used by Chapter 3 or later chapters live in thematic core modules;
core modules never import this file.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Real Matrix WithLp Module
open scoped BigOperators ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace HDP.Chapter3

noncomputable section

/- EXERCISE-SORRY (category A): Exercise 3.14 is not load-bearing. -/
/-- Every one-dimensional marginal of `N(μ,S)` is
Gaussian with the stated mean and quadratic-form variance. This includes
singular covariance matrices and the zero direction.

**Book Exercise 3.14.** -/
theorem exercise_3_14
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (v : EuclideanSpace ℝ ι) :
    Measure.map (fun x : EuclideanSpace ℝ ι ↦ inner ℝ v x)
        (multivariateGaussian μ S) =
      gaussianReal (inner ℝ v μ)
        (dotProduct (fun i ↦ v i)
          (Matrix.mulVec S (fun i ↦ v i))).toNNReal := by
  sorry

/- Exercise 3.17 is a pure witness/counterexample request (normal marginals,
zero covariance, but dependence). It is recorded and skipped under the
constructive-witness policy; there is no deferred declaration. -/

/- EXERCISE-SORRY (category A): Exercise 3.21 is not load-bearing. -/
/-- The orthogonal sum/difference transformation
preserves the product standard-Gaussian law.

**Book Exercise 3.21.** -/
theorem exercise_3_21
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    Measure.map
        (fun p : E × E ↦
          ((Real.sqrt 2)⁻¹ • (p.1 + p.2),
            (Real.sqrt 2)⁻¹ • (p.1 - p.2)))
        ((stdGaussian E).prod (stdGaussian E)) =
      (stdGaussian E).prod (stdGaussian E) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.24 is not load-bearing. -/
/-- A vector uniformly distributed on a Euclidean unit ball admits an
almost-everywhere polar decomposition into an independent radius and a uniform
unit-sphere direction.

**Book Exercise 3.24.** -/
theorem exercise_3_24
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measure.map X P = unitBallMeasure E) :
    ∃ (r : Ω → ℝ) (Z : Ω → Metric.sphere (0 : E) 1),
      IndepFun r Z P ∧
      Measure.map r P = unitBallRadiusMeasure (Module.finrank ℝ E) ∧
      Measure.map Z P = HDP.unitSphereMeasure E ∧
      (∀ᵐ ω ∂P, 0 ≤ r ω ∧ r ω ≤ 1) ∧
      X =ᵐ[P] fun ω ↦ r ω • (Z ω : E) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.25 is not load-bearing. -/
/-- The uniform ball of radius `√(n+2)` is isotropic.

**Book Exercise 3.25.** -/
theorem exercise_3_25 (n : ℕ) (hn : 0 < n) :
    HDP.IsIsotropic
      (fun y : EuclideanSpace ℝ (Fin n) ↦ Real.sqrt (n + 2) • y)
      (unitBallMeasure (EuclideanSpace ℝ (Fin n))) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.26 is not load-bearing. -/
/-- The expected coordinate supremum norm of a uniform point on the unit
sphere in `ℝⁿ` is comparable to `√(log n / n)`.

**Book Exercise 3.26.** -/
theorem exercise_3_26 (n : ℕ) (hn : 2 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c * Real.sqrt (Real.log n / n) ≤
        ∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          finSupNorm (x : EuclideanSpace ℝ (Fin n))
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) ∧
      (∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          finSupNorm (x : EuclideanSpace ℝ (Fin n))
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        C * Real.sqrt (Real.log n / n) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.28(a) is not load-bearing. -/
/-- Coordinatewise clipping is a metric projection
onto the cube.

**Book Exercise 3.28(a).** -/
theorem exercise_3_28a {n : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (x : EuclideanSpace ℝ (Fin n)) :
    cubeClip a x ∈ coordinateCube a ∧
      ∀ y ∈ coordinateCube a, dist x (cubeClip a x) ≤ dist x y := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.28(b) is not load-bearing. -/
/-- In sufficiently high dimension, a standard Gaussian vector is, with
probability at least `99/100`, close to a fixed coordinate cube relative to
its norm while still lying outside the cube dilated by a factor of `100`.

**Book Exercise 3.28(b).** -/
theorem exercise_3_28b :
    ∃ (n₀ : ℕ) (a : ℝ), 0 < a ∧ ∀ n > n₀,
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
        {g | Metric.infDist g (coordinateCube a) < (1 / 100 : ℝ) * ‖g‖ ∧
          g ∉ coordinateCube (100 * a)} ≥ ENNReal.ofReal (99 / 100) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.29 is not load-bearing. -/
/-- A family is Parseval iff the synthesis matrix has
orthonormal rows.

**Book Exercise 3.29.** -/
theorem exercise_3_29 {n N : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) :
    HDP.IsParsevalFrame u ↔
      ∀ i j, inner ℝ (frameRow u i) (frameRow u j) =
        if i = j then 1 else 0 := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.30 is not load-bearing. -/
/-- At least three equispaced
points on the circle of radius `√(2/N)` form a Parseval frame in `ℝ²`.

**Book Exercise 3.30.** -/
theorem exercise_3_30 (N : ℕ) (hN : 3 ≤ N) :
    HDP.IsParsevalFrame (regularPolygonFrame N) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.31 is not load-bearing. -/
/-- A finite isotropic law, retaining repeated support
points through its index type, yields a Parseval frame.

**Book Exercise 3.31.** -/
theorem exercise_3_31
    {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ι → ℝ) (x : ι → EuclideanSpace ℝ (Fin n))
    (hp : ∀ i, 0 ≤ p i)
    (hmom : ∀ a b, ∑ i, p i * x i a * x i b = if a = b then 1 else 0) :
    HDP.IsParsevalFrame (fun i ↦ Real.sqrt (p i) • x i) := by
  sorry

end

end HDP.Chapter3
