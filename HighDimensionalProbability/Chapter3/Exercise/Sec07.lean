import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# Book Chapter 3 exercises 3.55--3.58

Exercise 3.55 is promoted to the core file `23_AnalyticFeatures.lean`, where its
unique authoritative declaration is used by Chapter 3. The remaining proof
questions are isolated category-A leaves and are not imported by any core
module.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter3

/-- The difference between the linear Gaussian surrogate
`√(2/π) ⟪g,w⟫` and the sign of `⟪g,w⟫`.

**Book Exercise 3.56.** -/
noncomputable def linearizedSignError
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g w : E) : ℝ :=
  Real.sqrt (2 / Real.pi) * inner ℝ g w -
    HDP.pmSign (inner ℝ g w)

/- EXERCISE-SORRY (category A): Exercise 3.56 is not load-bearing.
The printed ambient dimensions `g ∈ ℝⁿ`, `u,v ∈ ℝⁿ⁻¹` are inconsistent;
the corrected declaration places all three vectors in the same space. -/
/-- Gaussian sign rounding yields the stated linear correlation identity, and
the sign-sign correlation splits into its linear term plus the covariance of
the two linearization errors.

**Book Exercise 3.56.** -/
theorem exercise_3_56
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∫ g : E, inner ℝ g u * HDP.pmSign (inner ℝ g v)
        ∂stdGaussian E) =
        Real.sqrt (2 / Real.pi) * inner ℝ u v ∧
      (∫ g : E, HDP.pmSign (inner ℝ g u) * HDP.pmSign (inner ℝ g v)
        ∂stdGaussian E) =
        (2 / Real.pi) * inner ℝ u v +
          ∫ g : E, linearizedSignError g u * linearizedSignError g v
            ∂stdGaussian E := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.57 is not load-bearing. -/
/-- For a positive-semidefinite quadratic form whose value on every sign
vector is at most `1`, every unit-vector relaxation has value at most `π/2`.

**Book Exercise 3.57.** -/
theorem exercise_3_57
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hsign : ∀ x : ι → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      HDP.quadraticObjective A x ≤ 1)
    (u : ι → EuclideanSpace ℝ κ) (hu : ∀ i, ‖u i‖ = 1) :
    HDP.vectorSDPObjective A u ≤ Real.pi / 2 := by
  sorry

/-- The supremum of the quadratic objective over all sign vectors.

**Lean implementation helper.** -/
noncomputable def integerQuadraticOptimum
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : ι → ℝ,
    (∀ i, x i = 1 ∨ x i = -1) ∧ r = HDP.quadraticObjective A x}

/-- The supremum of the vector-valued quadratic objective over unit-vector
assignments in the fixed-dimensional SDP relaxation.

**Lean implementation helper.** -/
noncomputable def vectorSDPOptimum
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  sSup {r : ℝ | ∃ X : ι → EuclideanSpace ℝ ι,
    (∀ i, ‖X i‖ = 1) ∧ r = HDP.vectorSDPObjective A X}

/- EXERCISE-SORRY (category A): Exercise 3.58 is not load-bearing. -/
/-- The SDP gap and the Gaussian randomized-rounding
guarantee, stated for the source-corrected finite index set.

**Book Exercise 3.58.** -/
theorem exercise_3_58
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    integerQuadraticOptimum A ≤ vectorSDPOptimum A ∧
      vectorSDPOptimum A ≤
        (Real.pi / 2) * integerQuadraticOptimum A ∧
      ∀ X : ι → EuclideanSpace ℝ ι, (∀ i, ‖X i‖ = 1) →
        (2 / Real.pi) * HDP.vectorSDPObjective A X ≤
          ∫ g : EuclideanSpace ℝ ι,
            HDP.quadraticObjective A
              (fun i => HDP.hyperplaneLabel g (X i))
            ∂stdGaussian (EuclideanSpace ℝ ι) := by
  sorry

end HDP.Chapter3
