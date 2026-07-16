import HighDimensionalProbability.Chapter4_RandomMatrices

/-!
# Chapter 5 exercises attached to Section 5.5

Exercise 5.25 asks for the loopless analogue of the source's loop-aware model.
The theorem below makes “a version” precise while keeping the model and
algorithm outside the main import graph.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace HDP.Chapter5.Exercise

/-- Adjacency matrix obtained by deleting the diagonal coordinates from the shared balanced SBM
sample. The unused loop coordinates do not affect its law, so this realizes the usual loopless
model without a second product space.

**Lean implementation helper.** -/
def looplessSBMAdjacency {k : ℕ} (G : HDP.SBMSample k) :
    Matrix (HDP.SBMVertex k) (HDP.SBMVertex k) ℝ :=
  fun i j => if i = j then 0 else HDP.sbmAdjacencyMatrix G i j

/-- Shows that loopless sbmadjacency is symmetric.

**Lean implementation helper.** -/
lemma looplessSBMAdjacency_symmetric {k : ℕ} (G : HDP.SBMSample k) :
    (looplessSBMAdjacency G).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, looplessSBMAdjacency]
  by_cases h : i = j
  · subst j
    simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    exact congrFun (congrFun (HDP.sbmAdjacencyMatrix_symmetric G) i) j

/-- Ordered second eigenvector of the loopless adjacency operator.

**Lean implementation helper.** -/
noncomputable def looplessSBMSecondEigenvector {k : ℕ} (hk : 0 < k)
    (G : HDP.SBMSample k) : EuclideanSpace ℝ (HDP.SBMVertex k) :=
  let T := (looplessSBMAdjacency G).toEuclideanLin
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (isHermitian_iff_isSymm.mpr (looplessSBMAdjacency_symmetric G))
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (HDP.SBMVertex k)) = 2 * k := by
    simp [finrank_euclideanSpace]
  hT.eigenvectorBasis hn ⟨1, by omega⟩

/-- Sign classifier associated with the loopless second eigenvector.

**Lean implementation helper.** -/
noncomputable def looplessSBMSpectralEstimate {k : ℕ} (hk : 0 < k)
    (G : HDP.SBMSample k) : HDP.SBMVertex k → ℝ :=
  fun i => WithLp.ofLp (looplessSBMSecondEigenvector hk G) i

/-- The error is minimized over global label swap, diagonal deletion is explicit, and all
constants are absolute.

**Book Exercise 5.25.** -/
theorem exercise_5_25 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {k : ℕ} (hk : 0 < k) (p q : Set.Icc (0 : ℝ) 1),
        0 < (q : ℝ) → (q : ℝ) < p →
        C * (p : ℝ) * Real.log (2 * k) ≤
          (k : ℝ) * ((p : ℝ) - q) ^ 2 →
        (HDP.stochasticBlockModel k p q).real
          {G | HDP.misclassifiedUpToSign HDP.sbmCommunityLabel
              (looplessSBMSpectralEstimate hk G) ≤ (2 * k) / 100} ≥
          99 / 100 := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 5.25.
  sorry

end HDP.Chapter5.Exercise
