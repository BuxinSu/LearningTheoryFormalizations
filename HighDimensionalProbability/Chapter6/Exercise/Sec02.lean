import HighDimensionalProbability.Chapter6_QuadraticFormsSymmetrizationContraction
import HighDimensionalProbability.Prelude.SimpleGraph

/-!
# Chapter 6 exercises attached to Section 6.2

Exercise 6.5 is a pure counterexample task and is intentionally omitted.  The
remaining declarations are the non-load-bearing Hanson--Wright applications
and variants, with the source's degenerate cases made explicit.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HDP.Chapter6.Exercise

/-- A column of a random real matrix as a Euclidean random vector.

**Lean implementation helper.** -/
def randomMatrixColumn {Ω : Type*} {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    Ω → EuclideanSpace ℝ (Fin m) :=
  fun ω => WithLp.toLp 2 ((A ω).col j)

/-- The scalar quadratic form `xᵀ A x`.

**Lean implementation helper.** -/
def realQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- The off-diagonal inner-product quadratic form from the corresponding exercise.

**Lean implementation helper.** -/
def offDiagonalVectorQuadratic {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, A i j * inner ℝ (X i) (X j)

/-- The empirical mean of `N` Euclidean observations.

**Lean implementation helper.** -/
def empiricalVectorMean {Ω : Type*} {N n : ℕ}
    (X : Fin N → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) :=
  (N : ℝ)⁻¹ • ∑ i, X i ω

/-- The Euclidean distance to a subspace, represented by its orthogonal projection.

**Lean implementation helper.** -/
def distanceToSubspace {n : ℕ} (E : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖x - HDP.orthogonalProjectionOperator E x‖

/-- The number of edges of a finite graph, exposed without leaking the noncomputable `Fintype
G.edgeSet` implementation into theorem signatures.

**Lean implementation helper.** -/
def graphEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- The vectors need not be independent and may have dependent coordinates; only their
one-dimensional subgaussian marginals are uniformly controlled.

**Book Exercise 6.6(a).** -/
theorem exercise_6_6a :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {N n : ℕ} (hN : 0 < N)
        (X : Fin N → Ω → EuclideanSpace ℝ (Fin n)),
        (∀ i, AEMeasurable (X i) P) →
        (∀ i, Integrable (X i) P) →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, HDP.SubGaussianVector (X i) P) →
        ∀ {K : ℝ}, 0 < K →
        (∀ i, HDP.psi2NormVector (X i) P ≤ K) →
        (∫ ω, Finset.univ.sup'
            ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun i => ‖X i ω‖) ∂P) ≤
          C * K * (Real.sqrt n + Real.sqrt (Real.log N)) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.6(a).
  sorry

/-- The columns are independent isotropic subgaussian vectors; their coordinates need not be
independent.

**Book Exercise 6.6(b).** -/
theorem exercise_6_6b :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
        (A : Ω → Matrix (Fin m) (Fin n) ℝ),
        (∀ i j, AEMeasurable (fun ω => A ω i j) P) →
        iIndepFun (randomMatrixColumn A) P →
        (∀ j, HDP.IsIsotropic (randomMatrixColumn A j) P) →
        (∀ j, HDP.SubGaussianVector (randomMatrixColumn A j) P) →
        ∀ {K : ℝ}, 0 < K →
        (∀ j, HDP.psi2NormVector (randomMatrixColumn A j) P ≤ K) →
        (∫ ω, HDP.Chapter4.matrixLpToLpNorm 1 ∞ (A ω) ∂P) ≤
            C * K * (Real.sqrt (Real.log m) + Real.sqrt (Real.log n)) ∧
          (∫ ω, HDP.Chapter4.matrixLpToLpNorm 1 2 (A ω) ∂P) ≤
            C * K * (Real.sqrt m + Real.sqrt (Real.log n)) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.6(b).
  sorry

/-- The Gaussian specialization of Hanson--Wright. The exercise's requirement that the proof use
SVD and rotation invariance is a proof-audit obligation rather than part of the proposition.

**Book Exercise 6.7.** -/
theorem exercise_6_7 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {n : ℕ}
        (X : Ω → EuclideanSpace ℝ (Fin n))
        (hX : HDP.HasGaussianVectorLaw X P 0 1)
        (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.IsHermitian)
        {t : ℝ}, 0 ≤ t →
        P.real {ω | |realQuadraticForm A (X ω) - A.trace| ≥ t} ≤
          2 * Real.exp (-c * min
            (t ^ 2 / HDP.matrixFrobeniusNorm A ^ 2)
            (t / HDP.matrixOpNorm A)) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.7.
  sorry

/-- Higher-dimensional off-diagonal Hanson--Wright, with the absolute-value event restored from
the authoritative PDF.

**Book Exercise 6.8.** -/
theorem exercise_6_8 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {n d : ℕ} (hd : 0 < d)
        (A : Matrix (Fin n) (Fin n) ℝ)
        (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)),
        iIndepFun X P → (∀ i, AEMeasurable (X i) P) →
        (∀ i, Integrable (X i) P) → (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, HDP.SubGaussianVector (X i) P) →
        ∀ {K t : ℝ}, 0 < K → 0 ≤ t →
        (∀ i, HDP.psi2NormVector (X i) P ≤ K) →
        P.real {ω | |offDiagonalVectorQuadratic A (fun i => X i ω)| ≥ t} ≤
          2 * Real.exp (-c * min
            (t ^ 2 /
              (K ^ 4 * (d : ℝ) * HDP.matrixFrobeniusNorm A ^ 2))
            (t / (K ^ 2 * HDP.matrixOpNorm A))) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.8.
  sorry

/-- MGF of the squared norm of a linear image of a centered subgaussian vector.

**Book Exercise 6.9.** -/
theorem exercise_6_9 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ}
        (B : Matrix (Fin m) (Fin n) ℝ)
        (X : Ω → EuclideanSpace ℝ (Fin n)),
        AEMeasurable X P → Integrable X P → (∫ ω, X ω ∂P = 0) →
        HDP.SubGaussianVector X P →
        ∀ {K lam : ℝ}, 0 < K → HDP.psi2NormVector X P ≤ K →
        |lam| ≤ c / (K * HDP.matrixOpNorm B) →
        (∫ ω, Real.exp (lam ^ 2 * ‖B.toEuclideanLin (X ω)‖ ^ 2) ∂P) ≤
          Real.exp
            (C * K ^ 2 * lam ^ 2 * HDP.matrixFrobeniusNorm B ^ 2) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.9.
  sorry

/-- Tail bound for the norm of an anisotropic subgaussian vector.

**Book Exercise 6.10.** -/
theorem exercise_6_10 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ}
        (B : Matrix (Fin m) (Fin n) ℝ)
        (X : Ω → EuclideanSpace ℝ (Fin n)),
        AEMeasurable X P → Integrable X P → (∫ ω, X ω ∂P = 0) →
        HDP.SubGaussianVector X P →
        ∀ {K t : ℝ}, 0 < K → 0 ≤ t →
        HDP.psi2NormVector X P ≤ K →
        P.real {ω | ‖B.toEuclideanLin (X ω)‖ ≥
          C * K * (HDP.matrixFrobeniusNorm B + t * HDP.matrixOpNorm B)} ≤
          Real.exp (-t ^ 2) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.10.
  sorry

/-- Positive-semidefinite Hanson--Wright without coordinate independence. The requested
counterexample explaining why no lower tail is possible is a non-proof subtask and is omitted.

**Book Exercise 6.11.** -/
theorem exercise_6_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {n : ℕ}
        (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.PosSemidef)
        (X : Ω → EuclideanSpace ℝ (Fin n)),
        AEMeasurable X P → Integrable X P → (∫ ω, X ω ∂P = 0) →
        HDP.SubGaussianVector X P →
        ∀ {K s : ℝ}, 0 < K → 0 ≤ s →
        HDP.psi2NormVector X P ≤ K →
        P.real {ω | realQuadraticForm A (X ω) ≥
          C * K ^ 2 * (A.trace + s * HDP.matrixOpNorm A)} ≤
          Real.exp (-s) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.11.
  sorry

/-- The empirical mean is `μ_N`, not the source's mismatched `μ_n`.

**Book Exercise 6.12.** -/
theorem exercise_6_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {N n : ℕ} (hN : 0 < N)
        (X : Fin N → Ω → EuclideanSpace ℝ (Fin n))
        (mu : EuclideanSpace ℝ (Fin n))
        (Sigma : Matrix (Fin n) (Fin n) ℝ),
        iIndepFun X P → (∀ i, AEMeasurable (X i) P) →
        (∀ i, Integrable (X i) P) →
        (∀ i, ∫ ω, X i ω ∂P = mu) →
        (∀ i, HDP.covarianceMatrix (X i) P = Sigma) →
        (∀ i j, IdentDistrib (X i) (X j) P P) →
        ∀ {K alpha : ℝ}, 0 < K → 0 < alpha → alpha < 1 →
        (∀ i u, HDP.psi2Norm
            (fun ω => inner ℝ (X i ω - mu) u) P ≤
          K * Real.sqrt
            (∫ ω, inner ℝ (X i ω - mu) u ^ 2 ∂P)) →
        P.real {ω | ‖empiricalVectorMean X ω - mu‖ ≤
          C * K * Real.sqrt (Sigma.trace / N) +
            C * K * Real.sqrt
              (HDP.matrixOpNorm Sigma * Real.log (alpha⁻¹) / N)} ≥
          1 - alpha := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.12.
  sorry

/-- Anisotropic concentration of the norm for a vector with independent centered unit-variance
subgaussian coordinates.

**Book Exercise 6.13.** -/
theorem exercise_6_13 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {m n : ℕ}
        (B : Matrix (Fin m) (Fin n) ℝ)
        (X : Ω → EuclideanSpace ℝ (Fin n)),
        AEMeasurable X P →
        iIndepFun (fun i ω => X ω i) P →
        (∀ i, ∫ ω, X ω i ∂P = 0) →
        (∀ i, ∫ ω, X ω i ^ 2 ∂P = 1) →
        (∀ i, HDP.SubGaussian (fun ω => X ω i) P) →
        ∀ {K : ℝ}, 0 < K →
        (∀ i, HDP.psi2Norm (fun ω => X ω i) P ≤ K) →
        HDP.psi2Norm
          (fun ω => ‖B.toEuclideanLin (X ω)‖ - HDP.matrixFrobeniusNorm B) P ≤
          C * K ^ 2 * HDP.matrixOpNorm B := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.13.
  sorry

/-- Exact mean squared distance to a `d`-dimensional subspace.

**Book Exercise 6.14(a).** -/
theorem exercise_6_14a {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {n d : ℕ}
    (E : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (_hdim : Module.finrank ℝ E = d)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (_hXm : AEMeasurable X P)
    (_hind : iIndepFun (fun i ω => X ω i) P)
    (_hmean : ∀ i, ∫ ω, X ω i ∂P = 0)
    (_hsecond : ∀ i, ∫ ω, X ω i ^ 2 ∂P = 1) :
    (∫ ω, distanceToSubspace E (X ω) ^ 2 ∂P) = (n - d : ℕ) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.14(a).
  sorry

/-- Concentration of distance to a subspace, including the full-subspace zero-distance case
without division by `n-d`.

**Book Exercise 6.14(b).** -/
theorem exercise_6_14b :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        [IsProbabilityMeasure P] {n d : ℕ}
        (E : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
        Module.finrank ℝ E = d →
        ∀ (X : Ω → EuclideanSpace ℝ (Fin n)),
        AEMeasurable X P →
        iIndepFun (fun i ω => X ω i) P →
        (∀ i, ∫ ω, X ω i ∂P = 0) →
        (∀ i, ∫ ω, X ω i ^ 2 ∂P = 1) →
        (∀ i, HDP.SubGaussian (fun ω => X ω i) P) →
        ∀ {K t : ℝ}, 0 < K → 0 ≤ t →
        (∀ i, HDP.psi2Norm (fun ω => X ω i) P ≤ K) →
        P.real {ω | |distanceToSubspace E (X ω) - Real.sqrt (n - d)| > t} ≤
          2 * Real.exp (-c * t ^ 2 / K ^ 4) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.14(b).
  sorry

/-- The positive edge count excludes the false edgeless case caused by the source's non-strict
event.

**Book Exercise 6.15.** -/
theorem exercise_6_15 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V Ω : Type*} [Fintype V] [DecidableEq V]
        {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
        (G : SimpleGraph V),
        0 < graphEdgeCount G →
        ∀ (xi : V → Ω → ℝ),
        (∀ v, HDP.IsRademacher (xi v) P) → iIndepFun xi P →
        ∀ {s : ℝ}, 1 ≤ s →
        P.real {ω |
          |HDP.SimpleGraph.cutValue G {v | 0 ≤ xi v ω} -
              (graphEdgeCount G : ℝ) / 2| ≥
            s * Real.sqrt (graphEdgeCount G)} ≤
          2 * Real.exp (-c * s) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.15.
  sorry

end HDP.Chapter6.Exercise
