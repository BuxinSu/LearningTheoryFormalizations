import HighDimensionalProbability.Chapter6_QuadraticFormsSymmetrizationContraction

/-!
# Chapter 6 exercises attached to Section 6.3

Exercise 6.16 is load-bearing and belongs to core.  Exercise 6.17 is a pair of
concrete distribution computations and is omitted under the non-proof policy.
Only the proof-bearing, non-load-bearing symmetrization and type exercises live
in this leaf module.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HDP.Chapter6.Exercise

/-- A signed finite sum of vectors.

**Lean implementation helper.** -/
def signedVectorSum {Ω E : Type*} {N : ℕ} [AddCommMonoid E] [Module ℝ E]
    (eps : Fin N → Ω → ℝ) (X : Fin N → Ω → E) (ω : Ω) : E :=
  ∑ i, eps i ω • X i ω

/-- The ordinary finite sum of random vectors.

**Lean implementation helper.** -/
def randomVectorSum {Ω E : Type*} {N : ℕ} [AddCommMonoid E]
    (X : Fin N → Ω → E) (ω : Ω) : E :=
  ∑ i, X i ω

/-- The centered sum used in the corresponding exercise.

**Lean implementation helper.** -/
def centeredVectorSum {Ω E : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin N → Ω → E) (μ : Measure Ω) (ω : Ω) : E :=
  ∑ i, X i ω - ∑ i, ∫ ω', X i ω' ∂μ

/-- A weighted barycenter of finitely many coordinate vectors.

**Lean implementation helper.** -/
def weightedBarycenter {M n : ℕ} (a : Fin M → ℝ)
    (x : Fin M → Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, a i * x i j

/-- The equal-weight average of a finite sampled list.

**Lean implementation helper.** -/
def sampledAverage {M N n : ℕ} (I : Fin N → Fin M)
    (x : Fin M → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (N : ℝ)⁻¹ * ∑ k, x (I k) j

/-- Compares the expected norm of a symmetric random vector shifted by a fixed vector, with
explicit constants.

**Book Exercise 6.18.** -/
theorem exercise_6_18 {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (X : Ω → E) (hX : Integrable X μ)
    (_hsym : IdentDistrib X (fun ω => -X ω) μ μ) (v : E) :
    (1 / 2 : ℝ) * ((∫ ω, ‖X ω‖ ∂μ) + ‖v‖) ≤
        ∫ ω, ‖X ω + v‖ ∂μ ∧
      (∫ ω, ‖X ω + v‖ ∂μ) ≤ (∫ ω, ‖X ω‖ ∂μ) + ‖v‖ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.18.
  sorry

/-- Symmetrization without the zero-mean assumption. The counterexample requested in part (b) is
a non-proof subtask and is omitted.

**Book Exercise 6.19(a).** -/
theorem exercise_6_19a {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (X : Fin N → Ω → E) (eps : Fin N → Ω → ℝ)
    (_hXint : ∀ i, Integrable (X i) μ) (_hXind : iIndepFun X μ)
    (_hrad : ∀ i, HDP.IsRademacher (eps i) μ)
    (_hepsInd : iIndepFun eps μ)
    (_hjoint : IndepFun (fun ω i => X i ω) (fun ω i => eps i ω) μ) :
    (∫ ω, ‖centeredVectorSum X μ ω‖ ∂μ) ≤
      2 * ∫ ω, ‖signedVectorSum eps X ω‖ ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.19(a).
  sorry

/-- Symmetrization through an increasing convex function of the norm.

**Book Exercise 6.20.** -/
theorem exercise_6_20 {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (X : Fin N → Ω → E) (eps : Fin N → Ω → ℝ)
    (_hXint : ∀ i, Integrable (X i) μ) (_hXind : iIndepFun X μ)
    (_hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (_hrad : ∀ i, HDP.IsRademacher (eps i) μ)
    (_hepsInd : iIndepFun eps μ)
    (_hjoint : IndepFun (fun ω i => X i ω) (fun ω i => eps i ω) μ)
    (F : ℝ → ℝ) (_hmono : MonotoneOn F (Set.Ici 0))
    (_hconv : ConvexOn ℝ (Set.Ici 0) F)
    (_hintLeft : Integrable
      (fun ω => F ((1 / 2 : ℝ) * ‖signedVectorSum eps X ω‖)) μ)
    (_hintMid : Integrable (fun ω => F ‖randomVectorSum X ω‖) μ)
    (_hintRight : Integrable
      (fun ω => F (2 * ‖signedVectorSum eps X ω‖)) μ) :
    (∫ ω, F ((1 / 2 : ℝ) * ‖signedVectorSum eps X ω‖) ∂μ) ≤
        ∫ ω, F ‖randomVectorSum X ω‖ ∂μ ∧
      (∫ ω, F ‖randomVectorSum X ω‖ ∂μ) ≤
        ∫ ω, F (2 * ‖signedVectorSum eps X ω‖) ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.20.
  sorry

/-- A sum is subgaussian exactly when its Rademacher symmetrization is, with comparable `ψ₂`
norms.

**Book Exercise 6.21.** -/
theorem exercise_6_21 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {N : ℕ}
        (X eps : Fin N → Ω → ℝ),
        (∀ i, AEMeasurable (X i) μ) → iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, HDP.IsRademacher (eps i) μ) → iIndepFun eps μ →
        IndepFun (fun ω i => X i ω) (fun ω i => eps i ω) μ →
        (HDP.SubGaussian (randomVectorSum X) μ ↔
          HDP.SubGaussian (fun ω => ∑ i, eps i ω * X i ω) μ) ∧
        c * HDP.psi2Norm (fun ω => ∑ i, eps i ω * X i ω) μ ≤
            HDP.psi2Norm (randomVectorSum X) μ ∧
          HDP.psi2Norm (randomVectorSum X) μ ≤
            C * HDP.psi2Norm (fun ω => ∑ i, eps i ω * X i ω) μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.21.
  sorry

/-- Strict inequality avoids the false all-zero case in the printed non-strict event.

**Book Exercise 6.22.** -/
theorem exercise_6_22 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    (X : Fin N → Ω → ℝ) (_hXm : ∀ i, AEMeasurable (X i) μ)
    (_hind : iIndepFun X μ)
    (_hsym : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    {t : ℝ} (_ht : 0 < t) :
    μ.real {ω | |∑ i, X i ω| >
      t * Real.sqrt (∑ i, X i ω ^ 2)} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.22.
  sorry

/-- `ℓᵖ` has Rademacher type `p` for `1 ≤ p ≤ 2`.

**Book Exercise 6.23(a).** -/
theorem exercise_6_23a {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N n : ℕ}
    (eps : Fin N → Ω → ℝ) (_hrad : ∀ i, HDP.IsRademacher (eps i) μ)
    (_hind : iIndepFun eps μ) (x : Fin N → Fin n → ℝ)
    {p : ℝ} (_hp1 : 1 ≤ p) (_hp2 : p ≤ 2) :
    (∫ ω, HDP.Chapter1.lpNorm p
      (fun j => ∑ i, eps i ω * x i j) ^ p ∂μ) ≤
      ∑ i, HDP.Chapter1.lpNorm p (x i) ^ p := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.23(a).
  sorry

/-- The independent centered random-vector form of type `p`. Symmetrization contributes the
factor `2^p`; the printed constant-one version is false in general.

**Book Exercise 6.23(b).** -/
theorem exercise_6_23b {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N n : ℕ}
    (X : Fin N → Ω → (Fin n → ℝ))
    (_hXm : ∀ i j, AEMeasurable (fun ω => X i ω j) μ)
    (_hind : iIndepFun X μ)
    (_hmean : ∀ i j, ∫ ω, X i ω j ∂μ = 0)
    {p : ℝ} (_hp1 : 1 ≤ p) (_hp2 : p ≤ 2)
    (_hint : ∀ i, Integrable
      (fun ω => HDP.Chapter1.lpNorm p (X i ω) ^ p) μ) :
    (∫ ω, HDP.Chapter1.lpNorm p
      (fun j => ∑ i, X i ω j) ^ p ∂μ) ≤
      Real.rpow 2 p *
        ∑ i, ∫ ω, HDP.Chapter1.lpNorm p (X i ω) ^ p ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.23(b).
  sorry

/-- `ℓᵖ` has Rademacher type `2` with constant of order `sqrt p`.

**Book Exercise 6.24(a).** -/
theorem exercise_6_24a :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {N n : ℕ}
        (eps : Fin N → Ω → ℝ),
        (∀ i, HDP.IsRademacher (eps i) μ) → iIndepFun eps μ →
        ∀ (x : Fin N → Fin n → ℝ) {p : ℝ}, 2 ≤ p →
        (∫ ω, HDP.Chapter1.lpNorm p
          (fun j => ∑ i, eps i ω * x i j) ^ 2 ∂μ) ≤
          C * p * ∑ i, HDP.Chapter1.lpNorm p (x i) ^ 2 := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.24(a).
  sorry

/-- Independent centered random vectors inherit the type-`2` estimate.

**Book Exercise 6.24(b).** -/
theorem exercise_6_24b :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {N n : ℕ}
        (X : Fin N → Ω → (Fin n → ℝ)),
        (∀ i j, AEMeasurable (fun ω => X i ω j) μ) →
        iIndepFun X μ → (∀ i j, ∫ ω, X i ω j ∂μ = 0) →
        ∀ {p : ℝ}, 2 ≤ p →
        (∀ i, Integrable
          (fun ω => HDP.Chapter1.lpNorm p (X i ω) ^ 2) μ) →
        (∫ ω, HDP.Chapter1.lpNorm p
          (fun j => ∑ i, X i ω j) ^ 2 ∂μ) ≤
          C * p * ∑ i, ∫ ω, HDP.Chapter1.lpNorm p (X i ω) ^ 2 ∂μ := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.24(b).
  sorry

/-- The source's problematic `p=1` endpoint is separated: the dimension-free type estimate
starts at `p>1`.

**Book Exercise 6.25.** -/
theorem exercise_6_25 :
    ∃ C : ℝ, 0 < C ∧
      (∀ {M N n : ℕ} (hN : 0 < N) (a : Fin M → ℝ)
          (x : Fin M → Fin n → ℝ) {p R : ℝ},
          1 < p → p ≤ 2 → 0 ≤ R →
          (∀ i, 0 ≤ a i) → (∑ i, a i = 1) →
          (∀ i, HDP.Chapter1.lpNorm p
            (x i - weightedBarycenter a x) ≤ R) →
          ∃ I : Fin N → Fin M,
            HDP.Chapter1.lpNorm p
              (sampledAverage I x - weightedBarycenter a x) ≤
              C * R / Real.rpow N ((p - 1) / p)) ∧
        (∀ {M N n : ℕ} (hN : 0 < N) (a : Fin M → ℝ)
          (x : Fin M → Fin n → ℝ) {p R : ℝ},
          2 ≤ p → 0 ≤ R →
          (∀ i, 0 ≤ a i) → (∑ i, a i = 1) →
          (∀ i, HDP.Chapter1.lpNorm p
            (x i - weightedBarycenter a x) ≤ R) →
          ∃ I : Fin N → Fin M,
            HDP.Chapter1.lpNorm p
              (sampledAverage I x - weightedBarycenter a x) ≤
              C * Real.sqrt p * R / Real.sqrt N) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.25.
  sorry

/-- Marcinkiewicz--Zygmund inequality in the real-valued `L^p` wrapper, with the finiteness
assumptions required by that wrapper.

**Book Exercise 6.26.** -/
theorem exercise_6_26 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {N : ℕ}
        (X : Fin N → Ω → ℝ),
        iIndepFun X μ → (∀ i, ∫ ω, X i ω ∂μ = 0) →
        ∀ {p : ℝ}, 2 ≤ p →
        (∀ i, MemLp (X i) (ENNReal.ofReal p) μ) →
        HDP.Chapter1.lpNormRV (randomVectorSum X) p μ ^ 2 ≤
          C * p * ∑ i, HDP.Chapter1.lpNormRV (X i) p μ ^ 2 := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.26.
  sorry

/-- The printed statement omits coordinate independence, while its hint explicitly invokes
Marcinkiewicz--Zygmund for the centered squares.

**Book Exercise 6.27.** -/
theorem exercise_6_27 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {n : ℕ}
        (X : Fin n → Ω → ℝ),
        iIndepFun X μ → (∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) →
        ∀ {p K : ℝ}, 2 ≤ p → 0 ≤ K →
        (∀ i, MemLp (X i) (ENNReal.ofReal (2 * p)) μ) →
        (∀ i, HDP.Chapter1.lpNormRV (X i) (2 * p) μ ≤ K) →
        HDP.Chapter1.lpNormRV
          (fun ω => Real.sqrt (∑ i, X i ω ^ 2) - Real.sqrt n) p μ ≤
          C * Real.sqrt p * K ^ 2 := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 6.27.
  sorry

end HDP.Chapter6.Exercise
