import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums

/-!
# Book Chapter 2 exercises for Section 2.8

Exercises 2.41, 2.42, and 2.44(a) are absorbed into the core results they prove
or support; their authoritative declarations are not duplicated here. The
remaining non-load-bearing proof questions are exact category-A leaves and are
never imported by core modules.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Exercise 2.43 -/

/-- `PsiAlphaTailAt α X μ K` is the stretched-exponential tail bound
`P(|X| ≥ t) ≤ 2 exp(-(t/K)ᵅ)` for every `t ≥ 0`.

**Lean implementation helper.** -/
def PsiAlphaTailAt (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-((t / K) ^ α)))

/-- `PsiAlphaMomentAt α X μ K` bounds every moment of order `p ≥ 1` by
`(K p^(1/α))ᵖ`.

**Lean implementation helper.** -/
def PsiAlphaMomentAt (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ ∀ p : ℝ, 1 ≤ p →
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ ≤
      ENNReal.ofReal ((K * p ^ (1 / α)) ^ p)

/-- `PsiAlphaExpAt α X μ K` bounds the exponential moment of
`(|X|/K)ᵅ` by `2`.

**Lean implementation helper.** -/
def PsiAlphaExpAt (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ α)) ∂μ ≤ 2

/-- The `ψα` norm is the infimum of scales satisfying the corresponding
stretched-exponential moment bound.

**Lean implementation helper.** -/
noncomputable def psiAlphaNorm (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | PsiAlphaExpAt α X μ K}

/- EXERCISE-SORRY (category A): Exercise 2.43 is not load-bearing. -/
/-- For each `α > 0`, stretched-exponential tails, polynomial moment growth,
and the `ψα` exponential-moment condition imply one another up to a constant
depending only on `α`.

**Book Exercise 2.43.** -/
theorem exercise_2_43 (α : ℝ) (hα : 0 < α) :
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
        [IsProbabilityMeasure μ] {X : Ω → ℝ},
        AEMeasurable X μ →
        (∀ {K : ℝ}, PsiAlphaTailAt α X μ K →
          PsiAlphaMomentAt α X μ (Cα * K)) ∧
        (∀ {K : ℝ}, PsiAlphaMomentAt α X μ K →
          PsiAlphaExpAt α X μ (Cα * K)) ∧
        (∀ {K : ℝ}, PsiAlphaExpAt α X μ K →
          PsiAlphaTailAt α X μ (Cα * K)) := by
  sorry

/-! ## Exercise 2.44 (non-load-bearing parts) -/

/-- The pointwise maximum of the absolute values in a nonempty finite family
of random variables.

**Book Exercise 2.44(b).** -/
noncomputable def finiteMaxAbs {N : ℕ} [Nonempty (Fin N)]
    (X : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |X i ω|)

/- EXERCISE-SORRY (category A): Exercise 2.44(b) is not load-bearing. -/
/-- Independent copies of a subexponential variable have expected maximum
`O(‖X‖ψ₁ log N)`, and this logarithmic maximal bound conversely characterizes
subexponentiality, with one universal constant.

**Book Exercise 2.44(b).** -/
theorem exercise_2_44b :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
          [IsProbabilityMeasure μ] {N : ℕ} [Nonempty (Fin N)]
          (hN : 2 ≤ N) {X₀ : Ω → ℝ} {X : Fin N → Ω → ℝ},
        AEMeasurable X₀ μ → HDP.SubExponential X₀ μ →
        (∀ i, IdentDistrib (X i) X₀ μ μ) → iIndepFun X μ →
        Integrable (finiteMaxAbs X) μ ∧
          ∫ ω, finiteMaxAbs X ω ∂μ ≤
            C * HDP.psi1Norm X₀ μ * Real.log N) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X₀ : Ω → ℝ} {Y : ℕ → Ω → ℝ},
        AEMeasurable X₀ μ → (∀ i, IdentDistrib (Y i) X₀ μ μ) →
        iIndepFun Y μ → ∀ {K : ℝ}, 0 < K →
        (∀ (N : ℕ) (hN : 2 ≤ N),
          letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
          Integrable (finiteMaxAbs (fun i : Fin N => Y i)) μ ∧
            ∫ ω, finiteMaxAbs (fun i : Fin N => Y i) ω ∂μ ≤ K * Real.log N) →
        HDP.SubExponential X₀ μ ∧ HDP.psi1Norm X₀ μ ≤ C * K) := by
  sorry

/-- Convex-increasing domination by a scaled standard exponential random
variable, with all real expectations explicitly integrable.

**Lean implementation helper.** -/
def ExponentialConvexDominated (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  ∀ Φ : ℝ → ℝ, ConvexOn ℝ Set.univ Φ → Monotone Φ →
    Integrable (Φ ∘ X) μ →
    Integrable (Φ ∘ fun x : ℝ => K * x) (expMeasure 1) →
      ∫ ω, Φ (X ω) ∂μ ≤ ∫ x, Φ (K * x) ∂(expMeasure 1)

/- EXERCISE-SORRY (category A): Exercise 2.44(c) is not load-bearing. -/
/-- A random variable is subexponential if and only if its absolute value is
dominated, against every convex increasing test function, by a suitably scaled
standard exponential variable, with universal quantitative constants.

**Book Exercise 2.44(c).** -/
theorem exercise_2_44c :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ},
        AEMeasurable X μ → HDP.SubExponential X μ →
        ∃ K : ℝ, 0 < K ∧ K ≤ C * HDP.psi1Norm X μ ∧
          ExponentialConvexDominated (fun ω => |X ω|) μ K) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ},
        0 < K → ExponentialConvexDominated (fun ω => |X ω|) μ K →
        HDP.SubExponential X μ ∧ HDP.psi1Norm X μ ≤ C * K) := by
  sorry

end HDP.Chapter2
