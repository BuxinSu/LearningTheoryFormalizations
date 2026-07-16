import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Pareto

/-!
# Book Chapter 2 exercises for Section 2.6

Exercises 2.22--2.24 are used by the Chapter 2 core or later chapters. Their
authoritative declarations live in `01_GaussianTails.lean` and
`08_SubGaussianNorm.lean`, and are not duplicated here. The declarations tagged
`EXERCISE-SORRY` below are category-A leaf results: their statements are
retained exactly, but no core module imports this file.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal unitInterval Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- EXERCISE-SORRY (category A): Exercise 2.25 is not load-bearing. -/
/-- The standard exponential, nondegenerate Poisson and
geometric, chi-squared/Gamma, nondegenerate Cauchy, and Pareto laws are not
subgaussian. Chi-squared with `k` degrees of freedom is represented as
`Gamma(k/2, 1/2)` in Mathlib's rate parametrization.

**Book Exercise 2.25.** -/
theorem exercise_2_25 :
    (∀ r : ℝ, 0 < r →
      ¬ HDP.SubGaussian (fun x : ℝ => x) (expMeasure r)) ∧
    (∀ r : ℝ≥0, 0 < r →
      ¬ HDP.SubGaussian (fun n : ℕ => (n : ℝ)) (poissonMeasure r)) ∧
    (∀ p : I, 0 < (p : ℝ) → (p : ℝ) < 1 →
      ¬ HDP.SubGaussian (fun n : ℕ => (n : ℝ)) (geometricMeasure p)) ∧
    (∀ k : ℝ, 0 < k →
      ¬ HDP.SubGaussian (fun x : ℝ => x) (gammaMeasure (k / 2) (1 / 2))) ∧
    (∀ a r : ℝ, 0 < a → 0 < r →
      ¬ HDP.SubGaussian (fun x : ℝ => x) (gammaMeasure a r)) ∧
    (∀ x₀ : ℝ, ∀ γ : ℝ≥0, 0 < γ →
      ¬ HDP.SubGaussian (fun x : ℝ => x) (cauchyMeasure x₀ γ)) ∧
    (∀ t r : ℝ, 0 < t → 0 < r →
      ¬ HDP.SubGaussian (fun x : ℝ => x) (paretoMeasure t r)) := by
  sorry

/-- `SquareMGFBound X μ K` asserts the prescribed exponential-moment bound
for `X²` whenever `|λ| ≤ 1/K`.

**Book Exercise 2.26.** -/
def SquareMGFBound (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  ∀ lam : ℝ, |lam| ≤ 1 / K →
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam ^ 2 * X ω ^ 2)) ∂μ ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * K ^ 2))

/- EXERCISE-SORRY (category A): Exercise 2.26 is not load-bearing. -/
/-- A measurable subgaussian variable satisfies the square-MGF bound with
`K` equal to its `ψ₂` norm.

**Book Exercise 2.26.** -/
theorem exercise_2_26_forward [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : HDP.SubGaussian X μ) :
    SquareMGFBound X μ (HDP.psi2Norm X μ) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.26 is not load-bearing. -/
/-- A square-MGF bound at a positive scale `K` implies subgaussianity and
the quantitative estimate `‖X‖ψ₂ ≤ 2K`.

**Book Exercise 2.26.** -/
theorem exercise_2_26_converse [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hK : 0 < K) (h : SquareMGFBound X μ K) :
    HDP.SubGaussian X μ ∧ HDP.psi2Norm X μ ≤ 2 * K := by
  sorry

/-- `AlmostStochDominated X μ Y ν` means that every upper tail of `X` is at
most twice the corresponding upper tail of `Y`.

**Book Exercise 2.27.** -/
def AlmostStochDominated {Ω' : Type*} [MeasurableSpace Ω']
    (X : Ω → ℝ) (μ : Measure Ω) (Y : Ω' → ℝ) (ν : Measure Ω') : Prop :=
  ∀ t : ℝ, μ.real {ω | t ≤ X ω} ≤ 2 * ν.real {ω | t ≤ Y ω}

/- EXERCISE-SORRY (category A): Exercise 2.27(a) is not load-bearing. -/
/-- Subgaussianity is equivalent, up to one universal constant, to almost
stochastic domination of `|X|` by a scaled absolute standard Gaussian.

**Book Exercise 2.27(a).** -/
theorem exercise_2_27a :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ},
        AEMeasurable X μ → HDP.SubGaussian X μ →
        ∃ K : ℝ, 0 < K ∧ K ≤ C * HDP.psi2Norm X μ ∧
          AlmostStochDominated (fun ω => |X ω|) μ
            (fun g : ℝ => K * |g|) (gaussianReal 0 1)) ∧
      (∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ},
        0 < K → AlmostStochDominated (fun ω => |X ω|) μ
          (fun g : ℝ => K * |g|) (gaussianReal 0 1) →
        HDP.SubGaussian X μ ∧ HDP.psi2Norm X μ ≤ C * K) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.27(b) is not load-bearing. -/
/-- The factor `2` in almost stochastic domination cannot be replaced by `1`:
the constant random variable `1` is not tail-dominated by any scaled absolute
standard Gaussian.

**Book Exercise 2.27(b).** -/
theorem exercise_2_27b :
    ¬ ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      (Measure.dirac (1 : ℝ)).real {x | t ≤ |x|} ≤
        (gaussianReal 0 1).real {g | t ≤ K * |g|} := by
  sorry

/-- Convex increasing dominance from Exercise 2.28. Integrability is made
explicit so both real expectations have their intended meaning.

**Book Exercise 2.28.** -/
def ConvexIncreasingDominated {Ω' : Type*} [MeasurableSpace Ω']
    (X : Ω → ℝ) (μ : Measure Ω) (Y : Ω' → ℝ) (ν : Measure Ω') : Prop :=
  ∀ Φ : ℝ → ℝ, ConvexOn ℝ Set.univ Φ → Monotone Φ →
    Integrable (Φ ∘ X) μ → Integrable (Φ ∘ Y) ν →
      ∫ ω, Φ (X ω) ∂μ ≤ ∫ ω, Φ (Y ω) ∂ν

/- EXERCISE-SORRY (category A): Exercise 2.28 is not load-bearing. -/
/-- Subgaussianity is equivalent, up to one universal constant, to domination
of `|X|` by a scaled absolute Gaussian against every convex increasing test
function with integrable expectations.

**Book Exercise 2.28.** -/
theorem exercise_2_28 :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ},
        AEMeasurable X μ → HDP.SubGaussian X μ →
        ∃ K : ℝ, 0 < K ∧ K ≤ C * HDP.psi2Norm X μ ∧
          ConvexIncreasingDominated (fun ω => |X ω|) μ
            (fun g : ℝ => K * |g|) (gaussianReal 0 1)) ∧
      (∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
          [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ},
        0 < K → ConvexIncreasingDominated (fun ω => |X ω|) μ
          (fun g : ℝ => K * |g|) (gaussianReal 0 1) →
        HDP.SubGaussian X μ ∧ HDP.psi2Norm X μ ≤ C * K) := by
  sorry

/- Exercise 2.29 is non-load-bearing but is proved as a direct wrapper over
the bounded Hoeffding theorem. -/
/-- The subgaussian Hoeffding theorem recovers a bounded
Hoeffding estimate, with an absolute constant in the exponent.

**Book Exercise 2.29.** -/
theorem exercise_2_29 [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} {a b : Fin N → ℝ}
    (hm : ∀ i, AEMeasurable (X i) μ)
    (hab : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hindep : iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂μ)} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) :=
  hoeffding_bounded hm hab hindep ht

/- EXERCISE-SORRY (category A): Exercise 2.30 is not load-bearing. -/
/-- A normalized weighted sum of independent, centered, variance-one
subgaussian variables exceeds half its coefficient `ℓ²` norm with probability
at least `1 / (10000 K⁴)`.

**Book Exercise 2.30.** -/
theorem exercise_2_30 [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKmax : ∀ i, HDP.psi2Norm (X i) μ ≤ K) (a : Fin N → ℝ) :
    1 / (10000 * K ^ 4) ≤
      μ.real {ω | (1 / 2 : ℝ) * Real.sqrt (∑ i, a i ^ 2) ≤
        |∑ i, a i * X i ω|} := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.31 is not load-bearing. -/
/-- An i.i.d. family satisfying a uniform Hoeffding-like
bound has zero mean.

**Book Exercise 2.31.** -/
theorem exercise_2_31 [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {c : ℝ} (hc : 0 < c)
    (hhoeffding : ∀ (N : ℕ) (a : Fin N → ℝ) (t : ℝ), 0 ≤ t →
      μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
        2 * Real.exp (-c * t ^ 2 / ∑ i, a i ^ 2)) :
    ∫ ω, X 0 ω ∂μ = 0 := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.32 is not load-bearing. -/
/-- The `ψ₂` norm of the sum of two independent centered subgaussian variables
is comparable, with explicit constants, to the sum of their individual
`ψ₂` norms.

**Book Exercise 2.32.** -/
theorem exercise_2_32 [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : HDP.SubGaussian X μ) (hY : HDP.SubGaussian Y μ)
    (hXmean : ∫ ω, X ω ∂μ = 0) (hYmean : ∫ ω, Y ω ∂μ = 0)
    (hindep : IndepFun X Y μ) :
    (1 / 10 : ℝ) * (HDP.psi2Norm X μ + HDP.psi2Norm Y μ) ≤
        HDP.psi2Norm (fun ω => X ω + Y ω) μ ∧
      HDP.psi2Norm (fun ω => X ω + Y ω) μ ≤
        Real.sqrt 30 * (HDP.psi2Norm X μ + HDP.psi2Norm Y μ) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.33 is not load-bearing. -/
/-- The `ψ₂` norm of a sum of `N` independent copies of a centered
subgaussian variable is comparable to `√N` times the common `ψ₂` norm.

**Book Exercise 2.33(a).** -/
theorem exercise_2_33a [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X₀ : Ω → ℝ} {X : Fin N → Ω → ℝ}
    (hXm : AEMeasurable X₀ μ) (hX : HDP.SubGaussian X₀ μ)
    (hmean : ∫ ω, X₀ ω ∂μ = 0)
    (hident : ∀ i, IdentDistrib (X i) X₀ μ μ)
    (hindep : iIndepFun X μ) :
    (1 / 10 : ℝ) * Real.sqrt N * HDP.psi2Norm X₀ μ ≤
        HDP.psi2Norm (fun ω => ∑ i, X i ω) μ ∧
      HDP.psi2Norm (fun ω => ∑ i, X i ω) μ ≤
        10 * Real.sqrt N * HDP.psi2Norm X₀ μ := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.33 is not load-bearing. -/
/-- The `ψ₂` norm of a centered `Binomial(N,p)` sum is comparable to
`√(N / log(2/p))`, with explicit constants.

**Book Exercise 2.33(b).** -/
theorem exercise_2_33b {N : ℕ} (hN : 0 < N) {p : I} (hp : 0 < (p : ℝ))
    {X : Fin N → Ω → ℝ} (hX : ∀ i, HDP.IsBernoulli (X i) p μ)
    (hindep : iIndepFun X μ) :
    (1 / 10 : ℝ) * Real.sqrt
        (N / Real.log (2 / (p : ℝ))) ≤
      HDP.psi2Norm (fun ω => ∑ i, X i ω - N * (p : ℝ)) μ ∧
    HDP.psi2Norm (fun ω => ∑ i, X i ω - N * (p : ℝ)) μ ≤
      10 * Real.sqrt (N / Real.log (2 / (p : ℝ))) := by
  sorry

/- Book Exercise 2.34 is a counterexample/construction task rather than a
proof-question exercise.  It is intentionally skipped under the exercise policy;
the reason is recorded in the chapter inventory. -/

end HDP.Chapter2
