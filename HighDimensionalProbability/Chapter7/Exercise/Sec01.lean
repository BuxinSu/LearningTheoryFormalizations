import HighDimensionalProbability.Chapter6.Main

/-!
# Book Chapter 7 exercises attached to Section 7.1

Only the non-load-bearing proof payloads live here.  Exercise 7.1(a) and
Exercise 7.3 are used by the main development and belong to Chapter 7 core.
Exercise 7.1(c) and Exercise 7.5 are concrete counterexample/construction
tasks and are omitted under the non-proof policy.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HDP.Chapter7.Exercise

/-- The squared canonical `L²` increment, written directly as a real integral.

**Lean implementation helper.** -/
def processDistSq {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : T → Ω → ℝ) (t s : T) (mu : Measure Ω) : ℝ :=
  ∫ ω, (X t ω - X s ω) ^ 2 ∂mu

/-- The covariance function is `E[X_t X_s]` for centered processes.

**Book Section 7.1.1, covariance display.** -/
def processCovariance {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : T → Ω → ℝ) (t s : T) (mu : Measure Ω) : ℝ :=
  ∫ ω, X t ω * X s ω ∂mu

/-- **Exercise 7.1(b).** If the process is closed under negation, covariance
is recovered from its canonical metric by polarization. Almost-everywhere
equality is the appropriate random-variable equality.

**Book Exercise 7.1(b).** -/
theorem exercise_7_1b {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    {mu : Measure Ω} (X : T → Ω → ℝ) (negIndex : T → T)
    (_hneg : ∀ s, X (negIndex s) =ᵐ[mu] fun ω => -X s ω)
    (_hcenter : ∀ t, ∫ ω, X t ω ∂mu = 0)
    (_hsq : ∀ t, Integrable (fun ω => X t ω ^ 2) mu)
    (t s : T) :
    4 * processCovariance X t s mu =
      processDistSq X t (negIndex s) mu - processDistSq X t s mu := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.1(b).
  sorry

/-- Maximum absolute value of a finite restriction of a random process.

**Lean implementation helper.** -/
def finiteProcessMaxAbs {I Ω : Type*} (S : Finset I) (hS : S.Nonempty)
    (Y : I → Ω → ℝ) (ω : Ω) : ℝ :=
  S.sup' hS fun t => |Y t ω|

/-- **Exercise 7.2, corrected from the conversion.** The authoritative PDF
has absolute values around all three process suprema. The finite restriction
is the source's stated convention for avoiding measurability pathologies.

**Book Exercise 7.2.** -/
theorem exercise_7_2 {I Ω : Type*} {mΩ : MeasurableSpace Ω}
    {mu : Measure Ω} [IsProbabilityMeasure mu] {N : ℕ}
    (S : Finset I) (hS : S.Nonempty) (X : Fin N → I → Ω → ℝ)
    (eps : Fin N → Ω → ℝ)
    (_hcenter : ∀ i t, ∫ ω, X i t ω ∂mu = 0)
    (_hprocInd : iIndepFun (fun i ω t => X i t ω) mu)
    (_hrad : ∀ i, HDP.IsRademacher (eps i) mu)
    (_hepsInd : iIndepFun eps mu)
    (_hjoint : IndepFun (fun ω i => eps i ω)
      (fun ω i t => X i t ω) mu)
    (_hintSym : Integrable (fun ω => finiteProcessMaxAbs S hS
      (fun t ω => ∑ i, eps i ω * X i t ω) ω) mu)
    (_hintSum : Integrable (fun ω => finiteProcessMaxAbs S hS
      (fun t ω => ∑ i, X i t ω) ω) mu) :
    (1 / 2 : ℝ) *
        (∫ ω, finiteProcessMaxAbs S hS
          (fun t ω => ∑ i, eps i ω * X i t ω) ω ∂mu) ≤
      ∫ ω, finiteProcessMaxAbs S hS
        (fun t ω => ∑ i, X i t ω) ω ∂mu ∧
    (∫ ω, finiteProcessMaxAbs S hS
        (fun t ω => ∑ i, X i t ω) ω ∂mu) ≤
      2 * ∫ ω, finiteProcessMaxAbs S hS
        (fun t ω => ∑ i, eps i ω * X i t ω) ω ∂mu := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.2.
  sorry

/-- The supremum of a real function on a nonempty finite set.

**Lean implementation helper.** -/
def finiteSetSup {A Ω : Type*} (S : Finset A) (hS : S.Nonempty)
    (F : A → Ω → ℝ) (ω : Ω) : ℝ :=
  S.sup' hS fun x => F x ω

/-- **Exercise 7.4.** General Talagrand contraction with an arbitrary common
Lipschitz bound. The source's unrestricted coordinate norms are captured by
taking their finite maximum as `L`.

**Book Exercise 7.4.** -/
theorem exercise_7_4 {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu] {n : ℕ}
    (S : Finset (Fin n → ℝ)) (hS : S.Nonempty)
    (phi : Fin n → ℝ → ℝ) (L : ℝ≥0)
    (_hLip : ∀ i, LipschitzWith L (phi i))
    (eps : Fin n → Omega → ℝ)
    (_hrad : ∀ i, HDP.IsRademacher (eps i) mu)
    (_hind : iIndepFun eps mu)
    (_hintLeft : Integrable (fun omega => finiteSetSup S hS
      (fun t omega => ∑ i, eps i omega * phi i (t i)) omega) mu)
    (_hintRight : Integrable (fun omega => finiteSetSup S hS
      (fun t omega => ∑ i, eps i omega * t i) omega) mu) :
    (∫ omega, finiteSetSup S hS
      (fun t omega => ∑ i, eps i omega * phi i (t i)) omega ∂mu) ≤
      (L : ℝ) * ∫ omega, finiteSetSup S hS
        (fun t omega => ∑ i, eps i omega * t i) omega ∂mu := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.4.
  sorry

end HDP.Chapter7.Exercise
