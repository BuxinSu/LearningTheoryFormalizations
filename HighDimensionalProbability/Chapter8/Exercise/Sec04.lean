/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter8_Chaining
import Mathlib.Data.Finset.SymmDiff

/-!
# Book Chapter 8 exercises attached to Section 8.4

Exercise 8.29 is promoted into Chapter 8 core and is not redeclared here.
The remaining declarations expose the source's random-label extension,
Lipschitz regression bound, and finite shattered-set obstruction to learning.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal symmDiff Topology

namespace HDP.Chapter8.Exercise

noncomputable section

/-! ## Exercise 8.30: random labels -/

/-- Squared loss evaluated on a labeled example `(x,y)`.

**Lean implementation helper.** -/
def labeledSquaredLoss {α : Type*} (hypothesis : α → ℝ)
    (z : α × ℝ) : ℝ :=
  (hypothesis z.1 - z.2) ^ 2

/-- Population risk for genuinely random labels.

**Lean implementation helper.** -/
def labeledPopulationRisk {α : Type*} {mα : MeasurableSpace α}
    (ν : Measure (α × ℝ)) (hypothesis : α → ℝ) : ℝ :=
  ∫ z, labeledSquaredLoss hypothesis z ∂ν

/-- Empirical risk for a labeled sample.

**Lean implementation helper.** -/
def labeledEmpiricalRisk {α : Type*} {n : ℕ}
    (sample : Fin n → α × ℝ) (hypothesis : α → ℝ) : ℝ :=
  empiricalAverage sample (labeledSquaredLoss hypothesis)

/-- Empirical-minus-population risk vector for a finite hypothesis class.

**Lean implementation helper.** -/
def labeledRiskDeviationVector {α : Type*} {mα : MeasurableSpace α}
    {n : ℕ} (F : Finset (α → ℝ)) (ν : Measure (α × ℝ))
    (sample : Fin n → α × ℝ) : ↥F → ℝ :=
  fun f => labeledEmpiricalRisk sample f.1 - labeledPopulationRisk ν f.1

/-- Finite uniform labeled-risk deviation.

**Lean implementation helper.** -/
def labeledRiskUniformDeviation {α : Type*} {mα : MeasurableSpace α}
    {n : ℕ} (F : Finset (α → ℝ)) (ν : Measure (α × ℝ))
    (sample : Fin n → α × ℝ) : ℝ :=
  ‖labeledRiskDeviationVector F ν sample‖

/-- A finite empirical-risk minimizer for labeled observations.

**Lean implementation helper.** -/
def IsLabeledEmpiricalRiskMinimizer {α : Type*} {n : ℕ}
    (F : Finset (α → ℝ)) (sample : Fin n → α × ℝ)
    (learned : ↥F) : Prop :=
  IsFiniteMinimizer F (labeledEmpiricalRisk sample) learned

/-- A finite population-risk minimizer for a joint `(X,Y)` distribution.

**Lean implementation helper.** -/
def IsLabeledPopulationRiskMinimizer {α : Type*}
    {mα : MeasurableSpace α} (F : Finset (α → ℝ))
    (ν : Measure (α × ℝ)) (best : ↥F) : Prop :=
  IsFiniteMinimizer F (labeledPopulationRisk ν) best

/-- Uniform labeled-risk deviation over an arbitrary hypothesis class.

**Lean implementation helper.** -/
def labeledRiskUniformDeviationForClass {α : Type*}
    {mα : MeasurableSpace α} {n : ℕ} (F : Set (α → ℝ))
    (ν : Measure (α × ℝ)) (sample : Fin n → α × ℝ) : ℝ :=
  sSup (Set.range fun f : F =>
    |labeledEmpiricalRisk sample f.1 - labeledPopulationRisk ν f.1|)

/-- Empirical-risk minimality over an arbitrary class, with attainment made
explicit as required for the source's `argmin`.

**Lean implementation helper.** -/
def IsLabeledEmpiricalRiskMinimizerIn {α : Type*} {n : ℕ}
    (F : Set (α → ℝ)) (sample : Fin n → α × ℝ)
    (learned : α → ℝ) : Prop :=
  learned ∈ F ∧ ∀ f ∈ F,
    labeledEmpiricalRisk sample learned ≤ labeledEmpiricalRisk sample f

/-- Population-risk minimality over an arbitrary class, again with an
explicit attained minimizer.

**Lean implementation helper.** -/
def IsLabeledPopulationRiskMinimizerIn {α : Type*}
    {mα : MeasurableSpace α} (F : Set (α → ℝ))
    (ν : Measure (α × ℝ)) (best : α → ℝ) : Prop :=
  best ∈ F ∧ ∀ f ∈ F,
    labeledPopulationRisk ν best ≤ labeledPopulationRisk ν f

/-- **Exercise 8.30.** Expected generalization with genuinely random,
possibly noisy labels. The samples are independent copies of the joint law
`ν`, and the hypothesis class is not replaced by a finite surrogate. Since
the source allows arbitrary real labels, it does not imply a distribution-free
VC rate without an additional tail assumption; the universally valid
extension is the exact ERM/uniform-deviation inequality below.

**Book Exercise 8.30.** -/
theorem exercise_8_30_learning_with_random_labels
    {α Ω : Type*} {mα : MeasurableSpace α}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (F : Set (α → ℝ)) (ν : Measure (α × ℝ))
    [IsProbabilityMeasure ν]
    (Z : Fin n → Ω → α × ℝ) (learned : Ω → α → ℝ) (best : α → ℝ)
    (hZm : ∀ i, Measurable (Z i))
    (hLaw : ∀ i, HasLaw (Z i) ν P) (hInd : iIndepFun Z P)
    (hERM : ∀ ω, IsLabeledEmpiricalRiskMinimizerIn F
      (fun i => Z i ω) (learned ω))
    (hbest : IsLabeledPopulationRiskMinimizerIn F ν best)
    (hDevBdd : ∀ ω, BddAbove (Set.range fun f : F =>
      |labeledEmpiricalRisk (fun i => Z i ω) f.1 -
        labeledPopulationRisk ν f.1|))
    (hLearnedInt : Integrable
      (fun ω => labeledPopulationRisk ν (learned ω)) P)
    (hUniformInt : Integrable
      (fun ω => labeledRiskUniformDeviationForClass F ν
        (fun i => Z i ω)) P) :
    (∫ ω, labeledPopulationRisk ν (learned ω) ∂P) ≤
      labeledPopulationRisk ν best +
        2 * ∫ ω, labeledRiskUniformDeviationForClass F ν
          (fun i => Z i ω) ∂P :=
  -- EXERCISE-SORRY: Exercise 8.30.
  by sorry

/-! ## Exercise 8.31: Lipschitz regression -/

/-- Uniform probability measure on `[0,1]`.

**Lean implementation helper.** -/
def unitIntervalProbability : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The finite hypotheses are restrictions of the source's unit-Lipschitz,
unit-range class.

**Lean implementation helper.** -/
def IsUnitIntervalLipschitzClass (F : Finset (ℝ → ℝ)) : Prop :=
  ∀ f : ↥F,
    LipschitzWith 1 f.1 ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, f.1 x ∈ Set.Icc (0 : ℝ) 1

/-- The full source hypothesis class of unit-Lipschitz maps `[0,1] → [0,1]`. -/
structure UnitIntervalLipschitzHypothesis where
  toFun : ℝ → ℝ
  lipschitz : LipschitzWith 1 toFun
  maps_unit_interval : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    toFun x ∈ Set.Icc (0 : ℝ) 1

instance : CoeFun UnitIntervalLipschitzHypothesis (fun _ => ℝ → ℝ) :=
  ⟨UnitIntervalLipschitzHypothesis.toFun⟩

/-- Empirical-risk minimality over the entire Lipschitz hypothesis class.

**Lean implementation helper.** -/
def IsFullLipschitzERM {n : ℕ} (sample : Fin n → ℝ)
    (target learned : UnitIntervalLipschitzHypothesis) : Prop :=
  ∀ f : UnitIntervalLipschitzHypothesis,
    empiricalRisk sample target.toFun learned.toFun ≤
      empiricalRisk sample target.toFun f.toFun

/-- Population-risk minimality over the entire Lipschitz hypothesis class.

**Lean implementation helper.** -/
def IsFullLipschitzPopulationMinimizer
    (target best : UnitIntervalLipschitzHypothesis) : Prop :=
  ∀ f : UnitIntervalLipschitzHypothesis,
    populationRisk unitIntervalProbability target.toFun best.toFun ≤
      populationRisk unitIntervalProbability target.toFun f.toFun

/-- **Exercise 8.31.** Generalization for empirical-risk minimization over the
full class of unit-Lipschitz `[0,1] → [0,1]` functions.

**Book Exercise 8.31.** -/
theorem exercise_8_31_learning_lipschitz_function :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (target learnedBest : UnitIntervalLipschitzHypothesis)
        (learned : Ω → UnitIntervalLipschitzHypothesis)
        (X : Fin n → Ω → ℝ),
        0 < n →
        (∀ i, Measurable (X i)) →
        (∀ i, Measure.map (X i) P = unitIntervalProbability) →
        iIndepFun X P →
        (∀ ω, IsFullLipschitzERM (fun i => X i ω)
          target (learned ω)) →
        IsFullLipschitzPopulationMinimizer target learnedBest →
        Integrable (fun ω => populationRisk unitIntervalProbability
          target.toFun (learned ω).toFun) P →
        (∫ ω, populationRisk unitIntervalProbability
            target.toFun (learned ω).toFun ∂P) ≤
          populationRisk unitIntervalProbability target.toFun learnedBest.toFun +
            C / Real.sqrt n :=
  -- EXERCISE-SORRY: Exercise 8.31.
  by sorry

/-! ## Exercise 8.32: infinite VC dimension obstructs learning -/

/-- A deterministic Boolean learning rule from sample locations and labels. -/
abbrev BooleanLearningRule (α : Type*) (n : ℕ) :=
  (Fin n → α) → (Fin n → Bool) → Set α

/-- Labels induced on a finite sample by an arbitrary target support.

**Lean implementation helper.** -/
noncomputable def supportLabels {α : Type*} {n : ℕ}
    (target : Set α) (sample : Fin n → α) : Fin n → Bool := by
  classical
  exact fun i => decide (sample i ∈ target)

/-- **Exercise 8.32.** If the sample size is less than half the VC dimension,
every deterministic learning rule has constant expected risk for some target
and some iid input distribution.

**Book Exercise 8.32.** -/
theorem exercise_8_32_no_learning_below_vc_dimension
    {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {n : ℕ} (F : HDP.BooleanClass α) (hvc : ¬ F.VCDimLE (2 * n))
    (learner : BooleanLearningRule α n) :
    ∃ μ : Measure α, ∃ P : Measure (Fin n → α), ∃ target : Set α,
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure P ∧ target ∈ F ∧
      (∀ i, Measure.map (fun sample => sample i) P = μ) ∧
      iIndepFun (fun i sample => sample i) P ∧
      (1 / 8 : ℝ) ≤
        ∫ sample, μ.real (target ∆
          learner sample (supportLabels target sample)) ∂P :=
  -- EXERCISE-SORRY: Exercise 8.32.
  by sorry

end

end HDP.Chapter8.Exercise
