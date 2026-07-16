/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter4_RandomMatrices
import HighDimensionalProbability.Prelude.RandomVector
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Probability.IdentDistribIndep
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import Mathlib.MeasureTheory.Integral.Prod
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.LinearAlgebra.Matrix.PosDef
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import HighDimensionalProbability.Prelude.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Chapter 6 — Quadratic Forms, Symmetrization and Contraction

## Contents

- §6.1 Decoupling — diagonal-free quadratic chaos and independent-copy
  bilinear forms (Theorem 6.1.1)
- §6.2 Hanson--Wright inequality — norm concentration (Proposition 6.2.1),
  Gaussian replacement (Lemmas 6.2.3--6.2.4), and the quadratic-form tail
  bound (Theorem 6.2.2)
- §6.3 Symmetrization — symmetric distributions (Lemma 6.3.1) and
  Rademacher symmetrization (Lemma 6.3.2)
- §6.4 Random matrices with non-i.i.d. entries — symmetric and rectangular
  expected-norm bounds (Theorem 6.4.1 and promoted exercises)
- §6.5 Matrix completion — deterministic recovery and Bernoulli sampling
  (Theorem 6.5.1)
- §6.6 Contraction principle — Rademacher contraction (Theorem 6.6.1) and
  Gaussian symmetrization (Lemma 6.6.2)

The detailed entries below identify the chapter's key source-facing definitions and
results by the numbering printed in the second-edition book PDF.
-/

/-! ## Material formerly in `01_QuadraticForms.lean` -/

section Source_01_QuadraticForms

/-!
# Chapter 6, §6.1: quadratic and bilinear forms

This file fixes the source-facing notation before decoupling.  The expectation
identity below makes the square-integrability hidden in the prose explicit.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

namespace HDP.Chapter6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The source's phrase “`X'` is an independent copy of `X`”, unpacked into equality of laws and
independence of the two random objects.

**Lean implementation helper.** -/
def IsIndependentCopy {E : Type*} [MeasurableSpace E]
    (X X' : Ω → E) (μ : Measure Ω) : Prop :=
  IdentDistrib X X' μ μ ∧ IndepFun X X' μ

namespace IsIndependentCopy

/-- Extracts equality in distribution from the independent-copy hypothesis.

**Lean implementation helper.** -/
theorem identDistrib {E : Type*} [MeasurableSpace E]
    {X X' : Ω → E} (h : IsIndependentCopy X X' μ) :
    IdentDistrib X X' μ μ := h.1

/-- Extracts independence from the independent-copy hypothesis.

**Lean implementation helper.** -/
theorem indepFun {E : Type*} [MeasurableSpace E]
    {X X' : Ω → E} (h : IsIndependentCopy X X' μ) :
    IndepFun X X' μ := h.2

/-- Reverses the order of an independent-copy pair.

**Lean implementation helper.** -/
theorem symm {E : Type*} [MeasurableSpace E]
    {X X' : Ω → E} (h : IsIndependentCopy X X' μ) :
    IsIndependentCopy X' X μ :=
  ⟨h.1.symm, h.2.symm⟩

end IsIndependentCopy

/-- Every diagonal entry vanishes.

**Lean implementation helper.** -/
def IsDiagonalFree {n : Type*} (A : Matrix n n ℝ) : Prop :=
  ∀ i, A i i = 0

/-- The finite quadratic form `xᵀ A x` used in (6.2).

**Book (6.2).** -/
def quadraticForm {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  HDP.Chapter4.matrixBilinear A x x

/-- The decoupled bilinear form `xᵀ A y`.

**Lean implementation helper.** -/
def bilinearForm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  HDP.Chapter4.matrixBilinear A x y

/-- Expands the quadratic form as a finite double sum.

**Lean implementation helper.** -/
@[simp] theorem quadraticForm_apply {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    quadraticForm A x = ∑ i, ∑ j, x i * A i j * x j := rfl

/-- Expands the bilinear form as a finite double sum.

**Lean implementation helper.** -/
@[simp] theorem bilinearForm_apply {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilinearForm A x y = ∑ i, ∑ j, x i * A i j * y j := rfl

/-- The off-diagonal part of a square matrix.

**Lean implementation helper.** -/
def offDiagonal {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => if i = j then 0 else A i j

/-- Shows that the off-diagonal part vanishes on the diagonal.

**Lean implementation helper.** -/
@[simp] theorem offDiagonal_apply_same {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) (i : n) : offDiagonal A i i = 0 := by
  simp [offDiagonal]

/-- Shows that the off-diagonal part agrees with the original matrix away from the diagonal.

**Lean implementation helper.** -/
@[simp] theorem offDiagonal_apply_ne {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) {i j : n} (hij : i ≠ j) :
    offDiagonal A i j = A i j := by
  simp [offDiagonal, hij]

/-- A matrix is diagonal-free exactly when it agrees with its off-diagonal part.

**Lean implementation helper.** -/
theorem offDiagonal_eq_self_iff {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) :
    offDiagonal A = A ↔ IsDiagonalFree A := by
  constructor
  · intro h i
    have hz : 0 = A i i := by
      simpa using congrFun (congrFun h i) i
    exact hz.symm
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j
      rw [offDiagonal_apply_same, h i]
    · simp [offDiagonal, hij]

/-- Expanded as a finite double sum.

**Book (6.2).** -/
theorem quadraticForm_eq_doubleSum {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    quadraticForm A x = ∑ i, ∑ j, A i j * x i * x j := by
  simp only [quadraticForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Implicit assertion after (6.2): independent centered coordinates have no off-diagonal
contribution to the expected quadratic form.

**Book (6.2).** -/
theorem integral_quadraticForm_eq_diagonal
    [IsProbabilityMeasure μ]
    {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (X : n → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    ∫ ω, quadraticForm A (fun i => X i ω) ∂μ =
      ∑ i, A i i * ∫ ω, (X i ω) ^ 2 ∂μ := by
  classical
  have hterm : ∀ i j, Integrable (fun ω => X i ω * A i j * X j ω) μ := by
    intro i j
    have hp : Integrable (fun ω => X i ω * X j ω) μ :=
      (hX i).integrable_mul (hX j)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hp.const_mul (A i j)
  simp only [quadraticForm_apply]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ]
    · rw [Finset.sum_eq_single i]
      · rw [show (fun ω => X i ω * A i i * X i ω) =
            fun ω => A i i * (X i ω) ^ 2 by
              funext ω; ring,
          integral_const_mul]
      · intro j _ hji
        have hij : i ≠ j := Ne.symm hji
        have hfactor := (hindep.indepFun hij).integral_mul_eq_mul_integral
          (hX i).aestronglyMeasurable (hX j).aestronglyMeasurable
        have hfactor' : (∫ ω, X i ω * X j ω ∂μ) =
            (∫ ω, X i ω ∂μ) * ∫ ω, X j ω ∂μ := by
          simpa only [Pi.mul_apply] using hfactor
        rw [show (fun ω => X i ω * A i j * X j ω) =
              fun ω => A i j * (X i ω * X j ω) by
                funext ω; ring,
            integral_const_mul, hfactor', hmean i, hmean j]
        simp
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · intro j _
      exact hterm i j
  · intro i _
    exact integrable_finsetSum Finset.univ (fun j _ => hterm i j)

/-- The expectation computation displayed after (6.2): for centered, independent,
unit-second-moment coordinates, `𝔼[XᵀAX] = tr A`.

**Book (6.2).** -/
theorem integral_quadraticForm_eq_trace
    [IsProbabilityMeasure μ]
    {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (X : n → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsecond : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1) :
    ∫ ω, quadraticForm A (fun i => X i ω) ∂μ = Matrix.trace A := by
  classical
  rw [integral_quadraticForm_eq_diagonal A X hX hindep hmean]
  simp [Matrix.trace, hsecond]

end HDP.Chapter6

end Source_01_QuadraticForms

/-! ## Material formerly in `02_Decoupling.lean` -/

section Source_02_Decoupling

/-!
# Chapter 6, §6.1: decoupling

The finite selector layer is kept explicit.  This makes the factor `4` in the
book's proof independently checkable, rather than hiding it in probability
notation.
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators ENNReal

namespace HDP.Chapter6

noncomputable section

/-- The `0/1` value of a selector.

**Lean implementation helper.** -/
def selectorValue {n : ℕ} (δ : Fin n → Bool) (i : Fin n) : ℝ :=
  if δ i then 1 else 0

/-- The partial chaos selected by `I = {i | δ i = true}`.

**Lean implementation helper.** -/
def partialChaos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (δ : Fin n → Bool) : ℝ :=
  ∑ i, ∑ j, selectorValue δ i * (1 - selectorValue δ j) *
    A i j * x i * x j

/-- Pairing two independent coordinate families on a product probability space produces an independent family of pairs.

**Lean implementation helper.** -/
private theorem iIndepFun_prodMk_prod_decoupling
    {ι Ω Ω' E F : Type*} [Finite ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [MeasurableSpace F] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {Y : ι → Ω' → F}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hXind : iIndepFun X μ) (hYind : iIndepFun Y ν) :
    iIndepFun (fun i (z : Ω × Ω') => (X i z.1, Y i z.2)) (μ.prod ν) := by
  letI := Fintype.ofFinite ι
  let XV : Ω → (ι → E) := fun ω i => X i ω
  let YV : Ω' → (ι → F) := fun ω i => Y i ω
  let zip : ((ι → E) × (ι → F)) → (ι → E × F) :=
    (MeasurableEquiv.arrowProdEquivProdArrow E F ι).symm
  have hXVm : Measurable XV := measurable_pi_lambda _ hXm
  have hYVm : Measurable YV := measurable_pi_lambda _ hYm
  have hzipm : Measurable zip :=
    (MeasurableEquiv.arrowProdEquivProdArrow E F ι).symm.measurable
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (f := fun i (z : Ω × Ω') => (X i z.1, Y i z.2))
    (fun i => ((hXm i).comp measurable_fst |>.prodMk
      ((hYm i).comp measurable_snd)).aemeasurable)]
  have hfun : (fun z : Ω × Ω' => fun i => (X i z.1, Y i z.2)) =
      zip ∘ Prod.map XV YV := by
    funext z i
    rfl
  rw [hfun, ← Measure.map_map hzipm (hXVm.prodMap hYVm),
    ← Measure.map_prod_map μ ν hXVm hYVm,
    hXind.map_fun_eq_pi_map (fun i => (hXm i).aemeasurable),
    hYind.map_fun_eq_pi_map (fun i => (hYm i).aemeasurable)]
  rw [(MeasureTheory.measurePreserving_arrowProdEquivProdArrow E F ι
    (fun i => μ.map (X i)) (fun i => ν.map (Y i))).symm.map_eq]
  congr 1
  funext i
  calc
    (μ.map (X i)).prod (ν.map (Y i)) =
        (μ.prod ν).map (Prod.map (X i) (Y i)) :=
      Measure.map_prod_map μ ν (hXm i) (hYm i)
    _ = (μ.prod ν).map (fun z => (X i z.1, Y i z.2)) := by
      congr 1

/-- Coordinatewise recombination of two independent copies according to a deterministic
selector.

**Lean implementation helper.** -/
def selectorMix {n : ℕ} {Ω E : Type*}
    (X : Fin n → Ω → E) (δ : Fin n → Bool) (z : Ω × Ω)
    (i : Fin n) : E :=
  if δ i then X i z.1 else X i z.2

/-- Recombining two independent realizations coordinatewise preserves the joint law of an
independent coordinate family.

**Lean implementation helper.** -/
theorem identDistrib_selectorMix
    {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → E} (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X μ) (δ : Fin n → Bool) :
    IdentDistrib (fun z : Ω × Ω => selectorMix X δ z)
      (fun ω => fun i => X i ω) (μ.prod μ) μ := by
  have hpairs : iIndepFun
      (fun i (z : Ω × Ω) => (X i z.1, X i z.2)) (μ.prod μ) :=
    iIndepFun_prodMk_prod_decoupling hXm hXm hXind hXind
  have hmixInd : iIndepFun (fun i (z : Ω × Ω) =>
      if δ i then X i z.1 else X i z.2) (μ.prod μ) := by
    simpa [Function.comp_def] using hpairs.comp
      (fun i (p : E × E) => if δ i then p.1 else p.2)
      (fun i => by
        cases h : δ i
        · simpa [h] using (measurable_snd : Measurable (Prod.snd : E × E → E))
        · simpa [h] using (measurable_fst : Measurable (Prod.fst : E × E → E)))
  have hcoord (i : Fin n) :
      IdentDistrib (fun z : Ω × Ω => selectorMix X δ z i)
        (X i) (μ.prod μ) μ := by
    cases h : δ i
    · simp only [selectorMix, h, Bool.false_eq_true, if_false]
      refine ⟨(hXm i).comp measurable_snd |>.aemeasurable,
        (hXm i).aemeasurable, ?_⟩
      change Measure.map (X i ∘ Prod.snd) (μ.prod μ) = Measure.map (X i) μ
      rw [← Measure.map_map (hXm i) measurable_snd,
        (measurePreserving_snd (μ := μ) (ν := μ)).map_eq]
    · simp only [selectorMix, h, if_true]
      refine ⟨(hXm i).comp measurable_fst |>.aemeasurable,
        (hXm i).aemeasurable, ?_⟩
      change Measure.map (X i ∘ Prod.fst) (μ.prod μ) = Measure.map (X i) μ
      rw [← Measure.map_map (hXm i) measurable_fst,
        (measurePreserving_fst (μ := μ) (ν := μ)).map_eq]
  convert IdentDistrib.pi hcoord hmixInd hXind using 1

/-- Replace the unselected coordinates by coordinates of an independent copy on a separate
probability space.

**Lean implementation helper.** -/
def selectorReplacement {n : ℕ} {Ω Ω' E : Type*}
    (X : Fin n → Ω → E) (X' : Fin n → Ω' → E)
    (δ : Fin n → Bool) (z : Ω × Ω') (i : Fin n) : E :=
  if δ i then X i z.1 else X' i z.2

/-- Replacing any deterministic subset of independent coordinates by the corresponding
coordinates of an independent identically distributed family preserves the full joint law.

**Lean implementation helper.** -/
theorem identDistrib_selectorReplacement
    {n : ℕ} {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → E} {X' : Fin n → Ω' → E}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (δ : Fin n → Bool) :
    IdentDistrib (fun z : Ω × Ω' => selectorReplacement X X' δ z)
      (fun ω => fun i => X i ω) (μ.prod ν) μ := by
  have hpairs : iIndepFun
      (fun i (z : Ω × Ω') => (X i z.1, X' i z.2)) (μ.prod ν) :=
    iIndepFun_prodMk_prod_decoupling hXm hX'm hXind hX'ind
  have hmixInd : iIndepFun (fun i (z : Ω × Ω') =>
      if δ i then X i z.1 else X' i z.2) (μ.prod ν) := by
    simpa [Function.comp_def] using hpairs.comp
      (fun i (p : E × E) => if δ i then p.1 else p.2)
      (fun i => by
        cases h : δ i
        · simpa [h] using (measurable_snd : Measurable (Prod.snd : E × E → E))
        · simpa [h] using (measurable_fst : Measurable (Prod.fst : E × E → E)))
  have hcoord (i : Fin n) :
      IdentDistrib (fun z : Ω × Ω' => selectorReplacement X X' δ z i)
        (X i) (μ.prod ν) μ := by
    cases h : δ i
    · simp only [selectorReplacement, h, Bool.false_eq_true, if_false]
      have hsnd : IdentDistrib (fun z : Ω × Ω' => X' i z.2)
          (X' i) (μ.prod ν) ν := by
        refine ⟨(hX'm i).comp measurable_snd |>.aemeasurable,
          (hX'm i).aemeasurable, ?_⟩
        change Measure.map (X' i ∘ Prod.snd) (μ.prod ν) = Measure.map (X' i) ν
        rw [← Measure.map_map (hX'm i) measurable_snd,
          (measurePreserving_snd (μ := μ) (ν := ν)).map_eq]
      exact hsnd.trans (hcopy i)
    · simp only [selectorReplacement, h, if_true]
      refine ⟨(hXm i).comp measurable_fst |>.aemeasurable,
        (hXm i).aemeasurable, ?_⟩
      change Measure.map (X i ∘ Prod.fst) (μ.prod ν) = Measure.map (X i) μ
      rw [← Measure.map_map (hXm i) measurable_fst,
        (measurePreserving_fst (μ := μ) (ν := ν)).map_eq]
  convert IdentDistrib.pi hcoord hmixInd hXind using 1

/-- The partial chaos after replacing the complementary coordinates by an independent copy.

**Lean implementation helper.** -/
def decoupledPartialChaos {n : ℕ} {Ω Ω' : Type*}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (X' : Fin n → Ω' → ℝ)
    (δ : Fin n → Bool) (z : Ω × Ω') : ℝ :=
  ∑ i, ∑ j, selectorValue δ i * (1 - selectorValue δ j) *
    A i j * X i z.1 * X' j z.2

/-- Replacing each coordinate according to the selector rewrites the partial chaos exactly as its decoupled form.

**Lean implementation helper.** -/
lemma partialChaos_selectorReplacement
    {n : ℕ} {Ω Ω' : Type*}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (X' : Fin n → Ω' → ℝ)
    (δ : Fin n → Bool) (z : Ω × Ω') :
    partialChaos A (selectorReplacement X X' δ z) δ =
      decoupledPartialChaos A X X' δ z := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases hi : δ i <;> cases hj : δ j <;>
    simp [selectorReplacement, selectorValue, hi, hj]

/-- Raw law form of Step 2. This is the interface used to transport both integrability and
expectations, rather than merely asserting an equality of already-integrable expectations.

**Lean implementation helper.** -/
theorem identDistrib_partialChaos_decoupledPartialChaos
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (δ : Fin n → Bool) :
    IdentDistrib (decoupledPartialChaos A X X' δ)
      (fun ω => partialChaos A (fun i => X i ω) δ)
      (μ.prod ν) μ := by
  let G : (Fin n → ℝ) → ℝ := fun x => partialChaos A x δ
  have hG : Measurable G := by
    dsimp only [G, partialChaos]
    fun_prop
  have hLaw := (identDistrib_selectorReplacement
    hXm hX'm hXind hX'ind hcopy δ).comp hG
  simpa [G, Function.comp_def, partialChaos_selectorReplacement] using hLaw

/-- Step 2's replacement: the partial chaos is unchanged in law when the complementary
coordinates are replaced by an independent copy.

**Lean implementation helper.** -/
theorem integral_partialChaos_eq_decoupledPartialChaos
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (F : ℝ → ℝ) (hFcont : Continuous F) (δ : Fin n → Bool) :
    (∫ ω, F (4 * partialChaos A (fun i => X i ω) δ) ∂μ) =
      ∫ z : Ω × Ω', F (4 * decoupledPartialChaos A X X' δ z) ∂μ.prod ν := by
  let G : (Fin n → ℝ) → ℝ := fun x => F (4 * partialChaos A x δ)
  have hG : Measurable G := by
    apply hFcont.measurable.comp
    simp only [partialChaos]
    fun_prop
  have hLaw := (identDistrib_selectorReplacement
    hXm hX'm hXind hX'ind hcopy δ).comp hG
  have hint := hLaw.integral_eq
  simpa [G, Function.comp_def, partialChaos_selectorReplacement] using hint.symm

/-- The fully decoupled bilinear form after the four independent coordinate blocks have been
recombined according to a selector.

**Lean implementation helper.** -/
def recombinedBilinear {n : ℕ} {Ω Ω' : Type*}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (X' : Fin n → Ω' → ℝ)
    (δ : Fin n → Bool) (z : (Ω × Ω) × (Ω' × Ω')) : ℝ :=
  bilinearForm A (selectorMix X δ z.1)
    (selectorMix X' (fun i => !δ i) z.2)

/-- The recombined full bilinear form has the same law as the original fully decoupled form.

**Lean implementation helper.** -/
theorem identDistrib_recombinedBilinear
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (δ : Fin n → Bool) :
    IdentDistrib (recombinedBilinear A X X' δ)
      (fun z : Ω × Ω' => bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2))
      ((μ.prod μ).prod (ν.prod ν)) (μ.prod ν) := by
  let MX : (Ω × Ω) → (Fin n → ℝ) := fun z => selectorMix X δ z
  let MX' : (Ω' × Ω') → (Fin n → ℝ) :=
    fun z => selectorMix X' (fun i => !δ i) z
  let XV : Ω → (Fin n → ℝ) := fun ω i => X i ω
  let X'V : Ω' → (Fin n → ℝ) := fun ω i => X' i ω
  have hMXm : Measurable MX := by
    apply measurable_pi_lambda
    intro i
    dsimp only [MX, selectorMix]
    by_cases h : δ i = true
    · simp only [h, if_true]
      change Measurable (X i ∘ (Prod.fst : Ω × Ω → Ω))
      exact (hXm i).comp measurable_fst
    · have hf : δ i = false := Bool.eq_false_of_not_eq_true h
      simp only [hf, Bool.false_eq_true, if_false]
      change Measurable (X i ∘ (Prod.snd : Ω × Ω → Ω))
      exact (hXm i).comp measurable_snd
  have hMX'm : Measurable MX' := by
    apply measurable_pi_lambda
    intro i
    dsimp only [MX', selectorMix]
    by_cases h : δ i = true
    · simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
      change Measurable (X' i ∘ (Prod.snd : Ω' × Ω' → Ω'))
      exact (hX'm i).comp measurable_snd
    · have hf : δ i = false := Bool.eq_false_of_not_eq_true h
      simp only [hf, Bool.not_false, if_true]
      change Measurable (X' i ∘ (Prod.fst : Ω' × Ω' → Ω'))
      exact (hX'm i).comp measurable_fst
  have hXVm : Measurable XV := measurable_pi_lambda _ hXm
  have hX'Vm : Measurable X'V := measurable_pi_lambda _ hX'm
  have hMixX : IdentDistrib MX XV (μ.prod μ) μ := by
    simpa [MX, XV] using identDistrib_selectorMix hXm hXind δ
  have hMixX' : IdentDistrib MX' X'V (ν.prod ν) ν := by
    simpa [MX', X'V] using
      identDistrib_selectorMix hX'm hX'ind (fun i => !δ i)
  have hPair : IdentDistrib
      (fun z : (Ω × Ω) × (Ω' × Ω') => (MX z.1, MX' z.2))
      (fun z : Ω × Ω' => (XV z.1, X'V z.2))
      ((μ.prod μ).prod (ν.prod ν)) (μ.prod ν) := by
    refine ⟨(hMXm.comp measurable_fst).prodMk (hMX'm.comp measurable_snd) |>.aemeasurable,
      (hXVm.comp measurable_fst).prodMk (hX'Vm.comp measurable_snd) |>.aemeasurable, ?_⟩
    calc
      Measure.map (fun z : (Ω × Ω) × (Ω' × Ω') =>
          (MX z.1, MX' z.2)) ((μ.prod μ).prod (ν.prod ν)) =
          (Measure.map MX (μ.prod μ)).prod (Measure.map MX' (ν.prod ν)) :=
        (Measure.map_prod_map (μ.prod μ) (ν.prod ν) hMXm hMX'm).symm
      _ = (Measure.map XV μ).prod (Measure.map X'V ν) := by
        rw [hMixX.map_eq, hMixX'.map_eq]
      _ = Measure.map (fun z : Ω × Ω' => (XV z.1, X'V z.2)) (μ.prod ν) :=
        Measure.map_prod_map μ ν hXVm hX'Vm
  let H : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun p => bilinearForm A p.1 p.2
  have hH : Measurable H := by
    dsimp only [H, bilinearForm, HDP.Chapter4.matrixBilinear]
    fun_prop
  change IdentDistrib
    (fun z : (Ω × Ω) × (Ω' × Ω') => bilinearForm A
      (selectorMix X δ z.1) (selectorMix X' (fun i => !δ i) z.2))
    (fun z : Ω × Ω' => bilinearForm A
      (fun i => X i z.1) (fun j => X' j z.2))
    ((μ.prod μ).prod (ν.prod ν)) (μ.prod ν)
  simpa [MX, MX', XV, X'V, H, Function.comp_def] using hPair.comp hH

/-- Jensen's inequality with a parameter-dependent centered remainder. This is the precise
analytic form of conditioning used in Step 3 of decoupling.

**Lean implementation helper.** -/
theorem integral_convex_le_integral_add_conditionally_centered
    {Λ Θ : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ]
    {ρ : Measure Λ} {τ : Measure Θ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ]
    {Y : Λ → ℝ} {Z : Λ → Θ → ℝ} {F : ℝ → ℝ}
    (hFconv : ConvexOn ℝ Set.univ F) (hFcont : Continuous F)
    (hZint : ∀ u, Integrable (Z u) τ)
    (hZ0 : ∀ u, ∫ v, Z u v ∂τ = 0)
    (hFY : Integrable (F ∘ Y) ρ)
    (hFadd : Integrable (fun p : Λ × Θ => F (Y p.1 + Z p.1 p.2))
      (ρ.prod τ)) :
    (∫ u, F (Y u) ∂ρ) ≤
      ∫ p : Λ × Θ, F (Y p.1 + Z p.1 p.2) ∂ρ.prod τ := by
  have hslice : ∀ᵐ u ∂ρ,
      Integrable (fun v => F (Y u + Z u v)) τ :=
    hFadd.prod_right_ae
  have hjensen : ∀ᵐ u ∂ρ,
      F (Y u) ≤ ∫ v, F (Y u + Z u v) ∂τ := by
    filter_upwards [hslice] with u hu
    have huZ : Integrable (fun v => Y u + Z u v) τ :=
      (integrable_const (Y u)).add (hZint u)
    have hint : ∫ v, Y u + Z u v ∂τ = Y u := by
      rw [integral_add (integrable_const (Y u)) (hZint u), integral_const, hZ0 u]
      simp
    have hmap := hFconv.map_integral_le hFcont.continuousOn isClosed_univ
      (by simp) huZ (by simpa [Function.comp_def] using hu)
    simpa [hint] using hmap
  have houter : Integrable (fun u => ∫ v, F (Y u + Z u v) ∂τ) ρ :=
    hFadd.integral_prod_left
  calc
    (∫ u, F (Y u) ∂ρ) = ∫ u, (F ∘ Y) u ∂ρ := by rfl
    _ ≤ ∫ u, ∫ v, F (Y u + Z u v) ∂τ ∂ρ :=
      integral_mono_ae hFY houter hjensen
    _ = ∫ p : Λ × Θ, F (Y p.1 + Z p.1 p.2) ∂ρ.prod τ :=
      (integral_prod _ hFadd).symm

/-- The coordinate permutation `(a,c,b,d) ↦ (a,b,c,d)` used to compare the conditional product
grouping with the grouping by the two random-vector families.

**Lean implementation helper.** -/
def decouplingShuffle {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] :
    ((Ω × Ω') × (Ω × Ω')) → ((Ω × Ω) × (Ω' × Ω')) :=
  fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))

/-- The four-factor shuffle preserves the corresponding product probability measure.

**Lean implementation helper.** -/
theorem measurePreserving_decouplingShuffle
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (decouplingShuffle :
      ((Ω × Ω') × (Ω × Ω')) → ((Ω × Ω) × (Ω' × Ω')))
      ((μ.prod ν).prod (μ.prod ν))
      ((μ.prod μ).prod (ν.prod ν)) := by
  let h1 := measurePreserving_prodAssoc μ ν (μ.prod ν)
  let ha := (measurePreserving_prodAssoc ν μ ν).symm
  let hs := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod
    (MeasurePreserving.id ν)
  let hb := measurePreserving_prodAssoc μ ν ν
  let hInner := hb.comp (hs.comp ha)
  let h2 := (MeasurePreserving.id μ).prod hInner
  let h3 := (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm
  convert h3.comp (h2.comp h1) using 1
  funext z
  rfl

/-- The recombined full form in the product grouping used for conditional Jensen: the first pair
contains the fixed blocks and the second pair the centered remainder blocks.

**Lean implementation helper.** -/
def crossRecombinedBilinear {n : ℕ} {Ω Ω' : Type*}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (X' : Fin n → Ω' → ℝ)
    (δ : Fin n → Bool) (z : (Ω × Ω') × (Ω × Ω')) : ℝ :=
  bilinearForm A
    (fun i => if δ i then X i z.1.1 else X i z.2.1)
    (fun j => if δ j then X' j z.2.2 else X' j z.1.2)

/-- Identifies cross recombined bilinear with recombined bilinear shuffle.

**Lean implementation helper.** -/
@[simp] lemma crossRecombinedBilinear_eq_recombinedBilinear_shuffle
    {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (X' : Fin n → Ω' → ℝ)
    (δ : Fin n → Bool) (z : (Ω × Ω') × (Ω × Ω')) :
    crossRecombinedBilinear A X X' δ z =
      recombinedBilinear A X X' δ (decouplingShuffle z) := by
  unfold crossRecombinedBilinear recombinedBilinear decouplingShuffle
  congr 1
  funext j
  cases h : δ j <;> simp [selectorMix, h]

/-- The conditionally grouped recombination has the same distribution as the original decoupled
bilinear form.

**Lean implementation helper.** -/
theorem identDistrib_crossRecombinedBilinear
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (δ : Fin n → Bool) :
    IdentDistrib (fun z : (Ω × Ω') × (Ω × Ω') =>
        crossRecombinedBilinear A X X' δ z)
      (fun z : Ω × Ω' => bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2))
      ((μ.prod ν).prod (μ.prod ν)) (μ.prod ν) := by
  have hRm : Measurable (recombinedBilinear A X X' δ) := by
    have hMX : ∀ i, Measurable (fun z : (Ω × Ω) × (Ω' × Ω') =>
        selectorMix X δ z.1 i) := by
      intro i
      cases h : δ i
      · simp only [selectorMix, h, Bool.false_eq_true, if_false]
        convert (hXm i).comp (measurable_snd.comp measurable_fst) using 1
        funext z
        rfl
      · simp only [selectorMix, h, if_true]
        convert (hXm i).comp (measurable_fst.comp measurable_fst) using 1
        funext z
        rfl
    have hMX' : ∀ j, Measurable (fun z : (Ω × Ω) × (Ω' × Ω') =>
        selectorMix X' (fun i => !δ i) z.2 j) := by
      intro j
      cases h : δ j
      · simp only [selectorMix, h, Bool.not_false, if_true]
        convert (hX'm j).comp (measurable_fst.comp measurable_snd) using 1
        funext z
        rfl
      · simp only [selectorMix, h, Bool.not_true, Bool.false_eq_true, if_false]
        convert (hX'm j).comp (measurable_snd.comp measurable_snd) using 1
        funext z
        rfl
    unfold recombinedBilinear bilinearForm HDP.Chapter4.matrixBilinear
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ =>
        ((hMX i).mul_const (A i j)).mul (hMX' j)
  have hShuffle : IdentDistrib
      (recombinedBilinear A X X' δ ∘ decouplingShuffle)
      (recombinedBilinear A X X' δ)
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) := by
    let hMP : MeasurePreserving (decouplingShuffle :
        ((Ω × Ω') × (Ω × Ω')) → ((Ω × Ω) × (Ω' × Ω')))
        ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) :=
      measurePreserving_decouplingShuffle
    refine ⟨(hRm.comp hMP.measurable).aemeasurable,
      hRm.aemeasurable, ?_⟩
    rw [← Measure.map_map hRm hMP.measurable, hMP.map_eq]
  have hLaw := hShuffle.trans
    (identDistrib_recombinedBilinear A hXm hX'm hXind hX'ind δ)
  simpa [Function.comp_def] using hLaw

/-- For fixed selector blocks, the recombined bilinear form is integrable in the two centered
remainder blocks.

**Lean implementation helper.** -/
theorem integrable_crossRecombinedBilinear_snd
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hX'int : ∀ i, Integrable (X' i) ν)
    (δ : Fin n → Bool) (u : Ω × Ω') :
    Integrable (fun v : Ω × Ω' =>
      crossRecombinedBilinear A X X' δ (u, v)) (μ.prod ν) := by
  classical
  let T : Fin n → Fin n → (Ω × Ω') → ℝ := fun i j v =>
    (if δ i then X i u.1 else X i v.1) * A i j *
      (if δ j then X' j v.2 else X' j u.2)
  have hTint (i j : Fin n) : Integrable (T i j) (μ.prod ν) := by
    cases hi : δ i <;> cases hj : δ j
    · have h := (hXint i).comp_fst ν |>.mul_const (A i j * X' j u.2)
      convert h using 1
      funext v
      simp [T, hi, hj]
      ring
    · have h := ((hXint i).mul_prod (hX'int j)).const_mul (A i j)
      convert h using 1
      funext v
      simp [T, hi, hj]
      ring
    · simpa [T, hi, hj] using
        (integrable_const (μ := μ.prod ν)
          (X i u.1 * A i j * X' j u.2 : ℝ))
    · have h := (hX'int j).comp_snd μ |>.const_mul (X i u.1 * A i j)
      convert h using 1
      funext v
      simp [T, hi, hj]
  change Integrable (fun v : Ω × Ω' => ∑ i, ∑ j, T i j v) (μ.prod ν)
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hTint i j))

/-- Conditional centering calculation in Step 3: averaging the recombined full form over the
remainder blocks leaves exactly the fixed partial chaos.

**Lean implementation helper.** -/
theorem integral_crossRecombinedBilinear_snd
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hX'int : ∀ i, Integrable (X' i) ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0)
    (δ : Fin n → Bool) (u : Ω × Ω') :
    (∫ v : Ω × Ω', crossRecombinedBilinear A X X' δ (u, v)
        ∂μ.prod ν) = decoupledPartialChaos A X X' δ u := by
  classical
  let T : Fin n → Fin n → (Ω × Ω') → ℝ := fun i j v =>
    (if δ i then X i u.1 else X i v.1) * A i j *
      (if δ j then X' j v.2 else X' j u.2)
  have hTint (i j : Fin n) : Integrable (T i j) (μ.prod ν) := by
    cases hi : δ i <;> cases hj : δ j
    · have h := (hXint i).comp_fst ν |>.mul_const (A i j * X' j u.2)
      convert h using 1
      funext v
      simp [T, hi, hj]
      ring
    · have h := ((hXint i).mul_prod (hX'int j)).const_mul (A i j)
      convert h using 1
      funext v
      simp [T, hi, hj]
      ring
    · simpa [T, hi, hj] using
        (integrable_const (μ := μ.prod ν)
          (X i u.1 * A i j * X' j u.2 : ℝ))
    · have h := (hX'int j).comp_snd μ |>.const_mul (X i u.1 * A i j)
      convert h using 1
      funext v
      simp [T, hi, hj]
  have hTintegral (i j : Fin n) :
      (∫ v, T i j v ∂μ.prod ν) =
        selectorValue δ i * (1 - selectorValue δ j) *
          A i j * X i u.1 * X' j u.2 := by
    rw [integral_prod _ (hTint i j)]
    cases hi : δ i <;> cases hj : δ j
    · simp [T, selectorValue, hi, hj, integral_mul_const, hX0]
    · simp [T, selectorValue, hi, hj, integral_const_mul, hX'0]
    · trans X i u.1 * A i j * X' j u.2
      · simp [T, hi, hj]
      · unfold selectorValue
        rw [hi, hj]
        simp only [if_true, Bool.false_eq_true, if_false]
        ring
    · simp [T, selectorValue, hi, hj, integral_const_mul, hX'0]
  change (∫ v : Ω × Ω', ∑ i, ∑ j, T i j v ∂μ.prod ν) = _
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hTint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hTint i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact hTintegral i j

/-- Step 3 of the source proof: after Step 2 has replaced the complementary coordinates by an
independent copy, conditional Jensen completes the partial chaos to the full decoupled bilinear
form.

**Book (6.4).** -/
theorem integral_decoupledPartialChaos_le_bilinear
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX'int : ∀ i, Integrable (X' i) ν)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0)
    (F : ℝ → ℝ) (hFconv : ConvexOn ℝ Set.univ F)
    (hFcont : Continuous F) (δ : Fin n → Bool)
    (hpartial : Integrable (fun z : Ω × Ω' =>
      F (4 * decoupledPartialChaos A X X' δ z)) (μ.prod ν))
    (hfull : Integrable (fun z : Ω × Ω' =>
      F (4 * bilinearForm A (fun i => X i z.1)
        (fun j => X' j z.2))) (μ.prod ν)) :
    (∫ z : Ω × Ω', F (4 * decoupledPartialChaos A X X' δ z)
        ∂μ.prod ν) ≤
      ∫ z : Ω × Ω', F (4 * bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
  let Y : (Ω × Ω') → ℝ := fun u =>
    4 * decoupledPartialChaos A X X' δ u
  let Z : (Ω × Ω') → (Ω × Ω') → ℝ := fun u v =>
    4 * crossRecombinedBilinear A X X' δ (u, v) - Y u
  have hZint : ∀ u, Integrable (Z u) (μ.prod ν) := by
    intro u
    exact (integrable_crossRecombinedBilinear_snd A hXint hX'int δ u).const_mul 4
      |>.sub (integrable_const (Y u))
  have hZ0 : ∀ u, ∫ v, Z u v ∂μ.prod ν = 0 := by
    intro u
    have hc := integrable_crossRecombinedBilinear_snd A hXint hX'int δ u
    calc
      (∫ v, Z u v ∂μ.prod ν) =
          4 * (∫ v, crossRecombinedBilinear A X X' δ (u, v) ∂μ.prod ν) -
            Y u := by
        dsimp only [Z]
        rw [integral_sub (hc.const_mul 4) (integrable_const (Y u)),
          integral_const_mul, integral_const]
        simp
      _ = 0 := by
        rw [integral_crossRecombinedBilinear_snd A hXint hX'int hX0 hX'0]
        dsimp only [Y]
        ring
  let G : ℝ → ℝ := fun t => F (4 * t)
  have hGm : Measurable G := hFcont.measurable.comp (measurable_const.mul measurable_id)
  have hLaw := (identDistrib_crossRecombinedBilinear
    A hXm hX'm hXind hX'ind δ).comp hGm
  have hFcross : Integrable (fun p : (Ω × Ω') × (Ω × Ω') =>
      F (4 * crossRecombinedBilinear A X X' δ p))
      ((μ.prod ν).prod (μ.prod ν)) := by
    have := hLaw.integrable_iff.mpr hfull
    simpa [G, Function.comp_def] using this
  have hFadd : Integrable (fun p : (Ω × Ω') × (Ω × Ω') =>
      F (Y p.1 + Z p.1 p.2)) ((μ.prod ν).prod (μ.prod ν)) := by
    convert hFcross using 1
    funext p
    congr 1
    dsimp only [Y, Z]
    ring
  have hstep := integral_convex_le_integral_add_conditionally_centered
    (ρ := μ.prod ν) (τ := μ.prod ν) (Y := Y) (Z := Z)
    hFconv hFcont hZint hZ0 (by simpa [Y, Function.comp_def] using hpartial) hFadd
  calc
    (∫ z : Ω × Ω', F (4 * decoupledPartialChaos A X X' δ z) ∂μ.prod ν) =
        ∫ u, F (Y u) ∂μ.prod ν := by rfl
    _ ≤ ∫ p : (Ω × Ω') × (Ω × Ω'),
        F (Y p.1 + Z p.1 p.2) ∂(μ.prod ν).prod (μ.prod ν) := hstep
    _ = ∫ p : (Ω × Ω') × (Ω × Ω'),
        F (4 * crossRecombinedBilinear A X X' δ p)
          ∂(μ.prod ν).prod (μ.prod ν) := by
      congr 1
      funext p
      congr 1
      dsimp only [Y, Z]
      ring
    _ = ∫ z : Ω × Ω', F (4 * bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
      simpa [G, Function.comp_def] using hLaw.integral_eq

/-- For the exponential test function, integrability of the completed bilinear MGF already
implies integrability of every selector partial MGF. This removes the auxiliary
selector-integrability premise from the extended MGF corollary below.

**Lean implementation helper.** -/
theorem integrable_exp_decoupledPartialChaos_of_integrable_bilinear
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX'int : ∀ i, Integrable (X' i) ν)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0)
    (lam : ℝ) (δ : Fin n → Bool)
    (hfull : Integrable (fun z : Ω × Ω' =>
      Real.exp (4 * lam * bilinearForm A (fun i => X i z.1)
        (fun j => X' j z.2))) (μ.prod ν)) :
    Integrable (fun z : Ω × Ω' =>
      Real.exp (4 * lam * decoupledPartialChaos A X X' δ z))
      (μ.prod ν) := by
  let Y : (Ω × Ω') → ℝ := fun u =>
    4 * decoupledPartialChaos A X X' δ u
  let Z : (Ω × Ω') → (Ω × Ω') → ℝ := fun u v =>
    4 * crossRecombinedBilinear A X X' δ (u, v) - Y u
  let F : ℝ → ℝ := fun t => Real.exp (lam * t)
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFconv : ConvexOn ℝ Set.univ F := by
    convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ lam) using 1
  have hZint : ∀ u, Integrable (Z u) (μ.prod ν) := by
    intro u
    exact (integrable_crossRecombinedBilinear_snd A hXint hX'int δ u).const_mul 4
      |>.sub (integrable_const (Y u))
  have hZ0 : ∀ u, ∫ v, Z u v ∂μ.prod ν = 0 := by
    intro u
    have hc := integrable_crossRecombinedBilinear_snd A hXint hX'int δ u
    calc
      (∫ v, Z u v ∂μ.prod ν) =
          4 * (∫ v, crossRecombinedBilinear A X X' δ (u, v) ∂μ.prod ν) -
            Y u := by
        dsimp only [Z]
        rw [integral_sub (hc.const_mul 4) (integrable_const (Y u)),
          integral_const_mul, integral_const]
        simp
      _ = 0 := by
        rw [integral_crossRecombinedBilinear_snd A hXint hX'int hX0 hX'0]
        dsimp only [Y]
        ring
  let G : ℝ → ℝ := fun t => Real.exp (4 * lam * t)
  have hGm : Measurable G := by
    dsimp only [G]
    fun_prop
  have hLaw := (identDistrib_crossRecombinedBilinear
    A hXm hX'm hXind hX'ind δ).comp hGm
  have hFcross : Integrable (fun p : (Ω × Ω') × (Ω × Ω') =>
      Real.exp (4 * lam * crossRecombinedBilinear A X X' δ p))
      ((μ.prod ν).prod (μ.prod ν)) := by
    have := hLaw.integrable_iff.mpr hfull
    simpa [G, Function.comp_def] using this
  have hFadd : Integrable (fun p : (Ω × Ω') × (Ω × Ω') =>
      F (Y p.1 + Z p.1 p.2)) ((μ.prod ν).prod (μ.prod ν)) := by
    convert hFcross using 1
    funext p
    dsimp only [F, Y, Z]
    congr 1
    ring
  have hslice : ∀ᵐ u ∂μ.prod ν,
      Integrable (fun v => F (Y u + Z u v)) (μ.prod ν) :=
    hFadd.prod_right_ae
  have hjensen : ∀ᵐ u ∂μ.prod ν,
      F (Y u) ≤ ∫ v, F (Y u + Z u v) ∂μ.prod ν := by
    filter_upwards [hslice] with u hu
    have huZ : Integrable (fun v => Y u + Z u v) (μ.prod ν) :=
      (integrable_const (Y u)).add (hZint u)
    have hint : ∫ v, Y u + Z u v ∂μ.prod ν = Y u := by
      rw [integral_add (integrable_const (Y u)) (hZint u), integral_const,
        hZ0 u]
      simp
    have hmap := hFconv.map_integral_le hFcont.continuousOn isClosed_univ
      (by simp) huZ (by simpa [Function.comp_def] using hu)
    simpa [hint] using hmap
  have houter : Integrable
      (fun u => ∫ v, F (Y u + Z u v) ∂μ.prod ν) (μ.prod ν) :=
    hFadd.integral_prod_left
  have hYm : Measurable Y := by
    dsimp only [Y, decoupledPartialChaos]
    fun_prop
  have hFY : Integrable (fun u => F (Y u)) (μ.prod ν) := by
    refine houter.mono' (hFcont.measurable.comp hYm).aestronglyMeasurable ?_
    filter_upwards [hjensen] with u hu
    simpa [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hu
  convert hFY using 1
  funext z
  dsimp only [F, Y]
  congr 1
  ring

/-- A coordinate factor that enforces selection of `i`, rejection of `j`, and imposes no
condition on every other coordinate.

**Lean implementation helper.** -/
private def selectorFactor {n : ℕ} (i j k : Fin n) (b : Bool) : ℝ :=
  if k = i then (if b then 1 else 0)
  else if k = j then (if b then 0 else 1)
  else 1

/-- The product of selector factors equals the indicator that coordinate `i` is selected while coordinate `j` is not.

**Lean implementation helper.** -/
private lemma prod_selectorFactor {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (δ : Fin n → Bool) :
    (∏ k, selectorFactor i j k (δ k)) =
      selectorValue δ i * (1 - selectorValue δ j) := by
  classical
  have hfactor : ∀ k : Fin n,
      selectorFactor i j k (δ k) =
        (if k = i then (if δ k then (1 : ℝ) else 0) else 1) *
        (if k = j then (if δ k then (0 : ℝ) else 1) else 1) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [selectorFactor, hij]
    · by_cases hkj : k = j
      · subst k
        simp [selectorFactor, hki]
      · simp [selectorFactor, hki, hkj]
  simp_rw [hfactor, Finset.prod_mul_distrib]
  cases hi : δ i <;> cases hj : δ j <;>
    simp [selectorValue, hi, hj]

/-- Independent fair selectors satisfy the moment used in Step 1 of the decoupling proof.

**Lean implementation helper.** -/
theorem selector_cross_moment {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (𝔼 δ : Fin n → Bool,
      selectorValue δ i * (1 - selectorValue δ j)) = (1 / 4 : ℝ) := by
  classical
  have hfun :
      (fun δ : Fin n → Bool =>
        selectorValue δ i * (1 - selectorValue δ j)) =
      (fun δ => ∏ k, selectorFactor i j k (δ k)) := by
    funext δ
    exact (prod_selectorFactor i j hij δ).symm
  rw [hfun]
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum]
  let f : Fin n → ℝ := fun k => if k = i then 1 else if k = j then 1 else 2
  have hcoord : ∀ k : Fin n,
      (∑ b : Bool, selectorFactor i j k b) = f k := by
    intro k
    rw [Fintype.sum_bool]
    by_cases hki : k = i
    · simp [selectorFactor, f, hki]
    · by_cases hkj : k = j
      · simp [selectorFactor, f, hkj, hij.symm]
      · norm_num [selectorFactor, f, hki, hkj]
  rw [Finset.prod_congr rfl (fun k _ => hcoord k)]
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin n)) := by
    simp [hij.symm]
  have hprod : (∏ k, f k) = (2 : ℝ) ^ (n - 2) := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) f hjmem]
    simp only [f, if_pos, hij.symm, if_false, one_mul]
    have hrest : ∀ k ∈ (Finset.univ.erase i).erase j, f k = (2 : ℝ) := by
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp [f, hki, hkj]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const]
    congr 1
    rw [Finset.card_erase_of_mem hjmem,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  change (∏ k, f k) / (2 : ℝ) ^ n = 1 / 4
  rw [hprod]
  have hn : 2 ≤ n := by
    have hv : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    omega
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hn]
  field_simp
  norm_num

/-- A diagonal-free quadratic form is four times the selector average of its partial chaoses
(Step 1 of the proof of the corresponding theorem).

**Lean implementation helper.** -/
theorem quadraticForm_eq_four_mul_selectorAverage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    (x : Fin n → ℝ) :
    quadraticForm A x = 4 * (𝔼 δ : Fin n → Bool, partialChaos A x δ) := by
  classical
  rw [quadraticForm_eq_doubleSum]
  simp only [partialChaos]
  simp_rw [Finset.expect_sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [hA i]
  · rw [show (𝔼 δ : Fin n → Bool,
        selectorValue δ i * (1 - selectorValue δ j) * A i j * x i * x j) =
        (𝔼 δ : Fin n → Bool,
          selectorValue δ i * (1 - selectorValue δ j)) * A i j * x i * x j by
          rw [Finset.expect_mul, Finset.expect_mul, Finset.expect_mul]]
    rw [selector_cross_moment i j hij]
    ring

/-- A selector partial chaos never sees diagonal entries, so replacing a matrix by its
off-diagonal part leaves it unchanged.

**Lean implementation helper.** -/
theorem partialChaos_offDiagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (δ : Fin n → Bool) :
    partialChaos (offDiagonal A) x δ = partialChaos A x δ := by
  classical
  unfold partialChaos
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    cases h : δ i <;> simp [selectorValue, h]
  · simp [offDiagonal, hij]

/-- Selector identity for an arbitrary matrix: the left side is its off-diagonal quadratic form,
while the selector chaos may retain the original matrix because its diagonal coefficients
vanish.

**Lean implementation helper.** -/
theorem quadraticForm_offDiagonal_eq_four_mul_selectorAverage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm (offDiagonal A) x =
      4 * (𝔼 δ : Fin n → Bool, partialChaos A x δ) := by
  rw [quadraticForm_eq_four_mul_selectorAverage (offDiagonal A)
    (fun i => offDiagonal_apply_same A i) x]
  congr 1
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  apply Finset.sum_congr rfl
  intro δ _
  exact partialChaos_offDiagonal A x δ

/-- Step 2 before integration: Jensen's inequality for the finite selector average. It is stated
for `ConvexOn ℝ univ`, which is the exact Mathlib form of a globally convex real function.

**Lean implementation helper.** -/
theorem convex_quadraticForm_le_selectorAverage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    (x : Fin n → ℝ) (F : ℝ → ℝ)
    (hF : ConvexOn ℝ Set.univ F) :
    F (quadraticForm A x) ≤
      (𝔼 δ : Fin n → Bool, F (4 * partialChaos A x δ)) := by
  classical
  let S := Fin n → Bool
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcard : (0 : ℝ) < Fintype.card S := by positivity
  have hc : 0 ≤ c := inv_nonneg.mpr hcard.le
  have hsumw : ∑ _δ : S, c = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [c]
    field_simp
  have hJ := hF.map_sum_le
    (t := (Finset.univ : Finset S))
    (w := fun _ : S => c)
    (p := fun δ : S => 4 * partialChaos A x δ)
    (fun _ _ => hc) hsumw (fun _ _ => Set.mem_univ _)
  rw [quadraticForm_eq_four_mul_selectorAverage A hA x]
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  simpa only [smul_eq_mul, c, div_eq_mul_inv, Finset.mul_sum,
    Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using hJ

/-- Integrated selector Jensen step, including the finite Fubini exchange used in the source
proof.

**Lean implementation helper.** -/
theorem integral_convex_quadraticForm_le_selectorAverage
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    (X : Fin n → Omega → ℝ) (F : ℝ → ℝ)
    (hF : ConvexOn ℝ Set.univ F)
    (hleft : Integrable
      (fun omega => F (quadraticForm A (fun i => X i omega))) mu)
    (hpartial : ∀ δ : Fin n → Bool, Integrable
      (fun omega => F (4 * partialChaos A (fun i => X i omega) δ)) mu) :
    (∫ omega, F (quadraticForm A (fun i => X i omega)) ∂mu) ≤
      (𝔼 δ : Fin n → Bool,
        ∫ omega, F (4 * partialChaos A (fun i => X i omega) δ) ∂mu) := by
  classical
  let G : Omega → ℝ := fun omega =>
    (𝔼 δ : Fin n → Bool,
      F (4 * partialChaos A (fun i => X i omega) δ))
  have hG : Integrable G mu := by
    rw [show G = fun omega =>
        (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
          ∑ δ : Fin n → Bool,
            F (4 * partialChaos A (fun i => X i omega) δ) by
      funext omega
      simp only [G, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
      ring]
    exact (integrable_finsetSum Finset.univ
      (fun δ _ => hpartial δ)).const_mul _
  calc
    (∫ omega, F (quadraticForm A (fun i => X i omega)) ∂mu)
        ≤ ∫ omega, G omega ∂mu :=
      integral_mono hleft hG (fun omega =>
        convex_quadraticForm_le_selectorAverage A hA
          (fun i => X i omega) F hF)
    _ = (𝔼 δ : Fin n → Bool,
        ∫ omega, F (4 * partialChaos A (fun i => X i omega) δ) ∂mu) := by
      rw [show G = fun omega =>
          (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
            ∑ δ : Fin n → Bool,
              F (4 * partialChaos A (fun i => X i omega) δ) by
        funext omega
        simp only [G, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
        ring]
      rw [integral_const_mul, integral_finsetSum Finset.univ]
      · rw [Fintype.expect_eq_sum_div_card]
        simp only [div_eq_mul_inv]
        ring
      · intro δ _
        exact hpartial δ

/-- For a general matrix, the same bound holds for the off-diagonal part on the left and all
entries on the decoupled right.

**Book Remark 6.1.2.** -/
theorem decoupling_offDiagonal
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (F : ℝ → ℝ) (hFconv : ConvexOn ℝ Set.univ F)
    (hFcont : Continuous F)
    (hleft : Integrable (fun ω =>
      F (quadraticForm (offDiagonal A) (fun i => X i ω))) μ)
    (hpartialInt : ∀ δ : Fin n → Bool, Integrable (fun ω =>
      F (4 * partialChaos A (fun i => X i ω) δ)) μ)
    (hright : Integrable (fun z : Ω × Ω' =>
      F (4 * bilinearForm A (fun i => X i z.1)
        (fun j => X' j z.2))) (μ.prod ν)) :
    (∫ ω, F (quadraticForm (offDiagonal A) (fun i => X i ω)) ∂μ) ≤
      ∫ z : Ω × Ω', F (4 * bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
  have hX'int : ∀ i, Integrable (X' i) ν := fun i =>
    (hcopy i).integrable_iff.mpr (hXint i)
  have hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0 := fun i =>
    (hcopy i).integral_eq.trans (hX0 i)
  have hpartialOff : ∀ δ : Fin n → Bool, Integrable (fun ω =>
      F (4 * partialChaos (offDiagonal A) (fun i => X i ω) δ)) μ := by
    intro δ
    convert hpartialInt δ using 1
    funext ω
    congr 2
    exact partialChaos_offDiagonal A (fun i => X i ω) δ
  have hselector :
      (∫ ω, F (quadraticForm (offDiagonal A) (fun i => X i ω)) ∂μ) ≤
        (𝔼 δ : Fin n → Bool,
          ∫ ω, F (4 * partialChaos A (fun i => X i ω) δ) ∂μ) := by
    have h := integral_convex_quadraticForm_le_selectorAverage μ
      (offDiagonal A) (fun i => offDiagonal_apply_same A i) X F hFconv
      hleft hpartialOff
    convert h using 1
    rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
    congr 1
    apply Finset.sum_congr rfl
    intro δ _
    congr 1
    funext ω
    congr 2
    exact (partialChaos_offDiagonal A (fun i => X i ω) δ).symm
  have hcomparison : ∀ δ : Fin n → Bool,
      (∫ ω, F (4 * partialChaos A (fun i => X i ω) δ) ∂μ) ≤
        ∫ z : Ω × Ω', F (4 * bilinearForm A
          (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
    intro δ
    let G : ℝ → ℝ := fun t => F (4 * t)
    have hGm : Measurable G :=
      hFcont.measurable.comp (measurable_const.mul measurable_id)
    have hLaw := (identDistrib_partialChaos_decoupledPartialChaos
      A hXm hX'm hXind hX'ind hcopy δ).comp hGm
    have hDecInt : Integrable (fun z : Ω × Ω' =>
        F (4 * decoupledPartialChaos A X X' δ z)) (μ.prod ν) := by
      have := hLaw.integrable_iff.mpr (hpartialInt δ)
      simpa [G, Function.comp_def] using this
    have hcomplete := integral_decoupledPartialChaos_le_bilinear
      A hXm hX'm hXint hX'int hXind hX'ind hX0 hX'0
      F hFconv hFcont δ hDecInt hright
    calc
      (∫ ω, F (4 * partialChaos A (fun i => X i ω) δ) ∂μ) =
          ∫ z : Ω × Ω', F (4 * decoupledPartialChaos A X X' δ z)
            ∂μ.prod ν := by
        simpa [G, Function.comp_def] using hLaw.integral_eq.symm
      _ ≤ ∫ z : Ω × Ω', F (4 * bilinearForm A
          (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := hcomplete
  calc
    (∫ ω, F (quadraticForm (offDiagonal A) (fun i => X i ω)) ∂μ) ≤
        (𝔼 δ : Fin n → Bool,
          ∫ ω, F (4 * partialChaos A (fun i => X i ω) δ) ∂μ) := hselector
    _ ≤ ∫ z : Ω × Ω', F (4 * bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
      rw [Fintype.expect_eq_sum_div_card]
      have hcard : (0 : ℝ) < Fintype.card (Fin n → Bool) := by positivity
      calc
        (∑ δ : Fin n → Bool,
              ∫ ω, F (4 * partialChaos A (fun i => X i ω) δ) ∂μ) /
            Fintype.card (Fin n → Bool)
            ≤ (∑ _δ : Fin n → Bool,
              ∫ z : Ω × Ω', F (4 * bilinearForm A
                (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν) /
              Fintype.card (Fin n → Bool) := by
          apply (div_le_div_iff_of_pos_right hcard).2
          exact Finset.sum_le_sum (fun δ _ => hcomparison δ)
        _ = ∫ z : Ω × Ω', F (4 * bilinearForm A
              (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
          simp

/-- Decoupling bounds a diagonal-free quadratic chaos by a bilinear form with an independent
copy, up to factor four under convex transforms.

**Book Theorem 6.1.1.** -/
theorem decoupling
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (F : ℝ → ℝ) (hFconv : ConvexOn ℝ Set.univ F)
    (hFcont : Continuous F)
    (hleft : Integrable (fun ω => F (quadraticForm A (fun i => X i ω))) μ)
    (hpartialInt : ∀ δ : Fin n → Bool, Integrable (fun ω =>
      F (4 * partialChaos A (fun i => X i ω) δ)) μ)
    (hright : Integrable (fun z : Ω × Ω' =>
      F (4 * bilinearForm A (fun i => X i z.1)
        (fun j => X' j z.2))) (μ.prod ν)) :
    (∫ ω, F (quadraticForm A (fun i => X i ω)) ∂μ) ≤
      ∫ z : Ω × Ω', F (4 * bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
  have hoff : offDiagonal A = A := (offDiagonal_eq_self_iff A).2 hA
  simpa [hoff] using decoupling_offDiagonal A hXm hX'm hXint hXind hX'ind
    hX0 hcopy F hFconv hFcont (by simpa [hoff] using hleft)
    hpartialInt hright

/-- Real-valued MGF form of the corresponding theorem. Integrability of the completed MGF alone
suffices; selector and quadratic-form integrability are consequences of the three-step proof.
The parameter may have either sign.

**Book Theorem 6.1.1.** -/
theorem decoupling_mgf
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (lam : ℝ)
    (hright : Integrable (fun z : Ω × Ω' =>
      Real.exp (4 * lam * bilinearForm A (fun i => X i z.1)
        (fun j => X' j z.2))) (μ.prod ν)) :
    (∫ ω, Real.exp (lam * quadraticForm A (fun i => X i ω)) ∂μ) ≤
      ∫ z : Ω × Ω', Real.exp (4 * lam * bilinearForm A
        (fun i => X i z.1) (fun j => X' j z.2)) ∂μ.prod ν := by
  let F : ℝ → ℝ := fun t => Real.exp (lam * t)
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFconv : ConvexOn ℝ Set.univ F := by
    convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ lam) using 1
  have hX'int : ∀ i, Integrable (X' i) ν := fun i =>
    (hcopy i).integrable_iff.mpr (hXint i)
  have hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0 := fun i =>
    (hcopy i).integral_eq.trans (hX0 i)
  have hpartialInt : ∀ δ : Fin n → Bool, Integrable (fun ω =>
      F (4 * partialChaos A (fun i => X i ω) δ)) μ := by
    intro δ
    have hDec := integrable_exp_decoupledPartialChaos_of_integrable_bilinear
      A hXm hX'm hXint hX'int hXind hX'ind hX0 hX'0 lam δ hright
    let G : ℝ → ℝ := fun t => Real.exp (4 * lam * t)
    have hGm : Measurable G := by
      dsimp only [G]
      fun_prop
    have hLaw := (identDistrib_partialChaos_decoupledPartialChaos
      A hXm hX'm hXind hX'ind hcopy δ).comp hGm
    have hOrig := hLaw.integrable_iff.mp hDec
    convert hOrig using 1
    funext ω
    dsimp only [F, G, Function.comp_apply]
    congr 1
    ring
  let H : Ω → ℝ := fun ω =>
    (𝔼 δ : Fin n → Bool,
      F (4 * partialChaos A (fun i => X i ω) δ))
  have hHint : Integrable H μ := by
    rw [show H = fun ω =>
        (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
          ∑ δ : Fin n → Bool,
            F (4 * partialChaos A (fun i => X i ω) δ) by
      funext ω
      simp only [H, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
      ring]
    exact (integrable_finsetSum Finset.univ
      (fun δ _ => hpartialInt δ)).const_mul _
  have hleftm : Measurable (fun ω =>
      F (quadraticForm A (fun i => X i ω))) := by
    dsimp only [F, quadraticForm, HDP.Chapter4.matrixBilinear]
    fun_prop
  have hpoint : ∀ ω,
      F (quadraticForm A (fun i => X i ω)) ≤ H ω := by
    intro ω
    exact convex_quadraticForm_le_selectorAverage A hA
      (fun i => X i ω) F hFconv
  have hleft : Integrable (fun ω =>
      F (quadraticForm A (fun i => X i ω))) μ := by
    refine hHint.mono' hleftm.aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hp := hpoint ω
    simpa [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hp
  have hmain := decoupling A hA hXm hX'm hXint hXind hX'ind hX0 hcopy
    F hFconv hFcont hleft hpartialInt (by
      convert hright using 1
      funext z
      dsimp only [F]
      congr 1
      ring)
  convert hmain using 1
  congr 1
  funext z
  dsimp only [F]
  congr 1
  ring

/-- Finiteness companion to `decoupling_mgf`: a finite completed MGF forces the original
quadratic-form MGF to be finite.

**Lean implementation helper.** -/
theorem integrable_exp_quadraticForm_of_integrable_bilinear
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (lam : ℝ)
    (hright : Integrable (fun z : Ω × Ω' =>
      Real.exp (4 * lam * bilinearForm A (fun i => X i z.1)
        (fun j => X' j z.2))) (μ.prod ν)) :
    Integrable (fun ω =>
      Real.exp (lam * quadraticForm A (fun i => X i ω))) μ := by
  let F : ℝ → ℝ := fun t => Real.exp (lam * t)
  have hFconv : ConvexOn ℝ Set.univ F := by
    convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ lam) using 1
  have hX'int : ∀ i, Integrable (X' i) ν := fun i =>
    (hcopy i).integrable_iff.mpr (hXint i)
  have hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0 := fun i =>
    (hcopy i).integral_eq.trans (hX0 i)
  have hpartialInt : ∀ δ : Fin n → Bool, Integrable (fun ω =>
      F (4 * partialChaos A (fun i => X i ω) δ)) μ := by
    intro δ
    have hDec := integrable_exp_decoupledPartialChaos_of_integrable_bilinear
      A hXm hX'm hXint hX'int hXind hX'ind hX0 hX'0 lam δ hright
    let G : ℝ → ℝ := fun t => Real.exp (4 * lam * t)
    have hGm : Measurable G := by
      dsimp only [G]
      fun_prop
    have hLaw := (identDistrib_partialChaos_decoupledPartialChaos
      A hXm hX'm hXind hX'ind hcopy δ).comp hGm
    have hOrig := hLaw.integrable_iff.mp hDec
    convert hOrig using 1
    funext ω
    dsimp only [F, G, Function.comp_apply]
    congr 1
    ring
  let H : Ω → ℝ := fun ω =>
    (𝔼 δ : Fin n → Bool,
      F (4 * partialChaos A (fun i => X i ω) δ))
  have hHint : Integrable H μ := by
    rw [show H = fun ω =>
        (Fintype.card (Fin n → Bool) : ℝ)⁻¹ *
          ∑ δ : Fin n → Bool,
            F (4 * partialChaos A (fun i => X i ω) δ) by
      funext ω
      simp only [H, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
      ring]
    exact (integrable_finsetSum Finset.univ
      (fun δ _ => hpartialInt δ)).const_mul _
  have hleftm : Measurable (fun ω =>
      F (quadraticForm A (fun i => X i ω))) := by
    dsimp only [F, quadraticForm, HDP.Chapter4.matrixBilinear]
    fun_prop
  have hpoint : ∀ ω,
      F (quadraticForm A (fun i => X i ω)) ≤ H ω := by
    intro ω
    exact convex_quadraticForm_le_selectorAverage A hA
      (fun i => X i ω) F hFconv
  have hleft : Integrable (fun ω =>
      F (quadraticForm A (fun i => X i ω))) μ := by
    refine hHint.mono' hleftm.aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hp := hpoint ω
    simpa [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hp
  exact hleft

/-- Extended-valued MGF decoupling. Unlike a real-integral wrapper, this statement remains valid
when the completed MGF is infinite, so it can be used directly in Hanson--Wright without a
separate finiteness split.

**Book Theorem 6.1.1.** -/
theorem decoupling_mgf_lintegral
    {n : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    {X : Fin n → Ω → ℝ} {X' : Fin n → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX'm : ∀ i, Measurable (X' i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hXind : iIndepFun X μ) (hX'ind : iIndepFun X' ν)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hcopy : ∀ i, IdentDistrib (X' i) (X i) ν μ)
    (lam : ℝ) :
    (∫⁻ ω, ENNReal.ofReal
      (Real.exp (lam * quadraticForm A (fun i => X i ω))) ∂μ) ≤
      ∫⁻ z : Ω × Ω', ENNReal.ofReal
        (Real.exp (4 * lam * bilinearForm A
          (fun i => X i z.1) (fun j => X' j z.2))) ∂μ.prod ν := by
  let f : (Ω × Ω') → ℝ := fun z =>
    Real.exp (4 * lam * bilinearForm A
      (fun i => X i z.1) (fun j => X' j z.2))
  have hfm : Measurable f := by
    dsimp only [f, bilinearForm, HDP.Chapter4.matrixBilinear]
    fun_prop
  by_cases hf : Integrable f (μ.prod ν)
  · have hf' : Integrable (fun z : Ω × Ω' =>
        Real.exp (4 * lam * bilinearForm A
          (fun i => X i z.1) (fun j => X' j z.2))) (μ.prod ν) := by
      simpa [f] using hf
    have hl := integrable_exp_quadraticForm_of_integrable_bilinear
      A hA hXm hX'm hXint hXind hX'ind hX0 hcopy lam hf'
    have hreal := decoupling_mgf A hA hXm hX'm hXint hXind hX'ind
      hX0 hcopy lam hf'
    rw [← ofReal_integral_eq_lintegral_ofReal hl
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      ← ofReal_integral_eq_lintegral_ofReal hf'
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hnotFinite : ¬ HasFiniteIntegral f (μ.prod ν) := by
      intro hfin
      exact hf ⟨hfm.aestronglyMeasurable, hfin⟩
    have hnotlt : ¬ (∫⁻ z : Ω × Ω', ENNReal.ofReal ‖f z‖ ∂μ.prod ν) < ⊤ := by
      intro hlt
      exact hnotFinite ((hasFiniteIntegral_iff_norm f).2 hlt)
    have htopNorm : (∫⁻ z : Ω × Ω', ENNReal.ofReal ‖f z‖ ∂μ.prod ν) = ⊤ :=
      not_lt_top_iff.mp hnotlt
    have hfnorm : ∀ z : Ω × Ω', ‖f z‖ = f z := by
      intro z
      rw [Real.norm_eq_abs, abs_of_pos]
      exact Real.exp_pos _
    have htop : (∫⁻ z : Ω × Ω', ENNReal.ofReal (f z) ∂μ.prod ν) = ⊤ := by
      simpa only [hfnorm] using htopNorm
    change (∫⁻ ω, ENNReal.ofReal
      (Real.exp (lam * quadraticForm A (fun i => X i ω))) ∂μ) ≤
        ∫⁻ z : Ω × Ω', ENNReal.ofReal (f z) ∂μ.prod ν
    rw [htop]
    exact le_top

/-- Exercise 6.1, retained as a source-numbered core declaration because it
is used by the Hanson--Wright proof later in the chapter. -/
abbrev exercise_6_1 := @decoupling_offDiagonal

/-- Decoupling after the two probabilistic comparison steps have been supplied. This theorem
isolates the selector/Jensen argument from the product-law lemma that replaces and then
completes every partial chaos.

**Lean implementation helper.** -/
theorem decoupling_of_partial_comparison
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsDiagonalFree A)
    (X X' : Fin n → Omega → ℝ) (F : ℝ → ℝ)
    (hF : ConvexOn ℝ Set.univ F)
    (hleft : Integrable
      (fun omega => F (quadraticForm A (fun i => X i omega))) mu)
    (hpartialInt : ∀ δ : Fin n → Bool, Integrable
      (fun omega => F (4 * partialChaos A (fun i => X i omega) δ)) mu)
    (hpartial : ∀ δ : Fin n → Bool,
      (∫ omega, F (4 * partialChaos A (fun i => X i omega) δ) ∂mu) ≤
        ∫ omega, F (4 * bilinearForm A
          (fun i => X i omega) (fun j => X' j omega)) ∂mu) :
    (∫ omega, F (quadraticForm A (fun i => X i omega)) ∂mu) ≤
      ∫ omega, F (4 * bilinearForm A
        (fun i => X i omega) (fun j => X' j omega)) ∂mu := by
  calc
    (∫ omega, F (quadraticForm A (fun i => X i omega)) ∂mu)
        ≤ (𝔼 δ : Fin n → Bool,
          ∫ omega, F (4 * partialChaos A (fun i => X i omega) δ) ∂mu) :=
      integral_convex_quadraticForm_le_selectorAverage mu A hA X F hF
        hleft hpartialInt
    _ ≤ ∫ omega, F (4 * bilinearForm A
        (fun i => X i omega) (fun j => X' j omega)) ∂mu := by
      rw [Fintype.expect_eq_sum_div_card]
      have hcard : (0 : ℝ) < Fintype.card (Fin n → Bool) := by positivity
      calc
        (∑ δ : Fin n → Bool,
              ∫ omega, F (4 * partialChaos A (fun i => X i omega) δ) ∂mu) /
            Fintype.card (Fin n → Bool)
            ≤ (∑ _δ : Fin n → Bool,
              ∫ omega, F (4 * bilinearForm A
                (fun i => X i omega) (fun j => X' j omega)) ∂mu) /
              Fintype.card (Fin n → Bool) := by
          apply (div_le_div_iff_of_pos_right hcard).2
          exact Finset.sum_le_sum (fun δ _ => hpartial δ)
        _ = ∫ omega, F (4 * bilinearForm A
              (fun i => X i omega) (fun j => X' j omega)) ∂mu := by
          simp

end

end HDP.Chapter6

end Source_02_Decoupling

/-! ## Material formerly in `03_SubGaussianVectorNorm.lean` -/

section Source_03_SubGaussianVectorNorm

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace HDP.Chapter6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A vector written as a matrix with one row.

**Lean implementation helper.** -/
def vectorRowMatrix {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    Ω → Matrix (Fin 1) (Fin n) ℝ :=
  fun ω _ j => X ω j

/-- The sole row of `vectorRowMatrix X ω` is the vector `X ω` itself.

**Lean implementation helper.** -/
@[simp] lemma vectorRowMatrix_apply {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω)
    (i : Fin 1) (j : Fin n) :
    vectorRowMatrix X ω i j = X ω j := rfl

/-- The operator norm of a one-row matrix is the Euclidean norm of its row vector.

**Lean implementation helper.** -/
lemma matrixOpNorm_vectorRowMatrix {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    HDP.matrixOpNorm (vectorRowMatrix X ω) = ‖X ω‖ := by
  have horth : ∀ i j : Fin 1, i ≠ j →
      inner ℝ
        (WithLp.toLp 2 ((vectorRowMatrix X ω).row i) :
          EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 ((vectorRowMatrix X ω).row j) :
          EuclideanSpace ℝ (Fin n)) = 0 := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  rw [HDP.Chapter4.exercise_4_7c_row_eq_of_pairwise_orthogonal
    (vectorRowMatrix X ω) horth]
  obtain ⟨i, hi⟩ :=
    HDP.Chapter4.exists_row_eq_maxRowL2Norm (vectorRowMatrix X ω)
  rw [← hi]
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst i
  congr 1

/-- The bilinear form of a one-row random matrix is `y₀` times the inner product of its row with `x`.

**Lean implementation helper.** -/
lemma randomMatrixBilinear_vectorRowMatrix {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin 1)) (ω : Ω) :
    HDP.Chapter4.RandomMatrixBounds.randomMatrixBilinear
        (vectorRowMatrix X) x y ω =
      y 0 * inner ℝ (X ω) x := by
  simp only [HDP.Chapter4.RandomMatrixBounds.randomMatrixBilinear,
    vectorRowMatrix_apply, Fin.sum_univ_one]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Derives abs random matrix bilinear vector row matrix from unit.

**Lean implementation helper.** -/
lemma abs_randomMatrixBilinear_vectorRowMatrix_of_unit {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin 1)) (hy : ‖y‖ = 1) (ω : Ω) :
    |HDP.Chapter4.RandomMatrixBounds.randomMatrixBilinear
        (vectorRowMatrix X) x y ω| =
      |inner ℝ (X ω) x| := by
  rw [randomMatrixBilinear_vectorRowMatrix, abs_mul]
  have hySq := EuclideanSpace.real_norm_sq_eq y
  have hy0sq : y 0 ^ 2 = 1 := by
    simpa [hy] using hySq.symm
  have hay : |y 0| = 1 := by
    nlinarith [sq_abs (y 0), abs_nonneg (y 0)]
  rw [hay, one_mul]

/-- A one-row random matrix inherits the fixed-marginal subgaussian tail bound `2 exp(-u²/(30K²))` from its row vector.

**Lean implementation helper.** -/
private lemma fixed_marginal_tail_for_vectorRowMatrix
    [IsProbabilityMeasure μ]
    {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (hXm : AEMeasurable X μ)
    (hsub : HDP.SubGaussianVector X μ)
    (hbounded : BddAbove {r : ℝ |
      ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (X ω) v) μ})
    {K : ℝ} (hK : 0 < K)
    (hpsi : HDP.psi2NormVector X μ ≤ K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    (y : EuclideanSpace ℝ (Fin 1)) (hy : ‖y‖ = 1)
    (u : ℝ) (hu : 0 ≤ u) :
    μ {ω | u ≤
        |HDP.Chapter4.RandomMatrixBounds.randomMatrixBilinear
          (vectorRowMatrix X) x y ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by
  have hmarg : AEMeasurable (fun ω => inner ℝ (X ω) x) μ := by
    have hc : Continuous
        (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ z x) := by fun_prop
    exact hc.aemeasurable.comp_aemeasurable hXm
  have hnorm : HDP.psi2Norm (fun ω => inner ℝ (X ω) x) μ ≤ K :=
    (HDP.psi2Norm_marginal_le_vector hbounded hx).trans hpsi
  have hmgf := HDP.psi2MGF_le_two_of_ge hmarg (hsub x) hnorm hK
  have htail := HDP.subgaussian_iii_to_i hmarg hK hmgf hu
  rw [show {ω | u ≤
      |HDP.Chapter4.RandomMatrixBounds.randomMatrixBilinear
        (vectorRowMatrix X) x y ω|} =
      {ω | u ≤ |inner ℝ (X ω) x|} by
        ext ω
        simp only [Set.mem_setOf_eq]
        rw [abs_randomMatrixBilinear_vectorRowMatrix_of_unit X x y hy ω]]
  calc
    μ {ω | u ≤ |inner ℝ (X ω) x|}
        ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / K ^ 2)) := htail
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (30 * K ^ 2))) := by
      apply ENNReal.ofReal_le_ofReal
      have hKsq : 0 < K ^ 2 := sq_pos_of_pos hK
      have hden : K ^ 2 ≤ 30 * K ^ 2 := by nlinarith
      have hfrac : u ^ 2 / (30 * K ^ 2) ≤ u ^ 2 / K ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg u) hKsq hden
      have hexp : -u ^ 2 / K ^ 2 ≤ -u ^ 2 / (30 * K ^ 2) := by
        simpa only [neg_div] using neg_le_neg hfrac
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexp) (by norm_num)

/-- Explicit-constant form of the corresponding proposition.

**Book Proposition 6.2.1.** -/
theorem subGaussianVector_norm_tail_explicit
    [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hXm : AEMeasurable X μ)
    (hsub : HDP.SubGaussianVector X μ)
    (hbounded : BddAbove {r : ℝ |
      ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (X ω) v) μ})
    {K : ℝ} (hK : 0 < K)
    (hpsi : HDP.psi2NormVector X μ ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 300 * K * (Real.sqrt n + t) ≤ ‖X ω‖} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let s : ℝ := Real.sqrt (t ^ 2 + Real.log 2)
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = t ^ 2 + Real.log 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hslt : s < t + 1 := by
    have hloglt : Real.log 2 < 1 := by
      nlinarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)]
    nlinarith
  have hsqrtN : 1 ≤ Real.sqrt n := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.one_le_sqrt.mpr hnR
  have hthreshold :
      100 * K * (1 + Real.sqrt n + s) <
        300 * K * (Real.sqrt n + t) := by
    nlinarith
  have hmat :=
    HDP.Chapter4.matrixOpNorm_tail_of_fixed_bilinear_tail
      (μ := μ) (vectorRowMatrix X) hK
      (fixed_marginal_tail_for_vectorRowMatrix X hXm hsub hbounded hK hpsi)
      hs0
  have hmat' :
      μ {ω | 100 * K * (1 + Real.sqrt n + s) <
          HDP.matrixOpNorm (vectorRowMatrix X ω)} ≤
        ENNReal.ofReal (2 * Real.exp (-s ^ 2)) := by
    simpa using hmat
  have hsubset :
      {ω | 300 * K * (Real.sqrt n + t) ≤ ‖X ω‖} ⊆
        {ω | 100 * K * (1 + Real.sqrt n + s) <
          HDP.matrixOpNorm (vectorRowMatrix X ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [matrixOpNorm_vectorRowMatrix]
    exact hthreshold.trans_le hω
  calc
    μ {ω | 300 * K * (Real.sqrt n + t) ≤ ‖X ω‖}
        ≤ μ {ω | 100 * K * (1 + Real.sqrt n + s) <
          HDP.matrixOpNorm (vectorRowMatrix X ω)} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (2 * Real.exp (-s ^ 2)) := hmat'
    _ = ENNReal.ofReal (Real.exp (-t ^ 2)) := by
      congr 1
      have hexpNegLog : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
        calc
          Real.exp (-(Real.log 2)) = (Real.exp (Real.log 2))⁻¹ :=
            Real.exp_neg (Real.log 2)
          _ = (2 : ℝ)⁻¹ := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = 1 / 2 := by norm_num
      rw [hsSq]
      rw [show -(t ^ 2 + Real.log 2) = -t ^ 2 + -(Real.log 2) by ring,
        Real.exp_add, hexpNegLog]
      ring

/-- The norm of a subgaussian random vector concentrates around `sqrt n` with a subgaussian
tail.

**Book Proposition 6.2.1.** -/
theorem proposition_6_2_1
    [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 0 < n →
      ∀ (X : Ω → EuclideanSpace ℝ (Fin n)),
      AEMeasurable X μ → Integrable X μ →
      (∫ ω, X ω ∂μ) = 0 →
      HDP.SubGaussianVector X μ →
      BddAbove {r : ℝ |
        ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
          r = HDP.psi2Norm (fun ω => inner ℝ (X ω) v) μ} →
      ∀ {K : ℝ}, 0 < K → HDP.psi2NormVector X μ ≤ K →
      ∀ {t : ℝ}, 0 ≤ t →
        μ {ω | C * K * (Real.sqrt n + t) ≤ ‖X ω‖} ≤
          ENNReal.ofReal (Real.exp (-t ^ 2)) := by
  refine ⟨300, by norm_num, ?_⟩
  intro n hn X hXm hXint hmean hsub hbounded K hK hpsi t ht
  exact subGaussianVector_norm_tail_explicit hn X hXm hsub hbounded hK hpsi ht

end HDP.Chapter6

end Source_03_SubGaussianVectorNorm

/-! ## Material formerly in `04_GaussianReplacement.lean` -/

section Source_04_GaussianReplacement

/-!
# Chapter 6, §6.2: Gaussian replacement

This file proves the one-vector exponential-moment comparison underlying
Lemma 6.2.3.  Extended nonnegative integrals are authoritative here, so the
statement remains meaningful for every parameter, including outside the
finite MGF range of the eventual Gaussian bilinear form.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter6

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A vector-valued random variable is centered in the Bochner sense.

**Lean implementation helper.** -/
def IsCenteredVector {n : ℕ}
    (X : Omega → EuclideanSpace ℝ (Fin n)) (mu : Measure Omega) : Prop :=
  Integrable X mu ∧ ∫ omega, X omega ∂mu = 0

/-- A Bochner-centered vector has centered scalar marginals.

**Lean implementation helper.** -/
lemma IsCenteredVector.integral_inner_eq_zero {n : ℕ}
    {X : Omega → EuclideanSpace ℝ (Fin n)}
    (hX : IsCenteredVector X mu) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ omega, ⟪X omega, v⟫ ∂mu = 0 := by
  have hcomm := ((innerSL ℝ) v).integral_comp_comm hX.1
  rw [hX.2] at hcomm
  simpa [real_inner_comm] using hcomm

/-- Explicit scalar MGF bound for a marginal of a subgaussian vector whose vector `psi2` norm is
at most `K`.

**Lean implementation helper.** -/
theorem subGaussianVector_mgf_bound
    [IsProbabilityMeasure mu] {n : ℕ}
    {X : Omega → EuclideanSpace ℝ (Fin n)}
    (hXm : AEMeasurable X mu)
    (hsub : HDP.SubGaussianVector X mu)
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun omega => ⟪X omega, u⟫) mu})
    (hcenter : IsCenteredVector X mu)
    {K : ℝ} (hK : 0 ≤ K)
    (hpsi : HDP.psi2NormVector X mu ≤ K)
    (v : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * ⟪X omega, v⟫)) ∂mu ≤
      ENNReal.ofReal
        (Real.exp ((3 / 2) * K ^ 2 * ‖v‖ ^ 2 * lam ^ 2)) := by
  have hmarg : AEMeasurable (fun omega => ⟪X omega, v⟫) mu :=
    (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, v⟫))
      |>.aemeasurable.comp_aemeasurable hXm
  have hnorm := HDP.Chapter3.psi2Norm_marginal_le_norm_mul_vector
    hbounded v
  have hnormK : HDP.psi2Norm (fun omega => ⟪X omega, v⟫) mu ≤ ‖v‖ * K :=
    hnorm.trans (mul_le_mul_of_nonneg_left hpsi (norm_nonneg v))
  have hnorm0 : 0 ≤ HDP.psi2Norm (fun omega => ⟪X omega, v⟫) mu :=
    HDP.psi2Norm_nonneg _ _
  have hright0 : 0 ≤ ‖v‖ * K := mul_nonneg (norm_nonneg v) hK
  have hsquare :
      HDP.psi2Norm (fun omega => ⟪X omega, v⟫) mu ^ 2 ≤
        (‖v‖ * K) ^ 2 :=
    (sq_le_sq₀ hnorm0 hright0).2 hnormK
  have hmgf := (hsub v).mgf_bound hmarg (hcenter.integral_inner_eq_zero v) lam
  refine hmgf.trans (ENNReal.ofReal_le_ofReal ?_)
  apply Real.exp_le_exp.mpr
  have hlam2 : 0 ≤ lam ^ 2 := sq_nonneg lam
  calc
    (3 / 2) * HDP.psi2Norm (fun omega => ⟪X omega, v⟫) mu ^ 2 * lam ^ 2
        ≤ (3 / 2) * (‖v‖ * K) ^ 2 * lam ^ 2 := by gcongr
    _ = (3 / 2) * K ^ 2 * ‖v‖ ^ 2 * lam ^ 2 := by ring

/-- Exact MGF of a standard Gaussian marginal, in extended-integral form.

**Book (6.10).** -/
theorem standardGaussian_inner_lmgf {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    ∫⁻ g : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (Real.exp (lam * ⟪g, v⟫))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
      ENNReal.ofReal (Real.exp (lam ^ 2 * ‖v‖ ^ 2 / 2)) := by
  have hLaw : HasLaw (fun g : EuclideanSpace ℝ (Fin n) => ⟪g, v⟫)
      (gaussianReal 0 (HDP.Chapter3.gaussianMarginalVariance v))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [real_inner_comm] using
      (HDP.Chapter3.standardGaussian_inner_hasLaw v)
  have hintBase := integrable_exp_mul_gaussianReal
    (μ := (0 : ℝ))
    (v := HDP.Chapter3.gaussianMarginalVariance v) lam
  rw [← hLaw.map_eq] at hintBase
  have hint : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) => Real.exp (lam * ⟪g, v⟫))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    hintBase.comp_aemeasurable hLaw.aemeasurable
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  congr 1
  change mgf (fun g : EuclideanSpace ℝ (Fin n) => ⟪g, v⟫)
    (stdGaussian (EuclideanSpace ℝ (Fin n))) lam = _
  rw [mgf_gaussianReal hLaw.map_eq]
  simp [HDP.Chapter3.gaussianMarginalVariance]
  ring_nf

/-- One replacement step: a centered subgaussian vector is dominated, for linear exponential
moments, by a standard Gaussian after the explicit factor `sqrt 3 * K`.

**Book (6.9).** -/
theorem subGaussianVector_lmgf_le_gaussian
    [IsProbabilityMeasure mu] {n : ℕ}
    {X : Omega → EuclideanSpace ℝ (Fin n)}
    (hXm : AEMeasurable X mu)
    (hsub : HDP.SubGaussianVector X mu)
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun omega => ⟪X omega, u⟫) mu})
    (hcenter : IsCenteredVector X mu)
    {K : ℝ} (hK : 0 ≤ K)
    (hpsi : HDP.psi2NormVector X mu ≤ K)
    (v : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp (lam * ⟪X omega, v⟫)) ∂mu) ≤
      ∫⁻ g : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal
          (Real.exp ((Real.sqrt 3 * K * lam) * ⟪g, v⟫))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [standardGaussian_inner_lmgf]
  refine (subGaussianVector_mgf_bound hXm hsub hbounded hcenter hK hpsi v lam).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  rw [mul_pow, mul_pow, hsqrt]
  ring_nf
  exact le_rfl

/-! ## Two-vector replacement -/

/-- Let `X` and `X'` live on separate probability spaces, so their independence is structural.
If both centered vectors have vector psi-two norm at most `K`, then the exponential moment of
the bilinear form is bounded by that of two independent standard Gaussian vectors after the
factor `3 K^2`. The theorem is stated with extended nonnegative integrals. Consequently it is
valid for every real `lam`, without a hidden integrability assumption.

**Book Lemma 6.2.3.** -/
theorem gaussianReplacement
    {Omega' : Type*} [MeasurableSpace Omega'] {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu'] {n : ℕ}
    {X : Omega → EuclideanSpace ℝ (Fin n)}
    {X' : Omega' → EuclideanSpace ℝ (Fin n)}
    (hXm : Measurable X) (hX'm : Measurable X')
    (hsub : HDP.SubGaussianVector X mu)
    (hsub' : HDP.SubGaussianVector X' mu')
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun omega ↦ ⟪X omega, u⟫) mu})
    (hbounded' : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun omega ↦ ⟪X' omega, u⟫) mu'})
    (hcenter : IsCenteredVector X mu)
    (hcenter' : IsCenteredVector X' mu')
    {K : ℝ} (hK : 0 ≤ K)
    (hpsi : HDP.psi2NormVector X mu ≤ K)
    (hpsi' : HDP.psi2NormVector X' mu' ≤ K)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : ℝ) :
    (∫⁻ z : Omega × Omega',
        ENNReal.ofReal (Real.exp (lam * ⟪X z.1, A (X' z.2)⟫))
      ∂(mu.prod mu')) ≤
      ∫⁻ z : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal
          (Real.exp ((3 * K ^ 2 * lam) * ⟪z.1, A z.2⟫))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let gammaE : Measure E := stdGaussian E
  have horig : AEMeasurable
      (fun z : Omega × Omega' ↦
        ENNReal.ofReal (Real.exp (lam * ⟪X z.1, A (X' z.2)⟫)))
      (mu.prod mu') := by
    fun_prop
  have hfirst : AEMeasurable
      (fun z : Omega × E ↦
        ENNReal.ofReal
          (Real.exp ((Real.sqrt 3 * K * lam) *
            ⟪z.2, LinearMap.adjoint A (X z.1)⟫)))
      (mu.prod gammaE) := by
    fun_prop
  have hgauss : AEMeasurable
      (fun z : E × E ↦
        ENNReal.ofReal
          (Real.exp ((3 * K ^ 2 * lam) * ⟪z.1, A z.2⟫)))
      (gammaE.prod gammaE) := by
    fun_prop
  have hinnerOriginal (x : Omega) (y : Omega') :
      ⟪X x, A (X' y)⟫ =
        ⟪X' y, LinearMap.adjoint A (X x)⟫ := by
    simpa [real_inner_comm] using
      (A.adjoint_inner_left (X' y) (X x)).symm
  have hinnerFirst (x : Omega) (g : E) :
      ⟪g, LinearMap.adjoint A (X x)⟫ = ⟪X x, A g⟫ := by
    simpa [real_inner_comm] using A.adjoint_inner_left g (X x)
  have hcoefficient :
      Real.sqrt 3 * K * (Real.sqrt 3 * K * lam) = 3 * K ^ 2 * lam := by
    have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by norm_num
    calc
      Real.sqrt 3 * K * (Real.sqrt 3 * K * lam) =
          (Real.sqrt 3) ^ 2 * K ^ 2 * lam := by ring
      _ = 3 * K ^ 2 * lam := by rw [hsqrt]
  rw [MeasureTheory.lintegral_prod _ horig]
  calc
    (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (Real.exp (lam * ⟪X x, A (X' y)⟫)) ∂mu' ∂mu) ≤
        ∫⁻ x, ∫⁻ g : E,
          ENNReal.ofReal
            (Real.exp ((Real.sqrt 3 * K * lam) *
              ⟪g, LinearMap.adjoint A (X x)⟫)) ∂gammaE ∂mu := by
      apply lintegral_mono
      intro x
      simpa only [hinnerOriginal x] using
        (subGaussianVector_lmgf_le_gaussian
          hX'm.aemeasurable hsub' hbounded' hcenter' hK hpsi'
          (LinearMap.adjoint A (X x)) lam)
    _ = ∫⁻ g : E, ∫⁻ x,
          ENNReal.ofReal
            (Real.exp ((Real.sqrt 3 * K * lam) *
              ⟪g, LinearMap.adjoint A (X x)⟫)) ∂mu ∂gammaE := by
      exact (MeasureTheory.lintegral_prod _ hfirst).symm.trans
        (MeasureTheory.lintegral_prod_symm _ hfirst)
    _ ≤ ∫⁻ g' : E, ∫⁻ g : E,
          ENNReal.ofReal
            (Real.exp ((3 * K ^ 2 * lam) * ⟪g, A g'⟫))
          ∂gammaE ∂gammaE := by
      apply lintegral_mono
      intro g'
      calc
        (∫⁻ x,
            ENNReal.ofReal
              (Real.exp ((Real.sqrt 3 * K * lam) *
                ⟪g', LinearMap.adjoint A (X x)⟫)) ∂mu) =
            ∫⁻ x,
              ENNReal.ofReal
                (Real.exp ((Real.sqrt 3 * K * lam) * ⟪X x, A g'⟫)) ∂mu := by
          apply lintegral_congr
          intro x
          rw [hinnerFirst]
        _ ≤ ∫⁻ g : E,
              ENNReal.ofReal
                (Real.exp
                  ((Real.sqrt 3 * K * (Real.sqrt 3 * K * lam)) *
                    ⟪g, A g'⟫)) ∂gammaE :=
          subGaussianVector_lmgf_le_gaussian
            hXm.aemeasurable hsub hbounded hcenter hK hpsi
            (A g') (Real.sqrt 3 * K * lam)
        _ = ∫⁻ g : E,
              ENNReal.ofReal
                (Real.exp ((3 * K ^ 2 * lam) * ⟪g, A g'⟫)) ∂gammaE := by
          simp only [hcoefficient]
    _ = ∫⁻ z : E × E,
          ENNReal.ofReal
            (Real.exp ((3 * K ^ 2 * lam) * ⟪z.1, A z.2⟫))
          ∂(gammaE.prod gammaE) := by
      exact (MeasureTheory.lintegral_prod_symm _ hgauss).symm

end

end HDP.Chapter6

end Source_04_GaussianReplacement

/-! ## Material formerly in `05_GaussianQuadraticMGF.lean` -/

section Source_05_GaussianQuadraticMGF

/-!
# Chapter 6, §6.2: Gaussian product and bilinear MGFs

This file proves the scalar product-normal computation used in (6.11).  The
proof is an actual Fubini calculation and explicitly verifies the integrability
range, which the source leaves implicit.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter6

noncomputable section

local notation "gamma" => gaussianReal 0 1

/-- Simplified square-exponential MGF of a standard Gaussian.

**Lean implementation helper.** -/
theorem standardGaussian_sq_mgf {a : ℝ} (ha : a < 1 / 2) :
    (∫ x : ℝ, Real.exp (a * x ^ 2) ∂gamma) =
      1 / Real.sqrt (1 - 2 * a) := by
  rw [HDP.Chapter2.integral_exp_sq_mul_standardGaussian ha]
  have hd : 0 < 1 - 2 * a := by linarith
  have hden : 1 / 2 - a = (1 - 2 * a) / 2 := by ring
  rw [hden]
  have hfrac : Real.pi / ((1 - 2 * a) / 2) =
      (2 * Real.pi) / (1 - 2 * a) := by
    field_simp
  rw [hfrac, Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  field_simp

/-- Integrability of the product-normal exponential in its exact domain.

**Lean implementation helper.** -/
theorem integrable_exp_product_standardGaussian {t : ℝ} (ht : t ^ 2 < 1) :
    Integrable (fun z : ℝ × ℝ => Real.exp (t * z.1 * z.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have ha : t ^ 2 / 2 < 1 / 2 := by linarith
  apply (integrable_prod_iff (by fun_prop)).2
  constructor
  · filter_upwards with x
    simpa [mul_assoc] using
      (integrable_exp_mul_gaussianReal (μ := (0 : ℝ))
        (v := (1 : NNReal)) (t * x))
  · have hsq := HDP.Chapter2.integrable_exp_sq_mul_standardGaussian ha
    convert hsq using 1
    funext x
    have hinner :
        (∫ y : ℝ, ‖Real.exp (t * x * y)‖ ∂gamma) =
          Real.exp ((t * x) ^ 2 / 2) := by
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      change mgf id (gaussianReal 0 1) (t * x) = _
      rw [mgf_id_gaussianReal]
      norm_num
    rw [hinner]
    congr 1
    ring

/-- Exact MGF of the product of two independent standard Gaussians.

**Lean implementation helper.** -/
theorem productStandardGaussian_mgf {t : ℝ} (ht : t ^ 2 < 1) :
    (∫ z : ℝ × ℝ, Real.exp (t * z.1 * z.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      1 / Real.sqrt (1 - t ^ 2) := by
  have hint := integrable_exp_product_standardGaussian ht
  rw [integral_prod _ hint]
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, Real.exp (t * x * y) ∂gamma) =
        Real.exp ((t ^ 2 / 2) * x ^ 2) := by
    intro x
    change mgf id (gaussianReal 0 1) (t * x) = _
    rw [mgf_id_gaussianReal]
    norm_num
    ring
  simp_rw [hinner]
  have h := standardGaussian_sq_mgf (a := t ^ 2 / 2) (by linarith)
  rw [h]
  congr 2
  ring

/-- Bounds inv one sub by exp two.

**Lean implementation helper.** -/
private lemma inv_one_sub_le_exp_two {u : ℝ}
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    1 / (1 - u) ≤ Real.exp (2 * u) := by
  have hd : 0 < 1 - u := by linarith
  have hinv : 0 < (1 - u)⁻¹ := inv_pos.mpr hd
  have hlog := Real.log_le_sub_one_of_pos hinv
  have hfrac : (1 - u)⁻¹ - 1 = u / (1 - u) := by
    field_simp
    ring
  have hratio : u / (1 - u) ≤ 2 * u := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hlogle : Real.log ((1 - u)⁻¹) ≤ 2 * u := by
    rw [hfrac] at hlog
    exact hlog.trans hratio
  calc
    1 / (1 - u) = Real.exp (Real.log ((1 - u)⁻¹)) := by
      simpa only [one_div] using (Real.exp_log hinv).symm
    _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr hlogle

/-- The elementary bound in the proof of the corresponding lemma: `(1-t²)^{-1/2} ≤ exp(t²)` for
`t² ≤ 1/2`.

**Lean implementation helper.** -/
theorem invSqrt_one_sub_sq_le_exp_sq {t : ℝ} (ht : t ^ 2 ≤ 1 / 2) :
    1 / Real.sqrt (1 - t ^ 2) ≤ Real.exp (t ^ 2) := by
  have hu : 0 ≤ t ^ 2 := sq_nonneg t
  have hd : 0 < 1 - t ^ 2 := by linarith
  have hbase := inv_one_sub_le_exp_two hu ht
  have hsqrt := Real.sqrt_le_sqrt hbase
  have hleft : Real.sqrt (1 / (1 - t ^ 2)) =
      1 / Real.sqrt (1 - t ^ 2) := by
    simpa only [one_div] using Real.sqrt_inv (1 - t ^ 2)
  have hright : Real.sqrt (Real.exp (2 * t ^ 2)) = Real.exp (t ^ 2) := by
    calc
      Real.sqrt (Real.exp (2 * t ^ 2)) = Real.exp ((2 * t ^ 2) / 2) :=
        (Real.exp_half _).symm
      _ = Real.exp (t ^ 2) := by ring_nf
  simpa [hleft, hright] using hsqrt

/-- Scalar endpoint of the corresponding lemma, including exact MGF and source constant.

**Lean implementation helper.** -/
theorem productStandardGaussian_mgf_le {t : ℝ} (ht : t ^ 2 ≤ 1 / 2) :
    (∫ z : ℝ × ℝ, Real.exp (t * z.1 * z.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      Real.exp (t ^ 2) := by
  have ht1 : t ^ 2 < 1 := lt_of_le_of_lt ht (by norm_num)
  rw [productStandardGaussian_mgf ht1]
  exact invSqrt_one_sub_sq_le_exp_sq ht

/-! ## Finite diagonal Gaussian products -/

/-- Exact factorization of the MGF of a diagonal Gaussian bilinear form. Each coordinate of the
canonical product measure is a pair of independent standard Gaussians. This is equation (6.11)
after singular-value diagonalization.

**Book (6.11).** -/
theorem gaussianDiagonal_mgf {n : ℕ} (s : Fin n → ℝ) (lam : ℝ)
    (hsmall : ∀ i, (lam * s i) ^ 2 < 1) :
    (∫ z : Fin n → ℝ × ℝ,
        Real.exp (lam * ∑ i, s i * (z i).1 * (z i).2)
      ∂Measure.pi (fun _ : Fin n =>
        (gaussianReal 0 1).prod (gaussianReal 0 1))) =
      ∏ i, 1 / Real.sqrt (1 - (lam * s i) ^ 2) := by
  rw [show (fun z : Fin n → ℝ × ℝ =>
      Real.exp (lam * ∑ i, s i * (z i).1 * (z i).2)) =
      fun z => ∏ i, Real.exp ((lam * s i) * (z i).1 * (z i).2) by
    funext z
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  calc
    (∫ z : Fin n → ℝ × ℝ,
        ∏ i, Real.exp ((lam * s i) * (z i).1 * (z i).2)
      ∂Measure.pi (fun _ : Fin n =>
        (gaussianReal 0 1).prod (gaussianReal 0 1))) =
        ∏ i, ∫ z : ℝ × ℝ,
          Real.exp ((lam * s i) * z.1 * z.2)
            ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : Fin n =>
          (gaussianReal 0 1).prod (gaussianReal 0 1))
        (fun i (z : ℝ × ℝ) =>
          Real.exp ((lam * s i) * z.1 * z.2))
    _ = ∏ i, 1 / Real.sqrt (1 - (lam * s i) ^ 2) := by
      apply Finset.prod_congr rfl
      intro i _
      exact productStandardGaussian_mgf (hsmall i)

/-- Product-normal MGF bound in singular coordinates. The hypothesis is kept coordinatewise; the
matrix norm reduction is supplied by `gaussianBilinear_mgf` below.

**Lean implementation helper.** -/
theorem gaussianDiagonal_mgf_le {n : ℕ} (s : Fin n → ℝ) (lam : ℝ)
    (hsmall : ∀ i, (lam * s i) ^ 2 ≤ 1 / 2) :
    (∫ z : Fin n → ℝ × ℝ,
        Real.exp (lam * ∑ i, s i * (z i).1 * (z i).2)
      ∂Measure.pi (fun _ : Fin n =>
        (gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      Real.exp (lam ^ 2 * ∑ i, (s i) ^ 2) := by
  rw [gaussianDiagonal_mgf s lam (fun i =>
    lt_of_le_of_lt (hsmall i) (by norm_num))]
  calc
    (∏ i, 1 / Real.sqrt (1 - (lam * s i) ^ 2)) ≤
        ∏ i, Real.exp ((lam * s i) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact invSqrt_one_sub_sq_le_exp_sq (hsmall i)
    _ = Real.exp (lam ^ 2 * ∑ i, (s i) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-! ## Singular-coordinate realization -/

/-- Synthesis of Euclidean vectors from a finite family.

**Lean implementation helper.** -/
def gaussianSynthesis {n : ℕ}
    (u : Fin n → EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i, x i • u i

/-- Establishes measurability of gaussian synthesis.

**Lean implementation helper.** -/
lemma measurable_gaussianSynthesis {n : ℕ}
    (u : Fin n → EuclideanSpace ℝ (Fin n)) :
    Measurable (gaussianSynthesis u) := by
  unfold gaussianSynthesis
  fun_prop

/-- Algebraic diagonalization of a square bilinear form from a rank-one SVD. This helper is
independent of probability and checks the index matching in the source's display preceding
(6.11).

**Lean implementation helper.** -/
theorem bilinear_svd_synthesis {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (u v : Fin n → EuclideanSpace ℝ (Fin n))
    (s x y : Fin n → ℝ)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (hA : A = ∑ i, s i • HDP.Chapter4.outerMatrix (u i) (v i)) :
    ⟪gaussianSynthesis u x, A.toEuclideanLin (gaussianSynthesis v y)⟫ =
      ∑ i, s i * x i * y i := by
  have happly : ∀ j : Fin n,
      A.toEuclideanLin (v j) = s j • u j := by
    intro j
    calc
      A.toEuclideanLin (v j) =
          (∑ i, s i • HDP.Chapter4.outerMatrix (u i) (v i)).toEuclideanLin
            (v j) := by rw [← hA]
      _ = s j • u j := by
        simp only [map_sum, map_smul,
          HDP.Chapter4.toEuclideanLin_outerMatrix,
          LinearMap.sum_apply, LinearMap.smul_apply]
        rw [Finset.sum_eq_single j]
        · change s j • (⟪v j, v j⟫ • u j) = _
          rw [inner_self_eq_norm_sq_to_K, hv.1]
          simp
        · intro i _ hij
          change s i • (⟪v i, v j⟫ • u i) = 0
          rw [hv.inner_eq_zero hij]
          simp
        · simp
  have hmap : A.toEuclideanLin (gaussianSynthesis v y) =
      ∑ i, (s i * y i) • u i := by
    simp only [gaussianSynthesis, map_sum, map_smul, happly]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  rw [hmap]
  simpa [gaussianSynthesis, mul_assoc, mul_left_comm, mul_comm] using
    hu.inner_sum x (fun i => s i * y i) Finset.univ

/-- Rotation-invariance and product-measure bridge used in the corresponding lemma. It
identifies the standard-Gaussian bilinear MGF with the diagonal product-normal integral for any
full square SVD.

**Book (6.11).** -/
theorem integral_gaussianBilinear_eq_diagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (u v : Fin n → EuclideanSpace ℝ (Fin n))
    (s : Fin n → ℝ)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (hA : A = ∑ i, s i • HDP.Chapter4.outerMatrix (u i) (v i))
    (lam : ℝ) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      ∫ z : Fin n → ℝ × ℝ,
        Real.exp (lam * ∑ i, s i * (z i).1 * (z i).2)
      ∂Measure.pi (fun _ : Fin n =>
        (gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let piGaussian : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let pairGaussian : Measure (Fin n → ℝ × ℝ) :=
    Measure.pi (fun _ : Fin n =>
      (gaussianReal 0 1).prod (gaussianReal 0 1))
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by
    simp [E]
  have hspanU : Submodule.span ℝ (Set.range u) = ⊤ :=
    hu.linearIndependent.span_eq_top_of_card_eq_finrank' hcard
  have hspanV : Submodule.span ℝ (Set.range v) = ⊤ :=
    hv.linearIndependent.span_eq_top_of_card_eq_finrank' hcard
  let bU : OrthonormalBasis (Fin n) ℝ E :=
    OrthonormalBasis.mk hu hspanU.ge
  let bV : OrthonormalBasis (Fin n) ℝ E :=
    OrthonormalBasis.mk hv hspanV.ge
  have hbU : (bU : Fin n → E) = u := by
    exact OrthonormalBasis.coe_mk hu hspanU.ge
  have hbV : (bV : Fin n → E) = v := by
    exact OrthonormalBasis.coe_mk hv hspanV.ge
  have hLawU : HasLaw (gaussianSynthesis u) (stdGaussian E) piGaussian := by
    refine ⟨(measurable_gaussianSynthesis u).aemeasurable, ?_⟩
    change Measure.map (fun x : Fin n → ℝ => ∑ i, x i • u i)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) = stdGaussian E
    simpa [hbU] using
      (stdGaussian_eq_map_pi_orthonormalBasis bU).symm
  have hLawV : HasLaw (gaussianSynthesis v) (stdGaussian E) piGaussian := by
    refine ⟨(measurable_gaussianSynthesis v).aemeasurable, ?_⟩
    change Measure.map (fun x : Fin n → ℝ => ∑ i, x i • v i)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) = stdGaussian E
    simpa [hbV] using
      (stdGaussian_eq_map_pi_orthonormalBasis bV).symm
  have hInd :
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => gaussianSynthesis u p.1) ⟂ᵢ[
        piGaussian.prod piGaussian]
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => gaussianSynthesis v p.2) :=
    indepFun_prod (measurable_gaussianSynthesis u)
      (measurable_gaussianSynthesis v)
  have hLawUFst : HasLaw
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => gaussianSynthesis u p.1)
      (stdGaussian E) (piGaussian.prod piGaussian) := by
    simpa [Function.comp_def] using hLawU.comp
      (measurePreserving_fst (μ := piGaussian) (ν := piGaussian)).hasLaw
  have hLawVSnd : HasLaw
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => gaussianSynthesis v p.2)
      (stdGaussian E) (piGaussian.prod piGaussian) := by
    simpa [Function.comp_def] using hLawV.comp
      (measurePreserving_snd (μ := piGaussian) (ν := piGaussian)).hasLaw
  have hLawPair : HasLaw
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (gaussianSynthesis u p.1, gaussianSynthesis v p.2))
      ((stdGaussian E).prod (stdGaussian E))
      (piGaussian.prod piGaussian) :=
    hInd.hasLaw_prod hLawUFst hLawVSnd
  have hPairing := measurePreserving_arrowProdEquivProdArrow
    ℝ ℝ (Fin n)
    (fun _ : Fin n => gaussianReal 0 1)
    (fun _ : Fin n => gaussianReal 0 1)
  have hLawDiag : HasLaw
      (fun z : Fin n → ℝ × ℝ =>
        (gaussianSynthesis u (fun i => (z i).1),
          gaussianSynthesis v (fun i => (z i).2)))
      ((stdGaussian E).prod (stdGaussian E)) pairGaussian := by
    have hcomp := hLawPair.comp hPairing.hasLaw
    simpa [pairGaussian, piGaussian, Function.comp_def,
      MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow] using hcomp
  have htransport := hLawDiag.integral_comp
    (f := fun p : E × E => Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫))
    (by fun_prop)
  calc
    (∫ p : E × E, Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫)
        ∂(stdGaussian E).prod (stdGaussian E)) =
        ∫ z : Fin n → ℝ × ℝ,
          Real.exp (lam *
            ⟪gaussianSynthesis u (fun i => (z i).1),
              A.toEuclideanLin (gaussianSynthesis v (fun i => (z i).2))⟫)
          ∂pairGaussian := by
      simpa [Function.comp_def] using htransport.symm
    _ = ∫ z : Fin n → ℝ × ℝ,
        Real.exp (lam * ∑ i, s i * (z i).1 * (z i).2)
        ∂pairGaussian := by
      apply integral_congr_ae
      filter_upwards with z
      rw [bilinear_svd_synthesis A u v s
        (fun i => (z i).1) (fun i => (z i).2) hu hv hA]
    _ = ∫ z : Fin n → ℝ × ℝ,
        Real.exp (lam * ∑ i, s i * (z i).1 * (z i).2)
        ∂Measure.pi (fun _ : Fin n =>
          (gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      rfl

/-- The source calls this a Gaussian quadratic form, although the two Gaussian vectors are
independent. The denominator-free small-parameter condition is equivalent to `|lam| ≤ 1 / (2
‖A‖)` when `A ≠ 0`, and correctly keeps every `lam` when `A = 0`.

**Book Lemma 6.2.4.** -/
theorem gaussianBilinear_mgf {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (hscale : 2 * |lam| * HDP.matrixOpNorm A ≤ 1) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      Real.exp (lam ^ 2 * HDP.matrixFrobeniusNorm A ^ 2) := by
  by_cases hzero : HDP.matrixOpNorm A = 0
  · have hA : A = 0 := (HDP.Chapter4.matrixOpNorm_eq_zero_iff A).mp hzero
    subst A
    simp
  · obtain ⟨u, hu, hA⟩ := HDP.Chapter4.exists_tall_svd A (le_refl n)
    rw [integral_gaussianBilinear_eq_diagonal A u
      (HDP.Chapter4.rightSingularBasis A)
      (fun i : Fin n => HDP.matrixSingularValue A i) hu
      (HDP.Chapter4.rightSingularBasis A).orthonormal hA lam]
    have hsmall : ∀ i : Fin n,
        (lam * HDP.matrixSingularValue A i) ^ 2 ≤ 1 / 2 := by
      intro i
      letI : Nonempty (Fin n) := ⟨i⟩
      have hs0 : 0 ≤ HDP.matrixSingularValue A i :=
        HDP.matrixSingularValue_nonneg A i
      have hsM : HDP.matrixSingularValue A i ≤ HDP.matrixOpNorm A := by
        rw [HDP.Chapter4.opNorm_eq_largestSingularValue A]
        exact HDP.matrixSingularValue_antitone A (Nat.zero_le i.val)
      have habsMul : |lam * HDP.matrixSingularValue A i| ≤
          |lam| * HDP.matrixOpNorm A := by
        rw [abs_mul, abs_of_nonneg hs0]
        exact mul_le_mul_of_nonneg_left hsM (abs_nonneg lam)
      have hhalf : |lam| * HDP.matrixOpNorm A ≤ 1 / 2 := by
        nlinarith
      have habsHalf : |lam * HDP.matrixSingularValue A i| ≤ 1 / 2 :=
        habsMul.trans hhalf
      nlinarith [sq_abs (lam * HDP.matrixSingularValue A i),
        abs_nonneg (lam * HDP.matrixSingularValue A i)]
    calc
      (∫ z : Fin n → ℝ × ℝ,
          Real.exp (lam * ∑ i : Fin n,
            HDP.matrixSingularValue A i * (z i).1 * (z i).2)
        ∂Measure.pi (fun _ : Fin n =>
          (gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
          Real.exp (lam ^ 2 *
            ∑ i : Fin n, HDP.matrixSingularValue A i ^ 2) :=
        gaussianDiagonal_mgf_le
          (fun i : Fin n => HDP.matrixSingularValue A i) lam hsmall
      _ = Real.exp (lam ^ 2 * HDP.matrixFrobeniusNorm A ^ 2) := by
        rw [HDP.Chapter4.frobeniusNorm_sq_eq_sum_singularValues]

/-- The Gaussian bilinear exponential is integrable throughout the safe parameter range of the
corresponding lemma. This lemma makes explicit the finiteness that is implicit in the source's
MGF notation.

**Lean implementation helper.** -/
theorem integrable_exp_gaussianBilinear {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (hscale : 2 * |lam| * HDP.matrixOpNorm A ≤ 1) :
    Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  by_cases hzero : HDP.matrixOpNorm A = 0
  · have hA : A = 0 := (HDP.Chapter4.matrixOpNorm_eq_zero_iff A).mp hzero
    subst A
    simp
  · obtain ⟨u, hu, hA⟩ := HDP.Chapter4.exists_tall_svd A (le_refl n)
    let v := HDP.Chapter4.rightSingularBasis A
    let s : Fin n → ℝ := fun i ↦ HDP.matrixSingularValue A i
    have hv : Orthonormal ℝ v :=
      (HDP.Chapter4.rightSingularBasis A).orthonormal
    have hsmall : ∀ i : Fin n, (lam * s i) ^ 2 < 1 := by
      intro i
      letI : Nonempty (Fin n) := ⟨i⟩
      have hs0 : 0 ≤ s i := HDP.matrixSingularValue_nonneg A i
      have hsM : s i ≤ HDP.matrixOpNorm A := by
        rw [HDP.Chapter4.opNorm_eq_largestSingularValue A]
        exact HDP.matrixSingularValue_antitone A (Nat.zero_le i.val)
      have habsMul : |lam * s i| ≤ |lam| * HDP.matrixOpNorm A := by
        rw [abs_mul, abs_of_nonneg hs0]
        exact mul_le_mul_of_nonneg_left hsM (abs_nonneg lam)
      have hhalf : |lam| * HDP.matrixOpNorm A ≤ 1 / 2 := by
        nlinarith
      have habsHalf : |lam * s i| ≤ 1 / 2 := habsMul.trans hhalf
      nlinarith [sq_abs (lam * s i), abs_nonneg (lam * s i)]
    have heq := integral_gaussianBilinear_eq_diagonal A u v s hu hv hA lam
    rw [gaussianDiagonal_mgf s lam hsmall] at heq
    have hprodPos : 0 < ∏ i, 1 / Real.sqrt (1 - (lam * s i) ^ 2) := by
      apply Finset.prod_pos
      intro i _
      exact one_div_pos.mpr (Real.sqrt_pos.2 (by
        have hi := hsmall i
        linarith))
    by_contra hnot
    have hzeroIntegral :
        (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin n)))) = 0 :=
      integral_undef hnot
    rw [hzeroIntegral] at heq
    exact (ne_of_gt hprodPos) heq.symm

/-- Extended-integral form of the corresponding lemma.

**Book Lemma 6.2.4.** -/
theorem gaussianBilinear_lmgf {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (hscale : 2 * |lam| * HDP.matrixOpNorm A ≤ 1) :
    (∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      ENNReal.ofReal
        (Real.exp (lam ^ 2 * HDP.matrixFrobeniusNorm A ^ 2)) := by
  have hint := integrable_exp_gaussianBilinear A lam hscale
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (gaussianBilinear_mgf A lam hscale)

/-- Conventional nonzero-matrix wrapper for the printed hypothesis in the corresponding lemma.

**Book Lemma 6.2.4.** -/
theorem gaussianBilinear_mgf_of_abs_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0) (lam : ℝ)
    (hlam : |lam| ≤ 1 / (2 * HDP.matrixOpNorm A)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Real.exp (lam * ⟪p.1, A.toEuclideanLin p.2⟫)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      Real.exp (lam ^ 2 * HDP.matrixFrobeniusNorm A ^ 2) := by
  apply gaussianBilinear_mgf A lam
  have hM : 0 < HDP.matrixOpNorm A :=
    lt_of_le_of_ne (HDP.matrixOpNorm_nonneg A)
      (fun h => hA ((HDP.Chapter4.matrixOpNorm_eq_zero_iff A).mp h.symm))
  rw [div_eq_mul_inv] at hlam
  have hlam' : |lam| ≤ (2 * HDP.matrixOpNorm A)⁻¹ := by
    simpa using hlam
  calc
    2 * |lam| * HDP.matrixOpNorm A ≤
        2 * ((2 * HDP.matrixOpNorm A)⁻¹) * HDP.matrixOpNorm A := by
      gcongr
    _ = 1 := by field_simp

end

end HDP.Chapter6

end Source_05_GaussianQuadraticMGF

/-! ## Material formerly in `06_HansonWright.lean` -/

section Source_06_HansonWright

/-!
# Chapter 6, §6.2: the Hanson--Wright inequality

The proof is split exactly as in the source: a scalar Bernstein estimate for
the diagonal, followed by decoupling and Gaussian replacement for the
off-diagonal chaos.  All constants below are explicit.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter6

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Every real matrix entry is bounded by the Euclidean operator norm.

**Lean implementation helper.** -/
theorem abs_matrixEntry_le_opNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    |A i j| ≤ HDP.matrixOpNorm A := by
  let v : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 (A.col j)
  let ei : EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.basisFun (Fin m) ℝ i
  calc
    |A i j| = |⟪v, ei⟫| := by
      congr 1
      simpa [v, ei] using
        (EuclideanSpace.inner_basisFun_real (Fin m) v i).symm
    _ ≤ ‖v‖ * ‖ei‖ := abs_real_inner_le_norm v ei
    _ = ‖v‖ := by simp [ei]
    _ ≤ HDP.matrixOpNorm A :=
      HDP.Chapter4.exercise_4_7a_column_le A j

/-- The diagonal square sum is bounded by the squared Frobenius norm.

**Lean implementation helper.** -/
theorem sum_diagonal_sq_le_frobenius_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, A i i ^ 2 ≤ HDP.matrixFrobeniusNorm A ^ 2 := by
  rw [HDP.matrixFrobeniusNorm_sq]
  exact Finset.sum_le_sum fun i _ ↦
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (A i j))
      (Finset.mem_univ i)

/-- Centered coordinate square used for the diagonal term.

**Lean implementation helper.** -/
def centeredCoordinateSquare {n : ℕ}
    (mu : Measure Omega) (X : Fin n → Omega → ℝ)
    (i : Fin n) (omega : Omega) : ℝ :=
  X i omega ^ 2 - ∫ omega', X i omega' ^ 2 ∂mu

set_option linter.unusedSectionVars false in
/-- Coordinate assembly written in the orthonormal Euclidean basis.

**Lean implementation helper.** -/
theorem vectorOfCoordinates_eq_basis_sum {n : ℕ}
    (X : Fin n → Omega → ℝ) (omega : Omega) :
    HDP.Chapter3.vectorOfCoordinates X omega =
      ∑ i, X i omega • EuclideanSpace.basisFun (Fin n) ℝ i := by
  simpa [HDP.Chapter3.vectorOfCoordinates] using
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr
      (HDP.Chapter3.vectorOfCoordinates X omega)).symm

/-- Centered scalar coordinates assemble into a Bochner-centered Euclidean random vector.

**Lean implementation helper.** -/
theorem isCenteredVector_vectorOfCoordinates
    [IsProbabilityMeasure mu] {n : ℕ}
    {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) mu)
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0) :
    IsCenteredVector (HDP.Chapter3.vectorOfCoordinates X) mu := by
  have hXint : ∀ i, Integrable (X i) mu := fun i ↦ by
    have hmem := (hsub i).memLp (hXm i) (p := (1 : ℝ)) (by norm_num)
    have hmem' : MemLp (X i) 1 mu := by simpa using hmem
    exact hmem'.integrable le_rfl
  have hfun : HDP.Chapter3.vectorOfCoordinates X =
      fun omega ↦ ∑ i, X i omega •
        EuclideanSpace.basisFun (Fin n) ℝ i := by
    funext omega
    exact vectorOfCoordinates_eq_basis_sum X omega
  constructor
  · rw [hfun]
    exact integrable_finsetSum Finset.univ fun i _ ↦
      (hXint i).smul_const (EuclideanSpace.basisFun (Fin n) ℝ i)
  · rw [hfun, integral_finsetSum Finset.univ]
    · simp_rw [integral_smul_const, hmean]
      simp
    · intro i _
      exact (hXint i).smul_const
        (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Uniform marginal bound for a vector with independent centered subgaussian coordinates. It is
the pointwise form of the corresponding source lemma and is also the boundedness certificate
needed by the real-valued vector psi-two supremum.

**Lean implementation helper.** -/
theorem psi2Norm_inner_vectorOfCoordinates_le
    [IsProbabilityMeasure mu] {n : ℕ}
    {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) mu)
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (hindep : iIndepFun X mu) {K : ℝ} (hK : 0 ≤ K)
    (hpsi : ∀ i, HDP.psi2Norm (X i) mu ≤ K)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    HDP.psi2Norm
        (fun omega ↦ ⟪HDP.Chapter3.vectorOfCoordinates X omega, u⟫) mu ≤
      Real.sqrt 30 * K := by
  let Y : Fin n → Omega → ℝ := fun i omega ↦ u i * X i omega
  have hYm : ∀ i, AEMeasurable (Y i) mu := fun i ↦
    (hXm i).const_mul (u i)
  have hYsub : ∀ i, HDP.SubGaussian (Y i) mu := fun i ↦
    (hsub i).const_mul (u i)
  have hYmean : ∀ i, ∫ omega, Y i omega ∂mu = 0 := by
    intro i
    rw [show Y i = fun omega ↦ u i * X i omega by rfl,
      integral_const_mul, hmean i, mul_zero]
  have hYindep : iIndepFun Y mu :=
    hindep.comp (fun i x ↦ u i * x) (fun i ↦ measurable_const_mul (u i))
  have hsum := (HDP.psi2Norm_sum_sq_le hYm hYsub hYmean hYindep).2
  have hpsiSq : ∀ i, HDP.psi2Norm (X i) mu ^ 2 ≤ K ^ 2 := fun i ↦
    (sq_le_sq₀ (HDP.psi2Norm_nonneg (X i) mu) hK).2 (hpsi i)
  have hsumSq : ∑ i, HDP.psi2Norm (Y i) mu ^ 2 ≤ K ^ 2 := by
    calc
      ∑ i, HDP.psi2Norm (Y i) mu ^ 2 ≤
          ∑ i, (u i) ^ 2 * K ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [show Y i = fun omega ↦ u i * X i omega by rfl,
          HDP.psi2Norm_const_mul, mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_left (hpsiSq i) (sq_nonneg (u i))
      _ = K ^ 2 * ∑ i, (u i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = K ^ 2 := by
        rw [← EuclideanSpace.real_norm_sq_eq, hu]
        norm_num
  have hsquare :
      HDP.psi2Norm (fun omega ↦ ∑ i, Y i omega) mu ^ 2 ≤
        30 * K ^ 2 := hsum.trans
    (mul_le_mul_of_nonneg_left hsumSq (by norm_num))
  have hsumEq : (fun omega ↦ ∑ i, Y i omega) =
      fun omega ↦ ⟪HDP.Chapter3.vectorOfCoordinates X omega, u⟫ := by
    funext omega
    simp [Y, HDP.Chapter3.vectorOfCoordinates, PiLp.inner_apply, mul_comm]
  rw [hsumEq] at hsquare
  apply (sq_le_sq₀ (HDP.psi2Norm_nonneg _ mu)
    (mul_nonneg (Real.sqrt_nonneg _) hK)).1
  calc
    HDP.psi2Norm
        (fun omega ↦ ⟪HDP.Chapter3.vectorOfCoordinates X omega, u⟫) mu ^ 2 ≤
        30 * K ^ 2 := hsquare
    _ = (Real.sqrt 30 * K) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

/-- The directional psi-two set for independent coordinates is bounded above. This discharges
the safety hypothesis of the real-valued `psi2NormVector`.

**Lean implementation helper.** -/
theorem bddAbove_directionalPsi2_vectorOfCoordinates
    [IsProbabilityMeasure mu] {n : ℕ}
    {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) mu)
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (hindep : iIndepFun X mu) {K : ℝ} (hK : 0 ≤ K)
    (hpsi : ∀ i, HDP.psi2Norm (X i) mu ≤ K) :
    BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm
          (fun omega ↦ ⟪HDP.Chapter3.vectorOfCoordinates X omega, u⟫) mu} := by
  refine ⟨Real.sqrt 30 * K, ?_⟩
  rintro r ⟨u, hu, rfl⟩
  exact psi2Norm_inner_vectorOfCoordinates_le
    hXm hsub hmean hindep hK hpsi u hu

set_option linter.unusedSectionVars false in
/-- The scalar matrix bilinear form agrees with the Euclidean inner-product interface used by
Gaussian replacement.

**Lean implementation helper.** -/
theorem bilinearForm_eq_inner_vectorOfCoordinates {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X Y : Fin n → Omega → ℝ) (omega eta : Omega) :
    bilinearForm A (fun i ↦ X i omega) (fun j ↦ Y j eta) =
      ⟪HDP.Chapter3.vectorOfCoordinates X omega,
        A.toEuclideanLin (HDP.Chapter3.vectorOfCoordinates Y eta)⟫ := by
  simp only [bilinearForm_apply, HDP.Chapter3.vectorOfCoordinates,
    PiLp.inner_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Removing the diagonal can only decrease the Frobenius norm.

**Lean implementation helper.** -/
theorem offDiagonal_frobeniusNorm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HDP.matrixFrobeniusNorm (offDiagonal A) ≤
      HDP.matrixFrobeniusNorm A := by
  apply (sq_le_sq₀ (HDP.matrixFrobeniusNorm_nonneg (offDiagonal A))
    (HDP.matrixFrobeniusNorm_nonneg A)).1
  rw [HDP.matrixFrobeniusNorm_sq, HDP.matrixFrobeniusNorm_sq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    rw [offDiagonal_apply_same]
    simpa using sq_nonneg (A i i)
  · rw [offDiagonal_apply_ne A hij]

set_option maxHeartbeats 800000 in
-- The finite operator-norm expansion below needs a larger deterministic
-- elaboration budget than Lean's project default.
/-- Removing the diagonal increases the operator norm by at most a factor two.

**Lean implementation helper.** -/
theorem offDiagonal_opNorm_le_two_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HDP.matrixOpNorm (offDiagonal A) ≤ 2 * HDP.matrixOpNorm A := by
  classical
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ A i i)
  have hoff : offDiagonal A = A - D := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [offDiagonal_apply_same]
      simp [D]
    · rw [offDiagonal_apply_ne A hij]
      simp [D, hij]
  have hD : HDP.matrixOpNorm D ≤ HDP.matrixOpNorm A := by
    rw [show D = Matrix.diagonal (fun i ↦ A i i) by rfl,
      HDP.Chapter4.exercise_4_3b_diagonal]
    apply (pi_norm_le_iff_of_nonneg (HDP.matrixOpNorm_nonneg A)).2
    intro i
    simpa [Real.norm_eq_abs] using abs_matrixEntry_le_opNorm A i i
  rw [hoff]
  calc
    HDP.matrixOpNorm (A - D) ≤
        HDP.matrixOpNorm A + HDP.matrixOpNorm D :=
      HDP.matrixOpNorm_sub_le A D
    _ ≤ HDP.matrixOpNorm A + HDP.matrixOpNorm A :=
      by linarith
    _ = 2 * HDP.matrixOpNorm A := by ring

/-- Algebraic diagonal/off-diagonal decomposition of a quadratic form.

**Lean implementation helper.** -/
theorem quadraticForm_eq_diagonal_add_offDiagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm A x =
      ∑ i, A i i * x i ^ 2 + quadraticForm (offDiagonal A) x := by
  rw [quadraticForm_eq_doubleSum, quadraticForm_eq_doubleSum]
  calc
    (∑ i, ∑ j, A i j * x i * x j) =
        ∑ i, (A i i * x i ^ 2 +
          (∑ j ∈ Finset.univ.erase i, A i j * x i * x j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    _ = ∑ i, A i i * x i ^ 2 +
        ∑ i, ∑ j, offDiagonal A i j * x i * x j := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        offDiagonal_apply_same]
      simp only [zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun a : ℝ ↦ a * x i * x j)
        (offDiagonal_apply_ne A (Ne.symm (Finset.mem_erase.mp hj).1)).symm

/-- The centered quadratic form is the sum of its centered diagonal term and the (already
centered) off-diagonal chaos.

**Book Chapter 6, pp.186--187, Hanson--Wright proof.** -/
theorem quadraticForm_sub_integral_eq_diagonal_add_offDiagonal
    [IsProbabilityMeasure mu] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {X : Fin n → Omega → ℝ}
    (hX : ∀ i, MemLp (X i) 2 mu)
    (hindep : iIndepFun X mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (omega : Omega) :
    quadraticForm A (fun i ↦ X i omega) -
        ∫ eta, quadraticForm A (fun i ↦ X i eta) ∂mu =
      (∑ i, A i i * centeredCoordinateSquare mu X i omega) +
        quadraticForm (offDiagonal A) (fun i ↦ X i omega) := by
  rw [integral_quadraticForm_eq_diagonal A X hX hindep hmean,
    quadraticForm_eq_diagonal_add_offDiagonal]
  simp only [centeredCoordinateSquare]
  have hsum :
      (∑ i, A i i * (X i omega ^ 2 - ∫ eta, X i eta ^ 2 ∂mu)) =
        (∑ i, A i i * X i omega ^ 2) -
          ∑ i, A i i * ∫ eta, X i eta ^ 2 ∂mu := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- The scalar Bernstein part of Hanson--Wright. This is the source's diagonal estimate, with
the Chapter 2 centering constant retained explicitly.

**Book Chapter 6, pp.186--187, Hanson--Wright proof.** -/
theorem hansonWright_diagonal
    [IsProbabilityMeasure mu] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0)
    {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) mu)
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hindep : iIndepFun X mu)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HDP.psi2Norm (X i) mu ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    mu {omega | t ≤
        |∑ i, A i i * centeredCoordinateSquare mu X i omega|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
        min
          (t ^ 2 /
            (((1 + 1 / Real.log 2) * K ^ 2) ^ 2 *
              ∑ i, (A i i) ^ 2))
          (t /
            ((1 + 1 / Real.log 2) * K ^ 2 *
              HDP.matrixOpNorm A)))) := by
  classical
  let Y : Fin n → Omega → ℝ :=
    centeredCoordinateSquare mu X
  let C : ℝ := 1 + 1 / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hYmeas : ∀ i, AEMeasurable (Y i) mu := fun i ↦ by
    dsimp [Y, centeredCoordinateSquare]
    exact ((hXm i).pow_const 2).sub aemeasurable_const
  have hYsub : ∀ i, HDP.SubExponential (Y i) mu := by
    intro i
    change HDP.SubExponential
      (fun omega ↦ X i omega ^ 2 - ∫ omega', X i omega' ^ 2 ∂mu) mu
    have hsq : HDP.SubExponential (fun omega ↦ X i omega ^ 2) mu :=
      (HDP.subExponential_sq_iff (X i)).2 (hsub i)
    exact (HDP.psi1Norm_centering ((hXm i).pow_const 2) hsq).1
  have hYmean : ∀ i, ∫ omega, Y i omega ∂mu = 0 := by
    intro i
    have hmem : MemLp (X i) 2 mu := by
      simpa using (hsub i).memLp (hXm i) (p := (2 : ℝ)) (by norm_num)
    dsimp [Y, centeredCoordinateSquare]
    rw [integral_sub hmem.integrable_sq (integrable_const _), integral_const]
    simp
  have hYindep : iIndepFun Y mu := by
    change iIndepFun
      (fun i omega ↦ X i omega ^ 2 - ∫ omega', X i omega' ^ 2 ∂mu) mu
    simpa [Function.comp_def] using
      hindep.comp
        (fun i (x : ℝ) ↦ x ^ 2 - ∫ omega, X i omega ^ 2 ∂mu)
        (fun _ ↦ (measurable_id.pow_const 2).sub_const _)
  have hYnorm : ∀ i, HDP.psi1Norm (Y i) mu ≤ C * K ^ 2 := by
    intro i
    change HDP.psi1Norm
      (fun omega ↦ X i omega ^ 2 - ∫ omega', X i omega' ^ 2 ∂mu) mu ≤
        C * K ^ 2
    have hsq : HDP.SubExponential (fun omega ↦ X i omega ^ 2) mu :=
      (HDP.subExponential_sq_iff (X i)).2 (hsub i)
    have hcenter :=
      (HDP.psi1Norm_centering ((hXm i).pow_const 2) hsq).2
    have hsquare : HDP.psi2Norm (X i) mu ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (HDP.psi2Norm_nonneg (X i) mu) (hpsi i) 2
    calc
      HDP.psi1Norm
          (fun omega ↦ X i omega ^ 2 - ∫ omega', X i omega' ^ 2 ∂mu) mu ≤
          (1 + 1 / Real.log 2) *
            HDP.psi1Norm (fun omega ↦ X i omega ^ 2) mu := by
        exact hcenter
      _ = C * HDP.psi2Norm (X i) mu ^ 2 := by
        rw [HDP.psi1Norm_sq (hXm i) (hsub i)]
      _ ≤ C * K ^ 2 := mul_le_mul_of_nonneg_left hsquare hC.le
  have hOp : 0 < HDP.matrixOpNorm A := by
    exact lt_of_le_of_ne (HDP.matrixOpNorm_nonneg A)
      (fun h ↦ hA ((HDP.Chapter4.matrixOpNorm_eq_zero_iff A).1 h.symm))
  have hweight : ∀ i, |A i i| ≤ HDP.matrixOpNorm A :=
    fun i ↦ abs_matrixEntry_le_opNorm A i i
  simpa [Y, C] using
    (HDP.bernstein_weighted (μ := mu) (X := Y)
      (fun i ↦ A i i) hYmeas hYsub hYmean hYindep
      (mul_pos hC (sq_pos_of_pos hK)) hOp hYnorm hweight ht)

/-- The complete exponential-moment bound for the off-diagonal chaos. The constant `129600 =
360²` records, without hiding any dependency, the factor `4` from decoupling, `3` from Gaussian
replacement, and `√30` from the independent-coordinate vector psi-two estimate.

**Book (6.12).** -/
theorem hansonWright_offDiagonal_lmgf
    [IsProbabilityMeasure mu] {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (hindep : iIndepFun X mu)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HDP.psi2Norm (X i) mu ≤ K)
    (lam : ℝ)
    (hscale : 1440 * K ^ 2 * |lam| * HDP.matrixOpNorm A ≤ 1) :
    (∫⁻ omega, ENNReal.ofReal
        (Real.exp (lam * quadraticForm (offDiagonal A)
          (fun i ↦ X i omega))) ∂mu) ≤
      ENNReal.ofReal (Real.exp
        (129600 * K ^ 4 * lam ^ 2 *
          HDP.matrixFrobeniusNorm A ^ 2)) := by
  let V : Omega → EuclideanSpace ℝ (Fin n) :=
    HDP.Chapter3.vectorOfCoordinates X
  let Kvec : ℝ := Real.sqrt 30 * K
  let c : ℝ := 360 * K ^ 2 * lam
  have hXint : ∀ i, Integrable (X i) mu := fun i ↦ by
    have hmem := (hsub i).memLp (hXm i).aemeasurable
      (p := (1 : ℝ)) (by norm_num)
    have hmem' : MemLp (X i) 1 mu := by simpa using hmem
    exact hmem'.integrable le_rfl
  have hdec := decoupling_mgf_lintegral
    (offDiagonal A) (fun i ↦ offDiagonal_apply_same A i)
    hXm hXm hXint hindep hindep hmean
    (fun i ↦ IdentDistrib.refl (hXm i).aemeasurable) lam
  have hVm : Measurable V := by
    have hVfun : V = fun omega ↦ ∑ i, X i omega •
        EuclideanSpace.basisFun (Fin n) ℝ i := by
      funext omega
      exact vectorOfCoordinates_eq_basis_sum X omega
    rw [hVfun]
    exact Finset.measurable_sum Finset.univ fun i _ ↦
      (hXm i).smul_const (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hVsub : HDP.SubGaussianVector V mu := by
    simpa [V] using
      (HDP.Chapter3.subGaussianVector_of_independent_coordinates
        (fun i ↦ (hXm i).aemeasurable) hsub hmean hindep)
  have hVbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun omega ↦ ⟪V omega, u⟫) mu} := by
    simpa [V] using bddAbove_directionalPsi2_vectorOfCoordinates
      (fun i ↦ (hXm i).aemeasurable) hsub hmean hindep hK.le hpsi
  have hVcenter : IsCenteredVector V mu := by
    simpa [V] using isCenteredVector_vectorOfCoordinates
      (fun i ↦ (hXm i).aemeasurable) hsub hmean
  have hKvec : 0 ≤ Kvec := by
    dsimp [Kvec]
    positivity
  have hVpsi : HDP.psi2NormVector V mu ≤ Kvec := by
    simpa [V, Kvec] using
      (HDP.Chapter3.psi2NormVector_independent_coordinates_le
        (fun i ↦ (hXm i).aemeasurable) hsub hmean hindep hK.le hpsi)
  have hreplaceRaw := gaussianReplacement
    hVm hVm hVsub hVsub hVbounded hVbounded hVcenter hVcenter
    hKvec hVpsi hVpsi (offDiagonal A).toEuclideanLin (4 * lam)
  have hcoef : 3 * Kvec ^ 2 * (4 * lam) = c := by
    dsimp [Kvec, c]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]
    ring
  have hreplace :
      (∫⁻ z : Omega × Omega, ENNReal.ofReal
        (Real.exp (4 * lam * bilinearForm (offDiagonal A)
          (fun i ↦ X i z.1) (fun j ↦ X j z.2))) ∂mu.prod mu) ≤
        ∫⁻ z : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal
            (Real.exp (c * ⟪z.1, (offDiagonal A).toEuclideanLin z.2⟫))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa only [V, bilinearForm_eq_inner_vectorOfCoordinates,
      hcoef] using hreplaceRaw
  have hscaleGaussian :
      2 * |c| * HDP.matrixOpNorm (offDiagonal A) ≤ 1 := by
    have hOff := offDiagonal_opNorm_le_two_mul A
    have hnonneg : 0 ≤ 720 * K ^ 2 * |lam| := by positivity
    calc
      2 * |c| * HDP.matrixOpNorm (offDiagonal A) =
          (720 * K ^ 2 * |lam|) *
            HDP.matrixOpNorm (offDiagonal A) := by
        dsimp [c]
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 360),
          abs_pow, abs_of_pos hK]
        ring
      _ ≤ (720 * K ^ 2 * |lam|) *
          (2 * HDP.matrixOpNorm A) :=
        mul_le_mul_of_nonneg_left hOff hnonneg
      _ = 1440 * K ^ 2 * |lam| * HDP.matrixOpNorm A := by ring
      _ ≤ 1 := hscale
  have hgauss := gaussianBilinear_lmgf (offDiagonal A) c hscaleGaussian
  have hFrobSq : HDP.matrixFrobeniusNorm (offDiagonal A) ^ 2 ≤
      HDP.matrixFrobeniusNorm A ^ 2 :=
    (sq_le_sq₀ (HDP.matrixFrobeniusNorm_nonneg (offDiagonal A))
      (HDP.matrixFrobeniusNorm_nonneg A)).2
      (offDiagonal_frobeniusNorm_le A)
  calc
    (∫⁻ omega, ENNReal.ofReal
        (Real.exp (lam * quadraticForm (offDiagonal A)
          (fun i ↦ X i omega))) ∂mu) ≤
        ∫⁻ z : Omega × Omega, ENNReal.ofReal
          (Real.exp (4 * lam * bilinearForm (offDiagonal A)
            (fun i ↦ X i z.1) (fun j ↦ X j z.2))) ∂mu.prod mu := hdec
    _ ≤ ∫⁻ z : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal
          (Real.exp (c * ⟪z.1, (offDiagonal A).toEuclideanLin z.2⟫))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin n))) := hreplace
    _ ≤ ENNReal.ofReal (Real.exp
          (c ^ 2 * HDP.matrixFrobeniusNorm (offDiagonal A) ^ 2)) := hgauss
    _ ≤ ENNReal.ofReal (Real.exp
          (129600 * K ^ 4 * lam ^ 2 *
            HDP.matrixFrobeniusNorm A ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hcSq : c ^ 2 = 129600 * K ^ 4 * lam ^ 2 := by
        dsimp [c]
        ring
      rw [hcSq]
      exact mul_le_mul_of_nonneg_left hFrobSq (by positivity)

/-! ## The elementary two-sided Chernoff optimization -/

/-- A reusable two-sided tail bound from a local quadratic MGF estimate. The optimizer is `min
(t/(2a)) (1/(2b))`; the explicit `1/4` is convenient for the Hanson--Wright constants below.

**Lean implementation helper.** -/
theorem twoSided_tail_of_local_quadratic_lmgf
    [IsProbabilityMeasure mu] {Z : Omega → ℝ}
    (hZm : AEMeasurable Z mu) {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t)
    (hmgfPos : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * Z omega)) ∂mu ≤
        ENNReal.ofReal (Real.exp (a * lam ^ 2)))
    (hmgfNeg : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * (-Z omega))) ∂mu ≤
        ENNReal.ofReal (Real.exp (a * lam ^ 2))) :
    mu {omega | t ≤ |Z omega|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 4) *
        min (t ^ 2 / a) (t / b))) := by
  let lam : ℝ := min (t / (2 * a)) (1 / (2 * b))
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact le_min (by positivity) (by positivity)
  have hlamSmall : lam ≤ 1 / b := by
    calc
      lam ≤ 1 / (2 * b) := by dsimp [lam]; exact min_le_right _ _
      _ ≤ 1 / b := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b) hb).2
        nlinarith
  have hopt : -lam * t + a * lam ^ 2 ≤
      -(1 / 4) * min (t ^ 2 / a) (t / b) := by
    rcases le_or_gt (t / (2 * a)) (1 / (2 * b)) with hcase | hcase
    · have hlam : lam = t / (2 * a) := min_eq_left hcase
      have hexact : -(t / (2 * a)) * t + a * (t / (2 * a)) ^ 2 =
          -(1 / 4) * (t ^ 2 / a) := by
        field_simp [ha.ne']
        ring
      rw [hlam, hexact]
      have hmin := min_le_left (t ^ 2 / a) (t / b)
      nlinarith
    · have hright : 1 / (2 * b) ≤ t / (2 * a) := hcase.le
      have hlam : lam = 1 / (2 * b) := min_eq_right hright
      have habRaw : (1 : ℝ) * (2 * a) ≤ t * (2 * b) :=
        (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)
          (by positivity : (0 : ℝ) < 2 * a)).1 hright
      have hab : a / b ≤ t := by
        apply (div_le_iff₀ hb).2
        nlinarith
      have hquarter : a / (4 * b ^ 2) ≤ t / (4 * b) := by
        calc
          a / (4 * b ^ 2) = (a / b) * (1 / (4 * b)) := by
            field_simp [hb.ne']
          _ ≤ t * (1 / (4 * b)) :=
            mul_le_mul_of_nonneg_right hab (by positivity)
          _ = t / (4 * b) := by
            field_simp [hb.ne']
      have hexact : -(1 / (2 * b)) * t + a * (1 / (2 * b)) ^ 2 =
          -(t / (2 * b)) + a / (4 * b ^ 2) := by
        field_simp [hb.ne']
        ring
      rw [hlam, hexact]
      have hlinear : -(t / (2 * b)) + a / (4 * b ^ 2) ≤
          -(1 / 4) * (t / b) := by
        calc
          -(t / (2 * b)) + a / (4 * b ^ 2) ≤
              -(t / (2 * b)) + t / (4 * b) :=
            by linarith
          _ = -(1 / 4) * (t / b) := by
            field_simp [hb.ne']
            ring
      have hmin := min_le_right (t ^ 2 / a) (t / b)
      exact hlinear.trans
        (mul_le_mul_of_nonpos_left hmin (by norm_num))
  have hpos := HDP.meas_ge_le_of_exp_bound hZm
    (lam := lam) (t := t) (B := Real.exp (a * lam ^ 2)) hlam0
    (hmgfPos lam hlam0 hlamSmall)
  have hnegMeas : AEMeasurable (fun omega ↦ -Z omega) mu := hZm.neg
  have hneg := HDP.meas_ge_le_of_exp_bound hnegMeas
    (lam := lam) (t := t) (B := Real.exp (a * lam ^ 2)) hlam0
    (hmgfNeg lam hlam0 hlamSmall)
  have htailPos : mu {omega | t ≤ Z omega} ≤
      ENNReal.ofReal (Real.exp (-lam * t + a * lam ^ 2)) := by
    calc
      mu {omega | t ≤ Z omega} ≤
          ENNReal.ofReal
            (Real.exp (-(lam * t)) * Real.exp (a * lam ^ 2)) := hpos
      _ = ENNReal.ofReal (Real.exp (-lam * t + a * lam ^ 2)) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
  have htailNeg : mu {omega | t ≤ -Z omega} ≤
      ENNReal.ofReal (Real.exp (-lam * t + a * lam ^ 2)) := by
    calc
      mu {omega | t ≤ -Z omega} ≤
          ENNReal.ofReal
            (Real.exp (-(lam * t)) * Real.exp (a * lam ^ 2)) := hneg
      _ = ENNReal.ofReal (Real.exp (-lam * t + a * lam ^ 2)) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
  have hevent : {omega | t ≤ |Z omega|} =
      {omega | t ≤ Z omega} ∪ {omega | t ≤ -Z omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      rcases le_total 0 (Z omega) with hz | hz
      · exact Or.inl (by simpa [abs_of_nonneg hz] using h)
      · exact Or.inr (by simpa [abs_of_nonpos hz] using h)
    · rintro (h | h)
      · exact h.trans (le_abs_self (Z omega))
      · exact h.trans (neg_le_abs (Z omega))
  rw [hevent]
  calc
    mu ({omega | t ≤ Z omega} ∪ {omega | t ≤ -Z omega}) ≤
        mu {omega | t ≤ Z omega} + mu {omega | t ≤ -Z omega} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-lam * t + a * lam ^ 2)) +
        ENNReal.ofReal (Real.exp (-lam * t + a * lam ^ 2)) :=
      add_le_add htailPos htailNeg
    _ = ENNReal.ofReal (2 * Real.exp (-lam * t + a * lam ^ 2)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le
        (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal
        (2 * Real.exp (-(1 / 4) * min (t ^ 2 / a) (t / b))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr hopt

/-- Two-sided tail bound for the off-diagonal chaos, before the final harmless constant
unification with the diagonal term.

**Book (6.12).** -/
theorem hansonWright_offDiagonal
    [IsProbabilityMeasure mu] {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0)
    {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (hindep : iIndepFun X mu)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HDP.psi2Norm (X i) mu ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    mu {omega | t ≤
        |quadraticForm (offDiagonal A) (fun i ↦ X i omega)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 4) *
        min
          (t ^ 2 /
            (129600 * K ^ 4 * HDP.matrixFrobeniusNorm A ^ 2))
          (t /
            (1440 * K ^ 2 * HDP.matrixOpNorm A)))) := by
  let Z : Omega → ℝ := fun omega ↦
    quadraticForm (offDiagonal A) (fun i ↦ X i omega)
  let a : ℝ := 129600 * K ^ 4 * HDP.matrixFrobeniusNorm A ^ 2
  let b : ℝ := 1440 * K ^ 2 * HDP.matrixOpNorm A
  have hOp : 0 < HDP.matrixOpNorm A :=
    lt_of_le_of_ne (HDP.matrixOpNorm_nonneg A)
      (fun h ↦ hA ((HDP.Chapter4.matrixOpNorm_eq_zero_iff A).1 h.symm))
  have hFrob : 0 < HDP.matrixFrobeniusNorm A :=
    lt_of_lt_of_le hOp (HDP.Chapter4.operatorNorm_le_frobeniusNorm A)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hZm : AEMeasurable Z mu := by
    dsimp only [Z, quadraticForm, HDP.Chapter4.matrixBilinear]
    fun_prop
  have hscale_of_le {lam : ℝ} (hlam0 : 0 ≤ lam)
      (hlam : lam ≤ 1 / b) :
      1440 * K ^ 2 * |lam| * HDP.matrixOpNorm A ≤ 1 := by
    have hmul : lam * b ≤ 1 := (le_div_iff₀ hb).1 hlam
    simpa [b, abs_of_nonneg hlam0, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hmain := twoSided_tail_of_local_quadratic_lmgf hZm ha hb ht
    (fun lam hlam0 hlam ↦ by
      simpa [Z, a, mul_assoc, mul_left_comm, mul_comm] using
        hansonWright_offDiagonal_lmgf
        A hXm hsub hmean hindep hK hpsi lam
          (hscale_of_le hlam0 hlam))
    (fun lam hlam0 hlam ↦ by
      have hscaleNeg :
          1440 * K ^ 2 * |-lam| * HDP.matrixOpNorm A ≤ 1 := by
        simpa only [abs_neg] using hscale_of_le hlam0 hlam
      simpa [Z, a, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
        hansonWright_offDiagonal_lmgf
        A hXm hsub hmean hindep hK hpsi (-lam) hscaleNeg)
  simpa [Z, a, b] using hmain

/-- For a vector with independent centered subgaussian coordinates, every real quadratic form
concentrates around its mean in the Frobenius and operator norm regimes. The numerical constant
is deliberately exposed: it is not optimized, but is absolute and all zero-matrix and
zero-threshold cases are included in the statement.

**Book Theorem 6.2.2.** -/
theorem hansonWright
    [IsProbabilityMeasure mu] {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Omega → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hsub : ∀ i, HDP.SubGaussian (X i) mu)
    (hmean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (hindep : iIndepFun X mu)
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HDP.psi2Norm (X i) mu ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    mu {omega | t ≤
        |quadraticForm A (fun i ↦ X i omega) -
          ∫ eta, quadraticForm A (fun i ↦ X i eta) ∂mu|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 4147200) *
        min
          (t ^ 2 /
            (K ^ 4 * HDP.matrixFrobeniusNorm A ^ 2))
          (t /
            (K ^ 2 * HDP.matrixOpNorm A)))) := by
  classical
  by_cases ht0 : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hAzero : A = 0
  · subst A
    simp [quadraticForm, HDP.Chapter4.matrixBilinear,
      not_le.mpr htpos]
  let F : ℝ := HDP.matrixFrobeniusNorm A
  let O : ℝ := HDP.matrixOpNorm A
  let S : ℝ := ∑ i, A i i ^ 2
  let C : ℝ := 1 + 1 / Real.log 2
  let u : ℝ := min (t ^ 2 / (K ^ 4 * F ^ 2)) (t / (K ^ 2 * O))
  let c0 : ℝ := 1 / 2073600
  let c : ℝ := 1 / 4147200
  let D : Omega → ℝ := fun omega ↦
    ∑ i, A i i * centeredCoordinateSquare mu X i omega
  let R : Omega → ℝ := fun omega ↦
    quadraticForm (offDiagonal A) (fun i ↦ X i omega)
  let Z : Omega → ℝ := fun omega ↦
    quadraticForm A (fun i ↦ X i omega) -
      ∫ eta, quadraticForm A (fun i ↦ X i eta) ∂mu
  have hO : 0 < O := by
    dsimp [O]
    exact lt_of_le_of_ne (HDP.matrixOpNorm_nonneg A)
      (fun h ↦ hAzero
        ((HDP.Chapter4.matrixOpNorm_eq_zero_iff A).1 h.symm))
  have hF : 0 < F := by
    dsimp [F]
    exact lt_of_lt_of_le hO
      (HDP.Chapter4.operatorNorm_le_frobeniusNorm A)
  have hK2O : 0 < K ^ 2 * O := by positivity
  have hK4F : 0 < K ^ 4 * F ^ 2 := by positivity
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact le_min (by positivity) (by positivity)
  have hc0 : 0 < c0 := by dsimp [c0]; norm_num
  have hc : 0 < c := by dsimp [c]; norm_num
  have hc0_eq : c0 = 2 * c := by
    dsimp [c0, c]
    norm_num
  have hX2 : ∀ i, MemLp (X i) 2 mu := fun i ↦ by
    simpa using (hsub i).memLp (hXm i).aemeasurable
      (p := (2 : ℝ)) (by norm_num)
  have hdecomp : ∀ omega, Z omega = D omega + R omega := by
    intro omega
    simpa [Z, D, R] using
      quadraticForm_sub_integral_eq_diagonal_add_offDiagonal
        A hX2 hindep hmean omega
  have hOffRaw := hansonWright_offDiagonal A hAzero
    hXm hsub hmean hindep hK hpsi (t := t / 2) (by positivity)
  have hOffExponent : c0 * u ≤
      (1 / 4) *
        min
          ((t / 2) ^ 2 / (129600 * K ^ 4 * F ^ 2))
          ((t / 2) / (1440 * K ^ 2 * O)) := by
    have huQ : u ≤ t ^ 2 / (K ^ 4 * F ^ 2) := by
      dsimp [u]
      exact min_le_left _ _
    have huL : u ≤ t / (K ^ 2 * O) := by
      dsimp [u]
      exact min_le_right _ _
    have hq : c0 * u ≤
        (1 / 4) * ((t / 2) ^ 2 /
          (129600 * K ^ 4 * F ^ 2)) := by
      have heq : (1 / 4 : ℝ) * ((t / 2) ^ 2 /
            (129600 * K ^ 4 * F ^ 2)) =
          c0 * (t ^ 2 / (K ^ 4 * F ^ 2)) := by
        dsimp [c0]
        field_simp [hK.ne', hF.ne']
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left huQ hc0.le
    have hl : c0 * u ≤
        (1 / 4) * ((t / 2) / (1440 * K ^ 2 * O)) := by
      have hbase : 0 ≤ t / (K ^ 2 * O) := by positivity
      calc
        c0 * u ≤ c0 * (t / (K ^ 2 * O)) :=
          mul_le_mul_of_nonneg_left huL hc0.le
        _ ≤ (1 / 11520 : ℝ) * (t / (K ^ 2 * O)) := by
          exact mul_le_mul_of_nonneg_right (by dsimp [c0]; norm_num) hbase
        _ = (1 / 4) * ((t / 2) / (1440 * K ^ 2 * O)) := by
          field_simp [hK.ne', hO.ne']
          ring
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    exact le_min hq hl
  have hOff : mu {omega | t / 2 ≤ |R omega|} ≤
      ENNReal.ofReal (2 * Real.exp (-c0 * u)) := by
    calc
      mu {omega | t / 2 ≤ |R omega|} ≤
          ENNReal.ofReal (2 * Real.exp (-(1 / 4) *
            min
              ((t / 2) ^ 2 / (129600 * K ^ 4 * F ^ 2))
              ((t / 2) / (1440 * K ^ 2 * O)))) := by
        simpa [R, F, O] using hOffRaw
      _ ≤ ENNReal.ofReal (2 * Real.exp (-c0 * u)) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCle : C ≤ 3 := by
    have hlogHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hone : 1 / Real.log 2 ≤ (2 : ℝ) := by
      apply (div_le_iff₀ hlog).2
      nlinarith
    dsimp [C]
    linarith
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hSle : S ≤ F ^ 2 := by
    dsimp [S, F]
    exact sum_diagonal_sq_le_frobenius_sq A
  have hDiag : mu {omega | t / 2 ≤ |D omega|} ≤
      ENNReal.ofReal (2 * Real.exp (-c0 * u)) := by
    by_cases hSzero : S = 0
    · have hdiagZero : ∀ i, A i i = 0 := by
        intro i
        have hi : A i i ^ 2 ≤ S := by
          dsimp [S]
          exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (A j j))
            (Finset.mem_univ i)
        have : A i i ^ 2 = 0 := le_antisymm (by simpa [hSzero] using hi)
          (sq_nonneg _)
        exact sq_eq_zero_iff.mp this
      have hDzero : D = fun _ ↦ 0 := by
        funext omega
        simp [D, hdiagZero]
      rw [hDzero]
      simp [not_le.mpr (half_pos htpos)]
    · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSzero)
      have hDiagRaw := hansonWright_diagonal A hAzero
        (fun i ↦ (hXm i).aemeasurable) hsub hindep hK hpsi
        (t := t / 2) (by positivity)
      have hCK0 : 0 ≤ C * K ^ 2 := by positivity
      have hCKle : C * K ^ 2 ≤ 3 * K ^ 2 :=
        mul_le_mul_of_nonneg_right hCle (sq_nonneg K)
      have hquadDen : (C * K ^ 2) ^ 2 * S ≤
          9 * (K ^ 4 * F ^ 2) := by
        calc
          (C * K ^ 2) ^ 2 * S ≤ (3 * K ^ 2) ^ 2 * S :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hCK0 hCKle 2) hS0
          _ ≤ (3 * K ^ 2) ^ 2 * F ^ 2 :=
            mul_le_mul_of_nonneg_left hSle (sq_nonneg (3 * K ^ 2))
          _ = 9 * (K ^ 4 * F ^ 2) := by ring
      have hlinDen : C * K ^ 2 * O ≤ 3 * (K ^ 2 * O) := by
        calc
          C * K ^ 2 * O ≤ (3 * K ^ 2) * O :=
            mul_le_mul_of_nonneg_right hCKle hO.le
          _ = 3 * (K ^ 2 * O) := by ring
      have hqLower : t ^ 2 / (36 * (K ^ 4 * F ^ 2)) ≤
          (t / 2) ^ 2 / ((C * K ^ 2) ^ 2 * S) := by
        apply (div_le_div_iff₀ (by positivity :
          (0 : ℝ) < 36 * (K ^ 4 * F ^ 2)) (by positivity)).2
        have hmul := mul_le_mul_of_nonneg_left hquadDen (sq_nonneg t)
        nlinarith
      have hlLower : t / (6 * (K ^ 2 * O)) ≤
          (t / 2) / (C * K ^ 2 * O) := by
        apply (div_le_div_iff₀ (by positivity :
          (0 : ℝ) < 6 * (K ^ 2 * O)) (by positivity)).2
        have hmul := mul_le_mul_of_nonneg_left hlinDen ht
        nlinarith
      have huQ : u ≤ t ^ 2 / (K ^ 4 * F ^ 2) := by
        dsimp [u]
        exact min_le_left _ _
      have huL : u ≤ t / (K ^ 2 * O) := by
        dsimp [u]
        exact min_le_right _ _
      have hq : c0 * u ≤ (1 / 8) *
          ((t / 2) ^ 2 / ((C * K ^ 2) ^ 2 * S)) := by
        have hbase : 0 ≤ t ^ 2 / (K ^ 4 * F ^ 2) := by positivity
        calc
          c0 * u ≤ c0 * (t ^ 2 / (K ^ 4 * F ^ 2)) :=
            mul_le_mul_of_nonneg_left huQ hc0.le
          _ ≤ (1 / 288 : ℝ) * (t ^ 2 / (K ^ 4 * F ^ 2)) := by
            exact mul_le_mul_of_nonneg_right (by dsimp [c0]; norm_num) hbase
          _ = (1 / 8 : ℝ) *
              (t ^ 2 / (36 * (K ^ 4 * F ^ 2))) := by ring
          _ ≤ (1 / 8 : ℝ) *
              ((t / 2) ^ 2 / ((C * K ^ 2) ^ 2 * S)) :=
            mul_le_mul_of_nonneg_left hqLower (by norm_num)
      have hl : c0 * u ≤ (1 / 8) *
          ((t / 2) / (C * K ^ 2 * O)) := by
        have hbase : 0 ≤ t / (K ^ 2 * O) := by positivity
        calc
          c0 * u ≤ c0 * (t / (K ^ 2 * O)) :=
            mul_le_mul_of_nonneg_left huL hc0.le
          _ ≤ (1 / 48 : ℝ) * (t / (K ^ 2 * O)) := by
            exact mul_le_mul_of_nonneg_right (by dsimp [c0]; norm_num) hbase
          _ = (1 / 8 : ℝ) * (t / (6 * (K ^ 2 * O))) := by ring
          _ ≤ (1 / 8 : ℝ) * ((t / 2) / (C * K ^ 2 * O)) :=
            mul_le_mul_of_nonneg_left hlLower (by norm_num)
      have hDiagExponent : c0 * u ≤ (1 / 8) *
          min
            ((t / 2) ^ 2 / ((C * K ^ 2) ^ 2 * S))
            ((t / 2) / (C * K ^ 2 * O)) := by
        rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        exact le_min hq hl
      calc
        mu {omega | t / 2 ≤ |D omega|} ≤
            ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
              min
                ((t / 2) ^ 2 / ((C * K ^ 2) ^ 2 * S))
                ((t / 2) / (C * K ^ 2 * O)))) := by
          simpa [D, C, S, O] using hDiagRaw
        _ ≤ ENNReal.ofReal (2 * Real.exp (-c0 * u)) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          linarith
  have hevent : {omega | t ≤ |Z omega|} ⊆
      {omega | t / 2 ≤ |D omega|} ∪ {omega | t / 2 ≤ |R omega|} := by
    intro omega hz
    by_cases hd : t / 2 ≤ |D omega|
    · exact Or.inl hd
    · apply Or.inr
      by_contra hr
      have hdlt : |D omega| < t / 2 := lt_of_not_ge hd
      have hrlt : |R omega| < t / 2 := lt_of_not_ge hr
      have htri : |D omega + R omega| ≤ |D omega| + |R omega| :=
        by simpa [Real.norm_eq_abs] using norm_add_le (D omega) (R omega)
      change t ≤ |Z omega| at hz
      rw [hdecomp omega] at hz
      linarith
  have hUnion : mu {omega | t ≤ |Z omega|} ≤
      ENNReal.ofReal (4 * Real.exp (-c0 * u)) := by
    calc
      mu {omega | t ≤ |Z omega|} ≤
          mu ({omega | t / 2 ≤ |D omega|} ∪
            {omega | t / 2 ≤ |R omega|}) := measure_mono hevent
      _ ≤ mu {omega | t / 2 ≤ |D omega|} +
          mu {omega | t / 2 ≤ |R omega|} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * Real.exp (-c0 * u)) +
          ENNReal.ofReal (2 * Real.exp (-c0 * u)) := add_le_add hDiag hOff
      _ = ENNReal.ofReal (4 * Real.exp (-c0 * u)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  change mu {omega | t ≤ |Z omega|} ≤ _
  rw [show (-(1 / 4147200 : ℝ)) *
      min (t ^ 2 / (K ^ 4 * HDP.matrixFrobeniusNorm A ^ 2))
        (t / (K ^ 2 * HDP.matrixOpNorm A)) = -c * u by
    simp only [c, u, F, O]]
  by_cases hsmall : c * u ≤ Real.log 2
  · calc
      mu {omega | t ≤ |Z omega|} ≤ mu Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (2 * Real.exp (-c * u)) := by
        apply ENNReal.ofReal_le_ofReal
        have hexp : (1 / 2 : ℝ) ≤ Real.exp (-c * u) := by
          calc
            (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
              rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
              norm_num
            _ ≤ Real.exp (-c * u) := Real.exp_le_exp.mpr (by linarith)
        nlinarith
  · have hlarge : Real.log 2 ≤ c * u := le_of_not_ge hsmall
    calc
      mu {omega | t ≤ |Z omega|} ≤
          ENNReal.ofReal (4 * Real.exp (-c0 * u)) := hUnion
      _ ≤ ENNReal.ofReal (2 * Real.exp (-c * u)) := by
        apply ENNReal.ofReal_le_ofReal
        have htwo : (2 : ℝ) * Real.exp (-(2 * (c * u))) ≤
            Real.exp (-(c * u)) := by
          calc
            (2 : ℝ) * Real.exp (-(2 * (c * u))) =
                Real.exp (Real.log 2) * Real.exp (-(2 * (c * u))) := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            _ = Real.exp (Real.log 2 + -(2 * (c * u))) := by
              rw [Real.exp_add]
            _ ≤ Real.exp (-(c * u)) := Real.exp_le_exp.mpr (by linarith)
        rw [hc0_eq]
        have hrewrite : -(2 * c) * u = -(2 * (c * u)) := by ring
        rw [hrewrite]
        calc
          4 * Real.exp (-(2 * (c * u))) =
              2 * (2 * Real.exp (-(2 * (c * u)))) := by ring
          _ ≤ 2 * Real.exp (-(c * u)) :=
            mul_le_mul_of_nonneg_left htwo (by norm_num)
          _ = 2 * Real.exp (-c * u) := by rw [neg_mul]

/-- Source-numbered alias for Theorem 6.2.2. -/
abbrev theorem_6_2_2 := @hansonWright

end

end HDP.Chapter6

end Source_06_HansonWright

/-! ## Material formerly in `07_SymmetricDistributions.lean` -/

section Source_07_SymmetricDistributions

/-!
# Chapter 6, §6.3: symmetric distributions

This file formalizes Lemma 6.3.1 in full.  The source checks only that
`ξ * X` is symmetric and leaves every remaining assertion to Exercise 6.16;
the exercise is load-bearing, so its sole authoritative implementation is
kept here in core.

The source-wide predicate `HDP.IsSymmetricRV` is equality in distribution with
the pointwise negation.  It is defined for an arbitrary measurable type with
negation, while the absolute-value reconstruction argument used for parts
(a) and (b) is specialized to real random variables.  Part (c) is proved at
the more useful generality of measurable additive groups, so it also applies
to the random vectors used later in the chapter.
-/

open MeasureTheory ProbabilityTheory

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A random variable is symmetric when it and its pointwise negation have the same
distribution. The `IdentDistrib` formulation records both required almost-everywhere
measurability facts and is safe for non-measurable raw functions.

**Lean implementation helper.** -/
def IsSymmetricRV {E : Type*} [MeasurableSpace E] [Neg E]
    (X : Ω → E) (μ : Measure Ω) : Prop :=
  IdentDistrib X (fun ω => -X ω) μ μ

namespace IsSymmetricRV

/-- Cosine is unchanged when the scalar argument `x` is replaced by `|x|`.

**Lean implementation helper.** -/
private theorem cos_mul_abs (t x : ℝ) :
    Real.cos (t * x) = Real.cos (t * |x|) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, mul_neg, Real.cos_neg]

/-- The real part of a real random variable's characteristic function only depends on the law of
its absolute value.

**Lean implementation helper.** -/
theorem charFun_re_eq_integral_cos_abs [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (t : ℝ) :
    (charFun (Measure.map X μ) t).re =
      ∫ ω, Real.cos (t * |X ω|) ∂μ := by
  rw [charFun_apply_real, integral_map hX (by fun_prop)]
  have hint : Integrable
      (fun ω => Complex.exp ((t : ℂ) * (X ω : ℂ) * Complex.I)) μ :=
    (integrable_const (1 : ℝ)).mono (by fun_prop) (by
      filter_upwards with ω
      rw [show (t : ℂ) * (X ω : ℂ) = ((t * X ω : ℝ) : ℂ) by norm_num,
        Complex.norm_exp_ofReal_mul_I]
      simp)
  rw [← RCLike.re_eq_complex_re, ← integral_re hint]
  apply integral_congr_ae
  filter_upwards with ω
  rw [show (t : ℂ) * (X ω : ℂ) = ((t * X ω : ℝ) : ℂ) by norm_num,
    RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re]
  exact cos_mul_abs t (X ω)

/-- Symmetry of `X` is invariance of its pushforward law under negation.

**Lean implementation helper.** -/
theorem map_neg_eq (X : Ω → ℝ) (h : IsSymmetricRV X μ) :
    Measure.map (fun x : ℝ => -x) (Measure.map X μ) = Measure.map X μ := by
  rw [AEMeasurable.map_map_of_aemeasurable measurable_neg.aemeasurable
    h.aemeasurable_fst]
  exact h.map_eq.symm

/-- A symmetric real law has an even characteristic function.

**Lean implementation helper.** -/
theorem charFun_eq_neg (X : Ω → ℝ) (h : IsSymmetricRV X μ) (t : ℝ) :
    charFun (Measure.map X μ) t = charFun (Measure.map X μ) (-t) := by
  calc
    charFun (Measure.map X μ) t =
        charFun (Measure.map (fun x : ℝ => -x) (Measure.map X μ)) t := by
          rw [h.map_neg_eq X]
    _ = charFun (Measure.map X μ) (-t) := by
      convert charFun_map_mul (μ := Measure.map X μ) (-1) t using 1 <;> simp

/-- A symmetric real law has a real-valued characteristic function.

**Lean implementation helper.** -/
theorem charFun_im_eq_zero (X : Ω → ℝ) (h : IsSymmetricRV X μ) (t : ℝ) :
    (charFun (Measure.map X μ) t).im = 0 := by
  have hc : charFun (Measure.map X μ) t =
      star (charFun (Measure.map X μ) t) := by
    calc
      charFun (Measure.map X μ) t = charFun (Measure.map X μ) (-t) :=
        h.charFun_eq_neg X t
      _ = star (charFun (Measure.map X μ) t) := charFun_neg t
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- Two symmetric real random variables with identically distributed absolute values are
identically distributed. This avoids any moment or integrability assumption: uniqueness is
obtained from characteristic functions.

**Lean implementation helper.** -/
theorem identDistrib_of_abs [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : IsSymmetricRV X μ) (hY : IsSymmetricRV Y μ)
    (habs : IdentDistrib (fun ω => |X ω|) (fun ω => |Y ω|) μ μ) :
    IdentDistrib X Y μ μ := by
  refine ⟨hX.aemeasurable_fst, hY.aemeasurable_fst, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  apply Complex.ext
  · rw [charFun_re_eq_integral_cos_abs X hX.aemeasurable_fst t,
      charFun_re_eq_integral_cos_abs Y hY.aemeasurable_fst t]
    have hc :=
      (habs.comp (by fun_prop : Measurable fun x : ℝ => Real.cos (t * x))).integral_eq
    simpa only [Function.comp_apply] using hc
  · rw [hX.charFun_im_eq_zero X t, hY.charFun_im_eq_zero Y t]

end IsSymmetricRV

/-- A Rademacher random variable is symmetric.

**Lean implementation helper.** -/
theorem IsRademacher.isSymmetricRV {ε : Ω → ℝ}
    (hε : IsRademacher ε μ) : IsSymmetricRV ε μ := by
  let p : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hp : unitInterval.symm p = p := by
    ext
    norm_num [p, unitInterval.symm]
  refine ⟨hε.aemeasurable, hε.aemeasurable.neg, ?_⟩
  rw [show (fun ω => -ε ω) = (fun x : ℝ => -x) ∘ ε by rfl,
    ← AEMeasurable.map_map_of_aemeasurable measurable_neg.aemeasurable hε.aemeasurable,
    hε.map_eq, map_bernoulliMeasure']
  · have hswap : bernoulliMeasure (1 : ℝ) (-1) p =
        bernoulliMeasure (-1) 1 p := by
      rw [bernoulliMeasure_def, bernoulliMeasure_def, hp, add_comm]
    simpa [p] using hswap
  · fun_prop

end HDP

namespace HDP.Chapter6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Multiplying an independent random variable by a symmetric real random sign produces a
symmetric random variable.

**Lean implementation helper.** -/
theorem isSymmetricRV_mul_of_left [IsFiniteMeasure μ]
    {ε X : Ω → ℝ} (hε : HDP.IsSymmetricRV ε μ)
    (hX : AEMeasurable X μ) (hind : IndepFun ε X μ) :
    HDP.IsSymmetricRV (fun ω => ε ω * X ω) μ := by
  have hnegInd : IndepFun (fun ω => -ε ω) X μ := by
    change IndepFun (-ε) X μ
    exact hind.neg_left
  have hjoint : IdentDistrib (fun ω => (ε ω, X ω))
      (fun ω => (-ε ω, X ω)) μ μ :=
    hε.prodMk (IdentDistrib.refl hX) hind hnegInd
  have hmul :=
    hjoint.comp (by fun_prop : Measurable fun z : ℝ × ℝ => z.1 * z.2)
  simpa [HDP.IsSymmetricRV, Function.comp_def] using hmul

/-- A Rademacher sign times an independent real random variable is symmetric.

**Lean implementation helper.** -/
theorem rademacher_mul_isSymmetricRV [IsFiniteMeasure μ]
    {ε X : Ω → ℝ} (hε : HDP.IsRademacher ε μ)
    (hX : AEMeasurable X μ) (hind : IndepFun ε X μ) :
    HDP.IsSymmetricRV (fun ω => ε ω * X ω) μ :=
  isSymmetricRV_mul_of_left hε.isSymmetricRV hX hind

/-- Multiplication by a Rademacher sign preserves absolute value in distribution (indeed, almost
surely).

**Lean implementation helper.** -/
theorem abs_rademacher_mul_identDistrib [IsFiniteMeasure μ]
    {ε X : Ω → ℝ} (hε : HDP.IsRademacher ε μ)
    (hX : AEMeasurable X μ) :
    IdentDistrib (fun ω => |ε ω * X ω|) (fun ω => |X ω|) μ μ := by
  apply IdentDistrib.of_ae_eq (hε.aemeasurable.mul hX).abs
  filter_upwards [hε.ae_mem] with ω hω
  rcases hω with hω | hω <;> simp [hω]

/-- The corresponding source lemma, with the omitted proof supplied as required by the
corresponding exercise: the two Rademacher symmetrizations have the same law and are both
symmetric.

**Book Lemma 6.3.1.** -/
theorem constructingSymmetricDistributions_part_a [IsFiniteMeasure μ]
    {ε X : Ω → ℝ} (hε : HDP.IsRademacher ε μ)
    (hX : AEMeasurable X μ) (hind : IndepFun ε X μ) :
    IdentDistrib (fun ω => ε ω * X ω) (fun ω => ε ω * |X ω|) μ μ ∧
      HDP.IsSymmetricRV (fun ω => ε ω * X ω) μ ∧
      HDP.IsSymmetricRV (fun ω => ε ω * |X ω|) μ := by
  have hindAbs : IndepFun ε (fun ω => |X ω|) μ := by
    change IndepFun (id ∘ ε) (abs ∘ X) μ
    exact hind.comp measurable_id measurable_abs
  have hsX := rademacher_mul_isSymmetricRV hε hX hind
  have hsAbs := rademacher_mul_isSymmetricRV hε hX.abs hindAbs
  have habs : IdentDistrib (fun ω => abs (ε ω * X ω))
      (fun ω => abs (ε ω * abs (X ω))) μ μ := by
    apply IdentDistrib.of_ae_eq (hε.aemeasurable.mul hX).abs
    filter_upwards [hε.ae_mem] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  exact ⟨HDP.IsSymmetricRV.identDistrib_of_abs hsX hsAbs habs, hsX, hsAbs⟩

/-- The corresponding source lemma, also the core payload of the corresponding exercise:
when `X` is symmetric, both Rademacher symmetrizations have the law of `X`.

**Lean implementation helper.** -/
theorem constructingSymmetricDistributions_part_b [IsFiniteMeasure μ]
    {ε X : Ω → ℝ} (hε : HDP.IsRademacher ε μ)
    (hX : AEMeasurable X μ) (hind : IndepFun ε X μ)
    (hsym : HDP.IsSymmetricRV X μ) :
    IdentDistrib (fun ω => ε ω * X ω) X μ μ ∧
      IdentDistrib (fun ω => ε ω * |X ω|) X μ μ := by
  obtain ⟨hsame, hsMul, _hsMulAbs⟩ :=
    constructingSymmetricDistributions_part_a hε hX hind
  have hmulX : IdentDistrib (fun ω => ε ω * X ω) X μ μ :=
    HDP.IsSymmetricRV.identDistrib_of_abs hsMul hsym
      (abs_rademacher_mul_identDistrib hε hX)
  exact ⟨hmulX, hsame.symm.trans hmulX⟩

/-- The corresponding source lemma, generalized to measurable additive groups so the same
core result applies to the random vectors used later in §6.3. This is the final promoted payload
of the corresponding exercise.

**Book Lemma 6.3.1.** -/
theorem independentCopy_sub_isSymmetricRV [IsFiniteMeasure μ]
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [MeasurableSub₂ E]
    {X X' : Ω → E} (hcopy : IsIndependentCopy X X' μ) :
    HDP.IsSymmetricRV (fun ω => X ω - X' ω) μ := by
  have hjoint : IdentDistrib (fun ω => (X ω, X' ω))
      (fun ω => (X' ω, X ω)) μ μ :=
    hcopy.identDistrib.prodMk hcopy.identDistrib.symm
      hcopy.indepFun hcopy.indepFun.symm
  have hsub := hjoint.comp
    (measurable_fst.sub measurable_snd : Measurable fun z : E × E => z.1 - z.2)
  simpa [HDP.IsSymmetricRV, Function.comp_def] using hsub

/-- The corresponding source lemma on constructing symmetric distributions, in its exact
three-part logical form. The source proves only one assertion and delegates all remaining
assertions to the corresponding exercise; every component here is proved.

**Book Lemma 6.3.1.** -/
theorem constructingSymmetricDistributions [IsProbabilityMeasure μ]
    {ε X X' : Ω → ℝ} (hε : HDP.IsRademacher ε μ)
    (hX : AEMeasurable X μ) (hind : IndepFun ε X μ) :
    (IdentDistrib (fun ω => ε ω * X ω) (fun ω => ε ω * |X ω|) μ μ ∧
        HDP.IsSymmetricRV (fun ω => ε ω * X ω) μ ∧
        HDP.IsSymmetricRV (fun ω => ε ω * |X ω|) μ) ∧
      (HDP.IsSymmetricRV X μ →
        IdentDistrib (fun ω => ε ω * X ω) X μ μ ∧
        IdentDistrib (fun ω => ε ω * |X ω|) X μ μ) ∧
      (IsIndependentCopy X X' μ →
        HDP.IsSymmetricRV (fun ω => X ω - X' ω) μ) := by
  exact ⟨constructingSymmetricDistributions_part_a hε hX hind,
    constructingSymmetricDistributions_part_b hε hX hind,
    independentCopy_sub_isSymmetricRV⟩

end HDP.Chapter6

end Source_07_SymmetricDistributions

/-! ## Material formerly in `08_Symmetrization.lean` -/

section Source_08_Symmetrization

/-!
# Chapter 6, §6.3: symmetrization

The two probability spaces in the public API encode the source's implicit
assumption that the Rademacher signs are jointly independent of the random
vectors.  This avoids hiding a conditional-independence hypothesis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter6

noncomputable section

/-- Independent coordinate families on separate probability spaces remain independent after
their corresponding coordinates are paired on the product space.

**Lean implementation helper.** -/
theorem iIndepFun_prodMk_prod
    {ι Ω Ω' E F : Type*} [Finite ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [MeasurableSpace F] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {Y : ι → Ω' → F}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hXind : iIndepFun X μ) (hYind : iIndepFun Y ν) :
    iIndepFun (fun i (z : Ω × Ω') => (X i z.1, Y i z.2)) (μ.prod ν) := by
  letI := Fintype.ofFinite ι
  let XV : Ω → (ι → E) := fun ω i => X i ω
  let YV : Ω' → (ι → F) := fun ω i => Y i ω
  let zip : ((ι → E) × (ι → F)) → (ι → E × F) :=
    (MeasurableEquiv.arrowProdEquivProdArrow E F ι).symm
  have hXVm : Measurable XV := measurable_pi_lambda _ hXm
  have hYVm : Measurable YV := measurable_pi_lambda _ hYm
  have hzipm : Measurable zip :=
    (MeasurableEquiv.arrowProdEquivProdArrow E F ι).symm.measurable
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (f := fun i (z : Ω × Ω') => (X i z.1, Y i z.2))
    (fun i => ((hXm i).comp measurable_fst |>.prodMk
      ((hYm i).comp measurable_snd)).aemeasurable)]
  have hfun : (fun z : Ω × Ω' => fun i => (X i z.1, Y i z.2)) =
      zip ∘ Prod.map XV YV := by
    funext z i
    rfl
  rw [hfun, ← Measure.map_map hzipm (hXVm.prodMap hYVm),
    ← Measure.map_prod_map μ ν hXVm hYVm,
    hXind.map_fun_eq_pi_map (fun i => (hXm i).aemeasurable),
    hYind.map_fun_eq_pi_map (fun i => (hYm i).aemeasurable)]
  rw [(MeasureTheory.measurePreserving_arrowProdEquivProdArrow E F ι
    (fun i => μ.map (X i)) (fun i => ν.map (Y i))).symm.map_eq]
  congr 1
  funext i
  calc
    (μ.map (X i)).prod (ν.map (Y i)) =
        (μ.prod ν).map (Prod.map (X i) (Y i)) :=
      Measure.map_prod_map μ ν (hXm i) (hYm i)
    _ = (μ.prod ν).map (fun z => (X i z.1, Y i z.2)) := by
      congr 1

/-- A Rademacher sign on a separate probability space does not change a symmetric vector law.
This is the vector-valued counterpart of the corresponding lemma.

**Lean implementation helper.** -/
theorem identDistrib_rademacher_smul_symmetric
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → E} {ε : Ω' → ℝ}
    (hXm : Measurable X) (hεm : Measurable ε)
    (hXsym : HDP.IsSymmetricRV X μ) (hε : HDP.IsRademacher ε ν) :
    IdentDistrib (fun z : Ω × Ω' => ε z.2 • X z.1) X (μ.prod ν) μ := by
  let act : E × ℝ → E := fun z => z.2 • z.1
  have hact : Measurable act := by fun_prop
  have hpair :
      (μ.map X).prod (ν.map ε) =
        (μ.prod ν).map (Prod.map X ε) :=
    Measure.map_prod_map μ ν hXm hεm
  have hneg : (μ.map X).map (fun x : E => -x) = μ.map X := by
    rw [Measure.map_map (by fun_prop) hXm]
    exact hXsym.map_eq.symm
  refine ⟨(hεm.comp measurable_snd).smul (hXm.comp measurable_fst) |>.aemeasurable,
    hXm.aemeasurable, ?_⟩
  have hfun : (fun z : Ω × Ω' => ε z.2 • X z.1) =
      act ∘ Prod.map X ε := by
    rfl
  rw [hfun, ← Measure.map_map hact (hXm.prodMap hεm), ← hpair, hε.map_eq]
  rw [bernoulliMeasure_def, Measure.prod_add]
  rw [Measure.map_add _ _ hact]
  have hprod (c : ℝ≥0) (y : ℝ) :
      (μ.map X).prod (c • Measure.dirac y) =
        c • ((μ.map X).prod (Measure.dirac y)) := by
    change (μ.map X).prod ((c : ℝ≥0∞) • Measure.dirac y) =
      (c : ℝ≥0∞) • ((μ.map X).prod (Measure.dirac y))
    rw [Measure.prod_smul_right]
  rw [hprod, hprod, Measure.map_smul, Measure.map_smul, Measure.prod_dirac,
    Measure.prod_dirac]
  rw [Measure.map_map hact (by fun_prop),
    Measure.map_map hact (by fun_prop)]
  change unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ •
        (μ.map X).map (fun x : E => (1 : ℝ) • x) +
      unitInterval.toNNReal
          (unitInterval.symm ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) •
        (μ.map X).map (fun x : E => (-1 : ℝ) • x) = μ.map X
  have hw :
      unitInterval.toNNReal
          (unitInterval.symm ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) =
        unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ := by
    ext
    norm_num
  rw [hw]
  simp only [one_smul, neg_one_smul, hneg]
  have hid : (μ.map X).map (fun x : E => x) = μ.map X := by
    change (μ.map X).map id = μ.map X
    rw [Measure.map_id]
  rw [hid]
  rw [← add_smul]
  have hsum :
      unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ +
        unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ = 1 := by
    ext
    norm_num
  rw [hsum, one_smul]

/-- Coordinatewise multiplication by an independent Rademacher family does not change the joint
law of an independent family of symmetric random vectors.

**Lean implementation helper.** -/
theorem identDistrib_rademacher_smul_family
    {ι Ω Ω' E : Type*} [Finite ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hεm : ∀ i, Measurable (ε i))
    (hXsym : ∀ i, HDP.IsSymmetricRV (X i) μ)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hXind : iIndepFun X μ) (hεind : iIndepFun ε ν) :
    IdentDistrib (fun z : Ω × Ω' => fun i => ε i z.2 • X i z.1)
      (fun ω => fun i => X i ω) (μ.prod ν) μ := by
  letI := Fintype.ofFinite ι
  have hpairs : iIndepFun
      (fun i (z : Ω × Ω') => (X i z.1, ε i z.2)) (μ.prod ν) :=
    iIndepFun_prodMk_prod hXm hεm hXind hεind
  have hsigned : iIndepFun
      (fun i (z : Ω × Ω') => ε i z.2 • X i z.1) (μ.prod ν) := by
    simpa [Function.comp_def] using hpairs.comp
      (fun _ (z : E × ℝ) => z.2 • z.1) (fun _ => by fun_prop)
  exact IdentDistrib.pi
    (fun i => identDistrib_rademacher_smul_symmetric
      (hXm i) (hεm i) (hXsym i) (hε i)) hsigned hXind

/-- In a form useful beyond the norm: adding an independent centered random vector can only
increase the expectation of a continuous convex functional. Independence is encoded without an
extra predicate by placing `Y` and `Z` on separate probability spaces and adding them on the
product space.

**Book Equation (6.13).** -/
theorem integral_convex_le_integral_add_independent_centered
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : Ω → E} {Z : Ω' → E} {F : E → ℝ}
    (hFconv : ConvexOn ℝ Set.univ F) (hFcont : Continuous F)
    (hZ : Integrable Z ν)
    (hZ0 : ∫ z, Z z ∂ν = 0)
    (hFY : Integrable (F ∘ Y) μ)
    (hFadd : Integrable (fun p : Ω × Ω' => F (Y p.1 + Z p.2)) (μ.prod ν)) :
    ∫ y, F (Y y) ∂μ ≤
      ∫ p : Ω × Ω', F (Y p.1 + Z p.2) ∂μ.prod ν := by
  have hslice : ∀ᵐ y ∂μ,
      Integrable (fun z => F (Y y + Z z)) ν :=
    hFadd.prod_right_ae
  have hjensen : ∀ᵐ y ∂μ,
      F (Y y) ≤ ∫ z, F (Y y + Z z) ∂ν := by
    filter_upwards [hslice] with y hy
    have hyZ : Integrable (fun z => Y y + Z z) ν :=
      (integrable_const (Y y)).add hZ
    have hint : ∫ z, Y y + Z z ∂ν = Y y := by
      rw [integral_add (integrable_const (Y y)) hZ, integral_const, hZ0]
      simp
    have hmap := hFconv.map_integral_le hFcont.continuousOn isClosed_univ
      (by simp) hyZ
      (by simpa [Function.comp_def] using hy)
    simpa [hint] using hmap
  have houter : Integrable (fun y => ∫ z, F (Y y + Z z) ∂ν) μ :=
    hFadd.integral_prod_left
  calc
    ∫ y, F (Y y) ∂μ = ∫ y, (F ∘ Y) y ∂μ := by rfl
    _ ≤ ∫ y, ∫ z, F (Y y + Z z) ∂ν ∂μ :=
      integral_mono_ae hFY houter hjensen
    _ = ∫ p : Ω × Ω', F (Y p.1 + Z p.2) ∂μ.prod ν :=
      (integral_prod _ hFadd).symm

/-- Equation (6.13) of the source: if `Z` is centered and independent of `Y`, then `E ‖Y‖ ≤ E ‖Y
+ Z‖`. The separate source spaces encode the independence assumption.

**Book (6.13).** -/
theorem integral_norm_le_integral_norm_add_independent_centered
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : Ω → E} {Z : Ω' → E}
    (hY : Integrable Y μ) (hZ : Integrable Z ν)
    (hZ0 : ∫ z, Z z ∂ν = 0) :
    ∫ y, ‖Y y‖ ∂μ ≤
      ∫ p : Ω × Ω', ‖Y p.1 + Z p.2‖ ∂μ.prod ν := by
  apply integral_convex_le_integral_add_independent_centered
    (convexOn_norm convex_univ) continuous_norm hZ hZ0 hY.norm
  exact (hY.comp_fst ν).add (hZ.comp_snd μ) |>.norm

/-- The finite random-vector sum used in the corresponding lemma.

**Lean implementation helper.** -/
def randomVectorSum {ι Ω E : Type*} [Fintype ι]
    [AddCommMonoid E] (X : ι → Ω → E) (ω : Ω) : E :=
  ∑ i, X i ω

/-- The independently signed finite random-vector sum used in the corresponding lemma.

**Lean implementation helper.** -/
def signedRandomVectorSum {ι Ω Ω' E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : ι → Ω → E) (ε : ι → Ω' → ℝ) (z : Ω × Ω') : E :=
  ∑ i, ε i z.2 • X i z.1

/-- Establishes integrability of random vector sum.

**Lean implementation helper.** -/
lemma integrable_randomVectorSum
    {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {X : ι → Ω → E}
    (hX : ∀ i, Integrable (X i) μ) :
    Integrable (randomVectorSum X) μ := by
  exact integrable_finsetSum Finset.univ (fun i _ => hX i)

/-- Establishes integrability of signed random vector sum.

**Lean implementation helper.** -/
lemma integrable_signedRandomVectorSum
    {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hX : ∀ i, Integrable (X i) μ)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν) :
    Integrable (signedRandomVectorSum X ε) (μ.prod ν) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have hi : Integrable
      (fun z : Ω' × Ω => ε i z.1 • X i z.2) (ν.prod μ) :=
    (((hε i).memLp 1).integrable le_rfl).smul_prod (hX i)
  simpa [signedRandomVectorSum, Function.comp_def] using hi.swap

/-- The two coordinate projections of a product space give an independent copy of any measurable
random object.

**Lean implementation helper.** -/
lemma isIndependentCopy_prod_fst_snd
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → E} (hX : Measurable X) :
    IsIndependentCopy (fun z : Ω × Ω => X z.1)
      (fun z : Ω × Ω => X z.2) (μ.prod μ) := by
  have hXLaw : HasLaw X (μ.map X) μ :=
    ⟨hX.aemeasurable, rfl⟩
  have hfst : HasLaw (fun z : Ω × Ω => X z.1) (μ.map X) (μ.prod μ) := by
    simpa [Function.comp_def] using hXLaw.comp
      (measurePreserving_fst (α := Ω) (β := Ω) (μ := μ) (ν := μ)).hasLaw
  have hsnd : HasLaw (fun z : Ω × Ω => X z.2) (μ.map X) (μ.prod μ) := by
    simpa [Function.comp_def] using hXLaw.comp
      (measurePreserving_snd (α := Ω) (β := Ω) (μ := μ) (ν := μ)).hasLaw
  exact ⟨⟨hfst.aemeasurable, hsnd.aemeasurable,
      hfst.map_eq.trans hsnd.map_eq.symm⟩,
    indepFun_prod hX hX⟩

/-- The signed independent-copy differences have the same joint law as the unsigned differences.
This is the distributional core of symmetrization.

**Lean implementation helper.** -/
lemma identDistrib_signed_independentCopy_sub
    {ι Ω Ω' E : Type*} [Finite ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSub₂ E] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hεm : ∀ i, Measurable (ε i))
    (hXind : iIndepFun X μ) (hεind : iIndepFun ε ν)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν) :
    IdentDistrib
      (fun z : (Ω × Ω) × Ω' => fun i =>
        ε i z.2 • (X i z.1.1 - X i z.1.2))
      (fun z : Ω × Ω => fun i => X i z.1 - X i z.2)
      ((μ.prod μ).prod ν) (μ.prod μ) := by
  letI := Fintype.ofFinite ι
  let D : ι → (Ω × Ω) → E :=
    fun i z => X i z.1 - X i z.2
  have hpair : iIndepFun
      (fun i (z : Ω × Ω) => (X i z.1, X i z.2)) (μ.prod μ) :=
    iIndepFun_prodMk_prod hXm hXm hXind hXind
  have hDind : iIndepFun D (μ.prod μ) := by
    simpa [D, Function.comp_def] using hpair.comp
      (fun _ (z : E × E) => z.1 - z.2)
      (fun _ => measurable_fst.sub measurable_snd)
  have hDm : ∀ i, Measurable (D i) := fun i => by
    dsimp only [D]
    exact (hXm i).comp measurable_fst |>.sub ((hXm i).comp measurable_snd)
  have hDsym : ∀ i, HDP.IsSymmetricRV (D i) (μ.prod μ) := by
    intro i
    simpa [D] using independentCopy_sub_isSymmetricRV
      (isIndependentCopy_prod_fst_snd (hXm i))
  simpa [D] using identDistrib_rademacher_smul_family
    hDm hεm hDsym hε hDind hεind

/-- The elementary triangle-inequality half of the independent-copy method: the expected
distance from an independent copy is at most twice the expected norm.

**Lean implementation helper.** -/
lemma integral_norm_sub_independentCopy_le_two
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → E} (hY : Integrable Y μ) :
    (∫ z : Ω × Ω, ‖Y z.1 - Y z.2‖ ∂μ.prod μ) ≤
      2 * ∫ ω, ‖Y ω‖ ∂μ := by
  have hdiff : Integrable (fun z : Ω × Ω => Y z.1 - Y z.2) (μ.prod μ) :=
    (hY.comp_fst μ).sub (hY.comp_snd μ)
  have hmajor : Integrable
      (fun z : Ω × Ω => ‖Y z.1‖ + ‖Y z.2‖) (μ.prod μ) :=
    (hY.norm.comp_fst μ).add (hY.norm.comp_snd μ)
  have hfst :
      (∫ z : Ω × Ω, ‖Y z.1‖ ∂μ.prod μ) = ∫ ω, ‖Y ω‖ ∂μ := by
    rw [integral_prod _ (hY.norm.comp_fst μ)]
    simp
  have hsnd :
      (∫ z : Ω × Ω, ‖Y z.2‖ ∂μ.prod μ) = ∫ ω, ‖Y ω‖ ∂μ := by
    rw [integral_prod _ (hY.norm.comp_snd μ)]
    simp
  calc
    (∫ z : Ω × Ω, ‖Y z.1 - Y z.2‖ ∂μ.prod μ) ≤
        ∫ z : Ω × Ω, (‖Y z.1‖ + ‖Y z.2‖) ∂μ.prod μ := by
      apply integral_mono hdiff.norm hmajor
      intro z
      exact norm_sub_le _ _
    _ = (∫ z : Ω × Ω, ‖Y z.1‖ ∂μ.prod μ) +
        ∫ z : Ω × Ω, ‖Y z.2‖ ∂μ.prod μ := by
      rw [integral_add (hY.norm.comp_fst μ) (hY.norm.comp_snd μ)]
    _ = 2 * ∫ ω, ‖Y ω‖ ∂μ := by rw [hfst, hsnd]; ring

/-- At the level of the norm of the total sum, the signed independent-copy differences and
unsigned independent-copy differences have equal expectation.

**Lean implementation helper.** -/
lemma integral_norm_signed_independentCopy_sub_eq
    {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hεm : ∀ i, Measurable (ε i))
    (hXind : iIndepFun X μ) (hεind : iIndepFun ε ν)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν) :
    (∫ z : (Ω × Ω) × Ω',
        ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
          ∂(μ.prod μ).prod ν) =
      ∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ := by
  let F : (ι → E) → ℝ := fun x => ‖∑ i, x i‖
  have hF : Measurable F := by
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => measurable_pi_apply i)).norm
  have hLaw := (identDistrib_signed_independentCopy_sub
    hXm hεm hXind hεind hε).comp hF
  simpa [F, Function.comp_def] using hLaw.integral_eq

/-- The signed independent-copy difference is bounded by two copies of the original signed sum.
This analytic half of symmetrization does not require independence within either family.

**Lean implementation helper.** -/
lemma integral_norm_signed_independentCopy_sub_le_two
    {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν) :
    (∫ z : (Ω × Ω) × Ω',
        ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
          ∂(μ.prod μ).prod ν) ≤
      2 * ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν := by
  have hsignedInt : Integrable
      (fun z : Ω × Ω' => ∑ i, ε i z.2 • X i z.1) (μ.prod ν) := by
    convert (integrable_signedRandomVectorSum hXint hε) using 1
    funext z
    rfl
  let D : ι → (Ω × Ω) → E :=
    fun i z => X i z.1 - X i z.2
  have hDint : ∀ i, Integrable (D i) (μ.prod μ) := fun i => by
    exact (hXint i).comp_fst μ |>.sub ((hXint i).comp_snd μ)
  have hsignedDInt : Integrable
      (fun z : (Ω × Ω) × Ω' =>
        ∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2))
      ((μ.prod μ).prod ν) := by
    convert (integrable_signedRandomVectorSum hDint hε) using 1
    funext z
    rfl
  have hslice (η : Ω') :
      (∫ z : Ω × Ω,
          ‖∑ i, ε i η • (X i z.1 - X i z.2)‖ ∂μ.prod μ) ≤
        2 * ∫ ω, ‖∑ i, ε i η • X i ω‖ ∂μ := by
    have hηint : Integrable (fun ω => ∑ i, ε i η • X i ω) μ :=
      integrable_finsetSum Finset.univ
        (fun i _ => by
          convert (hXint i).smul (ε i η) using 1 <;> rfl)
    simpa only [Finset.sum_sub_distrib, smul_sub] using
      (integral_norm_sub_independentCopy_le_two hηint)
  have houter := integral_mono
    hsignedDInt.norm.integral_prod_right
    (hsignedInt.norm.integral_prod_right.const_mul 2) hslice
  calc
    (∫ z : (Ω × Ω) × Ω',
        ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
          ∂(μ.prod μ).prod ν) =
        ∫ η, ∫ z : Ω × Ω,
          ‖∑ i, ε i η • (X i z.1 - X i z.2)‖ ∂μ.prod μ ∂ν :=
      integral_prod_symm _ hsignedDInt.norm
    _ ≤ ∫ η, 2 * ∫ ω, ‖∑ i, ε i η • X i ω‖ ∂μ ∂ν := houter
    _ = 2 * ∫ η, ∫ ω, ‖∑ i, ε i η • X i ω‖ ∂μ ∂ν := by
      rw [integral_const_mul]
    _ = 2 * ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν := by
      rw [integral_prod_symm _ hsignedInt.norm]

/-- For independent centered integrable random vectors and a jointly independent Rademacher
family, the expected norm of the ordinary sum and that of the independently signed sum agree up
to the sharp factors displayed in the source. The vectors and signs live on separate probability
spaces. Thus their mutual independence is structural, while `hXind` and `hεind` state
independence within the two respective families.

**Book Lemma 6.3.2.** -/
theorem symmetrization
    {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν) :
    ((1 / 2 : ℝ) *
        ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν) ≤
        ∫ ω, ‖∑ i, X i ω‖ ∂μ ∧
      (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
        2 * ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν := by
  have hsumInt : Integrable (fun ω => ∑ i, X i ω) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hXint i)
  have hsum0 : ∫ ω, ∑ i, X i ω ∂μ = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hXint i)]
    simp [hX0]
  have hsignedInt : Integrable
      (fun z : Ω × Ω' => ∑ i, ε i z.2 • X i z.1) (μ.prod ν) := by
    convert (integrable_signedRandomVectorSum hXint hε) using 1
    funext z
    rfl
  let D : ι → (Ω × Ω) → E :=
    fun i z => X i z.1 - X i z.2
  have hDint : ∀ i, Integrable (D i) (μ.prod μ) := fun i => by
    exact (hXint i).comp_fst μ |>.sub ((hXint i).comp_snd μ)
  have hsignedDInt : Integrable
      (fun z : (Ω × Ω) × Ω' =>
        ∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2))
      ((μ.prod μ).prod ν) := by
    convert (integrable_signedRandomVectorSum hDint hε) using 1
    funext z
    rfl
  have hsignedD_eq_D :
      (∫ z : (Ω × Ω) × Ω',
          ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
            ∂(μ.prod μ).prod ν) =
        ∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ :=
    integral_norm_signed_independentCopy_sub_eq
      hXm hεm hXind hεind hε
  have hsum_le_D :
      (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
        ∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ := by
    have hcenteredNeg :
        ∫ ω, -( ∑ i, X i ω) ∂μ = 0 := by
      rw [integral_neg]
      simp [hsum0]
    have haux := integral_norm_le_integral_norm_add_independent_centered
      (Y := fun ω => ∑ i, X i ω) (Z := fun ω => -(∑ i, X i ω))
      hsumInt hsumInt.neg hcenteredNeg
    calc
      (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
          ∫ z : Ω × Ω,
            ‖(∑ i, X i z.1) + -(∑ i, X i z.2)‖ ∂μ.prod μ := haux
      _ = ∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [← sub_eq_add_neg, Finset.sum_sub_distrib]
  have hD_le_two_sum :
      (∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ) ≤
        2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
    have haux := integral_norm_sub_independentCopy_le_two hsumInt
    calc
      (∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ) =
          ∫ z : Ω × Ω, ‖(∑ i, X i z.1) - (∑ i, X i z.2)‖ ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [Finset.sum_sub_distrib]
      _ ≤ 2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ := haux
  have hsignedD_le_two_signed :
      (∫ z : (Ω × Ω) × Ω',
          ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
            ∂(μ.prod μ).prod ν) ≤
        2 * ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν :=
    integral_norm_signed_independentCopy_sub_le_two hXint hε
  have hslice_signed_le_signedD (η : Ω') :
      (∫ ω, ‖∑ i, ε i η • X i ω‖ ∂μ) ≤
        ∫ z : Ω × Ω,
          ‖∑ i, ε i η • (X i z.1 - X i z.2)‖ ∂μ.prod μ := by
    have hηint : Integrable (fun ω => ∑ i, ε i η • X i ω) μ :=
      integrable_finsetSum Finset.univ
        (fun i _ => by
          convert (hXint i).smul (ε i η) using 1 <;> rfl)
    have hη0 : ∫ ω, ∑ i, ε i η • X i ω ∂μ = 0 := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => by
          convert (hXint i).smul (ε i η) using 1
          rfl)]
      simp [integral_smul, hX0]
    have hneg0 : ∫ ω, -(∑ i, ε i η • X i ω) ∂μ = 0 := by
      rw [integral_neg]
      simp [hη0]
    have haux := integral_norm_le_integral_norm_add_independent_centered
      (Y := fun ω => ∑ i, ε i η • X i ω)
      (Z := fun ω => -(∑ i, ε i η • X i ω))
      hηint hηint.neg hneg0
    simpa only [← sub_eq_add_neg, Finset.sum_sub_distrib, smul_sub] using haux
  have hsigned_le_signedD :
      (∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν) ≤
        ∫ z : (Ω × Ω) × Ω',
          ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
            ∂(μ.prod μ).prod ν := by
    have houter := integral_mono
      hsignedInt.norm.integral_prod_right
      hsignedDInt.norm.integral_prod_right
      hslice_signed_le_signedD
    calc
      (∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν) =
          ∫ η, ∫ ω, ‖∑ i, ε i η • X i ω‖ ∂μ ∂ν :=
        integral_prod_symm _ hsignedInt.norm
      _ ≤ ∫ η, ∫ z : Ω × Ω,
          ‖∑ i, ε i η • (X i z.1 - X i z.2)‖ ∂μ.prod μ ∂ν := houter
      _ = ∫ z : (Ω × Ω) × Ω',
          ‖∑ i, ε i z.2 • (X i z.1.1 - X i z.1.2)‖
            ∂(μ.prod μ).prod ν :=
        (integral_prod_symm _ hsignedDInt.norm).symm
  constructor
  · have hsigned_le_two_sum :
        (∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν) ≤
          2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ :=
      hsigned_le_signedD.trans <| hsignedD_eq_D.le.trans hD_le_two_sum
    linarith
  · exact hsum_le_D.trans <| hsignedD_eq_D.symm.le.trans hsignedD_le_two_signed

/-- Upper-bound projection of the corresponding lemma, convenient for later chapters.

**Book Lemma 6.3.2.** -/
theorem symmetrization_upper
    {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν) :
    (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
      2 * ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν :=
  (symmetrization hXm hXint hX0 hXind hεm hε hεind).2

/-- Uncentered-input form of the symmetrization upper bound. This is the form used in
matrix-completion arguments: the left side centers each vector, whereas the Rademacher sum on
the right uses the original vectors.

**Book Lemma 6.3.2.** -/
theorem symmetrization_centered_sum_upper
    {ι Ω Ω' E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {ε : ι → Ω' → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν) :
    (∫ ω, ‖∑ i, (X i ω - ∫ u, X i u ∂μ)‖ ∂μ) ≤
      2 * ∫ z : Ω × Ω', ‖∑ i, ε i z.2 • X i z.1‖ ∂μ.prod ν := by
  have htermInt (i : ι) :
      Integrable (fun ω => X i ω - ∫ u, X i u ∂μ) μ :=
    (hXint i).sub (integrable_const _)
  have hcenterInt : Integrable
      (fun ω => ∑ i, (X i ω - ∫ u, X i u ∂μ)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => htermInt i)
  have hterm0 (i : ι) :
      ∫ ω, (X i ω - ∫ u, X i u ∂μ) ∂μ = 0 := by
    rw [integral_sub (hXint i) (integrable_const _), integral_const]
    simp
  have hcenter0 :
      ∫ ω, ∑ i, (X i ω - ∫ u, X i u ∂μ) ∂μ = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => htermInt i)]
    simp [hterm0]
  have hnegCenter0 :
      ∫ ω, -(∑ i, (X i ω - ∫ u, X i u ∂μ)) ∂μ = 0 := by
    calc
      ∫ ω, -(∑ i, (X i ω - ∫ u, X i u ∂μ)) ∂μ =
          -(∫ ω, ∑ i, (X i ω - ∫ u, X i u ∂μ) ∂μ) :=
        integral_neg (fun ω => ∑ i, (X i ω - ∫ u, X i u ∂μ))
      _ = 0 := by rw [hcenter0]; simp
  have hcenter_le_Daux :=
    integral_norm_le_integral_norm_add_independent_centered
      (Y := fun ω => ∑ i, (X i ω - ∫ u, X i u ∂μ))
      (Z := fun ω => -(∑ i, (X i ω - ∫ u, X i u ∂μ)))
      hcenterInt hcenterInt.neg hnegCenter0
  have hcenter_le_D :
      (∫ ω, ‖∑ i, (X i ω - ∫ u, X i u ∂μ)‖ ∂μ) ≤
        ∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ := by
    calc
      (∫ ω, ‖∑ i, (X i ω - ∫ u, X i u ∂μ)‖ ∂μ) ≤
          ∫ z : Ω × Ω,
            ‖(∑ i, (X i z.1 - ∫ u, X i u ∂μ)) +
              -(∑ i, (X i z.2 - ∫ u, X i u ∂μ))‖ ∂μ.prod μ :=
        hcenter_le_Daux
      _ = ∫ z : Ω × Ω, ‖∑ i, (X i z.1 - X i z.2)‖ ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        apply congrArg norm
        simp only [Finset.sum_sub_distrib]
        abel
  have hsignedD_eq_D := integral_norm_signed_independentCopy_sub_eq
    hXm hεm hXind hεind hε
  have hsignedD_le := integral_norm_signed_independentCopy_sub_le_two hXint hε
  exact hcenter_le_D.trans <| hsignedD_eq_D.symm.le.trans hsignedD_le

end

end HDP.Chapter6

end Source_08_Symmetrization

/-! ## Material formerly in `09_SymmetricRandomMatrices.lean` -/

section Source_09_SymmetricRandomMatrices

/-!
# Chapter 6, §6.4: symmetric random matrices

The source proof decomposes a symmetric matrix into one summand for every
unordered matrix coordinate.  A non-loop summand has two transposed nonzero
entries and is therefore not diagonal; the corrected assertion used below is
that its square is diagonal.  This is the source typo in the proof of
Theorem 6.4.1.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval Matrix.Norms.L2Operator
  RealInnerProductSpace

namespace HDP.Chapter6

noncomputable section

variable {n : ℕ}

/-- One symmetric `0/1` coordinate matrix. Loops have one nonzero entry and non-loops have the
two transposed entries.

**Lean implementation helper.** -/
def symmetricCoordinateMatrix (e : Sym2 (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if s(i, j) = e then 1 else 0

/-- The symmetric coordinate matrix of an unordered pair has entry one exactly at that pair of
indices and zero elsewhere.

**Lean implementation helper.** -/
@[simp] lemma symmetricCoordinateMatrix_apply (e : Sym2 (Fin n))
    (i j : Fin n) :
    symmetricCoordinateMatrix e i j = if s(i, j) = e then 1 else 0 := rfl

/-- Shows that symmetric coordinate matrix is symmetric.

**Lean implementation helper.** -/
lemma symmetricCoordinateMatrix_isSymm (e : Sym2 (Fin n)) :
    (symmetricCoordinateMatrix e).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [symmetricCoordinateMatrix, Sym2.eq_swap]

/-- The unordered coordinates incident to a fixed row.

**Lean implementation helper.** -/
def symmetricIncidentCoordinates (i : Fin n) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun j => s(i, j))

/-- Shows that symmetric incident coordinate map is injective.

**Lean implementation helper.** -/
private lemma symmetricIncidentCoordinateMap_injective (i : Fin n) :
    Function.Injective (fun j : Fin n => s(i, j)) := by
  intro a b h
  rcases Sym2.eq_iff.mp h with h | h
  · exact h.2
  · exact h.2.trans h.1

/-- Computes the cardinality of symmetric incident coordinates.

**Lean implementation helper.** -/
@[simp] lemma card_symmetricIncidentCoordinates (i : Fin n) :
    (symmetricIncidentCoordinates i).card = n := by
  classical
  rw [symmetricIncidentCoordinates,
    Finset.card_image_of_injective _ (symmetricIncidentCoordinateMap_injective i)]
  simp

/-- Squaring the symmetric coordinate matrix supported on `{a,b}` gives the diagonal projector onto those two coordinates.

**Lean implementation helper.** -/
private lemma symmetricCoordinateMatrix_sq_mk (a b i j : Fin n) :
    (symmetricCoordinateMatrix s(a, b) * symmetricCoordinateMatrix s(a, b)) i j =
      if i = j ∧ (i = a ∨ i = b) then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, symmetricCoordinateMatrix_apply]
  simp only [Sym2.eq_iff, ite_mul, one_mul, zero_mul]
  by_cases hij : i = j
  · subst j
    by_cases hia : i = a
    · subst a
      rw [Finset.sum_eq_single b]
      all_goals simp_all [eq_comm]
      all_goals aesop
    · by_cases hib : i = b
      · subst b
        rw [Finset.sum_eq_single a] <;> simp_all [eq_comm]
      · simp [hia, hib]
  · by_cases hia : i = a
    · subst a
      rw [Finset.sum_eq_single b]
      all_goals simp_all [eq_comm]
      all_goals aesop
    · by_cases hib : i = b
      · subst b
        rw [Finset.sum_eq_single a] <;> simp_all [eq_comm]
      · simp [hia, hib, hij]

/-- Algebraic assertion in the proof of the corresponding theorem: the square of a coordinate
summand is diagonal. The summand itself is not diagonal for a non-loop coordinate.

**Book Chapter 6, p.190, random-matrix proof.** -/
lemma symmetricCoordinateMatrix_sq_apply (e : Sym2 (Fin n)) (i j : Fin n) :
    (symmetricCoordinateMatrix e * symmetricCoordinateMatrix e) i j =
      if i = j ∧ e ∈ symmetricIncidentCoordinates i then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [symmetricCoordinateMatrix_sq_mk]
      congr 2
      simp [symmetricIncidentCoordinates, eq_comm]
      all_goals aesop

/-- A symmetric matrix assembled from its independent upper-triangular coordinates, indexed
without an arbitrary ordering by `Sym2`.

**Lean implementation helper.** -/
def symmetricMatrixOfCoordinates {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (ω : Ω) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => a s(i, j) ω

/-- Shows that symmetric matrix of coordinates is symmetric.

**Lean implementation helper.** -/
lemma symmetricMatrixOfCoordinates_isSymm {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (ω : Ω) :
    (symmetricMatrixOfCoordinates a ω).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [symmetricMatrixOfCoordinates, Sym2.eq_swap]

/-- The matrix summand belonging to one unordered scalar coordinate.

**Lean implementation helper.** -/
def symmetricCoordinateSummand {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (e : Sym2 (Fin n)) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  a e ω • symmetricCoordinateMatrix e

/-- Shows that symmetric coordinate summand is Hermitian.

**Lean implementation helper.** -/
lemma symmetricCoordinateSummand_isHermitian {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (e : Sym2 (Fin n)) (ω : Ω) :
    (symmetricCoordinateSummand a e ω).IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr
    ((symmetricCoordinateMatrix_isSymm e).smul (a e ω))

/-- Shows that symmetric coordinate summand is measurable.

**Lean implementation helper.** -/
lemma symmetricCoordinateSummand_measurable {Ω : Type*} [MeasurableSpace Ω]
    {a : Sym2 (Fin n) → Ω → ℝ} (ha : ∀ e, Measurable (a e))
    (e : Sym2 (Fin n)) :
    Measurable (symmetricCoordinateSummand a e) := by
  exact (ha e).smul_const (symmetricCoordinateMatrix e)

/-- Shows that symmetric coordinate summand is integrable.

**Lean implementation helper.** -/
lemma symmetricCoordinateSummand_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a : Sym2 (Fin n) → Ω → ℝ}
    (ha : ∀ e, Integrable (a e) μ) (e : Sym2 (Fin n)) :
    Integrable (symmetricCoordinateSummand a e) μ := by
  exact (ha e).smul_const (symmetricCoordinateMatrix e)

/-- Shows that symmetric coordinate summand is centered.

**Lean implementation helper.** -/
lemma symmetricCoordinateSummand_centered {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a : Sym2 (Fin n) → Ω → ℝ}
    (ha : ∀ e, ∫ ω, a e ω ∂μ = 0) (e : Sym2 (Fin n)) :
    ∫ ω, symmetricCoordinateSummand a e ω ∂μ = 0 := by
  change (∫ ω, a e ω • symmetricCoordinateMatrix e ∂μ) = 0
  rw [integral_smul_const, ha e, zero_smul]

/-- Shows that symmetric coordinate summand is independent.

**Lean implementation helper.** -/
lemma symmetricCoordinateSummand_independent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a : Sym2 (Fin n) → Ω → ℝ}
    (ha : iIndepFun a μ) :
    iIndepFun (symmetricCoordinateSummand a) μ := by
  exact ha.comp
    (fun e x => x • symmetricCoordinateMatrix e) (fun _ => by fun_prop)

/-- The coordinate summands reconstruct the original symmetric matrix.

**Lean implementation helper.** -/
lemma sum_symmetricCoordinateSummand {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (ω : Ω) :
    ∑ e, symmetricCoordinateSummand a e ω = symmetricMatrixOfCoordinates a ω := by
  classical
  ext i j
  simp only [symmetricCoordinateSummand, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, symmetricCoordinateMatrix_apply, symmetricMatrixOfCoordinates]
  rw [Finset.sum_eq_single s(i, j)]
  · simp
  · intro e _ he
    rw [if_neg (fun h => he h.symm)]
    ring
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Squaring and summing all coordinate summands gives the diagonal matrix of the squared
Euclidean row lengths.

**Lean implementation helper.** -/
lemma sum_symmetricCoordinateSummand_sq {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (ω : Ω) :
    (∑ e, (symmetricCoordinateSummand a e ω) ^ 2) =
      Matrix.diagonal (fun i => ∑ j, (symmetricMatrixOfCoordinates a ω i j) ^ 2) := by
  classical
  ext i j
  simp only [Matrix.sum_apply, symmetricCoordinateSummand, pow_two]
  simp_rw [smul_mul_smul_comm]
  simp only [Matrix.smul_apply, smul_eq_mul, symmetricCoordinateMatrix_sq_apply,
    Matrix.diagonal_apply, symmetricMatrixOfCoordinates]
  by_cases hij : i = j
  · subst j
    simp only [true_and, if_true]
    rw [show (∑ e : Sym2 (Fin n),
        a e ω * a e ω * if e ∈ symmetricIncidentCoordinates i then 1 else 0) =
        (∑ e ∈ symmetricIncidentCoordinates i, (a e ω) ^ 2) by
      simp [pow_two]]
    rw [symmetricIncidentCoordinates, Finset.sum_image]
    · simp [pow_two]
    · intro x _ y _ hxy
      exact symmetricIncidentCoordinateMap_injective i hxy
  · simp [hij]

/-- Identifies pi norm row energy with max row l2 norm squared.

**Lean implementation helper.** -/
private lemma piNorm_rowEnergy_eq_maxRowL2Norm_sq [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖(fun i => ∑ j, A i j ^ 2)‖ =
      (HDP.Chapter4.maxRowL2Norm A) ^ 2 := by
  let d : Fin n → ℝ := fun i => ∑ j, A i j ^ 2
  have hd0 (i : Fin n) : 0 ≤ d i := by
    dsimp [d]
    positivity
  have hrow (i : Fin n) :
      d i = ‖(WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    dsimp [d]
    exact (EuclideanSpace.real_norm_sq_eq
      (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))).symm
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg
      (sq_nonneg (HDP.Chapter4.maxRowL2Norm A))).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hd0 i), hrow]
    have hle := HDP.Chapter4.row_norm_le_maxRowL2Norm A i
    nlinarith [norm_nonneg
      (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n)),
      HDP.Chapter4.maxRowL2Norm_nonneg A]
  · obtain ⟨i, hi⟩ := HDP.Chapter4.exists_row_eq_maxRowL2Norm A
    have heval : |d i| ≤ ‖d‖ :=
      (pi_norm_le_iff_of_nonneg (x := d) (norm_nonneg d)).1 le_rfl i
    rw [abs_of_nonneg (hd0 i), hrow, hi] at heval
    exact heval

/-- The conditional matrix-Khintchine variance is exactly the square of the largest row norm.

**Lean implementation helper.** -/
lemma symmetricCoordinateVarianceNorm [Nonempty (Fin n)] {Ω : Type*}
    (a : Sym2 (Fin n) → Ω → ℝ) (ω : Ω) :
    ‖∑ e, (symmetricCoordinateSummand a e ω) ^ 2‖ =
      (HDP.Chapter4.maxRowL2Norm (symmetricMatrixOfCoordinates a ω)) ^ 2 := by
  rw [sum_symmetricCoordinateSummand_sq]
  change HDP.matrixOpNorm (Matrix.diagonal (fun i => ∑ j,
    symmetricMatrixOfCoordinates a ω i j ^ 2)) = _
  rw [HDP.Chapter4.exercise_4_3b_diagonal,
    piNorm_rowEnergy_eq_maxRowL2Norm_sq]

/-- Derives matrix concentration is rademacher from is rademacher.

**Lean implementation helper.** -/
private lemma matrixConcentration_isRademacher_of_isRademacher
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : Ω → ℝ}
    (hε : HDP.IsRademacher ε μ) :
    MatrixConcentration.IsRademacher ε μ := by
  rw [MatrixConcentration.IsRademacher, hε.map_eq,
    ProbabilityTheory.bernoulliMeasure_def,
    MatrixConcentration.rademacherMeasure]
  have hp :
      unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ =
        (2 : ℝ≥0)⁻¹ := by
    ext
    change (1 / 2 : ℝ) = (2 : ℝ)⁻¹
    norm_num
  have hm :
      unitInterval.toNNReal
          (unitInterval.symm ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) =
        (2 : ℝ≥0)⁻¹ := by
    ext
    simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    norm_num
  rw [hp, hm]
  have hsmul (x : ℝ) :
      (2 : ℝ≥0)⁻¹ • Measure.dirac x =
        (2 : ℝ≥0∞)⁻¹ • Measure.dirac x := by
    rw [← Measure.coe_nnreal_smul]
    simp
  rw [hsmul, hsmul]

/-- Conditional matrix Khintchine for the coordinate decomposition. After conditioning on the
entries, its variance is exactly the squared largest row norm.

**Book (6.15).** -/
theorem conditionalKhintchine_symmetricCoordinates [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ωε] {ν : Measure Ωε}
    [IsProbabilityMeasure ν]
    (a : Sym2 (Fin n) → Ω → ℝ) (ω : Ω)
    {ε : Sym2 (Fin n) → Ωε → ℝ}
    (hεm : ∀ e, Measurable (ε e))
    (hε : ∀ e, HDP.IsRademacher (ε e) ν)
    (hεind : iIndepFun ε ν) :
    (∫ η, ‖∑ e, ε e η • symmetricCoordinateSummand a e ω‖ ∂ν) ≤
      Real.sqrt (2 * Real.log (2 * n)) *
        HDP.Chapter4.maxRowL2Norm (symmetricMatrixOfCoordinates a ω) := by
  let R : ℝ := HDP.Chapter4.maxRowL2Norm (symmetricMatrixOfCoordinates a ω)
  have hR : 0 ≤ R := HDP.Chapter4.maxRowL2Norm_nonneg _
  have h := HDP.Chapter5.matrixKhintchineOne
    (μ := ν) (fun e => symmetricCoordinateSummand a e ω)
    (fun e => symmetricCoordinateSummand_isHermitian a e ω)
    hεm (fun e => matrixConcentration_isRademacher_of_isRademacher (hε e)) hεind
  rw [symmetricCoordinateVarianceNorm] at h
  have h' :
      (∫ η, ‖∑ e, ε e η • symmetricCoordinateSummand a e ω‖ ∂ν) ≤
        Real.sqrt (2 * R ^ 2 * Real.log (2 * n)) := by
    simpa only [R, Fintype.card_fin] using h
  calc
    (∫ η, ‖∑ e, ε e η • symmetricCoordinateSummand a e ω‖ ∂ν) ≤
        Real.sqrt (2 * R ^ 2 * Real.log (2 * n)) := h'
    _ = Real.sqrt (2 * Real.log (2 * n)) * R := by
      rw [show 2 * R ^ 2 * Real.log (2 * n) =
          R ^ 2 * (2 * Real.log (2 * n)) by ring,
        Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hR, mul_comm]

/-- The deterministic lower half of the corresponding theorem: every row norm is bounded by the
Euclidean operator norm.

**Lean implementation helper.** -/
lemma maxRowL2Norm_le_symmetricOperatorNorm [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HDP.Chapter4.maxRowL2Norm A ≤ HDP.matrixOpNorm A := by
  obtain ⟨i, hi⟩ := HDP.Chapter4.exists_row_eq_maxRowL2Norm A
  rw [← hi]
  exact HDP.Chapter4.exercise_4_7c_row_le A i

/-- The expectation lower bound in the corresponding theorem.

**Lean implementation helper.** -/
theorem expectedMaxRowL2Norm_le_expectedOperatorNorm [Nonempty (Fin n)]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hrow : Integrable (fun ω => HDP.Chapter4.maxRowL2Norm (A ω)) μ)
    (hop : Integrable (fun ω => HDP.matrixOpNorm (A ω)) μ) :
    (∫ ω, HDP.Chapter4.maxRowL2Norm (A ω) ∂μ) ≤
      ∫ ω, HDP.matrixOpNorm (A ω) ∂μ := by
  exact integral_mono hrow hop fun ω => maxRowL2Norm_le_symmetricOperatorNorm (A ω)

/-- Establishes integrability of signed symmetric coordinate sum.

**Lean implementation helper.** -/
private lemma integrable_signed_symmetricCoordinateSum
    [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωε]
    {μ : Measure Ω} {ν : Measure Ωε}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : Sym2 (Fin n) → Ω → ℝ} (ha : ∀ e, Integrable (a e) μ)
    {ε : Sym2 (Fin n) → Ωε → ℝ}
    (hε : ∀ e, HDP.IsRademacher (ε e) ν) :
    Integrable (fun z : Ω × Ωε =>
      ∑ e, ε e z.2 • symmetricCoordinateSummand a e z.1) (μ.prod ν) := by
  apply integrable_finsetSum Finset.univ
  intro e _
  have hεint : Integrable (ε e) ν :=
    ((hε e).memLp 1).integrable le_rfl
  have hcoef : Integrable (fun z : Ω × Ωε => a e z.1 * ε e z.2)
      (μ.prod ν) :=
    (ha e).mul_prod hεint
  have hterm := hcoef.smul_const (symmetricCoordinateMatrix e)
  simpa only [symmetricCoordinateSummand, smul_smul, mul_comm] using hterm

/-- The analytic part of the corresponding theorem after the symmetrization inequality has been
supplied. This separate lemma makes the conditional-Khintchine/Fubini step reusable and keeps
the general symmetrization proof in §6.3.

**Book (6.14).** -/
theorem symmetricRandomMatrix_expectedNorm_upper_of_symmetrization
    [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωε]
    {μ : Measure Ω} {ν : Measure Ωε}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : Sym2 (Fin n) → Ω → ℝ)
    (ha : ∀ e, Integrable (a e) μ)
    (hrow : Integrable (fun ω =>
      HDP.Chapter4.maxRowL2Norm (symmetricMatrixOfCoordinates a ω)) μ)
    {ε : Sym2 (Fin n) → Ωε → ℝ}
    (hεm : ∀ e, Measurable (ε e))
    (hε : ∀ e, HDP.IsRademacher (ε e) ν)
    (hεind : iIndepFun ε ν)
    (hsymm :
      (∫ ω, ‖∑ e, symmetricCoordinateSummand a e ω‖ ∂μ) ≤
        2 * ∫ z : Ω × Ωε,
          ‖∑ e, ε e z.2 • symmetricCoordinateSummand a e z.1‖ ∂μ.prod ν) :
    (∫ ω, HDP.matrixOpNorm (symmetricMatrixOfCoordinates a ω) ∂μ) ≤
      2 * Real.sqrt (2 * Real.log (2 * n)) *
        ∫ ω, HDP.Chapter4.maxRowL2Norm
          (symmetricMatrixOfCoordinates a ω) ∂μ := by
  let c : ℝ := Real.sqrt (2 * Real.log (2 * n))
  have hsigned : Integrable (fun z : Ω × Ωε =>
      ∑ e, ε e z.2 • symmetricCoordinateSummand a e z.1) (μ.prod ν) :=
    integrable_signed_symmetricCoordinateSum ha hε
  have hsignedNorm : Integrable (fun z : Ω × Ωε =>
      ‖∑ e, ε e z.2 • symmetricCoordinateSummand a e z.1‖) (μ.prod ν) :=
    hsigned.norm
  have hinner : Integrable (fun ω =>
      ∫ η, ‖∑ e, ε e η • symmetricCoordinateSummand a e ω‖ ∂ν) μ :=
    hsignedNorm.integral_prod_left
  have hpoint (ω : Ω) :
      (∫ η, ‖∑ e, ε e η • symmetricCoordinateSummand a e ω‖ ∂ν) ≤
        c * HDP.Chapter4.maxRowL2Norm
          (symmetricMatrixOfCoordinates a ω) := by
    exact conditionalKhintchine_symmetricCoordinates a ω hεm hε hεind
  have hiterated :
      (∫ z : Ω × Ωε,
          ‖∑ e, ε e z.2 • symmetricCoordinateSummand a e z.1‖ ∂μ.prod ν) ≤
        c * ∫ ω, HDP.Chapter4.maxRowL2Norm
          (symmetricMatrixOfCoordinates a ω) ∂μ := by
    rw [integral_prod _ hsignedNorm]
    calc
      (∫ ω, ∫ η,
          ‖∑ e, ε e η • symmetricCoordinateSummand a e ω‖ ∂ν ∂μ) ≤
          ∫ ω, c * HDP.Chapter4.maxRowL2Norm
            (symmetricMatrixOfCoordinates a ω) ∂μ := by
        apply integral_mono hinner (hrow.const_mul c)
        exact hpoint
      _ = c * ∫ ω, HDP.Chapter4.maxRowL2Norm
          (symmetricMatrixOfCoordinates a ω) ∂μ := by
        rw [integral_const_mul]
  have hsumFun :
      (fun ω => ‖∑ e, symmetricCoordinateSummand a e ω‖) =
        (fun ω => HDP.matrixOpNorm (symmetricMatrixOfCoordinates a ω)) := by
    funext ω
    rw [sum_symmetricCoordinateSummand]
    rfl
  rw [hsumFun] at hsymm
  calc
    (∫ ω, HDP.matrixOpNorm (symmetricMatrixOfCoordinates a ω) ∂μ) ≤
        2 * ∫ z : Ω × Ωε,
          ‖∑ e, ε e z.2 • symmetricCoordinateSummand a e z.1‖ ∂μ.prod ν := hsymm
    _ ≤ 2 * (c * ∫ ω, HDP.Chapter4.maxRowL2Norm
          (symmetricMatrixOfCoordinates a ω) ∂μ) :=
      mul_le_mul_of_nonneg_left hiterated (by norm_num)
    _ = 2 * Real.sqrt (2 * Real.log (2 * n)) *
        ∫ ω, HDP.Chapter4.maxRowL2Norm
          (symmetricMatrixOfCoordinates a ω) ∂μ := by
      dsimp [c]
      ring

/-- A symmetric matrix whose unordered entries are independent, centered, and integrable has
expected operator norm between its expected largest row norm and an explicit logarithmic
multiple of that quantity. The source writes `sqrt (log n)`, which degenerates at `n = 1`. This
declaration uses the uniform correction `sqrt (log (2n))`; its explicit absolute factor is `2 *
sqrt 2` after separating the logarithm.

**Book Theorem 6.4.1.** -/
theorem theorem_6_4_1 [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωε]
    {μ : Measure Ω} {ν : Measure Ωε}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : Sym2 (Fin n) → Ω → ℝ)
    (ham : ∀ e, Measurable (a e))
    (ha : ∀ e, Integrable (a e) μ)
    (ha0 : ∀ e, ∫ ω, a e ω ∂μ = 0)
    (haind : iIndepFun a μ)
    (hrow : Integrable (fun ω =>
      HDP.Chapter4.maxRowL2Norm (symmetricMatrixOfCoordinates a ω)) μ)
    {ε : Sym2 (Fin n) → Ωε → ℝ}
    (hεm : ∀ e, Measurable (ε e))
    (hε : ∀ e, HDP.IsRademacher (ε e) ν)
    (hεind : iIndepFun ε ν) :
    (∫ ω, HDP.Chapter4.maxRowL2Norm
        (symmetricMatrixOfCoordinates a ω) ∂μ) ≤
        ∫ ω, HDP.matrixOpNorm (symmetricMatrixOfCoordinates a ω) ∂μ ∧
      (∫ ω, HDP.matrixOpNorm (symmetricMatrixOfCoordinates a ω) ∂μ) ≤
        2 * Real.sqrt (2 * Real.log (2 * n)) *
          ∫ ω, HDP.Chapter4.maxRowL2Norm
            (symmetricMatrixOfCoordinates a ω) ∂μ := by
  have hsumInt : Integrable
      (fun ω => ∑ e, symmetricCoordinateSummand a e ω) μ :=
    integrable_finsetSum Finset.univ fun e _ =>
      symmetricCoordinateSummand_integrable ha e
  have hsumFun :
      (fun ω => ∑ e, symmetricCoordinateSummand a e ω) =
        symmetricMatrixOfCoordinates a := by
    funext ω
    exact sum_symmetricCoordinateSummand a ω
  rw [hsumFun] at hsumInt
  have hop : Integrable (fun ω =>
      HDP.matrixOpNorm (symmetricMatrixOfCoordinates a ω)) μ := by
    change Integrable (fun ω => ‖symmetricMatrixOfCoordinates a ω‖) μ
    exact hsumInt.norm
  have hsymm := symmetrization_upper
    (X := symmetricCoordinateSummand a) (ε := ε)
    (symmetricCoordinateSummand_measurable ham)
    (symmetricCoordinateSummand_integrable ha)
    (symmetricCoordinateSummand_centered ha0)
    (symmetricCoordinateSummand_independent haind)
    hεm hε hεind
  exact ⟨expectedMaxRowL2Norm_le_expectedOperatorNorm
      (symmetricMatrixOfCoordinates a) hrow hop,
    symmetricRandomMatrix_expectedNorm_upper_of_symmetrization
      a ha hrow hεm hε hεind hsymm⟩

/-! ## Corrected Exercise 6.28: rectangular matrices -/

/-- A rectangular matrix assembled from independent scalar entries.

**Lean implementation helper.** -/
def rectangularMatrixOfCoordinates {m n : ℕ} {Ω : Type*}
    (a : Fin m × Fin n → Ω → ℝ) (ω : Ω) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => a (i, j) ω

/-- The deterministic matrix unit belonging to one rectangular coordinate.

**Lean implementation helper.** -/
def rectangularCoordinateMatrix {m n : ℕ} (ij : Fin m × Fin n) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.single ij.1 ij.2 1

/-- One scalar-entry summand in the rectangular decomposition.

**Lean implementation helper.** -/
def rectangularCoordinateSummand {m n : ℕ} {Ω : Type*}
    (a : Fin m × Fin n → Ω → ℝ) (ij : Fin m × Fin n) (ω : Ω) :
    Matrix (Fin m) (Fin n) ℝ :=
  a ij ω • rectangularCoordinateMatrix ij

/-- The rectangular coordinate summands reconstruct the matrix.

**Lean implementation helper.** -/
lemma sum_rectangularCoordinateSummand {m n : ℕ} {Ω : Type*}
    (a : Fin m × Fin n → Ω → ℝ) (ω : Ω) :
    ∑ ij, rectangularCoordinateSummand a ij ω =
      rectangularMatrixOfCoordinates a ω := by
  classical
  ext i j
  simp only [rectangularCoordinateSummand, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, rectangularCoordinateMatrix, Matrix.single_apply,
    rectangularMatrixOfCoordinates]
  rw [Finset.sum_eq_single (i, j)]
  · simp
  · rintro ⟨r, s⟩ _ hrs
    by_cases hri : r = i
    · subst r
      have hsj : s ≠ j := fun h => hrs (by simp [h])
      simp [hsj]
    · simp [hri]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Multiplying a rectangular coordinate matrix by its transpose yields the diagonal projector
onto its selected row.

**Lean implementation helper.** -/
private lemma rectangularCoordinateMatrix_mul_transpose_apply
    {m n : ℕ} (ij : Fin m × Fin n) (r s : Fin m) :
    (rectangularCoordinateMatrix ij * (rectangularCoordinateMatrix ij)ᵀ) r s =
      if r = ij.1 ∧ s = ij.1 then 1 else 0 := by
  classical
  rcases ij with ⟨i, j⟩
  simp only [rectangularCoordinateMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.single_apply]
  by_cases hrs : r = i ∧ s = i
  · rcases hrs with ⟨rfl, rfl⟩
    rw [Finset.sum_eq_single j]
    all_goals simp [eq_comm]
  · by_cases hri : r = i
    · subst r
      have hsi : s ≠ i := fun hs => hrs ⟨rfl, hs⟩
      simp [hsi, eq_comm]
    · simp [hri, eq_comm]

/-- Multiplying the transpose of a rectangular coordinate matrix by the matrix yields the
diagonal projector onto its selected column.

**Lean implementation helper.** -/
private lemma rectangularCoordinateMatrix_transpose_mul_apply
    {m n : ℕ} (ij : Fin m × Fin n) (r s : Fin n) :
    ((rectangularCoordinateMatrix ij)ᵀ * rectangularCoordinateMatrix ij) r s =
      if r = ij.2 ∧ s = ij.2 then 1 else 0 := by
  classical
  rcases ij with ⟨i, j⟩
  simp only [rectangularCoordinateMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.single_apply]
  by_cases hrs : r = j ∧ s = j
  · rcases hrs with ⟨rfl, rfl⟩
    rw [Finset.sum_eq_single i]
    all_goals simp [eq_comm]
  · by_cases hrj : r = j
    · subst r
      have hsj : s ≠ j := fun hs => hrs ⟨rfl, hs⟩
      simp [hsj, eq_comm]
    · simp [hrj, eq_comm]

/-- The left variance matrix of rectangular coordinate summands is diagonal, with entries equal to rowwise sums of squares.

**Lean implementation helper.** -/
private lemma sum_rectangularCoordinateSummand_mul_transpose
    {m n : ℕ} {Ω : Type*} (a : Fin m × Fin n → Ω → ℝ) (ω : Ω) :
    HDP.Chapter5.rademacherVarianceLeft
        (fun ij => rectangularCoordinateSummand a ij ω) =
      Matrix.diagonal (fun i => ∑ j, (rectangularMatrixOfCoordinates a ω i j) ^ 2) := by
  classical
  ext r s
  simp only [HDP.Chapter5.rademacherVarianceLeft, Matrix.sum_apply,
    rectangularCoordinateSummand, Matrix.transpose_smul]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul,
    rectangularCoordinateMatrix_mul_transpose_apply,
    Matrix.diagonal_apply, rectangularMatrixOfCoordinates]
  rw [Fintype.sum_prod_type]
  by_cases hrs : r = s
  · subst s
    simp [pow_two]
  · rw [if_neg hrs]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by
      intro h
      exact hrs (h.1.trans h.2.symm))]
    ring

/-- The right variance matrix of rectangular coordinate summands is diagonal, with entries equal to columnwise sums of squares.

**Lean implementation helper.** -/
private lemma sum_rectangularCoordinateSummand_transpose_mul
    {m n : ℕ} {Ω : Type*} (a : Fin m × Fin n → Ω → ℝ) (ω : Ω) :
    HDP.Chapter5.rademacherVarianceRight
        (fun ij => rectangularCoordinateSummand a ij ω) =
      Matrix.diagonal (fun j => ∑ i, (rectangularMatrixOfCoordinates a ω i j) ^ 2) := by
  classical
  ext r s
  simp only [HDP.Chapter5.rademacherVarianceRight, Matrix.sum_apply,
    rectangularCoordinateSummand, Matrix.transpose_smul]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul,
    rectangularCoordinateMatrix_transpose_mul_apply,
    Matrix.diagonal_apply, rectangularMatrixOfCoordinates]
  rw [Fintype.sum_prod_type]
  by_cases hrs : r = s
  · subst s
    simp [pow_two]
  · rw [if_neg hrs]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by
      intro h
      exact hrs (h.1.trans h.2.symm))]
    ring

/-- Identifies pi norm rectangular row energy with max row l2 norm squared.

**Lean implementation helper.** -/
private lemma piNorm_rectangularRowEnergy_eq_maxRowL2Norm_sq
    {m n : ℕ} [Nonempty (Fin m)] (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(fun i => ∑ j, A i j ^ 2)‖ =
      (HDP.Chapter4.maxRowL2Norm A) ^ 2 := by
  let d : Fin m → ℝ := fun i => ∑ j, A i j ^ 2
  have hd0 (i : Fin m) : 0 ≤ d i := by
    dsimp [d]
    positivity
  have hrow (i : Fin m) :
      d i = ‖(WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    dsimp [d]
    exact (EuclideanSpace.real_norm_sq_eq
      (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n))).symm
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg
      (sq_nonneg (HDP.Chapter4.maxRowL2Norm A))).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hd0 i), hrow]
    have hle := HDP.Chapter4.row_norm_le_maxRowL2Norm A i
    nlinarith [norm_nonneg
      (WithLp.toLp 2 (A.row i) : EuclideanSpace ℝ (Fin n)),
      HDP.Chapter4.maxRowL2Norm_nonneg A]
  · obtain ⟨i, hi⟩ := HDP.Chapter4.exists_row_eq_maxRowL2Norm A
    have heval : |d i| ≤ ‖d‖ :=
      (pi_norm_le_iff_of_nonneg (x := d) (norm_nonneg d)).1 le_rfl i
    rw [abs_of_nonneg (hd0 i), hrow, hi] at heval
    exact heval

/-- The larger of the maximum rectangular row and column Euclidean norms. This is the corrected
right-hand random variable in the corresponding exercise.

**Lean implementation helper.** -/
noncomputable def rectangularRowColumnL2Norm {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  max (HDP.Chapter4.maxRowL2Norm A) (HDP.Chapter4.maxColumnL2Norm A)

/-- Shows that rectangular row column l2 norm is nonnegative.

**Lean implementation helper.** -/
lemma rectangularRowColumnL2Norm_nonneg {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ rectangularRowColumnL2Norm A :=
  (HDP.Chapter4.maxRowL2Norm_nonneg A).trans (le_max_left _ _)

/-- Identifies pi norm rectangular column energy with max column l2 norm squared.

**Lean implementation helper.** -/
private lemma piNorm_rectangularColumnEnergy_eq_maxColumnL2Norm_sq
    {m n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(fun j => ∑ i, A i j ^ 2)‖ =
      (HDP.Chapter4.maxColumnL2Norm A) ^ 2 := by
  have h := piNorm_rectangularRowEnergy_eq_maxRowL2Norm_sq Aᵀ
  simpa [HDP.Chapter4.maxColumnL2Norm, HDP.Chapter4.maxRowL2Norm,
    Matrix.transpose_apply, Matrix.col] using h

/-- The rectangular Rademacher variance of the entry decomposition is exactly the square of the
larger maximum row/column norm. The rectangular Khintchine theorem used below is itself proved
by Hermitian dilation in Chapter 5, implementing the hint to the corresponding exercise.

**Lean implementation helper.** -/
lemma rectangularCoordinateVariance {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    {Ω : Type*} (a : Fin m × Fin n → Ω → ℝ) (ω : Ω) :
    HDP.Chapter5.rademacherVariance
        (fun ij => rectangularCoordinateSummand a ij ω) =
      (rectangularRowColumnL2Norm (rectangularMatrixOfCoordinates a ω)) ^ 2 := by
  let A := rectangularMatrixOfCoordinates a ω
  let R := HDP.Chapter4.maxRowL2Norm A
  let C := HDP.Chapter4.maxColumnL2Norm A
  have hR : 0 ≤ R := HDP.Chapter4.maxRowL2Norm_nonneg A
  have hC : 0 ≤ C := HDP.Chapter4.maxColumnL2Norm_nonneg A
  rw [HDP.Chapter5.rademacherVariance,
    sum_rectangularCoordinateSummand_mul_transpose,
    sum_rectangularCoordinateSummand_transpose_mul]
  change max
      (HDP.matrixOpNorm (Matrix.diagonal (fun i => ∑ j, A i j ^ 2)))
      (HDP.matrixOpNorm (Matrix.diagonal (fun j => ∑ i, A i j ^ 2))) =
    (max R C) ^ 2
  rw [HDP.Chapter4.exercise_4_3b_diagonal,
    HDP.Chapter4.exercise_4_3b_diagonal,
    piNorm_rectangularRowEnergy_eq_maxRowL2Norm_sq,
    piNorm_rectangularColumnEnergy_eq_maxColumnL2Norm_sq]
  rcases le_total R C with hRC | hCR
  · rw [max_eq_right hRC, max_eq_right]
    exact (sq_le_sq₀ hR hC).2 hRC
  · rw [max_eq_left hCR, max_eq_left]
    exact (sq_le_sq₀ hC hR).2 hCR

/-- Shows that rectangular coordinate summand is measurable.

**Lean implementation helper.** -/
lemma rectangularCoordinateSummand_measurable
    {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {a : Fin m × Fin n → Ω → ℝ} (ha : ∀ ij, Measurable (a ij))
    (ij : Fin m × Fin n) :
    Measurable (rectangularCoordinateSummand a ij) := by
  exact (ha ij).smul_const (rectangularCoordinateMatrix ij)

/-- Shows that rectangular coordinate summand is integrable.

**Lean implementation helper.** -/
lemma rectangularCoordinateSummand_integrable
    {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Fin n → Ω → ℝ} (ha : ∀ ij, Integrable (a ij) μ)
    (ij : Fin m × Fin n) :
    Integrable (rectangularCoordinateSummand a ij) μ := by
  exact (ha ij).smul_const (rectangularCoordinateMatrix ij)

/-- Shows that rectangular coordinate summand is centered.

**Lean implementation helper.** -/
lemma rectangularCoordinateSummand_centered
    {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Fin n → Ω → ℝ} (ha : ∀ ij, ∫ ω, a ij ω ∂μ = 0)
    (ij : Fin m × Fin n) :
    ∫ ω, rectangularCoordinateSummand a ij ω ∂μ = 0 := by
  change (∫ ω, a ij ω • rectangularCoordinateMatrix ij ∂μ) = 0
  rw [integral_smul_const, ha ij, zero_smul]

/-- Shows that rectangular coordinate summand is independent.

**Lean implementation helper.** -/
lemma rectangularCoordinateSummand_independent
    {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Fin n → Ω → ℝ} (ha : iIndepFun a μ) :
    iIndepFun (rectangularCoordinateSummand a) μ := by
  exact ha.comp
    (fun ij x => x • rectangularCoordinateMatrix ij) (fun _ => by fun_prop)

/-- Conditional rectangular Khintchine, with the variance rewritten as the maximum row/column
norm. Chapter 5 proves the invoked rectangular theorem by Hermitian dilation.

**Lean implementation helper.** -/
theorem conditionalKhintchine_rectangularCoordinates
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ωε] {ν : Measure Ωε}
    [IsProbabilityMeasure ν]
    (a : Fin m × Fin n → Ω → ℝ) (ω : Ω)
    {ε : Fin m × Fin n → Ωε → ℝ}
    (hεm : ∀ ij, Measurable (ε ij))
    (hε : ∀ ij, HDP.IsRademacher (ε ij) ν)
    (hεind : iIndepFun ε ν) :
    (∫ η, ‖∑ ij, ε ij η • rectangularCoordinateSummand a ij ω‖ ∂ν) ≤
      Real.sqrt (2 * Real.log (m + n)) *
        rectangularRowColumnL2Norm (rectangularMatrixOfCoordinates a ω) := by
  let R : ℝ := rectangularRowColumnL2Norm (rectangularMatrixOfCoordinates a ω)
  have hR : 0 ≤ R := rectangularRowColumnL2Norm_nonneg _
  have h := HDP.Chapter5.rectangularRademacherExpectation
    (μ := ν) (fun ij => rectangularCoordinateSummand a ij ω)
    hεm (fun ij => matrixConcentration_isRademacher_of_isRademacher (hε ij)) hεind
  rw [rectangularCoordinateVariance] at h
  have h' :
      (∫ η, ‖∑ ij, ε ij η • rectangularCoordinateSummand a ij ω‖ ∂ν) ≤
        Real.sqrt (2 * R ^ 2 * Real.log (m + n)) := by
    simpa only [R, Fintype.card_fin] using h
  calc
    (∫ η, ‖∑ ij, ε ij η • rectangularCoordinateSummand a ij ω‖ ∂ν) ≤
        Real.sqrt (2 * R ^ 2 * Real.log (m + n)) := h'
    _ = Real.sqrt (2 * Real.log (m + n)) * R := by
      rw [show 2 * R ^ 2 * Real.log (m + n) =
          R ^ 2 * (2 * Real.log (m + n)) by ring,
        Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hR, mul_comm]

/-- Establishes integrability of signed rectangular coordinate sum.

**Lean implementation helper.** -/
private lemma integrable_signed_rectangularCoordinateSum
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωε]
    {μ : Measure Ω} {ν : Measure Ωε}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : Fin m × Fin n → Ω → ℝ} (ha : ∀ ij, Integrable (a ij) μ)
    {ε : Fin m × Fin n → Ωε → ℝ}
    (hε : ∀ ij, HDP.IsRademacher (ε ij) ν) :
    Integrable (fun z : Ω × Ωε =>
      ∑ ij, ε ij z.2 • rectangularCoordinateSummand a ij z.1) (μ.prod ν) := by
  apply integrable_finsetSum Finset.univ
  intro ij _
  have hεint : Integrable (ε ij) ν :=
    ((hε ij).memLp 1).integrable le_rfl
  have hcoef : Integrable (fun z : Ω × Ωε => a ij z.1 * ε ij z.2)
      (μ.prod ν) := (ha ij).mul_prod hεint
  have hterm := hcoef.smul_const (rectangularCoordinateMatrix ij)
  simpa only [rectangularCoordinateSummand, smul_smul, mul_comm] using hterm

/-- For a rectangular matrix with independent centered entries, the expected operator norm is
controlled by the expected larger maximum row/column norm. The printed exercise omitted the
expectation on its right-hand side; this declaration states the corrected quantity and uses the
safe `log (m+n)` normalization.

**Book Exercise 6.28.** -/
theorem exercise_6_28_rectangular_expectedNorm_upper
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωε]
    {μ : Measure Ω} {ν : Measure Ωε}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : Fin m × Fin n → Ω → ℝ)
    (ham : ∀ ij, Measurable (a ij))
    (ha : ∀ ij, Integrable (a ij) μ)
    (ha0 : ∀ ij, ∫ ω, a ij ω ∂μ = 0)
    (haind : iIndepFun a μ)
    (hrc : Integrable (fun ω =>
      rectangularRowColumnL2Norm (rectangularMatrixOfCoordinates a ω)) μ)
    {ε : Fin m × Fin n → Ωε → ℝ}
    (hεm : ∀ ij, Measurable (ε ij))
    (hε : ∀ ij, HDP.IsRademacher (ε ij) ν)
    (hεind : iIndepFun ε ν) :
    (∫ ω, HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω) ∂μ) ≤
      2 * Real.sqrt (2 * Real.log (m + n)) *
        ∫ ω, rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) ∂μ := by
  let c : ℝ := Real.sqrt (2 * Real.log (m + n))
  have hsymm := symmetrization_upper
    (X := rectangularCoordinateSummand a) (ε := ε)
    (rectangularCoordinateSummand_measurable ham)
    (rectangularCoordinateSummand_integrable ha)
    (rectangularCoordinateSummand_centered ha0)
    (rectangularCoordinateSummand_independent haind)
    hεm hε hεind
  have hsigned : Integrable (fun z : Ω × Ωε =>
      ∑ ij, ε ij z.2 • rectangularCoordinateSummand a ij z.1) (μ.prod ν) :=
    integrable_signed_rectangularCoordinateSum ha hε
  have hsignedNorm : Integrable (fun z : Ω × Ωε =>
      ‖∑ ij, ε ij z.2 • rectangularCoordinateSummand a ij z.1‖) (μ.prod ν) :=
    hsigned.norm
  have hinner : Integrable (fun ω =>
      ∫ η, ‖∑ ij, ε ij η • rectangularCoordinateSummand a ij ω‖ ∂ν) μ :=
    hsignedNorm.integral_prod_left
  have hpoint (ω : Ω) :
      (∫ η, ‖∑ ij, ε ij η • rectangularCoordinateSummand a ij ω‖ ∂ν) ≤
        c * rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) := by
    exact conditionalKhintchine_rectangularCoordinates a ω hεm hε hεind
  have hiterated :
      (∫ z : Ω × Ωε,
          ‖∑ ij, ε ij z.2 • rectangularCoordinateSummand a ij z.1‖ ∂μ.prod ν) ≤
        c * ∫ ω, rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) ∂μ := by
    rw [integral_prod _ hsignedNorm]
    calc
      (∫ ω, ∫ η,
          ‖∑ ij, ε ij η • rectangularCoordinateSummand a ij ω‖ ∂ν ∂μ) ≤
          ∫ ω, c * rectangularRowColumnL2Norm
            (rectangularMatrixOfCoordinates a ω) ∂μ := by
        apply integral_mono hinner (hrc.const_mul c)
        exact hpoint
      _ = c * ∫ ω, rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) ∂μ := by
        rw [integral_const_mul]
  have hsumFun :
      (fun ω => ‖∑ ij, rectangularCoordinateSummand a ij ω‖) =
        (fun ω => HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω)) := by
    funext ω
    rw [sum_rectangularCoordinateSummand]
    rfl
  rw [hsumFun] at hsymm
  calc
    (∫ ω, HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω) ∂μ) ≤
        2 * ∫ z : Ω × Ωε,
          ‖∑ ij, ε ij z.2 • rectangularCoordinateSummand a ij z.1‖ ∂μ.prod ν :=
      hsymm
    _ ≤ 2 * (c * ∫ ω, rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) ∂μ) :=
      mul_le_mul_of_nonneg_left hiterated (by norm_num)
    _ = 2 * Real.sqrt (2 * Real.log (m + n)) *
        ∫ ω, rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) ∂μ := by
      dsimp [c]
      ring

/-- Derives rectangular matrix operator norm integrable from coordinates symmetric matrix.

**Lean implementation helper.** -/
private lemma rectangularMatrixOpNorm_integrable_of_coordinates_symmetric_matrix
    {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Fin n → Ω → ℝ} (ha : ∀ ij, Integrable (a ij) μ) :
    Integrable (fun ω =>
      HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω)) μ := by
  have hsum : Integrable
      (fun ω => ∑ ij, rectangularCoordinateSummand a ij ω) μ :=
    integrable_finsetSum Finset.univ fun ij _ =>
      rectangularCoordinateSummand_integrable ha ij
  have hfun :
      (fun ω => ∑ ij, rectangularCoordinateSummand a ij ω) =
        rectangularMatrixOfCoordinates a := by
    funext ω
    exact sum_rectangularCoordinateSummand a ω
  rw [hfun] at hsum
  change Integrable (fun ω => ‖rectangularMatrixOfCoordinates a ω‖) μ
  exact hsum.norm

/-- Probability wrapper for the corrected exercise. It is the direct Markov
consequence of the expectation estimate, useful when a downstream argument needs an explicit
high-probability threshold rather than only a mean bound.

**Book Exercise 6.28.** -/
theorem exercise_6_28_rectangular_probability_upper
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {Ω Ωε : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωε]
    {μ : Measure Ω} {ν : Measure Ωε}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : Fin m × Fin n → Ω → ℝ)
    (ham : ∀ ij, Measurable (a ij))
    (ha : ∀ ij, Integrable (a ij) μ)
    (ha0 : ∀ ij, ∫ ω, a ij ω ∂μ = 0)
    (haind : iIndepFun a μ)
    (hrc : Integrable (fun ω =>
      rectangularRowColumnL2Norm (rectangularMatrixOfCoordinates a ω)) μ)
    {ε : Fin m × Fin n → Ωε → ℝ}
    (hεm : ∀ ij, Measurable (ε ij))
    (hε : ∀ ij, HDP.IsRademacher (ε ij) ν)
    (hεind : iIndepFun ε ν)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω)} ≤
      (2 * Real.sqrt (2 * Real.log (m + n)) *
        ∫ ω, rectangularRowColumnL2Norm
          (rectangularMatrixOfCoordinates a ω) ∂μ) / t := by
  have hop := rectangularMatrixOpNorm_integrable_of_coordinates_symmetric_matrix ha
  have hmarkov := HDP.markov_real
    (μ := μ)
    (X := fun ω => HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω))
    (Filter.Eventually.of_forall fun ω => HDP.matrixOpNorm_nonneg _)
    hop ht
  have hexp := exercise_6_28_rectangular_expectedNorm_upper
    a ham ha ha0 haind hrc hεm hε hεind
  exact hmarkov.trans (div_le_div_of_nonneg_right hexp ht.le)

end

end HDP.Chapter6

end Source_09_SymmetricRandomMatrices

/-! ## Material formerly in `10_RectangularRandomMatrices.lean` -/

section Source_10_RectangularRandomMatrices

/-!
# Chapter 6, §6.4: rectangular random matrices

This file records the rectangular row/column interface used in matrix
completion and proves the Bernoulli row-energy estimate delegated to Exercise
6.30.  The latter proof is the standard exponential-moment proof: Jensen and
the Bernoulli MGF bound control the maximum row count, after which the centered
row energy is bounded deterministically.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal unitInterval Matrix.Norms.L2Operator

namespace HDP.Chapter6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The pointwise ingredient for the lower half of the corrected exercise: every
row and every column Euclidean norm is bounded by the rectangular operator norm. The row/column
maximum is the authoritative definition from `09_SymmetricRandomMatrices`; this module does not
introduce a duplicate.

**Lean implementation helper.** -/
theorem rectangularRowColumnL2Norm_le_operatorNorm {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    rectangularRowColumnL2Norm A ≤ HDP.matrixOpNorm A := by
  rw [rectangularRowColumnL2Norm, max_le_iff]
  constructor
  · obtain ⟨i, hi⟩ := HDP.Chapter4.exists_row_eq_maxRowL2Norm A
    rw [← hi]
    exact HDP.Chapter4.exercise_4_7c_row_le A i
  · obtain ⟨j, hj⟩ := HDP.Chapter4.exists_column_eq_maxColumnL2Norm A
    rw [← hj]
    exact HDP.Chapter4.exercise_4_7a_column_le A j

/-- Bounds the expected maximum row-or-column Euclidean norm by the expected matrix operator
norm.

**Book Exercise 6.28.** -/
theorem exercise_6_28_rectangular_expectedNorm_lower {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hmax : Integrable (fun ω => rectangularRowColumnL2Norm (A ω)) μ)
    (hop : Integrable (fun ω => HDP.matrixOpNorm (A ω)) μ) :
    (∫ ω, rectangularRowColumnL2Norm (A ω) ∂μ) ≤
      ∫ ω, HDP.matrixOpNorm (A ω) ∂μ := by
  exact integral_mono hmax hop fun ω =>
    rectangularRowColumnL2Norm_le_operatorNorm (A ω)

/-! ### Canonical signs and the complete Exercise 6.28 interface -/

/-- Canonical independent signs indexed by rectangular matrix coordinates. -/
abbrev RectangularSignSample (m n : ℕ) := Fin m × Fin n → ℝ

/-- Product law of canonical Rademacher signs.

**Lean implementation helper.** -/
noncomputable def rectangularSignMeasure (m n : ℕ) :
    Measure (RectangularSignSample m n) :=
  Measure.pi fun _ : Fin m × Fin n =>
    bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩

noncomputable instance rectangularSignMeasure_isProbabilityMeasure (m n : ℕ) :
    IsProbabilityMeasure (rectangularSignMeasure m n) := by
  rw [rectangularSignMeasure]
  infer_instance

/-- One canonical rectangular sign coordinate.

**Lean implementation helper.** -/
def rectangularSignCoordinate {m n : ℕ} (ij : Fin m × Fin n) :
    RectangularSignSample m n → ℝ := fun ε => ε ij

/-- Shows that rectangular sign coordinate is measurable.

**Lean implementation helper.** -/
lemma rectangularSignCoordinate_measurable {m n : ℕ} (ij : Fin m × Fin n) :
    Measurable (rectangularSignCoordinate ij) := measurable_pi_apply ij

/-- Each coordinate of the rectangular sign cube is a Rademacher random variable.

**Lean implementation helper.** -/
lemma rectangularSignCoordinate_isRademacher {m n : ℕ} (ij : Fin m × Fin n) :
    HDP.IsRademacher (rectangularSignCoordinate ij)
      (rectangularSignMeasure m n) := by
  refine ⟨(rectangularSignCoordinate_measurable ij).aemeasurable, ?_⟩
  exact (MeasureTheory.measurePreserving_eval
    (fun _ : Fin m × Fin n =>
      bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩) ij).map_eq

/-- Shows that rectangular sign coordinate is independent.

**Lean implementation helper.** -/
lemma rectangularSignCoordinate_independent {m n : ℕ} :
    iIndepFun (fun ij : Fin m × Fin n => rectangularSignCoordinate ij)
      (rectangularSignMeasure m n) := by
  exact iIndepFun_pi (X := fun _ : Fin m × Fin n => id)
    (fun _ => measurable_id.aemeasurable)

/-- Coordinatewise integrability implies integrability of the rectangular operator norm. This is
the finite-dimensional bridge needed by the lower half of the corresponding exercise.

**Lean implementation helper.** -/
lemma rectangularMatrixOpNorm_integrable_of_coordinates
    {m n : ℕ} {a : Fin m × Fin n → Ω → ℝ}
    (ha : ∀ ij, Integrable (a ij) μ) :
    Integrable (fun ω =>
      HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω)) μ := by
  have hsum : Integrable
      (fun ω => ∑ ij, rectangularCoordinateSummand a ij ω) μ :=
    integrable_finsetSum Finset.univ fun ij _ =>
      rectangularCoordinateSummand_integrable ha ij
  have hfun :
      (fun ω => ∑ ij, rectangularCoordinateSummand a ij ω) =
        rectangularMatrixOfCoordinates a := by
    funext ω
    exact sum_rectangularCoordinateSummand a ω
  rw [hfun] at hsum
  change Integrable (fun ω => ‖rectangularMatrixOfCoordinates a ω‖) μ
  exact hsum.norm

/-- Coordinatewise measurability makes the finite maximum of all row and column Euclidean norms
measurable.

**Lean implementation helper.** -/
lemma rectangularRowColumnL2Norm_measurable_of_coordinates
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {a : Fin m × Fin n → Ω → ℝ}
    (ha : ∀ ij, Measurable (a ij)) :
    Measurable (fun ω => rectangularRowColumnL2Norm
      (rectangularMatrixOfCoordinates a ω)) := by
  let A : Ω → Matrix (Fin m) (Fin n) ℝ := rectangularMatrixOfCoordinates a
  have hrow (i : Fin m) : Measurable (fun ω =>
      ‖(WithLp.toLp 2 ((A ω).row i) : WithLp 2 (Fin n → ℝ))‖) := by
    apply Measurable.norm
    exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
      (measurable_pi_lambda _ fun j => ha (i, j))
  have hrowSup : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin m)) (fun i ω =>
        ‖(WithLp.toLp 2 ((A ω).row i) : WithLp 2 (Fin n → ℝ))‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ => hrow i
  have hrowEq : (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin m)) (fun i ω =>
        ‖(WithLp.toLp 2 ((A ω).row i) : WithLp 2 (Fin n → ℝ))‖)) =
      fun ω => HDP.Chapter4.maxRowL2Norm (A ω) := by
    funext ω
    simp only [Finset.sup'_apply]
    unfold HDP.Chapter4.maxRowL2Norm
    rw [Finset.max'_eq_sup', Finset.sup'_image]
    simp only [Function.comp_apply, id_eq]
  have hrowM : Measurable (fun ω => HDP.Chapter4.maxRowL2Norm (A ω)) := by
    rwa [hrowEq] at hrowSup
  have hcol (j : Fin n) : Measurable (fun ω =>
      ‖(WithLp.toLp 2 ((A ω).col j) : WithLp 2 (Fin m → ℝ))‖) := by
    apply Measurable.norm
    exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable.comp
      (measurable_pi_lambda _ fun i => ha (i, j))
  have hcolSup : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin n)) (fun j ω =>
        ‖(WithLp.toLp 2 ((A ω).col j) : WithLp 2 (Fin m → ℝ))‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun j _ => hcol j
  have hcolEq : (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin n)) (fun j ω =>
        ‖(WithLp.toLp 2 ((A ω).col j) : WithLp 2 (Fin m → ℝ))‖)) =
      fun ω => HDP.Chapter4.maxColumnL2Norm (A ω) := by
    funext ω
    simp only [Finset.sup'_apply]
    unfold HDP.Chapter4.maxColumnL2Norm
    rw [Finset.max'_eq_sup', Finset.sup'_image]
    simp only [Function.comp_apply, id_eq]
  have hcolM : Measurable (fun ω => HDP.Chapter4.maxColumnL2Norm (A ω)) := by
    rwa [hcolEq] at hcolSup
  exact hrowM.max hcolM

/-- Coordinatewise integrability also controls the rectangular row/column maximum. This
discharges the last analytic hypothesis of the corresponding exercise.

**Lean implementation helper.** -/
lemma rectangularRowColumnL2Norm_integrable_of_coordinates
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    {a : Fin m × Fin n → Ω → ℝ}
    (ham : ∀ ij, Measurable (a ij)) (ha : ∀ ij, Integrable (a ij) μ) :
    Integrable (fun ω => rectangularRowColumnL2Norm
      (rectangularMatrixOfCoordinates a ω)) μ := by
  refine (rectangularMatrixOpNorm_integrable_of_coordinates ha).mono'
    (rectangularRowColumnL2Norm_measurable_of_coordinates ham).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (rectangularRowColumnL2Norm_nonneg _)]
  exact rectangularRowColumnL2Norm_le_operatorNorm _

/-- This combines the elementary lower bound proved here with the unique upper-bound proof in
`09_SymmetricRandomMatrices`. The source's missing expectation on the upper right-hand side is
restored.

**Book (6.18).** -/
theorem exercise_6_28_rectangular_expectedNorm
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    [IsProbabilityMeasure μ]
    (a : Fin m × Fin n → Ω → ℝ)
    (ham : ∀ ij, Measurable (a ij))
    (ha : ∀ ij, Integrable (a ij) μ)
    (ha0 : ∀ ij, ∫ ω, a ij ω ∂μ = 0)
    (haind : iIndepFun a μ)
    (hrc : Integrable (fun ω =>
      rectangularRowColumnL2Norm (rectangularMatrixOfCoordinates a ω)) μ) :
    (∫ ω, rectangularRowColumnL2Norm
        (rectangularMatrixOfCoordinates a ω) ∂μ) ≤
        ∫ ω, HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω) ∂μ ∧
      (∫ ω, HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω) ∂μ) ≤
        2 * Real.sqrt (2 * Real.log (m + n)) *
          ∫ ω, rectangularRowColumnL2Norm
            (rectangularMatrixOfCoordinates a ω) ∂μ := by
  have hop := rectangularMatrixOpNorm_integrable_of_coordinates ha
  constructor
  · exact exercise_6_28_rectangular_expectedNorm_lower _ hrc hop
  · exact exercise_6_28_rectangular_expectedNorm_upper
      a ham ha ha0 haind hrc
      (fun ij => rectangularSignCoordinate_measurable ij)
      (fun ij => rectangularSignCoordinate_isRademacher ij)
      rectangularSignCoordinate_independent

/-- A row sum of Bernoulli selectors.

**Lean implementation helper.** -/
def bernoulliRowCount {n : ℕ} (δ : Fin n → Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  ∑ j, δ i j ω

/-- The largest row count. A nonempty dimension is explicit because this is an actual finite
maximum, not a supremum with an arbitrary empty value.

**Lean implementation helper.** -/
noncomputable def maxBernoulliRowCount {n : ℕ} [Nonempty (Fin n)]
    (δ : Fin n → Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => bernoulliRowCount δ i ω)

/-- The squared Euclidean energy of a centered selector row.

**Lean implementation helper.** -/
def centeredBernoulliRowEnergy {n : ℕ}
    (δ : Fin n → Fin n → Ω → ℝ) (p : ℝ) (i : Fin n) (ω : Ω) : ℝ :=
  ∑ j, (δ i j ω - p) ^ 2

/-- The largest centered selector-row energy.

**Lean implementation helper.** -/
noncomputable def maxCenteredBernoulliRowEnergy {n : ℕ} [Nonempty (Fin n)]
    (δ : Fin n → Fin n → Ω → ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => centeredBernoulliRowEnergy δ p i ω)

/-- Shows that bernoulli row count is measurable.

**Lean implementation helper.** -/
private lemma bernoulliRowCount_measurable {n : ℕ}
    {δ : Fin n → Fin n → Ω → ℝ} (hδm : ∀ i j, Measurable (δ i j))
    (i : Fin n) : Measurable (bernoulliRowCount δ i) := by
  exact Finset.measurable_sum _ fun j _ => hδm i j

/-- Shows that max bernoulli row count is measurable.

**Lean implementation helper.** -/
private lemma maxBernoulliRowCount_measurable {n : ℕ} [Nonempty (Fin n)]
    {δ : Fin n → Fin n → Ω → ℝ} (hδm : ∀ i j, Measurable (δ i j)) :
    Measurable (maxBernoulliRowCount δ) := by
  have h1 : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin n))
      (fun i => bernoulliRowCount δ i)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ =>
      bernoulliRowCount_measurable hδm i
  have hfun : (Finset.univ.sup' (Finset.univ_nonempty (α := Fin n))
      (fun i => bernoulliRowCount δ i)) = maxBernoulliRowCount δ := by
    funext ω
    simp only [Finset.sup'_apply]
    rfl
  rwa [hfun] at h1

/-- Shows that max centered bernoulli row energy is measurable.

**Lean implementation helper.** -/
private lemma maxCenteredBernoulliRowEnergy_measurable {n : ℕ}
    [Nonempty (Fin n)] {δ : Fin n → Fin n → Ω → ℝ}
    (hδm : ∀ i j, Measurable (δ i j)) (p : ℝ) :
    Measurable (maxCenteredBernoulliRowEnergy δ p) := by
  have h1 : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin n))
      (fun i => centeredBernoulliRowEnergy δ p i)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ =>
        ((hδm i j).sub_const p).pow_const 2
  have hfun : (Finset.univ.sup' (Finset.univ_nonempty (α := Fin n))
      (fun i => centeredBernoulliRowEnergy δ p i)) =
      maxCenteredBernoulliRowEnergy δ p := by
    funext ω
    simp only [Finset.sup'_apply]
    rfl
  rwa [hfun] at h1

/-- Shows that max bernoulli row count is integrable.

**Lean implementation helper.** -/
private lemma maxBernoulliRowCount_integrable [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] {δ : Fin n → Fin n → Ω → ℝ}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ) :
    Integrable (maxBernoulliRowCount δ) μ := by
  have hsum : Integrable (fun ω => ∑ i, ∑ j, δ i j ω) μ :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hδ i j).integrable_comp id
  refine hsum.mono' (maxBernoulliRowCount_measurable hδm).aestronglyMeasurable ?_
  have hae : ∀ᵐ ω ∂μ, ∀ i j, δ i j ω = 1 ∨ δ i j ω = 0 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hδ i j).ae_mem
  filter_upwards [hae] with ω hω
  have hnonneg (i j : Fin n) : 0 ≤ δ i j ω := by
    rcases hω i j with h | h <;> simp [h]
  have hrow (i : Fin n) : 0 ≤ bernoulliRowCount δ i ω :=
    Finset.sum_nonneg fun j _ => hnonneg i j
  have hmax0 : 0 ≤ maxBernoulliRowCount δ ω := by
    obtain ⟨i, _⟩ := Finset.univ_nonempty (α := Fin n)
    exact (hrow i).trans (by
      simpa [maxBernoulliRowCount] using
        (Finset.le_sup' (fun k => bernoulliRowCount δ k ω) (Finset.mem_univ i)))
  rw [Real.norm_eq_abs, abs_of_nonneg hmax0]
  calc
    maxBernoulliRowCount δ ω ≤ ∑ i, bernoulliRowCount δ i ω :=
      Finset.sup'_le _ _ fun i _ =>
        Finset.single_le_sum (fun k _ => hrow k) (Finset.mem_univ i)
    _ = ∑ i, ∑ j, δ i j ω := rfl

/-- Shows that exp max bernoulli row count is integrable.

**Lean implementation helper.** -/
private lemma exp_maxBernoulliRowCount_integrable [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] {δ : Fin n → Fin n → Ω → ℝ}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ) :
    Integrable (fun ω => Real.exp (maxBernoulliRowCount δ ω)) μ := by
  have hsum : Integrable (fun ω => ∑ i,
      Real.exp (bernoulliRowCount δ i ω)) μ :=
    integrable_finsetSum _ fun i _ => by
      simpa [bernoulliRowCount, one_mul] using
        HDP.Chapter2.integrable_exp_mul_bernoulli_sum
          (X := δ i) (p := fun _ => p) (fun j => hδ i j) 1
  refine hsum.mono'
    (measurable_exp.comp (maxBernoulliRowCount_measurable hδm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (H := Finset.univ_nonempty (α := Fin n))
    (fun i => bernoulliRowCount δ i ω)
  rw [show maxBernoulliRowCount δ ω = bernoulliRowCount δ i ω by exact hi]
  exact Finset.single_le_sum
    (f := fun k => Real.exp (bernoulliRowCount δ k ω))
    (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ i)

/-- Exponential-moment bound for the largest Bernoulli row count. Independence is only required
within each row.

**Lean implementation helper.** -/
lemma integral_maxBernoulliRowCount_le [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {δ : Fin n → Fin n → Ω → ℝ} {p : I}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hindep : ∀ i, iIndepFun (δ i) μ) :
    (∫ ω, maxBernoulliRowCount δ ω ∂μ) ≤
      Real.log n + (Real.exp 1 - 1) * (n * (p : ℝ)) := by
  let M : Ω → ℝ := maxBernoulliRowCount δ
  have hMint : Integrable M μ := maxBernoulliRowCount_integrable hδm hδ
  have hexpint : Integrable (fun ω => Real.exp (M ω)) μ :=
    exp_maxBernoulliRowCount_integrable hδm hδ
  have hjensen : Real.exp (∫ ω, M ω ∂μ) ≤ ∫ ω, Real.exp (M ω) ∂μ := by
    simpa using HDP.Chapter1.jensen_inequality convexOn_exp hMint hexpint
  have hmgf (i : Fin n) :
      (∫ ω, Real.exp (bernoulliRowCount δ i ω) ∂μ) ≤
        Real.exp ((Real.exp 1 - 1) * (n * (p : ℝ))) := by
    have h := HDP.Chapter2.mgf_bernoulli_sum_le
      (X := δ i) (p := fun _ => p) (fun j => hδ i j) (hindep i) 1
    simpa [mgf, bernoulliRowCount, one_mul] using h
  have hupper : (∫ ω, Real.exp (M ω) ∂μ) ≤
      n * Real.exp ((Real.exp 1 - 1) * (n * (p : ℝ))) := by
    calc
      (∫ ω, Real.exp (M ω) ∂μ) ≤
          ∫ ω, ∑ i, Real.exp (bernoulliRowCount δ i ω) ∂μ := by
        apply integral_mono hexpint
          (integrable_finsetSum _ fun i _ => by
            simpa [bernoulliRowCount, one_mul] using
              HDP.Chapter2.integrable_exp_mul_bernoulli_sum
                (X := δ i) (p := fun _ => p) (fun j => hδ i j) 1)
        intro ω
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
          (H := Finset.univ_nonempty (α := Fin n))
          (fun i => bernoulliRowCount δ i ω)
        change Real.exp (maxBernoulliRowCount δ ω) ≤ _
        rw [show maxBernoulliRowCount δ ω = bernoulliRowCount δ i ω by
          simpa [maxBernoulliRowCount] using hi]
        exact Finset.single_le_sum
          (f := fun k => Real.exp (bernoulliRowCount δ k ω))
          (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ i)
      _ = ∑ i, ∫ ω, Real.exp (bernoulliRowCount δ i ω) ∂μ :=
        integral_finsetSum _ fun i _ => by
          simpa [bernoulliRowCount, one_mul] using
            HDP.Chapter2.integrable_exp_mul_bernoulli_sum
              (X := δ i) (p := fun _ => p) (fun j => hδ i j) 1
      _ ≤ ∑ _i : Fin n,
          Real.exp ((Real.exp 1 - 1) * (n * (p : ℝ))) :=
        Finset.sum_le_sum fun i _ => hmgf i
      _ = n * Real.exp ((Real.exp 1 - 1) * (n * (p : ℝ))) := by simp
  have hlog := Real.log_le_log (Real.exp_pos _) (hjensen.trans hupper)
  have hnreal : (0 : ℝ) < n := by positivity
  rw [Real.log_exp, Real.log_mul hnreal.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  simpa [M] using hlog

/-- Bounds centered row energy by count add.

**Lean implementation helper.** -/
private lemma centeredRowEnergy_le_count_add {n : ℕ}
    {δ : Fin n → Fin n → Ω → ℝ} {p : I} {i : Fin n} {ω : Ω}
    (hδ : ∀ j, δ i j ω = 1 ∨ δ i j ω = 0) :
    centeredBernoulliRowEnergy δ p i ω ≤
      bernoulliRowCount δ i ω + n * (p : ℝ) ^ 2 := by
  simp only [centeredBernoulliRowEnergy, bernoulliRowCount]
  calc
    (∑ j, (δ i j ω - (p : ℝ)) ^ 2) ≤
        ∑ j, (δ i j ω + (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      rcases hδ j with h | h <;> rw [h]
      · have hp0 : 0 ≤ (p : ℝ) := p.2.1
        nlinarith
      · norm_num
    _ = (∑ j, δ i j ω) + n * (p : ℝ) ^ 2 := by simp [Finset.sum_add_distrib]

/-- The maximum centered Bernoulli row energy is at most the maximum row count plus `n p²`.

**Lean implementation helper.** -/
private lemma maxCenteredRowEnergy_le {n : ℕ} [Nonempty (Fin n)]
    {δ : Fin n → Fin n → Ω → ℝ} {p : I} {ω : Ω}
    (hδ : ∀ i j, δ i j ω = 1 ∨ δ i j ω = 0) :
    maxCenteredBernoulliRowEnergy δ p ω ≤
      maxBernoulliRowCount δ ω + n * (p : ℝ) ^ 2 := by
  apply Finset.sup'_le _ _
  intro i _
  have hle : bernoulliRowCount δ i ω ≤ maxBernoulliRowCount δ ω := by
    let hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
    change bernoulliRowCount δ i ω ≤
      Finset.univ.sup' hne (fun k => bernoulliRowCount δ k ω)
    exact Finset.le_sup' (fun k : Fin n => bernoulliRowCount δ k ω)
      (Finset.mem_univ i)
  exact (centeredRowEnergy_le_count_add (fun j => hδ i j)).trans
    (add_le_add hle le_rfl)

/-- Shows that max centered bernoulli row energy is integrable.

**Lean implementation helper.** -/
private lemma maxCenteredBernoulliRowEnergy_integrable [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] {δ : Fin n → Fin n → Ω → ℝ} {p : I}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ) :
    Integrable (maxCenteredBernoulliRowEnergy δ p) μ := by
  have hM := maxBernoulliRowCount_integrable hδm hδ
  have hdom : Integrable (fun ω => maxBernoulliRowCount δ ω + n * (p : ℝ) ^ 2) μ :=
    hM.add (integrable_const _)
  refine hdom.mono'
    (maxCenteredBernoulliRowEnergy_measurable hδm p).aestronglyMeasurable ?_
  have hae : ∀ᵐ ω ∂μ, ∀ i j, δ i j ω = 1 ∨ δ i j ω = 0 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hδ i j).ae_mem
  filter_upwards [hae] with ω hω
  have henergy0 : 0 ≤ maxCenteredBernoulliRowEnergy δ p ω := by
    obtain ⟨i, _⟩ := Finset.univ_nonempty (α := Fin n)
    exact (Finset.sum_nonneg fun j _ => sq_nonneg _).trans (by
      simpa [maxCenteredBernoulliRowEnergy, centeredBernoulliRowEnergy] using
        (Finset.le_sup'
          (fun k => centeredBernoulliRowEnergy δ p k ω) (Finset.mem_univ i)))
  have hcount0 : 0 ≤ maxBernoulliRowCount δ ω := by
    obtain ⟨i, _⟩ := Finset.univ_nonempty (α := Fin n)
    have hi : 0 ≤ bernoulliRowCount δ i ω :=
      Finset.sum_nonneg fun j _ => by
        rcases hω i j with h | h <;> simp [h]
    exact hi.trans (by
      simpa [maxBernoulliRowCount] using
        (Finset.le_sup' (fun k => bernoulliRowCount δ k ω) (Finset.mem_univ i)))
  rw [Real.norm_eq_abs, abs_of_nonneg henergy0]
  exact maxCenteredRowEnergy_le hω

/-- For Bernoulli selectors and `pn ≥ log n`, the expected largest centered row energy is at
most `4pn`. The explicit constant is absolute and no independence between different rows is
needed.

**Book Exercise 6.30.** -/
theorem exercise_6_30_bernoulli_row_energy [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {δ : Fin n → Fin n → Ω → ℝ} {p : I}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hindep : ∀ i, iIndepFun (δ i) μ)
    (hregime : Real.log n ≤ n * (p : ℝ)) :
    (∫ ω, maxCenteredBernoulliRowEnergy δ p ω ∂μ) ≤
      4 * (n * (p : ℝ)) := by
  have hM := integral_maxBernoulliRowCount_le hn hδm hδ hindep
  have henergyInt := maxCenteredBernoulliRowEnergy_integrable hδm hδ
  have hcountInt := maxBernoulliRowCount_integrable hδm hδ
  have hpoint : ∀ᵐ ω ∂μ,
      maxCenteredBernoulliRowEnergy δ p ω ≤
        maxBernoulliRowCount δ ω + n * (p : ℝ) ^ 2 := by
    have hae : ∀ᵐ ω ∂μ, ∀ i j, δ i j ω = 1 ∨ δ i j ω = 0 :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hδ i j).ae_mem
    filter_upwards [hae] with ω hω
    exact maxCenteredRowEnergy_le hω
  have hint : (∫ ω, maxCenteredBernoulliRowEnergy δ p ω ∂μ) ≤
      (∫ ω, maxBernoulliRowCount δ ω ∂μ) + n * (p : ℝ) ^ 2 := by
    calc
      (∫ ω, maxCenteredBernoulliRowEnergy δ p ω ∂μ) ≤
          ∫ ω, (maxBernoulliRowCount δ ω + n * (p : ℝ) ^ 2) ∂μ :=
        integral_mono_ae henergyInt (hcountInt.add (integrable_const _)) hpoint
      _ = (∫ ω, maxBernoulliRowCount δ ω ∂μ) + n * (p : ℝ) ^ 2 := by
        rw [integral_add hcountInt (integrable_const _), integral_const,
          probReal_univ]
        simp
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hnp0 : 0 ≤ n * (p : ℝ) := mul_nonneg (Nat.cast_nonneg n) hp0
  have hexp : Real.exp 1 - 1 ≤ 2 := by
    linarith [Real.exp_one_lt_three]
  have hpSq : n * (p : ℝ) ^ 2 ≤ n * (p : ℝ) := by
    nlinarith
  calc
    (∫ ω, maxCenteredBernoulliRowEnergy δ p ω ∂μ) ≤
        (∫ ω, maxBernoulliRowCount δ ω ∂μ) + n * (p : ℝ) ^ 2 := hint
    _ ≤ (Real.log n + (Real.exp 1 - 1) * (n * (p : ℝ))) +
        n * (p : ℝ) ^ 2 := add_le_add hM le_rfl
    _ ≤ 4 * (n * (p : ℝ)) := by nlinarith

/-- Shows that integrability sqrt of integrability is nonnegative.

**Lean implementation helper.** -/
private lemma integrable_sqrt_of_integrable_nonneg [IsFiniteMeasure μ]
    {M : Ω → ℝ} (hM : Integrable M μ) (hM0 : ∀ ω, 0 ≤ M ω) :
    Integrable (fun ω => Real.sqrt (M ω)) μ := by
  refine (hM.add (integrable_const 1)).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hM.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_le_iff]
  constructor
  · linarith [hM0 ω]
  · nlinarith [hM0 ω, sq_nonneg (M ω)]

/-- Jensen's square-root consequence of the corresponding exercise. This is the exact form
consumed by the matrix-completion proof.

**Book Exercise 6.30.** -/
theorem exercise_6_30_sqrt_row_energy [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {δ : Fin n → Fin n → Ω → ℝ} {p : I}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hindep : ∀ i, iIndepFun (δ i) μ)
    (hregime : Real.log n ≤ n * (p : ℝ)) :
    Integrable (fun ω => Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω)) μ ∧
      (∫ ω, Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) ∂μ) ≤
        2 * Real.sqrt (n * (p : ℝ)) := by
  have hM : Integrable (maxCenteredBernoulliRowEnergy δ p) μ :=
    maxCenteredBernoulliRowEnergy_integrable hδm hδ
  have hM0 : ∀ ω, 0 ≤ maxCenteredBernoulliRowEnergy δ p ω := by
    intro ω
    let i : Fin n := Classical.choice inferInstance
    exact (Finset.sum_nonneg fun j _ => sq_nonneg (δ i j ω - (p : ℝ))).trans (by
      simpa [maxCenteredBernoulliRowEnergy, centeredBernoulliRowEnergy] using
        (Finset.le_sup'
          (fun k => centeredBernoulliRowEnergy δ p k ω) (Finset.mem_univ i)))
  have hsqrt := integrable_sqrt_of_integrable_nonneg hM hM0
  refine ⟨hsqrt, ?_⟩
  have hjensen := HDP.Chapter1.jensen_inequality_concave
    (X := maxCenteredBernoulliRowEnergy δ p) (g := Real.sqrt)
    (Real.strictConcaveOn_sqrt).concaveOn Real.continuous_sqrt.continuousOn
    (Filter.Eventually.of_forall hM0) hM hsqrt
  have hMbound := exercise_6_30_bernoulli_row_energy
    hn hδm hδ hindep hregime
  have hnp : 0 ≤ n * (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) p.2.1
  calc
    (∫ ω, Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) ∂μ) ≤
        Real.sqrt (∫ ω, maxCenteredBernoulliRowEnergy δ p ω ∂μ) :=
      hjensen
    _ ≤ Real.sqrt (4 * (n * (p : ℝ))) := Real.sqrt_le_sqrt hMbound
    _ = 2 * Real.sqrt (n * (p : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
          Real.sqrt_sq_eq_abs]
        norm_num
      rw [h4]

end HDP.Chapter6

end Source_10_RectangularRandomMatrices

/-! ## Material formerly in `11_MatrixCompletion.lean` -/

section Source_11_MatrixCompletion

/-!
# Chapter 6, §6.5: matrix completion

The probabilistic part of matrix completion supplies an operator-norm bound for
the centered observation matrix.  This module proves the complete deterministic
recovery chain, including its rectangular and noisy forms, and exposes a
measure-theoretic transfer theorem which consumes such an operator estimate.
No measurable choice of singular vectors is hidden in the API: a candidate
approximation is quantified together with its rank and best-approximation
certificate.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal unitInterval Matrix.Norms.L2Operator

namespace HDP.Chapter6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Rank calculus -/

/-- Rank is subadditive for the authoritative Euclidean matrix rank.

**Lean implementation helper.** -/
theorem matrixRank_add_le {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixRank (A + B) ≤ HDP.matrixRank A + HDP.matrixRank B := by
  rw [HDP.matrixRank_eq_finrank_range, HDP.matrixRank_eq_finrank_range,
    HDP.matrixRank_eq_finrank_range]
  have hrange : (A + B).toEuclideanLin.range ≤
      A.toEuclideanLin.range ⊔ B.toEuclideanLin.range := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hA : A.toEuclideanLin x ∈ A.toEuclideanLin.range := ⟨x, rfl⟩
    have hB : B.toEuclideanLin x ∈ B.toEuclideanLin.range := ⟨x, rfl⟩
    simpa using Submodule.add_mem_sup hA hB
  exact (Submodule.finrank_mono hrange).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Negating a matrix does not change its rank.

**Lean implementation helper.** -/
@[simp] lemma matrixRank_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixRank (-A) = HDP.matrixRank A := by
  rw [HDP.matrixRank_eq_finrank_range, HDP.matrixRank_eq_finrank_range]
  have hrange : (-A).toEuclideanLin.range = A.toEuclideanLin.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      simp
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      simp
  rw [hrange]

/-- Rank of a difference is at most the sum of ranks.

**Lean implementation helper.** -/
theorem matrixRank_sub_le {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixRank (A - B) ≤ HDP.matrixRank A + HDP.matrixRank B := by
  simpa [sub_eq_add_neg] using matrixRank_add_le A (-B)

/-- Two rank-`r` matrices differ by a matrix of rank at most `2r`.

**Lean implementation helper.** -/
theorem matrixRank_sub_le_two_mul {m n r : ℕ}
    {A B : Matrix (Fin m) (Fin n) ℝ}
    (hA : HDP.matrixRank A ≤ r) (hB : HDP.matrixRank B ≤ r) :
    HDP.matrixRank (A - B) ≤ 2 * r := by
  exact (matrixRank_sub_le A B).trans (by omega)

/-! ## Best-rank approximation and deterministic recovery -/

/-- A tie-safe certificate saying that `Xhat` is at least as good as the rank-`r` target `X`
when approximating the proxy `Z` in operator norm.

**Lean implementation helper.** -/
def IsBestAgainst (Xhat X Z : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  HDP.matrixOpNorm (Xhat - Z) ≤ HDP.matrixOpNorm (X - Z)

/-- Best-approximation operator error is at most twice the proxy error.

**Book (6.17).** -/
theorem operatorError_le_two_mul_proxyError {m n : ℕ}
    {Xhat X Z : Matrix (Fin m) (Fin n) ℝ}
    (hbest : IsBestAgainst Xhat X Z) :
    HDP.matrixOpNorm (Xhat - X) ≤ 2 * HDP.matrixOpNorm (Z - X) := by
  have hXZ : HDP.matrixOpNorm (X - Z) = HDP.matrixOpNorm (Z - X) := by
    rw [show X - Z = -(Z - X) by abel, HDP.matrixOpNorm_neg]
  have hdecomp : Xhat - X = (Xhat - Z) + (Z - X) := by abel
  calc
    HDP.matrixOpNorm (Xhat - X) =
        HDP.matrixOpNorm ((Xhat - Z) + (Z - X)) := by rw [hdecomp]
    _ ≤ HDP.matrixOpNorm (Xhat - Z) + HDP.matrixOpNorm (Z - X) :=
      HDP.matrixOpNorm_add_le _ _
    _ ≤ HDP.matrixOpNorm (X - Z) + HDP.matrixOpNorm (Z - X) :=
      add_le_add hbest le_rfl
    _ = 2 * HDP.matrixOpNorm (Z - X) := by rw [hXZ]; ring

/-- Deterministic Frobenius recovery bound. This is Step 2 of the corresponding theorem and
simultaneously the core of rectangular the corresponding exercise.

**Book Chapter 6, pp.190--192, completion proof.** -/
theorem frobeniusError_le_of_bestRank {m n r : ℕ}
    {Xhat X Z : Matrix (Fin m) (Fin n) ℝ}
    (hXhatRank : HDP.matrixRank Xhat ≤ r)
    (hXRank : HDP.matrixRank X ≤ r)
    (hbest : IsBestAgainst Xhat X Z) :
    HDP.matrixFrobeniusNorm (Xhat - X) ≤
      2 * Real.sqrt (↑(2 * r) : ℝ) * HDP.matrixOpNorm (Z - X) := by
  have hrank : HDP.matrixRank (Xhat - X) ≤ 2 * r :=
    matrixRank_sub_le_two_mul hXhatRank hXRank
  have hfrob := HDP.Chapter4.frobeniusNorm_le_sqrt_rank_mul_operatorNorm
    (Xhat - X) hrank
  have hop := operatorError_le_two_mul_proxyError hbest
  calc
    HDP.matrixFrobeniusNorm (Xhat - X) ≤
        Real.sqrt (↑(2 * r) : ℝ) * HDP.matrixOpNorm (Xhat - X) := hfrob
    _ ≤ Real.sqrt (↑(2 * r) : ℝ) * (2 * HDP.matrixOpNorm (Z - X)) :=
      mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (↑(2 * r) : ℝ) * HDP.matrixOpNorm (Z - X) := by ring

/-- The Chapter 4 spectral truncation is a concrete best-rank approximation. The index condition
`r<n` is the safe zero-indexed form required by the SVD API.

**Lean implementation helper.** -/
noncomputable def matrixCompletionEstimator {m n r : ℕ}
    (Z : Matrix (Fin m) (Fin n) ℝ) (hr : r < n) :
    Matrix (Fin m) (Fin n) ℝ :=
  HDP.Chapter4.truncatedSVDApproximation Z hr

/-- The rank-`r` matrix-completion estimator has rank at most `r`.

**Lean implementation helper.** -/
lemma matrixCompletionEstimator_rank_le {m n r : ℕ}
    (Z : Matrix (Fin m) (Fin n) ℝ) (hr : r < n) :
    HDP.matrixRank (matrixCompletionEstimator Z hr) ≤ r := by
  exact HDP.Chapter4.rank_truncatedSVDApproximation_le Z hr

/-- The rank-constrained matrix-completion estimator is a best approximation to the observations among admissible competitors.

**Lean implementation helper.** -/
lemma matrixCompletionEstimator_bestAgainst {m n r : ℕ}
    (Z X : Matrix (Fin m) (Fin n) ℝ) (hr : r < n)
    (hXrank : HDP.matrixRank X ≤ r) :
    IsBestAgainst (matrixCompletionEstimator Z hr) X Z := by
  have hEYM := HDP.Chapter4.eckartYoungMirsky hr Z
  have hlower := hEYM.2.2 X hXrank
  have heq := hEYM.2.1
  have hleft : HDP.matrixOpNorm (matrixCompletionEstimator Z hr - Z) =
      HDP.matrixOpNorm (Z - matrixCompletionEstimator Z hr) := by
    rw [show matrixCompletionEstimator Z hr - Z =
      -(Z - matrixCompletionEstimator Z hr) by abel, HDP.matrixOpNorm_neg]
  have hright : HDP.matrixOpNorm (X - Z) = HDP.matrixOpNorm (Z - X) := by
    rw [show X - Z = -(Z - X) by abel, HDP.matrixOpNorm_neg]
  change HDP.matrixOpNorm (matrixCompletionEstimator Z hr - Z) ≤
    HDP.matrixOpNorm (X - Z)
  rw [hleft, hright]
  change HDP.matrixOpNorm
    (Z - HDP.Chapter4.truncatedSVDApproximation Z hr) ≤
      HDP.matrixOpNorm (Z - X)
  rw [heq]
  exact hlower

/-- Concrete deterministic endpoint obtained by spectral truncation.

**Lean implementation helper.** -/
theorem matrixCompletionEstimator_frobeniusError {m n r : ℕ}
    (Z X : Matrix (Fin m) (Fin n) ℝ) (hr : r < n)
    (hXrank : HDP.matrixRank X ≤ r) :
    HDP.matrixFrobeniusNorm (matrixCompletionEstimator Z hr - X) ≤
      2 * Real.sqrt (↑(2 * r) : ℝ) * HDP.matrixOpNorm (Z - X) := by
  exact frobeniusError_le_of_bestRank
    (matrixCompletionEstimator_rank_le Z hr) hXrank
    (matrixCompletionEstimator_bestAgainst Z X hr hXrank)

/-! ## Observation model and scaling -/

/-- Entrywise Bernoulli observation of a deterministic matrix.

**Book Chapter 6, pp.190--192, completion proof.** -/
def sampledMatrix {m n : ℕ}
    (δ : Fin m → Fin n → Ω → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (ω : Ω) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => δ i j ω * X i j

/-- Sampling acts entrywise: the `(i,j)` entry is `δ i j ω * X i j`.

**Lean implementation helper.** -/
@[simp] lemma sampledMatrix_apply {m n : ℕ}
    (δ : Fin m → Fin n → Ω → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (ω : Ω) (i : Fin m) (j : Fin n) :
    sampledMatrix δ X ω i j = δ i j ω * X i j := rfl

/-- The centered observed matrix has entries `(δᵢⱼ-p)Xᵢⱼ`.

**Lean implementation helper.** -/
lemma sampledMatrix_sub_mean_apply {m n : ℕ}
    (δ : Fin m → Fin n → Ω → ℝ) (X : Matrix (Fin m) (Fin n) ℝ)
    (p : ℝ) (ω : Ω) (i : Fin m) (j : Fin n) :
    (sampledMatrix δ X ω - p • X) i j = (δ i j ω - p) * X i j := by
  simp [sampledMatrix]
  ring

/-- Independent scalar coordinates of the centered observation matrix.

**Lean implementation helper.** -/
def centeredSamplingCoordinates {m n : ℕ}
    (δ : Fin m → Fin n → Ω → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) (p : ℝ) :
    Fin m × Fin n → Ω → ℝ :=
  fun ij ω => (δ ij.1 ij.2 ω - p) * X ij.1 ij.2

/-- The coordinate model reconstructs `Y-pX` exactly.

**Lean implementation helper.** -/
lemma rectangularMatrixOfCoordinates_centeredSamplingCoordinates
    {m n : ℕ} (δ : Fin m → Fin n → Ω → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) (p : ℝ) (ω : Ω) :
    rectangularMatrixOfCoordinates (centeredSamplingCoordinates δ X p) ω =
      sampledMatrix δ X ω - p • X := by
  ext i j
  exact sampledMatrix_sub_mean_apply δ X p ω i j |>.symm

/-- Deterministic row-norm estimate used in the corresponding theorem.

**Lean implementation helper.** -/
lemma maxRowL2Norm_centeredSampling_le {n : ℕ} [Nonempty (Fin n)]
    (δ : Fin n → Fin n → Ω → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (ω : Ω) :
    HDP.Chapter4.maxRowL2Norm (sampledMatrix δ X ω - p • X) ≤
      HDP.Chapter4.maxAbsEntry X *
        Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) := by
  let M : ℝ := HDP.Chapter4.maxAbsEntry X
  let E : ℝ := maxCenteredBernoulliRowEnergy δ p ω
  have hM : 0 ≤ M := HDP.Chapter4.maxAbsEntry_nonneg X
  have hE : 0 ≤ E := by
    let i : Fin n := Classical.choice inferInstance
    exact (Finset.sum_nonneg fun j _ => sq_nonneg (δ i j ω - p)).trans (by
      simpa [E, maxCenteredBernoulliRowEnergy, centeredBernoulliRowEnergy] using
        (Finset.le_sup'
          (fun k => centeredBernoulliRowEnergy δ p k ω) (Finset.mem_univ i)))
  have hRhs : 0 ≤ M * Real.sqrt E :=
    mul_nonneg hM (Real.sqrt_nonneg _)
  obtain ⟨i, hi⟩ := HDP.Chapter4.exists_row_eq_maxRowL2Norm
    (sampledMatrix δ X ω - p • X)
  rw [← hi]
  apply (sq_le_sq₀ (norm_nonneg _) hRhs).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt hE]
  simp only [Matrix.row, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    sampledMatrix_apply]
  calc
    (∑ j, ( δ i j ω * X i j - p * X i j) ^ 2) =
        ∑ j, ((δ i j ω - p) * X i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    (∑ j, ((δ i j ω - p) * X i j) ^ 2) ≤
        ∑ j, (δ i j ω - p) ^ 2 * M ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hx := HDP.Chapter4.abs_entry_le_maxAbsEntry X i j
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (X i j)) hM).2 hx
    _ = M ^ 2 * centeredBernoulliRowEnergy δ p i ω := by
      simp only [centeredBernoulliRowEnergy]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ M ^ 2 * E := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
      simpa [E, maxCenteredBernoulliRowEnergy] using
        (Finset.le_sup' (fun k => centeredBernoulliRowEnergy δ p k ω)
          (Finset.mem_univ i))

/-- Deterministic column analogue, obtained from the row estimate by transposition.

**Lean implementation helper.** -/
lemma maxColumnL2Norm_centeredSampling_le {n : ℕ} [Nonempty (Fin n)]
    (δ : Fin n → Fin n → Ω → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (ω : Ω) :
    HDP.Chapter4.maxColumnL2Norm (sampledMatrix δ X ω - p • X) ≤
      HDP.Chapter4.maxAbsEntry X *
        Real.sqrt (maxCenteredBernoulliRowEnergy
          (fun j i => δ i j) p ω) := by
  let δT : Fin n → Fin n → Ω → ℝ := fun j i => δ i j
  have h := maxRowL2Norm_centeredSampling_le δT X.transpose p ω
  have hmat : sampledMatrix δT X.transpose ω - p • X.transpose =
      (sampledMatrix δ X ω - p • X).transpose := by
    ext i j
    simp [δT, sampledMatrix]
  have hmax : HDP.Chapter4.maxAbsEntry X.transpose =
      HDP.Chapter4.maxAbsEntry X := by
    apply le_antisymm
    · obtain ⟨i, j, hij⟩ :=
        HDP.Chapter4.exists_entry_eq_maxAbsEntry X.transpose
      rw [← hij]
      simpa using HDP.Chapter4.abs_entry_le_maxAbsEntry X j i
    · obtain ⟨i, j, hij⟩ := HDP.Chapter4.exists_entry_eq_maxAbsEntry X
      rw [← hij]
      simpa using HDP.Chapter4.abs_entry_le_maxAbsEntry X.transpose j i
  rw [hmat, hmax] at h
  simpa [δT, HDP.Chapter4.maxColumnL2Norm, HDP.Chapter4.maxRowL2Norm,
    Matrix.row, Matrix.col] using h

/-- Pointwise row/column control for the centered sampling matrix.

**Lean implementation helper.** -/
lemma rectangularRowColumnL2Norm_centeredSampling_le
    {n : ℕ} [Nonempty (Fin n)]
    (δ : Fin n → Fin n → Ω → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (ω : Ω) :
    rectangularRowColumnL2Norm (sampledMatrix δ X ω - p • X) ≤
      HDP.Chapter4.maxAbsEntry X *
        (Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) +
          Real.sqrt (maxCenteredBernoulliRowEnergy
            (fun j i => δ i j) p ω)) := by
  have hM : 0 ≤ HDP.Chapter4.maxAbsEntry X :=
    HDP.Chapter4.maxAbsEntry_nonneg X
  rw [rectangularRowColumnL2Norm, max_le_iff]
  constructor
  · exact (maxRowL2Norm_centeredSampling_le δ X p ω).trans (by
      apply mul_le_mul_of_nonneg_left _ hM
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · exact (maxColumnL2Norm_centeredSampling_le δ X p ω).trans (by
      apply mul_le_mul_of_nonneg_left _ hM
      exact le_add_of_nonneg_left (Real.sqrt_nonneg _))

/-- Coordinatewise measurability of the centered Bernoulli sampling model.

**Lean implementation helper.** -/
lemma centeredSamplingCoordinates_measurable {m n : ℕ}
    {δ : Fin m → Fin n → Ω → ℝ}
    (X : Matrix (Fin m) (Fin n) ℝ) (p : ℝ)
    (hδm : ∀ i j, Measurable (δ i j)) (ij : Fin m × Fin n) :
    Measurable (centeredSamplingCoordinates δ X p ij) := by
  exact ((hδm ij.1 ij.2).sub_const p).mul_const (X ij.1 ij.2)

/-- Bernoulli coordinates give integrable centered sampling coordinates.

**Lean implementation helper.** -/
lemma centeredSamplingCoordinates_integrable [IsProbabilityMeasure μ]
    {m n : ℕ} {δ : Fin m → Fin n → Ω → ℝ}
    (X : Matrix (Fin m) (Fin n) ℝ) (p : I)
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (ij : Fin m × Fin n) :
    Integrable (centeredSamplingCoordinates δ X p ij) μ := by
  exact (hδ ij.1 ij.2).integrable_comp
    (fun x => (x - (p : ℝ)) * X ij.1 ij.2)

/-- Every centered sampling coordinate has mean zero.

**Lean implementation helper.** -/
lemma centeredSamplingCoordinates_integral_eq_zero [IsProbabilityMeasure μ]
    {m n : ℕ} {δ : Fin m → Fin n → Ω → ℝ}
    (X : Matrix (Fin m) (Fin n) ℝ) (p : I)
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (ij : Fin m × Fin n) :
    ∫ ω, centeredSamplingCoordinates δ X p ij ω ∂μ = 0 := by
  have h := (hδ ij.1 ij.2).integral_comp
    (fun x => (x - (p : ℝ)) * X ij.1 ij.2)
  change (∫ ω, (δ ij.1 ij.2 ω - (p : ℝ)) * X ij.1 ij.2 ∂μ) = 0
  calc
    (∫ ω, (δ ij.1 ij.2 ω - (p : ℝ)) * X ij.1 ij.2 ∂μ) =
        (p : ℝ) * ((1 - (p : ℝ)) * X ij.1 ij.2) +
          (1 - (p : ℝ)) * ((0 - (p : ℝ)) * X ij.1 ij.2) := h
    _ = 0 := by ring

/-- Independence is preserved by coordinatewise centering and deterministic entry scaling.

**Lean implementation helper.** -/
lemma centeredSamplingCoordinates_independent {m n : ℕ}
    {δ : Fin m → Fin n → Ω → ℝ}
    (X : Matrix (Fin m) (Fin n) ℝ) (p : ℝ)
    (hind : iIndepFun (fun ij : Fin m × Fin n => δ ij.1 ij.2) μ) :
    iIndepFun (centeredSamplingCoordinates δ X p) μ := by
  change iIndepFun
    (fun (ij : Fin m × Fin n) ω => (δ ij.1 ij.2 ω - p) * X ij.1 ij.2) μ
  exact hind.comp
    (fun ij : Fin m × Fin n => fun x => (x - p) * X ij.1 ij.2)
    (fun _ => by fun_prop)

/-- Joint entry independence supplies independence within every row.

**Lean implementation helper.** -/
lemma iIndepFun_rows_of_entries {m n : ℕ}
    {δ : Fin m → Fin n → Ω → ℝ}
    (hind : iIndepFun (fun ij : Fin m × Fin n => δ ij.1 ij.2) μ)
    (i : Fin m) : iIndepFun (δ i) μ := by
  refine ProbabilityTheory.iIndepFun.precomp
    (g := fun j : Fin n => (i, j)) ?_ hind
  intro j k h
  exact congrArg Prod.snd h

/-- Joint entry independence also supplies independence within every column.

**Lean implementation helper.** -/
lemma iIndepFun_columns_of_entries {m n : ℕ}
    {δ : Fin m → Fin n → Ω → ℝ}
    (hind : iIndepFun (fun ij : Fin m × Fin n => δ ij.1 ij.2) μ)
    (j : Fin n) : iIndepFun (fun i => δ i j) μ := by
  refine ProbabilityTheory.iIndepFun.precomp
    (g := fun i : Fin m => (i, j)) ?_ hind
  intro i k h
  exact congrArg Prod.fst h

/-- Expected row/column maximum for a centered Bernoulli sampling matrix. Both row and column
contributions are controlled by the corresponding exercise.

**Lean implementation helper.** -/
theorem centeredSampling_expectedRowColumnNorm_le [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {δ : Fin n → Fin n → Ω → ℝ} {p : I}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hind : iIndepFun (fun ij : Fin n × Fin n => δ ij.1 ij.2) μ)
    (hregime : Real.log n ≤ n * (p : ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ) :
    (∫ ω, rectangularRowColumnL2Norm
      (sampledMatrix δ X ω - (p : ℝ) • X) ∂μ) ≤
      4 * HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ)) := by
  let δT : Fin n → Fin n → Ω → ℝ := fun j i => δ i j
  have hrow := exercise_6_30_sqrt_row_energy hn hδm hδ
    (iIndepFun_rows_of_entries hind) hregime
  have hcol := exercise_6_30_sqrt_row_energy hn
    (fun i j => hδm j i) (fun i j => hδ j i)
    (fun j => iIndepFun_columns_of_entries hind j) hregime
  have ham : ∀ ij, Measurable (centeredSamplingCoordinates δ X p ij) :=
    fun ij => centeredSamplingCoordinates_measurable X p hδm ij
  have ha : ∀ ij, Integrable (centeredSamplingCoordinates δ X p ij) μ :=
    fun ij => centeredSamplingCoordinates_integrable X p hδ ij
  have hrc : Integrable (fun ω => rectangularRowColumnL2Norm
      (sampledMatrix δ X ω - (p : ℝ) • X)) μ := by
    have h := rectangularRowColumnL2Norm_integrable_of_coordinates ham ha
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      change rectangularRowColumnL2Norm
        (rectangularMatrixOfCoordinates (centeredSamplingCoordinates δ X p) ω) = _
      rw [rectangularMatrixOfCoordinates_centeredSamplingCoordinates])
  have hM : 0 ≤ HDP.Chapter4.maxAbsEntry X :=
    HDP.Chapter4.maxAbsEntry_nonneg X
  have hdom : Integrable (fun ω => HDP.Chapter4.maxAbsEntry X *
      (Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) +
        Real.sqrt (maxCenteredBernoulliRowEnergy δT p ω))) μ :=
    (hrow.1.add hcol.1).const_mul _
  calc
    (∫ ω, rectangularRowColumnL2Norm
        (sampledMatrix δ X ω - (p : ℝ) • X) ∂μ) ≤
        ∫ ω, HDP.Chapter4.maxAbsEntry X *
          (Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) +
            Real.sqrt (maxCenteredBernoulliRowEnergy δT p ω)) ∂μ := by
      apply integral_mono hrc hdom
      intro ω
      simpa [δT] using rectangularRowColumnL2Norm_centeredSampling_le δ X p ω
    _ = HDP.Chapter4.maxAbsEntry X *
        ((∫ ω, Real.sqrt (maxCenteredBernoulliRowEnergy δ p ω) ∂μ) +
          ∫ ω, Real.sqrt (maxCenteredBernoulliRowEnergy δT p ω) ∂μ) := by
      rw [integral_const_mul, integral_add hrow.1 hcol.1]
    _ ≤ HDP.Chapter4.maxAbsEntry X *
        (2 * Real.sqrt (n * (p : ℝ)) +
          2 * Real.sqrt (n * (p : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hrow.2 hcol.2) hM
    _ = 4 * HDP.Chapter4.maxAbsEntry X *
        Real.sqrt (n * (p : ℝ)) := by ring

/-- The unconditional expected operator-norm estimate used in the corresponding theorem. It is
obtained by instantiating the corrected exercise with centered Bernoulli sampling
coordinates and then applying the corresponding exercise.

**Book (6.19).** -/
theorem centeredSampling_expectedOperatorNorm_le [IsProbabilityMeasure μ]
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {δ : Fin n → Fin n → Ω → ℝ} {p : I}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hind : iIndepFun (fun ij : Fin n × Fin n => δ ij.1 ij.2) μ)
    (hregime : Real.log n ≤ n * (p : ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ) :
    (∫ ω, HDP.matrixOpNorm
      (sampledMatrix δ X ω - (p : ℝ) • X) ∂μ) ≤
      8 * Real.sqrt (2 * Real.log (n + n)) *
        HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ)) := by
  let a := centeredSamplingCoordinates δ X (p : ℝ)
  have ham : ∀ ij, Measurable (a ij) :=
    fun ij => centeredSamplingCoordinates_measurable X p hδm ij
  have ha : ∀ ij, Integrable (a ij) μ :=
    fun ij => centeredSamplingCoordinates_integrable X p hδ ij
  have ha0 : ∀ ij, ∫ ω, a ij ω ∂μ = 0 :=
    fun ij => centeredSamplingCoordinates_integral_eq_zero X p hδ ij
  have haind : iIndepFun a μ := centeredSamplingCoordinates_independent X p hind
  have hrc : Integrable (fun ω => rectangularRowColumnL2Norm
      (rectangularMatrixOfCoordinates a ω)) μ :=
    rectangularRowColumnL2Norm_integrable_of_coordinates ham ha
  have hup := (exercise_6_28_rectangular_expectedNorm a ham ha ha0 haind hrc).2
  have hrowcol := centeredSampling_expectedRowColumnNorm_le
    hn hδm hδ hind hregime X
  have hc : 0 ≤ 2 * Real.sqrt (2 * Real.log (n + n)) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rw [show (∫ ω, HDP.matrixOpNorm
      (sampledMatrix δ X ω - (p : ℝ) • X) ∂μ) =
      ∫ ω, HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω) ∂μ by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [rectangularMatrixOfCoordinates_centeredSamplingCoordinates]]
  calc
    (∫ ω, HDP.matrixOpNorm (rectangularMatrixOfCoordinates a ω) ∂μ) ≤
        2 * Real.sqrt (2 * Real.log (n + n)) *
          ∫ ω, rectangularRowColumnL2Norm
            (rectangularMatrixOfCoordinates a ω) ∂μ := hup
    _ ≤ 2 * Real.sqrt (2 * Real.log (n + n)) *
        (4 * HDP.Chapter4.maxAbsEntry X *
          Real.sqrt (n * (p : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hc
      calc
        (∫ ω, rectangularRowColumnL2Norm
            (rectangularMatrixOfCoordinates a ω) ∂μ) =
            ∫ ω, rectangularRowColumnL2Norm
              (sampledMatrix δ X ω - (p : ℝ) • X) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [show rectangularMatrixOfCoordinates a ω =
              sampledMatrix δ X ω - (p : ℝ) • X by
            simpa only [a] using
              rectangularMatrixOfCoordinates_centeredSamplingCoordinates
                δ X p ω]
        _ ≤ 4 * HDP.Chapter4.maxAbsEntry X *
            Real.sqrt (n * (p : ℝ)) := hrowcol
    _ = 8 * Real.sqrt (2 * Real.log (n + n)) *
        HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ)) := by ring

/-- Scaling identity used in the proof of the corresponding theorem.

**Lean implementation helper.** -/
theorem scaledSample_proxyError {m n : ℕ}
    (Y X : Matrix (Fin m) (Fin n) ℝ) {p : ℝ} (hp : 0 < p) :
    HDP.matrixOpNorm (p⁻¹ • Y - X) =
      p⁻¹ * HDP.matrixOpNorm (Y - p • X) := by
  have hmat : p⁻¹ • Y - X = p⁻¹ • (Y - p • X) := by
    ext i j
    simp
    field_simp
  rw [hmat, HDP.matrixOpNorm_smul, abs_of_pos (inv_pos.mpr hp)]

/-! ## Expected recovery and source-facing wrappers -/

/-- Expected rectangular recovery from an expected operator-norm proxy bound. All integrability
assumptions are explicit, so the theorem is safe for potentially unbounded observation models.

**Lean implementation helper.** -/
theorem integral_frobeniusError_le_of_proxyError {m n r : ℕ}
    {X : Matrix (Fin m) (Fin n) ℝ}
    {Xhat Z : Ω → Matrix (Fin m) (Fin n) ℝ}
    (hXhatRank : ∀ ω, HDP.matrixRank (Xhat ω) ≤ r)
    (hXRank : HDP.matrixRank X ≤ r)
    (hbest : ∀ ω, IsBestAgainst (Xhat ω) X (Z ω))
    (hfrob : Integrable (fun ω => HDP.matrixFrobeniusNorm (Xhat ω - X)) μ)
    (hop : Integrable (fun ω => HDP.matrixOpNorm (Z ω - X)) μ) :
    (∫ ω, HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
      2 * Real.sqrt (↑(2 * r) : ℝ) *
        ∫ ω, HDP.matrixOpNorm (Z ω - X) ∂μ := by
  let c : ℝ := 2 * Real.sqrt (↑(2 * r) : ℝ)
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hcop : Integrable (fun ω => c * HDP.matrixOpNorm (Z ω - X)) μ :=
    hop.const_mul c
  calc
    (∫ ω, HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
        ∫ ω, c * HDP.matrixOpNorm (Z ω - X) ∂μ := by
      apply integral_mono hfrob hcop
      intro ω
      simpa [c] using frobeniusError_le_of_bestRank
        (hXhatRank ω) hXRank (hbest ω)
    _ = c * ∫ ω, HDP.matrixOpNorm (Z ω - X) ∂μ := by
      rw [integral_const_mul]
    _ = 2 * Real.sqrt (↑(2 * r) : ℝ) *
        ∫ ω, HDP.matrixOpNorm (Z ω - X) ∂μ := rfl

/-- Once the centered sampling matrix satisfies the displayed expected operator bound `D`,
spectral truncation yields the stated expected Frobenius error. This is the exact load-bearing
conclusion of the source proof; the separate rectangular random matrix theorem supplies `D`.

**Book Theorem 6.5.1.** -/
theorem matrixCompletion_of_centered_operator_bound [IsProbabilityMeasure μ]
    {n r : ℕ} {p D : ℝ} (hp : 0 < p)
    {X : Matrix (Fin n) (Fin n) ℝ}
    {Y Xhat : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hXrank : HDP.matrixRank X ≤ r)
    (hXhatRank : ∀ ω, HDP.matrixRank (Xhat ω) ≤ r)
    (hbest : ∀ ω, IsBestAgainst (Xhat ω) X (p⁻¹ • Y ω))
    (hfrob : Integrable (fun ω => HDP.matrixFrobeniusNorm (Xhat ω - X)) μ)
    (hcentered : Integrable
      (fun ω => HDP.matrixOpNorm (Y ω - p • X)) μ)
    (hD : (∫ ω, HDP.matrixOpNorm (Y ω - p • X) ∂μ) ≤ D) :
    (∫ ω, HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
      2 * Real.sqrt (↑(2 * r) : ℝ) * p⁻¹ * D := by
  let Z : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => p⁻¹ • Y ω
  have hproxyPoint (ω : Ω) : HDP.matrixOpNorm (Z ω - X) =
      p⁻¹ * HDP.matrixOpNorm (Y ω - p • X) :=
    scaledSample_proxyError (Y ω) X hp
  have hproxy : Integrable (fun ω => HDP.matrixOpNorm (Z ω - X)) μ := by
    have h := hcentered.const_mul p⁻¹
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      exact (hproxyPoint ω).symm)
  have htransfer := integral_frobeniusError_le_of_proxyError
    (X := X) (Xhat := Xhat) (Z := Z) hXhatRank hXrank hbest hfrob hproxy
  have hproxyIntegral : (∫ ω, HDP.matrixOpNorm (Z ω - X) ∂μ) =
      p⁻¹ * ∫ ω, HDP.matrixOpNorm (Y ω - p • X) ∂μ := by
    simp_rw [hproxyPoint]
    rw [integral_const_mul]
  rw [hproxyIntegral] at htransfer
  calc
    (∫ ω, HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
        2 * Real.sqrt (↑(2 * r) : ℝ) *
          (p⁻¹ * ∫ ω, HDP.matrixOpNorm (Y ω - p • X) ∂μ) := htransfer
    _ ≤ 2 * Real.sqrt (↑(2 * r) : ℝ) * (p⁻¹ * D) := by
      gcongr
    _ = 2 * Real.sqrt (↑(2 * r) : ℝ) * p⁻¹ * D := by ring

/-- Let `Yᵢⱼ = δᵢⱼ Xᵢⱼ`, where all selectors are independent `Bernoulli(p)`, and assume `pn ≥
log n`. Any measurable rank-`r` candidate which is at least as good as `X` for the scaled proxy
`p⁻¹Y` obeys the displayed expected Frobenius-error bound. The constant is explicit; there is no
separate concentration hypothesis or abstract deviation parameter. The formula remains valid in
the degenerate branches `r = 0` and `X = 0`. The assumptions `2 ≤ n` and `0 < p` are precisely
what make the sampling scale and logarithmic regime nondegenerate.

**Book Theorem 6.5.1.** -/
theorem matrixCompletion_bernoulli [IsProbabilityMeasure μ]
    {n r : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {p : I} (hp : 0 < (p : ℝ))
    {δ : Fin n → Fin n → Ω → ℝ}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hind : iIndepFun (fun ij : Fin n × Fin n => δ ij.1 ij.2) μ)
    (hregime : Real.log n ≤ n * (p : ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hXrank : HDP.matrixRank X ≤ r)
    (Xhat : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hXhatm : ∀ i j, Measurable (fun ω => Xhat ω i j))
    (hXhatRank : ∀ ω, HDP.matrixRank (Xhat ω) ≤ r)
    (hbest : ∀ ω, IsBestAgainst (Xhat ω) X
      ((p : ℝ)⁻¹ • sampledMatrix δ X ω)) :
    (∫ ω, HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
      16 * Real.sqrt (↑(2 * r) : ℝ) * (p : ℝ)⁻¹ *
        Real.sqrt (2 * Real.log (n + n)) *
        HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ)) := by
  let Y : Ω → Matrix (Fin n) (Fin n) ℝ := sampledMatrix δ X
  let Z : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => (p : ℝ)⁻¹ • Y ω
  let D : ℝ := 8 * Real.sqrt (2 * Real.log (n + n)) *
    HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ))
  have ha : ∀ ij, Integrable (centeredSamplingCoordinates δ X p ij) μ :=
    fun ij => centeredSamplingCoordinates_integrable X p hδ ij
  have hcentered : Integrable
      (fun ω => HDP.matrixOpNorm (Y ω - (p : ℝ) • X)) μ := by
    have h := rectangularMatrixOpNorm_integrable_of_coordinates ha
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      change HDP.matrixOpNorm
        (rectangularMatrixOfCoordinates (centeredSamplingCoordinates δ X p) ω) = _
      rw [rectangularMatrixOfCoordinates_centeredSamplingCoordinates])
  have hD : (∫ ω, HDP.matrixOpNorm (Y ω - (p : ℝ) • X) ∂μ) ≤ D := by
    simpa only [Y, D] using
      centeredSampling_expectedOperatorNorm_le hn hδm hδ hind hregime X
  have hproxy : Integrable (fun ω => HDP.matrixOpNorm (Z ω - X)) μ := by
    have h := hcentered.const_mul (p : ℝ)⁻¹
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      exact (scaledSample_proxyError (Y ω) X hp).symm)
  have hfrobm : Measurable
      (fun ω => HDP.matrixFrobeniusNorm (Xhat ω - X)) := by
    unfold HDP.matrixFrobeniusNorm
    apply Real.continuous_sqrt.measurable.comp
    apply Finset.measurable_sum Finset.univ
    intro i _
    apply Finset.measurable_sum Finset.univ
    intro j _
    simpa only [Matrix.sub_apply] using
      ((hXhatm i j).sub_const (X i j)).pow_const 2
  have hfrob : Integrable
      (fun ω => HDP.matrixFrobeniusNorm (Xhat ω - X)) μ := by
    let c : ℝ := 2 * Real.sqrt (↑(2 * r) : ℝ)
    have hdom : Integrable (fun ω => c * HDP.matrixOpNorm (Z ω - X)) μ :=
      hproxy.const_mul c
    refine hdom.mono' hfrobm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (HDP.matrixFrobeniusNorm_nonneg _)]
    simpa only [c, Z, Y] using
      frobeniusError_le_of_bestRank (hXhatRank ω) hXrank (hbest ω)
  have hmain := matrixCompletion_of_centered_operator_bound
    (p := (p : ℝ)) (D := D) hp (X := X) (Y := Y) (Xhat := Xhat)
    hXrank hXhatRank (by simpa only [Y] using hbest) hfrob hcentered hD
  calc
    (∫ ω, HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
        2 * Real.sqrt (↑(2 * r) : ℝ) * (p : ℝ)⁻¹ * D := hmain
    _ = 16 * Real.sqrt (↑(2 * r) : ℝ) * (p : ℝ)⁻¹ *
        Real.sqrt (2 * Real.log (n + n)) *
        HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ)) := by
      simp only [D]
      ring

/-- Source-normalized form of the corresponding theorem. Dividing by `n` displays the per-row
Frobenius error; the right side is the explicit-constant version of the source's `C √(r log n
/(pn)) ‖X‖∞` rate.

**Book Theorem 6.5.1.** -/
theorem matrixCompletion_bernoulli_normalized [IsProbabilityMeasure μ]
    {n r : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {p : I} (hp : 0 < (p : ℝ))
    {δ : Fin n → Fin n → Ω → ℝ}
    (hδm : ∀ i j, Measurable (δ i j))
    (hδ : ∀ i j, HDP.IsBernoulli (δ i j) p μ)
    (hind : iIndepFun (fun ij : Fin n × Fin n => δ ij.1 ij.2) μ)
    (hregime : Real.log n ≤ n * (p : ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hXrank : HDP.matrixRank X ≤ r)
    (Xhat : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hXhatm : ∀ i j, Measurable (fun ω => Xhat ω i j))
    (hXhatRank : ∀ ω, HDP.matrixRank (Xhat ω) ≤ r)
    (hbest : ∀ ω, IsBestAgainst (Xhat ω) X
      ((p : ℝ)⁻¹ • sampledMatrix δ X ω)) :
    (∫ ω, (n : ℝ)⁻¹ * HDP.matrixFrobeniusNorm (Xhat ω - X) ∂μ) ≤
      (n : ℝ)⁻¹ *
        (16 * Real.sqrt (↑(2 * r) : ℝ) * (p : ℝ)⁻¹ *
          Real.sqrt (2 * Real.log (n + n)) *
          HDP.Chapter4.maxAbsEntry X * Real.sqrt (n * (p : ℝ))) := by
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (matrixCompletion_bernoulli hn hp hδm hδ hind hregime X hXrank
      Xhat hXhatm hXhatRank hbest)
    (inv_nonneg.mpr (Nat.cast_nonneg n))

/-- Canonical source-number alias for the complete Bernoulli statement. -/
alias theorem_6_5_1 := matrixCompletion_bernoulli_normalized

/-- This packages the fully proved deterministic rectangular result under an operator-deviation
bound `D`.

**Book Remark 6.5.2.** -/
theorem exercise_6_31_rectangular_matrix_completion {m n r : ℕ}
    {Xhat X Z : Matrix (Fin m) (Fin n) ℝ}
    (hXhatRank : HDP.matrixRank Xhat ≤ r)
    (hXRank : HDP.matrixRank X ≤ r)
    (hbest : IsBestAgainst Xhat X Z)
    {D : ℝ} (hD : HDP.matrixOpNorm (Z - X) ≤ D) :
    HDP.matrixFrobeniusNorm (Xhat - X) ≤
      2 * Real.sqrt (↑(2 * r) : ℝ) * D := by
  exact (frobeniusError_le_of_bestRank hXhatRank hXRank hbest).trans
    (mul_le_mul_of_nonneg_left hD
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- If the proxy splits into a sampling proxy plus an additive noise matrix, their operator
errors add.

**Book Remark 6.5.2.** -/
theorem exercise_6_32_noisy_matrix_completion {m n r : ℕ}
    {Xhat X Z Noise : Matrix (Fin m) (Fin n) ℝ}
    (hXhatRank : HDP.matrixRank Xhat ≤ r)
    (hXRank : HDP.matrixRank X ≤ r)
    (hbest : IsBestAgainst Xhat X (Z + Noise))
    {D N : ℝ} (hD : HDP.matrixOpNorm (Z - X) ≤ D)
    (hN : HDP.matrixOpNorm Noise ≤ N) :
    HDP.matrixFrobeniusNorm (Xhat - X) ≤
      2 * Real.sqrt (↑(2 * r) : ℝ) * (D + N) := by
  apply exercise_6_31_rectangular_matrix_completion
    hXhatRank hXRank hbest
  have hdecomp : Z + Noise - X = (Z - X) + Noise := by abel
  rw [hdecomp]
  exact (HDP.matrixOpNorm_add_le (Z - X) Noise).trans (add_le_add hD hN)

end HDP.Chapter6

end Source_11_MatrixCompletion

/-! ## Material formerly in `12_UnboundedMatrixExtensions.lean` -/

section Source_12_UnboundedMatrixExtensions

/-!
# Chapter 6: unbounded matrix extensions

This source-ordered helper module contains the load-bearing content of
Exercises 6.33 and 6.34.  In contrast to Chapter 5's bounded matrix Bernstein
theorem, all tail information here is encoded by the finite expectation of the
largest summand norm.
-/

open Matrix WithLp MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder
  ComplexOrder RealInnerProductSpace

namespace HDP.Chapter6

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The authoritative L2-operator-norm matrix space is continuously linearly equivalent to
continuous operators on Euclidean space. This bridge lets the generic Banach-valued
symmetrization theorem avoid the matrix type's separate entrywise measurable-space instance.

**Lean implementation helper.** -/
noncomputable def matrixOperatorEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

/-- The matrix-to-operator equivalence sends a matrix to its Euclidean linear operator.

**Lean implementation helper.** -/
@[simp] lemma matrixOperatorEquiv_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixOperatorEquiv n A = HDP.matrixOperator A := rfl

/-- The norm of a matrix viewed as a linear operator equals its matrix operator norm.

**Lean implementation helper.** -/
lemma matrixOperatorEquiv_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖matrixOperatorEquiv n A‖ = HDP.matrixOpNorm A := rfl

/-! ## Rank-one matrices and the corrected iid-copy maximum -/

/-- The Chapter 4 covariance outer product is the source-neutral outer matrix used by the matrix
norm API.

**Lean implementation helper.** -/
lemma outerProductMatrix_eq_outerMatrix {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    HDP.Chapter4.outerProductMatrix x = HDP.Chapter4.outerMatrix x x := rfl

/-- Every real rank-one covariance matrix is positive semidefinite.

**Lean implementation helper.** -/
lemma outerProductMatrix_posSemidef {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    (HDP.Chapter4.outerProductMatrix x).PosSemidef := by
  rw [outerProductMatrix_eq_outerMatrix]
  exact Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp x)

/-- The operator norm of `x xᵀ` is exactly `‖x‖²`.

**Lean implementation helper.** -/
lemma matrixOpNorm_outerProductMatrix {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    HDP.matrixOpNorm (HDP.Chapter4.outerProductMatrix x) = ‖x‖ ^ 2 := by
  rw [outerProductMatrix_eq_outerMatrix,
    (HDP.Chapter4.exercise_4_3a_outer_norms x x).1]
  ring

/-- The trace of `x xᵀ` is exactly its Euclidean energy.

**Lean implementation helper.** -/
lemma trace_outerProductMatrix {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    (HDP.Chapter4.outerProductMatrix x).trace = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.trace, Matrix.diag, HDP.Chapter4.outerProductMatrix]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Measurability of the rank-one covariance map.

**Lean implementation helper.** -/
lemma measurable_outerProductMatrix {n : ℕ} :
    Measurable (HDP.Chapter4.outerProductMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hi : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.ofLp x) i) :=
    (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)
  have hj : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.ofLp x) j) :=
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  exact hi.mul hj

/-- Integrable vector energy is exactly what is needed for Bochner integrability of the rank-one
covariance matrix.

**Lean implementation helper.** -/
lemma integrable_outerProductMatrix {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : Measurable X)
    (henergy : Integrable (fun ω => ‖X ω‖ ^ 2) μ) :
    Integrable (fun ω => HDP.Chapter4.outerProductMatrix (X ω)) μ := by
  refine henergy.mono'
    (measurable_outerProductMatrix.comp hXm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  change HDP.matrixOpNorm (HDP.Chapter4.outerProductMatrix (X ω)) ≤ ‖X ω‖ ^ 2
  exact (matrixOpNorm_outerProductMatrix (X ω)).le

/-- The maximum in the corrected exercise ranges over the actual iid copies, not
over the unindexed base variable in the printed statement.

**Lean implementation helper.** -/
noncomputable def maxSampleEnergy {m n : ℕ} [Nonempty (Fin m)]
    (Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ‖Xs i ω‖ ^ 2)

/-- Shows that max sample energy is nonnegative.

**Lean implementation helper.** -/
lemma maxSampleEnergy_nonneg {m n : ℕ} [Nonempty (Fin m)]
    (Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    0 ≤ maxSampleEnergy Xs ω := by
  let i : Fin m := Classical.choice inferInstance
  exact (sq_nonneg ‖Xs i ω‖).trans (by
    simpa [maxSampleEnergy] using
      (Finset.le_sup' (fun k => ‖Xs k ω‖ ^ 2) (Finset.mem_univ i)))

/-- Bounds sample energy by max sample energy.

**Lean implementation helper.** -/
lemma sampleEnergy_le_maxSampleEnergy {m n : ℕ} [Nonempty (Fin m)]
    (Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (i : Fin m) (ω : Ω) :
    ‖Xs i ω‖ ^ 2 ≤ maxSampleEnergy Xs ω := by
  simpa [maxSampleEnergy] using
    (Finset.le_sup' (fun k => ‖Xs k ω‖ ^ 2) (Finset.mem_univ i))

/-- Shows that max sample energy is measurable.

**Lean implementation helper.** -/
lemma maxSampleEnergy_measurable {m n : ℕ} [Nonempty (Fin m)]
    {Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (Xs i)) : Measurable (maxSampleEnergy Xs) := by
  have h : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin m))
      (fun i ω => ‖Xs i ω‖ ^ 2)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ =>
      ((hXm i).norm.pow_const 2)
  have heq : (Finset.univ.sup' (Finset.univ_nonempty (α := Fin m))
      (fun i ω => ‖Xs i ω‖ ^ 2)) = maxSampleEnergy Xs := by
    funext ω
    simp only [Finset.sup'_apply]
    rfl
  rwa [heq] at h

/-- Trace commutes with the Bochner expectation of an integrable rank-one matrix, giving the
source identity `tr Σ = E ‖X‖²` without boundedness.

**Lean implementation helper.** -/
lemma trace_integral_outerProductMatrix {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : Measurable X)
    (henergy : Integrable (fun ω => ‖X ω‖ ^ 2) μ) :
    (∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ).trace =
      ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  let T : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap
  have houter := integrable_outerProductMatrix hXm henergy
  have hcomm := T.integral_comp_comm houter
  change (∫ ω, T (HDP.Chapter4.outerProductMatrix (X ω)) ∂μ) =
      T (∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ) at hcomm
  change T (∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ) =
    ∫ ω, ‖X ω‖ ^ 2 ∂μ
  rw [← hcomm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => trace_outerProductMatrix (X ω)

/-- The normalized sum of rank-one outer products is the existing Chapter 4 sample-second-moment
estimator.

**Lean implementation helper.** -/
lemma sum_scaled_outerProductMatrix_eq_sampleCovarianceMatrix {m n : ℕ}
    (X : Fin m → EuclideanSpace ℝ (Fin n)) :
    (∑ i, (m : ℝ)⁻¹ • HDP.Chapter4.outerProductMatrix (X i)) =
      HDP.Chapter4.sampleCovarianceMatrix X := by
  ext j k
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul,
    HDP.Chapter4.sampleCovarianceMatrix_apply,
    HDP.Chapter4.outerProductMatrix]
  rw [Finset.mul_sum]

/-- The sample second moment of identically distributed copies is unbiased as a Bochner
integral. No boundedness assumption is used.

**Lean implementation helper.** -/
lemma integral_sampleCovarianceMatrix_eq
    [IsProbabilityMeasure μ] {m n : ℕ} (hm : 0 < m)
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    {Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : Measurable X)
    (henergy : Integrable (fun ω => ‖X ω‖ ^ 2) μ)
    (hid : ∀ i, IdentDistrib (Xs i) X μ μ) :
    (∫ ω, HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) ∂μ) =
      ∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ := by
  let O : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    HDP.Chapter4.outerProductMatrix
  have hOX : Integrable (fun ω => O (X ω)) μ :=
    integrable_outerProductMatrix hXm henergy
  have hidO (i : Fin m) : IdentDistrib (fun ω => O (Xs i ω))
      (fun ω => O (X ω)) μ μ := by
    simpa [Function.comp_def, O] using
      (hid i).comp measurable_outerProductMatrix
  have hOXs (i : Fin m) : Integrable (fun ω => O (Xs i ω)) μ :=
    ((hidO i).integrable_iff).2 hOX
  have hZi (i : Fin m) : Integrable
      (fun ω => (m : ℝ)⁻¹ • O (Xs i ω)) μ :=
    Integrable.smul (m : ℝ)⁻¹ (hOXs i)
  calc
    (∫ ω, HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) ∂μ) =
        ∫ ω, ∑ i, (m : ℝ)⁻¹ • O (Xs i ω) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω =>
            (sum_scaled_outerProductMatrix_eq_sampleCovarianceMatrix _).symm
    _ = ∑ i, ∫ ω, (m : ℝ)⁻¹ • O (Xs i ω) ∂μ :=
      integral_finsetSum Finset.univ fun i _ => hZi i
    _ = ∑ i, (m : ℝ)⁻¹ • ∫ ω, O (Xs i ω) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_smul]
    _ = ∑ _i : Fin m, (m : ℝ)⁻¹ • ∫ ω, O (X ω) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hidO i).integral_eq]
    _ = ∫ ω, O (X ω) ∂μ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [mul_inv_cancel₀ hmR, one_smul]

/-! ## A canonical finite Rademacher product space -/

/-- Product sample space for the auxiliary Rademacher signs. -/
abbrev MatrixSignSample (N : ℕ) := Fin N → ℝ

/-- Independent canonical Rademacher coordinates.

**Lean implementation helper.** -/
noncomputable def matrixSignMeasure (N : ℕ) : Measure (MatrixSignSample N) :=
  Measure.pi fun _ : Fin N => MatrixConcentration.rademacherMeasure

noncomputable instance matrixSignMeasure_isProbabilityMeasure (N : ℕ) :
    IsProbabilityMeasure (matrixSignMeasure N) := by
  rw [matrixSignMeasure]
  infer_instance

/-- The `i`th canonical sign coordinate.

**Lean implementation helper.** -/
def matrixSignCoordinate {N : ℕ} (i : Fin N) : MatrixSignSample N → ℝ :=
  fun ε => ε i

/-- Shows that matrix sign coordinate is measurable.

**Lean implementation helper.** -/
lemma matrixSignCoordinate_measurable {N : ℕ} (i : Fin N) :
    Measurable (matrixSignCoordinate i) := measurable_pi_apply i

/-- Each coordinate projection on the matrix sign cube is a Rademacher random variable.

**Lean implementation helper.** -/
lemma matrixSignCoordinate_isRademacher {N : ℕ} (i : Fin N) :
    MatrixConcentration.IsRademacher (matrixSignCoordinate i)
      (matrixSignMeasure N) := by
  rw [MatrixConcentration.IsRademacher]
  exact (MeasureTheory.measurePreserving_eval
    (fun _ : Fin N => MatrixConcentration.rademacherMeasure) i).map_eq

/-- Compatibility with the source-wide Rademacher predicate. The frozen matrix library and the
source use definitionally different but equal two-point measures.

**Lean implementation helper.** -/
lemma matrixSignCoordinate_isRademacherHDP {N : ℕ} (i : Fin N) :
    HDP.IsRademacher (matrixSignCoordinate i) (matrixSignMeasure N) := by
  refine ⟨(matrixSignCoordinate_measurable i).aemeasurable, ?_⟩
  rw [matrixSignCoordinate_isRademacher i]
  rw [MatrixConcentration.rademacherMeasure, bernoulliMeasure_def]
  have h₁ : (2⁻¹ : ENNReal) =
      unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ := by
    calc
      (2⁻¹ : ENNReal) = ↑((2 : NNReal)⁻¹) :=
        (ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0)).symm
      _ = ↑(unitInterval.toNNReal
          ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) := by
        apply congrArg ENNReal.ofNNReal
        ext
        norm_num
  have hsymmHalf :
      unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ =
        unitInterval.toNNReal
          (unitInterval.symm
            ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) := by
    ext
    norm_num
  rw [h₁, hsymmHalf]
  simp only [Measure.coe_nnreal_smul]

/-- Shows that matrix sign coordinate is independent.

**Lean implementation helper.** -/
lemma matrixSignCoordinate_independent {N : ℕ} :
    iIndepFun (fun i : Fin N => matrixSignCoordinate i)
      (matrixSignMeasure N) := by
  exact iIndepFun_pi (X := fun _ : Fin N => id)
    (fun _ => measurable_id.aemeasurable)

/-! ## Maximum summand and square-function helpers -/

/-- Actual maximum operator norm of a nonempty finite matrix family.

**Lean implementation helper.** -/
noncomputable def maxMatrixSummandNorm {N n : ℕ} [Nonempty (Fin N)]
    (Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => HDP.matrixOpNorm (Z i ω))

/-- Shows that max matrix summand norm is nonnegative.

**Lean implementation helper.** -/
lemma maxMatrixSummandNorm_nonneg {N n : ℕ} [Nonempty (Fin N)]
    (Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    0 ≤ maxMatrixSummandNorm Z ω := by
  let i : Fin N := Classical.choice inferInstance
  exact (HDP.matrixOpNorm_nonneg (Z i ω)).trans (by
    simpa [maxMatrixSummandNorm] using
      (Finset.le_sup' (fun k => HDP.matrixOpNorm (Z k ω))
        (Finset.mem_univ i)))

/-- Bounds matrix operator norm by max matrix summand norm.

**Lean implementation helper.** -/
lemma matrixOpNorm_le_maxMatrixSummandNorm {N n : ℕ} [Nonempty (Fin N)]
    (Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ) (i : Fin N) (ω : Ω) :
    HDP.matrixOpNorm (Z i ω) ≤ maxMatrixSummandNorm Z ω := by
  simpa [maxMatrixSummandNorm] using
    (Finset.le_sup' (fun k => HDP.matrixOpNorm (Z k ω))
      (Finset.mem_univ i))

/-- Shows that max matrix summand norm is measurable.

**Lean implementation helper.** -/
private lemma maxMatrixSummandNorm_measurable {N n : ℕ} [Nonempty (Fin N)]
    {Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ}
    (hZm : ∀ i, Measurable (Z i)) : Measurable (maxMatrixSummandNorm Z) := by
  have h1 : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin N))
      (fun i ω => HDP.matrixOpNorm (Z i ω))) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ =>
      continuous_norm.measurable.comp (hZm i)
  have heq : (Finset.univ.sup' (Finset.univ_nonempty (α := Fin N))
      (fun i ω => HDP.matrixOpNorm (Z i ω))) = maxMatrixSummandNorm Z := by
    funext ω
    simp only [Finset.sup'_apply]
    rfl
  rwa [heq] at h1

/-- Finite expected maximum implies integrability of every summand norm.

**Lean implementation helper.** -/
lemma summandNorm_integrable_of_max {N n : ℕ} [Nonempty (Fin N)]
    {Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ}
    (hZm : ∀ i, Measurable (Z i))
    (hmax : Integrable (maxMatrixSummandNorm Z) μ) (i : Fin N) :
    Integrable (fun ω => HDP.matrixOpNorm (Z i ω)) μ := by
  refine hmax.mono'
    (continuous_norm.measurable.comp (hZm i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (HDP.matrixOpNorm_nonneg _)]
  exact matrixOpNorm_le_maxMatrixSummandNorm Z i ω

/-- Finite expected maximum also gives Bochner integrability of every matrix summand. This is
the form needed by symmetrization.

**Lean implementation helper.** -/
lemma summand_integrable_of_max {N n : ℕ} [Nonempty (Fin N)]
    {Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ}
    (hZm : ∀ i, Measurable (Z i))
    (hmax : Integrable (maxMatrixSummandNorm Z) μ) (i : Fin N) :
    Integrable (Z i) μ := by
  refine hmax.mono' (hZm i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  exact matrixOpNorm_le_maxMatrixSummandNorm Z i ω

/-- Consequently the matrix-valued finite sum is Bochner integrable.

**Lean implementation helper.** -/
lemma matrixSum_integrable_of_max {N n : ℕ} [Nonempty (Fin N)]
    {Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ}
    (hZm : ∀ i, Measurable (Z i))
    (hmax : Integrable (maxMatrixSummandNorm Z) μ) :
    Integrable (fun ω => ∑ i, Z i ω) μ := by
  exact integrable_finsetSum _ fun i _ => summand_integrable_of_max hZm hmax i

/-- Consequently the norm of the finite sum is integrable.

**Lean implementation helper.** -/
lemma matrixSumNorm_integrable_of_max {N n : ℕ} [Nonempty (Fin N)]
    {Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ}
    (hZm : ∀ i, Measurable (Z i))
    (hmax : Integrable (maxMatrixSummandNorm Z) μ) :
    Integrable (fun ω => HDP.matrixOpNorm (∑ i, Z i ω)) μ := by
  have hsum : Integrable (fun ω => ∑ i, HDP.matrixOpNorm (Z i ω)) μ :=
    integrable_finsetSum _ fun i _ => summandNorm_integrable_of_max hZm hmax i
  refine hsum.mono'
    (continuous_norm.measurable.comp
      (Finset.measurable_sum _ fun i _ => hZm i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (HDP.matrixOpNorm_nonneg _)]
  exact norm_sum_le _ _

/-- Identifies complex psd squared with cfc.

**Lean implementation helper.** -/
private lemma complex_psd_sq_eq_cfc [Nonempty (Fin n)]
    {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.IsHermitian) : P * P = cfc (fun x : ℝ => x * x) P := by
  rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) P,
    cfc_id' ℝ P]

/-- Local real-bridge ingredient: `P² ≤ ‖P‖P` for a complex PSD matrix.

**Lean implementation helper.** -/
private lemma complex_psd_sq_le_norm_smul [Nonempty (Fin n)]
    {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosSemidef) : P * P ≤ ‖P‖ • P := by
  rw [complex_psd_sq_eq_cfc hP.1,
    MatrixConcentration.smul_eq_cfc hP.1 ‖P‖]
  refine MatrixConcentration.transfer_rule hP.1
    (I := Set.Icc 0 ‖P‖) (fun i => ?_) fun a ha => ?_
  · refine ⟨hP.eigenvalues_nonneg i, ?_⟩
    exact (MatrixConcentration.eigenvalues_le_lambdaMax hP.1 i).trans
      ((le_abs_self _).trans (MatrixConcentration.abs_lambdaMax_le hP.1))
  · nlinarith [ha.1, ha.2]

/-- Pointwise square-function estimate for a finite real PSD family.

**Lean implementation helper.** -/
lemma norm_sum_sq_le_max_mul_norm_sum {N n : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin n)]
    (A : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).PosSemidef) :
    HDP.matrixOpNorm (∑ i, (A i) ^ 2) ≤
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i => HDP.matrixOpNorm (A i))) *
        HDP.matrixOpNorm (∑ i, A i) := by
  let C : Fin N → Matrix (Fin n) (Fin n) ℂ := fun i => HDP.complexifyMatrix (A i)
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun i => HDP.matrixOpNorm (A i))
  have hC : ∀ i, (C i).PosSemidef := fun i => HDP.complexifyMatrix_posSemidef (hA i)
  have hM0 : 0 ≤ M := by
    let i : Fin N := Classical.choice inferInstance
    have hle : HDP.matrixOpNorm (A i) ≤ M := by
      change HDP.matrixOpNorm (A i) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun k => HDP.matrixOpNorm (A k))
      exact Finset.le_sup'
        (fun k : Fin N => HDP.matrixOpNorm (A k)) (Finset.mem_univ i)
    exact (HDP.matrixOpNorm_nonneg (A i)).trans hle
  have hiNorm (i : Fin N) : ‖C i‖ ≤ M := by
    change ‖HDP.complexifyMatrix (A i)‖ ≤ M
    rw [HDP.complexifyMatrix_opNorm]
    change HDP.matrixOpNorm (A i) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun k => HDP.matrixOpNorm (A k))
    exact Finset.le_sup'
      (fun k : Fin N => HDP.matrixOpNorm (A k)) (Finset.mem_univ i)
  have hiSq (i : Fin N) : (C i) ^ 2 ≤ M • C i := by
    rw [pow_two]
    exact (complex_psd_sq_le_norm_smul (hC i)).trans (by
      rw [Matrix.le_iff, ← sub_smul]
      exact (hC i).smul (sub_nonneg.mpr (hiNorm i)))
  have hsumSqPsd : (∑ i, (C i) ^ 2).PosSemidef :=
    MatrixConcentration.posSemidef_matsum Finset.univ fun i => by
      rw [pow_two]
      exact MatrixConcentration.posSemidef_sq (hC i).1
  have hsumPsd : (∑ i, C i).PosSemidef :=
    MatrixConcentration.posSemidef_matsum Finset.univ hC
  have hsumLe : (∑ i, (C i) ^ 2) ≤ M • ∑ i, C i := by
    rw [Finset.smul_sum]
    exact MatrixConcentration.sum_loewner_mono Finset.univ fun i _ => hiSq i
  have hrightPsd : (M • ∑ i, C i).PosSemidef := hsumPsd.smul hM0
  have hcomplex : ‖∑ i, (C i) ^ 2‖ ≤ M * ‖∑ i, C i‖ := by
    calc
      ‖∑ i, (C i) ^ 2‖ = MatrixConcentration.lambdaMax hsumSqPsd.1 :=
        MatrixConcentration.posSemidef_l2_opNorm_eq_lambdaMax hsumSqPsd
      _ ≤ MatrixConcentration.lambdaMax hrightPsd.1 :=
        MatrixConcentration.lambdaMax_le_of_loewner_le
          hsumSqPsd.1 hrightPsd.1 hsumLe
      _ = M * MatrixConcentration.lambdaMax hsumPsd.1 :=
        MatrixConcentration.lambdaMax_smul_nonneg hsumPsd.1 hM0 hrightPsd.1
      _ = M * ‖∑ i, C i‖ := by
        rw [MatrixConcentration.posSemidef_l2_opNorm_eq_lambdaMax hsumPsd]
  have hsumC : (∑ i, C i) = HDP.complexifyMatrix (∑ i, A i) := by
    symm
    simp [C, HDP.complexifyMatrix_sum]
  have hsumSqC : (∑ i, (C i) ^ 2) =
      HDP.complexifyMatrix (∑ i, (A i) ^ 2) := by
    rw [HDP.complexifyMatrix_sum Finset.univ]
    apply Finset.sum_congr rfl
    intro i _
    simp [C, pow_two]
  rw [hsumC, hsumSqC, HDP.complexifyMatrix_opNorm,
    HDP.complexifyMatrix_opNorm] at hcomplex
  exact hcomplex

/-! ## Scalar integration and closing estimates -/

/-- Cauchy--Schwarz bounds the expectation of `sqrt (M Y)` by the geometric mean of the
expectations of nonnegative integrable `M` and `Y`.

**Lean implementation helper.** -/
private lemma integral_sqrt_mul_le {M Y : Ω → ℝ}
    (hM : Integrable M μ) (hY : Integrable Y μ)
    (hM0 : ∀ ω, 0 ≤ M ω) (hY0 : ∀ ω, 0 ≤ Y ω) :
    (∫ ω, Real.sqrt (M ω * Y ω) ∂μ) ≤
      Real.sqrt ((∫ ω, M ω ∂μ) * (∫ ω, Y ω ∂μ)) := by
  have hsM : AEStronglyMeasurable (fun ω => Real.sqrt (M ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hM.aestronglyMeasurable
  have hsY : AEStronglyMeasurable (fun ω => Real.sqrt (Y ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hY.aestronglyMeasurable
  have hsM2 : Integrable (fun ω => Real.sqrt (M ω) ^ 2) μ :=
    hM.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hM0 ω)).symm)
  have hsY2 : Integrable (fun ω => Real.sqrt (Y ω) ^ 2) μ :=
    hY.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hY0 ω)).symm)
  have hMLp : MemLp (fun ω => Real.sqrt (M ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hsM).2 hsM2
  have hYLp : MemLp (fun ω => Real.sqrt (Y ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hsY).2 hsY2
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (M ω))
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (Y ω))
    (by simpa using hMLp) (by simpa using hYLp)
  simp_rw [Real.rpow_two, Real.sq_sqrt (hM0 _), Real.sq_sqrt (hY0 _)] at hh
  calc
    (∫ ω, Real.sqrt (M ω * Y ω) ∂μ) =
        ∫ ω, Real.sqrt (M ω) * Real.sqrt (Y ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => Real.sqrt_mul (hM0 ω) (Y ω)
    _ ≤ (∫ ω, M ω ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ ω, Y ω ∂μ) ^ ((1 : ℝ) / 2) := hh
    _ = Real.sqrt (∫ ω, M ω ∂μ) * Real.sqrt (∫ ω, Y ω ∂μ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ = Real.sqrt ((∫ ω, M ω ∂μ) * (∫ ω, Y ω ∂μ)) := by
      rw [Real.sqrt_mul (integral_nonneg hM0)]

/-- Establishes integrability of sqrt mul.

**Lean implementation helper.** -/
private lemma integrable_sqrt_mul {M Y : Ω → ℝ}
    (hM : Integrable M μ) (hY : Integrable Y μ)
    (hM0 : ∀ ω, 0 ≤ M ω) (hY0 : ∀ ω, 0 ≤ Y ω) :
    Integrable (fun ω => Real.sqrt (M ω * Y ω)) μ := by
  refine (hM.add hY).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (hM.aestronglyMeasurable.mul hY.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg (hM0 ω) (hY0 ω)
  · change M ω * Y ω ≤ (M ω + Y ω) ^ 2
    nlinarith [hM0 ω, hY0 ω, sq_nonneg (M ω - Y ω)]

/-- Elementary quadratic closure for the unbounded matrix estimate.

**Lean implementation helper.** -/
lemma unbounded_matrix_scalar_closure {y a q : ℝ}
    (hy : 0 ≤ y) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (h : y ≤ 2 * Real.sqrt (q * (a + y))) :
    y ≤ 4 * Real.sqrt (q * a) + 8 * q := by
  have haq : 0 ≤ q * (a + y) := mul_nonneg hq (add_nonneg ha hy)
  have hsquare : y ^ 2 ≤ 4 * q * (a + y) := by
    have hs := (sq_le_sq₀ hy (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).2 h
    rw [mul_pow, Real.sq_sqrt haq] at hs
    nlinarith
  have ht0 : 0 ≤ Real.sqrt (q * a) := Real.sqrt_nonneg _
  have htSq : Real.sqrt (q * a) ^ 2 = q * a :=
    Real.sq_sqrt (mul_nonneg hq ha)
  by_contra hnot
  have hlarge : 4 * Real.sqrt (q * a) + 8 * q < y := lt_of_not_ge hnot
  nlinarith [sq_nonneg (y - 4 * q), sq_nonneg (y - 4 * Real.sqrt (q * a))]

/-! The following theorem isolates all algebra after symmetrization and matrix
Khintchine.  Its last hypothesis is precisely the analytic inequality supplied
by Lemma 6.3.2 followed pointwise by Theorem 5.4.14.  Keeping this boundary
explicit prevents a duplicate sign/product-space proof in this module. -/

/-- Algebraic closure of the unbounded positive-semidefinite matrix estimate. Here `log (2n)` is
the corrected, dimension-safe replacement for the printed `log n`. Once symmetrization and
matrix Khintchine give `hsymmKh`, the conclusion has completely explicit constants.

**Book Exercise 6.33.** -/
theorem unbounded_psd_sum_of_symmetrized_khintchine
    [IsProbabilityMeasure μ] {N n : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin n)]
    (Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hZm : ∀ i, Measurable (Z i))
    (hmax : Integrable (maxMatrixSummandNorm Z) μ)
    (hsymmKh :
      let S : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => ∑ i, Z i ω
      let y := ∫ ω, HDP.matrixOpNorm (S ω - ∫ ξ, S ξ ∂μ) ∂μ
      y ≤ 2 * ∫ ω, Real.sqrt
        ((2 * Real.log (2 * n)) * maxMatrixSummandNorm Z ω *
          HDP.matrixOpNorm (S ω)) ∂μ) :
    let S : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => ∑ i, Z i ω
    let y := ∫ ω, HDP.matrixOpNorm (S ω - ∫ ξ, S ξ ∂μ) ∂μ
    let a := HDP.matrixOpNorm (∫ ω, S ω ∂μ)
    let q := (2 * Real.log (2 * n)) *
      (∫ ω, maxMatrixSummandNorm Z ω ∂μ)
    y ≤ 4 * Real.sqrt (q * a) + 8 * q := by
  dsimp only
  let S : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => ∑ i, Z i ω
  let E : Matrix (Fin n) (Fin n) ℝ := ∫ ω, S ω ∂μ
  let y : ℝ := ∫ ω, HDP.matrixOpNorm (S ω - E) ∂μ
  let a : ℝ := HDP.matrixOpNorm E
  let c : ℝ := 2 * Real.log (2 * n)
  let b : ℝ := ∫ ω, maxMatrixSummandNorm Z ω ∂μ
  let q : ℝ := c * b
  have hn : (1 : ℝ) ≤ 2 * n := by
    have hnNat : 1 ≤ n := by
      have hnPos : 0 < n := by
        simpa using (Fintype.card_pos (α := Fin n))
      omega
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (Real.log_nonneg hn)
  have hb : 0 ≤ b := integral_nonneg fun ω => maxMatrixSummandNorm_nonneg Z ω
  have hq : 0 ≤ q := mul_nonneg hc hb
  have hS : Integrable S μ := matrixSum_integrable_of_max hZm hmax
  have hSnorm : Integrable (fun ω => HDP.matrixOpNorm (S ω)) μ := hS.norm
  have hcenter : Integrable (fun ω => S ω - E) μ :=
    hS.sub (integrable_const E)
  have hyInt : Integrable (fun ω => HDP.matrixOpNorm (S ω - E)) μ :=
    hcenter.norm
  have hy : 0 ≤ y := integral_nonneg fun _ => HDP.matrixOpNorm_nonneg _
  have ha : 0 ≤ a := HDP.matrixOpNorm_nonneg _
  have hEY : (∫ ω, HDP.matrixOpNorm (S ω) ∂μ) ≤ a + y := by
    have hpoint : ∀ ω, HDP.matrixOpNorm (S ω) ≤
        HDP.matrixOpNorm (S ω - E) + a := by
      intro ω
      have h := norm_add_le (S ω - E) E
      change ‖S ω‖ ≤ ‖S ω - E‖ + ‖E‖
      simpa only [sub_add_cancel] using h
    calc
      (∫ ω, HDP.matrixOpNorm (S ω) ∂μ) ≤
          ∫ ω, (HDP.matrixOpNorm (S ω - E) + a) ∂μ :=
        integral_mono hSnorm (hyInt.add (integrable_const a)) hpoint
      _ = y + a := by
        rw [integral_add hyInt (integrable_const a), integral_const,
          probReal_univ, one_smul]
      _ = a + y := add_comm _ _
  have hcM : Integrable (fun ω => c * maxMatrixSummandNorm Z ω) μ :=
    hmax.const_mul c
  have hsqrt := integral_sqrt_mul_le
    (μ := μ) hcM hSnorm
    (fun ω => mul_nonneg hc (maxMatrixSummandNorm_nonneg Z ω))
    (fun ω => HDP.matrixOpNorm_nonneg (S ω))
  have hcInt : (∫ ω, c * maxMatrixSummandNorm Z ω ∂μ) = q := by
    rw [integral_const_mul]
  have hrad : (∫ ω, Real.sqrt
      (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) ∂μ) ≤
      Real.sqrt (q * (a + y)) := by
    calc
      (∫ ω, Real.sqrt
          (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) ∂μ)
          ≤ Real.sqrt ((∫ ω, c * maxMatrixSummandNorm Z ω ∂μ) *
              (∫ ω, HDP.matrixOpNorm (S ω) ∂μ)) := hsqrt
      _ = Real.sqrt (q * (∫ ω, HDP.matrixOpNorm (S ω) ∂μ)) := by rw [hcInt]
      _ ≤ Real.sqrt (q * (a + y)) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hEY hq)
  have hclose : y ≤ 2 * Real.sqrt (q * (a + y)) := by
    calc
      y ≤ 2 * ∫ ω, Real.sqrt
          (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) ∂μ := by
        simpa [S, E, y, c] using hsymmKh
      _ ≤ 2 * Real.sqrt (q * (a + y)) :=
        mul_le_mul_of_nonneg_left hrad (by norm_num)
  have hfinal := unbounded_matrix_scalar_closure hy ha hq hclose
  simpa [S, E, y, a, c, b, q] using hfinal

/-- This is a fully explicit, dimension-safe version of the source claim. The printed `log n` is
replaced by `log (2n)`, so the theorem remains valid in dimension one.

**Book Exercise 6.33.** -/
theorem exercise_6_33
    [IsProbabilityMeasure μ] {N n : ℕ}
    [Nonempty (Fin N)] [Nonempty (Fin n)]
    (Z : Fin N → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hZm : ∀ i, Measurable (Z i))
    (hZpsd : ∀ i ω, (Z i ω).PosSemidef)
    (hind : iIndepFun Z μ)
    (hmax : Integrable (maxMatrixSummandNorm Z) μ) :
    let S : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => ∑ i, Z i ω
    let y := ∫ ω, HDP.matrixOpNorm (S ω - ∫ ξ, S ξ ∂μ) ∂μ
    let a := HDP.matrixOpNorm (∫ ω, S ω ∂μ)
    let q := (2 * Real.log (2 * n)) *
      (∫ ω, maxMatrixSummandNorm Z ω ∂μ)
    y ≤ 4 * Real.sqrt (q * a) + 8 * q := by
  let S : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => ∑ i, Z i ω
  let c : ℝ := 2 * Real.log (2 * n)
  let R : Ω → ℝ := fun ω =>
    ∫ ε, HDP.matrixOpNorm
      (∑ i, matrixSignCoordinate i ε • Z i ω) ∂matrixSignMeasure N
  have hZint : ∀ i, Integrable (Z i) μ :=
    fun i => summand_integrable_of_max hZm hmax i
  letI : MeasurableSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := borel _
  letI : BorelSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  let e := matrixOperatorEquiv n
  let Zop : Fin N → Ω →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun i ω => e (Z i ω)
  have hZopm : ∀ i, Measurable (Zop i) := fun i =>
    e.continuous.measurable.comp (hZm i)
  have hZopint : ∀ i, Integrable (Zop i) μ := fun i =>
    e.toContinuousLinearMap.integrable_comp (hZint i)
  have hZopind : iIndepFun Zop μ := by
    simpa [Zop, Function.comp_def] using
      hind.comp (fun _ => e) (fun _ => e.continuous.measurable)
  have hsignedMatrix : Integrable
      (fun z : Ω × MatrixSignSample N =>
        ∑ i, matrixSignCoordinate i z.2 • Z i z.1)
      (μ.prod (matrixSignMeasure N)) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    have hi : Integrable
        (fun z : MatrixSignSample N × Ω =>
          matrixSignCoordinate i z.1 • Z i z.2)
        ((matrixSignMeasure N).prod μ) :=
      (((matrixSignCoordinate_isRademacherHDP i).memLp 1).integrable le_rfl).smul_prod
        (hZint i)
    simpa [Function.comp_def] using hi.swap
  have hsignedNorm (z : Ω × MatrixSignSample N) :
      ‖∑ i, matrixSignCoordinate i z.2 • Zop i z.1‖ =
        HDP.matrixOpNorm
          (∑ i, matrixSignCoordinate i z.2 • Z i z.1) := by
    have heq : (∑ i, matrixSignCoordinate i z.2 • Zop i z.1) =
        e (∑ i, matrixSignCoordinate i z.2 • Z i z.1) := by
      symm
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [Zop]
    rw [heq]
    exact matrixOperatorEquiv_norm _
  have hRint : Integrable R μ := by
    exact hsignedMatrix.norm.integral_prod_left
  have hn : (1 : ℝ) ≤ 2 * n := by
    have hnPos : 0 < n := by
      simpa using (Fintype.card_pos (α := Fin n))
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (Real.log_nonneg hn)
  have hS : Integrable S μ := matrixSum_integrable_of_max hZm hmax
  have hSnorm : Integrable (fun ω => HDP.matrixOpNorm (S ω)) μ := hS.norm
  have hcM : Integrable (fun ω => c * maxMatrixSummandNorm Z ω) μ :=
    hmax.const_mul c
  have hrhsInt : Integrable (fun ω => Real.sqrt
      ((c * maxMatrixSummandNorm Z ω) * HDP.matrixOpNorm (S ω))) μ :=
    integrable_sqrt_mul hcM hSnorm
      (fun ω => mul_nonneg hc (maxMatrixSummandNorm_nonneg Z ω))
      (fun ω => HDP.matrixOpNorm_nonneg (S ω))
  have hpoint (ω : Ω) : R ω ≤ Real.sqrt
      (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) := by
    have hkh := HDP.Chapter5.matrixKhintchineOne
      (μ := matrixSignMeasure N) (fun i => Z i ω)
      (fun i => (hZpsd i ω).1)
      (fun i => matrixSignCoordinate_measurable i)
      (fun i => matrixSignCoordinate_isRademacher i)
      matrixSignCoordinate_independent
    have hsq := norm_sum_sq_le_max_mul_norm_sum
      (fun i => Z i ω) (fun i => hZpsd i ω)
    have hinside :
        2 * HDP.matrixOpNorm (∑ i, (Z i ω) ^ 2) *
            Real.log (2 * n) ≤
          c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω) := by
      have hlog : 0 ≤ Real.log (2 * n) := Real.log_nonneg hn
      have hM : (Finset.univ.sup' Finset.univ_nonempty
          (fun i => HDP.matrixOpNorm (Z i ω))) =
          maxMatrixSummandNorm Z ω := rfl
      rw [hM] at hsq
      dsimp only [c, S]
      nlinarith [HDP.matrixOpNorm_nonneg (∑ i, (Z i ω) ^ 2),
        maxMatrixSummandNorm_nonneg Z ω,
        HDP.matrixOpNorm_nonneg (∑ i, Z i ω)]
    have hinside' :
        2 * ‖∑ i, (Z i ω) ^ 2‖ *
            Real.log (2 * Fintype.card (Fin n)) ≤
          c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω) := by
      simpa [HDP.matrixOpNorm] using hinside
    exact hkh.trans (Real.sqrt_le_sqrt hinside')
  have hRbound : (∫ ω, R ω ∂μ) ≤
      ∫ ω, Real.sqrt
        (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) ∂μ := by
    exact integral_mono hRint (by simpa [mul_assoc] using hrhsInt) hpoint
  have hsymmOp := symmetrization_centered_sum_upper
    (μ := μ) (ν := matrixSignMeasure N) hZopm hZopint hZopind
    (fun i => matrixSignCoordinate_measurable i)
    (fun i => matrixSignCoordinate_isRademacherHDP i)
    matrixSignCoordinate_independent
  have hIntZop (i : Fin N) :
      (∫ ω, Zop i ω ∂μ) = e (∫ ω, Z i ω ∂μ) :=
    e.toContinuousLinearMap.integral_comp_comm (hZint i)
  have hIntS : (∫ ω, S ω ∂μ) = ∑ i, ∫ ω, Z i ω ∂μ := by
    exact integral_finsetSum Finset.univ fun i _ => hZint i
  have hcenterNorm (ω : Ω) :
      ‖∑ i, (Zop i ω - ∫ u, Zop i u ∂μ)‖ =
        HDP.matrixOpNorm (S ω - ∫ u, S u ∂μ) := by
    have heq : (∑ i, (Zop i ω - ∫ u, Zop i u ∂μ)) =
        e (S ω - ∫ u, S u ∂μ) := by
      calc
        (∑ i, (Zop i ω - ∫ u, Zop i u ∂μ)) =
            ∑ i, (e (Z i ω) - e (∫ u, Z i u ∂μ)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hIntZop i]
        _ = e (∑ i, (Z i ω - ∫ u, Z i u ∂μ)) := by
          symm
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_sub]
        _ = e (S ω - ∫ u, S u ∂μ) := by
          congr 1
          rw [Finset.sum_sub_distrib, hIntS]
    rw [heq]
    exact matrixOperatorEquiv_norm _
  have hsymm :
      (∫ ω, HDP.matrixOpNorm (S ω - ∫ u, S u ∂μ) ∂μ) ≤
        2 * ∫ z : Ω × MatrixSignSample N,
          HDP.matrixOpNorm
            (∑ i, matrixSignCoordinate i z.2 • Z i z.1)
              ∂μ.prod (matrixSignMeasure N) := by
    calc
      (∫ ω, HDP.matrixOpNorm (S ω - ∫ u, S u ∂μ) ∂μ) =
          ∫ ω, ‖∑ i, (Zop i ω - ∫ u, Zop i u ∂μ)‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => (hcenterNorm ω).symm
      _ ≤ 2 * ∫ z : Ω × MatrixSignSample N,
          ‖∑ i, matrixSignCoordinate i z.2 • Zop i z.1‖
            ∂μ.prod (matrixSignMeasure N) := hsymmOp
      _ = 2 * ∫ z : Ω × MatrixSignSample N,
          HDP.matrixOpNorm
            (∑ i, matrixSignCoordinate i z.2 • Z i z.1)
              ∂μ.prod (matrixSignMeasure N) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hsignedNorm
  have hprod :
      (∫ z : Ω × MatrixSignSample N,
          HDP.matrixOpNorm
            (∑ i, matrixSignCoordinate i z.2 • Z i z.1)
            ∂μ.prod (matrixSignMeasure N)) = ∫ ω, R ω ∂μ := by
    calc
      (∫ z : Ω × MatrixSignSample N,
          HDP.matrixOpNorm
            (∑ i, matrixSignCoordinate i z.2 • Z i z.1)
            ∂μ.prod (matrixSignMeasure N)) =
          ∫ ω, ∫ ε,
            HDP.matrixOpNorm
              (∑ i, matrixSignCoordinate i ε • Z i ω)
              ∂matrixSignMeasure N ∂μ := integral_prod _ hsignedMatrix.norm
      _ = ∫ ω, R ω ∂μ := rfl
  have hsymmKh :
      let y := ∫ ω, HDP.matrixOpNorm
        (S ω - ∫ ξ, S ξ ∂μ) ∂μ
      y ≤ 2 * ∫ ω, Real.sqrt
        (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) ∂μ := by
    dsimp only
    calc
      (∫ ω, HDP.matrixOpNorm (S ω - ∫ ξ, S ξ ∂μ) ∂μ) ≤
          2 * ∫ z : Ω × MatrixSignSample N,
            HDP.matrixOpNorm
              (∑ i, matrixSignCoordinate i z.2 • Z i z.1)
              ∂μ.prod (matrixSignMeasure N) := by
        exact hsymm
      _ = 2 * ∫ ω, R ω ∂μ := by rw [hprod]
      _ ≤ 2 * ∫ ω, Real.sqrt
          (c * maxMatrixSummandNorm Z ω * HDP.matrixOpNorm (S ω)) ∂μ :=
        mul_le_mul_of_nonneg_left hRbound (by norm_num)
  simpa [S, c] using
    unbounded_psd_sum_of_symmetrized_khintchine Z hZm hmax hsymmKh

/-! ## Exercise 6.34: covariance estimation under an expected-maximum bound -/

/-- The direct expected-maximum form underlying the corresponding exercise. The maximum is taken
over the actual iid sample copies (the printed display omits this index), and the normalization
is valid for every positive integer sample size.

**Book Exercise 6.34.** -/
theorem unbounded_sampleCovariance_expected_max
    [IsProbabilityMeasure μ] {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (hm : 0 < m)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hXm : Measurable X)
    (hXsm : ∀ i, Measurable (Xs i))
    (henergy : Integrable (fun ω => ‖X ω‖ ^ 2) μ)
    (hmax : Integrable (maxSampleEnergy Xs) μ)
    (hid : ∀ i, IdentDistrib (Xs i) X μ μ)
    (hind : iIndepFun Xs μ) :
    let Sigma := ∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ
    let q := (2 * Real.log (2 * n)) *
      ((m : ℝ)⁻¹ * ∫ ω, maxSampleEnergy Xs ω ∂μ)
    ∫ ω, HDP.matrixOpNorm
        (HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) - Sigma) ∂μ ≤
      4 * Real.sqrt (q * HDP.matrixOpNorm Sigma) + 8 * q := by
  dsimp only
  let O : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    HDP.Chapter4.outerProductMatrix
  let Z : Fin m → Ω → Matrix (Fin n) (Fin n) ℝ :=
    fun i ω => (m : ℝ)⁻¹ • O (Xs i ω)
  have hmR : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have hZm : ∀ i, Measurable (Z i) := fun i => by
    exact (measurable_outerProductMatrix.comp (hXsm i)).const_smul (m : ℝ)⁻¹
  have hZpsd : ∀ i ω, (Z i ω).PosSemidef := fun i ω => by
    exact (outerProductMatrix_posSemidef (Xs i ω)).smul hmR
  have hZind : iIndepFun Z μ := by
    simpa [Z, O, Function.comp_def] using
      hind.comp (fun _ x => (m : ℝ)⁻¹ • HDP.Chapter4.outerProductMatrix x)
        (fun _ => measurable_outerProductMatrix.const_smul (m : ℝ)⁻¹)
  have hZnorm (i : Fin m) (ω : Ω) :
      HDP.matrixOpNorm (Z i ω) = (m : ℝ)⁻¹ * ‖Xs i ω‖ ^ 2 := by
    dsimp only [Z, O]
    rw [HDP.matrixOpNorm_smul, abs_of_nonneg hmR,
      matrixOpNorm_outerProductMatrix]
  have hmaxEq (ω : Ω) :
      maxMatrixSummandNorm Z ω = (m : ℝ)⁻¹ * maxSampleEnergy Xs ω := by
    unfold maxMatrixSummandNorm maxSampleEnergy
    calc
      Finset.univ.sup' Finset.univ_nonempty
          (fun i => HDP.matrixOpNorm (Z i ω)) =
          Finset.univ.sup' Finset.univ_nonempty
            (fun i => (m : ℝ)⁻¹ * ‖Xs i ω‖ ^ 2) := by
        apply Finset.sup'_congr Finset.univ_nonempty rfl
        intro i _
        exact hZnorm i ω
      _ = (m : ℝ)⁻¹ * Finset.univ.sup' Finset.univ_nonempty
          (fun i => ‖Xs i ω‖ ^ 2) :=
        (Finset.mul₀_sup' hmR (fun i => ‖Xs i ω‖ ^ 2)
          Finset.univ Finset.univ_nonempty).symm
  have hZmax : Integrable (maxMatrixSummandNorm Z) μ := by
    refine ((hmax.const_mul (m : ℝ)⁻¹).congr
      (Filter.Eventually.of_forall fun ω => ?_))
    exact hmaxEq ω |>.symm
  have hmaxInt :
      (∫ ω, maxMatrixSummandNorm Z ω ∂μ) =
        (m : ℝ)⁻¹ * ∫ ω, maxSampleEnergy Xs ω ∂μ := by
    calc
      (∫ ω, maxMatrixSummandNorm Z ω ∂μ) =
          ∫ ω, (m : ℝ)⁻¹ * maxSampleEnergy Xs ω ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hmaxEq
      _ = (m : ℝ)⁻¹ * ∫ ω, maxSampleEnergy Xs ω ∂μ :=
        by rw [integral_const_mul]
  have hsum (ω : Ω) :
      (∑ i, Z i ω) =
        HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) := by
    exact sum_scaled_outerProductMatrix_eq_sampleCovarianceMatrix _
  have hmain := exercise_6_33 (Z := Z) hZm hZpsd hZind hZmax
  simp only [hsum, hmaxInt] at hmain
  rw [integral_sampleCovarianceMatrix_eq hm hXm henergy hid] at hmain
  exact hmain

/-- Let `Sigma` be the uncentered population second moment and let `Sigma_m` be formed from `m`
iid copies. If the expected maximum sample energy is at most `K²` times the population energy,
then the expected operator-norm error obeys the displayed effective-rank bound. The total
definition of `effectiveRank` makes the zero-second-moment case meaningful, and that case is
proved separately below. Source correction: the maximum assumption ranges over the indexed
copies `Xs i`; the unindexed maximum printed in the source is malformed.

**Book Exercise 6.34.** -/
theorem exercise_6_34
    [IsProbabilityMeasure μ] {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (hm : 0 < m)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (Xs : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hXm : Measurable X)
    (hXsm : ∀ i, Measurable (Xs i))
    (henergy : Integrable (fun ω => ‖X ω‖ ^ 2) μ)
    (hmax : Integrable (maxSampleEnergy Xs) μ)
    (hid : ∀ i, IdentDistrib (Xs i) X μ μ)
    (hind : iIndepFun Xs μ)
    {K : ℝ} (hK : 1 ≤ K)
    (hmaxBound :
      (∫ ω, maxSampleEnergy Xs ω ∂μ) ≤
        K ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂μ) :
    let Sigma := ∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ
    let t := 2 * K ^ 2 * HDP.effectiveRank Sigma *
      Real.log (2 * n) / m
    ∫ ω, HDP.matrixOpNorm
        (HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) - Sigma) ∂μ ≤
      (4 * Real.sqrt t + 8 * t) * HDP.matrixOpNorm Sigma := by
  dsimp only
  let Sigma : Matrix (Fin n) (Fin n) ℝ :=
    ∫ ω, HDP.Chapter4.outerProductMatrix (X ω) ∂μ
  let a : ℝ := HDP.matrixOpNorm Sigma
  let q : ℝ := (2 * Real.log (2 * n)) *
    ((m : ℝ)⁻¹ * ∫ ω, maxSampleEnergy Xs ω ∂μ)
  let t : ℝ := 2 * K ^ 2 * HDP.effectiveRank Sigma *
    Real.log (2 * n) / m
  change (∫ ω, HDP.matrixOpNorm
      (HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) - Sigma) ∂μ) ≤
    (4 * Real.sqrt t + 8 * t) * a
  have hbase :
      (∫ ω, HDP.matrixOpNorm
          (HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) - Sigma) ∂μ) ≤
        4 * Real.sqrt (q * a) + 8 * q := by
    simpa [Sigma, q, a] using
      unbounded_sampleCovariance_expected_max hm X Xs hXm hXsm henergy hmax hid hind
  have hnPos : 0 < n := by
    simpa using (Fintype.card_pos (α := Fin n))
  have hn : (1 : ℝ) ≤ 2 * n := by
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  have hlog : 0 ≤ Real.log (2 * n) := Real.log_nonneg hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hinv : (0 : ℝ) ≤ (m : ℝ)⁻¹ := (inv_pos.mpr hmR).le
  have hK0 : 0 ≤ K := (by linarith : 0 ≤ K)
  have henergy0 : 0 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg ‖X ω‖
  have hmax0 : 0 ≤ ∫ ω, maxSampleEnergy Xs ω ∂μ :=
    integral_nonneg (maxSampleEnergy_nonneg Xs)
  have ha : 0 ≤ a := HDP.matrixOpNorm_nonneg Sigma
  have htrace : Sigma.trace = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
    simpa [Sigma] using trace_integral_outerProductMatrix hXm henergy
  by_cases ha0 : a = 0
  · have hSigma0 : Sigma = 0 := by
      apply (HDP.Chapter4.matrixOpNorm_eq_zero_iff Sigma).mp
      exact ha0
    have henergyEq0 : (∫ ω, ‖X ω‖ ^ 2 ∂μ) = 0 := by
      rw [← htrace, hSigma0]
      simp
    have hmaxEq0 : (∫ ω, maxSampleEnergy Xs ω ∂μ) = 0 := by
      apply le_antisymm
      · calc
          (∫ ω, maxSampleEnergy Xs ω ∂μ) ≤
              K ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂μ := hmaxBound
          _ = 0 := by rw [henergyEq0]; ring
      · exact hmax0
    have hq0 : q = 0 := by simp [q, hmaxEq0]
    have ht0 : t = 0 := by simp [t, hSigma0]
    calc
      (∫ ω, HDP.matrixOpNorm
          (HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) - Sigma) ∂μ)
          ≤ 4 * Real.sqrt (q * a) + 8 * q := hbase
      _ = 0 := by rw [hq0]; norm_num
      _ = (4 * Real.sqrt t + 8 * t) * a := by rw [ht0, ha0]; norm_num
  · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have htrace0 : 0 ≤ Sigma.trace := by rw [htrace]; exact henergy0
    have hr : 0 ≤ HDP.effectiveRank Sigma := by
      rw [HDP.effectiveRank]
      exact div_nonneg htrace0 ha
    have ht : 0 ≤ t := by
      dsimp only [t]
      positivity
    have htraceEff :
        Sigma.trace = HDP.effectiveRank Sigma * a := by
      dsimp only [a]
      rw [HDP.effectiveRank]
      exact (div_mul_cancel₀ Sigma.trace (by simpa [a] using ha0)).symm
    have hq : q ≤ t * a := by
      calc
        q = (2 * Real.log (2 * n)) *
            ((m : ℝ)⁻¹ * ∫ ω, maxSampleEnergy Xs ω ∂μ) := rfl
        _ ≤ (2 * Real.log (2 * n)) *
            ((m : ℝ)⁻¹ *
              (K ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂μ)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hlog)
          exact mul_le_mul_of_nonneg_left hmaxBound hinv
        _ = t * a := by
          rw [← htrace, htraceEff]
          dsimp only [t]
          field_simp
    have hsqrtFactor : Real.sqrt ((t * a) * a) = Real.sqrt t * a := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) ha)).mp
      rw [Real.sq_sqrt (mul_nonneg (mul_nonneg ht ha) ha), mul_pow,
        Real.sq_sqrt ht]
      ring
    have hsqrt : Real.sqrt (q * a) ≤ Real.sqrt t * a := by
      calc
        Real.sqrt (q * a) ≤ Real.sqrt ((t * a) * a) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hq ha)
        _ = Real.sqrt t * a := hsqrtFactor
    calc
      (∫ ω, HDP.matrixOpNorm
          (HDP.Chapter4.sampleCovarianceMatrix (fun i => Xs i ω) - Sigma) ∂μ)
          ≤ 4 * Real.sqrt (q * a) + 8 * q := hbase
      _ ≤ (4 * Real.sqrt t + 8 * t) * a := by nlinarith

end HDP.Chapter6

end Source_12_UnboundedMatrixExtensions

/-! ## Material formerly in `13_Contraction.lean` -/

section Source_13_Contraction

/-!
# Chapter 6, §6.6: the contraction principle

This file proves the contraction principle for an actual finite independent
Rademacher family.  The proof follows the source: the expected norm is a convex
function of the coefficient vector, the coefficient cube is the convex hull of
its sign vectors, and multiplying independent Rademachers by deterministic
signs does not change their joint law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace HDP.Chapter6

noncomputable section

variable {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

/-- The expected norm of a Rademacher series as a function of its deterministic coefficient
vector.

**Book (6.20).** -/
def contractionFunctional (μ : Measure Ω) (ε : ι → Ω → ℝ) (x : ι → E)
    (a : ι → ℝ) : ℝ :=
  ∫ ω, ‖∑ i, (a i * ε i ω) • x i‖ ∂μ

/-- Every finite deterministic-coefficient Rademacher series, and hence its norm, is integrable.
Independence is not needed for this analytic fact.

**Lean implementation helper.** -/
lemma integrable_rademacherSeries_norm [IsProbabilityMeasure μ]
    {ε : ι → Ω → ℝ} (hε : ∀ i, HDP.IsRademacher (ε i) μ)
    (x : ι → E) (a : ι → ℝ) :
    Integrable (fun ω => ‖∑ i, (a i * ε i ω) • x i‖) μ := by
  apply Integrable.norm
  apply integrable_finsetSum Finset.univ
  intro i _
  exact ((((hε i).memLp 1).integrable le_rfl).const_mul (a i)).smul_const (x i)

/-- The function in (6.20) is convex. This is kept in the thematic core because it is the main
proof input to the corresponding theorem.

**Book Exercise 6.35.** -/
theorem exercise_6_35_contractionFunctional_convex [IsProbabilityMeasure μ]
    {ε : ι → Ω → ℝ} (hε : ∀ i, HDP.IsRademacher (ε i) μ)
    (x : ι → E) :
    ConvexOn ℝ Set.univ (contractionFunctional μ ε x) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ p q hp hq _
  unfold contractionFunctional
  let fa : Ω → ℝ := fun ω => ‖∑ i, (a i * ε i ω) • x i‖
  let fb : Ω → ℝ := fun ω => ‖∑ i, (b i * ε i ω) • x i‖
  calc
    (∫ ω, ‖∑ i, (((p • a + q • b) i) * ε i ω) • x i‖ ∂μ)
        ≤ ∫ ω, p * fa ω + q * fb ω ∂μ := by
      apply integral_mono
      · exact integrable_rademacherSeries_norm hε x (p • a + q • b)
      · exact ((integrable_rademacherSeries_norm hε x a).const_mul p).add
          ((integrable_rademacherSeries_norm hε x b).const_mul q)
      · intro ω
        have hsum :
            (∑ i, (((p • a + q • b) i) * ε i ω) • x i) =
              p • (∑ i, (a i * ε i ω) • x i) +
                q • (∑ i, (b i * ε i ω) • x i) := by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [smul_smul, smul_smul, ← add_smul]
          congr 1
          ring
        change ‖∑ i, (((p • a + q • b) i) * ε i ω) • x i‖ ≤
          p * fa ω + q * fb ω
        rw [hsum]
        calc
          ‖p • (∑ i, (a i * ε i ω) • x i) +
              q • (∑ i, (b i * ε i ω) • x i)‖
              ≤ ‖p • (∑ i, (a i * ε i ω) • x i)‖ +
                ‖q • (∑ i, (b i * ε i ω) • x i)‖ := norm_add_le _ _
          _ = p * fa ω + q * fb ω := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hp,
              Real.norm_of_nonneg hq]
    _ = p • (∫ ω, fa ω ∂μ) + q • (∫ ω, fb ω ∂μ) := by
      rw [integral_add, integral_const_mul, integral_const_mul]
      · rfl
      · exact (integrable_rademacherSeries_norm hε x a).const_mul p
      · exact (integrable_rademacherSeries_norm hε x b).const_mul q

/-- A deterministic sign preserves the fair Rademacher law.

**Lean implementation helper.** -/
lemma isRademacher_sign_mul [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : HDP.IsRademacher X μ) {s : ℝ}
    (hs : s = -1 ∨ s = 1) :
    HDP.IsRademacher (fun ω => s * X ω) μ := by
  classical
  rcases hs with rfl | rfl
  · refine ⟨hX.aemeasurable.const_mul (-1), ?_⟩
    have hfun : (fun ω => (-1 : ℝ) * X ω) = (fun z : ℝ => -z) ∘ X := by
      funext ω
      simp
    rw [hfun, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX.aemeasurable,
      hX.map_eq, map_bernoulliMeasure' _ _ (by fun_prop)]
    simp only [bernoulliMeasure_def]
    have hweights :
        unitInterval.toNNReal
            (unitInterval.symm ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) =
          unitInterval.toNNReal ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ := by
      ext
      norm_num
    rw [hweights, add_comm]
    norm_num
  · simpa using hX

omit [Fintype ι] in
/-- Multiplying every coordinate of an independent Rademacher family by a deterministic sign
vector preserves its joint distribution.

**Lean implementation helper.** -/
lemma identDistrib_sign_mul_rademacherFamily [Finite ι]
    [IsProbabilityMeasure μ]
    {ε : ι → Ω → ℝ} (hε : ∀ i, HDP.IsRademacher (ε i) μ)
    (hindep : iIndepFun ε μ) {s : ι → ℝ}
    (hs : ∀ i, s i = -1 ∨ s i = 1) :
    IdentDistrib (fun ω i => s i * ε i ω) (fun ω i => ε i ω) μ μ := by
  classical
  letI := Fintype.ofFinite ι
  have hscaled : ∀ i, HDP.IsRademacher (fun ω => s i * ε i ω) μ :=
    fun i => isRademacher_sign_mul (hε i) (hs i)
  have hscaled_indep : iIndepFun (fun i ω => s i * ε i ω) μ :=
    hindep.comp (fun i z => s i * z) (fun i => measurable_const_mul (s i))
  refine ⟨aemeasurable_pi_lambda _ (fun i => (hscaled i).aemeasurable),
    aemeasurable_pi_lambda _ (fun i => (hε i).aemeasurable), ?_⟩
  rw [hscaled_indep.map_fun_eq_pi_map (fun i => (hscaled i).aemeasurable),
    hindep.map_fun_eq_pi_map (fun i => (hε i).aemeasurable)]
  apply congrArg (fun ν : ι → Measure ℝ => Measure.pi ν)
  funext i
  exact (hscaled i).map_eq.trans (hε i).map_eq.symm

/-- Shows that the contraction functional has the same value at every sign vector as at the
all-ones vector.

**Book (6.20).** -/
lemma contractionFunctional_eq_of_mem_cubeVertices [IsProbabilityMeasure μ]
    {ε : ι → Ω → ℝ} (hε : ∀ i, HDP.IsRademacher (ε i) μ)
    (hindep : iIndepFun ε μ) (x : ι → E) {s : ι → ℝ}
    (hs : s ∈ HDP.Chapter1.cubeVertices) :
    contractionFunctional μ ε x s = contractionFunctional μ ε x (fun _ => 1) := by
  have hsign : ∀ i, s i = -1 ∨ s i = 1 := by
    intro i
    have hi := hs i (Set.mem_univ i)
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
  let F : (ι → ℝ) → ℝ := fun e => ‖∑ i, (e i) • x i‖
  have hF : Measurable F := by
    apply Continuous.measurable
    fun_prop
  have hid := (identDistrib_sign_mul_rademacherFamily hε hindep hsign).comp hF
  have hint := hid.integral_eq
  simpa [contractionFunctional, F, Function.comp_def] using hint

/-- Unit-cube form of the corresponding theorem.

**Book Theorem 6.6.1.** -/
theorem contractionPrinciple_unit [IsProbabilityMeasure μ]
    {ε : ι → Ω → ℝ} (hε : ∀ i, HDP.IsRademacher (ε i) μ)
    (hindep : iIndepFun ε μ) (x : ι → E) (a : ι → ℝ)
    (ha : HDP.Chapter1.linftyNorm a ≤ 1) :
    contractionFunctional μ ε x a ≤
      contractionFunctional μ ε x (fun _ => 1) := by
  have ha_mem : a ∈ HDP.Chapter1.linftyUnitBall := ha
  rw [HDP.Chapter1.linftyUnitBall_eq_convexHull_cubeVertices] at ha_mem
  obtain ⟨s, hs, has⟩ := HDP.Chapter1.convexHull_value_le_generator
    (exercise_6_35_contractionFunctional_convex hε x)
    (Set.subset_univ HDP.Chapter1.cubeVertices) ha_mem
  rw [contractionFunctional_eq_of_mem_cubeVertices hε hindep x hs] at has
  exact has

/-- For independent Rademacher signs and deterministic vectors in a real normed space,
coordinatewise scalar contraction costs exactly the finite `ell-infinity` norm of the
coefficient vector.

**Book Theorem 6.6.1.** -/
theorem contractionPrinciple [IsProbabilityMeasure μ]
    {ε : ι → Ω → ℝ} (hε : ∀ i, HDP.IsRademacher (ε i) μ)
    (hindep : iIndepFun ε μ) (x : ι → E) (a : ι → ℝ) :
    (∫ ω, ‖∑ i, (a i * ε i ω) • x i‖ ∂μ) ≤
      HDP.Chapter1.linftyNorm a *
        ∫ ω, ‖∑ i, (ε i ω) • x i‖ ∂μ := by
  let A := HDP.Chapter1.linftyNorm a
  by_cases hA : A = 0
  · have ha0 : a = 0 := HDP.Chapter1.linftyNorm_eq_zero_iff.mp hA
    rw [ha0, HDP.Chapter1.linftyNorm_eq_zero_iff.mpr rfl]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne (HDP.Chapter1.linftyNorm_nonneg a)
      (Ne.symm hA)
    let c : ι → ℝ := fun i => a i / A
    have hc : HDP.Chapter1.linftyNorm c ≤ 1 := by
      rw [HDP.Chapter1.linftyNorm_le_iff zero_le_one]
      intro i
      rw [abs_div, abs_of_pos hApos]
      exact (div_le_one hApos).mpr
        ((HDP.Chapter1.linftyNorm_le_iff hApos.le).mp le_rfl i)
    have hunit := contractionPrinciple_unit hε hindep x c hc
    have hscale :
        (∫ ω, ‖∑ i, (a i * ε i ω) • x i‖ ∂μ) =
          A * contractionFunctional μ ε x c := by
      rw [contractionFunctional, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [← Real.norm_of_nonneg hApos.le, ← norm_smul]
      congr 1
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      apply congrArg (fun r : ℝ => r • x i)
      dsimp only [c]
      field_simp
    rw [hscale]
    have hmul := mul_le_mul_of_nonneg_left hunit hApos.le
    simpa [contractionFunctional, A] using hmul

end

end HDP.Chapter6

end Source_13_Contraction

/-! ## Material formerly in `14_GaussianSymmetrization.lean` -/

section Source_14_GaussianSymmetrization

/-!
# Chapter 6, §6.6: Gaussian symmetrization

The probability spaces in this file are deliberately separated.  Thus the
Gaussian coefficients, the Rademacher signs, and the random vectors are
mutually independent by construction; only independence inside each finite
family has to be stated.

The printed lower estimate in Lemma 6.6.2 contains `sqrt (log N)` and is not
meaningful for `N = 1`.  The primary theorem below therefore uses the safe
quantity `sqrt (2 * log (2 * N))`.  A source-shaped wrapper assumes `N >= 2`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace HDP.Chapter6

noncomputable section

/-- A centered real Gaussian law is symmetric.

**Lean implementation helper.** -/
lemma isSymmetricRV_of_hasLaw_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ) :
  HDP.IsSymmetricRV g μ := by
  refine ⟨hg.aemeasurable, hg.aemeasurable.neg, ?_⟩
  change μ.map g = μ.map (-g)
  have hneg : μ.map (-g) = gaussianReal 0 1 := by
    simpa only [neg_zero] using (gaussianReal_neg hg).map_eq
  exact hg.map_eq.trans hneg.symm

/-- Multiplying the absolute value of a standard Gaussian by an independent fair sign
reconstructs the standard Gaussian law.

**Lean implementation helper.** -/
theorem identDistrib_rademacher_mul_abs_standardGaussian
    {Ωε Ωg : Type*} [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {ε : Ωε → ℝ} {g : Ωg → ℝ}
    (hεm : Measurable ε) (hε : HDP.IsRademacher ε ν)
    (hgm : Measurable g) (hg : HasLaw g (gaussianReal 0 1) γ) :
    IdentDistrib (fun z : Ωε × Ωg => ε z.1 * |g z.2|)
      (fun z : Ωε × Ωg => g z.2) (ν.prod γ) (ν.prod γ) := by
  let e : Ωε × Ωg → ℝ := fun z => ε z.1
  let a : Ωε × Ωg → ℝ := fun z => |g z.2|
  let gp : Ωε × Ωg → ℝ := fun z => g z.2
  have he : HDP.IsRademacher e (ν.prod γ) := by
    refine ⟨(hεm.comp measurable_fst).aemeasurable, ?_⟩
    rw [show e = ε ∘ Prod.fst by rfl,
      ← Measure.map_map hεm measurable_fst,
      (measurePreserving_fst (α := Ωε) (β := Ωg) (μ := ν) (ν := γ)).map_eq,
      hε.map_eq]
  have hea : IndepFun e a (ν.prod γ) := by
    exact indepFun_prod hεm hgm.abs
  have hsigned : HDP.IsSymmetricRV (fun z => e z * a z) (ν.prod γ) :=
    rademacher_mul_isSymmetricRV he
      ((hgm.comp measurable_snd).aemeasurable.abs) hea
  have hgpLaw : HasLaw gp (gaussianReal 0 1) (ν.prod γ) := by
    exact hg.comp
      (measurePreserving_snd (α := Ωε) (β := Ωg) (μ := ν) (ν := γ)).hasLaw
  have hgpSym : HDP.IsSymmetricRV gp (ν.prod γ) :=
    isSymmetricRV_of_hasLaw_standardGaussian hgpLaw
  have habs : IdentDistrib (fun z => |e z * a z|) (fun z => |gp z|)
      (ν.prod γ) (ν.prod γ) := by
    apply IdentDistrib.of_ae_eq ((he.aemeasurable.mul
      ((hgm.comp measurable_snd).aemeasurable.abs)).abs)
    filter_upwards [he.ae_mem] with z hz
    rcases hz with hz | hz <;> simp [e, gp, hz]
  simpa [e, a, gp] using
    HDP.IsSymmetricRV.identDistrib_of_abs hsigned hgpSym habs

/-- Joint version of `identDistrib_rademacher_mul_abs_standardGaussian`. Independence of the two
input families is exactly what upgrades the coordinatewise law calculation to equality of the
complete finite vectors.

**Lean implementation helper.** -/
theorem identDistrib_rademacher_mul_abs_standardGaussian_family
    {ι Ωε Ωg : Type*} [Finite ι]
    [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {ε : ι → Ωε → ℝ} {g : ι → Ωg → ℝ}
    (hεm : ∀ i, Measurable (ε i)) (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    IdentDistrib
      (fun z : Ωε × Ωg => fun i => ε i z.1 * |g i z.2|)
      (fun z : Ωε × Ωg => fun i => g i z.2)
      (ν.prod γ) (ν.prod γ) := by
  letI := Fintype.ofFinite ι
  have hpairs : iIndepFun
      (fun i (z : Ωε × Ωg) => (ε i z.1, g i z.2)) (ν.prod γ) :=
    iIndepFun_prodMk_prod hεm hgm hεind hgind
  have hsigned : iIndepFun
      (fun i (z : Ωε × Ωg) => ε i z.1 * |g i z.2|) (ν.prod γ) := by
    simpa [Function.comp_def] using hpairs.comp
      (fun _ (z : ℝ × ℝ) => z.1 * |z.2|)
      (fun _ => measurable_fst.mul measurable_snd.abs)
  have hgprod : iIndepFun
      (fun i (z : Ωε × Ωg) => g i z.2) (ν.prod γ) := by
    simpa [Function.comp_def] using hpairs.comp
      (fun _ (z : ℝ × ℝ) => z.2) (fun _ => measurable_snd)
  exact IdentDistrib.pi
    (fun i => identDistrib_rademacher_mul_abs_standardGaussian
      (hεm i) (hε i) (hgm i) (hg i)) hsigned hgprod

/-- Exact first absolute moment of a standard Gaussian, in the algebraically convenient `sqrt 2
/ sqrt pi` form used in the proof of the corresponding lemma.

**Lean implementation helper.** -/
lemma integral_abs_of_hasLaw_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ) :
    (∫ ω, |g ω| ∂μ) = Real.sqrt 2 / Real.sqrt Real.pi := by
  have h := HDP.Chapter2.gaussian_absolute_moment hg
    (p := (1 : ℝ)) (by norm_num)
  norm_num [Real.Gamma_one, Real.sqrt_eq_rpow] at h ⊢
  exact h

/-- Gaussian-coefficient random-vector sum on the structurally independent product space.

**Lean implementation helper.** -/
def gaussianRandomVectorSum
    {ι Ω Ωg E : Type*} [Fintype ι] [AddCommMonoid E] [SMul ℝ E]
    (X : ι → Ω → E) (g : ι → Ωg → ℝ) : Ω × Ωg → E :=
  fun z => ∑ i, (g i z.2) • X i z.1

/-- Signed-Gaussian-magnitude sum used in the Jensen step.

**Lean implementation helper.** -/
def signedAbsGaussianRandomVectorSum
    {ι Ω Ωε Ωg E : Type*} [Fintype ι] [AddCommMonoid E] [SMul ℝ E]
    (X : ι → Ω → E) (ε : ι → Ωε → ℝ) (g : ι → Ωg → ℝ) :
    Ω × (Ωε × Ωg) → E :=
  fun z => ∑ i, (ε i z.2.1 * |g i z.2.2|) • X i z.1

/-- Establishes integrability of gaussian random vector sum.

**Lean implementation helper.** -/
lemma integrable_gaussianRandomVectorSum
    {ι Ω Ωg E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    {X : ι → Ω → E} {g : ι → Ωg → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ) :
    Integrable (gaussianRandomVectorSum X g) (μ.prod γ) := by
  unfold gaussianRandomVectorSum
  apply integrable_finsetSum Finset.univ
  intro i _
  have hi : Integrable
      (fun z : Ωg × Ω => g i z.1 • X i z.2) (γ.prod μ) :=
    (HDP.Chapter2.integrable_of_hasLaw_standardGaussian (hg i)).smul_prod
      (hXint i)
  simpa [gaussianRandomVectorSum, Function.comp_def] using hi.swap

/-- Establishes integrability of signed abs gaussian random vector sum.

**Lean implementation helper.** -/
lemma integrable_signedAbsGaussianRandomVectorSum
    {ι Ω Ωε Ωg E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : ι → Ω → E} {ε : ι → Ωε → ℝ} {g : ι → Ωg → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ) :
    Integrable (signedAbsGaussianRandomVectorSum X ε g)
      (μ.prod (ν.prod γ)) := by
  unfold signedAbsGaussianRandomVectorSum
  apply integrable_finsetSum Finset.univ
  intro i _
  have hc : Integrable
      (fun z : Ωε × Ωg => ε i z.1 * |g i z.2|) (ν.prod γ) :=
    (((hε i).memLp 1).integrable le_rfl).mul_prod
      (HDP.Chapter2.integrable_of_hasLaw_standardGaussian (hg i)).abs
  have hi : Integrable
      (fun z : (Ωε × Ωg) × Ω =>
        (ε i z.1.1 * |g i z.1.2|) • X i z.2)
      ((ν.prod γ).prod μ) := hc.smul_prod (hXint i)
  simpa [signedAbsGaussianRandomVectorSum, Function.comp_def] using hi.swap

/-- Jensen's inequality in the exact form used in the Gaussian symmetrization proof: replacing
`E |g|` by `|g|` can only increase the expected norm.

**Lean implementation helper.** -/
lemma gaussianMagnitude_jensen
    {ι Ωg E : Type*} [Fintype ι] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {γ : Measure Ωg} [IsProbabilityMeasure γ]
    {g : ι → Ωg → ℝ}
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (a : ι → ℝ) (x : ι → E) :
    (Real.sqrt 2 / Real.sqrt Real.pi) * ‖∑ i, (a i) • x i‖ ≤
      ∫ ω, ‖∑ i, (a i * |g i ω|) • x i‖ ∂γ := by
  let α : ℝ := Real.sqrt 2 / Real.sqrt Real.pi
  have hα0 : 0 ≤ α := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hterm (i : ι) : Integrable
      (fun ω => (a i * |g i ω|) • x i) γ :=
    (((HDP.Chapter2.integrable_of_hasLaw_standardGaussian (hg i)).abs.const_mul
      (a i)).smul_const (x i))
  have hsum : Integrable (fun ω => ∑ i, (a i * |g i ω|) • x i) γ :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hint : (∫ ω, ∑ i, (a i * |g i ω|) • x i ∂γ) =
      α • ∑ i, (a i) • x i := by
    rw [integral_finsetSum Finset.univ (fun i _ => hterm i), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_const, integral_const_mul,
      integral_abs_of_hasLaw_standardGaussian (hg i)]
    rw [smul_smul]
    congr 1
    dsimp [α]
    ring
  calc
    α * ‖∑ i, (a i) • x i‖ = ‖α • ∑ i, (a i) • x i‖ := by
      rw [norm_smul, Real.norm_of_nonneg hα0]
    _ = ‖∫ ω, ∑ i, (a i * |g i ω|) • x i ∂γ‖ := by rw [hint]
    _ ≤ ∫ ω, ‖∑ i, (a i * |g i ω|) • x i‖ ∂γ :=
      norm_integral_le_integral_norm _

/-- Establishes integrability of signed abs gaussian series norm.

**Lean implementation helper.** -/
lemma integrable_signedAbsGaussianSeries_norm
    {ι Ωε Ωg E : Type*} [Fintype ι]
    [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {ε : ι → Ωε → ℝ} {g : ι → Ωg → ℝ}
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (x : ι → E) :
    Integrable (fun z : Ωε × Ωg =>
      ‖∑ i, (ε i z.1 * |g i z.2|) • x i‖) (ν.prod γ) := by
  apply Integrable.norm
  apply integrable_finsetSum Finset.univ
  intro i _
  have hc : Integrable
      (fun z : Ωε × Ωg => ε i z.1 * |g i z.2|) (ν.prod γ) :=
    (((hε i).memLp 1).integrable le_rfl).mul_prod
      (HDP.Chapter2.integrable_of_hasLaw_standardGaussian (hg i)).abs
  exact hc.smul_const (x i)

/-- Analytic core of the upper half of the corresponding lemma. The expected signed sum,
multiplied by `E |g|`, is at most the Gaussian-coefficient sum.

**Lean implementation helper.** -/
theorem rademacherSeries_mul_gaussianAbsMean_le_gaussianSeries
    {n : ℕ} {Ω Ωε Ωg E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : Fin (n + 2) → Ω → E}
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    (Real.sqrt 2 / Real.sqrt Real.pi) *
        (∫ z : Ω × Ωε, ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν) ≤
      ∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ := by
  let α : ℝ := Real.sqrt 2 / Real.sqrt Real.pi
  have hRvec : Integrable
      (fun z : Ω × Ωε => ∑ i, (ε i z.2) • X i z.1) (μ.prod ν) := by
    change Integrable (signedRandomVectorSum X ε) (μ.prod ν)
    exact integrable_signedRandomVectorSum hXint hε
  have hGvec : Integrable (gaussianRandomVectorSum X g) (μ.prod γ) :=
    integrable_gaussianRandomVectorSum hXint hg
  have hcoeffLaw :=
    identDistrib_rademacher_mul_abs_standardGaussian_family
      hεm hε hεind hgm hg hgind
  have hinner (ω : Ω) :
      (∫ z : Ωε × Ωg,
          ‖∑ i, (ε i z.1 * |g i z.2|) • X i ω‖ ∂ν.prod γ) =
        ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ := by
    let F : (Fin (n + 2) → ℝ) → ℝ :=
      fun c => ‖∑ i, (c i) • X i ω‖
    have hF : Measurable F := by
      exact (by fun_prop : Continuous F).measurable
    have hEq := (hcoeffLaw.comp hF).integral_eq
    have hsnd :
        (∫ z : Ωε × Ωg, ‖∑ i, (g i z.2) • X i ω‖ ∂ν.prod γ) =
          ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ := by
      let q : Ωg → ℝ := fun ξ => ‖∑ i, (g i ξ) • X i ω‖
      change (∫ z : Ωε × Ωg, q z.2 ∂ν.prod γ) = ∫ ξ, q ξ ∂γ
      rw [integral_fun_snd]
      simp
    have hleft :
        (∫ z : Ωε × Ωg,
          ‖∑ i, (ε i z.1 * |g i z.2|) • X i ω‖ ∂ν.prod γ) =
          ∫ z : Ωε × Ωg, ‖∑ i, (g i z.2) • X i ω‖ ∂ν.prod γ := by
      simpa [F, Function.comp_def] using hEq
    exact hleft.trans hsnd
  have hslice (ω : Ω) :
      α * (∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν) ≤
        ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ := by
    have hT : Integrable (fun z : Ωε × Ωg =>
        ‖∑ i, (ε i z.1 * |g i z.2|) • X i ω‖) (ν.prod γ) :=
      integrable_signedAbsGaussianSeries_norm hε hg (fun i => X i ω)
    have hR : Integrable (fun η => ‖∑ i, (ε i η) • X i ω‖) ν :=
      integrable_rademacherSeries_norm hε (fun i => X i ω) (fun _ => 1) |>.congr
        (Filter.Eventually.of_forall fun η => by simp)
    have hJ : ∀ η,
        α * ‖∑ i, (ε i η) • X i ω‖ ≤
          ∫ ξ, ‖∑ i, (ε i η * |g i ξ|) • X i ω‖ ∂γ := by
      intro η
      simpa [α] using gaussianMagnitude_jensen hg
        (fun i => ε i η) (fun i => X i ω)
    have hmono :
        (∫ η, α * ‖∑ i, (ε i η) • X i ω‖ ∂ν) ≤
          ∫ η, ∫ ξ,
            ‖∑ i, (ε i η * |g i ξ|) • X i ω‖ ∂γ ∂ν :=
      integral_mono (hR.const_mul α) hT.integral_prod_left hJ
    calc
      α * (∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν) =
          ∫ η, α * ‖∑ i, (ε i η) • X i ω‖ ∂ν :=
        (integral_const_mul ..).symm
      _ ≤ ∫ η, ∫ ξ,
          ‖∑ i, (ε i η * |g i ξ|) • X i ω‖ ∂γ ∂ν := hmono
      _ = ∫ z : Ωε × Ωg,
          ‖∑ i, (ε i z.1 * |g i z.2|) • X i ω‖ ∂ν.prod γ :=
        (integral_prod _ hT).symm
      _ = ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ := hinner ω
  have houter := integral_mono
    (hRvec.norm.integral_prod_left.const_mul α)
    hGvec.norm.integral_prod_left hslice
  calc
    α * (∫ z : Ω × Ωε, ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν) =
        ∫ ω, α * (∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν) ∂μ := by
      rw [integral_prod _ hRvec.norm, integral_const_mul]
    _ ≤ ∫ ω, ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ ∂μ := houter
    _ = ∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ := by
      rw [integral_prod _ hGvec.norm]
      rfl

/-- Shows that gaussian abs mean is positive.

**Lean implementation helper.** -/
lemma gaussianAbsMean_pos :
    0 < Real.sqrt 2 / Real.sqrt Real.pi := by positivity

/-- The Gaussian absolute-mean constant `√(2/π)` times its reciprocal is `1`.

**Lean implementation helper.** -/
lemma gaussianAbsMean_mul_recip :
    (Real.sqrt 2 / Real.sqrt Real.pi) *
        (Real.sqrt Real.pi / Real.sqrt 2) = 1 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

/-- Bounds two mul gaussian abs mean recip by three.

**Lean implementation helper.** -/
lemma two_mul_gaussianAbsMean_recip_le_three :
    2 * (Real.sqrt Real.pi / Real.sqrt 2) ≤ 3 := by
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hpi0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  have hpile : Real.pi ≤ 4 := Real.pi_le_four
  rw [show 2 * (Real.sqrt Real.pi / Real.sqrt 2) =
    (2 * Real.sqrt Real.pi) / Real.sqrt 2 by ring]
  rw [div_le_iff₀ h2]
  nlinarith

/-- Upper half of the corrected source lemma, with the source's explicit constant `3`.

**Book Lemma 6.6.2.** -/
theorem gaussianSymmetrization_upper
    {n : ℕ} {Ω Ωε Ωg E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : Fin (n + 2) → Ω → E}
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
      3 * ∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ := by
  let α : ℝ := Real.sqrt 2 / Real.sqrt Real.pi
  let β : ℝ := Real.sqrt Real.pi / Real.sqrt 2
  let R : ℝ := ∫ z : Ω × Ωε,
    ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν
  let G : ℝ := ∫ z : Ω × Ωg,
    ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ
  have hsymm : (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤ 2 * R := by
    simpa [R] using
      symmetrization_upper hXm hXint hX0 hXind hεm hε hεind
  have hRG : α * R ≤ G := by
    simpa [α, R, G] using
      rademacherSeries_mul_gaussianAbsMean_le_gaussianSeries
        hXint hεm hε hεind hgm hg hgind
  have hβ0 : 0 ≤ β := by dsimp [β]; positivity
  have hαβ : α * β = 1 := by
    simpa [α, β] using gaussianAbsMean_mul_recip
  have hRle : R ≤ β * G := by
    calc
      R = β * (α * R) := by rw [← mul_assoc, mul_comm β α, hαβ, one_mul]
      _ ≤ β * G := mul_le_mul_of_nonneg_left hRG hβ0
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact integral_nonneg fun _ => norm_nonneg _
  calc
    (∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤ 2 * R := hsymm
    _ ≤ 2 * (β * G) := mul_le_mul_of_nonneg_left hRle (by norm_num)
    _ = (2 * β) * G := by ring
    _ ≤ 3 * G := mul_le_mul_of_nonneg_right
      (by simpa [β] using two_mul_gaussianAbsMean_recip_le_three) hG0

/-- Identifies `ℓ∞` norm with fin sup abs.

**Lean implementation helper.** -/
lemma linftyNorm_eq_finSup_abs {n : ℕ} (a : Fin (n + 2) → ℝ) :
    HDP.Chapter1.linftyNorm a =
      Finset.univ.sup' Finset.univ_nonempty (fun i => |a i|) := by
  let M := Finset.univ.sup' Finset.univ_nonempty (fun i => |a i|)
  have hM0 : 0 ≤ M := by
    exact (abs_nonneg (a 0)).trans
      (Finset.le_sup' (fun i => |a i|) (Finset.mem_univ 0))
  apply le_antisymm
  · rw [HDP.Chapter1.linftyNorm_le_iff hM0]
    intro i
    exact Finset.le_sup' (fun j => |a j|) (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i _
    exact (HDP.Chapter1.linftyNorm_le_iff
      (HDP.Chapter1.linftyNorm_nonneg a)).mp le_rfl i

/-- Establishes integrability of signed gaussian series norm.

**Lean implementation helper.** -/
lemma integrable_signedGaussianSeries_norm
    {ι Ωg Ωε E : Type*} [Fintype ι]
    [MeasurableSpace Ωg] [MeasurableSpace Ωε]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : Measure Ωg} {ν : Measure Ωε}
    [IsProbabilityMeasure γ] [IsProbabilityMeasure ν]
    {g : ι → Ωg → ℝ} {ε : ι → Ωε → ℝ}
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hε : ∀ i, HDP.IsRademacher (ε i) ν) (x : ι → E) :
    Integrable (fun z : Ωg × Ωε =>
      ‖∑ i, (g i z.1 * ε i z.2) • x i‖) (γ.prod ν) := by
  apply Integrable.norm
  apply integrable_finsetSum Finset.univ
  intro i _
  have hc : Integrable
      (fun z : Ωg × Ωε => g i z.1 * ε i z.2) (γ.prod ν) :=
    (HDP.Chapter2.integrable_of_hasLaw_standardGaussian (hg i)).mul_prod
      (((hε i).memLp 1).integrable le_rfl)
  exact hc.smul_const (x i)

/-- The contraction/maximal-inequality core of the lower half of the corresponding lemma.

**Lean implementation helper.** -/
theorem gaussianSeries_le_gaussianMax_mul_rademacherSeries
    {n : ℕ} {Ω Ωε Ωg E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : Fin (n + 2) → Ω → E}
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hXint : ∀ i, Integrable (X i) μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    (∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) ≤
      (∫ ξ, Finset.univ.sup' Finset.univ_nonempty
          (fun i => |g i ξ|) ∂γ) *
        ∫ z : Ω × Ωε, ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν := by
  let M : Ωg → ℝ := fun ξ =>
    Finset.univ.sup' Finset.univ_nonempty (fun i => |g i ξ|)
  have hMint : Integrable M γ :=
    HDP.Chapter2.gaussian_fin_max_abs_integrable hgm hg
  have hRvec : Integrable
      (fun z : Ω × Ωε => ∑ i, (ε i z.2) • X i z.1) (μ.prod ν) := by
    change Integrable (signedRandomVectorSum X ε) (μ.prod ν)
    exact integrable_signedRandomVectorSum hXint hε
  have hGvec : Integrable (gaussianRandomVectorSum X g) (μ.prod γ) :=
    integrable_gaussianRandomVectorSum hXint hg
  have hgSym : ∀ i, HDP.IsSymmetricRV (g i) γ :=
    fun i => isSymmetricRV_of_hasLaw_standardGaussian (hg i)
  have hsignedLaw := identDistrib_rademacher_smul_family
    hgm hεm hgSym hε hgind hεind
  have hslice (ω : Ω) :
      (∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ) ≤
        (∫ ξ, M ξ ∂γ) *
          ∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν := by
    let F : (Fin (n + 2) → ℝ) → ℝ :=
      fun c => ‖∑ i, (c i) • X i ω‖
    have hF : Measurable F := (by fun_prop : Continuous F).measurable
    have hLawEq := (hsignedLaw.comp hF).integral_eq
    have hsignedInt : Integrable (fun z : Ωg × Ωε =>
        ‖∑ i, (g i z.1 * ε i z.2) • X i ω‖) (γ.prod ν) :=
      integrable_signedGaussianSeries_norm hg hε (fun i => X i ω)
    have hR : Integrable (fun η => ‖∑ i, (ε i η) • X i ω‖) ν :=
      integrable_rademacherSeries_norm hε (fun i => X i ω) (fun _ => 1) |>.congr
        (Filter.Eventually.of_forall fun η => by simp)
    have hcontract (ξ : Ωg) :
        (∫ η, ‖∑ i, (g i ξ * ε i η) • X i ω‖ ∂ν) ≤
          M ξ * ∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν := by
      have h := contractionPrinciple hε hεind
        (fun i => X i ω) (fun i => g i ξ)
      simpa [M, linftyNorm_eq_finSup_abs] using h
    have hmono :
        (∫ ξ, ∫ η,
          ‖∑ i, (g i ξ * ε i η) • X i ω‖ ∂ν ∂γ) ≤
        ∫ ξ, M ξ *
          (∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν) ∂γ :=
      integral_mono hsignedInt.integral_prod_left
        (hMint.mul_const _ ) hcontract
    have hsignedEq :
        (∫ z : Ωg × Ωε,
          ‖∑ i, (g i z.1 * ε i z.2) • X i ω‖ ∂γ.prod ν) =
          ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ := by
      have hleft :
          (∫ z : Ωg × Ωε,
            ‖∑ i, (ε i z.2 * g i z.1) • X i ω‖ ∂γ.prod ν) =
            ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ := by
        simpa [F, Function.comp_def] using hLawEq
      convert hleft using 1
      all_goals simp only [mul_comm]
    calc
      (∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ) =
          ∫ z : Ωg × Ωε,
            ‖∑ i, (g i z.1 * ε i z.2) • X i ω‖ ∂γ.prod ν := hsignedEq.symm
      _ = ∫ ξ, ∫ η,
          ‖∑ i, (g i ξ * ε i η) • X i ω‖ ∂ν ∂γ :=
        integral_prod _ hsignedInt
      _ ≤ ∫ ξ, M ξ *
          (∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν) ∂γ := hmono
      _ = (∫ ξ, M ξ ∂γ) *
          ∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν :=
        by rw [integral_mul_const]
  have hM0 : 0 ≤ ∫ ξ, M ξ ∂γ :=
    integral_nonneg fun ξ => by
      exact (abs_nonneg (g 0 ξ)).trans
        (Finset.le_sup' (fun i => |g i ξ|) (Finset.mem_univ 0))
  have houter := integral_mono hGvec.norm.integral_prod_left
    (hRvec.norm.integral_prod_left.const_mul (∫ ξ, M ξ ∂γ)) hslice
  calc
    (∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) =
        ∫ ω, ∫ ξ, ‖∑ i, (g i ξ) • X i ω‖ ∂γ ∂μ := by
      rw [integral_prod _ hGvec.norm]
      rfl
    _ ≤ ∫ ω, (∫ ξ, M ξ ∂γ) *
        (∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν) ∂μ := houter
    _ = (∫ ξ, M ξ ∂γ) *
        ∫ ω, ∫ η, ‖∑ i, (ε i η) • X i ω‖ ∂ν ∂μ :=
      by rw [integral_const_mul]
    _ = (∫ ξ, M ξ ∂γ) *
        ∫ z : Ω × Ωε, ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν := by
      rw [integral_prod _ hRvec.norm]
    _ = (∫ ξ, Finset.univ.sup' Finset.univ_nonempty
          (fun i => |g i ξ|) ∂γ) *
        ∫ z : Ω × Ωε, ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν := rfl

/-- Lower half of the corrected source lemma. The `log (2N)` normalization is safe also
at the smallest admissible finite family.

**Lean implementation helper.** -/
theorem gaussianSymmetrization_lower_safe
    {n : ℕ} {Ω Ωε Ωg E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : Fin (n + 2) → Ω → E}
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    (1 / (2 * Real.sqrt
        (2 * Real.log (2 * (n + 2 : ℝ))))) *
        (∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) ≤
      ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  let S : ℝ := Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ)))
  let R : ℝ := ∫ z : Ω × Ωε,
    ‖∑ i, (ε i z.2) • X i z.1‖ ∂μ.prod ν
  let G : ℝ := ∫ z : Ω × Ωg,
    ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ
  let A : ℝ := ∫ ω, ‖∑ i, X i ω‖ ∂μ
  have hN : (1 : ℝ) < 2 * (n + 2 : ℝ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hS : 0 < S := by
    dsimp [S]
    exact Real.sqrt_pos.mpr (mul_pos (by norm_num) (Real.log_pos hN))
  have hMle :
      (∫ ξ, Finset.univ.sup' Finset.univ_nonempty
        (fun i => |g i ξ|) ∂γ) ≤ S := by
    simpa [S] using HDP.Chapter2.exercise_2_38a_max_abs hgm hg
  have hGR : G ≤
      (∫ ξ, Finset.univ.sup' Finset.univ_nonempty
        (fun i => |g i ξ|) ∂γ) * R := by
    simpa [G, R] using gaussianSeries_le_gaussianMax_mul_rademacherSeries
      hXint hεm hε hεind hgm hg hgind
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact integral_nonneg fun _ => norm_nonneg _
  have hRle : R ≤ 2 * A := by
    have h := (symmetrization hXm hXint hX0 hXind hεm hε hεind).1
    dsimp [R, A]
    linarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun _ => norm_nonneg _
  have hGA : G ≤ 2 * S * A := by
    calc
      G ≤ (∫ ξ, Finset.univ.sup' Finset.univ_nonempty
          (fun i => |g i ξ|) ∂γ) * R := hGR
      _ ≤ S * R := mul_le_mul_of_nonneg_right hMle hR0
      _ ≤ S * (2 * A) := mul_le_mul_of_nonneg_left hRle hS.le
      _ = 2 * S * A := by ring
  have hdiv : G / (2 * S) ≤ A := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hS)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hGA
  change (1 / (2 * S)) * G ≤ A
  calc
    (1 / (2 * S)) * G = G / (2 * S) := by
      simp only [one_mul, div_eq_mul_inv]
      ring
    _ ≤ A := hdiv

/-- Gaussian symmetrization compares expected norms of a centered sum with a Gaussian-signed
sum, losing `sqrt(log N)`.

**Book Lemma 6.6.2.** -/
theorem gaussianSymmetrization
    {n : ℕ} {Ω Ωε Ωg E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : Fin (n + 2) → Ω → E}
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    ((1 / (2 * Real.sqrt
        (2 * Real.log (2 * (n + 2 : ℝ))))) *
        (∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) ≤
      ∫ ω, ‖∑ i, X i ω‖ ∂μ) ∧
    ((∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
      3 * ∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) := by
  exact ⟨gaussianSymmetrization_lower_safe hXm hXint hX0 hXind
      hεm hε hεind hgm hg hgind,
    gaussianSymmetrization_upper hXm hXint hX0 hXind
      hεm hε hεind hgm hg hgind⟩

/-- Bounds gaussian safe scale by two source scale.

**Lean implementation helper.** -/
lemma gaussianSafeScale_le_two_sourceScale (n : ℕ) :
    Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ))) ≤
      2 * Real.sqrt (Real.log (n + 2 : ℝ)) := by
  let N : ℝ := n + 2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN2 : 2 ≤ N := by dsimp [N]; linarith
  have hN0 : 0 < N := by linarith
  have hN1 : 1 < N := by dsimp [N]; linarith
  have hlogN0 : 0 ≤ Real.log N := (Real.log_pos hN1).le
  have hlog2le : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) hN2
  have hlogmul : Real.log (2 * N) = Real.log 2 + Real.log N := by
    rw [Real.log_mul (by norm_num) hN0.ne']
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [show (n + 2 : ℝ) = N by rfl, hlogmul]
    rw [show (2 * Real.sqrt (Real.log N)) ^ 2 =
      4 * Real.log N by
        rw [mul_pow, Real.sq_sqrt hlogN0]
        norm_num]
    nlinarith

/-- Source-shaped corrected form of the corresponding lemma. Since the API indexes the family by `Fin
(n+2)`, the necessary condition `N ≥ 2` is built into the type. The explicit absolute lower
constant is `c = 1/4`.

**Book Lemma 6.6.2.** -/
theorem gaussianSymmetrization_source
    {n : ℕ} {Ω Ωε Ωg E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E]
    {μ : Measure Ω} {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure γ]
    {X : Fin (n + 2) → Ω → E}
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXind : iIndepFun X μ)
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    (((1 / 4 : ℝ) / Real.sqrt (Real.log (n + 2 : ℝ))) *
        (∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) ≤
      ∫ ω, ‖∑ i, X i ω‖ ∂μ) ∧
    ((∫ ω, ‖∑ i, X i ω‖ ∂μ) ≤
      3 * ∫ z : Ω × Ωg, ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ) := by
  let S : ℝ := Real.sqrt (2 * Real.log (2 * (n + 2 : ℝ)))
  let L : ℝ := Real.sqrt (Real.log (n + 2 : ℝ))
  let G : ℝ := ∫ z : Ω × Ωg,
    ‖gaussianRandomVectorSum X g z‖ ∂μ.prod γ
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 < Real.log (n + 2 : ℝ) :=
    Real.log_pos (by linarith)
  have hL : 0 < L := by dsimp [L]; exact Real.sqrt_pos.mpr hlog
  have hS : 0 < S := by
    dsimp [S]
    exact Real.sqrt_pos.mpr (mul_pos (by norm_num)
      (Real.log_pos (by linarith)))
  have hscale : 2 * S ≤ 4 * L := by
    have h := gaussianSafeScale_le_two_sourceScale n
    dsimp [S, L]
    linarith
  have hcoef : 1 / (4 * L) ≤ 1 / (2 * S) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) hS) hscale
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact integral_nonneg fun _ => norm_nonneg _
  have hsafe := gaussianSymmetrization_lower_safe hXm hXint hX0 hXind
    hεm hε hεind hgm hg hgind
  have hlower : (1 / (4 * L)) * G ≤ ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
    calc
      (1 / (4 * L)) * G ≤ (1 / (2 * S)) * G :=
        mul_le_mul_of_nonneg_right hcoef hG0
      _ ≤ ∫ ω, ‖∑ i, X i ω‖ ∂μ := by simpa [S, G] using hsafe
  constructor
  · change ((1 / 4 : ℝ) / L) * G ≤ ∫ ω, ‖∑ i, X i ω‖ ∂μ
    have heq : (1 / 4 : ℝ) / L = 1 / (4 * L) := by
      field_simp
    rw [heq]
    exact hlower
  · exact gaussianSymmetrization_upper hXm hXint hX0 hXind
      hεm hε hεind hgm hg hgind

/-! ## Exercise 6.37: optimality of the logarithmic factor -/

/-- The `i`-th coordinate vector in the finite `ell-infinity` space.

**Lean implementation helper.** -/
def coordinateVector {N : ℕ} (i : Fin N) : Fin N → ℝ :=
  fun j => if i = j then 1 else 0

/-- Summing the coordinate basis vectors with coefficients `a i` reconstructs every coordinate
of `a`.

**Lean implementation helper.** -/
@[simp] lemma coordinateSeries_apply {N : ℕ} (a : Fin N → ℝ) (j : Fin N) :
    (∑ i, (a i) • coordinateVector i) j = a j := by
  classical
  simp [coordinateVector]

/-- The `l-infinity` norm of a coordinate expansion is the maximum absolute coefficient.

**Lean implementation helper.** -/
lemma norm_coordinateSeries {n : ℕ} (a : Fin (n + 2) → ℝ) :
    ‖∑ i, (a i) • coordinateVector i‖ =
      Finset.univ.sup' Finset.univ_nonempty (fun i => |a i|) := by
  have hfun : (∑ i, (a i) • coordinateVector i) = a := by
    funext j
    exact coordinateSeries_apply a j
  rw [hfun]
  exact linftyNorm_eq_finSup_abs a

/-- The concrete centered vectors used in the corresponding exercise.

**Lean implementation helper.** -/
def coordinateRademacherVector
    {n : ℕ} {Ωε : Type*} (ε : Fin (n + 2) → Ωε → ℝ)
    (i : Fin (n + 2)) (η : Ωε) : Fin (n + 2) → ℝ :=
  (ε i η) • coordinateVector i

/-- Coordinate Rademacher vectors have expected sum norm exactly one, while Gaussianizing them
gives exactly the expected absolute Gaussian maximum.

**Book Remark 6.6.3.** -/
theorem exercise_6_37_coordinate_witness
    {n : ℕ} {Ωε Ωg : Type*}
    [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {ε : Fin (n + 2) → Ωε → ℝ}
    {g : Fin (n + 2) → Ωg → ℝ}
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    ((∫ η, ‖∑ i, coordinateRademacherVector ε i η‖ ∂ν) = 1) ∧
      ((∫ z : Ωε × Ωg,
          ‖∑ i, (g i z.2) • coordinateRademacherVector ε i z.1‖
            ∂ν.prod γ) =
        ∫ ξ, Finset.univ.sup' Finset.univ_nonempty
          (fun i => |g i ξ|) ∂γ) := by
  have hεall : ∀ᵐ η ∂ν, ∀ i, ε i η = 1 ∨ ε i η = -1 :=
    ae_all_iff.mpr fun i => (hε i).ae_mem
  constructor
  · calc
      (∫ η, ‖∑ i, coordinateRademacherVector ε i η‖ ∂ν) =
          ∫ _η, (1 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hεall] with η hη
        rw [show (∑ i, coordinateRademacherVector ε i η) =
            ∑ i, (ε i η) • coordinateVector i by rfl,
          norm_coordinateSeries]
        have habs : ∀ i, |ε i η| = 1 := by
          intro i
          rcases hη i with hi | hi <;> simp [hi]
        simp_rw [habs]
        simp
      _ = 1 := by simp
  · have hLaw :=
      identDistrib_rademacher_mul_abs_standardGaussian_family
        hεm hε hεind hgm hg hgind
    let F : (Fin (n + 2) → ℝ) → ℝ :=
      fun a => ‖∑ i, (a i) • coordinateVector i‖
    have hF : Measurable F := (by fun_prop : Continuous F).measurable
    have hEq := (hLaw.comp hF).integral_eq
    have hleft :
        (∫ z : Ωε × Ωg,
          ‖∑ i, (g i z.2) • coordinateRademacherVector ε i z.1‖
            ∂ν.prod γ) =
          ∫ z : Ωε × Ωg, Finset.univ.sup' Finset.univ_nonempty
            (fun i => |g i z.2|) ∂ν.prod γ := by
      simpa [F, Function.comp_def, coordinateRademacherVector,
        smul_smul, mul_comm, abs_mul, norm_coordinateSeries] using hEq
    have hsnd :
        (∫ z : Ωε × Ωg, Finset.univ.sup' Finset.univ_nonempty
          (fun i => |g i z.2|) ∂ν.prod γ) =
          ∫ ξ, Finset.univ.sup' Finset.univ_nonempty
            (fun i => |g i ξ|) ∂γ := by
      let q : Ωg → ℝ := fun ξ =>
        Finset.univ.sup' Finset.univ_nonempty (fun i => |g i ξ|)
      change (∫ z : Ωε × Ωg, q z.2 ∂ν.prod γ) = ∫ ξ, q ξ ∂γ
      rw [integral_fun_snd]
      simp
    exact hleft.trans hsnd

/-- For the coordinate Rademacher construction, the ordinary expected norm is identically one,
whereas the Gaussianized expected norm divided by `sqrt (2 log N)` tends to one. Consequently no
dimension-free replacement for the `sqrt (log N)` factor in the corresponding lemma is possible.

**Book Remark 6.6.3.** -/
theorem exercise_6_37_gaussianSymmetrization_log_optimal
    {Ωε Ωg : Type*} [MeasurableSpace Ωε] [MeasurableSpace Ωg]
    {ν : Measure Ωε} {γ : Measure Ωg}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {ε : ℕ → Ωε → ℝ} {g : ℕ → Ωg → ℝ}
    (hεm : ∀ i, Measurable (ε i))
    (hε : ∀ i, HDP.IsRademacher (ε i) ν)
    (hεind : iIndepFun ε ν)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) γ)
    (hgind : iIndepFun g γ) :
    (∀ n,
      (∫ η, ‖∑ i : Fin (n + 2),
        coordinateRademacherVector (fun j : Fin (n + 2) => ε j) i η‖ ∂ν) = 1) ∧
    Tendsto (fun n =>
      (∫ z : Ωε × Ωg,
        ‖∑ i : Fin (n + 2), (g i z.2) •
          coordinateRademacherVector (fun j : Fin (n + 2) => ε j) i z.1‖
          ∂ν.prod γ) / HDP.Chapter2.gaussianMaxScale n)
      atTop (𝓝 1) := by
  have hεind_fin (n : ℕ) :
      iIndepFun (fun i : Fin (n + 2) => ε i) ν :=
    hεind.precomp Fin.val_injective
  have hgind_fin (n : ℕ) :
      iIndepFun (fun i : Fin (n + 2) => g i) γ :=
    hgind.precomp Fin.val_injective
  have hwitness (n : ℕ) := exercise_6_37_coordinate_witness
    (ε := fun i : Fin (n + 2) => ε i)
    (g := fun i : Fin (n + 2) => g i)
    (fun i => hεm i) (fun i => hε i) (hεind_fin n)
    (fun i => hgm i) (fun i => hg i) (hgind_fin n)
  constructor
  · intro n
    exact (hwitness n).1
  · have hbase := HDP.Chapter2.exercise_2_38b_max_abs hgm hg hgind
    apply hbase.congr'
    filter_upwards with n
    rw [(hwitness n).2]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    exact HDP.Chapter2.gaussianMaxAbsSeq_eq_finSup g n ξ

end

end HDP.Chapter6

end Source_14_GaussianSymmetrization
