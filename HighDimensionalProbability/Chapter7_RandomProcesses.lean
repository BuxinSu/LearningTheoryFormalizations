/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import HighDimensionalProbability.Chapter6_QuadraticFormsSymmetrizationContraction
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import HighDimensionalProbability.Chapter4_RandomMatrices
import HighDimensionalProbability.Prelude.MatrixConcentrationReal
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ProductMeasure
import HighDimensionalProbability.Prelude.MetricEntropy
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BrownianMotion.Basic
import HighDimensionalProbability.Prelude.Sphere
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Chapter 7 — Random Processes

## Contents

- §7.1 Random processes, covariance, increments, and Gaussian processes
  - Definition 7.1.1 and equation (7.1): processes and their canonical increments
  - Example 7.1.6: Brownian and random-walk `L²` increment metrics are square-root time
  - Theorem 7.1.11: concentration of an arbitrary finite Gaussian process maximum
  - Definitions 7.1.9 and Lemma 7.1.12: finite Gaussian laws and affine canonical representation
- §7.2 Gaussian comparison
  - Lemmas 7.2.3–7.2.5: Gaussian integration by parts and interpolation
  - Theorems 7.2.2, 7.2.8, and 7.2.9: Slepian, Sudakov–Fernique, and Gordon
- §7.3 Sharp Gaussian-matrix bounds
  - Theorem 7.3.1 and Corollary 7.3.2: extremal singular values and condition numbers
- §7.4 Sudakov minoration and metric entropy
  - Theorem 7.4.1 and Corollaries 7.4.2–7.4.3
- §7.5 Gaussian and spherical width
  - Definitions 7.5.1, 7.5.4, 7.5.9, and 7.5.12
  - Width calculus, examples, nuclear norm, Gaussian complexity, and effective dimension
- §7.6 Random projections of sets
  - Equation (7.21): projection of the unit ball onto a nonzero subspace has diameter two
  - Theorem 7.6.1 and its Gaussian and finite-set variants

The detailed entries below identify the chapter's key source-facing definitions and
results by the numbering printed in the second-edition book PDF.
-/

/-! ## Material formerly in `01_RandomProcesses.lean` -/

section Source_01_RandomProcesses

/-!
# Book Chapter 7, §7.1.1: random processes, covariance, and increments

The book works with real-valued processes.  The real increment below is used
only together with `MemLp` hypotheses; Mathlib's extended `eLpNorm` remains the
authoritative interface when finiteness is not known.

Examples 7.1.2--7.1.6 are explanatory examples (finite vectors, random walks,
Brownian motion, and random fields).  They introduce no load-bearing theorem,
so this core module records them here rather than manufacturing unused models.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HDP

/-- **Book Definition 7.1.1.** A real random process indexed by `T`. -/
abbrev RandomProcess (T Ω : Type*) := T → Ω → ℝ

/-- A process is centered when every marginal has expectation zero.

**Lean implementation helper.** -/
def IsCenteredProcess {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : RandomProcess T Ω) (μ : Measure Ω) : Prop :=
  ∀ t, ∫ ω, X t ω ∂μ = 0

/-- Every marginal of the process has a finite second moment.

**Lean implementation helper.** -/
def IsL2Process {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : RandomProcess T Ω) (μ : Measure Ω) : Prop :=
  ∀ t, MemLp (X t) 2 μ

/-- The covariance function is `E[X_t X_s]` for centered processes. The covariance function of a real process.

**Book Section 7.1.1, covariance display.** -/
noncomputable def processCovariance {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : RandomProcess T Ω) (μ : Measure Ω) (s t : T) : ℝ :=
  cov[X s, X t; μ]

/-- Canonical `L2` increment distance. Equation (7.1), the real `L²` increment of a process. All results using this real-valued wrapper carry the `MemLp` hypotheses which
ensure that the corresponding extended norm is finite.

**Book Equation (7.1).** -/
noncomputable def processIncrement {T Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : RandomProcess T Ω) (μ : Measure Ω) (s t : T) : ℝ :=
  Chapter1.lpNormRV (fun ω => X s ω - X t ω) 2 μ

variable {T Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} {X : RandomProcess T Ω}

/-- Canonical `L2` increment distance. The source's real increment agrees with Mathlib's finite real `L²` norm.

**Book Equation (7.1).** -/
theorem processIncrement_eq_lpNorm {s t : T}
    (hs : MemLp (X s) 2 μ) (ht : MemLp (X t) 2 μ) :
    processIncrement X μ s t = lpNorm (fun ω => X s ω - X t ω) 2 μ := by
  change Chapter1.lpNormRV (X s - X t) 2 μ = lpNorm (X s - X t) 2 μ
  have hst : MemLp (X s - X t) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hs.sub ht
  rw [Chapter1.lpNormRV_eq_toReal_eLpNorm (by norm_num) hst]
  simpa using toReal_eLpNorm hst.aestronglyMeasurable

/-- A finite real increment is nonnegative.

**Lean implementation helper.** -/
theorem processIncrement_nonneg {s t : T}
    (hs : MemLp (X s) 2 μ) (ht : MemLp (X t) 2 μ) :
    0 ≤ processIncrement X μ s t := by
  rw [processIncrement_eq_lpNorm hs ht]
  exact lpNorm_nonneg

/-- The increment of a square-integrable process from an index to itself is zero.

**Lean implementation helper.** -/
@[simp]
theorem processIncrement_self (s : T) (hs : MemLp (X s) 2 μ) :
    processIncrement X μ s s = 0 := by
  rw [processIncrement_eq_lpNorm hs hs]
  simp

/-- The L² process increment is symmetric in its two indices.

**Lean implementation helper.** -/
theorem processIncrement_comm {s t : T}
    (hs : MemLp (X s) 2 μ) (ht : MemLp (X t) 2 μ) :
    processIncrement X μ s t = processIncrement X μ t s := by
  rw [processIncrement_eq_lpNorm hs ht, processIncrement_eq_lpNorm ht hs]
  exact lpNorm_sub_comm _ _ _ _

/-- Minkowski's inequality gives the triangle inequality for the canonical
pseudometric.

**Lean implementation helper.** -/
theorem processIncrement_triangle (hX : IsL2Process X μ) (r s t : T) :
    processIncrement X μ r t ≤
      processIncrement X μ r s + processIncrement X μ s t := by
  rw [processIncrement_eq_lpNorm (hX r) (hX t),
    processIncrement_eq_lpNorm (hX r) (hX s),
    processIncrement_eq_lpNorm (hX s) (hX t)]
  exact lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hX r) (hX s) (by norm_num)

/-- `L2` increments obey zero, symmetry, and the triangle inequality. The increment obeys the pseudometric
laws. Separation is deliberately absent: distinct indices may represent the
same random variable almost everywhere.

**Book Remark 7.1.7.** -/
theorem processIncrement_pseudometric_laws (hX : IsL2Process X μ) :
    (∀ t, processIncrement X μ t t = 0) ∧
      (∀ s t, processIncrement X μ s t = processIncrement X μ t s) ∧
      (∀ r s t, processIncrement X μ r t ≤
        processIncrement X μ r s + processIncrement X μ s t) := by
  exact ⟨fun t => processIncrement_self t (hX t),
    fun s t => processIncrement_comm (hX s) (hX t),
    processIncrement_triangle hX⟩

/-- Process covariance is symmetric in its two indices.

**Lean implementation helper.** -/
theorem processCovariance_comm (s t : T) :
    processCovariance X μ s t = processCovariance X μ t s := by
  exact covariance_comm _ _

/-- For a centered process, covariance is the uncentered product moment used
in the prose immediately before (7.1).

**Book Equation (7.1).** -/
theorem processCovariance_eq_integral_mul
    (hcenter : IsCenteredProcess X μ) (s t : T) :
    processCovariance X μ s t = ∫ ω, X s ω * X t ω ∂μ := by
  simp [processCovariance, Chapter1.covariance_def', hcenter s, hcenter t]

/-- Squared increments equal `Sigma(t,t)-2 Sigma(t,s)+Sigma(s,s)`; with a zero coordinate, increments recover covariance. Expanding the square recovers increments from the
covariance function.

**Book Remark 7.1.8.** -/
theorem processIncrement_sq_eq_covariance [IsProbabilityMeasure μ]
    (hX : IsL2Process X μ) (hcenter : IsCenteredProcess X μ) (s t : T) :
    processIncrement X μ s t ^ 2 =
      processCovariance X μ s s - 2 * processCovariance X μ s t +
        processCovariance X μ t t := by
  let D : Ω → ℝ := fun ω => X s ω - X t ω
  have hD : MemLp D 2 μ := (hX s).sub (hX t)
  have hDmean : ∫ ω, D ω ∂μ = 0 := by
    rw [integral_sub (hX s |>.integrable one_le_two)
      (hX t |>.integrable one_le_two), hcenter s, hcenter t, sub_self]
  calc
    processIncrement X μ s t ^ 2 = Chapter1.l2InnerRV D D μ := by
      exact Chapter1.sq_lpNormRV_two_eq_l2InnerRV hD
    _ = cov[D, D; μ] := by
      simp [Chapter1.l2InnerRV, Chapter1.covariance_def', hDmean]
    _ = cov[X s, X s; μ] - cov[X s, X t; μ] -
          cov[X t, X s; μ] + cov[X t, X t; μ] := by
      exact covariance_fun_sub_fun_sub (hX s) (hX t) (hX s) (hX t)
    _ = processCovariance X μ s s - 2 * processCovariance X μ s t +
          processCovariance X μ t t := by
      rw [covariance_comm (X t) (X s)]
      simp only [processCovariance]
      ring

/-- Squared increments equal `Sigma(t,t)-2 Sigma(t,s)+Sigma(s,s)`; with a zero coordinate, increments recover covariance. If the zero random variable is
one of the process coordinates, the covariance is recovered from increments
by polarization.

**Book Remark 7.1.8.** -/
theorem exercise_7_1a_covariance_from_zero [IsProbabilityMeasure μ]
    (hX : IsL2Process X μ) (hcenter : IsCenteredProcess X μ)
    {z : T} (hzero : X z = 0) (s t : T) :
    processCovariance X μ s t =
      (processIncrement X μ s z ^ 2 + processIncrement X μ t z ^ 2 -
        processIncrement X μ s t ^ 2) / 2 := by
  have hsz := processIncrement_sq_eq_covariance hX hcenter s z
  have htz := processIncrement_sq_eq_covariance hX hcenter t z
  have hst := processIncrement_sq_eq_covariance hX hcenter s t
  simp [hzero, processCovariance] at hsz htz
  simp only [processCovariance] at hst ⊢
  linarith

end HDP

namespace HDP.Chapter7

noncomputable section

/-- The canonical `L²` increment metric of a standard Brownian motion is the
square root of elapsed time.

**Book Example 7.1.6.** -/
theorem brownian_processIncrement
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HDP.processIncrement B P t s =
      Real.sqrt ((t : ℝ) - (s : ℝ)) := by
  have hL2 : HDP.IsL2Process B P := fun u =>
    (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hcenter : ∀ u, ∫ ω, B u ω ∂P = 0 := hB.integral_eval
  have hsq := HDP.processIncrement_sq_eq_covariance hL2 hcenter t s
  have hcov_ts : HDP.processCovariance B P t s = (s : ℝ) := by
    simp [HDP.processCovariance, hB.covariance_eval, min_eq_right hst]
  have hcov_tt : HDP.processCovariance B P t t = (t : ℝ) := by
    simp [HDP.processCovariance, hB.covariance_eval]
  have hcov_ss : HDP.processCovariance B P s s = (s : ℝ) := by
    simp [HDP.processCovariance, hB.covariance_eval]
  rw [hcov_tt, hcov_ts, hcov_ss] at hsq
  have hnonneg := HDP.processIncrement_nonneg (hL2 t) (hL2 s)
  apply (Real.sqrt_sq hnonneg).symm.trans
  congr 1
  rw [hsq]
  ring

/-- The partial-sum process generated by a sequence of increments.

**Book Example 7.1.3.** -/
def randomWalkProcess {Ω : Type*} (Z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => ∑ i ∈ Finset.range n, Z i ω

/-- A random walk with independent, centered, unit-variance increments has
canonical `L²` increment metric `d(n,m)=√(n-m)` for `m≤n`.

**Book Example 7.1.6.** -/
theorem randomWalk_processIncrement
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 P)
    (hcenter : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (hvar : ∀ i, Var[Z i; P] = 1)
    (hIndep : iIndepFun Z P) {m n : ℕ} (hmn : m ≤ n) :
    HDP.processIncrement (randomWalkProcess Z) P n m =
      Real.sqrt ((n - m : ℕ) : ℝ) := by
  let I := Finset.Ico m n
  let S : Ω → ℝ := fun ω => ∑ i ∈ I, Z i ω
  have hdiff :
      (fun ω => randomWalkProcess Z n ω - randomWalkProcess Z m ω) = S := by
    funext ω
    simp only [randomWalkProcess, S, I]
    rw [Finset.sum_Ico_eq_sub _ hmn]
  have hS : MemLp S 2 P := by
    have h := memLp_finsetSum' I (fun i _ => hZ i)
    convert h using 1
    ext ω
    simp [S]
  have hSmean : ∫ ω, S ω ∂P = 0 := by
    simp only [S]
    rw [integral_finset_sum I (fun i _ => (hZ i).integrable (by norm_num))]
    simp [hcenter]
  have hSvar : Var[S; P] = ((n - m : ℕ) : ℝ) := by
    have hpair : Set.Pairwise (↑I : Set ℕ)
        (fun i j => IndepFun (Z i) (Z j) P) := by
      intro i _ j _ hij
      exact hIndep.indepFun hij
    have hv := IndepFun.variance_sum
      (μ := P) (X := Z) (s := I) (fun i _ => hZ i) hpair
    change Var[S; P] = _
    rw [show S = ∑ i ∈ I, Z i by
      funext ω
      simp [S]]
    rw [hv]
    simp [I, hvar, hmn]
  change Chapter1.lpNormRV
      (fun ω => randomWalkProcess Z n ω - randomWalkProcess Z m ω) 2 P = _
  rw [hdiff]
  calc
    Chapter1.lpNormRV S 2 P =
        Chapter1.lpNormRV
          (fun ω => S ω - ∫ ω', S ω' ∂P) 2 P := by
      rw [hSmean]
      simp
    _ = Real.sqrt (Var[S; P]) :=
      (Chapter1.stdDev_eq_lpNormRV hS).symm
    _ = Real.sqrt ((n - m : ℕ) : ℝ) := by rw [hSvar]

/-! ## Exercise 7.3: Talagrand's contraction principle -/

/-- The finite supremum form of the elementary two-sign contraction step.
This slightly more general `A,b` formulation is used in the coordinate
induction below.

**Lean implementation helper.** -/
private lemma finite_sup_contraction_pair {ι : Type*}
    (T : Finset ι) (hT : T.Nonempty) (A b : ι → ℝ) (φ : ℝ → ℝ)
    (hφ : LipschitzWith 1 φ) :
    T.sup' hT (fun t => A t + φ (b t)) +
        T.sup' hT (fun t => A t - φ (b t)) ≤
      T.sup' hT (fun t => A t + b t) +
        T.sup' hT (fun t => A t - b t) := by
  obtain ⟨u, hu, huMax⟩ :=
    Finset.exists_mem_eq_sup' hT (fun t => A t + φ (b t))
  obtain ⟨v, hv, hvMax⟩ :=
    Finset.exists_mem_eq_sup' hT (fun t => A t - φ (b t))
  rw [huMax, hvMax]
  have hLip : |φ (b u) - φ (b v)| ≤ |b u - b v| := by
    simpa [Real.norm_eq_abs] using hφ.norm_sub_le (b u) (b v)
  by_cases huv : b v ≤ b u
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)] at hLip
    calc
      (A u + φ (b u)) + (A v - φ (b v))
          ≤ (A u + b u) + (A v - b v) := by
            linarith [le_abs_self (φ (b u) - φ (b v))]
      _ ≤ T.sup' hT (fun t => A t + b t) +
          T.sup' hT (fun t => A t - b t) :=
        add_le_add
          (Finset.le_sup' (fun t => A t + b t) hu)
          (Finset.le_sup' (fun t => A t - b t) hv)
  · have huv' : b u ≤ b v := le_of_not_ge huv
    rw [abs_of_nonpos (sub_nonpos.mpr huv')] at hLip
    calc
      (A u + φ (b u)) + (A v - φ (b v))
          ≤ (A v + b v) + (A u - b u) := by
            linarith [le_abs_self (φ (b u) - φ (b v))]
      _ ≤ T.sup' hT (fun t => A t + b t) +
          T.sup' hT (fun t => A t - b t) :=
        add_le_add
          (Finset.le_sup' (fun t => A t + b t) hv)
          (Finset.le_sup' (fun t => A t - b t) hu)

/-- Talagrand contraction for finite random processes. For a finite nonempty subset of `ℝ²`, pairing
the two signs in the second coordinate cannot increase the sum of the two
suprema after applying a contraction. A finite set is the exact form needed
for the fully formalized expectation argument.

**Book Exercise 7.3.** -/
theorem exercise_7_3a_finite_sup_contraction
    (T : Finset (Fin 2 → ℝ)) (hT : T.Nonempty)
    (φ : ℝ → ℝ) (hφ : LipschitzWith 1 φ) :
    T.sup' hT (fun t => t 0 + φ (t 1)) +
        T.sup' hT (fun t => t 0 - φ (t 1)) ≤
      T.sup' hT (fun t => t 0 + t 1) +
        T.sup' hT (fun t => t 0 - t 1) := by
  exact finite_sup_contraction_pair T hT (fun t => t 0) (fun t => t 1) φ hφ

/-- The finite Rademacher supremum associated with coordinate maps `ψ`.
The argument is a sign vector in the canonical product space from Chapter 6.

**Lean implementation helper.** -/
def finiteRademacherSupremum {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (ε : Fin n → ℝ) : ℝ :=
  T.sup' hT fun t => ∑ j, ε j * ψ j (t j)

/-- Defines the multiplier that negates one selected coordinate and leaves every other coordinate unchanged.

**Lean implementation helper.** -/
private def signFlipMultiplier {n : ℕ} (i j : Fin n) : ℝ :=
  if j = i then -1 else 1

/-- Flips one selected coordinate of a sign vector.

**Lean implementation helper.** -/
private def signFlip {n : ℕ} (i : Fin n) (ε : Fin n → ℝ) : Fin n → ℝ :=
  fun j => signFlipMultiplier i j * ε j

/-- Splits a finite weighted sum into the selected coordinate and the sum over all remaining coordinates.

**Lean implementation helper.** -/
private lemma sum_separate_coordinate {n : ℕ} (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε t : Fin n → ℝ) :
    (∑ j, ε j * ψ j (t j)) =
      (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) +
        ε i * ψ i (t i) := by
  exact (Finset.sum_erase_add
    (s := Finset.univ) (f := fun j => ε j * ψ j (t j))
    (Finset.mem_univ i)).symm

/-- After flipping one sign, splits the weighted sum into the unchanged coordinates minus the selected term.

**Lean implementation helper.** -/
private lemma sum_signFlip_separate_coordinate {n : ℕ} (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε t : Fin n → ℝ) :
    (∑ j, signFlip i ε j * ψ j (t j)) =
      (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) -
        ε i * ψ i (t i) := by
  have hrest :
      (∑ j ∈ Finset.univ.erase i, signFlip i ε j * ψ j (t j)) =
        ∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [signFlip, signFlipMultiplier, hji]
  calc
    (∑ j, signFlip i ε j * ψ j (t j)) =
        (∑ j ∈ Finset.univ.erase i, signFlip i ε j * ψ j (t j)) +
          signFlip i ε i * ψ i (t i) :=
      sum_separate_coordinate i ψ (signFlip i ε) t
    _ = (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) -
        ε i * ψ i (t i) := by
      rw [hrest]
      have hself : signFlip i ε i = -ε i := by
        simp [signFlip, signFlipMultiplier]
      rw [hself]
      ring

/-- After replacing one contraction by the identity, separates the selected coordinate from the remaining sum.

**Lean implementation helper.** -/
private lemma sum_update_separate_coordinate {n : ℕ} (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε t : Fin n → ℝ) :
    (∑ j, ε j * (Function.update ψ i id) j (t j)) =
      (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) + ε i * t i := by
  have hrest :
      (∑ j ∈ Finset.univ.erase i,
        ε j * (Function.update ψ i id) j (t j)) =
        ∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  calc
    (∑ j, ε j * (Function.update ψ i id) j (t j)) =
        (∑ j ∈ Finset.univ.erase i,
          ε j * (Function.update ψ i id) j (t j)) +
          ε i * (Function.update ψ i id) i (t i) :=
      sum_separate_coordinate i (Function.update ψ i id) ε t
    _ = (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) + ε i * t i := by
      rw [hrest]
      simp

/-- After an identity update and a sign flip, separates the selected coordinate with a negative sign.

**Lean implementation helper.** -/
private lemma sum_update_signFlip_separate_coordinate {n : ℕ} (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε t : Fin n → ℝ) :
    (∑ j, signFlip i ε j * (Function.update ψ i id) j (t j)) =
      (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) - ε i * t i := by
  rw [sum_signFlip_separate_coordinate]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  · simp

/-- Rewrites the finite Rademacher supremum by separating one coordinate from the remaining sum.

**Lean implementation helper.** -/
private lemma finiteRademacherSupremum_separate {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty) (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε : Fin n → ℝ) :
    finiteRademacherSupremum T hT ψ ε = T.sup' hT (fun t =>
      (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) + ε i * ψ i (t i)) := by
  unfold finiteRademacherSupremum
  apply Finset.sup'_congr hT rfl
  intro t _
  exact sum_separate_coordinate i ψ ε t

/-- Rewrites the sign-flipped Rademacher supremum with the selected coordinate appearing negatively.

**Lean implementation helper.** -/
private lemma finiteRademacherSupremum_signFlip_separate {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty) (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε : Fin n → ℝ) :
    finiteRademacherSupremum T hT ψ (signFlip i ε) = T.sup' hT (fun t =>
      (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) - ε i * ψ i (t i)) := by
  unfold finiteRademacherSupremum
  apply Finset.sup'_congr hT rfl
  intro t _
  exact sum_signFlip_separate_coordinate i ψ ε t

/-- Rewrites the Rademacher supremum after replacing one contraction by the identity.

**Lean implementation helper.** -/
private lemma finiteRademacherSupremum_update_separate {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty) (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε : Fin n → ℝ) :
    finiteRademacherSupremum T hT (Function.update ψ i id) ε =
      T.sup' hT (fun t =>
        (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) + ε i * t i) := by
  unfold finiteRademacherSupremum
  apply Finset.sup'_congr hT rfl
  intro t _
  exact sum_update_separate_coordinate i ψ ε t

/-- Rewrites the sign-flipped supremum after replacing one contraction by the identity.

**Lean implementation helper.** -/
private lemma finiteRademacherSupremum_update_signFlip_separate {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty) (i : Fin n)
    (ψ : Fin n → ℝ → ℝ) (ε : Fin n → ℝ) :
    finiteRademacherSupremum T hT (Function.update ψ i id) (signFlip i ε) =
      T.sup' hT (fun t =>
        (∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)) - ε i * t i) := by
  unfold finiteRademacherSupremum
  apply Finset.sup'_congr hT rfl
  intro t _
  exact sum_update_signFlip_separate_coordinate i ψ ε t

/-- Bounds the sum of a supremum and its one-coordinate sign flip by the corresponding pair with that contraction removed.

**Lean implementation helper.** -/
private lemma finiteRademacherSupremum_pair_le {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (i : Fin n) (hψ : LipschitzWith 1 (ψ i))
    (ε : Fin n → ℝ) (hε : ε i = -1 ∨ ε i = 1) :
    finiteRademacherSupremum T hT ψ ε +
        finiteRademacherSupremum T hT ψ (signFlip i ε) ≤
      finiteRademacherSupremum T hT (Function.update ψ i id) ε +
        finiteRademacherSupremum T hT (Function.update ψ i id) (signFlip i ε) := by
  let A : (Fin n → ℝ) → ℝ := fun t =>
    ∑ j ∈ Finset.univ.erase i, ε j * ψ j (t j)
  have hp := finite_sup_contraction_pair T hT A (fun t => t i) (ψ i) hψ
  rcases hε with hi | hi
  · rw [finiteRademacherSupremum_separate,
      finiteRademacherSupremum_signFlip_separate,
      finiteRademacherSupremum_update_separate,
      finiteRademacherSupremum_update_signFlip_separate, hi]
    dsimp only [A] at hp
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp
  · rw [finiteRademacherSupremum_separate,
      finiteRademacherSupremum_signFlip_separate,
      finiteRademacherSupremum_update_separate,
      finiteRademacherSupremum_update_signFlip_separate, hi]
    dsimp only [A] at hp
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp

/-- The finite Rademacher supremum is measurable.

**Lean implementation helper.** -/
private lemma measurable_finiteRademacherSupremum {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty)
    (ψ : Fin n → ℝ → ℝ) : Measurable (finiteRademacherSupremum T hT ψ) := by
  unfold finiteRademacherSupremum
  have h : Measurable (T.sup' hT
      (fun t (ε : Fin n → ℝ) => ∑ j, ε j * ψ j (t j))) := by
    apply Finset.measurable_sup' hT
    intro t _
    apply Finset.measurable_sum
    intro j _
    exact (measurable_pi_apply j).mul measurable_const
  have heq : T.sup' hT
      (fun t (ε : Fin n → ℝ) => ∑ j, ε j * ψ j (t j)) =
      (fun ε => T.sup' hT (fun t => ∑ j, ε j * ψ j (t j))) := by
    funext ε
    simp only [Finset.sup'_apply]
  rwa [heq] at h

/-- The finite Rademacher supremum is integrable under the uniform sign measure.

**Lean implementation helper.** -/
private lemma integrable_finiteRademacherSupremum {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty)
    (ψ : Fin n → ℝ → ℝ) :
    Integrable (finiteRademacherSupremum T hT ψ)
      (HDP.Chapter6.matrixSignMeasure n) := by
  let μ := HDP.Chapter6.matrixSignMeasure n
  let f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun t ε =>
    ∑ j, ε j * ψ j (t j)
  have hf (t : Fin n → ℝ) : Integrable (f t) μ := by
    apply integrable_finsetSum Finset.univ
    intro j _
    exact (((HDP.Chapter6.matrixSignCoordinate_isRademacherHDP j).memLp 1).integrable
      le_rfl).mul_const (ψ j (t j))
  have hbound : Integrable (fun ε => ∑ t ∈ T, |f t ε|) μ := by
    apply integrable_finsetSum T
    intro t _
    exact (hf t).abs
  refine hbound.mono'
    (measurable_finiteRademacherSupremum T hT ψ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ε => ?_)
  rw [Real.norm_eq_abs]
  obtain ⟨t, ht, htMax⟩ :=
    Finset.exists_mem_eq_sup' hT (f := fun t => f t ε)
  rw [show finiteRademacherSupremum T hT ψ ε =
      T.sup' hT (fun t => f t ε) by rfl, htMax]
  exact Finset.single_le_sum (fun u _ => abs_nonneg (f u ε)) ht

/-- Flipping one Rademacher coordinate preserves the joint sign distribution.

**Lean implementation helper.** -/
private lemma signFlip_identDistrib {n : ℕ} (i : Fin n) :
    IdentDistrib (signFlip i) id
      (HDP.Chapter6.matrixSignMeasure n) (HDP.Chapter6.matrixSignMeasure n) := by
  let s : Fin n → ℝ := fun j => signFlipMultiplier i j
  have hs : ∀ j, s j = -1 ∨ s j = 1 := by
    intro j
    by_cases hji : j = i
    · left
      simp [s, signFlipMultiplier, hji]
    · right
      simp [s, signFlipMultiplier, hji]
  have hid := HDP.Chapter6.identDistrib_sign_mul_rademacherFamily
    (μ := HDP.Chapter6.matrixSignMeasure n)
    (ε := fun j => HDP.Chapter6.matrixSignCoordinate j)
    (fun j => HDP.Chapter6.matrixSignCoordinate_isRademacherHDP j)
    HDP.Chapter6.matrixSignCoordinate_independent hs
  change IdentDistrib
    (fun ω j => s j * HDP.Chapter6.matrixSignCoordinate j ω)
    (fun ω j => HDP.Chapter6.matrixSignCoordinate j ω)
    (HDP.Chapter6.matrixSignMeasure n) (HDP.Chapter6.matrixSignMeasure n)
  exact hid

/-- Replacing one 1-Lipschitz contraction by the identity can only increase the expected finite Rademacher supremum.

**Lean implementation helper.** -/
private lemma one_coordinate_expected_contraction {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (i : Fin n) (hψ : LipschitzWith 1 (ψ i)) :
    (∫ ε, finiteRademacherSupremum T hT ψ ε
        ∂HDP.Chapter6.matrixSignMeasure n) ≤
      ∫ ε, finiteRademacherSupremum T hT (Function.update ψ i id) ε
        ∂HDP.Chapter6.matrixSignMeasure n := by
  let μ := HDP.Chapter6.matrixSignMeasure n
  let F : (Fin n → ℝ) → ℝ := finiteRademacherSupremum T hT ψ
  let G : (Fin n → ℝ) → ℝ :=
    finiteRademacherSupremum T hT (Function.update ψ i id)
  have hFm : Measurable F := measurable_finiteRademacherSupremum T hT ψ
  have hGm : Measurable G :=
    measurable_finiteRademacherSupremum T hT (Function.update ψ i id)
  have hFi : Integrable F μ := integrable_finiteRademacherSupremum T hT ψ
  have hGi : Integrable G μ :=
    integrable_finiteRademacherSupremum T hT (Function.update ψ i id)
  have hidF := (signFlip_identDistrib i).comp hFm
  have hidG := (signFlip_identDistrib i).comp hGm
  have hFflip : Integrable (fun ε => F (signFlip i ε)) μ := by
    exact hidF.integrable_iff.mpr hFi
  have hGflip : Integrable (fun ε => G (signFlip i ε)) μ := by
    exact hidG.integrable_iff.mpr hGi
  have hpair : ∀ᵐ ε ∂μ,
      F ε + F (signFlip i ε) ≤ G ε + G (signFlip i ε) := by
    filter_upwards
      [HDP.Chapter6.matrixSignCoordinate_isRademacherHDP i |>.ae_mem]
      with ε hε
    apply finiteRademacherSupremum_pair_le T hT ψ i hψ ε
    exact hε.elim (fun h => Or.inr h) (fun h => Or.inl h)
  have hint := integral_mono_ae (hFi.add hFflip) (hGi.add hGflip) hpair
  have hidFint : (∫ ε, F (signFlip i ε) ∂μ) = ∫ ε, F ε ∂μ := by
    simpa [Function.comp_def] using hidF.integral_eq
  have hidGint : (∫ ε, G (signFlip i ε) ∂μ) = ∫ ε, G ε ∂μ := by
    simpa [Function.comp_def] using hidG.integral_eq
  change (∫ ε, F ε + F (signFlip i ε) ∂μ) ≤
    ∫ ε, G ε + G (signFlip i ε) ∂μ at hint
  rw [integral_add hFi hFflip, integral_add hGi hGflip,
    hidFint, hidGint] at hint
  change (∫ ε, finiteRademacherSupremum T hT ψ ε ∂_) ≤
    ∫ ε, finiteRademacherSupremum T hT (Function.update ψ i id) ε ∂_
  change (∫ ε, F ε ∂μ) ≤ ∫ ε, G ε ∂μ
  linarith

/-- Replaces the contractions indexed by a finite set with the identity map.

**Lean implementation helper.** -/
private def contractedOn {n : ℕ} (ψ : Fin n → ℝ → ℝ)
    (s : Finset (Fin n)) : Fin n → ℝ → ℝ :=
  fun i => if i ∈ s then id else ψ i

/-- Adding an index to the contracted set is the same as updating that coordinate to the identity map.

**Lean implementation helper.** -/
private lemma contractedOn_insert {n : ℕ} (ψ : Fin n → ℝ → ℝ)
    (s : Finset (Fin n)) (i : Fin n) :
    contractedOn ψ (insert i s) = Function.update (contractedOn ψ s) i id := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [contractedOn]
  · simp [contractedOn, hji]

/-- Talagrand contraction for Rademacher processes.

**Book Equation (7.25), Exercise 7.3.** -/
theorem exercise_7_3_talagrand_contraction {n : ℕ}
    (T : Finset (Fin n → ℝ)) (hT : T.Nonempty)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ i, LipschitzWith 1 (φ i)) :
    (∫ ε, T.sup' hT (fun t => ∑ i, ε i * φ i (t i))
        ∂HDP.Chapter6.matrixSignMeasure n) ≤
      ∫ ε, T.sup' hT (fun t => ∑ i, ε i * t i)
        ∂HDP.Chapter6.matrixSignMeasure n := by
  have hind : ∀ s : Finset (Fin n),
      (∫ ε, finiteRademacherSupremum T hT φ ε
          ∂HDP.Chapter6.matrixSignMeasure n) ≤
        ∫ ε, finiteRademacherSupremum T hT (contractedOn φ s) ε
          ∂HDP.Chapter6.matrixSignMeasure n := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hzero : contractedOn φ ∅ = φ := by
          funext i
          simp [contractedOn]
        rw [hzero]
    | @insert i s hi ih =>
        have hLip : LipschitzWith 1 (contractedOn φ s i) := by
          simp [contractedOn, hi, hφ i]
        have hstep := one_coordinate_expected_contraction T hT
          (contractedOn φ s) i hLip
        rw [← contractedOn_insert φ s i] at hstep
        exact ih.trans hstep
  have hall := hind Finset.univ
  simpa [finiteRademacherSupremum, contractedOn] using hall

end

end HDP.Chapter7

end Source_01_RandomProcesses

/-! ## Material formerly in `02_GaussianProcesses.lean` -/

section Source_02_GaussianProcesses

/-!
# Book Chapter 7, §7.1.2: Gaussian processes

Mathlib's `ProbabilityTheory.IsGaussianProcess` is the authoritative
finite-dimensional-distribution definition.  In particular, this module does
not introduce a competing Gaussian-process predicate.
-/

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped BigOperators ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace HDP.Chapter7

noncomputable section

variable {T Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {ν : Measure Ω'}

/-- A Gaussian process has jointly Gaussian restriction to every finite index set; equivalently every finite linear combination is Gaussian. Mathlib's definition says exactly that every
finite restriction has a Gaussian law.

**Book Definition 7.1.9.** -/
theorem isGaussianProcess_iff_finset (X : HDP.RandomProcess T Ω) :
    IsGaussianProcess X μ ↔
      ∀ I : Finset T,
        HasGaussianLaw (fun ω => I.restrict (X · ω)) μ :=
  ⟨fun h => h.hasGaussianLaw, fun h => ⟨h⟩⟩

/-- A Gaussian process has jointly Gaussian restriction to every finite index set; equivalently every finite linear combination is Gaussian. The finite-linear-combination formulation in Definition 7.1.9, in the
direction used throughout the book.

**Book Definition 7.1.9.** -/
theorem IsGaussianProcess.hasGaussianLaw_finiteLinearCombination
    {X : HDP.RandomProcess T Ω} (hX : IsGaussianProcess X μ)
    (I : Finset T) (a : T → ℝ) :
    HasGaussianLaw (fun ω => ∑ t ∈ I, a t * X t ω) μ := by
  simpa [smul_eq_mul] using
    (hX.smul a).hasGaussianLaw_fun_sum (I := I)

/-- Mean and covariance determine a Gaussian process in law; with a zero coordinate, increments determine it too. Two finite Gaussian
vectors with the same coordinate means and covariance function have the same
law. Degenerate covariance matrices are included.

**Book Remark 7.1.10.** -/
theorem finiteGaussianProcess_identDistrib_of_mean_covariance
    {I : Type*} [Finite I]
    {X : I → Ω → ℝ} {Y : I → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω => toLp 2 (X · ω)) μ)
    (hY : HasGaussianLaw (fun ω => toLp 2 (Y · ω)) ν)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = ∫ ω, Y i ω ∂ν)
    (hcov : ∀ i j, cov[X i, X j; μ] = cov[Y i, Y j; ν]) :
    IdentDistrib (fun ω => toLp 2 (X · ω))
      (fun ω => toLp 2 (Y · ω)) μ ν := by
  letI := Fintype.ofFinite I
  letI := hX.isProbabilityMeasure
  letI := hY.isProbabilityMeasure
  have hXi : ∀ i, MemLp (X i) 2 μ := by
    intro i
    simpa using (hX.map_fun (EuclideanSpace.proj i)).memLp_two
  have hYi : ∀ i, MemLp (Y i) 2 ν := by
    intro i
    simpa using (hY.map_fun (EuclideanSpace.proj i)).memLp_two
  letI := hX.isGaussian_map
  letI := hY.isGaussian_map
  refine ⟨hX.aemeasurable, hY.aemeasurable, ?_⟩
  apply HDP.Chapter3.gaussianLaw_unique
  · rw [integral_map hX.aemeasurable (by fun_prop),
      integral_map hY.aemeasurable (by fun_prop)]
    simp only [id_eq]
    ext i
    change (EuclideanSpace.proj i)
        (∫ ω, toLp 2 (X · ω) ∂μ) =
      (EuclideanSpace.proj i) (∫ ω, toLp 2 (Y · ω) ∂ν)
    rw [← (EuclideanSpace.proj i).integral_comp_comm hX.integrable,
      ← (EuclideanSpace.proj i).integral_comp_comm hY.integrable]
    simpa using hmean i
  · ext u v
    rw [covarianceBilin_apply_pi hXi, covarianceBilin_apply_pi hYi]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcov i j]

/-! ## The canonical Gaussian process -/

/-- Canonical Gaussian process `X_t=<g,t>`. Equation (7.2): the canonical Gaussian process indexed by vectors `a t`.
The sample point itself is a standard Gaussian vector.

**Book Equation (7.2).** -/
def canonicalGaussianProcess
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : T → E) : HDP.RandomProcess T E :=
  fun t g => inner ℝ (a t) g

/-- Every canonical process is Gaussian.

**Lean implementation helper.** -/
theorem canonicalGaussianProcess_isGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : T → E) :
    IsGaussianProcess (canonicalGaussianProcess a) (stdGaussian E) := by
  refine ⟨fun I => ?_⟩
  let L : E →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i => (innerSL ℝ) (a i)
  have hL : HasGaussianLaw (fun g : E => L g) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun L
  exact hL.congr (ae_of_all _ fun g => by
    ext i
    simp [L, canonicalGaussianProcess, innerSL_apply_apply])

/-- The canonical Gaussian process is centered.

**Lean implementation helper.** -/
theorem canonicalGaussianProcess_centered
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : T → E) :
    HDP.IsCenteredProcess (canonicalGaussianProcess a) (stdGaussian E) := by
  intro t
  change ∫ g : E, (innerSL ℝ (a t)) g ∂stdGaussian E = 0
  exact integral_strongDual_stdGaussian ((innerSL ℝ) (a t))

/-- Every coordinate of the canonical Gaussian process belongs to L² under the standard Gaussian measure.

**Lean implementation helper.** -/
theorem canonicalGaussianProcess_memLp_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : T → E) :
    HDP.IsL2Process (canonicalGaussianProcess a) (stdGaussian E) := by
  intro t
  exact ((canonicalGaussianProcess_isGaussian a).hasGaussianLaw_eval t).memLp_two

/-- Covariance of the canonical process is the ambient inner product.

**Lean implementation helper.** -/
theorem canonicalGaussianProcess_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : T → E) (s t : T) :
    HDP.processCovariance (canonicalGaussianProcess a) (stdGaussian E) s t =
      inner ℝ (a s) (a t) := by
  change cov[(fun g : E => inner ℝ (a s) g),
    (fun g : E => inner ℝ (a t) g); stdGaussian E] = _
  have h := covarianceBilin_apply_eq_cov
    (IsGaussian.memLp_two_id : MemLp id 2 (stdGaussian E)) (a s) (a t)
  rw [covarianceBilin_stdGaussian] at h
  change inner ℝ (a s) (a t) =
    cov[(fun g : E => inner ℝ (a s) g),
      (fun g : E => inner ℝ (a t) g); stdGaussian E] at h
  exact h.symm

/-- The marginal variance of a canonical process is `‖a t‖²`.

**Lean implementation helper.** -/
theorem canonicalGaussianProcess_variance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : T → E) (t : T) :
    Var[canonicalGaussianProcess a t; stdGaussian E] = ‖a t‖ ^ 2 := by
  change Var[(innerSL ℝ) (a t); stdGaussian E] = _
  rw [variance_dual_stdGaussian, innerSL_apply_norm]

/-- Euclidean Gaussian width dominates every Sudakov covering scale. The canonical Gaussian-process increment is exactly Euclidean distance.

**Book Corollary 7.4.2.** -/
theorem canonicalGaussianProcess_increment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : T → E) (s t : T) :
    HDP.processIncrement (canonicalGaussianProcess a) (stdGaussian E) s t =
      ‖a s - a t‖ := by
  let X := canonicalGaussianProcess a
  have hL2 : HDP.IsL2Process X (stdGaussian E) :=
    canonicalGaussianProcess_memLp_two a
  have hcenter : HDP.IsCenteredProcess X (stdGaussian E) :=
    canonicalGaussianProcess_centered a
  have hsq := HDP.processIncrement_sq_eq_covariance hL2 hcenter s t
  have hcov (u v : T) :
      HDP.processCovariance X (stdGaussian E) u v = inner ℝ (a u) (a v) :=
    canonicalGaussianProcess_covariance a u v
  rw [hcov s s, hcov s t, hcov t t] at hsq
  have hinner :
      inner ℝ (a s) (a s) - 2 * inner ℝ (a s) (a t) +
          inner ℝ (a t) (a t) = ‖a s - a t‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  rw [hinner] at hsq
  have hd := HDP.processIncrement_nonneg (hL2 s) (hL2 t)
  have hn := norm_nonneg (a s - a t)
  nlinarith

/-! ## Finite concentration and finite Gaussian representation -/

/-- The centered maximum of a finite Gaussian process has `psi2` norm bounded by a universal constant times the largest marginal standard deviation. The finite canonical affine representation of a
Gaussian process satisfies the source's maximum-concentration estimate. By
Lemma 7.1.12 every finite Gaussian process has such a representation.

**Book Theorem 7.1.11.** -/
theorem finiteGaussianProcess_concentration_canonical
    {I : Type*} [Fintype I] [Nonempty I] {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) (b : I → ℝ) :
    let M : EuclideanSpace ℝ (Fin n) → ℝ :=
      HDP.Chapter5.finiteMaximum (HDP.Chapter5.gaussianAffineFamily a b)
    HDP.SubGaussian (HDP.Chapter5.gaussianCentered M)
        (HDP.Chapter5.gaussianPiMeasure n) ∧
      HDP.psi2Norm (HDP.Chapter5.gaussianCentered M)
          (HDP.Chapter5.gaussianPiMeasure n) ≤
        2 * Real.sqrt 5 * HDP.Chapter5.gaussianMaximumScale a :=
  HDP.Chapter5.exercise_5_9b_gaussian_maximum a b

/-- The canonical linear image associated with a covariance matrix.

**Lean implementation helper.** -/
def canonicalCovarianceVector {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) g

/-- The indexing vectors in Lemma 7.1.12, defined invariantly using the
adjoint rather than choosing row-coordinate conventions.

**Book Lemma 7.1.12.** -/
def canonicalCovariancePoint {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).adjoint
    (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Each coordinate of the canonical covariance vector is the inner product with the corresponding canonical covariance point.

**Lean implementation helper.** -/
theorem canonicalCovarianceVector_apply {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    canonicalCovarianceVector S g i =
      inner ℝ (canonicalCovariancePoint S i) g := by
  calc
    canonicalCovarianceVector S g i =
        inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
          (canonicalCovarianceVector S g) := by
      simp [PiLp.inner_apply]
    _ = inner ℝ (canonicalCovariancePoint S i) g := by
      rw [canonicalCovariancePoint, canonicalCovarianceVector,
        ContinuousLinearMap.adjoint_inner_left]

/-- Every centered Gaussian vector is equal in law to inner products of one standard Gaussian vector with deterministic points. The canonical covariance vector has the centered multivariate Gaussian
law with covariance `S`.

**Book Lemma 7.1.12.** -/
theorem canonicalCovarianceVector_hasLaw {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) :
    HasLaw (canonicalCovarianceVector S) (multivariateGaussian 0 S)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  refine ⟨?_, ?_⟩
  · change AEMeasurable
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
    fun_prop
  · change
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) =
        (stdGaussian (EuclideanSpace ℝ (Fin n))).map
          (fun x => 0 + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
    simp

/-- Every centered Gaussian vector is equal in law to inner products of one standard Gaussian vector with deterministic points. A centered
Gaussian vector with law `N(0,S)` is identically distributed with inner
products against the points `canonicalCovariancePoint S i`. Singular
covariance matrices are allowed.

**Book Lemma 7.1.12.** -/
theorem gaussianVector_canonical_representation
    {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)}
    {S : Matrix (Fin n) (Fin n) ℝ}
    (hX : HasLaw X (multivariateGaussian 0 S) μ) :
    ∃ t : Fin n → EuclideanSpace ℝ (Fin n),
      IdentDistrib X
        (fun g => toLp 2 (fun i => inner ℝ (t i) g)) μ
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let t : Fin n → EuclideanSpace ℝ (Fin n) :=
    canonicalCovariancePoint S
  refine ⟨t, hX.identDistrib ?_⟩
  have hcan := canonicalCovarianceVector_hasLaw S
  refine hcan.congr (ae_of_all _ fun g => ?_)
  ext i
  exact (canonicalCovarianceVector_apply S g i).symm

end

end HDP.Chapter7

end Source_02_GaussianProcesses

/-! ## Material formerly in `03_GaussianIntegrationByParts.lean` -/

section Source_03_GaussianIntegrationByParts

/-!
# Book Chapter 7, §7.2.1: Gaussian integration by parts

The printed scalar statement assumes only differentiability and finiteness of
the two displayed expectations.  That does not by itself justify improper
integration by parts.  The theorem below exposes the three product
integrability conditions used by Mathlib's whole-line integration-by-parts
theorem.  This is a conservative, directly checkable correction.
-/

open MeasureTheory ProbabilityTheory Real Filter Set Matrix
open scoped NNReal MatrixOrder RealInnerProductSpace

namespace HDP.Chapter7

noncomputable section

/-- Scalar Gaussian integration by parts: `E[X f(X)] = E[f'(X)]`. The assumptions are exactly the derivative and product-integrability
certificates needed on the whole real line.

**Book Lemma 7.2.3.** -/
theorem gaussianIntegrationByParts
    (f f' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (h_fxp : Integrable
      (fun x ↦ f x * (-x * HDP.Chapter2.stdGaussianDensity x)))
    (h_f'p : Integrable
      (fun x ↦ f' x * HDP.Chapter2.stdGaussianDensity x))
    (h_fp : Integrable
      (fun x ↦ f x * HDP.Chapter2.stdGaussianDensity x)) :
    (∫ x, x * f x ∂gaussianReal 0 1) =
      ∫ x, f' x ∂gaussianReal 0 1 := by
  let p : ℝ → ℝ := HDP.Chapter2.stdGaussianDensity
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := p)
    (v' := fun x ↦ -x * p x)
    (fun x _ ↦ hderiv x)
    (fun x _ ↦ HDP.Chapter2.hasDerivAt_stdGaussianDensity x)
    h_fxp h_f'p h_fp
  have hne : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [integral_gaussianReal_eq_integral_smul
      (f := fun x ↦ x * f x) hne,
    integral_gaussianReal_eq_integral_smul (f := f') hne]
  simp only [smul_eq_mul, ← HDP.Chapter2.stdGaussianDensity_eq_gaussianPDFReal]
  have hrewrite :
      (∫ x, p x * (x * f x)) = -∫ x, f x * (-x * p x) := by
    calc
      (∫ x, p x * (x * f x)) =
          ∫ x, -(f x * (-x * p x)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = -∫ x, f x * (-x * p x) := integral_neg _
  rw [hrewrite, hibp, neg_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [p]
  ring

/-- A differentiable function whose product with the identity is integrable
under the standard Gaussian is itself integrable.

**Lean implementation helper.** -/
private lemma integrable_gaussianReal_of_integrable_mul_id
    (f : ℝ → ℝ) (hf : Continuous f)
    (hxf : Integrable (fun x ↦ x * f x) (gaussianReal 0 1)) :
    Integrable f (gaussianReal 0 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hdom : ∀ x : ℝ, ‖f x‖ ≤ ‖x * f x‖ + C' := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · exact (hC x hx).trans <| (le_max_left C 0).trans <|
        le_add_of_nonneg_left (norm_nonneg (x * f x))
    · have hxabs : 1 ≤ |x| := by
        by_contra h
        have hlt : |x| < 1 := lt_of_not_ge h
        exact hx ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
      calc
        ‖f x‖ ≤ |x| * ‖f x‖ := by nlinarith [norm_nonneg (f x)]
        _ = ‖x * f x‖ := by simp [norm_mul]
        _ ≤ ‖x * f x‖ + C' := le_add_of_nonneg_right hC'
  apply Integrable.mono' (hxf.norm.add (integrable_const C')) hf.aestronglyMeasurable
  filter_upwards [] with x
  simpa [abs_of_nonneg (add_nonneg (norm_nonneg (x * f x)) hC')] using hdom x

/-- The scalar identity rewritten entirely in terms of the Gaussian measure.

**Lean implementation helper.** -/
private theorem gaussianIntegrationByParts_measure
    (f f' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hxf : Integrable (fun x ↦ x * f x) (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1)) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfcont : Continuous f := continuous_iff_continuousAt.2 fun x ↦
    (hderiv x).continuousAt
  have hfint := integrable_gaussianReal_of_integrable_mul_id f hfcont hxf
  have hdens (g : ℝ → ℝ) (hg : Integrable g (gaussianReal 0 1)) :
      Integrable (fun x ↦ g x * HDP.Chapter2.stdGaussianDensity x) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff (measurable_gaussianPDF 0 1)
        (Filter.Eventually.of_forall fun _ ↦ gaussianPDF_lt_top)] at hg
    simpa [HDP.Chapter2.stdGaussianDensity_eq_gaussianPDFReal, mul_comm] using hg
  apply gaussianIntegrationByParts f f' hderiv
  · have heq : (fun x ↦ f x * (-x * HDP.Chapter2.stdGaussianDensity x)) =
        -(fun x ↦ (x * f x) * HDP.Chapter2.stdGaussianDensity x) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [heq]
    exact (hdens (fun x ↦ x * f x) hxf).neg
  · exact hdens f' hf'
  · exact hdens f hfint

/-- Coordinatewise integration by parts on a finite product of independent
standard Gaussian measures.

**Lean implementation helper.** -/
private theorem piGaussianIntegrationByParts
    {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (partialDeriv : Fin n → (Fin n → ℝ) → ℝ)
    (hdiff : Differentiable ℝ g)
    (hpartial : ∀ i x, partialDeriv i x =
      fderiv ℝ g x (Pi.single i 1))
    (hintLeft : ∀ i, Integrable (fun x ↦ x i * g x)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1))
    (hintRight : ∀ i, Integrable (partialDeriv i)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1))
    (k : Fin n) :
    (∫ x, x k * g x ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)) =
      ∫ x, partialDeriv k x
        ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ m =>
      let μ : Fin (m + 1) → Measure ℝ := fun _ ↦ gaussianReal 0 1
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) k
      let ν : Measure (Fin m → ℝ) := Measure.pi fun j ↦ μ (k.succAbove j)
      let mp : MeasurePreserving e (Measure.pi μ) ((μ k).prod ν) :=
        measurePreserving_piFinSuccAbove μ k
      let L : (Fin (m + 1) → ℝ) → ℝ := fun x ↦ x k * g x
      let R : (Fin (m + 1) → ℝ) → ℝ := partialDeriv k
      have hLint : Integrable L (Measure.pi μ) := hintLeft k
      have hRint : Integrable R (Measure.pi μ) := hintRight k
      have hLint' : Integrable (fun p ↦ L (e.symm p)) ((μ k).prod ν) :=
        mp.symm.integrable_comp_of_integrable hLint
      have hRint' : Integrable (fun p ↦ R (e.symm p)) ((μ k).prod ν) :=
        mp.symm.integrable_comp_of_integrable hRint
      have hsections : ∀ᵐ y ∂ν,
          Integrable (fun t ↦ L (e.symm (t, y))) (μ k) ∧
          Integrable (fun t ↦ R (e.symm (t, y))) (μ k) := by
        filter_upwards [hLint'.prod_left_ae, hRint'.prod_left_ae] with y hyL hyR
        exact ⟨hyL, hyR⟩
      have hline : ∀ y : Fin m → ℝ, ∀ t : ℝ,
          HasDerivAt (fun s ↦ g (e.symm (s, y))) (R (e.symm (t, y))) t := by
        intro y t
        let z : Fin (m + 1) → ℝ := e.symm (0, y)
        have heupdate : ∀ s : ℝ, e.symm (s, y) = Function.update z k s := by
          intro s
          apply e.injective
          ext j
          · simp [e, z, Fin.insertNthEquiv]
          · simp [e, z, Fin.insertNthEquiv]
        have hu := hasDerivAt_update z k t
        have hc : HasDerivAt (g ∘ Function.update z k)
            (fderiv ℝ g (Function.update z k t) (Pi.single k 1)) t :=
          (hdiff (Function.update z k t)).hasFDerivAt.comp_hasDerivAt t hu
        have hc' : HasDerivAt (fun s ↦ g (Function.update z k s))
            (fderiv ℝ g (Function.update z k t) (Pi.single k 1)) t := by
          change HasDerivAt (fun s ↦ g (Function.update z k s))
            (fderiv ℝ g (Function.update z k t) (Pi.single k 1)) t at hc
          exact hc
        rw [← hpartial k, ← heupdate] at hc'
        simpa only [R] using hc'.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s ↦ by rw [heupdate])
      calc
        (∫ x, x k * g x ∂(Measure.pi fun _ : Fin (m + 1) ↦ gaussianReal 0 1)) =
            ∫ p, L (e.symm p) ∂((μ k).prod ν) := by
              exact (mp.symm.integral_comp' L).symm
        _ = ∫ y, ∫ t, L (e.symm (t, y)) ∂(μ k) ∂ν :=
          integral_prod_symm _ hLint'
        _ = ∫ y, ∫ t, R (e.symm (t, y)) ∂(μ k) ∂ν := by
          apply integral_congr_ae
          filter_upwards [hsections] with y hy
          have hyL : Integrable
              (fun t ↦ t * g (e.symm (t, y))) (gaussianReal 0 1) := by
            simpa [L, μ, e] using hy.1
          have hyR : Integrable
              (fun t ↦ R (e.symm (t, y))) (gaussianReal 0 1) := by
            simpa [μ] using hy.2
          simpa [L, μ, e] using gaussianIntegrationByParts_measure
            (fun t ↦ g (e.symm (t, y)))
            (fun t ↦ R (e.symm (t, y))) (hline y) hyL hyR
        _ = ∫ p, R (e.symm p) ∂((μ k).prod ν) :=
          (integral_prod_symm _ hRint').symm
        _ = ∫ x, partialDeriv k x
            ∂(Measure.pi fun _ : Fin (m + 1) ↦ gaussianReal 0 1) := by
          exact mp.symm.integral_comp' R

/-- Linear pullback from independent scalar Gaussians through the positive
semidefinite square root of a covariance matrix.

**Lean implementation helper.** -/
private def gaussianSqrtPullbackCLM {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ WithLp.toLp 2 ((CFC.sqrt S) *ᵥ z)
      map_add' := by
        intro x y
        apply WithLp.ofLp_injective
        ext i
        simp [Matrix.mulVec]
      map_smul' := by
        intro c x
        apply WithLp.ofLp_injective
        ext i
        simp [Matrix.mulVec] }

/-- Evaluates the Gaussian square-root pullback as multiplication by the positive square root of the covariance matrix.

**Lean implementation helper.** -/
@[simp] private lemma gaussianSqrtPullbackCLM_apply {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    gaussianSqrtPullbackCLM S z =
      toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) (WithLp.toLp 2 z) := rfl

/-- Expands the derivative of a function after Gaussian square-root pullback in the Euclidean basis.

**Lean implementation helper.** -/
private lemma fderiv_gaussianSqrtPullbackCLM_apply
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (z : Fin n → ℝ) (k : Fin n) :
    fderiv ℝ (fun z ↦ f (gaussianSqrtPullbackCLM S z)) z (Pi.single k 1) =
      ∑ j, (CFC.sqrt S) j k *
        fderiv ℝ f (gaussianSqrtPullbackCLM S z)
          (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hcomp := (hf (gaussianSqrtPullbackCLM S z)).hasFDerivAt.comp z
    (gaussianSqrtPullbackCLM S).hasFDerivAt
  have hfd := hcomp.fderiv
  change (fderiv ℝ (f ∘ ⇑(gaussianSqrtPullbackCLM S)) z) (Pi.single k 1) = _
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply]
  have hv : gaussianSqrtPullbackCLM S (Pi.single k 1) =
      ∑ j, (CFC.sqrt S) j k • EuclideanSpace.basisFun (Fin n) ℝ j := by
    apply WithLp.ofLp_injective
    ext i
    simp [gaussianSqrtPullbackCLM, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The Gaussian square-root pullback sends an independent standard Gaussian vector to the centered Gaussian law with the prescribed covariance.

**Lean implementation helper.** -/
private lemma map_gaussianSqrtPullbackCLM {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map
        (gaussianSqrtPullbackCLM S) = multivariateGaussian 0 S := by
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map]
  · congr 1
    funext z
    simp [gaussianSqrtPullbackCLM]
  · fun_prop
  · fun_prop

/-- Bounded-observable multivariate Gaussian integration by parts. The printed exercise repeats the insufficient differentiability-only
hypothesis of the scalar statement. This corrected analytic form assumes a
global bound and explicit left/right integrability certificates. The proof
realizes an arbitrary, possibly
singular, positive-semidefinite Gaussian as the square-root pushforward of
independent standard Gaussians and applies the proved scalar identity on every
coordinate line.

**Lean implementation helper.** -/
theorem multivariateGaussianIntegrationByParts_of_bounded
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (partialDeriv : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ContDiff ℝ 1 f) (hbounded : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hpartial : ∀ i x, partialDeriv i x =
      fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hintLeft : ∀ i, Integrable
      (fun x ↦ x i * f x) (multivariateGaussian 0 S))
    (hintRight : ∀ j, Integrable
      (partialDeriv j) (multivariateGaussian 0 S))
    (i : Fin n) :
    (∫ x, x i * f x ∂multivariateGaussian 0 S) =
      ∑ j, S i j * ∫ x, partialDeriv j x ∂multivariateGaussian 0 S := by
  let P0 : Measure (Fin n → ℝ) := Measure.pi fun _ ↦ gaussianReal 0 1
  let B := gaussianSqrtPullbackCLM S
  let g : (Fin n → ℝ) → ℝ := fun z ↦ f (B z)
  let pd : Fin n → (Fin n → ℝ) → ℝ := fun k z ↦
    ∑ j, (CFC.sqrt S) j k * partialDeriv j (B z)
  have hmp : MeasurePreserving B P0 (multivariateGaussian 0 S) := by
    refine ⟨B.measurable, ?_⟩
    exact map_gaussianSqrtPullbackCLM S
  have hLaw : HasLaw B (multivariateGaussian 0 S) P0 := hmp.hasLaw
  have hfdiff : Differentiable ℝ f := hdiff.differentiable (by norm_num)
  have hgdiff : Differentiable ℝ g := hfdiff.comp B.differentiable
  have hpd : ∀ k z, pd k z = fderiv ℝ g z (Pi.single k 1) := by
    intro k z
    rw [fderiv_gaussianSqrtPullbackCLM_apply S f hfdiff z k]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpartial]
  obtain ⟨C, hC⟩ := hbounded
  let C' := max C 0
  have hC' : ∀ z, ‖g z‖ ≤ C' := fun z ↦
    (hC (B z)).trans (le_max_left _ _)
  have hleftPi : ∀ k, Integrable (fun z ↦ z k * g z) P0 := by
    intro k
    have hk : Integrable (fun z : Fin n → ℝ ↦ z k) P0 := by
      exact integrable_eval IsGaussian.integrable_id
    exact hk.mul_bdd hgdiff.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC')
  have hrightComp : ∀ j, Integrable (fun z ↦ partialDeriv j (B z)) P0 := by
    intro j
    change Integrable (partialDeriv j ∘ B) P0
    exact hmp.integrable_comp_of_integrable (hintRight j)
  have hrightPi : ∀ k, Integrable (pd k) P0 := by
    intro k
    apply integrable_finsetSum
    intro j _
    exact (hrightComp j).const_mul _
  have hstein : ∀ k,
      (∫ z, z k * g z ∂P0) = ∫ z, pd k z ∂P0 := by
    intro k
    exact piGaussianIntegrationByParts g pd hgdiff hpd hleftPi hrightPi k
  let r : Fin n → ℝ := fun j ↦
    ∫ x, partialDeriv j x ∂multivariateGaussian 0 S
  have hrComp : ∀ j, (∫ z, partialDeriv j (B z) ∂P0) = r j := by
    intro j
    exact hLaw.integral_comp (hintRight j).aestronglyMeasurable
  have hstein' : ∀ k, (∫ z, z k * g z ∂P0) =
      ∑ j, (CFC.sqrt S) j k * r j := by
    intro k
    rw [hstein k]
    change (∫ z, ∑ j, (CFC.sqrt S) j k * partialDeriv j (B z) ∂P0) = _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, hrComp]
    · intro j _
      exact (hrightComp j).const_mul _
  have hleftLaw :
      (∫ z, (B z) i * f (B z) ∂P0) =
        ∫ x, x i * f x ∂multivariateGaussian 0 S := by
    exact hLaw.integral_comp (hintLeft i).aestronglyMeasurable
  have hsymm : ∀ j k, (CFC.sqrt S) j k = (CFC.sqrt S) k j := by
    intro j k
    simpa using (CFC.sqrt_nonneg S).isSelfAdjoint.isHermitian.apply k j
  have hsqrt : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hsqrtEntry : ∀ j, ∑ k, (CFC.sqrt S) i k * (CFC.sqrt S) k j = S i j := by
    intro j
    simpa [Matrix.mul_apply] using congr_fun (congr_fun hsqrt i) j
  rw [← hleftLaw]
  calc
    (∫ z, (B z) i * f (B z) ∂P0) =
        ∫ z, ∑ k, (CFC.sqrt S) i k * (z k * g z) ∂P0 := by
      apply integral_congr_ae
      filter_upwards [] with z
      change ((∑ k, (CFC.sqrt S) i k * z k) *
        f (WithLp.toLp 2 ((CFC.sqrt S) *ᵥ z))) =
          ∑ k, (CFC.sqrt S) i k *
            (z k * f (WithLp.toLp 2 ((CFC.sqrt S) *ᵥ z)))
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k, (CFC.sqrt S) i k * ∫ z, z k * g z ∂P0 := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [integral_const_mul]
      · intro k _
        exact (hleftPi k).const_mul _
    _ = ∑ k, (CFC.sqrt S) i k *
        (∑ j, (CFC.sqrt S) j k * r j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hstein']
    _ = ∑ j, S i j * r j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hsqrtEntry j]
      simp_rw [hsymm j]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, S i j *
        ∫ x, partialDeriv j x ∂multivariateGaussian 0 S := rfl

/-- Multivariate Gaussian integration by parts contracts covariance with the gradient.

**Book Lemma 7.2.4.** -/
theorem multivariateGaussianIntegrationByParts
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (partialDeriv : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hpartial : ∀ i x, partialDeriv i x =
      fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hintLeft : ∀ i, Integrable
      (fun x ↦ x i * f x) (multivariateGaussian 0 S))
    (hintRight : ∀ j, Integrable
      (partialDeriv j) (multivariateGaussian 0 S))
    (i : Fin n) :
    (∫ x, x i * f x ∂multivariateGaussian 0 S) =
      ∑ j, S i j * ∫ x, partialDeriv j x ∂multivariateGaussian 0 S := by
  apply multivariateGaussianIntegrationByParts_of_bounded S hS f partialDeriv hdiff
  · exact hcompact.exists_bound_of_continuous hdiff.continuous
  · exact hpartial
  · exact hintLeft
  · exact hintRight

end

end HDP.Chapter7

end Source_03_GaussianIntegrationByParts

/-! ## Material formerly in `04_GaussianInterpolation.lean` -/

section Source_04_GaussianInterpolation

/-!
# Book Chapter 7, §7.2.1: Gaussian interpolation

We use the product of two multivariate Gaussian laws.  Thus independence is
part of the model rather than an informal “without loss of generality”.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter7

noncomputable section

/-- Interpolation `sqrt(u)X+sqrt(1-u)Y`.

**Book Equation (7.8).** -/
def gaussianInterpolationPoint {n : ℕ} (u : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  Real.sqrt u • p.1 + Real.sqrt (1 - u) • p.2

/-- Expected observable along the independent Gaussian interpolation.

**Lean implementation helper.** -/
def gaussianInterpolationExpectation {n : ℕ}
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (u : ℝ) : ℝ :=
  ∫ p, f (gaussianInterpolationPoint u p)
    ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))

/-- Coordinate entry of the Fréchet Hessian in the standard Euclidean basis.

**Lean implementation helper.** -/
def gaussianHessianEntry {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (fderiv ℝ (fderiv ℝ f) x)
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- Defines the velocity vector of the square-root Gaussian interpolation.

**Lean implementation helper.** -/
def gaussianInterpolationVelocity {n : ℕ} (u : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (1 / (2 * Real.sqrt u)) • p.1 -
    (1 / (2 * Real.sqrt (1 - u))) • p.2

/-- The Gaussian interpolation point is continuous.

**Lean implementation helper.** -/
private lemma continuous_gaussianInterpolationPoint {n : ℕ} (u : ℝ) :
    Continuous (gaussianInterpolationPoint (n := n) u) := by
  unfold gaussianInterpolationPoint
  fun_prop

/-- The Gaussian interpolation velocity is continuous.

**Lean implementation helper.** -/
private lemma continuous_gaussianInterpolationVelocity {n : ℕ} (u : ℝ) :
    Continuous (gaussianInterpolationVelocity (n := n) u) := by
  unfold gaussianInterpolationVelocity
  fun_prop

/-- The derivative of the square-root Gaussian interpolation point is its interpolation velocity away from the endpoints.

**Lean implementation helper.** -/
private lemma hasDerivAt_gaussianInterpolationPoint {n : ℕ}
    {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun t ↦ gaussianInterpolationPoint t p)
      (gaussianInterpolationVelocity u p) u := by
  have hX := (Real.hasDerivAt_sqrt hu0).smul_const p.1
  have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub 1
  have hY0 := (Real.hasDerivAt_sqrt hu1).comp u hsub
  have hY := hY0.smul_const p.2
  have h := hX.add hY
  have hv : (1 / (2 * Real.sqrt u)) • p.1 +
      (1 / (2 * Real.sqrt (1 - u)) * (-1 : ℝ)) • p.2 =
        gaussianInterpolationVelocity u p := by
    dsimp [gaussianInterpolationVelocity]
    rw [mul_neg, mul_one, neg_smul]
    rfl
  rw [hv] at h
  exact h.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t ↦ by
    simp [gaussianInterpolationPoint]

/-- Differentiating an observable along the Gaussian interpolation pairs its Fréchet derivative with the interpolation velocity.

**Lean implementation helper.** -/
private lemma hasDerivAt_interp_observable {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun t ↦ f (gaussianInterpolationPoint t p))
      (fderiv ℝ f (gaussianInterpolationPoint u p)
        (gaussianInterpolationVelocity u p)) u := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt u
    (hasDerivAt_gaussianInterpolationPoint hu0 hu1 p)

/-- A globally bounded derivative supplies the linear-growth estimate used
to integrate unbounded smooth observables against Gaussian laws.

**Lean implementation helper.** -/
private lemma norm_apply_le_linear_of_fderiv_bound
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (C : ℝ)
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖f z‖ ≤ C * ‖z‖ + ‖f 0‖ := by
  have hmv : ‖f z - f 0‖ ≤ C * ‖z - 0‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ ↦ hf x) (fun x _ ↦ hC x) (Set.mem_univ 0) (Set.mem_univ z)
  calc
    ‖f z‖ = ‖(f z - f 0) + f 0‖ := by congr 1; ring
    _ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ C * ‖z‖ + ‖f 0‖ := by simpa using add_le_add_right hmv ‖f 0‖

/-- Differentiates the Gaussian interpolation expectation under the integral sign.

**Lean implementation helper.** -/
private lemma hasDerivAt_gaussianInterpolationExpectation_raw
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianInterpolationExpectation SX SY f)
      (∫ p, fderiv ℝ f (gaussianInterpolationPoint u p)
          (gaussianInterpolationVelocity u p)
        ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) u := by
  let μX := multivariateGaussian 0 SX
  let μY := multivariateGaussian 0 SY
  let μ := μX.prod μY
  let a := u / 2
  let b := (u + 1) / 2
  let A := 1 / (2 * Real.sqrt a)
  let B := 1 / (2 * Real.sqrt (1 - b))
  have ha : 0 < a := by dsimp [a]; linarith [hu.1]
  have hb : b < 1 := by dsimp [b]; linarith [hu.2]
  have hub : u < b := by dsimp [b]; linarith [hu.2]
  have hau : a < u := by dsimp [a]; linarith [hu.1]
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  obtain ⟨C, hC⟩ := hDfBound
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hfderiv_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ C' := fun x ↦
    (hC x).trans (le_max_left _ _)
  let bound : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p ↦ C' * (A * ‖p.1‖ + B * ‖p.2‖)
  have hcoefX : ∀ x ∈ Set.Icc a b, 0 ≤ 1 / (2 * Real.sqrt x) ∧
      1 / (2 * Real.sqrt x) ≤ A := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    constructor
    · positivity
    · dsimp [A]
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx.1) (by norm_num))
  have hcoefY : ∀ x ∈ Set.Icc a b, 0 ≤ 1 / (2 * Real.sqrt (1 - x)) ∧
      1 / (2 * Real.sqrt (1 - x)) ≤ B := by
    intro x hx
    have hxb : 1 - b ≤ 1 - x := sub_le_sub_left hx.2 1
    have hpos : 0 < 1 - x := by linarith [lt_of_le_of_lt hx.2 hb]
    constructor
    · positivity
    · dsimp [B]
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxb) (by norm_num))
  have hvel : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ∀ x ∈ Set.Icc a b,
      ‖gaussianInterpolationVelocity x p‖ ≤ A * ‖p.1‖ + B * ‖p.2‖ := by
    intro p x hx
    calc
      ‖gaussianInterpolationVelocity x p‖ ≤
          ‖(1 / (2 * Real.sqrt x)) • p.1‖ +
            ‖(1 / (2 * Real.sqrt (1 - x))) • p.2‖ := by
              exact norm_sub_le _ _
      ‖(1 / (2 * Real.sqrt x)) • p.1‖ +
          ‖(1 / (2 * Real.sqrt (1 - x))) • p.2‖ =
          (1 / (2 * Real.sqrt x)) * ‖p.1‖ +
            (1 / (2 * Real.sqrt (1 - x))) * ‖p.2‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (hcoefX x hx).1, abs_of_nonneg (hcoefY x hx).1]
      _ ≤ A * ‖p.1‖ + B * ‖p.2‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hcoefX x hx).2 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hcoefY x hx).2 (norm_nonneg _))
  have hbound : ∀ p, ∀ x ∈ Set.Icc a b,
      ‖fderiv ℝ f (gaussianInterpolationPoint x p)
        (gaussianInterpolationVelocity x p)‖ ≤ bound p := by
    intro p x hx
    calc
      ‖fderiv ℝ f (gaussianInterpolationPoint x p)
          (gaussianInterpolationVelocity x p)‖ ≤
          ‖fderiv ℝ f (gaussianInterpolationPoint x p)‖ *
            ‖gaussianInterpolationVelocity x p‖ :=
        (fderiv ℝ f (gaussianInterpolationPoint x p)).le_opNorm _
      _ ≤ C' * (A * ‖p.1‖ + B * ‖p.2‖) := by
        gcongr
        · exact hfderiv_bound _
        · exact hvel p x hx
      _ = bound p := rfl
  have hbound_int : Integrable bound μ := by
    have hX : Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ ‖p.1‖) μ := by
      exact IsGaussian.integrable_id.norm.comp_fst μY
    have hY : Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ ‖p.2‖) μ := by
      exact IsGaussian.integrable_id.norm.comp_snd μX
    exact (hX.const_mul A).add (hY.const_mul B) |>.const_mul C'
  have hFint : Integrable
      (fun p ↦ f (gaussianInterpolationPoint u p)) μ := by
    have hgrowth := norm_apply_le_linear_of_fderiv_bound f
      (hf.differentiable (by norm_num)) C' hfderiv_bound
    let A := |Real.sqrt u|
    let B := |Real.sqrt (1 - u)|
    let growthBound : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) → ℝ :=
      fun p ↦ C' * (A * ‖p.1‖ + B * ‖p.2‖) + ‖f 0‖
    have hgrowthBound : Integrable growthBound μ := by
      have hX : Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) ↦ ‖p.1‖) μ :=
        IsGaussian.integrable_id.norm.comp_fst μY
      have hY : Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) ↦ ‖p.2‖) μ :=
        IsGaussian.integrable_id.norm.comp_snd μX
      have hconst : Integrable
          (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
            ‖f 0‖) μ := integrable_const_iff.2 (Or.inr inferInstance)
      exact (((hX.const_mul A).add (hY.const_mul B)).const_mul C').add hconst
    apply hgrowthBound.mono'
      (hf.continuous.comp
        (continuous_gaussianInterpolationPoint u)).aestronglyMeasurable
    filter_upwards [] with p
    calc
      ‖f (gaussianInterpolationPoint u p)‖ ≤
          C' * ‖gaussianInterpolationPoint u p‖ + ‖f 0‖ := hgrowth _
      _ ≤ C' * (A * ‖p.1‖ + B * ‖p.2‖) + ‖f 0‖ := by
        gcongr
        unfold gaussianInterpolationPoint A B
        calc
          ‖Real.sqrt u • p.1 + Real.sqrt (1 - u) • p.2‖ ≤
              ‖Real.sqrt u • p.1‖ + ‖Real.sqrt (1 - u) • p.2‖ := norm_add_le _ _
          _ = |Real.sqrt u| * ‖p.1‖ + |Real.sqrt (1 - u)| * ‖p.2‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = growthBound p := rfl
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun x p ↦ f (gaussianInterpolationPoint x p))
    (F' := fun x p ↦ fderiv ℝ f (gaussianInterpolationPoint x p)
      (gaussianInterpolationVelocity x p))
    (bound := bound) (x₀ := u) (s := Set.Icc a b)
    (Icc_mem_nhds hau hub)
    (Filter.Eventually.of_forall fun x ↦
      (hf.continuous.comp
        (continuous_gaussianInterpolationPoint x)).aestronglyMeasurable)
    hFint
    (((hf.continuous_fderiv (by norm_num)).comp
      (continuous_gaussianInterpolationPoint u)).clm_apply
        (continuous_gaussianInterpolationVelocity u)).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) hbound_int
    (Filter.Eventually.of_forall fun p x hx ↦
      hasDerivAt_interp_observable f (hf.differentiable (by norm_num))
        (ne_of_gt (lt_of_lt_of_le ha hx.1))
        (ne_of_gt (by linarith [lt_of_le_of_lt hx.2 hb])) p)
  change HasDerivAt
    (fun t ↦ ∫ p, f (gaussianInterpolationPoint t p)
      ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) _ u
  simpa only [μ, μX, μY] using hparam.2

/-- Every Euclidean vector is the sum of its coordinates times the standard basis vectors.

**Lean implementation helper.** -/
private lemma euclidean_sum_smul_basis {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, x i • EuclideanSpace.basisFun (Fin n) ℝ i) = x := by
  simpa only [EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x

/-- A real continuous linear functional equals the coordinate sum of its values on the Euclidean basis.

**Lean implementation helper.** -/
private lemma continuousLinearMap_apply_euclideanBasis {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    L x = ∑ i, x i * L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  conv_lhs => rw [← euclidean_sum_smul_basis x]
  simp

/-- On a finite Euclidean space, uniform bounds on all coordinate partial
derivatives give a uniform operator-norm bound on the full derivative.

**Lean implementation helper.** -/
theorem fderiv_opNorm_bounded_of_coordinate_bounded
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hcoord : ∀ i, ∃ C, ∀ x,
      ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ C) :
    ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C := by
  choose C hC using hcoord
  let C' : Fin n → ℝ := fun i ↦ max (C i) 0
  refine ⟨∑ i, C' i, fun x ↦ ?_⟩
  apply (fderiv ℝ f x).opNorm_le_bound
  · exact Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  · intro v
    rw [continuousLinearMap_apply_euclideanBasis]
    calc
      ‖∑ i, v i * fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤
          ∑ i, ‖v i * fderiv ℝ f x
            (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := norm_sum_le _ _
      _ = ∑ i, |v i| * ‖fderiv ℝ f x
            (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Real.norm_eq_abs]
      _ ≤ ∑ i, ‖v‖ * C' i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul
        · rw [← EuclideanSpace.basisFun_inner (Fin n) ℝ v i, ← Real.norm_eq_abs]
          simpa using
            (@norm_inner_le_norm ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
              (EuclideanSpace.basisFun (Fin n) ℝ i) v)
        · exact (hC i x).trans (le_max_left _ _)
        · exact norm_nonneg _
        · exact norm_nonneg v
      _ = (∑ i, C' i) * ‖v‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Computes the derivative of an affine pullback of one gradient coordinate in terms of a Hessian entry.

**Lean implementation helper.** -/
private lemma fderiv_gradientCoordinate_affine
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (c : ℝ) (d : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z ↦ fderiv ℝ f (c • z + d)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
      c * gaussianHessianEntry f j i (c • x + d) := by
  let e_i := EuclideanSpace.basisFun (Fin n) ℝ i
  let e_j := EuclideanSpace.basisFun (Fin n) ℝ j
  change fderiv ℝ (fun z ↦ fderiv ℝ f (c • z + d) e_i) x e_j =
    c * gaussianHessianEntry f j i (c • x + d)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgrad : HasFDerivAt (fun z ↦ fderiv ℝ f z e_i)
      ((fderiv ℝ (fderiv ℝ f) (c • x + d)).flip e_i)
      (c • x + d) := by
    have h := (hDf (c • x + d)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (x := c • x + d) (c := e_i))
    simpa using h
  have haff : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ c • z + d)
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x := by
    simpa using ((hasFDerivAt_id x).const_smul c).add_const d
  have hcomp := hgrad.comp x haff
  have hfd : fderiv ℝ (fun z ↦ fderiv ℝ f (c • z + d) e_i) x =
      (fderiv ℝ (fderiv ℝ f) (c • x + d)).flip e_i ∘L
        (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  rw [hfd]
  simp [e_i, e_j, gaussianHessianEntry]

/-- An affine pullback of a gradient coordinate is continuously differentiable.

**Lean implementation helper.** -/
private lemma gradientCoordinate_affine_contDiff
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (c : ℝ) (d : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    ContDiff ℝ 1 (fun z ↦ fderiv ℝ f (c • z + d)
      (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  have hgrad : ContDiff ℝ 1
      (fun z ↦ fderiv ℝ f z (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact hgrad.comp (by fun_prop)

/-- An affine pullback of a gradient coordinate has compact support when the original function does and the scaling is nonzero.

**Lean implementation helper.** -/
private lemma gradientCoordinate_affine_hasCompactSupport
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hcompact : HasCompactSupport f) (c : ℝ) (hc : c ≠ 0)
    (d : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    HasCompactSupport (fun z ↦ fderiv ℝ f (c • z + d)
      (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.smulOfNeZero c hc).trans (Homeomorph.addRight d)
  have hs := (hcompact.fderiv_apply ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ i)).comp_homeomorph e
  simpa [e, Function.comp_def] using hs

/-- Every Euclidean coordinate is integrable under a centered multivariate Gaussian law.

**Lean implementation helper.** -/
private lemma integrable_euclidean_coord {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ x i)
      (multivariateGaussian 0 S) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
  have h := L.integrable_comp
    (IsGaussian.integrable_id (μ := multivariateGaussian 0 S))
  convert h using 1
  funext x
  simpa [L] using (EuclideanSpace.basisFun_inner (Fin n) ℝ x i).symm

/-- Applies Gaussian integration by parts to an affine pullback of a gradient coordinate.

**Lean implementation helper.** -/
private lemma multivariateGaussian_gradientCoordinate_affine
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ j i, ∃ D, ∀ x, ‖gaussianHessianEntry f j i x‖ ≤ D)
    (c : ℝ) (d : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (∫ x, x i * fderiv ℝ f (c • x + d)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
      ∂multivariateGaussian 0 S) =
      ∑ j, S i j * ∫ x, c * gaussianHessianEntry f j i (c • x + d)
        ∂multivariateGaussian 0 S := by
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    fderiv ℝ f (c • x + d) (EuclideanSpace.basisFun (Fin n) ℝ i)
  let pd : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun j x ↦
    fderiv ℝ q x (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hqdiff : ContDiff ℝ 1 q :=
    gradientCoordinate_affine_contDiff f hf c d i
  obtain ⟨C, hC⟩ := hDfBound
  have hqbound : ∃ C, ∀ x, ‖q x‖ ≤ C := by
    refine ⟨C, fun x ↦ ?_⟩
    exact ((fderiv ℝ f (c • x + d)).le_opNorm _).trans <| by
      simpa using hC (c • x + d)
  have hleft : ∀ k, Integrable (fun x ↦ x k * q x)
      (multivariateGaussian 0 S) := by
    intro k
    have hk : Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ x k)
        (multivariateGaussian 0 S) := integrable_euclidean_coord S k
    exact hk.mul_bdd hqdiff.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hqbound.choose_spec x)
  have hright : ∀ j, Integrable (pd j) (multivariateGaussian 0 S) := by
    intro j
    have hcont : Continuous (pd j) :=
      (hqdiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨D, hD⟩ := hHBound j i
    refine Integrable.of_bound hcont.aestronglyMeasurable (|c| * D)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [show pd j x = c * gaussianHessianEntry f j i (c • x + d) by
      exact fderiv_gradientCoordinate_affine f hf c d i j x]
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg c)
  have hibp := multivariateGaussianIntegrationByParts_of_bounded S hS q pd hqdiff
    hqbound (fun _ _ ↦ rfl) hleft hright i
  simpa only [q, pd, fderiv_gradientCoordinate_affine f hf c d] using hibp

/-- Every Hessian entry of a twice continuously differentiable function is continuous.

**Lean implementation helper.** -/
private lemma gaussianHessianEntry_continuous {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin n) : Continuous (gaussianHessianEntry f i j) := by
  exact (((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
    (by norm_num)).clm_apply continuous_const).clm_apply continuous_const

/-- A uniformly bounded Hessian entry evaluated along the Gaussian interpolation is integrable.

**Lean implementation helper.** -/
private lemma integrable_gaussianHessianEntry_interpolation
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hHBound : ∀ i j, ∃ D, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ D)
    (u : ℝ) (i j : Fin n) :
    Integrable (fun p ↦ gaussianHessianEntry f i j
      (gaussianInterpolationPoint u p))
      ((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
  obtain ⟨D, hD⟩ := hHBound i j
  apply Integrable.of_bound
    ((gaussianHessianEntry_continuous f hf i j).comp
      (continuous_gaussianInterpolationPoint u)).aestronglyMeasurable D
  filter_upwards [] with p
  exact hD _

/-- The first Gaussian component times a uniformly bounded gradient coordinate along the interpolation is integrable.

**Lean implementation helper.** -/
private lemma integrable_first_mul_gradient_interpolation
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ D, ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (u : ℝ) (i : Fin n) :
    Integrable (fun p ↦ p.1 i *
      fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
  let μX := multivariateGaussian 0 SX
  let μY := multivariateGaussian 0 SY
  have hgradcont : Continuous
      (fun z ↦ fderiv ℝ f z (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨D, hD⟩ := hDfBound
  have hcoord : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦ p.1 i)
      (μX.prod μY) :=
    (integrable_euclidean_coord SX i).comp_fst μY
  exact hcoord.mul_bdd
    (hgradcont.comp (continuous_gaussianInterpolationPoint u)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦
      ((fderiv ℝ f (gaussianInterpolationPoint u p)).le_opNorm _).trans <| by
        simpa using hD (gaussianInterpolationPoint u p))

/-- The second Gaussian component times a uniformly bounded gradient coordinate along the interpolation is integrable.

**Lean implementation helper.** -/
private lemma integrable_second_mul_gradient_interpolation
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ D, ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (u : ℝ) (i : Fin n) :
    Integrable (fun p ↦ p.2 i *
      fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
  let μX := multivariateGaussian 0 SX
  let μY := multivariateGaussian 0 SY
  have hgradcont : Continuous
      (fun z ↦ fderiv ℝ f z (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨D, hD⟩ := hDfBound
  have hcoord : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦ p.2 i)
      (μX.prod μY) :=
    (integrable_euclidean_coord SY i).comp_snd μX
  exact hcoord.mul_bdd
    (hgradcont.comp (continuous_gaussianInterpolationPoint u)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦
      ((fderiv ℝ f (gaussianInterpolationPoint u p)).le_opNorm _).trans <| by
        simpa using hD (gaussianInterpolationPoint u p))

/-- Evaluates the first Gaussian component times a gradient coordinate by Gaussian integration by parts.

**Lean implementation helper.** -/
private lemma integral_first_mul_gradient_interpolation
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ) (hSX : SX.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ i j, ∃ D, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ D)
    {u : ℝ} (_hu : u ∈ Ioo (0 : ℝ) 1) (i : Fin n) :
    (∫ p, p.1 i * fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
      ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) =
      ∑ j, SX i j *
        ∫ p, Real.sqrt u * gaussianHessianEntry f j i
          (gaussianInterpolationPoint u p)
        ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
  let μX := multivariateGaussian 0 SX
  let μY := multivariateGaussian 0 SY
  let H : Fin n → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ :=
    fun j p ↦ Real.sqrt u * gaussianHessianEntry f j i
      (gaussianInterpolationPoint u p)
  have hg : Integrable (fun p ↦ p.1 i *
      fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) (μX.prod μY) :=
    integrable_first_mul_gradient_interpolation SX SY f hf hDfBound u i
  have hH : ∀ j, Integrable (H j) (μX.prod μY) := fun j ↦
    (integrable_gaussianHessianEntry_interpolation SX SY f hf hHBound u j i).const_mul _
  have hsection : ∀ y,
      (∫ x, x i * fderiv ℝ f
          (Real.sqrt u • x + Real.sqrt (1 - u) • y)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μX) =
        ∑ j, SX i j * ∫ x, H j (x, y) ∂μX := by
    intro y
    simpa [H, μX, gaussianInterpolationPoint] using
      multivariateGaussian_gradientCoordinate_affine SX hSX f hf hDfBound hHBound
        (Real.sqrt u) (Real.sqrt (1 - u) • y) i
  calc
    (∫ p, p.1 i * fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂(μX.prod μY)) =
        ∫ y, ∫ x, x i * fderiv ℝ f
          (Real.sqrt u • x + Real.sqrt (1 - u) • y)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μX ∂μY := by
      simpa [gaussianInterpolationPoint] using
        integral_prod_symm _ hg
    _ = ∫ y, ∑ j, SX i j * ∫ x, H j (x, y) ∂μX ∂μY := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hsection y
    _ = ∑ j, ∫ y, SX i j * ∫ x, H j (x, y) ∂μX ∂μY := by
      rw [integral_finsetSum]
      intro j _
      exact (hH j).integral_prod_right.const_mul _
    _ = ∑ j, SX i j * ∫ p, H j p ∂(μX.prod μY) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_prod_symm _ (hH j)]

/-- Evaluates the second Gaussian component times a gradient coordinate by Gaussian integration by parts.

**Lean implementation helper.** -/
private lemma integral_second_mul_gradient_interpolation
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ i j, ∃ D, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ D)
    {u : ℝ} (_hu : u ∈ Ioo (0 : ℝ) 1) (i : Fin n) :
    (∫ p, p.2 i * fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
      ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) =
      ∑ j, SY i j *
        ∫ p, Real.sqrt (1 - u) * gaussianHessianEntry f j i
          (gaussianInterpolationPoint u p)
        ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
  let μX := multivariateGaussian 0 SX
  let μY := multivariateGaussian 0 SY
  let H : Fin n → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ :=
    fun j p ↦ Real.sqrt (1 - u) * gaussianHessianEntry f j i
      (gaussianInterpolationPoint u p)
  have hg : Integrable (fun p ↦ p.2 i *
      fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) (μX.prod μY) :=
    integrable_second_mul_gradient_interpolation SX SY f hf hDfBound u i
  have hH : ∀ j, Integrable (H j) (μX.prod μY) := fun j ↦
    (integrable_gaussianHessianEntry_interpolation SX SY f hf hHBound u j i).const_mul _
  have hsection : ∀ x,
      (∫ y, y i * fderiv ℝ f
          (Real.sqrt (1 - u) • y + Real.sqrt u • x)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μY) =
        ∑ j, SY i j * ∫ y, H j (x, y) ∂μY := by
    intro x
    have h := multivariateGaussian_gradientCoordinate_affine SY hSY f hf hDfBound hHBound
      (Real.sqrt (1 - u)) (Real.sqrt u • x) i
    simpa [H, μY, gaussianInterpolationPoint, add_comm] using h
  calc
    (∫ p, p.2 i * fderiv ℝ f (gaussianInterpolationPoint u p)
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂(μX.prod μY)) =
        ∫ x, ∫ y, y i * fderiv ℝ f
          (Real.sqrt (1 - u) • y + Real.sqrt u • x)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μY ∂μX := by
      simpa only [gaussianInterpolationPoint, add_comm] using integral_prod _ hg
    _ = ∫ x, ∑ j, SY i j * ∫ y, H j (x, y) ∂μY ∂μX := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hsection x
    _ = ∑ j, ∫ x, SY i j * ∫ y, H j (x, y) ∂μY ∂μX := by
      rw [integral_finsetSum]
      intro j _
      exact (hH j).integral_prod_left.const_mul _
    _ = ∑ j, SY i j * ∫ p, H j p ∂(μX.prod μY) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_prod _ (hH j)]

/-- Expands the expected derivative along the interpolation velocity into first- and second-Gaussian contributions.

**Lean implementation helper.** -/
private lemma integral_fderiv_interpolationVelocity
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    {u : ℝ} (_hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ p, fderiv ℝ f (gaussianInterpolationPoint u p)
        (gaussianInterpolationVelocity u p)
      ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) =
      (∑ i, (1 / (2 * Real.sqrt u)) *
        ∫ p, p.1 i * fderiv ℝ f (gaussianInterpolationPoint u p)
          (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) -
      ∑ i, (1 / (2 * Real.sqrt (1 - u))) *
        ∫ p, p.2 i * fderiv ℝ f (gaussianInterpolationPoint u p)
          (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
  let μ := (multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)
  let GX : Fin n → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ :=
    fun i p ↦ p.1 i * fderiv ℝ f (gaussianInterpolationPoint u p)
      (EuclideanSpace.basisFun (Fin n) ℝ i)
  let GY : Fin n → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ :=
    fun i p ↦ p.2 i * fderiv ℝ f (gaussianInterpolationPoint u p)
      (EuclideanSpace.basisFun (Fin n) ℝ i)
  let a := 1 / (2 * Real.sqrt u)
  let b := 1 / (2 * Real.sqrt (1 - u))
  have hGX : ∀ i, Integrable (GX i) μ := fun i ↦
    integrable_first_mul_gradient_interpolation SX SY f hf hDfBound u i
  have hGY : ∀ i, Integrable (GY i) μ := fun i ↦
    integrable_second_mul_gradient_interpolation SX SY f hf hDfBound u i
  have hpoint : ∀ p,
      fderiv ℝ f (gaussianInterpolationPoint u p)
          (gaussianInterpolationVelocity u p) =
        (∑ i, a * GX i p) - ∑ i, b * GY i p := by
    intro p
    let L := fderiv ℝ f (gaussianInterpolationPoint u p)
    rw [gaussianInterpolationVelocity, map_sub, map_smul, map_smul,
      continuousLinearMap_apply_euclideanBasis L p.1,
      continuousLinearMap_apply_euclideanBasis L p.2]
    simp only [smul_eq_mul, Finset.mul_sum, GX, GY, a, b, L]
  calc
    (∫ p, fderiv ℝ f (gaussianInterpolationPoint u p)
        (gaussianInterpolationVelocity u p) ∂μ) =
        ∫ p, ((∑ i, a * GX i p) - ∑ i, b * GY i p) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact hpoint p
    _ = (∫ p, ∑ i, a * GX i p ∂μ) - ∫ p, ∑ i, b * GY i p ∂μ := by
      rw [integral_sub]
      · exact integrable_finsetSum _ fun i _ ↦ (hGX i).const_mul a
      · exact integrable_finsetSum _ fun i _ ↦ (hGY i).const_mul b
    _ = (∑ i, a * ∫ p, GX i p ∂μ) - ∑ i, b * ∫ p, GY i p ∂μ := by
      rw [integral_finsetSum, integral_finsetSum]
      · apply congrArg₂ (· - ·) <;> apply Finset.sum_congr rfl <;>
          intro i hi <;> rw [integral_const_mul]
      · intro i _
        exact (hGY i).const_mul b
      · intro i _
        exact (hGX i).const_mul a

/-- Uses covariance symmetry to transpose the Hessian indices in a double sum.

**Lean implementation helper.** -/
private lemma covariance_hessian_doubleSum_transpose
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (K : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, S i j * K j i) = ∑ i, ∑ j, S i j * K i j := by
  calc
    (∑ i, ∑ j, S i j * K j i) = ∑ j, ∑ i, S i j * K j i :=
      Finset.sum_comm
    _ = ∑ i, ∑ j, S j i * K i j := rfl
    _ = ∑ i, ∑ j, S i j * K i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show S j i = S i j by simpa using hS.isHermitian.apply i j]

/-- Gaussian interpolation for observables whose gradient and Hessian are
globally bounded. The gradient bound supplies the linear-growth estimate
needed for Gaussian integrability, so the observable itself need not be
bounded; this is the form used for log-sum-exp comparison observables.

**Lean implementation helper.** -/
theorem gaussianInterpolation_of_boundedDerivative
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianInterpolationExpectation SX SY f)
      ((1 / 2 : ℝ) * ∑ i, ∑ j,
        (SX i j - SY i j) *
          ∫ p, gaussianHessianEntry f i j
              (gaussianInterpolationPoint u p)
            ∂((multivariateGaussian 0 SX).prod
              (multivariateGaussian 0 SY))) u := by
  let μ := (multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)
  let K : Fin n → Fin n → ℝ := fun i j ↦
    ∫ p, gaussianHessianEntry f i j (gaussianInterpolationPoint u p) ∂μ
  let a := 1 / (2 * Real.sqrt u)
  let b := 1 / (2 * Real.sqrt (1 - u))
  have hsqrtX : Real.sqrt u ≠ 0 := Real.sqrt_ne_zero'.2 hu.1
  have hsqrtY : Real.sqrt (1 - u) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by linarith [hu.2])
  have hcancelX : a * Real.sqrt u = (1 / 2 : ℝ) := by
    dsimp [a]
    field_simp
  have hcancelY : b * Real.sqrt (1 - u) = (1 / 2 : ℝ) := by
    dsimp [b]
    field_simp
  have hXcoord : ∀ i,
      (∫ p, p.1 i * fderiv ℝ f (gaussianInterpolationPoint u p)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, SX i j * (Real.sqrt u * K j i) := by
    intro i
    simpa only [μ, K, integral_const_mul] using
      integral_first_mul_gradient_interpolation SX SY hSX f hf hDfBound hHBound hu i
  have hYcoord : ∀ i,
      (∫ p, p.2 i * fderiv ℝ f (gaussianInterpolationPoint u p)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, SY i j * (Real.sqrt (1 - u) * K j i) := by
    intro i
    simpa only [μ, K, integral_const_mul] using
      integral_second_mul_gradient_interpolation SX SY hSY f hf hDfBound hHBound hu i
  have hscaleX :
      (∑ i, a * ∑ j, SX i j * (Real.sqrt u * K j i)) =
        (1 / 2 : ℝ) * ∑ i, ∑ j, SX i j * K j i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      a * (SX i j * (Real.sqrt u * K j i)) =
          (a * Real.sqrt u) * (SX i j * K j i) := by ring
      _ = (1 / 2 : ℝ) * (SX i j * K j i) := by rw [hcancelX]
  have hscaleY :
      (∑ i, b * ∑ j, SY i j * (Real.sqrt (1 - u) * K j i)) =
        (1 / 2 : ℝ) * ∑ i, ∑ j, SY i j * K j i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      b * (SY i j * (Real.sqrt (1 - u) * K j i)) =
          (b * Real.sqrt (1 - u)) * (SY i j * K j i) := by ring
      _ = (1 / 2 : ℝ) * (SY i j * K j i) := by rw [hcancelY]
  have hraw := hasDerivAt_gaussianInterpolationExpectation_raw SX SY f hf hDfBound hu
  apply hraw.congr_deriv
  calc
    (∫ p, fderiv ℝ f (gaussianInterpolationPoint u p)
        (gaussianInterpolationVelocity u p) ∂μ) =
        (∑ i, a * ∫ p, p.1 i * fderiv ℝ f
          (gaussianInterpolationPoint u p)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) -
        ∑ i, b * ∫ p, p.2 i * fderiv ℝ f
          (gaussianInterpolationPoint u p)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ := by
      simpa only [μ, a, b] using
        integral_fderiv_interpolationVelocity SX SY f hf hDfBound hu
    _ = (∑ i, a * ∑ j, SX i j * (Real.sqrt u * K j i)) -
        ∑ i, b * ∑ j, SY i j * (Real.sqrt (1 - u) * K j i) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [hXcoord i]
      · apply Finset.sum_congr rfl
        intro i _
        rw [hYcoord i]
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, SX i j * K j i) -
        (1 / 2 : ℝ) * (∑ i, ∑ j, SY i j * K j i) := by
      rw [hscaleX, hscaleY]
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, SX i j * K i j) -
        (1 / 2 : ℝ) * (∑ i, ∑ j, SY i j * K i j) := by
      rw [covariance_hessian_doubleSum_transpose SX hSX K,
        covariance_hessian_doubleSum_transpose SY hSY K]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j, (SX i j - SY i j) * K i j := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      ring

/-- Backwards-compatible bounded-observable wrapper around
`gaussianInterpolation_of_boundedDerivative`.

**Lean implementation helper.** -/
theorem gaussianInterpolation_of_bounded
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (_hfBound : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianInterpolationExpectation SX SY f)
      ((1 / 2 : ℝ) * ∑ i, ∑ j,
        (SX i j - SY i j) *
          ∫ p, gaussianHessianEntry f i j
              (gaussianInterpolationPoint u p)
            ∂((multivariateGaussian 0 SX).prod
              (multivariateGaussian 0 SY))) u := by
  exact gaussianInterpolation_of_boundedDerivative
    SX SY hSX hSY f hf hDfBound hHBound hu

set_option maxHeartbeats 1200000 in
-- Compact support is converted into uniform first- and second-derivative
-- bounds here; elaborating that analytic bridge exceeds the default budget.
/-- The derivative of an interpolated Gaussian expectation is one half the covariance difference contracted with the expected Hessian. The direct square-root differentiation is asserted only for `u ∈ (0,1)`;
endpoint comparison is obtained later from continuity.

**Book Lemma 7.2.5.** -/
theorem gaussianInterpolation
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianInterpolationExpectation SX SY f)
      ((1 / 2 : ℝ) * ∑ i, ∑ j,
        (SX i j - SY i j) *
          ∫ p, gaussianHessianEntry f i j
              (gaussianInterpolationPoint u p)
            ∂((multivariateGaussian 0 SX).prod
              (multivariateGaussian 0 SY))) u := by
  have hDfCompact : HasCompactSupport (fderiv ℝ f) := hcompact.fderiv ℝ
  have hDfCont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C := by
    intro i j
    have hsupp := (hcompact.fderiv_apply ℝ
      (EuclideanSpace.basisFun (Fin n) ℝ j)).fderiv_apply ℝ
        (EuclideanSpace.basisFun (Fin n) ℝ i)
    have heq : (fun x ↦ fderiv ℝ
        (fun z ↦ fderiv ℝ f z (EuclideanSpace.basisFun (Fin n) ℝ j)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)) = gaussianHessianEntry f i j := by
      funext x
      simpa using fderiv_gradientCoordinate_affine f hf 1 0 j i x
    rw [heq] at hsupp
    exact hsupp.exists_bound_of_continuous
      (gaussianHessianEntry_continuous f hf i j)
  apply gaussianInterpolation_of_bounded SX SY hSX hSY f hf
  · exact hcompact.exists_bound_of_continuous hf.continuous
  · exact hDfCompact.exists_bound_of_continuous hDfCont
  · exact hHBound
  · exact hu

/-- A bounded continuous observable has a continuous expectation along the
closed Gaussian interpolation interval (in fact, on all of `ℝ`).

**Lean implementation helper.** -/
theorem continuous_gaussianInterpolationExpectation_of_bounded
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hfBound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Continuous (gaussianInterpolationExpectation SX SY f) := by
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨C, hC⟩ := hfBound
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
  · filter_upwards [] with v
    exact (hf.comp (by unfold gaussianInterpolationPoint; fun_prop)).aestronglyMeasurable
  · filter_upwards [] with v
    filter_upwards [] with p
    exact hC _
  · exact integrable_const_iff.2 (Or.inr inferInstance)
  · filter_upwards [] with p
    exact (hf.comp (by unfold gaussianInterpolationPoint; fun_prop)).continuousAt

/-- A continuously differentiable function with uniformly bounded derivative is integrable under every centered multivariate Gaussian law.

**Lean implementation helper.** -/
private lemma integrable_multivariateGaussian_of_fderiv_bound
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    Integrable f (multivariateGaussian 0 S) := by
  obtain ⟨C, hC⟩ := hDfBound
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ C' := fun x ↦
    (hC x).trans (le_max_left _ _)
  let bound : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x ↦ C' * ‖x‖ + ‖f 0‖
  have hbound : Integrable bound (multivariateGaussian 0 S) := by
    exact ((IsGaussian.integrable_id.norm.const_mul C').add
      (integrable_const_iff.2 (Or.inr inferInstance)))
  apply hbound.mono' hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  exact norm_apply_le_linear_of_fderiv_bound f
    (hf.differentiable (by norm_num)) C' hderiv x

/-- Linear-growth version of continuity along the closed interpolation
interval. A bounded gradient is enough to dominate the observable by an
integrable affine function of the two Gaussian norms.

**Lean implementation helper.** -/
theorem continuousOn_gaussianInterpolationExpectation_of_boundedDerivative
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    ContinuousOn (gaussianInterpolationExpectation SX SY f) (Icc (0 : ℝ) 1) := by
  intro u hu
  obtain ⟨C, hC⟩ := hDfBound
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ C' := fun x ↦
    (hC x).trans (le_max_left _ _)
  let bound : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p ↦ C' * (‖p.1‖ + ‖p.2‖) + ‖f 0‖
  have hbound : Integrable bound
      ((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) := by
    have hX : Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ ‖p.1‖)
        ((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) :=
      IsGaussian.integrable_id.norm.comp_fst _
    have hY : Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ ‖p.2‖)
        ((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY)) :=
      IsGaussian.integrable_id.norm.comp_snd _
    exact (((hX.add hY).const_mul C').add
      (integrable_const_iff.2 (Or.inr inferInstance)))
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [] with v
    exact (hf.continuous.comp
      (continuous_gaussianInterpolationPoint v)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with v hv
    filter_upwards [] with p
    have hsv : |Real.sqrt v| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
      exact hv.2
    have hs1v : |Real.sqrt (1 - v)| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
      linarith [hv.1]
    calc
      ‖f (gaussianInterpolationPoint v p)‖ ≤
          C' * ‖gaussianInterpolationPoint v p‖ + ‖f 0‖ :=
        norm_apply_le_linear_of_fderiv_bound f
          (hf.differentiable (by norm_num)) C' hderiv _
      _ ≤ C' * (‖p.1‖ + ‖p.2‖) + ‖f 0‖ := by
        gcongr
        unfold gaussianInterpolationPoint
        calc
          ‖Real.sqrt v • p.1 + Real.sqrt (1 - v) • p.2‖ ≤
              ‖Real.sqrt v • p.1‖ + ‖Real.sqrt (1 - v) • p.2‖ := norm_add_le _ _
          _ = |Real.sqrt v| * ‖p.1‖ + |Real.sqrt (1 - v)| * ‖p.2‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖p.1‖ + ‖p.2‖ := by
            exact add_le_add
              (by simpa using mul_le_mul_of_nonneg_right hsv (norm_nonneg p.1))
              (by simpa using mul_le_mul_of_nonneg_right hs1v (norm_nonneg p.2))
      _ = bound p := rfl
  · exact hbound
  · filter_upwards [] with p
    exact (hf.continuous.comp
      (by unfold gaussianInterpolationPoint; fun_prop)).continuousWithinAt

/-- The `u = 0` endpoint for an observable with bounded derivative.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_zero_of_boundedDerivative
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    gaussianInterpolationExpectation SX SY f 0 =
      ∫ x, f x ∂multivariateGaussian 0 SY := by
  have hfi := integrable_multivariateGaussian_of_fderiv_bound SY f hf hDfBound
  unfold gaussianInterpolationExpectation gaussianInterpolationPoint
  simp only [Real.sqrt_zero, zero_smul, zero_add, sub_zero, Real.sqrt_one, one_smul]
  rw [integral_prod_symm]
  · simp
  · exact hfi.comp_snd _

/-- The `u = 1` endpoint for an observable with bounded derivative.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_one_of_boundedDerivative
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    gaussianInterpolationExpectation SX SY f 1 =
      ∫ x, f x ∂multivariateGaussian 0 SX := by
  have hfi := integrable_multivariateGaussian_of_fderiv_bound SX f hf hDfBound
  unfold gaussianInterpolationExpectation gaussianInterpolationPoint
  simp only [Real.sqrt_one, one_smul, sub_self, Real.sqrt_zero, zero_smul, add_zero]
  rw [integral_prod]
  · simp
  · exact hfi.comp_fst _

/-- The `u = 0` endpoint of Gaussian interpolation is the `SY` law.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_zero
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hfBound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    gaussianInterpolationExpectation SX SY f 0 =
      ∫ x, f x ∂multivariateGaussian 0 SY := by
  obtain ⟨C, hC⟩ := hfBound
  have hfi : Integrable f (multivariateGaussian 0 SY) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  unfold gaussianInterpolationExpectation gaussianInterpolationPoint
  simp only [Real.sqrt_zero, zero_smul, zero_add, sub_zero, Real.sqrt_one, one_smul]
  rw [integral_prod_symm]
  · simp
  · exact hfi.comp_snd _

/-- The `u = 1` endpoint of Gaussian interpolation is the `SX` law.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_one
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hfBound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    gaussianInterpolationExpectation SX SY f 1 =
      ∫ x, f x ∂multivariateGaussian 0 SX := by
  obtain ⟨C, hC⟩ := hfBound
  have hfi : Integrable f (multivariateGaussian 0 SX) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  unfold gaussianInterpolationExpectation gaussianInterpolationPoint
  simp only [Real.sqrt_one, one_smul, sub_self, Real.sqrt_zero, zero_smul, add_zero]
  rw [integral_prod]
  · simp
  · exact hfi.comp_fst _

/-- Endpoint comparison obtained from the interpolation identity when the
covariance--Hessian contraction is nonnegative on the open interval.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_le_of_hessianSum_nonneg
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hfBound : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C)
    (hnonneg : ∀ u ∈ Ioo (0 : ℝ) 1,
      0 ≤ ∑ i, ∑ j, (SX i j - SY i j) *
        ∫ p, gaussianHessianEntry f i j (gaussianInterpolationPoint u p)
          ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) :
    (∫ x, f x ∂multivariateGaussian 0 SY) ≤
      ∫ x, f x ∂multivariateGaussian 0 SX := by
  let F := gaussianInterpolationExpectation SX SY f
  have hcont : Continuous F :=
    continuous_gaussianInterpolationExpectation_of_bounded SX SY f hf.continuous hfBound
  have hdiff : DifferentiableOn ℝ F (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro u hu
    exact (gaussianInterpolation_of_bounded SX SY hSX hSY f hf
      hfBound hDfBound hHBound hu).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Icc (0 : ℝ) 1), 0 ≤ deriv F u := by
    intro u hu
    rw [interior_Icc] at hu
    have hd := gaussianInterpolation_of_bounded SX SY hSX hSY f hf
      hfBound hDfBound hHBound hu
    rw [hd.deriv]
    exact mul_nonneg (by norm_num) (hnonneg u hu)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hcont.continuousOn hdiff hderiv
  have h01 := hmono (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  change gaussianInterpolationExpectation SX SY f 0 ≤
    gaussianInterpolationExpectation SX SY f 1 at h01
  rw [gaussianInterpolationExpectation_zero SX SY f hf.continuous hfBound,
    gaussianInterpolationExpectation_one SX SY f hf.continuous hfBound] at h01
  exact h01

/-- Endpoint comparison for possibly unbounded observables with globally
bounded gradient and Hessian. This is the linear-growth interpolation API
used by the finite log-sum-exp proof of Sudakov--Fernique.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_le_of_hessianSum_nonneg_boundedDerivative
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hDfBound : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C)
    (hnonneg : ∀ u ∈ Ioo (0 : ℝ) 1,
      0 ≤ ∑ i, ∑ j, (SX i j - SY i j) *
        ∫ p, gaussianHessianEntry f i j (gaussianInterpolationPoint u p)
          ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) :
    (∫ x, f x ∂multivariateGaussian 0 SY) ≤
      ∫ x, f x ∂multivariateGaussian 0 SX := by
  let F := gaussianInterpolationExpectation SX SY f
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    continuousOn_gaussianInterpolationExpectation_of_boundedDerivative
      SX SY f (hf.of_le (by norm_num)) hDfBound
  have hdiff : DifferentiableOn ℝ F (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro u hu
    exact (gaussianInterpolation_of_boundedDerivative SX SY hSX hSY f hf
      hDfBound hHBound hu).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Icc (0 : ℝ) 1), 0 ≤ deriv F u := by
    intro u hu
    rw [interior_Icc] at hu
    have hd := gaussianInterpolation_of_boundedDerivative
      SX SY hSX hSY f hf hDfBound hHBound hu
    rw [hd.deriv]
    exact mul_nonneg (by norm_num) (hnonneg u hu)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hcont hdiff hderiv
  have h01 := hmono (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  change gaussianInterpolationExpectation SX SY f 0 ≤
    gaussianInterpolationExpectation SX SY f 1 at h01
  rw [gaussianInterpolationExpectation_zero_of_boundedDerivative
      SX SY f (hf.of_le (by norm_num)) hDfBound,
    gaussianInterpolationExpectation_one_of_boundedDerivative
      SX SY f (hf.of_le (by norm_num)) hDfBound] at h01
  exact h01

/-- Coordinate-bounded version of
`gaussianInterpolationExpectation_le_of_hessianSum_nonneg`. It is often
more convenient for explicit soft-max and smooth-event observables.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_le_of_hessianSum_nonneg_coordinate
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hfBound : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hcoord : ∀ i, ∃ C, ∀ x,
      ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ C)
    (hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C)
    (hnonneg : ∀ u ∈ Ioo (0 : ℝ) 1,
      0 ≤ ∑ i, ∑ j, (SX i j - SY i j) *
        ∫ p, gaussianHessianEntry f i j (gaussianInterpolationPoint u p)
          ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) :
    (∫ x, f x ∂multivariateGaussian 0 SY) ≤
      ∫ x, f x ∂multivariateGaussian 0 SX := by
  exact gaussianInterpolationExpectation_le_of_hessianSum_nonneg
    SX SY hSX hSY f hf hfBound
      (fderiv_opNorm_bounded_of_coordinate_bounded f hcoord) hHBound hnonneg

/-- Coordinate-gradient wrapper for the linear-growth endpoint comparison.

**Lean implementation helper.** -/
theorem gaussianInterpolationExpectation_le_of_hessianSum_nonneg_boundedDerivative_coordinate
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hcoord : ∀ i, ∃ C, ∀ x,
      ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ C)
    (hHBound : ∀ i j, ∃ C, ∀ x, ‖gaussianHessianEntry f i j x‖ ≤ C)
    (hnonneg : ∀ u ∈ Ioo (0 : ℝ) 1,
      0 ≤ ∑ i, ∑ j, (SX i j - SY i j) *
        ∫ p, gaussianHessianEntry f i j (gaussianInterpolationPoint u p)
          ∂((multivariateGaussian 0 SX).prod (multivariateGaussian 0 SY))) :
    (∫ x, f x ∂multivariateGaussian 0 SY) ≤
      ∫ x, f x ∂multivariateGaussian 0 SX := by
  exact gaussianInterpolationExpectation_le_of_hessianSum_nonneg_boundedDerivative
    SX SY hSX hSY f hf
      (fderiv_opNorm_bounded_of_coordinate_bounded f hcoord) hHBound hnonneg

/-- The derivative of an interpolated Gaussian expectation is one half the covariance difference contracted with the expected Hessian. The covariance matrix of the interpolation is the affine interpolation
of the two input covariance matrices. This source display is recorded as a
pointwise matrix identity, avoiding any invertibility assumption.

**Book Lemma 7.2.5.** -/
theorem gaussianInterpolation_covariance_entry
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (i j : Fin n) :
    u * SX i j + (1 - u) * SY i j =
      (u • SX + (1 - u) • SY) i j := by
  simp

end

end HDP.Chapter7

end Source_04_GaussianInterpolation

/-! ## Material formerly in `05_GaussianComparison.lean` -/

section Source_05_GaussianComparison

/-!
# Book Chapter 7, §7.2: Gaussian comparison inequalities

All public comparisons use finite nonempty index types.  This is the precise
finite-dimensional content behind Remark 7.2.1's convention for arbitrary
index sets.  The two processes may live on different probability spaces.
-/

open MeasureTheory ProbabilityTheory Real Set Matrix Filter
open scoped BigOperators RealInnerProductSpace MatrixOrder Topology

namespace HDP.Chapter7

noncomputable section

/-- For arbitrary index sets, expected suprema are interpreted as suprema of finite-subset expected maxima. Expected maximum of a finite nonempty process.

**Book Remark 7.2.1.** -/
def expectedFiniteSupremum {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] (μ : Measure Ω) (X : I → Ω → ℝ) : ℝ :=
  ∫ ω, HDP.Chapter5.finiteMaximum X ω ∂μ

/-- Second moment of a process coordinate.

**Lean implementation helper.** -/
def processSecondMoment {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) (i : I) : ℝ :=
  ∫ ω, X i ω ^ 2 ∂μ

/-- Squared canonical increment of a real process.

**Lean implementation helper.** -/
def processIncrementSecondMoment {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) (i j : I) : ℝ :=
  ∫ ω, (X i ω - X j ω) ^ 2 ∂μ

/-- The finite off-diagonal expression obtained in Exercise 7.7 after
substituting the Hessian of the log-partition function into the Gaussian
interpolation formula. In the source, `q i j` is
`E[p_i(Z(u)) p_j(Z(u))]`.

**Book Exercise 7.7.** -/
def logPartitionDerivativeExpression {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (dX dY q : I → I → ℝ) : ℝ :=
  (β / 4) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    (dX i j - dY i j) * q i j

/-- Differentiate log-sum-exp under interpolation to prove Sudakov--Fernique. Once Gaussian integration by
parts has produced the source's derivative formula, increment domination and
nonnegativity of the softmax-weight products make every off-diagonal summand
nonpositive. This is the complete finite algebraic calculation used by the
verified log-sum-exp interpolation proof.

**Book Exercise 7.7.** -/
theorem exercise_7_7_logPartitionDerivativeExpression_nonpos
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (hβ : 0 ≤ β)
    (dX dY q : I → I → ℝ)
    (hinc : ∀ i j, dX i j ≤ dY i j)
    (hq : ∀ i j, 0 ≤ q i j) :
    logPartitionDerivativeExpression β dX dY q ≤ 0 := by
  have hrow : ∀ i : I,
      (∑ j ∈ Finset.univ.erase i,
        (dX i j - dY i j) * q i j) ≤ 0 := by
    intro i
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hinc i j)) (hq i j)
  have hsum :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        (dX i j - dY i j) * q i j) ≤ 0 := by
    exact Finset.sum_nonpos fun i _ ↦ hrow i
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 4)) hsum

/-- Differentiate log-sum-exp under interpolation to prove Sudakov--Fernique. This source-facing
wrapper records the exact conclusion for the expected log-partition function:
any derivative furnished by the interpolation formula is nonpositive. The
premise `hderiv` exposes the source's derivative identity, while this theorem
records its exact algebraic sign consequence.

**Book Exercise 7.7.** -/
theorem exercise_7_7_expectedLogPartition_derivative_nonpos
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : ℝ → ℝ) (u β : ℝ) (hβ : 0 ≤ β)
    (dX dY q : I → I → ℝ)
    (hinc : ∀ i j, dX i j ≤ dY i j)
    (hq : ∀ i j, 0 ≤ q i j)
    (hderiv : HasDerivAt F
      (logPartitionDerivativeExpression β dX dY q) u) :
    ∃ d : ℝ, HasDerivAt F d u ∧ d ≤ 0 := by
  exact ⟨logPartitionDerivativeExpression β dX dY q, hderiv,
    exercise_7_7_logPartitionDerivativeExpression_nonpos
      β hβ dX dY q hinc hq⟩

/-- Minimum over one finite index and maximum over another.

**Lean implementation helper.** -/
def finiteMinimax {U T Ω : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] (X : U → T → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun u ↦ HDP.Chapter5.finiteMaximum (X u) ω)

/-! ### Private finite-dimensional Gaussian-law bridge for comparison -/

/-- Defines coordinate evaluation as a continuous linear functional for the Gaussian comparison argument.

**Lean implementation helper.** -/
private def comparisonCoordCLM {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The comparison coordinate functional evaluates the selected Euclidean coordinate.

**Lean implementation helper.** -/
private lemma comparisonCoordCLM_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : comparisonCoordCLM i x = x i := by
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x i

/-- Defines the sum of coordinatewise exponential penalties above a threshold.

**Lean implementation helper.** -/
private def orthantEnergy {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, Real.exp (β * (x i - a))

/-- Defines the exponential of the negative orthant energy, a smooth approximation to an orthant indicator.

**Lean implementation helper.** -/
private def orthantSmoother {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-orthantEnergy β a x)

/-- Computes the Fréchet derivative of the orthant energy at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_orthantEnergy {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (orthantEnergy β a)
      (∑ i, Real.exp (β * (x i - a)) • (β • comparisonCoordCLM i)) x := by
  have hcomp : ∀ i : Fin n, HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ Real.exp (β * (z i - a)))
      (Real.exp (β * (x i - a)) • (β • comparisonCoordCLM i)) x := by
    intro i
    have hc : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ β * (z i - a))
        (β • comparisonCoordCLM i) x := by
      simpa [comparisonCoordCLM_apply] using
        ((comparisonCoordCLM i).hasFDerivAt.sub_const a).const_mul β
    simpa using hc.exp
  change HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦
    ∑ i, Real.exp (β * (z i - a))) _ x
  exact HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ ↦ hcomp i)

/-- Computes the Fréchet derivative of the orthant smoother at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_orthantSmoother {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (orthantSmoother β a)
      (Real.exp (-orthantEnergy β a x) •
        (-(∑ i, Real.exp (β * (x i - a)) •
          (β • comparisonCoordCLM i)))) x := by
  unfold orthantSmoother
  simpa using (hasFDerivAt_orthantEnergy β a x).neg.exp

/-- Computes the directional derivative of the orthant smoother along a standard basis vector.

**Lean implementation helper.** -/
private lemma fderiv_orthantSmoother_basis {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderiv ℝ (orthantSmoother β a) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      -β * Real.exp (β * (x i - a)) * orthantSmoother β a x := by
  rw [(hasFDerivAt_orthantSmoother β a x).fderiv]
  simp [orthantSmoother, comparisonCoordCLM_apply]
  ring

/-- Collects the coordinates of a finite stochastic process into a Euclidean-valued random vector.

**Lean implementation helper.** -/
def processEuclideanVector {I Ω : Type*} [Fintype I]
    [MeasurableSpace Ω] (X : I → Ω → ℝ) :
    Ω → EuclideanSpace ℝ I := fun ω ↦ WithLp.toLp 2 (fun i ↦ X i ω)

/-- The process Euclidean vector has a Gaussian probability law.

**Lean implementation helper.** -/
lemma processEuclideanVector_hasGaussianLaw
    {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ}
    (hX : IsGaussianProcess X μ) :
    HasGaussianLaw (processEuclideanVector X) μ := by
  let J := {i : I // i ∈ (Finset.univ : Finset I)}
  let L : (J → ℝ) →L[ℝ] (I → ℝ) :=
    { toFun := fun z i ↦ z ⟨i, Finset.mem_univ i⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hfull := hX.hasGaussianLaw (Finset.univ : Finset I)
  have hpi : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω : I → ℝ)) μ := by
    have hm := hfull.map L
    simpa [L, Finset.restrict_def, Function.comp_def, J] using hm
  exact hpi.toLp_pi 2

/-- Defines the covariance matrix of a Euclidean-valued measure from its covariance bilinear form.

**Lean implementation helper.** -/
def gaussianMeasureCovarianceMatrix {I : Type*} [Fintype I]
    (ν : Measure (EuclideanSpace ℝ I)) : Matrix I I ℝ :=
  fun i j ↦ covarianceBilin ν
    (EuclideanSpace.basisFun I ℝ i) (EuclideanSpace.basisFun I ℝ j)

/-- The Gaussian measure covariance matrix is positive semidefinite.

**Lean implementation helper.** -/
lemma gaussianMeasureCovarianceMatrix_posSemidef
    {I : Type*} [Fintype I] (ν : Measure (EuclideanSpace ℝ I)) :
    (gaussianMeasureCovarianceMatrix ν).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa [gaussianMeasureCovarianceMatrix] using
      covarianceBilin_comm (μ := ν)
        (EuclideanSpace.basisFun I ℝ j) (EuclideanSpace.basisFun I ℝ i)
  · intro v
    let z : EuclideanSpace ℝ I := WithLp.toLp 2 v
    have hz : z = ∑ i, v i • EuclideanSpace.basisFun I ℝ i := by
      symm
      simpa [z] using (EuclideanSpace.basisFun I ℝ).sum_repr z
    calc
      star v ⬝ᵥ (gaussianMeasureCovarianceMatrix ν *ᵥ v) =
          covarianceBilin ν z z := by
        rw [hz]
        simp only [dotProduct, Matrix.mulVec, gaussianMeasureCovarianceMatrix,
          Finset.mul_sum, star_trivial, EuclideanSpace.basisFun_apply, map_sum,
          map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro i _
        rw [covarianceBilin_comm]
        ring
      _ ≥ 0 := covarianceBilin_self_nonneg z

/-- The Gaussian law built from a measure's covariance matrix has the same covariance bilinear form as that measure.

**Lean implementation helper.** -/
private lemma covarianceBilin_multivariateGaussian_gaussianMeasureCovarianceMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (ν : Measure (EuclideanSpace ℝ I)) [IsFiniteMeasure ν]
    (m : EuclideanSpace ℝ I) :
    covarianceBilin (multivariateGaussian m (gaussianMeasureCovarianceMatrix ν)) =
      covarianceBilin ν := by
  classical
  let b : Module.Basis I ℝ (EuclideanSpace ℝ I) :=
    (EuclideanSpace.basisFun I ℝ).toBasis
  have hS := gaussianMeasureCovarianceMatrix_posSemidef ν
  apply ContinuousLinearMap.ext
  intro x
  conv_lhs => rw [← b.sum_repr x]
  conv_rhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply ContinuousLinearMap.ext
  intro y
  conv_lhs => rw [← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr y]
  simp only [map_sum, map_smul, _root_.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [covarianceBilin_multivariateGaussian hS]
  simp [b, gaussianMeasureCovarianceMatrix]

/-- A centered Gaussian measure equals the multivariate Gaussian law determined by its covariance matrix.

**Lean implementation helper.** -/
private lemma gaussianMeasure_eq_multivariateGaussian_covariance
    {I : Type*} [Fintype I] [DecidableEq I]
    (ν : Measure (EuclideanSpace ℝ I)) [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0) :
    ν = multivariateGaussian 0 (gaussianMeasureCovarianceMatrix ν) := by
  apply IsGaussian.ext
  · simpa using hmean
  · exact
      (covarianceBilin_multivariateGaussian_gaussianMeasureCovarianceMatrix ν 0).symm

/-- A finite-dimensional Gaussian measure equals the multivariate Gaussian law
with its actual mean and covariance matrix.

**Lean implementation helper.** -/
private lemma gaussianMeasure_eq_multivariateGaussian_mean_covariance
    {I : Type*} [Fintype I] [DecidableEq I]
    (ν : Measure (EuclideanSpace ℝ I)) [IsGaussian ν] :
    ν = multivariateGaussian (∫ x, x ∂ν)
      (gaussianMeasureCovarianceMatrix ν) := by
  apply IsGaussian.ext
  · exact integral_id_multivariateGaussian.symm
  · exact
      (covarianceBilin_multivariateGaussian_gaussianMeasureCovarianceMatrix ν
        (∫ x, x ∂ν)).symm

/-- The mean of the Euclidean process vector is the vector of coordinatewise means.

**Lean implementation helper.** -/
private lemma processEuclideanVector_integral
    {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ}
    (hX : IsGaussianProcess X μ) :
    ∫ ω, processEuclideanVector X ω ∂μ =
      WithLp.toLp 2 (fun i ↦ ∫ ω, X i ω ∂μ) := by
  let V := processEuclideanVector X
  have hV := processEuclideanVector_hasGaussianLaw hX
  apply WithLp.ofLp_injective
  ext i
  simpa [V, processEuclideanVector] using
    (ContinuousLinearMap.integral_comp_comm
      (EuclideanSpace.proj i) hV.integrable).symm

/-- The law of a finite Gaussian process vector is the multivariate Gaussian
with its coordinatewise mean and covariance matrix.

**Lean implementation helper.** -/
lemma processEuclideanVector_law_eq_multivariateGaussian_mean_covariance
    {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ}
    (hX : IsGaussianProcess X μ) :
    Measure.map (processEuclideanVector X) μ =
      multivariateGaussian
        (WithLp.toLp 2 (fun i ↦ ∫ ω, X i ω ∂μ))
        (gaussianMeasureCovarianceMatrix
          (Measure.map (processEuclideanVector X) μ)) := by
  let ν := Measure.map (processEuclideanVector X) μ
  have hV := processEuclideanVector_hasGaussianLaw hX
  haveI : IsGaussian ν := hV.isGaussian_map
  change ν =
    multivariateGaussian
      (WithLp.toLp 2 (fun i ↦ ∫ ω, X i ω ∂μ))
      (gaussianMeasureCovarianceMatrix ν)
  calc
    ν = multivariateGaussian (∫ x, x ∂ν)
        (gaussianMeasureCovarianceMatrix ν) :=
      gaussianMeasure_eq_multivariateGaussian_mean_covariance ν
    _ = multivariateGaussian
        (WithLp.toLp 2 (fun i ↦ ∫ ω, X i ω ∂μ))
        (gaussianMeasureCovarianceMatrix ν) := by
      rw [integral_map hV.aemeasurable (by fun_prop),
        processEuclideanVector_integral hX]

/-- Every finite Gaussian process is an affine canonical Gaussian process in
law, with coefficient norms equal to the marginal standard deviations.

**Book Lemma 7.1.12.** -/
theorem finiteGaussianProcess_affine_representation
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Fin n → Ω → ℝ}
    (hX : IsGaussianProcess X μ) :
    ∃ (a : Fin n → EuclideanSpace ℝ (Fin n)) (b : Fin n → ℝ),
      IdentDistrib (processEuclideanVector X)
        (fun g ↦ WithLp.toLp 2
          (fun i ↦ HDP.Chapter5.gaussianAffineFamily a b i g))
        μ (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      ∀ i, ‖a i‖ = Real.sqrt Var[X i; μ] := by
  classical
  let V := processEuclideanVector X
  let ν := Measure.map V μ
  let S := gaussianMeasureCovarianceMatrix ν
  let b : Fin n → ℝ := fun i ↦ ∫ ω, X i ω ∂μ
  let a : Fin n → EuclideanSpace ℝ (Fin n) :=
    canonicalCovariancePoint S
  let Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun g ↦ WithLp.toLp 2
      (fun i ↦ HDP.Chapter5.gaussianAffineFamily a b i g)
  have hVg := processEuclideanVector_hasGaussianLaw hX
  have hVlaw : HasLaw V (multivariateGaussian (WithLp.toLp 2 b) S) μ := by
    refine ⟨hVg.aemeasurable, ?_⟩
    simpa [V, ν, S, b] using
      processEuclideanVector_law_eq_multivariateGaussian_mean_covariance hX
  have hYeq :
      Y = fun g ↦ WithLp.toLp 2 b +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) g := by
    funext g
    ext i
    change b i + inner ℝ (canonicalCovariancePoint S i) g =
      b i + canonicalCovarianceVector S g i
    rw [canonicalCovarianceVector_apply]
  have hYlaw : HasLaw Y (multivariateGaussian (WithLp.toLp 2 b) S)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    refine ⟨hYeq ▸ (by fun_prop), ?_⟩
    change
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map Y =
        (stdGaussian (EuclideanSpace ℝ (Fin n))).map
          (fun g ↦ WithLp.toLp 2 b +
            Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) g)
    rw [hYeq]
  have hid : IdentDistrib V Y μ
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    hVlaw.identDistrib hYlaw
  refine ⟨a, b, ?_, ?_⟩
  · simpa [V, Y] using hid
  · intro i
    have hi := hid.comp (EuclideanSpace.proj i).measurable
    have hvar : Var[X i; μ] =
        Var[fun g ↦ HDP.Chapter5.gaussianAffineFamily a b i g;
          stdGaussian (EuclideanSpace ℝ (Fin n))] := by
      have hvariance := hi.variance_eq
      change Var[X i; μ] =
        Var[fun g ↦ HDP.Chapter5.gaussianAffineFamily a b i g;
          stdGaussian (EuclideanSpace ℝ (Fin n))] at hvariance
      exact hvariance
    have hcanonical :
        Var[fun g ↦ HDP.Chapter5.gaussianAffineFamily a b i g;
          stdGaussian (EuclideanSpace ℝ (Fin n))] = ‖a i‖ ^ 2 := by
      rw [show (fun g ↦ HDP.Chapter5.gaussianAffineFamily a b i g) =
        fun g ↦ b i + canonicalGaussianProcess a i g by
          funext g
          rfl]
      rw [variance_const_add
          ((canonicalGaussianProcess_isGaussian a).aemeasurable i).aestronglyMeasurable,
        canonicalGaussianProcess_variance]
    rw [hcanonical] at hvar
    rw [hvar, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The largest marginal standard deviation of a nonempty finite process.

**Lean implementation helper.** -/
def finiteGaussianProcessStdDev
    {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (X : I → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i ↦ Real.sqrt Var[X i; μ])

/-- The centered maximum of an arbitrary nonempty finite Gaussian process is
sub-Gaussian, with `ψ₂` norm bounded by a universal constant times the largest
marginal standard deviation.

**Book Theorem 7.1.11.** -/
theorem finiteGaussianProcess_concentration
    {n : ℕ} [NeZero n] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Fin n → Ω → ℝ}
    (hX : IsGaussianProcess X μ) :
    let M : Ω → ℝ := HDP.Chapter5.finiteMaximum X
    HDP.SubGaussian (fun ω ↦ M ω - ∫ η, M η ∂μ) μ ∧
      HDP.psi2Norm (fun ω ↦ M ω - ∫ η, M η ∂μ) μ ≤
        2 * Real.sqrt 5 * finiteGaussianProcessStdDev X μ := by
  classical
  let M : Ω → ℝ := HDP.Chapter5.finiteMaximum X
  rcases finiteGaussianProcess_affine_representation hX with
    ⟨a, b, hid, hnorm⟩
  let maxVec : EuclideanSpace ℝ (Fin n) → ℝ :=
    HDP.Chapter5.finiteMaximum
      (fun i : Fin n ↦ fun x : EuclideanSpace ℝ (Fin n) ↦ x i)
  let MC : EuclideanSpace ℝ (Fin n) → ℝ :=
    HDP.Chapter5.finiteMaximum (HDP.Chapter5.gaussianAffineFamily a b)
  have hmaxVec : Continuous maxVec := by
    unfold maxVec HDP.Chapter5.finiteMaximum
    exact Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun _ _ ↦ by fun_prop)
  have hMC : Continuous MC := by
    unfold MC HDP.Chapter5.finiteMaximum
    exact Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun _ _ ↦ by
        unfold HDP.Chapter5.gaussianAffineFamily
        fun_prop)
  have hidMaxVec := hid.comp hmaxVec.measurable
  have hidMax :
      IdentDistrib M
        (fun g ↦ maxVec (WithLp.toLp 2
          (fun i ↦ HDP.Chapter5.gaussianAffineFamily a b i g)))
        μ (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    convert hidMaxVec using 1 <;>
      ext <;> rfl
  have hToLp : HasLaw (WithLp.toLp 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (HDP.Chapter5.gaussianPiMeasure n) := by
    refine ⟨(WithLp.measurable_toLp 2 (Fin n → ℝ)).aemeasurable, ?_⟩
    exact map_pi_eq_stdGaussian
  have hId : HasLaw (id : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    HasLaw.id
  have hidToLp := hToLp.identDistrib hId
  have hidCanonicalVec := hidToLp.comp hMC.measurable
  have hidCanonical :
      IdentDistrib (fun z : Fin n → ℝ ↦ MC (WithLp.toLp 2 z))
        MC
        (HDP.Chapter5.gaussianPiMeasure n)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    convert hidCanonicalVec using 1 <;>
      ext <;> rfl
  have hidMaxCanonical :
      IdentDistrib M MC μ
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    convert hidMax using 1 <;>
      ext <;> rfl
  have hidRawCanonical :
      IdentDistrib M (fun z : Fin n → ℝ ↦ MC (WithLp.toLp 2 z))
        μ (HDP.Chapter5.gaussianPiMeasure n) :=
    hidMaxCanonical.trans hidCanonical.symm
  have hmean :
      (∫ ω, M ω ∂μ) =
        ∫ z, MC (WithLp.toLp 2 z)
          ∂HDP.Chapter5.gaussianPiMeasure n :=
    hidRawCanonical.integral_eq
  have hidCentered :
      IdentDistrib (fun ω ↦ M ω - ∫ η, M η ∂μ)
        (HDP.Chapter5.gaussianCentered MC)
        μ (HDP.Chapter5.gaussianPiMeasure n) := by
    have h := hidRawCanonical.sub_const (∫ η, M η ∂μ)
    have heq :
        (fun z : Fin n → ℝ ↦
          MC (WithLp.toLp 2 z) - ∫ η, M η ∂μ) =
          HDP.Chapter5.gaussianCentered MC := by
      funext z
      simp only [HDP.Chapter5.gaussianCentered]
      rw [hmean]
    rw [← heq]
    exact h
  have hcanonical :=
    finiteGaussianProcess_concentration_canonical a b
  change HDP.SubGaussian (HDP.Chapter5.gaussianCentered MC)
      (HDP.Chapter5.gaussianPiMeasure n) ∧
    HDP.psi2Norm (HDP.Chapter5.gaussianCentered MC)
      (HDP.Chapter5.gaussianPiMeasure n) ≤
        2 * Real.sqrt 5 * HDP.Chapter5.gaussianMaximumScale a at hcanonical
  have hscale :
      HDP.Chapter5.gaussianMaximumScale a =
        finiteGaussianProcessStdDev X μ := by
    unfold HDP.Chapter5.gaussianMaximumScale
      finiteGaussianProcessStdDev
    simp_rw [hnorm]
  have hRawNorm :
      HDP.psi2Norm (fun ω ↦ M ω - ∫ η, M η ∂μ) μ =
        HDP.psi2Norm (HDP.Chapter5.gaussianCentered MC)
          (HDP.Chapter5.gaussianPiMeasure n) := by
    let ρ := Measure.map (HDP.Chapter5.gaussianCentered MC)
      (HDP.Chapter5.gaussianPiMeasure n)
    have hC : HasLaw (HDP.Chapter5.gaussianCentered MC) ρ
        (HDP.Chapter5.gaussianPiMeasure n) :=
      ⟨hidCentered.aemeasurable_snd, rfl⟩
    have hR : HasLaw (fun ω ↦ M ω - ∫ η, M η ∂μ) ρ μ :=
      hidCentered.symm.hasLaw hC
    rw [HDP.psi2Norm_eq_of_hasLaw hR,
      HDP.psi2Norm_eq_of_hasLaw hC]
  have hRawSub :
      HDP.SubGaussian (fun ω ↦ M ω - ∫ η, M η ∂μ) μ := by
    rcases hcanonical.1 with ⟨K, hK, hψ⟩
    refine ⟨K, hK, ?_⟩
    let ρ := Measure.map (HDP.Chapter5.gaussianCentered MC)
      (HDP.Chapter5.gaussianPiMeasure n)
    have hC : HasLaw (HDP.Chapter5.gaussianCentered MC) ρ
        (HDP.Chapter5.gaussianPiMeasure n) :=
      ⟨hidCentered.aemeasurable_snd, rfl⟩
    have hR : HasLaw (fun ω ↦ M ω - ∫ η, M η ∂μ) ρ μ :=
      hidCentered.symm.hasLaw hC
    rw [HDP.psi2MGF_eq_of_hasLaw hR]
    rw [HDP.psi2MGF_eq_of_hasLaw hC] at hψ
    exact hψ
  dsimp only
  refine ⟨hRawSub, ?_⟩
  rw [hRawNorm, ← hscale]
  exact hcanonical.2

/-- A centered finite Gaussian process vector has the multivariate Gaussian law determined by its covariance matrix.

**Lean implementation helper.** -/
lemma processEuclideanVector_law_eq_multivariateGaussian
    {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ}
    (hX : IsGaussianProcess X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    Measure.map (processEuclideanVector X) μ =
      multivariateGaussian 0
        (gaussianMeasureCovarianceMatrix
          (Measure.map (processEuclideanVector X) μ)) := by
  let ν := Measure.map (processEuclideanVector X) μ
  have hV := processEuclideanVector_hasGaussianLaw hX
  haveI : IsGaussian ν := hV.isGaussian_map
  apply gaussianMeasure_eq_multivariateGaussian_covariance ν
  rw [integral_map hV.aemeasurable (by fun_prop),
    processEuclideanVector_integral hX]
  apply WithLp.ofLp_injective
  ext i
  simp [hX0]

/-- A covariance-matrix entry of a centered Gaussian process vector is the expected product of the corresponding process coordinates.

**Lean implementation helper.** -/
lemma gaussianMeasureCovarianceMatrix_processVector_apply
    {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ}
    (hX : IsGaussianProcess X μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) (i j : I) :
    gaussianMeasureCovarianceMatrix (Measure.map (processEuclideanVector X) μ) i j =
      ∫ ω, X i ω * X j ω ∂μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hmem : ∀ k, MemLp (X k) 2 μ := fun k ↦
    (hX.hasGaussianLaw_eval k).memLp_two
  unfold processEuclideanVector
  rw [gaussianMeasureCovarianceMatrix,
    covarianceBilin_apply_basisFun hmem]
  simp [Chapter1.covariance_def', hX0 i, hX0 j]

/-- Expands the second moment of a process increment into two marginal second moments and the cross moment.

**Lean implementation helper.** -/
lemma processIncrementSecondMoment_eq
    {I Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ}
    (hX : IsGaussianProcess X μ) (i j : I) :
    processIncrementSecondMoment μ X i j =
      processSecondMoment μ X i + processSecondMoment μ X j -
        2 * ∫ ω, X i ω * X j ω ∂μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hi := (hX.hasGaussianLaw_eval i).memLp_two
  have hj := (hX.hasGaussianLaw_eval j).memLp_two
  have hi2 : Integrable (fun ω ↦ X i ω ^ 2) μ := by
    rw [show (fun ω ↦ X i ω ^ 2) = X i * X i by
      funext ω; simp [pow_two]]
    exact hi.integrable_mul hi
  have hj2 : Integrable (fun ω ↦ X j ω ^ 2) μ := by
    rw [show (fun ω ↦ X j ω ^ 2) = X j * X j by
      funext ω; simp [pow_two]]
    exact hj.integrable_mul hj
  have hij : Integrable (fun ω ↦ X i ω * X j ω) μ := hi.integrable_mul hj
  unfold processIncrementSecondMoment processSecondMoment
  rw [show (fun ω ↦ (X i ω - X j ω) ^ 2) =
      fun ω ↦ X i ω ^ 2 + X j ω ^ 2 - 2 * (X i ω * X j ω) by
    funext ω; ring]
  let f : Ω → ℝ := fun ω ↦ X i ω ^ 2
  let g : Ω → ℝ := fun ω ↦ X j ω ^ 2
  let h : Ω → ℝ := fun ω ↦ X i ω * X j ω
  change (∫ ω, (f + g) ω - (fun ω ↦ 2 * h ω) ω ∂μ) =
    (∫ ω, f ω ∂μ) + (∫ ω, g ω ∂μ) - 2 * ∫ ω, h ω ∂μ
  rw [integral_sub (by simpa [f, g] using hi2.add hj2)
      (by simpa [h] using hij.const_mul 2)]
  congr 1
  · change (∫ ω, f ω + g ω ∂μ) =
      (∫ ω, f ω ∂μ) + ∫ ω, g ω ∂μ
    exact integral_add (by simpa [f] using hi2) (by simpa [g] using hj2)
  · exact integral_const_mul (2 : ℝ) h

/-- The finite maximum of a finite Gaussian process is integrable.

**Lean implementation helper.** -/
private lemma integrable_finiteMaximum_gaussian
    {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) (hX : IsGaussianProcess X μ) :
    Integrable (HDP.Chapter5.finiteMaximum X) μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  rw [show HDP.Chapter5.finiteMaximum X =
      Finset.univ.sup' Finset.univ_nonempty X by
    funext ω
    unfold HDP.Chapter5.finiteMaximum
    exact (Finset.sup'_apply Finset.univ_nonempty X ω).symm]
  refine Finset.sup'_induction Finset.univ_nonempty
    (f := X) (p := fun f ↦ Integrable f μ) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro i _
    exact (hX.hasGaussianLaw_eval i).memLp_two.integrable (by norm_num)

/-- Relabeling a finite family by an equivalence leaves its pointwise maximum unchanged.

**Lean implementation helper.** -/
private lemma finiteMaximum_comp_equiv
    {I J Ω : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (e : I ≃ J) (X : I → Ω → ℝ) :
    HDP.Chapter5.finiteMaximum (fun j ↦ X (e.symm j)) =
      HDP.Chapter5.finiteMaximum X := by
  funext ω
  unfold HDP.Chapter5.finiteMaximum
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro j _
    exact Finset.le_sup' (fun i ↦ X i ω) (Finset.mem_univ (e.symm j))
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro i _
    simpa using Finset.le_sup' (fun j ↦ X (e.symm j) ω)
      (Finset.mem_univ (e i))

/-! ### Atom-safe lower-orthant smoothing -/

/-- Defines a smooth approximation to the indicator of a finite-maximum tail event.

**Lean implementation helper.** -/
private def orthantSmootherApprox {n : ℕ} (τ : ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let m : ℝ := k + 1
  Real.exp (-∑ i, Real.exp ((x i - τ) * m ^ 2 + m))

/-- Expresses the tail-event smoother approximation as an orthant smoother with explicit parameters.

**Lean implementation helper.** -/
private lemma orthantSmootherApprox_eq {n : ℕ} (τ : ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    orthantSmootherApprox τ k x =
      orthantSmoother (((k : ℝ) + 1) ^ 2)
        (τ - 1 / ((k : ℝ) + 1)) x := by
  have hm : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold orthantSmootherApprox orthantSmoother orthantEnergy
  dsimp only
  apply congrArg Real.exp
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Real.exp
  field_simp [hm]
  ring

/-- The approximation exponent tends to negative infinity below the threshold.

**Lean implementation helper.** -/
private lemma tendsto_orthantApprox_exponent_atBot
    {d : ℝ} (hd : d < 0) :
    Tendsto (fun k : ℕ ↦
      let m : ℝ := k + 1
      d * m ^ 2 + m) atTop atBot := by
  let m : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  have hm : Tendsto m atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun k ↦ d * m k + 1) atTop atBot :=
    tendsto_atBot_add_const_right atTop 1 (hm.const_mul_atTop_of_neg hd)
  have hp := hm.atTop_mul_atBot₀ hg
  apply hp.congr'
  filter_upwards [] with k
  dsimp [m]
  ring

/-- The approximation exponent tends to positive infinity above the threshold.

**Lean implementation helper.** -/
private lemma tendsto_orthantApprox_exponent_atTop
    {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun k : ℕ ↦
      let m : ℝ := k + 1
      d * m ^ 2 + m) atTop atTop := by
  let m : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  have hm : Tendsto m atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop (Filter.Eventually.of_forall fun k ↦ by
    dsimp [m]
    nlinarith [sq_nonneg ((k : ℝ) + 1)]) hm

/-- The orthant smoother approximations converge pointwise to the finite-maximum tail indicator.

**Lean implementation helper.** -/
private lemma tendsto_orthantSmootherApprox_pointwise
    {n : ℕ} [NeZero n] (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k ↦ orthantSmootherApprox τ k x) atTop
      (nhds (Set.indicator
        {z : EuclideanSpace ℝ (Fin n) |
          HDP.Chapter5.finiteMaximum (fun i : Fin n ↦ fun y ↦ y i) z < τ}
        (fun _ ↦ (1 : ℝ)) x)) := by
  let M := HDP.Chapter5.finiteMaximum
    (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x
  by_cases hM : M < τ
  · have hall : ∀ i : Fin n, x i < τ := by
      intro i
      unfold M HDP.Chapter5.finiteMaximum at hM
      exact (Finset.sup'_lt_iff Finset.univ_nonempty).mp hM i (Finset.mem_univ i)
    have hterm : ∀ i : Fin n,
        Tendsto (fun k : ℕ ↦
          let m : ℝ := k + 1
          Real.exp ((x i - τ) * m ^ 2 + m)) atTop (nhds 0) := by
      intro i
      exact Real.tendsto_exp_atBot.comp
        (tendsto_orthantApprox_exponent_atBot (sub_neg.mpr (hall i)))
    have hsum : Tendsto (fun k : ℕ ↦
        let m : ℝ := k + 1
        ∑ i, Real.exp ((x i - τ) * m ^ 2 + m)) atTop (nhds 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ hterm i)
    have hneg : Tendsto (fun k : ℕ ↦
        -(let m : ℝ := k + 1
          ∑ i, Real.exp ((x i - τ) * m ^ 2 + m))) atTop (nhds 0) := by
      simpa using hsum.neg
    have hout := (Real.continuous_exp.tendsto 0).comp hneg
    have hind : Set.indicator
        {z : EuclideanSpace ℝ (Fin n) |
          HDP.Chapter5.finiteMaximum (fun i : Fin n ↦ fun y ↦ y i) z < τ}
        (fun _ ↦ (1 : ℝ)) x = 1 := by
      simp [M, hM]
    rw [hind]
    unfold orthantSmootherApprox
    dsimp only
    change Tendsto (fun k : ℕ ↦
      Real.exp (-∑ i, Real.exp
        ((x i - τ) * ((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1))))
      atTop (nhds (Real.exp 0)) at hout
    simpa only [Real.exp_zero] using hout
  · have hex : ∃ i : Fin n, τ ≤ x i := by
      by_contra h
      push Not at h
      apply hM
      unfold M HDP.Chapter5.finiteMaximum
      exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ ↦ h i)
    obtain ⟨i, hi⟩ := hex
    have hcomponent : Tendsto (fun k : ℕ ↦
        let m : ℝ := k + 1
        Real.exp ((x i - τ) * m ^ 2 + m)) atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (tendsto_orthantApprox_exponent_atTop (sub_nonneg.mpr hi))
    have hsum : Tendsto (fun k : ℕ ↦
        let m : ℝ := k + 1
        ∑ j, Real.exp ((x j - τ) * m ^ 2 + m)) atTop atTop := by
      apply tendsto_atTop_mono' atTop _ hcomponent
      exact Filter.Eventually.of_forall fun k ↦ by
        dsimp only
        exact Finset.single_le_sum
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
            Real.exp_nonneg
              ((x j - τ) * ((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1)))
          (Finset.mem_univ i)
    have hout := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hsum)
    have hind : Set.indicator
        {z : EuclideanSpace ℝ (Fin n) |
          HDP.Chapter5.finiteMaximum (fun i : Fin n ↦ fun y ↦ y i) z < τ}
        (fun _ ↦ (1 : ℝ)) x = 0 := by
      simp [M, hM]
    rw [hind]
    unfold orthantSmootherApprox
    dsimp only
    change Tendsto (fun k : ℕ ↦
      Real.exp (-∑ i, Real.exp
        ((x i - τ) * ((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1))))
      atTop (nhds 0) at hout
    exact hout

/-- The maximum-coordinate functional on finite-dimensional Euclidean space is continuous.

**Lean implementation helper.** -/
private lemma continuous_euclideanFiniteMaximum {n : ℕ} [NeZero n] :
    Continuous (HDP.Chapter5.finiteMaximum
      (fun i : Fin n ↦ fun x : EuclideanSpace ℝ (Fin n) ↦ x i)) := by
  unfold HDP.Chapter5.finiteMaximum
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun _ _ ↦ by fun_prop)

/-- The Gaussian expectations of the orthant smoother approximations converge to the tail probability.

**Lean implementation helper.** -/
private lemma tendsto_integral_orthantSmootherApprox
    {n : ℕ} [NeZero n] (S : Matrix (Fin n) (Fin n) ℝ) (τ : ℝ) :
    Tendsto (fun k ↦ ∫ x, orthantSmootherApprox τ k x
      ∂multivariateGaussian 0 S) atTop
      (nhds ((multivariateGaussian 0 S).real
        {x | HDP.Chapter5.finiteMaximum
          (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x < τ})) := by
  let A := {x : EuclideanSpace ℝ (Fin n) |
    HDP.Chapter5.finiteMaximum
      (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x < τ}
  have hA : MeasurableSet A :=
    (continuous_euclideanFiniteMaximum (n := n)).measurable measurableSet_Iio
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := multivariateGaussian 0 S) (F := fun k x ↦ orthantSmootherApprox τ k x)
    (f := A.indicator fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun k ↦ (by unfold orthantSmootherApprox; fun_prop :
      Continuous (orthantSmootherApprox (n := n) τ k)).aestronglyMeasurable)
    (integrable_const_iff.2 (Or.inr inferInstance))
    (fun _ ↦ Filter.Eventually.of_forall fun x ↦ by
      unfold orthantSmootherApprox
      dsimp only
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (Finset.sum_nonneg fun _ _ ↦ Real.exp_nonneg _)))
    (Filter.Eventually.of_forall fun x ↦
      tendsto_orthantSmootherApprox_pointwise τ x)
  convert hDCT using 1
  all_goals
    simp [A, integral_indicator_const
      (μ := multivariateGaussian 0 S) (1 : ℝ) hA]

/-- The orthant smoother is twice continuously differentiable.

**Lean implementation helper.** -/
private lemma orthantSmoother_contDiff {n : ℕ} (β a : ℝ) :
    ContDiff ℝ 2 (orthantSmoother (n := n) β a) := by
  unfold orthantSmoother orthantEnergy
  fun_prop

/-- Computes every Hessian entry of the orthant smoother.

**Lean implementation helper.** -/
private lemma gaussianHessianEntry_orthantSmoother {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    gaussianHessianEntry (orthantSmoother β a) i j x =
      β ^ 2 * orthantSmoother β a x *
        (Real.exp (β * (x i - a)) * Real.exp (β * (x j - a)) -
          if i = j then Real.exp (β * (x i - a)) else 0) := by
  let e_i := EuclideanSpace.basisFun (Fin n) ℝ i
  let e_j := EuclideanSpace.basisFun (Fin n) ℝ j
  have hCD := orthantSmoother_contDiff (n := n) β a
  have hDc : DifferentiableAt ℝ (fderiv ℝ (orthantSmoother β a)) x :=
    (hCD.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hlink : gaussianHessianEntry (orthantSmoother β a) i j x =
      fderiv ℝ (fun z ↦ fderiv ℝ (orthantSmoother β a) z e_j) x e_i := by
    unfold gaussianHessianEntry
    rw [fderiv_clm_apply hDc (differentiableAt_const e_j)]
    simp [e_i, e_j]
  rw [hlink]
  have hei : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ Real.exp (β * (z j - a)))
      (Real.exp (β * (x j - a)) • (β • comparisonCoordCLM j)) x := by
    have hc : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ β * (z j - a))
        (β • comparisonCoordCLM j) x := by
      simpa [comparisonCoordCLM_apply] using
        ((comparisonCoordCLM j).hasFDerivAt.sub_const a).const_mul β
    simpa using hc.exp
  have hs := hasFDerivAt_orthantSmoother β a x
  have hg := (hei.mul hs).const_mul (-β)
  have hfun : (fun z ↦ fderiv ℝ (orthantSmoother β a) z e_j) =
      (fun z ↦ -β * Real.exp (β * (z j - a)) * orthantSmoother β a z) := by
    funext z
    exact fderiv_orthantSmoother_basis β a z j
  have hassoc :
      (fun z : EuclideanSpace ℝ (Fin n) ↦
        -β * Real.exp (β * (z j - a)) * orthantSmoother β a z) =
      (fun z ↦ -β * (Real.exp (β * (z j - a)) * orthantSmoother β a z)) := by
    funext z
    ring
  change HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦
    -β * (Real.exp (β * (z j - a)) * orthantSmoother β a z)) _ x at hg
  rw [hfun, hassoc, hg.fderiv]
  simp [e_i, comparisonCoordCLM_apply, orthantSmoother, eq_comm]
  split_ifs with hij
  · subst j
    ring
  · ring

/-- For a nonnegative argument, its square times its negative exponential is at most four.

**Lean implementation helper.** -/
private lemma sq_mul_exp_neg_le_four (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 4 := by
  let u := t / 2
  have hu : 0 ≤ u := div_nonneg ht (by norm_num)
  have hsmall : u * Real.exp (-u) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one u).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hsmall0 : 0 ≤ u * Real.exp (-u) :=
    mul_nonneg hu (Real.exp_nonneg _)
  have hsq : (u * Real.exp (-u)) ^ 2 ≤ 1 := by nlinarith
  have hexp : Real.exp (-t) = Real.exp (-u) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  rw [hexp]
  dsimp [u] at hsq ⊢
  nlinarith

/-- The orthant energy is nonnegative.

**Lean implementation helper.** -/
private lemma orthantEnergy_nonneg {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ orthantEnergy β a x := by
  unfold orthantEnergy
  exact Finset.sum_nonneg fun _ _ ↦ Real.exp_nonneg _

/-- Each exponential coordinate contribution is bounded by the total orthant energy.

**Lean implementation helper.** -/
private lemma orthant_component_le_energy {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Real.exp (β * (x i - a)) ≤ orthantEnergy β a x := by
  unfold orthantEnergy
  exact Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
      Real.exp_nonneg (β * (x j - a))) (Finset.mem_univ i)

/-- The sum of two exponential coordinate contributions is bounded by the total orthant energy.

**Lean implementation helper.** -/
private lemma orthant_two_components_le_energy {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    Real.exp (β * (x i - a)) + Real.exp (β * (x j - a)) ≤
      orthantEnergy β a x := by
  unfold orthantEnergy
  calc
    Real.exp (β * (x i - a)) + Real.exp (β * (x j - a)) =
        ∑ k ∈ ({i, j} : Finset (Fin n)), Real.exp (β * (x k - a)) := by
      simp [hij]
    _ ≤ ∑ k, Real.exp (β * (x k - a)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun _ _ _ ↦ Real.exp_nonneg _)

/-- A coordinate energy contribution times the orthant smoother is at most one.

**Lean implementation helper.** -/
private lemma orthant_component_mul_smoother_le_one {n : ℕ} (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Real.exp (β * (x i - a)) * orthantSmoother β a x ≤ 1 := by
  let y := β * (x i - a)
  have hy : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hyE : y ≤ orthantEnergy β a x :=
    hy.trans (orthant_component_le_energy β a x i)
  rw [orthantSmoother, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by dsimp [y] at hyE ⊢; linarith)

/-- The product of two coordinate contributions and the orthant smoother is at most four.

**Lean implementation helper.** -/
private lemma orthant_two_component_mul_smoother_le_four {n : ℕ}
    (β a : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    Real.exp (β * (x i - a)) * Real.exp (β * (x j - a)) *
      orthantSmoother β a x ≤ 4 := by
  by_cases hij : i = j
  · subst j
    let t := Real.exp (β * (x i - a))
    have ht : 0 ≤ t := Real.exp_nonneg _
    have htE : t ≤ orthantEnergy β a x := orthant_component_le_energy β a x i
    have he : Real.exp (-orthantEnergy β a x) ≤ Real.exp (-t) :=
      Real.exp_le_exp.mpr (neg_le_neg htE)
    calc
      Real.exp (β * (x i - a)) * Real.exp (β * (x i - a)) *
          orthantSmoother β a x = t ^ 2 * Real.exp (-orthantEnergy β a x) := by
        simp [t, orthantSmoother, pow_two]
      _ ≤ t ^ 2 * Real.exp (-t) := mul_le_mul_of_nonneg_left he (sq_nonneg t)
      _ ≤ 4 := sq_mul_exp_neg_le_four t ht
  · let ti := Real.exp (β * (x i - a))
    let tj := Real.exp (β * (x j - a))
    let s := ti + tj
    have hti : 0 ≤ ti := Real.exp_nonneg _
    have htj : 0 ≤ tj := Real.exp_nonneg _
    have hs : 0 ≤ s := add_nonneg hti htj
    have hsE : s ≤ orthantEnergy β a x := by
      simpa [s, ti, tj] using orthant_two_components_le_energy β a x hij
    have he : Real.exp (-orthantEnergy β a x) ≤ Real.exp (-s) :=
      Real.exp_le_exp.mpr (neg_le_neg hsE)
    calc
      Real.exp (β * (x i - a)) * Real.exp (β * (x j - a)) *
          orthantSmoother β a x = ti * tj * Real.exp (-orthantEnergy β a x) := by
        simp [ti, tj, orthantSmoother]
      _ ≤ s ^ 2 * Real.exp (-orthantEnergy β a x) := by
        gcongr
        nlinarith [sq_nonneg (ti - tj)]
      _ ≤ s ^ 2 * Real.exp (-s) := mul_le_mul_of_nonneg_left he (sq_nonneg s)
      _ ≤ 4 := sq_mul_exp_neg_le_four s hs

/-- The orthant smoother is uniformly bounded in absolute value.

**Lean implementation helper.** -/
private lemma orthantSmoother_value_bound {n : ℕ} (β a : ℝ) :
    ∃ C, ∀ x : EuclideanSpace ℝ (Fin n), ‖orthantSmoother β a x‖ ≤ C := by
  refine ⟨1, fun x ↦ ?_⟩
  rw [Real.norm_eq_abs, orthantSmoother, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (orthantEnergy_nonneg β a x))

/-- Every coordinate derivative of the orthant smoother admits a uniform bound.

**Lean implementation helper.** -/
private lemma orthantSmoother_coordinate_derivative_bound {n : ℕ} (β a : ℝ) :
    ∀ i, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (orthantSmoother β a) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ C := by
  intro i
  refine ⟨|β|, fun x ↦ ?_⟩
  rw [fderiv_orthantSmoother_basis, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_neg, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg (show 0 ≤ orthantSmoother β a x by
      unfold orthantSmoother; exact Real.exp_nonneg _)]
  rw [mul_assoc]
  calc
    |β| * (Real.exp (β * (x i - a)) * orthantSmoother β a x) ≤
        |β| * 1 := mul_le_mul_of_nonneg_left
      (orthant_component_mul_smoother_le_one β a x i) (abs_nonneg β)
    _ = |β| := mul_one _

/-- Every Hessian entry of the orthant smoother admits a uniform bound.

**Lean implementation helper.** -/
private lemma orthantSmoother_hessian_bound {n : ℕ} (β a : ℝ) :
    ∀ i j, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖gaussianHessianEntry (orthantSmoother β a) i j x‖ ≤ C := by
  intro i j
  refine ⟨5 * β ^ 2, fun x ↦ ?_⟩
  rw [gaussianHessianEntry_orthantSmoother, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (sq_nonneg β),
    abs_of_nonneg (show 0 ≤ orthantSmoother β a x by
      unfold orthantSmoother; exact Real.exp_nonneg _)]
  have hf0 : 0 ≤ orthantSmoother β a x := Real.exp_nonneg _
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    rw [← pow_two (Real.exp (β * (x i - a)))]
    calc
      β ^ 2 * orthantSmoother β a x *
          |Real.exp (β * (x i - a)) ^ 2 - Real.exp (β * (x i - a))| ≤
          β ^ 2 * (4 + 1) := by
        rw [show β ^ 2 * orthantSmoother β a x *
            |Real.exp (β * (x i - a)) ^ 2 - Real.exp (β * (x i - a))| =
            β ^ 2 * (orthantSmoother β a x *
              |Real.exp (β * (x i - a)) ^ 2 - Real.exp (β * (x i - a))|) by ring]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
        calc
          orthantSmoother β a x *
              |Real.exp (β * (x i - a)) ^ 2 - Real.exp (β * (x i - a))| ≤
              orthantSmoother β a x *
                (Real.exp (β * (x i - a)) ^ 2 + Real.exp (β * (x i - a))) := by
            apply mul_le_mul_of_nonneg_left _ hf0
            apply abs_le.mpr
            constructor <;>
              nlinarith [sq_nonneg (Real.exp (β * (x i - a))),
                Real.exp_nonneg (β * (x i - a))]
          _ = (Real.exp (β * (x i - a)) * Real.exp (β * (x i - a)) *
                orthantSmoother β a x) +
              (Real.exp (β * (x i - a)) * orthantSmoother β a x) := by ring
          _ ≤ 4 + 1 := add_le_add
            (orthant_two_component_mul_smoother_le_four β a x i i)
            (orthant_component_mul_smoother_le_one β a x i)
      _ = 5 * β ^ 2 := by ring
  · simp only [if_neg hij, sub_zero, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      β ^ 2 * orthantSmoother β a x *
          (Real.exp (β * (x i - a)) * Real.exp (β * (x j - a))) =
          β ^ 2 * (Real.exp (β * (x i - a)) *
            Real.exp (β * (x j - a)) * orthantSmoother β a x) := by ring
      _ ≤ β ^ 2 * 4 := mul_le_mul_of_nonneg_left
        (orthant_two_component_mul_smoother_le_four β a x i j) (sq_nonneg β)
      _ ≤ 5 * β ^ 2 := by nlinarith [sq_nonneg β]

/-- Orders the expected orthant smoothers under two Gaussian covariance matrices with matching diagonals and ordered off-diagonal entries.

**Lean implementation helper.** -/
private lemma orthantSmoother_expectation_comparison
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hdiag : ∀ i, SX i i = SY i i)
    (hoff : ∀ i j, i ≠ j → SY i j ≤ SX i j)
    (β a : ℝ) :
    (∫ x, orthantSmoother β a x ∂multivariateGaussian 0 SY) ≤
      ∫ x, orthantSmoother β a x ∂multivariateGaussian 0 SX := by
  apply gaussianInterpolationExpectation_le_of_hessianSum_nonneg_coordinate
    SX SY hSX hSY (orthantSmoother β a)
      (orthantSmoother_contDiff β a)
      (orthantSmoother_value_bound β a)
      (orthantSmoother_coordinate_derivative_bound β a)
      (orthantSmoother_hessian_bound β a)
  intro _ _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : i = j
  · subst j
    simp [hdiag i]
  · have hcoeff : 0 ≤ SX i j - SY i j := sub_nonneg.mpr (hoff i j hij)
    apply mul_nonneg hcoeff
    apply integral_nonneg_of_ae
    filter_upwards [] with p
    rw [gaussianHessianEntry_orthantSmoother, if_neg hij, sub_zero]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg β) (show 0 ≤ orthantSmoother β a _ by
        unfold orthantSmoother; exact Real.exp_nonneg _))
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))

/-- Transfers the covariance comparison inequality to the finite-parameter orthant smoother approximation.

**Lean implementation helper.** -/
private lemma orthantSmootherApprox_expectation_comparison
    {n : ℕ} (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hdiag : ∀ i, SX i i = SY i i)
    (hoff : ∀ i j, i ≠ j → SY i j ≤ SX i j)
    (τ : ℝ) (k : ℕ) :
    (∫ x, orthantSmootherApprox τ k x ∂multivariateGaussian 0 SY) ≤
      ∫ x, orthantSmootherApprox τ k x ∂multivariateGaussian 0 SX := by
  simp_rw [orthantSmootherApprox_eq]
  exact orthantSmoother_expectation_comparison SX SY hSX hSY hdiag hoff _ _

/-- Compares upper-tail probabilities of Gaussian coordinate maxima under the covariance ordering.

**Lean implementation helper.** -/
private lemma multivariateGaussian_finiteMaximum_tail_comparison
    {n : ℕ} [NeZero n]
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hdiag : ∀ i, SX i i = SY i i)
    (hoff : ∀ i j, i ≠ j → SY i j ≤ SX i j) :
    ∀ τ : ℝ,
      (multivariateGaussian 0 SX).real
          {x | τ ≤ HDP.Chapter5.finiteMaximum
            (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x} ≤
        (multivariateGaussian 0 SY).real
          {x | τ ≤ HDP.Chapter5.finiteMaximum
            (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x} := by
  intro τ
  let M : EuclideanSpace ℝ (Fin n) → ℝ :=
    HDP.Chapter5.finiteMaximum
      (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i)
  let A : Set (EuclideanSpace ℝ (Fin n)) := {x | M x < τ}
  have hA : MeasurableSet A :=
    (continuous_euclideanFiniteMaximum (n := n)).measurable measurableSet_Iio
  have hlimY := tendsto_integral_orthantSmootherApprox SY τ
  have hlimX := tendsto_integral_orthantSmootherApprox SX τ
  have hLower : (multivariateGaussian 0 SY).real A ≤
      (multivariateGaussian 0 SX).real A := by
    exact le_of_tendsto_of_tendsto' hlimY hlimX fun k ↦
      orthantSmootherApprox_expectation_comparison SX SY hSX hSY hdiag hoff τ k
  have htail : {x : EuclideanSpace ℝ (Fin n) | τ ≤ M x} = Aᶜ := by
    ext x
    simp [A]
  rw [show {x : EuclideanSpace ℝ (Fin n) | τ ≤
        HDP.Chapter5.finiteMaximum
          (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x} = Aᶜ
      by simpa [M] using htail,
    measureReal_compl hA, measureReal_compl hA, probReal_univ, probReal_univ]
  linarith

/-- Slepian: equal variances plus dominated increments imply stochastic and expected-max domination. The threshold is every real number, as in the process statement 7.2.2; the
spurious `τ ≥ 0` restriction in the later vector restatement is not retained.
The proof transports the processes to their finite-dimensional Gaussian laws,
uses an atom-safe smooth approximation of strict lower orthants, and integrates
the resulting tail comparison.

**Book Theorem 7.2.2.** -/
theorem slepianInequality
    {I ΩX ΩY : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (μX : Measure ΩX) (μY : Measure ΩY)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (X : I → ΩX → ℝ) (Y : I → ΩY → ℝ)
    (hX : IsGaussianProcess X μX) (hY : IsGaussianProcess Y μY)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μX = 0)
    (hY0 : ∀ i, ∫ ω, Y i ω ∂μY = 0)
    (hvar : ∀ i, processSecondMoment μX X i =
      processSecondMoment μY Y i)
    (hinc : ∀ i j, processIncrementSecondMoment μX X i j ≤
      processIncrementSecondMoment μY Y i j) :
    (∀ τ : ℝ,
      μX.real {ω | τ ≤ HDP.Chapter5.finiteMaximum X ω} ≤
        μY.real {ω | τ ≤ HDP.Chapter5.finiteMaximum Y ω}) ∧
      expectedFiniteSupremum μX X ≤ expectedFiniteSupremum μY Y := by
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  have hn : 0 < n := Fintype.card_pos
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let XF : Fin n → ΩX → ℝ := fun i ↦ X (e.symm i)
  let YF : Fin n → ΩY → ℝ := fun i ↦ Y (e.symm i)
  have hXF : IsGaussianProcess XF μX := hX.comp_right e.symm
  have hYF : IsGaussianProcess YF μY := hY.comp_right e.symm
  have hXF0 : ∀ i, ∫ ω, XF i ω ∂μX = 0 := fun i ↦ by
    simpa [XF] using hX0 (e.symm i)
  have hYF0 : ∀ i, ∫ ω, YF i ω ∂μY = 0 := fun i ↦ by
    simpa [YF] using hY0 (e.symm i)
  let VX := processEuclideanVector XF
  let VY := processEuclideanVector YF
  let νX := Measure.map VX μX
  let νY := Measure.map VY μY
  let SX := gaussianMeasureCovarianceMatrix νX
  let SY := gaussianMeasureCovarianceMatrix νY
  have hSX : SX.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νX
  have hSY : SY.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νY
  have hLawX : νX = multivariateGaussian 0 SX := by
    simpa [νX, VX, SX] using
      processEuclideanVector_law_eq_multivariateGaussian hXF hXF0
  have hLawY : νY = multivariateGaussian 0 SY := by
    simpa [νY, VY, SY] using
      processEuclideanVector_law_eq_multivariateGaussian hYF hYF0
  have hdiag : ∀ i, SX i i = SY i i := by
    intro i
    rw [show SX i i = ∫ ω, XF i ω * XF i ω ∂μX by
      simpa [SX, νX, VX] using
        gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 i i,
      show SY i i = ∫ ω, YF i ω * YF i ω ∂μY by
      simpa [SY, νY, VY] using
        gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 i i]
    simpa [processSecondMoment, XF, YF, pow_two] using hvar (e.symm i)
  have hoff : ∀ i j, i ≠ j → SY i j ≤ SX i j := by
    intro i j _
    have hv_i : processSecondMoment μX XF i =
        processSecondMoment μY YF i := by
      change (∫ ω, X (e.symm i) ω ^ 2 ∂μX) =
        ∫ ω, Y (e.symm i) ω ^ 2 ∂μY
      simpa [processSecondMoment] using hvar (e.symm i)
    have hv_j : processSecondMoment μX XF j =
        processSecondMoment μY YF j := by
      change (∫ ω, X (e.symm j) ω ^ 2 ∂μX) =
        ∫ ω, Y (e.symm j) ω ^ 2 ∂μY
      simpa [processSecondMoment] using hvar (e.symm j)
    have hincF : processIncrementSecondMoment μX XF i j ≤
        processIncrementSecondMoment μY YF i j := by
      change (∫ ω, (X (e.symm i) ω - X (e.symm j) ω) ^ 2 ∂μX) ≤
        ∫ ω, (Y (e.symm i) ω - Y (e.symm j) ω) ^ 2 ∂μY
      simpa [processIncrementSecondMoment] using hinc (e.symm i) (e.symm j)
    rw [processIncrementSecondMoment_eq hXF,
      processIncrementSecondMoment_eq hYF, hv_i, hv_j] at hincF
    rw [show SY i j = ∫ ω, YF i ω * YF j ω ∂μY by
      simpa [SY, νY, VY] using
        gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 i j,
      show SX i j = ∫ ω, XF i ω * XF j ω ∂μX by
      simpa [SX, νX, VX] using
        gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 i j]
    linarith
  have hmatrix := multivariateGaussian_finiteMaximum_tail_comparison
    SX SY hSX hSY hdiag hoff
  have htail : ∀ τ : ℝ,
      μX.real {ω | τ ≤ HDP.Chapter5.finiteMaximum X ω} ≤
        μY.real {ω | τ ≤ HDP.Chapter5.finiteMaximum Y ω} := by
    intro τ
    let M : EuclideanSpace ℝ (Fin n) → ℝ :=
      HDP.Chapter5.finiteMaximum
        (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i)
    let A : Set (EuclideanSpace ℝ (Fin n)) := {x | τ ≤ M x}
    have hA : MeasurableSet A :=
      (continuous_euclideanFiniteMaximum (n := n)).measurable measurableSet_Ici
    have hVX : AEMeasurable VX μX := by
      simpa [VX] using (processEuclideanVector_hasGaussianLaw hXF).aemeasurable
    have hVY : AEMeasurable VY μY := by
      simpa [VY] using (processEuclideanVector_hasGaussianLaw hYF).aemeasurable
    have hpreX : VX ⁻¹' A =
        {ω | τ ≤ HDP.Chapter5.finiteMaximum X ω} := by
      ext ω
      change τ ≤ HDP.Chapter5.finiteMaximum
        (fun i : Fin n ↦ fun ω ↦ X (e.symm i) ω) ω ↔
          τ ≤ HDP.Chapter5.finiteMaximum X ω
      rw [finiteMaximum_comp_equiv e X]
    have hpreY : VY ⁻¹' A =
        {ω | τ ≤ HDP.Chapter5.finiteMaximum Y ω} := by
      ext ω
      change τ ≤ HDP.Chapter5.finiteMaximum
        (fun i : Fin n ↦ fun ω ↦ Y (e.symm i) ω) ω ↔
          τ ≤ HDP.Chapter5.finiteMaximum Y ω
      rw [finiteMaximum_comp_equiv e Y]
    have hmapX : μX.real {ω | τ ≤ HDP.Chapter5.finiteMaximum X ω} =
        νX.real A := by
      change ENNReal.toReal (μX {ω | τ ≤ HDP.Chapter5.finiteMaximum X ω}) =
        ENNReal.toReal ((Measure.map VX μX) A)
      rw [Measure.map_apply_of_aemeasurable hVX hA, hpreX]
    have hmapY : μY.real {ω | τ ≤ HDP.Chapter5.finiteMaximum Y ω} =
        νY.real A := by
      change ENNReal.toReal (μY {ω | τ ≤ HDP.Chapter5.finiteMaximum Y ω}) =
        ENNReal.toReal ((Measure.map VY μY) A)
      rw [Measure.map_apply_of_aemeasurable hVY hA, hpreY]
    rw [hmapX, hmapY, hLawX, hLawY]
    simpa [A, M] using hmatrix τ
  refine ⟨htail, ?_⟩
  unfold expectedFiniteSupremum
  exact HDP.integral_le_integral_of_forall_measureReal_ge
    (integrable_finiteMaximum_gaussian μX X hX)
    (integrable_finiteMaximum_gaussian μY Y hY) htail

/-- Defines coordinate evaluation as a continuous linear functional for the smooth-maximum argument.

**Lean implementation helper.** -/
private def sfCoordCLM {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The smooth-maximum coordinate functional evaluates the selected Euclidean coordinate.

**Lean implementation helper.** -/
private lemma sfCoordCLM_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : sfCoordCLM i x = x i := by
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x i

/-- Defines the exponential normalizing denominator for the soft maximum.

**Lean implementation helper.** -/
private def softMaxDenominator {n : ℕ} (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, Real.exp (β * x i)

/-- Defines the normalized exponential weight of one coordinate.

**Lean implementation helper.** -/
private def softMaxWeight {n : ℕ} (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : ℝ :=
  Real.exp (β * x i - Real.log (softMaxDenominator β x))

/-- Defines the log-sum-exp smooth approximation to the maximum coordinate.

**Lean implementation helper.** -/
private def smoothMaximum {n : ℕ} (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / β) * Real.log (softMaxDenominator β x)

/-- The soft max denominator is strictly positive.

**Lean implementation helper.** -/
private lemma softMaxDenominator_pos {n : ℕ} [NeZero n]
    (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 < softMaxDenominator β x := by
  let i : Fin n := ⟨0, NeZero.one_le⟩
  calc
    0 < Real.exp (β * x i) := Real.exp_pos _
    _ ≤ softMaxDenominator β x := by
      unfold softMaxDenominator
      exact Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
          Real.exp_nonneg (β * x j)) (Finset.mem_univ i)

/-- The soft max weight is nonnegative.

**Lean implementation helper.** -/
private lemma softMaxWeight_nonneg {n : ℕ} [NeZero n]
    (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 ≤ softMaxWeight β x i := by
  exact Real.exp_nonneg _

/-- The soft-max coordinate weights sum to one.

**Lean implementation helper.** -/
private lemma sum_softMaxWeight {n : ℕ} [NeZero n]
    (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, softMaxWeight β x i = 1 := by
  have hD := softMaxDenominator_pos β x
  simp_rw [softMaxWeight, Real.exp_sub, Real.exp_log hD]
  rw [← Finset.sum_div]
  exact div_self hD.ne'

/-- The soft max weight is at most one.

**Lean implementation helper.** -/
private lemma softMaxWeight_le_one {n : ℕ} [NeZero n]
    (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    softMaxWeight β x i ≤ 1 := by
  rw [← sum_softMaxWeight β x]
  exact Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
      softMaxWeight_nonneg β x j) (Finset.mem_univ i)

/-- Computes the Fréchet derivative of the soft max denominator at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_softMaxDenominator {n : ℕ}
    (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (softMaxDenominator β)
      (∑ i, Real.exp (β * x i) • (β • sfCoordCLM i)) x := by
  have hcomp : ∀ i : Fin n, HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ Real.exp (β * z i))
      (Real.exp (β * x i) • (β • sfCoordCLM i)) x := by
    intro i
    have hc : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ β * z i)
        (β • sfCoordCLM i) x := by
      simpa [sfCoordCLM_apply] using (sfCoordCLM i).hasFDerivAt.const_mul β
    simpa using hc.exp
  unfold softMaxDenominator
  exact HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ ↦ hcomp i)

/-- The log-sum-exp smooth maximum is twice continuously differentiable.

**Lean implementation helper.** -/
private lemma smoothMaximum_contDiff {n : ℕ} [NeZero n]
    (β : ℝ) : ContDiff ℝ 2 (smoothMaximum (n := n) β) := by
  unfold smoothMaximum
  apply contDiff_const.mul
  exact (by unfold softMaxDenominator; fun_prop :
    ContDiff ℝ 2 (softMaxDenominator (n := n) β)).log
      (fun x ↦ (softMaxDenominator_pos β x).ne')

/-- The derivative of the smooth maximum along a coordinate basis vector is the corresponding soft-max weight.

**Lean implementation helper.** -/
private lemma fderiv_smoothMaximum_basis {n : ℕ} [NeZero n]
    (β : ℝ) (hβ : β ≠ 0) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderiv ℝ (smoothMaximum β) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      softMaxWeight β x i := by
  have hd := (hasFDerivAt_softMaxDenominator β x).log
    (softMaxDenominator_pos β x).ne'
  have hs := hd.const_mul (1 / β)
  have hs' : HasFDerivAt (fun y ↦
      (1 / β) * Real.log (softMaxDenominator β y))
      ((1 / β) • ((softMaxDenominator β x)⁻¹ •
        ∑ j, Real.exp (β * x j) • (β • sfCoordCLM j))) x := by
    simpa only [one_div] using hs
  change fderiv ℝ (fun y ↦
      (1 / β) * Real.log (softMaxDenominator β y)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) = _
  rw [hs'.fderiv]
  have hD := softMaxDenominator_pos β x
  simp_rw [softMaxWeight, Real.exp_sub, Real.exp_log hD]
  simp only [_root_.smul_apply, _root_.sum_apply, sfCoordCLM_apply,
    smul_eq_mul]
  have hsum :
      (∑ k : Fin n,
        Real.exp (β * x k) *
          (β * (EuclideanSpace.basisFun (Fin n) ℝ i) k)) =
        β * Real.exp (β * x i) := by
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, mul_comm]
  rw [hsum]
  field_simp [hβ, hD.ne']

/-- Computes the coordinate derivative of a soft-max weight.

**Lean implementation helper.** -/
private lemma fderiv_softMaxWeight_basis {n : ℕ} [NeZero n]
    (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    fderiv ℝ (fun z ↦ softMaxWeight β z j) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      β * softMaxWeight β x j *
        ((if i = j then (1 : ℝ) else 0) - softMaxWeight β x i) := by
  let D := softMaxDenominator β x
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ∑ k, Real.exp (β * x k) • (β • sfCoordCLM k)
  have hD : 0 < D := softMaxDenominator_pos β x
  have hcoord : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ β * z j)
      (β • sfCoordCLM j) x := by
    simpa [sfCoordCLM_apply] using (sfCoordCLM j).hasFDerivAt.const_mul β
  have hexponent : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦
        β * z j - Real.log (softMaxDenominator β z))
      ((β • sfCoordCLM j) - D⁻¹ • L) x := by
    exact hcoord.sub
      ((hasFDerivAt_softMaxDenominator β x).log hD.ne')
  rw [show (fun z ↦ softMaxWeight β z j) =
      (fun z ↦ Real.exp
        (β * z j - Real.log (softMaxDenominator β z))) by rfl,
    hexponent.exp.fderiv]
  dsimp only [D, L] at hD ⊢
  simp only [_root_.sub_apply, _root_.smul_apply, _root_.sum_apply,
    sfCoordCLM_apply, smul_eq_mul]
  have hsingle :
      (EuclideanSpace.basisFun (Fin n) ℝ i) j =
        if i = j then (1 : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      simp [EuclideanSpace.basisFun_apply]
    · have hji : j ≠ i := Ne.symm hij
      simp [EuclideanSpace.basisFun_apply, hij, hji]
  have hsum :
      (∑ k : Fin n,
        Real.exp (β * x k) *
          (β * (EuclideanSpace.basisFun (Fin n) ℝ i) k)) =
        β * Real.exp (β * x i) := by
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, mul_comm]
  rw [hsingle, hsum]
  simp_rw [softMaxWeight, Real.exp_sub, Real.exp_log hD]
  field_simp [hD.ne']

/-- Computes each Hessian entry of the smooth maximum from the soft-max weights.

**Lean implementation helper.** -/
private lemma gaussianHessianEntry_smoothMaximum {n : ℕ} [NeZero n]
    (β : ℝ) (hβ : β ≠ 0) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    gaussianHessianEntry (smoothMaximum β) i j x =
      β * softMaxWeight β x j *
        ((if i = j then (1 : ℝ) else 0) - softMaxWeight β x i) := by
  let e_i := EuclideanSpace.basisFun (Fin n) ℝ i
  let e_j := EuclideanSpace.basisFun (Fin n) ℝ j
  have hCD := smoothMaximum_contDiff (n := n) β
  have hDc : DifferentiableAt ℝ (fderiv ℝ (smoothMaximum β)) x :=
    (hCD.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hlink : gaussianHessianEntry (smoothMaximum β) i j x =
      fderiv ℝ (fun z ↦ fderiv ℝ (smoothMaximum β) z e_j) x e_i := by
    unfold gaussianHessianEntry
    rw [fderiv_clm_apply hDc (differentiableAt_const e_j)]
    simp [e_i, e_j]
  rw [hlink]
  have hfun : (fun z ↦ fderiv ℝ (smoothMaximum β) z e_j) =
      fun z ↦ softMaxWeight β z j := by
    funext z
    exact fderiv_smoothMaximum_basis β hβ z j
  rw [hfun]
  exact fderiv_softMaxWeight_basis β x i j

/-- Every coordinate derivative of the smooth maximum has a uniform bound.

**Lean implementation helper.** -/
private lemma smoothMaximum_coordinateDerivative_bound {n : ℕ} [NeZero n]
    {β : ℝ} (hβ : β ≠ 0) :
    ∀ i, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (smoothMaximum β) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ C := by
  intro i
  refine ⟨1, fun x ↦ ?_⟩
  rw [fderiv_smoothMaximum_basis β hβ, Real.norm_eq_abs,
    abs_of_nonneg (softMaxWeight_nonneg β x i)]
  exact softMaxWeight_le_one β x i

/-- Every Hessian entry of the smooth maximum has a uniform bound when the temperature is positive.

**Lean implementation helper.** -/
private lemma smoothMaximum_hessian_bound {n : ℕ} [NeZero n]
    {β : ℝ} (hβ : 0 < β) :
    ∀ i j, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖gaussianHessianEntry (smoothMaximum β) i j x‖ ≤ C := by
  intro i j
  refine ⟨β, fun x ↦ ?_⟩
  rw [gaussianHessianEntry_smoothMaximum β hβ.ne', Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos hβ]
  have hpj0 := softMaxWeight_nonneg β x j
  have hpj1 := softMaxWeight_le_one β x j
  have hpi0 := softMaxWeight_nonneg β x i
  have hpi1 := softMaxWeight_le_one β x i
  rw [abs_of_nonneg hpj0]
  by_cases hij : i = j
  · subst j
    simp only [if_pos, abs_of_nonneg (sub_nonneg.mpr hpi1)]
    have hp : softMaxWeight β x i * (1 - softMaxWeight β x i) ≤ 1 := by
      calc
        softMaxWeight β x i * (1 - softMaxWeight β x i) ≤
            1 * (1 - softMaxWeight β x i) :=
          mul_le_mul_of_nonneg_right hpi1 (sub_nonneg.mpr hpi1)
        _ ≤ 1 := by linarith
    calc
      β * softMaxWeight β x i * (1 - softMaxWeight β x i) =
          β * (softMaxWeight β x i * (1 - softMaxWeight β x i)) := by ring
      _ ≤ β * 1 := mul_le_mul_of_nonneg_left hp hβ.le
      _ = β := mul_one _
  · simp only [if_neg hij, zero_sub, abs_neg,
      abs_of_nonneg hpi0]
    have hp : softMaxWeight β x j * softMaxWeight β x i ≤ 1 := by
      calc
        softMaxWeight β x j * softMaxWeight β x i ≤
            1 * softMaxWeight β x i :=
          mul_le_mul_of_nonneg_right hpj1 hpi0
        _ ≤ 1 := by simpa using hpi1
    calc
      β * softMaxWeight β x j * softMaxWeight β x i =
          β * (softMaxWeight β x j * softMaxWeight β x i) := by ring
      _ ≤ β * 1 := mul_le_mul_of_nonneg_left hp hβ.le
      _ = β := mul_one _

/-- Rewrites contraction against a zero-row-sum symmetric kernel in terms of covariance increments.

**Lean implementation helper.** -/
private lemma covariance_contraction_eq_increment_contraction
    {I : Type*} [Fintype I]
    (C H : I → I → ℝ)
    (hHsymm : ∀ i j, H i j = H j i)
    (hHrow : ∀ i, ∑ j, H i j = 0) :
    (∑ i, ∑ j, C i j * H i j) =
      -(1 / 2 : ℝ) * ∑ i, ∑ j,
        (C i i + C j j - 2 * C i j) * H i j := by
  have hdiagLeft : (∑ i, ∑ j, C i i * H i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.mul_sum, hHrow, mul_zero]
  have hcol : ∀ j, ∑ i, H i j = 0 := by
    intro j
    calc
      (∑ i, H i j) = ∑ i, H j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hHsymm i j
      _ = 0 := hHrow j
  have hdiagRight : (∑ i, ∑ j, C j j * H i j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.mul_sum, hcol j, mul_zero]
  have hexpand :
      (∑ i, ∑ j, (C i i + C j j - 2 * C i j) * H i j) =
        (∑ i, ∑ j, C i i * H i j) +
        (∑ i, ∑ j, C j j * H i j) -
        2 * (∑ i, ∑ j, C i j * H i j) := by
    calc
      (∑ i, ∑ j, (C i i + C j j - 2 * C i j) * H i j) =
          Finset.univ.sum (fun i : I ↦ Finset.univ.sum (fun j : I ↦
            (C i i * H i j + C j j * H i j) - 2 * (C i j * H i j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
  rw [hexpand, hdiagLeft, hdiagRight]
  ring

/-- Defines the squared-increment quantity determined by two entries and two diagonal entries of a covariance matrix.

**Lean implementation helper.** -/
private def matrixIncrement {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  S i i + S j j - 2 * S i j

/-- Orders expected smooth maxima when one covariance matrix has smaller pairwise increments.

**Lean implementation helper.** -/
private lemma smoothMaximum_expectation_comparison
    {n : ℕ} [NeZero n]
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hinc : ∀ i j, matrixIncrement SX i j ≤ matrixIncrement SY i j)
    {β : ℝ} (hβ : 0 < β) :
    (∫ x, smoothMaximum β x ∂multivariateGaussian 0 SX) ≤
      ∫ x, smoothMaximum β x ∂multivariateGaussian 0 SY := by
  apply gaussianInterpolationExpectation_le_of_hessianSum_nonneg_boundedDerivative_coordinate
    SY SX hSY hSX (smoothMaximum β)
      (smoothMaximum_contDiff β)
      (smoothMaximum_coordinateDerivative_bound hβ.ne')
      (smoothMaximum_hessian_bound hβ)
  intro u hu
  let ν := (multivariateGaussian 0 SY).prod (multivariateGaussian 0 SX)
  let z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) := gaussianInterpolationPoint u
  let C : Fin n → Fin n → ℝ := fun i j ↦ SY i j - SX i j
  let K : Fin n → Fin n → ℝ := fun i j ↦
    ∫ p, gaussianHessianEntry (smoothMaximum β) i j (z p) ∂ν
  have hzcont : Continuous z := by
    dsimp [z]
    unfold gaussianInterpolationPoint
    fun_prop
  have hCD := smoothMaximum_contDiff (n := n) β
  have hHcont : ∀ i j : Fin n, Continuous
      (gaussianHessianEntry (smoothMaximum β) i j) := by
    intro i j
    exact (((hCD.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hHint : ∀ i j : Fin n, Integrable
      (fun p ↦ gaussianHessianEntry (smoothMaximum β) i j (z p)) ν := by
    intro i j
    obtain ⟨D, hD⟩ := smoothMaximum_hessian_bound hβ i j
    apply Integrable.of_bound ((hHcont i j).comp hzcont).aestronglyMeasurable D
    filter_upwards [] with p
    exact hD _
  have hKsymm : ∀ i j, K i j = K j i := by
    intro i j
    unfold K
    apply integral_congr_ae
    filter_upwards [] with p
    rw [gaussianHessianEntry_smoothMaximum β hβ.ne',
      gaussianHessianEntry_smoothMaximum β hβ.ne']
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij]
      ring
  have hKrow : ∀ i, ∑ j, K i j = 0 := by
    intro i
    unfold K
    rw [← integral_finsetSum]
    · apply integral_eq_zero_of_ae
      filter_upwards [] with p
      change (∑ j, gaussianHessianEntry (smoothMaximum β) i j (z p)) =
        (0 : ℝ)
      simp_rw [gaussianHessianEntry_smoothMaximum β hβ.ne']
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ j, softMaxWeight β (z p) j *
          (if i = j then (1 : ℝ) else 0)) = softMaxWeight β (z p) i by
        simp]
      rw [← Finset.sum_mul, sum_softMaxWeight]
      ring
    · intro j _
      exact hHint i j
  have hKoff : ∀ i j, i ≠ j → K i j ≤ 0 := by
    intro i j hij
    unfold K
    apply integral_nonpos_of_ae
    filter_upwards [] with p
    rw [gaussianHessianEntry_smoothMaximum β hβ.ne', if_neg hij,
      zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hβ.le (softMaxWeight_nonneg β (z p) j))
      (neg_nonpos.mpr (softMaxWeight_nonneg β (z p) i))
  change 0 ≤ ∑ i, ∑ j, C i j * K i j
  rw [covariance_contraction_eq_increment_contraction C K hKsymm hKrow]
  have hterm : ∀ i j,
      (C i i + C j j - 2 * C i j) * K i j ≤ 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      dsimp [C]
      ring_nf
      simp
    · apply mul_nonpos_of_nonneg_of_nonpos
      · have h := hinc i j
        dsimp [C, matrixIncrement] at h ⊢
        linarith
      · exact hKoff i j hij
  have hsum : (∑ i, ∑ j,
      (C i i + C j j - 2 * C i j) * K i j) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ Finset.sum_nonpos fun j _ ↦ hterm i j
  exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) hsum

/-- Defines the maximum coordinate of a finite-dimensional Euclidean vector.

**Lean implementation helper.** -/
private def euclideanFiniteMaximumSF {n : ℕ} [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  HDP.Chapter5.finiteMaximum
    (fun i : Fin n ↦ fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x

/-- The maximum-coordinate functional on finite-dimensional Euclidean space is continuous.

**Lean implementation helper.** -/
private lemma continuous_euclideanFiniteMaximumSF {n : ℕ} [NeZero n] :
    Continuous (euclideanFiniteMaximumSF (n := n)) := by
  unfold euclideanFiniteMaximumSF HDP.Chapter5.finiteMaximum
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun _ _ ↦ by fun_prop)

/-- The log-sum-exp smooth maximum lies between the true maximum and the maximum plus the logarithmic approximation error.

**Lean implementation helper.** -/
private lemma smoothMaximum_bounds {n : ℕ} [NeZero n]
    {β : ℝ} (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanFiniteMaximumSF x ≤ smoothMaximum β x ∧
      smoothMaximum β x ≤ euclideanFiniteMaximumSF x +
        Real.log n / β := by
  let M := euclideanFiniteMaximumSF x
  let D := softMaxDenominator β x
  have hD : 0 < D := softMaxDenominator_pos β x
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hcoord : ∀ i : Fin n, x i ≤ M := by
    intro i
    unfold M euclideanFiniteMaximumSF HDP.Chapter5.finiteMaximum
    exact Finset.le_sup' (fun j ↦ x j) (Finset.mem_univ i)
  have hLowerExp : Real.exp (β * M) ≤ D := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
      (fun j ↦ x j)
    have hi' : M = x i := by
      simpa [M, euclideanFiniteMaximumSF, HDP.Chapter5.finiteMaximum] using hi
    rw [hi']
    unfold D softMaxDenominator
    exact Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
        Real.exp_nonneg (β * x j))
      (Finset.mem_univ i)
  have hUpperExp : D ≤ (n : ℝ) * Real.exp (β * M) := by
    unfold D softMaxDenominator
    calc
      (∑ i, Real.exp (β * x i)) ≤ ∑ _i : Fin n, Real.exp (β * M) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcoord i) hβ.le)
      _ = (n : ℝ) * Real.exp (β * M) := by simp
  constructor
  · change M ≤ (1 / β) * Real.log D
    rw [show (1 / β) * Real.log D = Real.log D / β by ring,
      le_div_iff₀ hβ]
    rw [mul_comm]
    exact (Real.le_log_iff_exp_le hD).2 hLowerExp
  · change (1 / β) * Real.log D ≤ M + Real.log n / β
    rw [show (1 / β) * Real.log D = Real.log D / β by ring]
    apply (div_le_iff₀ hβ).2
    have hlog := Real.log_le_log hD hUpperExp
    rw [Real.log_mul hn.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    calc
      Real.log D ≤ Real.log n + β * M := hlog
      _ = (M + Real.log n / β) * β := by
        field_simp [hβ.ne']
        ring

/-- The absolute maximum coordinate of a Euclidean vector is bounded by its norm.

**Lean implementation helper.** -/
private lemma abs_euclideanFiniteMaximumSF_le {n : ℕ} [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) :
    |euclideanFiniteMaximumSF x| ≤ ‖x‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun j ↦ x j)
  have hi' : euclideanFiniteMaximumSF x = x i := by
    simpa [euclideanFiniteMaximumSF, HDP.Chapter5.finiteMaximum] using hi
  rw [hi']
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- The maximum-coordinate functional is integrable under every centered multivariate Gaussian law.

**Lean implementation helper.** -/
private lemma integrable_euclideanFiniteMaximumSF_gaussian
    {n : ℕ} [NeZero n] (S : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (euclideanFiniteMaximumSF (n := n)) (multivariateGaussian 0 S) := by
  have hid : Integrable
      (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (multivariateGaussian 0 S) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.integrable (by norm_num)
  apply Integrable.mono' hid.norm
    continuous_euclideanFiniteMaximumSF.aestronglyMeasurable
  filter_upwards [] with x
  simpa [Real.norm_eq_abs] using abs_euclideanFiniteMaximumSF_le x

/-- The smooth maximum is integrable under every centered multivariate Gaussian law.

**Lean implementation helper.** -/
private lemma integrable_smoothMaximum_gaussian
    {n : ℕ} [NeZero n] {β : ℝ} (hβ : 0 < β)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (smoothMaximum β) (multivariateGaussian 0 S) := by
  let c := Real.log n / β
  have hc : 0 ≤ c := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ n))) hβ.le
  have hM := integrable_euclideanFiniteMaximumSF_gaussian S
  have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦
      ‖euclideanFiniteMaximumSF x‖ + c) (multivariateGaussian 0 S) :=
    hM.norm.add (integrable_const c)
  apply Integrable.mono' hdom
    (smoothMaximum_contDiff β).continuous.aestronglyMeasurable
  filter_upwards [] with x
  have hb := smoothMaximum_bounds hβ x
  rw [Real.norm_eq_abs]
  apply (abs_le).2
  constructor
  · have hm : -‖euclideanFiniteMaximumSF x‖ ≤
        euclideanFiniteMaximumSF x := by
      simpa [Real.norm_eq_abs] using neg_abs_le (euclideanFiniteMaximumSF x)
    linarith [hb.1]
  · have hm : euclideanFiniteMaximumSF x ≤
        ‖euclideanFiniteMaximumSF x‖ := le_norm_self _
    linarith [hb.2]

/-- Integrating preserves the lower and upper approximation bounds for the smooth maximum.

**Lean implementation helper.** -/
private lemma integral_smoothMaximum_bounds
    {n : ℕ} [NeZero n] {β : ℝ} (hβ : 0 < β)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 S) ≤
        ∫ x, smoothMaximum β x ∂multivariateGaussian 0 S ∧
      (∫ x, smoothMaximum β x ∂multivariateGaussian 0 S) ≤
        (∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 S) +
          Real.log n / β := by
  let c := Real.log n / β
  have hM := integrable_euclideanFiniteMaximumSF_gaussian S
  have hF := integrable_smoothMaximum_gaussian hβ S
  have hc : Integrable (fun _x : EuclideanSpace ℝ (Fin n) ↦ c)
      (multivariateGaussian 0 S) := integrable_const c
  constructor
  · exact integral_mono hM hF fun x ↦ (smoothMaximum_bounds hβ x).1
  · have h := integral_mono hF (hM.add hc) fun x ↦
      (smoothMaximum_bounds hβ x).2
    change (∫ x, smoothMaximum β x ∂multivariateGaussian 0 S) ≤
      ∫ x, euclideanFiniteMaximumSF x + c ∂multivariateGaussian 0 S at h
    rw [integral_add hM hc, integral_const] at h
    simpa [c] using h

/-- The maximum coordinate of the Euclidean process vector equals the finite maximum of the original process.

**Lean implementation helper.** -/
private lemma finiteMaximum_processEuclideanVector_sf
    {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (e : I ≃ Fin (Fintype.card I)) (X : I → Ω → ℝ) (ω : Ω) :
    euclideanFiniteMaximumSF
        (processEuclideanVector (fun k ↦ X (e.symm k)) ω) =
      HDP.Chapter5.finiteMaximum X ω := by
  unfold euclideanFiniteMaximumSF HDP.Chapter5.finiteMaximum processEuclideanVector
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro k _
    exact Finset.le_sup' (fun i ↦ X i ω) (Finset.mem_univ (e.symm k))
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro i _
    simpa using Finset.le_sup' (fun k ↦ X (e.symm k) ω)
      (Finset.mem_univ (e i))

/-- Sudakov--Fernique: increment domination implies expected-supremum domination. The proof transports both finite processes to multivariate Gaussian laws,
applies Gaussian interpolation to the log-sum-exp smoother, rewrites the
covariance--Hessian contraction in terms of canonical increments, and removes
the smoothing error by an explicit inverse-temperature argument.

**Book Theorem 7.2.8.** -/
theorem sudakovFernique
    {I ΩX ΩY : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (μX : Measure ΩX) (μY : Measure ΩY)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (X : I → ΩX → ℝ) (Y : I → ΩY → ℝ)
    (hX : IsGaussianProcess X μX) (hY : IsGaussianProcess Y μY)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μX = 0)
    (hY0 : ∀ i, ∫ ω, Y i ω ∂μY = 0)
    (hinc : ∀ i j, processIncrementSecondMoment μX X i j ≤
      processIncrementSecondMoment μY Y i j) :
    expectedFiniteSupremum μX X ≤ expectedFiniteSupremum μY Y := by
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  have hn : 0 < n := Fintype.card_pos
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let XF : Fin n → ΩX → ℝ := fun i ↦ X (e.symm i)
  let YF : Fin n → ΩY → ℝ := fun i ↦ Y (e.symm i)
  have hXF : IsGaussianProcess XF μX := hX.comp_right e.symm
  have hYF : IsGaussianProcess YF μY := hY.comp_right e.symm
  have hXF0 : ∀ i, ∫ ω, XF i ω ∂μX = 0 := fun i ↦ by
    simpa [XF] using hX0 (e.symm i)
  have hYF0 : ∀ i, ∫ ω, YF i ω ∂μY = 0 := fun i ↦ by
    simpa [YF] using hY0 (e.symm i)
  let VX := processEuclideanVector XF
  let VY := processEuclideanVector YF
  let νX := Measure.map VX μX
  let νY := Measure.map VY μY
  let SX := gaussianMeasureCovarianceMatrix νX
  let SY := gaussianMeasureCovarianceMatrix νY
  have hSX : SX.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νX
  have hSY : SY.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νY
  have hLawX : νX = multivariateGaussian 0 SX := by
    simpa [νX, VX, SX] using
      processEuclideanVector_law_eq_multivariateGaussian hXF hXF0
  have hLawY : νY = multivariateGaussian 0 SY := by
    simpa [νY, VY, SY] using
      processEuclideanVector_law_eq_multivariateGaussian hYF hYF0
  have hSXinc : ∀ i j, matrixIncrement SX i j =
      processIncrementSecondMoment μX XF i j := by
    intro i j
    have h := processIncrementSecondMoment_eq hXF i j
    unfold matrixIncrement
    dsimp [SX, νX, VX]
    rw [gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 i i,
      gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 j j,
      gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 i j]
    symm
    simpa [processSecondMoment, pow_two] using h
  have hSYinc : ∀ i j, matrixIncrement SY i j =
      processIncrementSecondMoment μY YF i j := by
    intro i j
    have h := processIncrementSecondMoment_eq hYF i j
    unfold matrixIncrement
    dsimp [SY, νY, VY]
    rw [gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 i i,
      gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 j j,
      gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 i j]
    symm
    simpa [processSecondMoment, pow_two] using h
  have hmatrixInc : ∀ i j, matrixIncrement SX i j ≤
      matrixIncrement SY i j := by
    intro i j
    rw [hSXinc, hSYinc]
    change (∫ ω, (X (e.symm i) ω - X (e.symm j) ω) ^ 2 ∂μX) ≤
      ∫ ω, (Y (e.symm i) ω - Y (e.symm j) ω) ^ 2 ∂μY
    simpa [processIncrementSecondMoment] using hinc (e.symm i) (e.symm j)
  have hVX := processEuclideanVector_hasGaussianLaw hXF
  have hVY := processEuclideanVector_hasGaussianLaw hYF
  have hobjX : expectedFiniteSupremum μX X =
      ∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 SX := by
    unfold expectedFiniteSupremum
    calc
      (∫ ω, HDP.Chapter5.finiteMaximum X ω ∂μX) =
          ∫ ω, euclideanFiniteMaximumSF (VX ω) ∂μX := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simpa [VX, XF] using (finiteMaximum_processEuclideanVector_sf e X ω).symm
      _ = ∫ x, euclideanFiniteMaximumSF x ∂νX := by
        exact (integral_map hVX.aemeasurable
          continuous_euclideanFiniteMaximumSF.aestronglyMeasurable).symm
      _ = ∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 SX := by
        rw [hLawX]
  have hobjY : expectedFiniteSupremum μY Y =
      ∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 SY := by
    unfold expectedFiniteSupremum
    calc
      (∫ ω, HDP.Chapter5.finiteMaximum Y ω ∂μY) =
          ∫ ω, euclideanFiniteMaximumSF (VY ω) ∂μY := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simpa [VY, YF] using (finiteMaximum_processEuclideanVector_sf e Y ω).symm
      _ = ∫ x, euclideanFiniteMaximumSF x ∂νY := by
        exact (integral_map hVY.aemeasurable
          continuous_euclideanFiniteMaximumSF.aestronglyMeasurable).symm
      _ = ∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 SY := by
        rw [hLawY]
  rw [hobjX, hobjY]
  let AX := ∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 SX
  let AY := ∫ x, euclideanFiniteMaximumSF x ∂multivariateGaussian 0 SY
  by_contra hle
  have hdelta : 0 < AX - AY := sub_pos.mpr (lt_of_not_ge hle)
  let c := Real.log n
  have hc : 0 ≤ c := Real.log_nonneg (by exact_mod_cast hn)
  let β := c / (AX - AY) + 1
  have hβ : 0 < β := by dsimp [β]; positivity
  have herr : c / β < AX - AY := by
    have hmul : (AX - AY) * β = c + (AX - AY) := by
      dsimp [β]
      field_simp [hdelta.ne']
    apply (div_lt_iff₀ hβ).2
    rw [hmul]
    nlinarith
  have hcomp := smoothMaximum_expectation_comparison
    SX SY hSX hSY hmatrixInc hβ
  have hbX := integral_smoothMaximum_bounds hβ SX
  have hbY := integral_smoothMaximum_bounds hβ SY
  have hAXAY : AX ≤ AY + c / β := by
    dsimp [AX, AY, c]
    linarith [hbX.1, hcomp, hbY.2]
  linarith

/-- Defines coordinate evaluation as a continuous linear functional for Gordon's comparison argument.

**Lean implementation helper.** -/
private def gordonCoordCLM {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The Gordon coordinate functional evaluates the selected Euclidean coordinate.

**Lean implementation helper.** -/
@[simp] private lemma gordonCoordCLM_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : gordonCoordCLM i x = x i := by
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x i

/-- Defines the temperature-scaled log-sum-exp of a finite real family.

**Lean implementation helper.** -/
private def finiteLogSumExp {I : Type*} [Fintype I]
    (τ : ℝ) (a : I → ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (τ * a i)) / τ

/-- The finite log-sum-exp lies between the maximum and the maximum plus the logarithmic temperature error.

**Lean implementation helper.** -/
private lemma finiteLogSumExp_bounds
    {I : Type*} [Fintype I] [Nonempty I]
    (τ : ℝ) (hτ : 0 < τ) (a : I → ℝ) :
    let M := Finset.univ.sup' Finset.univ_nonempty a
    M ≤ finiteLogSumExp τ a ∧
      finiteLogSumExp τ a ≤ M + Real.log (Fintype.card I) / τ := by
  let M := Finset.univ.sup' Finset.univ_nonempty a
  let E := ∑ i, Real.exp (τ * a i)
  have hE : 0 < E :=
    Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hcard0 : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmax : ∀ i, a i ≤ M := by
    intro i
    exact Finset.le_sup' a (Finset.mem_univ i)
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  have hlowerExp : Real.exp (τ * M) ≤ E := by
    change Real.exp (τ * Finset.univ.sup' Finset.univ_nonempty a) ≤
      ∑ i, Real.exp (τ * a i)
    rw [hi₀]
    exact Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ Real.exp_nonneg (τ * a i))
      (Finset.mem_univ i₀)
  have hupperExp : E ≤ (Fintype.card I : ℝ) * Real.exp (τ * M) := by
    calc
      E ≤ ∑ _i : I, Real.exp (τ * M) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hmax i) hτ.le)
      _ = (Fintype.card I : ℝ) * Real.exp (τ * M) := by simp
  have hlowerLog : τ * M ≤ Real.log E := by
    exact (Real.le_log_iff_exp_le hE).2 hlowerExp
  have hupperLog :
      Real.log E ≤ Real.log (Fintype.card I) + τ * M := by
    calc
      Real.log E ≤
          Real.log ((Fintype.card I : ℝ) * Real.exp (τ * M)) :=
        Real.log_le_log hE hupperExp
      _ = Real.log (Fintype.card I) + τ * M := by
        rw [Real.log_mul hcard0 (Real.exp_ne_zero _), Real.log_exp]
  dsimp only
  constructor
  · unfold finiteLogSumExp
    apply (le_div_iff₀ hτ).2
    dsimp [E] at hlowerLog ⊢
    nlinarith
  · unfold finiteLogSumExp
    apply (div_le_iff₀ hτ).2
    dsimp [E] at hupperLog ⊢
    calc
      Real.log (∑ i, Real.exp (τ * a i)) ≤
          Real.log (Fintype.card I) + τ * M := hupperLog
      _ = (M + Real.log (Fintype.card I) / τ) * τ := by
        field_simp [hτ.ne']
        ring

/-- Defines the soft minimum as the negative log-sum-exp of the negated family.

**Lean implementation helper.** -/
private def finiteSoftMin {I : Type*} [Fintype I]
    (τ : ℝ) (a : I → ℝ) : ℝ :=
  -finiteLogSumExp τ (fun i ↦ -a i)

/-- The supremum of a negated finite family is the negative of its infimum.

**Lean implementation helper.** -/
private lemma sup_neg_eq_neg_inf
    {I : Type*} [Fintype I] [Nonempty I] (a : I → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun i ↦ -a i) =
      -Finset.univ.inf' Finset.univ_nonempty a := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    exact neg_le_neg (Finset.inf'_le a (Finset.mem_univ i))
  · obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty a
    rw [hi₀]
    exact Finset.le_sup' (fun i ↦ -a i) (Finset.mem_univ i₀)

/-- The finite soft minimum lies between the minimum minus the logarithmic temperature error and the minimum.

**Lean implementation helper.** -/
private lemma finiteSoftMin_bounds
    {I : Type*} [Fintype I] [Nonempty I]
    (τ : ℝ) (hτ : 0 < τ) (a : I → ℝ) :
    let m := Finset.univ.inf' Finset.univ_nonempty a
    m - Real.log (Fintype.card I) / τ ≤ finiteSoftMin τ a ∧
      finiteSoftMin τ a ≤ m := by
  have h := finiteLogSumExp_bounds τ hτ (fun i ↦ -a i)
  rw [sup_neg_eq_neg_inf a] at h
  dsimp only
  unfold finiteSoftMin
  constructor <;> linarith [h.1, h.2]

/-- The inner log-partition sum for one row.

**Lean implementation helper.** -/
private def gordonRowEnergy {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (u : U) : ℝ :=
  ∑ t, Real.exp (β * x (e (u, t)))

/-- The inner soft maximum at inverse temperature `β`.

**Lean implementation helper.** -/
private def gordonRowSoftMax {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (u : U) : ℝ :=
  Real.log (gordonRowEnergy e β x u) / β

/-- The outer log-partition sum for the soft minimum.

**Lean implementation helper.** -/
private def gordonOuterEnergy {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (α β : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ u, Real.exp (-α * gordonRowSoftMax e β x u)

/-- Two-temperature smooth minimum of row-wise smooth maxima.

**Lean implementation helper.** -/
private def gordonSmoothMinimax {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (α β : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -Real.log (gordonOuterEnergy e α β x) / α

/-- Defines the maximum over one row of a vector indexed by row-column pairs.

**Lean implementation helper.** -/
private def gordonRowMaximum {U T : Type*} [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun t ↦ x (e (u, t)))

/-- Defines the minimum over rows of their coordinatewise maxima.

**Lean implementation helper.** -/
private def gordonVectorMinimax {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (gordonRowMaximum e x)

/-- Inner Gibbs weight.

**Lean implementation helper.** -/
private def gordonInnerWeight {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u : U) (t : T) : ℝ :=
  Real.exp (β * x (e (u, t)) - Real.log (gordonRowEnergy e β x u))

/-- Outer Gibbs weight.

**Lean implementation helper.** -/
private def gordonOuterWeight {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (α β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u : U) : ℝ :=
  Real.exp (-α * gordonRowSoftMax e β x u -
    Real.log (gordonOuterEnergy e α β x))

/-- Coordinate gradient weight of the two-temperature smoother.

**Lean implementation helper.** -/
private def gordonCoordinateWeight {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (α β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u : U) (t : T) : ℝ :=
  gordonOuterWeight e α β x u * gordonInnerWeight e β x u t

/-- Defines the coordinate kernel representing the Hessian of the smooth Gordon minimax functional.

**Lean implementation helper.** -/
private def gordonHessianKernel {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Fintype T] {n : ℕ} (e : U × T ≃ Fin n)
    (α β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : U × T) : ℝ :=
  β * gordonCoordinateWeight e α β x i.1 i.2 *
      (if i.1 = j.1 then
        (if i.2 = j.2 then 1 else 0) - gordonInnerWeight e β x j.1 j.2
      else 0) -
    α * gordonCoordinateWeight e α β x i.1 i.2 *
      ((if i.1 = j.1 then 1 else 0) - gordonOuterWeight e α β x j.1) *
      gordonInnerWeight e β x j.1 j.2

/-- The Hessian kernel of the smooth Gordon minimax functional is symmetric.

**Lean implementation helper.** -/
private lemma gordonHessianKernel_symmetric
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : U × T) :
    gordonHessianKernel e α β x i j =
      gordonHessianKernel e α β x j i := by
  by_cases hrow : i.1 = j.1
  · by_cases hcol : i.2 = j.2
    · have hij : i = j := Prod.ext hrow hcol
      subst j
      rfl
    · have hrow' : j.1 = i.1 := hrow.symm
      have hcol' : j.2 ≠ i.2 := Ne.symm hcol
      unfold gordonHessianKernel gordonCoordinateWeight
      rw [if_pos hrow, if_pos hrow', if_neg hcol, if_neg hcol', hrow]
      ring
  · have hrow' : j.1 ≠ i.1 := Ne.symm hrow
    unfold gordonHessianKernel gordonCoordinateWeight
    rw [if_neg hrow, if_neg hrow']
    simp only [hrow, hrow', if_false]
    ring

/-- Defines the soft-max weighted gradient within one row.

**Lean implementation helper.** -/
private def gordonRowGradient {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ∑ t, gordonInnerWeight e β x u t • gordonCoordCLM (e (u, t))

/-- Defines the outer-weighted mean of the row gradients.

**Lean implementation helper.** -/
private def gordonMeanGradient {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ∑ u, gordonOuterWeight e α β x u • gordonRowGradient e β x u

/-- Defines the gradient of an inner soft-max weight.

**Lean implementation helper.** -/
private def gordonInnerWeightGradient {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u : U) (t : T) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  gordonInnerWeight e β x u t •
    (β • (gordonCoordCLM (e (u, t)) - gordonRowGradient e β x u))

/-- Defines the gradient of an outer soft-min weight.

**Lean implementation helper.** -/
private def gordonOuterWeightGradient {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  gordonOuterWeight e α β x u •
    ((-α) • (gordonRowGradient e β x u - gordonMeanGradient e α β x))

/-- The Gordon row energy is strictly positive.

**Lean implementation helper.** -/
private lemma gordonRowEnergy_pos {U T : Type*} [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    0 < gordonRowEnergy e β x u := by
  unfold gordonRowEnergy
  exact Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

/-- The Gordon outer energy is strictly positive.

**Lean implementation helper.** -/
private lemma gordonOuterEnergy_pos {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 < gordonOuterEnergy e α β x := by
  unfold gordonOuterEnergy
  exact Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

/-- Each row soft maximum approximates the row maximum within the logarithmic temperature error.

**Lean implementation helper.** -/
private lemma gordonRowSoftMax_bounds
    {U T : Type*} [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (hβ : 0 < β)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    gordonRowMaximum e x u ≤ gordonRowSoftMax e β x u ∧
      gordonRowSoftMax e β x u ≤
        gordonRowMaximum e x u + Real.log (Fintype.card T) / β := by
  simpa [gordonRowMaximum, gordonRowSoftMax, gordonRowEnergy,
    finiteLogSumExp] using
    finiteLogSumExp_bounds β hβ (fun t ↦ x (e (u, t)))

/-- The smooth Gordon minimax is the finite soft minimum of the row soft maxima.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_eq_finiteSoftMin
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonSmoothMinimax e α β x =
      finiteSoftMin α (fun u ↦ gordonRowSoftMax e β x u) := by
  unfold gordonSmoothMinimax gordonOuterEnergy finiteSoftMin finiteLogSumExp
  have hsum : (∑ u, Real.exp (-α * gordonRowSoftMax e β x u)) =
      ∑ u, Real.exp (α * -gordonRowSoftMax e β x u) := by
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    ring
  rw [hsum]
  ring

/-- The outer soft minimum approximates the minimum row soft maximum within the logarithmic temperature error.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_outer_bounds
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (α : ℝ) (hα : 0 < α) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    let m := Finset.univ.inf' Finset.univ_nonempty
      (fun u ↦ gordonRowSoftMax e β x u)
    m - Real.log (Fintype.card U) / α ≤ gordonSmoothMinimax e α β x ∧
      gordonSmoothMinimax e α β x ≤ m := by
  rw [gordonSmoothMinimax_eq_finiteSoftMin]
  exact finiteSoftMin_bounds α hα (fun u ↦ gordonRowSoftMax e β x u)

/-- Deterministic two-temperature approximation error.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_bounds
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin n)) :
    gordonVectorMinimax e x - Real.log (Fintype.card U) / α ≤
        gordonSmoothMinimax e α β x ∧
      gordonSmoothMinimax e α β x ≤
        gordonVectorMinimax e x + Real.log (Fintype.card T) / β := by
  let m₀ := gordonVectorMinimax e x
  let m₁ := Finset.univ.inf' Finset.univ_nonempty
    (fun u ↦ gordonRowSoftMax e β x u)
  have hrow := fun u ↦ gordonRowSoftMax_bounds e β hβ x u
  have hmLower : m₀ ≤ m₁ := by
    obtain ⟨u₁, -, hu₁⟩ := Finset.exists_mem_eq_inf'
      Finset.univ_nonempty (fun u ↦ gordonRowSoftMax e β x u)
    calc
      m₀ ≤ gordonRowMaximum e x u₁ :=
        Finset.inf'_le _ (Finset.mem_univ u₁)
      _ ≤ gordonRowSoftMax e β x u₁ := (hrow u₁).1
      _ = m₁ := hu₁.symm
  have hmUpper : m₁ ≤ m₀ + Real.log (Fintype.card T) / β := by
    obtain ⟨u₀, -, hu₀⟩ := Finset.exists_mem_eq_inf'
      Finset.univ_nonempty (gordonRowMaximum e x)
    calc
      m₁ ≤ gordonRowSoftMax e β x u₀ :=
        Finset.inf'_le _ (Finset.mem_univ u₀)
      _ ≤ gordonRowMaximum e x u₀ + Real.log (Fintype.card T) / β :=
        (hrow u₀).2
      _ = m₀ + Real.log (Fintype.card T) / β := by
        simp only [m₀, gordonVectorMinimax, hu₀]
  have houter := gordonSmoothMinimax_outer_bounds e α hα β x
  dsimp only at houter
  constructor
  · linarith [houter.1]
  · linarith [houter.2]

/-- The absolute Gordon vector minimax is bounded by the ambient Euclidean norm.

**Lean implementation helper.** -/
private lemma abs_gordonVectorMinimax_le
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    |gordonVectorMinimax e x| ≤ ‖x‖ := by
  have hcoord : ∀ i : U × T, |x (e i)| ≤ ‖x‖ := by
    intro i
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x (e i)
  have hrowLower : ∀ u, -‖x‖ ≤ gordonRowMaximum e x u := by
    intro u
    let t₀ : T := Classical.choice inferInstance
    calc
      -‖x‖ ≤ x (e (u, t₀)) := (abs_le.mp (hcoord (u, t₀))).1
      _ ≤ gordonRowMaximum e x u := by
        exact Finset.le_sup' (fun t ↦ x (e (u, t))) (Finset.mem_univ t₀)
  have hrowUpper : ∀ u, gordonRowMaximum e x u ≤ ‖x‖ := by
    intro u
    apply Finset.sup'_le Finset.univ_nonempty
    intro t _
    exact (le_abs_self _).trans (hcoord (u, t))
  have hminLower : -‖x‖ ≤ gordonVectorMinimax e x := by
    unfold gordonVectorMinimax
    exact Finset.le_inf' Finset.univ_nonempty _ fun u _ ↦ hrowLower u
  have hminUpper : gordonVectorMinimax e x ≤ ‖x‖ := by
    let u₀ : U := Classical.choice inferInstance
    exact (Finset.inf'_le (gordonRowMaximum e x) (Finset.mem_univ u₀)).trans
      (hrowUpper u₀)
  exact (abs_le).2 ⟨hminLower, hminUpper⟩

/-- The smooth Gordon minimax has at most linear growth in the Euclidean norm.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_linearGrowth
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ C, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖gordonSmoothMinimax e α β x‖ ≤ C * (1 + ‖x‖) := by
  let cU := Real.log (Fintype.card U) / α
  let cT := Real.log (Fintype.card T) / β
  have hcU : 0 ≤ cU := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) hα.le
  have hcT : 0 ≤ cT := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) hβ.le
  refine ⟨1 + cU + cT, by positivity, fun x ↦ ?_⟩
  have hb := gordonSmoothMinimax_bounds e hα hβ x
  have hm := abs_gordonVectorMinimax_le e x
  have hsabs : |gordonSmoothMinimax e α β x| ≤ ‖x‖ + cU + cT := by
    apply (abs_le).2
    constructor
    · dsimp [cU, cT] at hb ⊢
      have hmneg : -‖x‖ ≤ gordonVectorMinimax e x := (abs_le.mp hm).1
      linarith [hb.1]
    · dsimp [cU, cT] at hb ⊢
      have hmpos : gordonVectorMinimax e x ≤ ‖x‖ := (abs_le.mp hm).2
      linarith [hb.2]
  rw [Real.norm_eq_abs]
  calc
    |gordonSmoothMinimax e α β x| ≤ ‖x‖ + cU + cT := hsabs
    _ ≤ (1 + cU + cT) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg x]

/-- The Gordon inner weight is nonnegative.

**Lean implementation helper.** -/
private lemma gordonInnerWeight_nonneg {U T : Type*} [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) (t : T) :
    0 ≤ gordonInnerWeight e β x u t := by
  exact Real.exp_nonneg _

/-- The Gordon outer weight is nonnegative.

**Lean implementation helper.** -/
private lemma gordonOuterWeight_nonneg {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    0 ≤ gordonOuterWeight e α β x u := by
  exact Real.exp_nonneg _

/-- The inner soft-max weights in each row sum to one.

**Lean implementation helper.** -/
@[simp] private lemma sum_gordonInnerWeight {U T : Type*} [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    ∑ t, gordonInnerWeight e β x u t = 1 := by
  have hE := gordonRowEnergy_pos e β x u
  simp_rw [gordonInnerWeight, Real.exp_sub, Real.exp_log hE]
  rw [← Finset.sum_div]
  exact div_self hE.ne'

/-- The outer soft-min weights over rows sum to one.

**Lean implementation helper.** -/
@[simp] private lemma sum_gordonOuterWeight {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑ u, gordonOuterWeight e α β x u = 1 := by
  have hE := gordonOuterEnergy_pos e α β x
  simp_rw [gordonOuterWeight, Real.exp_sub, Real.exp_log hE]
  rw [← Finset.sum_div]
  exact div_self hE.ne'

/-- The Gordon outer weight is at most one.

**Lean implementation helper.** -/
private lemma gordonOuterWeight_le_one {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    gordonOuterWeight e α β x u ≤ 1 := by
  rw [← sum_gordonOuterWeight e α β x]
  exact Finset.single_le_sum
    (fun v (_ : v ∈ (Finset.univ : Finset U)) ↦
      gordonOuterWeight_nonneg e α β x v) (Finset.mem_univ u)

/-- The Gordon inner weight is at most one.

**Lean implementation helper.** -/
private lemma gordonInnerWeight_le_one {U T : Type*} [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) (t : T) :
    gordonInnerWeight e β x u t ≤ 1 := by
  rw [← sum_gordonInnerWeight e β x u]
  exact Finset.single_le_sum
    (fun s (_ : s ∈ (Finset.univ : Finset T)) ↦
      gordonInnerWeight_nonneg e β x u s) (Finset.mem_univ t)

/-- The Gordon coordinate weight is nonnegative.

**Lean implementation helper.** -/
private lemma gordonCoordinateWeight_nonneg {U T : Type*}
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) (t : T) :
    0 ≤ gordonCoordinateWeight e α β x u t :=
  mul_nonneg (gordonOuterWeight_nonneg e α β x u)
    (gordonInnerWeight_nonneg e β x u t)

/-- The Gordon coordinate weight is at most one.

**Lean implementation helper.** -/
private lemma gordonCoordinateWeight_le_one {U T : Type*}
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) (t : T) :
    gordonCoordinateWeight e α β x u t ≤ 1 := by
  unfold gordonCoordinateWeight
  calc
    gordonOuterWeight e α β x u * gordonInnerWeight e β x u t ≤
        1 * gordonInnerWeight e β x u t :=
      mul_le_mul_of_nonneg_right (gordonOuterWeight_le_one e α β x u)
        (gordonInnerWeight_nonneg e β x u t)
    _ ≤ 1 := by simpa using gordonInnerWeight_le_one e β x u t

/-- Computes the Fréchet derivative of the Gordon row energy at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonRowEnergy
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β : ℝ) (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    HasFDerivAt (fun z ↦ gordonRowEnergy e β z u)
      (∑ t, Real.exp (β * x (e (u, t))) •
        (β • gordonCoordCLM (e (u, t)))) x := by
  unfold gordonRowEnergy
  apply HasFDerivAt.fun_sum (u := (Finset.univ : Finset T))
  intro t _
  have hc : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ β * z (e (u, t)))
      (β • gordonCoordCLM (e (u, t))) x := by
    simpa [gordonCoordCLM_apply] using
      (gordonCoordCLM (e (u, t))).hasFDerivAt.const_mul β
  simpa using hc.exp

/-- Computes the Fréchet derivative of the Gordon row soft max at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonRowSoftMax
    {U T : Type*} [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) {β : ℝ} (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    HasFDerivAt (fun z ↦ gordonRowSoftMax e β z u)
      (gordonRowGradient e β x u) x := by
  let E := gordonRowEnergy e β x u
  let D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ∑ t, Real.exp (β * x (e (u, t))) •
      (β • gordonCoordCLM (e (u, t)))
  have hE : 0 < E := gordonRowEnergy_pos e β x u
  have hraw : HasFDerivAt (fun z ↦
      Real.log (gordonRowEnergy e β z u) / β)
      ((1 / β) • (E⁻¹ • D)) x := by
    have hlog := (hasFDerivAt_gordonRowEnergy e β x u).log hE.ne'
    simpa [E, D, div_eq_mul_inv, mul_comm] using hlog.const_mul (1 / β)
  apply hraw.congr_fderiv
  ext z
  simp only [gordonRowGradient, _root_.sum_apply,
    _root_.smul_apply]
  simp_rw [gordonInnerWeight, Real.exp_sub,
    Real.exp_log (gordonRowEnergy_pos e β x u)]
  simp only [E, D, _root_.smul_apply,
    _root_.sum_apply, gordonCoordCLM_apply]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  field_simp [hβ, (gordonRowEnergy_pos e β x u).ne']

/-- Computes the Fréchet derivative of the Gordon outer energy at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonOuterEnergy
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z ↦ gordonOuterEnergy e α β z)
      (∑ u, Real.exp (-α * gordonRowSoftMax e β x u) •
        ((-α) • gordonRowGradient e β x u)) x := by
  unfold gordonOuterEnergy
  apply HasFDerivAt.fun_sum (u := (Finset.univ : Finset U))
  intro u _
  have hm := hasFDerivAt_gordonRowSoftMax e hβ x u
  convert (hm.const_mul (-α)).exp using 1

/-- Computes the Fréchet derivative of the Gordon smooth minimax at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonSmoothMinimax
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gordonSmoothMinimax e α β)
      (gordonMeanGradient e α β x) x := by
  let A := gordonOuterEnergy e α β x
  let D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ∑ u, Real.exp (-α * gordonRowSoftMax e β x u) •
      ((-α) • gordonRowGradient e β x u)
  have hA : 0 < A := gordonOuterEnergy_pos e α β x
  have hraw₀ := ((hasFDerivAt_gordonOuterEnergy e α hβ x).log hA.ne').const_mul
    (-1 / α)
  have hfun : gordonSmoothMinimax e α β =
      (fun y ↦ (-1 / α) * Real.log (gordonOuterEnergy e α β y)) := by
    funext y
    unfold gordonSmoothMinimax
    ring
  have hraw : HasFDerivAt (gordonSmoothMinimax e α β)
      ((-1 / α) • (A⁻¹ • D)) x := by
    rw [hfun]
    apply hraw₀.congr_fderiv
    ext z
    simp only [A, D, _root_.smul_apply,
      _root_.sum_apply]
  apply hraw.congr_fderiv
  ext z
  simp only [gordonMeanGradient, _root_.sum_apply,
    _root_.smul_apply]
  simp_rw [gordonOuterWeight, Real.exp_sub,
    Real.exp_log (gordonOuterEnergy_pos e α β x)]
  simp only [A, D, _root_.smul_apply,
    _root_.sum_apply]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  field_simp [hα, (gordonOuterEnergy_pos e α β x).ne']

/-- The derivative of the smooth Gordon minimax along a coordinate basis vector is the corresponding coordinate weight.

**Lean implementation helper.** -/
private lemma fderiv_gordonSmoothMinimax_basis
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (x : EuclideanSpace ℝ (Fin n))
    (i : U × T) :
    fderiv ℝ (gordonSmoothMinimax e α β) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e i)) =
      gordonCoordinateWeight e α β x i.1 i.2 := by
  rw [(hasFDerivAt_gordonSmoothMinimax e hα hβ x).fderiv]
  simp only [gordonMeanGradient, gordonRowGradient,
    _root_.sum_apply, _root_.smul_apply,
    gordonCoordCLM_apply]
  rw [Fintype.sum_eq_single i.1]
  · rw [Fintype.sum_eq_single i.2]
    · simp [gordonCoordinateWeight]
    · intro t ht
      simp [ht, e.injective.eq_iff, Prod.ext_iff]
  · intro u hu
    simp [hu, e.injective.eq_iff, Prod.ext_iff]

/-- Computes the Fréchet derivative of the Gordon inner weight at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonInnerWeight
    {U T : Type*} [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) {β : ℝ} (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) (t : T) :
    HasFDerivAt (fun z ↦ gordonInnerWeight e β z u t)
      (gordonInnerWeightGradient e β x u t) x := by
  let E := gordonRowEnergy e β x u
  let D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ∑ s, Real.exp (β * x (e (u, s))) •
      (β • gordonCoordCLM (e (u, s)))
  have hE : 0 < E := gordonRowEnergy_pos e β x u
  have hexponent : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦
        β * z (e (u, t)) - Real.log (gordonRowEnergy e β z u))
      ((β • gordonCoordCLM (e (u, t))) - E⁻¹ • D) x := by
    have hcoord : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) ↦ β * z (e (u, t)))
        (β • gordonCoordCLM (e (u, t))) x := by
      simpa [gordonCoordCLM_apply] using
        (gordonCoordCLM (e (u, t))).hasFDerivAt.const_mul β
    exact hcoord.sub ((hasFDerivAt_gordonRowEnergy e β x u).log hE.ne')
  have hraw := hexponent.exp
  apply hraw.congr_fderiv
  ext z
  simp only [gordonInnerWeightGradient, _root_.smul_apply,
    _root_.sub_apply, gordonRowGradient,
    _root_.sum_apply]
  simp_rw [gordonInnerWeight, Real.exp_sub,
    Real.exp_log (gordonRowEnergy_pos e β x u)]
  simp only [E, D, _root_.smul_apply,
    _root_.sum_apply, gordonCoordCLM_apply]
  simp only [smul_eq_mul]
  congr 1
  calc
    β * z (e (u, t)) - (gordonRowEnergy e β x u)⁻¹ *
        (∑ s, Real.exp (β * x (e (u, s))) * (β * z (e (u, s)))) =
      β * z (e (u, t)) - β *
        (∑ s, Real.exp (β * x (e (u, s))) /
          gordonRowEnergy e β x u * z (e (u, s))) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      field_simp [(gordonRowEnergy_pos e β x u).ne']
    _ = β * (z (e (u, t)) -
        ∑ s, Real.exp (β * x (e (u, s))) /
          gordonRowEnergy e β x u * z (e (u, s))) := by ring

/-- Computes the Fréchet derivative of the Gordon outer weight at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonOuterWeight
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (u : U) :
    HasFDerivAt (fun z ↦ gordonOuterWeight e α β z u)
      (gordonOuterWeightGradient e α β x u) x := by
  let A := gordonOuterEnergy e α β x
  let D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ∑ v, Real.exp (-α * gordonRowSoftMax e β x v) •
      ((-α) • gordonRowGradient e β x v)
  have hA : 0 < A := gordonOuterEnergy_pos e α β x
  have hexponent : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦
        -α * gordonRowSoftMax e β z u -
          Real.log (gordonOuterEnergy e α β z))
      (((-α) • gordonRowGradient e β x u) - A⁻¹ • D) x := by
    exact (hasFDerivAt_gordonRowSoftMax e hβ x u).const_mul (-α) |>.sub
      ((hasFDerivAt_gordonOuterEnergy e α hβ x).log hA.ne')
  have hraw := hexponent.exp
  apply hraw.congr_fderiv
  ext z
  simp only [gordonOuterWeightGradient, _root_.smul_apply,
    _root_.sub_apply, gordonMeanGradient,
    _root_.sum_apply]
  simp_rw [gordonOuterWeight, Real.exp_sub,
    Real.exp_log (gordonOuterEnergy_pos e α β x)]
  simp only [A, D, _root_.smul_apply,
    _root_.sum_apply]
  simp only [smul_eq_mul]
  congr 1
  calc
    -α * (gordonRowGradient e β x u) z -
        (gordonOuterEnergy e α β x)⁻¹ *
          (∑ v, Real.exp (-α * gordonRowSoftMax e β x v) *
            (-α * (gordonRowGradient e β x v) z)) =
      -α * (gordonRowGradient e β x u) z - (-α) *
        (∑ v, Real.exp (-α * gordonRowSoftMax e β x v) /
          gordonOuterEnergy e α β x * (gordonRowGradient e β x v) z) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      field_simp [(gordonOuterEnergy_pos e α β x).ne']
    _ = -α * ((gordonRowGradient e β x u) z -
        ∑ v, Real.exp (-α * gordonRowSoftMax e β x v) /
          gordonOuterEnergy e α β x * (gordonRowGradient e β x v) z) := by ring

/-- Computes the Fréchet derivative of the Gordon coordinate weight at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonCoordinateWeight
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (i : U × T) :
    HasFDerivAt (fun z ↦ gordonCoordinateWeight e α β z i.1 i.2)
      (gordonOuterWeight e α β x i.1 •
          gordonInnerWeightGradient e β x i.1 i.2 +
        gordonInnerWeight e β x i.1 i.2 •
          gordonOuterWeightGradient e α β x i.1) x := by
  change HasFDerivAt
    ((fun z ↦ gordonOuterWeight e α β z i.1) *
      (fun z ↦ gordonInnerWeight e β z i.1 i.2)) _ x
  exact (hasFDerivAt_gordonOuterWeight e α hβ x i.1).mul
    (hasFDerivAt_gordonInnerWeight e hβ x i.1 i.2)

/-- A finite sum of a point-mass indicator selects the prescribed entry in a fixed row.

**Lean implementation helper.** -/
private lemma sum_ite_fixed_prod_row
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype T] (u : U) (j : U × T) (b : T → ℝ) :
    (∑ t, if u = j.1 ∧ t = j.2 then b t else 0) =
      if u = j.1 then b j.2 else 0 := by
  by_cases hu : u = j.1
  · subst u
    rw [Fintype.sum_eq_single j.2]
    · simp
    · intro t ht
      simp [ht]
  · simp [hu]

/-- A nested indicator sum over row-column pairs collapses to the selected product.

**Lean implementation helper.** -/
private lemma sum_mul_sum_ite_prod
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Fintype T]
    (a : U → ℝ) (b : U → T → ℝ) (j : U × T) :
    (∑ u, a u * ∑ t, if u = j.1 ∧ t = j.2 then b u t else 0) =
      a j.1 * b j.1 j.2 := by
  rw [Fintype.sum_eq_single j.1]
  · rw [Fintype.sum_eq_single j.2]
    · simp
    · intro t ht
      simp [ht]
  · intro u hu
    simp [hu]

/-- Computes the coordinate derivative of a Gordon coordinate weight as the Hessian kernel.

**Lean implementation helper.** -/
private lemma fderiv_gordonCoordinateWeight_basis
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (i j : U × T) :
    fderiv ℝ (fun z ↦ gordonCoordinateWeight e α β z i.1 i.2) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e j)) =
      gordonHessianKernel e α β x i j := by
  rw [(hasFDerivAt_gordonCoordinateWeight e α hβ x i).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    gordonInnerWeightGradient, gordonOuterWeightGradient,
    _root_.sub_apply, gordonRowGradient, gordonMeanGradient,
    _root_.sum_apply, gordonCoordCLM_apply,
    gordonCoordinateWeight, gordonHessianKernel]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply,
    e.injective.eq_iff, Prod.ext_iff]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_mul_sum_ite_prod]
  simp_rw [sum_ite_fixed_prod_row]
  by_cases hrow : i.1 = j.1
  · by_cases hcol : i.2 = j.2
    · have hij : i = j := Prod.ext hrow hcol
      subst j
      simp
      ring
    · simp [hrow, hcol]
      ring
  · simp [hrow]
    ring

/-- The smooth Gordon minimax functional is twice continuously differentiable.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_contDiff
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    ContDiff ℝ 2 (gordonSmoothMinimax e α β) := by
  have hrowEnergy : ∀ u : U,
      ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦
        gordonRowEnergy e β x u) := by
    intro u
    unfold gordonRowEnergy
    apply ContDiff.sum
    intro t _
    fun_prop
  have hrow : ∀ u : U,
      ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦
        gordonRowSoftMax e β x u) := by
    intro u
    unfold gordonRowSoftMax
    exact ((hrowEnergy u).log (fun x ↦ (gordonRowEnergy_pos e β x u).ne')).div
      contDiff_const (fun _ ↦ hβ)
  have houter : ContDiff ℝ 2 (gordonOuterEnergy e α β) := by
    unfold gordonOuterEnergy
    apply ContDiff.sum
    intro u _
    exact (contDiff_const.mul (hrow u)).exp
  unfold gordonSmoothMinimax
  exact ((houter.log fun x ↦ (gordonOuterEnergy_pos e α β x).ne').neg).div
    contDiff_const (fun _ ↦ hα)

/-- Identifies each Hessian entry of the smooth Gordon minimax with the Gordon Hessian kernel.

**Lean implementation helper.** -/
private lemma gaussianHessianEntry_gordonSmoothMinimax
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (i j : U × T) :
    gaussianHessianEntry (gordonSmoothMinimax e α β) (e i) (e j) x =
      gordonHessianKernel e α β x i j := by
  let e_i := EuclideanSpace.basisFun (Fin n) ℝ (e i)
  let e_j := EuclideanSpace.basisFun (Fin n) ℝ (e j)
  have hCD := gordonSmoothMinimax_contDiff e hα hβ
  have hDc : DifferentiableAt ℝ (fderiv ℝ (gordonSmoothMinimax e α β)) x :=
    (hCD.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hlink :
      gaussianHessianEntry (gordonSmoothMinimax e α β) (e i) (e j) x =
        fderiv ℝ
          (fun z ↦ fderiv ℝ (gordonSmoothMinimax e α β) z e_j) x e_i := by
    unfold gaussianHessianEntry
    rw [fderiv_clm_apply hDc (differentiableAt_const e_j)]
    simp [e_i, e_j]
  rw [hlink]
  have hfun :
      (fun z ↦ fderiv ℝ (gordonSmoothMinimax e α β) z e_j) =
        (fun z ↦ gordonCoordinateWeight e α β z j.1 j.2) := by
    funext z
    exact fderiv_gordonSmoothMinimax_basis e hα hβ z j
  rw [hfun]
  change fderiv ℝ
      (fun z ↦ gordonCoordinateWeight e α β z j.1 j.2) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e i)) = _
  rw [fderiv_gordonCoordinateWeight_basis e α hβ x j i]
  exact gordonHessianKernel_symmetric e α β x j i

/-- Every coordinate derivative of the smooth Gordon minimax admits a uniform bound.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_coordinateDerivative_bound
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∀ k, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (gordonSmoothMinimax e α β) x
        (EuclideanSpace.basisFun (Fin n) ℝ k)‖ ≤ C := by
  intro k
  refine ⟨1, fun x ↦ ?_⟩
  let i : U × T := e.symm k
  have hk : e i = k := e.apply_symm_apply k
  rw [← hk, fderiv_gordonSmoothMinimax_basis e hα hβ x i,
    Real.norm_eq_abs, abs_of_nonneg
      (gordonCoordinateWeight_nonneg e α β x i.1 i.2)]
  exact gordonCoordinateWeight_le_one e α β x i.1 i.2

/-- Distinct coordinates in the same row give a nonpositive Gordon Hessian entry.

**Lean implementation helper.** -/
private lemma gordonHessianKernel_within_nonpos
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : EuclideanSpace ℝ (Fin n))
    {i j : U × T} (hrow : i.1 = j.1) (hij : i ≠ j) :
    gordonHessianKernel e α β x i j ≤ 0 := by
  have hcol : i.2 ≠ j.2 := by
    intro h
    apply hij
    exact Prod.ext hrow h
  have hpi : 0 ≤ gordonCoordinateWeight e α β x i.1 i.2 :=
    mul_nonneg (gordonOuterWeight_nonneg e α β x i.1)
      (gordonInnerWeight_nonneg e β x i.1 i.2)
  have hqj : 0 ≤ gordonInnerWeight e β x j.1 j.2 :=
    gordonInnerWeight_nonneg e β x j.1 j.2
  have ha : 0 ≤ 1 - gordonOuterWeight e α β x j.1 :=
    sub_nonneg.mpr (gordonOuterWeight_le_one e α β x j.1)
  unfold gordonHessianKernel
  rw [if_pos hrow, if_neg hcol]
  simp only [if_pos hrow]
  have hfirst : β * gordonCoordinateWeight e α β x i.1 i.2 *
      (-gordonInnerWeight e β x j.1 j.2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβ hpi) (neg_nonpos.mpr hqj)
  have hsecond : 0 ≤ α * gordonCoordinateWeight e α β x i.1 i.2 *
      (1 - gordonOuterWeight e α β x j.1) *
      gordonInnerWeight e β x j.1 j.2 := by positivity
  linarith

/-- Coordinates in different rows give a nonnegative Gordon Hessian entry.

**Lean implementation helper.** -/
private lemma gordonHessianKernel_across_nonneg
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 ≤ α) (x : EuclideanSpace ℝ (Fin n))
    {i j : U × T} (hrow : i.1 ≠ j.1) :
    0 ≤ gordonHessianKernel e α β x i j := by
  have hpi : 0 ≤ gordonCoordinateWeight e α β x i.1 i.2 :=
    mul_nonneg (gordonOuterWeight_nonneg e α β x i.1)
      (gordonInnerWeight_nonneg e β x i.1 i.2)
  have haj : 0 ≤ gordonOuterWeight e α β x j.1 :=
    gordonOuterWeight_nonneg e α β x j.1
  have hqj : 0 ≤ gordonInnerWeight e β x j.1 j.2 :=
    gordonInnerWeight_nonneg e β x j.1 j.2
  unfold gordonHessianKernel
  rw [if_neg hrow]
  simp only [if_neg hrow]
  have hterm : 0 ≤ α * gordonCoordinateWeight e α β x i.1 i.2 *
      gordonOuterWeight e α β x j.1 *
      gordonInnerWeight e β x j.1 j.2 := by positivity
  linarith

/-- Bounds the absolute Gordon Hessian kernel by the sum of its inner- and outer-weight contributions.

**Lean implementation helper.** -/
private lemma abs_gordonHessianKernel_le
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : EuclideanSpace ℝ (Fin n))
    (i j : U × T) :
    |gordonHessianKernel e α β x i j| ≤ β + α := by
  let p := gordonCoordinateWeight e α β x i.1 i.2
  let q := gordonInnerWeight e β x j.1 j.2
  let a := gordonOuterWeight e α β x j.1
  have hp0 : 0 ≤ p := gordonCoordinateWeight_nonneg e α β x i.1 i.2
  have hp1 : p ≤ 1 := gordonCoordinateWeight_le_one e α β x i.1 i.2
  have hq0 : 0 ≤ q := gordonInnerWeight_nonneg e β x j.1 j.2
  have hq1 : q ≤ 1 := gordonInnerWeight_le_one e β x j.1 j.2
  have ha0 : 0 ≤ a := gordonOuterWeight_nonneg e α β x j.1
  have ha1 : a ≤ 1 := gordonOuterWeight_le_one e α β x j.1
  let A : ℝ := if i.1 = j.1 then (if i.2 = j.2 then 1 else 0) - q else 0
  let B : ℝ := (if i.1 = j.1 then 1 else 0) - a
  have hA : |A| ≤ 1 := by
    dsimp [A]
    split_ifs <;> simp_all [abs_of_nonneg, abs_of_nonpos]
  have hB : |B| ≤ 1 := by
    dsimp [B]
    split_ifs <;> simp_all [abs_of_nonneg, abs_of_nonpos]
  have hpA : p * |A| ≤ 1 := by
    calc p * |A| ≤ 1 * |A| := mul_le_mul_of_nonneg_right hp1 (abs_nonneg A)
      _ ≤ 1 := by simpa using hA
  have hpBq : p * |B| * q ≤ 1 := by
    have hpB : p * |B| ≤ 1 := by
      calc p * |B| ≤ 1 * |B| := mul_le_mul_of_nonneg_right hp1 (abs_nonneg B)
        _ ≤ 1 := by simpa using hB
    calc p * |B| * q ≤ 1 * q := mul_le_mul_of_nonneg_right hpB hq0
      _ ≤ 1 := by simpa using hq1
  change |β * p * A - α * p * B * q| ≤ β + α
  calc
    |β * p * A - α * p * B * q| ≤
        |β * p * A| + |α * p * B * q| := abs_sub _ _
    _ = β * (p * |A|) + α * (p * |B| * q) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hα, abs_of_nonneg hβ, abs_of_nonneg hp0,
        abs_of_nonneg hq0]
      ring
    _ ≤ β * 1 + α * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hpA hβ)
        (mul_le_mul_of_nonneg_left hpBq hα)
    _ = β + α := by ring

/-- Every Hessian entry of the smooth Gordon minimax admits a uniform bound.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_hessian_bound
    {U T : Type*}
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∀ k l, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖gaussianHessianEntry (gordonSmoothMinimax e α β) k l x‖ ≤ C := by
  classical
  intro k l
  refine ⟨β + α, fun x ↦ ?_⟩
  let i : U × T := e.symm k
  let j : U × T := e.symm l
  have hk : e i = k := e.apply_symm_apply k
  have hl : e j = l := e.apply_symm_apply l
  rw [← hk, ← hl, gaussianHessianEntry_gordonSmoothMinimax e hα.ne' hβ.ne' x i j,
    Real.norm_eq_abs]
  exact abs_gordonHessianKernel_le e hα.le hβ.le x i j

/-- Every Hessian row sums to zero. This is the analytic expression of the
translation identity `Φ(x+c·1)=Φ(x)+c`.

**Lean implementation helper.** -/
private lemma sum_gordonHessianKernel_row
    {U T : Type*} [DecidableEq U] [DecidableEq T]
    [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) (α β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : U × T) :
    ∑ j : U × T, gordonHessianKernel e α β x i j = 0 := by
  let p := gordonCoordinateWeight e α β x i.1 i.2
  let A : U × T → ℝ := fun j ↦
    if i.1 = j.1 then
      (if i.2 = j.2 then 1 else 0) - gordonInnerWeight e β x j.1 j.2
    else 0
  let B : U × T → ℝ := fun j ↦
    ((if i.1 = j.1 then 1 else 0) - gordonOuterWeight e α β x j.1) *
      gordonInnerWeight e β x j.1 j.2
  have hA : ∑ j, A j = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [A]
    have hrow : ∀ u : U,
        (∑ t, if i.1 = u then
          (if i.2 = t then (1 : ℝ) else 0) - gordonInnerWeight e β x u t
        else 0) = if i.1 = u then 0 else 0 := by
      intro u
      by_cases hu : i.1 = u
      · subst u
        simp [sum_gordonInnerWeight]
      · simp [hu]
    simp_rw [hrow]
    simp
  have hB : ∑ j, B j = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [B]
    calc
      (∑ u, ∑ t,
          ((if i.1 = u then (1 : ℝ) else 0) -
              gordonOuterWeight e α β x u) *
            gordonInnerWeight e β x u t) =
          ∑ u, ((if i.1 = u then (1 : ℝ) else 0) -
              gordonOuterWeight e α β x u) *
            (∑ t, gordonInnerWeight e β x u t) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
      _ = ∑ u, ((if i.1 = u then (1 : ℝ) else 0) -
              gordonOuterWeight e α β x u) := by
        simp only [sum_gordonInnerWeight, mul_one]
      _ = 0 := by
        rw [Finset.sum_sub_distrib, sum_gordonOuterWeight e α β x]
        simp
  unfold gordonHessianKernel
  have hfactorA :
      Finset.univ.sum (fun j : U × T ↦ β * p * A j) =
        β * p * Finset.univ.sum A := by
    rw [Finset.mul_sum]
  have hfactorB :
      Finset.univ.sum (fun j : U × T ↦
        α * p *
          ((if i.1 = j.1 then 1 else 0) - gordonOuterWeight e α β x j.1) *
          gordonInnerWeight e β x j.1 j.2) =
        α * p * Finset.univ.sum B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_sub_distrib, hfactorA, hfactorB, hA, hB]
  ring

/-- The contraction of ordered increments against a Hessian with the Gordon sign pattern is nonnegative.

**Lean implementation helper.** -/
private lemma classified_increment_contraction_nonneg
    {I U : Type*} [Fintype I]
    (row : I → U) (d H : I → I → ℝ)
    (hdiag : ∀ i, d i i = 0)
    (hwithin : ∀ i j, row i = row j → 0 ≤ d i j)
    (hacross : ∀ i j, row i ≠ row j → d i j ≤ 0)
    (hHwithin : ∀ i j, row i = row j → i ≠ j → H i j ≤ 0)
    (hHacross : ∀ i j, row i ≠ row j → 0 ≤ H i j) :
    0 ≤ -(1 / 2 : ℝ) * ∑ i, ∑ j, d i j * H i j := by
  have hterm : ∀ i j, d i j * H i j ≤ 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · by_cases hrow : row i = row j
      · exact mul_nonpos_of_nonneg_of_nonpos
          (hwithin i j hrow) (hHwithin i j hrow hij)
      · exact mul_nonpos_of_nonpos_of_nonneg
          (hacross i j hrow) (hHacross i j hrow)
  have hsum : (∑ i, ∑ j, d i j * H i j) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ Finset.sum_nonpos fun j _ ↦ hterm i j
  exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) hsum

/-- Matrix-law Gordon comparison for the two-temperature smoother. This is
the only place where the generic linear-growth interpolation endpoint is
used.

**Lean implementation helper.** -/
private lemma gordonSmoothMinimax_expectation_comparison
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hwithin : ∀ i j : U × T, i.1 = j.1 →
      matrixIncrement SX (e i) (e j) ≤ matrixIncrement SY (e i) (e j))
    (hacross : ∀ i j : U × T, i.1 ≠ j.1 →
      matrixIncrement SY (e i) (e j) ≤ matrixIncrement SX (e i) (e j)) :
    (∫ x, gordonSmoothMinimax e α β x ∂multivariateGaussian 0 SX) ≤
      ∫ x, gordonSmoothMinimax e α β x ∂multivariateGaussian 0 SY := by
  classical
  apply gaussianInterpolationExpectation_le_of_hessianSum_nonneg_boundedDerivative_coordinate
    SY SX hSY hSX (gordonSmoothMinimax e α β)
      (gordonSmoothMinimax_contDiff e hα.ne' hβ.ne')
      (gordonSmoothMinimax_coordinateDerivative_bound e hα.ne' hβ.ne')
      (gordonSmoothMinimax_hessian_bound e hα hβ)
  intro u hu
  let ν := (multivariateGaussian 0 SY).prod (multivariateGaussian 0 SX)
  let z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) := gaussianInterpolationPoint u
  let C : Fin n → Fin n → ℝ := fun k l ↦ SY k l - SX k l
  let K : Fin n → Fin n → ℝ := fun k l ↦
    ∫ p, gaussianHessianEntry (gordonSmoothMinimax e α β) k l (z p) ∂ν
  let d : Fin n → Fin n → ℝ := fun k l ↦
    C k k + C l l - 2 * C k l
  have hzcont : Continuous z := by
    dsimp [z]
    unfold gaussianInterpolationPoint
    fun_prop
  have hCD := gordonSmoothMinimax_contDiff e hα.ne' hβ.ne'
  have hHcont : ∀ k l, Continuous
      (gaussianHessianEntry (gordonSmoothMinimax e α β) k l) := by
    intro k l
    exact (((hCD.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hHint : ∀ k l, Integrable
      (fun p ↦ gaussianHessianEntry (gordonSmoothMinimax e α β) k l (z p)) ν := by
    intro k l
    obtain ⟨D, hD⟩ := gordonSmoothMinimax_hessian_bound e hα hβ k l
    apply Integrable.of_bound ((hHcont k l).comp hzcont).aestronglyMeasurable D
    filter_upwards [] with p
    exact hD _
  have hKsymm : ∀ k l, K k l = K l k := by
    intro k l
    unfold K
    apply integral_congr_ae
    filter_upwards [] with p
    let i : U × T := e.symm k
    let j : U × T := e.symm l
    have hk : e i = k := e.apply_symm_apply k
    have hl : e j = l := e.apply_symm_apply l
    rw [← hk, ← hl,
      gaussianHessianEntry_gordonSmoothMinimax e hα.ne' hβ.ne' (z p) i j,
      gaussianHessianEntry_gordonSmoothMinimax e hα.ne' hβ.ne' (z p) j i]
    exact gordonHessianKernel_symmetric e α β (z p) i j
  have hKrow : ∀ k, ∑ l, K k l = 0 := by
    intro k
    unfold K
    rw [← integral_finsetSum]
    · apply integral_eq_zero_of_ae
      filter_upwards [] with p
      let i : U × T := e.symm k
      have hk : e i = k := e.apply_symm_apply k
      calc
        (∑ l, gaussianHessianEntry (gordonSmoothMinimax e α β) k l (z p)) =
            ∑ j : U × T,
              gaussianHessianEntry (gordonSmoothMinimax e α β)
                k (e j) (z p) := by
          symm
          exact e.sum_comp (fun l : Fin n ↦
            gaussianHessianEntry (gordonSmoothMinimax e α β) k l (z p))
        _ = ∑ j : U × T, gordonHessianKernel e α β (z p) i j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← hk, gaussianHessianEntry_gordonSmoothMinimax
            e hα.ne' hβ.ne' (z p) i j]
        _ = 0 := sum_gordonHessianKernel_row e α β (z p) i
    · intro l _
      exact hHint k l
  have hdDiag : ∀ k, d k k = 0 := by
    intro k
    dsimp [d]
    ring
  have hdWithin : ∀ k l, (e.symm k).1 = (e.symm l).1 → 0 ≤ d k l := by
    intro k l hrow
    let i : U × T := e.symm k
    let j : U × T := e.symm l
    have hk : e i = k := e.apply_symm_apply k
    have hl : e j = l := e.apply_symm_apply l
    have hinc := hwithin i j hrow
    dsimp [d, C, matrixIncrement] at hinc ⊢
    rw [← hk, ← hl]
    linarith
  have hdAcross : ∀ k l, (e.symm k).1 ≠ (e.symm l).1 → d k l ≤ 0 := by
    intro k l hrow
    let i : U × T := e.symm k
    let j : U × T := e.symm l
    have hk : e i = k := e.apply_symm_apply k
    have hl : e j = l := e.apply_symm_apply l
    have hinc := hacross i j hrow
    dsimp [d, C, matrixIncrement] at hinc ⊢
    rw [← hk, ← hl]
    linarith
  have hKWithin : ∀ k l, (e.symm k).1 = (e.symm l).1 → k ≠ l → K k l ≤ 0 := by
    intro k l hrow hkl
    let i : U × T := e.symm k
    let j : U × T := e.symm l
    have hk : e i = k := e.apply_symm_apply k
    have hl : e j = l := e.apply_symm_apply l
    have hij : i ≠ j := by
      intro hij
      apply hkl
      rw [← hk, ← hl, hij]
    unfold K
    apply integral_nonpos_of_ae
    filter_upwards [] with p
    rw [← hk, ← hl,
      gaussianHessianEntry_gordonSmoothMinimax e hα.ne' hβ.ne' (z p) i j]
    exact gordonHessianKernel_within_nonpos e hα.le hβ.le (z p) hrow hij
  have hKAcross : ∀ k l, (e.symm k).1 ≠ (e.symm l).1 → 0 ≤ K k l := by
    intro k l hrow
    let i : U × T := e.symm k
    let j : U × T := e.symm l
    have hk : e i = k := e.apply_symm_apply k
    have hl : e j = l := e.apply_symm_apply l
    unfold K
    apply integral_nonneg_of_ae
    filter_upwards [] with p
    rw [← hk, ← hl,
      gaussianHessianEntry_gordonSmoothMinimax e hα.ne' hβ.ne' (z p) i j]
    exact gordonHessianKernel_across_nonneg e hα.le (z p) hrow
  change 0 ≤ ∑ k, ∑ l, C k l * K k l
  rw [covariance_contraction_eq_increment_contraction C K hKsymm hKrow]
  exact classified_increment_contraction_nonneg
    (fun k ↦ (e.symm k).1) d K hdDiag hdWithin hdAcross hKWithin hKAcross

/-- The Gordon vector minimax is continuous.

**Lean implementation helper.** -/
private lemma continuous_gordonVectorMinimax
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) :
    Continuous (gordonVectorMinimax e) := by
  unfold gordonVectorMinimax gordonRowMaximum
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro u _
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro t _
  fun_prop

/-- The nonsmooth Gordon minimax functional is integrable under every centered multivariate Gaussian law.

**Lean implementation helper.** -/
private lemma integrable_gordonVectorMinimax_gaussian
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (gordonVectorMinimax e) (multivariateGaussian 0 S) := by
  have hid : Integrable (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (multivariateGaussian 0 S) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.integrable (by norm_num)
  apply Integrable.mono' hid.norm
    (continuous_gordonVectorMinimax e).aestronglyMeasurable
  filter_upwards [] with x
  simpa [Real.norm_eq_abs] using abs_gordonVectorMinimax_le e x

/-- The smooth Gordon minimax functional is integrable under every centered multivariate Gaussian law.

**Lean implementation helper.** -/
private lemma integrable_gordonSmoothMinimax_gaussian
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (gordonSmoothMinimax e α β) (multivariateGaussian 0 S) := by
  obtain ⟨C, hC0, hC⟩ := gordonSmoothMinimax_linearGrowth e hα hβ
  have hid : Integrable (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (multivariateGaussian 0 S) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.integrable (by norm_num)
  have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦
      C * (1 + ‖x‖)) (multivariateGaussian 0 S) := by
    simpa [mul_add] using (integrable_const C).add (hid.norm.const_mul C)
  apply Integrable.mono' hdom
    (gordonSmoothMinimax_contDiff e hα.ne' hβ.ne').continuous.aestronglyMeasurable
  filter_upwards [] with x
  exact hC x

/-- Integrating preserves the approximation bounds between the smooth and nonsmooth Gordon minimax functionals.

**Lean implementation helper.** -/
private lemma integral_gordonSmoothMinimax_bounds
    {U T : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    {n : ℕ} (e : U × T ≃ Fin n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 S) -
          Real.log (Fintype.card U) / α ≤
        ∫ x, gordonSmoothMinimax e α β x ∂multivariateGaussian 0 S ∧
      (∫ x, gordonSmoothMinimax e α β x ∂multivariateGaussian 0 S) ≤
        (∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 S) +
          Real.log (Fintype.card T) / β := by
  let cU := Real.log (Fintype.card U) / α
  let cT := Real.log (Fintype.card T) / β
  have hM := integrable_gordonVectorMinimax_gaussian e S
  have hF := integrable_gordonSmoothMinimax_gaussian e hα hβ S
  have hcU : Integrable (fun _x : EuclideanSpace ℝ (Fin n) ↦ cU)
      (multivariateGaussian 0 S) := integrable_const cU
  have hcT : Integrable (fun _x : EuclideanSpace ℝ (Fin n) ↦ cT)
      (multivariateGaussian 0 S) := integrable_const cT
  constructor
  · have h := integral_mono (hM.sub hcU) hF fun x ↦
      (gordonSmoothMinimax_bounds e hα hβ x).1
    change (∫ x, gordonVectorMinimax e x - cU
        ∂multivariateGaussian 0 S) ≤ _ at h
    rw [integral_sub hM hcU, integral_const] at h
    simpa [cU] using h
  · have h := integral_mono hF (hM.add hcT) fun x ↦
      (gordonSmoothMinimax_bounds e hα hβ x).2
    change _ ≤ (∫ x, gordonVectorMinimax e x + cT
        ∂multivariateGaussian 0 S) at h
    rw [integral_add hM hcT, integral_const] at h
    simpa [cT] using h

/-- The vector minimax of the Euclidean process vector equals the original finite process minimax.

**Lean implementation helper.** -/
private lemma gordonVectorMinimax_processEuclideanVector
    {U T Ω : Type*} [Fintype U] [Nonempty U] [Fintype T] [Nonempty T]
    [MeasurableSpace Ω]
    (e : U × T ≃ Fin (Fintype.card (U × T)))
    (X : U → T → Ω → ℝ) (ω : Ω) :
    gordonVectorMinimax e
        (processEuclideanVector
          (fun k ↦ X (e.symm k).1 (e.symm k).2) ω) =
      finiteMinimax X ω := by
  unfold gordonVectorMinimax gordonRowMaximum finiteMinimax
    HDP.Chapter5.finiteMaximum processEuclideanVector
  apply Finset.inf'_congr Finset.univ_nonempty rfl
  intro u _
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro t _
  simp

/-- Gordon min-max comparison for Gaussian processes. The increment hypotheses imply this expectation comparison without equal
marginal variances. The proof uses a two-temperature smooth min--max,
Gaussian interpolation, and the canonical increment-contraction identity.

**Book Theorem 7.2.9.** -/
theorem gordonExpectationInequality
    {U T ΩX ΩY : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T]
    [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (μX : Measure ΩX) (μY : Measure ΩY)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (X : U → T → ΩX → ℝ) (Y : U → T → ΩY → ℝ)
    (hX : IsGaussianProcess (fun p : U × T ↦ X p.1 p.2) μX)
    (hY : IsGaussianProcess (fun p : U × T ↦ Y p.1 p.2) μY)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μX = 0)
    (hY0 : ∀ u t, ∫ ω, Y u t ω ∂μY = 0)
    (hwithin : ∀ u t s,
      processIncrementSecondMoment μX (fun p : U × T ↦ X p.1 p.2)
          (u, t) (u, s) ≤
        processIncrementSecondMoment μY (fun p : U × T ↦ Y p.1 p.2)
          (u, t) (u, s))
    (hacross : ∀ u v, u ≠ v → ∀ t s,
      processIncrementSecondMoment μY (fun p : U × T ↦ Y p.1 p.2)
          (u, t) (v, s) ≤
        processIncrementSecondMoment μX (fun p : U × T ↦ X p.1 p.2)
          (u, t) (v, s)) :
    (∫ ω, finiteMinimax X ω ∂μX) ≤
      ∫ ω, finiteMinimax Y ω ∂μY := by
  let e : U × T ≃ Fin (Fintype.card (U × T)) := Fintype.equivFin (U × T)
  let PX : U × T → ΩX → ℝ := fun p ↦ X p.1 p.2
  let PY : U × T → ΩY → ℝ := fun p ↦ Y p.1 p.2
  let XF : Fin (Fintype.card (U × T)) → ΩX → ℝ := PX ∘ e.symm
  let YF : Fin (Fintype.card (U × T)) → ΩY → ℝ := PY ∘ e.symm
  have hXF : IsGaussianProcess XF μX := by
    simpa [XF, PX] using hX.comp_right e.symm
  have hYF : IsGaussianProcess YF μY := by
    simpa [YF, PY] using hY.comp_right e.symm
  have hXF0 : ∀ k, ∫ ω, XF k ω ∂μX = 0 := by
    intro k
    simpa [XF, PX] using hX0 (e.symm k).1 (e.symm k).2
  have hYF0 : ∀ k, ∫ ω, YF k ω ∂μY = 0 := by
    intro k
    simpa [YF, PY] using hY0 (e.symm k).1 (e.symm k).2
  let VX := processEuclideanVector XF
  let VY := processEuclideanVector YF
  let νX := Measure.map VX μX
  let νY := Measure.map VY μY
  let SX := gaussianMeasureCovarianceMatrix νX
  let SY := gaussianMeasureCovarianceMatrix νY
  have hSX : SX.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νX
  have hSY : SY.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νY
  have hlawX : νX = multivariateGaussian 0 SX := by
    simpa [νX, VX, SX] using
      processEuclideanVector_law_eq_multivariateGaussian hXF hXF0
  have hlawY : νY = multivariateGaussian 0 SY := by
    simpa [νY, VY, SY] using
      processEuclideanVector_law_eq_multivariateGaussian hYF hYF0
  have hSXinc : ∀ k l, matrixIncrement SX k l =
      processIncrementSecondMoment μX XF k l := by
    intro k l
    have hinc := processIncrementSecondMoment_eq hXF k l
    unfold matrixIncrement
    dsimp [SX, νX, VX]
    rw [gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 k k,
      gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 l l,
      gaussianMeasureCovarianceMatrix_processVector_apply hXF hXF0 k l]
    symm
    simpa [processSecondMoment, pow_two] using hinc
  have hSYinc : ∀ k l, matrixIncrement SY k l =
      processIncrementSecondMoment μY YF k l := by
    intro k l
    have hinc := processIncrementSecondMoment_eq hYF k l
    unfold matrixIncrement
    dsimp [SY, νY, VY]
    rw [gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 k k,
      gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 l l,
      gaussianMeasureCovarianceMatrix_processVector_apply hYF hYF0 k l]
    symm
    simpa [processSecondMoment, pow_two] using hinc
  have hmatrixWithin : ∀ i j : U × T, i.1 = j.1 →
      matrixIncrement SX (e i) (e j) ≤ matrixIncrement SY (e i) (e j) := by
    intro i j hrow
    rw [hSXinc, hSYinc]
    simpa [XF, YF, PX, PY, processIncrementSecondMoment, hrow] using
      hwithin i.1 i.2 j.2
  have hmatrixAcross : ∀ i j : U × T, i.1 ≠ j.1 →
      matrixIncrement SY (e i) (e j) ≤ matrixIncrement SX (e i) (e j) := by
    intro i j hrow
    rw [hSXinc, hSYinc]
    simpa [XF, YF, PX, PY, processIncrementSecondMoment] using
      hacross i.1 j.1 hrow i.2 j.2
  have hVX := processEuclideanVector_hasGaussianLaw hXF
  have hVY := processEuclideanVector_hasGaussianLaw hYF
  have hobjX : (∫ ω, finiteMinimax X ω ∂μX) =
      ∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 SX := by
    calc
      (∫ ω, finiteMinimax X ω ∂μX) =
          ∫ ω, gordonVectorMinimax e (VX ω) ∂μX := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change finiteMinimax X ω = gordonVectorMinimax e
          (processEuclideanVector
            (fun k ↦ X (e.symm k).1 (e.symm k).2) ω)
        exact (gordonVectorMinimax_processEuclideanVector e X ω).symm
      _ = ∫ x, gordonVectorMinimax e x ∂νX := by
        exact (integral_map hVX.aemeasurable
          (continuous_gordonVectorMinimax e).aestronglyMeasurable).symm
      _ = ∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 SX := by
        rw [hlawX]
  have hobjY : (∫ ω, finiteMinimax Y ω ∂μY) =
      ∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 SY := by
    calc
      (∫ ω, finiteMinimax Y ω ∂μY) =
          ∫ ω, gordonVectorMinimax e (VY ω) ∂μY := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change finiteMinimax Y ω = gordonVectorMinimax e
          (processEuclideanVector
            (fun k ↦ Y (e.symm k).1 (e.symm k).2) ω)
        exact (gordonVectorMinimax_processEuclideanVector e Y ω).symm
      _ = ∫ x, gordonVectorMinimax e x ∂νY := by
        exact (integral_map hVY.aemeasurable
          (continuous_gordonVectorMinimax e).aestronglyMeasurable).symm
      _ = ∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 SY := by
        rw [hlawY]
  rw [hobjX, hobjY]
  let AX := ∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 SX
  let AY := ∫ x, gordonVectorMinimax e x ∂multivariateGaussian 0 SY
  by_contra hle
  have hdelta : 0 < AX - AY := sub_pos.mpr (lt_of_not_ge hle)
  let c := Real.log (Fintype.card U) + Real.log (Fintype.card T)
  have hc : 0 ≤ c := add_nonneg
    (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
    (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
  let τ := c / (AX - AY) + 1
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have herr : Real.log (Fintype.card U) / τ +
      Real.log (Fintype.card T) / τ < AX - AY := by
    have hmul : (AX - AY) * τ = c + (AX - AY) := by
      dsimp [τ]
      field_simp [hdelta.ne']
    rw [← add_div]
    apply (div_lt_iff₀ hτ).2
    dsimp [c] at hmul ⊢
    rw [hmul]
    linarith
  have hcomp := gordonSmoothMinimax_expectation_comparison
    e hτ hτ SX SY hSX hSY hmatrixWithin hmatrixAcross
  have hbX := integral_gordonSmoothMinimax_bounds e hτ hτ SX
  have hbY := integral_gordonSmoothMinimax_bounds e hτ hτ SY
  have hAXAY : AX ≤ AY + Real.log (Fintype.card U) / τ +
      Real.log (Fintype.card T) / τ := by
    dsimp [AX, AY]
    linarith [hbX.1, hcomp, hbY.2]
  linarith

/-- Defines coordinate evaluation as a continuous linear functional for the Gordon tail comparison.

**Lean implementation helper.** -/
private def gordonTailCoordCLM {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The Gordon tail coordinate functional evaluates the selected Euclidean coordinate.

**Lean implementation helper.** -/
private lemma gordonTailCoordCLM_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : gordonTailCoordCLM i x = x i := by
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x i

/-- Defines the exponential energy associated with one row and a threshold.

**Lean implementation helper.** -/
private def gordonTailRowEnergy
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ t, Real.exp (β * (x (e (u, t)) - a))

/-- Defines a smooth approximation to the event that a row maximum lies below the threshold.

**Lean implementation helper.** -/
private def gordonTailRowBelow
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-gordonTailRowEnergy e β a u x)

/-- Defines the complementary row factor appearing in the smoothed minimax tail event.

**Lean implementation helper.** -/
private def gordonTailRowFactor
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 - gordonTailRowBelow e β a u x

/-- Defines the product smoother for the Gordon minimax tail event.

**Lean implementation helper.** -/
private def gordonTailSmoother
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ u, gordonTailRowFactor e β a u x

/-- Defines a finite-parameter approximation to the Gordon tail smoother.

**Lean implementation helper.** -/
private def gordonTailSmootherApprox
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (τ : ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let m : ℝ := k + 1
  ∏ u, (1 - Real.exp
    (-∑ t, Real.exp ((x (e (u, t)) - τ) * m ^ 2 + m)))

/-- Expresses the tail smoother approximation as the exact smoother with explicit parameters.

**Lean implementation helper.** -/
private lemma gordonTailSmootherApprox_eq
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (τ : ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailSmootherApprox e τ k x =
      gordonTailSmoother e (((k : ℝ) + 1) ^ 2)
        (τ - 1 / ((k : ℝ) + 1)) x := by
  classical
  have hm : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold gordonTailSmootherApprox gordonTailSmoother
    gordonTailRowFactor gordonTailRowBelow gordonTailRowEnergy
  dsimp only
  apply Finset.prod_congr rfl
  intro u _
  apply congrArg (fun z : ℝ ↦ 1 - Real.exp (-z))
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg Real.exp
  field_simp [hm]
  ring

/-- The Gordon tail approximation exponent tends to negative infinity below the threshold.

**Lean implementation helper.** -/
private lemma gordonTail_exponent_atBot {d : ℝ} (hd : d < 0) :
    Tendsto (fun k : ℕ ↦
      let m : ℝ := k + 1
      d * m ^ 2 + m) atTop atBot := by
  let m : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  have hm : Tendsto m atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun k ↦ d * m k + 1) atTop atBot :=
    tendsto_atBot_add_const_right atTop 1 (hm.const_mul_atTop_of_neg hd)
  have hp := hm.atTop_mul_atBot₀ hg
  apply hp.congr'
  filter_upwards [] with k
  dsimp [m]
  ring

/-- The Gordon tail approximation exponent tends to positive infinity above the threshold.

**Lean implementation helper.** -/
private lemma gordonTail_exponent_atTop {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun k : ℕ ↦
      let m : ℝ := k + 1
      d * m ^ 2 + m) atTop atTop := by
  let m : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  have hm : Tendsto m atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun k ↦ by
      dsimp [m]
      nlinarith [sq_nonneg ((k : ℝ) + 1)]) hm

/-- Defines the finite-parameter approximation to a smoothed row-below-threshold indicator.

**Lean implementation helper.** -/
private def gordonTailRowBelowApprox
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (τ : ℝ) (k : ℕ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let m : ℝ := k + 1
  Real.exp (-∑ t, Real.exp ((x (e (u, t)) - τ) * m ^ 2 + m))

/-- The row-below-threshold approximation converges pointwise to its indicator.

**Lean implementation helper.** -/
private lemma gordonTailRowBelowApprox_pointwise
    {U T : Type*} [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (τ : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k ↦ gordonTailRowBelowApprox e τ k u x) atTop
      (nhds (Set.indicator
        {z : EuclideanSpace ℝ (Fin n) | ∀ t, z (e (u, t)) < τ}
        (fun _ ↦ (1 : ℝ)) x)) := by
  classical
  by_cases hall : ∀ t, x (e (u, t)) < τ
  · have hterm : ∀ t : T,
        Tendsto (fun k : ℕ ↦
          let m : ℝ := k + 1
          Real.exp ((x (e (u, t)) - τ) * m ^ 2 + m))
          atTop (nhds 0) := by
      intro t
      exact Real.tendsto_exp_atBot.comp
        (gordonTail_exponent_atBot (sub_neg.mpr (hall t)))
    have hsum : Tendsto (fun k : ℕ ↦
        let m : ℝ := k + 1
        ∑ t, Real.exp ((x (e (u, t)) - τ) * m ^ 2 + m))
        atTop (nhds 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun t _ ↦ hterm t)
    have hneg : Tendsto (fun k : ℕ ↦
        -(let m : ℝ := k + 1
          ∑ t, Real.exp ((x (e (u, t)) - τ) * m ^ 2 + m)))
        atTop (nhds 0) := by simpa using hsum.neg
    have hout := (Real.continuous_exp.tendsto 0).comp hneg
    have hind : Set.indicator
        {z : EuclideanSpace ℝ (Fin n) | ∀ t, z (e (u, t)) < τ}
        (fun _ ↦ (1 : ℝ)) x = 1 := by
      simp [hall]
    rw [hind]
    unfold gordonTailRowBelowApprox
    dsimp only
    change Tendsto (fun k : ℕ ↦
      Real.exp (-∑ t, Real.exp
        ((x (e (u, t)) - τ) * ((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1))))
      atTop (nhds (Real.exp 0)) at hout
    simpa only [Real.exp_zero] using hout
  · push Not at hall
    obtain ⟨t, ht⟩ := hall
    have hcomponent : Tendsto (fun k : ℕ ↦
        let m : ℝ := k + 1
        Real.exp ((x (e (u, t)) - τ) * m ^ 2 + m))
        atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (gordonTail_exponent_atTop (sub_nonneg.mpr ht))
    have hsum : Tendsto (fun k : ℕ ↦
        let m : ℝ := k + 1
        ∑ s, Real.exp ((x (e (u, s)) - τ) * m ^ 2 + m))
        atTop atTop := by
      apply tendsto_atTop_mono' atTop _ hcomponent
      exact Filter.Eventually.of_forall fun k ↦ by
        dsimp only
        exact Finset.single_le_sum
          (f := fun s ↦ Real.exp
            ((x (e (u, s)) - τ) * ((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1)))
          (fun s (_ : s ∈ (Finset.univ : Finset T)) ↦ Real.exp_nonneg _)
          (Finset.mem_univ t)
    have hout := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hsum)
    have hind : Set.indicator
        {z : EuclideanSpace ℝ (Fin n) | ∀ s, z (e (u, s)) < τ}
        (fun _ ↦ (1 : ℝ)) x = 0 := by
      simp only [indicator_apply_eq_zero, mem_setOf_eq, one_ne_zero,
        imp_false, not_forall, not_lt]
      exact ⟨t, ht⟩
    rw [hind]
    unfold gordonTailRowBelowApprox
    dsimp only
    exact hout

/-- The Gordon tail smoother approximation converges pointwise to the minimax tail indicator.

**Lean implementation helper.** -/
private lemma gordonTailSmootherApprox_pointwise
    {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k ↦ gordonTailSmootherApprox e τ k x) atTop
      (nhds (Set.indicator
        {z : EuclideanSpace ℝ (Fin n) |
          ∀ u, ∃ t, τ ≤ z (e (u, t))}
        (fun _ ↦ (1 : ℝ)) x)) := by
  classical
  have hrow : ∀ u : U, Tendsto
      (fun k ↦ 1 - gordonTailRowBelowApprox e τ k u x) atTop
      (nhds (1 - Set.indicator
        {z : EuclideanSpace ℝ (Fin n) | ∀ t, z (e (u, t)) < τ}
        (fun _ ↦ (1 : ℝ)) x)) := by
    intro u
    exact tendsto_const_nhds.sub
      (gordonTailRowBelowApprox_pointwise e τ u x)
  have hp := tendsto_finsetProd (Finset.univ : Finset U)
    (fun u _ ↦ hrow u)
  have hfun : (fun k ↦ gordonTailSmootherApprox e τ k x) =
      (fun k ↦ ∏ u ∈ (Finset.univ : Finset U),
        (1 - gordonTailRowBelowApprox e τ k u x)) := by
    funext k
    simp [gordonTailSmootherApprox, gordonTailRowBelowApprox]
  rw [hfun]
  convert hp using 1
  by_cases hA : ∀ u, ∃ t, τ ≤ x (e (u, t))
  · have hzero : ∀ u : U, Set.indicator
        {z : EuclideanSpace ℝ (Fin n) | ∀ t, z (e (u, t)) < τ}
        (fun _ ↦ (1 : ℝ)) x = 0 := by
      intro u
      obtain ⟨t, ht⟩ := hA u
      simp only [indicator_apply_eq_zero, mem_setOf_eq, one_ne_zero,
        imp_false, not_forall, not_lt]
      exact ⟨t, ht⟩
    have hmemA : x ∈ {z : EuclideanSpace ℝ (Fin n) |
        ∀ u, ∃ t, τ ≤ z (e (u, t))} := hA
    rw [Set.indicator_of_mem hmemA]
    simp [hzero]
  · push Not at hA
    obtain ⟨u, hu⟩ := hA
    have hall : ∀ t, x (e (u, t)) < τ := by
      intro t
      exact hu t
    have hmem : x ∈
        {z : EuclideanSpace ℝ (Fin n) | ∀ t, z (e (u, t)) < τ} := hall
    have hnotmem : x ∉ {z : EuclideanSpace ℝ (Fin n) |
        ∀ v, ∃ t, τ ≤ z (e (v, t))} := by
      intro h
      obtain ⟨t, ht⟩ := h u
      exact (not_le_of_gt (hu t)) ht
    rw [Set.indicator_of_notMem hnotmem]
    congr 1
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    rw [Set.indicator_of_mem hmem]
    simp

/-- The Gordon tail row below is nonnegative.

**Lean implementation helper.** -/
private lemma gordonTailRowBelow_nonneg
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ gordonTailRowBelow e β a u x := by
  unfold gordonTailRowBelow
  exact Real.exp_nonneg _

/-- The Gordon tail row below is at most one.

**Lean implementation helper.** -/
private lemma gordonTailRowBelow_le_one
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailRowBelow e β a u x ≤ 1 := by
  unfold gordonTailRowBelow gordonTailRowEnergy
  exact Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Finset.sum_nonneg fun _ _ ↦ Real.exp_nonneg _))

/-- Each complementary row factor lies in the unit interval.

**Lean implementation helper.** -/
private lemma gordonTailRowFactor_mem_Icc
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailRowFactor e β a u x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (gordonTailRowBelow_le_one e β a u x)
  · unfold gordonTailRowFactor
    linarith [gordonTailRowBelow_nonneg e β a u x]

/-- The product tail smoother lies in the unit interval.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_mem_Icc
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailSmoother e β a x ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold gordonTailSmoother
  constructor
  · exact Finset.prod_nonneg fun u _ ↦
      (gordonTailRowFactor_mem_Icc e β a u x).1
  · exact Finset.prod_le_one
      (fun u _ ↦ (gordonTailRowFactor_mem_Icc e β a u x).1)
      (fun u _ ↦ (gordonTailRowFactor_mem_Icc e β a u x).2)

/-- Defines the minimum of the row maxima used in Gordon's tail comparison.

**Lean implementation helper.** -/
private def gordonTailVectorMinimax
    {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun u ↦ Finset.univ.sup' Finset.univ_nonempty
      (fun t ↦ x (e (u, t))))

/-- The Gordon tail vector minimax is continuous.

**Lean implementation helper.** -/
private lemma continuous_gordonTailVectorMinimax
    {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) :
    Continuous (gordonTailVectorMinimax e) := by
  unfold gordonTailVectorMinimax
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun u _ ↦ Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun t _ ↦ by fun_prop))

/-- Identifies the minimax tail event with the event that every row maximum exceeds the threshold.

**Lean implementation helper.** -/
private lemma gordonTail_event_eq
    {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (τ : ℝ) :
    {x : EuclideanSpace ℝ (Fin n) | τ ≤ gordonTailVectorMinimax e x} =
      {x | ∀ u, ∃ t, τ ≤ x (e (u, t))} := by
  ext x
  unfold gordonTailVectorMinimax
  simp only [Set.mem_setOf_eq]
  rw [Finset.le_inf'_iff]
  constructor
  · intro h u
    have hu := h u (Finset.mem_univ u)
    obtain ⟨t, _, ht⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).mp hu
    exact ⟨t, ht⟩
  · rintro h u -
    obtain ⟨t, ht⟩ := h u
    exact (Finset.le_sup'_iff Finset.univ_nonempty).mpr
      ⟨t, Finset.mem_univ t, ht⟩

/-- The expectations of the tail smoother approximations converge to the minimax tail probability.

**Lean implementation helper.** -/
private lemma tendsto_integral_gordonTailSmootherApprox
    {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n) (S : Matrix (Fin n) (Fin n) ℝ) (τ : ℝ) :
    Tendsto (fun k ↦ ∫ x, gordonTailSmootherApprox e τ k x
      ∂multivariateGaussian 0 S) atTop
      (nhds ((multivariateGaussian 0 S).real
        {x | τ ≤ gordonTailVectorMinimax e x})) := by
  let A := {x : EuclideanSpace ℝ (Fin n) |
    ∀ u, ∃ t, τ ≤ x (e (u, t))}
  have hA : MeasurableSet A := by
    dsimp [A]
    rw [← gordonTail_event_eq e τ]
    exact (continuous_gordonTailVectorMinimax e).measurable measurableSet_Ici
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := multivariateGaussian 0 S)
    (F := fun k x ↦ gordonTailSmootherApprox e τ k x)
    (f := A.indicator fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun k ↦ (by unfold gordonTailSmootherApprox; fun_prop :
      Continuous (gordonTailSmootherApprox e τ k)).aestronglyMeasurable)
    (integrable_const_iff.2 (Or.inr inferInstance))
    (fun k ↦ Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact (show gordonTailSmootherApprox e τ k x ≤ 1 by
          rw [gordonTailSmootherApprox_eq]
          exact (gordonTailSmoother_mem_Icc e _ _ x).2)
      · rw [gordonTailSmootherApprox_eq]
        exact (gordonTailSmoother_mem_Icc e _ _ x).1)
    (Filter.Eventually.of_forall fun x ↦
      gordonTailSmootherApprox_pointwise e τ x)
  rw [gordonTail_event_eq e τ]
  convert hDCT using 1
  all_goals simp [A, integral_indicator_const
    (μ := multivariateGaussian 0 S) (1 : ℝ) hA]

/-! ### Calculus stack for the Gordon tail smoother -/

/-- Computes the Fréchet derivative of the Gordon tail row energy at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonTailRowEnergy
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gordonTailRowEnergy e β a u)
      (∑ t, Real.exp (β * (x (e (u, t)) - a)) •
        (β • gordonTailCoordCLM (e (u, t)))) x := by
  have hcomp : ∀ t : T, HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦
        Real.exp (β * (z (e (u, t)) - a)))
      (Real.exp (β * (x (e (u, t)) - a)) •
        (β • gordonTailCoordCLM (e (u, t)))) x := by
    intro t
    have hc : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) ↦ β * (z (e (u, t)) - a))
        (β • gordonTailCoordCLM (e (u, t))) x := by
      simpa [gordonTailCoordCLM_apply] using
        ((gordonTailCoordCLM (e (u, t))).hasFDerivAt.sub_const a).const_mul β
    simpa using hc.exp
  change HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦
    ∑ t, Real.exp (β * (z (e (u, t)) - a))) _ x
  exact HasFDerivAt.fun_sum (u := (Finset.univ : Finset T))
    (fun t _ ↦ hcomp t)

/-- Computes the Fréchet derivative of the Gordon tail row below at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonTailRowBelow
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gordonTailRowBelow e β a u)
      (gordonTailRowBelow e β a u x •
        (-(∑ t, Real.exp (β * (x (e (u, t)) - a)) •
          (β • gordonTailCoordCLM (e (u, t)))))) x := by
  unfold gordonTailRowBelow
  simpa using (hasFDerivAt_gordonTailRowEnergy e β a u x).neg.exp

/-- Computes the Fréchet derivative of the Gordon tail row factor at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonTailRowFactor
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gordonTailRowFactor e β a u)
      (gordonTailRowBelow e β a u x •
        (∑ t, Real.exp (β * (x (e (u, t)) - a)) •
          (β • gordonTailCoordCLM (e (u, t))))) x := by
  change HasFDerivAt
    ((fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ)) -
      gordonTailRowBelow e β a u) _ x
  have h := (hasFDerivAt_const (x := x) (c := (1 : ℝ))).sub
    (hasFDerivAt_gordonTailRowBelow e β a u x)
  refine h.congr_fderiv ?_
  ext z
  simp only [_root_.sub_apply, _root_.smul_apply, _root_.zero_apply,
    _root_.neg_apply, _root_.sum_apply, smul_eq_mul]
  ring_nf
  apply congrArg (fun r : ℝ ↦ gordonTailRowBelow e β a u x * r)
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun r : ℝ ↦ β * r * gordonTailCoordCLM (e (u, t)) z)
  apply congrArg Real.exp
  ring

/-- Computes the coordinate derivative of a complementary row factor.

**Lean implementation helper.** -/
private lemma fderiv_gordonTailRowFactor_basis
    {U T : Type*} [Fintype T] [DecidableEq U] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) (p : U × T) :
    fderiv ℝ (gordonTailRowFactor e β a u) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e p)) =
      if p.1 = u then
        β * Real.exp (β * (x (e p) - a)) *
          gordonTailRowBelow e β a u x
      else 0 := by
  classical
  rw [(hasFDerivAt_gordonTailRowFactor e β a u x).fderiv]
  by_cases hpu : p.1 = u
  · subst u
    simp [gordonTailCoordCLM_apply, e.injective.eq_iff, Prod.ext_iff]
    ring
  · simp [gordonTailCoordCLM_apply, e.injective.eq_iff, Prod.ext_iff, hpu]

/-- The Gordon tail smoother is twice continuously differentiable.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_contDiff
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) :
    ContDiff ℝ 2 (gordonTailSmoother e β a) := by
  unfold gordonTailSmoother gordonTailRowFactor gordonTailRowBelow
    gordonTailRowEnergy
  fun_prop

/-- Defines one exponential coordinate contribution to a row energy.

**Lean implementation helper.** -/
private def gordonTailAtom
    {U T : Type*} {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p : U × T)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (β * (x (e p) - a))

/-- Defines the product of all row factors except a selected row.

**Lean implementation helper.** -/
private def gordonTailFactorProduct
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (A : Finset U)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ u ∈ A, gordonTailRowFactor e β a u x

/-- Computes the Fréchet derivative of the Gordon tail atom at an arbitrary point.

**Lean implementation helper.** -/
private lemma hasFDerivAt_gordonTailAtom
    {U T : Type*} {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p : U × T)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gordonTailAtom e β a p)
      (gordonTailAtom e β a p x • (β • gordonTailCoordCLM (e p))) x := by
  have hc : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ β * (z (e p) - a))
      (β • gordonTailCoordCLM (e p)) x := by
    simpa [gordonTailCoordCLM_apply] using
      ((gordonTailCoordCLM (e p)).hasFDerivAt.sub_const a).const_mul β
  change HasFDerivAt
    (fun z : EuclideanSpace ℝ (Fin n) ↦ Real.exp (β * (z (e p) - a)))
    (Real.exp (β * (x (e p) - a)) •
      (β • gordonTailCoordCLM (e p))) x
  exact hc.exp

/-- Computes the coordinate derivative of a single Gordon tail atom.

**Lean implementation helper.** -/
private lemma fderiv_gordonTailAtom_basis
    {U T : Type*} [DecidableEq U] [DecidableEq T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p q : U × T)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (gordonTailAtom e β a p) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e q)) =
      if q = p then β * gordonTailAtom e β a p x else 0 := by
  rw [(hasFDerivAt_gordonTailAtom e β a p x).fderiv]
  by_cases hqp : q = p
  · subst q
    simp [gordonTailCoordCLM_apply]
    ring
  · have hep : e q ≠ e p := fun h ↦ hqp (e.injective h)
    simp [gordonTailCoordCLM_apply, hqp, hep]

/-- Computes the coordinate derivative of the smoothed row-below-threshold function.

**Lean implementation helper.** -/
private lemma fderiv_gordonTailRowBelow_basis
    {U T : Type*} [Fintype T] [DecidableEq U] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (u : U)
    (x : EuclideanSpace ℝ (Fin n)) (p : U × T) :
    fderiv ℝ (gordonTailRowBelow e β a u) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e p)) =
      if p.1 = u then
        -β * gordonTailAtom e β a p x * gordonTailRowBelow e β a u x
      else 0 := by
  classical
  rw [(hasFDerivAt_gordonTailRowBelow e β a u x).fderiv]
  by_cases hpu : p.1 = u
  · subst u
    simp [gordonTailCoordCLM_apply, gordonTailAtom,
      e.injective.eq_iff, Prod.ext_iff]
    ring
  · simp [gordonTailCoordCLM_apply, e.injective.eq_iff, Prod.ext_iff, hpu]

/-- Computes the coordinate derivative of the product of all other row factors.

**Lean implementation helper.** -/
private lemma fderiv_gordonTailFactorProduct_basis
    {U T : Type*} [Fintype T] [DecidableEq U] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (A : Finset U)
    (x : EuclideanSpace ℝ (Fin n)) (p : U × T) :
    fderiv ℝ (gordonTailFactorProduct e β a A) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e p)) =
      if p.1 ∈ A then
        β * gordonTailAtom e β a p x *
          gordonTailRowBelow e β a p.1 x *
          (∏ w ∈ A.erase p.1, gordonTailRowFactor e β a w x)
      else 0 := by
  classical
  unfold gordonTailFactorProduct
  rw [fderiv_finsetProd]
  · simp only [_root_.sum_apply, _root_.smul_apply,
      smul_eq_mul]
    by_cases hpA : p.1 ∈ A
    · rw [Finset.sum_eq_single p.1]
      · rw [fderiv_gordonTailRowFactor_basis]
        simp [hpA, gordonTailAtom]
        ring
      · intro b _ hbp
        rw [fderiv_gordonTailRowFactor_basis]
        simp [Ne.symm hbp]
      · exact fun hpnot ↦ (hpnot hpA).elim
    · have hzero : ∀ b ∈ A,
          fderiv ℝ (gordonTailRowFactor e β a b) x
              (EuclideanSpace.basisFun (Fin n) ℝ (e p)) = 0 := by
        intro b hb
        have hne : p.1 ≠ b := fun h ↦ hpA (h.symm ▸ hb)
        rw [fderiv_gordonTailRowFactor_basis]
        simp [hne]
      rw [Finset.sum_eq_zero]
      · simp [hpA]
      · intro b hb
        rw [hzero b hb, mul_zero]
  · intro u hu
    exact (hasFDerivAt_gordonTailRowFactor e β a u x).differentiableAt

/-- Defines a first coordinate partial derivative of the Gordon tail smoother.

**Lean implementation helper.** -/
private def gordonTailFirstPartial
    {U T : Type*} [Fintype U] [Fintype T] [DecidableEq U] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p : U × T)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  β * gordonTailAtom e β a p x *
    gordonTailRowBelow e β a p.1 x *
    gordonTailFactorProduct e β a (Finset.univ.erase p.1) x

/-- Computes a coordinate derivative of the full Gordon tail smoother.

**Lean implementation helper.** -/
private lemma fderiv_gordonTailSmoother_basis
    {U T : Type*} [Fintype U] [Fintype T]
    [DecidableEq U] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p : U × T) :
    fderiv ℝ (gordonTailSmoother e β a) x
        (EuclideanSpace.basisFun (Fin n) ℝ (e p)) =
      gordonTailFirstPartial e β a p x := by
  classical
  have hfun : gordonTailSmoother e β a =
      gordonTailFactorProduct e β a Finset.univ := by
    funext z
    simp [gordonTailSmoother, gordonTailFactorProduct]
  rw [hfun, fderiv_gordonTailFactorProduct_basis]
  simp [gordonTailFirstPartial, gordonTailFactorProduct]

/-- Computes each Hessian entry of the Gordon tail smoother.

**Lean implementation helper.** -/
private lemma gaussianHessianEntry_gordonTailSmoother
    {U T : Type*} [Fintype U] [Fintype T]
    [DecidableEq U] [DecidableEq T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p q : U × T) :
    gaussianHessianEntry (gordonTailSmoother e β a) (e p) (e q) x =
      if p.1 = q.1 then
        β ^ 2 * gordonTailAtom e β a q x *
          gordonTailRowBelow e β a q.1 x *
          ((if p = q then 1 else 0) - gordonTailAtom e β a p x) *
          gordonTailFactorProduct e β a (Finset.univ.erase q.1) x
      else
        β ^ 2 * gordonTailAtom e β a q x *
          gordonTailRowBelow e β a q.1 x *
          gordonTailAtom e β a p x *
          gordonTailRowBelow e β a p.1 x *
          gordonTailFactorProduct e β a
            ((Finset.univ.erase q.1).erase p.1) x := by
  classical
  let bq := EuclideanSpace.basisFun (Fin n) ℝ (e q)
  let bp := EuclideanSpace.basisFun (Fin n) ℝ (e p)
  have hCD := gordonTailSmoother_contDiff e β a
  have hDc : DifferentiableAt ℝ
      (fderiv ℝ (gordonTailSmoother e β a)) x :=
    (hCD.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hlink : gaussianHessianEntry (gordonTailSmoother e β a) (e p) (e q) x =
      fderiv ℝ (fun z ↦ fderiv ℝ (gordonTailSmoother e β a) z bq) x bp := by
    unfold gaussianHessianEntry
    rw [fderiv_clm_apply hDc (differentiableAt_const bq)]
    simp [bp, bq]
  rw [hlink]
  have hfun : (fun z ↦ fderiv ℝ (gordonTailSmoother e β a) z bq) =
      gordonTailFirstPartial e β a q := by
    funext z
    exact fderiv_gordonTailSmoother_basis e β a z q
  rw [hfun]
  have hA : HasFDerivAt (gordonTailAtom e β a q)
      (fderiv ℝ (gordonTailAtom e β a q) x) x :=
    (hasFDerivAt_gordonTailAtom e β a q x).differentiableAt.hasFDerivAt
  have hQ : HasFDerivAt (gordonTailRowBelow e β a q.1)
      (fderiv ℝ (gordonTailRowBelow e β a q.1) x) x :=
    (hasFDerivAt_gordonTailRowBelow e β a q.1 x).differentiableAt.hasFDerivAt
  have hP : HasFDerivAt
      (gordonTailFactorProduct e β a (Finset.univ.erase q.1))
      (fderiv ℝ (gordonTailFactorProduct e β a (Finset.univ.erase q.1)) x) x :=
    (by
      unfold gordonTailFactorProduct
      exact (HasFDerivAt.finsetProd
        (u := Finset.univ.erase q.1)
        (fun u _ ↦ hasFDerivAt_gordonTailRowFactor e β a u x)).differentiableAt
      : DifferentiableAt ℝ
        (gordonTailFactorProduct e β a (Finset.univ.erase q.1)) x).hasFDerivAt
  have hderiv := ((hA.mul hQ).mul hP).const_mul β
  have hassoc : gordonTailFirstPartial e β a q =
      (fun z ↦ β * ((gordonTailAtom e β a q z *
        gordonTailRowBelow e β a q.1 z) *
        gordonTailFactorProduct e β a (Finset.univ.erase q.1) z)) := by
    funext z
    simp [gordonTailFirstPartial]
    ring
  have hderiv' : HasFDerivAt
      (fun z ↦ β * ((gordonTailAtom e β a q z *
        gordonTailRowBelow e β a q.1 z) *
        gordonTailFactorProduct e β a (Finset.univ.erase q.1) z))
      _ x :=
    hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by
      simp only [Pi.mul_apply])
  rw [hassoc, hderiv'.fderiv]
  simp only [_root_.smul_apply, _root_.add_apply,
    smul_eq_mul]
  rw [fderiv_gordonTailFactorProduct_basis]
  simp only [Finset.mem_erase, Finset.mem_univ]
  by_cases hpqrow : p.1 = q.1
  · simp only [Pi.mul_apply, ne_eq, and_true, ite_not, mul_ite, mul_zero]
    rw [fderiv_gordonTailAtom_basis, fderiv_gordonTailRowBelow_basis]
    by_cases hpq : p = q <;> simp [hpq, hpqrow] <;> ring_nf
  · simp only [Pi.mul_apply, ne_eq, and_true, ite_not, mul_ite, mul_zero]
    rw [fderiv_gordonTailAtom_basis, fderiv_gordonTailRowBelow_basis]
    have hpq : p ≠ q := fun h ↦ hpqrow (congrArg Prod.fst h)
    simp only [hpq, hpqrow, if_false, neg_mul, mul_zero]
    unfold gordonTailFactorProduct
    ring

/-- Distinct coordinates in the same row give a nonpositive Hessian entry of the Gordon tail smoother.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_hessian_sameRow_nonpos
    {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p q : U × T)
    (hrow : p.1 = q.1) (hpq : p ≠ q) :
    gaussianHessianEntry (gordonTailSmoother e β a) (e p) (e q) x ≤ 0 := by
  classical
  rw [gaussianHessianEntry_gordonTailSmoother e β a x p q, if_pos hrow,
    if_neg hpq, zero_sub]
  have hprod : 0 ≤ gordonTailFactorProduct e β a
      (Finset.univ.erase q.1) x := by
    unfold gordonTailFactorProduct
    exact Finset.prod_nonneg fun u _ ↦
      (gordonTailRowFactor_mem_Icc e β a u x).1
  rw [show β ^ 2 * gordonTailAtom e β a q x *
      gordonTailRowBelow e β a q.1 x *
      -gordonTailAtom e β a p x *
      gordonTailFactorProduct e β a (Finset.univ.erase q.1) x =
      -(β ^ 2 * gordonTailAtom e β a q x *
        gordonTailRowBelow e β a q.1 x *
        gordonTailAtom e β a p x *
        gordonTailFactorProduct e β a (Finset.univ.erase q.1) x) by ring]
  have hAq : 0 ≤ gordonTailAtom e β a q x := by
    unfold gordonTailAtom; exact Real.exp_nonneg _
  have hAp : 0 ≤ gordonTailAtom e β a p x := by
    unfold gordonTailAtom; exact Real.exp_nonneg _
  have hQ : 0 ≤ gordonTailRowBelow e β a q.1 x :=
    gordonTailRowBelow_nonneg e β a q.1 x
  apply neg_nonpos.mpr
  positivity

/-- Coordinates in different rows give a nonnegative Hessian entry of the Gordon tail smoother.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_hessian_differentRow_nonneg
    {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p q : U × T)
    (hrow : p.1 ≠ q.1) :
    0 ≤ gaussianHessianEntry (gordonTailSmoother e β a) (e p) (e q) x := by
  classical
  rw [gaussianHessianEntry_gordonTailSmoother e β a x p q, if_neg hrow]
  have hprod : 0 ≤ gordonTailFactorProduct e β a
      ((Finset.univ.erase q.1).erase p.1) x := by
    unfold gordonTailFactorProduct
    exact Finset.prod_nonneg fun u _ ↦
      (gordonTailRowFactor_mem_Icc e β a u x).1
  have hAq : 0 ≤ gordonTailAtom e β a q x := by
    unfold gordonTailAtom; exact Real.exp_nonneg _
  have hAp : 0 ≤ gordonTailAtom e β a p x := by
    unfold gordonTailAtom; exact Real.exp_nonneg _
  have hQ : 0 ≤ gordonTailRowBelow e β a q.1 x :=
    gordonTailRowBelow_nonneg e β a q.1 x
  have hP : 0 ≤ gordonTailRowBelow e β a p.1 x :=
    gordonTailRowBelow_nonneg e β a p.1 x
  positivity

/-- The squared Gordon tail energy times its negative exponential is at most four.

**Lean implementation helper.** -/
private lemma gordonTail_sq_mul_exp_neg_le_four (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 4 := by
  let u := t / 2
  have hu : 0 ≤ u := div_nonneg ht (by norm_num)
  have hsmall : u * Real.exp (-u) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one u).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hsmall0 : 0 ≤ u * Real.exp (-u) :=
    mul_nonneg hu (Real.exp_nonneg _)
  have hsq : (u * Real.exp (-u)) ^ 2 ≤ 1 := by nlinarith
  have hexp : Real.exp (-t) = Real.exp (-u) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  rw [hexp]
  dsimp [u] at hsq ⊢
  nlinarith

/-- Each Gordon tail atom is bounded by its row energy.

**Lean implementation helper.** -/
private lemma gordonTailAtom_le_rowEnergy
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p : U × T)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailAtom e β a p x ≤ gordonTailRowEnergy e β a p.1 x := by
  unfold gordonTailAtom gordonTailRowEnergy
  exact Finset.single_le_sum
    (f := fun t ↦ Real.exp (β * (x (e (p.1, t)) - a)))
    (fun t (_ : t ∈ (Finset.univ : Finset T)) ↦ Real.exp_nonneg _)
    (Finset.mem_univ p.2)

/-- A tail atom times the row-below smoother is at most one.

**Lean implementation helper.** -/
private lemma gordonTailAtom_mul_rowBelow_le_one
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p : U × T)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailAtom e β a p x *
        gordonTailRowBelow e β a p.1 x ≤ 1 := by
  let y := β * (x (e p) - a)
  have hy : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hyE : y ≤ gordonTailRowEnergy e β a p.1 x :=
    hy.trans (by simpa [y, gordonTailAtom] using
      gordonTailAtom_le_rowEnergy e β a p x)
  rw [gordonTailAtom, gordonTailRowBelow, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by dsimp [y] at hyE ⊢; linarith)

/-- Two tail atoms times the row-below smoother are at most four.

**Lean implementation helper.** -/
private lemma gordonTailTwoAtoms_mul_rowBelow_le_four
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (p q : U × T)
    (hrow : p.1 = q.1) (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailAtom e β a p x * gordonTailAtom e β a q x *
        gordonTailRowBelow e β a p.1 x ≤ 4 := by
  classical
  have hqeq : (p.1, q.2) = q := Prod.ext hrow rfl
  let tp := gordonTailAtom e β a p x
  let tq := gordonTailAtom e β a q x
  let E := gordonTailRowEnergy e β a p.1 x
  have hp0 : 0 ≤ tp := by dsimp [tp, gordonTailAtom]; positivity
  have hq0 : 0 ≤ tq := by dsimp [tq, gordonTailAtom]; positivity
  by_cases hpq : p = q
  · subst q
    have hpE : tp ≤ E := by
      simpa [tp, E] using gordonTailAtom_le_rowEnergy e β a p x
    have hexp : Real.exp (-E) ≤ Real.exp (-tp) :=
      Real.exp_le_exp.mpr (neg_le_neg hpE)
    calc
      gordonTailAtom e β a p x * gordonTailAtom e β a p x *
          gordonTailRowBelow e β a p.1 x = tp ^ 2 * Real.exp (-E) := by
        simp [tp, E, gordonTailRowBelow, pow_two]
      _ ≤ tp ^ 2 * Real.exp (-tp) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg tp)
      _ ≤ 4 := gordonTail_sq_mul_exp_neg_le_four tp hp0
  · have hne : p.2 ≠ q.2 := fun h ↦ hpq (Prod.ext hrow h)
    let s := tp + tq
    have hs0 : 0 ≤ s := add_nonneg hp0 hq0
    have hsE : s ≤ E := by
      dsimp [s, tp, tq, E, gordonTailAtom, gordonTailRowEnergy]
      calc
        Real.exp (β * (x (e p) - a)) + Real.exp (β * (x (e q) - a)) =
            ∑ t ∈ ({p.2, q.2} : Finset T),
              Real.exp (β * (x (e (p.1, t)) - a)) := by
          simp [hne, hqeq]
        _ ≤ ∑ t, Real.exp (β * (x (e (p.1, t)) - a)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun _ _ _ ↦ Real.exp_nonneg _)
    have hexp : Real.exp (-E) ≤ Real.exp (-s) :=
      Real.exp_le_exp.mpr (neg_le_neg hsE)
    calc
      gordonTailAtom e β a p x * gordonTailAtom e β a q x *
          gordonTailRowBelow e β a p.1 x = tp * tq * Real.exp (-E) := by
        simp [tp, tq, E, gordonTailRowBelow]
      _ ≤ s ^ 2 * Real.exp (-E) := by
        gcongr
        nlinarith [sq_nonneg (tp - tq)]
      _ ≤ s ^ 2 * Real.exp (-s) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg s)
      _ ≤ 4 := gordonTail_sq_mul_exp_neg_le_four s hs0

/-- The product of the complementary row factors lies in the unit interval.

**Lean implementation helper.** -/
private lemma gordonTailFactorProduct_mem_Icc
    {U T : Type*} [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) (A : Finset U)
    (x : EuclideanSpace ℝ (Fin n)) :
    gordonTailFactorProduct e β a A x ∈ Icc (0 : ℝ) 1 := by
  unfold gordonTailFactorProduct
  constructor
  · exact Finset.prod_nonneg fun u _ ↦
      (gordonTailRowFactor_mem_Icc e β a u x).1
  · exact Finset.prod_le_one
      (fun u _ ↦ (gordonTailRowFactor_mem_Icc e β a u x).1)
      (fun u _ ↦ (gordonTailRowFactor_mem_Icc e β a u x).2)

/-- The Gordon tail smoother is uniformly bounded in absolute value.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_value_bound
    {U T : Type*} [Fintype U] [Fintype T] {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) :
    ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖gordonTailSmoother e β a x‖ ≤ C := by
  refine ⟨1, fun x ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (gordonTailSmoother_mem_Icc e β a x).1]
  exact (gordonTailSmoother_mem_Icc e β a x).2

/-- Every coordinate derivative of the Gordon tail smoother admits a uniform bound.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_coordinate_derivative_bound
    {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) :
    ∀ i, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (gordonTailSmoother e β a) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ C := by
  classical
  intro i
  let p := e.symm i
  refine ⟨|β|, fun x ↦ ?_⟩
  have hei : e p = i := e.apply_symm_apply i
  rw [← hei, fderiv_gordonTailSmoother_basis]
  rw [gordonTailFirstPartial, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ gordonTailAtom e β a p x by
      unfold gordonTailAtom; positivity),
    abs_of_nonneg (gordonTailRowBelow_nonneg e β a p.1 x),
    abs_of_nonneg (gordonTailFactorProduct_mem_Icc e β a _ x).1]
  calc
    |β| * gordonTailAtom e β a p x *
        gordonTailRowBelow e β a p.1 x *
        gordonTailFactorProduct e β a (Finset.univ.erase p.1) x ≤
      |β| * 1 * 1 := by
        rw [show |β| * gordonTailAtom e β a p x *
            gordonTailRowBelow e β a p.1 x *
            gordonTailFactorProduct e β a (Finset.univ.erase p.1) x =
            |β| * (gordonTailAtom e β a p x *
              gordonTailRowBelow e β a p.1 x) *
              gordonTailFactorProduct e β a (Finset.univ.erase p.1) x by ring]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (gordonTailAtom_mul_rowBelow_le_one e β a p x) (abs_nonneg β))
          (gordonTailFactorProduct_mem_Icc e β a _ x).2
          (gordonTailFactorProduct_mem_Icc e β a _ x).1
          (by positivity)
    _ = |β| := by ring

/-- Every Hessian entry of the Gordon tail smoother admits a uniform bound.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_hessian_bound
    {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ}
    (e : U × T ≃ Fin n) (β a : ℝ) :
    ∀ i j, ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖gaussianHessianEntry (gordonTailSmoother e β a) i j x‖ ≤ C := by
  classical
  intro i j
  let p := e.symm i
  let q := e.symm j
  refine ⟨5 * β ^ 2, fun x ↦ ?_⟩
  have hei : e p = i := e.apply_symm_apply i
  have hej : e q = j := e.apply_symm_apply j
  rw [← hei, ← hej, gaussianHessianEntry_gordonTailSmoother]
  by_cases hrow : p.1 = q.1
  · rw [if_pos hrow]
    by_cases hpq : p = q
    · rw [if_pos hpq]
      rw [← hpq]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg β),
        abs_of_nonneg (show 0 ≤ gordonTailAtom e β a p x by
          unfold gordonTailAtom; positivity),
        abs_of_nonneg (gordonTailRowBelow_nonneg e β a p.1 x),
        abs_of_nonneg (gordonTailFactorProduct_mem_Icc e β a _ x).1]
      have hq := gordonTailAtom_mul_rowBelow_le_one e β a p x
      have hqq := gordonTailTwoAtoms_mul_rowBelow_le_four e β a p p rfl x
      have hP := (gordonTailFactorProduct_mem_Icc e β a
        (Finset.univ.erase p.1) x).2
      calc
        β ^ 2 * gordonTailAtom e β a p x *
            gordonTailRowBelow e β a p.1 x *
            |1 - gordonTailAtom e β a p x| *
            gordonTailFactorProduct e β a (Finset.univ.erase p.1) x ≤
          β ^ 2 * 5 * 1 := by
            have habs : gordonTailAtom e β a p x *
                gordonTailRowBelow e β a p.1 x *
                |1 - gordonTailAtom e β a p x| ≤ 5 := by
              calc
                _ ≤ gordonTailAtom e β a p x *
                    gordonTailRowBelow e β a p.1 x *
                    (1 + gordonTailAtom e β a p x) := by
                  apply mul_le_mul_of_nonneg_left
                  · apply abs_le.mpr
                    constructor
                    · have hA : 0 ≤ gordonTailAtom e β a p x := by
                        unfold gordonTailAtom; exact Real.exp_nonneg _
                      linarith
                    · have hA : 0 ≤ gordonTailAtom e β a p x := by
                        unfold gordonTailAtom; exact Real.exp_nonneg _
                      linarith
                  · exact mul_nonneg
                      (by unfold gordonTailAtom; exact Real.exp_nonneg _)
                      (gordonTailRowBelow_nonneg e β a p.1 x)
                _ = (gordonTailAtom e β a p x *
                      gordonTailRowBelow e β a p.1 x) +
                    (gordonTailAtom e β a p x *
                      gordonTailAtom e β a p x *
                      gordonTailRowBelow e β a p.1 x) := by ring
                _ ≤ 1 + 4 := add_le_add hq hqq
                _ = 5 := by norm_num
            rw [show β ^ 2 * gordonTailAtom e β a p x *
                gordonTailRowBelow e β a p.1 x *
                |1 - gordonTailAtom e β a p x| *
                gordonTailFactorProduct e β a (Finset.univ.erase p.1) x =
              β ^ 2 * (gordonTailAtom e β a p x *
                gordonTailRowBelow e β a p.1 x *
                |1 - gordonTailAtom e β a p x|) *
                gordonTailFactorProduct e β a (Finset.univ.erase p.1) x by ring]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left habs (sq_nonneg β)) hP
              (gordonTailFactorProduct_mem_Icc e β a _ x).1
              (by positivity)
        _ = 5 * β ^ 2 := by ring
    · rw [if_neg hpq, zero_sub, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg β),
        abs_of_nonneg (show 0 ≤ gordonTailAtom e β a q x by
          unfold gordonTailAtom; positivity),
        abs_of_nonneg (gordonTailRowBelow_nonneg e β a q.1 x),
        abs_of_nonneg (show 0 ≤ gordonTailAtom e β a p x by
          unfold gordonTailAtom; positivity),
        abs_of_nonneg (gordonTailFactorProduct_mem_Icc e β a _ x).1]
      have htwo := gordonTailTwoAtoms_mul_rowBelow_le_four e β a q p hrow.symm x
      have hP := (gordonTailFactorProduct_mem_Icc e β a
        (Finset.univ.erase q.1) x).2
      calc
        β ^ 2 * gordonTailAtom e β a q x *
            gordonTailRowBelow e β a q.1 x *
            gordonTailAtom e β a p x *
            gordonTailFactorProduct e β a (Finset.univ.erase q.1) x ≤
          β ^ 2 * 4 * 1 := by
            rw [show β ^ 2 * gordonTailAtom e β a q x *
                gordonTailRowBelow e β a q.1 x *
                gordonTailAtom e β a p x *
                gordonTailFactorProduct e β a (Finset.univ.erase q.1) x =
              β ^ 2 * (gordonTailAtom e β a q x *
                gordonTailAtom e β a p x *
                gordonTailRowBelow e β a q.1 x) *
                gordonTailFactorProduct e β a (Finset.univ.erase q.1) x by ring]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left htwo (sq_nonneg β)) hP
              (gordonTailFactorProduct_mem_Icc e β a _ x).1
              (by positivity)
        _ ≤ 5 * β ^ 2 := by nlinarith [sq_nonneg β]
  · rw [if_neg hrow, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_mul, abs_of_nonneg (sq_nonneg β),
      abs_of_nonneg (show 0 ≤ gordonTailAtom e β a q x by
        unfold gordonTailAtom; positivity),
      abs_of_nonneg (gordonTailRowBelow_nonneg e β a q.1 x),
      abs_of_nonneg (show 0 ≤ gordonTailAtom e β a p x by
        unfold gordonTailAtom; positivity),
      abs_of_nonneg (gordonTailRowBelow_nonneg e β a p.1 x),
      abs_of_nonneg (gordonTailFactorProduct_mem_Icc e β a _ x).1]
    have hq := gordonTailAtom_mul_rowBelow_le_one e β a q x
    have hp := gordonTailAtom_mul_rowBelow_le_one e β a p x
    have hP := (gordonTailFactorProduct_mem_Icc e β a
      ((Finset.univ.erase q.1).erase p.1) x).2
    calc
      β ^ 2 * gordonTailAtom e β a q x *
          gordonTailRowBelow e β a q.1 x *
          gordonTailAtom e β a p x *
          gordonTailRowBelow e β a p.1 x *
          gordonTailFactorProduct e β a
            ((Finset.univ.erase q.1).erase p.1) x ≤
        β ^ 2 * 1 * 1 * 1 := by
          rw [show β ^ 2 * gordonTailAtom e β a q x *
              gordonTailRowBelow e β a q.1 x *
              gordonTailAtom e β a p x *
              gordonTailRowBelow e β a p.1 x *
              gordonTailFactorProduct e β a
                ((Finset.univ.erase q.1).erase p.1) x =
            β ^ 2 * (gordonTailAtom e β a q x *
              gordonTailRowBelow e β a q.1 x) *
              (gordonTailAtom e β a p x *
                gordonTailRowBelow e β a p.1 x) *
              gordonTailFactorProduct e β a
                ((Finset.univ.erase q.1).erase p.1) x by ring]
          have hfirst : β ^ 2 * (gordonTailAtom e β a q x *
              gordonTailRowBelow e β a q.1 x) ≤ β ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hq (sq_nonneg β)
          have hsecond : β ^ 2 * (gordonTailAtom e β a q x *
                gordonTailRowBelow e β a q.1 x) *
                (gordonTailAtom e β a p x *
                  gordonTailRowBelow e β a p.1 x) ≤
              β ^ 2 * 1 * 1 :=
            mul_le_mul hfirst hp
              (mul_nonneg
                (by unfold gordonTailAtom; exact Real.exp_nonneg _)
                (gordonTailRowBelow_nonneg e β a p.1 x))
              (mul_nonneg (sq_nonneg β) (by norm_num))
          exact mul_le_mul hsecond hP
            (gordonTailFactorProduct_mem_Icc e β a _ x).1
            (by positivity)
      _ ≤ 5 * β ^ 2 := by nlinarith [sq_nonneg β]

/-- Orders expected Gordon tail smoothers under the classified Gaussian increment assumptions.

**Lean implementation helper.** -/
private lemma gordonTailSmoother_expectation_comparison
    {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ}
    (e : U × T ≃ Fin n)
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hdiag : ∀ p : U × T, SX (e p) (e p) = SY (e p) (e p))
    (hwithin : ∀ p q : U × T, p.1 = q.1 → p ≠ q →
      SY (e p) (e q) ≤ SX (e p) (e q))
    (hacross : ∀ p q : U × T, p.1 ≠ q.1 →
      SX (e p) (e q) ≤ SY (e p) (e q))
    (β a : ℝ) :
    (∫ x, gordonTailSmoother e β a x ∂multivariateGaussian 0 SX) ≤
      ∫ x, gordonTailSmoother e β a x ∂multivariateGaussian 0 SY := by
  classical
  apply gaussianInterpolationExpectation_le_of_hessianSum_nonneg_coordinate
    SY SX hSY hSX (gordonTailSmoother e β a)
      (gordonTailSmoother_contDiff e β a)
      (gordonTailSmoother_value_bound e β a)
      (gordonTailSmoother_coordinate_derivative_bound e β a)
      (gordonTailSmoother_hessian_bound e β a)
  intro _ _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  let p := e.symm i
  let q := e.symm j
  have hei : e p = i := e.apply_symm_apply i
  have hej : e q = j := e.apply_symm_apply j
  by_cases hij : i = j
  · have hpq : p = q := by
      apply e.injective
      calc
        e p = i := hei
        _ = j := hij
        _ = e q := hej.symm
    have hcoeff : SY i j - SX i j = 0 := by
      rw [← hei, ← hej, hpq, hdiag q]
      ring
    simp [hcoeff]
  · have hpq : p ≠ q := by
      intro h
      apply hij
      calc
        i = e p := hei.symm
        _ = e q := congrArg e h
        _ = j := hej
    by_cases hrow : p.1 = q.1
    · have hcoeff : SY i j - SX i j ≤ 0 := by
        rw [← hei, ← hej]
        exact sub_nonpos.mpr (hwithin p q hrow hpq)
      apply mul_nonneg_of_nonpos_of_nonpos hcoeff
      apply integral_nonpos_of_ae
      filter_upwards [] with z
      rw [← hei, ← hej]
      exact gordonTailSmoother_hessian_sameRow_nonpos
        e β a _ p q hrow hpq
    · have hcoeff : 0 ≤ SY i j - SX i j := by
        rw [← hei, ← hej]
        exact sub_nonneg.mpr (hacross p q hrow)
      apply mul_nonneg hcoeff
      apply integral_nonneg_of_ae
      filter_upwards [] with z
      rw [← hei, ← hej]
      exact gordonTailSmoother_hessian_differentRow_nonneg
        e β a _ p q hrow

/-- Transfers the Gaussian comparison inequality to the finite-parameter Gordon tail smoother.

**Lean implementation helper.** -/
private lemma gordonTailSmootherApprox_expectation_comparison
    {U T : Type*} [Fintype U] [Fintype T]
    {n : ℕ}
    (e : U × T ≃ Fin n)
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hdiag : ∀ p : U × T, SX (e p) (e p) = SY (e p) (e p))
    (hwithin : ∀ p q : U × T, p.1 = q.1 → p ≠ q →
      SY (e p) (e q) ≤ SX (e p) (e q))
    (hacross : ∀ p q : U × T, p.1 ≠ q.1 →
      SX (e p) (e q) ≤ SY (e p) (e q))
    (τ : ℝ) (k : ℕ) :
    (∫ x, gordonTailSmootherApprox e τ k x ∂multivariateGaussian 0 SX) ≤
      ∫ x, gordonTailSmootherApprox e τ k x ∂multivariateGaussian 0 SY := by
  classical
  rw [show gordonTailSmootherApprox e τ k =
      gordonTailSmoother e (((k : ℝ) + 1) ^ 2)
        (τ - 1 / ((k : ℝ) + 1)) by
    funext x; exact gordonTailSmootherApprox_eq e τ k x]
  exact gordonTailSmoother_expectation_comparison e SX SY hSX hSY
    hdiag hwithin hacross _ _

/-- Compares Gaussian minimax tail probabilities under the classified increment ordering.

**Lean implementation helper.** -/
private lemma multivariateGaussian_gordonTail_comparison
    {U T : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] {n : ℕ}
    (e : U × T ≃ Fin n)
    (SX SY : Matrix (Fin n) (Fin n) ℝ)
    (hSX : SX.PosSemidef) (hSY : SY.PosSemidef)
    (hdiag : ∀ p : U × T, SX (e p) (e p) = SY (e p) (e p))
    (hwithin : ∀ p q : U × T, p.1 = q.1 → p ≠ q →
      SY (e p) (e q) ≤ SX (e p) (e q))
    (hacross : ∀ p q : U × T, p.1 ≠ q.1 →
      SX (e p) (e q) ≤ SY (e p) (e q)) :
    ∀ τ : ℝ,
      (multivariateGaussian 0 SX).real
          {x | τ ≤ gordonTailVectorMinimax e x} ≤
        (multivariateGaussian 0 SY).real
          {x | τ ≤ gordonTailVectorMinimax e x} := by
  classical
  intro τ
  have hlimX := tendsto_integral_gordonTailSmootherApprox e SX τ
  have hlimY := tendsto_integral_gordonTailSmootherApprox e SY τ
  exact le_of_tendsto_of_tendsto' hlimX hlimY fun k ↦
    gordonTailSmootherApprox_expectation_comparison
      e SX SY hSX hSY hdiag hwithin hacross τ k

/-- Gordon min-max comparison for Gaussian processes. The printed tail statement is false without equal marginal variances (already
for singleton index sets), so equality of coordinate second moments is stated
explicitly. The proof reconstructs Exercise 7.9's product smoother with an
atom-safe shift, proves its within-row and across-row Hessian signs, applies
Gaussian interpolation, and transports the closed tail event back to the two
finite Gaussian processes.

**Book Theorem 7.2.9.** -/
theorem gordonTailInequality
    {U T ΩX ΩY : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T]
    [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (μX : Measure ΩX) (μY : Measure ΩY)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (X : U → T → ΩX → ℝ) (Y : U → T → ΩY → ℝ)
    (hX : IsGaussianProcess (fun p : U × T ↦ X p.1 p.2) μX)
    (hY : IsGaussianProcess (fun p : U × T ↦ Y p.1 p.2) μY)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μX = 0)
    (hY0 : ∀ u t, ∫ ω, Y u t ω ∂μY = 0)
    (hvar : ∀ u t,
      processSecondMoment μX (fun p : U × T ↦ X p.1 p.2) (u, t) =
        processSecondMoment μY (fun p : U × T ↦ Y p.1 p.2) (u, t))
    (hwithin : ∀ u t s,
      processIncrementSecondMoment μX (fun p : U × T ↦ X p.1 p.2)
          (u, t) (u, s) ≤
        processIncrementSecondMoment μY (fun p : U × T ↦ Y p.1 p.2)
          (u, t) (u, s))
    (hacross : ∀ u v, u ≠ v → ∀ t s,
      processIncrementSecondMoment μY (fun p : U × T ↦ Y p.1 p.2)
          (u, t) (v, s) ≤
        processIncrementSecondMoment μX (fun p : U × T ↦ X p.1 p.2)
          (u, t) (v, s)) :
    ∀ τ : ℝ,
      μX.real {ω | τ ≤ finiteMinimax X ω} ≤
        μY.real {ω | τ ≤ finiteMinimax Y ω} := by
  classical
  let I := U × T
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let PX : I → ΩX → ℝ := fun p ↦ X p.1 p.2
  let PY : I → ΩY → ℝ := fun p ↦ Y p.1 p.2
  let XF : Fin n → ΩX → ℝ := fun i ↦ PX (e.symm i)
  let YF : Fin n → ΩY → ℝ := fun i ↦ PY (e.symm i)
  have hXF : IsGaussianProcess XF μX := by
    change IsGaussianProcess ((fun p : U × T ↦ X p.1 p.2) ∘ e.symm) μX
    exact hX.comp_right e.symm
  have hYF : IsGaussianProcess YF μY := by
    change IsGaussianProcess ((fun p : U × T ↦ Y p.1 p.2) ∘ e.symm) μY
    exact hY.comp_right e.symm
  have hXF0 : ∀ i, ∫ ω, XF i ω ∂μX = 0 := fun i ↦ by
    simpa [XF, PX, I] using hX0 (e.symm i).1 (e.symm i).2
  have hYF0 : ∀ i, ∫ ω, YF i ω ∂μY = 0 := fun i ↦ by
    simpa [YF, PY, I] using hY0 (e.symm i).1 (e.symm i).2
  let VX := processEuclideanVector XF
  let VY := processEuclideanVector YF
  let νX := Measure.map VX μX
  let νY := Measure.map VY μY
  let SX := gaussianMeasureCovarianceMatrix νX
  let SY := gaussianMeasureCovarianceMatrix νY
  have hSX : SX.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νX
  have hSY : SY.PosSemidef := gaussianMeasureCovarianceMatrix_posSemidef νY
  have hLawX : νX = multivariateGaussian 0 SX := by
    simpa [νX, VX, SX] using
      processEuclideanVector_law_eq_multivariateGaussian hXF hXF0
  have hLawY : νY = multivariateGaussian 0 SY := by
    simpa [νY, VY, SY] using
      processEuclideanVector_law_eq_multivariateGaussian hYF hYF0
  have hdiag : ∀ p : I, SX (e p) (e p) = SY (e p) (e p) := by
    intro p
    rw [show SX (e p) (e p) = ∫ ω, XF (e p) ω * XF (e p) ω ∂μX by
      simpa [SX, νX, VX] using
        gaussianMeasureCovarianceMatrix_processVector_apply
          hXF hXF0 (e p) (e p),
      show SY (e p) (e p) = ∫ ω, YF (e p) ω * YF (e p) ω ∂μY by
      simpa [SY, νY, VY] using
        gaussianMeasureCovarianceMatrix_processVector_apply
          hYF hYF0 (e p) (e p)]
    simpa [processSecondMoment, XF, YF, PX, PY, I, pow_two] using
      hvar p.1 p.2
  have hwithinCov : ∀ p q : I, p.1 = q.1 → p ≠ q →
      SY (e p) (e q) ≤ SX (e p) (e q) := by
    intro p q hrow _
    have hqeq : (p.1, q.2) = q := Prod.ext hrow rfl
    have hvp : processSecondMoment μX XF (e p) =
        processSecondMoment μY YF (e p) := by
      simpa [processSecondMoment, XF, YF, PX, PY, I] using hvar p.1 p.2
    have hvq : processSecondMoment μX XF (e q) =
        processSecondMoment μY YF (e q) := by
      simpa [processSecondMoment, XF, YF, PX, PY, I] using hvar q.1 q.2
    have hincF : processIncrementSecondMoment μX XF (e p) (e q) ≤
        processIncrementSecondMoment μY YF (e p) (e q) := by
      rw [← hqeq]
      simpa [processIncrementSecondMoment, XF, YF, PX, PY, I] using
        hwithin p.1 p.2 q.2
    rw [processIncrementSecondMoment_eq hXF,
      processIncrementSecondMoment_eq hYF, hvp, hvq] at hincF
    rw [show SY (e p) (e q) = ∫ ω, YF (e p) ω * YF (e q) ω ∂μY by
      simpa [SY, νY, VY] using
        gaussianMeasureCovarianceMatrix_processVector_apply
          hYF hYF0 (e p) (e q),
      show SX (e p) (e q) = ∫ ω, XF (e p) ω * XF (e q) ω ∂μX by
      simpa [SX, νX, VX] using
        gaussianMeasureCovarianceMatrix_processVector_apply
          hXF hXF0 (e p) (e q)]
    linarith
  have hacrossCov : ∀ p q : I, p.1 ≠ q.1 →
      SX (e p) (e q) ≤ SY (e p) (e q) := by
    intro p q hrow
    have hvp : processSecondMoment μX XF (e p) =
        processSecondMoment μY YF (e p) := by
      simpa [processSecondMoment, XF, YF, PX, PY, I] using hvar p.1 p.2
    have hvq : processSecondMoment μX XF (e q) =
        processSecondMoment μY YF (e q) := by
      simpa [processSecondMoment, XF, YF, PX, PY, I] using hvar q.1 q.2
    have hincF : processIncrementSecondMoment μY YF (e p) (e q) ≤
        processIncrementSecondMoment μX XF (e p) (e q) := by
      simpa [processIncrementSecondMoment, XF, YF, PX, PY, I] using
        hacross p.1 q.1 hrow p.2 q.2
    rw [processIncrementSecondMoment_eq hYF,
      processIncrementSecondMoment_eq hXF, ← hvp, ← hvq] at hincF
    rw [show SX (e p) (e q) = ∫ ω, XF (e p) ω * XF (e q) ω ∂μX by
      simpa [SX, νX, VX] using
        gaussianMeasureCovarianceMatrix_processVector_apply
          hXF hXF0 (e p) (e q),
      show SY (e p) (e q) = ∫ ω, YF (e p) ω * YF (e q) ω ∂μY by
      simpa [SY, νY, VY] using
        gaussianMeasureCovarianceMatrix_processVector_apply
          hYF hYF0 (e p) (e q)]
    linarith
  have hmatrix := multivariateGaussian_gordonTail_comparison
    e SX SY hSX hSY hdiag hwithinCov hacrossCov
  intro τ
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | τ ≤ gordonTailVectorMinimax e x}
  have hA : MeasurableSet A :=
    (continuous_gordonTailVectorMinimax e).measurable measurableSet_Ici
  have hVX : AEMeasurable VX μX := by
    simpa [VX] using (processEuclideanVector_hasGaussianLaw hXF).aemeasurable
  have hVY : AEMeasurable VY μY := by
    simpa [VY] using (processEuclideanVector_hasGaussianLaw hYF).aemeasurable
  have hminimaxX : ∀ ω, gordonTailVectorMinimax e (VX ω) = finiteMinimax X ω := by
    intro ω
    unfold gordonTailVectorMinimax finiteMinimax HDP.Chapter5.finiteMaximum
    simp [VX, processEuclideanVector, XF, PX, I]
  have hminimaxY : ∀ ω, gordonTailVectorMinimax e (VY ω) = finiteMinimax Y ω := by
    intro ω
    unfold gordonTailVectorMinimax finiteMinimax HDP.Chapter5.finiteMaximum
    simp [VY, processEuclideanVector, YF, PY, I]
  have hpreX : VX ⁻¹' A = {ω | τ ≤ finiteMinimax X ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, A]
    rw [hminimaxX]
  have hpreY : VY ⁻¹' A = {ω | τ ≤ finiteMinimax Y ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, A]
    rw [hminimaxY]
  have hmapX : μX.real {ω | τ ≤ finiteMinimax X ω} = νX.real A := by
    change ENNReal.toReal (μX {ω | τ ≤ finiteMinimax X ω}) =
      ENNReal.toReal ((Measure.map VX μX) A)
    rw [Measure.map_apply_of_aemeasurable hVX hA, hpreX]
  have hmapY : μY.real {ω | τ ≤ finiteMinimax Y ω} = νY.real A := by
    change ENNReal.toReal (μY {ω | τ ≤ finiteMinimax Y ω}) =
      ENNReal.toReal ((Measure.map VY μY) A)
    rw [Measure.map_apply_of_aemeasurable hVY hA, hpreY]
  rw [hmapX, hmapY, hLawX, hLawY]
  simpa [A] using hmatrix τ

/-- Gordon min-max comparison for Gaussian processes. The exercise is the source's proof obligation for the equal-variance case of
Gordon's comparison theorem. Its tail conclusion must range over every real
threshold; restricting to nonnegative thresholds would not imply the stated
expectation comparison for a possibly negative min--max variable. The Lean
derivation below now combines the two fully verified comparison endpoints.

**Book Theorem 7.2.9.** -/
theorem exercise_7_9_gordon_equalVariance
    {U T Ω : Type*} [Fintype U] [Nonempty U]
    [Fintype T] [Nonempty T] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : U → T → Ω → ℝ)
    (hX : IsGaussianProcess (fun p : U × T ↦ X p.1 p.2) μ)
    (hY : IsGaussianProcess (fun p : U × T ↦ Y p.1 p.2) μ)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μ = 0)
    (hY0 : ∀ u t, ∫ ω, Y u t ω ∂μ = 0)
    (hvar : ∀ u t,
      processSecondMoment μ (fun p : U × T ↦ X p.1 p.2) (u, t) =
        processSecondMoment μ (fun p : U × T ↦ Y p.1 p.2) (u, t))
    (hwithin : ∀ u t s,
      processIncrementSecondMoment μ (fun p : U × T ↦ X p.1 p.2)
          (u, t) (u, s) ≤
        processIncrementSecondMoment μ (fun p : U × T ↦ Y p.1 p.2)
          (u, t) (u, s))
    (hacross : ∀ u v, u ≠ v → ∀ t s,
      processIncrementSecondMoment μ (fun p : U × T ↦ Y p.1 p.2)
          (u, t) (v, s) ≤
        processIncrementSecondMoment μ (fun p : U × T ↦ X p.1 p.2)
          (u, t) (v, s)) :
    (∀ τ : ℝ,
      μ.real {ω | τ ≤ finiteMinimax X ω} ≤
        μ.real {ω | τ ≤ finiteMinimax Y ω}) ∧
      (∫ ω, finiteMinimax X ω ∂μ) ≤
        ∫ ω, finiteMinimax Y ω ∂μ := by
  exact ⟨gordonTailInequality μ μ X Y hX hY hX0 hY0 hvar hwithin hacross,
    gordonExpectationInequality μ μ X Y hX hY hX0 hY0 hwithin hacross⟩

end

end HDP.Chapter7

end Source_05_GaussianComparison

/-! ## Material formerly in `06_GaussianMatrices.lean` -/

section Source_06_GaussianMatrices

/-!
# Book Chapter 7, §7.3: sharp bounds for Gaussian matrices
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator ENNReal NNReal

namespace HDP.Chapter7

noncomputable section

/-- Product law of an `m × n` matrix of independent standard normal entries. -/
abbrev gaussianMatrixMeasure (m n : ℕ) :
    Measure (Matrix (Fin m) (Fin n) ℝ) :=
  Measure.pi (fun _ : Fin m ↦ Measure.pi
    (fun _ : Fin n ↦ gaussianReal 0 1))

/-- Frobenius distance identity for rank-one tensors used in the Gaussian matrix comparison. Corrected ambient dimensions:
`u,w` live in `ℝⁿ` and `v,z` in `ℝᵐ`; the printed `ℝⁿ⁻¹/ℝᵐ⁻¹` confuses a
sphere's superscript with its ambient dimension.

**Book Exercise 7.10.** -/
theorem exercise_7_10_rankOne_frobenius_distance
    {n m : ℕ}
    (u w : EuclideanSpace ℝ (Fin n))
    (v z : EuclideanSpace ℝ (Fin m))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    HDP.matrixFrobeniusNorm
        (HDP.Chapter4.outerMatrix u v - HDP.Chapter4.outerMatrix w z) ^ 2 ≤
      ‖u - w‖ ^ 2 + ‖v - z‖ ^ 2 := by
  have houter (a c : EuclideanSpace ℝ (Fin n))
      (b d : EuclideanSpace ℝ (Fin m)) :
      HDP.matrixFrobeniusInner
          (HDP.Chapter4.outerMatrix a b)
          (HDP.Chapter4.outerMatrix c d) =
        inner ℝ a c * inner ℝ b d := by
    simp only [HDP.matrixFrobeniusInner, HDP.Chapter4.outerMatrix,
      Matrix.vecMulVec_apply, PiLp.inner_apply, Real.inner_apply]
    calc
      (∑ i, ∑ j, a.ofLp i * b.ofLp j * (c.ofLp i * d.ofLp j)) =
          ∑ i, ∑ j, (a.ofLp i * c.ofLp i) * (b.ofLp j * d.ofLp j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ i, (a.ofLp i * c.ofLp i) *
          ∑ j, (b.ofLp j * d.ofLp j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = (∑ i, a.ofLp i * c.ofLp i) *
          ∑ j, b.ofLp j * d.ofLp j := by rw [Finset.sum_mul]
  have hinnerUW : inner ℝ u w ≤ 1 := by
    calc
      inner ℝ u w ≤ ‖u‖ * ‖w‖ := real_inner_le_norm u w
      _ = 1 := by rw [hu, hw]; norm_num
  have hinnerVZ : inner ℝ v z ≤ 1 := by
    calc
      inner ℝ v z ≤ ‖v‖ * ‖z‖ := real_inner_le_norm v z
      _ = 1 := by rw [hv, hz]; norm_num
  have hprod : 0 ≤ (1 - inner ℝ u w) * (1 - inner ℝ v z) :=
    mul_nonneg (sub_nonneg.mpr hinnerUW) (sub_nonneg.mpr hinnerVZ)
  have hF :
      HDP.matrixFrobeniusNorm
          (HDP.Chapter4.outerMatrix u v - HDP.Chapter4.outerMatrix w z) ^ 2 =
        2 - 2 * inner ℝ u w * inner ℝ v z := by
    let A := HDP.Chapter4.outerMatrix u v
    let B := HDP.Chapter4.outerMatrix w z
    calc
      HDP.matrixFrobeniusNorm (A - B) ^ 2 =
          HDP.matrixFrobeniusInner (A - B) (A - B) :=
        HDP.Chapter4.frobeniusNorm_sq_eq_inner (A - B)
      _ = HDP.matrixFrobeniusInner A A -
          2 * HDP.matrixFrobeniusInner A B +
          HDP.matrixFrobeniusInner B B := by
            simp only [HDP.matrixFrobeniusInner, Matrix.sub_apply]
            simp_rw [sub_mul, mul_sub]
            simp only [Finset.sum_sub_distrib]
            have hcomm :
                (∑ i, ∑ j, B i j * A i j) =
                  ∑ i, ∑ j, A i j * B i j := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hcomm]
            ring
      _ = 2 - 2 * inner ℝ u w * inner ℝ v z := by
        simp only [A, B, houter, real_inner_self_eq_norm_sq]
        rw [hu, hw, hv, hz]
        ring
  rw [hF, norm_sub_sq_real, norm_sub_sq_real, hu, hw, hv, hz]
  nlinarith

/-! ### Finite-net Gaussian comparison infrastructure -/

/-- A finite sum of inner products with independent standard Gaussian vectors is a Gaussian process.

**Lean implementation helper.** -/
private theorem isGaussianProcess_sum_inner_prod_aux
    {I E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (u : I → E) (v : I → F) :
    IsGaussianProcess
      (fun i (p : E × F) => inner ℝ (u i) p.1 + inner ℝ (v i) p.2)
      ((stdGaussian E).prod (stdGaussian F)) := by
  refine ⟨fun J => ?_⟩
  let f : E → (J → ℝ) := fun g i => inner ℝ (u i) g
  let h : F → (J → ℝ) := fun z i => inner ℝ (v i) z
  have hfm : Measurable f := by
    apply measurable_pi_lambda
    intro i
    exact ((innerSL ℝ) (u i)).continuous.measurable
  have hhm : Measurable h := by
    apply measurable_pi_lambda
    intro i
    exact ((innerSL ℝ) (v i)).continuous.measurable
  have hfG : HasGaussianLaw f (stdGaussian E) := by
    have hbase := (canonicalGaussianProcess_isGaussian u).hasGaussianLaw J
    refine hbase.congr (ae_of_all _ fun g => ?_)
    ext i
    rfl
  have hhG : HasGaussianLaw h (stdGaussian F) := by
    have hbase := (canonicalGaussianProcess_isGaussian v).hasGaussianLaw J
    refine hbase.congr (ae_of_all _ fun z => ?_)
    ext i
    rfl
  have hfst : HasGaussianLaw (fun p : E × F => f p.1)
      ((stdGaussian E).prod (stdGaussian F)) := by
    refine ⟨?_⟩
    have hmap : ((stdGaussian E).prod (stdGaussian F)).map
        (fun p : E × F => f p.1) = (stdGaussian E).map f := by
      rw [show (fun p : E × F => f p.1) = f ∘ Prod.fst by rfl,
        ← Measure.map_map hfm measurable_fst,
        (measurePreserving_fst (μ := stdGaussian E)
          (ν := stdGaussian F)).map_eq]
    rw [hmap]
    exact hfG.isGaussian_map
  have hsnd : HasGaussianLaw (fun p : E × F => h p.2)
      ((stdGaussian E).prod (stdGaussian F)) := by
    refine ⟨?_⟩
    have hmap : ((stdGaussian E).prod (stdGaussian F)).map
        (fun p : E × F => h p.2) = (stdGaussian F).map h := by
      rw [show (fun p : E × F => h p.2) = h ∘ Prod.snd by rfl,
        ← Measure.map_map hhm measurable_snd,
        (measurePreserving_snd (μ := stdGaussian E)
          (ν := stdGaussian F)).map_eq]
    rw [hmap]
    exact hhG.isGaussian_map
  have hind : (fun p : E × F => f p.1) ⟂ᵢ[
      (stdGaussian E).prod (stdGaussian F)] (fun p : E × F => h p.2) :=
    indepFun_prod (X := f) (Y := h) hfm hhm
  have hadd := iIndepFun.hasGaussianLaw_fun_add hfst hsnd hind
  refine hadd.congr (ae_of_all _ fun p => ?_)
  ext i
  rfl

/-- The inner product with a standard Gaussian vector belongs to L².

**Lean implementation helper.** -/
private theorem memLp_two_inner_stdGaussian_aux
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x : E) :
    MemLp (fun g : E => inner ℝ x g) 2 (stdGaussian E) := by
  let L : StrongDual ℝ E := (innerSL ℝ) x
  have h := (ProbabilityTheory.IsGaussian.hasGaussianLaw_id :
    HasGaussianLaw (id : E → E) (stdGaussian E)).map L
  simpa [L, Function.comp_def, innerSL_apply_apply] using h.memLp_two

/-- The second moment of a standard Gaussian inner product is the squared norm of its coefficient.

**Lean implementation helper.** -/
private theorem integral_inner_sq_stdGaussian_aux
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x : E) :
    (∫ g : E, (inner ℝ x g) ^ 2 ∂stdGaussian E) = ‖x‖ ^ 2 := by
  let L : StrongDual ℝ E := (innerSL ℝ) x
  have hmem : MemLp L 2 (stdGaussian E) := by
    simpa [L, Function.comp_def, innerSL_apply_apply] using
      memLp_two_inner_stdGaussian_aux x
  have hv := variance_eq_sub hmem
  rw [integral_strongDual_stdGaussian L, variance_dual_stdGaussian L,
    innerSL_apply_norm] at hv
  change ‖x‖ ^ 2 =
    (∫ g : E, (inner ℝ x g) ^ 2 ∂stdGaussian E) - 0 ^ 2 at hv
  nlinarith

/-- Computes the increment second moment of a process formed from sums of Gaussian inner products.

**Lean implementation helper.** -/
private theorem processIncrementSecondMoment_sum_inner_prod_aux
    {I E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (u : I → E) (v : I → F) (i j : I) :
    processIncrementSecondMoment ((stdGaussian E).prod (stdGaussian F))
      (fun i (p : E × F) => inner ℝ (u i) p.1 + inner ℝ (v i) p.2) i j =
      ‖u i - u j‖ ^ 2 + ‖v i - v j‖ ^ 2 := by
  let a : E → ℝ := fun g => inner ℝ (u i - u j) g
  let b : F → ℝ := fun h => inner ℝ (v i - v j) h
  have ha : MemLp a 2 (stdGaussian E) := by
    simpa [a] using memLp_two_inner_stdGaussian_aux (u i - u j)
  have hb : MemLp b 2 (stdGaussian F) := by
    simpa [b] using memLp_two_inner_stdGaussian_aux (v i - v j)
  have hv := variance_add_prod ha hb
  have hmeanA : (∫ g, a g ∂stdGaussian E) = 0 := by
    simpa only [a, innerSL_apply_apply] using
      integral_strongDual_stdGaussian ((innerSL ℝ) (u i - u j))
  have hmeanB : (∫ h, b h ∂stdGaussian F) = 0 := by
    simpa only [b, innerSL_apply_apply] using
      integral_strongDual_stdGaussian ((innerSL ℝ) (v i - v j))
  have hmean : (∫ p : E × F, a p.1 + b p.2
      ∂(stdGaussian E).prod (stdGaussian F)) = 0 := by
    rw [integral_add ((ha.integrable (by norm_num)).comp_fst _)
      ((hb.integrable (by norm_num)).comp_snd _)]
    rw [integral_prod _ ((ha.integrable (by norm_num)).comp_fst _),
      integral_prod _ ((hb.integrable (by norm_num)).comp_snd _)]
    simp [hmeanA, hmeanB]
  have hmem : MemLp (fun p : E × F => a p.1 + b p.2) 2
      ((stdGaussian E).prod (stdGaussian F)) :=
    (ha.comp_fst _).add (hb.comp_snd _)
  have hsecond := variance_eq_sub hmem
  rw [hmean] at hsecond
  have hvarA : Var[a; stdGaussian E] = ‖u i - u j‖ ^ 2 := by
    rw [variance_eq_sub ha, hmeanA]
    simpa [a] using integral_inner_sq_stdGaussian_aux (u i - u j)
  have hvarB : Var[b; stdGaussian F] = ‖v i - v j‖ ^ 2 := by
    rw [variance_eq_sub hb, hmeanB]
    simpa [b] using integral_inner_sq_stdGaussian_aux (v i - v j)
  rw [hvarA, hvarB] at hv
  unfold processIncrementSecondMoment
  have hfun : (fun p : E × F =>
      ((inner ℝ (u i) p.1 + inner ℝ (v i) p.2) -
        (inner ℝ (u j) p.1 + inner ℝ (v j) p.2)) ^ 2) =
      fun p => (a p.1 + b p.2) ^ 2 := by
    funext p
    simp only [a, b, inner_sub_left]
    ring
  rw [hfun]
  rw [hv] at hsecond
  norm_num at hsecond
  exact hsecond.symm

/-- Every positive scale admits a finite net of the Euclidean unit sphere.

**Lean implementation helper.** -/
private theorem exists_finite_unitSphereNet_aux
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin d)),
      N.Nonempty ∧
        HDP.IsUnitSphereNet ε
          (N : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin d)) :=
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  let εnn : ℝ≥0 := ⟨ε, hε.le⟩
  have hεnn : εnn ≠ 0 := by
    apply ne_of_gt
    exact hε
  have hS : IsCompact (closure S) := by
    rw [show closure S = S by exact Metric.isClosed_sphere.closure_eq]
    exact isCompact_sphere 0 1
  obtain ⟨Nset, hNsub, hNfin, hNcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact_closure hεnn hS
  let N : Finset (EuclideanSpace ℝ (Fin d)) := hNfin.toFinset
  have hNnet : HDP.IsUnitSphereNet ε
      (N : Set (EuclideanSpace ℝ (Fin d))) := by
    constructor
    · intro x hx
      have hxN : x ∈ Nset := by simpa [N] using hx
      have hxS : x ∈ S := hNsub hxN
      simpa [S, Metric.mem_sphere, dist_zero_right] using hxS
    · intro x hx
      have hxS : x ∈ S := by
        simpa [S, Metric.mem_sphere, dist_zero_right] using hx
      obtain ⟨y, hyN, hxy⟩ := hNcover hxS
      refine ⟨y, by simpa [N] using hyN, ?_⟩
      have hdist : dist x y ≤ ε := by
        change edist x y ≤ (εnn : ℝ≥0∞) at hxy
        rw [edist_nndist] at hxy
        have hnn : nndist x y ≤ εnn := ENNReal.coe_le_coe.mp hxy
        exact_mod_cast hnn
      simpa [dist_eq_norm] using hdist
  have hNnonempty : N.Nonempty := by
    let i : Fin d := ⟨0, hd⟩
    let x : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    have hx : ‖x‖ = 1 := by simp [x]
    obtain ⟨y, hy, _⟩ := hNnet.2 x hx
    exact ⟨y, hy⟩
  exact ⟨N, hNnonempty, hNnet⟩

private abbrev SignedNetPointAux {d : ℕ}
    (N : Finset (EuclideanSpace ℝ (Fin d))) := ↥N × Bool

/-- Assigns to a signed net point the corresponding signed Euclidean vector.

**Lean implementation helper.** -/
private def signedNetValueAux {d : ℕ}
    {N : Finset (EuclideanSpace ℝ (Fin d))}
    (p : SignedNetPointAux N) : EuclideanSpace ℝ (Fin d) :=
  if p.2 then p.1 else -p.1

/-- Every signed net value has unit norm.

**Lean implementation helper.** -/
private lemma signedNetValueAux_norm {d : ℕ}
    {N : Finset (EuclideanSpace ℝ (Fin d))}
    (hN : ∀ x ∈ N, ‖x‖ = 1) (p : SignedNetPointAux N) :
    ‖signedNetValueAux p‖ = 1 := by
  cases p with
  | mk x b =>
      cases b <;> simp [signedNetValueAux, hN x x.property]

/-- Negating the sign negates the corresponding signed net value.

**Lean implementation helper.** -/
private lemma signedNetValueAux_flip {d : ℕ}
    {N : Finset (EuclideanSpace ℝ (Fin d))}
    (p : SignedNetPointAux N) :
    signedNetValueAux (p.1, !p.2) = -signedNetValueAux p := by
  cases p with
  | mk x b => cases b <;> simp [signedNetValueAux]

/-- The range of signed net values is a finite net of the unit sphere.

**Lean implementation helper.** -/
private lemma signedNetRange_isUnitSphereNet_aux {d : ℕ} {ε : ℝ}
    {N : Finset (EuclideanSpace ℝ (Fin d))}
    (hN : HDP.IsUnitSphereNet ε
      (N : Set (EuclideanSpace ℝ (Fin d)))) :
    HDP.IsUnitSphereNet ε
      (Set.range (signedNetValueAux (N := N))) := by
  constructor
  · intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact signedNetValueAux_norm hN.1 p
  · intro x hx
    obtain ⟨y, hyN, hxy⟩ := hN.2 x hx
    let p : SignedNetPointAux N := (⟨y, hyN⟩, true)
    refine ⟨signedNetValueAux p, ⟨p, rfl⟩, ?_⟩
    simpa [p, signedNetValueAux] using hxy

/-- Forms the rank-one tensor point obtained from a vector and a Gaussian vector.

**Lean implementation helper.** -/
private def rankOneGaussianPointAux {m n : ℕ}
    (u : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (fun p => (WithLp.ofLp v) p.1 * (WithLp.ofLp u) p.2)

/-- The squared distance between two rank-one Gaussian points is bounded by the Gaussian norm times the squared distance of their unit factors.

**Lean implementation helper.** -/
private lemma rankOneGaussianPointAux_sub_norm_sq_le
    {m n : ℕ}
    (u w : EuclideanSpace ℝ (Fin n))
    (v z : EuclideanSpace ℝ (Fin m))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    ‖rankOneGaussianPointAux u v - rankOneGaussianPointAux w z‖ ^ 2 ≤
      ‖u - w‖ ^ 2 + ‖v - z‖ ^ 2 := by
  have h := exercise_7_10_rankOne_frobenius_distance
    v z u w hv hz hu hw
  rw [HDP.matrixFrobeniusNorm_sq] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [rankOneGaussianPointAux, PiLp.sub_apply,
    HDP.Chapter4.outerMatrix, Matrix.vecMulVec_apply, Matrix.sub_apply] at h ⊢
  rw [← Finset.sum_product'] at h
  simpa [add_comm] using h

/-- Converts a Euclidean vector indexed by matrix coordinates back into a real matrix.

**Lean implementation helper.** -/
private def unflattenEuclideanMatrixAux {m n : ℕ}
    (g : EuclideanSpace ℝ (Fin m × Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => (WithLp.ofLp g) (i, j)

/-- The inner product with a rank-one Gaussian point equals the corresponding Gaussian bilinear form.

**Lean implementation helper.** -/
private lemma rankOneGaussianPointAux_inner
    {m n : ℕ}
    (u : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin m × Fin n)) :
    inner ℝ (rankOneGaussianPointAux u v) g =
      inner ℝ ((unflattenEuclideanMatrixAux g).toEuclideanLin u) v := by
  simp only [rankOneGaussianPointAux, unflattenEuclideanMatrixAux,
    PiLp.inner_apply, Real.inner_apply,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The operator norm of an unflattened Euclidean matrix is bounded by the Euclidean norm of its coordinates.

**Lean implementation helper.** -/
private lemma unflattenEuclideanMatrixAux_opNorm_le_norm
    {m n : ℕ} (g : EuclideanSpace ℝ (Fin m × Fin n)) :
    HDP.matrixOpNorm (unflattenEuclideanMatrixAux g) ≤ ‖g‖ := by
  calc
    HDP.matrixOpNorm (unflattenEuclideanMatrixAux g) ≤
        HDP.matrixFrobeniusNorm (unflattenEuclideanMatrixAux g) :=
      HDP.Chapter4.operatorNorm_le_frobeniusNorm _
    _ = ‖g‖ := by
      apply sq_eq_sq₀ (HDP.matrixFrobeniusNorm_nonneg _) (norm_nonneg _)|>.mp
      rw [HDP.matrixFrobeniusNorm_sq, EuclideanSpace.real_norm_sq_eq]
      rw [← Finset.sum_product']
      rfl

/-- The canonical Gaussian increment second moment equals the squared Euclidean distance between its index vectors.

**Lean implementation helper.** -/
private lemma canonicalGaussian_incrementSecondMoment_aux
    {I E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : I → E) (i j : I) :
    processIncrementSecondMoment (stdGaussian E)
        (canonicalGaussianProcess a) i j = ‖a i - a j‖ ^ 2 := by
  unfold processIncrementSecondMoment
  have hfun : (fun g : E =>
      (canonicalGaussianProcess a i g - canonicalGaussianProcess a j g) ^ 2) =
      fun g => (inner ℝ (a i - a j) g) ^ 2 := by
    funext g
    simp [canonicalGaussianProcess, inner_sub_left]
  rw [hfun]
  exact integral_inner_sq_stdGaussian_aux (a i - a j)

/-- The pointwise maximum of a finite Gaussian family is integrable.

**Lean implementation helper.** -/
private lemma integrable_finiteMaximum_aux
    {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] {μ : Measure Ω}
    (X : I → Ω → ℝ) (hX : ∀ i, Integrable (X i) μ) :
    Integrable (HDP.Chapter5.finiteMaximum X) μ := by
  rw [show HDP.Chapter5.finiteMaximum X =
      Finset.univ.sup' Finset.univ_nonempty X by
    funext x
    simp [HDP.Chapter5.finiteMaximum]]
  refine Finset.sup'_induction Finset.univ_nonempty X
    (p := fun f : Ω → ℝ => Integrable f μ) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro i hi
    exact hX i

/-- Flattens a Gaussian matrix into its coordinate function.

**Lean implementation helper.** -/
private def flattenGaussianMatrixAux {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin m × Fin n → ℝ :=
  fun p => A p.1 p.2

/-- Views a Gaussian matrix as a Euclidean vector of its entries.

**Lean implementation helper.** -/
private def vectorizeGaussianMatrixAux {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (flattenGaussianMatrixAux A)

/-- Flattening a Gaussian matrix into its coordinate function is measurable.

**Lean implementation helper.** -/
private lemma flattenGaussianMatrixAux_measurable {m n : ℕ} :
    Measurable (flattenGaussianMatrixAux :
      Matrix (Fin m) (Fin n) ℝ → (Fin m × Fin n → ℝ)) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- Flattening a Gaussian matrix sends its law to the product standard Gaussian measure on coordinates.

**Lean implementation helper.** -/
private lemma flattenGaussianMatrixAux_map (m n : ℕ) :
    (gaussianMatrixMeasure m n).map flattenGaussianMatrixAux =
      Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
  change (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map
        flattenGaussianMatrixAux = _
  have h := Measure.infinitePi_map_curry_symm
    (fun _ : Fin m => fun _ : Fin n => gaussianReal 0 1)
  have hfun : flattenGaussianMatrixAux =
      ⇑(MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm := rfl
  rw [hfun]
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  congr 2

/-- The vectorized Gaussian matrix has the standard Euclidean Gaussian law.

**Lean implementation helper.** -/
private lemma vectorizeGaussianMatrixAux_hasLaw (m n : ℕ) :
    HasLaw vectorizeGaussianMatrixAux
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)))
      (gaussianMatrixMeasure m n) := by
  have hmeas : Measurable (vectorizeGaussianMatrixAux :
      Matrix (Fin m) (Fin n) ℝ → EuclideanSpace ℝ (Fin m × Fin n)) := by
    change Measurable ((WithLp.toLp 2) ∘ flattenGaussianMatrixAux)
    exact (PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
      (fun _ : Fin m × Fin n => ℝ)).measurable.comp
      flattenGaussianMatrixAux_measurable
  refine ⟨hmeas.aemeasurable, ?_⟩
  rw [show vectorizeGaussianMatrixAux =
      (WithLp.toLp 2) ∘ flattenGaussianMatrixAux by rfl,
    ← Measure.map_map (by fun_prop) flattenGaussianMatrixAux_measurable,
    flattenGaussianMatrixAux_map, map_pi_eq_stdGaussian]

/-- Unflattening the vectorized Gaussian matrix recovers the original matrix.

**Lean implementation helper.** -/
private lemma unflatten_vectorizeGaussianMatrixAux {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    unflattenEuclideanMatrixAux (vectorizeGaussianMatrixAux A) = A := by
  rfl

/-- The map from Euclidean matrix coordinates `g` to `matrixOpNorm (unflattenEuclideanMatrixAux g)` is measurable.

**Lean implementation helper.** -/
private lemma unflattenEuclideanMatrixAux_opNorm_measurable {m n : ℕ} :
    Measurable (fun g : EuclideanSpace ℝ (Fin m × Fin n) =>
      HDP.matrixOpNorm (unflattenEuclideanMatrixAux g)) := by
  apply Continuous.measurable
  have hU : Continuous (unflattenEuclideanMatrixAux :
      EuclideanSpace ℝ (Fin m × Fin n) → Matrix (Fin m) (Fin n) ℝ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact PiLp.continuous_apply (p := (2 : ℝ≥0∞))
      (fun _ : Fin m × Fin n => ℝ) (i, j)
  change Continuous ((fun A : Matrix (Fin m) (Fin n) ℝ => ‖A‖) ∘
    unflattenEuclideanMatrixAux)
  exact continuous_norm.comp hU

/-- The expected Gaussian matrix operator norm equals the expected operator norm of its Euclidean coordinate representation.

**Lean implementation helper.** -/
private lemma gaussianMatrix_opNorm_integral_eq_euclidean_aux (m n : ℕ) :
    (∫ A, HDP.matrixOpNorm A ∂gaussianMatrixMeasure m n) =
      ∫ g : EuclideanSpace ℝ (Fin m × Fin n),
        HDP.matrixOpNorm (unflattenEuclideanMatrixAux g)
        ∂stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)) := by
  let W : EuclideanSpace ℝ (Fin m × Fin n) → ℝ := fun g =>
    HDP.matrixOpNorm (unflattenEuclideanMatrixAux g)
  have h := (vectorizeGaussianMatrixAux_hasLaw m n).integral_comp
    unflattenEuclideanMatrixAux_opNorm_measurable.aestronglyMeasurable
  simpa only [Function.comp_def, unflatten_vectorizeGaussianMatrixAux] using h

/-- The operator norm `matrixOpNorm (unflattenEuclideanMatrixAux g)` is integrable under the standard Gaussian law on Euclidean matrix coordinates.

**Lean implementation helper.** -/
private lemma integrable_unflattenEuclideanMatrixAux_opNorm
    (m n : ℕ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin m × Fin n) =>
      HDP.matrixOpNorm (unflattenEuclideanMatrixAux g))
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) := by
  have hid : Integrable
      (id : EuclideanSpace ℝ (Fin m × Fin n) →
        EuclideanSpace ℝ (Fin m × Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.integrable (by norm_num)
  refine hid.norm.mono'
    unflattenEuclideanMatrixAux_opNorm_measurable.aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (HDP.matrixOpNorm_nonneg (unflattenEuclideanMatrixAux g))]
  simpa using unflattenEuclideanMatrixAux_opNorm_le_norm g

/-- A finite sum of inner products against independent standard Gaussians is centered.

**Lean implementation helper.** -/
private theorem sum_inner_prod_centered_aux
    {I E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (u : I → E) (v : I → F) (i : I) :
    (∫ p : E × F, inner ℝ (u i) p.1 + inner ℝ (v i) p.2
      ∂(stdGaussian E).prod (stdGaussian F)) = 0 := by
  have hu := (memLp_two_inner_stdGaussian_aux (u i)).integrable (by norm_num)
  have hv := (memLp_two_inner_stdGaussian_aux (v i)).integrable (by norm_num)
  have hEu : (∫ g : E, inner ℝ (u i) g ∂stdGaussian E) = 0 := by
    simpa only [innerSL_apply_apply] using
      integral_strongDual_stdGaussian ((innerSL ℝ) (u i))
  have hFv : (∫ z : F, inner ℝ (v i) z ∂stdGaussian F) = 0 := by
    simpa only [innerSL_apply_apply] using
      integral_strongDual_stdGaussian ((innerSL ℝ) (v i))
  rw [integral_add (hu.comp_fst _) (hv.comp_snd _)]
  rw [integral_prod _ (hu.comp_fst _), integral_prod _ (hv.comp_snd _)]
  simp [hEu, hFv]

/-- Bounds the expected supremum of a Gaussian inner-product process by a Gaussian norm factor times the expected operator norm.

**Lean implementation helper.** -/
private theorem expectedFiniteSupremum_sum_inner_prod_le_aux
    {I E F : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (u : I → E) (v : I → F)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) :
    expectedFiniteSupremum ((stdGaussian E).prod (stdGaussian F))
        (fun i (p : E × F) => inner ℝ (u i) p.1 + inner ℝ (v i) p.2) ≤
      (∫ g : E, ‖g‖ ∂stdGaussian E) +
        ∫ h : F, ‖h‖ ∂stdGaussian F := by
  let Y : I → E × F → ℝ :=
    fun i p => inner ℝ (u i) p.1 + inner ℝ (v i) p.2
  have hYi : ∀ i, Integrable (Y i) ((stdGaussian E).prod (stdGaussian F)) := by
    intro i
    exact (((memLp_two_inner_stdGaussian_aux (u i)).integrable
      (by norm_num)).comp_fst _).add
      (((memLp_two_inner_stdGaussian_aux (v i)).integrable
        (by norm_num)).comp_snd _)
  have hmax : Integrable (HDP.Chapter5.finiteMaximum Y)
      ((stdGaussian E).prod (stdGaussian F)) :=
    integrable_finiteMaximum_aux Y hYi
  have hE : Integrable (id : E → E) (stdGaussian E) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.integrable (by norm_num)
  have hF : Integrable (id : F → F) (stdGaussian F) :=
    ProbabilityTheory.IsGaussian.memLp_two_id.integrable (by norm_num)
  have hEnorm : Integrable (fun g : E => ‖g‖) (stdGaussian E) := by
    simpa only [id_eq] using hE.norm
  have hFnorm : Integrable (fun h : F => ‖h‖) (stdGaussian F) := by
    simpa only [id_eq] using hF.norm
  have hrhs : Integrable (fun p : E × F => ‖p.1‖ + ‖p.2‖)
      ((stdGaussian E).prod (stdGaussian F)) :=
    (hEnorm.comp_fst _).add (hFnorm.comp_snd _)
  have hpoint : ∀ p : E × F,
      HDP.Chapter5.finiteMaximum Y p ≤ ‖p.1‖ + ‖p.2‖ := by
    intro p
    unfold HDP.Chapter5.finiteMaximum
    apply Finset.sup'_le
    intro i hi
    dsimp [Y]
    calc
      inner ℝ (u i) p.1 + inner ℝ (v i) p.2 ≤
          ‖u i‖ * ‖p.1‖ + ‖v i‖ * ‖p.2‖ :=
        add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
      _ = ‖p.1‖ + ‖p.2‖ := by rw [hu i, hv i, one_mul, one_mul]
  unfold expectedFiniteSupremum
  calc
    (∫ p, HDP.Chapter5.finiteMaximum Y p
        ∂(stdGaussian E).prod (stdGaussian F)) ≤
        ∫ p : E × F, (‖p.1‖ + ‖p.2‖)
          ∂(stdGaussian E).prod (stdGaussian F) := by
      exact integral_mono hmax hrhs hpoint
    _ = (∫ g : E, ‖g‖ ∂stdGaussian E) +
        ∫ h : F, ‖h‖ ∂stdGaussian F := by
      have hfst :
          (∫ p : E × F, ‖p.1‖
            ∂(stdGaussian E).prod (stdGaussian F)) =
            ∫ g : E, ‖g‖ ∂stdGaussian E := by
        rw [integral_prod _ (hEnorm.comp_fst _)]
        simp
      have hsnd :
          (∫ p : E × F, ‖p.2‖
            ∂(stdGaussian E).prod (stdGaussian F)) =
            ∫ h : F, ‖h‖ ∂stdGaussian F := by
        rw [integral_prod _ (hFnorm.comp_snd _)]
        simp
      rw [integral_add (hEnorm.comp_fst _) (hFnorm.comp_snd _),
        hfst, hsnd]

/-- The expected norm of a standard Gaussian vector is at most the square root of the dimension.

**Lean implementation helper.** -/
private theorem integral_norm_stdGaussian_le_sqrt_card_aux (n : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.sqrt n := by
  let ν := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hcoord (i : Fin n) :
      (∫ g : EuclideanSpace ℝ (Fin n), (g i) ^ 2 ∂ν) = 1 := by
    let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
    let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := (innerSL ℝ) u
    have hId : HasGaussianLaw
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ν :=
      IsGaussian.hasGaussianLaw_id
    have hmem : MemLp L 2 ν := by
      simpa [L, Function.comp_def] using (hId.map L).memLp_two
    have hv := variance_eq_sub hmem
    rw [integral_strongDual_stdGaussian L, variance_dual_stdGaussian L] at hv
    have hLu : ‖L‖ = 1 := by simp [L, u, innerSL_apply_norm]
    rw [hLu] at hv
    have hfun : ∀ g : EuclideanSpace ℝ (Fin n), L g = g i := by
      intro g
      simp [L, u, innerSL_apply_apply, PiLp.inner_apply]
    change 1 ^ 2 = (∫ x, (L x) ^ 2 ∂ν) - 0 ^ 2 at hv
    simp_rw [hfun] at hv
    nlinarith
  have hsq : (∫ g : EuclideanSpace ℝ (Fin n), ‖g‖ ^ 2 ∂ν) = n := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum]
    · simp_rw [hcoord]
      simp
    · intro i _
      let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
      let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := (innerSL ℝ) u
      have hId : HasGaussianLaw
          (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ν :=
        IsGaussian.hasGaussianLaw_id
      have hmem : MemLp L 2 ν := by
        simpa [L, Function.comp_def] using (hId.map L).memLp_two
      have hi := hmem.integrable_norm_pow' (p := 2)
      simpa [L, u, innerSL_apply_apply, PiLp.inner_apply,
        Real.norm_eq_abs, sq_abs] using hi
  have hIdMem : MemLp
      (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    IsGaussian.memLp_id ν 2 (by simp)
  have hnormMem : MemLp (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖g‖)
      (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using hIdMem.norm
  have honeMem : MemLp (fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using (memLp_const (p := ENNReal.ofReal (2 : ℝ)) (1 : ℝ))
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := ν) Real.HolderConjugate.two_two
    (f := fun g : EuclideanSpace ℝ (Fin n) ↦ ‖g‖)
    (g := fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ by norm_num)
    hnormMem honeMem
  simp only [Real.rpow_two] at h
  rw [hsq] at h
  simpa [ν, Real.sqrt_eq_rpow] using h



/-- An iid standard Gaussian `m x n` matrix has expected operator norm at most `sqrt m + sqrt n`. The proof compares the bilinear Gaussian process on signed finite sphere nets
with the sum of two canonical Gaussian processes via Sudakov--Fernique. The
rank-one Frobenius increment estimate is Exercise 7.10. Letting the net radius
tend to zero gives the sharp constant one. Empty row or column dimensions are
handled separately.

**Book Theorem 7.3.1.** -/
theorem gaussianMatrix_expected_opNorm (m n : ℕ) :
    (∫ A, HDP.matrixOpNorm A ∂gaussianMatrixMeasure m n) ≤
      Real.sqrt m + Real.sqrt n := by
  classical
  by_cases hm0 : m = 0
  · subst m
    have hzero (A : Matrix (Fin 0) (Fin n) ℝ) :
        HDP.matrixOpNorm A = 0 := by
      have hA : A = 0 := by
        ext i
        exact Fin.elim0 i
      simp [hA, HDP.matrixOpNorm]
    simp [hzero]
  by_cases hn0 : n = 0
  · subst n
    have hzero (A : Matrix (Fin m) (Fin 0) ℝ) :
        HDP.matrixOpNorm A = 0 := by
      have hA : A = 0 := by
        ext i j
        exact Fin.elim0 j
      simp [hA, HDP.matrixOpNorm]
    simp [hzero]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let L : ℝ := ∫ A, HDP.matrixOpNorm A ∂gaussianMatrixMeasure m n
  let S : ℝ := Real.sqrt m + Real.sqrt n
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  by_contra hnot
  have hgap : S < L := lt_of_not_ge hnot
  have hL : 0 < L := hS0.trans_lt hgap
  let ε : ℝ := (L - S) / (4 * L)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεhalf : 2 * ε < 1 := by
    have hεle : ε ≤ 1 / 4 := by
      dsimp [ε]
      have hLS : L - S ≤ L := by linarith
      have hL4 : 0 < 4 * L := by positivity
      rw [div_le_iff₀ hL4]
      nlinarith
    nlinarith
  have hden : 0 < 1 - 2 * ε := sub_pos.mpr hεhalf
  obtain ⟨N, hNne, hN⟩ := exists_finite_unitSphereNet_aux n hn ε hε
  obtain ⟨M, hMne, hM⟩ := exists_finite_unitSphereNet_aux m hm ε hε
  obtain ⟨u0, hu0⟩ := hNne
  obtain ⟨v0, hv0⟩ := hMne
  letI : Nonempty ↥N := ⟨⟨u0, hu0⟩⟩
  letI : Nonempty ↥M := ⟨⟨v0, hv0⟩⟩
  let u : SignedNetPointAux N → EuclideanSpace ℝ (Fin n) :=
    signedNetValueAux
  let v : SignedNetPointAux M → EuclideanSpace ℝ (Fin m) :=
    signedNetValueAux
  let uI : SignedNetPointAux N × SignedNetPointAux M →
      EuclideanSpace ℝ (Fin n) := fun i => u i.1
  let vI : SignedNetPointAux N × SignedNetPointAux M →
      EuclideanSpace ℝ (Fin m) := fun i => v i.2
  let a : SignedNetPointAux N × SignedNetPointAux M →
      EuclideanSpace ℝ (Fin m × Fin n) := fun i =>
    rankOneGaussianPointAux (uI i) (vI i)
  let X := canonicalGaussianProcess a
  let Y : (SignedNetPointAux N × SignedNetPointAux M) →
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ :=
    fun i p => inner ℝ (uI i) p.1 + inner ℝ (vI i) p.2
  have huI : ∀ i, ‖uI i‖ = 1 := by
    intro i
    exact signedNetValueAux_norm hN.1 i.1
  have hvI : ∀ i, ‖vI i‖ = 1 := by
    intro i
    exact signedNetValueAux_norm hM.1 i.2
  have hinc : ∀ i j,
      processIncrementSecondMoment
          (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) X i j ≤
        processIncrementSecondMoment
          ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin m)))) Y i j := by
    intro i j
    rw [show X = canonicalGaussianProcess a from rfl,
      canonicalGaussian_incrementSecondMoment_aux a i j]
    rw [show Y = (fun i (p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin m)) =>
          inner ℝ (uI i) p.1 + inner ℝ (vI i) p.2) from rfl,
      processIncrementSecondMoment_sum_inner_prod_aux uI vI i j]
    exact rankOneGaussianPointAux_sub_norm_sq_le
      (uI i) (uI j) (vI i) (vI j)
      (huI i) (huI j) (hvI i) (hvI j)
  have hcompare :
      expectedFiniteSupremum
          (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) X ≤
        expectedFiniteSupremum
          ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin m)))) Y := by
    apply sudakovFernique
    · exact canonicalGaussianProcess_isGaussian a
    · simpa [Y] using isGaussianProcess_sum_inner_prod_aux uI vI
    · exact canonicalGaussianProcess_centered a
    · intro i
      simpa [Y] using sum_inner_prod_centered_aux uI vI i
    · exact hinc
  have hYupper :
      expectedFiniteSupremum
          ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin m)))) Y ≤ S := by
    calc
      expectedFiniteSupremum
          ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin m)))) Y ≤
          (∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
              ∂stdGaussian (EuclideanSpace ℝ (Fin n))) +
            ∫ h : EuclideanSpace ℝ (Fin m), ‖h‖
              ∂stdGaussian (EuclideanSpace ℝ (Fin m)) := by
        simpa [Y] using
          expectedFiniteSupremum_sum_inner_prod_le_aux uI vI huI hvI
      _ ≤ Real.sqrt n + Real.sqrt m :=
        add_le_add (integral_norm_stdGaussian_le_sqrt_card_aux n)
          (integral_norm_stdGaussian_le_sqrt_card_aux m)
      _ = S := by dsimp [S]; ring
  have hXupper :
      expectedFiniteSupremum
          (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) X ≤ S :=
    hcompare.trans hYupper
  have hXcoord : ∀ i, Integrable (X i)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) := by
    intro i
    simpa [X] using
      ((canonicalGaussianProcess_isGaussian a).hasGaussianLaw_eval i).integrable
  have hXmax : Integrable (HDP.Chapter5.finiteMaximum X)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) :=
    integrable_finiteMaximum_aux X hXcoord
  have hpoint : ∀ g : EuclideanSpace ℝ (Fin m × Fin n),
      HDP.matrixOpNorm (unflattenEuclideanMatrixAux g) ≤
        HDP.Chapter5.finiteMaximum X g / (1 - 2 * ε) := by
    intro g
    let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      (unflattenEuclideanMatrixAux g).toEuclideanLin.toContinuousLinearMap
    have hUN := signedNetRange_isUnitSphereNet_aux hN
    have hVM := signedNetRange_isUnitSphereNet_aux hM
    have hval (i : SignedNetPointAux N × SignedNetPointAux M) :
        X i g = inner ℝ (T (uI i)) (vI i) := by
      simpa [X, a, canonicalGaussianProcess, T] using
        rankOneGaussianPointAux_inner (uI i) (vI i) g
    have habs (i : SignedNetPointAux N × SignedNetPointAux M) :
        |X i g| ≤ HDP.Chapter5.finiteMaximum X g := by
      let j : SignedNetPointAux N × SignedNetPointAux M :=
        ((i.1.1, !i.1.2), i.2)
      have hi : X i g ≤ HDP.Chapter5.finiteMaximum X g := by
        unfold HDP.Chapter5.finiteMaximum
        exact Finset.le_sup' (fun k => X k g) (Finset.mem_univ i)
      have hj : X j g ≤ HDP.Chapter5.finiteMaximum X g := by
        unfold HDP.Chapter5.finiteMaximum
        exact Finset.le_sup' (fun k => X k g) (Finset.mem_univ j)
      have hneg : X j g = -X i g := by
        rw [hval j, hval i]
        have huj : uI j = -uI i := by
          simpa [j, uI, u] using signedNetValueAux_flip i.1
        have hvj : vI j = vI i := rfl
        rw [huj, hvj, map_neg, inner_neg_left]
      rw [hneg] at hj
      exact abs_le.mpr ⟨by linarith, hi⟩
    have hR0 : 0 ≤ HDP.Chapter5.finiteMaximum X g := by
      let i0 : SignedNetPointAux N × SignedNetPointAux M :=
        Classical.choice inferInstance
      exact (abs_nonneg (X i0 g)).trans (habs i0)
    have hnet : ∀ x ∈ Set.range (signedNetValueAux (N := N)),
        ∀ y ∈ Set.range (signedNetValueAux (N := M)),
          |inner ℝ (T x) y| ≤ HDP.Chapter5.finiteMaximum X g := by
      intro x hx y hy
      obtain ⟨ix, rfl⟩ := hx
      obtain ⟨iy, rfl⟩ := hy
      let i : SignedNetPointAux N × SignedNetPointAux M := (ix, iy)
      have hi := habs i
      rw [hval i] at hi
      exact hi
    have hop := HDP.Chapter4.opNorm_le_of_bilinear_on_nets
      T hε.le hεhalf hUN hVM hR0 hnet
    simpa [T, HDP.matrixOpNorm, Matrix.l2_opNorm_def] using hop
  have hWint := integrable_unflattenEuclideanMatrixAux_opNorm m n
  have hquotInt : Integrable
      (fun g : EuclideanSpace ℝ (Fin m × Fin n) =>
        HDP.Chapter5.finiteMaximum X g / (1 - 2 * ε))
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) :=
    hXmax.div_const _
  have hintBound :
      (∫ g : EuclideanSpace ℝ (Fin m × Fin n),
          HDP.matrixOpNorm (unflattenEuclideanMatrixAux g)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) ≤
        (∫ g : EuclideanSpace ℝ (Fin m × Fin n),
          HDP.Chapter5.finiteMaximum X g
          ∂stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))) /
            (1 - 2 * ε) := by
    calc
      _ ≤ ∫ g : EuclideanSpace ℝ (Fin m × Fin n),
          HDP.Chapter5.finiteMaximum X g / (1 - 2 * ε)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)) :=
        integral_mono hWint hquotInt hpoint
      _ = _ := integral_div _ _
  have hbound : L ≤ S / (1 - 2 * ε) := by
    dsimp only [L]
    rw [gaussianMatrix_opNorm_integral_eq_euclidean_aux]
    exact hintBound.trans (div_le_div_of_nonneg_right
      (by simpa [expectedFiniteSupremum] using hXupper) hden.le)
  have hmul : L * (1 - 2 * ε) ≤ S :=
    (le_div_iff₀ hden).mp hbound
  have heps : 2 * ε * L = (L - S) / 2 := by
    dsimp [ε]
    field_simp [hL.ne']
    ring
  nlinarith


/-! ### Matrix vectorization and Gaussian concentration -/

/-- Row-major flattening, used only to identify the nested product law with
the standard product Gaussian on matrix entries.

**Lean implementation helper.** -/
private def flattenMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Fin m × Fin n → ℝ := fun p => A p.1 p.2

/-- The inverse row-major matrix vectorization.

**Lean implementation helper.** -/
private def unflattenMatrix {m n : ℕ} (x : Fin m × Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => x (i, j)

/-- Unflattening the coordinate function of a matrix recovers the original matrix.

**Lean implementation helper.** -/
@[simp]
private lemma unflattenMatrix_flattenMatrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    unflattenMatrix (flattenMatrix A) = A := by
  rfl

/-- Flattening a real matrix into its coordinate function is measurable.

**Lean implementation helper.** -/
private lemma flattenMatrix_measurable {m n : ℕ} :
    Measurable (flattenMatrix : Matrix (Fin m) (Fin n) ℝ →
      (Fin m × Fin n → ℝ)) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- Flattening sends the Gaussian matrix measure to the product standard Gaussian coordinate measure.

**Lean implementation helper.** -/
private lemma flattenMatrix_map_gaussianMatrixMeasure (m n : ℕ) :
    (gaussianMatrixMeasure m n).map flattenMatrix =
      Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
  change (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map flattenMatrix = _
  have h := Measure.infinitePi_map_curry_symm
    (fun _ : Fin m => fun _ : Fin n => gaussianReal 0 1)
  have hfun : flattenMatrix =
      ⇑(MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm := rfl
  rw [hfun]
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  congr 2

/-- The operator norm after unflattening is one-Lipschitz with respect to the Euclidean coordinate norm.

**Lean implementation helper.** -/
private lemma matrixOpNorm_unflatten_lipschitz {m n : ℕ}
    (x y : Fin m × Fin n → ℝ) :
    |HDP.matrixOpNorm (unflattenMatrix x) -
        HDP.matrixOpNorm (unflattenMatrix y)| ≤
      Real.sqrt (∑ p, (x p - y p) ^ 2) := by
  classical
  change |‖unflattenMatrix x‖ - ‖unflattenMatrix y‖| ≤ _
  calc
    |‖unflattenMatrix x‖ - ‖unflattenMatrix y‖|
        ≤ ‖unflattenMatrix x - unflattenMatrix y‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ HDP.matrixFrobeniusNorm (unflattenMatrix x - unflattenMatrix y) :=
      HDP.Chapter4.operatorNorm_le_frobeniusNorm _
    _ = Real.sqrt (∑ p, (x p - y p) ^ 2) := by
      rw [HDP.matrixFrobeniusNorm]
      congr 1
      simp only [unflattenMatrix, Matrix.sub_apply]
      rw [← Finset.sum_product']
      simp

/-- The operator norm of an unflattened coordinate function is measurable.

**Lean implementation helper.** -/
private lemma matrixOpNorm_unflatten_measurable {m n : ℕ} :
    Measurable (fun x : Fin m × Fin n → ℝ =>
      HDP.matrixOpNorm (unflattenMatrix x)) := by
  classical
  apply Continuous.measurable
  have hU : Continuous (unflattenMatrix : (Fin m × Fin n → ℝ) →
      Matrix (Fin m) (Fin n) ℝ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply (i, j)
  change Continuous ((fun A : Matrix (Fin m) (Fin n) ℝ => ‖A‖) ∘
    unflattenMatrix)
  exact continuous_norm.comp hU

/-- The Gaussian matrix norm has Gaussian upper tails around `sqrt m + sqrt n`. The proof vectorizes the matrix product law, verifies that operator norm is
one-Lipschitz for the Euclidean/Frobenius metric, and applies the sharp finite
product-Gaussian concentration theorem. Its `exp (-t²/2)` conclusion is then
weakened to the book's conservative displayed constant.

**Book Corollary 7.3.2.** -/
theorem gaussianMatrix_opNorm_tail (m n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianMatrixMeasure m n).real
        {A | Real.sqrt m + Real.sqrt n + t ≤ HDP.matrixOpNorm A} ≤
      2 * Real.exp (-(t ^ 2) / 40) := by
  classical
  let γ : Measure (Fin m × Fin n → ℝ) :=
    Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)
  let W : (Fin m × Fin n → ℝ) → ℝ := fun x =>
    HDP.matrixOpNorm (unflattenMatrix x)
  have hWm : Measurable W := matrixOpNorm_unflatten_measurable
  have hWLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2) :=
    matrixOpNorm_unflatten_lipschitz
  have hmap : (gaussianMatrixMeasure m n).map flattenMatrix = γ := by
    exact flattenMatrix_map_gaussianMatrixMeasure m n
  have hLaw : HasLaw flattenMatrix γ (gaussianMatrixMeasure m n) :=
    ⟨flattenMatrix_measurable.aemeasurable, hmap⟩
  have hmean : (∫ x, W x ∂γ) =
      ∫ A, HDP.matrixOpNorm A ∂gaussianMatrixMeasure m n := by
    have h := hLaw.integral_comp hWm.aestronglyMeasurable
    simpa [W, Function.comp_def] using h.symm
  have hmean_le : (∫ x, W x ∂γ) ≤ Real.sqrt m + Real.sqrt n := by
    rw [hmean]
    exact gaussianMatrix_expected_opNorm m n
  have htail := MatrixConcentration.gaussian_lipschitz_tail_one
    (Fin m × Fin n) W hWLip hWm ht
  have htail' : γ.real
      {x | (∫ y, W y ∂γ) + t ≤ W x} ≤ Real.exp (-(t ^ 2) / 2) := by
    simpa [γ] using htail
  have hsubset : {x | Real.sqrt m + Real.sqrt n + t ≤ W x} ⊆
      {x | (∫ y, W y ∂γ) + t ≤ W x} := by
    intro x hx
    dsimp only [Set.mem_setOf_eq] at hx ⊢
    linarith
  have hflat : γ.real {x | Real.sqrt m + Real.sqrt n + t ≤ W x} ≤
      Real.exp (-(t ^ 2) / 2) :=
    (measureReal_mono hsubset).trans htail'
  have hpres : MeasurePreserving flattenMatrix
      (gaussianMatrixMeasure m n) γ :=
    ⟨flattenMatrix_measurable, hmap⟩
  have hevent : (gaussianMatrixMeasure m n).real
      {A | Real.sqrt m + Real.sqrt n + t ≤ HDP.matrixOpNorm A} =
      γ.real {x | Real.sqrt m + Real.sqrt n + t ≤ W x} := by
    have hs : MeasurableSet {x | Real.sqrt m + Real.sqrt n + t ≤ W x} :=
      hWm measurableSet_Ici
    have hp := hpres.measureReal_preimage hs.nullMeasurableSet
    simpa [W] using hp
  rw [hevent]
  calc
    γ.real {x | Real.sqrt m + Real.sqrt n + t ≤ W x}
        ≤ Real.exp (-(t ^ 2) / 2) := hflat
    _ ≤ Real.exp (-(t ^ 2) / 40) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t]
    _ ≤ 2 * Real.exp (-(t ^ 2) / 40) := by
      nlinarith [Real.exp_pos (-(t ^ 2) / 40)]

/-! ### The sharp radial mean recurrence -/

/-- The mean Euclidean norm of a standard Gaussian in dimension `n`.

**Lean implementation helper.** -/
private def gaussianNormMean (n : ℕ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Expresses the mean norm of a standard Gaussian vector as a radial volume integral.

**Lean implementation helper.** -/
private lemma gaussianNormMean_eq_volume {n : ℕ} (_hn : 0 < n) :
    gaussianNormMean n =
      (HDP.gaussianRadialNormalizer (EuclideanSpace ℝ (Fin n)))⁻¹ *
        ∫ x : EuclideanSpace ℝ (Fin n),
          ‖x‖ * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp _hn
  rw [gaussianNormMean, ← HDP.gaussianRadialMeasure_eq_stdGaussian E,
    HDP.gaussianRadialMeasure]
  rw [integral_withDensity_eq_integral_smul
    (HDP.measurable_gaussianRadialDensity E)]
  simp_rw [NNReal.smul_def, HDP.coe_gaussianRadialDensity]
  rw [← integral_const_mul]
  apply congrArg
  funext x
  ring

/-- Evaluates the radial volume integral associated with the Gaussian norm mean.

**Lean implementation helper.** -/
private lemma gaussianNormRadialVolume {n : ℕ} (hn : 0 < n) :
    (∫ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) =
      (n : ℝ) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real
          (Metric.ball 0 1) *
        ∫ y in Set.Ioi (0 : ℝ),
          y ^ (n - 1) * (y * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have h := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun y : ℝ ↦ y * Real.exp (-(1 / 2 : ℝ) * y ^ 2))
  simpa [finrank_euclideanSpace, nsmul_eq_mul, smul_eq_mul,
    mul_assoc] using h

/-- Identifies the real Euclidean unit ball used in the radial integration formula.

**Lean implementation helper.** -/
private lemma euclideanUnitBallReal {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real
        (Metric.ball 0 1) =
      Real.sqrt Real.pi ^ n /
        Real.Gamma ((n : ℝ) / 2 + 1) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [Measure.real, EuclideanSpace.volume_ball]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal]
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (Real.Gamma_pos_of_pos (by positivity)).le

/-- Evaluates the radial Gaussian integral in terms of Gamma-function constants.

**Lean implementation helper.** -/
private lemma gaussianNormRadialIntegral {n : ℕ} (hn : 0 < n) :
    (∫ y in Set.Ioi (0 : ℝ),
        y ^ (n - 1) * (y * Real.exp (-(1 / 2 : ℝ) * y ^ 2))) =
      (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
        Real.Gamma (((n : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (n : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num)
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
    (by norm_num)
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 ≤ y := hy.le
  change y ^ (n - 1) * (y * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
    y ^ (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * y ^ (2 : ℝ))
  rw [Real.rpow_natCast, Real.rpow_two]
  calc
    y ^ (n - 1) * (y * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
        y ^ ((n - 1) + 1) * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
      rw [pow_succ]
      ring
    _ = y ^ n * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]

/-- Rewrites a power of the square root of π as a half-power of π.

**Lean implementation helper.** -/
private lemma sqrtPi_pow (n : ℕ) :
    Real.sqrt Real.pi ^ n =
      Real.pi ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast Real.pi_pos.le]
  congr 1
  ring

/-- Simplifies the dimensional coefficient in the Gaussian radial integral.

**Lean implementation helper.** -/
private lemma radialPowerCoefficient (n : ℕ) :
    ((Real.pi / (1 / 2 : ℝ)) ^ ((n : ℝ) / 2))⁻¹ *
        (Real.sqrt Real.pi ^ n) *
        (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) =
      Real.sqrt 2 := by
  rw [sqrtPi_pow]
  rw [Real.div_rpow Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hpi : Real.pi ^ ((n : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hhalf : (1 / 2 : ℝ) ^ ((n : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [inv_div]
  field_simp
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) ^ ((n : ℝ) / 2 + -(((n : ℝ) + 1) / 2)) =
        (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      congr 1
      ring
    _ = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = (Real.sqrt (1 / 2 : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt 2 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) 2]
      norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Gives the Gamma-function formula for the mean norm of a standard Gaussian vector.

**Lean implementation helper.** -/
private lemma gaussianNormMean_formula {n : ℕ} (hn : 0 < n) :
    gaussianNormMean n =
      Real.sqrt 2 * Real.Gamma (((n : ℝ) + 1) / 2) /
        Real.Gamma ((n : ℝ) / 2) := by
  rw [gaussianNormMean_eq_volume hn, gaussianNormRadialVolume hn,
    euclideanUnitBallReal hn, gaussianNormRadialIntegral hn]
  simp only [HDP.gaussianRadialNormalizer, finrank_euclideanSpace,
    Fintype.card_fin]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn2pos : 0 < (n : ℝ) / 2 := by positivity
  have hGamma0 : Real.Gamma ((n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos hn2pos).ne'
  have hGammaAdd : Real.Gamma ((n : ℝ) / 2 + 1) =
      ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) :=
    Real.Gamma_add_one hn2pos.ne'
  rw [hGammaAdd]
  have hpow := radialPowerCoefficient n
  norm_num at hpow ⊢
  have hnormalizer : (Real.pi * 2) ^ ((n : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (mul_pos Real.pi_pos (by norm_num)) _).ne'
  field_simp [hnormalizer] at hpow ⊢
  nlinarith

/-- The Gaussian norm mean is strictly positive.

**Lean implementation helper.** -/
private lemma gaussianNormMean_pos {n : ℕ} (hn : 0 < n) :
    0 < gaussianNormMean n := by
  rw [gaussianNormMean_formula hn]
  positivity

/-- Relates consecutive Gaussian norm means through the Gamma recurrence.

**Lean implementation helper.** -/
private lemma gaussianNormMean_mul_succ {n : ℕ} (hn : 0 < n) :
    gaussianNormMean n * gaussianNormMean (n + 1) = n := by
  rw [gaussianNormMean_formula hn,
    gaussianNormMean_formula (Nat.zero_lt_succ n)]
  have hn2pos : 0 < (n : ℝ) / 2 := by positivity
  have hmidpos : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have hG0 : Real.Gamma ((n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos hn2pos).ne'
  have hGmid : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos hmidpos).ne'
  have hGadd : Real.Gamma (((n : ℝ) + 2) / 2) =
      ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) := by
    rw [show ((n : ℝ) + 2) / 2 = (n : ℝ) / 2 + 1 by ring]
    exact Real.Gamma_add_one hn2pos.ne'
  have hGadd' : Real.Gamma (((n : ℝ) + 1 + 1) / 2) =
      ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) := by
    rw [show ((n : ℝ) + 1 + 1) / 2 = ((n : ℝ) + 2) / 2 by ring]
    exact hGadd
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at ⊢
  rw [hGadd']
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

/-- Relates Gaussian norm means whose dimensions differ by two.

**Lean implementation helper.** -/
private lemma gaussianNormMean_add_two {n : ℕ} (hn : 0 < n) :
    gaussianNormMean (n + 2) =
      ((n : ℝ) + 1) / n * gaussianNormMean n := by
  have hprod0 := gaussianNormMean_mul_succ hn
  have hprod1 := gaussianNormMean_mul_succ (n := n + 1) (Nat.zero_lt_succ n)
  have hmidpos := gaussianNormMean_pos (n := n + 1) (Nat.zero_lt_succ n)
  push_cast at hprod0 hprod1 ⊢
  field_simp
  nlinarith

/-- The squared Gaussian norm mean is at most the dimension.

**Lean implementation helper.** -/
private lemma gaussianNormMean_sq_le {n : ℕ} (hn : 0 < n) :
    gaussianNormMean n ^ 2 ≤ n := by
  rw [gaussianNormMean_formula hn]
  let x : ℝ := (n : ℝ) / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := x) (t := x + 1) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    hx (by positivity) (by norm_num) (by norm_num) (by norm_num)
  have harg : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (x + 1) =
      ((n : ℝ) + 1) / 2 := by dsimp [x]; ring
  rw [harg, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hconv
  have hG0pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hG1pos : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hGmpos : 0 < Real.Gamma (((n : ℝ) + 1) / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hsqrt0 : Real.sqrt (Real.Gamma x) ^ 2 = Real.Gamma x :=
    Real.sq_sqrt hG0pos.le
  have hsqrt1 : Real.sqrt (Real.Gamma (x + 1)) ^ 2 = Real.Gamma (x + 1) :=
    Real.sq_sqrt hG1pos.le
  have hsquare : Real.Gamma (((n : ℝ) + 1) / 2) ^ 2 ≤
      Real.Gamma x * Real.Gamma (x + 1) := by
    have hnonneg : 0 ≤
        (Real.sqrt (Real.Gamma x) * Real.sqrt (Real.Gamma (x + 1)) -
          Real.Gamma (((n : ℝ) + 1) / 2)) *
        (Real.sqrt (Real.Gamma x) * Real.sqrt (Real.Gamma (x + 1)) +
          Real.Gamma (((n : ℝ) + 1) / 2)) :=
      mul_nonneg (sub_nonneg.mpr hconv)
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hGmpos.le)
    nlinarith
  have hGadd : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one hx.ne'
  rw [hGadd] at hsquare
  have hG0ne : Real.Gamma x ≠ 0 := hG0pos.ne'
  dsimp [x] at hsquare ⊢
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

/-- Defines the gap between the Gaussian norm mean and the square root of the dimension.

**Lean implementation helper.** -/
private def gaussianNormDefect (n : ℕ) : ℝ :=
  (n : ℝ) - gaussianNormMean n ^ 2

/-- The Gaussian norm defect is nonnegative.

**Lean implementation helper.** -/
private lemma gaussianNormDefect_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ gaussianNormDefect n := by
  exact sub_nonneg.mpr (gaussianNormMean_sq_le hn)

/-- Expresses the Gaussian norm defect two dimensions later in terms of the earlier defect.

**Lean implementation helper.** -/
private lemma gaussianNormDefect_add_two {n : ℕ} (hn : 0 < n) :
    gaussianNormDefect (n + 2) =
      (((n : ℝ) + 1) / n) ^ 2 * gaussianNormDefect n - 1 / n := by
  rw [gaussianNormDefect, gaussianNormDefect, gaussianNormMean_add_two hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp
  ring

/-- A rational lower barrier for the radial Gaussian variance defect.

**Lean implementation helper.** -/
private def gaussianNormDefectBarrier (n : ℕ) : ℝ :=
  (n : ℝ) * (4 * n + 9) / (8 * n ^ 2 + 20 * n + 9)

/-- The Gaussian norm defect barrier is nonnegative.

**Lean implementation helper.** -/
private lemma gaussianNormDefectBarrier_nonneg (n : ℕ) :
    0 ≤ gaussianNormDefectBarrier n := by
  rw [gaussianNormDefectBarrier]
  positivity

/-- The explicit lower barrier for the Gaussian norm defect is at most one half.

**Lean implementation helper.** -/
private lemma gaussianNormDefectBarrier_le_half (n : ℕ) :
    gaussianNormDefectBarrier n ≤ 1 / 2 := by
  rw [gaussianNormDefectBarrier]
  have hden : 0 < (8 : ℝ) * n ^ 2 + 20 * n + 9 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (n : ℝ)]

/-- Gives the two-step recurrence for the excess above the Gaussian norm-defect barrier.

**Lean implementation helper.** -/
private lemma gaussianNormDefectExcess_add_two {n : ℕ} (hn : 0 < n) :
    gaussianNormDefect (n + 2) - gaussianNormDefectBarrier (n + 2) =
      (((n : ℝ) + 1) / n) ^ 2 *
          (gaussianNormDefect n - gaussianNormDefectBarrier n) -
        72 * ((n : ℝ) + 2) /
          ((8 * (n : ℝ) ^ 2 + 20 * n + 9) *
            (8 * (n : ℝ) ^ 2 + 52 * n + 81)) := by
  rw [gaussianNormDefect_add_two hn, gaussianNormDefectBarrier,
    gaussianNormDefectBarrier]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hden0 : (8 : ℝ) * n ^ 2 + 20 * n + 9 ≠ 0 := by positivity
  have hden2 : (8 : ℝ) * n ^ 2 + 52 * n + 81 ≠ 0 := by positivity
  field_simp
  ring

/-- The Gaussian norm defect is bounded below by the explicit dimensional barrier.

**Lean implementation helper.** -/
private lemma gaussianNormDefect_ge_barrier {n : ℕ} (hn : 0 < n) :
    gaussianNormDefectBarrier n ≤ gaussianNormDefect n := by
  by_contra hnot
  have he0 : gaussianNormDefect n - gaussianNormDefectBarrier n < 0 := by
    exact sub_neg.mpr (lt_of_not_ge hnot)
  have hchain : ∀ k : ℕ,
      gaussianNormDefect (n + 2 * k) -
          gaussianNormDefectBarrier (n + 2 * k) ≤
        (((n : ℝ) + 2 * k) / n) *
          (gaussianNormDefect n - gaussianNormDefectBarrier n) := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.cast_zero, mul_zero, add_zero]
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        simp [div_self hnR]
    | succ k ih =>
        let j : ℕ := n + 2 * k
        have hjn : n ≤ j := by dsimp [j]; omega
        have hj : 0 < j := hn.trans_le hjn
        have hrel := gaussianNormDefectExcess_add_two (n := j) hj
        have hrem : 0 ≤
            72 * ((j : ℝ) + 2) /
              ((8 * (j : ℝ) ^ 2 + 20 * j + 9) *
                (8 * (j : ℝ) ^ 2 + 52 * j + 81)) := by positivity
        have hejnonpos :
            gaussianNormDefect j - gaussianNormDefectBarrier j ≤ 0 := by
          have hcoefpos : 0 < (((n : ℝ) + 2 * k) / n) := by positivity
          have hupperneg : (((n : ℝ) + 2 * k) / n) *
              (gaussianNormDefect n - gaussianNormDefectBarrier n) < 0 :=
            mul_neg_of_pos_of_neg hcoefpos he0
          have hij : n + 2 * k = j := rfl
          rw [hij] at ih
          exact ih.trans hupperneg.le
        have hfactor : ((j : ℝ) + 2) / j ≤
            (((j : ℝ) + 1) / j) ^ 2 := by
          have hjR : (0 : ℝ) < j := by exact_mod_cast hj
          rw [div_le_iff₀ hjR]
          field_simp
          nlinarith
        have hstep :
            gaussianNormDefect (j + 2) - gaussianNormDefectBarrier (j + 2) ≤
              (((j : ℝ) + 2) / j) *
                (gaussianNormDefect j - gaussianNormDefectBarrier j) := by
          calc
            _ ≤ (((j : ℝ) + 1) / j) ^ 2 *
                (gaussianNormDefect j - gaussianNormDefectBarrier j) := by
              rw [hrel]
              linarith
            _ ≤ (((j : ℝ) + 2) / j) *
                (gaussianNormDefect j - gaussianNormDefectBarrier j) :=
              mul_le_mul_of_nonpos_right hfactor hejnonpos
        have hcoef : 0 ≤ ((j : ℝ) + 2) / j := by positivity
        have hcombine := hstep.trans
          (mul_le_mul_of_nonneg_left ih hcoef)
        have hjcast : (j : ℝ) = (n : ℝ) + 2 * k := by
          dsimp [j]
          push_cast
          ring
        have hfinal :
          gaussianNormDefect (j + 2) - gaussianNormDefectBarrier (j + 2) ≤
            (((n : ℝ) + 2 * (k + 1)) / n) *
              (gaussianNormDefect n - gaussianNormDefectBarrier n) := by
          calc
            _ ≤ (((j : ℝ) + 2) / j) *
                ((((n : ℝ) + 2 * k) / n) *
                  (gaussianNormDefect n - gaussianNormDefectBarrier n)) := hcombine
            _ = (((n : ℝ) + 2 * (k + 1)) / n) *
                (gaussianNormDefect n - gaussianNormDefectBarrier n) := by
              rw [hjcast]
              have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
              field_simp
              ring
        have hidx : n + 2 * (k + 1) = j + 2 := by
          dsimp [j]
          omega
        rw [hidx]
        simpa only [Nat.cast_add, Nat.cast_one] using hfinal
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((n : ℝ) /
      (-4 * (gaussianNormDefect n - gaussianNormDefectBarrier n)))
  have hkpos : 0 < (k : ℝ) := by
    have hquotpos : 0 < (n : ℝ) /
        (-4 * (gaussianNormDefect n - gaussianNormDefectBarrier n)) := by
      exact div_pos (by exact_mod_cast hn)
        (mul_pos_of_neg_of_neg (by norm_num) he0)
    linarith
  have hfar := hchain k
  have hfarLower : -(1 / 2 : ℝ) ≤
      gaussianNormDefect (n + 2 * k) -
        gaussianNormDefectBarrier (n + 2 * k) := by
    have hq := gaussianNormDefect_nonneg (n := n + 2 * k) (by omega)
    have hB := gaussianNormDefectBarrier_le_half (n + 2 * k)
    linarith
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper : (((n : ℝ) + 2 * k) / n) *
      (gaussianNormDefect n - gaussianNormDefectBarrier n) <
        -(1 / 2 : ℝ) := by
    have hdenpos : 0 < -4 *
        (gaussianNormDefect n - gaussianNormDefectBarrier n) :=
      mul_pos_of_neg_of_neg (by norm_num) he0
    rw [div_lt_iff₀ hdenpos] at hk
    field_simp
    nlinarith
  linarith

/-- The Gaussian norm defect controls the increment of the Gaussian norm mean relative to square-root growth.

**Lean implementation helper.** -/
private lemma gaussianNormDefect_controls_increment {n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt (n + 1) - Real.sqrt n) * gaussianNormMean n ≤
      gaussianNormDefect n := by
  let N : ℝ := n
  let q : ℝ := gaussianNormDefect n
  let b : ℝ := gaussianNormDefectBarrier n
  let d : ℝ := Real.sqrt (n + 1) - Real.sqrt n
  let mu : ℝ := gaussianNormMean n
  have hn0 : 0 < n := by omega
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn0
  have hmu : 0 < mu := gaussianNormMean_pos hn0
  have hq : b ≤ q := gaussianNormDefect_ge_barrier hn0
  have hb0 : 0 ≤ b := gaussianNormDefectBarrier_nonneg n
  have hq0 : 0 ≤ q := gaussianNormDefect_nonneg hn0
  have hmuSq : mu ^ 2 = N - q := by
    dsimp [mu, N, q, gaussianNormDefect]
    ring
  have hsqrtn : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hsqrtn1 : Real.sqrt (N + 1) ^ 2 = N + 1 :=
    Real.sq_sqrt (by positivity)
  have hsqrtprod : Real.sqrt N * Real.sqrt (N + 1) =
      Real.sqrt (N * (N + 1)) := by
    rw [Real.sqrt_mul hN.le]
  have hsqrtprod_ge : N ≤ Real.sqrt (N * (N + 1)) := by
    have hsq : Real.sqrt (N * (N + 1)) ^ 2 = N * (N + 1) :=
      Real.sq_sqrt (mul_nonneg hN.le (by positivity))
    have hs0 : 0 ≤ Real.sqrt (N * (N + 1)) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt (N * (N + 1)) - N)]
  have hsumSq : 4 * N + 1 ≤
      (Real.sqrt N + Real.sqrt (N + 1)) ^ 2 := by
    calc
      4 * N + 1 ≤ N + 2 * Real.sqrt (N * (N + 1)) + (N + 1) := by
        nlinarith
      _ = (Real.sqrt N + Real.sqrt (N + 1)) ^ 2 := by
        rw [add_sq, hsqrtn, hsqrtn1, ← hsqrtprod]
        ring
  have hsumPos : 0 < Real.sqrt N + Real.sqrt (N + 1) := by positivity
  have hdId : d * (Real.sqrt N + Real.sqrt (N + 1)) = 1 := by
    dsimp [d, N]
    nlinarith [hsqrtn, hsqrtn1]
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n))
  have hdSq : d ^ 2 * (4 * N + 1) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hsumSq (sq_nonneg d)
    have hidSq : d ^ 2 *
        (Real.sqrt N + Real.sqrt (N + 1)) ^ 2 = 1 := by
      nlinarith [hdId]
    nlinarith
  have hbFormula : b = N * (4 * N + 9) /
      (8 * N ^ 2 + 20 * N + 9) := by
    dsimp [b, N, gaussianNormDefectBarrier]
  have hbSq : (N - b) / (4 * N + 1) ≤ b ^ 2 := by
    rw [hbFormula]
    have hD : 0 < 8 * N ^ 2 + 20 * N + 9 := by positivity
    have h4 : 0 < 4 * N + 1 := by positivity
    field_simp
    have hN2 : (2 : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast hn
    nlinarith [sq_nonneg (4 * N - 2)]
  have hNq : N - q ≤ N - b := by linarith
  have hdmuSq : (d * mu) ^ 2 ≤ b ^ 2 := by
    have h4pos : 0 < 4 * N + 1 := by positivity
    have hdBound : d ^ 2 ≤ 1 / (4 * N + 1) := by
      rw [le_div_iff₀ h4pos]
      nlinarith
    calc
      (d * mu) ^ 2 = d ^ 2 * (N - q) := by rw [mul_pow, hmuSq]
      _ ≤ d ^ 2 * (N - b) := by
        exact mul_le_mul_of_nonneg_left hNq (sq_nonneg d)
      _ ≤ (1 / (4 * N + 1)) * (N - b) := by
        exact mul_le_mul_of_nonneg_right hdBound (by
          have hbhalf := gaussianNormDefectBarrier_le_half n
          dsimp [b, N] at hbhalf ⊢
          nlinarith)
      _ ≤ b ^ 2 := by simpa [div_eq_mul_inv, mul_comm] using hbSq
  have hdb : d * mu ≤ b := by
    have hdm0 : 0 ≤ d * mu := mul_nonneg hd0 hmu.le
    nlinarith
  exact hdb.trans hq

/-- The Gaussian norm mean minus the square root of dimension is nonincreasing in the dimension.

**Lean implementation helper.** -/
private lemma gaussianNormMean_sub_sqrt_mono_succ {n : ℕ} (hn : 2 ≤ n) :
    gaussianNormMean n - Real.sqrt n ≤
      gaussianNormMean (n + 1) - Real.sqrt (n + 1) := by
  have hn0 : 0 < n := by omega
  have hmu := gaussianNormMean_pos hn0
  have hprod := gaussianNormMean_mul_succ hn0
  have hcontrol := gaussianNormDefect_controls_increment hn
  rw [gaussianNormDefect] at hcontrol
  have hquot : gaussianNormMean (n + 1) =
      (n : ℝ) / gaussianNormMean n := by
    apply (eq_div_iff hmu.ne').2
    nlinarith
  rw [hquot]
  rw [le_sub_iff_add_le, le_div_iff₀ hmu]
  nlinarith

/-- The Gaussian radial-mean correction is eventually monotone in natural dimension. The dimension is natural-valued, so the source's phrase “increasing on
`[C,∞)`” is expressed as eventual monotonicity of the sequence. The proof
computes the exact chi mean by polar integration, uses log-convexity of Gamma,
and controls the resulting two-step recurrence with an explicit rational
barrier. In fact the conclusion holds from dimension `2` onward.

**Book Exercise 7.12.** -/
theorem exercise_7_12_gaussianNorm_eventuallyMonotone :
    ∃ C : ℕ, ∀ ⦃n k : ℕ⦄, C ≤ n → n ≤ k →
      (∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) - Real.sqrt n ≤
        (∫ g : EuclideanSpace ℝ (Fin k), ‖g‖
          ∂stdGaussian (EuclideanSpace ℝ (Fin k))) - Real.sqrt k := by
  refine ⟨2, ?_⟩
  intro n k hn hnk
  change gaussianNormMean n - Real.sqrt n ≤
    gaussianNormMean k - Real.sqrt k
  induction k, hnk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hnk ih =>
      exact ih.trans (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          gaussianNormMean_sub_sqrt_mono_succ (hn.trans hnk))

end

end HDP.Chapter7

end Source_06_GaussianMatrices

/-! ## Material formerly in `07_SudakovInequality.lean` -/

section Source_07_SudakovInequality

/-!
# Book Chapter 7, §7.4: Sudakov minoration

The authoritative arbitrary-index supremum is extended-real and is defined as
the supremum over all nonempty finite indexed subfamilies, exactly following
Remark 7.2.1.  The finite theorem retains Mathlib's `ℕ∞` covering number and
requires an explicit finiteness certificate before casting to `ℕ`/`ℝ`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter7

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Evaluates the expected absolute difference of two independent standard Gaussian variables.

**Lean implementation helper.** -/
private lemma integral_abs_sub_iid_standardGaussian
    {g : ℕ → Ω → ℝ}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) :
    (∫ ω, |g 0 ω - g 1 ω| ∂μ) = 2 / Real.sqrt Real.pi := by
  let d : Ω → ℝ := fun ω => g 0 ω - g 1 ω
  let z : Ω → ℝ := fun ω => d ω / Real.sqrt 2
  have h01 : IndepFun (g 0) (g 1) μ := hi.indepFun (by norm_num)
  have h0neg1 : IndepFun (g 0) (fun ω => -g 1 ω) μ := by
    convert h01.comp measurable_id measurable_neg using 1 <;> rfl
  have hneg1 : HasLaw (fun ω => -g 1 ω) (gaussianReal 0 1) μ := by
    change HasLaw (-g 1) (gaussianReal 0 1) μ
    simpa using gaussianReal_neg (hg 1)
  have hdmap : μ.map d = gaussianReal 0 2 := by
    have h := gaussianReal_add_gaussianReal_of_indepFun h0neg1
      (hg 0).map_eq hneg1.map_eq
    rw [show d = g 0 + fun ω => -g 1 ω by
      funext ω
      simp [d, sub_eq_add_neg]]
    simpa only [zero_add, show (1 : ℝ≥0) + 1 = 2 by norm_num] using h
  have hd : HasLaw d (gaussianReal 0 2) μ :=
    ⟨((hgm 0).sub (hgm 1)).aemeasurable, hdmap⟩
  have hz : HasLaw z (gaussianReal 0 1) μ := by
    have h := gaussianReal_div_const hd (Real.sqrt 2)
    have hv : (2 : ℝ≥0) /
        .mk (Real.sqrt 2 ^ 2) (sq_nonneg _) = 1 := by
      ext
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hv] at h
    simpa [z] using h
  have hzabs := HDP.Chapter2.gaussian_absolute_moment hz
    (p := (1 : ℝ)) (by norm_num)
  have hzabs' : (∫ ω, |z ω| ∂μ) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [show Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) by
      rw [← Real.sqrt_eq_rpow]]
    simpa [Real.rpow_one, Real.Gamma_one] using hzabs
  have hdz : ∀ ω, |d ω| = Real.sqrt 2 * |z ω| := by
    intro ω
    dsimp [z]
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)]
  calc
    (∫ ω, |g 0 ω - g 1 ω| ∂μ) = ∫ ω, |d ω| ∂μ := rfl
    _ = ∫ ω, Real.sqrt 2 * |z ω| ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ hdz
    _ = Real.sqrt 2 * ∫ ω, |z ω| ∂μ := by rw [integral_const_mul]
    _ = 2 / Real.sqrt Real.pi := by
      rw [hzabs']
      rw [← mul_div_assoc, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The expected maximum of at least two independent standard Gaussians is at least the reciprocal square root of π.

**Lean implementation helper.** -/
private lemma gaussianMaxSeq_expectation_ge_inv_sqrt_pi
    {g : ℕ → Ω → ℝ}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) (n : ℕ) :
    1 / Real.sqrt Real.pi ≤
      ∫ ω, HDP.Chapter2.gaussianMaxSeq g n ω ∂μ := by
  letI : IsProbabilityMeasure μ := (hg 0).isProbabilityMeasure
  let P : Ω → ℝ := fun ω => max (g 0 ω) (g 1 ω)
  have hgint : ∀ i, Integrable (g i) μ := by
    intro i
    have hmem := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
      ((hg i).measurePreserving (hgm i))
    simpa [Function.comp_def] using hmem.integrable (by norm_num)
  have hPint : Integrable P μ := by
    change Integrable (g 0 ⊔ g 1) μ
    exact Integrable.sup (hgint 0) (hgint 1)
  have hMint := HDP.Chapter2.gaussianMaxSeq_integrable hgm hg n
  have hpoint : ∀ ω, P ω ≤ HDP.Chapter2.gaussianMaxSeq g n ω := by
    intro ω
    apply max_le
    · exact Finset.le_sup' (fun i : ℕ => g i ω)
        (by simp : 0 ∈ Finset.range (n + 2))
    · exact Finset.le_sup' (fun i : ℕ => g i ω)
        (by simp : 1 ∈ Finset.range (n + 2))
  have hmeans : (∫ ω, g 0 ω ∂μ) = 0 ∧ (∫ ω, g 1 ω ∂μ) = 0 := by
    constructor
    · calc
        (∫ ω, g 0 ω ∂μ) = ∫ x, x ∂gaussianReal 0 1 := by
          simpa [Function.comp_def] using
            (hg 0).integral_comp (f := id) (by fun_prop)
        _ = 0 := integral_id_gaussianReal
    · calc
        (∫ ω, g 1 ω ∂μ) = ∫ x, x ∂gaussianReal 0 1 := by
          simpa [Function.comp_def] using
            (hg 1).integral_comp (f := id) (by fun_prop)
        _ = 0 := integral_id_gaussianReal
  have hP : (∫ ω, P ω ∂μ) = 1 / Real.sqrt Real.pi := by
    have habs := integral_abs_sub_iid_standardGaussian hgm hg hi
    have hmax : ∀ ω, P ω =
        (g 0 ω + g 1 ω + |g 0 ω - g 1 ω|) / 2 := by
      intro ω
      dsimp [P]
      by_cases h : g 0 ω ≤ g 1 ω
      · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · have h' : g 1 ω ≤ g 0 ω := le_of_not_ge h
        rw [max_eq_left h', abs_of_nonneg (sub_nonneg.mpr h')]
        ring
    calc
      (∫ ω, P ω ∂μ) =
          ∫ ω, (g 0 ω + g 1 ω + |g 0 ω - g 1 ω|) / 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ hmax
      _ = ((∫ ω, g 0 ω ∂μ) + (∫ ω, g 1 ω ∂μ) +
          (∫ ω, |g 0 ω - g 1 ω| ∂μ)) / 2 := by
        rw [integral_div]
        rw [integral_add]
        · rw [integral_add]
          · exact hgint 0
          · exact hgint 1
        · exact (hgint 0).add (hgint 1)
        · exact ((hgint 0).sub (hgint 1)).abs
      _ = 1 / Real.sqrt Real.pi := by rw [hmeans.1, hmeans.2, habs]; ring
  rw [← hP]
  exact integral_mono hPint hMint hpoint

/-- Gives an explicit exponential lower bound for a Gaussian upper tail at a selected scale.

**Lean implementation helper.** -/
private lemma gaussian_tail_exp_lower_spike {p : ℝ} (hp : 1 ≤ p) :
    (1 / 100 : ℝ) * Real.exp (-p) ≤
      (gaussianReal 0 1).real
        (Set.Ici (Real.sqrt p / 4)) := by
  let s : ℝ := Real.sqrt p
  let t : ℝ := s / 4
  have hp0 : 0 < p := one_pos.trans_le hp
  have hs0 : 0 < s := by simpa [s] using Real.sqrt_pos.2 hp0
  have hsSq : s ^ 2 = p := by simpa [s] using Real.sq_sqrt hp0.le
  have ht0 : 0 < t := div_pos hs0 (by norm_num)
  have htSq : t ^ 2 = p / 16 := by
    dsimp [t]
    rw [div_pow, hsSq]
    norm_num
  have hratio : 4 / (17 * s) ≤ t / (t ^ 2 + 1) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hs0) (by positivity)]
    dsimp [t]
    nlinarith [hsSq]
  have hsqrtpi0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrtpi3 : Real.sqrt (2 * Real.pi) ≤ 3 := by
    have hsquare := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have hsnonneg := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_lt_four]
  have hinvsqrt : (1 / 3 : ℝ) ≤ 1 / Real.sqrt (2 * Real.pi) :=
    one_div_le_one_div_of_le hsqrtpi0 hsqrtpi3
  have hlogle : Real.log p ≤ p :=
    (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
  have hsExp : s ≤ Real.exp (31 * p / 32) := by
    have hsEq : s = Real.exp (Real.log p / 2) := by
      dsimp [s]
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]
      congr 1
      ring
    rw [hsEq]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexpdom : s * Real.exp (-p) ≤ Real.exp (-p / 32) := by
    calc
      s * Real.exp (-p) ≤ Real.exp (31 * p / 32) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right hsExp (Real.exp_pos _).le
      _ = Real.exp (-p / 32) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hexpdiv : Real.exp (-p) ≤ Real.exp (-p / 32) / s :=
    (le_div_iff₀ hs0).2 (by simpa [mul_comm] using hexpdom)
  have hdensity : HDP.Chapter2.stdGaussianDensity t =
      Real.exp (-p / 32) * (1 / Real.sqrt (2 * Real.pi)) := by
    rw [HDP.Chapter2.stdGaussianDensity, htSq]
    congr 2
    ring
  calc
    (1 / 100 : ℝ) * Real.exp (-p) ≤ (4 / 51 : ℝ) * Real.exp (-p) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    _ ≤ (4 / 51 : ℝ) * (Real.exp (-p / 32) / s) :=
      mul_le_mul_of_nonneg_left hexpdiv (by norm_num)
    _ = (4 / (17 * s)) * (Real.exp (-p / 32) * (1 / 3)) := by
      field_simp
      ring
    _ ≤ (4 / (17 * s)) *
        (Real.exp (-p / 32) * (1 / Real.sqrt (2 * Real.pi))) := by
      gcongr
    _ = (4 / (17 * s)) * HDP.Chapter2.stdGaussianDensity t := by
      rw [hdensity]
    _ ≤ (t / (t ^ 2 + 1)) * HDP.Chapter2.stdGaussianDensity t :=
      mul_le_mul_of_nonneg_right hratio
        (HDP.Chapter2.stdGaussianDensity_pos t).le
    _ ≤ (gaussianReal 0 1).real (Set.Ici t) :=
      HDP.Chapter2.gaussian_tail_lower_measure ht0
    _ = (gaussianReal 0 1).real
        (Set.Ici (Real.sqrt p / 4)) := by rfl

/-- Bounds exp(-16) by one hundred-thousandth.

**Lean implementation helper.** -/
private lemma exp_neg_sixteen_le_inv_hundred_thousand :
    Real.exp (-16) ≤ (1 : ℝ) / 100000 := by
  have hbase : (27 : ℝ) / 10 < Real.exp 1 :=
    (by norm_num : (27 : ℝ) / 10 < 2.7182818283).trans
      Real.exp_one_gt_d9
  have hpow : ((27 : ℝ) / 10) ^ 16 < (Real.exp 1) ^ 16 :=
    pow_lt_pow_left₀ hbase (by norm_num) (by norm_num)
  have hexp : (100000 : ℝ) < Real.exp 16 := by
    rw [show (16 : ℝ) = (16 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact (by norm_num : (100000 : ℝ) < ((27 : ℝ) / 10) ^ 16).trans hpow
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (by positivity) (by norm_num)).2 hexp.le

/-- Gives a uniform square-root-logarithmic lower bound for the expected maximum of independent standard Gaussians.

**Lean implementation helper.** -/
private theorem gaussianMaxSeq_expectation_uniform
    {g : ℕ → Ω → ℝ}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) (n : ℕ) :
    (1 / 50 : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
      ∫ ω, HDP.Chapter2.gaussianMaxSeq g n ω ∂μ := by
  letI : IsProbabilityMeasure μ := (hg 0).isProbabilityMeasure
  let N : ℝ := (n : ℝ) + 2
  let L : ℝ := Real.sqrt (Real.log N)
  have hN2 : 2 ≤ N := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [N]
    linarith
  have hN0 : 0 < N :=
    (show (0 : ℝ) < 2 by norm_num).trans_le hN2
  have hlog0 : 0 < Real.log N := Real.log_pos (one_lt_two.trans_le hN2)
  have hL0 : 0 < L := by simpa [L] using Real.sqrt_pos.2 hlog0
  have hLSq : L ^ 2 = Real.log N := by simpa [L] using Real.sq_sqrt hlog0.le
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  by_cases hsmall : Real.log N ≤ 625
  · have hL25 : L ≤ 25 := by nlinarith
    have hleft : (1 / 50 : ℝ) * L ≤ 1 / 2 := by
      calc
        (1 / 50 : ℝ) * L ≤ (1 / 50 : ℝ) * 25 := by gcongr
        _ = 1 / 2 := by norm_num
    have hsqrtpi0 : 0 < Real.sqrt Real.pi := by positivity
    have hsqrtpi2 : Real.sqrt Real.pi ≤ 2 := by
      have hs := Real.sq_sqrt Real.pi_pos.le
      have hs0 := Real.sqrt_nonneg Real.pi
      nlinarith [Real.pi_lt_four]
    have hhalf : (1 / 2 : ℝ) ≤ 1 / Real.sqrt Real.pi :=
      one_div_le_one_div_of_le hsqrtpi0 hsqrtpi2
    change (1 / 50 : ℝ) * L ≤ _
    exact hleft.trans (hhalf.trans
      (gaussianMaxSeq_expectation_ge_inv_sqrt_pi hgm hg hi n))
  · have hlarge : 625 < Real.log N := lt_of_not_ge hsmall
    have hL25 : 25 < L := by nlinarith
    let p : ℝ := Real.log N / 16
    let s : ℝ := Real.sqrt p
    let t : ℝ := s / 4
    have hp1 : 1 ≤ p := by dsimp [p]; linarith
    have hp0 : 0 < p := zero_lt_one.trans_le hp1
    have hs0 : 0 < s := by simpa [s] using Real.sqrt_pos.2 hp0
    have hsSq : s ^ 2 = p := by simpa [s] using Real.sq_sqrt hp0.le
    have hsL : s = L / 4 := by
      have hL4nonneg : 0 ≤ L / 4 := by positivity
      have hsq : (L / 4) ^ 2 = p := by dsimp [p]; nlinarith
      nlinarith
    have htL : t = L / 16 := by
      change s / 4 = L / 16
      rw [hsL]
      ring
    let q : ℝ := (gaussianReal 0 1).real (Set.Ici t)
    have hq : (1 / 100 : ℝ) * Real.exp (-p) ≤ q := by
      simpa [q, t] using gaussian_tail_exp_lower_spike hp1
    have hscale : 16 ≤ N * ((1 / 100 : ℝ) * Real.exp (-p)) := by
      let x : ℝ := (15 / 16 : ℝ) * Real.log N
      have hx0 : 0 ≤ x := by dsimp [x]; positivity
      have hx : 500 < x := by dsimp [x]; linarith
      have hpowexp : x ^ 2 / (2 : ℝ) ≤ Real.exp x :=
        Real.pow_div_factorial_le_exp (x := x) hx0 2
      have hid : N * ((1 / 100 : ℝ) * Real.exp (-p)) =
          (1 / 100 : ℝ) * Real.exp x := by
        rw [show N = Real.exp (Real.log N) by rw [Real.exp_log hN0]]
        dsimp [p, x]
        rw [show Real.exp (Real.log N) *
            (1 / 100 * Real.exp (-(Real.log N / 16))) =
              (1 / 100) *
                (Real.exp (Real.log N) * Real.exp (-(Real.log N / 16))) by ring]
        rw [← Real.exp_add]
        congr 2
        ring
      rw [hid]
      calc
        (16 : ℝ) ≤ (1 / 100 : ℝ) * (x ^ 2 / 2) := by nlinarith
        _ ≤ (1 / 100 : ℝ) * Real.exp x := by gcongr
    have hnq : 16 ≤ N * q :=
      hscale.trans (mul_le_mul_of_nonneg_left hq (by positivity))
    have hlt : μ.real {ω | HDP.Chapter2.gaussianMaxSeq g n ω < t} ≤
        1 / 100000 := by
      calc
        μ.real {ω | HDP.Chapter2.gaussianMaxSeq g n ω < t} ≤
            Real.exp (-(n + 2 : ℝ) * q) := by
          simpa [N, q] using
            HDP.Chapter2.gaussianMaxSeq_lt_measure_le_exp hg hi n t
        _ ≤ Real.exp (-16) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        _ ≤ 1 / 100000 := exp_neg_sixteen_le_inv_hundred_thousand
    have hg0abs : (∫ ω, |g 0 ω| ∂μ) ≤ 1 := by
      have h := HDP.Chapter2.gaussian_absolute_moment (hg 0)
        (p := (1 : ℝ)) (by norm_num)
      have heq : (∫ ω, |g 0 ω| ∂μ) =
          Real.sqrt 2 / Real.sqrt Real.pi := by
        rw [show Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) by
          rw [← Real.sqrt_eq_rpow]]
        simpa [Real.rpow_one, Real.Gamma_one] using h
      rw [heq]
      have hsqrt2pi : Real.sqrt 2 ≤ Real.sqrt Real.pi :=
        Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      exact (div_le_one (by positivity)).2 hsqrt2pi
    have hlower := HDP.Chapter2.gaussianMaxSeq_expectation_lower
      hgm hg n t
    have hnumeric : (1 / 50 : ℝ) * L ≤
        t * (1 - μ.real {ω | HDP.Chapter2.gaussianMaxSeq g n ω < t}) -
          (∫ ω, |g 0 ω| ∂μ) := by
      rw [htL]
      have hprob0 := measureReal_nonneg (μ := μ)
        (s := {ω | HDP.Chapter2.gaussianMaxSeq g n ω < t})
      have hprob1 := hlt
      have hcoarse : (1 / 50 : ℝ) * L ≤
          (L / 16) * (1 - (1 / 100000 : ℝ)) - 1 := by
        nlinarith
      have htailprod : (L / 16) *
          μ.real {ω | HDP.Chapter2.gaussianMaxSeq g n ω < t} ≤
          (L / 16) * (1 / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_left hlt (by positivity)
      rw [htL] at htailprod
      exact hcoarse.trans (by nlinarith)
    change (1 / 50 : ℝ) * L ≤ _
    exact hnumeric.trans hlower

/-- The expected supremum of a nonempty finite centered family is nonnegative.

**Lean implementation helper.** -/
private lemma expectedFiniteSupremum_nonneg_of_centered
    {I Ω' : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω']
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Z : I → Ω' → ℝ) (hZ : IsGaussianProcess Z ν)
    (hZ0 : ∀ i, ∫ ω, Z i ω ∂ν = 0) :
    0 ≤ expectedFiniteSupremum ν Z := by
  classical
  let i0 : I := Classical.choice inferInstance
  have hZi : ∀ i, Integrable (Z i) ν := by
    intro i
    exact ((hZ.hasGaussianLaw_eval i).memLp_two.integrable (by norm_num))
  have hM : Integrable (HDP.Chapter5.finiteMaximum Z) ν := by
    rw [show HDP.Chapter5.finiteMaximum Z =
        Finset.univ.sup' Finset.univ_nonempty Z by
      funext ω
      simp [HDP.Chapter5.finiteMaximum]]
    refine Finset.sup'_induction Finset.univ_nonempty Z
      (p := fun f => Integrable f ν) ?_ ?_
    · intro f hf g hg
      exact hf.sup hg
    · intro i hi
      exact hZi i
  have hpoint : ∀ ω, Z i0 ω ≤ HDP.Chapter5.finiteMaximum Z ω := by
    intro ω
    exact Finset.le_sup' (fun i => Z i ω) (Finset.mem_univ i0)
  rw [show (0 : ℝ) = ∫ ω, Z i0 ω ∂ν by rw [hZ0 i0]]
  exact integral_mono (hZi i0) hM hpoint

/-- For arbitrary index sets, expected suprema are interpreted as suprema of finite-subset expected maxima. Remark 7.2.1's expected-supremum convention, with values in `EReal`.
The `n+1` indexing makes every approximating family nonempty.

**Book Remark 7.2.1.** -/
def extendedExpectedSupremum {T Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : T → Ω → ℝ) : EReal :=
  ⨆ n : ℕ, ⨆ t : Fin (n + 1) → T,
    (expectedFiniteSupremum μ (fun i ↦ X (t i)) : EReal)

/-- A finite centered Gaussian family with uniformly separated increments has expected supremum bounded below by the separation scale times the square root of the logarithmic cardinality.

**Lean implementation helper.** -/
private theorem sudakovSeparated_strong
    {T Ω' : Type*} [PseudoMetricSpace T] [MeasurableSpace Ω']
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : T → Ω' → ℝ) (hX : IsGaussianProcess X ν)
    (hX0 : ∀ t, ∫ ω, X t ω ∂ν = 0)
    (hcanonical : ∀ s t,
      dist s t ^ 2 = processIncrementSecondMoment ν X s t)
    (ε : ℝ≥0) (k : ℕ) (a : Fin (k + 2) → T)
    (hsep : ∀ i j, i ≠ j → (ε : ℝ) < dist (a i) (a j)) :
    (Real.sqrt 2 / 100) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) ≤
      expectedFiniteSupremum ν (fun i => X (a i)) := by
  classical
  let μG : Measure (ℕ → ℝ) :=
    Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)
  let g : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
  let c : ℝ := (ε : ℝ) / Real.sqrt 2
  let Y : Fin (k + 2) → (ℕ → ℝ) → ℝ := fun i ω => c * g i ω
  letI : IsProbabilityMeasure μG := by
    dsimp [μG]
    infer_instance
  have hgm : ∀ i, Measurable (g i) := fun i => measurable_pi_apply i
  have hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μG := by
    intro i
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ => gaussianReal 0 1) i).hasLaw
  have hgi : iIndepFun g μG := by
    dsimp [g, μG]
    simpa only [id_eq] using
      (iIndepFun_infinitePi
        (P := fun _ : ℕ => gaussianReal 0 1)
        (X := fun _ : ℕ => id) (fun _ => measurable_id))
  have hgproc : IsGaussianProcess g μG := by
    constructor
    intro I
    have hIind : iIndepFun (fun i : I => g i) μG :=
      hgi.precomp Subtype.val_injective
    have hIlaw : ∀ i : I, HasGaussianLaw (g i) μG := fun i =>
      (hg i).hasGaussianLaw
    simpa [Finset.restrict_def] using hIind.hasGaussianLaw hIlaw
  have hY : IsGaussianProcess Y μG := by
    exact (hgproc.comp_right (fun i : Fin (k + 2) => (i : ℕ))).smul
      (fun _ => c)
  have hgmean : ∀ i, ∫ ω, g i ω ∂μG = 0 := by
    intro i
    calc
      (∫ ω, g i ω ∂μG) = ∫ x, x ∂gaussianReal 0 1 := by
        simpa [Function.comp_def] using
          (hg i).integral_comp (f := id) (by fun_prop)
      _ = 0 := integral_id_gaussianReal
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μG = 0 := by
    intro i
    rw [show Y i = fun ω => c * g i ω by rfl, integral_const_mul,
      hgmean i, mul_zero]
  have hgmem : ∀ i, MemLp (g i) 2 μG := by
    intro i
    have hmem := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2
      (by norm_num)).comp_measurePreserving
      ((hg i).measurePreserving (hgm i))
    simpa [Function.comp_def] using hmem
  have hgsq : ∀ i, (∫ ω, (g i ω) ^ 2 ∂μG) = 1 := by
    intro i
    calc
      (∫ ω, (g i ω) ^ 2 ∂μG) =
          ∫ x, x ^ 2 ∂gaussianReal 0 1 := by
        simpa [Function.comp_def] using
          (hg i).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
      _ = 1 := by
        have hv := variance_eq_sub
          (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num))
        simpa using hv.symm
  have hgcross : ∀ i j, i ≠ j →
      (∫ ω, g i ω * g j ω ∂μG) = 0 := by
    intro i j hij
    have hfactor := (hgi.indepFun hij).integral_mul_eq_mul_integral
      (hgmem i).aestronglyMeasurable (hgmem j).aestronglyMeasurable
    simpa only [Pi.mul_apply, hgmean i, hgmean j, mul_zero] using hfactor
  have hYinc : ∀ i j,
      processIncrementSecondMoment μG Y i j =
        if i = j then 0 else (ε : ℝ) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [processIncrementSecondMoment]
    · rw [if_neg hij]
      have hprodInt : Integrable (fun ω => g i ω * g j ω) μG :=
        (hgmem i).integrable_mul (hgmem j)
      have hiSqInt : Integrable (fun ω => (g i ω) ^ 2) μG := by
        rw [show (fun ω => (g i ω) ^ 2) =
            g (i : ℕ) * g (i : ℕ) by
          funext ω
          simp [pow_two]]
        exact (hgmem (i : ℕ)).integrable_mul (hgmem (i : ℕ))
      have hjSqInt : Integrable (fun ω => (g j ω) ^ 2) μG := by
        rw [show (fun ω => (g j ω) ^ 2) =
            g (j : ℕ) * g (j : ℕ) by
          funext ω
          simp [pow_two]]
        exact (hgmem (j : ℕ)).integrable_mul (hgmem (j : ℕ))
      have hinner :
          (∫ ω, ((g i ω) ^ 2 - 2 * (g i ω * g j ω) +
              (g j ω) ^ 2) ∂μG) =
            (∫ ω, (g i ω) ^ 2 ∂μG) -
              2 * (∫ ω, g i ω * g j ω ∂μG) +
              (∫ ω, (g j ω) ^ 2 ∂μG) := by
        calc
          _ = ∫ ω, (((g i ω) ^ 2 - 2 * (g i ω * g j ω)) +
              (g j ω) ^ 2) ∂μG := rfl
          _ = (∫ ω, ((g i ω) ^ 2 - 2 * (g i ω * g j ω)) ∂μG) +
              ∫ ω, (g j ω) ^ 2 ∂μG :=
            integral_add (hiSqInt.sub (hprodInt.const_mul 2)) hjSqInt
          _ = ((∫ ω, (g i ω) ^ 2 ∂μG) -
                ∫ ω, 2 * (g i ω * g j ω) ∂μG) +
              ∫ ω, (g j ω) ^ 2 ∂μG := by
            rw [integral_sub hiSqInt (hprodInt.const_mul 2)]
          _ = _ := by rw [integral_const_mul]
      rw [processIncrementSecondMoment]
      simp only [Y, c]
      have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      calc
        (∫ ω, (ε / Real.sqrt 2 * g i ω -
            ε / Real.sqrt 2 * g j ω) ^ 2 ∂μG) =
            (ε / Real.sqrt 2) ^ 2 *
              ∫ ω, ((g i ω) ^ 2 - 2 * (g i ω * g j ω) +
                (g j ω) ^ 2) ∂μG := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with ω
          ring
        _ = (ε / Real.sqrt 2) ^ 2 *
            ((∫ ω, (g i ω) ^ 2 ∂μG) -
              2 * (∫ ω, g i ω * g j ω ∂μG) +
              (∫ ω, (g j ω) ^ 2 ∂μG)) := by
          rw [hinner]
        _ = (ε : ℝ) ^ 2 := by
          have hijval : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hij
          rw [hgsq i, hgsq j, hgcross i j hijval]
          have hsqrt2ne : Real.sqrt 2 ≠ 0 :=
            Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)
          field_simp [hsqrt2ne]
          nlinarith [hsqrt2sq]
  let X' : Fin (k + 2) → Ω' → ℝ := fun i => X (a i)
  have hX' : IsGaussianProcess X' ν := hX.comp_right a
  have hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0 := fun i => hX0 (a i)
  have hinc : ∀ i j,
      processIncrementSecondMoment μG Y i j ≤
        processIncrementSecondMoment ν X' i j := by
    intro i j
    rw [hYinc]
    by_cases hij : i = j
    · subst j
      simp [processIncrementSecondMoment]
    · rw [if_neg hij]
      change (ε : ℝ) ^ 2 ≤
        processIncrementSecondMoment ν X (a i) (a j)
      rw [← hcanonical (a i) (a j)]
      have hd0 : 0 ≤ dist (a i) (a j) := dist_nonneg
      have he0 : 0 ≤ (ε : ℝ) := ε.coe_nonneg
      nlinarith [hsep i j hij]
  have hcompare : expectedFiniteSupremum μG Y ≤
      expectedFiniteSupremum ν X' :=
    sudakovFernique μG ν Y X' hY hX' hY0 hX'0 hinc
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hmaxY : expectedFiniteSupremum μG Y =
      c * ∫ ω, HDP.Chapter2.gaussianMaxSeq g k ω ∂μG := by
    rw [expectedFiniteSupremum]
    rw [show (fun ω => HDP.Chapter5.finiteMaximum Y ω) =
        fun ω => c * HDP.Chapter2.gaussianMaxSeq g k ω by
      funext ω
      rw [HDP.Chapter2.gaussianMaxSeq_eq_finSup]
      unfold HDP.Chapter5.finiteMaximum
      rw [Finset.mul₀_sup' hc0]]
    rw [integral_const_mul]
  have hmaxlower := gaussianMaxSeq_expectation_uniform hgm hg hgi k
  have hmul := mul_le_mul_of_nonneg_left
    (gaussianMaxSeq_expectation_uniform hgm hg hgi k) hc0
  have hcoeff : c * ((1 / 50 : ℝ) *
      Real.sqrt (Real.log ((k : ℝ) + 2))) =
      (Real.sqrt 2 / 100) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) := by
    dsimp [c]
    have hsqrt2ne : Real.sqrt 2 ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)
    field_simp [hsqrt2ne]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  calc
    (Real.sqrt 2 / 100) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) =
      c * ((1 / 50 : ℝ) *
        Real.sqrt (Real.log ((k : ℝ) + 2))) := hcoeff.symm
    _ ≤ c * ∫ ω, HDP.Chapter2.gaussianMaxSeq g k ω ∂μG := hmul
    _ = expectedFiniteSupremum μG Y := hmaxY.symm
    _ ≤ expectedFiniteSupremum ν X' := hcompare

/-- Sudakov lower-bounds a Gaussian expected supremum by `epsilon sqrt(log covering-number)`. The
explicit `1/100` is a conservative absolute constant; `ε>0` excludes the
undefined product `0 * sqrt(log ⊤)` from the printed `ε≥0` formulation. The proof extracts an exact-cardinality separated subfamily through Mathlib's
`ℕ∞` covering/packing APIs, compares it with independent Gaussian
coordinates by Sudakov--Fernique, and proves the required Gaussian-maximum
lower bound with explicit constants.

**Book Theorem 7.4.1.** -/
theorem sudakovInequality
    {T Ω' : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T]
    [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : T → Ω' → ℝ) (hX : IsGaussianProcess X ν)
    (hX0 : ∀ t, ∫ ω, X t ω ∂ν = 0)
    (hcanonical : ∀ s t,
      dist s t ^ 2 = processIncrementSecondMoment ν X s t)
    (ε : ℝ≥0) (hε : 0 < ε)
    (hfinite : Metric.coveringNumber ε (Set.univ : Set T) ≠ ⊤) :
    (1 / 100 : ℝ) * ε *
        Real.sqrt (Real.log
          (HDP.finiteCoveringNumber ε (Set.univ : Set T) hfinite)) ≤
      expectedFiniteSupremum ν X := by
  classical
  let N : ℕ := HDP.finiteCoveringNumber ε (Set.univ : Set T) hfinite
  have hNpos : 0 < N := by
    have hcovpos : 0 < Metric.coveringNumber ε (Set.univ : Set T) := by simp
    have hcoe := HDP.coe_finiteCoveringNumber ε (Set.univ : Set T) hfinite
    have hN_enat : (0 : ℕ∞) < (N : ℕ∞) := by
      rw [show (N : ℕ∞) =
        Metric.coveringNumber ε (Set.univ : Set T) by
        exact hcoe]
      exact hcovpos
    exact_mod_cast hN_enat
  by_cases hNsmall : N < 2
  · have hN1 : N = 1 := by omega
    rw [show HDP.finiteCoveringNumber ε (Set.univ : Set T) hfinite = 1 by
      exact hN1]
    simp only [Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero]
    exact expectedFiniteSupremum_nonneg_of_centered ν X hX hX0
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, N = k + 2 := by
      exact ⟨N - 2, by omega⟩
    let P : Set T := Metric.maximalSeparatedSet ε (Set.univ : Set T)
    have hpackfinite : Metric.packingNumber ε (Set.univ : Set T) ≠ ⊤ := by
      exact (HDP.finite_covering_packing_of_finite
        (Set.finite_univ : (Set.univ : Set T).Finite) ε).2
    have hPfinite : P.Finite := by
      apply Set.encard_lt_top_iff.mp
      rw [show P = Metric.maximalSeparatedSet ε (Set.univ : Set T) by rfl,
        Metric.encard_maximalSeparatedSet hpackfinite]
      exact hpackfinite.lt_top
    letI : Fintype P := hPfinite.fintype
    have hNP_enat : (N : ℕ∞) ≤ P.encard := by
      rw [HDP.coe_finiteCoveringNumber ε (Set.univ : Set T) hfinite]
      calc
        Metric.coveringNumber ε (Set.univ : Set T) ≤
            Metric.packingNumber ε (Set.univ : Set T) :=
          Metric.coveringNumber_le_packingNumber ε _
        _ = P.encard := by
          symm
          exact Metric.encard_maximalSeparatedSet hpackfinite
    have hNP : N ≤ Fintype.card P := by
      have hNP_enat' : (N : ℕ∞) ≤ (Fintype.card P : ℕ∞) := by
        simpa only [Set.coe_fintypeCard] using hNP_enat
      exact_mod_cast hNP_enat'
    have hecard : Fintype.card (Fin (k + 2)) ≤ Fintype.card P := by
      simpa [hk] using hNP
    let e : Fin (k + 2) ↪ P :=
      Classical.choice (Function.Embedding.nonempty_of_card_le hecard)
    let a : Fin (k + 2) → T := fun i => e i
    have hsep : ∀ i j, i ≠ j → (ε : ℝ) < dist (a i) (a j) := by
      intro i j hij
      have hijT : (a i : T) ≠ a j := by
        intro heq
        apply hij
        exact e.injective (Subtype.ext heq)
      have hed := Metric.isSeparated_maximalSeparatedSet
        (show a i ∈ P from (e i).property)
        (show a j ∈ P from (e j).property) hijT
      simpa [edist_dist] using hed
    let μG : Measure (ℕ → ℝ) :=
      Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)
    let g : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
    let c : ℝ := (ε : ℝ) / Real.sqrt 2
    let Y : Fin (k + 2) → (ℕ → ℝ) → ℝ := fun i ω => c * g i ω
    letI : IsProbabilityMeasure μG := by
      dsimp [μG]
      infer_instance
    have hgm : ∀ i, Measurable (g i) := fun i => measurable_pi_apply i
    have hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μG := by
      intro i
      exact (measurePreserving_eval_infinitePi
        (fun _ : ℕ => gaussianReal 0 1) i).hasLaw
    have hgi : iIndepFun g μG := by
      dsimp [g, μG]
      simpa only [id_eq] using
        (iIndepFun_infinitePi
          (P := fun _ : ℕ => gaussianReal 0 1)
          (X := fun _ : ℕ => id) (fun _ => measurable_id))
    have hgproc : IsGaussianProcess g μG := by
      constructor
      intro I
      have hIind : iIndepFun (fun i : I => g i) μG :=
        hgi.precomp Subtype.val_injective
      have hIlaw : ∀ i : I, HasGaussianLaw (g i) μG := fun i =>
        (hg i).hasGaussianLaw
      simpa [Finset.restrict_def] using hIind.hasGaussianLaw hIlaw
    have hY : IsGaussianProcess Y μG := by
      exact (hgproc.comp_right (fun i : Fin (k + 2) => (i : ℕ))).smul
        (fun _ => c)
    have hgmean : ∀ i, ∫ ω, g i ω ∂μG = 0 := by
      intro i
      calc
        (∫ ω, g i ω ∂μG) = ∫ x, x ∂gaussianReal 0 1 := by
          simpa [Function.comp_def] using
            (hg i).integral_comp (f := id) (by fun_prop)
        _ = 0 := integral_id_gaussianReal
    have hY0 : ∀ i, ∫ ω, Y i ω ∂μG = 0 := by
      intro i
      rw [show Y i = fun ω => c * g i ω by rfl, integral_const_mul,
        hgmean i, mul_zero]
    have hgmem : ∀ i, MemLp (g i) 2 μG := by
      intro i
      have hmem := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2
        (by norm_num)).comp_measurePreserving
        ((hg i).measurePreserving (hgm i))
      simpa [Function.comp_def] using hmem
    have hgsq : ∀ i, (∫ ω, (g i ω) ^ 2 ∂μG) = 1 := by
      intro i
      calc
        (∫ ω, (g i ω) ^ 2 ∂μG) =
            ∫ x, x ^ 2 ∂gaussianReal 0 1 := by
          simpa [Function.comp_def] using
            (hg i).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
        _ = 1 := by
          have hv := variance_eq_sub
            (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num))
          simpa using hv.symm
    have hgcross : ∀ i j, i ≠ j →
        (∫ ω, g i ω * g j ω ∂μG) = 0 := by
      intro i j hij
      have hfactor := (hgi.indepFun hij).integral_mul_eq_mul_integral
        (hgmem i).aestronglyMeasurable (hgmem j).aestronglyMeasurable
      simpa only [Pi.mul_apply, hgmean i, hgmean j, mul_zero] using hfactor
    have hYinc : ∀ i j,
        processIncrementSecondMoment μG Y i j =
          if i = j then 0 else (ε : ℝ) ^ 2 := by
      intro i j
      by_cases hij : i = j
      · subst j
        simp [processIncrementSecondMoment]
      · rw [if_neg hij]
        have hprodInt : Integrable (fun ω => g i ω * g j ω) μG :=
          (hgmem i).integrable_mul (hgmem j)
        have hiSqInt : Integrable (fun ω => (g i ω) ^ 2) μG := by
          rw [show (fun ω => (g i ω) ^ 2) =
              g (i : ℕ) * g (i : ℕ) by
            funext ω
            simp [pow_two]]
          exact (hgmem (i : ℕ)).integrable_mul (hgmem (i : ℕ))
        have hjSqInt : Integrable (fun ω => (g j ω) ^ 2) μG := by
          rw [show (fun ω => (g j ω) ^ 2) =
              g (j : ℕ) * g (j : ℕ) by
            funext ω
            simp [pow_two]]
          exact (hgmem (j : ℕ)).integrable_mul (hgmem (j : ℕ))
        have hinner :
            (∫ ω, ((g i ω) ^ 2 - 2 * (g i ω * g j ω) +
                (g j ω) ^ 2) ∂μG) =
              (∫ ω, (g i ω) ^ 2 ∂μG) -
                2 * (∫ ω, g i ω * g j ω ∂μG) +
                (∫ ω, (g j ω) ^ 2 ∂μG) := by
          calc
            _ = ∫ ω, (((g i ω) ^ 2 - 2 * (g i ω * g j ω)) +
                (g j ω) ^ 2) ∂μG := rfl
            _ = (∫ ω, ((g i ω) ^ 2 - 2 * (g i ω * g j ω)) ∂μG) +
                ∫ ω, (g j ω) ^ 2 ∂μG :=
              integral_add (hiSqInt.sub (hprodInt.const_mul 2)) hjSqInt
            _ = ((∫ ω, (g i ω) ^ 2 ∂μG) -
                  ∫ ω, 2 * (g i ω * g j ω) ∂μG) +
                ∫ ω, (g j ω) ^ 2 ∂μG := by
              rw [integral_sub hiSqInt (hprodInt.const_mul 2)]
            _ = _ := by rw [integral_const_mul]
        rw [processIncrementSecondMoment]
        simp only [Y, c]
        have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
          Real.sq_sqrt (by norm_num)
        calc
          (∫ ω, (ε / Real.sqrt 2 * g i ω -
              ε / Real.sqrt 2 * g j ω) ^ 2 ∂μG) =
              (ε / Real.sqrt 2) ^ 2 *
                ∫ ω, ((g i ω) ^ 2 - 2 * (g i ω * g j ω) +
                  (g j ω) ^ 2) ∂μG := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with ω
            ring
          _ = (ε / Real.sqrt 2) ^ 2 *
              ((∫ ω, (g i ω) ^ 2 ∂μG) -
                2 * (∫ ω, g i ω * g j ω ∂μG) +
                (∫ ω, (g j ω) ^ 2 ∂μG)) := by
            rw [hinner]
          _ = (ε : ℝ) ^ 2 := by
            have hijval : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hij
            rw [hgsq i, hgsq j, hgcross i j hijval]
            have hsqrt2ne : Real.sqrt 2 ≠ 0 :=
              Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)
            field_simp [hsqrt2ne]
            nlinarith [hsqrt2sq]
    let X' : Fin (k + 2) → Ω' → ℝ := fun i => X (a i)
    have hX' : IsGaussianProcess X' ν := hX.comp_right a
    have hX'0 : ∀ i, ∫ ω, X' i ω ∂ν = 0 := fun i => hX0 (a i)
    have hinc : ∀ i j,
        processIncrementSecondMoment μG Y i j ≤
          processIncrementSecondMoment ν X' i j := by
      intro i j
      rw [hYinc]
      by_cases hij : i = j
      · subst j
        simp [processIncrementSecondMoment]
      · rw [if_neg hij]
        change (ε : ℝ) ^ 2 ≤
          processIncrementSecondMoment ν X (a i) (a j)
        rw [← hcanonical (a i) (a j)]
        have hd0 : 0 ≤ dist (a i) (a j) := dist_nonneg
        have he0 : 0 ≤ (ε : ℝ) := ε.coe_nonneg
        nlinarith [hsep i j hij]
    have hcompare : expectedFiniteSupremum μG Y ≤
        expectedFiniteSupremum ν X' :=
      sudakovFernique μG ν Y X' hY hX' hY0 hX'0 hinc
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hmaxY : expectedFiniteSupremum μG Y =
        c * ∫ ω, HDP.Chapter2.gaussianMaxSeq g k ω ∂μG := by
      rw [expectedFiniteSupremum]
      rw [show (fun ω => HDP.Chapter5.finiteMaximum Y ω) =
          fun ω => c * HDP.Chapter2.gaussianMaxSeq g k ω by
        funext ω
        rw [HDP.Chapter2.gaussianMaxSeq_eq_finSup]
        unfold HDP.Chapter5.finiteMaximum
        rw [Finset.mul₀_sup' hc0]]
      rw [integral_const_mul]
    have hmaxlower := gaussianMaxSeq_expectation_uniform hgm hg hgi k
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hYlower : (1 / 100 : ℝ) * ε *
        Real.sqrt (Real.log N) ≤ expectedFiniteSupremum μG Y := by
      rw [hmaxY]
      have hmul := mul_le_mul_of_nonneg_left hmaxlower hc0
      rw [show N = k + 2 from hk, Nat.cast_add, Nat.cast_ofNat]
      have hcoeff : c * ((Real.sqrt 2 / 100) *
          Real.sqrt (Real.log ((k : ℝ) + 2))) =
          (1 / 100 : ℝ) * ε *
            Real.sqrt (Real.log ((k : ℝ) + 2)) := by
        dsimp [c]
        field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)]
      rw [← hcoeff]
      refine (mul_le_mul_of_nonneg_left ?_ hc0).trans hmul
      have hsqrt2sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hsqrt2nonneg := Real.sqrt_nonneg (2 : ℝ)
      have hsqrt2le : Real.sqrt 2 ≤ 2 := by nlinarith
      have hcoeffle : Real.sqrt 2 / 100 ≤ (1 / 50 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hcoeffle (Real.sqrt_nonneg _)
    have hXcoord : ∀ t, Integrable (X t) ν := by
      intro t
      exact (hX.hasGaussianLaw_eval t).memLp_two.integrable (by norm_num)
    have hXint : Integrable (HDP.Chapter5.finiteMaximum X) ν := by
      rw [show HDP.Chapter5.finiteMaximum X =
          Finset.univ.sup' Finset.univ_nonempty X by
        funext ω
        simp [HDP.Chapter5.finiteMaximum]]
      refine Finset.sup'_induction Finset.univ_nonempty X
        (p := fun f => Integrable f ν) ?_ ?_
      · intro f hf g' hg'
        exact hf.sup hg'
      · intro t ht
        exact hXcoord t
    have hX'int : Integrable (HDP.Chapter5.finiteMaximum X') ν := by
      rw [show HDP.Chapter5.finiteMaximum X' =
          Finset.univ.sup' Finset.univ_nonempty X' by
        funext ω
        simp [HDP.Chapter5.finiteMaximum]]
      refine Finset.sup'_induction Finset.univ_nonempty X'
        (p := fun f => Integrable f ν) ?_ ?_
      · intro f hf g' hg'
        exact hf.sup hg'
      · intro i hi
        exact hXcoord (a i)
    have hrestrict : expectedFiniteSupremum ν X' ≤
        expectedFiniteSupremum ν X := by
      apply integral_mono hX'int hXint
      intro ω
      apply Finset.sup'_le
      intro i hi
      exact Finset.le_sup' (fun t : T => X t ω)
        (Finset.mem_univ (a i))
    simpa [N] using hYlower.trans (hcompare.trans hrestrict)

/-- Infinite packing number yields arbitrarily large finite separated subsets.

**Lean implementation helper.** -/
private lemma exists_fin_separated_of_packingNumber_eq_top
    {T : Type*} [PseudoMetricSpace T]
    (ε : ℝ≥0) (hpack : Metric.packingNumber ε (Set.univ : Set T) = ⊤)
    (N : ℕ) :
    ∃ a : Fin N → T, Function.Injective a ∧
      ∀ i j, i ≠ j → (ε : ℝ) < dist (a i) (a j) := by
  classical
  have hlt : (N : ℕ∞) <
      Metric.packingNumber ε (Set.univ : Set T) := by
    rw [hpack]
    exact ENat.coe_lt_top N
  rw [Metric.packingNumber] at hlt
  rw [lt_iSup_iff] at hlt
  obtain ⟨C, hlt⟩ := hlt
  rw [lt_iSup_iff] at hlt
  obtain ⟨hCsub, hlt⟩ := hlt
  rw [lt_iSup_iff] at hlt
  obtain ⟨hCsep, hlt⟩ := hlt
  have hNle : (N : ℕ∞) ≤ C.encard := hlt.le
  obtain ⟨D, hDC, hDcard⟩ := Set.exists_subset_encard_eq hNle
  have hDfinite : D.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [hDcard]
    exact ENat.coe_ne_top N
  letI : Fintype D := hDfinite.fintype
  have hcard : Fintype.card D = N := by
    have hcard' : (Fintype.card D : ℕ∞) = (N : ℕ∞) := by
      rw [Set.coe_fintypeCard, hDcard]
    exact_mod_cast hcard'
  let e : Fin N ↪ D := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simp [hcard]))
  let a : Fin N → T := fun i => e i
  refine ⟨a, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i j hij
    have hijD : e i ≠ e j := by
      intro h
      exact hij (e.injective h)
    have hijT : (e i : T) ≠ (e j : T) := by
      intro h
      exact hijD (Subtype.ext h)
    have hed := hCsep (hDC (e i).property) (hDC (e j).property)
      hijT
    simpa [edist_dist] using hed

/-- The extended expected supremum dominates the Sudakov lower-bound sequence arising from finite separated subsets.

**Lean implementation helper.** -/
private lemma extendedExpectedSupremum_ge_sudakovSeq
    {T Ω : Type*} [PseudoMetricSpace T] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : T → Ω → ℝ) (hX : IsGaussianProcess X μ)
    (hX0 : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hcanonical : ∀ s t,
      dist s t ^ 2 = processIncrementSecondMoment μ X s t)
    (ε : ℝ≥0) (hε : 0 < ε)
    (hinfinite : Metric.coveringNumber ε (Set.univ : Set T) = ⊤)
    (k : ℕ) :
    (((1 / 200 : ℝ) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) : ℝ) : EReal) ≤
      extendedExpectedSupremum μ X := by
  classical
  have hpack : Metric.packingNumber ε (Set.univ : Set T) = ⊤ := by
    apply top_unique
    rw [← hinfinite]
    exact Metric.coveringNumber_le_packingNumber ε _
  obtain ⟨a, hainj, hsep⟩ :=
    exists_fin_separated_of_packingNumber_eq_top ε hpack (k + 2)
  letI : PseudoMetricSpace (Fin (k + 2)) :=
    PseudoMetricSpace.induced a (by infer_instance)
  let X' : Fin (k + 2) → Ω → ℝ := fun i => X (a i)
  have hX' : IsGaussianProcess X' μ := hX.comp_right a
  have hX'0 : ∀ i, ∫ ω, X' i ω ∂μ = 0 := fun i => hX0 (a i)
  have hcanonical' : ∀ i j,
      dist i j ^ 2 = processIncrementSecondMoment μ X' i j := by
    intro i j
    change dist (a i) (a j) ^ 2 =
      processIncrementSecondMoment μ X (a i) (a j)
    exact hcanonical (a i) (a j)
  let δ : ℝ≥0 := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcoverfinite :
      Metric.coveringNumber δ (Set.univ : Set (Fin (k + 2))) ≠ ⊤ := by
    apply ne_of_lt
    refine (Metric.coveringNumber_le_encard_self
      (Set.univ : Set (Fin (k + 2)))).trans_lt ?_
    simpa using ENat.coe_lt_top (k + 2)
  have hsepSet : Metric.IsSeparated (ε : ℝ≥0∞)
      (Set.univ : Set (Fin (k + 2))) := by
    intro i hi j hj hij
    have hdist : dist i j = dist (a i) (a j) := rfl
    simpa [edist_dist, hdist] using hsep i j hij
  have hcoverlower : ((k + 2 : ℕ) : ℕ∞) ≤
      Metric.coveringNumber δ (Set.univ : Set (Fin (k + 2))) := by
    calc
      ((k + 2 : ℕ) : ℕ∞) =
          (Set.univ : Set (Fin (k + 2))).encard := by simp
      _ ≤ Metric.packingNumber ε (Set.univ : Set (Fin (k + 2))) :=
        hsepSet.encard_le_packingNumber (by simp)
      _ = Metric.packingNumber (2 * δ)
          (Set.univ : Set (Fin (k + 2))) := by
        congr 2
        ext
        change (ε : ℝ) = 2 * ((ε : ℝ) / 2)
        ring
      _ ≤ Metric.externalCoveringNumber δ
          (Set.univ : Set (Fin (k + 2))) :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber δ _
      _ ≤ Metric.coveringNumber δ
          (Set.univ : Set (Fin (k + 2))) :=
        Metric.externalCoveringNumber_le_coveringNumber δ _
  let M : ℕ := HDP.finiteCoveringNumber δ
    (Set.univ : Set (Fin (k + 2))) hcoverfinite
  have hM : k + 2 ≤ M := by
    have hM' : ((k + 2 : ℕ) : ℕ∞) ≤ (M : ℕ∞) := by
      rw [show (M : ℕ∞) = Metric.coveringNumber δ
          (Set.univ : Set (Fin (k + 2))) by
        exact HDP.coe_finiteCoveringNumber δ
          (Set.univ : Set (Fin (k + 2))) hcoverfinite]
      exact hcoverlower
    exact_mod_cast hM'
  have hlog : Real.log ((k : ℝ) + 2) ≤ Real.log (M : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact show (0 : ℝ) < (k : ℝ) + 2 by positivity
    · have : (2 : ℕ) ≤ M := le_trans (by omega) hM
      have hMpos : (0 : ℕ) < M := by omega
      change (0 : ℝ) < (M : ℝ)
      exact_mod_cast hMpos
    · have hMreal : ((k + 2 : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hM
      simpa [Nat.cast_add, Nat.cast_ofNat] using hMreal
  have hsqrt : Real.sqrt (Real.log ((k : ℝ) + 2)) ≤
      Real.sqrt (Real.log (M : ℝ)) := Real.sqrt_le_sqrt hlog
  have hsud := sudakovInequality μ X' hX' hX'0 hcanonical' δ hδ hcoverfinite
  have hlower : (1 / 200 : ℝ) * ε *
      Real.sqrt (Real.log ((k : ℝ) + 2)) ≤
        expectedFiniteSupremum μ X' := by
    calc
      (1 / 200 : ℝ) * ε * Real.sqrt (Real.log ((k : ℝ) + 2)) =
          (1 / 100 : ℝ) * δ *
            Real.sqrt (Real.log ((k : ℝ) + 2)) := by
        dsimp [δ]
        ring
      _ ≤ (1 / 100 : ℝ) * δ * Real.sqrt (Real.log (M : ℝ)) := by
        gcongr
      _ ≤ expectedFiniteSupremum μ X' := by simpa [M] using hsud
  calc
    (((1 / 200 : ℝ) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) : ℝ) : EReal) ≤
        (expectedFiniteSupremum μ X' : EReal) := by exact_mod_cast hlower
    _ ≤ extendedExpectedSupremum μ X := by
      unfold extendedExpectedSupremum
      exact le_iSup_of_le (k + 1) (le_iSup_of_le a (by exact le_rfl))

/-- A non-relatively-compact index set has divergent finite-subset Gaussian maxima. Infinite covering number forces
the finite-subfamily expected supremum to be `+∞`. The proof extracts
arbitrarily large finite separated subfamilies from the infinite packing
number, applies the finite Sudakov estimate at half scale, and proves that the
resulting logarithmic lower bounds are unbounded in `EReal`.

**Book Exercise 7.14.** -/
theorem exercise_7_14_noncompact_expectedSupremum
    {T Ω : Type*} [PseudoMetricSpace T] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : T → Ω → ℝ) (hX : IsGaussianProcess X μ)
    (hX0 : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hcanonical : ∀ s t,
      dist s t ^ 2 = processIncrementSecondMoment μ X s t)
    (ε : ℝ≥0) (hε : 0 < ε)
    (hinfinite : Metric.coveringNumber ε (Set.univ : Set T) = ⊤) :
    extendedExpectedSupremum μ X = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).2
  intro y
  let d : ℝ := (1 / 200 : ℝ) * ε
  have hd : 0 < d := by dsimp [d]; positivity
  let q : ℝ := max (y / d) 0 + 1
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hyq : y / d < q := by
    dsimp [q]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.exp (q ^ 2))
  have hk2 : Real.exp (q ^ 2) < (k : ℝ) + 2 :=
    hk.trans (by norm_num)
  have hlog : q ^ 2 < Real.log ((k : ℝ) + 2) := by
    have hmono := Real.strictMonoOn_log (Real.exp_pos (q ^ 2))
      (show (0 : ℝ) < (k : ℝ) + 2 by positivity) hk2
    simpa using hmono
  have hqsqrt : q < Real.sqrt (Real.log ((k : ℝ) + 2)) :=
    (Real.lt_sqrt hq0).2 hlog
  have hydq : y < d * q := by
    have := (div_lt_iff₀ hd).1 hyq
    simpa [mul_comm] using this
  have hybound : y < (1 / 200 : ℝ) * ε *
      Real.sqrt (Real.log ((k : ℝ) + 2)) := by
    change y < d * Real.sqrt (Real.log ((k : ℝ) + 2))
    exact hydq.trans (mul_lt_mul_of_pos_left hqsqrt hd)
  exact (EReal.coe_lt_coe_iff.2 hybound).trans_le
    (extendedExpectedSupremum_ge_sudakovSeq μ X hX hX0 hcanonical
      ε hε hinfinite k)

/-- Every exponential multiple of a real Gaussian random variable is integrable.

**Lean implementation helper.** -/
private lemma integrable_exp_mul_of_hasLaw_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {g : Ω → ℝ} {μ₀ : ℝ} {v : ℝ≥0}
    (hg : HasLaw g (gaussianReal μ₀ v) μ) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam * g ω)) μ := by
  have h := integrable_exp_mul_gaussianReal (μ := μ₀) (v := v) lam
  rw [← hg.map_eq] at h
  exact h.comp_aemeasurable hg.aemeasurable

/-- Evaluation of the canonical Gaussian process has the one-dimensional Gaussian law with variance equal to the squared index norm.

**Lean implementation helper.** -/
private lemma canonicalGaussian_eval_map {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (canonicalGaussianProcess (fun _ : Unit => x) ()) =
      gaussianReal 0 (Real.toNNReal (‖x‖ ^ 2)) := by
  have hmap := (ProbabilityTheory.IsGaussian.map_eq_gaussianReal ((innerSL ℝ) x) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map ((innerSL ℝ) x) =
      gaussianReal
        ((stdGaussian (EuclideanSpace ℝ (Fin n)))[(innerSL ℝ) x])
        Var[(innerSL ℝ) x;
          stdGaussian (EuclideanSpace ℝ (Fin n))].toNNReal)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm] at hmap
  have hfun : canonicalGaussianProcess (fun _ : Unit => x) () =
      (innerSL ℝ) x := by
    funext g
    simp [canonicalGaussianProcess, innerSL_apply_apply]
  rw [hfun]
  exact hmap

/-- Bounds the expected maximum of finitely many canonical Gaussian evaluations by the extended expected supremum.

**Lean implementation helper.** -/
private theorem canonicalGaussian_fin_max_le {n k : ℕ}
    (a : Fin (k + 2) → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    expectedFiniteSupremum (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (canonicalGaussianProcess a) ≤
      Real.sqrt (2 * Real.log ((k : ℝ) + 2)) := by
  let μG := stdGaussian (EuclideanSpace ℝ (Fin n))
  let g : Fin (k + 2) → EuclideanSpace ℝ (Fin n) → ℝ :=
    canonicalGaussianProcess a
  let N : ℝ := (k : ℝ) + 2
  have hN : 1 < N := by
    dsimp [N]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  let lam : ℝ := Real.sqrt (2 * Real.log N)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos.mpr (mul_pos (by norm_num) hlogN)
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    have hfun : g i = (innerSL ℝ) (a i) := by
      funext ω
      simp [g, canonicalGaussianProcess, innerSL_apply_apply]
    rw [hfun]
    exact ((innerSL ℝ) (a i)).continuous.measurable
  have hgmap : ∀ i, μG.map (g i) =
      gaussianReal 0 (Real.toNNReal (‖a i‖ ^ 2)) := by
    intro i
    have hfun : g i = canonicalGaussianProcess (fun _ : Unit => a i) () := by
      rfl
    rw [hfun]
    exact canonicalGaussian_eval_map (a i)
  have hgmem : ∀ i, MemLp (g i) 2 μG := by
    intro i
    exact ((canonicalGaussianProcess_isGaussian a).hasGaussianLaw_eval i).memLp_two
  let Z : EuclideanSpace ℝ (Fin n) → ℝ := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => g i ω
  have hZm : Measurable Z := by
    have h1 : Measurable (Finset.univ.sup'
        (Finset.univ_nonempty (α := Fin (k + 2))) fun i ω => g i ω) :=
      Finset.measurable_sup' Finset.univ_nonempty fun i _ => hgm i
    have h2 : (Finset.univ.sup'
        (Finset.univ_nonempty (α := Fin (k + 2))) fun i ω => g i ω) = Z := by
      funext ω
      simp only [Z, Finset.sup'_apply]
    rwa [h2] at h1
  have hsumAbs : Integrable (fun ω => ∑ i, |g i ω|) μG :=
    integrable_finsetSum _ fun i _ => (hgmem i).integrable (by norm_num) |>.abs
  have hZint : Integrable Z μG := by
    refine hsumAbs.mono' hZm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    calc
      |Z ω| ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun i => |g i ω|) := HDP.abs_sup'_le Finset.univ_nonempty _
      _ ≤ ∑ i, |g i ω| := Finset.sup'_le _ _ fun i _ =>
        Finset.single_le_sum (f := fun j => |g j ω|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hexp_each : ∀ i,
      Integrable (fun ω => Real.exp (lam * g i ω)) μG := by
    intro i
    exact integrable_exp_mul_of_hasLaw_gaussian
      ⟨(hgm i).aemeasurable, hgmap i⟩ lam
  have hexpint : Integrable (fun ω => Real.exp (lam * Z ω)) μG := by
    have hsum : Integrable (fun ω => ∑ i, Real.exp (lam * g i ω)) μG :=
      integrable_finsetSum _ fun i _ => hexp_each i
    refine hsum.mono'
      (measurable_exp.comp (hZm.const_mul lam)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
      (H := Finset.univ_nonempty (α := Fin (k + 2))) (fun i => g i ω)
    rw [show Z ω = g j ω by exact hj]
    exact Finset.single_le_sum (f := fun i => Real.exp (lam * g i ω))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  have hjensen : Real.exp (lam * ∫ ω, Z ω ∂μG) ≤
      ∫ ω, Real.exp (lam * Z ω) ∂μG := by
    have h := HDP.Chapter1.jensen_inequality convexOn_exp
      (hZint.const_mul lam) hexpint
    rwa [integral_const_mul] at h
  have hmgf : ∀ i,
      (∫ ω, Real.exp (lam * g i ω) ∂μG) ≤
        Real.exp (lam ^ 2 / 2) := by
    intro i
    have heq : (∫ ω, Real.exp (lam * g i ω) ∂μG) =
        Real.exp ((Real.toNNReal (‖a i‖ ^ 2) : ℝ) * lam ^ 2 / 2) := by
      change mgf (g i) μG lam = _
      rw [mgf_gaussianReal (hgmap i)]
      congr 1
      ring
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hnorm0 : 0 ≤ ‖a i‖ := norm_nonneg _
    have hsq : ‖a i‖ ^ 2 ≤ 1 := by nlinarith [ha i]
    rw [Real.coe_toNNReal (‖a i‖ ^ 2) (sq_nonneg _)]
    nlinarith [sq_nonneg lam]
  have hupper : (∫ ω, Real.exp (lam * Z ω) ∂μG) ≤
      N * Real.exp (lam ^ 2 / 2) := by
    calc
      (∫ ω, Real.exp (lam * Z ω) ∂μG) ≤
          ∫ ω, ∑ i, Real.exp (lam * g i ω) ∂μG := by
        apply integral_mono_ae hexpint
          (integrable_finsetSum _ fun i _ => hexp_each i)
        filter_upwards [] with ω
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
          (H := Finset.univ_nonempty (α := Fin (k + 2))) (fun i => g i ω)
        rw [show Z ω = g j ω by exact hj]
        exact Finset.single_le_sum (f := fun i => Real.exp (lam * g i ω))
          (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)
      _ = ∑ i, ∫ ω, Real.exp (lam * g i ω) ∂μG :=
        integral_finsetSum _ fun i _ => hexp_each i
      _ ≤ ∑ _i : Fin (k + 2), Real.exp (lam ^ 2 / 2) :=
        Finset.sum_le_sum fun i _ => hmgf i
      _ = N * Real.exp (lam ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [N]
        push_cast
        ring
  have hlog := Real.log_le_log (Real.exp_pos _) (hjensen.trans hupper)
  have hN0 : N ≠ 0 := ne_of_gt (zero_lt_one.trans hN)
  rw [Real.log_exp, Real.log_mul hN0 (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hlamsq : lam ^ 2 = 2 * Real.log N := by
    dsimp [lam]
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hlogN.le
  have hresult : (∫ ω, Z ω ∂μG) ≤ lam := by
    rw [hlamsq] at hlog
    nlinarith
  simpa [expectedFiniteSupremum, HDP.Chapter5.finiteMaximum, Z, g, lam, N]
    using hresult

/-- Bounds the Gaussian maximum over a finite vertex set by the extended expected supremum over the ambient set.

**Lean implementation helper.** -/
private theorem finiteVertexGaussianMax_le {n : ℕ}
    (V : Finset (EuclideanSpace ℝ (Fin n))) (hV : V.Nonempty)
    (hunit : ∀ x ∈ V, ‖x‖ ≤ 1) :
    (∫ g, V.sup' hV (fun x => inner ℝ x g)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      Real.sqrt (2 * Real.log V.card) := by
  classical
  have hcardpos : 0 < V.card := Finset.card_pos.mpr hV
  by_cases hsmall : V.card < 2
  · have hcard1 : V.card = 1 := by omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard1
    have hzero := canonicalGaussianProcess_centered
      (fun _ : Unit => x) ()
    have hzero' :
        (∫ g, inner ℝ x g ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
      simpa [canonicalGaussianProcess] using hzero
    simp [hzero']
  · have hcard2 : 2 ≤ V.card := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, V.card = k + 2 :=
      ⟨V.card - 2, by omega⟩
    let e : Fin (k + 2) ≃ {x // x ∈ V} :=
      Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, Fintype.card_coe, hk])
    let a : Fin (k + 2) → EuclideanSpace ℝ (Fin n) := fun i => e i
    have ha : ∀ i, ‖a i‖ ≤ 1 := fun i => hunit (e i) (e i).property
    have himage : Finset.univ.image a = V := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro hx
        obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
        exact ⟨i, by exact congrArg Subtype.val hi⟩
    have hpoint : (fun g => V.sup' hV (fun x => inner ℝ x g)) =
        HDP.Chapter5.finiteMaximum (canonicalGaussianProcess a) := by
      funext g
      unfold HDP.Chapter5.finiteMaximum
      apply le_antisymm
      · apply Finset.sup'_le
        intro x hx
        obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
        have hval : a i = x := congrArg Subtype.val hi
        rw [← hval]
        exact Finset.le_sup' (fun i => canonicalGaussianProcess a i g)
          (Finset.mem_univ i)
      · apply Finset.sup'_le
        intro i hi
        exact Finset.le_sup' (fun x => inner ℝ x g) (e i).property
    rw [hpoint, ← expectedFiniteSupremum]
    simpa [hk, Nat.cast_add, Nat.cast_ofNat] using
      canonicalGaussian_fin_max_le a ha

/-- The canonical Gaussian increment second moment equals squared Euclidean distance.

**Lean implementation helper.** -/
private lemma canonicalGaussian_incrementSecondMoment
    {I : Type*} {n : ℕ}
    (a : I → EuclideanSpace ℝ (Fin n)) (i j : I) :
    processIncrementSecondMoment
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (canonicalGaussianProcess a) i j = ‖a i - a j‖ ^ 2 := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (innerSL ℝ) (a i - a j)
  have hId : HasGaussianLaw
      (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.hasGaussianLaw_id
  have hmem : MemLp L 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [Function.comp_def] using (hId.map L).memLp_two
  have hv := variance_eq_sub hmem
  rw [integral_strongDual_stdGaussian L, variance_dual_stdGaussian L,
    innerSL_apply_norm] at hv
  change ‖a i - a j‖ ^ 2 =
    (∫ g : EuclideanSpace ℝ (Fin n), (L g) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) - 0 ^ 2 at hv
  norm_num at hv
  unfold processIncrementSecondMoment
  calc
    (∫ g : EuclideanSpace ℝ (Fin n),
        (canonicalGaussianProcess a i g -
          canonicalGaussianProcess a j g) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∫ g : EuclideanSpace ℝ (Fin n), (L g) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp [canonicalGaussianProcess, L, innerSL_apply_apply]
    _ = ‖a i - a j‖ ^ 2 := hv.symm

/-- A polytope with `N` vertices has logarithmic covering-number bound controlled by its diameter and `log N`. This form is equivalent to a power bound and avoids raising an
extended-natural number to a non-natural exponent. The proof applies the
strong separated-set form of Sudakov minoration to the canonical Gaussian
process, reduces the support function of the convex hull to its vertices, and
uses the sharp finite Gaussian maximal inequality.

**Book Corollary 7.4.3.** -/
theorem polytopeCovering_log_bound
    {n : ℕ} (V : Finset (EuclideanSpace ℝ (Fin n)))
    (hV : V.Nonempty) (hunit : ∀ x ∈ V, ‖x‖ ≤ 1)
    (ε : ℝ≥0) (hε : 0 < ε)
    (hfinite : Metric.coveringNumber ε
      (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) ≠ ⊤) :
    Real.log (HDP.finiteCoveringNumber ε
        (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) hfinite) ≤
      10000 * Real.log V.card / (ε : ℝ) ^ 2 := by
  classical
  let A : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (V : Set _)
  let N : ℕ := HDP.finiteCoveringNumber ε A hfinite
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hV
    refine ⟨x, ?_⟩
    change x ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))
    have hxset : x ∈ (V : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa using hx
    apply subset_convexHull ℝ
    exact hxset
  have hNpos : 0 < N := by
    have hcovpos : 0 < Metric.coveringNumber ε A := by simpa using hAne
    have hcoe := HDP.coe_finiteCoveringNumber ε A hfinite
    have hNenat : (0 : ℕ∞) < (N : ℕ∞) := by
      rw [show (N : ℕ∞) = Metric.coveringNumber ε A by
        exact hcoe]
      exact hcovpos
    exact_mod_cast hNenat
  by_cases hsmall : N < 2
  · have hN1 : N = 1 := by omega
    change Real.log N ≤ _
    rw [hN1]
    simp only [Nat.cast_one, Real.log_one]
    have hcard1 : (1 : ℝ) ≤ V.card := by
      exact_mod_cast (Finset.one_le_card.mpr hV)
    have hlogV : 0 ≤ Real.log (V.card : ℝ) := Real.log_nonneg hcard1
    positivity
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, N = k + 2 :=
      ⟨N - 2, by omega⟩
    have hAcompact : IsCompact A := by
      dsimp [A]
      exact V.finite_toSet.isCompact_convexHull ℝ
    have hAclosure : IsCompact (closure A) := by
      rw [hAcompact.isClosed.closure_eq]
      exact hAcompact
    have hhalf : ε / 2 ≠ 0 := div_ne_zero (ne_of_gt hε) (by norm_num)
    obtain ⟨C, hCA, hCfinite, hCcover⟩ :=
      Metric.exists_finite_isCover_of_isCompact_closure hhalf hAclosure
    have hext : Metric.externalCoveringNumber (ε / 2) A ≠ ⊤ :=
      ne_top_of_le_ne_top hCfinite.encard_lt_top.ne
        hCcover.externalCoveringNumber_le_encard
    have hpackfinite : Metric.packingNumber ε A ≠ ⊤ := by
      have hle := Metric.packingNumber_two_mul_le_externalCoveringNumber
        (ε / 2) A
      have htwo : (2 : ℝ≥0) * (ε / 2) = ε :=
        mul_div_cancel₀ ε (by norm_num)
      rw [htwo] at hle
      exact ne_top_of_le_ne_top hext hle
    let P : Set (EuclideanSpace ℝ (Fin n)) :=
      Metric.maximalSeparatedSet ε A
    have hPfinite : P.Finite := by
      apply Set.encard_lt_top_iff.mp
      rw [show P = Metric.maximalSeparatedSet ε A by rfl,
        Metric.encard_maximalSeparatedSet hpackfinite]
      exact hpackfinite.lt_top
    letI : Fintype P := hPfinite.fintype
    have hNPenat : (N : ℕ∞) ≤ P.encard := by
      rw [HDP.coe_finiteCoveringNumber ε A hfinite]
      calc
        Metric.coveringNumber ε A ≤ Metric.packingNumber ε A :=
          Metric.coveringNumber_le_packingNumber ε A
        _ = P.encard := by
          symm
          exact Metric.encard_maximalSeparatedSet hpackfinite
    have hNP : N ≤ Fintype.card P := by
      have hNP' : (N : ℕ∞) ≤ (Fintype.card P : ℕ∞) := by
        simpa only [Set.coe_fintypeCard] using hNPenat
      exact_mod_cast hNP'
    have hcard : Fintype.card (Fin (k + 2)) ≤ Fintype.card P := by
      simpa [hk] using hNP
    let e : Fin (k + 2) ↪ P :=
      Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
    let a : Fin (k + 2) → EuclideanSpace ℝ (Fin n) := fun i => e i
    have haA : ∀ i, a i ∈ A := fun i =>
      Metric.maximalSeparatedSet_subset (e i).property
    have hsep : ∀ i j, i ≠ j → (ε : ℝ) < dist (a i) (a j) := by
      intro i j hij
      have hijE : (a i : EuclideanSpace ℝ (Fin n)) ≠ a j := by
        intro h
        apply hij
        exact e.injective (Subtype.ext h)
      have hed := Metric.isSeparated_maximalSeparatedSet
        (show a i ∈ P from (e i).property)
        (show a j ∈ P from (e j).property) hijE
      simpa [edist_dist] using hed
    let X := canonicalGaussianProcess
      (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    have hX : IsGaussianProcess X
        (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
      canonicalGaussianProcess_isGaussian id
    have hX0 : ∀ x, ∫ g, X x g
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = 0 :=
      canonicalGaussianProcess_centered id
    have hcanonical : ∀ x y,
        dist x y ^ 2 = processIncrementSecondMoment
          (stdGaussian (EuclideanSpace ℝ (Fin n))) X x y := by
      intro x y
      rw [canonicalGaussian_incrementSecondMoment]
      simp only [id_eq, dist_eq_norm]
    have hlower := sudakovSeparated_strong
      (stdGaussian (EuclideanSpace ℝ (Fin n))) X hX hX0 hcanonical
      ε k a hsep
    have hlower' : (Real.sqrt 2 / 100) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) ≤
      expectedFiniteSupremum
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (canonicalGaussianProcess a) := by
      have hproc : (fun i => X (a i)) = canonicalGaussianProcess a := by
        funext i g
        rfl
      rw [hproc] at hlower
      exact hlower
    let M : EuclideanSpace ℝ (Fin n) → ℝ := fun g =>
      V.sup' hV (fun x => inner ℝ x g)
    have hcoordInt : ∀ x : EuclideanSpace ℝ (Fin n),
        Integrable (fun g => inner ℝ x g)
          (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
      intro x
      exact ((canonicalGaussianProcess_isGaussian id).hasGaussianLaw_eval x).memLp_two.integrable
        (by norm_num)
    have hMInt : Integrable M
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
      have hraw : Integrable (V.sup' hV (fun x g => inner ℝ x g))
          (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
        refine Finset.sup'_induction hV (fun x g => inner ℝ x g)
          (p := fun f => Integrable f
            (stdGaussian (EuclideanSpace ℝ (Fin n)))) ?_ ?_
        · intro f hf g hg
          exact hf.sup hg
        · intro x hx
          exact hcoordInt x
      apply (integrable_congr ?_).mp hraw
      filter_upwards [] with g
      simp only [M, Finset.sup'_apply]
    have hselInt : Integrable
        (HDP.Chapter5.finiteMaximum (canonicalGaussianProcess a))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
      have hraw : Integrable
          (Finset.univ.sup' Finset.univ_nonempty (canonicalGaussianProcess a))
          (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
        refine Finset.sup'_induction Finset.univ_nonempty
          (canonicalGaussianProcess a)
          (p := fun f => Integrable f
            (stdGaussian (EuclideanSpace ℝ (Fin n)))) ?_ ?_
        · intro f hf g hg
          exact hf.sup hg
        · intro i hi
          exact hcoordInt (a i)
      apply (integrable_congr ?_).mp hraw
      filter_upwards [] with g
      simp only [HDP.Chapter5.finiteMaximum, Finset.sup'_apply]
    have hpoint : ∀ g,
        HDP.Chapter5.finiteMaximum (canonicalGaussianProcess a) g ≤ M g := by
      intro g
      unfold HDP.Chapter5.finiteMaximum
      apply Finset.sup'_le
      intro i hi
      have hlinear : ConvexOn ℝ Set.univ
          (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x g) := by
        simpa [real_inner_comm] using
          (((innerSL ℝ) g).toLinearMap.convexOn
            (convex_univ : Convex ℝ
              (Set.univ : Set (EuclideanSpace ℝ (Fin n)))))
      exact hlinear.le_sup_of_mem_convexHull (Set.subset_univ _) (haA i)
    have hselectedUpper : expectedFiniteSupremum
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (canonicalGaussianProcess a) ≤
          Real.sqrt (2 * Real.log V.card) := by
      calc
        expectedFiniteSupremum
            (stdGaussian (EuclideanSpace ℝ (Fin n)))
            (canonicalGaussianProcess a) ≤
            ∫ g, M g ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
          integral_mono hselInt hMInt hpoint
        _ ≤ Real.sqrt (2 * Real.log V.card) := by
          simpa [M] using finiteVertexGaussianMax_le V hV hunit
    have hbound := hlower'.trans hselectedUpper
    change Real.log N ≤ _
    rw [hk, Nat.cast_add, Nat.cast_ofNat]
    have hkreal : (1 : ℝ) ≤ (k : ℝ) + 2 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hlogN : 0 ≤ Real.log ((k : ℝ) + 2) :=
      Real.log_nonneg hkreal
    have hcardReal : (1 : ℝ) ≤ V.card := by
      exact_mod_cast (Finset.one_le_card.mpr hV)
    have hlogV : 0 ≤ Real.log (V.card : ℝ) :=
      Real.log_nonneg hcardReal
    have hlhs0 : 0 ≤ (Real.sqrt 2 / 100) * (ε : ℝ) *
        Real.sqrt (Real.log ((k : ℝ) + 2)) := by positivity
    have hsq : ((Real.sqrt 2 / 100) * (ε : ℝ) *
          Real.sqrt (Real.log ((k : ℝ) + 2))) ^ 2 ≤
        (Real.sqrt (2 * Real.log V.card)) ^ 2 :=
      (sq_le_sq₀ hlhs0 (Real.sqrt_nonneg _)).2 hbound
    have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    have hsqrtNsq : Real.sqrt (Real.log ((k : ℝ) + 2)) ^ 2 =
        Real.log ((k : ℝ) + 2) := Real.sq_sqrt hlogN
    have hsqrtVsq : Real.sqrt (2 * Real.log (V.card : ℝ)) ^ 2 =
        2 * Real.log (V.card : ℝ) :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hlogV)
    have hsq' : (2 / 10000 : ℝ) * (ε : ℝ) ^ 2 *
        Real.log ((k : ℝ) + 2) ≤ 2 * Real.log (V.card : ℝ) := by
      calc
        (2 / 10000 : ℝ) * (ε : ℝ) ^ 2 *
            Real.log ((k : ℝ) + 2) =
            ((Real.sqrt 2 / 100) * (ε : ℝ) *
              Real.sqrt (Real.log ((k : ℝ) + 2))) ^ 2 := by
          rw [show ((Real.sqrt 2 / 100) * (ε : ℝ) *
              Real.sqrt (Real.log ((k : ℝ) + 2))) ^ 2 =
              (Real.sqrt 2 ^ 2 / 10000) * (ε : ℝ) ^ 2 *
                Real.sqrt (Real.log ((k : ℝ) + 2)) ^ 2 by ring,
            hsqrt2sq, hsqrtNsq]
        _ ≤ Real.sqrt (2 * Real.log V.card) ^ 2 := hsq
        _ = 2 * Real.log (V.card : ℝ) := hsqrtVsq
    apply (le_div_iff₀ (by positivity : 0 < (ε : ℝ) ^ 2)).2
    nlinarith [hsq']

end

end HDP.Chapter7

end Source_07_SudakovInequality

/-! ## Material formerly in `08_GaussianWidth.lean` -/

section Source_08_GaussianWidth

/-!
# Book Chapter 7, §7.5: Gaussian width

An ordinary real expectation of a supremum over an arbitrary set need not be
measurable or finite.  The real API in this file is therefore for finite
Euclidean sets.  It is total by the harmless convention that the support of
the empty finite set is zero; every source-facing result requiring a selected
point carries `T.Nonempty`.  The preceding Sudakov module's `EReal` supremum
is the authoritative arbitrary-set interface.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter7

noncomputable section

variable {n : ℕ}

/-- Pointwise support function of a finite Euclidean set, with value zero on
the empty set.

**Lean implementation helper.** -/
def finiteGaussianSupport (T : Finset (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if hT : T.Nonempty then
    (T.sup' hT (fun x ↦ fun z : EuclideanSpace ℝ (Fin n) ↦ inner ℝ z x)) g
  else 0

/-- Gaussian width is the expected support of a set in a standard Gaussian direction. Finite form.

**Book Definition 7.5.1.** -/
def gaussianWidth (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ g, finiteGaussianSupport T g
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Expresses finite Gaussian support as a supremum over the finite index set.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_eq_sup'
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport T g = T.sup' hT (fun x ↦ inner ℝ g x) := by
  simp only [finiteGaussianSupport, dif_pos hT, Finset.sup'_apply]

/-- Finite Gaussian support of the empty set is zero.

**Lean implementation helper.** -/
@[simp] theorem finiteGaussianSupport_empty
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport ∅ g = 0 := by
  simp [finiteGaussianSupport]

/-- The finite Gaussian support is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteGaussianSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Measurable (finiteGaussianSupport T) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show finiteGaussianSupport T =
        T.sup' hT (fun x ↦ fun g ↦ inner ℝ g x) by
      funext g
      simp [finiteGaussianSupport, hT]]
    apply Finset.measurable_sup' hT
    intro x _
    fun_prop
  · rw [show finiteGaussianSupport T = 0 by
      funext g
      simp [finiteGaussianSupport, hT]]
    fun_prop

/-- Every inner product with a standard Gaussian vector is integrable.

**Lean implementation helper.** -/
theorem integrable_inner_stdGaussian (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) ↦ inner ℝ g x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  simpa [real_inner_comm] using
    ((innerSL ℝ) x).integrable_comp
      (isGaussian_stdGaussian (E := EuclideanSpace ℝ (Fin n))).integrable_id

/-- Finite Gaussian support is integrable under the standard Gaussian measure.

**Lean implementation helper.** -/
theorem integrable_finiteGaussianSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Integrable (finiteGaussianSupport T)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show finiteGaussianSupport T =
        T.sup' hT (fun x ↦ fun g ↦ inner ℝ g x) by
      funext g
      simp [finiteGaussianSupport, hT]]
    refine Finset.sup'_induction hT
      (f := fun x ↦ fun g : EuclideanSpace ℝ (Fin n) ↦ inner ℝ g x)
      (p := fun f => Integrable f
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ?_ ?_
    · intro f hf g hg
      exact hf.sup hg
    · intro x hx
      exact integrable_inner_stdGaussian x
  · rw [show finiteGaussianSupport T = 0 by
      funext g
      simp [finiteGaussianSupport, hT]]
    fun_prop

/-- The expectation of a standard Gaussian inner product is zero.

**Lean implementation helper.** -/
theorem integral_inner_stdGaussian (x : EuclideanSpace ℝ (Fin n)) :
    (∫ g : EuclideanSpace ℝ (Fin n), inner ℝ g x
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  simpa [real_inner_comm] using
    integral_strongDual_stdGaussian ((innerSL ℝ) x)

/-- The first moment of the Euclidean norm of a standard Gaussian vector is
at most the square root of the dimension. This is the explicit `L²`
Cauchy--Schwarz step used in Proposition 7.5.2(f).

**Book Proposition 7.5.2(f).** -/
theorem integral_norm_stdGaussian_le_sqrt_card (n : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.sqrt n := by
  let ν := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hcoord (i : Fin n) :
      (∫ g : EuclideanSpace ℝ (Fin n), (g i) ^ 2 ∂ν) = 1 := by
    let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
    let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := (innerSL ℝ) u
    have hId : HasGaussianLaw
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ν :=
      IsGaussian.hasGaussianLaw_id
    have hmem : MemLp L 2 ν := by
      simpa [L, Function.comp_def] using (hId.map L).memLp_two
    have hv := variance_eq_sub hmem
    rw [integral_strongDual_stdGaussian L, variance_dual_stdGaussian L] at hv
    have hLu : ‖L‖ = 1 := by simp [L, u, innerSL_apply_norm]
    rw [hLu] at hv
    have hfun : ∀ g : EuclideanSpace ℝ (Fin n), L g = g i := by
      intro g
      simp [L, u, innerSL_apply_apply, PiLp.inner_apply]
    change 1 ^ 2 = (∫ x, (L x) ^ 2 ∂ν) - 0 ^ 2 at hv
    simp_rw [hfun] at hv
    nlinarith
  have hsq : (∫ g : EuclideanSpace ℝ (Fin n), ‖g‖ ^ 2 ∂ν) = n := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum]
    · simp_rw [hcoord]
      simp
    · intro i _
      let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
      let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := (innerSL ℝ) u
      have hId : HasGaussianLaw
          (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ν :=
        IsGaussian.hasGaussianLaw_id
      have hmem : MemLp L 2 ν := by
        simpa [L, Function.comp_def] using (hId.map L).memLp_two
      have hi := hmem.integrable_norm_pow' (p := 2)
      simpa [L, u, innerSL_apply_apply, PiLp.inner_apply,
        Real.norm_eq_abs, sq_abs] using hi
  have hIdMem : MemLp
      (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    IsGaussian.memLp_id ν 2 (by simp)
  have hnormMem : MemLp (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖g‖)
      (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using hIdMem.norm
  have honeMem : MemLp (fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using (memLp_const (p := ENNReal.ofReal (2 : ℝ)) (1 : ℝ))
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := ν) Real.HolderConjugate.two_two
    (f := fun g : EuclideanSpace ℝ (Fin n) ↦ ‖g‖)
    (g := fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ by norm_num)
    hnormMem honeMem
  simp only [Real.rpow_two] at h
  rw [hsq] at h
  simpa [ν, Real.sqrt_eq_rpow] using h

/-- Each Gaussian inner product is bounded by the finite Gaussian support over a nonempty set.

**Lean implementation helper.** -/
theorem inner_le_finiteGaussianSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T)
    (g : EuclideanSpace ℝ (Fin n)) :
    inner ℝ g x ≤ finiteGaussianSupport T g := by
  rw [finiteGaussianSupport_eq_sup' T hT]
  exact Finset.le_sup' (fun y ↦ inner ℝ g y) hx

/-- The Gaussian width is nonnegative.

**Lean implementation helper.** -/
theorem gaussianWidth_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    0 ≤ gaussianWidth T := by
  obtain ⟨x, hx⟩ := hT
  rw [gaussianWidth, ← integral_inner_stdGaussian x]
  exact integral_mono (integrable_inner_stdGaussian x)
    (integrable_finiteGaussianSupport T)
    (fun g ↦ inner_le_finiteGaussianSupport T ⟨x, hx⟩ hx g)

/-- Gaussian width of the empty set is zero.

**Lean implementation helper.** -/
@[simp] theorem gaussianWidth_empty :
    gaussianWidth (∅ : Finset (EuclideanSpace ℝ (Fin n))) = 0 := by
  simp [gaussianWidth]

/-- Gaussian width of a singleton is zero.

**Lean implementation helper.** -/
@[simp] theorem gaussianWidth_singleton (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWidth {x} = 0 := by
  rw [gaussianWidth]
  simp only [finiteGaussianSupport_eq_sup' {x} (by simp), Finset.sup'_singleton]
  exact integral_inner_stdGaussian x

/-- The Gaussian width is monotone under set inclusion.

**Lean implementation helper.** -/
theorem gaussianWidth_mono
    {S T : Finset (EuclideanSpace ℝ (Fin n))}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T) :
    gaussianWidth S ≤ gaussianWidth T := by
  apply integral_mono (integrable_finiteGaussianSupport S)
    (integrable_finiteGaussianSupport T)
  intro g
  rw [finiteGaussianSupport_eq_sup' S hS,
    finiteGaussianSupport_eq_sup' T hT]
  apply (Finset.sup'_le_iff hS (fun x ↦ inner ℝ g x)).mpr
  intro x hx
  exact Finset.le_sup' (fun y ↦ inner ℝ g y) (hST hx)

/-- Translation of a finite set.

**Lean implementation helper.** -/
def translateFinset (y : EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) :=
  T.image (fun x ↦ x + y)

/-- Translating a nonempty finite set preserves nonemptiness.

**Lean implementation helper.** -/
theorem translateFinset_nonempty
    (y : EuclideanSpace ℝ (Fin n))
    {T : Finset (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (translateFinset y T).Nonempty := hT.image _

/-- Translation adds the Gaussian inner product with the translation vector to finite Gaussian support.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_translate
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (y g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (translateFinset y T) g =
      finiteGaussianSupport T g + inner ℝ g y := by
  classical
  rw [finiteGaussianSupport_eq_sup' _ (translateFinset_nonempty y hT),
    finiteGaussianSupport_eq_sup' T hT]
  unfold translateFinset
  rw [Finset.sup'_image]
  change T.sup' _ (fun x ↦ inner ℝ g (x + y)) = _
  simp_rw [inner_add_right]
  exact (Finset.sup'_add T (fun x ↦ inner ℝ g x) (inner ℝ g y) hT).symm

/-- Proposition 7.5.2(b), translation part (Exercise 7.15).

**Book Proposition 7.5.2(b).** -/
theorem gaussianWidth_translate
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (y : EuclideanSpace ℝ (Fin n)) :
    gaussianWidth (translateFinset y T) = gaussianWidth T := by
  rw [gaussianWidth, gaussianWidth]
  simp_rw [finiteGaussianSupport_translate T hT y]
  rw [integral_add (integrable_finiteGaussianSupport T)
    (integrable_inner_stdGaussian y), integral_inner_stdGaussian, add_zero]

/-- Orthogonal image of a finite set.

**Lean implementation helper.** -/
def orthogonalImageFinset
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) := T.image U

/-- An orthogonal image of a nonempty finite set is nonempty.

**Lean implementation helper.** -/
theorem orthogonalImageFinset_nonempty
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {T : Finset (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (orthogonalImageFinset U T).Nonempty := hT.image _

/-- Orthogonal images transform finite Gaussian support by the adjoint action on the Gaussian vector.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_orthogonalImage
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (orthogonalImageFinset U T) g =
      finiteGaussianSupport T (U.symm g) := by
  classical
  rw [finiteGaussianSupport_eq_sup' _ (orthogonalImageFinset_nonempty U hT),
    finiteGaussianSupport_eq_sup' T hT]
  unfold orthogonalImageFinset
  rw [Finset.sup'_image]
  change T.sup' _ ((fun z ↦ inner ℝ g z) ∘ U) = _
  refine Finset.sup'_congr _ rfl ?_
  intro x hx
  simpa [Function.comp_apply, real_inner_comm] using U.inner_map_eq_flip x g

/-- Proposition 7.5.2(b), orthogonal invariance (Exercise 7.15).

**Book Proposition 7.5.2(b).** -/
theorem gaussianWidth_orthogonalImage
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianWidth (orthogonalImageFinset U T) = gaussianWidth T := by
  rw [gaussianWidth, gaussianWidth]
  simp_rw [finiteGaussianSupport_orthogonalImage U T hT]
  have hi := integral_map_equiv
    (μ := stdGaussian (EuclideanSpace ℝ (Fin n))) U.symm.toMeasurableEquiv
    (finiteGaussianSupport T)
  have hmap : Measure.map (⇑U.symm.toMeasurableEquiv)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    simpa using stdGaussian_map U.symm
  rw [hmap] at hi
  simpa using hi.symm

/-! ### Convex hulls -/

/-- Support function of the genuine convex hull of a finite set. This
separate definition lets Proposition 7.5.2(c) retain its set-theoretic meaning
while the chapter's primary, automatically measurable width API remains
finite.

**Book Proposition 7.5.2(c).** -/
def convexHullGaussianSupport
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x ↦ inner ℝ g x) '' convexHull ℝ (T : Set _))

/-- A linear functional has the same supremum on a nonempty finite set and
on its convex hull. This is the pointwise mathematical core of Proposition
7.5.2(c).

**Book Proposition 7.5.2(c).** -/
theorem convexHullGaussianSupport_eq
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    convexHullGaussianSupport T g = finiteGaussianSupport T g := by
  let V : Set ℝ :=
    (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ g x) ''
      convexHull ℝ (T : Set _)
  have hlinear : ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ g x) := by
    simpa [real_inner_comm] using
      (((innerSL ℝ) g).toLinearMap.convexOn (convex_univ :
        Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))))
  have hupper : ∀ z ∈ V, z ≤ finiteGaussianSupport T g := by
    rintro z ⟨x, hx, rfl⟩
    rw [finiteGaussianSupport_eq_sup' T hT]
    exact hlinear.le_sup_of_mem_convexHull (Set.subset_univ _) hx
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hT
    have hxc : x ∈ convexHull ℝ
        (T : Set (EuclideanSpace ℝ (Fin n))) :=
      (subset_convexHull ℝ
        (T : Set (EuclideanSpace ℝ (Fin n)))) (by exact hx)
    exact ⟨inner ℝ g x, x, hxc, rfl⟩
  have hVbdd : BddAbove V :=
    ⟨finiteGaussianSupport T g, hupper⟩
  apply le_antisymm
  · exact csSup_le hVne hupper
  · rw [finiteGaussianSupport_eq_sup' T hT]
    apply (Finset.sup'_le_iff hT (fun x ↦ inner ℝ g x)).mpr
    intro x hx
    apply le_csSup hVbdd
    have hxc : x ∈ convexHull ℝ
        (T : Set (EuclideanSpace ℝ (Fin n))) :=
      (subset_convexHull ℝ
        (T : Set (EuclideanSpace ℝ (Fin n)))) (by exact hx)
    exact ⟨x, hxc, rfl⟩

/-- The Gaussian width of `convexHull T` is the integral of `convexHullGaussianSupport T g` against the standard Gaussian measure.

**Lean implementation helper.** -/
def convexHullGaussianWidth
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ g, convexHullGaussianSupport T g
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Gaussian width is finite for bounded sets and obeys scaling, Minkowski, convex-hull, symmetry, diameter, and linear-image laws. Taking a convex hull does not change Gaussian width.

**Book Proposition 7.5.2.** -/
theorem gaussianWidth_convexHull
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    convexHullGaussianWidth T = gaussianWidth T := by
  rw [convexHullGaussianWidth, gaussianWidth]
  apply integral_congr_ae
  filter_upwards [] with g
  exact convexHullGaussianSupport_eq T hT g

/-- Finite Minkowski sum.

**Lean implementation helper.** -/
def minkowskiSumFinset
    (T S : Finset (EuclideanSpace ℝ (Fin n))) :=
  (T.product S).image (fun p ↦ p.1 + p.2)

/-- The Minkowski sum of two nonempty finite sets is nonempty.

**Lean implementation helper.** -/
theorem minkowskiSumFinset_nonempty
    {T S : Finset (EuclideanSpace ℝ (Fin n))}
    (hT : T.Nonempty) (hS : S.Nonempty) :
    (minkowskiSumFinset T S).Nonempty := (hT.product hS).image _

/-- Finite Gaussian support is additive under Minkowski sums.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_minkowskiSum
    (T S : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) (hS : S.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (minkowskiSumFinset T S) g =
      finiteGaussianSupport T g + finiteGaussianSupport S g := by
  classical
  rw [finiteGaussianSupport_eq_sup' _ (minkowskiSumFinset_nonempty hT hS),
    finiteGaussianSupport_eq_sup' T hT,
    finiteGaussianSupport_eq_sup' S hS]
  unfold minkowskiSumFinset
  rw [Finset.sup'_image]
  change (T.product S).sup' _ (fun p ↦ inner ℝ g (p.1 + p.2)) = _
  rw [show (T.product S).sup' _ (fun p ↦ inner ℝ g (p.1 + p.2)) =
      T.sup' hT (fun x ↦ S.sup' hS
        (fun y ↦ inner ℝ g (x + y))) by
    exact Finset.sup'_product_left (hT.product hS)
      (fun p ↦ inner ℝ g (p.1 + p.2))]
  simp_rw [inner_add_right]
  have hrow (x : EuclideanSpace ℝ (Fin n)) :
      S.sup' hS (fun y ↦ inner ℝ g x + inner ℝ g y) =
        inner ℝ g x + S.sup' hS (fun y ↦ inner ℝ g y) := by
    simpa [add_comm] using
      (Finset.sup'_add S (fun y ↦ inner ℝ g y) (inner ℝ g x) hS).symm
  simp_rw [hrow]
  simpa using
    (Finset.sup'_add T (fun x ↦ inner ℝ g x)
      (S.sup' hS (fun y ↦ inner ℝ g y)) hT).symm

/-- Gaussian width is finite for bounded sets and obeys scaling, Minkowski, convex-hull, symmetry, diameter, and linear-image laws. Proposition 7.5.2(d), Minkowski addition (Exercise 7.15).

**Book Proposition 7.5.2.** -/
theorem gaussianWidth_minkowskiSum
    (T S : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) (hS : S.Nonempty) :
    gaussianWidth (minkowskiSumFinset T S) = gaussianWidth T + gaussianWidth S := by
  rw [gaussianWidth, gaussianWidth, gaussianWidth]
  simp_rw [finiteGaussianSupport_minkowskiSum T S hT hS]
  exact integral_add (integrable_finiteGaussianSupport T)
    (integrable_finiteGaussianSupport S)

/-- Finite dilation.

**Lean implementation helper.** -/
def scaleFinset (a : ℝ) (T : Finset (EuclideanSpace ℝ (Fin n))) :=
  T.image (fun x ↦ a • x)

/-- Scaling a nonempty finite set preserves nonemptiness.

**Lean implementation helper.** -/
theorem scaleFinset_nonempty (a : ℝ)
    {T : Finset (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (scaleFinset a T).Nonempty := hT.image _

/-- Scaling a finite set by a nonnegative scalar scales its finite Gaussian support.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_scale_of_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (scaleFinset a T) g =
      a * finiteGaussianSupport T g := by
  classical
  rw [finiteGaussianSupport_eq_sup' _ (scaleFinset_nonempty a hT),
    finiteGaussianSupport_eq_sup' T hT]
  unfold scaleFinset
  rw [Finset.sup'_image]
  change T.sup' _ (fun x ↦ inner ℝ g (a • x)) = _
  simp_rw [inner_smul_right]
  exact (Finset.mul₀_sup' ha (fun x ↦ inner ℝ g x) T hT).symm

/-- Gaussian width scales linearly under nonnegative dilations.

**Lean implementation helper.** -/
theorem gaussianWidth_scale_of_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {a : ℝ} (ha : 0 ≤ a) :
    gaussianWidth (scaleFinset a T) = a * gaussianWidth T := by
  rw [gaussianWidth, gaussianWidth]
  simp_rw [finiteGaussianSupport_scale_of_nonneg T hT ha]
  exact integral_const_mul _ _

/-- Negation of a finite set.

**Lean implementation helper.** -/
def negFinset (T : Finset (EuclideanSpace ℝ (Fin n))) := T.image (-·)

/-- Negating a nonempty finite set preserves nonemptiness.

**Lean implementation helper.** -/
theorem negFinset_nonempty
    {T : Finset (EuclideanSpace ℝ (Fin n))} (hT : T.Nonempty) :
    (negFinset T).Nonempty := hT.image _

/-- Gaussian width is invariant under negating the set.

**Lean implementation helper.** -/
theorem gaussianWidth_neg
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianWidth (negFinset T) = gaussianWidth T := by
  let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.neg ℝ
  simpa [negFinset, orthogonalImageFinset, U] using
    gaussianWidth_orthogonalImage U T hT

/-- Gaussian width is finite for bounded sets and obeys scaling, Minkowski, convex-hull, symmetry, diameter, and linear-image laws. Proposition 7.5.2(d), arbitrary real scaling (Exercise 7.15).

**Book Proposition 7.5.2.** -/
theorem gaussianWidth_scale
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (a : ℝ) :
    gaussianWidth (scaleFinset a T) = |a| * gaussianWidth T := by
  by_cases ha : 0 ≤ a
  · simpa [abs_of_nonneg ha] using gaussianWidth_scale_of_nonneg T hT ha
  · have hna : 0 ≤ -a := (neg_pos.mpr (lt_of_not_ge ha)).le
    have himage : scaleFinset a T = scaleFinset (-a) (negFinset T) := by
      classical
      ext x
      simp only [scaleFinset, negFinset, Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨-y, ⟨y, hy, rfl⟩, by simp⟩
      · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by simp⟩
    calc
      gaussianWidth (scaleFinset a T) =
          gaussianWidth (scaleFinset (-a) (negFinset T)) := congrArg gaussianWidth himage
      _ = (-a) * gaussianWidth (negFinset T) :=
        gaussianWidth_scale_of_nonneg (negFinset T) (negFinset_nonempty hT) hna
      _ = |a| * gaussianWidth T := by
        rw [gaussianWidth_neg T hT, abs_of_neg (lt_of_not_ge ha)]

/-- Width is the mean directional width of the difference set. Finite difference set.

**Book Equation (7.16).** -/
def differenceFinset
    (T S : Finset (EuclideanSpace ℝ (Fin n))) :=
  minkowskiSumFinset T (negFinset S)

/-- The difference of two nonempty finite sets is nonempty.

**Lean implementation helper.** -/
theorem differenceFinset_nonempty
    {T S : Finset (EuclideanSpace ℝ (Fin n))}
    (hT : T.Nonempty) (hS : S.Nonempty) :
    (differenceFinset T S).Nonempty :=
  minkowskiSumFinset_nonempty hT (negFinset_nonempty hS)

/-- The Gaussian width of a difference set is twice the Gaussian width of the original set.

**Lean implementation helper.** -/
theorem gaussianWidth_difference
    (T S : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) (hS : S.Nonempty) :
    gaussianWidth (differenceFinset T S) = gaussianWidth T + gaussianWidth S := by
  unfold differenceFinset
  rw [gaussianWidth_minkowskiSum T (negFinset S) hT (negFinset_nonempty hS),
    gaussianWidth_neg S hS]

/-- Width is the mean directional width of the difference set. Proposition 7.5.2(e), finite form.

**Book Equation (7.16).** -/
theorem gaussianWidth_eq_half_difference
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianWidth T = (1 / 2 : ℝ) * gaussianWidth (differenceFinset T T) := by
  rw [gaussianWidth_difference T T hT hT]
  ring

/-! ### Width and diameter -/

/-- Diameter of a finite Euclidean set, totalized by zero on the empty set.

**Lean implementation helper.** -/
def finiteEuclideanDiameter
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if hT : T.Nonempty then
    (T.product T).sup' (hT.product hT) (fun p ↦ ‖p.1 - p.2‖)
  else 0

/-- Expresses finite Euclidean diameter as the supremum of pairwise distances.

**Lean implementation helper.** -/
theorem finiteEuclideanDiameter_eq_sup'
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    finiteEuclideanDiameter T =
      (T.product T).sup' (hT.product hT) (fun p ↦ ‖p.1 - p.2‖) := by
  simp [finiteEuclideanDiameter, hT]

/-- The distance between any two members of a finite set is bounded by its Euclidean diameter.

**Lean implementation helper.** -/
theorem norm_sub_le_finiteEuclideanDiameter
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (hy : y ∈ T) :
    ‖x - y‖ ≤ finiteEuclideanDiameter T := by
  rw [finiteEuclideanDiameter_eq_sup' T hT]
  exact Finset.le_sup' (fun p ↦ ‖p.1 - p.2‖)
    (show (x, y) ∈ T.product T from Finset.mem_product.mpr ⟨hx, hy⟩)

/-- The finite Euclidean diameter is nonnegative.

**Lean implementation helper.** -/
theorem finiteEuclideanDiameter_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ finiteEuclideanDiameter T := by
  by_cases hT : T.Nonempty
  · have hT' := hT
    obtain ⟨x, hx⟩ := hT'
    exact (norm_nonneg (x - x)).trans
      (norm_sub_le_finiteEuclideanDiameter T hT hx hx)
  · simp [finiteEuclideanDiameter, hT]

/-- Bounds Gaussian support of a difference set by the Gaussian norm times the finite diameter.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_difference_le_norm_mul_diameter
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (differenceFinset T T) g ≤
      ‖g‖ * finiteEuclideanDiameter T := by
  classical
  rw [finiteGaussianSupport_eq_sup' _ (differenceFinset_nonempty hT hT)]
  apply (Finset.sup'_le_iff (differenceFinset_nonempty hT hT)
    (fun z ↦ inner ℝ g z)).mpr
  intro z hz
  unfold differenceFinset minkowskiSumFinset negFinset at hz
  rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hpT, hp2⟩
  rcases Finset.mem_image.mp hp2 with ⟨q, hqT, hq⟩
  rw [← hq]
  change inner ℝ g (p.1 - q) ≤ ‖g‖ * finiteEuclideanDiameter T
  exact (real_inner_le_norm g (p.1 - q)).trans
    (mul_le_mul_of_nonneg_left
      (norm_sub_le_finiteEuclideanDiameter T hT hpT hqT) (norm_nonneg g))

/-- Finite form.

**Book Proposition 7.5.2(f).** -/
theorem gaussianWidth_le_sqrt_card_mul_diameter
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianWidth T ≤
      Real.sqrt n / 2 * finiteEuclideanDiameter T := by
  let ν := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hnormInt : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖g‖) ν := by
    have hId : MemLp
        (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
      IsGaussian.memLp_id ν 2 (by simp)
    simpa using (hId.integrable (by norm_num : (1 : ENNReal) ≤ 2)).norm
  have hdiam0 := finiteEuclideanDiameter_nonneg T
  have hrhs : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) ↦
        ‖g‖ * finiteEuclideanDiameter T) ν := by
    simpa [mul_comm] using hnormInt.const_mul (finiteEuclideanDiameter T)
  have hint :
      (∫ g, finiteGaussianSupport (differenceFinset T T) g ∂ν) ≤
        ∫ g, ‖g‖ * finiteEuclideanDiameter T ∂ν :=
    integral_mono (integrable_finiteGaussianSupport (differenceFinset T T))
      hrhs (finiteGaussianSupport_difference_le_norm_mul_diameter T hT)
  have hrad := integral_norm_stdGaussian_le_sqrt_card n
  rw [gaussianWidth_eq_half_difference T hT, gaussianWidth]
  calc
    (1 / 2 : ℝ) *
        ∫ g, finiteGaussianSupport (differenceFinset T T) g ∂ν ≤
        (1 / 2 : ℝ) *
          ∫ g, ‖g‖ * finiteEuclideanDiameter T ∂ν := by
      gcongr
    _ = (1 / 2 : ℝ) *
        ((∫ g, ‖g‖ ∂ν) * finiteEuclideanDiameter T) := by
      rw [integral_mul_const]
    _ ≤ (1 / 2 : ℝ) *
        (Real.sqrt n * finiteEuclideanDiameter T) := by
      gcongr
    _ = Real.sqrt n / 2 * finiteEuclideanDiameter T := by ring

/-- The symmetric pair used to obtain the lower width--diameter estimate.

**Lean implementation helper.** -/
def diameterSymmetricPairFinset (v : EuclideanSpace ℝ (Fin n)) :
    Finset (EuclideanSpace ℝ (Fin n)) := {v, -v}

/-- Computes Gaussian support of the symmetric pair generated by a diameter vector.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_diameterSymmetricPair
    (v g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (diameterSymmetricPairFinset v) g =
      |inner ℝ g v| := by
  rw [finiteGaussianSupport_eq_sup' _ (by simp [diameterSymmetricPairFinset])]
  simp [diameterSymmetricPairFinset, abs_eq_max_neg]

/-- Exact width of a symmetric two-point set.

**Lean implementation helper.** -/
theorem gaussianWidth_diameterSymmetricPair_eq
    (v : EuclideanSpace ℝ (Fin n)) :
    gaussianWidth (diameterSymmetricPairFinset v) =
      (Real.sqrt 2 / Real.sqrt Real.pi) * ‖v‖ := by
  by_cases hv : v = 0
  · subst v
    simp [diameterSymmetricPairFinset]
  · let u : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v
    have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, hnv]
    have hvrep : v = ‖v‖ • u := by
      simp [u, smul_smul, hnv]
    have hlaw : HasLaw
        (fun g : EuclideanSpace ℝ (Fin n) ↦ inner ℝ g u)
        (gaussianReal 0 1)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
      have hmap := (IsGaussian.map_eq_gaussianReal ((innerSL ℝ) u) :
        (stdGaussian (EuclideanSpace ℝ (Fin n))).map ((innerSL ℝ) u) =
          gaussianReal
            ((stdGaussian (EuclideanSpace ℝ (Fin n)))[(innerSL ℝ) u])
            Var[(innerSL ℝ) u;
              stdGaussian (EuclideanSpace ℝ (Fin n))].toNNReal)
      rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
        innerSL_apply_norm, hu] at hmap
      refine ⟨(by fun_prop), ?_⟩
      simpa [innerSL_apply_apply, real_inner_comm] using hmap
    have habs := HDP.Chapter2.gaussian_absolute_moment
      hlaw (p := (1 : ℝ)) le_rfl
    have hs : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
      rw [← Real.sqrt_eq_rpow]
    rw [hs] at habs
    have habs' :
        (∫ g : EuclideanSpace ℝ (Fin n), |inner ℝ g u|
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
          Real.sqrt 2 / Real.sqrt Real.pi := by
      simpa [Real.rpow_one, Real.Gamma_one] using habs
    rw [gaussianWidth]
    simp_rw [finiteGaussianSupport_diameterSymmetricPair]
    calc
      (∫ g : EuclideanSpace ℝ (Fin n), |inner ℝ g v|
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
          ∫ g : EuclideanSpace ℝ (Fin n),
            ‖v‖ * |inner ℝ g u|
              ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        apply integral_congr_ae
        filter_upwards [] with g
        have hinner : inner ℝ g v = ‖v‖ * inner ℝ g u := by
          calc
            inner ℝ g v = inner ℝ g (‖v‖ • u) :=
              congrArg (fun z ↦ inner ℝ g z) hvrep
            _ = ‖v‖ * inner ℝ g u := by
              rw [inner_smul_right]
        rw [hinner, abs_mul, abs_of_nonneg (norm_nonneg v)]
      _ = ‖v‖ * (Real.sqrt 2 / Real.sqrt Real.pi) := by
        rw [integral_const_mul, habs']
      _ = (Real.sqrt 2 / Real.sqrt Real.pi) * ‖v‖ := by ring

/-- The symmetric pair generated by two points lies in their difference set.

**Lean implementation helper.** -/
theorem diameterSymmetricPair_subset_difference
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (hy : y ∈ T) :
    diameterSymmetricPairFinset (x - y) ⊆ differenceFinset T T := by
  classical
  intro z hz
  simp only [diameterSymmetricPairFinset, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · unfold differenceFinset minkowskiSumFinset negFinset
    apply Finset.mem_image.mpr
    refine ⟨(x, -y), Finset.mem_product.mpr ⟨hx, ?_⟩, by
      simp only [sub_eq_add_neg]⟩
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  · unfold differenceFinset minkowskiSumFinset negFinset
    apply Finset.mem_image.mpr
    refine ⟨(y, -x), Finset.mem_product.mpr ⟨hy, ?_⟩, by
      simp only [sub_eq_add_neg, neg_add_rev, neg_neg]⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Gaussian width is bounded below by a universal constant times any pairwise distance.

**Lean implementation helper.** -/
theorem gaussianWidth_pairwise_diameter_lower
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (hy : y ∈ T) :
    (1 / Real.sqrt (2 * Real.pi) : ℝ) * ‖x - y‖ ≤ gaussianWidth T := by
  have hpair : (diameterSymmetricPairFinset (x - y)).Nonempty := by
    simp [diameterSymmetricPairFinset]
  have hmono := gaussianWidth_mono hpair
    (differenceFinset_nonempty hT hT)
    (diameterSymmetricPair_subset_difference T hx hy)
  rw [gaussianWidth_diameterSymmetricPair_eq] at hmono
  have hc : (1 / Real.sqrt (2 * Real.pi) : ℝ) =
      (1 / 2 : ℝ) * (Real.sqrt 2 / Real.sqrt Real.pi) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    have hspi : Real.sqrt Real.pi ≠ 0 := by positivity
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hc, mul_assoc]
  calc
    (1 / 2 : ℝ) *
        ((Real.sqrt 2 / Real.sqrt Real.pi) * ‖x - y‖) ≤
        (1 / 2 : ℝ) * gaussianWidth (differenceFinset T T) := by
      gcongr
    _ = gaussianWidth T := (gaussianWidth_eq_half_difference T hT).symm

/-- Finite form.

**Book Proposition 7.5.2(f).** -/
theorem gaussianWidth_lower_diameter
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    (1 / Real.sqrt (2 * Real.pi) : ℝ) * finiteEuclideanDiameter T ≤
      gaussianWidth T := by
  rw [finiteEuclideanDiameter_eq_sup' T hT]
  have hc : 0 ≤ (1 / Real.sqrt (2 * Real.pi) : ℝ) := by positivity
  rw [Finset.mul₀_sup' hc (fun p : EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin n) ↦ ‖p.1 - p.2‖)
      (T.product T) (hT.product hT)]
  apply (Finset.sup'_le_iff (hT.product hT)
    (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
      (1 / Real.sqrt (2 * Real.pi) : ℝ) * ‖p.1 - p.2‖)).mpr
  intro p hp
  exact gaussianWidth_pairwise_diameter_lower T hT
    (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2

/-- Gaussian width is finite for bounded sets and obeys scaling, Minkowski, convex-hull, symmetry, diameter, and linear-image laws. Proposition 7.5.2(f), source-facing two-sided wrapper.

**Book Proposition 7.5.2.** -/
theorem gaussianWidth_diameter_bounds
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    (1 / Real.sqrt (2 * Real.pi) : ℝ) * finiteEuclideanDiameter T ≤
        gaussianWidth T ∧
      gaussianWidth T ≤
        Real.sqrt n / 2 * finiteEuclideanDiameter T :=
  ⟨gaussianWidth_lower_diameter T hT,
    gaussianWidth_le_sqrt_card_mul_diameter T hT⟩

/-! ### Linear images -/

/-- Image of a finite Euclidean set under a continuous linear map.

**Lean implementation helper.** -/
def continuousLinearImageFinset {d e : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin e))
    (T : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (EuclideanSpace ℝ (Fin e)) :=
  T.image A

/-- The image of a nonempty finite set under a continuous linear map is nonempty.

**Lean implementation helper.** -/
theorem continuousLinearImageFinset_nonempty {d e : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin e))
    {T : Finset (EuclideanSpace ℝ (Fin d))} (hT : T.Nonempty) :
    (continuousLinearImageFinset A T).Nonempty :=
  hT.image A

/-- The uncentered second moment of a canonical standard-Gaussian increment
is its squared Euclidean distance. This is the exact normalization required
when applying Sudakov--Fernique to Gaussian width.

**Lean implementation helper.** -/
theorem processIncrementSecondMoment_canonicalGaussianProcess
    {I : Type*} {d : ℕ}
    (a : I → EuclideanSpace ℝ (Fin d)) (i j : I) :
    processIncrementSecondMoment
        (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (canonicalGaussianProcess a) i j = ‖a i - a j‖ ^ 2 := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) :=
    (innerSL ℝ) (a i - a j)
  have hId : HasGaussianLaw
      (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.hasGaussianLaw_id
  have hmem : MemLp L 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa [Function.comp_def] using (hId.map L).memLp_two
  have hv := variance_eq_sub hmem
  rw [integral_strongDual_stdGaussian L, variance_dual_stdGaussian L,
    innerSL_apply_norm] at hv
  change ‖a i - a j‖ ^ 2 =
    (∫ g : EuclideanSpace ℝ (Fin d), (L g) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) - 0 ^ 2 at hv
  norm_num at hv
  unfold processIncrementSecondMoment
  calc
    (∫ g : EuclideanSpace ℝ (Fin d),
        (canonicalGaussianProcess a i g -
          canonicalGaussianProcess a j g) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ g : EuclideanSpace ℝ (Fin d), (L g) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp [canonicalGaussianProcess, L, innerSL_apply_apply]
    _ = ‖a i - a j‖ ^ 2 := hv.symm

/-- A continuous linear map
increases Gaussian width by at most its operator norm. The proof applies the
finite Sudakov--Fernique comparison to the canonical processes indexed by
`A '' T` and `‖A‖ • T`.

**Book Proposition 7.5.2(g).** -/
theorem gaussianWidth_continuousLinearImage {d e : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin e))
    (T : Finset (EuclideanSpace ℝ (Fin d))) (hT : T.Nonempty) :
    gaussianWidth (continuousLinearImageFinset A T) ≤
      ‖A‖ * gaussianWidth T := by
  classical
  let I := {x // x ∈ T}
  letI : Nonempty I := by
    obtain ⟨x, hx⟩ := hT
    exact ⟨⟨x, hx⟩⟩
  let aX : I → EuclideanSpace ℝ (Fin e) := fun i ↦ A i.1
  let aY : I → EuclideanSpace ℝ (Fin d) := fun i ↦ ‖A‖ • i.1
  let X := canonicalGaussianProcess aX
  let Y := canonicalGaussianProcess aY
  have hmaxX (g : EuclideanSpace ℝ (Fin e)) :
      HDP.Chapter5.finiteMaximum X g =
        finiteGaussianSupport (continuousLinearImageFinset A T) g := by
    unfold continuousLinearImageFinset
    rw [finiteGaussianSupport_eq_sup' _ (hT.image A), Finset.sup'_image]
    unfold HDP.Chapter5.finiteMaximum X canonicalGaussianProcess aX
    apply le_antisymm
    · apply (Finset.sup'_le_iff Finset.univ_nonempty
        (fun i : I ↦ inner ℝ (A i.1) g)).mpr
      intro i hi
      simpa [real_inner_comm] using
        (Finset.le_sup' (fun x ↦ inner ℝ g (A x)) i.property)
    · apply (Finset.sup'_le_iff hT
        (fun x ↦ inner ℝ g (A x))).mpr
      intro x hx
      let i : I := ⟨x, hx⟩
      simpa [i, real_inner_comm] using
        (Finset.le_sup' (fun i : I ↦ inner ℝ (A i.1) g)
          (Finset.mem_univ i))
  have hmaxY (g : EuclideanSpace ℝ (Fin d)) :
      HDP.Chapter5.finiteMaximum Y g =
        finiteGaussianSupport (scaleFinset ‖A‖ T) g := by
    unfold scaleFinset
    rw [finiteGaussianSupport_eq_sup' _ (hT.image _), Finset.sup'_image]
    unfold HDP.Chapter5.finiteMaximum Y canonicalGaussianProcess aY
    apply le_antisymm
    · apply (Finset.sup'_le_iff Finset.univ_nonempty
        (fun i : I ↦ inner ℝ (‖A‖ • i.1) g)).mpr
      intro i hi
      simpa [real_inner_comm] using
        (Finset.le_sup'
          (fun x ↦ inner ℝ g (‖A‖ • x)) i.property)
    · apply (Finset.sup'_le_iff hT
        (fun x ↦ inner ℝ g (‖A‖ • x))).mpr
      intro x hx
      let i : I := ⟨x, hx⟩
      simpa [i, real_inner_comm] using
        (Finset.le_sup'
          (fun i : I ↦ inner ℝ (‖A‖ • i.1) g)
          (Finset.mem_univ i))
  have hinc (i j : I) :
      processIncrementSecondMoment
          (stdGaussian (EuclideanSpace ℝ (Fin e))) X i j ≤
        processIncrementSecondMoment
          (stdGaussian (EuclideanSpace ℝ (Fin d))) Y i j := by
    rw [show X = canonicalGaussianProcess aX from rfl,
      show Y = canonicalGaussianProcess aY from rfl,
      processIncrementSecondMoment_canonicalGaussianProcess aX i j,
      processIncrementSecondMoment_canonicalGaussianProcess aY i j]
    have hop : ‖A (i.1 - j.1)‖ ≤ ‖A‖ * ‖i.1 - j.1‖ :=
      A.le_opNorm _
    have hsquare :=
      mul_self_le_mul_self (norm_nonneg (A (i.1 - j.1))) hop
    have hXnorm : ‖aX i - aX j‖ = ‖A (i.1 - j.1)‖ := by
      simp [aX, map_sub]
    have hYnorm : ‖aY i - aY j‖ = ‖A‖ * ‖i.1 - j.1‖ := by
      rw [show aY i - aY j = ‖A‖ • (i.1 - j.1) by
        simp [aY, smul_sub]]
      simp [norm_smul]
    rw [hXnorm, hYnorm]
    simpa [pow_two] using hsquare
  have hcomp := sudakovFernique
    (stdGaussian (EuclideanSpace ℝ (Fin e)))
    (stdGaussian (EuclideanSpace ℝ (Fin d))) X Y
    (canonicalGaussianProcess_isGaussian aX)
    (canonicalGaussianProcess_isGaussian aY)
    (canonicalGaussianProcess_centered aX)
    (canonicalGaussianProcess_centered aY) hinc
  unfold expectedFiniteSupremum at hcomp
  have himage :
      gaussianWidth (continuousLinearImageFinset A T) ≤
        gaussianWidth (scaleFinset ‖A‖ T) := by
    rw [show gaussianWidth (continuousLinearImageFinset A T) =
        ∫ g, HDP.Chapter5.finiteMaximum X g
          ∂stdGaussian (EuclideanSpace ℝ (Fin e)) by
        rw [gaussianWidth]
        exact integral_congr_ae (ae_of_all _ fun g ↦ (hmaxX g).symm)]
    rw [show gaussianWidth (scaleFinset ‖A‖ T) =
        ∫ g, HDP.Chapter5.finiteMaximum Y g
          ∂stdGaussian (EuclideanSpace ℝ (Fin d)) by
        rw [gaussianWidth]
        exact integral_congr_ae (ae_of_all _ fun g ↦ (hmaxY g).symm)]
    exact hcomp
  calc
    gaussianWidth (continuousLinearImageFinset A T) ≤
        gaussianWidth (scaleFinset ‖A‖ T) := himage
    _ = ‖A‖ * gaussianWidth T :=
      gaussianWidth_scale_of_nonneg T hT
        (ContinuousLinearMap.opNorm_nonneg A)

/-- Gaussian width is finite for bounded sets and obeys scaling, Minkowski, convex-hull, symmetry, diameter, and linear-image laws. Exercise 7.15(g), source-numbered core wrapper.

**Book Proposition 7.5.2.** -/
theorem exercise_7_15g_linearImage {d e : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin e))
    (T : Finset (EuclideanSpace ℝ (Fin d))) (hT : T.Nonempty) :
    gaussianWidth (continuousLinearImageFinset A T) ≤
      ‖A‖ * gaussianWidth T :=
  gaussianWidth_continuousLinearImage A T hT

/-- Prove all algebraic properties of Gaussian width. Exercise 7.15(a): finiteness is an actual integrability theorem.

**Book Exercise 7.15.** -/
theorem exercise_7_15a_finiteness
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Integrable (finiteGaussianSupport T)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
  integrable_finiteGaussianSupport T

/-- Prove all algebraic properties of Gaussian width. Exercise 7.15(b--d), bundled finite-safe statement.

**Book Exercise 7.15.** -/
theorem exercise_7_15bd
    (T S : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) (hS : S.Nonempty)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    gaussianWidth (translateFinset y (orthogonalImageFinset U T)) =
        gaussianWidth T ∧
      gaussianWidth (minkowskiSumFinset T S) =
        gaussianWidth T + gaussianWidth S ∧
      gaussianWidth (scaleFinset a T) = |a| * gaussianWidth T := by
  exact ⟨(gaussianWidth_translate _ (orthogonalImageFinset_nonempty U hT) _).trans
      (gaussianWidth_orthogonalImage U T hT),
    gaussianWidth_minkowskiSum T S hT hS,
    gaussianWidth_scale T hT a⟩

/-- Prove all algebraic properties of Gaussian width. Exercise 7.15(c), source-numbered core wrapper.

**Book Exercise 7.15.** -/
theorem exercise_7_15c_convexHull
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    convexHullGaussianWidth T = gaussianWidth T :=
  gaussianWidth_convexHull T hT

/-- Prove all algebraic properties of Gaussian width. Exercise 7.15(e), omitted from the exercise's printed list but used by
the source immediately afterwards.

**Book Exercise 7.15.** -/
theorem exercise_7_15e_symmetry
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianWidth T = (1 / 2 : ℝ) * gaussianWidth (differenceFinset T T) :=
  gaussianWidth_eq_half_difference T hT

end

end HDP.Chapter7

end Source_08_GaussianWidth

/-! ## Material formerly in `09_SphericalWidth.lean` -/

section Source_09_SphericalWidth

/-!
# Book Chapter 7, §7.5.1: spherical width

The sphere in dimension zero is empty, so source-facing statements carry
`0 < n`.  This is the missing positive-dimension hypothesis in the printed
definition and Lemma 7.5.5.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace Metric
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter7

noncomputable section

variable {n : ℕ}

/-- Spherical width is average support over a uniform unit-sphere direction. Finite form.

**Book Definition 7.5.4.** -/
def sphericalWidth (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    finiteGaussianSupport T θ
    ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))

/-- Radius of a Euclidean set.

**Book Equation (8.51).** -/
def finiteRadius (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if hT : T.Nonempty then T.sup' hT norm else 0

/-- Expresses finite radius as the supremum of norms over the finite set.

**Lean implementation helper.** -/
theorem finiteRadius_eq_sup'
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    finiteRadius T = T.sup' hT norm := by
  simp [finiteRadius, hT]

/-- Every member's norm is bounded by the finite radius.

**Lean implementation helper.** -/
theorem norm_le_finiteRadius
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) :
    ‖x‖ ≤ finiteRadius T := by
  rw [finiteRadius_eq_sup' T hT]
  exact Finset.le_sup' norm hx

/-- The finite radius is nonnegative.

**Lean implementation helper.** -/
theorem finiteRadius_nonneg (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ finiteRadius T := by
  classical
  by_cases hT : T.Nonempty
  · exact (norm_nonneg hT.choose).trans
      (norm_le_finiteRadius T hT hT.choose_spec)
  · simp [finiteRadius, hT]

/-- A point of the Euclidean unit sphere has norm one.

**Lean implementation helper.** -/
theorem norm_coe_unitSphere
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simpa only [mem_sphere_zero_iff_norm] using θ.property

/-- The absolute finite Gaussian support on the unit sphere is bounded by the Gaussian norm.

**Lean implementation helper.** -/
theorem abs_finiteGaussianSupport_unitSphere_le
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    |finiteGaussianSupport T θ| ≤ finiteRadius T := by
  classical
  by_cases hT : T.Nonempty
  · rw [finiteGaussianSupport_eq_sup' T hT]
    obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup' hT
      (fun y ↦ inner ℝ (θ : EuclideanSpace ℝ (Fin n)) y)
    rw [hmax]
    calc
      |inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x| ≤
          ‖(θ : EuclideanSpace ℝ (Fin n))‖ * ‖x‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖x‖ := by rw [norm_coe_unitSphere]; simp
      _ ≤ finiteRadius T := norm_le_finiteRadius T hT hx
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    simp [finiteRadius]

/-- Finite Gaussian support over a nonempty finite subset of the unit sphere is integrable.

**Lean implementation helper.** -/
theorem integrable_finiteGaussianSupport_unitSphere
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hn : 0 < n) :
    Integrable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
        finiteGaussianSupport T θ)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  apply Integrable.of_bound
    ((measurable_finiteGaussianSupport T).comp measurable_subtype_coe).aestronglyMeasurable
    (finiteRadius T)
  filter_upwards [] with θ
  simpa [Real.norm_eq_abs] using abs_finiteGaussianSupport_unitSphere_le T θ

/-- The spherical width is nonnegative.

**Lean implementation helper.** -/
theorem sphericalWidth_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hn : 0 < n) : 0 ≤ sphericalWidth T := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  obtain ⟨x, hx⟩ := hT
  have hinner : Integrable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
        inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
    apply Integrable.of_bound
      ((by fun_prop : Measurable (fun θ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
          inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x))).aestronglyMeasurable
      ‖x‖
    filter_upwards [] with θ
    simpa [Real.norm_eq_abs, norm_coe_unitSphere] using
      (abs_real_inner_le_norm
        (θ : EuclideanSpace ℝ (Fin n)) x)
  have hmean : (∫ θ : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1,
      inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) = 0 := by
    -- Rotation by `-1` preserves the uniform law and negates this linear functional.
    let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin n) := LinearIsometryEquiv.neg ℝ
    have hmap := HDP.map_unitSphereMeasure U
    have hi := integral_map
      (μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereHomeomorph U).measurable.aemeasurable
      ((by fun_prop : Measurable (fun θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
          inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x))).aestronglyMeasurable
    rw [hmap] at hi
    have hneg : (∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1,
        inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
        -(∫ θ : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1,
          inner ℝ (θ : EuclideanSpace ℝ (Fin n)) x
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
      calc
        _ = ∫ θ, inner ℝ
            (((HDP.unitSphereHomeomorph U) θ : Metric.sphere
              (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n)) x
            ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := hi
        _ = -_ := by
          rw [← integral_neg]
          apply integral_congr_ae
          filter_upwards [] with θ
          simp [HDP.unitSphereHomeomorph, U]
    linarith
  rw [sphericalWidth, ← hmean]
  exact integral_mono hinner
    (integrable_finiteGaussianSupport_unitSphere T hn)
    (fun θ ↦ inner_le_finiteGaussianSupport T ⟨x, hx⟩ hx θ)

/-- Mean length of a standard Gaussian vector.

**Lean implementation helper.** -/
def gaussianRadialMean (n : ℕ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin n), ‖g‖
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Moving a scalar from the Gaussian vector to the finite set leaves the support pairing unchanged.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_smul_left
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (z : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport T (a • z) = a * finiteGaussianSupport T z := by
  rw [finiteGaussianSupport_eq_sup' T hT,
    finiteGaussianSupport_eq_sup' T hT]
  simp_rw [inner_smul_left]
  exact (Finset.mul₀_sup' ha (fun x ↦ inner ℝ z x) T hT).symm

/-- Finite Gaussian support can be written using radial norm and direction.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_polar
    [Nonempty (Fin n)]
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport T g = ‖g‖ *
      finiteGaussianSupport T
        ((HDP.gaussianDirection g : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n)) := by
  by_cases hg : g = 0
  · subst g
    simp [finiteGaussianSupport_eq_sup' T hT]
  · have hrec : ‖g‖ •
        ((HDP.gaussianDirection g : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n)) = g := by
      rw [HDP.Chapter3.coe_gaussianDirection_eq_inv_norm_smul g hg,
        smul_smul]
      simp [hg]
    calc
      finiteGaussianSupport T g = finiteGaussianSupport T
          (‖g‖ • ((HDP.gaussianDirection g : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))) := congrArg _ hrec.symm
      _ = ‖g‖ * finiteGaussianSupport T
          ((HDP.gaussianDirection g : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n)) :=
        finiteGaussianSupport_smul_left T hT (norm_nonneg g) _

/-- Gaussian width equals mean Gaussian radius times spherical width, so the two differ by a `sqrt n` factor. Exact polar-factorization identity for finite sets.
The numerical `sqrt n` bounds are separated below from this measure-theoretic
identity.

**Book Lemma 7.5.5.** -/
theorem gaussianWidth_eq_radialMean_mul_sphericalWidth
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hn : 0 < n) :
    gaussianWidth T = gaussianRadialMean n * sphericalWidth T := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial E := inferInstance
  let φ : E → S × ℝ := fun g ↦ (HDP.gaussianDirection g, ‖g‖)
  let F : S × ℝ → ℝ := fun p ↦
    finiteGaussianSupport T (p.1 : E) * p.2
  have hφm : AEMeasurable φ (stdGaussian E) := by
    exact ((HDP.measurable_gaussianDirection (E := E)).prodMk
      measurable_norm).aemeasurable
  have hFm : AEStronglyMeasurable F (Measure.map φ (stdGaussian E)) := by
    have hFmeas : Measurable F := by
      dsimp [F]
      exact ((measurable_finiteGaussianSupport T).comp
        (measurable_subtype_coe.comp measurable_fst)).mul measurable_snd
    exact hFmeas.aestronglyMeasurable
  have hmapInt := integral_map hφm hFm
  have hjoint : Measure.map φ (stdGaussian E) =
      (HDP.unitSphereMeasure E).prod
        (Measure.map (fun g : E ↦ ‖g‖) (stdGaussian E)) := by
    dsimp [φ]
    rw [HDP.map_gaussianDirection_norm_stdGaussian,
      HDP.map_gaussianDirection_stdGaussian]
  rw [hjoint] at hmapInt
  have hprod := integral_prod_mul
    (μ := HDP.unitSphereMeasure E)
    (ν := Measure.map (fun g : E ↦ ‖g‖) (stdGaussian E))
    (fun θ : S ↦ finiteGaussianSupport T (θ : E))
    (fun r : ℝ ↦ r)
  have hradial : (∫ r : ℝ, r
      ∂Measure.map (fun g : E ↦ ‖g‖) (stdGaussian E)) =
      gaussianRadialMean n := by
    rw [integral_map measurable_norm.aemeasurable]
    · rfl
    · exact measurable_id.aestronglyMeasurable
  rw [sphericalWidth, gaussianWidth]
  calc
    (∫ g : E, finiteGaussianSupport T g ∂stdGaussian E) =
        ∫ g : E, F (φ g) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with g
      dsimp [F, φ]
      rw [finiteGaussianSupport_polar T hT g]
      ring
    _ = ∫ p : S × ℝ, F p
          ∂(HDP.unitSphereMeasure E).prod
            (Measure.map (fun g : E ↦ ‖g‖) (stdGaussian E)) := hmapInt.symm
    _ = (∫ θ : S, finiteGaussianSupport T (θ : E)
          ∂HDP.unitSphereMeasure E) *
        (∫ r : ℝ, r
          ∂Measure.map (fun g : E ↦ ‖g‖) (stdGaussian E)) := by
      simpa [F] using hprod
    _ = (∫ g : E, ‖g‖ ∂stdGaussian E) *
        ∫ θ : S, finiteGaussianSupport T (θ : E)
          ∂HDP.unitSphereMeasure E := by
      rw [hradial, gaussianRadialMean]
      ring

/-- Gaussian width equals mean Gaussian radius times spherical width, so the two differ by a `sqrt n` factor. The explicit absolute constant
`16` follows by applying the fully proved fourth-moment Exercise 3.2 to the
canonical product realization of a standard Gaussian vector.

**Book Lemma 7.5.5.** -/
theorem gaussianRadialMean_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 0 < n →
      Real.sqrt n - C / Real.sqrt n ≤ gaussianRadialMean n ∧
      gaussianRadialMean n ≤ Real.sqrt n := by
  refine ⟨16, by norm_num, ?_⟩
  intro n hn
  let μn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let X : Fin n → (Fin n → ℝ) → ℝ := fun i x => x i
  letI : IsProbabilityMeasure μn := by
    dsimp [μn]
    infer_instance
  have hXm : ∀ i, AEMeasurable (X i) μn := fun _ => (by fun_prop)
  have hindep : iIndepFun X μn := by
    dsimp [X, μn]
    simpa only [id_eq] using
      (iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hm2 : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num))
    simpa using h.symm
  have hm4 : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
    have h := HDP.Chapter2.gaussian_absolute_moment_measure
      (p := (4 : ℝ)) (by norm_num)
    have hfun : (fun x : ℝ => |x| ^ (4 : ℝ)) = fun x => x ^ 4 := by
      funext x
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
      rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]
      ring
    rw [hfun] at h
    rw [show ((4 : ℝ) + 1) / 2 = (3 / 2 : ℝ) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num),
      show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq] at h
    have hs : Real.sqrt Real.pi ≠ 0 := by positivity
    rw [show (2 : ℝ) ^ ((4 : ℝ) / 2) = 4 by norm_num] at h
    field_simp at h
    linarith
  have hsecond : ∀ i, ∫ x, X i x ^ 2 ∂μn = 1 := by
    intro i
    simpa [X, μn] using
      (MeasureTheory.integral_comp_eval
        (μ := fun _ : Fin n => gaussianReal 0 1)
        (i := i) (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans hm2
  have hfourthInt : ∀ i, Integrable (fun x => X i x ^ 4) μn := by
    intro i
    have hbase : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
      have hmem := memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num)
      have hi := hmem.integrable_norm_pow' (p := 4)
      simpa [Real.norm_eq_abs, show ∀ x : ℝ, |x| ^ 4 = x ^ 4 by
        intro x
        rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]
        ring] using hi
    exact MeasurePreserving.integrable_comp_of_integrable
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i) hbase
  have hfourth : ∀ i, ∫ x, X i x ^ 4 ∂μn ≤ (2 : ℝ) ^ 4 := by
    intro i
    have hi := MeasureTheory.integral_comp_eval
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (i := i) (f := fun x : ℝ => x ^ 4) (by fun_prop)
    dsimp [X, μn]
    rw [hi, hm4]
    norm_num
  have hmain := HDP.Chapter3.exercise_3_2 hn hXm hindep hsecond
    (K := (2 : ℝ)) (by norm_num) hfourthInt hfourth
  have hradius : (∫ x, HDP.Chapter3.euclideanRadius X x ∂μn) =
      gaussianRadialMean n := by
    let e : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
      MeasurableEquiv.toLp 2 (Fin n → ℝ)
    have he : MeasurePreserving e μn
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
      refine ⟨e.measurable, ?_⟩
      change Measure.map (WithLp.toLp 2) μn =
        stdGaussian (EuclideanSpace ℝ (Fin n))
      simpa [μn] using (map_pi_eq_stdGaussian (ι := Fin n))
    have hi := he.integral_comp' (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖)
    rw [gaussianRadialMean]
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [X, HDP.Chapter3.euclideanRadius, e]
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hradius] at hmain
  norm_num at hmain
  exact ⟨by linarith [hmain.2.1], hmain.2.2⟩

end

end HDP.Chapter7

end Source_09_SphericalWidth

/-! ## Material formerly in `10_WidthExamples.lean` -/

section Source_10_WidthExamples

/-!
# Book Chapter 7, §7.5.2: examples of Gaussian width

The support functions of the Euclidean ball, cube, and cross-polytope are,
respectively, `‖g‖₂`, `‖g‖₁`, and `‖g‖∞`.  We expose these exact support
integrals directly, avoiding an unsafe real `sSup` over an arbitrary set.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace Filter
open scoped BigOperators RealInnerProductSpace Topology

namespace HDP.Chapter7

noncomputable section

variable {n : ℕ}

/-- Every coordinate of the canonical standard Gaussian vector has the
standard one-dimensional Gaussian law.

**Lean implementation helper.** -/
theorem hasLaw_stdGaussian_coordinate (i : Fin n) :
    HasLaw (fun g : EuclideanSpace ℝ (Fin n) ↦ g i)
      (gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have hu : ‖u‖ = 1 := by simp [u]
  have hmap := (IsGaussian.map_eq_gaussianReal ((innerSL ℝ) u) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map ((innerSL ℝ) u) =
      gaussianReal
        ((stdGaussian (EuclideanSpace ℝ (Fin n)))[(innerSL ℝ) u])
        Var[(innerSL ℝ) u;
          stdGaussian (EuclideanSpace ℝ (Fin n))].toNNReal)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hu] at hmap
  have hfun : (fun g : EuclideanSpace ℝ (Fin n) ↦ g i) = (innerSL ℝ) u := by
    funext g
    simp [u, innerSL_apply_apply, PiLp.inner_apply]
  refine ⟨(by fun_prop), ?_⟩
  rw [hfun]
  simpa using hmap

/-- The Euclidean unit ball and sphere have Gaussian width comparable to `sqrt n`. Support-integral realization of `w(B₂ⁿ)`.

**Book Example 7.5.6.** -/
def euclideanBallGaussianWidth (n : ℕ) : ℝ := gaussianRadialMean n

/-- Support-integral realization of `w(B∞ⁿ)`.

**Lean implementation helper.** -/
def cubeGaussianWidth (n : ℕ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin n), ∑ i, |g i|
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Support-integral realization of `w(B₁ⁿ)`, totalized by zero when
there is no coordinate.

**Lean implementation helper.** -/
def crossPolytopeGaussianWidth (n : ℕ) : ℝ :=
  if hn : 0 < n then
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    ∫ g : EuclideanSpace ℝ (Fin n),
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |g i|)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))
  else 0

/-- Evaluates the expected absolute value of one standard Gaussian coordinate.

**Lean implementation helper.** -/
private theorem integral_abs_stdGaussian_coordinate (i : Fin n) :
    (∫ g : EuclideanSpace ℝ (Fin n), |g i|
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
  have h := HDP.Chapter2.gaussian_absolute_moment
    (hasLaw_stdGaussian_coordinate i) (p := (1 : ℝ)) le_rfl
  have hs : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [← Real.sqrt_eq_rpow]
  rw [hs] at h
  simpa [Real.rpow_one, Real.Gamma_one] using h

/-- Exact cube width.

**Book Example 7.5.7.** -/
theorem cubeGaussianWidth_eq (n : ℕ) :
    cubeGaussianWidth n = (n : ℝ) *
      (Real.sqrt 2 / Real.sqrt Real.pi) := by
  rw [cubeGaussianWidth, integral_finsetSum]
  · simp_rw [integral_abs_stdGaussian_coordinate]
    simp
  · intro i hi
    exact (HDP.Chapter2.integrable_of_hasLaw_standardGaussian
      (hasLaw_stdGaussian_coordinate i)).abs

/-- The cube has Gaussian width exactly `sqrt(2/pi) n`. The source's `sqrt (2 / pi)` presentation of Example 7.5.7.

**Book Example 7.5.7.** -/
theorem cubeGaussianWidth_eq_source (n : ℕ) :
    cubeGaussianWidth n = Real.sqrt (2 / Real.pi) * n := by
  rw [cubeGaussianWidth_eq]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsqrt : Real.sqrt (2 / Real.pi) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity)]
  rw [hsqrt]
  ring

/-- The cross-polytope has Gaussian width of order `sqrt(log n)`. The sharp finite upper bound for the
cross-polytope width (written in dimension `k+2`, matching the promoted
Exercise 2.38 API).

**Book Example 7.5.8.** -/
theorem crossPolytopeGaussianWidth_upper (k : ℕ) :
    crossPolytopeGaussianWidth (k + 2) ≤
      Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) := by
  rw [crossPolytopeGaussianWidth, dif_pos (by omega)]
  simpa using HDP.Chapter2.exercise_2_38a_max_abs
    (n := k)
    (g := fun i (x : EuclideanSpace ℝ (Fin (k + 2))) ↦ x i)
    (fun _ ↦ by fun_prop)
    (fun i ↦ hasLaw_stdGaussian_coordinate i)

/-- A common-space version of the cross-polytope widths used to state the
asymptotic conclusion without pretending that `Fin n` has a fixed ambient
probability space as `n` varies.

**Lean implementation helper.** -/
def iidCrossPolytopeWidth {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (g : ℕ → Omega → ℝ) (k : ℕ) : ℝ :=
  ∫ omega, HDP.Chapter2.gaussianMaxAbsSeq g k omega ∂mu

/-- The cross-polytope has Gaussian width of order `sqrt(log n)`. Asymptotic sharpness, inherited from the fully
proved load-bearing Exercise 2.38(b).

**Book Example 7.5.8.** -/
theorem crossPolytopeGaussianWidth_asymptotic
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (g : ℕ → Omega → ℝ)
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) mu)
    (hi : iIndepFun g mu) :
    Tendsto (fun k ↦ iidCrossPolytopeWidth mu g k /
      HDP.Chapter2.gaussianMaxScale k) atTop (𝓝 1) := by
  simpa [iidCrossPolytopeWidth] using
    HDP.Chapter2.exercise_2_38b_max_abs hgm hg hi

/-- A single canonical probability space carrying an infinite independent
standard-Gaussian sequence.

**Lean implementation helper.** -/
private noncomputable def canonicalGaussianSequenceMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- The coordinate process on the canonical Gaussian product space.

**Lean implementation helper.** -/
private def canonicalGaussianSequence (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

/-- Every coordinate of the canonical Gaussian sequence is measurable.

**Lean implementation helper.** -/
private lemma canonicalGaussianSequence_measurable (i : ℕ) :
    Measurable (canonicalGaussianSequence i) := measurable_pi_apply i

/-- Every coordinate of the canonical Gaussian sequence has standard-normal
law.

**Lean implementation helper.** -/
private lemma canonicalGaussianSequence_hasLaw (i : ℕ) :
    HasLaw (canonicalGaussianSequence i) (gaussianReal 0 1)
      canonicalGaussianSequenceMeasure :=
  (measurePreserving_eval_infinitePi
    (fun _ : ℕ => gaussianReal 0 1) i).hasLaw

/-- The coordinates of the canonical Gaussian sequence are independent.

**Lean implementation helper.** -/
private lemma canonicalGaussianSequence_iIndep :
    iIndepFun canonicalGaussianSequence canonicalGaussianSequenceMeasure := by
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ : ℕ => id) (fun _ => measurable_id)

/-- The canonical finite-dimensional cross-polytope width is the expected
absolute maximum of the corresponding initial segment of one infinite
independent Gaussian sequence.

**Lean implementation helper.** -/
private theorem crossPolytopeGaussianWidth_eq_sequence (k : ℕ) :
    crossPolytopeGaussianWidth (k + 2) =
      iidCrossPolytopeWidth canonicalGaussianSequenceMeasure
        canonicalGaussianSequence k := by
  let μG := canonicalGaussianSequenceMeasure
  let g := canonicalGaussianSequence
  let X : (ℕ → ℝ) → EuclideanSpace ℝ (Fin (k + 2)) :=
    fun ω => WithLp.toLp 2 (fun i => g i ω)
  have hiFin : iIndepFun (fun i : Fin (k + 2) => g i) μG :=
    canonicalGaussianSequence_iIndep.precomp Fin.val_injective
  have hpi : HasLaw
      (fun (ω : ℕ → ℝ) (i : Fin (k + 2)) => g i ω)
      (Measure.pi (fun _ : Fin (k + 2) => gaussianReal 0 1)) μG :=
    hiFin.hasLaw_pi (fun i => canonicalGaussianSequence_hasLaw i)
  have hX : HasLaw X (stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))) μG := by
    refine ⟨(WithLp.measurable_toLp 2 (Fin (k + 2) → ℝ)).aemeasurable
      |>.comp_aemeasurable hpi.aemeasurable, ?_⟩
    have hto : AEMeasurable (WithLp.toLp 2)
        (Measure.map
          (fun (ω : ℕ → ℝ) (i : Fin (k + 2)) => g i ω) μG) := by
      rw [hpi.map_eq]
      exact (WithLp.measurable_toLp 2 (Fin (k + 2) → ℝ)).aemeasurable
    rw [show X = (WithLp.toLp 2) ∘
        (fun (ω : ℕ → ℝ) (i : Fin (k + 2)) => g i ω) from rfl,
      ← hto.map_map_of_aemeasurable hpi.aemeasurable, hpi.map_eq,
      map_pi_eq_stdGaussian]
  let F : EuclideanSpace ℝ (Fin (k + 2)) → ℝ := fun x =>
    Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)
  have hFm : Measurable F := by
    dsimp [F]
    fun_prop
  rw [crossPolytopeGaussianWidth, dif_pos (by omega),
    iidCrossPolytopeWidth]
  simpa [F, X, g, canonicalGaussianSequence,
    HDP.Chapter2.gaussianMaxAbsSeq_eq_finSup, Function.comp_def] using
      (hX.integral_comp hFm.aestronglyMeasurable).symm

/-- The expected absolute value of the first canonical standard-Gaussian
coordinate.

**Lean implementation helper.** -/
private lemma integral_abs_canonicalGaussianSequence_zero :
    (∫ ω, |canonicalGaussianSequence 0 ω|
        ∂canonicalGaussianSequenceMeasure) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
  calc
    (∫ ω, |canonicalGaussianSequence 0 ω|
        ∂canonicalGaussianSequenceMeasure) =
        ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
          simpa [Function.comp_def] using
            (canonicalGaussianSequence_hasLaw 0).integral_comp
              continuous_abs.aestronglyMeasurable
    _ = Real.sqrt 2 / Real.sqrt Real.pi := by
      have h := HDP.Chapter2.gaussian_absolute_moment_measure
        (p := (1 : ℝ)) le_rfl
      have hpow : (2 : ℝ) ^ (2 : ℝ)⁻¹ = Real.sqrt 2 := by
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
      simpa [Real.rpow_one, Real.Gamma_one, hpow] using h

/-- Every nontrivial cross-polytope width is bounded below by the expected
absolute value of one standard Gaussian coordinate.

**Lean implementation helper.** -/
private theorem crossPolytopeGaussianWidth_lower_constant (k : ℕ) :
    Real.sqrt 2 / Real.sqrt Real.pi ≤
      crossPolytopeGaussianWidth (k + 2) := by
  rw [crossPolytopeGaussianWidth_eq_sequence, iidCrossPolytopeWidth,
    ← integral_abs_canonicalGaussianSequence_zero]
  apply integral_mono
  · have hm : Integrable abs
        (Measure.map (canonicalGaussianSequence 0)
          canonicalGaussianSequenceMeasure) := by
          rw [(canonicalGaussianSequence_hasLaw 0).map_eq]
          exact ((memLp_id_gaussianReal'
            (μ := 0) (v := 1) 1 (by norm_num)).integrable
              (by norm_num)).abs
    simpa [Function.comp_def] using
      (integrable_map_measure continuous_abs.aestronglyMeasurable
        (canonicalGaussianSequence_hasLaw 0).aemeasurable).mp hm
  · exact HDP.Chapter2.gaussianMaxAbsSeq_integrable
      canonicalGaussianSequence_measurable canonicalGaussianSequence_hasLaw k
  · intro ω
    rw [HDP.Chapter2.gaussianMaxAbsSeq_eq_finSup]
    exact Finset.le_sup' (fun i : Fin (k + 2) =>
      |canonicalGaussianSequence i ω|) (Finset.mem_univ 0)

/-- The actual canonical cross-polytope widths have the sharp Gaussian-maximum
asymptotic.

**Book Equation (7.19).** -/
theorem crossPolytopeGaussianWidth_asymptotic_actual :
    Tendsto (fun k ↦ crossPolytopeGaussianWidth (k + 2) /
      HDP.Chapter2.gaussianMaxScale k) atTop (𝓝 1) := by
  simpa [crossPolytopeGaussianWidth_eq_sequence] using
    crossPolytopeGaussianWidth_asymptotic
      (mu := canonicalGaussianSequenceMeasure) canonicalGaussianSequence
      canonicalGaussianSequence_measurable canonicalGaussianSequence_hasLaw
      canonicalGaussianSequence_iIndep

/-- The normalizing scale for Gaussian maxima is monotone.

**Lean implementation helper.** -/
private lemma gaussianMaxScale_mono {k K : ℕ} (hkK : k ≤ K) :
    HDP.Chapter2.gaussianMaxScale k ≤
      HDP.Chapter2.gaussianMaxScale K := by
  unfold HDP.Chapter2.gaussianMaxScale
  gcongr

/-- Direct finite two-sided comparison for the actual canonical
cross-polytope widths.

**Book Example 7.5.8; Equation (7.19).** -/
theorem crossPolytopeGaussianWidth_twoSided :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : ℕ,
      c * HDP.Chapter2.gaussianMaxScale k ≤
          crossPolytopeGaussianWidth (k + 2) ∧
        crossPolytopeGaussianWidth (k + 2) ≤
          C * HDP.Chapter2.gaussianMaxScale k := by
  have hevent :
      ∀ᶠ k : ℕ in atTop,
        (1 / 2 : ℝ) <
          crossPolytopeGaussianWidth (k + 2) /
            HDP.Chapter2.gaussianMaxScale k :=
    crossPolytopeGaussianWidth_asymptotic_actual.eventually
      (Ioi_mem_nhds (by norm_num))
  rw [eventually_atTop] at hevent
  obtain ⟨K, hK⟩ := hevent
  let a : ℝ := Real.sqrt 2 / Real.sqrt Real.pi
  let c : ℝ := min (1 / 2) (a / HDP.Chapter2.gaussianMaxScale K)
  refine ⟨c, Real.sqrt 2, ?_, Real.sqrt_pos.2 (by norm_num), ?_⟩
  · have ha : 0 < a := by
      dsimp [a]
      positivity
    exact lt_min (by norm_num)
      (div_pos ha (HDP.Chapter2.gaussianMaxScale_pos K))
  · intro k
    constructor
    · by_cases hk : K ≤ k
      · have hratio := hK k hk
        rw [lt_div_iff₀ (HDP.Chapter2.gaussianMaxScale_pos k)] at hratio
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
          (HDP.Chapter2.gaussianMaxScale_pos k).le).trans hratio.le
      · have hscale := gaussianMaxScale_mono (Nat.le_of_lt (lt_of_not_ge hk))
        have hc : c ≤ a / HDP.Chapter2.gaussianMaxScale K :=
          min_le_right _ _
        calc
          c * HDP.Chapter2.gaussianMaxScale k ≤
              (a / HDP.Chapter2.gaussianMaxScale K) *
                HDP.Chapter2.gaussianMaxScale k := by
                  exact mul_le_mul_of_nonneg_right hc
                    (HDP.Chapter2.gaussianMaxScale_pos k).le
          _ ≤ (a / HDP.Chapter2.gaussianMaxScale K) *
                HDP.Chapter2.gaussianMaxScale K := by
                  exact mul_le_mul_of_nonneg_left hscale
                    (div_nonneg (by dsimp [a]; positivity)
                      (HDP.Chapter2.gaussianMaxScale_pos K).le)
          _ = a := by
            field_simp [ne_of_gt (HDP.Chapter2.gaussianMaxScale_pos K)]
          _ ≤ crossPolytopeGaussianWidth (k + 2) :=
            crossPolytopeGaussianWidth_lower_constant k
    · have hu := crossPolytopeGaussianWidth_upper k
      have hn : (2 : ℝ) ≤ k + 2 := by
        exact_mod_cast (by omega : 2 ≤ k + 2)
      have hlog : Real.log 2 ≤ Real.log (k + 2 : ℝ) :=
        Real.log_le_log (by norm_num) hn
      have harg :
          2 * Real.log (2 * (k + 2 : ℝ)) ≤
            4 * Real.log (k + 2 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        nlinarith
      calc
        crossPolytopeGaussianWidth (k + 2) ≤
            Real.sqrt (2 * Real.log (2 * (k + 2 : ℝ))) := hu
        _ ≤ Real.sqrt (4 * Real.log (k + 2 : ℝ)) :=
          Real.sqrt_le_sqrt harg
        _ = Real.sqrt 2 * HDP.Chapter2.gaussianMaxScale k := by
          rw [HDP.Chapter2.gaussianMaxScale,
            ← Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
          congr 1
          ring

/-- Width of a finite family, retaining its supplied indexing.

**Lean implementation helper.** -/
def gaussianFamilyWidth {I : Type*} [Fintype I] [Nonempty I]
    (x : I → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ g, Finset.univ.sup' Finset.univ_nonempty
      (fun i ↦ inner ℝ g (x i))
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- A finite point set has Gaussian width at most a universal constant times diameter times `sqrt(log cardinality)`. Unit-sphere finite-family form. Translation and
scaling are supplied by module 08.

**Book Example 7.5.9.** -/
theorem gaussianFamilyWidth_unit_upper (k : ℕ)
    (x : Fin (k + 2) → EuclideanSpace ℝ (Fin n))
    (hx : ∀ i, ‖x i‖ = 1) :
    gaussianFamilyWidth x ≤ Real.sqrt (2 * Real.log (k + 2 : ℝ)) := by
  apply HDP.Chapter2.exercise_2_38a_max
    (g := fun i g ↦ inner ℝ g (x i))
  · intro i
    fun_prop
  · intro i
    have hmap := (IsGaussian.map_eq_gaussianReal ((innerSL ℝ) (x i)) :
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map ((innerSL ℝ) (x i)) =
        gaussianReal
          ((stdGaussian (EuclideanSpace ℝ (Fin n)))[(innerSL ℝ) (x i)])
          Var[(innerSL ℝ) (x i);
            stdGaussian (EuclideanSpace ℝ (Fin n))].toNNReal)
    rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
      innerSL_apply_norm, hx i] at hmap
    refine ⟨(by fun_prop), ?_⟩
    simpa [innerSL_apply_apply, real_inner_comm] using hmap

/-- The symmetric two-point set used in Exercise 7.16.

**Book Exercise 7.16.** -/
def symmetricPairFinset (x : EuclideanSpace ℝ (Fin n)) :
    Finset (EuclideanSpace ℝ (Fin n)) := {x, -x}

/-- Computes Gaussian support of a symmetric two-point set as an absolute inner product.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_symmetricPair
    (x g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport (symmetricPairFinset x) g = |inner ℝ g x| := by
  rw [finiteGaussianSupport_eq_sup' _ (by simp [symmetricPairFinset])]
  simp [symmetricPairFinset, abs_eq_max_neg]

/-- The width/diameter constants are optimal, witnessed by a symmetric pair and Euclidean balls. Exercise 7.16, lower-diameter extreme: a unit symmetric interval has
width `E |N(0,1)|`.

**Book Remark 7.5.3.** -/
theorem exercise_7_16_symmetricPair
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    gaussianWidth (symmetricPairFinset x) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
  rw [gaussianWidth]
  simp_rw [finiteGaussianSupport_symmetricPair]
  have hmap := (IsGaussian.map_eq_gaussianReal ((innerSL ℝ) x) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map ((innerSL ℝ) x) =
      gaussianReal
        ((stdGaussian (EuclideanSpace ℝ (Fin n)))[(innerSL ℝ) x])
        Var[(innerSL ℝ) x;
          stdGaussian (EuclideanSpace ℝ (Fin n))].toNNReal)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hx] at hmap
  have hlaw : HasLaw (fun g : EuclideanSpace ℝ (Fin n) ↦ inner ℝ g x)
      (gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    refine ⟨(by fun_prop), ?_⟩
    simpa [innerSL_apply_apply, real_inner_comm] using hmap
  have h := HDP.Chapter2.gaussian_absolute_moment hlaw (p := (1 : ℝ)) le_rfl
  have hs : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [← Real.sqrt_eq_rpow]
  rw [hs] at h
  simpa [Real.rpow_one, Real.Gamma_one] using h

/-- The dual-norm support integral representing the Gaussian width of an
`ℓᵖ` unit ball when `p'` is the conjugate exponent.

**Lean implementation helper.** -/
def lpBallGaussianWidthProxy (p' : ℝ) (n : ℕ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin n),
    HDP.Chapter1.lpNorm p' (fun i ↦ g i)
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Width of `ell_p` balls. Corrected to `n ≥ 2`, so `log n > 0` and the
two printed regimes are meaningful. The explicit constants below are
`gaussianLpLowerConstant` and `12`; they come from the fully proved promoted
Exercises 3.5--3.6.

**Book Exercise 7.17.** -/
theorem exercise_7_17_lpBall_width :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {n : ℕ} {p' : ℝ}, 2 ≤ n → 1 ≤ p' →
        (p' ≤ Real.log n →
          c * Real.sqrt p' * Real.rpow n (1 / p') ≤
              lpBallGaussianWidthProxy p' n ∧
          lpBallGaussianWidthProxy p' n ≤
              C * Real.sqrt p' * Real.rpow n (1 / p')) ∧
        (Real.log n ≤ p' →
          c * Real.sqrt (Real.log n) ≤ lpBallGaussianWidthProxy p' n ∧
          lpBallGaussianWidthProxy p' n ≤
            C * Real.sqrt (Real.log n)) := by
  refine ⟨HDP.Chapter3.gaussianLpLowerConstant, 12,
    HDP.Chapter3.gaussianLpLowerConstant_pos, by norm_num, ?_⟩
  intro n p' hn hp
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hkn : n = k + 2 := by omega
  subst n
  simp only [Nat.add_comm 2 k] at hn ⊢
  let μN : Measure (Fin (k + 2) → ℝ) :=
    Measure.pi (fun _ : Fin (k + 2) => gaussianReal 0 1)
  let X : Fin (k + 2) → (Fin (k + 2) → ℝ) → ℝ := fun i x => x i
  letI : IsProbabilityMeasure μN := by
    dsimp [μN]
    infer_instance
  have hXm : ∀ i, Measurable (X i) := fun _ => (by fun_prop)
  have hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) μN := by
    intro i
    exact (measurePreserving_eval
      (fun _ : Fin (k + 2) => gaussianReal 0 1) i).hasLaw
  have hindep : iIndepFun X μN := by
    dsimp [X, μN]
    simpa only [id_eq] using
      (iIndepFun_pi (X := fun _ : Fin (k + 2) => id)
        (fun _ => aemeasurable_id))
  have hsub : ∀ i, HDP.SubGaussian (X i) μN := by
    intro i
    refine ⟨2, by norm_num, ?_⟩
    rw [HDP.psi2MGF_eq_of_hasLaw_standardGaussian (hlaw i)]
    unfold HDP.psi2MGF
    calc
      (∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / (2 : ℝ) ^ 2))
          ∂gaussianReal 0 1) ≤
          ∫⁻ x, ENNReal.ofReal (Real.exp ((3 / 8 : ℝ) * x ^ 2))
            ∂gaussianReal 0 1 := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg x]
      _ = 2 := HDP.Chapter2.lintegral_exp_three_eighths_sq_standardGaussian
  have hpsi : ∀ i, HDP.psi2Norm (X i) μN ≤ 2 := by
    intro i
    rw [HDP.psi2Norm_standardGaussian (hlaw i)]
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3)
    have hsqrt0 := Real.sqrt_nonneg (8 / 3 : ℝ)
    nlinarith
  have hint : (∫ x, HDP.Chapter1.lpNorm p' (fun i => X i x) ∂μN) =
      lpBallGaussianWidthProxy p' (k + 2) := by
    let e : (Fin (k + 2) → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (k + 2)) :=
      MeasurableEquiv.toLp 2 (Fin (k + 2) → ℝ)
    have he : HasLaw e (stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))) μN := by
      refine ⟨e.measurable.aemeasurable, ?_⟩
      change Measure.map (WithLp.toLp 2) μN =
        stdGaussian (EuclideanSpace ℝ (Fin (k + 2)))
      simpa [μN] using (map_pi_eq_stdGaussian (ι := Fin (k + 2)))
    have hi := he.integral_comp
      (f := fun g : EuclideanSpace ℝ (Fin (k + 2)) =>
        HDP.Chapter1.lpNorm p' (fun i => g i)) (by
          apply Measurable.aestronglyMeasurable
          simp_rw [HDP.Chapter1.lpNorm_eq_sum (lt_of_lt_of_le one_pos hp)]
          fun_prop)
    rw [lpBallGaussianWidthProxy]
    simpa [X, e, Function.comp_def] using hi
  have hu := HDP.Chapter3.exercise_3_5 (n := k) hXm hsub
    (K := (2 : ℝ)) (p := p') (by norm_num) hpsi hp
  have hl := HDP.Chapter3.exercise_3_6 (n := k) hXm hlaw hindep (p := p') hp
  rw [hint] at hu hl
  constructor
  · intro hplog
    have hplog' : p' ≤ Real.log ((k : ℝ) + 2) := by
      simpa [Nat.cast_add] using hplog
    have hlower := hl.1 hplog'
    have hupper := hu.1 hplog'
    constructor
    · simpa [Nat.cast_add] using hlower
    · have hfac :
          2 * Real.sqrt p' * (((k : ℝ) + 2) ^ (1 / p')) ≤
            12 * Real.sqrt p' * (((k : ℝ) + 2) ^ (1 / p')) := by
          have hs0 : 0 ≤ Real.sqrt p' := Real.sqrt_nonneg _
          have hpw0 : 0 ≤ ((k : ℝ) + 2) ^ (1 / p') :=
            Real.rpow_nonneg (by positivity) _
          nlinarith
      exact hupper.trans (by simpa [Nat.cast_add] using hfac)
  · intro hlogp
    have hlogp' : Real.log ((k : ℝ) + 2) ≤ p' := by
      simpa [Nat.cast_add] using hlogp
    have hlower := hl.2.1 hlogp'
    have hupper := hu.2.1 hlogp'
    constructor
    · simpa [Nat.cast_add] using hlower
    · calc
        lpBallGaussianWidthProxy p' (k + 2) ≤
            6 * 2 * Real.sqrt (Real.log ((k : ℝ) + 2)) := hupper
        _ = 12 * Real.sqrt (Real.log ((k : ℝ) + 2)) := by ring
        _ = 12 * Real.sqrt (Real.log (k + 2 : ℕ)) := by
          simp [Nat.cast_add]

end

end HDP.Chapter7

end Source_10_WidthExamples

/-! ## Material formerly in `11_NuclearNorm.lean` -/

section Source_11_NuclearNorm

/-!
# Book Chapter 7, Exercise 7.18: the nuclear norm

The source introduces this load-bearing matrix norm in an exercise and uses
its duality again in Chapter 9.  It therefore belongs to the core chain.
-/

open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace HDP.Chapter7

noncomputable section

/-- The nuclear norm of a square real matrix: the `ℓ¹` norm of its singular
values. Mathlib's singular values are zero-indexed.

**Lean implementation helper.** -/
def matrixNuclearNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, HDP.matrixSingularValue A i

/-- The matrix nuclear norm is nonnegative.

**Lean implementation helper.** -/
theorem matrixNuclearNorm_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ matrixNuclearNorm A := by
  exact Finset.sum_nonneg fun i _ => HDP.matrixSingularValue_nonneg A i

/-- The nuclear norm of the zero matrix is zero.

**Lean implementation helper.** -/
@[simp] theorem matrixNuclearNorm_zero_matrix {n : ℕ} :
    matrixNuclearNorm (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  simp [matrixNuclearNorm, HDP.matrixSingularValue]

/-- The real Frobenius inner product is symmetric.

**Lean implementation helper.** -/
private lemma matrixFrobeniusInner_comm {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner A B = HDP.matrixFrobeniusInner B A := by
  simp only [HDP.matrixFrobeniusInner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Frobenius inner product is additive in its left argument.

**Lean implementation helper.** -/
private lemma matrixFrobeniusInner_add_left {m n : ℕ}
    (A B C : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner (A + B) C =
      HDP.matrixFrobeniusInner A C + HDP.matrixFrobeniusInner B C := by
  simp only [HDP.matrixFrobeniusInner, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]

/-- The Frobenius inner product is homogeneous in its left argument.

**Lean implementation helper.** -/
private lemma matrixFrobeniusInner_smul_left {m n : ℕ}
    (c : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner (c • A) B =
      c * HDP.matrixFrobeniusInner A B := by
  simp only [HDP.matrixFrobeniusInner, Matrix.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc, ← Finset.mul_sum]

/-- Negating the right argument negates the Frobenius inner product.

**Lean implementation helper.** -/
private lemma matrixFrobeniusInner_neg_right {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner A (-B) = -HDP.matrixFrobeniusInner A B := by
  simp [HDP.matrixFrobeniusInner, ← Finset.sum_neg_distrib]

/-- A finite sum in the left argument passes through the Frobenius inner product.

**Lean implementation helper.** -/
private lemma matrixFrobeniusInner_sum_left {n : ℕ}
    {ι : Type*} [Fintype ι]
    (F : ι → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner (∑ i, F i) B =
      ∑ i, HDP.matrixFrobeniusInner (F i) B := by
  simp only [HDP.matrixFrobeniusInner, Matrix.sum_apply, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ x, F x i j * B i j) =
        ∑ i, ∑ x, ∑ j, F x i j * B i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ i, ∑ j, F x i j * B i j := by
      rw [Finset.sum_comm]

/-- The Frobenius pairing with an outer product equals the associated bilinear form.

**Lean implementation helper.** -/
private lemma matrixFrobeniusInner_outer_left {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) :
    HDP.matrixFrobeniusInner (HDP.Chapter4.outerMatrix u v) B =
      inner ℝ u (B.toEuclideanLin v) := by
  rw [matrixFrobeniusInner_comm]
  rw [HDP.Chapter4.outerMatrix,
    HDP.Chapter4.matrixInner_vecMulVec_eq_bilinear]
  simp only [HDP.Chapter4.matrixBilinear, PiLp.inner_apply,
    Matrix.toLpLin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mulVec, dotProduct, Real.inner_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nuclear/operator duality and the nuclear norm laws. The nuclear and Euclidean operator norms are dual. The existential clause is
the attainment content of the printed `max` and avoids an unsafe real `sSup`. The proof uses the real SVD from Chapter 4. The sum of the corresponding
rank-one partial isometries is contractive by Bessel's inequality and attains
the Frobenius pairing term by term.

**Book Exercise 7.18.** -/
theorem exercise_7_18a_nuclear_operator_duality {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ B : Matrix (Fin n) (Fin n) ℝ,
        HDP.matrixOpNorm B ≤ 1 →
          HDP.matrixFrobeniusInner A B ≤ matrixNuclearNorm A) ∧
      ∃ B : Matrix (Fin n) (Fin n) ℝ,
        HDP.matrixOpNorm B ≤ 1 ∧
          HDP.matrixFrobeniusInner A B = matrixNuclearNorm A := by
  classical
  obtain ⟨u, hu, hA⟩ :=
    HDP.Chapter4.exists_tall_svd A (le_refl n)
  let v : Fin n → EuclideanSpace ℝ (Fin n) :=
    HDP.Chapter4.rightSingularBasis A
  have hv : Orthonormal ℝ v :=
    HDP.Chapter4.rightSingularBasis_orthonormal A
  let B₀ : Matrix (Fin n) (Fin n) ℝ :=
    ∑ i : Fin n, HDP.Chapter4.outerMatrix (u i) (v i)
  have hB₀apply (x : EuclideanSpace ℝ (Fin n)) :
      B₀.toEuclideanLin x =
        ∑ i : Fin n, inner ℝ (v i) x • u i := by
    simp [B₀, HDP.Chapter4.toEuclideanLin_outerMatrix]
  have hB₀norm (x : EuclideanSpace ℝ (Fin n)) :
      ‖B₀.toEuclideanLin x‖ ≤ ‖x‖ := by
    have hsq : ‖B₀.toEuclideanLin x‖ ^ 2 =
        ∑ i : Fin n, (inner ℝ (v i) x) ^ 2 := by
      rw [hB₀apply, ← real_inner_self_eq_norm_sq]
      have h := hu.inner_sum
        (fun i : Fin n => inner ℝ (v i) x)
        (fun i : Fin n => inner ℝ (v i) x) Finset.univ
      simpa [pow_two] using h
    have hbessel := hv.sum_inner_products_le x (s := Finset.univ)
    have hbessel' : (∑ i : Fin n, (inner ℝ (v i) x) ^ 2) ≤
        ‖x‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using hbessel
    apply le_of_sq_le_sq
    · simpa [hsq] using hbessel'
    · exact norm_nonneg x
  have hB₀op : HDP.matrixOpNorm B₀ ≤ 1 := by
    rw [HDP.matrixOpNorm, Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro x
    simpa using hB₀norm x
  have hB₀basis (i : Fin n) : B₀.toEuclideanLin (v i) = u i := by
    rw [hB₀apply]
    rw [Finset.sum_eq_single i]
    · rw [inner_self_eq_norm_sq_to_K, hv.norm_eq_one]
      norm_num
    · intro j hj hji
      rw [hv.2 hji]
      simp
    · simp
  constructor
  · intro B hBop
    calc
      HDP.matrixFrobeniusInner A B =
          HDP.matrixFrobeniusInner
            (∑ i : Fin n, HDP.matrixSingularValue A i •
              HDP.Chapter4.outerMatrix (u i) (v i)) B := by
        exact congrArg (fun M => HDP.matrixFrobeniusInner M B) hA
      _ = ∑ i : Fin n, HDP.matrixFrobeniusInner
          (HDP.matrixSingularValue A i •
            HDP.Chapter4.outerMatrix (u i) (v i)) B :=
        matrixFrobeniusInner_sum_left _ _
      _ ≤ ∑ i : Fin n, HDP.matrixSingularValue A i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [matrixFrobeniusInner_smul_left,
          matrixFrobeniusInner_outer_left]
        have hs0 := HDP.matrixSingularValue_nonneg A i
        apply (mul_le_mul_of_nonneg_left (real_inner_le_norm (u i)
          (B.toEuclideanLin (v i))) hs0).trans
        rw [hu.norm_eq_one, one_mul]
        calc
          HDP.matrixSingularValue A i * ‖B.toEuclideanLin (v i)‖ ≤
              HDP.matrixSingularValue A i *
                (HDP.matrixOpNorm B * ‖v i‖) := by
            gcongr
            exact HDP.Chapter4.matrixOpNorm_apply_le B (v i)
          _ = HDP.matrixSingularValue A i * HDP.matrixOpNorm B := by
            rw [hv.norm_eq_one, mul_one]
          _ ≤ HDP.matrixSingularValue A i := by
            simpa using mul_le_mul_of_nonneg_left hBop hs0
      _ = matrixNuclearNorm A := rfl
  · refine ⟨B₀, hB₀op, ?_⟩
    calc
      HDP.matrixFrobeniusInner A B₀ =
          HDP.matrixFrobeniusInner
            (∑ i : Fin n, HDP.matrixSingularValue A i •
              HDP.Chapter4.outerMatrix (u i) (v i)) B₀ := by
        exact congrArg (fun M => HDP.matrixFrobeniusInner M B₀) hA
      _ = ∑ i : Fin n, HDP.matrixFrobeniusInner
          (HDP.matrixSingularValue A i •
            HDP.Chapter4.outerMatrix (u i) (v i)) B₀ :=
        matrixFrobeniusInner_sum_left _ _
      _ = ∑ i : Fin n, HDP.matrixSingularValue A i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixFrobeniusInner_smul_left,
          matrixFrobeniusInner_outer_left, hB₀basis,
          real_inner_self_eq_norm_sq, hu.norm_eq_one]
        norm_num
      _ = matrixNuclearNorm A := rfl

/-- Bounds the absolute Frobenius pairing by nuclear norm times operator norm.

**Lean implementation helper.** -/
theorem abs_matrixFrobeniusInner_le_nuclear_mul_opNorm {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    |HDP.matrixFrobeniusInner A B| ≤
      matrixNuclearNorm A * HDP.matrixOpNorm B := by
  by_cases hB : HDP.matrixOpNorm B = 0
  · have hB0 : B = 0 :=
      (HDP.Chapter4.matrixOpNorm_eq_zero_iff B).mp hB
    subst B
    simp [HDP.matrixFrobeniusInner]
  · have hBpos : 0 < HDP.matrixOpNorm B :=
      lt_of_le_of_ne (HDP.matrixOpNorm_nonneg B) (Ne.symm hB)
    let C : Matrix (Fin n) (Fin n) ℝ :=
      (HDP.matrixOpNorm B)⁻¹ • B
    have hCop : HDP.matrixOpNorm C ≤ 1 := by
      change HDP.matrixOpNorm ((HDP.matrixOpNorm B)⁻¹ • B) ≤ 1
      rw [HDP.matrixOpNorm_smul, abs_inv, abs_of_pos hBpos]
      field_simp [hBpos.ne']
      norm_num
    have hupper := (exercise_7_18a_nuclear_operator_duality A).1 C hCop
    have hnegOp : HDP.matrixOpNorm (-C) ≤ 1 := by simpa using hCop
    have hlower := (exercise_7_18a_nuclear_operator_duality A).1 (-C) hnegOp
    rw [matrixFrobeniusInner_neg_right] at hlower
    have hCpair : HDP.matrixFrobeniusInner A C =
        (HDP.matrixOpNorm B)⁻¹ * HDP.matrixFrobeniusInner A B := by
      rw [matrixFrobeniusInner_comm, matrixFrobeniusInner_smul_left,
        matrixFrobeniusInner_comm]
    rw [hCpair] at hupper hlower
    have hu := mul_le_mul_of_nonneg_left hupper hBpos.le
    have hl := mul_le_mul_of_nonneg_left hlower hBpos.le
    field_simp [hBpos.ne'] at hu hl
    rw [abs_le]
    constructor <;> nlinarith

/-- The nuclear norm satisfies the triangle inequality.

**Lean implementation helper.** -/
theorem matrixNuclearNorm_add_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixNuclearNorm (A + B) ≤ matrixNuclearNorm A + matrixNuclearNorm B := by
  obtain ⟨C, hCop, hC⟩ :=
    (exercise_7_18a_nuclear_operator_duality (A + B)).2
  rw [← hC, matrixFrobeniusInner_add_left]
  exact add_le_add
    ((exercise_7_18a_nuclear_operator_duality A).1 C hCop)
    ((exercise_7_18a_nuclear_operator_duality B).1 C hCop)

/-- The nuclear norm of a scalar multiple is the scalar absolute value times the nuclear norm.

**Lean implementation helper.** -/
theorem matrixNuclearNorm_smul {n : ℕ}
    (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixNuclearNorm (c • A) = |c| * matrixNuclearNorm A := by
  by_cases hc : c = 0
  · subst c
    simp
  have habs : 0 < |c| := abs_pos.mpr hc
  apply le_antisymm
  · obtain ⟨B, hBop, hB⟩ :=
      (exercise_7_18a_nuclear_operator_duality (c • A)).2
    rw [← hB, matrixFrobeniusInner_smul_left]
    calc
      c * HDP.matrixFrobeniusInner A B ≤
          |c| * |HDP.matrixFrobeniusInner A B| :=
        (le_abs_self (c * HDP.matrixFrobeniusInner A B)).trans_eq
          (abs_mul c _)
      _ ≤ |c| * matrixNuclearNorm A := by
        gcongr
        calc
          |HDP.matrixFrobeniusInner A B| ≤
              matrixNuclearNorm A * HDP.matrixOpNorm B :=
            abs_matrixFrobeniusInner_le_nuclear_mul_opNorm A B
          _ ≤ matrixNuclearNorm A * 1 :=
            mul_le_mul_of_nonneg_left hBop (matrixNuclearNorm_nonneg A)
          _ = matrixNuclearNorm A := mul_one _
  · obtain ⟨B, hBop, hB⟩ :=
      (exercise_7_18a_nuclear_operator_duality A).2
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · have hnegOp : HDP.matrixOpNorm (-B) ≤ 1 := by simpa using hBop
      have hbound :=
        (exercise_7_18a_nuclear_operator_duality (c • A)).1 (-B) hnegOp
      rw [matrixFrobeniusInner_neg_right,
        matrixFrobeniusInner_smul_left, hB] at hbound
      rw [abs_of_neg hcneg]
      nlinarith
    · have hbound :=
        (exercise_7_18a_nuclear_operator_duality (c • A)).1 B hBop
      rw [matrixFrobeniusInner_smul_left, hB] at hbound
      rw [abs_of_pos hcpos]
      exact hbound

/-- A matrix has zero nuclear norm exactly when it is the zero matrix.

**Lean implementation helper.** -/
theorem matrixNuclearNorm_eq_zero_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixNuclearNorm A = 0 ↔ A = 0 := by
  constructor
  · intro hA
    have hinner := abs_matrixFrobeniusInner_le_nuclear_mul_opNorm A A
    rw [hA, zero_mul] at hinner
    have hpair0 : HDP.matrixFrobeniusInner A A = 0 := abs_eq_zero.mp
      (le_antisymm hinner (abs_nonneg _))
    rw [HDP.matrixInner_self] at hpair0
    have hfrob0 : HDP.matrixFrobeniusNorm A = 0 := sq_eq_zero_iff.mp hpair0
    have hentries : A = 0 := by
      ext i j
      have hs := HDP.matrixFrobeniusNorm_sq A
      rw [hfrob0, zero_pow (by norm_num)] at hs
      have hentry : A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      have hrow : (∑ j', A i j' ^ 2) ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)
      have hterm : A i j ^ 2 ≤ 0 := by
        calc
          A i j ^ 2 ≤ ∑ j', A i j' ^ 2 := hentry
          _ ≤ ∑ i', ∑ j', A i' j' ^ 2 := hrow
          _ = 0 := hs.symm
      change A i j = 0
      nlinarith [sq_nonneg (A i j)]
    exact hentries
  · rintro rfl
    exact matrixNuclearNorm_zero_matrix

/-- Nuclear/operator duality and the nuclear norm laws. The three substantive
norm axioms for the nuclear norm.

**Book Exercise 7.18.** -/
theorem exercise_7_18b_nuclear_norm {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    matrixNuclearNorm (A + B) ≤ matrixNuclearNorm A + matrixNuclearNorm B ∧
      matrixNuclearNorm (c • A) = |c| * matrixNuclearNorm A ∧
      (matrixNuclearNorm A = 0 ↔ A = 0) :=
  ⟨matrixNuclearNorm_add_le A B, matrixNuclearNorm_smul c A,
    matrixNuclearNorm_eq_zero_iff A⟩

end

end HDP.Chapter7

end Source_11_NuclearNorm

/-! ## Material formerly in `12_GaussianComplexity.lean` -/

section Source_12_GaussianComplexity

/-!
# Book Chapter 7, §7.5.3: Gaussian complexity

As for Gaussian width, the real-valued API is intentionally finite.  This
makes the maxima measurable and the expectations finite without hiding a
measurability hypothesis on an arbitrary set.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace ENNReal NNReal

namespace HDP.Chapter7

noncomputable section

variable {n : ℕ}

/-- Pointwise absolute support of a finite set, totalized by zero on the
empty set.

**Lean implementation helper.** -/
def finiteGaussianAbsSupport
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if hT : T.Nonempty then
    T.sup' hT (fun x => |inner ℝ g x|)
  else 0

/-- Expresses finite absolute Gaussian support as a supremum over the finite index set.

**Lean implementation helper.** -/
theorem finiteGaussianAbsSupport_eq_sup'
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianAbsSupport T g =
      T.sup' hT (fun x => |inner ℝ g x|) := by
  simp [finiteGaussianAbsSupport, hT]

/-- Finite absolute Gaussian support of the empty set is zero.

**Lean implementation helper.** -/
@[simp] theorem finiteGaussianAbsSupport_empty
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianAbsSupport ∅ g = 0 := by
  simp [finiteGaussianAbsSupport]

/-- The finite Gaussian absolute support is nonnegative.

**Lean implementation helper.** -/
theorem finiteGaussianAbsSupport_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) :
    0 ≤ finiteGaussianAbsSupport T g := by
  classical
  by_cases hT : T.Nonempty
  · rw [finiteGaussianAbsSupport_eq_sup' T hT]
    obtain ⟨x, hx⟩ := hT
    exact (abs_nonneg (inner ℝ g x)).trans
      (Finset.le_sup' (fun y => |inner ℝ g y|) hx)
  · simp [finiteGaussianAbsSupport, hT]

/-- The finite Gaussian absolute support is measurable.

**Lean implementation helper.** -/
theorem measurable_finiteGaussianAbsSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Measurable (finiteGaussianAbsSupport T) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show finiteGaussianAbsSupport T =
        T.sup' hT (fun x => fun g => |inner ℝ g x|) by
      funext g
      simp [finiteGaussianAbsSupport, hT]]
    apply Finset.measurable_sup' hT
    intro x _
    fun_prop
  · rw [show finiteGaussianAbsSupport T = 0 by
      funext g
      simp [finiteGaussianAbsSupport, hT]]
    fun_prop

/-- Every inner product with a standard Gaussian vector belongs to L².

**Lean implementation helper.** -/
private theorem memLp_two_inner_stdGaussian
    (x : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun g : EuclideanSpace ℝ (Fin n) => inner ℝ g x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).continuousLinearMap_comp
      ((innerSL ℝ) x)
  simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm] using h

/-- Finite absolute Gaussian support belongs to L² under the standard Gaussian measure.

**Lean implementation helper.** -/
theorem memLp_two_finiteGaussianAbsSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    MemLp (finiteGaussianAbsSupport T) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show finiteGaussianAbsSupport T =
        T.sup' hT (fun x => fun g => |inner ℝ g x|) by
      funext g
      simp [finiteGaussianAbsSupport, hT]]
    refine Finset.sup'_induction hT
      (f := fun x => fun g : EuclideanSpace ℝ (Fin n) => |inner ℝ g x|)
      (p := fun f => MemLp f 2
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ?_ ?_
    · intro f hf g hg
      exact hf.sup hg
    · intro x hx
      simpa only [Real.norm_eq_abs] using
        (memLp_two_inner_stdGaussian x).norm
  · rw [show finiteGaussianAbsSupport T = 0 by
      funext g
      simp [finiteGaussianAbsSupport, hT]]
    exact MemLp.zero

/-- Finite absolute Gaussian support is integrable under the standard Gaussian measure.

**Lean implementation helper.** -/
theorem integrable_finiteGaussianAbsSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Integrable (finiteGaussianAbsSupport T)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
  (memLp_two_finiteGaussianAbsSupport T).integrable (by norm_num)

/-- Finite Gaussian complexity.

**Book Definition 7.5.9.** -/
def gaussianComplexity (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ g, finiteGaussianAbsSupport T g
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- The source's squared-average width `h(T)`.

**Lean implementation helper.** -/
def gaussianL2Width (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Real.sqrt (∫ g, (finiteGaussianAbsSupport T g) ^ 2
    ∂stdGaussian (EuclideanSpace ℝ (Fin n)))

/-- The Gaussian complexity is nonnegative.

**Lean implementation helper.** -/
theorem gaussianComplexity_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ gaussianComplexity T := by
  exact integral_nonneg fun g => finiteGaussianAbsSupport_nonneg T g

/-- The Gaussian L² width is nonnegative.

**Lean implementation helper.** -/
theorem gaussianL2Width_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ gaussianL2Width T := Real.sqrt_nonneg _

/-- Finite Gaussian support is bounded by finite absolute Gaussian support.

**Lean implementation helper.** -/
theorem finiteGaussianSupport_le_absSupport
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianSupport T g ≤ finiteGaussianAbsSupport T g := by
  classical
  by_cases hT : T.Nonempty
  · rw [finiteGaussianSupport_eq_sup' T hT,
      finiteGaussianAbsSupport_eq_sup' T hT]
    apply Finset.sup'_le
    intro x hx
    exact (le_abs_self (inner ℝ g x)).trans
      (Finset.le_sup' (fun y => |inner ℝ g y|) hx)
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    simp

/-- The first elementary comparison in §7.5.3.

**Book Section 7.5.3.** -/
theorem gaussianWidth_le_gaussianComplexity
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    gaussianWidth T ≤ gaussianComplexity T := by
  exact integral_mono (integrable_finiteGaussianSupport T)
    (integrable_finiteGaussianAbsSupport T)
    (finiteGaussianSupport_le_absSupport T)

/-- The second elementary comparison in §7.5.3.

**Book Section 7.5.3.** -/
theorem gaussianComplexity_le_gaussianL2Width
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    gaussianComplexity T ≤ gaussianL2Width T := by
  let f := finiteGaussianAbsSupport T
  have hf2 := memLp_two_finiteGaussianAbsSupport T
  have hf2' : MemLp f (ENNReal.ofReal (2 : ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [f] using hf2
  have hmono := HDP.Chapter1.exercise_1_11a
    (X := f) (p := (1 : ℝ)) (q := (2 : ℝ))
    (by norm_num) (by norm_num) hf2'
  have hf0 : ∀ g, 0 ≤ f g := finiteGaussianAbsSupport_nonneg T
  have habs : (∫ g, |f g|
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ g, f g ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply integral_congr_ae
    filter_upwards [] with g
    exact abs_of_nonneg (hf0 g)
  rw [HDP.Chapter1.lpNormRV, HDP.Chapter1.lpNormRV] at hmono
  norm_num at hmono
  rw [habs] at hmono
  rw [← Real.sqrt_eq_rpow] at hmono
  rw [gaussianComplexity, gaussianL2Width]
  simpa [f] using hmono

/-! ### Quantitative comparison infrastructure -/

/-- The largest Euclidean norm of a finite set, totalized by zero.

**Lean implementation helper.** -/
private def finiteGaussianRadius
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if hT : T.Nonempty then T.sup' hT norm else 0

/-- The finite Gaussian radius is nonnegative.

**Lean implementation helper.** -/
private theorem finiteGaussianRadius_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ finiteGaussianRadius T := by
  classical
  by_cases hT : T.Nonempty
  · rw [finiteGaussianRadius, dif_pos hT]
    obtain ⟨x, hx⟩ := hT
    exact (norm_nonneg x).trans (Finset.le_sup' norm hx)
  · simp [finiteGaussianRadius, hT]

/-- Every point's norm is bounded by the finite Gaussian radius.

**Lean implementation helper.** -/
private theorem norm_le_finiteGaussianRadius
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) :
    ‖x‖ ≤ finiteGaussianRadius T := by
  rw [finiteGaussianRadius, dif_pos hT]
  exact Finset.le_sup' norm hx

/-- The absolute inner-product process is Lipschitz with constant equal to the finite Gaussian radius.

**Lean implementation helper.** -/
private theorem lipschitzWith_abs_inner_finiteGaussianRadius
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) :
    LipschitzWith ⟨finiteGaussianRadius T, finiteGaussianRadius_nonneg T⟩
      (fun g : EuclideanSpace ℝ (Fin n) => |inner ℝ g x|) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro g h
  rw [Real.dist_eq]
  calc
    |(|inner ℝ g x| - |inner ℝ h x|)| ≤
        |inner ℝ g x - inner ℝ h x| := abs_abs_sub_abs_le _ _
    _ = |inner ℝ (g - h) x| := by rw [inner_sub_left]
    _ ≤ ‖g - h‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using
        (@norm_inner_le_norm ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ (g - h) x)
    _ ≤ finiteGaussianRadius T * ‖g - h‖ := by
      rw [mul_comm]
      gcongr
      exact norm_le_finiteGaussianRadius T hT hx
    _ = finiteGaussianRadius T * dist g h := by rw [dist_eq_norm]

/-- Finite absolute Gaussian support is Lipschitz with constant equal to the finite Gaussian radius.

**Lean implementation helper.** -/
private theorem lipschitzWith_finiteGaussianAbsSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    LipschitzWith ⟨finiteGaussianRadius T, finiteGaussianRadius_nonneg T⟩
      (finiteGaussianAbsSupport T) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show finiteGaussianAbsSupport T =
        T.sup' hT (fun x => fun g : EuclideanSpace ℝ (Fin n) =>
          |inner ℝ g x|) by
      funext g
      simp [finiteGaussianAbsSupport, hT]]
    refine Finset.sup'_induction hT
      (f := fun x => fun g : EuclideanSpace ℝ (Fin n) => |inner ℝ g x|)
      (p := fun f => LipschitzWith
        ⟨finiteGaussianRadius T, finiteGaussianRadius_nonneg T⟩ f)
      ?_ ?_
    · intro f hf g hg
      rw [show (f ⊔ g) = fun x => max (f x) (g x) from rfl]
      simpa only [max_self] using hf.max hg
    · intro x hx
      exact lipschitzWith_abs_inner_finiteGaussianRadius T hT hx
  · have hzero : finiteGaussianAbsSupport T = 0 := by
      funext g
      simp [finiteGaussianAbsSupport, hT]
    rw [hzero]
    exact (LipschitzWith.const _).weaken (finiteGaussianRadius_nonneg T)

/-- The negative of each point belongs to the difference set when zero belongs to the original set.

**Lean implementation helper.** -/
private theorem neg_mem_differenceFinset
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ differenceFinset T T) : -z ∈ differenceFinset T T := by
  classical
  unfold differenceFinset minkowskiSumFinset negFinset at hz ⊢
  rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hpT, hpneg⟩
  rcases Finset.mem_image.mp hpneg with ⟨q, hqT, hq⟩
  apply Finset.mem_image.mpr
  refine ⟨(q, -p.1), Finset.mem_product.mpr ⟨hqT, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨p.1, hpT, rfl⟩
  · rw [← hq]
    simp

/-- Absolute Gaussian support of a difference set equals ordinary support of that difference set.

**Lean implementation helper.** -/
private theorem finiteGaussianAbsSupport_difference_eq_support
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianAbsSupport (differenceFinset T T) g =
      finiteGaussianSupport (differenceFinset T T) g := by
  classical
  let D := differenceFinset T T
  have hD : D.Nonempty := differenceFinset_nonempty hT hT
  apply le_antisymm
  · rw [finiteGaussianAbsSupport_eq_sup' D hD,
      finiteGaussianSupport_eq_sup' D hD]
    apply Finset.sup'_le
    intro z hz
    rw [abs_le]
    constructor
    · have hnz : -z ∈ D := neg_mem_differenceFinset T hz
      have hle := Finset.le_sup' (fun x => inner ℝ g x) hnz
      have : -inner ℝ g z ≤ D.sup' hD (fun x => inner ℝ g x) := by
        simpa using hle
      linarith
    · exact Finset.le_sup' (fun x => inner ℝ g x) hz
  · exact finiteGaussianSupport_le_absSupport D g

/-- The expected absolute Gaussian inner product is the universal Gaussian absolute-value constant times the vector norm.

**Lean implementation helper.** -/
private theorem integral_abs_inner_stdGaussian
    (y : EuclideanSpace ℝ (Fin n)) :
    (∫ g : EuclideanSpace ℝ (Fin n), |inner ℝ g y|
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (Real.sqrt 2 / Real.sqrt Real.pi) * ‖y‖ := by
  have h := gaussianWidth_diameterSymmetricPair_eq y
  rw [gaussianWidth] at h
  simpa only [finiteGaussianSupport_diameterSymmetricPair] using h

/-- The universal Gaussian absolute-value constant is at least one half.

**Lean implementation helper.** -/
private theorem half_le_gaussian_abs_constant :
    (1 / 2 : ℝ) ≤ Real.sqrt 2 / Real.sqrt Real.pi := by
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [le_div_iff₀ hspi]
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspisq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hpi : Real.pi < 4 := Real.pi_lt_four
  nlinarith

/-- The universal Gaussian absolute-value constant is at most one.

**Lean implementation helper.** -/
private theorem gaussian_abs_constant_le_one :
    Real.sqrt 2 / Real.sqrt Real.pi ≤ 1 := by
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [div_le_one hspi]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])

/-- Gaussian complexity of a two-point set controls half the distance between its points.

**Lean implementation helper.** -/
private theorem half_norm_le_gaussianComplexity
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ T) :
    (1 / 2 : ℝ) * ‖y‖ ≤ gaussianComplexity T := by
  have hpoint (g : EuclideanSpace ℝ (Fin n)) :
      |inner ℝ g y| ≤ finiteGaussianAbsSupport T g := by
    rw [finiteGaussianAbsSupport_eq_sup' T hT]
    exact Finset.le_sup' (fun x => |inner ℝ g x|) hy
  have hint := integral_mono
    (integrable_inner_stdGaussian y).abs
    (integrable_finiteGaussianAbsSupport T) hpoint
  rw [integral_abs_inner_stdGaussian, ← gaussianComplexity] at hint
  exact (mul_le_mul_of_nonneg_right half_le_gaussian_abs_constant
    (norm_nonneg y)).trans hint

/-- If zero belongs to the finite set, its radius is at most twice its Gaussian complexity.

**Lean implementation helper.** -/
private theorem finiteGaussianRadius_le_two_complexity
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    finiteGaussianRadius T ≤ 2 * gaussianComplexity T := by
  rw [finiteGaussianRadius, dif_pos hT]
  apply (Finset.sup'_le_iff hT norm).mpr
  intro y hy
  have h := half_norm_le_gaussianComplexity T hT hy
  linarith

/-- Translating a set by the negative of one of its points makes the translated set contain zero.

**Lean implementation helper.** -/
private theorem zero_mem_translate_neg
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ T) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ translateFinset (-y) T := by
  classical
  unfold translateFinset
  exact Finset.mem_image.mpr ⟨y, hy, by simp⟩

/-- Absolute Gaussian support is bounded by support at a vector plus support at its negation.

**Lean implementation helper.** -/
private theorem finiteGaussianAbsSupport_le_support_add_negSupport
    (S : Finset (EuclideanSpace ℝ (Fin n))) (hS : S.Nonempty)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ S)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianAbsSupport S g ≤
      finiteGaussianSupport S g + finiteGaussianSupport (negFinset S) g := by
  classical
  rw [finiteGaussianAbsSupport_eq_sup' S hS]
  apply Finset.sup'_le
  intro x hx
  have hpos : 0 ≤ finiteGaussianSupport S g := by
    calc
      0 = inner ℝ g (0 : EuclideanSpace ℝ (Fin n)) := by simp
      _ ≤ finiteGaussianSupport S g :=
        inner_le_finiteGaussianSupport S hS h0 g
  have hnegpos : 0 ≤ finiteGaussianSupport (negFinset S) g := by
    have hn0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ negFinset S := by
      unfold negFinset
      exact Finset.mem_image.mpr ⟨0, h0, by simp⟩
    calc
      0 = inner ℝ g (0 : EuclideanSpace ℝ (Fin n)) := by simp
      _ ≤ finiteGaussianSupport (negFinset S) g :=
        inner_le_finiteGaussianSupport (negFinset S)
          (negFinset_nonempty hS) hn0 g
  rw [abs_le]
  constructor
  · have hnx : -x ∈ negFinset S := by
      unfold negFinset
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hle := inner_le_finiteGaussianSupport (negFinset S)
      (negFinset_nonempty hS) hnx g
    have hneg : -inner ℝ g x ≤ finiteGaussianSupport (negFinset S) g := by
      simpa using hle
    have hupper := hneg.trans (le_add_of_nonneg_left hpos)
    linarith
  · exact (inner_le_finiteGaussianSupport S hS hx g).trans
      (le_add_of_nonneg_right hnegpos)

/-- For a finite set containing zero, Gaussian complexity is at most twice Gaussian width.

**Lean implementation helper.** -/
private theorem gaussianComplexity_le_two_width_of_zero_mem
    (S : Finset (EuclideanSpace ℝ (Fin n))) (hS : S.Nonempty)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ S) :
    gaussianComplexity S ≤ 2 * gaussianWidth S := by
  have hrhs : Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
      finiteGaussianSupport S g + finiteGaussianSupport (negFinset S) g)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (integrable_finiteGaussianSupport S).add
      (integrable_finiteGaussianSupport (negFinset S))
  have hi := integral_mono (integrable_finiteGaussianAbsSupport S) hrhs
    (fun g => finiteGaussianAbsSupport_le_support_add_negSupport S hS h0 g)
  rw [← gaussianComplexity, integral_add,
    ← gaussianWidth, ← gaussianWidth, gaussianWidth_neg S hS] at hi
  · linarith
  · exact integrable_finiteGaussianSupport S
  · exact integrable_finiteGaussianSupport (negFinset S)

/-- Translation changes finite absolute Gaussian support by at most the absolute Gaussian pairing with the translation vector.

**Lean implementation helper.** -/
private theorem finiteGaussianAbsSupport_translate_bound
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {y : EuclideanSpace ℝ (Fin n)} (_hy : y ∈ T)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianAbsSupport T g ≤
      finiteGaussianAbsSupport (translateFinset (-y) T) g + |inner ℝ g y| := by
  classical
  let S := translateFinset (-y) T
  have hS : S.Nonempty := translateFinset_nonempty (-y) hT
  rw [finiteGaussianAbsSupport_eq_sup' T hT]
  apply Finset.sup'_le
  intro x hx
  have hxy : x + -y ∈ S := by
    unfold S translateFinset
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hle : |inner ℝ g (x + -y)| ≤ finiteGaussianAbsSupport S g := by
    rw [finiteGaussianAbsSupport_eq_sup' S hS]
    exact Finset.le_sup' (fun z => |inner ℝ g z|) hxy
  calc
    |inner ℝ g x| = |inner ℝ g (x + -y) + inner ℝ g y| := by
      congr 2
      rw [inner_add_right, inner_neg_right]
      ring
    _ ≤ |inner ℝ g (x + -y)| + |inner ℝ g y| := abs_add_le _ _
    _ ≤ finiteGaussianAbsSupport S g + |inner ℝ g y| := by gcongr

/-- Gaussian complexity of a translate is bounded by the original complexity plus the translation norm.

**Lean implementation helper.** -/
private theorem gaussianComplexity_translation_upper
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ T) :
    gaussianComplexity T ≤ 2 * gaussianWidth T + ‖y‖ := by
  let S := translateFinset (-y) T
  have hS : S.Nonempty := translateFinset_nonempty (-y) hT
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ S := zero_mem_translate_neg T hy
  have hrhs : Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
      finiteGaussianAbsSupport S g + |inner ℝ g y|)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (integrable_finiteGaussianAbsSupport S).add
      (integrable_inner_stdGaussian y).abs
  have hi := integral_mono (integrable_finiteGaussianAbsSupport T) hrhs
    (finiteGaussianAbsSupport_translate_bound T hT hy)
  rw [integral_add (integrable_finiteGaussianAbsSupport S)
      (integrable_inner_stdGaussian y).abs,
    ← gaussianComplexity, integral_abs_inner_stdGaussian] at hi
  change gaussianComplexity T ≤ gaussianComplexity S +
    (Real.sqrt 2 / Real.sqrt Real.pi) * ‖y‖ at hi
  have hSc := gaussianComplexity_le_two_width_of_zero_mem S hS h0
  have hSw : gaussianWidth S = gaussianWidth T :=
    gaussianWidth_translate T hT (-y)
  rw [hSw] at hSc
  have hcoef := mul_le_mul_of_nonneg_right gaussian_abs_constant_le_one
    (norm_nonneg y)
  linarith

/-- Gaussian complexity of a difference set is exactly twice the Gaussian width.

**Lean implementation helper.** -/
private theorem gaussianComplexity_difference_exact
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianComplexity (differenceFinset T T) = 2 * gaussianWidth T := by
  calc
    gaussianComplexity (differenceFinset T T) =
        gaussianWidth (differenceFinset T T) := by
      unfold gaussianComplexity gaussianWidth
      exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
        finiteGaussianAbsSupport_difference_eq_support T hT g)
    _ = gaussianWidth T + gaussianWidth T :=
      gaussianWidth_difference T T hT hT
    _ = 2 * gaussianWidth T := by ring

/-- The canonical coordinate map from the product Gaussian space has the standard Euclidean Gaussian law.

**Lean implementation helper.** -/
private theorem hasLaw_gaussianPi_to_stdGaussian (n : ℕ) :
    HasLaw (WithLp.toLp 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (HDP.Chapter5.gaussianPiMeasure n) := by
  refine ⟨(WithLp.measurable_toLp 2 (Fin n → ℝ)).aemeasurable, ?_⟩
  exact map_pi_eq_stdGaussian

/-- The mean coordinatewise absolute support equals the universal Gaussian absolute-value constant.

**Lean implementation helper.** -/
private theorem coordinate_absSupport_mean
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    (∫ z : Fin n → ℝ,
        finiteGaussianAbsSupport T (WithLp.toLp 2 z)
        ∂HDP.Chapter5.gaussianPiMeasure n) = gaussianComplexity T := by
  have h := (hasLaw_gaussianPi_to_stdGaussian n).integral_comp
    (measurable_finiteGaussianAbsSupport T).aestronglyMeasurable
  simpa [Function.comp_def, gaussianComplexity] using h

/-- The L² norm of finite absolute Gaussian support equals the finite Gaussian L² width.

**Lean implementation helper.** -/
private theorem lpNormRV_absSupport_eq_gaussianL2Width
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    HDP.Chapter1.lpNormRV (finiteGaussianAbsSupport T) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n))) = gaussianL2Width T := by
  rw [HDP.Chapter1.lpNormRV, gaussianL2Width]
  have hnonneg : ∀ g : EuclideanSpace ℝ (Fin n),
      0 ≤ finiteGaussianAbsSupport T g := finiteGaussianAbsSupport_nonneg T
  simp_rw [abs_of_nonneg (hnonneg _)]
  rw [← Real.sqrt_eq_rpow]
  norm_num

/-- The L² norm of a constant random variable is its absolute value.

**Lean implementation helper.** -/
private theorem lpNormRV_const_two
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 ≤ c) :
    HDP.Chapter1.lpNormRV (fun _ : Ω => c) 2 μ = c := by
  rw [HDP.Chapter1.lpNormRV]
  simp only [abs_of_nonneg hc, integral_const, probReal_univ,
    one_mul, div_eq_mul_inv]
  simp only [one_smul]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.rpow_two]
  exact Real.sqrt_sq hc

/-- Centered finite absolute Gaussian support belongs to every finite Lᵖ space.

**Lean implementation helper.** -/
private theorem memLp_centered_absSupport
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    MemLp (fun g : EuclideanSpace ℝ (Fin n) =>
        finiteGaussianAbsSupport T g - gaussianComplexity T) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  exact (memLp_two_finiteGaussianAbsSupport T).sub
    (memLp_const (gaussianComplexity T))

/-- Transfers an Lᵖ bound for centered absolute support to a bound for uncentered support.

**Lean implementation helper.** -/
private theorem centered_absSupport_lpNorm_transfer
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    HDP.Chapter1.lpNormRV
        (fun g : EuclideanSpace ℝ (Fin n) =>
          finiteGaussianAbsSupport T g - gaussianComplexity T) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      HDP.Chapter1.lpNormRV
        (HDP.Chapter5.gaussianCentered (finiteGaussianAbsSupport T)) 2
        (HDP.Chapter5.gaussianPiMeasure n) := by
  have hmean := coordinate_absSupport_mean T
  have hint := (hasLaw_gaussianPi_to_stdGaussian n).integral_comp
    ((measurable_finiteGaussianAbsSupport T).sub_const
      (gaussianComplexity T) |>.pow_const 2 |>.aestronglyMeasurable)
  rw [HDP.Chapter1.lpNormRV, HDP.Chapter1.lpNormRV]
  congr 1
  simpa [Function.comp_def, HDP.Chapter5.gaussianCentered, hmean] using hint.symm

/-- The centered absolute Gaussian support has L² norm at most twenty times the finite radius.

**Lean implementation helper.** -/
private theorem centered_absSupport_lpNorm_le_twenty_radius
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    HDP.Chapter1.lpNormRV
        (fun g : EuclideanSpace ℝ (Fin n) =>
          finiteGaussianAbsSupport T g - gaussianComplexity T) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      20 * finiteGaussianRadius T := by
  let K : ℝ≥0 := ⟨finiteGaussianRadius T, finiteGaussianRadius_nonneg T⟩
  have hconc := HDP.Chapter5.gaussian_lipschitz_concentration n
    (finiteGaussianAbsSupport T) K
    (lipschitzWith_finiteGaussianAbsSupport T)
  have hm : AEMeasurable
      (HDP.Chapter5.gaussianCentered (finiteGaussianAbsSupport T))
      (HDP.Chapter5.gaussianPiMeasure n) :=
    ((measurable_finiteGaussianAbsSupport T).comp
      (WithLp.measurable_toLp 2 (Fin n → ℝ))).sub_const _ |>.aemeasurable
  have hmoment := hconc.1.moment_bound hm (p := (2 : ℝ)) (by norm_num)
  rw [centered_absSupport_lpNorm_transfer T]
  calc
    HDP.Chapter1.lpNormRV
        (HDP.Chapter5.gaussianCentered (finiteGaussianAbsSupport T)) 2
        (HDP.Chapter5.gaussianPiMeasure n) ≤
        HDP.psi2Norm
          (HDP.Chapter5.gaussianCentered (finiteGaussianAbsSupport T))
          (HDP.Chapter5.gaussianPiMeasure n) * Real.sqrt 2 := hmoment
    _ ≤ (2 * Real.sqrt 5 * finiteGaussianRadius T) * Real.sqrt 2 := by
      gcongr
      have hpsi := hconc.2
      change HDP.psi2Norm
          (HDP.Chapter5.gaussianCentered (finiteGaussianAbsSupport T))
          (HDP.Chapter5.gaussianPiMeasure n) ≤
        2 * Real.sqrt 5 * finiteGaussianRadius T at hpsi
      exact hpsi
    _ ≤ 20 * finiteGaussianRadius T := by
      have hs5 : Real.sqrt 5 ≤ 5 := Real.sqrt_le_iff.mpr (by norm_num)
      have hs2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
      have hR := finiteGaussianRadius_nonneg T
      have hcoef : 2 * Real.sqrt 5 * Real.sqrt 2 ≤ 20 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]
      calc
        (2 * Real.sqrt 5 * finiteGaussianRadius T) * Real.sqrt 2 =
            (2 * Real.sqrt 5 * Real.sqrt 2) * finiteGaussianRadius T := by ring
        _ ≤ 20 * finiteGaussianRadius T :=
          mul_le_mul_of_nonneg_right hcoef hR

/-- Finite Gaussian L² width is at most fifty times Gaussian complexity.

**Lean implementation helper.** -/
private theorem gaussianL2Width_le_fifty_complexity
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianL2Width T ≤ 50 * gaussianComplexity T := by
  let Z : EuclideanSpace ℝ (Fin n) → ℝ := fun g =>
    finiteGaussianAbsSupport T g - gaussianComplexity T
  let m : EuclideanSpace ℝ (Fin n) → ℝ := fun _ => gaussianComplexity T
  have hZ : MemLp Z 2 (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    memLp_centered_absSupport T
  have hm : MemLp m 2 (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    memLp_const (gaussianComplexity T)
  have hZ' : MemLp Z (ENNReal.ofReal (2 : ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa using hZ
  have hm' : MemLp m (ENNReal.ofReal (2 : ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa using hm
  have htri := HDP.Chapter1.minkowski_Lp
    (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    (X := Z) (Y := m) (p := (2 : ℝ)) (by norm_num) hZ' hm'
  have hsum : (fun g => Z g + m g) = finiteGaussianAbsSupport T := by
    funext g
    simp [Z, m]
  rw [hsum, lpNormRV_absSupport_eq_gaussianL2Width,
    lpNormRV_const_two _ (gaussianComplexity_nonneg T)] at htri
  change gaussianL2Width T ≤
    HDP.Chapter1.lpNormRV
      (fun g : EuclideanSpace ℝ (Fin n) =>
        finiteGaussianAbsSupport T g - gaussianComplexity T) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) + gaussianComplexity T at htri
  have hcenter := centered_absSupport_lpNorm_le_twenty_radius T
  have hR := finiteGaussianRadius_le_two_complexity T hT
  have hc := gaussianComplexity_nonneg T
  nlinarith

/-- Gaussian width, Gaussian complexity, and the `L2`-supremum variant are equivalent up to universal constants. Finite safe form, together with the load-bearing
Exercise 7.20. Constants are uniform in the dimension and finite set. The
proof uses Gaussian concentration for the absolute support function, whose
Lipschitz constant is the radius of `T`, and the exact one-dimensional
Gaussian absolute moment.

**Book Lemma 7.5.11.** -/
theorem almostEquivalentGaussianWidths :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {n : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        ∀ (y : EuclideanSpace ℝ (Fin n)), y ∈ T →
          gaussianComplexity (differenceFinset T T) = 2 * gaussianWidth T ∧
          c * gaussianComplexity T ≤ gaussianL2Width T ∧
          gaussianL2Width T ≤ C * gaussianComplexity T ∧
          c * (gaussianWidth T + ‖y‖) ≤ gaussianComplexity T ∧
          gaussianComplexity T ≤ C * (gaussianWidth T + ‖y‖) := by
  refine ⟨1 / 4, 50, by norm_num, by norm_num, ?_⟩
  intro n T hT y hy
  have hdiff := gaussianComplexity_difference_exact T hT
  have hc0 := gaussianComplexity_nonneg T
  have hw0 := gaussianWidth_nonneg T hT
  have hn0 := norm_nonneg y
  have hcL2 := gaussianComplexity_le_gaussianL2Width T
  have hL2c := gaussianL2Width_le_fifty_complexity T hT
  have hnorm := half_norm_le_gaussianComplexity T hT hy
  have hw := gaussianWidth_le_gaussianComplexity T
  have hu := gaussianComplexity_translation_upper T hT hy
  refine ⟨hdiff, ?_, hL2c, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- Gaussian width, Gaussian complexity, and the `L2`-supremum variant are equivalent up to universal constants.

**Book Lemma 7.5.11.** -/
theorem gaussianComplexity_difference
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianComplexity (differenceFinset T T) = 2 * gaussianWidth T := by
  obtain ⟨c, C, hc, hC, h⟩ := almostEquivalentGaussianWidths
  rcases hT with ⟨y, hy⟩
  exact (h T ⟨y, hy⟩ y hy).1

/-- Gaussian width, Gaussian complexity, and the `L2`-supremum variant are equivalent up to universal constants. With explicit uniform
two-sided constants.

**Book Lemma 7.5.11.** -/
theorem exercise_7_20_gaussianWidth_vs_complexity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {n : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        ∀ (y : EuclideanSpace ℝ (Fin n)), y ∈ T →
          c * (gaussianWidth T + ‖y‖) ≤ gaussianComplexity T ∧
          gaussianComplexity T ≤ C * (gaussianWidth T + ‖y‖) := by
  obtain ⟨c, C, hc, hC, h⟩ := almostEquivalentGaussianWidths
  exact ⟨c, C, hc, hC, fun T hT y hy =>
    ⟨(h T hT y hy).2.2.2.1, (h T hT y hy).2.2.2.2⟩⟩

end

end HDP.Chapter7

end Source_12_GaussianComplexity

/-! ## Material formerly in `13_EffectiveDimension.lean` -/

section Source_13_EffectiveDimension

/-!
# Book Chapter 7, Definition 7.5.12: effective dimension

The printed quotient is undefined for a singleton.  The reusable finite API
below uses the conventional value zero when the diameter vanishes, and also
exports the exact positive-diameter formula.
-/

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace HDP.Chapter7

noncomputable section

variable {n : ℕ}

/-- Diameter of a finite Euclidean set, totalized by zero on the empty set.

**Lean implementation helper.** -/
def finiteDiameter (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if hT : T.Nonempty then
    (T.product T).sup' (hT.product hT) (fun xy => ‖xy.1 - xy.2‖)
  else 0

/-- Expresses finite diameter as the supremum of pairwise distances.

**Lean implementation helper.** -/
theorem finiteDiameter_eq_sup'
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    finiteDiameter T =
      (T.product T).sup' (hT.product hT) (fun xy => ‖xy.1 - xy.2‖) := by
  simp [finiteDiameter, hT]

/-- The finite diameter is nonnegative.

**Lean implementation helper.** -/
theorem finiteDiameter_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ finiteDiameter T := by
  classical
  by_cases hT : T.Nonempty
  · rw [finiteDiameter_eq_sup' T hT]
    obtain ⟨x, hx⟩ := hT
    have hpair : (x, x) ∈ T.product T := by simp [hx]
    exact (norm_nonneg (x - x)).trans
      (Finset.le_sup' (fun xy => ‖xy.1 - xy.2‖) hpair)
  · simp [finiteDiameter, hT]

/-- The diameter of the empty finite set is zero.

**Lean implementation helper.** -/
@[simp] theorem finiteDiameter_empty :
    finiteDiameter (∅ : Finset (EuclideanSpace ℝ (Fin n))) = 0 := by
  simp [finiteDiameter]

/-- The diameter of a singleton is zero.

**Lean implementation helper.** -/
@[simp] theorem finiteDiameter_singleton
    (x : EuclideanSpace ℝ (Fin n)) : finiteDiameter {x} = 0 := by
  rw [finiteDiameter_eq_sup' {x} (by simp)]
  simp

/-- Effective dimension is width-squared divided by diameter-squared and is bounded by affine dimension. Finite and zero-safe.

**Book Definition 7.5.12.** -/
def effectiveDimension (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if finiteDiameter T = 0 then 0
  else gaussianL2Width (differenceFinset T T) ^ 2 / finiteDiameter T ^ 2

/-- For nonzero diameter, effective dimension is the squared Gaussian L² width divided by squared diameter.

**Lean implementation helper.** -/
theorem effectiveDimension_eq_of_diameter_ne_zero
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : finiteDiameter T ≠ 0) :
    effectiveDimension T =
      gaussianL2Width (differenceFinset T T) ^ 2 / finiteDiameter T ^ 2 := by
  simp [effectiveDimension, hT]

/-- The effective dimension is nonnegative.

**Lean implementation helper.** -/
theorem effectiveDimension_nonneg
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    0 ≤ effectiveDimension T := by
  by_cases hT : finiteDiameter T = 0
  · simp [effectiveDimension, hT]
  · rw [effectiveDimension_eq_of_diameter_ne_zero T hT]
    positivity

/-- The effective dimension of the empty finite set is zero.

**Lean implementation helper.** -/
@[simp] theorem effectiveDimension_empty :
    effectiveDimension (∅ : Finset (EuclideanSpace ℝ (Fin n))) = 0 := by
  simp [effectiveDimension]

/-- The effective dimension of a singleton is zero.

**Lean implementation helper.** -/
@[simp] theorem effectiveDimension_singleton
    (x : EuclideanSpace ℝ (Fin n)) : effectiveDimension {x} = 0 := by
  simp [effectiveDimension]

/-- Linear-algebraic (affine) dimension of a finite Euclidean set.

**Lean implementation helper.** -/
def finiteAffineDimensionNat
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction

/-- Real-valued wrapper used in comparison with effective dimension.

**Lean implementation helper.** -/
def finiteAffineDimension
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  finiteAffineDimensionNat T

/-- The affine dimension of a finite subset is at most the ambient finite dimension.

**Lean implementation helper.** -/
theorem finiteAffineDimension_le_ambient
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    finiteAffineDimension T ≤ n := by
  unfold finiteAffineDimension finiteAffineDimensionNat
  have hNat :
      Module.finrank ℝ
          (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction ≤ n := by
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_le
        (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction)
  exact_mod_cast hNat

/-! ### Affine-span reduction of the Gaussian support -/

/-- The Gaussian inner product with an affine-direction vector belongs to L².

**Lean implementation helper.** -/
private theorem memLp_two_inner_stdGaussian_affine
    (x : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun g : EuclideanSpace ℝ (Fin n) => inner ℝ g x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).continuousLinearMap_comp
      ((innerSL ℝ) x)
  simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm] using h

/-- The squared Gaussian inner product with an affine-direction vector is integrable.

**Lean implementation helper.** -/
private theorem integrable_inner_sq_stdGaussian_affine
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) => (inner ℝ g x) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h :=
    (memLp_two_inner_stdGaussian_affine x).integrable_norm_pow' (p := 2)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- The second moment of the Gaussian inner product with an affine-direction vector equals its squared norm.

**Lean implementation helper.** -/
private theorem integral_inner_sq_stdGaussian_affine
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ g : EuclideanSpace ℝ (Fin n), (inner ℝ g x) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = ‖x‖ ^ 2 := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := (innerSL ℝ) x
  have hmem : MemLp L 2 (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [L, Function.comp_def, innerSL_apply_apply, real_inner_comm] using
      memLp_two_inner_stdGaussian_affine x
  have hv := variance_eq_sub hmem
  rw [integral_strongDual_stdGaussian L, variance_dual_stdGaussian L,
    innerSL_apply_norm] at hv
  have hfun : ∀ g : EuclideanSpace ℝ (Fin n), L g = inner ℝ g x := by
    intro g
    simp [L, innerSL_apply_apply, real_inner_comm]
  have hpow : (L ^ 2 : EuclideanSpace ℝ (Fin n) → ℝ) =
      fun g => (inner ℝ g x) ^ 2 := by
    funext g
    simp [hfun]
  rw [hpow] at hv
  norm_num at hv
  exact hv.symm

/-- The distance between any two points of a finite set is bounded by its diameter.

**Lean implementation helper.** -/
private theorem norm_sub_le_finiteDiameter
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ T) (hy : y ∈ T) :
    ‖x - y‖ ≤ finiteDiameter T := by
  rw [finiteDiameter_eq_sup' T hT]
  exact Finset.le_sup' (fun p => ‖p.1 - p.2‖)
    (show (x, y) ∈ T.product T from Finset.mem_product.mpr ⟨hx, hy⟩)

/-- Differences of points in a finite set lie in its affine-direction subspace.

**Lean implementation helper.** -/
private theorem mem_affineDirection_of_mem_difference
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ differenceFinset T T) :
    z ∈ (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction := by
  classical
  unfold differenceFinset minkowskiSumFinset negFinset at hz
  rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hpT, hpneg⟩
  rcases Finset.mem_image.mp hpneg with ⟨q, hqT, hq⟩
  rw [← hq]
  let A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) :=
    affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))
  have hpA : p.1 ∈ A :=
    mem_affineSpan ℝ (show p.1 ∈ (T : Set _) from hpT)
  have hqA : q ∈ A := mem_affineSpan ℝ (show q ∈ (T : Set _) from hqT)
  change p.1 + -q ∈
    (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction
  simpa only [vsub_eq_sub, sub_eq_add_neg, A] using
    AffineSubspace.vsub_mem_direction hpA hqA

set_option maxHeartbeats 400000 in
-- Elaborating the finite orthonormal-basis expansion needs more than the
-- default heartbeat budget, although the proof term is a finite sum.
/-- The expected squared norm of a Gaussian orthogonal projection equals the dimension of the subspace.

**Lean implementation helper.** -/
private theorem integral_orthogonalProjection_norm_sq
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    (∫ g : EuclideanSpace ℝ (Fin n), ‖U.orthogonalProjectionOnto g‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = Module.finrank ℝ U := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ U)) ℝ U :=
    stdOrthonormalBasis ℝ U
  have hnorm (g : EuclideanSpace ℝ (Fin n)) :
      ‖U.orthogonalProjectionOnto g‖ ^ 2 =
        ∑ i, (inner ℝ g (b i : EuclideanSpace ℝ (Fin n))) ^ 2 := by
    rw [← b.sum_sq_inner_left (U.orthogonalProjectionOnto g)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [U.inner_orthogonalProjectionOnto_eq_of_mem_right (b i) g]
  simp_rw [hnorm]
  rw [integral_finsetSum]
  · simp_rw [integral_inner_sq_stdGaussian_affine]
    have hb : ∀ i : Fin (Module.finrank ℝ U),
        ‖(b i : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      intro i
      change ‖b i‖ ^ 2 = 1
      rw [b.norm_eq_one]
      norm_num
    simp_rw [hb]
    simp
  · intro i _hi
    exact integrable_inner_sq_stdGaussian_affine
      ((b i : U) : EuclideanSpace ℝ (Fin n))

/-- Absolute Gaussian support of a difference set is bounded by diameter times the norm of the projection onto its affine direction.

**Lean implementation helper.** -/
private theorem absSupport_difference_le_diameter_mul_projection
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianAbsSupport (differenceFinset T T) g ≤
      finiteDiameter T *
        ‖(affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction
          |>.orthogonalProjectionOnto g‖ := by
  classical
  let U := (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction
  have hD : (differenceFinset T T).Nonempty := differenceFinset_nonempty hT hT
  rw [finiteGaussianAbsSupport_eq_sup' _ hD]
  apply Finset.sup'_le
  intro z hz
  have hzU : z ∈ U := mem_affineDirection_of_mem_difference T hz
  let zU : U := ⟨z, hzU⟩
  have hinner : inner ℝ g z = inner ℝ (U.orthogonalProjectionOnto g) zU := by
    symm
    exact U.inner_orthogonalProjectionOnto_eq_of_mem_right zU g
  have hnormz : ‖z‖ ≤ finiteDiameter T := by
    unfold differenceFinset minkowskiSumFinset negFinset at hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, hpz⟩
    rcases Finset.mem_product.mp hp with ⟨hpT, hpneg⟩
    rcases Finset.mem_image.mp hpneg with ⟨q, hqT, hq⟩
    rw [← hpz, ← hq]
    simpa [sub_eq_add_neg] using norm_sub_le_finiteDiameter T hT hpT hqT
  calc
    |inner ℝ g z| = |inner ℝ (U.orthogonalProjectionOnto g) zU| := by
      rw [hinner]
    _ ≤ ‖U.orthogonalProjectionOnto g‖ * ‖zU‖ := by
      simpa [Real.norm_eq_abs] using
        (@norm_inner_le_norm ℝ U _ _ _ (U.orthogonalProjectionOnto g) zU)
    _ ≤ ‖U.orthogonalProjectionOnto g‖ * finiteDiameter T :=
      mul_le_mul_of_nonneg_left (by simpa [zU] using hnormz) (norm_nonneg _)
    _ = finiteDiameter T * ‖U.orthogonalProjectionOnto g‖ := by ring

/-- The squared absolute Gaussian support of a finite affine set is integrable.

**Lean implementation helper.** -/
private theorem integrable_absSupport_sq_affine
    (S : Finset (EuclideanSpace ℝ (Fin n))) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
        (finiteGaussianAbsSupport S g) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := (memLp_two_finiteGaussianAbsSupport S).integrable_norm_pow' (p := 2)
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (finiteGaussianAbsSupport_nonneg S _)] using h

/-- The squared norm of a standard Gaussian orthogonal projection is integrable.

**Lean implementation helper.** -/
private theorem integrable_orthogonalProjection_norm_sq
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
        ‖U.orthogonalProjectionOnto g‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hmem : MemLp (U.orthogonalProjectionOnto :
      EuclideanSpace ℝ (Fin n) → U) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    exact (ProbabilityTheory.IsGaussian.memLp_two_id :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n)))).continuousLinearMap_comp
          U.orthogonalProjectionOnto
  exact hmem.integrable_norm_pow' (p := 2)

/-- The squared Gaussian L² width of a difference set is bounded by diameter squared times affine dimension.

**Lean implementation helper.** -/
private theorem gaussianL2Width_difference_sq_le_affineDimension
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    gaussianL2Width (differenceFinset T T) ^ 2 ≤
      finiteDiameter T ^ 2 *
        Module.finrank ℝ
          (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction := by
  let U := (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction
  let D := differenceFinset T T
  have hdiam : 0 ≤ finiteDiameter T := finiteDiameter_nonneg T
  have hpoint (g : EuclideanSpace ℝ (Fin n)) :
      (finiteGaussianAbsSupport D g) ^ 2 ≤
        (finiteDiameter T * ‖U.orthogonalProjectionOnto g‖) ^ 2 := by
    have hF : 0 ≤ finiteGaussianAbsSupport D g :=
      finiteGaussianAbsSupport_nonneg D g
    have hR : 0 ≤ finiteDiameter T * ‖U.orthogonalProjectionOnto g‖ :=
      mul_nonneg hdiam (norm_nonneg _)
    have hle := absSupport_difference_le_diameter_mul_projection T hT g
    exact (sq_le_sq₀ hF hR).2 hle
  have hFint : Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
      (finiteGaussianAbsSupport D g) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    integrable_absSupport_sq_affine D
  have hUint := integrable_orthogonalProjection_norm_sq U
  have hRint : Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
      (finiteDiameter T * ‖U.orthogonalProjectionOnto g‖) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [mul_pow] using hUint.const_mul (finiteDiameter T ^ 2)
  have hi := integral_mono hFint hRint hpoint
  have hnonneg : 0 ≤ ∫ g : EuclideanSpace ℝ (Fin n),
      (finiteGaussianAbsSupport D g) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    integral_nonneg (fun g => sq_nonneg _)
  calc
    gaussianL2Width D ^ 2 =
        ∫ g : EuclideanSpace ℝ (Fin n),
          (finiteGaussianAbsSupport D g) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      rw [gaussianL2Width, Real.sq_sqrt hnonneg]
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin n),
        (finiteDiameter T * ‖U.orthogonalProjectionOnto g‖) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := hi
    _ = finiteDiameter T ^ 2 *
        ∫ g : EuclideanSpace ℝ (Fin n),
          ‖U.orthogonalProjectionOnto g‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
    _ = finiteDiameter T ^ 2 * Module.finrank ℝ U := by
      rw [integral_orthogonalProjection_norm_sq U]
    _ = finiteDiameter T ^ 2 *
        Module.finrank ℝ
          (affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin n)))).direction := rfl

/-- Effective dimension is width-squared divided by diameter-squared and is bounded by affine dimension. Effective dimension is at
most affine dimension. The proof projects the standard Gaussian onto the
direction of the affine span, expands that projection in an orthonormal
basis, and computes its exact second moment as the dimension.

**Book Definition 7.5.12.** -/
theorem exercise_7_21a_effectiveDimension_le_affineDimension
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    effectiveDimension T ≤ finiteAffineDimension T := by
  by_cases hT : T.Nonempty
  · by_cases hd : finiteDiameter T = 0
    · simp [effectiveDimension, hd, finiteAffineDimension]
    · have hdpos : 0 < finiteDiameter T :=
        lt_of_le_of_ne (finiteDiameter_nonneg T) (Ne.symm hd)
      rw [effectiveDimension_eq_of_diameter_ne_zero T hd]
      unfold finiteAffineDimension finiteAffineDimensionNat
      apply (div_le_iff₀ (sq_pos_of_pos hdpos)).2
      simpa [mul_comm] using
        gaussianL2Width_difference_sq_le_affineDimension T hT
  · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    simp [finiteAffineDimension, finiteAffineDimensionNat]

/-- The effective-dimension quotient for a Euclidean unit ball in `ℝᵈ`.
The support of the difference ball is `2‖g‖` and its diameter is `2`.

**Lean implementation helper.** -/
def euclideanBallEffectiveDimension (d : ℕ) : ℝ :=
  (∫ g : EuclideanSpace ℝ (Fin d), (2 * ‖g‖) ^ 2
    ∂stdGaussian (EuclideanSpace ℝ (Fin d))) / 2 ^ 2

/-- A standard Gaussian coordinate has second moment one.

**Lean implementation helper.** -/
private theorem integral_sq_stdGaussian_coordinate (i : Fin n) :
    (∫ g : EuclideanSpace ℝ (Fin n), (g i) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 1 := by
  have hbase : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num))
    simpa using h.symm
  have h := (hasLaw_stdGaussian_coordinate i).integral_comp
    (f := fun x : ℝ => x ^ 2) (by fun_prop)
  simpa [Function.comp_def] using h.trans hbase

/-- The square of a standard Gaussian coordinate is integrable.

**Lean implementation helper.** -/
private theorem integrable_sq_stdGaussian_coordinate (i : Fin n) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) => (g i) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let e : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  have hm : MemLp (fun g : EuclideanSpace ℝ (Fin n) => g i) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    have h := (ProbabilityTheory.IsGaussian.memLp_two_id :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n)))).continuousLinearMap_comp e
    simpa [e, Function.comp_def] using h
  have hi := hm.integrable_norm_pow' (p := 2)
  simpa [Real.norm_eq_abs, sq_abs] using hi

/-- The expected squared norm of a standard Gaussian vector equals the dimension.

**Lean implementation helper.** -/
theorem integral_norm_sq_stdGaussian (d : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin d), ‖g‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) = d := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp_rw [integral_sq_stdGaussian_coordinate]
    simp
  · intro i hi
    exact integrable_sq_stdGaussian_coordinate i

/-- Effective dimension is at most affine dimension and equals dimension for Euclidean balls. A Euclidean ball has
effective dimension equal to its algebraic dimension. Orthogonal invariance
transports this identity to a ball in any `d`-dimensional subspace.

**Book Exercise 7.21.** -/
theorem exercise_7_21b_euclideanBall (d : ℕ) :
    euclideanBallEffectiveDimension d = d := by
  rw [euclideanBallEffectiveDimension]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_norm_sq_stdGaussian]
  norm_num

/-- The width/diameter constants are optimal, witnessed by a symmetric pair and Euclidean balls. Upper extreme: Euclidean balls have width of
order `√n`, with the same explicit radial estimate as Lemma 7.5.5.

**Book Remark 7.5.3.** -/
theorem exercise_7_16_euclideanBall :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 0 < n →
      Real.sqrt n - C / Real.sqrt n ≤ euclideanBallGaussianWidth n ∧
      euclideanBallGaussianWidth n ≤ Real.sqrt n := by
  simpa [euclideanBallGaussianWidth] using gaussianRadialMean_bounds

end

end HDP.Chapter7

end Source_13_EffectiveDimension

/-! ## Material formerly in `14_RandomProjections.lean` -/

section Source_14_RandomProjections

/-!
# Book Chapter 7, §7.6: random projections of sets

The source's matrix description is corrected here: an `m × n` coordinate
restriction consists of the first `m` rows of a Haar orthogonal matrix.  The
equivalent first-column model is its transpose.  We use Chapter 5's genuine
Grassmannian probability law, so the statement is independent of coordinates.

All set APIs are finite.  This makes the diameter, support functions, and
expectations total and measurable without pretending that an arbitrary
bounded-set supremum is automatically measurable.  The constants are
quantified before the dimensions and sets, so they really are absolute.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators RealInnerProductSpace ENNReal NNReal

namespace HDP.Chapter7

noncomputable section

/-- Image of a finite set under a Grassmannian orthogonal projection.

**Lean implementation helper.** -/
def grassmannProjectedFinset {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  T.image (HDP.Chapter5.randomProjection P)

/-- Diameter of a projected finite set. `Metric.diam` uses the safe value
zero on the empty set.

**Lean implementation helper.** -/
def grassmannProjectedDiameter {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Metric.diam (grassmannProjectedFinset P T :
    Set (EuclideanSpace ℝ (Fin n)))

/-- Image of a finite set under a rectangular real matrix.

**Lean implementation helper.** -/
def matrixImageFinset {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Finset (EuclideanSpace ℝ (Fin m)) :=
  T.image A.toEuclideanLin

/-- Diameter after a rectangular matrix map.

**Lean implementation helper.** -/
def matrixImageDiameter {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Metric.diam (matrixImageFinset A T :
    Set (EuclideanSpace ℝ (Fin m)))

/-- Haar orbit of a fixed unit vector is uniform on the sphere.

**Book Exercise 7.24.** -/
theorem exercise_7_24_haarOrbit_uniform {n : ℕ} (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.map (HDP.Chapter5.inverseOrthogonalSphereOrbit v)
        (HDP.Chapter5.orthogonalHaarMeasure n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) :=
  HDP.Chapter5.map_inverseOrthogonalSphereOrbit hn v

/-- Expresses projected diameter as the supremum of pairwise projected distances.

**Lean implementation helper.** -/
private theorem grassmannProjectedDiameter_eq_sup'_aux {m n : ℕ}
    (P : HDP.Chapter5.Grassmannian n m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    grassmannProjectedDiameter P T =
      (T.product T).sup' (hT.product hT) (fun p =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖) := by
  classical
  let R := (T.product T).sup' (hT.product hT) (fun p =>
    ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
  have hR : 0 ≤ R := by
    have hTT : (T.product T).Nonempty := hT.product hT
    obtain ⟨x, hx⟩ := hT
    change 0 ≤ (T.product T).sup' hTT (fun p =>
      ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
    have hle := Finset.le_sup' (fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
      (show (x, x) ∈ T.product T from by simp [hx])
    simpa using hle
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le hR
    intro a ha b hb
    simp only [grassmannProjectedFinset, Finset.coe_image,
      Set.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hx' : x ∈ T := by exact hx
    have hy' : y ∈ T := by exact hy
    rw [dist_eq_norm, ← map_sub]
    change ‖HDP.Chapter5.randomProjection P (x - y)‖ ≤
      (T.product T).sup' (hT.product hT) (fun p =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
    exact Finset.le_sup' (fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) =>
        ‖HDP.Chapter5.randomProjection P (p.1 - p.2)‖)
      (show (x, y) ∈ T.product T from by simp [hx', hy'])
  · apply Finset.sup'_le
    intro p hp
    have hp' : p.1 ∈ T ∧ p.2 ∈ T := Finset.mem_product.mp hp
    rw [map_sub, ← dist_eq_norm]
    apply Metric.dist_le_diam_of_mem
    · exact (grassmannProjectedFinset P T).finite_toSet.isBounded
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.1, hp'.1, rfl⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.2, hp'.2, rfl⟩)

/-- Projected diameter is measurable as a function of the Grassmannian subspace.

**Lean implementation helper.** -/
private theorem measurable_grassmannProjectedDiameter_aux {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Measurable (fun P : HDP.Chapter5.Grassmannian n m =>
      grassmannProjectedDiameter P T) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show (fun P : HDP.Chapter5.Grassmannian n m =>
        grassmannProjectedDiameter P T) =
      (T.product T).sup' (hT.product hT) (fun p =>
        fun P : HDP.Chapter5.Grassmannian n m =>
          HDP.Chapter5.grassmannProjectedNorm (p.1 - p.2) P) by
      funext P
      rw [grassmannProjectedDiameter_eq_sup'_aux P T hT]
      exact (Finset.sup'_apply (hT.product hT) (fun p =>
        fun P : HDP.Chapter5.Grassmannian n m =>
          HDP.Chapter5.grassmannProjectedNorm (p.1 - p.2) P) P).symm]
    apply Finset.measurable_sup'
    intro p hp
    exact (HDP.Chapter5.continuous_grassmannProjectedNorm
      (m := m) (p.1 - p.2)).measurable
  · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    simp [grassmannProjectedDiameter, grassmannProjectedFinset]

/-- Zero-padding from the first `m` coordinates into `n` coordinates.

**Lean implementation helper.** -/
private def firstCoordinateEmbedding_aux {m n : ℕ} (_hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j =>
    if hj : j.val < m then z ⟨j.val, hj⟩ else 0

/-- Evaluating the first-coordinate embedding returns the scalar in the first coordinate and zero elsewhere.

**Lean implementation helper.** -/
@[simp] private theorem firstCoordinateEmbedding_apply_aux {m n : ℕ}
    (hmn : m ≤ n) (z : EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    firstCoordinateEmbedding_aux hmn z j =
      if hj : j.val < m then z ⟨j.val, hj⟩ else 0 := rfl

/-- The norm of the first-coordinate embedding is the absolute value of its scalar input.

**Lean implementation helper.** -/
private theorem norm_firstCoordinateEmbedding_aux {m n : ℕ}
    (hmn : m ≤ n) (z : EuclideanSpace ℝ (Fin m)) :
    ‖firstCoordinateEmbedding_aux hmn z‖ = ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [firstCoordinateEmbedding_apply_aux]
  let F : Fin n → ℝ := fun j =>
    (if hj : j.val < m then z ⟨j.val, hj⟩ else 0) ^ 2
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin n)) := by simp
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      j ∉ Finset.univ.map e → F j = 0 := by
    intro j hj hjnot
    simp only [F]
    split_ifs with hjlt
    · exfalso
      apply hjnot
      exact Finset.mem_map.mpr ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · simp
  calc
    (∑ j : Fin n, (if hj : j.val < m then z ⟨j.val, hj⟩ else 0) ^ 2) =
        ∑ j : Fin n, F j := by rfl
    _ = ∑ j ∈ Finset.univ.map e, F j :=
      (Finset.sum_subset hsub hzero).symm
    _ = ∑ i : Fin m, F (e i) := by rw [Finset.sum_map]
    _ = ∑ i : Fin m, z i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [F, e, Fin.castLEEmb_apply]

/-- The inner product with the first-coordinate restriction equals the first coordinate times the corresponding inner product.

**Lean implementation helper.** -/
private theorem inner_firstCoordinateRestriction_aux {m n : ℕ}
    (hmn : m ≤ n) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (HDP.Chapter5.firstCoordinateRestriction hmn x) z =
      inner ℝ x (firstCoordinateEmbedding_aux hmn z) := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    HDP.Chapter5.firstCoordinateRestriction_apply,
    firstCoordinateEmbedding_apply_aux]
  let F : Fin n → ℝ := fun j =>
    x j * (if hj : j.val < m then z ⟨j.val, hj⟩ else 0)
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin n)) := by simp
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      j ∉ Finset.univ.map e → F j = 0 := by
    intro j hj hjnot
    simp only [F]
    split_ifs with hjlt
    · exfalso
      apply hjnot
      exact Finset.mem_map.mpr ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · simp
  calc
    (∑ i : Fin m, x (Fin.castLE hmn i) * z i) =
        ∑ i : Fin m, F (e i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [F, e, Fin.castLEEmb_apply]
    _ = ∑ j ∈ Finset.univ.map e, F j := by rw [Finset.sum_map]
    _ = ∑ j : Fin n, F j := Finset.sum_subset hsub hzero
    _ = ∑ j : Fin n,
        x j * (if hj : j.val < m then z ⟨j.val, hj⟩ else 0) := by rfl

/-- Rewrites the inner product with a rotated coordinate restriction using the inverse rotation.

**Lean implementation helper.** -/
private theorem inner_rotatedCoordinateRestriction_aux {m n : ℕ}
    (hmn : m ≤ n) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) :
    inner ℝ
        (HDP.Chapter5.firstCoordinateRestriction hmn
          (HDP.Chapter5.orthogonalAction U⁻¹ x)) z =
      inner ℝ x
        (HDP.Chapter5.orthogonalAction U
          (firstCoordinateEmbedding_aux hmn z)) := by
  rw [inner_firstCoordinateRestriction_aux]
  let L := HDP.Chapter5.orthogonalLinearIsometryEquiv U
  have h := L.inner_map_map
    (HDP.Chapter5.orthogonalAction U⁻¹ x)
    (firstCoordinateEmbedding_aux hmn z)
  change inner ℝ
      (HDP.Chapter5.orthogonalAction U
        (HDP.Chapter5.orthogonalAction U⁻¹ x))
      (HDP.Chapter5.orthogonalAction U
        (firstCoordinateEmbedding_aux hmn z)) = _ at h
  rw [← HDP.Chapter5.orthogonalAction_mul] at h
  have hone : HDP.Chapter5.orthogonalAction
      (1 : Matrix.orthogonalGroup (Fin n) ℝ) x = x := by
    unfold HDP.Chapter5.orthogonalAction
    simp
  have hmul : U * U⁻¹ = 1 := mul_inv_cancel U
  rw [hmul, hone] at h
  exact h.symm

/-- Maps an orthogonal transformation to the image of the first unit vector.

**Lean implementation helper.** -/
private def forwardOrthogonalSphereOrbit_aux {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨HDP.Chapter5.orthogonalAction U v, by
    simpa [Metric.mem_sphere, dist_zero_right] using
      congrArg (fun r : ℝ => r) (HDP.Chapter5.norm_orthogonalAction U v)⟩

/-- The orbit map sending an orthogonal transformation to the image of the first unit vector is measurable.

**Lean implementation helper.** -/
private theorem measurable_forwardOrthogonalSphereOrbit_aux {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measurable (forwardOrthogonalSphereOrbit_aux v) := by
  have hfun : forwardOrthogonalSphereOrbit_aux v =
      HDP.Chapter5.inverseOrthogonalSphereOrbit v ∘ Inv.inv := by
    funext U
    apply Subtype.ext
    rfl
  rw [hfun]
  exact (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable.comp
    measurable_inv

/-- Inversion preserves Haar probability measure on the orthogonal group.

**Lean implementation helper.** -/
private theorem map_inv_orthogonalHaarMeasure_aux (n : ℕ) :
    Measure.map Inv.inv (HDP.Chapter5.orthogonalHaarMeasure n) =
      HDP.Chapter5.orthogonalHaarMeasure n := by
  let μ := HDP.Chapter5.orthogonalHaarMeasure n
  letI : Measure.IsMulRightInvariant μ := by
    constructor
    intro g
    let ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
      Measure.map (fun x => x * g) μ
    letI : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map (by fun_prop :
        AEMeasurable (fun x : Matrix.orthogonalGroup (Fin n) ℝ => x * g) μ)
    letI : ν.IsHaarMeasure := by
      dsimp only [ν]
      infer_instance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν μ
  let ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ) := μ.inv
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop :
      AEMeasurable
        (fun x : Matrix.orthogonalGroup (Fin n) ℝ => x⁻¹) μ)
  letI : ν.IsHaarMeasure := by
    refine
      { toIsMulLeftInvariant := inferInstance
        toIsFiniteMeasureOnCompacts := inferInstance
        toIsOpenPosMeasure := inferInstance }
  have h := Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν μ
  simpa [ν, μ, Measure.inv] using h

/-- The forward orbit of the first unit vector pushes orthogonal Haar measure to uniform sphere measure.

**Lean implementation helper.** -/
private theorem map_forwardOrthogonalSphereOrbit_aux {n : ℕ} (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.map (forwardOrthogonalSphereOrbit_aux v)
        (HDP.Chapter5.orthogonalHaarMeasure n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  have hfun : forwardOrthogonalSphereOrbit_aux v =
      HDP.Chapter5.inverseOrthogonalSphereOrbit v ∘ Inv.inv := by
    funext U
    apply Subtype.ext
    rfl
  rw [hfun, ← Measure.map_map]
  · rw [map_inv_orthogonalHaarMeasure_aux,
      HDP.Chapter5.map_inverseOrthogonalSphereOrbit hn v]
  · exact (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable
  · exact measurable_inv

/-- Every member of a finite difference set has norm at most the original finite diameter.

**Lean implementation helper.** -/
private theorem norm_mem_difference_le_diameter_aux {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ differenceFinset T T) :
    ‖z‖ ≤ finiteEuclideanDiameter T := by
  classical
  unfold differenceFinset minkowskiSumFinset negFinset at hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hpT, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨q, hqT, hq⟩ := Finset.mem_image.mp hp2
  rw [← hq]
  change ‖p.1 - q‖ ≤ finiteEuclideanDiameter T
  exact norm_sub_le_finiteEuclideanDiameter T hT hpT hqT

/-- Gaussian support of a finite difference set is Lipschitz with constant equal to its diameter.

**Lean implementation helper.** -/
private theorem finiteGaussianSupport_difference_lipschitz_aux {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    LipschitzWith (⟨finiteEuclideanDiameter T,
      finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0)
      (finiteGaussianSupport (differenceFinset T T)) := by
  classical
  rw [lipschitzWith_iff_dist_le_mul]
  intro g h
  let D := differenceFinset T T
  have hD : D.Nonempty := differenceFinset_nonempty hT hT
  obtain ⟨zg, hzg, hzgmax⟩ := Finset.exists_mem_eq_sup' hD
    (fun z => inner ℝ g z)
  obtain ⟨zh, hzh, hzhmax⟩ := Finset.exists_mem_eq_sup' hD
    (fun z => inner ℝ h z)
  rw [Real.dist_eq, finiteGaussianSupport_eq_sup' D hD,
    hzgmax, finiteGaussianSupport_eq_sup' D hD, hzhmax]
  change |inner ℝ g zg - inner ℝ h zh| ≤
    finiteEuclideanDiameter T * ‖g - h‖
  rw [abs_le]
  constructor
  · have hle : inner ℝ g zh ≤ inner ℝ g zg := by
      rw [← hzgmax]
      exact Finset.le_sup' (fun z => inner ℝ g z) hzh
    have hinner : inner ℝ (h - g) zh ≤
        ‖h - g‖ * finiteEuclideanDiameter T := by
      calc
        inner ℝ (h - g) zh ≤ ‖h - g‖ * ‖zh‖ := real_inner_le_norm _ _
        _ ≤ ‖h - g‖ * finiteEuclideanDiameter T :=
          mul_le_mul_of_nonneg_left
            (norm_mem_difference_le_diameter_aux T hT hzh) (norm_nonneg _)
    rw [norm_sub_rev] at hinner
    rw [inner_sub_left] at hinner
    rw [mul_comm] at hinner
    linarith
  · have hle : inner ℝ h zg ≤ inner ℝ h zh := by
      rw [← hzhmax]
      exact Finset.le_sup' (fun z => inner ℝ h z) hzg
    have hinner : inner ℝ (g - h) zg ≤
        ‖g - h‖ * finiteEuclideanDiameter T := by
      calc
        inner ℝ (g - h) zg ≤ ‖g - h‖ * ‖zg‖ := real_inner_le_norm _ _
        _ ≤ ‖g - h‖ * finiteEuclideanDiameter T :=
          mul_le_mul_of_nonneg_left
            (norm_mem_difference_le_diameter_aux T hT hzg) (norm_nonneg _)
    rw [inner_sub_left] at hinner
    rw [mul_comm] at hinner
    linarith

/-- The mean radius of a nontrivial standard Gaussian vector is strictly positive.

**Lean implementation helper.** -/
private theorem gaussianRadialMean_pos_aux {n : ℕ} (hn : 0 < n) :
    0 < gaussianRadialMean n := by
  let i : Fin n := ⟨0, hn⟩
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  let S := diameterSymmetricPairFinset v
  have hv : ‖v‖ = 1 := by simp [v]
  have hS : S.Nonempty := by simp [S, diameterSymmetricPairFinset]
  have hw := gaussianWidth_diameterSymmetricPair_eq v
  rw [hv, mul_one] at hw
  have hwpos : 0 < gaussianWidth S := by
    rw [hw]
    positivity
  have hsnonneg : 0 ≤ sphericalWidth S := sphericalWidth_nonneg S hS hn
  have hpolar := gaussianWidth_eq_radialMean_mul_sphericalWidth S hS hn
  nlinarith

/-- Spherical width of a finite difference set equals Gaussian width divided by the mean Gaussian radius.

**Lean implementation helper.** -/
private theorem sphericalWidth_difference_aux {n : ℕ} (hn : 0 < n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    sphericalWidth (differenceFinset T T) = 2 * sphericalWidth T := by
  have hD : (differenceFinset T T).Nonempty :=
    differenceFinset_nonempty hT hT
  have hpolarD := gaussianWidth_eq_radialMean_mul_sphericalWidth
    (differenceFinset T T) hD hn
  have hpolarT := gaussianWidth_eq_radialMean_mul_sphericalWidth T hT hn
  have hwidthD := gaussianWidth_difference T T hT hT
  have hrpos := gaussianRadialMean_pos_aux hn
  rw [hwidthD] at hpolarD
  nlinarith

/-- The selected finite quarter-net of the Euclidean unit sphere is nonempty.

**Lean implementation helper.** -/
private theorem quarterNet_nonempty_aux {m : ℕ} (hm : 0 < m)
    {N : Finset (EuclideanSpace ℝ (Fin m))}
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m)))) :
    N.Nonempty := by
  let i : Fin m := ⟨0, hm⟩
  let u : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
  have hu : ‖u‖ = 1 := by simp [u]
  obtain ⟨z, hz, hdist⟩ := hN.2 u hu
  exact ⟨z, hz⟩

/-- A quarter-net controls the Euclidean norm by twice the largest absolute inner product with a net point.

**Lean implementation helper.** -/
private theorem norm_le_quarterNet_sup_abs_inner_aux {m : ℕ} (hm : 0 < m)
    {N : Finset (EuclideanSpace ℝ (Fin m))}
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m))))
    (q : EuclideanSpace ℝ (Fin m)) :
    ‖q‖ ≤ (4 / 3 : ℝ) *
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z => |inner ℝ q z|) := by
  have hNne := quarterNet_nonempty_aux hm hN
  by_cases hq : q = 0
  · subst q
    simp
  · let u : EuclideanSpace ℝ (Fin m) := ‖q‖⁻¹ • q
    have hqn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hqn]
    obtain ⟨z, hzN, huz⟩ := hN.2 u hu
    have hqu : inner ℝ q u = ‖q‖ := by
      rw [show u = ‖q‖⁻¹ • q by rfl, inner_smul_right,
        real_inner_self_eq_norm_sq]
      field_simp [hqn]
    have hsplit : inner ℝ q u = inner ℝ q z + inner ℝ q (u - z) := by
      rw [inner_sub_right]
      ring
    have herr : |inner ℝ q (u - z)| ≤ ‖q‖ / 4 := by
      calc
        |inner ℝ q (u - z)| ≤ ‖q‖ * ‖u - z‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ ‖q‖ * (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left huz (norm_nonneg q)
        _ = ‖q‖ / 4 := by ring
    have hzsup : |inner ℝ q z| ≤
        N.sup' hNne (fun w => |inner ℝ q w|) :=
      Finset.le_sup' (fun w => |inner ℝ q w|) hzN
    have hmain : ‖q‖ ≤
        N.sup' hNne (fun w => |inner ℝ q w|) + ‖q‖ / 4 := by
      calc
        ‖q‖ = inner ℝ q z + inner ℝ q (u - z) := by rw [← hsplit, hqu]
        _ ≤ |inner ℝ q z| + |inner ℝ q (u - z)| := by
          exact add_le_add (le_abs_self _) (le_abs_self _)
        _ ≤ N.sup' hNne (fun w => |inner ℝ q w|) + ‖q‖ / 4 :=
          add_le_add hzsup herr
    nlinarith

/-- An absolute inner product with a net point is bounded by Gaussian support of the associated difference set.

**Lean implementation helper.** -/
private theorem abs_inner_le_support_difference_aux {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ differenceFinset T T) :
    |inner ℝ g z| ≤ finiteGaussianSupport (differenceFinset T T) g := by
  have hD := differenceFinset_nonempty hT hT
  rw [finiteGaussianSupport_eq_sup' _ hD, abs_le]
  constructor
  · have hnz : -z ∈ differenceFinset T T := by
      classical
      unfold differenceFinset minkowskiSumFinset negFinset at hz ⊢
      rw [Finset.mem_image] at hz ⊢
      obtain ⟨⟨x, ny⟩, hp, rfl⟩ := hz
      have hx : x ∈ T := (Finset.mem_product.mp hp).1
      have hny : ny ∈ Finset.image
          (fun x : EuclideanSpace ℝ (Fin n) => -x) T :=
        (Finset.mem_product.mp hp).2
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hny
      refine ⟨(y, -x), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨hy, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      · simp only [neg_add_rev, neg_neg]
    have hle := Finset.le_sup' (fun w : EuclideanSpace ℝ (Fin n) =>
      inner ℝ g w) hnz
    simp only [inner_neg_right] at hle
    linarith
  · exact Finset.le_sup' (fun w : EuclideanSpace ℝ (Fin n) =>
      inner ℝ g w) hz

/-- Bounds projected diameter along an orthogonal orbit by twice a finite net support functional.

**Lean implementation helper.** -/
private theorem grassmannProjectedDiameter_orbit_le_net_aux {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m))))
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    grassmannProjectedDiameter (HDP.Chapter5.grassmannOrbit n m U) T ≤
      (4 / 3 : ℝ) * N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (HDP.Chapter5.orthogonalAction U
            (firstCoordinateEmbedding_aux hmn z))) := by
  rw [grassmannProjectedDiameter_eq_sup'_aux _ T hT]
  apply Finset.sup'_le
  intro p hp
  have hp' := Finset.mem_product.mp hp
  rw [HDP.Chapter5.randomProjection_grassmannOrbit_norm hmn]
  change ‖HDP.Chapter5.firstCoordinateRestriction hmn
      (HDP.Chapter5.orthogonalAction U⁻¹ (p.1 - p.2))‖ ≤ _
  calc
    _ ≤ (4 / 3 : ℝ) * N.sup' (quarterNet_nonempty_aux hm hN)
        (fun z => |inner ℝ
          (HDP.Chapter5.firstCoordinateRestriction hmn
            (HDP.Chapter5.orthogonalAction U⁻¹ (p.1 - p.2))) z|) :=
      norm_le_quarterNet_sup_abs_inner_aux hm hN _
    _ ≤ (4 / 3 : ℝ) * N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (HDP.Chapter5.orthogonalAction U
          (firstCoordinateEmbedding_aux hmn z))) := by
      gcongr
      rw [inner_rotatedCoordinateRestriction_aux]
      rw [real_inner_comm]
      exact abs_inner_le_support_difference_aux T hT _
        (show p.1 - p.2 ∈ differenceFinset T T by
          unfold differenceFinset minkowskiSumFinset negFinset
          apply Finset.mem_image.mpr
          refine ⟨(p.1, -p.2), Finset.mem_product.mpr ⟨hp'.1, ?_⟩,
            (sub_eq_add_neg _ _).symm⟩
          exact Finset.mem_image.mpr ⟨p.2, hp'.2, rfl⟩)

/-- Composition with a measure-preserving map preserves the sub-Gaussian property.

**Lean implementation helper.** -/
private theorem subGaussian_comp_measurePreserving_aux
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : Ω → Ω') (hmp : MeasurePreserving f μ ν)
    (Y : Ω' → ℝ) (hYm : AEMeasurable Y ν) (hY : HDP.SubGaussian Y ν) :
    HDP.SubGaussian (Y ∘ f) μ := by
  let ξ := Measure.map Y ν
  have hYlaw : HasLaw Y ξ ν := ⟨hYm, rfl⟩
  have hXlaw : HasLaw (Y ∘ f) ξ μ := hYlaw.comp hmp.hasLaw
  obtain ⟨K, hK, hpsi⟩ := hY
  refine ⟨K, hK, ?_⟩
  rw [HDP.psi2MGF_eq_of_hasLaw hXlaw K]
  rw [← HDP.psi2MGF_eq_of_hasLaw hYlaw K]
  exact hpsi

/-- Composition with a measure-preserving map preserves the ψ₂ norm.

**Lean implementation helper.** -/
private theorem psi2Norm_comp_measurePreserving_aux
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : Ω → Ω') (hmp : MeasurePreserving f μ ν)
    (Y : Ω' → ℝ) (hYm : AEMeasurable Y ν) :
    HDP.psi2Norm (Y ∘ f) μ = HDP.psi2Norm Y ν := by
  let ξ := Measure.map Y ν
  have hYlaw : HasLaw Y ξ ν := ⟨hYm, rfl⟩
  have hXlaw : HasLaw (Y ∘ f) ξ μ := hYlaw.comp hmp.hasLaw
  rw [HDP.psi2Norm_eq_of_hasLaw hXlaw,
    HDP.psi2Norm_eq_of_hasLaw hYlaw]

/-- Bounds the square root of the logarithm of a quarter-net's cardinality by a dimensional constant.

**Lean implementation helper.** -/
private theorem sqrt_log_card_quarterNet_le_aux {m : ℕ} (hm : 0 < m)
    {N : Finset (EuclideanSpace ℝ (Fin m))}
    (hcard : (N.card : ℝ≥0∞) ≤ (9 : ℝ≥0∞) ^ m) :
    Real.sqrt (Real.log (N.card + 2 : ℝ)) ≤ 4 * Real.sqrt m := by
  have hcardNat : N.card ≤ 9 ^ m := by exact_mod_cast hcard
  have hcardReal : (N.card + 2 : ℝ) ≤ 3 * (9 : ℝ) ^ m := by
    have hpowpos : 0 < 9 ^ m := pow_pos (by omega) _
    have hpowone : 1 ≤ 9 ^ m := hpowpos
    exact_mod_cast (calc
      N.card + 2 ≤ 9 ^ m + 2 := Nat.add_le_add_right hcardNat 2
      _ ≤ 3 * 9 ^ m := by omega)
  have hleftpos : (0 : ℝ) < N.card + 2 := by positivity
  have hrightpos : (0 : ℝ) < 3 * (9 : ℝ) ^ m := by positivity
  have hlog := Real.log_le_log hleftpos hcardReal
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog9 : Real.log (9 : ℝ) ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity),
    Real.log_pow] at hlog
  have hlogbound : Real.log (N.card + 2 : ℝ) ≤ 16 * m := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc
    Real.sqrt (Real.log (N.card + 2 : ℝ)) ≤ Real.sqrt (16 * (m : ℝ)) :=
      Real.sqrt_le_sqrt hlogbound
    _ = 4 * Real.sqrt m := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]

/-- Bounds the expected Haar-rotated net support by Gaussian width with the dimension and radius factors made explicit.

**Lean implementation helper.** -/
private theorem haar_net_support_expectation_le_aux {m n : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hdiam : 0 < finiteEuclideanDiameter T)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m))))
    (hNcard : (N.card : ℝ≥0∞) ≤ (9 : ℝ≥0∞) ^ m) :
    (∫ U, N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (HDP.Chapter5.orthogonalAction U
            (firstCoordinateEmbedding_aux hmn z)))
      ∂HDP.Chapter5.orthogonalHaarMeasure n) ≤
      2 * sphericalWidth T +
        8 * HDP.Chapter5.sphereConcentrationConstant *
          Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := HDP.Chapter5.orthogonalHaarMeasure n
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsProbabilityMeasure σ := by
    dsimp [σ]
    infer_instance
  let D := differenceFinset T T
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteGaussianSupport D
  let M : ℝ := sphericalWidth D
  have hD : D.Nonempty := differenceFinset_nonempty hT hT
  have hLip : LipschitzWith
      (⟨finiteEuclideanDiameter T, finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0) F :=
    finiteGaussianSupport_difference_lipschitz_aux T hT
  have hcenterSub := HDP.Chapter5.unitSphere_lipschitz_subGaussian_ambient
    n hn F
      (⟨finiteEuclideanDiameter T, finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0) hLip
  have hcenterPsi := HDP.Chapter5.unitSphere_lipschitz_concentration_ambient
    n hn F
      (⟨finiteEuclideanDiameter T, finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0) hLip
  have hM : M = ∫ θ : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1, F θ ∂σ := by
    rfl
  let z₀ : EuclideanSpace ℝ (Fin m) :=
    (quarterNet_nonempty_aux hm hN).choose
  have hz₀ : z₀ ∈ N := (quarterNet_nonempty_aux hm hN).choose_spec
  let idx : Fin (N.card + 2) → EuclideanSpace ℝ (Fin m) := fun i =>
    if hi : i.val < N.card then
      (N.equivFin.symm ⟨i.val, hi⟩ : N).1
    else z₀
  have hidx (i : Fin (N.card + 2)) : idx i ∈ N := by
    dsimp [idx]
    split_ifs with hi
    · exact (N.equivFin.symm ⟨i.val, hi⟩ : N).2
    · exact hz₀
  have hidxnorm (i : Fin (N.card + 2)) : ‖idx i‖ = 1 :=
    hN.1 (idx i) (hidx i)
  let v : Fin (N.card + 2) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := fun i =>
    ⟨firstCoordinateEmbedding_aux hmn (idx i), by
      simpa [Metric.mem_sphere, dist_zero_right,
        norm_firstCoordinateEmbedding_aux hmn] using hidxnorm i⟩
  let X : Fin (N.card + 2) →
      Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun i U =>
    F (HDP.Chapter5.orthogonalAction U
      (firstCoordinateEmbedding_aux hmn (idx i))) - M
  have hXeq (i : Fin (N.card + 2)) : X i =
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => F θ - M) ∘
        forwardOrthogonalSphereOrbit_aux (v i) := by
    funext U
    rfl
  have hvmp (i : Fin (N.card + 2)) : MeasurePreserving
      (forwardOrthogonalSphereOrbit_aux (v i)) μ σ :=
    ⟨measurable_forwardOrthogonalSphereOrbit_aux (v i),
      map_forwardOrthogonalSphereOrbit_aux hn (v i)⟩
  have hXm (i : Fin (N.card + 2)) : Measurable (X i) := by
    rw [hXeq]
    exact ((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const M).comp
      (measurable_forwardOrthogonalSphereOrbit_aux (v i))
  have hXsub (i : Fin (N.card + 2)) : HDP.SubGaussian (X i) μ := by
    rw [hXeq]
    have hcenterEq :
        (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => F θ - M) =
        (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          F θ - ∫ q : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1, F q ∂σ) := by
      funext θ
      rw [hM]
    rw [hcenterEq]
    exact subGaussian_comp_measurePreserving_aux _ (hvmp i) _
      ((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const _).aemeasurable
      hcenterSub
  let K : ℝ := HDP.Chapter5.sphereConcentrationConstant *
    finiteEuclideanDiameter T / Real.sqrt n
  have hK : 0 < K := by
    dsimp [K]
    have hsqrtn : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    exact div_pos
      (mul_pos HDP.Chapter5.sphereConcentrationConstant_pos hdiam) hsqrtn
  have hXpsi (i : Fin (N.card + 2)) : HDP.psi2Norm (X i) μ ≤ K := by
    rw [hXeq]
    have hcenterEq :
        (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => F θ - M) =
        (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          F θ - ∫ q : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1, F q ∂σ) := by
      funext θ
      rw [hM]
    have hcenterMeas : AEMeasurable
        (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          F θ - ∫ q : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1, F q ∂σ) σ :=
      ((hLip.continuous.measurable.comp measurable_subtype_coe).sub_const _).aemeasurable
    rw [hcenterEq,
      psi2Norm_comp_measurePreserving_aux _ (hvmp i) _ hcenterMeas]
    have hcenterPsi' := hcenterPsi
    change HDP.psi2Norm
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          F x - ∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            F y ∂σ) σ ≤ K at hcenterPsi'
    exact hcenterPsi'
  have hmax := HDP.expectation_max_le hXm hXsub hK hXpsi
  have hlog := sqrt_log_card_quarterNet_le_aux hm hNcard
  have hmaxBound :
      (∫ U, Finset.univ.sup' Finset.univ_nonempty (fun i => X i U) ∂μ) ≤
        8 * Real.sqrt m * K := by
    calc
      _ ≤ 2 * Real.sqrt (Real.log (N.card + 2 : ℝ)) * K := hmax
      _ ≤ 2 * (4 * Real.sqrt m) * K := by gcongr
      _ = 8 * Real.sqrt m * K := by ring
  let Y : EuclideanSpace ℝ (Fin m) →
      Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun z U =>
    F (HDP.Chapter5.orthogonalAction U
      (firstCoordinateEmbedding_aux hmn z))
  have hpoint (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z U) ≤
        M + Finset.univ.sup' Finset.univ_nonempty (fun i => X i U) := by
    apply Finset.sup'_le
    intro z hz
    let j : Fin N.card := N.equivFin ⟨z, hz⟩
    let i : Fin (N.card + 2) := ⟨j.val, by omega⟩
    have hi : i.val < N.card := j.isLt
    have hidxz : idx i = z := by
      simp only [idx, dif_pos hi]
      exact congrArg Subtype.val (N.equivFin.symm_apply_apply ⟨z, hz⟩)
    have hXi : X i U = Y z U - M := by
      simp only [X, Y, hidxz]
    have hle := Finset.le_sup' (fun k => X k U) (Finset.mem_univ i)
    rw [hXi] at hle
    linarith
  have hYmeas (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ N) :
      Measurable (Y z) := by
    let vz : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨firstCoordinateEmbedding_aux hmn z, by
        simpa [Metric.mem_sphere, dist_zero_right,
          norm_firstCoordinateEmbedding_aux hmn] using hN.1 z hz⟩
    have heq : Y z = F ∘ ((↑) : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 → EuclideanSpace ℝ (Fin n)) ∘
          forwardOrthogonalSphereOrbit_aux vz := by
      funext U
      rfl
    rw [heq]
    exact hLip.continuous.measurable.comp measurable_subtype_coe |>.comp
      (measurable_forwardOrthogonalSphereOrbit_aux vz)
  have hYint : Integrable
      (fun U => N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z U)) μ := by
    have hfun : Integrable (N.sup' (quarterNet_nonempty_aux hm hN)
        (fun z => Y z)) μ := by
      refine Finset.sup'_induction (quarterNet_nonempty_aux hm hN)
        (f := fun z => Y z) (p := fun f => Integrable f μ) ?_ ?_
      · intro f (hf : Integrable f μ) g (hg : Integrable g μ)
        exact hf.sup hg
      · intro z hz
        apply Integrable.of_bound (hYmeas z hz).aestronglyMeasurable
          (finiteEuclideanDiameter T)
        filter_upwards [] with U
        rw [Real.norm_eq_abs]
        dsimp [Y, F]
        rw [abs_of_nonneg]
        · calc
            finiteGaussianSupport D
                (HDP.Chapter5.orthogonalAction U
                  (firstCoordinateEmbedding_aux hmn z)) ≤
                ‖HDP.Chapter5.orthogonalAction U
                  (firstCoordinateEmbedding_aux hmn z)‖ *
                    finiteEuclideanDiameter T :=
              finiteGaussianSupport_difference_le_norm_mul_diameter T hT _
            _ = finiteEuclideanDiameter T := by
              rw [HDP.Chapter5.norm_orthogonalAction,
                norm_firstCoordinateEmbedding_aux hmn, hN.1 z hz, one_mul]
        · have hz0 : 0 ∈ D := by
            unfold D differenceFinset minkowskiSumFinset negFinset
            obtain ⟨x, hx⟩ := hT
            apply Finset.mem_image.mpr
            refine ⟨(x, -x), Finset.mem_product.mpr ⟨hx, ?_⟩, by simp⟩
            exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
          rw [finiteGaussianSupport_eq_sup' D hD]
          exact (show (0 : ℝ) = inner ℝ
            (HDP.Chapter5.orthogonalAction U
              (firstCoordinateEmbedding_aux hmn z)) 0 by simp) ▸
            Finset.le_sup' (fun w => inner ℝ
              (HDP.Chapter5.orthogonalAction U
                (firstCoordinateEmbedding_aux hmn z)) w) hz0
    convert hfun using 1
    funext U
    exact (Finset.sup'_apply (quarterNet_nonempty_aux hm hN) (fun z => Y z) U).symm
  have hXint (i : Fin (N.card + 2)) : Integrable (X i) μ := by
    have hmem := (hXsub i).memLp (hXm i).aemeasurable (le_refl (1 : ℝ))
    rw [ENNReal.ofReal_one] at hmem
    exact memLp_one_iff_integrable.mp hmem
  have hmaxXint : Integrable
      (fun U => Finset.univ.sup' Finset.univ_nonempty (fun i => X i U)) μ := by
    have hfun : Integrable
        (Finset.univ.sup' Finset.univ_nonempty (fun i => X i)) μ := by
      refine Finset.sup'_induction Finset.univ_nonempty
        (f := fun i => X i) (p := fun f => Integrable f μ) ?_ ?_
      · intro f (hf : Integrable f μ) g (hg : Integrable g μ)
        exact hf.sup hg
      · intro i hi
        exact hXint i
    convert hfun using 1
    funext U
    exact (Finset.sup'_apply Finset.univ_nonempty (fun i => X i) U).symm
  have hmain :
      (∫ U, N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z U) ∂μ) ≤
        M + 8 * Real.sqrt m * K := by
    calc
      _ ≤ ∫ U, (M + Finset.univ.sup' Finset.univ_nonempty
          (fun i => X i U)) ∂μ :=
        integral_mono hYint ((integrable_const M).add hmaxXint) hpoint
      _ = M + ∫ U, Finset.univ.sup' Finset.univ_nonempty
          (fun i => X i U) ∂μ := by
        rw [integral_add (integrable_const M) hmaxXint]
        simp
      _ ≤ M + 8 * Real.sqrt m * K := by
        simpa [add_comm] using add_le_add_left hmaxBound M
  have hMval : M = 2 * sphericalWidth T := by
    dsimp [M, D]
    exact sphericalWidth_difference_aux hn T hT
  have hsqrtdiv : Real.sqrt ((m : ℝ) / n) =
      Real.sqrt m / Real.sqrt n := by rw [Real.sqrt_div (by positivity)]
  have hterm : 8 * Real.sqrt m * K =
      8 * HDP.Chapter5.sphereConcentrationConstant *
        Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T := by
    dsimp [K]
    rw [hsqrtdiv]
    ring
  rw [hMval, hterm] at hmain
  simpa [Y, F, D, μ] using hmain

/-- Projected diameter along an orthogonal orbit never exceeds the original diameter.

**Lean implementation helper.** -/
private theorem grassmannProjectedDiameter_orbit_le_original_aux {m n : ℕ}
    (hmn : m ≤ n) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    grassmannProjectedDiameter (HDP.Chapter5.grassmannOrbit n m U) T ≤
      finiteEuclideanDiameter T := by
  rw [grassmannProjectedDiameter_eq_sup'_aux _ T hT]
  apply Finset.sup'_le
  intro p hp
  have hp' := Finset.mem_product.mp hp
  rw [HDP.Chapter5.randomProjection_grassmannOrbit_norm hmn]
  calc
    HDP.Chapter5.coordinateProjectionNorm hmn
        (HDP.Chapter5.orthogonalAction U⁻¹ (p.1 - p.2)) ≤
        ‖HDP.Chapter5.orthogonalAction U⁻¹ (p.1 - p.2)‖ :=
      HDP.Chapter5.norm_firstCoordinateRestriction_le hmn _
    _ = ‖p.1 - p.2‖ := HDP.Chapter5.norm_orthogonalAction _ _
    _ ≤ finiteEuclideanDiameter T :=
      norm_sub_le_finiteEuclideanDiameter T hT hp'.1 hp'.2

/-- Projected diameter along an orthogonal orbit is integrable under orthogonal Haar measure.

**Lean implementation helper.** -/
private theorem integrable_grassmannProjectedDiameter_orbit_aux {m n : ℕ}
    (hmn : m ≤ n) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) :
    Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      grassmannProjectedDiameter (HDP.Chapter5.grassmannOrbit n m U) T)
      (HDP.Chapter5.orthogonalHaarMeasure n) := by
  apply Integrable.of_bound
    (((measurable_grassmannProjectedDiameter_aux T).comp
      (HDP.Chapter5.continuous_grassmannOrbit n m).measurable).aestronglyMeasurable)
    (finiteEuclideanDiameter T)
  filter_upwards [] with U
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact grassmannProjectedDiameter_orbit_le_original_aux hmn T hT U
  · exact Metric.diam_nonneg

/-- The finite net-support functional along an orthogonal orbit is integrable under Haar measure.

**Lean implementation helper.** -/
private theorem integrable_haar_net_support_aux {m n : ℕ}
    (_hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m)))) :
    Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (HDP.Chapter5.orthogonalAction U
            (firstCoordinateEmbedding_aux hmn z))))
      (HDP.Chapter5.orthogonalHaarMeasure n) := by
  classical
  let D := differenceFinset T T
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteGaussianSupport D
  have hD : D.Nonempty := differenceFinset_nonempty hT hT
  have hLip : LipschitzWith
      (⟨finiteEuclideanDiameter T, finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0) F :=
    finiteGaussianSupport_difference_lipschitz_aux T hT
  let Y : EuclideanSpace ℝ (Fin m) →
      Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun z U =>
    F (HDP.Chapter5.orthogonalAction U
      (firstCoordinateEmbedding_aux hmn z))
  have hYmeas (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ N) :
      Measurable (Y z) := by
    let vz : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨firstCoordinateEmbedding_aux hmn z, by
        simpa [Metric.mem_sphere, dist_zero_right,
          norm_firstCoordinateEmbedding_aux hmn] using hN.1 z hz⟩
    have heq : Y z = F ∘ ((↑) : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin n)) 1 → EuclideanSpace ℝ (Fin n)) ∘
          forwardOrthogonalSphereOrbit_aux vz := by
      funext U
      rfl
    rw [heq]
    exact hLip.continuous.measurable.comp measurable_subtype_coe |>.comp
      (measurable_forwardOrthogonalSphereOrbit_aux vz)
  have hfun : Integrable
      (N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z))
      (HDP.Chapter5.orthogonalHaarMeasure n) := by
    refine Finset.sup'_induction (quarterNet_nonempty_aux hm hN)
      (f := fun z => Y z)
      (p := fun f => Integrable f (HDP.Chapter5.orthogonalHaarMeasure n)) ?_ ?_
    · intro f (hf : Integrable f _) g (hg : Integrable g _)
      exact hf.sup hg
    · intro z hz
      apply Integrable.of_bound (hYmeas z hz).aestronglyMeasurable
        (finiteEuclideanDiameter T)
      filter_upwards [] with U
      rw [Real.norm_eq_abs]
      dsimp [Y, F]
      rw [abs_of_nonneg]
      · calc
          finiteGaussianSupport D
              (HDP.Chapter5.orthogonalAction U
                (firstCoordinateEmbedding_aux hmn z)) ≤
              ‖HDP.Chapter5.orthogonalAction U
                (firstCoordinateEmbedding_aux hmn z)‖ *
                  finiteEuclideanDiameter T :=
            finiteGaussianSupport_difference_le_norm_mul_diameter T hT _
          _ = finiteEuclideanDiameter T := by
            rw [HDP.Chapter5.norm_orthogonalAction,
              norm_firstCoordinateEmbedding_aux hmn, hN.1 z hz, one_mul]
      · have hz0 : 0 ∈ D := by
          unfold D differenceFinset minkowskiSumFinset negFinset
          obtain ⟨x, hx⟩ := hT
          apply Finset.mem_image.mpr
          refine ⟨(x, -x), Finset.mem_product.mpr ⟨hx, ?_⟩, by simp⟩
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        rw [finiteGaussianSupport_eq_sup' D hD]
        exact (show (0 : ℝ) = inner ℝ
          (HDP.Chapter5.orthogonalAction U
            (firstCoordinateEmbedding_aux hmn z)) 0 by simp) ▸
          Finset.le_sup' (fun w => inner ℝ
            (HDP.Chapter5.orthogonalAction U
              (firstCoordinateEmbedding_aux hmn z)) w) hz0
  convert hfun using 1
  funext U
  exact (Finset.sup'_apply (quarterNet_nonempty_aux hm hN) (fun z => Y z) U).symm

/-- Bounds expected random-projection diameter above by Gaussian width with the dimension and projection-rank factors.

**Lean implementation helper.** -/
private theorem randomProjection_expectedDiameter_upper_aux :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        (∫ P, grassmannProjectedDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
          C * (sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) := by
  let C : ℝ := 16 * (1 + HDP.Chapter5.sphereConcentrationConstant)
  refine ⟨C, by
    dsimp [C]
    nlinarith [HDP.Chapter5.sphereConcentrationConstant_pos], ?_⟩
  intro m n hn hm hmn T hT
  have hwidth : 0 ≤ sphericalWidth T := sphericalWidth_nonneg T hT hn
  have hdiam : 0 ≤ finiteEuclideanDiameter T :=
    finiteEuclideanDiameter_nonneg T
  by_cases hdiam0 : finiteEuclideanDiameter T = 0
  · have hsub : (↑T : Set (EuclideanSpace ℝ (Fin n))).Subsingleton := by
      intro x hx y hy
      have hxy := norm_sub_le_finiteEuclideanDiameter T hT
        (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy)
      rw [hdiam0] at hxy
      have hz : ‖x - y‖ = 0 := le_antisymm hxy (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    have hproj (P : HDP.Chapter5.Grassmannian n m) :
        grassmannProjectedDiameter P T = 0 := by
      apply Metric.diam_subsingleton
      intro a ha b hb
      simp only [grassmannProjectedFinset, Finset.coe_image,
        Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [hsub hx hy]
    simp_rw [hproj]
    simp only [integral_zero]
    have hsqrt : 0 ≤ Real.sqrt ((m : ℝ) / n) := Real.sqrt_nonneg _
    have hC : 0 ≤ C := by
      dsimp [C]
      nlinarith [HDP.Chapter5.sphereConcentrationConstant_pos]
    exact mul_nonneg hC (add_nonneg hwidth (mul_nonneg hsqrt hdiam))
  · have hdiampos : 0 < finiteEuclideanDiameter T :=
      lt_of_le_of_ne hdiam (Ne.symm hdiam0)
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    obtain ⟨N, hN, hNcard⟩ := HDP.Chapter4.exists_quarter_unitSphereNet m
    have hmap :
        (∫ P, grassmannProjectedDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) =
        ∫ U, grassmannProjectedDiameter
          (HDP.Chapter5.grassmannOrbit n m U) T
          ∂HDP.Chapter5.orthogonalHaarMeasure n := by
      rw [HDP.Chapter5.grassmannHaarMeasure, integral_map
        (HDP.Chapter5.continuous_grassmannOrbit n m).measurable.aemeasurable]
      exact (measurable_grassmannProjectedDiameter_aux T).aestronglyMeasurable
    rw [hmap]
    let Z : Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun U =>
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (HDP.Chapter5.orthogonalAction U
            (firstCoordinateEmbedding_aux hmn z)))
    have hZint : Integrable Z (HDP.Chapter5.orthogonalHaarMeasure n) :=
      integrable_haar_net_support_aux hn hm hmn T hT N hN
    have hprojInt := integrable_grassmannProjectedDiameter_orbit_aux hmn T hT
    calc
      (∫ U, grassmannProjectedDiameter
          (HDP.Chapter5.grassmannOrbit n m U) T
          ∂HDP.Chapter5.orthogonalHaarMeasure n) ≤
          ∫ U, (4 / 3 : ℝ) * Z U
            ∂HDP.Chapter5.orthogonalHaarMeasure n := by
        apply integral_mono hprojInt (hZint.const_mul (4 / 3 : ℝ))
        intro U
        exact grassmannProjectedDiameter_orbit_le_net_aux hm hmn T hT N hN U
      _ = (4 / 3 : ℝ) * ∫ U, Z U
          ∂HDP.Chapter5.orthogonalHaarMeasure n := by
        rw [integral_const_mul]
      _ ≤ (4 / 3 : ℝ) * (2 * sphericalWidth T +
          8 * HDP.Chapter5.sphereConcentrationConstant *
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) := by
        gcongr
        exact haar_net_support_expectation_le_aux hn hm hmn T hT hdiampos
          N hN hNcard
      _ ≤ C * (sphericalWidth T +
          Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) := by
        have hsqrt : 0 ≤ Real.sqrt ((m : ℝ) / n) := Real.sqrt_nonneg _
        have hb : 0 ≤ Real.sqrt ((m : ℝ) / n) *
            finiteEuclideanDiameter T := mul_nonneg hsqrt hdiam
        have hc : 0 ≤ HDP.Chapter5.sphereConcentrationConstant :=
          le_of_lt HDP.Chapter5.sphereConcentrationConstant_pos
        dsimp [C]
        nlinarith [mul_nonneg hc hwidth, mul_nonneg hc hb]


/-- A quarter-net reduces projected diameter to finitely many support values. The proof uses a quarter-net of the projected unit sphere, Haar-orbit
uniformity, spherical Lipschitz concentration, and the finite sub-Gaussian
maximum inequality. The quantified constant is independent of both
dimensions and of `T`.

**Book Equation (7.22).** -/
theorem randomProjection_expectedDiameter_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        (∫ P, grassmannProjectedDiameter P T
          ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
          C * (sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) := by
  exact randomProjection_expectedDiameter_upper_aux

/-- The universal Gaussian absolute-value constant is at least one half.

**Lean implementation helper.** -/
private theorem half_le_gaussian_abs_constant_aux :
    (1 / 2 : ℝ) ≤ Real.sqrt 2 / Real.sqrt Real.pi := by
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [le_div_iff₀ hspi]
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspisq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hpi : Real.pi < 4 := Real.pi_lt_four
  nlinarith

/-- Spherical width of a symmetric diameter pair gives a universal lower bound proportional to the diameter.

**Lean implementation helper.** -/
private theorem sphericalWidth_diameterSymmetricPair_lower_aux {n : ℕ}
    (hn : 0 < n) (d : EuclideanSpace ℝ (Fin n)) :
    (1 / (2 * Real.sqrt n) : ℝ) * ‖d‖ ≤
      sphericalWidth (diameterSymmetricPairFinset d) := by
  let S := diameterSymmetricPairFinset d
  have hS : S.Nonempty := by simp [S, diameterSymmetricPairFinset]
  have hsw : 0 ≤ sphericalWidth S := sphericalWidth_nonneg S hS hn
  obtain ⟨C, hC, hradial⟩ := gaussianRadialMean_bounds
  have hrad := (hradial hn).2
  have heq := gaussianWidth_eq_radialMean_mul_sphericalWidth S hS hn
  have hgauss : (1 / 2 : ℝ) * ‖d‖ ≤ gaussianWidth S := by
    rw [show gaussianWidth S =
      (Real.sqrt 2 / Real.sqrt Real.pi) * ‖d‖ by
        dsimp [S]
        exact gaussianWidth_diameterSymmetricPair_eq d]
    exact mul_le_mul_of_nonneg_right half_le_gaussian_abs_constant_aux
      (norm_nonneg d)
  have hmain : (1 / 2 : ℝ) * ‖d‖ ≤
      Real.sqrt n * sphericalWidth S := by
    calc
      _ ≤ gaussianWidth S := hgauss
      _ = gaussianRadialMean n * sphericalWidth S := heq
      _ ≤ Real.sqrt n * sphericalWidth S :=
        mul_le_mul_of_nonneg_right hrad hsw
  have hsqrtn : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have halg : (1 / (2 * Real.sqrt n) : ℝ) * ‖d‖ =
      ((1 / 2 : ℝ) * ‖d‖) / Real.sqrt n := by
    field_simp
  rw [halg]
  exact (div_le_iff₀ hsqrtn).2 (by simpa [mul_comm] using hmain)

/-- Bounds a finite sum of absolute coordinates by square-root cardinality times the Euclidean norm.

**Lean implementation helper.** -/
private theorem sum_abs_le_sqrt_mul_norm_aux {m : ℕ}
    (x : EuclideanSpace ℝ (Fin m)) :
    (∑ i, |x i|) ≤ Real.sqrt m * ‖x‖ := by
  have h := HDP.Chapter1.cauchy_schwarz_vector
    (fun i : Fin m => |x i|) (fun _ : Fin m => (1 : ℝ))
  rw [HDP.Chapter1.dotProduct, HDP.Chapter1.lpNorm_two,
    HDP.Chapter1.lpNorm_two] at h
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, one_pow] at h
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)] at h
  have hx : Real.sqrt (∑ i : Fin m, |x i| ^ 2) = ‖x‖ := by
    rw [show (∑ i : Fin m, |x i| ^ 2) = ∑ i : Fin m, x i ^ 2 by
      apply Finset.sum_congr rfl
      intro i hi
      exact sq_abs (x i)]
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact Real.sqrt_sq (norm_nonneg x)
  rw [hx] at h
  simpa [mul_comm] using h

/-- Evaluates the expected absolute inner product along a Haar orthogonal orbit.

**Lean implementation helper.** -/
private theorem integral_abs_inner_forwardOrbit_aux {n : ℕ}
    (hn : 0 < n) (d : EuclideanSpace ℝ (Fin n))
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (∫ U, |inner ℝ d
        (HDP.Chapter5.orthogonalAction U (v : EuclideanSpace ℝ (Fin n)))|
      ∂HDP.Chapter5.orthogonalHaarMeasure n) =
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))|
        ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  let μ := HDP.Chapter5.orthogonalHaarMeasure n
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hmap := map_forwardOrthogonalSphereOrbit_aux hn v
  change (∫ U, |inner ℝ d ((forwardOrthogonalSphereOrbit_aux v U :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
        EuclideanSpace ℝ (Fin n))| ∂μ) = _
  rw [← hmap, integral_map
    (measurable_forwardOrthogonalSphereOrbit_aux v).aemeasurable]
  exact (by fun_prop : Measurable (fun θ : Metric.sphere
    (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))|)).aestronglyMeasurable

/-- The absolute inner product along a Haar orthogonal orbit is integrable.

**Lean implementation helper.** -/
private theorem integrable_abs_inner_forwardOrbit_aux {n : ℕ}
    (hn : 0 < n) (d : EuclideanSpace ℝ (Fin n))
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Integrable (fun U => |inner ℝ d
      (HDP.Chapter5.orthogonalAction U (v : EuclideanSpace ℝ (Fin n)))|)
      (HDP.Chapter5.orthogonalHaarMeasure n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  have hsphere : Integrable (fun θ : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))|)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
    apply Integrable.of_bound (by fun_prop : Measurable (fun θ : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))|)).aestronglyMeasurable
      ‖d‖
    filter_upwards [] with θ
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))| ≤
          ‖d‖ * ‖(θ : EuclideanSpace ℝ (Fin n))‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖d‖ := by rw [norm_coe_unitSphere, mul_one]
  have hmp : MeasurePreserving (forwardOrthogonalSphereOrbit_aux v)
      (HDP.Chapter5.orthogonalHaarMeasure n)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) :=
    ⟨measurable_forwardOrthogonalSphereOrbit_aux v,
      map_forwardOrthogonalSphereOrbit_aux hn v⟩
  change Integrable ((fun θ : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))|) ∘
      forwardOrthogonalSphereOrbit_aux v)
      (HDP.Chapter5.orthogonalHaarMeasure n)
  exact hmp.integrable_comp_of_integrable hsphere

/-- Every `z ∈ differenceFinset T T` can be written as `z = x - y` for some `x, y ∈ T`.

**Lean implementation helper.** -/
private theorem mem_differenceFinset_exists_aux
    {n : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n)))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ differenceFinset T T) :
    ∃ x ∈ T, ∃ y ∈ T, z = x - y := by
  unfold differenceFinset minkowskiSumFinset negFinset at hz
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  have hp' := Finset.mem_product.mp hp
  obtain ⟨y, hy, hpy⟩ := Finset.mem_image.mp hp'.2
  refine ⟨p.1, hp'.1, y, hy, ?_⟩
  rw [← hpz, ← hpy]
  exact sub_eq_add_neg _ _

/-- Bounds an orbit inner product by the projected distance of a corresponding pair.

**Lean implementation helper.** -/
private theorem inner_orbit_embedding_le_projectedPair_aux
    {m n : ℕ} (hmn : m ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (e : EuclideanSpace ℝ (Fin m)) (he : ‖e‖ = 1)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ
        (HDP.Chapter5.orthogonalAction U
          (firstCoordinateEmbedding_aux hmn e)) (x - y) ≤
      ‖HDP.Chapter5.randomProjection
        (HDP.Chapter5.grassmannOrbit n m U) (x - y)‖ := by
  rw [real_inner_comm, ← inner_rotatedCoordinateRestriction_aux]
  calc
    inner ℝ
        (HDP.Chapter5.firstCoordinateRestriction hmn
          (HDP.Chapter5.orthogonalAction U⁻¹ (x - y))) e ≤
        |inner ℝ
          (HDP.Chapter5.firstCoordinateRestriction hmn
            (HDP.Chapter5.orthogonalAction U⁻¹ (x - y))) e| := le_abs_self _
    _ ≤ ‖HDP.Chapter5.firstCoordinateRestriction hmn
          (HDP.Chapter5.orthogonalAction U⁻¹ (x - y))‖ * ‖e‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖HDP.Chapter5.firstCoordinateRestriction hmn
          (HDP.Chapter5.orthogonalAction U⁻¹ (x - y))‖ := by rw [he, mul_one]
    _ = _ := by
      rw [HDP.Chapter5.randomProjection_grassmannOrbit_norm hmn]
      rfl

/-- Bounds Gaussian support of a difference set using a pointwise bound on all representing pairs.

**Lean implementation helper.** -/
private theorem finiteGaussianSupport_difference_le_of_pair_aux
    {n : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (g : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hR : ∀ x ∈ T, ∀ y ∈ T, inner ℝ g (x - y) ≤ R) :
    finiteGaussianSupport (differenceFinset T T) g ≤ R := by
  rw [finiteGaussianSupport_eq_sup' _ (differenceFinset_nonempty hT hT)]
  apply Finset.sup'_le
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_differenceFinset_exists_aux T hz
  exact hR x hx y hy

set_option maxHeartbeats 500000 in
-- The proof expands a nested finite-support supremum over `T × T` and then
-- normalizes the orthogonal-action/projection identities for every pair; the
-- extra local budget is needed by those `Finset.sup'` and linear-algebra rewrites.
/-- Bounds Gaussian support of the difference set by Gaussian norm times projected diameter along the orbit.

**Lean implementation helper.** -/
private theorem finiteGaussianSupport_difference_le_projectedDiameter_orbit_aux
    {m n : ℕ} (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (e : EuclideanSpace ℝ (Fin m)) (he : ‖e‖ = 1)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    finiteGaussianSupport (differenceFinset T T)
        (HDP.Chapter5.orthogonalAction U
          (firstCoordinateEmbedding_aux hmn e)) ≤
      grassmannProjectedDiameter (HDP.Chapter5.grassmannOrbit n m U) T := by
  let g : EuclideanSpace ℝ (Fin n) :=
    HDP.Chapter5.orthogonalAction U (firstCoordinateEmbedding_aux hmn e)
  let f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ := fun q =>
    ‖HDP.Chapter5.randomProjection
      (HDP.Chapter5.grassmannOrbit n m U) (q.1 - q.2)‖
  let R : ℝ := (T.product T).sup' (hT.product hT) f
  change finiteGaussianSupport (differenceFinset T T) g ≤ _
  have hsupport : finiteGaussianSupport (differenceFinset T T) g ≤ R := by
    refine finiteGaussianSupport_difference_le_of_pair_aux T hT g R ?_
    intro x hx y hy
    have h₁ : inner ℝ g (x - y) ≤ f (x, y) := by
      dsimp [g]
      exact inner_orbit_embedding_le_projectedPair_aux hmn U e he x y
    have h₂ : f (x, y) ≤ R := by
      dsimp [R]
      exact Finset.le_sup' f
        (Finset.mem_product.mpr ⟨hx, hy⟩)
    exact h₁.trans h₂
  calc
    finiteGaussianSupport (differenceFinset T T) g ≤ R := hsupport
    _ = grassmannProjectedDiameter
        (HDP.Chapter5.grassmannOrbit n m U) T := by
      simpa [R, f] using
        (grassmannProjectedDiameter_eq_sup'_aux
          (HDP.Chapter5.grassmannOrbit n m U) T hT).symm

/-- Bounds expected projected diameter below by Gaussian width.

**Lean implementation helper.** -/
private theorem randomProjection_orbit_expectation_width_lower_aux {m n : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    2 * sphericalWidth T ≤
      ∫ U, grassmannProjectedDiameter
        (HDP.Chapter5.grassmannOrbit n m U) T
        ∂HDP.Chapter5.orthogonalHaarMeasure n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let e : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single ⟨0, hm⟩ 1
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨firstCoordinateEmbedding_aux hmn e, by
      simp [norm_firstCoordinateEmbedding_aux hmn, e]⟩
  let D := differenceFinset T T
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteGaussianSupport D
  have hFint : Integrable (F ∘ ((↑) : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 → EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
    simpa [Function.comp_def, F] using
      integrable_finiteGaussianSupport_unitSphere D hn
  have hvmp : MeasurePreserving (forwardOrthogonalSphereOrbit_aux v)
      (HDP.Chapter5.orthogonalHaarMeasure n)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) :=
    ⟨measurable_forwardOrthogonalSphereOrbit_aux v,
      map_forwardOrthogonalSphereOrbit_aux hn v⟩
  have hleft : Integrable (fun U => F
      (HDP.Chapter5.orthogonalAction U
        (firstCoordinateEmbedding_aux hmn e)))
      (HDP.Chapter5.orthogonalHaarMeasure n) := by
    convert hvmp.integrable_comp_of_integrable hFint using 1
    funext U
    rfl
  have hright := integrable_grassmannProjectedDiameter_orbit_aux hmn T hT
  have hInt :
      (∫ U, F (HDP.Chapter5.orthogonalAction U
          (firstCoordinateEmbedding_aux hmn e))
        ∂HDP.Chapter5.orthogonalHaarMeasure n) ≤
      ∫ U, grassmannProjectedDiameter
          (HDP.Chapter5.grassmannOrbit n m U) T
        ∂HDP.Chapter5.orthogonalHaarMeasure n := by
    apply integral_mono hleft hright
    intro U
    exact finiteGaussianSupport_difference_le_projectedDiameter_orbit_aux
      hmn T hT e (by simp [e]) U
  have hleftEq :
      (∫ U, F (HDP.Chapter5.orthogonalAction U
          (firstCoordinateEmbedding_aux hmn e))
        ∂HDP.Chapter5.orthogonalHaarMeasure n) = sphericalWidth D := by
    have hmap := map_forwardOrthogonalSphereOrbit_aux hn v
    rw [sphericalWidth, ← hmap, integral_map
      (measurable_forwardOrthogonalSphereOrbit_aux v).aemeasurable]
    · rfl
    · exact ((measurable_finiteGaussianSupport D).comp
        measurable_subtype_coe).aestronglyMeasurable
  rw [hleftEq, sphericalWidth_difference_aux hn T hT] at hInt
  exact hInt

/-- Bounds expected projected diameter below by the original diameter.

**Lean implementation helper.** -/
private theorem randomProjection_orbit_expectation_diameter_lower_aux {m n : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    (1 / 2 : ℝ) * Real.sqrt ((m : ℝ) / n) *
        finiteEuclideanDiameter T ≤
      ∫ U, grassmannProjectedDiameter
        (HDP.Chapter5.grassmannOrbit n m U) T
        ∂HDP.Chapter5.orthogonalHaarMeasure n := by
  classical
  have hdiamSup := finiteEuclideanDiameter_eq_sup' T hT
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_mem_eq_sup' (hT.product hT)
    (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖q.1 - q.2‖)
  let d := p.1 - p.2
  have hdiamEq : finiteEuclideanDiameter T = ‖d‖ := by
    rw [hdiamSup]
    simpa [d] using hpmax
  have hp' := Finset.mem_product.mp hp
  have hsqrtn : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrtm : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  let e : Fin m → EuclideanSpace ℝ (Fin m) := fun i =>
    EuclideanSpace.single i 1
  let v : Fin m → Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 := fun i =>
    ⟨firstCoordinateEmbedding_aux hmn (e i), by
      simp [norm_firstCoordinateEmbedding_aux hmn, e]⟩
  let A : Fin m → Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun i U =>
    |inner ℝ d (HDP.Chapter5.orthogonalAction U
      (firstCoordinateEmbedding_aux hmn (e i)))|
  have hAint (i : Fin m) : Integrable (A i)
      (HDP.Chapter5.orthogonalHaarMeasure n) := by
    simpa [A, v] using integrable_abs_inner_forwardOrbit_aux
      hn d (v i)
  have hsumInt : Integrable (fun U => (∑ i, A i U))
      (HDP.Chapter5.orthogonalHaarMeasure n) :=
    integrable_finsetSum Finset.univ (fun i hi => hAint i)
  have hlowerInt : Integrable (fun U => (1 / Real.sqrt m : ℝ) *
      ∑ i, A i U) (HDP.Chapter5.orthogonalHaarMeasure n) :=
    hsumInt.const_mul _
  have hright := integrable_grassmannProjectedDiameter_orbit_aux hmn T hT
  have hpoint (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      (1 / Real.sqrt m : ℝ) * ∑ i, A i U ≤
        grassmannProjectedDiameter (HDP.Chapter5.grassmannOrbit n m U) T := by
    let x := HDP.Chapter5.firstCoordinateRestriction hmn
      (HDP.Chapter5.orthogonalAction U⁻¹ d)
    have hsum : (∑ i, A i U) = ∑ i, |x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [A, x, e, d]
      rw [← inner_rotatedCoordinateRestriction_aux]
      simp [EuclideanSpace.inner_single_right]
    have hl1 := sum_abs_le_sqrt_mul_norm_aux x
    have hscaled : (1 / Real.sqrt m : ℝ) * ∑ i, A i U ≤ ‖x‖ := by
      rw [hsum]
      calc
        (1 / Real.sqrt m : ℝ) * ∑ i, |x i| ≤
            (1 / Real.sqrt m : ℝ) * (Real.sqrt m * ‖x‖) := by
          gcongr
        _ = ‖x‖ := by field_simp
    calc
      _ ≤ ‖x‖ := hscaled
      _ = ‖HDP.Chapter5.randomProjection
          (HDP.Chapter5.grassmannOrbit n m U) d‖ := by
        rw [HDP.Chapter5.randomProjection_grassmannOrbit_norm hmn]
        rfl
      _ ≤ grassmannProjectedDiameter
          (HDP.Chapter5.grassmannOrbit n m U) T := by
        rw [grassmannProjectedDiameter_eq_sup'_aux _ T hT]
        simpa [d] using (Finset.le_sup' (fun q =>
          ‖HDP.Chapter5.randomProjection
            (HDP.Chapter5.grassmannOrbit n m U) (q.1 - q.2)‖) hp)
  have hmono :
      ∫ U, (1 / Real.sqrt m : ℝ) * ∑ i, A i U
          ∂HDP.Chapter5.orthogonalHaarMeasure n ≤
        ∫ U, grassmannProjectedDiameter
          (HDP.Chapter5.grassmannOrbit n m U) T
          ∂HDP.Chapter5.orthogonalHaarMeasure n :=
    integral_mono hlowerInt hright hpoint
  have hAeq (i : Fin m) :
      (∫ U, A i U ∂HDP.Chapter5.orthogonalHaarMeasure n) =
        sphericalWidth (diameterSymmetricPairFinset d) := by
    rw [show sphericalWidth (diameterSymmetricPairFinset d) =
        ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ d (θ : EuclideanSpace ℝ (Fin n))|
          ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) by
      rw [sphericalWidth]
      simp_rw [finiteGaussianSupport_diameterSymmetricPair, real_inner_comm]]
    simpa [A, v] using integral_abs_inner_forwardOrbit_aux hn d (v i)
  have hpairLower := sphericalWidth_diameterSymmetricPair_lower_aux hn d
  have hsqrtdiv : Real.sqrt ((m : ℝ) / n) =
      Real.sqrt m / Real.sqrt n := by rw [Real.sqrt_div (by positivity)]
  have hmSq : (Real.sqrt (m : ℝ)) ^ 2 = m :=
    Real.sq_sqrt (by positivity)
  have hcalc :
      (1 / 2 : ℝ) * Real.sqrt ((m : ℝ) / n) * ‖d‖ ≤
        ∫ U, (1 / Real.sqrt m : ℝ) * ∑ i, A i U
          ∂HDP.Chapter5.orthogonalHaarMeasure n := by
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun i hi => hAint i)]
    simp_rw [hAeq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [hsqrtdiv]
    calc
      (1 / 2 : ℝ) * (Real.sqrt m / Real.sqrt n) * ‖d‖ =
          (1 / Real.sqrt m : ℝ) * (m *
            ((1 / (2 * Real.sqrt n) : ℝ) * ‖d‖)) := by
        field_simp
        rw [hmSq]
        ring
      _ ≤ (1 / Real.sqrt m : ℝ) *
          (m * sphericalWidth (diameterSymmetricPairFinset d)) := by
        gcongr
      _ = _ := rfl
  rw [hdiamEq]
  simpa [d] using hcalc.trans hmono

/-- Combines the Gaussian-width and diameter lower bounds for expected random-projection diameter.

**Lean implementation helper.** -/
private theorem randomProjection_expectedDiameter_lower_aux :
    ∃ c : ℝ, 0 < c ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        c * (sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) ≤
          ∫ P, grassmannProjectedDiameter P T
            ∂HDP.Chapter5.grassmannHaarMeasure n m := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro m n hn hm hmn T hT
  have hmap :
      (∫ P, grassmannProjectedDiameter P T
        ∂HDP.Chapter5.grassmannHaarMeasure n m) =
      ∫ U, grassmannProjectedDiameter
        (HDP.Chapter5.grassmannOrbit n m U) T
        ∂HDP.Chapter5.orthogonalHaarMeasure n := by
    rw [HDP.Chapter5.grassmannHaarMeasure, integral_map
      (HDP.Chapter5.continuous_grassmannOrbit n m).measurable.aemeasurable]
    exact (measurable_grassmannProjectedDiameter_aux T).aestronglyMeasurable
  rw [hmap]
  have hw := randomProjection_orbit_expectation_width_lower_aux
    hn hm hmn T hT
  have hd := randomProjection_orbit_expectation_diameter_lower_aux
    hn hm hmn T hT
  have hwidth := sphericalWidth_nonneg T hT hn
  have hterm : 0 ≤ Real.sqrt ((m : ℝ) / n) *
      finiteEuclideanDiameter T := mul_nonneg (Real.sqrt_nonneg _)
        (finiteEuclideanDiameter_nonneg T)
  nlinarith

/-- Matching lower bound for expected random-projection diameter. The spherical-width term follows from one fixed projected coordinate. The
diameter term averages the absolute values of all projected coordinates and
uses the finite-dimensional `ℓ¹`--`ℓ²` comparison together with Haar-orbit
uniformity.

**Book Exercise 7.26.** -/
theorem exercise_7_26_randomProjection_expectedDiameter_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        c * (sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) ≤
          ∫ P, grassmannProjectedDiameter P T
            ∂HDP.Chapter5.grassmannHaarMeasure n m := by
  exact randomProjection_expectedDiameter_lower_aux

/-- Expected diameter of a random `m`-dimensional projection is comparable to spherical width plus `sqrt(m/n)` times diameter. Two-sided finite form, obtained from the verified
upper theorem and promoted Exercise 7.26.

**Book Theorem 7.6.1.** -/
theorem randomProjection_expectedDiameter :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        c * (sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) ≤
          (∫ P, grassmannProjectedDiameter P T
            ∂HDP.Chapter5.grassmannHaarMeasure n m) ∧
        (∫ P, grassmannProjectedDiameter P T
            ∂HDP.Chapter5.grassmannHaarMeasure n m) ≤
          C * (sphericalWidth T +
            Real.sqrt ((m : ℝ) / n) * finiteEuclideanDiameter T) := by
  obtain ⟨C, hC, hupper⟩ := randomProjection_expectedDiameter_upper
  obtain ⟨c, hc, hlower⟩ :=
    exercise_7_26_randomProjection_expectedDiameter_lower
  refine ⟨c, C, hc, hC, ?_⟩
  intro m n hn hm hmn T hT
  exact ⟨hlower hn hm hmn T hT, hupper hn hm hmn T hT⟩

/-- Flattens a real matrix into a function on pairs of indices.

**Lean implementation helper.** -/
private def flattenMatrix_aux {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Fin m × Fin n → ℝ := fun p => A p.1 p.2

/-- Flattening a real matrix into its coordinate function is measurable.

**Lean implementation helper.** -/
private theorem flattenMatrix_measurable_aux {m n : ℕ} :
    Measurable (flattenMatrix_aux : Matrix (Fin m) (Fin n) ℝ →
      (Fin m × Fin n → ℝ)) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- Flattens a real matrix into the corresponding Euclidean vector.

**Lean implementation helper.** -/
private def flattenEuclidean_aux {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (flattenMatrix_aux A)

/-- Viewing a real matrix as a Euclidean coordinate vector is measurable.

**Lean implementation helper.** -/
private theorem flattenEuclidean_measurable_aux {m n : ℕ} :
    Measurable (flattenEuclidean_aux : Matrix (Fin m) (Fin n) ℝ →
      EuclideanSpace ℝ (Fin m × Fin n)) := by
  exact (WithLp.measurable_toLp 2 _).comp flattenMatrix_measurable_aux

/-- Flattening sends the Gaussian matrix measure to the product standard Gaussian coordinate measure.

**Lean implementation helper.** -/
private theorem flattenMatrix_map_gaussianMatrixMeasure_aux (m n : ℕ) :
    (gaussianMatrixMeasure m n).map flattenMatrix_aux =
      Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
  change (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map flattenMatrix_aux = _
  have h := Measure.infinitePi_map_curry_symm
    (fun _ : Fin m => fun _ : Fin n => gaussianReal 0 1)
  have hfun : flattenMatrix_aux =
      ⇑(MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm := rfl
  rw [hfun]
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  congr 2

/-- Euclidean flattening sends the Gaussian matrix measure to the standard Gaussian law on matrix coordinates.

**Lean implementation helper.** -/
private theorem flattenEuclidean_map_gaussianMatrixMeasure_aux (m n : ℕ) :
    (gaussianMatrixMeasure m n).map flattenEuclidean_aux =
      stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)) := by
  have hcomp : flattenEuclidean_aux =
      WithLp.toLp 2 ∘ (flattenMatrix_aux :
        Matrix (Fin m) (Fin n) ℝ → Fin m × Fin n → ℝ) := rfl
  rw [hcomp, ← Measure.map_map]
  · rw [flattenMatrix_map_gaussianMatrixMeasure_aux, map_pi_eq_stdGaussian]
  · exact WithLp.measurable_toLp 2 _
  · exact flattenMatrix_measurable_aux

/-- Defines the rectangular matrix representing contraction by a fixed vector.

**Lean implementation helper.** -/
private def contractionMatrix_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin n) (Fin m × Fin n) ℝ := fun j p =>
  if p.2 = j then z p.1 else 0

/-- Defines contraction by a fixed vector as a continuous linear map.

**Lean implementation helper.** -/
private def contractionCLM_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m × Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanLin (contractionMatrix_aux z)).toContinuousLinearMap

/-- Evaluating the contraction map gives the corresponding matrix-vector contraction.

**Lean implementation helper.** -/
private theorem contractionCLM_apply_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m × Fin n)) (j : Fin n) :
    contractionCLM_aux z x j = ∑ i : Fin m, z i * x (i, j) := by
  rw [show contractionCLM_aux z x =
      Matrix.toEuclideanLin (contractionMatrix_aux z) x by rfl,
    Matrix.toLpLin_apply]
  change (contractionMatrix_aux z).mulVec x.ofLp j = _
  rw [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [contractionMatrix_aux]
  calc
    (∑ i : Fin m, ∑ k : Fin n,
        (if k = j then z i else 0) * x (i, k)) =
        ∑ i : Fin m, z i * x (i, j) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp

/-- Defines the matrix representing the adjoint of the contraction map.

**Lean implementation helper.** -/
private def contractionAdjointMatrix_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m × Fin n) (Fin n) ℝ := fun p j =>
  if p.2 = j then z p.1 else 0

/-- Defines the adjoint contraction as a continuous linear map.

**Lean implementation helper.** -/
private def contractionAdjointCLM_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  (Matrix.toEuclideanLin
    (contractionAdjointMatrix_aux z)).toContinuousLinearMap

/-- Evaluating the adjoint contraction gives its explicit coordinate formula.

**Lean implementation helper.** -/
private theorem contractionAdjointCLM_apply_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin n)) (p : Fin m × Fin n) :
    contractionAdjointCLM_aux z u p = z p.1 * u p.2 := by
  rw [show contractionAdjointCLM_aux z u =
      Matrix.toEuclideanLin (contractionAdjointMatrix_aux z) u by rfl,
    Matrix.toLpLin_apply]
  change (contractionAdjointMatrix_aux z).mulVec u.ofLp p = _
  rw [Matrix.mulVec, dotProduct]
  simp [contractionAdjointMatrix_aux]

/-- The adjoint of the contraction map is the explicitly defined adjoint contraction.

**Lean implementation helper.** -/
private theorem contractionCLM_adjoint_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    (contractionCLM_aux (n := n) z).adjoint =
      contractionAdjointCLM_aux (n := n) z := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, Real.inner_apply,
    contractionAdjointCLM_apply_aux, contractionCLM_apply_aux]
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin n, u j * ∑ i : Fin m, z i * x (i, j)) =
        ∑ i : Fin m, ∑ j : Fin n, z i * u j * x (i, j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- For a unit contraction vector, the adjoint contraction preserves inner products.

**Lean implementation helper.** -/
private theorem inner_contractionAdjointCLM_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1)
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (contractionAdjointCLM_aux z u)
        (contractionAdjointCLM_aux z v) = inner ℝ u v := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    contractionAdjointCLM_apply_aux]
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : Fin m, ∑ j : Fin n, (z i * u j) * (z i * v j)) =
        (∑ i : Fin m, z i ^ 2) * (∑ j : Fin n, u j * v j) := by
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ j : Fin n, u j * v j := by
      rw [← EuclideanSpace.real_norm_sq_eq, hz]
      norm_num

/-- Contraction sends a standard Gaussian vector to the centered Gaussian law with the induced covariance.

**Lean implementation helper.** -/
private theorem map_contractionCLM_stdGaussian_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))).map
        (contractionCLM_aux z) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))
  let ν := μ.map (contractionCLM_aux z)
  letI : IsGaussian ν :=
    (IsGaussian.hasGaussianLaw_id (μ := μ)).map_fun
      (contractionCLM_aux z) |>.isGaussian_map
  apply IsGaussian.ext
  · change (∫ x, x ∂μ.map (contractionCLM_aux z)) =
      ∫ x, x ∂stdGaussian (EuclideanSpace ℝ (Fin n))
    rw [ContinuousLinearMap.integral_id_map (μ := μ)
        IsGaussian.integrable_id (contractionCLM_aux z),
      integral_id_stdGaussian, map_zero, integral_id_stdGaussian]
  · ext u v
    change covarianceBilin (μ.map (contractionCLM_aux z)) u v =
      covarianceBilin (stdGaussian (EuclideanSpace ℝ (Fin n))) u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, covarianceBilin_stdGaussian]
    change inner ℝ ((contractionCLM_aux z).adjoint u)
        ((contractionCLM_aux z).adjoint v) = inner ℝ u v
    rw [contractionCLM_adjoint_aux]
    exact inner_contractionAdjointCLM_aux z hz u v

/-- Transposes matrix coordinates after unflattening a coordinate function.

**Lean implementation helper.** -/
private def matrixTransposeCoordinates_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ := fun j =>
  ∑ i : Fin m, z i * G i j

/-- Transposing an unflattened matrix in coordinate-function form is measurable.

**Lean implementation helper.** -/
private theorem matrixTransposeCoordinates_measurable_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    Measurable (matrixTransposeCoordinates_aux z :
      Matrix (Fin m) (Fin n) ℝ → Fin n → ℝ) := by
  apply measurable_pi_lambda
  intro j
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.mul
    ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- For a matrix `G` and vector `z`, the Euclidean transpose map has coordinate `j` equal to `∑ i, z i * G i j`.

**Lean implementation helper.** -/
private def matrixTransposeEuclidean_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (matrixTransposeCoordinates_aux z G)

/-- The Euclidean transpose map agrees with transposing after unflattening coordinates.

**Lean implementation helper.** -/
private theorem matrixTransposeEuclidean_eq_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin n) ℝ) :
    matrixTransposeEuclidean_aux z G =
      contractionCLM_aux z (flattenEuclidean_aux G) := by
  ext j
  rw [contractionCLM_apply_aux]
  rfl

/-- Applying the Euclidean transpose map to a Gaussian matrix produces a standard Gaussian vector.

**Lean implementation helper.** -/
private theorem map_matrixTransposeEuclidean_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1) :
    (gaussianMatrixMeasure m n).map (matrixTransposeEuclidean_aux z) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have hfun : (matrixTransposeEuclidean_aux (n := n) z) =
      (contractionCLM_aux (n := n) z) ∘
        (flattenEuclidean_aux : Matrix (Fin m) (Fin n) ℝ →
          EuclideanSpace ℝ (Fin m × Fin n)) := by
    funext G
    exact matrixTransposeEuclidean_eq_aux z G
  rw [hfun, ← Measure.map_map]
  · rw [flattenEuclidean_map_gaussianMatrixMeasure_aux,
      map_contractionCLM_stdGaussian_aux z hz]
  · exact (contractionCLM_aux z).continuous.measurable
  · exact flattenEuclidean_measurable_aux

/-- Applying the coordinate transpose map to a Gaussian matrix produces independent standard Gaussian coordinates.

**Lean implementation helper.** -/
private theorem map_matrixTransposeCoordinates_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1) :
    (gaussianMatrixMeasure m n).map (matrixTransposeCoordinates_aux z) =
      HDP.Chapter5.gaussianPiMeasure n := by
  apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp]
  calc
    Measure.map (WithLp.toLp 2)
        (Measure.map (matrixTransposeCoordinates_aux z)
          (gaussianMatrixMeasure m n)) =
        Measure.map (WithLp.toLp 2 ∘ matrixTransposeCoordinates_aux z)
          (gaussianMatrixMeasure m n) :=
      Measure.map_map (WithLp.measurable_toLp 2 _)
        (matrixTransposeCoordinates_measurable_aux z)
    _ = Measure.map (matrixTransposeEuclidean_aux z)
          (gaussianMatrixMeasure m n) := by rfl
    _ = stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      map_matrixTransposeEuclidean_aux z hz
    _ = Measure.map (WithLp.toLp 2) (HDP.Chapter5.gaussianPiMeasure n) := by
      exact (map_pi_eq_stdGaussian (ι := Fin n)).symm

/-- Defines the operator-norm distance between the images of two index points under a matrix.

**Lean implementation helper.** -/
private def matrixPairDistance_aux {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖G.toEuclideanLin (p.1 - p.2)‖

set_option maxHeartbeats 1000000 in
-- Converting the diameter to a `Finset.sup'` requires two set-image witness
-- eliminations followed by large Euclidean matrix/norm simplifications in both
-- inequality directions; this local budget is confined to that normalization.
/-- Expresses matrix-image diameter as the supremum of pairwise operator-norm distances.

**Lean implementation helper.** -/
private theorem matrixImageDiameter_eq_sup'_aux {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    matrixImageDiameter G T =
      (T.product T).sup' (hT.product hT) (matrixPairDistance_aux G) := by
  classical
  let f := matrixPairDistance_aux G
  let R := (T.product T).sup' (hT.product hT) f
  have hR : 0 ≤ R := by
    let x := hT.choose
    have hx : x ∈ T := hT.choose_spec
    change 0 ≤ (T.product T).sup' (hT.product hT) f
    have hle := Finset.le_sup' f
      (show (x, x) ∈ T.product T by simp [hx])
    simpa [f, matrixPairDistance_aux] using hle
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le hR
    intro a ha b hb
    simp only [matrixImageFinset, Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [dist_eq_norm, ← map_sub]
    change matrixPairDistance_aux G (x, y) ≤ R
    exact Finset.le_sup' f (Finset.mem_product.mpr ⟨hx, hy⟩)
  · apply Finset.sup'_le
    intro p hp
    have hp' := Finset.mem_product.mp hp
    change matrixPairDistance_aux G p ≤ _
    dsimp [matrixPairDistance_aux]
    rw [map_sub, ← dist_eq_norm]
    apply Metric.dist_le_diam_of_mem
    · exact (matrixImageFinset G T).finite_toSet.isBounded
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.1, hp'.1, rfl⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.2, hp'.2, rfl⟩)

/-- Matrix-image diameter is measurable as a function of the matrix.

**Lean implementation helper.** -/
private theorem measurable_matrixImageDiameter_aux {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) :
    Measurable (fun G : Matrix (Fin m) (Fin n) ℝ =>
      matrixImageDiameter G T) := by
  classical
  by_cases hT : T.Nonempty
  · rw [show (fun G : Matrix (Fin m) (Fin n) ℝ =>
        matrixImageDiameter G T) =
      (T.product T).sup' (hT.product hT) (fun p =>
        fun G : Matrix (Fin m) (Fin n) ℝ =>
          matrixPairDistance_aux G p) by
      funext G
      rw [matrixImageDiameter_eq_sup'_aux G T hT]
      exact (Finset.sup'_apply (hT.product hT) (fun p =>
        fun G : Matrix (Fin m) (Fin n) ℝ =>
          matrixPairDistance_aux G p) G).symm]
    apply Finset.measurable_sup'
    intro p hp
    dsimp [matrixPairDistance_aux]
    apply Measurable.norm
    have hcoord : Measurable (fun G : Matrix (Fin m) (Fin n) ℝ =>
        fun i : Fin m => ∑ j : Fin n, G i j * (p.1 - p.2) j) := by
      apply measurable_pi_lambda
      intro i
      apply Finset.measurable_sum
      intro j hj
      exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
    have heq : (fun G : Matrix (Fin m) (Fin n) ℝ =>
        G.toEuclideanLin (p.1 - p.2)) =
        (WithLp.toLp 2) ∘ (fun G =>
          fun i : Fin m => ∑ j : Fin n, G i j * (p.1 - p.2) j) := by
      funext G
      rw [Matrix.toLpLin_apply]
      rfl
    rw [heq]
    exact (WithLp.measurable_toLp 2 _).comp hcoord
  · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    simp [matrixImageDiameter, matrixImageFinset]

/-- Moves matrix multiplication across the Euclidean inner product by transposing the matrix.

**Lean implementation helper.** -/
private theorem inner_matrix_mul_eq_transpose_aux {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (G.toEuclideanLin d) z =
      inner ℝ d (matrixTransposeEuclidean_aux z G) := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    Matrix.toLpLin_apply]
  change (∑ i : Fin m, (∑ j : Fin n, G i j * d j) * z i) =
    ∑ j : Fin n, d j * ∑ i : Fin m, z i * G i j
  calc
    (∑ i : Fin m, (∑ j : Fin n, G i j * d j) * z i) =
        ∑ i : Fin m, ∑ j : Fin n, (G i j * d j) * z i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ i : Fin m, (G i j * d j) * z i :=
      Finset.sum_comm
    _ = ∑ j : Fin n, d j * ∑ i : Fin m, z i * G i j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Bounds matrix-image diameter by twice a finite Gaussian support functional over a sphere net.

**Lean implementation helper.** -/
private theorem matrixImageDiameter_le_netSupport_aux {m n : ℕ}
    (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m))))
    (G : Matrix (Fin m) (Fin n) ℝ) :
    matrixImageDiameter G T ≤
      (4 / 3 : ℝ) * N.sup' (by
        -- reproduced locally because the production lemma is private
        let i : Fin m := ⟨0, hm⟩
        let u : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
        have hu : ‖u‖ = 1 := by simp [u]
        obtain ⟨z, hz, _⟩ := hN.2 u hu
        exact ⟨z, hz⟩) (fun z =>
          finiteGaussianSupport (differenceFinset T T)
            (matrixTransposeEuclidean_aux z G)) := by
  let hNne : N.Nonempty := by
    let i : Fin m := ⟨0, hm⟩
    let u : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
    have hu : ‖u‖ = 1 := by simp [u]
    obtain ⟨z, hz, _⟩ := hN.2 u hu
    exact ⟨z, hz⟩
  change matrixImageDiameter G T ≤
      (4 / 3 : ℝ) * N.sup' hNne (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (matrixTransposeEuclidean_aux z G))
  rw [matrixImageDiameter_eq_sup'_aux G T hT]
  apply Finset.sup'_le
  intro p hp
  have hp' := Finset.mem_product.mp hp
  let q := G.toEuclideanLin (p.1 - p.2)
  calc
    ‖q‖ ≤ (4 / 3 : ℝ) * N.sup' hNne
        (fun z => |inner ℝ q z|) := by
      -- same elementary quarter-net estimate as in the Haar proof
      by_cases hq : q = 0
      · simp [hq]
      · let u : EuclideanSpace ℝ (Fin m) := ‖q‖⁻¹ • q
        have hqn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
        have hu : ‖u‖ = 1 := by simp [u, norm_smul, hqn]
        obtain ⟨z, hzN, huz⟩ := hN.2 u hu
        have hqu : inner ℝ q u = ‖q‖ := by
          rw [show u = ‖q‖⁻¹ • q by rfl, inner_smul_right,
            real_inner_self_eq_norm_sq]
          field_simp [hqn]
        have hsplit : inner ℝ q u = inner ℝ q z + inner ℝ q (u - z) := by
          rw [inner_sub_right]
          ring
        have herr : |inner ℝ q (u - z)| ≤ ‖q‖ / 4 := by
          calc
            |inner ℝ q (u - z)| ≤ ‖q‖ * ‖u - z‖ :=
              abs_real_inner_le_norm _ _
            _ ≤ ‖q‖ * (1 / 4 : ℝ) :=
              mul_le_mul_of_nonneg_left huz (norm_nonneg q)
            _ = ‖q‖ / 4 := by ring
        have hzsup : |inner ℝ q z| ≤
            N.sup' hNne (fun w => |inner ℝ q w|) :=
          Finset.le_sup' (fun w => |inner ℝ q w|) hzN
        have hmain : ‖q‖ ≤
            N.sup' hNne (fun w => |inner ℝ q w|) + ‖q‖ / 4 := by
          calc
            ‖q‖ = inner ℝ q z + inner ℝ q (u - z) := by rw [← hsplit, hqu]
            _ ≤ |inner ℝ q z| + |inner ℝ q (u - z)| :=
              add_le_add (le_abs_self _) (le_abs_self _)
            _ ≤ N.sup' hNne (fun w => |inner ℝ q w|) + ‖q‖ / 4 :=
              add_le_add hzsup herr
        nlinarith
    _ ≤ (4 / 3 : ℝ) * N.sup' hNne (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (matrixTransposeEuclidean_aux z G)) := by
      gcongr
      rw [inner_matrix_mul_eq_transpose_aux]
      rw [real_inner_comm]
      -- use symmetry of `T-T`
      have hzmem : p.1 - p.2 ∈ differenceFinset T T := by
        unfold differenceFinset minkowskiSumFinset negFinset
        apply Finset.mem_image.mpr
        refine ⟨(p.1, -p.2), Finset.mem_product.mpr ⟨hp'.1, ?_⟩,
          (sub_eq_add_neg _ _).symm⟩
        exact Finset.mem_image.mpr ⟨p.2, hp'.2, rfl⟩
      have hD := differenceFinset_nonempty hT hT
      rw [finiteGaussianSupport_eq_sup' _ hD, abs_le]
      constructor
      · have hneg : -(p.1 - p.2) ∈ differenceFinset T T := by
          simpa [neg_sub] using (show p.2 - p.1 ∈ differenceFinset T T by
            unfold differenceFinset minkowskiSumFinset negFinset
            apply Finset.mem_image.mpr
            refine ⟨(p.2, -p.1), Finset.mem_product.mpr ⟨hp'.2, ?_⟩,
              (sub_eq_add_neg _ _).symm⟩
            exact Finset.mem_image.mpr ⟨p.1, hp'.1, rfl⟩)
        have hle := Finset.le_sup' (fun w => inner ℝ
          (matrixTransposeEuclidean_aux z G) w) hneg
        simp only [inner_neg_right] at hle
        linarith
      · exact Finset.le_sup' (fun w => inner ℝ
          (matrixTransposeEuclidean_aux z G) w) hzmem

/-- For fixed `z`, the Euclidean transpose map `G ↦ matrixTransposeEuclidean_aux z G` is measurable.

**Lean implementation helper.** -/
private theorem matrixTransposeEuclidean_measurable_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) :
    Measurable (matrixTransposeEuclidean_aux z :
      Matrix (Fin m) (Fin n) ℝ → EuclideanSpace ℝ (Fin n)) := by
  exact (WithLp.measurable_toLp 2 _).comp
    (matrixTransposeCoordinates_measurable_aux z)

/-- Bounds the expected Gaussian net support by the product of expected operator norm and expected Gaussian norm.

**Lean implementation helper.** -/
private theorem gaussianNetSupport_expectation_le_aux {m n : ℕ}
    (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (hdiam : 0 < finiteEuclideanDiameter T)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m))))
    (hNcard : (N.card : ℝ≥0∞) ≤ (9 : ℝ≥0∞) ^ m) :
    (∫ G, N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (matrixTransposeEuclidean_aux z G))
      ∂gaussianMatrixMeasure m n) ≤
      2 * gaussianWidth T +
        16 * Real.sqrt 5 * Real.sqrt m * finiteEuclideanDiameter T := by
  classical
  let μ := gaussianMatrixMeasure m n
  let γ := HDP.Chapter5.gaussianPiMeasure n
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    exact Measure.pi.instIsProbabilityMeasure _
  letI : IsProbabilityMeasure γ := by
    dsimp [γ]
    infer_instance
  let D := differenceFinset T T
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteGaussianSupport D
  let M : ℝ := gaussianWidth D
  have hD : D.Nonempty := differenceFinset_nonempty hT hT
  have hLip : LipschitzWith
      (⟨finiteEuclideanDiameter T, finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0) F :=
    finiteGaussianSupport_difference_lipschitz_aux T hT
  have hconc := HDP.Chapter5.gaussian_lipschitz_concentration n F
    (⟨finiteEuclideanDiameter T, finiteEuclideanDiameter_nonneg T⟩ : ℝ≥0) hLip
  have hM : M = ∫ y : Fin n → ℝ, F (WithLp.toLp 2 y) ∂γ := by
    have hLaw : HasLaw (WithLp.toLp 2)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) γ :=
      ⟨(WithLp.measurable_toLp 2 _).aemeasurable,
        map_pi_eq_stdGaussian⟩
    have h := hLaw.integral_comp
      (measurable_finiteGaussianSupport D).aestronglyMeasurable
    simpa [M, F, gaussianWidth] using h.symm
  let z₀ : EuclideanSpace ℝ (Fin m) :=
    (quarterNet_nonempty_aux hm hN).choose
  have hz₀ : z₀ ∈ N := (quarterNet_nonempty_aux hm hN).choose_spec
  let idx : Fin (N.card + 2) → EuclideanSpace ℝ (Fin m) := fun i =>
    if hi : i.val < N.card then
      (N.equivFin.symm ⟨i.val, hi⟩ : N).1
    else z₀
  have hidx (i : Fin (N.card + 2)) : idx i ∈ N := by
    dsimp [idx]
    split_ifs with hi
    · exact (N.equivFin.symm ⟨i.val, hi⟩ : N).2
    · exact hz₀
  have hidxnorm (i : Fin (N.card + 2)) : ‖idx i‖ = 1 :=
    hN.1 (idx i) (hidx i)
  let X : Fin (N.card + 2) → Matrix (Fin m) (Fin n) ℝ → ℝ := fun i G =>
    F (matrixTransposeEuclidean_aux (idx i) G) - M
  have hmpCoord (i : Fin (N.card + 2)) : MeasurePreserving
      (matrixTransposeCoordinates_aux (idx i)) μ γ :=
    ⟨matrixTransposeCoordinates_measurable_aux (idx i),
      map_matrixTransposeCoordinates_aux (idx i) (hidxnorm i)⟩
  have hXeq (i : Fin (N.card + 2)) : X i =
      HDP.Chapter5.gaussianCentered F ∘
        matrixTransposeCoordinates_aux (idx i) := by
    funext G
    simp only [X, Function.comp_apply, HDP.Chapter5.gaussianCentered]
    rw [← hM]
    rfl
  have hXm (i : Fin (N.card + 2)) : Measurable (X i) := by
    rw [hXeq]
    exact (hLip.continuous.measurable.comp
      (WithLp.measurable_toLp 2 _)).sub_const _ |>.comp
        (matrixTransposeCoordinates_measurable_aux (idx i))
  have hXsub (i : Fin (N.card + 2)) : HDP.SubGaussian (X i) μ := by
    rw [hXeq]
    exact subGaussian_comp_measurePreserving_aux _ (hmpCoord i) _
      ((hLip.continuous.measurable.comp
        (WithLp.measurable_toLp 2 _)).sub_const _).aemeasurable hconc.1
  let K : ℝ := 2 * Real.sqrt 5 * finiteEuclideanDiameter T
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hXpsi (i : Fin (N.card + 2)) : HDP.psi2Norm (X i) μ ≤ K := by
    rw [hXeq, psi2Norm_comp_measurePreserving_aux _ (hmpCoord i)]
    · exact hconc.2
    · exact ((hLip.continuous.measurable.comp
        (WithLp.measurable_toLp 2 _)).sub_const _).aemeasurable
  have hmax := HDP.expectation_max_le hXm hXsub hK hXpsi
  have hlog := sqrt_log_card_quarterNet_le_aux hm hNcard
  have hmaxBound :
      (∫ G, Finset.univ.sup' Finset.univ_nonempty (fun i => X i G) ∂μ) ≤
        16 * Real.sqrt 5 * Real.sqrt m * finiteEuclideanDiameter T := by
    calc
      _ ≤ 2 * Real.sqrt (Real.log (N.card + 2 : ℝ)) * K := hmax
      _ ≤ 2 * (4 * Real.sqrt m) * K := by gcongr
      _ = 16 * Real.sqrt 5 * Real.sqrt m * finiteEuclideanDiameter T := by
        dsimp [K]
        ring
  let Y : EuclideanSpace ℝ (Fin m) →
      Matrix (Fin m) (Fin n) ℝ → ℝ := fun z G =>
    F (matrixTransposeEuclidean_aux z G)
  have hpoint (G : Matrix (Fin m) (Fin n) ℝ) :
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z G) ≤
        M + Finset.univ.sup' Finset.univ_nonempty (fun i => X i G) := by
    apply Finset.sup'_le
    intro z hz
    let j : Fin N.card := N.equivFin ⟨z, hz⟩
    let i : Fin (N.card + 2) := ⟨j.val, by omega⟩
    have hi : i.val < N.card := j.isLt
    have hidxz : idx i = z := by
      simp only [idx, dif_pos hi]
      exact congrArg Subtype.val (N.equivFin.symm_apply_apply ⟨z, hz⟩)
    have hXi : X i G = Y z G - M := by simp only [X, Y, hidxz]
    have hle := Finset.le_sup' (fun k => X k G) (Finset.mem_univ i)
    rw [hXi] at hle
    linarith
  have hYint (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ N) :
      Integrable (Y z) μ := by
    have hmp : MeasurePreserving (matrixTransposeEuclidean_aux z) μ
        (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
      ⟨matrixTransposeEuclidean_measurable_aux z,
        map_matrixTransposeEuclidean_aux z (hN.1 z hz)⟩
    change Integrable (F ∘ matrixTransposeEuclidean_aux z) μ
    exact hmp.integrable_comp_of_integrable (integrable_finiteGaussianSupport D)
  have hYsupInt : Integrable
      (fun G => N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z G)) μ := by
    have hfun : Integrable
        (N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z)) μ := by
      refine Finset.sup'_induction (quarterNet_nonempty_aux hm hN)
        (f := fun z => Y z) (p := fun f => Integrable f μ) ?_ ?_
      · intro f (hf : Integrable f μ) g (hg : Integrable g μ)
        exact hf.sup hg
      · intro z hz
        exact hYint z hz
    convert hfun using 1
    funext G
    exact (Finset.sup'_apply (quarterNet_nonempty_aux hm hN) (fun z => Y z) G).symm
  have hXint (i : Fin (N.card + 2)) : Integrable (X i) μ := by
    have hmem := (hXsub i).memLp (hXm i).aemeasurable (le_refl (1 : ℝ))
    rw [ENNReal.ofReal_one] at hmem
    exact memLp_one_iff_integrable.mp hmem
  have hmaxInt : Integrable
      (fun G => Finset.univ.sup' Finset.univ_nonempty (fun i => X i G)) μ := by
    have hfun : Integrable
        (Finset.univ.sup' Finset.univ_nonempty (fun i => X i)) μ := by
      refine Finset.sup'_induction Finset.univ_nonempty
        (f := fun i => X i) (p := fun f => Integrable f μ) ?_ ?_
      · intro f (hf : Integrable f μ) g (hg : Integrable g μ)
        exact hf.sup hg
      · intro i hi
        exact hXint i
    convert hfun using 1
    funext G
    exact (Finset.sup'_apply Finset.univ_nonempty (fun i => X i) G).symm
  have hmain :
      (∫ G, N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z G) ∂μ) ≤
        M + 16 * Real.sqrt 5 * Real.sqrt m * finiteEuclideanDiameter T := by
    calc
      _ ≤ ∫ G, (M + Finset.univ.sup' Finset.univ_nonempty
          (fun i => X i G)) ∂μ :=
        integral_mono hYsupInt ((integrable_const M).add hmaxInt) hpoint
      _ = M + ∫ G, Finset.univ.sup' Finset.univ_nonempty
          (fun i => X i G) ∂μ := by
        rw [integral_add (integrable_const M) hmaxInt]
        simp
      _ ≤ M + 16 * Real.sqrt 5 * Real.sqrt m * finiteEuclideanDiameter T := by
        simpa [add_comm] using add_le_add_left hmaxBound M
  have hMval : M = 2 * gaussianWidth T := by
    dsimp [M, D]
    rw [gaussianWidth_difference T T hT hT]
    ring
  rw [hMval] at hmain
  simpa [Y, F, D, μ] using hmain

/-- The Gaussian support functional over the finite net is integrable.

**Lean implementation helper.** -/
private theorem integrable_gaussianNetSupport_aux {m n : ℕ}
    (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (_hT : T.Nonempty)
    (N : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : HDP.IsUnitSphereNet (1 / 4 : ℝ)
      (↑N : Set (EuclideanSpace ℝ (Fin m)))) :
    Integrable (fun G : Matrix (Fin m) (Fin n) ℝ =>
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (matrixTransposeEuclidean_aux z G)))
      (gaussianMatrixMeasure m n) := by
  classical
  let μ := gaussianMatrixMeasure m n
  let D := differenceFinset T T
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteGaussianSupport D
  let Y : EuclideanSpace ℝ (Fin m) →
      Matrix (Fin m) (Fin n) ℝ → ℝ := fun z G =>
    F (matrixTransposeEuclidean_aux z G)
  have hYint (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ N) :
      Integrable (Y z) μ := by
    have hmp : MeasurePreserving (matrixTransposeEuclidean_aux z) μ
        (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
      ⟨matrixTransposeEuclidean_measurable_aux z,
        map_matrixTransposeEuclidean_aux z (hN.1 z hz)⟩
    change Integrable (F ∘ matrixTransposeEuclidean_aux z) μ
    exact hmp.integrable_comp_of_integrable (integrable_finiteGaussianSupport D)
  have hfun : Integrable
      (N.sup' (quarterNet_nonempty_aux hm hN) (fun z => Y z)) μ := by
    refine Finset.sup'_induction (quarterNet_nonempty_aux hm hN)
      (f := fun z => Y z) (p := fun f => Integrable f μ) ?_ ?_
    · intro f (hf : Integrable f μ) g (hg : Integrable g μ)
      exact hf.sup hg
    · intro z hz
      exact hYint z hz
  convert hfun using 1
  funext G
  exact (Finset.sup'_apply (quarterNet_nonempty_aux hm hN) (fun z => Y z) G).symm

/-- Matrix-image diameter is integrable under the standard Gaussian matrix law.

**Lean implementation helper.** -/
private theorem integrable_matrixImageDiameter_aux {m n : ℕ}
    (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    Integrable (fun G : Matrix (Fin m) (Fin n) ℝ => matrixImageDiameter G T)
      (gaussianMatrixMeasure m n) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨N, hN, hNcard⟩ := HDP.Chapter4.exists_quarter_unitSphereNet m
  let Z : Matrix (Fin m) (Fin n) ℝ → ℝ := fun G =>
    N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
      finiteGaussianSupport (differenceFinset T T)
        (matrixTransposeEuclidean_aux z G))
  have hZint := integrable_gaussianNetSupport_aux hm T hT N hN
  apply Integrable.mono' (hZint.const_mul (4 / 3 : ℝ))
  · exact (measurable_matrixImageDiameter_aux T).aestronglyMeasurable
  · filter_upwards [] with G
    simp only [Real.norm_eq_abs]
    have hdiamnonneg : 0 ≤ matrixImageDiameter G T := Metric.diam_nonneg
    rw [abs_of_nonneg hdiamnonneg]
    exact matrixImageDiameter_le_netSupport_aux hm T hT N hN G

/-- Bounds expected Gaussian-projection diameter above by Gaussian width times the expected Gaussian norm.

**Lean implementation helper.** -/
private theorem gaussianProjection_expectedDiameter_upper_aux :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ}, 0 < m →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        (∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n) ≤
          C * (gaussianWidth T +
            Real.sqrt m * finiteEuclideanDiameter T) := by
  refine ⟨64, by norm_num, ?_⟩
  intro m n hm T hT
  have hwidth := gaussianWidth_nonneg T hT
  have hdiam := finiteEuclideanDiameter_nonneg T
  by_cases hdiam0 : finiteEuclideanDiameter T = 0
  · have hsub : (↑T : Set (EuclideanSpace ℝ (Fin n))).Subsingleton := by
      intro x hx y hy
      have hxy := norm_sub_le_finiteEuclideanDiameter T hT
        (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy)
      rw [hdiam0] at hxy
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hxy (norm_nonneg _)))
    have himage (G : Matrix (Fin m) (Fin n) ℝ) :
        matrixImageDiameter G T = 0 := by
      apply Metric.diam_subsingleton
      intro a ha b hb
      simp only [matrixImageFinset, Finset.coe_image, Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [hsub hx hy]
    simp_rw [himage]
    simp only [integral_zero]
    exact mul_nonneg (by norm_num) (add_nonneg hwidth
      (mul_nonneg (Real.sqrt_nonneg _) hdiam))
  · have hdiampos : 0 < finiteEuclideanDiameter T :=
      lt_of_le_of_ne hdiam (Ne.symm hdiam0)
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    obtain ⟨N, hN, hNcard⟩ := HDP.Chapter4.exists_quarter_unitSphereNet m
    let Z : Matrix (Fin m) (Fin n) ℝ → ℝ := fun G =>
      N.sup' (quarterNet_nonempty_aux hm hN) (fun z =>
        finiteGaussianSupport (differenceFinset T T)
          (matrixTransposeEuclidean_aux z G))
    have hZint := integrable_gaussianNetSupport_aux hm T hT N hN
    have hdiamInt := integrable_matrixImageDiameter_aux hm T hT
    have hZexp := gaussianNetSupport_expectation_le_aux hm T hT hdiampos
      N hN hNcard
    have hs5nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    have hs5sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hs5le : Real.sqrt 5 ≤ 3 := by nlinarith
    have hb : 0 ≤ Real.sqrt m * finiteEuclideanDiameter T :=
      mul_nonneg (Real.sqrt_nonneg _) hdiam
    have hs5b : Real.sqrt 5 *
        (Real.sqrt m * finiteEuclideanDiameter T) ≤
        3 * (Real.sqrt m * finiteEuclideanDiameter T) :=
      mul_le_mul_of_nonneg_right hs5le hb
    calc
      (∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n) ≤
          ∫ G, (4 / 3 : ℝ) * Z G ∂gaussianMatrixMeasure m n := by
        apply integral_mono hdiamInt (hZint.const_mul (4 / 3 : ℝ))
        intro G
        exact matrixImageDiameter_le_netSupport_aux hm T hT N hN G
      _ = (4 / 3 : ℝ) *
          ∫ G, Z G ∂gaussianMatrixMeasure m n := by rw [integral_const_mul]
      _ ≤ (4 / 3 : ℝ) * (2 * gaussianWidth T +
          16 * Real.sqrt 5 * Real.sqrt m * finiteEuclideanDiameter T) := by
        gcongr
      _ ≤ 64 * (gaussianWidth T +
          Real.sqrt m * finiteEuclideanDiameter T) := by
        nlinarith

/-- Bounds Gaussian support of a difference set by Gaussian norm times matrix-image diameter.

**Lean implementation helper.** -/
private theorem finiteGaussianSupport_difference_le_matrixDiameter_aux
    {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1)
    (G : Matrix (Fin m) (Fin n) ℝ) :
    finiteGaussianSupport (differenceFinset T T)
        (matrixTransposeEuclidean_aux z G) ≤ matrixImageDiameter G T := by
  rw [finiteGaussianSupport_eq_sup' _ (differenceFinset_nonempty hT hT)]
  apply Finset.sup'_le
  intro d hd
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_differenceFinset_exists_aux T hd
  have hpair : matrixPairDistance_aux G (x, y) ≤ matrixImageDiameter G T := by
    rw [matrixImageDiameter_eq_sup'_aux G T hT]
    exact Finset.le_sup' (matrixPairDistance_aux G)
      (Finset.mem_product.mpr ⟨hx, hy⟩)
  calc
    inner ℝ (matrixTransposeEuclidean_aux z G) (x - y) =
        inner ℝ (G.toEuclideanLin (x - y)) z := by
      rw [real_inner_comm, inner_matrix_mul_eq_transpose_aux]
    _ ≤ |inner ℝ (G.toEuclideanLin (x - y)) z| := le_abs_self _
    _ ≤ ‖G.toEuclideanLin (x - y)‖ * ‖z‖ := abs_real_inner_le_norm _ _
    _ = matrixPairDistance_aux G (x, y) := by
      simp [matrixPairDistance_aux, hz]
    _ ≤ matrixImageDiameter G T := hpair

/-- Bounds expected Gaussian-projection diameter below by Gaussian width.

**Lean implementation helper.** -/
private theorem gaussianProjection_expectedDiameter_width_lower_aux
    {m n : ℕ} (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    2 * gaussianWidth T ≤
      ∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n := by
  let e : EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.single ⟨0, hm⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  let D := differenceFinset T T
  let F : EuclideanSpace ℝ (Fin n) → ℝ := finiteGaussianSupport D
  have hmp : MeasurePreserving (matrixTransposeEuclidean_aux e)
      (gaussianMatrixMeasure m n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨matrixTransposeEuclidean_measurable_aux e,
      map_matrixTransposeEuclidean_aux e he⟩
  have hleft : Integrable (fun G => F (matrixTransposeEuclidean_aux e G))
      (gaussianMatrixMeasure m n) := by
    change Integrable (F ∘ matrixTransposeEuclidean_aux e)
      (gaussianMatrixMeasure m n)
    exact hmp.integrable_comp_of_integrable (integrable_finiteGaussianSupport D)
  have hright := integrable_matrixImageDiameter_aux hm T hT
  have hmono :
      (∫ G, F (matrixTransposeEuclidean_aux e G)
        ∂gaussianMatrixMeasure m n) ≤
      ∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n := by
    apply integral_mono hleft hright
    intro G
    exact finiteGaussianSupport_difference_le_matrixDiameter_aux T hT e he G
  have hLaw : HasLaw (matrixTransposeEuclidean_aux e)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (gaussianMatrixMeasure m n) :=
    ⟨(matrixTransposeEuclidean_measurable_aux e).aemeasurable,
      map_matrixTransposeEuclidean_aux e he⟩
  have hInt := hLaw.integral_comp
    (measurable_finiteGaussianSupport D).aestronglyMeasurable
  have hleftEq :
      (∫ G, F (matrixTransposeEuclidean_aux e G)
        ∂gaussianMatrixMeasure m n) = gaussianWidth D := by
    simpa [F, gaussianWidth] using hInt
  rw [hleftEq] at hmono
  have hDwidth : gaussianWidth D = 2 * gaussianWidth T := by
    dsimp [D]
    rw [gaussianWidth_difference T T hT hT]
    ring
  rw [hDwidth] at hmono
  exact hmono

/-- Evaluates the expected absolute inner product after Gaussian matrix transposition.

**Lean implementation helper.** -/
private theorem integral_abs_inner_matrixTranspose_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1)
    (d : EuclideanSpace ℝ (Fin n)) :
    (∫ G, |inner ℝ d (matrixTransposeEuclidean_aux z G)|
      ∂gaussianMatrixMeasure m n) =
      Real.sqrt 2 / Real.sqrt Real.pi * ‖d‖ := by
  have hLaw : HasLaw (matrixTransposeEuclidean_aux z)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (gaussianMatrixMeasure m n) :=
    ⟨(matrixTransposeEuclidean_measurable_aux z).aemeasurable,
      map_matrixTransposeEuclidean_aux z hz⟩
  have hInt := hLaw.integral_comp
    (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      |inner ℝ d g|)).aestronglyMeasurable
  calc
    (∫ G, |inner ℝ d (matrixTransposeEuclidean_aux z G)|
      ∂gaussianMatrixMeasure m n) =
        ∫ g : EuclideanSpace ℝ (Fin n), |inner ℝ d g|
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      simpa using hInt
    _ = gaussianWidth (diameterSymmetricPairFinset d) := by
      rw [gaussianWidth]
      simp_rw [finiteGaussianSupport_diameterSymmetricPair, real_inner_comm]
    _ = Real.sqrt 2 / Real.sqrt Real.pi * ‖d‖ :=
      gaussianWidth_diameterSymmetricPair_eq d

/-- The absolute inner product after Gaussian matrix transposition is integrable.

**Lean implementation helper.** -/
private theorem integrable_abs_inner_matrixTranspose_aux {m n : ℕ}
    (z : EuclideanSpace ℝ (Fin m)) (hz : ‖z‖ = 1)
    (d : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun G => |inner ℝ d (matrixTransposeEuclidean_aux z G)|)
      (gaussianMatrixMeasure m n) := by
  have hmp : MeasurePreserving (matrixTransposeEuclidean_aux z)
      (gaussianMatrixMeasure m n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨matrixTransposeEuclidean_measurable_aux z,
      map_matrixTransposeEuclidean_aux z hz⟩
  change Integrable ((fun g : EuclideanSpace ℝ (Fin n) => |inner ℝ d g|) ∘
    matrixTransposeEuclidean_aux z) (gaussianMatrixMeasure m n)
  apply hmp.integrable_comp_of_integrable
  have hinner : Integrable (fun g : EuclideanSpace ℝ (Fin n) => inner ℝ d g)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [real_inner_comm] using integrable_inner_stdGaussian d
  simpa only [Real.norm_eq_abs] using hinner.norm

/-- Bounds expected Gaussian-projection diameter below by the original diameter.

**Lean implementation helper.** -/
private theorem gaussianProjection_expectedDiameter_diameter_lower_aux
    {m n : ℕ} (hm : 0 < m)
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) :
    (1 / 2 : ℝ) * Real.sqrt m * finiteEuclideanDiameter T ≤
      ∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n := by
  classical
  have hdiamSup := finiteEuclideanDiameter_eq_sup' T hT
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_mem_eq_sup' (hT.product hT)
    (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖q.1 - q.2‖)
  let d := p.1 - p.2
  have hdiamEq : finiteEuclideanDiameter T = ‖d‖ := by
    rw [hdiamSup]
    simpa [d] using hpmax
  have hsqrtm : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hmSq : (Real.sqrt (m : ℝ)) ^ 2 = m :=
    Real.sq_sqrt (by positivity)
  let e : Fin m → EuclideanSpace ℝ (Fin m) := fun i =>
    EuclideanSpace.single i 1
  have he (i : Fin m) : ‖e i‖ = 1 := by simp [e]
  let A : Fin m → Matrix (Fin m) (Fin n) ℝ → ℝ := fun i G =>
    |inner ℝ d (matrixTransposeEuclidean_aux (e i) G)|
  have hAint (i : Fin m) : Integrable (A i)
      (gaussianMatrixMeasure m n) := by
    simpa [A] using integrable_abs_inner_matrixTranspose_aux (e i) (he i) d
  have hsumInt : Integrable (fun G => ∑ i, A i G)
      (gaussianMatrixMeasure m n) :=
    integrable_finsetSum Finset.univ (fun i hi => hAint i)
  have hlowerInt : Integrable (fun G => (1 / Real.sqrt m : ℝ) * ∑ i, A i G)
      (gaussianMatrixMeasure m n) := hsumInt.const_mul _
  have hright := integrable_matrixImageDiameter_aux hm T hT
  have hpoint (G : Matrix (Fin m) (Fin n) ℝ) :
      (1 / Real.sqrt m : ℝ) * ∑ i, A i G ≤ matrixImageDiameter G T := by
    let q := G.toEuclideanLin d
    have hsum : (∑ i, A i G) = ∑ i, |q i| := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [A, q, e]
      rw [← inner_matrix_mul_eq_transpose_aux]
      simp [EuclideanSpace.inner_single_right]
    have hl1 := sum_abs_le_sqrt_mul_norm_aux q
    have hscaled : (1 / Real.sqrt m : ℝ) * ∑ i, A i G ≤ ‖q‖ := by
      rw [hsum]
      calc
        (1 / Real.sqrt m : ℝ) * ∑ i, |q i| ≤
            (1 / Real.sqrt m : ℝ) * (Real.sqrt m * ‖q‖) := by gcongr
        _ = ‖q‖ := by field_simp
    have hpair : ‖q‖ ≤ matrixImageDiameter G T := by
      rw [matrixImageDiameter_eq_sup'_aux G T hT]
      change matrixPairDistance_aux G p ≤ _
      exact Finset.le_sup' (matrixPairDistance_aux G) hp
    exact hscaled.trans hpair
  have hmono :
      (∫ G, (1 / Real.sqrt m : ℝ) * ∑ i, A i G
        ∂gaussianMatrixMeasure m n) ≤
      ∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n :=
    integral_mono hlowerInt hright hpoint
  have hAeq (i : Fin m) :
      (∫ G, A i G ∂gaussianMatrixMeasure m n) =
        Real.sqrt 2 / Real.sqrt Real.pi * ‖d‖ := by
    simpa [A] using integral_abs_inner_matrixTranspose_aux (e i) (he i) d
  have habsLower : (1 / 2 : ℝ) * ‖d‖ ≤
      Real.sqrt 2 / Real.sqrt Real.pi * ‖d‖ :=
    mul_le_mul_of_nonneg_right half_le_gaussian_abs_constant_aux (norm_nonneg d)
  have hcalc :
      (1 / 2 : ℝ) * Real.sqrt m * ‖d‖ ≤
        ∫ G, (1 / Real.sqrt m : ℝ) * ∑ i, A i G
          ∂gaussianMatrixMeasure m n := by
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun i hi => hAint i)]
    simp_rw [hAeq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    calc
      (1 / 2 : ℝ) * Real.sqrt m * ‖d‖ =
          (1 / Real.sqrt m : ℝ) *
            (m * ((1 / 2 : ℝ) * ‖d‖)) := by
        field_simp
        rw [hmSq]
        ring
      _ ≤ (1 / Real.sqrt m : ℝ) *
          (m * (Real.sqrt 2 / Real.sqrt Real.pi * ‖d‖)) := by
        gcongr
      _ = _ := rfl
  rw [hdiamEq]
  exact hcalc.trans hmono

/-- Combines Gaussian-width and diameter lower bounds for expected Gaussian-projection diameter.

**Lean implementation helper.** -/
private theorem gaussianProjection_expectedDiameter_lower_aux :
    ∃ c : ℝ, 0 < c ∧
      ∀ {m n : ℕ}, 0 < m →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        c * (gaussianWidth T +
            Real.sqrt m * finiteEuclideanDiameter T) ≤
          ∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro m n hm T hT
  have hw := gaussianProjection_expectedDiameter_width_lower_aux hm T hT
  have hd := gaussianProjection_expectedDiameter_diameter_lower_aux hm T hT
  have hwidth := gaussianWidth_nonneg T hT
  have hterm : 0 ≤ Real.sqrt m * finiteEuclideanDiameter T :=
    mul_nonneg (Real.sqrt_nonneg _) (finiteEuclideanDiameter_nonneg T)
  nlinarith

/-- Universal positive constants bound expected Gaussian-projection diameter above and below by Gaussian width plus square-root rank times diameter.

**Lean implementation helper.** -/
private theorem gaussianProjection_expectedDiameter_aux :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < m →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        c * (gaussianWidth T +
            Real.sqrt m * finiteEuclideanDiameter T) ≤
          (∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n) ∧
        (∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n) ≤
          C * (gaussianWidth T +
            Real.sqrt m * finiteEuclideanDiameter T) := by
  obtain ⟨c, hc, hlower⟩ := gaussianProjection_expectedDiameter_lower_aux
  obtain ⟨C, hC, hupper⟩ := gaussianProjection_expectedDiameter_upper_aux
  refine ⟨c, C, hc, hC, ?_⟩
  intro m n hm T hT
  exact ⟨hlower hm T hT, hupper hm T hT⟩

/-- Gaussian projection analogue of the projection-diameter theorem. The square-root term is unnormalized because the entries have law
`N(0,1)`. This proof is independent of the Gaussian comparison theorems. It identifies
every fixed `Gᵀz` with a standard Gaussian vector, uses a quarter-net and
Gaussian Lipschitz concentration for the upper bound, and obtains the two
lower terms from a fixed row and from the exact mean absolute Gaussian
coordinate, respectively.

**Book Exercise 7.25.** -/
theorem exercise_7_25_gaussianProjection_expectedDiameter :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ}, 0 < m →
      ∀ (T : Finset (EuclideanSpace ℝ (Fin n))), T.Nonempty →
        c * (gaussianWidth T +
            Real.sqrt m * finiteEuclideanDiameter T) ≤
          (∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n) ∧
        (∫ G, matrixImageDiameter G T ∂gaussianMatrixMeasure m n) ≤
          C * (gaussianWidth T +
            Real.sqrt m * finiteEuclideanDiameter T) := by
  exact gaussianProjection_expectedDiameter_aux

/-- Orthogonally projecting the Euclidean unit ball onto a nonzero subspace
produces exactly the unit ball of that subspace, so its diameter remains two.

**Book Equation (7.21).** -/
theorem orthogonalProjection_unitBall_diam
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Submodule ℝ E} [K.HasOrthogonalProjection] (hK : K ≠ ⊥) :
    Metric.diam (K.orthogonalProjectionOnto ''
      Metric.closedBall (0 : E) 1) = 2 := by
  letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
  have himage :
      K.orthogonalProjectionOnto '' Metric.closedBall (0 : E) 1 =
        Metric.closedBall (0 : K) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
      exact (K.norm_orthogonalProjectionOnto_apply_le x).trans hx
    · intro hz
      refine ⟨(z : E), ?_, ?_⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using hz
      · simp
  rw [himage]
  simpa using
    (Metric.diam_closedBall_eq (0 : K) (by norm_num : (0 : ℝ) ≤ 1))

/-- Random-projection diameter has a width-dominated/diameter-dominated phase transition. The elementary sum-to-maximum comparison behind
the phase-transition formulation.

**Book Remark 7.6.2.** -/
theorem phaseTransition_sum_equiv_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ a + b ∧ a + b ≤ 2 * max a b := by
  constructor
  · exact max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
  · have ha' : a ≤ max a b := le_max_left _ _
    have hb' : b ≤ max a b := le_max_right _ _
    linarith

end

end HDP.Chapter7

end Source_14_RandomProjections
