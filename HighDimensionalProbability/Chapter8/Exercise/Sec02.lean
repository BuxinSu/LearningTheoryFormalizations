/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter8_Chaining

/-!
# Book Chapter 8 exercises attached to Section 8.2

Exercises 8.9 and 8.11 are promoted into Chapter 8 core.  Exercise 8.10 is
stated for the full anchored Lipschitz class, with the needed integrability of
its supremum exposed explicitly.  The source
accidentally says that the samples are `[0,1]`-valued although its functions
have domain `[0,1]^d`; below the samples correctly take values in the cube.

The anchored representative `f(0)=0` repairs a second harmless presentation
gap: the unrestricted class of real-valued Lipschitz functions has infinite
uniform covering number because it is closed under arbitrary constant shifts,
while empirical-process deviations are invariant under those shifts.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace HDP.Chapter8.Exercise

noncomputable section

/-- The closed unit cube `[0,1]^d`. -/
abbrev UnitCube (d : ℕ) :=
  {x : Fin d → ℝ // ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The origin in the unit cube.

**Lean implementation helper.** -/
def unitCubeOrigin (d : ℕ) : UnitCube d :=
  ⟨0, by simp⟩

/-- An anchored `L`-Lipschitz real function on the unit cube. -/
structure CubeLipschitzFunction (d : ℕ) (L : ℝ≥0) where
  toFun : UnitCube d → ℝ
  lipschitz : LipschitzWith L toFun
  at_origin : toFun (unitCubeOrigin d) = 0

instance (d : ℕ) (L : ℝ≥0) : CoeFun (CubeLipschitzFunction d L)
    (fun _ => UnitCube d → ℝ) := ⟨CubeLipschitzFunction.toFun⟩

/-- Uniform distance between two cube functions.

**Lean implementation helper.** -/
def cubeUniformDistance {d : ℕ} {L : ℝ≥0}
    (f g : CubeLipschitzFunction d L) : ℝ :=
  sSup (Set.range fun x : UnitCube d => |f x - g x|)

/-- A finite uniform net for the full anchored Lipschitz class.

**Lean implementation helper.** -/
def IsCubeUniformNet {d : ℕ} {L : ℝ≥0}
    (net : Finset (CubeLipschitzFunction d L)) (ε : ℝ) : Prop :=
  ∀ f : CubeLipschitzFunction d L,
    ∃ g : ↥net, cubeUniformDistance f g.1 ≤ ε

/-- Finite measurable supremum of empirical-process deviations over a cube
function class.

**Lean implementation helper.** -/
def cubeUniformEmpiricalDeviation {d n : ℕ} {L : ℝ≥0}
    (F : Finset (CubeLipschitzFunction d L)) (μ : Measure (UnitCube d))
    (sample : Fin n → UnitCube d) : ℝ :=
  ‖fun f : ↥F =>
    empiricalProcessValue μ sample f.1.toFun‖

/-- Supremum of the absolute empirical-process deviation over the entire
anchored Lipschitz class. Anchoring is harmless because empirical deviations
are invariant under adding constants, and it repairs the source's otherwise
false finite-covering assertion for real-valued Lipschitz functions.

**Lean implementation helper.** -/
def cubeUniformEmpiricalDeviationAll {d n : ℕ} (L : ℝ≥0)
    (μ : Measure (UnitCube d)) (sample : Fin n → UnitCube d) : ℝ :=
  sSup (Set.range fun f : CubeLipschitzFunction d L =>
    |empiricalProcessValue μ sample f.toFun|)

/-- **Exercise 8.10(a).** Entropy of anchored Lipschitz functions on the
`d`-dimensional cube.

**Book Exercise 8.10(a).** -/
theorem exercise_8_10a_cube_lipschitz_covering :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 0 < d → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ net : Finset (CubeLipschitzFunction d 1),
        (net.card : ℝ) ≤ Real.exp (C / ε ^ d) ∧
        ∀ f : CubeLipschitzFunction d 1,
          ∃ g : ↥net, cubeUniformDistance f g.1 ≤ ε :=
  -- EXERCISE-SORRY: Exercise 8.10(a).
  by sorry

/-- **Exercise 8.10(b).** The empirical Dudley integral may be truncated at
an arbitrary scale `δ`, paying the additive discretization error `δ`.

**Book Exercise 8.10(b).** -/
theorem exercise_8_10b_refined_empirical_dudley :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (μ : Measure (UnitCube d)) (X : Fin n → Ω → UnitCube d)
        (coverCard : ℝ → ℕ) (δ : ℝ),
        0 < n → 0 ≤ δ → δ ≤ 1 →
        (∀ ε, δ ≤ ε → ε ≤ 1 →
          ∃ net : Finset (CubeLipschitzFunction d 1),
            IsCubeUniformNet net ε ∧ net.card ≤ coverCard ε) →
        (∀ i, Measurable (X i)) →
        (∀ i, Measure.map (X i) P = μ) →
        iIndepFun X P →
        Integrable (fun ω => cubeUniformEmpiricalDeviationAll 1 μ
          (fun i => X i ω)) P →
        (∫ ω, cubeUniformEmpiricalDeviationAll 1 μ
            (fun i => X i ω) ∂P) ≤
          C * (δ + (Real.sqrt n)⁻¹ *
            ∫ ε in Set.Icc δ 1,
              Real.sqrt (Real.log (coverCard ε : ℝ))) :=
  -- EXERCISE-SORRY: Exercise 8.10(b).
  by sorry

/-- **Exercise 8.10, dimension two.** Correctly cube-valued samples satisfy
the logarithmically corrected `n⁻¹/²` rate.

**Book Exercise 8.10.** -/
theorem exercise_8_10_lipschitz_lln_dimension_two :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} {L : ℝ≥0} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (μ : Measure (UnitCube 2)) (X : Fin n → Ω → UnitCube 2),
        0 < n →
        (∀ i, Measurable (X i)) →
        (∀ i, Measure.map (X i) P = μ) →
        iIndepFun X P →
        Integrable (fun ω => cubeUniformEmpiricalDeviationAll L μ
          (fun i => X i ω)) P →
        (∫ ω, cubeUniformEmpiricalDeviationAll L μ
            (fun i => X i ω) ∂P) ≤
          C * (L : ℝ) * Real.log (n + 1) / Real.sqrt n :=
  -- EXERCISE-SORRY: Exercise 8.10 (the case d = 2).
  by sorry

/-- **Exercise 8.10, dimensions at least three.**.

**Book Exercise 8.10.** -/
theorem exercise_8_10_lipschitz_lln_high_dimension :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} {L : ℝ≥0} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (μ : Measure (UnitCube d)) (X : Fin n → Ω → UnitCube d),
        3 ≤ d → 0 < n →
        (∀ i, Measurable (X i)) →
        (∀ i, Measure.map (X i) P = μ) →
        iIndepFun X P →
        Integrable (fun ω => cubeUniformEmpiricalDeviationAll L μ
          (fun i => X i ω)) P →
        (∫ ω, cubeUniformEmpiricalDeviationAll L μ
            (fun i => X i ω) ∂P) ≤
          C * (L : ℝ) * Real.rpow n (-(1 / (d : ℝ))) :=
  -- EXERCISE-SORRY: Exercise 8.10 (the case d ≥ 3).
  by sorry

end

end HDP.Chapter8.Exercise
