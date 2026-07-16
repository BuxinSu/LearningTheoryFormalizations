/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter8_Chaining
import HighDimensionalProbability.Chapter7_RandomProcesses

/-!
# Book Chapter 8 exercises attached to Section 8.6

Exercise 8.39 is promoted into Chapter 8 core and is not redeclared here.
Exercise 8.40 is stated for the source's arbitrary nonempty bounded sets; its
explicit event-measurability hypothesis is the standard condition suppressed
by the printed statement.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
  Matrix.Norms.L2Operator Topology

namespace HDP.Chapter8.Exercise

noncomputable section

/-- Radius of a nonempty finite Euclidean set.

**Lean implementation helper.** -/
def finiteEuclideanRadius {n : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin n))) (hS : S.Nonempty) : ℝ :=
  S.sup' hS norm

/-- Finite bilinear supremum `sup ⟪A x,y⟫`.

**Lean implementation helper.** -/
def finiteMatrixBilinearSup {m n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty)
    (S : Finset (EuclideanSpace ℝ (Fin m))) (hS : S.Nonempty)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (T.product S).sup' (hT.product hS) fun p =>
    ∑ i, (A.mulVec p.1) i * p.2 i

/-- Radius of an arbitrary Euclidean set.

**Lean implementation helper.** -/
def euclideanSetRadius {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup (norm '' S)

/-- Gaussian width is the expected support of a set in a standard Gaussian direction. Gaussian width of an arbitrary Euclidean set.

**Book Definition 7.5.1.** -/
def euclideanSetGaussianWidth {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ g, sSup ((fun x => inner ℝ g x) '' S)
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Bilinear supremum over arbitrary Euclidean index sets.

**Lean implementation helper.** -/
def matrixSetBilinearSup {m n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ T, ∃ y ∈ S,
    r = ∑ i, (A.mulVec x) i * y i}

/-- **Exercise 8.40.** High-probability subgaussian Chevet inequality on the
arbitrary nonempty bounded index sets of Theorem 8.6.1.

**Book Exercise 8.40.** -/
theorem exercise_8_40_chevet_high_probability :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (T : Set (EuclideanSpace ℝ (Fin n)))
        (S : Set (EuclideanSpace ℝ (Fin m)))
        (K u : ℝ),
        T.Nonempty → S.Nonempty → Bornology.IsBounded T → Bornology.IsBounded S →
        0 ≤ K → 0 ≤ u →
        (∀ i j, Measurable (fun ω => A ω i j)) →
        (∀ i j, ∫ ω, A ω i j ∂P = 0) →
        iIndepFun (fun i ω => A ω i) P →
        (∀ i, ∀ x : EuclideanSpace ℝ (Fin n),
          HDP.SubGaussian (fun ω => ∑ j, A ω i j * x j) P ∧
            HDP.psi2Norm (fun ω => ∑ j, A ω i j * x j) P ≤ K * ‖x‖) →
        MeasurableSet {ω | matrixSetBilinearSup T S (A ω) ≤
          C * K *
            (euclideanSetGaussianWidth T * euclideanSetRadius S +
              euclideanSetGaussianWidth S * euclideanSetRadius T +
              u * euclideanSetRadius T * euclideanSetRadius S)} →
        P.real {ω | matrixSetBilinearSup T S (A ω) ≤
          C * K *
            (euclideanSetGaussianWidth T * euclideanSetRadius S +
              euclideanSetGaussianWidth S * euclideanSetRadius T +
              u * euclideanSetRadius T * euclideanSetRadius S)} ≥
          1 - 2 * Real.exp (-u ^ 2) :=
  -- EXERCISE-SORRY: Exercise 8.40.
  by sorry

/-! ## Exercise 8.41: p-to-q norms -/

/-- `ℓᵖ` norm for `p : [0,∞]`; the top exponent is the maximum coordinate.

**Lean implementation helper.** -/
def extendedEllPNorm {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (x : ι → ℝ) : ℝ :=
  if p = ⊤ then sSup (Set.range fun i => |x i|)
  else Real.rpow (∑ i, Real.rpow |x i| p.toReal) (1 / p.toReal)

/-- Matrix norm from `ℓᵖ` to `ℓᑫ`.

**Lean implementation helper.** -/
def matrixPToQNorm {m n : ℕ} (p q : ℝ≥0∞)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℝ,
    extendedEllPNorm p x ≤ 1 ∧
      r = extendedEllPNorm q (A.mulVec x)}

/-- Hölder conjugate, including the endpoints `1 ↔ ∞`.

**Lean implementation helper.** -/
def extendedHolderConjugate (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 1 then ⊤
  else if p = ⊤ then 1
  else ENNReal.ofReal (p.toReal / (p.toReal - 1))

/-- The radius scale `r(n,p)` from Exercise 8.41.

**Book Exercise 8.41.** -/
def pqRadiusScale (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  if p ≤ 2 then 1
  else Real.rpow n
    ((1 : ℝ) / 2 - if p = ⊤ then 0 else 1 / p.toReal)

/-- The Gaussian-width scale `w(n,p)` from Exercise 8.41.

**Book Exercise 8.41.** -/
def pqWidthScale (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  if p ≤ ENNReal.ofReal (Real.log n) then
    Real.sqrt p.toReal * Real.rpow n (1 / p.toReal)
  else Real.sqrt (Real.log n)

/-- **Exercise 8.41(a).** Expected `p → q` norm of a matrix with independent
mean-zero subgaussian rows. The harmless assumptions `m,n ≥ 2` make the
printed `sqrt (log m)` and `sqrt (log n)` proxies nondegenerate; the omitted
one-dimensional cases require the usual `log (2m)`/`log (2n)` convention.

**Book Exercise 8.41(a).** -/
theorem exercise_8_41a_expected_p_to_q_norm :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (p q : ℝ≥0∞) (K : ℝ),
        2 ≤ m → 2 ≤ n → 1 ≤ p → 1 ≤ q → 0 ≤ K →
        (∀ i j, Measurable (fun ω => A ω i j)) →
        (∀ i j, ∫ ω, A ω i j ∂P = 0) →
        iIndepFun (fun i ω => A ω i) P →
        (∀ i, ∀ x : EuclideanSpace ℝ (Fin n),
          HDP.SubGaussian (fun ω => ∑ j, A ω i j * x j) P ∧
            HDP.psi2Norm (fun ω => ∑ j, A ω i j * x j) P ≤ K * ‖x‖) →
        Integrable (fun ω => matrixPToQNorm p q (A ω)) P →
        (∫ ω, matrixPToQNorm p q (A ω) ∂P) ≤
          C * K *
            (pqRadiusScale n p * pqWidthScale m q +
              pqRadiusScale m (extendedHolderConjugate q) *
                pqWidthScale n (extendedHolderConjugate p)) :=
  -- EXERCISE-SORRY: Exercise 8.41(a).
  by sorry

/-- **Exercise 8.41(b).** Matching Gaussian lower bound, in the same
nondegenerate dimensional range as part (a).

**Book Exercise 8.41(b).** -/
theorem exercise_8_41b_gaussian_p_to_q_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (p q : ℝ≥0∞),
        2 ≤ m → 2 ≤ n → 1 ≤ p → 1 ≤ q →
        (∀ i j, HasLaw (fun ω => A ω i j)
          (gaussianReal 0 1) P) →
        iIndepFun (fun ij : Fin m × Fin n =>
          fun ω => A ω ij.1 ij.2) P →
        Integrable (fun ω => matrixPToQNorm p q (A ω)) P →
        c * (pqRadiusScale n p * pqWidthScale m q +
          pqRadiusScale m (extendedHolderConjugate q) *
            pqWidthScale n (extendedHolderConjugate p)) ≤
          ∫ ω, matrixPToQNorm p q (A ω) ∂P :=
  -- EXERCISE-SORRY: Exercise 8.41(b).
  by sorry

end

end HDP.Chapter8.Exercise
