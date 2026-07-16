import HighDimensionalProbability.Chapter4_RandomMatrices
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher

/-!
# Chapter 4 exercises attached to Sections 4.2--4.3

These declarations are exercise leaves.  Pure counterexample/construction
components are recorded in the audit and skipped; Exercise 4.29(a) uses the
audited fundamental-theorem hypothesis rather than the false
differentiability-only printed version.
-/

open Set Filter MeasureTheory Metric
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

namespace HDP.Chapter4.Exercise

variable {X : Type*} [PseudoEMetricSpace X]

/-- Nets compose, with the radii added.

**Book Exercise 4.23.** -/
theorem exercise_4_23 {K M N : Set X} {ε δ : ℝ≥0}
    (hNM : HDP.IsEpsilonNet ε M N) (hMK : HDP.IsEpsilonNet δ K M) :
    HDP.IsEpsilonNet (ε + δ) K N := by
  constructor
  · exact hNM.1.trans hMK.1
  · intro x hx
    obtain ⟨y, hyM, hxy⟩ := hMK.2 hx
    obtain ⟨z, hzN, hyz⟩ := hNM.2 hyM
    refine ⟨z, hzN, ?_⟩
    change edist x y ≤ (δ : ℝ≥0∞) at hxy
    change edist y z ≤ (ε : ℝ≥0∞) at hyz
    calc
      edist x z ≤ edist x y + edist y z := edist_triangle _ _ _
      _ ≤ (δ : ℝ≥0∞) + (ε : ℝ≥0∞) := add_le_add hxy hyz
      _ = ((ε + δ : ℝ≥0) : ℝ≥0∞) := by simp [add_comm]

/- Exercise 4.24(a) is a pure counterexample request and is therefore recorded
and skipped under the constructive-witness policy. -/

/-- In a real normed space the midpoint proves the converse.

**Book Exercise 4.24(b).** -/
theorem exercise_4_24b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε : ℝ≥0} {N : Set E}
    (hballs : Set.PairwiseDisjoint N
      (fun x => Metric.closedBall x ((ε : ℝ) / 2))) :
    Metric.IsSeparated ε N := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.24(b).
  sorry

/- Exercise 4.26(a) is a pure counterexample request and is therefore recorded
and skipped under the constructive-witness policy. -/

/-- Approximate monotonicity of internal covering numbers.

**Book Exercise 4.26(b).** -/
theorem exercise_4_26b {L K : Set X} (hLK : L ⊆ K) (ε : ℝ≥0) :
    Metric.coveringNumber ε L ≤ Metric.coveringNumber (ε / 2) K := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.26(b).
  sorry

/-! ## Volume exercises -/

/-- The canonical simplex in Euclidean `n`-space.

**Lean implementation helper.** -/
def canonicalSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The unit `ℓ¹` ball.

**Lean implementation helper.** -/
def l1Ball (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∑ i, |x i| ≤ 1}

/-- Computes the exact volume of the canonical simplex.

**Book Exercise 4.27(a).** -/
theorem exercise_4_27a (n : ℕ) :
    (volume (canonicalSimplex n)).toReal = 1 / (n.factorial : ℝ) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.27(a).
  sorry

/-- Computes the exact volume of the `ℓ¹` ball and gives its elementary exponential upper bound.

**Book Exercise 4.27(b).** -/
theorem exercise_4_27b (n : ℕ) :
    (volume (l1Ball n)).toReal = 2 ^ n / (n.factorial : ℝ) ∧
      (volume (l1Ball n)).toReal ≤ (2 * Real.exp 1 / n) ^ n := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.27(b).
  sorry

/-- Gives matching elementary upper and lower volume bounds for the Euclidean unit ball.

**Book Exercise 4.27(c).** -/
theorem exercise_4_27c (n : ℕ) (hn : 1 ≤ n) :
    (2 / Real.sqrt n) ^ n ≤
        (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ∧
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ≤
        (2 * Real.exp 1 / Real.sqrt n) ^ n := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.27(c).
  sorry

/-- The probabilistic upper bound for Euclidean volume.

**Book Exercise 4.28.** -/
theorem exercise_4_28 (n : ℕ) (hn : 1 ≤ n) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ≤
      (Real.sqrt (2 * Real.pi * Real.exp 1 / n)) ^ n := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.28.
  sorry

/-- Audited fundamental-theorem condition for the corresponding exercise.

**Lean implementation helper.** -/
def HasTailIntegralRepresentation (f f' : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → f t = -∫ u in Set.Ici t, f' u

/-- The explicit tail-integral hypothesis captures the absolute-continuity/fundamental-theorem
step missing in print; measurability and nonnegativity record that `N` is a norm, so only the
audited nonnegative tail representation is used.

**Book Exercise 4.29(a).** -/
theorem exercise_4_29a {n : ℕ} (N : EuclideanSpace ℝ (Fin n) → ℝ)
    (f f' : ℝ → ℝ) (hNmeas : Measurable N) (hNnonneg : ∀ x, 0 ≤ N x)
    (hN : ∀ c : ℝ, 0 ≤ c →
      volume {x | N x ≤ c} = ENNReal.ofReal (c ^ n) * volume {x | N x ≤ 1})
    (hFTC : HasTailIntegralRepresentation f f')
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f (N x)))
    (hint' : IntegrableOn (fun t => t ^ n * f' t) (Set.Ici 0)) :
    ∫ x : EuclideanSpace ℝ (Fin n), f (N x) =
      -(volume {x | N x ≤ 1}).toReal * ∫ t in Set.Ici (0 : ℝ), t ^ n * f' t := by
  -- EXERCISE-SORRY: category A; corrected non-load-bearing Exercise 4.29(a).
  sorry

/-- Exact Euclidean ball volume.

**Book Exercise 4.29(b).** -/
theorem exercise_4_29b (n : ℕ) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal =
      Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.29(b).
  sorry

/-- Shows the asymptotic radius of a Euclidean ball normalized to have unit volume.

**Book Exercise 4.29(c).** -/
theorem exercise_4_29c
    (R : ℕ → ℝ) (hR : ∀ n, 0 < n →
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R n)) = 1) :
    Tendsto (fun n => R n / Real.sqrt (n / (2 * Real.pi * Real.exp 1)))
      atTop (𝓝 1) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.29(c).
  sorry

/-- Unit `ℓᵖ` ball for finite positive `p`.

**Lean implementation helper.** -/
def lpBall (n : ℕ) (p : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∑ i, |x i| ^ p ≤ 1}

/-- The `ℓ∞` unit ball, kept separate from the real-valued finite-`p` parameter above.

**Lean implementation helper.** -/
def linftyBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, |x i| ≤ 1}

/-- Identifies `ℓ∞` ball with preimage icc.

**Lean implementation helper.** -/
private lemma linftyBall_eq_preimage_Icc (n : ℕ) :
    linftyBall n = WithLp.ofLp ⁻¹'
      Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ : Fin n => 1) := by
  ext x
  simp only [linftyBall, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc,
    Pi.le_def]
  constructor
  · intro hx
    exact ⟨fun i => (abs_le.mp (hx i)).1, fun i => (abs_le.mp (hx i)).2⟩
  · rintro ⟨hl, hu⟩ i
    exact abs_le.mpr ⟨hl i, hu i⟩

/-- Gives elementary upper and lower volume bounds for finite-`p` unit balls.

**Book Exercise 4.30(a).** -/
theorem exercise_4_30a (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) :
    (2 / (n : ℝ) ^ (1 / p)) ^ n ≤ (volume (lpBall n p)).toReal ∧
      (volume (lpBall n p)).toReal ≤
        (2 * Real.exp 1 / (n : ℝ) ^ (1 / p)) ^ n := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.30(a).
  sorry

/-- Computes the exact finite-`p` unit-ball volume using the Gamma function.

**Book Exercise 4.30(b).** -/
theorem exercise_4_30b (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    (volume (lpBall n p)).toReal =
      (2 * Real.Gamma (1 / p + 1)) ^ n /
        Real.Gamma ((n : ℝ) / p + 1) := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.30(b).
  sorry

/-- The unit ball is the cube `[-1,1]^n`, whose exact volume is `2^n`; the source's two
geometric bounds then follow. This endpoint is proved rather than deferred.

**Book Exercise 4.30.** -/
theorem exercise_4_30_infty (n : ℕ) :
    (volume (linftyBall n)).toReal = (2 : ℝ) ^ n ∧
      (2 : ℝ) ^ n ≤ (volume (linftyBall n)).toReal ∧
      (volume (linftyBall n)).toReal ≤ (2 * Real.exp 1) ^ n := by
  have hvol : (volume (linftyBall n)).toReal = (2 : ℝ) ^ n := by
    rw [linftyBall_eq_preimage_Icc,
      (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
        measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi]
    norm_num
  refine ⟨hvol, hvol.ge, ?_⟩
  rw [hvol]
  apply pow_le_pow_left₀ (by norm_num)
  nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]

/-- The scaled integer lattice points inside the Euclidean unit ball.

**Lean implementation helper.** -/
def scaledLatticeNet (n : ℕ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ ≤ 1 ∧ ∃ z : Fin n → ℤ,
    ∀ i, x i = ε / Real.sqrt n * z i}

/-- The required positivity is explicit. The final cover witness is the formal nearest-lattice
approximation algorithm.

**Book Remark 4.2.13.** -/
theorem exercise_4_31 (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    (scaledLatticeNet n ε).Finite ∧
      Metric.IsCover (Real.toNNReal ε)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        (scaledLatticeNet n ε) ∧
      ((scaledLatticeNet n ε).ncard : ℝ) ≤
        Real.exp n * (2 / ε + 1) ^ n := by
  -- EXERCISE-SORRY: category A; non-load-bearing Exercise 4.31.
  sorry

end HDP.Chapter4.Exercise
