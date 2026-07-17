import HighDimensionalProbability.Prelude.Basic
import HighDimensionalProbability.Prelude.MetricEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Appetizer: Using Probability to Cover a Set

This file formalizes the source-facing results from the opening Appetizer.

## Contents

- Exercise 0.1(a): vector bias--variance identity.
- Exercise 0.2: the mean minimizes expected squared Euclidean distance.
- Exercise 0.3: Pythagorean identity for sums of independent centered vectors.
- Theorem 0.0.2: approximate Caratheodory theorem.
- Corollary 0.0.3: covering a polytope by equal-radius Euclidean balls.
- Equations (0.3)--(0.4), Theorem 0.0.4, and Remark 0.0.5: volume consequences.

The later declarations are added in dependency order as their prerequisites are
completed. The original book PDF, pages 2--6, is the authoritative source.
-/

open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace ENNReal NNReal

namespace HDP.Chapter0

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The vector bias--variance identity.

For a square-integrable random vector `Z` in a real Hilbert space,
`𝔼 ‖Z - 𝔼Z‖² = 𝔼 ‖Z‖² - ‖𝔼Z‖²`.

**Book Exercise 0.1(a).** This is a load-bearing
exercise: the proof of Theorem 0.0.2 invokes it explicitly.
-/
theorem integral_norm_sub_mean_sq
    [IsProbabilityMeasure μ] {Z : Ω → E} (hZ : MemLp Z 2 μ) :
    (∫ ω, ‖Z ω - ∫ ω, Z ω ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - ‖∫ ω, Z ω ∂μ‖ ^ 2 := by
  let m : E := ∫ ω, Z ω ∂μ
  have hZint : Integrable Z μ := hZ.integrable one_le_two
  have hnormZ : Integrable (fun ω ↦ ‖Z ω‖ ^ 2) μ := by
    exact hZ.integrable_norm_pow'
  have hinner : Integrable (fun ω ↦ ⟪m, Z ω⟫_ℝ) μ := hZint.const_inner m
  calc
    (∫ ω, ‖Z ω - m‖ ^ 2 ∂μ)
        = ∫ ω, (‖Z ω‖ ^ 2 - 2 * ⟪m, Z ω⟫_ℝ + ‖m‖ ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self]
            simp only [real_inner_comm, real_inner_self_eq_norm_sq]
    _ = (∫ ω, (‖Z ω‖ ^ 2 - 2 * ⟪m, Z ω⟫_ℝ) ∂μ) +
          ∫ _ω, ‖m‖ ^ 2 ∂μ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              integral_add (hnormZ.sub (hinner.const_mul 2))
                (integrable_const (μ := μ) (c := ‖m‖ ^ 2))
    _ = (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - 2 * (∫ ω, ⟪m, Z ω⟫_ℝ ∂μ) + ‖m‖ ^ 2 := by
          rw [integral_sub hnormZ (hinner.const_mul 2), integral_const_mul]
          simp
    _ = (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - ‖m‖ ^ 2 := by
          rw [integral_inner hZint]
          simp only [m, real_inner_self_eq_norm_sq]
          ring

/-- The mean minimizes expected squared Euclidean distance.

The mean of a square-integrable random vector minimizes expected squared
Euclidean distance: for every deterministic center `a`,
`𝔼 ‖Z-𝔼Z‖² ≤ 𝔼 ‖Z-a‖²`.

**Book Exercise 0.2.** The scalar specialization is used
later at equation (2.23); this theorem supplies the full vector statement asked
for in the Appetizer.
-/
theorem integral_norm_sub_mean_sq_le
    [IsProbabilityMeasure μ] {Z : Ω → E} (hZ : MemLp Z 2 μ) (a : E) :
    (∫ ω, ‖Z ω - ∫ ω, Z ω ∂μ‖ ^ 2 ∂μ) ≤
      ∫ ω, ‖Z ω - a‖ ^ 2 ∂μ := by
  let m : E := ∫ ω, Z ω ∂μ
  have hZint : Integrable Z μ := hZ.integrable one_le_two
  have hnormZ : Integrable (fun ω ↦ ‖Z ω‖ ^ 2) μ := by
    exact hZ.integrable_norm_pow'
  have hinner : Integrable (fun ω ↦ ⟪a, Z ω⟫_ℝ) μ := hZint.const_inner a
  have hdecomp :
      (∫ ω, ‖Z ω - a‖ ^ 2 ∂μ) =
        (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - ‖m‖ ^ 2 + ‖a - m‖ ^ 2 := by
    calc
      (∫ ω, ‖Z ω - a‖ ^ 2 ∂μ)
          = ∫ ω, (‖Z ω‖ ^ 2 - 2 * ⟪a, Z ω⟫_ℝ + ‖a‖ ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self]
              simp only [real_inner_comm, real_inner_self_eq_norm_sq]
      _ = (∫ ω, (‖Z ω‖ ^ 2 - 2 * ⟪a, Z ω⟫_ℝ) ∂μ) +
            ∫ _ω, ‖a‖ ^ 2 ∂μ := by
              simpa only [Pi.add_apply, Pi.sub_apply] using
                integral_add (hnormZ.sub (hinner.const_mul 2))
                  (integrable_const (μ := μ) (c := ‖a‖ ^ 2))
      _ = (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - 2 * (∫ ω, ⟪a, Z ω⟫_ℝ ∂μ) + ‖a‖ ^ 2 := by
            rw [integral_sub hnormZ (hinner.const_mul 2), integral_const_mul]
            simp
      _ = (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - ‖m‖ ^ 2 + ‖a - m‖ ^ 2 := by
            rw [integral_inner hZint]
            simp only [m]
            rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
              ← real_inner_self_eq_norm_sq]
            simp only [real_inner_sub_sub_self]
            ring
  rw [integral_norm_sub_mean_sq hZ, hdecomp]
  exact le_add_of_nonneg_right (sq_nonneg ‖a - m‖)

/-- The vector Pythagorean identity for independent centered sums.

For a finite independent family of mean-zero square-integrable random vectors,
the expected squared Euclidean norm of the sum is the sum of the expected
squared norms.

**Book Exercise 0.3.** This is a load-bearing exercise:
the proof of Theorem 0.0.2 invokes it in the mean-square computation.
-/
theorem integral_norm_sum_sq_of_iIndepFun
    {ι : Type*} [Fintype ι] {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    [IsProbabilityMeasure μ]
    {Z : ι → Ω → EuclideanSpace ℝ (Fin n)}
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hindep : Set.Pairwise Set.univ fun i j ↦ IndepFun (Z i) (Z j) μ) :
    (∫ ω, ‖(∑ i, Z i) ω‖ ^ 2 ∂μ) =
      ∑ i, ∫ ω, ‖Z i ω‖ ^ 2 ∂μ := by
  classical
  have hcoordMem : ∀ i (r : Fin n), MemLp (fun ω ↦ Z i ω r) 2 μ := by
    intro i r
    simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using
      (hZ i).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) r)
  have hcoordMean : ∀ i (r : Fin n), ∫ ω, Z i ω r ∂μ = 0 := by
    intro i r
    have hcomm := (EuclideanSpace.proj (𝕜 := ℝ) r).integral_comp_comm
      ((hZ i).integrable one_le_two)
    simpa only [Function.comp_apply, EuclideanSpace.coe_proj, hmean i, map_zero] using hcomm
  have hcoordIndep : ∀ r : Fin n,
      Set.Pairwise Set.univ fun i j ↦ IndepFun (fun ω ↦ Z i ω r) (fun ω ↦ Z j ω r) μ := by
    intro r i _ j _ hij
    exact (hindep (Set.mem_univ i) (Set.mem_univ j) hij).comp
      (EuclideanSpace.proj (𝕜 := ℝ) r).continuous.measurable
      (EuclideanSpace.proj (𝕜 := ℝ) r).continuous.measurable
  have hcoordinate (r : Fin n) :
      (∫ ω, ((∑ i, fun ω ↦ Z i ω r) ω) ^ 2 ∂μ) =
        ∑ i, ∫ ω, (Z i ω r) ^ 2 ∂μ := by
    have hvar := IndepFun.variance_sum
      (s := Finset.univ) (fun i _ ↦ hcoordMem i r)
      (fun i _ j _ hij ↦ hcoordIndep r (Set.mem_univ i) (Set.mem_univ j) hij)
    have hsumMean : ∫ ω, (∑ i, fun ω ↦ Z i ω r) ω ∂μ = 0 := by
      calc
        (∫ ω, (∑ i, fun ω ↦ Z i ω r) ω ∂μ)
            = ∫ ω, ∑ i, Z i ω r ∂μ := by
                apply integral_congr_ae
                filter_upwards [] with ω
                simp
        _ = ∑ i, ∫ ω, Z i ω r ∂μ := by
              rw [integral_finsetSum Finset.univ
                (fun i _ ↦ (hcoordMem i r).integrable one_le_two)]
        _ = 0 := by simp only [hcoordMean, Finset.sum_const_zero]
    have hvar' :
        Var[∑ i, fun ω ↦ Z i ω r; μ] = ∑ i, Var[fun ω ↦ Z i ω r; μ] := by
      simpa only [Finset.sum_const_zero] using hvar
    rw [variance_eq_integral] at hvar'
    · rw [hsumMean] at hvar'
      simp only [sub_zero] at hvar'
      refine hvar'.trans ?_
      apply Finset.sum_congr rfl
      intro i _
      rw [variance_eq_integral (hcoordMem i r).aemeasurable, hcoordMean]
      simp
    · exact (memLp_finsetSum' Finset.univ (fun i _ ↦ hcoordMem i r)).aemeasurable
  calc
    (∫ ω, ‖(∑ i, Z i) ω‖ ^ 2 ∂μ)
        = ∫ ω, ∑ r : Fin n, ((∑ i, fun ω ↦ Z i ω r) ω) ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            rw [EuclideanSpace.real_norm_sq_eq]
            apply Finset.sum_congr rfl
            intro r _
            congr 1
            simp
    _ = ∑ r : Fin n, ∫ ω, ((∑ i, fun ω ↦ Z i ω r) ω) ^ 2 ∂μ := by
          rw [integral_finsetSum Finset.univ]
          intro r _
          exact (memLp_finsetSum' Finset.univ (fun i _ ↦ hcoordMem i r)).integrable_sq
    _ = ∑ r : Fin n, ∑ i, ∫ ω, (Z i ω r) ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro r _
          exact hcoordinate r
    _ = ∑ i, ∑ r : Fin n, ∫ ω, (Z i ω r) ^ 2 ∂μ :=
          Finset.sum_comm
    _ = ∑ i, ∫ ω, ∑ r : Fin n, (Z i ω r) ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_finsetSum Finset.univ]
          intro r _
          exact (hcoordMem i r).integrable_sq
    _ = ∑ i, ∫ ω, ‖Z i ω‖ ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [EuclideanSpace.real_norm_sq_eq]

/-- The approximate Carathéodory theorem.

If `T` lies in the Euclidean unit ball, every point of `conv(T)` is within
`1 / sqrt k` of an equal-weight average of `k` points of `T`.

**Book Theorem 0.0.2.** The proof is the empirical
method from the book: represent `x` as the mean of a finitely supported random
vector, take `k` independent copies, and apply the preceding second-moment
identities.
-/
theorem approximate_caratheodory {n k : ℕ} (hk : 0 < k)
    {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : T ⊆ Metric.closedBall 0 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ T) :
    ∃ y : Fin k → EuclideanSpace ℝ (Fin n),
      (∀ i, y i ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ i, y i‖ ≤ 1 / Real.sqrt k := by
  classical
  rw [mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, inst, w, z, hw, hwsum, hz, hxsum⟩
  letI : Fintype ι := inst
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  have hpsum : ∑ i, ENNReal.ofReal (w i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw i), hwsum]
    norm_num
  let p : PMF ι := PMF.ofFintype (fun i ↦ ENNReal.ofReal (w i)) hpsum
  have hzmean : ∫ i, z i ∂p.toMeasure = x := by
    rw [PMF.integral_eq_sum]
    simpa [p, ENNReal.toReal_ofReal (hw _)] using hxsum
  let μ : Measure (Fin k → ι) := Measure.pi (fun _ ↦ p.toMeasure)
  let Z : Fin k → (Fin k → ι) → EuclideanSpace ℝ (Fin n) := fun j ω ↦ z (ω j) - x
  have hZmem : ∀ j, MemLp (Z j) 2 μ := by
    intro j
    exact MemLp.of_discrete
  have hZmean : ∀ j, ∫ ω, Z j ω ∂μ = 0 := by
    intro j
    rw [show Z j = fun ω ↦ (fun i ↦ z i - x) (ω j) by rfl]
    rw [← MeasureTheory.integral_map]
    · rw [(measurePreserving_eval (fun _ : Fin k ↦ p.toMeasure) j).map_eq]
      rw [integral_sub (Integrable.of_finite (f := z))
        (integrable_const (μ := p.toMeasure) (c := x))]
      simp [hzmean]
    · exact Measurable.aemeasurable (measurable_pi_apply j)
    · exact AEMeasurable.aestronglyMeasurable (Measurable.of_discrete.aemeasurable)
  have hZi : iIndepFun (fun j ω ↦ Z j ω) μ := by
    exact iIndepFun_pi (Ω := fun _ : Fin k ↦ ι)
      (𝓧 := fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n))
      (μ := fun _ : Fin k ↦ p.toMeasure) (X := fun _ i ↦ z i - x)
      (fun _ ↦ (measurable_of_finite (fun i ↦ z i - x)).aemeasurable)
  have hpair : Set.Pairwise Set.univ fun i j ↦ IndepFun (Z i) (Z j) μ := by
    intro i _ j _ hij
    exact hZi.indepFun hij
  have hsumsq := integral_norm_sum_sq_of_iIndepFun hZmem hZmean hpair
  have hsecond : ∀ j, (∫ ω, ‖Z j ω‖ ^ 2 ∂μ) ≤ 1 := by
    intro j
    have hmap : (∫ ω, ‖Z j ω‖ ^ 2 ∂μ) = ∫ i, ‖z i - x‖ ^ 2 ∂p.toMeasure := by
      change (∫ ω, (fun i ↦ ‖z i - x‖ ^ 2) (ω j) ∂μ) = _
      calc
        _ = ∫ i, ‖z i - x‖ ^ 2 ∂Measure.map (fun ω ↦ ω j) μ := by
          exact (MeasureTheory.integral_map (μ := μ)
            (φ := fun ω : Fin k → ι ↦ ω j) (f := fun i ↦ ‖z i - x‖ ^ 2)
            (measurable_pi_apply j).aemeasurable AEStronglyMeasurable.of_discrete).symm
        _ = _ := by rw [(measurePreserving_eval (fun _ : Fin k ↦ p.toMeasure) j).map_eq]
    rw [hmap]
    calc
      (∫ i, ‖z i - x‖ ^ 2 ∂p.toMeasure)
          = (∫ i, ‖z i‖ ^ 2 ∂p.toMeasure) - ‖x‖ ^ 2 := by
              simpa [hzmean] using
                (integral_norm_sub_mean_sq (μ := p.toMeasure)
                  (Z := z) (MemLp.of_discrete : MemLp z 2 p.toMeasure))
      _ ≤ ∫ i, ‖z i‖ ^ 2 ∂p.toMeasure := sub_le_self _ (sq_nonneg ‖x‖)
      _ ≤ ∫ _i, (1 : ℝ) ∂p.toMeasure := by
            apply integral_mono (MemLp.of_discrete.integrable_sq) (integrable_const 1)
            intro i
            have hzi : ‖z i‖ ≤ 1 := by
              simpa [Metric.mem_closedBall, dist_zero_right] using hT (hz i)
            nlinarith [norm_nonneg (z i)]
      _ = 1 := by simp
  have hsumle : (∫ ω, ‖(∑ j, Z j) ω‖ ^ 2 ∂μ) ≤ k := by
    rw [hsumsq]
    calc
      (∑ j, ∫ ω, ‖Z j ω‖ ^ 2 ∂μ) ≤ ∑ _j : Fin k, (1 : ℝ) := by
        exact Finset.sum_le_sum fun j _ ↦ hsecond j
      _ = k := by simp
  have hsumMem : MemLp (∑ j, Z j) 2 μ :=
    memLp_finsetSum' Finset.univ (fun j _ ↦ hZmem j)
  have hsumInt : Integrable (fun ω ↦ ‖(∑ j, Z j) ω‖ ^ 2) μ := by
    exact hsumMem.integrable_norm_pow'
  obtain ⟨ω, hω⟩ := exists_le_integral hsumInt
  have hωk : ‖(∑ j, Z j) ω‖ ^ 2 ≤ k := hω.trans hsumle
  refine ⟨fun j ↦ z (ω j), fun j ↦ hz (ω j), ?_⟩
  have hsumid : (∑ j, Z j) ω = (∑ j, z (ω j)) - k • x := by
    simp only [Finset.sum_apply, Z, Finset.sum_sub_distrib]
    simp
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkreal
  have hinv : (1 : ℝ) = (k : ℝ) * (k : ℝ)⁻¹ := (mul_inv_cancel₀ hkne).symm
  have herr : x - (k : ℝ)⁻¹ • ∑ j, z (ω j) =
      -((k : ℝ)⁻¹ • (∑ j, Z j) ω) := by
    rw [hsumid, ← Nat.cast_smul_eq_nsmul ℝ k x, smul_sub, smul_smul,
      inv_mul_cancel₀ hkne, one_smul]
    module
  rw [herr, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hkreal]
  have hsqrtpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hsqrtsq : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (le_of_lt hkreal)
  have hnorm : ‖(∑ j, Z j) ω‖ ≤ Real.sqrt (k : ℝ) := by
    nlinarith [norm_nonneg ((∑ j, Z j) ω)]
  rw [one_div]
  exact (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 (le_of_lt hkreal))).trans_eq (by
    field_simp
    nlinarith)

/-- A finite internal cover of a polytope by equal empirical averages.

If a polytope is generated by `N` points in the Euclidean unit ball, then for
every positive `k` it has an internal `1 / sqrt k` cover with at most `N^k`
centers. The returned finset is the explicit set of all equal-weight empirical
averages of `k` vertices.

**Book Corollary 0.0.3.**
-/
theorem exists_polytope_cover {n k : ℕ} (hk : 0 < k)
    (V : Finset (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
      C.card ≤ V.card ^ k ∧
      (C : Set (EuclideanSpace ℝ (Fin n))) ⊆
        convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) ∧
      Metric.IsCover ⟨1 / Real.sqrt k, by positivity⟩
        (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))))
        (C : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  let avg : (Fin k → ↥V) → EuclideanSpace ℝ (Fin n) :=
    fun y ↦ (k : ℝ)⁻¹ • ∑ i, (y i : EuclideanSpace ℝ (Fin n))
  let C := Finset.univ.image avg
  refine ⟨C, ?_, ?_, ?_⟩
  · calc
      C.card ≤ (Finset.univ : Finset (Fin k → ↥V)).card := Finset.card_image_le
      _ = V.card ^ k := by simp
  · intro c hc
    simp only [C, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨y, rfl⟩
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have hw : ∑ _i : Fin k, (k : ℝ)⁻¹ = 1 := by simp [ne_of_gt hkreal]
    have hm :=
      (convex_convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))).sum_mem
        (t := Finset.univ) (w := fun _i : Fin k ↦ (k : ℝ)⁻¹)
        (z := fun i ↦ (y i : EuclideanSpace ℝ (Fin n)))
        (fun _ _ ↦ inv_nonneg.2 hkreal.le) hw
        (fun i _ ↦ subset_convexHull ℝ _ (y i).property)
    simpa [avg, Finset.smul_sum] using hm
  · intro x hx
    have hsub : (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.closedBall 0 1 := by
      intro v hv
      exact hV v hv
    obtain ⟨y, hy, hxy⟩ := approximate_caratheodory hk hsub hx
    let ys : Fin k → ↥V := fun i ↦ ⟨y i, hy i⟩
    refine ⟨avg ys, ?_, ?_⟩
    · simp [C]
    · simpa [avg, ys, edist_dist, dist_eq_norm] using (show
        ‖x - (k : ℝ)⁻¹ • ∑ i, y i‖₊ ≤
          ⟨1 / Real.sqrt k, by positivity⟩ from by exact_mod_cast hxy)

/-- A finite-cover volume bound used in the polytope-volume argument.

**Lean implementation helper.** -/
private theorem volume_le_card_mul_ball {n : ℕ} [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))}
    {C : Finset (EuclideanSpace ℝ (Fin n))} {r : ℝ}
    (hcover : K ⊆ ⋃ c ∈ C, Metric.closedBall c r) :
    volume K ≤ (C.card : ℝ≥0∞) *
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r) := by
  calc
    volume K ≤ volume (⋃ c ∈ C, Metric.closedBall c r) := measure_mono hcover
    _ ≤ ∑ c ∈ C, volume (Metric.closedBall c r) :=
      measure_biUnion_finset_le C (fun c ↦ Metric.closedBall c r)
    _ = _ := by simp [EuclideanSpace.volume_closedBall]

/-- The covering argument before rewriting the radius scaling in equation
(0.3).

**Book Equation (0.3).** -/
theorem polytope_volume_le_card_mul_ball {n k : ℕ} [NeZero n] (hk : 0 < k)
    (V : Finset (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    volume (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) ≤
      (V.card ^ k : ℕ) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / Real.sqrt k)) := by
  obtain ⟨C, hcard, _hCsub, hcover⟩ := exists_polytope_cover hk V hV
  have hset : convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) ⊆
      ⋃ c ∈ C, Metric.closedBall c (1 / Real.sqrt k) := by
    intro x hx
    obtain ⟨c, hc, hdist⟩ := hcover hx
    refine Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
    simp only [Metric.mem_closedBall]
    exact_mod_cast hdist
  refine (volume_le_card_mul_ball hset).trans ?_
  gcongr

/-- The polytope-volume estimate in division-free `ℝ≥0∞` form.

This is exactly `Vol(P) ≤ N^k k^{-n/2} Vol(B)` with the factor
`k^{-n/2}` written as the `n`th power of the radius `1 / sqrt k`.

**Book Equation (0.3).**
-/
theorem polytope_volume_equation_0_3 {n k : ℕ} [NeZero n] (hk : 0 < k)
    (V : Finset (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    volume (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) ≤
      (V.card ^ k : ℕ) * (ENNReal.ofReal (1 / Real.sqrt k)) ^ n *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have h := polytope_volume_le_card_mul_ball hk V hV
  rw [EuclideanSpace.volume_closedBall] at h
  rw [EuclideanSpace.volume_closedBall]
  simpa [Fintype.card_fin, mul_assoc] using h

/-- The positive critical point of the logarithm of `N^k / k^(n/2)` is
`k₀ = n / (2 log N)`.

**Book Equation (0.4).** -/
theorem polytope_volume_optimizer_equation_0_4 {n N : ℝ}
    (hn : 0 < n) (hlog : 0 < Real.log N) :
    0 < n / (2 * Real.log N) ∧
      Real.log N - n / (2 * (n / (2 * Real.log N))) = 0 := by
  constructor
  · positivity
  · field_simp
    ring

/-- The positive solution of the critical-point equation is unique.

**Book Equation (0.4).** -/
theorem polytope_volume_optimizer_unique {n N k : ℝ} (hk : 0 < k)
    (hlog : 0 < Real.log N)
    (hcrit : Real.log N - n / (2 * k) = 0) :
    k = n / (2 * Real.log N) := by
  have hkn : k ≠ 0 := ne_of_gt hk
  have hln : Real.log N ≠ 0 := ne_of_gt hlog
  field_simp [hkn, hln] at hcrit ⊢
  nlinarith

/-- The numerical constant needed after rounding the continuous optimizer in
the proof of Theorem 0.0.4.

**Lean implementation helper.** -/
private theorem exp_eleven_eighteenths_mul_sqrt_two_le_three :
    Real.exp (11 / 18 : ℝ) * Real.sqrt 2 ≤ 3 := by
  have hexpTwoNinths : Real.exp (2 / 9 : ℝ) ≤ 9 / 7 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (x := (2 / 9 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hexpElevenNinths : Real.exp (11 / 9 : ℝ) < 9 / 2 := by
    rw [show (11 / 9 : ℝ) = 1 + 2 / 9 by norm_num, Real.exp_add]
    calc
      Real.exp 1 * Real.exp (2 / 9 : ℝ)
          ≤ Real.exp 1 * (9 / 7) :=
            mul_le_mul_of_nonneg_left hexpTwoNinths (Real.exp_pos 1).le
      _ < (2.7182818286 : ℝ) * (9 / 7) :=
            mul_lt_mul_of_pos_right Real.exp_one_lt_d9 (by norm_num)
      _ < 9 / 2 := by norm_num
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq :
      (Real.exp (11 / 18 : ℝ) * Real.sqrt 2) ^ 2 < 9 := by
    rw [mul_pow, hsqrt, ← Real.exp_nat_mul]
    norm_num
    simpa [show (2 : ℝ) * (11 / 18) = 11 / 9 by norm_num] using
      (mul_lt_mul_of_pos_right hexpElevenNinths (by norm_num : (0 : ℝ) < 2))
  nlinarith [Real.exp_pos (11 / 18 : ℝ), Real.sqrt_nonneg (2 : ℝ)]

/-- The rounded optimization step in Theorem 0.0.4.

For `k = ⌈n / (2 log N)⌉`, equation (0.3)'s real coefficient is bounded by
the claimed coefficient whenever `2 ≤ N` and `log N ≤ n / 9`.

**Lean implementation helper.**
-/
private theorem rounded_polytope_coefficient_le
    {n N : ℕ} (hn : 0 < n) (hN : 2 ≤ N)
    (hsmall : Real.log (N : ℝ) ≤ (n : ℝ) / 9) :
    let k := ⌈(n : ℝ) / (2 * Real.log (N : ℝ))⌉₊
    (N : ℝ) ^ k * (1 / Real.sqrt (k : ℝ)) ^ n ≤
      (3 * Real.sqrt (Real.log (N : ℝ) / n)) ^ n := by
  dsimp only
  let k₀ : ℝ := (n : ℝ) / (2 * Real.log (N : ℝ))
  let k : ℕ := ⌈k₀⌉₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hNR
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hk₀ : 0 < k₀ := by
    dsimp [k₀]
    positivity
  have hk : 0 < k := Nat.ceil_pos.mpr hk₀
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk₀le : k₀ ≤ (k : ℝ) := Nat.le_ceil k₀
  have hklt : (k : ℝ) < k₀ + 1 := Nat.ceil_lt_add_one hk₀.le
  have hklog :
      Real.log (N : ℝ) * (k : ℝ) ≤ (11 / 18 : ℝ) * n := by
    have hlt :
        Real.log (N : ℝ) * (k : ℝ) <
          Real.log (N : ℝ) * (k₀ + 1) :=
      mul_lt_mul_of_pos_left hklt hlog
    have hk₀eval :
        Real.log (N : ℝ) * (k₀ + 1) =
          (n : ℝ) / 2 + Real.log (N : ℝ) := by
      dsimp [k₀]
      field_simp [ne_of_gt hlog]
    rw [hk₀eval] at hlt
    nlinarith
  have hNpow :
      (N : ℝ) ^ k ≤ Real.exp (11 / 18 : ℝ) ^ n := by
    calc
      (N : ℝ) ^ k = Real.exp (Real.log (N : ℝ)) ^ k := by
        rw [Real.exp_log hNpos]
      _ = Real.exp ((k : ℝ) * Real.log (N : ℝ)) :=
        (Real.exp_nat_mul _ _).symm
      _ = Real.exp (Real.log (N : ℝ) * (k : ℝ)) := by
        congr 1
        ring
      _ ≤ Real.exp ((11 / 18 : ℝ) * n) :=
        Real.exp_le_exp.mpr hklog
      _ = Real.exp (11 / 18 : ℝ) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hinv :
      ((k : ℝ))⁻¹ ≤ 2 * Real.log (N : ℝ) / n := by
    have h := one_div_le_one_div_of_le hk₀ hk₀le
    rw [one_div, one_div] at h
    calc
      ((k : ℝ))⁻¹ ≤ k₀⁻¹ := h
      _ = 2 * Real.log (N : ℝ) / n := by
        dsimp [k₀]
        field_simp [ne_of_gt hlog, ne_of_gt hnR]
  have hradius :
      1 / Real.sqrt (k : ℝ) ≤
        Real.sqrt (2 * Real.log (N : ℝ) / n) := by
    have h := Real.sqrt_le_sqrt hinv
    rw [Real.sqrt_inv] at h
    simpa [one_div] using h
  have hradiusPow :
      (1 / Real.sqrt (k : ℝ)) ^ n ≤
        Real.sqrt (2 * Real.log (N : ℝ) / n) ^ n :=
    pow_le_pow_left₀ (by positivity) hradius n
  have hbase :
      Real.exp (11 / 18 : ℝ) *
          Real.sqrt (2 * Real.log (N : ℝ) / n) ≤
        3 * Real.sqrt (Real.log (N : ℝ) / n) := by
    have ha : 0 ≤ Real.log (N : ℝ) / n := by positivity
    have hsqrt :
        Real.sqrt (2 * Real.log (N : ℝ) / n) =
          Real.sqrt 2 * Real.sqrt (Real.log (N : ℝ) / n) := by
      rw [show 2 * Real.log (N : ℝ) / n =
        2 * (Real.log (N : ℝ) / n) by ring, Real.sqrt_mul (by norm_num)]
    rw [hsqrt]
    calc
      Real.exp (11 / 18 : ℝ) *
            (Real.sqrt 2 * Real.sqrt (Real.log (N : ℝ) / n)) =
          (Real.exp (11 / 18 : ℝ) * Real.sqrt 2) *
            Real.sqrt (Real.log (N : ℝ) / n) := by ring
      _ ≤ 3 * Real.sqrt (Real.log (N : ℝ) / n) :=
        mul_le_mul_of_nonneg_right
          exp_eleven_eighteenths_mul_sqrt_two_le_three (Real.sqrt_nonneg _)
  calc
    (N : ℝ) ^ k * (1 / Real.sqrt (k : ℝ)) ^ n
        ≤ Real.exp (11 / 18 : ℝ) ^ n *
            Real.sqrt (2 * Real.log (N : ℝ) / n) ^ n :=
      mul_le_mul hNpow hradiusPow (by positivity) (by positivity)
    _ = (Real.exp (11 / 18 : ℝ) *
        Real.sqrt (2 * Real.log (N : ℝ) / n)) ^ n := by rw [mul_pow]
    _ ≤ (3 * Real.sqrt (Real.log (N : ℝ) / n)) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n

/-- The polytope-volume theorem in multiplication form.

If the finite vertex set `V` lies in the Euclidean unit ball of `ℝⁿ`, then
the volume of its convex hull is at most
`(3 * sqrt (log |V| / n))^n` times the volume of the unit ball.

The proof uses equation (0.3) with the integer
`k = ⌈n / (2 log |V|)⌉` when `2 ≤ |V|` and `log |V| ≤ n / 9`.
It uses the trivial inclusion in the unit ball in the complementary range,
exactly as in the source. The empty and singleton vertex sets are handled
separately; both convex hulls have zero `n`-dimensional volume because `n > 0`.

**Book Theorem 0.0.4.**
-/
theorem polytope_volume_le_theorem_0_0_4 {n : ℕ} [NeZero n]
    (V : Finset (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, v ∈ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) :
    volume (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) ≤
      ENNReal.ofReal
          ((3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n) *
        volume (Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hN : 2 ≤ V.card
  · by_cases hsmall : Real.log (V.card : ℝ) ≤ (n : ℝ) / 9
    · let k : ℕ :=
        ⌈(n : ℝ) / (2 * Real.log (V.card : ℝ))⌉₊
      have hlog : 0 < Real.log (V.card : ℝ) :=
        Real.log_pos (by exact_mod_cast hN)
      have hk₀ : 0 <
          (n : ℝ) / (2 * Real.log (V.card : ℝ)) := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      have hk : 0 < k := Nat.ceil_pos.mpr hk₀
      have hvolume := polytope_volume_equation_0_3 hk V hV
      have hcoefficientReal :
          (V.card : ℝ) ^ k *
              (1 / Real.sqrt (k : ℝ)) ^ n ≤
            (3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n := by
        simpa only [k] using
          rounded_polytope_coefficient_le hn hN hsmall
      have hcoefficientENN :
          (V.card ^ k : ℕ) *
              (ENNReal.ofReal (1 / Real.sqrt k)) ^ n ≤
            ENNReal.ofReal
              ((3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n) := by
        calc
          (V.card ^ k : ℕ) *
                (ENNReal.ofReal (1 / Real.sqrt k)) ^ n =
              ENNReal.ofReal ((V.card : ℝ) ^ k) *
                (ENNReal.ofReal (1 / Real.sqrt k)) ^ n := by
                  rw [ENNReal.ofReal_pow
                    (by positivity : (0 : ℝ) ≤ V.card),
                    ENNReal.ofReal_natCast]
                  norm_cast
          _ = ENNReal.ofReal ((V.card : ℝ) ^ k) *
                ENNReal.ofReal ((1 / Real.sqrt (k : ℝ)) ^ n) := by
                  rw [ENNReal.ofReal_pow (by positivity :
                    (0 : ℝ) ≤ 1 / Real.sqrt (k : ℝ))]
          _ = ENNReal.ofReal
                ((V.card : ℝ) ^ k *
                  (1 / Real.sqrt (k : ℝ)) ^ n) := by
                  rw [ENNReal.ofReal_mul
                    (by positivity : (0 : ℝ) ≤ (V.card : ℝ) ^ k)]
          _ ≤ ENNReal.ofReal
                ((3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n) :=
              ENNReal.ofReal_le_ofReal hcoefficientReal
      exact hvolume.trans
        (by
          simpa [mul_comm] using
            mul_le_mul_left
              hcoefficientENN
              (volume (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) 1)))
    · have hlarge :
          (n : ℝ) / 9 < Real.log (V.card : ℝ) := lt_of_not_ge hsmall
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hratio : (1 / 9 : ℝ) <
          Real.log (V.card : ℝ) / n := by
        rw [lt_div_iff₀ hnR]
        nlinarith
      have hsqrt : (1 / 3 : ℝ) <
          Real.sqrt (Real.log (V.card : ℝ) / n) := by
        have hsqrtone : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
          rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num,
            Real.sqrt_sq_eq_abs]
          norm_num
        rw [← hsqrtone]
        exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 9) hratio
      have hbase :
          (1 : ℝ) ≤
            3 * Real.sqrt (Real.log (V.card : ℝ) / n) := by
        nlinarith
      have hcoeff :
          (1 : ℝ) ≤
            (3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbase n
      have hcoeffENN :
          (1 : ℝ≥0∞) ≤ ENNReal.ofReal
            ((3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hcoeff
      have hsubset :
          convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) ⊆
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        convexHull_min (by
          intro v hv
          exact hV v hv) (convex_closedBall 0 1)
      calc
        volume (convexHull ℝ
            (V : Set (EuclideanSpace ℝ (Fin n))))
            ≤ volume (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) 1) :=
          measure_mono hsubset
        _ = 1 * volume (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) 1) := by simp
        _ ≤ ENNReal.ofReal
                ((3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n) *
              volume (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin n)) 1) :=
          by
            simpa [mul_comm] using
              mul_le_mul_left
                hcoeffENN
                (volume (Metric.closedBall
                  (0 : EuclideanSpace ℝ (Fin n)) 1))
  · have hcard : V.card = 0 ∨ V.card = 1 := by omega
    rcases hcard with hcard | hcard
    · have hVempty : V = ∅ := Finset.card_eq_zero.mp hcard
      subst V
      simp
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      simp

/-- The polytope-volume theorem in the relative-volume form displayed as
equation (0.2).

The denominator is nonzero and finite because it is the volume of the
positive-radius closed unit ball.

**Book Theorem 0.0.4 and Equation (0.2).**
-/
theorem polytope_volume_theorem_0_0_4 {n : ℕ} [NeZero n]
    (V : Finset (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, v ∈ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) :
    volume (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))) /
        volume (Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
      ENNReal.ofReal
        ((3 * Real.sqrt (Real.log (V.card : ℝ) / n)) ^ n) := by
  rw [ENNReal.div_le_iff
    (Metric.measure_closedBall_pos volume
      (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'
    measure_closedBall_lt_top.ne]
  exact polytope_volume_le_theorem_0_0_4 V hV

/-- The radius interpretation of subexponential vertex growth.

Here the precise meaning of subexponential vertex growth is
`log (N n) / n → 0`. Under this hypothesis the radius
`3 * sqrt (log (N n) / n)` tends to zero.

**Book Remark 0.0.5.**
-/
theorem polytope_volume_radius_tendsto_zero_of_subexponential
    (N : ℕ → ℕ)
    (hsubexponential :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.log (N n : ℝ) / n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ 3 * Real.sqrt (Real.log (N n : ℝ) / n))
      Filter.atTop (nhds 0) := by
  have hsqrt :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.sqrt (Real.log (N n : ℝ) / n))
        Filter.atTop (nhds 0) := by
    have h :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsubexponential
    have heq :
        (fun x : ℝ ↦ Real.sqrt x) ∘
            (fun n : ℕ ↦ Real.log (N n : ℝ) / n) =
          (fun n : ℕ ↦ Real.sqrt (Real.log (N n : ℝ) / n)) := rfl
    rw [heq, Real.sqrt_zero] at h
    exact h
  simpa using hsqrt.const_mul 3

/-- The volume-coefficient interpretation of subexponential vertex growth.

Under subexponential vertex growth, not only the comparison-ball radius but
also the exact coefficient from Theorem 0.0.4,
`(3 * sqrt (log (N n) / n))^n`, tends to zero.

**Book Remark 0.0.5.**
-/
theorem polytope_volume_coefficient_tendsto_zero_of_subexponential
    (N : ℕ → ℕ)
    (hsubexponential :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.log (N n : ℝ) / n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (3 * Real.sqrt (Real.log (N n : ℝ) / n)) ^ n)
      Filter.atTop (nhds 0) := by
  let r : ℕ → ℝ :=
    fun n ↦ 3 * Real.sqrt (Real.log (N n : ℝ) / n)
  have hr : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa only [r] using
      polytope_volume_radius_tendsto_zero_of_subexponential N hsubexponential
  have heventually : ∀ᶠ n in Filter.atTop, r n < (1 / 2 : ℝ) :=
    (tendsto_order.1 hr).2 (1 / 2) (by norm_num)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ pow_nonneg (by positivity) n
  · filter_upwards [heventually] with n hn
    exact pow_le_pow_left₀ (by positivity) hn.le n
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

/-- Subexponential vertex growth forces both the comparison radius and the
relative-volume coefficient in Theorem 0.0.4 to vanish.

**Book Remark 0.0.5.**
-/
theorem polytope_volume_remark_0_0_5
    (N : ℕ → ℕ)
    (hsubexponential :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.log (N n : ℝ) / n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
        (fun n : ℕ ↦ 3 * Real.sqrt (Real.log (N n : ℝ) / n))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          (3 * Real.sqrt (Real.log (N n : ℝ) / n)) ^ n)
        Filter.atTop (nhds 0) :=
  ⟨polytope_volume_radius_tendsto_zero_of_subexponential N hsubexponential,
    polytope_volume_coefficient_tendsto_zero_of_subexponential N hsubexponential⟩

end HDP.Chapter0
