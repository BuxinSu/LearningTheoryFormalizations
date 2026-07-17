import HighDimensionalProbability.Prelude.Basic
import HighDimensionalProbability.Prelude.MetricEntropy
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

/-- HDP Exercise 0.1(a), vector bias--variance identity.

For a square-integrable random vector `Z` in a real Hilbert space,
`𝔼 ‖Z - 𝔼Z‖² = 𝔼 ‖Z‖² - ‖𝔼Z‖²`.

Source: Appetizer, Exercise 0.1(a), PDF page 5. This is a load-bearing
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

/-- HDP Exercise 0.2, vector form.

The mean of a square-integrable random vector minimizes expected squared
Euclidean distance: for every deterministic center `a`,
`𝔼 ‖Z-𝔼Z‖² ≤ 𝔼 ‖Z-a‖²`.

Source: Appetizer, Exercise 0.2, PDF page 6. The scalar specialization is used
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

/-- HDP Exercise 0.3, the vector Pythagorean identity.

For a finite independent family of mean-zero square-integrable random vectors,
the expected squared Euclidean norm of the sum is the sum of the expected
squared norms.

Source: Appetizer, Exercise 0.3, PDF page 6. This is a load-bearing exercise:
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

/-- HDP Theorem 0.0.2 (approximate Carathéodory theorem).

If `T` lies in the Euclidean unit ball, every point of `conv(T)` is within
`1 / sqrt k` of an equal-weight average of `k` points of `T`.

Source: Appetizer, Theorem 0.0.2, PDF page 2. The proof is the empirical
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

/-- HDP Corollary 0.0.3.

If a polytope is generated by `N` points in the Euclidean unit ball, then for
every positive `k` it has an internal `1 / sqrt k` cover with at most `N^k`
centers. The returned finset is the explicit set of all equal-weight empirical
averages of `k` vertices.

Source: Appetizer, Corollary 0.0.3, PDF page 3.
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

/-- A finite-cover volume bound used in the proof of HDP (0.3). -/
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

/-- The covering argument before rewriting the radius scaling in HDP (0.3). -/
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

/-- HDP equation (0.3), in division-free `ℝ≥0∞` form.

This is exactly `Vol(P) ≤ N^k k^{-n/2} Vol(B)` with the factor
`k^{-n/2}` written as the `n`th power of the radius `1 / sqrt k`.
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

/-- HDP equation (0.4): the positive critical point of the logarithm of
`N^k / k^(n/2)` is `k₀ = n / (2 log N)`. -/
theorem polytope_volume_optimizer_equation_0_4 {n N : ℝ}
    (hn : 0 < n) (hlog : 0 < Real.log N) :
    0 < n / (2 * Real.log N) ∧
      Real.log N - n / (2 * (n / (2 * Real.log N))) = 0 := by
  constructor
  · positivity
  · field_simp
    ring

/-- The positive solution of the critical-point equation in HDP (0.4) is
unique. -/
theorem polytope_volume_optimizer_unique {n N k : ℝ} (hk : 0 < k)
    (hlog : 0 < Real.log N)
    (hcrit : Real.log N - n / (2 * k) = 0) :
    k = n / (2 * Real.log N) := by
  have hkn : k ≠ 0 := ne_of_gt hk
  have hln : Real.log N ≠ 0 := ne_of_gt hlog
  field_simp [hkn, hln] at hcrit ⊢
  nlinarith

end HDP.Chapter0
