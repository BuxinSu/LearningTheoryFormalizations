import HighDimensionalProbability.Chapter7_RandomProcesses
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace HDP.Chapter7.BrownianDiscrete

noncomputable section

/-- The sum of the first `k` coordinates of a finite increment vector. -/
def partialSum {m : ℕ} (x : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ i.1 < k), x i

/-- The endpoint of a finite increment vector. -/
def endpoint {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∑ i, x i

/-- The running maximum of the partial sums, including the initial value zero. -/
def runningMax {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun k : Fin (m + 1) ↦ partialSum x k.1)

/-- The largest absolute increment. -/
def maxAbsStep {m : ℕ} [NeZero m] (x : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |x i|)

/-- Negate all increments after the `k`-th partial sum. -/
def tailFlip {m : ℕ} (k : ℕ) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i ↦ if k ≤ i.1 then -x i else x i

lemma partialSum_zero {m : ℕ} (x : Fin m → ℝ) :
    partialSum x 0 = 0 := by
  simp [partialSum]

lemma partialSum_endpoint {m : ℕ} (x : Fin m → ℝ) :
    partialSum x m = endpoint x := by
  simp [partialSum, endpoint, Finset.filter_true_of_mem]

lemma runningMax_nonneg {m : ℕ} (x : Fin m → ℝ) :
    0 ≤ runningMax x := by
  rw [← partialSum_zero x]
  exact Finset.le_sup'
    (fun k : Fin (m + 1) ↦ partialSum x k.1)
    (Finset.mem_univ (0 : Fin (m + 1)))

lemma endpoint_le_runningMax {m : ℕ} (x : Fin m → ℝ) :
    endpoint x ≤ runningMax x := by
  rw [← partialSum_endpoint x]
  exact Finset.le_sup'
    (fun k : Fin (m + 1) ↦ partialSum x k.1)
    (Finset.mem_univ (Fin.last m))

lemma measurable_partialSum {m : ℕ} (k : ℕ) :
    Measurable (fun x : Fin m → ℝ ↦ partialSum x k) := by
  unfold partialSum
  fun_prop

lemma measurable_endpoint {m : ℕ} :
    Measurable (endpoint : (Fin m → ℝ) → ℝ) := by
  unfold endpoint
  fun_prop

lemma measurable_runningMax {m : ℕ} :
    Measurable (runningMax : (Fin m → ℝ) → ℝ) := by
  unfold runningMax
  rw [show
    (fun x : Fin m → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin (m + 1) ↦ partialSum x k.1)) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) ↦ fun x ↦ partialSum x k.1) by
    funext x
    exact (Finset.sup'_apply Finset.univ_nonempty _ x).symm]
  exact Finset.measurable_sup' Finset.univ_nonempty
    (fun (i : Fin (m + 1)) _ ↦ measurable_partialSum i.1)

lemma measurable_maxAbsStep {m : ℕ} [NeZero m] :
    Measurable (maxAbsStep : (Fin m → ℝ) → ℝ) := by
  unfold maxAbsStep
  rw [show
    (fun x : Fin m → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin m ↦ |x i|)) =
      Finset.univ.sup' (Finset.univ_nonempty (α := Fin m))
        (fun i : Fin m ↦ fun x ↦ |x i|) by
    funext x
    exact (Finset.sup'_apply (Finset.univ_nonempty (α := Fin m))
      (fun i : Fin m ↦ fun x : Fin m → ℝ ↦ |x i|) x).symm]
  exact Finset.measurable_sup' (Finset.univ_nonempty (α := Fin m))
    (fun (i : Fin m) _ ↦
      (measurable_pi_apply i : Measurable
        (fun x : Fin m → ℝ ↦ x i)).abs)

lemma measurable_tailFlip {m : ℕ} (k : ℕ) :
    Measurable (tailFlip k : (Fin m → ℝ) → (Fin m → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  change Measurable
    (fun x : Fin m → ℝ ↦ if k ≤ i.1 then -x i else x i)
  by_cases h : k ≤ i.1
  · simpa only [if_pos h] using
      (measurable_pi_apply i : Measurable
        (fun x : Fin m → ℝ ↦ x i)).neg
  · simpa only [if_neg h] using
      (measurable_pi_apply i : Measurable
        (fun x : Fin m → ℝ ↦ x i))

lemma partialSum_tailFlip_of_le {m : ℕ} {j k : ℕ} (hjk : j ≤ k)
    (x : Fin m → ℝ) :
    partialSum (tailFlip k x) j = partialSum x j := by
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i.1 < j := (Finset.mem_filter.1 hi).2
  have hik : ¬k ≤ i.1 := by omega
  simp [tailFlip, hik]

lemma tailFlip_involutive {m : ℕ} (k : ℕ) :
    Function.Involutive (tailFlip k : (Fin m → ℝ) → (Fin m → ℝ)) := by
  intro x
  funext i
  by_cases h : k ≤ i.1 <;> simp [tailFlip, h]

lemma maxAbsStep_tailFlip {m : ℕ} [NeZero m] (k : ℕ)
    (x : Fin m → ℝ) :
    maxAbsStep (tailFlip k x) = maxAbsStep x := by
  unfold maxAbsStep
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [show |tailFlip k x i| = |x i| by
      by_cases h : k ≤ i.1 <;> simp [tailFlip, h]]
    exact Finset.le_sup' (fun j : Fin m ↦ |x j|)
      (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i _
    rw [show |x i| = |tailFlip k x i| by
      by_cases h : k ≤ i.1 <;> simp [tailFlip, h]]
    exact Finset.le_sup' (fun j : Fin m ↦ |tailFlip k x j|)
      (Finset.mem_univ i)

lemma maxAbsStep_nonneg {m : ℕ} [NeZero m] (x : Fin m → ℝ) :
    0 ≤ maxAbsStep x := by
  let i : Fin m := Classical.choice inferInstance
  exact (abs_nonneg (x i)).trans
    (Finset.le_sup' (fun j : Fin m ↦ |x j|) (Finset.mem_univ i))

lemma abs_le_maxAbsStep {m : ℕ} [NeZero m] (x : Fin m → ℝ)
    (i : Fin m) :
    |x i| ≤ maxAbsStep x :=
  Finset.le_sup' (fun j : Fin m ↦ |x j|) (Finset.mem_univ i)

lemma partialSum_succ {m k : ℕ} (x : Fin m → ℝ) (hk : k < m) :
    partialSum x (k + 1) = partialSum x k + x ⟨k, hk⟩ := by
  unfold partialSum
  have hfilter :
      Finset.univ.filter (fun i : Fin m ↦ i.1 < k + 1) =
        insert ⟨k, hk⟩
          (Finset.univ.filter (fun i : Fin m ↦ i.1 < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hi
      by_cases hik : i.1 = k
      · exact Or.inl (Fin.ext hik)
      · exact Or.inr (by omega)
    · rintro (hi | hi)
      · subst i
        exact Nat.lt_succ_self k
      · omega
  rw [hfilter, Finset.sum_insert (by simp)]
  abel

lemma endpoint_eq_partial_add_tail {m : ℕ} (x : Fin m → ℝ) (k : ℕ) :
    endpoint x =
      partialSum x k +
        ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.1), x i := by
  unfold endpoint partialSum
  calc
    (∑ i, x i) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ i.1 < k), x i) +
          ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ ¬i.1 < k), x i :=
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin m))
        (fun i : Fin m ↦ i.1 < k) x).symm
    _ = (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ i.1 < k), x i) +
          ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.1), x i := by
      congr 1
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro
        simp

lemma endpoint_tailFlip {m : ℕ} (x : Fin m → ℝ) (k : ℕ) :
    endpoint (tailFlip k x) = 2 * partialSum x k - endpoint x := by
  rw [endpoint_eq_partial_add_tail (tailFlip k x) k,
    partialSum_tailFlip_of_le le_rfl,
    endpoint_eq_partial_add_tail x k]
  have htail :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.1),
          tailFlip k x i) =
        -∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.1), x i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : k ≤ i.1 := (Finset.mem_filter.1 hi).2
    simp [tailFlip, hik]
  rw [htail]
  ring

/-- The first-crossing event at a deterministic finite-grid time. -/
def hitAt {m : ℕ} (a : ℝ) (k : Fin (m + 1))
    (x : Fin m → ℝ) : Prop :=
  a < partialSum x k.1 ∧
    ∀ j : ℕ, j < k.1 → partialSum x j ≤ a

lemma measurableSet_hitAt {m : ℕ} (a : ℝ) (k : Fin (m + 1)) :
    MeasurableSet {x : Fin m → ℝ | hitAt a k x} := by
  rw [show {x : Fin m → ℝ | hitAt a k x} =
      {x | a < partialSum x k.1} ∩
        ⋂ j : ℕ, {x | j < k.1 → partialSum x j ≤ a} by
    ext x
    simp [hitAt]]
  refine (measurableSet_lt measurable_const
      (measurable_partialSum (m := m) k.1)).inter
    (MeasurableSet.iInter fun j ↦ ?_)
  by_cases hj : j < k.1
  · simpa [hj] using
      (measurableSet_le (measurable_partialSum (m := m) j)
        measurable_const)
  · simp [hj]

lemma hitAt_tailFlip_iff {m : ℕ} (a : ℝ) (k : Fin (m + 1))
    (x : Fin m → ℝ) :
    hitAt a k (tailFlip k.1 x) ↔ hitAt a k x := by
  simp only [hitAt, partialSum_tailFlip_of_le le_rfl]
  constructor
  · rintro ⟨hk, hbefore⟩
    refine ⟨hk, fun j hj ↦ ?_⟩
    have h := hbefore j hj
    rw [partialSum_tailFlip_of_le (Nat.le_of_lt hj)] at h
    exact h
  · rintro ⟨hk, hbefore⟩
    refine ⟨hk, fun j hj ↦ ?_⟩
    rw [partialSum_tailFlip_of_le (Nat.le_of_lt hj)]
    exact hbefore j hj

lemma hitAt_partialSum_le_add_maxAbsStep {m : ℕ} [NeZero m]
    {a : ℝ} (ha : 0 < a) (k : Fin (m + 1)) (x : Fin m → ℝ)
    (hk : hitAt a k x) :
    partialSum x k.1 ≤ a + maxAbsStep x := by
  rcases k with ⟨_ | q, hklt⟩
  · have hk' : a < partialSum x 0 := hk.1
    rw [partialSum_zero] at hk'
    exact False.elim ((not_lt_of_ge ha.le) hk')
  · have hqm : q < m := by omega
    rw [partialSum_succ x hqm]
    calc
      partialSum x q + x ⟨q, hqm⟩
          ≤ a + |x ⟨q, hqm⟩| := by
            gcongr
            · exact hk.2 q (Nat.lt_succ_self q)
            · exact le_abs_self _
      _ ≤ a + maxAbsStep x := by
            gcongr
            exact abs_le_maxAbsStep x ⟨q, hqm⟩

lemma hitAt_pairwise_disjoint {m : ℕ} (a : ℝ) :
    Pairwise fun k l : Fin (m + 1) ↦
      Disjoint {x : Fin m → ℝ | hitAt a k x}
        {x : Fin m → ℝ | hitAt a l x} := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hk hl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact (not_lt_of_ge (hl.2 k.1 hlt)) hk.1
  · exact (not_lt_of_ge (hk.2 l.1 hgt)) hl.1

lemma iUnion_hitAt {m : ℕ} (a : ℝ) :
    (⋃ k : Fin (m + 1), {x : Fin m → ℝ | hitAt a k x}) =
      {x | a < runningMax x} := by
  ext x
  constructor
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    rintro ⟨k, hk⟩
    exact hk.1.trans_le
      (Finset.le_sup'
        (fun j : Fin (m + 1) ↦ partialSum x j.1)
        (Finset.mem_univ k))
  · intro hx
    have hex : ∃ k : Fin (m + 1), a < partialSum x k.1 := by
      change a < runningMax x at hx
      rw [runningMax, Finset.lt_sup'_iff] at hx
      simpa using hx
    let p : ℕ → Prop := fun q ↦ a < partialSum x q
    have hp : ∃ q, p q :=
      ⟨(Classical.choose hex).1, Classical.choose_spec hex⟩
    let j : ℕ := Nat.find hp
    have hj : a < partialSum x j := Nat.find_spec hp
    have hjle : j ≤ (Classical.choose hex).1 :=
      Nat.find_min' hp (Classical.choose_spec hex)
    have hjlt : j < m + 1 := hjle.trans_lt (Classical.choose hex).isLt
    refine Set.mem_iUnion.2 ⟨⟨j, hjlt⟩, ?_⟩
    refine ⟨hj, fun q hq ↦ ?_⟩
    exact le_of_not_gt (fun hpq : a < partialSum x q ↦ by
      have hle := Nat.find_min' hp hpq
      exact (Nat.not_le_of_lt hq) hle)

/-- Product law of independent centered Gaussian increments with possibly
different variances. -/
def gaussianIncrementMeasure {m : ℕ} (v : Fin m → ℝ≥0) :
    Measure (Fin m → ℝ) :=
  Measure.pi (fun i ↦ gaussianReal 0 (v i))

instance gaussianIncrementMeasure_isProbability {m : ℕ}
    (v : Fin m → ℝ≥0) :
    IsProbabilityMeasure (gaussianIncrementMeasure v) := by
  unfold gaussianIncrementMeasure
  infer_instance

lemma map_tailFlip_gaussianIncrementMeasure {m : ℕ}
    (v : Fin m → ℝ≥0) (k : ℕ) :
    (gaussianIncrementMeasure v).map (tailFlip k) =
      gaussianIncrementMeasure v := by
  unfold gaussianIncrementMeasure
  let f : (i : Fin m) → ℝ → ℝ :=
    fun i y ↦ if k ≤ i.1 then -y else y
  have hf : ∀ i, AEMeasurable (f i) (gaussianReal 0 (v i)) := by
    intro i
    by_cases h : k ≤ i.1
    · exact (show Measurable (f i) by
        simp only [f, h, ↓reduceIte]
        fun_prop).aemeasurable
    · exact (show Measurable (f i) by
        simp only [f, h, ↓reduceIte]
        fun_prop).aemeasurable
  rw [show (tailFlip k : (Fin m → ℝ) → (Fin m → ℝ)) =
      (fun x i ↦ f i (x i)) by
    funext x i
    simp [tailFlip, f]]
  rw [Measure.pi_map_pi hf]
  apply congrArg Measure.pi
  funext i
  by_cases h : k ≤ i.1
  · simpa [f, h] using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v i))
  · simp [f, h]

lemma measure_preimage_tailFlip {m : ℕ} (v : Fin m → ℝ≥0)
    (k : ℕ) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) :
    gaussianIncrementMeasure v (tailFlip k ⁻¹' A) =
      gaussianIncrementMeasure v A := by
  rw [← Measure.map_apply (measurable_tailFlip k) hA,
    map_tailFlip_gaussianIncrementMeasure]

lemma measure_hitAt_inter_preimage_tailFlip {m : ℕ}
    (v : Fin m → ℝ≥0) (a : ℝ) (k : Fin (m + 1))
    {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) :
    gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ tailFlip k.1 ⁻¹' A) =
      gaussianIncrementMeasure v ({x | hitAt a k x} ∩ A) := by
  rw [← measure_preimage_tailFlip v k.1
    ((measurableSet_hitAt a k).inter hA)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [hitAt_tailFlip_iff]

lemma measure_hitAt_endpoint_le_le_endpoint_gt {m : ℕ}
    (v : Fin m → ℝ≥0) (a : ℝ) (k : Fin (m + 1)) :
    gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ {x | endpoint x ≤ a}) ≤
      gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ {x | a < endpoint x}) := by
  calc
    gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ {x | endpoint x ≤ a}) ≤
      gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩
          tailFlip k.1 ⁻¹' {x | a < endpoint x}) := by
        apply measure_mono
        rintro x ⟨hxhit, hxend⟩
        change hitAt a k x at hxhit
        change endpoint x ≤ a at hxend
        refine ⟨hxhit, ?_⟩
        change a < endpoint (tailFlip k.1 x)
        rw [endpoint_tailFlip]
        nlinarith [hxhit.1]
    _ = gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ {x | a < endpoint x}) :=
      measure_hitAt_inter_preimage_tailFlip v a k
        (measurableSet_lt measurable_const measurable_endpoint)

lemma measure_runningMax_inter_endpoint_le_le_endpoint_gt {m : ℕ}
    (v : Fin m → ℝ≥0) (a : ℝ) :
    gaussianIncrementMeasure v
        ({x | a < runningMax x} ∩ {x | endpoint x ≤ a}) ≤
      gaussianIncrementMeasure v {x | a < endpoint x} := by
  let C : Fin (m + 1) → Set (Fin m → ℝ) :=
    fun k ↦ {x | hitAt a k x} ∩ {x | endpoint x ≤ a}
  let D : Fin (m + 1) → Set (Fin m → ℝ) :=
    fun k ↦ {x | hitAt a k x} ∩ {x | a < endpoint x}
  have hCpair : Pairwise fun k l ↦ Disjoint (C k) (C l) := by
    intro k l hkl
    exact ((hitAt_pairwise_disjoint a) hkl).mono
      Set.inter_subset_left Set.inter_subset_left
  have hDpair : Pairwise fun k l ↦ Disjoint (D k) (D l) := by
    intro k l hkl
    exact ((hitAt_pairwise_disjoint a) hkl).mono
      Set.inter_subset_left Set.inter_subset_left
  have hCmeas : ∀ k, MeasurableSet (C k) := fun k ↦
    (measurableSet_hitAt a k).inter
      (measurableSet_le measurable_endpoint measurable_const)
  have hDmeas : ∀ k, MeasurableSet (D k) := fun k ↦
    (measurableSet_hitAt a k).inter
      (measurableSet_lt measurable_const measurable_endpoint)
  have hCeq :
      (⋃ k, C k) =
        {x | a < runningMax x} ∩ {x | endpoint x ≤ a} := by
    rw [show (⋃ k, C k) =
        (⋃ k, {x : Fin m → ℝ | hitAt a k x}) ∩
          {x | endpoint x ≤ a} by
      ext x
      simp [C]]
    rw [iUnion_hitAt]
  calc
    gaussianIncrementMeasure v
        ({x | a < runningMax x} ∩ {x | endpoint x ≤ a}) =
      ∑' k, gaussianIncrementMeasure v (C k) := by
        rw [← hCeq, measure_iUnion hCpair hCmeas]
    _ ≤ ∑' k, gaussianIncrementMeasure v (D k) := by
        exact ENNReal.tsum_le_tsum fun k ↦
          measure_hitAt_endpoint_le_le_endpoint_gt v a k
    _ = gaussianIncrementMeasure v (⋃ k, D k) :=
        (measure_iUnion hDpair hDmeas).symm
    _ ≤ gaussianIncrementMeasure v {x | a < endpoint x} := by
        apply measure_mono
        intro x
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
        rintro ⟨k, _, hxend⟩
        exact hxend

lemma measure_runningMax_gt_le_two_endpoint_gt {m : ℕ}
    (v : Fin m → ℝ≥0) (a : ℝ) :
    gaussianIncrementMeasure v {x | a < runningMax x} ≤
      2 * gaussianIncrementMeasure v {x | a < endpoint x} := by
  let A : Set (Fin m → ℝ) := {x | a < endpoint x}
  let C : Set (Fin m → ℝ) :=
    {x | a < runningMax x} ∩ {x | endpoint x ≤ a}
  have hsubset : {x : Fin m → ℝ | a < runningMax x} ⊆ A ∪ C := by
    intro x hx
    by_cases hxa : a < endpoint x
    · exact Or.inl hxa
    · exact Or.inr ⟨hx, le_of_not_gt hxa⟩
  calc
    gaussianIncrementMeasure v {x | a < runningMax x} ≤
        gaussianIncrementMeasure v (A ∪ C) :=
      measure_mono hsubset
    _ ≤ gaussianIncrementMeasure v A +
        gaussianIncrementMeasure v C :=
      measure_union_le _ _
    _ ≤ gaussianIncrementMeasure v A +
        gaussianIncrementMeasure v A := by
      simpa [A, C] using add_le_add
        (le_refl (gaussianIncrementMeasure v A))
        (measure_runningMax_inter_endpoint_le_le_endpoint_gt v a)
    _ = 2 * gaussianIncrementMeasure v {x | a < endpoint x} := by
      simp [A, two_mul]

lemma measure_hitAt_meshTail_le_endpoint_lt {m : ℕ} [NeZero m]
    (v : Fin m → ℝ≥0) {a : ℝ} (ha : 0 < a)
    (k : Fin (m + 1)) :
    gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩
          {x | a + 2 * maxAbsStep x < endpoint x}) ≤
      gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ {x | endpoint x < a}) := by
  calc
    gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩
          {x | a + 2 * maxAbsStep x < endpoint x}) ≤
      gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩
          tailFlip k.1 ⁻¹' {x | endpoint x < a}) := by
        apply measure_mono
        rintro x ⟨hxhit, hxtail⟩
        change hitAt a k x at hxhit
        change a + 2 * maxAbsStep x < endpoint x at hxtail
        refine ⟨hxhit, ?_⟩
        change endpoint (tailFlip k.1 x) < a
        rw [endpoint_tailFlip]
        have hover :=
          hitAt_partialSum_le_add_maxAbsStep ha k x hxhit
        nlinarith
    _ = gaussianIncrementMeasure v
        ({x | hitAt a k x} ∩ {x | endpoint x < a}) :=
      measure_hitAt_inter_preimage_tailFlip v a k
        (measurableSet_lt measurable_endpoint measurable_const)

lemma measure_meshTail_le_runningMax_inter_endpoint_lt {m : ℕ}
    [NeZero m] (v : Fin m → ℝ≥0) {a : ℝ} (ha : 0 < a) :
    gaussianIncrementMeasure v
        {x | a + 2 * maxAbsStep x < endpoint x} ≤
      gaussianIncrementMeasure v
        ({x | a < runningMax x} ∩ {x | endpoint x < a}) := by
  let B : Set (Fin m → ℝ) :=
    {x | a + 2 * maxAbsStep x < endpoint x}
  let C : Fin (m + 1) → Set (Fin m → ℝ) :=
    fun k ↦ {x | hitAt a k x} ∩ B
  let D : Fin (m + 1) → Set (Fin m → ℝ) :=
    fun k ↦ {x | hitAt a k x} ∩ {x | endpoint x < a}
  have hCpair : Pairwise fun k l ↦ Disjoint (C k) (C l) := by
    intro k l hkl
    exact ((hitAt_pairwise_disjoint a) hkl).mono
      Set.inter_subset_left Set.inter_subset_left
  have hDpair : Pairwise fun k l ↦ Disjoint (D k) (D l) := by
    intro k l hkl
    exact ((hitAt_pairwise_disjoint a) hkl).mono
      Set.inter_subset_left Set.inter_subset_left
  have hBmeas : MeasurableSet B := by
    exact measurableSet_lt
      (measurable_const.add (measurable_maxAbsStep.const_mul 2))
      measurable_endpoint
  have hCmeas : ∀ k, MeasurableSet (C k) := fun k ↦
    (measurableSet_hitAt a k).inter hBmeas
  have hDmeas : ∀ k, MeasurableSet (D k) := fun k ↦
    (measurableSet_hitAt a k).inter
      (measurableSet_lt measurable_endpoint measurable_const)
  have hBeq : B = ⋃ k, C k := by
    apply Set.Subset.antisymm
    · intro x hx
      have hend : a < endpoint x := by
        have hD := maxAbsStep_nonneg x
        dsimp [B] at hx
        nlinarith
      have hmax : a < runningMax x :=
        hend.trans_le (endpoint_le_runningMax x)
      have hmax' : x ∈ {x | a < runningMax x} := hmax
      rw [← iUnion_hitAt] at hmax'
      rcases Set.mem_iUnion.1 hmax' with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨k, hk, hx⟩
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨k, _, hxB⟩
      exact hxB
  have hDeq :
      (⋃ k, D k) =
        {x | a < runningMax x} ∩ {x | endpoint x < a} := by
    rw [show (⋃ k, D k) =
        (⋃ k, {x : Fin m → ℝ | hitAt a k x}) ∩
          {x | endpoint x < a} by
      ext x
      simp [D]]
    rw [iUnion_hitAt]
  calc
    gaussianIncrementMeasure v B =
        ∑' k, gaussianIncrementMeasure v (C k) := by
      rw [hBeq, measure_iUnion hCpair hCmeas]
    _ ≤ ∑' k, gaussianIncrementMeasure v (D k) := by
      exact ENNReal.tsum_le_tsum fun k ↦
        measure_hitAt_meshTail_le_endpoint_lt v ha k
    _ = gaussianIncrementMeasure v (⋃ k, D k) :=
      (measure_iUnion hDpair hDmeas).symm
    _ = gaussianIncrementMeasure v
        ({x | a < runningMax x} ∩ {x | endpoint x < a}) := by
      rw [hDeq]

lemma endpoint_gt_add_meshTail_le_runningMax_gt {m : ℕ}
    [NeZero m] (v : Fin m → ℝ≥0) {a : ℝ} (ha : 0 < a) :
    gaussianIncrementMeasure v {x | a < endpoint x} +
        gaussianIncrementMeasure v
          {x | a + 2 * maxAbsStep x < endpoint x} ≤
      gaussianIncrementMeasure v {x | a < runningMax x} := by
  let A : Set (Fin m → ℝ) := {x | a < endpoint x}
  let C : Set (Fin m → ℝ) :=
    {x | a < runningMax x} ∩ {x | endpoint x < a}
  have hAC : Disjoint A C := by
    rw [Set.disjoint_left]
    rintro x hxA ⟨_, hxC⟩
    change a < endpoint x at hxA
    change endpoint x < a at hxC
    exact (not_lt_of_ge hxA.le) hxC
  have hCmeas : MeasurableSet C :=
    (measurableSet_lt measurable_const measurable_runningMax).inter
      (measurableSet_lt measurable_endpoint measurable_const)
  have hunion : A ∪ C ⊆ {x | a < runningMax x} := by
    rintro x (hxA | hxC)
    · exact hxA.trans_le (endpoint_le_runningMax x)
    · exact hxC.1
  calc
    gaussianIncrementMeasure v A +
        gaussianIncrementMeasure v
          {x | a + 2 * maxAbsStep x < endpoint x} ≤
      gaussianIncrementMeasure v A + gaussianIncrementMeasure v C := by
        simpa [A, C] using add_le_add
          (le_refl (gaussianIncrementMeasure v A))
          (measure_meshTail_le_runningMax_inter_endpoint_lt v ha)
    _ = gaussianIncrementMeasure v (A ∪ C) :=
      (measure_union hAC hCmeas).symm
    _ ≤ gaussianIncrementMeasure v {x | a < runningMax x} :=
      measure_mono hunion

lemma hasLaw_eval_gaussianIncrementMeasure {m : ℕ}
    (v : Fin m → ℝ≥0) (i : Fin m) :
    HasLaw (fun x : Fin m → ℝ ↦ x i) (gaussianReal 0 (v i))
      (gaussianIncrementMeasure v) := by
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  unfold gaussianIncrementMeasure
  rw [Measure.pi_map_eval]
  simp

lemma integrable_eval_gaussianIncrementMeasure {m : ℕ}
    (v : Fin m → ℝ≥0) (i : Fin m) :
    Integrable (fun x : Fin m → ℝ ↦ x i)
      (gaussianIncrementMeasure v) :=
  (hasLaw_eval_gaussianIncrementMeasure v i).hasGaussianLaw.integrable

lemma integrable_partialSum_gaussianIncrementMeasure {m : ℕ}
    (v : Fin m → ℝ≥0) (k : ℕ) :
    Integrable (fun x : Fin m → ℝ ↦ partialSum x k)
      (gaussianIncrementMeasure v) := by
  unfold partialSum
  exact integrable_finsetSum _ fun i _ ↦
    integrable_eval_gaussianIncrementMeasure v i

lemma integrable_endpoint_gaussianIncrementMeasure {m : ℕ}
    (v : Fin m → ℝ≥0) :
    Integrable endpoint (gaussianIncrementMeasure v) := by
  unfold endpoint
  exact integrable_finsetSum _ fun i _ ↦
    integrable_eval_gaussianIncrementMeasure v i

lemma integrable_runningMax_gaussianIncrementMeasure {m : ℕ}
    (v : Fin m → ℝ≥0) :
    Integrable runningMax (gaussianIncrementMeasure v) := by
  rw [show (runningMax : (Fin m → ℝ) → ℝ) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) ↦
          fun x : Fin m → ℝ ↦ partialSum x k.1) by
    funext x
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun k : Fin (m + 1) ↦
        fun x : Fin m → ℝ ↦ partialSum x k.1) x).symm]
  refine Finset.sup'_induction Finset.univ_nonempty
    (fun k : Fin (m + 1) ↦
      fun x : Fin m → ℝ ↦ partialSum x k.1)
    (p := fun f ↦ Integrable f (gaussianIncrementMeasure v)) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro k _
    exact integrable_partialSum_gaussianIncrementMeasure v k.1

lemma integrable_maxAbsStep_gaussianIncrementMeasure {m : ℕ}
    [NeZero m] (v : Fin m → ℝ≥0) :
    Integrable maxAbsStep (gaussianIncrementMeasure v) := by
  rw [show (maxAbsStep : (Fin m → ℝ) → ℝ) =
      Finset.univ.sup' (Finset.univ_nonempty (α := Fin m))
        (fun i : Fin m ↦ fun x : Fin m → ℝ ↦ |x i|) by
    funext x
    exact (Finset.sup'_apply (Finset.univ_nonempty (α := Fin m))
      (fun i : Fin m ↦ fun x : Fin m → ℝ ↦ |x i|) x).symm]
  refine Finset.sup'_induction (Finset.univ_nonempty (α := Fin m))
    (fun i : Fin m ↦ fun x : Fin m → ℝ ↦ |x i|)
    (p := fun f ↦ Integrable f (gaussianIncrementMeasure v)) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro i _
    exact (integrable_eval_gaussianIncrementMeasure v i).abs

lemma endpoint_identDistrib_neg {m : ℕ} (v : Fin m → ℝ≥0) :
    IdentDistrib endpoint (fun x : Fin m → ℝ ↦ -endpoint x)
      (gaussianIncrementMeasure v) (gaussianIncrementMeasure v) := by
  refine
    { aemeasurable_fst := measurable_endpoint.aemeasurable
      aemeasurable_snd := measurable_endpoint.neg.aemeasurable
      map_eq := ?_ }
  symm
  calc
    (gaussianIncrementMeasure v).map
        (fun x : Fin m → ℝ ↦ -endpoint x) =
      (gaussianIncrementMeasure v).map
        (endpoint ∘ tailFlip 0) := by
          congr 1
          funext x
          rw [Function.comp_apply, endpoint_tailFlip, partialSum_zero]
          ring
    _ = ((gaussianIncrementMeasure v).map (tailFlip 0)).map
        endpoint := (Measure.map_map measurable_endpoint
          (measurable_tailFlip 0)).symm
    _ = (gaussianIncrementMeasure v).map endpoint := by
      rw [map_tailFlip_gaussianIncrementMeasure]

lemma integral_abs_endpoint_eq_two_posPart {m : ℕ}
    (v : Fin m → ℝ≥0) :
    (∫ x, |endpoint x| ∂gaussianIncrementMeasure v) =
      2 * ∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v := by
  have hend := integrable_endpoint_gaussianIncrementMeasure v
  have hpos : Integrable (fun x : Fin m → ℝ ↦ max (endpoint x) 0)
      (gaussianIncrementMeasure v) :=
    hend.sup (integrable_const 0)
  have hnegpos : Integrable
      (fun x : Fin m → ℝ ↦ max (-endpoint x) 0)
      (gaussianIncrementMeasure v) :=
    hend.neg.sup (integrable_const 0)
  have hid := (endpoint_identDistrib_neg v).comp
    (u := fun y : ℝ ↦ max y 0)
    (measurable_id.max (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ))))
  have hsame :
      (∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v) =
        ∫ x, max (-endpoint x) 0 ∂gaussianIncrementMeasure v := by
    simpa [Function.comp_def] using hid.integral_eq
  calc
    (∫ x, |endpoint x| ∂gaussianIncrementMeasure v) =
        ∫ x, (max (endpoint x) 0 + max (-endpoint x) 0)
          ∂gaussianIncrementMeasure v := by
            apply integral_congr_ae
            filter_upwards [] with x
            rcases le_total 0 (endpoint x) with h | h
            · simp [abs_of_nonneg h, max_eq_left h,
                max_eq_right (neg_nonpos.mpr h)]
            · simp [abs_of_nonpos h, max_eq_right h,
                max_eq_left (neg_nonneg.mpr h)]
    _ = (∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v) +
        ∫ x, max (-endpoint x) 0 ∂gaussianIncrementMeasure v := by
          rw [integral_add hpos hnegpos]
    _ = 2 * ∫ x, max (endpoint x) 0
        ∂gaussianIncrementMeasure v := by rw [← hsame]; ring

/-- The expected discrete running maximum is at most twice the expected
positive part of the endpoint. -/
lemma integral_runningMax_le_two_posPart {m : ℕ}
    (v : Fin m → ℝ≥0) :
    (∫ x, runningMax x ∂gaussianIncrementMeasure v) ≤
      2 * ∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v := by
  have hM := integrable_runningMax_gaussianIncrementMeasure v
  have hP : Integrable (fun x : Fin m → ℝ => max (endpoint x) 0)
      (gaussianIncrementMeasure v) :=
    (integrable_endpoint_gaussianIncrementMeasure v).sup (integrable_const 0)
  have hM0 : 0 ≤ᵐ[gaussianIncrementMeasure v]
      (runningMax : (Fin m → ℝ) → ℝ) :=
    Filter.Eventually.of_forall runningMax_nonneg
  have hP0 : 0 ≤ᵐ[gaussianIncrementMeasure v]
      (fun x : Fin m → ℝ => max (endpoint x) (0 : ℝ)) :=
    Filter.Eventually.of_forall fun x => le_max_right _ _
  have hlayerM :
      (∫⁻ x, ENNReal.ofReal (runningMax x)
          ∂gaussianIncrementMeasure v) =
        ∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v {x | a < runningMax x} :=
    lintegral_eq_lintegral_meas_lt (gaussianIncrementMeasure v)
      hM0 hM.aemeasurable
  have hlayerP :
      (∫⁻ x, ENNReal.ofReal (max (endpoint x) (0 : ℝ))
          ∂gaussianIncrementMeasure v) =
        ∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v
            {x | a < max (endpoint x) (0 : ℝ)} :=
    lintegral_eq_lintegral_meas_lt (gaussianIncrementMeasure v)
      hP0 hP.aemeasurable
  have hENN :
      (∫⁻ x, ENNReal.ofReal (runningMax x)
          ∂gaussianIncrementMeasure v) ≤
        2 * ∫⁻ x, ENNReal.ofReal (max (endpoint x) 0)
          ∂gaussianIncrementMeasure v := by
    rw [hlayerM, hlayerP]
    calc
      (∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v {x | a < runningMax x}) ≤
          ∫⁻ a in Set.Ioi (0 : ℝ),
            2 * gaussianIncrementMeasure v
              {x | a < max (endpoint x) 0} := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        have h := measure_runningMax_gt_le_two_endpoint_gt v a
        have heq :
            {x : Fin m → ℝ | a < max (endpoint x) 0} =
              {x | a < endpoint x} := by
          ext x
          simp only [Set.mem_setOf_eq, lt_max_iff]
          exact or_iff_left (not_lt_of_ge ha.le)
        rwa [heq]
      _ = 2 * ∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v
            {x | a < max (endpoint x) 0} := by
        exact lintegral_const_mul' _ _ (by norm_num)
  rw [integral_eq_lintegral_of_nonneg_ae hM0 hM.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hP0 hP.aestronglyMeasurable]
  rw [← ENNReal.toReal_ofNat (n := 2), ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top (by simp) hP.lintegral_lt_top.ne
  · exact hENN

/-- The strict-crossing reflection lower tail bound, integrated by layer
cake.  The shifted positive part records the at-most-two-mesh overshoot. -/
lemma integral_posPart_add_shifted_le_runningMax
    {m : ℕ} [NeZero m] (v : Fin m → ℝ≥0) :
    (∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v) +
        (∫ x, max (endpoint x - 2 * maxAbsStep x) 0
          ∂gaussianIncrementMeasure v) ≤
      ∫ x, runningMax x ∂gaussianIncrementMeasure v := by
  have hE := integrable_endpoint_gaussianIncrementMeasure v
  have hR := integrable_maxAbsStep_gaussianIncrementMeasure v
  have hM := integrable_runningMax_gaussianIncrementMeasure v
  have hP : Integrable (fun x : Fin m → ℝ => max (endpoint x) 0)
      (gaussianIncrementMeasure v) :=
    hE.sup (integrable_const 0)
  have hT : Integrable
      (fun x : Fin m → ℝ => max (endpoint x - 2 * maxAbsStep x) 0)
      (gaussianIncrementMeasure v) := by
    exact (hE.sub (hR.const_mul 2)).sup (integrable_const 0)
  have htailP : Measurable (fun a : ℝ =>
      gaussianIncrementMeasure v
        {x : Fin m → ℝ | a < max (endpoint x) 0}) :=
    Antitone.measurable fun a b hab =>
      measure_mono fun x hx => lt_of_le_of_lt hab hx
  have hP0 : 0 ≤ᵐ[gaussianIncrementMeasure v]
      (fun x : Fin m → ℝ => max (endpoint x) (0 : ℝ)) :=
    Filter.Eventually.of_forall fun x => le_max_right _ _
  have hT0 : 0 ≤ᵐ[gaussianIncrementMeasure v]
      (fun x : Fin m → ℝ =>
        max (endpoint x - 2 * maxAbsStep x) (0 : ℝ)) :=
    Filter.Eventually.of_forall fun x => le_max_right _ _
  have hM0 : 0 ≤ᵐ[gaussianIncrementMeasure v]
      (runningMax : (Fin m → ℝ) → ℝ) :=
    Filter.Eventually.of_forall runningMax_nonneg
  have hlayerP :
      (∫⁻ x, ENNReal.ofReal (max (endpoint x) (0 : ℝ))
          ∂gaussianIncrementMeasure v) =
        ∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v
            {x | a < max (endpoint x) (0 : ℝ)} :=
    lintegral_eq_lintegral_meas_lt (f := fun x : Fin m → ℝ =>
      max (endpoint x) (0 : ℝ)) (gaussianIncrementMeasure v)
      hP0 hP.aemeasurable
  have hlayerT :
      (∫⁻ x, ENNReal.ofReal
          (max (endpoint x - 2 * maxAbsStep x) (0 : ℝ))
          ∂gaussianIncrementMeasure v) =
        ∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v
            {x | a < max (endpoint x - 2 * maxAbsStep x) (0 : ℝ)} :=
    lintegral_eq_lintegral_meas_lt (f := fun x : Fin m → ℝ =>
      max (endpoint x - 2 * maxAbsStep x) (0 : ℝ))
      (gaussianIncrementMeasure v) hT0 hT.aemeasurable
  have hlayerM :
      (∫⁻ x, ENNReal.ofReal (runningMax x)
          ∂gaussianIncrementMeasure v) =
        ∫⁻ a in Set.Ioi (0 : ℝ),
          gaussianIncrementMeasure v {x | a < runningMax x} :=
    lintegral_eq_lintegral_meas_lt (f := runningMax)
      (gaussianIncrementMeasure v) hM0 hM.aemeasurable
  have hENN :
      (∫⁻ x, ENNReal.ofReal (max (endpoint x) 0)
          ∂gaussianIncrementMeasure v) +
        (∫⁻ x, ENNReal.ofReal
            (max (endpoint x - 2 * maxAbsStep x) 0)
          ∂gaussianIncrementMeasure v) ≤
        ∫⁻ x, ENNReal.ofReal (runningMax x)
          ∂gaussianIncrementMeasure v := by
    rw [hlayerP, hlayerT, hlayerM]
    rw [← lintegral_add_left
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) htailP]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have h := endpoint_gt_add_meshTail_le_runningMax_gt v ha
    have hPeq :
        {x : Fin m → ℝ | a < max (endpoint x) 0} =
          {x | a < endpoint x} := by
      ext x
      simp only [Set.mem_setOf_eq, lt_max_iff]
      exact or_iff_left (not_lt_of_ge ha.le)
    have hTeq :
        {x : Fin m → ℝ |
            a < max (endpoint x - 2 * maxAbsStep x) 0} =
          {x | a + 2 * maxAbsStep x < endpoint x} := by
      ext x
      simp only [Set.mem_setOf_eq, lt_max_iff]
      rw [or_iff_left (not_lt_of_ge ha.le)]
      constructor <;> intro hx <;> linarith
    rwa [hPeq, hTeq]
  have hintP :
      (∫ x, max (endpoint x) (0 : ℝ)
          ∂gaussianIncrementMeasure v) =
        (∫⁻ x, ENNReal.ofReal (max (endpoint x) (0 : ℝ))
          ∂gaussianIncrementMeasure v).toReal :=
    integral_eq_lintegral_of_nonneg_ae hP0 hP.aestronglyMeasurable
  have hintT :
      (∫ x, max (endpoint x - 2 * maxAbsStep x) (0 : ℝ)
          ∂gaussianIncrementMeasure v) =
        (∫⁻ x, ENNReal.ofReal
            (max (endpoint x - 2 * maxAbsStep x) (0 : ℝ))
          ∂gaussianIncrementMeasure v).toReal :=
    integral_eq_lintegral_of_nonneg_ae hT0 hT.aestronglyMeasurable
  have hintM :
      (∫ x, runningMax x ∂gaussianIncrementMeasure v) =
        (∫⁻ x, ENNReal.ofReal (runningMax x)
          ∂gaussianIncrementMeasure v).toReal :=
    integral_eq_lintegral_of_nonneg_ae hM0 hM.aestronglyMeasurable
  rw [hintP, hintT, hintM]
  rw [← ENNReal.toReal_add hP.lintegral_lt_top.ne hT.lintegral_lt_top.ne]
  exact ENNReal.toReal_mono hM.lintegral_lt_top.ne hENN

/-- The expected running maximum is within twice the expected largest
increment of the endpoint absolute moment. -/
lemma integral_abs_endpoint_sub_two_maxAbsStep_le_runningMax
    {m : ℕ} [NeZero m] (v : Fin m → ℝ≥0) :
    (∫ x, |endpoint x| ∂gaussianIncrementMeasure v) -
        2 * (∫ x, maxAbsStep x ∂gaussianIncrementMeasure v) ≤
      ∫ x, runningMax x ∂gaussianIncrementMeasure v := by
  have hE := integrable_endpoint_gaussianIncrementMeasure v
  have hR := integrable_maxAbsStep_gaussianIncrementMeasure v
  have hP : Integrable (fun x : Fin m → ℝ => max (endpoint x) 0)
      (gaussianIncrementMeasure v) :=
    hE.sup (integrable_const 0)
  have hT : Integrable
      (fun x : Fin m → ℝ => max (endpoint x - 2 * maxAbsStep x) 0)
      (gaussianIncrementMeasure v) :=
    (hE.sub (hR.const_mul 2)).sup (integrable_const 0)
  have hPT := integral_posPart_add_shifted_le_runningMax v
  have hshift :
      (∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v) -
          2 * (∫ x, maxAbsStep x ∂gaussianIncrementMeasure v) ≤
        ∫ x, max (endpoint x - 2 * maxAbsStep x) 0
          ∂gaussianIncrementMeasure v := by
    calc
      (∫ x, max (endpoint x) 0 ∂gaussianIncrementMeasure v) -
          2 * (∫ x, maxAbsStep x ∂gaussianIncrementMeasure v) =
          ∫ x, max (endpoint x) 0 - 2 * maxAbsStep x
            ∂gaussianIncrementMeasure v := by
        rw [integral_sub hP (hR.const_mul 2), integral_const_mul]
      _ ≤ ∫ x, max (endpoint x - 2 * maxAbsStep x) 0
          ∂gaussianIncrementMeasure v := by
        apply integral_mono (hP.sub (hR.const_mul 2)) hT
        intro x
        change max (endpoint x) 0 - 2 * maxAbsStep x ≤
          max (endpoint x - 2 * maxAbsStep x) 0
        by_cases hx : 0 ≤ endpoint x
        · rw [max_eq_left hx]
          exact le_max_left _ _
        · rw [max_eq_right (le_of_not_ge hx)]
          exact (sub_nonpos.mpr (by
            nlinarith [maxAbsStep_nonneg x])).trans (le_max_right _ _)
  rw [integral_abs_endpoint_eq_two_posPart v]
  linarith

/-- The expected discrete running maximum is bounded above by the absolute
endpoint expectation. -/
lemma integral_runningMax_le_abs_endpoint {m : ℕ}
    (v : Fin m → ℝ≥0) :
    (∫ x, runningMax x ∂gaussianIncrementMeasure v) ≤
      ∫ x, |endpoint x| ∂gaussianIncrementMeasure v := by
  rw [integral_abs_endpoint_eq_two_posPart v]
  exact integral_runningMax_le_two_posPart v

end

end HDP.Chapter7.BrownianDiscrete
