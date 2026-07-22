import HighDimensionalProbability.Appendix.Infra.BrownianDiscrete

/-!
# Finite Brownian grids

This file transfers finite Brownian families to the canonical product model
of their consecutive centered Gaussian increments.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace HDP.Chapter7.BrownianFiniteGrid

noncomputable section

open BrownianDiscrete

/-- Enumerate a finite set of nonnegative times after an initial zero. -/
def orderedWithZero (I : Finset ℝ≥0) (i : Fin (I.card + 1)) : ℝ≥0 :=
  if h : i = 0 then 0 else I.orderEmbOfFin rfl (i.pred h)

@[simp]
lemma orderedWithZero_zero (I : Finset ℝ≥0) :
    orderedWithZero I 0 = 0 := rfl

@[simp]
lemma orderedWithZero_succ (I : Finset ℝ≥0) (i : Fin I.card) :
    orderedWithZero I i.succ = I.orderEmbOfFin rfl i := by
  rw [orderedWithZero]
  simp

lemma orderedWithZero_of_ne_zero (I : Finset ℝ≥0)
    (i : Fin (I.card + 1)) (hi : i ≠ 0) :
    orderedWithZero I i = I.orderEmbOfFin rfl (i.pred hi) := by
  rw [orderedWithZero, dif_neg hi]

lemma monotone_orderedWithZero (I : Finset ℝ≥0) :
    Monotone (orderedWithZero I) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  have hj : j ≠ 0 := by
    intro hj0
    apply hi
    exact le_antisymm (by simpa [hj0] using hij) (Fin.zero_le i)
  rw [orderedWithZero_of_ne_zero I i hi,
    orderedWithZero_of_ne_zero I j hj]
  exact OrderEmbedding.monotone _ (by simpa)

/-- Every member of the finite set occurs in its enumeration after zero. -/
lemma exists_orderedWithZero_eq_of_mem (I : Finset ℝ≥0)
    {s : ℝ≥0} (hs : s ∈ I) :
    ∃ k : Fin (I.card + 1), orderedWithZero I k = s := by
  let j : Fin I.card :=
    (I.orderIsoOfFin rfl).symm ⟨s, hs⟩
  refine ⟨j.succ, ?_⟩
  rw [orderedWithZero_succ]
  change ((I.orderIsoOfFin rfl j : I) : ℝ≥0) = s
  simp [j]

/-- The final point of `orderedWithZero` is the maximum of a nonempty
finite set. -/
lemma orderedWithZero_last_eq_max' (I : Finset ℝ≥0)
    (hI : I.Nonempty) :
    orderedWithZero I (Fin.last I.card) = I.max' hI := by
  have hc : 0 < I.card := Finset.card_pos.mpr hI
  let j : Fin I.card :=
    ⟨I.card - 1, Nat.sub_lt hc (Nat.succ_pos 0)⟩
  have hj : j.succ = Fin.last I.card := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [← hj, orderedWithZero_succ]
  exact Finset.orderEmbOfFin_last rfl hc

/-- If `t` belongs to a finite set and bounds all its elements, then it is
the final point of the enumeration after zero. -/
lemma orderedWithZero_last_eq_of_mem_of_forall_le
    (I : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∈ I)
    (hle : ∀ s ∈ I, s ≤ t) :
    orderedWithZero I (Fin.last I.card) = t := by
  rw [orderedWithZero_last_eq_max' I ⟨t, ht⟩]
  apply le_antisymm
  · exact Finset.max'_le I ⟨t, ht⟩ t hle
  · exact Finset.le_max' I t ht

/-- Consecutive increments of a process along a finite monotone time grid. -/
def processIncrements {Ω : Type*} {m : ℕ}
    (B : ℝ≥0 → Ω → ℝ) (τ : Fin (m + 1) → ℝ≥0) :
    Ω → Fin m → ℝ :=
  fun ω i => B (τ i.succ) ω - B (τ i.castSucc) ω

/-- Variances of consecutive increments along a monotone time grid. -/
def incrementVariances {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    Fin m → ℝ≥0 :=
  fun i => τ i.succ - τ i.castSucc

/-- Consecutive Brownian increments have the canonical independent product
Gaussian law. -/
theorem hasLaw_processIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    HasLaw (processIncrements B τ)
      (gaussianIncrementMeasure (incrementVariances τ)) P := by
  apply (hB.hasIndepIncrements m τ hτ).hasLaw_pi
  intro i
  have h := hB.hasLaw_sub (τ i.succ) (τ i.castSucc)
  have hle : τ i.castSucc ≤ τ i.succ :=
    hτ (Fin.castSucc_le_succ i)
  have hdist :
      nndist (τ i.succ : ℝ) (τ i.castSucc : ℝ) =
        τ i.succ - τ i.castSucc := by
    rw [Real.nndist_eq]
    apply NNReal.eq
    simp [Real.nnabs_of_nonneg, hle]
  change HasLaw
    (fun ω => B (τ i.succ) ω - B (τ i.castSucc) ω)
    (gaussianReal 0 (τ i.succ - τ i.castSucc)) P
  rw [← hdist]
  exact h

/-- A deterministic telescoping identity for the discrete partial sum of
consecutive differences. -/
lemma partialSum_consecutiveDifferences {m : ℕ}
    (y : Fin (m + 1) → ℝ) (k : ℕ) (hk : k ≤ m) :
    partialSum (fun i : Fin m => y i.succ - y i.castSucc) k =
      y ⟨k, Nat.lt_add_one_iff.mpr hk⟩ - y 0 := by
  induction k with
  | zero =>
      simp [partialSum_zero]
  | succ k ih =>
      have hkm : k < m := by omega
      rw [partialSum_succ _ hkm, ih (Nat.le_of_lt hkm)]
      change (y ⟨k, by omega⟩ - y 0) +
        (y ⟨k + 1, by omega⟩ - y ⟨k, by omega⟩) =
          y ⟨k + 1, by omega⟩ - y 0
      ring

/-- If the initial value is zero, discrete running maxima of consecutive
differences equal the maximum of the original finite path. -/
lemma runningMax_consecutiveDifferences {m : ℕ}
    (y : Fin (m + 1) → ℝ) (hy0 : y 0 = 0) :
    runningMax (fun i : Fin m => y i.succ - y i.castSucc) =
      Finset.univ.sup' Finset.univ_nonempty y := by
  unfold runningMax
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro k _
  rw [partialSum_consecutiveDifferences y k.1 (Nat.le_of_lt_succ k.2)]
  simp [hy0]

/-- If the initial value is zero, the endpoint of the consecutive-difference
vector is the last value of the original finite path. -/
lemma endpoint_consecutiveDifferences {m : ℕ}
    (y : Fin (m + 1) → ℝ) (hy0 : y 0 = 0) :
    endpoint (fun i : Fin m => y i.succ - y i.castSucc) =
      y (Fin.last m) := by
  rw [← partialSum_endpoint,
    partialSum_consecutiveDifferences y m le_rfl]
  rw [hy0, sub_zero]
  congr

/-- The Brownian finite-grid maximum is identically distributed with the
running maximum of the canonical increment vector. -/
theorem finiteGridMaximum_identDistrib_runningMax
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) :
    IdentDistrib
      (HDP.Chapter5.finiteMaximum (fun k => B (τ k)))
      (runningMax : (Fin m → ℝ) → ℝ) P
      (gaussianIncrementMeasure (incrementVariances τ)) := by
  have hvec := hasLaw_processIncrements hB τ hτ
  have hcomp :=
    (hvec.identDistrib
      (HasLaw.id :
        HasLaw id (gaussianIncrementMeasure (incrementVariances τ))
          (gaussianIncrementMeasure (incrementVariances τ)))).comp
      (measurable_runningMax (m := m))
  have hzero : ∀ᵐ ω ∂P, B (τ 0) ω = 0 := by
    simpa [hτ0] using hB.eval_zero_ae_eq_zero
  have hae :
      (fun ω => runningMax (processIncrements B τ ω)) =ᵐ[P]
        HDP.Chapter5.finiteMaximum (fun k => B (τ k)) := by
    filter_upwards [hzero] with ω hω
    exact runningMax_consecutiveDifferences
      (fun k => B (τ k) ω) hω
  have haeIdent :
      IdentDistrib
        (fun ω => runningMax (processIncrements B τ ω))
        (HDP.Chapter5.finiteMaximum (fun k => B (τ k))) P P :=
    IdentDistrib.of_ae_eq hcomp.aemeasurable_fst hae
  exact haeIdent.symm.trans (by
    simpa [Function.comp_def, processIncrements] using hcomp)

/-- The Brownian value at the last grid point is identically distributed
with the endpoint of the canonical increment vector. -/
theorem evalLast_identDistrib_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) :
    IdentDistrib
      (B (τ (Fin.last m)))
      (endpoint : (Fin m → ℝ) → ℝ) P
      (gaussianIncrementMeasure (incrementVariances τ)) := by
  have hvec := hasLaw_processIncrements hB τ hτ
  have hcomp :=
    (hvec.identDistrib
      (HasLaw.id :
        HasLaw id (gaussianIncrementMeasure (incrementVariances τ))
          (gaussianIncrementMeasure (incrementVariances τ)))).comp
      (measurable_endpoint (m := m))
  have hzero : ∀ᵐ ω ∂P, B (τ 0) ω = 0 := by
    simpa [hτ0] using hB.eval_zero_ae_eq_zero
  have hae :
      (fun ω => endpoint (processIncrements B τ ω)) =ᵐ[P]
        B (τ (Fin.last m)) := by
    filter_upwards [hzero] with ω hω
    exact endpoint_consecutiveDifferences
      (fun k => B (τ k) ω) hω
  have haeIdent :
      IdentDistrib
        (fun ω => endpoint (processIncrements B τ ω))
        (B (τ (Fin.last m))) P P :=
    IdentDistrib.of_ae_eq hcomp.aemeasurable_fst hae
  exact haeIdent.symm.trans (by
    simpa [Function.comp_def, processIncrements] using hcomp)

/-- A finite maximum of Brownian evaluations is integrable. -/
lemma integrable_finiteMaximum_eval
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (τ : ι → ℝ≥0) :
    Integrable (HDP.Chapter5.finiteMaximum (fun i => B (τ i))) P := by
  rw [show HDP.Chapter5.finiteMaximum (fun i => B (τ i)) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => B (τ i)) by
    funext ω
    unfold HDP.Chapter5.finiteMaximum
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun i => B (τ i)) ω).symm]
  refine Finset.sup'_induction Finset.univ_nonempty
    (f := fun i => B (τ i)) (p := fun f => Integrable f P) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro i _
    exact hB.integrable_eval (τ i)

/-! ## An arbitrary queried finite family -/

/-- The queried times together with the right endpoint. -/
def familyTimeSet {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) : Finset ℝ≥0 :=
  insert t (Finset.univ.image fun i => (u i).1)

lemma familyTimeSet_mem_endpoint {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    t ∈ familyTimeSet t u := by
  simp [familyTimeSet]

lemma familyTimeSet_mem_query {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) (i : Fin (n + 1)) :
    (u i).1 ∈ familyTimeSet t u := by
  simp [familyTimeSet]

lemma familyTimeSet_forall_le {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    ∀ s ∈ familyTimeSet t u, s ≤ t := by
  intro s hs
  simp only [familyTimeSet, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hs
  rcases hs with rfl | ⟨i, rfl⟩
  · exact le_rfl
  · exact (u i).2

/-- The monotone grid containing every queried time and the endpoint. -/
def familyGridTime {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    Fin ((familyTimeSet t u).card + 1) → ℝ≥0 :=
  orderedWithZero (familyTimeSet t u)

@[simp]
lemma familyGridTime_zero {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    familyGridTime t u 0 = 0 :=
  orderedWithZero_zero _

lemma monotone_familyGridTime {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    Monotone (familyGridTime t u) :=
  monotone_orderedWithZero _

@[simp]
lemma familyGridTime_last {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    familyGridTime t u (Fin.last (familyTimeSet t u).card) = t :=
  orderedWithZero_last_eq_of_mem_of_forall_le _ t
    (familyTimeSet_mem_endpoint t u) (familyTimeSet_forall_le t u)

/-- The position of a queried time in the sorted family grid. -/
def familyGridIndex {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) (i : Fin (n + 1)) :
    Fin ((familyTimeSet t u).card + 1) :=
  ((familyTimeSet t u).orderIsoOfFin rfl).symm
    ⟨(u i).1, familyTimeSet_mem_query t u i⟩ |>.succ

@[simp]
lemma familyGridTime_familyGridIndex {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) (i : Fin (n + 1)) :
    familyGridTime t u (familyGridIndex t u i) = (u i).1 := by
  rw [familyGridTime, familyGridIndex, orderedWithZero_succ]
  change (↑(((familyTimeSet t u).orderIsoOfFin rfl)
    (((familyTimeSet t u).orderIsoOfFin rfl).symm
      ⟨(u i).1, familyTimeSet_mem_query t u i⟩)) : ℝ≥0) = (u i).1
  simp

/-- Pointwise, the sorted family-grid maximum dominates the originally
queried maximum. -/
lemma finiteMaximum_query_le_familyGrid {Ω : Type*}
    {n : ℕ} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) (ω : Ω) :
    HDP.Chapter5.finiteMaximum (fun i => B (u i).1) ω ≤
      HDP.Chapter5.finiteMaximum
        (fun k => B (familyGridTime t u k)) ω := by
  unfold HDP.Chapter5.finiteMaximum
  apply Finset.sup'_le
  intro i _
  have h := Finset.le_sup'
    (fun k => B (familyGridTime t u k) ω)
    (Finset.mem_univ (familyGridIndex t u i))
  simpa using h

/-- The queried Brownian finite maximum is bounded by the running maximum
of the corresponding canonical Gaussian increment vector. -/
theorem finiteFamily_integral_le_runningMax_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    (∫ ω, HDP.Chapter5.finiteMaximum
        (fun i => B (u i).1) ω ∂P) ≤
      ∫ x, runningMax x
        ∂gaussianIncrementMeasure
          (incrementVariances (familyGridTime t u)) := by
  calc
    (∫ ω, HDP.Chapter5.finiteMaximum
        (fun i => B (u i).1) ω ∂P) ≤
      ∫ ω, HDP.Chapter5.finiteMaximum
        (fun k => B (familyGridTime t u k)) ω ∂P := by
        apply integral_mono
          (integrable_finiteMaximum_eval hB (fun i => (u i).1))
          (integrable_finiteMaximum_eval hB (familyGridTime t u))
        exact finiteMaximum_query_le_familyGrid B t u
    _ = ∫ x, runningMax x
        ∂gaussianIncrementMeasure
          (incrementVariances (familyGridTime t u)) :=
      (finiteGridMaximum_identDistrib_runningMax hB
        (familyGridTime t u) (monotone_familyGridTime t u)
        (familyGridTime_zero t u)).integral_eq

/-- The endpoint of the family-grid increment vector has the Brownian
endpoint law. -/
theorem familyEndpoint_identDistrib_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    IdentDistrib (B t) endpoint P
      (gaussianIncrementMeasure
        (incrementVariances (familyGridTime t u))) := by
  simpa using evalLast_identDistrib_endpoint hB
    (familyGridTime t u) (monotone_familyGridTime t u)
    (familyGridTime_zero t u)

/-- Absolute endpoint expectations agree on the Brownian and product
increment models. -/
theorem integral_abs_familyEndpoint_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {n : ℕ} (t : ℝ≥0)
    (u : Fin (n + 1) → {s : ℝ≥0 // s ≤ t}) :
    (∫ x, |endpoint x|
        ∂gaussianIncrementMeasure
          (incrementVariances (familyGridTime t u))) =
      ∫ ω, |B t ω| ∂P := by
  exact ((familyEndpoint_identDistrib_endpoint hB t u).comp
    measurable_abs).integral_eq.symm

/-! ## Uniform grids -/

/-- The `k`-th point of the uniform grid with `n+2` intervals in `[0,t]`. -/
def uniformGridTime (t : ℝ≥0) (n : ℕ) (k : Fin (n + 3)) : ℝ≥0 :=
  (k.1 : ℝ≥0) * (t / (n + 2))

@[simp]
lemma uniformGridTime_zero (t : ℝ≥0) (n : ℕ) :
    uniformGridTime t n 0 = 0 := by
  simp [uniformGridTime]

lemma monotone_uniformGridTime (t : ℝ≥0) (n : ℕ) :
    Monotone (uniformGridTime t n) := by
  intro i j hij
  apply mul_le_mul_right'
  exact_mod_cast hij

@[simp]
lemma uniformGridTime_last (t : ℝ≥0) (n : ℕ) :
    uniformGridTime t n (Fin.last (n + 2)) = t := by
  dsimp [uniformGridTime]
  field_simp
  push_cast
  ring

lemma uniformGridTime_le (t : ℝ≥0) (n : ℕ) (k : Fin (n + 3)) :
    uniformGridTime t n k ≤ t := by
  calc
    uniformGridTime t n k ≤
        (n + 2 : ℝ≥0) * (t / (n + 2)) := by
      apply mul_le_mul_right'
      exact_mod_cast (Nat.le_of_lt_succ k.2)
    _ = t := by
      field_simp

/-- Uniform-grid times as a family in the subtype `[0,t]`, ready for the
finite-family definition of `extendedExpectedSupremum`. -/
def uniformGridPoint (t : ℝ≥0) (n : ℕ) (k : Fin (n + 3)) :
    {s : ℝ≥0 // s ≤ t} :=
  ⟨uniformGridTime t n k, uniformGridTime_le t n k⟩

/-- Every uniform-grid increment has variance `t/(n+2)`. -/
lemma uniformGrid_incrementVariances (t : ℝ≥0) (n : ℕ) :
    incrementVariances (uniformGridTime t n) =
      fun _ : Fin (n + 2) => t / (n + 2) := by
  funext i
  simp [incrementVariances, uniformGridTime, Nat.cast_succ, add_mul]

/-- Uniform-grid Brownian maxima and canonical Gaussian-increment running
maxima are identically distributed. -/
theorem uniformGridMaximum_identDistrib_runningMax
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    IdentDistrib
      (HDP.Chapter5.finiteMaximum
        (fun k : Fin (n + 3) => B (uniformGridTime t n k)))
      (runningMax : (Fin (n + 2) → ℝ) → ℝ) P
      (gaussianIncrementMeasure
        (fun _ : Fin (n + 2) => t / (n + 2))) := by
  simpa [uniformGrid_incrementVariances] using
    finiteGridMaximum_identDistrib_runningMax hB
      (uniformGridTime t n) (monotone_uniformGridTime t n)
      (uniformGridTime_zero t n)

/-- The endpoint of the uniform-grid increment vector has the Brownian
endpoint law. -/
theorem uniformGridEndpoint_identDistrib_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    IdentDistrib (B t)
      (endpoint : (Fin (n + 2) → ℝ) → ℝ) P
      (gaussianIncrementMeasure
        (fun _ : Fin (n + 2) => t / (n + 2))) := by
  simpa [uniformGrid_incrementVariances] using
    evalLast_identDistrib_endpoint hB
      (uniformGridTime t n) (monotone_uniformGridTime t n)
      (uniformGridTime_zero t n)

/-- Uniform-grid maximum expectations agree in the Brownian and canonical
increment models. -/
theorem integral_uniformGridMaximum_eq_runningMax
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    (∫ ω, HDP.Chapter5.finiteMaximum
        (fun k : Fin (n + 3) => B (uniformGridTime t n k)) ω ∂P) =
      ∫ x, runningMax x
        ∂gaussianIncrementMeasure
          (fun _ : Fin (n + 2) => t / (n + 2)) :=
  (uniformGridMaximum_identDistrib_runningMax hB t n).integral_eq

/-- Absolute endpoint expectations agree for the uniform Brownian grid and
the canonical increment vector. -/
theorem integral_abs_uniformGridEndpoint_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    (∫ x, |endpoint x|
        ∂gaussianIncrementMeasure
          (fun _ : Fin (n + 2) => t / (n + 2))) =
      ∫ ω, |B t ω| ∂P := by
  exact ((uniformGridEndpoint_identDistrib_endpoint hB t n).comp
    measurable_abs).integral_eq.symm

/-- The Brownian maximum on a uniform finite grid is integrable. -/
lemma integrable_uniformGridMaximum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    Integrable
      (HDP.Chapter5.finiteMaximum
        (fun k : Fin (n + 3) => B (uniformGridTime t n k))) P :=
  integrable_finiteMaximum_eval hB (uniformGridTime t n)

end

end HDP.Chapter7.BrownianFiniteGrid
