import HighDimensionalProbability.Appendix.Infra.Concentration
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact

/-!
# Finite-dimensional geometry for Talagrand convex concentration

For a nonempty compact convex set `K` in a real cube, the squared Euclidean
distance has a dimension-free self-bounding property under one-coordinate
minimization.  This is the geometric input to the entropy proof of convex
concentration.
-/

open Set Filter
open scoped BigOperators Topology

namespace HDP.Appendix

noncomputable section

/-- Squared Euclidean distance on a finite real product.  We keep this
explicit because the ambient `Pi` norm is not the Euclidean norm. -/
def finEuclideanDistSq {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, (x i - y i) ^ 2

lemma finEuclideanDistSq_nonneg {n : ℕ} (x y : Fin n → ℝ) :
    0 ≤ finEuclideanDistSq x y := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

lemma continuous_finEuclideanDistSq {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      finEuclideanDistSq p.1 p.2) := by
  unfold finEuclideanDistSq
  fun_prop

/-- Squared Euclidean distance from a set, represented as a compact minimum
when the set is compact and nonempty. -/
def finEuclideanSetDistSq {n : ℕ} (K : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ :=
  sInf ((fun y => finEuclideanDistSq x y) '' K)

lemma continuous_finEuclideanSetDistSq {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    Continuous (finEuclideanSetDistSq K) := by
  unfold finEuclideanSetDistSq
  apply hK.continuous_sInf
  exact continuous_finEuclideanDistSq

lemma exists_finEuclideanSetDistSq_eq {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (x : Fin n → ℝ) :
    ∃ p ∈ K, finEuclideanSetDistSq K x = finEuclideanDistSq x p ∧
      ∀ q ∈ K, finEuclideanDistSq x p ≤ finEuclideanDistSq x q := by
  have hcont : ContinuousOn (fun y => finEuclideanDistSq x y) K :=
    (continuous_finEuclideanDistSq.comp
      (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨p, hp, heq, hmin⟩ :=
    hK.exists_sInf_image_eq_and_le hKne hcont
  exact ⟨p, hp, heq, hmin⟩

lemma finEuclideanSetDistSq_nonneg {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (x : Fin n → ℝ) :
    0 ≤ finEuclideanSetDistSq K x := by
  obtain ⟨p, hp, heq, _⟩ :=
    exists_finEuclideanSetDistSq_eq hK hKne x
  rw [heq]
  exact finEuclideanDistSq_nonneg x p

lemma finEuclideanSetDistSq_eq_zero_of_mem {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    {x : Fin n → ℝ} (hx : x ∈ K) :
    finEuclideanSetDistSq K x = 0 := by
  obtain ⟨p, hp, heq, hmin⟩ :=
    exists_finEuclideanSetDistSq_eq hK hKne x
  have hle := hmin x hx
  have hzero : finEuclideanDistSq x x = 0 := by
    simp [finEuclideanDistSq]
  rw [hzero] at hle
  exact le_antisymm (heq.trans_le hle)
    (finEuclideanSetDistSq_nonneg hK hKne x)

/-- Minimum of a continuous function after varying one cube coordinate. -/
def coordinateCubeMinimum {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun y : ℝ => f (Function.update x i y)) '' Set.Icc (-1 : ℝ) 1)

lemma continuous_coordinateCubeMinimum {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (i : Fin n) :
    Continuous (coordinateCubeMinimum f i) := by
  unfold coordinateCubeMinimum
  apply isCompact_Icc.continuous_sInf
  exact hf.comp (by fun_prop)

lemma coordinateCubeMinimum_update {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) (z : ℝ) :
    coordinateCubeMinimum f i (Function.update x i z) =
      coordinateCubeMinimum f i x := by
  unfold coordinateCubeMinimum
  congr 1
  ext r
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [Function.update_idem]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [Function.update_idem]

lemma coordinateCubeMinimum_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (i : Fin n) (x : Fin n → ℝ) (hxi : x i ∈ Set.Icc (-1 : ℝ) 1) :
    coordinateCubeMinimum f i x ≤ f x := by
  unfold coordinateCubeMinimum
  have hcont :
      ContinuousOn (fun y : ℝ => f (Function.update x i y))
        (Set.Icc (-1 : ℝ) 1) :=
    (hf.comp (by fun_prop)).continuousOn
  have hle := hcont.sInf_image_Icc_le hxi
  simpa using hle

lemma exists_coordinateCubeMinimum_eq {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (i : Fin n) (x : Fin n → ℝ) :
    ∃ y ∈ Set.Icc (-1 : ℝ) 1,
      coordinateCubeMinimum f i x = f (Function.update x i y) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        f (Function.update x i y) ≤ f (Function.update x i z) := by
  simpa [coordinateCubeMinimum] using
    isCompact_Icc.exists_sInf_image_eq_and_le
      (nonempty_Icc.2 (by norm_num : (-1 : ℝ) ≤ 1))
      ((hf.comp (by fun_prop)).continuousOn)

/-- First-order optimality of a closest point to a compact convex set. -/
lemma closestPoint_support {n : ℕ}
    {K : Set (Fin n → ℝ)} (hKconv : Convex ℝ K)
    {x p : Fin n → ℝ} (hp : p ∈ K)
    (hmin : ∀ q ∈ K,
      finEuclideanDistSq x p ≤ finEuclideanDistSq x q)
    {q : Fin n → ℝ} (hq : q ∈ K) :
    ∑ i, (x i - p i) * (q i - p i) ≤ 0 := by
  let S : ℝ := ∑ i, (x i - p i) * (q i - p i)
  let Q : ℝ := ∑ i, (q i - p i) ^ 2
  have hstep (k : ℕ) :
      2 * S ≤ (1 / ((k + 1 : ℕ) : ℝ)) * Q := by
    let t : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
    have hden : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have ht0 : 0 ≤ t := (one_div_pos.mpr hden).le
    have ht1 : t ≤ 1 := by
      apply (div_le_one hden).2
      norm_num
    let z : Fin n → ℝ := (1 - t) • p + t • q
    have hz : z ∈ K := by
      exact hKconv hp hq (sub_nonneg.mpr ht1) ht0 (by ring)
    have hdist := hmin z hz
    have hexpand :
        finEuclideanDistSq x z =
          finEuclideanDistSq x p - 2 * t * S + t ^ 2 * Q := by
      simp only [finEuclideanDistSq, z, S, Q, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      calc
        ∑ i, (x i - ((1 - t) * p i + t * q i)) ^ 2 =
            ∑ i, ((x i - p i) ^ 2 -
              (2 * t) * ((x i - p i) * (q i - p i)) +
              t ^ 2 * (q i - p i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i, (x i - p i) ^ 2) -
              2 * t * (∑ i, (x i - p i) * (q i - p i)) +
              t ^ 2 * (∑ i, (q i - p i) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.mul_sum]
    rw [hexpand] at hdist
    have htpos : 0 < 1 / ((k + 1 : ℕ) : ℝ) :=
      one_div_pos.mpr hden
    change 2 * S ≤ t * Q
    nlinarith
  have hlim :
      Tendsto (fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ)) * Q)
        atTop (𝓝 0) := by
    simpa using
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const Q
  have hS : 2 * S ≤ 0 :=
    ge_of_tendsto' hlim hstep
  dsimp [S] at hS ⊢
  linarith

/-- Subgradient inequality for squared distance to a compact convex set. -/
lemma finEuclideanSetDistSq_subgradient {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K) (x : Fin n → ℝ) :
    ∃ p ∈ K,
      finEuclideanSetDistSq K x = finEuclideanDistSq x p ∧
      ∀ z : Fin n → ℝ,
        finEuclideanSetDistSq K x +
            2 * ∑ i, (x i - p i) * (z i - x i) ≤
          finEuclideanSetDistSq K z := by
  obtain ⟨p, hp, heq, hmin⟩ :=
    exists_finEuclideanSetDistSq_eq hK hKne x
  refine ⟨p, hp, heq, ?_⟩
  intro z
  obtain ⟨q, hq, hzq, _⟩ :=
    exists_finEuclideanSetDistSq_eq hK hKne z
  have hsupp := closestPoint_support hKconv hp hmin hq
  rw [heq, hzq]
  dsimp [finEuclideanDistSq] at *
  calc
    (∑ i, (x i - p i) ^ 2) +
          2 * ∑ i, (x i - p i) * (z i - x i) =
        ∑ i, ((x i - p i) ^ 2 +
          2 * ((x i - p i) * (z i - x i))) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ i, ((z i - q i) ^ 2 +
          2 * ((x i - p i) * (q i - p i))) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg ((z i - x i) - (q i - p i))]
    _ = (∑ i, (z i - q i) ^ 2) +
          2 * ∑ i, (x i - p i) * (q i - p i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ i, (z i - q i) ^ 2 := by
      nlinarith

/-- The normalized squared distance used in the entropy argument. -/
def talagrandDistanceEnergy {n : ℕ} (K : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ :=
  finEuclideanSetDistSq K x / 16

lemma continuous_talagrandDistanceEnergy {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    Continuous (talagrandDistanceEnergy K) :=
  (continuous_finEuclideanSetDistSq hK).div_const 16

/-- Coordinatewise projection onto the closed cube. -/
def talagrandCubeClamp {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (Set.projIcc (-1 : ℝ) 1 (by norm_num) (x i) : ℝ)

lemma continuous_talagrandCubeClamp {n : ℕ} :
    Continuous (talagrandCubeClamp : (Fin n → ℝ) → (Fin n → ℝ)) := by
  unfold talagrandCubeClamp
  fun_prop

lemma talagrandCubeClamp_mem {n : ℕ} (x : Fin n → ℝ) :
    talagrandCubeClamp x ∈
      Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
  intro i _
  exact (Set.projIcc (-1 : ℝ) 1 (by norm_num) (x i)).property

lemma talagrandCubeClamp_eq_self {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)) :
    talagrandCubeClamp x = x := by
  funext i
  exact congrArg Subtype.val
    (Set.projIcc_of_mem (by norm_num)
      (hx i (Set.mem_univ i)))

lemma coordinateCubeMinimum_clamp_invariant {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    {x y : Fin n → ℝ}
    (hxy : ∀ j, j ≠ i → x j = y j) :
    coordinateCubeMinimum f i (talagrandCubeClamp x) =
      coordinateCubeMinimum f i (talagrandCubeClamp y) := by
  have heq :
      talagrandCubeClamp y =
        Function.update (talagrandCubeClamp x) i
          (talagrandCubeClamp y i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji, talagrandCubeClamp,
        hxy j hji]
  rw [heq, coordinateCubeMinimum_update]

/-- Uniform bounds for normalized squared distance on the cube. -/
lemma talagrandDistanceEnergy_bounds {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    {x : Fin n → ℝ}
    (hx : x ∈ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)) :
    0 ≤ talagrandDistanceEnergy K x ∧
      talagrandDistanceEnergy K x ≤ (n : ℝ) / 4 := by
  obtain ⟨q, hq, heq, hmin⟩ :=
    exists_finEuclideanSetDistSq_eq hK hKne x
  obtain ⟨p, hp⟩ := hKne
  have hpCube := hKcube hp
  have hcoord (i : Fin n) : (x i - p i) ^ 2 ≤ 4 := by
    have hxi := hx i (Set.mem_univ i)
    have hpi := hpCube i (Set.mem_univ i)
    have habs : |x i - p i| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hxi.1, hxi.2, hpi.1, hpi.2]
    have hs :=
      (sq_le_sq₀ (abs_nonneg (x i - p i)) (by norm_num : (0 : ℝ) ≤ 2)).2 habs
    rw [sq_abs] at hs
    norm_num at hs
    exact hs
  constructor
  · exact div_nonneg
      (finEuclideanSetDistSq_nonneg hK ⟨p, hp⟩ x) (by norm_num)
  · have hdist :
        finEuclideanSetDistSq K x ≤ 4 * (n : ℝ) := by
      calc
        finEuclideanSetDistSq K x =
            finEuclideanDistSq x q := heq
        _ ≤ finEuclideanDistSq x p := hmin p hp
        _ = ∑ i, (x i - p i) ^ 2 := rfl
        _ ≤ ∑ _i : Fin n, (4 : ℝ) :=
          Finset.sum_le_sum fun i _ => hcoord i
        _ = 4 * (n : ℝ) := by simp [mul_comm]
    dsimp [talagrandDistanceEnergy]
    linarith

/-- Coordinate decrements of normalized squared distance are self-bounding.
The point `x` and the minimizing set lie in the cube. -/
lemma talagrandDistanceEnergy_coordinate_self_bounding {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    {x : Fin n → ℝ}
    (hx : x ∈ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)) :
    let Z := talagrandDistanceEnergy K
    (∀ i, 0 ≤ Z x - coordinateCubeMinimum Z i x) ∧
    (∀ i, Z x - coordinateCubeMinimum Z i x ≤
      |(Classical.choose
        (finEuclideanSetDistSq_subgradient hK hKne hKconv x)) i - x i| / 4) ∧
    (∑ i, (Z x - coordinateCubeMinimum Z i x) ^ 2 ≤ Z x) ∧
    (∀ i, Z x - coordinateCubeMinimum Z i x ≤ 1 / 2) := by
  classical
  dsimp only
  let p : Fin n → ℝ :=
    Classical.choose
      (finEuclideanSetDistSq_subgradient hK hKne hKconv x)
  have hpData :=
    Classical.choose_spec
      (finEuclideanSetDistSq_subgradient hK hKne hKconv x)
  have hpK : p ∈ K := hpData.1
  have hpEq :
      finEuclideanSetDistSq K x = finEuclideanDistSq x p :=
    hpData.2.1
  have hpSub :
      ∀ z : Fin n → ℝ,
        finEuclideanSetDistSq K x +
            2 * ∑ i, (x i - p i) * (z i - x i) ≤
          finEuclideanSetDistSq K z := by
    simpa [p] using hpData.2.2
  have hpx : ∀ i, |p i - x i| ≤ 2 := by
    intro i
    have hpi := hKcube hpK i (Set.mem_univ i)
    have hxi := hx i (Set.mem_univ i)
    rw [abs_le]
    constructor <;> linarith [hpi.1, hpi.2, hxi.1, hxi.2]
  have hdec_nonneg (i : Fin n) :
      0 ≤ talagrandDistanceEnergy K x -
        coordinateCubeMinimum (talagrandDistanceEnergy K) i x := by
    exact sub_nonneg.mpr
      (coordinateCubeMinimum_le
        (continuous_talagrandDistanceEnergy hK) i x
        (hx i (Set.mem_univ i)))
  have hdec_bound (i : Fin n) :
      talagrandDistanceEnergy K x -
          coordinateCubeMinimum (talagrandDistanceEnergy K) i x ≤
        |p i - x i| / 4 := by
    obtain ⟨y, hy, hminEq, _⟩ :=
      exists_coordinateCubeMinimum_eq
        (continuous_talagrandDistanceEnergy hK) i x
    let z := Function.update x i y
    have hsub := hpSub z
    have hsum :
        ∑ j, (x j - p j) * (z j - x j) =
          (x i - p i) * (y - x i) := by
      calc
        ∑ j, (x j - p j) * (z j - x j) =
            (x i - p i) * (z i - x i) := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            simp [z, Function.update_of_ne hji]
          · simp
        _ = (x i - p i) * (y - x i) := by simp [z]
    rw [hsum] at hsub
    rw [hminEq]
    dsimp [talagrandDistanceEnergy]
    have habs :
        (x i - p i) * (x i - y) ≤
          |p i - x i| * 2 := by
      have hxy : |x i - y| ≤ 2 := by
        have hxi := hx i (Set.mem_univ i)
        rw [abs_le]
        constructor <;> linarith [hxi.1, hxi.2, hy.1, hy.2]
      calc
        (x i - p i) * (x i - y) ≤
            |(x i - p i) * (x i - y)| := le_abs_self _
        _ = |x i - p i| * |x i - y| := abs_mul _ _
        _ ≤ |x i - p i| * 2 :=
          mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
        _ = |p i - x i| * 2 := by rw [abs_sub_comm]
    have hcore :
        finEuclideanSetDistSq K x -
            finEuclideanSetDistSq K z ≤ 4 * |p i - x i| := by
      nlinarith
    linarith
  refine ⟨hdec_nonneg, hdec_bound, ?_, ?_⟩
  · calc
      ∑ i, (talagrandDistanceEnergy K x -
          coordinateCubeMinimum (talagrandDistanceEnergy K) i x) ^ 2 ≤
          ∑ i, (|p i - x i| / 4) ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          (sq_le_sq₀ (hdec_nonneg i)
            (div_nonneg (abs_nonneg _) (by norm_num))).2 (hdec_bound i)
      _ = finEuclideanDistSq x p / 16 := by
        unfold finEuclideanDistSq
        calc
          ∑ i, (|p i - x i| / 4) ^ 2 =
              ∑ i, (x i - p i) ^ 2 / 16 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [div_pow, sq_abs, sub_sq_comm (p i) (x i)]
            norm_num
          _ = (∑ i, (x i - p i) ^ 2) / 16 := by
            rw [Finset.sum_div]
      _ = talagrandDistanceEnergy K x := by
        rw [← hpEq]
        rfl
  · intro i
    exact (hdec_bound i).trans (by
      have := hpx i
      linarith)

end

end HDP.Appendix
