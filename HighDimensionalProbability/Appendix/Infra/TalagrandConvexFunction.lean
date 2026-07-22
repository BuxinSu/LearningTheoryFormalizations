import HighDimensionalProbability.Appendix.Infra.TalagrandSelfBounding
import Mathlib.Probability.CDF

/-!
# From convex distance to convex-function concentration

This module supplies the measure-theoretic median and finite-dimensional
continuity/separation lemmas needed to apply the convex-distance inequality
to a cube-local convex Lipschitz function.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HDP.Appendix

noncomputable section

/-- The coordinate cube `[-1, 1]ⁿ` in `Fin n → ℝ`. -/
def realCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)

lemma measurableSet_realCube (n : ℕ) : MeasurableSet (realCube n) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma isCompact_realCube (n : ℕ) : IsCompact (realCube n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma convex_realCube (n : ℕ) : Convex ℝ (realCube n) :=
  convex_pi fun _ _ => convex_Icc (-1 : ℝ) 1

lemma ae_mem_realCube_pi {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1) :
    ∀ᵐ x ∂(Measure.pi μ), x ∈ realCube n := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_realCube n)).2
  rw [realCube, Measure.pi_pi]
  simp [hμ]

lemma measureReal_inter_realCube_eq {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1)
    (A : Set (Fin n → ℝ)) :
    (Measure.pi μ).real (A ∩ realCube n) = (Measure.pi μ).real A := by
  apply measureReal_congr
  filter_upwards [ae_mem_realCube_pi μ hμ] with x hx
  apply propext
  exact and_iff_left hx

/-- Every measurable real random variable on a probability space has a
measure-theoretic median. -/
theorem exists_measure_median
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) :
    ∃ M : ℝ,
      (1 / 2 : ℝ) ≤ μ.real {ω | X ω ≤ M} ∧
      (1 / 2 : ℝ) ≤ μ.real {ω | M ≤ X ω} := by
  let ρ : Measure ℝ := Measure.map X μ
  let F : StieltjesFunction ℝ := cdf ρ
  let S : Set ℝ := {a | (1 / 2 : ℝ) ≤ F a}
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hSne : S.Nonempty := by
    obtain ⟨a, ha⟩ :
        ∃ a : ℝ, (1 / 2 : ℝ) < F a :=
      ((tendsto_order.1 (tendsto_cdf_atTop ρ)).1
        (1 / 2) (by norm_num)).exists
    exact ⟨a, ha.le⟩
  have hSbdd : BddBelow S := by
    obtain ⟨b, hb⟩ :
        ∃ b : ℝ, F b < (1 / 2 : ℝ) :=
      ((tendsto_order.1 (tendsto_cdf_atBot ρ)).2
        (1 / 2) (by norm_num)).exists
    refine ⟨b, ?_⟩
    intro a ha
    by_contra hba
    have hab : a < b := lt_of_not_ge hba
    have hmono := (monotone_cdf ρ) hab.le
    dsimp [S] at ha
    linarith
  let M : ℝ := sInf S
  have hSsub : S ⊆ Set.Ici M := by
    intro a ha
    exact csInf_le hSbdd ha
  have hMclosure : M ∈ closure S :=
    csInf_mem_closure hSne hSbdd
  have hFM : (1 / 2 : ℝ) ≤ F M := by
    exact ContinuousWithinAt.closure_le hMclosure continuousWithinAt_const
      ((F.right_continuous M).mono hSsub)
      (fun a ha => ha)
  have hleft : Function.leftLim F M ≤ (1 / 2 : ℝ) := by
    rw [(monotone_cdf ρ).leftLim_eq_sSup
      (neBot_iff.1 (inferInstance : NeBot (𝓝[<] M)))]
    apply csSup_le
    · simp
    · rintro y ⟨a, haM, rfl⟩
      have haNot : a ∉ S := by
        intro haS
        exact (not_lt_of_ge (csInf_le hSbdd haS)) haM
      exact le_of_not_ge haNot
  have hleft0 : 0 ≤ Function.leftLim F M := by
    have hnonneg := cdf_nonneg ρ (M - 1)
    exact hnonneg.trans
      ((monotone_cdf ρ).le_leftLim (by linarith : M - 1 < M))
  have hrealIio :
      ρ.real (Set.Iio M) = Function.leftLim F M := by
    rw [Measure.real, ← measure_cdf ρ,
      (cdf ρ).measure_Iio (tendsto_cdf_atBot ρ)]
    simp only [sub_zero]
    exact ENNReal.toReal_ofReal hleft0
  have hrealIci : (1 / 2 : ℝ) ≤ ρ.real (Set.Ici M) := by
    have hcompl := probReal_add_probReal_compl
      (μ := ρ) (measurableSet_Iio : MeasurableSet (Set.Iio M))
    rw [compl_Iio] at hcompl
    rw [hrealIio] at hcompl
    linarith
  refine ⟨M, ?_, ?_⟩
  · rw [show {ω | X ω ≤ M} = X ⁻¹' Set.Iic M by rfl,
      ← map_measureReal_apply hX measurableSet_Iic]
    rw [← cdf_eq_real ρ M]
    exact hFM
  · rw [show {ω | M ≤ X ω} = X ⁻¹' Set.Ici M by rfl,
      ← map_measureReal_apply hX measurableSet_Ici]
    exact hrealIci

/-- The source's cube-local Euclidean Lipschitz estimate implies continuity
on the cube. -/
lemma continuousOn_of_finEuclidean_lipschitz {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    (hLip : ∀ x ∈ realCube n, ∀ y ∈ realCube n,
      |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    ContinuousOn f (realCube n) := by
  intro y hy
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  let g : (Fin n → ℝ) → ℝ :=
    fun x => Real.sqrt (finEuclideanDistSq x y)
  have hg : Continuous g := by
    dsimp [g, finEuclideanDistSq]
    fun_prop
  have hgy : g y = 0 := by
    simp [g, finEuclideanDistSq]
  have hgev : ∀ᶠ x in 𝓝[realCube n] y, g x < ε := by
    have ht : Tendsto g (𝓝 y) (𝓝 (g y)) := hg.continuousAt.tendsto
    rw [hgy] at ht
    have hev :
        ∀ᶠ x in 𝓝[realCube n] y, dist (g x) 0 < ε :=
      ((Metric.tendsto_nhds.1 ht) ε hε).filter_mono inf_le_left
    filter_upwards [hev] with x hx
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hx
    exact hx
  filter_upwards [hgev, self_mem_nhdsWithin] with x hxg hx
  rw [Real.dist_eq]
  exact (hLip x hx y hy).trans_lt hxg

/-- The sublevel set `{x ∈ [-1,1]ⁿ | f x ≤ a}` of `f` inside the real cube. -/
def convexSublevelInCube {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (a : ℝ) : Set (Fin n → ℝ) :=
  {x ∈ realCube n | f x ≤ a}

lemma isCompact_convexSublevelInCube {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (realCube n)) (a : ℝ) :
    IsCompact (convexSublevelInCube f a) := by
  have hclosed :
      IsClosed {x ∈ realCube n | f x ≤ (fun _ => a) x} :=
    (isCompact_realCube n).isClosed.isClosed_le hf continuousOn_const
  exact IsCompact.of_isClosed_subset (isCompact_realCube n) hclosed
    (fun _ hx => hx.1)

lemma convex_convexSublevelInCube {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ (realCube n) f) (a : ℝ) :
    Convex ℝ (convexSublevelInCube f a) :=
  hf.convex_le a

lemma convexSublevelInCube_subset {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (a : ℝ) :
    convexSublevelInCube f a ⊆ realCube n :=
  fun _ hx => hx.1

lemma convexSublevelInCube_nonempty_of_half_mass {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → ℝ) → ℝ} {a : ℝ}
    (hhalf : (1 / 2 : ℝ) ≤
      (Measure.pi μ).real (convexSublevelInCube f a)) :
    (convexSublevelInCube f a).Nonempty := by
  by_contra hne
  have hempty : convexSublevelInCube f a = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hne
  rw [hempty] at hhalf
  norm_num at hhalf

/-- A point whose function value is at least `t` above a convex sublevel has
normalized squared distance at least `t²/16`. -/
lemma sq_div_sixteen_le_talagrandClampedEnergy_sublevel {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    (hLip : ∀ x ∈ realCube n, ∀ y ∈ realCube n,
      |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2))
    {a t : ℝ} (ht : 0 ≤ t)
    (hK : IsCompact (convexSublevelInCube f a))
    (hKne : (convexSublevelInCube f a).Nonempty)
    {x : Fin n → ℝ} (hx : x ∈ realCube n)
    (hfx : a + t ≤ f x) :
    t ^ 2 / 16 ≤
      talagrandClampedEnergy (convexSublevelInCube f a) x := by
  obtain ⟨p, hp, heq, _⟩ :=
    exists_finEuclideanSetDistSq_eq hK hKne x
  have hpCube : p ∈ realCube n := hp.1
  have hfp : f p ≤ a := hp.2
  have hpx : f p ≤ f x := by linarith
  have hLipxp := hLip x hx p hpCube
  rw [abs_of_nonneg (sub_nonneg.mpr hpx)] at hLipxp
  have htroot :
      t ≤ Real.sqrt (finEuclideanDistSq x p) := by
    exact (by linarith : t ≤ f x - f p).trans hLipxp
  have hsq :
      t ^ 2 ≤ finEuclideanDistSq x p := by
    have hs :=
      (sq_le_sq₀ ht (Real.sqrt_nonneg _)).2 htroot
    rw [Real.sq_sqrt (finEuclideanDistSq_nonneg x p)] at hs
    exact hs
  rw [talagrandClampedEnergy_eq hx]
  dsimp [talagrandDistanceEnergy]
  rw [heq]
  exact div_le_div_of_nonneg_right hsq (by norm_num)

lemma measureReal_convexSublevelInCube_eq {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1)
    (f : (Fin n → ℝ) → ℝ) (a : ℝ) :
    (Measure.pi μ).real (convexSublevelInCube f a) =
      (Measure.pi μ).real {x | f x ≤ a} := by
  apply measureReal_congr
  filter_upwards [ae_mem_realCube_pi μ hμ] with x hx
  apply propext
  exact and_iff_right hx

theorem convex_function_upper_median_tail {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1)
    (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (realCube n) f)
    (hLip : ∀ x ∈ realCube n, ∀ y ∈ realCube n,
      |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2))
    {M : ℝ}
    (hMlow : (1 / 2 : ℝ) ≤ (Measure.pi μ).real {x | f x ≤ M})
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | M + t ≤ f x} ≤
      2 * Real.exp (-(t ^ 2) / 192) := by
  let K : Set (Fin n → ℝ) := convexSublevelInCube f M
  have hfcont := continuousOn_of_finEuclidean_lipschitz hLip
  have hKcompact : IsCompact K :=
    isCompact_convexSublevelInCube hfcont M
  have hKconv : Convex ℝ K :=
    convex_convexSublevelInCube hconv M
  have hKhalf : (1 / 2 : ℝ) ≤ (Measure.pi μ).real K := by
    rw [measureReal_convexSublevelInCube_eq μ hμ f M]
    exact hMlow
  have hKne : K.Nonempty :=
    convexSublevelInCube_nonempty_of_half_mass μ hKhalf
  have htail :=
    talagrandClampedEnergy_half_mass_tail μ hKcompact hKne
      hKconv (convexSublevelInCube_subset f M) hKhalf t
  let B : Set (Fin n → ℝ) := {x | M + t ≤ f x}
  have hsub : B ∩ realCube n ⊆
      {x | t ^ 2 / 16 ≤ talagrandClampedEnergy K x} := by
    intro x hx
    exact sq_div_sixteen_le_talagrandClampedEnergy_sublevel
      hLip ht hKcompact hKne hx.2 hx.1
  calc
    (Measure.pi μ).real B =
        (Measure.pi μ).real (B ∩ realCube n) :=
      (measureReal_inter_realCube_eq μ hμ B).symm
    _ ≤ (Measure.pi μ).real
        {x | t ^ 2 / 16 ≤ talagrandClampedEnergy K x} :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ 2 * Real.exp (-(t ^ 2) / 192) := htail

theorem convex_function_lower_median_tail {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1)
    (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (realCube n) f)
    (hLip : ∀ x ∈ realCube n, ∀ y ∈ realCube n,
      |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2))
    {M : ℝ}
    (hMhigh : (1 / 2 : ℝ) ≤ (Measure.pi μ).real {x | M ≤ f x})
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | f x ≤ M - t} ≤
      2 * Real.exp (-(t ^ 2) / 64) := by
  let K : Set (Fin n → ℝ) := convexSublevelInCube f (M - t)
  have hfcont := continuousOn_of_finEuclidean_lipschitz hLip
  have hKcompact : IsCompact K :=
    isCompact_convexSublevelInCube hfcont (M - t)
  have hKconv : Convex ℝ K :=
    convex_convexSublevelInCube hconv (M - t)
  by_cases hKne : K.Nonempty
  · have hprod :=
      talagrandClampedEnergy_product_bound μ hKcompact hKne
        hKconv (convexSublevelInCube_subset f (M - t)) (t ^ 2 / 16)
    let B : Set (Fin n → ℝ) := {x | M ≤ f x}
    let D : Set (Fin n → ℝ) :=
      {x | t ^ 2 / 16 ≤ talagrandClampedEnergy K x}
    have hsub : B ∩ realCube n ⊆ D := by
      intro x hx
      have hBx : M ≤ f x := hx.1
      apply sq_div_sixteen_le_talagrandClampedEnergy_sublevel
        hLip ht hKcompact hKne hx.2
      linarith
    have hDhalf : (1 / 2 : ℝ) ≤ (Measure.pi μ).real D := by
      calc
        (1 / 2 : ℝ) ≤ (Measure.pi μ).real B := hMhigh
        _ = (Measure.pi μ).real (B ∩ realCube n) :=
          (measureReal_inter_realCube_eq μ hμ B).symm
        _ ≤ (Measure.pi μ).real D :=
          measureReal_mono hsub (measure_ne_top _ _)
    let p : ℝ := (Measure.pi μ).real K
    let q : ℝ := (Measure.pi μ).real D
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hpSq :
        p ^ 2 ≤ 2 * Real.exp (-(t ^ 2) / 32) := by
      have hhalfprod :
          p ^ 2 * (1 / 2 : ℝ) ≤ p ^ 2 * q :=
        mul_le_mul_of_nonneg_left hDhalf (sq_nonneg p)
      have hmain :
          p ^ 2 * q ≤ Real.exp (-(t ^ 2) / 32) := by
        change p ^ 2 * q ≤ Real.exp (-(t ^ 2 / 16) / 2) at hprod
        convert hprod using 1 <;> ring
      nlinarith
    have htarget :
        p ≤ 2 * Real.exp (-(t ^ 2) / 64) := by
      apply (sq_le_sq₀ hp0
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)).mp
      calc
        p ^ 2 ≤ 2 * Real.exp (-(t ^ 2) / 32) := hpSq
        _ ≤ (2 * Real.exp (-(t ^ 2) / 64)) ^ 2 := by
          have heq :
              (Real.exp (-(t ^ 2) / 64)) ^ 2 =
                Real.exp (-(t ^ 2) / 32) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
          rw [mul_pow, heq]
          nlinarith [Real.exp_pos (-(t ^ 2) / 32)]
    dsimp [p, K] at htarget
    rw [measureReal_convexSublevelInCube_eq μ hμ f (M - t)] at htarget
    exact htarget
  · have hempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    have hzero :
        (Measure.pi μ).real {x | f x ≤ M - t} = 0 := by
      rw [← measureReal_convexSublevelInCube_eq μ hμ f (M - t)]
      rw [show convexSublevelInCube f (M - t) = K by rfl, hempty]
      simp
    rw [hzero]
    positivity

/-- Two-sided concentration around a measure median, with a deliberately
rounded universal parameter `32`. -/
theorem convex_function_median_tail {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (-1 : ℝ) 1) = 1)
    (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (realCube n) f)
    (hLip : ∀ x ∈ realCube n, ∀ y ∈ realCube n,
      |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2))
    {M : ℝ}
    (hMlow : (1 / 2 : ℝ) ≤ (Measure.pi μ).real {x | f x ≤ M})
    (hMhigh : (1 / 2 : ℝ) ≤ (Measure.pi μ).real {x | M ≤ f x})
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | t ≤ |f x - M|} ≤
      2 * Real.exp (-(t ^ 2) / 32 ^ 2) := by
  let U : Set (Fin n → ℝ) := {x | M + t ≤ f x}
  let L : Set (Fin n → ℝ) := {x | f x ≤ M - t}
  have hset : {x | t ≤ |f x - M|} = U ∪ L := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, U, L]
    constructor
    · intro hx
      by_cases hMx : M ≤ f x
      · left
        rw [abs_of_nonneg (sub_nonneg.mpr hMx)] at hx
        linarith
      · right
        have hfxM : f x ≤ M := le_of_not_ge hMx
        rw [abs_of_nonpos (sub_nonpos.mpr hfxM)] at hx
        linarith
    · rintro (hx | hx)
      · have hMx : M ≤ f x := by linarith
        rw [abs_of_nonneg (sub_nonneg.mpr hMx)]
        linarith
      · have hfxM : f x ≤ M := by linarith
        rw [abs_of_nonpos (sub_nonpos.mpr hfxM)]
        linarith
  have hupper :
      (Measure.pi μ).real U ≤ 2 * Real.exp (-(t ^ 2) / 192) :=
    convex_function_upper_median_tail μ hμ f hconv hLip hMlow ht
  have hlower64 :
      (Measure.pi μ).real L ≤ 2 * Real.exp (-(t ^ 2) / 64) :=
    convex_function_lower_median_tail μ hμ f hconv hLip hMhigh ht
  have hlower :
      (Measure.pi μ).real L ≤ 2 * Real.exp (-(t ^ 2) / 192) := by
    calc
      (Measure.pi μ).real L ≤ 2 * Real.exp (-(t ^ 2) / 64) := hlower64
      _ ≤ 2 * Real.exp (-(t ^ 2) / 192) := by
        apply mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))
          (by norm_num)
  have hfour :
      (Measure.pi μ).real {x | t ≤ |f x - M|} ≤
        4 * Real.exp (-(t ^ 2) / 192) := by
    rw [hset]
    calc
      (Measure.pi μ).real (U ∪ L) ≤
          (Measure.pi μ).real U + (Measure.pi μ).real L :=
        measureReal_union_le U L
      _ ≤ 2 * Real.exp (-(t ^ 2) / 192) +
          2 * Real.exp (-(t ^ 2) / 192) :=
        add_le_add hupper hlower
      _ = 4 * Real.exp (-(t ^ 2) / 192) := by ring
  by_cases hsmall : t ^ 2 ≤ 512
  · have hexp := Real.add_one_le_exp (-(t ^ 2) / 32 ^ 2)
    have hhalfexp :
        (1 / 2 : ℝ) ≤ Real.exp (-(t ^ 2) / 32 ^ 2) := by
      norm_num at hsmall ⊢
      nlinarith
    calc
      (Measure.pi μ).real {x | t ≤ |f x - M|} ≤ 1 :=
        measureReal_le_one
      _ ≤ 2 * Real.exp (-(t ^ 2) / 32 ^ 2) := by nlinarith
  · have hlarge : 512 < t ^ 2 := lt_of_not_ge hsmall
    have hsplit :
        Real.exp (-(t ^ 2) / 192) ≤
          Real.exp (-(t ^ 2) / 32 ^ 2) *
            Real.exp (-(t ^ 2) / 512) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      norm_num
      nlinarith [sq_nonneg t]
    have htwoExp :
        (2 : ℝ) ≤ Real.exp (t ^ 2 / 512) := by
      calc
        (2 : ℝ) ≤ 1 + t ^ 2 / 512 := by
          nlinarith
        _ ≤ Real.exp (t ^ 2 / 512) :=
          by simpa [add_comm] using Real.add_one_le_exp (t ^ 2 / 512)
    have hfactor :
        2 * Real.exp (-(t ^ 2) / 512) ≤ 1 := by
      calc
        2 * Real.exp (-(t ^ 2) / 512) ≤
            Real.exp (t ^ 2 / 512) *
              Real.exp (-(t ^ 2) / 512) :=
          mul_le_mul_of_nonneg_right htwoExp (Real.exp_pos _).le
        _ = 1 := by
          rw [← Real.exp_add]
          ring_nf
          simp
    calc
      (Measure.pi μ).real {x | t ≤ |f x - M|} ≤
          4 * Real.exp (-(t ^ 2) / 192) := hfour
      _ ≤ 4 * (Real.exp (-(t ^ 2) / 32 ^ 2) *
            Real.exp (-(t ^ 2) / 512)) :=
        mul_le_mul_of_nonneg_left hsplit (by norm_num)
      _ = 2 * Real.exp (-(t ^ 2) / 32 ^ 2) *
            (2 * Real.exp (-(t ^ 2) / 512)) := by ring
      _ ≤ 2 * Real.exp (-(t ^ 2) / 32 ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      _ = 2 * Real.exp (-(t ^ 2) / 32 ^ 2) := by ring

end

end HDP.Appendix
