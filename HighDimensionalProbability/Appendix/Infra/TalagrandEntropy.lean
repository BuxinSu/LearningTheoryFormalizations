import HighDimensionalProbability.Appendix.Infra.ProductEntropy
import HighDimensionalProbability.Appendix.Infra.TalagrandGeometry

/-!
# Entropy estimates for self-bounding distance energies

This module contains the scalar exponential estimates used after product
entropy tensorization.  The coordinate decrements in
`TalagrandGeometry` are at most `1 / 2`, so parameters in `[0,2]` remain
inside the unit interval where the elementary exponential remainder estimate
applies.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Appendix

noncomputable section

lemma exp_sub_one_sub_id_le_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u - 1 - u ≤ u ^ 2 := by
  exact (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hu)

lemma exp_neg_sub_one_add_id_le_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp (-u) - 1 + u ≤ u ^ 2 := by
  have h :=
    exp_sub_one_sub_id_le_sq (u := -u) (by simpa using hu)
  nlinarith

lemma scalarRelEntropy_exp_sub
    (s u : ℝ) :
    scalarRelEntropy (Real.exp s) (Real.exp (s - u)) =
      Real.exp s * (u + Real.exp (-u) - 1) := by
  rw [scalarRelEntropy,
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  rw [show s - u = s + (-u) by ring, Real.exp_add]
  ring

lemma scalarRelEntropy_exp_add
    (s u : ℝ) :
    scalarRelEntropy (Real.exp s) (Real.exp (s + u)) =
      Real.exp s * (-u + Real.exp u - 1) := by
  rw [scalarRelEntropy,
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp, Real.exp_add]
  ring

/-- Cost estimate when the comparison density is obtained by decreasing the
exponent. -/
lemma scalarRelEntropy_exp_sub_le
    {s u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    scalarRelEntropy (Real.exp s) (Real.exp (s - u)) ≤
      Real.exp s * u ^ 2 := by
  rw [scalarRelEntropy_exp_sub]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hrem :=
    exp_neg_sub_one_add_id_le_sq
      (show |u| ≤ 1 by simpa [abs_of_nonneg hu0] using hu1)
  linarith

/-- Cost estimate when the comparison density is obtained by increasing the
exponent. -/
lemma scalarRelEntropy_exp_add_le
    {s u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    scalarRelEntropy (Real.exp s) (Real.exp (s + u)) ≤
      Real.exp s * u ^ 2 := by
  rw [scalarRelEntropy_exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hrem :=
    exp_sub_one_sub_id_le_sq
      (show |u| ≤ 1 by simpa [abs_of_nonneg hu0] using hu1)
  linarith

/-- The globally defined version of the distance energy, obtained by
coordinatewise projection onto the cube.  On the support of the product
measure this agrees with `talagrandDistanceEnergy`. -/
def talagrandClampedEnergy {n : ℕ} (K : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ :=
  talagrandDistanceEnergy K (talagrandCubeClamp x)

lemma continuous_talagrandClampedEnergy {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    Continuous (talagrandClampedEnergy K) :=
  (continuous_talagrandDistanceEnergy hK).comp
    continuous_talagrandCubeClamp

lemma talagrandClampedEnergy_eq {n : ℕ}
    {K : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)) :
    talagrandClampedEnergy K x = talagrandDistanceEnergy K x := by
  simp only [talagrandClampedEnergy, talagrandCubeClamp_eq_self hx]

lemma talagrandClampedEnergy_bounds {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    (x : Fin n → ℝ) :
    0 ≤ talagrandClampedEnergy K x ∧
      talagrandClampedEnergy K x ≤ (n : ℝ) / 4 := by
  exact talagrandDistanceEnergy_bounds hK hKne hKcube
    (talagrandCubeClamp_mem x)

lemma coordinateCubeMinimum_talagrandDistanceEnergy_bounds {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    (i : Fin n) {x : Fin n → ℝ}
    (hx : x ∈ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)) :
    0 ≤ coordinateCubeMinimum (talagrandDistanceEnergy K) i x ∧
      coordinateCubeMinimum (talagrandDistanceEnergy K) i x ≤
        (n : ℝ) / 4 := by
  obtain ⟨y, hy, heq, _⟩ :=
    exists_coordinateCubeMinimum_eq
      (continuous_talagrandDistanceEnergy hK) i x
  have hupdate :
      Function.update x i y ∈
        Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
    intro j _
    by_cases hji : j = i
    · subst j
      simpa using hy
    · simpa [Function.update_of_ne hji] using hx j (Set.mem_univ j)
  rw [heq]
  exact talagrandDistanceEnergy_bounds hK hKne hKcube hupdate

/-- Pointwise entropy cost of the coordinate comparisons.  This is the
finite-dimensional self-bounding estimate, valid for tilts of either sign. -/
lemma sum_scalarRelEntropy_exp_talagrand_le {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    {θ : ℝ} (hθ : |θ| ≤ 2) (x : Fin n → ℝ) :
    (∑ i, scalarRelEntropy
        (Real.exp (θ * talagrandClampedEnergy K x))
        (Real.exp (θ * coordinateCubeMinimum
          (talagrandDistanceEnergy K) i (talagrandCubeClamp x)))) ≤
      θ ^ 2 * Real.exp (θ * talagrandClampedEnergy K x) *
        talagrandClampedEnergy K x := by
  let q : Fin n → ℝ := talagrandCubeClamp x
  let Z : ℝ := talagrandDistanceEnergy K q
  let m : Fin n → ℝ :=
    fun i => coordinateCubeMinimum (talagrandDistanceEnergy K) i q
  let d : Fin n → ℝ := fun i => Z - m i
  have hself :=
    talagrandDistanceEnergy_coordinate_self_bounding
      hK hKne hKconv hKcube (talagrandCubeClamp_mem x)
  have hd0 (i : Fin n) : 0 ≤ d i := by
    simpa only [q, Z, m, d] using hself.1 i
  have hdsum : ∑ i, (d i) ^ 2 ≤ Z := by
    simpa only [q, Z, m, d] using hself.2.2.1
  have hdhalf (i : Fin n) : d i ≤ 1 / 2 := by
    simpa only [q, Z, m, d] using hself.2.2.2 i
  have hcost (i : Fin n) :
      scalarRelEntropy (Real.exp (θ * Z)) (Real.exp (θ * m i)) ≤
        Real.exp (θ * Z) * (θ * d i) ^ 2 := by
    by_cases hθ0 : 0 ≤ θ
    · have hu0 : 0 ≤ θ * d i := mul_nonneg hθ0 (hd0 i)
      have hθle : θ ≤ 2 := (le_abs_self θ).trans hθ
      have hu1 : θ * d i ≤ 1 := by
        nlinarith [hdhalf i]
      have heq : θ * m i = θ * Z - θ * d i := by
        dsimp [d]
        ring
      rw [heq]
      exact scalarRelEntropy_exp_sub_le hu0 hu1
    · have hθneg : θ < 0 := lt_of_not_ge hθ0
      have hu0 : 0 ≤ (-θ) * d i :=
        mul_nonneg (by linarith) (hd0 i)
      have hnegθle : -θ ≤ 2 := by
        have := (neg_le_abs θ).trans hθ
        linarith
      have hu1 : (-θ) * d i ≤ 1 := by
        nlinarith [hdhalf i]
      have heq : θ * m i = θ * Z + (-θ) * d i := by
        dsimp [d]
        ring
      rw [heq]
      have hc := scalarRelEntropy_exp_add_le
        (s := θ * Z) (u := (-θ) * d i) hu0 hu1
      convert hc using 1 <;> ring
  change (∑ i, scalarRelEntropy (Real.exp (θ * Z))
      (Real.exp (θ * m i))) ≤ θ ^ 2 * Real.exp (θ * Z) * Z
  calc
    (∑ i, scalarRelEntropy (Real.exp (θ * Z))
        (Real.exp (θ * m i))) ≤
        ∑ i, Real.exp (θ * Z) * (θ * d i) ^ 2 :=
      Finset.sum_le_sum fun i _ => hcost i
    _ = (θ ^ 2 * Real.exp (θ * Z)) * ∑ i, (d i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (θ ^ 2 * Real.exp (θ * Z)) * Z :=
      mul_le_mul_of_nonneg_left hdsum
        (mul_nonneg (sq_nonneg θ) (Real.exp_pos _).le)
    _ = θ ^ 2 * Real.exp (θ * Z) * Z := by ring

/-- Tensorized entropy estimate for the clamped distance energy under an
arbitrary product probability measure. -/
theorem boltzmannEntropy_exp_talagrandClampedEnergy_le {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    {θ : ℝ} (hθ : |θ| ≤ 2) :
    boltzmannEntropy (Measure.pi μ)
        (fun x => Real.exp (θ * talagrandClampedEnergy K x)) ≤
      θ ^ 2 * ∫ x, talagrandClampedEnergy K x *
        Real.exp (θ * talagrandClampedEnergy K x) ∂(Measure.pi μ) := by
  let E : (Fin n → ℝ) → ℝ := talagrandClampedEnergy K
  let F : (Fin n → ℝ) → ℝ := fun x => Real.exp (θ * E x)
  let c : Fin n → (Fin n → ℝ) → ℝ :=
    fun i x => Real.exp (θ * coordinateCubeMinimum
      (talagrandDistanceEnergy K) i (talagrandCubeClamp x))
  let δ : ℝ := Real.exp (-(n : ℝ))
  let M : ℝ := Real.exp (n : ℝ)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hθbounds : -2 ≤ θ ∧ θ ≤ 2 := by
    simpa only [abs_le] using hθ
  have hθsq : θ ^ 2 ≤ 4 := by
    have hs :=
      (sq_le_sq₀ (abs_nonneg θ) (by norm_num : (0 : ℝ) ≤ 2)).2 hθ
    rw [sq_abs] at hs
    norm_num at hs
    exact hs
  have hexponent_bounds {v : ℝ}
      (hv : 0 ≤ v ∧ v ≤ (n : ℝ) / 4) :
      -(n : ℝ) ≤ θ * v ∧ θ * v ≤ (n : ℝ) := by
    have hlo : 0 ≤ (θ + 2) * v :=
      mul_nonneg (by linarith [hθbounds.1]) hv.1
    have hhi : 0 ≤ (2 - θ) * v :=
      mul_nonneg (by linarith [hθbounds.2]) hv.1
    constructor <;> nlinarith [hv.2]
  have hδ : 0 < δ := Real.exp_pos _
  have hδM : δ ≤ M := by
    apply Real.exp_le_exp.mpr
    change -(n : ℝ) ≤ (n : ℝ)
    linarith
  have hE : Measurable E :=
    (continuous_talagrandClampedEnergy hK).measurable
  have hF : Measurable F :=
    (Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_talagrandClampedEnergy hK))).measurable
  have hc (i : Fin n) : Measurable (c i) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul
        ((continuous_coordinateCubeMinimum
          (continuous_talagrandDistanceEnergy hK) i).comp
            continuous_talagrandCubeClamp))).measurable
  have hFB : HasUniformPositiveBounds δ M F := by
    intro x
    have hb := hexponent_bounds (talagrandClampedEnergy_bounds
      hK hKne hKcube x)
    exact ⟨Real.exp_le_exp.mpr hb.1, Real.exp_le_exp.mpr hb.2⟩
  have hcB (i : Fin n) : HasUniformPositiveBounds δ M (c i) := by
    intro x
    have hv :=
      coordinateCubeMinimum_talagrandDistanceEnergy_bounds
        hK hKne hKcube i (talagrandCubeClamp_mem x)
    have hb := hexponent_bounds hv
    exact ⟨Real.exp_le_exp.mpr hb.1, Real.exp_le_exp.mpr hb.2⟩
  have hcInvariant :
      ∀ i x y, (∀ j, j ≠ i → x j = y j) → c i x = c i y := by
    intro i x y hxy
    dsimp [c]
    congr 2
    exact coordinateCubeMinimum_clamp_invariant
      (talagrandDistanceEnergy K) i hxy
  have htensor :
      boltzmannEntropy (Measure.pi μ) F ≤
        ∫ x, ∑ i, scalarRelEntropy (F x) (c i x) ∂(Measure.pi μ) :=
    boltzmannEntropy_pi_le_sum_scalarRelEntropy μ F c
      hδ hδM hF hc hFB hcB hcInvariant
  have hcostInt (i : Fin n) :
      Integrable (fun x => scalarRelEntropy (F x) (c i x))
        (Measure.pi μ) :=
    integrable_scalarRelEntropy_of_bounds hδ hδM hF (hc i) hFB (hcB i)
  have hcostSumInt :
      Integrable (fun x => ∑ i, scalarRelEntropy (F x) (c i x))
        (Measure.pi μ) := by
    simpa only using
      (integrable_finsetSum Finset.univ (fun i _ => hcostInt i))
  have hEint : Integrable E (Measure.pi μ) := by
    apply Integrable.of_bound hE.aestronglyMeasurable ((n : ℝ) / 4)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (talagrandClampedEnergy_bounds
          hK hKne hKcube x).1]
      exact (talagrandClampedEnergy_bounds hK hKne hKcube x).2
  have hmultBound :
      ∀ᵐ x ∂(Measure.pi μ), ‖θ ^ 2 * F x‖ ≤ 4 * M := by
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg θ) (Real.exp_pos _).le)]
      exact mul_le_mul hθsq (hFB x).2
        (Real.exp_pos _).le (by norm_num)
  have hrightInt :
      Integrable (fun x => θ ^ 2 * F x * E x) (Measure.pi μ) :=
    hEint.bdd_mul
      ((hF.const_mul (θ ^ 2)).aestronglyMeasurable)
      hmultBound
  have hpoint (x : Fin n → ℝ) :
      (∑ i, scalarRelEntropy (F x) (c i x)) ≤
        θ ^ 2 * F x * E x := by
    simpa only [F, c, E, mul_assoc] using
      sum_scalarRelEntropy_exp_talagrand_le
        hK hKne hKconv hKcube hθ x
  change boltzmannEntropy (Measure.pi μ) F ≤
    θ ^ 2 * ∫ x, E x * F x ∂(Measure.pi μ)
  calc
    boltzmannEntropy (Measure.pi μ) F ≤
        ∫ x, ∑ i, scalarRelEntropy (F x) (c i x) ∂(Measure.pi μ) :=
      htensor
    _ ≤ ∫ x, θ ^ 2 * F x * E x ∂(Measure.pi μ) :=
      integral_mono hcostSumInt hrightInt hpoint
    _ = ∫ x, θ ^ 2 * (F x * E x) ∂(Measure.pi μ) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = θ ^ 2 * ∫ x, F x * E x ∂(Measure.pi μ) :=
      integral_const_mul _ _
    _ = θ ^ 2 * ∫ x, E x * F x ∂(Measure.pi μ) := by
      apply congrArg (fun z : ℝ => θ ^ 2 * z)
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- Entropy inequality characteristic of a nonnegative self-bounding random
variable.  The first field supplies the analytic neighborhood needed for the
cumulant-generating-function argument. -/
def HasSelfBoundingEntropyBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) ∧
  ∀ t : ℝ, |t| ≤ 2 →
    t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ -
        mgf X μ t * Real.log (mgf X μ t) ≤
      t ^ 2 * ∫ ω, X ω * Real.exp (t * X ω) ∂μ

lemma boltzmannEntropy_exp_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    boltzmannEntropy μ (fun ω => Real.exp (t * X ω)) =
      t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ -
        mgf X μ t * Real.log (mgf X μ t) := by
  rw [boltzmannEntropy, mgf]
  congr 1
  calc
    (∫ ω, Real.exp (t * X ω) *
          Real.log (Real.exp (t * X ω)) ∂μ) =
        ∫ ω, t * (X ω * Real.exp (t * X ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.log_exp]
      ring
    _ = t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ :=
      integral_const_mul _ _

lemma integrable_exp_talagrandClampedEnergy {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1))
    (t : ℝ) :
    Integrable
      (fun x => Real.exp (t * talagrandClampedEnergy K x))
      (Measure.pi μ) := by
  let B : ℝ := Real.exp (|t| * ((n : ℝ) / 4))
  apply Integrable.of_bound
    ((Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_talagrandClampedEnergy hK))).measurable.aestronglyMeasurable)
    B
  exact ae_of_all _ fun x => by
    change |Real.exp (t * talagrandClampedEnergy K x)| ≤ B
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hE := talagrandClampedEnergy_bounds hK hKne hKcube x
    calc
      t * talagrandClampedEnergy K x ≤
          |t| * talagrandClampedEnergy K x :=
        mul_le_mul_of_nonneg_right (le_abs_self t) hE.1
      _ ≤ |t| * ((n : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hE.2 (abs_nonneg t)

/-- The product entropy theorem furnishes the abstract self-bounding entropy
predicate for the normalized convex-set distance. -/
theorem hasSelfBoundingEntropyBound_talagrandClampedEnergy {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKconv : Convex ℝ K)
    (hKcube : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)) :
    HasSelfBoundingEntropyBound (Measure.pi μ)
      (talagrandClampedEnergy K) := by
  constructor
  · exact integrable_exp_talagrandClampedEnergy μ hK hKne hKcube
  · intro t ht
    rw [← boltzmannEntropy_exp_eq]
    calc
      boltzmannEntropy (Measure.pi μ)
          (fun x => Real.exp (t * talagrandClampedEnergy K x)) ≤
          t ^ 2 * ∫ x, talagrandClampedEnergy K x *
            Real.exp (t * talagrandClampedEnergy K x) ∂(Measure.pi μ) :=
        boltzmannEntropy_exp_talagrandClampedEnergy_le
          μ hK hKne hKconv hKcube ht
      _ = t ^ 2 * ∫ x, talagrandClampedEnergy K x *
            Real.exp (t * talagrandClampedEnergy K x) ∂(Measure.pi μ) := rfl

end

end HDP.Appendix
