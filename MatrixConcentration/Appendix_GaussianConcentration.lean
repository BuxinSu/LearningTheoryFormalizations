import MatrixConcentration.Appendix_GoldenThompson
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Appendix: Gaussian concentration

This module proves **Book equation (4.1.8)** through the following components.

This consolidated appendix contains:

* the one-dimensional Brunn–Minkowski and Prékopa–Leindler inequalities;
* tensorized Gaussian Prékopa–Leindler inequalities;
* sharp Gaussian concentration for Lipschitz functions;
* matrix Gaussian concentration via the weak-variance Lipschitz bound.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.4: One-dimensional Prékopa–Leindler inequality

This section develops from first principles the one-dimensional geometric
inequalities needed for the proof of **Book eq. (4.1.8)**:

* `oneDim_brunn_minkowski` — the one-dimensional Brunn–Minkowski
  inequality `vol K₁ + vol K₂ ≤ vol (K₁ + K₂)` for nonempty compact sets
  (translates of `K₁` and `K₂` sit inside `K₁ + K₂` overlapping in at
  most one point);
* `oneDim_brunn_minkowski_measurable` — its extension to nonempty
  measurable sets, by inner regularity of Lebesgue measure;
* `oneDim_prekopa_leindler` — the **one-dimensional Prékopa–Leindler
  inequality** for measurable `ℝ≥0∞`-valued functions: if
  `f(x)^(1-p) g(y)^p ≤ h((1-p)x + py)` for all `x y` then
  `(∫f)^(1-p) (∫g)^p ≤ ∫h`.

The proof of the last item is the classical level-set argument
(essential-sup normalization, the level-set inclusion
`{h > t} ⊇ (1-p)•{f > t} + p•{g > t}`, Brunn–Minkowski, layer-cake, and
weighted AM–GM), followed by a truncation limit to remove boundedness
assumptions.  References: A. Prékopa (1971, 1973), L. Leindler (1972);
presentation as in R. J. Gardner, "The Brunn–Minkowski inequality",
*Bull. AMS* **39** (2002), §4.  Mathlib contains no Brunn–Minkowski or
Prékopa–Leindler inequality; everything here is proved from scratch.
-/

namespace MatrixConcentration

open MeasureTheory Filter Set
open scoped ENNReal NNReal Pointwise

/-! ## One-dimensional Brunn–Minkowski for compact sets -/

/-- Lean implementation helper: **One-dimensional Brunn–Minkowski inequality** for nonempty compact
sets: `vol K₁ + vol K₂ ≤ vol (K₁ + K₂)`.  Proof: the translates
`sInf K₂ +ᵥ K₁` and `sSup K₁ +ᵥ K₂` are subsets of `K₁ + K₂` whose
intersection is at most the single point `sSup K₁ + sInf K₂`. -/
theorem oneDim_brunn_minkowski {K₁ K₂ : Set ℝ} (h₁ : IsCompact K₁)
    (h₂ : IsCompact K₂) (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty) :
    volume K₁ + volume K₂ ≤ volume (K₁ + K₂) := by
  set a := sSup K₁ with ha
  set b := sInf K₂ with hb
  have haK : a ∈ K₁ := h₁.sSup_mem hne₁
  have hbK : b ∈ K₂ := h₂.sInf_mem hne₂
  -- the two translated copies sit inside the sumset
  have hsub₁ : b +ᵥ K₁ ⊆ K₁ + K₂ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.mp hz
    have hmem : x + b ∈ K₁ + K₂ := Set.add_mem_add hx hbK
    simpa [vadd_eq_add, add_comm] using hmem
  have hsub₂ : a +ᵥ K₂ ⊆ K₁ + K₂ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hz
    simpa [vadd_eq_add] using Set.add_mem_add haK hy
  -- the copies overlap in at most one point
  have hinter : (b +ᵥ K₁) ∩ (a +ᵥ K₂) ⊆ {a + b} := by
    intro z hz
    obtain ⟨x, hx, hxz⟩ := Set.mem_vadd_set.mp hz.1
    obtain ⟨y, hy, hyz⟩ := Set.mem_vadd_set.mp hz.2
    have hxa : x ≤ a := le_csSup h₁.bddAbove hx
    have hby : b ≤ y := csInf_le h₂.bddBelow hy
    have hxz' : b + x = z := hxz
    have hyz' : a + y = z := hyz
    have hz' : z = a + b := by linarith
    simp [hz']
  -- measure bookkeeping
  have hm₂ : MeasurableSet (a +ᵥ K₂) := (h₂.vadd a).measurableSet
  have key := measure_union_add_inter (μ := volume) (b +ᵥ K₁) hm₂
  have hv₁ : volume (b +ᵥ K₁) = volume K₁ := measure_vadd volume b K₁
  have hv₂ : volume (a +ᵥ K₂) = volume K₂ := measure_vadd volume a K₂
  have hunion : volume ((b +ᵥ K₁) ∪ (a +ᵥ K₂)) ≤ volume (K₁ + K₂) :=
    measure_mono (union_subset hsub₁ hsub₂)
  have hint0 : volume ((b +ᵥ K₁) ∩ (a +ᵥ K₂)) = 0 :=
    le_antisymm ((measure_mono hinter).trans_eq (measure_singleton _))
      zero_le
  calc volume K₁ + volume K₂
      = volume (b +ᵥ K₁) + volume (a +ᵥ K₂) := by rw [hv₁, hv₂]
    _ = volume ((b +ᵥ K₁) ∪ (a +ᵥ K₂)) +
        volume ((b +ᵥ K₁) ∩ (a +ᵥ K₂)) := key.symm
    _ = volume ((b +ᵥ K₁) ∪ (a +ᵥ K₂)) := by rw [hint0, add_zero]
    _ ≤ volume (K₁ + K₂) := hunion

/-! ## Extension to measurable sets by inner regularity -/

/-- Lean implementation helper: One-dimensional Brunn–Minkowski for nonempty measurable sets, by
inner regularity of Lebesgue measure (approximation by compacts from
inside). -/
theorem oneDim_brunn_minkowski_measurable {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a₀, ha₀⟩ := hneA
  obtain ⟨b₀, hb₀⟩ := hneB
  -- translates of each set sit inside the sumset
  have hsubA : b₀ +ᵥ A ⊆ A + B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.mp hz
    have hmem : x + b₀ ∈ A + B := Set.add_mem_add hx hb₀
    simpa [vadd_eq_add, add_comm] using hmem
  have hsubB : a₀ +ᵥ B ⊆ A + B := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hz
    simpa [vadd_eq_add] using Set.add_mem_add ha₀ hy
  have hAle : volume A ≤ volume (A + B) := by
    rw [← measure_vadd volume b₀ A]; exact measure_mono hsubA
  have hBle : volume B ≤ volume (A + B) := by
    rw [← measure_vadd volume a₀ B]; exact measure_mono hsubB
  -- infinite-measure cases are immediate from the translate bound
  rcases eq_or_ne (volume A) ∞ with hAtop | hAtop
  · have htop : volume (A + B) = ∞ := top_le_iff.mp (hAtop ▸ hAle)
    simp [htop]
  rcases eq_or_ne (volume B) ∞ with hBtop | hBtop
  · have htop : volume (A + B) = ∞ := top_le_iff.mp (hBtop ▸ hBle)
    simp [htop]
  -- finite case: approximate from inside by nonempty compacts
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hhalf : ((ε : ℝ≥0∞) / 2) ≠ 0 := by
    rw [Ne, ENNReal.div_eq_zero_iff]
    push Not
    exact ⟨ENNReal.coe_ne_zero.mpr hε.ne', ENNReal.ofNat_ne_top⟩
  obtain ⟨K, hKA, hKc, hKm⟩ := hA.exists_isCompact_lt_add hAtop hhalf
  obtain ⟨L, hLB, hLc, hLm⟩ := hB.exists_isCompact_lt_add hBtop hhalf
  set K' := insert a₀ K with hK'
  set L' := insert b₀ L with hL'
  have hK'c : IsCompact K' := hKc.insert a₀
  have hL'c : IsCompact L' := hLc.insert b₀
  have hK'A : K' ⊆ A := insert_subset ha₀ hKA
  have hL'B : L' ⊆ B := insert_subset hb₀ hLB
  have hKm' : volume A < volume K' + ↑ε / 2 :=
    hKm.trans_le (add_le_add (measure_mono (subset_insert _ _)) le_rfl)
  have hLm' : volume B < volume L' + ↑ε / 2 :=
    hLm.trans_le (add_le_add (measure_mono (subset_insert _ _)) le_rfl)
  have hbm : volume K' + volume L' ≤ volume (K' + L') :=
    oneDim_brunn_minkowski hK'c hL'c (insert_nonempty _ _)
      (insert_nonempty _ _)
  have hsum : volume (K' + L') ≤ volume (A + B) :=
    measure_mono (Set.add_subset_add hK'A hL'B)
  have hchain : volume A + volume B <
      (volume K' + volume L') + (↑ε / 2 + ↑ε / 2) := by
    calc volume A + volume B
        < (volume K' + ↑ε / 2) + (volume L' + ↑ε / 2) :=
          ENNReal.add_lt_add hKm' hLm'
      _ = (volume K' + volume L') + (↑ε / 2 + ↑ε / 2) := by ring
  calc volume A + volume B
      ≤ (volume K' + volume L') + (↑ε / 2 + ↑ε / 2) := hchain.le
    _ = (volume K' + volume L') + ↑ε := by rw [ENNReal.add_halves]
    _ ≤ volume (A + B) + ↑ε := add_le_add (hbm.trans hsum) le_rfl

/-! ## Essential supremum helpers -/

/-- Lean implementation helper: Below the essential supremum, superlevel sets have positive
measure. -/
lemma meas_pos_of_lt_essSup {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : c < essSup f μ) :
    0 < μ {x | c < f x} := by
  by_contra hc
  have h0 : μ {x | c < f x} = 0 := by
    simpa [pos_iff_ne_zero, not_not] using hc
  have hae : f ≤ᵐ[μ] fun _ => c := by
    rw [Filter.EventuallyLE, ae_iff]
    simpa [not_le] using h0
  exact absurd (essSup_le_of_ae_le c hae) (not_le.mpr h)

/-- Lean implementation helper: If `∫⁻ f ≠ 0` then `essSup f ≠ 0`. -/
lemma essSup_ne_zero_of_lintegral_ne_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ 0) :
    essSup f μ ≠ 0 := by
  intro h0
  have hae : f =ᵐ[μ] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [ENNReal.ae_le_essSup (μ := μ) f] with x hx
    simpa [h0] using hx
  exact h (by rw [lintegral_congr_ae hae, lintegral_zero])

/-! ## Weighted AM–GM in `ℝ≥0∞` -/

/-- Lean implementation helper: Weighted arithmetic–geometric mean inequality in `ℝ≥0∞`:
`a^(1-p) b^p ≤ (1-p)·a + p·b` for `p ∈ (0, 1)`. -/
lemma ennreal_geom_mean_le_arith_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (a b : ℝ≥0∞) :
    a ^ (1 - p) * b ^ p ≤
      ENNReal.ofReal (1 - p) * a + ENNReal.ofReal p * b := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [ENNReal.zero_rpow_of_pos h1p, zero_mul]
    exact zero_le
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [ENNReal.zero_rpow_of_pos hp0, mul_zero]
    exact zero_le
  have hw1ne : ENNReal.ofReal (1 - p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact h1p
  have hw2ne : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hp0
  rcases eq_or_ne a ∞ with rfl | hatop
  · have htop : ENNReal.ofReal (1 - p) * ∞ = ∞ := ENNReal.mul_top hw1ne
    rw [htop, top_add]
    exact le_top
  rcases eq_or_ne b ∞ with rfl | hbtop
  · have htop : ENNReal.ofReal p * ∞ = ∞ := ENNReal.mul_top hw2ne
    rw [htop, add_top]
    exact le_top
  -- finite positive case: reduce to the `ℝ≥0` inequality
  obtain ⟨a', rfl⟩ : ∃ x : ℝ≥0, a = (x : ℝ≥0∞) :=
    ⟨a.toNNReal, (ENNReal.coe_toNNReal hatop).symm⟩
  obtain ⟨b', rfl⟩ : ∃ x : ℝ≥0, b = (x : ℝ≥0∞) :=
    ⟨b.toNNReal, (ENNReal.coe_toNNReal hbtop).symm⟩
  set w₁ : ℝ≥0 := Real.toNNReal (1 - p) with hw₁
  set w₂ : ℝ≥0 := Real.toNNReal p with hw₂
  have hw₁c : (w₁ : ℝ) = 1 - p := Real.coe_toNNReal _ h1p.le
  have hw₂c : (w₂ : ℝ) = p := Real.coe_toNNReal _ hp0.le
  have hsum : w₁ + w₂ = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_add, hw₁c, hw₂c, NNReal.coe_one]
    ring
  have key := NNReal.geom_mean_le_arith_mean2_weighted w₁ w₂ a' b' hsum
  have ha' : a' ≠ 0 := by simpa using ha0
  have hb' : b' ≠ 0 := by simpa using hb0
  calc (a' : ℝ≥0∞) ^ (1 - p) * (b' : ℝ≥0∞) ^ p
      = ((a' ^ ((w₁ : ℝ)) * b' ^ ((w₂ : ℝ)) : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, ← ENNReal.coe_rpow_of_ne_zero ha',
          ← ENNReal.coe_rpow_of_ne_zero hb', hw₁c, hw₂c]
    _ ≤ ((w₁ * a' + w₂ * b' : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr key
    _ = ENNReal.ofReal (1 - p) * ↑a' + ENNReal.ofReal p * ↑b' := by
        rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul]
        rfl

/-! ## Layer-cake bridge for functions bounded by one -/

/-- Lean implementation helper: The superlevel-volume function is antitone, hence measurable. -/
private lemma measurable_levelVol (φ : ℝ → ℝ≥0∞) :
    Measurable fun t : ℝ => volume {x | ENNReal.ofReal t < φ x} := by
  refine Antitone.measurable fun s t hst => ?_
  exact measure_mono fun x hx =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- Lean implementation helper: Layer-cake formula for a measurable function bounded by `1`: the
lintegral equals the integral of superlevel volumes over `(0, 1)`. -/
private lemma lintegral_eq_layer {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ)
    (hle : ∀ x, φ x ≤ 1) :
    ∫⁻ x, φ x =
      ∫⁻ t in Ioo (0 : ℝ) 1, volume {x | ENNReal.ofReal t < φ x} := by
  have hne : ∀ x, φ x ≠ ∞ := fun x => ((hle x).trans_lt ENNReal.one_lt_top).ne
  set F : ℝ → ℝ := fun x => (φ x).toReal with hF
  have hFnn : (0 : ℝ → ℝ) ≤ᵐ[volume] F :=
    Eventually.of_forall fun x => ENNReal.toReal_nonneg
  have hFm : AEMeasurable F volume :=
    (ENNReal.measurable_toReal.comp hφ).aemeasurable
  have h1 : ∫⁻ x, φ x = ∫⁻ x, ENNReal.ofReal (F x) := by
    refine lintegral_congr fun x => ?_
    rw [hF, ENNReal.ofReal_toReal (hne x)]
  have h2 := lintegral_eq_lintegral_meas_lt volume hFnn hFm
  -- identify the level sets on `(0, ∞)`
  have h3 : ∫⁻ t in Ioi (0 : ℝ), volume {a | t < F a} =
      ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < φ x} := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    congr 1
    ext a
    simp only [mem_setOf_eq, hF]
    rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hne a)]
  -- the part over `[1, ∞)` vanishes since `φ ≤ 1`
  have hsplit : Ioo (0 : ℝ) 1 ∪ Ici (1 : ℝ) = Ioi 0 :=
    Ioo_union_Ici_eq_Ioi zero_lt_one
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_lt.mpr ht')
  have hzero : ∫⁻ t in Ici (1 : ℝ),
      volume {x | ENNReal.ofReal t < φ x} = 0 := by
    have hempty : ∀ t ∈ Ici (1 : ℝ),
        volume {x | ENNReal.ofReal t < φ x} = 0 := by
      intro t ht
      have he : {x | ENNReal.ofReal t < φ x} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hle x).trans (ENNReal.one_le_ofReal.mpr ht)
      simp [he]
    rw [setLIntegral_congr_fun measurableSet_Ici hempty]
    simp
  rw [h1, h2, h3, ← hsplit, lintegral_union measurableSet_Ici hdisj,
    hzero, add_zero]

/-! ## Prékopa–Leindler: the normalized bounded case -/

section PLCore

variable {p : ℝ}

/-- Lean implementation helper: Core case of Prékopa–Leindler: essential suprema of `f` and `g`
finite and nonzero. -/
private lemma pl_core (hp0 : 0 < p) (hp1 : p < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hcond : ∀ x y : ℝ, f x ^ (1 - p) * g y ^ p ≤ h ((1 - p) * x + p * y))
    (hMf0 : essSup f volume ≠ 0) (hMftop : essSup f volume ≠ ∞)
    (hMg0 : essSup g volume ≠ 0) (hMgtop : essSup g volume ≠ ∞) :
    (∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p ≤ ∫⁻ z, h z := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  set Mf := essSup f volume with hMf
  set Mg := essSup g volume with hMg
  set ch : ℝ≥0∞ := (Mf ^ (1 - p) * Mg ^ p)⁻¹ with hch
  -- basic facts about the normalizing constants
  have hMfp0 : Mf ^ (1 - p) ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h' => absurd h' hMf0, fun h' => absurd h' hMftop⟩
  have hMfptop : Mf ^ (1 - p) ≠ ∞ := by
    rw [Ne, ENNReal.rpow_eq_top_iff]
    push Not
    exact ⟨fun h' => absurd h' hMf0, fun h' => absurd h' hMftop⟩
  have hMgp0 : Mg ^ p ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h' => absurd h' hMg0, fun h' => absurd h' hMgtop⟩
  have hMgptop : Mg ^ p ≠ ∞ := by
    rw [Ne, ENNReal.rpow_eq_top_iff]
    push Not
    exact ⟨fun h' => absurd h' hMg0, fun h' => absurd h' hMgtop⟩
  have hC0 : Mf ^ (1 - p) * Mg ^ p ≠ 0 := mul_ne_zero hMfp0 hMgp0
  have hCtop : Mf ^ (1 - p) * Mg ^ p ≠ ∞ := ENNReal.mul_ne_top hMfptop hMgptop
  have hch0 : ch ≠ 0 := ENNReal.inv_ne_zero.mpr hCtop
  have hchtop : ch ≠ ∞ := ENNReal.inv_ne_top.mpr hC0
  have hMfi0 : Mf⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMftop
  have hMfitop : Mf⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hMf0
  have hMgi0 : Mg⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMgtop
  have hMgitop : Mg⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hMg0
  -- the scaling identity for the normalizing constants
  have hscale : Mf⁻¹ ^ (1 - p) * Mg⁻¹ ^ p = ch := by
    rw [ENNReal.inv_rpow, ENNReal.inv_rpow, hch,
      ENNReal.mul_inv (Or.inl hMfp0) (Or.inl hMfptop)]
  -- normalized truncated functions
  set f₂ : ℝ → ℝ≥0∞ := fun x => min (f x * Mf⁻¹) 1 with hf₂
  set g₂ : ℝ → ℝ≥0∞ := fun y => min (g y * Mg⁻¹) 1 with hg₂
  set h₂ : ℝ → ℝ≥0∞ := fun z => min (h z * ch) 1 with hh₂
  have hf₂m : Measurable f₂ := (hf.mul_const _).min measurable_const
  have hg₂m : Measurable g₂ := (hg.mul_const _).min measurable_const
  have hh₂m : Measurable h₂ := (hh.mul_const _).min measurable_const
  have hf₂le : ∀ x, f₂ x ≤ 1 := fun x => min_le_right _ _
  have hg₂le : ∀ y, g₂ y ≤ 1 := fun y => min_le_right _ _
  have hh₂le : ∀ z, h₂ z ≤ 1 := fun z => min_le_right _ _
  -- the normalized condition
  have hcond₂ : ∀ x y : ℝ,
      f₂ x ^ (1 - p) * g₂ y ^ p ≤ h₂ ((1 - p) * x + p * y) := by
    intro x y
    have hle1 : f₂ x ^ (1 - p) * g₂ y ^ p ≤ 1 := by
      calc f₂ x ^ (1 - p) * g₂ y ^ p
          ≤ (1 : ℝ≥0∞) ^ (1 - p) * (1 : ℝ≥0∞) ^ p :=
            mul_le_mul' (ENNReal.rpow_le_rpow (hf₂le x) h1p.le)
              (ENNReal.rpow_le_rpow (hg₂le y) hp0.le)
        _ = 1 := by rw [ENNReal.one_rpow, ENNReal.one_rpow, mul_one]
    have hle2 : f₂ x ^ (1 - p) * g₂ y ^ p ≤
        h ((1 - p) * x + p * y) * ch := by
      calc f₂ x ^ (1 - p) * g₂ y ^ p
          ≤ (f x * Mf⁻¹) ^ (1 - p) * (g y * Mg⁻¹) ^ p :=
            mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) h1p.le)
              (ENNReal.rpow_le_rpow (min_le_left _ _) hp0.le)
        _ = (f x ^ (1 - p) * g y ^ p) * (Mf⁻¹ ^ (1 - p) * Mg⁻¹ ^ p) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ h1p.le,
              ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
            ring
        _ = (f x ^ (1 - p) * g y ^ p) * ch := by rw [hscale]
        _ ≤ h ((1 - p) * x + p * y) * ch :=
            mul_le_mul_right' (hcond x y) _
    exact le_min hle2 hle1
  -- transferring strict level inequalities through the normalization
  have hiff_f : ∀ (u : ℝ≥0∞) (x : ℝ),
      u < f x * Mf⁻¹ ↔ u * Mf < f x := by
    intro u x
    constructor
    · intro h'
      have h'' := ENNReal.mul_lt_mul_right (a := Mf) hMf0 hMftop h'
      rw [show Mf * (f x * Mf⁻¹) = f x * (Mf⁻¹ * Mf) by ring,
        ENNReal.inv_mul_cancel hMf0 hMftop, mul_one] at h''
      rwa [mul_comm] at h''
    · intro h'
      have h'' := ENNReal.mul_lt_mul_right (a := Mf⁻¹) hMfi0 hMfitop h'
      rw [show Mf⁻¹ * (u * Mf) = u * (Mf⁻¹ * Mf) by ring,
        ENNReal.inv_mul_cancel hMf0 hMftop, mul_one, mul_comm] at h''
      exact h''
  have hiff_g : ∀ (u : ℝ≥0∞) (y : ℝ),
      u < g y * Mg⁻¹ ↔ u * Mg < g y := by
    intro u y
    constructor
    · intro h'
      have h'' := ENNReal.mul_lt_mul_right (a := Mg) hMg0 hMgtop h'
      rw [show Mg * (g y * Mg⁻¹) = g y * (Mg⁻¹ * Mg) by ring,
        ENNReal.inv_mul_cancel hMg0 hMgtop, mul_one] at h''
      rwa [mul_comm] at h''
    · intro h'
      have h'' := ENNReal.mul_lt_mul_right (a := Mg⁻¹) hMgi0 hMgitop h'
      rw [show Mg⁻¹ * (u * Mg) = u * (Mg⁻¹ * Mg) by ring,
        ENNReal.inv_mul_cancel hMg0 hMgtop, mul_one, mul_comm] at h''
      exact h''
  -- positivity of the level sets for levels in (0, 1)
  have hposA : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < volume {x | ENNReal.ofReal t < f₂ x} := by
    intro t ht
    have ht1 : ENNReal.ofReal t < 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1.le |>.mpr ht.2
    have hset : {x | ENNReal.ofReal t < f₂ x} =
        {x | ENNReal.ofReal t * Mf < f x} := by
      ext x
      simp only [hf₂, mem_setOf_eq, lt_min_iff]
      constructor
      · exact fun hx => (hiff_f _ x).mp hx.1
      · exact fun hx => ⟨(hiff_f _ x).mpr hx, ht1⟩
    rw [hset]
    refine meas_pos_of_lt_essSup ?_
    have hlt : Mf * ENNReal.ofReal t < Mf * 1 :=
      ENNReal.mul_lt_mul_right hMf0 hMftop ht1
    rw [mul_one, mul_comm] at hlt
    exact hlt
  have hposB : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < volume {y | ENNReal.ofReal t < g₂ y} := by
    intro t ht
    have ht1 : ENNReal.ofReal t < 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1.le |>.mpr ht.2
    have hset : {y | ENNReal.ofReal t < g₂ y} =
        {y | ENNReal.ofReal t * Mg < g y} := by
      ext y
      simp only [hg₂, mem_setOf_eq, lt_min_iff]
      constructor
      · exact fun hy => (hiff_g _ y).mp hy.1
      · exact fun hy => ⟨(hiff_g _ y).mpr hy, ht1⟩
    rw [hset]
    refine meas_pos_of_lt_essSup ?_
    have hlt : Mg * ENNReal.ofReal t < Mg * 1 :=
      ENNReal.mul_lt_mul_right hMg0 hMgtop ht1
    rw [mul_one, mul_comm] at hlt
    exact hlt
  -- the level-set inclusion
  have hInc : ∀ t ∈ Ioo (0 : ℝ) 1,
      (1 - p) • {x | ENNReal.ofReal t < f₂ x} +
        p • {y | ENNReal.ofReal t < g₂ y} ⊆
        {z | ENNReal.ofReal t < h₂ z} := by
    intro t ht z hz
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hz
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hu
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hv
    have hx' : ENNReal.ofReal t < f₂ x := hx
    have hy' : ENNReal.ofReal t < g₂ y := hy
    have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht.1).ne'
    have hsplit : ENNReal.ofReal t =
        ENNReal.ofReal t ^ (1 - p) * ENNReal.ofReal t ^ p := by
      rw [← ENNReal.rpow_add _ _ ht0 ENNReal.ofReal_ne_top]
      norm_num
    have hlt : ENNReal.ofReal t < f₂ x ^ (1 - p) * g₂ y ^ p := by
      rw [hsplit]
      exact ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx' h1p)
        (ENNReal.rpow_lt_rpow hy' hp0)
    have hz' : (1 - p) • x + p • y = z := huv
    have := hlt.trans_le (hcond₂ x y)
    simpa [mem_setOf_eq, ← hz', smul_eq_mul] using this
  -- Brunn–Minkowski on the level sets
  have hBM : ∀ t ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - p) * volume {x | ENNReal.ofReal t < f₂ x} +
        ENNReal.ofReal p * volume {y | ENNReal.ofReal t < g₂ y} ≤
        volume {z | ENNReal.ofReal t < h₂ z} := by
    intro t ht
    set A := {x | ENNReal.ofReal t < f₂ x} with hA
    set B := {y | ENNReal.ofReal t < g₂ y} with hB
    have hAm : MeasurableSet A := measurableSet_lt measurable_const hf₂m
    have hBm : MeasurableSet B := measurableSet_lt measurable_const hg₂m
    have hAne : A.Nonempty := nonempty_of_measure_ne_zero (hposA t ht).ne'
    have hBne : B.Nonempty := nonempty_of_measure_ne_zero (hposB t ht).ne'
    have hsA : volume ((1 - p) • A) = ENNReal.ofReal (1 - p) * volume A := by
      rw [Measure.addHaar_smul_of_nonneg volume h1p.le A,
        Module.finrank_self, pow_one]
    have hsB : volume (p • B) = ENNReal.ofReal p * volume B := by
      rw [Measure.addHaar_smul_of_nonneg volume hp0.le B,
        Module.finrank_self, pow_one]
    calc ENNReal.ofReal (1 - p) * volume A + ENNReal.ofReal p * volume B
        = volume ((1 - p) • A) + volume (p • B) := by rw [hsA, hsB]
      _ ≤ volume ((1 - p) • A + p • B) :=
          oneDim_brunn_minkowski_measurable
            (hAm.const_smul₀ (1 - p)) (hBm.const_smul₀ p)
            (hAne.smul_set) (hBne.smul_set)
      _ ≤ volume {z | ENNReal.ofReal t < h₂ z} :=
          measure_mono (hInc t ht)
  -- layer-cake representation of the three integrals
  have hlayF : ∫⁻ x, f₂ x =
      ∫⁻ t in Ioo (0 : ℝ) 1, volume {x | ENNReal.ofReal t < f₂ x} :=
    lintegral_eq_layer hf₂m hf₂le
  have hlayG : ∫⁻ y, g₂ y =
      ∫⁻ t in Ioo (0 : ℝ) 1, volume {y | ENNReal.ofReal t < g₂ y} :=
    lintegral_eq_layer hg₂m hg₂le
  have hlayH : ∫⁻ z, h₂ z =
      ∫⁻ t in Ioo (0 : ℝ) 1, volume {z | ENNReal.ofReal t < h₂ z} :=
    lintegral_eq_layer hh₂m hh₂le
  -- the key inequality for the normalized functions
  have hkey : ENNReal.ofReal (1 - p) * (∫⁻ x, f₂ x) +
      ENNReal.ofReal p * (∫⁻ y, g₂ y) ≤ ∫⁻ z, h₂ z := by
    rw [hlayF, hlayG, hlayH,
      ← lintegral_const_mul _ (measurable_levelVol f₂),
      ← lintegral_const_mul _ (measurable_levelVol g₂),
      ← lintegral_add_left (((measurable_levelVol f₂).const_mul _))]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hBM t ht
  have hgm : (∫⁻ x, f₂ x) ^ (1 - p) * (∫⁻ y, g₂ y) ^ p ≤ ∫⁻ z, h₂ z :=
    (ennreal_geom_mean_le_arith_mean hp0 hp1 _ _).trans hkey
  -- identify the normalized integrals
  have hf₂int : ∫⁻ x, f₂ x = (∫⁻ x, f x) * Mf⁻¹ := by
    have hae : f₂ =ᵐ[volume] fun x => f x * Mf⁻¹ := by
      filter_upwards [ENNReal.ae_le_essSup (μ := volume) f] with x hx
      have hle : f x * Mf⁻¹ ≤ 1 := by
        calc f x * Mf⁻¹ ≤ Mf * Mf⁻¹ := mul_le_mul_right' hx _
          _ = 1 := ENNReal.mul_inv_cancel hMf0 hMftop
      simp [hf₂, min_eq_left hle]
    rw [lintegral_congr_ae hae, lintegral_mul_const' _ _ hMfitop]
  have hg₂int : ∫⁻ y, g₂ y = (∫⁻ y, g y) * Mg⁻¹ := by
    have hae : g₂ =ᵐ[volume] fun y => g y * Mg⁻¹ := by
      filter_upwards [ENNReal.ae_le_essSup (μ := volume) g] with y hy
      have hle : g y * Mg⁻¹ ≤ 1 := by
        calc g y * Mg⁻¹ ≤ Mg * Mg⁻¹ := mul_le_mul_right' hy _
          _ = 1 := ENNReal.mul_inv_cancel hMg0 hMgtop
      simp [hg₂, min_eq_left hle]
    rw [lintegral_congr_ae hae, lintegral_mul_const' _ _ hMgitop]
  have hh₂int : ∫⁻ z, h₂ z ≤ (∫⁻ z, h z) * ch := by
    calc ∫⁻ z, h₂ z ≤ ∫⁻ z, h z * ch :=
        lintegral_mono fun z => min_le_left _ _
      _ = (∫⁻ z, h z) * ch := lintegral_mul_const' _ _ hchtop
  -- unscale
  have hfinal : ((∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p) * ch ≤
      (∫⁻ z, h z) * ch := by
    calc ((∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p) * ch
        = ((∫⁻ x, f x) * Mf⁻¹) ^ (1 - p) * ((∫⁻ y, g y) * Mg⁻¹) ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ h1p.le,
            ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← hscale]
          ring
      _ = (∫⁻ x, f₂ x) ^ (1 - p) * (∫⁻ y, g₂ y) ^ p := by
          rw [hf₂int, hg₂int]
      _ ≤ ∫⁻ z, h₂ z := hgm
      _ ≤ (∫⁻ z, h z) * ch := hh₂int
  -- cancel the (finite, nonzero) constant `ch`
  calc (∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p
      = ((∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p * ch) * ch⁻¹ := by
        rw [mul_assoc ((∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p) ch ch⁻¹,
          ENNReal.mul_inv_cancel hch0 hchtop, mul_one]
    _ ≤ ((∫⁻ z, h z) * ch) * ch⁻¹ := mul_le_mul_right' hfinal ch⁻¹
    _ = ∫⁻ z, h z := by
        rw [mul_assoc (∫⁻ z, h z) ch ch⁻¹,
          ENNReal.mul_inv_cancel hch0 hchtop, mul_one]

/-- Lean implementation helper: Prékopa–Leindler with nonvanishing integrals: obtained from the core
case by truncation `f ↦ min f N` and monotone convergence. -/
private lemma pl_pos (hp0 : 0 < p) (hp1 : p < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hcond : ∀ x y : ℝ, f x ^ (1 - p) * g y ^ p ≤ h ((1 - p) * x + p * y))
    (hf0 : ∫⁻ x, f x ≠ 0) (hg0 : ∫⁻ y, g y ≠ 0) :
    (∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p ≤ ∫⁻ z, h z := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  set fN : ℕ → ℝ → ℝ≥0∞ := fun N x => min (f x) (N : ℝ≥0∞) with hfN
  set gN : ℕ → ℝ → ℝ≥0∞ := fun N y => min (g y) (N : ℝ≥0∞) with hgN
  have hfNm : ∀ N, Measurable (fN N) := fun N => hf.min measurable_const
  have hgNm : ∀ N, Measurable (gN N) := fun N => hg.min measurable_const
  -- the truncations satisfy the hypothesis
  have hcondN : ∀ N, ∀ x y : ℝ,
      fN N x ^ (1 - p) * gN N y ^ p ≤ h ((1 - p) * x + p * y) := by
    intro N x y
    refine le_trans ?_ (hcond x y)
    exact mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) h1p.le)
      (ENNReal.rpow_le_rpow (min_le_left _ _) hp0.le)
  -- essential suprema of the truncations are finite …
  have hesstopF : ∀ N : ℕ, essSup (fN N) volume ≠ ∞ := by
    intro N
    have hle : essSup (fN N) volume ≤ (N : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Eventually.of_forall fun x => min_le_right _ _)
    exact (hle.trans_lt (ENNReal.natCast_lt_top N)).ne
  have hesstopG : ∀ N : ℕ, essSup (gN N) volume ≠ ∞ := by
    intro N
    have hle : essSup (gN N) volume ≤ (N : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Eventually.of_forall fun y => min_le_right _ _)
    exact (hle.trans_lt (ENNReal.natCast_lt_top N)).ne
  -- … and nonzero once `N ≥ 1`
  have hess0F : ∀ N : ℕ, 1 ≤ N → essSup (fN N) volume ≠ 0 := by
    intro N hN h0
    have hae : fN N =ᵐ[volume] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [ENNReal.ae_le_essSup (μ := volume) (fN N)] with x hx
      simpa [h0] using hx
    have haef : f =ᵐ[volume] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [hae] with x hx
      rcases min_choice (f x) ((N : ℝ≥0∞)) with hc | hc
    -- `min (f x) N = 0`; since `N ≠ 0` the minimum is `f x`
      · exact hc ▸ hx
      · exfalso
        have hNz : ((N : ℝ≥0∞)) = 0 := hc ▸ hx
        have : (N : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
        exact this hNz
    exact hf0 (by rw [lintegral_congr_ae haef, lintegral_zero])
  have hess0G : ∀ N : ℕ, 1 ≤ N → essSup (gN N) volume ≠ 0 := by
    intro N hN h0
    have hae : gN N =ᵐ[volume] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [ENNReal.ae_le_essSup (μ := volume) (gN N)] with y hy
      simpa [h0] using hy
    have haeg : g =ᵐ[volume] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [hae] with y hy
      rcases min_choice (g y) ((N : ℝ≥0∞)) with hc | hc
      · exact hc ▸ hy
      · exfalso
        have hNz : ((N : ℝ≥0∞)) = 0 := hc ▸ hy
        have : (N : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
        exact this hNz
    exact hg0 (by rw [lintegral_congr_ae haeg, lintegral_zero])
  -- the core case applies for each `N ≥ 1`
  have hcore : ∀ N : ℕ, 1 ≤ N →
      (∫⁻ x, fN N x) ^ (1 - p) * (∫⁻ y, gN N y) ^ p ≤ ∫⁻ z, h z := by
    intro N hN
    exact pl_core hp0 hp1 (hfNm N) (hgNm N) hh (hcondN N)
      (hess0F N hN) (hesstopF N) (hess0G N hN) (hesstopG N)
  -- monotone convergence of the truncated integrals
  have hmonoF : Monotone fun N : ℕ => fN N := by
    intro N M hNM x
    exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hNM)
  have hmonoG : Monotone fun N : ℕ => gN N := by
    intro N M hNM y
    exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hNM)
  have hsupF : ∀ x, ⨆ N : ℕ, fN N x = f x := by
    intro x
    rw [hfN]
    simp only
    rw [← inf_iSup_eq]
    simp [ENNReal.iSup_natCast]
  have hsupG : ∀ y, ⨆ N : ℕ, gN N y = g y := by
    intro y
    rw [hgN]
    simp only
    rw [← inf_iSup_eq]
    simp [ENNReal.iSup_natCast]
  have hintF : ⨆ N : ℕ, ∫⁻ x, fN N x = ∫⁻ x, f x := by
    rw [← lintegral_iSup hfNm hmonoF]
    exact lintegral_congr hsupF
  have hintG : ⨆ N : ℕ, ∫⁻ y, gN N y = ∫⁻ y, g y := by
    rw [← lintegral_iSup hgNm hmonoG]
    exact lintegral_congr hsupG
  have hmonoIF : Monotone fun N : ℕ => ∫⁻ x, fN N x :=
    fun N M hNM => lintegral_mono fun x => hmonoF hNM x
  have hmonoIG : Monotone fun N : ℕ => ∫⁻ y, gN N y :=
    fun N M hNM => lintegral_mono fun y => hmonoG hNM y
  have htendF : Tendsto (fun N : ℕ => ∫⁻ x, fN N x) atTop
      (nhds (∫⁻ x, f x)) := hintF ▸ tendsto_atTop_iSup hmonoIF
  have htendG : Tendsto (fun N : ℕ => ∫⁻ y, gN N y) atTop
      (nhds (∫⁻ y, g y)) := hintG ▸ tendsto_atTop_iSup hmonoIG
  -- pass to the limit in the product
  have hrf : (∫⁻ x, f x) ^ (1 - p) ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h' => absurd h' hf0, fun _ => h1p.le⟩
  have hrg : (∫⁻ y, g y) ^ p ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h' => absurd h' hg0, fun _ => hp0.le⟩
  have htendRF : Tendsto (fun N : ℕ => (∫⁻ x, fN N x) ^ (1 - p)) atTop
      (nhds ((∫⁻ x, f x) ^ (1 - p))) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp htendF
  have htendRG : Tendsto (fun N : ℕ => (∫⁻ y, gN N y) ^ p) atTop
      (nhds ((∫⁻ y, g y) ^ p)) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp htendG
  have htendMul : Tendsto
      (fun N : ℕ => (∫⁻ x, fN N x) ^ (1 - p) * (∫⁻ y, gN N y) ^ p) atTop
      (nhds ((∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p)) :=
    ENNReal.Tendsto.mul htendRF (Or.inl hrf) htendRG (Or.inl hrg)
  refine le_of_tendsto htendMul ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact hcore N hN

end PLCore

/-- Lean implementation helper: **One-dimensional Prékopa–Leindler inequality** (measurable `ℝ≥0∞`
form): if `p ∈ (0,1)` and `f(x)^(1-p) · g(y)^p ≤ h((1-p)·x + p·y)` for
all real `x, y`, then `(∫⁻f)^(1-p) · (∫⁻g)^p ≤ ∫⁻h` with respect to
Lebesgue measure. -/
theorem oneDim_prekopa_leindler {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hcond : ∀ x y : ℝ, f x ^ (1 - p) * g y ^ p ≤ h ((1 - p) * x + p * y)) :
    (∫⁻ x, f x) ^ (1 - p) * (∫⁻ y, g y) ^ p ≤ ∫⁻ z, h z := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  rcases eq_or_ne (∫⁻ x, f x) 0 with hf0 | hf0
  · rw [hf0, ENNReal.zero_rpow_of_pos h1p, zero_mul]
    exact zero_le
  rcases eq_or_ne (∫⁻ y, g y) 0 with hg0 | hg0
  · rw [hg0, ENNReal.zero_rpow_of_pos hp0, mul_zero]
    exact zero_le
  exact pl_pos hp0 hp1 hf hg hh hcond hf0 hg0

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.5: The Gaussian Prékopa–Leindler inequality

This section transports the one-dimensional Prékopa–Leindler inequality to the
standard Gaussian product measure on `ι → ℝ`, in the *Gaussian-adapted*
form (`GaussPL`): for `p ∈ (0,1)` and measurable `F G H : (ι → ℝ) → ℝ≥0∞`
with

`F(x)^(1-p) G(y)^p exp(−p(1-p)|x−y|²/2) ≤ H((1-p)x + py)`,

one has `(∫F dγ)^(1-p) (∫G dγ)^p ≤ ∫H dγ` for the standard Gaussian
product measure `γ`.  The Gaussian-adapted form is chosen because it
**tensorizes**: the quadratic transport cost `|x−y|²` is additive over
coordinates, so the product step is pure Fubini plus the one-dimensional
case, with no dimension-dependent constants.

Contents: `GaussPL` (the predicate, for a measure with an abstract convex
combination and cost), `gaussPL_real` (the 1-D case, by substituting the
Gaussian density into `oneDim_prekopa_leindler` — the exponent identity
`(1-p)x²/2 + py²/2 − ((1-p)x+py)²/2 = p(1-p)(x−y)²/2` is exactly the
Gaussian cost), `GaussPL.prod` (tensorization), `gaussPL_pi_fin`
(induction on `Fin n`), and `gaussPL_pi` (any finite index type, via
`measurePreserving_piCongrLeft`).

Reference for the method: B. Maurey, "Some deviation inequalities",
*GAFA* **1** (1991) (property (τ)); S. G. Bobkov, M. Ledoux, "From
Brunn–Minkowski to Brascamp–Lieb and to logarithmic Sobolev
inequalities", *GAFA* **10** (2000), §2.
-/

namespace MatrixConcentration

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The Gaussian Prékopa–Leindler predicate -/

/-- Lean implementation helper: The Gaussian-adapted Prékopa–Leindler property of a measure `μ`, with
convex-combination map `comb` and quadratic transport cost `cost`. -/
def GaussPL {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (comb : ℝ → α → α → α) (cost : α → α → ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
    ∀ F G H : α → ℝ≥0∞, Measurable F → Measurable G → Measurable H →
      (∀ x y : α, F x ^ (1 - p) * G y ^ p *
          ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * cost x y)) ≤
        H (comb p x y)) →
      (∫⁻ x, F x ∂μ) ^ (1 - p) * (∫⁻ y, G y ∂μ) ^ p ≤ ∫⁻ z, H z ∂μ

/-! ## Cancellation helpers -/

/-- Lean implementation helper: cancel a finite nonzero ENNReal factor on the right. -/
lemma le_mul_inv_of_mul_le {D X Y : ℝ≥0∞} (hD0 : D ≠ 0)
    (hDtop : D ≠ ∞) (h : X * D ≤ Y) : X ≤ Y * D⁻¹ := by
  calc X = (X * D) * D⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hD0 hDtop, mul_one]
    _ ≤ Y * D⁻¹ := mul_le_mul_right' h D⁻¹

/-- Lean implementation helper: restore a finite nonzero ENNReal factor on the right. -/
lemma mul_le_of_le_mul_inv {D X Y : ℝ≥0∞} (hD0 : D ≠ 0)
    (hDtop : D ≠ ∞) (h : X ≤ Y * D⁻¹) : X * D ≤ Y := by
  calc X * D ≤ (Y * D⁻¹) * D := mul_le_mul_right' h D
    _ = Y := by rw [mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, mul_one]

/-! ## The one-dimensional case -/

/-- Lean implementation helper: The Gaussian exponent identity: the standard normal density satisfies
`ρ(x)^(1-p) ρ(y)^p = ρ((1-p)x + py) · exp(−p(1-p)(x−y)²/2)`. -/
private lemma gaussianPDFReal_combo {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (x y : ℝ) :
    gaussianPDFReal 0 1 x ^ (1 - p) * gaussianPDFReal 0 1 y ^ p =
      gaussianPDFReal 0 1 ((1 - p) * x + p * y) *
        Real.exp (-(p * (1 - p) / 2) * (x - y) ^ 2) := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  have hc : (0 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  rw [Real.mul_rpow hc.le (Real.exp_nonneg _),
    Real.mul_rpow hc.le (Real.exp_nonneg _), ← Real.exp_log hc]
  simp only [← Real.exp_mul, ← Real.exp_add]
  rw [Real.exp_eq_exp]
  ring

/-- Lean implementation helper: **Gaussian Prékopa–Leindler in one dimension**, for the standard
Gaussian measure on `ℝ`. -/
theorem gaussPL_real :
    GaussPL (gaussianReal 0 1) (fun p x y => (1 - p) * x + p * y)
      (fun x y => (x - y) ^ 2) := by
  intro p hp0 hp1 F G H hF hG hH hcond
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hγ : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  have hpdf_eq : ∀ t : ℝ,
      gaussianPDF 0 1 t = ENNReal.ofReal (gaussianPDFReal 0 1 t) :=
    fun _ => rfl
  have hpdf_pos : ∀ t : ℝ, 0 < gaussianPDFReal 0 1 t :=
    fun t => gaussianPDFReal_pos 0 1 t one_ne_zero
  have hfm : Measurable fun x => F x * gaussianPDF 0 1 x :=
    hF.mul (measurable_gaussianPDF 0 1)
  have hgm : Measurable fun y => G y * gaussianPDF 0 1 y :=
    hG.mul (measurable_gaussianPDF 0 1)
  have hhm : Measurable fun z => H z * gaussianPDF 0 1 z :=
    hH.mul (measurable_gaussianPDF 0 1)
  -- the density-weighted functions satisfy the Lebesgue PL hypothesis
  have hcondPL : ∀ x y : ℝ,
      (F x * gaussianPDF 0 1 x) ^ (1 - p) *
        (G y * gaussianPDF 0 1 y) ^ p ≤
      H ((1 - p) * x + p * y) * gaussianPDF 0 1 ((1 - p) * x + p * y) := by
    intro x y
    calc (F x * gaussianPDF 0 1 x) ^ (1 - p) *
          (G y * gaussianPDF 0 1 y) ^ p
        = (F x ^ (1 - p) * G y ^ p) *
            (gaussianPDF 0 1 x ^ (1 - p) * gaussianPDF 0 1 y ^ p) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ h1p.le,
            ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          ring
      _ = (F x ^ (1 - p) * G y ^ p *
            ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * (x - y) ^ 2))) *
            gaussianPDF 0 1 ((1 - p) * x + p * y) := by
          rw [hpdf_eq x, hpdf_eq y,
            ENNReal.ofReal_rpow_of_pos (hpdf_pos x),
            ENNReal.ofReal_rpow_of_pos (hpdf_pos y),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpdf_pos x).le _),
            gaussianPDFReal_combo hp0 hp1 x y,
            ENNReal.ofReal_mul (hpdf_pos _).le,
            ← hpdf_eq ((1 - p) * x + p * y)]
          ring
      _ ≤ H ((1 - p) * x + p * y) *
            gaussianPDF 0 1 ((1 - p) * x + p * y) :=
          mul_le_mul_right' (hcond x y) _
  -- convert Gaussian integrals to Lebesgue integrals of weighted functions
  have hIF : ∫⁻ x, F x ∂(gaussianReal 0 1) =
      ∫⁻ x, F x * gaussianPDF 0 1 x := by
    rw [hγ, lintegral_withDensity_eq_lintegral_mul volume
      (measurable_gaussianPDF 0 1) hF]
    exact lintegral_congr fun x => mul_comm _ _
  have hIG : ∫⁻ y, G y ∂(gaussianReal 0 1) =
      ∫⁻ y, G y * gaussianPDF 0 1 y := by
    rw [hγ, lintegral_withDensity_eq_lintegral_mul volume
      (measurable_gaussianPDF 0 1) hG]
    exact lintegral_congr fun y => mul_comm _ _
  have hIH : ∫⁻ z, H z ∂(gaussianReal 0 1) =
      ∫⁻ z, H z * gaussianPDF 0 1 z := by
    rw [hγ, lintegral_withDensity_eq_lintegral_mul volume
      (measurable_gaussianPDF 0 1) hH]
    exact lintegral_congr fun z => mul_comm _ _
  rw [hIF, hIG, hIH]
  exact oneDim_prekopa_leindler hp0 hp1 hfm hgm hhm hcondPL

/-! ## Transfer along a measure-preserving equivalence -/

/-- Lean implementation helper: `GaussPL` transfers along a measure-preserving measurable equivalence
that intertwines the combination maps and the costs. -/
lemma GaussPL.transfer {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {comb : ℝ → α → α → α} {cost : α → α → ℝ}
    {comb' : ℝ → β → β → β} {cost' : β → β → ℝ}
    (hPL : GaussPL μ comb cost) (e : β ≃ᵐ α) (he : MeasurePreserving e ν μ)
    (hcomb : ∀ (p : ℝ) (x y : β), e (comb' p x y) = comb p (e x) (e y))
    (hcost : ∀ x y : β, cost (e x) (e y) = cost' x y) :
    GaussPL ν comb' cost' := by
  intro p hp0 hp1 F G H hF hG hH hcond
  have hcond' : ∀ u v : α,
      (fun u => F (e.symm u)) u ^ (1 - p) * (fun v => G (e.symm v)) v ^ p *
        ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * cost u v)) ≤
      (fun w => H (e.symm w)) (comb p u v) := by
    intro u v
    simp only
    have h1 : cost u v = cost' (e.symm u) (e.symm v) := by
      conv_lhs => rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
      exact hcost _ _
    have h2 : e.symm (comb p u v) = comb' p (e.symm u) (e.symm v) := by
      have h3 := hcomb p (e.symm u) (e.symm v)
      rw [e.apply_symm_apply, e.apply_symm_apply] at h3
      rw [← h3, e.symm_apply_apply]
    rw [h1, h2]
    exact hcond (e.symm u) (e.symm v)
  have hout := hPL p hp0 hp1 (fun u => F (e.symm u)) (fun v => G (e.symm v))
    (fun w => H (e.symm w)) (hF.comp e.symm.measurable)
    (hG.comp e.symm.measurable) (hH.comp e.symm.measurable) hcond'
  have hes : MeasurePreserving (⇑e.symm) μ ν := he.symm e
  rw [hes.lintegral_comp hF, hes.lintegral_comp hG,
    hes.lintegral_comp hH] at hout
  exact hout

/-! ## Tensorization -/

/-- Lean implementation helper: **Tensorization of Gaussian Prékopa–Leindler**: the product of two
measures with the `GaussPL` property has it, with combination acting
componentwise and costs adding. -/
lemma GaussPL.prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {c₁ : ℝ → α → α → α} {k₁ : α → α → ℝ}
    {c₂ : ℝ → β → β → β} {k₂ : β → β → ℝ}
    (h₁ : GaussPL μ c₁ k₁) (h₂ : GaussPL ν c₂ k₂) :
    GaussPL (μ.prod ν)
      (fun p u v => (c₁ p u.1 v.1, c₂ p u.2 v.2))
      (fun u v => k₁ u.1 v.1 + k₂ u.2 v.2) := by
  intro p hp0 hp1 F G H hF hG hH hcond
  -- the partially integrated functions satisfy the `α`-level hypothesis
  have hmid : ∀ a₁ a₂ : α,
      (fun a => ∫⁻ b, F (a, b) ∂ν) a₁ ^ (1 - p) *
        (fun a => ∫⁻ b, G (a, b) ∂ν) a₂ ^ p *
        ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * k₁ a₁ a₂)) ≤
      (fun a => ∫⁻ b, H (a, b) ∂ν) (c₁ p a₁ a₂) := by
    intro a₁ a₂
    simp only
    set D : ℝ≥0∞ :=
      ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * k₁ a₁ a₂)) with hD
    have hD0 : D ≠ 0 := by
      rw [hD, Ne, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _
    have hDtop : D ≠ ∞ := ENNReal.ofReal_ne_top
    -- inner application of `GaussPL ν`
    have hinner := h₂ p hp0 hp1 (fun b => F (a₁, b)) (fun b => G (a₂, b))
      (fun b => H (c₁ p a₁ a₂, b) * D⁻¹)
      (hF.comp measurable_prodMk_left) (hG.comp measurable_prodMk_left)
      ((hH.comp measurable_prodMk_left).mul_const D⁻¹) ?_
    · -- deduce the middle inequality
      have hHint : ∫⁻ b, H (c₁ p a₁ a₂, b) * D⁻¹ ∂ν =
          (∫⁻ b, H (c₁ p a₁ a₂, b) ∂ν) * D⁻¹ :=
        lintegral_mul_const' D⁻¹ _ (ENNReal.inv_ne_top.mpr hD0)
      rw [hHint] at hinner
      exact mul_le_of_le_mul_inv hD0 hDtop hinner
    · -- the inner hypothesis, from the product hypothesis
      intro b₁ b₂
      have hsplit : ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) *
          (k₁ a₁ a₂ + k₂ b₁ b₂))) =
          D * ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * k₂ b₁ b₂)) := by
        rw [hD, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring
      have h0 := hcond (a₁, b₁) (a₂, b₂)
      simp only at h0
      rw [hsplit] at h0
      have h0' : (F (a₁, b₁) ^ (1 - p) * G (a₂, b₂) ^ p *
          ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * k₂ b₁ b₂))) * D ≤
          H (c₁ p a₁ a₂, c₂ p b₁ b₂) := by
        calc (F (a₁, b₁) ^ (1 - p) * G (a₂, b₂) ^ p *
            ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) * k₂ b₁ b₂))) * D
            = F (a₁, b₁) ^ (1 - p) * G (a₂, b₂) ^ p *
              (D * ENNReal.ofReal
                (Real.exp (-(p * (1 - p) / 2) * k₂ b₁ b₂))) := by ring
          _ ≤ H (c₁ p a₁ a₂, c₂ p b₁ b₂) := h0
      exact le_mul_inv_of_mul_le hD0 hDtop h0'
  -- outer application of `GaussPL μ`, then Fubini
  have hout := h₁ p hp0 hp1 (fun a => ∫⁻ b, F (a, b) ∂ν)
    (fun a => ∫⁻ b, G (a, b) ∂ν) (fun a => ∫⁻ b, H (a, b) ∂ν)
    hF.lintegral_prod_right' hG.lintegral_prod_right'
    hH.lintegral_prod_right' hmid
  rw [lintegral_prod F hF.aemeasurable, lintegral_prod G hG.aemeasurable,
    lintegral_prod H hH.aemeasurable]
  exact hout

/-! ## The standard Gaussian product measure and the induction -/

/-- Lean implementation helper: Gaussian Prékopa–Leindler on `Fin n → ℝ` with the product standard
Gaussian measure, by induction on the dimension. -/
theorem gaussPL_pi_fin : ∀ n : ℕ,
    GaussPL (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (fun p x y k => (1 - p) * x k + p * y k)
      (fun x y => ∑ k, (x k - y k) ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro p hp0 hp1 F G H hF hG hH hcond
    have hpi := Measure.pi_of_empty (fun _ : Fin 0 => gaussianReal 0 1)
    rw [hpi, lintegral_dirac' _ hF, lintegral_dirac' _ hG,
      lintegral_dirac' _ hH]
    calc F (fun a => isEmptyElim a) ^ (1 - p) *
          G (fun a => isEmptyElim a) ^ p
        = F (fun a => isEmptyElim a) ^ (1 - p) *
            G (fun a => isEmptyElim a) ^ p *
            ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) *
              ∑ k : Fin 0, ((fun a : Fin 0 => (isEmptyElim a : ℝ)) k -
                (fun a : Fin 0 => (isEmptyElim a : ℝ)) k) ^ 2)) := by
          simp
      _ ≤ H (fun k : Fin 0 =>
            (1 - p) * (fun a : Fin 0 => (isEmptyElim a : ℝ)) k +
              p * (fun a : Fin 0 => (isEmptyElim a : ℝ)) k) := hcond _ _
      _ = H (fun a => isEmptyElim a) :=
          congrArg H (funext fun a => isEmptyElim a)
  | succ n ih =>
    have hprod := GaussPL.prod gaussPL_real ih
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      with he_def
    have he : MeasurePreserving e
        (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
        ((gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
      measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
    refine GaussPL.transfer hprod e he ?_ ?_
    · intro p x y
      rfl
    · intro x y
      exact (Fin.sum_univ_succAbove (fun k => (x k - y k) ^ 2) 0).symm

/-- Lean implementation helper: **Gaussian Prékopa–Leindler on `ι → ℝ`** for any finite index type,
with the standard Gaussian product measure, componentwise convex
combination, and squared-euclidean transport cost. -/
theorem gaussPL_pi (ι : Type*) [Fintype ι] :
    GaussPL (Measure.pi fun _ : ι => gaussianReal 0 1)
      (fun p x y k => (1 - p) * x k + p * y k)
      (fun x y => ∑ k, (x k - y k) ^ 2) := by
  set fEq : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hfEq
  set e : (ι → ℝ) ≃ᵐ (Fin (Fintype.card ι) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℝ) fEq
    with he_def
  have happly : ∀ (x : ι → ℝ) (k : Fin (Fintype.card ι)),
      e x k = x (fEq.symm k) := by
    intro x k
    have h1 := Equiv.piCongrLeft_apply_apply
      (fun _ : Fin (Fintype.card ι) => ℝ) fEq x (fEq.symm k)
    rw [Equiv.apply_symm_apply] at h1
    exact h1
  have he : MeasurePreserving e
      (Measure.pi fun _ : ι => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft
      (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) fEq
  refine GaussPL.transfer (gaussPL_pi_fin (Fintype.card ι)) e he ?_ ?_
  · intro p x y
    funext k
    rw [happly, happly, happly]
  · intro x y
    calc ∑ k, (e x k - e y k) ^ 2
        = ∑ k, (x (fEq.symm k) - y (fEq.symm k)) ^ 2 :=
          Finset.sum_congr rfl fun k _ => by rw [happly, happly]
      _ = ∑ i, (x i - y i) ^ 2 :=
          Equiv.sum_comp fEq.symm fun i => (x i - y i) ^ 2

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.6: Sharp Gaussian concentration for Lipschitz functions

For the proof of **Book eq. (4.1.8)**, starting
from the tensorised Gaussian Prékopa–Leindler theorem `gaussPL_pi`, this file
proves the sharp dimension-free concentration inequality for a Lipschitz
function of a finite standard Gaussian vector.

The proof follows the direct property-(τ) argument recorded in
`UP005_PROGRESS.md`: an elementary complete-the-square choice of the three
Prékopa–Leindler functions yields a Laplace-transform bound with parameter
`p ∈ (0,1)`; Jensen controls the second factor; the limit `p → 1⁻` recovers
the sharp constant `1/2`; and Mathlib's sub-Gaussian Chernoff lemma gives the
tail. Exponential integrability is proved directly from the one-dimensional
Gaussian exponential moment, Fubini over the finite product, and
`√(∑xᵢ²) ≤ ∑|xᵢ|`.
-/

namespace MatrixConcentration

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-- Lean implementation helper: the Euclidean norm is bounded by the ℓ₁ norm. -/
lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (∑ k, x k ^ 2) ≤ ∑ k, |x k| := by
  classical
  have habs : 0 ≤ ∑ k, |x k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.sqrt_le_iff]
  refine ⟨habs, ?_⟩
  simpa only [sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun k => |x k|) (fun _ _ => abs_nonneg _))

/-- Lean implementation helper: exponentials of a Lipschitz function are integrable
under a finite product of standard Gaussian measures. -/
lemma integrable_exp_mul_lipschitz_gaussianPi
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |W x - W y| ≤
      L * Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) (c : ℝ) :
    Integrable (fun x => Real.exp (c * W x))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let a : ℝ := |c| * L
  have hcoord : ∀ k : ι,
      Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 1) := by
    intro k
    exact integrable_exp_mul_abs
      (ProbabilityTheory.integrable_exp_mul_gaussianReal a)
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (-a))
  have hprod : Integrable
      (fun x : ι → ℝ => ∏ k, Real.exp (a * |x k|)) γ := by
    exact MeasureTheory.Integrable.fintype_prod hcoord
  have hdom : Integrable
      (fun x : ι → ℝ => Real.exp (|c| * |W 0|) *
        ∏ k, Real.exp (a * |x k|)) γ := hprod.const_mul _
  refine hdom.mono' ((hmeas.const_mul c).exp.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hW : |W x| ≤ |W 0| + L * ∑ k, |x k| := by
    calc
      |W x| ≤ |W x - W 0| + |W 0| := by
        have := abs_add_le (W x - W 0) (W 0)
        simpa only [sub_add_cancel] using this
      _ ≤ L * Real.sqrt (∑ k, (x k - (0 : ι → ℝ) k) ^ 2) + |W 0| :=
        add_le_add_left (hLip x 0) |W 0|
      _ ≤ L * (∑ k, |x k|) + |W 0| := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left (by simpa using sqrt_sum_sq_le_sum_abs x) hL) _
      _ = |W 0| + L * ∑ k, |x k| := by ring
  have hcW : c * W x ≤ |c| * |W x| := by
    calc c * W x ≤ |c * W x| := le_abs_self _
      _ = |c| * |W x| := abs_mul _ _
  calc
    Real.exp (c * W x) ≤ Real.exp (|c| * |W x|) := Real.exp_le_exp.mpr hcW
    _ ≤ Real.exp (|c| * (|W 0| + L * ∑ k, |x k|)) := by
      gcongr
    _ = Real.exp (|c| * |W 0|) * Real.exp (∑ k, a * |x k|) := by
      rw [← Real.exp_add]
      congr 1
      simp only [a, mul_add, mul_assoc, Finset.mul_sum]
    _ = Real.exp (|c| * |W 0|) * ∏ k, Real.exp (a * |x k|) := by
      rw [Real.exp_sum]

/-- Lean implementation helper: the Prékopa–Leindler estimate at an intermediate
parameter `p ∈ (0,1)`. -/
lemma gaussian_lipschitz_pl_bound
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs : 0 < s) :
    (∫ x, Real.exp (p * s * W x)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      Real.exp (p * (s *
        (∫ x, W x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + s ^ 2 / 2)) := by
  classical
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have h1p : 0 < 1 - p := by linarith
  have hExp : ∀ c : ℝ, Integrable (fun x => Real.exp (c * W x)) γ := by
    intro c
    exact integrable_exp_mul_lipschitz_gaussianPi ι W (L := 1) zero_le_one
      (by simpa using hLip) hmeas c
  have hWint : Integrable W γ := by
    simpa using integrable_pow_of_integrable_exp_mul (X := W) (μ := γ)
      one_ne_zero (hExp 1) (hExp (-1)) 1
  let F : (ι → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (p * (s * W x - s ^ 2 / 2)))
  let G : (ι → ℝ) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (-(1 - p) * s * W y))
  let H : (ι → ℝ) → ℝ≥0∞ := fun _ => 1
  have hFm : Measurable F := by
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hGm : Measurable G := by
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hHm : Measurable H := measurable_const
  have hcond : ∀ x y : ι → ℝ,
      F x ^ (1 - p) * G y ^ p *
          ENNReal.ofReal (Real.exp (-(p * (1 - p) / 2) *
            ∑ k, (x k - y k) ^ 2)) ≤
        H (fun k => (1 - p) * x k + p * y k) := by
    intro x y
    let d : ℝ := ∑ k, (x k - y k) ^ 2
    have hd : 0 ≤ d := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hdiff : W x - W y ≤ Real.sqrt d := by
      exact (le_abs_self _).trans (by simpa [d] using hLip x y)
    have hamgm : s * Real.sqrt d ≤ s ^ 2 / 2 + d / 2 := by
      have hsqrt : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd
      nlinarith [sq_nonneg (Real.sqrt d - s)]
    have hbase : s * (W x - W y) - s ^ 2 / 2 - d / 2 ≤ 0 := by
      have hmul := mul_le_mul_of_nonneg_left hdiff hs.le
      nlinarith
    have harg : p * (1 - p) *
        (s * (W x - W y) - s ^ 2 / 2 - d / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp0.le h1p.le) hbase
    simp only [F, G, H]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← Real.exp_mul, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add]
    apply ENNReal.ofReal_le_one.mpr
    rw [Real.exp_le_one_iff]
    convert harg using 1
    simp only [d]
    ring
  have hPL := (gaussPL_pi ι) p hp0 hp1 F G H hFm hGm hHm hcond
  have hFint : Integrable
      (fun x => Real.exp (p * (s * W x - s ^ 2 / 2))) γ := by
    have heq : (fun x => Real.exp (p * (s * W x - s ^ 2 / 2))) =
        fun x => Real.exp (-p * s ^ 2 / 2) * Real.exp ((p * s) * W x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact (hExp (p * s)).const_mul _
  have hGint : Integrable
      (fun x => Real.exp (-(1 - p) * s * W x)) γ := by
    convert hExp (-(1 - p) * s) using 1
  have hFL : (∫⁻ x, F x ∂γ) = ENNReal.ofReal
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / 2)) ∂γ) := by
    simp only [F]
    rw [← ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall fun _ => (Real.exp_nonneg _))]
  have hGL : (∫⁻ x, G x ∂γ) = ENNReal.ofReal
      (∫ x, Real.exp (-(1 - p) * s * W x) ∂γ) := by
    simp only [G]
    rw [← ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall fun _ => (Real.exp_nonneg _))]
  have hHL : (∫⁻ x, H x ∂γ) = 1 := by simp [H, γ]
  rw [show (Measure.pi fun _ : ι => gaussianReal 0 1) = γ from rfl,
    hFL, hGL, hHL] at hPL
  have hFpos : 0 < ∫ x, Real.exp (p * (s * W x - s ^ 2 / 2)) ∂γ :=
    integral_exp_pos hFint
  have hGpos : 0 < ∫ x, Real.exp (-(1 - p) * s * W x) ∂γ :=
    integral_exp_pos hGint
  have hPLreal :
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / 2)) ∂γ) ^ (1 - p) *
        (∫ x, Real.exp (-(1 - p) * s * W x) ∂γ) ^ p ≤ 1 := by
    have ht := ENNReal.toReal_mono (by simp) hPL
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hFpos.le, ENNReal.toReal_ofReal hGpos.le,
      ENNReal.toReal_one] at ht
    exact ht
  let m : ℝ := ∫ x, W x ∂γ
  let J : ℝ := Real.exp (-(1 - p) * s * m)
  have hJpos : 0 < J := Real.exp_pos _
  have hJ : J ≤ ∫ x, Real.exp (-(1 - p) * s * W x) ∂γ := by
    have hjensen := convexOn_exp.map_integral_le Real.continuousOn_exp isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      (hWint.const_mul (-(1 - p) * s)) hGint
    simpa only [Function.comp_apply, integral_const_mul, J, m] using hjensen
  have hcore :
      (∫ x, Real.exp (p * (s * W x - s ^ 2 / 2)) ∂γ) ^ (1 - p) *
        J ^ p ≤ 1 := by
    calc
      _ ≤ (∫ x, Real.exp (p * (s * W x - s ^ 2 / 2)) ∂γ) ^ (1 - p) *
          (∫ x, Real.exp (-(1 - p) * s * W x) ∂γ) ^ p := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hJpos.le hJ hp0.le) (Real.rpow_nonneg hFpos.le _)
      _ ≤ 1 := hPLreal
  let A : ℝ := ∫ x, Real.exp (p * s * W x) ∂γ
  have hAint : Integrable (fun x => Real.exp (p * s * W x)) γ := by
    convert hExp (p * s) using 1
  have hApos : 0 < A := integral_exp_pos hAint
  have hFeq : (∫ x, Real.exp (p * (s * W x - s ^ 2 / 2)) ∂γ) =
      Real.exp (-p * s ^ 2 / 2) * A := by
    have heq : (fun x => Real.exp (p * (s * W x - s ^ 2 / 2))) =
        fun x => Real.exp (-p * s ^ 2 / 2) * Real.exp (p * s * W x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, integral_const_mul]
  have hlog :
      (1 - p) * Real.log (Real.exp (-p * s ^ 2 / 2) * A) +
        p * Real.log J ≤ 0 := by
    have hleftpos : 0 <
        (Real.exp (-p * s ^ 2 / 2) * A) ^ (1 - p) * J ^ p := by positivity
    have hlogle : Real.log
        ((Real.exp (-p * s ^ 2 / 2) * A) ^ (1 - p) * J ^ p) ≤
        Real.log 1 := by
      apply Real.log_le_log hleftpos
      simpa only [hFeq] using hcore
    rw [Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne'
        (Real.rpow_pos_of_pos hJpos _).ne',
      Real.log_rpow (by positivity), Real.log_rpow hJpos,
      Real.log_one] at hlogle
    exact hlogle
  have hlogA : Real.log A ≤ p * (s * m + s ^ 2 / 2) := by
    rw [Real.log_mul (Real.exp_ne_zero _) hApos.ne', Real.log_exp] at hlog
    simp only [J, Real.log_exp] at hlog
    nlinarith
  have hAle : A ≤ Real.exp (p * (s * m + s ^ 2 / 2)) :=
    Real.le_exp_of_log_le hlogA
  simpa only [A, m, γ] using hAle

/-- Lean implementation helper: pass `p → 1⁻` in the positive-parameter uncentered
Gaussian Lipschitz mgf bound. -/
lemma gaussian_lipschitz_mgf_pos_uncentered
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) {u : ℝ} (hu : 0 < u) :
    (∫ x, Real.exp (u * W x)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      Real.exp (u *
        (∫ x, W x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + u ^ 2 / 2) := by
  classical
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let m : ℝ := ∫ x, W x ∂γ
  let q : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hq0 : ∀ n : ℕ, 1 ≤ n → 0 < q n := by
    intro n hn
    simp only [q]
    have hn1 : 1 < (n : ℝ) + 1 := by exact_mod_cast Nat.lt_add_one_iff.mpr hn
    rw [sub_pos, div_lt_one (by positivity)]
    exact hn1
  have hq1 : ∀ n : ℕ, q n < 1 := by
    intro n
    simp only [q]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hbound : ∀ n : ℕ, 1 ≤ n →
      (∫ x, Real.exp (u * W x) ∂γ) ≤
        Real.exp (u * m + u ^ 2 / (2 * q n)) := by
    intro n hn
    have hqn0 := hq0 n hn
    have h := gaussian_lipschitz_pl_bound ι W hLip hmeas
      hqn0 (hq1 n) (div_pos hu hqn0)
    have hqn : q n ≠ 0 := hqn0.ne'
    convert h using 1 <;> simp only [γ, m]
    · congr 2
      field_simp
    · congr 2
      field_simp
  have hqtend : Tendsto q atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := hone.sub hzero
    simpa only [q, sub_zero] using h
  have hcont : ContinuousAt (fun r : ℝ =>
      Real.exp (u * m + u ^ 2 / (2 * r))) 1 := by
    fun_prop (disch := norm_num)
  have hrhs : Tendsto (fun n : ℕ =>
      Real.exp (u * m + u ^ 2 / (2 * q n))) atTop
      (nhds (Real.exp (u * m + u ^ 2 / 2))) := by
    have hcomp := hcont.tendsto.comp hqtend
    change Tendsto (fun n : ℕ => Real.exp (u * m + u ^ 2 / (2 * q n))) atTop
      (nhds (Real.exp (u * m + u ^ 2 / (2 * (1 : ℝ))))) at hcomp
    simpa only [mul_one] using hcomp
  have hle : (∫ x, Real.exp (u * W x) ∂γ) ≤
      Real.exp (u * m + u ^ 2 / 2) := by
    refine ge_of_tendsto hrhs ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
  simpa only [γ, m] using hle

/-- Lean implementation helper: center the positive-parameter Gaussian Lipschitz mgf
bound. -/
lemma gaussian_lipschitz_mgf_pos_centered
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) {u : ℝ} (hu : 0 < u) :
    (∫ x, Real.exp (u * (W x -
        (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1))))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      Real.exp (u ^ 2 / 2) := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let m : ℝ := ∫ y, W y ∂γ
  have hunc := gaussian_lipschitz_mgf_pos_uncentered ι W hLip hmeas hu
  rw [show (Measure.pi fun _ : ι => gaussianReal 0 1) = γ from rfl] at hunc ⊢
  calc
    (∫ x, Real.exp (u * (W x - m)) ∂γ) =
        Real.exp (-u * m) * ∫ x, Real.exp (u * W x) ∂γ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-u * m) * Real.exp (u * m + u ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by simpa only [m] using hunc) (Real.exp_nonneg _)
    _ = Real.exp (u ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Lean implementation helper: extend the centered Gaussian Lipschitz mgf bound to
all real parameters. -/
lemma gaussian_lipschitz_mgf_centered
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) (u : ℝ) :
    (∫ x, Real.exp (u * (W x -
        (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1))))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      Real.exp (u ^ 2 / 2) := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · let V : (ι → ℝ) → ℝ := fun x => -W x
    have hVLip : ∀ x y, |V x - V y| ≤
        Real.sqrt (∑ k, (x k - y k) ^ 2) := by
      intro x y
      change |-W x - -W y| ≤ _
      rw [show -W x - -W y = -(W x - W y) by ring, abs_neg]
      exact hLip x y
    have hVmeas : Measurable V := hmeas.neg
    have h := gaussian_lipschitz_mgf_pos_centered ι V hVLip hVmeas (neg_pos.mpr hu)
    have heq : (fun x => Real.exp ((-u) * (V x -
        (∫ y, V y ∂(Measure.pi fun _ : ι => gaussianReal 0 1))))) =
        fun x => Real.exp (u * (W x -
          (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)))) := by
      funext x
      congr 1
      simp only [V, integral_neg]
      ring
    rw [heq] at h
    convert h using 1
    ring
  · subst u
    simp
  · exact gaussian_lipschitz_mgf_pos_centered ι W hLip hmeas hu

/-- Lean implementation helper: package a one-Lipschitz Gaussian functional as a
sub-Gaussian random variable with variance proxy one. -/
theorem gaussian_lipschitz_hasSubgaussianMGF_one
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) :
    HasSubgaussianMGF
      (fun x => W x -
        (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1))) 1
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let m : ℝ := ∫ y, W y ∂γ
  have hExp : ∀ c : ℝ, Integrable (fun x => Real.exp (c * W x)) γ := by
    intro c
    exact integrable_exp_mul_lipschitz_gaussianPi ι W (L := 1) zero_le_one
      (by simpa using hLip) hmeas c
  constructor
  · intro c
    have heq : (fun x => Real.exp (c * (W x - m))) =
        fun x => Real.exp (-c * m) * Real.exp (c * W x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show (Measure.pi fun _ : ι => gaussianReal 0 1) = γ from rfl]
    rw [heq]
    exact (hExp c).const_mul _
  · intro c
    simpa only [ProbabilityTheory.mgf, γ, m, NNReal.coe_one, one_mul] using
      gaussian_lipschitz_mgf_centered ι W hLip hmeas c

/-- Lean implementation helper: sharp upper-tail concentration for a one-Lipschitz
function of a finite standard Gaussian vector. -/
theorem gaussian_lipschitz_tail_one
    (ι : Type*) [Fintype ι] (W : (ι → ℝ) → ℝ)
    (hLip : ∀ x y, |W x - W y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x | (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + t ≤ W x} ≤
      Real.exp (-(t ^ 2) / 2) := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have htail := (gaussian_lipschitz_hasSubgaussianMGF_one ι W hLip hmeas).measure_ge_le ht
  have hset : {x | t ≤ W x -
      (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1))} =
      {x | (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + t ≤ W x} := by
    apply Set.ext
    intro x
    change (t ≤ W x -
      (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1))) ↔
      ((∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + t ≤ W x)
    constructor <;> intro h <;> linarith
  rw [show (Measure.pi fun _ : ι => gaussianReal 0 1) = γ from rfl] at htail ⊢
  rw [hset] at htail
  simpa only [NNReal.coe_one, mul_one] using htail

/-- Lean implementation helper: sharp upper-tail concentration for an
`L`-Lipschitz function of a finite standard Gaussian vector. -/
theorem gaussian_lipschitz_tail (ι : Type*) [Fintype ι]
    (W : (ι → ℝ) → ℝ) {L : ℝ} (hL : 0 < L)
    (hLip : ∀ x y, |W x - W y| ≤ L * Real.sqrt (∑ k, (x k - y k) ^ 2))
    (hmeas : Measurable W) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x | (∫ y, W y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + t ≤ W x}
      ≤ Real.exp (-(t ^ 2) / (2 * L ^ 2)) := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let V : (ι → ℝ) → ℝ := fun x => W x / L
  have hVmeas : Measurable V := hmeas.div_const L
  have hVLip : ∀ x y, |V x - V y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2) := by
    intro x y
    simp only [V]
    rw [div_sub_div_same, abs_div, abs_of_pos hL]
    exact (div_le_iff₀ hL).mpr (by simpa [mul_comm] using hLip x y)
  have htail := gaussian_lipschitz_tail_one ι V hVLip hVmeas
    (t := t / L) (div_nonneg ht hL.le)
  have hmean : (∫ y, V y ∂γ) = (∫ y, W y ∂γ) / L := by
    simp only [V, integral_div]
  have hset : {x | (∫ y, V y ∂γ) + t / L ≤ V x} =
      {x | (∫ y, W y ∂γ) + t ≤ W x} := by
    ext x
    simp only [Set.mem_setOf_eq, hmean, V]
    rw [← add_div]
    exact div_le_div_iff_of_pos_right hL
  rw [show (Measure.pi fun _ : ι => gaussianReal 0 1) = γ from rfl] at htail ⊢
  rw [hset] at htail
  calc
    γ.real {x | (∫ y, W y ∂γ) + t ≤ W x} ≤
        Real.exp (-(t / L) ^ 2 / 2) := htail
    _ = Real.exp (-(t ^ 2) / (2 * L ^ 2)) := by
      congr 1
      field_simp

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.7: Matrix Gaussian concentration

This section proves
that the spectral norm of a rectangular matrix series is Lipschitz with
constant equal to the square root of its weak variance, applies the sharp
product-Gaussian concentration theorem from `06_GaussianLipschitz`, and
transfers the result to an arbitrary independent standard-Gaussian family.

The auxiliary definitions `gaussianWeakVarianceSet` and
`gaussianWeakVariance` deliberately have the same bodies as the Chapter 4
definitions. Keeping them here makes the dependency acyclic; Chapter 4 relates
the two pairs by unfolding their definitions.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory Set
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: The weak-variance values, duplicated here to keep the Appendix-to-Chapter
dependency acyclic. -/
def gaussianWeakVarianceSet (B : ι → Matrix m n ℂ) : Set ℝ :=
  {r | ∃ (u : m → ℂ) (w : n → ℂ), l2norm u = 1 ∧ l2norm w = 1 ∧
    r = ∑ k, ‖star u ⬝ᵥ (B k *ᵥ w)‖ ^ 2}

/-- Lean implementation helper: The weak variance used by the standalone matrix Gaussian reduction. -/
noncomputable def gaussianWeakVariance (B : ι → Matrix m n ℂ) : ℝ :=
  sSup (gaussianWeakVarianceSet B)

/-- Lean implementation helper: standard basis vectors have unit ℓ₂ norm. -/
private lemma l2norm_single_one_aux {a : Type*} [Fintype a] [DecidableEq a]
    (j : a) : l2norm (Pi.single j (1 : ℂ)) = 1 := by
  rw [l2norm_eq_sqrt_sum]
  have hsum : ∑ i, ‖(Pi.single j (1 : ℂ) : a → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij]
    · exact fun h => absurd (Finset.mem_univ j) h
  rw [hsum, Real.sqrt_one]

/-- Lean implementation helper: the auxiliary weak-variance value set is nonempty. -/
lemma gaussianWeakVarianceSet_nonempty (B : ι → Matrix m n ℂ) :
    (gaussianWeakVarianceSet B).Nonempty :=
  ⟨_, Pi.single (Classical.arbitrary m) 1, Pi.single (Classical.arbitrary n) 1,
    l2norm_single_one_aux _, l2norm_single_one_aux _, rfl⟩

/-- Lean implementation helper: bound each auxiliary weak-variance value by the sum
of squared coefficient norms. -/
lemma gaussianWeakVarianceSet_le_sum_normsq {B : ι → Matrix m n ℂ} {r : ℝ}
    (hr : r ∈ gaussianWeakVarianceSet B) : r ≤ ∑ k, ‖B k‖ ^ 2 := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hr
  refine Finset.sum_le_sum fun k _ => ?_
  have h := norm_dotProduct_mulVec_le (B k) u w
  rw [hu, hw, mul_one, mul_one] at h
  nlinarith [norm_nonneg (star u ⬝ᵥ (B k *ᵥ w)), norm_nonneg (B k)]

/-- Lean implementation helper: the auxiliary weak-variance value set is bounded
above. -/
lemma gaussianWeakVarianceSet_bddAbove (B : ι → Matrix m n ℂ) :
    BddAbove (gaussianWeakVarianceSet B) :=
  ⟨∑ k, ‖B k‖ ^ 2, fun _ hr => gaussianWeakVarianceSet_le_sum_normsq hr⟩

/-- Lean implementation helper: auxiliary weak variance is nonnegative. -/
lemma gaussianWeakVariance_nonneg (B : ι → Matrix m n ℂ) :
    0 ≤ gaussianWeakVariance B := by
  obtain ⟨r, hr⟩ := gaussianWeakVarianceSet_nonempty B
  have h0 : 0 ≤ r := by
    obtain ⟨u, w, _, _, rfl⟩ := hr
    positivity
  exact h0.trans (le_csSup (gaussianWeakVarianceSet_bddAbove B) hr)

/-- Lean implementation helper: The vector of matrix pairings is controlled by the weak variance, with
the correct homogeneous factors for arbitrary test vectors. -/
lemma pairing_l2norm_le_gaussianWeakVariance (B : ι → Matrix m n ℂ)
    (u : m → ℂ) (w : n → ℂ) :
    l2norm (fun k => star u ⬝ᵥ (B k *ᵥ w)) ≤
      Real.sqrt (gaussianWeakVariance B) * l2norm u * l2norm w := by
  classical
  by_cases hu : u = 0
  · subst u
    simp [l2norm_eq_sqrt_sum]
  by_cases hw : w = 0
  · subst w
    simp [l2norm_eq_sqrt_sum]
  have hupos : 0 < l2norm u := l2norm_pos_of_ne_zero hu
  have hwpos : 0 < l2norm w := l2norm_pos_of_ne_zero hw
  let u₀ : m → ℂ := ((l2norm u : ℂ)⁻¹) • u
  let w₀ : n → ℂ := ((l2norm w : ℂ)⁻¹) • w
  have hu₀ : l2norm u₀ = 1 := by
    simp only [u₀]
    rw [l2norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hupos.le]
    exact inv_mul_cancel₀ hupos.ne'
  have hw₀ : l2norm w₀ = 1 := by
    simp only [w₀]
    rw [l2norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hwpos.le]
    exact inv_mul_cancel₀ hwpos.ne'
  let q₀ : ι → ℂ := fun k => star u₀ ⬝ᵥ (B k *ᵥ w₀)
  have hq₀sq : ∑ k, ‖q₀ k‖ ^ 2 ≤ gaussianWeakVariance B :=
    le_csSup (gaussianWeakVarianceSet_bddAbove B) ⟨u₀, w₀, hu₀, hw₀, rfl⟩
  have hq₀ : l2norm q₀ ≤ Real.sqrt (gaussianWeakVariance B) := by
    rw [l2norm_eq_sqrt_sum]
    exact Real.sqrt_le_sqrt hq₀sq
  have hq : (fun k => star u ⬝ᵥ (B k *ᵥ w)) =
      ((l2norm u * l2norm w : ℝ) : ℂ) • q₀ := by
    funext k
    simp only [q₀, u₀, w₀, Pi.smul_apply]
    rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
    simp only [star_inv₀, RCLike.star_def, Complex.conj_ofReal, smul_eq_mul]
    field_simp
    push_cast
    ring
  rw [hq, l2norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hupos.le hwpos.le)]
  calc
    l2norm u * l2norm w * l2norm q₀
        ≤ l2norm u * l2norm w * Real.sqrt (gaussianWeakVariance B) := by
          exact mul_le_mul_of_nonneg_left hq₀ (mul_nonneg hupos.le hwpos.le)
    _ = Real.sqrt (gaussianWeakVariance B) * l2norm u * l2norm w := by ring

/-- Lean implementation helper: The norm of a deterministic matrix series is bounded by weak variance
times the Euclidean norm of its coefficients. -/
lemma norm_matrix_series_le_gaussianWeakVariance (B : ι → Matrix m n ℂ)
    (c : ι → ℝ) :
    ‖∑ k, c k • B k‖ ≤
      Real.sqrt (gaussianWeakVariance B) * Real.sqrt (∑ k, (c k) ^ 2) := by
  classical
  refine l2_opNorm_le_of_forall_dotProduct _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) fun u w => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  have hdot : (∑ k, star u ⬝ᵥ ((c k • B k) *ᵥ w)) =
      star (fun k => (c k : ℂ)) ⬝ᵥ (fun k => star u ⬝ᵥ (B k *ᵥ w)) := by
    have hleft : (∑ k, star u ⬝ᵥ ((c k • B k) *ᵥ w)) =
        ∑ k, c k • (star u ⬝ᵥ (B k *ᵥ w)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul]
    rw [hleft]
    change (∑ k, c k • (star u ⬝ᵥ (B k *ᵥ w))) =
      ∑ k, star (c k : ℂ) * (star u ⬝ᵥ (B k *ᵥ w))
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.star_def, Complex.conj_ofReal]
    rfl
  rw [hdot]
  have hc : l2norm (fun k => (c k : ℂ)) = Real.sqrt (∑ k, (c k) ^ 2) := by
    rw [l2norm_eq_sqrt_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    ‖star (fun k => (c k : ℂ)) ⬝ᵥ (fun k => star u ⬝ᵥ (B k *ᵥ w))‖
        ≤ l2norm (fun k => (c k : ℂ)) *
            l2norm (fun k => star u ⬝ᵥ (B k *ᵥ w)) := norm_dotProduct_le _ _
    _ ≤ l2norm (fun k => (c k : ℂ)) *
          (Real.sqrt (gaussianWeakVariance B) * l2norm u * l2norm w) := by
        gcongr
        · exact l2norm_nonneg _
        · exact pairing_l2norm_le_gaussianWeakVariance B u w
    _ = (Real.sqrt (gaussianWeakVariance B) * Real.sqrt (∑ k, (c k) ^ 2)) *
          l2norm u * l2norm w := by rw [hc]; ring

/-- Lean implementation helper: measurability of the deterministic matrix-series
norm as a function of its coefficient vector. -/
lemma measurable_matrix_series_norm (B : ι → Matrix m n ℂ) :
    Measurable (fun c : ι → ℝ => ‖∑ k, c k • B k‖) := by
  have hcont : Continuous (fun c : ι → ℝ => ‖∑ k, c k • B k‖) := by
    fun_prop
  exact hcont.measurable

/-- Lean implementation helper: The spectral norm of the matrix series is square-root-weak-variance
Lipschitz in its real coefficient vector. -/
lemma matrix_series_norm_lipschitz (B : ι → Matrix m n ℂ) (x y : ι → ℝ) :
    |‖∑ k, x k • B k‖ - ‖∑ k, y k • B k‖| ≤
      Real.sqrt (gaussianWeakVariance B) * Real.sqrt (∑ k, (x k - y k) ^ 2) := by
  calc
    |‖∑ k, x k • B k‖ - ‖∑ k, y k • B k‖|
        ≤ ‖(∑ k, x k • B k) - ∑ k, y k • B k‖ := abs_norm_sub_norm_le _ _
    _ = ‖∑ k, (x k - y k) • B k‖ := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_smul]
    _ ≤ Real.sqrt (gaussianWeakVariance B) * Real.sqrt (∑ k, (x k - y k) ^ 2) :=
      norm_matrix_series_le_gaussianWeakVariance B (fun k => x k - y k)

/-- Lean implementation helper: Sharp upper-tail concentration for a rectangular matrix series driven by
an arbitrary independent standard-Gaussian family.  The law assumption is
stated directly as a pushforward equality so this Appendix theorem is
independent of the Chapter 4 wrapper `IsStdGaussian`. -/
theorem matrix_gaussian_concentration
    {γ : ι → Ω → ℝ} (B : ι → Matrix m n ℂ)
    (hmeas : ∀ k, Measurable (γ k))
    (hlaw : ∀ k, μ.map (γ k) = ProbabilityTheory.gaussianReal 0 1)
    (hind : ProbabilityTheory.iIndepFun γ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (∫ ω', ‖∑ k, γ k ω' • B k‖ ∂μ) + t ≤
        ‖∑ k, γ k ω • B k‖} ≤
      Real.exp (-(t ^ 2) / (2 * gaussianWeakVariance B)) := by
  classical
  have hvnn : 0 ≤ gaussianWeakVariance B := gaussianWeakVariance_nonneg B
  rcases eq_or_lt_of_le hvnn with hv0 | hvpos
  · rw [← hv0, mul_zero, div_zero, Real.exp_zero]
    letI : IsProbabilityMeasure μ := hind.isProbabilityMeasure
    exact measureReal_le_one
  let ν : Measure (ι → ℝ) :=
    Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
  let Φ : Ω → (ι → ℝ) := fun ω k => γ k ω
  let W : (ι → ℝ) → ℝ := fun c => ‖∑ k, c k • B k‖
  have hΦ : Measurable Φ := measurable_pi_lambda _ hmeas
  have hW : Measurable W := measurable_matrix_series_norm B
  have hmap : μ.map Φ = ν := by
    rw [hind.map_fun_eq_pi_map (fun k => (hmeas k).aemeasurable)]
    simp only [ν]
    congr 1
    funext k
    exact hlaw k
  have hmean : (∫ ω, ‖∑ k, γ k ω • B k‖ ∂μ) = ∫ c, W c ∂ν := by
    calc
      (∫ ω, ‖∑ k, γ k ω • B k‖ ∂μ) = ∫ ω, W (Φ ω) ∂μ := by rfl
      _ = ∫ c, W c ∂(μ.map Φ) :=
        (MeasureTheory.integral_map hΦ.aemeasurable hW.aestronglyMeasurable).symm
      _ = ∫ c, W c ∂ν := by rw [hmap]
  let S : Set (ι → ℝ) := {c | (∫ d, W d ∂ν) + t ≤ W c}
  have hS : MeasurableSet S := measurableSet_le measurable_const hW
  have hevent : {ω | (∫ ω', ‖∑ k, γ k ω' • B k‖ ∂μ) + t ≤
        ‖∑ k, γ k ω • B k‖} = Φ ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hmean]
    rfl
  have hLip : ∀ x y, |W x - W y| ≤ Real.sqrt (gaussianWeakVariance B) *
      Real.sqrt (∑ k, (x k - y k) ^ 2) := matrix_series_norm_lipschitz B
  have htail : ν.real S ≤ Real.exp (-(t ^ 2) / (2 * gaussianWeakVariance B)) := by
    have h := gaussian_lipschitz_tail ι W (Real.sqrt_pos.2 hvpos) hLip hW ht
    simpa only [ν, S, Real.sq_sqrt hvnn] using h
  calc
    μ.real {ω | (∫ ω', ‖∑ k, γ k ω' • B k‖ ∂μ) + t ≤
        ‖∑ k, γ k ω • B k‖}
        = μ.real (Φ ⁻¹' S) := by rw [hevent]
    _ = (μ.map Φ).real S := by
      rw [measureReal_def, measureReal_def, Measure.map_apply hΦ hS]
    _ = ν.real S := by rw [hmap]
    _ ≤ Real.exp (-(t ^ 2) / (2 * gaussianWeakVariance B)) := htail

end MatrixConcentration
