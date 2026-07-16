/-
Prelude for the formalization of Vershynin, "High-Dimensional Probability" (2nd ed.),
Chapters 1–2.

This file collects:

* book-specific distribution predicates (Rademacher, Bernoulli) built on Mathlib's
  `ProbabilityTheory.bernoulliMeasure`, with their expectation/MGF/moment API;
* small wrappers giving Mathlib inequalities the exact shape used by the book
  (Markov, tail splitting);
* the variance extremal property (Book Exercise 0.2, scalar case), a Chapter 0
  prerequisite used at Book (2.23);
* the numeric inequality `e^x ≤ 1 + x + (x²/2)e^{|x|}` used in the proofs of
  Book Propositions 2.6.1 and 2.8.1.

Declarations are classified per the translation reports: most items here are
"source prerequisites recovered from context" (Chapter 0 / basic-course facts the book
assumes) or "Lean implementation helpers"; correspondences with Mathlib are noted in
docstrings.
-/
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Tail-splitting and monotonicity helpers -/

/-- Lean implementation helper (book §2.2, unnumbered): the two-sided tail splits,
`ℙ{|X| ≥ t} ≤ ℙ{X ≥ t} + ℙ{−X ≥ t}`. Used to derive every two-sided bound in Chapter 2
from its one-sided version.

**Book Section 2.2.** -/
lemma real_tail_abs_le_add [IsFiniteMeasure μ] (X : Ω → ℝ) (t : ℝ) :
    μ.real {ω | t ≤ |X ω|} ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} := by
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    rcases abs_cases (X ω) with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl (by simp only [Set.mem_setOf_eq] at hω ⊢; simpa [h] using hω)
    · exact Or.inr (by simp only [Set.mem_setOf_eq] at hω ⊢; simpa [h] using hω)
  calc μ.real {ω | t ≤ |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _

/-- Tails are monotone in the threshold.

**Lean implementation helper.** -/
lemma real_tail_mono [IsFiniteMeasure μ] {X : Ω → ℝ} {s t : ℝ} (hst : s ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ μ.real {ω | s ≤ X ω} :=
  measureReal_mono (fun _ h => hst.trans h)

/-- First-order stochastic domination by all
closed upper tails implies domination of expectations. Integrability is
explicit because the variables need not be nonnegative.

**Lean implementation helper.** -/
theorem integral_le_integral_of_forall_measureReal_ge
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {μX : Measure ΩX} {μY : Measure ΩY}
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    {X : ΩX → ℝ} {Y : ΩY → ℝ}
    (hX : Integrable X μX) (hY : Integrable Y μY)
    (hTail : ∀ t : ℝ,
      μX.real {ω | t ≤ X ω} ≤ μY.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂μX) ≤ ∫ ω, Y ω ∂μY := by
  let Xp : ΩX → ℝ := fun ω ↦ max (X ω) 0
  let Xn : ΩX → ℝ := fun ω ↦ max (-X ω) 0
  let Yp : ΩY → ℝ := fun ω ↦ max (Y ω) 0
  let Yn : ΩY → ℝ := fun ω ↦ max (-Y ω) 0
  have hXp : Integrable Xp μX := by
    refine ⟨(hX.aemeasurable.max aemeasurable_const).aestronglyMeasurable, ?_⟩
    simpa [Xp] using hX.hasFiniteIntegral.max_zero
  have hXn : Integrable Xn μX := by
    refine ⟨(hX.neg.aemeasurable.max aemeasurable_const).aestronglyMeasurable, ?_⟩
    simpa [Xn] using hX.neg.hasFiniteIntegral.max_zero
  have hYp : Integrable Yp μY := by
    refine ⟨(hY.aemeasurable.max aemeasurable_const).aestronglyMeasurable, ?_⟩
    simpa [Yp] using hY.hasFiniteIntegral.max_zero
  have hYn : Integrable Yn μY := by
    refine ⟨(hY.neg.aemeasurable.max aemeasurable_const).aestronglyMeasurable, ?_⟩
    simpa [Yn] using hY.neg.hasFiniteIntegral.max_zero
  have hXp0 : 0 ≤ᵐ[μX] Xp :=
    Filter.Eventually.of_forall fun ω ↦ by simp [Xp]
  have hXn0 : 0 ≤ᵐ[μX] Xn :=
    Filter.Eventually.of_forall fun ω ↦ by simp [Xn]
  have hYp0 : 0 ≤ᵐ[μY] Yp :=
    Filter.Eventually.of_forall fun ω ↦ by simp [Yp]
  have hYn0 : 0 ≤ᵐ[μY] Yn :=
    Filter.Eventually.of_forall fun ω ↦ by simp [Yn]
  have hpos : (∫ ω, Xp ω ∂μX) ≤ ∫ ω, Yp ω ∂μY := by
    rw [integral_eq_lintegral_of_nonneg_ae hXp0 hXp.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hYp0 hYp.aestronglyMeasurable]
    apply ENNReal.toReal_mono (hYp.lintegral_lt_top.ne)
    rw [lintegral_eq_lintegral_meas_le μX hXp0 hXp.aemeasurable,
      lintegral_eq_lintegral_meas_le μY hYp0 hYp.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hleReal :
        μX.real {ω | t ≤ Xp ω} ≤ μY.real {ω | t ≤ Yp ω} := by
      have hXpSet : {ω | t ≤ Xp ω} = {ω | t ≤ X ω} := by
        ext ω
        simp [Xp, not_le_of_gt ht0]
      have hYpSet : {ω | t ≤ Yp ω} = {ω | t ≤ Y ω} := by
        ext ω
        simp [Yp, not_le_of_gt ht0]
      simpa only [hXpSet, hYpSet] using hTail t
    exact (ENNReal.toReal_le_toReal
      (measure_ne_top μX _) (measure_ne_top μY _)).mp hleReal
  have hneg : (∫ ω, Yn ω ∂μY) ≤ ∫ ω, Xn ω ∂μX := by
    rw [integral_eq_lintegral_of_nonneg_ae hYn0 hYn.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hXn0 hXn.aestronglyMeasurable]
    apply ENNReal.toReal_mono (hXn.lintegral_lt_top.ne)
    rw [lintegral_eq_lintegral_meas_lt μY hYn0 hYn.aemeasurable,
      lintegral_eq_lintegral_meas_lt μX hXn0 hXn.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hleReal :
        μY.real {ω | t < Yn ω} ≤ μX.real {ω | t < Xn ω} := by
      have hYnSet : {ω | t < Yn ω} = {ω | Y ω < -t} := by
        ext ω
        simp only [Yn, Set.mem_setOf_eq, lt_max_iff]
        rw [or_iff_left (not_lt_of_ge ht0.le)]
        constructor <;> intro h <;> linarith
      have hXnSet : {ω | t < Xn ω} = {ω | X ω < -t} := by
        ext ω
        simp only [Xn, Set.mem_setOf_eq, lt_max_iff]
        rw [or_iff_left (not_lt_of_ge ht0.le)]
        constructor <;> intro h <;> linarith
      rw [hYnSet, hXnSet]
      have hXmeas : NullMeasurableSet {ω | -t ≤ X ω} μX :=
        hX.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
      have hYmeas : NullMeasurableSet {ω | -t ≤ Y ω} μY :=
        hY.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
      rw [show {ω | Y ω < -t} = {ω | -t ≤ Y ω}ᶜ by ext; simp,
        show {ω | X ω < -t} = {ω | -t ≤ X ω}ᶜ by ext; simp,
        measureReal_compl₀ hYmeas, measureReal_compl₀ hXmeas,
        probReal_univ, probReal_univ]
      linarith [hTail (-t)]
    exact (ENNReal.toReal_le_toReal
      (measure_ne_top μY _) (measure_ne_top μX _)).mp hleReal
  have hXdecomp :
      (∫ ω, X ω ∂μX) = (∫ ω, Xp ω ∂μX) - ∫ ω, Xn ω ∂μX := by
    rw [← integral_sub hXp hXn]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [Xp, Xn]
    rcases le_total 0 (X ω) with h | h <;> simp [h]
  have hYdecomp :
      (∫ ω, Y ω ∂μY) = (∫ ω, Yp ω ∂μY) - ∫ ω, Yn ω ∂μY := by
    rw [← integral_sub hYp hYn]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [Yp, Yn]
    rcases le_total 0 (Y ω) with h | h <;> simp [h]
  rw [hXdecomp, hYdecomp]
  linarith

/-! ## Markov inequality, book form

Book Proposition 1.6.2 itself is stated and proved in `Chapter1.Probability`; this wrapper
is the raw Mathlib correspondence reused throughout Chapter 2. -/

/-- Mathlib correspondence lemma (the source Proposition 1.6.2, Markov inequality, source form):
for a nonnegative integrable random variable and `t > 0`, `ℙ{X ≥ t} ≤ 𝔼X / t`.
Wrapper around `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`.

**Book Proposition 1.6.2.** -/
lemma markov_real {X : Ω → ℝ} (hX_nonneg : 0 ≤ᵐ[μ] X) (hX_int : Integrable X μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ X ω} ≤ (∫ ω, X ω ∂μ) / t := by
  rw [le_div_iff₀ ht, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hX_nonneg hX_int t

/-! ## Functions are a.e. strongly measurable for two-point laws -/

/-- Every function is a.e. strongly measurable with respect to
the two-point Bernoulli measure.

**Lean implementation helper.** -/
lemma aestronglyMeasurable_bernoulliMeasure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {E : Type*} [TopologicalSpace E]
    (f : α → E) (x y : α) (p : I) :
    AEStronglyMeasurable f (bernoulliMeasure x y p) := by
  classical
  refine ⟨fun z => if z = x then f x else if z = y then f y else f y, ?_, ?_⟩
  · exact StronglyMeasurable.ite measurableSet_eq stronglyMeasurable_const
      (StronglyMeasurable.ite measurableSet_eq stronglyMeasurable_const
        stronglyMeasurable_const)
  · have hnull : bernoulliMeasure x y p ({x, y}ᶜ) = 0 := by
      rw [bernoulliMeasure_apply _ (MeasurableSet.compl (by measurability))]
      simp
    refine (MeasureTheory.ae_iff).mpr (measure_mono_null ?_ hnull)
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    by_cases hzx : z = x
    · exact absurd (by rw [if_pos hzx, hzx]) hz
    · by_cases hzy : z = y
      · exact absurd (by rw [if_neg hzx, if_pos hzy, hzy]) hz
      · exact ⟨hzx, hzy⟩

/-! ## Distribution predicates -/

/-- The **Rademacher distribution** (Book, Example 1.5.1 and §2.2): a random variable taking
values `−1` and `1` with probability `1/2` each.  The formal definition says that the law
of `X` is Mathlib's two-point `bernoulliMeasure` on `{1, −1}` with `p = 1/2`. -/
structure IsRademacher (X : Ω → ℝ) (μ : Measure Ω) : Prop where
  aemeasurable : AEMeasurable X μ
  map_eq : μ.map X = bernoulliMeasure (1 : ℝ) (-1) ⟨1/2, by norm_num, by norm_num⟩

/-- The **Bernoulli distribution** `Ber(p)` (Book, Example 1.7.4): values `1` and `0` with
probabilities `p` and `1−p`.  Explicit source definition. -/
structure IsBernoulli (X : Ω → ℝ) (p : I) (μ : Measure Ω) : Prop where
  aemeasurable : AEMeasurable X μ
  map_eq : μ.map X = bernoulliMeasure (1 : ℝ) 0 p

/-- A random variable whose law is a two-point measure lies
a.e. in the two-point set.

**Lean implementation helper.** -/
lemma ae_mem_pair_of_map_eq {X : Ω → ℝ} {x y : ℝ} {p : I}
    (hXm : AEMeasurable X μ) (hmap : μ.map X = bernoulliMeasure x y p) :
    ∀ᵐ ω ∂μ, X ω = x ∨ X ω = y := by
  classical
  have hms : MeasurableSet (({x, y} : Set ℝ)ᶜ) := (by measurability : MeasurableSet
    ({x, y} : Set ℝ)).compl
  have h0 : (μ.map X) (({x, y} : Set ℝ)ᶜ) = 0 := by
    rw [hmap, bernoulliMeasure_apply _ hms]
    simp
  have h1 : μ (X ⁻¹' ({x, y} : Set ℝ)ᶜ) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hXm hms]
    exact h0
  refine (MeasureTheory.ae_iff).mpr ?_
  convert h1 using 2
  ext ω
  simp [Set.mem_preimage, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or]

/-- Any composition `f(X)` of a random variable with a
two-point law is a.e. strongly measurable.

**Lean implementation helper.** -/
lemma aestronglyMeasurable_comp_of_map_eq {X : Ω → ℝ} {x y : ℝ} {p : I}
    (hXm : AEMeasurable X μ) (hmap : μ.map X = bernoulliMeasure x y p)
    (hxy : x ≠ y) (f : ℝ → ℝ) :
    AEStronglyMeasurable (fun ω => f (X ω)) μ := by
  classical
  have hmem_ae := ae_mem_pair_of_map_eq hXm hmap
  obtain ⟨Y, hYmeas, hXY⟩ := hXm
  refine ⟨fun ω => if Y ω = x then f x else f y, ?_, ?_⟩
  · exact StronglyMeasurable.ite (hYmeas (measurableSet_singleton x))
      stronglyMeasurable_const stronglyMeasurable_const
  · filter_upwards [hXY, hmem_ae] with ω hω hmem
    rcases hmem with h | h
    · rw [h] at hω ⊢
      rw [if_pos hω.symm]
    · rw [h] at hω ⊢
      rw [if_neg (by rw [← hω]; exact hxy.symm)]

/-- Any composition `f(X)` of a random variable with a
two-point law is integrable (it is a.e. bounded by `max |f x| |f y|`).

**Lean implementation helper.** -/
lemma integrable_comp_of_map_eq {X : Ω → ℝ} {x y : ℝ} {p : I}
    [IsProbabilityMeasure μ] (hXm : AEMeasurable X μ)
    (hmap : μ.map X = bernoulliMeasure x y p) (hxy : x ≠ y) (f : ℝ → ℝ) :
    Integrable (fun ω => f (X ω)) μ := by
  refine (memLp_top_of_bound (aestronglyMeasurable_comp_of_map_eq hXm hmap hxy f)
    (max |f x| |f y|) ?_).integrable le_top
  filter_upwards [ae_mem_pair_of_map_eq hXm hmap] with ω hmem
  rcases hmem with h | h <;> rw [h, Real.norm_eq_abs]
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- A random variable with a two-point law is in every `L^p`
(it is a.e. bounded).

**Lean implementation helper.** -/
lemma memLp_of_map_eq {X : Ω → ℝ} {x y : ℝ} {p₀ : I} [IsProbabilityMeasure μ]
    (hXm : AEMeasurable X μ) (hmap : μ.map X = bernoulliMeasure x y p₀)
    (q : ℝ≥0∞) : MemLp X q μ := by
  refine (memLp_top_of_bound hXm.aestronglyMeasurable (max |x| |y|) ?_).mono_exponent
    le_top
  filter_upwards [ae_mem_pair_of_map_eq hXm hmap] with ω hmem
  rcases hmem with h | h <;> rw [h, Real.norm_eq_abs]
  · exact le_max_left _ _
  · exact le_max_right _ _

namespace IsRademacher

variable {X : Ω → ℝ}

/-- Transfer of expectations of functions of a Rademacher random variable:
`𝔼 f(X) = (f(1) + f(−1))/2`.

**Lean implementation helper.** -/
lemma integral_comp (h : IsRademacher X μ) (f : ℝ → ℝ) :
    ∫ ω, f (X ω) ∂μ = (f 1 + f (-1)) / 2 := by
  have hmeas : AEStronglyMeasurable f (μ.map X) := by
    rw [h.map_eq]; exact aestronglyMeasurable_bernoulliMeasure f _ _ _
  rw [← integral_map h.aemeasurable hmeas, h.map_eq, integral_bernoulliMeasure]
  change (1 / 2 : ℝ) • f 1 + (1 - (1 / 2 : ℝ)) • f (-1) = _
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- A measure supporting a Rademacher random variable has total mass one.

**Lean implementation helper.** -/
lemma isProbabilityMeasure (h : IsRademacher X μ) : IsProbabilityMeasure μ := by
  constructor
  have h1 : (μ.map X) Set.univ = 1 := by rw [h.map_eq]; exact measure_univ
  rwa [Measure.map_apply_of_aemeasurable h.aemeasurable MeasurableSet.univ,
    Set.preimage_univ] at h1

/-- A Rademacher random variable has zero mean (the source §2.2, §2.7, implicit).

**Book Section 2.2.** -/
lemma integral_eq_zero (h : IsRademacher X μ) : ∫ ω, X ω ∂μ = 0 := by
  have := h.integral_comp id
  simpa using this

/-- MGF of a Rademacher random variable: `𝔼 exp(λX) = cosh λ`
(the source, proof of Theorem 2.2.1, unnumbered display).

**Book Theorem 2.2.1.** -/
lemma mgf_eq_cosh (h : IsRademacher X μ) (t : ℝ) : mgf X μ t = Real.cosh t := by
  rw [mgf, Real.cosh_eq]
  have := h.integral_comp (fun x => Real.exp (t * x))
  simp only [mul_one, mul_neg] at this
  exact this

/-- A Rademacher random variable takes values in `{−1, 1}` a.e.

**Lean implementation helper.** -/
lemma ae_mem (h : IsRademacher X μ) : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1 :=
  ae_mem_pair_of_map_eq h.aemeasurable h.map_eq

/-- A Rademacher random variable is in every `L^p`.

**Lean implementation helper.** -/
lemma memLp (h : IsRademacher X μ) (q : ℝ≥0∞) : MemLp X q μ := by
  have := h.isProbabilityMeasure
  exact memLp_of_map_eq h.aemeasurable h.map_eq q

/-- Any composition `f(X)` of a Rademacher random variable is integrable.

**Lean implementation helper.** -/
lemma integrable_comp (h : IsRademacher X μ) (f : ℝ → ℝ) :
    Integrable (fun ω => f (X ω)) μ := by
  have := h.isProbabilityMeasure
  exact integrable_comp_of_map_eq h.aemeasurable h.map_eq (by norm_num) f

/-- Atom bound for the Rademacher distribution: `ℙ{X = u} ≤ 1/2` for every fixed `u`
(the source, implicit claim inside the proof of Example 1.5.1).

**Book Example 1.5.1.** -/
lemma real_atom_le_half (h : IsRademacher X μ) (u : ℝ) :
    μ.real {ω | X ω = u} ≤ 1 / 2 := by
  classical
  have hpre : μ.real {ω | X ω = u} = (μ.map X).real {u} := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable h.aemeasurable (measurableSet_singleton u)]
    rfl
  rw [hpre, h.map_eq, bernoulliMeasure_real_apply _ (measurableSet_singleton u)]
  split_ifs with h1 h2 h2
  · exfalso
    rw [Set.mem_singleton_iff] at h1 h2
    have h12 : (1 : ℝ) = -1 := h1.trans h2.symm
    norm_num at h12
  · exact le_of_eq
      (show ((unitInterval.toNNReal ⟨1/2, by norm_num, by norm_num⟩ : ℝ≥0) : ℝ) = 1/2
        from rfl)
  · have hσ : ((unitInterval.toNNReal (σ ⟨1/2, by norm_num, by norm_num⟩) : ℝ≥0) : ℝ)
        = 1 - 1/2 := rfl
    rw [hσ]; norm_num
  · norm_num

end IsRademacher

namespace IsBernoulli

variable {X : Ω → ℝ} {p : I}

/-- Transfer of expectations of functions of a Bernoulli random variable:
`𝔼 f(X) = p·f(1) + (1−p)·f(0)`.

**Lean implementation helper.** -/
lemma integral_comp (h : IsBernoulli X p μ) (f : ℝ → ℝ) :
    ∫ ω, f (X ω) ∂μ = p * f 1 + (1 - p) * f 0 := by
  have hmeas : AEStronglyMeasurable f (μ.map X) := by
    rw [h.map_eq]; exact aestronglyMeasurable_bernoulliMeasure f _ _ _
  rw [← integral_map h.aemeasurable hmeas, h.map_eq, integral_bernoulliMeasure]
  simp [smul_eq_mul]

/-- A measure supporting a Bernoulli random variable has total mass one.

**Lean implementation helper.** -/
lemma isProbabilityMeasure (h : IsBernoulli X p μ) : IsProbabilityMeasure μ := by
  constructor
  have h1 : (μ.map X) Set.univ = 1 := by rw [h.map_eq]; exact measure_univ
  rwa [Measure.map_apply_of_aemeasurable h.aemeasurable MeasurableSet.univ,
    Set.preimage_univ] at h1

/-- A Bernoulli random variable takes values in `{0, 1}` a.e.

**Lean implementation helper.** -/
lemma ae_mem (h : IsBernoulli X p μ) : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = 0 :=
  ae_mem_pair_of_map_eq h.aemeasurable h.map_eq

/-- A Bernoulli random variable is in every `L^p`.

**Lean implementation helper.** -/
lemma memLp (h : IsBernoulli X p μ) (q : ℝ≥0∞) : MemLp X q μ := by
  have := h.isProbabilityMeasure
  exact memLp_of_map_eq h.aemeasurable h.map_eq q

/-- Any composition `f(X)` of a Bernoulli random variable is integrable.

**Lean implementation helper.** -/
lemma integrable_comp (h : IsBernoulli X p μ) (f : ℝ → ℝ) :
    Integrable (fun ω => f (X ω)) μ := by
  have := h.isProbabilityMeasure
  exact integrable_comp_of_map_eq h.aemeasurable h.map_eq (by norm_num) f

/-- `𝔼X = p` for `X ∼ Ber(p)` (the source Example 1.7.4, "one can easily check").

**Book Example 1.7.4.** -/
lemma integral_eq (h : IsBernoulli X p μ) : ∫ ω, X ω ∂μ = p := by
  have := h.integral_comp id
  simpa using this

/-- `𝔼X² = p` for `X ∼ Ber(p)`.

**Lean implementation helper.** -/
lemma integral_sq_eq (h : IsBernoulli X p μ) : ∫ ω, (X ω) ^ 2 ∂μ = p := by
  have := h.integral_comp (fun x => x ^ 2)
  simpa using this

/-- MGF of `Ber(p)`: `𝔼 exp(λX) = 1 + (e^λ − 1)p` (the source, proof of Theorem 2.3.1,
unnumbered display).

**Book Theorem 2.3.1.** -/
lemma mgf_eq (h : IsBernoulli X p μ) (t : ℝ) :
    mgf X μ t = 1 + (Real.exp t - 1) * p := by
  rw [mgf]
  have := h.integral_comp (fun x => Real.exp (t * x))
  simp only [mul_one, mul_zero, Real.exp_zero] at this
  rw [this]
  ring

end IsBernoulli

/-! ## Variance: Chapter 0 prerequisite -/

/-- Scalar case), recovered Chapter 0 prerequisite used at the source (2.23):
`𝔼(X−a)² = Var(X) + (a−𝔼X)²`; in particular the mean minimizes the mean squared
deviation. tex`, hint 0.2.

**Book Exercise 0.2.** -/
lemma integral_sq_sub_eq_variance_add {X : Ω → ℝ} [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) (a : ℝ) :
    ∫ ω, (X ω - a) ^ 2 ∂μ = Var[X; μ] + (a - ∫ ω, X ω ∂μ) ^ 2 := by
  have hXint : Integrable X μ := hX.integrable one_le_two
  have hX2 : Integrable (fun ω => (X ω) ^ 2) μ := hX.integrable_sq
  have hvar : Var[X; μ] = (∫ ω, (X ω) ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 := by
    simpa using variance_eq_sub hX
  have hsub : Integrable (fun ω => (X ω) ^ 2 - 2 * a * X ω) μ :=
    hX2.sub (hXint.const_mul (2 * a))
  rw [hvar]
  calc ∫ ω, (X ω - a) ^ 2 ∂μ
      = ∫ ω, ((X ω) ^ 2 - 2 * a * X ω + a ^ 2) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    _ = (∫ ω, ((X ω) ^ 2 - 2 * a * X ω) ∂μ) + a ^ 2 := by
        rw [integral_add hsub (integrable_const _)]
        simp
    _ = (∫ ω, (X ω) ^ 2 ∂μ) - 2 * a * ∫ ω, X ω ∂μ + a ^ 2 := by
        rw [integral_sub hX2 (hXint.const_mul (2 * a)), integral_const_mul]
    _ = (∫ ω, (X ω) ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 + (a - ∫ ω, X ω ∂μ) ^ 2 := by ring

/-- Centering minimizes the second moment: `Var(X) = 𝔼(X−𝔼X)² ≤ 𝔼(X−a)²` for every `a`
(consequence of the source Exercise 0.2, used at the source (2.23) with `a = 0`).

**Book Exercise 0.2.** -/
lemma variance_le_integral_sq_sub {X : Ω → ℝ} [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) (a : ℝ) :
    Var[X; μ] ≤ ∫ ω, (X ω - a) ^ 2 ∂μ := by
  rw [integral_sq_sub_eq_variance_add hX a]
  nlinarith [sq_nonneg (a - ∫ ω, X ω ∂μ)]

/-! ## Numeric inequalities -/

/-- Bounds `one_sub_mul_exp` above by `one`.

**Lean implementation helper.** -/
private lemma one_sub_mul_exp_le_one (t : ℝ) : (1 - t) * Real.exp t ≤ 1 := by
  have h := Real.add_one_le_exp (-t)
  have hmul : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

/-- For nonnegative `x`, the exponential satisfies
`exp x ≤ 1 + x + x ^ 2 / 2 * exp x`.

**Lean implementation helper.** -/
private lemma exp_taylor_bound_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp x := by
  set g : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 * Real.exp t - Real.exp t with hg
  have hderiv : ∀ t : ℝ,
      HasDerivAt g (1 + (t * Real.exp t + t ^ 2 / 2 * Real.exp t) - Real.exp t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have := (hasDerivAt_pow 2 t).div_const 2
      simpa [pow_one] using this
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * Real.exp s)
        (t * Real.exp t + t ^ 2 / 2 * Real.exp t) t :=
      h1.mul (Real.hasDerivAt_exp t)
    have h3 : HasDerivAt (fun s : ℝ => 1 + s) 1 t :=
      (hasDerivAt_id t).const_add (1 : ℝ)
    exact (h3.add h2).sub (Real.hasDerivAt_exp t)
  have hmono : MonotoneOn g (Set.Ici (0:ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t _ => ((hderiv t).continuousAt).continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hderiv t).deriv]
      have h1 := one_sub_mul_exp_le_one t
      nlinarith [Real.exp_pos t, sq_nonneg t]
  have h0 : g 0 = 0 := by simp [hg]
  have hgle : g 0 ≤ g x := hmono Set.self_mem_Ici hx hx
  rw [h0] at hgle
  simp only [hg] at hgle
  linarith

/-- For a nonpositive real input, the exponential is bounded by its quadratic Taylor polynomial.

**Lean implementation helper.** -/
private lemma exp_taylor_bound_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  set g : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 - Real.exp t with hg
  have hderiv : ∀ t : ℝ, HasDerivAt g (1 + t - Real.exp t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have := (hasDerivAt_pow 2 t).div_const 2
      simpa [pow_one] using this
    have h3 : HasDerivAt (fun s : ℝ => 1 + s) 1 t :=
      (hasDerivAt_id t).const_add (1 : ℝ)
    exact (h3.add h1).sub (Real.hasDerivAt_exp t)
  have hanti : AntitoneOn g (Set.Iic (0:ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic 0) ?_ ?_ ?_
    · exact fun t _ => ((hderiv t).continuousAt).continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hderiv t).deriv]
      have := Real.add_one_le_exp t
      linarith
  have h0 : g 0 = 0 := by simp [hg]
  have hgle : g 0 ≤ g x := hanti hx Set.self_mem_Iic hx
  rw [h0] at hgle
  simp only [hg] at hgle
  linarith

/-- Numeric inequality `e^x ≤ 1 + x + (x²/2)e^{|x|}` (Taylor's theorem with the Lagrange
form of the remainder), used in the proofs of the source Propositions 2.6.1 (iii)⇒(iv) and
2.8.1 (iii)⇒(iv). Implicit source claim (stated in both proofs).

**Book Chapter 1.** -/
lemma exp_le_one_add_add_sq_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact exp_taylor_bound_nonneg hx
  · rw [abs_of_neg hx]
    have h1 := exp_taylor_bound_nonpos hx.le
    have h2 : (1 : ℝ) ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith [sq_nonneg x]

end HDP
