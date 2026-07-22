import HighDimensionalProbability.Appendix.Infra.Herbst
import Mathlib.Analysis.Convex.Integral
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Entropy tensorization for finite product measures

This file develops the finite-product entropy inequality used in the
Talagrand convex-concentration argument.  The local cost is the scalar
relative-entropy integrand

`a * log (a / b) + b - a`.

Its joint convexity is the log-sum inequality.  Tensorization with a
coordinate-invariant comparison density then follows by induction over the
coordinates.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Appendix

noncomputable section

/-- Scalar relative-entropy integrand.  In the positive quadrant this is the
perspective of `InformationTheory.klFun`. -/
def scalarRelEntropy (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + b - a

@[simp]
lemma scalarRelEntropy_self {a : ℝ} (ha : 0 < a) :
    scalarRelEntropy a a = 0 := by
  simp [scalarRelEntropy, ha.ne']

lemma scalarRelEntropy_eq_mul_klFun {a b : ℝ} (hb : 0 < b) :
    scalarRelEntropy a b =
      b * InformationTheory.klFun (a / b) := by
  rw [scalarRelEntropy, InformationTheory.klFun]
  by_cases ha : a = 0
  · simp [ha]
  rw [Real.log_div ha hb.ne']
  field_simp [hb.ne']

lemma scalarRelEntropy_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ scalarRelEntropy a b := by
  rw [scalarRelEntropy_eq_mul_klFun hb]
  exact mul_nonneg hb.le
    (InformationTheory.klFun_nonneg (div_nonneg ha hb.le))

/-- The open positive quadrant on which the scalar relative-entropy
integrand is represented by a genuine perspective. -/
def positiveQuadrant : Set (ℝ × ℝ) :=
  Set.Ioi 0 ×ˢ Set.Ioi 0

lemma convexOn_scalarRelEntropy :
    ConvexOn ℝ positiveQuadrant
      (fun p : ℝ × ℝ => scalarRelEntropy p.1 p.2) := by
  refine ⟨(convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ)), ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩ u v hu hv huv
  simp only [Prod.smul_mk, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  have hB : 0 < u * b + v * d := by
    rcases hu.eq_or_lt with rfl | hu'
    · have : v = 1 := by linarith
      simpa [this] using hd
    · exact add_pos_of_pos_of_nonneg (mul_pos hu' hb)
        (mul_nonneg hv hd.le)
  have hb0 : b ≠ 0 := hb.ne'
  have hd0 : d ≠ 0 := hd.ne'
  let θ : ℝ := u * b / (u * b + v * d)
  let η : ℝ := v * d / (u * b + v * d)
  have hθ : 0 ≤ θ := div_nonneg (mul_nonneg hu hb.le) hB.le
  have hη : 0 ≤ η := div_nonneg (mul_nonneg hv hd.le) hB.le
  have hθη : θ + η = 1 := by
    dsimp [θ, η]
    rw [← add_div]
    exact div_self hB.ne'
  have hratio :
      (u * a + v * c) / (u * b + v * d) =
        θ * (a / b) + η * (c / d) := by
    dsimp [θ, η]
    field_simp [hb0, hd0, hB.ne']
  have hab : a / b ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ a / b
    exact div_nonneg ha.le hb.le
  have hcd : c / d ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ c / d
    exact div_nonneg hc.le hd.le
  have hconv :
      InformationTheory.klFun
          (θ * (a / b) + η * (c / d)) ≤
        θ * InformationTheory.klFun (a / b) +
          η * InformationTheory.klFun (c / d) := by
    simpa only [smul_eq_mul] using
      InformationTheory.convexOn_klFun.2 hab hcd hθ hη hθη
  rw [← hratio] at hconv
  rw [scalarRelEntropy_eq_mul_klFun hB,
    scalarRelEntropy_eq_mul_klFun hb,
    scalarRelEntropy_eq_mul_klFun hd]
  calc
    (u * b + v * d) *
          InformationTheory.klFun ((u * a + v * c) / (u * b + v * d))
        ≤ (u * b + v * d) *
          (θ * InformationTheory.klFun (a / b) +
            η * InformationTheory.klFun (c / d)) :=
      mul_le_mul_of_nonneg_left hconv hB.le
    _ = u * (b * InformationTheory.klFun (a / b)) +
        v * (d * InformationTheory.klFun (c / d)) := by
      dsimp [θ, η]
      field_simp [hB.ne']

/-- A closed positive quadrant, used to invoke the Bochner-integral form of
Jensen's inequality. -/
def quadrantAbove (δ : ℝ) : Set (ℝ × ℝ) :=
  Set.Ici δ ×ˢ Set.Ici δ

lemma quadrantAbove_subset_positiveQuadrant {δ : ℝ} (hδ : 0 < δ) :
    quadrantAbove δ ⊆ positiveQuadrant := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact ⟨hδ.trans_le ha, hδ.trans_le hb⟩

lemma convexOn_scalarRelEntropy_quadrantAbove {δ : ℝ} (hδ : 0 < δ) :
    ConvexOn ℝ (quadrantAbove δ)
      (fun p : ℝ × ℝ => scalarRelEntropy p.1 p.2) :=
  convexOn_scalarRelEntropy.subset
    (quadrantAbove_subset_positiveQuadrant hδ)
    ((convex_Ici δ).prod (convex_Ici δ))

lemma continuousOn_scalarRelEntropy_quadrantAbove {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun p : ℝ × ℝ => scalarRelEntropy p.1 p.2)
      (quadrantAbove δ) := by
  intro p hp
  have hp' := quadrantAbove_subset_positiveQuadrant hδ hp
  have hp1 : p.1 ≠ 0 := ne_of_gt hp'.1
  have hp2 : p.2 ≠ 0 := ne_of_gt hp'.2
  have hdiv : ContinuousAt (fun q : ℝ × ℝ => q.1 / q.2) p :=
    continuousAt_fst.div continuousAt_snd hp2
  have hlog : ContinuousAt
      (fun q : ℝ × ℝ => Real.log (q.1 / q.2)) p :=
    (continuousAt_log (div_ne_zero hp1 hp2)).tendsto.comp hdiv
  unfold scalarRelEntropy
  exact (((continuousAt_fst.mul hlog).add continuousAt_snd).sub
    continuousAt_fst).continuousWithinAt

/-- Integral log-sum inequality.  This is Jensen's inequality for the jointly
convex scalar relative-entropy integrand. -/
lemma scalarRelEntropy_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hab : ∀ᵐ x ∂μ, δ ≤ a x ∧ δ ≤ b x)
    (hint : Integrable (fun x => (a x, b x)) μ)
    (hcost : Integrable
      (fun x => scalarRelEntropy (a x) (b x)) μ) :
    scalarRelEntropy (∫ x, a x ∂μ) (∫ x, b x ∂μ) ≤
      ∫ x, scalarRelEntropy (a x) (b x) ∂μ := by
  have hmem :
      ∀ᵐ x ∂μ, (a x, b x) ∈ quadrantAbove δ := hab
  have hjensen :=
    (convexOn_scalarRelEntropy_quadrantAbove hδ).map_integral_le
      (continuousOn_scalarRelEntropy_quadrantAbove hδ)
      ((isClosed_Ici.prod isClosed_Ici))
      hmem hint (by
        change Integrable (fun x => scalarRelEntropy (a x) (b x)) μ
        exact hcost)
  rw [integral_pair hint.fst hint.snd] at hjensen
  exact hjensen

/-- Exact variational decomposition of entropy against a positive constant
comparison density. -/
lemma integral_scalarRelEntropy_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (b : ℝ)
    (hfpos : ∀ x, 0 < f x) (hb : 0 < b)
    (hf : Integrable f μ)
    (hflog : Integrable (fun x => f x * Real.log (f x)) μ) :
    (∫ x, scalarRelEntropy (f x) b ∂μ) =
      boltzmannEntropy μ f +
        scalarRelEntropy (∫ x, f x ∂μ) b := by
  have hfb : Integrable (fun x => f x * Real.log b) μ :=
    hf.mul_const _
  have hconst : Integrable (fun _x : Ω => b) μ := integrable_const _
  have hpoint (x : Ω) :
      scalarRelEntropy (f x) b =
        f x * Real.log (f x) - f x * Real.log b + b - f x := by
    rw [scalarRelEntropy, Real.log_div (hfpos x).ne' hb.ne']
    ring
  simp_rw [hpoint]
  have hmean_pos : 0 < ∫ x, f x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg
      (fun x => (hfpos x).le) hf]
    have hsupp : Function.support f = Set.univ := by
      ext x
      simp [Function.mem_support, (hfpos x).ne']
    rw [hsupp]
    simp
  calc
    (∫ x, f x * Real.log (f x) - f x * Real.log b + b - f x ∂μ) =
        (∫ x, f x * Real.log (f x) - f x * Real.log b + b ∂μ) -
          ∫ x, f x ∂μ :=
      integral_sub ((hflog.sub hfb).add hconst) hf
    _ = ((∫ x, f x * Real.log (f x) ∂μ) -
          ∫ x, f x * Real.log b ∂μ) + b -
          ∫ x, f x ∂μ := by
      congr 1
      calc
        (∫ x, f x * Real.log (f x) - f x * Real.log b + b ∂μ) =
            (∫ x, f x * Real.log (f x) - f x * Real.log b ∂μ) +
              ∫ _x : Ω, b ∂μ := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_add (hflog.sub hfb) hconst
        _ = ((∫ x, f x * Real.log (f x) ∂μ) -
              ∫ x, f x * Real.log b ∂μ) + b := by
          rw [integral_sub hflog hfb, integral_const]
          simp
    _ = boltzmannEntropy μ f +
        scalarRelEntropy (∫ x, f x ∂μ) b := by
      rw [integral_mul_const, boltzmannEntropy, scalarRelEntropy,
        Real.log_div hmean_pos.ne' hb.ne']
      ring

/-- The one-coordinate variational entropy bound. -/
lemma boltzmannEntropy_le_integral_scalarRelEntropy_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (b : ℝ)
    (hfpos : ∀ x, 0 < f x) (hb : 0 < b)
    (hf : Integrable f μ)
    (hflog : Integrable (fun x => f x * Real.log (f x)) μ) :
    boltzmannEntropy μ f ≤
      ∫ x, scalarRelEntropy (f x) b ∂μ := by
  rw [integral_scalarRelEntropy_const μ f b hfpos hb hf hflog]
  exact le_add_of_nonneg_right
    (scalarRelEntropy_nonneg
      (integral_nonneg fun x => (hfpos x).le) hb)

/-- Entropy chain rule for a product measure, in the analytic regime needed
below. -/
lemma boltzmannEntropy_prod_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : A × B → ℝ)
    (hF : Integrable F (μ.prod ν))
    (hFlog : Integrable
      (fun p => F p * Real.log (F p)) (μ.prod ν))
    (hhlog : Integrable
      (fun y =>
        (∫ x, F (x, y) ∂μ) *
          Real.log (∫ x, F (x, y) ∂μ)) ν) :
    boltzmannEntropy (μ.prod ν) F =
      (∫ y, boltzmannEntropy μ (fun x => F (x, y)) ∂ν) +
        boltzmannEntropy ν (fun y => ∫ x, F (x, y) ∂μ) := by
  let h : B → ℝ := fun y => ∫ x, F (x, y) ∂μ
  have hh : Integrable h ν := hF.integral_prod_right
  have hinnerlog : Integrable
      (fun y => ∫ x, F (x, y) * Real.log (F (x, y)) ∂μ) ν :=
    hFlog.integral_prod_right
  rw [boltzmannEntropy, boltzmannEntropy]
  simp_rw [boltzmannEntropy]
  rw [integral_sub hinnerlog hhlog,
    integral_prod_symm F hF,
    integral_prod_symm (fun p => F p * Real.log (F p)) hFlog]
  ring

/-- Uniform positive upper and lower bounds. -/
def HasUniformPositiveBounds {Ω : Type*}
    (δ M : ℝ) (f : Ω → ℝ) : Prop :=
  ∀ x, δ ≤ f x ∧ f x ≤ M

lemma HasUniformPositiveBounds.pos
    {Ω : Type*} {δ M : ℝ} {f : Ω → ℝ}
    (hδ : 0 < δ) (h : HasUniformPositiveBounds δ M f) (x : Ω) :
    0 < f x :=
  hδ.trans_le (h x).1

lemma HasUniformPositiveBounds.integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {δ M : ℝ} {f : Ω → ℝ}
    (hδ : 0 < δ) (hf : Measurable f)
    (h : HasUniformPositiveBounds δ M f) :
    Integrable f μ := by
  have hM : 0 ≤ M := by
    letI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    exact (hδ.trans_le (h Classical.ofNonempty).1).le.trans
      (h Classical.ofNonempty).2
  apply Integrable.of_bound hf.aestronglyMeasurable M
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hδ.trans_le (h x).1).le]
    exact (h x).2

lemma HasUniformPositiveBounds.log_abs_le
    {Ω : Type*} {δ M : ℝ} {f : Ω → ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (h : HasUniformPositiveBounds δ M f) (x : Ω) :
    |Real.log (f x)| ≤ max |Real.log δ| |Real.log M| := by
  have hfx : 0 < f x := hδ.trans_le (h x).1
  have hM : 0 < M := hδ.trans_le hδM
  exact abs_le_max_abs_abs
    (Real.log_le_log hδ (h x).1)
    (Real.log_le_log hfx (h x).2)

lemma HasUniformPositiveBounds.integrable_mul_log
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {δ M : ℝ} {f : Ω → ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hf : Measurable f) (h : HasUniformPositiveBounds δ M f) :
    Integrable (fun x => f x * Real.log (f x)) μ := by
  let C := M * max |Real.log δ| |Real.log M|
  have hM : 0 ≤ M := (hδ.trans_le hδM).le
  have hC : 0 ≤ C :=
    mul_nonneg hM (le_max_of_le_left (abs_nonneg _))
  apply Integrable.of_bound (hf.mul hf.log).aestronglyMeasurable C
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hδ.trans_le (h x).1).le]
    exact mul_le_mul (h x).2
      (h.log_abs_le hδ hδM x)
      (abs_nonneg _) hM

/-- Integrability of the scalar log-sum cost under common positive bounds. -/
lemma integrable_scalarRelEntropy_of_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {δ M : ℝ} {a b : Ω → ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (ha : Measurable a) (hb : Measurable b)
    (haB : HasUniformPositiveBounds δ M a)
    (hbB : HasUniformPositiveBounds δ M b) :
    Integrable (fun x => scalarRelEntropy (a x) (b x)) μ := by
  have haInt := haB.integrable (μ := μ) hδ ha
  have hbInt := hbB.integrable (μ := μ) hδ hb
  have haloga := haB.integrable_mul_log (μ := μ) hδ hδM ha
  have halogb : Integrable (fun x => a x * Real.log (b x)) μ := by
    apply Integrable.of_bound (ha.mul hb.log).aestronglyMeasurable
      (M * max |Real.log δ| |Real.log M|)
    exact ae_of_all μ fun x => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hδ.trans_le (haB x).1).le]
      exact mul_le_mul (haB x).2
        (hbB.log_abs_le hδ hδM x)
        (abs_nonneg _) (hδ.trans_le hδM).le
  have hdecomp :
      (fun x => scalarRelEntropy (a x) (b x)) =
        (fun x => a x * Real.log (a x)) -
          (fun x => a x * Real.log (b x)) + b - a := by
    funext x
    rw [scalarRelEntropy,
      Real.log_div (haB.pos hδ x).ne' (hbB.pos hδ x).ne']
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hdecomp]
  exact ((haloga.sub halogb).add hbInt).sub haInt

/-- Positive uniform bounds are preserved by averaging one coordinate of a
probability product. -/
lemma HasUniformPositiveBounds.integral_prod_left
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    {δ M : ℝ} {F : A × B → ℝ}
    (hδ : 0 < δ) (hF : Measurable F)
    (hB : HasUniformPositiveBounds δ M F) :
    HasUniformPositiveBounds δ M
      (fun y => ∫ x, F (x, y) ∂μ) := by
  intro y
  have hfy : Measurable (fun x => F (x, y)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hfyB : HasUniformPositiveBounds δ M (fun x => F (x, y)) :=
    fun x => hB (x, y)
  have hfyInt : Integrable (fun x => F (x, y)) μ :=
    hfyB.integrable (μ := μ) hδ hfy
  constructor
  · calc
      δ = ∫ _x : A, δ ∂μ := by simp
      _ ≤ ∫ x, F (x, y) ∂μ :=
        integral_mono (integrable_const _) hfyInt
          (fun x => (hB (x, y)).1)
  · calc
      (∫ x, F (x, y) ∂μ) ≤ ∫ _x : A, M ∂μ :=
        integral_mono hfyInt (integrable_const _)
          (fun x => (hB (x, y)).2)
      _ = M := by simp

/-- Measurability of a one-coordinate average. -/
lemma measurable_integral_prod_left
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ]
    {F : A × B → ℝ} (hF : Measurable F) :
    Measurable (fun y => ∫ x, F (x, y) ∂μ) :=
  hF.stronglyMeasurable.integral_prod_left'.measurable

/-- Entropy tensorization for a finite product probability measure.

Each comparison density `c i` may depend on all coordinates except its own
coordinate `i`.  The right-hand side is the sum of the corresponding scalar
relative-entropy costs. -/
theorem boltzmannEntropy_pi_le_sum_scalarRelEntropy
    {N : ℕ} {X : Fin N → Type*}
    [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, X i) → ℝ)
    (c : Fin N → (∀ i, X i) → ℝ)
    {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hf : Measurable f) (hc : ∀ i, Measurable (c i))
    (hfB : HasUniformPositiveBounds δ M f)
    (hcB : ∀ i, HasUniformPositiveBounds δ M (c i))
    (hc_invariant :
      ∀ i x y, (∀ j, j ≠ i → x j = y j) → c i x = c i y) :
    boltzmannEntropy (Measure.pi μ) f ≤
      ∫ x, ∑ i, scalarRelEntropy (f x) (c i x) ∂(Measure.pi μ) := by
  induction N with
  | zero =>
      let z : ∀ i : Fin 0, X i := fun i => Fin.elim0 i
      have hfconst : f = fun _ => f z := by
        funext x
        congr
        funext i
        exact Fin.elim0 i
      rw [hfconst]
      simp [boltzmannEntropy]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove X (0 : Fin (n + 1))
      let ν : Measure (∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) :=
        Measure.pi (fun j => μ ((0 : Fin (n + 1)).succAbove j))
      let F : X 0 × (∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
        fun p => f (e.symm p)
      have hF : Measurable F := hf.comp e.symm.measurable
      have hFB : HasUniformPositiveBounds δ M F :=
        fun p => hfB (e.symm p)
      have hFint : Integrable F ((μ 0).prod ν) :=
        hFB.integrable hδ hF
      have hFlog : Integrable
          (fun p => F p * Real.log (F p)) ((μ 0).prod ν) :=
        hFB.integrable_mul_log hδ hδM hF
      let g : (∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
        fun y => ∫ x, F (x, y) ∂(μ 0)
      have hg : Measurable g :=
        measurable_integral_prod_left (μ 0) hF
      have hgB : HasUniformPositiveBounds δ M g :=
        hFB.integral_prod_left (μ 0) hδ hF
      have hgint : Integrable g ν :=
        hgB.integrable hδ hg
      have hglog : Integrable (fun y => g y * Real.log (g y)) ν :=
        hgB.integrable_mul_log hδ hδM hg
      have hchain :
          boltzmannEntropy ((μ 0).prod ν) F =
            (∫ y, boltzmannEntropy (μ 0) (fun x => F (x, y)) ∂ν) +
              boltzmannEntropy ν g := by
        exact boltzmannEntropy_prod_eq (μ 0) ν F hFint hFlog hglog
      letI : Nonempty (X 0) := nonempty_of_isProbabilityMeasure (μ 0)
      let x₀ : X 0 := Classical.ofNonempty
      let b : (∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
        fun y => c 0 (e.symm (x₀, y))
      have hb : Measurable b := by
        exact (hc 0).comp
          (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
      have hbB : HasUniformPositiveBounds δ M b :=
        fun y => hcB 0 (e.symm (x₀, y))
      have e_symm_zero (x : X 0) (y : ∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) :
          e.symm (x, y) 0 = x := by
        change (Fin.insertNth 0 x y) 0 = x
        simp
      have e_symm_succ (x : X 0) (y : ∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) (k : Fin n) :
          e.symm (x, y) ((0 : Fin (n + 1)).succAbove k) = y k := by
        change (Fin.insertNth 0 x y)
          ((0 : Fin (n + 1)).succAbove k) = y k
        exact Fin.insertNth_apply_succAbove 0 x y k
      have hc_zero_eq_b (x : X 0) (y : ∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) :
          c 0 (e.symm (x, y)) = b y := by
        apply hc_invariant 0 (e.symm (x, y)) (e.symm (x₀, y))
        intro j hj
        obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        exact (e_symm_succ x y k).trans (e_symm_succ x₀ y k).symm
      have hlocal (y : ∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) :
          boltzmannEntropy (μ 0) (fun x => F (x, y)) ≤
            ∫ x, scalarRelEntropy (F (x, y))
              (c 0 (e.symm (x, y))) ∂(μ 0) := by
        have hFy : Measurable (fun x => F (x, y)) :=
          hF.comp (measurable_id.prodMk measurable_const)
        have hFyB : HasUniformPositiveBounds δ M (fun x => F (x, y)) :=
          fun x => hFB (x, y)
        have hbase :=
          boltzmannEntropy_le_integral_scalarRelEntropy_const
            (μ 0) (fun x => F (x, y)) (b y)
            (fun x => hFyB.pos hδ x) (hbB.pos hδ y)
            (hFyB.integrable hδ hFy)
            (hFyB.integrable_mul_log hδ hδM hFy)
        calc
          boltzmannEntropy (μ 0) (fun x => F (x, y)) ≤
              ∫ x, scalarRelEntropy (F (x, y)) (b y) ∂(μ 0) :=
            hbase
          _ = ∫ x, scalarRelEntropy (F (x, y))
                (c 0 (e.symm (x, y))) ∂(μ 0) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hc_zero_eq_b x y]
      let cTail (i : Fin n) :
          X 0 × (∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
        fun p => c ((0 : Fin (n + 1)).succAbove i) (e.symm p)
      have hcTail (i : Fin n) : Measurable (cTail i) :=
        (hc ((0 : Fin (n + 1)).succAbove i)).comp e.symm.measurable
      have hcTailB (i : Fin n) :
          HasUniformPositiveBounds δ M (cTail i) :=
        fun p => hcB ((0 : Fin (n + 1)).succAbove i) (e.symm p)
      let d (i : Fin n) :
          (∀ j : Fin n, X ((0 : Fin (n + 1)).succAbove j)) → ℝ :=
        fun y => ∫ x, cTail i (x, y) ∂(μ 0)
      have hd (i : Fin n) : Measurable (d i) :=
        measurable_integral_prod_left (μ 0) (hcTail i)
      have hdB (i : Fin n) :
          HasUniformPositiveBounds δ M (d i) :=
        (hcTailB i).integral_prod_left (μ 0) hδ (hcTail i)
      have hd_invariant :
          ∀ i y z, (∀ j, j ≠ i → y j = z j) → d i y = d i z := by
        intro i y z hyz
        apply integral_congr_ae
        filter_upwards with x
        apply hc_invariant ((0 : Fin (n + 1)).succAbove i)
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          exact (e_symm_zero x y).trans (e_symm_zero x z).symm
        · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          change e.symm (x, y) ((0 : Fin (n + 1)).succAbove k) =
            e.symm (x, z) ((0 : Fin (n + 1)).succAbove k)
          rw [e_symm_succ, e_symm_succ]
          apply hyz
          intro hki
          subst k
          exact hj rfl
      have houter :
          boltzmannEntropy ν g ≤
            ∫ y, ∑ i, scalarRelEntropy (g y) (d i y) ∂ν := by
        exact ih (μ := fun i => μ ((0 : Fin (n + 1)).succAbove i))
          (f := g) (c := d) hg hd hgB hdB hd_invariant
      have hlogsum (i : Fin n) (y : ∀ j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) :
          scalarRelEntropy (g y) (d i y) ≤
            ∫ x, scalarRelEntropy (F (x, y)) (cTail i (x, y))
              ∂(μ 0) := by
        have hFy : Measurable (fun x => F (x, y)) :=
          hF.comp (measurable_id.prodMk measurable_const)
        have hCy : Measurable (fun x => cTail i (x, y)) :=
          (hcTail i).comp (measurable_id.prodMk measurable_const)
        have hFyB :
            HasUniformPositiveBounds δ M (fun x => F (x, y)) :=
          fun x => hFB (x, y)
        have hCyB :
            HasUniformPositiveBounds δ M (fun x => cTail i (x, y)) :=
          fun x => hcTailB i (x, y)
        have hpair : Integrable
            (fun x => (F (x, y), cTail i (x, y))) (μ 0) :=
          (hFyB.integrable hδ hFy).prodMk
            (hCyB.integrable hδ hCy)
        have hcost : Integrable
            (fun x => scalarRelEntropy (F (x, y)) (cTail i (x, y)))
              (μ 0) :=
          integrable_scalarRelEntropy_of_bounds hδ hδM
            hFy hCy hFyB hCyB
        exact scalarRelEntropy_integral_le (μ 0)
          (fun x => F (x, y)) (fun x => cTail i (x, y)) hδ
          (ae_of_all _ fun x => ⟨(hFyB x).1, (hCyB x).1⟩)
          hpair hcost
      have hlocalInt : Integrable
          (fun y => boltzmannEntropy (μ 0) (fun x => F (x, y))) ν := by
        simp only [boltzmannEntropy]
        exact hFlog.integral_prod_right.sub hglog
      have hcZeroPair : Measurable
          (fun p : X 0 × (∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) =>
              c 0 (e.symm p)) :=
        (hc 0).comp e.symm.measurable
      have hcZeroPairB : HasUniformPositiveBounds δ M
          (fun p : X 0 × (∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) =>
              c 0 (e.symm p)) :=
        fun p => hcB 0 (e.symm p)
      have hcostZeroProd : Integrable
          (fun p : X 0 × (∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) =>
              scalarRelEntropy (F p) (c 0 (e.symm p)))
          ((μ 0).prod ν) :=
        integrable_scalarRelEntropy_of_bounds hδ hδM hF
          hcZeroPair hFB hcZeroPairB
      have hcostZeroInner : Integrable
          (fun y => ∫ x, scalarRelEntropy (F (x, y))
            (c 0 (e.symm (x, y))) ∂(μ 0)) ν :=
        hcostZeroProd.integral_prod_right
      have hlocalIntegrated :
          (∫ y, boltzmannEntropy (μ 0) (fun x => F (x, y)) ∂ν) ≤
            ∫ y, ∫ x, scalarRelEntropy (F (x, y))
              (c 0 (e.symm (x, y))) ∂(μ 0) ∂ν :=
        integral_mono hlocalInt hcostZeroInner hlocal
      have hcostOuter (i : Fin n) : Integrable
          (fun y => scalarRelEntropy (g y) (d i y)) ν :=
        integrable_scalarRelEntropy_of_bounds hδ hδM hg (hd i)
          hgB (hdB i)
      have hcostOuterSum : Integrable
          (fun y => ∑ i, scalarRelEntropy (g y) (d i y)) ν := by
        simpa only using
          (integrable_finsetSum Finset.univ
            (fun i _hi => hcostOuter i))
      have hcostTailProd (i : Fin n) : Integrable
          (fun p : X 0 × (∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) =>
              scalarRelEntropy (F p) (cTail i p))
          ((μ 0).prod ν) :=
        integrable_scalarRelEntropy_of_bounds hδ hδM hF
          (hcTail i) hFB (hcTailB i)
      have hcostTailSection (i : Fin n)
          (y : ∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) :
          Integrable
            (fun x => scalarRelEntropy (F (x, y)) (cTail i (x, y)))
            (μ 0) := by
        exact integrable_scalarRelEntropy_of_bounds hδ hδM
          (hF.comp (measurable_id.prodMk measurable_const))
          ((hcTail i).comp (measurable_id.prodMk measurable_const))
          (fun x => hFB (x, y)) (fun x => hcTailB i (x, y))
      have hcostTailSumProd : Integrable
          (fun p : X 0 × (∀ j : Fin n,
            X ((0 : Fin (n + 1)).succAbove j)) =>
              ∑ i, scalarRelEntropy (F p) (cTail i p))
          ((μ 0).prod ν) := by
        simpa only using
          (integrable_finsetSum Finset.univ
            (fun i _hi => hcostTailProd i))
      have hcostTailSumInner : Integrable
          (fun y => ∫ x, ∑ i,
            scalarRelEntropy (F (x, y)) (cTail i (x, y))
              ∂(μ 0)) ν :=
        hcostTailSumProd.integral_prod_right
      have htailIntegrated :
          (∫ y, ∑ i, scalarRelEntropy (g y) (d i y) ∂ν) ≤
            ∫ y, ∫ x, ∑ i,
              scalarRelEntropy (F (x, y)) (cTail i (x, y))
                ∂(μ 0) ∂ν := by
        apply integral_mono hcostOuterSum hcostTailSumInner
        intro y
        calc
          (∑ i, scalarRelEntropy (g y) (d i y)) ≤
              ∑ i, ∫ x, scalarRelEntropy (F (x, y))
                (cTail i (x, y)) ∂(μ 0) :=
            Finset.sum_le_sum fun i _hi => hlogsum i y
          _ = ∫ x, ∑ i, scalarRelEntropy (F (x, y))
                (cTail i (x, y)) ∂(μ 0) := by
            rw [integral_finsetSum]
            intro i hi
            exact hcostTailSection i y
      have hprodPair :
          boltzmannEntropy ((μ 0).prod ν) F ≤
            ∫ p, ∑ i : Fin (n + 1),
              scalarRelEntropy (F p) (c i (e.symm p))
                ∂((μ 0).prod ν) := by
        rw [hchain]
        calc
          (∫ y, boltzmannEntropy (μ 0) (fun x => F (x, y)) ∂ν) +
                boltzmannEntropy ν g ≤
              (∫ y, boltzmannEntropy (μ 0) (fun x => F (x, y)) ∂ν) +
                ∫ y, ∑ i, scalarRelEntropy (g y) (d i y) ∂ν :=
            add_le_add_right houter _
          _ ≤
              (∫ y, ∫ x, scalarRelEntropy (F (x, y))
                    (c 0 (e.symm (x, y))) ∂(μ 0) ∂ν) +
                ∫ y, ∫ x, ∑ i,
                    scalarRelEntropy (F (x, y)) (cTail i (x, y))
                  ∂(μ 0) ∂ν :=
            add_le_add hlocalIntegrated htailIntegrated
          _ = (∫ p, scalarRelEntropy (F p) (c 0 (e.symm p))
                  ∂((μ 0).prod ν)) +
                ∫ p, ∑ i, scalarRelEntropy (F p) (cTail i p)
                  ∂((μ 0).prod ν) := by
            rw [integral_prod_symm
              (fun p => scalarRelEntropy (F p) (c 0 (e.symm p)))
              hcostZeroProd,
              integral_prod_symm
                (fun p => ∑ i, scalarRelEntropy (F p) (cTail i p))
                hcostTailSumProd]
          _ = ∫ p, (scalarRelEntropy (F p) (c 0 (e.symm p)) +
                ∑ i, scalarRelEntropy (F p) (cTail i p))
                  ∂((μ 0).prod ν) := by
            rw [integral_add hcostZeroProd hcostTailSumProd]
          _ = ∫ p, ∑ i : Fin (n + 1),
                scalarRelEntropy (F p) (c i (e.symm p))
                  ∂((μ 0).prod ν) := by
            apply integral_congr_ae
            filter_upwards with p
            rw [Fin.sum_univ_succ]
            rfl
      have mp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod ν) := by
        exact measurePreserving_piFinSuccAbove μ 0
      have hmeanTransfer :
          (∫ p, F p ∂((μ 0).prod ν)) =
            ∫ x, f x ∂(Measure.pi μ) := by
        rw [← mp.integral_comp' F]
        apply integral_congr_ae
        filter_upwards with x
        change f (e.symm (e x)) = f x
        rw [e.symm_apply_apply]
      have hmulLogTransfer :
          (∫ p, F p * Real.log (F p) ∂((μ 0).prod ν)) =
            ∫ x, f x * Real.log (f x) ∂(Measure.pi μ) := by
        rw [← mp.integral_comp'
          (fun p => F p * Real.log (F p))]
        apply integral_congr_ae
        filter_upwards with x
        change f (e.symm (e x)) * Real.log (f (e.symm (e x))) =
          f x * Real.log (f x)
        rw [e.symm_apply_apply]
      have hentropyTransfer :
          boltzmannEntropy (Measure.pi μ) f =
            boltzmannEntropy ((μ 0).prod ν) F := by
        unfold boltzmannEntropy
        rw [hmeanTransfer, hmulLogTransfer]
      have hcostTransfer :
          (∫ p, ∑ i : Fin (n + 1),
              scalarRelEntropy (F p) (c i (e.symm p))
                ∂((μ 0).prod ν)) =
            ∫ x, ∑ i : Fin (n + 1),
              scalarRelEntropy (f x) (c i x) ∂(Measure.pi μ) := by
        rw [← mp.integral_comp'
          (fun p => ∑ i : Fin (n + 1),
            scalarRelEntropy (F p) (c i (e.symm p)))]
        apply integral_congr_ae
        filter_upwards with x
        change (∑ i : Fin (n + 1),
            scalarRelEntropy (f (e.symm (e x))) (c i (e.symm (e x)))) =
          ∑ i : Fin (n + 1), scalarRelEntropy (f x) (c i x)
        rw [e.symm_apply_apply]
      rw [hentropyTransfer, ← hcostTransfer]
      exact hprodPair

end

end HDP.Appendix
