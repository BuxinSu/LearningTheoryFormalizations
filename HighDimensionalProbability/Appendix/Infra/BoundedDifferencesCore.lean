import HighDimensionalProbability.Appendix.Infra.Concentration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.SubGaussian

/-!
# Infrastructure for bounded differences

The local lemma below is the sharp form of Hoeffding's lemma needed in the
McDiarmid argument: a measurable function whose range has diameter at most
`c` has centered sub-Gaussian MGF parameter `c^2 / 4`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter5.Appendix

noncomputable section

/-- The NNReal parameter corresponding to an oscillation bound `c`. -/
def oscillationParameter (c : Real) : ℝ≥0 :=
  Real.toNNReal (c ^ 2 / 4)

@[simp]
lemma coe_oscillationParameter {c : Real} (_hc : 0 <= c) :
    (oscillationParameter c : Real) = c ^ 2 / 4 := by
  rw [oscillationParameter, Real.coe_toNNReal]
  positivity

/-- Sharp Hoeffding lemma stated using a pairwise oscillation bound rather
than preselected interval endpoints. -/
lemma hasSubgaussianMGF_of_pairwise_abs_sub_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (g : Omega -> Real) (hg : Measurable g) (c : Real) (hc : 0 <= c)
    (hosc : forall x y, |g x - g y| <= c) :
    HasSubgaussianMGF (fun x => g x - ∫ y, g y ∂mu)
      (oscillationParameter c) mu := by
  letI : Nonempty Omega := nonempty_of_isProbabilityMeasure mu
  let S : Set Real := Set.range g
  have hS_nonempty : S.Nonempty := Set.range_nonempty g
  have hS_bddAbove : BddAbove S := by
    refine ⟨g Classical.ofNonempty + c, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h := hosc x Classical.ofNonempty
    have h' : g x - g Classical.ofNonempty <= c :=
      (le_abs_self _).trans h
    linarith
  have hS_bddBelow : BddBelow S := by
    refine ⟨g Classical.ofNonempty - c, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h := hosc x Classical.ofNonempty
    have h' : g Classical.ofNonempty - g x <= c :=
      (le_abs_self (g Classical.ofNonempty - g x)).trans
        (by simpa [abs_sub_comm] using h)
    linarith
  have hmem : forall x, g x ∈ Set.Icc (sInf S) (sSup S) := by
    intro x
    exact ⟨csInf_le hS_bddBelow ⟨x, rfl⟩,
      le_csSup hS_bddAbove ⟨x, rfl⟩⟩
  have hwidth : sSup S - sInf S <= c := by
    have hsup : sSup S <= sInf S + c := by
      apply csSup_le hS_nonempty
      rintro _ ⟨x, rfl⟩
      have hlower : g x - c <= sInf S := by
        apply le_csInf hS_nonempty
        rintro _ ⟨y, rfl⟩
        have h := hosc x y
        have hxy : g x - g y <= c := (le_abs_self _).trans h
        linarith
      linarith
    linarith
  have hwidth_nonneg : 0 <= sSup S - sInf S :=
    sub_nonneg.mpr (csInf_le_csSup hS_nonempty hS_bddBelow hS_bddAbove)
  have hbase := hasSubgaussianMGF_of_mem_Icc
    (μ := mu) (X := g) hg.aemeasurable
    (ae_of_all mu fun x => hmem x)
  refine ⟨hbase.integrable_exp_mul, fun t => (hbase.mgf_le t).trans ?_⟩
  rw [coe_oscillationParameter hc]
  apply Real.exp_le_exp.mpr
  rw [Real.nnnorm_of_nonneg hwidth_nonneg]
  push_cast
  have hsq : (sSup S - sInf S) ^ 2 <= c ^ 2 :=
    (sq_le_sq₀ hwidth_nonneg hc).2 hwidth
  have hsqt := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
  nlinarith

/-- Tensorization step for a product: a uniformly sub-Gaussian centered
fiber, followed by a sub-Gaussian fiber mean, has the sum of the two MGF
parameters.  This is the analytic induction step in McDiarmid's theorem and
does not require regular conditional probabilities. -/
lemma hasSubgaussianMGF_prod_of_fiberwise
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (F : A × B -> Real) (hF : Measurable F) (hFint : Integrable F (mu.prod nu))
    (c d : ℝ≥0)
    (hlocal : forall y,
      HasSubgaussianMGF
        (fun x => F (x, y) - ∫ z, F (z, y) ∂mu) c mu)
    (houter : HasSubgaussianMGF
      (fun y => (∫ x, F (x, y) ∂mu) -
        ∫ z, (∫ x, F (x, z) ∂mu) ∂nu) d nu) :
    HasSubgaussianMGF
      (fun p => F p - ∫ q, F q ∂(mu.prod nu)) (c + d) (mu.prod nu) := by
  let g : B -> Real := fun y => ∫ x, F (x, y) ∂mu
  have hg_meas : Measurable g :=
    hF.stronglyMeasurable.integral_prod_left'.measurable
  have hmean : ∫ q, F q ∂(mu.prod nu) = ∫ y, g y ∂nu :=
    integral_prod_symm F hFint
  have hdecomp (p : A × B) :
      F p - ∫ q, F q ∂(mu.prod nu) =
        (F p - g p.2) + (g p.2 - ∫ y, g y ∂nu) := by
    rw [hmean]
    ring
  have hJointIntegrable (t : Real) : Integrable
      (fun p : A × B => Real.exp
        (t * (F p - ∫ q, F q ∂(mu.prod nu)))) (mu.prod nu) := by
    have hmeas : AEStronglyMeasurable
        (fun p : A × B => Real.exp
          (t * (F p - ∫ q, F q ∂(mu.prod nu)))) (mu.prod nu) := by
      simpa [mul_comm] using
        ((hF.sub_const _).mul_const t |>.exp.aestronglyMeasurable)
    rw [integrable_prod_iff' hmeas]
    constructor
    · exact ae_of_all nu fun y => by
        convert ((hlocal y).integrable_exp_mul t).mul_const
          (Real.exp (t * (g y - ∫ z, g z ∂nu))) using 1
        ext x
        rw [hdecomp (x, y), mul_add, Real.exp_add]
    · have hdomInt : Integrable
          (fun y => Real.exp ((c : Real) * t ^ 2 / 2) *
            Real.exp (t * (g y - ∫ z, g z ∂nu))) nu :=
        (houter.integrable_exp_mul t).const_mul _
      refine hdomInt.mono' ?_ ?_
      · have hp : StronglyMeasurable (fun p : A × B =>
            ‖Real.exp (t * (F p - ∫ q, F q ∂(mu.prod nu)))‖) :=
          (show Measurable (fun p : A × B =>
            ‖Real.exp (t * (F p - ∫ q, F q ∂(mu.prod nu)))‖) by fun_prop).stronglyMeasurable
        exact hp.integral_prod_left'.aestronglyMeasurable
      · filter_upwards with y
        simp only [Real.norm_eq_abs, abs_exp]
        have hnonneg : 0 <= ∫ x, Real.exp
            (t * (F (x, y) - ∫ q, F q ∂(mu.prod nu))) ∂mu :=
          integral_nonneg fun _ => Real.exp_nonneg _
        rw [abs_of_nonneg hnonneg]
        calc
          ∫ x, Real.exp
                (t * (F (x, y) - ∫ q, F q ∂(mu.prod nu))) ∂mu
              = Real.exp (t * (g y - ∫ z, g z ∂nu)) *
                  ∫ x, Real.exp (t * (F (x, y) - g y)) ∂mu := by
                    rw [← integral_const_mul]
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [hdecomp (x, y), mul_add, Real.exp_add, mul_comm]
          _ <= Real.exp (t * (g y - ∫ z, g z ∂nu)) *
                Real.exp ((c : Real) * t ^ 2 / 2) := by
                  gcongr
                  simpa [mgf, g] using (hlocal y).mgf_le t
          _ = Real.exp ((c : Real) * t ^ 2 / 2) *
                Real.exp (t * (g y - ∫ z, g z ∂nu)) := mul_comm _ _
  refine ⟨hJointIntegrable, ?_⟩
  intro t
  rw [mgf, integral_prod_symm _ (hJointIntegrable t)]
  simp_rw [hmean]
  calc
      ∫ y, ∫ x, Real.exp
            (t * (F (x, y) - ∫ z, g z ∂nu)) ∂mu ∂nu
          = ∫ y, Real.exp (t * (g y - ∫ z, g z ∂nu)) *
              (∫ x, Real.exp (t * (F (x, y) - g y)) ∂mu) ∂nu := by
                apply integral_congr_ae
                filter_upwards with y
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards with x
                rw [← Real.exp_add]
                congr 1
                ring
      _ <= ∫ y, Real.exp (t * (g y - ∫ z, g z ∂nu)) *
              Real.exp ((c : Real) * t ^ 2 / 2) ∂nu := by
                apply integral_mono_of_nonneg
                · exact ae_of_all _ fun y =>
                    mul_nonneg (Real.exp_nonneg _)
                      (integral_nonneg fun _ => Real.exp_nonneg _)
                · exact (houter.integrable_exp_mul t).mul_const _
                · filter_upwards with y
                  gcongr
                  simpa [mgf, g] using (hlocal y).mgf_le t
      _ = Real.exp ((c : Real) * t ^ 2 / 2) *
            mgf (fun y => g y - ∫ z, g z ∂nu) nu t := by
              rw [mgf, integral_mul_const]
              ring
      _ <= Real.exp ((c : Real) * t ^ 2 / 2) *
            Real.exp ((d : Real) * t ^ 2 / 2) := by
              gcongr
              simpa [g] using houter.mgf_le t
      _ = Real.exp (((c + d : ℝ≥0) : Real) * t ^ 2 / 2) := by
              rw [← Real.exp_add]
              push_cast
              ring_nf

/-- Integrating preserves a pointwise oscillation bound, including the
degenerate case where both Bochner integrals use Mathlib's nonintegrable
default value. -/
lemma abs_integral_sub_integral_le_of_abs_sub_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (u v : Omega -> Real) (hu : Measurable u) (hv : Measurable v)
    (c : Real) (hc : 0 <= c) (h : forall x, |u x - v x| <= c) :
    |(∫ x, u x ∂mu) - ∫ x, v x ∂mu| <= c := by
  have hdiff : Integrable (fun x => u x - v x) mu :=
    Integrable.of_bound (hu.sub hv).aestronglyMeasurable c
      (ae_of_all mu fun x => by simpa [Real.norm_eq_abs] using h x)
  by_cases hui : Integrable u mu
  · have hvi : Integrable v mu := by
      have heq : v = u - (fun x => u x - v x) := by
        funext x
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      exact hui.sub hdiff
    rw [← integral_sub hui hvi]
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const
        (μ := mu) (f := fun x => u x - v x)
        (ae_of_all mu fun x => by simpa [Real.norm_eq_abs] using h x))
  · have hvi : ¬ Integrable v mu := by
      intro hvi
      apply hui
      have heq : u = v + (fun x => u x - v x) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact hvi.add hdiff
    simp [integral_undef hui, integral_undef hvi, hc]

/-- Sum of the sharp one-coordinate Hoeffding parameters. -/
def boundedDifferencesParameter {N : Nat} (c : Fin N -> Real) : ℝ≥0 :=
  ∑ i, oscillationParameter (c i)

/-- MGF form of McDiarmid's bounded-differences inequality. -/
lemma boundedDifferences_hasSubgaussianMGF {N : Nat}
    {X : Fin N -> Type*} [forall i, MeasurableSpace (X i)]
    (mu : forall i, Measure (X i)) [forall i, IsProbabilityMeasure (mu i)]
    (f : (forall i, X i) -> Real) (c : Fin N -> Real)
    (hf : Measurable f) (hc : forall i, 0 <= c i)
    (hbounded : forall x y i,
      (forall j, j ≠ i -> x j = y j) -> |f x - f y| <= c i)
    (hfint : Integrable f (Measure.pi mu)) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂(Measure.pi mu))
      (boundedDifferencesParameter c) (Measure.pi mu) := by
  induction N with
  | zero =>
      let z : forall i : Fin 0, X i := fun i => Fin.elim0 i
      have hconst : forall x, f x = f z := fun x => by
        congr
        funext i
        exact Fin.elim0 i
      have hmean : ∫ x, f x ∂(Measure.pi mu) = f z := by
        calc
          ∫ x, f x ∂(Measure.pi mu) = ∫ _x, f z ∂(Measure.pi mu) :=
            integral_congr_ae (ae_of_all _ hconst)
          _ = f z := by simp
      have hcenter : (fun x => f x - ∫ y, f y ∂(Measure.pi mu)) =
          (fun _ => 0) := by
        funext x
        rw [hmean, hconst x]
        ring
      rw [hcenter]
      simpa [boundedDifferencesParameter] using
        (HasSubgaussianMGF.fun_zero (μ := Measure.pi mu))
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove X (0 : Fin (n + 1))
      let nu : Measure (forall j : Fin n, X ((0 : Fin (n + 1)).succAbove j)) :=
        Measure.pi (fun j => mu ((0 : Fin (n + 1)).succAbove j))
      let F : X 0 × (forall j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) -> Real :=
        fun p => f (e.symm p)
      have hF : Measurable F := hf.comp e.symm.measurable
      have mp := measurePreserving_piFinSuccAbove mu (0 : Fin (n + 1))
      have hFint : Integrable F ((mu 0).prod nu) := by
        exact mp.symm.integrable_comp_of_integrable hfint
      let g : (forall j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) -> Real :=
        fun y => ∫ x, F (x, y) ∂(mu 0)
      have hg : Measurable g :=
        hF.stronglyMeasurable.integral_prod_left'.measurable
      have hgint : Integrable g nu := hFint.integral_prod_right
      have e_symm_zero (x : X 0) (y : forall j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) : e.symm (x, y) 0 = x := by
        change (Fin.insertNth 0 x y) 0 = x
        simp
      have e_symm_succ (x : X 0) (y : forall j : Fin n,
          X ((0 : Fin (n + 1)).succAbove j)) (k : Fin n) :
          e.symm (x, y) ((0 : Fin (n + 1)).succAbove k) = y k := by
        change (Fin.insertNth 0 x y) ((0 : Fin (n + 1)).succAbove k) = y k
        exact Fin.insertNth_apply_succAbove 0 x y k
      have hlocal : forall y,
          HasSubgaussianMGF
            (fun x => F (x, y) - ∫ z, F (z, y) ∂(mu 0))
            (oscillationParameter (c 0)) (mu 0) := by
        intro y
        apply hasSubgaussianMGF_of_pairwise_abs_sub_le
          (mu 0) (fun x => F (x, y))
          (hF.comp (measurable_id.prodMk measurable_const)) (c 0) (hc 0)
        intro x x'
        apply hbounded (e.symm (x, y)) (e.symm (x', y)) 0
        intro j hj
        obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        simpa using (e_symm_succ x y k).trans (e_symm_succ x' y k).symm
      have hg_bounded : forall y z (i : Fin n),
          (forall j, j ≠ i -> y j = z j) ->
            |g y - g z| <= c ((0 : Fin (n + 1)).succAbove i) := by
        intro y z i hyz
        apply abs_integral_sub_integral_le_of_abs_sub_le
          (mu 0) (fun x => F (x, y)) (fun x => F (x, z))
          (hF.comp (measurable_id.prodMk measurable_const))
          (hF.comp (measurable_id.prodMk measurable_const))
          (c ((0 : Fin (n + 1)).succAbove i))
          (hc ((0 : Fin (n + 1)).succAbove i))
        intro x
        apply hbounded (e.symm (x, y)) (e.symm (x, z))
          ((0 : Fin (n + 1)).succAbove i)
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          exact (e_symm_zero x y).trans (e_symm_zero x z).symm
        · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          have hki : k ≠ i := by
            intro hki
            apply hj
            simp [hki]
          exact (e_symm_succ x y k).trans <|
            (hyz k hki).trans (e_symm_succ x z k).symm
      have houter : HasSubgaussianMGF
          (fun y => g y - ∫ z, g z ∂nu)
          (boundedDifferencesParameter (fun i : Fin n =>
            c ((0 : Fin (n + 1)).succAbove i))) nu := by
        exact ih (mu := fun i => mu ((0 : Fin (n + 1)).succAbove i)) (f := g)
          (c := fun i => c ((0 : Fin (n + 1)).succAbove i)) hg
          (fun i => hc ((0 : Fin (n + 1)).succAbove i)) hg_bounded hgint
      have hpair := hasSubgaussianMGF_prod_of_fiberwise
        (mu 0) nu F hF hFint
        (oscillationParameter (c 0))
        (boundedDifferencesParameter (fun i : Fin n =>
          c ((0 : Fin (n + 1)).succAbove i)))
        hlocal houter
      have hpair_map : HasSubgaussianMGF
          (fun p => F p - ∫ q, F q ∂((mu 0).prod nu))
          (oscillationParameter (c 0) +
            boundedDifferencesParameter (fun i : Fin n =>
              c ((0 : Fin (n + 1)).succAbove i)))
          ((Measure.pi mu).map e) := by
        rw [mp.map_eq]
        exact hpair
      have hback := HasSubgaussianMGF.of_map
        e.measurable.aemeasurable hpair_map
      have hmean_pair : ∫ q, F q ∂((mu 0).prod nu) =
          ∫ x, f x ∂(Measure.pi mu) := by
        rw [← mp.integral_comp' F]
        apply integral_congr_ae
        filter_upwards with x
        exact congrArg f (e.symm_apply_apply x)
      have hcenter := hback.congr (ae_of_all (Measure.pi mu) fun x => by
        simp only [Function.comp_apply, hmean_pair, F]
        exact congrArg (fun z => f z - ∫ y, f y ∂(Measure.pi mu))
          (e.symm_apply_apply x))
      simpa [Function.comp_def, F, e,
        boundedDifferencesParameter, Fin.sum_univ_succ,
        Fin.zero_succAbove] using hcenter

end

end HDP.Chapter5.Appendix
