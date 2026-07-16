import MatrixConcentration.Appendix_SymmetricLowerBound
import MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Appendix: Matrix Rosenthal inequality

This module proves **Book equation (5.1.9)** through the following components.

This appendix contains:

* independent-copy symmetrization for random matrices;
* Rademacher sign-law and signed-sum estimates;
* deterministic norm and variance comparisons;
* the complete auxiliary proof of the matrix Rosenthal inequality.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.9: Matrix Rosenthal inequality

This section supplies the symmetrization and Rademacher estimates behind the
matrix Rosenthal inequality. For positive-semidefinite summands, the
square-function statistic of a fixed realization is bounded by the product
of its largest summand and its total sum.  Combining this fact with the
one-sided Hermitian Rademacher estimate gives a coefficient `8 * log d`,
which is slightly stronger than the Book's `8 * e * log d` coefficient.

**Author note.** The auxiliary argument retains the Book's coefficient in its
conclusion even though its final scalar estimate first proves the stronger
coefficient `8 * log d`.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset Function
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

section SumExpectationHelper

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ}
variable {A : Matrix n n ℂ}

/-- **Book §5.1**, implicit prerequisite of its standing hypotheses: a Hermitian
matrix with `0 ≤ λ_min` is positive semidefinite (the book treats
`0 ≤ λ_min(X_k)` and positive semidefiniteness interchangeably, §5.1). -/
lemma posSemidef_of_lambdaMin_nonneg [Nonempty n] (hA : A.IsHermitian)
    (h : 0 ≤ lambdaMin hA) : A.PosSemidef := by
  refine hA.posSemidef_iff_eigenvalues_nonneg.mpr fun i => ?_
  exact h.trans (lambdaMin_le_eigenvalues hA i)

/-- **Book (5.1.2)/(5.1.3)** (first identity): `𝔼Y = Σ_k 𝔼X_k` — linearity of the
expectation across the sum.  Implicit source declaration. -/
lemma expectation_matsum_eq (hint : ∀ k, MIntegrable (X k) μ) :
    expectation μ (fun ω => ∑ k, X k ω) = ∑ k, expectation μ (X k) := by
  ext i j
  rw [expectation_apply, Matrix.sum_apply]
  have h1 : (fun ω => ∑ k, X k ω i j) = fun ω => ∑ k, (fun ω' => X k ω' i j) ω := by
    funext ω
    rfl
  have h2 : ∫ ω, (∑ k, X k ω) i j ∂μ = ∫ ω, ∑ k, X k ω i j ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (∑ k, X k ω) i j = ∑ k, X k ω i j
    rw [Matrix.sum_apply]
  rw [h2, MeasureTheory.integral_finset_sum _ fun k _ => hint k i j]
  exact Finset.sum_congr rfl fun k _ => (expectation_apply _ _ _).symm

/-- Lean implementation helper: the Hermitian certificate for `Σ_k 𝔼X_k`. -/
lemma isHermitian_sum_expectation (hherm : ∀ k ω, (X k ω).IsHermitian) :
    (∑ k, expectation μ (X k)).IsHermitian :=
  isHermitian_matsum Finset.univ fun k =>
    isHermitian_expectation (Filter.Eventually.of_forall (hherm k))

end SumExpectationHelper

noncomputable section

section HermitianFacts

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: Subadditivity of the top eigenvalue on Hermitian matrices. -/
lemma lambdaMax_add_le {A B : Matrix n n Complex} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    lambdaMax (hA.add hB) ≤ lambdaMax hA + lambdaMax hB := by
  refine lambdaMax_le_of_forall_rayleigh (hA.add hB) fun u hu => ?_
  have hsplit : rayleigh (A + B) u = rayleigh A u + rayleigh B u := by
    simp only [rayleigh, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  rw [hsplit]
  exact add_le_add (rayleigh_le_lambdaMax_of_unit hA hu)
    (rayleigh_le_lambdaMax_of_unit hB hu)

end HermitianFacts

section GhostSymmetrization

variable {Omega n : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: One-sided symmetrization against an independent ghost copy. -/
lemma lambdaMax_symmetrization_ghost
    {Y : Omega → Matrix n n Complex}
    (hYmeas : Measurable Y) (hYherm : ∀ omega, (Y omega).IsHermitian)
    (hYint : MIntegrable Y mu)
    (hnorm : Integrable (fun omega => ‖Y omega‖) mu)
    (hlam : Integrable (fun omega => lambdaMax (hYherm omega)) mu) :
    (∫ omega, lambdaMax (hYherm omega) ∂mu) ≤
      lambdaMax (isHermitian_expectation (μ := mu)
        (Filter.Eventually.of_forall hYherm)) +
      ∫ p : Omega × Omega,
        lambdaMax ((hYherm p.1).sub (hYherm p.2)) ∂(mu.prod mu) := by
  let hEY : (expectation mu Y).IsHermitian :=
    isHermitian_expectation (μ := mu) (Filter.Eventually.of_forall hYherm)
  let C : Omega → Matrix n n Complex := fun omega => Y omega - expectation mu Y
  have hCmeas : Measurable C := hYmeas.sub measurable_const
  have hCherm : ∀ omega, (C omega).IsHermitian := fun omega =>
    (hYherm omega).sub hEY
  have hCnorm : Integrable (fun omega => ‖C omega‖) mu := by
    refine Integrable.mono' (hnorm.add (integrable_const ‖expectation mu Y‖))
      (continuous_l2_opNorm.measurable.comp hCmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_sub_le _ _
  have hClam : Integrable (fun omega => lambdaMax (hCherm omega)) mu := by
    refine Integrable.mono' hCnorm
      (measurable_lambdaMax_of_forall hCmeas hCherm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs]
    exact abs_lambdaMax_le (hCherm omega)
  let D : Omega × Omega → Matrix n n Complex := fun p => Y p.1 - Y p.2
  have hDmeas : Measurable D :=
    (hYmeas.comp measurable_fst).sub (hYmeas.comp measurable_snd)
  have hDherm : ∀ p, (D p).IsHermitian := fun p =>
    (hYherm p.1).sub (hYherm p.2)
  have hDnorm : Integrable (fun p : Omega × Omega => ‖D p‖) (mu.prod mu) := by
    refine Integrable.mono' ((hnorm.comp_fst mu).add (hnorm.comp_snd mu))
      (continuous_l2_opNorm.measurable.comp hDmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_sub_le _ _
  have hDlam : Integrable (fun p : Omega × Omega => lambdaMax (hDherm p))
      (mu.prod mu) := by
    refine Integrable.mono' hDnorm
      (measurable_lambdaMax_of_forall hDmeas hDherm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact abs_lambdaMax_le (hDherm p)
  have hpoint_add : ∀ omega, lambdaMax (hYherm omega) ≤
      lambdaMax hEY + lambdaMax (hCherm omega) := by
    intro omega
    have hdecomp : expectation mu Y + C omega = Y omega := by
      simp only [C]
      abel
    have h := lambdaMax_add_le hEY (hCherm omega)
    rwa [lambdaMax_congr hdecomp (hEY.add (hCherm omega)) (hYherm omega)] at h
  have hghost_point : ∀ omega, lambdaMax (hCherm omega) ≤
      ∫ omega', lambdaMax ((hYherm omega).sub (hYherm omega')) ∂mu := by
    intro omega
    let V : Omega → Matrix n n Complex := fun omega' => Y omega - Y omega'
    have hVint : MIntegrable V mu := (MIntegrable.const (Y omega)).sub hYint
    have hVherm : ∀ omega', (V omega').IsHermitian := fun omega' =>
      (hYherm omega).sub (hYherm omega')
    have hEV : expectation mu V = C omega := by
      rw [show V = fun omega' => Y omega - Y omega' from rfl,
        expectation_sub (MIntegrable.const _) hYint, expectation_const]
    have hEVherm : (expectation mu V).IsHermitian :=
      isHermitian_expectation (Filter.Eventually.of_forall hVherm)
    have hVlam : Integrable (fun omega' => lambdaMax (hVherm omega')) mu := by
      have hslice : Integrable (fun omega' => ‖V omega'‖) mu := by
        refine Integrable.mono' ((integrable_const ‖Y omega‖).add hnorm)
          ((continuous_l2_opNorm.measurable.comp
            (measurable_const.sub hYmeas)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun omega' => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_sub_le _ _
      refine Integrable.mono' hslice
        (measurable_lambdaMax_of_forall
          (measurable_const.sub hYmeas) hVherm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun omega' => ?_)
      rw [Real.norm_eq_abs]
      exact abs_lambdaMax_le (hVherm omega')
    have hj := lambdaMax_expectation_le hVint hVherm hEVherm hVlam
    have hc : lambdaMax hEVherm = lambdaMax (hCherm omega) :=
      lambdaMax_congr hEV hEVherm (hCherm omega)
    rw [hc] at hj
    exact hj
  have h1 : (∫ omega, lambdaMax (hYherm omega) ∂mu) ≤
      ∫ omega, (lambdaMax hEY + lambdaMax (hCherm omega)) ∂mu :=
    integral_mono hlam ((integrable_const _).add hClam) hpoint_add
  have h2 : (∫ omega, lambdaMax (hCherm omega) ∂mu) ≤
      ∫ omega, (∫ omega', lambdaMax ((hYherm omega).sub (hYherm omega')) ∂mu) ∂mu :=
    integral_mono hClam hDlam.integral_prod_left hghost_point
  calc
    (∫ omega, lambdaMax (hYherm omega) ∂mu)
        ≤ ∫ omega, (lambdaMax hEY + lambdaMax (hCherm omega)) ∂mu := h1
    _ = lambdaMax hEY + ∫ omega, lambdaMax (hCherm omega) ∂mu := by
      rw [integral_add (integrable_const _) hClam, integral_const,
        probReal_univ, one_smul]
    _ ≤ lambdaMax hEY +
        ∫ omega, (∫ omega', lambdaMax ((hYherm omega).sub (hYherm omega')) ∂mu) ∂mu :=
      add_le_add (le_refl _) h2
    _ = lambdaMax hEY +
        ∫ p : Omega × Omega, lambdaMax ((hYherm p.1).sub (hYherm p.2))
          ∂(mu.prod mu) := by
      rw [MeasureTheory.integral_prod _ hDlam]

end GhostSymmetrization
section Signs

variable {I n : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: A globally measurable top-eigenvalue functional, obtained by projecting an
arbitrary matrix to its Hermitian part.  On Hermitian inputs this is `lambdaMax`. -/
def topHerm (A : Matrix n n ℂ) : ℝ := lambdaMax (isHermitian_hermPart A)

/-- Lean implementation helper: measurability of `topHerm`. -/
lemma measurable_topHerm : Measurable (topHerm : Matrix n n ℂ → ℝ) := by
  exact measurable_lambdaMax_of_forall continuous_hermPart.measurable
    isHermitian_hermPart

/-- Lean implementation helper: on Hermitian matrices, `topHerm` is the top eigenvalue. -/
lemma topHerm_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    topHerm A = lambdaMax hA := by
  exact lambdaMax_congr (hermPart_of_isHermitian hA) (isHermitian_hermPart A) hA

/-- Lean implementation helper: the absolute value of `topHerm` is bounded by operator norm. -/
lemma abs_topHerm_le_norm (A : Matrix n n ℂ) : |topHerm A| ≤ ‖A‖ := by
  exact (abs_lambdaMax_le (isHermitian_hermPart A)).trans (norm_hermPart_le A)

/-- Lean implementation helper: subadditivity of `topHerm`. -/
lemma topHerm_add_le (A B : Matrix n n ℂ) :
    topHerm (A + B) ≤ topHerm A + topHerm B := by
  have hadd : hermPart (A + B) = hermPart A + hermPart B := map_add _ _ _
  have h := lambdaMax_add_le (isHermitian_hermPart A) (isHermitian_hermPart B)
  exact (lambdaMax_congr hadd (isHermitian_hermPart (A + B))
    ((isHermitian_hermPart A).add (isHermitian_hermPart B))).le.trans h

/-- Lean implementation helper: `false` represents `+1` and `true` represents `-1`. -/
def boolSign (b : Bool) : ℝ := if b then -1 else 1

/-- Lean implementation helper: the Boolean value `false` encodes the sign `+1`. -/
@[simp] lemma boolSign_false : boolSign false = 1 := rfl
/-- Lean implementation helper: the Boolean value `true` encodes the sign `-1`. -/
@[simp] lemma boolSign_true : boolSign true = -1 := rfl
/-- Lean implementation helper: Boolean negation reverses the encoded sign. -/
@[simp] lemma boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> simp [boolSign]

/-- Lean implementation helper: every encoded Boolean sign has absolute value one. -/
lemma abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> simp [boolSign]

/-- Lean implementation helper: the matrix sum associated with a Boolean sign pattern. -/
def signSum (b : I → Bool) (x : I → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, boolSign (b k) • x k

/-- Lean implementation helper: measurability of a fixed signed-sum map. -/
lemma measurable_signSum (b : I → Bool) : Measurable (signSum (n := n) b) := by
  exact measurable_matsum Finset.univ fun k =>
    (measurable_pi_apply k).const_smul (boolSign (b k))

/-- Lean implementation helper: triangle-inequality bound for a Boolean signed sum. -/
lemma norm_signSum_le (b : I → Bool) (x : I → Matrix n n ℂ) :
    ‖signSum b x‖ ≤ ∑ k, ‖x k‖ := by
  calc
    ‖signSum b x‖ ≤ ∑ k, ‖boolSign (b k) • x k‖ := norm_sum_le _ _
    _ = ∑ k, ‖x k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_smul, Real.norm_eq_abs, abs_boolSign, one_mul]

/-- Lean implementation helper: measurability of `topHerm` applied to a signed sum. -/
lemma measurable_topHerm_signSum (b : I → Bool) :
    Measurable fun x : I → Matrix n n ℂ => topHerm (signSum b x) :=
  measurable_topHerm.comp (measurable_signSum b)

/-- Lean implementation helper: complementing every Boolean sign negates the signed sum. -/
lemma signSum_not (b : I → Bool) (x : I → Matrix n n ℂ) :
    signSum (fun k => !(b k)) x = -signSum b x := by
  simp only [signSum, boolSign_not, neg_smul, Finset.sum_neg_distrib]

/-- Lean implementation helper: the coordinate map that swaps a pair when its sign bit is set. -/
def pairSwapMap (b : I → Bool) (k : I) :
    (Matrix n n ℂ × Matrix n n ℂ) → (Matrix n n ℂ × Matrix n n ℂ) :=
  if b k then Prod.swap else id

/-- Lean implementation helper: coordinatewise pair swapping for a Boolean pattern. -/
def pairSwap (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) :
    I → Matrix n n ℂ × Matrix n n ℂ :=
  fun k => pairSwapMap b k (q k)

/-- Lean implementation helper: measurability of one coordinate swap. -/
lemma measurable_pairSwapMap (b : I → Bool) (k : I) :
    Measurable (pairSwapMap (n := n) b k) := by
  cases h : b k <;> simp [pairSwapMap, h, measurable_id, measurable_swap]

/-- Lean implementation helper: measurability of coordinatewise pair swapping. -/
lemma measurable_pairSwap (b : I → Bool) :
    Measurable (pairSwap (n := n) b) := by
  exact measurable_pi_lambda _ fun k =>
    (measurable_pairSwapMap (n := n) b k).comp (measurable_pi_apply k)

/-- Lean implementation helper: coordinatewise pair swapping preserves an iid product-pair law. -/
lemma measurePreserving_pairSwap (ν : I → Measure (Matrix n n ℂ))
    [∀ k, IsProbabilityMeasure (ν k)] (b : I → Bool) :
    MeasurePreserving (pairSwap (n := n) b)
      (Measure.pi fun k => (ν k).prod (ν k))
      (Measure.pi fun k => (ν k).prod (ν k)) := by
  apply measurePreserving_pi _ _
  intro k
  cases h : b k
  · simpa [pairSwap, pairSwapMap, h] using
      (MeasurePreserving.id ((ν k).prod (ν k)))
  · simpa [pairSwap, pairSwapMap, h] using
      (Measure.measurePreserving_swap (μ := ν k) (ν := ν k))

/-- Lean implementation helper: the difference between the two matrices in a coordinate pair. -/
def pairDiff (q : I → Matrix n n ℂ × Matrix n n ℂ)
    (k : I) : Matrix n n ℂ := (q k).1 - (q k).2

/-- Lean implementation helper: swapping a coordinate multiplies its pair difference by its sign. -/
lemma pairDiff_pairSwap (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) (k : I) :
    pairDiff (pairSwap (n := n) b q) k = boolSign (b k) • pairDiff q k := by
  cases h : b k <;>
    simp [pairDiff, pairSwap, pairSwapMap, boolSign, h]

/-- Lean implementation helper: coordinatewise swapping converts the unsigned difference sum to a signed sum. -/
lemma sum_pairDiff_pairSwap (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) :
    (∑ k, pairDiff (pairSwap (n := n) b q) k) =
      ∑ k, boolSign (b k) • pairDiff q k := by
  exact Finset.sum_congr rfl fun k _ => pairDiff_pairSwap b q k

/-- Lean implementation helper: the Boolean-signed sum of coordinate-pair differences. -/
def pairSignedDiffSum (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, boolSign (b k) • pairDiff q k

/-- Lean implementation helper: decomposition of a signed pair-difference sum into two signed sums. -/
lemma pairSignedDiffSum_eq (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) :
    pairSignedDiffSum b q = signSum b (fun k => (q k).1) -
      signSum b (fun k => (q k).2) := by
  simp only [pairSignedDiffSum, pairDiff, signSum, smul_sub,
    Finset.sum_sub_distrib]

/-- Lean implementation helper: the equivalence that complements every Boolean sign. -/
def boolPatternNot : (I → Bool) ≃ (I → Bool) :=
  Equiv.piCongrRight fun _ => Equiv.boolNot

/-- Lean implementation helper: evaluation of the Boolean-pattern complement equivalence. -/
@[simp] lemma boolPatternNot_apply (b : I → Bool) (k : I) :
    boolPatternNot b k = !(b k) := rfl

end Signs

section PairSignAverage

variable {I n : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: an integrable norm budget for a family of matrix pairs. -/
def pairNormBudget (q : I → Matrix n n ℂ × Matrix n n ℂ) : ℝ :=
  (∑ k, ‖(q k).1‖) + ∑ k, ‖(q k).2‖

/-- Lean implementation helper: `topHerm` of the unsigned sum of pair differences. -/
def pairUnsignedTop (q : I → Matrix n n ℂ × Matrix n n ℂ) : ℝ :=
  topHerm (∑ k, pairDiff q k)

/-- Lean implementation helper: `topHerm` of the signed sum of pair differences. -/
def pairSignedTop (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) : ℝ :=
  topHerm (pairSignedDiffSum b q)

/-- Lean implementation helper: the positive-coordinate contribution for a sign pattern. -/
def pairPlusTop (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) : ℝ :=
  topHerm (signSum b (fun k => (q k).1))

/-- Lean implementation helper: the negated second-coordinate contribution for a sign pattern. -/
def pairMinusTop (b : I → Bool)
    (q : I → Matrix n n ℂ × Matrix n n ℂ) : ℝ :=
  topHerm (-signSum b (fun k => (q k).2))

/-- Lean implementation helper: measurability of the unsigned pair functional. -/
lemma measurable_pairUnsignedTop :
    Measurable (pairUnsignedTop :
      (I → Matrix n n ℂ × Matrix n n ℂ) → ℝ) := by
  apply measurable_topHerm.comp
  exact measurable_matsum Finset.univ fun k =>
    ((measurable_fst.comp (measurable_pi_apply k)).sub
      (measurable_snd.comp (measurable_pi_apply k)))

/-- Lean implementation helper: measurability of the signed pair functional. -/
lemma measurable_pairSignedTop (b : I → Bool) :
    Measurable (pairSignedTop (n := n) b) := by
  apply measurable_topHerm.comp
  exact measurable_matsum Finset.univ fun k =>
    (((measurable_fst.comp (measurable_pi_apply k)).sub
      (measurable_snd.comp (measurable_pi_apply k))).const_smul
        (boolSign (b k)))

/-- Lean implementation helper: measurability of the positive-coordinate functional. -/
lemma measurable_pairPlusTop (b : I → Bool) :
    Measurable (pairPlusTop (n := n) b) :=
  measurable_topHerm_signSum b |>.comp <|
    measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k)

/-- Lean implementation helper: measurability of the negated second-coordinate functional. -/
lemma measurable_pairMinusTop (b : I → Bool) :
    Measurable (pairMinusTop (n := n) b) := by
  exact measurable_topHerm.comp ((measurable_signSum b).comp
    (measurable_pi_lambda _ fun k => measurable_snd.comp (measurable_pi_apply k))).neg

/-- Lean implementation helper: integrability of the signed pair functional under the norm budget. -/
lemma integrable_pairSignedTop {τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ)}
    (hbudget : Integrable (pairNormBudget (I := I) (n := n)) τ)
    (b : I → Bool) : Integrable (pairSignedTop (n := n) b) τ := by
  refine Integrable.mono' hbudget (measurable_pairSignedTop b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_topHerm_le_norm _).trans <|
    calc
      ‖pairSignedDiffSum b q‖ ≤
          ∑ k, ‖boolSign (b k) • pairDiff q k‖ := norm_sum_le _ _
      _ = ∑ k, ‖pairDiff q k‖ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_smul, Real.norm_eq_abs, abs_boolSign, one_mul]
      _ ≤ ∑ k, (‖(q k).1‖ + ‖(q k).2‖) :=
        Finset.sum_le_sum fun k _ => norm_sub_le _ _
      _ = pairNormBudget q := by
        simp only [pairNormBudget, Finset.sum_add_distrib]

/-- Lean implementation helper: integrability of the positive-coordinate functional under the norm budget. -/
lemma integrable_pairPlusTop {τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ)}
    (hbudget : Integrable (pairNormBudget (I := I) (n := n)) τ)
    (b : I → Bool) : Integrable (pairPlusTop (n := n) b) τ := by
  refine Integrable.mono' hbudget (measurable_pairPlusTop b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_topHerm_le_norm _).trans <| (norm_signSum_le b _).trans <|
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Lean implementation helper: integrability of the negated second-coordinate functional under the norm budget. -/
lemma integrable_pairMinusTop {τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ)}
    (hbudget : Integrable (pairNormBudget (I := I) (n := n)) τ)
    (b : I → Bool) : Integrable (pairMinusTop (n := n) b) τ := by
  refine Integrable.mono' hbudget (measurable_pairMinusTop b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_topHerm_le_norm _).trans ?_
  rw [norm_neg]
  exact (norm_signSum_le b _).trans <|
    le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Lean implementation helper: pair reflection identifies the unsigned and signed integrals. -/
lemma integral_pairUnsigned_eq_signed
    (ν : I → Measure (Matrix n n ℂ)) [∀ k, IsProbabilityMeasure (ν k)]
    (b : I → Bool) :
    (∫ q, pairUnsignedTop q ∂Measure.pi fun k => (ν k).prod (ν k)) =
      ∫ q, pairSignedTop b q ∂Measure.pi fun k => (ν k).prod (ν k) := by
  let τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ) :=
    Measure.pi fun k => (ν k).prod (ν k)
  have hswap := measurePreserving_pairSwap (n := n) ν b
  calc
    (∫ q, pairUnsignedTop q ∂τ) =
        ∫ q, pairUnsignedTop (pairSwap b q) ∂τ := by
      rw [← integral_map hswap.aemeasurable
        measurable_pairUnsignedTop.aestronglyMeasurable, hswap.map_eq]
    _ = ∫ q, pairSignedTop b q ∂τ := by
      apply integral_congr_ae
      filter_upwards [] with q
      change topHerm (∑ k, pairDiff (pairSwap b q) k) =
        topHerm (pairSignedDiffSum b q)
      rw [sum_pairDiff_pairSwap]
      rfl

/-- Lean implementation helper: subadditivity bounds the signed pair integral by its two coordinate contributions. -/
lemma integral_pairSigned_le_plus_minus
    {τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ)}
    (hbudget : Integrable (pairNormBudget (I := I) (n := n)) τ)
    (b : I → Bool) :
    (∫ q, pairSignedTop b q ∂τ) ≤
      (∫ q, pairPlusTop b q ∂τ) + ∫ q, pairMinusTop b q ∂τ := by
  rw [← integral_add (integrable_pairPlusTop hbudget b)
    (integrable_pairMinusTop hbudget b)]
  refine integral_mono (integrable_pairSignedTop hbudget b)
    ((integrable_pairPlusTop hbudget b).add (integrable_pairMinusTop hbudget b))
    fun q => ?_
  change topHerm (pairSignedDiffSum b q) ≤
    topHerm (signSum b (fun k => (q k).1)) +
      topHerm (-signSum b (fun k => (q k).2))
  rw [pairSignedDiffSum_eq]
  simpa only [sub_eq_add_neg] using
    topHerm_add_le (signSum b (fun k => (q k).1))
      (-signSum b (fun k => (q k).2))

/-- Lean implementation helper: after averaging over signs, the two coordinate contributions agree. -/
lemma sum_integral_pairMinus_eq_plus
    (ν : I → Measure (Matrix n n ℂ)) [∀ k, IsProbabilityMeasure (ν k)] :
    (∑ b : I → Bool, ∫ q, pairMinusTop b q
        ∂Measure.pi fun k => (ν k).prod (ν k)) =
      ∑ b : I → Bool, ∫ q, pairPlusTop b q
        ∂Measure.pi fun k => (ν k).prod (ν k) := by
  let τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ) :=
    Measure.pi fun k => (ν k).prod (ν k)
  let allMinus : I → Bool := fun _ => true
  have hswap := measurePreserving_pairSwap (n := n) ν allMinus
  calc
    (∑ b : I → Bool, ∫ q, pairMinusTop b q ∂τ) =
        ∑ b : I → Bool, ∫ q, pairPlusTop (boolPatternNot b) q ∂τ := by
      apply Finset.sum_congr rfl
      intro b _
      calc
        (∫ q, pairMinusTop b q ∂τ) =
            ∫ q, pairMinusTop b (pairSwap allMinus q) ∂τ := by
          rw [← integral_map hswap.aemeasurable
            (measurable_pairMinusTop b).aestronglyMeasurable, hswap.map_eq]
        _ = ∫ q, pairPlusTop (boolPatternNot b) q ∂τ := by
          apply integral_congr_ae
          filter_upwards [] with q
          have hs := signSum_not b (fun k => (q k).1)
          apply congrArg topHerm
          rw [show boolPatternNot b = fun k => !(b k) by
            funext k
            exact boolPatternNot_apply b k]
          simpa [pairMinusTop, pairPlusTop, pairSwap, pairSwapMap,
            allMinus] using hs.symm
    _ = ∑ b : I → Bool, ∫ q, pairPlusTop b q ∂τ := by
      exact Equiv.sum_comp boolPatternNot
        (fun b => ∫ q, pairPlusTop b q ∂τ)

/-- Lean implementation helper: the finite-sign average bound obtained from pair reflection. -/
lemma pair_reflection_average_bound
    (ν : I → Measure (Matrix n n ℂ)) [∀ k, IsProbabilityMeasure (ν k)]
    (hbudget : Integrable (pairNormBudget (I := I) (n := n))
      (Measure.pi fun k => (ν k).prod (ν k))) :
    (∫ q, pairUnsignedTop q ∂Measure.pi fun k => (ν k).prod (ν k)) ≤
      2 * ((Fintype.card (I → Bool) : ℝ)⁻¹ *
        ∑ b : I → Bool,
          ∫ q, pairPlusTop b q ∂Measure.pi fun k => (ν k).prod (ν k)) := by
  let τ : Measure (I → Matrix n n ℂ × Matrix n n ℂ) :=
    Measure.pi fun k => (ν k).prod (ν k)
  let u : ℝ := ∫ q, pairUnsignedTop q ∂τ
  let a : (I → Bool) → ℝ := fun b => ∫ q, pairPlusTop b q ∂τ
  have hreflect : (Fintype.card (I → Bool) : ℝ) * u =
      ∑ b : I → Bool, ∫ q, pairSignedTop b q ∂τ := by
    calc
      (Fintype.card (I → Bool) : ℝ) * u = ∑ _b : I → Bool, u := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ b : I → Bool, ∫ q, pairSignedTop b q ∂τ :=
        Finset.sum_congr rfl fun b _ => integral_pairUnsigned_eq_signed ν b
  have htri : (∑ b : I → Bool, ∫ q, pairSignedTop b q ∂τ) ≤
      2 * ∑ b : I → Bool, a b := by
    calc
      _ ≤ ∑ b : I → Bool,
          ((∫ q, pairPlusTop b q ∂τ) + ∫ q, pairMinusTop b q ∂τ) :=
        Finset.sum_le_sum fun b _ => integral_pairSigned_le_plus_minus hbudget b
      _ = (∑ b : I → Bool, a b) +
          ∑ b : I → Bool, ∫ q, pairMinusTop b q ∂τ := Finset.sum_add_distrib
      _ = 2 * ∑ b : I → Bool, a b := by
        rw [sum_integral_pairMinus_eq_plus ν]
        ring
  have h := hreflect.le.trans htri
  have hcardpos : (0 : ℝ) < Fintype.card (I → Bool) := by
    exact_mod_cast Fintype.card_pos
  change u ≤ 2 * ((Fintype.card (I → Bool) : ℝ)⁻¹ * ∑ b, a b)
  calc
    u = (Fintype.card (I → Bool) : ℝ)⁻¹ *
        ((Fintype.card (I → Bool) : ℝ) * u) := by field_simp
    _ ≤ (Fintype.card (I → Bool) : ℝ)⁻¹ * (2 * ∑ b, a b) :=
      mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hcardpos))
    _ = 2 * ((Fintype.card (I → Bool) : ℝ)⁻¹ * ∑ b, a b) := by ring

end PairSignAverage

section IndependentSigns

variable {Ω I n : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype I] [DecidableEq I]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable {X : I → Ω → Matrix n n ℂ}

/-- Lean implementation helper: Independent-coordinate reflection, expressed as the exact finite average
over Boolean sign patterns.  The sole moment assumption is integrability of
the sum of coordinate norms. -/
lemma independent_pair_reflection_bound
    (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ)
    (hnormsum : Integrable (fun ω => ∑ k, ‖X k ω‖) μ) :
    (∫ p : Ω × Ω,
        topHerm ((∑ k, X k p.1) - ∑ k, X k p.2) ∂(μ.prod μ)) ≤
      2 * ((Fintype.card (I → Bool) : ℝ)⁻¹ *
        ∑ b : I → Bool, ∫ ω, topHerm (signSum b (fun k => X k ω)) ∂μ) := by
  let Φ : Ω → (I → Matrix n n ℂ) := fun ω k => X k ω
  have hΦmeas : Measurable Φ := measurable_pi_lambda _ hmeas
  let ν : I → Measure (Matrix n n ℂ) := fun k => μ.map (X k)
  let ρ : Measure (I → Matrix n n ℂ) := Measure.pi ν
  let σ : Measure (I → Matrix n n ℂ × Matrix n n ℂ) :=
    Measure.pi fun k => (ν k).prod (ν k)
  letI (k : I) : IsProbabilityMeasure (ν k) :=
    Measure.isProbabilityMeasure_map (hmeas k).aemeasurable
  have hΦlaw : μ.map Φ = ρ := by
    simpa only [Φ, ρ, ν] using
      hind.map_fun_eq_pi_map (fun k => (hmeas k).aemeasurable)
  have hΦmp : MeasurePreserving Φ μ ρ := ⟨hΦmeas, hΦlaw⟩
  have hArrow : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (Matrix n n ℂ) (Matrix n n ℂ) I)
      σ (ρ.prod ρ) := by
    simpa only [σ, ρ] using
      (measurePreserving_arrowProdEquivProdArrow
        (Matrix n n ℂ) (Matrix n n ℂ) I ν ν)
  let fstFamily : (I → Matrix n n ℂ × Matrix n n ℂ) →
      (I → Matrix n n ℂ) := fun q k => (q k).1
  let sndFamily : (I → Matrix n n ℂ × Matrix n n ℂ) →
      (I → Matrix n n ℂ) := fun q k => (q k).2
  have hfst : MeasurePreserving fstFamily σ ρ := by
    have hc := (measurePreserving_fst (μ := ρ) (ν := ρ)).comp hArrow
    change MeasurePreserving fstFamily σ ρ at hc
    exact hc
  have hsnd : MeasurePreserving sndFamily σ ρ := by
    have hc := (measurePreserving_snd (μ := ρ) (ν := ρ)).comp hArrow
    change MeasurePreserving sndFamily σ ρ at hc
    exact hc
  let G : (I → Matrix n n ℂ) × (I → Matrix n n ℂ) → ℝ :=
    fun p => topHerm ((∑ k, p.1 k) - ∑ k, p.2 k)
  have hsumMeas : Measurable (fun x : I → Matrix n n ℂ => ∑ k, x k) :=
    measurable_matsum Finset.univ fun k => measurable_pi_apply k
  have hGmeas : Measurable G := by
    exact measurable_topHerm.comp
      ((hsumMeas.comp measurable_fst).sub (hsumMeas.comp measurable_snd))
  have hghost_to_prod :
      (∫ p : Ω × Ω,
          topHerm ((∑ k, X k p.1) - ∑ k, X k p.2) ∂(μ.prod μ)) =
        ∫ p, G p ∂(ρ.prod ρ) := by
    have hp := hΦmp.prod hΦmp
    calc
      (∫ p : Ω × Ω,
          topHerm ((∑ k, X k p.1) - ∑ k, X k p.2) ∂(μ.prod μ)) =
          ∫ p : Ω × Ω, G (Prod.map Φ Φ p) ∂(μ.prod μ) := by rfl
      _ = ∫ p, G p ∂(ρ.prod ρ) := by
        rw [← integral_map hp.aemeasurable hGmeas.aestronglyMeasurable,
          hp.map_eq]
  have hprod_to_pairs :
      (∫ p, G p ∂(ρ.prod ρ)) =
        ∫ q, topHerm (∑ k, pairDiff q k) ∂σ := by
    calc
      (∫ p, G p ∂(ρ.prod ρ)) =
          ∫ q, G (MeasurableEquiv.arrowProdEquivProdArrow
            (Matrix n n ℂ) (Matrix n n ℂ) I q) ∂σ := by
        rw [← integral_map hArrow.aemeasurable hGmeas.aestronglyMeasurable,
          hArrow.map_eq]
      _ = ∫ q, topHerm (∑ k, pairDiff q k) ∂σ := by
        apply integral_congr_ae
        filter_upwards [] with q
        change topHerm ((∑ k, (q k).1) - ∑ k, (q k).2) =
          topHerm (∑ k, ((q k).1 - (q k).2))
        rw [Finset.sum_sub_distrib]
  let K : (I → Matrix n n ℂ) → ℝ := fun x => ∑ k, ‖x k‖
  have hKmeas : Measurable K := by
    exact Finset.measurable_sum _ fun k _ =>
      continuous_l2_opNorm.measurable.comp (measurable_pi_apply k)
  have hKρ : Integrable K ρ := by
    exact (hΦmp.integrable_comp hKmeas.aestronglyMeasurable).mp hnormsum
  have hKfstσ : Integrable (fun q => K (fstFamily q)) σ := by
    exact (hfst.integrable_comp hKmeas.aestronglyMeasurable).mpr hKρ
  have hKsndσ : Integrable (fun q => K (sndFamily q)) σ := by
    exact (hsnd.integrable_comp hKmeas.aestronglyMeasurable).mpr hKρ
  have hbudget : Integrable (pairNormBudget (I := I) (n := n)) σ := by
    refine (hKfstσ.add hKsndσ).congr ?_
    filter_upwards [] with q
    rfl
  have hpair := pair_reflection_average_bound (n := n) ν hbudget
  have hplus_transfer : ∀ b : I → Bool,
      (∫ q, pairPlusTop b q ∂σ) =
        ∫ ω, topHerm (signSum b (fun k => X k ω)) ∂μ := by
    intro b
    have hm := measurable_topHerm_signSum (n := n) b
    change (∫ q, topHerm (signSum b (fstFamily q)) ∂σ) = _
    calc
      (∫ q, topHerm (signSum b (fstFamily q)) ∂σ) =
          ∫ x, topHerm (signSum b x) ∂ρ := by
        rw [← integral_map hfst.aemeasurable hm.aestronglyMeasurable,
          hfst.map_eq]
      _ = ∫ ω, topHerm (signSum b (fun k => X k ω)) ∂μ := by
        symm
        rw [← integral_map hΦmp.aemeasurable hm.aestronglyMeasurable,
          hΦmp.map_eq]
  have hsum_transfer :
      (∑ b : I → Bool, ∫ q, pairPlusTop b q ∂σ) =
        ∑ b : I → Bool, ∫ ω, topHerm (signSum b (fun k => X k ω)) ∂μ :=
    Finset.sum_congr rfl fun b _ => hplus_transfer b
  rw [hghost_to_prod, hprod_to_pairs]
  change (∫ q, pairUnsignedTop q ∂σ) ≤ _
  rw [← hsum_transfer]
  exact hpair

end IndependentSigns

section BoolRademacherBridge

variable {I n : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: the uniform probability measure on Boolean signs. -/
def boolRademacherMeasure : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac false + (2 : ENNReal)⁻¹ • Measure.dirac true

instance : IsProbabilityMeasure boolRademacherMeasure := by
  rw [boolRademacherMeasure]
  constructor
  simp [ENNReal.inv_two_add_inv_two]

/-- Lean implementation helper: measurability of the Boolean sign encoding. -/
lemma measurable_boolSign : Measurable boolSign := measurable_of_countable _

/-- Lean implementation helper: the encoded uniform Boolean sign has the Rademacher law. -/
lemma map_boolSign_boolRademacherMeasure :
    boolRademacherMeasure.map boolSign = rademacherMeasure := by
  rw [boolRademacherMeasure, rademacherMeasure]
  simp [Measure.map_add, measurable_boolSign, boolSign]

/-- Lean implementation helper: each coordinate sign under the Boolean product measure is Rademacher. -/
lemma boolSign_law (k : I) :
    IsRademacher (fun b : I → Bool => boolSign (b k))
      (Measure.pi fun _ : I => boolRademacherMeasure) := by
  rw [IsRademacher]
  change (Measure.pi fun _ : I => boolRademacherMeasure).map
      (boolSign ∘ Function.eval k) = rademacherMeasure
  rw [← Measure.map_map measurable_boolSign (measurable_pi_apply k)]
  rw [(measurePreserving_eval (fun _ : I => boolRademacherMeasure) k).map_eq]
  exact map_boolSign_boolRademacherMeasure

/-- Lean implementation helper: the coordinate signs under the Boolean product measure are independent. -/
lemma boolSign_indep :
    iIndepFun (fun k (b : I → Bool) => boolSign (b k))
      (Measure.pi fun _ : I => boolRademacherMeasure) := by
  let hcoord : iIndepFun (fun k (b : I → Bool) => b k)
      (Measure.pi fun _ : I => boolRademacherMeasure) :=
    iIndepFun_pi (X := fun _ : I => id) (fun _ => measurable_id.aemeasurable)
  exact hcoord.comp (fun _ => boolSign) (fun _ => measurable_boolSign)

/-- Lean implementation helper: every Boolean sign pattern has uniform product probability. -/
lemma boolRademacher_pi_singleton (b : I → Bool) :
    (Measure.pi fun _ : I => boolRademacherMeasure).real {b} =
      (Fintype.card (I → Bool) : ℝ)⁻¹ := by
  rw [measureReal_def]
  have hset : ({b} : Set (I → Bool)) = Set.univ.pi (fun k => {b k}) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h k => congrFun h k, fun h => funext h⟩
  rw [hset, Measure.pi_pi]
  have hcoord : ∀ k : I, boolRademacherMeasure {b k} = (2 : ENNReal)⁻¹ := by
    intro k
    cases b k <;> simp [boolRademacherMeasure]
  simp_rw [hcoord, Finset.prod_const, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [Fintype.card_fun, Fintype.card_bool]
  norm_num
  rw [one_div, inv_pow]

/-- Lean implementation helper: the Hermitian Rademacher expectation bound written as a finite Boolean average. -/
lemma bool_sign_lambdaMax_average_le
    {A : I → Matrix n n ℂ} (hA : ∀ k, (A k).IsHermitian) :
    ((Fintype.card (I → Bool) : ℝ)⁻¹ *
        ∑ b : I → Bool, topHerm (signSum b A)) ≤
      Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) := by
  have hrad := rademacher_herm_expectation
    (μ := Measure.pi fun _ : I => boolRademacherMeasure)
    (fun k => measurable_boolSign.comp (measurable_pi_apply k))
    (fun k => boolSign_law k)
    (fun k b => by cases h : b k <;> simp [boolSign, h])
    boolSign_indep hA
  have hint : Integrable
      (fun b : I → Bool => topHerm (signSum b A))
      (Measure.pi fun _ : I => boolRademacherMeasure) := by
    exact Integrable.of_finite
  have havg :
      (∫ b : I → Bool, topHerm (signSum b A)
          ∂Measure.pi fun _ : I => boolRademacherMeasure) =
        (Fintype.card (I → Bool) : ℝ)⁻¹ *
          ∑ b : I → Bool, topHerm (signSum b A) := by
    rw [integral_fintype hint]
    simp_rw [boolRademacher_pi_singleton]
    simp only [smul_eq_mul, Finset.mul_sum]
  rw [← havg]
  calc
    (∫ b : I → Bool, topHerm (signSum b A)
        ∂Measure.pi fun _ : I => boolRademacherMeasure) =
        ∫ b : I → Bool, lambdaMax (isHermitian_matsum Finset.univ
          (fun k => isHermitian_real_smul (hA k) (boolSign (b k))))
          ∂Measure.pi fun _ : I => boolRademacherMeasure := by
      apply integral_congr_ae
      filter_upwards [] with b
      exact topHerm_of_isHermitian
        (isHermitian_matsum Finset.univ fun k =>
          isHermitian_real_smul (hA k) (boolSign (b k)))
    _ ≤ _ := hrad

end BoolRademacherBridge


section PsdSquare

variable {I n : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper: functional-calculus representation of the square of a Hermitian matrix. -/
private lemma psd_sq_eq_cfc {P : Matrix n n Complex} (hP : P.IsHermitian) :
    P * P = cfc (fun x : Real => x * x) P := by
  rw [cfc_mul (fun x : Real => x) (fun x : Real => x) P, cfc_id' Real P]

/-- Lean implementation helper: A positive-semidefinite matrix satisfies `P² ≤ ‖P‖ P`. -/
lemma psd_sq_le_norm_smul {P : Matrix n n Complex}
    (hP : P.PosSemidef) : P * P ≤ ‖P‖ • P := by
  rw [psd_sq_eq_cfc hP.1, smul_eq_cfc hP.1 ‖P‖]
  refine transfer_rule hP.1 (I := Set.Icc 0 ‖P‖) (fun i => ?_) fun a ha => ?_
  · refine ⟨hP.eigenvalues_nonneg i, ?_⟩
    exact (eigenvalues_le_lambdaMax hP.1 i).trans
      ((le_abs_self _).trans (abs_lambdaMax_le hP.1))
  · nlinarith [ha.1, ha.2]

/-- Lean implementation helper: For positive-semidefinite coefficients, the Rademacher square statistic is
controlled pointwise by the largest coefficient times the top eigenvalue of
their sum. -/
lemma norm_sum_sq_le_sup_mul_lambdaMax_sum
    {A : I → Matrix n n Complex} (hA : ∀ k, (A k).PosSemidef) :
    ‖∑ k, (A k) ^ 2‖ ≤
      (Finset.univ.sup' Finset.univ_nonempty
        (fun k => lambdaMax (hA k).1)) *
      lambdaMax (isHermitian_matsum Finset.univ (fun k => (hA k).1)) := by
  let M : Real := Finset.univ.sup' Finset.univ_nonempty
    (fun k => lambdaMax (hA k).1)
  have hM_nonneg : 0 ≤ M := by
    let k0 : I := Classical.arbitrary I
    exact ((hA k0).eigenvalues_nonneg (Classical.arbitrary n)).trans
      ((eigenvalues_le_lambdaMax (hA k0).1 (Classical.arbitrary n)).trans
        (Finset.le_sup' (fun k => lambdaMax (hA k).1) (Finset.mem_univ k0)))
  have hk_norm : ∀ k, ‖A k‖ ≤ M := by
    intro k
    rw [posSemidef_l2_opNorm_eq_lambdaMax (hA k)]
    exact Finset.le_sup' (fun j => lambdaMax (hA j).1) (Finset.mem_univ k)
  have hk_sq : ∀ k, (A k) ^ 2 ≤ M • A k := by
    intro k
    rw [pow_two]
    exact (psd_sq_le_norm_smul (hA k)).trans (by
      rw [Matrix.le_iff, ← sub_smul]
      exact (hA k).smul (sub_nonneg.mpr (hk_norm k)))
  have hsum_sq_psd : (∑ k, (A k) ^ 2).PosSemidef :=
    posSemidef_matsum Finset.univ fun k => by
      rw [pow_two]
      exact posSemidef_sq (hA k).1
  have hsum_psd : (∑ k, A k).PosSemidef := posSemidef_matsum Finset.univ hA
  have hsum_le : (∑ k, (A k) ^ 2) ≤ M • ∑ k, A k := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hk_sq k
  have hR_psd : (M • ∑ k, A k).PosSemidef := hsum_psd.smul hM_nonneg
  calc
    ‖∑ k, (A k) ^ 2‖ = lambdaMax hsum_sq_psd.1 :=
      posSemidef_l2_opNorm_eq_lambdaMax hsum_sq_psd
    _ ≤ lambdaMax hR_psd.1 :=
      lambdaMax_le_of_loewner_le hsum_sq_psd.1 hR_psd.1 hsum_le
    _ = M * lambdaMax hsum_psd.1 :=
      lambdaMax_smul_nonneg hsum_psd.1 hM_nonneg hR_psd.1
    _ = _ := rfl

end PsdSquare

section RealCauchy

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Lean implementation helper: The geometric mean of two nonnegative integrable real functions is
integrable. -/
lemma integrable_sqrt_mul
    {M Y : Omega → Real} (hM : Integrable M mu) (hY : Integrable Y mu)
    (hM0 : ∀ omega, 0 ≤ M omega) (hY0 : ∀ omega, 0 ≤ Y omega) :
    Integrable (fun omega => Real.sqrt (M omega * Y omega)) mu := by
  refine Integrable.mono' (hM.add hY)
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (hM.aestronglyMeasurable.mul hY.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt (M omega * Y omega) ≤ M omega + Y omega
  have hsquare := Real.sq_sqrt (mul_nonneg (hM0 omega) (hY0 omega))
  nlinarith [hM0 omega, hY0 omega, Real.sqrt_nonneg (M omega * Y omega),
    sq_nonneg (M omega - Y omega)]

/-- Lean implementation helper: Cauchy--Schwarz in the form used for the geometric-mean integrand. -/
lemma integral_sqrt_mul_le_sqrt_integral_mul
    {M Y : Omega → Real} (hM : Integrable M mu) (hY : Integrable Y mu)
    (hM0 : ∀ omega, 0 ≤ M omega) (hY0 : ∀ omega, 0 ≤ Y omega) :
    (∫ omega, Real.sqrt (M omega * Y omega) ∂mu) ≤
      Real.sqrt ((∫ omega, M omega ∂mu) * (∫ omega, Y omega ∂mu)) := by
  have hsM : AEStronglyMeasurable (fun omega => Real.sqrt (M omega)) mu :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hM.aestronglyMeasurable
  have hsY : AEStronglyMeasurable (fun omega => Real.sqrt (Y omega)) mu :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hY.aestronglyMeasurable
  have hsM_sq : Integrable (fun omega => Real.sqrt (M omega) ^ 2) mu :=
    hM.congr (Filter.Eventually.of_forall fun omega =>
      (Real.sq_sqrt (hM0 omega)).symm)
  have hsY_sq : Integrable (fun omega => Real.sqrt (Y omega) ^ 2) mu :=
    hY.congr (Filter.Eventually.of_forall fun omega =>
      (Real.sq_sqrt (hY0 omega)).symm)
  have hsM_L2 : MemLp (fun omega => Real.sqrt (M omega)) 2 mu :=
    (memLp_two_iff_integrable_sq hsM).2 hsM_sq
  have hsY_L2 : MemLp (fun omega => Real.sqrt (Y omega)) 2 mu :=
    (memLp_two_iff_integrable_sq hsY).2 hsY_sq
  have hsM_L2' : MemLp (fun omega => Real.sqrt (M omega))
      (ENNReal.ofReal (2 : Real)) mu := by simpa using hsM_L2
  have hsY_L2' : MemLp (fun omega => Real.sqrt (Y omega))
      (ENNReal.ofReal (2 : Real)) mu := by simpa using hsY_L2
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun omega => Real.sqrt_nonneg (M omega))
    (Filter.Eventually.of_forall fun omega => Real.sqrt_nonneg (Y omega))
    hsM_L2' hsY_L2'
  simp_rw [Real.rpow_two, Real.sq_sqrt (hM0 _), Real.sq_sqrt (hY0 _)] at hholder
  calc
    (∫ omega, Real.sqrt (M omega * Y omega) ∂mu) =
        ∫ omega, Real.sqrt (M omega) * Real.sqrt (Y omega) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega =>
        Real.sqrt_mul (hM0 omega) (Y omega)
    _ ≤ (∫ omega, M omega ∂mu) ^ ((1 : Real) / 2) *
        (∫ omega, Y omega ∂mu) ^ ((1 : Real) / 2) := hholder
    _ = Real.sqrt (∫ omega, M omega ∂mu) *
        Real.sqrt (∫ omega, Y omega ∂mu) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ = Real.sqrt ((∫ omega, M omega ∂mu) * (∫ omega, Y omega ∂mu)) := by
      rw [Real.sqrt_mul (integral_nonneg hM0)]

end RealCauchy

section ScalarAlgebra

/-- Lean implementation helper: the elementary quadratic rearrangement at the end
of the Rosenthal argument. The intermediate coefficient is `8`; `1 ≤ exp 1` gives
the Book's coefficient. -/
lemma rosenthal_scalar_algebra
    {y a ell b : Real} (hy : 0 ≤ y) (_ha : 0 ≤ a) (hell : 0 ≤ ell)
    (hb : 0 ≤ b)
    (h : y ≤ a + 2 * Real.sqrt (2 * ell * b * y)) :
    y ≤ 2 * a + 8 * Real.exp 1 * b * ell := by
  have hq : 0 ≤ 2 * ell * b * y := by positivity
  have hrhs : 0 ≤ y / 2 + 4 * ell * b := by positivity
  have hsq : 4 * (2 * ell * b * y) ≤ (y / 2 + 4 * ell * b) ^ 2 := by
    nlinarith [sq_nonneg (y / 2 - 4 * ell * b)]
  have hsqrt : 2 * Real.sqrt (2 * ell * b * y) ≤ y / 2 + 4 * ell * b := by
    calc
      2 * Real.sqrt (2 * ell * b * y) =
          Real.sqrt (4 * (2 * ell * b * y)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
        rw [show Real.sqrt (4 : Real) = 2 by
          exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
      _ ≤ Real.sqrt ((y / 2 + 4 * ell * b) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = y / 2 + 4 * ell * b := Real.sqrt_sq hrhs
  have hstrong : y ≤ 2 * a + 8 * ell * b := by
    nlinarith
  have he : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbell : 0 ≤ b * ell := mul_nonneg hb hell
  have hcoef : 8 * ell * b ≤ 8 * Real.exp 1 * b * ell := by
    have he8 : (8 : Real) ≤ 8 * Real.exp 1 := by nlinarith
    calc
      8 * ell * b = 8 * (b * ell) := by ring
      _ ≤ (8 * Real.exp 1) * (b * ell) := by
        exact mul_le_mul_of_nonneg_right he8 hbell
      _ = 8 * Real.exp 1 * b * ell := by ring
  nlinarith

end ScalarAlgebra

section MatrixRosenthalFinal

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable [IsProbabilityMeasure mu] [Nonempty n] [Nonempty I]
variable {X : I → Omega → Matrix n n Complex}

/-- Lean implementation helper: the complete auxiliary matrix Rosenthal estimate. -/
theorem matrix_rosenthal_aux
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k omega, (X k omega).IsHermitian)
    (hmin : ∀ k omega, 0 ≤ lambdaMin (hherm k omega))
    (hint : ∀ k, MIntegrable (X k) mu)
    (hind : ProbabilityTheory.iIndepFun X mu)
    (hsupint : Integrable (fun omega => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k omega))) mu)
    (hYint : Integrable (fun omega => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k omega))) mu) :
    ∫ omega, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k omega)) ∂mu ≤
      2 * lambdaMax (isHermitian_sum_expectation (μ := mu) hherm) +
        8 * Real.exp 1 *
          (∫ omega, Finset.univ.sup' Finset.univ_nonempty
            (fun k => lambdaMax (hherm k omega)) ∂mu) * Real.log (Fintype.card n) := by
  let Y : Omega → Matrix n n Complex := fun omega => ∑ k, X k omega
  let M : Omega → Real := fun omega => Finset.univ.sup' Finset.univ_nonempty
    (fun k => lambdaMax (hherm k omega))
  let V : Omega → Real := fun omega =>
    lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k omega))
  let ell : Real := Real.log (Fintype.card n)
  let y : Real := ∫ omega, V omega ∂mu
  let a : Real := lambdaMax (isHermitian_sum_expectation (μ := mu) hherm)
  let b : Real := ∫ omega, M omega ∂mu
  have hXpsd : ∀ k omega, (X k omega).PosSemidef := fun k omega =>
    posSemidef_of_lambdaMin_nonneg (hherm k omega) (hmin k omega)
  have hYmeas : Measurable Y := measurable_matsum Finset.univ hmeas
  have hYpsd : ∀ omega, (Y omega).PosSemidef := fun omega =>
    posSemidef_matsum Finset.univ fun k => hXpsd k omega
  have hYherm : ∀ omega, (Y omega).IsHermitian := fun omega => (hYpsd omega).1
  have hYmintegrable : MIntegrable Y mu := by
    simpa only [Y] using
      (MIntegrable.finsetSum (μ := mu) Finset.univ
        (fun k _ => hint k))
  have hV_eq : V = fun omega => lambdaMax (hYherm omega) := by
    funext omega
    apply lambdaMax_congr rfl
  have hVint : Integrable V mu := by
    simpa only [V] using hYint
  have hYnorm : Integrable (fun omega => ‖Y omega‖) mu := by
    refine hVint.congr (Filter.Eventually.of_forall fun omega => ?_)
    dsimp only [V, Y]
    rw [posSemidef_l2_opNorm_eq_lambdaMax (hYpsd omega)]
  have hM_nonneg : ∀ omega, 0 ≤ M omega := by
    intro omega
    let k0 : I := Classical.arbitrary I
    exact ((hXpsd k0 omega).eigenvalues_nonneg (Classical.arbitrary n)).trans
      ((eigenvalues_le_lambdaMax (hherm k0 omega) (Classical.arbitrary n)).trans
        (Finset.le_sup' (fun k => lambdaMax (hherm k omega))
          (Finset.mem_univ k0)))
  have hV_nonneg : ∀ omega, 0 ≤ V omega := by
    intro omega
    rw [hV_eq]
    exact ((hYpsd omega).eigenvalues_nonneg (Classical.arbitrary n)).trans
      (eigenvalues_le_lambdaMax (hYherm omega) (Classical.arbitrary n))
  have hell_nonneg : 0 ≤ ell := by
    dsimp only [ell]
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hb_nonneg : 0 ≤ b := by
    exact integral_nonneg hM_nonneg
  have hy_nonneg : 0 ≤ y := by
    exact integral_nonneg hV_nonneg
  have hEpsd : (∑ k, expectation mu (X k)).PosSemidef := by
    refine posSemidef_matsum Finset.univ fun k => ?_
    exact posSemidef_expectation (hint k)
      (Filter.Eventually.of_forall fun omega => hXpsd k omega)
  have ha_nonneg : 0 ≤ a := by
    exact (hEpsd.eigenvalues_nonneg (Classical.arbitrary n)).trans
      (eigenvalues_le_lambdaMax
        (isHermitian_sum_expectation (μ := mu) hherm) (Classical.arbitrary n))
  have hcoordNorm : ∀ k, Integrable (fun omega => ‖X k omega‖) mu := by
    intro k
    refine Integrable.mono' hsupint
      (continuous_l2_opNorm.measurable.comp (hmeas k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      posSemidef_l2_opNorm_eq_lambdaMax (hXpsd k omega)]
    exact Finset.le_sup' (fun j => lambdaMax (hherm j omega))
      (Finset.mem_univ k)
  have hnormsum : Integrable (fun omega => ∑ k, ‖X k omega‖) mu :=
    integrable_finsetSum Finset.univ fun k _ => hcoordNorm k
  have hghost0 := lambdaMax_symmetrization_ghost
    (mu := mu) hYmeas hYherm hYmintegrable hYnorm
    (by simpa only [V, Y] using hYint)
  have hEYeq : lambdaMax (isHermitian_expectation (μ := mu)
      (Filter.Eventually.of_forall hYherm)) = a := by
    dsimp only [a]
    apply lambdaMax_congr
    simpa only [Y] using expectation_matsum_eq (μ := mu) hint
  have hghost : y ≤ a +
      ∫ p : Omega × Omega,
        topHerm ((∑ k, X k p.1) - ∑ k, X k p.2) ∂(mu.prod mu) := by
    rw [hEYeq] at hghost0
    dsimp only [y, V]
    refine hghost0.trans_eq ?_
    congr 1
    apply integral_congr_ae
    filter_upwards [] with p
    rw [topHerm_of_isHermitian]
  have hreflect := independent_pair_reflection_bound
    (μ := mu) hmeas hind hnormsum
  have hsignint : ∀ pattern : I → Bool,
      Integrable (fun omega => topHerm (signSum pattern (fun k => X k omega))) mu := by
    intro pattern
    refine Integrable.mono' hnormsum
      ((measurable_topHerm_signSum pattern).comp
        (measurable_pi_lambda _ hmeas)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_topHerm_le_norm _).trans (norm_signSum_le pattern _)
  let Avg : Omega → Real := fun omega =>
    (Fintype.card (I → Bool) : Real)⁻¹ *
      ∑ pattern : I → Bool, topHerm (signSum pattern (fun k => X k omega))
  have hAvgInt : Integrable Avg mu := by
    exact (integrable_finsetSum Finset.univ fun pattern _ =>
      hsignint pattern).const_mul _
  have havg_eq :
      (Fintype.card (I → Bool) : Real)⁻¹ *
          ∑ pattern : I → Bool,
            ∫ omega, topHerm (signSum pattern (fun k => X k omega)) ∂mu =
        ∫ omega, Avg omega ∂mu := by
    dsimp only [Avg]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun pattern _ => hsignint pattern)]
  let M2 : Omega → Real := fun omega => 2 * ell * M omega
  have hM2int : Integrable M2 mu := by
    exact hsupint.const_mul (2 * ell)
  have hM2_nonneg : ∀ omega, 0 ≤ M2 omega := fun omega => by
    dsimp only [M2]
    exact mul_nonneg (mul_nonneg (by norm_num) hell_nonneg) (hM_nonneg omega)
  let U : Omega → Real := fun omega => Real.sqrt (M2 omega * V omega)
  have hUint : Integrable U mu := by
    exact integrable_sqrt_mul hM2int hVint hM2_nonneg hV_nonneg
  have hAvg_le_U : ∀ omega, Avg omega ≤ U omega := by
    intro omega
    have hrad := bool_sign_lambdaMax_average_le
      (A := fun k => X k omega) (fun k => hherm k omega)
    have hsq := norm_sum_sq_le_sup_mul_lambdaMax_sum
      (A := fun k => X k omega) (fun k => hXpsd k omega)
    have hinside : 2 * ‖∑ k, (X k omega) ^ 2‖ * ell ≤
        M2 omega * V omega := by
      dsimp only [M2, M, V]
      nlinarith
    exact hrad.trans (Real.sqrt_le_sqrt hinside)
  have havg_le :
      (Fintype.card (I → Bool) : Real)⁻¹ *
          ∑ pattern : I → Bool,
            ∫ omega, topHerm (signSum pattern (fun k => X k omega)) ∂mu ≤
        ∫ omega, U omega ∂mu := by
    rw [havg_eq]
    exact integral_mono hAvgInt hUint hAvg_le_U
  have hcauchy : (∫ omega, U omega ∂mu) ≤
      Real.sqrt (2 * ell * b * y) := by
    have hc := integral_sqrt_mul_le_sqrt_integral_mul
      hM2int hVint hM2_nonneg hV_nonneg
    have hM2_integral : (∫ omega, M2 omega ∂mu) = 2 * ell * b := by
      dsimp only [M2, b, M]
      rw [integral_const_mul]
    simpa only [U, hM2_integral, y] using hc
  have hmaster : y ≤ a + 2 * Real.sqrt (2 * ell * b * y) := by
    calc
      y ≤ a + ∫ p : Omega × Omega,
          topHerm ((∑ k, X k p.1) - ∑ k, X k p.2) ∂(mu.prod mu) := hghost
      _ ≤ a + 2 * ((Fintype.card (I → Bool) : Real)⁻¹ *
          ∑ pattern : I → Bool,
            ∫ omega, topHerm (signSum pattern (fun k => X k omega)) ∂mu) :=
        by simpa only [add_comm] using add_le_add_left hreflect a
      _ ≤ a + 2 * (∫ omega, U omega ∂mu) := by gcongr
      _ ≤ a + 2 * Real.sqrt (2 * ell * b * y) := by gcongr
  have hfinal := rosenthal_scalar_algebra hy_nonneg ha_nonneg hell_nonneg hb_nonneg hmaster
  simpa only [y, V, a, b, M, ell] using hfinal

end MatrixRosenthalFinal

end

end MatrixConcentration
