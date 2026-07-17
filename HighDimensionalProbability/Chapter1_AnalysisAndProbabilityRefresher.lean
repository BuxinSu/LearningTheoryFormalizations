import HighDimensionalProbability.Prelude.RandomGraph
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Probability.CDF
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Analysis.PSeries
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Chapter 1 — A Quick Refresher on Analysis and Probability

## Contents

- §1.1 Convex sets and functions
  - Convexity and concavity via line segments and the secant inequality.
    **Book Equation (1.1).**
  - The maximum principle on convex hulls, including a safe finite-attainment form.
    **Book Section 1.1.**
- §1.2 Norms and inner products
  - Finite-dimensional `ell^p` and `ell^infinity` norms and their unit balls.
    **Book Section 1.2.**
  - Euclidean identity, cube/cross-polytope formula, and monotonicity.
    **Book Equations (1.2)–(1.4).**
  - Hölder inequality and norm duality, including endpoint cases.
    **Book Equations (1.5)–(1.6).**
- §1.3 Random variables and random vectors
  - Expectation, variance, moment-generating functions, and random-variable `L^p` norms.
    **Book Equations (1.7)–(1.12).**
  - Covariance and covariance matrices. **Book Equation (1.13).**
- §1.4 Union bound
  - Indicator inequality and the union bound. **Book Equation (1.14); Lemma 1.4.1.**
  - Dense random graphs have no isolated vertices above the logarithmic threshold.
    **Book Example 1.4.2.**
- §1.5 Conditioning
  - Laws of total expectation and total probability. **Book Equations (1.15)–(1.17).**
  - A nontrivial Rademacher sum cancels with probability at most one half.
    **Book Example 1.5.1.**
- §1.6 Probabilistic inequalities
  - Jensen, norm-of-expectation, monotonicity, Minkowski, and Hölder.
    **Book Equations (1.18)–(1.22).**
  - Integrated tails, Markov (including sharpness), and Chebyshev.
    **Book Lemma 1.6.1; Proposition 1.6.2; Corollary 1.6.3.**
- §1.7 Limit theorems
  - Sample-mean variance, the strong law, and the central limit theorem.
    **Book Equation (1.23); Theorems 1.7.1 and 1.7.3.**
  - Gaussian, binomial, and Poisson laws. **Book Equations (1.24)–(1.27).**
  - Stirling, factorial, logarithmic, and Gamma estimates.
    **Book Equations (1.28)–(1.31).**
-/

/-
# Book Chapter 1.1: convex sets and convex functions

This file records the book's two-point definitions as exact correspondences with Mathlib,
and gives a formulation of the maximum principle which remains correct for arbitrary (possibly
noncompact and infinite) generating sets.  For a finite generating set it also gives the usual
maximum-attainment statement.
-/

open Set

namespace HDP.Chapter1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The book definition of a convex set: it is closed under the points of every line segment.

**Book Section 1.1.** -/
theorem convex_iff_segment {K : Set E} :
    Convex ℝ K ↔
      ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        t • x + (1 - t) • y ∈ K := by
  constructor
  · intro hK x hx y hy t ht ht1
    exact hK hx hy ht (sub_nonneg.mpr ht1) (by ring)
  · intro h x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    simpa [hb'] using h x hx y hy a ha (by linarith)

/-- Equation (1.1), as an exact correspondence with `ConvexOn` once the domain is known convex.

**Book Equation (1.1).** -/
theorem convexOn_iff {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} :
    ConvexOn ℝ K f ↔
      ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y := by
  constructor
  · intro hf x hx y hy t ht ht1
    simpa [smul_eq_mul] using
      hf.2 hx hy ht (sub_nonneg.mpr ht1) (by ring : t + (1 - t) = 1)
  · intro h
    refine ⟨hK, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    simpa [hb', smul_eq_mul] using h x hx y hy a ha (by linarith)

/-- Concavity is precisely convexity after negating the function.

**Book Equation (1.1).** -/
theorem concaveOn_iff_neg_convexOn {K : Set E} {f : E → ℝ} :
    ConcaveOn ℝ K f ↔ ConvexOn ℝ K (-f) :=
  neg_convexOn_iff.symm

/-- Safe maximum principle for an arbitrary generating set: every value on the convex hull is
bounded by some value on the generating set. Unlike a literal maximum statement, this needs no
compactness or finiteness assumption.

**Book Section 1.1.** -/
theorem convexHull_value_le_generator {K T : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hTK : T ⊆ K) {x : E} (hx : x ∈ convexHull ℝ T) :
    ∃ y ∈ T, f x ≤ f y :=
  hf.exists_ge_of_mem_convexHull hTK hx

/-- A number bounds `f` on a generating set iff it bounds `f` on its convex hull. This is the
supremum-safe version of Exercise 1.4 and does not require either image to be bounded above.

**Book Section 1.1.** -/
theorem upperBounds_image_convexHull {K T : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hTK : T ⊆ K) :
    upperBounds (f '' convexHull ℝ T) = upperBounds (f '' T) := by
  ext a
  constructor
  · intro ha b hb
    rcases hb with ⟨x, hx, rfl⟩
    exact ha ⟨x, subset_convexHull ℝ T hx, rfl⟩
  · intro ha b hb
    rcases hb with ⟨x, hx, rfl⟩
    obtain ⟨y, hyT, hxy⟩ := convexHull_value_le_generator hf hTK hx
    exact hxy.trans (ha ⟨y, hyT, rfl⟩)

/-- A convex function has the same supremum on a bounded nonempty generating set
and on its convex hull. The hypotheses make both suprema non-junk; for an
unrestricted set the upper-bound identity above is the safer public interface.

**Book Exercise 1.4.** -/
theorem exercise_1_4_sSup {K T : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) (hTK : T ⊆ K) (hT : T.Nonempty) (hbd : BddAbove (f '' T)) :
    sSup (f '' convexHull ℝ T) = sSup (f '' T) := by
  apply le_antisymm
  · refine csSup_le ((convexHull_nonempty_iff.mpr hT).image f) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyT, hxy⟩ := convexHull_value_le_generator hf hTK hx
    exact hxy.trans (le_csSup hbd ⟨y, hyT, rfl⟩)
  · refine csSup_le (hT.image f) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_csSup (hf.bddAbove_convexHull hTK hbd) ⟨x, subset_convexHull ℝ T hx, rfl⟩

/-- The finite maximum principle stated literally: a convex function on the convex hull of a
nonempty finite set attains a global maximum at one of the generators.

**Book Exercise 1.4.** -/
theorem maximum_principle_finset {f : E → ℝ} {t : Finset E} (ht : t.Nonempty)
    (hf : ConvexOn ℝ (convexHull ℝ (t : Set E)) f) :
    ∃ y ∈ t, ∀ x ∈ convexHull ℝ (t : Set E), f x ≤ f y := by
  obtain ⟨y, hyt, hymax⟩ := t.exists_max_image f ht
  refine ⟨y, hyt, ?_⟩
  intro x hx
  obtain ⟨z, hzt, hxz⟩ := hf.exists_ge_of_mem_convexHull
    (subset_convexHull ℝ (t : Set E)) hx
  exact hxz.trans (hymax z hzt)

/-- A norm is a convex function (book §1.2(a)).

**Book Section 1.1.** -/
theorem norm_convexOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set F} (hK : Convex ℝ K) : ConvexOn ℝ K (fun x => ‖x‖) :=
  convexOn_norm hK

/-- The unit ball of a normed real vector space is convex (book §1.2(b)).

**Book Section 1.1.** -/
theorem convex_unitBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Convex ℝ {x : F | ‖x‖ ≤ 1} := by
  have hset : {x : F | ‖x‖ ≤ 1} = Metric.closedBall (0 : F) 1 := by
    ext x
    simp [Metric.mem_closedBall]
  rw [hset]
  exact convex_closedBall (0 : F) 1

end HDP.Chapter1

/-
# Book Chapter 1.2: finite-dimensional `ell^p` norms

The book functions below are defined through Mathlib's finite `PiLp` norm.  The theorem
`lpNorm_eq_sum` proves that this definition is exactly the displayed real-rpow formula in the
source.  Using `PiLp` internally gives the norm laws without creating a competing global norm
instance on finite real vectors.
-/

open Set
open scoped ENNReal NNReal BigOperators

namespace HDP.Chapter1

variable {ι : Type*} [Fintype ι]

/-- The finite-dimensional `ell^p` norm from §1.2. Its source formula is
`lpNorm_eq_sum`; the definition has a harmless Mathlib junk value when `p ≤ 0`.

**Book Section 1.2.** -/
noncomputable def lpNorm (p : ℝ) (x : ι → ℝ) : ℝ :=
  ‖WithLp.toLp (ENNReal.ofReal p) x‖

/-- The displayed definition of `ell^p` in §1.2.

**Book Section 1.2.** -/
theorem lpNorm_eq_sum {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    lpNorm p x = (∑ i, |x i| ^ p) ^ (1 / p) := by
  rw [lpNorm, PiLp.norm_eq_sum]
  · simp [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  · simpa [ENNReal.toReal_ofReal hp.le] using hp

/-- The `ell^∞` norm. On a finite product this is the maximum coordinate absolute value.

**Book Section 1.2.** -/
noncomputable def linftyNorm (x : ι → ℝ) : ℝ := ‖x‖

/-- For a finite real vector, the ℓ∞ norm agrees with `piNorm`, hence equals `‖x‖`.

**Lean implementation helper.** -/
theorem linftyNorm_eq_piNorm (x : ι → ℝ) : linftyNorm x = ‖x‖ := rfl

/-- Coordinate characterization of the finite `ell^∞` norm.

**Lean implementation helper.** -/
theorem linftyNorm_le_iff {x : ι → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    linftyNorm x ≤ r ↔ ∀ i, |x i| ≤ r := by
  simpa [linftyNorm, Real.norm_eq_abs] using
    (pi_norm_le_iff_of_nonneg (x := x) hr)

/-- The finite-dimensional ℓᵖ norm is nonnegative whenever `p > 0`.

**Lean implementation helper.** -/
theorem lpNorm_nonneg {p : ℝ} (hp : 0 < p) (x : ι → ℝ) : 0 ≤ lpNorm p x := by
  rw [lpNorm_eq_sum hp]
  positivity

/-- The finite-dimensional ℓ∞ norm is nonnegative.

**Lean implementation helper.** -/
theorem linftyNorm_nonneg (x : ι → ℝ) : 0 ≤ linftyNorm x :=
  norm_nonneg _

/-- Positive definiteness, valid in the norm range `p ≥ 1`.

**Lean implementation helper.** -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 1 ≤ p) {x : ι → ℝ} :
    lpNorm p x = 0 ↔ x = 0 := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  simp [lpNorm]

/-- The finite-dimensional ℓ∞ norm satisfies `zero_iff`: it vanishes exactly
for the zero vector.

**Lean implementation helper.** -/
theorem linftyNorm_eq_zero_iff {x : ι → ℝ} : linftyNorm x = 0 ↔ x = 0 := by
  simp [linftyNorm]

/-- Absolute homogeneity of the finite `ell^p` norm.

**Lean implementation helper.** -/
theorem lpNorm_smul {p : ℝ} (hp : 1 ≤ p) (c : ℝ) (x : ι → ℝ) :
    lpNorm p (c • x) = |c| * lpNorm p x := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  simpa [lpNorm, Real.norm_eq_abs] using
    (norm_smul c (WithLp.toLp (ENNReal.ofReal p) x))

/-- Negating a vector does not change its finite `ℓᵖ` norm.

**Lean implementation helper.** -/
theorem lpNorm_neg {p : ℝ} (hp : 1 ≤ p) (x : ι → ℝ) :
    lpNorm p (-x) = lpNorm p x := by
  simpa using lpNorm_smul hp (-1 : ℝ) x

/-- Minkowski's inequality for finite-dimensional vectors.

**Book Section 1.2.** -/
theorem lpNorm_add_le {p : ℝ} (hp : 1 ≤ p) (x y : ι → ℝ) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  exact norm_add_le (WithLp.toLp (ENNReal.ofReal p) x)
    (WithLp.toLp (ENNReal.ofReal p) y)

/-- Scalar multiplication scales the finite `ℓ∞` norm by the scalar's absolute value.

**Lean implementation helper.** -/
theorem linftyNorm_smul (c : ℝ) (x : ι → ℝ) :
    linftyNorm (c • x) = |c| * linftyNorm x := by
  simpa [linftyNorm, Real.norm_eq_abs] using norm_smul c x

/-- Coordinate `ell^p`/`ell^infty` norms and Minkowski's inequality.

**Book Section 1.2.** -/
theorem linftyNorm_add_le (x y : ι → ℝ) :
    linftyNorm (x + y) ≤ linftyNorm x + linftyNorm y :=
  norm_add_le x y

/-- Every coordinate is bounded by the `ell^p` norm.

**Lean implementation helper.** -/
theorem abs_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → ℝ) (i : ι) :
    |x i| ≤ lpNorm p x := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  simpa [lpNorm, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i)

/-- Finite-dimensional `ell^p` norms
decrease with the exponent.

**Book Equation (1.4).** -/
theorem lpNorm_anti {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (x : ι → ℝ) :
    lpNorm q x ≤ lpNorm p x := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hq0 : 0 < q := hp0.trans_le hpq
  by_cases hx : x = 0
  · subst x
    rw [(lpNorm_eq_zero_iff hp).2 rfl,
      (lpNorm_eq_zero_iff (hp.trans hpq)).2 rfl]
  let M := lpNorm p x
  have hM0 : 0 < M := by
    have hMnonneg : 0 ≤ M := lpNorm_nonneg hp0 x
    exact hMnonneg.lt_of_ne fun hM => hx ((lpNorm_eq_zero_iff hp).1 hM.symm)
  have hcoord (i : ι) : |x i| ≤ M := abs_apply_le_lpNorm hp x i
  have hsum_p_nonneg : 0 ≤ ∑ i, |x i| ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p
  have hMpow : M ^ p = ∑ i, |x i| ^ p := by
    dsimp [M]
    rw [lpNorm_eq_sum hp0]
    rw [← Real.rpow_mul hsum_p_nonneg (1 / p) p]
    have : (1 / p) * p = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hterm (i : ι) : |x i| ^ q ≤ M ^ (q - p) * |x i| ^ p := by
    by_cases hi : x i = 0
    · simp [hi, Real.zero_rpow hp0.ne', Real.zero_rpow hq0.ne']
    · calc
        |x i| ^ q = |x i| ^ ((q - p) + p) := by ring_nf
        _ = |x i| ^ (q - p) * |x i| ^ p :=
          Real.rpow_add (abs_pos.mpr hi) _ _
        _ ≤ M ^ (q - p) * |x i| ^ p := by
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (abs_nonneg _) (hcoord i) (sub_nonneg.mpr hpq))
            (Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : ∑ i, |x i| ^ q ≤ M ^ q := by
    calc
      ∑ i, |x i| ^ q ≤ ∑ i, M ^ (q - p) * |x i| ^ p :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = M ^ (q - p) * ∑ i, |x i| ^ p := by rw [Finset.mul_sum]
      _ = M ^ (q - p) * M ^ p := by rw [← hMpow]
      _ = M ^ ((q - p) + p) := (Real.rpow_add hM0 _ _).symm
      _ = M ^ q := by ring_nf
  rw [lpNorm_eq_sum hq0]
  calc
    (∑ i, |x i| ^ q) ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
      Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) q) hsum
        (by positivity)
    _ = M ^ (q * (1 / q)) := (Real.rpow_mul hM0.le q (1 / q)).symm
    _ = M := by
      have : q * (1 / q) = 1 := by field_simp
      rw [this, Real.rpow_one]

/-- The source's `ell^1` formula.

**Lean implementation helper.** -/
theorem lpNorm_one (x : ι → ℝ) : lpNorm 1 x = ∑ i, |x i| := by
  simpa using lpNorm_eq_sum (p := (1 : ℝ)) zero_lt_one x

/-- The source's Euclidean formula (1.2), written for an ordinary coordinate vector.

**Book Equation (1.2).** -/
theorem lpNorm_two (x : ι → ℝ) :
    lpNorm 2 x = Real.sqrt (∑ i, (x i) ^ 2) := by
  unfold lpNorm
  rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
  rw [PiLp.norm_eq_of_L2]
  congr 2
  funext i
  simp [Real.norm_eq_abs, sq_abs]

/-- Formula (1.2): the book `ell^2` norm agrees with Mathlib's Euclidean norm.

**Book Equation (1.2).** -/
theorem lpNorm_two_eq_euclidean (x : EuclideanSpace ℝ ι) :
    lpNorm 2 (fun i => x i) = ‖x‖ := by
  rw [lpNorm_two, EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The real dot product used in (1.2).

**Book Equation (1.2).** -/
def dotProduct (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

/-- The dot product of a finite real vector with itself is the sum of its squared coordinates.

**Lean implementation helper.** -/
theorem dotProduct_self (x : ι → ℝ) : dotProduct x x = ∑ i, (x i) ^ 2 := by
  simp [dotProduct, pow_two]

/-- The Euclidean norm/dot-product identity in (1.2).

**Book Equation (1.2).** -/
theorem sq_lpNorm_two_eq_dotProduct (x : ι → ℝ) :
    (lpNorm 2 x) ^ 2 = dotProduct x x := by
  rw [lpNorm_two, dotProduct_self, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Hölder's inequality (1.5), for finite conjugate exponents.

**Book Equation (1.5).** -/
theorem holder_inequality {p q : ℝ} (hpq : p.HolderConjugate q) (x y : ι → ℝ) :
    |dotProduct x y| ≤ lpNorm p x * lpNorm q y := by
  have hp : 0 < p := lt_trans zero_lt_one (Real.holderConjugate_iff.mp hpq).1
  have hq : 0 < q :=
    lt_trans zero_lt_one (Real.holderConjugate_iff.mp hpq.symm).1
  rw [lpNorm_eq_sum hp, lpNorm_eq_sum hq, abs_le]
  constructor
  · have h := Real.inner_le_Lp_mul_Lq (s := Finset.univ)
      (fun i => -x i) y hpq
    have hneg : -dotProduct x y ≤
        (∑ i, |x i| ^ p) ^ (1 / p) * (∑ i, |y i| ^ q) ^ (1 / q) := by
      simpa [dotProduct, Finset.sum_neg_distrib] using h
    linarith
  · simpa [dotProduct] using
      (Real.inner_le_Lp_mul_Lq (s := Finset.univ) x y hpq)

/-- Cauchy--Schwarz is the `p=q=2` case of Hölder.

**Book Equation (1.5).** -/
theorem cauchy_schwarz_vector (x y : ι → ℝ) :
    |dotProduct x y| ≤ lpNorm 2 x * lpNorm 2 y :=
  holder_inequality Real.HolderConjugate.two_two x y

/-- Hölder's endpoint `(1,∞)`, using the source's convention for conjugate exponents.

**Book Equation (1.5).** -/
theorem holder_one_top (x y : ι → ℝ) :
    |dotProduct x y| ≤ lpNorm 1 x * linftyNorm y := by
  calc
    |dotProduct x y| ≤ ∑ i, |x i * y i| := by
      simpa [dotProduct] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => x i * y i))
    _ = ∑ i, |x i| * |y i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, |x i| * linftyNorm y := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact (linftyNorm_le_iff (linftyNorm_nonneg y)).1 le_rfl i
    _ = (∑ i, |x i|) * linftyNorm y := by rw [Finset.sum_mul]
    _ = lpNorm 1 x * linftyNorm y := by rw [lpNorm_one]

/-- Holder (including Cauchy--Schwarz and endpoint conjugates).

**Book Equation (1.5).** -/
theorem holder_top_one (x y : ι → ℝ) :
    |dotProduct x y| ≤ linftyNorm x * lpNorm 1 y := by
  rw [mul_comm]
  simpa [dotProduct, mul_comm] using holder_one_top y x

/-- The source unit ball `B_p^n`.

**Lean implementation helper.** -/
def lpUnitBall (p : ℝ) : Set (ι → ℝ) := {x | lpNorm p x ≤ 1}

/-- The source unit ball `B_∞^n`.

**Lean implementation helper.** -/
def linftyUnitBall : Set (ι → ℝ) := {x | linftyNorm x ≤ 1}

/-- Every finite-dimensional `ℓᵖ` unit ball with `p ≥ 1` is convex.

**Lean implementation helper.** -/
theorem convex_lpUnitBall {p : ℝ} (hp : 1 ≤ p) : Convex ℝ (lpUnitBall (ι := ι) p) := by
  rw [convex_iff_segment]
  intro x hx y hy t ht ht1
  change lpNorm p (t • x + (1 - t) • y) ≤ 1
  calc
    lpNorm p (t • x + (1 - t) • y)
        ≤ lpNorm p (t • x) + lpNorm p ((1 - t) • y) := lpNorm_add_le hp _ _
    _ = t * lpNorm p x + (1 - t) * lpNorm p y := by
      rw [lpNorm_smul hp, lpNorm_smul hp, abs_of_nonneg ht,
        abs_of_nonneg (sub_nonneg.mpr ht1)]
    _ ≤ t * 1 + (1 - t) * 1 := by
      gcongr
      · exact hx
      · exact hy
    _ = 1 := by ring

/-- The finite-dimensional `ℓ∞` unit ball is convex.

**Lean implementation helper.** -/
theorem convex_linftyUnitBall : Convex ℝ (linftyUnitBall (ι := ι)) := by
  simpa [linftyUnitBall, linftyNorm] using
    (convex_unitBall (F := ι → ℝ))

/-- The first identity in (1.3): the `ell^∞` unit ball is the coordinate cube.

**Book Equation (1.3).** -/
theorem linftyUnitBall_eq_cube :
    linftyUnitBall (ι := ι) = Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [linftyUnitBall, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]
  rw [linftyNorm_le_iff zero_le_one]
  simp [abs_le]

/-- The vertex set of the coordinate cube.

**Lean implementation helper.** -/
def cubeVertices : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ => ({-1, 1} : Set ℝ))

/-- The cube is the convex hull of its vertices.

**Book Equation (1.3).** -/
theorem linftyUnitBall_eq_convexHull_cubeVertices :
    linftyUnitBall (ι := ι) = convexHull ℝ (cubeVertices (ι := ι)) := by
  rw [linftyUnitBall_eq_cube, cubeVertices, convexHull_pi]
  congr 1
  funext i
  rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]

/-- Formula (1.4), equivalently: `B_p` is contained in `B_q` for `p ≤ q`.

**Book Equation (1.4).** -/
theorem lpUnitBall_mono {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    lpUnitBall (ι := ι) p ⊆ lpUnitBall q := by
  intro x hx
  exact (lpNorm_anti hp hpq x).trans hx

/-- A concrete vector which norms a vector in the `(1,∞)` Hölder pairing.

**Lean implementation helper.** -/
noncomputable def normingSign (x : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ x i then 1 else -1

omit [Fintype ι] in
/-- The norming sign of every coordinate has absolute value one.

**Lean implementation helper.** -/
@[simp] theorem abs_normingSign (x : ι → ℝ) (i : ι) :
    |normingSign x i| = 1 := by
  unfold normingSign
  split <;> simp

omit [Fintype ι] in
/-- Multiplying a coordinate by its norming sign gives its absolute value.

**Lean implementation helper.** -/
@[simp] theorem mul_normingSign (x : ι → ℝ) (i : ι) :
    x i * normingSign x i = |x i| := by
  by_cases h : 0 ≤ x i
  · simp [normingSign, h, abs_of_nonneg h]
  · have h' : x i ≤ 0 := le_of_lt (lt_of_not_ge h)
    simp [normingSign, h, abs_of_nonpos h']

omit [Fintype ι] in
/-- Multiplying a coordinate's absolute value by its norming sign recovers the coordinate.

**Lean implementation helper.** -/
@[simp] theorem abs_mul_normingSign (x : ι → ℝ) (i : ι) :
    |x i| * normingSign x i = x i := by
  by_cases h : 0 ≤ x i
  · simp [normingSign, h, abs_of_nonneg h]
  · have h' : x i ≤ 0 := le_of_lt (lt_of_not_ge h)
    simp [normingSign, h, abs_of_nonpos h']

/-- The `ell^1` norm is the greatest pairing with a vector in the `ell^infinity`
unit ball. This endpoint form uses `IsGreatest` rather than an unsafe maximum
over an arbitrary set.

**Book Equation (1.6).** -/
theorem duality_one_top (x : ι → ℝ) :
    IsGreatest ((fun y => dotProduct x y) '' linftyUnitBall (ι := ι)) (lpNorm 1 x) := by
  constructor
  · refine ⟨normingSign x, ?_, ?_⟩
    · rw [linftyUnitBall, Set.mem_setOf_eq, linftyNorm_le_iff zero_le_one]
      exact fun i => by simp
    · change (∑ i, x i * normingSign x i) = lpNorm 1 x
      rw [lpNorm_one]
      exact Finset.sum_congr rfl fun i _ => mul_normingSign x i
  · rintro _ ⟨y, hy, rfl⟩
    change linftyNorm y ≤ 1 at hy
    calc
      dotProduct x y ≤ |dotProduct x y| := le_abs_self _
      _ ≤ lpNorm 1 x * linftyNorm y := holder_one_top x y
      _ ≤ lpNorm 1 x * 1 :=
        mul_le_mul_of_nonneg_left hy (lpNorm_nonneg zero_lt_one x)
      _ = lpNorm 1 x := mul_one _

/-- The `ell^infinity` norm is the greatest pairing with a vector in the `ell^1`
unit ball.

**Book Equation (1.6).** -/
theorem duality_top_one (x : ι → ℝ) :
    IsGreatest ((fun y => dotProduct x y) '' lpUnitBall (ι := ι) 1) (linftyNorm x) := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun j => |x j|)
      Finset.univ_nonempty
    have htop : linftyNorm x = |x i| := by
      apply le_antisymm
      · rw [linftyNorm_le_iff (abs_nonneg (x i))]
        exact fun j => hi j (Finset.mem_univ j)
      · exact (linftyNorm_le_iff (linftyNorm_nonneg x)).1 le_rfl i
    let y : ι → ℝ := fun j => if j = i then normingSign x i else 0
    have hy : y ∈ lpUnitBall (ι := ι) 1 := by
      change lpNorm 1 y ≤ 1
      rw [lpNorm_one]
      have hsum : ∑ j, |y j| = 1 := by
        rw [Finset.sum_eq_single i]
        · simp [y]
        · intro j _ hji
          simp [y, hji]
        · simp
      rw [hsum]
    constructor
    · refine ⟨y, hy, ?_⟩
      change dotProduct x y = linftyNorm x
      rw [htop]
      simp [dotProduct, y, mul_normingSign]
    · rintro _ ⟨z, hz, rfl⟩
      change lpNorm 1 z ≤ 1 at hz
      calc
        dotProduct x z ≤ |dotProduct x z| := le_abs_self _
        _ ≤ linftyNorm x * lpNorm 1 z := holder_top_one x z
        _ ≤ linftyNorm x * 1 :=
          mul_le_mul_of_nonneg_left hz (linftyNorm_nonneg x)
        _ = linftyNorm x := mul_one _
  · letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    rw [(linftyNorm_eq_zero_iff).2 rfl]
    constructor
    · refine ⟨0, ?_, by simp [dotProduct]⟩
      rw [lpUnitBall, Set.mem_setOf_eq, (lpNorm_eq_zero_iff le_rfl).2 rfl]
      norm_num
    · rintro _ ⟨y, _, rfl⟩
      simp [dotProduct]

/-- A norming vector for the finite-exponent Hölder pairing.

**Lean implementation helper.** -/
noncomputable def normingVector (p : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  normingSign x i * (|x i| / lpNorm p x) ^ (p - 1)

/-- Duality for finite conjugate exponents.

**Book Equation (1.6).** -/
theorem exercise_1_19 {p q : ℝ} (hpq : p.HolderConjugate q) (x : ι → ℝ) :
    IsGreatest ((fun y => dotProduct x y) '' lpUnitBall (ι := ι) q) (lpNorm p x) := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  by_cases hx : x = 0
  · subst x
    have hp1 : 1 ≤ p := hpq.lt.le
    rw [(lpNorm_eq_zero_iff hp1).2 rfl]
    constructor
    · refine ⟨0, ?_, by simp [dotProduct]⟩
      rw [lpUnitBall, Set.mem_setOf_eq, (lpNorm_eq_zero_iff hpq.symm.lt.le).2 rfl]
      norm_num
    · rintro _ ⟨y, _, rfl⟩
      simp [dotProduct]
  let M := lpNorm p x
  have hp1 : 1 ≤ p := hpq.lt.le
  have hM0 : 0 < M :=
    (lpNorm_nonneg hp x).lt_of_ne fun h => hx ((lpNorm_eq_zero_iff hp1).1 h.symm)
  have hsum_nonneg : 0 ≤ ∑ i, |x i| ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p
  have hMpow : M ^ p = ∑ i, |x i| ^ p := by
    dsimp [M]
    rw [lpNorm_eq_sum hp, ← Real.rpow_mul hsum_nonneg (1 / p) p]
    have h : (1 / p) * p = 1 := by field_simp
    rw [h, Real.rpow_one]
  let y := normingVector p x
  have hyabs (i : ι) : |y i| = (|x i| / M) ^ (p - 1) := by
    change |normingSign x i * (|x i| / M) ^ (p - 1)| = _
    rw [abs_mul, abs_normingSign, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (div_nonneg (abs_nonneg _) hM0.le) _)]
  have hsum_y : ∑ i, |y i| ^ q = 1 := by
    calc
      ∑ i, |y i| ^ q = ∑ i, (|x i| / M) ^ ((p - 1) * q) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hyabs, ← Real.rpow_mul (div_nonneg (abs_nonneg _) hM0.le)]
      _ = ∑ i, (|x i| / M) ^ p := by rw [hpq.sub_one_mul_conj]
      _ = ∑ i, |x i| ^ p / M ^ p := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.div_rpow (abs_nonneg _) hM0.le]
      _ = (∑ i, |x i| ^ p) / M ^ p := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
      _ = 1 := by rw [← hMpow, div_self (ne_of_gt (Real.rpow_pos_of_pos hM0 p))]
  have hyNorm : lpNorm q y = 1 := by
    rw [lpNorm_eq_sum hq, hsum_y]
    simp
  have hdot : dotProduct x y = M := by
    rw [dotProduct]
    calc
      ∑ i, x i * y i = ∑ i, |x i| ^ p / M ^ (p - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x i = 0
        · simp [hi, y, normingVector, hp.ne']
        · change x i * (normingSign x i * (|x i| / M) ^ (p - 1)) = _
          rw [← mul_assoc, mul_normingSign]
          rw [Real.div_rpow (abs_nonneg _) hM0.le]
          rw [← mul_div_assoc]
          congr 1
          calc
            |x i| * |x i| ^ (p - 1) = |x i| ^ 1 * |x i| ^ (p - 1) := by
              rw [Real.rpow_one]
            _ = |x i| ^ (1 + (p - 1)) := (Real.rpow_add (abs_pos.mpr hi) _ _).symm
            _ = |x i| ^ p := by ring_nf
      _ = (∑ i, |x i| ^ p) / M ^ (p - 1) := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
      _ = M ^ p / M ^ (p - 1) := by rw [hMpow]
      _ = M ^ (p - (p - 1)) := (Real.rpow_sub hM0 p (p - 1)).symm
      _ = M := by ring_nf; rw [Real.rpow_one]
  constructor
  · refine ⟨y, ?_, hdot⟩
    rw [lpUnitBall, Set.mem_setOf_eq, hyNorm]
  · rintro _ ⟨z, hz, rfl⟩
    change lpNorm q z ≤ 1 at hz
    calc
      dotProduct x z ≤ |dotProduct x z| := le_abs_self _
      _ ≤ lpNorm p x * lpNorm q z := holder_inequality hpq x z
      _ ≤ lpNorm p x * 1 := mul_le_mul_of_nonneg_left hz (lpNorm_nonneg hp x)
      _ = lpNorm p x := mul_one _

/-- The standard coordinate vectors, used in the cross-polytope identity.

**Lean implementation helper.** -/
noncomputable def standardBasisSet : Set (ι → ℝ) := by
  classical
  exact Set.range fun i => Pi.single i 1

/-- The `ℓ¹` unit ball is absolutely convex.

**Lean implementation helper.** -/
theorem absConvex_lpUnitBall_one : AbsConvex ℝ (lpUnitBall (ι := ι) 1) := by
  constructor
  · intro a ha
    rintro _ ⟨x, hx, rfl⟩
    change lpNorm 1 x ≤ 1 at hx
    change lpNorm 1 (a • x) ≤ 1
    rw [lpNorm_smul le_rfl]
    calc
      |a| * lpNorm 1 x ≤ 1 * 1 := by
        apply mul_le_mul
        · simpa [Real.norm_eq_abs] using ha
        · exact hx
        · exact lpNorm_nonneg zero_lt_one x
        · norm_num
      _ = 1 := one_mul 1
  · exact convex_lpUnitBall le_rfl

/-- The `ell^1` unit ball is the absolute convex hull of the standard basis.

**Lean implementation helper.** -/
theorem lpUnitBall_one_eq_absConvexHull [Nonempty ι] :
    lpUnitBall (ι := ι) 1 = absConvexHull ℝ (standardBasisSet (ι := ι)) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    let A := absConvexHull ℝ (standardBasisSet (ι := ι))
    have hA : AbsConvex ℝ A := absConvex_absConvexHull
    by_cases hx0 : x = 0
    · subst x
      apply hA.1.zero_mem
      apply Set.Nonempty.mono subset_absConvexHull
      refine ⟨Pi.single (Classical.arbitrary ι) 1, ?_⟩
      change Pi.single (Classical.arbitrary ι) 1 ∈ standardBasisSet
      rw [standardBasisSet]
      exact ⟨Classical.arbitrary ι, rfl⟩
    let s : ℝ := ∑ i, |x i|
    have hs_eq : s = lpNorm 1 x := by rw [lpNorm_one]
    have hs0 : 0 < s := by
      rw [hs_eq]
      exact (lpNorm_nonneg zero_lt_one x).lt_of_ne fun h =>
        hx0 ((lpNorm_eq_zero_iff le_rfl).1 h.symm)
    have hs1 : s ≤ 1 := hs_eq.symm ▸ hx
    let z : ι → (ι → ℝ) := fun i => normingSign x i • Pi.single i 1
    have hz (i : ι) : z i ∈ A := by
      apply hA.1.smul_mem
      · simp [Real.norm_eq_abs]
      · exact subset_absConvexHull ⟨i, rfl⟩
    have hw0 (i : ι) : 0 ≤ |x i| / s := div_nonneg (abs_nonneg _) hs0.le
    have hw1 : ∑ i, |x i| / s = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      change s * s⁻¹ = 1
      exact mul_inv_cancel₀ hs0.ne'
    have hcomb : (∑ i, (|x i| / s) • z i) ∈ A :=
      hA.2.sum_mem (fun i _ => hw0 i) hw1 (fun i _ => hz i)
    have hsum : (∑ i, (|x i| / s) • z i) = (1 / s) • x := by
      ext j
      suffices (|x j| / s) * normingSign x j = (1 / s) * x j by
        simpa [z, Pi.single_apply] using this
      rw [div_eq_mul_inv, one_div]
      calc
        |x j| * s⁻¹ * normingSign x j = s⁻¹ * (|x j| * normingSign x j) := by ring
        _ = s⁻¹ * x j := by rw [abs_mul_normingSign]
    have hscaled : s • ((1 / s) • x) ∈ A := by
      apply hA.1.smul_mem
      · simpa [Real.norm_eq_abs, abs_of_nonneg hs0.le] using hs1
      · exact hsum ▸ hcomb
    simpa [smul_smul, hs0.ne'] using hscaled
  · apply absConvexHull_min ?_ absConvex_lpUnitBall_one
    intro v hv
    change v ∈ Set.range (fun i => Pi.single i 1) at hv
    rcases hv with ⟨i, rfl⟩
    rw [lpUnitBall, Set.mem_setOf_eq, lpNorm_one]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp

/-- For a nonempty finite coordinate type, `B_1` is the convex hull of the signed
standard basis vectors.

**Book Equation (1.3).** -/
theorem lpUnitBall_one_eq_crossPolytope [Nonempty ι] :
    lpUnitBall (ι := ι) 1 =
      convexHull ℝ (standardBasisSet (ι := ι) ∪ -(standardBasisSet (ι := ι))) := by
  rw [convexHull_union_neg_eq_absConvexHull, lpUnitBall_one_eq_absConvexHull]

end HDP.Chapter1


/-!
# Book Chapter 1, Sections 1.3–1.5

Random variables, random vectors, the union bound, and conditioning. See the
second-edition PDF, pages 18–22 (printed pages 10–14).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval

namespace HDP.Chapter1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## §1.3 Random variables and random vectors -/

/-- The source's `L^p` norm of a random variable, `‖X‖_{L^p} = (𝔼|X|^p)^{1/p}`,
for `0 < p < ∞`. Implicit source definition (note the normalization difference with the
`ℓ^p` norm of a vector, the source §1.6 footnote). Mathlib expresses the `L^∞` norm
(`ess sup |X|`) as `eLpNorm X ∞ μ`.

**Book Equation (1.10).** -/
noncomputable def lpNormRV (X : Ω → ℝ) (p : ℝ) (μ : Measure Ω) : ℝ :=
  (∫ ω, |X ω| ^ p ∂μ) ^ (1/p)

/-- Mathlib correspondence lemma: the source's finite real `L^p` norm (1.10) agrees
with Mathlib's authoritative extended-valued `eLpNorm` for `0 < p < ∞`.
The `MemLp` hypothesis records the finiteness needed before taking `toReal`.

**Book Equation (1.10).** -/
lemma lpNormRV_eq_toReal_eLpNorm {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hX : MemLp X (ENNReal.ofReal p) μ) :
    lpNormRV X p μ = (eLpNorm X (ENNReal.ofReal p) μ).toReal := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  have hint : ∫ ω, |X ω| ^ p ∂μ = (∫⁻ ω, ‖X ω‖ₑ ^ p ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => rpow_nonneg (abs_nonneg _) p)
      (by
        have h1 : AEStronglyMeasurable (fun ω => |X ω|) μ := by
          simpa [Real.norm_eq_abs] using hX.aestronglyMeasurable.norm
        exact (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable h1)]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  rw [lpNormRV, hint, ← ENNReal.toReal_rpow]

/-- Mathlib correspondence lemma (the source §1.3): the moment generating function
`M_X(t) = 𝔼 e^{tX}` is Mathlib's `ProbabilityTheory.mgf`.

**Book Section 1.3.** -/
lemma mgf_def' (X : Ω → ℝ) (t : ℝ) : mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl

/-- Linearity of expectation: `𝔼[a₁X₁ + ⋯ + aₙXₙ] = a₁𝔼X₁ + ⋯ + aₙ𝔼Xₙ`
for any (not necessarily independent) integrable random variables. Explicit unnumbered
source statement; Mathlib correspondence via `integral_finsetSum`.

**Book Section 1.3.** -/
theorem expectation_linear {ι : Type*} (s : Finset ι) (a : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) μ) :
    ∫ ω, (∑ i ∈ s, a i * X i ω) ∂μ = ∑ i ∈ s, a i * ∫ ω, X i ω ∂μ := by
  rw [integral_finsetSum s (fun i hi => (hX i hi).const_mul (a i))]
  exact Finset.sum_congr rfl fun i hi => integral_const_mul _ _

/-- For pairwise independent random variables,
`Var(a₁X₁ + ⋯ + aₙXₙ) = a₁²Var(X₁) + ⋯ + aₙ²Var(Xₙ)`.
Explicit source statement (stated for "independent (or even uncorrelated)" families;
formalized for pairwise independent families, which covers both source readings since
the source's proof only uses vanishing covariances).

**Book Equation (1.8).** -/
theorem variance_weighted_sum [IsProbabilityMeasure μ] {ι : Type*} {s : Finset ι}
    {X : ι → Ω → ℝ} (a : ι → ℝ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hindep : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ) :
    Var[∑ i ∈ s, fun ω => a i * X i ω; μ] = ∑ i ∈ s, (a i)^2 * Var[X i; μ] := by
  have hmul : ∀ i ∈ s, MemLp (fun ω => a i * X i ω) 2 μ :=
    fun i hi => (hX i hi).const_mul (a i)
  have hindep' : Set.Pairwise ↑s fun i j =>
      IndepFun (fun ω => a i * X i ω) (fun ω => a j * X j ω) μ := by
    intro i hi j hj hij
    exact (hindep hi hj hij).comp (measurable_const_mul (a i)) (measurable_const_mul (a j))
  rw [IndepFun.variance_sum hmul hindep']
  exact Finset.sum_congr rfl fun i _ => variance_const_mul (a i) (X i) μ

/-- The variance of a weighted sum is the sum of the weighted variances when
all off-diagonal covariances vanish.

The off-diagonal covariance hypotheses are exactly the part of independence used by the
variance computation. This source-facing wrapper therefore does not add an independence
assumption merely for convenience.

**Book Equation (1.8).** -/
theorem variance_weighted_sum_uncorrelated [IsProbabilityMeasure μ]
    {ι : Type*} {s : Finset ι} {X : ι → Ω → ℝ} (a : ι → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (huncorr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[∑ i ∈ s, fun ω => a i * X i ω; μ] =
      ∑ i ∈ s, (a i) ^ 2 * Var[X i; μ] := by
  have hmul : ∀ i ∈ s, MemLp (fun ω => a i * X i ω) 2 μ :=
    fun i hi => (hX i hi).const_mul (a i)
  rw [variance_sum' hmul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · rw [covariance_self (hmul i hi).aemeasurable, variance_const_mul]
  · intro j hj hji
    rw [covariance_const_mul_left, covariance_const_mul_right,
      huncorr i hi j hj (Ne.symm hji)]
    ring
  · exact fun hnot => (hnot hi).elim

/-- The expectation of the indicator of an event equals its probability,
`𝔼 𝟏_E = ℙ(E)`. Explicit source statement; Mathlib correspondence via
`integral_indicator_one`.

**Book Equation (1.9).** -/
theorem expectation_indicator (E : Set Ω) (hE : MeasurableSet E) :
    ∫ ω, E.indicator (fun _ => (1:ℝ)) ω ∂μ = μ.real E :=
  integral_indicator_one hE

/-- The `L²` inner product of two random variables, `⟨X,Y⟩_{L²} = 𝔼 XY`.
Implicit source definition.

**Book Equation (1.11).** -/
noncomputable def l2InnerRV (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ := ∫ ω, X ω * Y ω ∂μ

/-- `‖X‖²_{L²} = ⟨X,X⟩_{L²}` (the `L²` norm agrees with the inner product).
Implicit source claim.

**Book Equation (1.11).** -/
lemma sq_lpNormRV_two_eq_l2InnerRV {X : Ω → ℝ} (_hX : MemLp X 2 μ) :
    (lpNormRV X 2 μ) ^ (2:ℕ) = l2InnerRV X X μ := by
  have h1 : ∀ ω, |X ω| ^ (2:ℝ) = X ω * X ω := by
    intro ω
    rw [show ((2:ℝ) = ((2:ℕ):ℝ)) by norm_num, rpow_natCast, sq_abs, sq]
  have h2 : ∫ ω, |X ω| ^ (2:ℝ) ∂μ = l2InnerRV X X μ := by
    unfold l2InnerRV
    exact integral_congr_ae (Filter.Eventually.of_forall h1)
  have hnn : 0 ≤ l2InnerRV X X μ := by
    unfold l2InnerRV
    exact integral_nonneg fun ω => mul_self_nonneg _
  rw [lpNormRV, h2, ← Real.rpow_natCast (l2InnerRV X X μ ^ (1/(2:ℝ))) 2,
    ← Real.rpow_mul hnn]
  norm_num

/-- The standard deviation `σ(X) = √Var(X)` satisfies
`σ(X) = ‖X − 𝔼X‖_{L²}`. Implicit source definition with embedded identity.

**Book Equation (1.12).** -/
theorem stdDev_eq_lpNormRV [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Real.sqrt (Var[X; μ]) = lpNormRV (fun ω => X ω - ∫ ω', X ω' ∂μ) 2 μ := by
  have hvar : Var[X; μ] = ∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ 2 ∂μ :=
    variance_eq_integral hX.aemeasurable
  have h1 : ∀ ω, |X ω - ∫ ω', X ω' ∂μ| ^ (2:ℝ) = (X ω - ∫ ω', X ω' ∂μ) ^ (2:ℕ) := by
    intro ω
    rw [show ((2:ℝ) = ((2:ℕ):ℝ)) by norm_num, rpow_natCast, sq_abs]
  rw [lpNormRV, integral_congr_ae (Filter.Eventually.of_forall h1), ← hvar,
    Real.sqrt_eq_rpow]

/-- The covariance `cov(X,Y) = 𝔼(X−𝔼X)(Y−𝔼Y)`.
Mathlib correspondence: this is `ProbabilityTheory.covariance`.

**Book Equation (1.13).** -/
lemma covariance_def' {X Y : Ω → ℝ} :
    cov[X, Y; μ] = ∫ ω, (X ω - ∫ ω', X ω' ∂μ) * (Y ω - ∫ ω', Y ω' ∂μ) ∂μ := rfl

/-- Coordinatewise expectation of a random vector,
`(𝔼X)ᵢ = 𝔼(Xᵢ)`. Implicit source definition ("The expected value of `X` is defined
coordinate-wise"); in Lean the Bochner integral in `EuclideanSpace` is automatically
coordinatewise, which this lemma records.

**Book Equation (1.13).** -/
theorem expectation_vector_apply {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hX : Integrable X μ) (i : Fin n) :
    (∫ ω, X ω ∂μ) i = ∫ ω, X ω i ∂μ := by
  have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).integral_comp_comm hX
  simpa using this.symm

/-- The covariance matrix `cov(X) = 𝔼 (X−𝔼X)(X−𝔼X)ᵀ` of a random vector.
Implicit source definition.

**Book Equation (1.13).** -/
noncomputable def covMatrix {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n)) (μ : Measure Ω) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * (X ω j - ∫ ω', X ω' j ∂μ) ∂μ

/-- The `(i,j)` entry of the covariance matrix equals `cov(Xᵢ, Xⱼ)`.
Implicit source claim ("an `n×n` matrix whose `(i,j)`-th entry equals `cov(Xᵢ,Xⱼ)`").

**Book Equation (1.13).** -/
theorem covMatrix_apply {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    covMatrix X μ i j = cov[fun ω => X ω i, fun ω => X ω j; μ] := rfl

/-! ## §1.4 Union bound -/

/-- Additivity of probability: for pairwise disjoint events,
`ℙ(⋃ Eᵢ) = ∑ ℙ(Eᵢ)`. Explicit unnumbered source statement.

**Book Section 1.4.** -/
theorem probability_additive [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    (E : ι → Set Ω) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hdisj : Set.Pairwise ↑s (Function.onFun Disjoint E)) :
    μ.real (⋃ i ∈ s, E i) = ∑ i ∈ s, μ.real (E i) :=
  measureReal_biUnion_finset hdisj hE

/-- The indicator of a union is at most the sum of the indicators,
`𝟏_{⋃ᵢEᵢ} ≤ ∑ᵢ 𝟏_{Eᵢ}`. Intermediate claim in the proof of Lemma 1.4.1.

**Book Equation (1.14).** -/
lemma indicator_biUnion_le_sum {ι : Type*} (s : Finset ι) (E : ι → Set Ω) (ω : Ω) :
    (⋃ i ∈ s, E i).indicator (fun _ => (1:ℝ)) ω
      ≤ ∑ i ∈ s, (E i).indicator (fun _ => (1:ℝ)) ω := by
  classical
  by_cases hω : ω ∈ ⋃ i ∈ s, E i
  · rw [Set.indicator_of_mem hω]
    obtain ⟨i, hi, hωi⟩ := Set.mem_iUnion₂.mp hω
    calc (1:ℝ) = (E i).indicator (fun _ => (1:ℝ)) ω :=
          (Set.indicator_of_mem hωi (fun _ => (1:ℝ))).symm
      _ ≤ ∑ j ∈ s, (E j).indicator (fun _ => (1:ℝ)) ω :=
          Finset.single_le_sum (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
            hi
  · rw [Set.indicator_of_notMem hω]
    exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω

/-- For any events `E₁, …, Eₙ`,
`ℙ(⋃ᵢ Eᵢ) ≤ ∑ᵢ ℙ(Eᵢ)`.

The source proof takes expectations in the indicator inequality (1.14) and uses (1.9)
and linearity; that proof is reproduced here.

**Book Lemma 1.4.1.** -/
theorem union_bound [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    μ.real (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ.real (E i) := by
  classical
  -- Take expectations in (1.14) and use (1.9) on both sides.
  have hleft : μ.real (⋃ i ∈ s, E i)
      = ∫ ω, (⋃ i ∈ s, E i).indicator (fun _ => (1:ℝ)) ω ∂μ :=
    (expectation_indicator _ (MeasurableSet.biUnion s.countable_toSet hE)).symm
  have hright : ∑ i ∈ s, μ.real (E i)
      = ∫ ω, ∑ i ∈ s, (E i).indicator (fun _ => (1:ℝ)) ω ∂μ := by
    rw [integral_finsetSum s fun i hi =>
      (integrable_indicator_iff (hE i hi)).mpr (integrableOn_const (measure_ne_top μ _))]
    exact Finset.sum_congr rfl fun i hi => (expectation_indicator _ (hE i hi)).symm
  rw [hleft, hright]
  refine integral_mono ?_ ?_ (fun ω => indicator_biUnion_le_sum s E ω)
  · exact (integrable_indicator_iff (MeasurableSet.biUnion s.countable_toSet hE)).mpr
      (integrableOn_const (measure_ne_top μ _))
  · exact integrable_finsetSum s fun i hi =>
      (integrable_indicator_iff (hE i hi)).mpr (integrableOn_const (measure_ne_top μ _))

/-- Union bound over a `Fintype` index (form used at the source Proposition 2.5.1).

**Book Lemma 1.4.1.** -/
theorem union_bound_fintype [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) :
    μ.real (⋃ i, E i) ≤ ∑ i, μ.real (E i) := by
  have := union_bound (μ := μ) Finset.univ E (fun i _ => hE i)
  simpa using this

/-- Lean implementation helper for the source Example 1.4.2 ("a little computation"):
if `n ≥ 2`, `0 ≤ p ≤ 1` and `p ≥ 4 ln n / n`, then `n(1−p)^{n−1} ≤ 1/n`.
Implicit source claim (the omitted computation in the proof of Example 1.4.2).

**Book Example 1.4.2.** -/
lemma example_1_4_2_calc {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 4 * Real.log n / n ≤ p) :
    (n : ℝ) * (1 - p) ^ (n - 1) ≤ 1 / n := by
  have hn0 : (0:ℝ) < n := by positivity
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast le_trans (by norm_num : (1:ℕ) ≤ 2) hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  -- Step 1: `(1-p)^(n-1) ≤ exp (-(p * (n-1)))` from `1 - p ≤ e^{-p}`.
  have h1p : (1 : ℝ) - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  have hstep1 : (1 - p) ^ (n - 1) ≤ Real.exp (-(p * (n - 1 : ℕ))) := by
    calc (1 - p) ^ (n - 1) ≤ Real.exp (-p) ^ (n - 1) :=
          pow_le_pow_left₀ (by linarith) h1p _
      _ = Real.exp (-(p * (n - 1 : ℕ))) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  -- Step 2: `2 log n ≤ p (n-1)` since `p ≥ 4 log n / n` and `(n-1)/n ≥ 1/2`.
  have hn1' : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    have : (1:ℕ) ≤ n := le_trans (by norm_num) hn
    push_cast [this]
    ring
  have hstep2 : 2 * Real.log n ≤ p * ((n - 1 : ℕ) : ℝ) := by
    rw [← hn1']
    have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc 2 * Real.log n = (4 * Real.log n / n) * (n / 2) := by
          rw [div_mul_div_comm,
            show 4 * Real.log ↑n * ↑n = (2 * Real.log ↑n) * (↑n * 2) by ring]
          exact (mul_div_cancel_right₀ _ (by positivity)).symm
      _ ≤ p * ((n:ℝ) - 1) := by
          apply mul_le_mul hp hhalf (by positivity)
          exact hp0
  -- Step 3: conclude.
  have hexp : Real.exp (-(p * ((n - 1 : ℕ) : ℝ))) ≤ Real.exp (-(2 * Real.log n)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlog : Real.exp (-(2 * Real.log n)) = 1 / (n:ℝ)^2 := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log n = Real.log ((n:ℝ)^2) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_log (by positivity)]
    exact (one_div _).symm
  calc (n : ℝ) * (1 - p) ^ (n - 1) ≤ (n:ℝ) * Real.exp (-(p * ((n - 1 : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hstep1 hn0.le
    _ ≤ (n:ℝ) * (1 / (n:ℝ)^2) := by
        rw [← hlog]
        exact mul_le_mul_of_nonneg_left hexp hn0.le
    _ = 1 / n := by
        field_simp

/-- Explicit source declaration (example with proof), formalized in abstract form: if each of
`n ≥ 2` "friendless" events has probability `(1−p)^{n−1}` and `p ≥ 4 ln n / n`, then with
probability at least `1 − 1/n` none of them occurs. (The random-graph model itself is
constructed in Chapter 2, §2.5; the source proof of this example only uses the value of
`ℙ(Eᵢ)`, the union bound, and the computation `example_1_4_2_calc`.)

**Book Example 1.4.2.** -/
theorem example_1_4_2 [IsProbabilityMeasure μ] {n : ℕ} {p : ℝ} (hn : 2 ≤ n)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 4 * Real.log n / n ≤ p)
    (E : Fin n → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hprob : ∀ i, μ.real (E i) = (1 - p) ^ (n - 1)) :
    1 - 1/(n:ℝ) ≤ μ.real (⋃ i, E i)ᶜ := by
  have hbound : μ.real (⋃ i, E i) ≤ 1/(n:ℝ) := by
    calc μ.real (⋃ i, E i) ≤ ∑ i, μ.real (E i) := union_bound_fintype E hE
      _ = (n : ℝ) * (1 - p) ^ (n - 1) := by
          simp [hprob, Finset.sum_const, Finset.card_univ]
      _ ≤ 1/n := example_1_4_2_calc hn hp0 hp1 hp
  have hcompl : μ.real (⋃ i, E i)ᶜ = 1 - μ.real (⋃ i, E i) := by
    rw [measureReal_compl (MeasurableSet.iUnion fun i => hE i), probReal_univ]
  rw [hcompl]
  linarith

/-- Instantiated in the shared finite Erdős–Rényi model.
This is the source-facing concrete statement; `example_1_4_2` above isolates its
union-bound calculation for reuse.

**Book Example 1.4.2.** -/
theorem example_1_4_2_erdosRenyi {n : ℕ} (p : Set.Icc (0 : ℝ) 1) (hn : 2 ≤ n)
    (hp : 4 * Real.log n / n ≤ (p : ℝ)) :
    1 - 1 / (n : ℝ) ≤ (HDP.erdosRenyi n p).real
      {G | ∀ v : Fin n, HDP.degree v G ≠ 0} := by
  have h := example_1_4_2 (μ := HDP.erdosRenyi n p) hn p.2.1 p.2.2 hp
    (fun v : Fin n ↦ HDP.isolated v) (fun v ↦ HDP.isolated_measurable v)
    (fun v ↦ HDP.isolated_probability p v)
  convert h using 1
  congr 1
  ext G
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
  exact forall_congr' fun v ↦ not_congr (HDP.isolated_iff_degree_eq_zero v G).symm

/-! ## §1.5 Conditioning -/

/-- The conditional probability `ℙ(E∣F) = ℙ(E∩F)/ℙ(F)`.
Mathlib correspondence: `ProbabilityTheory.cond` (notation `μ[|F]`), converted to the
book's real-valued quotient form. (When `ℙ(F) = 0` both sides are the junk value `0`.)

**Book Section 1.5.** -/
lemma cond_real_def [IsFiniteMeasure μ] {F : Set Ω} (hF : MeasurableSet F) (E : Set Ω) :
    (μ[|F]).real E = μ.real (E ∩ F) / μ.real F := by
  rw [measureReal_def, cond_apply hF, measureReal_def, measureReal_def,
    Set.inter_comm E F, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [div_eq_inv_mul]

/-- `𝔼X = 𝔼[𝔼[X∣Y]]`.

Source location: Chapter 1, §1.5. Explicit source statement (no proof in source; complete
Lean proof via Mathlib's `integral_condExp`). Conditioning on the random variable `Y` is
formalized as conditioning on the σ-algebra `comap Y` it generates.

**Book Equation (1.15).** -/
theorem law_of_total_expectation [IsProbabilityMeasure μ] {β : Type*}
    [MeasurableSpace β] {Y : Ω → β} {X : Ω → ℝ} (hY : Measurable Y) :
    ∫ ω, (μ[X | MeasurableSpace.comap Y ‹MeasurableSpace β›]) ω ∂μ = ∫ ω, X ω ∂μ :=
  integral_condExp hY.comap_le

/-- Source remark that conditional expectation and (1.15) extend to
random vectors. The codomain may be any real Banach space, so this covers the
finite-dimensional random-vector use without a coordinatewise workaround.

**Book Equation (1.15).** -/
theorem law_of_total_expectation_vector [IsProbabilityMeasure μ]
    {β E : Type*} [MeasurableSpace β] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Y : Ω → β} {X : Ω → E}
    (hY : Measurable Y) :
    ∫ ω, (μ[X | MeasurableSpace.comap Y ‹MeasurableSpace β›]) ω ∂μ =
      ∫ ω, X ω ∂μ :=
  integral_condExp hY.comap_le

/-- The conditional probability of an event given a random variable,
`ℙ(E∣Y):= 𝔼[𝟏_E ∣ Y]`. Implicit source definition.

**Book Equation (1.16).** -/
noncomputable def condProbGiven (E : Set Ω) {β : Type*} [MeasurableSpace β]
    (Y : Ω → β) (μ : Measure Ω) : Ω → ℝ :=
  μ[E.indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap Y ‹MeasurableSpace β›]

/-- `ℙ(E) = 𝔼[ℙ(E∣Y)]`. Explicit source statement (derived in the
source from (1.15) and (1.9); same derivation here).

**Book Equation (1.16).** -/
theorem law_of_total_probability_rv [IsProbabilityMeasure μ] {β : Type*}
    [MeasurableSpace β] {Y : Ω → β} (hY : Measurable Y) {E : Set Ω}
    (hE : MeasurableSet E) :
    μ.real E = ∫ ω, condProbGiven E Y μ ω ∂μ := by
  rw [condProbGiven, law_of_total_expectation hY, expectation_indicator E hE]

/-- If the sample space is decomposed into
countably many pairwise disjoint events `Fᵢ`, then
`ℙ(E) = ∑ᵢ ℙ(E∣Fᵢ)ℙ(Fᵢ)`.

Explicit source statement (the source derives it from (1.16); the Lean proof uses
countable additivity directly, which is mathematically equivalent — both amount to
splitting `E` over the partition). Terms with `ℙ(Fᵢ) = 0` vanish on both sides.

**Book Equation (1.17).** -/
theorem law_of_total_probability [IsProbabilityMeasure μ] {ι : Type*} [Countable ι]
    {F : ι → Set Ω} (hF : ∀ i, MeasurableSet (F i))
    (hdisj : Pairwise (Function.onFun Disjoint F)) (hcover : (⋃ i, F i) = Set.univ)
    {E : Set Ω} (hE : MeasurableSet E) :
    μ.real E = ∑' i, (μ[|F i]).real E * μ.real (F i) := by
  classical
  have hsplit : μ.real E = ∑' i, μ.real (E ∩ F i) := by
    have h1 : E = ⋃ i, E ∩ F i := by
      rw [← Set.inter_iUnion, hcover, Set.inter_univ]
    have h2 : μ E = ∑' i, μ (E ∩ F i) := by
      conv_lhs => rw [h1]
      exact measure_iUnion (fun i j hij => (hdisj hij).mono
        Set.inter_subset_right Set.inter_subset_right) (fun i => hE.inter (hF i))
    rw [measureReal_def, h2, ENNReal.tsum_toReal_eq (fun i => measure_ne_top μ _)]
    rfl
  rw [hsplit]
  congr 1
  funext i
  by_cases hFi : μ (F i) = 0
  · have h0 : μ.real (F i) = 0 := by simp [measureReal_def, hFi]
    have h0' : μ.real (E ∩ F i) = 0 := by
      rw [measureReal_def, measure_inter_null_of_null_right E hFi]
      simp
    rw [h0, h0', mul_zero]
  · rw [cond_real_def (hF i) E]
    rw [div_mul_cancel₀]
    intro h0
    exact hFi (by
      rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (by finiteness)] at h0)

/-- Explicit source declaration (example with proof). Let `X₁, …, Xₙ` be independent
Rademacher random variables and `a₁, …, aₙ` real numbers with `a_{i₀} ≠ 0` for some `i₀`
(the source says "not all zero" and reduces to this case by reordering). Then
`ℙ{∑ᵢ aᵢXᵢ = 0} ≤ 1/2`.

The source proof conditions on `X₁, …, X_{n−1}`; the Lean proof implements the same
argument by splitting off the `i₀` term and integrating the Rademacher atom bound
`ℙ{X_{i₀} = u} ≤ 1/2` against the law of the remaining sum (Fubini on the product
measure given by independence).

**Book Example 1.5.1.** -/
theorem example_1_5_1 [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    {a : Fin n → ℝ} (hX : ∀ i, IsRademacher (X i) μ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {i₀ : Fin n} (ha : a i₀ ≠ 0) :
    μ.real {ω | ∑ i, a i * X i ω = 0} ≤ 1/2 := by
  classical
  -- Work with the scaled family `Y i = a i * X i`.
  set Y : Fin n → Ω → ℝ := fun i ω => a i * X i ω with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => (hXm i).const_mul (a i)
  have hYindep : iIndepFun Y μ :=
    hindep.comp (fun i x => a i * x) (fun i => measurable_const_mul (a i))
  -- Split off the `i₀` term: `∑ᵢ Yᵢ = S + Y_{i₀}` with `S` independent of `Y_{i₀}`.
  set s : Finset (Fin n) := Finset.univ.erase i₀ with hs
  set S : Ω → ℝ := fun ω => ∑ i ∈ s, Y i ω with hS
  have hSm : Measurable S := by
    apply Finset.measurable_sum
    exact fun i _ => hYm i
  have hsum : ∀ ω, ∑ i, a i * X i ω = S ω + Y i₀ ω := by
    intro ω
    have h1 : ∑ i, Y i ω = S ω + Y i₀ ω := by
      simp only [hS]
      exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i₀)).symm
    exact h1
  have hSV : IndepFun S (Y i₀) μ := by
    have h := hYindep.indepFun_finsetSum_of_notMem hYm
      (s := s) (i := i₀) (Finset.notMem_erase i₀ Finset.univ)
    have hfun : (∑ j ∈ s, Y j) = S := by
      funext ω
      simp [hS, Finset.sum_apply]
    rwa [hfun] at h
  -- Atom bound for `Y i₀ = a i₀ · X i₀` in `ℝ≥0∞` form.
  have hatom : ∀ c : ℝ, (μ.map (Y i₀)) {c} ≤ 1/2 := by
    intro c
    have hpre : (μ.map (Y i₀)) {c} = μ {ω | X i₀ ω = c / a i₀} := by
      rw [Measure.map_apply (hYm i₀) (measurableSet_singleton c)]
      congr 1
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hY]
      rw [eq_div_iff ha, mul_comm (X i₀ ω) (a i₀)]
    rw [hpre]
    have hre := (hX i₀).real_atom_le_half (c / a i₀)
    have hne : μ {ω | X i₀ ω = c / a i₀} ≠ ⊤ := by finiteness
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
    exact ENNReal.le_ofReal_iff_toReal_le hne (by norm_num) |>.mpr hre
  -- Rewrite the event via the product measure and integrate the atom bound.
  have hset : {ω | ∑ i, a i * X i ω = 0}
      = (fun ω => (S ω, Y i₀ ω)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0} := by
    ext ω
    simp [hsum ω]
  have hmeas_diag : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 = 0} :=
    (measurable_fst.add measurable_snd) (measurableSet_singleton 0)
  have hmap : μ {ω | ∑ i, a i * X i ω = 0}
      = ((μ.map S).prod (μ.map (Y i₀))) {q : ℝ × ℝ | q.1 + q.2 = 0} := by
    rw [hset, ← hSV.map_prod_eq_prod_map_map hSm.aemeasurable (hYm i₀).aemeasurable,
      Measure.map_apply (hSm.prodMk (hYm i₀)) hmeas_diag]
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  have : IsProbabilityMeasure (μ.map (Y i₀)) :=
    Measure.isProbabilityMeasure_map (hYm i₀).aemeasurable
  have hprod : ((μ.map S).prod (μ.map (Y i₀))) {q : ℝ × ℝ | q.1 + q.2 = 0} ≤ 1/2 := by
    rw [Measure.prod_apply hmeas_diag]
    have hslice : ∀ u : ℝ,
        (μ.map (Y i₀)) (Prod.mk u ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0}) ≤ 1/2 := by
      intro u
      have : Prod.mk u ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0} = {-u} := by
        ext v
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro h; linarith
        · intro h; rw [h]; ring
      rw [this]
      exact hatom (-u)
    calc ∫⁻ u, (μ.map (Y i₀)) (Prod.mk u ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0})
          ∂(μ.map S) ≤ ∫⁻ _, 1/2 ∂(μ.map S) := lintegral_mono hslice
      _ = 1/2 := by simp
  have hle : μ {ω | ∑ i, a i * X i ω = 0} ≤ 1/2 := hmap.le.trans hprod
  rw [measureReal_def]
  calc (μ {ω | ∑ i, a i * X i ω = 0}).toReal ≤ ((1:ℝ≥0∞)/2).toReal :=
        ENNReal.toReal_mono (by norm_num) hle
    _ = 1/2 := by norm_num

/-- Sharpness after the source Example 1.5.1. If the only two nonzero coefficients are
equal to the same `a ≠ 0`, then two independent Rademacher signs cancel with
probability exactly `1/2`.

**Book Example 1.5.1.** -/
theorem example_1_5_1_sharp [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : HDP.IsRademacher X μ) (hY : HDP.IsRademacher Y μ)
    (hXm : Measurable X) (hYm : Measurable Y) (hindep : IndepFun X Y μ)
    {a : ℝ} (ha : a ≠ 0) :
    μ.real {ω | a * X ω + a * Y ω = 0} = 1 / 2 := by
  let A : Set Ω := {ω | X ω = 1 ∧ Y ω = -1}
  let B : Set Ω := {ω | X ω = -1 ∧ Y ω = 1}
  have haiff (u v : ℝ) : a * u + a * v = 0 ↔ u + v = 0 := by
    rw [← mul_add]
    constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left ha
    · intro h
      rw [h, mul_zero]
  have hAE : (({ω | a * X ω + a * Y ω = 0} : Set Ω) : Ω → Prop) =ᵐ[μ]
      ((A ∪ B : Set Ω) : Ω → Prop) := by
    filter_upwards [hX.ae_mem, hY.ae_mem] with ω hωX hωY
    apply propext
    change (a * X ω + a * Y ω = 0) ↔
      ((X ω = 1 ∧ Y ω = -1) ∨ (X ω = -1 ∧ Y ω = 1))
    rw [haiff]
    rcases hωX with hωX | hωX <;> rcases hωY with hωY | hωY <;>
      norm_num [hωX, hωY]
  have hXprob (u : ℝ) (hu : u = 1 ∨ u = -1) :
      μ.real (X ⁻¹' {u}) = 1 / 2 := by
    rw [measureReal_def, ← Measure.map_apply_of_aemeasurable hX.aemeasurable
      (measurableSet_singleton u), hX.map_eq, bernoulliMeasure_apply _
      (measurableSet_singleton u)]
    rcases hu with rfl | rfl <;> norm_num
  have hYprob (u : ℝ) (hu : u = 1 ∨ u = -1) :
      μ.real (Y ⁻¹' {u}) = 1 / 2 := by
    rw [measureReal_def, ← Measure.map_apply_of_aemeasurable hY.aemeasurable
      (measurableSet_singleton u), hY.map_eq, bernoulliMeasure_apply _
      (measurableSet_singleton u)]
    rcases hu with rfl | rfl <;> norm_num
  have hA : μ.real A = 1 / 4 := by
    have h := hindep.measure_inter_preimage_eq_mul ({1} : Set ℝ) ({-1} : Set ℝ)
      (measurableSet_singleton 1) (measurableSet_singleton (-1))
    change μ (X ⁻¹' {1} ∩ Y ⁻¹' {-1}) = _ at h
    have hAset : A = X ⁻¹' {1} ∩ Y ⁻¹' {-1} := by
      ext
      simp [A]
    rw [measureReal_def, hAset, h, ENNReal.toReal_mul,
      ← measureReal_def, ← measureReal_def, hXprob 1 (Or.inl rfl),
      hYprob (-1) (Or.inr rfl)]
    norm_num
  have hB : μ.real B = 1 / 4 := by
    have h := hindep.measure_inter_preimage_eq_mul ({-1} : Set ℝ) ({1} : Set ℝ)
      (measurableSet_singleton (-1)) (measurableSet_singleton 1)
    change μ (X ⁻¹' {-1} ∩ Y ⁻¹' {1}) = _ at h
    have hBset : B = X ⁻¹' {-1} ∩ Y ⁻¹' {1} := by
      ext
      simp [B]
    rw [measureReal_def, hBset, h, ENNReal.toReal_mul,
      ← measureReal_def, ← measureReal_def, hXprob (-1) (Or.inr rfl),
      hYprob 1 (Or.inl rfl)]
    norm_num
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hωA hωB
    simp only [A, B, Set.mem_setOf_eq] at hωA hωB
    linarith [hωA.1, hωB.1]
  have hBmeas : MeasurableSet B := by
    exact (hXm (measurableSet_singleton (-1))).inter
      (hYm (measurableSet_singleton 1))
  calc
    μ.real {ω | a * X ω + a * Y ω = 0} = μ.real (A ∪ B) := by
      exact congrArg ENNReal.toReal (measure_congr hAE)
    _ = μ.real A + μ.real B := measureReal_union hdisj hBmeas
    _ = 1 / 2 := by rw [hA, hB]; norm_num

end HDP.Chapter1


/-!
# Book Chapter 1, Section 1.6

Jensen, monotonicity and triangle inequalities for random-variable norms, integrated
tails, Markov's inequality, and Chebyshev's inequality. The source is PDF pages
23–24 (printed 15–16).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace HDP.Chapter1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Jensen's inequality -/

/-- For real random variables: for a convex function
`f: ℝ → ℝ` and an integrable random variable `X` with `f(X)` integrable,
`f(𝔼X) ≤ 𝔼 f(X)`.

Explicit source statement. The source proves the finitely-many-values case in
Exercise 1.3 and says "the general case can be deduced by approximation"; the Lean proof
uses Mathlib's `ConvexOn.map_integral_le` (mathematically equivalent; continuity of a
convex function on `ℝ` is automatic and supplied by `ConvexOn.continuousOn`).

**Book Equation (1.18).** -/
theorem jensen_inequality [IsProbabilityMeasure μ] {X : Ω → ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hX : Integrable X μ)
    (hfX : Integrable (fun ω => f (X ω)) μ) :
    f (∫ ω, X ω ∂μ) ≤ ∫ ω, f (X ω) ∂μ :=
  hf.map_integral_le (hf.continuousOn isOpen_univ) isClosed_univ
    (Filter.Eventually.of_forall fun _ω => Set.mem_univ _) hX hfX

/-- General form for random vectors in `ℝⁿ`: for a convex
`f: ℝⁿ → ℝ` and an integrable random vector `X` with `f(X)` integrable,
`f(𝔼X) ≤ 𝔼 f(X)`. Explicit source statement ("More generally, (1.18) holds for any
random vector...").

**Book Equation (1.18).** -/
theorem jensen_inequality_vector [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hX : Integrable X μ)
    (hfX : Integrable (fun ω => f (X ω)) μ) :
    f (∫ ω, X ω ∂μ) ≤ ∫ ω, f (X ω) ∂μ :=
  hf.map_integral_le (hf.continuousOn isOpen_univ) isClosed_univ
    (Filter.Eventually.of_forall fun _ω => Set.mem_univ _) hX hfX

/-- Jensen's inequality for concave functions on `[0,∞)` (implicit source variant, needed
for Exercise 1.14 and used via the hint to Exercise 1.11): `𝔼 g(X) ≤ g(𝔼X)`.

**Book Equation (1.18).** -/
theorem jensen_inequality_concave [IsProbabilityMeasure μ] {X : Ω → ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) (hgc : ContinuousOn g (Set.Ici 0))
    (hX0 : 0 ≤ᵐ[μ] X) (hX : Integrable X μ)
    (hgX : Integrable (fun ω => g (X ω)) μ) :
    ∫ ω, g (X ω) ∂μ ≤ g (∫ ω, X ω ∂μ) :=
  hg.le_map_integral hgc isClosed_Ici (by filter_upwards [hX0] with ω h using h) hX hgX

/-- `‖𝔼X‖ ≤ 𝔼‖X‖` for a random vector `X` (Jensen applied to the norm,
which is a convex function). Explicit source statement; Mathlib correspondence via
`norm_integral_le_integral_norm`.

**Book Equation (1.19).** -/
theorem norm_expectation_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Ω → E) : ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ :=
  norm_integral_le_integral_norm X

/-! ## Monotonicity of `L^p` norms: Book (1.20) = Exercise 1.11(a) -/

/-- Mathlib correspondence form: on a probability space, `eLpNorm` is
monotone in the exponent (including `p` or `q` equal to `∞`). Explicit
source statement.

**Book Equation (1.20).** -/
theorem exercise_1_11a_eLpNorm [IsProbabilityMeasure μ] {X : Ω → ℝ} {p q : ℝ≥0∞}
    (hpq : p ≤ q) (hX : AEStronglyMeasurable X μ) :
    eLpNorm X p μ ≤ eLpNorm X q μ :=
  eLpNorm_le_eLpNorm_of_exponent_le hpq hX

/-- Source form: `‖X‖_{L^p} ≤ ‖X‖_{L^q}` whenever
`0 < p ≤ q < ∞` and `X ∈ L^q`. (The `L^q`-membership hypothesis is needed for the
real-valued formulation; the `eLpNorm` form above is unconditional.)

**Book Equation (1.20).** -/
theorem exercise_1_11a [IsProbabilityMeasure μ] {X : Ω → ℝ} {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) (hX : MemLp X (ENNReal.ofReal q) μ) :
    lpNormRV X p μ ≤ lpNormRV X q μ := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hXp : MemLp X (ENNReal.ofReal p) μ :=
    hX.mono_exponent (ENNReal.ofReal_le_ofReal hpq)
  rw [lpNormRV_eq_toReal_eLpNorm hp hXp,
    lpNormRV_eq_toReal_eLpNorm hq hX]
  exact ENNReal.toReal_mono hX.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)
      hX.aestronglyMeasurable)

/-- With `q = ∞`: `‖X‖_{L^p} ≤ ‖X‖_{L^∞}` for a bounded random variable.

**Book Equation (1.20).** -/
theorem exercise_1_11a_top [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hX : MemLp X ⊤ μ) :
    lpNormRV X p μ ≤ (eLpNorm X ⊤ μ).toReal := by
  have hXp : MemLp X (ENNReal.ofReal p) μ := hX.mono_exponent le_top
  rw [lpNormRV_eq_toReal_eLpNorm hp hXp]
  exact ENNReal.toReal_mono hX.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le le_top hX.aestronglyMeasurable)

/-! ## Minkowski's inequality: Book (1.21) -/

/-- Mathlib correspondence form: the triangle
inequality for `eLpNorm`, valid for all `p ∈ [1,∞]` with no integrability hypotheses.

**Book Equation (1.21).** -/
theorem minkowski_eLpNorm {X Y : Ω → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (fun ω => X ω + Y ω) p μ ≤ eLpNorm X p μ + eLpNorm Y p μ :=
  eLpNorm_add_le hX hY hp

/-- Source form: for `1 ≤ p < ∞` and
`X, Y ∈ L^p`, `‖X+Y‖_{L^p} ≤ ‖X‖_{L^p} + ‖Y‖_{L^p}`. Explicit source statement.

**Book Equation (1.21).** -/
theorem minkowski_Lp {X Y : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hX : MemLp X (ENNReal.ofReal p) μ) (hY : MemLp Y (ENNReal.ofReal p) μ) :
    lpNormRV (fun ω => X ω + Y ω) p μ ≤ lpNormRV X p μ + lpNormRV Y p μ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hXY : AEStronglyMeasurable (fun ω => X ω + Y ω) μ :=
    hX.aestronglyMeasurable.add hY.aestronglyMeasurable
  have hXYmem : MemLp (fun ω => X ω + Y ω) (ENNReal.ofReal p) μ := hX.add hY
  rw [lpNormRV_eq_toReal_eLpNorm hp0 hXYmem,
    lpNormRV_eq_toReal_eLpNorm hp0 hX,
    lpNormRV_eq_toReal_eLpNorm hp0 hY]
  have h1p : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have htri := eLpNorm_add_le hX.aestronglyMeasurable hY.aestronglyMeasurable h1p
  calc (eLpNorm (fun ω => X ω + Y ω) (ENNReal.ofReal p) μ).toReal
      ≤ (eLpNorm X (ENNReal.ofReal p) μ + eLpNorm Y (ENNReal.ofReal p) μ).toReal :=
        ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨hX.eLpNorm_ne_top, hY.eLpNorm_ne_top⟩) htri
    _ = _ := ENNReal.toReal_add hX.eLpNorm_ne_top hY.eLpNorm_ne_top

/-! ## Cauchy–Schwarz and Hölder: Book (1.22) -/

/-- For conjugate exponents
`1 < p, p′ < ∞` and `X ∈ L^p`, `Y ∈ L^{p′}`,
`‖XY‖_{L¹} = 𝔼|XY| ≤ ‖X‖_{L^p} ‖Y‖_{L^{p′}}`.

Explicit source statement; Mathlib correspondence via
`MeasureTheory.integral_mul_norm_le_Lp_mul_Lq`. The endpoint cases `(1,∞)`, `(∞,1)`
(conventions in the §1.2 footnote) are `holder_rv_top` below.

**Book Equation (1.22).** -/
theorem holder_rv {X Y : Ω → ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hX : MemLp X (ENNReal.ofReal p) μ) (hY : MemLp Y (ENNReal.ofReal q) μ) :
    ∫ ω, |X ω * Y ω| ∂μ ≤ lpNormRV X p μ * lpNormRV Y q μ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hpq hX hY
  simp only [Real.norm_eq_abs] at h
  calc ∫ ω, |X ω * Y ω| ∂μ = ∫ ω, |X ω| * |Y ω| ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => abs_mul _ _)
    _ ≤ (∫ ω, |X ω| ^ p ∂μ) ^ (1/p) * (∫ ω, |Y ω| ^ q ∂μ) ^ (1/q) := h
    _ = lpNormRV X p μ * lpNormRV Y q μ := rfl

/-- Endpoint case `(p, p′) = (1, ∞)`: `𝔼|XY| ≤ ‖X‖_{L¹}·‖Y‖_{L^∞}`.
Explicit source statement (footnote conventions `1/0 = ∞`, `1/∞ = 0`).

**Book Equation (1.22).** -/
theorem holder_rv_top {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : MemLp Y ⊤ μ) :
    ∫ ω, |X ω * Y ω| ∂μ ≤ (∫ ω, |X ω| ∂μ) * (eLpNorm Y ⊤ μ).toReal := by
  set M := (eLpNorm Y ⊤ μ).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hYle : ∀ᵐ ω ∂μ, |Y ω| ≤ M := by
    filter_upwards [MeasureTheory.ae_le_eLpNormEssSup (f := Y) (μ := μ)] with ω hω
    have h1 : ENNReal.ofReal |Y ω| ≤ eLpNorm Y ⊤ μ := by
      rw [eLpNorm_exponent_top, ← Real.enorm_eq_ofReal_abs]
      exact hω
    calc |Y ω| = (ENNReal.ofReal |Y ω|).toReal :=
          (ENNReal.toReal_ofReal (abs_nonneg _)).symm
      _ ≤ M := ENNReal.toReal_mono hY.eLpNorm_ne_top h1
  have hbound : ∀ᵐ ω ∂μ, |X ω * Y ω| ≤ |X ω| * M := by
    filter_upwards [hYle] with ω hω
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  have hXabs : Integrable (fun ω => |X ω|) μ := hX.abs
  have hXM : Integrable (fun ω => |X ω| * M) μ := hXabs.mul_const M
  have hXYm : AEStronglyMeasurable (fun ω => |X ω * Y ω|) μ := by
    have h1 : AEStronglyMeasurable (fun ω => X ω * Y ω) μ :=
      hX.aestronglyMeasurable.mul hY.aestronglyMeasurable
    simpa [Real.norm_eq_abs] using h1.norm
  have hXYint : Integrable (fun ω => |X ω * Y ω|) μ := by
    refine hXM.mono' hXYm ?_
    filter_upwards [hbound] with ω hω
    calc ‖|X ω * Y ω|‖ = |X ω * Y ω| := by rw [Real.norm_eq_abs, abs_abs]
      _ ≤ |X ω| * M := hω
  calc ∫ ω, |X ω * Y ω| ∂μ ≤ ∫ ω, |X ω| * M ∂μ :=
        integral_mono_ae hXYint hXM hbound
    _ = (∫ ω, |X ω| ∂μ) * M := by rw [integral_mul_const]

/-- Endpoint case `(p, p′) = (∞, 1)`. This is stated separately so
the two endpoint conventions in the source are both visible in the public API.

**Book Equation (1.22).** -/
theorem holder_top_rv {X Y : Ω → ℝ} (hX : MemLp X ⊤ μ) (hY : Integrable Y μ) :
    ∫ ω, |X ω * Y ω| ∂μ ≤
      (eLpNorm X ⊤ μ).toReal * ∫ ω, |Y ω| ∂μ := by
  simpa [mul_comm] using (holder_rv_top (μ := μ) (X := Y) (Y := X) hY hX)

/-- Cauchy–Schwarz inequality for random variables:
`‖XY‖_{L¹} ≤ ‖X‖_{L²}‖Y‖_{L²}`. Explicit unnumbered source statement (the case
`p = p′ = 2` of Hölder).

**Book Equation (1.22).** -/
theorem cauchy_schwarz_rv {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, |X ω * Y ω| ∂μ ≤ lpNormRV X 2 μ * lpNormRV Y 2 μ := by
  have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
  exact holder_rv (Real.HolderConjugate.two_two) (h2 ▸ hX) (h2 ▸ hY)

/-! ## CDF and tails -/

/-- The cumulative distribution function `F_X(t) = ℙ{X ≤ t}`.
Implicit source definition.

**Book Section 1.6.** -/
noncomputable def bookCDF (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ.real {ω | X ω ≤ t}

/-- Tails and the CDF, `ℙ{X > t} = 1 − F_X(t)`.
Explicit unnumbered source statement.

**Book Section 1.6.** -/
theorem tail_eq_one_sub_cdf [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (t : ℝ) :
    μ.real {ω | t < X ω} = 1 - bookCDF X μ t := by
  have hc : {ω | t < X ω} = {ω | X ω ≤ t}ᶜ := by
    ext ω
    simp [not_le]
  rw [hc, bookCDF]
  have hms : NullMeasurableSet {ω | X ω ≤ t} μ :=
    (hX.nullMeasurableSet_preimage measurableSet_Iic)
  rw [measureReal_compl₀ hms, probReal_univ]

/-! ## The integrated tail formula: Book Lemma 1.6.1 -/

/-- `∫⁻` form covering the source's claim
that "the two sides are either finite or infinite simultaneously": for a nonnegative
random variable, `𝔼X = ∫₀^∞ ℙ{X > t} dt` as an identity in `[0,∞]`.

Source location: Chapter 1, §1.6 (PDF page 24). Explicit source declaration; the source
proof (write `x = ∫₀^∞ 𝟏_{t<x} dt` and apply Fubini–Tonelli) is exactly Mathlib's
layer-cake proof, used here via `lintegral_eq_lintegral_meas_lt`.

**Book Lemma 1.6.1.** -/
theorem integrated_tail_formula_lintegral {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X)
    (hX : AEMeasurable X μ) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ∫⁻ t in Set.Ioi (0:ℝ), μ {ω | t < X ω} :=
  lintegral_eq_lintegral_meas_lt μ hX0 hX

/-- Bochner form: for an integrable
nonnegative random variable, `𝔼X = ∫₀^∞ ℙ{X > t} dt`. Explicit source declaration;
Mathlib correspondence via `Integrable.integral_eq_integral_meas_lt`.

**Book Lemma 1.6.1.** -/
theorem integrated_tail_formula {X : Ω → ℝ} (hX : Integrable X μ) (hX0 : 0 ≤ᵐ[μ] X) :
    ∫ ω, X ω ∂μ = ∫ t in Set.Ioi (0:ℝ), μ.real {ω | t < X ω} :=
  hX.integral_eq_integral_meas_lt hX0

/-! ## Markov and Chebyshev: Book Proposition 1.6.2 and Corollary 1.6.3 -/

/-- For a nonnegative (integrable) random variable `X` and
`t > 0`, `ℙ{X ≥ t} ≤ 𝔼X / t`. The source proof (split `x = x𝟏_{x≥t} + x𝟏_{x<t}` and
drop the second term) is mathematically the same restriction argument implemented by
Mathlib's `mul_meas_ge_le_integral_of_nonneg`, used via the Prelude wrapper.

**Book Proposition 1.6.2.** -/
theorem markov_inequality {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hX : Integrable X μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ X ω} ≤ (∫ ω, X ω ∂μ) / t :=
  HDP.markov_real hX0 hX ht

/-- The sharpness assertion immediately following Book Proposition 1.6.2.

For every admissible mean `m ≤ t`, the two-point random variable taking value
`t` with probability `m/t` and zero otherwise has mean `m` and attains equality
in Markov's bound. Thus no smaller universal tail bound can follow from the
mean alone.

**Book §1.6, Markov optimality prose.** -/
theorem markov_inequality_is_sharp {m t : ℝ} (hm : 0 ≤ m) (hmt : m ≤ t)
    (ht : 0 < t) :
    ∃ (p : PMF Bool) (X : Bool → ℝ),
      (∫ b, X b ∂p.toMeasure) = m ∧
      p.toMeasure {b | t ≤ X b} = ENNReal.ofReal (m / t) := by
  have hq0 : 0 ≤ m / t := div_nonneg hm ht.le
  have hq1 : m / t ≤ 1 := (div_le_one ht).2 hmt
  have hsum : ENNReal.ofReal (m / t) + ENNReal.ofReal (1 - m / t) = 1 := by
    rw [← ENNReal.ofReal_add hq0 (sub_nonneg.2 hq1)]
    norm_num
  let p : PMF Bool := PMF.ofFintype
    (fun b ↦ if b then ENNReal.ofReal (m / t) else ENNReal.ofReal (1 - m / t)) (by
      simpa [Fintype.sum_bool] using hsum)
  let X : Bool → ℝ := fun b ↦ if b then t else 0
  refine ⟨p, X, ?_, ?_⟩
  · rw [PMF.integral_eq_sum]
    simp [p, X, ENNReal.toReal_ofReal hq0]
    field_simp
  · have hevent : {b | t ≤ X b} = {true} := by
      ext b
      cases b <;> simp [X, not_le_of_gt ht]
    rw [hevent, PMF.toMeasure_apply_singleton p true (MeasurableSet.singleton true)]
    simp [p]

/-- If `X` has mean `μ₀` and variance `σ²`, then for `t > 0`,
`ℙ{|X − μ₀| ≥ t} ≤ σ²/t²`. The source proof squares both sides and applies Markov to
`(X−μ₀)²`; Mathlib's `meas_ge_le_variance_div_sq` implements exactly this argument.

**Book Corollary 1.6.3.** -/
theorem chebyshev_inequality [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ Var[X; μ] / t^2 := by
  have h := meas_ge_le_variance_div_sq hX ht
  rw [measureReal_def]
  calc (μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|}).toReal
      ≤ (ENNReal.ofReal (Var[X; μ] / t^2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = Var[X; μ] / t^2 :=
        ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (by positivity))

end HDP.Chapter1


/-!
# Book Chapter 1: Moment and finite-dimensional norm inequalities

This core module contains the results of Book Exercises 1.14–1.17 because later
chapters and exercise hints consume them.  Exercise provenance is recorded on
the declarations; no exercise module is imported here.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal BigOperators Topology unitInterval

namespace HDP.Chapter1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Interpolation between `L¹` and `L∞` -/

/-- The explicit `MemLp` hypotheses make every real-valued norm finite, in accordance
with the book-wide `eLpNorm`/`lpNormRV` interface policy.

**Book Exercise 1.12.** -/
theorem exercise_1_12 {X : Ω → ℝ} {p : ℝ} (hp : 1 < p) (hX1 : Integrable X μ)
    (hXp : MemLp X (ENNReal.ofReal p) μ) (hXtop : MemLp X ⊤ μ) :
    lpNormRV X p μ ≤
      (lpNormRV X 1 μ) ^ (1 / p) *
        ((eLpNorm X ⊤ μ).toReal) ^ (1 - 1 / p) := by
  let M : ℝ := (eLpNorm X ⊤ μ).toReal
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hXle : ∀ᵐ ω ∂μ, |X ω| ≤ M := by
    filter_upwards [MeasureTheory.ae_le_eLpNormEssSup (f := X) (μ := μ)] with ω hω
    have hle : ENNReal.ofReal |X ω| ≤ eLpNorm X ⊤ μ := by
      rw [eLpNorm_exponent_top, ← Real.enorm_eq_ofReal_abs]
      exact hω
    calc
      |X ω| = (ENNReal.ofReal |X ω|).toReal :=
        (ENNReal.toReal_ofReal (abs_nonneg _)).symm
      _ ≤ M := ENNReal.toReal_mono hXtop.eLpNorm_ne_top hle
  have hpowle : ∀ᵐ ω ∂μ, |X ω| ^ p ≤ |X ω| * M ^ (p - 1) := by
    filter_upwards [hXle] with ω hω
    by_cases hx : X ω = 0
    · simp [hx, hp0.ne']
    · calc
        |X ω| ^ p = |X ω| ^ (1 + (p - 1)) := by congr 1; ring
        _ = |X ω| ^ (1 : ℝ) * |X ω| ^ (p - 1) :=
          Real.rpow_add (abs_pos.mpr hx) 1 (p - 1)
        _ = |X ω| * |X ω| ^ (p - 1) := by rw [Real.rpow_one]
        _ ≤ |X ω| * M ^ (p - 1) := by
          gcongr
  have hpowInt : Integrable (fun ω => |X ω| ^ p) μ := by
    have h := hXp.integrable_norm_rpow
      (by positivity) ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using h
  have hmajorInt : Integrable (fun ω => |X ω| * M ^ (p - 1)) μ :=
    hX1.abs.mul_const _
  have hintle : (∫ ω, |X ω| ^ p ∂μ) ≤
      (∫ ω, |X ω| ∂μ) * M ^ (p - 1) := by
    calc
      (∫ ω, |X ω| ^ p ∂μ) ≤
          ∫ ω, |X ω| * M ^ (p - 1) ∂μ :=
        integral_mono_ae hpowInt hmajorInt hpowle
      _ = (∫ ω, |X ω| ∂μ) * M ^ (p - 1) := by
        rw [integral_mul_const]
  have hA0 : 0 ≤ ∫ ω, |X ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  rw [lpNormRV]
  have hr := Real.rpow_le_rpow
    (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p)
    hintle (show 0 ≤ 1 / p by positivity)
  calc
    (∫ ω, |X ω| ^ p ∂μ) ^ (1 / p)
        ≤ ((∫ ω, |X ω| ∂μ) * M ^ (p - 1)) ^ (1 / p) := hr
    _ = (∫ ω, |X ω| ∂μ) ^ (1 / p) * M ^ (1 - 1 / p) := by
      rw [Real.mul_rpow hA0 (Real.rpow_nonneg hM0 _), ← Real.rpow_mul hM0]
      congr 2
      field_simp
    _ = ((∫ ω, |X ω| ^ (1 : ℝ) ∂μ) ^ (1 / (1 : ℝ))) ^ (1 / p) *
          M ^ (1 - 1 / p) := by simp

/-- The first inequality in **the source Exercise 1.14 (promoted to core; reused in
later exercise hints)**.

**Book Exercise 1.14.** -/
theorem exercise_1_14_lower {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    {X : ι → Ω → ℝ} (hX : ∀ i, Integrable (X i) μ) :
    lpNorm p (fun i => ∫ ω, X i ω ∂μ) ≤
      ∫ ω, lpNorm p (fun i => X i ω) ∂μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  let Y : Ω → PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) :=
    fun ω => WithLp.toLp (ENNReal.ofReal p) (fun i => X i ω)
  have hYeval (i : ι) : Integrable (fun ω => Y ω i) μ := by
    simpa [Y] using hX i
  have hY : Integrable Y μ := Integrable.of_eval_piLp hYeval
  have hint : (∫ ω, Y ω ∂μ) =
      WithLp.toLp (ENNReal.ofReal p) (fun i => ∫ ω, X i ω ∂μ) := by
    ext i
    rw [eval_integral_piLp hYeval]
  calc
    lpNorm p (fun i => ∫ ω, X i ω ∂μ) = ‖∫ ω, Y ω ∂μ‖ := by
      rw [lpNorm, hint]
    _ ≤ ∫ ω, ‖Y ω‖ ∂μ := norm_integral_le_integral_norm Y
    _ = ∫ ω, lpNorm p (fun i => X i ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rfl

/-- The second inequality in **the source Exercise 1.14 (promoted to core; reused in
later exercise hints)**. The integrability hypotheses
make all three source expectations finite.

**Book Exercise 1.14.** -/
theorem exercise_1_14_upper {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    [IsProbabilityMeasure μ] {X : Fin n → Ω → ℝ}
    (hX0 : ∀ i, 0 ≤ᵐ[μ] X i)
    (hXp : ∀ i, Integrable (fun ω => X i ω ^ p) μ)
    (hroot : Integrable (fun ω => lpNorm p (fun i => X i ω)) μ) :
    (∫ ω, lpNorm p (fun i => X i ω) ∂μ) ≤
      (∑ i, ∫ ω, X i ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, X i ω ^ p
  have hall : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω := ae_all_iff.mpr hX0
  have hS0 : 0 ≤ᵐ[μ] S := by
    filter_upwards [hall] with ω hω
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hω i) p
  have hS : Integrable S μ := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact hXp i
  have hrootEq : (fun ω => lpNorm p (fun i => X i ω)) =ᵐ[μ]
      fun ω => S ω ^ (1 / p) := by
    filter_upwards [hall] with ω hω
    rw [lpNorm_eq_sum hp0]
    congr 2
    funext i
    rw [abs_of_nonneg (hω i)]
  have hroot' : Integrable (fun ω => S ω ^ (1 / p)) μ :=
    hroot.congr hrootEq
  have hj := jensen_inequality_concave
    (X := S) (g := fun x : ℝ => x ^ (1 / p))
    (Real.concaveOn_rpow (by positivity) (by
      apply (div_le_one hp0).2
      exact hp))
    (Real.continuous_rpow_const (by positivity)).continuousOn
    hS0 hS hroot'
  calc
    (∫ ω, lpNorm p (fun i => X i ω) ∂μ) =
        ∫ ω, S ω ^ (1 / p) ∂μ := integral_congr_ae hrootEq
    _ ≤ (∫ ω, S ω ∂μ) ^ (1 / p) := hj
    _ = (∑ i, ∫ ω, X i ω ^ p ∂μ) ^ (1 / p) := by
      congr 1
      rw [show (∫ ω, S ω ∂μ) = ∑ i, ∫ ω, X i ω ^ p ∂μ by
        dsimp [S]
        rw [integral_finsetSum]
        exact fun i _ => hXp i]

/-- With the source's nonnegativity and the explicit
finiteness hypotheses required by real-valued Bochner integrals.

**Book Exercise 1.14.** -/
theorem exercise_1_14 {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    [IsProbabilityMeasure μ] {X : Fin n → Ω → ℝ}
    (hX0 : ∀ i, 0 ≤ᵐ[μ] X i) (hX : ∀ i, Integrable (X i) μ)
    (hXp : ∀ i, Integrable (fun ω => X i ω ^ p) μ)
    (hroot : Integrable (fun ω => lpNorm p (fun i => X i ω)) μ) :
    lpNorm p (fun i => ∫ ω, X i ω ∂μ) ≤
        ∫ ω, lpNorm p (fun i => X i ω) ∂μ ∧
      (∫ ω, lpNorm p (fun i => X i ω) ∂μ) ≤
        (∑ i, ∫ ω, X i ω ^ p ∂μ) ^ (1 / p) :=
  ⟨exercise_1_14_lower hp hX, exercise_1_14_upper hp hX0 hXp hroot⟩

/-! ## Exercise 1.15: corrected integrated-tail identities -/

/-- The printed formula needs integrability
(or two separate extended-valued identities). This is the finite Bochner-integral form.

**Book Exercise 1.15(a--c).** -/
theorem exercise_1_15a {X : Ω → ℝ} (hX : Integrable X μ) :
    (∫ ω, X ω ∂μ) =
      (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω}) -
        ∫ t in Set.Iio (0 : ℝ), μ.real {ω | X ω < t} := by
  let Xp : Ω → ℝ := fun ω => max (X ω) 0
  let Xn : Ω → ℝ := fun ω => max (-X ω) 0
  have hXpEq : Xp = fun ω => (X ω + |X ω|) / 2 := by
    funext ω
    dsimp [Xp]
    rcases le_total 0 (X ω) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
    · rw [max_eq_right h, abs_of_nonpos h]
      ring
  have hXnEq : Xn = fun ω => (|X ω| - X ω) / 2 := by
    funext ω
    dsimp [Xn]
    rcases le_total 0 (X ω) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
      ring
    · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
      ring
  have hXp : Integrable Xp μ := by
    rw [hXpEq]
    exact (hX.add hX.abs).div_const 2
  have hXn : Integrable Xn μ := by
    rw [hXnEq]
    exact (hX.abs.sub hX).div_const 2
  have hXp0 : 0 ≤ᵐ[μ] Xp :=
    Filter.Eventually.of_forall fun ω => by simp [Xp]
  have hXn0 : 0 ≤ᵐ[μ] Xn :=
    Filter.Eventually.of_forall fun ω => by simp [Xn]
  have hpTail := integrated_tail_formula hXp hXp0
  have hnTail := integrated_tail_formula hXn hXn0
  have hpSet (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      {ω | t < Xp ω} = {ω | t < X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Xp, lt_max_iff]
    have ht0 : ¬t < 0 := not_lt_of_ge (le_of_lt ht)
    simp only [ht0, or_false]
  have hnSet (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      {ω | t < Xn ω} = {ω | X ω < -t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Xn, lt_max_iff]
    have ht0 : ¬t < 0 := not_lt_of_ge (le_of_lt ht)
    simp only [ht0, or_false]
    constructor <;> intro h <;> linarith
  have hpTail' : (∫ ω, Xp ω ∂μ) =
      ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω} := by
    rw [hpTail]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change μ.real {ω | t < Xp ω} = μ.real {ω | t < X ω}
    rw [hpSet t ht]
  have hnTail' : (∫ ω, Xn ω ∂μ) =
      ∫ t in Set.Iio (0 : ℝ), μ.real {ω | X ω < t} := by
    rw [hnTail]
    calc
      (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < Xn ω}) =
          ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω < -t} := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            change μ.real {ω | t < Xn ω} = μ.real {ω | X ω < -t}
            rw [hnSet t ht]
      _ = ∫ t in Set.Iic (0 : ℝ), μ.real {ω | X ω < t} := by
        simpa using integral_comp_neg_Ioi (0 : ℝ)
          (fun t : ℝ => μ.real {ω | X ω < t})
      _ = ∫ t in Set.Iio (0 : ℝ), μ.real {ω | X ω < t} :=
        integral_Iic_eq_integral_Iio
  have hdecomp : X = fun ω => Xp ω - Xn ω := by
    funext ω
    rw [hXpEq, hXnEq]
    ring
  calc
    (∫ ω, X ω ∂μ) = ∫ ω, Xp ω - Xn ω ∂μ := by rw [← hdecomp]
    _ = (∫ ω, Xp ω ∂μ) - ∫ ω, Xn ω ∂μ := integral_sub hXp hXn
    _ = _ := by rw [hpTail', hnTail']

/-- Mere differentiability is insufficient.
Here `g` is an a.e.-nonnegative locally integrable derivative and `hfFTC` is the
explicit fundamental-theorem/absolute-continuity hypothesis on `[0,∞)`.

**Book Exercise 1.15(a--c).** -/
theorem exercise_1_15b [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hXmeas : AEMeasurable X μ)
    {f g : ℝ → ℝ}
    (hgInt : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (hg0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] g)
    (hfFTC : ∀ x, 0 ≤ x → f x = ∫ t in (0 : ℝ)..x, g t)
    (hfX : Integrable (fun ω => f (X ω)) μ)
    (hfX0 : 0 ≤ᵐ[μ] fun ω => f (X ω))
    (hrhs : IntegrableOn
      (fun t => μ.real {ω | t < X ω} * g t) (Set.Ioi (0 : ℝ))) :
    (∫ ω, f (X ω) ∂μ) =
      ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω} * g t := by
  have hFTCae : (fun ω => ∫ t in (0 : ℝ)..X ω, g t) =ᵐ[μ]
      fun ω => f (X ω) := by
    filter_upwards [hX0] with ω hω
    exact (hfFTC (X ω) hω).symm
  have hR0 : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t => μ.real {ω | t < X ω} * g t := by
    filter_upwards [hg0] with t ht
    exact mul_nonneg measureReal_nonneg ht
  have hRInt : Integrable
      (fun t => μ.real {ω | t < X ω} * g t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := hrhs
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ hX0 hXmeas hgInt hg0
  have hrightAE : (fun t =>
      μ {ω | t < X ω} * ENNReal.ofReal (g t)) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun t => ENNReal.ofReal (μ.real {ω | t < X ω} * g t) := by
    filter_upwards [hg0] with t ht
    rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hleft0 : 0 ≤ ∫ ω, f (X ω) ∂μ := integral_nonneg_of_ae hfX0
  have hright0 : 0 ≤
      ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω} * g t :=
    integral_nonneg_of_ae hR0
  apply (ENNReal.ofReal_eq_ofReal_iff hleft0 hright0).mp
  calc
    ENNReal.ofReal (∫ ω, f (X ω) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (f (X ω)) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hfX hfX0
    _ = ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..X ω, g t) ∂μ := by
      apply lintegral_congr_ae
      exact hFTCae.fun_comp ENNReal.ofReal |>.symm
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
        μ {ω | t < X ω} * ENNReal.ofReal (g t) := hlayer
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (μ.real {ω | t < X ω} * g t) :=
      lintegral_congr_ae hrightAE
    _ = ENNReal.ofReal
        (∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t < X ω} * g t) :=
      (ofReal_integral_eq_lintegral_ofReal hRInt hR0).symm

/-- The absolute-moment tail formula. The explicit
integrability hypotheses select the finite real-valued version of the source identity.

**Book Exercise 1.15(a--c).** -/
theorem exercise_1_15c [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {p : ℝ} (hp : 0 < p)
    (hpow : Integrable (fun ω => |X ω| ^ p) μ)
    (hrhs : IntegrableOn
      (fun t => μ.real {ω | t < |X ω|} * (p * t ^ (p - 1)))
      (Set.Ioi (0 : ℝ))) :
    (∫ ω, |X ω| ^ p ∂μ) =
      ∫ t in Set.Ioi (0 : ℝ),
        μ.real {ω | t < |X ω|} * (p * t ^ (p - 1)) := by
  let Y : Ω → ℝ := fun ω => |X ω|
  let g : ℝ → ℝ := fun t => p * t ^ (p - 1)
  have hY0 : 0 ≤ᵐ[μ] Y :=
    Filter.Eventually.of_forall fun ω => abs_nonneg (X ω)
  have hYmeas : AEMeasurable Y μ := by
    simpa [Y, Real.norm_eq_abs] using hX.norm
  have hgInt : ∀ t > 0, IntervalIntegrable g volume 0 t := by
    intro t ht
    exact (intervalIntegral.intervalIntegrable_rpow'
      (show -1 < p - 1 by linarith)).const_mul p
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt ht) _)
  have hFTC : ∀ x, 0 ≤ x → x ^ p = ∫ t in (0 : ℝ)..x, g t := by
    intro x hx
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < p - 1))]
    rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp.ne']
    field_simp
    ring
  have hpow0 : 0 ≤ᵐ[μ] fun ω => Y ω ^ p :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _
  simpa only [Y, g] using
    (exercise_1_15b (X := Y) hY0 hYmeas
      (f := fun x => x ^ p) (g := g) hgInt hg0 hFTC hpow hpow0 hrhs)

/-! ## Exercise 1.16 -/

/-- Paley--Zygmund inequality.

**Book Exercise 1.16.** -/
theorem exercise_1_16 [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : 0 ≤ᵐ[μ] X) (hX2 : MemLp X 2 μ)
    (ε : I) :
    (1 - (ε : ℝ)) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 /
        (∫ ω, (X ω) ^ 2 ∂μ) ≤
      μ.real {ω | (ε : ℝ) * (∫ ω', X ω' ∂μ) < X ω} := by
  let m : ℝ := ∫ ω, X ω ∂μ
  let s : ℝ := ∫ ω, (X ω) ^ 2 ∂μ
  let A : Set Ω := {ω | (ε : ℝ) * m < X ω}
  let Y : Ω → ℝ := A.indicator (fun _ => 1)
  have hXint : Integrable X μ := hX2.integrable (by norm_num)
  have hm0 : 0 ≤ m := integral_nonneg_of_ae hX0
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_const hXm
  have hY2 : MemLp Y 2 μ := by
    exact memLp_indicator_const 2 hA 1 (Or.inr (measure_ne_top μ A))
  have hYint : Integrable Y μ := hY2.integrable (by norm_num)
  have hXYint : Integrable (fun ω => |X ω * Y ω|) μ := by
    have hInd : Integrable (A.indicator fun ω => |X ω|) μ := hXint.abs.indicator hA
    apply hInd.congr
    filter_upwards [] with ω
    by_cases hω : ω ∈ A <;> simp [Y, Set.indicator, hω]
  have hlower : (1 - (ε : ℝ)) * m ≤ ∫ ω, |X ω * Y ω| ∂μ := by
    have hmajor : ∀ᵐ ω ∂μ,
        X ω ≤ |X ω * Y ω| + (ε : ℝ) * m := by
      filter_upwards [hX0] with ω hω0
      by_cases hω : ω ∈ A
      · have hY : Y ω = 1 := by
          change A.indicator (fun _ => 1) ω = 1
          rw [Set.indicator_of_mem hω]
        rw [hY, mul_one, abs_of_nonneg hω0]
        exact le_add_of_nonneg_right (mul_nonneg ε.2.1 hm0)
      · have hle : X ω ≤ (ε : ℝ) * m := by
          exact le_of_not_gt hω
        simpa [Y, Set.indicator, hω] using hle
    have hR : Integrable (fun ω => |X ω * Y ω| + (ε : ℝ) * m) μ :=
      hXYint.add (integrable_const _)
    have hi := integral_mono_ae hXint hR hmajor
    simp only [integral_add hXYint (integrable_const ((ε : ℝ) * m)),
      integral_const, probReal_univ, one_smul] at hi
    linarith
  have hupper : (∫ ω, |X ω * Y ω| ∂μ) ≤
      lpNormRV X 2 μ * lpNormRV Y 2 μ :=
    cauchy_schwarz_rv hX2 hY2
  have hxSq : (lpNormRV X 2 μ) ^ 2 = s := by
    rw [sq_lpNormRV_two_eq_l2InnerRV hX2]
    dsimp [s, l2InnerRV]
    apply integral_congr_ae
    filter_upwards [] with ω
    ring
  have hySq : (lpNormRV Y 2 μ) ^ 2 = μ.real A := by
    rw [sq_lpNormRV_two_eq_l2InnerRV hY2]
    dsimp [l2InnerRV]
    calc
      (∫ ω, Y ω * Y ω ∂μ) = ∫ ω, Y ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hω : ω ∈ A <;> simp [Y, hω]
      _ = μ.real A := expectation_indicator A hA
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact integral_nonneg fun ω => sq_nonneg _
  have hd0 : 0 ≤ (1 - (ε : ℝ)) * m :=
    mul_nonneg (sub_nonneg.mpr ε.2.2) hm0
  have hnx0 : 0 ≤ lpNormRV X 2 μ := by
    rw [lpNormRV]
    positivity
  have hny0 : 0 ≤ lpNormRV Y 2 μ := by
    rw [lpNormRV]
    positivity
  have hprod : (1 - (ε : ℝ)) * m ≤
      lpNormRV X 2 μ * lpNormRV Y 2 μ := hlower.trans hupper
  have hsq : ((1 - (ε : ℝ)) * m) ^ 2 ≤ s * μ.real A := by
    calc
      ((1 - (ε : ℝ)) * m) ^ 2 ≤
          (lpNormRV X 2 μ * lpNormRV Y 2 μ) ^ 2 := by nlinarith
      _ = s * μ.real A := by rw [mul_pow, hxSq, hySq]
  change (1 - (ε : ℝ)) ^ 2 * m ^ 2 / s ≤ μ.real A
  by_cases hs : s = 0
  · simp [hs]
  · apply (div_le_iff₀ (lt_of_le_of_ne hs0 (Ne.symm hs))).2
    nlinarith [hsq]

/-! ## Exercise 1.17 -/

/-- For counting measure, the real value of `eLpNorm'`—the `'_count_toReal`
quantity—equals the finite-dimensional ℓᵖ norm.

**Lean implementation helper.** -/
private lemma eLpNorm'_count_toReal_eq_lpNorm
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    (eLpNorm' x p Measure.count).toReal = lpNorm p x := by
  rw [eLpNorm'_eq_lintegral_enorm, lpNorm_eq_sum hp]
  rw [lintegral_count, tsum_fintype]
  simp_rw [Real.enorm_eq_ofReal_abs]
  rw [← ENNReal.toReal_rpow]
  congr 1
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]
  · intro i _
    exact ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top

/-- For finite exponents. The printed lower endpoint
`p = 0` is omitted because the chapter has no `ℓ⁰` norm.

**Book Equation (1.4).** -/
theorem exercise_1_17_finite {ι : Type*} [Fintype ι]
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (x : ι → ℝ) :
    lpNorm q x ≤ lpNorm p x ∧
      lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p - 1 / q) * lpNorm q x := by
  constructor
  · exact lpNorm_anti hp hpq x
  · letI : MeasurableSpace ι := ⊤
    have hp0 : 0 < p := zero_lt_one.trans_le hp
    have hq0 : 0 < q := hp0.trans_le hpq
    have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
      (f := x) (μ := Measure.count) hp0 hpq
      (measurable_of_finite x).aestronglyMeasurable
    have hfin : eLpNorm' x q Measure.count *
        (Measure.count : Measure ι) (Set.univ : Set ι) ^ (1 / p - 1 / q) ≠ ∞ := by
      apply ENNReal.mul_ne_top
      · rw [eLpNorm', lintegral_count, tsum_fintype]
        apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
        exact ENNReal.sum_ne_top.mpr fun i _ =>
          ENNReal.rpow_ne_top_of_nonneg hq0.le enorm_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · exact sub_nonneg.mpr (one_div_le_one_div_of_le hp0 hpq)
        · simp
    have hr := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_mul, eLpNorm'_count_toReal_eq_lpNorm hp0,
      eLpNorm'_count_toReal_eq_lpNorm hq0] at hr
    simpa [Measure.count_apply_finite, ← ENNReal.toReal_rpow, mul_comm] using hr

/-- `ell^p` norms decrease as `p` increases.

**Book Equation (1.4).** -/
theorem exercise_1_17_top {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 ≤ p) (x : ι → ℝ) :
    linftyNorm x ≤ lpNorm p x ∧
      lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * linftyNorm x := by
  constructor
  · rw [linftyNorm_le_iff (lpNorm_nonneg (zero_lt_one.trans_le hp) x)]
    exact fun i => abs_apply_le_lpNorm hp x i
  · letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    have hp0 : 0 < p := zero_lt_one.trans_le hp
    have h := PiLp.lipschitzWith_toLp
      (p := ENNReal.ofReal p) (fun _ : ι => ℝ) x 0
    have hr := ENNReal.toReal_mono (by finiteness) h
    simpa [lpNorm, linftyNorm, ENNReal.toReal_ofReal hp0.le, toReal_enorm] using hr

/- Exercise 1.17(b) consists only of explicit extremizer constructions; under the
exercise policy it is recorded here without adding a witness declaration. -/

/- The non-load-bearing Exercise 1.18 remains in `Chapter1.Exercise.Sec06`. -/

/- Exercise 1.19's body-level duality declarations live only in
`Chapter1.«02_Norms»`; this core module deliberately adds no wrapper aliases. -/

end HDP.Chapter1


/-!
# Book Chapter 1: Erdős--Rényi isolated-vertex thresholds

This core module contains Book Exercises 1.9 and 1.10 because the Chapter 1
notes and Chapter 2 consume their conclusions.  Their exercise provenance is
recorded on the declarations; no exercise module is imported here.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal BigOperators Topology unitInterval

namespace HDP.Chapter1

/-- The event that a concrete Erdős--Rényi graph has no isolated vertex.

**Lean implementation helper.** -/
def noIsolatedVertices (n : ℕ) : Set (HDP.ERSample n) :=
  {G | ∀ v : Fin n, G ∉ HDP.isolated v}

/-- The event that some vertex is isolated.

**Lean implementation helper.** -/
def hasIsolatedVertex (n : ℕ) : Set (HDP.ERSample n) :=
  ⋃ v : Fin n, HDP.isolated v

/-- Having no isolated vertices is the complement of having at least one isolated vertex.

**Lean implementation helper.** -/
lemma noIsolatedVertices_eq_compl (n : ℕ) :
    noIsolatedVertices n = (hasIsolatedVertex n)ᶜ := by
  ext G
  simp [noIsolatedVertices, hasIsolatedVertex]

/-- The event that at least one vertex is isolated is measurable.

**Lean implementation helper.** -/
lemma hasIsolatedVertex_measurable (n : ℕ) : MeasurableSet (hasIsolatedVertex n) :=
  MeasurableSet.iUnion fun v => HDP.isolated_measurable v

/-! Exercises 1.9 and 1.10 -/

/-- The probability that a fixed vertex is isolated in the Erdős–Rényi graph has the stated exponential bound.

**Lean implementation helper.** -/
lemma hasIsolatedVertex_bound (n : ℕ) (p : I) :
    (HDP.erdosRenyi n p).real (hasIsolatedVertex n) ≤
      (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) := by
  calc
    (HDP.erdosRenyi n p).real (hasIsolatedVertex n)
        ≤ ∑ v : Fin n, (HDP.erdosRenyi n p).real (HDP.isolated v) :=
      union_bound_fintype _ fun v => HDP.isolated_measurable v
    _ = (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) := by
      simp_rw [HDP.isolated_probability]
      simp

/-- Under the intended eventual threshold
`pₙ > (1+ε) log(n)/n`, the concrete Erdős--Rényi graph has no isolated
vertices with probability tending to one.

**Book Exercise 1.9--1.10.** -/
theorem exercise_1_9 {p : ℕ → I} {ε : ℝ} (hε : 0 < ε)
    (hp : ∀ᶠ n : ℕ in atTop, (1 + ε) * Real.log n / n < (p n : ℝ)) :
    Tendsto (fun n => (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ n : ℕ in atTop, 2 / ε ≤ Real.log (n : ℝ) :=
    hlog.eventually (eventually_ge_atTop (2 / ε))
  have hnLarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hupper : ∀ᶠ n : ℕ in atTop,
      (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n) ≤
        (n : ℝ) ^ (-ε / 2) := by
    filter_upwards [hp, hlogLarge, hnLarge] with n hpn hln hn
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hsrc : (1 + ε) * Real.log n < (p n : ℝ) * n := by
      rwa [div_lt_iff₀ hnpos] at hpn
    have hgap : 1 ≤ (ε / 2) * Real.log n := by
      have := mul_le_mul_of_nonneg_left hln hε.le
      field_simp at this ⊢
      linarith
    have hprod : (1 + ε / 2) * Real.log n ≤
        (p n : ℝ) * (n - 1 : ℕ) := by
      rw [Nat.cast_sub hn1]
      have hp1 : (p n : ℝ) ≤ 1 := (p n).2.2
      nlinarith
    calc
      (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n)
          ≤ (n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1) :=
        hasIsolatedVertex_bound n (p n)
      _ ≤ (n : ℝ) * (Real.exp (-(p n : ℝ))) ^ (n - 1) := by
        gcongr
        · exact sub_nonneg.mpr (p n).2.2
        · exact Real.one_sub_le_exp_neg _
      _ = (n : ℝ) * Real.exp (-(p n : ℝ) * (n - 1 : ℕ)) := by
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ (n : ℝ) * Real.exp (-(1 + ε / 2) * Real.log n) := by
        apply mul_le_mul_of_nonneg_left _ hnpos.le
        exact Real.exp_le_exp.mpr (by linarith)
      _ = (n : ℝ) ^ (-ε / 2) := by
        rw [show -(1 + ε / 2) * Real.log n =
          Real.log n * (-(1 + ε / 2)) by ring, Real.exp_mul,
          Real.exp_log hnpos]
        calc
          (n : ℝ) * (n : ℝ) ^ (-(1 + ε / 2)) =
              (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 + ε / 2)) := by
                rw [Real.rpow_one]
          _ = (n : ℝ) ^ ((1 : ℝ) + (-(1 + ε / 2))) :=
            (Real.rpow_add hnpos _ _).symm
          _ = (n : ℝ) ^ (-ε / 2) := by congr 1; ring
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε / 2)) atTop (𝓝 0) := by
    have hbase := (tendsto_rpow_neg_atTop (show 0 < ε / 2 by positivity)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa [Function.comp_def, neg_div] using hbase
  have hiso : Tendsto
      (fun n => (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n)) atTop (𝓝 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun n => measureReal_nonneg)
      hupper hpow
  have hcompl : ∀ n,
      (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n) =
        1 - (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n) := by
    intro n
    rw [noIsolatedVertices_eq_compl, measureReal_compl (hasIsolatedVertex_measurable n),
      probReal_univ]
  have hdiff : Tendsto
      (fun n => 1 - (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n))
      atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hiso)
  exact hdiff.congr' (Filter.Eventually.of_forall fun n => (hcompl n).symm)

/-! Exercise 1.10 is developed below. -/

/-- The finite set of all edges incident to a fixed vertex.

**Lean implementation helper.** -/
private noncomputable def incidentEdgeFinset {n : ℕ} (v : Fin n) :
    Finset (HDP.EREdge n) :=
  Finset.univ.image (HDP.incidentEdge v)

/-- Characterizes membership in the finite set of edges incident to a vertex.

**Lean implementation helper.** -/
private lemma mem_incidentEdgeFinset {n : ℕ} (v : Fin n) (e : HDP.EREdge n) :
    e ∈ incidentEdgeFinset v ↔ v ∈ e.1 := by
  constructor
  · rintro h
    rw [incidentEdgeFinset, Finset.mem_image] at h
    obtain ⟨w, -, rfl⟩ := h
    exact Sym2.mem_mk_left _ _
  · intro hv
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    have hwne : w ≠ v := by
      intro hwv
      apply e.2
      rw [hw, hwv, Sym2.mk_isDiag_iff]
    rw [incidentEdgeFinset, Finset.mem_image]
    refine ⟨⟨w, hwne⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact hw.symm

/-- A vertex in an `n`-vertex loopless graph has exactly `n - 1` possible incident edges.

**Lean implementation helper.** -/
private lemma card_incidentEdgeFinset {n : ℕ} (v : Fin n) :
    (incidentEdgeFinset v).card = n - 1 := by
  rw [incidentEdgeFinset, Finset.card_image_of_injective _ (HDP.incidentEdge_injective v)]
  simp

/-- The intersection of the incident-edge sets of two distinct vertices is their common edge.

**Lean implementation helper.** -/
private lemma incidentEdgeFinset_inter {n : ℕ} {v w : Fin n} (hvw : v ≠ w) :
    incidentEdgeFinset v ∩ incidentEdgeFinset w =
      {HDP.incidentEdge v ⟨w, hvw.symm⟩} := by
  ext e
  simp only [Finset.mem_inter, mem_incidentEdgeFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hw⟩
    apply Subtype.ext
    exact (Sym2.mem_and_mem_iff hvw).mp ⟨hv, hw⟩
  · intro he
    subst e
    exact ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩

/-- Two distinct vertices have `2 * n - 3` edges incident to at least one of them.

**Lean implementation helper.** -/
private lemma card_incidentEdgeFinset_union {n : ℕ} (hn : 2 ≤ n)
    {v w : Fin n} (hvw : v ≠ w) :
    (incidentEdgeFinset v ∪ incidentEdgeFinset w).card = 2 * n - 3 := by
  have hcard := Finset.card_union_add_card_inter (incidentEdgeFinset v) (incidentEdgeFinset w)
  rw [card_incidentEdgeFinset, card_incidentEdgeFinset,
    incidentEdgeFinset_inter hvw, Finset.card_singleton] at hcard
  omega

/-- The event that every edge in a finite family is absent.

**Lean implementation helper.** -/
private def edgesAbsent {n : ℕ} (s : Finset (HDP.EREdge n)) :
    Set (HDP.ERSample n) :=
  ⋂ e ∈ s, HDP.edgeIndicator e ⁻¹' {0}

/-- A vertex is isolated exactly when all of its incident edges are absent.

**Lean implementation helper.** -/
private lemma isolated_eq_edgesAbsent {n : ℕ} (v : Fin n) :
    HDP.isolated v = edgesAbsent (incidentEdgeFinset v) := by
  ext G
  simp only [HDP.isolated, edgesAbsent, Set.mem_setOf_eq, Set.mem_iInter,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h e he
    rw [mem_incidentEdgeFinset] at he
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp he
    have hwne : w ≠ v := by
      intro hwv
      exact e.2 (by rw [hw, hwv, Sym2.mk_isDiag_iff])
    have hedge : e = HDP.incidentEdge v ⟨w, hwne⟩ := by
      apply Subtype.ext
      exact hw
    rw [hedge]
    exact h ⟨w, hwne⟩
  · intro h w
    exact h (HDP.incidentEdge v w) (by
      rw [mem_incidentEdgeFinset]
      exact Sym2.mem_mk_left _ _)

/-- The event that two incident-edge families are absent splits into the absence of their union with the shared edge counted once.

**Lean implementation helper.** -/
private lemma edgesAbsent_inter {n : ℕ} (s t : Finset (HDP.EREdge n)) :
    edgesAbsent s ∩ edgesAbsent t = edgesAbsent (s ∪ t) := by
  ext G
  simp only [edgesAbsent, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hs, ht⟩ e he
    rcases Finset.mem_union.mp he with he | he
    · exact hs e he
    · exact ht e he
  · intro hu
    constructor
    · intro e he
      exact hu e (Finset.mem_union_left _ he)
    · intro e he
      exact hu e (Finset.mem_union_right _ he)

/-- The probability that every edge in a finite family is absent is `(1-p)` raised to the family size.

**Lean implementation helper.** -/
private lemma edgesAbsent_probability {n : ℕ} (p : I) (s : Finset (HDP.EREdge n)) :
    (HDP.erdosRenyi n p).real (edgesAbsent s) =
      (1 - (p : ℝ)) ^ s.card := by
  have h := (HDP.edgeIndicator_independent p).measure_inter_preimage_eq_mul
    (S := s) (sets := fun _ : HDP.EREdge n => ({0} : Set ℝ)) (by simp)
  rw [edgesAbsent, measureReal_def, h, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, HDP.edge_absent_probability]
  simp

/-- Two distinct vertices are simultaneously isolated with probability `(1-p)^(2n-3)`.

**Lean implementation helper.** -/
private lemma isolated_pair_probability {n : ℕ} (hn : 2 ≤ n) (p : I)
    {v w : Fin n} (hvw : v ≠ w) :
    (HDP.erdosRenyi n p).real (HDP.isolated v ∩ HDP.isolated w) =
      (1 - (p : ℝ)) ^ (2 * n - 3) := by
  rw [isolated_eq_edgesAbsent, isolated_eq_edgesAbsent,
    edgesAbsent_inter, edgesAbsent_probability, card_incidentEdgeFinset_union hn hvw]

/-- The `0`/`1` indicator that a vertex is isolated.

**Lean implementation helper.** -/
noncomputable def isolatedIndicator {n : ℕ} (v : Fin n) : HDP.ERSample n → ℝ :=
  (HDP.isolated v).indicator (fun _ => 1)

/-- The number of isolated vertices, viewed as a real-valued random variable.

**Lean implementation helper.** -/
noncomputable def isolatedCount (n : ℕ) : HDP.ERSample n → ℝ :=
  fun G => ∑ v : Fin n, isolatedIndicator v G

/-- The indicator of a fixed vertex's isolation event is integrable.

**Lean implementation helper.** -/
private lemma isolatedIndicator_integrable {n : ℕ} (p : I) (v : Fin n) :
    Integrable (isolatedIndicator v) (HDP.erdosRenyi n p) := by
  exact (integrable_const 1).indicator (HDP.isolated_measurable v)

/-- The expected isolated-vertex indicator equals the isolation probability `(1-p)^(n-1)`.

**Lean implementation helper.** -/
private lemma isolatedIndicator_integral {n : ℕ} (p : I) (v : Fin n) :
    ∫ G, isolatedIndicator v G ∂(HDP.erdosRenyi n p) =
      (1 - (p : ℝ)) ^ (n - 1) := by
  rw [isolatedIndicator, integral_indicator (HDP.isolated_measurable v)]
  simp [HDP.isolated_probability]

/-- The product of two isolated-vertex indicators is the indicator that both vertices are isolated.

**Lean implementation helper.** -/
private lemma isolatedIndicator_mul_eq {n : ℕ} (v w : Fin n) :
    (fun G => isolatedIndicator v G * isolatedIndicator w G) =
      (HDP.isolated v ∩ HDP.isolated w).indicator (fun _ => 1) := by
  funext G
  by_cases hv : G ∈ HDP.isolated v <;> by_cases hw : G ∈ HDP.isolated w <;>
    simp [isolatedIndicator, Set.indicator, hv, hw]

/-- The product moment of two isolated-vertex indicators uses the one-vertex probability on the diagonal and the two-vertex probability off the diagonal.

**Lean implementation helper.** -/
private lemma isolatedIndicator_mul_integral {n : ℕ} (hn : 2 ≤ n) (p : I)
    (v w : Fin n) :
    ∫ G, isolatedIndicator v G * isolatedIndicator w G ∂(HDP.erdosRenyi n p) =
      if v = w then (1 - (p : ℝ)) ^ (n - 1)
      else (1 - (p : ℝ)) ^ (2 * n - 3) := by
  by_cases hvw : v = w
  · subst w
    have hsq : (fun G => isolatedIndicator v G * isolatedIndicator v G) =
        isolatedIndicator v := by
      funext G
      simp [isolatedIndicator, Set.indicator]
    rw [hsq, isolatedIndicator_integral]
    simp
  · rw [if_neg hvw]
    rw [isolatedIndicator_mul_eq, integral_indicator]
    · simp [isolated_pair_probability hn p hvw]
    · exact (HDP.isolated_measurable v).inter (HDP.isolated_measurable w)

/-- The expected number of isolated vertices is `n(1-p)^(n-1)`.

**Lean implementation helper.** -/
private lemma isolatedCount_integral {n : ℕ} (p : I) :
    ∫ G, isolatedCount n G ∂(HDP.erdosRenyi n p) =
      (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) := by
  change (∫ G, ∑ v : Fin n, isolatedIndicator v G ∂(HDP.erdosRenyi n p)) = _
  rw [integral_finsetSum Finset.univ]
  · simp_rw [isolatedIndicator_integral]
    simp
  · intro v _
    exact isolatedIndicator_integrable p v

/-- Summing `a` at one distinguished index and `b` elsewhere gives
`a + (n - 1) * b`.

**Lean implementation helper.** -/
private lemma sum_if_eq_fin {n : ℕ} (v : Fin n) (a b : ℝ) :
    ∑ w : Fin n, (if v = w then a else b) = a + (n - 1 : ℕ) * b := by
  rw [Finset.sum_ite]
  have hEq : Finset.univ.filter (fun w : Fin n => v = w) = {v} := by
    ext w
    simp [eq_comm]
  have hNe : Finset.univ.filter (fun w : Fin n => ¬v = w) = Finset.univ.erase v := by
    ext w
    simp [eq_comm]
  rw [hEq, hNe]
  simp

/-- The second moment of the isolated-vertex count splits into diagonal and distinct-vertex contributions.

**Lean implementation helper.** -/
private lemma isolatedCount_sq_integral {n : ℕ} (hn : 2 ≤ n) (p : I) :
    ∫ G, (isolatedCount n G) ^ 2 ∂(HDP.erdosRenyi n p) =
      (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) +
        (n : ℝ) * (n - 1 : ℕ) * (1 - (p : ℝ)) ^ (2 * n - 3) := by
  have hprodInt (v w : Fin n) :
      Integrable (fun G => isolatedIndicator v G * isolatedIndicator w G)
        (HDP.erdosRenyi n p) := by
    rw [isolatedIndicator_mul_eq]
    exact (integrable_const 1).indicator
      ((HDP.isolated_measurable v).inter (HDP.isolated_measurable w))
  calc
    ∫ G, (isolatedCount n G) ^ 2 ∂(HDP.erdosRenyi n p)
        = ∫ G, ∑ v : Fin n, ∑ w : Fin n,
            isolatedIndicator v G * isolatedIndicator w G ∂(HDP.erdosRenyi n p) := by
          congr 1
          funext G
          simp only [isolatedCount, pow_two, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ v : Fin n, ∑ w : Fin n,
          ∫ G, isolatedIndicator v G * isolatedIndicator w G
            ∂(HDP.erdosRenyi n p) := by
          rw [integral_finsetSum Finset.univ]
          · apply Finset.sum_congr rfl
            intro v _
            rw [integral_finsetSum Finset.univ]
            exact fun w _ => hprodInt v w
          · intro v _
            exact integrable_finsetSum Finset.univ fun w _ => hprodInt v w
    _ = ∑ v : Fin n, ∑ w : Fin n,
          if v = w then (1 - (p : ℝ)) ^ (n - 1)
          else (1 - (p : ℝ)) ^ (2 * n - 3) := by
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro w _
          exact isolatedIndicator_mul_integral hn p v w
    _ = (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) +
        (n : ℝ) * (n - 1 : ℕ) * (1 - (p : ℝ)) ^ (2 * n - 3) := by
          calc
            ∑ v : Fin n, ∑ w : Fin n,
                (if v = w then (1 - (p : ℝ)) ^ (n - 1)
                else (1 - (p : ℝ)) ^ (2 * n - 3)) =
              ∑ _v : Fin n, ((1 - (p : ℝ)) ^ (n - 1) +
                (n - 1 : ℕ) * (1 - (p : ℝ)) ^ (2 * n - 3)) := by
                  apply Finset.sum_congr rfl
                  intro v _
                  exact sum_if_eq_fin v _ _
            _ = _ := by simp; ring

/-- The number of isolated vertices has a finite second moment.

**Lean implementation helper.** -/
private lemma isolatedCount_memLp_two {n : ℕ} (p : I) :
    MemLp (isolatedCount n) 2 (HDP.erdosRenyi n p) := by
  refine ⟨?_, eLpNorm_lt_top_of_finite⟩
  change AEStronglyMeasurable (fun G => ∑ v : Fin n, isolatedIndicator v G)
    (HDP.erdosRenyi n p)
  have h : AEStronglyMeasurable (∑ v : Fin n, isolatedIndicator v)
      (HDP.erdosRenyi n p) :=
    Finset.aestronglyMeasurable_sum Finset.univ fun v _ =>
      (isolatedIndicator_integrable p v).aestronglyMeasurable
  have heq : (∑ v : Fin n, isolatedIndicator v) =
      (fun G => ∑ v : Fin n, isolatedIndicator v G) := by
    funext G
    rw [Finset.sum_apply]
  rw [← heq]
  exact h

/-- The isolated-vertex count satisfies `zero_iff`: it vanishes exactly when
the graph has no isolated vertices.

**Lean implementation helper.** -/
private lemma isolatedCount_eq_zero_iff {n : ℕ} (G : HDP.ERSample n) :
    isolatedCount n G = 0 ↔ G ∈ noIsolatedVertices n := by
  constructor
  · intro h v hv
    have hi0 : isolatedIndicator v G = 0 := by
      have hiff := Fintype.sum_eq_zero_iff_of_nonneg
        (f := fun i : Fin n => isolatedIndicator i G)
        (fun i => by
          by_cases hi : G ∈ HDP.isolated i <;>
            simp [isolatedIndicator, Set.indicator, hi])
      exact congrFun ((hiff.mp (by simpa [isolatedCount] using h))) v
    simp [isolatedIndicator, Set.indicator, hv] at hi0
  · intro h
    simp only [isolatedCount]
    apply Fintype.sum_eq_zero
    intro v
    simp [isolatedIndicator, Set.indicator, h v]

/-- The variance of the isolated-vertex count is its explicit second moment minus the square of its mean.

**Lean implementation helper.** -/
private lemma isolatedCount_variance {n : ℕ} (hn : 2 ≤ n) (p : I) :
    Var[isolatedCount n; HDP.erdosRenyi n p] =
      (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) +
        (n : ℝ) * (n - 1 : ℕ) * (1 - (p : ℝ)) ^ (2 * n - 3) -
          ((n : ℝ) * (1 - (p : ℝ)) ^ (n - 1)) ^ 2 := by
  rw [variance_eq_sub (isolatedCount_memLp_two p), isolatedCount_integral]
  congr 1
  simpa only [Pi.pow_apply] using isolatedCount_sq_integral hn p

/-- The variance-to-mean-squared ratio of the isolated-vertex count is bounded by the reciprocal mean plus `p/(1-p)`.

**Lean implementation helper.** -/
private lemma isolatedCount_variance_ratio_le {n : ℕ} (hn : 2 ≤ n) (p : I)
    (hp1 : (p : ℝ) < 1) :
    Var[isolatedCount n; HDP.erdosRenyi n p] /
        ((n : ℝ) * (1 - (p : ℝ)) ^ (n - 1)) ^ 2
      ≤ 1 / ((n : ℝ) * (1 - (p : ℝ)) ^ (n - 1)) +
        (p : ℝ) / (1 - (p : ℝ)) := by
  let a : ℝ := 1 - (p : ℝ)
  let A : ℝ := a ^ (n - 1)
  have ha : 0 < a := sub_pos.mpr hp1
  have hn0 : (0 : ℝ) < n := by positivity
  have hA : 0 < A := pow_pos ha _
  have hexp : 2 * n - 3 + 1 = 2 * (n - 1) := by omega
  have hB : a ^ (2 * n - 3) = A ^ 2 / a := by
    apply (eq_div_iff ha.ne').2
    rw [← pow_succ, hexp, mul_comm, pow_mul]
  rw [isolatedCount_variance hn p]
  change ((n : ℝ) * A + (n : ℝ) * (n - 1 : ℕ) * a ^ (2 * n - 3) -
      ((n : ℝ) * A) ^ 2) / ((n : ℝ) * A) ^ 2 ≤
        1 / ((n : ℝ) * A) + (p : ℝ) / a
  rw [hB]
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hncast]
  field_simp [hn0.ne', ha.ne', hA.ne']
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have haeq : a = 1 - (p : ℝ) := rfl
  nlinarith

/-- The probability of having no isolated vertices is bounded by the normalized isolated-count variance estimate.

**Lean implementation helper.** -/
private lemma noIsolatedVertices_probability_le {n : ℕ} (hn : 2 ≤ n) (p : I)
    (hp1 : (p : ℝ) < 1) :
    (HDP.erdosRenyi n p).real (noIsolatedVertices n) ≤
      1 / ((n : ℝ) * (1 - (p : ℝ)) ^ (n - 1)) +
        (p : ℝ) / (1 - (p : ℝ)) := by
  let m : ℝ := (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1)
  have hm : 0 < m := mul_pos (by positivity) (pow_pos (sub_pos.mpr hp1) _)
  have hsub : noIsolatedVertices n ⊆
      {G | m ≤ |isolatedCount n G - ∫ G', isolatedCount n G' ∂(HDP.erdosRenyi n p)|} := by
    intro G hG
    rw [← isolatedCount_eq_zero_iff] at hG
    change m ≤ |isolatedCount n G -
      ∫ G', isolatedCount n G' ∂(HDP.erdosRenyi n p)|
    rw [isolatedCount_integral, hG, zero_sub, abs_neg, abs_of_pos hm]
  calc
    (HDP.erdosRenyi n p).real (noIsolatedVertices n)
        ≤ (HDP.erdosRenyi n p).real
          {G | m ≤ |isolatedCount n G -
            ∫ G', isolatedCount n G' ∂(HDP.erdosRenyi n p)|} :=
      measureReal_mono hsub
    _ ≤ Var[isolatedCount n; HDP.erdosRenyi n p] / m ^ 2 :=
      chebyshev_inequality (isolatedCount_memLp_two p) hm
    _ ≤ 1 / ((n : ℝ) * (1 - (p : ℝ)) ^ (n - 1)) +
        (p : ℝ) / (1 - (p : ℝ)) := by
      exact isolatedCount_variance_ratio_le hn p hp1

/-- In the supercritical regime, the reciprocal of the expected isolated-vertex count satisfies the stated decay bound.

**Lean implementation helper.** -/
private lemma isolatedMean_reciprocal_le
    {n : ℕ} (hn : 2 ≤ n) {q ε : ℝ} (hq0 : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (hqe : q ≤ ε / 4) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hthreshold : q * (n : ℝ) < (1 - ε) * Real.log (n : ℝ)) :
    1 / ((n : ℝ) * (1 - q) ^ (n - 1)) ≤ (n : ℝ) ^ (-ε / 2) := by
  let a : ℝ := 1 - q
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have ha : 0 < a := by dsimp [a]; linarith
  have hinv0 : a⁻¹ ≤ 1 + 2 * q := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha).2
    dsimp [a]
    nlinarith
  have hinv : a⁻¹ ≤ 1 + ε / 2 := by linarith
  have hlogLower : -q / a ≤ Real.log a := by
    have h := Real.one_sub_inv_le_log_of_pos ha
    convert h using 1
    dsimp [a] at ha ⊢
    field_simp [ha.ne']; ring
  have hcoef : (1 + ε / 2) * (1 - ε) ≤ 1 - ε / 2 := by nlinarith
  have hexponent : -(1 - ε / 2) * Real.log (n : ℝ) ≤
      (n - 1 : ℕ) * Real.log a := by
    have hnp : (n - 1 : ℕ) * q / a ≤ (1 + ε / 2) * (q * (n : ℝ)) := by
      rw [div_eq_mul_inv]
      have hnsub : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.sub_le n 1
      calc
        ((n - 1 : ℕ) : ℝ) * q * a⁻¹
            ≤ ((n : ℝ) * q) * a⁻¹ := by gcongr
        _ ≤ ((n : ℝ) * q) * (1 + ε / 2) := by gcongr
        _ = (1 + ε / 2) * (q * (n : ℝ)) := by ring
    have hnp' : (n - 1 : ℕ) * q / a <
        (1 - ε / 2) * Real.log (n : ℝ) := by
      calc
        (n - 1 : ℕ) * q / a ≤ (1 + ε / 2) * (q * (n : ℝ)) := hnp
        _ < (1 + ε / 2) * ((1 - ε) * Real.log (n : ℝ)) := by
          exact mul_lt_mul_of_pos_left hthreshold (by linarith)
        _ ≤ (1 - ε / 2) * Real.log (n : ℝ) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hlogn0
    calc
      -(1 - ε / 2) * Real.log (n : ℝ) ≤ -((n - 1 : ℕ) * q / a) := by
        linarith
      _ = (n - 1 : ℕ) * (-q / a) := by ring
      _ ≤ (n - 1 : ℕ) * Real.log a := by gcongr
  have hmean : (n : ℝ) ^ (ε / 2) ≤ (n : ℝ) * a ^ (n - 1) := by
    have hrpowId : (n : ℝ) * Real.exp (-(1 - ε / 2) * Real.log (n : ℝ)) =
        (n : ℝ) ^ (ε / 2) := by
      rw [show -(1 - ε / 2) * Real.log (n : ℝ) =
        Real.log (n : ℝ) * (-(1 - ε / 2)) by ring, Real.exp_mul,
        Real.exp_log hn0]
      calc
        (n : ℝ) * (n : ℝ) ^ (-(1 - ε / 2)) =
            (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 - ε / 2)) := by
              rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((1 : ℝ) + (-(1 - ε / 2))) :=
          (Real.rpow_add hn0 _ _).symm
        _ = (n : ℝ) ^ (ε / 2) := by congr 1; ring
    rw [← hrpowId]
    rw [show a ^ (n - 1) = Real.exp ((n - 1 : ℕ) * Real.log a) by
      rw [Real.exp_nat_mul, Real.exp_log ha]]
    gcongr
  calc
    1 / ((n : ℝ) * (1 - q) ^ (n - 1)) = 1 / ((n : ℝ) * a ^ (n - 1)) := by
      rfl
    _ ≤ 1 / (n : ℝ) ^ (ε / 2) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hn0 _) hmean
    _ = (n : ℝ) ^ (-ε / 2) := by
      rw [one_div, ← Real.rpow_neg (le_of_lt hn0)]
      congr 1
      ring

/-- Under the intended eventual sparse threshold
`pₙ < (1-ε) log(n)/n`, a concrete Erdős--Rényi graph has an isolated
vertex with probability tending to one.

**Book Exercise 1.9--1.10.** -/
theorem exercise_1_10 {p : ℕ → I} {ε : ℝ} (hε0 : 0 < ε)
    (hp : ∀ᶠ n : ℕ in atTop, (p n : ℝ) < (1 - ε) * Real.log n / n) :
    Tendsto (fun n => (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n))
      atTop (𝓝 1) := by
  have hε1 : ε < 1 := by
    by_contra hε
    have hfalse : ∀ᶠ _n : ℕ in atTop, False := by
      filter_upwards [hp, eventually_ge_atTop 2] with n hpn hn
      have hlog0 : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hright : (1 - ε) * Real.log (n : ℝ) / (n : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog0) (by positivity)
      exact (not_lt_of_ge (p n).2.1) (lt_of_lt_of_le hpn hright)
    obtain ⟨_, h⟩ := hfalse.exists
    exact h
  have hlogDivR : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogDiv : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hlogDivR.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hthreshold : Tendsto
      (fun n : ℕ => (1 - ε) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hlogDiv.const_mul (1 - ε)
  have hpzero : Tendsto (fun n : ℕ => (p n : ℝ)) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => (p n).2.1)
      (hp.mono fun _ hn => hn.le) hthreshold
  have hpHalf : ∀ᶠ n : ℕ in atTop, (p n : ℝ) < 1 / 2 :=
    (tendsto_order.1 hpzero).2 (1 / 2) (by norm_num)
  have hpEps : ∀ᶠ n : ℕ in atTop, (p n : ℝ) < ε / 4 :=
    (tendsto_order.1 hpzero).2 (ε / 4) (by positivity)
  have hnLarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hnoUpper : ∀ᶠ n : ℕ in atTop,
      (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n) ≤
        (n : ℝ) ^ (-ε / 2) + 2 * (p n : ℝ) := by
    filter_upwards [hp, hpHalf, hpEps, hnLarge] with n hpn hphalf hpeps hn
    have hn0 : (0 : ℝ) < n := by positivity
    have hq0 : 0 ≤ (p n : ℝ) := (p n).2.1
    have hmean := isolatedMean_reciprocal_le hn hq0 hphalf.le hpeps.le hε0 hε1
      (by rwa [lt_div_iff₀ hn0] at hpn)
    have ha : 0 < 1 - (p n : ℝ) := by linarith
    have hratio : (p n : ℝ) / (1 - (p n : ℝ)) ≤ 2 * (p n : ℝ) := by
      apply (div_le_iff₀ ha).2
      have hfac : 0 ≤ (p n : ℝ) * (1 - 2 * (p n : ℝ)) :=
        mul_nonneg hq0 (by linarith)
      nlinarith
    calc
      (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n) ≤
          1 / ((n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1)) +
            (p n : ℝ) / (1 - (p n : ℝ)) :=
        noIsolatedVertices_probability_le hn (p n) (by linarith)
      _ ≤ (n : ℝ) ^ (-ε / 2) + 2 * (p n : ℝ) :=
        add_le_add hmean hratio
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε / 2)) atTop (𝓝 0) := by
    have hbase := (tendsto_rpow_neg_atTop (show 0 < ε / 2 by positivity)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa [Function.comp_def, neg_div] using hbase
  have htwop : Tendsto (fun n : ℕ => 2 * (p n : ℝ)) atTop (𝓝 0) := by
    simpa using hpzero.const_mul 2
  have hupperZero : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (-ε / 2) + 2 * (p n : ℝ)) atTop (𝓝 0) := by
    simpa using hpow.add htwop
  have hno : Tendsto
      (fun n => (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n))
      atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      hnoUpper hupperZero
  have hcompl : ∀ n,
      (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n) =
        1 - (HDP.erdosRenyi n (p n)).real (hasIsolatedVertex n) := by
    intro n
    rw [noIsolatedVertices_eq_compl, measureReal_compl (hasIsolatedVertex_measurable n),
      probReal_univ]
  have hdiff : Tendsto
      (fun n => 1 - (HDP.erdosRenyi n (p n)).real (noIsolatedVertices n))
      atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hno)
  apply hdiff.congr'
  filter_upwards [] with n
  linarith [hcompl n]

end HDP.Chapter1


/-!
# Book Chapter 1: distribution infrastructure

This module is the distribution layer in the Chapter 1 import graph.  The reusable
two-point laws (`IsRademacher` and `IsBernoulli`) live in the book-wide
prelude, while Mathlib supplies the Gaussian and Poisson measures used by §1.7.
Source-numbered facts about those laws are exposed in `LimitTheorems`.

Keeping this layer explicit prevents later concentration modules from reaching around
Chapter 1 to import distribution implementations directly.
-/



/-!
# Book Chapter 1, Section 1.7

The strong law, central limit theorem, de Moivre–Laplace theorem, Poisson law,
factorial asymptotics, and Gamma-function interface. The source is PDF pages 25–28
(printed 17–20).
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal unitInterval Topology Nat

namespace HDP.Chapter1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Book (1.23): variance of the sample mean -/

/-- If `X₁, …, X_N` have common variance `σ²` and are (pairwise)
independent, then `Var((1/N)∑ᵢXᵢ) = σ²/N`. Explicit displayed source identity; derived,
as in the source, from (1.8).

**Book Equation (1.23).** -/
theorem variance_sample_mean [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (σsq : ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hvar : ∀ i, Var[X i; μ] = σsq)
    (hindep : Set.Pairwise Set.univ fun i j => IndepFun (X i) (X j) μ) :
    Var[fun ω => (∑ i, X i ω) / N; μ] = σsq / N := by
  have h1 : (fun ω => (∑ i, X i ω) / N) = fun ω => ∑ i, (1/(N:ℝ)) * X i ω := by
    funext ω
    rw [← Finset.mul_sum]
    ring
  have h2 : (fun ω => ∑ i, (1/(N:ℝ)) * X i ω)
      = ∑ i, fun ω => (1/(N:ℝ)) * X i ω := by
    funext ω
    rw [Finset.sum_apply]
  rw [h1, h2, variance_weighted_sum (fun _ => 1/(N:ℝ)) (fun i _ => hX i)
    (fun i _ j _ hij => hindep (Set.mem_univ i) (Set.mem_univ j) hij)]
  have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ## Book Theorem 1.7.1: the strong law of large numbers -/

/-- For i.i.d. integrable `X₁, X₂, …` with mean `m`,
`S_N/N → m` almost surely. The source omits the proof (citations to Durrett and
Billingsley); a complete Lean proof is obtained from Mathlib's
`ProbabilityTheory.strong_law_ae_real` (Etemadi's theorem).

**Book Theorem 1.7.1.** -/
theorem strong_law_of_large_numbers [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m : ℝ}
    (hint : Integrable (X 0) μ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hmean : ∫ ω, X 0 ω ∂μ = m) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, X i ω) / N)
      atTop (𝓝 m) := by
  have h := strong_law_ae_real X hint (fun i j hij => hindep.indepFun hij) hident
  rw [show μ[X 0] = m from hmean] at h
  exact h

/-! ## Book Definition 1.7.2: the normal distribution -/

/-- The density of the standard normal distribution is
`f(x) = (1/√(2π)) e^{−x²/2}`. Explicit source definition; Mathlib correspondence:
`gaussianPDFReal 0 1` is exactly this function.

**Book Definition 1.7.2.** -/
lemma stdGaussian_density (x : ℝ) :
    gaussianPDFReal 0 1 x = (1 / Real.sqrt (2 * π)) * Real.exp (-x^2 / 2) := by
  rw [gaussianPDFReal_def]
  norm_num [one_div]

/-- Mean of `N(0,1)`: `𝔼X = 0`. Explicit source claim.

**Book Definition 1.7.2.** -/
lemma stdGaussian_mean : ∫ x, x ∂(gaussianReal 0 1) = 0 :=
  integral_id_gaussianReal

/-- Variance of `N(0,1)`: `Var(X) = 1`. Explicit source claim.

**Book Definition 1.7.2.** -/
lemma stdGaussian_variance : Var[fun x => x; gaussianReal 0 1] = 1 := by
  rw [variance_fun_id_gaussianReal]
  norm_num

/-- "`X ∼ N(m,σ²)` if `X = m + σZ` with `Z ∼ N(0,1)`"):
an affine image `m + σ₀Z` of a standard normal random variable has law
`gaussianReal m σ₀²`. Explicit source definition, expressed as the statement that the
book's definition of `N(m,σ²)` agrees with Mathlib's `gaussianReal`.

**Book Definition 1.7.2.** -/
theorem normal_of_affine {Z : Ω → ℝ} (hZm : AEMeasurable Z μ)
    (hZ : μ.map Z = gaussianReal 0 1) (m σ₀ : ℝ) (v : ℝ≥0)
    (hv : (v : ℝ) = σ₀ ^ 2) :
    μ.map (fun ω => m + σ₀ * Z ω) = gaussianReal m v := by
  have hveq : (NNReal.mk (σ₀^2) (sq_nonneg _)) * 1 = v := by
    ext
    push_cast
    rw [hv]
    ring
  have hmul : μ.map (fun ω => σ₀ * Z ω) = gaussianReal 0 v := by
    have h1 : (fun ω => σ₀ * Z ω) = (fun x => σ₀ * x) ∘ Z := rfl
    rw [h1, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZm, hZ]
    have h2 := gaussianReal_map_const_mul (μ := 0) (v := 1) σ₀
    rw [show ((σ₀ * ·) : ℝ → ℝ) = fun x => σ₀ * x from rfl] at h2
    rw [h2, mul_zero, hveq]
  have h3 : (fun ω => m + σ₀ * Z ω) = (fun x => x + m) ∘ (fun ω => σ₀ * Z ω) := by
    funext ω
    simp [add_comm]
  rw [h3, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), hmul]
  have h4 := gaussianReal_map_add_const (μ := 0) (v := v) m
  rw [show ((· + m) : ℝ → ℝ) = fun x => x + m from rfl] at h4
  rw [h4, zero_add]

/-- Density of `N(m,σ²)`:
`f(x) = (1/(σ√(2π))) e^{−(x−m)²/(2σ²)}` for `σ > 0`. Explicit source claim; Mathlib
correspondence via `gaussianPDFReal`.

**Book Definition 1.7.2.** -/
lemma gaussian_density (m σ₀ : ℝ) (hσ : 0 < σ₀) (v : ℝ≥0)
    (hv : (v : ℝ) = σ₀ ^ 2)
    (x : ℝ) :
    gaussianPDFReal m v x
      = (1 / (σ₀ * Real.sqrt (2 * π))) * Real.exp (-(x - m)^2 / (2 * σ₀^2)) := by
  rw [gaussianPDFReal_def]
  have h1 : Real.sqrt (2 * π * σ₀^2) = σ₀ * Real.sqrt (2 * π) := by
    rw [mul_comm (2 * π) (σ₀^2), Real.sqrt_mul (sq_nonneg σ₀), Real.sqrt_sq hσ.le,
      mul_comm]
  rw [hv, h1, one_div]

/-- Mean of `N(m,σ²)` is `m`. Explicit source claim.

**Book Definition 1.7.2.** -/
lemma gaussian_mean (m : ℝ) (v : ℝ≥0) : ∫ x, x ∂(gaussianReal m v) = m :=
  integral_id_gaussianReal

/-- Variance of `N(m,σ²)` is `σ² = v`. Explicit source claim.

**Book Definition 1.7.2.** -/
lemma gaussian_variance (m : ℝ) (v : ℝ≥0) : Var[fun x => x; gaussianReal m v] = v :=
  variance_fun_id_gaussianReal

/-! ## Book Theorem 1.7.3: the Lindeberg–Lévy central limit theorem -/

/-- Convergence in distribution is stated, as the source itself explains after the theorem,
as pointwise convergence of the CDFs of `Z_N` (the CDF of `N(0,1)` is continuous, so
pointwise everywhere). The proof applies Mathlib's central limit theorem, rescales its
Gaussian limit to unit variance, and uses the Portmanteau theorem on `(-∞, t]`.

**Book Theorem 1.7.3.** -/
theorem central_limit_theorem [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m sig : ℝ}
    (hsig : 0 < sig) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hmem : MemLp (X 0) 2 μ)
    (hmean : ∫ ω, X 0 ω ∂μ = m) (hvar : Var[X 0; μ] = sig ^ 2) (t : ℝ) :
    Tendsto (fun N : ℕ =>
        μ.real {ω | (∑ i ∈ Finset.range N, X i ω - N * m) / (sig * Real.sqrt N) ≤ t})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  let v : ℝ≥0 := Var[X 0; μ].toNNReal
  have hv : (v : ℝ) = sig ^ 2 := by
    simp [v, hvar, Real.toNNReal_of_nonneg (sq_nonneg sig)]
  have hv0 : v ≠ 0 := by
    intro hvzero
    have : (v : ℝ) = 0 := by simp [hvzero]
    rw [hv] at this
    nlinarith
  have hY : HasLaw (fun x : ℝ => x) (gaussianReal 0 v) (gaussianReal 0 v) := by
    refine ⟨measurable_id.aemeasurable, ?_⟩
    simp
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := X) hY hmem hindep hident
  have hscaled := hclt.continuous_comp (g := fun x : ℝ => x / sig) (by fun_prop)
  let Z : ℕ → Ω → ℝ := fun N ω =>
    (∑ i ∈ Finset.range N, X i ω - N * m) / (sig * Real.sqrt N)
  have hscaled' : TendstoInDistribution Z atTop
      ((fun x : ℝ => x / sig) ∘ fun x => x) (fun _ => μ) (gaussianReal 0 v) := by
    refine hscaled.congr (fun N => Filter.Eventually.of_forall fun ω => ?_)
      Filter.EventuallyEq.rfl
    simp only [Z, Function.comp_apply, div_eq_mul_inv]
    rw [hmean]
    ring
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => x / sig) = gaussianReal 0 1 := by
    rw [gaussianReal_map_div_const]
    have hvdiv : v / NNReal.mk (sig ^ 2) (sq_nonneg sig) = 1 := by
      ext
      simp [hv, hsig.ne']
    rw [hvdiv]
    simp
  have hfrontier : ((gaussianReal 0 v).map (fun x : ℝ => x / sig))
      (frontier (Set.Iic t)) = 0 := by
    rw [hmap, frontier_Iic]
    exact @measure_singleton ℝ _ (gaussianReal 0 1) (noAtoms_gaussianReal one_ne_zero) t
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hscaled'.tendsto hfrontier
  have htReal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  simp only [Function.comp_def] at htReal
  convert htReal using 1
  · funext N
    rw [measureReal_def]
    change (μ {ω | Z N ω ≤ t}).toReal = ((μ.map (Z N)) (Set.Iic t)).toReal
    rw [Measure.map_apply_of_aemeasurable (hscaled'.forall_aemeasurable N)
      measurableSet_Iic]
    rfl
  · apply congrArg nhds
    rw [measureReal_def]
    change (gaussianReal 0 1 (Set.Iic t)).toReal =
      (((gaussianReal 0 v).map (fun x : ℝ => x / sig)) (Set.Iic t)).toReal
    rw [hmap]

/-! ## Book Example 1.7.4: Bernoulli and binomial distributions -/

/-- `Var(X) = p(1−p)` for `X ∼ Ber(p)` ("One can easily check").
Implicit source claim; complete proof. (The mean `𝔼X = p` is
`IsBernoulli.integral_eq`.)

**Book Example 1.7.4.** -/
theorem bernoulli_variance [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : I}
    (hX : IsBernoulli X p μ) :
    Var[X; μ] = p * (1 - p) := by
  have h1 : Var[X; μ] = (∫ ω, (X ω)^2 ∂μ) - (∫ ω, X ω ∂μ)^2 := by
    simpa using variance_eq_sub (hX.memLp 2)
  rw [h1, hX.integral_sq_eq, hX.integral_eq]
  ring

/-- For a binomial sum of independent Bernoulli variables,
as a sum `S_N = X₁ + ⋯ + X_N` of independent `Ber(p)` random variables, and this
formalization represents `Binom(N,p)` throughout by exactly these hypotheses.
Mean of the binomial: `𝔼S_N = Np`. Implicit source claim.

**Book Example 1.7.4.** -/
theorem binomial_mean [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ} {p : I}
    (hX : ∀ i, IsBernoulli (X i) p μ) :
    ∫ ω, (∑ i, X i ω) ∂μ = N * p := by
  rw [integral_finsetSum Finset.univ
    (fun i _ => ((hX i).memLp 1).integrable le_rfl)]
  simp [(hX · |>.integral_eq)]

/-- / §2.1: variance of the binomial, `Var(S_N) = Np(1−p)`.
Implicit source claim (used at the source (2.1)).

**Book Example 1.7.4.** -/
theorem binomial_variance [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ} {p : I}
    (hX : ∀ i, IsBernoulli (X i) p μ) (hindep : iIndepFun X μ) :
    Var[∑ i, X i; μ] = N * (p * (1 - p)) := by
  rw [IndepFun.variance_sum (fun i _ => (hX i).memLp 2)
    (fun i _ j _ hij => hindep.indepFun hij)]
  simp [bernoulli_variance (hX _)]

/-- For i.i.d. `Xᵢ ∼ Ber(p)`,
`(S_N − Np)/√(Np(1−p)) → N(0,1)` in distribution.

Explicit source statement ("The central limit theorem (Theorem 1.7.3) yields...").
The result is an unconditional consequence of `central_limit_theorem`.

**Book Example 1.7.4.** -/
theorem deMoivreLaplace [IsProbabilityMeasure μ] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, IsBernoulli (X i) ⟨p, hp0.le, hp1.le⟩ μ)
    (hindep : iIndepFun X μ) (t : ℝ) :
    Tendsto (fun N : ℕ =>
        μ.real {ω | (∑ i ∈ Finset.range N, X i ω - N * p)
          / Real.sqrt (N * (p * (1 - p))) ≤ t})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  set sig := Real.sqrt (p * (1 - p)) with hsigdef
  have hpq : 0 < p * (1 - p) := by nlinarith
  have hsig : 0 < sig := Real.sqrt_pos.mpr hpq
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [(hX i).map_eq, (hX 0).map_eq]⟩
  have hvar : Var[X 0; μ] = sig^2 := by
    rw [bernoulli_variance (hX 0), hsigdef, Real.sq_sqrt hpq.le]
  have h := central_limit_theorem hsig hindep hident ((hX 0).memLp 2)
    ((hX 0).integral_eq) hvar t
  have hset : ∀ N : ℕ,
      {ω | (∑ i ∈ Finset.range N, X i ω - N * p) / Real.sqrt (N * (p * (1 - p))) ≤ t}
        = {ω | (∑ i ∈ Finset.range N, X i ω - N * p) / (sig * Real.sqrt N) ≤ t} := by
    intro N
    have hd : Real.sqrt (N * (p * (1 - p))) = sig * Real.sqrt N := by
      rw [Real.sqrt_mul (Nat.cast_nonneg N), hsigdef, mul_comm]
    rw [hd]
  simpa only [hset] using h

/-! ## Book Definition 1.7.5: the Poisson distribution -/

/-- **Book Definition 1.7.5 (Poisson distribution)**: `Z ∼ Pois(λ)` if `Z` takes values
in `{0, 1, 2, …}` with probabilities (1.26).  Formally, the law of `Z` is
Mathlib's `poissonMeasure`. -/
structure IsPoissonRV (Z : Ω → ℕ) (r : ℝ≥0) (μ : Measure Ω) : Prop where
  aemeasurable : AEMeasurable Z μ
  map_eq : μ.map Z = poissonMeasure r

/-- `ℙ{Z = k} = e^{−λ} λ^k / k!` for `Z ∼ Pois(λ)`.
Explicit displayed source identity; Mathlib correspondence via
`poissonMeasure_real_singleton`.

**Book Definition 1.7.5.** -/
theorem poisson_pmf {Z : Ω → ℕ} {r : ℝ≥0} (h : IsPoissonRV Z r μ) (k : ℕ) :
    μ.real {ω | Z ω = k} = Real.exp (-r) * r^k / k ! := by
  have h1 : μ.real {ω | Z ω = k} = (μ.map Z).real {k} := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable h.aemeasurable (measurableSet_singleton k)]
    rfl
  rw [h1, h.map_eq, poissonMeasure_real_singleton]

/-! ## Book Lemma 1.7.7: Stirling's approximation -/

/-- `n! = √(2πn)(n/e)ⁿ(1+o(1))`, formalized as asymptotic equivalence.

Source location: Chapter 1, §1.7 (PDF page 27). Explicit source declaration; the source
omits the proof (citations to Robbins and Feller); a complete Lean proof is obtained from
Mathlib's `Stirling.factorial_isEquivalent_stirling`.

**Book Lemma 1.7.7.** -/
theorem stirling_approximation :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (n ! : ℝ))
      (fun n : ℕ => Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n) := by
  have h := Stirling.factorial_isEquivalent_stirling
  have heq : (fun n : ℕ => Real.sqrt (2 * (n:ℝ) * π) * ((n:ℝ) / Real.exp 1) ^ n)
      = fun n : ℕ => Real.sqrt (2 * π * n) * ((n:ℝ) / Real.exp 1) ^ n := by
    funext n
    rw [mul_right_comm]
  rw [heq] at h
  exact h

/-- Ratio form: `n! / (√(2πn)(n/e)ⁿ) → 1` (the "`(1+o(1))`" form of
Stirling used in concrete estimates, e.g. at the source §2.1).

**Book Lemma 1.7.7.** -/
theorem stirling_ratio_tendsto_one :
    Tendsto (fun n : ℕ => (n ! : ℝ) / (Real.sqrt (2 * π * n) * ((n:ℝ) / Real.exp 1) ^ n))
      atTop (𝓝 1) := by
  have hne : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * π * n) * ((n:ℝ) / Real.exp 1) ^ n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp stirling_approximation

/-- The Poisson pmf asymptotics
`ℙ{Z = k} = (e^{−λ}/√(2πk)) (eλ/k)^k (1+o(1))` as `k → ∞`, formalized as asymptotic
equivalence of the pmf (1.26) with the displayed expression. Explicit displayed source
claim (obtained by "Using Stirling approximation in (1.26)"); same derivation here.

**Book Equation (1.27).** -/
theorem poisson_pmf_asymptotic (r : ℝ≥0) :
    Asymptotics.IsEquivalent atTop
      (fun k : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ)^k / k !)
      (fun k : ℕ => Real.exp (-(r:ℝ)) / Real.sqrt (2 * π * k)
        * (Real.exp 1 * r / k)^k) := by
  have hdiv := (Asymptotics.IsEquivalent.refl
    (u := fun k : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ)^k) (l := atTop)).div
    stirling_approximation
  have heq : (fun k : ℕ => (Real.exp (-(r:ℝ)) * (r:ℝ)^k)
        / (Real.sqrt (2*π*k) * ((k:ℝ)/Real.exp 1)^k))
      =ᶠ[atTop] (fun k : ℕ => Real.exp (-(r:ℝ)) / Real.sqrt (2 * π * k)
        * (Real.exp 1 * r / k)^k) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hs : Real.sqrt (2*π*k) ≠ 0 := by positivity
    have hkne : ((k:ℝ))^k ≠ 0 := by positivity
    have hene : (Real.exp 1)^k ≠ 0 := by positivity
    simp only [div_pow, mul_pow]
    field_simp
  refine Asymptotics.IsEquivalent.trans ?_ heq.isEquivalent
  exact hdiv

/-! ## Book Lemma 1.7.8: bounds on the factorial -/

/-- Lower bound: `(n/e)ⁿ ≤ n!`. The source proof (drop all terms except the
`n`-th in the Taylor series of `eⁿ`) is reproduced via `Real.sum_le_exp_of_nonneg`.

**Book Lemma 1.7.8.** -/
theorem factorial_lower_bound (n : ℕ) : ((n:ℝ) / Real.exp 1) ^ n ≤ n ! := by
  have hterm : ((n:ℝ)^n / n !) ≤ Real.exp n := by
    calc ((n:ℝ)^n / n !) ≤ ∑ i ∈ Finset.range (n+1), (n:ℝ)^i / i ! :=
          Finset.single_le_sum (f := fun i => (n:ℝ)^i / i !)
            (fun i _ => by positivity) (Finset.self_mem_range_succ n)
      _ ≤ Real.exp n := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) (n+1)
  have hfac : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hexp : (0:ℝ) < Real.exp 1 ^ n := by positivity
  rw [div_le_iff₀ hfac, ← Real.exp_one_pow] at hterm
  rw [div_pow, div_le_iff₀ hexp]
  calc (n:ℝ)^n ≤ Real.exp 1 ^ n * ↑n ! := hterm
    _ = ↑n ! * Real.exp 1 ^ n := mul_comm _ _

/-- Lean implementation helper (key step for the upper bound in the source (1.28)):
`e · n^(n+1) ≤ (n+1)^(n+1)`, i.e. `e ≤ (1 + 1/n)^(n+1)`.

**Book Equation (1.28).** -/
lemma exp_mul_pow_le_succ_pow (n : ℕ) (hn : 1 ≤ n) :
    Real.exp 1 * (n:ℝ)^(n+1) ≤ ((n:ℝ)+1)^(n+1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  -- Step 1: `exp(1/(n+1)) ≤ 1 + 1/n`.
  have h1 : Real.exp (1/((n:ℝ)+1)) ≤ 1 + 1/n := by
    have h3 : (n:ℝ)/(n+1) ≤ Real.exp (-(1/((n:ℝ)+1))) := by
      calc (n:ℝ)/(n+1) = -(1/((n:ℝ)+1)) + 1 := by
            field_simp
            ring
        _ ≤ _ := Real.add_one_le_exp _
    have h4 : Real.exp (1/((n:ℝ)+1)) * ((n:ℝ)/(n+1)) ≤ 1 := by
      calc Real.exp (1/((n:ℝ)+1)) * ((n:ℝ)/(n+1))
          ≤ Real.exp (1/((n:ℝ)+1)) * Real.exp (-(1/((n:ℝ)+1))) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [show (1:ℝ) + 1/n = ((n:ℝ)+1)/n by field_simp, le_div_iff₀ hn0]
    calc Real.exp (1/((n:ℝ)+1)) * n
        = (Real.exp (1/((n:ℝ)+1)) * ((n:ℝ)/(n+1))) * ((n:ℝ)+1) := by
          field_simp
      _ ≤ 1 * ((n:ℝ)+1) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (n:ℝ)+1 := one_mul _
  -- Step 2: `1/(n+1) ≤ log(1 + 1/n)`, hence `e ≤ (1+1/n)^(n+1)`.
  have hlog : (1:ℝ)/((n:ℝ)+1) ≤ Real.log (1 + 1/n) := by
    calc (1:ℝ)/((n:ℝ)+1) = Real.log (Real.exp (1/((n:ℝ)+1))) := (Real.log_exp _).symm
      _ ≤ Real.log (1 + 1/n) := Real.log_le_log (Real.exp_pos _) h1
  have hkey : Real.exp 1 ≤ (1 + 1/(n:ℝ))^(n+1) := by
    have h5 : (1:ℝ) ≤ ((n:ℝ)+1) * Real.log (1 + 1/n) := by
      calc (1:ℝ) = ((n:ℝ)+1) * (1/((n:ℝ)+1)) := by field_simp
        _ ≤ ((n:ℝ)+1) * Real.log (1 + 1/n) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
    calc Real.exp 1 ≤ Real.exp (((n:ℝ)+1) * Real.log (1 + 1/n)) :=
          Real.exp_le_exp.mpr h5
      _ = (1 + 1/(n:ℝ))^(n+1) := by
          rw [show ((n:ℝ)+1) = ((n+1 : ℕ) : ℝ) by push_cast; ring,
            Real.exp_nat_mul, Real.exp_log (by positivity)]
  -- Step 3: multiply by `n^(n+1)`.
  have h6 : (1 + 1/(n:ℝ)) = ((n:ℝ)+1)/n := by field_simp
  rw [h6, div_pow] at hkey
  calc Real.exp 1 * (n:ℝ)^(n+1)
      ≤ (((n:ℝ)+1)^(n+1)/(n:ℝ)^(n+1)) * (n:ℝ)^(n+1) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = ((n:ℝ)+1)^(n+1) := div_mul_cancel₀ _ (by positivity)

/-- Upper bound: `n! ≤ e·n·(n/e)ⁿ` for `n ≥ 1`.

The source proves this via the integral bound (1.29); the Lean proof is an alternative
complete proof by induction (see the proof audit), from which (1.29) is derived in
`log_factorial_le` below. (In the source `ℕ` starts at 1; for `n = 0` the inequality
fails, so the hypothesis `1 ≤ n` is explicit.)

**Book Lemma 1.7.8.** -/
theorem factorial_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ Real.exp 1 * n * ((n:ℝ) / Real.exp 1) ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with h1 | h1
    · have hm0 : m = 0 := by omega
      subst hm0
      norm_num [Nat.factorial]
    · have ihm := ih h1
      have hstep := exp_mul_pow_le_succ_pow m h1
      have hm0 : (0:ℝ) < m := by exact_mod_cast h1
      have hlhs : ((m+1)! : ℝ) = ((m:ℝ)+1) * m ! := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hlhs]
      have hexp : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
      calc ((m:ℝ)+1) * m !
          ≤ ((m:ℝ)+1) * (Real.exp 1 * m * ((m:ℝ)/Real.exp 1)^m) :=
            mul_le_mul_of_nonneg_left ihm (by positivity)
        _ = ((m:ℝ)+1) * ((Real.exp 1 * (m:ℝ)^(m+1)) / Real.exp 1 ^ m) := by
            rw [div_pow]
            field_simp
            ring
        _ ≤ ((m:ℝ)+1) * ((((m:ℝ)+1)^(m+1)) / Real.exp 1 ^ m) := by
            gcongr
        _ = Real.exp 1 * ((m:ℝ)+1) * ((((m:ℝ)+1))/Real.exp 1)^(m+1) := by
            rw [div_pow]
            rw [pow_succ (Real.exp 1) m]
            field_simp
        _ = Real.exp 1 * (↑(m+1)) * ((↑(m+1) : ℝ)/Real.exp 1)^(m+1) := by
            push_cast
            ring

/-- Unnumbered identity inside the proof of Lemma 1.7.8:
`ln(n!) = ∑_{k=1}^n ln k`. Implicit source claim.

**Book Equation (1.29).** -/
lemma log_factorial_eq_sum (n : ℕ) :
    Real.log (n !) = ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity : (0:ℝ) < (m ! : ℝ)).ne', ih]
    ring

/-- `ln(n!) ≤ ∫₁ⁿ ln x dx + ln n (= n(ln n − 1) + 1 + ln n)`.
Explicit displayed source claim (the inequality "follows by comparing the areas as in the
usual proof of the integral test — do it!"); here derived from the factorial upper bound
(mathematically equivalent content; see the proof audit).

**Book Equation (1.29).** -/
theorem log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n !) ≤ (∫ x in (1:ℝ)..(n:ℝ), Real.log x) + Real.log n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hint : (∫ x in (1:ℝ)..(n:ℝ), Real.log x) = n * Real.log n - n + 1 := by
    rw [integral_log]
    simp
  rw [hint]
  have hub := factorial_upper_bound n hn
  calc Real.log (n !)
      ≤ Real.log (Real.exp 1 * n * ((n:ℝ)/Real.exp 1)^n) := by
        apply Real.log_le_log (by positivity) hub
    _ = 1 + Real.log n + n * (Real.log n - 1) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (Real.exp_ne_zero 1) hn0.ne', Real.log_exp, Real.log_pow,
          Real.log_div hn0.ne' (Real.exp_ne_zero 1), Real.log_exp]
    _ = n * Real.log n - n + 1 + Real.log n := by ring

/-! ## Book Remark 1.7.9: the Gamma function -/

/-- The Gamma function `Γ(z) = ∫₀^∞ t^{z−1} e^{−t} dt` (for real
`z > 0`; the source also allows complex `z` with positive real part, available in Mathlib
as `Complex.Gamma`). Mathlib correspondence via `Real.Gamma_eq_integral`.

**Book Remark 1.7.9.** -/
theorem gamma_def {z : ℝ} (hz : 0 < z) :
    Real.Gamma z = ∫ t in Set.Ioi (0:ℝ), t ^ (z-1) * Real.exp (-t) := by
  rw [Real.Gamma_eq_integral hz]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- `Γ(n+1) = n!` ("Repeated integration by parts (do it!) reveals").
Explicit source claim; Mathlib correspondence via `Real.Gamma_nat_eq_factorial`.

**Book Remark 1.7.9.** -/
theorem gamma_nat_add_one (n : ℕ) : Real.Gamma (n + 1) = n ! :=
  Real.Gamma_nat_eq_factorial n

end HDP.Chapter1


/-!
# Book §1.7: the Gamma extension of Stirling's formula

This file complements the discrete Stirling theorem in `LimitTheorems`.  The proof
squeezes `log Γ(x + 1)` between the adjacent log-factorial interpolation lines supplied
by log-convexity of Gamma, then uses the factorial Stirling asymptotic.
-/

open Filter Set Topology
open scoped Nat Real

namespace HDP.Chapter1

/-- The main term in the real Gamma Stirling formula.

**Lean implementation helper.** -/
noncomputable def gammaStirlingMain (x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * x) * (x / Real.exp 1) ^ x

/-- Logarithm of the main term, on the positive half-line.

**Lean implementation helper.** -/
noncomputable def gammaStirlingLog (x : ℝ) : ℝ :=
  Real.log (2 * Real.pi * x) / 2 + x * (Real.log x - 1)

/-- The logarithm of the Gamma function admits the main Stirling expansion with its remainder term.

**Lean implementation helper.** -/
lemma log_gammaStirlingMain {x : ℝ} (hx : 0 < x) :
    Real.log (gammaStirlingMain x) = gammaStirlingLog x := by
  rw [gammaStirlingMain, gammaStirlingLog, Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_rpow (by positivity)]
  rw [Real.log_div (ne_of_gt hx) (Real.exp_ne_zero 1), Real.log_exp]

/-- The remainder in the logarithmic Stirling formula for factorials tends to zero.

**Lean implementation helper.** -/
lemma log_factorial_stirling_remainder_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n ! : ℝ) - gammaStirlingLog n) atTop (𝓝 0) := by
  have h := stirling_ratio_tendsto_one
  have hlog := h.log (by norm_num : (1 : ℝ) ≠ 0)
  convert hlog using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp [gammaStirlingLog]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.log_div (by positivity : (n ! : ℝ) ≠ 0) (by positivity)]
      congr 1
      rw [gammaStirlingLog,
        Real.log_mul (x := Real.sqrt (2 * Real.pi * (n : ℝ))) (by positivity) (by positivity),
        Real.log_sqrt (by positivity), Real.log_pow,
        Real.log_div (ne_of_gt hnpos) (Real.exp_ne_zero 1), Real.log_exp]
  · simp

/-- The logarithmic Stirling asymptotic extends from integers to all large real arguments by interpolation.

**Lean implementation helper.** -/
lemma gammaStirlingLog_interpolation {m : ℕ} {y : ℝ} (hm : m ≠ 0)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ gammaStirlingLog (m + y) - (gammaStirlingLog m + y * Real.log m) ∧
      gammaStirlingLog (m + y) - (gammaStirlingLog m + y * Real.log m)
        ≤ 3 / (2 * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmy : 0 < (m : ℝ) + y := add_pos hm0 hy0
  have hq : 0 < ((m : ℝ) + y) / m := div_pos hmy hm0
  have hid :
      gammaStirlingLog (m + y) - (gammaStirlingLog m + y * Real.log m) =
        ((m : ℝ) + y + 1 / 2) * Real.log (((m : ℝ) + y) / m) - y := by
    rw [gammaStirlingLog, gammaStirlingLog,
      Real.log_div (ne_of_gt hmy) (ne_of_gt hm0)]
    rw [Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (ne_of_gt hmy),
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (ne_of_gt hm0)]
    ring
  rw [hid]
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  have hhi := Real.log_le_sub_one_of_pos hq
  have hcoef : 0 ≤ (m : ℝ) + y + 1 / 2 := by positivity
  constructor
  · calc
      0 ≤ ((m : ℝ) + y + 1 / 2) * (1 - (((m : ℝ) + y) / m)⁻¹) - y := by
        rw [inv_div]
        rw [show ((m : ℝ) + y + 1 / 2) * (1 - (m : ℝ) / ((m : ℝ) + y)) - y =
          y / (2 * ((m : ℝ) + y)) by field_simp; ring]
        positivity
      _ ≤ ((m : ℝ) + y + 1 / 2) * Real.log (((m : ℝ) + y) / m) - y := by
        gcongr
  · calc
      ((m : ℝ) + y + 1 / 2) * Real.log (((m : ℝ) + y) / m) - y
          ≤ ((m : ℝ) + y + 1 / 2) * (((m : ℝ) + y) / m - 1) - y := by
            gcongr
      _ = (y ^ 2 + y / 2) / m := by field_simp; ring
      _ ≤ 3 / (2 * (m : ℝ)) := by
        rw [show 3 / (2 * (m : ℝ)) = (3 / 2) / m by ring,
          div_le_div_iff_of_pos_right hm0]
        have hyy : y ^ 2 ≤ y := by
          nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hy1)]
        linarith

/-- The logarithm of Gamma at a real argument is squeezed between neighboring integer Gamma values.

**Lean implementation helper.** -/
lemma log_gamma_ceil_bounds {x : ℝ} (hx : 1 < x) :
    let m := ⌈x⌉₊ - 1
    let y := x - m
    Real.log (m ! : ℝ) + y * Real.log m ≤ Real.log (Real.Gamma (x + 1)) ∧
      Real.log (Real.Gamma (x + 1)) ≤ Real.log (m ! : ℝ) + y * Real.log (m + 1) := by
  let n := ⌈x⌉₊
  let m := n - 1
  let y := x - m
  have hn2 : 2 ≤ n := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Nat.add_one_le_ceil_iff]
    exact_mod_cast hx
  have hn1 : 1 ≤ n := le_trans (by omega) hn2
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hn_eq : n = m + 1 := by dsimp [m]; omega
  have hy0 : 0 < y := by
    have hceil : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_trans zero_le_one hx.le)
    dsimp [y, m]
    rw [Nat.cast_sub hn1]
    norm_num
    linarith
  have hy1 : y ≤ 1 := by
    have hle : x ≤ (n : ℝ) := Nat.le_ceil x
    dsimp [y, m]
    rw [Nat.cast_sub hn1]
    norm_num
    linarith
  have hfeq : ∀ {z : ℝ}, 0 < z →
      (Real.log ∘ Real.Gamma) (z + 1) = (Real.log ∘ Real.Gamma) z + Real.log z := by
    intro z hz
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hz.ne', Real.log_mul hz.ne' (Real.Gamma_pos_of_pos hz).ne']
    ring
  have hlo := Real.BohrMollerup.f_add_nat_ge Real.convexOn_log_Gamma hfeq hn2 hy0
  have hhi := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma hfeq
    (by omega : n ≠ 0) hy0 hy1
  have harg : (n : ℝ) + y = x + 1 := by
    dsimp [y, m]
    rw [Nat.cast_sub hn1]
    ring
  have hfac : (Real.log ∘ Real.Gamma) n = Real.log (m ! : ℝ) := by
    simp only [Function.comp_apply]
    rw [hn_eq]
    push_cast
    rw [Real.Gamma_nat_eq_factorial]
  have hpred : (n : ℝ) - 1 = m := by
    rw [Nat.cast_sub hn1]
    norm_num
  change Real.log (m ! : ℝ) + y * Real.log m ≤ Real.log (Real.Gamma (x + 1)) ∧
    Real.log (Real.Gamma (x + 1)) ≤ Real.log (m ! : ℝ) + y * Real.log (m + 1)
  constructor
  · rw [hfac, harg, hpred] at hlo
    exact hlo
  · rw [hfac, harg] at hhi
    have hncast : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hn_eq
    rw [hncast] at hhi
    exact hhi

/-- Stirling asymptotic for Gamma.

**Book Equation (1.31).** -/
theorem log_gamma_stirling :
    Tendsto (fun x : ℝ => Real.log (Real.Gamma (x + 1)) - gammaStirlingLog x)
      atTop (𝓝 0) := by
  let m : ℝ → ℕ := fun x => ⌈x⌉₊ - 1
  have hm : Tendsto m atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (tendsto_nat_ceil_atTop (α := ℝ))
  have hmcast : Tendsto (fun x : ℝ => (m x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hrem : Tendsto
      (fun x : ℝ => Real.log ((m x) ! : ℝ) - gammaStirlingLog (m x)) atTop (𝓝 0) :=
    log_factorial_stirling_remainder_tendsto_zero.comp hm
  have hinv : Tendsto (fun x : ℝ => ((m x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hmcast
  have hlo : Tendsto
      (fun x : ℝ => (Real.log ((m x) ! : ℝ) - gammaStirlingLog (m x)) -
        (3 / 2) * ((m x : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hrem.sub (tendsto_const_nhds.mul hinv)
  have hhi : Tendsto
      (fun x : ℝ => (Real.log ((m x) ! : ℝ) - gammaStirlingLog (m x)) +
        ((m x : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hrem.add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    let y : ℝ := x - m x
    have hm1 : 1 ≤ m x := by
      dsimp [m]
      have hn2 : 2 ≤ ⌈x⌉₊ := by
        rw [show (2 : ℕ) = 1 + 1 by omega, Nat.add_one_le_ceil_iff]
        exact_mod_cast hx
      omega
    have hm0 : m x ≠ 0 := by omega
    have hy0 : 0 < y := by
      have hceil : (⌈x⌉₊ : ℝ) < x + 1 :=
        Nat.ceil_lt_add_one (le_trans zero_le_one hx.le)
      have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans hx)
      have hmceil' : (m x : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
        dsimp [m]
        rw [Nat.cast_sub hceil1]
        norm_num
      dsimp [y]
      linarith
    have hy1 : y ≤ 1 := by
      have hle : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans hx)
      have hmceil' : (m x : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
        dsimp [m]
        rw [Nat.cast_sub hceil1]
        norm_num
      dsimp [y]
      linarith
    have hg := (log_gamma_ceil_bounds hx).1
    have hi := (gammaStirlingLog_interpolation hm0 hy0 hy1).2
    have hxy : (m x : ℝ) + y = x := by simp [y]
    rw [hxy] at hi
    change (Real.log ((m x) ! : ℝ) - gammaStirlingLog (m x)) -
        (3 / 2) * ((m x : ℝ))⁻¹ ≤
      Real.log (Real.Gamma (x + 1)) - gammaStirlingLog x
    have hfrac : (3 / 2) * ((m x : ℝ))⁻¹ = 3 / (2 * (m x : ℝ)) := by
      field_simp
    rw [hfrac]
    change Real.log ((m x) ! : ℝ) + y * Real.log (m x) ≤
      Real.log (Real.Gamma (x + 1)) at hg
    linarith
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    let y : ℝ := x - m x
    have hm1 : 1 ≤ m x := by
      dsimp [m]
      have hn2 : 2 ≤ ⌈x⌉₊ := by
        rw [show (2 : ℕ) = 1 + 1 by omega, Nat.add_one_le_ceil_iff]
        exact_mod_cast hx
      omega
    have hm0 : m x ≠ 0 := by omega
    have hmpos : (0 : ℝ) < m x := by exact_mod_cast hm1
    have hy0 : 0 < y := by
      have hceil : (⌈x⌉₊ : ℝ) < x + 1 :=
        Nat.ceil_lt_add_one (le_trans zero_le_one hx.le)
      have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans hx)
      have hmceil' : (m x : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
        dsimp [m]
        rw [Nat.cast_sub hceil1]
        norm_num
      dsimp [y]
      linarith
    have hy1 : y ≤ 1 := by
      have hle : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans hx)
      have hmceil' : (m x : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
        dsimp [m]
        rw [Nat.cast_sub hceil1]
        norm_num
      dsimp [y]
      linarith
    have hg := (log_gamma_ceil_bounds hx).2
    have hi := (gammaStirlingLog_interpolation hm0 hy0 hy1).1
    have hxy : (m x : ℝ) + y = x := by simp [y]
    rw [hxy] at hi
    have hlog : Real.log ((m x : ℝ) + 1) - Real.log (m x) ≤ ((m x : ℝ))⁻¹ := by
      rw [← Real.log_div (by positivity : (m x : ℝ) + 1 ≠ 0) (ne_of_gt hmpos)]
      have := Real.log_le_sub_one_of_pos
        (show 0 < ((m x : ℝ) + 1) / (m x) by positivity)
      convert this using 1
      all_goals field_simp
      all_goals ring
    have hlog0 : 0 ≤ Real.log ((m x : ℝ) + 1) - Real.log (m x) := by
      rw [← Real.log_div (by positivity : (m x : ℝ) + 1 ≠ 0) (ne_of_gt hmpos)]
      exact Real.log_nonneg ((le_div_iff₀ hmpos).2 (by linarith))
    have hylog : y * (Real.log ((m x : ℝ) + 1) - Real.log (m x)) ≤
        ((m x : ℝ))⁻¹ := by
      calc
        _ ≤ 1 * (Real.log ((m x : ℝ) + 1) - Real.log (m x)) := by gcongr
        _ ≤ _ := by simpa using hlog
    change Real.log (Real.Gamma (x + 1)) - gammaStirlingLog x ≤
      (Real.log ((m x) ! : ℝ) - gammaStirlingLog (m x)) + ((m x : ℝ))⁻¹
    change Real.log (Real.Gamma (x + 1)) ≤
      Real.log ((m x) ! : ℝ) + y * Real.log ((m x : ℝ) + 1) at hg
    linarith

/-- Ratio form on the full real axis.

**Book Equation (1.31).** -/
theorem gamma_stirling_ratio_tendsto_one :
    Tendsto (fun x : ℝ => Real.Gamma (x + 1) / gammaStirlingMain x) atTop (𝓝 1) := by
  have h := (Real.continuous_exp.tendsto 0).comp log_gamma_stirling
  rw [Real.exp_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  change Real.exp (Real.log (Real.Gamma (x + 1)) - gammaStirlingLog x) =
    Real.Gamma (x + 1) / gammaStirlingMain x
  have hmainpos : 0 < gammaStirlingMain x := by
    rw [gammaStirlingMain]
    positivity
  rw [Real.exp_sub, Real.exp_log (Real.Gamma_pos_of_pos (by linarith)),
    ← log_gammaStirlingMain hx0, Real.exp_log hmainpos]

/-- Stirling's formula for the real Gamma function,
`Γ(x+1) ~ √(2πx)(x/e)^x` as `x → +∞`.

**Book Equation (1.31).** -/
theorem gamma_stirling :
    Asymptotics.IsEquivalent atTop (fun x : ℝ => Real.Gamma (x + 1)) gammaStirlingMain := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).2 gamma_stirling_ratio_tendsto_one
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [gammaStirlingMain]
  positivity

/-- Complex Euler integral definition of Gamma in its convergence half-plane.

**Book Remark 1.7.9.** -/
theorem complex_gamma_def {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma z =
      ∫ t in Set.Ioi (0 : ℝ), (Complex.ofReal (Real.exp (-t))) *
        (Complex.ofReal t) ^ (z - 1) := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]

/-- Gamma integral and `Gamma(n+1)=n!`, real and complex.

**Book Remark 1.7.9.** -/
theorem complex_gamma_nat_add_one (n : ℕ) :
    Complex.Gamma (n + 1) = (n ! : ℂ) :=
  Complex.Gamma_nat_eq_factorial n

end HDP.Chapter1
