import HighDimensionalProbability.Appendix.Infra.SLT.GaussianLSI.TensorizedGLSI
import HighDimensionalProbability.Appendix.Infra.Herbst
import HighDimensionalProbability.Prelude.Sphere

/-!
# Gaussian logarithmic Sobolev inequality in Euclidean coordinates

The tensorized formalization used in the appendix is stated on the ordinary
function space `Fin n → ℝ`, while the geometric parts of this project use
`EuclideanSpace ℝ (Fin n)`.  This file records the coordinate bridge, including
the exact identity between the sum of squared partial derivatives and the
operator norm squared of the Fréchet derivative.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Appendix

noncomputable section

private abbrev toEuclidean (n : ℕ) :
    (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm

private lemma partialDeriv_comp_toEuclidean
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (i : Fin n) (w : Fin n → ℝ) :
    GaussianLSI.partialDeriv i (fun z => g (toEuclidean n z)) w =
      fderiv ℝ g (toEuclidean n w)
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  unfold GaussianLSI.partialDeriv
  have hcomp :
      HasFDerivAt (fun z => g (toEuclidean n z))
        ((fderiv ℝ g (toEuclidean n w)).comp
          (toEuclidean n).toContinuousLinearEquiv.toContinuousLinearMap) w :=
    (hg (toEuclidean n w)).hasFDerivAt.comp w
      (toEuclidean n).toContinuousLinearEquiv.hasFDerivAt
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, toEuclidean]

/-- The coordinate gradient used by the tensorized Gaussian LSI is exactly
the squared norm of the Euclidean Fréchet derivative. -/
lemma gradNormSq_comp_toEuclidean
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (w : Fin n → ℝ) :
    GaussianLSI.gradNormSq n (fun z => g (toEuclidean n z)) w =
      ‖fderiv ℝ g (toEuclidean n w)‖ ^ 2 := by
  rw [GaussianLSI.gradNormSq]
  simp_rw [partialDeriv_comp_toEuclidean hg]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_dual
    (fderiv ℝ g (toEuclidean n w)) |>.symm

/-- The coordinate product Gaussian, pushed through the canonical `L²`
identification, is Mathlib's standard Gaussian on Euclidean space. -/
private lemma measurePreserving_toEuclidean (n : ℕ) :
    MeasurePreserving (toEuclidean n)
      (GaussianMeasure.stdGaussianPi n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  refine ⟨(toEuclidean n).continuous.measurable, ?_⟩
  change Measure.map (WithLp.toLp 2)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
    stdGaussian (EuclideanSpace ℝ (Fin n))
  exact map_pi_eq_stdGaussian

/-- Euclidean-coordinate form of the tensorized Gaussian logarithmic
Sobolev inequality.

The two Sobolev/integrability premises are deliberately stated after
pullback to ordinary coordinates: this is the exact analytic domain of the
vendored tensorized theorem, while the conclusion is entirely geometric. -/
theorem gaussian_logSobolev_euclidean
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : GaussianLSI.MemW12GaussianPi n
      (fun z => g (toEuclidean n z))
      (GaussianMeasure.stdGaussianPi n))
    (hg_diff : Differentiable ℝ g)
    (hg_grad_cont : Continuous (fun x => fderiv ℝ g x))
    (hg_log_int : Integrable
      (fun z =>
        (g (toEuclidean n z)) ^ 2 *
          Real.log ((g (toEuclidean n z)) ^ 2))
      (GaussianMeasure.stdGaussianPi n)) :
    boltzmannEntropy
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (fun x => g x ^ 2) ≤
      2 * ∫ x : EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ g x‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let e := toEuclidean n
  let gc : (Fin n → ℝ) → ℝ := fun z => g (e z)
  have hgc_diff : Differentiable ℝ gc :=
    hg_diff.comp e.differentiable
  have hgc_grad_cont :
      ∀ i, Continuous (fun z => GaussianLSI.partialDeriv i gc z) := by
    intro i
    have hformula :
        (fun z => GaussianLSI.partialDeriv i gc z) =
          fun z =>
            fderiv ℝ g (e z)
              (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      funext z
      exact partialDeriv_comp_toEuclidean hg_diff i z
    rw [hformula]
    fun_prop
  have hlsi := GaussianLSI.gaussian_logSobolev_W12_pi
    hg hgc_diff hgc_grad_cont hg_log_int
  have he := measurePreserving_toEuclidean n
  have hemb : MeasurableEmbedding (toEuclidean n) :=
    (toEuclidean n).toHomeomorph.measurableEmbedding
  have hsq := he.integral_comp hemb
    (fun x : EuclideanSpace ℝ (Fin n) => g x ^ 2)
  have hsqlog := he.integral_comp hemb
    (fun x : EuclideanSpace ℝ (Fin n) =>
      g x ^ 2 * Real.log (g x ^ 2))
  have henergy := he.integral_comp hemb
    (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ g x‖ ^ 2)
  have hgradfun :
      GaussianLSI.gradNormSq n
          (fun z => g (toEuclidean n z)) =
        fun z => ‖fderiv ℝ g (toEuclidean n z)‖ ^ 2 := by
    funext z
    exact gradNormSq_comp_toEuclidean hg_diff z
  rw [hgradfun] at hlsi
  change
    (∫ x, g x ^ 2 * Real.log (g x ^ 2)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) -
        (∫ x, g x ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) *
          Real.log
            (∫ x, g x ^ 2
              ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ _
  rw [← hsqlog, ← hsq, ← henergy]
  simpa [gc, e, LogSobolev.entropy, boltzmannEntropy] using hlsi

/-- Bounded-data wrapper for `gaussian_logSobolev_euclidean`.

This form is convenient for smooth regularizations on a probability space:
uniform bounds on the function, its Fréchet derivative, and the entropy
integrand automatically supply the Gaussian Sobolev and integrability
premises of the tensorized theorem. -/
theorem gaussian_logSobolev_euclidean_of_bounds
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_diff : Differentiable ℝ g)
    (hg_grad_cont : Continuous (fun x => fderiv ℝ g x))
    {C D B : ℝ}
    (hg_bound : ∀ x, ‖g x‖ ≤ C)
    (hg_grad_bound : ∀ x, ‖fderiv ℝ g x‖ ≤ D)
    (hg_log_bound :
      ∀ x, ‖g x ^ 2 * Real.log (g x ^ 2)‖ ≤ B) :
    boltzmannEntropy
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (fun x => g x ^ 2) ≤
      2 * ∫ x : EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ g x‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let e := toEuclidean n
  let γ := GaussianMeasure.stdGaussianPi n
  have hgc_cont : Continuous (fun z => g (e z)) :=
    hg_diff.continuous.comp e.continuous
  have hgc_mem :
      MemLp (fun z => g (e z)) 2 γ := by
    apply MemLp.of_bound hgc_cont.aestronglyMeasurable C
    filter_upwards [] with z
    exact hg_bound _
  have hpartial_mem :
      ∀ i : Fin n,
        MemLp
          (fun z =>
            GaussianLSI.partialDeriv i (fun w => g (e w)) z)
          2 γ := by
    intro i
    have hformula :
        (fun z =>
          GaussianLSI.partialDeriv i (fun w => g (e w)) z) =
        fun z =>
          fderiv ℝ g (e z)
            (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      funext z
      exact partialDeriv_comp_toEuclidean hg_diff i z
    rw [hformula]
    apply MemLp.of_bound
      (by
        have hcont :
            Continuous
              (fun z =>
                fderiv ℝ g (e z)
                  (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
          fun_prop
        exact hcont.aestronglyMeasurable)
      D
    filter_upwards [] with z
    calc
      ‖fderiv ℝ g (e z)
          (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤
          ‖fderiv ℝ g (e z)‖ *
            ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
        (fderiv ℝ g (e z)).le_opNorm _
      _ = ‖fderiv ℝ g (e z)‖ := by simp
      _ ≤ D := hg_grad_bound _
  have hW12 :
      GaussianLSI.MemW12GaussianPi n
        (fun z => g (e z)) γ :=
    ⟨hgc_mem, hpartial_mem⟩
  have hlog_meas :
      AEStronglyMeasurable
        (fun z =>
          g (e z) ^ 2 * Real.log (g (e z) ^ 2)) γ := by
    have hsq : Measurable (fun z => g (e z) ^ 2) :=
      hgc_cont.measurable.pow_const 2
    exact (hsq.mul hsq.log).aestronglyMeasurable
  have hlog_int :
      Integrable
        (fun z =>
          g (e z) ^ 2 * Real.log (g (e z) ^ 2)) γ := by
    apply Integrable.of_bound hlog_meas B
    filter_upwards [] with z
    exact hg_log_bound _
  exact gaussian_logSobolev_euclidean hW12 hg_diff
    hg_grad_cont hlog_int

/-- A uniform bound on `g` automatically bounds the continuous entropy
integrand `g² log(g²)`, so only function and derivative bounds need be
supplied. -/
theorem gaussian_logSobolev_euclidean_of_bound
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_diff : Differentiable ℝ g)
    (hg_grad_cont : Continuous (fun x => fderiv ℝ g x))
    {C D : ℝ} (hC : 0 ≤ C)
    (hg_bound : ∀ x, ‖g x‖ ≤ C)
    (hg_grad_bound : ∀ x, ‖fderiv ℝ g x‖ ≤ D) :
    boltzmannEntropy
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (fun x => g x ^ 2) ≤
      2 * ∫ x : EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ g x‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  obtain ⟨B, hB⟩ :=
    GaussianPoincare.mul_log_bounded_on_Icc C hC
  apply gaussian_logSobolev_euclidean_of_bounds
    hg_diff hg_grad_cont hg_bound hg_grad_bound
  intro x
  rw [Real.norm_eq_abs]
  apply hB
  refine ⟨sq_nonneg _, ?_⟩
  have hx : |g x| ≤ C := by
    simpa [Real.norm_eq_abs] using hg_bound x
  calc
    g x ^ 2 = |g x| ^ 2 := (sq_abs (g x)).symm
    _ ≤ C ^ 2 := by nlinarith [abs_nonneg (g x)]

end

end HDP.Appendix
