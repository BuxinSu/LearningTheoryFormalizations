import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSmoothCore
import HighDimensionalProbability.Appendix.Infra.SLT.GaussianSobolevDense.LipschitzMollification

/-!
# Smooth approximation of Lipschitz observables on `SO(n)`

The chordal Frobenius embedding of `SO(n)` is isometric.  McShane's theorem
therefore extends every unit-Lipschitz observable to the ambient Euclidean
matrix space with the same Lipschitz constant.  After reindexing the `n²`
coordinates, ordinary Euclidean mollification produces globally smooth
unit-Lipschitz approximants with an explicit uniform error.
-/

open Matrix
open scoped NNReal RealInnerProductSpace Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

/-- Chordal embedding of `SO(n)` into its ambient Frobenius Euclidean
space. -/
def specialOrthogonalEmbedding (n : ℕ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    FrobeniusEuclidean n :=
  HDP.gaussianMatrixVectorize U.1

lemma specialOrthogonalEmbedding_injective (n : ℕ) :
    Function.Injective (specialOrthogonalEmbedding n) := by
  intro U V h
  apply Subtype.ext
  have hh := congrArg HDP.gaussianMatrixUnvectorize h
  simpa [specialOrthogonalEmbedding] using hh

lemma continuous_specialOrthogonalEmbedding (n : ℕ) :
    Continuous (specialOrthogonalEmbedding n) :=
  continuous_gaussianMatrixVectorize.comp continuous_subtype_val

/-- The ambient Euclidean distance is exactly the chordal Frobenius
distance. -/
lemma dist_specialOrthogonalEmbedding
    {n : ℕ}
    (U V : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    dist (specialOrthogonalEmbedding n U)
        (specialOrthogonalEmbedding n V) =
      HDP.matrixFrobeniusNorm (U.1 - V.1) := by
  rw [dist_eq_norm]
  change
    ‖HDP.gaussianMatrixVectorize U.1 -
        HDP.gaussianMatrixVectorize V.1‖ =
      HDP.matrixFrobeniusNorm (U.1 - V.1)
  rw [← norm_gaussianMatrixVectorize]
  rfl

/-- A chordally unit-Lipschitz observable on `SO(n)` admits an ambient
unit-Lipschitz extension which agrees with it everywhere on the group. -/
theorem exists_ambient_lipschitzExtension
    (n : ℕ)
    (f : Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ)
    (hf :
      ∀ U V, |f U - f V| ≤
        HDP.matrixFrobeniusNorm (U.1 - V.1)) :
    ∃ H : FrobeniusEuclidean n → ℝ,
      LipschitzWith 1 H ∧
        ∀ U, H (specialOrthogonalEmbedding n U) = f U := by
  let f₀ : FrobeniusEuclidean n → ℝ :=
    fun y =>
      f (Function.invFun (specialOrthogonalEmbedding n) y)
  have hinj :
      Function.Injective (specialOrthogonalEmbedding n) :=
    specialOrthogonalEmbedding_injective n
  have hlip :
      LipschitzOnWith 1 f₀
        (Set.range (specialOrthogonalEmbedding n)) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩
    have hleft :
        Function.invFun (specialOrthogonalEmbedding n)
            (specialOrthogonalEmbedding n U) = U :=
      Function.leftInverse_invFun hinj U
    have hright :
        Function.invFun (specialOrthogonalEmbedding n)
            (specialOrthogonalEmbedding n V) = V :=
      Function.leftInverse_invFun hinj V
    rw [show f₀ (specialOrthogonalEmbedding n U) = f U by
      simp [f₀, hleft],
      show f₀ (specialOrthogonalEmbedding n V) = f V by
        simp [f₀, hright],
      dist_specialOrthogonalEmbedding]
    simpa [Real.dist_eq] using hf U V
  obtain ⟨H, hH, hEq⟩ := hlip.extend_real
  refine ⟨H, hH, fun U => ?_⟩
  rw [← hEq ⟨U, rfl⟩]
  simp [f₀, Function.leftInverse_invFun hinj U]

/-- Isometric coordinate reindexing from matrix coordinates to `Fin (n²)`,
the coordinate type used by the Euclidean mollifier. -/
def frobeniusReindex (n : ℕ) :
    FrobeniusEuclidean n ≃ₗᵢ[ℝ]
      GaussianSobolev.E (n * n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n))

/-- The `k`-th globally smooth approximation of an ambient Lipschitz
function, with mollification scale `1 / (k + 1)`. -/
def smoothLipschitzApproximation
    (n : ℕ) (H : FrobeniusEuclidean n → ℝ) (k : ℕ) :
    FrobeniusEuclidean n → ℝ :=
  fun y =>
    GaussianSobolev.mollify (1 / ((k : ℝ) + 1))
      (H ∘ (frobeniusReindex n).symm)
      (frobeniusReindex n y)

lemma smoothLipschitzApproximation_contDiff
    (n : ℕ) (H : FrobeniusEuclidean n → ℝ)
    (hH : LipschitzWith 1 H) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (smoothLipschitzApproximation n H k) := by
  have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hcomp :
      LipschitzWith 1 (H ∘ (frobeniusReindex n).symm) := by
    simpa using hH.comp (frobeniusReindex n).symm.lipschitz
  exact
    (GaussianSobolev.mollify_smooth_of_lipschitz hcomp hε).comp
      (frobeniusReindex n).contDiff

lemma smoothLipschitzApproximation_lipschitz
    (n : ℕ) (H : FrobeniusEuclidean n → ℝ)
    (hH : LipschitzWith 1 H) (k : ℕ) :
    LipschitzWith 1
      (smoothLipschitzApproximation n H k) := by
  have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hcomp :
      LipschitzWith 1 (H ∘ (frobeniusReindex n).symm) := by
    simpa using hH.comp (frobeniusReindex n).symm.lipschitz
  change
    LipschitzWith 1
      ((GaussianSobolev.mollify (1 / ((k : ℝ) + 1))
        (H ∘ (frobeniusReindex n).symm)) ∘
          (frobeniusReindex n))
  simpa using
    (GaussianSobolev.mollify_lipschitzWith hε hcomp).comp
      (frobeniusReindex n).lipschitz

lemma smoothLipschitzApproximation_fderiv_norm_le
    (n : ℕ) (H : FrobeniusEuclidean n → ℝ)
    (hH : LipschitzWith 1 H) (k : ℕ)
    (y : FrobeniusEuclidean n) :
    ‖fderiv ℝ (smoothLipschitzApproximation n H k) y‖ ≤ 1 :=
  norm_fderiv_le_of_lipschitz ℝ
    (smoothLipschitzApproximation_lipschitz n H hH k)

/-- Explicit uniform approximation error. -/
lemma smoothLipschitzApproximation_dist_le
    (n : ℕ) (H : FrobeniusEuclidean n → ℝ)
    (hH : LipschitzWith 1 H) (k : ℕ)
    (y : FrobeniusEuclidean n) :
    dist (smoothLipschitzApproximation n H k y) (H y) ≤
      (1 / ((k : ℝ) + 1)) * Real.sqrt (n * n) := by
  have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hcomp :
      LipschitzWith 1 (H ∘ (frobeniusReindex n).symm) := by
    simpa using hH.comp (frobeniusReindex n).symm.lipschitz
  have h :=
    GaussianSobolev.mollify_dist_le_of_lipschitz'
      hε hcomp (frobeniusReindex n y)
  simpa [smoothLipschitzApproximation] using h

/-- The smooth approximants converge pointwise (indeed uniformly) to the
ambient Lipschitz extension. -/
lemma smoothLipschitzApproximation_tendsto
    (n : ℕ) (H : FrobeniusEuclidean n → ℝ)
    (hH : LipschitzWith 1 H)
    (y : FrobeniusEuclidean n) :
    Filter.Tendsto
      (fun k => smoothLipschitzApproximation n H k y)
      Filter.atTop (𝓝 (H y)) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero
  · exact fun _ => dist_nonneg
  · exact fun k =>
      smoothLipschitzApproximation_dist_le n H hH k y
  · have h :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
        (Real.sqrt ((n * n : ℕ) : ℝ))
    simpa [Nat.cast_mul] using h

end

end HDP.Appendix.SpecialOrthogonal
