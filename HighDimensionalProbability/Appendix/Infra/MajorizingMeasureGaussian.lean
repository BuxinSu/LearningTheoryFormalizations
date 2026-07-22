import HighDimensionalProbability.Chapter8_Chaining

/-!
# Gaussian growth estimates for the finite majorizing-measure lower bound

This file develops the probabilistic part of the finite
Fernique--Talagrand lower theorem.  The combinatorial ranked-partition and
admissible-chain construction is kept in separate appendix infrastructure.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace HDP.Chapter8.Appendix

noncomputable section

/-! ## A finite canonical Euclidean representation -/

variable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]

/-- The canonical covariance vector, generalized from `Fin n` to an arbitrary
finite index type. -/
def canonicalCovarianceVectorGeneral [DecidableEq I] (S : Matrix I I ℝ)
    (g : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) g

/-- The canonical point representing one coordinate of a covariance matrix. -/
def canonicalCovariancePointGeneral [DecidableEq I] (S : Matrix I I ℝ) (i : I) :
    EuclideanSpace ℝ I :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).adjoint
    (EuclideanSpace.basisFun I ℝ i)

theorem canonicalCovarianceVectorGeneral_apply [DecidableEq I]
    (S : Matrix I I ℝ)
    (g : EuclideanSpace ℝ I) (i : I) :
    canonicalCovarianceVectorGeneral S g i =
      inner ℝ (canonicalCovariancePointGeneral S i) g := by
  calc
    canonicalCovarianceVectorGeneral S g i =
        inner ℝ (EuclideanSpace.basisFun I ℝ i)
          (canonicalCovarianceVectorGeneral S g) := by
      exact (EuclideanSpace.basisFun_inner I ℝ
        (canonicalCovarianceVectorGeneral S g) i).symm
    _ = inner ℝ (canonicalCovariancePointGeneral S i) g := by
      rw [canonicalCovariancePointGeneral, canonicalCovarianceVectorGeneral,
        ContinuousLinearMap.adjoint_inner_left]

theorem canonicalCovarianceVectorGeneral_hasLaw [DecidableEq I]
    (S : Matrix I I ℝ) :
    HasLaw (canonicalCovarianceVectorGeneral S) (multivariateGaussian 0 S)
      (stdGaussian (EuclideanSpace ℝ I)) := by
  refine ⟨?_, ?_⟩
  · change AEMeasurable
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
      (stdGaussian (EuclideanSpace ℝ I))
    fun_prop
  · change
      (stdGaussian (EuclideanSpace ℝ I)).map
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) =
        (stdGaussian (EuclideanSpace ℝ I)).map
          (fun x => 0 + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
    simp

/-- Every centered finite Gaussian process has the same joint law as a
canonical inner-product process on a finite-dimensional Euclidean space. -/
theorem finiteGaussianProcess_canonicalRepresentation
    (μ : Measure Ω) (X : I → Ω → ℝ)
    (hX : IsGaussianProcess X μ)
    (hX0 : HDP.IsCenteredProcess X μ) :
    ∃ a : I → EuclideanSpace ℝ I,
      IdentDistrib (HDP.Chapter7.processEuclideanVector X)
        (fun g => WithLp.toLp 2 (fun i => inner ℝ (a i) g)) μ
        (stdGaussian (EuclideanSpace ℝ I)) := by
  classical
  let V := HDP.Chapter7.processEuclideanVector X
  let ν := Measure.map V μ
  let S := HDP.Chapter7.gaussianMeasureCovarianceMatrix ν
  let a : I → EuclideanSpace ℝ I :=
    canonicalCovariancePointGeneral S
  have hV := HDP.Chapter7.processEuclideanVector_hasGaussianLaw hX
  have hlaw : ν = multivariateGaussian 0 S := by
    simpa [ν, V, S] using
      HDP.Chapter7.processEuclideanVector_law_eq_multivariateGaussian hX hX0
  have hVX : HasLaw V (multivariateGaussian 0 S) μ := by
    exact ⟨hV.aemeasurable, by simpa [ν] using hlaw⟩
  refine ⟨a, hVX.identDistrib ?_⟩
  have hcan := canonicalCovarianceVectorGeneral_hasLaw (I := I) S
  refine hcan.congr (ae_of_all _ fun g => ?_)
  ext i
  exact (canonicalCovarianceVectorGeneral_apply (I := I) S g i).symm

/-! ## Finite local Gaussian widths -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_inner_stdGaussian_general (x : E) :
    Integrable (fun g : E => inner ℝ (x : E) g) (stdGaussian E) := by
  simpa [real_inner_comm] using
    ((innerSL ℝ) x).integrable_comp
      (isGaussian_stdGaussian (E := E)).integrable_id

theorem integral_inner_stdGaussian_general (x : E) :
    (∫ g : E, inner ℝ x g ∂stdGaussian E) = 0 := by
  simpa [real_inner_comm] using
    integral_strongDual_stdGaussian ((innerSL ℝ) x)

/-- The maximum of the canonical Gaussian process over a nonempty finite
subfamily. -/
def localGaussianMaximum (a : I → E) (A : Finset I) (hA : A.Nonempty) :
    E → ℝ :=
  A.sup' hA fun i => fun g => inner ℝ (a i) g

/-- Expected maximum of a canonical Gaussian process over a nonempty finite
subfamily. -/
def localGaussianWidth (a : I → E) (A : Finset I) (hA : A.Nonempty) : ℝ :=
  ∫ g, localGaussianMaximum a A hA g ∂stdGaussian E

theorem measurable_localGaussianMaximum (a : I → E) (A : Finset I)
    (hA : A.Nonempty) :
    Measurable (localGaussianMaximum a A hA) := by
  unfold localGaussianMaximum
  exact Finset.measurable_sup' hA fun i _ => by fun_prop

theorem integrable_localGaussianMaximum (a : I → E) (A : Finset I)
    (hA : A.Nonempty) :
    Integrable (localGaussianMaximum a A hA) (stdGaussian E) := by
  unfold localGaussianMaximum
  refine Finset.sup'_induction hA (fun i g => inner ℝ (a i) g)
    (p := fun f => Integrable f (stdGaussian E)) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro i hi
    exact integrable_inner_stdGaussian_general (a i)

theorem localGaussianWidth_mono (a : I → E)
    {A B : Finset I} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : A ⊆ B) :
    localGaussianWidth a A hA ≤ localGaussianWidth a B hB := by
  unfold localGaussianWidth
  apply integral_mono
    (integrable_localGaussianMaximum a A hA)
    (integrable_localGaussianMaximum a B hB)
  intro g
  unfold localGaussianMaximum
  rw [Finset.sup'_apply, Finset.sup'_apply]
  apply Finset.sup'_le
  intro i hi
  exact Finset.le_sup' (fun j => inner ℝ (a j) g) (hAB hi)

theorem localGaussianWidth_nonneg (a : I → E)
    (A : Finset I) (hA : A.Nonempty) :
    0 ≤ localGaussianWidth a A hA := by
  let i : I := hA.choose
  have hi : i ∈ A := hA.choose_spec
  have hint := integrable_inner_stdGaussian_general (a i)
  have hpoint : ∀ g,
      inner ℝ (a i) g ≤ localGaussianMaximum a A hA g := by
    intro g
    rw [localGaussianMaximum, Finset.sup'_apply]
    exact Finset.le_sup' (fun j => inner ℝ (a j) g) hi
  calc
    0 = ∫ g, inner ℝ (a i) g ∂stdGaussian E := by
      exact (integral_inner_stdGaussian_general (a i)).symm
    _ ≤ ∫ g, localGaussianMaximum a A hA g ∂stdGaussian E :=
      integral_mono hint (integrable_localGaussianMaximum a A hA) hpoint
    _ = localGaussianWidth a A hA := rfl

/-- The local maximum after translating all indexing points by a chosen
center. -/
def centeredLocalGaussianMaximum
    (a : I → E) (A : Finset I) (hA : A.Nonempty) (c : I) : E → ℝ :=
  A.sup' hA fun i => fun g => inner ℝ (a i - a c) g

@[simp] theorem centeredLocalGaussianMaximum_apply
    (a : I → E) (A : Finset I) (hA : A.Nonempty) (c : I) (g : E) :
    centeredLocalGaussianMaximum a A hA c g =
      A.sup' hA (fun i => inner ℝ (a i - a c) g) := by
  exact Finset.sup'_apply hA
    (fun i => fun x : E => inner ℝ (a i - a c) x) g

theorem measurable_centeredLocalGaussianMaximum
    (a : I → E) (A : Finset I) (hA : A.Nonempty) (c : I) :
    Measurable (centeredLocalGaussianMaximum a A hA c) := by
  unfold centeredLocalGaussianMaximum
  exact Finset.measurable_sup' hA fun i _ => by fun_prop

theorem integrable_centeredLocalGaussianMaximum
    (a : I → E) (A : Finset I) (hA : A.Nonempty) (c : I) :
    Integrable (centeredLocalGaussianMaximum a A hA c)
      (stdGaussian E) := by
  unfold centeredLocalGaussianMaximum
  refine Finset.sup'_induction hA
    (fun i g => inner ℝ (a i - a c) g)
    (p := fun f => Integrable f (stdGaussian E)) ?_ ?_
  · intro f hf g hg
    exact hf.sup hg
  · intro i hi
    exact integrable_inner_stdGaussian_general (a i - a c)

theorem localGaussianMaximum_subtract_center
    (a : I → E) (A : Finset I) (hA : A.Nonempty)
    {c : I} (hc : c ∈ A) (g : E) :
    localGaussianMaximum a A hA g =
      inner ℝ (a c) g +
        centeredLocalGaussianMaximum a A hA c g := by
  unfold localGaussianMaximum centeredLocalGaussianMaximum
  rw [Finset.sup'_apply, Finset.sup'_apply]
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_mem_eq_sup' hA (fun j => inner ℝ (a j) g)
  obtain ⟨j, hj, hmax'⟩ :=
    Finset.exists_mem_eq_sup' hA (fun j => inner ℝ (a j - a c) g)
  rw [hmax, hmax']
  apply le_antisymm
  · have hle := Finset.le_sup'
      (fun z => inner ℝ (a z - a c) g) hi
    rw [hmax', inner_sub_left] at hle
    linarith
  · have hle := Finset.le_sup' (fun z => inner ℝ (a z) g) hj
    rw [hmax] at hle
    rw [inner_sub_left]
    linarith

theorem integral_centeredLocalMaximum
    (a : I → E) (A : Finset I) (hA : A.Nonempty)
    {c : I} (hc : c ∈ A) :
    (∫ g, centeredLocalGaussianMaximum a A hA c g ∂stdGaussian E) =
      localGaussianWidth a A hA := by
  have hcenter := integrable_inner_stdGaussian_general (a c)
  have hlocal := integrable_centeredLocalGaussianMaximum a A hA c
  have hpoint := localGaussianMaximum_subtract_center a A hA hc
  unfold localGaussianWidth
  calc
    (∫ g, centeredLocalGaussianMaximum a A hA c g
        ∂stdGaussian E) =
        ∫ g, (inner ℝ (a c) g +
          centeredLocalGaussianMaximum a A hA c g)
          ∂stdGaussian E := by
      rw [integral_add hcenter hlocal,
        integral_inner_stdGaussian_general]
      simp
    _ = ∫ g, localGaussianMaximum a A hA g ∂stdGaussian E := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => (hpoint g).symm

/-! ## Gaussian concentration in arbitrary finite coordinates -/

/-- Center a real observable under the intrinsic standard Gaussian law. -/
def stdGaussianCentered
    {J : Type*} [Fintype J]
    (F : EuclideanSpace ℝ J → ℝ) (g : EuclideanSpace ℝ J) : ℝ :=
  F g - ∫ y, F y ∂stdGaussian (EuclideanSpace ℝ J)

theorem euclidean_lipschitz_to_coordinate_general
    {J : Type*} [Fintype J]
    {F : EuclideanSpace ℝ J → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (x y : J → ℝ) :
    |F (WithLp.toLp 2 x) - F (WithLp.toLp 2 y)| ≤
      (K : ℝ) * Real.sqrt (∑ k, (x k - y k) ^ 2) := by
  have h := hF.dist_le_mul (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [Real.dist_eq] at h
  simpa only [PiLp.dist_eq_of_L2, Real.dist_eq, sq_abs] using h

/-- A positive-constant Lipschitz observable of an intrinsic finite standard
Gaussian vector has the usual centered subgaussian MGF.  This is the
coordinate-free version of the chapter's `Fin n` theorem. -/
theorem stdGaussian_lipschitz_hasSubgaussianMGF
    {J : Type*} [Fintype J]
    (F : EuclideanSpace ℝ J → ℝ)
    (K : ℝ) (hK : 0 < K)
    (hF : LipschitzWith ⟨K, hK.le⟩ F) :
    HasSubgaussianMGF (stdGaussianCentered F)
      ⟨K ^ 2, sq_nonneg K⟩
      (stdGaussian (EuclideanSpace ℝ J)) := by
  let γcoord : Measure (J → ℝ) :=
    Measure.pi fun _ : J => gaussianReal 0 1
  let W : (J → ℝ) → ℝ := fun z => F (WithLp.toLp 2 z)
  let V : (J → ℝ) → ℝ := fun z => W z / K
  have hWm : Measurable W := hF.continuous.measurable.comp
    (WithLp.measurable_toLp 2 (J → ℝ))
  have hVm : Measurable V := hWm.div_const K
  have hVLip : ∀ x y, |V x - V y| ≤
      Real.sqrt (∑ k, (x k - y k) ^ 2) := by
    intro x y
    rw [show V x - V y = (W x - W y) / K by simp [V]; ring,
      abs_div, abs_of_pos hK]
    rw [div_le_iff₀ hK]
    have hraw := euclidean_lipschitz_to_coordinate_general hF x y
    change |F (WithLp.toLp 2 x) - F (WithLp.toLp 2 y)| ≤
      K * Real.sqrt (∑ k, (x k - y k) ^ 2) at hraw
    simpa only [W, mul_comm] using hraw
  have hV := MatrixConcentration.gaussian_lipschitz_hasSubgaussianMGF_one
    J V hVLip hVm
  have hscaled := hV.const_mul K
  have hmeanV : (∫ y, V y ∂γcoord) =
      (∫ y, W y ∂γcoord) / K := by
    simp only [V, integral_div]
  have hLp : HasLaw (WithLp.toLp 2)
      (stdGaussian (EuclideanSpace ℝ J)) γcoord := by
    refine ⟨(WithLp.measurable_toLp 2 (J → ℝ)).aemeasurable, ?_⟩
    simpa [γcoord] using (map_pi_eq_stdGaussian (ι := J))
  have hmeanW :
      (∫ y, W y ∂γcoord) =
        ∫ g, F g ∂stdGaussian (EuclideanSpace ℝ J) := by
    simpa only [W, Function.comp_apply] using
      hLp.integral_comp hF.continuous.aestronglyMeasurable
  have hcoord' : HasSubgaussianMGF
      (fun z => stdGaussianCentered F (WithLp.toLp 2 z))
      (⟨K ^ 2, sq_nonneg K⟩ * 1) γcoord := by
    refine hscaled.congr (ae_of_all _ fun z => ?_)
    rw [hmeanV, hmeanW]
    simp only [V, W, stdGaussianCentered]
    field_simp
  have hcoord : HasSubgaussianMGF
      (fun z => stdGaussianCentered F (WithLp.toLp 2 z))
      ⟨K ^ 2, sq_nonneg K⟩ γcoord := by
    simpa only [mul_one] using hcoord'
  have hid : HasLaw (fun g : EuclideanSpace ℝ J => g)
      (stdGaussian (EuclideanSpace ℝ J))
      (stdGaussian (EuclideanSpace ℝ J)) := by
    exact ⟨measurable_id.aemeasurable, by simp⟩
  have hident : IdentDistrib
      (fun z => stdGaussianCentered F (WithLp.toLp 2 z))
      (stdGaussianCentered F) γcoord
      (stdGaussian (EuclideanSpace ℝ J)) := by
    have hbase := hLp.identDistrib hid
    have hcomp := hbase.comp
      ((hF.continuous.measurable.sub_const
        (∫ g, F g ∂stdGaussian (EuclideanSpace ℝ J))))
    convert hcomp using 1 <;> funext x <;> rfl
  exact hcoord.congr_identDistrib hident

theorem stdGaussianCentered_eq_zero_of_lipschitz_zero
    {J : Type*} [Fintype J]
    {F : EuclideanSpace ℝ J → ℝ}
    (hF : LipschitzWith 0 F) :
    stdGaussianCentered F = 0 := by
  have hconst : ∀ x, F x = F 0 := by
    intro x
    have h := hF.dist_le_mul x 0
    simp only [NNReal.coe_zero, zero_mul] at h
    exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
  funext g
  simp only [stdGaussianCentered, Pi.zero_apply]
  rw [hconst g]
  have hfun : F = fun _ => F 0 := by
    funext x
    exact hconst x
  rw [hfun]
  simp

/-- Zero-safe Gaussian concentration for a Lipschitz observable in an
arbitrary finite Euclidean coordinate system. -/
theorem stdGaussian_lipschitz_concentration
    {J : Type*} [Fintype J]
    (F : EuclideanSpace ℝ J → ℝ)
    (K : ℝ≥0) (hF : LipschitzWith K F) :
    HDP.SubGaussian (stdGaussianCentered F)
        (stdGaussian (EuclideanSpace ℝ J)) ∧
      HDP.psi2Norm (stdGaussianCentered F)
          (stdGaussian (EuclideanSpace ℝ J)) ≤
        2 * Real.sqrt 5 * K := by
  by_cases hK0 : (K : ℝ) = 0
  · have hzero : stdGaussianCentered F = 0 := by
      apply stdGaussianCentered_eq_zero_of_lipschitz_zero
      have hKnn : K = 0 := NNReal.eq hK0
      simpa [hKnn] using hF
    have hsub : HDP.SubGaussian (stdGaussianCentered F)
        (stdGaussian (EuclideanSpace ℝ J)) := by
      rw [hzero]
      exact (HDP.psi2Norm_le_of_bounded
        (X := fun _ : EuclideanSpace ℝ J => (0 : ℝ))
        (M := 1) zero_lt_one
        (Filter.Eventually.of_forall fun _ => by simp)).1
    constructor
    · exact hsub
    · have hcm : AEMeasurable (stdGaussianCentered F)
          (stdGaussian (EuclideanSpace ℝ J)) :=
        (hF.continuous.measurable.sub_const
          (∫ g, F g ∂stdGaussian (EuclideanSpace ℝ J))).aemeasurable
      have hz : HDP.psi2Norm (stdGaussianCentered F)
          (stdGaussian (EuclideanSpace ℝ J)) = 0 :=
        (HDP.psi2Norm_eq_zero_iff hcm hsub).2 (by rw [hzero])
      simp [hz, hK0]
  · have hK : 0 < (K : ℝ) :=
      lt_of_le_of_ne K.property (Ne.symm hK0)
    have hmgf :=
      stdGaussian_lipschitz_hasSubgaussianMGF F K hK hF
    have h := HDP.Chapter5.psi2Norm_le_of_hasSubgaussianMGF_sq hK hmgf
    constructor
    · exact h.1
    · calc
        HDP.psi2Norm (stdGaussianCentered F)
            (stdGaussian (EuclideanSpace ℝ J))
            ≤ Real.sqrt 5 * (2 * (K : ℝ)) := h.2
        _ = 2 * Real.sqrt 5 * K := by ring

theorem lipschitzWith_centeredLocalGaussianMaximum
    {J : Type*} [Fintype J]
    (a : I → EuclideanSpace ℝ J)
    (A : Finset I) (hA : A.Nonempty) (c : I)
    (σ : ℝ≥0)
    (hball : ∀ i ∈ A, ‖a i - a c‖ ≤ (σ : ℝ)) :
    LipschitzWith σ
      (centeredLocalGaussianMaximum a A hA c) := by
  unfold centeredLocalGaussianMaximum
  have hcoord : ∀ i ∈ A,
      LipschitzWith σ
        (fun g : EuclideanSpace ℝ J => inner ℝ (a i - a c) g) := by
    intro i hi
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq]
    have hinner :
        |inner ℝ (a i - a c) (x - y)| ≤
          ‖a i - a c‖ * ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using
        (@norm_inner_le_norm ℝ (EuclideanSpace ℝ J) _ _ _
          (a i - a c) (x - y))
    calc
      |inner ℝ (a i - a c) x - inner ℝ (a i - a c) y| =
          |inner ℝ (a i - a c) (x - y)| := by
            rw [inner_sub_right]
      _ ≤ ‖a i - a c‖ * ‖x - y‖ := hinner
      _ ≤ (σ : ℝ) * ‖x - y‖ := by
        gcongr
        exact hball i hi
      _ = (σ : ℝ) * dist x y := by rw [dist_eq_norm]
  refine Finset.sup'_induction hA
    (fun i => fun g : EuclideanSpace ℝ J =>
      inner ℝ (a i - a c) g)
    (p := fun f => LipschitzWith σ f) ?_ ?_
  · intro f hf g hg
    rw [show (f ⊔ g) = fun x => max (f x) (g x) from rfl]
    simpa only [max_self] using hf.max hg
  · intro i hi
    exact hcoord i hi

/-- A local canonical Gaussian maximum, centered by its expectation, has
subgaussian scale controlled by the radius about any member chosen as center. -/
theorem centeredLocalGaussianMaximum_concentration
    {J : Type*} [Fintype J]
    (a : I → EuclideanSpace ℝ J)
    (A : Finset I) (hA : A.Nonempty) {c : I} (hc : c ∈ A)
    (σ : ℝ≥0)
    (hball : ∀ i ∈ A, ‖a i - a c‖ ≤ (σ : ℝ)) :
    HDP.SubGaussian
        (fun g => centeredLocalGaussianMaximum a A hA c g -
          localGaussianWidth a A hA)
        (stdGaussian (EuclideanSpace ℝ J)) ∧
      HDP.psi2Norm
          (fun g => centeredLocalGaussianMaximum a A hA c g -
            localGaussianWidth a A hA)
          (stdGaussian (EuclideanSpace ℝ J)) ≤
        2 * Real.sqrt 5 * σ := by
  have hconc := stdGaussian_lipschitz_concentration
    (centeredLocalGaussianMaximum a A hA c) σ
    (lipschitzWith_centeredLocalGaussianMaximum a A hA c σ hball)
  have hcenterEq :
      stdGaussianCentered (centeredLocalGaussianMaximum a A hA c) =
        (fun g => centeredLocalGaussianMaximum a A hA c g -
          localGaussianWidth a A hA) := by
    funext g
    simp only [stdGaussianCentered]
    rw [integral_centeredLocalMaximum a A hA hc]
  rw [hcenterEq] at hconc
  exact hconc

/-! ## A separated-center Sudakov bound -/

theorem processIncrement_sq_eq_secondMoment
    {T Ω' : Type*} [MeasurableSpace Ω']
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Z : T → Ω' → ℝ) (hZ : IsGaussianProcess Z ν)
    (hZ0 : HDP.IsCenteredProcess Z ν)
    (hZ2 : HDP.IsL2Process Z ν) (s t : T) :
    HDP.processIncrement Z ν s t ^ 2 =
      HDP.Chapter7.processIncrementSecondMoment ν Z s t := by
  rw [HDP.processIncrement_sq_eq_covariance hZ2 hZ0,
    HDP.Chapter7.processIncrementSecondMoment_eq hZ]
  simp only [HDP.Chapter7.processSecondMoment]
  rw [HDP.processCovariance_eq_integral_mul hZ0,
    HDP.processCovariance_eq_integral_mul hZ0,
    HDP.processCovariance_eq_integral_mul hZ0]
  ring_nf

/-- A finite separated family of canonical Gaussian coordinates has expected
maximum at least a universal constant times separation times square-root
logarithmic cardinality.  This is a public half-scale consequence of the
chapter's Sudakov inequality. -/
theorem separatedCanonicalGaussian_lower
    {k : ℕ} (a : I → E) (c : Fin (k + 2) → I) (ε : ℝ≥0)
    (hε : 0 < ε)
    (hsep : ∀ i j, i ≠ j →
      (ε : ℝ) < dist (a (c i)) (a (c j))) :
    (1 / 200 : ℝ) * ε *
        Real.sqrt (Real.log ((k : ℝ) + 2)) ≤
      ∫ g, Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)
        ∂stdGaussian E := by
  classical
  let p : Fin (k + 2) → E := fun i => a (c i)
  let Y : Fin (k + 2) → E → ℝ :=
    HDP.Chapter7.canonicalGaussianProcess p
  letI : PseudoMetricSpace (Fin (k + 2)) :=
    PseudoMetricSpace.induced p (by infer_instance)
  have hY : IsGaussianProcess Y (stdGaussian E) :=
    HDP.Chapter7.canonicalGaussianProcess_isGaussian p
  have hY0 : HDP.IsCenteredProcess Y (stdGaussian E) :=
    HDP.Chapter7.canonicalGaussianProcess_centered p
  have hY2 : HDP.IsL2Process Y (stdGaussian E) :=
    HDP.Chapter7.canonicalGaussianProcess_memLp_two p
  have hcanonical : ∀ i j,
      dist i j ^ 2 =
        HDP.Chapter7.processIncrementSecondMoment (stdGaussian E) Y i j := by
    intro i j
    change dist (p i) (p j) ^ 2 =
      HDP.Chapter7.processIncrementSecondMoment (stdGaussian E) Y i j
    rw [dist_eq_norm]
    rw [← HDP.Chapter7.canonicalGaussianProcess_increment p i j]
    exact processIncrement_sq_eq_secondMoment
      (stdGaussian E) Y hY hY0 hY2 i j
  let δ : ℝ≥0 := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcoverfinite :
      Metric.coveringNumber δ (Set.univ : Set (Fin (k + 2))) ≠ ⊤ := by
    apply ne_of_lt
    refine (Metric.coveringNumber_le_encard_self
      (Set.univ : Set (Fin (k + 2)))).trans_lt ?_
    simpa using ENat.coe_lt_top (k + 2)
  have hsepSet : Metric.IsSeparated (ε : ℝ≥0∞)
      (Set.univ : Set (Fin (k + 2))) := by
    intro i hi j hj hij
    have hdist : dist i j = dist (a (c i)) (a (c j)) := by
      change dist (p i) (p j) = _
      simp [p]
    simpa [edist_dist, hdist] using hsep i j hij
  have hcoverlower : ((k + 2 : ℕ) : ℕ∞) ≤
      Metric.coveringNumber δ (Set.univ : Set (Fin (k + 2))) := by
    calc
      ((k + 2 : ℕ) : ℕ∞) =
          (Set.univ : Set (Fin (k + 2))).encard := by simp
      _ ≤ Metric.packingNumber ε (Set.univ : Set (Fin (k + 2))) :=
        hsepSet.encard_le_packingNumber (by simp)
      _ = Metric.packingNumber (2 * δ)
          (Set.univ : Set (Fin (k + 2))) := by
        congr 2
        ext
        change (ε : ℝ) = 2 * ((ε : ℝ) / 2)
        ring
      _ ≤ Metric.externalCoveringNumber δ
          (Set.univ : Set (Fin (k + 2))) :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber δ _
      _ ≤ Metric.coveringNumber δ
          (Set.univ : Set (Fin (k + 2))) :=
        Metric.externalCoveringNumber_le_coveringNumber δ _
  let M : ℕ := HDP.finiteCoveringNumber δ
    (Set.univ : Set (Fin (k + 2))) hcoverfinite
  have hM : k + 2 ≤ M := by
    have hM' : ((k + 2 : ℕ) : ℕ∞) ≤ (M : ℕ∞) := by
      rw [show (M : ℕ∞) = Metric.coveringNumber δ
          (Set.univ : Set (Fin (k + 2))) by
        exact HDP.coe_finiteCoveringNumber δ
          (Set.univ : Set (Fin (k + 2))) hcoverfinite]
      exact hcoverlower
    exact_mod_cast hM'
  have hlog : Real.log ((k : ℝ) + 2) ≤ Real.log (M : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (k : ℝ) + 2 by positivity)
    · have hMpos : 0 < M := by omega
      simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (M : ℝ) by exact_mod_cast hMpos)
    · have hMreal : ((k + 2 : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hM
      simpa [Nat.cast_add, Nat.cast_ofNat] using hMreal
  have hsqrt : Real.sqrt (Real.log ((k : ℝ) + 2)) ≤
      Real.sqrt (Real.log (M : ℝ)) :=
    Real.sqrt_le_sqrt hlog
  have hsud := HDP.Chapter7.sudakovInequality
    (stdGaussian E) Y hY hY0 hcanonical δ hδ hcoverfinite
  calc
    (1 / 200 : ℝ) * ε * Real.sqrt (Real.log ((k : ℝ) + 2)) =
        (1 / 100 : ℝ) * δ *
          Real.sqrt (Real.log ((k : ℝ) + 2)) := by
      dsimp [δ]
      ring
    _ ≤ (1 / 100 : ℝ) * δ * Real.sqrt (Real.log (M : ℝ)) := by
      gcongr
    _ ≤ HDP.Chapter7.expectedFiniteSupremum (stdGaussian E) Y := by
      simpa [M] using hsud
    _ = ∫ g, Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)
        ∂stdGaussian E := by
      rfl

/-- Super-Sudakov growth for a separated family of local Gaussian pieces.
The loss on the right is precisely the Gaussian-concentration error coming
from the radii of the pieces. -/
theorem separatedLocalGaussian_growth
    {J : Type*} [Fintype J] {k : ℕ}
    (a : I → EuclideanSpace ℝ J)
    (A : Finset I) (hA : A.Nonempty)
    (c : Fin (k + 2) → I)
    (H : Fin (k + 2) → Finset I)
    (hH : ∀ i, (H i).Nonempty)
    (hcH : ∀ i, c i ∈ H i)
    (hHA : ∀ i, H i ⊆ A)
    (r : Fin (k + 2))
    (hwidth : ∀ i,
      localGaussianWidth a (H r) (hH r) ≤
        localGaussianWidth a (H i) (hH i))
    (ε σ : ℝ≥0) (hε : 0 < ε)
    (hsep : ∀ i j, i ≠ j →
      (ε : ℝ) < dist (a (c i)) (a (c j)))
    (hball : ∀ i x, x ∈ H i →
      ‖a x - a (c i)‖ ≤ (σ : ℝ)) :
    (1 / 200 : ℝ) * ε *
          Real.sqrt (Real.log ((k : ℝ) + 2)) +
        localGaussianWidth a (H r) (hH r) ≤
      localGaussianWidth a A hA +
        4 * Real.sqrt 5 *
          Real.sqrt (Real.log ((k : ℝ) + 4)) * σ := by
  classical
  let G : Fin (k + 2) → ℝ := fun i =>
    localGaussianWidth a (H i) (hH i)
  let N : Fin (k + 2) → EuclideanSpace ℝ J → ℝ := fun i =>
    centeredLocalGaussianMaximum a (H i) (hH i) (c i)
  let Y : Fin (k + 2) → EuclideanSpace ℝ J → ℝ := fun i g =>
    G i - N i g
  have hYm : ∀ i ∈ (Finset.univ : Finset (Fin (k + 2))),
      Measurable (Y i) := by
    intro i hi
    exact measurable_const.sub
      (measurable_centeredLocalGaussianMaximum
        a (H i) (hH i) (c i))
  have hYsub : ∀ i ∈ (Finset.univ : Finset (Fin (k + 2))),
      HDP.SubGaussian (Y i)
        (stdGaussian (EuclideanSpace ℝ J)) := by
    intro i hi
    have hconc := centeredLocalGaussianMaximum_concentration
      a (H i) (hH i) (hcH i) σ (hball i)
    have hneg := hconc.1.const_mul (-1)
    have hfun :
        (fun g => (-1 : ℝ) *
          (centeredLocalGaussianMaximum a (H i) (hH i) (c i) g -
            localGaussianWidth a (H i) (hH i))) = Y i := by
      funext g
      simp only [Y, N, G]
      ring
    simpa only [hfun] using hneg
  have hYpsi : ∀ i ∈ (Finset.univ : Finset (Fin (k + 2))),
      HDP.psi2Norm (Y i)
          (stdGaussian (EuclideanSpace ℝ J)) ≤
        2 * Real.sqrt 5 * σ := by
    intro i hi
    have hconc := centeredLocalGaussianMaximum_concentration
      a (H i) (hH i) (hcH i) σ (hball i)
    have hfun :
        Y i = fun g => (-1 : ℝ) *
          (centeredLocalGaussianMaximum a (H i) (hH i) (c i) g -
            localGaussianWidth a (H i) (hH i)) := by
      funext g
      simp only [Y, N, G]
      ring
    rw [hfun, HDP.psi2Norm_const_mul]
    simpa using hconc.2
  have herr := HDP.Chapter8.expectation_finset_sup_abs_le
    (μ := stdGaussian (EuclideanSpace ℝ J))
    (Finset.univ : Finset (Fin (k + 2)))
    Finset.univ_nonempty Y hYm hYsub
    (K := 2 * Real.sqrt 5 * (σ : ℝ)) (by positivity) hYpsi
  have herr' :
      (∫ g, Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (k + 2) => |Y i g|)
          ∂stdGaussian (EuclideanSpace ℝ J)) ≤
        4 * Real.sqrt 5 *
          Real.sqrt (Real.log ((k : ℝ) + 4)) * σ := by
    calc
      (∫ g, Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (k + 2) => |Y i g|)
          ∂stdGaussian (EuclideanSpace ℝ J)) ≤
          2 * Real.sqrt
              (Real.log
                (((Finset.univ : Finset (Fin (k + 2))).card : ℝ) + 2)) *
            (2 * Real.sqrt 5 * (σ : ℝ)) := herr
      _ = 4 * Real.sqrt 5 *
          Real.sqrt (Real.log ((k : ℝ) + 4)) * σ := by
        simp only [Finset.card_univ, Fintype.card_fin,
          Nat.cast_add, Nat.cast_ofNat]
        ring_nf
  have hcenterInt :
      Integrable
        (fun g : EuclideanSpace ℝ J =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => inner ℝ (a (c i)) g))
        (stdGaussian (EuclideanSpace ℝ J)) := by
    have hraw := integrable_localGaussianMaximum
      (fun i : Fin (k + 2) => a (c i))
      Finset.univ Finset.univ_nonempty
    have heq :
        (fun g : EuclideanSpace ℝ J =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)) =
        localGaussianMaximum
          (fun i : Fin (k + 2) => a (c i))
          Finset.univ Finset.univ_nonempty := by
      funext g
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i : Fin (k + 2) =>
          fun x : EuclideanSpace ℝ J => inner ℝ (a (c i)) x) g).symm
    rw [heq]
    exact hraw
  have hYint (i : Fin (k + 2)) :
      Integrable (Y i) (stdGaussian (EuclideanSpace ℝ J)) := by
    exact (integrable_const _).sub
      (integrable_centeredLocalGaussianMaximum
        a (H i) (hH i) (c i))
  have herrInt :
      Integrable
        (fun g : EuclideanSpace ℝ J =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => |Y i g|))
        (stdGaussian (EuclideanSpace ℝ J)) := by
    have hraw :
        Integrable
          (Finset.univ.sup' Finset.univ_nonempty
            (fun i => fun g : EuclideanSpace ℝ J => |Y i g|))
          (stdGaussian (EuclideanSpace ℝ J)) := by
      refine Finset.sup'_induction Finset.univ_nonempty
        (fun i => fun g : EuclideanSpace ℝ J => |Y i g|)
        (p := fun f => Integrable f
          (stdGaussian (EuclideanSpace ℝ J))) ?_ ?_
      · intro f hf g hg
        exact hf.sup hg
      · intro i hi
        exact (hYint i).abs
    have heq :
        (fun g : EuclideanSpace ℝ J =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => |Y i g|)) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun i => fun g : EuclideanSpace ℝ J => |Y i g|) := by
      funext g
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i => fun x : EuclideanSpace ℝ J => |Y i x|) g).symm
    rw [heq]
    exact hraw
  have hpoint (g : EuclideanSpace ℝ J) :
      G r +
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => inner ℝ (a (c i)) g) ≤
        localGaussianMaximum a A hA g +
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => |Y i g|) := by
    obtain ⟨i, hi, hmax⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : Fin (k + 2) => inner ℝ (a (c j)) g)
    rw [hmax]
    have hlocal :
        localGaussianMaximum a (H i) (hH i) g ≤
          localGaussianMaximum a A hA g := by
      unfold localGaussianMaximum
      rw [Finset.sup'_apply, Finset.sup'_apply]
      apply Finset.sup'_le
      intro x hx
      exact Finset.le_sup' (fun y => inner ℝ (a y) g)
        (hHA i hx)
    calc
      G r + inner ℝ (a (c i)) g ≤
          G i + inner ℝ (a (c i)) g := by
        gcongr
        exact hwidth i
      _ = localGaussianMaximum a (H i) (hH i) g + Y i g := by
        rw [localGaussianMaximum_subtract_center
          a (H i) (hH i) (hcH i) g]
        simp only [Y, N, G]
        ring
      _ ≤ localGaussianMaximum a A hA g + |Y i g| := by
        exact add_le_add hlocal (le_abs_self (Y i g))
      _ ≤ localGaussianMaximum a A hA g +
          Finset.univ.sup' Finset.univ_nonempty
            (fun j : Fin (k + 2) => |Y j g|) := by
        gcongr
        exact Finset.le_sup' (fun j : Fin (k + 2) => |Y j g|)
          (Finset.mem_univ i)
  have hmain :
      G r +
          (∫ g, Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)
            ∂stdGaussian (EuclideanSpace ℝ J)) ≤
        localGaussianWidth a A hA +
          ∫ g, Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => |Y i g|)
            ∂stdGaussian (EuclideanSpace ℝ J) := by
    calc
      G r +
          (∫ g, Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)
            ∂stdGaussian (EuclideanSpace ℝ J)) =
          ∫ g, (G r +
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 2) => inner ℝ (a (c i)) g))
            ∂stdGaussian (EuclideanSpace ℝ J) := by
        rw [integral_add (integrable_const _) hcenterInt]
        simp
      _ ≤ ∫ g, (localGaussianMaximum a A hA g +
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 2) => |Y i g|))
            ∂stdGaussian (EuclideanSpace ℝ J) := by
        exact integral_mono
          ((integrable_const _).add hcenterInt)
          ((integrable_localGaussianMaximum a A hA).add herrInt)
          hpoint
      _ = localGaussianWidth a A hA +
          ∫ g, Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin (k + 2) => |Y i g|)
            ∂stdGaussian (EuclideanSpace ℝ J) := by
        rw [integral_add
          (integrable_localGaussianMaximum a A hA) herrInt]
        rfl
  have hsud := separatedCanonicalGaussian_lower
    a c ε hε hsep
  calc
    (1 / 200 : ℝ) * ε *
          Real.sqrt (Real.log ((k : ℝ) + 2)) +
        localGaussianWidth a (H r) (hH r) ≤
      (∫ g, Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)
          ∂stdGaussian (EuclideanSpace ℝ J)) + G r := by
        exact add_le_add hsud le_rfl
    _ = G r +
        (∫ g, Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (k + 2) => inner ℝ (a (c i)) g)
          ∂stdGaussian (EuclideanSpace ℝ J)) := by ring
    _ ≤ localGaussianWidth a A hA +
        ∫ g, Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (k + 2) => |Y i g|)
          ∂stdGaussian (EuclideanSpace ℝ J) := hmain
    _ ≤ localGaussianWidth a A hA +
        4 * Real.sqrt 5 *
          Real.sqrt (Real.log ((k : ℝ) + 4)) * σ := by
      gcongr

end

end HDP.Chapter8.Appendix
