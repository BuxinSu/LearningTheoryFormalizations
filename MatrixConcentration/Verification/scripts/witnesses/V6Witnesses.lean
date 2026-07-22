import Lean
import MatrixConcentration

open Lean Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false
set_option maxHeartbeats 0

namespace MatrixConcentration.V6Witnesses

/-! ## Reusable nonconstant one-coordinate product-sign model -/

abbrev I : Type := Fin 1
abbrev N : Type := Fin 1
abbrev BoolΩ : Type := I → Bool

noncomputable def radMu : Measure BoolΩ :=
  Measure.pi fun _ : I => boolRademacherMeasure

noncomputable local instance : IsProbabilityMeasure radMu := by
  dsimp [radMu]
  infer_instance

def signs (k : I) (ω : BoolΩ) : ℝ :=
  boolSign (ω k)

lemma signs_measurable (k : I) : Measurable (signs k) :=
  measurable_boolSign.comp (measurable_pi_apply k)

lemma signs_law (k : I) : IsRademacher (signs k) radMu := by
  change IsRademacher (fun b : I → Bool => boolSign (b k))
    (Measure.pi fun _ : I => boolRademacherMeasure)
  exact boolSign_law (I := I) k

lemma signs_indep : iIndepFun signs radMu := by
  change iIndepFun (fun k (b : I → Bool) => boolSign (b k))
    (Measure.pi fun _ : I => boolRademacherMeasure)
  exact boolSign_indep (I := I)

noncomputable def hermCoeff (_ : I) : Matrix N N ℂ := 1
noncomputable def rectCoeff (_ : I) : Matrix N N ℂ := 1

lemma hermCoeff_hermitian (k : I) : (hermCoeff k).IsHermitian :=
  Matrix.isHermitian_one

noncomputable def hermSeries (k : I) (ω : BoolΩ) : Matrix N N ℂ :=
  signs k ω • hermCoeff k

lemma hermSeries_measurable (k : I) : Measurable (hermSeries k) :=
  measurable_of_finite _

lemma hermSeries_hermitian (k : I) (ω : BoolΩ) :
    (hermSeries k ω).IsHermitian :=
  isHermitian_real_smul (hermCoeff_hermitian k) _

lemma hermSeries_indep : iIndepFun hermSeries radMu := by
  change iIndepFun
    (fun k ω => signs k ω • hermCoeff k) radMu
  exact signs_indep.comp
    (fun k r => r • hermCoeff k)
    (fun _ => by fun_prop)

lemma hermSeries_norm_le_one (k : I) (ω : BoolΩ) :
    ‖hermSeries k ω‖ ≤ (1 : ℝ) := by
  by_cases h : ω k = true <;>
    simp [hermSeries, hermCoeff, signs, boolSign, h]

lemma hermSeries_mIntegrable (k : I) : MIntegrable (hermSeries k) radMu :=
  fun _ _ => Integrable.of_finite

lemma hermSeries_sq_mIntegrable (k : I) :
    MIntegrable (fun ω => hermSeries k ω * hermSeries k ω) radMu :=
  fun _ _ => Integrable.of_finite

lemma hermSeries_centered (k : I) :
    expectation radMu (hermSeries k) = 0 := by
  ext i j
  rw [expectation_apply]
  change
    (∫ ω, (signs k ω : ℂ) • hermCoeff k i j ∂radMu) = (0 : ℂ)
  rw [integral_smul_const, integral_complex_ofReal,
    integral_id_isRademacher (signs_measurable k) (signs_law k)]
  simp

/-! ## Tier-B boundary witnesses for all six SUSPECT definitions -/

theorem suspect_sampleCovariance_zero_samples
    {Ω : Type*} [MeasurableSpace Ω] {P : ℕ}
    (μ : Measure Ω) (xs : Fin 0 → Ω → Fin P → ℂ) (ω : Ω) :
    sampleCovariance μ 0 xs ω = 0 := by
  simp [sampleCovariance]

theorem suspect_lambdaMax_fin_zero :
    lambdaMax (Matrix.isHermitian_zero (n := Fin 0) (α := ℂ)) = 0 :=
  lambdaMax_of_isEmpty Matrix.isHermitian_zero

theorem suspect_lambdaMin_fin_zero :
    lambdaMin (Matrix.isHermitian_zero (n := Fin 0) (α := ℂ)) = 0 :=
  lambdaMin_of_isEmpty Matrix.isHermitian_zero

theorem suspect_stableRank_zero_matrix :
    stableRank (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [stableRank, frobeniusNorm]

theorem suspect_secondSmallestEigenvalue_fin_one :
    secondSmallestEigenvalue
        (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)) = 0 := by
  simp [secondSmallestEigenvalue]

noncomputable def unboundedRatMatrixFamily :
    ℚ → Unit → Matrix Unit Unit ℂ :=
  fun q _ => (q : ℂ) • 1

theorem suspect_maxSummandSq_unbounded_family_collapse :
    maxSummandSq unboundedRatMatrixFamily (Measure.dirac ()) = 0 := by
  rw [maxSummandSq]
  have hsup : (⨆ q : ℚ, ‖unboundedRatMatrixFamily q ()‖ ^ 2) = 0 := by
    rw [Real.iSup_of_not_bddAbove]
    rintro ⟨a, ha⟩
    obtain ⟨q, hq⟩ := exists_rat_gt (max a 1)
    have hqa : a < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq
    have hq1 : 1 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq
    have hq_sq : (q : ℝ) < (q : ℝ) ^ 2 := by nlinarith
    have hmem :
        (q : ℝ) ^ 2 ∈ Set.range
          (fun q : ℚ => ‖unboundedRatMatrixFamily q ()‖ ^ 2) := by
      refine ⟨q, ?_⟩
      simp [unboundedRatMatrixFamily, norm_smul, abs_of_pos (hq1.trans' zero_lt_one)]
    exact (not_lt_of_ge (ha hmem)) (hqa.trans hq_sq)
  simp [hsup]

/- Non-boundary witnesses show that the five intentionally totalized
definitions also have ordinary nondegenerate models. -/

theorem suspect_lambdaMax_nonzero_model :
    lambdaMax (Matrix.isHermitian_one (n := Fin 2) (α := ℂ)) = 1 :=
  lambdaMax_one

theorem suspect_lambdaMin_nonzero_model :
    lambdaMin (Matrix.isHermitian_one (n := Fin 2) (α := ℂ)) = 1 :=
  lambdaMin_one

theorem suspect_stableRank_nonzero_model :
    1 ≤ stableRank (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  one_le_stableRank one_ne_zero

theorem suspect_secondSmallest_nonzero_model :
    0 < secondSmallestEigenvalue
      (isHermitian_lapMatrixC (SimpleGraph.completeGraph (Fin 2))) := by
  exact (connected_iff_secondSmallest_pos
    (SimpleGraph.completeGraph (Fin 2)) (by decide)).mp SimpleGraph.connected_top

def oneSample (_ : Fin 1) (_ : Unit) (_ : Fin 1) : ℂ := 1

theorem suspect_sampleCovariance_nonzero_model :
    sampleCovariance (Measure.dirac ()) 1 oneSample () = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [sampleCovariance, oneSample, vecMulVec]

noncomputable def finiteNonzeroMatrixFamily :
    Fin 1 → Unit → Matrix Unit Unit ℂ :=
  fun _ _ => 1

theorem suspect_maxSummandSq_finite_nonzero_model :
    maxSummandSq finiteNonzeroMatrixFamily (Measure.dirac ()) = 1 := by
  simp [maxSummandSq, finiteNonzeroMatrixFamily]

/-! ## Fresh named witnesses for randomly sampled endpoints lacking citations -/

theorem sampled_bernstein_variance_identity :
    ∫ ω, (∑ k, signs k ω) ^ 2 ∂radMu =
      ∑ k, ∫ ω, (signs k ω) ^ 2 ∂radMu := by
  exact bernstein_variance_identity
    (L := 1)
    signs_indep signs_measurable
    (fun k => integral_id_isRademacher (signs_measurable k) (signs_law k))
    (fun k => Filter.Eventually.of_forall fun ω => by
      by_cases h : ω k = true <;> simp [signs, boolSign, h])

theorem sampled_lambdaMin_neg :
    lambdaMin
        (Matrix.isHermitian_one (n := Fin 2) (α := ℂ)).neg =
      -lambdaMax (Matrix.isHermitian_one (n := Fin 2) (α := ℂ)) :=
  lambdaMin_neg Matrix.isHermitian_one

theorem sampled_stableRank_le_rank :
    stableRank (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤
      ((1 : Matrix (Fin 2) (Fin 2) ℂ).rank : ℝ) :=
  stableRank_le_rank one_ne_zero

theorem sampled_matrix_exp_add_of_commute :
    NormedSpace.exp
        ((1 : Matrix N N ℂ) + (1 : Matrix N N ℂ)) =
      NormedSpace.exp (1 : Matrix N N ℂ) *
        NormedSpace.exp (1 : Matrix N N ℂ) :=
  matrix_exp_add_of_commute (Commute.refl (1 : Matrix N N ℂ))

theorem sampled_scalar_cgf_sum (θ : ℝ) :
    Real.log (ProbabilityTheory.mgf (fun ω => ∑ k, signs k ω) radMu θ) =
      ∑ k, Real.log (ProbabilityTheory.mgf (signs k) radMu θ) := by
  exact scalar_cgf_sum signs_indep signs_measurable
    (fun _ => Integrable.of_finite)

theorem sampled_master_expectation_upper_inf_hypotheses :
    (∀ k, Measurable (hermSeries k)) ∧
    (∀ k ω, (hermSeries k ω).IsHermitian) ∧
    (∀ k ω, ‖hermSeries k ω‖ ≤ (1 : ℝ)) ∧
    iIndepFun hermSeries radMu :=
  ⟨hermSeries_measurable, hermSeries_hermitian,
    hermSeries_norm_le_one, hermSeries_indep⟩

theorem sampled_rademacher_rect_expectation :
    ∫ ω, ‖∑ k, signs k ω • rectCoeff k‖ ∂radMu ≤
      Real.sqrt (2 *
        max ‖∑ k, rectCoeff k * (rectCoeff k)ᴴ‖
          ‖∑ k, (rectCoeff k)ᴴ * rectCoeff k‖ *
        Real.log (Fintype.card N + Fintype.card N)) := by
  exact rademacher_series_rect_expectation_of_isRademacher
    signs_measurable signs_law signs_indep

theorem sampled_rademacher_herm_min_tail :
    radMu.real {ω |
        lambdaMin (isHermitian_matsum Finset.univ
          (fun k => isHermitian_real_smul
            (hermCoeff_hermitian k) (signs k ω))) ≤ -(1 : ℝ)} ≤
      (Fintype.card N : ℝ) *
        Real.exp (-((1 : ℝ) ^ 2) /
          (2 * ‖∑ k, (hermCoeff k) ^ 2‖)) := by
  exact rademacher_herm_min_tail_of_isRademacher
    signs_measurable signs_law signs_indep hermCoeff_hermitian (by positivity)

theorem sampled_rademacher_second_moment :
    (expectation radMu fun ω =>
        (∑ k, signs k ω • rectCoeff k) *
          (∑ k, signs k ω • rectCoeff k)ᴴ) =
        ∑ k, rectCoeff k * (rectCoeff k)ᴴ ∧
      (expectation radMu fun ω =>
        (∑ k, signs k ω • rectCoeff k)ᴴ *
          (∑ k, signs k ω • rectCoeff k)) =
        ∑ k, (rectCoeff k)ᴴ * rectCoeff k := by
  exact rademacher_series_second_moment
    signs_measurable signs_law signs_indep

/- A d=2 product Gaussian Toeplitz model avoids both zero-dimensional and
single-diagonal boundary cases. -/
abbrev ToeplitzI : Type := Unit ⊕ Fin (2 - 1) ⊕ Fin (2 - 1)
abbrev GaussΩ : Type := ToeplitzI → ℝ

noncomputable def gaussMu : Measure GaussΩ :=
  Measure.pi fun _ : ToeplitzI => gaussianReal 0 1

noncomputable local instance : IsProbabilityMeasure gaussMu := by
  dsimp [gaussMu]
  infer_instance

def gaussCoords (p : ToeplitzI) (ω : GaussΩ) : ℝ := ω p

lemma gaussCoords_measurable (p : ToeplitzI) : Measurable (gaussCoords p) :=
  measurable_pi_apply p

lemma gaussCoords_law (p : ToeplitzI) :
    IsStdGaussian (gaussCoords p) gaussMu := by
  rw [IsStdGaussian]
  change Measure.map (fun ω : ToeplitzI → ℝ => ω p)
      (Measure.pi fun _ : ToeplitzI => gaussianReal 0 1) =
    gaussianReal 0 1
  exact (measurePreserving_eval
    (fun _ : ToeplitzI => gaussianReal 0 1) p).map_eq

lemma gaussCoords_indep : iIndepFun gaussCoords gaussMu := by
  change iIndepFun (fun p (ω : ToeplitzI → ℝ) => ω p)
    (Measure.pi fun _ : ToeplitzI => gaussianReal 0 1)
  simpa only [id_eq] using
    (iIndepFun_pi (X := fun _ : ToeplitzI => id)
      (fun _ => measurable_id.aemeasurable))

theorem sampled_toeplitz_expected_norm :
    ∫ ω, ‖∑ p, gaussCoords p ω • toeplitzCoeff 2 p‖ ∂gaussMu ≤
      Real.sqrt (2 * (2 : ℝ) * Real.log (2 * 2)) := by
  exact toeplitz_expected_norm
    gaussCoords_measurable gaussCoords_law gaussCoords_indep

/- A genuinely nonconstant product Bernoulli model, used for the sampled
Chapter-5 and Chapter-7 Bernoulli/Chernoff endpoints. -/
abbrev BernΩ : Type := I → ℝ

lemma half_mem_Icc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

noncomputable local instance bernBaseProbability :
    IsProbabilityMeasure (bernoulliMeasureReal (1 / 2 : ℝ)) :=
  isProbabilityMeasure_bernoulliMeasureReal half_mem_Icc

noncomputable def bernMu : Measure BernΩ :=
  Measure.pi fun _ : I => bernoulliMeasureReal (1 / 2 : ℝ)

noncomputable local instance : IsProbabilityMeasure bernMu := by
  dsimp [bernMu]
  infer_instance

def bernCoords (k : I) (ω : BernΩ) : ℝ := ω k

lemma bernCoords_measurable (k : I) : Measurable (bernCoords k) :=
  measurable_pi_apply k

lemma bernCoords_law (k : I) :
    IsBernoulli (1 / 2 : ℝ) (bernCoords k) bernMu := by
  rw [IsBernoulli]
  change Measure.map (fun ω : I → ℝ => ω k)
      (Measure.pi fun _ : I => bernoulliMeasureReal (1 / 2 : ℝ)) =
    bernoulliMeasureReal (1 / 2 : ℝ)
  exact (measurePreserving_eval
    (fun _ : I => bernoulliMeasureReal (1 / 2 : ℝ)) k).map_eq

lemma bernCoords_indep : iIndepFun bernCoords bernMu := by
  change iIndepFun (fun k (ω : I → ℝ) => ω k)
    (Measure.pi fun _ : I => bernoulliMeasureReal (1 / 2 : ℝ))
  simpa only [id_eq] using
    (iIndepFun_pi (X := fun _ : I => id)
      (fun _ => measurable_id.aemeasurable))

theorem sampled_column_submatrix_upper_hypotheses :
    (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ k, Measurable (bernCoords k)) ∧
    (∀ k, IsBernoulli (1 / 2 : ℝ) (bernCoords k) bernMu) ∧
    iIndepFun bernCoords bernMu ∧
    (1 : Matrix N N ℂ) ≠ 0 := by
  exact ⟨half_mem_Icc, bernCoords_measurable, bernCoords_law,
    bernCoords_indep, one_ne_zero⟩

noncomputable def bernHerm (k : I) (ω : BernΩ) : Matrix N N ℂ :=
  bernCoords k ω • (1 : Matrix N N ℂ)

lemma bernHerm_measurable (k : I) : Measurable (bernHerm k) := by
  change Measurable
    ((fun r : ℝ => r • (1 : Matrix N N ℂ)) ∘ bernCoords k)
  exact
    (show Measurable (fun r : ℝ => r • (1 : Matrix N N ℂ)) by
      fun_prop).comp (bernCoords_measurable k)

lemma bernHerm_hermitian (k : I) (ω : BernΩ) :
    (bernHerm k ω).IsHermitian :=
  isHermitian_real_smul Matrix.isHermitian_one _

lemma bernHerm_indep : iIndepFun bernHerm bernMu := by
  change iIndepFun
    (fun k ω => bernCoords k ω • (1 : Matrix N N ℂ)) bernMu
  exact bernCoords_indep.comp
    (fun _ r => r • (1 : Matrix N N ℂ))
    (fun _ => by fun_prop)

lemma bernHerm_expectation (k : I) :
    expectation bernMu (bernHerm k) =
      (1 / 2 : ℝ) • (1 : Matrix N N ℂ) := by
  ext i j
  rw [expectation_apply]
  change
    (∫ ω, (bernCoords k ω : ℂ) • (1 : Matrix N N ℂ) i j ∂bernMu) =
      ((1 / 2 : ℝ) • (1 : Matrix N N ℂ)) i j
  rw [integral_smul_const, integral_complex_ofReal,
    integral_id_isBernoulli half_mem_Icc
      (bernCoords_measurable k) (bernCoords_law k)]
  rfl

lemma bernHerm_min_ae (k : I) :
    ∀ᵐ ω ∂bernMu, 0 ≤ lambdaMin (bernHerm_hermitian k ω) := by
  filter_upwards
    [ae_range_isBernoulli half_mem_Icc
      (bernCoords_measurable k) (bernCoords_law k)] with ω hω
  have hnonneg : 0 ≤ bernCoords k ω := by
    rcases hω with hω | hω <;> simp [hω]
  have hpsd : (bernHerm k ω).PosSemidef := by
    exact Matrix.PosDef.one.posSemidef.smul hnonneg
  exact le_lambdaMin _ fun i => hpsd.eigenvalues_nonneg i

lemma bernHerm_max_ae (k : I) :
    ∀ᵐ ω ∂bernMu, lambdaMax (bernHerm_hermitian k ω) ≤ (1 : ℝ) := by
  filter_upwards
    [ae_range_isBernoulli half_mem_Icc
      (bernCoords_measurable k) (bernCoords_law k)] with ω hω
  have hnonneg : 0 ≤ bernCoords k ω := by
    rcases hω with hω | hω <;> simp [hω]
  have hle : bernCoords k ω ≤ 1 := by
    rcases hω with hω | hω <;> simp [hω]
  calc
    lambdaMax (bernHerm_hermitian k ω) ≤
        |lambdaMax (bernHerm_hermitian k ω)| := le_abs_self _
    _ ≤ ‖bernHerm k ω‖ :=
      abs_lambdaMax_le (bernHerm_hermitian k ω)
    _ = |bernCoords k ω| := by
      simp [bernHerm]
    _ = bernCoords k ω := abs_of_nonneg hnonneg
    _ ≤ 1 := hle

lemma bernHerm_expectation_sum_le_one :
    (∑ k, expectation bernMu (bernHerm k)) ≤
      (1 : Matrix N N ℂ) := by
  simp only [Fin.sum_univ_one, bernHerm_expectation]
  have h := smul_le_smul_of_posSemidef
    (P := (1 : Matrix N N ℂ)) Matrix.PosDef.one.posSemidef
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  simpa using h

theorem sampled_intdim_chernoff_expectation_ae_hypotheses :
    (∀ k, Measurable (bernHerm k)) ∧
    (∀ k ω, (bernHerm k ω).IsHermitian) ∧
    (∀ k, ∀ᵐ ω ∂bernMu, 0 ≤ lambdaMin (bernHerm_hermitian k ω)) ∧
    (∀ k, ∀ᵐ ω ∂bernMu,
      lambdaMax (bernHerm_hermitian k ω) ≤ (1 : ℝ)) ∧
    iIndepFun bernHerm bernMu ∧
    (0 : ℝ) < 1 ∧
    (1 : Matrix N N ℂ).PosSemidef ∧
    (1 : Matrix N N ℂ) ≠ 0 ∧
    (∑ k, expectation bernMu (bernHerm k)) ≤
      (1 : Matrix N N ℂ) := by
  exact ⟨bernHerm_measurable, bernHerm_hermitian, bernHerm_min_ae,
    bernHerm_max_ae, bernHerm_indep, by norm_num,
    Matrix.PosDef.one.posSemidef, one_ne_zero,
    bernHerm_expectation_sum_le_one⟩

theorem sampled_bernstein_cgf_ae_hypotheses :
    Measurable (hermSeries (0 : I)) ∧
    (∀ ω, (hermSeries (0 : I) ω).IsHermitian) ∧
    MIntegrable (hermSeries (0 : I)) radMu ∧
    MIntegrable (fun ω => hermSeries (0 : I) ω * hermSeries (0 : I) ω) radMu ∧
    expectation radMu (hermSeries (0 : I)) = 0 ∧
    (∀ᵐ ω ∂radMu,
      lambdaMax (hermSeries_hermitian (0 : I) ω) ≤ (1 : ℝ)) ∧
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) * 1 < 3 := by
  refine ⟨hermSeries_measurable 0, hermSeries_hermitian 0,
    hermSeries_mIntegrable 0, hermSeries_sq_mIntegrable 0,
    hermSeries_centered 0, ?_, by positivity, by positivity, by norm_num⟩
  exact Filter.Eventually.of_forall fun ω =>
    ((le_abs_self _).trans
      (abs_lambdaMax_le (hermSeries_hermitian 0 ω))).trans
        (hermSeries_norm_le_one 0 ω)

theorem sampled_varStat_summand_le_varAW :
    ‖∑ k, expectation radMu fun ω => hermSeries k ω * hermSeries k ω‖ ≤
      varAW radMu hermSeries :=
  varStat_summand_le_varAW hermSeries

theorem sampled_intdim_not_monotone :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧ A ≤ B ∧ intdim B < intdim A :=
  intdim_not_monotone

theorem sampled_matrixPerspective_arg_posDef :
    ((posSqrt (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (posSqrt (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹).PosDef :=
  matrixPerspective_arg_posDef Matrix.PosDef.one Matrix.PosDef.one

theorem sampled_one_le_inv_of_le_one :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤
      (1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
  one_le_inv_of_le_one Matrix.PosDef.one (le_refl 1)

/-! ## Additional named applications required by the stratified OK sample -/

theorem sampled_schattenOneAddGroupNorm_nonzero :
    (schattenOneAddGroupNorm (m := Fin 1) (n := Fin 1)).toFun
        (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 := by
  intro h
  have hzero :=
    (schattenOneAddGroupNorm (m := Fin 1) (n := Fin 1)).eq_zero_of_map_eq_zero' _ h
  exact one_ne_zero hzero

theorem sampled_varStat_sum :
    varStat radMu (fun ω => ∑ k, hermSeries k ω) =
      max ‖∑ k, matrixVar1 radMu (hermSeries k)‖
        ‖∑ k, matrixVar2 radMu (hermSeries k)‖ := by
  exact varStat_sum hermSeries_indep hermSeries_measurable
    hermSeries_mIntegrable
    (fun _ => fun _ _ => Integrable.of_finite)
    (fun _ => fun _ _ => Integrable.of_finite)

theorem sampled_matrixFun_powerSeries_constant_one :
    let c : ℕ → ℝ := fun q => if q = 0 then 1 else 0
    Filter.Tendsto
      (fun N => (c 0 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) +
        ∑ q ∈ Finset.Icc 1 N,
          (c q : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) ^ q)
      Filter.atTop (nhds (cfc (fun _ : ℝ => 1)
        (1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
  dsimp only
  refine matrixFun_powerSeries
    (A := (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (I := Set.univ)
    (c := fun q => if q = 0 then 1 else 0)
    (f := fun _ => 1) Matrix.isHermitian_one ?_ ?_
  · intro i
    simp
  · intro a ha
    have hconst :
        (fun N : ℕ =>
          (if (0 : ℕ) = 0 then 1 else 0) +
            ∑ q ∈ Finset.Icc 1 N,
              (if q = 0 then 1 else 0) * a ^ q) =
          fun _ => (1 : ℝ) := by
      funext N
      simp only [ite_true]
      rw [Finset.sum_eq_zero]
      · simp
      · intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        simp [Nat.ne_of_gt hq1]
    rw [hconst]
    exact tendsto_const_nhds

theorem sampled_master_expectation_upper_inf :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hermSeries_hermitian k ω)) ∂radMu ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, (θ : ℝ)⁻¹ * Real.log
        ((NormedSpace.exp
          (∑ k, matrixCgf radMu (hermSeries k) (θ : ℝ))).trace).re := by
  exact master_expectation_upper_inf hermSeries_measurable
    hermSeries_hermitian hermSeries_norm_le_one hermSeries_indep

theorem sampled_gaussian_herm_min_tail :
    gaussMu.real {ω |
        lambdaMin (isHermitian_matsum Finset.univ
          (fun k => isHermitian_real_smul
            (Matrix.isHermitian_one : (1 : Matrix N N ℂ).IsHermitian)
            (gaussCoords k ω))) ≤ -(1 : ℝ)} ≤
      (Fintype.card N : ℝ) *
        Real.exp (-((1 : ℝ) ^ 2) /
          (2 * ‖∑ _k : ToeplitzI, (1 : Matrix N N ℂ) ^ 2‖)) := by
  exact gaussian_herm_min_tail gaussCoords_measurable gaussCoords_law
    gaussCoords_indep (fun _ => Matrix.isHermitian_one) (by positivity)

theorem sampled_varAW_eq_of_identDistrib :
    varAW radMu hermSeries =
      ‖∑ k, expectation radMu
        (fun ω => hermSeries k ω * hermSeries k ω)‖ := by
  apply varAW_eq_of_identDistrib
  intro k
  have hk : k = Classical.arbitrary I := Subsingleton.elim _ _
  subst k
  exact ProbabilityTheory.IdentDistrib.refl
    (hermSeries_measurable _).aemeasurable

theorem sampled_intdim_chernoff_expectation_ae :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        fun k => bernHerm_hermitian k ω) ∂bernMu ≤
      (Real.exp (1 : ℝ) - 1) / 1 *
          lambdaMax
            (Matrix.PosDef.one.posSemidef :
              (1 : Matrix N N ℂ).PosSemidef).1 +
        1 * Real.log (2 * intdim (1 : Matrix N N ℂ)) / 1 := by
  exact intdim_chernoff_expectation_ae bernHerm_measurable
    bernHerm_hermitian bernHerm_min_ae bernHerm_max_ae bernHerm_indep
    (by positivity) Matrix.PosDef.one.posSemidef one_ne_zero
    bernHerm_expectation_sum_le_one (θ := 1) (by positivity)

/-! ## Closed applications required by the corrected-snapshot Tier-C sample -/

theorem sampled_entrywiseL1AddGroupNorm_nonzero :
    (entrywiseL1AddGroupNorm (m := Fin 1) (n := Fin 1)).toFun
        (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 := by
  intro h
  have hzero :=
    (entrywiseL1AddGroupNorm (m := Fin 1) (n := Fin 1)).eq_zero_of_map_eq_zero' _ h
  exact one_ne_zero hzero

theorem sampled_l2_opNorm_replicateRow :
    ‖Matrix.replicateRow Unit (fun _ : Fin 1 => (1 : ℂ))‖ =
      l2norm (star (fun _ : Fin 1 => (1 : ℂ))) :=
  l2_opNorm_replicateRow (fun _ : Fin 1 => (1 : ℂ))

theorem sampled_schattenOneNorm_eq_zero_iff :
    schattenOneNorm (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 ↔
      (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 :=
  schattenOneNorm_eq_zero_iff _

theorem sampled_matrixMgf_hasSum_moments :
    HasSum (fun q : ℕ => (((1 : ℝ) ^ q / q.factorial : ℝ) : ℂ) •
      expectation radMu (fun ω => hermSeries (0 : I) ω ^ q))
      (matrixMgf radMu (hermSeries (0 : I)) 1) := by
  exact matrixMgf_hasSum_moments
    (hermSeries_measurable 0) (hermSeries_hermitian 0)
    (hermSeries_norm_le_one 0) 1

theorem sampled_master_tail_upper_inf :
    radMu.real {ω | (1 : ℝ) ≤
        lambdaMax (isHermitian_matsum Finset.univ
          (fun k => hermSeries_hermitian k ω))} ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, Real.exp (-(θ : ℝ) * 1) *
        ((NormedSpace.exp
          (∑ k, matrixCgf radMu (hermSeries k) (θ : ℝ))).trace).re := by
  exact master_tail_upper_inf hermSeries_measurable
    hermSeries_hermitian hermSeries_norm_le_one hermSeries_indep 1

theorem sampled_gauss_expect_sq_upper :
    ∫ ω, ‖∑ k, gaussCoords k ω • (1 : Matrix N N ℂ)‖ ^ 2 ∂gaussMu ≤
      2 *
        max
          ‖∑ _k : ToeplitzI,
            (1 : Matrix N N ℂ) * (1 : Matrix N N ℂ)ᴴ‖
          ‖∑ _k : ToeplitzI,
            (1 : Matrix N N ℂ)ᴴ * (1 : Matrix N N ℂ)‖ *
        (1 + Real.log ((Fintype.card N : ℝ) + Fintype.card N)) := by
  exact gauss_expect_sq_upper
    (μ := gaussMu)
    (γ := gaussCoords)
    (B := fun _ : ToeplitzI => (1 : Matrix N N ℂ))
    gaussCoords_measurable gaussCoords_law gaussCoords_indep

theorem sampled_gauss_concentration :
    gaussMu.real {ω |
      (∫ ω', ‖∑ k, gaussCoords k ω' • (1 : Matrix N N ℂ)‖ ∂gaussMu) + 1 ≤
        ‖∑ k, gaussCoords k ω • (1 : Matrix N N ℂ)‖} ≤
      Real.exp (-(1 : ℝ) ^ 2 /
        (2 * weakVariance (fun _ : ToeplitzI => (1 : Matrix N N ℂ)))) := by
  exact gauss_concentration
    (μ := gaussMu)
    (γ := gaussCoords)
    (B := fun _ : ToeplitzI => (1 : Matrix N N ℂ))
    gaussCoords_measurable gaussCoords_law gaussCoords_indep
    (t := 1) (by positivity)

theorem sampled_coupon_collector_lower_instance :
    (1 - Real.exp (-(1 : ℝ))) / 1 * (Fintype.card I : ℝ) -
        (1 : ℝ)⁻¹ * (Fintype.card N : ℝ) * Real.log (Fintype.card N) ≤
      ∫ _ω, lambdaMin
        (isHermitian_matsum Finset.univ
          (fun _k : I => (Matrix.isHermitian_one :
            (1 : Matrix N N ℂ).IsHermitian))) ∂radMu := by
  exact coupon_collector_lower_instance
    (μ := radMu)
    (X := fun (_ : I) (_ : BoolΩ) => (1 : Matrix N N ℂ))
    (fun _ => measurable_const)
    (fun _ _ => Matrix.isHermitian_one)
    (fun _ _ => by rw [lambdaMin_one]; norm_num)
    (fun _ _ => by rw [lambdaMax_one]; norm_num)
    (fun _ => by
      ext i j
      rw [expectation_apply, integral_const, probReal_univ, one_smul])
    ProbabilityTheory.iIndepFun.of_subsingleton
    (θ := 1) (by norm_num)

theorem sampled_intdim_column_submatrix_upper_totalized :
    ∫ ω, ‖columnSubmatrix (1 : Matrix N N ℂ) bernCoords ω‖ ^ 2 ∂bernMu ≤
      1.72 * ((1 / 2 : ℝ) * ‖(1 : Matrix N N ℂ)‖ ^ 2) +
        Real.log (2 * stableRank (1 : Matrix N N ℂ)) *
          Finset.univ.sup' Finset.univ_nonempty
            (colNormSq (1 : Matrix N N ℂ)) := by
  exact intdim_column_submatrix_upper_totalized
    (μ := bernMu) (q := (1 / 2 : ℝ)) (δ := bernCoords)
    (1 : Matrix N N ℂ) half_mem_Icc bernCoords_measurable
    bernCoords_law bernCoords_indep

theorem sampled_matrix_sampling_intdim_tail_ae :
    bernMu.real {_ω |
        (4 / 3 : ℝ) ≤
          ‖(↑(1 : ℕ) : ℝ)⁻¹ •
              (∑ _k : Fin 1, (1 : Matrix N N ℂ)) -
            (1 : Matrix N N ℂ)‖} ≤
      4 * intdim
          (Matrix.fromBlocks (1 : Matrix N N ℂ) 0 0
            (1 : Matrix N N ℂ)) *
        Real.exp
          (-((↑(1 : ℕ) : ℝ) * (4 / 3 : ℝ) ^ 2) / 2 /
            (max ‖(1 : Matrix N N ℂ)‖ ‖(1 : Matrix N N ℂ)‖ +
              2 * 1 * (4 / 3 : ℝ) / 3)) := by
  exact matrix_sampling_intdim_tail_ae
    (μ := bernMu) (nn := 1)
    (R := fun _ _ => (1 : Matrix N N ℂ))
    (R₀ := fun _ => (1 : Matrix N N ℂ))
    (B := (1 : Matrix N N ℂ)) (L := 1)
    (M₁ := (1 : Matrix N N ℂ)) (M₂ := (1 : Matrix N N ℂ))
    (by norm_num)
    measurable_const
    (Filter.Eventually.of_forall fun _ => by simp)
    (by simp [expectation_const])
    Matrix.PosDef.one.posSemidef
    Matrix.PosDef.one.posSemidef
    (by simp)
    (by simp [expectation_const])
    (by simp [expectation_const])
    (fun _ => measurable_const)
    (fun _ =>
      ProbabilityTheory.IdentDistrib.refl measurable_const.aemeasurable)
    ProbabilityTheory.iIndepFun.of_subsingleton
    (t := (4 / 3 : ℝ))
    (by norm_num [Real.sqrt_one])

theorem sampled_vre_convexOn :
    vre
        (fun _ : Fin 1 =>
          (1 / 2 : ℝ) * 1 + (1 - (1 / 2 : ℝ)) * 3)
        (fun _ : Fin 1 =>
          (1 / 2 : ℝ) * 2 + (1 - (1 / 2 : ℝ)) * 1) ≤
      (1 / 2 : ℝ) *
          vre (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) +
        (1 - (1 / 2 : ℝ)) *
          vre (fun _ : Fin 1 => (3 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
  exact vre_convexOn
    (a₁ := fun _ : Fin 1 => (1 : ℝ))
    (a₂ := fun _ : Fin 1 => (3 : ℝ))
    (h₁ := fun _ : Fin 1 => (2 : ℝ))
    (h₂ := fun _ : Fin 1 => (1 : ℝ))
    (τ := (1 / 2 : ℝ))
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
    (by norm_num)

theorem sampled_kronecker_mixed_product :
    let A₁ : Matrix (Fin 2) (Fin 2) ℂ :=
      Matrix.single (0 : Fin 2) (1 : Fin 2) 1
    let H₁ : Matrix (Fin 2) (Fin 2) ℂ :=
      Matrix.single (1 : Fin 2) (0 : Fin 2) 1
    let A₂ : Matrix (Fin 2) (Fin 2) ℂ :=
      Matrix.single (1 : Fin 2) (0 : Fin 2) 1
    let H₂ : Matrix (Fin 2) (Fin 2) ℂ :=
      Matrix.single (0 : Fin 2) (1 : Fin 2) 1
    Matrix.kroneckerMap (· * ·) A₁ H₁ *
        Matrix.kroneckerMap (· * ·) A₂ H₂ =
      Matrix.kroneckerMap (· * ·) (A₁ * A₂) (H₁ * H₂) := by
  dsimp only
  exact kronecker_mixed_product _ _ _ _

theorem sampled_intdim_eq_one_iff_rank_eq_one :
    intdim (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 ↔
      (1 : Matrix (Fin 1) (Fin 1) ℂ).rank = 1 :=
  intdim_eq_one_iff_rank_eq_one Matrix.PosDef.one.posSemidef one_ne_zero

theorem sampled_scalar_bernstein :
    radMu.real {ω | (1 : ℝ) ≤ |∑ k, signs k ω|} ≤
      2 * Real.exp ((-((1 : ℝ) ^ 2) / 2) /
        ((∑ k, ∫ ω, (signs k ω) ^ 2 ∂radMu) + 1 * 1 / 3)) := by
  exact scalar_bernstein (L := 1)
    signs_indep signs_measurable
    (fun k => integral_id_isRademacher (signs_measurable k) (signs_law k))
    (fun k => Filter.Eventually.of_forall fun ω => by
      by_cases h : ω k = true <;> simp [signs, boolSign, h])
    (by norm_num)

theorem sampled_master_expectation_lower_sup :
    (⨆ θ : {θ : ℝ // θ < 0}, (θ : ℝ)⁻¹ * Real.log
        ((NormedSpace.exp
          (∑ k, matrixCgf radMu (hermSeries k) (θ : ℝ))).trace).re) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hermSeries_hermitian k ω)) ∂radMu := by
  exact master_expectation_lower_sup hermSeries_measurable
    hermSeries_hermitian hermSeries_norm_le_one hermSeries_indep

theorem sampled_chernoff_expected_trace_bound_ae :
    ∫ ω, (((NormedSpace.exp
        ((1 : ℝ) • ∑ k, bernHerm k ω)).trace).re -
          (Fintype.card N : ℝ)) ∂bernMu ≤
      intdim (1 : Matrix N N ℂ) *
        Real.exp (gChernoff 1 1 * ‖(1 : Matrix N N ℂ)‖) := by
  exact chernoff_expected_trace_bound_ae
    (μ := bernMu) (X := bernHerm) (L := 1)
    (M := (1 : Matrix N N ℂ)) (θ := 1)
    bernHerm_measurable bernHerm_hermitian bernHerm_min_ae bernHerm_max_ae
    bernHerm_indep (by norm_num) (by norm_num)
    Matrix.PosDef.one.posSemidef bernHerm_expectation_sum_le_one

theorem sampled_generalized_klein :
    0 ≤ ∑ _i : Fin 1,
      ((cfc (fun _ : ℝ => (1 : ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) *
        cfc (fun _ : ℝ => (1 : ℝ))
          (1 : Matrix (Fin 1) (Fin 1) ℂ)).trace).re := by
  exact generalized_klein
    (fun _ : Fin 1 => fun _ : ℝ => (1 : ℝ))
    (fun _ : Fin 1 => fun _ : ℝ => (1 : ℝ))
    (I := Set.univ) (by simp)
    Matrix.isHermitian_one Matrix.isHermitian_one (by simp) (by simp)

/-! ## Closed applications for the corrected Chapter 4--6 sample -/

theorem sampled_maxqp_rounding_bound_one_of_isRademacher :
    ∫ ω, ‖∑ k, signs k ω •
        ((Real.sqrt (2 * Real.log
          ((Fintype.card N : ℝ) + Fintype.card N)))⁻¹ • rectCoeff k)‖ ∂radMu ≤
      1 := by
  exact maxqp_rounding_bound_one_of_isRademacher
    (μ := radMu) (B := rectCoeff)
    (by simp [rectCoeff]) (by simp [rectCoeff])
    signs_measurable signs_law signs_indep

abbrev Two : Type := Fin 2

def mixedDiagEntries (i : Two) : ℝ :=
  if i = 0 then 1 else -1

noncomputable def mixedDiagCoeff (_ : I) : Matrix Two Two ℂ :=
  Matrix.diagonal (RCLike.ofReal ∘ mixedDiagEntries)

lemma mixedDiagCoeff_hermitian (k : I) :
    (mixedDiagCoeff k).IsHermitian := by
  simpa [mixedDiagCoeff] using
    (isHermitian_diagonal_ofReal mixedDiagEntries)

theorem sampled_rademacher_herm_min_expectation_of_isRademacher :
    -Real.sqrt (2 * ‖∑ k, (mixedDiagCoeff k) ^ 2‖ *
        Real.log (Fintype.card Two)) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul
          (mixedDiagCoeff_hermitian k) (signs k ω))) ∂radMu := by
  exact rademacher_herm_min_expectation_of_isRademacher
    signs_measurable signs_law signs_indep mixedDiagCoeff_hermitian

def retainedRow (_ : N) (_ : Unit) : ℝ := 1

theorem sampled_conditional_column_bound_pointwise_of_isBernoulli :
    ∫ ω₂, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowColumnSubmatrix (1 : Matrix N N ℂ) retainedRow
          bernCoords () ω₂)) ∂bernMu ≤
      1.72 * ((1 / 2 : ℝ) *
        lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
          (rowSubmatrix (1 : Matrix N N ℂ) retainedRow ()))) +
        Real.log (Fintype.card N) * Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix (1 : Matrix N N ℂ) retainedRow ())) := by
  exact conditional_column_bound_pointwise_of_isBernoulli
    (μ₂ := bernMu) (B := (1 : Matrix N N ℂ))
    (δ := retainedRow) (ξ := bernCoords)
    half_mem_Icc bernCoords_measurable bernCoords_law bernCoords_indep ()

def positiveDiagEntries (i : Two) : ℝ :=
  if i = 0 then 1 else 2

noncomputable def positiveDiag : Matrix Two Two ℂ :=
  Matrix.diagonal (RCLike.ofReal ∘ positiveDiagEntries)

lemma positiveDiag_hermitian : positiveDiag.IsHermitian := by
  simpa [positiveDiag] using
    (isHermitian_diagonal_ofReal positiveDiagEntries)

noncomputable def positiveDiagSeries (ω : BoolΩ) : Matrix Two Two ℂ :=
  signs 0 ω • positiveDiag

lemma positiveDiagSeries_hermitian (ω : BoolΩ) :
    (positiveDiagSeries ω).IsHermitian :=
  isHermitian_real_smul positiveDiag_hermitian _

theorem sampled_variance_max_eq_of_hermitian :
    expectation radMu
        (fun ω => positiveDiagSeries ω * (positiveDiagSeries ω)ᴴ) =
      expectation radMu
        (fun ω => (positiveDiagSeries ω)ᴴ * positiveDiagSeries ω) := by
  exact variance_max_eq_of_hermitian positiveDiagSeries_hermitian

noncomputable def singletonSignSample
    (_ : Fin 1) : BoolΩ → Matrix N N ℂ :=
  hermSeries 0

theorem sampled_matrix_sampling_estimator_tail_ae :
    radMu.real {ω |
        (1 / 2 : ℝ) ≤
          ‖((↑(1 : ℕ) : ℝ)⁻¹ •
              (∑ k : Fin 1, singletonSignSample k ω)) -
            (0 : Matrix N N ℂ)‖} ≤
      ((Fintype.card N : ℝ) + Fintype.card N) *
        Real.exp
          (-((↑(1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2) / 2 /
            (secondMoment radMu (hermSeries 0) +
              2 * 1 * (1 / 2 : ℝ) / 3)) := by
  exact matrix_sampling_estimator_tail_ae
    (μ := radMu) (nn := 1)
    (R := singletonSignSample) (R₀ := hermSeries 0)
    (B := (0 : Matrix N N ℂ)) (L := 1)
    (by norm_num)
    (hermSeries_measurable 0)
    (Filter.Eventually.of_forall (hermSeries_norm_le_one 0))
    (hermSeries_centered 0)
    (fun _ => hermSeries_measurable 0)
    (fun _ => by
      simpa [singletonSignSample] using
        (ProbabilityTheory.IdentDistrib.refl
          (hermSeries_measurable 0).aemeasurable))
    ProbabilityTheory.iIndepFun.of_subsingleton
    (t := (1 / 2 : ℝ)) (by norm_num)

abbrev ScalarMatrix : Type := Matrix (Fin 1) (Fin 1) ℂ

noncomputable def schattenUnitScale : ℝ :=
  schattenOneNorm (1 : ScalarMatrix)

noncomputable def schattenUnit : ScalarMatrix :=
  (((schattenUnitScale)⁻¹ : ℝ) : ℂ) • (1 : ScalarMatrix)

lemma schattenUnitScale_pos : 0 < schattenUnitScale := by
  have hnonneg : 0 ≤ schattenUnitScale :=
    schattenOneNorm_nonneg (1 : ScalarMatrix)
  have hne : schattenUnitScale ≠ 0 := by
    intro hzero
    have hone : (1 : ScalarMatrix) = 0 := by
      apply (schattenOneNorm_eq_zero_iff (1 : ScalarMatrix)).mp
      exact hzero
    exact one_ne_zero hone
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

lemma schattenUnit_norm : schattenOneNorm schattenUnit = 1 := by
  rw [schattenUnit, schattenOneNorm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr schattenUnitScale_pos)]
  exact inv_mul_cancel₀ (ne_of_gt schattenUnitScale_pos)

theorem sampled_trace_control_of_norm_le :
    ‖((1 : ScalarMatrix) * schattenUnit).trace -
        ((0 : ScalarMatrix) * schattenUnit).trace‖ ≤ (1 : ℝ) := by
  apply trace_control_of_norm_le
  · simp
  · exact schattenUnit_norm.le

def featureSignVector (ω : BoolΩ) (i : Two) : ℝ :=
  if i = 0 then 1 else signs 0 ω

lemma featureSignVector_measurable : Measurable featureSignVector :=
  measurable_of_finite _

lemma featureSignVector_sq_le_one (ω : BoolΩ) (i : Two) :
    (featureSignVector ω i) ^ 2 ≤ (1 : ℝ) := by
  fin_cases i
  · norm_num [featureSignVector]
  · by_cases h : ω 0 = true <;>
      norm_num [featureSignVector, signs, boolSign, h]

lemma expectation_featureSignVector_outer :
    expectation radMu (featureOuter featureSignVector) =
      (1 : Matrix Two Two ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · rw [expectation_apply]
    simp [featureOuter, Matrix.vecMulVec_apply, featureSignVector]
  · rw [expectation_apply]
    simp [featureOuter, Matrix.vecMulVec_apply, featureSignVector]
    rw [integral_complex_ofReal,
      integral_id_isRademacher (signs_measurable 0) (signs_law 0)]
    norm_num
  · rw [expectation_apply]
    simp [featureOuter, Matrix.vecMulVec_apply, featureSignVector]
    rw [integral_complex_ofReal,
      integral_id_isRademacher (signs_measurable 0) (signs_law 0)]
    norm_num
  · rw [expectation_apply]
    simp [featureOuter, Matrix.vecMulVec_apply, featureSignVector]
    simp_rw [← Complex.ofReal_mul, ← pow_two]
    rw [integral_complex_ofReal,
      integral_sq_isRademacher (signs_measurable 0) (signs_law 0)]
    norm_num

noncomputable def featureSignSample
    (_ : Fin 1) : BoolΩ → Matrix Two Two ℂ :=
  featureOuter featureSignVector

theorem sampled_random_feature_relative_error :
    ∫ ω, ‖((↑(1 : ℕ) : ℝ)⁻¹ •
          (∑ k : Fin 1, featureSignSample k ω)) -
        (1 : Matrix Two Two ℂ)‖ ∂radMu ≤
      ((4 : ℝ) + (4 : ℝ) ^ 2 / 3) *
        ‖(1 : Matrix Two Two ℂ)‖ := by
  apply random_feature_relative_error
    (μ := radMu) (N := 2) (nn := 1)
    (z := featureSignVector) (b := 1)
    (G := (1 : Matrix Two Two ℂ))
    (R := featureSignSample) (ε := 4)
  · norm_num
  · norm_num
  · exact featureSignVector_measurable
  · norm_num
  · exact featureSignVector_sq_le_one
  · exact expectation_featureSignVector_outer
  · rw [l2_opNorm_one]
    norm_num
  · intro k
    simpa [featureSignSample] using
      (measurable_featureOuter featureSignVector_measurable)
  · intro k
    simpa [featureSignSample] using
      (ProbabilityTheory.IdentDistrib.refl
        (measurable_featureOuter featureSignVector_measurable).aemeasurable)
  · exact ProbabilityTheory.iIndepFun.of_subsingleton
  · norm_num
  · have hlog : Real.log (4 : ℝ) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      norm_num at h ⊢
      exact h
    norm_num [l2_opNorm_one]
    linarith

theorem suspect_normalizedLapMatrix_isolated_vertex :
    normalizedLapMatrix (SimpleGraph.emptyGraph (Fin 1)) = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [normalizedLapMatrix, lapMatrixC]

theorem suspect_normalizedLapMatrix_one_edge_nonzero :
    normalizedLapMatrix (SimpleGraph.completeGraph (Fin 2)) ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
  have hlapzero :
      (SimpleGraph.completeGraph (Fin 2)).lapMatrix ℝ 0 0 = 0 := by
    simpa [normalizedLapMatrix, lapMatrixC, Matrix.mul_apply] using hentry
  have hlapone :
      (SimpleGraph.completeGraph (Fin 2)).lapMatrix ℝ 0 0 = 1 := by
    norm_num [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
  linarith

theorem suspect_gChernoff_zero_bound :
    gChernoff 1 0 = 0 := by
  simp [gChernoff]

theorem suspect_gChernoff_positive_bound :
    gChernoff 1 1 = Real.exp 1 - 1 := by
  simp [gChernoff]

/-! ## Closed applications for the reseeded 467-endpoint sample -/

def sampleCovVector (ω : BoolΩ) (i : Two) : ℂ :=
  (featureSignVector ω i : ℂ)

def sampleCovFamily (_ : Fin 1) : BoolΩ → Two → ℂ :=
  sampleCovVector

lemma sampleCovVector_measurable : Measurable sampleCovVector :=
  measurable_of_finite _

lemma sampleCovVector_bound (ω : BoolΩ) :
    l2norm (sampleCovVector ω) ^ 2 ≤ (2 : ℝ) := by
  rw [l2norm_sq]
  by_cases h : ω 0 = true <;>
    norm_num [sampleCovVector, featureSignVector, signs, boolSign, h]

theorem sampled_sampleCov_varStat_eq :
    varStatHerm radMu
        (fun ω => ∑ k : Fin 1,
          sampleCovSummand radMu sampleCovVector 1 sampleCovFamily k ω) =
      ‖∑ k : Fin 1, expectation radMu (fun ω =>
        sampleCovSummand radMu sampleCovVector 1 sampleCovFamily k ω *
          sampleCovSummand radMu sampleCovVector 1 sampleCovFamily k ω)‖ := by
  exact sampleCov_varStat_eq
    (μ := radMu) (x := sampleCovVector) (xs := sampleCovFamily) (B := 2)
    sampleCovVector_measurable
    (fun _ => sampleCovVector_measurable)
    (Filter.Eventually.of_forall sampleCovVector_bound)
    (fun _ => Filter.Eventually.of_forall sampleCovVector_bound)
    (fun _ => ProbabilityTheory.IdentDistrib.refl
      sampleCovVector_measurable.aemeasurable)
    ProbabilityTheory.iIndepFun.of_subsingleton
    (fun _ => fun _ _ => Integrable.of_finite)

theorem sampled_matrix_laplace_tail_upper_inf :
    radMu.real {ω |
        (1 : ℝ) ≤ lambdaMax (hermSeries_hermitian (0 : I) ω)} ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, Real.exp (-(θ : ℝ) * 1) *
        ∫ ω, ((NormedSpace.exp
          ((θ : ℝ) • hermSeries (0 : I) ω)).trace).re ∂radMu := by
  exact matrix_laplace_tail_upper_inf
    (μ := radMu) (Y := hermSeries (0 : I))
    (hermSeries_measurable 0) (hermSeries_hermitian 0)
    (hermSeries_norm_le_one 0) 1

theorem sampled_matrix_laplace_expectation_lower_sup :
    (⨆ θ : {θ : ℝ // θ < 0}, (θ : ℝ)⁻¹ *
        Real.log (∫ ω, ((NormedSpace.exp
          ((θ : ℝ) • hermSeries (0 : I) ω)).trace).re ∂radMu)) ≤
      ∫ ω, lambdaMin (hermSeries_hermitian (0 : I) ω) ∂radMu := by
  exact matrix_laplace_expectation_lower_sup
    (μ := radMu) (Y := hermSeries (0 : I))
    (hermSeries_measurable 0) (hermSeries_hermitian 0)
    (hermSeries_norm_le_one 0)

abbrev RectIndex : Type := Fin 2 × Fin 1
abbrev RectGaussΩ : Type := RectIndex → ℝ

noncomputable def rectGaussMu : Measure RectGaussΩ :=
  Measure.pi fun _ : RectIndex => gaussianReal 0 1

noncomputable local instance : IsProbabilityMeasure rectGaussMu := by
  dsimp [rectGaussMu]
  infer_instance

def rectGaussCoords (p : RectIndex) (ω : RectGaussΩ) : ℝ := ω p

lemma rectGaussCoords_measurable (p : RectIndex) :
    Measurable (rectGaussCoords p) :=
  measurable_pi_apply p

lemma rectGaussCoords_law (p : RectIndex) :
    IsStdGaussian (rectGaussCoords p) rectGaussMu := by
  rw [IsStdGaussian]
  change Measure.map (fun ω : RectIndex → ℝ => ω p)
      (Measure.pi fun _ : RectIndex => gaussianReal 0 1) =
    gaussianReal 0 1
  exact (measurePreserving_eval
    (fun _ : RectIndex => gaussianReal 0 1) p).map_eq

lemma rectGaussCoords_indep :
    iIndepFun rectGaussCoords rectGaussMu := by
  change iIndepFun (fun p (ω : RectIndex → ℝ) => ω p)
    (Measure.pi fun _ : RectIndex => gaussianReal 0 1)
  simpa only [id_eq] using
    (iIndepFun_pi (X := fun _ : RectIndex => id)
      (fun _ => measurable_id.aemeasurable))

theorem sampled_gaussianRect_expected_norm :
    ∫ ω, ‖∑ p : Fin 2 × Fin 1,
        rectGaussCoords p ω • Matrix.single p.1 p.2 (1 : ℂ)‖ ∂rectGaussMu ≤
      Real.sqrt (2 * max (Fintype.card (Fin 2) : ℝ)
          (Fintype.card (Fin 1)) *
        Real.log ((Fintype.card (Fin 2) : ℝ) +
          Fintype.card (Fin 1))) := by
  exact gaussianRect_expected_norm
    (μ := rectGaussMu) (γ := rectGaussCoords)
    rectGaussCoords_measurable rectGaussCoords_law rectGaussCoords_indep

theorem sampled_erAdjacency_complete_three :
    erAdjacency
        (fun _ : WignerIndex 3 => fun _ : Unit => (1 : ℝ)) () =
      Matrix.of (fun _ _ : Fin 3 => (1 : ℂ)) - 1 := by
  rw [erAdjacency]
  simp only [one_smul]
  exact sum_wignerCoeff 3

theorem sampled_IsPosDefKernel_linear :
    IsPosDefKernel (fun a b : ℝ => a * b) := by
  rw [IsPosDefKernel]
  intro N' x
  have hmatrix :
      kernelMatrix (fun a b : ℝ => a * b) x =
        Matrix.vecMulVec (fun i => ((x i : ℝ) : ℂ))
          (star (fun i => ((x i : ℝ) : ℂ))) := by
    ext i j
    simp [kernelMatrix, Matrix.vecMulVec_apply]
  rw [hmatrix]
  exact Matrix.posSemidef_vecMulVec_self_star _

noncomputable def uncenteredSignSeries
    (k : I) (ω : BoolΩ) : Matrix N N ℂ :=
  (1 : Matrix N N ℂ) + hermSeries k ω

lemma uncenteredSignSeries_measurable (k : I) :
    Measurable (uncenteredSignSeries k) :=
  measurable_const.add (hermSeries_measurable k)

lemma uncenteredSignSeries_expectation (k : I) :
    expectation radMu (uncenteredSignSeries k) =
      (1 : Matrix N N ℂ) := by
  change expectation radMu
    (fun ω => (1 : Matrix N N ℂ) + hermSeries k ω) = _
  rw [expectation_add
    (fun _ _ => Integrable.of_finite)
    (hermSeries_mIntegrable k)]
  rw [expectation_const (μ := radMu), hermSeries_centered k, add_zero]

lemma uncenteredSignSeries_indep :
    iIndepFun uncenteredSignSeries radMu := by
  change iIndepFun
    (fun k ω => (1 : Matrix N N ℂ) + hermSeries k ω) radMu
  exact hermSeries_indep.comp
    (fun _ M => (1 : Matrix N N ℂ) + M)
    (fun _ => by fun_prop)

lemma uncenteredSignSeries_centered_norm_le_one (k : I) (ω : BoolΩ) :
    ‖uncenteredSignSeries k ω -
        expectation radMu (uncenteredSignSeries k)‖ ≤ (1 : ℝ) := by
  rw [uncenteredSignSeries_expectation, uncenteredSignSeries]
  simpa using hermSeries_norm_le_one k ω

theorem sampled_matrix_bernstein_uncentered_expectation :
    ∫ ω, ‖(∑ k, uncenteredSignSeries k ω) -
        ∑ k, expectation radMu (uncenteredSignSeries k)‖ ∂radMu ≤
      Real.sqrt (2 * max
          ‖∑ k, expectation radMu
            (fun ω => (uncenteredSignSeries k ω -
                expectation radMu (uncenteredSignSeries k)) *
              (uncenteredSignSeries k ω -
                expectation radMu (uncenteredSignSeries k))ᴴ)‖
          ‖∑ k, expectation radMu
            (fun ω => (uncenteredSignSeries k ω -
                expectation radMu (uncenteredSignSeries k))ᴴ *
              (uncenteredSignSeries k ω -
                expectation radMu (uncenteredSignSeries k)))‖ *
        Real.log (Fintype.card N + Fintype.card N)) +
      (1 : ℝ) / 3 * Real.log (Fintype.card N + Fintype.card N) := by
  exact matrix_bernstein_uncentered_expectation
    (μ := radMu) (S := uncenteredSignSeries) (L := 1)
    uncenteredSignSeries_measurable
    uncenteredSignSeries_centered_norm_le_one
    (by norm_num) uncenteredSignSeries_indep

lemma secondMoment_hermSeries_zero :
    secondMoment radMu (hermSeries 0) = 1 := by
  have hright :
      (fun ω => hermSeries 0 ω * (hermSeries 0 ω)ᴴ) =
        fun _ : BoolΩ => (1 : Matrix N N ℂ) := by
    funext ω
    by_cases h : ω 0 = true <;>
      simp [hermSeries, hermCoeff, signs, boolSign, h]
  have hleft :
      (fun ω => (hermSeries 0 ω)ᴴ * hermSeries 0 ω) =
        fun _ : BoolΩ => (1 : Matrix N N ℂ) := by
    funext ω
    by_cases h : ω 0 = true <;>
      simp [hermSeries, hermCoeff, signs, boolSign, h]
  rw [secondMoment, hright, hleft]
  rw [expectation_const (μ := radMu)]
  simp

theorem sampled_matrix_sampling_sample_cost_ae :
    ∫ ω, ‖((↑(1 : ℕ) : ℝ)⁻¹ •
          (∑ k : Fin 1, singletonSignSample k ω)) -
        (0 : Matrix N N ℂ)‖ ∂radMu ≤
      2 * (4 : ℝ) := by
  apply matrix_sampling_sample_cost_ae
    (μ := radMu) (nn := 1)
    (R := singletonSignSample) (R₀ := hermSeries 0)
    (B := (0 : Matrix N N ℂ)) (L := 1) (ε := 4)
  · norm_num
  · exact hermSeries_measurable 0
  · exact Filter.Eventually.of_forall (hermSeries_norm_le_one 0)
  · exact hermSeries_centered 0
  · intro k
    exact hermSeries_measurable 0
  · intro k
    simpa [singletonSignSample] using
      (ProbabilityTheory.IdentDistrib.refl
        (hermSeries_measurable 0).aemeasurable)
  · exact ProbabilityTheory.iIndepFun.of_subsingleton
  · norm_num
  · rw [secondMoment_hermSeries_zero]
    have hlog : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    norm_num
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

theorem sampled_min_intdim_le_intdim_fromBlocks :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 ∧
      min
          (intdim (1 : Matrix (Fin 2) (Fin 2) ℂ))
          (intdim (1 : Matrix (Fin 1) (Fin 1) ℂ)) ≤
        intdim
          (Matrix.fromBlocks
            (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  refine ⟨one_ne_zero, one_ne_zero, ?_⟩
  exact min_intdim_le_intdim_fromBlocks
    Matrix.PosDef.one.posSemidef Matrix.PosDef.one.posSemidef

theorem sampled_convexOn_psiTwo_midpoint :
    (1 : ℝ) ≠ 0 ∧
      (0 : ℝ) ≠ 1 ∧
      0 < (1 / 2 : ℝ) ∧
      psiTwo 1 ((0 + 1) / 2) ≤
        (1 / 2 : ℝ) • psiTwo 1 0 +
          (1 / 2 : ℝ) • psiTwo 1 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  have happ :=
    (convexOn_psiTwo (1 : ℝ)).2
      (show (0 : ℝ) ∈ Set.univ by simp)
      (show (1 : ℝ) ∈ Set.univ by simp)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
  simpa [smul_eq_mul] using happ

/- Negative Tier-C calibration: this theorem is kernel-clean and uses no
axioms, but has no dependency on any correspondence endpoint.  Mapping it to
`covarianceMatrix` must be rejected by the evidence checker. -/
theorem calibration_unrelated_allowed_axiom : True := True.intro

/-! ## Axiom evidence for every fresh named witness -/

private def witnessNames : Array Name := #[
  ``suspect_sampleCovariance_zero_samples,
  ``suspect_lambdaMax_fin_zero,
  ``suspect_lambdaMin_fin_zero,
  ``suspect_stableRank_zero_matrix,
  ``suspect_secondSmallestEigenvalue_fin_one,
  ``suspect_maxSummandSq_unbounded_family_collapse,
  ``suspect_lambdaMax_nonzero_model,
  ``suspect_lambdaMin_nonzero_model,
  ``suspect_stableRank_nonzero_model,
  ``suspect_secondSmallest_nonzero_model,
  ``suspect_sampleCovariance_nonzero_model,
  ``suspect_maxSummandSq_finite_nonzero_model,
  ``sampled_bernstein_variance_identity,
  ``sampled_lambdaMin_neg,
  ``sampled_stableRank_le_rank,
  ``sampled_matrix_exp_add_of_commute,
  ``sampled_scalar_cgf_sum,
  ``sampled_master_expectation_upper_inf_hypotheses,
  ``sampled_rademacher_rect_expectation,
  ``sampled_rademacher_herm_min_tail,
  ``sampled_rademacher_second_moment,
  ``sampled_toeplitz_expected_norm,
  ``sampled_column_submatrix_upper_hypotheses,
  ``sampled_intdim_chernoff_expectation_ae_hypotheses,
  ``sampled_bernstein_cgf_ae_hypotheses,
  ``sampled_varStat_summand_le_varAW,
  ``sampled_intdim_not_monotone,
  ``sampled_matrixPerspective_arg_posDef,
  ``sampled_one_le_inv_of_le_one,
  ``sampled_schattenOneAddGroupNorm_nonzero,
  ``sampled_varStat_sum,
  ``sampled_matrixFun_powerSeries_constant_one,
  ``sampled_master_expectation_upper_inf,
  ``sampled_gaussian_herm_min_tail,
  ``sampled_varAW_eq_of_identDistrib,
  ``sampled_intdim_chernoff_expectation_ae,
  ``sampled_entrywiseL1AddGroupNorm_nonzero,
  ``sampled_l2_opNorm_replicateRow,
  ``sampled_schattenOneNorm_eq_zero_iff,
  ``sampled_matrixMgf_hasSum_moments,
  ``sampled_master_tail_upper_inf,
  ``sampled_gauss_expect_sq_upper,
  ``sampled_gauss_concentration,
  ``sampled_coupon_collector_lower_instance,
  ``sampled_intdim_column_submatrix_upper_totalized,
  ``sampled_matrix_sampling_intdim_tail_ae,
  ``sampled_vre_convexOn,
  ``sampled_kronecker_mixed_product,
  ``sampled_intdim_eq_one_iff_rank_eq_one,
  ``sampled_scalar_bernstein,
  ``sampled_master_expectation_lower_sup,
  ``sampled_chernoff_expected_trace_bound_ae,
  ``sampled_generalized_klein,
  ``sampled_maxqp_rounding_bound_one_of_isRademacher,
  ``sampled_rademacher_herm_min_expectation_of_isRademacher,
  ``sampled_conditional_column_bound_pointwise_of_isBernoulli,
  ``sampled_variance_max_eq_of_hermitian,
  ``sampled_matrix_sampling_estimator_tail_ae,
  ``sampled_trace_control_of_norm_le,
  ``sampled_random_feature_relative_error,
  ``suspect_normalizedLapMatrix_isolated_vertex,
  ``suspect_normalizedLapMatrix_one_edge_nonzero,
  ``suspect_gChernoff_zero_bound,
  ``suspect_gChernoff_positive_bound,
  ``sampled_sampleCov_varStat_eq,
  ``sampled_matrix_laplace_tail_upper_inf,
  ``sampled_matrix_laplace_expectation_lower_sup,
  ``sampled_gaussianRect_expected_norm,
  ``sampled_erAdjacency_complete_three,
  ``sampled_matrix_bernstein_uncentered_expectation,
  ``sampled_matrix_sampling_sample_cost_ae,
  ``sampled_IsPosDefKernel_linear,
  ``sampled_min_intdim_le_intdim_fromBlocks,
  ``sampled_convexOn_psiTwo_midpoint
]

run_cmd do
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v6_witness_axioms.tsv" IO.FS.Mode.write
  output.putStrLn "name\taxioms"
  for name in witnessNames do
    let axs ← collectAxioms name
    let sorted := axs.toList.toArray.qsort (fun a b => a.toString < b.toString)
    output.putStrLn
      s!"{name}\t{String.intercalate "," (sorted.toList.map Name.toString)}"

end MatrixConcentration.V6Witnesses
