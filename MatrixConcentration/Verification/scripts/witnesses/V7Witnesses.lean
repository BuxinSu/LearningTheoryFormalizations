import Lean
import MatrixConcentration

open Lean Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false
set_option maxHeartbeats 0

namespace MatrixConcentration.V7Witnesses

/-! Concrete witnesses used only where a source citation alone would not
establish an inhabited or nonzero model. -/

theorem mIntegrable_nonzero_constant :
    MIntegrable
      (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (Measure.dirac ()) ∧
    ¬ MIntegrable
      (fun _ : Nat => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      Measure.count := by
  constructor
  · exact MIntegrable.const _
  · intro h
    have hi := h 0 0
    rw [integrable_const_iff] at hi
    rcases hi with hzero | hfinite
    · norm_num at hzero
    · have hlt := hfinite.measure_univ_lt_top
      rw [Measure.count_apply_infinite Set.infinite_univ] at hlt
      exact (lt_self_iff_false ⊤).mp hlt

theorem isRademacher_identity :
    IsRademacher (fun x : ℝ => x) rademacherMeasure ∧
      ¬ IsRademacher (fun _ : Unit => (0 : ℝ)) (Measure.dirac ()) := by
  constructor
  · simpa [IsRademacher] using
      (Measure.map_id (μ := rademacherMeasure))
  · intro h
    have hs := integral_sq_isRademacher
      (μ := Measure.dirac ())
      (ϱ := fun _ : Unit => (0 : ℝ))
      measurable_const h
    norm_num at hs

theorem isStdGaussian_identity :
    IsStdGaussian (fun x : ℝ => x) (gaussianReal 0 1) ∧
      ¬ IsStdGaussian (fun _ : Unit => (0 : ℝ)) (Measure.dirac ()) := by
  constructor
  · simpa [IsStdGaussian] using
      (Measure.map_id (μ := gaussianReal 0 1))
  · intro h
    have hs := integral_sq_isStdGaussian
      (μ := Measure.dirac ())
      (γ := fun _ : Unit => (0 : ℝ))
      measurable_const h
    norm_num at hs

theorem isBernoulli_identity :
    IsBernoulli (1 / 2) (fun x : ℝ => x) (bernoulliMeasureReal (1 / 2)) ∧
      ¬ IsBernoulli (1 / 2) (fun _ : Unit => (0 : ℝ)) (Measure.dirac ()) := by
  constructor
  · simpa [IsBernoulli] using
      (Measure.map_id (μ := bernoulliMeasureReal (1 / 2)))
  · intro h
    have hs := integral_id_isBernoulli
      (μ := Measure.dirac ())
      (p := 1 / 2)
      (δ := fun _ : Unit => (0 : ℝ))
      (by norm_num) measurable_const h
    norm_num at hs

def zeroVector (_ : Unit) (_ : Fin 1) : ℂ := 0

def oneSample (_ : Fin 1) (_ : Unit) (_ : Fin 1) : ℂ := 1

theorem sampleCovSummand_nonzero_model :
    sampleCovSummand (Measure.dirac ()) zeroVector 1 oneSample 0 () =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [sampleCovSummand, covarianceMatrix, expectation, zeroVector, oneSample,
    Matrix.vecMulVec_apply]

theorem gChernoff_positive_model : 0 < gChernoff 1 1 := by
  rw [gChernoff]
  norm_num

theorem gBernstein_value_model : gBernstein 1 1 = 3 / 4 := by
  norm_num [gBernstein]

noncomputable def finiteNonzeroMatrixFamily :
    Fin 1 → Unit → Matrix Unit Unit ℂ :=
  fun _ _ => 1

theorem maxSummandSq_finite_nonzero_model :
    maxSummandSq finiteNonzeroMatrixFamily (Measure.dirac ()) = 1 := by
  simp [maxSummandSq, finiteNonzeroMatrixFamily]

def oneFeature (_ : Unit) (_ : Fin 1) : ℝ := 1

theorem featureOuter_nonzero_model :
    featureOuter oneFeature () = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [featureOuter, oneFeature, Matrix.vecMulVec_apply]

theorem secondMoment_nonzero_model :
    secondMoment (Measure.dirac ())
      (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ)) = 1 := by
  have h₁ : expectation (Measure.dirac ())
      (fun _ : Unit =>
        (1 : Matrix (Fin 1) (Fin 1) ℂ) *
          (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ) = 1 := by
    simpa using
      (expectation_const (μ := Measure.dirac ())
        (1 : Matrix (Fin 1) (Fin 1) ℂ))
  have h₂ : expectation (Measure.dirac ())
      (fun _ : Unit =>
        (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ *
          (1 : Matrix (Fin 1) (Fin 1) ℂ)) = 1 := by
    simpa using
      (expectation_const (μ := Measure.dirac ())
        (1 : Matrix (Fin 1) (Fin 1) ℂ))
  rw [secondMoment, h₁, h₂, max_self, norm_one]

noncomputable def scalarRademacherMatrix (x : ℝ) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => x

theorem expectation_scalarRademacherMatrix :
    expectation rademacherMeasure scalarRademacherMatrix = 0 := by
  ext i j
  rw [expectation_apply]
  change (∫ x : ℝ, (x : ℂ) ∂rademacherMeasure) = 0
  rw [integral_complex_ofReal, rademacherMeasure_integral_id]
  norm_num

theorem matrixVar_scalarRademacherMatrix :
    matrixVar rademacherMeasure scalarRademacherMatrix = 1 := by
  have hsq : ∫ x : ℝ, x ^ 2 ∂rademacherMeasure = 1 :=
    integral_sq_isRademacher measurable_id
      (by
        simpa [IsRademacher] using
          (Measure.map_id (μ := rademacherMeasure)))
  rw [matrixVar, expectation_scalarRademacherMatrix]
  have hsqC :
      (∫ x : ℝ, (x : ℂ) * (x : ℂ) ∂rademacherMeasure) = 1 := by
    calc
      (∫ x : ℝ, (x : ℂ) * (x : ℂ) ∂rademacherMeasure)
          = ∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) ∂rademacherMeasure := by
              congr 1
              funext x
              norm_num [pow_two]
      _ = (∫ x : ℝ, x ^ 2 ∂rademacherMeasure : ℝ) :=
        integral_complex_ofReal
      _ = 1 := by rw [hsq]; norm_num
  ext i j
  fin_cases i
  fin_cases j
  simpa [expectation_apply, scalarRademacherMatrix, Matrix.mul_apply] using hsqC

theorem variance_statistics_nonzero_models :
    matrixVar rademacherMeasure scalarRademacherMatrix = 1 ∧
      varStatHerm rademacherMeasure scalarRademacherMatrix = 1 ∧
      matrixVar1 rademacherMeasure scalarRademacherMatrix = 1 ∧
      matrixVar2 rademacherMeasure scalarRademacherMatrix = 1 ∧
      varStat rademacherMeasure scalarRademacherMatrix = 1 := by
  have hm := matrixVar_scalarRademacherMatrix
  have hherm : ∀ᵐ x ∂rademacherMeasure,
      (scalarRademacherMatrix x).IsHermitian := by
    filter_upwards [] with x
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarRademacherMatrix]
  have hm1 : matrixVar1 rademacherMeasure scalarRademacherMatrix = 1 := by
    rw [matrixVar1_eq_matrixVar hherm, hm]
  have hm2 : matrixVar2 rademacherMeasure scalarRademacherMatrix = 1 := by
    rw [matrixVar2_eq_matrixVar hherm, hm]
  refine ⟨hm, ?_, hm1, hm2, ?_⟩
  · rw [varStatHerm, hm, norm_one]
  · rw [varStat, hm1, hm2, norm_one, max_self]

noncomputable def entropyA (_ : Unit) : ℝ := Real.exp 1

def entropyH (_ : Unit) : ℝ := 1

theorem entropy_nonzero_models :
    vre entropyA entropyH = 1 ∧
      mre
        (Matrix.diagonal (RCLike.ofReal ∘ entropyA) : Matrix Unit Unit ℂ)
        (Matrix.diagonal (RCLike.ofReal ∘ entropyH) : Matrix Unit Unit ℂ) = 1 := by
  have hv : vre entropyA entropyH = 1 := by
    simp [vre, entropyA, entropyH, Real.log_exp]
  refine ⟨hv, ?_⟩
  rw [← vre_eq_mre_diagonal]
  exact hv

def edge01 : WignerIndex 2 :=
  ⟨(0, 1), by decide⟩

theorem laplCoeff_nonzero_model :
    laplCoeff edge01 (0 : Fin 2) (0 : Fin 2) = 1 := by
  norm_num [laplCoeff_apply, diffVec_apply, edge01]

theorem psiOne_positive_model : 0 < psiOne 1 1 := by
  rw [psiOne]
  norm_num

theorem psiTwo_positive_model : 0 < psiTwo 1 1 := by
  rw [psiTwo]
  norm_num
  linarith [Real.exp_one_gt_two]

end MatrixConcentration.V7Witnesses

run_cmd do
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v7_witness_axioms.tsv"
    IO.FS.Mode.write
  output.putStrLn "name\taxioms\ttype_dependencies"
  let witnessNames : Array Name := #[
    `MatrixConcentration.V7Witnesses.mIntegrable_nonzero_constant,
    `MatrixConcentration.V7Witnesses.isRademacher_identity,
    `MatrixConcentration.V7Witnesses.isStdGaussian_identity,
    `MatrixConcentration.V7Witnesses.isBernoulli_identity,
    `MatrixConcentration.V7Witnesses.sampleCovSummand_nonzero_model,
    `MatrixConcentration.V7Witnesses.gChernoff_positive_model,
    `MatrixConcentration.V7Witnesses.gBernstein_value_model,
    `MatrixConcentration.V7Witnesses.maxSummandSq_finite_nonzero_model,
    `MatrixConcentration.V7Witnesses.featureOuter_nonzero_model,
    `MatrixConcentration.V7Witnesses.secondMoment_nonzero_model,
    `MatrixConcentration.V7Witnesses.variance_statistics_nonzero_models,
    `MatrixConcentration.V7Witnesses.entropy_nonzero_models,
    `MatrixConcentration.V7Witnesses.laplCoeff_nonzero_model,
    `MatrixConcentration.V7Witnesses.psiOne_positive_model,
    `MatrixConcentration.V7Witnesses.psiTwo_positive_model
  ]
  for name in witnessNames do
    let axioms ← collectAxioms name
    let sorted := axioms.qsort (fun left right => left.toString < right.toString)
    let info ← getConstInfo name
    let dependencies := info.type.getUsedConstantsAsSet.toList.toArray.qsort
      (fun left right => left.toString < right.toString)
    output.putStrLn
      s!"{name}\t{String.intercalate "," (sorted.toList.map Name.toString)}\t{String.intercalate "," (dependencies.toList.map Name.toString)}"
