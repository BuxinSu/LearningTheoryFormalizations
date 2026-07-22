import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalQuotientCoordinate
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalFiberSmoothCore
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalTwoLogSobolev

/-!
# Ambient logarithmic-Sobolev inequality on special orthogonal groups

The `SO(2)` inequality starts the recursion.  In each higher dimension, the
all-coordinate quotient estimate supplies horizontal energy, while restriction
to a smooth coordinate-stabilizer fiber and the exact fiber-gradient identity
supply vertical energy.  Averaging the splittings closes the dimension-free
numerator at `256`.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

local instance matrixFirstCountableTopologyAmbientLSI (n : ℕ) :
    FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))

local instance matrixSecondCountableTopologyAmbientLSI (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

local instance specialOrthogonalFirstCountableTopologyAmbientLSI (n : ℕ) :
    FirstCountableTopology
      (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  TopologicalSpace.firstCountableTopology_induced
    (Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ) Subtype.val

local instance specialOrthogonalSecondCountableTopologyAmbientLSI (n : ℕ) :
    SecondCountableTopology
      (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  TopologicalSpace.secondCountableTopology_induced
    (Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ) Subtype.val

private lemma integral_coordinateStabilizer_right_mul_eq
    (n : ℕ) (i : Fin (n + 1))
    (e : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (he : Continuous e) :
    (∫ U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
        ∫ V : Matrix.specialOrthogonalGroup (Fin n) ℝ,
          e (U * coordinateStabilizerHom i V)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure n
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) =
      ∫ U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
        e U ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1) := by
  let G := Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ
  let K := Matrix.specialOrthogonalGroup (Fin n) ℝ
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)
  let ν := HDP.Chapter5.specialOrthogonalHaarMeasure n
  let F : G × K → ℝ :=
    fun p => e (p.1 * coordinateStabilizerHom i p.2)
  have hF : Continuous F := by
    exact he.comp
      (continuous_fst.mul
        ((continuous_coordinateStabilizerHom i).comp continuous_snd))
  have hFint : Integrable F (μ.prod ν) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hF.continuousOn.integrableOn_compact
        (μ := μ.prod ν) isCompact_univ
  have hright (V : K) :
      (∫ U : G, e (U * coordinateStabilizerHom i V) ∂μ) =
        ∫ U : G, e U ∂μ := by
    calc
      (∫ U : G, e (U * coordinateStabilizerHom i V) ∂μ) =
          ∫ W : G, e W
            ∂Measure.map
              (fun U : G => U * coordinateStabilizerHom i V) μ := by
        symm
        exact integral_map (by fun_prop) he.aestronglyMeasurable
      _ = ∫ U : G, e U ∂μ := by
        rw [HDP.Appendix.probabilityHaar_map_mul_right_eq_self
          μ (coordinateStabilizerHom i V)]
  change (∫ U, ∫ V, F (U, V) ∂ν ∂μ) = ∫ U, e U ∂μ
  rw [integral_integral_swap hFint]
  change (∫ V, ∫ U, e (U * coordinateStabilizerHom i V) ∂μ ∂ν) =
    ∫ U, e U ∂μ
  rw [show
      (fun V : K =>
        ∫ U : G, e (U * coordinateStabilizerHom i V) ∂μ) =
        fun _ : K => ∫ U : G, e U ∂μ by
    funext V
    exact hright V]
  rw [integral_const]
  simp [ν, G, μ]

theorem specialOrthogonal_ambient_logSobolev
    (n : ℕ) (hn : 2 ≤ n)
    (H : FrobeniusEuclidean n → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H)) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        (fun U => H (HDP.gaussianMatrixVectorize U.1) ^ 2) ≤
      2 * (256 / (n : ℝ)) *
        ∫ U : Matrix.specialOrthogonalGroup (Fin n) ℝ,
          HDP.matrixFrobeniusNorm (tangentGradient H U) ^ 2
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn2 : n = 2
      · subst n
        exact specialOrthogonal_two_logSobolev H hHdiff hHderiv
      · have hn3 : 3 ≤ n := by omega
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := by
          exact ⟨n - 3, by omega⟩
        let G :=
          Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ
        let μ :=
          HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
        let g : G → ℝ :=
          fun U => H (HDP.gaussianMatrixVectorize U.1)
        let X : G → Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
          tangentGradient H
        have hg : Continuous g :=
          hHdiff.continuous.comp
            (continuous_gaussianMatrixVectorize.comp
              continuous_subtype_val)
        have hX : Continuous X :=
          continuous_tangentGradient hHderiv
        have hQuotient :
            ∀ i : Fin (k + 3),
              boltzmannEntropy μ
                  (rightAverage (coordinateStabilizerMeasure i)
                    (fun U => g U ^ 2)) ≤
                2 * (6 / (((k + 3 : ℕ) : ℝ))) *
                  ∫ U, tangentFieldHorizontalEnergy X i U ∂μ := by
          intro i
          simpa [G, μ, g, X, tangentFieldHorizontalEnergy] using
            coordinate_quotient_entropy_le_ambient_six
              k H hHdiff hHderiv i
        have hFiber :
            ∀ i : Fin (k + 3),
              (∫ U,
                  boltzmannEntropy (coordinateStabilizerMeasure i)
                    (fun V => g (U * V) ^ 2) ∂μ) ≤
                2 * (256 / (((k + 2 : ℕ) : ℝ))) *
                  ∫ U, tangentFieldVerticalEnergy X i U ∂μ := by
          intro i
          let c : ℝ := 2 * (256 / (((k + 2 : ℕ) : ℝ)))
          let e : G → ℝ :=
            fun W => verticalSquareEnergy (tangentGradient H W) i
          let A : G → ℝ :=
            fun U =>
              ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
                e (U * coordinateStabilizerHom i V)
                ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
          have he : Continuous e :=
            continuous_tangentFieldVerticalEnergy hX i
          have hA : Continuous A := by
            have hjoint :
                Continuous
                  (Function.uncurry
                    (fun U : G =>
                      fun V :
                          Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
                        e (U * coordinateStabilizerHom i V))) := by
              exact he.comp
                (continuous_fst.mul
                  ((continuous_coordinateStabilizerHom i).comp
                    continuous_snd))
            simpa only [A, Measure.restrict_univ] using
              continuous_parametric_integral_of_continuous
                (μ :=
                  HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2))
                hjoint (s := Set.univ) isCompact_univ
          have hEntropyContinuous :
              Continuous
                (fun U : G =>
                  boltzmannEntropy (coordinateStabilizerMeasure i)
                    (fun V => g (U * V) ^ 2)) :=
            continuous_fiberBoltzmannEntropy_coordinateStabilizer
              i g hg
          have hpoint :
              ∀ U : G,
                boltzmannEntropy (coordinateStabilizerMeasure i)
                    (fun V => g (U * V) ^ 2) ≤
                  c * A U := by
            intro U
            let K : FrobeniusEuclidean (k + 2) → ℝ :=
              fiberAmbientFunction i U.1 H
            have hKdiff : Differentiable ℝ K :=
              differentiable_fiberAmbientFunction i U.1 H hHdiff
            have hKderiv : Continuous (fderiv ℝ K) :=
              continuous_fderiv_fiberAmbientFunction
                i U.1 H hHdiff hHderiv
            have hlow :=
              ih (k + 2) (by omega) (by omega)
                K hKdiff hKderiv
            rw [boltzmannEntropy_coordinateStabilizer_sq_mul
              i U g hg]
            simpa [c, A, e, g, K, fiberAmbientFunction,
              Function.comp_def, tangentFieldVerticalEnergy] using
              (show
                boltzmannEntropy
                    (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2))
                    (fun V =>
                      K (HDP.gaussianMatrixVectorize V.1) ^ 2) ≤
                  c *
                    ∫ V :
                        Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
                      e (U * coordinateStabilizerHom i V)
                      ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) by
                calc
                  _ ≤
                      2 * (256 / (((k + 2 : ℕ) : ℝ))) *
                        ∫ V :
                            Matrix.specialOrthogonalGroup
                              (Fin (k + 2)) ℝ,
                          HDP.matrixFrobeniusNorm
                            (tangentGradient K V) ^ 2
                          ∂HDP.Chapter5.specialOrthogonalHaarMeasure
                            (k + 2) :=
                    hlow
                  _ =
                      c *
                        ∫ V :
                            Matrix.specialOrthogonalGroup
                              (Fin (k + 2)) ℝ,
                          e (U * coordinateStabilizerHom i V)
                          ∂HDP.Chapter5.specialOrthogonalHaarMeasure
                            (k + 2) := by
                    congr 1
                    apply integral_congr_ae
                    filter_upwards []
                    intro V
                    exact tangentGradient_fiberAmbientFunction_energy
                      i U V H hHdiff)
          have hmono :
              (∫ U,
                  boltzmannEntropy (coordinateStabilizerMeasure i)
                    (fun V => g (U * V) ^ 2) ∂μ) ≤
                ∫ U, c * A U ∂μ := by
            exact integral_mono
              (by
                simpa only [IntegrableOn, Measure.restrict_univ] using
                  hEntropyContinuous.continuousOn.integrableOn_compact
                    (μ := μ) isCompact_univ)
              ((by
                simpa only [IntegrableOn, Measure.restrict_univ] using
                  hA.continuousOn.integrableOn_compact
                    (μ := μ) isCompact_univ : Integrable A μ).const_mul c)
              hpoint
          calc
            (∫ U,
                boltzmannEntropy (coordinateStabilizerMeasure i)
                  (fun V => g (U * V) ^ 2) ∂μ) ≤
                ∫ U, c * A U ∂μ := hmono
            _ = c * ∫ U, A U ∂μ := integral_const_mul c A
            _ = c * ∫ U, e U ∂μ := by
              rw [integral_coordinateStabilizer_right_mul_eq
                (k + 2) i e he]
            _ =
                2 * (256 / (((k + 2 : ℕ) : ℝ))) *
                  ∫ U, tangentFieldVerticalEnergy X i U ∂μ := by
              rfl
        have hstep :=
          specialOrthogonal_logSobolev_induction_step
            (k + 2) (by omega) g hg X hX
            (a := 256) (b := 6) (by norm_num) (by norm_num)
            hQuotient hFiber
        simpa [G, μ, g, X, tangentFieldSquareEnergy,
          Nat.add_assoc] using hstep

end

end HDP.Appendix.SpecialOrthogonal
