import Lean
import HighDimensionalProbability.Verification.scripts.witnesses.V6TierCCh5_7

/-! Current-tree declaration-exact axiom harness for V6 Chapters 5--7. -/

set_option autoImplicit false

open Lean

private def witnessNames : List Name :=
  [ ``HDP.Verification.V6TierC.queue_ch5_grassmannian_fin2_line
  , ``HDP.Verification.V6TierC.queue_ch5_matrixNorm_loewner_diagonal_fin2
  , ``HDP.Verification.V6TierC.queue_ch7_gaussianInterpolation_fin1_half
  , ``HDP.Verification.V6TierC.queue_ch7_crossPolytope_dimension_two
  , ``HDP.Verification.V6TierC.queue_ch7_multivariateGaussianIBP_fin1
  , ``HDP.Verification.V6TierC.tierA_ch6_exercise625_two_branches_nonvacuous
  , ``HDP.Verification.V6TierC.tierA_ch7_logPartition_positiveBeta_fin2
  , ``HDP.Verification.V6TierC.seeded_final_ch5_euclidean_isoperimetric
  , ``HDP.Verification.V6TierC.seeded_final_ch5_sparseSBM_expectedNoise_degree
  , ``HDP.Verification.V6TierC.seeded_final_ch5_orthogonalHaarMeasure_left_invariant
  , ``HDP.Verification.V6TierC.seeded_final_ch5_sphere_lipschitz_tail
  , ``HDP.Verification.V6TierC.seeded_final_ch6_hansonWright
  , ``HDP.Verification.V6TierC.seeded_final_ch6_quadraticForm_eq_doubleSum
  , ``HDP.Verification.V6TierC.seeded_final_ch6_sampledMatrix_apply
  , ``HDP.Verification.V6TierC.seeded_final_ch6_centeredSampling_expectedOperatorNorm_le
  , ``HDP.Verification.V6TierC.seeded_final_ch6_integral_decoupledPartialChaos_le_bilinear
  , ``HDP.Verification.V6TierC.seeded_final_ch7_gaussianInterpolation_of_boundedDerivative
  , ``HDP.Verification.V6TierC.seeded_final_ch7_finiteGaussianProcess_identDistrib
  , ``HDP.Verification.V6TierC.seeded_final_ch7_extendedExpectation_eq_integral
  , ``HDP.Verification.V6TierC.seeded_final_ch7_extendedExpectedSupremum_noncompact
  , ``HDP.Verification.V6TierC.seeded_final_ch7_slepianInequality
  , ``HDP.Verification.V6TierC.seeded_final_ch7_brownianReflectionPrinciple_external
  ]

run_cmd do
  for name in witnessNames do
    let axioms ← collectAxioms name
    IO.println <| String.intercalate "\t"
      [ "V6_TIER_C_AXIOM"
      , toString name
      , String.intercalate ";" (axioms.toList.map toString)
      ]
