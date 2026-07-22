import Lean
import HighDimensionalProbability.Verification.scripts.witnesses.V6TierCCh8_9

/-! Current-tree declaration-exact axiom harness for V6 Chapters 8--9. -/

set_option autoImplicit false

open Lean

private def witnessNames : List Name :=
  [ ``HDP.Verification.V6TierC.queue_ch8_weightedBasis_actualWidth_dimension_two
  , ``HDP.Verification.V6TierC.queue_ch8_gamma2_finiteness_downstream
  , ``HDP.Verification.V6TierC.queue_ch8_dimensionFreeMonteCarlo_two_sample_model
  , ``HDP.Verification.V6TierC.queue_ch8_empiricalRisk_minimizer_downstream
  , ``HDP.Verification.V6TierC.queue_ch8_pajor_zero_vc_downstream
  , ``HDP.Verification.V6TierC.queue_ch9_subGaussianIncrements_matrixDeviation_downstream
  , ``HDP.Verification.V6TierC.queue_ch9_sublinear_lipschitz_subgaussian_downstream
  , ``HDP.Verification.V6TierC.queue_ch9_gaussianComplexity_projectionDiameter_downstream
  , ``HDP.Verification.V6TierC.queue_ch9_approximatelySparseWidth_remark_downstream
  , ``HDP.Verification.V6TierC.queue_ch9_subGaussianIncrements_quadraticDeviation_downstream
  , ``HDP.Verification.V6TierC.seeded_final_ch8_corollary_8_5_8_geometric
  , ``HDP.Verification.V6TierC.seeded_final_ch8_example_8_3_5_euclidean_halfspaces
  , ``HDP.Verification.V6TierC.seeded_final_ch8_discreteDudleyInequality_coveringNumber
  , ``HDP.Verification.V6TierC.seeded_final_ch8_majorizingMeasureLowerPrinciple_external
  , ``HDP.Verification.V6TierC.seeded_final_ch8_theorem_8_3_17_glivenko_cantelli_real
  , ``HDP.Verification.V6TierC.seeded_final_ch9_theorem_9_4_8_sparseRecovery
  , ``HDP.Verification.V6TierC.seeded_final_ch9_remark_9_4_6_convexRelaxation
  , ``HDP.Verification.V6TierC.seeded_final_ch9_ae_finrank_kernel_eq_sub
  , ``HDP.Verification.V6TierC.seeded_final_ch9_theorem_9_1_1_matrixDeviation_envelope
  , ``HDP.Verification.V6TierC.seeded_final_ch9_functionalDeviationProcess_setSupport_eq
  ]

run_cmd do
  for name in witnessNames do
    let axioms ← collectAxioms name
    IO.println <| String.intercalate "\t"
      [ "V6_TIER_C_AXIOM"
      , toString name
      , String.intercalate ";" (axioms.toList.map toString)
      ]
