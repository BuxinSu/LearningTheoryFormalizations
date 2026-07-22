import Lean
import HighDimensionalProbability.Verification.scripts.witnesses.V6TierCCh0_4

/-!
# Axiom audit for the V6 Tier-C Chapter 0--4 witnesses

This harness checks every declaration introduced as a witness.  Its accepted
kernel dependencies are exactly `propext`, `Classical.choice`, and
`Quot.sound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean

private def witnessNames : List Name :=
  [ ``HDP.Verification.V6TierC.queue_ch0_polytope_volume_remark_constant_two
  , ``HDP.Verification.V6TierC.queue_ch0_polytope_cover_downstream
  , ``HDP.Verification.V6TierC.queue_ch0_polytope_equation_downstream
  , ``HDP.Verification.V6TierC.queue_ch0_polytope_volume_fin1_two_vertices
  , ``HDP.Verification.V6TierC.queue_ch0_approximate_caratheodory_downstream
  , ``HDP.Verification.V6TierC.queue_ch1_example_1_4_2_calc_downstream
  , ``HDP.Verification.V6TierC.queue_ch1_union_bound_downstream
  , ``HDP.Verification.V6TierC.queue_ch1_bookCDF_downstream
  , ``HDP.Verification.V6TierC.queue_ch1_stirling_downstream
  , ``HDP.Verification.V6TierC.queue_ch1_robbins_stirling_n_two
  , ``HDP.Verification.V6TierC.queue_ch2_psi2_zero_downstream
  , ``HDP.Verification.V6TierC.queue_ch2_median_of_means_downstream
  , ``HDP.Verification.V6TierC.queue_ch2_pythagorean_downstream
  , ``HDP.Verification.V6TierC.queue_ch2_tail_bound_downstream
  , ``HDP.Verification.V6TierC.queue_ch2_psi2_sum_downstream
  , ``HDP.Verification.V6TierC.queue_ch3_gaussian_direction_downstream
  , ``HDP.Verification.V6TierC.queue_ch3_cut_size_downstream
  , ``HDP.Verification.V6TierC.queue_ch3_pca_kth_downstream
  , ``HDP.Verification.V6TierC.queue_ch3_relaxation_downstream
  , ``HDP.Verification.V6TierC.queue_ch3_isotropic_entropy_fin2_model
  , ``HDP.Verification.V6TierC.queue_ch3_isotropic_finite_support_fin2_model
  , ``HDP.Verification.V6TierC.queue_ch4_covariance_tail_gaussian_mixture_fin1
  , ``HDP.Verification.V6TierC.queue_ch4_orthogonal_invariance_fin1_nonzero
  , ``HDP.Verification.V6TierC.queue_ch4_gram_tail_downstream
  , ``HDP.Verification.V6TierC.queue_ch4_rayleigh_fin1_identity
  , ``HDP.Verification.V6TierC.queue_ch4_operator_norm_tail_downstream
  , ``HDP.Verification.V6TierC.tierA_prelude_matrixSingularValue_fin1_index_one
  , ``HDP.Verification.V6TierC.seeded_final_app_polytope_optimizer_unique
  , ``HDP.Verification.V6TierC.seeded_current_ch0_polytope_optimizer_equation
  , ``HDP.Verification.V6TierC.seeded_app_convexHull_eq_union_two_point
  , ``HDP.Verification.V6TierC.seeded_final_app_integral_norm_sub_mean_sq
  , ``HDP.Verification.V6TierC.seeded_final_ch1_indicator_biUnion_le_sum
  , ``HDP.Verification.V6TierC.seeded_final_ch1_exercise_1_11a_eLpNorm
  , ``HDP.Verification.V6TierC.seeded_final_ch1_holder_rv
  , ``HDP.Verification.V6TierC.seeded_final_ch1_log_gamma_stirling
  , ``HDP.Verification.V6TierC.seeded_final_ch1_convex_iff_segment
  , ``HDP.Verification.V6TierC.seeded_final_ch2_gaussian_mgf
  , ``HDP.Verification.V6TierC.seeded_final_ch2_expectation_linear
  , ``HDP.Verification.V6TierC.seeded_final_ch2_remark_2_2_4
  , ``HDP.Verification.V6TierC.seeded_final_ch2_median_one_coordinate_robust
  , ``HDP.Verification.V6TierC.seeded_final_ch2_centering_L2
  , ``HDP.Verification.V6TierC.seeded_final_ch3_sphere_isIsotropic
  , ``HDP.Verification.V6TierC.seeded_final_ch3_secondMoment_inner_sq
  , ``HDP.Verification.V6TierC.seeded_final_ch3_thinShellVariance_subGaussian
  , ``HDP.Verification.V6TierC.seeded_ch3_tensor_power_fin2_two
  , ``HDP.Verification.V6TierC.seeded_final_ch3_quadraticObjective_eq_bilinear
  , ``HDP.Verification.V6TierC.seeded_final_ch4_theorem_4_6_1_singular
  , ``HDP.Verification.V6TierC.seeded_final_ch4_courantFischer
  , ``HDP.Verification.V6TierC.seeded_final_ch4_definition_4_5_1_expectedAdjacency
  , ``HDP.Verification.V6TierC.seeded_final_ch4_remark_4_7_2
  , ``HDP.Verification.V6TierC.seeded_final_ch4_exercise_4_50c_fin1
  ]

private def allowedAxiom (name : Name) : Bool :=
  name == ``propext ||
    name == ``Classical.choice ||
    name == ``Quot.sound

private def boolText (value : Bool) : String :=
  if value then "true" else "false"

private def renderNames (names : List Name) : String :=
  String.intercalate ";"
    ((names.map toString).mergeSort
      (fun left right => compare left right == .lt))

run_cmd do
  let handle ← IO.FS.Handle.mk
    "HighDimensionalProbability/Verification/logs/recert_v6_tier_c_ch0_4_axioms.tsv"
    IO.FS.Mode.write
  handle.putStrLn "witness\taxioms\tunexpected\thas_sorryAx"
  for witness in witnessNames do
    let axioms ← collectAxioms witness
    let names := axioms.toList
    let unexpected := names.filter fun name => !allowedAxiom name
    let hasSorry := axioms.contains ``sorryAx
    handle.putStrLn <| String.intercalate "\t"
      [ toString witness
      , renderNames names
      , renderNames unexpected
      , boolText hasSorry
      ]
    unless unexpected.isEmpty do
      throwError
        "unexpected axioms in {witness}: {renderNames unexpected}"
    if hasSorry then
      throwError "sorryAx reached witness {witness}"
  handle.flush
