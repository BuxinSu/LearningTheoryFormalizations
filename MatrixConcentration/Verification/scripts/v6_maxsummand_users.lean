import Lean
import Lean.Util.FoldConsts
import MatrixConcentration

open Lean Meta

set_option autoImplicit false
set_option maxHeartbeats 0

private def tabSafe (text : String) : String :=
  text.replace "\t" " " |>.replace "\r" " " |>.replace "\n" " "

private def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def isGeneratedDefinitionHelper (name : Name) : Bool :=
  name == `MatrixConcentration.maxSummandSq.eq_1 ||
    name == `MatrixConcentration.maxSummandSq.congr_simp

private def isGuardedPredicateDefinition (name : Name) : Bool :=
  name == `MatrixConcentration.ProvidesCenteredRosenthalBootstrap

run_cmd do
  let env ← getEnv
  let target := `MatrixConcentration.maxSummandSq
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v6_maxsummand_users.tsv"
    IO.FS.Mode.write
  output.putStrLn
    "compiled_name\tuser_name\tkind\tclassification\thas_Fintype_in_type\tin_type\tin_value\tfull_type"
  let constants := env.constants.toList.toArray.qsort
    (fun a b => a.1.toString < b.1.toString)
  let mut directUsers := 0
  let mut handwritten := 0
  let mut handwrittenFinite := 0
  let mut guardedPredicates := 0
  let mut generated := 0
  for (name, info) in constants do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.getRoot != `MatrixConcentration then continue
      let typeUses := info.type.getUsedConstantsAsSet
      let valueUses :=
        match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstantsAsSet
        | none => ({} : NameSet)
      let inType := typeUses.contains target
      let inValue := valueUses.contains target
      if !inType && !inValue then continue
      directUsers := directUsers + 1
      let generatedHelper := isGeneratedDefinitionHelper name
      let guardedPredicate := isGuardedPredicateDefinition name
      let classification :=
        if generatedHelper then "generated-definition-helper"
        else if guardedPredicate then "handwritten-Fintype-guarded-predicate"
        else "handwritten-downstream-user"
      if generatedHelper then
        generated := generated + 1
      else if guardedPredicate then
        guardedPredicates := guardedPredicates + 1
      else
        handwritten := handwritten + 1
      let fullType ← Lean.Elab.Command.liftTermElabM do
        return (← ppExpr info.type).pretty 100000
      let hasFintype := fullType.contains "Fintype"
      if !generatedHelper && !guardedPredicate && hasFintype then
        handwrittenFinite := handwrittenFinite + 1
      let userName := (privateToUserName? name).getD name
      output.putStrLn
        s!"{name}\t{userName}\t{infoKind info}\t{classification}\t{hasFintype}\t{inType}\t{inValue}\t{tabSafe fullType}"
  let summary ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v6_maxsummand_users.log"
    IO.FS.Mode.write
  summary.putStrLn "V6 maxSummandSq DIRECT-USER CONTAINMENT AUDIT"
  summary.putStrLn s!"DIRECT_COMPILED_USERS {directUsers}"
  summary.putStrLn s!"HANDWRITTEN_DOWNSTREAM_USERS {handwritten}"
  summary.putStrLn s!"HANDWRITTEN_WITH_FINTYPE_IN_TELESCOPE {handwrittenFinite}"
  summary.putStrLn s!"HANDWRITTEN_FINTYPE_GUARDED_PREDICATES {guardedPredicates}"
  summary.putStrLn s!"GENERATED_DEFINITION_HELPERS {generated}"
  let pass := directUsers == 27 && handwritten == handwrittenFinite &&
    handwritten == 24 && guardedPredicates == 1 && generated == 2
  summary.putStrLn s!"VERDICT {if pass then "PASS" else "FAIL"}"
  if !pass then
    throwError
      "maxSummandSq containment drift: direct={directUsers}, handwritten={handwritten}, finite={handwrittenFinite}, guarded={guardedPredicates}, generated={generated}"
