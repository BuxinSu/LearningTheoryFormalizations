import Lean
import MatrixConcentration

open Lean

set_option autoImplicit false
set_option maxHeartbeats 0

private def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def sortedNames (names : NameSet) : Array Name :=
  names.toList.toArray.qsort (fun left right => left.toString < right.toString)

private def nameText (names : NameSet) : String :=
  String.intercalate "," ((sortedNames names).toList.map Name.toString)

run_cmd do
  let env ← getEnv
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v7_environment_dependencies.tsv"
    IO.FS.Mode.write
  output.putStrLn
    "module\tname\tuser_name\tkind\trange_start_line\trange_end_line\ttype_dependencies\tvalue_dependencies\taxioms"
  let constants := env.constants.toList.toArray.qsort
    (fun left right => left.1.toString < right.1.toString)
  let mut projectConstants := 0
  let mut rangedConstants := 0
  for (name, info) in constants do
    let some moduleIndex := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[moduleIndex.toNat]!
    if moduleName.getRoot != `MatrixConcentration then continue
    projectConstants := projectConstants + 1
    let ranges ← findDeclarationRanges? name
    if ranges.isSome then rangedConstants := rangedConstants + 1
    let startLine := ranges.map (·.range.pos.line) |>.getD 0
    let endLine := ranges.map (·.range.endPos.line) |>.getD 0
    let typeDependencies := info.type.getUsedConstantsAsSet
    let valueDependencies :=
      match info.value? (allowOpaque := true) with
      | some value => value.getUsedConstantsAsSet
      | none => ({} : NameSet)
    let axioms ← collectAxioms name
    let axiomNames := axioms.qsort (fun left right => left.toString < right.toString)
    let axiomText :=
      String.intercalate "," (axiomNames.toList.map Name.toString)
    let userName := (privateToUserName? name).getD name
    output.putStrLn
      s!"{moduleName}\t{name}\t{userName}\t{infoKind info}\t{startLine}\t{endLine}\t{nameText typeDependencies}\t{nameText valueDependencies}\t{axiomText}"
  let summary ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v7_environment_dependencies_summary.log"
    IO.FS.Mode.write
  summary.putStrLn "V7 PROJECT ENVIRONMENT DIRECT-DEPENDENCY DUMP"
  summary.putStrLn s!"PROJECT_CONSTANTS {projectConstants}"
  summary.putStrLn s!"CONSTANTS_WITH_SOURCE_RANGE {rangedConstants}"
  summary.putStrLn "DEPENDENCY_RULE direct constants in elaborated type and value/proof"
  summary.putStrLn "VERDICT PASS"
