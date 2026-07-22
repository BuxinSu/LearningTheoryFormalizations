import Lean
import Lean.Util.FoldConsts
import MatrixConcentration
import MatrixConcentration.Verification.scripts.witnesses.V6Witnesses

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

private def resolve (env : Environment) (raw : String) : Option Name :=
  let direct := raw.toName
  if raw.startsWith "MatrixConcentration." then
    if env.contains direct then some direct else none
  else
    let package := Name.str `MatrixConcentration raw
    if env.contains package then some package
    else
      let witness := Name.str `MatrixConcentration.V6Witnesses raw
      if env.contains witness then some witness
      else if env.contains direct then some direct
      else none

private def dependencies (info : ConstantInfo) : NameSet × NameSet :=
  let typeUses := info.type.getUsedConstantsAsSet
  let valueUses :=
    match info.value? (allowOpaque := true) with
    | some value => value.getUsedConstantsAsSet
    | none => ({} : NameSet)
  (typeUses, valueUses)

private def axiomText (name : Name) : CoreM String := do
  let axs ← collectAxioms name
  let sorted := axs.toList.toArray.qsort (fun a b => a.toString < b.toString)
  return String.intercalate "," (sorted.toList.map Name.toString)

private def propBinderCount (type : Expr) : MetaM Nat :=
  forallTelescope type fun fvars _ => do
    let mut count := 0
    for fvar in fvars do
      if ← isProp (← inferType fvar) then
        count := count + 1
    return count

private def emitEvidenceRows
    (env : Environment)
    (inputPath outputPath modelPath : String)
    (isCalibration : Bool := false) :
    Lean.Elab.Command.CommandElabM Unit := do
  let input ← IO.FS.readFile inputPath
  let output ← IO.FS.Handle.mk outputPath IO.FS.Mode.write
  output.putStrLn
    "global_row\tendpoint\tendpoint_kind\tevidence_name\tevidence_kind\ttarget_in_type\ttarget_in_value\tprop_binders\taxioms\tevidence_type"
  let models ← IO.FS.Handle.mk modelPath IO.FS.Mode.write
  models.putStrLn
    "global_row\tendpoint\tmodel_name\tmodel_kind\ttarget_in_type\ttarget_in_value\tprop_binders\taxioms\tmodel_type"
  for line in (input.splitOn "\n").drop 1 do
    if line.trimAscii.isEmpty then continue
    let columns := line.splitOn "\t"
    let globalRow :=
      if isCalibration then "CALIBRATION" else columns[0]!
    let endpointRaw :=
      if isCalibration then columns[0]! else columns[3]!
    let endpointKind :=
      if isCalibration then columns[1]! else columns[4]!
    let evidenceRaw :=
      if isCalibration then columns[2]! else columns[8]!
    let modelRaw :=
      if isCalibration then "" else columns[11]!
    let some endpoint := resolve env endpointRaw
      | throwError "cannot resolve Tier-C endpoint {endpointRaw}"
    for raw in evidenceRaw.splitOn ";" do
      if raw.trimAscii.isEmpty then continue
      let some name := resolve env raw.trimAscii.copy
        | throwError "cannot resolve Tier-C evidence {raw}"
      let info ← getConstInfo name
      let deps := dependencies info
      let typeFmt ← Lean.Elab.Command.liftTermElabM do
        return (← ppExpr info.type).pretty 100000
      let propBinders ← Lean.Elab.Command.liftTermElabM do
        propBinderCount info.type
      let axiomList ← Lean.Elab.Command.liftCoreM <| axiomText name
      output.putStrLn
        s!"{globalRow}\t{endpoint}\t{endpointKind}\t{name}\t{infoKind info}\t{deps.1.contains endpoint}\t{deps.2.contains endpoint}\t{propBinders}\t{axiomList}\t{tabSafe typeFmt}"
    for raw in modelRaw.splitOn ";" do
      if raw.trimAscii.isEmpty then continue
      let some name := resolve env raw.trimAscii.copy
        | throwError "cannot resolve Tier-C model {raw}"
      let info ← getConstInfo name
      let deps := dependencies info
      let typeFmt ← Lean.Elab.Command.liftTermElabM do
        return (← ppExpr info.type).pretty 100000
      let propBinders ← Lean.Elab.Command.liftTermElabM do
        propBinderCount info.type
      let axiomList ← Lean.Elab.Command.liftCoreM <| axiomText name
      models.putStrLn
        s!"{globalRow}\t{endpoint}\t{name}\t{infoKind info}\t{deps.1.contains endpoint}\t{deps.2.contains endpoint}\t{propBinders}\t{axiomList}\t{tabSafe typeFmt}"

run_cmd do
  let env ← getEnv
  emitEvidenceRows env
    "MatrixConcentration/Verification/curation/v6_tier_c_evidence.tsv"
    "MatrixConcentration/Verification/logs/v6_tier_c_environment_evidence.tsv"
    "MatrixConcentration/Verification/logs/v6_tier_c_environment_models.tsv"
  emitEvidenceRows env
    ".audit_work/V6BadTierCEvidence.tsv"
    "MatrixConcentration/Verification/logs/v6_tier_c_negative_evidence.tsv"
    "MatrixConcentration/Verification/logs/v6_tier_c_negative_models.tsv"
    true
