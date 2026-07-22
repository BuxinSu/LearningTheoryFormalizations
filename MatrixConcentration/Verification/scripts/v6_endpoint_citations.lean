import Lean
import Lean.Util.FoldConsts
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

run_cmd do
  let env ← getEnv
  let input ← IO.FS.readFile
    "MatrixConcentration/Verification/logs/v6_correspondence_rows.tsv"
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v6_endpoint_citations.tsv" IO.FS.Mode.write
  output.putStrLn
    "endpoint_global_row\tendpoint\tciting_name\tciting_user_name\tciting_kind\tin_type\tin_value"
  let mut targets : NameMap String := {}
  for line in (input.splitOn "\n").drop 1 do
    if line.trimAscii.isEmpty then continue
    let columns := line.splitOn "\t"
    if columns.length < 9 then throwError "malformed correspondence row: {line}"
    let endpoint := Name.str `MatrixConcentration columns[5]!
    targets := targets.insert endpoint columns[0]!
  let constants := env.constants.toList.toArray.qsort
    (fun a b => a.1.toString < b.1.toString)
  let mut citationRows := 0
  let mut proofCitationRows := 0
  for (citingName, info) in constants do
    if let some idx := env.getModuleIdxFor? citingName then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.getRoot != `MatrixConcentration then continue
      let typeUses := info.type.getUsedConstantsAsSet
      let valueUses :=
        match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstantsAsSet
        | none => ({} : NameSet)
      let uses := typeUses ++ valueUses
      for endpoint in uses do
        if endpoint == citingName then continue
        if let some globalRow := targets.find? endpoint then
          let inType := typeUses.contains endpoint
          let inValue := valueUses.contains endpoint
          let userName := (privateToUserName? citingName).getD citingName
          output.putStrLn
            s!"{globalRow}\t{endpoint}\t{citingName}\t{userName}\t{infoKind info}\t{inType}\t{inValue}"
          citationRows := citationRows + 1
          if inValue then proofCitationRows := proofCitationRows + 1
  let summary ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v6_endpoint_citations_summary.log"
    IO.FS.Mode.write
  summary.putStrLn "V6 DIRECT ENDPOINT CITATION DUMP"
  summary.putStrLn s!"ENDPOINTS {targets.toList.length}"
  summary.putStrLn s!"CITATION_ROWS {citationRows}"
  summary.putStrLn s!"VALUE_OR_PROOF_CITATION_ROWS {proofCitationRows}"
  summary.putStrLn s!"VERDICT {if targets.toList.length == 467 then "PASS" else "FAIL"}"
