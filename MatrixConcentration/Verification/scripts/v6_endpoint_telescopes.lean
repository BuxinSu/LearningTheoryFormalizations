import Lean
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

private def binderInfoText : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instanceImplicit"

private def sortDomainClass (type : Expr) : MetaM String := do
  match ← whnf type with
  | .sort level =>
      return if level.isZero then "Prop-variable" else "Type-variable"
  | _ => return "term"

private def resolveEndpoint (env : Environment) (raw : String) : Option Name :=
  let full := Name.str `MatrixConcentration raw
  if env.contains full then
    some full
  else
    let direct := raw.toName
    if env.contains direct then some direct else none

run_cmd do
  let env ← getEnv
  let inputPath := "MatrixConcentration/Verification/logs/v6_correspondence_rows.tsv"
  let endpointPath := "MatrixConcentration/Verification/logs/v6_endpoint_telescopes.tsv"
  let binderPath := "MatrixConcentration/Verification/logs/v6_endpoint_binders.tsv"
  let summaryPath := "MatrixConcentration/Verification/logs/v6_endpoint_dump_summary.log"
  let input ← IO.FS.readFile inputPath
  let endpoints ← IO.FS.Handle.mk endpointPath IO.FS.Mode.write
  let binders ← IO.FS.Handle.mk binderPath IO.FS.Mode.write
  endpoints.putStrLn
    "global_row\tchapter\tchapter_row\treadme_name\tresolved_name\tkind\tbinder_count\taxioms\tfull_type\tresult"
  binders.putStrLn
    "global_row\tchapter\tchapter_row\treadme_name\tresolved_name\tbinder_index\tbinder_name\tbinder_info\tdomain_class\tbinder_type"
  let mut total := 0
  let mut theoremTotal := 0
  let mut definitionTotal := 0
  let mut binderTotal := 0
  let mut sortBinderTotal := 0
  let mut unresolved : Array String := #[]
  for line in (input.splitOn "\n").drop 1 do
    if line.trimAscii.isEmpty then continue
    let columns := line.splitOn "\t"
    if columns.length < 9 then
      throwError "malformed correspondence TSV row: {line}"
    let globalRow := columns[0]!
    let chapter := columns[1]!
    let chapterRow := columns[2]!
    let raw := columns[5]!
    match resolveEndpoint env raw with
    | none =>
        unresolved := unresolved.push raw
    | some name =>
        total := total + 1
        let info ← getConstInfo name
        let kind := infoKind info
        if kind == "theorem" then theoremTotal := theoremTotal + 1
        if kind == "definition" then definitionTotal := definitionTotal + 1
        let axs ← collectAxioms name
        let axiomNames := axs.toList.toArray.qsort (fun a b => a.toString < b.toString)
        let axiomText := String.intercalate "," (axiomNames.toList.map Name.toString)
        let rendered ← Lean.Elab.Command.liftTermElabM do
          let fullFmt ← ppExpr info.type
          forallTelescope info.type fun xs result => do
            let resultFmt ← ppExpr result
            let mut rows : Array (String × String × String × String) := #[]
            for x in xs do
              let decl ← getFVarLocalDecl x
              let domainClass ← sortDomainClass decl.type
              let typeFmt ← ppExpr decl.type
              rows := rows.push
                (decl.userName.toString, binderInfoText decl.binderInfo, domainClass,
                  typeFmt.pretty 100000)
            return (fullFmt.pretty 100000, resultFmt.pretty 100000, rows)
        let fullType := tabSafe rendered.1
        let resultType := tabSafe rendered.2.1
        let binderRows := rendered.2.2
        binderTotal := binderTotal + binderRows.size
        endpoints.putStrLn
          s!"{globalRow}\t{chapter}\t{chapterRow}\t{raw}\t{name}\t{kind}\t{binderRows.size}\t{axiomText}\t{fullType}\t{resultType}"
        for index in [:binderRows.size] do
          let row := binderRows[index]!
          if row.2.2.1 != "term" then sortBinderTotal := sortBinderTotal + 1
          binders.putStrLn
            s!"{globalRow}\t{chapter}\t{chapterRow}\t{raw}\t{name}\t{index + 1}\t{tabSafe row.1}\t{row.2.1}\t{row.2.2.1}\t{tabSafe row.2.2.2}"
  let summary ← IO.FS.Handle.mk summaryPath IO.FS.Mode.write
  summary.putStrLn "V6 CORRESPONDENCE ENDPOINT TELESCOPE DUMP"
  summary.putStrLn s!"INPUT_ROWS {total + unresolved.size}"
  summary.putStrLn s!"RESOLVED {total}"
  summary.putStrLn s!"UNRESOLVED {unresolved.size}"
  for name in unresolved do summary.putStrLn s!"UNRESOLVED_NAME {name}"
  summary.putStrLn s!"THEOREM_ENDPOINTS {theoremTotal}"
  summary.putStrLn s!"DEFINITION_ENDPOINTS {definitionTotal}"
  summary.putStrLn s!"BINDERS {binderTotal}"
  summary.putStrLn s!"TYPE_OR_PROP_VARIABLE_BINDERS {sortBinderTotal}"
  summary.putStrLn s!"VERDICT {if unresolved.isEmpty && total == 467 then "PASS" else "FAIL"}"
  if !unresolved.isEmpty || total != 467 then
    throwError
      "endpoint telescope coverage failed: resolved={total}, unresolved={unresolved.size}"
