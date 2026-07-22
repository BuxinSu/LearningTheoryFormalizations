import Lean
import MatrixConcentration

open Lean

set_option autoImplicit false
set_option maxHeartbeats 0

private def auditKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def tabSafe (text : String) : String :=
  text.replace "\t" " " |>.replace "\n" " "

run_cmd do
  let env ← getEnv
  let audit ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/axiom_audit.tsv" IO.FS.Mode.write
  let modules ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/axiom_modules.txt" IO.FS.Mode.write
  let decls ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/declaration_types.tsv" IO.FS.Mode.write
  audit.putStrLn "module\tname\tuser_name\tkind\taxioms"
  decls.putStrLn "module\tname\tuser_name\tkind\ttype"
  let mut moduleNames : Array Name := #[]
  for mod in env.header.moduleNames do
    if mod.getRoot == `MatrixConcentration then
      moduleNames := moduleNames.push mod
  let sortedModuleNames := moduleNames.qsort (fun a b => a.toString < b.toString)
  for mod in sortedModuleNames do
    modules.putStrLn mod.toString
  let constants := env.constants.toList.toArray.qsort
    (fun a b => a.1.toString < b.1.toString)
  for (name, info) in constants do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.getRoot == `MatrixConcentration then
        let axioms ← collectAxioms name
        let axiomNames := axioms.toList.toArray.qsort
          (fun a b => a.toString < b.toString)
        let axiomText := String.intercalate "," (axiomNames.toList.map Name.toString)
        let userName := (privateToUserName? name).getD name
        audit.putStrLn s!"{mod}\t{name}\t{userName}\t{auditKind info}\t{axiomText}"
        let typeText := tabSafe (reprStr info.type)
        decls.putStrLn s!"{mod}\t{name}\t{userName}\t{auditKind info}\t{typeText}"
