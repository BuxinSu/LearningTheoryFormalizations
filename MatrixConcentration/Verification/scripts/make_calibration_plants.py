#!/usr/bin/env python3
"""Create the positive-control files used to calibrate audit scanners."""

from __future__ import annotations

from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
WORK = ROOT / ".audit_work"

PLANTS = {
    "SorryPlant.lean": """import Lean

set_option autoImplicit false

theorem VerificationPublicSorryPlant : True := by
  sorry

private theorem verificationPrivateSorryPlant : True := by
  sorry
""",
    "EscapePlant.lean": """import MatrixConcentration

set_option autoImplicit false

axiom VerificationEscapeAxiom : False

unsafe def verificationUnsafePlant : Nat := 0

theorem verificationNativeDecidePlant : True := by
  native_decide

run_cmd logInfo "verification run_cmd calibration plant"
""",
    "VacuityPlant.lean": """import MatrixConcentration

set_option autoImplicit false

theorem verificationContradictionPlant (x : Nat) (hpos : 0 < x) (hle : x <= 0) :
    x = x := by
  rfl

theorem verificationIsEmptyPlant (alpha : Type) [IsEmpty alpha] :
    forall x : alpha, False := by
  intro x
  exact isEmptyElim x

theorem verificationTrivialConclusionPlant (x : Nat) : x = x := by
  rfl
""",
    "DeadCodePlant.lean": """import Lean

set_option autoImplicit false

def verificationUnreferencedPlant : Nat := 37
""",
    "ConditionalPlant.lean": """import Lean

open Lean Meta

set_option autoImplicit false

def FakePrinciple : Prop := False

theorem fake_result (h : FakePrinciple) : True := by
  trivial

theorem fake_external_head_result (h : (0 : Nat) = 1) : True := by
  trivial

theorem fake_compound_result (h : FakePrinciple ∧ (0 : Nat) = 1) : True := by
  trivial

run_cmd Lean.Elab.Command.liftTermElabM do
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v10_inline_calibration_binders.tsv"
    IO.FS.Mode.write
  output.putStrLn
    "name\\tbinder_index\\tbinder_name\\tbinder_info\\tdomain_head\\tdomain_dependencies\\tdomain_type"
  for name in #[
      `fake_result,
      `fake_external_head_result,
      `fake_compound_result
    ] do
    let info ← getConstInfo name
    forallTelescope info.type fun binders _ => do
      for index in [:binders.size] do
        let binder := binders[index]!
        let localDecl ← getFVarLocalDecl binder
        if ← isProp localDecl.type then
          let domainHead := localDecl.type.getAppFn.constName?
            |>.map Name.toString |>.getD ""
          let dependencies := localDecl.type.getUsedConstantsAsSet.toList.toArray.qsort
            (fun left right => left.toString < right.toString)
          let dependencyText :=
            String.intercalate "," (dependencies.toList.map Name.toString)
          let binderInfo :=
            if localDecl.binderInfo == .instImplicit then
              "instanceImplicit"
            else
              "explicit"
          let domainType :=
            (reprStr localDecl.type).replace "\\t" " " |>.replace "\\n" " "
          output.putStrLn
            s!"{name}\\t{index + 1}\\t{localDecl.userName}\\t{binderInfo}\\t{domainHead}\\t{dependencyText}\\t{domainType}"
""",
    "BadWitness.lean": """import Lean

set_option autoImplicit false

theorem verificationBadWitness : ∃ n : Nat, n > 100 := by
  sorry
""",
    "AxiomCalibration.lean": """import Lean

open Lean

set_option autoImplicit false
set_option maxHeartbeats 0

theorem VerificationPublicAxiomCalibration : True := by
  sorry

private theorem verificationPrivateAxiomCalibration : True := by
  sorry

run_cmd do
  let env ← getEnv
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/axiom_calibration.tsv" IO.FS.Mode.write
  output.putStrLn "name\\tuser_name\\taxioms"
  let constants := env.constants.toList.toArray.qsort
    (fun a b => a.1.toString < b.1.toString)
  for (name, _) in constants do
    let userName := (privateToUserName? name).getD name
    if name == `VerificationPublicAxiomCalibration ||
        userName == `verificationPrivateAxiomCalibration then
      let axioms ← collectAxioms name
      let axiomNames := axioms.toList.toArray.qsort
        (fun a b => a.toString < b.toString)
      let axiomText := String.intercalate "," (axiomNames.toList.map Name.toString)
      output.putStrLn s!"{name}\\t{userName}\\t{axiomText}"
""",
    "V6AutoImplicitPlant.lean": """import Lean

open Lean Meta

set_option autoImplicit true

/-- Deliberately auto-binds the undeclared one-letter type `α`. -/
theorem verificationAutoBoundTypePlant (x : α) : x = x := rfl

/-- Deliberately auto-binds the undeclared one-letter proposition `P`. -/
theorem verificationAutoBoundPropPlant : P ∧ P → P := fun h => h.1

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

run_cmd do
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v6_autoimplicit_calibration_binders.tsv"
    IO.FS.Mode.write
  output.putStrLn
    "readme_name\\tresolved_name\\tbinder_index\\tbinder_name\\tbinder_info\\tdomain_class\\tbinder_type"
  for name in [
      ``verificationAutoBoundTypePlant,
      ``verificationAutoBoundPropPlant
    ] do
    let info ← getConstInfo name
    let rendered ← Lean.Elab.Command.liftTermElabM do
      forallTelescope info.type fun xs _ => do
        let mut rows : Array (String × String × String × String) := #[]
        for x in xs do
          let decl ← getFVarLocalDecl x
          let domainClass ← sortDomainClass decl.type
          let typeFmt ← ppExpr decl.type
          rows := rows.push
            (decl.userName.toString, binderInfoText decl.binderInfo,
              domainClass, typeFmt.pretty 1000)
        return rows
    for index in [:rendered.size] do
      let row := rendered[index]!
      output.putStrLn
        s!"{name}\\t{name}\\t{index + 1}\\t{row.1}\\t{row.2.1}\\t{row.2.2.1}\\t{row.2.2.2}"
""",
}


def main() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    for name, text in PLANTS.items():
        path = WORK / name
        path.write_text(text, encoding="utf-8")
        print(path.relative_to(ROOT))
    bad_tier_c = WORK / "V6BadTierCEvidence.tsv"
    bad_tier_c.write_text(
        "endpoint\tendpoint_kind\tevidence_name\n"
        "MatrixConcentration.covarianceMatrix\tdefinition\t"
        "MatrixConcentration.V6Witnesses."
        "calibration_unrelated_allowed_axiom\n",
        encoding="utf-8",
    )
    print(bad_tier_c.relative_to(ROOT))


if __name__ == "__main__":
    main()
