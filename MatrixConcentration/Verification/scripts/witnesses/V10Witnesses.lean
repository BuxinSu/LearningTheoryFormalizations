import Lean
import MatrixConcentration

open Lean MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 0

namespace MatrixConcentration.V10Witnesses

/-! A concrete source-external instantiation for the ordinary random-feature
model condition that has no producer theorem in the read-only library. -/

theorem hasReproducingProperty_zero :
    HasReproducingProperty
      (fun (_ _ : Unit) => (0 : ℝ))
      (Measure.dirac ())
      (fun (_ _ : Unit) => (0 : ℝ)) := by
  intro x y
  simp [HasReproducingProperty]

end MatrixConcentration.V10Witnesses

run_cmd do
  let output ← IO.FS.Handle.mk
    "MatrixConcentration/Verification/logs/v10_witness_axioms.tsv"
    IO.FS.Mode.write
  output.putStrLn "name\taxioms\ttype_dependencies"
  for name in #[
      `MatrixConcentration.V10Witnesses.hasReproducingProperty_zero
    ] do
    let axioms ← collectAxioms name
    let sorted := axioms.qsort (fun left right => left.toString < right.toString)
    let info ← getConstInfo name
    let dependencies := info.type.getUsedConstantsAsSet.toList.toArray.qsort
      (fun left right => left.toString < right.toString)
    output.putStrLn
      s!"{name}\t{String.intercalate "," (sorted.toList.map Name.toString)}\t{String.intercalate "," (dependencies.toList.map Name.toString)}"
