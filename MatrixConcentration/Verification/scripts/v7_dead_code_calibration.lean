import Lean
import DeadCodePlant

open Lean

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let target := `verificationUnreferencedPlant
  if !env.contains target then
    throwError "dead-code calibration target did not load"
  let mut referring : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name == target then continue
    let typeUses := info.type.getUsedConstantsAsSet
    let valueUses :=
      match info.value? (allowOpaque := true) with
      | some value => value.getUsedConstantsAsSet
      | none => ({} : NameSet)
    if typeUses.contains target || valueUses.contains target then
      referring := referring.push name
  if !referring.isEmpty then
    throwError "dead-code calibration target unexpectedly has referrers: {referring}"
  logInfo m!"CALIBRATION_HIT unreferenced definition {target} REFERRERS 0"
