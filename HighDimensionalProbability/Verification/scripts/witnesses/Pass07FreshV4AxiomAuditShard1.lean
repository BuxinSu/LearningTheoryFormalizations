import Lean
import HighDimensionalProbability
import MatrixConcentration
import HighDimensionalProbability.Appendix
import HighDimensionalProbability.Appendix.Infra.BerryEsseenSmoothing

/-!
# V4 exhaustive buildable-surface axiom audit harness

This scratch module imports the two roots, the isolated Appendix closure, and
the sole buildable orphan.  V1/V2 prove that the remaining four
MatrixConcentration orphans cannot elaborate because
`Appendix_RosenthalPinelis` fails.  A separate full-surface import harness
records that failure; this harness audits every constant in the maximal
elaborated surface and deliberately does not filter internal or private names.

The planted private theorem below is excluded from the library audit by the
module-root filter and is used only to calibrate that `Lean.collectAxioms`
detects `sorryAx` through mangled private names.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean

private theorem v4_private_bad_calibration : True := by
  sorry

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def isAuditedModule (moduleName : Name) : Bool :=
  moduleName.getRoot == `HighDimensionalProbability ||
    moduleName.getRoot == `MatrixConcentration

private def renderAxioms (axioms : Array Name) : String :=
  String.intercalate ";" (axioms.toList.map toString)

private def privateUserName (name : Name) : String :=
  match privateToUserName? name with
  | some userName => toString userName
  | none => ""

private def boolText (value : Bool) : String :=
  if value then "true" else "false"

private def binderInfoText : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def renderRawExpr (expr : Expr) : String :=
  toString (repr expr)

private def tsvEscape (text : String) : String :=
  (((text.replace "\\" "\\\\").replace "\t" "\\t").replace "\n" "\\n").replace
    "\r" "\\r"

private def moduleNameFor?
    (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  env.header.moduleNames[moduleIdx.toNat]?

private def writeCalibration
    (handle : IO.FS.Handle) (label : String) (name : Name)
    (axioms : Array Name) : IO Unit := do
  let hasSorry := axioms.contains ``sorryAx
  handle.putStrLn <| String.intercalate "\t"
    [label, toString name, boolText hasSorry, renderAxioms axioms]
  unless hasSorry do
    throw <| IO.userError
      s!"V4 calibration {label} did not contain sorryAx: {name}"

private def writeDependencyEdge
    (handle : IO.FS.Handle) (env : Environment)
    (sourceModule source : Name) (sourceKind origin : String)
    (target : Name) : IO Unit := do
  let targetModule :=
    match moduleNameFor? env target with
    | some moduleName => toString moduleName
    | none => ""
  handle.putStrLn <| String.intercalate "\t"
    [ toString sourceModule
    , toString source
    , sourceKind
    , origin
    , targetModule
    , toString target
    ]

private partial def writeTelescope
    (handle : IO.FS.Handle) (moduleName name : Name)
    (userName kind : String) (type : Expr) (index : Nat := 0) :
    IO (Nat × Expr) := do
  match type.consumeMData with
  | .forallE binderName binderType body binderInfo =>
      handle.putStrLn <| String.intercalate "\t"
        [ toString moduleName
        , toString name
        , userName
        , kind
        , toString index
        , toString binderName
        , binderInfoText binderInfo
        , tsvEscape (renderRawExpr binderType)
        ]
      writeTelescope handle moduleName name userName kind body (index + 1)
  | conclusion => pure (index, conclusion)

run_cmd do
  let env ← getEnv
  let calibrationHandle ← IO.FS.Handle.mk
    "/tmp/pass07_v4_shard1/axiom_calibration.tsv"
    IO.FS.Mode.write
  calibrationHandle.putStrLn "label\tname\thas_sorryAx\taxioms"

  let exerciseName := ``HDP.Chapter1.exercise_1_2
  let exerciseAxioms ← collectAxioms exerciseName
  writeCalibration calibrationHandle "known_exercise_sorry"
    exerciseName exerciseAxioms

  let privateBad? := env.constants.toList.findSome? fun (name, _) =>
    match privateToUserName? name with
    | some userName =>
        if userName == `v4_private_bad_calibration then some name else none
    | none => none
  let some privateBad := privateBad?
    | throwError "privateToUserName? did not recover v4_private_bad_calibration"
  let privateBadAxioms ← collectAxioms privateBad
  writeCalibration calibrationHandle "planted_private_sorry"
    privateBad privateBadAxioms
  calibrationHandle.flush

  let moduleHandle ← IO.FS.Handle.mk
    "/tmp/pass07_v4_shard1/axiom_modules.txt"
    IO.FS.Mode.write
  for moduleName in env.header.moduleNames do
    if isAuditedModule moduleName then
      moduleHandle.putStrLn (toString moduleName)
  moduleHandle.flush

  let auditHandle ← IO.FS.Handle.mk
    "/tmp/pass07_v4_shard1/axiom_audit.tsv"
    IO.FS.Mode.write
  auditHandle.putStrLn
    "module\tname\tkind\tis_private\tprivate_user_name\tis_internal\taxioms"
  let typeHandle ← IO.FS.Handle.mk
    "/tmp/pass07_v4_shard1/axiom_declaration_types.tsv"
    IO.FS.Mode.write
  typeHandle.putStrLn <|
    "module\tname\tkind\tis_private\tprivate_user_name\tis_internal\t" ++
      "level_params\tbinder_count\ttype_raw\tconclusion_raw"
  let binderHandle ← IO.FS.Handle.mk
    "/tmp/pass07_v4_shard1/axiom_declaration_binders.tsv"
    IO.FS.Mode.write
  binderHandle.putStrLn <|
    "module\tname\tprivate_user_name\tkind\tbinder_index\tbinder_name\t" ++
      "binder_info\tbinder_type_raw"
  let edgeHandle ← IO.FS.Handle.mk
    "/tmp/pass07_v4_shard1/axiom_direct_dependencies.tsv"
    IO.FS.Mode.write
  edgeHandle.putStrLn <|
    "source_module\tsource\tsource_kind\torigin\ttarget_module\ttarget"
  let mut auditedIndex : Nat := 0
  for (name, info) in env.constants.toList do
    if let some moduleName := moduleNameFor? env name then
      if isAuditedModule moduleName then
        let currentIndex := auditedIndex
        auditedIndex := auditedIndex + 1
        if currentIndex % 2 == 1 then
          let axioms ← collectAxioms name
          let isPrivate := (privateToUserName? name).isSome
          let userName := privateUserName name
          let kind := constantKind info
          auditHandle.putStrLn <| String.intercalate "\t"
            [ toString moduleName
            , toString name
            , kind
            , boolText isPrivate
            , userName
            , boolText name.isInternal
            , renderAxioms axioms
            ]
          let (binderCount, conclusion) ←
            writeTelescope binderHandle moduleName name userName kind info.type
          typeHandle.putStrLn <| String.intercalate "\t"
            [ toString moduleName
            , toString name
            , kind
            , boolText isPrivate
            , userName
            , boolText name.isInternal
            , String.intercalate ";" (info.levelParams.map toString)
            , toString binderCount
            , tsvEscape (renderRawExpr info.type)
            , tsvEscape (renderRawExpr conclusion)
            ]
          for target in info.type.getUsedConstants do
            writeDependencyEdge edgeHandle env moduleName name kind "type" target
          if let some value := info.value? (allowOpaque := true) then
            for target in value.getUsedConstants do
              writeDependencyEdge edgeHandle env moduleName name kind "value" target
  auditHandle.flush
  typeHandle.flush
  binderHandle.flush
  edgeHandle.flush
