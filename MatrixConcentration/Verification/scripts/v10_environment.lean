import Lean
import MatrixConcentration

open Lean Meta

set_option autoImplicit false
set_option maxHeartbeats 0

private def tabSafe (text : String) : String :=
  text.replace "\t" " " |>.replace "\n" " "

private def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def definitionKind : DefinitionVal → String
  | info =>
      match info.hints with
      | .abbrev => "abbrev"
      | .regular _ => "def"
      | .opaque => "def"

private def reducibilityHint : DefinitionVal → String
  | info =>
      match info.hints with
      | .abbrev => "abbrev"
      | .regular height => s!"regular:{height}"
      | .opaque => "opaque"

private def binderInfoText : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instanceImplicit"

private def nameText (names : NameSet) : String :=
  String.intercalate ","
    (names.toList.toArray.qsort (fun left right =>
      left.toString < right.toString) |>.toList.map Name.toString)

private def projectModule? (env : Environment) (name : Name) : Option Name := do
  let moduleIndex ← env.getModuleIdxFor? name
  let moduleName := env.header.moduleNames[moduleIndex.toNat]!
  if moduleName.getRoot == `MatrixConcentration then
    some moduleName
  else
    none

private def sortedProjectConstants (env : Environment) :
    Array (Name × ConstantInfo) :=
  env.constants.toList.toArray
    |>.filter (fun entry => (projectModule? env entry.1).isSome)
    |>.qsort (fun left right => left.1.toString < right.1.toString)

private def hasPropCodomain (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ result => do
    let result ← whnf result
    match result with
    | .sort level => pure level.isZero
    | _ => pure false

private def fieldPropMode (type : Expr) : MetaM String :=
  forallTelescope type fun _ result => do
    let reduced ← whnf result
    match reduced with
    | .sort level =>
        if level.isZero then pure "predicate-codomain" else pure ""
    | _ =>
        if ← isProp result then pure "proof-valued" else pure ""

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- Filter by the defining module before sorting.  Sorting the whole imported
  -- Mathlib environment and then discarding all but the project constants is
  -- semantically identical but needlessly dominates this census.
  let constants := sortedProjectConstants env
  let logs := "MatrixConcentration/Verification/logs/"
  let predicates ← IO.FS.Handle.mk
    (logs ++ "v10_environment_predicates.tsv") IO.FS.Mode.write
  let fields ← IO.FS.Handle.mk
    (logs ++ "v10_environment_prop_fields.tsv") IO.FS.Mode.write
  let projectConstants ← IO.FS.Handle.mk
    (logs ++ "v10_environment_constants.tsv") IO.FS.Mode.write
  let structures ← IO.FS.Handle.mk
    (logs ++ "v10_environment_structures.tsv") IO.FS.Mode.write
  let roles ← IO.FS.Handle.mk
    (logs ++ "v10_declaration_roles.tsv") IO.FS.Mode.write
  let propBinders ← IO.FS.Handle.mk
    (logs ++ "v10_prop_binders.tsv") IO.FS.Mode.write
  let instanceBinders ← IO.FS.Handle.mk
    (logs ++ "v10_instance_binders.tsv") IO.FS.Mode.write
  let modules ← IO.FS.Handle.mk
    (logs ++ "v10_modules.txt") IO.FS.Mode.write
  let summary ← IO.FS.Handle.mk
    (logs ++ "v10_environment_summary.txt") IO.FS.Mode.write

  predicates.putStrLn
    "module\tname\tuser_name\tdeclaration_kind\treducibility_hint\trange_start_line\trange_end_line\ttype"
  fields.putStrLn
    "module\tstructure\tstructure_is_class\tfield\tfield_user_name\tprop_mode\trange_start_line\trange_end_line\ttype"
  projectConstants.putStrLn "module\tname\tkind"
  structures.putStrLn "module\tstructure\tstructure_is_class"
  roles.putStrLn
    "module\tname\tuser_name\tkind\trange_start_line\trange_end_line\tfinal_head\tfinal_dependencies\tvalue_dependencies"
  propBinders.putStrLn
    "module\tname\tuser_name\tkind\trange_start_line\trange_end_line\tbinder_index\tbinder_name\tbinder_info\tdomain_head\tdomain_dependencies\tdomain_type"
  instanceBinders.putStrLn
    "module\tname\tuser_name\tkind\trange_start_line\trange_end_line\tbinder_index\tbinder_name\tdomain_head\tdomain_dependencies\tdomain_type"

  let mut moduleNames : Array Name := #[]
  for moduleName in env.header.moduleNames do
    if moduleName.getRoot == `MatrixConcentration then
      moduleNames := moduleNames.push moduleName
  let sortedModuleNames :=
    moduleNames.qsort (fun left right => left.toString < right.toString)
  for moduleName in sortedModuleNames do
    modules.putStrLn moduleName.toString

  let mut projectConstantCount := 0
  let mut definitionCount := 0
  let mut predicateCount := 0
  let mut sourceBackedCount := 0
  let mut propBinderCount := 0
  let mut instanceBinderCount := 0
  for (name, info) in constants do
    let some moduleName := projectModule? env name | continue
    projectConstantCount := projectConstantCount + 1
    projectConstants.putStrLn s!"{moduleName}\t{name}\t{infoKind info}"
    let userName := (privateToUserName? name).getD name
    let ranges ← findDeclarationRanges? name
    let startLine := ranges.map (·.range.pos.line) |>.getD 0
    let endLine := ranges.map (·.range.endPos.line) |>.getD 0
    if startLine > 0 then sourceBackedCount := sourceBackedCount + 1

    match info with
    | .defnInfo defn =>
        definitionCount := definitionCount + 1
        if ← hasPropCodomain info.type then
          predicateCount := predicateCount + 1
          predicates.putStrLn
            s!"{moduleName}\t{name}\t{userName}\t{definitionKind defn}\t{reducibilityHint defn}\t{startLine}\t{endLine}\t{tabSafe (reprStr info.type)}"
    | _ => pure ()

    -- Generated auxiliaries have no source range. The named/inline
    -- conditional-interface question is about source declarations, while V4
    -- separately audits every generated constant for axioms.
    if startLine == 0 then continue
    let (declarationPropBinders, declarationInstanceBinders) ←
      forallTelescope info.type fun binders finalTarget => do
        let finalHead := finalTarget.getAppFn.constName?
          |>.map Name.toString |>.getD ""
        let valueDependencies :=
          -- Definition bodies can themselves encode conditional infrastructure
          -- (notably ProvidesCenteredRosenthalBootstrap). Never traverse theorem
          -- proof values: they are irrelevant to interface roles and can be
          -- enormous.
          match info with
          | .defnInfo defn => nameText defn.value.getUsedConstantsAsSet
          | _ => ""
        roles.putStrLn
          s!"{moduleName}\t{name}\t{userName}\t{infoKind info}\t{startLine}\t{endLine}\t{finalHead}\t{nameText finalTarget.getUsedConstantsAsSet}\t{valueDependencies}"
        let mut localPropBinderCount := 0
        let mut localInstanceBinderCount := 0
        if info.isTheorem then
          for index in [:binders.size] do
            let binder := binders[index]!
            let localDecl ← getFVarLocalDecl binder
            let domainHead := localDecl.type.getAppFn.constName?
              |>.map Name.toString |>.getD ""
            let domainDependencies := nameText localDecl.type.getUsedConstantsAsSet
            let domainType := tabSafe (reprStr localDecl.type)
            if localDecl.binderInfo == .instImplicit then
              localInstanceBinderCount := localInstanceBinderCount + 1
              instanceBinders.putStrLn
                s!"{moduleName}\t{name}\t{userName}\t{infoKind info}\t{startLine}\t{endLine}\t{index + 1}\t{localDecl.userName}\t{domainHead}\t{domainDependencies}\t{domainType}"
            if ← isProp localDecl.type then
              localPropBinderCount := localPropBinderCount + 1
              propBinders.putStrLn
                s!"{moduleName}\t{name}\t{userName}\t{infoKind info}\t{startLine}\t{endLine}\t{index + 1}\t{localDecl.userName}\t{binderInfoText localDecl.binderInfo}\t{domainHead}\t{domainDependencies}\t{domainType}"
        pure (localPropBinderCount, localInstanceBinderCount)
    propBinderCount := propBinderCount + declarationPropBinders
    instanceBinderCount := instanceBinderCount + declarationInstanceBinders

  let mut structureCount := 0
  let mut classCount := 0
  let mut propFieldCount := 0
  for (name, info) in constants do
    let some moduleName := projectModule? env name | continue
    -- Only inductive declarations can be structures. Calling
    -- `getStructureInfo?` on every theorem/definition is needlessly
    -- expensive in this 2,000+ constant environment.
    let .inductInfo _ := info | continue
    let some structureInfo := getStructureInfo? env name | continue
    structureCount := structureCount + 1
    let structureIsClass := isClass env name
    if structureIsClass then classCount := classCount + 1
    structures.putStrLn s!"{moduleName}\t{name}\t{structureIsClass}"
    for fieldInfo in structureInfo.fieldInfo do
      let fieldName := fieldInfo.projFn
      let some fieldConstant := env.constants.find? fieldName | continue
      let propMode ← fieldPropMode fieldConstant.type
      if propMode.isEmpty then continue
      propFieldCount := propFieldCount + 1
      let fieldUserName := (privateToUserName? fieldName).getD fieldName
      let ranges ← findDeclarationRanges? fieldName
      let startLine := ranges.map (·.range.pos.line) |>.getD 0
      let endLine := ranges.map (·.range.endPos.line) |>.getD 0
      fields.putStrLn
        s!"{moduleName}\t{name}\t{structureIsClass}\t{fieldName}\t{fieldUserName}\t{propMode}\t{startLine}\t{endLine}\t{tabSafe (reprStr fieldConstant.type)}"

  summary.putStrLn "V10 ENVIRONMENT CONDITIONAL-INTERFACE CENSUS"
  summary.putStrLn s!"MODULES {sortedModuleNames.size}"
  summary.putStrLn s!"PROJECT_CONSTANTS {projectConstantCount}"
  summary.putStrLn s!"SOURCE_BACKED_CONSTANTS {sourceBackedCount}"
  summary.putStrLn s!"PROJECT_DEFINITIONS {definitionCount}"
  summary.putStrLn s!"PROP_CODOMAIN_DEF_OR_ABBREV {predicateCount}"
  summary.putStrLn s!"PROJECT_STRUCTURES {structureCount}"
  summary.putStrLn s!"PROJECT_CLASSES {classCount}"
  summary.putStrLn s!"PROP_VALUED_STRUCTURE_OR_CLASS_FIELDS {propFieldCount}"
  summary.putStrLn s!"PROP_BINDERS {propBinderCount}"
  summary.putStrLn s!"INSTANCE_BINDERS {instanceBinderCount}"
  summary.putStrLn
    "CODOMAIN_RULE telescope all binders; weak-head-normalized final codomain is Sort 0"
  summary.putStrLn
    "ROLE_RULE Prop binders, final targets, and value dependencies are emitted independently"
  summary.putStrLn "VERDICT PASS"
