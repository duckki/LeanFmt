import Lean
import LeanFmt.Driver.Options
import LeanFmt.Formatter
import LeanFmt.LeanEnvironment

open System

namespace LeanFmt.Driver

structure ImportPrefixCache where
  maxEntries : Nat
  entries : IO.Ref (List (String × LeanEnvironment.ImportPrefixState))

structure EnvironmentLoader where
  default : Lean.Environment
  lastExact : IO.Ref (Option (String × Lean.Environment))
  importPrefixes? : Option ImportPrefixCache := none
  leakExact : Bool := false

inductive EnvironmentOrigin where
  | default
  | reusedExact
  | importedExact

structure EnvironmentResult where
  environment : Lean.Environment
  origin : EnvironmentOrigin

structure ImportHeaderGroup where
  key : String
  files : List FilePath
deriving Repr

def profileLine (options : Options) (message : String) : IO Unit := do
  if options.profile then
    IO.eprintln s!"leanfmt profile: {message}"

def timeIO (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let value ← action
  let stop ← IO.monoMsNow
  pure (value, stop - start)

def usesDefaultEnvironmentImports (imports : Array Lean.Import) : Bool :=
  imports
    == #[
      { module := `Init : Lean.Import },
      { module := `Init, isMeta := true : Lean.Import }
    ]
  || imports.isEmpty

def shouldReuseImportPrefixes (options : Options) : Bool :=
  options.worker && options.importPrefixCacheSize != 0

def isExactEnvironmentWorker (options : Options) : Bool :=
  options.worker && !options.workerDefaultEnvironment

def shouldImportEnvironmentFirst (options : Options) : Bool :=
  options.importEnvFirst || isExactEnvironmentWorker options

def ImportPrefixCache.create (maxEntries : Nat) : IO ImportPrefixCache := do
  pure { maxEntries, entries := ← IO.mkRef [] }

def ImportPrefixCache.remember
    (cache : ImportPrefixCache) (key : String)
    (state : LeanEnvironment.ImportPrefixState)
    : IO Unit := do
  cache.entries.modify
    fun entries =>
      ((key, state) :: entries.filter (fun entry => entry.1 != key))
      |>.take cache.maxEntries

def ImportPrefixCache.find? (cache : ImportPrefixCache) (key : String)
    : IO (Option LeanEnvironment.ImportPrefixState) := do
  match (← cache.entries.get).find? (fun entry => entry.1 == key) with
  | some (_, state) => cache.remember key state *> pure (some state)
  | none => pure none

def ImportPrefixCache.importEnvironment
    (cache : ImportPrefixCache) (spec : LeanEnvironment.Spec) (leakEnv := false)
    : IO Lean.Environment := do
  let firstImportKey? := spec.imports[0]?.map (LeanEnvironment.firstImportKey spec.level)
  let firstImportState? ←
    match firstImportKey? with
    | some key => cache.find? key
    | none => pure none
  let (environment, importedFirstState?) ←
    LeanEnvironment.importEnvironmentReusingFirstImport spec firstImportState? leakEnv
  if firstImportState?.isNone then
    match firstImportKey?, importedFirstState? with
    | some key, some state => cache.remember key state
    | _, _ => pure ()
  pure environment

def loadEnvironmentLoader (options : Options) : IO EnvironmentLoader := do
  Lean.initSearchPath (← Lean.findSysroot)
  let exactWorker := isExactEnvironmentWorker options
  let default ←
    if exactWorker then
      Lean.mkEmptyEnvironment
    else
      Formatter.defaultEnvironment
  let lastExact ← IO.mkRef none
  let importPrefixes? ←
    if shouldReuseImportPrefixes options then
      some <$> ImportPrefixCache.create options.importPrefixCacheSize
    else
      pure none
  pure { default, lastExact, importPrefixes?, leakExact := exactWorker }

def EnvironmentLoader.lastExactEnvironment? (loader : EnvironmentLoader) (key : String)
    : IO (Option Lean.Environment) := do
  match ← loader.lastExact.get with
  | some (cachedKey, environment) =>
      pure <| if cachedKey == key then some environment else none
  | none => pure none

def EnvironmentLoader.rememberExactEnvironment
    (loader : EnvironmentLoader) (key : String) (environment : Lean.Environment)
    : IO Unit := do
  loader.lastExact.set (some (key, environment))

def EnvironmentLoader.environmentForSpec
    (loader : EnvironmentLoader) (spec : LeanEnvironment.Spec)
    : IO EnvironmentResult := do
  if !loader.leakExact
      && spec.level == .private
      && usesDefaultEnvironmentImports spec.imports then
    pure { environment := loader.default, origin := .default }
  else
    let key := spec.key
    match ← loader.lastExactEnvironment? key with
    | some environment => pure { environment, origin := .reusedExact }
    | none =>
        let environment ←
          match loader.importPrefixes? with
          | some prefixes => prefixes.importEnvironment spec loader.leakExact
          | none => LeanEnvironment.importEnvironment spec loader.leakExact
        loader.rememberExactEnvironment key environment
        pure { environment, origin := .importedExact }

def EnvironmentLoader.environmentForImports
    (loader : EnvironmentLoader) (imports : Array Lean.Import)
    (level : Lean.OLeanLevel := .private)
    : IO Lean.Environment := do
  pure (← loader.environmentForSpec { imports, level }).environment

def EnvironmentLoader.environmentForSource
    (loader : EnvironmentLoader) (options : Options) (source fileName : String)
    : IO Lean.Environment := do
  let normalized := Formatter.Internal.normalizeSource source
  if shouldImportEnvironmentFirst options then
    let importSpec ← LeanEnvironment.specForSource normalized fileName
    pure (← loader.environmentForSpec importSpec).environment
  else
    try
      discard
      <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates loader.default
          normalized fileName
      pure loader.default
    catch _ =>
      let importSpec ← LeanEnvironment.specForSource normalized fileName
      pure (← loader.environmentForSpec importSpec).environment

def EnvironmentOrigin.description : EnvironmentOrigin → String
  | .default => "default-imports"
  | .reusedExact => "reused-exact"
  | .importedExact => "imported-exact"

def EnvironmentLoader.environmentForSourceProfiled
    (loader : EnvironmentLoader) (options : Options) (source fileName : String)
    : IO Lean.Environment := do
  let (normalized, normalizeMs) ←
    timeIO <| pure <| Formatter.Internal.normalizeSource source
  let loadFromHeader (defaultParse : String)
      : IO Lean.Environment := do
        let (spec, headerMs) ← timeIO <| LeanEnvironment.specForSource normalized fileName
        let (result, environmentMs) ← timeIO <| loader.environmentForSpec spec
        profileLine options
          s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParse} import-header={headerMs}ms import-env={environmentMs}ms origin={result.origin.description}"
        pure result.environment
  if shouldImportEnvironmentFirst options then
    loadFromHeader "skipped"
  else
    let defaultParseStart ← IO.monoMsNow
    try
      discard
      <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates loader.default
          normalized fileName
      let defaultParseStop ← IO.monoMsNow
      profileLine options
        s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParseStop - defaultParseStart}ms import-header=0ms import-env=0ms cache=default"
      pure loader.default
    catch _ =>
      let defaultParseStop ← IO.monoMsNow
      loadFromHeader s!"{defaultParseStop - defaultParseStart}ms failed"

def relativePathFromComponents (base path : List String) : Option FilePath :=
  let rec dropCommon : List String → List String → List String × List String
    | baseHead :: baseRest, pathHead :: pathRest =>
        if baseHead == pathHead then
          dropCommon baseRest pathRest
        else
          (baseHead :: baseRest, pathHead :: pathRest)
    | baseRest, pathRest => (baseRest, pathRest)
  let (baseRest, pathRest) := dropCommon base path
  if baseRest.isEmpty then
    some <| FilePath.mk <| "/".intercalate pathRest
  else
    none

def pathForWorkerCwd (cwd? : Option FilePath) (file : FilePath) : IO FilePath := do
  match cwd? with
  | none => pure file
  | some cwd =>
      let currentDir ← IO.currentDir
      let absoluteFile := if file.isAbsolute then file else currentDir / file
      let absoluteCwd := if cwd.isAbsolute then cwd else currentDir / cwd
      match relativePathFromComponents
              absoluteCwd.normalize.components absoluteFile.normalize.components with
      | some relative => pure relative
      | none => pure absoluteFile.normalize

def pathsForWorkerCwd (cwd? : Option FilePath) (files : List FilePath)
    : IO (List FilePath) :=
  files.mapM (pathForWorkerCwd cwd?)

def addFileToImportGroup
    (groups : List (String × List FilePath)) (key : String) (file : FilePath)
    : List (String × List FilePath) :=
  let rec loop (seen : List (String × List FilePath))
      : List (String × List FilePath) → List (String × List FilePath)
    | [] => (key, [file]) :: seen
    | (groupKey, files) :: rest =>
        if groupKey == key then
          seen.reverse ++ ((groupKey, file :: files) :: rest)
        else
          loop ((groupKey, files) :: seen) rest
  loop [] groups

def exactImportHeaderGroups (files : List FilePath) : IO (List ImportHeaderGroup) := do
  let mut groups := []
  for file in files do
    let source ← IO.FS.readFile file
    let importSpec ←
      LeanEnvironment.specForSource
        (Formatter.Internal.normalizeSource source) file.toString
    groups := addFileToImportGroup groups importSpec.key file
  pure
  <| (groups.reverse.filterMap
        fun (key, files) =>
          match files.reverse with
          | [] => none
          | _ => some { key, files := files.reverse })
      |>.toArray
      |>.qsort (fun left right => left.key < right.key)
      |>.toList

end LeanFmt.Driver
