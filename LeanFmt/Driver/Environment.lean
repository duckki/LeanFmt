import Lean
import LeanFmt.Driver.Options
import LeanFmt.Formatter

open System

namespace LeanFmt.Driver

structure ParserEnvironmentReservoir where
  exported? : Option Lean.Environment := none
  private? : Option Lean.Environment := none

structure ImportEnvironmentSpec where
  imports : Array Lean.Import
  level : Lean.OLeanLevel

structure EnvironmentCache where
  default : Lean.Environment
  maxEntries : Nat
  entries : IO.Ref (List (String × Lean.Environment))
  parserReservoir? : Option ParserEnvironmentReservoir := none

structure ImportWorkerGroup where
  environmentFile : FilePath
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

def importKey (importDecl : Lean.Import) : String :=
  s!"{importDecl.module}|all={importDecl.importAll}|exported={importDecl.isExported}|meta={importDecl.isMeta}"

def importLevelKey : Lean.OLeanLevel → String
  | .exported => "exported"
  | .server => "server"
  | .private => "private"

def importsKey (imports : Array Lean.Import) (level : Lean.OLeanLevel := .private)
    : String :=
  importLevelKey level ++ "\n" ++ String.intercalate "\n" (imports.toList.map importKey)

def importEnvironmentSpecForSource (source fileName : String)
    : IO ImportEnvironmentSpec := do
  let inputContext := Lean.Parser.mkInputContext source fileName
  let (header, _state, _messages) ← Lean.Parser.parseHeader inputContext
  pure
    {
      imports := Lean.Elab.headerToImports header
      level :=
        if Lean.Elab.HeaderSyntax.isModule header then .exported else .private
    }

def importsForSource (source fileName : String) : IO (Array Lean.Import) := do
  pure (← importEnvironmentSpecForSource source fileName).imports

def usesDefaultEnvironmentImports (imports : Array Lean.Import) : Bool :=
  imports
    == #[
      { module := `Init : Lean.Import },
      { module := `Init, isMeta := true : Lean.Import }
    ]
  || imports.isEmpty

def loadFormatterEnvironment (options : Options) : IO EnvironmentCache := do
  Lean.initSearchPath (← Lean.findSysroot)
  let default ← Formatter.defaultEnvironment
  let entries ← IO.mkRef []
  pure { default, maxEntries := options.environmentCacheSize, entries }

def pushUniqueImport (imports : Array Lean.Import) (fileImport : Lean.Import)
    : Array Lean.Import :=
  let key := importKey fileImport
  if imports.any fun existing => importKey existing == key then
    imports
  else
    imports.push fileImport

def importsForFiles (files : List FilePath)
    : IO (Array Lean.Import × Array Lean.Import) := do
  let mut exported := #[]
  let mut privateImports := #[]
  for file in files do
    let source ← IO.FS.readFile file
    let importSpec ←
      importEnvironmentSpecForSource
        (Formatter.Internal.normalizeSource source) file.toString
    for fileImport in importSpec.imports do
      if importSpec.level == .exported then
        exported := pushUniqueImport exported fileImport
      else
        privateImports := pushUniqueImport privateImports fileImport
  pure (exported, privateImports)

def loadParserEnvironmentReservoir (files : List FilePath)
    : IO (Option ParserEnvironmentReservoir) := do
  let (exportedImports, privateImports) ← importsForFiles files
  if exportedImports.isEmpty && privateImports.isEmpty then
    pure none
  else
    let exported? ←
      if exportedImports.isEmpty then
        pure none
      else
        some
        <$> SyntaxTree.importEnvironment exportedImports
              (leakEnv := true) (level := .exported)
    let private? ←
      if privateImports.isEmpty then
        pure none
      else
        some
        <$> SyntaxTree.importEnvironment privateImports
              (leakEnv := true) (level := .private)
    pure <| some { exported?, private? }

partial def moduleIndicesForImports
    (environment : Lean.Environment) (imports : Array Lean.Import)
    (level : Lean.OLeanLevel := .private)
    : IO (Array Lean.ModuleIdx) := do
  let requirementsRef ← IO.mkRef ({} : Lean.NameMap (Bool × Bool))
  let indicesRef ← IO.mkRef (#[] : Array Lean.ModuleIdx)
  let rec visitImports
      (moduleImports : Array Lean.Import)
      (importAll isExported needsData : Bool)
      : IO Unit := do
        for imported in moduleImports do
          let importedNeedsData := needsData && (imported.isExported || importAll)
          let importedImportAll := level == .private || importAll && imported.importAll
          let importedIsExported := isExported && imported.isExported
          unless importedNeedsData do
            continue
          let requirements ← requirementsRef.get
          let previous? := requirements.find? imported.module
          let effectiveImportAll := importedImportAll || previous?.any (·.1)
          let effectiveIsExported := importedIsExported || previous?.any (·.2)
          let changed :=
            previous?.isNone
            || previous?.any
                fun previous =>
                  previous.1 != effectiveImportAll || previous.2 != effectiveIsExported
          unless changed do
            continue
          requirementsRef.set
          <| requirements.insert imported.module (effectiveImportAll, effectiveIsExported)
          let some moduleIndex := environment.getModuleIdx? imported.module
          | throw
            <| IO.userError
                s!"shared parser environment is missing module {imported.module}"
          let moduleData := environment.header.moduleData[moduleIndex]!
          visitImports moduleData.imports effectiveImportAll
            effectiveIsExported importedNeedsData
          if previous?.isNone then
            indicesRef.modify (·.push moduleIndex)
  visitImports imports (importAll := true)
    (isExported := level < .private) (needsData := true)
  indicesRef.get

def ParserEnvironmentReservoir.environmentForImports
    (reservoir : ParserEnvironmentReservoir) (imports : Array Lean.Import)
    (level : Lean.OLeanLevel := .private)
    : IO Lean.Environment := do
  let environment? :=
    match level with
    | .exported => reservoir.exported?
    | .server => none
    | .private => reservoir.private?
  let some environment := environment?
  | throw
    <| IO.userError
        s!"shared parser environment has no {importLevelKey level} module reservoir"
  let moduleIndices ← moduleIndicesForImports environment imports level
  let importedEntries :=
    moduleIndices.map
      fun moduleIndex =>
        Lean.Parser.parserExtension.ext.getModuleEntries environment moduleIndex
  let parserState ←
    (Lean.Parser.parserExtension.ext.addImportedFn importedEntries).run
      { env := environment, opts := {} }
  pure <| Lean.Parser.parserExtension.ext.setState environment parserState

def EnvironmentCache.withParserReservoirForFiles
    (cache : EnvironmentCache) (files : List FilePath)
    : IO EnvironmentCache := do
  let parserReservoir? ← loadParserEnvironmentReservoir files
  let entries ← IO.mkRef []
  pure { cache with entries, parserReservoir? }

def EnvironmentCache.rememberEnvironment
    (cache : EnvironmentCache) (key : String) (env : Lean.Environment)
    : IO Unit := do
  if cache.maxEntries == 0 then
    pure ()
  else
    cache.entries.modify
      fun entries =>
        ((key, env) :: entries.filter (fun entry => entry.1 != key)).take cache.maxEntries

def EnvironmentCache.environmentForImports
    (cache : EnvironmentCache) (imports : Array Lean.Import)
    (level : Lean.OLeanLevel := .private)
    : IO Lean.Environment := do
  if level == .private && usesDefaultEnvironmentImports imports then
    pure cache.default
  else
    let key := importsKey imports level
    let entries ← cache.entries.get
    match entries.find? (fun entry => entry.1 == key) with
    | some (_, env) => cache.rememberEnvironment key env *> pure env
    | none =>
        let env ←
          match cache.parserReservoir? with
          | some reservoir => reservoir.environmentForImports imports level
          | none => SyntaxTree.importEnvironment imports (level := level)
        cache.rememberEnvironment key env
        pure env

def EnvironmentCache.environmentForSource
    (cache : EnvironmentCache) (options : Options) (source fileName : String)
    : IO Lean.Environment := do
  let normalized := Formatter.Internal.normalizeSource source
  if options.importEnvFirst then
    let importSpec ← importEnvironmentSpecForSource normalized fileName
    cache.environmentForImports importSpec.imports importSpec.level
  else
    try
      discard
      <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates cache.default
          normalized fileName
      pure cache.default
    catch _ =>
      let importSpec ← importEnvironmentSpecForSource normalized fileName
      cache.environmentForImports importSpec.imports importSpec.level

def EnvironmentCache.environmentForSourceProfiled
    (cache : EnvironmentCache) (options : Options) (source fileName : String)
    : IO Lean.Environment := do
  let (normalized, normalizeMs) ←
    timeIO <| pure <| Formatter.Internal.normalizeSource source
  if options.importEnvFirst then
    let (importSpec, headerMs) ←
      timeIO <| importEnvironmentSpecForSource normalized fileName
    let imports := importSpec.imports
    let level := importSpec.level
    if level == .private && usesDefaultEnvironmentImports imports then
      profileLine options
        s!"{fileName}: environment.normalize={normalizeMs}ms default-parse=skipped import-header={headerMs}ms import-env=0ms cache=default-imports"
      pure cache.default
    else
      let key := importsKey imports level
      let entries ← cache.entries.get
      match entries.find? (fun entry => entry.1 == key) with
      | some (_, env) =>
          let (_, rememberMs) ← timeIO <| cache.rememberEnvironment key env
          profileLine options
            s!"{fileName}: environment.normalize={normalizeMs}ms default-parse=skipped import-header={headerMs}ms import-env=0ms cache=hit remember={rememberMs}ms"
          pure env
      | none =>
          let (env, importMs) ←
            timeIO
            <| match cache.parserReservoir? with
                | some reservoir => reservoir.environmentForImports imports level
                | none => SyntaxTree.importEnvironment imports (level := level)
          let (_, rememberMs) ← timeIO <| cache.rememberEnvironment key env
          profileLine options
            s!"{fileName}: environment.normalize={normalizeMs}ms default-parse=skipped import-header={headerMs}ms import-env={importMs}ms cache=miss remember={rememberMs}ms"
          pure env
  else
    let defaultParseStart ← IO.monoMsNow
    try
      discard
      <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates cache.default
          normalized fileName
      let defaultParseStop ← IO.monoMsNow
      profileLine options
        s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParseStop - defaultParseStart}ms import-header=0ms import-env=0ms cache=default"
      pure cache.default
    catch _ =>
      let defaultParseStop ← IO.monoMsNow
      let defaultParseMs := defaultParseStop - defaultParseStart
      let (importSpec, headerMs) ←
        timeIO <| importEnvironmentSpecForSource normalized fileName
      let imports := importSpec.imports
      let level := importSpec.level
      if level == .private && usesDefaultEnvironmentImports imports then
        profileLine options
          s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParseMs}ms failed import-header={headerMs}ms import-env=0ms cache=default-imports"
        pure cache.default
      else
        let key := importsKey imports level
        let entries ← cache.entries.get
        match entries.find? (fun entry => entry.1 == key) with
        | some (_, env) =>
            let (_, rememberMs) ← timeIO <| cache.rememberEnvironment key env
            profileLine options
              s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParseMs}ms failed import-header={headerMs}ms import-env=0ms cache=hit remember={rememberMs}ms"
            pure env
        | none =>
            let (env, importMs) ←
              timeIO
              <| match cache.parserReservoir? with
                  | some reservoir => reservoir.environmentForImports imports level
                  | none => SyntaxTree.importEnvironment imports (level := level)
            let (_, rememberMs) ← timeIO <| cache.rememberEnvironment key env
            profileLine options
              s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParseMs}ms failed import-header={headerMs}ms import-env={importMs}ms cache=miss remember={rememberMs}ms"
            pure env

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

def exactImportFileGroups (files : List FilePath) : IO (List ImportWorkerGroup) := do
  let mut groups := []
  for file in files do
    let source ← IO.FS.readFile file
    let importSpec ←
      importEnvironmentSpecForSource
        (Formatter.Internal.normalizeSource source) file.toString
    groups :=
      addFileToImportGroup groups (importsKey importSpec.imports importSpec.level) file
  pure
  <| groups.reverse.filterMap
      fun (_, files) =>
        match files.reverse with
        | [] => none
        | envFile :: _ => some { environmentFile := envFile, files := files.reverse }

def importFileGroups (_cwd? : Option FilePath) (files : List FilePath)
    : IO (List ImportWorkerGroup) := do
  exactImportFileGroups files

def importFileGroupsWithEnvironmentCandidates
    (_cwd? : Option FilePath) (_environmentFiles files : List FilePath)
    : IO (List ImportWorkerGroup) := do
  exactImportFileGroups files

end LeanFmt.Driver
