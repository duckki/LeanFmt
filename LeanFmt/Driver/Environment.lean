import Lean
import LeanFmt.Driver.Options
import LeanFmt.Formatter

open System

namespace LeanFmt.Driver

structure ParserEnvironmentReservoir where
  environment : Lean.Environment

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

def importsKey (imports : Array Lean.Import) : String :=
  String.intercalate "\n" (imports.toList.map importKey)

def importsForSource (source fileName : String) : IO (Array Lean.Import) := do
  let inputContext := Lean.Parser.mkInputContext source fileName
  let (header, _state, _messages) ← Lean.Parser.parseHeader inputContext
  pure <| Lean.Elab.headerToImports header

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

def importsForFiles (files : List FilePath) : IO (Array Lean.Import) := do
  let mut imports := #[]
  for file in files do
    let source ← IO.FS.readFile file
    let fileImports ←
      importsForSource (Formatter.Internal.normalizeSource source) file.toString
    for fileImport in fileImports do
      let key := importKey fileImport
      unless imports.any fun existing => importKey existing == key do
        imports := imports.push fileImport
  pure imports

def loadParserEnvironmentReservoir (files : List FilePath)
    : IO (Option ParserEnvironmentReservoir) := do
  let imports ← importsForFiles files
  if imports.isEmpty then
    pure none
  else
    pure
    <| some
        { environment :=
            ← SyntaxTree.importEnvironment imports (leakEnv := true) }

partial def moduleIndicesForImports
    (environment : Lean.Environment) (imports : Array Lean.Import)
    : IO (Array Lean.ModuleIdx) := do
  let visitedRef ← IO.mkRef ({} : Lean.NameSet)
  let indicesRef ← IO.mkRef (#[] : Array Lean.ModuleIdx)
  let rec visit (moduleName : Lean.Name)
      : IO Unit := do
        let visited ← visitedRef.get
        unless visited.contains moduleName do
          visitedRef.set <| visited.insert moduleName
          let some moduleIndex := environment.getModuleIdx? moduleName
          | throw
            <| IO.userError s!"shared parser environment is missing module {moduleName}"
          let moduleData := environment.header.moduleData[moduleIndex]!
          for imported in moduleData.imports do
            visit imported.module
          indicesRef.modify (·.push moduleIndex)
  for imported in imports do
    visit imported.module
  indicesRef.get

def ParserEnvironmentReservoir.environmentForImports
    (reservoir : ParserEnvironmentReservoir) (imports : Array Lean.Import)
    : IO Lean.Environment := do
  let moduleIndices ← moduleIndicesForImports reservoir.environment imports
  let importedEntries :=
    moduleIndices.map
      fun moduleIndex =>
        Lean.Parser.parserExtension.ext.getModuleEntries reservoir.environment moduleIndex
  let parserState ←
    (Lean.Parser.parserExtension.ext.addImportedFn importedEntries).run
      { env := reservoir.environment, opts := {} }
  pure <| Lean.Parser.parserExtension.ext.setState reservoir.environment parserState

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
    : IO Lean.Environment := do
  if usesDefaultEnvironmentImports imports then
    pure cache.default
  else
    let key := importsKey imports
    let entries ← cache.entries.get
    match entries.find? (fun entry => entry.1 == key) with
    | some (_, env) => cache.rememberEnvironment key env *> pure env
    | none =>
        let env ←
          match cache.parserReservoir? with
          | some reservoir => reservoir.environmentForImports imports
          | none => SyntaxTree.importEnvironment imports
        cache.rememberEnvironment key env
        pure env

def EnvironmentCache.environmentForSource
    (cache : EnvironmentCache) (options : Options) (source fileName : String)
    : IO Lean.Environment := do
  let normalized := Formatter.Internal.normalizeSource source
  if options.importEnvFirst then
    cache.environmentForImports (← importsForSource normalized fileName)
  else
    try
      discard
      <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates cache.default
          normalized fileName
      pure cache.default
    catch _ =>
      cache.environmentForImports (← importsForSource normalized fileName)

def EnvironmentCache.environmentForSourceProfiled
    (cache : EnvironmentCache) (options : Options) (source fileName : String)
    : IO Lean.Environment := do
  let (normalized, normalizeMs) ←
    timeIO <| pure <| Formatter.Internal.normalizeSource source
  if options.importEnvFirst then
    let (imports, headerMs) ← timeIO <| importsForSource normalized fileName
    if usesDefaultEnvironmentImports imports then
      profileLine options
        s!"{fileName}: environment.normalize={normalizeMs}ms default-parse=skipped import-header={headerMs}ms import-env=0ms cache=default-imports"
      pure cache.default
    else
      let key := importsKey imports
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
                | some reservoir => reservoir.environmentForImports imports
                | none => SyntaxTree.importEnvironment imports
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
      let (imports, headerMs) ← timeIO <| importsForSource normalized fileName
      if usesDefaultEnvironmentImports imports then
        profileLine options
          s!"{fileName}: environment.normalize={normalizeMs}ms default-parse={defaultParseMs}ms failed import-header={headerMs}ms import-env=0ms cache=default-imports"
        pure cache.default
      else
        let key := importsKey imports
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
                  | some reservoir => reservoir.environmentForImports imports
                  | none => SyntaxTree.importEnvironment imports
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
    let imports ←
      importsForSource (Formatter.Internal.normalizeSource source) file.toString
    groups := addFileToImportGroup groups (importsKey imports) file
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
