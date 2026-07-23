import Lean
import LeanFmt.Formatter

open System

namespace LeanFmt.Cli

structure Options where
  check : Bool := false
  checkException : Bool := false
  checkIdempotent : Bool := false
  recursive : Bool := false
  includeHidden : Bool := false
  worker : Bool := false
  formatterOptions : Formatter.Options := {}
  workerBatchSize? : Option Nat := none
  files : List FilePath := []
deriving Repr

inductive ParseResult where
  | run (options : Options)
  | help
  | error (message : String)
deriving Repr

structure ExceptionCounts where
  codeChanged : Nat := 0
  lineOverflow : Nat := 0
  missingRule : Nat := 0
  missingRuleWithRegisteredLeanFormatter : Nat := 0
  missingRuleWithParserDescription : Nat := 0
  missingRuleWithoutLeanFormatter : Nat := 0
  formatFallback : Nat := 0
  notIdempotent : Nat := 0
deriving DecidableEq, Repr

structure EnvironmentCache where
  default : Lean.Environment
  maxEntries : Nat
  entries : IO.Ref (List (String × Lean.Environment))

def ExceptionCounts.add (left right : ExceptionCounts) : ExceptionCounts :=
  {
    codeChanged := left.codeChanged + right.codeChanged
    lineOverflow := left.lineOverflow + right.lineOverflow
    missingRule := left.missingRule + right.missingRule
    missingRuleWithRegisteredLeanFormatter :=
      left.missingRuleWithRegisteredLeanFormatter
      + right.missingRuleWithRegisteredLeanFormatter
    missingRuleWithParserDescription :=
      left.missingRuleWithParserDescription + right.missingRuleWithParserDescription
    missingRuleWithoutLeanFormatter :=
      left.missingRuleWithoutLeanFormatter + right.missingRuleWithoutLeanFormatter
    formatFallback := left.formatFallback + right.formatFallback
    notIdempotent := left.notIdempotent + right.notIdempotent
  }

def ExceptionCounts.isEmpty (counts : ExceptionCounts) : Bool :=
  counts.codeChanged == 0
  && counts.lineOverflow == 0
  && counts.missingRule == 0
  && counts.formatFallback == 0
  && counts.notIdempotent == 0

def ExceptionCounts.addFormattingException (counts : ExceptionCounts)
    : Formatter.Diagnostics.FormattingException → ExceptionCounts
  | .codeChanged => { counts with codeChanged := counts.codeChanged + 1 }
  | .lineOverflow _ => { counts with lineOverflow := counts.lineOverflow + 1 }
  | .missingRule _ => { counts with missingRule := counts.missingRule + 1 }

def ExceptionCounts.addMissingRuleAudit (counts : ExceptionCounts)
    : Formatter.Diagnostics.LeanFormatterAvailability → ExceptionCounts
  | .registered =>
      {
        counts with
          missingRuleWithRegisteredLeanFormatter :=
            counts.missingRuleWithRegisteredLeanFormatter + 1
      }
  | .parserDescription =>
      {
        counts with
          missingRuleWithParserDescription :=
            counts.missingRuleWithParserDescription + 1
      }
  | .unavailable =>
      {
        counts with
          missingRuleWithoutLeanFormatter := counts.missingRuleWithoutLeanFormatter + 1
      }

def ExceptionCounts.summary (counts : ExceptionCounts) : String :=
  String.intercalate "\n"
    [
      "exception counts:",
      s!"  code changed: {counts.codeChanged}",
      s!"  line overflow: {counts.lineOverflow}",
      s!"  missing rule: {counts.missingRule}",
      s!"    registered Lean formatter: {counts.missingRuleWithRegisteredLeanFormatter}",
      s!"    Lean parser description: {counts.missingRuleWithParserDescription}",
      s!"    no Lean formatter metadata: {counts.missingRuleWithoutLeanFormatter}",
      s!"  format fallback: {counts.formatFallback}",
      s!"  not idempotent: {counts.notIdempotent}"
    ]

structure FileOutcome where
  changed : Bool := false
  failed : Bool := false
  exceptionCounts : ExceptionCounts := {}
deriving DecidableEq, Repr

def usage : String :=
  String.intercalate "\n"
    [
      "Usage: fmt [--check] [--recursive] [--include-hidden] PATH...",
      "",
      "Options:",
      "  --check   Check whether files are already formatted without rewriting them.",
      "  -r, --recursive",
      "            Recursively format Lean files under directory arguments.",
      "  --include-hidden",
      "            Include hidden entries discovered during directory traversal.",
      "  --line-width N",
      s!"            Use N as the formatter line limit; default is {Formatter.maxLineWidth}.",
      "  --worker-batch-size N",
      "            Format at most N files in each worker process.",
      "  -h, --help",
      "",
      "Internal debugging options (not intended for general use):",
      "  --check-exception",
      "            Check code preservation, remaining overflow, and missing rules.",
      "  --check-idempotent",
      "            Fail if formatting the formatted output changes it again.",
      "  With either diagnostic option, --check is a dry run; formatting",
      "  differences alone do not affect the exit status."
    ]

def parseArgs (args : List String) : ParseResult :=
  let rec loop (options : Options) (files : List FilePath) : List String → ParseResult
    | [] =>
        if files.isEmpty then
          .error "no input files"
        else
          .run { options with files := files.reverse }
    | "--check" :: rest => loop { options with check := true } files rest
    | "--check-exception" :: rest =>
        loop { options with checkException := true } files rest
    | "--check-idempotent" :: rest =>
        loop { options with checkIdempotent := true } files rest
    | "--line-width" :: value :: rest =>
        match value.toNat? with
        | some width =>
            if width == 0 then
              .error s!"invalid --line-width value: {value}"
            else
              loop
                {
                  options with
                    formatterOptions :=
                      { options.formatterOptions with lineWidth := width }
                }
                files rest
        | none => .error s!"invalid --line-width value: {value}"
    | "--line-width" :: [] =>
        .error "--line-width requires a value"
    | "--worker-batch-size" :: value :: rest =>
        match value.toNat? with
        | some size =>
            if size == 0 then
              .error s!"invalid --worker-batch-size value: {value}"
            else
              loop { options with workerBatchSize? := some size } files rest
        | none => .error s!"invalid --worker-batch-size value: {value}"
    | "--worker-batch-size" :: [] =>
        .error "--worker-batch-size requires a value"
    | "--worker" :: rest =>
        loop { options with worker := true } files rest
    | "--recursive" :: rest | "-r" :: rest =>
        loop { options with recursive := true } files rest
    | "--include-hidden" :: rest =>
        loop { options with includeHidden := true } files rest
    | "-h" :: _ | "--help" :: _ => .help
    | arg :: rest =>
        if arg.startsWith "-" then
          .error s!"unknown option: {arg}"
        else
          loop options (FilePath.mk arg :: files) rest
  loop {} [] args

def loadFormatterEnvironment : IO EnvironmentCache := do
  Lean.initSearchPath (← Lean.findSysroot)
  let default ← Formatter.defaultEnvironment
  let entries ← IO.mkRef []
  pure { default, maxEntries := 1, entries }

def importKey (importDecl : Lean.Import) : String :=
  s!"{importDecl.module}|all={importDecl.importAll}|exported={importDecl.isExported}|meta={importDecl.isMeta}"

def importsKey (imports : Array Lean.Import) : String :=
  String.intercalate "\n" (imports.toList.map importKey)

def usesDefaultEnvironmentImports (imports : Array Lean.Import) : Bool :=
  imports
    == #[
      { module := `Init : Lean.Import },
      { module := `Init, isMeta := true : Lean.Import }
    ]
  || imports.isEmpty

def importsForSource (source fileName : String) : IO (Array Lean.Import) := do
  let inputContext := Lean.Parser.mkInputContext source fileName
  let (header, _state, _messages) ← Lean.Parser.parseHeader inputContext
  pure <| Lean.Elab.headerToImports header

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
        let env ← SyntaxTree.importEnvironment imports
        cache.rememberEnvironment key env
        pure env

def EnvironmentCache.environmentForSource
    (cache : EnvironmentCache) (source fileName : String)
    : IO Lean.Environment := do
  let normalized := Formatter.Internal.normalizeSource source
  try
    discard
    <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates cache.default
        normalized fileName
    pure cache.default
  catch _ =>
    cache.environmentForImports (← importsForSource normalized fileName)

def sourceParsesWithDefaultEnvironment
    (cache : EnvironmentCache) (source fileName : String)
    : IO Bool := do
  try
    discard
    <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates cache.default
        (Formatter.Internal.normalizeSource source) fileName
    pure true
  catch _ =>
    pure false

def partitionDefaultEnvironmentFiles (cache : EnvironmentCache) (files : List FilePath)
    : IO (List FilePath × List FilePath) := do
  let mut defaultFiles := []
  let mut importFiles := []
  for file in files do
    let source ← IO.FS.readFile file
    if (← sourceParsesWithDefaultEnvironment cache source file.toString) then
      defaultFiles := file :: defaultFiles
    else
      importFiles := file :: importFiles
  pure (defaultFiles.reverse, importFiles.reverse)

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

def importFileGroups (files : List FilePath) : IO (List (List FilePath)) := do
  let mut groups := []
  for file in files do
    let source ← IO.FS.readFile file
    let imports ←
      importsForSource (Formatter.Internal.normalizeSource source) file.toString
    groups := addFileToImportGroup groups (importsKey imports) file
  pure <| groups.reverse.map fun (_, files) => files.reverse

def reportFormattingException
    (options : Options)
    (path : FilePath) (exception : Formatter.Diagnostics.FormattingException)
    (leanFormatter? : Option Formatter.Diagnostics.LeanFormatterAvailability := none)
    : IO Unit :=
  match exception with
  | .codeChanged =>
      IO.eprintln s!"non-whitespace changed: {path}"
  | .lineOverflow occurrence => do
      IO.eprintln
        s!"line overflow: {path}:{occurrence.line}: {occurrence.width} > {options.formatterOptions.lineWidth}"
      IO.eprintln occurrence.text
  | .missingRule occurrence => do
      IO.eprintln s!"missing rule: {path}:{occurrence.line}: {occurrence.kind}"
      if let some availability := leanFormatter? then
        IO.eprintln s!"Lean formatter: {availability.description}"
      IO.eprintln
      <| if occurrence.treeText.isEmpty then "<empty>" else occurrence.treeText

def runDiagnosticChecks
    (env : Lean.Environment)
    (options : Options)
    (path : FilePath)
    (source formatted : String)
    : IO ExceptionCounts := do
  let exceptions ←
    if options.checkException then
      let normalized := Formatter.Internal.normalizeSource source
      let sourceModule ←
        Formatter.Internal.parseModuleWithEnv env normalized path.toString
      let formattedModule ←
        Formatter.Internal.parseModuleWithEnv env formatted path.toString
      pure
      <| Formatter.Diagnostics.formattingExceptions sourceModule formattedModule
          options.formatterOptions
    else
      pure []
  let mut exceptionCounts : ExceptionCounts := {}
  for exception in exceptions do
    let leanFormatter? :=
      match exception with
      | .missingRule occurrence =>
          some
          <| Formatter.Diagnostics.leanFormatterAvailability env occurrence.syntaxKind?
      | _ => none
    reportFormattingException options path exception leanFormatter?
    exceptionCounts := exceptionCounts.addFormattingException exception
    if let some availability := leanFormatter? then
      exceptionCounts := exceptionCounts.addMissingRuleAudit availability
  if options.checkIdempotent then
    let formattedAgain ←
      Formatter.formatSourceWithEnv env formatted path.toString options.formatterOptions
    if formattedAgain != formatted then
      IO.eprintln s!"not idempotent: {path}"
      exceptionCounts :=
        { exceptionCounts with notIdempotent := exceptionCounts.notIdempotent + 1 }
  pure exceptionCounts

def formatFileWithEnv (env : Lean.Environment) (options : Options) (path : FilePath)
    : IO FileOutcome := do
  try
    let source ← IO.FS.readFile path
    let result ←
      Formatter.formatSourceWithEnvDetailed env source path.toString
        options.formatterOptions
    let formatted := result.formatted
    let exceptionCounts ←
      if result.fellBack then
        IO.eprintln s!"format fallback: {path}"
        pure { formatFallback := 1 }
      else
        runDiagnosticChecks env options path source formatted
    if !exceptionCounts.isEmpty then
      pure { failed := true, exceptionCounts }
    else if formatted == source then
      pure {}
    else if options.check then
      IO.eprintln s!"needs formatting: {path}"
      pure { changed := true }
    else
      IO.FS.writeFile path formatted
      IO.println s!"formatted {path}"
      pure { changed := true }
  catch error =>
    IO.eprintln s!"leanfmt: {path}: {error}"
    pure { failed := true }

def formatFile (cache : EnvironmentCache) (options : Options) (path : FilePath)
    : IO FileOutcome := do
  try
    let source ← IO.FS.readFile path
    let env ← cache.environmentForSource source path.toString
    formatFileWithEnv env options path
  catch error =>
    IO.eprintln s!"leanfmt: {path}: {error}"
    pure { failed := true }

def isLeanFile (path : FilePath) : Bool := path.extension == some "lean"

def isHiddenName (name : String) : Bool :=
  name.startsWith "." && name != "." && name != ".."

partial def leanFilesInDirectory (options : Options) (dir : FilePath)
    : IO (List FilePath) := do
  let mut files := []
  for entry in (← dir.readDir) do
    if options.includeHidden || !isHiddenName entry.fileName then
      if (← entry.path.isDir) then
        if options.recursive then
          files := files ++ (← leanFilesInDirectory options entry.path)
      else if isLeanFile entry.path then
        files := files ++ [entry.path]
  pure files

def expandInputPath (options : Options) (path : FilePath) : IO (List FilePath) := do
  if (← path.pathExists) && (← path.isDir) then
    leanFilesInDirectory options path
  else
    pure [path]

def expandInputPaths (options : Options) : IO (List FilePath) := do
  let mut files := []
  for path in options.files do
    files := files ++ (← expandInputPath options path)
  pure files

def Options.workerArgs (options : Options) (files : List FilePath) : Array String :=
  Id.run
    do
      let mut args := #["--worker"]
      if options.check then
        args := args.push "--check"
      if options.checkException then
        args := args.push "--check-exception"
      if options.checkIdempotent then
        args := args.push "--check-idempotent"
      if options.includeHidden then
        args := args.push "--include-hidden"
      args := args.push "--line-width"
      args := args.push s!"{options.formatterOptions.lineWidth}"
      for file in files do
        args := args.push file.toString
      args

def isLakePackageRoot (path : FilePath) : IO Bool := do
  pure
  <| (← (path / "lakefile.lean").pathExists) || (← (path / "lakefile.toml").pathExists)

partial def findLakePackageRoot? (path : FilePath) : IO (Option FilePath) := do
  let candidate ←
    if (← path.pathExists) && (← path.isDir) then
      pure path
    else
      match path.parent with
      | some parent => pure parent
      | none => pure "."
  if (← isLakePackageRoot candidate) then
    pure <| some candidate
  else
    match candidate.parent with
    | some parent =>
        if parent == candidate then
          pure none
        else
          findLakePackageRoot? parent
    | none => pure none

def workerCwd? (options : Options) : IO (Option FilePath) := do
  let rec commonRoot? (expected? : Option FilePath) : List FilePath → IO (Option FilePath)
    | [] => pure expected?
    | path :: rest => do
        let some root ←
          findLakePackageRoot? path
        | pure none
        match expected? with
        | none => commonRoot? (some root) rest
        | some expected =>
            if root.normalize == expected.normalize then
              commonRoot? expected? rest
            else
              pure none
  commonRoot? none options.files

def expectedLeanToolchain : String :=
  s!"leanprover/lean4:v{Lean.versionStringCore}"

def checkWorkerToolchain (cwd? : Option FilePath) : IO Bool := do
  match cwd? with
  | none => pure true
  | some cwd =>
      let toolchainFile := cwd / "lean-toolchain"
      if !(← toolchainFile.pathExists) then
        pure true
      else
        let targetToolchain := (← IO.FS.readFile toolchainFile).trimAscii.toString
        if targetToolchain == expectedLeanToolchain then
          pure true
        else
          IO.eprintln
            s!"leanfmt: target package uses {targetToolchain}, but this formatter was built with {expectedLeanToolchain}"
          IO.eprintln
            "leanfmt: rebuild/run LeanFmt with the target package's Lean toolchain, or rebuild the target package with this Lean version"
          pure false

def workerExecutable : IO FilePath := do
  let executable ← IO.appPath
  if executable.fileName == some "lean" then
    pure ".lake/build/bin/fmt"
  else
    pure executable

def shouldUseWorker (options : Options) (cwd? : Option FilePath) (fileCount : Nat)
    : Bool :=
  !options.worker
  && ((cwd?.isSome && fileCount > 1)
      || options.workerBatchSize?.any (fun size => fileCount > size))

def defaultWorkerBatchSize (_cwd? : Option FilePath) (files : List FilePath)
    : IO Nat := do
  pure files.length

def initialWorkerBatchSize (options : Options) (cwd? : Option FilePath)
    (files : List FilePath)
    : IO Nat := do
  match options.workerBatchSize? with
  | some size => pure size
  | none => defaultWorkerBatchSize cwd? files

def runWorkerBatch (options : Options) (cwd? : Option FilePath) (files : List FilePath)
    : IO UInt32 := do
  let executable ← workerExecutable
  let files ← pathsForWorkerCwd cwd? files
  let child ←
    IO.Process.spawn
      {
        cmd := "lake"
        args := #["env", executable.toString] ++ options.workerArgs files
        cwd := cwd?
        stdin := .null
        stdout := .inherit
        stderr := .inherit
      }
  child.wait

partial def runWorkerBatches
    (options : Options) (cwd? : Option FilePath) (files : List FilePath)
    : IO UInt32 := do
  let initialBatchSize ← initialWorkerBatchSize options cwd? files
  let rec loop (failed : Bool) : List FilePath → IO UInt32
    | [] => pure <| if failed then 1 else 0
    | remaining => do
        let batch := remaining.take initialBatchSize
        let exitCode ← runWorkerBatch options cwd? batch
        loop (failed || exitCode != 0) (remaining.drop initialBatchSize)
  loop false files

def summarizeOutcomes (options : Options) (outcomes : List FileOutcome) : IO UInt32 := do
  let changed := outcomes.any (·.changed)
  let failed := outcomes.any (·.failed)
  let exceptionCounts : ExceptionCounts :=
    outcomes.foldl (fun counts outcome => counts.add outcome.exceptionCounts) {}
  if !exceptionCounts.isEmpty then
    IO.eprintln exceptionCounts.summary
  let diagnosticMode := options.checkException || options.checkIdempotent
  let formattingDifferenceFailed := options.check && !diagnosticMode && changed
  pure <| if failed || formattingDifferenceFailed then 1 else 0

def formatDefaultEnvironmentFiles
    (cache : EnvironmentCache) (options : Options) (files : List FilePath)
    : IO UInt32 := do
  let outcomes ← files.mapM (formatFileWithEnv cache.default options)
  summarizeOutcomes options outcomes

partial def runImportWorkerGroups
    (options : Options) (cwd? : Option FilePath) (groups : List (List FilePath))
    : IO UInt32 := do
  let rec loop (failed : Bool) : List (List FilePath) → IO UInt32
    | [] => pure <| if failed then 1 else 0
    | group :: rest => do
        let exitCode ← runWorkerBatches options cwd? group
        loop (failed || exitCode != 0) rest
  loop false groups

def runMixedWorkerBatches
    (cache : EnvironmentCache) (options : Options) (cwd? : Option FilePath)
    (files : List FilePath)
    : IO UInt32 := do
  let (defaultFiles, importFiles) ← partitionDefaultEnvironmentFiles cache files
  let defaultExitCode ← formatDefaultEnvironmentFiles cache options defaultFiles
  let importGroups ← importFileGroups importFiles
  let importExitCode ← runImportWorkerGroups options cwd? importGroups
  pure <| if defaultExitCode != 0 || importExitCode != 0 then 1 else 0

def runOptionsWithCache (cache : EnvironmentCache) (options : Options) : IO UInt32 := do
  let files ← expandInputPaths options
  let cwd? ← workerCwd? options
  if shouldUseWorker options cwd? files.length then
    if (← checkWorkerToolchain cwd?) then
      runMixedWorkerBatches cache options cwd? files
    else
      pure 1
  else
    summarizeOutcomes options (← files.mapM (formatFile cache options))

def runOptions (options : Options) : IO UInt32 := do
  let cache ← loadFormatterEnvironment
  runOptionsWithCache cache options

def runMain (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .run options => runOptions options
  | .help => IO.println usage; pure 0
  | .error message => IO.eprintln s!"leanfmt: {message}"; IO.eprintln usage; pure 1

end LeanFmt.Cli

def main (args : List String) : IO UInt32 := LeanFmt.Cli.runMain args
