import LeanFmt.Driver.Files

open System

namespace LeanFmt.Driver

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

def formatSourceWithEnvForFile
    (env : Lean.Environment) (options : Options) (path : FilePath) (source : String)
    : IO FileOutcome := do
  try
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
    let changed := !result.fellBack && formatted != source
    if changed && !options.check then
      IO.FS.writeFile path formatted
      IO.println s!"formatted {path}"
    if !exceptionCounts.isEmpty then
      pure { changed, failed := true, exceptionCounts }
    else if !changed then
      pure {}
    else if options.check then
      IO.eprintln s!"needs formatting: {path}"
      pure { changed := true }
    else
      pure { changed := true }
  catch error =>
    IO.eprintln s!"leanfmt: {path}: {error}"
    pure { failed := true }

def formatFileWithEnv (env : Lean.Environment) (options : Options) (path : FilePath)
    : IO FileOutcome := do
  let (source, readMs) ← timeIO <| IO.FS.readFile path
  let (outcome, formatMs) ← timeIO <| formatSourceWithEnvForFile env options path source
  profileLine options
    s!"{path}: read={readMs}ms environment=0ms format={formatMs}ms total={readMs + formatMs}ms"
  pure outcome

def formatFile (cache : EnvironmentCache) (options : Options) (path : FilePath)
    : IO FileOutcome := do
  try
    let totalStart ← IO.monoMsNow
    let (source, readMs) ← timeIO <| IO.FS.readFile path
    let (env, environmentMs) ←
      timeIO
      <|  if options.profile then
            cache.environmentForSourceProfiled options source path.toString
          else
            cache.environmentForSource options source path.toString
    let (outcome, formatMs) ← timeIO <| formatSourceWithEnvForFile env options path source
    let totalStop ← IO.monoMsNow
    profileLine options
      s!"{path}: read={readMs}ms environment={environmentMs}ms format={formatMs}ms total={totalStop - totalStart}ms"
    pure outcome
  catch error =>
    IO.eprintln s!"leanfmt: {path}: {error}"
    pure { failed := true }

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
      if options.profile then
        args := args.push "--profile"
      if options.importEnvFirst then
        args := args.push "--import-env-first"
      if options.includeHidden then
        args := args.push "--include-hidden"
      if let some envFile := options.workerEnvironment? then
        args := args.push "--worker-env"
        args := args.push envFile.toString
      args := args.push "--env-cache-size"
      args := args.push s!"{options.environmentCacheSize}"
      args := args.push "--line-width"
      args := args.push s!"{options.formatterOptions.lineWidth}"
      for file in files do
        args := args.push file.toString
      args

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

def runWorkerBatch
    (options : Options) (cwd? : Option FilePath) (group : ImportWorkerGroup)
    : IO UInt32 := do
  let executable ← workerExecutable
  let group ← workerGroupForCwd cwd? group
  let childOptions := { options with workerEnvironment? := some group.environmentFile }
  let (exitCode, elapsedMs) ←
    timeIO <| do
      let child ←
        IO.Process.spawn
          {
            cmd := "lake"
            args := #["env", executable.toString] ++ childOptions.workerArgs group.files
            cwd := cwd?
            stdin := .null
            stdout := .inherit
            stderr := .inherit
          }
      child.wait
  profileLine options
    s!"worker-batch: env={group.environmentFile} files={group.files.length} elapsed={elapsedMs}ms"
  pure exitCode

partial def runWorkerBatches
    (options : Options) (cwd? : Option FilePath) (group : ImportWorkerGroup)
    : IO UInt32 := do
  let initialBatchSize ← initialWorkerBatchSize options cwd? group.files
  let rec loop (failed : Bool) : List FilePath → IO UInt32
    | [] => pure <| if failed then 1 else 0
    | remaining => do
        let batch := remaining.take initialBatchSize
        let exitCode ←
          runWorkerBatch options cwd?
            { environmentFile := group.environmentFile, files := batch }
        loop (failed || exitCode != 0) (remaining.drop initialBatchSize)
  loop false group.files

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

def formatFilesWithWorkerEnvironment
    (cache : EnvironmentCache) (options : Options) (envFile : FilePath)
    (files : List FilePath)
    : IO UInt32 := do
  let (env, environmentMs) ←
    timeIO <| environmentForWorkerEnvironmentFile cache options envFile
  profileLine options
    s!"worker-env: {envFile}: files={files.length} environment={environmentMs}ms"
  let (outcomes, formatMs) ← timeIO <| files.mapM (formatFileWithEnv env options)
  profileLine options
    s!"worker-env-files: {envFile}: files={files.length} format={formatMs}ms"
  summarizeOutcomes options outcomes

def formatDefaultEnvironmentFiles
    (cache : EnvironmentCache) (options : Options) (files : List FilePath)
    : IO UInt32 := do
  let (outcomes, elapsedMs) ←
    timeIO <| files.mapM (formatFileWithEnv cache.default options)
  profileLine options
    s!"default-environment-files: files={files.length} elapsed={elapsedMs}ms"
  summarizeOutcomes options outcomes

partial def runImportWorkerGroups
    (options : Options) (cwd? : Option FilePath) (groups : List ImportWorkerGroup)
    : IO UInt32 := do
  let rec loop (failed : Bool) : List ImportWorkerGroup → IO UInt32
    | [] => pure <| if failed then 1 else 0
    | group :: rest => do
        let exitCode ← runWorkerBatches options cwd? group
        loop (failed || exitCode != 0) rest
  loop false groups

def runMixedWorkerBatches
    (cache : EnvironmentCache) (options : Options) (cwd? : Option FilePath)
    (files : List FilePath)
    : IO UInt32 := do
  let ((defaultFiles, importFiles), partitionMs) ←
    timeIO <| partitionDefaultEnvironmentFiles cache files
  profileLine options
    s!"partition: files={files.length} default={defaultFiles.length} import={importFiles.length} elapsed={partitionMs}ms"
  let defaultExitCode ← formatDefaultEnvironmentFiles cache options defaultFiles
  let (importGroups, groupMs) ←
    timeIO <| importFileGroupsWithEnvironmentCandidates cwd? files importFiles
  profileLine options
    s!"import-groups: files={importFiles.length} groups={importGroups.length} elapsed={groupMs}ms"
  let importExitCode ← runImportWorkerGroups options cwd? importGroups
  pure <| if defaultExitCode != 0 || importExitCode != 0 then 1 else 0

end LeanFmt.Driver
