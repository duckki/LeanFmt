import Lean
import LeanFmt.Formatter

open System

namespace LeanFmt.Cli

structure Options where
  check : Bool := false
  checkException : Bool := false
  checkIdempotent : Bool := false
  recursive : Bool := false
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
  notIdempotent : Nat := 0
deriving DecidableEq, Repr

def ExceptionCounts.add (left right : ExceptionCounts) : ExceptionCounts :=
  {
    codeChanged := left.codeChanged + right.codeChanged
    lineOverflow := left.lineOverflow + right.lineOverflow
    missingRule := left.missingRule + right.missingRule
    notIdempotent := left.notIdempotent + right.notIdempotent
  }

def ExceptionCounts.isEmpty (counts : ExceptionCounts) : Bool :=
  counts.codeChanged == 0
  && counts.lineOverflow == 0
  && counts.missingRule == 0
  && counts.notIdempotent == 0

def ExceptionCounts.addFormattingException (counts : ExceptionCounts)
    : Formatter.Diagnostics.FormattingException → ExceptionCounts
  | .codeChanged => { counts with codeChanged := counts.codeChanged + 1 }
  | .lineOverflow _ => { counts with lineOverflow := counts.lineOverflow + 1 }
  | .missingRule _ => { counts with missingRule := counts.missingRule + 1 }

def ExceptionCounts.summary (counts : ExceptionCounts) : String :=
  String.intercalate "\n"
    [
      "exception counts:",
      s!"  code changed: {counts.codeChanged}",
      s!"  line overflow: {counts.lineOverflow}",
      s!"  missing rule: {counts.missingRule}",
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
      "Usage: fmt [--check] [--recursive] PATH...",
      "",
      "Options:",
      "  --check   Check whether files are already formatted without rewriting them.",
      "  -r, --recursive",
      "            Recursively format Lean files under directory arguments.",
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
    | "--recursive" :: rest | "-r" :: rest =>
        loop { options with recursive := true } files rest
    | "-h" :: _ | "--help" :: _ => .help
    | arg :: rest =>
        if arg.startsWith "-" then
          .error s!"unknown option: {arg}"
        else
          loop options (FilePath.mk arg :: files) rest
  loop {} [] args

def loadFormatterEnvironment : IO Lean.Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  Formatter.defaultEnvironment

def reportFormattingException
    (path : FilePath) (exception : Formatter.Diagnostics.FormattingException)
    : IO Unit :=
  match exception with
  | .codeChanged =>
      IO.eprintln s!"non-whitespace changed: {path}"
  | .lineOverflow occurrence => do
      IO.eprintln
        s!"line overflow: {path}:{occurrence.line}: {occurrence.width} > {Formatter.maxLineWidth}"
      IO.eprintln occurrence.text
  | .missingRule occurrence => do
      IO.eprintln s!"missing rule: {path}:{occurrence.line}: {occurrence.kind}"
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
      pure <| Formatter.Diagnostics.formattingExceptions sourceModule formattedModule
    else
      pure []
  let mut exceptionCounts : ExceptionCounts := {}
  for exception in exceptions do
    reportFormattingException path exception
    exceptionCounts := exceptionCounts.addFormattingException exception
  if options.checkIdempotent then
    let formattedAgain ← Formatter.formatSourceWithEnv env formatted path.toString
    if formattedAgain != formatted then
      IO.eprintln s!"not idempotent: {path}"
      exceptionCounts :=
        { exceptionCounts with notIdempotent := exceptionCounts.notIdempotent + 1 }
  pure exceptionCounts

def formatFile (env : Lean.Environment) (options : Options) (path : FilePath)
    : IO FileOutcome := do
  try
    let source ← IO.FS.readFile path
    let formatted ← Formatter.formatSourceWithEnv env source path.toString
    let exceptionCounts ← runDiagnosticChecks env options path source formatted
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

def isLeanFile (path : FilePath) : Bool := path.extension == some "lean"

partial def leanFilesInDirectory (recursive : Bool) (dir : FilePath)
    : IO (List FilePath) := do
  let mut files := []
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      if recursive && entry.fileName != ".lake" then
        files := files ++ (← leanFilesInDirectory recursive entry.path)
    else if isLeanFile entry.path then
      files := files ++ [entry.path]
  pure files

def expandInputPath (options : Options) (path : FilePath) : IO (List FilePath) := do
  if (← path.pathExists) && (← path.isDir) then
    leanFilesInDirectory options.recursive path
  else
    pure [path]

def expandInputPaths (options : Options) : IO (List FilePath) := do
  let mut files := []
  for path in options.files do
    files := files ++ (← expandInputPath options path)
  pure files

def runOptions (options : Options) : IO UInt32 := do
  let env ← loadFormatterEnvironment
  let files ← expandInputPaths options
  let mut changed := false
  let mut failed := false
  let mut exceptionCounts : ExceptionCounts := {}
  for file in files do
    let outcome ← formatFile env options file
    changed := changed || outcome.changed
    failed := failed || outcome.failed
    exceptionCounts := exceptionCounts.add outcome.exceptionCounts
  if !exceptionCounts.isEmpty then
    IO.eprintln exceptionCounts.summary
  let diagnosticMode := options.checkException || options.checkIdempotent
  let formattingDifferenceFailed := options.check && !diagnosticMode && changed
  pure <| if failed || formattingDifferenceFailed then 1 else 0

def runMain (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .run options => runOptions options
  | .help => IO.println usage; pure 0
  | .error message => IO.eprintln s!"leanfmt: {message}"; IO.eprintln usage; pure 1

end LeanFmt.Cli

def main (args : List String) : IO UInt32 := LeanFmt.Cli.runMain args
