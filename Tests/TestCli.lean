import Lean
import LeanFmt.Formatter

open System

namespace LeanFmt.TestCli

def loadFormatterEnvironment : IO Lean.Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  Formatter.defaultEnvironment

inductive Mode where
  | format
  | updateFixture
deriving DecidableEq, Repr

structure Options where
  mode : Mode := .format
  profile : Bool := false
  traceRenderer : Bool := false
  check : Bool := false
  files : List FilePath := []
deriving Repr

inductive ParseResult where
  | run (options : Options)
  | help
  | error (message : String)
deriving Repr

def usage : String :=
  String.intercalate "\n"
    [
      "Usage: fmt-test [--profile | --update-fixture [--trace-renderer]] [--check] PATH...",
      "",
      "Test-only options:",
      "  --profile          Print formatter timing information to stderr.",
      "  --update-fixture   Update the expected-output half of fixture files.",
      "  --trace-renderer   With --update-fixture, print renderer trace output.",
      "  --check            Report changes without rewriting files.",
      "  -h, --help"
    ]

def parseArgs (args : List String) : ParseResult :=
  let rec loop (options : Options) (files : List FilePath) : List String → ParseResult
    | [] =>
        if files.isEmpty then
          .error "no input files"
        else if options.traceRenderer && options.mode != .updateFixture then
          .error "--trace-renderer requires --update-fixture"
        else
          .run { options with files := files.reverse }
    | "--profile" :: rest => loop { options with profile := true } files rest
    | "--update-fixture" :: rest =>
        loop { options with mode := .updateFixture } files rest
    | "--trace-renderer" :: rest =>
        loop { options with traceRenderer := true } files rest
    | "--check" :: rest => loop { options with check := true } files rest
    | "-h" :: _ | "--help" :: _ => .help
    | arg :: rest =>
        if arg.startsWith "-" then
          .error s!"unknown option: {arg}"
        else
          loop options (FilePath.mk arg :: files) rest
  loop {} [] args

def fixtureSeparatorRule : String :=
  "-----------------------------------------------------------------------------------------"

def fixtureSeparator : String :=
  fixtureSeparatorRule
  ++ "\n"
  ++ "-- leanfmt: expected output below (DO NOT EDIT)\n"
  ++ fixtureSeparatorRule

def updateFixtureContent
    (env : Lean.Environment) (fileName content : String) (traceRenderer : Bool := false)
    : IO String := do
  match content.splitOn (fixtureSeparator ++ "\n") with
  | [source, _expected] =>
      let formatted ←
        if traceRenderer then
          let (formatted, trace) ←
            Formatter.Debug.formatSourceWithTraceWithEnv env source fileName
          IO.eprintln s!"renderer trace: {fileName}"
          unless trace.isEmpty do
            IO.eprintln trace
          pure formatted
        else
          Formatter.formatSourceWithEnv env source fileName
      pure <| source ++ fixtureSeparator ++ "\n" ++ formatted
  | _ => throw <| IO.userError "fixture must contain exactly one separator"

def printProfile (path : FilePath) (profile : Formatter.Debug.FormatProfile)
    : IO Unit := do
  IO.eprintln s!"leanfmt profile: {path}: normalize: {profile.normalizeMs}ms"
  IO.eprintln s!"leanfmt profile: {path}: parse: {profile.parseMs}ms"
  IO.eprintln s!"leanfmt profile: {path}: syntax-tree: {profile.syntaxTreeMs}ms"
  IO.eprintln s!"leanfmt profile: {path}: render: {profile.renderMs}ms"
  IO.eprintln s!"leanfmt profile: {path}: format-total: {profile.totalMs}ms"

def formatContent
    (env : Lean.Environment) (options : Options) (path : FilePath) (source : String)
    : IO String := do
  match options.mode with
  | .updateFixture =>
      updateFixtureContent env path.toString source options.traceRenderer
  | .format =>
      if options.profile then
        let (formatted, profile) ←
          Formatter.Debug.formatSourceProfiledWithEnv env source path.toString
        printProfile path profile
        pure formatted
      else
        Formatter.formatSourceWithEnv env source path.toString

def runOptions (options : Options) : IO UInt32 := do
  let env ← loadFormatterEnvironment
  let mut changed := false
  let mut failed := false
  for path in options.files do
    try
      let source ← IO.FS.readFile path
      let formatted ← formatContent env options path source
      if formatted != source then
        changed := true
        if options.check then
          IO.eprintln s!"needs update: {path}"
        else
          IO.FS.writeFile path formatted
          IO.println s!"updated {path}"
    catch error =>
      failed := true
      IO.eprintln s!"fmt-test: {path}: {error}"
  pure <| if failed || (options.check && changed) then 1 else 0

def runMain (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .run options => runOptions options
  | .help => IO.println usage; pure 0
  | .error message => IO.eprintln s!"fmt-test: {message}"; IO.eprintln usage; pure 1

end LeanFmt.TestCli
