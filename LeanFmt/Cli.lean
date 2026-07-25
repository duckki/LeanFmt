import Lean
import LeanFmt.Driver
import LeanFmt.Formatter

open System

namespace LeanFmt.Cli

abbrev Options := LeanFmt.Driver.Options

inductive ParseResult where
  | run (options : Options)
  | help
  | error (message : String)
deriving Repr

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
      "  --profile",
      "            Print formatter CLI phase timings to stderr.",
      "  --env-cache-size N",
      "            Keep up to N imported parser environments in one formatter process.",
      "  --import-env-first",
      "            Import the source header environment before trying default parsing.",
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
    | "--profile" :: rest =>
        loop { options with profile := true } files rest
    | "--import-env-first" :: rest =>
        loop { options with importEnvFirst := true } files rest
    | "--env-cache-size" :: value :: rest =>
        match value.toNat? with
        | some size => loop { options with environmentCacheSize := size } files rest
        | none => .error s!"invalid --env-cache-size value: {value}"
    | "--env-cache-size" :: [] =>
        .error "--env-cache-size requires a value"
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

def runMain (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .run options => LeanFmt.Driver.runOptions options
  | .help => IO.println usage; pure 0
  | .error message => IO.eprintln s!"leanfmt: {message}"; IO.eprintln usage; pure 1

end LeanFmt.Cli

def main (args : List String) : IO UInt32 := LeanFmt.Cli.runMain args
