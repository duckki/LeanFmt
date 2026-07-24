import LeanFmt.Driver.Options
import LeanFmt.Driver.Environment
import LeanFmt.Driver.Files
import LeanFmt.Driver.Workers

open System

namespace LeanFmt.Driver

def runOptionsWithCache (cache : EnvironmentCache) (options : Options) : IO UInt32 := do
  let (files, expandMs) ← timeIO <| expandInputPaths options
  let (cwd?, cwdMs) ← timeIO <| workerCwd? options
  profileLine options
    s!"inputs: files={files.length} expand={expandMs}ms worker-cwd={cwd?.isSome} cwd-check={cwdMs}ms"
  match options.workerEnvironment? with
  | some envFile =>
      formatFilesWithWorkerEnvironment cache options envFile files
  | none =>
      if shouldUseWorker options cwd? files.length then
        if (← checkWorkerToolchain cwd?) then
          runMixedWorkerBatches cache options cwd? files
        else
          pure 1
      else
        summarizeOutcomes options (← files.mapM (formatFile cache options))

def runOptions (options : Options) : IO UInt32 := do
  let cache ← loadFormatterEnvironment options
  runOptionsWithCache cache options

end LeanFmt.Driver
