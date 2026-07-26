import LeanFmt.Driver.Options
import LeanFmt.Driver.Environment
import LeanFmt.Driver.Files
import LeanFmt.Driver.Workers

open System

namespace LeanFmt.Driver

def runOptionsWithLoader (loader : EnvironmentLoader) (options : Options)
    : IO UInt32 := do
  let (files, expandMs) ← timeIO <| expandInputPaths options
  let (cwd?, cwdMs) ← timeIO <| workerCwd? options
  profileLine options
    s!"inputs: files={files.length} expand={expandMs}ms worker-cwd={cwd?.isSome} cwd-check={cwdMs}ms"
  if shouldUseWorker options cwd? files.length then
    if (← checkWorkerToolchain cwd?) then
      runMixedWorkerBatches loader options cwd? files
    else
      pure 1
  else
    summarizeOutcomes options (← files.mapM (formatFile loader options))

def runOptions (options : Options) : IO UInt32 := do
  let loader ← loadEnvironmentLoader options
  runOptionsWithLoader loader options

end LeanFmt.Driver
