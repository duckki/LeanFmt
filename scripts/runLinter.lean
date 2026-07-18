import Batteries.Tactic.Lint
import Lake.CLI.Main

open Lean Core Batteries.Tactic.Lint

def lintRoot : Name := `LeanFmt.Cli

def disabledLinters : Array Name := #[`docBlame]

def buildModuleIfNeeded (module : Name) : IO Unit := do
  let olean ← findOLean module
  unless (← olean.pathExists) do
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{module}"]
      stdin := .null
    }
    let exitCode ← child.wait
    unless exitCode == 0 do
      throw <| IO.userError s!"failed to build {module}"

unsafe def runLinters : IO Unit := do
  initSearchPath (← findSysroot)
  buildModuleIfNeeded lintRoot
  let lintModule := `Batteries.Tactic.Lint
  buildModuleIfNeeded lintModule
  unsafe Lean.enableInitializersExecution
  let env ←
    importModules #[lintRoot, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let context : Core.Context := { fileName := "", fileMap := default, options := {} }
  let state : Core.State := { env }
  Prod.fst <$> (CoreM.toIO · context state) do
    let declarations ← getDeclsInPackage lintRoot.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let linters := linters.filter fun linter => !disabledLinters.contains linter.name
    let results ←
      lintCore declarations linters (inIO := true) (currentModule := lintRoot)
    if results.any (!·.2.isEmpty) then
      let formatted ←
        formatLinterResults results declarations (groupByFilename := true)
          (useErrorFormat := true) s!"in {lintRoot}" (runSlowLinters := true)
          .medium linters.size
      IO.print (← formatted.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {lintRoot}."

unsafe def main (_args : List String) : IO Unit := do
  runLinters
  IO.Process.exit 0
