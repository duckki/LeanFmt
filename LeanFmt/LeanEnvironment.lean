import Lean

namespace LeanFmt.LeanEnvironment

/-!
This module is the maintenance boundary between LeanFmt and Lean's module
loader. Keep cache and worker policy outside it, and delegate the import fixed
point and environment construction to Lean.
-/

structure Spec where
  imports : Array Lean.Import
  level : Lean.OLeanLevel

/-!
`ImportPrefixState` is intentionally opaque to the driver by convention. The
driver may retain and return it, but every operation on it stays in this module
so Lean API changes remain localized here.
-/

abbrev ImportPrefixState := Lean.ImportState

def importKey (importDecl : Lean.Import) : String :=
  s!"{importDecl.module}|all={importDecl.importAll}|exported={importDecl.isExported}|meta={importDecl.isMeta}"

def levelKey : Lean.OLeanLevel → String
  | .exported => "exported"
  | .server => "server"
  | .private => "private"

def Spec.key (spec : Spec) : String :=
  levelKey spec.level
  ++ "\n"
  ++ String.intercalate "\n" (spec.imports.toList.map importKey)

def specForSource (source fileName : String) : IO Spec := do
  let inputContext := Lean.Parser.mkInputContext source fileName
  let (header, _state, _messages) ← Lean.Parser.parseHeader inputContext
  pure
    {
      imports := Lean.Elab.headerToImports header
      level :=
        if Lean.Elab.HeaderSyntax.isModule header then .exported else .private
    }

def importsForSource (source fileName : String) : IO (Array Lean.Import) := do
  pure (← specForSource source fileName).imports

def importEnvironmentDirect (spec : Spec) (leakEnv := false) : IO Lean.Environment := do
  unsafe Lean.enableInitializersExecution
  Lean.importModules (leakEnv := leakEnv) (loadExts := true)
    (level := spec.level) spec.imports {} 0

def firstImportKey (level : Lean.OLeanLevel) (importDecl : Lean.Import) : String :=
  levelKey level ++ "\n" ++ importKey importDecl

def importEnvironmentReusingFirstImport
    (spec : Spec) (firstImportState? : Option ImportPrefixState)
    (leakEnv := false)
    : IO (Lean.Environment × Option ImportPrefixState) := do
  unsafe Lean.enableInitializersExecution
  Lean.withImporting do
    let (firstImportState?, state) ←
      match spec.imports[0]? with
      | none => pure (none, default)
      | some firstImport =>
          match firstImportState? with
          | some state => pure (some state, state)
          | none =>
              let (_, state) ← (Lean.importModulesCore #[firstImport] spec.level).run
              pure (some state, state)
    let remainingImports := spec.imports.extract 1 spec.imports.size
    let (_, state) ← (Lean.importModulesCore remainingImports spec.level).run state
    let environment ←
      Lean.finalizeImport state spec.imports {} 0 leakEnv true spec.level
        (spec.level != .private)
    pure (environment, firstImportState?)

def importEnvironment (spec : Spec) (leakEnv := false) : IO Lean.Environment :=
  importEnvironmentDirect spec leakEnv

end LeanFmt.LeanEnvironment
