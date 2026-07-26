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

def importEnvironment (spec : Spec) (leakEnv := false) : IO Lean.Environment := do
  unsafe Lean.enableInitializersExecution
  Lean.importModules (leakEnv := leakEnv) (loadExts := true)
    (level := spec.level) spec.imports {} 0

end LeanFmt.LeanEnvironment
