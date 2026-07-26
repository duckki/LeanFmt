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

structure Session where
  maxEntries : Nat
  firstImportStates : IO.Ref (List (String × Lean.ImportState))

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

def Session.create (maxEntries : Nat) : IO Session := do
  pure { maxEntries, firstImportStates := ← IO.mkRef [] }

def firstImportKey (level : Lean.OLeanLevel) (importDecl : Lean.Import) : String :=
  levelKey level ++ "\n" ++ importKey importDecl

def Session.rememberFirstImportState
    (session : Session) (key : String) (state : Lean.ImportState)
    : IO Unit := do
  if session.maxEntries != 0 then
    session.firstImportStates.modify
      fun entries =>
        ((key, state) :: entries.filter (fun entry => entry.1 != key))
        |>.take session.maxEntries

def Session.firstImportState
    (session : Session) (level : Lean.OLeanLevel) (importDecl : Lean.Import)
    : IO Lean.ImportState := do
  let key := firstImportKey level importDecl
  match (← session.firstImportStates.get).find? (fun entry => entry.1 == key) with
  | some (_, state) =>
      session.rememberFirstImportState key state
      pure state
  | none =>
      let (_, state) ← (Lean.importModulesCore #[importDecl] level).run
      session.rememberFirstImportState key state
      pure state

def Session.importEnvironment (session : Session) (spec : Spec) (leakEnv := false)
    : IO Lean.Environment := do
  unsafe Lean.enableInitializersExecution
  Lean.withImporting
    do
      let state ←
        match spec.imports[0]? with
        | none => pure default
        | some firstImport => session.firstImportState spec.level firstImport
      let remainingImports := spec.imports.extract 1 spec.imports.size
      let (_, state) ← (Lean.importModulesCore remainingImports spec.level).run state
      Lean.finalizeImport state spec.imports {} 0 leakEnv true spec.level
        (spec.level != .private)

def importEnvironment (spec : Spec) (leakEnv := false) : IO Lean.Environment :=
  importEnvironmentDirect spec leakEnv

end LeanFmt.LeanEnvironment
