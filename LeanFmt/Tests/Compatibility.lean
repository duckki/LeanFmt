import LeanFmt
import LeanFmt.Cli
import LeanFmt.Tests.ExportedModuleSyntax
import LeanFmt.Tests.MetaImportRoot
import LeanFmt.Tests.ProjectSyntax

namespace LeanFmt.Tests.Compatibility

private def assertEq (label expected actual : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label} mismatch\nexpected:\n{expected}\nactual:\n{actual}"

private def assertTrue (label : String) (value : Bool) : IO Unit := do
  unless value do
    throw <| IO.userError s!"assertion failed: {label}"

private def assertContains (label text needle : String) : IO Unit := do
  assertTrue label ((text.splitOn needle).length > 1)

private def assertSyntaxTreeRoundTrip (env : Lean.Environment) : IO Unit := do
  let source := "def f (x : Nat) :=\n  x + 1\n"
  let moduleTree ←
    SyntaxTree.parseModuleStringWithEnv env source "compatibility-round-trip.lean"
  assertEq "syntax tree reconstruction" source moduleTree.reconstruct

private def assertFormattingInvariants (env : Lean.Environment) : IO Unit := do
  let source := "def compatibilitySmoke(left right:Nat):Nat:=left+right\n"
  let formatted ← Formatter.formatSourceWithEnv env source "compatibility-smoke.lean"
  let before ← SyntaxTree.parseModuleStringWithEnv env source "compatibility-before.lean"
  let after ← SyntaxTree.parseModuleStringWithEnv env formatted "compatibility-after.lean"
  assertTrue "compatibility formatting preserves code"
    (Formatter.Diagnostics.preservesCodeIgnoringWhitespace before after)
  let formattedAgain ←
    Formatter.formatSourceWithEnv env formatted "compatibility-formatted.lean"
  assertEq "compatibility formatting is idempotent" formatted formattedAgain

private def assertCliParsing : IO Unit := do
  match LeanFmt.Cli.parseArgs
          [
            "--check",
            "--check-exception",
            "--check-idempotent",
            "--jobs",
            "2",
            "Compatibility.lean"
          ] with
  | .run options =>
      assertTrue "CLI check flag" options.check
      assertTrue "CLI exception flag" options.checkException
      assertTrue "CLI idempotence flag" options.checkIdempotent
      assertTrue "CLI jobs flag" (options.workerJobs? == some 2)
      assertTrue "CLI input file" (options.files.map toString == ["Compatibility.lean"])
  | result =>
      throw <| IO.userError s!"compatibility CLI parse failed: {repr result}"

private def assertSourceImportLevels : IO Unit := do
  let moduleSpec ←
    LeanEnvironment.specForSource
      "module\n\npublic import Lean\n" "compatibility-module.lean"
  assertTrue "module headers import exported olean data" (moduleSpec.level == .exported)
  let scriptSpec ←
    LeanEnvironment.specForSource "import Lean\n" "compatibility-script.lean"
  assertTrue "script headers import private olean data" (scriptSpec.level == .private)

private def assertEnvironmentKeys : IO Unit := do
  let base : Lean.Import := { module := `Lean }
  let specs : Array LeanEnvironment.Spec :=
    #[
      { imports := #[base], level := .private },
      { imports := #[base], level := .exported },
      { imports := #[{ base with importAll := true }], level := .private },
      { imports := #[{ base with isExported := false }], level := .private },
      { imports := #[{ base with isMeta := true }], level := .private }
    ]
  let keys := (specs.map (·.key)).toList.eraseDups
  assertTrue "environment keys include every import modifier" (keys.length == specs.size)

private def assertImportPrefixReuse : IO Unit := do
  let spec : LeanEnvironment.Spec :=
    {
      imports :=
        #[
          { module := `LeanFmt.Tests.ProjectSyntax },
          { module := `LeanFmt.Tests.ExportedModuleSyntax }
        ]
      level := .private
    }
  let direct ← LeanEnvironment.importEnvironmentDirect spec
  let prefixes ← Driver.ImportPrefixCache.create 1
  let reused ← prefixes.importEnvironment spec
  let effectiveImports (env : Lean.Environment) :=
    env.header.modules.map
      fun imported =>
        s!"{imported.module}|all={imported.importAll}|exported={imported.isExported}|ir={repr imported.irPhases}"
  assertEq "prefix reuse preserves effective imports" (toString (effectiveImports direct))
    (toString (effectiveImports reused))
  assertEq "prefix reuse preserves imported constants"
    (toString direct.constants.map₁.size) (toString reused.constants.map₁.size)
  let parsed ←
    SyntaxTree.parseModuleStringWithEnv reused "#check project_syntax\n"
      "compatibility-imported-syntax.lean"
  assertTrue "prefix reuse preserves imported parser syntax"
    (parsed.tree.containsNodeKind (.raw `projectSyntax))

private def assertExportedEnvironment : IO Unit := do
  let exported ←
    LeanEnvironment.importEnvironment
      {
        imports := #[{ module := `LeanFmt.Tests.ExportedModuleSyntax }]
        level := .exported
      }
  assertTrue "exported environments omit private transitive imports"
    (exported.getModuleIdx? `LeanFmt.Tests.PrivateModuleDependency).isNone
  let parsed ←
    SyntaxTree.parseModuleStringWithEnv exported "#check exported_module_syntax\n"
      "compatibility-exported-syntax.lean"
  assertTrue "exported parser syntax remains available"
    (parsed.tree.containsNodeKind (.raw `exportedModuleSyntax))

  let prefixes ← Driver.ImportPrefixCache.create 1
  let withMetaIr ←
    prefixes.importEnvironment
      {
        imports := #[{ module := `LeanFmt.Tests.MetaImportRoot, isExported := true }]
        level := .exported
      }
  let some leafIndex := withMetaIr.getModuleIdx? `LeanFmt.Tests.MetaImportLeaf
  | throw <| IO.userError "expected meta/IR-only leaf import"
  assertTrue "meta/IR-only imports remain available"
    (withMetaIr.header.modules[leafIndex]!.irPhases == .comptime)

private def assertExecutableConfiguration : IO Unit := do
  let lakefile ← IO.FS.readFile "lakefile.toml"
  assertContains "lakefile defines public fmt executable" lakefile "name = \"fmt\""
  assertContains "fmt uses the runtime-aware entry point" lakefile
    "root = \"LeanFmt.Main\""
  assertContains "compatibility smoke builds fmt first" lakefile
    "name = \"compatibilityTest\""

def run : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Formatter.defaultEnvironment
  assertSyntaxTreeRoundTrip env
  assertFormattingInvariants env
  assertCliParsing
  assertSourceImportLevels
  assertEnvironmentKeys
  assertImportPrefixReuse
  assertExportedEnvironment
  assertExecutableConfiguration

end LeanFmt.Tests.Compatibility

def main (_args : List String) : IO UInt32 := do
  LeanFmt.Tests.Compatibility.run
  pure 0
