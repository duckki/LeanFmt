import LeanFmt.Formatter.Diagnostics
import LeanFmt.Formatter.Renderer
import LeanFmt.Formatter.SpaceRules

namespace LeanFmt
namespace Formatter

open Lean

namespace Debug

structure FormatProfile where
  normalizeMs : Nat
  parseMs : Nat
  syntaxTreeMs : Nat
  renderMs : Nat
  totalMs : Nat
deriving Repr

def timeIO (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let value ← action
  let stop ← IO.monoMsNow
  pure (value, stop - start)

end Debug

/-! ## Public formatting API -/

def formatModule (moduleTree : SyntaxTree.Module) (options : Options := {}) : String :=
  renderModuleTree moduleTree options

def formatModuleWithEnv (_env : Environment) (moduleTree : SyntaxTree.Module)
    (options : Options := {})
    : IO String :=
  pure <| formatModule moduleTree options

namespace Internal

/-! Shared phases used by ordinary, traced, and profiled formatting. -/

def normalizeSource (source : String) : String :=
  SpaceRules.normalizeLineEndings source

def buildModule (source : String) (rawSyntax : Syntax) : SyntaxTree.Module :=
  let tree := SyntaxTree.extractTree source rawSyntax
  { source, rawSyntax, tree, tokens := tree.tokens }

def parseModuleWithEnv (env : Environment) (source fileName : String)
    : IO SyntaxTree.Module := do
  let rawSyntax ← SyntaxTree.parseModuleSyntaxWithEnv env source fileName
  pure <| buildModule source rawSyntax

def formatPassWithEnv
    (env : Environment) (source fileName : String) (options : Options := {})
    : IO String := do
  formatModuleWithEnv env (← parseModuleWithEnv env source fileName) options

def maxConvergencePasses : Nat := 4

structure FormatResult where
  formatted : String
  fellBack : Bool := false
deriving BEq, Repr

def warnConvergenceFallback (fileName reason : String) : IO Unit :=
  IO.eprintln s!"leanfmt: warning: using original source for {fileName}: {reason}"

partial def convergeSourceWithEnv
    (env : Environment) (source fileName : String)
    (passesRemaining : Nat := maxConvergencePasses)
    (seen : List String := []) (fallback : String := source)
    (options : Options := {})
    : IO FormatResult := do
  if passesRemaining == 0 then
    warnConvergenceFallback fileName
      s!"formatting did not converge within {maxConvergencePasses} passes"
    pure { formatted := fallback, fellBack := true }
  else
    let formatted ← formatPassWithEnv env source fileName options
    if formatted == source then
      pure { formatted }
    else if seen.contains formatted then
      warnConvergenceFallback fileName "formatting entered a layout cycle"
      pure { formatted := fallback, fellBack := true }
    else
      try
        convergeSourceWithEnv env formatted fileName (passesRemaining - 1)
          (source :: seen) fallback options
      catch _ =>
        warnConvergenceFallback fileName "an intermediate result did not parse"
        pure { formatted := fallback, fellBack := true }

end Internal

def formatSourceWithEnvDetailed
    (env : Environment) (source fileName : String := "<input>")
    (options : Options := {})
    : IO Internal.FormatResult :=
  let normalized := Internal.normalizeSource source
  Internal.convergeSourceWithEnv env normalized fileName Internal.maxConvergencePasses
    [] normalized options

def formatSourceWithEnv (env : Environment) (source fileName : String := "<input>")
    (options : Options := {})
    : IO String := do
  pure (← formatSourceWithEnvDetailed env source fileName options).formatted

def defaultEnvironment : IO Environment :=
  SyntaxTree.importLeanEnvironment

def formatSource (source fileName : String := "<input>") (options : Options := {})
    : IO String := do
  formatSourceWithEnv (← defaultEnvironment) source fileName options

namespace Debug

/-! ## Tracing and profiling -/

def formatModuleWithTrace (moduleTree : SyntaxTree.Module) (options : Options := {})
    : String × String :=
  renderModuleTreeWithTrace moduleTree options

def formatSourceProfiledWithEnv
    (env : Environment) (source fileName : String := "<input>")
    (options : Options := {})
    : IO (String × FormatProfile) := do
  let totalStart ← IO.monoMsNow
  let (normalizedSource, normalizeMs) ← timeIO <| pure <| Internal.normalizeSource source
  let (rawSyntax, parseMs) ←
    timeIO <| SyntaxTree.parseModuleSyntaxWithEnv env normalizedSource fileName
  let (moduleTree, syntaxTreeMs) ←
    timeIO <| pure <| Internal.buildModule normalizedSource rawSyntax
  let (formatted, renderMs) ←
    timeIO <| do
      let firstPass ← formatModuleWithEnv env moduleTree options
      if firstPass == normalizedSource then
        pure firstPass
      else
        pure
          (← Internal.convergeSourceWithEnv env firstPass fileName
              (Internal.maxConvergencePasses - 1) [normalizedSource]
              normalizedSource options).formatted
  let totalStop ← IO.monoMsNow
  pure
    (
      formatted,
      {
        normalizeMs
        parseMs
        syntaxTreeMs
        renderMs
        totalMs := totalStop - totalStart
      }
    )

def formatSourceWithTraceWithEnv
    (env : Environment) (source fileName : String := "<input>")
    (options : Options := {})
    : IO (String × String) := do
  let moduleTree ←
    Internal.parseModuleWithEnv env (Internal.normalizeSource source) fileName
  pure <| formatModuleWithTrace moduleTree options

end Debug

end Formatter
end LeanFmt
