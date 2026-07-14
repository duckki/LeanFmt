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

def formatModule (moduleTree : SyntaxTree.Module) : String :=
  renderModuleTree moduleTree

def formatModuleWithEnv (_env : Environment) (moduleTree : SyntaxTree.Module)
    : IO String :=
  pure <| formatModule moduleTree

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

def formatPassWithEnv (env : Environment) (source fileName : String) : IO String := do
  formatModuleWithEnv env (← parseModuleWithEnv env source fileName)

def maxConvergencePasses : Nat := 4

def warnConvergenceFallback (fileName reason : String) : IO Unit :=
  IO.eprintln s!"leanfmt: warning: using original source for {fileName}: {reason}"

partial def convergeSourceWithEnv
    (env : Environment) (source fileName : String)
    (passesRemaining : Nat := maxConvergencePasses)
    (seen : List String := []) (fallback : String := source)
    : IO String := do
  if passesRemaining == 0 then
    warnConvergenceFallback fileName
      s!"formatting did not converge within {maxConvergencePasses} passes"
    pure fallback
  else
    let formatted ← formatPassWithEnv env source fileName
    if formatted == source then
      pure formatted
    else if seen.contains formatted then
      warnConvergenceFallback fileName "formatting entered a layout cycle"
      pure fallback
    else
      try
        convergeSourceWithEnv env formatted fileName (passesRemaining - 1)
          (source :: seen) fallback
      catch _ =>
        warnConvergenceFallback fileName "an intermediate result did not parse"
        pure fallback

end Internal

def formatSourceWithEnv (env : Environment) (source fileName : String := "<input>")
    : IO String :=
  let normalized := Internal.normalizeSource source
  Internal.convergeSourceWithEnv env normalized fileName Internal.maxConvergencePasses

def defaultEnvironment : IO Environment :=
  importModules (loadExts := true) #[{ module := `Lean }] {} 0

def formatSource (source fileName : String := "<input>") : IO String := do
  formatSourceWithEnv (← defaultEnvironment) source fileName

namespace Debug

/-! ## Tracing and profiling -/

def formatModuleWithTrace (moduleTree : SyntaxTree.Module) : String × String :=
  renderModuleTreeWithTrace moduleTree

def formatSourceProfiledWithEnv
    (env : Environment) (source fileName : String := "<input>")
    : IO (String × FormatProfile) := do
  let totalStart ← IO.monoMsNow
  let (normalizedSource, normalizeMs) ←
    timeIO <| pure <| Internal.normalizeSource source
  let (rawSyntax, parseMs) ←
    timeIO <| SyntaxTree.parseModuleSyntaxWithEnv env normalizedSource fileName
  let (moduleTree, syntaxTreeMs) ←
    timeIO <| pure <| Internal.buildModule normalizedSource rawSyntax
  let (formatted, renderMs) ←
    timeIO
    <| do
      let firstPass ← formatModuleWithEnv env moduleTree
      if firstPass == normalizedSource then
        pure firstPass
      else
        Internal.convergeSourceWithEnv env firstPass fileName
          (Internal.maxConvergencePasses - 1) [normalizedSource] normalizedSource
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
    : IO (String × String) := do
  let moduleTree ←
    Internal.parseModuleWithEnv env (Internal.normalizeSource source) fileName
  pure <| formatModuleWithTrace moduleTree

end Debug

end Formatter
end LeanFmt
