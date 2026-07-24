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

def ignoreRegionStartMarker : String := "-- leanfmt: off"

def ignoreRegionStopMarker : String := "-- leanfmt: on"

def normalizeSource (source : String) : String :=
  SpaceRules.normalizeLineEndings source

def lineChunks (source : String) : List String :=
  match source.splitOn "\n" with
  | [] => []
  | line :: rest =>
      let rec go : String → List String → List String
        | current, [] => [current]
        | current, next :: rest => (current ++ "\n") :: go next rest
      go line rest

inductive SourceChunk where
  | format (text : String)
  | preserve (text : String)
deriving BEq, Repr

namespace SourceChunk

def text : SourceChunk → String
  | .format text => text
  | .preserve text => text

def merge (left right : SourceChunk) : Option SourceChunk :=
  match left, right with
  | .format leftText, .format rightText => some <| .format (leftText ++ rightText)
  | .preserve leftText, .preserve rightText => some <| .preserve (leftText ++ rightText)
  | _, _ => none

end SourceChunk

def pushSourceChunk (chunks : List SourceChunk) (chunk : SourceChunk)
    : List SourceChunk :=
  if chunk.text.isEmpty then
    chunks
  else
    match chunks with
    | previous :: rest =>
        match SourceChunk.merge previous chunk with
        | some merged => merged :: rest
        | none => chunk :: chunks
    | [] => [chunk]

def lineStartsWithMarker (line marker : String) : Bool :=
  (SpaceRules.stripLeadingHorizontalWhitespace line).startsWith marker

partial def chunkIgnoredRegionsAux
    : List String → Bool → String → List SourceChunk → List SourceChunk
  | [], preserving, pending, chunks =>
      let chunk := if preserving then .preserve pending else .format pending
      (pushSourceChunk chunks chunk).reverse
  | line :: rest, preserving, pending, chunks =>
      if preserving then
        let pending := pending ++ line
        if lineStartsWithMarker line ignoreRegionStopMarker then
          chunkIgnoredRegionsAux rest false ""
            (pushSourceChunk chunks (.preserve pending))
        else
          chunkIgnoredRegionsAux rest true pending chunks
      else if lineStartsWithMarker line ignoreRegionStartMarker
              && !lineStartsWithMarker line ignoreNextMarker then
        let chunks := pushSourceChunk chunks (.format pending)
        chunkIgnoredRegionsAux rest true line chunks
      else
        chunkIgnoredRegionsAux rest false (pending ++ line) chunks

def chunkIgnoredRegions (source : String) : List SourceChunk :=
  chunkIgnoredRegionsAux (lineChunks source) false "" []

def hasIgnoredRegions (source : String) : Bool :=
  (lineChunks source).any
    fun line =>
      lineStartsWithMarker line ignoreRegionStartMarker
      && !lineStartsWithMarker line ignoreNextMarker

def buildModule
    (source : String) (rawSyntax : Syntax)
    (letBodyParserFacts : Array SyntaxTree.LetBodyParserFact := #[])
    : SyntaxTree.Module :=
  let tree := SyntaxTree.extractTree source rawSyntax letBodyParserFacts
  { source, rawSyntax, tree, tokens := tree.tokens }

def parseModuleWithEnv (env : Environment) (source fileName : String)
    : IO SyntaxTree.Module := do
  let parsed ←
    SyntaxTree.parseModuleSyntaxWithEnvCoreDetailed env source fileName
      (updateParserState := true)
  pure <| buildModule source parsed.rawSyntax parsed.letBodyParserFacts

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

partial def convergeModuleWithEnv
    (env : Environment) (moduleTree : SyntaxTree.Module) (fileName : String)
    (passesRemaining : Nat := maxConvergencePasses)
    (seen : List String := []) (fallback : String := moduleTree.source)
    (options : Options := {})
    : IO FormatResult := do
  let source := moduleTree.source
  if passesRemaining == 0 then
    warnConvergenceFallback fileName
      s!"formatting did not converge within {maxConvergencePasses} passes"
    pure { formatted := fallback, fellBack := true }
  else
    let formatted ← formatModuleWithEnv env moduleTree options
    if formatted == source then
      pure { formatted }
    else if seen.contains formatted then
      warnConvergenceFallback fileName "formatting entered a layout cycle"
      pure { formatted := fallback, fellBack := true }
    else
      try
        let formattedModule ← parseModuleWithEnv env formatted fileName
        let sourceFragments := Diagnostics.preservationFragments moduleTree
        let formattedFragments := Diagnostics.preservationFragments formattedModule
        if sourceFragments == formattedFragments then
          convergeModuleWithEnv env formattedModule fileName (passesRemaining - 1)
            (source :: seen) fallback options
        else
          let mismatch :=
            Diagnostics.firstPreservationFragmentMismatch?
              sourceFragments formattedFragments
          warnConvergenceFallback fileName
            s!"an intermediate result dropped or changed source tokens: {repr mismatch}"
          pure { formatted := fallback, fellBack := true }
      catch _ =>
        warnConvergenceFallback fileName "an intermediate result did not parse"
        pure { formatted := fallback, fellBack := true }

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
    convergeModuleWithEnv env (← parseModuleWithEnv env source fileName) fileName
      passesRemaining seen fallback options

def formatChunkWithEnv
    (env : Environment) (source fileName : String) (options : Options := {})
    : IO FormatResult :=
  convergeSourceWithEnv env source fileName maxConvergencePasses [] source options

def formatSourceChunksWithEnv
    (env : Environment) (chunks : List SourceChunk) (fileName : String)
    (options : Options := {})
    : IO FormatResult := do
  let mut fellBack := false
  let mut formatted := ""
  for chunk in chunks do
    match chunk with
    | .preserve text =>
        formatted := formatted ++ text
    | .format text =>
        let result ← formatChunkWithEnv env text fileName options
        fellBack := fellBack || result.fellBack
        formatted := formatted ++ result.formatted
  pure { formatted, fellBack }

def formatIgnoredRegionChunksWithEnv
    (env : Environment) (source fileName : String) (options : Options := {})
    : IO FormatResult :=
  formatSourceChunksWithEnv env (chunkIgnoredRegions source) fileName options

end Internal

def formatSourceWithEnvDetailed
    (env : Environment) (source fileName : String := "<input>")
    (options : Options := {})
    : IO Internal.FormatResult :=
  let normalized := Internal.normalizeSource source
  if Internal.hasIgnoredRegions normalized then
    Internal.formatIgnoredRegionChunksWithEnv env normalized fileName options
  else
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
  let (parsedSyntax, parseMs) ←
    timeIO
    <| SyntaxTree.parseModuleSyntaxWithEnvCoreDetailed env normalizedSource fileName
        (updateParserState := true)
  let (moduleTree, syntaxTreeMs) ←
    timeIO
    <| pure
    <| Internal.buildModule normalizedSource parsedSyntax.rawSyntax
        parsedSyntax.letBodyParserFacts
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
