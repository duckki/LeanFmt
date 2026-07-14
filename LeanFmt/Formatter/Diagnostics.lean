import LeanFmt.Formatter.Renderer
import LeanFmt.Formatter.SpaceRules

namespace LeanFmt
namespace Formatter
namespace Diagnostics

open Lean

inductive DiagnosticKind where
  | compactBangApplication
deriving BEq, Repr

structure Diagnostic where
  kind : DiagnosticKind
  span : SyntaxTree.Span
  message : String
deriving BEq, Repr

structure MissingRuleOccurrence where
  kind : String
  line : Nat
  treeText : String
deriving BEq, Repr

structure OverflowOccurrence where
  line : Nat
  width : Nat
  text : String
deriving BEq, Repr

inductive FormattingException where
  | codeChanged
  | lineOverflow (occurrence : OverflowOccurrence)
  | missingRule (occurrence : MissingRuleOccurrence)
deriving BEq, Repr

def realTokens (moduleTree : SyntaxTree.Module) : List SyntaxTree.Token :=
  moduleTree.sourceOrderedTokens.toList.filter fun token => !token.lexeme.isEmpty

def isApplicationArgumentStart (token : SyntaxTree.Token) : Bool :=
  token.role == .ident
  || SpaceRules.stringIn token.lexeme ["(", "[", "{", "⟨", "⟪", "."]

def compactBangApplicationDiagnostic (bang head : SyntaxTree.Token) : Diagnostic :=
  {
    kind := .compactBangApplication
    span := { start := bang.span.start, stop := head.span.stop }
    message := "compact `!f a b` is ambiguous; use `! f a b`, `! (f a b)`, or `!f`"
  }

partial def diagnosticsForTokensAux (source : String)
    : List SyntaxTree.Token → List Diagnostic
  | bang :: head :: next :: rest =>
      let restDiagnostics := diagnosticsForTokensAux source (head :: next :: rest)
      let bangHeadTrivia := SyntaxTree.sourceText source bang.span.stop head.span.start
      let headNextTrivia := SyntaxTree.sourceText source head.span.stop next.span.start
      if bang.lexeme == "!"
          && bangHeadTrivia.isEmpty
          && head.role == .ident
          && SpaceRules.hasOnlyHorizontalTrivia headNextTrivia
          && isApplicationArgumentStart next then
        compactBangApplicationDiagnostic bang head :: restDiagnostics
      else
        restDiagnostics
  | _token :: rest => diagnosticsForTokensAux source rest
  | [] => []

def diagnosticsForModule (moduleTree : SyntaxTree.Module) : List Diagnostic :=
  diagnosticsForTokensAux moduleTree.source (realTokens moduleTree)

def newlineCount (text : String) : Nat :=
  text.toList.foldl (fun count char => if char == '\n' then count + 1 else count) 0

def lineNumberAt (source : String) (position : String.Pos.Raw) : Nat :=
  newlineCount (SyntaxTree.sourceText source 0 position) + 1

def missingRuleReportSkipsTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.byTactic) _ => true
  | .node (.raw `Lean.Parser.Term.byTactic') _ => true
  | .node (.raw `Lean.Parser.Termination.suffix) _ => true
  | _ => false

def treeStart? (tree : SyntaxTree.Tree) : Option String.Pos.Raw :=
  match tree.firstToken? with
  | some token => some token.span.start
  | none => none

def treeSourceText? (source : String) (tree : SyntaxTree.Tree) : Option String := do
  let first ← tree.firstToken?
  let last ← tree.lastToken?
  some <| SyntaxTree.sourceText source first.span.start last.span.stop

partial def missingRuleOccurrences
    (source : String) (fallbackStart? : Option String.Pos.Raw)
    : SyntaxTree.Tree → List MissingRuleOccurrence
  | .missing => []
  | .leaf _ => []
  | tree@(.node kind children) =>
      if missingRuleReportSkipsTree tree then
        []
      else
        let currentStart? := treeStart? tree <|> fallbackStart?
        let current :=
          match LineBreakRules.ruleFor tree with
          | some _ => []
          | none =>
              [{
                kind := SyntaxTree.nodeKindName kind
                line := currentStart?.map (lineNumberAt source ·) |>.getD 1
                treeText := (treeSourceText? source tree).getD ""
              }]
        current ++ children.toList.flatMap (missingRuleOccurrences source currentStart?)

def missingRuleOccurrencesForModule (moduleTree : SyntaxTree.Module)
    : List MissingRuleOccurrence :=
  missingRuleOccurrences moduleTree.source none moduleTree.tree

def isIgnoredWhitespace : Char → Bool
  | ' ' | '\t' | '\n' | '\r' => true
  | _ => false

def withoutIgnoredWhitespace (text : String) : String :=
  String.ofList <| text.toList.filter fun char => !isIgnoredWhitespace char

def preservesCodeIgnoringWhitespace (before after : String) : Bool :=
  withoutIgnoredWhitespace before == withoutIgnoredWhitespace after

def positionAfter (position : String.Pos.Raw) (text : String) : String.Pos.Raw :=
  String.Pos.Raw.mk (position.byteIdx + text.endPos.offset.byteIdx)

def tokenIntersects (start stop : String.Pos.Raw) (token : SyntaxTree.Token) : Bool :=
  token.span.start < stop && start < token.span.stop

def treeSpan? (tree : SyntaxTree.Tree) : Option SyntaxTree.Span := do
  let first ← tree.firstToken?
  let last ← tree.lastToken?
  some { start := first.span.start, stop := last.span.stop }

def atomicTreeSpan? (tree : SyntaxTree.Tree) : Option SyntaxTree.Span :=
  match tree with
  | .node (.raw `termS!_) _ => treeSpan? tree
  | _ =>
      match tree.tokens.toList.filter fun token => !token.lexeme.isEmpty with
      | [token] => some token.span
      | _ => none

def atomicWithCommaSpan? (atomicTree commaTree : SyntaxTree.Tree)
    : Option SyntaxTree.Span := do
  let .leaf comma := commaTree | none
  if comma.lexeme != "," then
    none
  else
    let atomicSpan ← atomicTreeSpan? atomicTree
    some { start := atomicSpan.start, stop := comma.span.stop }

def atomicWithCommaSpans : List SyntaxTree.Tree → List SyntaxTree.Span
  | atomicTree :: commaTree :: rest =>
      let current := atomicWithCommaSpan? atomicTree commaTree |>.toList
      current ++ atomicWithCommaSpans (commaTree :: rest)
  | _ => []

partial def indivisibleOverflowSpans : SyntaxTree.Tree → List SyntaxTree.Span
  | .missing | .leaf _ => []
  | tree@(.node kind children) =>
      let current :=
        if kind == .raw `termS!_ then
          treeSpan? tree |>.toList
        else
          []
      current
      ++ atomicWithCommaSpans children.toList
      ++ children.toList.flatMap indivisibleOverflowSpans

def spanCovers (start stop : String.Pos.Raw) (span : SyntaxTree.Span) : Bool :=
  span.start <= start && stop <= span.stop

def excludedOverflowLineEnders : List String :=
  [")", "]", "}", "⟩", "⟫", ",", ";"]

def tokensAreAdjacentAfter (position : String.Pos.Raw) : List SyntaxTree.Token → Bool
  | [] => true
  | token :: rest =>
      token.span.start == position && tokensAreAdjacentAfter token.span.stop rest

def spanWithLineEndersCovers
    (tokens : List SyntaxTree.Token)
    (overflowStart contentStop : String.Pos.Raw)
    (span : SyntaxTree.Span)
    : Bool :=
  if overflowStart < span.start || contentStop <= span.stop then
    spanCovers overflowStart contentStop span
  else
    let suffixTokens :=
      tokens.filter
        fun token =>
          span.stop <= token.span.start && token.span.start < contentStop
    match suffixTokens.getLast? with
    | none => false
    | some last =>
        tokensAreAdjacentAfter span.stop suffixTokens
        && (suffixTokens.all
              fun token =>
                excludedOverflowLineEnders.contains token.lexeme)
        && contentStop <= last.span.stop

def overflowIsExempt
    (tokens : List SyntaxTree.Token)
    (indivisibleSpans : List SyntaxTree.Span)
    (overflowStart contentStop : String.Pos.Raw)
    : Bool :=
  let suffixTokens := tokens.filter (tokenIntersects overflowStart contentStop)
  let indivisibleSpans :=
    indivisibleSpans.filter
      fun span =>
        span.start <= overflowStart && overflowStart < span.stop
  let atomicSpans := indivisibleSpans ++ suffixTokens.map (·.span)
  if atomicSpans.any
      (spanWithLineEndersCovers suffixTokens overflowStart contentStop) then
    true
  else
    suffixTokens.isEmpty

def overflowOccurrences (moduleTree : SyntaxTree.Module) : List OverflowOccurrence :=
  let tokens := realTokens moduleTree
  let indivisibleSpans := indivisibleOverflowSpans moduleTree.tree
  let rec loop (lineNumber : Nat) (lineStart : String.Pos.Raw)
      : List String → List OverflowOccurrence
    | [] => []
    | line :: rest =>
        let nextLineStart := positionAfter lineStart (line ++ "\n")
        let remaining := loop (lineNumber + 1) nextLineStart rest
        let overflowStart := positionAfter lineStart (line.take maxLineWidth).toString
        let contentStop := positionAfter lineStart line.trimAsciiEnd.toString
        if maxLineWidth < line.length
            && !overflowIsExempt tokens indivisibleSpans overflowStart contentStop then
          { line := lineNumber, width := line.length, text := line } :: remaining
        else
          remaining
  loop 1 0 (moduleTree.source.splitOn "\n")

def formattingExceptions (sourceModule formattedModule : SyntaxTree.Module)
    : List FormattingException :=
  let codeExceptions :=
    if preservesCodeIgnoringWhitespace sourceModule.source formattedModule.source then
      []
    else
      [.codeChanged]
  let overflowExceptions :=
    (overflowOccurrences formattedModule).map FormattingException.lineOverflow
  let missingRuleExceptions :=
    (missingRuleOccurrencesForModule sourceModule).map FormattingException.missingRule
  codeExceptions ++ overflowExceptions ++ missingRuleExceptions

end Diagnostics
end Formatter
end LeanFmt
