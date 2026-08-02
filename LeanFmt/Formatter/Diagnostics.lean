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
  syntaxKind? : Option SyntaxNodeKind
  line : Nat
  treeText : String
deriving BEq, Repr

inductive LeanFormatterAvailability where
  | registered
  | parserDescription
  | unavailable
deriving BEq, Inhabited, Repr

def LeanFormatterAvailability.description : LeanFormatterAvailability → String
  | .registered => "registered formatter"
  | .parserDescription => "parser description"
  | .unavailable => "no formatter metadata"

def syntaxNodeKind? : SyntaxTree.NodeKind → Option SyntaxNodeKind
  | .raw kind => some kind
  | .letExpression kind _ => some kind
  | _ => none

unsafe def leanFormatterAvailabilityUnsafe
    (env : Environment) (kind? : Option SyntaxNodeKind)
    : LeanFormatterAvailability :=
  match kind? with
  | none => .unavailable
  | some kind =>
      if !(KeyedDeclsAttribute.getValues
            PrettyPrinter.formatterAttribute env kind).isEmpty then
        .registered
      else
        match env.find? kind with
        | some info =>
            if info.type.isConstOf ``ParserDescr
                || info.type.isConstOf ``TrailingParserDescr then
              .parserDescription
            else
              .unavailable
        | none => .unavailable

@[implemented_by leanFormatterAvailabilityUnsafe]
opaque leanFormatterAvailability
  (env : Environment) (kind? : Option SyntaxNodeKind) : LeanFormatterAvailability

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

def sourceLexicalTokens (moduleTree : SyntaxTree.Module) : Array SyntaxTree.Token :=
  (moduleTree.tokens.filter
    fun token => SyntaxTree.tokenComesFromSource moduleTree.source token)
  |>.qsort fun left right => left.span.start < right.span.start

def realTokens (moduleTree : SyntaxTree.Module) : List SyntaxTree.Token :=
  (sourceLexicalTokens moduleTree).toList.filter fun token => !token.lexeme.isEmpty

def isApplicationArgumentStart (token : SyntaxTree.Token) : Bool :=
  token.role == .ident || SpaceRules.stringIn token.lexeme ["(", "[", "{", "⟨", "⟪", "."]

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

def missingRuleReportSkipsTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.byTactic') _ => true
  | tree => OriginalTree.shouldEmit tree

def missingRuleReportIgnoresTermNotationKindName (kindName : String) : Bool :=
  kindName.startsWith "term"
  || SpaceRules.containsSubstring kindName ".term"
  || kindName.startsWith "«term"
  || SpaceRules.containsSubstring kindName ".«term"

def missingRuleReportIgnoresKindName (kindName : String) : Bool :=
  kindName.startsWith "token."
  || kindName.startsWith "_private."
  || missingRuleReportIgnoresTermNotationKindName kindName
  || kindName.startsWith "«stx"
  || SpaceRules.containsSubstring kindName ".«stx"
  || kindName.startsWith "Lean.Elab.Command.command_"

def treeStart? (tree : SyntaxTree.Tree) : Option String.Pos.Raw :=
  match tree.firstToken? with
  | some token => some token.span.start
  | none => none

def treeSourceText? (source : String) (tree : SyntaxTree.Tree) : Option String := do
  let first ← tree.firstToken?
  let last ← tree.lastToken?
  some <| SyntaxTree.sourceText source first.span.start last.span.stop

private partial def missingRuleOccurrencesWith
    (sourceMap : SyntaxTree.SourcePositionMap)
    (fallbackStart? : Option String.Pos.Raw)
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
              let kindName := SyntaxTree.nodeKindName kind
              if missingRuleReportIgnoresKindName kindName then
                []
              else
                [{
                  kind := kindName
                  syntaxKind? := syntaxNodeKind? kind
                  line := currentStart?.map sourceMap.lineNumberAt |>.getD 1
                  treeText := (treeSourceText? sourceMap.source tree).getD ""
                }]
        current
        ++ children.toList.flatMap (missingRuleOccurrencesWith sourceMap currentStart?)

def missingRuleOccurrences
    (source : String) (fallbackStart? : Option String.Pos.Raw)
    (tree : SyntaxTree.Tree)
    : List MissingRuleOccurrence :=
  missingRuleOccurrencesWith (SyntaxTree.SourcePositionMap.ofString source)
    fallbackStart? tree

def missingRuleOccurrencesForModule (moduleTree : SyntaxTree.Module)
    : List MissingRuleOccurrence :=
  missingRuleOccurrencesWith
    (SyntaxTree.SourcePositionMap.ofString moduleTree.source) none moduleTree.tree

def treeSpan? (tree : SyntaxTree.Tree) : Option SyntaxTree.Span := do
  let first ← tree.firstToken?
  let last ← tree.lastToken?
  some { start := first.span.start, stop := last.span.stop }

inductive PreservationFragment where
  | code (text : String)
  | comment (text normalizedIndent : String)
  | space
deriving Repr

instance : BEq PreservationFragment where
  beq
    | .code before, .code after => before == after
    | .comment before beforeNormalized, .comment after afterNormalized =>
        before == after || beforeNormalized == afterNormalized
    | .space, .space => true
    | _, _ => false

structure PreservationFragmentMismatch where
  index : Nat
  before? : Option PreservationFragment
  after? : Option PreservationFragment
deriving Repr

partial def firstPreservationFragmentMismatch?
    (before after : List PreservationFragment) (index : Nat := 0)
    : Option PreservationFragmentMismatch :=
  match before, after with
  | [], [] => none
  | beforeHead :: beforeTail, afterHead :: afterTail =>
      if beforeHead == afterHead then
        firstPreservationFragmentMismatch? beforeTail afterTail (index + 1)
      else
        some { index, before? := some beforeHead, after? := some afterHead }
  | beforeHead :: _, [] =>
      some { index, before? := some beforeHead, after? := none }
  | [], afterHead :: _ =>
      some { index, before? := none, after? := some afterHead }

/-- A syntax-tree representation that omits source positions and other source metadata. -/
inductive SyntaxSignature where
  | missing
  | atom (value : String)
  | ident (rawValue : String) (value : Name)
  | node (kind : SyntaxNodeKind) (children : Array SyntaxSignature)
deriving BEq, Inhabited, Repr

/-- Converts Lean syntax into the source-information-free form used by preservation checks. -/
def SyntaxSignature.isEmptyNull : SyntaxSignature → Bool
  | .node `null children => children.isEmpty
  | _ => false

def isSyntaxCommentKind (kind : SyntaxNodeKind) : Bool :=
  kind == `Lean.Parser.Command.moduleDoc || kind == `Lean.Parser.Command.docComment

partial def syntaxSignature : Syntax → SyntaxSignature
  | .missing => .missing
  | .atom _ value => .atom value
  | .ident _ rawValue value _ => .ident rawValue.toString value
  | .node _ kind children =>
      if isSyntaxCommentKind kind then
        .node kind #[]
      else
        .node kind
        <| (children.map syntaxSignature).filter fun child => !child.isEmptyNull

partial def takeLineCommentAux (reversed : List Char) : List Char → List Char × List Char
  | [] => (reversed.reverse, [])
  | chars@('\n' :: _) => (reversed.reverse, chars)
  | chars@('\r' :: _) => (reversed.reverse, chars)
  | char :: rest => takeLineCommentAux (char :: reversed) rest

partial def takeBlockCommentAux (depth : Nat) (reversed : List Char)
    : List Char → List Char × List Char
  | [] => (reversed.reverse, [])
  | '/' :: '-' :: rest =>
      takeBlockCommentAux (depth + 1) ('-' :: '/' :: reversed) rest
  | '-' :: '/' :: rest =>
      let reversed := '/' :: '-' :: reversed
      if depth == 1 then
        (reversed.reverse, rest)
      else
        takeBlockCommentAux (depth - 1) reversed rest
  | char :: rest => takeBlockCommentAux depth (char :: reversed) rest

def normalizeBlockCommentIndent (openingColumn : Nat) (comment : String) : String :=
  match (SpaceRules.normalizeLineEndings comment).splitOn "\n" with
  | [] | [_] => comment
  | first :: rest =>
      let normalizedRest :=
        rest.map
          fun line =>
            if line.isEmpty then
              ""
            else
              let stripped := SpaceRules.stripLeadingHorizontalWhitespace line
              let indentation := line.length - stripped.length
              let relativeIndent := Int.ofNat indentation - Int.ofNat openingColumn
              s!"{relativeIndent}:{stripped}"
      String.intercalate "\n" (first :: normalizedRest)

def preservationComment (openingColumn : Nat) (comment : String) : PreservationFragment :=
  if comment.startsWith "/-" then
    .comment comment (normalizeBlockCommentIndent openingColumn comment)
  else
    .comment comment comment

def columnAfterText (column : Nat) (text : String) : Nat :=
  text.toList.foldl
    (fun column char =>
      if char == '\n' || char == '\r' then 0 else column + 1)
    column

partial def commentFragmentsAux (column : Nat) (reversed : List PreservationFragment)
    : List Char → List PreservationFragment
  | [] => reversed.reverse
  | '-' :: '-' :: rest =>
      let (comment, rest) := takeLineCommentAux ['-', '-'] rest
      let comment := String.ofList comment
      commentFragmentsAux
        (columnAfterText column comment)
        (preservationComment column comment :: reversed) rest
  | '/' :: '-' :: rest =>
      let (comment, rest) := takeBlockCommentAux 1 ['-', '/'] rest
      let comment := String.ofList comment
      commentFragmentsAux
        (columnAfterText column comment)
        (preservationComment column comment :: reversed) rest
  | char :: rest =>
      let column := if char == '\n' || char == '\r' then 0 else column + 1
      commentFragmentsAux column reversed rest

def commentFragments (trivia : String) (startColumn : Nat := 0)
    : List PreservationFragment :=
  commentFragmentsAux startColumn [] trivia.toList

partial def syntaxCommentSpans : SyntaxTree.Tree → List SyntaxTree.Span
  | .missing | .leaf _ => []
  | tree@(.node (.raw kind) children) =>
      if isSyntaxCommentKind kind then
        treeSpan? tree |>.toList
      else
        children.toList.flatMap syntaxCommentSpans
  | .node _ children => children.toList.flatMap syntaxCommentSpans

def commentSpanForToken? (spans : List SyntaxTree.Span) (token : SyntaxTree.Token)
    : Option SyntaxTree.Span :=
  spans.find? fun span => span.start <= token.span.start && token.span.stop <= span.stop

def preservationFragments (moduleTree : SyntaxTree.Module) : List PreservationFragment :=
  let tokens := (sourceLexicalTokens moduleTree).toList
  let syntaxCommentSpans := syntaxCommentSpans moduleTree.tree
  let (fragments, consumedUntil, consumedColumn) :=
    tokens.foldl
      (fun (fragments, consumedUntil, consumedColumn) token =>
        if token.span.stop <= consumedUntil then
          (fragments, consumedUntil, consumedColumn)
        else
          match commentSpanForToken? syntaxCommentSpans token with
          | some span =>
              let leadingText :=
                if consumedUntil < span.start then
                  SyntaxTree.sourceText moduleTree.source consumedUntil span.start
                else
                  ""
              let leading := commentFragments leadingText consumedColumn
              let commentColumn := columnAfterText consumedColumn leadingText
              let commentText :=
                SyntaxTree.sourceText moduleTree.source span.start span.stop
              let fragments :=
                (leading.foldl (fun fragments fragment => fragments.push fragment)
                    fragments)
                  |>.push
                <| preservationComment commentColumn commentText
              (fragments, span.stop, columnAfterText commentColumn commentText)
          | none =>
              let leadingText :=
                if consumedUntil < token.span.start then
                  SyntaxTree.sourceText moduleTree.source consumedUntil token.span.start
                else
                  ""
              let leading := commentFragments leadingText consumedColumn
              let fragments :=
                leading.foldl (fun fragments fragment => fragments.push fragment)
                  fragments
              let fragments :=
                if token.lexeme.isEmpty then
                  fragments
                else
                  fragments.push (.code token.lexeme)
              let tokenColumn := columnAfterText consumedColumn leadingText
              (fragments, token.span.stop, columnAfterText tokenColumn token.lexeme))
      (#[], 0, 0)
  let trailingSource :=
    SyntaxTree.sourceText moduleTree.source consumedUntil moduleTree.source.endPos.offset
  (fragments.toList ++ commentFragments trailingSource consumedColumn).intersperse .space

/-- Checks whether two modules have the same parsed syntax after discarding source metadata. -/
def preservesSyntaxIgnoringSourceInfo (before after : SyntaxTree.Module) : Bool :=
  syntaxSignature before.rawSyntax == syntaxSignature after.rawSyntax

def preservesCodeIgnoringWhitespace (before after : SyntaxTree.Module) : Bool :=
  preservationFragments before == preservationFragments after
  && preservesSyntaxIgnoringSourceInfo before after

def positionAfter (position : String.Pos.Raw) (text : String) : String.Pos.Raw :=
  String.Pos.Raw.mk (position.byteIdx + text.endPos.offset.byteIdx)

partial def preservedOriginalSpans : SyntaxTree.Tree → List SyntaxTree.Span
  | .missing | .leaf _ => []
  | tree@(.node _ children) =>
      if OriginalTree.shouldEmit tree then
        treeSpan? tree |>.toList
      else
        children.toList.flatMap preservedOriginalSpans

partial def unbreakableOriginalSpans : SyntaxTree.Tree → List SyntaxTree.Span
  | .missing | .leaf _ => []
  | tree@(.node _ children) =>
      if (OriginalTree.classify? tree).any
          OriginalTree.LayoutIslandKind.hasUnbreakableLineLayout then
        treeSpan? tree |>.toList
      else
        children.toList.flatMap unbreakableOriginalSpans

def tokenIntersects (start stop : String.Pos.Raw) (token : SyntaxTree.Token) : Bool :=
  token.span.start < stop && start < token.span.stop

def isAtomicTree (tree : SyntaxTree.Tree) : Bool :=
  match LineBreakRules.ruleFor tree with
  | some rule => rule.atomic
  | none => false

def atomicTreeSpan? (tree : SyntaxTree.Tree) : Option SyntaxTree.Span :=
  if isAtomicTree tree then
    treeSpan? tree
  else
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
  | tree@(.node _ children) =>
      let current :=
        if isAtomicTree tree then
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
    (allowMovableLayoutExemptions : Bool)
    (lineWidth contentWidth : Nat)
    (overflowStart contentStop : String.Pos.Raw)
    : Bool :=
  let suffixTokens := tokens.filter (tokenIntersects overflowStart contentStop)
  let indivisibleSpans :=
    indivisibleSpans.filter
      fun span =>
        span.start <= overflowStart
  let unbreakableTokenSpans :=
    suffixTokens.filter (fun token => lineWidth < token.lexeme.length) |>.map (·.span)
  let isolatedTokenSpans :=
    match suffixTokens with
    | first :: _ =>
        let suffixWidth :=
          suffixTokens.foldl (fun width token => width + token.lexeme.length) 0
        if suffixWidth == contentWidth then [first.span] else []
    | [] => []
  let movableSpans :=
    if allowMovableLayoutExemptions then
      indivisibleSpans ++ isolatedTokenSpans
    else
      []
  let atomicSpans := movableSpans ++ unbreakableTokenSpans
  if atomicSpans.any (spanWithLineEndersCovers tokens overflowStart contentStop) then
    true
  else
    suffixTokens.isEmpty && lineWidth < contentWidth

private def overflowOccurrencesWith
    (moduleTree : SyntaxTree.Module) (options : Options)
    (allowMovableLayoutExemptions : Bool)
    : List OverflowOccurrence :=
  let tokens := realTokens moduleTree
  let indivisibleSpans :=
    if allowMovableLayoutExemptions then
      preservedOriginalSpans moduleTree.tree ++ indivisibleOverflowSpans moduleTree.tree
    else
      []
  let rec loop (lineNumber : Nat) (lineStart : String.Pos.Raw)
      : List String → List OverflowOccurrence
    | [] => []
    | line :: rest =>
        let nextLineStart := positionAfter lineStart (line ++ "\n")
        let remaining := loop (lineNumber + 1) nextLineStart rest
        let overflowStart :=
          positionAfter lineStart (line.take options.lineWidth).toString
        let contentStop := positionAfter lineStart line.trimAsciiEnd.toString
        let contentWidth :=
          line.toList.dropWhile (fun char => char == ' ' || char == '\t') |>.length
        if options.lineWidth < line.length
            && !overflowIsExempt tokens indivisibleSpans
                  allowMovableLayoutExemptions options.lineWidth contentWidth
                  overflowStart contentStop then
          { line := lineNumber, width := line.length, text := line } :: remaining
        else
          remaining
  loop 1 0 (moduleTree.source.splitOn "\n")

def overflowOccurrences (moduleTree : SyntaxTree.Module) (options : Options := {})
    : List OverflowOccurrence :=
  overflowOccurrencesWith moduleTree options true

def lineWidthAtToken?
    (sourceMap : SyntaxTree.SourcePositionMap) (token : SyntaxTree.Token)
    : Option Nat :=
  let lineNumber := sourceMap.lineNumberAt token.span.start
  let fileMap := sourceMap.fileMap
  let line :=
    SyntaxTree.sourceText sourceMap.source
      (fileMap.lineStart lineNumber) (fileMap.lineStart (lineNumber + 1))
  (SpaceRules.normalizeLineEndings line).splitOn "\n" |>.head? |>.map (·.length)

def isolatedOverflowTokenIndex?
    (sourceMap : SyntaxTree.SourcePositionMap) (tokens : List SyntaxTree.Token)
    (occurrence : OverflowOccurrence)
    : Option Nat :=
  let text := occurrence.text.trimAscii
  let matching :=
    tokens.zipIdx.filter
      fun (token, _) =>
        token.lexeme == text && sourceMap.lineNumberAt token.span.start == occurrence.line
  match matching with
  | [(_, index)] => some index
  | _ => none

def isolatedTokenSourceLineOverflowed
    (sourceMap formattedMap : SyntaxTree.SourcePositionMap)
    (sourceTokens formattedTokens : List SyntaxTree.Token)
    (occurrence : OverflowOccurrence) (lineWidth : Nat)
    : Bool :=
  match isolatedOverflowTokenIndex? formattedMap formattedTokens occurrence with
  | none => false
  | some index =>
      match sourceTokens[index]? with
      | none => false
      | some sourceToken =>
          lineWidthAtToken? sourceMap sourceToken |>.any (lineWidth < ·)

def sourceCommentLineTexts (moduleTree : SyntaxTree.Module) : List String :=
  (preservationFragments moduleTree).flatMap
    fun
    | .comment text _ =>
        (SpaceRules.normalizeLineEndings text).splitOn "\n"
        |>.map (·.trimAscii.toString)
        |>.filter fun line => !line.isEmpty
    | _ => []

def commentOnlyOverflowMatchesSource
    (formattedMap : SyntaxTree.SourcePositionMap)
    (formattedTokens : List SyntaxTree.Token)
    (sourceCommentLineTexts : List String)
    (occurrence : OverflowOccurrence)
    : Bool :=
  let lineStart := formattedMap.fileMap.lineStart occurrence.line
  let contentStop := positionAfter lineStart occurrence.text.trimAsciiEnd.toString
  !formattedTokens.any (tokenIntersects lineStart contentStop)
  && sourceCommentLineTexts.contains occurrence.text.trimAscii.toString

def atomicSyntaxSourceLineOverflowed
    (sourceMap formattedMap : SyntaxTree.SourcePositionMap)
    (sourceTokens formattedTokens : List SyntaxTree.Token)
    (formattedAtomicSpans : List SyntaxTree.Span)
    (occurrence : OverflowOccurrence) (lineWidth : Nat)
    : Bool :=
  let lineStart := formattedMap.fileMap.lineStart occurrence.line
  let overflowStart := positionAfter lineStart (occurrence.text.take lineWidth).toString
  let contentStop := positionAfter lineStart occurrence.text.trimAsciiEnd.toString
  let span? :=
    formattedAtomicSpans.find?
      (spanWithLineEndersCovers formattedTokens overflowStart contentStop)
  match span? with
  | none => false
  | some span =>
      let indexes :=
        formattedTokens.zipIdx.filterMap
          fun (token, index) =>
            if span.start <= token.span.start
                && token.span.stop <= span.stop
                && tokenIntersects lineStart contentStop token then
              some index
            else
              none
      match indexes.head?, indexes.getLast? with
      | some firstIndex, some lastIndex =>
          match sourceTokens[firstIndex]?, sourceTokens[lastIndex]? with
          | some firstToken, some lastToken =>
              sourceMap.lineNumberAt firstToken.span.start
                == sourceMap.lineNumberAt lastToken.span.start
              && (lineWidthAtToken? sourceMap firstToken).any (lineWidth < ·)
          | _, _ => false
      | _, _ => false

def overflowCoveredBySpans
    (formattedMap : SyntaxTree.SourcePositionMap)
    (formattedTokens : List SyntaxTree.Token)
    (spans : List SyntaxTree.Span)
    (occurrence : OverflowOccurrence) (lineWidth : Nat)
    : Bool :=
  let lineStart := formattedMap.fileMap.lineStart occurrence.line
  let overflowStart := positionAfter lineStart (occurrence.text.take lineWidth).toString
  let contentStop := positionAfter lineStart occurrence.text.trimAsciiEnd.toString
  spans.any (spanWithLineEndersCovers formattedTokens overflowStart contentStop)

def formattingExceptions (sourceModule formattedModule : SyntaxTree.Module)
    (options : Options := {})
    : List FormattingException :=
  let codeExceptions :=
    if preservesCodeIgnoringWhitespace sourceModule formattedModule then
      []
    else
      [.codeChanged]
  let overflowExceptions :=
    let formattedOccurrences := overflowOccurrencesWith formattedModule options false
    if formattedOccurrences.isEmpty then
      []
    else
      let sourceMap := SyntaxTree.SourcePositionMap.ofString sourceModule.source
      let formattedMap := SyntaxTree.SourcePositionMap.ofString formattedModule.source
      let sourceTokens := realTokens sourceModule
      let formattedTokens := realTokens formattedModule
      let formattedAtomicSpans := indivisibleOverflowSpans formattedModule.tree
      let formattedUnbreakableOriginalSpans :=
        unbreakableOriginalSpans formattedModule.tree
      let sourceOverflowTexts :=
        (overflowOccurrencesWith sourceModule options false).map
          fun occurrence =>
            occurrence.text.trimAscii
      let sourceCommentLineTexts := sourceCommentLineTexts sourceModule
      formattedOccurrences.filterMap
        fun occurrence =>
          if overflowCoveredBySpans formattedMap formattedTokens
                formattedUnbreakableOriginalSpans occurrence options.lineWidth
              || sourceOverflowTexts.contains occurrence.text.trimAscii
              || commentOnlyOverflowMatchesSource formattedMap formattedTokens
                  sourceCommentLineTexts occurrence
              || isolatedTokenSourceLineOverflowed sourceMap formattedMap
                  sourceTokens formattedTokens occurrence options.lineWidth then
            none
          else if atomicSyntaxSourceLineOverflowed sourceMap formattedMap
                    sourceTokens formattedTokens formattedAtomicSpans occurrence
                    options.lineWidth then
            none
          else
            some <| FormattingException.lineOverflow occurrence
  let missingRuleExceptions :=
    (missingRuleOccurrencesForModule sourceModule).map FormattingException.missingRule
  codeExceptions ++ overflowExceptions ++ missingRuleExceptions

end Diagnostics
end Formatter
end LeanFmt
