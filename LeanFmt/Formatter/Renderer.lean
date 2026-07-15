import LeanFmt.Formatter.LineBreakRules
import LeanFmt.Formatter.SpaceRules
import LeanFmt.Formatter.Trace

namespace LeanFmt
namespace Formatter

/-! ## Output and indentation state -/

def maxLineWidth : Nat :=
  88

def indentationSpaces : Nat :=
  2

def lineWidth (text : String) : Nat :=
  text.length

def lineFits (text : String) : Bool :=
  lineWidth text <= maxLineWidth

def linesFit (text : String) : Bool :=
  (SpaceRules.normalizeLineEndings text).splitOn "\n" |>.all lineFits

def lineFitsWithTrailingWidth (line : String) (trailingWidth : Nat) : Bool :=
  lineWidth line + trailingWidth <= maxLineWidth

def linesFitWithTrailingWidth (text : String) (trailingWidth : Nat) : Bool :=
  let rec loop : List String → Bool
    | [] => trailingWidth <= maxLineWidth
    | [line] => lineFitsWithTrailingWidth line trailingWidth
    | line :: rest => lineFits line && loop rest
  loop <| (SpaceRules.normalizeLineEndings text).splitOn "\n"

def spaces (count : Nat) : String :=
  String.ofList <| List.replicate count ' '

def indentationLevelForColumn (column : Nat) : Nat :=
  column / indentationSpaces

def indentationPastColumn (column : Nat) : Nat :=
  indentationLevelForColumn (column + indentationSpaces - 1) * indentationSpaces

def leadingWhitespace (line : String) : String :=
  (line.takeWhile SpaceRules.isHorizontalWhitespace).toString

def hasLineBreakChar (text : String) : Bool :=
  text.contains '\n' || text.contains '\r'

structure AppendedLines where
  lineBreakCount : Nat
  completedLineOverflowCount : Nat
  currentLine : String

def appendedLines (currentLine text : String) : AppendedLines :=
  let rec loop (lineWidth breakCount overflowCount : Nat) (current : List Char)
      : List Char → AppendedLines
    | [] =>
        {
          lineBreakCount := breakCount
          completedLineOverflowCount := overflowCount
          currentLine := String.ofList current.reverse
        }
    | '\r' :: '\n' :: rest =>
        loop 0 (breakCount + 1)
          (overflowCount + if lineWidth > maxLineWidth then 1 else 0) [] rest
    | '\n' :: rest =>
        loop 0 (breakCount + 1)
          (overflowCount + if lineWidth > maxLineWidth then 1 else 0) [] rest
    | '\r' :: rest =>
        loop 0 (breakCount + 1)
          (overflowCount + if lineWidth > maxLineWidth then 1 else 0) [] rest
    | char :: rest =>
        loop (lineWidth + 1) breakCount overflowCount (char :: current) rest
  loop currentLine.length 0 0 [] text.toList

def charsAfterLastNewline (text : String) : String :=
  let rec loop : List Char → List Char → String
    | [], current => String.ofList current.reverse
    | '\n' :: rest, _ => loop rest []
    | char :: rest, current => loop rest (char :: current)
  loop (SpaceRules.normalizeLineEndings text).toList []

def currentLineIndent (text : String) : Nat :=
  (leadingWhitespace (charsAfterLastNewline text)).length

def hasBlankLineStructure (text : String) : Bool :=
  hasLineBreakChar text
  && SpaceRules.containsSubstring (SpaceRules.normalizeLineEndings text) "\n\n"

def originalColumnAt (source : String) (position : String.Pos.Raw) : Nat :=
  lineWidth <| charsAfterLastNewline <| SyntaxTree.sourceText source 0 position

def shiftLineIndent (sourceColumn targetColumn : Nat) (line : String) : String :=
  if line.isEmpty then
    line
  else if sourceColumn <= targetColumn then
    spaces (targetColumn - sourceColumn) ++ line
  else
    let removeCount := min (sourceColumn - targetColumn) (leadingWhitespace line).length
    (line.drop removeCount).toString

def adjustOriginalTextIndent (sourceColumn targetColumn : Nat) (text : String)
    : String :=
  match (SpaceRules.normalizeLineEndings text).splitOn "\n" with
  | [] => text
  | first :: rest =>
      String.intercalate "\n"
      <| first :: rest.map (shiftLineIndent sourceColumn targetColumn)

structure SourceBreak where
  index : Nat
  indent : Nat
deriving BEq, Repr

structure RenderState where
  source : String
  output : String := ""
  outputLineBreakCount : Nat := 0
  completedLineOverflowCount : Nat := 0
  currentLine : String := ""
  lastToken? : Option SyntaxTree.Token := none
  pendingIndent? : Option Nat := none
  segmentBaseColumn : Nat := 0
  segmentIndentation : Nat := 0
  infixLeftDepth : Nat := 0
  lineFitSuffixWidth : Nat := 0
  context : LineBreakRules.RuleContext := {}
  trace : Trace.State := {}
deriving Repr

structure SegmentBase where
  column : Nat
  indentation : Nat
deriving Repr

structure ChildRenderScope where
  context : LineBreakRules.RuleContext
  segmentBaseColumn : Nat
  segmentIndentation : Nat
  lineFitSuffixWidth : Nat
  trace : Trace.State

def ChildRenderScope.capture (state : RenderState) : ChildRenderScope :=
  {
    context := state.context
    segmentBaseColumn := state.segmentBaseColumn
    segmentIndentation := state.segmentIndentation
    lineFitSuffixWidth := state.lineFitSuffixWidth
    trace := state.trace
  }

def ChildRenderScope.restore (scope : ChildRenderScope) (rendered : RenderState)
    : RenderState :=
  {
    rendered with
      context := scope.context
      segmentBaseColumn := scope.segmentBaseColumn
      segmentIndentation := scope.segmentIndentation
      lineFitSuffixWidth := scope.lineFitSuffixWidth
      trace := rendered.trace.restorePathFrom scope.trace
  }

def currentLineAfterAppend (currentLine text : String) : String :=
  if hasLineBreakChar text then
    charsAfterLastNewline text
  else
    currentLine ++ text

def RenderState.appendOutput (state : RenderState) (text : String) : RenderState :=
  if hasLineBreakChar text then
    let appended := appendedLines state.currentLine text
    {
      state with
        output := state.output ++ text
        outputLineBreakCount := state.outputLineBreakCount + appended.lineBreakCount
        completedLineOverflowCount :=
          state.completedLineOverflowCount + appended.completedLineOverflowCount
        currentLine := appended.currentLine
    }
  else
    {
      state with
        output := state.output ++ text
        currentLine := state.currentLine ++ text
    }

def segmentFirstToken? (segment : LineBreakRules.Segment) : Option SyntaxTree.Token :=
  match segment.parent with
  | .leaf token => if token.lexeme.isEmpty then none else some token
  | .missing => none
  | .node _ _ =>
      segment.indexes.foldl
        (fun found index =>
          match found with
          | some token => some token
          | none =>
              match segment.child? index with
              | some child => SyntaxTree.Tree.firstToken? child
              | none => none)
        none

def RenderState.currentColumn (state : RenderState) : Nat :=
  match state.pendingIndent? with
  | some indent => indent
  | none => lineWidth state.currentLine

def RenderState.currentIndent (state : RenderState) : Nat :=
  match state.pendingIndent? with
  | some indent => indent
  | none => (leadingWhitespace state.currentLine).length

def RenderState.segmentBaseIndent (state : RenderState) : Nat :=
  state.segmentIndentation * indentationSpaces

def RenderState.defaultWhitespace (state : RenderState) (token : SyntaxTree.Token)
    (preserveLines : Bool := false)
    : String :=
  match state.lastToken?, state.pendingIndent? with
  | some left, some indent =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop token.span.start
      let indentation := spaces indent
      if SpaceRules.hasCommentStart trivia then
        SpaceRules.commentTriviaForBreak trivia indentation
      else if hasBlankLineStructure trivia then
        "\n\n" ++ indentation
      else
        "\n" ++ indentation
  | none, some indent =>
      let indentation := spaces indent
      if SpaceRules.hasCommentStart token.leading.text then
        SpaceRules.commentTriviaForBreak token.leading.text indentation
      else if hasBlankLineStructure token.leading.text then
        "\n\n" ++ indentation
      else
        "\n" ++ indentation
  | none, none =>
      if SpaceRules.hasCommentStart token.leading.text then
        SpaceRules.reindentCommentTrivia token.leading.text ""
      else
        ""
  | some left, none =>
      SpaceRules.interTokenWhitespace state.source left token preserveLines

def RenderState.segmentStartColumn (state : RenderState)
    (segment : LineBreakRules.Segment)
    : Nat :=
  match segmentFirstToken? segment with
  | some token =>
      let whitespace := state.defaultWhitespace token
      lineWidth <| currentLineAfterAppend state.currentLine whitespace
  | none => state.currentColumn

def RenderState.traceSegment
    (state : RenderState) (segment : LineBreakRules.Segment) (ruleName : String)
    : RenderState :=
  {
    state with
      trace :=
        state.trace.recordSegment state.output
          (fun token => state.defaultWhitespace token) segment ruleName
          (state.segmentStartColumn segment) state.currentIndent
          state.segmentIndentation state.pendingIndent? state.infixLeftDepth
  }

def RenderState.nextTokenColumn (state : RenderState) (token : SyntaxTree.Token)
    (preserveLines : Bool := false)
    : Nat :=
  let whitespace := state.defaultWhitespace token preserveLines
  lineWidth <| currentLineAfterAppend state.currentLine whitespace

def RenderState.emitToken (state : RenderState) (token : SyntaxTree.Token)
    (preserveLines : Bool := false)
    : RenderState :=
  if token.lexeme.isEmpty then
    state
  else
    {
      state.appendOutput
          (state.defaultWhitespace token preserveLines ++ token.lexeme) with
        lastToken? := some token
        pendingIndent? := none
    }

def RenderState.withPendingIndent (state : RenderState) (indent : Nat) : RenderState :=
  {
    state with
      pendingIndent? := some indent
      infixLeftDepth := 0
      segmentBaseColumn := indent
      segmentIndentation := indentationLevelForColumn indent
  }

def breakIndent
    (baseColumn baseIndentation infixDepth : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : Nat :=
  let addedLevels := infixDepth + breakPoint.indentLevels
  if addedLevels == 0 then
    indentationPastColumn baseColumn
  else
    (baseIndentation + addedLevels) * indentationSpaces

def RenderState.withRuleBreakIndent
    (state : RenderState) (baseColumn baseIndentation infixDepth : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : RenderState :=
  state.withPendingIndent
  <| breakIndent baseColumn baseIndentation infixDepth breakPoint

def outputIntroducedLineBreak (before after : RenderState) : Bool :=
  before.outputLineBreakCount < after.outputLineBreakCount

def renderedCandidateFits (before after : RenderState) : Bool :=
  before.completedLineOverflowCount == after.completedLineOverflowCount
  && lineFitsWithTrailingWidth after.currentLine after.lineFitSuffixWidth

def RenderState.segmentStartBaseFor
    (state : RenderState) (segment : LineBreakRules.Segment)
    : SegmentBase :=
  let column :=
    match segmentFirstToken? segment with
    | some token => state.nextTokenColumn token
    | none => state.currentColumn
  { column, indentation := indentationLevelForColumn column }

def RenderState.preserveBlankBoundaryBefore
    (state : RenderState) (tree : SyntaxTree.Tree)
    : RenderState :=
  match state.lastToken?, state.pendingIndent?, SyntaxTree.Tree.firstToken? tree with
  | some left, none, some right =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop right.span.start
      if hasBlankLineStructure trivia && !SpaceRules.hasCommentStart trivia then
        { state.appendOutput (SpaceRules.cleanTrivia trivia) with lastToken? := none }
      else
        state
  | _, _, _ => state

def renderedTreeIsMultiline (before after : RenderState) (tree : SyntaxTree.Tree)
    : Bool :=
  let prepared := before.preserveBlankBoundaryBefore tree
  let leadingBreakCount :=
    prepared.outputLineBreakCount - before.outputLineBreakCount
    + match SyntaxTree.Tree.firstToken? tree with
      | some token =>
          let whitespace := prepared.defaultWhitespace token
          if hasLineBreakChar whitespace then
            (appendedLines "" whitespace).lineBreakCount
          else
            0
      | none => 0
  before.outputLineBreakCount + leadingBreakCount < after.outputLineBreakCount

def RenderState.hasBlankBoundaryBefore (state : RenderState) (tree : SyntaxTree.Tree)
    : Bool :=
  match state.lastToken?, SyntaxTree.Tree.firstToken? tree with
  | some left, some right =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop right.span.start
      hasBlankLineStructure trivia
  | _, _ => false

def isProofTree (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Term.byTactic) _ => true
  | .node (.raw `Lean.Parser.Termination.suffix) _ =>
      (SyntaxTree.Tree.firstToken? tree).isSome
  | _ => false

def isQuotationTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.quot) _ => true
  | _ => false

def isLayoutSensitiveCommand : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Command.macro_rules) _ => true
  | _ => false

def isSyntaxCommentTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Command.moduleDoc) _ => true
  | .node (.raw `Lean.Parser.Command.docComment) _ => true
  | _ => false

partial def containsProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      isProofTree tree || children.any containsProofTree

def isDefinitionContainingProof (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node .definition _ => containsProofTree tree
  | .node (.raw `Lean.Parser.Command.definition) _ => containsProofTree tree
  | .node (.raw `Lean.Parser.Command.abbrev) _ => containsProofTree tree
  | _ => false

def shouldEmitOriginalTree (tree : SyntaxTree.Tree) : Bool :=
  isProofTree tree
  || isDefinitionContainingProof tree
  || isQuotationTree tree
  || isLayoutSensitiveCommand tree
  || isSyntaxCommentTree tree

def isTheoremValueChild (parent : SyntaxTree.Tree) (index : Nat) : Bool :=
  match parent with
  | .node (.raw `Lean.Parser.Command.theorem) _ => index == 3
  | _ => false

def shouldEmitOriginalChild
    (parent : SyntaxTree.Tree) (index : Nat) (child : SyntaxTree.Tree)
    : Bool :=
  isTheoremValueChild parent index || shouldEmitOriginalTree child

def RenderState.emitOriginalTree (state : RenderState) (tree : SyntaxTree.Tree)
    : RenderState :=
  match SyntaxTree.Tree.firstToken? tree, SyntaxTree.Tree.lastToken? tree with
  | some firstToken, some lastToken =>
      let leading :=
        match state.lastToken? with
        | some leftToken =>
            SyntaxTree.sourceText state.source leftToken.span.stop firstToken.span.start
        | none => firstToken.leading.text
      let sourceText :=
        SyntaxTree.sourceText state.source firstToken.span.start lastToken.span.stop
      let sourceColumn := originalColumnAt state.source firstToken.span.start
      let targetColumn := lineWidth <| currentLineAfterAppend state.currentLine leading
      let emittedText :=
        if isProofTree tree then
          adjustOriginalTextIndent sourceColumn targetColumn sourceText
        else
          sourceText
      {
        state.appendOutput <| leading ++ emittedText with
          lastToken? := some lastToken
          pendingIndent? := none
      }
  | _, _ => state

/-! ## Flat rendering and fit measurement -/

partial def renderFlatSegment (state : RenderState) (segment : LineBreakRules.Segment)
    : RenderState :=
  match segment.parent with
  | .missing => state
  | .leaf token => state.emitToken token false
  | .node _ _ =>
      segment.indexes.foldl
        (fun state index =>
          match segment.child? index with
          | some child =>
              if shouldEmitOriginalChild segment.parent index child then
                state.emitOriginalTree child
              else
                renderFlatSegment state (LineBreakRules.Segment.ofTree child)
          | none => state)
        state

partial def flatSegmentText (state : RenderState) (segment : LineBreakRules.Segment)
    : String :=
  (renderFlatSegment { state with output := "", currentLine := "" } segment).output

def currentLineFitsWith (state : RenderState) (suffix : String) : Bool :=
  lineFitsWithTrailingWidth
    (currentLineAfterAppend state.currentLine suffix)
    state.lineFitSuffixWidth

def firstLineWithBreakFlag (text : String) : String × Bool :=
  let rec loop : List Char → List Char → String × Bool
    | [], current => (String.ofList current.reverse, false)
    | '\n' :: _, current => (String.ofList current.reverse, true)
    | char :: rest, current => loop rest (char :: current)
  loop (SpaceRules.normalizeLineEndings text).toList []

def RenderState.withoutLineFitSuffix (state : RenderState) : RenderState :=
  { state with lineFitSuffixWidth := 0 }

def hasRuleBreakAt
    (context : LineBreakRules.RuleContext) (segment : LineBreakRules.Segment)
    (index : Nat)
    : Bool :=
  let rule := LineBreakRules.formattingRuleFor segment.parent
  (rule.breakPoints context segment).any
    fun breakPoint =>
      breakPoint.index == index

structure WidthState where
  source : String
  currentLineWidth : Nat
  lastToken? : Option SyntaxTree.Token
  pendingIndent? : Option Nat

def WidthState.ofRenderState (state : RenderState) : WidthState :=
  {
    source := state.source
    currentLineWidth := lineWidth state.currentLine
    lastToken? := state.lastToken?
    pendingIndent? := state.pendingIndent?
  }

def widthAfterAppend (currentLineWidth : Nat) (text : String) : Nat :=
  let rec loop : List Char → Nat → Nat
    | [], width => width
    | '\n' :: rest, _ => loop rest 0
    | '\r' :: rest, _ => loop rest 0
    | _ :: rest, width => loop rest (width + 1)
  loop text.toList currentLineWidth

def firstLineAppendWidth (text : String) : Nat × Bool :=
  let rec loop : List Char → Nat → Nat × Bool
    | [], width => (width, false)
    | '\n' :: _, width => (width, true)
    | '\r' :: _, width => (width, true)
    | _ :: rest, width => loop rest (width + 1)
  loop text.toList 0

def WidthState.defaultWhitespace (state : WidthState) (token : SyntaxTree.Token)
    (preserveLines : Bool := false)
    : String :=
  match state.lastToken?, state.pendingIndent? with
  | some left, some indent =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop token.span.start
      let indentation := spaces indent
      if SpaceRules.hasCommentStart trivia then
        SpaceRules.commentTriviaForBreak trivia indentation
      else if hasBlankLineStructure trivia then
        "\n\n" ++ indentation
      else
        "\n" ++ indentation
  | none, some indent =>
      let indentation := spaces indent
      if SpaceRules.hasCommentStart token.leading.text then
        SpaceRules.commentTriviaForBreak token.leading.text indentation
      else if hasBlankLineStructure token.leading.text then
        "\n\n" ++ indentation
      else
        "\n" ++ indentation
  | none, none =>
      if SpaceRules.hasCommentStart token.leading.text then
        SpaceRules.reindentCommentTrivia token.leading.text ""
      else
        ""
  | some left, none =>
      SpaceRules.interTokenWhitespace state.source left token preserveLines

def WidthState.appendText (state : WidthState) (text : String) : WidthState :=
  { state with currentLineWidth := widthAfterAppend state.currentLineWidth text }

def WidthState.hasBlankBoundaryBefore (state : WidthState) (tree : SyntaxTree.Tree)
    : Bool :=
  match state.lastToken?, SyntaxTree.Tree.firstToken? tree with
  | some left, some right =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop right.span.start
      hasBlankLineStructure trivia
  | _, _ => false

def WidthState.afterFlatTreeForSuffix (state : WidthState) (tree : SyntaxTree.Tree)
    : WidthState :=
  match SyntaxTree.Tree.lastToken? tree with
  | some token => { state with lastToken? := some token, pendingIndent? := none }
  | none => state

structure SuffixState where
  widthState : WidthState
  suffixWidth : Nat

def SuffixState.appendText (state : SuffixState) (text : String) : SuffixState × Bool :=
  let (addedWidth, stopped) := firstLineAppendWidth text
  let widthState :=
    if stopped then
      state.widthState
    else
      state.widthState.appendText text
  ({ widthState, suffixWidth := state.suffixWidth + addedWidth }, stopped)

def SuffixState.emitToken (state : SuffixState) (token : SyntaxTree.Token)
    (preserveLines : Bool := false)
    : SuffixState × Bool :=
  if token.lexeme.isEmpty then
    (state, false)
  else
    let text := state.widthState.defaultWhitespace token preserveLines ++ token.lexeme
    let (state, stopped) := state.appendText text
    (
      {
        state with
          widthState :=
            {
              state.widthState with
                lastToken? := some token
                pendingIndent? := none
            }
      },
      stopped
    )

partial def measureSuffixOfTree
    (context : LineBreakRules.RuleContext) (state : SuffixState)
    (tree : SyntaxTree.Tree)
    : SuffixState × Bool :=
  match tree with
  | .missing => (state, false)
  | .leaf token =>
      match LineBreakRules.suffixTokenAction context token with
      | .skip => (state, false)
      | .emit => state.emitToken token false
      | .stop => (state, true)
  | .node _ _ =>
      let segment := LineBreakRules.Segment.ofTree tree
      segment.indexes.foldl
        (fun (state, stopped) index =>
          if stopped then
            (state, true)
          else
            match segment.child? index with
            | none => (state, false)
            | some child =>
                if segment.start < index && hasRuleBreakAt context segment index then
                  (state, true)
                else
                  let childContext := context.push segment index
                  measureSuffixOfTree childContext state child)
        (state, false)

def RenderState.firstLineOfOriginalTree (state : RenderState) (tree : SyntaxTree.Tree)
    : RenderState × Bool :=
  match SyntaxTree.Tree.firstToken? tree, SyntaxTree.Tree.lastToken? tree with
  | some firstToken, some lastToken =>
      let emitted :=
        state.defaultWhitespace firstToken true
        ++ SyntaxTree.sourceText state.source firstToken.span.start lastToken.span.stop
      let (firstLine, stopped) := firstLineWithBreakFlag emitted
      (
        {
          state.appendOutput firstLine with
            lastToken? := some lastToken
            pendingIndent? := none
        },
        stopped
      )
  | _, _ => (state, false)

partial def renderFirstLineOfTree (state : RenderState) (tree : SyntaxTree.Tree)
    : RenderState × Bool :=
  match tree with
  | .missing => (state, false)
  | .leaf token =>
      if token.lexeme.isEmpty then
        (state, false)
      else
        let emitted := state.defaultWhitespace token false ++ token.lexeme
        let (firstLine, stopped) := firstLineWithBreakFlag emitted
        (
          {
            state.appendOutput firstLine with
              lastToken? := some token
              pendingIndent? := none
          },
          stopped
        )
  | .node _ _ =>
      if shouldEmitOriginalTree tree then
        state.firstLineOfOriginalTree tree
      else
        let segment := LineBreakRules.Segment.ofTree tree
        segment.indexes.foldl
          (fun (state, stopped) index =>
            if stopped then
              (state, true)
            else
              match segment.child? index with
              | none => (state, false)
              | some child =>
                  if segment.start < index
                      && hasRuleBreakAt state.context segment index then
                    (state, true)
                  else
                    let childContext := state.context.push segment index
                    let (rendered, stopped) :=
                      renderFirstLineOfTree { state with context := childContext } child
                    ({ rendered with context := state.context }, stopped))
          (state.withoutLineFitSuffix, false)

partial def lineFitSuffixAfterChild
    (state : RenderState) (segment : LineBreakRules.Segment) (index : Nat)
    (child : SyntaxTree.Tree)
    : Nat × Bool :=
  let afterChild := (WidthState.ofRenderState state).afterFlatTreeForSuffix child
  let context := state.context
  let rec loop (suffixState : SuffixState) (nextIndex : Nat)
      : SuffixState × Bool :=
    if nextIndex < segment.stop then
      match segment.child? nextIndex with
      | some nextChild =>
          if suffixState.widthState.hasBlankBoundaryBefore nextChild then
            (suffixState, false)
          else
            let childContext := context.push segment nextIndex
            let (rendered, stopped) :=
              measureSuffixOfTree childContext suffixState nextChild
            if stopped then (rendered, false) else loop rendered (nextIndex + 1)
      | none => loop suffixState (nextIndex + 1)
    else
      (suffixState, true)
  let (suffixState, reachedEnd) :=
    loop { widthState := afterChild, suffixWidth := 0 } (index + 1)
  (suffixState.suffixWidth, reachedEnd)

def firstRuleBreakAfter
    (context : LineBreakRules.RuleContext) (segment : LineBreakRules.Segment)
    (index suffixStop : Nat)
    : Nat :=
  let rule := LineBreakRules.formattingRuleFor segment.parent
  (rule.breakPoints context segment).foldl
    (fun stop breakPoint =>
      if index < breakPoint.index && breakPoint.index < stop then
        breakPoint.index
      else
        stop)
    suffixStop

def lineFitSuffixForChild
    (state : RenderState) (segment : LineBreakRules.Segment) (index suffixStop : Nat)
    (child : SyntaxTree.Tree)
    : Nat :=
  let suffixStop := firstRuleBreakAfter state.context segment index suffixStop
  let suffixSegment := segment.slice segment.start suffixStop
  let (localSuffix, reachedEnd) :=
    lineFitSuffixAfterChild state suffixSegment index child
  let inheritedSuffix :=
    if suffixStop == segment.stop && reachedEnd then
      state.lineFitSuffixWidth
    else
      0
  localSuffix + inheritedSuffix

/-! ## Source-break discovery -/

structure SourceBreakLayout where
  segment : LineBreakRules.Segment
  breaks : List SourceBreak

def SourceBreakLayout.breakAt? (layout : SourceBreakLayout) (index : Nat)
    : Option SourceBreak :=
  layout.breaks.find? fun sourceBreak => sourceBreak.index == index

def SourceBreakLayout.nextBreakIndex (layout : SourceBreakLayout) (index : Nat) : Nat :=
  match layout.breaks.find? fun sourceBreak => index < sourceBreak.index with
  | some sourceBreak => sourceBreak.index
  | none => layout.segment.stop

def hasSourceBreakBetweenTokens
    (source : String) (leftToken rightToken : SyntaxTree.Token)
    : Bool :=
  let trivia := SyntaxTree.sourceText source leftToken.span.stop rightToken.span.start
  SpaceRules.hasLineStructure trivia && !hasBlankLineStructure trivia

def sourceBreaksInSegment (source : String) (segment : LineBreakRules.Segment)
    : List SourceBreak :=
  match segment.children? with
  | none => []
  | some children =>
      let step (state : Option SyntaxTree.Token × List SourceBreak) (index : Nat) :=
        let (left?, breaks) := state
        let break? :=
          if segment.start < index then
            match left?, children[index]? >>= SyntaxTree.Tree.firstToken? with
            | some left, some right =>
                if hasSourceBreakBetweenTokens source left right then
                  some { index, indent := 0 }
                else
                  none
            | _, _ => none
          else
            none
        let left? :=
          match children[index]? >>= SyntaxTree.Tree.lastToken? with
          | some token => some token
          | none => left?
        let breaks :=
          match break? with
          | some sourceBreak => sourceBreak :: breaks
          | none => breaks
        (left?, breaks)
      let (_, breaks) := (List.range segment.stop).foldl step (none, [])
      breaks.reverse

def normalizeBreakPoints
    (segment : LineBreakRules.Segment) (breakPoints : List LineBreakRules.BreakPoint)
    : List LineBreakRules.BreakPoint :=
  (breakPoints.filter
    fun breakPoint =>
      segment.start <= breakPoint.index && breakPoint.index < segment.stop)
  |>.mergeSort fun left right => left.index < right.index

def ruleBreakPoints
    (context : LineBreakRules.RuleContext) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    : List LineBreakRules.BreakPoint :=
  normalizeBreakPoints segment (rule.breakPoints context segment)

def sourceBreaksAllowedByBreakPoints
    (source : String) (segment : LineBreakRules.Segment)
    (breakPoints : List LineBreakRules.BreakPoint)
    : List SourceBreak :=
  (sourceBreaksInSegment source segment).filter
    fun sourceBreak =>
      breakPoints.any fun breakPoint => breakPoint.index == sourceBreak.index

def sourceBreakBeforeSegmentStart? (state : RenderState)
    (segment : LineBreakRules.Segment)
    : Option SourceBreak := do
  let left ← state.lastToken?
  let right ← segmentFirstToken? segment
  let trivia := SyntaxTree.sourceText state.source left.span.stop right.span.start
  if SpaceRules.hasLineStructure trivia && !hasBlankLineStructure trivia then
    some { index := segment.start, indent := 0 }
  else
    none

def sourceBreaksAllowedByBreakPointsInState
    (state : RenderState) (segment : LineBreakRules.Segment)
    (breakPoints : List LineBreakRules.BreakPoint)
    : List SourceBreak :=
  let sourceBreaks := sourceBreaksAllowedByBreakPoints state.source segment breakPoints
  if breakPoints.any fun breakPoint => breakPoint.index == segment.start then
    match sourceBreakBeforeSegmentStart? state segment with
    | some sourceBreak => sourceBreak :: sourceBreaks
    | none => sourceBreaks
  else
    sourceBreaks

def segmentHasAllowedSourceBreaks
    (source : String) (context : LineBreakRules.RuleContext)
    (segment : LineBreakRules.Segment)
    : Bool :=
  let rule := LineBreakRules.formattingRuleFor segment.parent
  let breakPoints := ruleBreakPoints context segment rule
  rule.useExistingBreaks context segment
  && !(sourceBreaksAllowedByBreakPoints source segment breakPoints).isEmpty

partial def segmentHasRuleSourceBreaks
    (source : String) (context : LineBreakRules.RuleContext)
    (segment : LineBreakRules.Segment)
    : Bool :=
  match segment.parent with
  | .missing => false
  | .leaf _ => false
  | .node _ _ =>
      if segmentHasAllowedSourceBreaks source context segment then
        true
      else
        let rec loop : List Nat → Bool
          | [] => false
          | index :: rest =>
              match segment.child? index with
              | none => false
              | some child =>
                  let childSegment := LineBreakRules.Segment.ofTree child
                  segmentHasRuleSourceBreaks source (context.push segment index)
                    childSegment
                  || loop rest
        loop segment.indexes

partial def segmentAllowsFlat
    (source : String) (context : LineBreakRules.RuleContext)
    (segment : LineBreakRules.Segment) (respectSourceBreaks : Bool := true)
    : Bool :=
  match segment.parent with
  | .missing => true
  | .leaf _ => true
  | .node _ _ =>
      if isProofTree segment.parent then
        false
      else
        match segment.singleChild? with
        | some (index, child) =>
            segmentAllowsFlat source (context.push segment index)
              (LineBreakRules.Segment.ofTree child)
        | none =>
            let rule := LineBreakRules.formattingRuleFor segment.parent
            if rule.mandatory context segment then
              false
            else if respectSourceBreaks
                    && segmentHasAllowedSourceBreaks source context segment then
              false
            else
              let rec loop : List Nat → Bool
                | [] => true
                | index :: rest =>
                    match segment.child? index with
                    | none => true
                    | some child =>
                        segmentAllowsFlat source (context.push segment index)
                          (LineBreakRules.Segment.ofTree child)
                        && loop rest
              loop segment.indexes

def flatSegmentFits (state : RenderState) (segment : LineBreakRules.Segment) : Bool :=
  segmentAllowsFlat state.source state.context segment
  && currentLineFitsWith state (flatSegmentText state segment)

def flatSegmentFitsIgnoringSourceBreaks
    (state : RenderState) (segment : LineBreakRules.Segment)
    : Bool :=
  segmentAllowsFlat state.source state.context segment false
  && currentLineFitsWith state (flatSegmentText state segment)

def segmentFirstTokenColumn (state : RenderState) (segment : LineBreakRules.Segment)
    : Nat :=
  match segmentFirstToken? segment with
  | some token => state.nextTokenColumn token
  | none => state.currentColumn

def ruleBreakDepth
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    : Nat :=
  if rule.accumulatesInfixLeftDepth state.context segment then
    state.infixLeftDepth
  else
    0

def ruleBreakBase
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn baseIndentation : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : SegmentBase :=
  if !rule.accumulatesInfixLeftDepth state.context segment
      && rule.flow state.context segment
      && 0 < state.infixLeftDepth
      && 0 < breakPoint.indentLevels then
    let roundedIndentation :=
      indentationLevelForColumn (indentationPastColumn baseColumn)
    let indentation := roundedIndentation + (state.infixLeftDepth - 1)
    { column := indentation * indentationSpaces, indentation }
  else
    { column := baseColumn, indentation := baseIndentation }

def breakPointIndent
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (breakPoint : LineBreakRules.BreakPoint)
    : Nat :=
  let baseIndentation := state.segmentIndentation
  let baseColumn :=
    if baseIndentation == state.segmentIndentation then
      state.segmentBaseColumn
    else
      baseIndentation * indentationSpaces
  let base := ruleBreakBase state segment rule baseColumn baseIndentation breakPoint
  breakIndent base.column base.indentation
    (ruleBreakDepth state segment rule) breakPoint

def sourceBreaksForRule?
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    : Option (List SourceBreak) :=
  let points := ruleBreakPoints state.context segment rule
  let sourceBreaks := sourceBreaksAllowedByBreakPointsInState state segment points
  if sourceBreaks.isEmpty then
    none
  else
    some
    <| points.filterMap
        fun breakPoint =>
          if sourceBreaks.any
              fun sourceBreak => sourceBreak.index == breakPoint.index then
            some
              {
                index := breakPoint.index,
                indent := breakPointIndent state segment rule breakPoint
              }
          else
            none

/-! ## Flow rendering decisions -/

structure FlowRenderContext where
  segment : LineBreakRules.Segment
  rule : LineBreakRules.LineBreakRule
  breakPoints : List LineBreakRules.BreakPoint
  entryState : RenderState

def FlowRenderContext.breakAt? (flow : FlowRenderContext) (index : Nat)
    : Option LineBreakRules.BreakPoint :=
  flow.breakPoints.find? fun breakPoint => breakPoint.index == index

def FlowRenderContext.nextBreakIndex (flow : FlowRenderContext) (index : Nat) : Nat :=
  match flow.breakPoints.find? fun breakPoint => index < breakPoint.index with
  | some breakPoint => breakPoint.index
  | none => flow.segment.stop

def FlowRenderContext.stateForPieceFit
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    : RenderState :=
  if flow.nextBreakIndex index == flow.segment.stop then
    state
  else
    { state with lineFitSuffixWidth := 0 }

def FlowRenderContext.pieceFits
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    : Bool :=
  flatSegmentFitsIgnoringSourceBreaks (flow.stateForPieceFit state index)
    (flow.segment.slice index (flow.nextBreakIndex index))

def FlowRenderContext.childFits
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    (context : LineBreakRules.RuleContext)
    (childSegment : LineBreakRules.Segment)
    (respectSourceBreaks : Bool := true)
    : Bool :=
  let probe := { flow.stateForPieceFit state index with context }
  if respectSourceBreaks then
    flatSegmentFits probe childSegment
  else
    flatSegmentFitsIgnoringSourceBreaks probe childSegment

def FlowRenderContext.childFirstLineFits
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    (context : LineBreakRules.RuleContext) (child : SyntaxTree.Tree)
    : Bool :=
  let probe := { flow.stateForPieceFit state index with context }
  let (rendered, _) := renderFirstLineOfTree probe child
  !outputIntroducedLineBreak probe rendered
  && lineFitsWithTrailingWidth rendered.currentLine rendered.lineFitSuffixWidth

def FlowRenderContext.withBreak
    (flow : FlowRenderContext) (state : RenderState)
    (breakPoint : LineBreakRules.BreakPoint)
    : RenderState :=
  let entryIndentation := flow.entryState.segmentIndentation
  let entryBaseColumn := flow.entryState.segmentBaseColumn
  let base :=
    ruleBreakBase flow.entryState flow.segment flow.rule
      entryBaseColumn entryIndentation breakPoint
  state.withRuleBreakIndent base.column base.indentation
    (ruleBreakDepth flow.entryState flow.segment flow.rule) breakPoint

def FlowRenderContext.stateForForcedNestedChild?
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    (breakAfterPreviousChild : Bool)
    (childContext : LineBreakRules.RuleContext)
    (childSegment : LineBreakRules.Segment)
    : Option RenderState :=
  match flow.breakAt? index with
  | some breakPoint =>
      if index == flow.segment.start then
        if flow.childFits state index childContext childSegment then
          some state
        else
          some
          <| state.withPendingIndent
              (state.currentIndent + breakPoint.indentLevels * indentationSpaces)
      else if breakAfterPreviousChild
              || !flow.childFits state index childContext childSegment false
              || !flow.pieceFits state index then
        some <| flow.withBreak state breakPoint
      else
        none
  | none =>
      if index == flow.segment.start then some state else none

/-! ## Recursive rendering -/

mutual

  partial def renderSegment (state : RenderState) (segment : LineBreakRules.Segment)
      : RenderState :=
    let rule := LineBreakRules.formattingRuleFor segment.parent
    let state :=
      match segment.parent with
      | .node _ _ =>
          if rule.accumulatesInfixLeftDepth state.context segment then
            let baseColumn := segmentFirstTokenColumn state segment
            {
              state with
                segmentBaseColumn := baseColumn
                segmentIndentation := indentationLevelForColumn baseColumn
            }
          else
            state
      | _ => state
    let state := state.traceSegment segment rule.name
    match segment.parent with
    | .missing => state
    | .leaf token => state.emitToken token
    | .node _ children =>
        if segment.start == 0
            && segment.stop == children.size
            && shouldEmitOriginalTree segment.parent then
          state.emitOriginalTree segment.parent
        else
          renderSegmentByRule state segment rule

partial def renderSegmentByRule (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    : RenderState :=
  let breakPoints := ruleBreakPoints state.context segment rule
  let isFlow := rule.flow state.context segment
  let useExistingBreaks := rule.useExistingBreaks state.context segment
  if rule.atomic then
    renderFlatSegment state segment
  else if rule.mandatory state.context segment && !breakPoints.isEmpty then
    renderBalancedSegment state segment rule breakPoints
  else if breakPoints.isEmpty && !isFlow then
    renderChildren state segment
  else if useExistingBreaks then
    renderUsingExistingBreaks state segment rule breakPoints isFlow
  else if flatSegmentFitsIgnoringSourceBreaks state segment then
    renderFlatSegment state segment
  else
    renderAfterFlatFailure state segment rule breakPoints isFlow

partial def renderRuleLayout
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (breakPoints : List LineBreakRules.BreakPoint) (isFlow : Bool)
    : RenderState :=
  if isFlow then
    renderFlowSegment state segment rule breakPoints
  else
    renderBalancedSegment state segment rule breakPoints

partial def renderAfterFlatFailure
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (breakPoints : List LineBreakRules.BreakPoint) (isFlow : Bool)
    : RenderState :=
  let fallback (_ : Unit) := renderRuleLayout state segment rule breakPoints isFlow
  if !isFlow then
    fallback ()
  else
    match sourceBreaksForRule? state segment rule with
    | none => fallback ()
    | some sourceBreaks =>
        match renderFlowSegmentWithSourceBreaks? state segment sourceBreaks with
        | some candidate =>
            if renderedCandidateFits state candidate then candidate else fallback ()
        | none => fallback ()

partial def renderUsingExistingBreaks
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (breakPoints : List LineBreakRules.BreakPoint) (isFlow : Bool)
    : RenderState :=
  let hasSourceBreaks :=
    !(sourceBreaksAllowedByBreakPointsInState state segment breakPoints).isEmpty
  if !isFlow && hasSourceBreaks then
    renderBalancedSegment state segment rule breakPoints
  else
    match tryRenderSegmentWithSourceBreaks? state segment rule with
    | some rendered => rendered
    | none =>
        if flatSegmentFitsIgnoringSourceBreaks state segment then
          renderFlatSegment state segment
        else
          renderAfterFlatFailure state segment rule breakPoints isFlow

partial def renderNestedSegment
    (state : RenderState) (segment : LineBreakRules.Segment) (index : Nat)
    (child : SyntaxTree.Tree) (suffixStop? : Option Nat := none)
    : RenderState :=
  let state := state.preserveBlankBoundaryBefore child
  let childContext := state.context.push segment index
  let childSegment := LineBreakRules.Segment.ofTree child
  let childRule := LineBreakRules.formattingRuleFor child
  let inheritsBase := childRule.inheritBase childContext childSegment
  let state :=
    if inheritsBase || !childRule.alignStartToIndentation childContext childSegment then
      state
    else
      let naturalStartColumn := state.segmentStartColumn childSegment
      let alignedStartColumn := indentationPastColumn naturalStartColumn
      state.appendOutput <| spaces (alignedStartColumn - naturalStartColumn)
  let scope := ChildRenderScope.capture state
  let suffixStop := suffixStop?.getD segment.stop
  let lineFitSuffix := lineFitSuffixForChild state segment index suffixStop child
  let childBase :=
    if inheritsBase then
      { column := state.segmentBaseColumn, indentation := state.segmentIndentation }
    else
      state.segmentStartBaseFor childSegment
  let childState :=
    {
      state with
        context := childContext
        segmentBaseColumn := childBase.column
        segmentIndentation := childBase.indentation
        lineFitSuffixWidth := lineFitSuffix
        trace := state.trace.pushPath index
    }
  let rendered :=
    if shouldEmitOriginalChild segment.parent index child then
      childState.emitOriginalTree child
    else
      renderSegment childState childSegment
  scope.restore rendered

partial def renderChildren (state : RenderState) (segment : LineBreakRules.Segment)
    : RenderState :=
  match segment.parent with
  | .missing => state
  | .leaf token => state.emitToken token
  | .node _ _ =>
      segment.indexes.foldl
        (fun state index =>
          match segment.child? index with
          | some child => renderNestedSegment state segment index child
          | none => state)
        state

partial def renderSegmentRange
    (state : RenderState) (segment : LineBreakRules.Segment)
    (start stop : Nat)
    : RenderState :=
  if start >= stop then
    state
  else if start == segment.start && stop == segment.stop then
    renderChildren state (segment.slice start stop)
  else
    renderSegment state (segment.slice start stop)

partial def renderSegmentWithSourceBreaks
    (state : RenderState) (segment : LineBreakRules.Segment) (breaks : List SourceBreak)
    : RenderState :=
  let layout : SourceBreakLayout := { segment, breaks }
  let rec loop (state : RenderState) (index : Nat)
      : RenderState :=
    if index < segment.stop then
      match segment.child? index with
      | none => loop state (index + 1)
      | some child =>
          let state :=
            match layout.breakAt? index with
            | some sourceBreak => state.withPendingIndent sourceBreak.indent
            | none => state
          loop
            (renderNestedSegment state segment index child
              (some (layout.nextBreakIndex index)))
            (index + 1)
    else
      state
  loop state segment.start

partial def renderFlowSegmentWithSourceBreaks?
    (state : RenderState) (segment : LineBreakRules.Segment) (breaks : List SourceBreak)
    : Option RenderState :=
  let layout : SourceBreakLayout := { segment, breaks }
  let rec loop (state : RenderState) (index : Nat)
      : Option RenderState :=
    if index < segment.stop then
      match segment.child? index with
      | none => loop state (index + 1)
      | some child =>
          let state :=
            match layout.breakAt? index with
            | some sourceBreak => state.withPendingIndent sourceBreak.indent
            | none => state
          let before := state
          let rendered :=
            renderNestedSegment state segment index child
              (some (layout.nextBreakIndex index))
          if renderedTreeIsMultiline before rendered child
              && (layout.breakAt? index).isNone then
            none
          else
            loop rendered (index + 1)
    else
      some state
  loop state segment.start

partial def tryRenderSegmentWithSourceBreaks?
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    : Option RenderState :=
  match sourceBreaksForRule? state segment rule with
  | none =>
      none
  | some breaks =>
      let candidate := renderSegmentWithSourceBreaks state segment breaks
      if renderedCandidateFits state candidate then
        some candidate
      else
        none

partial def renderFlowSegment
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (breakPoints : List LineBreakRules.BreakPoint)
    : RenderState :=
  match SyntaxTree.Tree.firstToken? segment.parent with
  | none => renderChildren state segment
  | some _ =>
      let flow : FlowRenderContext :=
        { segment, rule, breakPoints, entryState := state }
      renderFlowChildren state flow segment.start false

partial def renderFlowChildren
    (state : RenderState) (flow : FlowRenderContext) (index : Nat)
    (breakAfterPreviousChild : Bool)
    : RenderState :=
  if index >= flow.segment.stop then
    state
  else
    match flow.segment.child? index with
    | none => renderFlowChildren state flow (index + 1) breakAfterPreviousChild
    | some child =>
        let childSegment := LineBreakRules.Segment.ofTree child
        let childContext := state.context.push flow.segment index
        let renderNestedAndContinue (state : RenderState) :=
          let before := state
          let rendered :=
            renderNestedSegment state flow.segment index child
              (some (flow.nextBreakIndex index))
          renderFlowChildren rendered flow (index + 1)
            (renderedTreeIsMultiline before rendered child)
        match flow.stateForForcedNestedChild? state index breakAfterPreviousChild
                childContext childSegment with
        | some state => renderNestedAndContinue state
        | none =>
            if segmentHasRuleSourceBreaks state.source childContext childSegment then
              renderNestedAndContinue state
            else if flow.childFits state index childContext childSegment then
              renderFlowChildren (renderFlatSegment state childSegment)
                flow (index + 1) false
            else if flow.childFirstLineFits state index childContext child then
              renderNestedAndContinue state
            else
              let state :=
                match flow.breakAt? index with
                | some breakPoint => flow.withBreak state breakPoint
                | none =>
                    state.withPendingIndent
                      (state.segmentBaseIndent + indentationSpaces)
              renderNestedAndContinue state

partial def renderBalancedSegment
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (breakPoints : List LineBreakRules.BreakPoint)
    : RenderState :=
  if breakPoints.isEmpty then
    renderChildren state segment
  else
    let entryIndentation := state.segmentIndentation
    let entryBaseColumn := state.segmentBaseColumn
    let entryDepth := state.infixLeftDepth
    let accumulatesInfixLeftDepth :=
      rule.accumulatesInfixLeftDepth state.context segment
    let entryBreakDepth :=
      if accumulatesInfixLeftDepth then
        entryDepth
      else
        0
    let renderPiece (state : RenderState) (start stop pieceIndentLevels : Nat)
        : RenderState :=
      let depth :=
        if accumulatesInfixLeftDepth then
          entryDepth + pieceIndentLevels + 1
        else
          entryDepth
      let rendered :=
        renderSegmentRange
          { state with infixLeftDepth := depth, lineFitSuffixWidth := 0 } segment start
          stop
      {
        rendered with
          infixLeftDepth := entryDepth, lineFitSuffixWidth := state.lineFitSuffixWidth
      }
    let rec loop (state : RenderState) (start pieceIndentLevels : Nat)
        : List LineBreakRules.BreakPoint → RenderState
      | [] => renderSegmentRange state segment start segment.stop
      | breakPoint :: rest =>
          let state := renderPiece state start breakPoint.index pieceIndentLevels
          let base :=
            ruleBreakBase state segment rule entryBaseColumn entryIndentation breakPoint
          let state :=
            state.withRuleBreakIndent base.column base.indentation entryBreakDepth
              breakPoint
          let rest := rest.dropWhile fun next => next.index == breakPoint.index
          loop state breakPoint.index breakPoint.indentLevels rest
    loop state segment.start 0 breakPoints

end

def RenderState.finalTrivia (state : RenderState) : String :=
  match state.lastToken? with
  | some token =>
      SpaceRules.cleanFinalTrivia
      <| SyntaxTree.sourceText state.source token.span.stop state.source.endPos.offset
  | none =>
      SpaceRules.cleanFinalTrivia state.source

def renderModuleTree (moduleTree : SyntaxTree.Module) : String :=
  let state :=
    renderSegment { source := moduleTree.source }
      (LineBreakRules.Segment.ofTree moduleTree.tree)
  SpaceRules.normalizeFinalNewline (state.output ++ state.finalTrivia)

def renderModuleTreeWithTrace (moduleTree : SyntaxTree.Module) : String × String :=
  let state :=
    renderSegment
      { source := moduleTree.source, trace := { enabled := true } }
      (LineBreakRules.Segment.ofTree moduleTree.tree)
  let formatted := SpaceRules.normalizeFinalNewline (state.output ++ state.finalTrivia)
  (formatted, state.trace.formatWithOutput formatted)

end Formatter
end LeanFmt
