import LeanFmt.Formatter.LineBreakRules
import LeanFmt.Formatter.SpaceRules
import LeanFmt.Formatter.Trace

namespace LeanFmt
namespace Formatter

/-! ## Output and indentation state -/

def maxLineWidth : Nat :=
  90

structure Options where
  lineWidth : Nat := maxLineWidth
deriving BEq, Repr

def indentationSpaces : Nat :=
  2

def lineWidth (text : String) : Nat :=
  text.length

def firstLineAppendWidth (text : String) : Nat × Bool :=
  let rec loop : List Char → Nat → Nat × Bool
    | [], width => (width, false)
    | '\n' :: _, width
    | '\r' :: _, width => (width, true)
    | _ :: rest, width => loop rest (width + 1)
  loop text.toList 0

def lineFits (text : String) (limit : Nat := maxLineWidth) : Bool :=
  lineWidth text <= limit

def linesFit (text : String) (limit : Nat := maxLineWidth) : Bool :=
  (SpaceRules.normalizeLineEndings text).splitOn "\n"
  |>.all fun line => lineFits line limit

def lineFitsWithTrailingWidth
    (line : String) (trailingWidth : Nat) (limit : Nat := maxLineWidth)
    : Bool :=
  lineWidth line + trailingWidth <= limit

def linesFitWithTrailingWidth
    (text : String) (trailingWidth : Nat) (limit : Nat := maxLineWidth)
    : Bool :=
  let rec loop : List String → Bool
    | [] => trailingWidth <= limit
    | [line] => lineFitsWithTrailingWidth line trailingWidth limit
    | line :: rest => lineFits line limit && loop rest
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

def appendedLines (currentLine text : String) (limit : Nat := maxLineWidth)
    : AppendedLines :=
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
          (overflowCount + if lineWidth > limit then 1 else 0) [] rest
    | '\n' :: rest =>
        loop 0 (breakCount + 1)
          (overflowCount + if lineWidth > limit then 1 else 0) [] rest
    | '\r' :: rest =>
        loop 0 (breakCount + 1)
          (overflowCount + if lineWidth > limit then 1 else 0) [] rest
    | char :: rest =>
        loop (lineWidth + 1) breakCount overflowCount (char :: current) rest
  loop currentLine.length 0 0 [] text.toList

def charsAfterLastNewline (text : String) : String :=
  let rec loop : List Char → List Char → String
    | [], current => String.ofList current.reverse
    | '\n' :: rest, _ => loop rest []
    | char :: rest, current => loop rest (char :: current)
  loop (SpaceRules.normalizeLineEndings text).toList []

def hasBlankLineStructure (text : String) : Bool :=
  hasLineBreakChar text
  && SpaceRules.containsSubstring (SpaceRules.normalizeLineEndings text) "\n\n"

def originalColumnAt (source : String) (position : String.Pos.Raw) : Nat :=
  lineWidth <| charsAfterLastNewline <| SyntaxTree.sourceText source 0 position

def shiftColumnByAnchor (sourceAnchorColumn outputAnchorColumn sourceColumn : Nat)
    : Nat :=
  if sourceAnchorColumn <= outputAnchorColumn then
    sourceColumn + (outputAnchorColumn - sourceAnchorColumn)
  else
    sourceColumn - min sourceColumn (sourceAnchorColumn - outputAnchorColumn)

def shiftLineIndent (sourceColumn targetColumn : Nat) (line : String) : String :=
  if line.isEmpty then
    line
  else if sourceColumn <= targetColumn then
    spaces (targetColumn - sourceColumn) ++ line
  else
    let removeCount := min (sourceColumn - targetColumn) (leadingWhitespace line).length
    (line.drop removeCount).toString

def rebaseOriginalLines (sourceColumn targetColumn : Nat)
    : Nat → List String → List String
  | _, [] => []
  | blockCommentDepth, line :: rest =>
      let adjusted :=
        if 0 < blockCommentDepth then
          line
        else
          shiftLineIndent sourceColumn targetColumn line
      let blockCommentDepth :=
        SpaceRules.blockCommentDepthAfterLine blockCommentDepth line
      adjusted :: rebaseOriginalLines sourceColumn targetColumn blockCommentDepth rest

def rebaseOriginalTextIndent (sourceColumn targetColumn : Nat) (text : String) : String :=
  if sourceColumn == targetColumn then
    text
  else
    match (SpaceRules.normalizeLineEndings text).splitOn "\n" with
    | [] => text
    | first :: rest =>
        String.intercalate "\n"
        <| first
            :: rebaseOriginalLines sourceColumn targetColumn
                (SpaceRules.blockCommentDepthAfterLine 0 first) rest

def rebaseOriginalTreeText
    (source : String) (tree : SyntaxTree.Tree)
    (sourceColumn targetColumn : Nat)
    : String :=
  let rec loop (previous : SyntaxTree.Token) (parts : List String)
      : List SyntaxTree.Token → List String
    | [] => parts
    | token :: rest =>
        let trivia := SyntaxTree.sourceText source previous.span.stop token.span.start
        let trivia := rebaseOriginalTextIndent sourceColumn targetColumn trivia
        loop token (token.lexeme :: trivia :: parts) rest
  match tree.tokens.toList with
  | [] => ""
  | first :: rest => String.join <| (loop first [first.lexeme] rest).reverse

def originalContinuationIndent? (text : String) : Option Nat :=
  (SpaceRules.normalizeLineEndings text).splitOn "\n" |>.drop 1
  |>.foldl
      (fun minimum? line =>
        let indentation := (leadingWhitespace line).length
        if indentation == line.length then
          minimum?
        else
          match minimum? with
          | some minimum => some (min minimum indentation)
          | none => some indentation)
      none

structure SourceBreak where
  index : Nat
  indent : Nat
deriving BEq, Repr

structure TailIndentationAnchor where
  stop : Nat
  indentation : Nat
deriving Repr

inductive CommandBoundarySpacing where
  | lineBreak
  | blankLine
deriving BEq, Repr

structure RenderState where
  options : Options := {}
  source : String
  output : String := ""
  outputLineBreakCount : Nat := 0
  completedLineOverflowCount : Nat := 0
  introducedAtomicOverflowCount : Nat := 0
  currentLine : String := ""
  lastToken? : Option SyntaxTree.Token := none
  pendingIndent? : Option Nat := none
  pendingCommandBoundary? : Option CommandBoundarySpacing := none
  segmentBaseColumn : Nat := 0
  segmentIndentation : Nat := 0
  sourceLayoutBaseColumn : Nat := 0
  outputLayoutBaseColumn : Nat := 0
  tailIndentation? : Option Nat := none
  tailIndentationStop? : Option Nat := none
  tailIndentationAnchors : List TailIndentationAnchor := []
  breakIndentationShift : Nat := 0
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
  sourceLayoutBaseColumn : Nat
  outputLayoutBaseColumn : Nat
  tailIndentation? : Option Nat
  tailIndentationStop? : Option Nat
  tailIndentationAnchors : List TailIndentationAnchor
  breakIndentationShift : Nat
  lineFitSuffixWidth : Nat
  trace : Trace.State

def ChildRenderScope.capture (state : RenderState) : ChildRenderScope :=
  {
    context := state.context
    segmentBaseColumn := state.segmentBaseColumn
    segmentIndentation := state.segmentIndentation
    sourceLayoutBaseColumn := state.sourceLayoutBaseColumn
    outputLayoutBaseColumn := state.outputLayoutBaseColumn
    tailIndentation? := state.tailIndentation?
    tailIndentationStop? := state.tailIndentationStop?
    tailIndentationAnchors := state.tailIndentationAnchors
    breakIndentationShift := state.breakIndentationShift
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
      sourceLayoutBaseColumn := scope.sourceLayoutBaseColumn
      outputLayoutBaseColumn := scope.outputLayoutBaseColumn
      tailIndentation? := scope.tailIndentation?
      tailIndentationStop? := scope.tailIndentationStop?
      tailIndentationAnchors := scope.tailIndentationAnchors
      breakIndentationShift := scope.breakIndentationShift
      lineFitSuffixWidth := scope.lineFitSuffixWidth
      trace := rendered.trace.restorePathFrom scope.trace
  }

def currentLineAfterAppend (currentLine text : String) : String :=
  if hasLineBreakChar text then
    charsAfterLastNewline text
  else
    currentLine ++ text

def introducesCompletedLineOverflow
    (currentLine text : String) (limit : Nat := maxLineWidth)
    : Bool :=
  let rec loop (lineWidth : Nat) (lineTouched : Bool) : List Char → Bool
    | [] => false
    | '\r' :: '\n' :: rest =>
        (lineTouched && lineWidth > limit) || loop 0 false rest
    | '\n' :: rest => (lineTouched && lineWidth > limit) || loop 0 false rest
    | '\r' :: rest => (lineTouched && lineWidth > limit) || loop 0 false rest
    | _ :: rest => loop (lineWidth + 1) true rest
  loop currentLine.length false text.toList

def RenderState.appendOutput (state : RenderState) (text : String) : RenderState :=
  if hasLineBreakChar text then
    let appended := appendedLines state.currentLine text state.options.lineWidth
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

def ensureBlankLineBeforeIndentation (text indentation : String) : String :=
  let lineSuffix := "\n" ++ indentation
  let blankSuffix := "\n\n" ++ indentation
  if text.endsWith blankSuffix then
    text
  else if text.endsWith lineSuffix then
    (text.dropEnd lineSuffix.length).toString ++ blankSuffix
  else
    text ++ blankSuffix

def commentTriviaStartsOnNewLine (trivia : String) : Bool :=
  match trivia.toList.dropWhile SpaceRules.isHorizontalWhitespace with
  | '\n' :: _ | '\r' :: _ => true
  | _ => false

def ensureBlankLineBeforeLeadingComment (text : String) : String :=
  if text.startsWith "\n\n" || text.startsWith "\r\n\r\n" then
    text
  else if text.startsWith "\n" || text.startsWith "\r\n" then
    "\n" ++ text
  else
    "\n\n" ++ text

def commentTriviaForBoundary
    (trivia commentIndentation followingIndentation : String)
    (spacing : CommandBoundarySpacing)
    : String :=
  let adjusted :=
    SpaceRules.commentTriviaForBreakWithFollowingIndent trivia commentIndentation
      followingIndentation
  if spacing == .blankLine then
    if commentTriviaStartsOnNewLine trivia then
      ensureBlankLineBeforeLeadingComment adjusted
    else
      ensureBlankLineBeforeIndentation adjusted followingIndentation
  else
    adjusted

def whitespaceForPendingBoundary
    (trivia indentation : String) (lineWidth : Nat)
    (commandBoundary? : Option CommandBoundarySpacing)
    : String :=
  if SpaceRules.hasCommentStart trivia then
    let desiredIndent := indentation.length
    let commentIndentation :=
      spaces <| SpaceRules.commentIndentForWidth trivia desiredIndent lineWidth
    let result :=
      match commandBoundary? with
      | some spacing =>
          commentTriviaForBoundary trivia commentIndentation indentation spacing
      | none =>
          SpaceRules.commentTriviaForBreakWithFollowingIndent trivia commentIndentation
            indentation
    result
  else
    match commandBoundary? with
    | none =>
        if hasBlankLineStructure trivia then
          "\n\n" ++ indentation
        else
          "\n" ++ indentation
    | some .lineBreak => "\n" ++ indentation
    | some .blankLine => "\n\n" ++ indentation

def RenderState.indentForMultilineToken
    (state : RenderState) (token : SyntaxTree.Token) (desiredIndent : Nat)
    : Nat :=
  if hasLineBreakChar token.lexeme then
    match (SpaceRules.normalizeLineEndings token.lexeme).splitOn "\n" with
    | [] => desiredIndent
    | firstLine :: _ =>
        let sourceColumn := originalColumnAt state.source token.span.start
        if desiredIndent + firstLine.length > state.options.lineWidth
            && sourceColumn + firstLine.length <= state.options.lineWidth then
          sourceColumn
        else
          desiredIndent
  else
    desiredIndent

def RenderState.defaultWhitespace (state : RenderState) (token : SyntaxTree.Token)
    (preserveLines : Bool := false)
    : String :=
  match state.lastToken?, state.pendingIndent? with
  | some left, some indent =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop token.span.start
      let indent := state.indentForMultilineToken token indent
      let indentation := spaces indent
      whitespaceForPendingBoundary trivia indentation state.options.lineWidth
        state.pendingCommandBoundary?
  | none, some indent =>
      let indent := state.indentForMultilineToken token indent
      let indentation := spaces indent
      whitespaceForPendingBoundary token.leading.text indentation state.options.lineWidth
        state.pendingCommandBoundary?
  | none, none =>
      if SpaceRules.hasCommentStart token.leading.text then
        SpaceRules.reindentCommentTrivia token.leading.text ""
      else
        ""
  | some left, none =>
      SpaceRules.interTokenWhitespace state.source left token preserveLines

def RenderState.allowsStartAlignment (state : RenderState) : Bool :=
  match state.lastToken?, state.pendingIndent? with
  | some token, none => SpaceRules.allowsHorizontalAlignmentAfterToken token.lexeme
  | _, _ => true

def RenderState.ensureBlankCommandBoundaryBeforeRenderedTree
    (before rendered : RenderState) (tree : SyntaxTree.Tree)
    : RenderState :=
  match SyntaxTree.Tree.firstToken? tree with
  | none => rendered
  | some token =>
      let originalWhitespace := before.defaultWhitespace token
      let blankWhitespace :=
        ({ before with pendingCommandBoundary? := some .blankLine }).defaultWhitespace
          token
      if originalWhitespace == blankWhitespace then
        rendered
      else
        let renderedSuffix := (rendered.output.drop before.output.length).toString
        if !renderedSuffix.startsWith originalWhitespace then
          rendered
        else
          let body := (renderedSuffix.drop originalWhitespace.length).toString
          let addedLineBreaks :=
            Trace.newlineCount blankWhitespace - Trace.newlineCount originalWhitespace
          {
            rendered with
              output := before.output ++ blankWhitespace ++ body
              outputLineBreakCount := rendered.outputLineBreakCount + addedLineBreaks
              trace :=
                rendered.trace.shiftEntriesAfter before.trace.entries.length
                  addedLineBreaks
          }

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
          state.segmentIndentation state.pendingIndent? state.tailIndentation?
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
    let whitespace := state.defaultWhitespace token preserveLines
    let introducedAtomicOverflow :=
      match state.pendingIndent? with
      | none => false
      | some _ =>
          let tokenWidth := (firstLineAppendWidth token.lexeme).1
          let outputColumn :=
            lineWidth <| currentLineAfterAppend state.currentLine whitespace
          if state.options.lineWidth < outputColumn + tokenWidth then
            let sourceLeading :=
              match state.lastToken? with
              | some leftToken =>
                  SyntaxTree.sourceText state.source leftToken.span.stop token.span.start
              | none => token.leading.text
            if SpaceRules.hasLineStructure sourceLeading then
              let sourceColumn := lineWidth <| charsAfterLastNewline sourceLeading
              sourceColumn + tokenWidth <= state.options.lineWidth
            else
              false
          else
            false
    {
      state.appendOutput (whitespace ++ token.lexeme) with
        introducedAtomicOverflowCount :=
          state.introducedAtomicOverflowCount + if introducedAtomicOverflow then 1 else 0
        lastToken? := some token
        pendingIndent? := none
        pendingCommandBoundary? := none
    }

def RenderState.withPendingIndent (state : RenderState) (indent : Nat) : RenderState :=
  {
    state with
      pendingIndent? := some indent
      pendingCommandBoundary? := none
      tailIndentation? := none
      segmentBaseColumn := indent
      segmentIndentation := indentationLevelForColumn indent
  }

def breakIndent (baseColumn baseIndentation : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : Nat :=
  if breakPoint.indentLevels == 0 then
    max (indentationPastColumn baseColumn) (baseIndentation * indentationSpaces)
  else
    (baseIndentation + breakPoint.indentLevels) * indentationSpaces

def RenderState.withRuleBreakIndent
    (state : RenderState) (baseColumn baseIndentation : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : RenderState :=
  state.withPendingIndent <| breakIndent baseColumn baseIndentation breakPoint

def outputIntroducedLineBreak (before after : RenderState) : Bool :=
  before.outputLineBreakCount < after.outputLineBreakCount

def renderedCandidateFits (before after : RenderState) : Bool :=
  before.completedLineOverflowCount == after.completedLineOverflowCount
  && lineFitsWithTrailingWidth after.currentLine after.lineFitSuffixWidth
      after.options.lineWidth

def renderedOverflowCount (before after : RenderState) : Nat :=
  let completed := after.completedLineOverflowCount - before.completedLineOverflowCount
  let current :=
    if lineFitsWithTrailingWidth after.currentLine after.lineFitSuffixWidth
        after.options.lineWidth then
      0
    else
      1
  completed + current

def preferCandidateWithFewerOverflows (before current candidate : RenderState)
    : RenderState :=
  if renderedOverflowCount before candidate < renderedOverflowCount before current then
    candidate
  else
    current

def RenderState.segmentStartBaseFor
    (state : RenderState) (segment : LineBreakRules.Segment)
    : SegmentBase :=
  let column :=
    match segmentFirstToken? segment with
    | some token => state.nextTokenColumn token
    | none => state.currentColumn
  { column, indentation := indentationLevelForColumn column }

def RenderState.preserveBlankBoundaryBefore (state : RenderState) (tree : SyntaxTree.Tree)
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
            (appendedLines "" whitespace prepared.options.lineWidth).lineBreakCount
          else
            0
      | none => 0
  before.outputLineBreakCount + leadingBreakCount < after.outputLineBreakCount

def renderedSegmentIsMultiline
    (before after : RenderState) (segment : LineBreakRules.Segment)
    : Bool :=
  let leadingBreakCount :=
    match segmentFirstToken? segment with
    | some token =>
        let whitespace := before.defaultWhitespace token
        if hasLineBreakChar whitespace then
          (appendedLines "" whitespace before.options.lineWidth).lineBreakCount
        else
          0
    | none => 0
  before.outputLineBreakCount + leadingBreakCount < after.outputLineBreakCount

def RenderState.forFitProbe (state : RenderState) : RenderState :=
  {
    state with
      output := ""
      outputLineBreakCount := 0
      completedLineOverflowCount := 0
      introducedAtomicOverflowCount := 0
  }

def RenderState.hasBlankBoundaryBefore (state : RenderState) (tree : SyntaxTree.Tree)
    : Bool :=
  match state.lastToken?, SyntaxTree.Tree.firstToken? tree with
  | some left, some right =>
      let trivia := SyntaxTree.sourceText state.source left.span.stop right.span.start
      hasBlankLineStructure trivia
  | _, _ => false

def isProofTree (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node .proofBody _ => true
  | _ => false

def isQuotationTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.quot) _ => true
  | .node (.raw `Lean.Parser.Term.precheckedQuot) _ => true
  | .node (.raw `Lean.Parser.Command.quot) _ => true
  | .node (.raw `Lean.Parser.Tactic.quot) _ => true
  | .node (.raw `Lean.Parser.Tactic.quotSeq) _ => true
  | .node (.raw `token_antiquot) _ => true
  | .node (.raw `Qq.«termQ(__)») _ => true
  | .node kind _ =>
      let kindName := SyntaxTree.nodeKindName kind
      kindName == "antiquotName" || SpaceRules.containsSubstring kindName ".antiquot"
  | _ => false

partial def containsQuotationTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      isQuotationTree tree || children.any containsQuotationTree

partial def containsQuotationOutsideProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      if isProofTree tree then
        false
      else
        isQuotationTree tree || children.any containsQuotationOutsideProofTree

def isQqSyntaxTree : SyntaxTree.Tree → Bool
  | .node (.raw `Qq.«termQ(__)») _ => true
  | .node (.infixChain `Qq.«term_=Q_») _ => true
  | _ => false

def isProofWidgetsJsxSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "ProofWidgets.Jsx."
  | _ => false

def isLeanJsonSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "Lean.Json."
  | _ => false

def isBatteriesLibraryNoteSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "Batteries.Util.LibraryNote."
  | _ => false

def isLayoutSensitiveCommand : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Command.syntax) _ => true
  | .node (.raw `Lean.Parser.Command.syntaxAbbrev) _ => true
  | .node (.raw `Lean.Parser.Command.macro_rules) _ => true
  | .node (.raw `Lean.Parser.Command.elab) _ => true
  | .node (.raw `Lean.Parser.Command.elab_rules) _ => true
  | .node (.raw `Lean.Parser.«command_Simproc_decl_(_):=_») _ => true
  | .node (.raw `Lean.Parser.«command__Simproc__[_]_(_):=_») _ => true
  | .node (.raw `Batteries.Tactic.Alias.alias) _ => true
  | .node (.raw `Batteries.Tactic.Alias.aliasLR) _ => true
  | _ => false

def isMathlibTacticSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ => (SyntaxTree.nodeKindName kind).startsWith "Mathlib.Tactic."
  | _ => false

def isCalcTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.calc) _ => true
  | _ => false

def tokenHasCommentTrivia (token : SyntaxTree.Token) : Bool :=
  SpaceRules.hasCommentStart token.leading.text
  || SpaceRules.hasCommentStart token.trailing.text

partial def treeHasCommentTrivia : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => tokenHasCommentTrivia token
  | .node _ children => children.any treeHasCommentTrivia

def tokenHasLineBreakTrivia (token : SyntaxTree.Token) : Bool :=
  SpaceRules.hasLineStructure token.leading.text
  || SpaceRules.hasLineStructure token.trailing.text

partial def treeHasLineBreakTrivia : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => tokenHasLineBreakTrivia token
  | .node _ children => children.any treeHasLineBreakTrivia

def isCustomBracedTermSyntaxKindName (kindName : String) : Bool :=
  kindName != "«term{_}»"
  && (kindName.startsWith "«term" || SpaceRules.containsSubstring kindName ".«term")
  && SpaceRules.containsSubstring kindName "{_}"

def isCustomBracedTermSyntaxTree : SyntaxTree.Tree → Bool
  | tree@(.node kind _) =>
      isCustomBracedTermSyntaxKindName (SyntaxTree.nodeKindName kind)
      && treeHasLineBreakTrivia tree
  | _ => false

def isCustomSubalgebraAdjoinSyntaxTree : SyntaxTree.Tree → Bool
  | .node
      (.raw `Algebra.Subalgebra.AlgHom.Subalgebra.Subalgebra.Algebra.subalgebra_adjoin)
      _ =>
      true
  | _ => false

def isCommentSensitiveMatchExpr : SyntaxTree.Tree → Bool
  | tree@(.node (.raw `Lean.Parser.Term.matchExpr) _) =>
      treeHasCommentTrivia tree
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

def isDefinitionContainingQuotation (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node .definition _ => containsQuotationOutsideProofTree tree
  | .node (.raw `Lean.Parser.Command.definition) _ =>
      containsQuotationOutsideProofTree tree
  | .node (.raw `Lean.Parser.Command.abbrev) _ =>
      containsQuotationOutsideProofTree tree
  | .node (.raw `Lean.Parser.Command.declaration) _ =>
      containsQuotationOutsideProofTree tree
  | _ => false

def isQuotationLayoutIsland (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Term.set_option) _ => containsQuotationTree tree
  | _ => false

def isProofLayoutIsland (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Command.declValEqns) _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Term.structInst) _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Term.anonymousCtor) _ =>
      containsProofTree tree
  | .node (.raw `«term{_}») _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Command.whereStructInst) _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Term.show) _ =>
      containsProofTree tree
  | _ => false

def isProofLemmaCommand (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `lemma) _ =>
      LineBreakRules.treeFirstLexeme? tree == some "lemma" && containsProofTree tree
  | .node (.raw `group) _ =>
      LineBreakRules.treeFirstLexeme? tree == some "lemma" && containsProofTree tree
  | _ => false

def isAttributeModifierBlock (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Command.declModifiers) _ =>
      LineBreakRules.treeContainsLexeme "@[" tree
  | .node (.raw `Lean.Parser.Term.attributes) _ => true
  | _ => false

def ignoreNextMarker : String := "-- leanfmt: off next"

def isIgnoreNextTarget (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Module.module) _
  | .node (.raw `null) _ => false
  | .node _ _ =>
      tree.firstToken?.any fun token => token.leading.text.contains ignoreNextMarker
  | _ => false

def shouldEmitOriginalTree (tree : SyntaxTree.Tree) : Bool :=
  isIgnoreNextTarget tree
  || isProofTree tree
  || isProofLayoutIsland tree
  || isProofLemmaCommand tree
  || isAttributeModifierBlock tree
  || isDefinitionContainingQuotation tree
  || isCalcTree tree
  || isCommentSensitiveMatchExpr tree
  || isQuotationLayoutIsland tree
  || isQuotationTree tree
  || isQqSyntaxTree tree
  || isProofWidgetsJsxSyntaxTree tree
  || isLeanJsonSyntaxTree tree
  || isBatteriesLibraryNoteSyntaxTree tree
  || isLayoutSensitiveCommand tree
  || isMathlibTacticSyntaxTree tree
  || isCustomBracedTermSyntaxTree tree
  || isCustomSubalgebraAdjoinSyntaxTree tree
  || isSyntaxCommentTree tree

def shouldEmitOriginalChild
    (_parent : SyntaxTree.Tree) (_index : Nat) (child : SyntaxTree.Tree)
    : Bool :=
  shouldEmitOriginalTree child

partial def treeStartsWithOriginalEmission : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      if shouldEmitOriginalTree tree then
        true
      else
        let rec loop (index : Nat) : Bool :=
          match children[index]? with
          | some child =>
              if SyntaxTree.Tree.firstToken? child |>.isSome then
                treeStartsWithOriginalEmission child
              else
                loop (index + 1)
          | none => false
        loop 0

def RenderState.emitOriginalTree
    (state : RenderState) (tree : SyntaxTree.Tree)
    (respectPendingIndent : Bool := false)
    (rebaseSourceTextTargetColumn? : Option Nat := none)
    : RenderState :=
  match SyntaxTree.Tree.firstToken? tree, SyntaxTree.Tree.lastToken? tree with
  | some firstToken, some lastToken =>
      let usesPendingIndent :=
        (respectPendingIndent
          || isProofWidgetsJsxSyntaxTree tree
          || isQuotationTree tree
          || isSyntaxCommentTree tree)
        && state.pendingIndent?.isSome
      let originalLeading :=
        match state.lastToken? with
        | some leftToken =>
            SyntaxTree.sourceText state.source leftToken.span.stop firstToken.span.start
        | none => firstToken.leading.text
      let leading :=
        if usesPendingIndent then
          state.defaultWhitespace firstToken true
        else
          originalLeading
      let leadingColumn := lineWidth <| currentLineAfterAppend state.currentLine leading
      let sourceText :=
        SyntaxTree.sourceText state.source firstToken.span.start lastToken.span.stop
      let sourceColumn := originalColumnAt state.source firstToken.span.start
      let retainsRelativeLayout :=
        isProofTree tree || isProofWidgetsJsxSyntaxTree tree || isQuotationTree tree
      let inlineMultilineLayoutIsland :=
        retainsRelativeLayout
        && treeHasLineBreakTrivia tree
        && !SpaceRules.hasLineStructure originalLeading
      let inlineContinuationColumns? :=
        if !inlineMultilineLayoutIsland then
          none
        else
          match originalContinuationIndent? sourceText, state.lastToken? with
          | some sourceIndent, some leftToken =>
              let sourceAnchor := originalColumnAt state.source leftToken.span.start
              let outputAnchor := lineWidth state.currentLine - leftToken.lexeme.length
              let movedIndent :=
                shiftColumnByAnchor sourceAnchor outputAnchor sourceIndent
              let structuralIndent :=
                if isProofTree tree then
                  (state.segmentIndentation + 1) * indentationSpaces
                else if usesPendingIndent then
                  leadingColumn
                else
                  state.currentIndent
              some (sourceIndent, max movedIndent structuralIndent)
          | _, _ => none
      let sourceColumnRebasedFromLayoutBase :=
        shiftColumnByAnchor state.sourceLayoutBaseColumn
          state.outputLayoutBaseColumn sourceColumn
      let layoutTargetColumn? :=
        if !retainsRelativeLayout || inlineMultilineLayoutIsland then
          none
        else if usesPendingIndent then
          some leadingColumn
        else if SpaceRules.hasLineStructure originalLeading then
          some sourceColumnRebasedFromLayoutBase
        else
          none
      let targetColumn? :=
        rebaseSourceTextTargetColumn?.orElse fun _ => layoutTargetColumn?
      let targetColumn? :=
        if isProofTree tree && SpaceRules.hasLineStructure originalLeading then
          targetColumn?.map
            fun targetColumn =>
              max (state.segmentIndentation * indentationSpaces) targetColumn
        else
          targetColumn?
      let leading :=
        match targetColumn? with
        | some targetColumn =>
            rebaseOriginalTextIndent
              (if usesPendingIndent then leadingColumn else sourceColumn)
              targetColumn leading
        | none => leading
      let sourceText :=
        match inlineContinuationColumns?, rebaseSourceTextTargetColumn?,
              targetColumn? with
        | some (sourceIndent, targetIndent), _, _ =>
            if sourceIndent == targetIndent then
              sourceText
            else
              rebaseOriginalTreeText state.source tree sourceIndent targetIndent
        | none, some targetColumn, _ =>
            if sourceColumn == targetColumn then
              sourceText
            else
              rebaseOriginalTreeText state.source tree sourceColumn targetColumn
        | none, none, some targetColumn =>
            if sourceColumn == targetColumn then
              sourceText
            else
              rebaseOriginalTreeText state.source tree sourceColumn targetColumn
        | none, none, none => sourceText
      {
        state.appendOutput <| leading ++ sourceText with
          lastToken? := some lastToken
          pendingIndent? := none
          pendingCommandBoundary? := none
      }
  | _, _ => state

def originalTreeHasLineStructure (source : String) (tree : SyntaxTree.Tree) : Bool :=
  match SyntaxTree.Tree.firstToken? tree, SyntaxTree.Tree.lastToken? tree with
  | some firstToken, some lastToken =>
      SpaceRules.hasLineStructure
        (SyntaxTree.sourceText source firstToken.span.start lastToken.span.stop)
  | _, _ => false

/-! ## Flat rendering and fit measurement -/

partial def renderWithoutRuleBreaks
    (state : RenderState) (segment : LineBreakRules.Segment)
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
                renderWithoutRuleBreaks state (LineBreakRules.Segment.ofTree child)
          | none => state)
        state

def layoutProbeHasNotOverflowed (state : RenderState) : Bool :=
  state.completedLineOverflowCount == 0
  && lineFits state.currentLine state.options.lineWidth

partial def probeLayoutWithoutRuleBreaks?
    (state : RenderState) (segment : LineBreakRules.Segment)
    : Option RenderState :=
  match segment.parent with
  | .missing => some state
  | .leaf token =>
      let rendered := state.emitToken token false
      if layoutProbeHasNotOverflowed rendered then some rendered else none
  | .node _ _ =>
      let rec loop (state : RenderState) : List Nat → Option RenderState
        | [] => some state
        | index :: rest =>
            match segment.child? index with
            | none => loop state rest
            | some child =>
                let rendered? :=
                  if shouldEmitOriginalChild segment.parent index child then
                    let rendered := state.emitOriginalTree child
                    if layoutProbeHasNotOverflowed rendered then some rendered else none
                  else
                    probeLayoutWithoutRuleBreaks? state
                      (LineBreakRules.Segment.ofTree child)
                match rendered? with
                | some rendered => loop rendered rest
                | none => none
      loop state segment.indexes

def currentLineFitsWith (state : RenderState) (suffix : String) : Bool :=
  !introducesCompletedLineOverflow state.currentLine suffix state.options.lineWidth
  && lineFitsWithTrailingWidth
      (currentLineAfterAppend state.currentLine suffix) state.lineFitSuffixWidth
      state.options.lineWidth

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

def suffixMayContinueAcrossRuleBreak (segment : LineBreakRules.Segment) (index : Nat)
    : Bool :=
  match segment.child? index >>= SyntaxTree.Tree.firstToken? with
  | some token =>
      LineBreakRules.suffixTokenAction { ancestors := [] } token == .emit
  | none => false

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

def SuffixState.appendCommentTriviaBeforeToken
    (state : SuffixState) (token : SyntaxTree.Token)
    : SuffixState :=
  let trivia :=
    match state.widthState.lastToken? with
    | some left =>
        SyntaxTree.sourceText state.widthState.source left.span.stop token.span.start
    | none => token.leading.text
  if SpaceRules.hasCommentStart trivia then
    (state.appendText (state.widthState.defaultWhitespace token false)).1
  else
    state

def SuffixState.appendCommentTriviaBeforeTree
    (state : SuffixState) (tree : SyntaxTree.Tree)
    : SuffixState :=
  match SyntaxTree.Tree.firstToken? tree with
  | some token => state.appendCommentTriviaBeforeToken token
  | none => state

def SuffixState.emitOriginalFirstLine (state : SuffixState) (tree : SyntaxTree.Tree)
    : SuffixState × Bool :=
  match SyntaxTree.Tree.firstToken? tree, SyntaxTree.Tree.lastToken? tree with
  | some firstToken, some lastToken =>
      let text :=
        state.widthState.defaultWhitespace firstToken true
        ++ SyntaxTree.sourceText state.widthState.source firstToken.span.start
            lastToken.span.stop
      let (state, stopped) := state.appendText text
      let state :=
        if stopped then
          state
        else
          {
            state with
              widthState :=
                {
                  state.widthState with
                    lastToken? := some lastToken
                    pendingIndent? := none
                }
          }
      (state, stopped)
  | _, _ => (state, false)

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
      | .stop => (state.appendCommentTriviaBeforeToken token, true)
  | .node _ _ =>
      if shouldEmitOriginalTree tree then
        state.emitOriginalFirstLine tree
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
                      && hasRuleBreakAt context segment index
                      && !suffixMayContinueAcrossRuleBreak segment index then
                    (state.appendCommentTriviaBeforeTree child, true)
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
            pendingCommandBoundary? := none
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
              pendingCommandBoundary? := none
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
  let rec loop (suffixState : SuffixState) (nextIndex : Nat) : SuffixState × Bool :=
    if nextIndex < segment.stop then
      match segment.child? nextIndex with
      | some nextChild =>
          if suffixState.widthState.hasBlankBoundaryBefore nextChild then
            (suffixState.appendCommentTriviaBeforeTree nextChild, false)
          else
            let childContext := context.push segment nextIndex
            let (rendered, stopped) :=
              measureSuffixOfTree childContext suffixState nextChild
            if stopped then (rendered, false) else loop rendered (nextIndex + 1)
      | none => loop suffixState (nextIndex + 1)
    else
      let suffixState :=
        match segment.parentChild? segment.stop with
        | some nextChild => suffixState.appendCommentTriviaBeforeTree nextChild
        | none => suffixState
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
      if index < breakPoint.index
          && breakPoint.index < stop
          && !suffixMayContinueAcrossRuleBreak segment breakPoint.index then
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
  let (localSuffix, reachedEnd) := lineFitSuffixAfterChild state suffixSegment index child
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
  SpaceRules.hasLineStructure trivia

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

def contentChildIndexAtOrAfter? (segment : LineBreakRules.Segment) (index : Nat)
    : Option Nat :=
  segment.indexes.find?
    fun candidate =>
      index <= candidate
      && match segment.child? candidate with
          | some child => LineBreakRules.treeHasContent child
          | none => false

def tokenBoundaryAt? (segment : LineBreakRules.Segment) (index : Nat)
    : Option (SyntaxTree.Token × SyntaxTree.Token) := do
  let leftIndex ← LineBreakRules.previousContentIndex? segment index
  let rightIndex ← contentChildIndexAtOrAfter? segment index
  let leftTree ← segment.child? leftIndex
  let rightTree ← segment.child? rightIndex
  let leftToken ← SyntaxTree.Tree.lastToken? leftTree
  let rightToken ← SyntaxTree.Tree.firstToken? rightTree
  some (leftToken, rightToken)

def breakPointPreservesTightTokenBoundary
    (segment : LineBreakRules.Segment) (breakPoint : LineBreakRules.BreakPoint)
    : Bool :=
  match tokenBoundaryAt? segment breakPoint.index with
  | some (left, right) =>
      !SpaceRules.isTrailingSeparatorToken right.lexeme
      && !SpaceRules.preservesTightDotSpacing left right
      && !SpaceRules.preservesTightQuotedNameSpacing left right
      && !(left.span.stop == right.span.start
            && SpaceRules.preservesTightPostfixSpacing right)
  | none => true

def normalizeBreakPoints
    (segment : LineBreakRules.Segment) (breakPoints : List LineBreakRules.BreakPoint)
    : List LineBreakRules.BreakPoint :=
  (breakPoints.filter
    fun breakPoint =>
      segment.start <= breakPoint.index
      && breakPoint.index < segment.stop
      && breakPointPreservesTightTokenBoundary segment breakPoint)
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

def formattedWhitespaceKeepsSourceBreakAt
    (source : String) (segment : LineBreakRules.Segment) (index : Nat)
    : Bool :=
  match tokenBoundaryAt? segment index with
  | some (left, right) =>
      let originalTrivia := SyntaxTree.sourceText source left.span.stop right.span.start
      SpaceRules.hasCommentStart originalTrivia
      && SpaceRules.hasLineStructure originalTrivia
      && SpaceRules.hasLineStructure (SpaceRules.interTokenWhitespace source left right)
  | none => false

def sourceBreakBeforeSegmentStart? (state : RenderState)
    (segment : LineBreakRules.Segment)
    : Option SourceBreak := do
  let left ← state.lastToken?
  let right ← segmentFirstToken? segment
  let trivia := SyntaxTree.sourceText state.source left.span.stop right.span.start
  if SpaceRules.hasLineStructure trivia then
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

partial def segmentAllowsLayoutWithoutRuleBreaks
    (source : String) (context : LineBreakRules.RuleContext)
    (segment : LineBreakRules.Segment) (respectSourceBreaks : Bool := true)
    : Bool :=
  match segment.parent with
  | .missing => true
  | .leaf _ => true
  | .node _ _ =>
      if shouldEmitOriginalTree segment.parent then
        isAttributeModifierBlock segment.parent
        || isProofTree segment.parent
        || !originalTreeHasLineStructure source segment.parent
      else
        let rule := LineBreakRules.formattingRuleFor segment.parent
        if rule.mandatory context segment then
          false
        else
          match segment.singleChild? with
          | some (index, child) =>
              segmentAllowsLayoutWithoutRuleBreaks source (context.push segment index)
                (LineBreakRules.Segment.ofTree child)
          | none =>
              if respectSourceBreaks
                  && segmentHasAllowedSourceBreaks source context segment then
                false
              else
                let rec loop : List Nat → Bool
                  | [] => true
                  | index :: rest =>
                      match segment.child? index with
                      | none => true
                      | some child =>
                          segmentAllowsLayoutWithoutRuleBreaks source
                            (context.push segment index)
                            (LineBreakRules.Segment.ofTree child)
                          && loop rest
                loop segment.indexes

structure LayoutProbe where
  fits : Bool
  flat : Bool
  rendered? : Option RenderState := none

def RenderState.commitLayoutProbe (state : RenderState) (probe : LayoutProbe)
    : RenderState :=
  match probe.rendered? with
  | none => state
  | some rendered =>
      {
        state with
          output := state.output ++ rendered.output
          outputLineBreakCount :=
            state.outputLineBreakCount + rendered.outputLineBreakCount
          completedLineOverflowCount :=
            state.completedLineOverflowCount + rendered.completedLineOverflowCount
          introducedAtomicOverflowCount :=
            state.introducedAtomicOverflowCount + rendered.introducedAtomicOverflowCount
          currentLine := rendered.currentLine
          lastToken? := rendered.lastToken?
          pendingIndent? := rendered.pendingIndent?
          pendingCommandBoundary? := rendered.pendingCommandBoundary?
      }

def measureLayout
    (state : RenderState) (segment : LineBreakRules.Segment)
    (respectSourceBreaks : Bool := true)
    : LayoutProbe :=
  if !segmentAllowsLayoutWithoutRuleBreaks state.source state.context segment
        respectSourceBreaks then
    { fits := false, flat := false }
  else
    let probe := state.forFitProbe
    let rendered? :=
      if lineFits state.currentLine state.options.lineWidth then
        probeLayoutWithoutRuleBreaks? probe segment
      else
        some <| renderWithoutRuleBreaks probe segment
    match rendered? with
    | none => { fits := false, flat := false }
    | some rendered =>
        let fits :=
          if lineFits state.currentLine state.options.lineWidth then
            renderedCandidateFits probe rendered
          else
            currentLineFitsWith state rendered.output
        {
          fits
          flat := fits && !renderedSegmentIsMultiline probe rendered segment
          rendered? := some rendered
        }

def nestedLayoutFits (state : RenderState) (segment : LineBreakRules.Segment) : Bool :=
  (measureLayout state segment).fits

def LayoutProbe.acceptedForRule
    (probe : LayoutProbe)
    (isFlow : Bool) (breakPoints : List LineBreakRules.BreakPoint)
    : Bool :=
  if isFlow && breakPoints.any fun breakPoint => breakPoint.indentLevels == 0 then
    probe.flat
  else
    probe.fits

def segmentFirstTokenColumn (state : RenderState) (segment : LineBreakRules.Segment)
    : Nat :=
  match segmentFirstToken? segment with
  | some token => state.nextTokenColumn token
  | none => state.currentColumn

def RenderState.extendTailIndentation
    (state : RenderState) (_segment : LineBreakRules.Segment) (parentIndentation : Nat)
    : RenderState :=
  let inheritedIndentation :=
    match state.tailIndentation? with
    | some indentation => max indentation parentIndentation
    | none => parentIndentation
  { state with tailIndentation? := some inheritedIndentation }

def naturalRuleBreakBase
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn baseIndentation : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : SegmentBase :=
  let naturalIndentation :=
    if rule.roundUpBaseIndentation && 0 < breakPoint.indentLevels then
      max baseIndentation (indentationLevelForColumn (indentationPastColumn baseColumn))
    else
      baseIndentation
  { column := baseColumn, indentation := naturalIndentation }

def naturalBreakIndentation
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn baseIndentation : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : Nat :=
  let base := naturalRuleBreakBase rule baseColumn baseIndentation breakPoint
  indentationLevelForColumn <| breakIndent base.column base.indentation breakPoint

def leastNaturalBreakIndentation?
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn baseIndentation : Nat)
    : List LineBreakRules.BreakPoint → Option Nat
  | [] => none
  | breakPoint :: rest =>
      let indentation :=
        naturalBreakIndentation rule baseColumn baseIndentation breakPoint
      match leastNaturalBreakIndentation? rule baseColumn baseIndentation rest with
      | some minimum => some (min indentation minimum)
      | none => some indentation

def requiredTailIndentation
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn tailIndentation : Nat)
    : Nat :=
  if rule.liftsTailIndentation state.context segment
      || rule.flow state.context segment then
    let headIndentation := indentationLevelForColumn (indentationPastColumn baseColumn)
    max headIndentation (tailIndentation + 1)
  else
    tailIndentation

def computeRuleBreakShift
    (state : RenderState) (segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn baseIndentation : Nat)
    (points : List LineBreakRules.BreakPoint)
    : Nat :=
  match state.tailIndentation? with
  | some tailIndentation =>
      let required :=
        requiredTailIndentation state segment rule baseColumn tailIndentation
      let minimum? := leastNaturalBreakIndentation? rule baseColumn baseIndentation points
      required - minimum?.getD required
  | none => 0

def ruleBreakBase
    (state : RenderState) (_segment : LineBreakRules.Segment)
    (rule : LineBreakRules.LineBreakRule)
    (baseColumn baseIndentation : Nat)
    (breakPoint : LineBreakRules.BreakPoint)
    : SegmentBase :=
  let base :=
    if state.context.parentIsStructureWhereWrapper
        && state.context.parentStructureHasExtends
        && breakPoint.indentLevels == 0 then
      { column := 0, indentation := 0 }
    else
      naturalRuleBreakBase rule baseColumn baseIndentation breakPoint
  let shiftedIndentation :=
    if breakPoint.indentLevels == 0 then
      indentationLevelForColumn (breakIndent base.column base.indentation breakPoint)
      + state.breakIndentationShift
    else
      base.indentation + state.breakIndentationShift
  { base with indentation := shiftedIndentation }

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
  breakIndent base.column base.indentation breakPoint

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

def FlowRenderContext.measurePiece
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    : LayoutProbe :=
  measureLayout (flow.stateForPieceFit state index)
    (flow.segment.slice index (flow.nextBreakIndex index))
    false

def FlowRenderContext.measureChild
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    (context : LineBreakRules.RuleContext)
    (childSegment : LineBreakRules.Segment)
    (respectSourceBreaks : Bool := true)
    : LayoutProbe :=
  let probe := { flow.stateForPieceFit state index with context }
  measureLayout probe childSegment respectSourceBreaks

def FlowRenderContext.childFirstLineFits
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    (context : LineBreakRules.RuleContext) (child : SyntaxTree.Tree)
    : Bool :=
  let probe := { flow.stateForPieceFit state index with context }
  let (rendered, _) := renderFirstLineOfTree probe child
  !outputIntroducedLineBreak probe rendered
  && lineFitsWithTrailingWidth rendered.currentLine rendered.lineFitSuffixWidth
      rendered.options.lineWidth

def FlowRenderContext.withBreak
    (flow : FlowRenderContext) (state : RenderState)
    (breakPoint : LineBreakRules.BreakPoint)
    : RenderState :=
  let entryIndentation := flow.entryState.segmentIndentation
  let entryBaseColumn := flow.entryState.segmentBaseColumn
  let base :=
    ruleBreakBase flow.entryState flow.segment flow.rule
      entryBaseColumn entryIndentation breakPoint
  state.withRuleBreakIndent base.column base.indentation breakPoint

def FlowRenderContext.stateForForcedNestedChild?
    (flow : FlowRenderContext) (state : RenderState) (index : Nat)
    (breakAfterPreviousChild : Bool)
    (childFit : LayoutProbe) (pieceFit : LayoutProbe)
    : Option RenderState :=
  match flow.breakAt? index with
  | some breakPoint =>
      if index == flow.segment.start then
        if childFit.fits then
          some state
        else
          some
          <| state.withPendingIndent
              (state.currentIndent + breakPoint.indentLevels * indentationSpaces)
      else if breakAfterPreviousChild
              || !childFit.fits
              || formattedWhitespaceKeepsSourceBreakAt state.source flow.segment index
              || (breakPoint.indentLevels == 0 && !pieceFit.flat)
              || !pieceFit.fits then
        some <| flow.withBreak state breakPoint
      else
        none
  | none =>
      if index == flow.segment.start then some state else none

def segmentRangeFirstTree? (segment : LineBreakRules.Segment) (start stop : Nat)
    : Option SyntaxTree.Tree :=
  let rec loop (index : Nat) : Option SyntaxTree.Tree :=
    if index < stop then
      match segment.child? index with
      | some tree => if tree.firstToken?.isSome then some tree else loop (index + 1)
      | none => loop (index + 1)
    else
      none
  loop start

inductive CommandBoundaryPlan where
  | preserve
  | fixed (spacing : CommandBoundarySpacing)
  | blankLineIfMultiline

def commandBoundaryPlan
    (sequenceKind : LineBreakRules.TopLevelCommandSequenceKind)
    (previous current : LineBreakRules.TopLevelCommandKind)
    (previousMultiline : Bool)
    : CommandBoundaryPlan :=
  match sequenceKind with
  | .module | .header => .fixed .blankLine
  | .imports =>
      match previous, current with
      | .publicImport, .publicImport | .ordinaryImport, .ordinaryImport =>
          .fixed .lineBreak
      | _, _ => .fixed .blankLine
  | .commands =>
      match previous, current with
      | .moduleDoc, _ => .fixed .blankLine
      | .declaration, .declaration =>
          if previousMultiline then .fixed .blankLine else .blankLineIfMultiline
      | _, _ => .preserve

/-! ## Recursive rendering -/

mutual

  partial def renderSegment (state : RenderState) (segment : LineBreakRules.Segment)
      (prepared?
        : Option (LineBreakRules.LineBreakRule × List LineBreakRules.BreakPoint) := none)
      : RenderState :=
    let (rule, breakPoints) :=
      match prepared? with
      | some prepared => prepared
      | none =>
          let rule := LineBreakRules.formattingRuleFor segment.parent
          (rule, ruleBreakPoints state.context segment rule)
    let tailIndentationStop? :=
      match segment.parent with
      | .node _ children =>
          if segment.start == 0 && segment.stop == children.size then
            if rule.liftsTailIndentation state.context segment
                && segment.start < segment.stop then
              some (segment.stop - 1)
            else
              none
          else
            state.tailIndentationStop?
      | _ => none
    let state :=
      match segment.parent with
      | .node _ _ =>
          if rule.liftsTailIndentation state.context segment then
            match segmentFirstToken? segment with
            | some token =>
                let baseColumn := state.nextTokenColumn token
                {
                  state with
                    segmentBaseColumn := baseColumn
                    segmentIndentation := indentationLevelForColumn baseColumn
                }
            | none => state
          else
            state
      | _ => state
    let state :=
      match segment.parent with
      | .node _ children =>
          if segment.start == 0 && segment.stop == children.size then
            {
              state with
                breakIndentationShift :=
                  computeRuleBreakShift state segment rule state.segmentBaseColumn
                    state.segmentIndentation breakPoints
            }
          else
            state
      | _ => state
    let tailIndentationAnchors :=
      match segment.parent with
      | .node _ children =>
          if segment.start == 0
              && segment.stop == children.size
              && tailIndentationStop?.isSome then
            breakPoints.map
              fun breakPoint =>
                {
                  stop := breakPoint.index
                  indentation :=
                    indentationLevelForColumn
                      (breakPointIndent state segment rule breakPoint)
                }
          else
            state.tailIndentationAnchors
      | _ => []
    let state := { state with tailIndentationStop?, tailIndentationAnchors }
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
          renderSegmentByRule state segment rule breakPoints

  partial def renderSegmentByRule (state : RenderState) (segment : LineBreakRules.Segment)
      (rule : LineBreakRules.LineBreakRule)
      (breakPoints : List LineBreakRules.BreakPoint)
      : RenderState :=
    let isFlow := rule.flow state.context segment
    let useExistingBreaks := rule.useExistingBreaks state.context segment
    if rule.atomic then
      renderWithoutRuleBreaks state segment
    else if rule.mandatory state.context segment && !breakPoints.isEmpty then
      renderBalancedSegment state segment rule breakPoints
    else if breakPoints.isEmpty && !isFlow then
      renderChildren state segment
    else if useExistingBreaks then
      renderUsingExistingBreaks state segment rule breakPoints isFlow
    else
      let probe := measureLayout state segment false
      let hasRetainedSourceBreak :=
        breakPoints.any
          fun breakPoint =>
            formattedWhitespaceKeepsSourceBreakAt state.source segment breakPoint.index
      if probe.acceptedForRule isFlow breakPoints && !hasRetainedSourceBreak then
        state.commitLayoutProbe probe
      else if rule.preferChildLayouts state.context segment
              && !hasRetainedSourceBreak then
        match renderPreferredChildLayout? state segment breakPoints with
        | some childLayout => childLayout
        | none => renderAfterFlatFailure state segment rule breakPoints isFlow
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

  partial def renderPreferredChildLayout?
      (state : RenderState) (segment : LineBreakRules.Segment)
      (breakPoints : List LineBreakRules.BreakPoint)
      : Option RenderState :=
    let childLayout := renderChildren state segment
    let prefixStaysFlat :=
      match breakPoints.head? with
      | some breakPoint =>
          let prefixStop := min segment.stop (breakPoint.index + 1)
          let prefixSegment := segment.slice segment.start prefixStop
          let prefixRendered := renderSegmentRange state segment segment.start prefixStop
          !renderedSegmentIsMultiline state prefixRendered prefixSegment
      | none => true
    if prefixStaysFlat && renderedCandidateFits state childLayout then
      some childLayout
    else
      none

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
          let probe := measureLayout state segment false
          if probe.acceptedForRule isFlow breakPoints then
            state.commitLayoutProbe probe
          else if rule.preferChildLayouts state.context segment && !hasSourceBreaks then
            match renderPreferredChildLayout? state segment breakPoints with
            | some childLayout => childLayout
            | none => renderAfterFlatFailure state segment rule breakPoints isFlow
          else
            renderAfterFlatFailure state segment rule breakPoints isFlow

  partial def renderNestedSegment
      (state : RenderState) (segment : LineBreakRules.Segment) (index : Nat)
      (child : SyntaxTree.Tree) (suffixStop? : Option Nat := none)
      : RenderState :=
    let emitOriginal := shouldEmitOriginalChild segment.parent index child
    let state :=
      if emitOriginal || treeStartsWithOriginalEmission child then
        state
      else
        state.preserveBlankBoundaryBefore child
    let childContext := state.context.push segment index
    let childSegment := LineBreakRules.Segment.ofTree child
    let childRule := LineBreakRules.formattingRuleFor child
    let childBreakPoints :=
      if emitOriginal then [] else ruleBreakPoints childContext childSegment childRule
    let inheritsBase := childRule.inheritBase childContext childSegment
    let startAlignment := childRule.startAlignment childContext childSegment
    let suffixStop := suffixStop?.getD segment.stop
    let lineFitSuffix := lineFitSuffixForChild state segment index suffixStop child
    let state :=
      if inheritsBase || startAlignment == .none then
        state
      else if nestedLayoutFits
                {
                  state with
                    context := childContext, lineFitSuffixWidth := lineFitSuffix
                }
                childSegment then
        state
      else if startAlignment == .preferred && !state.allowsStartAlignment then
        state
      else
        let naturalStartColumn := state.segmentStartColumn childSegment
        let alignedStartColumn := indentationPastColumn naturalStartColumn
        state.appendOutput <| spaces (alignedStartColumn - naturalStartColumn)
    let firstToken? := SyntaxTree.Tree.firstToken? child
    let sourceLeading :=
      match state.lastToken?, firstToken? with
      | some leftToken, some firstToken =>
          SyntaxTree.sourceText state.source leftToken.span.stop firstToken.span.start
      | none, some firstToken => firstToken.leading.text
      | _, none => ""
    let startsOnNewSourceLine :=
      state.lastToken?.isNone || SpaceRules.hasLineStructure sourceLeading
    let sourceLayoutStart? :=
      if startsOnNewSourceLine then
        firstToken?.map
          fun _ =>
            let sourceColumn := lineWidth <| charsAfterLastNewline sourceLeading
            let parentRelativeColumn :=
              shiftColumnByAnchor state.sourceLayoutBaseColumn
                state.outputLayoutBaseColumn sourceColumn
            (sourceColumn, parentRelativeColumn)
      else
        none
    let parentRelativeOriginalColumn? := sourceLayoutStart?.map (·.2)
    let state :=
      match state.pendingIndent?, parentRelativeOriginalColumn? with
      | some desiredIndent, some targetColumn =>
          match child.singleToken? with
          | some token =>
              if desiredIndent + token.lexeme.length > state.options.lineWidth
                  && targetColumn + token.lexeme.length <= state.options.lineWidth then
                { state with pendingIndent? := some targetColumn }
              else
                state
          | none => state
      | _, _ => state
    let scope := ChildRenderScope.capture state
    let childBase :=
      if inheritsBase then
        { column := state.segmentBaseColumn, indentation := state.segmentIndentation }
      else
        state.segmentStartBaseFor childSegment
    let (sourceLayoutBaseColumn, outputLayoutBaseColumn) :=
      match sourceLayoutStart? with
      | some (sourceColumn, _) =>
          (sourceColumn, state.segmentStartColumn childSegment)
      | none => (state.sourceLayoutBaseColumn, state.outputLayoutBaseColumn)
    let childState :=
      {
        state with
          context := childContext
          segmentBaseColumn := childBase.column
          segmentIndentation := childBase.indentation
          sourceLayoutBaseColumn
          outputLayoutBaseColumn
          lineFitSuffixWidth := lineFitSuffix
          trace := state.trace.pushPath index
      }
    let childState :=
      if state.tailIndentationStop?.any fun stop => index < stop then
        let anchorIndentation :=
          match state.tailIndentationAnchors.find? fun anchor => index < anchor.stop with
          | some anchor => anchor.indentation
          | none => state.segmentIndentation
        childState.extendTailIndentation childSegment anchorIndentation
      else
        childState
    let rendered :=
      if emitOriginal then
        childState.emitOriginalTree child
          (respectPendingIndent :=
            isProofTree child
            || !startsOnNewSourceLine
            || isProofLemmaCommand child
            || state.pendingCommandBoundary?.isSome)
      else
        renderSegment childState childSegment (some (childRule, childBreakPoints))
    let rendered :=
      if !emitOriginal || !isProofWidgetsJsxSyntaxTree child then
        rendered
      else
        match parentRelativeOriginalColumn? with
        | none => rendered
        | some targetColumn =>
            let original :=
              childState.emitOriginalTree child
                (respectPendingIndent := true)
                (rebaseSourceTextTargetColumn? := some targetColumn)
            preferCandidateWithFewerOverflows childState rendered original
    let rendered :=
      if emitOriginal
          || rendered.introducedAtomicOverflowCount
              == childState.introducedAtomicOverflowCount
          || !LineBreakRules.canRetainParentRelativeOriginalLayoutForOverflow
                childContext child then
        rendered
      else
        match parentRelativeOriginalColumn? with
        | none => rendered
        | some targetColumn =>
            let original :=
              childState.emitOriginalTree child
                (respectPendingIndent := true)
                (rebaseSourceTextTargetColumn? := some targetColumn)
            preferCandidateWithFewerOverflows childState rendered original
    let rendered :=
      if emitOriginal
          || rendered.introducedAtomicOverflowCount
              == childState.introducedAtomicOverflowCount
          || !LineBreakRules.canRetainOriginalLayoutForOverflow childContext child then
        rendered
      else
        let targetColumn? :=
          sourceLayoutStart?.map
            fun (sourceColumn, _) =>
              shiftColumnByAnchor childState.sourceLayoutBaseColumn
                childState.outputLayoutBaseColumn sourceColumn
        if targetColumn? == parentRelativeOriginalColumn? then
          rendered
        else
          let original :=
            childState.emitOriginalTree child
              (respectPendingIndent := true)
              (rebaseSourceTextTargetColumn? := targetColumn?)
          preferCandidateWithFewerOverflows childState rendered original
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
    let rec loop (state : RenderState) (index : Nat) : RenderState :=
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
    let rec loop (state : RenderState) (index : Nat) : Option RenderState :=
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
          let childFit :=
            flow.measureChild state index childContext childSegment
              (index == flow.segment.start)
          let pieceFit :=
            if index == flow.segment.start || (flow.breakAt? index).isNone then
              childFit
            else
              flow.measurePiece state index
          let renderNestedAndContinue (state : RenderState) :=
            let before := state
            let rendered :=
              renderNestedSegment state flow.segment index child
                (some (flow.nextBreakIndex index))
            renderFlowChildren rendered flow (index + 1)
              (renderedTreeIsMultiline before rendered child)
          match flow.stateForForcedNestedChild? state index breakAfterPreviousChild
                  childFit pieceFit with
          | some state => renderNestedAndContinue state
          | none =>
              if segmentHasRuleSourceBreaks state.source childContext childSegment then
                renderNestedAndContinue state
              else if childFit.fits then
                renderFlowChildren (state.commitLayoutProbe childFit) flow (index + 1)
                  false
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
      let entryTailIndentation? := state.tailIndentation?
      let stateForPiece (state : RenderState) (firstPiece : Bool) : RenderState :=
        if firstPiece then
          { state with tailIndentation? := entryTailIndentation? }
        else
          { state with tailIndentation? := none }
      let renderPiece (state : RenderState) (start stop : Nat) (firstPiece : Bool)
          (preserveSuffix : Bool := false)
          : RenderState :=
        let state := stateForPiece state firstPiece
        let rendered :=
          if preserveSuffix then
            renderSegmentRange state segment start stop
          else
            renderSegmentRange { state with lineFitSuffixWidth := 0 } segment start stop
        {
          rendered with
            tailIndentation? := entryTailIndentation?
            lineFitSuffixWidth := state.lineFitSuffixWidth
        }
      let stateAfterBreak (rendered : RenderState)
          (breakPoint : LineBreakRules.BreakPoint)
          : RenderState :=
        let base :=
          ruleBreakBase rendered segment rule entryBaseColumn entryIndentation breakPoint
        rendered.withRuleBreakIndent base.column base.indentation breakPoint
      let rec renderOrdinaryPieces (state : RenderState) (start : Nat) (firstPiece : Bool)
          : List LineBreakRules.BreakPoint → RenderState
        | [] => renderPiece state start segment.stop firstPiece true
        | breakPoint :: rest =>
            let rendered := renderPiece state start breakPoint.index firstPiece
            let rest := rest.dropWhile fun next => next.index == breakPoint.index
            renderOrdinaryPieces (stateAfterBreak rendered breakPoint)
              breakPoint.index false rest
      let rec renderCommandPieces
          (state : RenderState) (start : Nat) (firstPiece : Bool)
          (sequenceKind : LineBreakRules.TopLevelCommandSequenceKind)
          (previousKind? : Option LineBreakRules.TopLevelCommandKind)
          (previousMultiline : Bool)
          : List LineBreakRules.BreakPoint → RenderState
        | breaks =>
            let stop := breaks.head?.map (·.index) |>.getD segment.stop
            let finalPiece := breaks.isEmpty
            let currentTree? := segmentRangeFirstTree? segment start stop
            let currentKind? := currentTree?.map LineBreakRules.topLevelCommandKind
            let boundaryPlan :=
              match previousKind?, currentKind? with
              | some previousKind, some currentKind =>
                  commandBoundaryPlan sequenceKind previousKind currentKind
                    previousMultiline
              | _, _ => .preserve
            let pieceState :=
              match boundaryPlan with
              | .fixed spacing => { state with pendingCommandBoundary? := some spacing }
              | .preserve | .blankLineIfMultiline => state
            let rendered := renderPiece pieceState start stop firstPiece finalPiece
            let currentMultiline :=
              match currentTree? with
              | some tree => renderedTreeIsMultiline pieceState rendered tree
              | none => false
            let rendered :=
              match boundaryPlan, currentMultiline, currentTree? with
              | .blankLineIfMultiline, true, some tree =>
                  state.ensureBlankCommandBoundaryBeforeRenderedTree rendered tree
              | _, _, _ => rendered
            match breaks with
            | [] => rendered
            | breakPoint :: rest =>
                let rest := rest.dropWhile fun next => next.index == breakPoint.index
                renderCommandPieces (stateAfterBreak rendered breakPoint)
                  breakPoint.index false sequenceKind currentKind? currentMultiline rest
      match LineBreakRules.topLevelCommandSequenceKind? state.context segment with
      | some sequenceKind =>
          renderCommandPieces state segment.start true sequenceKind none false breakPoints
      | none => renderOrdinaryPieces state segment.start true breakPoints

end

def RenderState.finalTrivia (state : RenderState) : String :=
  match state.lastToken? with
  | some token =>
      SpaceRules.cleanFinalTrivia
      <| SyntaxTree.sourceText state.source token.span.stop state.source.endPos.offset
  | none =>
      SpaceRules.cleanFinalTrivia state.source

def renderModuleTree (moduleTree : SyntaxTree.Module) (options : Options := {})
    : String :=
  let state :=
    renderSegment { options, source := moduleTree.source }
      (LineBreakRules.Segment.ofTree moduleTree.tree)
  SpaceRules.normalizeFinalNewline (state.output ++ state.finalTrivia)

def renderModuleTreeWithTrace (moduleTree : SyntaxTree.Module) (options : Options := {})
    : String × String :=
  let state :=
    renderSegment
      { options, source := moduleTree.source, trace := { enabled := true } }
      (LineBreakRules.Segment.ofTree moduleTree.tree)
  let formatted := SpaceRules.normalizeFinalNewline (state.output ++ state.finalTrivia)
  (formatted, state.trace.formatWithOutput formatted)

end Formatter
end LeanFmt
