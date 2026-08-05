import LeanFmt.Formatter.LineBreakRules
import LeanFmt.Formatter.SpaceRules

namespace LeanFmt
namespace Formatter
namespace OriginalTree

def indentationSpaces : Nat :=
  2

private def lineWidth (text : String) : Nat :=
  text.length

private def spaces (count : Nat) : String :=
  String.ofList <| List.replicate count ' '

private def charsAfterLastNewline (text : String) : String :=
  let rec loop : List Char → List Char → String
    | [], current => String.ofList current.reverse
    | '\n' :: rest, _ => loop rest []
    | char :: rest, current => loop rest (char :: current)
  loop (SpaceRules.normalizeLineEndings text).toList []

private def shiftColumnByAnchor (sourceAnchorColumn outputAnchorColumn sourceColumn : Nat)
    : Nat :=
  if sourceAnchorColumn <= outputAnchorColumn then
    sourceColumn + (outputAnchorColumn - sourceAnchorColumn)
  else
    sourceColumn - min sourceColumn (sourceAnchorColumn - outputAnchorColumn)

private def leadingWhitespace (line : String) : String :=
  (line.takeWhile SpaceRules.isHorizontalWhitespace).toString

private def shiftLineIndent (sourceColumn targetColumn : Nat) (line : String) : String :=
  if line.isEmpty then
    line
  else if sourceColumn <= targetColumn then
    spaces (targetColumn - sourceColumn) ++ line
  else
    let removeCount := min (sourceColumn - targetColumn) (leadingWhitespace line).length
    (line.drop removeCount).toString

private def shiftBoundaryIndent (sourceColumn targetColumn : Nat) (line : String)
    : String :=
  if line.isEmpty && sourceColumn <= targetColumn then
    spaces (targetColumn - sourceColumn)
  else
    shiftLineIndent sourceColumn targetColumn line

private def rebaseLines (sourceColumn targetColumn : Nat) : List String → List String
  | [] => []
  | [line] => [shiftBoundaryIndent sourceColumn targetColumn line]
  | line :: rest =>
      shiftLineIndent sourceColumn targetColumn line
      :: rebaseLines sourceColumn targetColumn rest

private def rebaseTextIndent (sourceColumn targetColumn : Nat) (text : String) : String :=
  if sourceColumn == targetColumn then
    text
  else
    match (SpaceRules.normalizeLineEndings text).splitOn "\n" with
    | [] => text
    | first :: rest =>
        String.intercalate "\n" <| first :: rebaseLines sourceColumn targetColumn rest

def sourceContinuationIndent? (text : String) : Option Nat :=
  (SpaceRules.normalizeLineEndings text).splitOn "\n"
  |>.drop 1
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

private def treeContinuationIndent?
    (sourceMap : SyntaxTree.SourcePositionMap) (tree : SyntaxTree.Tree)
    : Option Nat := do
  let firstToken ← tree.firstToken?
  let firstLine := sourceMap.lineNumberAt firstToken.span.start
  tree.tokens.foldl
    (fun minimum? token =>
      if firstLine < sourceMap.lineNumberAt token.span.start then
        let column := sourceMap.columnAt token.span.start
        match minimum? with
        | some minimum => some (min minimum column)
        | none => some column
      else
        minimum?)
    none

private def rebaseMultilineSourceSlice (targetColumn : Nat) (text : String) : String :=
  match (SpaceRules.normalizeLineEndings text).splitOn "\n" with
  | [] | [_] => text
  | first :: rest =>
      let sourceContinuationColumn := (sourceContinuationIndent? text).getD targetColumn
      String.intercalate "\n"
      <| first :: rebaseLines sourceContinuationColumn targetColumn rest

private def rebaseTokenLexeme (sourceColumn targetColumn : Nat) (token : SyntaxTree.Token)
    : String :=
  if SpaceRules.isCommentLexeme token.lexeme
      && SpaceRules.hasLineStructure token.lexeme then
    SpaceRules.reindentCommentLexeme token.lexeme sourceColumn targetColumn
  else
    token.lexeme

private inductive RebaseUnit where
  | sourceToken (token : SyntaxTree.Token)
  | syntaxComment (span : SyntaxTree.Span)

private def RebaseUnit.span : RebaseUnit → SyntaxTree.Span
  | .sourceToken token => token.span
  | .syntaxComment span => span

private partial def rebaseUnits
    : List SyntaxTree.Token → List SyntaxTree.Span → List RebaseUnit
  | [], _ => []
  | token :: tokens, [] => .sourceToken token :: rebaseUnits tokens []
  | token :: tokens, span :: spans =>
      if span.stop <= token.span.start then
        rebaseUnits (token :: tokens) spans
      else if span.start == token.span.start then
        let remaining := tokens.dropWhile fun token => token.span.stop <= span.stop
        .syntaxComment span :: rebaseUnits remaining spans
      else
        .sourceToken token :: rebaseUnits tokens (span :: spans)

private def columnAfterAppend (column : Nat) (text : String) : Nat :=
  if SpaceRules.hasLineStructure text then
    lineWidth <| charsAfterLastNewline text
  else
    column + lineWidth text

private def rebaseTreeText
    (source : String) (sourceMap : SyntaxTree.SourcePositionMap)
    (tree : SyntaxTree.Tree)
    (sourceColumn targetColumn : Nat)
    (rebaseTrivia : Bool := true)
    : String :=
  let rec loop (cursor : String.Pos.Raw) (outputColumn : Nat) (parts : List String)
      : List RebaseUnit → List String
    | [] => parts
    | unit :: rest =>
        let span := unit.span
        let trivia := SyntaxTree.sourceText source cursor span.start
        let trivia :=
          if rebaseTrivia then
            rebaseTextIndent sourceColumn targetColumn trivia
          else
            trivia
        let outputColumn := columnAfterAppend outputColumn trivia
        let text :=
          match unit with
          | .sourceToken token =>
              rebaseTokenLexeme (sourceMap.columnAt token.span.start) outputColumn token
          | .syntaxComment span =>
              let comment := SyntaxTree.sourceText source span.start span.stop
              if SpaceRules.hasLineStructure trivia then
                rebaseMultilineSourceSlice outputColumn comment
              else
                rebaseTextIndent (sourceMap.columnAt span.start) outputColumn comment
        loop span.stop (columnAfterAppend outputColumn text) (text :: trivia :: parts)
          rest
  match rebaseUnits tree.tokens.toList tree.syntaxCommentSpans with
  | [] => ""
  | units@(first :: _) =>
      String.join <| (loop first.span.start targetColumn [] units).reverse

private def fittingTargetColumn
    (source : String) (sourceMap : SyntaxTree.SourcePositionMap)
    (tree : SyntaxTree.Tree) (sourceText : String)
    (sourceColumn targetColumn lineWidthLimit suffixWidth : Nat)
    : Nat :=
  if targetColumn <= sourceColumn then
    targetColumn
  else
    let rebasedText := rebaseTreeText source sourceMap tree sourceColumn targetColumn
    let sourceLines := (SpaceRules.normalizeLineEndings sourceText).splitOn "\n"
    let rebasedLines := (SpaceRules.normalizeLineEndings rebasedText).splitOn "\n"
    let rec maximumOverflow (lineIndex maximum : Nat) : List String → List String → Nat
      | sourceLine :: sourceRest, rebasedLine :: rebasedRest =>
          let sourceWidth :=
            sourceLine.length
            + (if lineIndex == 0 then sourceColumn else 0)
            + (if sourceRest.isEmpty then suffixWidth else 0)
          let rebasedWidth :=
            rebasedLine.length
            + (if lineIndex == 0 then targetColumn else 0)
            + (if rebasedRest.isEmpty then suffixWidth else 0)
          let allowedWidth := max lineWidthLimit sourceWidth
          let overflow :=
            if allowedWidth < rebasedWidth then
              rebasedWidth - allowedWidth
            else
              0
          maximumOverflow (lineIndex + 1) (max maximum overflow) sourceRest rebasedRest
      | _, _ => maximum
    let overflow := maximumOverflow 0 0 sourceLines rebasedLines
    let roundedReduction :=
      ((overflow + indentationSpaces - 1) / indentationSpaces) * indentationSpaces
    targetColumn - min (targetColumn - sourceColumn) roundedReduction

private def currentLineAfterAppend (currentLine text : String) : String :=
  if text.contains '\n' || text.contains '\r' then
    charsAfterLastNewline text
  else
    currentLine ++ text

private def tokenStartsCurrentLine (currentLine : String) (token : SyntaxTree.Token)
    : Bool :=
  if !currentLine.endsWith token.lexeme then
    false
  else
    let prefixLength := currentLine.length - token.lexeme.length
    (currentLine.take prefixLength).all SpaceRules.isHorizontalWhitespace

private def bodyColumnAfterOpeningDelimiter?
    (currentLine : String) (token : SyntaxTree.Token)
    : Option Nat :=
  if !currentLine.endsWith token.lexeme then
    none
  else
    let prefixLength := currentLine.length - token.lexeme.length
    let precedingText :=
      SpaceRules.stripLineEndWhitespace <| (currentLine.take prefixLength).toString
    if LineBreakRules.suffixOpeningDelimiterLexeme precedingText then
      some (precedingText.length - 1 + indentationSpaces)
    else
      none

private def isProofBodyTree (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.proofBody _) _ => true
  | _ => false

private def proofBodyContainsTacticLayoutOwner : SyntaxTree.Tree → Bool
  | .node (.proofBody containsOwner) _ => containsOwner
  | _ => false

private def isQuotationTree : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.quot) _ => true
  | .node (.raw `Lean.Parser.Term.precheckedQuot) _ => true
  | .node (.raw `Lean.Parser.Command.quot) _ => true
  | .node (.raw `Lean.Parser.Tactic.quot) _ => true
  | .node (.raw `Lean.Parser.Tactic.quotSeq) _ => true
  | .node (.tactic `Lean.Parser.Tactic.quot _ _ _) _ => true
  | .node (.tactic `Lean.Parser.Tactic.quotSeq _ _ _) _ => true
  | .node (.raw `token_antiquot) _ => true
  | .node (.raw `Qq.«termQ(__)») _ => true
  | .node kind _ =>
      let kindName := SyntaxTree.nodeKindName kind
      kindName == "antiquotName" || SpaceRules.containsSubstring kindName ".antiquot"
  | _ => false

private partial def containsQuotationTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      isQuotationTree tree || children.any containsQuotationTree

private partial def containsQuotationOutsideProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      if isProofBodyTree tree then
        false
      else
        isQuotationTree tree || children.any containsQuotationOutsideProofTree

private def isQqSyntaxTree : SyntaxTree.Tree → Bool
  | .node (.raw `Qq.«termQ(__)») _ => true
  | .node (.infixChain `Qq.«term_=Q_») _ => true
  | _ => false

private def isProofWidgetsJsxSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "ProofWidgets.Jsx."
  | _ => false

private def isLeanJsonSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "Lean.Json."
  | _ => false

private def isBatteriesLibraryNoteSyntaxTree : SyntaxTree.Tree → Bool
  | .node kind _ =>
      (SyntaxTree.nodeKindName kind).startsWith "Batteries.Util.LibraryNote."
  | _ => false

private def macroPatternHasLineStructure : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Command.macro) children =>
      match children.findIdx?
              fun child => LineBreakRules.treeFirstLexeme? child == some "macro",
            children.findIdx?
              fun child =>
                match child with
                | .node (.raw `Lean.Parser.Command.macroTail) _ => true
                | _ => false with
      | some macroIndex, some tailIndex =>
          let tokens :=
            List.range' (macroIndex + 1) (tailIndex - (macroIndex + 1))
            |>.flatMap
                fun index =>
                  match children[index]? with
                  | some child => child.tokens.toList
                  | none => []
          (tokens.drop 1).any
            (fun token => SpaceRules.hasLineStructure token.leading.text)
          || tokens.dropLast.any
              fun token => SpaceRules.hasLineStructure token.trailing.text
      | _, _ => false
  | _ => false

private def isLayoutSensitiveCommand : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Command.syntax) _ => true
  | .node (.raw `Lean.Parser.Command.syntaxAbbrev) _ => true
  | tree@(.node (.raw `Lean.Parser.Command.macro) _) =>
      macroPatternHasLineStructure tree
  | .node (.raw `Lean.Parser.Command.macro_rules) _ => true
  | .node (.raw `Lean.Parser.Command.elab) _ => true
  | .node (.raw `Lean.Parser.Command.elab_rules) _ => true
  | .node (.raw `Lean.Parser.«command_Simproc_decl_(_):=_») _ => true
  | .node (.raw `Lean.Parser.«command__Simproc__[_]_(_):=_») _ => true
  | .node (.raw `Lean.Parser.«command_Dsimproc_decl_(_):=_») _ => true
  | .node (.raw `Lean.Parser.«command__Dsimproc__[_]_(_):=_») _ => true
  | .node (.raw `Lean.runCmd) _ => true
  | .node (.raw `Batteries.Tactic.Alias.alias) _ => true
  | .node (.raw `Batteries.Tactic.Alias.aliasLR) _ => true
  | _ => false

private def isTacticSequenceKind (kind : Lean.SyntaxNodeKind) : Bool :=
  SyntaxTree.Tree.isTacticSequenceKind kind

private def coreTacticKindName (kindName : String) : Bool :=
  SyntaxTree.isCoreTacticKindName kindName

private def isCalcTree : SyntaxTree.Tree → Bool
  | tree => SyntaxTree.Tree.isCalcTree tree

private def isTacticKindName (kindName : String) : Bool :=
  coreTacticKindName kindName || SyntaxTree.isExtensionTacticKindName kindName

private def isProtectedTacticTree : SyntaxTree.Tree → Bool
  | .node (.raw `Mathlib.Tactic.dsimpPercent) _ => false
  | .node (.tactic `Mathlib.Tactic.dsimpPercent _ _ _) _ => false
  | tree@(.node kind _) =>
      let kindName := SyntaxTree.nodeKindName kind
      if isQuotationTree tree then
        false
      else if isTacticKindName kindName then
        match kind with
        | .tactic rawKind _ isOwner _ =>
            !isTacticSequenceKind rawKind && !isOwner
        | .raw rawKind =>
            !isTacticSequenceKind rawKind && !SyntaxTree.Tree.isTacticLayoutOwner tree
        | _ => true
      else
        false
  | _ => false

private def tokenHasCommentTrivia (token : SyntaxTree.Token) : Bool :=
  SpaceRules.hasCommentStart token.leading.text
  || SpaceRules.hasCommentStart token.trailing.text

private partial def treeHasCommentTrivia : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => tokenHasCommentTrivia token
  | .node _ children => children.any treeHasCommentTrivia

private def tokenHasLineBreakTrivia (token : SyntaxTree.Token) : Bool :=
  SpaceRules.hasLineStructure token.leading.text
  || SpaceRules.hasLineStructure token.trailing.text

private partial def treeHasLineBreakTrivia : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf token => tokenHasLineBreakTrivia token
  | .node _ children => children.any treeHasLineBreakTrivia

private def treeHasInternalLineBreakTrivia (tree : SyntaxTree.Tree) : Bool :=
  match tree.tokens.toList with
  | [] | [_] => false
  | tokens =>
      let internalLeadingHasLineBreak :=
        tokens.drop 1
        |>.any
            fun token =>
              SpaceRules.hasLineStructure token.leading.text
      let internalTrailingHasLineBreak :=
        tokens.dropLast.any
          fun token =>
            SpaceRules.hasLineStructure token.trailing.text
      internalLeadingHasLineBreak || internalTrailingHasLineBreak

private def isCustomBracedTermSyntaxKindName (kindName : String) : Bool :=
  kindName != "«term{_}»"
  && (kindName.startsWith "«term" || SpaceRules.containsSubstring kindName ".«term")
  && SpaceRules.containsSubstring kindName "{_}"

private def isCustomBracedTermSyntaxTree : SyntaxTree.Tree → Bool
  | tree@(.node kind _) =>
      isCustomBracedTermSyntaxKindName (SyntaxTree.nodeKindName kind)
      && treeHasLineBreakTrivia tree
  | _ => false

private def isCustomSubalgebraAdjoinSyntaxTree : SyntaxTree.Tree → Bool
  | .node
      (.raw `Algebra.Subalgebra.AlgHom.Subalgebra.Subalgebra.Algebra.subalgebra_adjoin)
      _ =>
      true
  | _ => false

private def isCommentSensitiveMatchExpr : SyntaxTree.Tree → Bool
  | tree@(.node (.raw `Lean.Parser.Term.matchExpr) _) =>
      treeHasCommentTrivia tree
  | _ => false

private def isSyntaxCommentTree : SyntaxTree.Tree → Bool
  | .node (.raw kind) _ => SyntaxTree.isSyntaxCommentKind kind
  | _ => false

private partial def containsProofTree : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      isProofBodyTree tree || children.any containsProofTree

private def isProofLambdaTree (tree : SyntaxTree.Tree) : Bool :=
  LineBreakRules.treeFirstLexeme? tree == some "fun" && containsProofTree tree

private def isDefinitionContainingQuotation (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node .definition _ => containsQuotationOutsideProofTree tree
  | .node (.raw `Lean.Parser.Command.definition) _ =>
      containsQuotationOutsideProofTree tree
  | .node (.raw `Lean.Parser.Command.abbrev) _ =>
      containsQuotationOutsideProofTree tree
  | .node (.raw `Lean.Parser.Command.declaration) _ =>
      containsQuotationOutsideProofTree tree
  | _ => false

private def isQuotationLayoutIsland (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Term.set_option) _ =>
      containsQuotationTree tree
  | _ => false

private def isProofLayoutIsland (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node .application children =>
      let rec laterArgumentHasProofLambda (previous : List SyntaxTree.Tree)
          : List SyntaxTree.Tree → Bool
        | [] => false
        | argument :: rest =>
            (isProofLambdaTree argument
              && previous.any
                  fun previousArgument =>
                    containsProofTree previousArgument
                    && treeHasInternalLineBreakTrivia previousArgument)
            || laterArgumentHasProofLambda (argument :: previous) rest
      match children.toList.drop 1 with
      | [] | [_] => false
      | first :: rest => laterArgumentHasProofLambda [first] rest
  | .node (.raw `Lean.Parser.Command.declValEqns) _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Term.structInst) _ =>
      containsProofTree tree
  | .node (.raw `«term{_}») _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Command.whereStructInst) _ =>
      containsProofTree tree
  | .node (.raw `Lean.Parser.Term.show) _ =>
      containsProofTree tree
  | _ => false

private def proofLayoutRebasesFromFirstToken : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.structInst) _
  | .node (.raw `Lean.Parser.Term.anonymousCtor) _
  | .node (.raw `«term{_}») _
  | .node (.raw `Lean.Parser.Command.whereStructInst) _ => true
  | _ => false

private def isProofLemmaCommand (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `lemma) _ =>
      LineBreakRules.treeFirstLexeme? tree == some "lemma" && containsProofTree tree
  | .node (.raw `group) _ =>
      LineBreakRules.treeFirstLexeme? tree == some "lemma" && containsProofTree tree
  | _ => false

private partial def containsTransparentTacticLayoutOwner : SyntaxTree.Tree → Bool
  | .node kind children =>
      let tree := SyntaxTree.Tree.node kind children
      if isCalcTree tree || isProtectedTacticTree tree then
        false
      else
        tree.isTacticLayoutOwner || children.any containsTransparentTacticLayoutOwner
  | _ => false

private def isAttributeModifierBlock (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Command.declModifiers) _ =>
      LineBreakRules.treeContainsLexeme "@[" tree
  | .node (.raw `Lean.Parser.Term.attributes) _ => true
  | _ => false

private def ignoreNextMarker : String :=
  "-- leanfmt: off next"

private def isIgnoreNextTarget (tree : SyntaxTree.Tree) : Bool :=
  match tree with
  | .node (.raw `Lean.Parser.Module.module) _
  | .node (.raw `null) _ => false
  | .node _ _ =>
      tree.firstToken?.any fun token => token.leading.text.contains ignoreNextMarker
  | _ => false

inductive LayoutIslandKind where
  | ignored
  | proof
  | proofLayout
  | proofLemma
  | attributes
  | definitionQuotation
  | calc
  | commentSensitiveMatch
  | quotationLayout
  | quotation
  | qq
  | proofWidgetsJsx
  | leanJson
  | batteriesLibraryNote
  | layoutSensitiveCommand
  | mathlibTactic
  | customBracedTerm
  | customSubalgebraAdjoin
  | syntaxComment
deriving BEq, Repr

def classify? (tree : SyntaxTree.Tree) : Option LayoutIslandKind :=
  if isIgnoreNextTarget tree then
    some .ignored
  else if isProofBodyTree tree && !proofBodyContainsTacticLayoutOwner tree then
    some .proof
  else if isProtectedTacticTree tree then
    some .mathlibTactic
  else if isProofLayoutIsland tree then
    some .proofLayout
  else if isProofLemmaCommand tree && !containsTransparentTacticLayoutOwner tree then
    some .proofLemma
  else if isAttributeModifierBlock tree then
    some .attributes
  else if isDefinitionContainingQuotation tree then
    some .definitionQuotation
  else if isCalcTree tree then
    some .calc
  else if isCommentSensitiveMatchExpr tree then
    some .commentSensitiveMatch
  else if isQuotationLayoutIsland tree then
    some .quotationLayout
  else if isQuotationTree tree then
    some .quotation
  else if isQqSyntaxTree tree then
    some .qq
  else if isProofWidgetsJsxSyntaxTree tree then
    some .proofWidgetsJsx
  else if isLeanJsonSyntaxTree tree then
    some .leanJson
  else if isBatteriesLibraryNoteSyntaxTree tree then
    some .batteriesLibraryNote
  else if isLayoutSensitiveCommand tree then
    some .layoutSensitiveCommand
  else if isCustomBracedTermSyntaxTree tree then
    some .customBracedTerm
  else if isCustomSubalgebraAdjoinSyntaxTree tree then
    some .customSubalgebraAdjoin
  else if isSyntaxCommentTree tree then
    some .syntaxComment
  else
    none

@[inline]
def shouldEmit (tree : SyntaxTree.Tree) : Bool :=
  (classify? tree).isSome

def LayoutIslandKind.preservesMultilineLayoutWithoutRuleBreaks : LayoutIslandKind → Bool
  | .proof | .attributes => true
  | _ => false

def LayoutIslandKind.prefersParentRelativeColumn : LayoutIslandKind → Bool
  | .proofWidgetsJsx => true
  | _ => false

def LayoutIslandKind.hasUnbreakableLineLayout : LayoutIslandKind → Bool
  | .proof
  | .proofLayout
  | .calc
  | .quotationLayout
  | .quotation
  | .proofWidgetsJsx => true
  | _ => false

def LayoutIslandKind.isProof : LayoutIslandKind → Bool
  | .proof => true
  | _ => false

def LayoutIslandKind.isQuotation : LayoutIslandKind → Bool
  | .quotationLayout | .quotation => true
  | _ => false

def LayoutIslandKind.isProofLayout : LayoutIslandKind → Bool
  | .proofLayout => true
  | _ => false

def LayoutIslandKind.isCalc : LayoutIslandKind → Bool
  | .calc => true
  | _ => false

def LayoutIslandKind.retainsRelativeLayout : LayoutIslandKind → Bool
  | .proof
  | .quotationLayout
  | .quotation
  | .proofWidgetsJsx
  | .mathlibTactic
  | .layoutSensitiveCommand => true
  | _ => false

def LayoutIslandKind.usesPendingIndent : LayoutIslandKind → Bool
  | .proof
  | .proofLemma
  | .proofWidgetsJsx
  | .quotationLayout
  | .quotation
  | .mathlibTactic
  | .layoutSensitiveCommand
  | .syntaxComment => true
  | _ => false

def LayoutIslandKind.preservesFollowingCommentIndent : LayoutIslandKind → Bool
  | .proof | .layoutSensitiveCommand => true
  | _ => false

def LayoutIslandKind.formatsLeadingBoundary : LayoutIslandKind → Bool
  | .calc => true
  | _ => false

def canUseStructuralOverflowFallback : SyntaxTree.Tree → Bool
  | .node (.raw `Lean.Parser.Term.anonymousCtor) _
  | .node (.raw `Lean.Parser.Term.structInst) _ => true
  | _ => false

def canUseStructuralLayoutAfterParentMove : SyntaxTree.Tree → Bool
  | .node .application _
  | .node (.raw `Lean.Parser.Term.anonymousCtor) _
  | .node (.raw `Lean.Parser.Term.structInst) _
  | .node (.raw `«term{_}») _
  | .node (.raw `Lean.Parser.Command.whereStructInst) _ => true
  | _ => false

partial def startsWithEmission : SyntaxTree.Tree → Bool
  | .missing => false
  | .leaf _ => false
  | tree@(.node _ children) =>
      if (classify? tree).isSome then
        true
      else
        let rec loop (index : Nat) : Bool :=
          match children[index]? with
          | some child =>
              if SyntaxTree.Tree.firstToken? child |>.isSome then
                startsWithEmission child
              else
                loop (index + 1)
          | none => false
        loop 0

structure EmissionRequest where
  source : String
  sourceMap : SyntaxTree.SourcePositionMap
  currentLine : String
  currentIndent : Nat
  lastToken? : Option SyntaxTree.Token
  formattedLeadingWhitespace? : Option String
  pendingLeadingWhitespace? : Option String
  segmentIndentation : Nat
  sourceLayoutBaseColumn : Nat
  outputLayoutBaseColumn : Nat
  lineWidth : Nat
  lineFitSuffixWidth : Nat
  respectPendingIndent : Bool := false
  rebaseSourceTextTargetColumn? : Option Nat := none

structure Emission where
  text : String
  lastToken : SyntaxTree.Token
  preserveNextStandaloneCommentIndent : Bool

private def emitRebased? (request : EmissionRequest) (tree : SyntaxTree.Tree)
    (classification? : Option LayoutIslandKind)
    : Option Emission := do
  let firstToken ← SyntaxTree.Tree.firstToken? tree
  let lastToken ← SyntaxTree.Tree.lastToken? tree
  let proof := classification?.any LayoutIslandKind.isProof
  let proofLayout := classification?.any LayoutIslandKind.isProofLayout
  let calcLayout := classification?.any LayoutIslandKind.isCalc
  let quotation := classification?.any LayoutIslandKind.isQuotation
  let usesPendingIndent :=
    (request.respectPendingIndent
      || classification?.any LayoutIslandKind.usesPendingIndent)
    && request.pendingLeadingWhitespace?.isSome
  let originalLeading :=
    match request.lastToken? with
    | some leftToken =>
        SyntaxTree.sourceText request.source leftToken.span.stop firstToken.span.start
    | none => firstToken.leading.text
  let leading :=
    request.formattedLeadingWhitespace?.getD
      (if usesPendingIndent then
          request.pendingLeadingWhitespace?.getD originalLeading
        else
          originalLeading)
  let quotationStartsOnLine :=
    quotation
    && (currentLineAfterAppend request.currentLine leading).all
        SpaceRules.isHorizontalWhitespace
  let leadingColumn := lineWidth <| currentLineAfterAppend request.currentLine leading
  let sourceText :=
    SyntaxTree.sourceText request.source firstToken.span.start lastToken.span.stop
  let sourceColumn := request.sourceMap.columnAt firstToken.span.start
  let retainsRelativeLayout := classification?.any LayoutIslandKind.retainsRelativeLayout
  let retainsInlineRelativeLayout := retainsRelativeLayout || proofLayout || calcLayout
  let hasLineBreakTrivia := retainsInlineRelativeLayout && treeHasLineBreakTrivia tree
  let originalLeadingHasLineStructure := SpaceRules.hasLineStructure originalLeading
  let detachedInlineProofBody :=
    proof
    && hasLineBreakTrivia
    && usesPendingIndent
    && !originalLeadingHasLineStructure
    && SpaceRules.hasLineStructure leading
  let inlineMultilineLayoutIsland :=
    retainsInlineRelativeLayout
    && hasLineBreakTrivia
    && (!originalLeadingHasLineStructure || proofLayout || quotationStartsOnLine)
    && !detachedInlineProofBody
  let inlineContinuationColumns? :=
    if !inlineMultilineLayoutIsland then
      none
    else
      match treeContinuationIndent? request.sourceMap tree, request.lastToken? with
      | some sourceIndent, some leftToken =>
          let sourceAnchor := request.sourceMap.columnAt leftToken.span.start
          let outputAnchor := lineWidth request.currentLine - leftToken.lexeme.length
          let movedIndent := shiftColumnByAnchor sourceAnchor outputAnchor sourceIndent
          let structuralIndent :=
            if proof then
              (request.segmentIndentation + 1) * indentationSpaces
            else if proofLayout then
              if originalLeadingHasLineStructure then
                shiftColumnByAnchor sourceColumn leadingColumn sourceIndent
              else if proofLayoutRebasesFromFirstToken tree then
                sourceIndent
              else
                request.currentIndent + indentationSpaces
            else if calcLayout then
              (leadingColumn / indentationSpaces + 1) * indentationSpaces
            else if quotationStartsOnLine then
              (leadingColumn / indentationSpaces + 1) * indentationSpaces
            else if usesPendingIndent then
              leadingColumn
            else
              request.currentIndent
          let movedIndent :=
            if sourceAnchor < sourceIndent then
              movedIndent
            else
              sourceIndent
          let targetIndent :=
            if proofLayout
                && request.respectPendingIndent
                && originalLeadingHasLineStructure then
              structuralIndent
            else
              max movedIndent structuralIndent
          some (sourceIndent, targetIndent)
      | _, _ => none
  let inlineContinuationColumns? :=
    match inlineContinuationColumns? with
    | some (sourceIndent, targetIndent) =>
        if proofLayout && request.respectPendingIndent then
          some (sourceIndent, targetIndent)
        else if quotationStartsOnLine then
          some (sourceIndent, targetIndent)
        else if proofLayout || calcLayout || quotation then
          some
            (
              sourceIndent,
              fittingTargetColumn request.source request.sourceMap tree sourceText
                sourceIndent targetIndent request.lineWidth
                request.lineFitSuffixWidth
            )
        else
          some (sourceIndent, targetIndent)
    | none => none
  let sourceColumnRebasedFromLayoutBase :=
    shiftColumnByAnchor request.sourceLayoutBaseColumn
      request.outputLayoutBaseColumn sourceColumn
  let layoutTargetColumn? :=
    if !retainsRelativeLayout
        || inlineMultilineLayoutIsland
        || detachedInlineProofBody then
      none
    else if usesPendingIndent then
      some leadingColumn
    else if originalLeadingHasLineStructure then
      some sourceColumnRebasedFromLayoutBase
    else
      none
  let targetColumn? :=
    request.rebaseSourceTextTargetColumn?.orElse fun _ => layoutTargetColumn?
  let proofBodyTargetColumn? :=
    if proof && originalLeadingHasLineStructure then
      request.lastToken?.bind
        fun token =>
          if tokenStartsCurrentLine request.currentLine token then
            some (request.currentLine.length - token.lexeme.length + indentationSpaces)
          else if sourceColumn <= request.sourceLayoutBaseColumn then
            none
          else if request.sourceMap.columnAt token.span.start
                  == request.currentLine.length - token.lexeme.length then
            none
          else
            bodyColumnAfterOpeningDelimiter? request.currentLine token
    else
      none
  let targetColumn? :=
    match targetColumn?, proofBodyTargetColumn? with
    | some targetColumn, some proofBodyTargetColumn =>
        some (max targetColumn proofBodyTargetColumn)
    | some targetColumn, none => some targetColumn
    | none, some proofBodyTargetColumn => some proofBodyTargetColumn
    | none, none => none
  let targetColumn? :=
    if proof && originalLeadingHasLineStructure then
      targetColumn?.map
        fun targetColumn =>
          max request.outputLayoutBaseColumn targetColumn
    else
      targetColumn?
  let targetColumn? :=
    if quotation && !quotationStartsOnLine && !inlineMultilineLayoutIsland then
      targetColumn?.map
        fun targetColumn =>
          fittingTargetColumn request.source request.sourceMap tree sourceText
            sourceColumn targetColumn request.lineWidth request.lineFitSuffixWidth
    else
      targetColumn?
  let leading :=
    match targetColumn? with
    | some targetColumn =>
        let sourceColumn :=
          if request.formattedLeadingWhitespace?.isSome || usesPendingIndent then
            leadingColumn
          else
            sourceColumn
        rebaseTextIndent sourceColumn targetColumn leading
    | none => leading
  let sourceTextRebase? :=
    match inlineContinuationColumns?,
          request.rebaseSourceTextTargetColumn? with
    | some continuationColumns, some targetColumn =>
        if proof
            || (proofLayout
                && originalLeadingHasLineStructure
                && proofLayoutRebasesFromFirstToken tree) then
          some (sourceColumn, targetColumn)
        else
          some continuationColumns
    | some continuationColumns, none => some continuationColumns
    | none, some targetColumn =>
        if calcLayout then
          (treeContinuationIndent? request.sourceMap tree).map
            fun sourceIndent =>
              (sourceIndent, (targetColumn / indentationSpaces + 1) * indentationSpaces)
        else
          some (sourceColumn, targetColumn)
    | none, none =>
        if calcLayout then
          (treeContinuationIndent? request.sourceMap tree).map
            fun sourceIndent =>
              (sourceIndent, (leadingColumn / indentationSpaces + 1) * indentationSpaces)
        else
          targetColumn?.map
            fun targetColumn =>
              (sourceColumn, targetColumn)
  let sourceText :=
    match classification? with
    | some .syntaxComment =>
        let outputColumn :=
          lineWidth <| currentLineAfterAppend request.currentLine leading
        if SpaceRules.hasLineStructure leading then
          rebaseMultilineSourceSlice outputColumn sourceText
        else
          rebaseTextIndent sourceColumn outputColumn sourceText
    | _ =>
        match sourceTextRebase? with
        | some (sourceIndent, targetIndent) =>
            if sourceIndent == targetIndent then
              sourceText
            else
              rebaseTreeText request.source request.sourceMap tree sourceIndent
                targetIndent
        | none =>
            let outputColumn :=
              lineWidth <| currentLineAfterAppend request.currentLine leading
            if sourceColumn == outputColumn || !originalLeadingHasLineStructure then
              sourceText
            else
              rebaseTreeText request.source request.sourceMap tree sourceColumn
                outputColumn (rebaseTrivia := false)
  some
    {
      text := leading ++ sourceText
      lastToken
      preserveNextStandaloneCommentIndent :=
        classification?.any LayoutIslandKind.preservesFollowingCommentIndent
    }

@[inline]
def emit? (request : EmissionRequest) (tree : SyntaxTree.Tree)
    (classification? : Option LayoutIslandKind := none)
    : Option Emission :=
  emitRebased? request tree classification?

end OriginalTree
end Formatter
end LeanFmt
